---
title: "The egglog Language Model"
source: "Better Together: Unifying Datalog and Equality Saturation (Zhang, Wang, Flatt, Cao, Zucker, Rosenthal, Tatlock, Willsey — PLDI 2023)"
chapter: "Section 3, egglog (pp. 5–10)"
tags: [egglog, datalog, equality-saturation, functional-dependency, union-find, type-theory, automated-reasoning]
---

[[book-guidelines|↩ Back to guidelines]]

## Why egglog needs a new kind of "relation"

Datalog and equality saturation (EqSat) both compute fixpoints by repeatedly firing rules over a growing set of facts. But they disagree, structurally, about what a "fact" even is.

In Datalog, a relation is a **set** of tuples. `path(1, 4)` is either in the set or it isn't — there's no notion of *how* it got there, and two derivations of the same fact just collapse into one tuple. That's exactly what you want for reachability, but it's useless the moment you want to track *the shortest* path, or *the smallest* term equivalent to some expression. Classic Datalog handles that by bolting on **lattices**: a relation becomes a map from inputs to values in some join-semilattice, and conflicting derivations get resolved by taking the join (e.g. `min`, for shortest paths).

In EqSat, the atomic unit is the **e-class** — a set of terms all asserted to be equal — and the whole engine exists to grow and merge these sets without ever throwing information away (no destructive rewriting, which is what sidesteps the phase-ordering problem — see [[Fixpoint-Reasoning-Frameworks]]). But e-graphs are a bespoke, engine-specific data structure. Extending them (multiple analyses, richer patterns, conditional rewrites) means hand-writing more Rust inside the EqSat engine itself.

egglog's core idea is to notice that **both of these are instances of the same underlying primitive**: a partial function with a repair rule for conflicts. Once you build a language around "functions that repair themselves on conflict," you get Datalog-with-lattices, e-graph congruence, *and* term rewriting for free, as three uses of one mechanism rather than three separate systems.

## From relations to functions: the first move

egglog's concrete syntax is s-expression-based and looks superficially like Datalog. Here is classic transitive closure, side-by-side in Datalog-style egglog and function-style egglog:

```lisp
; relation-style (plain Datalog)
(relation edge (i64 i64))
(relation path (i64 i64))

(rule ((edge x y))
      ((path x y)))
(rule ((path x y) (edge y z))
      ((path x z)))

(edge 1 2) (edge 2 3) (edge 3 4)
(run)
(check (path 1 4)) ;; succeeds
```

```lisp
; function-style, with a merge for shortest path
(function edge (i64 i64) i64)
(function path (i64 i64) i64 :merge (min old new))

(rule ((= (edge x y) len))
      ((set (path x y) len)))
(rule ((= (path x y) xy) (= (edge y z) yz))
      ((set (path x z) (+ xy yz))))

(set (edge 1 2) 10) (set (edge 2 3) 10) (set (edge 1 3) 30)
(run)
(check (path 1 3)) ;; prints "20"
```

A rule in egglog has a **query** (the patterns before the actions — analogous to a Datalog rule's body) and a list of **actions** (what fires when the query matches — analogous to the head). This is deliberately the reverse reading order from textbook Datalog's `head :- body` notation, because egglog wants to read left-to-right as "match this, then do this."

The crucial design decision: **every user-defined function in egglog is backed by a map, not a set.** A plain Datalog relation `R` isn't a primitive in egglog at all — it's sugar for a function `f_R` into the built-in **unit type**, where `f_R(x) = ()` if `x ∈ R` and is undefined otherwise. So `(relation edge (i64 i64))` really means "a function from two `i64`s to `unit`." This is why the "relation-style" and "function-style" programs above are secretly the same program — the first is just the second with the return type erased to `unit` and the merge expression erased to the trivial one.

**What breaks without this:** if functions were still backed by sets (as a Datalog relation is), there'd be no way to express "the *same* input maps to two *different* candidate outputs, please reconcile them." You'd need a completely separate mechanism to layer lattice-style reasoning on top — which is exactly what earlier Datalog-with-lattices systems like Flix had to do as a bolted-on extension. By making the map (and its functional-dependency enforcement) the *default* representation, egglog gets that reconciliation machinery for every function automatically, not as a special case.

### Grounding: functions-with-repair as a Rust trait

Think of an egglog function as a `HashMap` guarded by an explicit conflict-resolution hook — which is a pattern you'd reach for in Rust the moment two writers might race on the same key:

```rust
trait Merge<V> {
    fn merge(old: V, new: V) -> V;
}

struct EgglogFunction<K, V, M: Merge<V>> {
    table: std::collections::HashMap<K, V>,
    _merge: std::marker::PhantomData<M>,
}

impl<K: std::hash::Hash + Eq, V: Clone, M: Merge<V>> EgglogFunction<K, V, M> {
    fn set(&mut self, key: K, new: V) {
        match self.table.get(&key) {
            Some(old) => {
                let resolved = M::merge(old.clone(), new);
                self.table.insert(key, resolved);
            }
            None => { self.table.insert(key, new); }
        }
    }
}

struct Min;
impl Merge<i64> for Min {
    fn merge(old: i64, new: i64) -> i64 { old.min(new) }
}
```

A Datalog `relation` is just `EgglogFunction<K, (), TrivialMerge>` where `TrivialMerge::merge(_, _) = ()` — there's nothing to reconcile because unit only has one value. The `path` function above is `EgglogFunction<(i64, i64), i64, Min>`. Same struct, different type parameter — which is the whole point: egglog didn't need a second mechanism for lattice-Datalog, only a different instantiation of the first one.

## The `:merge` expression as generalized lattice join

When `(set (path x y) new_len)` runs and `path(x, y)` is already mapped to some `old_len`, egglog evaluates the function's `:merge` expression with `old` and `new` bound to the two values, and stores *that* result. For `path`, `:merge (min old new)` gives exactly shortest-path relaxation — this is precisely the join operation of the min-lattice over `i64` (partial order `x ⊑ y ⟺ x ≥ y`), matching how Flix's lattice-Datalog resolves functional-dependency conflicts by taking the join.

But egglog does **not** restrict `:merge` to lattice joins. It can be *any* egglog expression — including, as the next section shows, an expression that unions two identifiers together. That generality is what lets the same mechanism cover EqSat's congruence closure, not just Datalog's lattice extension.

### Lean grounding: `:merge` as a total binary operation with an obligation

If you wanted `:merge` to behave sanely under any evaluation order (which egglog needs, since Datalog-style bottom-up evaluation doesn't guarantee a fixed application order for conflicting facts), you'd want it to be at least commutative and associative — i.e. actually a semilattice join, if you want determinism independent of rule-firing order. In Lean, stating that obligation directly on the merge function makes the requirement explicit rather than folklore:

```lean
structure MergeOp (α : Type) where
  merge : α → α → α
  comm  : ∀ a b, merge a b = merge b a
  assoc : ∀ a b c, merge (merge a b) c = merge a (merge b c)

def minMerge : MergeOp Int where
  merge := min
  comm  := Int.min_comm
  assoc := fun a b c => (Int.min_assoc a b c).symm
```

egglog's actual `:merge` expressions aren't checked against this obligation by the type system — the paper's *core egglog* fragment (Section 4) simplifies by assuming `:merge` is always either `union` on ids or a genuine lattice join, exactly to make this kind of algebraic reasoning tractable in the formal semantics (see [[Formal-Semantics-of-egglog]]).

## Sorts, `union`, and canonicalization

A Datalog `i64` is an *interpreted* base type — `3` means the number three, full stop, and can never be unioned with `4`. To get equality saturation, egglog needs values that are **opaque handles you're allowed to declare equal to each other**. That's a **sort**.

```lisp
(sort Node)
(function mk (i64) Node)
```

A sort is a set of opaque integer **ids** plus an equivalence relation over those ids, implemented with a **union-find** data structure (Tarjan 1975). `union`-ing two ids merges their equivalence classes; from then on they're indistinguishable to every rule in the program — any pattern variable bound to one could equally well have been bound to the other. These ids correspond directly to **e-class ids** in the EqSat view: a sort's union-find *is* an e-graph's equivalence structure, just described in database vocabulary instead of graph vocabulary.

```lisp
(edge (mk 1) (mk 2))
(edge (mk 2) (mk 3))
(edge (mk 5) (mk 6))

(union (mk 3) (mk 5))          ; nodes 3 and 5 are now the same node
(run)
(check (path (mk 1) (mk 6)))   ; succeeds — only true because of the union
```

Node contraction (vertex contraction) falls straight out of `union` on a sort — no special-cased graph algorithm needed, just the general equivalence mechanism applied to graph nodes.

**Canonicalization** is the invariant egglog maintains to make all of this coherent: every id appearing anywhere in the database is required to be canonical — i.e., the designated representative of its equivalence class. Queries only ever see canonical ids, which is what makes "matching modulo equality" automatic rather than something each rule has to implement by hand. (The mechanics of *keeping* the database canonical as new unions arrive — the rebuilding procedure — is its own topic; see [[Equivalence-and-Canonicalization]].)

### `:default` and "get-or-make-set"

What is `(mk 1)` the *first* time it's called, before anything has explicitly `set` it? egglog functions can carry a `:default` expression that extends a partial map into a total one: calling `(f x)` checks the map first, and only if `x` is undefined does egglog evaluate `:default`, store the result, and return it.

Unless overridden, a function returning a user-defined sort defaults to **creating a fresh equivalence class and returning its id** — the classic union-find "make-set" operation. (Functions returning a base type default to crashing — there's no sensible id to fabricate for an interpreted constant.) So calling `mk` is really a **get-or-make-set**: "give me the id for input `1`, creating a fresh one if this is the first time we've seen it."

```python
# illustrative sketch, not load-bearing
class UnionFind:
    def __init__(self):
        self.parent = {}

    def make_set(self):
        i = len(self.parent)
        self.parent[i] = i
        return i

    def find(self, x):
        while self.parent[x] != x:
            x = self.parent[x]
        return x

class EgglogFunction:
    def __init__(self, default_factory):
        self.table = {}
        self.default_factory = default_factory  # e.g. uf.make_set

    def call(self, *args):
        if args not in self.table:
            self.table[args] = self.default_factory()
        return self.table[args]
```

**What breaks without this:** if calling `mk` required a prior explicit `set`, every constructor use site would need its own boilerplate initialization step, and terms couldn't be built by simple nested function application — you'd be back to manually managing e-class allocation, which is exactly the low-level bookkeeping egg's Rust API forces on users.

## Terms, `datatype`, and `rewrite`: recovering equality saturation

Once functions can take sorts as *inputs* too (not just return them), nested function calls become term construction. A `Math` expression language:

```lisp
(datatype Math
  (Num i64)
  (Var String)
  (Add Math Math)
  (Mul Math Math))

(define expr1 (Mul (Num 2) (Add (Var "x") (Num 3))))  ; 2 * (x + 3)
(define expr2 (Add (Num 6) (Mul (Num 2) (Var "x"))))  ; 6 + 2 * x

(rewrite (Add a b)         (Add b a))
(rewrite (Mul a (Add b c)) (Add (Mul a b) (Mul a c)))
(rewrite (Add (Num a) (Num b)) (Num (+ a b)))
(rewrite (Mul (Num a) (Num b)) (Num (* a b)))

(run)
(check (= expr1 expr2))
```

Three pieces of sugar are doing real work here:

- **`datatype`** desugars to a `sort` declaration plus one constructor **function** per case — `Num`, `Var`, `Add`, `Mul` are all ordinary egglog functions returning `Math`, whose `:default` behavior is "make a fresh id," exactly like `mk` above.
- **`define`** desugars a named term into a nullary function: `(define x e)` becomes `(function x () T) (set (x) e)`, evaluating `e` and stashing it. Evaluating a term this way adds every subterm to the database via the constructors' `:default` behavior — building the term *is* populating the e-graph.
- **`rewrite`** desugars a rewrite rule into a query-plus-`union` rule: `(rewrite p1 p2)` becomes `(rule ((= __var p1)) ((union __var p2)))` — match the left pattern, bind it, and assert it's equal to (not replaced by) the right pattern.

That last point is the heart of how egglog recovers EqSat's non-destructive rewriting from Datalog's add-only semantics: a Datalog rule can only ever *add* facts to the database, never remove them. `union` is itself just an addition — an assertion that two ids belong to the same equivalence class — so `rewrite`-generated rules automatically inherit "keep everything, only ever add" for free. Nothing is deleted when `(Add a b)` rewrites to `(Add b a)`; both are still there, now unioned.

The constructors' default `:merge` is **`union`** — when two derivations produce the same function application with different output ids, egglog unions those ids rather than picking one arbitrarily. Combined with canonicalization, this makes the built-in equivalence relation automatically a **congruence relation**: if a map for `Add` contains both `(a, b) ↦ c` and `(a, d) ↦ e`, and a later rule unions `b` and `d`, canonicalizing the database exposes a functional-dependency violation — `(a, b) ↦ c` and `(a, b) ↦ e` simultaneously — which triggers `Add`'s `:merge`, unioning `c` and `e`. That is congruence closure: "if the parts are equal, the wholes must be too," implemented as an ordinary consequence of the general functional-dependency-repair mechanism, with no separate congruence-closure algorithm bolted on.

`extract` is the read-out step: given a term, it returns the smallest term in its equivalence class — the "optimize" half of equality saturation's "prove equal, then pick the best representative" workflow.

### Why this matters for a type-theory reader specifically

If you've worked with definitional equality and a kernel's `isDefEq`, egglog's canonicalize-then-compare check should look familiar: `(check (= expr1 expr2))` on a user-defined sort reduces to comparing two canonical ids for literal equality — the same move a dependently-typed kernel makes when it normalizes (or here, saturates) two terms and asks whether they land in the same equivalence class rather than requiring syntactic identity. The difference is *how* the equivalence is discovered: a type-theoretic kernel typically computes it by directed reduction to normal form, while egglog computes it by exhaustively exploring an undirected rewrite relation and merging as it goes. Both are answering "are these the same thing," just via different search strategies over the same underlying congruence-closure problem.

## Rules as "query + actions," not "body + head"

It's worth stating explicitly why egglog frames a rule as *query, then actions* rather than the textbook Datalog *head :- body*. The reversal isn't cosmetic — actions in egglog aren't restricted to "assert this one head atom." A rule's action list can `set` several functions, `union` several pairs, or do both, all conditioned on one shared query match. Datalog's single-head-atom convention doesn't have a natural slot for "and also union these two things while you're at it" — treating the fired-rule body as a small imperative action sequence does. This is also what makes `rewrite`'s desugaring (query for `p1`, then *union* the result with `p2`) fit naturally as "just another action," rather than needing a special rule shape carved out only for rewrites.

## Where this leads

Everything above — functions-with-merge, sorts, `union`, canonicalization — is described here only operationally, "by example." The next layer down gives it a real formal fixpoint semantics: an *inflationary* immediate consequence operator (inflationary specifically because `:merge` can make derived facts non-monotone, unlike plain Datalog), paired with a **rebuilding** operator that iterates to restore functional-dependency validity after each round of unions (see [[Formal-Semantics-of-egglog]] and [[Equivalence-and-Canonicalization]]). The functional, map-backed design described here is also precisely what lets egglog's implementation reuse ordinary Datalog machinery — semi-naïve evaluation and worst-case-optimal joins — for e-matching, essentially for free (see [[Query-Evaluation-and-E-Matching]] and [[Incremental-Evaluation]]). And because egglog is a real typechecked language rather than an embedded Rust API, it can support multiple datatypes and multiple independent analyses side by side — a structural advantage exploited directly in both case studies (see [[Language-Based-System-Design]], [[Case-Study-Unification-Based-Points-to-Analysis]], [[Case-Study-Sound-Floating-Point-Rewriting]]).
