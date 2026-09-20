---
title: "The Peggy Implementation"
source: "Equality Saturation: Using Equational Reasoning to Optimize Imperative Functions (Ross Tate, PhD Thesis, UCSD 2012)"
chapter: "Chapter 10, pp. 129–143"
tags: [equality-saturation, compilers, peg, e-graph, rete, pseudo-boolean-solver, program-optimization]
---

[[book-guidelines|↩ Back to guidelines]]

# The Peggy Implementation

## Why this chapter exists

Everything up to this point in the thesis is a beautiful idea sitting in a vacuum: represent an imperative program as a pure, referentially transparent graph (a PEG), repeatedly saturate it with equalities instead of destructively rewriting it ([[Equality-Saturation|equality saturation]]), and only at the very end pick the cheapest program hiding inside that graph. That idea works on paper for a toy language, SIMPLE, with no heap, no method calls, no exceptions.

Peggy is what happens when you try to make that idea survive contact with real Java bytecode and LLVM bitcode. Four very ordinary-sounding engineering problems show up the moment you do this, and each one turns out to have a sharp technical edge:

1. **Representation** — Java has a heap and virtual method calls. You need a PEG-native way to represent "this read depends on that write" and "this call must happen after that call" without reintroducing an implicit notion of instruction order (which is exactly what PEGs were built to avoid).
2. **Matching** — an E-PEG (an equality-annotated PEG) accumulates axiom applications, and each new equality can enable more axioms. If you recheck every axiom against the whole graph every time something changes, you get an implementation that is *correct* but unusably slow.
3. **Selection** — once saturation is done, the E-PEG represents exponentially many equivalent programs simultaneously. You need to pick one, globally, not just make a sequence of locally-good micro-decisions (which is exactly the "local profitability" trap destructive optimizers fall into).
4. **Design economy** — some representation choices (like keeping `eval` and `pass` as two nodes instead of merging them) look like redundant machinery until you see what a global search-and-select process needs from its intermediate representation to work efficiently.

This chapter is Tate's answer to all four, and it's worth reading as a case study in a recurring theme: *when you switch from "always run in a specific order" to "here is everything that could be equal, in whatever order you like," you push the ordering problem somewhere else — you don't eliminate it.* Sections 10.1–10.4 are literally that theme playing out four times: at the level of memory (the heap), at the level of pattern matching (Rete), at the level of global search (the pseudo-boolean solver), and at the level of node design (eval/pass).

---

## 10.1 Representing effects: σ nodes and `invoke` nodes

### The problem, from first principles

A PEG node has no implicit position in time. `load(addr)` in an imperative language means "read memory *right now*, at this point in the instruction stream." But a PEG node just says "the value obtained by loading `addr` from *some* heap state" — which heap state? If two loads and a store to the same location all just float in the graph with no ordering constraint between them, the graph no longer determines a single program; it determines an under-specified one, and the compiler can't safely reorder rewrites around it.

Chapter 9 already solved this for the general case with *effect witnesses*: any operation that touches shared, mutable state takes a witness value in and, if it mutates that state, produces a new witness value out. Sequential dependency, instead of being implicit in program order, becomes an explicit data-flow edge — the witness threads through the graph like a linear resource. Peggy specializes this general mechanism into two concrete node families.

### σ nodes: heap summaries

Peggy calls its effect witness for heap state a **σ node**, standing in for a "heap summary" — conceptually a function from addresses to values. Any Java/LLVM operation that reads and/or writes object state takes and/or returns a σ value. Stack and register variables, by contrast, are only ever touched by direct assignment, so they stay ordinary precise PEG values with no σ threading needed — this is a deliberate abstraction choice (you could imagine finer-grained heap summaries, e.g. per-object or per-field, but Peggy uses one coarse global σ). Because other effects (exceptions, non-determinism) also interact with the heap, Peggy actually reuses the general effect-witness machinery from Chapter 9 for σ, rather than inventing a heap-specific mechanism.

### `invoke` nodes: bundling a method call

A non-static method call is one PEG node, `invoke`, with four inputs: the input σ, the context object (`this`), a method identifier, and the list of actual parameters. Logically it *returns a tuple* $(\sigma', v)$ — the resulting effect witness and the method's return value — and two small **projection nodes**, $\rho_\sigma$ and $\rho_v$, pick the piece you want out of that tuple. (Static/free function calls just elide the context-object input.)

$$
\texttt{invoke}(\sigma_{\text{in}}, \; obj, \; \texttt{C.foo}, \; [a, b]) \;\longrightarrow\; (\sigma_{\text{out}}, v)
$$

The book's Figure 10.1 example is `T x = obj1.foo(a,b); T y = obj2.bar(x);` — two sequential calls. The PEG encodes their control dependency purely through data flow: the second `invoke`'s input σ is $\rho_\sigma$ of the first `invoke`'s output. There is no separate "happens-before" edge type; sequencing *is* the σ-threading.

This is the same move that shifted PEGs, in Chapter 9's language, from an "expression" grammar (multiple inputs, one output) toward a "string diagram" grammar (multiple inputs, multiple outputs) — and the projection nodes are exactly the bookkeeping needed to fold that back into an expression-shaped graph for uniformity with the rest of the PEG machinery.

### Grounding: what breaks without this

**Rust.** Think of `invoke` as a function whose real signature, if Rust let you write effect-typed functions, would look like this — the value you actually care about (`T`) is inseparable from the heap-state token that must thread through it linearly:

```rust
// Conceptually: an invoke node is this function, uncalled — a node in the PEG
// IS this function applied to specific argument-nodes, not a value.
fn invoke(sigma_in: HeapToken, obj: ObjRef, method: MethodId, args: Vec<Value>)
    -> (HeapToken, Value)
{ /* ... */ }

// Two sequential calls: the SECOND call's heap token must be
// the FIRST call's output token — not "the ambient heap".
let (sigma1, x) = invoke(sigma0, obj1, "C1.foo", vec![a, b]);
let (sigma2, y) = invoke(sigma1, obj2, "C2.bar", vec![x]);
```

If you instead let both calls take `sigma0` (the same nominal "heap"), nothing in the type system tells you `bar` must run after `foo` — you've silently reintroduced an implicit ordering assumption into a representation that's supposed to make ordering fully explicit. That's "[[Loop-and-Branch-Optimizations-Discovered-by-Saturation#What breaks without this|what breaks without this]]": equality saturation could then legally float `foo` and `bar` past each other, producing a semantically wrong program, because nothing in the graph says they conflict.

**Python**, as a five-line sketch of the same idea without Rust's ceremony:

```python
def invoke(sigma_in, obj, method, args):
    sigma_out, retval = run_effectful(obj, method, args, sigma_in)
    return sigma_out, retval

sigma1, x = invoke(sigma0, obj1, "foo", [a, b])
sigma2, y = invoke(sigma1, obj2, "bar", [x])   # threads sigma1, not sigma0
```

**Lean** angle: this is a linear/affine resource-threading pattern, structurally identical to how a monadic `IO` or `ST` computation threads a `RealWorld`/state token through otherwise-pure code, or how a linear type system would forbid `sigma1` from being used twice. Section 9.3's category-theoretic treatment (premonoidal categories, the "center," partial bifunctors) is the formal justification for *why* this threading is semantically sound — it's the same story as Haskell's `IO` monad being "just" a proof that effectful operations don't commute freely, dressed up categorically rather than monadically.

---

## 10.2 The linearization problem for effect witnesses

### Why threading a token through the graph isn't the end of the story

Effect witnesses solve the *equational* problem (how do we reason about ordering symbolically). But Peggy also has to turn the final selected PEG back into real bytecode — reversion, from Chapter 8. And reversion assumes every PEG value can be freely duplicated: if two different places need the value of node $n$, you just compute $n$ twice, or store it once and read it twice. That assumption is *false* for effect witnesses. A heap token isn't a value you can duplicate at runtime — there's only one heap, and "using the σ twice" doesn't correspond to any executable action. **Effect witnesses must be used linearly.**

This is a genuinely different kind of constraint from anything Chapter 8 dealt with, and it can be *unsolvable locally even though it's solvable globally*.

### The worked example (straight from the book)

Consider:

```
if (z) { x := 1 } else { x := 2 }
y := g(x);      // g reads the heap, doesn't write it
if (z) { f() }  // f reads AND writes the heap
retvar := y;
```

In the PEG, the σ node feeding into `g` is used in *three* places (it's a linear resource being shared, functionally, exactly as PEGs allow any value to be shared). As a pure graph this is completely fine — PEGs treat effect witnesses like any other value, functionally. The only question is: when we revert this back to imperative code, is there an *order* in which we can run the instructions using the σ exactly once each? Here, yes, obviously: run `g` first (it only reads), then `f` (which writes). The ordering is solvable — **globally**.

The trouble is *how* Peggy's reversion algorithm actually works: it first builds branch nodes (one per `if`) and *fuses* them, and only afterward tries to linearize effect witnesses *within* each already-built branch node. Once the fusion step has locked `f` inside a branch node whose φ-condition depends on the result of `g`'s branch, you're stuck: `f` can no longer run after `g`, because `f`'s branch node structurally depends on the value that `g`'s branch node produces. The constraint that was globally solvable becomes locally unsolvable, purely as an artifact of the order in which the reversion algorithm made its decisions.

$$
\text{globally solvable} \;\centernot\implies\; \text{solvable after local branch fusion}
$$

This is a real limitation, not a footnote: Peggy's reversion is incomplete for effect witnesses, and in about 3% of the Java methods compiled, this incompleteness bites and the method is simply left unoptimized.

### Stepp's mitigation (cited, not Peggy's own solution)

The thesis credits Michael Stepp's dissertation with a workaround, described at a high level:

1. Make every operation that *reads* the heap also *output* an effect witness (even if it wasn't going to modify anything) — so `g` now explicitly threads σ through, making the intended order explicit in the PEG from the start.
2. During saturation, add an equality between `g`'s *output* witness and its *input* witness (since `g` doesn't actually change the heap, they're semantically the same value) — this lets equality saturation still discover the "optimize as if `f`'s input were `g`'s input" rewrite when it's valid.
3. Restrict the global profitability heuristic (Section 10.3) to only ever select linearizable PEGs — and since the original, always-linearizable PEG is still present in the E-PEG as one of the equivalent options, there's always a fallback.

This is a nice illustration of a recurring equality-saturation pattern: instead of making the *representation* more expressive to dodge a problem, you make the *representation conservative* (always-linearizable by construction) and let the *search* (saturation + selection) recover the optimized cases opportunistically, with a guaranteed-safe fallback always available.

### Grounding

**Rust** — this is precisely the shape of Rust's own linear-ish ownership discipline, except Peggy's constraint is *dynamic/global* (a whole-graph scheduling problem) rather than syntactic:

```rust
// Rust's borrow checker forbids exactly the "use sigma twice" shape
// syntactically. Peggy's problem is: can we find SOME topological order
// of a DAG of effectful ops such that this token, used N times in the
// graph, is threaded through exactly once per use, in a valid sequence?
fn g(sigma: &HeapToken, x: i32) -> i32;              // reads only — could take &
fn f(sigma: HeapToken) -> HeapToken;                  // reads AND writes — consumes, returns

// Valid order: g doesn't consume sigma, so run it first,
// THEN consume sigma exactly once through f.
let y = g(&sigma0, x);
let sigma1 = f(sigma0);
```

If you called `f` first, `sigma0` would be moved/consumed, and any subsequent structural dependency on the *original* σ (which the fused branch node in the bad case effectively created) would be a borrow-check-style error. Peggy's linearization problem is, in effect, "find a valid move-order for a value used multiple times in a graph, under branch/loop-imposed structural constraints" — a scheduling problem the Rust compiler never has to solve because its ownership rules are checked syntactically at each use site, not searched for globally across a whole rewritten program.

---

## 10.3 The Rete algorithm for efficient trigger matching

### What breaks without it

An E-PEG is a PEG plus a set of discovered equalities. Peggy's saturation engine (Figure 10.3 in the book) is essentially this loop:

$$
\textbf{while } \exists (p, f) \in A,\ \text{subst} \in S.\ \text{subst} = \text{Match}(p, \text{epeg}) \textbf{ do } \text{epeg} := \text{AddNodesAndEqualities}(\text{epeg}, f(\text{subst}, \text{epeg}))
$$

Each **equality analysis** is a pair $(p, f)$: $p$ is a *trigger* — an E-PEG pattern with free variables (essentially: "find a sub-PEG shaped like this, with these placeholders unified consistently") — and $f$ is a callback that, given a match, returns new nodes/equalities to fold into the E-PEG. This is deliberately reminiscent of *rewrite rules in a rule-based system*: match a left-hand-side pattern, fire a right-hand-side action.

The problem: axiom applications trigger other axiom applications. A naive engine re-scans the *entire* E-PEG against *every* trigger every time anything changes. Tate reports that their first implementation did exactly this and it was "unusably slow" — the overwhelming majority of that work is redundant, because most triggers aren't anywhere near the part of the graph that just changed.

### The Rete algorithm, first-principles

Peggy borrows the **Rete algorithm** wholesale from the expert-systems/production-rule-system literature (Forgy 1982, cited as [36]) — the same family of algorithms behind systems like CLIPS/OPS5. The core idea:

> Instead of re-matching every pattern against the whole fact base every time a fact changes, maintain a network of **partial-match states** (essentially finite-state machines, one per in-progress pattern match) and only step the *relevant* machines when new information arrives.

Concretely for Peggy: the Rete network's patterns are the axioms' trigger preconditions — "does a sub-PEG of this shape exist" (or other checkable properties, like loop invariance). When a new node or equality is added to the E-PEG, only state machines whose next required piece is that new node/equality advance. When a machine reaches its accept state, its whole pattern has matched, and the corresponding axiom's action fires — which can itself create new nodes/equalities, advancing further machines. This is exactly how one axiom's firing "cascades" into enabling others, but *without* re-deriving from scratch which axioms are even candidates.

### Termination

Because saturation can genuinely fail to terminate (recursive inlining, `A = (A+1)-1` applied forever), triggers are also used as a termination-control mechanism, "a technique also used in automated theorem provers": most triggers just look for a left-hand side and equate it to a right-hand side, but some are deliberately made *more restrictive* to suppress expansions likely to be useless — e.g. only equating a constant to a loop expression if an appropriate `pass` node already exists, so a loop isn't manufactured out of nothing. Even so, saturation doesn't always finish: **84% of methods in Peggy's Java benchmarks fully saturate**; the rest are capped by a processed-expression bound, using breadth-first exploration order to avoid running down one infinitely deep branch of the search space.

### Grounding — this is the part that transfers directly

This is exactly the mechanism a bidirectional elaborator or theorem-proving unification engine needs, and it's worth calling out for the standing project: **Rete is an incremental-matching data structure for exactly the same problem a proof-search or constraint-solving loop faces** — "when a new fact/equality/binding is added, which of my many pending rules/unification goals does it actually affect?" A naive elaborator that re-runs every typing rule or every unification attempt from scratch on every metavariable assignment has the same performance pathology Tate describes.

**Rust** — a Rete-style E-PEG matcher, sketched as a trait over a graph and per-pattern automaton state:

```rust
struct PartialMatch {
    pattern_id: PatternId,
    bound: HashMap<PatternVar, NodeId>,  // free variables bound so far
    next_required: PatternStep,          // what this state machine needs next
}

trait ReteNetwork {
    // Called once when a new node/equality lands in the E-PEG.
    // Only machines whose `next_required` matches `event` get advanced —
    // NOT every pattern in the system.
    fn on_event(&mut self, event: EPegEvent) -> Vec<CompletedMatch>;
}

// A completed match fires the axiom's callback f(subst, epeg),
// which may emit new EPegEvents, transitively waking other machines.
```

**Lean** connection: this is structurally the same problem the elaborator's unifier and the tactic framework's `simp` set face — `simp` also needs to avoid re-trying every rewrite rule against the whole goal on every step, which is why Lean maintains discrimination trees / indexing structures keyed on head symbols, a lighter-weight cousin of Rete's automaton-per-pattern approach. If you build a custom prover for the compiler project, a Rete-like incremental matcher (or at minimum, symbol-indexed rule dispatch) is close to mandatory once your rule set and fact base grow past toy size — this is one of the clearest "mechanism, not just theory" payoffs in this chapter.

---

## 10.4 The pseudo-boolean solver for global profitability

### First principles: why this has to be global

After saturation, the E-PEG represents an astronomically large family of semantically equivalent PEGs — every combination of "which equivalent sub-expression did we pick, everywhere in the graph" is a distinct candidate program. `SelectBest` has to pick one, and it must do so *globally*: a cost-minimal choice at one node can be a bad choice once you account for what it forces elsewhere (e.g., choosing an operator that's individually cheap but pulls in a dependency that's expensive inside a loop). This is exactly the "local profitability heuristics" trap that destructive rewrite systems can't escape, since they never get to see all the alternatives at once.

Peggy casts this as a **0-1 integer linear program** — a *pseudo-boolean* problem — and hands it to an off-the-shelf pseudo-boolean solver, **Pueblo**.

### The encoding

For an E-PEG $\langle N, L, C, E \rangle$ (a PEG $\langle N, L, C\rangle$ plus equalities $E$ inducing equivalence classes $N/E$):

- For each **node** $n \in N$: a boolean variable $B_n$ — true iff we select $n$ for evaluation.
- For each **equivalence class** $q \in N/E$: a boolean variable $B_q$ — true iff *some* member of $q$ is selected.
- $r$ denotes the equivalence class of the return value.

$$
\text{Constraints}(\langle N, L, C, E \rangle) \;\equiv\; B_r \;\wedge\; \bigwedge_{n \in N} F(n) \;\wedge\; \bigwedge_{q \in N/E} G(q)
$$

$$
F(n) \;\equiv\; B_n \Rightarrow \bigwedge_{q \,\in\, \text{params}(n)} B_q
\qquad\qquad
G(q) \;\equiv\; B_q \Rightarrow \bigvee_{n \,\in\, q} B_n
$$

In words: (1) the return value's equivalence class must be selected; (2) selecting a node forces selecting every equivalence class it depends on; (3) selecting an equivalence class forces selecting at least one member node of it. This is a clean encoding of "the selected nodes must form a self-contained, dependency-closed program."

The objective:

$$
\min_{\text{Constraints}(\langle N,L,C,E\rangle)} \; \sum_{n \in N} B_n \cdot C_n
$$

### The cost model

$$
C_n = \text{basic\_cost}(n) \cdot k^{\,\text{depth}(n)}
$$

`basic_cost(n)` is how expensive the operator itself is; `depth(n)` is the loop-nesting depth of $n$ — reusing the `invariant`$_\ell$ machinery from Definition 6.2 (Section 6.3): $\text{depth}(n) = \max_\ell \neg \text{invariant}_\ell(n)$, i.e., the deepest loop level at which $n$ is *not* known to be invariant. $k$ is a tuned constant (Peggy uses $k = 20$). Crucially, this exponential-in-depth cost model is **crude but effective**, precisely *because* `invariant`$_\ell$ is the same predicate the reversion algorithm (Section 8.9) uses to decide what code actually gets hoisted out of loops — so the cost model's prediction of "how deep will this end up nested" tracks what reversion will actually do, even though cost is computed *before* reversion runs.

### The extra constraint: forbidding cycles without a θ node

There's a subtlety: naively, this ILP encoding alone can select an *invalid* PEG. Consider `x + 0`; after an axiom fires, `+` becomes equivalent to `x` — same equivalence class. Nothing in $F$/$G$ above stops the solver from picking `+` and then, as its own argument, picking a member of its own equivalence class, i.e., $+$'s own class — producing a structural cycle with no `θ` node breaking it. Valid PEGs may only have cycles that pass through a `θ` node (that's what makes a "loop" a loop rather than an infinite regress). Peggy patches this by adding **reachability variables** $B_{i;j}$ ("does $i$ reach $j$ without passing through a θ node in the selected solution") with propagation rules, and forbidding $B_{n;n}$ for any non-θ node $n$ — an explicit acyclicity-modulo-θ constraint bolted onto the ILP.

Effect-witness linearity (10.2) adds yet more pseudo-boolean constraints on top (again, credited to Stepp's thesis for the details) — so SelectBest isn't just "minimize cost subject to closure," it's "minimize cost subject to closure, acyclicity, and linearizability," all in one ILP call.

Solver choice is explicitly a pluggable implementation detail, not part of the correctness argument: Peggy uses Pueblo but the thesis reports also testing MiniSat and SAT4J, with MiniSat sometimes beating Pueblo and SAT4J uniformly worse — swappable because the *encoding*, not the solver, carries the semantic guarantees.

### What breaks without a global solver, concretely

A greedy/local selection ("pick the cheapest option at each node, independently") could — and in practice does — pick a mix of a peeled-loop version at one point in the graph and an unpeeled version elsewhere for structurally the "same" loop, because locally each choice looked cheapest in its own context. Section 10.4 is largely about how Peggy's node design *helps* the pseudo-boolean encoding avoid exactly this failure.

### Grounding

**Rust** — pseudo-boolean/ILP-as-implication is a close cousin of a SAT-encoded constraint propagation problem; if you're building a CSP kernel for the compiler project (per the learning goals), this section is close to a direct blueprint for "encode a global selection-with-dependencies problem as boolean implications + an objective, hand to an off-the-shelf solver, keep the encoding solver-agnostic":

```rust
struct PseudoBooleanEncoding {
    // one 0/1 variable per node and per equivalence class
    node_vars: HashMap<NodeId, Var>,
    class_vars: HashMap<ClassId, Var>,
    clauses: Vec<Clause>,       // F(n), G(q), acyclicity-modulo-theta
    objective: Vec<(Var, i64)>, // (B_n, C_n) pairs to minimize
}
// Solve with ANY 0-1 ILP / pseudo-boolean backend — the encoding
// (not the solver) is what carries correctness.
```

This is squarely the "how you'd implement/check it" reading the learning goals ask to prioritize: a real, checkable global-selection mechanism, not just "compilers pick the best option."

**Python**, as a sketch of the constraint shape without solver ceremony:

```python
# F(n): B_n -> AND(B_q for q in params(n))
# G(q): B_q -> OR(B_n for n in q)
# objective: minimize sum(B_n * cost(n) for n in N), subject to B_r and F,G for all n,q
```

---

## Why keep `eval` and `pass` as separate nodes?

### The design question

`eval`/`pass` are PEG's loop-evaluation pair (from earlier chapters): `pass` represents "the state of the loop variables after some iteration," `eval` represents "evaluate this loop-carried quantity, given a `pass` node telling you which iteration's values to use." Why not fuse them into a single `μ` node that does both jobs at once? The chapter gives three converging reasons, all about what a *global search process* needs from its own intermediate representation — not about expressiveness.

### Reason 1: other things can play `pass`'s role

Loop peeling (Section 4.3) works by *swapping out* what feeds the second child of `eval` — a `pass` node, or (mid-peeling) a $\Sigma$, $Z$, or $\varphi$ node. Keeping these two node kinds separate means `eval` can point at any of several different "which iteration" descriptors interchangeably. A fused `μ` node would need to internalize all of these variants itself.

### Reason 2: one loop, one node — and what that buys the analysis

With separate nodes, an entire loop has exactly **one `pass` node**, shared by every `eval` node that reads a loop-carried value from it. Suppose an expensive analysis running during saturation decides a particular loop is worth peeling. With `eval`/`pass` separated, it makes **one edit** — replace that single `pass` node with an appropriate `φ` node — and then ordinary, cheap axioms propagate the consequence to every `eval` node that depends on it, independently and automatically.

With fused `μ` nodes, there is no single node representing "the loop" — every loop-carried value has its own `μ` node, all sharing the same break condition but existing as separate objects. The same peeling decision would require the expensive analysis to explicitly rewrite *every* `μ` node for that loop, one at a time. This is the same "what breaks without this" pattern as 10.1–10.3: fusing the two concerns (evaluation + "which iteration") reintroduces per-instance bookkeeping that a global mechanism was specifically designed to avoid.

### Reason 3: this feeds directly into 10.3's global selection problem

After peeling, every `eval`/`pass` pair (or every `μ` node) effectively has two versions available: peeled and unpeeled. The *worst* outcome is the pseudo-boolean solver picking peeled for some and unpeeled for others of what should be "the same loop" — producing a program with two redundant copies of loop machinery.

With `eval`/`pass` separated, Peggy can bias the ILP's cost model to make `pass` nodes themselves expensive — since there's exactly one `pass` node per loop, this cheaply nudges the solver toward selecting a single, consistent loop version, peeled or not.

With fused `μ` nodes, there is no single node to attach that bias to — cost falls on the many individual `μ` nodes, and the solver, optimizing each independently, has no structural signal discouraging it from mixing peeled and unpeeled choices across different loop-carried values of what is conceptually one loop. It's a straightforward illustration of *representation choices propagating into optimizer quality*: a design decision that looks like it's "only" about the IR turns out to determine whether the global-selection ILP can even express the preference you want.

### Reason 4 (mentioned in passing): reversion simplicity

The same "one node, one edit" property helps reversion (Chapter 8): peeling a loop is "rewrite the `pass` node," and every dependent `eval` node restructures automatically — no separate coordination step is needed across the multiple `eval` nodes belonging to one loop.

### Grounding

This is best understood as a **normal-form / canonicalization design choice**, the same category of decision as choosing whether a compiler IR represents a loop as one `Loop` AST node with a body, vs. desugaring it immediately into flat basic blocks with back-edges. The desugared form is "more primitive" but loses the single attachment point a later pass needs. In Rust terms:

```rust
// Fused: one enum variant per loop-carried quantity, no single "this is
// the loop" handle to rewrite or cost-bias.
enum MuNode { Mu { break_cond: NodeId, body: NodeId } }  // many per loop

// Separated: exactly one PassNode per loop; many EvalNodes point at it.
struct PassNode { break_cond: NodeId }
struct EvalNode { iteration_selector: NodeId /* -> some PassNode, or Sigma/Z/Phi during peeling */ }
```

If you were designing an IR for the compiler project — say, representing loop invariants or fixpoint computations for the abstract-interpretation engine — this section is a concrete argument for giving recurring structural motifs (a whole loop, a whole method, a whole SCC) a *single canonical handle node* even when you could in principle desugar it into many finer-grained nodes: anything downstream that needs to reason about or rewrite "the loop as a unit" — a widening operator choosing a widening point, for instance — benefits from exactly the same "one edit, many consequences" property.

---

## Synthesis: how this chapter fits the thesis

```
Ch. 5  Formalization of equality saturation (Saturate, SelectBest as abstract components)
Ch. 6  PEGs / E-PEGs (the node vocabulary: eval, pass, θ, φ, ...)
Ch. 8  Reverting PEGs to CFGs (assumes free duplication of values)
Ch. 9  Effect witnesses (general mechanism: thread a token for any effect)
        │
        ▼
Ch. 10 THE PEGGY IMPLEMENTATION  ← this article
  10.1  σ / invoke  — specializes Ch. 9's effect witnesses to heap + calls
  10.2  linearization — exposes the tension between Ch.9's witnesses and
                         Ch.8's "values are freely duplicable" assumption
  10.3  Rete + pseudo-boolean solver — concretizes Ch.5's abstract
                         Saturate / SelectBest into real algorithms
  10.4  eval/pass rationale — an IR design choice that make 10.3's
                         global solver actually work well
        │
        ▼
Ch. 11 Evaluation — empirically validates THIS chapter's choices:
        84% saturation rate (10.2), Pueblo dominates runtime at ~1.5s/method
        (10.3), 6x slower than Soot but discovers optimizations Soot can't.
```

Chapter 10 is where the thesis stops being a formal system and becomes an engineering artifact you could actually run on SpecJVM. Every subsection is a place where an abstraction from earlier chapters (effect witnesses, PEG nodes, the abstract `Saturate`/`SelectBest` interface) meets a concrete constraint (linear resources at runtime, combinatorial matching cost, NP-hard-shaped global selection, IR ergonomics) and has to bend without breaking the equational-reasoning guarantees that make the whole approach sound. Chapter 11's empirical numbers — the saturation-rate statistic, the timing breakdown showing Pueblo dominates runtime — are direct measurements of the tradeoffs made here.

**[[Domain-Independent-Applications-of-Generalization#Where this leads|Where this leads]] (learning-goals note):** Two mechanisms in this chapter are close to load-bearing for the compiler/elaborator project described in the standing goals. First, **Rete-style incremental pattern matching (10.3)** is the general solution to "how does a proof-search, constraint-propagation, or elaboration loop avoid re-deriving everything from scratch on every new fact" — directly relevant to both the custom theorem prover and to any `simp`-like rewriting layer, and worth comparing explicitly against Lean's discrimination-tree-based rule indexing. Second, **the pseudo-boolean/ILP encoding of a global selection problem (10.3)** is a template for "phrase a combinatorial choice as boolean implications over a dependency structure, minimize an objective, delegate to a pluggable 0-1 solver" — structurally close to what the CSP kernel for invariant/counterexample search will eventually need to do, down to the pattern of keeping the *encoding* solver-agnostic so the backend (Pueblo/MiniSat/SAT4J here; a custom SAT/SMT core there) can be swapped freely.
