---
title: Type Classes and Class Inference
source: Elaboration in Dependent Type Theory (de Moura, Avigad, Kong, Roux, 2015)
chapters: "Section 2.4 (pp. 6-9); mechanism grounded in Section 3.2/3.5 (pp. 14-15, 20-21)"
tags: [type-theory, elaboration, type-classes, lean, unification]
---

[[book-guidelines|↩ Back to guidelines]]

## The problem: implicit arguments that need to be *found*, not just *inferred*

Earlier in the elaboration story, an implicit argument is something the elaborator can pin down purely from *unification*: you write `f x`, `f` expects an argument of type `A`, so the elaborator solves a metavariable `?m : A` by looking at what's already around — the type of `x`, the expected return type, and so on. That's a local, syntactic puzzle.

Now consider a different situation. You write `s * t` where `s` and `t` are natural numbers, and `*` is generic multiplication, defined once for any type that happens to support it. Somewhere inside the elaborated term there's an implicit argument that says *which* multiplication operation to use for `nat` specifically — and nothing about unifying types with each other will produce that value. It isn't lying around in the local context; it has to be *discovered* by searching a library of facts the user has declared ("here is how `nat` multiplies", "here is how `int` multiplies", …) and possibly chaining several of those facts together. This is a fundamentally different kind of implicit-argument problem: not "what term makes these two types match," but "what term satisfies this predicate, given a database of known solutions." That's class inference, and it's how Lean gets Haskell-style type classes to work inside a dependent type theory.

## From records to classes: the core mechanism

A type class in Lean is nothing exotic at the type-theory level — it's just a `structure` (a record type) tagged so the elaborator knows to treat instances of it specially:

```
structure has_mul [class] (A : Type) := (mul : A → A → A)
```

Read literally: for any type `A`, `has_mul A` is a one-field record holding a binary operation `A → A → A`. There's no magic in the type itself. The magic is in how `has_mul A` gets *filled in* automatically. First, the generic operation is defined, taking the class as an *implicit* argument in square brackets:

```
definition mul {A : Type} [s : has_mul A] : A → A → A := has_mul.mul
infix * := mul
```

The square brackets are the actual mechanism boundary: they tell the elaborator "don't try to infer this argument by unification — synthesize it via class inference instead." Then a specific type registers itself as a solution:

```
definition nat_has_mul [instance] : has_mul nat := has_mul.mk nat.mul
```

Now, when the user writes `s * t` with `s : nat`, elaboration eventually needs to solve `?M : has_mul nat`. The elaborator searches a stored list of `[instance]`-tagged declarations, finds `nat_has_mul`, and assigns `?M := nat_has_mul`. Compare this to the earlier stages of [[The-Elaboration-Task|the elaboration task]], where an implicit argument's value came from a rigid syntactic match; here, the value comes from a *lookup*, and in general — as the next section shows — a chain of lookups.

**Rust analogy.** This is precisely what a trait + trait bound + coherent `impl` gives you:

```rust
trait Mul {
    fn mul(&self, other: &Self) -> Self;
}
impl Mul for u64 {
    fn mul(&self, other: &Self) -> Self { self.wrapping_mul(*other) }
}
// generic fn requiring the trait — the compiler *finds* the right impl
fn double<T: Mul + Clone>(x: T) -> T { x.mul(&x.clone()) }
```

`impl Mul for u64` is exactly `nat_has_mul [instance]`, and the trait-bound resolution that lets `double::<u64>` compile is exactly the class-inference search that solves `?M : has_mul nat`. The difference is that in Lean's setting, `has_mul` is a first-class term (a record `Type`), not a special compiler-only concept, and the "instances" you can chain over can themselves be data-dependent, not just type-dependent.

**Python analogy.** Think of it as an explicit, declared version of what `functools.singledispatch` does implicitly by runtime type — except the "dispatch table" here is resolved once, statically, at elaboration time, and can itself require solving further placeholders (the next section) rather than a single flat type match.

## Backward chaining: instances that depend on instances

The search only becomes interesting once instance declarations are allowed to have their own implicit class arguments. Consider:

```
structure semigroup [class] (A : Type) extends has_mul A :=
(mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))
```

Declaring `semigroup` this way *automatically* makes `semigroup A` an instance of `has_mul A` (a semigroup obviously has a multiplication — it extends the structure). So if `nat` is declared an instance of `semigroup` but *not* directly of `has_mul`, class inference can still solve `?M : has_mul nat` — it just takes two steps: use the `semigroup`-to-`has_mul` extension instance, which in turn needs a `semigroup nat` instance, which is found directly. The paper is explicit about what kind of search this is: **backward-chaining, Prolog-like search**. Each instance declaration is effectively a Horn clause — "if you can produce instances of these arguments, you can produce an instance of this class" — and solving `?M : C args` means treating `C args` as a goal and chasing declared clauses backward until every subgoal bottoms out in something already known.

This is exactly what lets a whole algebraic hierarchy compose for free:

```
structure group [class] (A : Type)
          extends monoid A, has_inv A :=
(mul_left_inv : ∀ a, mul (inv a) a = one)
```

Since every group is a monoid and every monoid is a semigroup, a *generic* theorem proved once about semigroups (say, `mul.assoc`) applies automatically to any type the user has only ever declared to be a `group`. The user never restates or re-derives associativity for groups — class inference chains `group → monoid → semigroup` the same way it chained `semigroup → has_mul` above, silently, at elaboration time, inside ordinary proof terms:

```
theorem eq_inv_of_eq_inv {A : Type} [s : group A] {a b : A}
                         (H : a = b⁻¹) : b = a⁻¹ :=
by rewrite [H, inv_inv]
```

Here `inv_inv`'s own implicit `[s : group A]` argument, and the ambient one used by `rewrite`, are both resolved by the same backward-chaining search — invisibly, as part of elaborating an ordinary tactic proof.

**Lean-flavored pseudocode for the search itself**, stripped to its logical shape (this is genuinely a tiny Prolog interpreter over a fixed clause database, as the paper puts it in Section 3.5):

```
-- goal: find a term of type `C args`
resolve(goal):
    for instance in database matching goal.head:
        -- instance : Π (h1 : G1) ... (hn : Gn), C args
        subgoals := [G1, ..., Gn]           -- may themselves be class goals
        if all subgoals in subgoals resolve to terms t1, ..., tn:
            return instance t1 ... tn
    fail  -- backtrack to try the next matching instance
```

Backtracking over "the next matching instance" is what makes this genuinely a search rather than a single deterministic lookup — and it's why, later in the paper (Section 3.6), class-inference goals are folded into the same nonchronological-backtracking constraint solver used for unification, rather than being handled by a separate bolted-on mechanism.

## Fully bundled structures and coercion-assisted resolution

Lean also supports an alternative style, borrowed from the Mathematical Components library, where the carrier type is packaged *inside* the structure rather than passed separately:

```
structure Group := (carrier : Type) (struct : group carrier)

attribute Group.carrier [coercion]
attribute Group.struct [instance]
```

This declares that whenever you have `G : Group`, you can silently write `g : G` (Lean coerces `G` to `Group.carrier G` — a preview of the coercion machinery, covered under [[Overloading-and-Coercions|Overloading and Coercions]]), and whenever you have `g : carrier G`, class resolution can find `struct G` as the relevant `group` structure automatically. The two mechanisms — coercion and class inference — are declared as attributes on the same structure and cooperate seamlessly, which is a useful preview of just how uniformly this constraint-based elaborator treats what look, from the outside, like unrelated language features.

## Beyond notation: type classes as a control-flow mechanism

The examples above use class inference to resolve *notation* (which `*` to use) and *generic theorems* (which `mul_assoc` applies). But nothing in the mechanism restricts it to that — the paper's most striking example uses it to synthesize genuinely computational, data-carrying content: a decision procedure.

```
inductive decidable [class] (p : Prop) : Type :=
| inl : p → decidable p
| inr : ¬p → decidable p
```

Note carefully: `decidable p` lives in `Type`, not `Prop`. That distinction matters — a bare proof of `p ∨ ¬p` (classically always available) can't be *computed with*, but a term of `decidable p` carries an actual algorithm that decides which side holds, and can be pattern-matched on to produce data. This is what lets `if`-expressions be first-class and computable:

```
definition ite (c : Prop) [H : decidable c] {A : Type} (t e : A) : A :=
decidable.rec_on H (λ Hc, t) (λ Hnc, e)
```

`if c then t else e` is literally notation for `ite c t e`, and the implicit `[H : decidable c]` argument — the actual decision procedure for `c` — is synthesized by class inference exactly like `has_mul nat` was, via instances like

```
nat.decidable_eq [instance] : ∀ x y : nat, decidable (x = y)
```

Composed with decidability instances closed under boolean connectives and bounded quantification, this lets a term like

```
example : ∀ x : nat, x < 10 → x ≠ 10 ∧ x < 12 := dec_trivial
```

typecheck: class inference finds a decision procedure for the whole compound proposition (chaining through `∧`, `<`, `≠` instances), and computational reduction (see [[Computational-Behavior-and-Reduction|Computational Behavior and Reduction]]) evaluates it down to `true`, at which point the canonical proof `trivial` closes the goal. The `decidable` class is what lets Lean move smoothly between constructive and classical reasoning: classically every proposition is decidable, but only a *declared, computed* `decidable` instance actually lets a term reduce.

**Python analogy for the constructive/classical distinction.** `decidable p` is closer to Python's `bool(x)` returning an actual `True`/`False` you can branch on at runtime, versus merely being told, abstractly, "this expression is either truthy or falsy" without a way to evaluate it — the type-theoretic point being that `Type`-valued decidability *is* the evaluator, bundled with its own proof of correctness.

## How the elaborator's internals actually carry this out

Everything above describes class inference from the outside. Internally (Section 3, and see [[Constraints-and-Justifications|Constraints and Justifications]] and [[The-Preprocessing-Phase|The Preprocessing Phase]] for the fuller picture), a class-inference obligation like `?M : has_mul nat` is represented as a special kind of constraint — a **choice constraint** `⟨?m ℓ : t in f, j⟩`, where `f` is a procedure that, given the metavariable's expected type, produces a stream of candidate solutions. Ordinary overloading (see [[Overloading-and-Coercions|Overloading and Coercions]]) also uses choice constraints, but class-inference and coercion choice constraints are marked **`ondemand`**: the solver is instructed *not* to try synthesizing a value until the constraint's type `t` is fully free of other unresolved metavariables. Only once `t` has stabilized does the solver invoke `f`, which — per Section 3.5 — "is essentially a simple λ-Prolog interpreter, where the Horn clauses are the user-declared instances," precisely the backward-chaining search sketched above. This `ondemand` flag is the concrete, implementation-level answer to a real design tension: resolving a class goal *too early*, before its type is pinned down, risks committing to the wrong instance or exploring a huge, underconstrained search space; the elaborator's global priority queue (`ready ≺ regular ≺ ...`, detailed in [[The-Constraint-Solving-Procedure|The Constraint Solving Procedure]]) is precisely what lets class-inference goals wait their turn until they're safe to attempt.

## Synthesis

Type-class resolution is what turns Lean's elaborator from "a system that infers what you clearly meant" into "a system that can also *look things up* on your behalf." It sits on exactly the same constraint-solving infrastructure as unification-based implicit-argument inference (both ultimately populate metavariables), but the *content* of the search is different in kind: backward-chaining over a user-extensible database rather than syntactic matching. That's what makes generic algebraic reasoning (`semigroup` facts applying to `group`s for free), operator overloading via `*`, and computable case analysis via `decidable` all instances — pun intended — of one uniform mechanism. Downstream, this is the same machinery [[Overloading-and-Coercions|Overloading and Coercions]] leans on for coercion [[The-Elaboration-Task#Synthesis|synthesis]], and it feeds directly into the constraint categories (`ready`, `regular`, `postponed`) that the solver's priority queue has to schedule correctly.
