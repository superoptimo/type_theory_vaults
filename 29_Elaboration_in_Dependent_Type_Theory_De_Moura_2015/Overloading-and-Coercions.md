---
title: Overloading and Coercions
source: Elaboration in Dependent Type Theory (de Moura, Avigad, Kong, Roux, 2015)
chapters: "Sections 2.5-2.6 (pp. 8-10); mechanism grounded in Section 3.5 (pp. 19-20)"
tags: [type-theory, elaboration, overloading, coercions, lean, unification]
---

[[book-guidelines|↩ Back to guidelines]]

## Two ways to reuse a symbol

[[Type-Classes-and-Class-Inference|Type class inference]] already solves one flavor of "reuse the same notation for different things": `*` means multiplication for `nat`, `int`, or any type with a registered `has_mul` instance, and the elaborator threads the right implementation through via a synthesized instance argument. The paper calls this *parametric polymorphism* — one definition, one implementation-search mechanism, many types.

But there's a second, cruder flavor that type classes can't cover: what if two symbols denote genuinely unrelated things that just happen to share a name or a piece of notation, with no common structure to search over? `++` on lists means "concatenate two lists"; `++` on tuples means "concatenate two tuples of possibly different fixed lengths." These aren't two instances of one abstract "appendable" class — the underlying operations, and even their type shapes, are unrelated enough that forcing them into a shared class interface would be artificial. Lean's answer is *ad hoc polymorphism*: let the same identifier or notation name several unrelated definitions at once, and push the job of picking the right one onto the elaborator.

This matters because it's the same move, structurally, as *coercions* — inserting an implicit conversion function so that a term written as if it had one type can be used where another type was expected. Both overloading and coercions are, from the elaborator's point of view, ways of turning "the user wrote something under-determined" into "search a small space of candidate resolutions and pick the one that type-checks." Section 2 introduces them together because they're solved by the same underlying constraint-search machinery you'll meet properly in [[The-Preprocessing-Phase|preprocessing]] and [[The-Constraint-Solving-Procedure|constraint solving]].

## Overloading: same name, unrelated meanings

Concretely, `++` is declared once for `list` and once for `tuple`:

```
import data.list data.tuple
open list tuple

variables (A : Type) (m n : N)
variables (v : tuple A m) (w : tuple A n) (s t : list A)

check s ++ t
check v ++ w
```

Both `check`s type-check, but the elaborator resolves `++` to a *different* underlying constant in each — `list.append` in the first case, `tuple.append` in the second — purely by looking at what type-checks given the arguments' types. No trait-style dispatch table is involved; the "resolution" is closer to overload resolution in a language like C++ or Rust's inherent-method lookup among several `impl` blocks with the same method name, except here it's driven by full unification against the argument types rather than a fixed set of primitive-type rules.

When the ambiguity can't be resolved automatically — two candidates both type-check, or the user wants to be explicit — Lean lets a namespace prefix disambiguate directly:

```
check λ x y, (#list x + y)
check λ x y, (#tuples x + y)
```

The same mechanism handles overloaded plain identifiers, not just notation. If `foo` is defined in both namespace `a` and namespace `b`, and both namespaces are opened, then the bare name `foo` refers ambiguously to `a.foo` and `b.foo` simultaneously — and it's the elaborator's job, not the parser's, to pick between them based on where `foo` is used.

**Why not just always use type classes?** Ad hoc overloading is strictly more flexible than class-based overloading, precisely because it drops the requirement that the overloaded meanings share a structural interface. The paper's own example: in the standard library, `⁻¹` denotes the inverse operation for algebraic structures that have one (groups, and anything built on `group`), *and* it denotes the symmetry operation on equality proofs (`Eq.symm`), *and* it inverts bijections, group isomorphisms, ring isomorphisms, and categorical equivalences. There is no single class `has_inv` that meaningfully unifies "invert a group element" and "flip the direction of a proof of equality" — they're related only by informal analogy ("both undo something"), which is exactly the kind of relationship type classes cannot express but ad hoc overloading can piggyback on for free. The cost is that overloading "adds ambiguity and choice points to the elaboration process" — every overloaded occurrence is a fork the solver may have to explore — so the paper's guidance is to use it sparingly, reserved for cases like this where reuse is genuinely convenient and the alternative (inventing a spurious shared class) would be worse.

## Coercions: same value, different type

A coercion is a user-declared function the elaborator is allowed to insert *silently* when a term of type $C$ appears somewhere a term of type $A$ is expected, and $C \ne A$ syntactically but a designated conversion function $c : C \to A$ exists. The motivating cases are mundane: `bool` coerces to `nat` (`ff ↦ 0`, `tt ↦ 1`), `nat` coerces to `int`, and mixed-type list literals like `[n, i, m, j]` (some entries `nat`, some `int`) elaborate by coercing every `nat` entry up to `int` so the list has a single element type.

Lean allows three *kinds* of coercions, distinguished by what the target class is:

- **Family to family** — from a family of types indexed one way to a family of types indexed another way, e.g. `nat → int`. This lets you view an element of one type as an element of a related type directly.
- **Family to the class of sorts** — a coercion whose codomain is `Type` itself, letting an element of the source family be used *as a type*. This is what lets `Group.carrier` be declared `[coercion]` (seen already in the [[Type-Classes-and-Class-Inference|type-class discussion]]): a term `G : Group` can then appear anywhere a type is expected, standing in for `carrier G`.
- **Family to the class of function types** — a coercion whose codomain is a $\Pi$-type, letting an element of the source family be *applied as a function*. A bundled homomorphism record, for instance, can be coerced to its underlying function so `f x` makes sense even though `f` is technically a record, not a raw function.

These three kinds mirror exactly the three roles a term can play in dependent type theory — as a value, as a type, as a function — which is why three (and not some arbitrary larger number) is the natural stopping point; anywhere a term can occur in one of those three roles, a coercion can silently substitute a different-but-convertible term playing the same role.

**A composite example.** The paper's running illustration — composing two natural transformations between functors, `θ • η : F ⟹ H` given `η : F ⟹ G` and `θ : G ⟹ H` — needs coercions from *all three* kinds working together with overloading and class inference in a single elaboration: the functors `F`, `G`, `H` get coerced to their action on morphisms (family-to-function-types), the natural transformations `η` and `θ` get coerced to their first component (family-to-family or family-to-function, depending on the bundling), and the notation `•` itself is overloaded/class-resolved to mean "vertical composition of natural transformations" rather than any of its other uses. No single mechanism produces a term this compact — it's the union of all the outward-facing tasks from this section acting together that lets a categorical composition read almost exactly as a mathematician would write it on paper.

## How the elaborator actually decides to insert a coercion

Both overloading and coercion resolution bottom out in the same internal machine: [[Constraints-and-Justifications|choice constraints]], processed during [[The-Preprocessing-Phase|preprocessing]]. When the preprocessor elaborates an application `(r s)`, it uses `ensurefun` to pin down that `r`'s type has the shape $\Pi x : A,\, B$, then checks whether $s$'s type $C$ is convertible to $A$. Three outcomes are possible:

1. **$C$ converts to $A$ directly.** Nothing to do — this is the ordinary, coercion-free case.
2. **$C$ does not convert to $A$, but $A$ is not stuck, and a coercion $c : C \to A$ is registered.** The preprocessor rewrites `(r s)` to `(r (c s))` immediately — a deterministic, no-search insertion, since there's exactly one applicable coercion and nothing left to solve for.
3. **$A$ is stuck (its head is an unresolved metavariable, so the preprocessor can't yet tell which coercion would even apply), but there exist candidate coercions $c_1, \dots, c_n$ out of $C$.** Rather than guess, the preprocessor defers: it creates a fresh metavariable `?m` for the eventual argument, rewrites the application to `(r (?m ℓ))`, and emits an **ondemand choice constraint** `⟨?m ℓ : A in f, j⟩`, where the choice function `f` enumerates the alternatives — the uncoerced `s`, `c₁ s`, …, `cₙ s`. The solver, once other constraints have pinned down enough of `A` to make `f` deterministic, invokes it and (ideally) gets back exactly one candidate that type-checks; only if that fails does the solver need to backtrack across genuinely alternative choices.

Ad hoc overloading reuses this exact same choice-constraint machinery: instead of `f` enumerating coercions of a single argument, `f` enumerates the different definitions the overloaded identifier could refer to (`list.append`, `tuple.append`, …), and the solver picks whichever one lets the surrounding constraints resolve. The only asymmetry the paper flags is practical, not structural: coercion choice constraints are usually `ondemand` (solved lazily, once other information narrows `A`), while overloading more often uses a **regular** choice constraint, since there is typically nothing else to wait for — the identifier's surrounding argument types are already enough to disambiguate immediately. One current limitation the paper is explicit about: if *both* the target type $A$ and the source type $C$ are still stuck at the moment the application is preprocessed, no coercion is inserted at all — there simply isn't enough information yet to even enumerate the candidates.

## Where this fits

Overloading and coercions sit alongside [[Type-Classes-and-Class-Inference|type class inference]] as the three outward-facing mechanisms Lean uses to let notation and identifiers carry more meaning than their literal type would allow — and internally, all three compile down to the same choice-constraint apparatus that [[The-Constraint-Solving-Procedure|the constraint solver]] processes. Understanding coercion insertion here is a direct prerequisite for [[The-Preprocessing-Phase]], since the `ensurefun`/coercion-lookup step described above *is* one of preprocessing's core responsibilities — and it foreshadows why choice constraints, unlike unification constraints, need their own priority tier and their own care around when it's safe to commit to an answer.
