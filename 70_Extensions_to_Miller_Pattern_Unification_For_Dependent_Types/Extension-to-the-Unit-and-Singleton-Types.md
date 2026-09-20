---
title: Extension to the Unit and Singleton Types
source: "Extensions to Miller's Pattern Unification for Dependent Types and Records (Abel & Pientka)"
chapter: "Chapter 5 — Extension to Unit Type"
pages: "22–26"
tags: [type-theory, unification, dependent-types, singleton-types, elaboration]
---

[[book-guidelines|↩ Back to guidelines]]

## Why the unifier needs to know about the unit type at all

Back up to the paper's whole project: it wants to unify record-typed problems by rewriting $\Sigma$-types away, via the isomorphism $\Pi z{:}(\Sigma x{:}A.B).C \cong \Pi x{:}A.\Pi y{:}B.[(x,y)/z]C$. That trick handles *non-empty* records fine — split a pair into two components, recurse. But an empty record — one with zero fields, `struct Unit {}` in Rust terms, or `type Unit = ()` if you like — doesn't decompose into anything. It has to be modeled directly: as the unit type $1$, with a single canonical inhabitant $\star$ (the paper's $\star$, sometimes written $\langle\rangle$). Without $1$, every "record with a trailing empty tail" that shows up in a Σ-encoding has nowhere to bottom out. So this section fills the one remaining gap in "reduce records to Π/Σ": the base case of the recursion.

But the paper doesn't stop at the unit type narrowly. It generalizes to **singleton types**: any type with *exactly one inhabitant up to $\eta$-equality*. That generalization matters because $\Pi$- and $\Sigma$-types built entirely out of singletons are themselves singletons (e.g. $\Pi x{:}A.\,\mathrm{Unit}$, a function into the unit type, has exactly one inhabitant too — the constant function returning $\star$). If you only special-cased the literal unit type, these composite singletons would slip through as ordinary non-degenerate types, and the exact same problems would resurface one level up. So the paper solves the general case once.

### What breaks without this

Here's the concrete failure mode the paper leads with. Ordinary $\eta$-equality is supposed to be a *congruence that never touches free variables* — $\eta$-expanding or contracting a term changes its shape but never changes which variables occur free in it. Every earlier part of the algorithm (the occurs check, pruning, substitution inversion) silently leans on that invariant. Singleton types break it outright:

$$\frac{\Delta;\Phi \vdash M \Leftarrow 1}{\Delta;\Phi \vdash M =_\eta \star : 1}$$

Any term $M : 1$ — no matter what variables it mentions — is $\eta$-equal to the bare inhabitant $\star$, which mentions *no* variables. So if some meta-variable's argument happens to have unit type, a free variable can vanish under $\eta$-equality. Concretely: suppose you're trying to solve $u[x] = M$ where $M$ contains a stray occurrence of some other variable $y$ buried inside a subterm of type $1$. Naively, the occurs/scope check sees $y \notin \{x\}$ and reports the constraint unsolvable — pattern-unification failure. But that's wrong: that subterm is $\eta$-equal to $\star$, which mentions no $y$ at all, so the constraint was solvable all along. Reject it and you've turned a solvable unification problem into a spurious type-checking failure. Rust analogy: it's like a compiler refusing to unify two closures because one of them captures a variable in a branch of code that's provably unreachable — the capture is real syntactically but irrelevant semantically, and a unifier that doesn't know that will bail too early.

## Singleton types, defined structurally

$$
\begin{array}{ccc}
1\ \mathrm{sing} & \dfrac{B\ \mathrm{sing}}{\Pi x{:}A.\,B\ \mathrm{sing}} & \dfrac{A\ \mathrm{sing} \quad B\ \mathrm{sing}}{\Sigma x{:}A.\,B\ \mathrm{sing}}
\end{array}
$$

with canonical inhabitants defined by the same recursion:

$$\star_1 = \star \qquad \star_{\Pi x:A.B} = \lambda x.\,\star_B \qquad \star_{\Sigma x:A.B} = (\star_A, \star_B)$$

Read the rules in words: $1$ is trivially a singleton. A $\Pi$-type is a singleton exactly when its *codomain* is (note: no constraint on the domain $A$ — a function *from* anything *into* a singleton is still forced to be the unique constant function). A $\Sigma$-type is a singleton exactly when *both* components are (both fields must be individually unique, otherwise the pair has more than one possible shape).

**Lemma 5.1 (Soundness of the singleton predicate).** If $A\ \mathrm{sing}$:
1. $\Delta;\Psi \vdash \star_A \Leftarrow A$ — the canonical inhabitant really does have type $A$.
2. If $\Delta;\Psi \vdash M, N \Leftarrow A$ then $\Delta;\Psi \vdash M =_\eta N : A$ — *any two* inhabitants of a singleton type are $\eta$-equal, not just each one to $\star_A$.

This second clause is the one that licenses everything downstream: it means that wherever a singleton-typed subterm appears in a constraint, you're free to replace it by $\star_A$ without changing the meaning of the constraint. That's the mechanism the rest of the section exploits repeatedly.

**Rust/Lean framing.** This is a *proof-irrelevance*-flavored idea, but purely at the level of definitional equality, not a separate sort. In Lean's kernel, this is closest to what happens with `Unit`/`PUnit` and, more generally, with structure types that have a single constructor whose fields are themselves forced — `whnf`/`isDefEq` on two terms of such a type can short-circuit to `true` without inspecting them, because the type itself proves they're equal. If you were encoding this invariant as a Rust trait bound, you'd want a marker `trait Singleton` that your unifier's `unify(a, b)` checks *before* doing structural comparison: `if T::IS_SINGLETON { return Ok(()) }`, skipping the entire recursive walk. That's a real optimization in this space, not just a theoretical curiosity — an elaborator that special-cases singleton types can prune large swaths of otherwise-expensive unification work.

## Type-directed $\eta$-contraction: making $\eta$-equality decidable in the presence of singletons

Recall from Chapter 3 (see [[Constraint-Based-Unification-as-an-Inference-System]]) that the algorithm solves a constraint $\Psi \vdash u[\sigma] = M : C$ by first checking whether the substitution $\sigma$ is (equivalent to) a *variable* substitution $\rho$ — only then can it invert $\rho$ and read off a solution for $u$. Before singletons entered the picture, checking "is this term $\eta$-equal to a variable" was comparatively simple, because $\eta$-equality never touched which variables occurred. Now it can — a subterm of singleton type can be silently discarded during contraction — so the naive check breaks, and the paper needs a genuinely new **type-directed $\eta$-contraction judgment**.

First, three extra $\eta$-like laws, needed precisely because functions/pairs *containing* a singleton component (without being singletons themselves) can still shed arguments:

$$
\begin{array}{ll}
\Psi \vdash \lambda x.\,M\ N =_\eta M : \Pi x{:}B.\,C & \text{(if } B\ \mathrm{sing}, x \notin \mathrm{FV}(M)\text{, justified by } \Psi,x{:}B \vdash N =_\eta x : B\text{)} \\
\Psi \vdash (N, \mathrm{snd}\ M) =_\eta M : \Sigma x{:}B.\,C & \text{(if } B\ \mathrm{sing}\text{, justified by } \Psi \vdash N =_\eta \mathrm{fst}\ M : B\text{)} \\
\Psi \vdash (\mathrm{fst}\ M, N) =_\eta M : \Sigma x{:}A.\,B & \text{(if } B\ \mathrm{sing}\text{, justified by } \Psi \vdash N =_\eta \mathrm{snd}\ M : [\mathrm{fst}\ M/x]B\text{)}
\end{array}
$$

In words: if a $\Pi$'s *domain* is a singleton, you can drop an application to any argument $N$ whatsoever (since $N$ is forced equal to whatever the bound variable would have been) — that's the mirror image of the ordinary $\eta$-law for functions, but triggered by the *domain*, not the codomain. Similarly for pairs: if one component's type is a singleton, that component contributes nothing to determining pair-equality, so you can freely swap it in from the other side of the equation.

The actual judgment is $\Psi \vdash M \gg E[x] \Leftarrow A$ (paper's notation; the skill's guidelines file uses $\gg$ for the same relation described there as $M \Rightarrow E[x]$) — **defined only for non-singleton $A$** (a singleton-typed term is trivially $\eta$-equal to *any* variable of that type, so the question "does it contract to a *specific* variable" doesn't even make sense there; it would be underdetermined). Given a term $M$ of non-singleton type $A$, it produces a neutral term $E[x]$ headed by a variable $x$, such that $M =_\eta E[x] : A$.

Figure 6's three rules:

```
Ψ ⊢ E[x] ⇐ A
──────────────────────  (already neutral, variable-headed)
Ψ ⊢ E[x] ↠ E[x] ⇐ A

A sing    Ψ ⊢ [★_A/y]M ↠ E[x] N ⇐ [★_A/y]B    Ψ ⊢ E[x] ⇒ Πy:A.B
─────────────────────────────────────────────────────────────  (domain is a singleton: substitute it away, recurse)
Ψ ⊢ λy.M ↠ E[x] ⇐ Πy:A.B

not A sing   Ψ,y:A ⊢ M ↠ E[x] N ⇐ B   Ψ ⊢ E[x] ⇒ Πy:A.B   Ψ ⊢ N =η y : A
─────────────────────────────────────────────────────────────────────  (ordinary η-contraction case)
Ψ ⊢ λy.M ↠ E[x] ⇐ Πy:A.B

Ψ ⊢ M₁ ↠ fst E[x] ⇐ A  (unless A sing)    Ψ ⊢ M₂ ↠ snd E[x] ⇐ [M₁/y]B  (unless B sing)
─────────────────────────────────────────────────────────────────────────────────────  (pair case)
Ψ ⊢ (M₁,M₂) ↠ E[x] ⇐ Σy:A.B
```

Walk the lambda case carefully, because it's the crux of the whole extension. Given $\lambda y.M$ of type $\Pi y{:}A.B$:

- **If $A$ is a singleton**, you can't just try to $\eta$-contract $M$ as-is, because $y$ itself might occur in $M$ in a way that ordinary contraction can't see past. Instead you *substitute the canonical inhabitant for $y$* — $[\star_A/y]M$ — eliminating the singleton-typed bound variable outright, then recursively contract *that*. If the recursive call succeeds and hands back an application $E[x]\,N$ at the *same* function type, then by soundness of the singleton predicate that argument $N$ must be $\eta$-equal to whatever $y$ would have contributed, and you can report $E[x]$ directly — the abstraction $\lambda y.M$ is $\eta$-equal to $E[x]$.
- **If $A$ is not a singleton**, this reduces to the classical $\eta$-contraction rule you'd expect without any of this machinery: try to contract the body $M$ (under the extended context $\Psi,y{:}A$) to some $E[x]\,N$ at the right type, and check the argument $N$ is literally $\eta$-equal to the bound variable $y$ — that's the usual "$\lambda y.\,f\,y \rightsquigarrow f$" contraction.

The pair case is the dual move: try to contract each component separately to a projection off a *common* neutral $E[x]$, but *skip the check entirely* on whichever component has singleton type (since it's automatically compatible with anything).

### Worked example from the source

The paper's own illustration, given the context $x : \ldots$ and target

$$x : \ldots \vdash \lambda y.\lambda z.\,x\,(\mathrm{fst}\ y, z)\,z \;=_\eta\; x \;:\; \Pi y{:}(\Sigma\_{:}A.\,1).\,\Pi z{:}1.\,B$$

Step through it: the outer abstraction binds $y : \Sigma\_{:}A.1$ — not a singleton (its first component $A$ isn't assumed to be one), so we're in the "ordinary" branch and recurse into the body under $\Psi, y{:}\Sigma\_{:}A.1$, trying to reduce $\lambda z.\,x\,(\mathrm{fst}\ y,z)\,z$ to $E[x]\,N$ with $N =_\eta y$. That inner abstraction binds $z : 1$ — a singleton! — so we substitute $\star$ for $z$ and recurse on $x\,(\mathrm{fst}\ y, \star)\,\star$, which is already neutral and variable-headed, giving $E[x] = x\,(\mathrm{fst}\ y,\star)$ trivially by the first rule. Popping back up: we need $(\mathrm{fst}\ y, \star) =_\eta y : \Sigma\_{:}A.1$ — which holds by exactly the singleton pair-$\eta$ law above, since the *second* component of the $\Sigma$ is $1$, a singleton, so the second-component check is waived and only $\mathrm{fst}\ y =_\eta \mathrm{fst}\ y$ needs to hold (trivial). So the full contraction succeeds down to the bare variable $x$.

The derivation tree as given:

$$
\dfrac{
  \dfrac{
    x:\ldots \vdash x\,(\mathrm{fst}\ y,\star)\,\star \gg x\,(\mathrm{fst}\ y,\star)\,\star \Leftarrow [\star/z]B
  }{
    x:\ldots, y{:}\Sigma\_{:}A.1 \vdash \lambda z.\,x\,(\mathrm{fst}\ y,z)\,z \gg x\,(\mathrm{fst}\ y,\star) \Leftarrow \Pi z{:}1.B
  } \quad (*)
}{
  x:\ldots \vdash \lambda y.\lambda z.\,x\,(\mathrm{fst}\ y,z)\,z \gg x \Leftarrow \Pi y{:}(\Sigma\_{:}A.1).\Pi z{:}1.B
}
$$

where $(*) = x:\ldots, y{:}\Sigma\_{:}A.1 \vdash (\mathrm{fst}\ y,\star) =_\eta y : \Sigma\_{:}A.1$.

**Lemma 5.2 (η-contraction to variable).** For non-singleton $A$:
1. **Soundness** — if $\Psi \vdash M \gg E[x] \Leftarrow A$ then $\Psi \vdash M =_\eta E[x] : A$ (the algorithm's output is actually correct).
2. **Completeness** — if $\Psi \vdash M =_\eta E[x] : A$ then the algorithm finds *some* $E'[x]$ $\eta$-equal to it; in particular if $M =_\eta x$ outright, the algorithm finds exactly $x$ (no useful contraction is ever missed).
3. **Termination** — the query always terminates (by induction on the type $A$).
4. **Decidability** — falls out of 1–3: "does $M$ contract to *some* variable at all" is a decidable question, answered by just running the algorithm.

This is the standard soundness/completeness/termination/decidability quartet you should expect of any well-behaved decision procedure — the paper is careful to establish all four, not just "it usually works," because the whole unifier's correctness argument (Chapter 4) depends on every auxiliary judgment being this well-behaved.

**Lean framing.** This whole judgment is doing, very explicitly, the job that Lean's elaborator does silently whenever it needs to check `isDefEq` between a lambda and something else — Lean's WHNF-based defeq checker performs analogous eta-contraction internally, just without exposing a separate named judgment for "eta-contract to a variable head." Seeing it spelled out here as its own inference system is a good model for what a hand-rolled `isDefEq`/eta-reduction pass needs to account for once your kernel has *any* type with a degenerate (unit-like or provably-unique) structure — think `PUnit`, but also, more relevantly for a refinement-type compiler, any singleton subtype carved out by a trivial refinement predicate (`{x : Int | True}` is exactly a singleton-shaped type modulo the refinement machinery).

## Patching the algorithm: five new transitions

With type-directed $\eta$-contraction in hand, the paper slots five new rewrite rules into the constraint-solving system from Chapter 3 (see [[Constraint-Based-Unification-as-an-Inference-System]]). Each patches exactly one place where singleton types could otherwise corrupt an existing rule.

**(1) Decomposing away singleton equations entirely.**
$$\Phi \vdash M = N : A \;\mapsto_d\; \top \quad \text{if } A\ \mathrm{sing}$$
If two terms are being compared at a singleton type, there's nothing to check — Lemma 5.1(2) already guarantees they're equal. Delete the constraint outright.

**(2) Eliminating singleton subterms from the right-hand side.**
$$\Phi \vdash u[\sigma] = M : C \;\mapsto_e\; \Phi \vdash u[\sigma] = M' : C \quad \text{if } \Phi \vdash M =_\eta M' : C \text{ and } M'\text{ sing-free but } M\text{ isn't}$$
where "$M$ sing-free" means every subterm of $M$ at singleton type has already been rewritten down to its canonical $\star_A$. This is the direct fix for the motivating failure mode: before running the occurs check or pruning against $M$, first launder out every singleton-typed subterm, so that any free variable hiding inside one can never wrongly trigger a scope failure.

**(3) The occurs check, now conditioned on sing-freedom.**
$$\Delta \Vdash K \wedge \Psi \vdash u[\rho] = M : C \;\mapsto\; \bot \quad \text{if } \mathrm{FV}(M) \not\subseteq \rho \text{ (and } M \text{ is already sing-free)}$$
Exactly the old occurs-check failure rule from Chapter 3 — but it's now only sound to apply *after* rule (2) has cleaned $M$ up. That ordering dependency is precisely what closes the gap identified earlier: a variable that only occurred inside a singleton subterm never reaches this check at all, because (2) already erased it.

**(4) $\eta$-contraction of the meta-variable's substitution, now type-directed.**
$$\Psi \vdash u[\sigma] = N : A \;\mapsto_e\; \Psi \vdash u[\rho] = N : A \quad \text{if } \Psi \vdash \sigma \gg \rho \Leftarrow \Phi$$
This replaces the older, simpler $\eta$-contraction step from Chapter 3 with one that calls the new type-directed judgment (extended pointwise from single terms to whole substitutions) — needed because a substitution's components can themselves be singleton-typed and need the same careful treatment as the worked example above.

**(5) Solving singleton meta-variables immediately.**
$$\Delta \Vdash K \;\mapsto\; \Delta \Vdash K + (\Phi \vdash u \leftarrow \star_A : A) \quad \text{if } A\ \mathrm{sing}$$
If a meta-variable's *own* declared type is a singleton, there is exactly one possible value it could ever take — solve it right now, unconditionally, without waiting for any constraint to mention it. This is a genuine "free win": singleton-typed metavariables never need to participate in unification proper at all.

The paper is explicit that these five rules cover every place singleton types could interfere: (1) and (3) patch **the type of a constraint**, (2) and (4) patch **the terms inside a constraint**, and (5) patches **the type of a meta-variable declaration** — a clean, exhaustive case split over "everywhere a type can appear in the unifier's data structures."

### Optional: pruning singleton variables from contexts

The paper also notes two further transitions (6)–(7), which go one step *further* than strictly necessary: they eliminate singleton-typed *variables* from contexts altogether, rather than just from the terms of constraints.

$$\Phi_1, x{:}A, \Phi_2 \vdash M = N : C \;\mapsto_p\; \Phi_1, [\tau]\Phi_2 \vdash [\tau]M = [\tau]N : [\tau]C \quad \text{if } A\ \mathrm{sing},\ \tau = [\star_A/x]$$

and the analogous pruning-based version (7) that strips a singleton variable out of a meta-variable's own context by substitution rather than by direct rewriting. The paper flags these as *optional*: "singleton variables in contexts are harmless as long as we apply (2) to eliminate their occurrences in constraints" — i.e., rules (1)–(5) alone are already sound and complete; (6)–(7) are a cleanup/efficiency measure, not a correctness requirement. Worth remembering if you're implementing this: you get a fully correct unifier from the first five rules, and can add context-pruning later purely as a performance optimization.

## Synthesis: where this sits in the algorithm, and why it matters for the compiler

```
Chapter 3: constraints, decomposition, η-contraction, lowering, pruning, solving
                              │
                              │  (assumed: η-equality preserves free variables)
                              ▼
Chapter 5: unit/singleton types break that assumption
                              │
        ┌─────────────────────┼─────────────────────┐
        ▼                     ▼                      ▼
  type-directed          5 patched              (optional)
  η-contraction    →   transitions (1)-(5)  →   context pruning
  M ↠ E[x] ⇐ A       into Ch. 3's system         of singletons (6)-(7)
        │
        ▼
  Chapter 4's correctness proof must be re-checked
  against these new transitions (termination weight,
  solution-preservation, typing-preservation)
```

This section is a small piece of the paper by page count (5 of ~27 pages) but it's a template for a general engineering lesson: *every* extension to a unification algorithm has to be checked against the algorithm's own invariants, not just against "does it produce the right answer on this example." The unit/singleton extension is exactly the case where a seemingly harmless addition (one more base type!) silently invalidates an invariant (η-equality preserves free variables) that half the existing machinery depends on.

For the `type-theory`-tagged goals this book serves: this section is the most direct, self-contained worked example in the whole paper of **definitional equality doing more than syntactic comparison** — precisely the behavior your elaborator's `isDefEq`/unifier needs to replicate for any type with a provably-unique inhabitant, which is not just `Unit` but any refinement type whose predicate pins down a single value (a case that will come up routinely once you're doing constraint-based inference for refinement types, since a sufficiently precise refinement is exactly a singleton type in this sense). The pattern to carry forward into the compiler: *before* running your occurs check or scope check against a term, first normalize away every singleton-typed subterm to its canonical inhabitant — otherwise your elaborator will spuriously reject implicit-argument solutions that are perfectly valid up to definitional equality, exactly the bug this section exists to prevent.

## Where this leads

With Chapter 5, the paper has now handled the full record-unification story: non-empty records via the Σ-Π isomorphism (Chapter 3/[[Type-Isomorphisms-for-Dependent-Records]]), and empty records via the unit-type extension here. Chapter 4's correctness results ([[Correctness of the Unification Algorithm]], not yet in this vault under that exact name) are implicitly extended to cover these five new transitions, and Chapter 6/7 (Related Work, Conclusion) go on to report that exactly this machinery — Σ-type and unit-type unification — is what got shipped into Beluga's context-block flattening and Agda 2's record unification.
