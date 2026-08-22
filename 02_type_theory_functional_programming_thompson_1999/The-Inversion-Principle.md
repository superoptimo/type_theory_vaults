---
title: "The Inversion Principle Relating Introduction and Elimination Rules"
source: "Type Theory and Functional Programming (Thompson, 1999)"
chapter: "Chapter 8, §8.4 (pp. 326–330)"
tags: [type-theory, inversion-principle, elimination-rules, inductive-definitions, proof-theory]
---

[[book-guidelines|↩ Back to guidelines]] · [[Model-Theory|See also: Model Theory]] · [[Well-Founded-and-General-Recursion|See also: Well-Founded and General Recursion]]

## Why should the elimination rule be *derivable*, not stipulated?

Every type in $TT$ gets introduced by up to four kinds of rule: a **formation** rule (how to build the type expression itself), one or more **introduction** rules (how to build elements of it), and then an **elimination** rule paired with a **computation** rule (how to *use* an element, and what happens when you use one built by an introduction rule).

The first three of these feel like design choices — you decide what $A \vee B$ *is* and how to build one. But by the time you've written down the introduction rules, have you actually made a further choice in writing the elimination rule, or have you already said everything there is to say?

Thompson's answer is: you've already said everything. If the introduction rules for $\vee$ exhaustively describe every way a proof of $A \vee B$ could have arisen — either from a proof of $A$ via $inl$, or from a proof of $B$ via $inr$, and *no other way* — then "what can you validly conclude from a proof of $A \vee B$" is not a free design decision. It's a mechanical consequence of the introduction rules, obtainable by **inversion**: turn the introduction rules around, and the elimination rule falls out. This idea traces to Gentzen, and was developed rigorously for first-order intuitionistic logic by Schroeder-Heister ([SH83a], [SH83b]).

**What breaks without this:** without a principled derivation, a type theorist has to hand-design an elimination rule for every new connective and separately *prove* it's neither too strong (admits contradictions) nor too weak (fails to capture everything the introduction rules license). Inversion turns "invent, then verify" into "compute" — and, as you'll see in the closing section, it turns out to connect directly to how a modern proof assistant *generates* eliminators from constructors rather than requiring the implementer to write them.

## Working the derivation on $\vee$

Take the informal logical rule for disjunction elimination — proof by cases. If you can derive $C$ assuming $A$, and separately derive $C$ assuming $B$, then $C$ follows from $A \vee B$ itself:

$$
\begin{array}{c}
[A] \quad\quad [B] \\
\vdots \quad\quad \vdots \\
(A \vee B) \quad C \quad\quad C \\
\hline
C
\end{array}
\quad (\vee E')
$$

Lifted to type theory, where propositions carry explicit proof *objects*, this becomes:

$$
\begin{array}{c}
[x:A] \quad\quad [y:B] \\
\vdots \quad\quad\quad \vdots \\
p:(A\vee B) \quad u:C \quad\quad v:C \\
\hline
\mathrm{vcases}'_{x,y}\, p\, u\, v : C
\end{array}
\quad (\vee E')
$$

This isn't just a proof-existence statement anymore — $\mathrm{vcases}'_{x,y}\, p\, u\, v$ is a genuine new expression, binding $x$ in $u$ and $y$ in $v$. But it's *simplifiable*: any $p : A \vee B$ actually is either $inl\ a$ or $inr\ b$ (that's what the introduction rules guarantee), so the term should reduce accordingly:

$$
\mathrm{vcases}'_{x,y}\,(inl\ a)\, u\, v \to u[a/x] \qquad\qquad \mathrm{vcases}'_{x,y}\,(inr\ b)\, u\, v \to v[b/y]
$$

That reduction rule is the **computation rule** — and notice it, too, was forced, not chosen: it's just "substitute the constructor's argument into whichever branch matches."

## The general schema

Thompson generalizes this pattern mechanically. Suppose a connective $\theta$ has exactly $n$ introduction rules, one per constructor $K_i$:

$$
\dfrac{y_{i,1}:H_{i,1} \quad \ldots \quad y_{i,m_i}:H_{i,m_i}}{K_i\, y_{i,1} \ldots y_{i,m_i} : \varphi} \quad (\theta I_i)
$$

where $\varphi = \theta\, A_1 \ldots A_k$. Since these $n$ rules are declared to be the *only* ways to build an element of $\varphi$, a proof of $C$ from $\varphi$ can be assembled from $n$ hypothetical proofs of $C$ — one per constructor, each allowed to assume that constructor's argument types:

$$
\dfrac{p:\varphi \quad\quad
\begin{array}{c}[y_{i,1}:H_{i,1}\ \ldots\ y_{i,m_i}:H_{i,m_i}]\\ \vdots \\ p_i : C\end{array}
\ \text{(for each $i=1,\dots,n$)}}
{\theta\text{-}elim\; p\; p_1 \ldots p_n : C} \quad (\theta E)
$$

with the matching computation rule:

$$
\theta\text{-}elim\;(K_i\, a_1 \ldots a_{m_i})\; p_1 \ldots p_n \to p_i[a_1/y_{i,1}, \ldots, a_{m_i}/y_{i,m_i}]
$$

This is a recipe, and Thompson runs it on conjunction to show it isn't special-cased for disjunction. $\wedge$ has a single introduction rule $(\wedge I)$, so the schema hands back a single-branch eliminator $\wedge\text{-}elim_{x,y}\, p\, c$ with computation rule $\wedge\text{-}elim_{x,y}\,(a,b)\, c \to c[a/x, b/y]$. Setting $c := x$ recovers the familiar projection $\mathit{fst}$ as $\lambda p.\, \wedge\text{-}elim_{x,y}\, p\, x$ — the generated rule is exactly as strong as, and interderivable with, the "obvious" hand-written elimination rule you'd have picked anyway.

## Where inversion works — and where it stalls

The recipe above handles the existential quantifier, the finite types $N_n$, the natural numbers, and every well-founded type built like lists and trees — precisely the $\mathrm{Ind}$-style inductively-defined types from §7.10 (see [[Well-Founded-and-General-Recursion]]). It notably does **not** apply to the naive subset-elimination rule $(SetE)$ from Chapter 7 — the subset type's elimination behavior isn't determined by inversion on its introduction rule alone, which is part of why subsets keep causing trouble throughout the book.

There's a second, structural obstruction, independent of any particular connective: rules whose *introduction* rule **discharges a hypothesis**. Implication is the paradigm case —

$$
\dfrac{\begin{array}{c}[A]\\ \vdots \\ B\end{array}}{A \Rightarrow B} \quad (\Rightarrow I)
$$

— and the same issue recurs for universal quantification. Naively running the schema above on $\Rightarrow$ doesn't typecheck as a rule, because the schema as stated only knows how to bind *object-level* variables ($y_{i,j}$ ranging over terms), not to bind an entire *hypothetical derivation* the way $(\Rightarrow I)$'s premise does.

### Hypothetical hypotheses

The fix — due independently to Schroeder-Heister [SH83a] and Backhouse [Bac86], and first seen in this book at §7.7.2 — is to add a new kind of term to the system: **hypothetical hypotheses**, written $\{\Gamma \vdash J\}$, meaning "this is introduced by exhibiting a derivation of judgement $J$ in context $\Gamma$":

$$
\dfrac{\begin{array}{c}[\Gamma]\\ \vdots \\ J\end{array}}{\{\Gamma\vdash J\}} \quad (I)
\qquad\qquad
\dfrac{\{\Gamma\vdash J\}\quad \Gamma[t_1/x_1,\ldots,t_n/x_n]}{J[t_1/x_1,\ldots,t_n/x_n]} \quad (E)
$$

With this extra machinery, implication's elimination rule *does* invert cleanly, recovering (a dependently-typed, variable-binding-aware version of) modus ponens:

$$
\dfrac{f:A\Rightarrow B \quad\quad \dfrac{[\{x{:}A \vdash (e\cdot x){:}B\}]\quad\vdots\quad (c\cdot e):C}{}}{\mathrm{expand}\ f\ c : C} \quad (\Rightarrow E')
\qquad\qquad
\mathrm{expand}\,(\lambda\, g)\, c \to c \cdot g
$$

(Here $\Lambda$/$\cdot$ are meta-level abstraction/application, distinct from the object-language $\lambda$, needed to state the binding precisely — the book flags this notational care explicitly, since getting variable capture right in a rule that binds a *function*, not just a value, is exactly the kind of thing that's easy to get subtly wrong.)

### How far does the *general* method reach?

Backhouse offered inversion principles beyond this, but Thompson notes an open problem in his approach: it's not always decidable whether his method yields a *consistent* system, especially once recursive types are in play. Dybjer's later, more general treatment ([Dyb89]) reframes the whole question: **every type in $TT$ other than the universes can be presented as arising from a system of inductive definitions in the ambient logical framework** — and inversion is really a special case of a broader semantic fact:

> If a proposed type can be presented as a **positive** inductive definition, then consistent elimination and computation rules for it can be derived automatically.

That word "positive" should ring a bell — it's the exact same positivity condition that shows up in [[Model-Theory]] §8.2.3, where Allen's naive inductive-definition semantics for type theory failed for precisely this reason (the equality relation appeared in the *hypothesis* of an implication, a negative position, breaking the guarantee of a least fixed point). Here the same condition governs something different but structurally identical: whether an elimination rule can be safely auto-derived at all. Positive occurrence, in both places, is what keeps an inductively-defined thing from being ill-founded or paradoxical. Dybjer's framework also handles parametrized and simultaneously-defined type families — sanctioning constructions like [Dyc85]'s, though still not the subset or quotient types.

Thompson closes the section with a completeness remark for intuitionistic logic, echoing the classical fact that $\{\neg, \Rightarrow\}$ or $\{\neg, \wedge\}$ suffice to express every propositional connective: Schroeder-Heister [SH83b] shows $\{\wedge, \vee, \Rightarrow, \neg, \exists, \forall\}$ is sufficient to define every connective whose introduction/elimination rules obey the inversion principle described in this section.

## Grounding: this is exactly how a proof assistant generates eliminators

If you've ever written an `inductive` declaration in a dependently-typed proof assistant and gotten a recursor/eliminator for free, you have already watched this section's algorithm run.

### Lean: the `inductive` command *is* the inversion schema

**Lean** never asks you to hand-write an elimination principle for a new inductive type — it generates `T.rec` (and the derived `T.casesOn`, `T.recAux`, etc.) mechanically from the constructor signatures, using exactly the "one hypothetical branch per constructor, substitute the matching constructor's arguments" schema this section derives by hand:

```lean
inductive Sum (A B : Type) where
  | inl : A → Sum A B
  | inr : B → Sum A B

-- Lean auto-generates, schematically, the eliminator implied by exactly
-- the two constructors above — this is θ-elim, specialized to n = 2:
--
-- Sum.rec : {C : Sum A B → Sort u} →
--   ((a : A) → C (Sum.inl a)) →   -- the "θI₁" branch
--   ((b : B) → C (Sum.inr b)) →   -- the "θI₂" branch
--   (p : Sum A B) → C p

-- The computation rule is iota-reduction, and it's forced,
-- not designed, exactly as Thompson's schema forces it:
example (a : A) (f : (a:A) → C (Sum.inl a)) (g : (b:B) → C (Sum.inr b)) :
    Sum.rec f g (Sum.inl a) = f a := rfl
```

Positivity is enforced by Lean's kernel as a hard precondition on accepting the `inductive` declaration at all — the same check that would reject a naive encoding of the subset type's problematic elimination behavior, and the same one flagged in [[Model-Theory]]. When Dybjer says "if it's a positive inductive definition, elimination and computation rules follow automatically," he is describing, almost verbatim, what Lean's elaborator does every time you write `inductive`.

### Rust: implementing the schema as a code generator

If you were implementing this mechanism yourself — the load-bearing case for a meta-programming elaborator — you'd write exactly this transformation: read off constructor signatures, emit one eliminator branch per constructor, and generate the substitution-based reduction rule as the "match" behavior:

```rust
struct Constructor {
    name: String,
    arg_types: Vec<Type>,   // the H_{i,1} .. H_{i,m_i}
}

struct InductiveDef {
    type_name: String,
    constructors: Vec<Constructor>,
}

// Mechanically derive the eliminator's TYPE from the constructors —
// this is θE, generated rather than hand-designed.
fn derive_eliminator_signature(def: &InductiveDef, motive: &Type) -> Type {
    // one hypothetical-branch parameter per constructor,
    // each abstracted over that constructor's own argument types
    todo!()
}

// The computation rule: given a concrete constructor application,
// pick its branch and substitute — this is θ-elim's reduction rule.
fn eliminate(scrutinee_ctor: &str, ctor_args: &[Term], branches: &[Term]) -> Term {
    todo!() // substitute ctor_args into the matching branch
}
```

### Python: the same idea as pattern-match desugaring

```python
def eliminate(ctor_tag, ctor_args, branches):
    # branches[ctor_tag] is the hypothetical proof/function for that constructor
    return branches[ctor_tag](*ctor_args)  # theta-elim's computation rule, bare
```

## Where this leads

This section is the mechanism, not just a piece of proof theory: it's the reason a modern elaborator can accept a constructor list and hand back a working `match`/`rec` without a human ever writing an elimination rule by hand — which is exactly the "mechanism, not just theory" reading this material is worth for a compiler/elaborator project. The positivity requirement threading through both this section and [[Model-Theory]]'s §8.2.3 is the same guard-rail wearing two hats — semantic well-foundedness there, syntactic termination/consistency of a generated eliminator here — and it's worth remembering as one fact, not two coincidentally similar ones. And the boundary this section draws (inversion works for $\vee, \wedge, \exists, N, N_n$, well-founded types; it does *not* save you for subsets or quotients) previews exactly which of Chapter 7's augmented constructs Chapter 9 will need special-cased justification for, rather than getting it for free.
