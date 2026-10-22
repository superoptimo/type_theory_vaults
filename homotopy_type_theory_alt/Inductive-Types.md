---
title: Inductive Types
book: Homotopy Type Theory - Univalent Foundations of Mathematics
chapters: "Chapter 5 (printed pp. 149–178)"
tags: [type-theory, inductive-types, W-types, initial-algebras, strict-positivity, inductive-families]
---

[[book-guidelines|↩ Back to guidelines]]

# Inductive Types

## 1. Why this chapter exists

Chapter 1 introduced $\mathbf{0}, \mathbf{1}, \mathbf{2}, A\times B, A+B, \Sigma, \mathbb{N}$ one at a time, each with its own formation, introduction, elimination and computation rules. The book observes that, apart from $\Pi$-types and universes, *all of them are instances of one scheme*: an **inductive definition**. Chapter 5 studies that scheme directly, for three reasons:

1. A user of a proof assistant needs to *define new types*, so we need to know which "definitions" are legitimate and what rules they generate.
2. The homotopical reading asks for more than the rules. Inductive types should be characterized by a universal property that holds up to *coherent* homotopy.
3. The same machinery explains identity types, so path induction becomes a special case rather than a primitive oddity.

The chapter is also the bridge to Chapter 6 ([[Higher-Inductive-Types|higher inductive types]]). It fixes the "free generation" picture that Chapter 6 then relaxes.

## 2. Free generation, induction, recursion

**Intuition.** An inductive type $X$ is *freely generated* by a finite list of constructors, each a function with codomain $X$ (zero-argument constructors are just elements). Elements are exactly what you get by applying constructors repeatedly. The book lists constructors with bullets:

- $\mathbf{2}$: $0_{\mathbf{2}}, 1_{\mathbf{2}} : \mathbf{2}$
- $\mathbf{1}$: $\star : \mathbf{1}$, and $\mathbf{0}$ has no constructors
- $A + B$: $\mathsf{inl} : A \to A+B$, $\mathsf{inr} : B \to A+B$
- $A \times B$: $(-,-) : A \to B \to A\times B$
- $\mathbb{N}$: $0 : \mathbb{N}$, $\mathsf{succ} : \mathbb{N} \to \mathbb{N}$
- $\mathsf{List}(A)$: $\mathsf{nil}$, $\mathsf{cons} : A \to \mathsf{List}(A) \to \mathsf{List}(A)$

"Every element comes from a constructor" is not asserted directly. It is *expressed* by the **induction principle** (dependent elimination rule). For $\mathbb{N}$: to prove $E : \mathbb{N}\to\mathcal{U}$ for all $n$, give $e_z : E(0)$ and $e_s : \prod_{n:\mathbb{N}} E(n) \to E(\mathsf{succ}(n))$. The result $\mathsf{ind}_{\mathbb{N}}(E, e_z, e_s) : \prod_{x:\mathbb{N}}E(x)$ obeys the **judgmental computation rules**

$$\mathsf{ind}_{\mathbb{N}}(E,e_z,e_s,0) \equiv e_z,\qquad \mathsf{ind}_{\mathbb{N}}(E,e_z,e_s,\mathsf{succ}(n)) \equiv e_s(n,\mathsf{ind}_{\mathbb{N}}(E,e_z,e_s,n)).$$

The **recursion principle** is the special case where $E$ is a constant family. The book calls the induction principle the *eliminator* and the recursion principle the *non-dependent eliminator*.

### Grounding

Rust: the recursion principle is a fold. The "motive" $E$ disappears because Rust is not dependently typed, but the recurrence arguments are visible.

```rust
enum Nat { Zero, Succ(Box<Nat>) }

// rec_N(C, c0, cs): non-dependent eliminator
fn rec_nat<C>(n: &Nat, c0: C, cs: &dyn Fn(C) -> C) -> C {
    match n {
        Nat::Zero => c0,
        Nat::Succ(p) => cs(rec_nat(p, c0, cs)),
    }
}
```

Python: the same fold with a recursive call; the book's "recurrence $e_s(n, \text{recursive value})$" is the two-argument step function.

```python
def ind_nat(e_z, e_s, n):
    return e_z if n == 0 else e_s(n - 1, ind_nat(e_z, e_s, n - 1))
```

Lean: `Nat.rec` is exactly $\mathsf{ind}_{\mathbb{N}}$, with the motive explicit.

```lean
#check @Nat.rec
-- {motive : Nat → Sort u} → motive Nat.zero →
--   ((n : Nat) → motive n → motive n.succ) → (t : Nat) → motive t
```

## 3. Uniqueness of functions and of the type itself

**Theorem 5.1.1.** If $f,g : \prod_{x:\mathbb{N}}E(x)$ both satisfy the recurrences $e_z, e_s$ *up to propositional equality*, then $f = g$. Proof: induction on $D(x) :\equiv f(x)=g(x)$, with function extensionality at the end. The induction principle therefore proves its own uniqueness principle.

**Uniqueness of the type (§5.2).** Take a second type $\mathbb{N}'$ with identical-looking constructors. The recursion principles give $f :\equiv \mathsf{rec}_{\mathbb{N}}(\mathbb{N}',0',\lambda n.\mathsf{succ}')$ and $g :\equiv \mathsf{rec}_{\mathbb{N}'}(\mathbb{N},0,\lambda n.\mathsf{succ})$. Since $g\circ f$ satisfies the recurrences of $\mathsf{id}$, Theorem 5.1.1 gives $g\circ f = \mathsf{id}$ and symmetrically $f\circ g=\mathsf{id}$. So $\mathbb{N}\simeq\mathbb{N}'$, and **by univalence** $\mathbb{N}=_{\mathcal{U}}\mathbb{N}'$. Transport along this path then moves *every* function, lemma and proof from $\mathbb{N}$ to $\mathbb{N}'$ at once, with no "priming" of duplicates.

The argument does not require identical definitions, only that one induction principle implies the other. The book's example is $\mathsf{List}(\mathbf{1})$ with $0'' :\equiv \mathsf{nil}$ and $\mathsf{succ}''(\ell) :\equiv \mathsf{cons}(\star,\ell)$. The same reasoning shows $A+B \simeq \sum_{x:\mathbf{2}}\mathsf{rec}_{\mathbf{2}}(\mathcal{U},A,B,x)$, and in general any $W'$ satisfying the induction principle of $W$ is equivalent to $W$.

**Why it matters:** this is "same universal property ⇒ equivalent", which §5.4 makes literal.

## 4. $W$-types: the one recursive pattern

Martin-Löf's $W$-types (well-founded trees) are the special case through which the book says all inductive types can formally be reduced (the reduction itself is out of scope). Parameters: $A:\mathcal{U}$ (labels) and $B:A\to\mathcal{U}$ (arity of each label). One constructor:

$$\mathsf{sup} : \prod_{a:A}\bigl(B(a)\to W_{(x:A)}B(x)\bigr)\to W_{(x:A)}B(x).$$

A node labelled $a$ has $B(a)$-many children, supplied as a function $f : B(a)\to W$. Examples from the book:

$$\mathbb{N}^{\mathsf{w}} :\equiv W_{(b:\mathbf{2})}\mathsf{rec}_{\mathbf{2}}(\mathcal{U},\mathbf{0},\mathbf{1},b),\qquad \mathsf{List}(A) :\equiv W_{(x:\mathbf{1}+A)}\mathsf{rec}_{\mathbf{1}+A}(\mathcal{U},\mathbf{0},\lambda a.\mathbf{1},x),$$

with $0^{\mathsf{w}} :\equiv \mathsf{sup}(0_{\mathbf{2}},\lambda x.\mathsf{rec}_{\mathbf{0}}(\mathbb{N}^{\mathsf{w}},x))$ and $\mathsf{succ}^{\mathsf{w}} :\equiv \lambda n.\mathsf{sup}(1_{\mathbf{2}},\lambda x.n)$.

**Induction.** To prove $E$ for $\mathsf{sup}(a,f)$ it suffices to give

$$e : \prod_{a:A}\prod_{f:B(a)\to W}\Bigl(\prod_{b:B(a)}E(f(b))\Bigr)\to E(\mathsf{sup}(a,f)),$$

where the middle hypothesis is the inductive hypothesis for *every* child. The computation rule is

$$\mathsf{rec}(E,e,\mathsf{sup}(a,f)) \equiv e\bigl(a,f,\lambda b.\,\mathsf{rec}(E,e,f(b))\bigr).$$

Theorem 5.3.1 gives the same propositional uniqueness as for $\mathbb{N}$. The book works through $\mathsf{double}$ on $\mathbb{N}^{\mathsf{w}}$ by case analysis on the label ($e_0 :\equiv \lambda f.\lambda g.0^{\mathsf{w}}$, $e_1 :\equiv \lambda f.\lambda g.\mathsf{succ}^{\mathsf{w}}(\mathsf{succ}^{\mathsf{w}}(g(\star)))$).

### Grounding

Rust: a $W$-type is "a node tag plus a child *function*". Finite arities collapse to a `Vec`, but the infinitary case (e.g. $(\mathbb{N}\to W)\to W$) genuinely needs a closure.

```rust
// W_{a:A} B(a): tag A, children indexed by B(a), here modelled as a closure.
struct W<A, B> {
    label: A,
    children: Box<dyn Fn(B) -> W<A, B>>,
}
```

Lean: the kernel does not take $W$-types as primitive. It takes general inductive declarations (with a recursor generated per declaration), and `W` can be defined as one. This matches the book's remark that $W$-types are the representative case.

```lean
inductive W (A : Type) (B : A → Type) where
  | sup (a : A) (f : B a → W A B) : W A B
```

## 5. Inductive types are initial algebras (§5.4)

**Intuition.** "Freely generated" has a categorical meaning: the constructors make the type the *initial* object among types with the same structure.

- An **$\mathbb{N}$-algebra** is $(C,c_0,c_s)$ with $c_0:C$, $c_s:C\to C$, so $\mathsf{NAlg}:\equiv\sum_{C:\mathcal{U}}C\times(C\to C)$.
- An **$\mathbb{N}$-homomorphism** $(C,c_0,c_s)\to(D,d_0,d_s)$ is $h:C\to D$ with $h(c_0)=d_0$ and $h(c_s(c))=d_s(h(c))$ for all $c$.
- $I$ is **homotopy-initial** (h-initial) if for every algebra $C$ the type $\mathsf{NHom}(I,C)$ is *contractible*: $\mathsf{isHinit}_{\mathbb{N}}(I):\equiv\prod_{C:\mathsf{NAlg}}\mathsf{isContr}(\mathsf{NHom}(I,C))$.

Note that this asks for a *contractible type* of homomorphisms (an element plus uniqueness up to higher paths), not just "unique".

- **Theorem 5.4.4.** Any two h-initial $\mathbb{N}$-algebras are *equal* (univalence), and "being h-initial" is a mere proposition.
- **Theorem 5.4.5.** $(\mathbb{N},0,\mathsf{succ})$ is h-initial: $\mathsf{rec}_{\mathbb{N}}$ gives the centre of contraction, and Theorem 5.1.1 gives uniqueness.

For general $W$-types the relevant endofunctor is the **polynomial functor** $P(X)=\sum_{x:A}(B(x)\to X)$. A $P$-algebra is a type $C$ with $s_C:PC\to C$, so $\mathsf{WAlg}(A,B):\equiv\sum_{C:\mathcal{U}}\prod_{a:A}(B(a)\to C)\to C$. A homomorphism satisfies $f(s_C(a,h)) = s_D(a,f\circ h)$. **Theorem 5.4.7**: $(W,\mathsf{sup})$ is h-initial. The proof sketch needs algebra 2-cells (the coherence data $s_e$ between pasting diagrams), which is why homotopy-initiality is a stronger statement than ordinary initiality.

In the $\mathbb{N}$ case the endofunctor is $F(X)=X+\mathbf{1}$, the textbook "natural numbers object".

## 6. Homotopy-inductive types (§5.5)

**The problem.** Encode $\mathbb{N}$ as $\mathbb{N}^{\mathsf{w}}$. Recursion works, but for the *induction* principle one can only construct functions that satisfy the recurrences **propositionally** (up to a path). The judgmental computation rules for $\mathbb{N}$ cannot be derived from those of $W$-types in any obvious way.

**The fix.** Consider *homotopy-inductive types*, where every computation rule is stated with $=$ instead of $\equiv$. The trade-off is explicit in the book: computational behavior of functions built by induction is then only characterized propositionally. Benefits:

- Every h-initial algebra *is* a homotopy-inductive type (but not every h-initial algebra satisfies the strict induction principle).
- The uniqueness argument of §5.2 applies even when one of the types is only homotopy-inductive, e.g. $\mathbb{N}^{\mathsf{w}}\simeq\mathbb{N}$.
- The notion becomes *internal*: you can form the type of all natural-number objects.

Three characterizations of the homotopy $W$-type are given: $W^{\mathsf d}(A,B)$ (induction with propositional computation), $W^{\mathsf s}(A,B)$ (recursion + computation + uniqueness + coherence law, the last two postulated since uniqueness is not derivable from recursion alone), and $W^{\mathsf h}(A,B)$ (h-initial algebra). Theorems 5.5.1–5.5.3 say each is a mere proposition; **Lemma 5.5.4** says $W^{\mathsf d}\simeq W^{\mathsf s}\simeq W^{\mathsf h}$; **Theorem 5.5.5**: types satisfying the formation, introduction, elimination and *propositional* computation rules are precisely the h-initial $W$-algebras; **Theorem 5.5.6**: $\mathbb{N}$ with propositional computation can be derived from $W$-types with propositional computation. Most proofs are omitted in the book ("somewhat technical").

## 7. Which definitions are legal: positivity (§5.6)

Not everything that looks inductive is valid. The book gives a sequence of increasingly subtle failures:

1. **A constructor $g:(C\to\mathbb{N})\to C$**: contravariant occurrence of $C$. The recursion principle cannot even be stated, since "apply $f$ to $\alpha$" has no meaning when both have domain $C$. Ignoring the recursive occurrence (taking $h:(C\to\mathbb{N})\to P$ with $\mathsf{rec}_C(P,h,g(\alpha))\equiv h(\alpha)$) gives a statable rule, but the resulting type is *inconsistent* (Exercises 5.7–5.10).
2. **Covariance is necessary but not sufficient.** Double negative positions are covariant: $k:((D\to\mathsf{Prop})\to\mathsf{Prop})\to D$. With $r(k(\theta)):\equiv\theta$, $f(\delta):\equiv k(\lambda x.(x=\delta))$, $p(\delta):\equiv\lambda x.\delta(f(x))$, one shows $f$ is injective, $p(\delta)=\theta$ for $\delta(d):\equiv\exists\gamma.(f(\gamma)=d)\times\theta(\gamma)$, and then diagonalizes with $\theta(\gamma):\equiv\neg p(\gamma)(\gamma)$ to get $P\Leftrightarrow\neg P$. This is Cantor's paradox. (Remark 5.6.3: in a predicative setting the contradiction also needs propositional resizing, §3.5.)
3. **Strict positivity.** The type being defined may never occur to the left of an arrow in a constructor argument, even nested; the same applies to dependent function types. Each argument is then either a type not involving $W$ or an iterated function type *with codomain $W$*. The book's example is

$$c : (A\to W)\to(B\to C\to W)\to D\to W\to W.$$

Footnote 1 ties this to the categorical view: strict positivity makes the endofunctor *polynomial*, and not all endofunctors have initial algebras.

Other constraints: a finite list of constructors (infinitely many are simulated by parametrizing, e.g. $\mathbb{N}\to W\to W$), and the type lives in a universe containing everything used in its definition.

**Derived rules.** For example (5.6.4) the recursion principle needs $d:(A\to W)\to(A\to P)\to(B\to C\to W)\to(B\to C\to P)\to D\to W\to P\to P$, with computation rule $f(c(\alpha,\beta,\delta,\omega))\equiv d(\alpha,f\circ\alpha,\beta,f\circ\beta,\delta,\omega,f(\omega))$. For induction, each "recursive call" hypothesis is replaced by a *dependent* function, e.g. $\prod_{a:A}P(\alpha(a))$. The book deliberately declines to give a formal grammar of valid definitions ("necessary if implementing a computer proof assistant, but provides no additional insight").

### Grounding

Rust: the strict-positivity check is a recursive walk over a constructor's argument types. The sketch below is original and illustrative (not from the book, not compiled), and ignores universe levels and parameters.

```rust
enum Ty { Const, Ind, Arrow(Box<Ty>, Box<Ty>) } // Ind = occurrence of the type being defined

fn occurs(t: &Ty) -> bool {
    match t { Ty::Ind => true, Ty::Const => false,
              Ty::Arrow(a, b) => occurs(a) || occurs(b) }
}

// Argument allowed iff: no Ind at all, or it is  X1 -> ... -> Xn -> Ind
// with no Ind in any domain Xi.
fn strictly_positive(t: &Ty) -> bool {
    match t {
        Ty::Const | Ty::Ind => true,
        Ty::Arrow(dom, cod) => !occurs(dom) && strictly_positive(cod),
    }
}
```

Lean: the kernel rejects the book's bad examples with a positivity error.

```lean
-- rejected: "(kernel) arg #1 of 'Bad.mk' has a non positive occurrence"
inductive Bad where
  | mk : (Bad → Nat) → Bad
```

## 8. Generalizations (§5.7)

- **Parameters vs. indices.** $A+B$ and $\mathsf{List}(A)$ are families *parametrized* by types, each member inductively defined independently. **Inductive families** like vectors define the whole family together, because constructors change the index: $\mathsf{nil}:\mathsf{Vec}_0(A)$, $\mathsf{cons}:\prod_{n:\mathbb{N}}A\to\mathsf{Vec}_n(A)\to\mathsf{Vec}_{\mathsf{succ}(n)}(A)$. Its induction principle quantifies over $n$ and the vector: $C:\prod_{n:\mathbb{N}}\mathsf{Vec}_n(A)\to\mathcal{U}$ with $c_{\mathsf{nil}}:C(0,\mathsf{nil})$ and $c_{\mathsf{cons}}$ giving $C(\mathsf{succ}(n),\mathsf{cons}(a,\ell))$.
- **Inductive predicates**: $\mathsf{iseven}:\mathbb{N}\to\mathcal{U}$ with $\mathsf{even}_0:\mathsf{iseven}(0)$ and $\mathsf{even}_{ss}:\prod_n\mathsf{iseven}(n)\to\mathsf{iseven}(\mathsf{succ}(\mathsf{succ}(n)))$. The book notes that proving $\neg\mathsf{iseven}(1)$ is "not entirely trivial".
- **Mutual induction**: when the index type is finite it is equivalent to an inductive family indexed by it (e.g. $\mathsf{paritynat}:\mathbf{2}\to\mathcal{U}$ for even/odd); the induction principle must be applied to both at once.
- **Inductive-inductive** definitions (indices defined simultaneously with the indexed types) and **inductive-recursive** definitions (a type and a function on it defined together). The book states it does not yet know how to justify the latter homotopically and does not use them. Higher inductive-inductive types appear in Chapter 11.

### Grounding

Lean: indexed families are native, and this is the form used by dependently typed checkers.

```lean
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

inductive IsEven : Nat → Prop where
  | zero : IsEven 0
  | ss   : IsEven n → IsEven (n + 2)
```

Rust: the closest approximation uses type-level naturals (`typenum` or const generics); the index is erased at runtime, which is the usual "indices are proofs, parameters are data" split.

## 9. Identity types as an inductive family (§5.8)

The identity type is an inductive family with $A$ as a **parameter** and two **indices**, generated by a single constructor $\mathsf{refl}_a : a=_A a$. Extracting the induction principle gives exactly **path induction**: for $C:\prod_{a,b:A}(a=_A b)\to\mathcal{U}$ and $d:\prod_{a:A}C(a,a,\mathsf{refl}_a)$ there is $f$ with $f(a,a,\mathsf{refl}_a)\equiv d(a)$. Fixing $a_0$ as a parameter (one index) gives **based path induction**.

**The apparent paradox.** The "every element is built by constructors" intuition fails here: there is one constructor but not every path is $\mathsf{refl}$. Counterexample: the path $\mathbf{2}=_{\mathcal{U}}\mathbf{2}$ from univalence that is not $\mathsf{refl}_{\mathbf{2}}$ (Example 3.1.9). The book's resolution: "freely generated" really means free *with respect to all operations of the ambient structure*. Types now have operations on *paths* (concatenation, inversion, etc.) but none on *elements*, so $\mathbf{2}$ and $\mathbb{N}$ still contain only constructor-built elements. But a type *family* is a functor, and a functor acts on morphisms. So $(a_0=_A -)$ is the functor *freely generated by one element of $F(a_0)$*, which by Yoneda is the representable functor $\hom_A(a_0,-)$, i.e. the path space.

**Identity systems.** For a pointed predicate $(R,r_0)$ over $(A,a_0)$ (a family $R:A\to\mathcal{U}$ with $r_0:R(a_0)$), an **identity system** is one satisfying the path induction principle. **Theorem 5.8.2** gives equivalent characterizations: (i) identity system; (ii) $\mathsf{ppmap}(R,S)$ is contractible for every pointed $S$; (iii) $\mathsf{transport}^R(-,r_0):(a_0=_A b)\to R(b)$ is an equivalence for all $b$; (iv) $\sum_{b:A}R(b)$ is contractible. Statement (iv) is the practical test used throughout Chapter 8's encode-decode proofs.

## 10. Synthesis

**Dependencies.**

```
Ch.1 constructors / eliminators ─┐
Ch.2 univalence, funext ─────────┼─► Ch.5 uniqueness (§5.1–5.2), h-initiality (§5.4)
Ch.3 mere props, contractibility ┘            │
                                              ├─► §5.5 propositional computation (→ motivates Ch.6)
                                              ├─► §5.6 strict positivity, rec/ind schema
                                              ├─► §5.7 families, mutual, ind-ind
                                              └─► §5.8 identity systems ─► Ch.8 encode-decode
```

**How this bears on the compiler/elaborator project (Focus Area: `type-theory`).** This topic is load-bearing in the following places; the first three are the ones I would treat as prerequisites rather than background:

- **The kernel's inductive-declaration checker.** The positivity analysis, universe-level check ("lives in a universe containing all constituent types") and the recursor/eliminator *generation* of §5.6 (types (5.6.5) and (5.6.7)) are exactly the code a Rust kernel needs. Lean's kernel does this: it accepts inductive declarations plus parameters/indices, and *generates* `T.rec`. The $W$-type of §5.3 is the book's argument that this one scheme suffices.
- **Computation rules as reduction rules.** The judgmental equations such as (5.6.6) are the $\iota$-reduction rules of the kernel's `isDefEq` (definitional equality). Section 5.5 shows what would be lost if they were only propositional: reduction would no longer be able to fire.
- **Pattern matching elaboration.** The book states that pattern-matching definitions are repackaged as applications of $\mathsf{ind}_W$ with the recursive-call variables $\bar\alpha,\bar\beta,\bar\omega$. That compilation is what an elaborator for a surface language performs (Lean's equation compiler / structural recursion works this way), and it needs bidirectional checking against the motive.
- **Inductive families and indices** are the ones the refinement-type surface language will want (e.g. a length-indexed vector, `IsEven`-style inductive predicates for specifications). Index unification is where the elaborator's unifier is exercised (Focus Area `automated-reasoning`: unification), though the book itself does not discuss that algorithm.

Connections to the required list: inductive types, $\Pi$/$\Sigma$-types (as the shape of the eliminator's hypotheses), definitional equality (computation rules), judgments (formation/introduction/elimination/computation as judgment forms), trusted kernels.

**Not covered by the book here, so not claimed:** an algorithm for checking positivity, universe-level bookkeeping details, and index unification. The Rust and Lean snippets above are original illustrations.
