---
title: "The Lambda Cube of Type Systems"
source: "Type Theory and Formal Proof: An Introduction (Nederpelt & Geuvers, 2014)"
chapters: "3–6 (Second order typed lambda calculus, Types dependent on types, Types dependent on terms, The Calculus of Constructions)"
pages: "69–136"
tags: [type-theory, lambda-calculus, dependent-types, pure-type-systems, calculus-of-constructions, lean, rust]
---

# The Lambda Cube of Type Systems

[[book-guidelines|↩ Back to guidelines]]

## Why $\lambda\to$ isn't enough

[[The-Simply-Typed-Lambda-Calculus|The simply typed lambda calculus]], $\lambda\to$, is a well-behaved little machine: every term is strongly normalizing, every typable term has a unique type, type checking is decidable. But it is also cripplingly rigid. Consider the identity function. In $\lambda\to$ you can write $\lambda x : \mathsf{nat}.\, x$, or $\lambda x : \mathsf{bool}.\, x$, or $\lambda x : (\mathsf{nat}\to\mathsf{bool}).\, x$ — one identity function per type, and no way to write "the" identity function once and for all. If you try the obvious move and pick an arbitrary type $\alpha$, writing $f \equiv \lambda x : \alpha.\, x$, you get stuck the moment you want to apply $f$ to something concrete: $f\ 3$ isn't legal, because $\alpha$ was never bound to anything — it's a free type variable floating outside the system's syntax.

This single failure mode — *the calculus has no way to abstract over the thing that makes types vary* — turns out to have several independent flavors, and each flavor demands a different kind of generalization:

1. **Terms can't abstract over types.** You can't write a function that is generic in its input type. Fix: let terms depend on types. This is **$\lambda 2$** (Chapter 3).
2. **Types can't abstract over types.** You can't write a "type-level function" like *"pair this type with itself"* as a first-class object. Fix: let types depend on types. This is **$\lambda\omega$** (Chapter 4).
3. **Types can't abstract over terms.** You can't write a type like *"vectors of length $n$"* where $n$ is a runtime value, or a predicate like *"$n$ is prime"* as a type-valued function on naturals. Fix: let types depend on terms. This is **$\lambda P$** (Chapter 5).

Each of these three extensions is orthogonal — you can add any subset of them to $\lambda\to$ — and adding all three at once gives the **Calculus of Constructions**, $\lambda C$ (Chapter 6). Because the three extensions behave like three independent axes, the eight resulting systems (three axes, on/off) arrange themselves naturally into a cube — the **Barendregt cube**, or **$\lambda$-cube**. That geometry is not just a mnemonic: Barendregt showed that all eight systems can be presented with *one* set of derivation rules, parameterized by a single design choice. Understanding that parameterization is the payoff of this chapter, and it is also the direct ancestor of *pure type systems* (PTS), the framework modern proof assistants' kernels are built on.

---

## $\lambda 2$: terms depending on types

### The problem, concretely

The book's motivating trio is worth internalizing because each example recurs later:

- **The polymorphic identity.** $\lambda\alpha:{*}.\,\lambda x:\alpha.\,x$ — a term that takes a type $\alpha$ as its first argument, and only then behaves like the identity on $\alpha$.
- **Iteration.** $D \equiv \lambda\alpha:{*}.\,\lambda f{:}\alpha\to\alpha.\,\lambda x{:}\alpha.\, f(f\,x)$ — generic double-application, parametric in the carrier type.
- **Composition.** $\circ \equiv \lambda\alpha,\beta,\gamma:{*}.\,\lambda f{:}\alpha\to\beta.\,\lambda g{:}\beta\to\gamma.\,\lambda x{:}\alpha.\, g(f\,x)$.

The new ingredient in all three is the leading $\lambda\alpha:{*}.\, \ldots$ — abstraction where the *bound variable is itself a type*, ranging over $*$, "the type of all types." Applying such a term to a concrete type and $\beta$-reducing gives back an ordinary $\lambda\to$-term:
$$(\lambda\alpha:{*}.\,\lambda x{:}\alpha.\, x)\,\mathsf{nat} \to_\beta \lambda x{:}\mathsf{nat}.\, x.$$

This is **second order [[The-Untyped-Lambda-Calculus#Abstraction and application|abstraction and application]]**: the calculus now has two layers of binding, one over ordinary terms and one over types, and $\beta$-reduction has to be extended to cover both.

### Why arrow types aren't enough: $\Pi$-types

What is the type of $\lambda\alpha:{*}.\,\lambda x{:}\alpha.\,x$? The naive guess, by analogy with $\lambda\to$, is $* \to (\alpha \to \alpha)$. But this breaks $\alpha$-equivalence: renaming the bound $\alpha$ to $\beta$ inside the term should give an identical term, yet the type $* \to (\alpha \to \alpha)$ has a *free* $\alpha$ that doesn't get renamed along with it — two syntactically identical terms would end up with different types. The fix is to introduce a genuine binder for this situation, the **$\Pi$-binder**:
$$\lambda\alpha:{*}.\,\lambda x{:}\alpha.\,x \;:\; \Pi\alpha:{*}.\,\alpha\to\alpha.$$

$\Pi\alpha:{*}.\,\alpha\to\alpha$ is read "the type of functions that, given an arbitrary type $\alpha$, return a term of type $\alpha \to \alpha$." Because $\alpha$ is now bound inside the type itself, $\alpha$-conversion applies uniformly to both the term and its type, and the problem dissolves. This is the crucial conceptual move of the whole chapter: **a $\Pi$-type is a binder, not a connective** — it generalizes $\to$ by letting the *codomain* mention the *bound variable of the domain*. (Chapter 5 will push this further, binding a *term* variable instead of a type variable — same binder, different level.)

The two new rules that let you construct and use such terms are:

$$
(\text{abst}_2)\ \dfrac{\Gamma,\alpha:{*} \vdash M : A}{\Gamma \vdash \lambda\alpha:{*}.\,M : \Pi\alpha:{*}.\,A}
\qquad\qquad
(\text{appl}_2)\ \dfrac{\Gamma \vdash M : \Pi\alpha:{*}.\,A \quad \Gamma \vdash B : {*}}{\Gamma \vdash M\,B : A[\alpha:=B]}
$$

Note the shape of $(\text{appl}_2)$: it's exactly ordinary function application, except the "argument" is a type $B$, and the "codomain," rather than being fixed, is computed by substituting $B$ into $A$. This is your first sight of a pattern that recurs at every level of the cube: *application always instantiates a binder's body by substitution — what changes across the cube is only what kind of thing gets bound and substituted.*

A subtlety worth flagging: because type variables are now first-class citizens that get declared and used, contexts must be built up so that every type variable is declared *before* it's used in a later declaration — $x : \alpha \to \alpha$ presupposes $\alpha:{*}$ already sits earlier in the context. This bookkeeping requirement is exactly a well-formedness discipline; it reappears, generalized, as the recurring theme of every system in this chapter.

### Grounding: what this looks like as real code

**Lean** gives you the single most literal translation possible — Lean's `Type` plays the role of $*$, and dependent function types `(α : Type) → α → α` *are* $\Pi$-types over types:

```lean
def polyId : (α : Type) → α → α := fun α x => x

#check polyId Nat        -- Nat → Nat
#eval polyId Nat 3        -- 3
```

This isn't an analogy — `polyId` is definitionally the term $\lambda\alpha:{*}.\,\lambda x{:}\alpha.\,x$, its type is definitionally $\Pi\alpha:{*}.\,\alpha\to\alpha$, and `polyId Nat` is definitionally the second-order application $(\text{appl}_2)$ followed by the same substitution $A[\alpha:=B]$ the rule specifies. When you write `#check polyId Nat` and Lean's elaborator computes `Nat → Nat`, it is executing the substitution in the $(\text{appl}_2)$ rule.

**Rust generics get you the *effect* of $\lambda 2$, but not the mechanism.** `fn poly_id<T>(x: T) -> T { x }` looks like the same idea, but Rust achieves it through *monomorphization*: the compiler generates a separate copy of `poly_id` for every concrete `T` at compile time. There is no runtime (or even post-compilation) term that "is" the polymorphic identity the way `polyId` is in Lean — `poly_id::<T>` for a chosen `T` is a fresh function, not an application of one generic term to a type argument. What breaks without true second-order terms: Rust cannot express *rank-2 polymorphism* directly (a function that takes a genuinely polymorphic function as an argument and applies it at multiple types internally) without workarounds like a trait with a generic method:

```rust
trait PolyFn { fn apply<T>(&self, x: T) -> T; }
struct Id;
impl PolyFn for Id { fn apply<T>(&self, x: T) -> T { x } }
```

This trait-object encoding is Rust's closest approximation to a term of type $\Pi\alpha:{*}.\,\alpha\to\alpha$ — and it needs an entire trait definition to simulate what $\lambda 2$ gives you as a single binder.

**Python**, being untyped at the term level, sidesteps the whole issue — `def poly_id(x): return x` is "polymorphic" simply because Python never checks types. It's a useful contrast: $\lambda 2$'s difficulty is not *achieving* polymorphic behavior (dynamically typed languages get that for free) but *typing* it soundly and decidably, which is precisely what the derivation rules above are doing.

### A worked derivation, and why it matters

The book derives the type of $D \equiv \lambda\alpha:{*}.\,\lambda f{:}\alpha\to\alpha.\,\lambda x{:}\alpha.\,f(f\,x)$ bottom-up: peel off $(\text{abst}_2)$ for the outer $\lambda\alpha$, then $(\text{abst})$ twice for the ordinary abstractions, solve the inner $\lambda\to$ problem, and reassemble:
$$\emptyset \vdash \lambda\alpha:{*}.\,\lambda f{:}\alpha\to\alpha.\,\lambda x{:}\alpha.\,f(f\,x) \;:\; \Pi\alpha:{*}.\,(\alpha\to\alpha)\to\alpha\to\alpha.$$

Every property that made $\lambda\to$ well-behaved — Free Variables, Thinning, Condensing, Generation, Substitution, Uniqueness of Types, Church–Rosser, Subject Reduction, Strong Normalization — transfers to $\lambda2$ (only Permutation needs restricting, to permutations that remain valid $\lambda2$-contexts). $\lambda2$ was invented independently twice: by Girard (1972, "System F", for proof-theoretic reasons around second-order arithmetic) and by Reynolds (1974, "polymorphic lambda calculus", to capture *parametricity* — the fact that a function of type $\Pi\alpha:{*}.\,\alpha\to\alpha$ cannot inspect its argument's type and so, provably, can only be the identity). $\lambda2$ types are called **impredicative**: a type like $\Pi\alpha:{*}.\,\alpha\to\alpha$ quantifies over the entire collection of types, *including itself*. Girard proved this circularity is harmless (consistent), but it costs decidability elsewhere: type inference for $\lambda2$ is undecidable (Wells, 1994).

---

## $\lambda\omega$: types depending on types

### Type constructors and kinds

Symmetric to the previous move: instead of abstracting a *term* over a type, abstract a *type* over a type. $\lambda\alpha:{*}.\,\alpha\to\alpha$ is not itself a type — feed it nothing and it doesn't type-check as $*$ — but feed it a type and you get one back:
$$(\lambda\alpha:{*}.\,\alpha\to\alpha)\,\beta \to_\beta \beta\to\beta.$$

Such an object is called a **type constructor**. What's its type? Since $\alpha:{*}$ and $\alpha\to\alpha:{*}$, the constructor is a function from $*$ to $*$, so naturally $\lambda\alpha:{*}.\,\alpha\to\alpha : {*}\to{*}$. This forces a new tier of "super-types" above $*$, called **kinds**:
$$K = {*} \mid (K \to K).$$

And now the levels stack up: level 1 is terms, level 2 is constructors (ordinary types plus "proper" constructors that aren't types themselves, like $\lambda\alpha:{*}.\,\alpha\to\alpha : {*}\to{*}$), level 3 is kinds, and — since kinds themselves need a type — level 4 consists of a single new symbol $\Box$ (pronounced "box"), the "super-super-type," with $* : \Box$. A **sort** is either $*$ or $\Box$.

### The rule machinery: double roles everywhere

Adding $\Box$ forces a rewrite of the whole rule set, because now the same rule has to work at two levels simultaneously (once for $s\equiv *$, once for $s\equiv\Box$). This "double role" convention is the single most important structural idea of the chapter, because it is exactly the trick that later lets *one* rule set cover all eight cube systems.

$$
(\text{sort})\ \emptyset \vdash {*}:\Box
\qquad
(\text{var})\ \dfrac{\Gamma \vdash A : s}{\Gamma, x{:}A \vdash x : A}\ (x \notin \Gamma)
\qquad
(\text{weak})\ \dfrac{\Gamma \vdash A:B \quad \Gamma \vdash C:s}{\Gamma, x{:}C \vdash A:B}\ (x \notin \Gamma)
$$
$$
(\text{form})\ \dfrac{\Gamma \vdash A:s \quad \Gamma \vdash B:s}{\Gamma \vdash A\to B : s}
\qquad\qquad
(\text{conv})\ \dfrac{\Gamma \vdash A:B \quad \Gamma \vdash B':s}{\Gamma \vdash A:B'}\ (B =_\beta B')
$$

**What breaks without weakening.** With only (var), you can derive that the *last* declaration in a context is well-typed, but not that earlier ones still are — e.g. $\alpha:{*},\beta:{*} \vdash \beta:{*}$ (asking whether the *later* declared $\beta$ is well-typed with $\alpha$ hanging around unused) is *not* derivable from (var) alone. (weak) exists precisely to let you extend a context with an unrelated well-formed declaration without breaking existing judgements — "you may add or remove junk without affecting derivability."

**What breaks without the conversion rule.** Once types themselves reduce (a type constructor applied to an argument, like $(\lambda\alpha:{*}.\,\alpha\to\alpha)\,\beta$), a term can have a type that is $\beta$-convertible but not syntactically identical to a "nicer" type — $x : (\lambda\alpha:{*}.\,\alpha\to\alpha)\,\beta$ ought to also mean $x:\beta\to\beta$, but nothing in (appl)/(abst) lets you draw that conclusion. (conv) plugs the gap, with a crucial second premiss: $B'$ itself must independently be well-formed, because $\beta$-conversion alone doesn't preserve well-formedness (e.g. $\beta\to\gamma =_\beta (\lambda\alpha:{*}.\,\beta\to\gamma)\,M$ for *any* $M$, including ill-typed ones). This distinction — **Subject Reduction** (reducing the *subject*, a theorem, provable without (conv)) versus **Type Reduction** (reducing the *type*, a special case of (conv)) versus **Conversion** in general (the rule itself) — is worth holding onto precisely, because conflating them is a common source of confusion later.

A direct consequence: Uniqueness of Types weakens to **Uniqueness of Types up to Conversion** ($\Gamma \vdash A:B_1$ and $\Gamma \vdash A:B_2$ implies $B_1 =_\beta B_2$, not $B_1 \equiv B_2$).

### Grounding

**Lean, again, is the most direct translation** — and this is where the correspondence becomes load-bearing for the kernel-building project this vault is tracking. Lean's `isDefEq` — the definitional-equality check the elaborator calls constantly to decide whether two types "are the same" — *is* an implementation of the side condition $B =_\beta B'$ in (conv). Every time Lean accepts a term whose computed type differs syntactically from its expected type but reduces to it, that's (conv) firing:

```lean
-- a type constructor, kind * → *
def selfArrow : Type → Type := fun α => α → α

#check (selfArrow : Type → Type)
#check selfArrow Nat          -- reduces (definitionally) to Nat → Nat
example : selfArrow Nat = (Nat → Nat) := rfl   -- literally (conv)'s β =_β check
```

That `rfl` is not a coincidence — `rfl` succeeds exactly when the kernel's definitional-equality check (its own `isDefEq`/reduction-based conversion, the direct descendant of this book's $=_\beta$) can unify both sides. If you are building a checker whose (conv)-analogue needs to decide $\beta\delta$-equality, this is the literal mechanism to study.

**Rust's type system has no kind-level computation at all** in the sense of $\lambda\omega$: there's no way to write a *generic type constructor as a first-class value* and apply it. `Vec<T>` is a type constructor of "kind" $*\to*$, but you cannot abstract over `Vec` itself the way $\lambda\alpha:{*}.\,\alpha\to\alpha$ abstracts over $\alpha\to\alpha$ — Rust has no higher-kinded types. Associated types and GATs (generic associated types) let you *simulate* a fragment of this (a trait with `type Wrapped<T>;` gives a form of kind-$*\to*$ polymorphism through the trait system), but it is bolted-on machinery, not a primitive of the type system the way it is in $\lambda\omega$. This gap is exactly what motivates library designs like `Iterator` needing `Item` as an associated type instead of a first-class `F : * → *` parameter.

---

## $\lambda P$: types depending on terms

### Families of types and predicates

The third and last orthogonal direction: a *type* that depends on a *term*. General shape: $\lambda x{:}A.\,M$, where $M$ is a type. Two motivating readings, both central to everything that follows in the book:

- **Set-valued function.** Let $S_n$ be a set for each $n:\mathsf{nat}$ — e.g. $S_n = \{0, n, 2n, 3n, \ldots\}$. Then $\lambda n{:}\mathsf{nat}.\, S_n$ is a *family of types* (an *indexed type*), of type $\mathsf{nat}\to{*}$.
- **Proposition-valued function.** Let $P_n$ be a proposition for each $n$ (e.g. "$n$ is prime"). Then $\lambda n{:}\mathsf{nat}.\, P_n$ is exactly what logicians call a **predicate**, again of type $\mathsf{nat}\to{*}$.

This second reading is the doorway to the **PAT interpretation** (propositions-as-types, proofs-as-terms), which the book flags as "a foundational idea behind type theory as a whole." A term $b$ inhabiting a type $B$ that we're reading as a proposition *is* a proof of $B$; if $B$ has no inhabitant, $B$ is false. Everything downstream in this book — natural deduction, formalized mathematics, Bézout's Lemma — runs on this interpretation, so it is worth internalizing here rather than deferring it.

### $\Pi$-types are back — but term-indexed this time

$\lambda P$'s derivation rules look almost identical to $\lambda\omega$'s, with two changes that mirror each other exactly:

$$
(\text{form})\ \dfrac{\Gamma \vdash A:{*} \quad \Gamma,x{:}A \vdash B:s}{\Gamma \vdash \Pi x{:}A.\,B : s}
\qquad\qquad
(\text{appl})\ \dfrac{\Gamma \vdash M : \Pi x{:}A.\,B \quad \Gamma \vdash N:A}{\Gamma \vdash M\,N : B[x:=N]}
$$

**(i) Upgrading:** $\to$-types are replaced by genuine $\Pi x{:}A.\,B$, where $B$ may mention the bound *term* $x$ — this is the same $\Pi$-binder from $\lambda2$'s Section 3.2, just binding a term instead of a type. When $x \notin FV(B)$ it degenerates back to the ordinary arrow, so $A \to B$ survives purely as sugar for $\Pi x{:}A.\,B$.

**(ii) Downgrading:** the domain $A$ in $\Pi x{:}A.\,B$ is restricted to $A:{*}$ (not $A:\Box$), because $x$ must be a *term*, not a type — this is what excludes $\lambda\omega$'s type-level abstraction from $\lambda P$; the two extensions are genuinely orthogonal.

This is a real generalization of the arrow type, not mere notation: with $A$ fixed but $B$ allowed to depend on the specific value chosen for $x$, $\Pi x{:}A.\,B$ is a **dependent product** — the book notes (citing Martin-Löf) that when $A$ is finite with elements $a_1, a_2$, $\Pi x{:}A.\,B$ literally *is* the Cartesian product $B[x{:=}a_1] \times B[x{:=}a_2]$; when $x \notin FV(B)$ it's just the ordinary function space. One binder generalizes both.

### Natural deduction falls out of the typing rules

This is the payoff worked example of the chapter, and it's worth stating precisely because it's the mechanism the rest of the book (Chapters 7 and 11) builds entire proof systems on top of. Coding logic in $\lambda P$: $S:{*}$ for a set, $A:{*}$ for a proposition, $P : S \to {*}$ for a predicate, $A\Rightarrow B$ *as* $A\to B$, $\forall_{x\in S}(P(x))$ *as* $\Pi x{:}S.\,P\,x$. Under that reading, the natural-deduction rules for $\Rightarrow$ and $\forall$ turn out to be **literally** the typed (appl) and (abst) rules, just relabeled:

| Minimal predicate logic | $\lambda P$ typing |
|---|---|
| $A \Rightarrow B$ | $A \to B$ (i.e. $\Pi x{:}A.\,B$) |
| $\forall_{x\in S}(P(x))$ | $\Pi x{:}S.\,P\,x$ |
| $(\Rightarrow\text{-elim})$ | (appl) |
| $(\Rightarrow\text{-intro})$ | (abst) |
| $(\forall\text{-elim})$ | (appl) |
| $(\forall\text{-intro})$ | (abst) |

You get modus ponens and universal generalization *for free* — they were never added as separate rules; they are what (appl) and (abst) already say once you read $\Pi$ as $\forall$. **What $\lambda P$ still cannot express**: negation, [[The-Curry-Howard-Isomorphism#Conjunction|conjunction]], [[The-Curry-Howard-Isomorphism#Disjunction|disjunction]], or the existential quantifier — those require the impredicative encodings only available once $\lambda2$'s machinery is back in the picture (Chapter 7 shows this explicitly, once $\lambda C$ combines everything).

### Grounding — this is where Lean is the right primary language

Per the priority on this vault, dependent types are exactly the case where Lean should carry the main weight, because the correspondence is essentially exact:

```lean
-- λn : nat . S_n  as a Lean family of types, of type Nat → Type
def MultiplesOf (n : Nat) : Type := { m : Nat // n ∣ m }

-- Πn : nat . S_n — a dependent function whose *type* varies with its input
def zeroWitness (n : Nat) : MultiplesOf n := ⟨0, Dvd.intro 0 rfl⟩

-- the ∀-as-Π reading, worked exactly as in Section 5.4
def modusPonens {A B : Prop} (f : A → B) (a : A) : B := f a          -- (appl) = ⇒-elim
def univIntro {S : Type} {P : S → Prop} (proof : (x : S) → P x)
    : ∀ x, P x := proof                                              -- (abst) = ∀-intro
```

`MultiplesOf : Nat → Type` is precisely $\lambda n:\mathsf{nat}.\,S_n$; the dependent function `zeroWitness` is precisely a term inhabiting a $\Pi$-type whose codomain mentions the bound variable. And `Prop` in Lean *is* the PAT interpretation made real: a `Prop`-valued function is a predicate, and a term of a `Prop` is a proof — exactly $S \to {*}$ and "$p$ proves $A$" iff $p : A$ from the table above.

**What breaks in Rust without this.** Rust's type system has no dependent types: you cannot write a function whose *return type* varies based on the runtime *value* (not just the static type) of an argument. `fn make_array<const N: usize>() -> [i32; N]` gets you dependency on a **compile-time constant**, which is a narrow, closed-world approximation — it cannot depend on an ordinary runtime `usize` the way $\Pi n{:}\mathsf{nat}.\,S_n$ depends on an arbitrary term $n$. This is precisely the gap a Rust verifier embedding Hoare-triple-style contracts (as in this vault's standing compiler/verifier project) has to bridge externally, since the host language's own type system stops at $\lambda\to$ plus const generics — it never reaches $\lambda P$.

**Judgment forms and the twin readings.** The book's own framing — Well-typedness, Type Checking, and Term Finding as three flavors of the same judgment $\Gamma \vdash M : \sigma$ with different parts left as "?" — is precisely the shared ancestor of *a type checker* and *a proof checker* mentioned as a standing thread for this vault: Type Checking (context, term, and type all given; verify) is the **checking mode** of bidirectional typing, while Term Finding (context and type given, term unknown) is a **search problem** — the mode elaboration lives in, filling metavariables in exactly the way an implicit-argument elaborator does. $\lambda P$ is the first system in the book where Term Finding acquires real content, because it's the first system where "find a term of this type" coincides with "find a proof of this proposition."

---

## $\lambda C$: the union of all three extensions

### One parameter, four possibilities

$\lambda P$'s formation rule required its domain $A$ to have exactly $*$: `Γ ⊢ A:∗, Γ,x:A ⊢ B:s ⟹ Γ ⊢ Πx:A.B : s`. Lift that restriction — let $A$ range over *either* sort, independently of $B$'s sort — and you get the single formation rule that generates everything:

$$
(\text{form}_{\lambda C})\ \dfrac{\Gamma \vdash A:s_1 \quad \Gamma,x{:}A \vdash B:s_2}{\Gamma \vdash \Pi x{:}A.\,B : s_2}
$$

Now $s_1$ and $s_2$ range independently over $\{*,\Box\}$, giving four combinations, each of which is a recognizable named system:

| $(s_1, s_2)$ | $x:A:s_1$, $b:B:s_2$ | $\lambda x{:}A.\,b$ is | System |
|---|---|---|---|
| $(*,*)$ | term-depending-on-term | ordinary function | $\lambda\to$ |
| $(\Box,*)$ | term-depending-on-type | polymorphic term | $\lambda2$ |
| $(\Box,\Box)$ | type-depending-on-type | type constructor | $\lambda\omega$ |
| $(*,\Box)$ | type-depending-on-term | dependent type family | $\lambda P$ |

The type of $\Pi x{:}A.\,B$ is *inherited from its body* — it's $s_2$, not some new combination — a design choice the book flags as debatable-but-workable rather than forced: more general frameworks (pure type systems, below) let the conclusion's sort be an independent $s_3$.

### The Barendregt cube

Because the three extensions ($\lambda2$, $\lambda\omega$, $\lambda P$) are mutually independent directions, you can visualize $\lambda\to$ sitting at the origin of a three-dimensional coordinate system, with each axis toggling one extension on. All $2^3 = 8$ combinations are legitimate systems, each characterized purely by *which $(s_1,s_2)$ pairs its (form) rule permits*:

<pre class="cube-diagram">
<svg viewBox="0 0 480 380" xmlns="http://www.w3.org/2000/svg" font-family="ui-monospace, monospace" font-size="15">
  <!-- edges: front face -->
  <g stroke="#8a8a8a" stroke-width="1.5" fill="none">
    <line x1="100" y1="320" x2="320" y2="320"/>
    <line x1="100" y1="320" x2="100" y2="100"/>
    <line x1="320" y1="320" x2="320" y2="100"/>
    <line x1="100" y1="100" x2="320" y2="100"/>
    <!-- back face -->
    <line x1="180" y1="240" x2="400" y2="240"/>
    <line x1="180" y1="240" x2="180" y2="20"/>
    <line x1="400" y1="240" x2="400" y2="20"/>
    <line x1="180" y1="20" x2="400" y2="20"/>
    <!-- connectors -->
    <line x1="100" y1="320" x2="180" y2="240"/>
    <line x1="320" y1="320" x2="400" y2="240"/>
    <line x1="100" y1="100" x2="180" y2="20"/>
    <line x1="320" y1="100" x2="400" y2="20"/>
  </g>
  <!-- vertices -->
  <g>
    <circle cx="100" cy="320" r="7" fill="#4a90d9"/>
    <circle cx="320" cy="320" r="7" fill="#4a90d9"/>
    <circle cx="100" cy="100" r="7" fill="#4a90d9"/>
    <circle cx="320" cy="100" r="7" fill="#4a90d9"/>
    <circle cx="180" cy="240" r="7" fill="#4a90d9"/>
    <circle cx="400" cy="240" r="7" fill="#4a90d9"/>
    <circle cx="180" cy="20" r="7" fill="#4a90d9"/>
    <circle cx="400" cy="20" r="9" fill="#d9884a"/>
  </g>
  <!-- labels -->
  <g fill="#8a8a8a">
    <text x="60" y="345">λ→</text>
    <text x="330" y="345">λP</text>
    <text x="50" y="95">λ2</text>
    <text x="330" y="95">λP2</text>
    <text x="140" y="270">λω</text>
    <text x="405" y="270">λPω</text>
    <text x="140" y="15">λω̲</text>
    <text x="410" y="15" font-weight="bold">λC</text>
  </g>
  <g fill="#8a8a8a" font-size="12">
    <text x="205" y="360">→ terms/types on terms (λP axis)</text>
    <text x="0" y="370" transform="rotate(-90 20 360)"></text>
  </g>
</svg>
</pre>

*Axes: right = "types depend on terms" ($\lambda P$ direction), up = "terms depend on types" ($\lambda2$ direction), back = "types depend on types" ($\lambda\omega$ direction). $\lambda\to$ sits at the near-bottom-left corner with none of the three; $\lambda C$ sits at the far-top-right corner ($\Box$) with all three. $\lambda\underline{\omega}$ (underlined) is $\lambda2+\lambda\omega$ without $\lambda P$ — distinct from plain $\lambda\omega$ of Chapter 4.*

| System | Allowed $(s_1,s_2)$ | Reading |
|---|---|---|
| $\lambda\to$ | $(*,*)$ | none of the three extensions |
| $\lambda2$ | $(*,*),(\Box,*)$ | + terms-on-types |
| $\lambda\omega$ | $(*,*),(\Box,\Box)$ | + types-on-types |
| $\lambda P$ | $(*,*),(*,\Box)$ | + types-on-terms |
| $\lambda\underline{\omega}$ | $(*,*),(\Box,*),(\Box,\Box)$ | $\lambda2+\lambda\omega$ |
| $\lambda P2$ | $(*,*),(\Box,*),(*,\Box)$ | $\lambda2+\lambda P$ |
| $\lambda P\omega$ | $(*,*),(\Box,\Box),(*,\Box)$ | $\lambda\omega+\lambda P$ |
| $\lambda C$ | all four | $\lambda2+\lambda\omega+\lambda P$ |

The remarkable fact — Barendregt's actual contribution — isn't the cube picture, it's that **one fixed set of seven rule schemas** — (sort), (var), (weak), (form), (appl), (abst), (conv) — generates *all eight* systems, with the only knob being which $(s_1,s_2)$ pairs (form) is allowed to use. Everything you derived by hand for $\lambda\to$, $\lambda2$, $\lambda\omega$ and $\lambda P$ in the previous chapters is a restriction of this single rule set. (A historical aside worth keeping: de Bruijn's Automath — the first working formal proof-checking system, decades before Coq or Lean — sits roughly at $\lambda P + \tfrac12\lambda2 + \tfrac12\lambda\omega$, plus a definitions mechanism that this book spends its second half reconstructing as $\lambda D$.)

### $\lambda C$'s metatheory, and the two big theorems that matter operationally

Nearly everything from earlier chapters transfers to $\lambda C$ (Free Variables, Thinning/Permutation/Condensing, Generation — now with four cases instead of three, because $\Pi$-formation itself needs a case — Uniqueness of Types up to Conversion, Substitution, Church–Rosser, Subject Reduction, Strong Normalization). Two results deserve to be pulled out because they set the boundary of what any checker/prover built on this foundation can and cannot automate:

- **Well-typedness and Type Checking are decidable** in $\lambda C$ and every subsystem. A program can always answer "is this term legal?" and "does this term have this type?"
- **Term Finding is decidable only in $\lambda\to$ and $\lambda\underline{\omega}$** (the corner and edge of the cube with no $\lambda P$-direction) — everywhere $\lambda P$ enters, it becomes **undecidable**, as a direct consequence of the Church–Turing theorem, since under PAT, "find a term of type $M$" is the same problem as "prove or disprove proposition $M$."

This is the formal reason proof assistants need a human in the loop for the creative part (search) while being able to fully automate the mechanical part (checking) — and it is exactly the checker/elaborator division of labor this vault's two target projects are organized around: a Hoare-triple checker only ever needs the *decidable* fragment (type checking against a supplied proof term), while any component that *searches for* a proof or *infers* an implicit argument is operating in the undecidable fragment and can only ever be a heuristic, never a complete algorithm.

### Toward pure type systems

The book flags, almost in passing, the generalization that supersedes the cube: instead of fixing the conclusion's sort to $s_2$ (inherited from the body), let it be an independent $s_3$, giving $2^3 = 8$ choices for $(s_1,s_2,s_3)$ rather than $2$ choices for $(s_1,s_2)$-membership-in-a-fixed-set. This is Berardi and Terlouw's **pure type system** (PTS) framework — the cube's eight systems are the special case $s_3 = s_2$ always. PTS generality is what lets you describe, uniformly, systems with a genuine *hierarchy* of sorts (universes $\Box_0 = \Box, \Box_1, \Box_2, \ldots$ with $\Box_i : \Box_{i+1}$) rather than the flat two-sort $\{*,\Box\}$ used throughout this chapter — exactly the universe hierarchy Lean's `Type 0`, `Type 1`, `Type 2`, ... implements, and exactly the "Extended Calculus of Constructions" (ECC, Luo 1994) the book cites in its further-reading, with its rule
$$\dfrac{\Gamma \vdash A:\Box_i \quad \Gamma,x{:}A \vdash B:\Box_j}{\Gamma \vdash \Pi x{:}A.\,B : \Box_{\max(i,j)}}$$
and *cumulativity* ($\Box_i \subseteq \Box_{i+1}$). If you have ever wondered why Lean's kernel talks about `Sort u` with a universe-polymorphic level `u` instead of a single `Type`, this is the formal machinery underneath: a real proof assistant's kernel is a PTS with an infinite, cumulative universe hierarchy layered on top of exactly this chapter's rule schema.

### Grounding: Lean's kernel as the cube made concrete

```lean
-- λ2-flavored: term depending on type   (s1,s2) = (□,*)
#check (fun (α : Type) (x : α) => x)

-- λω-flavored: type depending on type   (s1,s2) = (□,□)
#check (fun (α : Type) => α → α)

-- λP-flavored: type depending on term   (s1,s2) = (*,□)
#check (fun (n : Nat) => Fin n)          -- Fin n : Type, depends on the *value* n

-- λC-flavored: all three at once, e.g. a type-indexed, term-indexed dependent function
#check (fun (α : Type) (n : Nat) (v : Fin n → α) => v)
```

Every one of these four snippets type-checks in Lean precisely because Lean's kernel is (a universe-polymorphic PTS extension of) $\lambda C$ — it permits all four $(s_1,s_2)$ combinations simultaneously, exactly as the cube's top-right-back vertex does. Rust cannot express the third or fourth snippet at all (no genuine term-indexed type families), and Python's lack of static types makes the whole question moot — which is itself the point: the cube is a taxonomy of *exactly which of these four snippets a type system supports*, and most languages you'll ever use sit at $\lambda\to$ or, with generics, an informal approximation of $\lambda2$.

---

## Where this leads

The cube is the conceptual centerpiece the rest of the book's type-theoretic apparatus hangs off. Chapter 7 immediately exploits $\lambda C$'s combination of $\lambda2$ (impredicative quantification) and $\lambda P$ (term-indexed types) to encode $\bot$, $\neg$, $\wedge$, $\vee$ and $\exists$ — connectives $\lambda P$ alone couldn't express — closing the PAT correspondence for full first-order logic. Chapters 9–10 then observe that raw $\lambda C$ proof terms explode in size, which motivates adding a *definitions* mechanism (parameter lists, unfolding, $\delta$-reduction) on top of exactly the rule set built here, yielding $\lambda D$ — the system the entire second half of the book (natural deduction, set theory, arithmetic, Bézout's Lemma) is actually formalized in.

For the standing projects this vault is tracking: the (conv) rule's $\beta$-conversion check is the direct, minimal ancestor of the `isDefEq` a bidirectional elaborator needs; the Well-typedness / Type Checking / Term Finding trichotomy is the formal statement of why a *checker* (decidable, mechanizable) and a *prover/elaborator* (undecidable, heuristic) are fundamentally different kinds of components even though both are answering instances of the same judgment $\Gamma \vdash M : \sigma$; and the PTS generalization sketched at the end is the shortest path from "the eight cube systems" to "the universe-polymorphic kernel Lean actually runs," which is the more realistic target for a from-scratch elaborator than the flat two-sort cube itself.
