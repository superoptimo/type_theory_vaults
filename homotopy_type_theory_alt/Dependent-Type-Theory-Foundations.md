---
title: Dependent Type Theory Foundations
source: Homotopy Type Theory - Univalent Foundations of Mathematics
chapters: "Chapter 1, Type theory (printed pp. 17–54)"
tags: [type-theory, automated-reasoning, dependent-types, judgments, hott]
---

[[book-guidelines|↩ Back to guidelines]]

# Dependent Type Theory Foundations

## 1. Why the book starts here

HoTT is offered as an alternative to ZFC, and the book says plainly that it "behaves differently from set theory in several important ways". Chapter 1 therefore spends a few pages being more formal than the rest of the book. The aim is to stop a set-theoretically trained reader from importing the wrong intuitions.

The core contrast is about layers.
- **Set theory** has two layers: first-order logic as a deductive system, with the axioms of ZFC formulated inside it. Its two basic notions are sets and propositions.
- **Type theory** is its own deductive system, with no logic underneath it. It has one basic notion, the *type*. Propositions are particular types, and proving a theorem is constructing an inhabitant.

A programmer will find this familiar. A type checker is the whole system, and there is no separate logic that "talks about" the program. The rest of the chapter shows that the same machine can also read as a proof checker.

## 2. Judgments: the "external" statements

A deductive system is a set of rules for deriving *judgments*. Judgments live in the metatheory, and the propositions of the theory live inside it. In first-order logic there is one judgment form, "$A$ has a proof". Type theory has two (§1.1):

| Judgment | Meaning |
|---|---|
| $a : A$ | $a$ is an object of type $A$ |
| $a \equiv b : A$ | $a$ and $b$ are definitionally equal objects of type $A$ |

The book stresses three consequences.

1. **$a : A$ is not $a \in A$.** Membership is a proposition about two pre-existing objects. $a : A$ is a judgment, so you cannot negate it, assume it inside a hypothesis, or "disprove" it. Every term has its type built in, and "let $x : \mathbb{N}$" is atomic. A variable cannot be introduced without a type.
2. **Two different equalities.** Propositional equality $a =_A b$ is a *type*, so it can be assumed, negated and proved. Judgmental equality $a \equiv b$ is a judgment ("equal by definition"). It cannot be assumed or negated inside the theory. The book notes that it is algorithmically decidable, though by a metatheoretic algorithm and not an internal one.
3. **Why judgmental equality exists at all.** It controls $a : A$. If $p : (3^2 = 9)$ and $f(x) :\equiv x^2$, then $p$ should also witness $f(3) = 9$. The rule is that from $a : A$ and $A \equiv B$ we derive $a : B$.

The book writes definitions with $:\equiv$, for example $f(x) :\equiv x^2$. Because judgments cannot be nested, $:$ and $\equiv$ bind more loosely than anything else. So $p : x = y$ parses as $p : (x = y)$.

**Contexts.** Judgments may depend on assumptions $x : A$. The collection of assumptions is the *context*, and "technically the context must be an ordered list", since later assumptions can mention earlier variables. You can assume a propositional equality (a variable $p : x = y$), but not a judgmental one. The phrase "now assume $x \equiv a$" really means substituting $a$ for $x$.

**Rules, not axioms.** The type theory of Chapter 1 consists entirely of rules, with no axioms. In set theory, the behaviour of sets sits in the axioms (the pairing axiom, for instance). In type theory the rule "from $a : A$ and $b : B$ derive $(a,b) : A \times B$" does the same job. The book calls this "procedural", and says it is what makes computational properties such as canonicity possible. Univalence (§2.10) and [[Higher-Inductive-Types|higher inductive types]] (Chapter 6) will later have to be added as axioms, since the authors do not yet know how to make them rules.

### Grounding

Python has nothing like judgments, but one can model them as a decision procedure for a typing relation over an AST. The Rust sketch below shows that structure. The key point is that `infer` computes $a : ?$, while `conv` decides $\equiv$ and sits outside the object language.

```rust
// Terms of a tiny dependent calculus (de Bruijn indices avoid capture).
enum Tm {
    Var(usize),
    Lam(Box<Tm>),                 // λ. body
    App(Box<Tm>, Box<Tm>),
    Pi(Box<Tm>, Box<Tm>),         // Π(x:A). B(x)
    U(u32),                       // universe U_i
}

struct Ctx(Vec<Tm>);              // ordered list: later entries may depend on earlier ones

// Judgment  Γ ⊢ a : A  as an algorithm; Γ ⊢ a ≡ b as `conv` (a metatheoretic decision procedure).
fn infer(g: &Ctx, a: &Tm) -> Result<Tm, TypeError> { /* ... */ unimplemented!() }
fn conv(g: &Ctx, a: &Tm, b: &Tm) -> bool { /* normalise both, compare */ unimplemented!() }
```

```lean
-- Lean: `:` is the typing judgment, `=` is the identity type, `rfl` witnesses it.
example : (fun x : Nat => x * x) 3 = 9 := rfl   -- accepted because f 3 ≡ 3*3 ≡ 9 by evaluation
#check (rfl : 2 + 2 = 4)                         -- the type `2 + 2 = 4` is inhabited by rfl
```

## 3. Function types and $\lambda$-calculus (§1.2)

Functions are primitive, not functional relations. A type former in the book's sense has:

1. a **formation rule** (when $A \to B$ is a type),
2. **constructors**, the introduction rules ($\lambda$-abstraction),
3. **eliminators** (application),
4. a **computation rule** ($\beta$): $(\lambda x.\,\Phi)(a) \equiv \Phi'$, where $\Phi'$ is $\Phi$ with $a$ substituted for $x$,
5. an optional **uniqueness principle** ($\eta$): $f \equiv (\lambda x.\, f(x))$.

This is Remark 1.5.1, and it is the template every later type follows. Notation matters here: $\lambda(x:A).\,\Phi$, $\lambda x.\,\Phi$ and $x \mapsto \Phi$ are the same thing. The book also notes that $\alpha$-, $\beta$- and $\eta$-conversion are all judgmental equalities.

**Capture-avoiding substitution** gets explicit treatment. If $f(x) :\equiv \lambda y.\, x + y$ and $y : \mathbb{N}$ is already in scope, then $f(y)$ is $\lambda z.\, y + z$ and not $\lambda y.\, y + y$. The book compares a $\lambda$ binder to the dummy variable of an integral. Renaming bound variables is an $\alpha$-equivalence, and so a definitional equality.

**Currying.** Two-argument functions are $f : A \to B \to C$, associating to the right. Application $f\,a\,b$ associates to the left.

### Grounding

```rust
// β-reduction with explicit shifting; this is exactly where variable capture is avoided.
fn subst(t: &Tm, idx: usize, s: &Tm) -> Tm { /* shift s under binders, replace Var(idx) */ unimplemented!() }
fn whnf(t: Tm) -> Tm {
    match t {
        Tm::App(f, a) => match whnf(*f) {
            Tm::Lam(body) => whnf(subst(&body, 0, &a)),   // (λx.Φ)(a) ≡ Φ[a/x]
            f2 => Tm::App(Box::new(f2), a),
        },
        t => t,
    }
}
```

```python
add = lambda m: lambda n: m + n   # curried: ℕ → ℕ → ℕ; add(2)(3) == 5
```

## 4. Universes and type families (§1.3)

A universe is a type whose elements are types. A universe containing itself ($\mathcal{U}_\infty : \mathcal{U}_\infty$) is unsound, and the book mentions that Russell's paradox can be encoded directly. So the theory has a cumulative hierarchy
$$\mathcal{U}_0 : \mathcal{U}_1 : \mathcal{U}_2 : \cdots$$
If $A : \mathcal{U}_i$ then also $A : \mathcal{U}_{i+1}$. Cumulativity means elements no longer have unique types.

*Typical ambiguity* lets us write $A : \mathcal{U}$ with the level implicit, and even $\mathcal{U} : \mathcal{U}$ meaning $\mathcal{U}_i : \mathcal{U}_{i+1}$. The book calls this "convenient but a bit dangerous". To check a suspicious argument, try to assign levels consistently. There is no family $\lambda(i:\mathbb{N}).\,\mathcal{U}_i$, since no universe is large enough, and the indices $i$ are not identified with $\mathbb{N}$.

A **type family** over $A$ is a function $B : A \to \mathcal{U}$. This is the book's "dependent type". Examples are $\mathsf{Fin} : \mathbb{N} \to \mathcal{U}$ and the constant family $\lambda(x:A).\,B$.

```lean
universe u
#check (Type u : Type (u+1))       -- hierarchy; Lean's levels are explicit and checked
def Vec (α : Type) : Nat → Type    -- a type family
  | 0     => Unit
  | n + 1 => α × Vec α n
```

```rust
// Rust approximates a family with const generics, but only for compile-time naturals:
struct Vec<T, const N: usize>([T; N]);   // N is a *term* of type usize appearing in a type
```

## 5. $\Pi$-types (§1.4)

For $A : \mathcal{U}$ and $B : A \to \mathcal{U}$, the dependent function type is $\prod_{x:A} B(x)$. Applying $f$ to $a : A$ gives $f(a) : B(a)$, so the result type depends on the argument. The rules are the same as for $A \to B$, namely $\beta$ and $\eta$. For a constant family, $\prod_{x:A} B \equiv (A \to B)$.

The polymorphic identity function shows why universes matter:
$$\mathsf{id} : \prod_{A:\mathcal{U}} A \to A, \qquad \mathsf{id} :\equiv \lambda(A:\mathcal{U}).\,\lambda(x:A).\,x.$$
Polymorphism is just a $\Pi$ over a universe. Arguments that can be inferred are written as subscripts or omitted, so $\mathsf{id}(a)$ means $\mathsf{id}_A(a)$. This is the book's informal version of *implicit arguments*. The $\mathsf{swap}$ example, with three type arguments, follows the same pattern.

```lean
def id' : (A : Type) → A → A := fun A x => x
def id'' {A : Type} (x : A) : A := x      -- implicit argument: the elaborator must solve ?A
def fmax : (n : Nat) → Fin (n + 1) := fun n => Fin.last n
```

## 6. Product, $\Sigma$, coproduct, empty, unit and boolean types (§§1.5–1.8)

All of them follow the template of Remark 1.5.1. The new idea is the pair *recursor* and *induction principle*.

- **Product $A \times B$.** Pairs are primitive. To define $f : A \times B \to C$ it suffices to give $g : A \to B \to C$ and set $f((a,b)) :\equiv g(a)(b)$. Packaged:
$$\mathsf{rec}_{A\times B} : \prod_{C:\mathcal{U}} (A \to B \to C) \to A \times B \to C.$$
 The book points out that set theory justifies this because every element is a pair. Type theory reverses the direction: the rule for functions on pairs is primitive, and "every element is a pair" is derived. It is only a *propositional* uniqueness principle, $\mathsf{uniq}_{A\times B} : \prod_{x : A\times B} (\mathsf{pr}_1(x), \mathsf{pr}_2(x)) = x$, proved using the dependent form below.
- **Induction $\mathsf{ind}_{A\times B}$.** Allowing the target family $C : A \times B \to \mathcal{U}$ to depend on the element gives
$$\mathsf{ind}_{A\times B} : \prod_{C} \Big(\prod_{x:A}\prod_{y:B} C((x,y))\Big) \to \prod_{x : A\times B} C(x).$$
 The recursor is the special case of a constant family. The recursor is the non-dependent eliminator, and induction is the dependent one.
- **Unit $\mathbf{1}$.** One element $\star$, with $\mathsf{ind}_{\mathbf{1}}$ more useful than $\mathsf{rec}_{\mathbf{1}}$.
- **$\Sigma$-types $\sum_{x:A} B(x)$.** Pairs $(a, b)$ with $b : B(a)$. The projection $\mathsf{pr}_2$ has type $B(\mathsf{pr}_1(p))$, which is typable because $B(\mathsf{pr}_1((a,b))) \equiv B(a)$. The book shows the "type-theoretic axiom of choice" $\mathsf{ac}$ is just provable:
$$\mathsf{ac} : \Big(\prod_{x:A}\sum_{y:B} R(x,y)\Big) \to \sum_{f : A\to B}\prod_{x:A} R(x, f(x)),$$
 and notes that "no choice is actually involved", since the choices are already supplied. A $\Sigma$ also expresses "structure": a magma is a $\Sigma$ of a carrier type and an operation.
- **Coproduct $A + B$.** Constructors $\mathsf{inl}$, $\mathsf{inr}$, and a recursor that is case analysis. The empty type $\mathbf{0}$ has no constructors, so $\mathsf{rec}_{\mathbf{0}} : \prod_{C} \mathbf{0} \to C$ ("ex falso").
- **Booleans $\mathbf{2}$.** The recursor is if-then-else. The book also shows $A + B :\equiv \sum_{x:\mathbf{2}} \mathsf{rec}_{\mathbf{2}}(\mathcal{U}, A, B, x)$ and $A \times B :\equiv \prod_{x:\mathbf{2}} \mathsf{rec}_{\mathbf{2}}(\mathcal{U}, A, B, x)$. Defining *types* by recursion on a term is the mechanism that makes dependent types powerful. It also flags that these encodings do not give the same judgmental equalities as the primitive types (Exercise 1.6).

```lean
-- recursor vs induction for Σ in Lean:
def ac {α β : Type} (R : α → β → Prop) (h : ∀ x, ∃ y, R x y) : ... -- Prop-valued: genuine choice needed
def ac' {α β : Type} (R : α → β → Type) (g : (x : α) → Σ y : β, R x y) :
    Σ f : α → β, (x : α) → R x (f x) := ⟨fun x => (g x).1, fun x => (g x).2⟩  -- just rules, as in the book
```

```rust
enum Either<A, B> { Inl(A), Inr(B) }           // A + B; rec_{A+B} is `match`
enum Void {}                                    // 0; fn absurd<C>(v: Void) -> C { match v {} }
```

## 7. Natural numbers, recursion and induction (§§1.9–1.10)

$\mathbb{N}$ has constructors $0$ and $\mathsf{succ}$. The recursor gives primitive recursion:
$$\mathsf{rec}_{\mathbb{N}} : \prod_{C:\mathcal{U}} C \to (\mathbb{N} \to C \to C) \to \mathbb{N} \to C,$$
with $\mathsf{rec}_{\mathbb{N}}(C, c_0, c_s, \mathsf{succ}(n)) :\equiv c_s(n, \mathsf{rec}_{\mathbb{N}}(C, c_0, c_s, n))$. The book defines $\mathsf{double}$ and $\mathsf{add}$ with it. $\mathsf{add}$ is defined with higher-order recursion (target $C :\equiv \mathbb{N} \to \mathbb{N}$), so the definable functions go beyond ordinary primitive recursive ones.

Generalising $C$ to a family $C : \mathbb{N} \to \mathcal{U}$ gives the induction principle
$$\mathsf{ind}_{\mathbb{N}} : \prod_{C} C(0) \to \Big(\prod_{n:\mathbb{N}} C(n) \to C(\mathsf{succ}(n))\Big) \to \prod_{n:\mathbb{N}} C(n).$$
The book comments: "Here we finally see the connection to the classical notion of proof by induction". A proof by induction *is* a dependent function defined by $\mathsf{ind}_{\mathbb{N}}$. The associativity-of-addition example computes the base case by judgmental equality ($0 + n \equiv n$). The successor case needs the induction hypothesis and the propositional lemma $\mathsf{succ}(m) = \mathsf{succ}(n)$ from $m = n$.

**Pattern matching** (§1.10) is shorthand for the recursor. A definition by equations is acceptable only when the recursive calls can be re-expressed as the second argument of $c_s$, that is, when $f$ appears only applied to the immediate predecessor ("structural recursion"). The book's policy is to derive the induction principle first and only then justify pattern matching as a shorthand.

```lean
def double : Nat → Nat
  | 0     => 0
  | n + 1 => (double n).succ.succ         -- compiles to Nat.rec; recursive call = `y` in cs(n, y)
theorem add_assoc' (i j k : Nat) : i + (j + k) = (i + j) + k := by
  induction i with
  | zero => rfl                            -- 0 + x ≡ x definitionally
  | succ n ih => simp [Nat.succ_add, ih]
```

```rust
fn rec_nat<C>(c0: C, cs: &dyn Fn(u64, C) -> C, n: u64) -> C {
    (0..n).fold(c0, |acc, k| cs(k, acc))   // cs receives the index and the result of the recursive call
}
```

## 8. Propositions as types (§1.11)

The book's table reads each connective as a type former, and the correspondence is "that in each case, the rules for constructing and using elements of the type correspond to the rules for proving and using the proposition".

| Logic | Type |
|---|---|
| $\top$, $\bot$ | $\mathbf{1}$, $\mathbf{0}$ |
| $A \wedge B$ | $A \times B$ |
| $A \vee B$ | $A + B$ |
| $A \Rightarrow B$ | $A \to B$ |
| $\neg A$ | $A \to \mathbf{0}$ |
| $\forall x.\,P(x)$ | $\prod_{x:A} P(x)$ |
| $\exists x.\,P(x)$ | $\sum_{x:A} P(x)$ |

Two caveats that matter. First, "or" and "there exists" carry *more information* than the logical versions: an element of $A + B$ says which side, and an element of $\Sigma$ gives a witness. (The book will repair this in Chapter 3 with truncation, which is outside this topic.) Second, the book's worked De Morgan-style example translates an English proof step by step into pattern matching and recursors: "suppose $A$ or $B$" is a case split, which is an application of $\mathsf{rec}_{A+B}$.

This is the type-checker-as-proof-checker connection in its plainest form.

## 9. Identity types and path induction (§1.12)

Given $a, b : A$ there is a type $(a =_A b) : \mathcal{U}$, written $\mathsf{Id}_A(a,b)$. Its only constructor is reflexivity, $\mathsf{refl} : \prod_{a:A}(a =_A a)$. If $a \equiv b$ then $\mathsf{refl}_a : a = b$ also typechecks, which is where judgmental equality feeds propositional equality.

**Indiscernibility of identicals** says that for $C : A \to \mathcal{U}$ there is $f : \prod_{x,y:A}\prod_{p : x = y} C(x) \to C(y)$ with $f(x,x,\mathsf{refl}_x) :\equiv \mathsf{id}_{C(x)}$. This is the recursion principle for the identity family.

**Path induction ($J$).** For $C : \prod_{x,y:A}(x = y) \to \mathcal{U}$ and $c : \prod_{x:A} C(x,x,\mathsf{refl}_x)$ there is
$$f : \prod_{x,y:A}\prod_{p : x = y} C(x,y,p), \qquad f(x,x,\mathsf{refl}_x) :\equiv c(x).$$
**Based path induction** fixes $a : A$. For $C : \prod_{x:A}(a = x) \to \mathcal{U}$ and $c : C(a, \mathsf{refl}_a)$ there is $f : \prod_{x}\prod_{p : a = x} C(x,p)$ with $f(a,\mathsf{refl}_a) :\equiv c$. The book proves the two equivalent (§1.12.2). Based path induction is derived from path induction via the family $D(x,y,p) :\equiv \prod_{C} C(x,\mathsf{refl}_x) \to C(y,p)$.

**The central subtlety (Remark 1.12.1).** It sounds as if path induction says "every path is $\mathsf{refl}$". It does not. What is inductively defined is the *family* $x =_A y$ as $x, y$ vary, and not any single identity type with both endpoints fixed. A family dependent on a loop $p : a = a$ cannot be handled by path induction, so we cannot prove all loops are $\mathsf{refl}$. What we can prove is that the *pair* $(x, p)$ equals $(x, \mathsf{refl}_x)$ in $\sum_{y:A}(x = y)$. Homotopically, the based path space is contractible even though individual loops need not be trivial. The book's punctured-disc rope example makes this concrete: a loop around the hole cannot be contracted with both ends fixed, but can if one end is free.

```lean
-- J in Lean 4 (Eq.rec); based path induction is Lean's native form:
example {A : Type} {a : A} (C : (x : A) → a = x → Type) (c : C a rfl) :
    (x : A) → (p : a = x) → C x p := fun _ p => by cases p; exact c
```

```rust
// No Rust analogue of a type that depends on a *proof*; the nearest idiom is a
// typestate/witness: `struct Eq<A, B>(PhantomData<(A, B)>)` with a private ctor `refl::<A>() -> Eq<A, A>`,
// from which only `fn cast<A, B>(e: Eq<A, B>, a: A) -> B` (indiscernibility of identicals) can be written.
```

## 10. How this feeds the project

**Type Theory (`type-theory`).**
- *Load-bearing for the kernel.* The judgment forms $a : A$ and $a \equiv b : A$, together with the context as an ordered dependent list, are the exact interface of the trusted kernel. Separating `infer`/`check` from a `conv`/`isDefEq` that decides $\equiv$ is the architecture the book assumes. The "conversion rule" ($a : A$ and $A \equiv B$ give $a : B$) is the one place where definitional equality enters typing.
- *Load-bearing for the elaborator.* $\beta$, $\eta$ and $\alpha$ (hence capture-avoiding substitution) are what `isDefEq` normalises with. The book's treatment of omitted arguments ($\mathsf{id}(a)$ for $\mathsf{id}_A(a)$) is the specification an elaborator's metavariable unifier must meet. In Lean terms, the elaborator solves `?A` by unifying `?A =?= typeof a`, and the kernel then rechecks the fully explicit term.
- *[[Inductive-Types|Inductive types]].* The five-part template (formation, constructors, eliminators, computation, uniqueness) is a design pattern for implementing $\mathbf{1}$, $\mathbf{0}$, $\mathbf{2}$, $\mathbb{N}$, $A+B$ and $\Sigma$ in the kernel. Each eliminator type can be generated mechanically, which is the stepping stone to a general inductive-type schema.
- *Refinement types.* $\sum_{x:A} P(x)$ is exactly the refinement-type encoding $\{x : A \mid P(x)\}$, and the dependent-pair projection $\mathsf{pr}_2 : P(\mathsf{pr}_1(p))$ is how a refinement predicate is recovered.

**Automated Reasoning (`automated-reasoning`).**
- Propositions as types is the reason a proof object can be handed to the kernel and checked by the ordinary type checker (proof certificates, proof reconstruction). Proof search over $\Pi$/$\Sigma$/$+$ is type inhabitation.
- Path induction and indiscernibility of identicals are the proof-theoretic form of rewriting ("replace equals by equals"). A `rewrite` tactic is a use of the $J$ eliminator.
- Substitution and context validity (the ordered-list requirement) are the plumbing shared with Hoare-logic soundness.

Not every part of this chapter bears on the compiler. The set-versus-type philosophy of §1.1 and the homotopical reading of path induction are background for the rest of the book and carry no direct implementation payoff.

```
Judgments (a:A, a≡b:A) ──► Contexts (ordered) ──► Substitution/α,β,η
        │                                              │
        ▼                                              ▼
 Type formers: →, Π, ×, Σ, +, 0, 1, 2, ℕ        isDefEq / kernel conv
        │  (formation / intro / elim / computation / uniqueness)
        ▼
 Propositions-as-types  ──►  Identity type, J  ──►  Ch.2 homotopy structure, univalence
```
