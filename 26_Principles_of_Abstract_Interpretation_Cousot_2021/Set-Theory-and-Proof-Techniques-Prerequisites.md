---
title: Set Theory and Proof Techniques Prerequisites
source: Principles of Abstract Interpretation (Patrick Cousot, 2021)
chapters: Chapter 2 "Basic Set Theory" (pp. 18–30); Chapter 3, §3.8 "Proofs by Structural Induction" (pp. 38–39)
tags: [abstract-interpretation, set-theory, proof-techniques, foundations, cousot]
---

[[book-guidelines|↩ Back to guidelines]]

## Why the book stops to do this at all

Cousot is about to spend thirty-five chapters building an entire theory on top of a handful of moves: *treat a program's possible behaviors as a set*, *treat a proof obligation as a set inclusion*, *treat "the abstraction is safe" as one set containing another*. None of that works unless the reader is fluent in exactly four things: what a set-builder expression actually claims, what a relation/function is *as a set* (not as a black-box procedure), what it means to reduce a logical property to a set membership question, and which small toolbox of proof techniques (contraposition, contradiction, recurrence, structural induction) will be reused, unannounced, on every later chapter's lemmas. Chapter 2 is Cousot clearing his throat before the real material starts — but it is a deliberately chosen throat-clearing, because the very first substantive design decision of the book (properties are sets, not formulas) is stated here, and it is the decision that makes the rest of the calculational method possible.

## 1. Terms and predicates: the raw notation

Before sets, the book fixes vocabulary for two kinds of mathematical writing (§2.1.1–2.1.2):

- **Terms** are symbolic expressions denoting *entities*: constants ($0$, $-42$), variables ($x, y$), and operations ($+, -, \times, |\cdot|$). Cousot is careful to distinguish a **mathematical variable** — a fixed, possibly-unknown entity, as in $\forall x \in \mathbb{Z}$ — from a **program variable**, which stores a value that changes over time via [[Forward-Reachability-Semantics#Assignment|assignment]]. This distinction matters immensely later: much of the book's semantics machinery exists precisely to formalize what a program variable's "current value" even means (Chapter 6 revisits this by reconstructing a variable's value from a stateless trace's assignment history).
- **Predicates** are terms that evaluate to $\mathbb{B} \triangleq \{\mathrm{tt}, \mathrm{ff}\}$, combined with the usual logical connectives $\vee, \wedge, \neg, \Rightarrow, \Leftrightarrow$ and quantifiers $\forall, \exists, \exists!$.

Two notational habits from this section recur constantly in the rest of the book, so they're worth internalizing now rather than re-deriving each time they appear:

- **Definitional equality**, $p \triangleq P$: defines the *definiendum* $p$ to *be* the *definiens* $P$, as opposed to asserting a fact about two already-existing things. E.g. $2 \triangleq 1+1$.
- **Sufficient vs. necessary conditions.** If $P \Rightarrow Q$, $P$ is a sufficient condition for $Q$ and $Q$ is a necessary condition for $P$; $P \Leftrightarrow Q$ makes $P$ necessary *and* sufficient for $Q$. This bookkeeping shows up whenever the book later argues that an abstract analysis's answer is a sound (but not necessarily complete) approximation of the concrete truth — soundness is exactly "the abstract answer being $\mathrm{tt}$ is a sufficient condition for the concrete property to hold," while completeness would additionally require necessity.

*Grounding.* This is really just typed logic notation, and the closest everyday analogue is a language's own boolean/predicate layer:

```python
# tt / ff as Python bool; forall/exists as generator expressions
def forall(iterable, p):
    return all(p(x) for x in iterable)

def exists(iterable, p):
    return any(p(x) for x in iterable)

# "for all n in N, (n+1)-1 = n" holds; "(n-1)+1 = n" fails at n = 0
naturals = range(0, 1000)
assert forall(naturals, lambda n: (n + 1) - 1 == n)
assert not forall(naturals, lambda n: (n - 1) + 1 == n)   # n = 0 is the counterexample
```

```rust
// A "term" is just an expression; a "predicate" is bool-valued.
fn implies(p: bool, q: bool) -> bool { !p || q }   // P ⇒ Q, per exercise 2.2

fn holds_for_all_nat(n_max: u32, pred: impl Fn(u32) -> bool) -> bool {
    (0..n_max).all(pred)
}
```

```lean
-- Lean's `∀`/`∃`/`→` ARE this notation, not an encoding of it —
-- the book's ∀x. P(x) is literally Lean's `∀ x, P x`.
example : ∀ n : ℕ, (n + 1) - 1 = n := by intro n; omega
example : ¬ (∀ n : ℕ, (n - 1) + 1 = n) := by
  intro h; have := h 0; simp at this
```

## 2. Sets, relations, and functions as one uniform vocabulary

### 2.1 Sets, set-builder, and the algebra of $\subseteq$

The book takes naive set theory as given: $x \in S$, $\emptyset$, singletons $\{x\}$, and — the workhorse notation for the rest of the book — the **set-builder** $\{x \mid p(x)\}$, satisfying $x \in \{y \mid p(y)\} \Leftrightarrow p(x)$ (§2.1.3). Standard operations follow: $\cup, \cap, \setminus$, complement $\neg S \triangleq U \setminus S$ relative to an ambient $U$, De Morgan's laws, the powerset $\wp(S) \triangleq \{S' \mid S' \subseteq S\}$ and the *finite* powerset $\wp_f(S) \triangleq \{S' \mid S' \subseteq S \wedge |S| \in \mathbb{N}\}$.

Two points the book makes explicitly that are easy to elide in casual set-theory usage but are load-bearing later:

- $\emptyset \subseteq S'$ *always* holds, vacuously — this convention underwrites definitions later in the book where the strongest possible property is $\emptyset$ (see §2.3.2 below), and $\bot$ of the empty poset is exactly this bottom.
- **Complement duality**: if $P \Leftrightarrow Q$ using only $\vee/\exists/\cup$, $\wedge/\forall/\cap$, and $\neg$, then swapping each connective for its dual and negating the free variables gives another valid equivalence. This is the *baby version* of the **duality principle** for posets that Chapter 10 elevates to a general theorem (swap $\sqsubseteq \leftrightarrow \sqsupseteq$, $\sqcup \leftrightarrow \sqcap$) — worth noticing now that the pattern already exists at the level of naive sets, before it gets reified as an order-theoretic principle.

*Grounding.*

```python
def powerset(s):
    s = list(s)
    from itertools import combinations
    return {frozenset(c) for r in range(len(s)+1) for c in combinations(s, r)}

S = {0, 1}
assert powerset(S) == {frozenset(), frozenset({0}), frozenset({1}), frozenset({0, 1})}
```

```rust
use std::collections::HashSet;

fn de_morgan_union<T: std::hash::Hash + Eq + Clone>(
    s: &HashSet<T>, s2: &HashSet<T>, universe: &HashSet<T>,
) -> bool {
    let complement = |a: &HashSet<T>| -> HashSet<T> {
        universe.difference(a).cloned().collect()
    };
    let lhs = complement(&s.union(s2).cloned().collect());
    let rhs: HashSet<T> = complement(s).intersection(&complement(s2)).cloned().collect();
    lhs == rhs   // ¬(S ∪ S') = (¬S) ∩ (¬S')
}
```

```lean
-- De Morgan for finite sets is a one-liner from the library, mirroring §2.1.3, exercise 2.5.
example (S S' U : Finset ℕ) (hS : S ⊆ U) (hS' : S' ⊆ U) :
    U \ (S ∪ S') = (U \ S) ∩ (U \ S') := by
  ext x; simp; tauto
```

### 2.2 Kuratowski pairs: sets encoding order

Rather than taking "ordered pair" as primitive, the book adopts **Kuratowski's encoding** (§2.2): $\langle x, y \rangle \triangleq \{\{x\}, \{x,y\}\}$, from which the first/second projections $\langle x,y\rangle_1 = x$ and $\langle x,y\rangle_2 = y$ are *derived*, not assumed. This is a small but telling methodological signal for the whole book: Cousot repeatedly prefers to *construct* a notion from set theory rather than to postulate it as a primitive with axioms attached — the same instinct that later drives the book's preference for *calculational design* (deriving an abstract semantics from a Galois connection) over *postulate-then-prove-sound*.

From pairs, the **Cartesian product** $S_1 \times S_2 \triangleq \{\langle x,y\rangle \mid x \in S_1 \wedge y \in S_2\}$ and $n$-ary tuples follow, with both index-subscript ($\langle x_1,\ldots,x_n\rangle_i$) and functional ($\langle x_1,\ldots,x_n\rangle(i)$) notations for projection, generalizing when the index set isn't literally $\{1,\ldots,n\}$ to the *indexed-product* notation $\Pi_{i \in \Delta} x_i$.

### 2.3 Relations

A **binary relation** on $S_1, S_2$ is, set-theoretically, nothing but $r \in \wp(S_1 \times S_2)$ (§2.2.2) — "relation" is not a new primitive, it *is* a set of pairs. From this single definition the book derives: domain, codomain, field; left/right restriction $r\rceil S$ / $r\lceil S$; composition $r_1 \, r_2$; inverse $r^{-1}$; and the observation that $\langle \wp(S \times S), \,\cdot\,, \mathrm{id}_S\rangle$ is a **monoid** (associative composition, identity relation as neutral element) — but *not* a group (exercise 2.9), because relation composition generally isn't invertible even though the notation $r^{-1}$ exists (that notation denotes the *converse* relation, not a compositional inverse).

**Equivalence relations** (reflexive, symmetric, transitive) partition a set into equivalence classes $[x]_\equiv \triangleq \{y \in S \mid y \equiv x\}$, and the **quotient set** $S/{\equiv} \triangleq \{[x]_\equiv \mid x \in S\}$ collects them (§2.2.3) — the mechanism the book later reuses to turn a *preorder* into a genuine *partial order* by quotienting out mutually-related elements (Chapter 10).

**Partial orders** ($\le$ reflexive, antisymmetric, transitive) give a **poset** $\langle S, \le \rangle$, with strict order $x < y \triangleq (x \le y) \wedge (x \ne y)$ and totality $\forall a,b \in S.\ (a \le b) \vee (b \le a)$. This is the single most important definition of the chapter for the rest of the book: essentially every subsequent chapter (7 through roughly 22) operates on some poset — of program properties ordered by $\subseteq$, of abstract values ordered by precision $\sqsubseteq$, of closure operators ordered by pointwise comparison — and it is *this* definition, stripped down to three axioms, that all of them instantiate.

*Grounding.*

```python
from dataclasses import dataclass
from typing import Callable, TypeVar, Generic

T = TypeVar("T")

@dataclass
class Poset(Generic[T]):
    elements: set[T]
    le: Callable[[T, T], bool]

    def is_total(self) -> bool:
        return all(self.le(a, b) or self.le(b, a)
                   for a in self.elements for b in self.elements)

# <Z, <=> restricted to {-1,0,1,2}: a total order
divides = Poset({1, 2, 3, 6}, le=lambda a, b: b % a == 0)  # divisibility poset: NOT total
assert not divides.is_total()   # 2 and 3 are incomparable
```

```rust
// A relation as a literal set of pairs, per §2.2.2 — composition and inverse follow directly.
use std::collections::HashSet;

fn compose(r1: &HashSet<(i32, i32)>, r2: &HashSet<(i32, i32)>) -> HashSet<(i32, i32)> {
    // r1 ; r2 = { (x,z) | ∃y. (x,y) ∈ r1 ∧ (y,z) ∈ r2 }
    let mut out = HashSet::new();
    for &(x, y) in r1 {
        for &(y2, z) in r2 {
            if y == y2 { out.insert((x, z)); }
        }
    }
    out
}

fn inverse(r: &HashSet<(i32, i32)>) -> HashSet<(i32, i32)> {
    r.iter().map(|&(x, y)| (y, x)).collect()
}
```

```lean
-- Poset as a structure with exactly the three axioms of §2.2.3 — Mathlib's `PartialOrder`
-- IS this definition, verbatim.
example (α : Type) [PartialOrder α] (x y : α) : x ≤ x := le_refl x                -- reflexive
example (α : Type) [PartialOrder α] (x y : α) (h1 : x ≤ y) (h2 : y ≤ x) : x = y :=
  le_antisymm h1 h2                                                                -- antisymmetric
```

### 2.4 Functions: partial, total, and their properties

A relation $r$ is **functional** when each $x$ has at most one image; a **partial function** $f \in S_1 \rightharpoonup S_2$ is such a relation, with $f(x)$ defined exactly on $\mathrm{dom}(f)$; a **total function** $f \in S_1 \to S_2$ additionally has $\mathrm{dom}(f) = S_1$ (§2.2.4). Injective ($S_1 \hookrightarrow S_2$), surjective ($S_1 \twoheadrightarrow S_2$), and bijective ($S_1 \cong S_2$) functions are defined the expected way, with isomorphism of sets meaning "a bijection exists between them."

Notably, this section also introduces **dependent types** as a mathematical (not just programming-language) notion: $f \in x \in S_1 \to S_2(x)$, where the codomain $S_2(x)$ varies with the input $x$ — e.g., $f \in n \in \mathbb{N} \to \{k \in \mathbb{N} \mid k \ge n\}$. This is a genuinely forward-looking notational choice: it lets the book later write things like "a family of posets indexed by $\Delta$" or "an abstract domain parameterized by the concrete domain" without inventing new machinery each time.

Two more constructions matter for later chapters:
- **Families** $F \in \Delta \to S$ (§2.2.5): a map from an index set into $S$, used throughout for indexed unions/products of abstract domains and for iterates of a fixpoint computation (Chapter 11 onward — a "chain" is exactly a family indexed by an ordinal).
- **Recursive definitions** (§2.2.6): $f(0) \triangleq c$, $f(n) \triangleq F(n, f(n-1))$. Cousot flags immediately that such definitions can be **ill-defined** (his example: $f(0) \triangleq 0$, $f(n) \triangleq f(n+1)$ for $n \ne 0$, which is undefined for all $n > 0$) — so *well-definedness itself needs proof*. This single caution is the seed of a major later concern: Chapter 12 generalizes recursive definitions to *inductive* ones and spends real effort establishing when a fixpoint-based definition is guaranteed to exist and be unique, precisely because "I wrote a recursive equation" does not by itself guarantee a well-defined mathematical object.

*Grounding.*

```python
from typing import Optional

# Partial function as an explicit dict; total function as one guaranteed to cover the domain.
def partial_sqrt(n: int) -> Optional[int]:
    r = int(n ** 0.5)
    return r if r * r == n else None   # dom(f) = perfect squares only

# An ILL-DEFINED recursive definition, mirroring the book's cautionary example:
def f(n: int) -> int:
    if n == 0:
        return 0
    return f(n + 1)   # never terminates for n > 0 — "recursive" is not automatically "well-defined"
```

```rust
// Dependent-type flavor: a function whose return type's INVARIANT depends on the input,
// approximated in Rust via a refinement-style wrapper (Rust has no true Π-types).
struct AtLeast<const N: u32>(u32);
fn ge_n<const N: u32>(k: u32) -> Option<AtLeast<N>> {
    if k >= N { Some(AtLeast(k)) } else { None }
}
```

```lean
-- Lean's Π-type IS the book's dependent function f ∈ x ∈ S₁ → S₂(x), not an approximation of it.
def atLeast (n : ℕ) : Type := { k : ℕ // k ≥ n }
def f (n : ℕ) : atLeast n := ⟨n, le_refl n⟩   -- f(n) ≥ n, by construction

-- The book's ILL-DEFINED f(0)=0, f(n)=f(n+1) for n≠0 has NO total, well-founded Lean encoding —
-- Lean's termination checker would reject it outright, which is exactly the book's point.
```

## 3. The pivotal move: properties *are* sets

Section 2.3 states, in two short paragraphs, a decision that quietly organizes the entire book:

> "Properties... can be understood as the set of mathematical objects that have this property... Hence if $P$ is a property then $x \in P$ means '$x$ has property $P$.'"

This sounds almost too simple to be a "decision" — of course $2\mathbb{Z} \triangleq \{x \in \mathbb{Z} \mid \exists k.\ x = 2k\}$ *is* the property of evenness. But the payoff is in §2.3.2: once properties are sets, **logical implication becomes subset inclusion**, $P \Rightarrow Q$ reduces to $P \subseteq Q$. This single substitution is what lets the book say a property is "stronger/more precise" (fewer satisfying elements, smaller set) or "weaker/less precise" (more satisfying elements, larger set) using only $\subseteq$ — with $\mathrm{ff} = \emptyset$ as the strongest property and $\mathrm{tt} = \mathbb{Z}$ (or the ambient universe) as the weakest.

Why does this matter more here than it would in an ordinary logic course? Because **abstraction itself is going to be defined as a relationship between sets of properties**, via Galois connections (Chapter 11): the entire machinery of "the abstract semantics is a *sound overapproximation* of the concrete one" is stated as $P \subseteq \gamma(\alpha(P))$ — a set inclusion. If properties were instead formulas, checking implication would require a proof theory or a decision procedure for the logic in question (undecidable in general, per Chapter 9's Rice's theorem); as sets, "is $P$ stronger than $Q$" is just "is $P$ a subset of $Q$," a question about sets that the whole toolbox of §2.1–2.2 already answers. The book's opening rhetorical question in the guidelines captures this precisely: treating properties as sets rather than formulas is what makes *reasoning about implication, strength, and abstraction* tractable and uniform throughout the book, rather than needing a bespoke proof system per logic.

*Grounding.* The cleanest way to feel this in code is to represent a "property" not as a boolean-returning function (a formula) but as an actual set (or a set-membership predicate treated purely extensionally), and to implement "stronger than" as literal subset containment:

```python
# A property IS a set (here: a Python predicate treated purely extensionally over a fixed universe).
Universe = range(-100, 100)

def as_set(pred):
    return frozenset(x for x in Universe if pred(x))

positive       = as_set(lambda x: x > 0)
greater_than_42 = as_set(lambda x: x > 42)

# "greater than 42 implies positive" IS subset inclusion — no proof theory required.
assert greater_than_42 <= positive
```

```lean
-- Lean's `Set α` literally realizes "property = set"; `⊆` literally realizes "implication."
def positive : Set ℤ := {x | x > 0}
def greaterThan42 : Set ℤ := {x | x > 42}

example : greaterThan42 ⊆ positive := by intro x hx; omega
```

## 4. The proof-technique toolbox (§2.4)

Cousot introduces exactly four techniques here, stated tersely because they will be *used*, not re-derived, from Chapter 3 onward.

**Proof by contraposition.** To prove $P \Rightarrow Q$, prove $\neg Q \Rightarrow \neg P$ instead. The justification given is almost a mini reductio: if $P$ holds and $\neg Q$ held, $\neg P$ would follow (from the contrapositive), contradicting $P$; so $\neg Q$ cannot hold, i.e. $Q$ holds.

**Proof by reductio ad absurdum (contradiction).** To prove $P$, find a known truth $Q$ and prove $\neg P \Rightarrow \neg Q$; by contraposition this gives $Q \Rightarrow P$, and since $Q$ is $\mathrm{tt}$, $P$ follows. Notice the book defines *this* technique *in terms of* contraposition rather than as an independent primitive — another instance of the "derive, don't postulate" instinct from §2.2's Kuratowski pairs.

**Proof by recurrence (mathematical induction).** Theorem 2.13: to prove $\mathbb{N} \subseteq P$ (i.e. $P$ holds of every natural), it suffices to prove $0 \in P$ (base case) and $\forall n \in \mathbb{N}.\ (n \in P) \Rightarrow (n+1 \in P)$ (inductive step, with $n \in P$ the *induction hypothesis*). What's unusual — and a strong signal of the book's overall rigor level — is that Cousot doesn't just state the principle, he proves **both directions**:

- *Soundness* (a proof by recurrence is a valid proof): by reductio ad absurdum. Assume the recurrence proof was made but $\mathbb{N} \not\subseteq P$; then some $n \notin P$ exists. $n \ne 0$ (since $0 \in P$ was proved), so $n = (n-1)+1$; by contraposition of the inductive step, $n \notin P \Rightarrow n-1 \notin P$, and iterating this descent, $n-2 \notin P, n-3 \notin P, \ldots, 0 \notin P$ — contradicting $0 \in P$. (This is explicitly identified as **Fermat's infinite-descent method**, originally stated contrapositively.)
- *Completeness* (if $\mathbb{N} \subseteq P$ holds, a recurrence proof exists for it): let $Q \triangleq P \cap \mathbb{N}$; since $\mathbb{N} \subseteq P$, $Q = \mathbb{N}$, so trivially $0 \in Q$ and $\forall n \in Q.\ n+1 \in Q$ — the base case and inductive step of a (possibly-strengthened) recurrence proof of $Q$, and $\mathbb{N} \subseteq Q = P \cap \mathbb{N} \subseteq P$.

The guidelines' own key question — *why bother proving both* — has a direct answer visible in the proof itself: soundness alone would tell you recurrence never lies, but completeness is what tells you recurrence is never *too weak a tool* — any true universal fact about the naturals *can*, in principle, be established this way (possibly after strengthening the induction hypothesis, exactly the move used throughout the book when a naive inductive invariant needs augmenting to go through — see Chapter 17's fixpoint induction and Chapter 18's Hoare-logic verification conditions, both of which are recurring instances of "strengthen the invariant, then recurrence/induction closes the case").

**Proof by structural induction** is only *named* in the Chapter 2 conclusion's promissory note ("additional topics... covered subsequently, as needed") but delivered in full in §3.8, immediately after the book needs it for the very first time (to prove properties of the recursively/structurally defined syntax of arithmetic and Boolean expressions). Rod Burstall's principle, quoted directly: *"If for some set of structures a structure has a certain property whenever all its proper constituents have that property then all the structures in the set have the property."* Concretely, to prove $P$ holds for every expression $E \in \mathbb{E}$: prove $P$ for the base cases ($\mathtt{1}$ and variables $x$), then prove $P$ for each composite form *assuming* $P$ already holds of its immediate sub-expressions (e.g., assuming $P(A_1)$ and $P(A_2)$, prove $P(A_1{-}A_2)$ and $P(A_1{<}A_2)$; assuming $P(B_1)$ and $P(B_2)$, prove $P(B_1 \,\mathrm{nand}\, B_2)$) — concluding $\mathbb{E} \subseteq P$.

Structural induction is exactly proof by recurrence with $\mathbb{N}$'s "$n \to n+1$" successor structure replaced by an expression grammar's "constituents $\to$ composite" structure — the same base-case/inductive-step shape, generalized from one well-founded structure (the naturals under $<$) to another (an abstract syntax tree under "is-a-proper-subterm-of"). This generalization is exactly what the book needs, since almost every semantic definition from Chapter 3 onward (the semantics of expressions, then of statements, then trace semantics) is itself defined *structurally* (recursively over syntax) — so *proving anything about those semantics* requires proving it the same way the semantics was built: one syntax case at a time.

*Grounding.*

```python
# Proof by recurrence -> code by recursion: computing over N with base case + inductive step.
def factorial(n: int) -> int:
    if n == 0:
        return 1          # base case: 0 ∈ P
    return n * factorial(n - 1)   # inductive step, using the "induction hypothesis" factorial(n-1)

# Structural induction -> recursion over an inductively defined datatype (not over N).
from dataclasses import dataclass
from typing import Union

@dataclass
class Lit: value: int
@dataclass
class Sub: left: "Expr"; right: "Expr"      # A1 - A2
Expr = Union[Lit, Sub]

def eval_expr(e: Expr) -> int:
    match e:
        case Lit(v):
            return v                          # base case: property proved directly for 1, x
        case Sub(l, r):
            return eval_expr(l) - eval_expr(r)  # inductive step: assumes it holds for l, r
```

```rust
// Structural induction over an AST is literally how a recursive-descent evaluator
// is proved correct: base cases for leaves, inductive step per constructor.
enum Expr {
    Lit(i64),
    Sub(Box<Expr>, Box<Expr>),
}

fn eval(e: &Expr) -> i64 {
    match e {
        Expr::Lit(v) => *v,                          // base case
        Expr::Sub(a, b) => eval(a) - eval(b),         // inductive step (assumes correctness on a, b)
    }
}
```

```lean
-- Lean's structural recursion on an inductive type IS Burstall's principle, and the
-- termination checker mechanically verifies the "well-definedness" caveat of §2.2.6.
inductive Expr where
  | lit : Int → Expr
  | sub  : Expr → Expr → Expr

def eval : Expr → Int
  | .lit v   => v
  | .sub a b => eval a - eval b

-- A property proved "by structural induction on Expr" is literally an Expr.rec / `induction e`
-- Lean tactic invocation — the base/inductive cases it generates ARE Burstall's two clauses.
example (e : Expr) : True := by induction e <;> trivial
```

## Synthesis: what this chapter buys the rest of the book

```
Sets, relations, functions (§2.1–2.2)
        │
        ├── posets ⟨S, ≤⟩ ───────────────► Ch. 7/10: posets, lattices, complete lattices
        │                                       │
        │                                       ▼
        ├── properties AS sets, ⇒ = ⊆ ────► Ch. 8: program properties as sets of semantics
        │   (§2.3)                              │
        │                                       ▼
        │                                Ch. 11: Galois connections
        │                                (soundness = a set inclusion P ⊆ γ(α(P)))
        │
        ├── recursive definitions,
        │   well-definedness caveat ──────► Ch. 12: deductive/inductive/coinductive definitions
        │   (§2.2.6)                             (fixpoints as the well-definedness fix)
        │
        └── contraposition, reductio,
            recurrence (§2.4) ┐
                               ├──► Ch. 3 §3.8: structural induction on expression syntax
                               │         │
                               │         ▼
                               └──► used silently in nearly every later lemma/theorem
                                    (e.g., Ch. 9 Rice's theorem by reduction+contradiction;
                                     Ch. 17–18 verification proofs by fixpoint/structural induction)
```

Nothing in this chapter is abstract-interpretation-specific yet — there's no notion of "abstract domain" or "concretization" anywhere in it. That's precisely the point: Chapter 2 is the shared mathematical substrate the *entire* calculational method sits on. The one idea worth carrying forward above all others is §2.3's reduction of *properties* to *sets* and *implication* to $\subseteq$ — it is the reason the rest of the book can talk about "how precise is this analysis" and "is this abstraction sound" using nothing but set inclusion and Galois connections, instead of needing a separate proof theory for every logic a given static analysis might be phrased in.
