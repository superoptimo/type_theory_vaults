In Martin-Löf’s Type Theory (MLTT), there is a strict **two-level division** between the raw syntax of expressions (governed by **arities**) and the semantic judgements of the type system (governed by **sets** or **types**).

To see how MLTT builds concrete sets on top of this syntactic foundation, we can look at the construction of the **natural numbers ($N$)**.

---

### 1. The Syntactic Level: Raw Expressions and Arities

At the base level, MLTT utilizes Per Martin-Löf's general theory of mathematical expressions. Every constant and variable is assigned a unique, fixed **arity** (representing its syntactic "functionality" or category) to ensure that definitional equality remains decidable and that syntactic nonsense is filtered out from the start.

For the natural numbers, the language declares three primitive syntactic constants with their respective arities:

- **$0$** : Arity **$0$** (representing a single, saturated expression).
- **$succ$** : Arity **$0 \to 0$** (an unsaturated operator that takes an expression of arity $0$ and yields one of arity $0$).
- **$natrec$** (the primitive recursor) : Arity **$0 \otimes 0 \otimes (0 \otimes 0 \to 0) \to 0$**.

Using the inductive rules of arity, we can construct raw, well-formed expressions such as $0$, $succ(0)$, and $natrec(n, d, e)$. However, at this purely grammatical level, **these expressions do not yet belong to any set**. They are simply raw, tree-like syntactic arrangements of symbols.

---

### 2. The Semantic/Type-Theoretic Level: Elevating Arities to the Set $N$

To give these raw syntactic trees mathematical and computational meaning, MLTT introduces the set **$N$** (formally $N \text{ set}$ or $N : \text{Set}$). In MLTT, explaining a set requires defining its **canonical elements** (the values of programs) and their **equality relation**.

The set $N$ is built on top of the arity layer through four standard rules of the type theory:

#### A. Formation Rule

We assert that $N$ is a well-formed set in the type system: 
$$\Gamma \vdash N \text{ set} \quad (\text{or } \Gamma \vdash N : \text{Set}) \quad$$

#### B. Introduction Rules (Defining Canonical Elements)

We specify how to construct the elements of $N$ using our syntactic constants. This defines the **canonical elements** of $N$:

1. **$0 \in N$**
2. If $n \in N$, then **$succ(n) \in N$**.

Syntactically, $0$ and $succ(n)$ are saturated expressions of arity $0$. Semantically, they are now recognized by the type system as the canonical inhabitants (values) of the set $N$.

#### C. Elimination Rule (The Selector `natrec`)

To compute with these numbers, we use the syntactic selector constant $natrec$. The elimination rule dictates that if we have a type family $C(x)$ indexed over $x \in N$, we can perform **induction** (or primitive recursion):

- If we have a base case $c_0 \in C(0)$,
- And an inductive step $c_s \in (x : N) \to C(x) \to C(succ(x))$,
- Then for any element $n \in N$, the expression **$natrec(n, c_0, c_s)$** is a valid element of $C(n)$.

#### D. Computation/Equality Rules

The operational behavior of the selector is defined by how it evaluates when its first argument reduces to a canonical form:

1. If the argument evaluates to the canonical form $0$, then: \[natrec(0, d, e) \equiv d \quad\]
2. If the argument evaluates to the canonical form $succ(b)$, then: \[natrec(succ(b), d, e) \equiv e(b, natrec(b, d, e)) \quad\]

---

### 3. Syntactic vs. Type-Theoretic Equality

This two-level structure explains why MLTT maintains a sharp distinction between two forms of equality:

- **Definitional (Intensional) Equality ($a \equiv b : \alpha$)**: This is a cheap, decidable, syntactic equivalence checked at the **arity level**. It checks if two expressions reduce to the same syntax tree via $\beta$-rules or macro expansions without needing to know anything about set memberships.
- **Judgemental/Type-Theoretic Equality ($a = b \in A$)**: This is a **semantic judgement**. It depends entirely on the set $A$ and is only meaningful if $a$ and $b$ are first derived as elements of $A$.

By keeping the raw arity grammar simple and separate from typing derivations, Per Martin-Löf ensured that the syntax of expressions remains completely tractable and decidable, even while building highly complex, mutually dependent, and self-referential mathematical sets on top of it.

