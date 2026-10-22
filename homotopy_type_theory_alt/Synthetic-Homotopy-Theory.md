---
title: Synthetic Homotopy Theory
book: Homotopy Type Theory - Univalent Foundations of Mathematics
chapters: Chapter 8 (Homotopy theory), printed pp. 259–306
tags:
  - homotopy-type-theory
  - synthetic-homotopy-theory
  - encode-decode
  - univalence
  - untagged-application
---

[[book-guidelines|↩ Back to guidelines]]

# Synthetic Homotopy Theory

## 1. Why this chapter exists

Chapters 1–7 built a calculus: types are $\infty$-groupoids, $a = b$ is a path space, univalence makes equivalences into paths, and [[Higher-Inductive-Types|higher inductive types]] (HITs) let us *name* spaces by generators. Chapter 8 asks whether the calculus is any good. The test is classical algebraic topology: can we compute the invariants that topologists use to tell spaces apart, using only the rules of the identity type, without ever defining a topological space?

"Synthetic" means points, paths and homotopies are not *built from* something (sets of points with a topology). They are the primitives, and a type's identity types supply the rest. Associativity of path concatenation is proved by path induction, not by reparametrising maps $[0,1]\to X$. The authors list three payoffs:

1. Proofs are elementary but abstract, so they hold in every model (Kan simplicial sets, $(\infty,1)$-toposes).
2. The only tools are path induction and the universal properties of HITs, and this has produced new constructions (the universal cover of the circle, the Hopf fibration).
3. The proofs are constructive and computer-checkable. The text notes that most of the chapter was checked in Coq and Agda.

The chapter's central lesson is a *proof technique*, the **encode-decode method**, applied six times with variations.

## 2. The invariant: homotopy groups as truncated loop spaces

Classically $\pi_1(X,x_0)$ is the group of loops at $x_0$ up to homotopy. $\pi_2$ is homotopies between the constant loop and itself, and so on. The book makes this literal. For a pointed type $(A,a)$, iterate loop spaces:

$$\Omega^0(A,a) = (A,a), \qquad \Omega^{n+1}(A,a) = \Omega^n(\Omega(A,a)).$$

**Definition 8.0.1.** For $n \ge 1$,

$$\pi_n(A,a) :\equiv \big\|\Omega^n(A,a)\big\|_0 .$$

Concatenation and inversion induce a group structure, and for $n \ge 2$ the group is abelian by the Eckmann–Hilton argument (Theorem 2.1.6). Also $\pi_0(A) :\equiv \|A\|_0$, which is not a group and needs no basepoint.

The 0-truncation matters. $\Omega^n(A,a)$ is a whole higher groupoid. Truncating to a set throws away the higher paths and leaves "loops up to homotopy". A HIT presents a type *freely* (as generators), but it does not hand you its identity types. Those are populated by the generators together with all groupoid operations. So "what is $\Omega(\mathbb S^1)$, really?" is a real question with a nontrivial answer. This is the same phenomenon as proving $0_{\mathbf 2}\neq 1_{\mathbf 2}$ (§2.12): the definition of an inductive type does not immediately describe its equality.

The book's Table 8.1 shows how hard the general problem is. There is no closed form for $\pi_k(\mathbb S^n)$. The first nontrivial surprise is $\pi_3(\mathbb S^2)=\mathbb Z$. The sphere $\mathbb S^2$ has no 3-dimensional generator, so the generator comes from the *interchange law* of the $\infty$-groupoid structure, not from any constructor.

## 3. §8.1 — $\pi_1(\mathbb S^1)=\mathbb Z$ and the encode-decode method

### 3.1 The obvious attempt and why it stalls

Define $\mathsf{loop}^{(-)}:\mathbb Z\to(\mathsf{base}=\mathsf{base})$ by iterated concatenation, from Corollary 6.10.13. For the other direction, $\mathsf{succ}:\mathbb Z\to\mathbb Z$ is an equivalence, so univalence gives $\mathsf{ua}(\mathsf{succ}):\mathbb Z=\mathbb Z$ in the universe. Circle recursion then gives a family $c:\mathbb S^1\to\mathcal U$ with $c(\mathsf{base}):\equiv\mathbb Z$ and $\mathsf{ap}_c(\mathsf{loop}):=\mathsf{ua}(\mathsf{succ})$. Define

$$g(p) :\equiv \mathsf{transport}^{X\mapsto X}(\mathsf{ap}_c(p),\,0).$$

One composite is easy: $g(\mathsf{loop}^n)=n$. The other, $\mathsf{loop}^{g(p)}=p$, resists. The reason is that path induction needs one free endpoint, and a loop $p:\mathsf{base}=\mathsf{base}$ has both endpoints fixed.

### 3.2 The fix: generalise from the fibre to the whole family

The classical proof uses the universal cover $\mathbb R\to\mathbb S^1$, a helix over the circle. Fibrations over $B$ are type families $B\to\mathcal U$. The path fibration is $x\mapsto(x_0=x)$. Its total space is contractible (Lemma 3.11.8), and its fibre over $x_0$ is the loop space by definition.

The type-theoretic cover is exactly the family $c$ above:

**Definition 8.1.1.** $\mathsf{code}:\mathbb S^1\to\mathcal U$ with $\mathsf{code}(\mathsf{base}):\equiv\mathbb Z$ and $\mathsf{ap}_{\mathsf{code}}(\mathsf{loop}):=\mathsf{ua}(\mathsf{succ})$.

**Lemma 8.1.2.** $\mathsf{transport}^{\mathsf{code}}(\mathsf{loop},x)=x+1$ and $\mathsf{transport}^{\mathsf{code}}(\mathsf{loop}^{-1},x)=x-1$.

What was wrong earlier was defining maps only on the fibres $\Omega(\mathbb S^1)$ and $\mathbb Z$. We need maps of *fibrations*, i.e. functions quantified over all $x:\mathbb S^1$. This is the standard trick of generalising an induction hypothesis from a particular inhabitant to all inhabitants.

### 3.3 The encode-decode proof

$$\mathsf{encode}:\prod_{x:\mathbb S^1}(\mathsf{base}=x)\to\mathsf{code}(x),\qquad \mathsf{encode}\,p:\equiv\mathsf{transport}^{\mathsf{code}}(p,0).$$

Read it operationally. A path built as $\mathsf{loop}\cdot\mathsf{loop}^{-1}\cdot\mathsf{loop}\cdots$ transports to $\mathsf{succ}\circ\mathsf{pred}\circ\mathsf{succ}\cdots$. Applying that to $0$ computes the **winding number**. The abstract groupoid is computed by a concrete function, because univalence and HIT recursion have computation rules.

$$\mathsf{decode}:\prod_{x:\mathbb S^1}\mathsf{code}(x)\to(\mathsf{base}=x)$$

is defined by circle induction. At $\mathsf{base}$ it is $\mathsf{loop}^{(-)}$. The obligation that it respects $\mathsf{loop}$ is a dependent path, computed by the characterisation of transport in a function type. It reduces to $\mathsf{loop}^{n-1}\cdot\mathsf{loop}=\mathsf{loop}^n$.

- **Lemma 8.1.7.** $\mathsf{decode}_x(\mathsf{encode}_x(p))=p$. This is now *easy*. By path induction on $p$ it suffices to treat $\mathsf{refl}_{\mathsf{base}}$, and $\mathsf{encode}(\mathsf{refl})\equiv 0$, $\mathsf{decode}(0)\equiv\mathsf{refl}$. The previously hard direction is easy because the statement is quantified over all $x$, so the endpoint is free.
- **Lemma 8.1.8.** $\mathsf{encode}_x(\mathsf{decode}_x(c))=c$ by circle induction. The $\mathsf{loop}$ case is a path between paths in $\mathbb Z$, trivial because $\mathbb Z$ is a set. The $\mathsf{base}$ case is integer induction.

**Theorem 8.1.9.** $\prod_{x:\mathbb S^1}(\mathsf{base}=x)\simeq\mathsf{code}(x)$. So $\Omega(\mathbb S^1)\simeq\mathbb Z$, as groups. Then $\pi_1(\mathbb S^1)=\mathbb Z$, and $\pi_n(\mathbb S^1)=0$ for $n>1$ because $\Omega^{n-1}(\mathbb Z)$ is contractible for a set.

### 3.4 Two other proofs of the same fact

- **Homotopy-theoretic proof (§8.1.5).** Mirror the classical argument. $\sum_x(\mathsf{base}=x)$ is contractible. $\sum_x\mathsf{code}(x)$ is also contractible by the flattening lemma (Lemma 6.12.2), which reveals it as the "homotopical reals" HIT $R$ with $c:\mathbb Z\to R$ and paths $c(z)=c(\mathsf{succ}\,z)$. An equivalence of total spaces then gives an equivalence of fibres (Theorem 4.7.7).
- **Identity-system proof (§8.1.6).** $(\mathsf{code},0)$ is an identity system at $\mathsf{base}$ in the sense of Definition 5.8.1. This does the inductive work once, generically, instead of twice.

The book's remark is that the encode-decode proof is an "unpackaging" of the homotopy-theoretic one.

### 3.5 Univalence is essential (Remark 8.1.17)

Without univalence it is consistent to assume uniqueness of identity proofs (axiom K, §7.2), and then $\pi_1(\mathbb S^1)\simeq\mathbf 1$. Conversely, if $\mathsf{loop}=\mathsf{refl}_{\mathsf{base}}$, then all types are sets (Lemma 6.4.1). So the nontriviality of $\pi_1(\mathbb S^1)$ *detects exactly* whether the theory is set-like. The step that uses univalence is turning the nontrivial equivalence $\mathsf{succ}$ into a path in $\mathcal U$.

## 4. §§8.2–8.3 — Connectivity and the vanishing of low homotopy groups

Recall $A$ is $n$-connected if $\|A\|_n$ is contractible (§7.5).

- **Theorem 8.2.1.** If $A$ is $n$-connected, then $\Sigma A$ is $(n+1)$-connected. The proof views $\Sigma A$ as the pushout $\mathbf 1\sqcup^A\mathbf 1$, computes the pushout inside $(n+1)$-types, and shows it is $\mathbf 1$.
- **Corollary 8.2.2.** $\mathbb S^n$ is $(n-1)$-connected, by induction since $\mathbb S^{n+1}:\equiv\Sigma\mathbb S^n$.
- **Lemma 8.3.1.** If $A$ is $n$-truncated, then $\pi_k(A,a)=1$ for $k>n$. If $A$ is $n$-connected, then $\pi_k(A,a)=1$ for $k\le n$ (Lemma 8.3.2).
- **Corollary 8.3.3.** $\pi_k(\mathbb S^n)=1$ for $k<n$.

These are cheap but they supply the connectivity bookkeeping for everything after.

## 5. §8.4 — Fibre sequences and the long exact sequence

A **pointed map** $f:X\to Y$ carries a path $f_0:f(x_0)=y_0$. Loop spaces are functorial: $(\Omega f)(p):\equiv f_0^{-1}\cdot f(p)\cdot f_0$. The **fibre sequence** (Definition 8.4.3) iterates "take the fibre of the previous map":

$$\cdots\to X^{(3)}\to X^{(2)}\to X^{(1)}:\equiv X\xrightarrow{f}X^{(0)}:\equiv Y,\qquad X^{(n+1)}:\equiv\mathsf{fib}_{f^{(n-1)}}(x_0^{(n-1)}).$$

**Lemma 8.4.4** identifies the terms: $\Omega Y\to F\to X\to Y$, with $F:\equiv\mathsf{fib}_f(y_0)$, and the following terms are $\Omega X,\Omega F,\dots$, with signs $(-)^{-1}$ on odd loop levels. Applying $\|{-}\|_0$ gives an *exact* sequence of pointed sets (**Theorem 8.4.6**):

$$\cdots\to\pi_k(F)\to\pi_k(X)\to\pi_k(Y)\to\pi_{k-1}(F)\to\cdots\to\pi_0(F)\to\pi_0(X)\to\pi_0(Y).$$

Exactness means image equals kernel. The proof is a short truncation argument: to show $\ker\subseteq\mathrm{im}$ the goal is a mere proposition, so truncation induction lets you pretend the witnesses are untruncated.

Useful consequences: **Lemma 8.4.7** (with $K=0$ the map is injective, with $Q=0$ it is surjective) and **Corollary 8.4.8** (an $n$-connected map induces isomorphisms on $\pi_k$ for $k\le n$ and a surjection for $k=n+1$).

## 6. §8.5 — The Hopf fibration

**Theorem 8.5.1.** There is a fibration over $\mathbb S^2$ with fibre $\mathbb S^1$ and total space $\mathbb S^3$.

The construction is entirely type-theoretic.

1. **Fibrations over pushouts (Lemma 8.5.3).** Given a span $Y\xleftarrow{j}X\xrightarrow{k}Z$, two families $E_Y,E_Z$, and a fibrewise equivalence $e_X(x):E_Y(j\,x)\simeq E_Z(k\,x)$, define $E$ on $Y\sqcup^X Z$ by pushout recursion with $E(\mathsf{glue}(x)):=\mathsf{ua}(e_X(x))$. The flattening lemma shows the total space is the pushout of the total spaces. Univalence is again what lets an equivalence be a path.
2. **H-spaces (Definition 8.5.4).** A type with basepoint $e$ and multiplication $\mu$ satisfying $\mu(e,a)=a=\mu(a,e)$. For a connected H-space each $\mu(a,-)$ is an equivalence (Lemma 8.5.5).
3. **Hopf construction (Lemma 8.5.7).** For a connected H-space $A$, with $\Sigma A=\mathbf 1\sqcup^A\mathbf 1$, use $F_1=F_2=A$ and $e(a)=\mu(a,-)$. The result is a fibration over $\Sigma A$ with fibre $A$ and total space the join $A*A$.
4. **$\mathbb S^1$ is an H-space (Lemma 8.5.8).** $\tilde\mu(\mathsf{base}):\equiv\mathsf{id}$ and $\tilde\mu(\mathsf{loop}):=\mathsf{funext}(h)$, with $h$ from Lemma 6.4.2.
5. **Join identities.** Join is associative (Lemma 8.5.9) and $\Sigma A\simeq\mathbf 2*A$ (Lemma 8.5.10). Hence $\mathbb S^1*\mathbb S^1=(\Sigma\mathbf 2)*\mathbb S^1=\cdots=\Sigma\Sigma\mathbb S^1=\mathbb S^3$.

Feeding the Hopf fibration into the long exact sequence gives **Corollary 8.5.2**: $\pi_2(\mathbb S^2)\simeq\mathbb Z$ and $\pi_k(\mathbb S^3)\simeq\pi_k(\mathbb S^2)$ for $k\ge3$.

## 7. §8.6 — Freudenthal suspension theorem

Suspension $\Sigma X$ has constructors $N,S:\Sigma X$ and $\mathsf{merid}:X\to(N=S)$. There is a canonical map

$$\sigma:X\to\Omega\Sigma X,\qquad \sigma(x):\equiv\mathsf{merid}(x)\cdot\mathsf{merid}(x_0)^{-1}.$$

(The $\mathsf{merid}(x_0)^{-1}$ appears because the suspension here is unreduced, Remark 8.6.3.)

**Theorem 8.6.4 (Freudenthal).** If $X$ is $n$-connected and pointed with $n\ge0$, then $\sigma$ is $2n$-connected.

This is a variant of encode-decode. We want *connectivity of a map into a loop space*, which means contractibility of truncated fibres. So instead of building $\mathsf{code}$ and $\mathsf{decode}$ separately, we build a family of codes for truncated fibres directly:

$$\mathsf{code}(N,p):\equiv\big\|\mathsf{fib}_\sigma(p)\big\|_{2n},\qquad \mathsf{code}(S,q):\equiv\big\|\mathsf{fib}_{\mathsf{merid}}(q)\big\|_{2n}.$$

Defining $\mathsf{code}$ on the path constructor needs the **wedge connectivity lemma** (Lemma 8.6.2). It says that to define a function $\prod_{a,b}P(a,b)$ on $A\times B$ with $A$ $n$-connected and $B$ $m$-connected and $P$ valued in $(n+m)$-types, it suffices to define it on the two axes and check agreement at the origin. Then one shows each $\mathsf{code}(y,p)$ is contractible, with centre given by transport (the analogue of $\mathsf{encode}$).

**Consequences**

- **Corollary 8.6.14.** $\|X\|_{2n}\simeq\|\Omega\Sigma X\|_{2n}$.
- **Corollary 8.6.15 (stability).** $\pi_{k+1}(\mathbb S^{n+1})=\pi_k(\mathbb S^n)$ for $k\le2n-2$.
- **Theorem 8.6.17.** $\pi_n(\mathbb S^n)=\mathbb Z$ for all $n\ge1$, by induction starting from $\pi_1(\mathbb S^1)$ and $\pi_2(\mathbb S^2)$.
- **Corollary 8.6.19.** $\pi_3(\mathbb S^2)=\mathbb Z$, via Hopf plus Freudenthal.
- **Corollary 8.6.18.** $\mathbb S^{n+1}$ is not an $n$-type.

## 8. §8.7 — van Kampen

Statement: for a pushout $P=B\sqcup^A C$, compute $\pi_1(P)$. The type-theoretic version works with the **fundamental groupoid** $\Pi_1X(x,y):\equiv\|x=y\|_0$ and applies encode-decode to a *truncated* path fibration.

- **Naive van Kampen (Theorem 8.7.4).** Define $\mathsf{code}:P\to P\to\mathcal U$ by double induction. For example $\mathsf{code}(i\,b,i\,b')$ is a set-quotient of alternating sequences

$$(b,p_0,x_1,q_1,y_1,p_1,\dots,y_n,p_n,b')$$

with $p_k$ in $\Pi_1B$, $q_k$ in $\Pi_1C$ and $x_k,y_k:A$. The generating relations cancel adjacent identity paths. Then $\Pi_1P(u,v)\simeq\mathsf{code}(u,v)$. It is "naive" because it says nothing about $\pi_1(A)$, which is buried in the quotient. It does recover $\pi_1(\mathbb S^1)\cong\mathbb Z$ (take $A=\mathbf 2$, $B=C=\mathbf 1$) and $\pi_1(B\vee C)\cong\pi_1B*\pi_1C$.
- **With a set of basepoints (Theorem 8.7.12).** Add a surjection $k:S\to A$ and an auxiliary HIT $T$ that improves the connectivity of $k$ to 0-connected (Lemma 8.7.9). Then for $S=\mathbf 1$ one gets the classical statement, the amalgamated free product $\pi_1(P)\cong\pi_1(B)*_{\pi_1(A)}\pi_1(C)$ (Example 8.7.13).
- **Examples.** The torus $T^2$ as a cofibre has $\pi_1=\langle p,q\mid pqp^{-1}q^{-1}\rangle\cong\mathbb Z\times\mathbb Z$ (Example 8.7.15). For any presented group $G=\langle X\mid R\rangle$ there is a type with $\pi_1\cong G$, and its 1-truncation is $K(G,1)$ (Example 8.7.17).

## 9. §8.8 — Whitehead's theorem and principle

Classically, a map inducing isomorphisms on all $\pi_n$ (and on $\pi_0$) is a homotopy equivalence (Whitehead's theorem). In HoTT this is **not provable**, because there are models (non-hypercomplete $\infty$-toposes) where it fails. The book calls **Whitehead's principle** a *classicality axiom*, like LEM or AC. It can be consistently assumed but is not part of the computationally motivated theory.

What *is* provable is the truncated version:

- **Theorem 8.8.1** (analogue of "fully faithful and essentially surjective $\Rightarrow$ equivalence"): $\|f\|_0$ surjective plus $\mathsf{ap}_f$ an equivalence on every path space implies $f$ is an equivalence.
- **Theorem 8.8.3** (Whitehead for $n$-types): for $n$-types $A,B$, if $\|f\|_0$ is a bijection and every $\pi_k(f)$ is a bijection, then $f$ is an equivalence. The proof is by induction on $n$ and *there is no way to start the induction if the types are not $n$-types for any finite $n$*.
- **Corollary 8.8.5** gives the converse of Corollary 8.4.8, characterising $n$-connected maps by homotopy groups.

Types with infinite truncation level exist: an infinite product $C=\prod_n\mathbb S^n$ is not an $m$-type for any $m$ (Example 8.8.6).

## 10. §8.9–8.10 — Encode-decode as a reusable lemma, and what is left out

The book states two specific variants rather than one universal lemma, because different problems need different variants:

**Lemma 8.9.1 (loop spaces).** Given a pointed $(A,a_0)$ and $\mathsf{code}:A\to\mathcal U$ with $c_0:\mathsf{code}(a_0)$ and $\mathsf{decode}:\prod_x\mathsf{code}(x)\to(a_0=x)$, if (iii) $\mathsf{transport}^{\mathsf{code}}(\mathsf{decode}(c),c_0)=c$ and (iv) $\mathsf{decode}(c_0)=\mathsf{refl}$, then $(a_0=a_0)\simeq\mathsf{code}(a_0)$.

**Lemma 8.9.2 (truncated loop spaces)** is the same with $\|a_0=x\|_k$ and $\mathsf{code}(x)$ a $k$-type.

§8.10 only *states* further results without proof: $\pi_{n+1}(\mathbb S^n)=\mathbb Z_k$ for $n\ge3$ (the classical $k$ is 2), the Blakers–Massey theorem, Eilenberg–Mac Lane spaces $K(G,n)$, and covering spaces as $\pi_1$-sets. The $\pi_4(\mathbb S^3)$ computation is notable because the proof is constructive and "the first calculation of a homotopy group for which we have not needed to know the answer in advance".

## 11. Grounding in code

The mathematics here has no direct Rust/Python/Lean implementation, because identity types with nontrivial higher structure require a cubical or HoTT-capable system (Cubical Agda, Arend, or Coq-HoTT). These snippets are *illustrations of the computational content*. They are my own, and I did not compile or run them.

### 11.1 What `encode` computes: the winding number (Rust)

A path in $\mathbb S^1$ built from $\mathsf{loop}^{\pm1}$ and concatenation is a word. `encode` sends it to the composite of $\mathsf{succ}/\mathsf{pred}$ applied to $0$, which is its winding number. Cancellation of $\mathsf{loop}\cdot\mathsf{loop}^{-1}$ is invisible on the output.

```rust
#[derive(Clone, Copy)]
enum Gen { Loop, LoopInv }

/// encode(p) = transport^code(p, 0): fold succ/pred over the word.
fn encode(word: &[Gen]) -> i64 {
    word.iter().fold(0, |n, g| match g {
        Gen::Loop => n + 1,     // transport^code(loop, n)    = n + 1
        Gen::LoopInv => n - 1,  // transport^code(loop^-1, n) = n - 1
    })
}

/// decode(n) = loop^n, in reduced form.
fn decode(n: i64) -> Vec<Gen> {
    let g = if n >= 0 { Gen::Loop } else { Gen::LoopInv };
    std::iter::repeat(g).take(n.unsigned_abs() as usize).collect()
}
// encode(decode(n)) == n holds by construction. The converse, decode(encode(w)) ~ w,
// holds only up to cancellation, which in HoTT is a *path*, not equality of words.
```

The step `fold` is exactly "transport is functorial". The part Rust cannot express is that $\mathsf{decode}(\mathsf{encode}(w))$ and $w$ are *identified* by a path rather than being the same vector.

### 11.2 Reduced words for van Kampen (Python)

The sequences defining $\mathsf{code}$ in §8.7 are words in an amalgamated free product, reduced by the quotient relations. For the free product $G*H$ the normal form is an alternating word:

```python
def reduce_free_product(word):
    """word: list of (side, g) with side in {'B','C'}; g is a group element (here: ints under +)."""
    out = []
    for side, g in word:
        if g == 0:
            continue                      # identity cancels
        if out and out[-1][0] == side:    # adjacent same-factor elements multiply
            s, h = out.pop()
            if h + g != 0:
                out.append((side, h + g))
        else:
            out.append((side, g))
    return out
```

This is the set-quotient of §8.7 in miniature. In the book the relation also lets elements of $\pi_1(A)$ slide across the boundary, which is the amalgamation.

### 11.3 Lean (what is and is not possible)

Lean's `Eq` lives in `Prop` and has definitional proof irrelevance, so UIP holds. This is exactly the situation of Remark 8.1.17: Lean cannot express a nontrivial $\pi_1(\mathbb S^1)$, and it cannot state univalence as an axiom compatible with its kernel. What Lean *can* express is the algebra of §8.4:

```lean
-- Exactness of a sequence of group homomorphisms, as in Theorem 8.4.6.
-- Mathlib: `Function.Exact f g` means `∀ y, g y = 0 ↔ y ∈ Set.range f`.
example {G H K : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup K]
    (f : G →+ H) (g : H →+ K) (hex : Function.Exact f g) (hK : ∀ k : K, k = 0)
    : Function.Surjective f := by
  intro h
  obtain ⟨x, hx⟩ := (hex h).1 (hK _)
  exact ⟨x, hx⟩
```

This is Lemma 8.4.7(ii) in algebraic form: if the next group is trivial, the map is surjective.

## 12. Synthesis: how this fits the book, and what to take from it

**Dependencies.** The chapter uses Chapter 2 (transport, $\mathsf{ap}$, $\mathsf{apd}$, univalence and funext), Chapter 6 (circle, suspension, pushout, join, truncation HITs and the flattening lemma), Chapter 7 (connectedness and truncation) and parts of Chapter 3 (contractibility, mere propositions).

**What depends on it.** The encode-decode method reappears in the Chapter 9–11 constructions, and Chapter 8 is the book's main evidence that the theory computes real mathematics.

```
 univalence ──► ua(succ) : Z = Z ──► code : S¹ → U ──► encode/decode ──► Ω(S¹) ≃ Z
      │                                                                    │
      ▼                                                                    ▼
 fibrations over pushouts ──► Hopf ──► π₂(S²)=Z ──┐            π_n(S¹)=0 (n>1)
                                                  ├──► Freudenthal ──► π_n(Sⁿ)=Z
 connectivity/truncation (Ch. 7) ────────────────┘
 pushouts + truncated paths ──► van Kampen ──► π₁ of CW complexes, any group
```

**Relevance to the compiler/prover goals.** This topic is a mathematical application with no mechanism for the verifier, elaborator, or solver targets, so I do not force a connection to the Focus Areas. Two narrow transferable ideas:

- **Generalise the motive.** The key move in §8.1 (prove the statement for all $x:\mathbb S^1$, not just $\mathsf{base}$) is the same move as choosing a general *motive* in dependent elimination. An elaborator that infers the motive of a `match` or `induction` by abstracting indices faces this problem directly. It is the idea behind "path induction does not apply to loops with both endpoints fixed", and it is related to why elaborators generalise indices before eliminating. (Connects to `type-theory`: $\Pi$-types, definitional vs propositional equality.)
- **Axiom K as a design switch.** Remark 8.1.17 shows that a kernel with UIP (as in Lean's `Prop`) and a kernel that admits univalence are *incompatible* choices, and the circle's fundamental group detects which one you picked. If your dependent type kernel has a proof-irrelevant equality, this chapter's results are unprovable there by design.

Everything else in the chapter (homotopy groups of spheres, Freudenthal, van Kampen) is pure homotopy theory and can be skipped for the stated project without loss.
