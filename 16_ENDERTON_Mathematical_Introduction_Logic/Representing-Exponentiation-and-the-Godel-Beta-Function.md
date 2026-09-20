---
title: Representing Exponentiation and the Gödel β-Function
book: A Mathematical Introduction to Logic (Enderton)
chapter: Chapter Three, Section 3.8 — Representing Exponentiation
pages: 276–281
tags: [logic, undecidability, godel-numbering, pairing-function, chinese-remainder-theorem, beta-function, arithmetization]
---

[[book-guidelines|↩ Back to guidelines]]

## Why this section has to exist

Every earlier result in Chapter 3 about undecidability and incompleteness was proved for the full structure $\mathfrak{N} = (\mathbb{N}; 0, S, <, +, \cdot, E)$ — natural numbers with successor, order, addition, multiplication, *and* exponentiation $E$. Exponentiation was doing real work there: it's what let the axiom set $A_E$ talk about arbitrary finite sequences of numbers as single numbers, which is what [[Arithmetization-of-Syntax|arithmetization of syntax]] needs (a "proof" is a finite sequence of formulas; a formula is a finite sequence of symbols; to Gödel-number any of that you need to pack a sequence into one number and get the pieces back out).

But exponentiation is a strange thing to bake into a theory's primitive vocabulary. It's not decidable on its own reducts, it's not needed to *state* most facts about numbers, and — more to the point for this section — it turns out to be unnecessary as a *primitive*. You can get it for free out of plain old $+$ and $\cdot$, provided you're willing to work for it. That's the entire point of Section 3.8: show that exponentiation is *representable* in $\mathrm{Cn}\,A_M$, where $A_M$ is $A_E$ with the two exponentiation axioms $E_1, E_2$ deleted, and $\mathfrak{N}_M = (\mathbb{N}; 0, S, <, +, \cdot)$ is $\mathfrak{N}$ with $E$ dropped from the language entirely.

If you're a software engineer, "representable in $\mathrm{Cn}\,A_M$" should be read concretely: there is a formula $\varepsilon(x,y,z)$, built using only $+$, $\cdot$, $<$, $S$, $0$ and quantifiers, such that $A_M$ proves $\varepsilon(x,y,z)$ holds exactly when $z = x^y$. No $E$ symbol anywhere. You've implemented `pow` as a *definable predicate* over a base theory that doesn't natively support exponentiation — using the multiplicative structure of $\mathbb{N}$ itself as your "instruction set."

**Why it matters, structurally:** every theorem from Sections 3.3–3.5 (representability of the syntactic apparatus, the Fixed-Point Lemma, Tarski's undefinability theorem, Gödel's incompleteness theorems, strong undecidability) was proved using $A_E$ and $\mathfrak{N}$. Section 3.8's payoff is that all of it transfers, verbatim, to $A_M$ and $\mathfrak{N}_M$ — meaning **multiplication alone (plus $+, <, S, 0$) is already enough to produce a theory that is undecidable and incomplete.** Exponentiation was never the load-bearing ingredient. Multiplication was.

**What breaks without this:** without Section 3.8, you'd be stuck with the impression that Gödel's results are somehow *about* exponential arithmetic specifically — an artifact of a convenient-but-inessential axiom. That would be a much weaker, more fragile-feeling result. This section is what upgrades "undecidability of arithmetic with exponentiation" to "undecidability of arithmetic, full stop, as soon as you have multiplication" — which is the sharper and more surprising fact.

## The obstacle: representing sequences without a primitive for them

Here's the actual engineering problem. Exponentiation satisfies the recursion equations

$$a^0 = 1, \qquad a^{b+1} = a^b \cdot a.$$

A natural first attempt: define a helper function that decodes the sequence of partial powers $a^0, a^1, \dots, a^b$ out of some single encoded number, then take its last element. Enderton calls this $E^*(a,b)$:

$$E^*(a,b) = \text{the least } s \text{ such that } (s)_0 = 1 \text{ and for all } i < b,\ (s)_{i+1} = (s)_i \cdot a,$$

where $(s)_i$ is "the $i$-th element of the sequence encoded by $s$" — the decomposition function used earlier in the chapter (built from the exponential-based encoding of Section 3.4). Then $a^b = (E^*(a,b))_b$.

The catch: that particular decomposition function $(s)_i$ was itself built using exponentiation. You can't use it here — you'd be assuming the very thing you're trying to prove representable. Circular.

**The fix is a change of perspective.** You don't actually need *that specific* sequence-decoding scheme. You need *some* function $\delta(s, i)$ that behaves like a decomposition function — i.e., for any finite list of numbers $a_0, \dots, a_n$, there's some code $s$ such that $\delta(s, i) = a_i$ for every $i \le n$ — and, crucially, that $\delta$ itself is representable using only $+$ and $\cdot$. This is stated as:

> **Lemma 38A.** There is a function $\delta$ representable in $\mathrm{Cn}\,A_M$ such that for every $n, a_0, \dots, a_n$, there is an $s$ for which $\delta(s,i) = a_i$ for all $i \le n$.

Once you have that, the same recursive trick works cleanly:

$$E^{**}(a,b) = \text{the least } s \text{ such that } \delta(s,0)=1 \text{ and for all } i<b,\ \delta(s,i+1)=\delta(s,i)\cdot a,$$

and then $a^b = \delta(E^{**}(a,b), b)$ — all expressible via $+,\cdot$, minimization, and composition, all of which the earlier "catalog of representable functions" (Section 3.3) already establishes stay representable under those operations. So the entire remaining burden of the section is: **construct $\delta$**. Everything else — building `pow` out of `mul` and a decode primitive — is straightforward once you have a working "decode."

If you've ever implemented a `Vec<u64>` as a packed `u64` (a small fixed-capacity bitfield, or a base-$k$ positional encoding) and then needed an `unpack(code, index) -> u64` accessor, you've built exactly this shape of thing already. The novelty here is doing it with *unbounded* length and with only $+$/$\cdot$ as your instruction set — no shifts, no explicit "array of digits," nothing but arithmetic and first-order quantifiers.

**What breaks without a $\delta$ like this:** without a way to pack an arbitrary-length finite sequence into a single number and pull elements back out definably, you cannot state "$d$ is a deduction from axioms $\Gamma$" as an arithmetic formula at all — a deduction *is* a finite sequence of formula-numbers satisfying a local well-formedness condition at each step. No sequence coding, no arithmetization of "is a proof," no Gödel numbering of deductions, no incompleteness theorem. Section 3.4's arithmetization of syntax leaned on exponentiation being available as a primitive to build its decomposition function; Section 3.8 is what makes that layer honest, by showing you never needed exponentiation as a primitive to begin with.

## Building block 1: a pairing function

Before tackling sequences of arbitrary length, warm up with sequences of length 2 — ordered pairs. The goal: a bijection $J : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$, together with two "inverse" projections $K, L$ such that $K(J(a,b)) = a$ and $L(J(a,b)) = b$. This is the **pairing function**, and Enderton's is the classic diagonal enumeration — walk the anti-diagonals $x + y = 0, 1, 2, \dots$ of the plane, and number the lattice points in the order you visit them:

$$J(a,b) = \tfrac{1}{2}(a+b)(a+b+1) + a = \tfrac{1}{2}\big[(a+b)^2 + 3a + b\big].$$

For example $J(2,1) = 8$ and $J(0,2) = 3$.

<svg viewBox="0 0 460 300" xmlns="http://www.w3.org/2000/svg" font-family="monospace" font-size="13">
  <style>
    .grid { stroke: #888; stroke-width: 1; }
    .diag { stroke: #6699cc; stroke-width: 1.4; }
    .pt { fill: #cc6644; }
    .lbl { fill: #444; }
    .axislbl { fill: #444; font-weight: bold; }
  </style>
  <!-- axes -->
  <line x1="40" y1="260" x2="440" y2="260" stroke="#666" stroke-width="1.5"/>
  <line x1="40" y1="260" x2="40" y2="20" stroke="#666" stroke-width="1.5"/>
  <text x="440" y="278" class="axislbl">x</text>
  <text x="18" y="20" class="axislbl">y</text>
  <!-- diagonals x+y=n for n=0..4 -->
  <line x1="40" y1="260" x2="40" y2="260" class="diag"/>
  <line x1="90" y1="260" x2="40" y2="210" class="diag"/>
  <line x1="140" y1="260" x2="40" y2="160" class="diag"/>
  <line x1="190" y1="260" x2="40" y2="110" class="diag"/>
  <line x1="240" y1="260" x2="40" y2="60" class="diag"/>
  <!-- lattice points with J-values: (x,y) -> screen (40+50x, 260-50y) -->
  <!-- n=0: (0,0)=0 -->
  <circle cx="40" cy="260" r="4" class="pt"/><text x="46" y="256" class="lbl">0: (0,0)</text>
  <!-- n=1: (0,1)=1, (1,0)=2 -->
  <circle cx="40" cy="210" r="4" class="pt"/><text x="46" y="206" class="lbl">1: (0,1)</text>
  <circle cx="90" cy="260" r="4" class="pt"/><text x="96" y="256" class="lbl">2: (1,0)</text>
  <!-- n=2: (0,2)=3, (1,1)=4, (2,0)=5 -->
  <circle cx="40" cy="160" r="4" class="pt"/><text x="46" y="156" class="lbl">3: (0,2)</text>
  <circle cx="90" cy="210" r="4" class="pt"/><text x="96" y="206" class="lbl">4: (1,1)</text>
  <circle cx="140" cy="260" r="4" class="pt"/><text x="146" y="256" class="lbl">5: (2,0)</text>
  <!-- n=3: (0,3)=6,(1,2)=7,(2,1)=8,(3,0)=9 -->
  <circle cx="40" cy="110" r="4" class="pt"/><text x="46" y="106" class="lbl">6: (0,3)</text>
  <circle cx="90" cy="160" r="4" class="pt"/><text x="96" y="156" class="lbl">7: (1,2)</text>
  <circle cx="140" cy="210" r="4" class="pt"/><text x="146" y="206" class="lbl">8: (2,1)</text>
  <circle cx="190" cy="260" r="4" class="pt"/><text x="196" y="256" class="lbl">9: (3,0)</text>
  <text x="250" y="150" class="lbl" font-size="12">J(a,b) walks each</text>
  <text x="250" y="168" class="lbl" font-size="12">anti-diagonal x+y=n</text>
  <text x="250" y="186" class="lbl" font-size="12">in order; J(2,1)=8</text>
</svg>

The formula translates directly to a closed-form arithmetic expression using a helper "half" function $H(a)$ = the least $b$ such that $a \le 2b$ (so $H(a) = a/2$ for even $a$):

$$J(a,b) = H\big((a+b)(a+b+1)\big) + a,$$
$$K(p) = \text{the least } a \text{ such that for some } b \le p,\ J(a,b) = p,$$
$$L(p) = \text{the least } b \text{ such that for some } a \le p,\ J(a,b) = p.$$

Every one of these is built from $+, \cdot$, bounded quantification (the "$\le p$" bound is what keeps the minimization finite and hence representable), and least-number-search — all operations the Section 3.3 catalog already knows are representable. So $H, J, K, L$ are all representable in $\mathrm{Cn}\,A_M$.

**Grounding (Rust).** This is precisely the "encode two `u32`s into one `u64`, decode losslessly" problem — the Cantor pairing function is a standard, if slightly obscure, corner of interview-question folklore. Here it is directly transliterated:

```rust
fn j(a: u64, b: u64) -> u64 {
    let s = a + b;
    s * (s + 1) / 2 + a
}

fn k_and_l(p: u64) -> (u64, u64) {
    // invert by walking back to the triangular number just below p
    let mut s: u64 = 0;
    while (s + 1) * (s + 2) / 2 <= p {
        s += 1;
    }
    let a = p - s * (s + 1) / 2;
    let b = s - a;
    (a, b)
}

fn main() {
    assert_eq!(j(2, 1), 8);
    assert_eq!(k_and_l(8), (2, 1));
    assert_eq!(j(0, 2), 3);
    assert_eq!(k_and_l(3), (0, 2));
}
```

The book's $K$ and $L$ are defined by *unbounded-but-provably-bounded search* ("the least $a$ such that for some $b \le p$...") rather than by the closed-form inverse used above — that's deliberate: representability theory needs the definitions to be first-order formulas built from bounded quantifiers and least-number operators, not "solve a quadratic," even though *semantically* they compute the same inverse. The Rust code computes the same function by a more direct route; the book's route is the one that survives translation into a formula $\varepsilon(x,y,z)$ in the language of $\mathfrak{N}_M$.

**What breaks without a pairing function:** without $J, K, L$, a theory that can talk about pairs of numbers can still be built, but it has to do so relationally rather than functionally — you'd need first-order machinery baked directly into [[Weak-Fragments-of-Number-Theory#The axioms|the axioms]] for "is a pair" rather than being able to *compute* one number that packages two others. Pairing is the base case; the $\beta$-function below is what generalizes it to sequences of *any* length, not just 2.

## Building block 2: the Chinese Remainder Theorem as the actual engine

Pairing handles two numbers. Lemma 38A needs to handle $n+1$ numbers for *arbitrary* $n$ — the real "encode a `Vec<u64>` into a single integer" problem. The mechanism that makes this possible is a genuinely old and beautiful piece of number theory, not something invented for logic: the **Chinese Remainder Theorem** (CRT).

**The idea in words, before the formula:** if you pick a bunch of moduli $d_0, \dots, d_n$ that share no common prime factors pairwise ("relatively prime in pairs"), then any pattern of remainders $a_0 < d_0, \; a_1 < d_1, \; \dots, \; a_n < d_n$ you might want is achievable by *some* single number $c$, and moreover $c$ is uniquely determined modulo the product $\prod_i d_i$. In other words: the map "reduce $c$ modulo each $d_i$" is a bijection from $\{0, 1, \dots, \prod d_i - 1\}$ onto the space of all possible remainder-tuples. That's your encoding scheme. To encode a sequence $(a_0, \dots, a_n)$: find such a $c$. To decode element $i$: just compute $c \bmod d_i$.

> **Chinese Remainder Theorem.** Let $d_0, \dots, d_n$ be relatively prime in pairs; let $a_0, \dots, a_n$ be natural numbers with each $a_i < d_i$. Then there is a number $c$ such that for all $i \le n$, $a_i$ is the remainder of $c$ divided by $d_i$.

The proof is a clean counting argument: let $p = \prod_{i \le n} d_i$. Define $F(c)$ to be the $(n{+}1)$-tuple of remainders of $c$ modulo each $d_i$. There are exactly $p$ possible values of this tuple (each $a_i$ ranges over $d_i$ choices). $F$ restricted to $\{0, \dots, p-1\}$ is injective: if $F(c_1) = F(c_2)$ then every $d_i$ divides $|c_1 - c_2|$, and since the $d_i$'s are pairwise coprime, their product $p$ divides $|c_1-c_2|$ too — but for $c_1, c_2 < p$ that forces $c_1 = c_2$. An injective map from a $p$-element set to a $p$-element set is a bijection, so every remainder-tuple — including $(a_0,\dots,a_n)$ — is hit by some $c$.

**Why "relatively prime in pairs" is the crux, and how to get moduli like that on demand.** The whole thing hinges on having, for any $n$, a supply of $n+1$ pairwise-coprime moduli, chosen *after* you already know how big $n$ and the $a_i$'s are. Enderton's move:

> **Lemma 38B.** For any $s \ge 0$, the $s+1$ numbers $1 + 1\cdot s!,\ 1 + 2\cdot s!,\ \dots,\ 1 + (s+1)\cdot s!$ are relatively prime in pairs.

Why: any prime $q$ dividing one of these numbers $1 + j\cdot s!$ cannot itself divide $s!$ (since $1 + j \cdot s! \equiv 1 \pmod q$ would fail otherwise), so $q > s$. If some prime $q$ divided both $1 + j\cdot s!$ and $1 + k\cdot s!$, it would divide their difference $|j-k|\cdot s!$; since $q \nmid s!$, it must divide $|j-k|$. But $|j-k| \le s < q$, forcing $|j-k|=0$. So no two of these numbers share a prime factor.

Putting it together (the proof of $(*)$, the existence claim underlying Lemma 38A): given $a_0, \dots, a_n$, let $s$ be the max of $\{n, a_0, \dots, a_n\}$ and set $d = s!$. By Lemma 38B the numbers $1 + (i+1)d$ for $i \le n$ are pairwise coprime, and each exceeds $s \ge a_i$, so the CRT applies and hands you a $c$ with remainder $a_i$ modulo $1+(i+1)d$ for every $i \le n$.

**Grounding (Rust) — the factorial-modulus CRT trick as actual code:**

```rust
/// Encode an arbitrary-length slice of u64s into a single (c, d) pair,
/// mirroring Enderton's construction: d = s!, moduli m_i = 1 + (i+1)*d.
fn encode(a: &[u64]) -> (u128, u128) {
    let s = a.iter().copied().max().unwrap_or(0).max(a.len() as u64);
    let d = factorial(s);
    let moduli: Vec<u128> = (0..a.len())
        .map(|i| 1 + (i as u128 + 1) * d as u128)
        .collect();
    let c = crt_solve(a, &moduli); // standard pairwise-CRT solve
    (c, d as u128)
}

/// Decode element i back out: this *is* Gödel's beta function.
fn beta(c: u128, d: u128, i: u128) -> u128 {
    let modulus = 1 + (i + 1) * d;
    c % modulus
}

fn factorial(n: u64) -> u64 {
    (1..=n.max(1)).product()
}
```

(`crt_solve` is the standard incremental CRT combine, folding moduli in pairwise via the extended Euclidean algorithm — mechanically identical to the existence proof above, just made computational instead of existential.)

**What breaks without CRT:** without a way to manufacture *arbitrarily many* pairwise-coprime moduli on demand, you're stuck: a fixed pairing function only ever handles a fixed arity. You could nest pairs ($J(a, J(b, J(c, \dots)))$) to encode a length-$n$ tuple for *fixed* $n$, and in fact this works fine for a *known, bounded* arity — but a *deduction* (Gödel-numbered proof) has unboundedly many steps, and its length isn't known in advance when you're writing the representing formula. You need one uniform decoding scheme $\delta(s,i)$ that works for sequences of *any* length $n$, with no arity baked into the formula itself. CRT is what supplies that uniformity — pick the modulus set based on the data, not on a fixed schema.

## Building block 3: the Gödel β-function

Now assemble the pieces into the actual decomposition function $\delta$ Lemma 38A promises. Define:

$$\beta(c,d,i) = \text{the remainder of } c \div \big[1 + (i+1)\cdot d\big] = \text{the least } r \text{ such that for some } q \le c,\ c = q\cdot[1+(i+1)d] + r.$$

This is the **Gödel β-function**. It looks unmotivated on first read — "the remainder of $c$ modulo a weirdly-shaped linear function of $i$ and $d$" — but by [[Godels-Incompleteness-Theorems#The construction|the construction]] above, it is *exactly* "decode index $i$ out of the CRT-packed code $(c,d)$." Then set

$$\delta(s,i) = \beta(K(s), L(s), i)$$

— i.e., use the pairing-function projections $K, L$ to unpack a *single* number $s$ into the $(c,d)$ pair $\beta$ needs, so that $\delta$ takes one argument for "the sequence" (just like $(s)_i$ in the exponential encoding) rather than two. By the $(*)$ argument above, for any finite list $a_0,\dots,a_n$ there exist $c,d$ with $\beta(c,d,i)=a_i$ for $i\le n$; taking $s = J(c,d)$ gives $\delta(J(c,d), i) = \beta(c,d,i) = a_i$. That's Lemma 38A, fully discharged — and every ingredient ($K$, $L$, remainder-of-division, bounded search) is representable in $\mathrm{Cn}\,A_M$ using only $+, \cdot$, so $\delta$ is too.

<svg viewBox="0 0 600 260" xmlns="http://www.w3.org/2000/svg" font-family="monospace" font-size="13">
  <style>
    .box { fill: none; stroke: #6699cc; stroke-width: 1.6; }
    .arrow { stroke: #888; stroke-width: 1.6; marker-end: url(#arrowhead); fill: none; }
    .lbl { fill: #444; }
    .hdr { fill: #cc6644; font-weight: bold; }
  </style>
  <defs>
    <marker id="arrowhead" markerWidth="8" markerHeight="8" refX="6" refY="3" orient="auto">
      <path d="M0,0 L6,3 L0,6 Z" fill="#888"/>
    </marker>
  </defs>
  <text x="20" y="24" class="hdr">encode(a0..an):</text>
  <rect x="20" y="36" width="220" height="46" class="box"/>
  <text x="30" y="56" class="lbl">choose s = max(n, a_i)</text>
  <text x="30" y="74" class="lbl">d = s!  (Lemma 38B moduli)</text>
  <path d="M240,59 H300" class="arrow"/>
  <rect x="300" y="36" width="220" height="46" class="box"/>
  <text x="310" y="56" class="lbl">CRT solve: find c with</text>
  <text x="310" y="74" class="lbl">c mod (1+(i+1)d) = a_i</text>
  <path d="M410,82 V120" class="arrow"/>
  <rect x="300" y="120" width="220" height="40" class="box"/>
  <text x="310" y="145" class="lbl">s' = J(c, d)   [pairing]</text>
  <text x="270" y="185" class="hdr">this s' is the "packed Vec&lt;u64&gt;"</text>

  <text x="20" y="220" class="hdr">decode(s', i):</text>
  <rect x="20" y="230" width="560" height="0" class="box" stroke="none"/>
  <text x="150" y="220" class="lbl">δ(s', i) = β(K(s'), L(s'), i) = remainder of c ÷ [1+(i+1)d]  =  a_i</text>
</svg>

**Grounding (Python — a short runnable sketch).** The mechanism is short enough to make fully concrete:

```python
from math import factorial

def crt_pair(remainders, moduli):
    # incremental pairwise CRT combine
    c, m = 0, 1
    for r, mi in zip(remainders, moduli):
        # solve x ≡ c (mod m), x ≡ r (mod mi)
        g = pow(m, -1, mi)
        c = (c + m * ((r - c) * g % mi)) % (m * mi)
        m *= mi
    return c

def encode_sequence(a):
    n = len(a) - 1
    s = max([n] + a)
    d = factorial(s)
    moduli = [1 + (i + 1) * d for i in range(len(a))]
    c = crt_pair(a, moduli)
    return c, d

def beta(c, d, i):
    return c % (1 + (i + 1) * d)

seq = [5, 12, 0, 7, 3]
c, d = encode_sequence(seq)
decoded = [beta(c, d, i) for i in range(len(seq))]
assert decoded == seq
```

Run this mentally (or literally) and it demonstrates the entire content of Lemma 38A: pick a factorial-sized modulus, CRT-combine, and $\beta$ is a plain "mod" that recovers each element. There is no bound on `len(seq)` baked into the code — a $(c,d)$ pair of just two numbers decodes a sequence of *any* length.

With $\delta$ in hand, exponentiation follows exactly as sketched at the start: define $E^{**}(a,b)$ as the least $s$ such that $\delta(s,0)=1$ and $\delta(s,i+1)=\delta(s,i)\cdot a$ for all $i<b$ (this exists by Lemma 38A, applied to the sequence $a^0, a^1, \dots, a^b$), and then

$$a^b = \delta(E^{**}(a,b), b).$$

Every function used — $\delta$, minimization bounded by the recursion, multiplication — is representable in $\mathrm{Cn}\,A_M$, so:

> **Theorem 38C.** Exponentiation is representable in $\mathrm{Cn}\,A_M$.

That is, there's a formula $\varepsilon(x,y,z)$ in the pure language of $\mathfrak{N}_M$ (only $0, S, <, +, \cdot$) such that

$$A_M \vdash \forall z\big[\varepsilon(S^a0, S^b0, z) \leftrightarrow z = S^{(a^b)}0\big].$$

**What breaks without the β-function specifically (as opposed to some other sequence code):** you could in principle try to build a decomposition function directly from the pairing function alone, by nesting: $s$ encodes $(a_0, J(a_1, J(a_2, \dots)))$. That works for representability *in principle*, but decoding element $i$ then requires $i$ applications of $L$ and $K$ — the formula for "$\delta(s,i) = a_i$" would need a bound tied to $i$ baked awkwardly into a bounded-quantifier chain of varying depth, which is exactly the kind of "arity known in advance" fragility CRT was brought in to avoid. The β-function's trick is that decoding *any* index $i$ from a *fixed-size* code $(c,d)$ is a single, uniform, one-step "take the remainder" operation — the depth of the formula $\beta(c,d,i)=r$ doesn't grow with $i$. That uniformity is precisely what a first-order representability proof needs, since the formula $\varepsilon(x,y,z)$ has to be one fixed formula, not a formula schema that grows with the exponent $b$.

## The payoff: strong undecidability with multiplication alone

Once exponentiation is representable in $\mathrm{Cn}\,A_M$, everything downstream falls into place by re-running the *same proofs* from Sections 3.3–3.5 with "$A_E$" and "$\mathfrak{N}$" replaced by "$A_M$" and "$\mathfrak{N}_M$":

- Every relation and function shown representable in $\mathrm{Cn}\,A_E$ via the Section 3.3 catalog (composition, primitive recursion, minimization, and now exponentiation itself) is representable in $\mathrm{Cn}\,A_M$ by the identical proofs.
- The arithmetization of syntax from Section 3.4 (Gödel numbering of terms, wffs, deductions) goes through unchanged, since it was built entirely from catalog-representable functions.
- The Fixed-Point Lemma, Tarski's Undefinability Theorem, and Gödel's First Incompleteness Theorem from Section 3.5 all transfer.
- **Strong undecidability of $\mathrm{Cn}\,A_M$:** any theory $T$ in the language of $\mathfrak{N}_M$ such that $T \cup A_M$ is consistent cannot be recursive (decidable).

The last point is the sharpest form of the result. It says: you cannot patch your way out of undecidability by adding more true axioms about $+$ and $\cdot$ — the "infection" of undecidability is structural, tied to having multiplication (plus successor, order, addition) at all, not to some deficiency of the particular axiom set chosen.

One more consequence worth flagging, connecting back to Section 2.7's interpretability machinery: since exponentiation is definable in $\mathfrak{N}_M$ (representability implies definability), and every relation definable in $\mathfrak{N}$ was already stated using $E$, it follows that every arithmetical relation (definable in the full $\mathfrak{N}$) is *also* definable in $\mathfrak{N}_M$ — just via a longer formula that expands each use of $E$ into $\varepsilon$. There is a **faithful interpretation** of $\mathrm{Th}\,\mathfrak{N}$ into $\mathrm{Th}\,\mathfrak{N}_M$: the identity on every parameter except $E$, and on $E$ the formula $\varepsilon$ defining exponentiation. And by the Tarski-style undefinability argument (Section 3.0/3.5, now transferred), $\sharp\,\mathrm{Th}\,\mathfrak{N}_M$ is not definable in $\mathfrak{N}_M$ — hence not arithmetical.

## Table X — the full landscape of reducts

Enderton closes the chapter with a summary table comparing every reduct of $\mathfrak{N}$ studied across Chapter 3, reproduced here (from the book's Table X, p. 280):

| Structure | Theory | Models of the theory | Definable sets | Comments |
|---|---|---|---|---|
| $(\mathbb{N})$ | Decidable. Not finitely axiomatizable. Admits [[Models-of-Theories#Elimination of quantifiers|elimination of quantifiers]]. | Any infinite set. | $\emptyset$ and $\mathbb{N}$. $\{0\}$ is not definable. | |
| $(\mathbb{N}; 0)$ | As above. | Any infinite set with distinguished element. | $\emptyset, \{0\}, \mathbb{N}-\{0\}, \mathbb{N}$. $S$ is not definable. | |
| $(\mathbb{N}; 0, S)$ | As above. | Standard part plus any number of $Z$-chains. | Finite and cofinite sets. $<$ is not definable. | $\{0\}$ is definable in $(\mathbb{N}; S)$. |
| $(\mathbb{N}; 0, S, <)$ | Decidable. Finitely axiomatizable. Admits elimination of quantifiers. | As above, with any ordering of the $Z$-chains. | Finite and cofinite sets. $+$ is not definable. | $\{0\}$ and $S$ are definable in $(\mathbb{N}; <)$. |
| $(\mathbb{N}; 0, S, <, +)$ | Decidable (Presburger). | The $Z$-chains are densely ordered without endpoints. Also there is a suitable addition operation. | Eventually periodic sets. $\cdot$ is not definable. | $\{0\}$, $S$, and $<$ are definable in $(\mathbb{N}; +)$. |
| $(\mathbb{N}; 0, S, <, +, \cdot)$ | Not arithmetical. $\therefore$ not recursively axiomatizable. | As above, but with a suitable multiplication operation. | All arithmetical relations are definable. | The arithmetical relations are definable in $(\mathbb{N}; S, \cdot)$, $(\mathbb{N}; +, \cdot)$, and $(\mathbb{N}; <, D)$, where $D(x,y) = (x)_y$. |

The bottom row is exactly Section 3.8's result: once you have $+$ and $\cdot$ together, the theory stops being "arithmetical" (definable within $\mathfrak{N}$ itself) altogether — full undecidability and, via Tarski, undefinability of truth. Everything above that row is comparatively tame and *decidable*: successor alone, successor with order, even successor-order-addition (Presburger arithmetic) all admit elimination of quantifiers and decision procedures. Multiplication is the single ingredient that tips the structure over into genuine undecidability — and Section 3.8's whole argument is the proof that multiplication suffices *on its own*, without needing exponentiation as backup.

## Where this leads

This section is the last technical piece of Chapter 3: it retroactively tightens every incompleteness and undecidability result proved earlier in the chapter, replacing "assuming you have exponentiation" with "multiplication alone is already enough" — which is both a stronger theorem and a more honest account of *why* arithmetic is undecidable (it's about coding arbitrary-length data as numbers, not about any specific arithmetic operation being present). After this, the book turns to Chapter 4 and Second-Order Logic, leaving number theory behind.

For the learning-goals threads this vault is tracking: this is as concrete an instance as you'll find of "represent structured, variable-length data as a single encodable value using only a small fixed instruction set" — exactly the kind of term-encoding or content-addressing scheme a Rust verifier's proof-term representation, hash-consing table, or de Bruijn-indexed context packing would need. The β-function's design principle — pick a modulus that depends on the data, encode via CRT, decode via one fixed-shape formula independent of sequence length — is a genuinely reusable trick anywhere you need a *uniform*, arity-independent way to pack and unpack variable-length structure into fixed-width values (a proof object's list of premises, a substitution's list of bindings, a term's list of subterms) without hard-coding an arity bound into your representation.
