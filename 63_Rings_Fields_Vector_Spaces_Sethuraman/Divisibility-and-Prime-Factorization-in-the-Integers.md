---
title: Divisibility and Prime Factorization in the Integers
source: "Rings, Fields, and Vector Spaces — B. A. Sethuraman"
chapter: "Chapter 1, pp. 9–28"
tags: [number-theory, integers, gcd, primes, well-ordering, induction]
---

[[book-guidelines|↩ Back to guidelines]]

# Divisibility and Prime Factorization in the Integers

## Why start here at all?

The book's whole arc is a proof that you can't trisect an angle with a straightedge and compass — a purely geometric-sounding claim that ends up resting on algebra. But the *first* piece of algebra it needs isn't fields or [[Vector-Spaces|vector spaces]]; it's the most familiar number system there is, $\mathbb{Z}$, examined closely enough to notice that it has a structural property most people take completely for granted: **every integer greater than 1 breaks down into primes in exactly one way.**

That "exactly one way" is not automatic. It fails in number systems that look superficially like $\mathbb{Z}$ — Sethuraman flags this early and asks you to hold the thought until Chapter 2, where you'll meet a commutative ring in which unique factorization genuinely breaks. If uniqueness of factorization isn't a free lunch, then something has to *earn* it for $\mathbb{Z}$. This chapter is the earning.

That "something" turns out to be a single foundational fact, taken as an axiom, from which everything else — the division algorithm, gcd, primes, unique factorization, and the infinitude of primes — is derived in a tight logical chain.

## The one axiom everything rests on

**Well Ordering Principle:** every nonempty subset of the nonnegative integers has a least element.

This sounds almost too obvious to state. But contrast it with $\mathbb{Q}^{+}$: the set of positive rationals has *no* least element (given any positive rational, you can always halve it and stay positive). So "having a least element" is not a property of "being a set of positive numbers" in general — it's specific to how the integers are built. Sethuraman takes it as a primitive axiom rather than deriving it from something more basic, and everything else in the chapter is downstream of it.

**What breaks without it:** without a guaranteed least element, there's no way to argue "stop the process here, at the smallest witness" — which is exactly the move used to construct the remainder in the division algorithm and to construct the gcd as a *minimal* positive linear combination. Both proofs below are, structurally, "consider a certain nonempty set of nonnegative integers, invoke Well Ordering, take its least element, and show that least element has the properties you wanted."

If you've done any work with well-founded recursion or structural induction over `Nat` in a proof assistant, this should already feel familiar — it's the same load-bearing beam.

```python
# The intuition, made executable: WOP is what guarantees this terminates.
def least_element(S: set[int]) -> int:
    assert all(x >= 0 for x in S) and S
    return min(S)  # exists because S ⊆ ℕ is nonempty — this is WOP, not an algorithm
```

## Divisibility, formally

**Definition 1.1.** A nonzero integer $d$ *divides* $a$ (written $d \mid a$) if there exists an integer $b$ with $a = db$. Then $d$ is a *divisor* or *factor* of $a$, and $a$ is a *multiple* of $d$.

Note the definition is symmetric in sign — negative divisors are allowed ($-2 \mid 6$, since $-2 \cdot -3 = 6$) — the book just conventionally restricts attention to positive divisors when convenient.

A small but structurally important lemma sets the pattern for everything downstream:

**Lemma 1.2.** If $d \mid a$ and $d \mid b$, then for any integers $x, y$: $d \mid (xa + yb)$.

*Proof idea:* $a = dm$, $b = dn$, so $xa + yb = d(xm + yn)$ — divisibility is closed under arbitrary integer linear combinations, not just sums. This single fact is what makes gcd expressible as a linear combination at all (see below), and it reappears **verbatim**, with an identical proof, for polynomials in Chapter 5 (Lemma 5.8) — same statement, same argument, different ring. That's the book's running theme made concrete: the *proof technique* generalizes even when the objects don't.

```rust
// The divisibility relation as a predicate — trivial to state, load-bearing to reason about
fn divides(d: i64, a: i64) -> bool {
    d != 0 && a % d == 0
}

// Lemma 1.2 in code: closure under linear combinations
fn linear_combination_divisible(d: i64, a: i64, b: i64, x: i64, y: i64) -> bool {
    // Given: divides(d, a) && divides(d, b)
    // Claim: divides(d, x*a + y*b) always holds
    divides(d, x * a + y * b)
}
```

## The Division Algorithm: existence *and* uniqueness, both from Well Ordering

**Lemma 1.3 (Division Algorithm).** Given integers $a, b$ with $b > 0$, there exist *unique* integers $q, r$ with $0 \le r < b$ such that $a = bq + r$.

The proof is a clean two-step application of Well Ordering:

1. **Existence.** Consider $S = \{a - bn \mid n \in \mathbb{Z}\}$, and let $S^* \subseteq S$ be the nonnegative elements. $S^*$ is nonempty (if $a \ge 0$, $a \in S^*$; if $a<0$, then $a - b(a) \ge 0$ since $b \geq 1$). By Well Ordering, $S^*$ has a least element $r$, and since $r \in S$, $r = a - bq$ for some $q$ — giving $a = bq + r$. A short contradiction argument (if $r \ge b$, then $r - b$ would be a *smaller* nonnegative element of $S^*$) forces $0 \le r < b$.
2. **Uniqueness.** Two representations $a = bq_1 + r_1 = bq_2 + r_2$ force $b(q_1 - q_2) = r_2 - r_1$, and since $|r_2 - r_1| < b$, the only multiple of $b$ in that range is $0$ — so $r_1 = r_2$ and hence $q_1 = q_2$.

**What breaks without uniqueness:** the entire idea of "the" remainder — used constantly downstream (e.g., "$d \mid a$ iff the remainder of $a$ divided by $d$ is zero") — would be ill-defined; you'd need to track *which* quotient/remainder pair you meant every time.

```rust
/// Division Algorithm as a typestate-verified pair: the invariant 0 <= r < b
/// is baked into the type by construction, not checked after the fact.
struct DivisionResult { q: i64, r: i64 }

fn divide(a: i64, b: i64) -> DivisionResult {
    assert!(b > 0);
    let q = a.div_euclid(b);
    let r = a.rem_euclid(b);
    debug_assert!(0 <= r && r < b);
    DivisionResult { q, r }
}
```

```lean
-- Lean's kernel already has this as a theorem about Nat/Int, but stating it
-- explicitly mirrors Lemma 1.3 exactly:
theorem division_algorithm (a : ℤ) (b : ℤ) (hb : b > 0) :
    ∃! (qr : ℤ × ℤ), a = b * qr.1 + qr.2 ∧ 0 ≤ qr.2 ∧ qr.2 < b := by
  sorry -- existence via Int.ediv/Int.emod, uniqueness by the argument above
```

The Lean version is worth pausing on: `∃!` (unique existence) is doing exactly what Sethuraman's Remark 1.4 spends a paragraph emphasizing in prose — that this isn't just "a $q,r$ exist" but "there is exactly one such pair." In a proof assistant, that distinction is forced into the type of the statement; in the textbook, it has to be argued for separately. This is a good early example of how formalization makes explicit what informal math states as an aside.

## GCD, reformulated as a minimal linear combination

The book first defines $\gcd(a,b)$ the obvious way — the largest common divisor (Definition 1.5), which makes sense because common divisors are bounded (any common divisor of $a,b$ lies between $-\min(|a|,|b|)$ and $\min(|a|,|b|)$, so there are finitely many).

But then it proves something much less obvious:

**Theorem 1.6.** Let $P = \{xa + yb \mid x,y \in \mathbb{Z},\ xa+yb > 0\}$. Let $d$ be the *least* element of $P$ (exists by Well Ordering, since $P \ne \varnothing$). Then $d = \gcd(a,b)$, and **every** element of $P$ is divisible by $d$.

*Proof sketch:* $d = xa+yb$ for some $x,y$ by construction. To see $d \mid a$: write $a = dq+r$ (division algorithm) and suppose $r > 0$. Substituting $d = xa+yb$ gives $r = (1-xq)a + (-yq)b$ — i.e. $r$ is *also* a positive linear combination of $a,b$, but $r < d$, contradicting minimality of $d$. So $r = 0$, i.e. $d \mid a$; symmetric for $b$. Then for any common divisor $c$ of $a,b$: since $d = xa+yb$, Lemma 1.2 gives $c \mid d$, so $c \le d$. Hence $d$ is not just *a* common divisor, it's the largest one — matching Definition 1.5.

This is the **Bézout identity** in disguise, proved constructively via Well Ordering rather than assumed. The notes explicitly flag the pitfall: knowing $xa+yb=2$ for *some* $x,y$ does **not** let you conclude $\gcd(a,b)=2$ — you need $d$ to be the *least* positive linear combination, not just *a* witness of some value. (You *can* conclude $\gcd(a,b)=1$ from $xa+yb=1$, though — since $1$ is automatically the smallest positive integer, minimality is free at that specific value.)

**Corollary 1.7** falls out immediately: *every* common divisor of $a,b$ divides $\gcd(a,b)$ — not just is smaller than it. This stronger, more structural characterization (rather than "largest") is the one that generalizes to [[Rings|rings]] without a natural ordering — Sethuraman explicitly notes this is exactly how gcd gets redefined for polynomials in Chapter 5, where "largest" is meaningless but "every common divisor divides it" still makes sense.

```rust
/// Extended Euclidean algorithm: computes gcd(a,b) AND witnesses x,y with
/// x*a + y*b = gcd(a,b) — i.e. it constructively exhibits Theorem 1.6's `d`.
fn extended_gcd(a: i64, b: i64) -> (i64, i64, i64) {
    // returns (gcd, x, y) such that x*a + y*b == gcd
    if b == 0 {
        return (a, 1, 0);
    }
    let (g, x1, y1) = extended_gcd(b, a % b);
    (g, y1, x1 - (a / b) * y1)
}
```

This isn't a loose analogy — `extended_gcd` *is* an algorithmic witness for Theorem 1.6: it doesn't just compute the largest common divisor, it hands back the exact $x,y$ making $d = xa+yb$ the minimal positive linear combination. The recursive step relies on the same fact proved in Exercise 2 of the chapter: $\gcd(a,b) = \gcd(b,r)$ where $a = bq+r$ — this identity is literally what makes the Euclidean algorithm terminate and is the reason the "Euclidean algorithm" is named after Euclid rather than Sethuraman's Theorem 1.6, even though 1.6 is what *proves* the linear-combination form works.

## Relatively prime, and the workhorse lemma

**Definition 1.8.** $a, b$ are *relatively prime* if $\gcd(a,b) = 1$.

**Corollary 1.9** (immediate from 1.6): $\gcd(a,b)=1$ iff $xa+yb=1$ for some integers $x,y$.

**Lemma 1.10.** If $a \mid bc$ and $\gcd(a,b)=1$, then $a \mid c$.

*Proof:* from $1 = xa+yb$, multiply by $c$: $c = xac + ybc$. Since $a \mid a$ (trivially) and $a \mid bc$ (given), Lemma 1.2 gives $a \mid (xac+ybc) = c$. $\blacksquare$

This lemma is the hinge the rest of the chapter swings on — it's what makes the "prime divides a product implies prime divides a factor" step work, which is in turn what makes unique factorization provable.

## Primes and the Fundamental Theorem of Arithmetic

**Definition 1.11.** $p > 1$ is *prime* if its only divisors are $\pm 1, \pm p$. A non-prime integer $>1$ is *composite*.

Two supporting lemmas, both direct consequences of the machinery above:

- **Lemma 1.12.** For prime $p$ and any integer $a$: either $p \mid a$, or $\gcd(p,a) = 1$. (Because $p$'s only positive divisors are $1$ and $p$ — if $p \nmid a$, then $p$ can't be a *common* divisor of $p,a$, leaving only $1$.)
- **Lemma 1.13.** If prime $p \mid ab$, then $p \mid a$ or $p \mid b$. (Direct from 1.12 + Lemma 1.10: if $p \nmid a$, then $\gcd(p,a)=1$, so Lemma 1.10 with the roles $a{\to}p, b{\to}a, c{\to}b$ gives $p \mid b$.)

**Theorem 1.14 (Fundamental Theorem of Arithmetic).** Every integer $>1$ factors into primes, and this factorization is unique up to reordering.

*Existence* is a straightforward "keep factoring composite factors until everything is prime" descent argument — it terminates because the factors strictly shrink and the smallest allowed factor is $2$. This is your first taste of a **well-founded descent argument**: no explicit induction variable is named, but the proof is really "induction on the size of $a$."

*Uniqueness* is more interesting structurally. Given two factorizations $a = p_1^{n_1}\cdots p_s^{n_s} = q_1^{m_1}\cdots q_t^{m_t}$, the argument is:

1. $p_1 \mid a = q_1^{m_1}\cdots q_t^{m_t}$. By the generalized form of Lemma 1.13 (a prime dividing a product of $k$ factors divides *some* factor — Exercise 3, proved by induction on $k$), $p_1$ divides some $q_j$; since $q_j$ is prime, $p_1 = q_j$.
2. Relabel so $p_1 = q_1$, then show $n_1 = m_1$ by a symmetric "can't have $n_1 > m_1$ or $m_1 > n_1$" contradiction argument.
3. Cancel $p_1^{n_1}$ from both sides (legal because $\mathbb{Z}$ is an integral domain — cancellation holds) and recurse on the smaller product.

This "peel off one prime, show it matches, cancel, recurse" pattern reappears **essentially unchanged** as the proof of unique factorization for polynomials in $F[x]$ (Theorem 5.19) — irreducible polynomials play the role of primes, and the only real difference is that polynomial factorizations are unique up to multiplication by a nonzero constant rather than exactly, since $F[x]$ has more "units" than $\{1,-1\}$.

```python
# Existence half of FTA as a direct descent — mirrors the book's proof structure,
# not an efficient factorization algorithm.
def prime_factorize(n: int) -> list[int]:
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors
```

## Euclid's proof: infinitude of primes

**Theorem 1.18.** There are infinitely many primes.

The book is careful to flag a tempting *wrong* argument first: "there are infinitely many integers, each factors into primes by FTA, so there must be infinitely many primes" — this is a non sequitur (infinitely many integers can, in principle, all be built from finitely many primes via ever-larger exponents; FTA alone doesn't rule that out).

The actual proof, by contradiction: suppose primes are exactly $p_1,\ldots,p_n$ (finite list). Let $a = p_1p_2\cdots p_n + 1$. By FTA, $a$ has *some* prime factor $q$; since the list is supposedly exhaustive, $q = p_i$ for some $i$. But then dividing $a$ by $p_i$ leaves remainder $1$ (since $a - p_i \cdot(\text{product of the others}) = 1$), so $p_i \nmid a$ — contradiction. Hence no finite list of primes can be exhaustive.

```lean
-- The structure of Euclid's argument, as a proof skeleton:
theorem infinite_primes : ¬ ∃ (l : List ℕ), ∀ p, p.Prime → p ∈ l := by
  rintro ⟨l, hl⟩
  let a := l.prod + 1
  -- a > 1, so a has some prime factor q (by FTA-style existence)
  -- q ∈ l by hl, so q divides l.prod
  -- q divides a (since q is a factor) and q divides l.prod ⟹ q divides 1 — contradiction
  sorry
```

Why this proof is "justly celebrated for its beauty" (the book's own words): it's a *pure existence* argument — it never actually exhibits a new prime, it just shows any *purported* finite complete list is self-contradicting. That's a proof-by-contradiction pattern worth internalizing on its own, independent of number theory.

## Where this leads

This chapter's real export isn't number theory — it's a **template**: (1) find the right well-founded ordering, (2) use it to guarantee a minimal/least witness exists, (3) characterize the object of interest (gcd, minimal polynomial, etc.) as that witness, (4) get uniqueness and closure properties almost for free. Chapter 5 ([[Polynomial-Rings-and-Factorization|Polynomial Rings and Factorization]]) runs this exact template again with polynomial degree standing in for integer size — division algorithm, gcd-as-linear-combination, irreducibles-as-primes, unique factorization, all reappear nearly verbatim. Chapter 6's minimal polynomial construction (the unique monic polynomial of least degree satisfied by an algebraic element) is *also* this same pattern, one more level removed. If you're building a Rust type-checker or elaborator later and find yourself reaching for "take the well-founded-least element of some property-satisfying set" to prove a normal form is unique, this chapter is the cleanest possible worked example of that move before it gets buried in more machinery.
