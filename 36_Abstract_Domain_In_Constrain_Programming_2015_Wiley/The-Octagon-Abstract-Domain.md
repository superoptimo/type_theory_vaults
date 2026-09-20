---
title: The Octagon Abstract Domain
source: Abstract Domains in Constraint Programming (2015, Wiley)
chapter: "Chapter 4: Octagons"
pages: 77-90
tags: [abstract-interpretation, constraint-programming, octagons, difference-bound-matrix, galois-connection, sat-smt-csp, static-analysis]
---

[[book-guidelines|↩ Back to guidelines]]

# The Octagon Abstract Domain

## The gap intervals and polyhedra leave open

Two abstract domains sit at the extremes of the accuracy/cost tradeoff. **Boxes** (intervals per variable, $v_i \in [a,b]$) are cheap — $O(n)$ space, trivial to intersect, trivial to split — but they are *non-relational*: they can't express that $v_1$ and $v_2$ are correlated. If your constraint set implies $v_1 - v_2 \le 2$, a box can only ever discover that fact by shrinking $v_1$'s and $v_2$'s *individual* ranges, which for a rotated or skewed solution region converges arbitrarily slowly, or not usefully at all. **Polyhedra** (arbitrary linear inequalities) capture every linear correlation exactly, but the domain operations — intersection, union, projection — cost worst-case exponential in the number of variables, because the number of facets of a polyhedron can blow up combinatorially.

Octagons, introduced by Antoine Miné for abstract interpretation of software ([MIN 06]) and repurposed here for constraint solving, are the classic answer to "give me *some* relational information without paying the polyhedron bill." The restriction that makes this possible: only constraints of the shape

$$\pm v_i \pm v_j \le c, \qquad c \in \mathbb{R}$$

are allowed — every constraint touches at most two variables, and only with coefficients $+1$ or $-1$. This is exactly enough to express "these two variables are correlated in this direction," but not enough to blow up combinatorially: the number of such constraints on $n$ variables is bounded by $2n^2$, so both the representation and the core algorithm (closure) are polynomial — $O(n^3)$, the same complexity as all-pairs shortest paths, which is not a coincidence.

**What breaks without this restriction:** if you allow arbitrary linear coefficients, you're back to polyhedra and lose the polynomial closure algorithm; if you drop relational constraints entirely, you're back to boxes and lose the ability to detect that, say, $v_1 + v_2 \le 10$ is implied by other constraints even when no individual variable's box shrinks — losing that information means either false "maybe" answers on constraints that are actually entailed, or wasted search into regions the octagon should have pruned outright.

Geometrically, an octagonal constraint is a half-space bounded by a line parallel to an axis ($i = j$, giving ordinary interval bounds) or to a diagonal at $45°$ ($i \ne j$). In $\mathbb{R}^2$, a conjunction of these can carve out a shape with up to 8 sides — hence the name — though note the book's definition is broader than the geometric one: an "octagon" here can have *fewer* than eight sides (some directions unconstrained), and in $\mathbb{R}^n$ the shape has at most $2n^2$ faces (not literally 8), so the name is really "the abstract domain whose shape looks octagonal in 2D," generalized dimension-agnostically.

![[octagon_domain.svg]]

*Left: an octagon in the canonical basis, defined by axis-aligned and diagonal half-spaces. Right: the same information viewed as an intersection of boxes, one in the canonical basis and one in a basis rotated by $\pi/4$ — the "intersection of boxes" representation developed below.*

## Definitions: octagonal constraints, and the octagon itself

**Definition 4.1.1 (Octagonal constraint).** For variables $v_i, v_j$, an octagonal constraint has the form $\pm v_i \pm v_j \le c$, $c \in \mathbb{R}$. Ordinary interval bounds ($v_i \ge a$, $v_i \le b$) are the special case $i = j$.

**Definition 4.1.2 (Octagon).** An octagon is the set of points in $\mathbb{R}^n$ satisfying a conjunction of octagonal constraints. Every octagon is convex (each constraint is a half-space, and the intersection of half-spaces is convex) — this matters because convexity is exactly what makes "closure," "join," and "split" all well-defined without producing degenerate or disconnected shapes.

Two closure properties are worth internalizing before anything else, because they're what make octagons usable as a *lattice element* in an abstract-interpretation or CSP-propagation loop:

- **Closed under intersection** (Remark 4.1.4): $\{\pm v_i \pm v_j \le c\} \cap \{\pm v_i \pm v_j \le c'\} = \{\pm v_i \pm v_j \le \min(c,c')\}$ — intersecting two octagons is just taking the pointwise min of matching constraints. This is cheap and exact.
- **Not closed under union**, but the *smallest enclosing octagon* is: $\{\pm v_i \pm v_j \le c\} \cup \{\pm v_i \pm v_j \le c'\} \subseteq \{\pm v_i \pm v_j \le \max(c,c')\}$ (Remark 4.1.5). This is the standard abstract-domain move — you don't need exact union, you need the least upper bound *in the domain*, and taking the componentwise max gives it for free.

If you've internalized [[Abstract-Interpretation-Foundations|Galois connections and lattices]] already, this should look familiar: intersection-as-meet and enclosing-union-as-join are exactly the lattice operations a domain needs to support a fixpoint iteration.

## Representation 1: the difference bound matrix

You can't store "a conjunction of $\pm v_i \pm v_j \le c$ constraints" directly as a convenient array — the $\pm$ signs mean each pair $(v_i, v_j)$ has up to four independent constraints. Miné's trick, borrowed from timing-constraint analysis, is to double the variable set: introduce $w_{2i-1} = v_i$ and $w_{2i} = -v_i$, so that *every* octagonal constraint, regardless of its sign pattern, becomes a **difference constraint** $w - w' \le c$ between two of these primed variables.

**Definition 4.2.1 (Difference constraint).** $w - w' \le c$, for variables $w, w'$ and constant $c \in \mathbb{F}$ (floating point, in the implementable version).

The rewriting rules (for $i \ne j$, the relational case) are mechanical case-analysis on the two signs:

| Octagonal constraint | Equivalent difference constraint(s) |
|---|---|
| $v_i - v_j \le c$ | $w_{2i-1} - w_{2j-1} \le c$ and $w_{2j} - w_{2i} \le c$ |
| $v_i + v_j \le c$ | $w_{2i-1} - w_{2j} \le c$ and $w_{2j-1} - w_{2i} \le c$ |
| $-v_i - v_j \le c$ | $w_{2i} - w_{2j-1} \le c$ and $w_{2j} - w_{2i-1} \le c$ |
| $-v_i + v_j \le c$ | $w_{2i} - w_{2j} \le c$ and $w_{2j-1} - w_{2i-1} \le c$ |

**Definition 4.2.2 (Difference bound matrix, DBM).** A $2n \times 2n$ matrix $M$ where $M[i][j]$ is the tightest known constant $c$ such that $w_j - w_i \le c$ (row/column indexing convention follows the book: the entry at row $i$, column $j$ bounds $w_j - w_i$).

This is a graph in disguise: think of each $w_k$ as a node, and each entry $M[i][j] = c$ as a directed edge $i \to j$ weighted $c$, meaning "the distance from $i$ to $j$ is at most $c$." A path $i \to k \to j$ with weights $c_1, c_2$ implies $M[i][j] \le c_1 + c_2$ (triangle inequality on differences) — so *tightening* the matrix to its best possible values is exactly **all-pairs shortest paths**. That's why the closure algorithm below is Floyd-Warshall.

```rust
/// A difference-bound-matrix octagon over n original variables (2n internal rows/cols).
/// M[i][j] represents the tightest known bound on w_j - w_i.
struct Dbm {
    n: usize,
    m: Vec<Vec<f64>>, // 2n x 2n, initialized to +inf off constraints, 0 on the diagonal
}

impl Dbm {
    fn new(n: usize) -> Self {
        let size = 2 * n;
        let mut m = vec![vec![f64::INFINITY; size]; size];
        for i in 0..size {
            m[i][i] = 0.0;
        }
        Dbm { n, m }
    }

    /// Add w_j - w_i <= c, tightening if this bound is stronger than what's known.
    fn add_difference(&mut self, i: usize, j: usize, c: f64) {
        self.m[i][j] = self.m[i][j].min(c);
    }

    /// i' flips a variable's positive/negative "copy": even indices <-> odd neighbor.
    fn flip(k: usize) -> usize {
        if k % 2 == 0 { k - 1 } else { k + 1 }
    }
}
```

## Closure: the modified Floyd-Warshall algorithm

Closing a DBM means computing, for every pair, the tightest bound derivable from the whole constraint set — the fixpoint of the triangle inequality. A naive Floyd-Warshall on the $2n \times 2n$ matrix would work, but it ignores the structural fact that rows $2i{-}1$ and $2i$ both describe the *same* underlying variable $v_i$ (as $+v_i$ and $-v_i$). Algorithm 4.1 exploits that redundancy with an extra pass:

```rust
/// Modified Floyd-Warshall closure for octagonal DBMs (Algorithm 4.1).
/// Returns Err if the octagon is empty (a variable's self-loop goes negative).
fn close(dbm: &mut Dbm) -> Result<(), &'static str> {
    let size = 2 * dbm.n;

    for k in 0..dbm.n {
        let k2 = 2 * k + 1;      // "2k" in 1-indexed book notation
        let k2m1 = 2 * k;        // "2k - 1"
        // Standard shortest-path relaxation, but routing through both
        // the positive and negative copies of variable v_{k+1}.
        for i in 0..size {
            for j in 0..size {
                let via = [
                    dbm.m[i][k2] + dbm.m[k2][j],
                    dbm.m[i][k2m1] + dbm.m[k2m1][j],
                    dbm.m[i][k2m1] + dbm.m[k2m1][k2] + dbm.m[k2][j],
                    dbm.m[i][k2] + dbm.m[k2][k2m1] + dbm.m[k2m1][j],
                ];
                let best = via.iter().cloned().fold(dbm.m[i][j], f64::min);
                dbm.m[i][j] = best;
            }
        }
        // Exploit w_{2i-1}/w_{2i} coupling: route through a variable's own flip.
        for i in 0..size {
            for j in 0..size {
                let ip = Dbm::flip(i);
                let jp = Dbm::flip(j);
                dbm.m[i][j] = dbm.m[i][j].min(dbm.m[i][ip] + dbm.m[jp][j]);
            }
        }
    }

    for i in 0..size {
        if dbm.m[i][i] < 0.0 {
            return Err("empty octagon: negative self-loop detected");
        }
        dbm.m[i][i] = 0.0;
    }
    Ok(())
}
```

The correctness argument for the "negative diagonal ⇒ empty" check is a one-liner once you see the graph reading: $M[i][i]$ is the shortest cycle from $w_i$ back to itself, i.e. a derived bound on $w_i - w_i \le c$. Since $w_i - w_i = 0$ identically, any derived $c < 0$ is a contradiction — the constraint set is unsatisfiable, so the octagon is empty. This closure runs in $O(n^3)$, same complexity class as unmodified Floyd-Warshall — the extra structural pass doesn't change the asymptotic cost, it just tightens the *result* using information plain APSP would miss.

## Representation 2: intersection of boxes, and rotated bases

The DBM is compact but opaque for some CP-specific operations (like consistency checks per variable). The book's own contribution is a second, equivalent representation: an octagon as the **intersection of several boxes**, each living in a different rotated coordinate system.

In 2D: rotate the axes by $\alpha = \pi/4$ and you get a new pair of "diagonal" coordinates. A box in the *original* axes plus a box in the *rotated* axes, intersected, reproduces the octagon. This generalizes to $n$ dimensions by rotating one *pair* of coordinates $(v_i, v_j)$ at a time and leaving the rest fixed:

**Definition 4.2.3 (Rotated basis).** For canonical basis $B = (u_1, \dots, u_n)$ and $\alpha = \pi/4$, the $(i,j)$-rotated basis $B_\alpha^{i,j}$ replaces $u_i, u_j$ with $\cos(\alpha)u_i + \sin(\alpha)u_j$ and $-\sin(\alpha)u_i + \cos(\alpha)u_j$, leaving every other basis vector untouched. A variable living in this rotated basis is written $v_k^{i,j}$.

There are $\binom{n}{2}$ such rotated-pair bases, plus the canonical one — that's the source of the $n(n+1)/2$ figure the chapter cites for how many "boxes" jointly represent one octagon. Each box $B^{i,j}_O$ is read directly off the DBM entries (Proposition 4.2.1 gives the exact index arithmetic — e.g. $I_i^{i,j} = [-\tfrac{1}{\sqrt2}M[2j{-}1,2i],\ \tfrac{1}{\sqrt2}M[2j,2i{-}1]]$), and **the octagon is exactly the intersection of all of them**:

$$O = \bigcap_{i,j \in \llbracket 1,n\rrbracket} B_O^{i,j}$$

```rust
/// One "rotated-basis box": an octagon viewed as a hull-consistent
/// interval box in the (i, j)-rotated coordinate system.
struct RotatedBox {
    basis: (usize, usize), // (i, j); (k, k) denotes the canonical basis
    bounds: Vec<(f64, f64)>, // one [lo, hi] pair per coordinate in this basis
}
```

Why bother with a second representation of the same object? Because **consistency and propagation** (the CSP machinery from [[Consistency-and-Propagation-in-Constraint-Programming|Consistency and Propagation]]) are naturally box-shaped operations — hull-consistency, splitting, and precision are all much easier to state and implement per-box than as raw matrix surgery. The DBM gives you the cheap *closure* algorithm; the box view gives you the CSP-native *operators*. Converting between them costs only a multiplication/division with appropriate floating-point rounding — cheap, and worth paying to get both views.

## The domain's operators: splitting and precision

An abstract domain used inside a branch-and-prune solver (see [[Exploration-and-Search-in-Constraint-Programming|Exploration and Search]]) needs two things beyond closure: a way to **split** an element into smaller sub-elements when it isn't yet a solution, and a way to measure an element's **precision** (size) to decide when to stop.

**Definition 4.3.1 (Octagonal splitting operator).** Given an octagon as boxes $I_1, \dots, I_n, I_1^{1,2}, \dots, I_n^{n-1,n}$, splitting on variable $v_k^{i,j} = [a,b]$ produces two sub-octagons, replacing that one interval with $[a,h]$ and $[h,b]$ respectively, $h = \frac{a+b}{2}$ (rounded in $\mathbb{F}$). The key generalization over interval splitting: this operator takes *three* parameters $(i,j,k)$ — which rotated basis, and which coordinate within it — not just one. Splitting in a rotated basis cuts the octagon along a diagonal, something interval splitting can never do.

Because a split changes one box's bounds without automatically updating the others, **every split must be immediately followed by another Floyd-Warshall closure pass** to propagate the new bound across all the other rotated bases — otherwise the representation becomes internally inconsistent (the boxes would no longer describe the same intersection).

```rust
/// Split box coordinate `k` of the rotated basis `(i, j)` at its midpoint.
/// Caller MUST re-run `close()` afterward — the other bases are now stale.
fn split(oct: &RotatedBox, k: usize) -> (RotatedBox, RotatedBox) {
    let (a, b) = oct.bounds[k];
    let h = a + (b - a) / 2.0; // midpoint, rounded to F in a real implementation
    let mut left = oct.bounds.clone();
    let mut right = oct.bounds.clone();
    left[k] = (a, h);
    right[k] = (h, b);
    (
        RotatedBox { basis: oct.basis, bounds: left },
        RotatedBox { basis: oct.basis, bounds: right },
    )
}
```

**What breaks without a relational precision function:** the obvious definition — "precision = size of the largest per-variable interval" — silently discards exactly the information octagons were built to keep. Two variables can each look wide open in the canonical box while being tightly correlated on the diagonal (imagine a thin sliver rotated 45°) — a per-axis measure would report "imprecise" on an octagon that is, diagonally, already very tight.

**Definition 4.3.2 (Octagonal precision).**
$$\tau_o(O) = \min_{i,j \in \llbracket 1,n\rrbracket} \left(\max_{k \in \llbracket 1,n\rrbracket} \left|I_k^{i,j}\right|\right)$$

Take the widest interval *within* each rotated-basis box, then take the *minimum* across all bases — i.e., report the size of the *tightest* basis, because that basis is the one giving you the most accurate localization. Proposition 4.3.1 cashes this out operationally: if $\tau_o(O) = r$, every point of $O$ is within distance $r$ of an actual solution — precision isn't just a heuristic stopping criterion, it's a certified error bound on the over-approximation, which is exactly the property you need if this domain is going to certify absence of bugs rather than just guess at it.

## The complete lattice and the Galois connection back to boxes

Two propositions turn "a representation with some operators" into "a legitimate abstract domain" in the technical sense from [[Abstract-Interpretation-Foundations|Abstract Interpretation Foundations]]:

- **Proposition 4.4.1**: the set of octagons $\mathcal{O}$ forms a **complete lattice** under inclusion — every finite set of octagons has both a least upper bound (Remark 4.1.4's intersection-as-meet) and a greatest lower bound (Remark 4.1.5's enclosing-union-as-join).
- **Proposition 4.4.2**: there is a **Galois connection** $\mathcal{O} \underset{\gamma_o}{\overset{\alpha_o}{\rightleftarrows}} \mathcal{B}$ between octagons and boxes:
  - $\alpha_o(O)$ keeps only the constraints of shape $\pm v_i \le c$ (drop every genuinely relational constraint, keep only the axis-aligned ones) — this is lossy abstraction, exactly as you'd expect from a Galois connection's upper adjoint.
  - $\gamma_o(B) = B$ — every box already *is* a valid octagon (concretization is the trivial inclusion).

This is a clean, minimal instance of the Galois-connection pattern: octagons *are themselves* an abstraction of the concrete solution set, and boxes are in turn a coarser abstraction *of octagons* — a two-level abstraction tower, each level trading precision for tractability.

**Definition 4.4.1 (Octagon abstract domain)** packages all of this: the lattice $\mathcal{O}$, the Galois connection to $\mathcal{B}$, the intersection-of-boxes representation, the splitting operator $\oplus_o$, and the precision function $\tau_o$. That's a complete abstract-domain interface — everything a generic solver (from [[Unified-Abstract-Domains-for-Constraint-Programming|Unified Abstract Domains for Constraint Programming]]) needs to plug octagons in as one instance among many.

```
                    α_o (drop relational constraints)
        Octagons  ─────────────────────────────────►  Boxes
           𝒪       ◄─────────────────────────────────    ℬ
                    γ_o (a box is already an octagon)

  𝒪 is a complete lattice:  meet = intersection (Remark 4.1.4)
                            join = enclosing octagon (Remark 4.1.5)
```

## Partial octagons: not every rotated basis is worth generating

A full octagon on $n$ variables needs $n(n+1)/2$ bases — quadratic blowup in both space and closure cost, even though closure stays polynomial. **Definition 4.4.2 (Partial octagon)** relaxes this: pick index sets $J, K \subseteq \llbracket 1,n \rrbracket$ and only keep constraints $\{\pm v_i \pm v_j \le c \mid i \in J, j \in K\} \cup \{\text{unary bounds on all variables}\}$. When $J = K = \llbracket 1,n\rrbracket$, this is exactly Definition 4.1.2 — full octagons are the special case where every pairing is kept. The properties proved for full octagons (lattice structure, Galois connection, closure) transfer to partial octagons essentially for free, because the proofs never used "every pair" — they only used "the constraints present form a coherent difference-constraint system."

This is the domain's actual scalability lever in practice: rather than paying $O(n^2)$ bases unconditionally, an **octagonalization heuristic** decides *which* pairs of variables are worth relating — ideas the chapter defers to Section 5.3.2 (heuristics like `ConstraintBased`, `Random`, `StrongestLink`, `Promising`), covered in [[Octagonal-Constraint-Solving|Octagonal Constraint Solving]].

## Where this leads

Octagons are the load-bearing middle layer of this book's abstract-domain story: [[Constraint-Satisfaction-Problem-Foundations|CSP Foundations]] and [[Consistency-and-Propagation-in-Constraint-Programming|Consistency and Propagation]] set up *why* you need relational information beyond intervals; this chapter builds the one relational domain cheap enough to actually deploy; and [[Octagonal-Constraint-Solving|Octagonal Constraint Solving]] takes these exact operators (DBM closure, box representation, split, $\tau_o$) and wires them into a full CSP solving loop with dedicated propagation and octagonalization heuristics. [[The-AbSolute-Solver|The AbSolute Solver]] later shows this domain (alongside polyhedra) running for real, on top of Apron.

For the `sat-smt-csp` and `static-analysis` focus areas specifically: this chapter is a fully worked example of **domain propagation on an abstract lattice** — the DBM closure algorithm *is* constraint propagation to a fixpoint, phrased in the vocabulary of shortest-path graphs rather than worklist algorithms. If your CSP kernel needs a relational domain for integer/real invariant generation that's cheaper than polyhedra but stronger than boxes — exactly the shape of problem "prove absence of bugs by over-approximation" runs into constantly — the octagon domain (or its closure algorithm, generalizable to other difference-constraint-shaped abstractions like the *zone* domain in timed-automata verification) is the standard off-the-shelf answer, and Miné's original [MIN 06] paper is the citation trail if you want the software-verification framing directly rather than through this book's CSP lens.
