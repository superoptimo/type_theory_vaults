---
title: Reduction Constraints for Sparse Bilinear Programs
book: Reformulation and Convex Relaxation Techniques for Global Optimization (Liberti, 2004)
chapter: Chapter 3, pp. 60-89
tags: [optimization, global-optimization, bilinear-programming, graph-theory, bipartite-matching, convex-relaxation, spatial-branch-and-bound]
---

# Reduction Constraints for Sparse Bilinear Programs

[[book-guidelines|↩ Back to guidelines]]

## The problem this chapter solves

Every spatial Branch-and-Bound (sBB) algorithm for nonconvex optimization lives or dies by one thing: how tight is the convex relaxation it can build at each node of the search tree? A loose relaxation gives a weak lower bound, the algorithm can't prune, and the search tree explodes. This is exactly analogous to the LP relaxation in integer programming — except, as Chapter 1 of the thesis stresses, an NLP's convex relaxation is not unique the way an LP relaxation of a MILP is. *How you write down the problem* changes how tight the relaxation can be. That's the thesis's whole thesis, if you like: formulation matters as much as algorithm.

Chapter 2 surveyed the standard toolkit for relaxing nonconvex terms. For a bilinear term $z_i = z_j z_k$, the workhorse is the **McCormick envelope**: given bounds $z_j \in [z_j^L, z_j^U]$, $z_k \in [z_k^L, z_k^U]$, you replace the equality with four linear inequalities

$$
z_i \ge z_j^L z_k + z_k^L z_j - z_j^L z_k^L, \qquad z_i \ge z_j^U z_k + z_k^U z_j - z_j^U z_k^U,
$$
$$
z_i \le z_j^U z_k + z_k^L z_j - z_j^U z_k^L, \qquad z_i \le z_j^L z_k + z_k^U z_j - z_j^L z_k^U.
$$

This is a genuinely useful envelope — it's the *tightest possible* convex relaxation of $z_i = z_j z_k$ given only the box bounds. But "tightest given only box bounds" is the catch. If a bilinear constraint is secretly redundant — if the *feasible set itself*, not just its relaxation, happens to be flatter than it looks — McCormick can't know that. It relaxes the equation you wrote, not the equation you could have written.

Chapter 3's contribution is a way to notice, automatically and cheaply, when that's happening: when a bilinear constraint's feasible region, intersected with the problem's other linear constraints, is *actually a hyperplane* — and to replace the nonlinear equation with the linear one that describes it exactly. This isn't a relaxation. It's an **exact reformulation** (in the sense of Chapter 2's exact-vs-relaxation distinction) that happens to produce a *tighter relaxable problem* as a side effect. You lose nothing from the feasible region, and you gain a strictly smaller, strictly tighter convex relaxation for free.

**What breaks without this:** without it, every bilinear term in a large sparse NLP — say, a refinery pooling problem with hundreds of flow-times-concentration terms — gets its own independent McCormick box, even when several of those terms are linearly entangled by the problem's own mass-balance constraints. The relaxation ends up far looser than the feasible region's actual geometry warrants, and sBB pays for that looseness in exploded node counts. The chapter's own numbers make this concrete later (Table 3.2): adding reduction constraints to an otherwise bare-bones sBB solver takes it from tens of thousands of nodes down to single digits on several benchmark instances.

## 3.1 — The basic idea: multiplying a constraint by a variable

Liberti's standard NLP form $[P]$ (used throughout the thesis and derived automatically by symbolic reformulation in Chapter 5) separates a problem into a linear part and defining constraints for every nonlinear term:

$$
[P]:\quad
\begin{aligned}
\min_z \quad & z_l \\
& Az = b \\
& z_i = z_j z_k && \forall (i,j,k) \in B \\
& z_i = z_j / z_k && \forall (i,j,k) \in F \\
& z_i = f_i(z_j) && \forall (i,j) \in N \\
& z^L \le z \le z^U
\end{aligned}
$$

where $z \in \mathbb{R}^p$, $A$ is $m \times p$ of full row rank $m$, $B$ indexes the bilinear terms, $F$ the fractional terms, $N$ the univariate nonlinear terms. This is the "factorable form" idea from Chapter 2, pushed to a normal form: *every* nonlinearity in the problem, however deeply nested in the original model, gets pulled out into its own defining equation, leaving only genuinely linear structure in $Az=b$.

Here's the core observation, in its simplest form. Suppose the problem contains a bilinear defining constraint

$$
w = xy
$$

and *also* a linear constraint involving $x$, say (writing it generically)

$$
a^T x' = b_0.
$$

Multiply the linear constraint through by $y$:

$$
y\,a^T x' = y\,b_0.
$$

If $x$ happens to be one of the components of $x'$, then the term $y \cdot x$ appears on the left — and by the defining constraint, $yx = w$. Substitute:

$$
a^T (\text{terms}) + (\text{coefficient of } x)\cdot w + \cdots = y\, b_0.
$$

This is a **new constraint, linear in the original variables plus $w$ and $y$** (and possibly a few other new bilinear terms, if $x'$ has other components). Call it a **reduction constraint**. It is *redundant* — it follows algebraically from constraints already in the problem, so adding it changes nothing about the feasible set. But redundant is not useless: because it's linear, it can be used to *eliminate* the bilinear defining constraint $w = xy$ from the problem altogether, replacing a nonlinear equation with a linear one that captures exactly the same information (in the presence of the rest of the system).

**Worked miniature (the book's own extreme case, §3.1.1).** Take one variable pair, $w = xy$, together with the single linear constraint $x = 1$ (so $a^T x' = b_0$ is literally $x=1$). Multiplying by $y$ gives $xy = y$, i.e. $w = y$ (a *linear* constraint, once you substitute the defining equation). Geometrically: $w=xy$ is a saddle-shaped hyperbolic paraboloid in $(x,y,w)$-space. Slicing it with the vertical plane $x=1$ gives a curve on that surface — and that curve is the straight line $w=y$. The book's Figure 3.1 draws exactly this: the bilinear surface, the vertical plane $x=1$, and the skew plane $w-y=0$ all meeting along one line. The set

$$
S = \{(x,y,w) : w=xy,\ x=1,\ (x,y,w)\in\text{bounds}\}
$$

is identical, point for point, to

$$
S' = \{(x,y,w) : w=y,\ x=1,\ (x,y,w)\in\text{bounds}\}.
$$

But $S'$ is defined by *purely linear* relationships. Convexifying $w=xy$ inside an sBB algorithm — building a McCormick box for it — would be both unnecessary (the constraint contributes nothing $w=y$ doesn't already say) and actively counter-productive (it adds slack the true feasible region doesn't have).

The general pattern — two linear constraints, both multiplied by the same variable, then linearly combined to eliminate an auxiliary bilinear term they jointly introduce — extends this to arbitrarily larger systems, and that generalization is what §3.2's theorem makes rigorous.

## 3.2 — Fundamental properties: Theorem 3.2.1

The informal argument above raises an obvious worry: does this *always* work, or only in cherry-picked examples? Theorem 3.2.1 answers it precisely, for the case of multiplying an entire full-row-rank linear subsystem by one variable at once.

**Setup.** $Ax = b$ is a linear system with $\mathrm{rank}(A) = m$ (so it constrains $x \in \mathbb{R}^n$ down to an $(n-m)$-dimensional affine subspace, in the usual sense — $m$ independent equations pin down $m$ degrees of freedom). Fix a multiplier variable $y$. Define $w_j = x_j y$ for every $j \le n$ (these are the bilinear defining constraints — one per component of $x$).

$$
C = \{(x,w,y) \mid Ax = b \ \wedge\ \forall j \le n\ (w_j = x_j y)\}
$$

is the "honest" feasible set: satisfy the linear system *and* every one of the $n$ bilinear definitions.

$$
R_J = \{(x,w,y) \mid Ax=b\ \wedge\ Aw - yb = 0\ \wedge\ \forall j \in J\ (w_j = x_jy)\}
$$

is a *relaxed* version: keep the linear system, keep the **reduction constraint** $Aw - yb = 0$ (this is exactly "multiply $Ax=b$ by $y$" — since $Ax=b \Rightarrow yAx = yb \Rightarrow A(yx) = yb$, and $yx = w$ componentwise), but only keep the *bilinear* definitions for a subset $J \subseteq \{1,\dots,n\}$ of the indices — the rest are "forgotten," replaced by nothing but the linear reduction constraint.

**Theorem 3.2.1.** *There is at least one index set $J$, with $|J| = n-m$, such that $C = R_J$.*

In words: you can discard $m$ of the $n$ bilinear defining constraints — replacing them with nothing but the single linear reduction-constraint block $Aw-yb=0$ — and recover the *exact same* feasible set. You don't lose information; the $m$ discarded bilinear equations were, in the presence of the reduction constraint and the remaining $n-m$ definitions, redundant.

**Why the proof works (the mechanism, not just the statement).** The inclusion $C \subseteq R_J$ is trivial — every point satisfying all $n$ bilinear definitions certainly satisfies any $n-m$ of them, and it satisfies $Aw=yb$ because that follows algebraically from $Ax=b$ multiplied through by $y$. The interesting direction is $R_J \subseteq C$: given a point that satisfies the linear system, the reduction constraint, and *only* the bilinear definitions in $J$, why must it also satisfy the other $m$?

Define the residual $u_j = w_j - x_j y$ for every $j$ — this measures "how far $w_j$ is from actually equalling $x_j y$." The reduction constraint $Aw - yAx = 0$ (using $b=Ax$) becomes, after substitution, the *homogeneous* linear system $Au = 0$. Now use $\mathrm{rank}(A)=m$: there's a permutation of columns splitting $A = (A_0\ A_1)$ with $A_0$ a nonsingular $m\times m$ block. Let $J$ be the index set corresponding to the *other* $n-m$ columns (the ones in $A_1$). Because the point is in $R_J$, we already know $u_j = 0$ for $j \in J$ — that's exactly what "$w_j = x_jy$ for $j\in J$" means. Plugging $u^{(1)} = 0$ into $A_0 u^{(0)} + A_1 u^{(1)} = 0$ gives $A_0 u^{(0)} = 0$, and since $A_0$ is nonsingular, $u^{(0)} = 0$ too. So *all* $n$ residuals vanish — the discarded bilinear constraints hold automatically.

This is Gaussian elimination wearing a different hat: the reduction constraint plus the surviving bilinear definitions pin down the residual vector $u$ to lie in the kernel of a system that, restricted to the "discarded" columns, is invertible — so the kernel is forced to zero exactly there.

**Invariance in $y$.** A second, easy-to-miss consequence: rerun the argument for a different multiplier variable $x_k$ instead of $y$. The proof shows $J$ is determined purely by which columns of $A$ can be pivoted into a nonsingular block — i.e., by $A$'s own structure, not by which variable you happened to multiply by. So the *same* index set $J$ works for every candidate multiplier. This is what makes an algorithm searching for good $J$'s over all variables at once (§3.3) sensible rather than combinatorially independent per variable.

**A structural note for the algebraic-graph-theory–minded reader.** Notice what this theorem *is*, underneath the optimization dressing: a statement about which rows of a linear system are implied by which others, phrased via a rank/pivoting argument on $A$. If you've been thinking about **structural tractability** and **Galois/lattice-style propagation** in CSP terms, this is the same move constraint propagation makes when it prunes a redundant constraint from a network without changing its solution set — except here "redundant" is being certified by linear-algebraic rank rather than by an inference rule. In Lean/mathlib terms, the theorem is a direct corollary of `LinearMap.ker` and a full-rank submatrix being `IsUnit`: $A_0$ invertible $\Rightarrow$ $A_0 u^{(0)} = 0 \Rightarrow u^{(0)}=0$ is literally `Matrix.eq_zero_of_mul_eq_zero` composed with the invertibility instance. Formalizing Theorem 3.2.1 faithfully would mostly be plumbing around `Matrix.rank` and a column-permutation lemma — the mathematical content is exactly the trusted-kernel-sized fact "an invertible linear map has trivial kernel."

## 3.3 — Finding valid reduction constraints: a bipartite-graph algorithm

Theorem 3.2.1 says reduction constraints always exist *in principle* for a full-row-rank linear subsystem — but existence isn't the same as *worth using*. Multiplying a linear constraint by a variable can also introduce brand-new bilinear terms (whenever the constraint mentions a variable not already multiplied by the multiplier elsewhere in the problem). If a multiplication set creates more new bilinear terms than it eliminates old ones, it's a net loss. This is exactly the flaw the book identifies in **RLT** (Reformulation-Linearization Technique, from Chapter 2): RLT multiplies *every* linear constraint by *every* variable, indiscriminately, and lets the LP relaxation sort out which resulting constraints are useful — which is correct but combinatorially wasteful on large sparse problems.

### Valid reduction constraint sets

Given a candidate multiplier variable $y$ and a subset $\mathcal{L}$ of the problem's linear constraints, multiplying $\mathcal{L}$ by $y$ creates bilinear terms $\{x_j y : x_j \text{ occurs in some constraint of } \mathcal{L}\}$. Some of these terms already exist in the problem (they're already in $B$); call the count of terms that are genuinely *new* $\eta$. The theorem guarantees $\mathcal{L}$, when multiplied by $y$, can eliminate $|\mathcal{L}| - m'$ bilinear constraints for some rank-related $m'$ — but the practically relevant criterion the book adopts is simpler and more conservative:

$$
\mathcal{L} \text{ is a \emph{valid} reduction constraint set} \iff \eta < |\mathcal{L}|.
$$

Fewer new bilinear terms introduced than old constraints eliminated. Checking this by brute force means enumerating $2^{|\mathcal{L}|}$ subsets per candidate multiplier variable — hopeless for large sparse problems. The chapter's actual contribution is turning this into a graph problem with a fast, exact algorithm.

### The bipartite graph and dilations

For a fixed multiplier variable $y$, build a bipartite graph $\mathcal{G} = (\mathcal{N}^C \cup \mathcal{N}^V, \mathcal{E})$:

- **Constraint nodes** $\mathcal{N}^C$ — one per linear constraint in the problem.
- **Variable nodes** $\mathcal{N}^V$ — one per problem variable that does *not* already appear multiplied by $y$ in some existing bilinear term (these are exactly the variables whose multiplication by $y$ *would* create something new).
- **Edge** $(c, x) \in \mathcal{E}$ exists iff variable $x$ occurs in constraint $c$ — i.e., multiplying $c$ by $y$ would create the new bilinear term $xy$.

For a subset $S \subseteq \mathcal{N}^C$ of constraint nodes, let $N(S) \subseteq \mathcal{N}^V$ be its neighborhood — the variables that would newly appear if you multiplied exactly the constraints in $S$ by $y$. A **dilation** is a subset $S$ with $|N(S)| < |S|$ — fewer neighbors than members. This is *exactly* the "fewer new terms than eliminated constraints" criterion, restated as a graph property: valid reduction constraint sets are precisely dilations in $\mathcal{G}$.

This reframing matters because dilations in bipartite graphs are a well-studied object, tightly linked (by a form of Hall's theorem) to the existence of a **complete output set assignment (OSA)**: a matching that saturates every variable node. A graph has *no* dilation if and only if it has a complete OSA. So: find the maximum matching; whatever variable nodes it leaves unmatched, together with everything reachable from them by an alternating-path search, is exactly a dilation.

### AugmentPath and ValidReductionConstraints

The book gives this as two mutually recursive procedures — a standard augmenting-path bipartite matcher, and a driver that harvests the "stuck" search trees as dilations.

**`AugmentPath(λ, assign, visitedC, visitedV)`** — attempts to extend the matching by finding an augmenting path starting from unmatched constraint node $\lambda$:
1. Mark $\lambda$ as visited.
2. If $\lambda$ has an unvisited, unassigned adjacent variable node $\mu$: assign $\mu \leftarrow \lambda$, return `PathFound = true`.
3. Otherwise, for every unvisited variable node $\mu$ adjacent to $\lambda$: mark $\mu$ visited; recursively call `AugmentPath` on the constraint node $\mu$ is *currently* assigned to. If that recursive call succeeds, re-assign $\mu \leftarrow \lambda$ (displacing the old assignment one level up) and return `true`.
4. If nothing works, return `false`.

**`ValidReductionConstraints(y)`** — drives the search:
1. Build $\mathcal{G}$ for multiplier $y$; initialize all variable-node assignments to unassigned; $\mathcal{L} \leftarrow \emptyset$.
2. For each constraint node $\lambda$ in turn: reset the visited-flags, call `AugmentPath(λ, …)`.
3. If it returns `false`, add *every constraint node visited during that failed search* to $\mathcal{L}$ — line 16-18 of the book's Figure 3.3.
4. After all constraint nodes are processed, $\mathcal{L}$ is the valid reduction constraint set for multiplier $y$.

The reason step 3 is correct — that a *failed* augmenting-path search's visited set is precisely a dilation — is the constructive half of the OSA/dilation equivalence: when `AugmentPath` fails, it has, by construction, visited exactly one more constraint node than variable node (it always visits a constraint node before any of its variable neighbors, and by the time it gives up it has explored the whole alternating-reachable component without finding a free variable), and it has visited *every* variable node adjacent to any visited constraint node. That's the definition of a dilation, discovered as a byproduct of failing to grow the matching.

**Complexity.** `AugmentPath` touches every edge at most once per top-level call; `ValidReductionConstraints` calls it once per constraint node, so worst case is $O(|\mathcal{N}^C| \cdot |\mathcal{E}|)$ — but the book notes (citing Duff, 1981) that in practice, as with most matching-based algorithms on sparse graphs, it behaves closer to $O(|\mathcal{N}^C| + |\mathcal{E}|)$, which is what makes it usable on large, sparse industrial NLPs rather than just textbook examples.

### Grounding it: a Rust implementation

This is a genuine, self-contained graph algorithm, so it's worth writing faithfully rather than just describing. The recursive re-assignment structure in `AugmentPath` is a textbook Kuhn/Hopcroft-style augmenting-path matcher; the "harvest the failed search as a dilation" step is the one Liberti-specific addition.

```rust
use std::collections::HashSet;

/// A bipartite graph: constraint nodes 0..n_constraints, variable nodes 0..n_vars,
/// represented as an adjacency list from constraint -> variables.
struct BipartiteGraph {
    n_constraints: usize,
    n_vars: usize,
    adj: Vec<Vec<usize>>, // adj[constraint] = variables it's connected to
}

struct Matcher<'g> {
    g: &'g BipartiteGraph,
    /// assign[v] = Some(constraint) currently matched to variable v, or None.
    assign: Vec<Option<usize>>,
    visited_c: Vec<bool>,
    visited_v: Vec<bool>,
}

impl<'g> Matcher<'g> {
    fn new(g: &'g BipartiteGraph) -> Self {
        Matcher {
            g,
            assign: vec![None; g.n_vars],
            visited_c: vec![false; g.n_constraints],
            visited_v: vec![false; g.n_vars],
        }
    }

    /// Mirrors AugmentPath(lambda, ...) from Figure 3.2.
    fn augment_path(&mut self, lambda: usize) -> bool {
        self.visited_c[lambda] = true;

        // Lines 3-7: an unassigned, unvisited neighbor -> immediate augmentation.
        for &mu in &self.g.adj[lambda] {
            if !self.visited_v[mu] && self.assign[mu].is_none() {
                self.assign[mu] = Some(lambda);
                return true;
            }
        }

        // Lines 8-15: try displacing an already-assigned neighbor.
        for &mu in &self.g.adj[lambda] {
            if self.visited_v[mu] {
                continue;
            }
            self.visited_v[mu] = true;
            let owner = self.assign[mu].expect("unassigned nodes handled above");
            if self.augment_path(owner) {
                self.assign[mu] = Some(lambda);
                return true;
            }
        }
        false // Line 16: no augmenting path from lambda.
    }

    /// Mirrors ValidReductionConstraints(y) from Figure 3.3.
    /// Returns the set L of constraint indices forming a valid reduction
    /// constraint set for the multiplier variable this graph was built for.
    fn valid_reduction_constraints(&mut self) -> HashSet<usize> {
        let mut l_set = HashSet::new();
        for lambda in 0..self.g.n_constraints {
            self.visited_c.iter_mut().for_each(|b| *b = false);
            self.visited_v.iter_mut().for_each(|b| *b = false);
            if !self.augment_path(lambda) {
                // Harvest every constraint node visited during the failed search.
                for c in 0..self.g.n_constraints {
                    if self.visited_c[c] {
                        l_set.insert(c);
                    }
                }
            }
        }
        l_set
    }
}
```

Two things worth noticing about this translation. First, `AugmentPath`'s recursion is literally structural recursion on "how deep into the alternating tree are we" — there's no separate termination argument needed beyond "the visited-set only grows, and the graph is finite," which is the same shape of argument you'd give for termination of a unification or constraint-propagation search that marks visited nodes to avoid revisiting them. Second, the harvesting step (`for c in 0..n_constraints { if visited_c[c] ... }`) is doing something conceptually close to reading off an **unsatisfiable core** from a failed search — the visited set *is* the certificate that no larger matching exists through that component, in exactly the way a CDCL solver's conflict clause is a certificate that a partial assignment can't be extended.

A Python sketch of just the invariant being exploited — useful as a five-line mental model, not as a load-bearing artifact:

```python
def is_dilation(S, adjacency):
    """S: set of constraint indices. adjacency[c]: set of variable indices."""
    neighbors = set().union(*(adjacency[c] for c in S)) if S else set()
    return len(neighbors) < len(S)
```

## 3.4 — A detailed example: 6 variables, 4 constraints

To see the algorithm actually run, the book works a bilinear problem with 6 "real" variables $z_1,\dots,z_6$, 4 linear constraints, and every pairwise bilinear combination of the 6 variables (including squares) *except* $z_1z_2$, $z_1z_3$, $z_2z_3$, $z_3^2$ already present as auxiliary variables $z_7,\dots,z_{23}$ — 17 bilinear defining constraints in all, linearly combined into an objective $z_{24}$:

$$
\begin{aligned}
\min_z\ & z_{24} \\
& z_{24} = c^Tz \\
& Az' = b \\
& z_i = z_jz_k \quad \forall (i,j,k)\in B \\
& 0 \le z \le 10,
\end{aligned}
$$

with $z' = (z_1,\dots,z_6)^T$,

$$
A = \begin{pmatrix} 1 & 2 & & 1 & 1 & \\ 2 & -1 & & 1 & & 3 \\ & 1 & & 6 & 2 & -3 \\ 2 & & & 1 & 3 & \end{pmatrix}, \qquad b = (1,2,-1,1)^T,
$$

and $B = \{(7,1,1),(8,2,2),(9,4,4),(10,5,5),(11,6,6),(12,1,4),(13,1,5),(14,1,6),(15,2,4),(16,2,5),(17,2,6),(18,3,4),(19,3,5),(20,3,6),(21,4,5),(22,4,6),(23,5,6)\}$.

(Note $A$'s rows correspond to constraints $c_1,\dots,c_4$; blank entries are zero coefficients — e.g. $c_1: z_1 + 2z_2 + z_4 + z_5 = 1$.)

Only $z_1,\dots,z_6$ can possibly produce reduction constraints (multiplying by an already-fully-bilinear-connected auxiliary variable can't create anything new). The algorithm runs once per candidate multiplier.

**Multiplier $z_1$.** The bipartite graph $\mathcal{G}_1$ has constraint nodes $c_1,\dots,c_4$ and, since $z_1$ already appears bilinearly with $z_4,z_5,z_6$ (via $z_{12},z_{13},z_{14}$) but *not* with $z_2$ or $z_3$, variable nodes for $z_2,z_3$ only — wait, more precisely: $z_1$'s existing bilinear partners are itself, $z_4,z_5,z_6$; the *missing* pairs are $z_1z_2, z_1z_3$, so multiplying a constraint by $z_1$ only creates something new if that constraint mentions $z_2$ or $z_3$. Running `ValidReductionConstraints`: an augmenting path assigns $z_3 \to c_1$ immediately, then $z_2 \to c_2$ immediately. Constraint $c_3$ is adjacent only to $z_2$, already taken — the recursive search into $c_2$ finds no further slack, so the search fails, and $\{c_2, c_3\}$ is harvested into $\mathcal{L}_1$. Constraint $c_4$ is isolated in $\mathcal{G}_1$ (mentions neither $z_2$ nor $z_3$), so it's immediately its own trivial dilation, harvested too. Result: $\mathcal{L}_1 = \{c_2,c_3,c_4\}$ — multiplying these three constraints by $z_1$ introduces only **one** new bilinear term ($z_2 z_3$, via $c_3$), while eliminating three bilinear defining constraints. A clear net win.

**Multipliers $z_2$, $z_3$.** The book runs the identical procedure on graphs $\mathcal{G}_2$ (missing pairs $z_1z_2, z_2z_3$) and $\mathcal{G}_3$ (missing pairs $z_1z_3,z_2z_3,z_3^2$), with the matcher this time needing one genuine re-assignment step (an augmenting path of length 3, displacing an earlier assignment) before settling. The outcomes: $\mathcal{L}_2 = \{c_1,c_3,c_4\}$ (one new term), $\mathcal{L}_3 = \{c_1,c_2,c_4\}$ (two new terms, $z_1z_3$ and $z_2z_3$ — still a net gain, eliminating three for the price of two).

**Multipliers $z_4, z_5, z_6$.** These three variables already appear in *every* bilinear combination — there's no missing pair left to create. So $\mathcal{N}^V_l = \emptyset$ for $l=4,5,6$: the bipartite graphs have no variable nodes at all, every constraint node is trivially isolated, and `AugmentPath` returns `false` immediately for each. Result: $\mathcal{L}_4=\mathcal{L}_5=\mathcal{L}_6=\{c_1,c_2,c_3,c_4\}$ — multiply *all four* constraints by each of $z_4,z_5,z_6$, entirely for free, no new bilinear terms whatsoever.

**The harvest.** Altogether this produces **21 reduction constraints**. From multiplication by $z_1$, for instance:

$$
z_1 \times c_2 \Rightarrow 2z_7 - z_{25} + z_{12} + 3z_{14} - 2z_1 = 0
$$
$$
z_1 \times c_3 \Rightarrow z_{25} + 6z_{12} + 2z_{13} - 3z_{14} + z_1 = 0
$$
$$
z_1 \times c_4 \Rightarrow 2z_7 + z_{12} + 3z_{13} - z_1 = 0
$$

(here $z_{25} = z_2z_3$, the one genuinely new term $\mathcal{L}_1$'s multiplication introduces), and analogous triplets from $z_2,z_3$ (introducing $z_{26}=z_1z_3$ and $z_{27}=z_1z_2$... in the book's labeling the new terms $z_{25},z_{26},z_{27}$ correspond to the three previously-absent pairs $z_2z_3, z_1z_3, z_1z_2$), and four-constraint blocks from each of $z_4,z_5,z_6$ (12 more constraints, no new variables). In total: 21 new linear constraints, only **3** new bilinear terms — against **17** old bilinear defining constraints available to eliminate.

**Collapsing the redundancy via Gaussian elimination.** Writing the 21 reduction constraints as $Ru = 0$ and row-reducing (with pivoting) reveals a nonsingular upper-triangular block acting on the 17 original bilinear auxiliary variables $(z_7,\dots,z_{23})$, expressing all of them in terms of the base variables $z_1,\dots,z_6$ and the 3 new terms $z_{25},z_{26},z_{27}$. That means **all 17** of the original bilinear defining triplets in $B$ can be deleted, replaced by the 21 linear reduction constraints (equivalently, their row-reduced form) plus just **2** new bilinear triplets — the book's own count leaves $\{(25,2,3),(26,1,3)\}$ as the surviving irreducible bilinear pair after the third, $z_{27}=z_1z_2$, turns out to be expressible via the other two and the linear system. The reformulated problem has gone from 17 bilinear constraints to 2.

This is the payoff made concrete: an sBB solver building McCormick relaxations for 17 independent bilinear terms is working with a dramatically looser feasible region than one building them for 2 — even though, as a *feasible set*, the two problems are identical.

## 3.5 — Computational results: pooling and blending

The algorithm is validated on the **pooling and blending problem** — mixing raw material streams through intermediate "pools" to meet product specifications at minimum cost, a workhorse nonconvex NLP in the petrochemical industry, notorious for multiple local minima. Using a general blending formulation (flow variables $p_{il}$ stream-into-pool, $y_{lj}$ pool-to-product, quality variables $q_{lk}$), two of the model's own constraint sets already contain bilinear products of the form $q_{lk}\, y_{lj}$ and $q_{lk}\, p_{il}$, arising from quality-balance equations. When the standard-form reformulation is applied, these become defining constraints for auxiliary variables; the reduction-constraint algorithm then finds that multiplying the quality-balance linear constraints by the quality variables $q_{lk}$ recreates much of that same bilinear structure "linearly," letting many of the auxiliary bilinear terms collapse. As the book observes, this is really the same phenomenon as noticing that *distributing a product over a sum* — rewriting $\sum_l q_l\,x_l$ as one aggregated bilinear structure rather than $\sum_l$ many separate bilinear products — reduces term count; the difference is that here it's discovered automatically by a generic graph algorithm, not hand-crafted by a modeler who happens to notice the distributive structure.

On thirteen benchmark instances (Haverly, Foulds, Ben-Tal, and the author's own examples), the reduction constraints shrink both the raw problem size and, more importantly, the sBB node count needed to solve to global optimality. The headline comparison: the book's own bare-bones sBB implementation, *without* reduction constraints, needs up to 20,000 nodes on some instances (hitting the iteration cap without closing the gap); the *identical* solver, with reduction constraints switched on, closes several of those same instances in single-digit node counts, and becomes competitive with (though not uniformly better than) BARON, a much more mature production solver with sophisticated range-reduction and branching heuristics that this basic implementation lacks entirely. The conclusion the chapter draws — and which the thesis's final chapter reiterates as its central thesis — is that a sufficiently good *reformulation* can compensate for a mediocre *algorithm*, which is a stronger and more interesting claim than "this speeds things up."

## 3.6 — Generalizing: multiplying by all variables at once

The per-variable algorithm of §3.3 has a blind spot, and the book is upfront about it with a tiny counterexample: consider the single linear constraint

$$
x + y = 1
$$

together with the (implicit) bilinear terms it could create. Multiplying by $x$ gives $x^2 + xy = x$ — one new term, $xy$ (assuming $x^2$ already exists in the problem, $xy$ doesn't). Multiplying by $y$ gives $xy + y^2 = y$ — also one new term, $xy$. Run separately, *neither* multiplication looks beneficial under the per-variable dilation criterion (one new term for one constraint eliminated isn't a strict gain). But run *together*: the two multiplications jointly introduce only **one** new term total (it's the *same* $xy$ both times), while producing two independent linear constraints capable of eliminating two bilinear terms. The per-variable algorithm can't see this because it builds a separate graph, and asks "is this beneficial," independently for each multiplier — it never notices that two ostensibly-separate "one new term" multiplications actually share the same new term. Concretely, the book reports this reformulation takes the example from 255 sBB nodes down to 1.

The fix is architecturally satisfying: build **one unified bipartite graph** over all *(constraint, variable)* multiplication pairs simultaneously.

- **$\rho$-nodes**: one for every pair $(c, x)$ — "multiply constraint $c$ by variable $x$."
- **$\sigma$-nodes**: one for every bilinear term $z_i = z_jz_k$ that such a multiplication could newly create.
- **Edge** $(\rho_{c,x}, \sigma_{jk})$ exists iff multiplying $c$ by $x$ would create bilinear term $jk$.

Run the same augmenting-path / dilation-finding machinery over this graph. A dilation found here — a set of $\rho$-nodes whose combined $\sigma$-neighborhood is strictly smaller — identifies exactly the situation the small example exhibited: several different (constraint, variable) multiplications that, taken together, share new bilinear terms rather than each contributing a fresh one.

**The cost.** This generality isn't free. The per-variable algorithm ran on a graph with (at most) $m$ constraint nodes and $n$ variable nodes, giving worst-case complexity $O(mn)$ per multiplier and $O(mn^2)$ overall (across all $n$ candidate multipliers) — with average-case complexity closer to $O(m+n)$ per multiplier. The unified graph instead has up to $mn$ $\rho$-nodes and up to $\binom{n}{2}$-ish $\sigma$-nodes, with correspondingly larger worst-case complexity (though the book notes the *average*-case complexity ends up comparable) — and, more pressingly, the memory footprint of the unified graph (all $mn$ potential multiplications, materialized as nodes) can be prohibitive for genuinely large sparse problems, unless it's built lazily, "on-the-fly," from the problem data as the search proceeds, rather than fully materialized up front.

This is a textbook **precision/cost trade-off**: the per-variable algorithm is cheap but structurally blind to shared-savings across variables; the unified algorithm sees everything but costs more to build and store. The book's own recommendation — use the cheap version by default, invoke the unified version when the extra structure is suspected to matter (e.g. sparse, highly symmetric constraint systems like the blending problem's quality balances) — is a pragmatic middle path rather than a universal answer.

## 3.7 — Why this actually tightens the relaxation (and where it can fail)

It's worth being precise about *why* an operation that provably doesn't change the feasible region can nonetheless produce a strictly better relaxation — this is the crux the chapter is built around, restated cleanly in the concluding section. Take the reduction constraint block, written generically as (following the book's own final derivation)

$$
A_1 z^{(1)} + A_2 z^{(2)} = 0
$$

where $z^{(1)}$ are the bilinear terms *already present* in the NLP (so this block is truly redundant with respect to the *original* problem) and $z^{(2)}$ are the *new* terms the multiplication introduced. Gaussian-eliminate with row pivoting to isolate a nonsingular block against $z^{(2)}$:

$$
\begin{pmatrix} A_1' & A_2' \\ 0 & A_1'' \end{pmatrix} \begin{pmatrix} z^{(1)} \\ z^{(2)} \end{pmatrix} = 0.
$$

The bottom block row, $A_1'' z^{(1)} = 0$, involves *only* the original bilinear terms $z^{(1)}$ — no new variables at all. With respect to the **original** NLP this row is genuinely redundant (it's implied by the bilinear definitions themselves, per Theorem 3.2.1). But with respect to *any relaxation that doesn't enforce $z_i = z_jz_k$ exactly* — i.e. any McCormick-relaxed version — it is **not** implied. McCormick's four inequalities carve out a box around the hyperbolic paraboloid; the exact equation $z_i=z_jz_k$ is a strict subset of that box's boundary. The linear row $A_1''z^{(1)}=0$, sitting on top of the McCormick box, slices away the part of the box that the true (nonlinear) constraint would have excluded but the (linear) relaxation doesn't. That's the whole mechanism: *redundant relative to the exact problem, non-redundant relative to its relaxation.*

Combined with the elimination of bilinear defining constraints (so fewer McCormick boxes need to be built at all — each eliminated term is one less nonconvex constraint the sBB solver has to relax), the reformulation produces a relaxation that is simultaneously **tighter and smaller**. The book is explicit that this two-for-one property is what distinguishes reduction constraints from RLT, which only ever adds constraints (tightening, at the cost of size) without ever *removing* any of the nonlinear structure it was trying to help relax.

**The honest limitation.** The graph-theoretic detection relies on *structural* rank — whether a constraint mentions a variable at all, not the actual numerical value of its coefficient. A matrix can be structurally full-rank (every pivot the algorithm expects to find, based on the sparsity pattern, is "there" in principle) while being *numerically* singular or ill-conditioned for a particular coefficient assignment (e.g. two structurally-independent rows that happen, for this instance's specific numbers, to be nearly linearly dependent). In that case the dilation-finding algorithm can report a valid reduction constraint set that Gaussian elimination then fails to cleanly exploit, or exploits with numerical instability. This is a real caveat for automatic reformulation pipelines applied to arbitrary user models — it's a place where a purely symbolic/structural analysis and the numerical reality of the coefficients can quietly diverge.

## Where this leads

Structurally, this chapter is one of exactly two places (with Chapter 4's odd-degree monomial envelopes) where the thesis stops surveying the field and contributes something new. It feeds forward into Chapter 5's $\mathcal{OS}$ software framework as one of the *reformulation passes* a fully automatic sBB pipeline is expected to run before convexification — the thesis's Chapter 6 traces the whole idea back to an empirical observation Smith made about distillation-column models, and frames "automatic reformulation can substitute for algorithmic sophistication" as the thesis's unifying claim, with this chapter's pooling/blending results as its strongest piece of evidence.

For the standing project this vault is built around — a Rust-based dependent/refinement-type checker with an embedded constraint solver — the load-bearing transfer isn't the optimization content itself, it's the *shape* of the algorithm. This chapter is a clean, real-world instance of casting "which subset of my constraint system is redundant, and can I certify that automatically and cheaply?" as a **bipartite matching / dilation-finding problem**, with a failed-search's visited set doubling as a certificate. That's precisely the move your CSP kernel will want for two things: (1) detecting redundant refinement constraints before handing a verification condition to an SMT backend (fewer, tighter constraints mean a smaller search for the solver, exactly as fewer/tighter bilinear terms mean fewer sBB nodes here), and (2) reading a failed matching or unification attempt's "visited set" as an unsat core or minimal conflict explanation — the same certificate-from-failure pattern this chapter's `AugmentPath` exhibits when it returns `false`. Theorem 3.2.1's proof technique — isolate a nonsingular pivot block, show the residual is forced to zero — is also a useful template for *any* soundness argument in the checker that has the shape "this derived fact is implied by already-established facts, provable by exhibiting an invertible linear (or otherwise structured) witness."
