---
title: "Holant Problems"
book: "The Constraint Satisfaction Problem: Complexity and Approximability"
chapter: "Chapter 6 — On the Complexity of Holant Problems (Guo & Lu)"
pages: "159–177"
tags:
  - csp
  - counting-complexity
  - sat-smt-csp
  - holant
  - matching
  - holographic-algorithms
  - algebraic-graph-theory
---

# Holant Problems

[[book-guidelines|↩ Back to guidelines]]

## The gap CSP can't cross: why matching needs a bigger framework

Start with a question that sounds like it should have already been answered by ordinary CSP theory: how hard is it to count the perfect matchings of a graph? A perfect matching is a set of edges that touches every vertex exactly once — the classic "pair everyone up" problem. It looks CSP-shaped: variables are edges, each variable is Boolean (in the matching or not), and each vertex imposes a constraint ("exactly one of my incident edges is chosen"). And yet this innocent-looking problem sits at the center of one of the richest complexity landscapes in the field, one that ordinary CSP dichotomy machinery cannot even *state*, let alone prove:

- **Deciding** whether a perfect matching exists is in P — but not for a boring reason. It took Edmonds' blossom algorithm (1965), and that paper is literally where Edmonds proposed "P" as the definition of tractable computation. This is not a toy example; it's foundational to what "efficient" means in complexity theory.
- **Counting** perfect matchings exactly is #P-complete (Valiant, right after he *defined* #P). So the decision and counting versions of the *same* combinatorial object live on opposite sides of the tractability boundary — one of the cleanest illustrations that "does a solution exist" and "how many solutions are there" are genuinely different questions.
- Restrict the input graph to be **planar**, and counting becomes polynomial again — the Fisher–Kasteleyn–Temperley (FKT) algorithm, discovered in statistical mechanics for counting dimer coverings of a lattice.
- Computing the **parity** of the number of matchings is polynomial (via the identity permanent ≡ determinant mod 2).
- **Approximately** counting matchings has an FPRAS (Jerrum–Sinclair); approximately counting perfect matchings in bipartite graphs also has one (via the permanent); but an FPRAS for *general* perfect matchings is a long-standing open problem.

Matching is a recurring boundary case — P, #P-complete, P again (with a topological restriction), open (for approximation) — depending on exactly which question you ask. A complexity theory of "local constraint problems" that can't even express matching is missing the problem that most cleanly tests where the boundary of efficient computation actually lies.

**Why can't CSP express it?** The reason is structural, not just a missing example. In the standard CSP picture, an instance is a bipartite graph of *variables* and *constraints*: an edge connects a variable to every constraint that mentions it. Crucially, if a variable $x$ appears in three different constraints, all three constraints see the *same* value of $x$ — the variable-sharing is implemented, implicitly, by an equality relation of unbounded arity gluing every occurrence of $x$ together. CSP, in other words, is a framework that *always* has equality functions of every arity freely available for gluing.

The Holant framework's key move is to strip that assumption away and make equality just one function among many, available only if you explicitly put it in your constraint language. Formally:

> **CSP is the special case of Holant where equality relations of every arity are always assumed to be present in addition to whatever constraint set you name.**

Once equality is no longer free, you can build instances where a "variable" — now literally an *edge* of a graph, shared between exactly the two vertices it touches — is not forced into any consistency across more than two occurrences. This lets you encode matching directly: put the vertex set as the constraint set, the edge set as the variable set, and let each vertex demand "exactly one of my incident edges is set to 1." That's a Holant instance. It is not directly a CSP instance, because CSP's implicit equality-gluing has no way to represent "this variable participates in exactly two constraints and nothing forces broader consistency."

This is the first thing worth internalizing about Holant problems: **expressiveness is controlled by what's "free."** CSP is Holant-with-free-equality. The "conservative" variant of CSP (where all unary relations are free) corresponds to a similarly enriched Holant variant, $\mathrm{Holant}^*$. Every time you design a constraint-solving framework — including, if you're building one, a CSP kernel — the question "what gates/relations am I implicitly assuming are always available" is exactly this question, and it silently determines what problems your framework can and cannot state.

## Signature grids and the Holant sum

**Definition (signature grid).** A signature grid $\Omega = (G, F, \pi)$ consists of a graph $G = (V, E)$, a set of functions $F$, and an assignment $\pi: V \to F$ from vertices to functions, such that the arity of $\pi(v)$ equals the degree of $v$ for every vertex $v$. Each function $f \in F$ of arity $k$ is a map $[q]^k \to \mathbb{C}$ (the survey works over the complex numbers for generality, though any commutative ring would do). Write $f_v := \pi(v)$.

An **edge assignment** $\sigma: E \to [q]$ assigns a value in $[q]$ to every edge. Its weight is
$$
\prod_{v \in V} f_v\bigl(\sigma|_{E(v)}\bigr),
$$
where $E(v)$ is the set of edges incident to $v$, and $\sigma|_{E(v)}$ is the restriction of $\sigma$ to those edges (in the order the function's arity expects). The **Holant value** is the sum over all assignments:
$$
\mathrm{Holant}_\Omega = \sum_{\sigma} \prod_{v \in V} f_v\bigl(\sigma|_{E(v)}\bigr). \tag{1}
$$

The **Holant problem** $\mathrm{Holant}(F)$, for a fixed function set $F$, takes a signature grid $\Omega = (G, F, \pi)$ as input and asks for $\mathrm{Holant}_\Omega$. This is a counting problem by default; its *decision* variant just asks whether the sum is nonzero, i.e. whether some assignment satisfies every vertex constraint simultaneously. $\mathrm{Pl}\text{-}\mathrm{Holant}(F)$ restricts inputs to planar graphs. Note the *variables* here are the **edges** of $G$ — every variable is shared by exactly the (at most two, or fewer for pendant structure — in practice, exactly the vertices at its two endpoints) vertices it touches, and nothing forces further agreement. This is the structural difference from CSP made precise.

**Function vs. signature.** Since a function $f: [q]^k \to \mathbb{C}$ is really just a truth table, it's naturally a vector in $\mathbb{C}^{q^k}$, or equivalently a tensor in $(\mathbb{C}^q)^{\otimes k}$. The survey calls this the *signature* of $f$ when it wants to emphasize that it's an object ready to be pushed through a linear transformation — the two words "function" and "signature" are used interchangeably otherwise.

**Worked example — matching as a Holant problem.** Let $\mathrm{ExactOne}_k$ be the Boolean symmetric function of arity $k$ that returns $1$ if exactly one of its $k$ Boolean inputs is $1$, else $0$; let $\mathrm{EO}$ be the set of all $\mathrm{ExactOne}_k$ for every arity $k$. Put a signature grid on graph $G$ where every vertex $v$ gets $f_v = \mathrm{ExactOne}_{\deg(v)}$. An edge assignment $\sigma: E \to \{0,1\}$ has nonzero weight exactly when every vertex sees exactly one incident edge labeled $1$ — i.e. $\sigma^{-1}(1)$ is a perfect matching. Every such assignment contributes weight $1$. So $\mathrm{Holant}_\Omega = |\{\text{perfect matchings of } G\}|$, i.e.
$$
\mathrm{Holant}(\mathrm{EO}) \equiv \#\text{PerfectMatching}.
$$

## Symmetric signatures and degeneracy

Most of the deep results concern **symmetric functions**: $f$ is symmetric if permuting its inputs never changes the output. A symmetric Boolean function is completely determined by its value on each Hamming weight, so it can be written compactly as
$$
[f_0, f_1, \ldots, f_k],
$$
where $f_i$ is the value of $f$ on any input of Hamming weight $i$ (arity $k$, so $k+1$ entries). In this notation, the arity-$k$ equality function is $\mathord{=_k} = [1, 0, \ldots, 0, 1]$ (only all-0 or all-1 is accepted), the "must be 0" unary function is $\Delta_0 = [1, 0]$, and $\mathrm{ExactOne}_k = [0, 1, 0, \ldots, 0]$.

Two facts about signatures matter for everything downstream:

**1. Signatures are projective.** Scaling any signature by a nonzero constant $c$ leaves $\mathrm{Holant}(F)$'s complexity unchanged — $f$ and $cf$ are treated as the same object. This is why the theorems below talk about sets of signatures "up to a constant multiple." (Every vertex's contribution just gets scaled, and the whole sum scales by a fixed nonzero factor, which doesn't change hardness.)

**2. Degeneracy.** A signature is **degenerate** if it decomposes as a tensor product of unary signatures — i.e. it carries no genuinely $k$-ary information; it behaves as if each of its $k$ inputs were independently constrained. For symmetric Boolean signatures this has a clean form: $f$ is degenerate iff $f = \lambda[x,y]^{\otimes k}$ for some scalars $x, y, \lambda$, meaning $f_i = \lambda x^{k-i} y^i \binom{k}{i}/\binom{k}{i}$... more precisely $f = \lambda [x,y]^{\otimes k}$ expands, entrywise, to a geometric-progression-with-binomial-weight pattern (concretely: $f_i \propto x^{k-i}y^i$, no binomial factor — the tensor power of a length-2 vector, symmetrized only in the sense that all orderings of a fixed multiset of 0s/1s contribute the same *base* value $x^{k-i}y^i$, not a weighted sum). Think of degeneracy as the signature-theoretic analogue of a "separable" or "rank-1" tensor: a $k$-ary constraint that is secretly $k$ independent unary constraints glued together, contributing no real interaction between its inputs. Lemma 12 below shows that a Holant instance built only from degenerate and arity-$\le 2$ signatures is always tractable — genuine hardness needs signatures that are neither.

## Holographic reductions

This is the survey's central technical tool, and it's genuinely new relative to [[Counting-CSP|counting CSP]]: a way to relate two Holant problems by a **change of tensor basis** rather than by a combinatorial gadget construction.

**Making everything bipartite (the 2-stretch).** Any graph can be turned into a bipartite one while preserving the Holant value: replace every edge by a path of length two (subdividing it), and assign the new midpoint vertices the binary equality signature $\mathord{=_2} = [1,0,1]$ (this signature just forces its two edges to carry the same value, reproducing the original single-edge variable). This is called the **2-stretch**, and it turns $G$ into its edge–vertex incidence graph. Write $\mathrm{Holant}(F \mid G)$ for the Holant problem on a bipartite graph $H = (U, V, E)$ where $U$-vertices get signatures from $F$ (as *row vectors*, or *covariant* tensors) and $V$-vertices get signatures from $G$ (as *column vectors*, or *contravariant* tensors). Then
$$
\mathrm{Holant}(F) \equiv_T \mathrm{Holant}(\mathord{=_2} \mid F).
$$

**The linear-transformation trick.** For an invertible $2\times 2$ matrix $T$ and signature set $F$, define
$$
TF = \{\, g \mid \exists f \in F \text{ of arity } n,\ g = T^{\otimes n} f \,\},
$$
(viewing $f, g$ as column vectors), and similarly $FT$ for row vectors. Given a bipartite signature grid for $\mathrm{Holant}(F \mid G)$, replace every $F$-signature by its image under $T$ on the row side and every $G$-signature by its image under $T^{-1}$ on the column side. This produces a *different* signature grid, but:

> **Theorem (Valiant's Holant Theorem).** For any invertible $T \in \mathbb{C}^{2\times 2}$, $\mathrm{Holant}(\Omega; F \mid G) = \mathrm{Holant}(\Omega'; FT \mid T^{-1}G)$.

This is remarkable: it says the *value* of the sum is invariant under simultaneously reparametrizing the two sides of the bipartite grid by mutually-inverse linear maps, even though the individual per-vertex functions can look completely different before and after. It's the tensor-network analogue of a change of basis — nothing about the underlying "physics" (the value being computed) changes, but the local descriptions do.

When $T$ is **orthogonal** ($T^T T = I$), it additionally preserves the binary equality signature, so it can be applied even in the non-bipartite (2-stretch-free) setting:
$$
\mathrm{Holant}(\Omega; F) = \mathrm{Holant}(\Omega'; TF) \quad \text{when } T \in O_2(\mathbb{C}).
$$

**The canonical example.** The matrix $Z = \tfrac{1}{\sqrt2}\begin{pmatrix}1 & 1\\ i & -i\end{pmatrix}$ transforms $\mathord{=_2} = [1,0,1]$ into $[0,1,0]$, the *disequality* signature $\mathord{\neq_2}$. So a holographic reduction via $Z$ literally converts "these two edges must agree" into "these two edges must differ" — a nontrivial statement, since it's not something you could achieve by any local, combinatorial relabeling; it only works because of how $Z$ acts on the whole tensor.

**$C$-transformability.** Generalizing this, say $F$ is **$C$-transformable** for a signature family $C$ if there is a $T \in GL_2(\mathbb{C})$ with $[1,0,1]T^{\otimes 2} \in C$ and $F \subseteq TC$. Then $\mathrm{Holant}(F) \le_T \mathrm{Holant}(C)$ and $\mathrm{Pl}\text{-}\mathrm{Holant}(F) \le_T \mathrm{Pl}\text{-}\mathrm{Holant}(C)$: if the "reference" family $C$ is tractable, so is every $C$-transformable $F$. This is the mechanism by which all five of the "tractable families" in the dichotomy theorem below (§4) actually get *used*: each is defined as a base family, and a signature set is tractable if it's a $T$-image of that base family for some invertible $T$.

**Reconstructing #CSP inside Holant.** Counting CSP falls out as the special case where equality functions of every arity are always present:
$$
\#\mathrm{CSP}(F) \equiv_T \mathrm{Holant}(\mathrm{EQ} \mid F), \qquad \mathrm{EQ} = \{\mathord{=_1}, \mathord{=_2}, \mathord{=_3}, \ldots\}.
$$
Equivalently, $\#\mathrm{CSP}(F) \equiv_T \mathrm{Holant}(\mathrm{EQ} \cup F)$ — one direction is immediate (a #CSP instance is already a valid, equality-augmented Holant instance); the other direction takes a general signature grid, 2-stretches every edge (introducing an $\mathord{=_2}$ midpoint per edge), and then *contracts* every maximal connected cluster of touching equality-signatures back into one large equality node — recovering the variable/constraint bipartite structure that #CSP expects.

## Graph matching as complexity landmark

Matching isn't just the motivating anecdote; it's the load-bearing example inside every one of the three main results (decision, exact counting, approximate counting).

**Decision.** A relation $R \subseteq \{0,1\}^d$ is a **$\Delta$-matroid** if for any two accepted vectors $x, y \in R$ differing in some coordinate $i$, either flipping just coordinate $i$ of $x$ ($x \oplus e_i$) stays in $R$, or there's some other coordinate $j$ where $x, y$ also differ such that flipping *both* $i$ and $j$ ($x \oplus e_i \oplus e_j$) stays in $R$. This is a combinatorial "local exchangeability" property — matroids generalized to allow sets that aren't all the same size. The $\mathrm{ExactOne}_k$ relation used to encode matching is a $\Delta$-matroid (a routine check), but the family is strictly larger — some $\Delta$-matroid functions cannot be built by composing $\mathrm{ExactOne}_k$'s at all.

Feder's hardness theorem says $\Delta$-matroid-ness is *exactly* the obstruction: unless every relation in $F$ is a $\Delta$-matroid, decision $\mathrm{Holant}(F)$ has the same complexity as $\mathrm{CSP}(F)$. Combined with Schaefer's classical CSP dichotomy, this gives:

> **Theorem 8.** Every decision $\mathrm{Holant}(F)$ falls into one of three cases: (1) every function in $F$ is a $\Delta$-matroid; (2) $F$ is tractable by Schaefer's CSP dichotomy (and hence $\mathrm{Holant}(F)$ is too); (3) otherwise, $\mathrm{Holant}(F)$ is NP-complete.

Case (1) — the whole class of $\Delta$-matroid decision problems — is the genuinely open, Holant-specific frontier; it's not covered by CSP theory at all, and matching is its flagship member. Two partial results are known: symmetric relations $[f_0,\ldots,f_k]$ where the largest "gap" (a run of consecutive 0s strictly between two 1s) has length $\le 1$ are tractable (Theorem 9); and *even* $\Delta$-matroids — where every accepted vector has the same parity of Hamming weight — are tractable (Theorem 10, Kazda–Kolmogorov–Rolínek), and this in turn gives a complete dichotomy for Boolean CSP restricted to planar graphs.

**Exact counting.** Matchgates, introduced by Valiant, are exactly the signatures whose Holant problems reduce to a weighted sum of perfect matchings — tractable on planar graphs via Kasteleyn's algorithm (independently found by Temperley–Fisher; the "FKT" algorithm). Symmetric matchgate signatures have a rigid, explicit shape: nonzero only on entries of a single Hamming-weight parity, forming a geometric progression $[a^n, 0, a^{n-1}b, 0, \ldots, 0, b^n]$ (up to which parity and length parameters). This rigidity is *why* matchgates admit an efficient algorithm at all — the signature carries essentially one real degree of freedom (the ratio $a{:}b$) per vertex, which is exactly what a weighted-matching count can track.

**Approximate counting.** Jerrum–Sinclair's FPRAS for counting matchings is the founding example of the "canonical paths" technique for proving a Markov chain mixes rapidly: the symmetric difference of two matchings decomposes into disjoint paths and cycles, and you can "(un)wind" along that decomposition to build low-congestion paths between any two states. This decomposition idea was later generalized into **windability** (§ below), of which the matching FPRAS becomes one instance among several.

Matching is thus the one example that appears, in a structurally different guise, at every layer of the theory — proof that the Holant framework's added generality (edges as variables, no forced equality) is not academic: it is precisely the generality needed to see the phenomenon that motivated the whole survey.

## Exact counting: the tractable families

Section 4 is the survey's center of gravity — for symmetric functions over the Boolean domain with complex weights, the exact-counting complexity of $\mathrm{Holant}(F)$ is now *completely classified*:

> **Theorem 11.** For $F$ a set of Boolean symmetric functions with complex weights, $\mathrm{Holant}(F)$ is either computable in polynomial time or is #P-hard. The same dichotomy holds for $\mathrm{Pl}\text{-}\mathrm{Holant}(F)$, though the tractable criterion differs.

To state the *explicit* criterion (not just its existence — the point of Ladner's theorem is that dichotomy is non-trivial to prove), the survey builds up five tractable families, each defined as a base set that gets extended to everything $C$-transformable to it (§ above).

**1. Low arity (Lemma 12).** If every non-degenerate signature in $F$ has arity $\le 2$, $\mathrm{Holant}(F)$ is tractable. The algorithm: replace degenerate signatures with unary ones, and any instance decomposes into disjoint paths and cycles once you remove the tractable "connectors." Represent a binary signature $f$ as a $2\times 2$ matrix $M_f = \begin{pmatrix}f(00) & f(01)\\ f(10) & f(11)\end{pmatrix}$; chaining two binary signatures along an edge multiplies their matrices ($M_h = M_f M_g$). A path's Holant value is $v M_f u^T$ for endpoint unary signatures $v, u$; a cycle's is $\mathrm{tr}(M_f)$. This is genuinely just linear algebra — matrix multiplication along a path, trace for a cycle.

**2. Affine signatures $\mathcal{A}$ (Definition 13).** A $k$-ary function is affine if it has the form $\lambda \cdot \chi_{Ax=0} \cdot i^{\sum_j \langle v_j, x\rangle}$ — a $0/1$ indicator of an $\mathbb{F}_2$-affine subspace, times a complex root-of-unity phase determined by a quadratic form over $\mathbb{F}_2$. The non-degenerate symmetric members of $\mathcal{A}$ split into three explicit families ($\mathcal{F}_1, \mathcal{F}_2, \mathcal{F}_3$) built from $[1,0]^{\otimes k} \pm i^r[0,1]^{\otimes k}$-style patterns — ten concrete signature shapes in total (Table 1 in the source), covering things like alternating patterns $[1,0,1,0,\ldots]$ and their $i$-phased variants. Affine signatures underlie linear-algebra-flavored tractability — they're the Holant analogue of the "affine" case in the Creignou–Hermann #CSP dichotomy (Chapter 8 of this book).

**3. Product-type signatures $\mathcal{P}$ (Definition 15).** These are (tensor-closure of) products of unary functions, the equality signature $[1,0,1]$, and the disequality signature $[0,1,0]$. Any symmetric member of $\mathcal{P}$ is either degenerate, the disequality signature, or of the very restricted form $[a, 0, \ldots, 0, b]$ — nonzero only at the two extreme Hamming weights. Tractability comes from a straightforward propagation algorithm: values flow deterministically once you know a single edge's assignment.

**4. Vanishing signatures $\mathcal{V}$ (Definitions 17–19).** A signature set is **vanishing** if its Holant value is *always* zero, on every instance — trivially tractable (the algorithm is "output 0"). What's non-trivial is characterizing which signatures have this property, and — more usefully — that vanishing signatures can be *combined* with certain other tractable pieces and remain tractable. The tool is **vanishing degree**: $f$ has positive vanishing degree $k$ if it can be written as a symmetrization $\mathrm{Sym}^k_n([1,i]; v_1,\ldots,v_{n-k})$ — informally, $f$ "contains" $k$ copies of the special unary signature $[1,i]$ symmetrized in with $n-k$ other unary signatures. (Negative vanishing degree uses $[1,-i]$ instead.) Theorem 20 shows a symmetric family $F$ is vanishing iff every member has "enough" vanishing degree relative to its arity ($2\,\mathrm{vd}^\sigma(f) > \mathrm{arity}(f)$ for a consistent sign $\sigma$). Lemma 21 and 22 then extend tractability to vanishing signatures mixed with binary signatures, or to "highly vanishing" ones mixed freely with *all* unary signatures.

**5. Matchgate signatures $\mathcal{M}$ (Definitions/Propositions 24–25).** As discussed above: the family reducible to weighted perfect-matching counting, tractable on **planar** graphs via FKT. Every symmetric matchgate signature is a support-restricted geometric progression (nonzero on only one Hamming-weight parity), which is also why it decomposes cleanly as $[a,b]^{\otimes n} \pm [a,-b]^{\otimes n}$ (up to scalar) or a pure "single 1" symmetrization $\lambda\,\mathrm{Sym}^{n-1}_n([1,0];[0,1])$.

**6. An extra planar-only case (Lemma 26).** A late addition (Cai–Fu–Guo–Williams, 2015) needed to *complete* the planar dichotomy: a family built from $Z$-transformed product-type signatures combined with $Z$-transformed (inverse) ExactOne signatures, tractable via a recursive edge-forcing procedure that exploits planar graphs' bounded average degree (never above 6) to always find a forced or unsatisfiable edge.

**The full statement.**

> **Theorem 27.** For $F$ any set of symmetric, complex-weighted Boolean functions, $\mathrm{Pl}\text{-}\mathrm{Holant}(F)$ is #P-hard *unless* $F$ satisfies one of: (1) all non-degenerate signatures have arity $\le 2$; (2) $F$ is $\mathcal{A}$-transformable; (3) $F$ is $\mathcal{P}$-transformable; (4) $F \subseteq \mathcal{V}^\sigma \cup \{f \mid \mathrm{vd}^\sigma(f) \ge 1,\ \mathrm{arity}(f)=2\}$ for some sign $\sigma$; (5) every non-degenerate $f \in F$ has $\mathrm{arity}(f) - \mathrm{vd}^\sigma(f) \le 1$ for some $\sigma$; (6) $F$ is $\mathcal{M}$-transformable; (7) the $Z$-transformed extra planar case of Lemma 26. In every exceptional case, $\mathrm{Pl}\text{-}\mathrm{Holant}(F)$ is polynomial time. Conditions (1)–(5) alone (no planarity needed) make plain $\mathrm{Holant}(F)$ tractable too; otherwise $\mathrm{Holant}(F)$ is #P-hard.

Notice the shape: conditions (1)–(5) are the **planarity-independent** tractable core — anything the classification calls tractable without needing planarity falls into one of these. Conditions (6) and (7) are **planar-only**: matchgates and the extra Lemma-26 case become tractable *because* the input graph is planar (FKT genuinely needs planarity — the same matchgate signatures are #P-hard on general graphs, which is the formal version of "counting perfect matchings is #P-complete on general graphs but P on planar graphs" from the introduction).

**Beyond symmetric Boolean functions.** The fully general case (arbitrary, not-necessarily-symmetric functions, arbitrary domain size) is still open. What's known: for $\mathrm{Holant}^*(F)$ (all unary functions freely available — the "conservative" analogue), a complete Boolean-domain dichotomy exists (Theorem 28), built from four tractable base families ($\mathcal{T}$ = all unary/binary functions; $\mathcal{E}$ = functions supported on a single pair of complementary inputs, a generalized equality; $\mathcal{M}$ = functions supported on Hamming weight $\le 1$, a generalized matching; and their $Z$-transforms). A single-ternary-function dichotomy is known for domain size 3, and a dichotomy for counting $k$-edge-colorings of $d$-regular (planar) multigraphs is known for all $(k,d)$ — with the striking clean statement that $k$-edge-coloring counting is #P-hard on planar $d$-regular graphs whenever $k \ge d \ge 3$ (Theorem 29).

## Planar Holant problems

Planarity is not a footnote here — it is one of the two axes (alongside "what function family") along which the whole theory is organized, and it earns that status honestly: the FKT algorithm is *the* reason planar counting problems can be dramatically easier than their general-graph counterparts, and it's also the computational engine underneath Valiant's holographic algorithms (the technique this whole survey exists to systematize). Concretely:

- Perfect-matching counting: #P-complete in general, polynomial-time on planar graphs (FKT).
- The Holant dichotomy itself bifurcates: the general-graph tractable core is conditions (1)–(5) of Theorem 27; the planar-graph tractable set is strictly larger, adding matchgates (6) and the Lemma-26 family (7).
- Even the *decision* version sees a planarity-specific result: even $\Delta$-matroids give a complete dichotomy specifically for planar Boolean CSP (Theorem 10's corollary), a result that doesn't have — and may not have — a clean general-graph analogue, since general $\Delta$-matroid decision Holant is still open.

The conceptual reason planarity helps so much: a planar graph's genus-zero embedding lets you apply Kasteleyn's trick of assigning signs (an orientation making every face have an odd number of clockwise-oriented edges) so that the *signed* sum over all perfect matchings collapses into a single Pfaffian/determinant computation — turning an exponential combinatorial sum into one polynomial-time linear-algebra operation. Non-planar graphs generally have no such consistent global sign assignment, which is exactly why the same counting problem becomes #P-hard once you drop the planarity restriction.

## Approximate counting

For approximation, precision is relaxed: an **FPTAS** computes, in time polynomial in $n$ and $1/\varepsilon$, some $\hat Z$ with $(1-\varepsilon)Z \le \hat Z \le (1+\varepsilon)Z$; an **FPRAS** is the randomized version (correct with high probability, using random bits). Bounding a Holant instance's degree to exactly 2 (which is what a Holant instance *is*, relative to CSP) turns out to *not* behave like other bounded-degree CSP variants — degree bound $> 2$ has a partial classification, but degree exactly 2 (i.e. genuine Holant) is wide open and appears to contain many more tractable cases than the bounded-degree CSP literature would predict. Known tractable cases include counting matchings (with weights), parity-function partition functions (which subsume the ferromagnetic Ising model), bounded-occurrence SAT, and Not-All-Equal constraints.

**Windability.** The unifying technique generalizing Jerrum–Sinclair's matching canonical-paths argument is **windability** (McQuillan; developed further by Huang–Lu–Zhang). For a configuration $x \in \{0,1\}^J$, let $M_x$ be the set of ways to partition $\{i : x_i = 1\}$ into pairs plus at most one leftover singleton. A function $f: \{0,1\}^J \to \mathbb{R}_{\ge 0}$ is **windable** if there exist nonnegative "weights" $B(x,y,M)$ for $x, y \in \{0,1\}^J$ and $M \in M_{x \oplus y}$ such that:

1. $f(x)f(y) = \sum_{M \in M_{x\oplus y}} B(x,y,M)$ for all $x, y$, and
2. $B(x,y,M) = B(x \oplus S, y \oplus S, M)$ for every $S \in M$, $M \in M_{x\oplus y}$.

This is the abstract shape of "you can decompose the symmetric difference between any two configurations into disjoint pairs/singleton, and consistently reweight along that decomposition" — exactly what Jerrum–Sinclair's path-cycle unwinding for matchings does concretely. The payoff: a rapidly-mixing Markov chain that moves between *perfect* edge-assignments (every incident half-edge pair agrees) and *near-perfect* ones (exactly two inconsistencies). It's rapid mixing alone that isn't quite enough, though — you additionally need the ratio $Z_2/Z_0$ (near-perfect Holant mass over perfect Holant mass) to be polynomially bounded, or the chain spends too much time in the enlarged, non-perfect state space to be useful:

> **Theorem 31.** There is an FPRAS for $\mathrm{Holant}(F)$ whenever every function in $F$ is windable and $Z_2/Z_0$ is polynomially bounded.

Both the matching FPRAS and the Ising-model FPRAS are special cases of this one theorem. A full characterization of which symmetric functions are windable (by solving a system of linear equations) has since unlocked new results: FPRASes for counting **$b$-matchings** (every vertex touches at most $b$ edges) for $b \le 7$, and for counting **$b$-edge-covers** (every vertex touches at least $b$ edges) for $b \le 2$ — both open for larger $b$.

**Fibonacci functions and correlation decay.** A different, deterministic route to approximation is **correlation decay**, illustrated via Fibonacci functions: a symmetric signature $[f_0,\ldots,f_k]$ is a Fibonacci function if $f_i = c f_{i-1} + f_{i-2}$ for a fixed constant $c$ (the parity function is the $c=0$ case). If all vertex functions share the same $c$ and edge weights are trivial, exact counting is already polynomial (product-type tractability); allowing per-edge or per-vertex weight variation makes exact counting #P-hard, which is what makes the *approximate* setting interesting, since it also connects to ferromagnetic 2-spin systems from statistical physics. The known FPTASes (Lu–Wang–Zhang) hold for suitably-bounded Fibonacci-function families combined with edge weights kept within a computable range (Theorems 32–33) — the mechanism being a spatial-mixing / correlation-decay argument rather than a Markov chain.

## Code grounding

The Holant sum (equation 1) is, at its core, a tensor-network contraction: every vertex is a local tensor, every edge is a shared index, and the whole-graph value is what you get by contracting every shared index. This maps naturally onto Rust, and connects directly to how you'd represent a constraint-propagation network for a CSP solver kernel.

**Brute-force Holant evaluator (Rust).** For small instances, this is a direct transcription of equation (1) — enumerate every edge assignment, multiply the local weights, sum:

```rust
use std::collections::HashMap;

/// A symmetric Boolean signature stored by Hamming weight: entry i is f([weight i]).
#[derive(Clone)]
struct Signature {
    values: Vec<f64>, // length = arity + 1
}

impl Signature {
    fn arity(&self) -> usize {
        self.values.len() - 1
    }
    fn eval(&self, assignment: &[u8]) -> f64 {
        let weight: usize = assignment.iter().map(|&b| b as usize).sum();
        self.values[weight]
    }
}

/// A signature grid: vertices carry signatures, edges are the shared variables.
struct SignatureGrid {
    num_edges: usize,
    // For each vertex: (signature, indices of its incident edges, in arity order)
    vertices: Vec<(Signature, Vec<usize>)>,
}

impl SignatureGrid {
    /// Direct evaluation of the Holant sum -- exponential, but a ground-truth
    /// reference and a faithful reading of equation (1).
    fn holant(&self) -> f64 {
        let mut total = 0.0;
        let mut assignment = vec![0u8; self.num_edges];
        let bound = 1u64 << self.num_edges;
        for mask in 0..bound {
            for e in 0..self.num_edges {
                assignment[e] = ((mask >> e) & 1) as u8;
            }
            let mut weight = 1.0;
            for (sig, incident) in &self.vertices {
                let local: Vec<u8> = incident.iter().map(|&e| assignment[e]).collect();
                weight *= sig.eval(&local);
                if weight == 0.0 {
                    break; // early exit: zero-weight vertex kills the whole term
                }
            }
            total += weight;
        }
        total
    }
}

fn exact_one(k: usize) -> Signature {
    // [0, 1, 0, ..., 0] with k+1 entries
    let mut values = vec![0.0; k + 1];
    values[1] = 1.0;
    Signature { values }
}

fn main() {
    // Triangle graph, every vertex demands ExactOne of its 2 incident edges:
    // this should count perfect matchings of a 3-cycle, which has none (odd cycle).
    let grid = SignatureGrid {
        num_edges: 3,
        vertices: vec![
            (exact_one(2), vec![0, 1]),
            (exact_one(2), vec![1, 2]),
            (exact_one(2), vec![2, 0]),
        ],
    };
    assert_eq!(grid.holant(), 0.0);

    // 4-cycle: two perfect matchings (opposite-edge pairs).
    let grid4 = SignatureGrid {
        num_edges: 4,
        vertices: vec![
            (exact_one(2), vec![0, 1]),
            (exact_one(2), vec![1, 2]),
            (exact_one(2), vec![2, 3]),
            (exact_one(2), vec![3, 0]),
        ],
    };
    assert_eq!(grid4.holant(), 2.0);
}
```

This brute-force evaluator is exponential in edge count — exactly why the survey's whole apparatus (tractable families, holographic reductions, $2\times2$ matrix chaining for arity-$\le 2$ signatures) exists: it's a catalogue of *structural* reasons a signature grid's contraction can be computed without ever materializing the exponential sum. The `Mf` matrix trick from Lemma 12 is a direct generalization: for a path of binary signatures, you're just computing a matrix product; a Rust implementation of that path/cycle decomposition (walk the graph, multiply $2\times2$ matrices, take a trace on cycles) replaces the `1 << num_edges` loop above with $O(|E|)$ matrix multiplications for that structural case — worth building explicitly if your CSP kernel ever needs to special-case degree-2 (Holant-shaped) subproblems the way real solvers special-case unit propagation.

**Degeneracy / symmetric-signature check (Python).** A quick illustrative script for recognizing the "low-information" signatures that Lemma 12 exploits — useful as a sanity check before running anything expensive:

```python
def is_degenerate_symmetric(values, tol=1e-9):
    """Check whether a symmetric Boolean signature [f0, ..., fk]
    equals lambda * [x, y]^{tensor k} for some x, y, lambda.
    Equivalent to: f_i / f_{i-1} is constant (a fixed ratio y/x) wherever defined."""
    nonzero = [(i, v) for i, v in enumerate(values) if abs(v) > tol]
    if len(nonzero) <= 1:
        return True  # trivially degenerate (rank <= 1 support)
    ratios = []
    for (i1, v1), (i2, v2) in zip(nonzero, nonzero[1:]):
        if i2 != i1 + 1:
            return False  # a "gap" of consecutive zeros between two nonzero
                            # entries generally breaks the pure geometric pattern
        ratios.append(v2 / v1)
    return all(abs(r - ratios[0]) < tol for r in ratios)

# ExactOne_2 = [0, 1, 0]: a single nonzero entry -> degenerate.
assert is_degenerate_symmetric([0, 1, 0])
# Equality =_2 = [1, 0, 1]: two nonzero entries separated by a zero -> not degenerate.
assert not is_degenerate_symmetric([1, 0, 1])
# [1, 2, 4]: geometric progression with ratio 2 -> degenerate ([1,2]^{⊗2}).
assert is_degenerate_symmetric([1, 2, 4])
```

A note on **Lean**: this chapter is a counting-complexity survey grounded in tensor algebra and combinatorics, not in judgment forms, type checking, or proof terms — there is no natural "this is exactly what `isDefEq` does" correspondence to draw here the way there would be for a chapter on unification or definitional equality. The one place a proof assistant's discipline is genuinely relevant is *verifying the matchgate identities* (Proposition 24/25's classification) as algebraic invariants — but that would be a strained example manufactured for the sake of including Lean, not something the source material calls for. Per the workbench style guidance, it's better to skip that than force it.

## Where this leads

**Structurally**, this chapter sits downstream of Chapter 4 ([[Hybrid-Tractability|Hybrid Tractability]]), which already introduced "edge CSPs" (every variable in exactly two constraints) as one of its five hybrid-tractability mechanisms and pointed out that these coincide with Holant problems, characterized by (even) $\Delta$-matroids — this chapter is where that boundary case gets its full treatment. It sits alongside Chapter 8 (Counting CSP), which explicitly *excludes* Holant and treats it as "a separate, more general 'read-twice' framework" — the two chapters partition the counting-complexity landscape between them, with Holant covering exactly the phenomena (matching, the FKT algorithm, holographic reductions) that plain #CSP's equality-gluing can't reach.

**For the CSP-kernel and abstract-interpretation project this workbench is building toward**, three things from this chapter are worth carrying forward (tagged `sat-smt-csp`, per the Focus Areas):

- **"What's free" as a design decision.** The single cleanest idea in this chapter — CSP is Holant with unlimited-arity equality assumed free — is a template for auditing any constraint-solving kernel's design: which relations does your solver implicitly assume are always available for variable-sharing (equality, disequality, some notion of "same abstract value")? Answering that precisely tells you what your kernel's expressive ceiling is, the same way it tells you Holant's relative to CSP's.
- **Degree-bounded constraint graphs as a genuinely different regime.** The chapter's repeated observation that Holant (degree exactly 2) behaves *unlike* other bounded-degree CSP variants — with more tractable structure, not less — is a concrete instance of "structural restriction" (per Chapter 4's framing) interacting with algebraic tractability in a way that isn't predictable from either alone. If your CSP kernel ever needs to special-case low-arity or low-occurrence subproblems (a natural thing to do for efficiency, e.g. during constraint propagation on a lattice/DFA-shaped domain), the matrix-chaining algorithm for arity-$\le 2$ Holant instances (Lemma 12) is a genuine, ready-to-borrow technique, not just an analogy.
- **Holographic reductions as a lesson in changing representation, not structure.** The $T^{\otimes n}$ linear-transformation trick — solving a hard-looking instance by first reparametrizing every local constraint via a fixed invertible matrix, then recognizing the transformed instance as tractable — is conceptually close to what abstraction (Galois connections, choosing a good abstract domain) is doing in the static-analysis side of this project: the *problem* doesn't change, but a well-chosen change of representation can turn an intractable-looking computation into a tractable one. Holographic reductions are the sharpest, most explicit version of "the right change of basis makes hardness disappear" this workbench has encountered so far, and it's worth keeping as a mental template even outside counting complexity.
