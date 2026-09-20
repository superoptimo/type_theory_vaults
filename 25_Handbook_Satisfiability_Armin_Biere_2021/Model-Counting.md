---
title: Model Counting
source: "Handbook of Satisfiability (2nd ed.), Biere, Heule, van Maaren, Walsh (eds.), 2021"
chapters: "Chapter 25 (Model Counting, pp. 993–1011); Chapter 26 (Approximate Model Counting, pp. 1015–1039)"
tags: [sat, model-counting, sharp-p, complexity-theory, knowledge-compilation, universal-hashing, toda-theorem]
---

# Model Counting

[[book-guidelines|↩ Back to guidelines]]

## Why counting is a different problem than deciding

A SAT solver answers one bit of information: does *some* satisfying assignment exist? For an enormous range of applications, that bit is not enough. If you're doing Bayesian network inference, you don't want to know whether a joint configuration consistent with your evidence exists — you want the *proportion* of the configuration space consistent with it, because that proportion literally *is* the posterior probability. If you're sizing a combinatorial design space, "at least one design exists" tells you nothing about how constrained the design actually is. If you're doing reliability estimation on a network, you want the fraction of edge-failure patterns under which two nodes stay connected, not just whether a single such pattern exists.

This generalization of SAT is **propositional model counting**, or **"#SAT"** (pronounced "sharp-SAT" or "number-SAT"): given a propositional formula $F$, compute $\#F$, the number of satisfying truth assignments. It is easy to *state* as "just SAT, but count all the witnesses instead of stopping at the first one" — and that phrasing is exactly why it's tempting to assume it inherits SAT's engineering maturity for free. It doesn't. The chapter's opening numbers make the scalability gap concrete: SAT solvers routinely handle formulas with hundreds of thousands of variables; exact model counters top out around a couple hundred; even approximate counters only reach into the low thousands. Something about the counting version of the problem is fundamentally more resistant to the heuristics that made SAT solving practical — and the theory tells you exactly what.

**What breaks without the distinction:** every heuristic that makes a modern CDCL SAT solver fast is built around *narrowing the search as fast as possible toward one solution* — pick the variable most likely to cause propagation, prune branches that can't possibly lead anywhere, throw away information about regions of the search space you've already ruled out except as conflict clauses. A model counter cannot behave this way: it is contractually obligated to account for *every* satisfying assignment, which means it must remain aware of the entire solution space even in regions a SAT heuristic would happily never visit. This is the central engineering tension of the whole topic, and it shapes every algorithm below.

## The complexity class "#P" and counting reductions

### From decision to counting

Take any problem in NP, phrased as a polynomial-time-decidable, polynomially-balanced relation $Q(x,y)$ (decidable in poly time, and any witness $y$ has length polynomial in $|x|$). The decision version asks: *does there exist* $y$ with $Q(x,y)$? The **counting version** asks: *how many* $y$ satisfy $Q(x,y)$? The complexity class **"#P"** ("number P" or "sharp P") is the set of all such counting problems. If $Q(x,y)$ = "$y$ is a satisfying assignment for propositional formula $x$," the counting problem for $Q$ is "#SAT". If $Q(x,y)$ = "$y$ is a clique in graph $x$," you get "#CLIQUE". Note "#P" is a class of *function* problems — the answer is a number, not a yes/no — sitting alongside, but structurally different from, the decision classes P, NP, PSPACE you already know from SAT complexity.

### Counting reductions, and why they're comparatively easy to build

Completeness for "#P" needs a different reduction machinery than NP-completeness does, because the object being preserved is no longer "solvable at all" but "solvable to the same *count*." A **counting reduction** from problem $B$ to problem $A$ is a pair of polynomial-time functions $(R, S)$: $R$ maps an instance $z$ of $B$ to an instance $R(z)$ of $A$, and $S$ recovers the count for $z$ from the count of $R(z)$ — i.e., $\#B(z) = S(\#A(R(z)))$. Given a counting algorithm for $A$, this pair converts it into one for $B$ at only polynomial overhead. This is strictly more general than a standard decision reduction, which only needs to preserve the *existence* of a witness.

The reason "#P"-completeness turns out to be easy to establish in practice is that many of the standard NP-completeness reductions are already **parsimonious** — they preserve the *number* of solutions exactly, not merely whether one exists. A parsimonious reduction gives you $R$ for free with $S$ as the trivial identity. In particular, a parsimonious version of the Cook–Levin construction shows "#SAT" is "#P"-complete, and the counting variants of essentially all of Garey and Johnson's classic NP-complete problems are known to be "#P"-complete too — but note carefully: *NP-completeness of the decision problem never automatically implies "#P"-completeness of its counting variant*. You must exhibit an actual counting reduction each time.

### Valiant's theorem: counting is hard even when deciding is easy

Here is the section's most conceptually loaded result. Valiant (1979) proved that the *counting version of a polynomial-time-solvable problem* can still be "#P"-complete — a fact with no decision-world analogue, since in the decision world "solvable in P" and "hard" are simply contradictory. The concrete example: computing the permanent of a 0-1 matrix, `PERM`, is equivalent to counting the perfect matchings of a bipartite graph, `#BIP-MATCHING`. Valiant showed this is "#P"-complete. Yet *finding a single* perfect matching is solvable in deterministic polynomial time via network flow. The counting variants of 2-SAT, Horn-SAT, DNF-SAT, and bipartite matching — all trivially in P as decision problems — are all "#P"-complete as counting problems.

Why is this surprising, and what does it reveal? It tells you that "finding a witness" and "counting all witnesses" are, as computational tasks, only loosely coupled. A polynomial algorithm for one gives you *nothing* constructive toward the other in general. Concretely: if you could reduce "#SAT" to `#BIP-MATCHING` *parsimoniously*, you'd be able to solve SAT in polynomial time (build the bipartite graph, check if a perfect matching exists via flow) — which would mean P=NP. So the "#P"-completeness of `PERM` cannot come from a parsimonious construction; Valiant's proof instead builds a genuinely non-identity recovery function $S$ that indirectly extracts the SAT-instance answer from the *count* of matchings, without that count-preserving reduction ever having to exist. This is the sharpest illustration in the whole topic of why counting reductions are a strictly richer tool than decision reductions.

### Toda's theorem: "#P" sits above the entire polynomial hierarchy

Toda (1989) placed "#P" in the broader landscape of complexity classes with one of the most striking separation results in the field:

$$P \subseteq NP \subseteq PH \subseteq P^{\"#P"} \subseteq PSPACE$$

Read $P^{\"#P"}$ as "the class of problems solvable in polynomial time given a *free* oracle for any "#P" problem" — one "#SAT" query, treated as a black box returning an exact count in unit time. Toda's theorem is $PH \subseteq P^{\"#P"}$: a single call to a "#P" oracle suffices to decide *any* problem in the entire polynomial hierarchy, including problems with arbitrarily many alternating $\exists/\forall$ quantifier blocks (QBF with $k$ alternations, for any fixed $k$). Since SAT itself is essentially "1-QBF" (one block of $\exists$), this says "#SAT" is provably at least as hard as QBF instances with any constant number of quantifier alternations — a formal vindication of the practitioners' intuition that "#SAT" is a harder beast than SAT.

The proof route goes through **PP** ("probabilistic polynomial time"), the natural *decision* sibling of "#P": given $Q(x,y)$, PP asks "does $(x,y)\in Q$ hold for *more than half* the $y$'s?" PP contains both NP and co-NP and turns out to be essentially as powerful as "#P" itself — the technical fact underlying Toda's proof is $P^{PP} = P^{\"#P"}$ (Angluin). Intuitively: a PP oracle can extract the *most significant bit* of a "#P" count, and by repeatedly querying PP on cleverly modified instances you can peel off every bit of the exact count, so the two oracle powers coincide.

```mermaid
graph TD
    P["P (poly-time decision)"] --> NP["NP"]
    NP --> PH["PH (polynomial hierarchy, all fixed quantifier depths)"]
    PH -->|"Toda's theorem: PH ⊆ P^"#P""| PSP["P^"#P" (poly-time + one "#P"-oracle call)"]
    PSP --> PSPACE["PSPACE (QBF-complete)"]
    SHARPP[""#P" (exact counting, e.g. "#SAT")"] -.->|"one oracle call captures all of PH"| PSP
    style SHARPP fill:#5b3a3a,stroke:#c99,color:#eee
    style PSP fill:#3a4a5b,stroke:#9bc,color:#eee
```

**Where this connects for a verification-toolchain builder:** this is the theoretical ceiling on any exact quantitative-verification query — "how many program inputs violate this Hoare postcondition," "what fraction of the state space is reachable," "how many concrete counterexamples does this refinement-type violation admit" — all of these are "#SAT"-shaped once you've encoded the verification condition as a Boolean formula. Toda's theorem tells you that exact answers to such quantitative queries are *provably* at least as expensive as deciding any bounded-alternation QBF (the same complexity class the book's own QBF chapters, Ch. 29–31, are built around) — which is exactly why practical quantitative-verification tools reach for *approximate* model counting (below) rather than exact counts, the same way CEGAR reaches for abstraction rather than full state enumeration.

## Exact model counting: DPLL extensions and knowledge compilation

The book organizes practical exact counters along two lines: systematic search extensions of DPLL, and compilation into a normal form from which counting is cheap.

### DPLL-based counting: from "stop at one" to "sum over all"

The earliest approach, formalized as **CDP** (Birnbaum and Lozinskii), is the most direct possible fix to DPLL: instead of returning as soon as a branch is satisfied, note how many variables remain *unassigned* on that branch, and credit it with $2^{n-t}$ solutions (all completions of the $t$ fixed variables), then backtrack and keep going. The recursion is genuinely simple:

$$\#F = \#F|_{x} + \#F|_{\lnot x}$$

with base cases: an empty clause means 0 models; all clauses satisfied with $t$ variables fixed means $2^{n-t}$ models. This single change — replacing "return `SAT`" with "return $2^{n-t}$ and keep searching" — is the entire conceptual leap from a decision procedure to a counting procedure. Note the practical wrinkle: most modern DPLL implementations don't bother tracking "are all clauses satisfied" as a first-class check, because for pure satisfiability that information is redundant (once satisfied, further branching just fills in arbitrary values). A model counter *must* maintain this tracking, or it degenerates into literally enumerating every one of the $2^{n-t}$ completions — which defeats the entire point.

A Rust sketch makes the base-case distinction concrete — this is the one line where "SAT solver" and "model counter" fork:

```rust
enum CountResult {
    Count(u128),
}

fn cdp_count(formula: &mut Cnf, fixed_vars: usize, total_vars: usize) -> CountResult {
    unit_propagate(formula);
    if formula.has_empty_clause() {
        return CountResult::Count(0);
    }
    if formula.all_clauses_satisfied() {
        // The DPLL fork: a decision procedure would return `Sat` here and stop.
        // A model counter credits every completion of the unfixed variables.
        let unfixed = total_vars - fixed_vars;
        return CountResult::Count(1u128 << unfixed);
    }
    let x = select_branch_variable(formula);
    let CountResult::Count(a) = cdp_count(&mut formula.assign(x, true), fixed_vars + 1, total_vars);
    let CountResult::Count(b) = cdp_count(&mut formula.assign(x, false), fixed_vars + 1, total_vars);
    CountResult::Count(a + b)
}
```

**Component analysis (Relsat).** If the constraint graph of $F$ (variables as vertices, an edge when two variables co-occur in a clause) splits into disjoint components $G_1, \dots, G_k$, the sub-formulas $F_1, \dots, F_k$ are independent and $\#F = \#F_1 \times \#F_2 \times \cdots \times \#F_k$. This is the model-counting analogue of a divide-and-conquer decomposition you'd recognize from lattice-based abstract interpretation over product domains: if two parts of your program state genuinely don't interact, you factor the analysis, not just for efficiency but because the *semantics* of the combination is literally a product. Relsat detects these components *dynamically*, as unit propagation simplifies the graph — a technique historically judged too expensive for pure SAT solving (you don't need components if you're going to stop at the first solution anyway) but essential for counting, where reusing independence pays for itself immediately.

**Caching.** As you descend the search tree, you may re-encounter a sub-formula (or component) you've already counted. The natural fix — memoize it — is precisely a form of formula/component caching, and it is the single technique the chapter singles out as *more powerful than clause learning* even for plain SAT, though its overhead only pays off on harder problems like "#SAT". Unlike clause learning, where the "reason" for unsatisfiability compresses neatly into one conflict clause, caching a satisfiable component requires storing a signature of the whole sub-formula plus its count. `Cachet` combines component caching with clause learning (with "sibling pruning" to avoid an unsound interaction that would otherwise silently degrade counts into lower bounds); `sharpSAT` stores components more compactly (only variable and clause indices, not full clause text) and adds a lookahead "failed literal" test.

If you're building a checker with a memoized elaborator in mind, this is a direct analogue: **component caching is memoized judgment-checking keyed by a syntactic signature of the sub-problem**, exactly the shape of a memo table keyed on `(context, goal)` pairs in an incremental type checker — the same tension applies too: you get reuse only if your signature is coarse enough to hit cache but precise enough to stay sound.

### Knowledge compilation: pay once, query cheaply

A structurally different idea: instead of searching the CNF directly, **compile** it into another representation from which the count (and other queries) can be read off in time polynomial in the *compiled* representation's size. The paradigm example is a BDD, where you can read off the model count by a single traversal from the "1" leaf to the root. `c2d` (Darwiche) compiles CNF into **d-DNNF** — deterministic, decomposable negation normal form — a strict generalization of ordered BDDs.

An NNF is a DAG with $\land$/$\lor$ internal nodes and literal leaves (no depth restriction, unlike CNF's rigid 3-layer shape); it becomes usable for counting once you impose two properties:

- **Decomposability**: the children of an $\land$-node share no variables, so $\#f^{\land} = \#f_1 \times \#f_2 \times \cdots \times \#f_s$ — this is the *same* independence-factoring idea as component analysis above, now baked structurally into the representation rather than discovered dynamically at each search node.
- **Determinism**: the children of an $\lor$-node have pairwise-inconsistent solution sets (no two children can be true simultaneously), so $\#f^{\lor} = \#f_1 + \#f_2 + \cdots + \#f_s$ — a disjoint union, so the counts simply add.

Given both, model counting is a single bottom-up topological pass: leaves get count 1, $\land$-nodes multiply their children's counts, $\lor$-nodes add theirs, and the root's count is $\#F$. `c2d` builds this by constructing a **dtree** (a binary decomposition tree over clauses, annotated at each internal node with a *separator* — the variables shared between its left and right subtrees) and driving an exhaustive DPLL search that resolves separator variables until the two sides become variable-disjoint (hence combinable with $\land$) or must be split by case analysis over the separator's values (hence combinable with $\lor$).

The knowledge-compilation payoff is architectural, not just algorithmic: once you've paid the compilation cost, you can answer *many* subsequent queries — marginal probabilities, backbone variables, another count after a small formula edit — each in time polynomial in the compiled representation, without ever re-running DPLL. This is exactly the "compile once, check fast" tradeoff you'd weigh when deciding whether your own verifier should re-elaborate a term from scratch on every query or maintain a persistent, incrementally-checkable normal form.

## Approximate model counting: estimation with and without guarantees

Exact counters hit a wall precisely because "#SAT" is "#P"-complete: an algorithm forced to distinguish $10^{70}$ solutions from $10^{70}+1$ is paying for a distinction almost no application actually needs. The chapters split approximate techniques into two tiers: **no guarantees** (fast heuristics with good typical-case behavior but no formal correctness statement) and **guarantees** (formal lower/upper bounds, usually probabilistic).

### Estimation without guarantees

`ApproxCount` (Wei and Selman) is built on a beautifully simple observation, due to Jerrum–Valiant–Vazirani: if you can sample (near-)uniformly from $\mathrm{Sol}(F)$, you can estimate $\gamma$, the fraction of solutions with variable $x$ set true, from a sample; then $\#F = (1/\gamma)\cdot\#(F|_{x=\mathrm{true}})$, recursively reducing counting to counting a smaller formula, terminating either when all variables are fixed or when an exact counter can finish off the residual formula. The catch: `SampleSat` (a Walksat-derived local search sampler) gives *no guarantee of uniformity*, and MCMC methods generally have exponentially long mixing times on hard combinatorial structure — so estimates can be excellent in practice yet arbitrarily wrong in the worst case. `SampleMinisat` (Gogate and Dechter) instead samples from the *backtrack-free* search space of a DPLL tree and uses importance re-weighting to correct toward uniformity, converging to exact uniform sampling in the limit as more of the tree gets explored.

### Estimation with guarantees, via a common hashing framework

This is where Chapter 26 pays off — a single unifying algorithm, `HashCounter`, into which nearly every modern approximate counter (`ApproxMC`, `SearchMC`, and their descendants) can be slotted as an instantiation:

**The core idea.** A **universal hash function** $h_i : \{0,1\}^n \to \{0,1\}^i$ partitions the solution space into $2^i$ roughly-equal "cells." Pick $i$ large enough that a single cell is small enough to count exactly, count the solutions landing in one fixed cell (say, the all-zeros cell $0^i$), then scale by $2^i$ — the count in a cell is an unbiased, low-variance estimator of $\lvert\mathrm{Sol}(F)\rvert / 2^i$ *when the hash family has the right statistical properties*.

```rust
// A structural sketch of Algorithm 1 (HashCounter) from Ch. 26.
// The real work happens inside `saturating_count`, which is a SAT-solver call.
fn hash_counter(phi: &Cnf, eps: f64, delta: f64) -> u128 {
    let thresh = find_small_cell_threshold(eps);          // poly(1/eps)
    if let Some(exact) = saturating_count(phi, thresh) {
        return exact;                                     // solution space already "small"
    }
    let iters = find_repetition_count(delta);              // amplifies confidence via median
    let mut estimates = Vec::new();
    for _ in 0..iters {
        let hash_family = choose_xor_hash_family(phi.num_vars());
        // Binary/galloping search over cell-index i: find smallest i where the
        // cell 0^i induced by h_i is "small" (< thresh) but 0^{i-1}'s cell saturated.
        let (i, cell_size) = find_small_cell_index(phi, &hash_family, thresh);
        estimates.push(cell_size * (1u128 << i));
    }
    median(estimates)
}
```

Two hash-function properties do the real theoretical work. A family is **uniform** if every element maps to every bucket with equal probability $1/2^i$; it is **strongly 2-universal** (Carter–Wegman) if for *any two distinct* elements $x \neq y$, $\Pr[h_i(x) = h_i(y)] = 1/2^i$ — i.e., collisions behave exactly as they would for a perfectly random function, pairwise. Strongly 2-universal families bound the *dispersion index* $\sigma_i^2/\mu_i$ of the cell-size distribution, which is exactly the statistical control needed to make Chebyshev/Markov-type tail bounds go through and deliver a rigorous $(1+\varepsilon, 1-\delta)$ PAC guarantee: with probability at least $1-\delta$, the reported estimate lies within a $(1+\varepsilon)$ multiplicative factor of the true count.

**The hash family that actually gets implemented.** Random **XOR (parity) constraints** are the practical instantiation: $h_i(X) = AX + b$ over $GF(2)$, with $A$ an $m\times n$ random 0-1 matrix and $b$ a random bit vector. Checking whether a solution lands in cell $0^i$ under this hash is exactly checking satisfiability of $\phi \land (AX + b = 0)$ — a CNF+XOR formula, directly solvable by SAT solvers that natively handle parity reasoning (`CryptoMiniSat`) or by Tseitin-encoding the XOR into extra CNF clauses. This is the same "random parity constraint as a universal hash, riding on a CNF SAT-solver backend" idea that MBound (2006, Gomes–Sabharwal–Selman) pioneered as a historical breakthrough, and it is the technique that turned Stockmeyer's 1983 theoretically-elegant-but-impractical construction (approximate counting via $\Sigma_2^P$/NP-oracle calls) into something that scales to formulas with hundreds of thousands of variables.

**A genuinely useful optimization: independent support.** A subset $I \subseteq \mathrm{Sup}(\phi)$ is an *independent support* if any two solutions agreeing on $I$ are identical — i.e., $I$ alone determines the full assignment. Hashing only over $I$ (instead of the full variable set) gives exactly the same statistical guarantees but with XOR clauses that can be one to two orders of magnitude smaller, since $|I| \ll |\mathrm{Sup}(\phi)|$ for many real formula classes. This is precisely a **dependency-slicing** move: throw away the variables that don't independently constrain the count, the same move you'd make when narrowing which program variables actually matter to a reachability query before running expensive abstract-interpretation propagation over the full state.

**Dependent hash functions as a performance lever.** Choosing the $h_i$'s *independently* forces a linear scan over candidate cell-indices $i$, because you can't rule out non-monotone cell sizes across $i$. Choosing them from a **prefix family** — where $h_i$'s output is literally a prefix of $h_{i+1}$'s output — guarantees $|\mathrm{Cell}_{\phi,h_i}| \le |\mathrm{Cell}_{\phi,h_{i-1}}|$ monotonically, enabling binary (or galloping) search over $i$, *and* letting a CDCL solver reuse learned clauses across successive queries as $i$ grows (since each query is a strict tightening of the previous formula). This trades a slightly harder correctness proof (bounding a union of correlated failure events instead of independent ones) for a large constant-factor speedup — a very familiar tradeoff if you've ever weighed incremental SMT solving (reusing a solver's learned state across successive, related queries) against re-solving from scratch.

**DNF counting is a genuinely different problem.** Karp and Luby's 1983 Monte Carlo FPRAS solved *DNF* counting decades before any hashing-based technique matched it (2016–2019), even though hashing had solved *CNF* counting since 1983. The reason is structural: Stockmeyer's trick for boosting a constant-factor approximation into a $(1+\varepsilon)$-factor one relies on conjoining $k = O(1/\varepsilon)$ independent copies of the formula — but the *class of DNF formulas is not closed under conjunction* (conjoining DNF formulas can blow up exponentially before you get back to DNF), so the same boosting trick simply doesn't apply. Karp–Luby instead built a clever alternate universe $\mathcal{U} = \{(\sigma,\phi_i) \mid \sigma \models \phi_i\}$ where the sampling ratio is bounded by the *number of cubes* $m$ rather than by the (possibly tiny) solution density — sidestepping the whole density problem that would otherwise make naive Monte Carlo need exponentially many samples.

**Weighted counting.** Attaching a weight $\rho(\sigma) \in [0,1]$ to every assignment and asking for $\rho(\phi) = \sum_{\sigma \models \phi} \rho(\sigma)$ generalizes unweighted counting (weight 1 everywhere) and is the formal shape of *probabilistic* verification queries. The chapter's unifying trick: define the **tail function** $\tau(u) = |\{\sigma \models \phi : \rho(\sigma) \ge u\}|$, note that $\rho(\phi)$ is exactly the area under the $\tau(u)$ curve, and reduce weighted counting to approximating that integral — either by turning it into a sequence of $O(n)$ optimization queries (MaxSAT/MPE, à la Ermon et al.) or into a sequence of $O(p)$ unweighted-counting subproblems on Pseudo-Boolean-constrained formulas (à la Chakraborty–Meel), each still resolved by the same hashing machinery.

## Synthesis

```mermaid
graph LR
    SAT["SAT: does a witness exist?"] --> MC[""#SAT": how many witnesses?"]
    MC --> EXACT["Exact: CDP / DPLL extensions,\ncomponent+caching, d-DNNF compilation"]
    MC --> APPROX["Approximate: universal-hashing PAC counters\n(1+ε, 1-δ) guarantees"]
    APPROX --> WEIGHTED["Weighted counting\n(probabilistic verification queries)"]
    MC -.->|""#P"-completeness (Valiant)"| SHARPP[""#P" above P, NP"]
    SHARPP -.->|"Toda's theorem"| PH2[""#P" provably ≥ PH ⊇ QBF(k)"]
```

Model counting is the chapter that makes the abstract complexity-theoretic ceiling of "counting versus deciding" concretely load-bearing: Valiant's theorem is the formal reason a fast SAT solver gives you *zero* traction on counting, and Toda's theorem is the formal reason exact quantitative-verification queries (how many inputs violate an invariant, what fraction of states are reachable, the weighted count behind a probabilistic-program's semantics) are inherently harder than even QBF validity — which is precisely why the practical machinery of this chapter (component/knowledge-compilation exact counters when the problem is small enough; universal-hashing PAC counters when it isn't) exists at all, and why quantitative CEGAR-style tools reach for approximate, guarantee-bearing counts rather than exact ones. The universal-hashing framework itself is worth remembering independently of counting: "partition a huge solution space into small, roughly-equal, efficiently-checkable cells using a randomly chosen structured linear map" is a general-purpose tool anywhere you need a statistically controlled way to sample or size a combinatorially large but SAT/SMT-checkable set — including projected model counting ($\lvert\mathrm{Sol}(\exists X.\,\phi)\rvert$) and network-reliability-style existential-quantifier elimination, both mentioned as direct extensions in the book's own conclusion.
