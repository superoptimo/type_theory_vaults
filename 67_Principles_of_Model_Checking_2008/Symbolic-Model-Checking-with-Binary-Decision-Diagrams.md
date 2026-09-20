---
title: Symbolic Model Checking with Binary Decision Diagrams
book: Principles of Model Checking (Baier & Katoen, 2008)
chapter: "Chapter 6, Section 6.7 (Symbolic CTL Model Checking)"
pages: 381–421
tags: [model-checking, ctl, obdd, bdd, symbolic-computation, sat-smt-csp, static-analysis, boolean-functions]
---

[[book-guidelines|↩ Back to guidelines]]

# Symbolic Model Checking with Binary Decision Diagrams

## Why explicit CTL model checking runs out of road

Everything the book built up to Section 6.7 — the recursive $\mathit{Sat}$-set computation for CTL, the least/greatest fixed-point characterizations of $\exists(\Phi\,U\,\Psi)$ and $\exists\Box\Phi$ — assumes you can *enumerate* states. Chapter 6's basic algorithm walks the parse tree of a formula and, at each node, builds an explicit set of states (as a list, a bitset indexed by state, whatever) representing $\mathit{Sat}(\Psi)$. That's fine while $|S|$ is small. But Chapter 2 already showed that $|S|$ explodes multiplicatively in the number of parallel components and exponentially in the number of variables: $n$ Boolean variables alone give $2^n$ states, and hardware/software models routinely have hundreds of them. An explicit representation — even a very good one, a bitset — needs $\Omega(|S|)$ space just to *write down* a single set of states. If $|S| = 2^{100}$, you cannot afford that, no matter how clever your traversal algorithm is.

The move Section 6.7 makes is not a smarter search algorithm — it's a change of representation. Instead of representing a set of states as a *list of its elements*, represent it as a **Boolean function that returns true exactly on the elements of that set**. This is the same idea as a type-level predicate versus an enumerated `HashSet`: a predicate `fn in_set(s: State) -> bool` can describe an astronomically large set in a constant-size closure, provided the predicate itself has a compact structure. The entire chapter's remaining content is about (a) how to encode transition systems as such predicates ("switching functions"), and (b) what data structure lets you store, combine, and compare these predicates efficiently — the answer being **(reduced, ordered, shared) binary decision diagrams**.

**What breaks without this:** without a *canonical* representation for these Boolean functions, you can build the predicates, but you can't cheaply check whether two of them are equal — and CTL's fixed-point algorithms (Algorithms 20/21 in the book) terminate exactly when two successive approximations $f_j$ and $f_{j+1}$ become equal as functions. If equality-checking on your representation is coNP-complete (as it is for general propositional formulas), your termination test alone can dominate the whole algorithm. This is the specific technical problem OBDDs solve.

## 1. Encoding transition systems as switching functions

### The setup

Take a "large" finite transition system $TS = (S, \rightarrow, I, AP, L)$ (the book drops the action set here — it's irrelevant to satisfaction-set computation) with $\rightarrow\, \subseteq S \times S$. Fix $n \geq \lceil \log|S| \rceil$ and an injective encoding $\mathrm{enc}: S \to \{0,1\}^n$. (Any leftover bit vectors not in the image are just declared "pseudo-states" nobody reaches — a harmless padding trick.) Once you fix this encoding you can stop thinking of states as an opaque type and start thinking of them as evaluations of $n$ Boolean variables $x_1, \dots, x_n$.

A **switching function** (Notation 6.49) for a variable set $\mathrm{Var} = \{z_1, \dots, z_m\}$ is a function $f: \mathrm{Eval}(\mathrm{Var}) \to \{0,1\}$, where $\mathrm{Eval}(\mathrm{Var})$ is the set of assignments $\eta: \mathrm{Var} \to \{0,1\}$. It's deliberately phrased as "function of named variables" rather than "function of a bit tuple $\{0,1\}^n \to \{0,1\}$" — this matters later because composition operators need to line up variables *by name*, not by position, once you start combining switching functions over different (but overlapping) variable sets.

Given this, any subset $T \subseteq S$ is represented by its **characteristic function** $\chi_T$, and the transition relation itself becomes a switching function over *two* copies of the state variables:

$$\Delta: \mathrm{Eval}(x, x') \to \{0,1\}, \qquad \Delta(s, t) = 1 \iff s \to t$$

where $x = (x_1,\dots,x_n)$ encodes the *current* state and $x' = (x_1',\dots,x_n')$ — a fresh, primed copy of the same variables — encodes the *successor* state. This unprimed/primed doubling is the standard trick in all of symbolic verification (it's exactly what SMT-based bounded model checking and CEGAR loops do too, when they encode a transition relation as a formula over "step $i$" and "step $i{+}1$" variable copies): the same physical variable needs two roles simultaneously, and the only way to keep them straight in a single Boolean formula is to give them different names.

*Worked example (Example 6.56).* Two states $s_0, s_1$ with transitions $s_0 \to s_0$, $s_0 \to s_1$, $s_1 \to s_0$, encoded $s_0 = 0$, $s_1 = 1$. The switching function is $\Delta = \neg x \lor \neg x'$ — check: $[x{=}0, x'{=}0]$, $[x{=}0,x'{=}1]$, $[x{=}1,x'{=}0]$ all satisfy it, and these are exactly the three transitions.

### Rust grounding: the predicate view

The cleanest way to see "characteristic function instead of enumerated set" is to contrast two `trait` shapes:

```rust
// Explicit representation — what Chapter 6's basic algorithm uses.
trait ExplicitStateSet {
    fn contains(&self, s: StateId) -> bool;
    fn states(&self) -> Vec<StateId>;   // must be able to enumerate — O(|S|) worst case
}

// Symbolic representation — what Section 6.7 introduces.
trait SwitchingFunction {
    // No enumeration method at all. The set is *defined* by this predicate,
    // and its size is irrelevant to the representation's own size.
    fn eval(&self, assignment: &[bool]) -> bool;
}
```

Naively, `SwitchingFunction` could just be `Box<dyn Fn(&[bool]) -> bool>` — but that's useless for model checking, because you can't compare two closures for semantic equality, can't compose them cheaply, and can't bound their memory footprint. The rest of Section 6.7 is precisely the search for a concrete `struct` implementing `SwitchingFunction` that supports equality, conjunction/disjunction/negation, and existential quantification, all efficiently. That struct is the (RO)BDD.

### Cofactors and the Shannon expansion

Before building that data structure, the book needs the algebraic tool that will let it exploit shared substructure: the **cofactor**.

**Definition (Notation 6.50).** For a switching function $f$ over $\{z\} \cup \{y_1,\dots,y_m\}$, the *positive cofactor* $f|_{z=1}$ and *negative cofactor* $f|_{z=0}$ fix $z$ to $1$ or $0$ respectively and leave the rest as a function of $y$. Iterated cofactors $f|_{z_1=b_1,\dots,z_k=b_k}$ chain this, and — crucially — **the order in which you fix variables doesn't matter**: cofactoring is commutative in the variables it eliminates. A variable $z$ is *essential* for $f$ iff $f|_{z=0} \neq f|_{z=1}$ (i.e., $f$ actually depends on $z$).

*Worked example (Example 6.51).* $f(z_1,z_2,z_3) = (z_1 \lor \neg z_2) \land z_3$. Then $f|_{z_1=1} = z_3$ and $f|_{z_1=0} = \neg z_2 \land z_3$ — these disagree, so $z_1$ is essential. But for $g(z_1,z_2,z_3) = z_1 \lor \neg z_2 \lor (z_1 \land z_2 \land \neg z_3)$, cofactoring on $z_3$ gives $g|_{z_3=1} = z_1 \lor \neg z_2 = g|_{z_3=0}$, so $z_3$ is *not* essential — it's syntactically present but semantically irrelevant. This distinction (syntactic occurrence vs. semantic dependence) is exactly what a BDD will expose structurally: an inessential variable simply won't need a node.

**Lemma 6.52, Shannon expansion.** For any switching function $f$ and any variable $z$ in its scope:

$$f = (\neg z \land f|_{z=0}) \lor (z \land f|_{z=1})$$

This is just case analysis on $z$ — but it is the single algebraic fact underlying every decision-diagram operation in the chapter: pick a variable, split the function into its two cofactors, recurse on each, recombine. A **binary decision tree** (Remark 6.53) is the naive, unreduced realization of repeatedly applying Shannon expansion to *every* variable in a fixed order: a tree of height $m$ where each node at level $i$ branches on $z_i$, and leaves hold the final 0/1 value. It has $2^{m+1}-1$ nodes regardless of $f$ — no compression at all yet.

Two more operators round out the toolkit (Notation 6.54, 6.55), both defined via cofactors:

$$\exists z.\, f = f|_{z=0} \lor f|_{z=1} \qquad \forall z.\, f = f|_{z=0} \land f|_{z=1}$$

plus a **rename operator** $f\{z \leftarrow y\}$ that substitutes variable names. These two — existential quantification and renaming — are not cosmetic; they are exactly what's needed later to compute predecessor/successor sets symbolically (Section 6.7.2) and they turn out to be the *expensive* operators to implement efficiently (Section 6.7.4's relational product).

**Python sketch** (a `SwitchingFunction` is small enough here to represent as a truth table, purely to make Shannon expansion concrete without any BDD machinery):

```python
from itertools import product

def shannon_expansion_check(f, z_index, n_vars):
    """Verify f == (not z and f|z=0) or (z and f|z=1) by brute force."""
    for bits in product([0, 1], repeat=n_vars):
        z = bits[z_index]
        cof0 = list(bits); cof0[z_index] = 0
        cof1 = list(bits); cof1[z_index] = 1
        lhs = f(bits)
        rhs = (not z and f(cof0)) or (z and f(cof1))
        assert lhs == rhs
```

### Encoding the transition relation and reachability, symbolically (6.7.2)

With $\chi_B$ for a set $B$ and $\Delta(x,x')$ for the transition relation in hand, the book derives the symbolic analogue of backward BFS. The successor set of a *single* state $s = [x{=}b]$ is obtained purely algebraically: $\chi_{\mathrm{Post}(s)} = \Delta|_s\{x' \leftarrow x\}$ — cofactor $\Delta$ on the current-state variables, then rename the primed result back to unprimed. More usefully, the predecessor image of a whole *set* $T_j$ (not just one state) is

$$\exists x'.\big(\Delta(x,x') \land f_j(x')\big)$$

— this is the "one step backward" operator, and it drives **Algorithm 20** (symbolic $\mathit{Sat}(\exists(C\,U\,B))$) and **Algorithm 21** (symbolic $\mathit{Sat}(\exists\Box B)$) directly:

```
Algorithm 20 — Sat(∃(C U B))          Algorithm 21 — Sat(∃□B)
f₀(x) := χ_B(x)                        f₀(x) := χ_B(x)
repeat                                  repeat
  f_{j+1} := f_j ∨ (χ_C ∧ ∃x'.(Δ∧f_j(x')))  f_{j+1} := f_j ∧ ∃x'.(Δ∧f_j(x'))
until f_j = f_{j-1}                     until f_j = f_{j-1}
return f_j                              return f_j
```

These are literally Chapter 6's least/greatest fixed-point iterations from Section 6.4 (backward reachability for until, coinductive shrinking for always) — just rewritten so that "set" means "switching function" and "successor/predecessor" means "cofactor + existential quantification + rename." Boolean connectives on sets (union, intersection, complement) become $\lor, \land, \neg$ on switching functions directly — no new machinery needed there. The one genuinely hard new primitive is the *termination test* `f_j == f_{j-1}` and the *relational product* $\exists x'.(\Delta \land f_j(x'))$: both need a representation where equality and composition are cheap. That's the whole motivation for OBDDs, stated plainly by the book itself (p. 391): truth tables and binary decision trees are always $\Theta(2^n)$-sized regardless of $f$; CNF/DNF make equivalence-checking coNP-complete and have switching functions (parity, majority) requiring exponentially long formulas.

**What breaks without this:** without a data structure supporting cheap equality, Algorithms 20/21's `until` loop-condition becomes the bottleneck — you'd be doing coNP-complete equivalence tests every iteration of a fixed-point computation that might need $O(|S|)$ iterations. The entire performance case for symbolic model checking evaporates if you can't compare functions fast.

## 2. Ordered binary decision diagrams

### From decision tree to OBDD: two collapsing moves

The compaction the book performs on a binary decision tree has exactly two moves (Example 6.60, 6.61):

1. **Collapse constant subtrees.** If every leaf under a subtree has the same value, replace the whole subtree with a single terminal (drain) node — this happens precisely when the cofactor down that branch turns out to be a constant.
2. **Merge isomorphic subtrees**, and further, **skip a node whose two children are already identical** (i.e., the variable at that node isn't essential for that cofactor — recall Lemma 6.52's corollary: $z$ is inessential for $f$ iff $f = f|_{z=0} = f|_{z=1}$).

Applying both repeatedly to $f(z_1,z_2,z_3) = z_1 \land (\neg z_2 \lor z_3)$ collapses a 15-node tree down to a 4-node DAG. This DAG — nodes labeled by variables, two children each, terminal drains labeled 0/1 — is an **ordered binary decision diagram**.

### The formal object

**Definition 6.63 (OBDD).** Fix a variable ordering $\wp = (z_1,\dots,z_m)$. A $\wp$-OBDD is a tuple $B = (V, V_I, V_T, \mathrm{succ}_0, \mathrm{succ}_1, \mathrm{var}, \mathrm{val}, v_0)$: a DAG of inner nodes ($V_I$, each labeled by a variable, each with a 0-successor and 1-successor) and terminal drains ($V_T$, each labeled 0 or 1), with a distinguished root $v_0$, subject to two constraints: (i) **order-consistency** — along any root-to-drain path, variable labels strictly increase according to $\wp$ (you never see $z_3$ above $z_1$ if $\wp = (z_1,z_2,z_3)$), and (ii) every node is reachable from the root. The **semantics** $f_B$ (Definition 6.64) is: evaluate an assignment by walking from the root, taking the $b_i$-branch at each $z_i$-node, and reading off the drain's value — this is literally executing nested Shannon expansions.

Each node $v$ (not just the root) denotes its own switching function $f_v$ — the function of the *sub*-OBDD rooted at $v$ — and **Lemma 6.66** gives the bottom-up recurrence that makes this precise: $f_v = (\neg z \land f_{\mathrm{succ}_0(v)}) \lor (z \land f_{\mathrm{succ}_1(v)})$ for a $z$-node $v$. This is Shannon expansion again, just read node-by-node instead of variable-by-variable.

Crucially, the functions representable by nodes of a *fixed* OBDD $B$ for $f_B$ are not arbitrary cofactors of $f_B$ — they're exactly the $\wp$-**consistent** cofactors: those obtainable by fixing a *prefix* $z_1,\dots,z_i$ of the ordering (Notation 6.67, Lemma 6.68). Fixing $z_2$ alone while skipping $z_1$ doesn't count, even if the resulting function happens to coincide with one that does arise this way.

### Reduced OBDDs as a canonical data structure

An OBDD can still have redundancy: two distinct nodes representing the *same* $\wp$-consistent cofactor (this literally happened with the two "0" drains and two "1" drains in the unreduced left diagram of Figure 6.21). **Definition 6.69**: $B$ is **reduced** ($\wp$-ROBDD) if distinct nodes always denote distinct functions — every $\wp$-consistent cofactor gets exactly one node.

This single structural property buys two theorems that make OBDDs *the* representation of choice (**Theorem 6.70, Universality and Canonicity**):

- **Universality**: every switching function over $\mathrm{Var}$ has a $\wp$-ROBDD (constructively: take the set of all $\wp$-consistent cofactors of $f$ as the node set, label each by its minimal essential variable, and wire successors by cofactoring — the proof is a direct existence argument, not an afterthought).
- **Canonicity**: any two $\wp$-ROBDDs for the *same* function are isomorphic. There is, up to renaming nodes, exactly one reduced OBDD per function per fixed variable ordering.

Canonicity is the single fact everything downstream depends on: **checking $f = g$ reduces to checking whether their ROBDDs are the same graph** (or, with sharing — see below — literally the same node). No semantic reasoning required, just a syntactic/structural comparison. Compare this to the CNF/DNF case, where equivalence-checking is coNP-complete, and to explicit-state model checking, where "are these two sets of states equal" is at best a linear scan.

**Corollary 6.71 (Minimality)**: $B$ is reduced iff it has the fewest nodes among all $\wp$-OBDDs for $f$ — reducedness isn't just "nice," it's provably optimal for that ordering.

**Local reduction rules (Figure 6.23, Theorem 6.72).** Two purely local rewrites suffice to reduce any OBDD to its unique ROBDD, and their exhaustive application is *complete* (no reduced OBDD admits a rule application, and every non-reduced one does):

- **Elimination rule**: if $\mathrm{succ}_0(v) = \mathrm{succ}_1(v) = w$ (the variable at $v$ is inessential here), delete $v$, redirect incoming edges to $w$.
- **Isomorphism rule**: if two distinct nodes $v \neq w$ have identical $(\mathrm{var}, \mathrm{succ}_1, \mathrm{succ}_0)$ triples (or are both drains with the same value), merge them.

Both rules are semantics-preserving (they just collapse nodes already computing the same $f_v = f_w$), and a bottom-up sweep (drains first, then level $m, m{-}1, \dots, 1$) applies them to completion in $O(\mathrm{size}(B))$ time using bucket/hash techniques on the info-triples.

### The variable ordering problem

Canonicity is *per fixed ordering* $\wp$ — change $\wp$ and you get a different (still canonical, but structurally different) ROBDD, and sizes can differ **exponentially**. The book's running example (6.73):

$$f_m = (z_1 \land y_1) \lor (z_2 \land y_2) \lor \dots \lor (z_m \land y_m)$$

- Ordering $\wp = (z_m, y_m, \dots, z_1, y_1)$ (interleaved, grouping each clause's variables together): ROBDD has $2m+2$ nodes — **linear**.
- Ordering $\wp' = (z_1,\dots,z_m,y_1,\dots,y_m)$ (all $z$'s before all $y$'s): the $\wp'$-consistent cofactors after fixing all $z_i$'s are $\bigwedge_{i \in I_b} y_i$ for each bit pattern $b$ — there are $2^m$ *distinct* such cofactors (different index sets give different essential-variable sets), forcing **exponential** size.

Finding the *optimal* ordering is NP-hard (even checking whether a given ordering is optimal is NP-hard), so practice relies on heuristics — the book names Rudell's **sifting algorithm** (local search: move each variable to its best position holding the others fixed) without developing it further, deferring to specialized BDD textbooks. Two structural facts bound the damage: **symmetric functions** (value depends only on how many inputs are 1 — parity, majority, threshold functions) have $O(m^2)$ ROBDDs under *every* ordering (Lemma 6.74, because there are at most $i+1$ distinct cofactors after fixing any $i$ variables of a symmetric function), while some functions (the middle bit of binary multiplication) are provably exponential under *every* ordering — no ordering saves you.

The CNF/DNF-vs-ROBDD asymmetry is worth sitting with (p. 407): negation is $O(1)$ for ROBDDs (swap drain labels) but can blow up a CNF exponentially; satisfiability is trivial for ROBDDs (is there a 1-drain reachable at all?) but NP-complete for CNF; equivalence is a linear graph-isomorphism check for ROBDDs but coNP-complete for CNF. This is a genuinely different point in the complexity-vs-representation tradeoff space than SAT solvers occupy — worth flagging explicitly since it bears on the `sat-smt-csp` focus area below.

## 3. Shared OBDDs and the ITE operator

### From one function to a whole system: sharing

A real symbolic model-checking run needs many switching functions alive simultaneously: $\Delta$, each $f_a$ for $a \in AP$, and a growing set of intermediate $\mathit{Sat}(\Psi)$ approximations from Algorithms 20/21. Building a *separate* ROBDD per function wastes the fact that they typically share huge amounts of substructure (many of the same $\wp$-consistent cofactors recur across functions describing the same system).

**Definition 6.75 (Shared OBDD).** A $\wp$-SOBDD is exactly a $\wp$-ROBDD except it has *multiple* roots $v^0 = (v_0^1,\dots,v_0^k)$, one per represented function, all sharing one global reduced node pool. Reducedness is still required globally: any two distinct nodes anywhere in the structure denote distinct functions, even across different roots' sub-OBDDs. Concretely, this means the total size is *at most* $N_{f_1} + \dots + N_{f_k}$ (the sum of individual ROBDD sizes) but frequently much less, since shared cofactors across different $f_i$'s collapse to one node.

The implementation backbone is the **unique table**: a hash table keyed by info-triples $(\mathrm{var}(v), \mathrm{succ}_1(v), \mathrm{succ}_0(v))$, supporting a `find_or_add` operation that either returns the existing node for a triple or creates a fresh one. This *is* the isomorphism rule, applied incrementally and automatically as new nodes are requested — the SOBDD stays reduced at every point in time rather than needing a batch reduction pass afterward.

```rust
// A first cut at the SOBDD node pool as a Rust arena + hash-consing table.
use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct NodeId(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum NodeKind {
    Drain(bool),
    Inner { var: u32, hi: NodeId, lo: NodeId }, // succ1, succ0
}

struct Sobdd {
    nodes: Vec<NodeKind>,
    unique_table: HashMap<NodeKind, NodeId>, // hash-consing: the "unique table"
}

impl Sobdd {
    // find_or_add: the isomorphism rule, made incremental.
    fn find_or_add(&mut self, kind: NodeKind) -> NodeId {
        if let Some(&id) = self.unique_table.get(&kind) {
            return id; // an isomorphic node already exists — reuse it
        }
        let id = NodeId(self.nodes.len() as u32);
        self.nodes.push(kind);
        self.unique_table.insert(kind, id);
        id
    }

    fn mk_node(&mut self, var: u32, hi: NodeId, lo: NodeId) -> NodeId {
        if hi == lo {
            return hi; // elimination rule: variable is inessential here
        }
        self.find_or_add(NodeKind::Inner { var, hi, lo })
    }
}
```

Note the two reduction rules appear verbatim: `mk_node`'s `if hi == lo` short-circuit *is* the elimination rule, and `find_or_add`'s hash lookup *is* the isomorphism rule. This is exactly how real BDD packages (CUDD, BuDDy, and friends) are built.

### The if-then-else operator as the universal synthesis primitive

Rather than hand-implementing $\lor, \land, \neg, \oplus, \to$ separately over SOBDDs, the book adopts a single ternary primitive:

$$\mathrm{ITE}(g, f_1, f_2) = (g \land f_1) \lor (\neg g \land f_2)$$

("if $g$ then $f_1$ else $f_2$"), with $\mathrm{ITE}(0,f_1,f_2) = f_2$, $\mathrm{ITE}(1,f_1,f_2) = f_1$. Every binary connective reduces to one ITE call:

$$f_1 \lor f_2 = \mathrm{ITE}(f_1, 1, f_2) \qquad f_1 \land f_2 = \mathrm{ITE}(f_1, f_2, 0) \qquad \neg f = \mathrm{ITE}(f, 0, 1) \qquad f_1 \oplus f_2 = \mathrm{ITE}(f_1, \neg f_2, f_2)$$

Why does ITE fit so well with the node representation specifically? Because a node's own semantics is already an ITE: **$f_v = \mathrm{ITE}(z, f_{\mathrm{succ}_1(v)}, f_{\mathrm{succ}_0(v)})$** for a $z$-node $v$ — this is just Shannon expansion rewritten, and it means the info-triple stored in the unique table *is* an ITE call waiting to be replayed. The recursive algorithm (**Lemma 6.76**, cofactor distributes through ITE: $\mathrm{ITE}(g,f_1,f_2)|_{z=b} = \mathrm{ITE}(g|_{z=b}, f_1|_{z=b}, f_2|_{z=b})$) picks the *minimal* essential variable among the three input nodes' labels, recurses on both cofactors, and reassembles via `find_or_add` — Algorithm 22:

```rust
fn ite(sobdd: &mut Sobdd, u: NodeId, v1: NodeId, v2: NodeId) -> NodeId {
    // memoization via a "computed table" omitted here — see below
    if let NodeKind::Drain(b) = sobdd.nodes[u.0 as usize] {
        return if b { v1 } else { v2 };
    }
    let z = min_var(sobdd, u, v1, v2);
    let (u1, v1_1, v2_1) = (cofactor(sobdd, u, z, true),  cofactor(sobdd, v1, z, true),  cofactor(sobdd, v2, z, true));
    let (u0, v1_0, v2_0) = (cofactor(sobdd, u, z, false), cofactor(sobdd, v1, z, false), cofactor(sobdd, v2, z, false));
    let w1 = ite(sobdd, u1, v1_1, v2_1);
    let w0 = ite(sobdd, u0, v1_0, v2_0);
    sobdd.mk_node(z, w1, w0) // elimination rule folded into mk_node
}
```

**Lemma 6.77** bounds the blow-up: $N_{\mathrm{ITE}(g,f_1,f_2)} \le N_g \cdot N_{f_1} \cdot N_{f_2}$ — so disjunction/conjunction of two ROBDDs is at worst a *product*-size blow-up, not the exponential explosion you'd fear from naively expanding formulas. XOR is subtler: naively $N_f \cdot N_g^2$, but since $g$ and $\neg g$'s ROBDDs are isomorphic up to swapped drains, the real bound tightens to $N_f \cdot N_g$.

The naive recursive ITE (Algorithm 22) is exponential in the worst case, because the same triple $(u', v_1', v_2')$ can be reached along many recursion paths and gets recomputed each time. The fix is a **computed table** — a memo table keyed by input triples (Algorithm 23) — which brings the number of recursive calls down to the ROBDD size of the *result*, i.e., $\le N_u \cdot N_{v_1} \cdot N_{v_2}$, with each call amortized to constant work given hashed table access. This is a completely standard trick — it's the BDD-world's version of memoizing a recursive parser or a dynamic-programming table — but the payoff (constant-time equality via reduced-and-shared structure, near-linear-time Boolean composition) is what makes BDD packages practical rather than a theoretical curiosity.

One more implementation refinement worth naming because it recurs in the "trusted kernel" style of thinking this project cares about: **complement edges**. Negation via `ITE(f,0,1)` seems wasteful since $f$'s and $\neg f$'s ROBDDs differ only in drain labeling — but for *shared* OBDDs you can't just swap a drain's label (other functions' roots point at the same drain!). The fix is to tag *edges*, not drains, with a complement bit, representing $f$ and $\neg f$ by the same node reached via differently-tagged edges — turning negation into an $O(1)$ bit flip even inside a shared structure, at the cost of a canonicity side-condition (only the 1-drain is used; complement bits only appear on 0-edges and root pointers) to keep the representation unique.

### Lean grounding: canonicity as a proof-relevant idea

The type-theory-flavored way to read "reduced OBDDs are canonical" is as **definitional equality decided by normal form**, exactly the shape of Lean's `isDefEq`/`whnf` machinery. In Lean, two terms are definitionally equal if they reduce to the same normal form under $\beta\iota\delta\zeta$-reduction; the kernel doesn't do semantic reasoning about arbitrary term equality (undecidable in general) — it *normalizes and compares [[Timed-CTL-and-TCTL-Model-Checking#Syntax|syntax]]*. A hash-consed, reduced OBDD is doing precisely this for Boolean functions: instead of asking "are these two functions semantically equal" (a question that's coNP-complete for CNF, i.e. genuinely hard), it maintains an invariant — every subterm is kept in reduced/hash-consed form at all times — that turns the question into `physical_eq(node_a, node_b)`, an $O(1)$ pointer comparison. This is the same move a hash-consed AST or a Lean kernel with cached WHNF results makes: push all the work into *maintaining* a canonical form incrementally (the unique table's `find_or_add`, analogous to Lean's `mkAppN`-style smart constructors that could hash-cons) so that *checking* becomes trivial. If your compiler's elaborator ever needs to decide "are these two refinement-type predicates equivalent," canonical BDD-like representations (or their SMT-flavored cousins, e-graphs) are the concrete precedent for how to make that decision cheap rather than re-deriving semantic equivalence from scratch every time.

## 4. Symbolic computation of satisfaction sets, put together

Sections 6.7.2 and 6.7.4 fit together into a full symbolic CTL model-checking pipeline. The remaining primitive is the **relational product** — the preimage computation $\exists x'.(\Delta(x,x') \land f(x'))$ needed by Algorithms 20/21. Computing this naively (rename $f$, conjoin with $\Delta$ via ITE, then existentially quantify by repeated cofactoring/disjunction) requires several full top-down SOBDD traversals and risks building a huge intermediate ROBDD for $\Delta \land f\{x' \leftarrow x\}$ before you even get to quantify anything away.

The book's fix (**Algorithm 26**, relational product) fuses renaming, conjunction, and existential quantification into a *single* DFS traversal, using **interleaved variable orderings** $x_1 <_\wp x_1' <_\wp x_2 <_\wp x_2' <_\wp \dots$ so that a variable and its primed copy are always neighbors. This interleaving is doing real work in two places (Remark 6.79):

- It makes the **rename operator** itself cheap: renaming a variable to its immediate neighbor in the ordering only requires relabeling — no reordering of the DAG's levels, because the swap doesn't violate order-consistency of any *other* node's position.
- It bounds the **composite transition relation's** size: for a synchronous product $TS = TS_1 \otimes \dots \otimes TS_m$, $\Delta = \bigwedge_i \Delta_i(x_i, x_i')$, and with an interleaved ordering grouping each component's variables together, $N_\Delta \le N_{\Delta_1} + \dots + N_{\Delta_m}$ — *additive*, not the $\prod_i N_{\Delta_i}$ that Lemma 6.77's generic ITE bound would otherwise predict. Interleaving components' variable blocks lets you literally *link* their ROBDDs end to end.

Put together, the symbolic realization of [[CTL-Model-Checking|CTL model checking]] is: (1) build $\Delta$'s SOBDD compositionally (via ITE, exploiting an interleaved ordering); (2) obtain the atomic-proposition SOBDDs $f_a$ (often trivial — the $x_i$ variables themselves can double as the $AP$ labels via projection functions); (3) run the ITE algorithm bottom-up over the CTL parse tree for the propositional connectives; (4) run Algorithms 20/21 for $\exists U$ and $\exists\Box$, using the relational product for each preimage step; (5) check termination each iteration via — trivially, thanks to canonicity and sharing — node-identity comparison.

## Where this leads

This section is the technical payoff of everything the book set up about CTL: Section 6.4's fixed-point characterization of $\mathit{Sat}(\exists(\Phi\,U\,\Psi))$ (least fixed point / backward reachability) and $\mathit{Sat}(\exists\Box\Phi)$ (greatest fixed point) become literally executable once "state set" is reinterpreted as "switching function," and "set operation" as "Boolean/BDD operation." The chapter closes (6.8) by extending to CTL$^*$, which stitches this symbolic CTL machinery to the automata-based LTL procedure of Chapter 5 at maximal state subformulae — so the OBDD techniques here are also silently present wherever CTL$^*$ model checking bottoms out in a pure-CTL subproblem. More broadly in the book, BDD-style canonical/compact representations of large Boolean state spaces are the conceptual ancestor of the region-based finite abstractions used for timed automata (Chapter 9) and the linear-equation-system techniques for Markov chains (Chapter 10) — all three are instances of "don't enumerate the state space, compute over a compact algebraic surrogate for it instead."

For the standing compiler/elaborator project, this topic is squarely in the `static-analysis` and `sat-smt-csp` Focus Areas, with a real connection into `type-theory` as well:

- **`static-analysis`** — the symbolic $\mathit{Sat}$-set fixed-point computation (Algorithms 20/21) is *exactly* the shape of an abstract-interpretation fixed-point iterate over a lattice of predicates, just concretized to CTL and BDDs specifically; if the compiler's invariant-generation pass ever represents an abstract domain element as a Boolean/predicate structure rather than an explicit set, this section is the direct precedent for how to make the fixed-point *iteration itself* implementable (cheap join/meet via Boolean connectives, cheap termination check via canonical form).
- **`sat-smt-csp`** — ROBDDs and CNF/SAT solvers are two different, deliberately contrasted answers to "how do you represent and query Boolean functions at scale": ROBDDs buy $O(1)$ equivalence/negation/satisfiability at the cost of sometimes-exponential representation size (and an NP-hard sizing/ordering problem), while SAT solvers buy compact input representation at the cost of hard equivalence/enumeration. A CSP or constraint-propagation kernel built for the compiler's abstract-domain and counterexample-search work will likely need to know explicitly *which* of these regimes a given sub-problem falls into (and BDD-like automata/DFA representations of abstract domains, which the standing project's goals mention directly, are a generalization of exactly this canonical-normal-form idea beyond pure Boolean functions).
- **`type-theory`** — the canonicity argument (Theorem 6.70) is worth remembering the next time a definitional-equality or `isDefEq` check needs to be made fast: "normalize into a reduced, hash-consed structure once, then compare by identity" is the same strategy in both settings, discussed explicitly in the Lean [[Concurrency-and-Communication-Modeling#Grounding|grounding]] above.
