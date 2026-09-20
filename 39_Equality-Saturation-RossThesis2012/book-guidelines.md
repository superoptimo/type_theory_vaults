# Equality Saturation: Using Equational Reasoning to Optimize Imperative Functions — Guidelines

## Header

**Title:** Equality Saturation: Using Equational Reasoning to Optimize Imperative Functions
**Author(s):** Ross Tate (PhD Dissertation, Committee Chair: Professor Sorin Lerner)
**Publication:** University of California, San Diego, 2012 (Doctor of Philosophy in Computer Science)

**Brief Summary:**
This dissertation reframes imperative functions as pure mathematical expressions via a new intermediate representation, Program Expression Graphs (PEGs), and shows that this algebraic view enables *equality saturation* — repeatedly adding equalities (rather than destructively rewriting) to a common representation until no more can be inferred, so a compiler can represent exponentially many optimized versions of a program at once and pick the best one only at the end. Building on this foundation, the thesis develops three connected technologies: an optimizer that avoids the phase-ordering problem and supports global profitability heuristics, a translation validator that proves two programs equivalent using the same saturation machinery, and a technique for learning general, provably-correct optimization rules from single before/after example programs by generalizing their proofs of correctness (formalized categorically via pushouts and pullbacks, and shown to generalize beyond compilers to database query optimization, type debugging, and type polymorphization).

**Intent of the Author:**
Tate wrote this dissertation to argue that treating imperative programs as referentially transparent algebraic expressions — rather than as sequences of destructive commands — removes long-standing obstacles in compiler construction (phase ordering, local profitability heuristics, the difficulty of writing and trusting new optimizations) and opens up new possibilities such as automatically learning optimizations from examples, all validated concretely through the Peggy implementation and its evaluation on real Java and LLVM code.

---

## Topic List

1. **Program Expression Graphs (PEGs)** : [[Program-Expression-Graphs-(PEGs)|Link]]
   - PEGs as referentially transparent algebraic representations of imperative code
   - Theta nodes for values that vary across loop iterations : [[Program-Expression-Graphs-(PEGs)|Link]]
   - Phi nodes as executable gated-SSA selectors : [[Program-Expression-Graphs-(PEGs)|Link]]
   - Eval and pass nodes for extracting post-loop values and termination iteration : [[Program-Expression-Graphs-(PEGs)|Link]]
   - Loop lifting and bottom lifting of node semantics : [[Program-Expression-Graphs-(PEGs)|Link]]
   - PEG well-formedness conditions : [[Program-Expression-Graphs-(PEGs)|Link]]
   - Parameter nodes and substitution : [[Program-Expression-Graphs-(PEGs)|Link]]
   - Built-in PEG axioms and the invariance predicate : [[Program-Expression-Graphs-(PEGs)|Link]]
   - E-PEGs as equivalence classes of equal PEG nodes : [[Program-Expression-Graphs-(PEGs)|Link]]

2. **Equality Saturation** : [[Equality-Saturation|Link]]
   - Optimizations as additive equality analyses rather than destructive rewrites : [[Equality-Saturation|Link]]
   - Equality analyses as trigger-and-callback rules
   - The Optimize pipeline of conversion, saturation, selection, and reversion : [[Equality-Saturation|Link]]
   - Monotonic equality analyses and the additivity property : [[Equality-Saturation|Link]]
   - Uniqueness of normal form and confluence of saturation : [[Equality-Saturation|Link]]
   - Non-termination of saturation and bounding the search : [[Equality-Saturation|Link]]
   - Elimination of the phase-ordering problem : [[Equality-Saturation|Link]]
   - Global profitability heuristics over saturated representations : [[Equality-Saturation|Link]]

3. **Converting Between Imperative Code and PEGs** : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
   - The SIMPLE imperative language and its typing rules : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
   - Type-directed translation from imperative programs to PEGs : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
   - Semantics preservation of the translation : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
   - Abstract PEGs and forward flow graphs for translating arbitrary control-flow graphs
   - CFG-like PEGs as the target form for reversion
   - Reversion of PEGs back into loops, branches, and sequenced statements
   - Loop fusion and branch fusion during reversion : [[Converting-Between-Imperative-Code-and-PEGs|Link1]], [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link2]]
   - Hoisting redundancies and loop-invariant code motion during reversion : [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link1]], [[Converting-Between-Imperative-Code-and-PEGs|Link2]]
   - Guarded PEG contexts and CFG nodes for break and continue : [[Converting-Between-Imperative-Code-and-PEGs|Link]]

4. **Representing Effects in PEGs** : [[Representing-Effects-in-PEGs|Link]]
   - Heap-summary values threaded through load and store : [[Representing-Effects-in-PEGs|Link]]
   - Effect witnesses for exceptions and non-termination : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
   - PEGs as string diagrams with multiple outputs
   - Premonoidal and monoidal categories as the semantic model of effects : [[Representing-Effects-in-PEGs|Link]]
   - The center of a premonoidal category
   - Partially monoidal categories for effect witnesses : [[Representing-Effects-in-PEGs|Link]]

5. **Loop and Branch Optimizations Discovered by Saturation** : [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link]]
   - Loop-induction-variable strength reduction : [[Learning-Optimizations-from-Proofs|Link1]], [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link2]]
   - Inter-loop strength reduction : [[Evaluation-of-Learning|Link1]], [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link2]]
   - Loop-based code motion via distributing through eval and theta : [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link]]
   - CFG restructuring from local PEG rewrites : [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link]]
   - Loop peeling : [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link]]
   - Branch hoisting : [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link]]

6. **The Peggy Implementation** : [[The-Peggy-Implementation|Link]]
   - Representing the heap and method calls with sigma and invoke nodes : [[The-Peggy-Implementation|Link]]
   - The linearization problem for effect witnesses : [[The-Peggy-Implementation|Link]]
   - The Rete algorithm for efficient trigger matching : [[The-Peggy-Implementation|Link]]
   - The pseudo-boolean solver for global profitability : [[The-Peggy-Implementation|Link]]
   - The cost model based on operation cost and loop depth
   - Rationale for keeping eval and pass as separate nodes : [[The-Peggy-Implementation|Link]]

7. **Empirical Evaluation of Optimization** : [[Empirical-Evaluation-of-Optimization|Link]]
   - Time and space overhead of saturation on Java benchmarks : [[Empirical-Evaluation-of-Optimization|Link]]
   - Emergent optimizations arising from simple built-in axioms : [[Evaluation-of-Learning|Link1]], [[Empirical-Evaluation-of-Optimization|Link2]], [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link3]]
   - Domain-specific axioms and their optimizations : [[Empirical-Evaluation-of-Optimization|Link]]
   - Safety of additive axioms compared to destructive rewrite rules

8. **Translation Validation** : [[Translation-Validation|Link]]
   - Proving program equivalence by saturating a combined E-PEG
   - Alias-dependent load and store axioms : [[Translation-Validation|Link]]
   - Proof generation as a byproduct of validation : [[Translation-Validation|Link]]
   - Validation results against Soot and LLVM : [[Translation-Validation|Link]]
   - Discovery of a real compiler bug through translation validation : [[Translation-Validation|Link]]

9. **Learning Optimizations from Proofs** : [[Learning-Optimizations-from-Proofs|Link]]
   - Generalizing a concrete optimization instance into a general rule
   - The splitting problem in naive generalization
   - Working backward through a proof to generalize correctly : [[Learning-Optimizations-from-Proofs|Link]]
   - Decomposition of an overly specific learned rule : [[Learning-Optimizations-from-Proofs|Link]]
   - Sequencing versus parallelizing axiom applications : [[Learning-Optimizations-from-Proofs|Link]]
   - Removing irrelevant axiom applications automatically : [[Learning-Optimizations-from-Proofs|Link]]

10. **Category-Theoretic Foundations of Proof Generalization** : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
    - Categories, morphisms, and commuting diagrams : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
    - Axioms encoded as identity-carried morphisms : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
    - Pushouts as the formal model of applying an axiom : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
    - Pullbacks as the formal model of isolating shared structure : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
    - Pushout completions and subpushout completions : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
    - The proof of maximal generality of a learned rule : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
    - Instantiating the categorical framework for E-PEGs : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
    - Coproducts and the encoding of parallel axiom applications : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]

11. **Domain-Independent Applications of Generalization** : [[Domain-Independent-Applications-of-Generalization|Link]]
    - Database query optimization via conjunctive queries and the chase : [[Domain-Independent-Applications-of-Generalization|Link1]], [[Equality-Saturation|Link2]]
    - Functional and multi-valued dependencies
    - Type debugging by generalizing backward through a typing proof : [[Domain-Independent-Applications-of-Generalization|Link]]
    - Automatic type polymorphization : [[Domain-Independent-Applications-of-Generalization|Link]]

12. **Evaluation of Learning** : [[Evaluation-of-Learning|Link]]
    - Learning new optimizations from single before-and-after examples : [[Evaluation-of-Learning|Link]]
    - Amortizing superoptimizer cost by learning rules from one run : [[Evaluation-of-Learning|Link]]
    - Partial inlining as a byproduct of learning : [[Evaluation-of-Learning|Link]]
    - Cross-training learned rules on unseen code : [[Evaluation-of-Learning|Link]]

13. **Related Work and Positioning** : [[Related-Work-and-Positioning|Link]]
    - Superoptimizers as inspiration for additive equality reasoning : [[Equality-Saturation|Link]]
    - Destructive rewrite-based optimizers and the phase-ordering problem : [[Related-Work-and-Positioning|Link]]
    - Value Dependence Graphs and the problem of intermediate variables : [[Related-Work-and-Positioning|Link]]
    - Program Dependence Graphs, Dependence Flow Graphs, and Lucid : [[Related-Work-and-Positioning|Link]]
    - Theorem proving and E-graphs as ancestors of E-PEGs : [[Related-Work-and-Positioning|Link]]
    - Explanation-based learning and machine-learned compiler heuristics : [[Related-Work-and-Positioning|Link]]
    - Open challenges in interprocedural optimization

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 1–10)

**Summary:** Introduces the compiler-reliability and phase-ordering problems that motivate the thesis, and previews the three technologies developed later — inferring optimizations via equality saturation, translation validation, and learning optimizations from proofs — all built on Program Expression Graphs. : [[Domain-Independent-Applications-of-Generalization|Link]]

**Key Definitions & Concepts by Section:**
- **1.1 Inferring Optimizations** — equality analysis (an optimization expressed as adding equality information rather than destructively transforming a program); phase-ordering problem (the order optimizations run in affects code quality); global profitability heuristic (a decision made only after saturation, seeing the full ramifications of every candidate transformation). : [[Learning-Optimizations-from-Proofs|Link1]], [[Empirical-Evaluation-of-Optimization|Link2]]
- **1.2 Translation Validation** — translation validator (a tool that proves an optimized program equivalent to its original), here realized by saturating a combined representation of both programs. : [[Translation-Validation|Link]]
- **1.3 Learning Optimizations** — optimization instance (a concrete before/after example pair); generalization (abstracting an optimization instance, guided by its correctness proof, into a broadly applicable rule). : [[Evaluation-of-Learning|Link1]], [[Learning-Optimizations-from-Proofs|Link2]]

**Key Questions:**
1. Why does representing both the original and transformed program simultaneously (rather than destructively rewriting) remove the need to reason about optimization ordering?
2. In what sense does a proof of correctness for one concrete optimization instance tell the compiler "which parts of the programs mattered," and why is that the key to safe generalization?

---

### Chapter 2: Optimizing with Equalities (pp. 11–22)

**Summary:** Introduces Program Expression Graphs (PEGs) and their equivalence-class extension E-PEGs through the running example of loop-induction-variable strength reduction, showing how equality analyses (triggers plus callbacks) incrementally saturate an E-PEG and how a global heuristic later selects the best represented program. : [[Equality-Saturation|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 Program Expression Graphs** — Program Expression Graph (a graph of operator nodes and dataflow edges representing a computation with no side effects); theta node ($\theta$, produces the sequence of values a loop variable takes across iterations, with a left child for the initial value and a right child for the next value in terms of the previous one); phi node ($\phi$, a gated-SSA-style executable selector that picks between two values based on a condition, unlike a plain SSA $\phi$); referential transparency (the value of an expression depends only on its constituents, with no side effects); heap-summary node (threads a heap value through stateful operations so PEGs can still represent effects while remaining pure). : [[Program-Expression-Graphs-(PEGs)|Link]]
- **2.2 Encoding Equalities using E-PEGs** — E-PEG (a PEG whose nodes are grouped into equivalence classes of provably-equal expressions, drawn with dashed edges); equality analysis (a trigger pattern plus a callback that adds equalities when the pattern is matched); saturation engine (repeatedly applies equality analyses until no more equalities can be added or a bound is reached); saturated E-PEG (compactly represents all programs derivable by applying the given equality analyses in any order); pseudo-boolean solver (used to select the lowest-cost program encoded in a saturated E-PEG).
- **2.3 Benefits of our Approach** — optimization-order irrelevance (an optimization can never disable another, since the original program remains represented); global profitability heuristic (chooses among fully optimized candidate programs rather than making local, isolated decisions, e.g. for inlining).

**Key Questions:**
1. Why does grouping equal PEG nodes into equivalence classes let an E-PEG represent exponentially many program variants without an exponential blow-up in size?
2. Concretely, how does applying the peephole rewrite $i*5 = i \ll 2 + i$ in a traditional destructive compiler disable loop-induction-variable strength reduction, and why can the same axiom never disable it in the equality-saturation approach?

---

### Chapter 3: Reasoning about Loops (pp. 23–30)

**Summary:** Shows how PEGs represent single and nested loops using $\theta$, $\text{eval}$, and $\text{pass}$ nodes, then demonstrates an unanticipated "inter-loop strength reduction" optimization that falls out automatically from simple axioms.

**Key Definitions & Concepts by Section:**
- **3.1 Single Loop** — theta node ($\theta$, produces the sequence of values a loop variable takes across iterations; left child = initial value, right child = next value in terms of previous); $\text{eval}(s,n)$ (returns the $n$th element of sequence $s$, used to get a variable's value after a loop); $\text{pass}(s)$ (given a boolean sequence, returns the index of the first true element — the iteration count at which a loop terminates); one $\theta$/$\text{eval}$ node per live variable, but only one $\text{pass}$ node per loop.
- **3.2 Nested Loops** — subscripted $\theta_\ell$, $\text{eval}_\ell$, $\text{pass}_\ell$ nodes indicate loop nesting depth $\ell$.
- **3.3 Inter-Loop Strength Reduction** — worked example converting `i*10+j` into an equivalent accumulator by chaining distributivity, identity, associativity/commutativity, and a "zero incremented $n$ times produces $n$" axiom; illustrates that a locally "worse" rewrite (turning a constant into a loop) can enable a globally better result, selected only by the global profitability heuristic. : [[Evaluation-of-Learning|Link1]], [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link2]]

**Key Questions:**
1. Why is it necessary to have separate $\theta$, $\text{eval}$, and $\text{pass}$ nodes rather than fusing them, given they are always used together?
2. How does the inter-loop strength reduction example demonstrate that equality saturation can discover optimizations that no traditional compiler pass explicitly searches for?

---

### Chapter 4: Local Changes with Global Impacts (pp. 31–39)

**Summary:** Presents further examples (loop-based code motion, CFG restructuring, loop peeling, branch hoisting) showing how purely local PEG rewrites cause large, non-local changes to the corresponding CFG, then discusses loop optimizations not yet fully explored.

**Key Definitions & Concepts by Section:**
- **4.1 Loop-Based Code Motion** — distributing an operator through $\text{eval}$ moves it into a loop; distributing further through $\theta$ splits it into base-case and inductive-case computations, achieving code motion into a loop via purely local axioms. : [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link]]
- **4.2 Restructuring the CFG** — distributing multiplication through $\phi$ nodes plus constant folding radically changes the CFG's branching structure. : [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link]]
- **4.3 Loop Peeling** — sequence of axioms ($\text{pass}$ rewritten via $\phi$, $\text{eval}$/$\text{peel}$ distributed through operators and $\theta$) that peel the first iteration off any loop; $\text{peel}(C)[i] = C[i+1]$ strips the first element of a sequence. : [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link]]
- **4.4 Branch Hoisting** — moving a loop-invariant conditional from inside to after a loop by distributing $\text{eval}$ through $\phi$ then through domain operators. : [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link]]
- **4.5 Limitations of PEGs** — loop fusion, loop unrolling, and loop interchange are not fully formalized; the cost model (based only on loop nesting depth, not loop bounds) cannot yet make these optimizations look profitable.

**Key Questions:**
1. Why does distributing an operator through $\text{eval}$ and then through $\theta$ constitute "code motion into a loop," and why is this safe?
2. What specifically prevents Peggy's cost model from correctly valuing loop unrolling or loop interchange?

---

### Chapter 5: Formalization of Equality Saturation (pp. 40–44)

**Summary:** Gives the formal, implementation-independent definition of the `Optimize` function (convert to IR, saturate, select the best, convert back) and proves a convergence property for saturation. : [[Equality-Saturation|Link]]

**Key Definitions & Concepts:**
- `Optimize(cfg)` — converts a CFG to an IR, saturates it with equality analyses $A$, selects the best result via a global heuristic, then converts back to a CFG.
- $ir_1 \xrightarrow{a} ir_2$ — an equality analysis $a$ non-deterministically transforms $ir_1$ into $ir_2$ by adding equalities.
- Information order $\sqsubseteq$ on IRs (e.g. for E-PEGs, a subset relation on nodes and equalities).
- Additivity property — $(ir_1 \xrightarrow{a} ir_2) \Rightarrow ir_1 \sqsubseteq ir_2$: equality analyses only add information, never destroy it.
- Monotonic equality analysis — applying $a$ to a larger IR can only produce an equal-or-larger result, formalizing that earlier analyses can never disable later ones.
- Normal form (an IR with no more applicable equalities) and the uniqueness-of-normal-form theorem: given monotonic analyses, any two normal forms of the same starting IR are equal, i.e. saturation is confluent when it terminates.
- Non-termination examples — $A = (A+1)-1$ applied repeatedly, or unbounded recursive inlining; since full saturation may not terminate, Peggy bounds the number of processed expressions.

**Key Questions:**
1. What does the additivity property (Eq. 5.1) provide that destructive, ordered rewriting cannot?
2. Why does monotonicity of equality analyses guarantee confluence (uniqueness of normal form) rather than merely termination?

---

### Chapter 6: PEGs and E-PEGs (pp. 45–55)

**Summary:** Gives the full formal semantics of PEGs and E-PEGs — nodes, labels, children, loop-lifted and bottom-lifted types, well-formedness, referential transparency — establishing the theoretical foundation used throughout the rest of the thesis. : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link1]], [[Learning-Optimizations-from-Proofs|Link2]], [[Program-Expression-Graphs-(PEGs)|Link3]], [[Related-Work-and-Positioning|Link4]]

**Key Definitions & Concepts by Section:**
- **6.1 Formalization of PEGs** — PEG $= \langle N, L, C \rangle$ (nodes, a labeling to semantic functions, and a children function); bottom lifting ($\tau_\bot = \tau \cup \{\bot\}$, representing non-termination); loop lifting (an iteration index $i: L \to \mathbb{N}$; loop-lifted type $\tilde\tau = I \to \tau_\bot$); PEG well-formedness (three syntactic conditions ensuring cycles pass through a $\theta$'s second child, no inner-loop-to-outer-loop leakage, and no self-referential inner-loop results), with a theorem that well-formed PEGs have unique node semantics; parameter node (`param(x)`) and substitution notation $n[x \mapsto c]$. : [[Evaluation-of-Learning|Link1]], [[The-Peggy-Implementation|Link2]]
- **6.2 Formalization of E-PEGs** — E-PEG $= \langle N, L, C, E \rangle$ where $E$ is an equality relation inducing equivalence classes $N/E$; $[n]$ denotes $n$'s equivalence class. : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link1]], [[Learning-Optimizations-from-Proofs|Link2]], [[Program-Expression-Graphs-(PEGs)|Link3]], [[Related-Work-and-Positioning|Link4]]
- **6.3 Built-in Axioms** — core PEG identities such as $\theta_\ell(A,B) = \theta_\ell(\text{eval}_\ell(A,0),B)$; invariance predicate $\text{invariant}_\ell(n)$ (the largest syntactic predicate for "value doesn't vary across loop $\ell$'s iterations," used later for cost modeling and code hoisting). : [[Program-Expression-Graphs-(PEGs)|Link]]
- **6.4 How PEGs Enable our Approach** — referential transparency stated formally ($L(n)=L(n') \wedge \llbracket C(n)\rrbracket = \llbracket C(n')\rrbracket \Rightarrow \llbracket n\rrbracket = \llbracket n'\rrbracket$), contrasted with CFGs, which would instead need subgraph or program-state equality.

**Key Questions:**
1. Why must a value be both bottom-lifted and loop-lifted for PEG semantics to be well defined?
2. What does each of the three PEG well-formedness conditions individually rule out, and why is each necessary for uniqueness of node semantics?
3. Why does referential transparency make it sufficient to record equalities as equivalence classes of nodes, rather than as CFG subgraph equalities?

---

### Chapter 7: Converting Imperative Code to PEGs (pp. 56–83)

**Summary:** Defines the minimal SIMPLE imperative language and gives both an ML-pseudocode algorithm and a formal type-directed translation (with a Coq-verified semantics-preservation theorem) for converting SIMPLE programs — and more generally CFGs — into PEGs. : [[Converting-Between-Imperative-Code-and-PEGs|Link]]

**Key Definitions & Concepts by Section:**
- **7.1 The SIMPLE Programming Language** — a grammar of sequencing, assignment, if/else, and while, together with typing judgments for programs, statements, and expressions. : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
- **7.2 Translating SIMPLE Programs to PEGs** — node context $\Psi$ (maps variables to the PEG nodes representing their current value); statement and expression translation functions; `TemporaryNode` and `FixpointTemps` (used to "tie the knot" of recursive $\theta$ definitions for while loops). : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
- **7.3 Type-Directed Translation** — judgments $\Gamma \vdash e : \tau \triangleright \Psi ; n$ and $\Gamma \vdash s : \Gamma' \triangleright \Psi ;_\ell \Psi'$, structured as induction on well-typedness proofs so the translation's invariants become explicit for the correctness proof. : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
- **7.4 Preservation of Semantics** — a theorem (machine-checked in Coq) that translation preserves semantics up to non-termination; effect witness (introduced here first, a technique for preserving the non-termination of side-effect-free infinite loops that would otherwise be discarded as unreachable from the return value). : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
- **7.5 Converting a CFG to a PEG** — Abstract PEG (operates over whole program stores rather than individual variables, using symbolic-evaluator nodes); forward flow graph (an acyclicized CFG); algorithms that recursively build $\phi$-based decision expressions using dominators. : [[Converting-Between-Imperative-Code-and-PEGs|Link]]

**Key Questions:**
1. Why does the type-directed translation make the correctness proof easier than the pseudocode version, even though they compute the same result?
2. How do effect witnesses change what a PEG-based translation "sees" as reachable from the return value, and why does that matter for preserving non-termination?
3. In the CFG-to-PEG decision algorithm, why does the loop-context parameter change the choice between constructing a $\phi$ node versus an $\text{eval}$/$\text{pass}$ node?

---

### Chapter 8: Reverting PEGs to Imperative Code (pp. 84–121)

**Summary:** The most involved formal chapter: presents the process of converting PEGs back into SIMPLE (or CFG) programs, starting with a naive but correct algorithm and then layering on optimizations (loop fusion, branch fusion, hoisting, loop-invariant code motion, advanced control flow) needed for both efficiency and, once effects are added, correctness. : [[Converting-Between-Imperative-Code-and-PEGs|Link]]

**Key Definitions & Concepts by Section:**
- **8.1 CFG-Like PEGs** — a restricted PEG form (e.g. every $\text{eval}$'s second child is a $\text{pass}$) for which reversion is tractable. : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
- **8.2 Overview** — an immutable context; a three-phase naive reversion (loop nodes, then branch nodes, then sequencing); statement node (a PEG node wrapping a SIMPLE statement with multiple inputs and outputs).
- **8.3 Translating Loops** — an algorithm that assigns fresh variables to reachable $\theta$ nodes and recursively reverts the loop body, condition, and post-loop code into a while-loop statement node. : [[Translation-Validation|Link]]
- **8.4 Translating Branches** — bottom-up conversion of $\phi$ nodes into if-then-else statement nodes, identifying nodes reachable from both branches as "always evaluated." : [[Translation-Validation|Link]]
- **8.5 Sequencing Operations and Statements** — bottom-up linearization of the acyclic PEG into a SIMPLE statement, handling naming conflicts via temporary copies.
- **8.6 Loop Fusion** — a loop node that defers converting a loop body to a statement so multiple loops sharing the same $\text{pass}$ node can be merged into one physical loop, avoiding duplication. : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
- **8.7 Branch Fusion** — an analogous branch node for lazily deferring $\phi$-derived branches that share a guard, including "vertical fusion" for nested or sequential branches with the same condition. : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
- **8.8 Hoisting Redundancies from Branches** — a MustEval analysis (a "minimally precise" requirement) that generalizes the "always evaluated" set beyond simple reachability to hoist shared computation out of both branches; the general problem is undecidable. : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
- **8.9 Loop-Invariant Code Motion** — hoisting loop-invariant nodes out of loop bodies only when doing so would not change how often they execute; an EvalCond analysis (generalizes MustEval to loops); loop peeling used destructively to expose more hoisting opportunities. : [[Converting-Between-Imperative-Code-and-PEGs|Link1]], [[Translation-Validation|Link2]]
- **8.10 Advanced Control Flow** — break and continue handled via guarded PEG contexts (a context with a distinguished guard node) and CFG nodes (a generalization of statement nodes producing single-entry, multi-exit CFGs).

**Key Questions:**
1. Why must branch fusion and loop fusion each be performed only after all $\phi$ and $\text{eval}$ nodes, respectively, have been converted, rather than incrementally?
2. Why is determining the precise "always evaluated" set for a $\phi$ node fundamentally undecidable, and how does the MustEval analysis still guarantee termination of the reversion algorithm despite this?
3. Why does hoisting loop-invariant code sometimes change program semantics, and how does loop peeling fix this without abandoning the hoisting optimization?

---

### Chapter 9: Representing Effects (pp. 122–128)

**Summary:** Explains how PEGs — which have no built-in notion of evaluation order — represent heap operations and, more generally, arbitrary side effects via explicit "effect witnesses," and formalizes the semantic justification using premonoidal and partially monoidal category theory. : [[Representing-Effects-in-PEGs|Link1]], [[The-Peggy-Implementation|Link2]]

**Key Definitions & Concepts by Section:**
- **9.1 Representing the Heap** — `load`/`store` take and return an explicit heap-state argument (a heap-summary value) so sequential dependency is encoded via PEG dataflow edges rather than syntactic order. : [[Representing-Effects-in-PEGs|Link]]
- **9.2 Extending to Arbitrary Effects** — effect witness (generalizes the heap-summary technique to any effect, such as exceptions: an operation takes an effect witness in and produces a new one out); this shifts PEGs from single-output "expressions" toward multi-output "string diagrams," requiring projection nodes. : [[Representing-Effects-in-PEGs|Link]]
- **9.3 Categorical Semantics of Effect Witnesses** — category (objects, morphisms, composition, identity); premonoidal category (has a context-combining operator that is functorial in each argument separately); monoidal category (the pure case, where the combining operator is a full bifunctor since order does not matter); center of a premonoidal category (the "pure" morphisms that commute with everything, itself forming a monoidal category, related to Freyd categories, arrows, and strong monads); partially monoidal category $EW_P$ (a construction turning any premonoidal category into one where the combining operator is only a *partial* bifunctor, formalizing that only one effect witness can be "live" at a time — the categorical model of effectful PEGs and string diagrams). : [[The-Peggy-Implementation|Link1]], [[Domain-Independent-Applications-of-Generalization|Link2]], [[Representing-Effects-in-PEGs|Link3]]

**Key Questions:**
1. Why can the heap-summary semantic justification not be extended directly to effects like exceptions?
2. What problem does the center of a premonoidal category solve, and why must impure operations necessarily fall outside it?
3. What does it mean, categorically, for effect witnesses to guarantee that any valid rearrangement of a PEG has the same semantics?

---

### Chapter 10: The Peggy Implementation (pp. 129–143)

**Summary:** Describes Peggy, the concrete Java and LLVM-bytecode compiler implementing equality saturation, covering how it represents the heap and method calls, its Rete-based saturation engine, and its pseudo-boolean-solver-based global profitability heuristic. : [[The-Peggy-Implementation|Link]]

**Key Definitions & Concepts by Section:**
- **10.1 Intermediate Representation** — sigma node ($\sigma$, a heap-summary effect witness); `invoke` node (bundles an input $\sigma$, context object, method id, and actual parameters, logically returning a tuple that is projected out); the linearization problem (effect witnesses must be used linearly in generated code, but branch/loop fusion can make this unsolvable locally even when solvable globally); equivalence classes implemented via union-find. : [[The-Peggy-Implementation|Link1]], [[Equality-Saturation|Link2]]
- **10.2 Saturation Engine** — equality analysis as a (trigger, callback) pair; the Rete algorithm (adapted from rule-engine research, storing partial-match state as finite-state machines to avoid re-matching every pattern on every update); 84% of methods fully saturate, with the remainder bounded to a fixed number of processed expressions. : [[Evaluation-of-Learning|Link1]], [[Equality-Saturation|Link2]]
- **10.3 Global Profitability Heuristic** — `SelectBest` via a pseudo-boolean (0-1 integer linear program) solver; boolean variables for "evaluate this node" and "evaluate some node in this equivalence class"; constraints requiring the return value and its dependencies to be computed; a cost model scaling exponentially with loop nesting depth. : [[Equality-Saturation|Link1]], [[The-Peggy-Implementation|Link2]]
- **10.4 Eval and Pass** — design rationale for keeping $\text{eval}$/$\text{pass}$ separate rather than merging into a single node: it enables one-step loop peeling, a single per-loop node for the cost heuristic, and simpler restructuring for reversion. : [[Converting-Between-Imperative-Code-and-PEGs|Link1]], [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link2]], [[Program-Expression-Graphs-(PEGs)|Link3]], [[The-Peggy-Implementation|Link4]]

**Key Questions:**
1. Why does the linearity requirement on effect witnesses conflict with branch and loop fusion, and why can this conflict be unsolvable locally but solvable globally?
2. What specific problem does the Rete algorithm solve for the saturation engine, and why would naive "recheck everything" pattern matching be impractical?
3. Why does separating $\text{eval}$ and $\text{pass}$ make it easier for the global profitability heuristic to avoid selecting a mix of peeled and unpeeled loop versions?

---

### Chapter 11: Evaluation of Optimization (pp. 144–150)

**Summary:** Empirically validates that equality saturation is practical (time and space) and effective (produces both standard and unanticipated optimizations, including via user-supplied domain-specific axioms) using the Peggy implementation on SpecJVM and other benchmarks. : [[Empirical-Evaluation-of-Optimization|Link]]

**Key Definitions & Concepts:**
- Timing breakdown across Peggy's phases, showing the pseudo-boolean solver dominates runtime.
- 84% of methods fully saturate within a bounded heap; unsaturated cases still represent astronomically many program versions on average.
- A three-tier optimization taxonomy: basic equality analyses, emergent general optimizations that arise from combining them, and domain-specific optimizations from user-supplied axioms.
- A ray-tracer case study showing vector-object deforestation from simple axioms, outperforming an interprocedural optimizer on that idiom.
- The `contains`/`indexOf` idiom example, showing why a destructive rewrite rule would be unsafe while equality saturation's additive approach lets the profitability heuristic decide contextually.

**Key Questions:**
1. Why does Peggy's approach let it safely add an axiom like `l.contains(e) = (l.indexOf(e) != -1)` when a traditional destructive rewrite rule could not?
2. What does the fact that basic equality analyses generate complex emergent optimizations without any developer effort say about the value of a saturation-based architecture versus hand-written passes?

---

### Chapter 12: Translation Validation (pp. 151–159)

**Summary:** Shows equality saturation repurposed to prove two programs equivalent (translation validation) by building both programs' PEGs in one combined E-PEG and checking whether saturation unifies their return values and effects, validated against Soot and LLVM. : [[Translation-Validation|Link]]

**Key Definitions & Concepts by Section:**
- **12.1 Overview** — worked examples proving copy-propagation with dead-store elimination, redundant-load removal (justified by a read-only annotation on library functions), and loop-invariant code motion (validated purely by PEG conversion, with no saturation needed, because PEGs are code-placement-agnostic).
- **12.2 Implementation** — LLVM-specific load/store axioms requiring alias information; pre-computed alias analysis (rather than encoding aliasing as saturation axioms, for performance); proof generation as a byproduct, usable to prune which axioms matter for a given function. : [[The-Peggy-Implementation|Link]]
- **12.3 Results** — a 98% validation success rate across thousands of Soot-optimized methods, and a real compiler bug found in Soot (incorrectly hoisting a statement out of a loop, turning a terminating loop into an infinite one); LLVM/SPEC results; comparison against a prior linear-path translation validator that needs a rewrite ordering, unlike this approach.

**Key Questions:**
1. Why can PEG-based translation validation prove loop-invariant code motion correct without running equality saturation at all?
2. Why is exposing a real bug in Soot a meaningful validation of the approach's power beyond just optimization?

---

### Chapter 13: Learning Optimizations from Proofs (pp. 160–169)

**Summary:** Introduces the core idea of generalizing a single before/after optimization example into a broadly applicable, provably correct optimization rule by generalizing its proof of equivalence rather than the programs themselves. : [[Learning-Optimizations-from-Proofs|Link]]

**Key Definitions & Concepts by Section:**
- **13.1 Generalization Examples** — a worked loop-induction-variable strength reduction example generalizing constants to an arbitrary pure expression (weak logic) versus generalizing the operators themselves with side conditions such as distributivity, zero, and identity (stronger logic), showing that the axiom logic used determines generalization strength. : [[Evaluation-of-Learning|Link]]
- **13.2 Obtaining the Most General Form** — the splitting problem: naively turning shared E-PEG nodes into meta-variables under-generalizes, because shared nodes sometimes need to be split apart and independently constrained.
- **13.3 Our Approach** — the key algorithmic idea of working backward through the proof from a near-empty E-PEG, applying each axiom in reverse and only merging or constraining nodes when the proof structure demands it, which naturally resolves the splitting problem.
- **13.4 Decomposition** — splitting an overly specific learned rule into independent smaller optimizations by identifying "required" nodes belonging to the original and transformed programs and cutting the proof at equalities between them. : [[The-Peggy-Implementation|Link]]

**Key Questions:**
1. Why does simply replacing all nodes with meta-variables, ignoring proof structure, fail to produce the most general correct optimization rule?
2. Why does working backward from the conclusion, rather than forward from the concrete proof, resolve the "how much to split" problem?
3. In what sense does decomposition trade off the generality of a single learned rule for the broader applicability of several smaller rules?

---

### Chapter 14: Proofs in Categories (pp. 170–189)

**Summary:** Formalizes the entire proof-generalization algorithm from Chapter 13 using category theory, so that it is independent of any particular proof domain (E-PEGs, databases, type systems, and others) — the technical core of the thesis's learning contribution.

**Key Definitions & Concepts by Section:**
- **14.1 Overview of Category Theory** — category (objects, morphisms, composition, identity); commuting diagram; example categories including $\mathbf{Set}$ and a category of binary relations. : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
- **14.2 Encoding Axioms in Category Theory** — axioms as (often identity-carried) morphisms, with "satisfying an axiom" defined via a lifting or commuting-diagram condition.
- **14.3 Encoding Inference in Category Theory** — pushout (a universal gluing construction, notation $B +_A C$) used to formalize "applying an axiom" as gluing new information into an E-PEG; a full inference run is a chain of pushout squares, and this chain is the formal notion of proof in this framework. : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
- **14.4 Defining Generalization in Category Theory** — property as a morphism into the final result; pullback (the dual of pushout, identifying common structure, notation $B \times_D C$) used to isolate which part of the property the last axiom application contributed. : [[Domain-Independent-Applications-of-Generalization|Link]]
- **14.5 Constructing Generalizations using Categories** — pushout completion (notation $D -_A B$, "removes $B$'s structure from $D$ while keeping $A$'s"); a three-step recipe per axiom step (pullback, then pushout, then pushout completion), iterated backward through the whole proof chain, proven to yield the most general generalization. : [[Domain-Independent-Applications-of-Generalization|Link]]
- **14.6 Subpushout Completions** — relaxes the requirement that every axiom admit a pushout completion into a more permissive subpushout completion requirement satisfied by all morphisms in the relevant categories. : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
- **14.7 Proof of Generality** — the full inductive construction and correctness argument that the produced generalized proof is maximally general. : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]

**Key Questions:**
1. Why is a pushout the right categorical tool for "applying an axiom to learn new information," as opposed to a union or a commuting square?
2. Why does the pullback/pushout/pushout-completion process, applied backward through the whole proof, guarantee the most general possible generalization rather than merely a generalization?
3. What is a pushout completion intuitively subtracting, and why does not every axiom or category admit one?

---

### Chapter 15: E-PEG Instantiation (pp. 190–193)

**Summary:** Instantiates the abstract categorical framework of Chapter 14 concretely for E-PEGs (defining pullback, pushout, and pushout completion in E-PEG terms) and walks an earlier example through the full categorical machinery. : [[Translation-Validation|Link1]], [[The-Peggy-Implementation|Link2]]

**Key Definitions & Concepts:**
- The E-PEG category, whose objects are E-PEGs with free variables and whose morphisms are substitutions mapping free variables to nodes that preserve equivalences.
- Pullback in E-PEGs as intersection of sub-E-PEGs; pushout as unification along common substructure; pushout completion as removing conclusion-only equalities not present in the smaller E-PEG.
- Extensions allowing free variables to range over operators (enabling operator-generic rules) and allowing non-equality relations (such as an alias-analysis distinctness relation) to extend generalization beyond purely equality-based optimizations.

**Key Questions:**
1. Concretely, what does a pushout completion remove when instantiated on E-PEGs, and how does this correspond to "running an axiom in reverse"?
2. Why does allowing free variables to range over operators, not just nodes, require re-expressing the axioms themselves rather than just changing the E-PEG category definition?

---

### Chapter 16: More Applications of Generalization (pp. 194–205)

**Summary:** Demonstrates the domain-independence of the categorical generalization framework by applying it to three unrelated problems: database query optimization, type-error debugging, and automatic type polymorphization. : [[Domain-Independent-Applications-of-Generalization|Link]]

**Key Definitions & Concepts by Section:**
- **16.1 Database Query Optimization** — a conjunctive query represented as a small database, with query results corresponding to relation- and constant-preserving morphisms into a database instance; functional dependency and multi-valued dependency; "the chase" algorithm; the framework learns new equality-generating dependencies from one example run of the chase, avoiding redundant intermediate tuples in future queries. : [[Domain-Independent-Applications-of-Generalization|Link]]
- **16.2 Type Debugging** — a category of typed expressions whose objects need not be validly typed; typing rules as morphisms; backward generalization used to answer "why does this subexpression need this type?", pinpointing the true cause of a Hindley-Milner type error rather than the compiler's often-misleading reported location. : [[Domain-Independent-Applications-of-Generalization|Link]]
- **16.3 Type Polymorphization** — a category of typed expressions annotated with validity checkmarks; typing rules as validity-propagating morphisms; example of automatically generalizing a concrete numeric function into one polymorphic over any numeric type by generalizing the proof that the concrete instantiation type-checks. : [[Domain-Independent-Applications-of-Generalization|Link]]

**Key Questions:**
1. What single abstract algorithm from Chapter 14 makes all three of database optimization, type debugging, and type polymorphization possible without redesigning the generalization procedure itself?
2. In the type-debugging example, why does generalizing backward through the proof pinpoint the bug better than the compiler's own error message?

---

### Chapter 17: Manipulating Proofs (pp. 206–211)

**Summary:** Describes three techniques for editing a proof before or during generalization to produce more broadly applicable learned optimizations: choosing a good linearization order for tree-shaped proofs, dropping irrelevant axiom applications, and cutting proofs into independently generalized lemmas. : [[Learning-Optimizations-from-Proofs|Link]]

**Key Definitions & Concepts by Section:**
- **17.1 Sequencing Axiom Applications** — coproduct (a categorical "sum type" with injections and case-matching) used to encode "parallel" axiom applications, such as sibling branches of a proof tree; a proof that sequential application of two axioms always generalizes at least as well as their parallelized combination, though no single sequential order may be universally optimal. : [[Learning-Optimizations-from-Proofs|Link]]
- **17.2 Removing Irrelevant Axiom Applications** — since generalization proceeds backward, steps that do not contribute to the property being generalized are automatically and cheaply skipped. : [[Learning-Optimizations-from-Proofs|Link]]
- **17.3 Decomposition** — formalizes the earlier decomposition idea categorically: a chosen set of "cut points" splits the proof into independently generalized lemmas wherever an intermediate property factors through them. : [[The-Peggy-Implementation|Link]]

**Key Questions:**
1. Why does sequencing two axiom applications always yield an equal-or-more-general result than parallelizing them, and why might no ordering still be best in all cases?
2. Why does proceeding backward through the proof make discarding irrelevant axiom applications a byproduct of the algorithm rather than requiring a separate relevance analysis?

---

### Chapter 18: Evaluation of Learning (pp. 212–220)

**Summary:** Empirically validates the proof-generalization technique via three experiments: learning new optimizations from single before/after examples, amortizing superoptimizer cost by learning fast rules from one superoptimizer run, and cross-training learned rules on unseen code using the same library. : [[Evaluation-of-Learning|Link]]

**Key Definitions & Concepts by Section:**
- **18.1 Extending the Compiler through Examples** — a list of learned optimizations most of which conventional compilers do not perform, including generalized inter-loop strength reduction, loop-operation factoring, and function-specific rules for library routines such as `pow`.
- **18.2 Learning from Superoptimizers** — using Peggy's own saturation-based superoptimization as the before/after source; some optimizations can only be learned this way since a superoptimizer alone cannot guess how to reassemble decomposed pieces into the target form; partial inlining (learning a fact enabled by inlining without needing to actually inline in the generated code); an amortization result showing per-method compile time drops substantially using only the learned rules while producing the same output. : [[Learning-Optimizations-from-Proofs|Link]]
- **18.3 Cross-Training** — training on one vector-heavy method and successfully, partially optimizing an unrelated method in the same codebase; combining learned rules with simplification-only axioms recovers the full speedup, showing that learned "large-step" rules compose well with safe simplification axioms. : [[Evaluation-of-Learning|Link]]

**Key Questions:**
1. Why can a superoptimizer alone not discover a rule like `pow(a,p)*pow(b,p) = pow(a*b,p)`, even though equality saturation can prove the two forms equivalent once both are given?
2. What does partial inlining reveal about the relationship between what saturation explores and what the profitability heuristic ultimately selects?
3. What does the cross-training result suggest about how stylized real-world library usage needs to be for this learning technique to generalize across call sites?

---

### Chapter 19: Related Work (pp. 221–229)

**Summary:** Surveys prior work across superoptimizers, rewrite-based optimizers, phase-ordering research, translation validation, alternative intermediate representations, theorem proving, extensible optimizers, explanation-based learning, and machine-learning-based compiler heuristics, positioning equality saturation and proof generalization relative to each. : [[Related-Work-and-Positioning|Link]]

**Key Definitions & Concepts:**
- Superoptimizers — inspiration for the additive-equality/E-graph idea, but limited to straight-line code, whereas PEGs extend this to loops and branches at the cost of a coarser cost model.
- Rewrite-based optimizers — destructive and ordering-dependent, contrasted with the order-irrelevant additive approach of this thesis.
- Value Dependence Graph (VDG) — the closest prior IR, using lambda-abstraction for loops, which the author argues introduces problematic intermediate variables requiring costly substitution reasoning during saturation, motivating the variable-free $\theta$/$\text{eval}$/$\text{pass}$ design.
- Program Dependence Graph/Web and Dependence Flow Graphs — statement-based or side-effecting alternatives contrasted with PEGs' fully functional, CFG-independent representation.
- Lucid — a dataflow language whose `first`/`next`/`as soon as` constructs closely resemble $\theta$/$\text{eval}$/$\text{pass}$, but designed for proof rather than optimization.
- Theorem proving and E-graphs — the direct ancestor of E-PEGs.
- Explanation-based learning — the AI-research category proof generalization belongs to.
- Machine learning in compilers — complementary, since it learns profitability heuristics rather than transformation rules.
- Optimization inference — a prior superoptimizer with simple constant/register-name generalization, contrasted with the proof-structure-driven generalization of this thesis.

**Key Questions:**
1. Why does the author argue that lambda-based loop representations, as in VDGs, are fundamentally at odds with efficient equality saturation, while PEGs avoid this problem?
2. In what precise sense is this thesis's machine-learning contribution complementary to, rather than competing with, statistical or reinforcement-learning-based compiler heuristic learning?

---

### Chapter 20: Conclusion (pp. 230–232)

**Summary:** Recaps PEGs as the central contribution enabling algebraic reasoning over entire CFGs rather than just straight-line code, reflects on unresolved interprocedural-optimization challenges and the practical gap between this approach and conventional optimizers, and closes with a personal reflection on category theory's unexpected value across the author's work.

**Key Definitions & Concepts:**
- PEGs restated as the key enabling representation for algebraic, equational reasoning over control flow.
- Two open obstacles to interprocedural optimization: the lack of a known algebraic, intermediate-variable-free interprocedural representation, and the combinatorial explosion of program size and search space with too little guidance on where interprocedural transformations help.
- Integration with conventional optimization pipelines named as the biggest practical gap and stated future direction.
- A personal account of category theory repeatedly providing high-level abstraction that transferred across unrelated projects beyond this dissertation.

**Key Questions:**
1. Why does the author consider the lack of an algebraic interprocedural representation more fundamentally insurmountable than the search-space problem?
2. What does the author's account of category theory transferring across unrelated problems suggest about the actual contribution of the categorical framework, beyond just formalizing E-PEG generalization?

---

### Appendix A: Axioms (pp. 233–243)

**Summary:** Catalogs the general-purpose and domain-specific axioms actually used to produce the optimizations evaluated in Chapter 11, organized into built-in E-PEG operator axioms, code-pattern axioms, basic arithmetic, and Java-specific axioms, followed by inlining, read-only, vector, design-pattern, and specialization axioms.

**Key Definitions & Concepts by Section:**
- **A.1 General-Purpose Axioms** — loop-liftedness (a formal definition of which operators can distribute through loop-lifted constructs); built-in E-PEG axioms, such as distributing any lifted operator through $\theta_\ell$ or $\phi$; code-pattern axioms expressed as source-level rewrites, such as entire-loop unrolling and loop peeling; basic arithmetic axioms including distributivity, commutativity, identities, and comparison identities; Java-specific axioms for array and field reads and writes, including read-after-write, independent-location commutativity, and write-after-write overwrite.
- **A.2 Domain-Specific Axioms** — inlining expressed as one large axiom; read-only annotations on library methods that do not modify the heap; immutable-vector axioms relating getters, fields, and arithmetic operations; design-pattern axioms, such as an integer-wrapper class or a `contains`/`indexOf` equivalence; method outlining (replacing a hand-written algorithm with a library call); specialized redirect (annotating a result with a property established by a called routine, such as being sorted).

**Key Questions:**
1. Why is loop-liftedness defined via two separate implication conditions, and what would go wrong with distributing a non-loop-lifted operator through $\theta_\ell$ or $\text{eval}_\ell$?
2. What distinguishes a general-purpose axiom from a domain-specific one in this appendix's organization, and why must the vector and design-pattern axioms remain domain-specific rather than being built into Peggy's core?
