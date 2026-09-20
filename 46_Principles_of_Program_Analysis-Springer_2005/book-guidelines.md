# Principles of Program Analysis — Guidelines

## Header

**Title:** Principles of Program Analysis
**Author(s):** Flemming Nielson, Hanne Riis Nielson, Chris Hankin
**Publication:** Springer, 1999 (corrected 2nd printing, 2005)

**Brief Summary:**
The book is a graduate-level textbook covering the four main approaches to static program analysis — Data Flow Analysis, Constraint Based Analysis, Abstract Interpretation, and Type and Effect Systems — treated as variations on a common theme rather than as unrelated techniques. Each approach is developed on a shared pair of example languages (the imperative language WHILE and the functional language FUN), with parallel treatment of specification, semantic correctness (with respect to an operational semantics), and algorithms for computing the analysis. A concluding chapter on generic worklist algorithms and three appendices (partial orders/lattices, induction and coinduction, graphs and regular expressions) supply the shared mathematical infrastructure.

**Intent of the Author:**
The authors set out to write the textbook they lacked for their own courses, and — more ambitiously — to counter the tendency of program-analysis subcommunities to treat their own techniques as unrelated to the others. Their explicit aim is to convince the reader that Data Flow Analysis, Constraint Based Analysis, Abstract Interpretation, and Type and Effect Systems are deeply interconnected (via equations vs. constraints, monotone frameworks, Galois connections, and shared worklist algorithms) and that insights from one approach routinely strengthen another.

---

## Topic List

1. **The Nature and Scope of Program Analysis** : [[The-Nature-and-Scope-of-Program-Analysis|Link]]
   - Static compile-time prediction of run-time behavior
   - Safe approximation and the tradeoff between precision and computability
   - Semantics-based versus semantics-directed analysis : [[The-Nature-and-Scope-of-Program-Analysis|Link]]
   - Program analysis as a basis for code transformation and optimization : [[The-Nature-and-Scope-of-Program-Analysis|Link]]

2. **The WHILE and FUN Model Languages** : [[The-WHILE-and-FUN-Model-Languages|Link]]
   - Labelled abstract syntax and elementary blocks : [[The-WHILE-and-FUN-Model-Languages|Link]]
   - Structural Operational Semantics for WHILE : [[The-WHILE-and-FUN-Model-Languages|Link]]
   - The FUN functional language with labelled terms : [[The-WHILE-and-FUN-Model-Languages|Link]]
   - Extensions of FUN with references, exceptions, regions, and concurrency

3. **Data Flow Analysis** : [[Data-Flow-Analysis|Link]]
   - Flow graphs, init, final, blocks, and flow functions
   - Available Expressions Analysis : [[Data-Flow-Analysis|Link]]
   - Reaching Definitions Analysis : [[Data-Flow-Analysis|Link]]
   - Very Busy Expressions Analysis : [[Data-Flow-Analysis|Link]]
   - Live Variables Analysis : [[Data-Flow-Analysis|Link]]
   - Use-Definition and Definition-Use chains
   - Forward versus backward, may versus must, flow-sensitive versus flow-insensitive analyses

4. **Monotone Frameworks** : [[Monotone-Frameworks|Link]]
   - Property spaces as complete lattices satisfying the Ascending Chain Condition
   - Transfer functions and the space of monotone functions
   - Distributive frameworks : [[Monotone-Frameworks|Link]]
   - Instances of a Monotone Framework : [[Monotone-Frameworks|Link]]
   - The MFP (Maximal Fixed Point) worklist algorithm : [[Algorithms-for-Solving-Analysis-Equations|Link]]
   - The MOP (Meet Over all Paths) solution and its undecidability
   - Comparing MFP and MOP solutions : [[Interprocedural-Data-Flow-Analysis|Link]]

5. **Interprocedural Data Flow Analysis** : [[Interprocedural-Data-Flow-Analysis|Link]]
   - Extending WHILE with procedures and call-by-value/call-by-result parameters : [[Interprocedural-Data-Flow-Analysis|Link]]
   - Interprocedural flow and the call/return matching problem : [[Interprocedural-Data-Flow-Analysis|Link]]
   - Complete paths, valid paths, and the MVP solution : [[Interprocedural-Data-Flow-Analysis|Link]]
   - Context information via embellished Monotone Frameworks : [[Interprocedural-Data-Flow-Analysis|Link]]
   - Call strings as context : [[Context-Sensitivity-in-Control-Flow-Analysis|Link1]], [[Interprocedural-Data-Flow-Analysis|Link2]]
   - Assumption sets as context : [[Interprocedural-Data-Flow-Analysis|Link]]
   - Context-sensitive versus context-insensitive analysis : [[Context-Sensitivity-in-Control-Flow-Analysis|Link]]
   - Flow-insensitive analysis of assigned variables : [[Interprocedural-Data-Flow-Analysis|Link]]

6. **Shape Analysis** : [[Shape-Analysis|Link]]
   - A pointer-manipulating extension of WHILE with malloc and selectors
   - Structural Operational Semantics with a heap component : [[The-WHILE-and-FUN-Model-Languages|Link]]
   - Shape graphs: abstract locations, abstract states, abstract heaps
   - The abstract summary location and sharing information : [[Shape-Analysis|Link]]
   - Compatible shape graphs and their invariants : [[Shape-Analysis|Link]]

7. **Control Flow Analysis (0-CFA and Constraint Based Analysis)** : [[Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)|Link]]
   - The dynamic dispatch problem in higher-order and object-oriented languages
   - Abstract caches and abstract environments : [[Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)|Link]]
   - The acceptability relation for 0-CFA : [[Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)|Link]]
   - Coinduction versus induction in defining the analysis : [[Induction-and-Coinduction|Link]]
   - Syntax directed 0-CFA analysis : [[Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)|Link1]], [[Induction-and-Coinduction|Link2]], [[The-Nature-and-Scope-of-Program-Analysis|Link3]]
   - Constraint based 0-CFA analysis and constraint generation : [[Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)|Link1]], [[Induction-and-Coinduction|Link2]]
   - Solving constraints via a worklist algorithm : [[Algorithms-for-Solving-Analysis-Equations|Link]]

8. **Combining Control Flow and Data Flow Analysis** : [[Combining-Control-Flow-and-Data-Flow-Analysis|Link]]
   - Abstract values as powersets of terms and data : [[Combining-Control-Flow-and-Data-Flow-Analysis|Link]]
   - Abstract values as complete lattices (monotone structures) : [[Combining-Control-Flow-and-Data-Flow-Analysis|Link1]], [[Partially-Ordered-Sets-and-Complete-Lattices|Link2]]
   - Flow-sensitivity in Control Flow Analysis : [[Context-Sensitivity-in-Control-Flow-Analysis|Link]]
   - Staging control flow and data flow constraint solving : [[Combining-Control-Flow-and-Data-Flow-Analysis|Link1]], [[Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)|Link2]]

9. **Context Sensitivity in Control Flow Analysis** : [[Context-Sensitivity-in-Control-Flow-Analysis|Link]]
   - Monovariant versus polyvariant analysis
   - k-CFA analysis : [[Shape-Analysis|Link1]], [[Context-Sensitivity-in-Control-Flow-Analysis|Link2]], [[Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)|Link3]], [[Data-Flow-Analysis|Link4]]
   - Uniform k-CFA analysis : [[Context-Sensitivity-in-Control-Flow-Analysis|Link]]
   - The Cartesian Product Algorithm : [[Context-Sensitivity-in-Control-Flow-Analysis|Link]]
   - Set-Constraint Based Analysis : [[Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)|Link1]], [[Induction-and-Coinduction|Link2]]

10. **Abstract Interpretation** : [[Abstract-Interpretation|Link]]
    - Correctness relations and representation functions : [[Abstract-Interpretation|Link]]
    - First-order versus second-order analyses
    - Approximation of fixed points : [[Abstract-Interpretation|Link1]], [[Partially-Ordered-Sets-and-Complete-Lattices|Link2]]
    - Widening operators
    - Narrowing operators
    - Galois connections and adjunctions : [[Abstract-Interpretation|Link1]], [[Induction-and-Coinduction|Link2]]
    - Galois insertions and reduction operators
    - Systematic design of Galois connections (independent attribute method, relational method, direct product, total and monotone function spaces)
    - Inducing an analysis along an abstraction function : [[Abstract-Interpretation|Link]]
    - Upper closure operators
    - Lattice duality

11. **Type and Effect Systems** : [[Type-and-Effect-Systems|Link]]
    - Annotated type systems versus effect systems : [[Type-and-Effect-Systems|Link]]
    - The underlying (ordinary) type system : [[Type-and-Effect-Systems|Link]]
    - Annotated types for Control Flow Analysis : [[Context-Sensitivity-in-Control-Flow-Analysis|Link1]], [[Type-and-Effect-Systems|Link2]]
    - Subeffecting and subtyping
    - Shape conformant subtyping
    - Semantic correctness via subject reduction and Natural Semantics : [[Type-and-Effect-Systems|Link]]
    - Syntactic soundness and completeness of an inference algorithm (Algorithm W variants) : [[Type-and-Effect-Systems|Link]]

12. **Effects Beyond Control Flow** : [[Effects-Beyond-Control-Flow|Link]]
    - Side Effect Analysis for a language with reference variables : [[Effects-Beyond-Control-Flow|Link]]
    - Exception Analysis with polymorphism and type schemes : [[Type-and-Effect-Systems|Link1]], [[Effects-Beyond-Control-Flow|Link2]]
    - Region Inference for stack-based memory management : [[Effects-Beyond-Control-Flow|Link]]
    - Communication Analysis and behaviours for a concurrent language : [[Effects-Beyond-Control-Flow|Link]]
    - Temporal ordering of effects and behaviour algebra : [[Graphs-and-Regular-Expressions|Link1]], [[Effects-Beyond-Control-Flow|Link2]]

13. **Algorithms for Solving Analysis Equations** : [[Algorithms-for-Solving-Analysis-Equations|Link]]
    - Constraint systems and flow variables : [[Algorithms-for-Solving-Analysis-Equations|Link]]
    - The abstract worklist algorithm : [[Algorithms-for-Solving-Analysis-Equations|Link]]
    - LIFO and FIFO iteration strategies
    - Reverse postorder iteration : [[Algorithms-for-Solving-Analysis-Equations|Link]]
    - The Round Robin Algorithm : [[Graphs-and-Regular-Expressions|Link]]
    - Iterating through strong components : [[Algorithms-for-Solving-Analysis-Equations|Link]]
    - Complexity bounds via loop connectedness : [[Graphs-and-Regular-Expressions|Link]]

14. **Partially Ordered Sets and Complete Lattices** : [[Partially-Ordered-Sets-and-Complete-Lattices|Link]]
    - Partial orders, upper and lower bounds, Moore families : [[Partially-Ordered-Sets-and-Complete-Lattices|Link]]
    - Construction of complete lattices (Cartesian product, total and monotone function spaces) : [[Partially-Ordered-Sets-and-Complete-Lattices|Link]]
    - Ascending and Descending Chain Conditions
    - Tarski's Fixed Point Theorem : [[Partially-Ordered-Sets-and-Complete-Lattices|Link]]
    - Least and greatest fixed points

15. **Induction and Coinduction** : [[Induction-and-Coinduction|Link]]
    - Mathematical, structural, course-of-values, and well-founded induction
    - Least fixed points as inductive definitions
    - Greatest fixed points as coinductive definitions
    - The coinduction proof principle : [[Induction-and-Coinduction|Link]]

16. **Graphs and Regular Expressions** : [[Graphs-and-Regular-Expressions|Link]]
    - Directed graphs, paths, and cycles
    - Strongly connected components and the reduced graph
    - Handles, roots, and dominators
    - Depth-first spanning forests and reverse postorder : [[Graphs-and-Regular-Expressions|Link]]
    - Reducible graphs and the loop connectedness parameter : [[Graphs-and-Regular-Expressions|Link]]
    - Regular expressions and homomorphisms : [[Graphs-and-Regular-Expressions|Link]]

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 1–33)

**Summary:** A gentle, worked-example tour of all four main approaches to program analysis (Data Flow, Constraint Based, Abstract Interpretation, Type and Effect Systems) applied to Reaching Definitions and Control Flow Analysis, meant to be read quickly before specializing into later chapters.

**Key Definitions & Concepts by Section:**
- **1.1 The Nature of Program Analysis** — safe approximation (erring on the side of over-approximation), semantics-based analysis : [[The-Nature-and-Scope-of-Program-Analysis|Link]]
- **1.2 Setting the Scene** — the WHILE language, labelled elementary blocks, abstract syntax
- **1.3 Data Flow Analysis** — Reaching Definitions Analysis, the equational approach (least solution via Chaotic Iteration), the constraint based approach : [[Data-Flow-Analysis|Link]]
- **1.4 Constraint Based Analysis** — Control Flow Analysis for a functional language, abstract cache $\mathcal{C}$, abstract environment $\rho$, conditional constraints : [[Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)|Link1]], [[Induction-and-Coinduction|Link2]]
- **1.5 Abstract Interpretation** — collecting semantics, semantically reaching definitions $SRD$, Galois connections $(\alpha, \gamma)$, induced analysis $\hat\alpha \circ G \circ \hat\gamma$ : [[Abstract-Interpretation|Link]]
- **1.6 Type and Effect Systems** — annotated base types, annotated type constructors, Call-Tracking Analysis as an Effect System : [[Type-and-Effect-Systems|Link]]
- **1.7 Algorithms** — Chaotic Iteration
- **1.8 Transformations** — Constant Folding as a source-to-source transformation driven by Reaching Definitions

**Key Questions:**
1. Why must a program analysis prefer a safe over-approximation to an exact answer, and why is "erring too far" also a problem?
2. How does the equational formulation of Reaching Definitions relate to its constraint based formulation, and why do they have the same least solution?
3. What role does the Galois connection $(\alpha, \gamma)$ play in showing that a hand-specified analysis (like Reaching Definitions) is correct with respect to the collecting semantics?

---

### Chapter 2: Data Flow Analysis (pp. 35–140)

**Summary:** Develops classical intraprocedural Data Flow Analysis for WHILE (Available Expressions, Reaching Definitions, Very Busy Expressions, Live Variables), proves correctness of Live Variables Analysis against a Structural Operational Semantics, unifies the four analyses as instances of a Monotone Framework, presents the MFP worklist algorithm and the MOP solution, then extends to interprocedural analysis (call strings, assumption sets) and to Shape Analysis of heap-manipulating programs. : [[Data-Flow-Analysis|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 Intraprocedural Analysis** — init, final, blocks, flow, flow$^R$; Available Expressions Analysis (kill/gen, largest solution); Reaching Definitions Analysis (smallest solution); Very Busy Expressions Analysis; Live Variables Analysis; Use-Definition (ud) and Definition-Use (du) chains : [[Interprocedural-Data-Flow-Analysis|Link]]
- **2.2 Theoretical Properties** — Structural Operational Semantics of WHILE; the correctness relation $\sigma_1 \sim_V \sigma_2$; Theorem 2.21 (preservation of correctness under execution)
- **2.3 Monotone Frameworks** — property space $L$ with the Ascending Chain Condition, transfer function space $F$, Distributive Framework, the four classical analyses recast as instances, Constant Propagation as a non-distributive example : [[Monotone-Frameworks|Link]]
- **2.4 Equation Solving** — the MFP solution (worklist algorithm, Table 2.8), paths and the MOP solution, undecidability of MOP for Constant Propagation, MFP $\sqsupseteq$ MOP in general and MFP = MOP for distributive frameworks : [[Algorithms-for-Solving-Analysis-Equations|Link1]], [[Data-Flow-Analysis|Link2]], [[Monotone-Frameworks|Link3]]
- **2.5 Interprocedural Analysis** — procedure declarations, interprocedural flow, complete paths and valid paths, the MVP solution, embellished Monotone Frameworks with context $\delta \in \Delta$, call strings (unbounded and bounded length $k$), assumption sets (large and small), flow-sensitivity versus flow-insensitivity, the procedure call graph : [[Interprocedural-Data-Flow-Analysis|Link]]
- **2.6 Shape Analysis** — heap-extended WHILE with malloc and selectors, abstract locations $n_X$ and the summary location $n_\emptyset$, abstract states $S$, abstract heaps $H$, sharing information $is$, the five compatibility invariants, the complete lattice of shape graphs $\mathcal{P}(SG)$ : [[Shape-Analysis|Link]]

**Key Questions:**
1. Why does Available Expressions Analysis require the *largest* solution to its equations while Reaching Definitions requires the *smallest*, and how does this connect to may- versus must-analysis?
2. What breaks when procedure calls and returns are treated "naively" as ordinary goto-like flow edges, and how do valid paths (via the MVP solution) and call strings restore correctness?
3. Why is a single abstract location insufficient to represent the heap, and what problem does the sharing component $is$ solve that the abstract heap $H$ alone cannot?

---

### Chapter 3: Constraint Based Analysis (pp. 141–210)

**Summary:** Develops Control Flow Analysis (0-CFA) for the functional language FUN as an abstract acceptability relation defined by coinduction, then refines it in stages — syntax directed specification, constraint generation, and constraint solving — before extending it with Data Flow Analysis components and context sensitivity (k-CFA, the Cartesian Product Algorithm). : [[Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)|Link1]], [[Induction-and-Coinduction|Link2]]

**Key Definitions & Concepts by Section:**
- **3.1 Abstract 0-CFA Analysis** — abstract cache $\hat C$, abstract environment $\hat\rho$, the acceptability relation $(\hat C,\hat\rho)\models e$ (Table 3.1), well-definedness via coinduction (greatest fixed point of a functional $Q$) : [[Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)|Link1]], [[Induction-and-Coinduction|Link2]]
- **3.2 Theoretical Properties** — Structural Operational Semantics of FUN with closures and environments, semantic correctness (subject reduction), existence of solutions as a Moore family, coinduction versus induction (why the greatest, not least, fixed point is needed)
- **3.3 Syntax Directed 0-CFA Analysis** — the relation $\models_s$, analysing each function body exactly once, preservation of solutions with respect to Table 3.1 : [[Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)|Link1]], [[Induction-and-Coinduction|Link2]], [[The-Nature-and-Scope-of-Program-Analysis|Link3]]
- **3.4 Constraint Based 0-CFA Analysis** — constraints and conditional constraints $\{t\}\subseteq \text{rhs}' \Rightarrow \text{lhs}\subseteq\text{rhs}$, the constraint generation function $\mathcal{C}_*$, solving constraints via a graph/worklist algorithm : [[Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)|Link1]], [[Induction-and-Coinduction|Link2]]
- **3.5 Adding Data Flow Analysis** — abstract values as powersets $\mathcal{P}(\text{Term}\cup\text{Data})$; abstract values as complete lattices (monotone structures); staging control flow before data flow : [[Data-Flow-Analysis|Link1]], [[Combining-Control-Flow-and-Data-Flow-Analysis|Link2]], [[Interprocedural-Data-Flow-Analysis|Link3]]
- **3.6 Adding Context Information** — monovariant versus polyvariant analysis, k-CFA analysis, uniform k-CFA analysis, the Cartesian Product Algorithm

**Key Questions:**
1. Why must the acceptability relation $\models$ for 0-CFA be defined as a *greatest* fixed point rather than a least one, and what concrete example (e.g. the looping program) forces this choice?
2. How does the syntax directed specification $\models_s$ guarantee termination of analysis (each function body analysed once) while still remaining a safe approximation of the abstract specification $\models$?
3. What is lost when Control Flow Analysis is made context-insensitive (0-CFA), and how do call strings/k-CFA recover precision at the cost of analysis size?

---

### Chapter 4: Abstract Interpretation (pp. 211–282)

**Summary:** Presents Abstract Interpretation in a language-independent style: correctness of an analysis is first related to a semantics via correctness relations or representation functions; widening and narrowing operators are introduced to force convergence of fixed-point computations over infinite-height lattices; Galois connections and insertions formalize how one property space safely approximates another and can be constructed systematically and used to induce new analyses from existing ones. : [[Abstract-Interpretation|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 A Mundane Approach to Correctness** — correctness relation $R : V\times L \to \{\text{true},\text{false}\}$, representation function $\beta : V \to L$, equivalence of the two correctness formulations (Lemma 4.5), first-order versus second-order analyses
- **4.2 Approximation of Fixed Points** — the interval lattice as a running example; fixed points, $\text{Fix}(f)$, $\text{Red}(f)$, $\text{Ext}(f)$; widening operators $\nabla$ and the sequence $f^\nabla_n$; narrowing operators $\Delta$ and the sequence $[f]^\Delta_n$ : [[Abstract-Interpretation|Link1]], [[Partially-Ordered-Sets-and-Complete-Lattices|Link2]]
- **4.3 Galois Connections** — abstraction $\alpha$ and concretisation $\gamma$, the adjunction condition $\alpha(l)\sqsubseteq m \Leftrightarrow l \sqsubseteq \gamma(m)$, Galois connections from extraction functions, properties (Lemma 4.22–4.24), Galois insertions (no superfluous elements of $M$), the reduction operator $\varsigma$ : [[Abstract-Interpretation|Link]]
- **4.4 Systematic Design of Galois Connections** — sequential composition, independent attribute method, relational method, direct product, total function space, monotone function space : [[Abstract-Interpretation|Link]]
- **4.5 Induced Operations** — inducing an analysis along the abstraction function ($g_p = \alpha_2\circ f_p\circ\gamma_1$), optimality of a transfer function, generalised Monotone Frameworks, inducing along the concretisation function

**Key Questions:**
1. What exactly do the two conditions on widening ($\sqcup$-type upper bound, plus eventual stabilisation on ascending chains) buy us, and why is narrowing not simply the dual notion?
2. Why are Galois connections, rather than arbitrary pairs of monotone functions, the "right" formalisation of "$M$ safely approximates $L$" — what does the adjunction law guarantee that a weaker relationship would not?
3. When is the independent attribute method for combining two Galois connections strictly less precise than the relational method, and why (e.g. for the property `(x, -x)`)?

---

### Chapter 5: Type and Effect Systems (pp. 283–364)

**Summary:** Recasts Control Flow Analysis as an Annotated Type System over FUN, proves its semantic soundness via a Natural Semantics and gives a sound-and-complete inference algorithm, then generalises to full Type and Effect Systems with subtyping and polymorphism through three case studies (Side Effect Analysis, Exception Analysis, Region Inference) and a richer temporal analysis (Communication Analysis with behaviours). : [[Type-and-Effect-Systems|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Control Flow Analysis** — the underlying type system for FUN, annotated types $\hat\tau_1 \xrightarrow{\varphi} \hat\tau_2$, subeffecting, the judgement $\Gamma \vdash_{CFA} e : \hat\tau \,\&\, \varphi$ : [[Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)|Link]]
- **5.2 Theoretical Properties** — Natural Semantics for FUN, semantic correctness (subject reduction), existence of solutions as a Moore family
- **5.3 Inference Algorithms** — Algorithm $\mathcal{W}$ for the underlying type system, Algorithm $\mathcal{W}_{CFA}$ for Control Flow Analysis, syntactic soundness and completeness : [[Type-and-Effect-Systems|Link]]
- **5.4 Effects** — Side Effect Analysis (reference variables, annotations $!\pi$, $\pi{:=}$, $\text{new}_\pi$, shape conformant subtyping); Exception Analysis (polymorphic type schemes $\forall(\zeta_1,\ldots,\zeta_n).\hat\tau$, generalisation [gen] and instantiation [ins] rules); Region Inference (polymorphic recursion, stack-based memory management)
- **5.5 Behaviours** — Communication Analysis for a concurrent extension of FUN (channels, spawn, send/receive), behaviours as a temporal effect algebra with sequencing, choice, and recursion, the ordering $\varphi \sqsubseteq \varphi'$ on behaviours : [[Effects-Beyond-Control-Flow|Link]]

**Key Questions:**
1. In what sense is the Control Flow Analysis of Section 5.1 "the same" analysis as the 0-CFA of Chapter 3, and what does casting it as a type system buy in terms of proof technique (subject reduction vs. coinductive acceptability)?
2. Why is a combined subeffecting-and-subtyping rule [sub] needed to obtain a conservative extension of the underlying type system, and what would go wrong with only one of the two?
3. How do behaviours (Section 5.5) generalise ordinary effects to capture *temporal order*, and why does this matter for a Communication Analysis specifically?

---

### Chapter 6: Algorithms (pp. 365–392)

**Summary:** Abstracts away the specific analysis and studies general algorithms for solving systems of (in)equations over flow variables in a complete lattice, showing how careful organisation of the worklist — reverse postorder, and iteration through strong components — improves practical (and sometimes provable) performance over naive LIFO/FIFO strategies.

**Key Definitions & Concepts by Section:**
- **6.1 Worklist Algorithms** — constraint systems $(x_i \sqsupseteq t_i)_{i=1}^N$, the abstract worklist algorithm (Table 6.1) with `insert`/`extract`, correctness via Tarski's Fixed Point Theorem, LIFO and FIFO extraction : [[Algorithms-for-Solving-Analysis-Equations|Link]]
- **6.2 Iterating in Reverse Postorder** — the graph structure $G_S$ of a constraint system, handles, depth-first spanning forests, extraction based on reverse postorder, the Round Robin Algorithm, the loop connectedness parameter $d(G_S,T)$ and its complexity bound : [[Algorithms-for-Solving-Analysis-Equations|Link]]
- **6.3 Iterating Through Strong Components** — the reduced graph as a DAG, topological ordering of strong components, srPostorder numbering, the three-level (component / pass / node) iteration strategy : [[Algorithms-for-Solving-Analysis-Equations|Link]]

**Key Questions:**
1. Why does the correctness proof of the abstract worklist algorithm (Lemma 6.4) go through unchanged regardless of which concrete `insert`/`extract` strategy is plugged in, and what does this tell you about where the "interesting" work of algorithm design lives?
2. How does reverse postorder iteration reduce the number of re-evaluations compared to LIFO, and why is the loop connectedness parameter $d(G_S,T)$ the right complexity measure for the Round Robin Algorithm?
3. What extra structure does iterating through strong components exploit that plain reverse postorder does not?

---

### Appendix A: Partially Ordered Sets (pp. 393–404)

**Summary:** Reviews the lattice-theoretic infrastructure used throughout the book: constructions of complete lattices, the Ascending/Descending Chain Conditions, and Tarski's Fixed Point Theorem.

**Key Definitions & Concepts:**
- **A.1 Basic Definitions** — partially ordered set, complete lattice, Moore family, monotone/additive/completely additive functions, isomorphism
- **A.2 Construction of Complete Lattices** — Cartesian product, total function space $S \to L$, monotone function space $L_1 \to L_2$
- **A.3 Chains** — ascending/descending chains, Ascending/Descending Chain Condition, finite height, Lemma A.8 (equivalent characterisation of a complete lattice with ACC)
- **A.4 Fixed Points** — reductive/extensive functions, $\text{lfp}(f)$, $\text{gfp}(f)$, Tarski's Fixed Point Theorem (Proposition A.10)

**Key Questions:**
1. Why is "having a least element and binary least upper bounds plus the Ascending Chain Condition" (Lemma A.8) an equivalent, often more convenient, characterisation of a complete lattice satisfying ACC?
2. What does Tarski's Fixed Point Theorem guarantee that mere existence of *a* fixed point would not?

---

### Appendix B: Induction and Coinduction (pp. 405–416)

**Summary:** Reviews classical inductive proof principles and then motivates and formalises coinduction as reasoning about greatest fixed points, using a running example (predicates $Q_0$–$Q_3$) to show exactly when induction fails and coinduction succeeds.

**Key Definitions & Concepts:**
- **B.1 Proof by Induction** — mathematical induction, structural induction, induction on the shape of inference trees, course-of-values induction, well-founded induction
- **B.2 Introducing Coinduction** — the motivating example ($f_0$–$f_3$), rewriting recursive definitions as a functional $Q$, least fixed point corresponding to inductive proof, greatest fixed point corresponding to coinductive proof
- **B.3 Proof by Coinduction** — the coinduction proof rule ($Q' \sqsubseteq Q(Q') \Rightarrow Q' \sqsubseteq Q$), the derived rule using $Q \cup Q'$, extension to relations

**Key Questions:**
1. In the motivating example, why does $f_3$ resist both an inductive base case *and* an inductive step, yet is intuitively "safe" — and how does the coinductive reading of $Q_3$ make this precise?
2. What does it mean, operationally, to "assume the desired result in order to prove it" in a coinductive proof, and why is this not circular reasoning?

---

### Appendix C: Graphs and Regular Expressions (pp. 417–428)

**Summary:** Supplies the graph-theoretic vocabulary (strong components, handles, dominators, depth-first spanning forests, reducibility) underlying the interprocedural and algorithmic chapters, plus a brief review of regular expressions and homomorphisms used in the mini projects.

**Key Definitions & Concepts:**
- **C.1 Graphs and Forests** — directed graphs, paths, cycles, strongly connected components and the reduced graph (always a DAG), handles and roots, minimal handles, forests/trees, dominators
- **C.2 Reverse Postorder** — the DFSF algorithm (Table C.1), tree/forward/back/cross edges, Lemma C.9 (back edges characterised by reverse postorder), the loop connectedness parameter, reducible graphs, dominator-back edges
- **C.3 Regular Expressions** — regular expressions over an alphabet, the language $\mathcal{L}[R]$ of a regular expression, homomorphisms between alphabets and their extension to regular expressions

**Key Questions:**
1. Why is the reduced graph of strong components guaranteed to be acyclic (a DAG), and what does this buy for topologically ordering the analysis of a constraint system?
2. What distinguishes a *reducible* graph from an irreducible one, and why does reducibility make the loop connectedness parameter independent of the chosen depth-first spanning forest?
