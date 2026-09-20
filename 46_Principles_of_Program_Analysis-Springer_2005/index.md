# Principles of Program Analysis — Index

[[book-guidelines|↩ Back to guidelines]]

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
