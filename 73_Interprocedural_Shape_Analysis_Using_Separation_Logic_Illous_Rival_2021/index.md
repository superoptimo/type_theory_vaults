# Interprocedural Shape Analysis Using Separation Logic-based Transformer Summaries — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Interprocedural Analysis via Procedure Summaries** : [[Interprocedural-Analysis-via-Procedure-Summaries|Link]]
   - The relational approach to interprocedural analysis : [[Modular-Interprocedural-Call-Analysis|Link]]
   - State analyses versus transformation analyses : [[Interprocedural-Analysis-via-Procedure-Summaries|Link]]
   - Tabulation of pre/post-condition pairs and its precision limits
   - Global transformation summaries : [[Relational-Shape-Abstraction-Transformation-Domain|Link1]], [[Intraprocedural-Transformation-Analysis|Link2]]
   - Context transformation summaries : [[Relational-Shape-Abstraction-Transformation-Domain|Link1]], [[Intraprocedural-Transformation-Analysis|Link2]]
   - Top-down versus bottom-up summary inference : [[Interprocedural-Analysis-via-Procedure-Summaries|Link]]

2. **Separation Logic for Shape Analysis** : [[Separation-Logic-for-Shape-Analysis|Link]]
   - Abstract heaps as separating conjunctions of region predicates
   - Points-to predicates over symbolic names
   - Summary predicates for list segments and singly-linked lists
   - Inductive unfolding of summary predicates : [[Separation-Logic-for-Shape-Analysis|Link]]
   - Concretization of abstract states via valuations : [[Separation-Logic-for-Shape-Analysis|Link]]

3. **Relational Shape Abstraction (Transformation Domain)** : [[Relational-Shape-Abstraction-Transformation-Domain|Link]]
   - Abstract transformations as identity, input-output pairs, and separating conjunction
   - The transformation-level separating connector distinguished from the state-level connector
   - Concretization of abstract transformations : [[Relational-Shape-Abstraction-Transformation-Domain|Link1]], [[Abstract-Intersection-and-Composition-Algorithms|Link2]], [[Separation-Logic-for-Shape-Analysis|Link3]]
   - Soundness statement for abstract transformer semantics : [[Relational-Shape-Abstraction-Transformation-Domain|Link]]
   - Widening over abstract transformations : [[Intraprocedural-Transformation-Analysis|Link1]], [[Relational-Shape-Abstraction-Transformation-Domain|Link2]], [[Abstract-Intersection-and-Composition-Algorithms|Link3]]
   - Inclusion testing over abstract transformations : [[Relational-Shape-Abstraction-Transformation-Domain|Link]]

4. **Intraprocedural Transformation Analysis** : [[Intraprocedural-Transformation-Analysis|Link]]
   - Forward abstract interpretation over transformations rather than states
   - Localization and mutation of pointer cells during assignment analysis : [[Intraprocedural-Transformation-Analysis|Link]]
   - Unfolding summaries to resolve modified cells
   - Weakening of transformations at loop widening points : [[Intraprocedural-Transformation-Analysis|Link]]
   - Variable introduction and removal transfer functions : [[Intraprocedural-Transformation-Analysis|Link]]

5. **Abstract Intersection and Composition Algorithms** : [[Abstract-Intersection-and-Composition-Algorithms|Link]]
   - Abstract intersection of two abstract heaps : [[Abstract-Intersection-and-Composition-Algorithms|Link]]
   - Rewriting rules for structural intersection reasoning
   - Abstract composition of two abstract transformations : [[Abstract-Intersection-and-Composition-Algorithms|Link]]
   - Rewriting rules for composition, including weakening rules
   - Soundness of abstract intersection and composition : [[Abstract-Intersection-and-Composition-Algorithms|Link]]
   - Composition as a mechanism for both application and sequencing

6. **Modular Interprocedural Call Analysis** : [[Modular-Interprocedural-Call-Analysis|Link]]
   - Procedure footprint extraction via the output-projection operator : [[Modular-Interprocedural-Call-Analysis|Link]]
   - Relevance slicing of an abstract heap with respect to call parameters
   - Context summary coverage testing via abstract inclusion
   - Summary application at a call site : [[Modular-Interprocedural-Call-Analysis|Link]]
   - Inference and generalization of a new context summary via widening
   - Analysis of recursive procedure calls via fixpoint iteration on summaries : [[Modular-Interprocedural-Call-Analysis|Link]]

7. **Experimental Evaluation of Summary-Based Shape Analysis** : [[Experimental-Evaluation-of-Summary-Based-Shape-Analysis|Link]]
   - Frama-C-based implementation for a fragment of C
   - Comparison against a call-string (inlining) based analysis
   - Precision preservation relative to state analysis : [[Separation-Logic-for-Shape-Analysis|Link1]], [[Experimental-Evaluation-of-Summary-Based-Shape-Analysis|Link2]]
   - Scalability and total analysis time : [[Experimental-Evaluation-of-Summary-Based-Shape-Analysis|Link]]
   - Effectiveness of summary reuse versus reanalysis frequency
   - Validation on recursive list and tree algorithms : [[Experimental-Evaluation-of-Summary-Based-Shape-Analysis|Link]]

---
