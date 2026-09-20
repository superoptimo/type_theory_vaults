# Introduction to Static Analysis: An Abstract Interpretation Perspective — Index

[[book-guidelines|↩ Back to guidelines]]

1. **The Landscape of Program Analysis Techniques** : [[The-Landscape-of-Program-Analysis-Techniques|Link]]
   - Semantics and semantic properties : [[Classes-of-Semantic-Properties-and-Their-Verification|Link]]
   - Program analysis versus program analysis tools : [[The-Landscape-of-Program-Analysis-Techniques|Link1]], [[Static-Analysis-for-Advanced-Programming-Language-Features|Link2]]
   - Domain-specific versus non-domain-specific analyses
   - Program-level versus model-level analyses
   - Safety liveness and information flow properties : [[Classes-of-Semantic-Properties-and-Their-Verification|Link]]
   - Static versus dynamic analysis : [[The-Landscape-of-Program-Analysis-Techniques|Link]]
   - The halting problem and Rice's theorem
   - Automation and scalability trade-offs
   - Soundness and completeness : [[The-Landscape-of-Program-Analysis-Techniques|Link]]
   - Testing
   - Assisted proof with theorem provers
   - Model checking
   - Conservative static analysis : [[Backward-Analysis|Link1]], [[Mathematical-Foundations-for-Static-Analysis|Link2]], [[Practical-Use-and-Deployment-of-Static-Analysis-Tools|Link3]], [[Scalability-Techniques-for-Static-Analysis|Link4]]
   - Bug finding : [[Specialized-Static-Analysis-Frameworks|Link]]

2. **Mathematical Foundations for Static Analysis** : [[Mathematical-Foundations-for-Static-Analysis|Link]]
   - Sets and set operations : [[Mathematical-Foundations-for-Static-Analysis|Link]]
   - Logical connectives and quantifiers : [[Mathematical-Foundations-for-Static-Analysis|Link]]
   - Inductive definitions and proof by induction
   - Functions and function composition : [[Mathematical-Foundations-for-Static-Analysis|Link]]
   - Order relations lattices and complete partial orders : [[Mathematical-Foundations-for-Static-Analysis|Link]]
   - Monotone continuous and extensive functions : [[Mathematical-Foundations-for-Static-Analysis|Link]]
   - Fixpoints and Kleene's fixpoint theorem : [[Mathematical-Foundations-for-Static-Analysis|Link]]

3. **Concrete Semantics of Programs** : [[Concrete-Semantics-of-Programs|Link]]
   - Collecting semantics as the set of all executions
   - Compositional denotational-style semantics : [[Concrete-Semantics-of-Programs|Link]]
   - Transitional operational-style semantics : [[Concrete-Semantics-of-Programs|Link]]
   - States memories and program labels : [[Concrete-Semantics-of-Programs|Link]]
   - Semantics of expressions conditions and commands : [[Sound-Abstract-Semantics-and-Analysis-Algorithms|Link]]
   - Control flow and dynamic control transfer
   - Semantics as a least fixpoint : [[Concrete-Semantics-of-Programs|Link]]

4. **Abstraction and Abstract Domains** : [[Abstraction-and-Abstract-Domains|Link]]
   - Concrete and abstract domains : [[Abstraction-and-Abstract-Domains|Link]]
   - Concretization and abstraction functions : [[Abstraction-and-Abstract-Domains|Link]]
   - Galois connections : [[Abstraction-and-Abstract-Domains|Link1]], [[Foundational-Soundness-Proofs|Link2]]
   - Best abstraction and its non-existence : [[Abstraction-and-Abstract-Domains|Link]]
   - Non-relational abstraction : [[Abstraction-and-Abstract-Domains|Link]]
   - Signs intervals and congruences
   - Relational abstraction : [[Abstraction-and-Abstract-Domains|Link]]
   - Linear equalities convex polyhedra and octagons
   - Reduction between abstract domains : [[Abstraction-and-Abstract-Domains|Link]]
   - Product and reduced product domains : [[Abstraction-and-Abstract-Domains|Link]]
   - Disjunctive completion : [[Abstraction-and-Abstract-Domains|Link]]
   - Cardinal power and state partitioning : [[Abstraction-and-Abstract-Domains|Link]]
   - Trace partitioning and context sensitivity : [[Static-Analysis-for-Advanced-Programming-Language-Features|Link]]

5. **Sound Abstract Semantics and Analysis Algorithms** : [[Sound-Abstract-Semantics-and-Analysis-Algorithms|Link]]
   - Transfer functions : [[Sound-Abstract-Semantics-and-Analysis-Algorithms|Link]]
   - Soundness of abstract interpretation : [[Specialized-Static-Analysis-Frameworks|Link]]
   - Abstract interpretation of assignment and expressions
   - Abstract filtering of conditions : [[Sound-Abstract-Semantics-and-Analysis-Algorithms|Link]]
   - Abstract union and join : [[Sound-Abstract-Semantics-and-Analysis-Algorithms|Link]]
   - Abstract iteration and global fixpoint computation : [[Static-Analyzer-Implementation|Link]]
   - Widening operators : [[Foundational-Soundness-Proofs|Link]]
   - Narrowing and post-fixpoint refinement : [[Practical-Use-and-Deployment-of-Static-Analysis-Tools|Link]]
   - Loop unrolling and delayed widening : [[Sound-Abstract-Semantics-and-Analysis-Algorithms|Link]]
   - Widening with thresholds : [[Sound-Abstract-Semantics-and-Analysis-Algorithms|Link]]
   - The worklist algorithm : [[Sound-Abstract-Semantics-and-Analysis-Algorithms|Link]]

6. **Design Methodology for Static Analyzers** : [[Design-Methodology-for-Static-Analyzers|Link]]
   - The three-stage recipe of semantics abstraction and algorithm : [[Sound-Abstract-Semantics-and-Analysis-Algorithms|Link]]
   - Diagnosing precision loss by design stage
   - Compositional versus transitional analysis design : [[Concrete-Semantics-of-Programs|Link]]

7. **Scalability Techniques for Static Analysis** : [[Scalability-Techniques-for-Static-Analysis|Link]]
   - Sparse analysis : [[Scalability-Techniques-for-Static-Analysis|Link]]
   - Spatial and temporal sparsity : [[Scalability-Techniques-for-Static-Analysis|Link]]
   - Def-use chains and safe pre-analysis : [[Scalability-Techniques-for-Static-Analysis|Link]]
   - Modular analysis : [[Scalability-Techniques-for-Static-Analysis|Link]]
   - Procedure parameterization and summaries : [[Practical-Use-and-Deployment-of-Static-Analysis-Tools|Link]]

8. **Backward Analysis** : [[Backward-Analysis|Link]]
   - Backward semantics of expressions and commands
   - Necessary conditions and impossibility proofs
   - Combined forward and backward iteration

9. **Practical Use and Deployment of Static Analysis Tools** : [[Practical-Use-and-Deployment-of-Static-Analysis-Tools|Link]]
   - Soundness under assumption
   - Analyzer implementation bugs and certification : [[Static-Analyzer-Implementation|Link]]
   - Analysis precision and partial completeness
   - Whole-program versus fragment analysis : [[Practical-Use-and-Deployment-of-Static-Analysis-Tools|Link]]
   - Stubs and code harnesses : [[Practical-Use-and-Deployment-of-Static-Analysis-Tools|Link]]
   - Selecting abstract domains and packing : [[Practical-Use-and-Deployment-of-Static-Analysis-Tools|Link]]
   - Automatic and manual parameterization : [[Practical-Use-and-Deployment-of-Static-Analysis-Tools|Link]]
   - Alarms and alarm triage : [[Practical-Use-and-Deployment-of-Static-Analysis-Tools|Link]]
   - Dependence analysis and counter-example construction : [[Practical-Use-and-Deployment-of-Static-Analysis-Tools|Link]]
   - Online and offline analysis dispatch models

10. **Static Analyzer Implementation** : [[Static-Analyzer-Implementation|Link]]
    - Concrete interpreter construction : [[Concrete-Semantics-of-Programs|Link1]], [[Static-Analyzer-Implementation|Link2]]
    - Abstract domain implementation : [[Static-Analyzer-Implementation|Link]]
    - Analysis of expressions and conditions : [[Static-Analyzer-Implementation|Link]]
    - Compositional-style analyzer implementation : [[Foundational-Soundness-Proofs|Link1]], [[Static-Analyzer-Implementation|Link2]]
    - Transitional-style analyzer implementation : [[Static-Analyzer-Implementation|Link1]], [[Foundational-Soundness-Proofs|Link2]]
    - Local versus global fixpoint iteration in implementation : [[Static-Analyzer-Implementation|Link]]

11. **Static Analysis for Advanced Programming Language Features** : [[Static-Analysis-for-Advanced-Programming-Language-Features|Link]]
    - Pointers and dynamic memory allocation
    - Aliasing
    - Strong and weak update
    - Functions and recursive calls
    - Calling context and call-string sensitivity
    - Arrays and array partitioning
    - Buffers and strings
    - Points-to sets and aliasing relations : [[Static-Analysis-for-Advanced-Programming-Language-Features|Link]]
    - Dynamic heap allocation and shape abstraction : [[Static-Analysis-for-Advanced-Programming-Language-Features|Link]]
    - Materialization and generalization
    - Procedures and procedure summaries
    - Parallelism deadlock and data races

12. **Classes of Semantic Properties and Their Verification** : [[Classes-of-Semantic-Properties-and-Their-Verification|Link]]
    - Trace properties versus state properties : [[Classes-of-Semantic-Properties-and-Their-Verification|Link]]
    - Safety properties : [[Classes-of-Semantic-Properties-and-Their-Verification|Link]]
    - Liveness properties and ranking functions
    - Termination proofs by instrumentation
    - Decomposition into safety and liveness
    - Information flow and non-interference
    - Hyperproperties
    - Self-composition
    - Taint analysis : [[Backward-Analysis|Link]]

13. **Specialized Static Analysis Frameworks** : [[Specialized-Static-Analysis-Frameworks|Link]]
    - Static analysis by equations : [[Specialized-Static-Analysis-Frameworks|Link]]
    - Data-flow analysis and control-flow graphs : [[Specialized-Static-Analysis-Frameworks|Link]]
    - Static analysis by monotonic closure : [[Specialized-Static-Analysis-Frameworks|Link]]
    - Pointer analysis by chain reaction : [[Specialized-Static-Analysis-Frameworks|Link]]
    - Higher-order control-flow analysis : [[Specialized-Static-Analysis-Frameworks|Link]]
    - Static analysis by proof construction : [[Specialized-Static-Analysis-Frameworks|Link]]
    - Type inference and type soundness : [[The-Landscape-of-Program-Analysis-Techniques|Link]]
    - Unification-based type inference
    - Polymorphic type systems : [[Specialized-Static-Analysis-Frameworks|Link]]

14. **Foundational Soundness Proofs** : [[Foundational-Soundness-Proofs|Link]]
    - Properties of Galois connections : [[Abstraction-and-Abstract-Domains|Link1]], [[Foundational-Soundness-Proofs|Link2]]
    - Soundness of compositional-style analysis : [[Foundational-Soundness-Proofs|Link]]
    - Soundness of transitional-style analysis : [[Foundational-Soundness-Proofs|Link]]
    - Soundness under widening

---
