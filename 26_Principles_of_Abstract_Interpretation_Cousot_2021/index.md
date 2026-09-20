# Principles of Abstract Interpretation — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Abstract Interpretation as a Unifying Theory** : [[Abstract-Interpretation-as-a-Unifying-Theory|Link]]
   - A mathematical framework for reasoning about program executions
   - Soundness completeness and incompleteness of formal methods : [[Abstract-Interpretation-as-a-Unifying-Theory|Link]]
   - Calculational design versus postulating and then proving sound : [[Abstract-Interpretation-as-a-Unifying-Theory|Link]]
   - Semantics proof methods and static analysis as its main applications : [[Abstract-Interpretation-as-a-Unifying-Theory|Link]]
   - The recurring abstraction recipe of concrete domain properties abstract domain and concretization
   - The three possible outcomes for any static analysis method under Rice's theorem

2. **Set Theory and Proof Techniques Prerequisites** : [[Set-Theory-and-Proof-Techniques-Prerequisites|Link]]
   - Sets relations and functions as basic term and predicate notations : [[Set-Theory-and-Proof-Techniques-Prerequisites|Link]]
   - Properties represented as sets rather than logical formulas
   - Proof by contraposition and by reductio ad absurdum
   - Proof by recurrence and structural induction : [[Syntax-and-Parsing-of-Programming-Languages|Link1]], [[Fixpoint-Abstraction|Link2]]

3. **Syntax and Parsing of Programming Languages** : [[Syntax-and-Parsing-of-Programming-Languages|Link]]
   - Context-free grammar of expressions and statements : [[Syntax-and-Parsing-of-Programming-Languages|Link]]
   - Axiomatic definition of program labels and program points : [[Syntax-and-Parsing-of-Programming-Languages|Link]]
   - Lexing and bottom-up shift-reduce parsing : [[Syntax-and-Parsing-of-Programming-Languages|Link]]
   - Resolving shift-reduce and reduce-reduce ambiguities : [[Syntax-and-Parsing-of-Programming-Languages|Link]]

4. **Trace Semantics of Programs** : [[Trace-Semantics-of-Programs|Link]]
   - Stateless structural deductive prefix trace semantics : [[Cartesian-Abstraction|Link1]], [[Forward-Reachability-Semantics|Link2]], [[Deductive-Inductive-and-Coinductive-Definitions|Link3]]
   - Recovering variable values from trace history : [[Trace-Semantics-of-Programs|Link]]
   - Left-recursive and right-recursive characterizations of iteration : [[Trace-Semantics-of-Programs|Link]]
   - Maximal finite and infinite trace semantics as limits of prefixes : [[Trace-Semantics-of-Programs|Link]]
   - Traces as relations between initialization and continuation : [[Trace-Semantics-of-Programs|Link]]

5. **Program Properties and Their Hierarchy** : [[Program-Properties-and-Their-Hierarchy|Link]]
   - Program properties as sets of program semantics : [[Stateful-and-Operational-Program-Semantics|Link1]], [[Program-Properties-and-Their-Hierarchy|Link2]]
   - The collecting semantics as the strongest program property : [[Program-Properties-and-Their-Hierarchy|Link]]
   - Trace properties versus semantic properties : [[Program-Properties-and-Their-Hierarchy|Link]]
   - Invariance and reachability properties : [[Program-Properties-and-Their-Hierarchy|Link]]
   - Abstraction of program properties by Galois connections : [[Graph-Theory-and-Path-Problems|Link]]

6. **Undecidability and the Limits of Static Analysis** : [[Undecidability-and-the-Limits-of-Static-Analysis|Link]]
   - Turing completeness and determinism of a language : [[Undecidability-and-the-Limits-of-Static-Analysis|Link]]
   - Undecidability of the halting and termination problem : [[Undecidability-and-the-Limits-of-Static-Analysis|Link]]
   - Decidability semidecidability and Post's theorem : [[Undecidability-and-the-Limits-of-Static-Analysis|Link]]
   - Rice's theorem on nontrivial semantic properties : [[Program-Properties-and-Their-Hierarchy|Link]]
   - Consequences of undecidability for sound program analysis : [[Undecidability-and-the-Limits-of-Static-Analysis|Link]]

7. **Order Theory of Posets Lattices and Complete Lattices** : [[Order-Theory-of-Posets-Lattices-and-Complete-Lattices|Link]]
   - Posets and Hasse diagrams : [[Order-Theory-of-Posets-Lattices-and-Complete-Lattices|Link]]
   - Least upper bounds and greatest lower bounds : [[Combining-and-Refining-Abstract-Domains|Link]]
   - The duality principle : [[Order-Theory-of-Posets-Lattices-and-Complete-Lattices|Link]]
   - Lattices complete lattices and complete partial orders : [[Order-Theory-of-Posets-Lattices-and-Complete-Lattices|Link]]
   - Chains and the ascending chain condition : [[Order-Theory-of-Posets-Lattices-and-Complete-Lattices|Link]]

8. **Galois Connections and Abstraction** : [[Galois-Connections-and-Abstraction|Link]]
   - Definition of a Galois connection between concrete and abstract domains : [[Relational-and-Predicate-Transformer-Semantics|Link1]], [[Galois-Connections-and-Abstraction|Link2]], [[Domain-Abstraction-and-the-Best-Abstract-Interpreter|Link3]]
   - Best abstraction as a most precise sound overapproximation : [[Flow-Sensitivity-and-Insensitivity|Link]]
   - Galois retractions and closure operators : [[Fixpoint-Abstraction|Link1]], [[Safety-and-Liveness-Properties|Link2]]
   - Moore families as an equivalent formalization of abstraction : [[Galois-Connections-and-Abstraction|Link1]], [[Domain-Abstraction-and-the-Best-Abstract-Interpreter|Link2]], [[Stateful-and-Operational-Program-Semantics|Link3]]
   - Logical relations and soundness relations : [[Galois-Connections-and-Abstraction|Link]]
   - The hierarchy of abstractions : [[Stateful-and-Operational-Program-Semantics|Link1]], [[Cartesian-Abstraction|Link2]], [[Fixpoint-Abstraction|Link3]], [[Linear-Algebra-and-Affine-Static-Analysis|Link4]]

9. **Relational and Predicate Transformer Semantics** : [[Relational-and-Predicate-Transformer-Semantics|Link]]
   - Relational and natural semantics as abstractions of trace semantics : [[Invariance-Verification-and-Hoare-Logic|Link]]
   - Forward and backward property transformers : [[Relational-and-Predicate-Transformer-Semantics|Link1]], [[Combining-and-Refining-Abstract-Domains|Link2]]
   - Postimage and preimage transformers : [[Relational-and-Predicate-Transformer-Semantics|Link]]
   - Dijkstra's weakest precondition and weakest liberal precondition : [[Relational-and-Predicate-Transformer-Semantics|Link]]
   - Strongest postcondition semantics : [[Program-Properties-and-Their-Hierarchy|Link1]], [[Relational-and-Predicate-Transformer-Semantics|Link2]]

10. **Safety and Liveness Properties** : [[Safety-and-Liveness-Properties|Link]]
    - Topological closure as the foundation of safety and liveness : [[Safety-and-Liveness-Properties|Link]]
    - Safety as closed trace properties checkable on a finite prefix
    - Liveness as dense trace properties : [[Safety-and-Liveness-Properties|Link]]
    - The safety liveness decomposition of trace properties : [[Safety-and-Liveness-Properties|Link]]
    - Guarantee properties as a strict subclass of liveness : [[Safety-and-Liveness-Properties|Link]]

11. **Fixpoint Theory** : [[Fixpoint-Theory|Link]]
    - Tarski's fixpoint theorem on complete lattices : [[Fixpoint-Theory|Link]]
    - The Tarski-Kantorovich and Scott-Kleene iterative fixpoint theorems : [[Fixpoint-Theory|Link]]
    - Park's conjugate fixpoint theorem : [[Fixpoint-Theory|Link]]
    - Least and greatest fixpoints of increasing functions : [[Fixpoint-Theory|Link]]
    - Upper and lower continuity : [[Combining-and-Refining-Abstract-Domains|Link]]

12. **Deductive Inductive and Coinductive Definitions** : [[Deductive-Inductive-and-Coinductive-Definitions|Link]]
    - Equivalence of fixpoint and deductive rule-based definitions : [[Deductive-Inductive-and-Coinductive-Definitions|Link]]
    - Inductive definitions on well founded orders : [[Deductive-Inductive-and-Coinductive-Definitions|Link]]
    - Structural definitions as induction on program syntax : [[Deductive-Inductive-and-Coinductive-Definitions|Link]]
    - Coinductive definitions as greatest fixpoints : [[Deductive-Inductive-and-Coinductive-Definitions|Link]]
    - Bi-inductive definitions combining induction and coinduction : [[Deductive-Inductive-and-Coinductive-Definitions|Link]]

13. **Fixpoint Abstraction** : [[Fixpoint-Abstraction|Link]]
    - Sound overapproximation of a concrete fixpoint : [[Fixpoint-Abstraction|Link]]
    - Exact and complete fixpoint abstraction by commutation : [[Fixpoint-Abstraction|Link]]
    - Iterates multiabstraction with a varying abstract transformer : [[Fixpoint-Abstraction|Link]]
    - Abstraction of deductive inductive and structural definitions : [[Fixpoint-Abstraction|Link]]

14. **Forward Reachability Semantics** : [[Forward-Reachability-Semantics|Link]]
    - Assertional and relational reachability semantics : [[Forward-Reachability-Semantics|Link]]
    - Reachability of assignments conditionals and iterations : [[Forward-Reachability-Semantics|Link]]
    - Uncomputability of the reachability semantics : [[Forward-Reachability-Semantics|Link]]
    - Calculational design of the reachability semantics from trace semantics : [[Forward-Reachability-Semantics|Link]]

15. **The Generic Abstract Interpreter** : [[The-Generic-Abstract-Interpreter|Link]]
    - Abstract domains as posets with join and primitive operations : [[The-Generic-Abstract-Interpreter|Link]]
    - The forward abstract interpreter parameterized by an abstract domain : [[Domain-Abstraction-and-the-Best-Abstract-Interpreter|Link1]], [[The-Generic-Abstract-Interpreter|Link2]], [[Dataflow-Analysis-as-Abstract-Interpretation|Link3]]
    - Well definedness and termination on finitary abstract domains
    - Instantiating one generic interpreter for many concrete semantics : [[The-Generic-Abstract-Interpreter|Link]]

16. **Chaotic Iteration and Equational Semantics** : [[Chaotic-Iteration-and-Equational-Semantics|Link]]
    - Jacobi and Gauss-Seidel iteration methods : [[Chaotic-Iteration-and-Equational-Semantics|Link]]
    - Chaotic iterations and their fairness condition : [[Chaotic-Iteration-and-Equational-Semantics|Link1]], [[Forward-Reachability-Semantics|Link2]], [[Domain-Abstraction-and-the-Best-Abstract-Interpreter|Link3]]
    - Convergence of chaotic iterations to the least fixpoint : [[Chaotic-Iteration-and-Equational-Semantics|Link]]
    - Equational semantics as systems of dataflow equations : [[Chaotic-Iteration-and-Equational-Semantics|Link]]
    - Equivalence of equations inequations and constraints : [[Chaotic-Iteration-and-Equational-Semantics|Link]]

17. **Fixpoint-Based Verification Proof Methods** : [[Fixpoint-Based-Verification-Proof-Methods|Link]]
    - Invariants versus inductive invariants : [[Fixpoint-Based-Verification-Proof-Methods|Link1]], [[Invariance-Verification-and-Hoare-Logic|Link2]]
    - Fixpoint induction as a sound and complete proof method : [[Fixpoint-Based-Verification-Proof-Methods|Link]]
    - Iteration induction based on the iterates of a transformer : [[Domain-Abstraction-and-the-Best-Abstract-Interpreter|Link1]], [[Relational-and-Predicate-Transformer-Semantics|Link2]], [[Convergence-Acceleration-by-Widening-and-Narrowing|Link3]]
    - Fixpoint checking by strengthening the invariant search with the specification : [[Fixpoint-Based-Verification-Proof-Methods|Link]]

18. **Invariance Verification and Hoare Logic** : [[Invariance-Verification-and-Hoare-Logic|Link]]
    - Reachability specifications and inductive invariants : [[Invariance-Verification-and-Hoare-Logic|Link]]
    - Structural verification conditions : [[Invariance-Verification-and-Hoare-Logic|Link1]], [[Deductive-Inductive-and-Coinductive-Definitions|Link2]]
    - Automation obstacles in program verification : [[Stateful-and-Operational-Program-Semantics|Link]]
    - Hoare triples extended with an escape component for break
    - Hoare logic as an abstract interpretation of invariance semantics : [[Invariance-Verification-and-Hoare-Logic|Link]]
    - Calculational design of Hoare logic inference rules : [[Abstract-Interpretation-as-a-Unifying-Theory|Link1]], [[Graph-Theory-and-Path-Problems|Link2]], [[Invariance-Verification-and-Hoare-Logic|Link3]], [[Forward-Reachability-Semantics|Link4]]

19. **Domain Abstraction and the Best Abstract Interpreter** : [[Domain-Abstraction-and-the-Best-Abstract-Interpreter|Link]]
    - Sound approximate and exact abstraction between abstract domains : [[Domain-Abstraction-and-the-Best-Abstract-Interpreter|Link]]
    - Local soundness of domain primitives implying global soundness : [[Domain-Abstraction-and-the-Best-Abstract-Interpreter|Link]]
    - Best abstraction via a Galois connection : [[Domain-Abstraction-and-the-Best-Abstract-Interpreter|Link]]
    - Predicate abstraction as an instance of abstract interpretation : [[Domain-Abstraction-and-the-Best-Abstract-Interpreter|Link1]], [[Dataflow-Analysis-as-Abstract-Interpretation|Link2]]

20. **Cartesian Abstraction** : [[Cartesian-Abstraction|Link]]
    - Cartesian abstraction as a projection onto individual variables : [[Cartesian-Abstraction|Link]]
    - The inductive hierarchy of Cartesian abstract domains : [[Cartesian-Abstraction|Link]]
    - Incompleteness of the structural Cartesian semantics : [[Cartesian-Abstraction|Link]]
    - Reachability and accessibility semantics of expressions : [[Cartesian-Abstraction|Link]]
    - Parity sign and constancy as Cartesian value domains : [[Cartesian-Abstraction|Link]]

21. **Combining and Refining Abstract Domains** : [[Combining-and-Refining-Abstract-Domains|Link]]
    - Reduction as iterating an increasing extensive operator to a closure : [[Combining-and-Refining-Abstract-Domains|Link]]
    - Local iterations for test reduction : [[Combining-and-Refining-Abstract-Domains|Link]]
    - Direct product versus reduced product : [[Combining-and-Refining-Abstract-Domains|Link]]
    - The reduced product as the greatest lower bound of abstract domains : [[Cartesian-Abstraction|Link]]
    - Iterated pairwise reduction and communication channels : [[Combining-and-Refining-Abstract-Domains|Link]]
    - Extremal versus intermediate forward-backward reduction : [[Combining-and-Refining-Abstract-Domains|Link]]

22. **Number-Theoretic and Interval Abstract Domains** : [[Number-Theoretic-and-Interval-Abstract-Domains|Link]]
    - Euclidean division congruences and the Bachet-Bezout identity
    - The Cartesian congruence abstract domain : [[Cartesian-Abstraction|Link1]], [[Number-Theoretic-and-Interval-Abstract-Domains|Link2]], [[Linear-Algebra-and-Affine-Static-Analysis|Link3]]
    - Dynamic interval arithmetic and rounding error bounds : [[Number-Theoretic-and-Interval-Abstract-Domains|Link]]
    - Static interval and range analysis : [[Number-Theoretic-and-Interval-Abstract-Domains|Link]]
    - Affine arithmetic and zonotopes : [[Number-Theoretic-and-Interval-Abstract-Domains|Link]]

23. **Convergence Acceleration by Widening and Narrowing** : [[Convergence-Acceleration-by-Widening-and-Narrowing|Link]]
    - Divergence of fixpoint iteration in non-Noetherian domains
    - Extrapolation by widening and its soundness and termination conditions : [[Trace-Semantics-of-Programs|Link1]], [[Convergence-Acceleration-by-Widening-and-Narrowing|Link2]], [[Fixpoint-Abstraction|Link3]], [[Order-Theory-of-Posets-Lattices-and-Complete-Lattices|Link4]]
    - Interpolation by narrowing : [[Convergence-Acceleration-by-Widening-and-Narrowing|Link]]
    - Widening thresholds delayed widening and history widening
    - Finitary versus infinitary abstract domains : [[Convergence-Acceleration-by-Widening-and-Narrowing|Link]]

24. **Linear Algebra and Affine Static Analysis** : [[Linear-Algebra-and-Affine-Static-Analysis|Link]]
    - Vector spaces fields and matrices : [[Linear-Algebra-and-Affine-Static-Analysis|Link]]
    - Gauss-Jordan elimination and reduced row echelon form
    - Affine spaces and systems of generators
    - The Karr linear equality abstract domain : [[Linear-Algebra-and-Affine-Static-Analysis|Link]]
    - Invertible and non-invertible affine assignments : [[Linear-Algebra-and-Affine-Static-Analysis|Link]]

25. **Graph Theory and Path Problems** : [[Graph-Theory-and-Path-Problems|Link]]
    - Fixpoint characterization of the paths of a graph : [[Graph-Theory-and-Path-Problems|Link]]
    - Abstraction of path problems by Galois connection : [[Graph-Theory-and-Path-Problems|Link]]
    - Elementary paths and cycles : [[Graph-Theory-and-Path-Problems|Link]]
    - Calculational design of the Roy-Floyd-Warshall algorithm : [[Graph-Theory-and-Path-Problems|Link]]
    - Weighted graphs and totally ordered groups : [[Graph-Theory-and-Path-Problems|Link]]

26. **Zone and Octagon Relational Domains** : [[Zone-and-Octagon-Relational-Domains|Link]]
    - Difference bound matrix encoding of zones
    - Normalization by saturation via Roy-Floyd-Warshall : [[Zone-and-Octagon-Relational-Domains|Link]]
    - Octagon encoding by variable doubling : [[Zone-and-Octagon-Relational-Domains|Link]]
    - History widening for zones and octagons : [[Convergence-Acceleration-by-Widening-and-Narrowing|Link]]
    - Template polyhedra and other relational numerical domains : [[Zone-and-Octagon-Relational-Domains|Link]]

27. **Dataflow Analysis as Abstract Interpretation** : [[Dataflow-Analysis-as-Abstract-Interpretation|Link]]
    - Potential versus definite liveness and deadness : [[Dataflow-Analysis-as-Abstract-Interpretation|Link]]
    - Semantic versus syntactic use and modification : [[Dataflow-Analysis-as-Abstract-Interpretation|Link]]
    - Unsoundness of classic syntactic liveness and its repair : [[Dataflow-Analysis-as-Abstract-Interpretation|Link]]
    - Structural liveness analysis without fixpoint iteration : [[Dataflow-Analysis-as-Abstract-Interpretation|Link]]
    - Order dual abstract interpretation : [[Dataflow-Analysis-as-Abstract-Interpretation|Link]]

28. **Stateful and Operational Program Semantics** : [[Stateful-and-Operational-Program-Semantics|Link]]
    - Abstraction of stateless traces into stateful traces : [[Stateful-and-Operational-Program-Semantics|Link]]
    - Transition systems and small step operational semantics : [[Stateful-and-Operational-Program-Semantics|Link1]], [[Chaotic-Iteration-and-Equational-Semantics|Link2]]
    - Equivalence of trace semantics and transition semantics

29. **Model Checking as Abstract Interpretation** : [[Model-Checking-as-Abstract-Interpretation|Link]]
    - Regular expressions as trace specifications : [[Model-Checking-as-Abstract-Interpretation|Link]]
    - The model checking abstraction as a Galois connection : [[Model-Checking-as-Abstract-Interpretation|Link]]
    - Soundness and completeness of model checking : [[Model-Checking-as-Abstract-Interpretation|Link]]
    - Structural calculational design of a model checker : [[Model-Checking-as-Abstract-Interpretation|Link]]

30. **Flow Sensitivity and Insensitivity** : [[Flow-Sensitivity-and-Insensitivity|Link]]
    - Flow-insensitive abstraction as joining local properties
    - Soundness of the flow-insensitive abstract interpreter : [[Flow-Sensitivity-and-Insensitivity|Link1]], [[Domain-Abstraction-and-the-Best-Abstract-Interpreter|Link2]], [[Dataflow-Analysis-as-Abstract-Interpretation|Link3]], [[The-Generic-Abstract-Interpreter|Link4]]
    - Path field and context sensitivity as analogous abstractions : [[Galois-Connections-and-Abstraction|Link]]

31. **Points-To Analysis** : [[Points-To-Analysis|Link]]
    - Static memory allocation and pointer semantic domains : [[Stateful-and-Operational-Program-Semantics|Link1]], [[Chaotic-Iteration-and-Equational-Semantics|Link2]]
    - Cartesian points-to abstraction : [[Cartesian-Abstraction|Link]]
    - Andersen's flow-insensitive points-to analysis : [[Flow-Sensitivity-and-Insensitivity|Link]]
    - Steensgaard's analysis as Andersen's analysis with widening : [[Points-To-Analysis|Link]]
    - Soundness of pointer analysis relative to undefined behavior : [[Points-To-Analysis|Link]]

32. **Dependency Analysis and Information Flow** : [[Dependency-Analysis-and-Information-Flow|Link]]
    - Syntactic versus semantic dependency : [[Dataflow-Analysis-as-Abstract-Interpretation|Link]]
    - Noninterference between low and high variables
    - Explicit implicit and timing dependency : [[Dependency-Analysis-and-Information-Flow|Link]]
    - Exact definite and potential value dependency semantics : [[Dependency-Analysis-and-Information-Flow|Link]]
    - Taint tracking and dualistic dependency abstractions

33. **The Herbrand Domain and Unification** : [[The-Herbrand-Domain-and-Unification|Link]]
    - Ground and symbolic terms : [[The-Herbrand-Domain-and-Unification|Link]]
    - The subsumption partial order on terms with variables : [[The-Herbrand-Domain-and-Unification|Link]]
    - Unification as the meet of the subsumption lattice
    - Least common generalization as the join : [[The-Herbrand-Domain-and-Unification|Link]]

34. **Type Systems as Abstract Interpretation** : [[Type-Systems-as-Abstract-Interpretation|Link]]
    - Static and dynamic errors : [[Type-Systems-as-Abstract-Interpretation|Link]]
    - Semantics of monomorphic types and type judgments : [[Type-Systems-as-Abstract-Interpretation|Link]]
    - Soundness of typable expressions : [[Soundness-Completeness-and-the-Practice-of-Static-Analysis|Link]]
    - Calculational design of typing rules : [[Invariance-Verification-and-Hoare-Logic|Link]]
    - Monotypes with variables for algorithmic type inference : [[Type-Systems-as-Abstract-Interpretation|Link]]

35. **Backward Accessibility Semantics** : [[Backward-Accessibility-Semantics|Link]]
    - Impossible failure and possible success accessibility : [[Backward-Accessibility-Semantics|Link]]
    - Duality between forward reachability and backward accessibility : [[Relational-and-Predicate-Transformer-Semantics|Link]]
    - The magic transformation between forward and backward analyses : [[Backward-Accessibility-Semantics|Link1]], [[Relational-and-Predicate-Transformer-Semantics|Link2]]

36. **Soundness Completeness and the Practice of Static Analysis** : [[Soundness-Completeness-and-the-Practice-of-Static-Analysis|Link]]
    - Soundness and completeness by calculational design : [[Soundness-Completeness-and-the-Practice-of-Static-Analysis|Link1]], [[Model-Checking-as-Abstract-Interpretation|Link2]]
    - Verification versus static analysis : [[Soundness-Completeness-and-the-Practice-of-Static-Analysis|Link]]
    - Handling alarms and semantic undefinedness : [[Soundness-Completeness-and-the-Practice-of-Static-Analysis|Link]]
    - Handling missing code and library stubs : [[Soundness-Completeness-and-the-Practice-of-Static-Analysis|Link]]
    - The ethics and economics of unsound analyzers : [[Soundness-Completeness-and-the-Practice-of-Static-Analysis|Link]]

37. **Engineering and Adoption of Static Analysis Tools** : [[Engineering-and-Adoption-of-Static-Analysis-Tools|Link]]
    - A taxonomy of static analysis tools : [[Engineering-and-Adoption-of-Static-Analysis-Tools|Link]]
    - Control architecture and property architecture of analyzers : [[Engineering-and-Adoption-of-Static-Analysis-Tools|Link]]
    - Extensibility scalability and qualification : [[Engineering-and-Adoption-of-Static-Analysis-Tools|Link]]
    - Obstacles to industrial adoption of sound analyzers : [[Engineering-and-Adoption-of-Static-Analysis-Tools|Link]]

---
