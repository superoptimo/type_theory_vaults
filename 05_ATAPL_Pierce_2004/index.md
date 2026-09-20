# Advanced Topics in Types and Programming Languages — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Substructural Type Systems** : [[Substructural-Type-Systems|Link]]
   - Structural properties exchange weakening and contraction
   - Linear affine relevant and ordered type systems
   - Context splitting : [[Substructural-Type-Systems|Link]]
   - Algorithmic linear type checking : [[Dependent-Types|Link]]
   - Sums and recursive types in a substructural setting : [[Substructural-Type-Systems|Link]]
   - Parametric polymorphism over types and usage qualifiers : [[Substructural-Type-Systems|Link]]
   - Linear arrays and swap-based access
   - Reference counting as a substructural discipline : [[Substructural-Type-Systems|Link]]
   - Ordered types and stack-based allocation : [[Substructural-Type-Systems|Link1]], [[Typed-Operational-Reasoning|Link2]]
   - Substructural types for guaranteeing polynomial time : [[Substructural-Type-Systems|Link]]
   - Substructural types for compiler optimization : [[Substructural-Type-Systems|Link1]], [[Logical-Relations-and-Equivalence-Checking|Link2]]

2. **Dependent Types** : [[Dependent-Types|Link]]
   - Pi types and dependent products : [[Dependent-Types|Link]]
   - Sigma types and dependent sums
   - The Curry–Howard correspondence : [[Dependent-Types|Link]]
   - Logical frameworks : [[Dependent-Types|Link1]], [[Proof-Carrying-Code|Link2]]
   - The calculus of constructions : [[Dependent-Types|Link]]
   - The calculus of inductive constructions : [[Dependent-Types|Link]]
   - Pure type systems and the lambda cube : [[Dependent-Types|Link]]
   - Dependent ML : [[Dependent-Types|Link]]
   - Decidability of typechecking
   - Algorithmic type equality : [[Dependent-Types|Link]]

3. **Effect Types and Region-Based Memory Management** : [[Effect-Types-and-Region-Based-Memory-Management|Link]]
   - Type-based program analysis
   - Value flow analysis : [[Effect-Types-and-Region-Based-Memory-Management|Link]]
   - Effect types : [[Effect-Types-and-Region-Based-Memory-Management|Link]]
   - Region-based memory management : [[Effect-Types-and-Region-Based-Memory-Management|Link]]
   - Region safety and region polymorphism : [[Effect-Types-and-Region-Based-Memory-Management|Link]]
   - The Tofte–Talpin type system : [[Effect-Types-and-Region-Based-Memory-Management|Link]]
   - Region inference : [[Effect-Types-and-Region-Based-Memory-Management|Link]]
   - Region resetting and early deallocation
   - Imperative regions
   - Practical region-based systems : [[Logical-Relations-and-Equivalence-Checking|Link]]

4. **Typed Assembly Language** : [[Typed-Assembly-Language|Link]]
   - Control-flow safety : [[Typed-Assembly-Language|Link]]
   - The TAL-0 abstract machine and type system : [[Substructural-Type-Systems|Link1]], [[Typed-Assembly-Language|Link2]], [[ML-Type-Inference|Link3]]
   - Type soundness for typed assembly language : [[Typed-Assembly-Language|Link]]
   - Memory safety via unique and shared pointers
   - Stack typing with allocated type variables
   - Compiling a procedural language to typed assembly : [[Typed-Assembly-Language|Link]]
   - Calling conventions encoded in types
   - Existential types for closures and objects : [[Typed-Assembly-Language|Link]]
   - Dependent types for array bounds elimination : [[Typed-Assembly-Language|Link]]
   - Garbage collection and object initialization in TAL

5. **Proof-Carrying Code** : [[Proof-Carrying-Code|Link]]
   - Proof-carrying code architecture : [[Proof-Carrying-Code|Link]]
   - Verification condition generation : [[Proof-Carrying-Code|Link]]
   - Symbolic evaluation for low-level code : [[Proof-Carrying-Code|Link]]
   - Loop invariant annotations : [[Proof-Carrying-Code|Link]]
   - Soundness of verification condition generation : [[Proof-Carrying-Code|Link]]
   - The Edinburgh Logical Framework for proof representation : [[Proof-Carrying-Code|Link]]
   - Implicit LF and proof compression
   - Certifying compilers and automated proof generation : [[Proof-Carrying-Code|Link]]
   - Safety policies beyond type safety : [[Proof-Carrying-Code|Link]]

6. **Logical Relations and Equivalence Checking** : [[Logical-Relations-and-Equivalence-Checking|Link]]
   - Definitional equivalence of terms : [[Logical-Relations-and-Equivalence-Checking|Link1]], [[Typed-Operational-Reasoning|Link2]], [[Dependent-Types|Link3]]
   - The normalize-and-compare strategy : [[Logical-Relations-and-Equivalence-Checking|Link]]
   - Confluence and normalization of reduction : [[Typed-Operational-Reasoning|Link]]
   - Type-directed equivalence checking : [[Logical-Relations-and-Equivalence-Checking|Link1]], [[Proof-Carrying-Code|Link2]]
   - Weak head normalization and paths
   - Logical relations as a proof technique : [[Logical-Relations-and-Equivalence-Checking|Link]]
   - Monotonicity and Kripke logical relations : [[Typed-Operational-Reasoning|Link]]
   - The fundamental theorem via simultaneous substitutions
   - Completeness of equivalence algorithms : [[Logical-Relations-and-Equivalence-Checking|Link1]], [[Type-Definitions-and-Singleton-Kinds|Link2]], [[Typed-Operational-Reasoning|Link3]]

7. **Typed Operational Reasoning** : [[Typed-Operational-Reasoning|Link]]
   - Existential types and information hiding
   - Contextual equivalence of programs : [[Typed-Operational-Reasoning|Link]]
   - CIU equivalence : [[Typed-Operational-Reasoning|Link]]
   - Operationally based logical relations : [[Typed-Operational-Reasoning|Link]]
   - Extensionality principles for abstract data types : [[Typed-Operational-Reasoning|Link]]
   - Relational parametricity : [[Typed-Operational-Reasoning|Link]]
   - The unwinding theorem for recursive functions : [[Typed-Operational-Reasoning|Link]]
   - The value restriction on polymorphic generalization : [[Proof-Carrying-Code|Link1]], [[Typed-Operational-Reasoning|Link2]]
   - Incompleteness of logical relations at existential types : [[Typed-Operational-Reasoning|Link1]], [[Logical-Relations-and-Equivalence-Checking|Link2]]

8. **ML-Style Module Systems** : [[ML-Style-Module-Systems|Link]]
   - Modules signatures and linking : [[ML-Style-Module-Systems|Link]]
   - Structural versus nominal signature matching
   - Principal signatures : [[ML-Style-Module-Systems|Link]]
   - Separate versus incremental compilation
   - The phase distinction : [[ML-Style-Module-Systems|Link]]
   - First-class versus second-class modules : [[ML-Style-Module-Systems|Link]]
   - Translucent signatures and sealing : [[ML-Style-Module-Systems|Link]]
   - Representation independence
   - The avoidance problem : [[ML-Style-Module-Systems|Link1]], [[Type-Definitions-and-Singleton-Kinds|Link2]]
   - Module hierarchies and submodules : [[ML-Style-Module-Systems|Link]]
   - Functors and the coherence problem : [[ML-Style-Module-Systems|Link]]
   - Generative versus applicative functors : [[ML-Style-Module-Systems|Link]]
   - Higher-order and recursive modules

9. **Type Definitions and Singleton Kinds** : [[Type-Definitions-and-Singleton-Kinds|Link]]
   - Type definitions as primitive concepts : [[Type-Definitions-and-Singleton-Kinds|Link]]
   - Definitions in the typing context : [[Type-Definitions-and-Singleton-Kinds|Link]]
   - Delta reduction and weak head normalization
   - Algorithmic type equivalence with definitions : [[Dependent-Types|Link]]
   - Translucent sums and manifest types
   - Dependent module interfaces : [[Type-Definitions-and-Singleton-Kinds|Link1]], [[ML-Style-Module-Systems|Link2]]
   - Generative sealing and information hiding
   - Singleton kinds : [[Type-Definitions-and-Singleton-Kinds|Link]]
   - Phase splitting of modules into static and dynamic parts : [[Type-Definitions-and-Singleton-Kinds|Link]]

10. **ML Type Inference** : [[ML-Type-Inference|Link]]
    - ML the calculus versus ML the type system : [[ML-Type-Inference|Link]]
    - The Damas–Milner type system : [[ML-Type-Inference|Link]]
    - Constraint-based type inference : [[ML-Type-Inference|Link]]
    - The HM(X) parameterized type system : [[ML-Type-Inference|Link]]
    - Separation of constraint generation and constraint solving : [[Proof-Carrying-Code|Link1]], [[ML-Type-Inference|Link2]]
    - Type soundness via subject reduction and progress : [[Effect-Types-and-Region-Based-Memory-Management|Link1]], [[Typed-Assembly-Language|Link2]], [[Dependent-Types|Link3]]
    - The value restriction for effectful expressions : [[Typed-Operational-Reasoning|Link]]
    - First-order unification with multi-equations : [[ML-Type-Inference|Link]]
    - Let-polymorphism and generalization : [[Effect-Types-and-Region-Based-Memory-Management|Link]]
    - Algebraic data types and isorecursive types
    - Equirecursive types : [[Substructural-Type-Systems|Link]]
    - Rows and polymorphic records
    - Polymorphic variants and message dispatch

---
