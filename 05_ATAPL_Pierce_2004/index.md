# Advanced Topics in Types and Programming Languages — Index

[[book-guidelines|↩ Back to guidelines]]

1. **[[Substructural-Type-Systems|Substructural Type Systems]]**
   - Structural properties exchange weakening and contraction
   - Linear affine relevant and ordered type systems
   - [[Substructural-Type-Systems|Context splitting]]
   - [[Dependent-Types|Algorithmic linear type checking]]
   - [[Substructural-Type-Systems|Sums and recursive types in a substructural setting]]
   - [[Substructural-Type-Systems|Parametric polymorphism over types and usage qualifiers]]
   - Linear arrays and swap-based access
   - [[Substructural-Type-Systems|Reference counting as a substructural discipline]]
   - [[Substructural-Type-Systems|Ordered types and stack-based allocation]]
   - [[Substructural-Type-Systems|Substructural types for guaranteeing polynomial time]]
   - [[Substructural-Type-Systems|Substructural types for compiler optimization]]

2. **[[Dependent-Types|Dependent Types]]**
   - [[Dependent-Types|Pi types and dependent products]]
   - Sigma types and dependent sums
   - [[Dependent-Types|The Curry–Howard correspondence]]
   - [[Dependent-Types|Logical frameworks]]
   - [[Dependent-Types|The calculus of constructions]]
   - [[Dependent-Types|The calculus of inductive constructions]]
   - [[Dependent-Types|Pure type systems and the lambda cube]]
   - [[Dependent-Types|Dependent ML]]
   - Decidability of typechecking
   - [[Dependent-Types|Algorithmic type equality]]

3. **[[Effect-Types-and-Region-Based-Memory-Management|Effect Types and Region-Based Memory Management]]**
   - Type-based program analysis
   - [[Effect-Types-and-Region-Based-Memory-Management|Value flow analysis]]
   - [[Effect-Types-and-Region-Based-Memory-Management|Effect types]]
   - [[Effect-Types-and-Region-Based-Memory-Management|Region-based memory management]]
   - [[Effect-Types-and-Region-Based-Memory-Management|Region safety and region polymorphism]]
   - [[Effect-Types-and-Region-Based-Memory-Management|The Tofte–Talpin type system]]
   - [[Effect-Types-and-Region-Based-Memory-Management|Region inference]]
   - Region resetting and early deallocation
   - Imperative regions
   - [[Logical-Relations-and-Equivalence-Checking|Practical region-based systems]]

4. **[[Typed-Assembly-Language|Typed Assembly Language]]**
   - [[Typed-Assembly-Language|Control-flow safety]]
   - [[Substructural-Type-Systems|The TAL-0 abstract machine and type system]]
   - [[Typed-Assembly-Language|Type soundness for typed assembly language]]
   - Memory safety via unique and shared pointers
   - Stack typing with allocated type variables
   - [[Typed-Assembly-Language|Compiling a procedural language to typed assembly]]
   - Calling conventions encoded in types
   - [[Typed-Assembly-Language|Existential types for closures and objects]]
   - [[Typed-Assembly-Language|Dependent types for array bounds elimination]]
   - Garbage collection and object initialization in TAL

5. **[[Proof-Carrying-Code|Proof-Carrying Code]]**
   - [[Proof-Carrying-Code|Proof-carrying code architecture]]
   - [[Proof-Carrying-Code|Verification condition generation]]
   - [[Proof-Carrying-Code|Symbolic evaluation for low-level code]]
   - [[Proof-Carrying-Code|Loop invariant annotations]]
   - [[Proof-Carrying-Code|Soundness of verification condition generation]]
   - [[Proof-Carrying-Code|The Edinburgh Logical Framework for proof representation]]
   - Implicit LF and proof compression
   - [[Proof-Carrying-Code|Certifying compilers and automated proof generation]]
   - [[Proof-Carrying-Code|Safety policies beyond type safety]]

6. **[[Logical-Relations-and-Equivalence-Checking|Logical Relations and Equivalence Checking]]**
   - [[Logical-Relations-and-Equivalence-Checking|Definitional equivalence of terms]]
   - [[Logical-Relations-and-Equivalence-Checking|The normalize-and-compare strategy]]
   - [[Typed-Operational-Reasoning|Confluence and normalization of reduction]]
   - [[Logical-Relations-and-Equivalence-Checking|Type-directed equivalence checking]]
   - Weak head normalization and paths
   - [[Logical-Relations-and-Equivalence-Checking|Logical relations as a proof technique]]
   - [[Typed-Operational-Reasoning|Monotonicity and Kripke logical relations]]
   - The fundamental theorem via simultaneous substitutions
   - [[Logical-Relations-and-Equivalence-Checking|Completeness of equivalence algorithms]]

7. **[[Typed-Operational-Reasoning|Typed Operational Reasoning]]**
   - Existential types and information hiding
   - [[Typed-Operational-Reasoning|Contextual equivalence of programs]]
   - [[Typed-Operational-Reasoning|CIU equivalence]]
   - [[Typed-Operational-Reasoning|Operationally based logical relations]]
   - [[Typed-Operational-Reasoning|Extensionality principles for abstract data types]]
   - [[Typed-Operational-Reasoning|Relational parametricity]]
   - [[Typed-Operational-Reasoning|The unwinding theorem for recursive functions]]
   - [[Proof-Carrying-Code|The value restriction on polymorphic generalization]]
   - [[Typed-Operational-Reasoning|Incompleteness of logical relations at existential types]]

8. **[[ML-Style-Module-Systems|ML-Style Module Systems]]**
   - [[ML-Style-Module-Systems|Modules signatures and linking]]
   - Structural versus nominal signature matching
   - [[ML-Style-Module-Systems|Principal signatures]]
   - Separate versus incremental compilation
   - [[ML-Style-Module-Systems|The phase distinction]]
   - [[ML-Style-Module-Systems|First-class versus second-class modules]]
   - [[ML-Style-Module-Systems|Translucent signatures and sealing]]
   - Representation independence
   - [[ML-Style-Module-Systems|The avoidance problem]]
   - [[ML-Style-Module-Systems|Module hierarchies and submodules]]
   - [[ML-Style-Module-Systems|Functors and the coherence problem]]
   - [[ML-Style-Module-Systems|Generative versus applicative functors]]
   - Higher-order and recursive modules

9. **[[Type-Definitions-and-Singleton-Kinds|Type Definitions and Singleton Kinds]]**
   - [[Type-Definitions-and-Singleton-Kinds|Type definitions as primitive concepts]]
   - [[Type-Definitions-and-Singleton-Kinds|Definitions in the typing context]]
   - Delta reduction and weak head normalization
   - [[Dependent-Types|Algorithmic type equivalence with definitions]]
   - Translucent sums and manifest types
   - [[Type-Definitions-and-Singleton-Kinds|Dependent module interfaces]]
   - Generative sealing and information hiding
   - [[Type-Definitions-and-Singleton-Kinds|Singleton kinds]]
   - [[Type-Definitions-and-Singleton-Kinds|Phase splitting of modules into static and dynamic parts]]

10. **[[ML-Type-Inference|ML Type Inference]]**
    - [[ML-Type-Inference|ML the calculus versus ML the type system]]
    - [[ML-Type-Inference|The Damas–Milner type system]]
    - [[ML-Type-Inference|Constraint-based type inference]]
    - [[ML-Type-Inference|The HM(X) parameterized type system]]
    - [[Proof-Carrying-Code|Separation of constraint generation and constraint solving]]
    - [[Effect-Types-and-Region-Based-Memory-Management|Type soundness via subject reduction and progress]]
    - [[Typed-Operational-Reasoning|The value restriction for effectful expressions]]
    - [[ML-Type-Inference|First-order unification with multi-equations]]
    - [[Effect-Types-and-Region-Based-Memory-Management|Let-polymorphism and generalization]]
    - Algebraic data types and isorecursive types
    - [[Substructural-Type-Systems|Equirecursive types]]
    - Rows and polymorphic records
    - Polymorphic variants and message dispatch

---
