# Types and Programming Languages — Index

[[book-guidelines|↩ Back to guidelines]]

1. **[[Inductive-Definitions-and-Proof-Techniques|Inductive Definitions and Proof Techniques]]**
   - [[Inductive-Definitions-and-Proof-Techniques|Sets defined by inference rules]]
   - [[Inductive-Definitions-and-Proof-Techniques|Induction on derivations]]
   - [[Inductive-Definitions-and-Proof-Techniques|Structural induction on terms]]
   - [[Inductive-Definitions-and-Proof-Techniques|Principle of induction on natural numbers]]
   - [[Inductive-Definitions-and-Proof-Techniques|Rule induction and generation lemmas]]

2. **[[Operational-Semantics|Operational Semantics]]**
   - [[Operational-Semantics|Small-step evaluation relations]]
   - [[Operational-Semantics|Big-step (natural) semantics]]
   - [[Operational-Semantics|Abstract machines]]
   - [[Inductive-Definitions-and-Proof-Techniques|Determinacy of the evaluation relation]]
   - [[Operational-Semantics|Normal forms versus values]]
   - [[Operational-Semantics|Multi-step evaluation and termination]]

3. **[[Type-Safety|Type Safety]]**
   - [[The-Simply-Typed-Lambda-Calculus|The subsumption-free typing relation]]
   - [[The-Simply-Typed-Lambda-Calculus|Progress]]
   - [[Higher-Order-Polymorphism-(System-F-omega)|Preservation]]
   - [[Type-Safety|Safety as progress plus preservation]]
   - Canonical forms lemmas
   - [[Type-Safety|Type safety in the presence of state and exceptions]]

4. **[[The-Untyped-Lambda-Calculus|The Untyped Lambda-Calculus]]**
   - [[Type-Operators-and-Kinding|Abstraction application and beta-reduction]]
   - [[The-Untyped-Lambda-Calculus|Free and bound variables]]
   - Alpha-conversion and variable capture
   - Call by value call by name and full beta-reduction strategies
   - [[The-Untyped-Lambda-Calculus|Encoding booleans numbers and pairs as lambda-terms]]
   - [[The-Untyped-Lambda-Calculus|Fixed-point combinators]]
   - [[The-Untyped-Lambda-Calculus|Divergence and the omega term]]

5. **[[Nameless-Representation-of-Terms|Nameless Representation of Terms]]**
   - [[Nameless-Representation-of-Terms|De Bruijn indices]]
   - [[Nameless-Representation-of-Terms|Shifting and substitution on nameless terms]]
   - Context length as a well-formedness check
   - [[Nameless-Representation-of-Terms|Naming and printing as inverse operations to parsing]]

6. **[[The-Simply-Typed-Lambda-Calculus|The Simply Typed Lambda-Calculus]]**
   - [[The-Simply-Typed-Lambda-Calculus|Function types]]
   - [[The-Simply-Typed-Lambda-Calculus|The typing relation]]
   - [[The-Simply-Typed-Lambda-Calculus|Uniqueness of types]]
   - [[The-Simply-Typed-Lambda-Calculus|Inversion of the typing relation]]
   - [[The-Simply-Typed-Lambda-Calculus|Erasure and typability]]
   - [[The-Simply-Typed-Lambda-Calculus|Curry-style versus Church-style typing]]

7. **[[The-Curry-Howard-Correspondence|The Curry-Howard Correspondence]]**
   - [[Dependent-Types|Propositions as types]]
   - [[The-Curry-Howard-Correspondence|Proofs as programs]]
   - [[The-Curry-Howard-Correspondence|Conjunction as product type and implication as function type]]

8. **[[Core-Language-Extensions|Core Language Extensions]]**
   - [[Core-Language-Extensions|Base types and the unit type]]
   - [[Core-Language-Extensions|Ascription]]
   - [[Type-Operators-and-Kinding|Let bindings]]
   - [[Core-Language-Extensions|Products and tuples]]
   - [[Core-Language-Extensions|Records]]
   - [[Core-Language-Extensions|Sums and variants]]
   - [[Core-Language-Extensions|General recursion and the fix operator]]
   - [[Core-Language-Extensions|Lists as a built-in type]]
   - Derived forms as syntactic sugar

9. **[[Normalization|Normalization]]**
   - [[The-Simply-Typed-Lambda-Calculus|Termination of the simply typed lambda-calculus]]
   - Tait's method of logical relations
   - Reducibility candidates

10. **[[Imperative-Features|Imperative Features]]**
    - [[Inductive-Definitions-and-Proof-Techniques|Reference cells]]
    - [[Existential-Types|The store and store typings]]
    - [[Imperative-Features|Aliasing]]
    - [[Imperative-Features|Garbage and unreachable locations]]
    - [[Subtyping|Exceptions as a control construct]]
    - [[Imperative-Features|Exceptions carrying values]]

11. **[[Subtyping|Subtyping]]**
    - [[Subtyping|The subsumption rule]]
    - [[Subtyping|The subtype relation as a preorder]]
    - [[Subtyping|Width depth and permutation subtyping for records]]
    - [[Metatheory-of-Bounded-Quantification|The Top and Bottom types]]
    - Interaction of subtyping with other language features
    - [[Subtyping|Coercion semantics for subtyping]]
    - [[Subtyping|Intersection and union types]]

12. **[[Coinduction-and-Infinite-Types|Metatheory and Algorithms for Subtyping]]**
    - Algorithmic (syntax-directed) subtyping
    - [[Metatheory-of-Bounded-Quantification|Algorithmic typing and minimal types]]
    - [[Metatheory-of-Bounded-Quantification|Joins and meets]]
    - [[ML-Implementation-Techniques|Decidability of subtype checking]]

13. **[[Object-Encodings-with-Imperative-State|Object Encodings with Imperative State]]**
    - [[Object-Encodings-with-Imperative-State|Objects as records of mutable methods]]
    - [[Object-Encodings-with-Imperative-State|Object generators and classes]]
    - [[Object-Encodings-with-Imperative-State|Instance variables and encapsulation]]
    - [[Object-Encodings-with-Imperative-State|Calling superclass methods]]
    - [[Object-Encodings-with-Imperative-State|Open recursion through self]]
    - [[Object-Encodings-with-Imperative-State|Efficient method-table construction]]

14. **[[Nominal-versus-Structural-Typing|Nominal versus Structural Typing]]**
    - [[Nominal-versus-Structural-Typing|Featherweight Java as a core calculus for Java]]
    - [[Nominal-versus-Structural-Typing|Nominal versus structural type systems]]
    - [[Purely-Functional-Object-Encodings|Classes fields methods and casts]]
    - [[Nominal-versus-Structural-Typing|Encodings of objects versus primitive object calculi]]

15. **[[Recursive-Types|Recursive Types]]**
    - [[Recursive-Types|Iso-recursive versus equi-recursive types]]
    - The fold and unfold operations
    - Encoding recursive data structures such as lists and streams
    - Divergence introduced by unrestricted recursive types

16. **[[Coinduction-and-Infinite-Types|Coinduction and Infinite Types]]**
    - [[Coinduction-and-Infinite-Types|Finite versus infinite regular trees]]
    - [[Inductive-Definitions-and-Proof-Techniques|Coinductive definitions and coinductive proof]]
    - [[Recursive-Types|Subtyping of equi-recursive types]]
    - Membership-checking algorithms for recursive types
    - [[Coinduction-and-Infinite-Types|Regular trees and their finite representations]]

17. **[[Type-Reconstruction|Type Reconstruction]]**
    - [[Type-Reconstruction|Type variables and substitutions]]
    - [[Type-Reconstruction|Constraint-based typing]]
    - [[Type-Reconstruction|Unification and most general unifiers]]
    - [[Type-Reconstruction|Principal types]]
    - [[Type-Reconstruction|Implicit type annotations]]
    - [[Type-Reconstruction|Let-polymorphism]]

18. **[[Universal-Types-(System-F)|Universal Types (System F)]]**
    - [[Universal-Types-(System-F)|Varieties of polymorphism]]
    - [[Universal-Types-(System-F)|Type abstraction and type application]]
    - [[Universal-Types-(System-F)|Church encodings of data at the level of types]]
    - [[Universal-Types-(System-F)|Erasure typability and type reconstruction for System F]]
    - [[Universal-Types-(System-F)|Fragments of System F such as prenex and rank-2 polymorphism]]
    - [[Universal-Types-(System-F)|Parametricity]]
    - [[Universal-Types-(System-F)|Impredicativity]]

19. **[[Existential-Types|Existential Types]]**
    - [[Existential-Types|Packing and unpacking existential values]]
    - [[Bounded-Quantification|Abstract data types via existential types]]
    - Existential encodings of simple objects
    - [[Existential-Types|Weak versus strong binary operations]]
    - [[Existential-Types|Encoding existentials in terms of universals]]

20. **[[Bounded-Quantification|Bounded Quantification]]**
    - Combining subtyping with polymorphism
    - Kernel versus full variants of the quantifier subtyping rule
    - [[Bounded-Quantification|Bounded existential types]]
    - [[Bounded-Quantification|F-bounded quantification]]

21. **[[Metatheory-of-Bounded-Quantification|Metatheory of Bounded Quantification]]**
    - [[Metatheory-of-Bounded-Quantification|The exposure relation and minimal typing]]
    - Decidability of subtyping in kernel $F_{<:}$
    - [[Metatheory-of-Bounded-Quantification|Undecidability of subtyping in full $F_{<:}$]]
    - [[Metatheory-of-Bounded-Quantification|Joins and meets under bounded quantification]]
    - [[Metatheory-of-Bounded-Quantification|The bottom type in bounded systems]]

22. **[[Type-Operators-and-Kinding|Type Operators and Kinding]]**
    - [[Type-Operators-and-Kinding|Abstraction and application at the level of types]]
    - [[Type-Operators-and-Kinding|Kinds as the types of types]]
    - [[Type-Operators-and-Kinding|Definitional equivalence of types]]
    - [[Higher-Order-Subtyping|Higher-order type operators]]

23. **[[Higher-Order-Polymorphism-(System-F-omega)|Higher-Order Polymorphism (System $F^\omega$)]]**
    - [[Bounded-Quantification|Combining type operators with universal quantification]]
    - Parallel reduction and confluence of type-level reduction
    - Preservation and progress for $F^\omega$
    - [[Higher-Order-Polymorphism-(System-F-omega)|The hierarchy of systems from $F_1$ to $F^\omega$]]
    - [[Dependent-Types|The Barendregt cube]]

24. **[[Dependent-Types|Dependent Types]]**
    - [[Dependent-Types|Types indexed by terms]]
    - [[Dependent-Types|Dependent function (Pi) types]]
    - [[Dependent-Types|Logical frameworks and proof assistants]]
    - Propositions as types in dependently typed calculi

25. **[[Higher-Order-Subtyping|Higher-Order Subtyping]]**
    - [[Higher-Order-Subtyping|Pointwise subtyping between type operators]]
    - [[Higher-Order-Subtyping|Interaction of kinding subtyping and type equivalence]]
    - [[Higher-Order-Subtyping|Covariant and contravariant type operators]]

26. **[[Purely-Functional-Object-Encodings|Purely Functional Object Encodings]]**
    - [[Universal-Types-(System-F)|Interface types and the abstract Object type operator]]
    - [[Purely-Functional-Object-Encodings|Polymorphic record update]]
    - [[Purely-Functional-Object-Encodings|Classes with self in a purely functional setting]]
    - [[Purely-Functional-Object-Encodings|Adding instance variables in subclasses]]

27. **[[ML-Implementation-Techniques|ML Implementation Techniques]]**
    - [[ML-Implementation-Techniques|Representing terms and types as OCaml datatypes]]
    - [[ML-Implementation-Techniques|Contexts as lists of bindings]]
    - [[ML-Implementation-Techniques|Generic shifting and substitution via mapping functions]]
    - [[ML-Implementation-Techniques|Syntax-directed typechecking algorithms in code]]

---
