# Types and Programming Languages — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Inductive Definitions and Proof Techniques** : [[Inductive-Definitions-and-Proof-Techniques|Link]]
   - Sets defined by inference rules : [[Inductive-Definitions-and-Proof-Techniques|Link]]
   - Induction on derivations : [[Inductive-Definitions-and-Proof-Techniques|Link]]
   - Structural induction on terms : [[Inductive-Definitions-and-Proof-Techniques|Link]]
   - Principle of induction on natural numbers : [[Inductive-Definitions-and-Proof-Techniques|Link]]
   - Rule induction and generation lemmas : [[Inductive-Definitions-and-Proof-Techniques|Link]]

2. **Operational Semantics** : [[Operational-Semantics|Link]]
   - Small-step evaluation relations : [[Operational-Semantics|Link]]
   - Big-step (natural) semantics : [[Operational-Semantics|Link]]
   - Abstract machines : [[Operational-Semantics|Link]]
   - Determinacy of the evaluation relation : [[Inductive-Definitions-and-Proof-Techniques|Link1]], [[Operational-Semantics|Link2]]
   - Normal forms versus values : [[Operational-Semantics|Link]]
   - Multi-step evaluation and termination : [[Operational-Semantics|Link]]

3. **Type Safety** : [[Type-Safety|Link]]
   - The subsumption-free typing relation : [[The-Simply-Typed-Lambda-Calculus|Link1]], [[Subtyping|Link2]]
   - Progress
   - Preservation : [[Type-Safety|Link1]], [[The-Simply-Typed-Lambda-Calculus|Link2]], [[Type-Reconstruction|Link3]]
   - Safety as progress plus preservation : [[Type-Safety|Link]]
   - Canonical forms lemmas : [[Canonical-Forms-Lemmas|Link]]
   - Type safety in the presence of state and exceptions : [[Type-Safety|Link]]

4. **The Untyped Lambda-Calculus** : [[The-Untyped-Lambda-Calculus|Link]]
   - Abstraction application and beta-reduction : [[Type-Operators-and-Kinding|Link1]], [[Universal-Types-(System-F)|Link2]]
   - Free and bound variables : [[The-Untyped-Lambda-Calculus|Link]]
   - Alpha-conversion and variable capture
   - Call by value call by name and full beta-reduction strategies
   - Encoding booleans numbers and pairs as lambda-terms : [[The-Untyped-Lambda-Calculus|Link]]
   - Fixed-point combinators : [[The-Untyped-Lambda-Calculus|Link]]
   - Divergence and the omega term : [[The-Untyped-Lambda-Calculus|Link]]

5. **Nameless Representation of Terms** : [[Nameless-Representation-of-Terms|Link]]
   - De Bruijn indices : [[Nameless-Representation-of-Terms|Link]]
   - Shifting and substitution on nameless terms : [[Nameless-Representation-of-Terms|Link]]
   - Context length as a well-formedness check
   - Naming and printing as inverse operations to parsing : [[Nameless-Representation-of-Terms|Link]]

6. **The Simply Typed Lambda-Calculus** : [[The-Simply-Typed-Lambda-Calculus|Link]]
   - Function types : [[Canonical-Forms-Lemmas|Link1]], [[The-Simply-Typed-Lambda-Calculus|Link2]], [[Type-Operators-and-Kinding|Link3]]
   - The typing relation : [[The-Simply-Typed-Lambda-Calculus|Link1]], [[Type-Safety|Link2]]
   - Uniqueness of types : [[The-Simply-Typed-Lambda-Calculus|Link]]
   - Inversion of the typing relation : [[The-Simply-Typed-Lambda-Calculus|Link]]
   - Erasure and typability : [[The-Simply-Typed-Lambda-Calculus|Link1]], [[Universal-Types-(System-F)|Link2]]
   - Curry-style versus Church-style typing : [[The-Simply-Typed-Lambda-Calculus|Link]]

7. **The Curry-Howard Correspondence** : [[The-Curry-Howard-Correspondence|Link]]
   - Propositions as types : [[Dependent-Types|Link1]], [[The-Curry-Howard-Correspondence|Link2]]
   - Proofs as programs : [[The-Curry-Howard-Correspondence|Link]]
   - Conjunction as product type and implication as function type : [[The-Curry-Howard-Correspondence|Link]]

8. **Core Language Extensions** : [[Core-Language-Extensions|Link]]
   - Base types and the unit type : [[Core-Language-Extensions|Link]]
   - Ascription
   - Let bindings : [[Type-Operators-and-Kinding|Link]]
   - Products and tuples : [[Core-Language-Extensions|Link]]
   - Records
   - Sums and variants : [[Core-Language-Extensions|Link]]
   - General recursion and the fix operator : [[Core-Language-Extensions|Link]]
   - Lists as a built-in type : [[Core-Language-Extensions|Link1]], [[Subtyping|Link2]], [[Existential-Types|Link3]]
   - Derived forms as syntactic sugar

9. **Normalization** : [[Normalization|Link]]
   - Termination of the simply typed lambda-calculus : [[The-Simply-Typed-Lambda-Calculus|Link]]
   - Tait's method of logical relations
   - Reducibility candidates

10. **Imperative Features** : [[Imperative-Features|Link]]
    - Reference cells : [[Inductive-Definitions-and-Proof-Techniques|Link]]
    - The store and store typings : [[Existential-Types|Link1]], [[Higher-Order-Subtyping|Link2]]
    - Aliasing : [[Normalization|Link]]
    - Garbage and unreachable locations : [[Imperative-Features|Link]]
    - Exceptions as a control construct : [[Subtyping|Link]]
    - Exceptions carrying values : [[Imperative-Features|Link]]

11. **Subtyping** : [[Subtyping|Link]]
    - The subsumption rule : [[Subtyping|Link]]
    - The subtype relation as a preorder : [[Subtyping|Link]]
    - Width depth and permutation subtyping for records : [[Subtyping|Link]]
    - The Top and Bottom types : [[Metatheory-of-Bounded-Quantification|Link]]
    - Interaction of subtyping with other language features
    - Coercion semantics for subtyping : [[Subtyping|Link]]
    - Intersection and union types : [[Subtyping|Link]]

12. **Metatheory and Algorithms for Subtyping** : [[Coinduction-and-Infinite-Types|Link]]
    - Algorithmic (syntax-directed) subtyping
    - Algorithmic typing and minimal types : [[Metatheory-of-Bounded-Quantification|Link]]
    - Joins and meets : [[Metatheory-of-Bounded-Quantification|Link]]
    - Decidability of subtype checking : [[ML-Implementation-Techniques|Link]]

13. **Object Encodings with Imperative State** : [[Object-Encodings-with-Imperative-State|Link]]
    - Objects as records of mutable methods : [[Object-Encodings-with-Imperative-State|Link]]
    - Object generators and classes : [[Object-Encodings-with-Imperative-State|Link]]
    - Instance variables and encapsulation : [[Object-Encodings-with-Imperative-State|Link]]
    - Calling superclass methods : [[Object-Encodings-with-Imperative-State|Link]]
    - Open recursion through self : [[Object-Encodings-with-Imperative-State|Link]]
    - Efficient method-table construction : [[Object-Encodings-with-Imperative-State|Link]]

14. **Nominal versus Structural Typing** : [[Nominal-versus-Structural-Typing|Link]]
    - Featherweight Java as a core calculus for Java : [[Nominal-versus-Structural-Typing|Link]]
    - Nominal versus structural type systems : [[Nominal-versus-Structural-Typing|Link]]
    - Classes fields methods and casts : [[Purely-Functional-Object-Encodings|Link]]
    - Encodings of objects versus primitive object calculi : [[Nominal-versus-Structural-Typing|Link]]

15. **Recursive Types** : [[Recursive-Types|Link]]
    - Iso-recursive versus equi-recursive types : [[Recursive-Types|Link]]
    - The fold and unfold operations
    - Encoding recursive data structures such as lists and streams
    - Divergence introduced by unrestricted recursive types

16. **Coinduction and Infinite Types** : [[Coinduction-and-Infinite-Types|Link]]
    - Finite versus infinite regular trees : [[Coinduction-and-Infinite-Types|Link]]
    - Coinductive definitions and coinductive proof : [[Inductive-Definitions-and-Proof-Techniques|Link]]
    - Subtyping of equi-recursive types : [[Recursive-Types|Link1]], [[Object-Encodings-with-Imperative-State|Link2]]
    - Membership-checking algorithms for recursive types
    - Regular trees and their finite representations : [[Coinduction-and-Infinite-Types|Link]]

17. **Type Reconstruction** : [[Type-Reconstruction|Link]]
    - Type variables and substitutions : [[Type-Reconstruction|Link]]
    - Constraint-based typing : [[Type-Reconstruction|Link]]
    - Unification and most general unifiers : [[Type-Reconstruction|Link]]
    - Principal types : [[Type-Reconstruction|Link]]
    - Implicit type annotations : [[Type-Reconstruction|Link]]
    - Let-polymorphism : [[Type-Reconstruction|Link]]

18. **Universal Types (System F)** : [[Universal-Types-(System-F)|Link]]
    - Varieties of polymorphism : [[Universal-Types-(System-F)|Link]]
    - Type abstraction and type application : [[Universal-Types-(System-F)|Link]]
    - Church encodings of data at the level of types : [[Universal-Types-(System-F)|Link]]
    - Erasure typability and type reconstruction for System F : [[Universal-Types-(System-F)|Link]]
    - Fragments of System F such as prenex and rank-2 polymorphism : [[Universal-Types-(System-F)|Link]]
    - Parametricity : [[Universal-Types-(System-F)|Link]]
    - Impredicativity : [[Universal-Types-(System-F)|Link]]

19. **Existential Types** : [[Existential-Types|Link]]
    - Packing and unpacking existential values : [[Existential-Types|Link]]
    - Abstract data types via existential types : [[Bounded-Quantification|Link1]], [[Existential-Types|Link2]]
    - Existential encodings of simple objects
    - Weak versus strong binary operations : [[Existential-Types|Link]]
    - Encoding existentials in terms of universals : [[Existential-Types|Link]]

20. **Bounded Quantification** : [[Bounded-Quantification|Link]]
    - Combining subtyping with polymorphism
    - Kernel versus full variants of the quantifier subtyping rule
    - Bounded existential types : [[Bounded-Quantification|Link]]
    - F-bounded quantification : [[Bounded-Quantification|Link]]

21. **Metatheory of Bounded Quantification** : [[Metatheory-of-Bounded-Quantification|Link]]
    - The exposure relation and minimal typing : [[Metatheory-of-Bounded-Quantification|Link]]
    - Decidability of subtyping in kernel $F_{<:}$
    - Undecidability of subtyping in full $F_{<:}$ : [[Metatheory-of-Bounded-Quantification|Link]]
    - Joins and meets under bounded quantification : [[Metatheory-of-Bounded-Quantification|Link1]], [[Bounded-Quantification|Link2]]
    - The bottom type in bounded systems : [[Metatheory-of-Bounded-Quantification|Link]]

22. **Type Operators and Kinding** : [[Type-Operators-and-Kinding|Link]]
    - Abstraction and application at the level of types : [[Type-Operators-and-Kinding|Link]]
    - Kinds as the types of types : [[Type-Operators-and-Kinding|Link]]
    - Definitional equivalence of types : [[Type-Operators-and-Kinding|Link]]
    - Higher-order type operators : [[Higher-Order-Subtyping|Link]]

23. **Higher-Order Polymorphism (System $F^\omega$)** : [[Higher-Order-Polymorphism-(System-F-omega)|Link]]
    - Combining type operators with universal quantification : [[Bounded-Quantification|Link1]], [[Metatheory-of-Bounded-Quantification|Link2]]
    - Parallel reduction and confluence of type-level reduction
    - Preservation and progress for $F^\omega$
    - The hierarchy of systems from $F_1$ to $F^\omega$ : [[Higher-Order-Polymorphism-(System-F-omega)|Link1]], [[Type-Operators-and-Kinding|Link2]]
    - The Barendregt cube : [[Dependent-Types|Link1]], [[Higher-Order-Polymorphism-(System-F-omega)|Link2]]

24. **Dependent Types** : [[Dependent-Types|Link]]
    - Types indexed by terms : [[Dependent-Types|Link]]
    - Dependent function (Pi) types : [[Dependent-Types|Link1]], [[The-Simply-Typed-Lambda-Calculus|Link2]]
    - Logical frameworks and proof assistants : [[Dependent-Types|Link]]
    - Propositions as types in dependently typed calculi

25. **Higher-Order Subtyping** : [[Higher-Order-Subtyping|Link]]
    - Pointwise subtyping between type operators : [[Higher-Order-Subtyping|Link]]
    - Interaction of kinding subtyping and type equivalence : [[Higher-Order-Subtyping|Link1]], [[Inductive-Definitions-and-Proof-Techniques|Link2]]
    - Covariant and contravariant type operators : [[Higher-Order-Subtyping|Link1]], [[Subtyping|Link2]]

26. **Purely Functional Object Encodings** : [[Purely-Functional-Object-Encodings|Link]]
    - Interface types and the abstract Object type operator : [[Universal-Types-(System-F)|Link]]
    - Polymorphic record update : [[Purely-Functional-Object-Encodings|Link]]
    - Classes with self in a purely functional setting : [[Purely-Functional-Object-Encodings|Link1]], [[Recursive-Types|Link2]]
    - Adding instance variables in subclasses : [[Purely-Functional-Object-Encodings|Link]]

27. **ML Implementation Techniques** : [[ML-Implementation-Techniques|Link]]
    - Representing terms and types as OCaml datatypes : [[ML-Implementation-Techniques|Link]]
    - Contexts as lists of bindings : [[ML-Implementation-Techniques|Link]]
    - Generic shifting and substitution via mapping functions : [[ML-Implementation-Techniques|Link]]
    - Syntax-directed typechecking algorithms in code : [[ML-Implementation-Techniques|Link1]], [[The-Simply-Typed-Lambda-Calculus|Link2]], [[The-Untyped-Lambda-Calculus|Link3]]

---
