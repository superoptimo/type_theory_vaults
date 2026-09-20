# Dependently Typed Functional Programs and their Proofs — Index

[[book-guidelines|↩ Back to guidelines]]

1. **The OLEG Type Theory of Holes** : [[The-OLEG-Type-Theory-of-Holes|Link]]
   - Universes identifiers bindings and terms : [[The-OLEG-Type-Theory-of-Holes|Link]]
   - Contexts and judgments with active computation : [[The-OLEG-Type-Theory-of-Holes|Link]]
   - Contraction schemes and compatible closure : [[The-OLEG-Type-Theory-of-Holes|Link]]
   - Cumulativity and typical ambiguity : [[The-OLEG-Type-Theory-of-Holes|Link]]
   - Core inference rules and metatheoretic properties : [[The-OLEG-Type-Theory-of-Holes|Link]]
   - The development calculus separating partial constructions from core terms
   - States components and partial constructions
   - Positions and the replacement property : [[The-OLEG-Type-Theory-of-Holes|Link]]
   - The state information order and monotonicity : [[The-OLEG-Type-Theory-of-Holes|Link]]
   - Basic component manipulations as tactics
   - Moving holes by raising and introduction : [[The-OLEG-Type-Theory-of-Holes|Link]]
   - Refinement and object-level unification under a mixed prefix : [[Equality-and-Object-Level-Unification|Link1]], [[The-OLEG-Type-Theory-of-Holes|Link2]]
   - Discharge and permutation of context components : [[The-OLEG-Type-Theory-of-Holes|Link]]
   - Comparison with explicit-substitution treatments of holes : [[The-OLEG-Type-Theory-of-Holes|Link]]
   - Telescopes triangles and indexed families notation : [[The-OLEG-Type-Theory-of-Holes|Link]]

2. **Elimination Rules for Refinement Proof** : [[Elimination-Rules-for-Refinement-Proof|Link]]
   - Introduction rules versus elimination rules : [[Elimination-Rules-for-Refinement-Proof|Link1]], [[Inductive-Datatypes-and-Their-Elimination|Link2]]
   - Anatomy of an elimination rule target scheme aperture and patterns : [[Elimination-Rules-for-Refinement-Proof|Link]]
   - Case analysis and inversion principles
   - Recursion induction for functions
   - Legitimate targets and target annotation : [[Elimination-Rules-for-Refinement-Proof|Link]]
   - Constrained scheme construction from a rule aperture
   - Simplification by coalescence
   - Choosing what to fix and what to abstract
   - Abstracting patterns from the goal for rewriting : [[Pattern-Matching-for-Dependent-Types|Link]]
   - Friendly versus unfriendly constraints in inductive proofs
   - The eliminate tactic preparation targeting scheming proving and tidying

3. **Inductive Datatypes and Their Elimination** : [[Inductive-Datatypes-and-Their-Elimination|Link]]
   - Components of an inductive datatype definition : [[Inductive-Datatypes-and-Their-Elimination|Link]]
   - Simple parameterised and higher-order recursive datatypes
   - Dependent inductive families : [[Inductive-Datatypes-and-Their-Elimination|Link]]
   - Inductively defined relations as proof-irrelevant families : [[Inductive-Datatypes-and-Their-Elimination|Link]]
   - Record types as degenerate datatypes : [[Inductive-Datatypes-and-Their-Elimination|Link]]
   - The blunderbuss search tactic
   - Deriving Case and Fix from the traditional eliminator : [[Inductive-Datatypes-and-Their-Elimination|Link]]
   - The guarded fixpoint principle and auxiliary recursion data

4. **Equality and Object-Level Unification** : [[Equality-and-Object-Level-Unification|Link]]
   - Martin-Löf's identity type and idElim : [[Equality-and-Object-Level-Unification|Link]]
   - Uniqueness of identity proofs : [[Equality-and-Object-Level-Unification|Link]]
   - John Major equality : [[Equality-and-Object-Level-Unification|Link]]
   - Equality for sequences and telescopic equations : [[Equality-and-Object-Level-Unification|Link]]
   - Equivalence of intensional equality and John Major equality : [[Equality-and-Object-Level-Unification|Link]]
   - First-order unification for constructor forms : [[Equality-and-Object-Level-Unification|Link]]
   - Transition rules identity coalescence substitution conflict injectivity cycle
   - Most general unifiers and termination of unification
   - The Peano concerto for injectivity and conflict : [[Equality-and-Object-Level-Unification|Link]]
   - Proving absence of cyclic equations
   - Limits of constructor-form unification : [[Equality-and-Object-Level-Unification|Link]]

5. **Pattern Matching for Dependent Types** : [[Pattern-Matching-for-Dependent-Types|Link]]
   - Coquand's characterisation of pattern matching in ALF : [[Pattern-Matching-for-Dependent-Types|Link]]
   - Elementary coverings and coverings by case-splitting : [[Pattern-Matching-for-Dependent-Types|Link]]
   - Computational aspects of elimination unfolding and folding : [[Pattern-Matching-for-Dependent-Types|Link]]
   - Conservativity of pattern matching over OLEG : [[Pattern-Matching-for-Dependent-Types|Link]]
   - Constructing programs interactively with program split and return : [[Pattern-Matching-for-Dependent-Types|Link]]
   - Recognising programs recursion spotting exact splitting and empty problems : [[Pattern-Matching-for-Dependent-Types|Link]]
   - Functions with varying arity : [[Pattern-Matching-for-Dependent-Types|Link]]
   - Exotic and lexicographic recursion structures : [[Pattern-Matching-for-Dependent-Types|Link]]

6. **Concrete Categories Functors and Monads for Syntax** : [[Concrete-Categories-Functors-and-Monads-for-Syntax|Link]]
   - Concrete categories and faithful interpretation : [[Concrete-Categories-Functors-and-Monads-for-Syntax|Link]]
   - Functors and preservation of extensional equality : [[Concrete-Categories-Functors-and-Monads-for-Syntax|Link]]
   - Concrete monads splitting a functor Kleisli triples : [[Concrete-Categories-Functors-and-Monads-for-Syntax|Link]]
   - Substitution for the untyped lambda-calculus with de Bruijn indices : [[Concrete-Categories-Functors-and-Monads-for-Syntax|Link]]
   - Lifting thinning and thickening of variables : [[Concrete-Categories-Functors-and-Monads-for-Syntax|Link]]
   - The substitution monad splits the renaming functor : [[Concrete-Categories-Functors-and-Monads-for-Syntax|Link]]

7. **A Structurally Recursive Unification Algorithm** : [[A-Structurally-Recursive-Unification-Algorithm|Link]]
   - Optimistic optimisation over downward-closed constraints
   - Unification as an optimisation problem in a Kleisli category : [[A-Structurally-Recursive-Unification-Algorithm|Link]]
   - Indexing terms by their variable count to make unification structural
   - Association lists as concrete accumulated substitutions : [[A-Structurally-Recursive-Unification-Algorithm|Link]]
   - Correctness of mgu and bmgu via inversion principles : [[A-Structurally-Recursive-Unification-Algorithm|Link]]
   - The occurs check as a partial inverse of thinning
   - Positions and one-hole contexts zippers : [[The-OLEG-Type-Theory-of-Holes|Link]]
   - FlexFlex and FlexRigid construction and correctness : [[A-Structurally-Recursive-Unification-Algorithm|Link]]
   - Comparison with prior unification verifications

8. **Implementation and Reflection** : [[Implementation-and-Reflection|Link]]
   - The LEGO-based OLEG prototype
   - Limitations of the implemented eliminate tactic
   - Further work recognisable dependently typed languages and derived views

---
