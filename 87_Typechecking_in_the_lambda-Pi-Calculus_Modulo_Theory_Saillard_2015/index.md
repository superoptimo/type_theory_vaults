# Typechecking in the λΠ-Calculus Modulo: Theory and Practice (Vérification de typage pour le λΠ-Calcul Modulo : théorie et pratique) — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Abstract Rewriting and Confluence Theory** : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
   - Abstract reduction systems and their basic properties : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
   - Local confluence versus confluence : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
   - Newman's Lemma : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
   - Term rewriting systems over first-order signatures : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
   - Critical pairs and the Critical Pair Theorem : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
   - Orthogonality and left-linearity as confluence criteria : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
   - Parallel reduction and the Parallel Closure Theorem
   - Modularity of confluence for disjoint signatures
   - The untyped λ-calculus and β-reduction : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
   - Combining term rewriting with the λ-calculus via currification
   - Loss of confluence from non-left-linear rules combined with β-reduction
   - Turing's fixed-point combinator as a source of non-confluence counterexamples

2. **The λΠ-Calculus Modulo** : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link1]], [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link2]]
   - Objects, types, kinds and the syntactic stratification of terms
   - Local contexts versus global contexts : [[The-lambda-Pi-Calculus-Modulo|Link]]
   - Rewrite rules as first-class citizens of the global context
   - Untyped rewriting as a departure from the original Cousineau–Dowek presentation : [[The-lambda-Pi-Calculus-Modulo|Link]]
   - Beta reduction and Gamma reduction
   - The generalized conversion rule and definitional equality modulo a rewrite system
   - Stratification of the conversion relation
   - Well-typed terms and the typing judgment : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Well-formed local contexts : [[The-lambda-Pi-Calculus-Modulo|Link]]

3. **Subject Reduction, Product Compatibility and Uniqueness of Types** : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link]]
   - Subject reduction as type preservation under reduction : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link1]], [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link2]]
   - Product compatibility as the key property enabling subject reduction for beta : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link]]
   - Product compatibility from confluence : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link1]], [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link2]]
   - Well-typed rewrite rules and permanently well-typed rewrite rules : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Strongly well-formed rewrite rules and strongly well-formed global contexts : [[The-lambda-Pi-Calculus-Modulo|Link]]
   - Uniqueness of types and its equivalence with right product compatibility : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link]]
   - Reduction to a convertibility check once uniqueness of types holds : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link]]
   - Undecidability of product compatibility and of subject reduction : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link]]
   - Undecidability of uniqueness of types : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link]]
   - Reduction from an undecidable word problem to establish these undecidability results

4. **The λΠ-Calculus Modulo as a Logical Framework** : [[The-lambda-Pi-Calculus-Modulo-as-a-Logical-Framework|Link]]
   - Shallow versus deep encodings of a source logic into a target calculus
   - Encoding of constructive predicate logic via the judgment-as-type correspondence : [[The-lambda-Pi-Calculus-Modulo-as-a-Logical-Framework|Link]]
   - Encoding of the Calculus of Constructions with universes and product representatives : [[The-lambda-Pi-Calculus-Modulo-as-a-Logical-Framework|Link]]
   - Encoding of Heyting Arithmetic with an induction principle : [[The-lambda-Pi-Calculus-Modulo-as-a-Logical-Framework|Link]]
   - Soundness and conservativity theorems for an embedding
   - The Calculus of Constructions Modulo as a polymorphic extension with type operators : [[The-lambda-Pi-Calculus-Modulo-as-a-Logical-Framework|Link]]
   - Toward Pure Type Systems Modulo as a further generalization

5. **Well-Typedness of Rewrite Rules** : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Algebraic left-hand sides as the simplest sufficient condition : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Bidirectional typing as type synthesis and type checking
   - Weakening the algebraicity restriction using bidirectional inference on left-hand sides : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Weakening the well-typedness restriction on left-hand sides : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Typing constraints collected while inferring the type of a left-hand side
   - Most general solutions and pre-solutions of a set of constraints modulo conversion : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Fine-grained typing of rewrite rules using pre-solutions
   - Static symbols versus definable symbols
   - Safe global contexts : [[The-lambda-Pi-Calculus-Modulo|Link]]
   - Permanent pre-solutions and weakly well-formed rewrite rules : [[Type-Inference-and-Type-Checking-Algorithms|Link]]
   - Weakly well-formed global contexts : [[The-lambda-Pi-Calculus-Modulo|Link1]], [[Type-Inference-and-Type-Checking-Algorithms|Link2]]
   - Linearization of non-left-linear rewrite rules justified by typing constraints : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link]]
   - Optimizing dependent pattern matching by dropping redundant constructors
   - An exact characterization of well-typedness as inclusion between solution sets of unification problems
   - Undecidability of well-typedness for rewrite rules via undecidability of higher-order unification : [[Well-Typedness-of-Rewrite-Rules|Link]]

6. **Rewriting Modulo β and Higher-Order Rewrite Systems** : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
   - Loss of confluence from rewrite rules with abstractions on their left-hand side
   - Failure modes of a naive definition of rewriting modulo beta : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
   - Higher-Order Rewrite Systems as a meta-language separating beta-reduction from rewriting : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
   - Preterms, patterns and Miller's decidability of higher-order pattern unification : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
   - Encoding the λΠ-Calculus Modulo into Higher-Order Rewrite Systems : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
   - Uniform terms and λΠ-patterns : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
   - Definition of rewriting modulo beta via the encoding : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
   - Subject reduction and preservation of the congruence for rewriting modulo beta
   - Product compatibility from confluence of rewriting modulo beta : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link]]
   - Beta-well-formed global contexts : [[The-lambda-Pi-Calculus-Modulo|Link]]
   - Higher-order critical pairs and overlapping patterns
   - The Development Closure Theorem as a confluence criterion for left-linear systems
   - Applications to equation solving, negation normal form and universe reflection
   - Compiling pattern matching modulo beta to decision trees : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
   - Soundness and completeness of the compilation to decision trees

7. **Non-Left-Linear Rewriting and Weak Typing** : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link]]
   - Product compatibility for object-level rewrite systems independently of confluence
   - The postponement lemma and the commutation lemma : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link]]
   - Pi-producing rewrite rules as the obstruction to extending the object-level result
   - Weak types and the stripping function from dependent types to simple types : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link]]
   - Non-confusing rewrite rules : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Weak typing as a simply-typed approximation of the full type system
   - The Colored λΠ-Calculus Modulo with a weakly well-typed conversion rule : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link]]
   - Black and white terms, positions and rewrite rules : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Internal reduction and external reduction as a refinement of postponement and commutation : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link]]
   - A general criterion for product compatibility mixing non-left-linear and Pi-producing rules : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link]]
   - Limits of the criterion when reasoning departs from weakly well-typed conversions

8. **Type Inference and Type-Checking Algorithms** : [[Type-Inference-and-Type-Checking-Algorithms|Link]]
   - A bidirectional inference algorithm for terms : [[Type-Inference-and-Type-Checking-Algorithms|Link]]
   - Soundness, termination and completeness of type inference : [[Type-Inference-and-Type-Checking-Algorithms|Link]]
   - A safe inference variant avoiding reliance on subject reduction : [[Type-Inference-and-Type-Checking-Algorithms|Link]]
   - Type checking reduced to inference plus a convertibility test : [[Type-Inference-and-Type-Checking-Algorithms|Link]]
   - Well-formedness checking for local contexts : [[Type-Inference-and-Type-Checking-Algorithms|Link]]
   - Solving unification constraints via a Herbrand-style presolution algorithm
   - Checking weak well-formedness of rewrite rules algorithmically : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Checking well-typedness of global contexts via a confluence oracle : [[The-lambda-Pi-Calculus-Modulo|Link1]], [[Type-Inference-and-Type-Checking-Algorithms|Link2]]
   - Termination guarantees contingent on strong normalization of the rewrite relation
   - Implementation of these algorithms in the DEDUKTI proof checker

---
