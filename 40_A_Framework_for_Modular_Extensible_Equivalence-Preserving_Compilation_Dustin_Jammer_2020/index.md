# A Framework for Modular, Extensible, Equivalence-Preserving Compilation — Index

[[book-guidelines|↩ Back to guidelines]]

1. **The Problem of Extensible Compiler Verification** : [[The-Problem-of-Extensible-Compiler-Verification|Link]]
   - Compiler verification as costly but critical for trustworthy software
   - Existing verified compilers tied to fixed source-language structure : [[The-Problem-of-Extensible-Compiler-Verification|Link]]
   - Separate compilation as a weak form of linking : [[The-Problem-of-Extensible-Compiler-Verification|Link]]
   - The expression problem in language and compiler design : [[Language-Specifications-as-Equational-Theories|Link1]], [[The-Problem-of-Extensible-Compiler-Verification|Link2]]
   - Multilanguage approaches that bake all languages into one correctness theorem
   - Living languages with evolving specifications resisting monolithic verification

2. **Pyrosome's Design Philosophy** : [[Pyrosomes-Design-Philosophy|Link]]
   - Compilers as small independent components analogous to pyrosome colonial organisms
   - Language specification via generalized algebraic theories : [[Language-Specifications-as-Equational-Theories|Link1]], [[Pyrosomes-Design-Philosophy|Link2]]
   - Deeply embedded formal notion of a programming language
   - Distinction between object-language variables and framework metavariables : [[Pyrosomes-Design-Philosophy|Link]]
   - Terms as n-ary syntax trees tagged with sorts : [[Pyrosomes-Design-Philosophy|Link]]
   - De Bruijn indices for object-language variables
   - Explicit named-form presentation for readability versus internal de Bruijn encoding

3. **Language Specifications as Equational Theories** : [[Language-Specifications-as-Equational-Theories|Link]]
   - Languages as lists of inference rules : [[Pyrosomes-Design-Philosophy|Link]]
   - Sort rules, term rules, and equation rules
   - Reflexive transitive symmetric congruence closure of equational axioms : [[Language-Specifications-as-Equational-Theories|Link]]
   - Implicit versus explicit subterms in term rules : [[Language-Specifications-as-Equational-Theories|Link1]], [[Pyrosomes-Design-Philosophy|Link2]]
   - Language extension by list concatenation : [[Language-Specifications-as-Equational-Theories|Link]]
   - Notation $L_1 + L_2$ for language extension

4. **Compilers as Finite Maps** : [[Compilers-as-Finite-Maps|Link]]
   - Compilers as finite maps from source constructors to target terms : [[Compilers-as-Finite-Maps|Link]]
   - Compilation by bottom-up traversal and metavariable substitution : [[Compilers-as-Finite-Maps|Link]]
   - Invariance of compilation under metavariable substitution : [[Compilers-as-Finite-Maps|Link]]
   - Compiler extension by appending new mappings : [[The-Preserving-Predicate-and-Modularity-Theorems|Link]]
   - Support for open terms and arbitrary linking

5. **The Preserving Predicate and Modularity Theorems** : [[The-Preserving-Predicate-and-Modularity-Theorems|Link]]
   - Inductive predicate $\mathrm{Preserving}(L_t, cmp, L_s)$
   - One proof obligation per sort rule, term rule, and equation
   - Well-formedness obligations for sorts and terms
   - Equivalence obligations for equations
   - Pointwise definition over rules enabling invariance under extension
   - Weakening and monotonicity principles
   - Compiler extension theorem for disjoint feature composition : [[The-Preserving-Predicate-and-Modularity-Theorems|Link]]
   - Preserving implies semantic preservation theorem : [[The-Preserving-Predicate-and-Modularity-Theorems|Link]]
   - Compiler codomain embedding theorem : [[The-Preserving-Predicate-and-Modularity-Theorems|Link]]
   - Vertical composition of compiler passes : [[The-Preserving-Predicate-and-Modularity-Theorems|Link]]

6. **Equivalence Preservation versus Contextual Equivalence** : [[Equivalence-Preservation-versus-Contextual-Equivalence|Link]]
   - Contextual equivalence and its difficulty under language extension
   - Equational theories as an alternative notion of language semantics : [[Equivalence-Preservation-versus-Contextual-Equivalence|Link]]
   - The callTwice example distinguishing contextual equivalence from equational semantics : [[Equivalence-Preservation-versus-Contextual-Equivalence|Link1]], [[Compiler-Correctness-in-the-Broader-Literature|Link2]]
   - Call-by-value beta restriction and its role in compiler correctness
   - Trivial and value-permuting compilers as blind spots of equivalence preservation : [[The-Preserving-Predicate-and-Modularity-Theorems|Link]]
   - Fixing an expected mapping of observable values across source and target

7. **Compiler Correctness in the Broader Literature** : [[Compiler-Correctness-in-the-Broader-Literature|Link]]
   - Whole-program simulation and trace refinement in CompCert : [[Compiler-Correctness-in-the-Broader-Literature|Link]]
   - Vertical compositionality of closed-program simulation : [[Compiler-Correctness-in-the-Broader-Literature|Link]]
   - The linking problem for modern multi-source software
   - Fully abstract compilation
   - Multilanguage semantics for compiler verification : [[The-Problem-of-Extensible-Compiler-Verification|Link]]
   - Ad-hoc versus formal frameworks for combining languages

8. **The STLC-to-CPS-to-Closures Case Study** : [[The-STLC-to-CPS-to-Closures-Case-Study|Link]]
   - Simply typed lambda calculus with explicit value/expression distinction
   - Continuation-passing style translation and the continuation calculus
   - Negation type $\neg A$ as the type of continuations : [[The-STLC-to-CPS-to-Closures-Case-Study|Link]]
   - Closure conversion via environment tuples : [[The-STLC-to-CPS-to-Closures-Case-Study|Link]]
   - Fused closure construct combining existential, pair, and function
   - Beta and eta laws for closures
   - Multipass compiler composition and reuse of correctness proofs

9. **Extending the Case Study** : [[Extending-the-Case-Study|Link]]
   - Recursive functions as fixpoint values
   - Recursive continuations in the CPS calculus
   - Fixpoint combinator separated from closure conversion
   - Global heap as a sort with finite-map axioms
   - Evaluation contexts and the plug operation : [[Extending-the-Case-Study|Link]]
   - Cross-extension interaction between evaluation contexts and stateful reduction
   - Compiling away evaluation contexts via CPS binding sequencing
   - Explicit substitution calculus and generated substitution equations : [[Extending-the-Case-Study|Link]]
   - Reuse of substitution behavior across CPS and closure-conversion calculi : [[The-STLC-to-CPS-to-Closures-Case-Study|Link]]

10. **Proof Automation and Elaboration** : [[Proof-Automation-and-Elaboration|Link]]
    - Elaboration judgments paired with well-formedness judgments
    - Preelaboration syntax and correct-by-construction derivation : [[Proof-Automation-and-Elaboration|Link]]
    - Generic tactics independent of specific language features : [[Proof-Automation-and-Elaboration|Link]]
    - Normalization-based automation of equivalence-preservation goals
    - Limitations of automation for type equations and dependent typechecking : [[Proof-Automation-and-Elaboration|Link]]
    - Lines-of-code accounting by definitions, theorem statements, and proofs

11. **Related Frameworks and Future Directions** : [[Related-Frameworks-and-Future-Directions|Link]]
    - Generalized algebraic theories versus Felleisen's expressive-power framework
    - Modular metatheory à la carte and data types à la carte : [[Related-Frameworks-and-Future-Directions|Link]]
    - Type- and scope-safe universes of syntax with binding : [[Related-Frameworks-and-Future-Directions|Link]]
    - The K semantic framework : [[Related-Frameworks-and-Future-Directions|Link]]
    - Prospects for intralanguage optimization passes
    - Modeling Pyrosome's equational theories atop verified low-level systems
    - Prospects for polymorphism, linearity, and dependent types in Pyrosome : [[Related-Frameworks-and-Future-Directions|Link]]

---
