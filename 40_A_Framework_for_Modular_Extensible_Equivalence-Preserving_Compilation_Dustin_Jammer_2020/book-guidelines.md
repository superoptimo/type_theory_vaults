# A Framework for Modular, Extensible, Equivalence-Preserving Compilation — Guidelines

## Header

**Title:** A Framework for Modular, Extensible, Equivalence-Preserving Compilation
**Author(s):** Dustin Jamner (Thesis Supervisor: Adam Chlipala)
**Publication:** M.S. Thesis, Massachusetts Institute of Technology, Department of Electrical Engineering and Computer Science, May 2022

**Brief Summary:**
This thesis presents Pyrosome, a generic Coq framework for verifying compilers that are fully extensible and composable. Rather than fixing a compiler's correctness proof to one monolithic language definition, Pyrosome specifies languages as sorted equational theories (generalized algebraic theories) and defines an inductive predicate, $\mathrm{Preserving}$, over compilers that lets correctness proofs be built one syntactic form or equation at a time. Because equivalence preservation is proved compositionally, adding a new language feature only requires proving obligations for that feature, while all prior proofs remain valid — and because compilers work over open terms, linking with arbitrary target code is supported. The approach is validated with a multipass STLC $\to$ CPS $\to$ closure-conversion compiler that is later extended with naturals, unit, recursive functions, and global state, reusing the original correctness theorems throughout.

**Intent of the Author:**
The author aims to make verified compiler construction incremental and reusable rather than bespoke, so that as real programming languages evolve, compiler correctness proofs can evolve with them instead of requiring wholesale reverification.

---

## Topic List

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

## Chapter Summaries

### Chapter 1: Introduction (pp. 9–14)

**Summary:** Motivates Pyrosome by surveying the limitations of existing verified-compiler work — rigidity to fixed source languages, weak linking guarantees, and poor support for evolving specifications — then previews Pyrosome's equational-theory approach with an informal STLC-to-CPS example and its extension to a global store.

**Key Definitions & Concepts:**
- Separate compilation (linking limited to programs compiled from the same source language, sometimes only by the same compiler)
- Contextual equivalence (relates terms indistinguishable by any surrounding context; noted as difficult to reason about and poorly behaved under extension)
- CPS translation $\lfloor - \rfloor$ (compiles STLC into continuation-passing style, binding the continuation to $k$)
- Beta and eta equivalence for STLC ($(\lambda(x:A).e)\,v = e[v/x]$; $\lambda(x:A).\,f\,x = f$)
- Language/compiler extension (adding new rules to source, target, and compiler while reusing prior correctness results)

**Key Questions:**
1. Why does contextual equivalence make compiler correctness proofs difficult to extend, and how does an equational-theory semantics avoid this problem?
2. In the worked beta-reduction proof, what makes the argument reusable when a global-store extension is later added to both source and target languages?

---

### Chapter 2: Concepts of Pyrosome (pp. 15–20)

**Summary:** Introduces Pyrosome's core mechanics informally: how the $\mathrm{Preserving}$ predicate reduces compiler verification to one goal per syntactic form and equation, how language extension composes proof obligations, and why equational-theory semantics (rather than contextual equivalence) support sound, extensible linking.

**Key Definitions & Concepts:**
- $\mathrm{Preserving}(L_t, cmp, L_s)$ — predicate implying $cmp$ is a type- and equivalence-preserving compiler from $L_s$ to $L_t$
- Language extension notation $L_1 + L_2$ (e.g., STLC + Recursion)
- Evaluation contexts $E$ and the plug operation $E[e]$, used to state heap-access equations
- Monotonicity of judgments under language extension
- callTwice example — a term contextually equivalent to $\lambda(f:\mathrm{nat}\to\mathrm{nat}).\,f$ in pure STLC but not equal under the call-by-value equational theory, illustrating why equational theories (not contextual equivalence) are the right basis for compiler correctness
- Call-by-value restriction on beta reduction and its necessity for CPS correctness

**Key Questions:**
1. Why can the $\mathrm{Preserving}$ obligations for STLC and for a Recursion extension be proved independently, and what does that buy the framework?
2. Using the callTwice example, explain why a compiler that is equivalence-preserving with respect to the source's equational theory need not also preserve contextual equivalence — and why this is treated as a feature rather than a limitation.

---

### Chapter 3: Formalism and Metatheory (pp. 21–32)

**Summary:** Formalizes Pyrosome's language specifications as generalized algebraic theories over terms and sorts, defines compilers as finite maps compatible with substitution, and states the three central modularity theorems (compiler extension, Preserving implies semantic preservation, and compiler codomain embedding), closing with a defense of equivalence preservation as the right correctness criterion.

**Key Definitions & Concepts by Section:**
- **3.1 Language Specifications** — generalized algebraic theory (GAT), term syntax `#c term...` vs. metavariables, sort (a syntactic class plus its well-formedness judgment), term rule (declares a new syntactic form with explicit vs. inferred subterms), language specification as an ordered list of sort/term/equation rules, language extension by list concatenation : [[Language-Specifications-as-Equational-Theories|Link]]
- **3.2 Compilers and Correctness** — compiler as a finite map from source sort/term names to target sorts/terms, substitution invariance $\lfloor \gamma(e) \rfloor = \lfloor\gamma\rfloor(\lfloor e\rfloor)$, compilation via bottom-up traversal with metavariable substitution, compiler extension by appending mappings : [[Compiler-Correctness-in-the-Broader-Literature|Link]]
- **3.3 Framework Proof Structure** — $\mathrm{Preserving}(L_t, cmp, L_s)$ (inductive, one case per rule kind: sort rules map to well-formed target sorts, term rules to well-formed target terms, equations to target-equivalent terms), Theorem 1 (Compiler extension — disjoint extensions of a shared prefix language compose), Theorem 2 (Preserving implies semantic preservation — implies full type and equivalence preservation via mutual induction), Theorem 3 (Compiler codomain embedding — a compiler's target language can be enlarged without invalidating Preserving), weakening and monotonicity as the key lemmas bridging pointwise obligations to whole-language guarantees
- **3.4 Why Equivalence Preservation** — whole-program simulation and trace refinement (CompCert), the linking problem for open/multi-source programs, equivalence preservation vs. contextual equivalence as correctness criteria, blind spots of equivalence-preserving compilers (e.g., trivial constant-returning compilers, true/false-swapping compilers), fixing an expected source-to-target mapping of observable values to close this gap : [[Equivalence-Preservation-versus-Contextual-Equivalence|Link]]

**Key Questions:**
1. Why must a language's terms, sorts, and contexts reference only earlier rules in the specification list, and how does this ordering constraint make Theorem 1 (compiler extension) provable?
2. What specific property of compilers in Pyrosome guarantees that congruence holds "for free" in the equivalence-preservation proof, without a separate proof case?
3. Why does the author consider equivalence preservation (rather than contextual-equivalence preservation or full abstraction) the right notion of compiler correctness, and what blind spot must be separately patched to avoid degenerate compilers?

---

### Chapter 4: Case Study (pp. 33–44)

**Summary:** Presents and verifies a three-pass compiler (STLC → CPS → closure conversion) in Pyrosome, then extends it with recursive functions, global state (via heaps and evaluation contexts), and an explicit substitution calculus, reporting on the proof automation that discharges most resulting obligations. : [[Extending-the-Case-Study|Link1]], [[The-STLC-to-CPS-to-Closures-Case-Study|Link2]]

**Key Definitions & Concepts by Section:**
- **4.1 Recursive Functions** — $\mathrm{fix}\ f(x:A) := e$ as a recursive function value, recursive continuations in the target CPS calculus, Theorem 5 (CPS translation for recursion satisfies Preserving), separated fixpoint combinator in closure conversion to isolate recursion from environment-tuple handling : [[Extending-the-Case-Study|Link]]
- **4.2 Global State and Evaluation Contexts** — heaps as finite maps from $\mathbb{N}$ to $\mathbb{N}$, configurations $\langle H, e\rangle$ pairing computations with heaps, evaluation contexts with judgment $\Gamma \vdash E : A \rightsquigarrow B$ and plug operation, compiling away evaluation contexts into CPS `bind` sequencing with a free variable $x_h$ : [[Extending-the-Case-Study|Link]]
- **4.3 Substitution** — explicit substitution calculus (derived from Sterling's dependently-typed version, here simply typed), variables as repeated weakening substitutions $\uparrow$ applied to index $0$, substitution equations generated systematically per syntactic form rather than hand-written per language
- **4.4 Summary of Case-Study Implementation** — Theorem 6 (equivalence preservation of the combined case-study compiler across STLC + Naturals + Recursion + Unit + State), lines-of-code breakdown by definitions/theorem statements/proofs
- **4.5 Inference and Automation** — elaboration judgments paired with well-formedness judgments, preelaboration syntax, `Derive ... SuchThat` Coq idiom for correct-by-construction elaboration, generic reduction-based tactics for equivalence-preservation goals, current limitation to simply typed (non-dependent, non-polymorphic) languages

**Key Questions:**
1. Why does closure conversion for recursive functions require a separate fixpoint combinator rather than folding recursion directly into the fused closure construct used for ordinary lambdas?
2. How does introducing evaluation contexts let the heap-access equations avoid depending on arbitrary surrounding program structure, and why do they disappear again after CPS translation?
3. What does it mean that substitution equations are "generated" rather than hand-written per language, and why does this matter for extensibility?

---

### Chapter 5: Related and Future Work (pp. 45–48)

**Summary:** Situates Pyrosome against alternative generic metatheory frameworks (GATs vs. Felleisen-style operational semantics, à la carte approaches, the K Framework) and multilanguage-semantics compiler-verification work, then outlines open problems in optimization, trusted-base reduction via models of target semantics, and support for richer type systems. : [[Related-Frameworks-and-Future-Directions|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Alternative Generic Frameworks** — GATs' presentation via equational theories vs. contextual-equivalence-based frameworks, meta-theory à la carte / modular monadic metatheory, type- and scope-safe syntax with binding, the K Framework's binder-expressive matching logic : [[Compiler-Correctness-in-the-Broader-Literature|Link]]
- **5.2 Multilanguage Semantics** — ad-hoc multilanguage constructions in prior compiler-verification work and their reliance on contextual equivalence, limiting further extension : [[Compiler-Correctness-in-the-Broader-Literature|Link]]
- **5.3 Optimization** — the syntactic invariant $\lfloor\gamma(e)\rfloor = \lfloor\gamma\rfloor(\lfloor e\rfloor)$ as an obstacle to optimizing compilation, proposed intralanguage optimization functions $o : \mathrm{term} \to \mathrm{term}$ preserving semantics
- **5.4 Modeling Pyrosome's Equational Theories** — trusted base currently including source/target language specifications, goal of modeling target theories atop verified systems like CompCert and Bedrock : [[Language-Specifications-as-Equational-Theories|Link]]
- **5.5 Advanced Type Systems** — prospects for polymorphism, linearity, and dependent types via extended substitution languages, current restriction to simple types for proof automation

**Key Questions:**
1. Why does the syntactic substitution-invariance requirement on compilers rule out standard translation-time optimizations, and why might intralanguage optimization passes escape this restriction?
2. What would be gained by modeling Pyrosome's target-language equational theories on top of an independently verified system like CompCert, rather than trusting the Pyrosome specification directly?

---
