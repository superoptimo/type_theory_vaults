# Type Inference, Haskell and Dependent Types — Guidelines

## Header

**Title:** Type Inference, Haskell and Dependent Types
**Author(s):** Adam Michael Gundry
**Publication:** PhD thesis, University of Strathclyde, Department of Computer and Information Sciences, 2013

**Brief Summary:**
This thesis develops a unified "contextual problem-solving" framework for unification and type inference — representing metavariables and their dependencies in an ordered context so that every solving step is minimal and most general — and applies it in three settings of increasing difficulty: first-order Hindley-Milner unification, unification for units of measure over the equational theory of abelian groups, and dynamic Miller pattern unification for a full-spectrum dependent type theory with $\Sigma$-types. It then uses these foundations to design `inch`, an extension of Haskell with $\Pi$-types and type-level integers, gives it a formal core ("evidence") language in the style of System $F_C$ with an explicit phase distinction, and describes an elaboration algorithm translating `inch` source programs into evidence terms via constraint solving.

**Intent of the Author:**
Gundry sets out to show that careful, explicit management of variable scope and dependency — rather than ad hoc occurs-checks and substitution — is the right lens for explaining generalisation, unification, and elaboration uniformly across increasingly rich type systems, and to demonstrate concretely how ideas from dependent type theory (in particular Miller pattern unification and $\Pi$-types) could inform the practical evolution of Haskell's type system and compiler intermediate language.

---

## Topic List

1. **Contextual Problem-Solving** : [[Contextual-Problem-Solving|Link]]
   - Contexts as dependency-ordered lists of variable declarations and definitions : [[Contextual-Problem-Solving|Link]]
   - Statements-in-context and sanity conditions : [[Contextual-Problem-Solving|Link]]
   - Information increase and metasubstitutions as an information order : [[Contextual-Problem-Solving|Link]]
   - Minimal solutions and most general unifiers : [[Contextual-Problem-Solving|Link]]
   - The Optimist's lemma for sequential problem solving : [[Contextual-Problem-Solving|Link]]
   - The isomorphism lemma for context replacement : [[Contextual-Problem-Solving|Link]]
   - Localities and the hash marker for scope discipline : [[Contextual-Problem-Solving|Link]]
   - Stability of statements under metasubstitution
   - Contexts as a category with information increases as morphisms : [[Contextual-Problem-Solving|Link]]

2. **Hindley-Milner Type Inference Reconstructed** : [[Hindley-Milner-Type-Inference-Reconstructed|Link]]
   - Type schemes and generic instantiation : [[Hindley-Milner-Type-Inference-Reconstructed|Link]]
   - The occurs check as a dependency-detection device : [[Hindley-Milner-Type-Inference-Reconstructed|Link]]
   - Algorithm W and its relationship to unification : [[Hindley-Milner-Type-Inference-Reconstructed|Link]]
   - Let-generalisation via skimming metavariables from a locality : [[Hindley-Milner-Type-Inference-Reconstructed|Link]]
   - The Generalist's lemma : [[Hindley-Milner-Type-Inference-Reconstructed|Link]]
   - Transforming type assignment into a syntax-directed algorithm : [[Hindley-Milner-Type-Inference-Reconstructed|Link]]
   - Soundness, completeness and generality of unification and inference : [[Hindley-Milner-Type-Inference-Reconstructed|Link]]

3. **Elaboration into Explicit Calculi** : [[Elaboration-into-Explicit-Calculi|Link]]
   - Elaboration as producing an explicit term alongside a type : [[Elaboration-into-Explicit-Calculi|Link]]
   - System F as an elaboration target for Hindley-Milner terms : [[Elaboration-into-Explicit-Calculi|Link]]
   - Zipper-style representation of partial elaboration progress
   - Downwards and upwards elaboration modes : [[Elaboration-into-Explicit-Calculi|Link]]
   - Syntactic and linguistic context unification : [[Elaboration-into-Explicit-Calculi|Link]]

4. **Unification for Units of Measure** : [[Unification-for-Units-of-Measure|Link]]
   - Units of measure as an abelian group equational theory : [[Unification-for-Units-of-Measure|Link]]
   - Loss of generalisation under nontrivial equational theories : [[Unification-for-Units-of-Measure|Link]]
   - Variable occurrence versus variable dependency : [[Unification-for-Units-of-Measure|Link]]
   - The abelian group unification algorithm : [[Unification-for-Units-of-Measure|Link]]
   - Normal forms and powers of atoms : [[Unification-for-Units-of-Measure|Link]]
   - Hulls and type skeletons for flex-rigid decomposition : [[Unification-for-Units-of-Measure|Link]]
   - Generalisers and recovering polymorphism : [[Unification-for-Units-of-Measure|Link]]
   - Presburger arithmetic as a decidable numeric constraint theory : [[Unification-for-Units-of-Measure|Link]]

5. **Miller Pattern Unification** : [[Miller-Pattern-Unification|Link]]
   - Higher-order unification and its undecidability : [[Miller-Pattern-Unification|Link1]], [[Unification-for-Units-of-Measure|Link2]]
   - The pattern fragment and its unique most general unifiers : [[Miller-Pattern-Unification|Link]]
   - Rigid, flexible, and strong rigid occurrences : [[Miller-Pattern-Unification|Link]]
   - The occurs check for higher-order problems : [[Miller-Pattern-Unification|Link]]
   - Linearity of bound-variable arguments : [[Miller-Pattern-Unification|Link]]
   - Twin variables for heterogeneous equality : [[Miller-Pattern-Unification|Link]]
   - Heterogeneity invariant and typing modulo : [[Miller-Pattern-Unification|Link]]
   - Solving equations by inversion : [[Miller-Pattern-Unification|Link]]
   - Solving flex-flex equations by intersection : [[Miller-Pattern-Unification|Link]]
   - Pruning to remove out-of-scope dependencies : [[Miller-Pattern-Unification|Link]]
   - Metavariable simplification via lowering through $\Sigma$-types : [[Miller-Pattern-Unification|Link]]
   - Problem decomposition and postponement of non-pattern constraints : [[Miller-Pattern-Unification|Link]]
   - Dynamic pattern unification : [[Miller-Pattern-Unification|Link]]
   - Soundness, generality, and partial completeness of unification : [[Miller-Pattern-Unification|Link]]
   - Open problem of termination for full-spectrum unification : [[Miller-Pattern-Unification|Link]]

6. **Dependent Types in Haskell** : [[Dependent-Types-in-Haskell|Link]]
   - Promoted datatypes and datatype-kind identification : [[Dependent-Types-in-Haskell|Link]]
   - Generalised algebraic datatypes and equality constraints
   - Singleton types as a term-type bridge : [[Dependent-Types-in-Haskell|Link]]
   - $\Pi$-types as dependent function spaces available at runtime and compile time : [[Dependent-Types-in-Haskell|Link]]
   - Dependent existential types : [[Dependent-Types-in-Haskell|Link]]
   - Implicit versus explicit arguments : [[Dependent-Types-in-Haskell|Link]]
   - Type-level natural numbers and integers : [[Dependent-Types-in-Haskell|Link]]
   - Dependent pattern matching and learning by testing : [[Dependent-Types-in-Haskell|Link]]
   - Type-level constraint languages and inequality constraints : [[Dependent-Types-in-Haskell|Link]]

7. **The Evidence Language** : [[The-Evidence-Language|Link]]
   - A single syntax and typing judgment shared across terms, types, and coercions
   - Phase distinctions and the access policy : [[The-Evidence-Language|Link]]
   - Relativisation of phases for promoted applications : [[The-Evidence-Language|Link]]
   - Shared functions and saturated function application : [[The-Evidence-Language|Link]]
   - Dependent case analysis and local equality hypotheses : [[The-Evidence-Language|Link]]
   - Coercions as explicit proofs of type equality : [[The-Evidence-Language|Link]]
   - Congruence, injectivity, and coherence rules for coercions : [[The-Evidence-Language|Link]]
   - Telescoped coercions : [[The-Evidence-Language|Link]]
   - Operational semantics and the push rule for scrutinees : [[The-Evidence-Language|Link]]
   - Subject reduction : [[The-Evidence-Language|Link]]
   - Compatibility as a step-indexed alternative to joinability : [[The-Evidence-Language|Link]]
   - Consistency and progress : [[The-Evidence-Language|Link]]
   - Runtime erasure of static information : [[The-Evidence-Language|Link]]

8. **Elaborating inch into the Evidence Language** : [[Elaborating-inch-into-the-Evidence-Language|Link]]
   - Type schemes with implicit and explicit argument annotations : [[Elaborating-inch-into-the-Evidence-Language|Link]]
   - Non-deterministic elaboration as a specification : [[Elaborating-inch-into-the-Evidence-Language|Link]]
   - Subsumption for higher-rank polymorphism : [[Elaborating-inch-into-the-Evidence-Language|Link]]
   - Metavariables and metacontexts for partial knowledge : [[Elaborating-inch-into-the-Evidence-Language|Link]]
   - Bidirectional elaboration judgments for scheme assignment, inference, and checking
   - Constraint solving via backward-chaining proof search : [[Elaborating-inch-into-the-Evidence-Language|Link]]
   - Elaboration of dependent case expressions : [[Elaborating-inch-into-the-Evidence-Language|Link]]
   - The decision not to generalise local let-bindings : [[Elaborating-inch-into-the-Evidence-Language|Link]]

9. **Verified Programming with Dependent Types** : [[Verified-Programming-with-Dependent-Types|Link]]
   - Length-indexed vectors and fold-based recursion : [[Verified-Programming-with-Dependent-Types|Link]]
   - Balanced trees and merge sort via higher-rank folds : [[Verified-Programming-with-Dependent-Types|Link]]
   - Left-leaning red-black trees and zipper-based rebalancing : [[Verified-Programming-with-Dependent-Types|Link]]
   - Static tracking of computational time complexity : [[Verified-Programming-with-Dependent-Types|Link]]
   - A units-of-measure library built from type-level integers : [[Verified-Programming-with-Dependent-Types|Link]]

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 2–7)

**Summary:** Introduces the thesis's two goals — a rationalised account of type inference via contextualised problem-solving, and `inch`, a Haskell extension with $\Pi$-types and type-level data — motivating both through the limitations of GHC's current dependent-type simulations (GADTs, type families, singletons). : [[The-Evidence-Language|Link]]

**Key Definitions & Concepts:**
- Let-generalisation, existential (metavariable) versus universal variables in type schemes
- Dependent types and term inference (using term-level data to discharge equational constraints on types)
- The phase distinction between compile-time and runtime data
- $\Pi$-type as a function space where the value is available both statically and dynamically, illustrated via `replicate :: Π (n :: N) → a → Vec a n`

**Key Questions:**
1. Why does adding term-level data into types make the classic "type inference" problem harder, and in what sense does it enable "term inference"?
2. What distinguishes a genuine $\Pi$-type from a GADT/singleton encoding of dependency in Haskell, both in expressivity and in the difficulty of type inference?

---

### Chapter 2: A Rationalised Reconstruction of Hindley-Milner Type Inference (pp. 8–30)

**Summary:** Rebuilds first-order unification and Hindley-Milner type inference around a single ordered context of metavariable declarations, definitions and term-variable bindings, showing that let-generalisation and unification's most-general-unifier property both fall out of the same "minimal information increase" discipline; concludes with an elaboration algorithm into System F represented via a zipper. : [[Hindley-Milner-Type-Inference-Reconstructed|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 A framework for contextual problem solving** — context $\Theta$ (dependency-ordered list of metavariables, definitions, term bindings, and `#` locality markers), statement-in-context $J$, sanity condition $\mathrm{San}\ J$, metasubstitution / information increase $\theta : \Theta_0 \sqsubseteq \Theta_1$, stability of a statement, locality, constraint problem, minimal solution : [[Contextual-Problem-Solving|Link]]
- **2.2 Unification for the syntactic equational theory** — unify judgment $\Theta_0 \vdash \tau \equiv \upsilon : * \dashv \Theta_1$, instantiate judgment with input conditions (Definition 2.1), occurs check (Lemma 2.7), soundness/completeness of unification : [[Unification-for-Units-of-Measure|Link]]
- **2.3 Type inference with generalisation made easy** — type scheme inference problem, generic instantiation $\sigma \sqsubseteq \sigma'$, the Generalist's lemma (Lemma 2.10), transformed declarative rules separating instantiation (at variables) from generalisation (at let), algorithmic type inference judgment $\Theta_0 \vdash t : \tau \dashv \Theta_1$
- **2.4 Elaboration, zipper style** — System F as elaboration target, zipper layers for partial elaboration progress, downwards/upwards state-transformation modes : [[Elaboration-into-Explicit-Calculi|Link]]

**Key Questions:**
1. Why does representing metavariables in a single dependency-ordered context (rather than as free-floating unification variables) make let-generalisation "fall out" of the unification algorithm rather than requiring a separate dependency analysis?
2. What is the role of the Optimist's lemma in guaranteeing that solving a conjunction of problems sequentially still yields a most general solution overall?
3. How does the `#` locality marker encode the notion of rank used in efficient ML generalisation algorithms?

---

### Chapter 3: Unification and Type Inference for Units of Measure (pp. 31–47)

**Summary:** Extends the Chapter 2 framework to Kennedy-style units of measure, showing that the free abelian group equational theory breaks the "occurrence implies dependency" assumption underlying ordinary generalisation, and repairing this by decomposing flex-rigid equations into a rigid "hull" plus fresh unit constraints. : [[Unification-for-Units-of-Measure|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 Unification for the theory of abelian groups** — units of measure $\nu$ as products of atoms with integer exponents, normal form $\prod \nu_i^{k_i}$, $\mathrm{maxpow}$, quotient/remainder operators $Q_k$, $R_k$, the abelian group unification algorithm (u-define, u-reduce, u-collect) : [[Unification-for-Units-of-Measure|Link]]
- **3.2 Unification for types with units of measure** — loss of generality under a nontrivial equational theory, hull/type-skeleton decomposition of flex-rigid constraints, revised input conditions (Definition 3.1) ensuring unit metavariables are genuine dependencies : [[Unification-for-Units-of-Measure|Link]]
- **3.3 Type inference for units of measure** — generalisation remains "skim off the locality" even with the richer equational theory, illustrated via Kennedy's troublesome `div`/`mass`/`time` example : [[Verified-Programming-with-Dependent-Types|Link1]], [[Elaboration-into-Explicit-Calculi|Link2]]

**Key Questions:**
1. Why does "variable occurs in $\tau$" fail to imply "variable is a genuine dependency of $\tau$" once the equational theory is a nontrivial group, and what concrete equation demonstrates this?
2. How does decomposing a flex-rigid equation into a hull plus fresh-variable unit constraints restore most-general-unifier behaviour without abandoning the abelian group unification algorithm?

---

### Chapter 4: Miller Pattern Unification (pp. 48–87)

**Summary:** Presents a dynamic, most-general-unifier-producing higher-order unification algorithm for a full-spectrum dependent type theory with $\Pi$- and $\Sigma$-types, using heterogeneous equality and "twin variables" to manage dependent typing during incremental problem solving, and proves it sound, general and partially complete (modulo an open termination question). : [[Miller-Pattern-Unification|Link]]

**Key Definitions & Concepts by Section:**
- **4.0 Introduction / related work** — pattern fragment (metavariables applied only to distinct bound variables), intensional vs. extensional definitional equality, heterogeneous equality, typing modulo : [[The-Evidence-Language|Link]]
- **4.1 Back to basics** — neutral terms $h \cdot e$, metacontext $\Theta$ vs. context $\Gamma$, twin variables $\hat x : S \ddagger T$ for provably-but-not-yet-definitionally equal types, hereditary substitution, substitution/metasubstitution typing
- **4.2 Specification of unification** — solving by inversion (Miller's pattern condition), solving flex-flex by intersection, pruning (restricting a metavariable's telescope to remove out-of-scope dependencies), metavariable simplification (lowering through $\Sigma$-types), problem decomposition steps ($\eta$-expansion, rigid-rigid decomposition, parameter simplification) : [[Miller-Pattern-Unification|Link1]], [[Hindley-Milner-Type-Inference-Reconstructed|Link2]], [[Unification-for-Units-of-Measure|Link3]]
- **4.3 Correctness** — solved-problem judgment, consistency (Corollary 4.11), soundness (Theorem 4.14), generality (Theorem 4.16), partial completeness for the pattern fragment (Theorem 4.18), the open problem of termination
- **4.4 Discussion** — the algorithm as the base for a full-spectrum dependently typed elaborator

**Key Questions:**
1. Why does Miller's pattern condition (application only to distinct bound variables) guarantee a *unique* most general unifier, whereas an application to non-variable terms only "partially determines" a metavariable?
2. What problem do twin variables solve that ordinary variable binding cannot, and why must definitional equality treat twins as distinct even though they are provably equal?
3. Why is termination of the algorithm still an open problem for the full-spectrum theory, when it is provable for the simpler pattern fragment restricted to LF?

---

### Chapter 5: The inch Language: Adding Dependent Types to Haskell (pp. 89–105)

**Summary:** Surveys existing approaches to simulating dependent types in Haskell (GADTs, type families, singletons, Dependent ML, GHC's TypeNats) and lays out `inch`'s design choices — genuine $\Pi$-types, unified types and kinds, integers rather than naturals as the primitive index kind, and fine-grained implicit/explicit argument annotation — by contrasting them example by example with the alternatives. : [[Dependent-Types-in-Haskell|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Related work** — GADTs and the GADT-to-equality-constraint translation, associated type families, singleton encodings, Dependent ML's constraint-domain parameterisation, GHC's TypeNats
- **5.2 Features of inch** — identification of types and kinds (following Weirich et al.'s $* : *$), $\Pi$-types vs. singleton encodings for dependent functions, dependent existential types via data constructors, implicit vs. explicit argument annotation (Milner's coincidence and its breakdown), integers as the type-level number kind, dependent case analysis / "learning by testing", equality and inequality constraints

**Key Questions:**
1. Why does identifying Haskell's type and kind levels (rather than keeping "promotable" and "non-promotable" datatypes distinct) make genuinely dependent programming easier?
2. In what precise sense do singleton types simulate a $\Pi$-type, and what expressive or ergonomic cost does that simulation incur compared to a native $\Pi$-type?

---

### Chapter 6: A Language of Evidence (pp. 106–143)

**Summary:** Defines the evidence language, a System-$F_C$-like intermediate language extended with $\Pi$-types and a phase distinction, giving it a single syntax and typing judgment shared by types, terms and coercions, an operational semantics with subject reduction, and a novel step-indexed compatibility relation used to prove consistency and progress without restricting which assumptions coercions may use. : [[Elaborating-inch-into-the-Evidence-Language|Link1]], [[The-Evidence-Language|Link2]]

**Key Definitions & Concepts by Section:**
- **6.1–6.2 Syntax, phase distinctions and promotion** — phases $\forall, \Pi, \square, \bullet$ and the access policy $\Phi \hookrightarrow \Psi$, the relativisation operator $\Phi \mathbin{/\!/} \Psi$, promoted data constructors, shared (saturated) functions $f(\delta)$, dependent case analysis (`dcase`) introducing a local equality hypothesis
- **6.3 Type system** — unified typing judgment $\Gamma \vdash \rho :_\Psi \kappa$, coercions as explicit type-equality evidence, congruence/injectivity/coherence coercion forms, telescoped coercions
- **6.4 Operational semantics** — small-step reduction shared by all phases, the `step` coercion embedding computation in propositional equality, the push rule for coerced scrutinees, subject reduction (Theorem 6.11) : [[The-Evidence-Language|Link]]
- **6.5 Consistency and progress** — computational/coerced/structural type expressions, step-indexed compatibility relation $A_k(\varphi)$, good declarations and signatures, consistency (Theorem 6.20) and progress (Theorem 6.21) : [[The-Evidence-Language|Link]]
- **6.6 Erasure** — erasure of static subterms to produce runtime terms, correspondence between evidence-language and erased-runtime-term reduction
- **6.7 Discussion** — representing numbers via axioms, $\eta$-laws, comparison with System $F_C$, $F_C^\uparrow$, and Weirich et al.'s kind-erased core language

**Key Questions:**
1. Why does unifying types, terms, and coercions into one syntax and one phase-indexed typing judgment simplify the presentation of $\Pi$-types compared to adding a separate promotion mechanism (as in System $F_C^\uparrow$)?
2. How does the step-indexed compatibility relation avoid the over-restriction of earlier approaches that forbid coercions from depending on potentially-inconsistent assumptions, while still proving consistency?
3. Why must shared functions be saturated, and what would break (in type-level application injectivity, or in elaboration) if type-level $\lambda$-abstraction were permitted?

---

### Chapter 7: Producing the Evidence: Elaborating inch (pp. 144–172)

**Summary:** Defines elaboration of `inch` source programs into evidence-language terms via a non-deterministic specification followed by a bidirectional, metavariable-based algorithm that reduces implicit-argument synthesis and subsumption to constraint solving, extending the contextual problem-solving method of Part I to a setting with local hypotheses and dependent case analysis. : [[Elaborating-inch-into-the-Evidence-Language|Link]]

**Key Definitions & Concepts by Section:**
- **7.1 Type schemes** — schemes annotated with implicit (`:i`) vs. explicit (`:e`) argument phase, erasure of schemes to evidence-language types : [[Elaborating-inch-into-the-Evidence-Language|Link1]], [[Hindley-Milner-Type-Inference-Reconstructed|Link2]]
- **7.2–7.3 Formal syntax and non-deterministic elaboration** — elaboration judgment $\Gamma \vdash \rho \rightsquigarrow \rho :_\Psi \sigma$, structural vs. "wrapping" (implicit-abstraction, unknown-marker, conversion) rules, subsumption judgment $\Gamma \vdash e : \sigma \prec e' : \sigma'$ for higher-rank polymorphism
- **7.4 Metavariables and information increase** — metacontext extended with parameterised metavariables $\alpha[\Delta]$, metasubstitution validity, the $\Delta \mathbin{\%} \Xi$ parameterisation (raising) operator : [[Contextual-Problem-Solving|Link]]
- **7.5 Deterministic elaboration** — bidirectional judgments for scheme assignment, type inference, and type checking; the abstract unification/constraint-solving judgment $\Theta_0 \vdash \tau \sim \upsilon \rightsquigarrow \gamma \dashv \Theta_1$ as backward-chaining proof search; soundness of elaboration relative to the non-deterministic specification
- **7.6 Elaboration for case analysis** — extending both systems with (dependent) case-branch elaboration and pattern-to-telescope matching : [[The-Evidence-Language|Link1]], [[Elaborating-inch-into-the-Evidence-Language|Link2]]
- **7.7 Discussion** — the decision (following Vytiniotis et al.) not to generalise local let-bindings, because parameterised metavariables make principal generalisation unpredictable; coherence of elaboration as an open property

**Key Questions:**
1. Why does the "magic" rule for implicit $\lambda$-abstraction make the elaboration relation non-deterministic, and what mechanism (metavariables plus bidirectional judgments) removes that non-determinism to produce an algorithm?
2. Why does `inch` refuse to generalise local let-bindings, unlike Chapters 2–3's Hindley-Milner treatment, and what specific problem (parameterised metavariables under local constraints) forces this choice?
3. In what sense does subsumption "invent" coercions, and why is this only possible at the runtime phase and not at a static (type-level) phase?

---

### Chapter 8: Applications (pp. 173–194)

**Summary:** Demonstrates `inch` (via a prototype preprocessor) on increasingly ambitious examples — length-indexed vectors and merge sort, invariant-preserving left-leaning red-black tree insertion/deletion via a zipper, static tracking of computational time complexity, and a units-of-measure library built purely from type-level integers — showing that genuine $\Pi$-types and integer type-level arithmetic make previously awkward dependently-typed Haskell idioms natural. : [[The-Evidence-Language|Link]]

**Key Definitions & Concepts by Section:**
- **8.1–8.2 Vectors and merge sort** — higher-rank folds over length-indexed vectors and balanced trees, ordered vectors indexed by bounds, merge as guarded pattern matching with local constraints
- **8.3 Left-leaning red-black trees** — invariant-carrying `RBTree` GADT, one-hole zipper `TreeZip` avoiding representation of invariant-violating trees, search/insertion/deletion via zipper traversal and rebalancing : [[Verified-Programming-with-Dependent-Types|Link]]
- **8.4 Tracking time complexity** — a `Cost n a` indexed monad (after Danielsson) whose index statically bounds computation steps, `tick`/`wait`/`returnW` combinators : [[Verified-Programming-with-Dependent-Types|Link]]
- **8.5 Units of measure** — a `Quantity` newtype over a fixed-basis `Unit` index, arithmetic combinators computing units via type-level integer addition/negation, reproducing Kennedy's "hard" generalisation example without difficulty : [[Unification-for-Units-of-Measure|Link1]], [[Verified-Programming-with-Dependent-Types|Link2]]

**Key Questions:**
1. Why does representing the "path back to the root" as a zipper (rather than rebalancing an already-constructed tree) avoid the need to represent trees that temporarily violate the red-black invariants?
2. What specific difficulty in inferring principal types for units-of-measure functions (as raised in Chapter 3) does `inch`'s integer-indexed `Quantity` library sidestep, and at what cost (fixed unit basis) does it do so?

---

### Chapter 9: Conclusion (pp. 195–196)

**Summary:** Reflects on `inch` as an exploratory re-imagining of GHC Haskell rather than a finished system, emphasizing three forward-looking themes: unifying types and kinds as a prerequisite for useful $\Pi$-types, giving programmers finer control over implicit/explicit arguments than Milner's original term/type coincidence allows, and the continuing need for a well-understood theory of constraint solving over nontrivial equational theories (abelian groups, $\beta\eta$-conversion) to support elaboration of full-spectrum dependently typed languages.

**Key Questions:**
1. What does Gundry mean by "Milner's compromise is no longer tenable," and what concrete language feature (explicit type application) does he argue should replace the strict implicit-type/explicit-term rule?

*Note: Appendices A–D (pp. 197–261) contain reference Haskell implementations of the Chapter 2–4 algorithms and selected proof details omitted from the main chapters; they are supporting material rather than independently taught content.*
