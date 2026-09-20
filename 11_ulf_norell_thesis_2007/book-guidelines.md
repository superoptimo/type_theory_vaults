# Towards a Practical Programming Language Based on Dependent Type Theory — Guidelines

## Header

**Title:** Towards a Practical Programming Language Based on Dependent Type Theory
**Author(s):** Ulf Norell
**Publication:** Doctoral thesis, Department of Computer Science and Engineering, Chalmers University of Technology and Göteborg University, Göteborg, Sweden, 2007. ISBN 978-91-7291-996-9.

**Brief Summary:**
This thesis bridges the gap between theoretical presentations of dependent type theory and the requirements of a practical programming language. It gives a type-checking algorithm for definitions by pattern matching over inductive families (supporting overlapping patterns and the `with` construct), a sound and terminating algorithm for type checking in the presence of metavariables (enabling implicit arguments), and a simple but powerful module system decoupled from the type checker. As a side track, it connects dependent type theory to a first-order resolution theorem prover to automate simple proof obligations. All of this is put into practice in the implementation of Agda, a dependently typed programming language, illustrated by an internal certified solver for commutative monoid equations.

**Intent of the Author:**
Norell aims to take concrete, practical steps toward an industrial-scale programming language founded on dependent type theory — showing that pattern matching, implicit syntax, modularity, and proof automation can each be given rigorous, implementable algorithms, and that the resulting ideas compose into a real, usable language (Agda).

---

## Topic List

1. **Dependent Type Theory Foundations** : [[Dependent-Type-Theory-Foundations|Link]]
   - The theory $UTT_\Sigma$: dependent function and pair types : [[Dependent-Type-Theory-Foundations|Link]]
   - Telescopes as dependency-ordered sequences of types
   - Universe hierarchy and cumulativity : [[Dependent-Type-Theory-Foundations|Link]]
   - Subtyping between universes : [[Dependent-Type-Theory-Foundations|Link]]
   - Bidirectional type checking and type inference : [[Dependent-Type-Theory-Foundations|Link]]
   - Weak head normal form and conversion checking : [[Dependent-Type-Theory-Foundations|Link]]
   - Inductive families of datatypes : [[Dependent-Type-Theory-Foundations|Link]]
   - The identity type and uniqueness of identity proofs : [[Dependent-Type-Theory-Foundations|Link]]
   - The K axiom : [[Dependent-Type-Theory-Foundations|Link1]], [[Pattern-Matching-over-Inductive-Families|Link2]]
   - Record types encoded via Sigma types : [[Dependent-Type-Theory-Foundations|Link]]
   - Implicit function spaces : [[Dependent-Type-Theory-Foundations|Link1]], [[The-Agda-Language|Link2]]

2. **Pattern Matching over Inductive Families** : [[Pattern-Matching-over-Inductive-Families|Link]]
   - Pattern matching instantiating both goal type and context
   - Accessible versus inaccessible patterns : [[Pattern-Matching-over-Inductive-Families|Link]]
   - Context mappings as substitutions given by patterns
   - Matching, unification, and context splitting : [[Pattern-Matching-over-Inductive-Families|Link]]
   - The external versus internal approach to checking pattern matching : [[Pattern-Matching-over-Inductive-Families|Link]]
   - Overlapping and prioritized clauses compiled to case trees
   - Coverage checking and the covering algorithm : [[Pattern-Matching-over-Inductive-Families|Link]]
   - Caseless versus empty datatypes and refutation of impossible cases
   - Reduction of pattern matching to elimination rules via the K axiom : [[Pattern-Matching-over-Inductive-Families|Link]]
   - The `with` construct for matching on intermediate results : [[Pattern-Matching-over-Inductive-Families|Link]]
   - Views as a pattern for emulating non-standard case analysis : [[Pattern-Matching-over-Inductive-Families|Link]]

3. **Metavariables and Implicit Arguments** : [[Metavariables-and-Implicit-Arguments|Link]]
   - Metavariables standing for undetermined terms
   - Well-typed approximation of ill-typed intermediate terms
   - Guarded constants carrying a candidate value and a constraint : [[Metavariables-and-Implicit-Arguments|Link]]
   - Constraint generation and postponement during conversion checking
   - Restricted pattern unification for instantiating metavariables : [[Metavariables-and-Implicit-Arguments|Link]]
   - Soundness and termination of type checking with metavariables : [[Metavariables-and-Implicit-Arguments|Link1]], [[The-Agda-Language|Link2]]
   - Consistent signatures and constraint solving as signature extension
   - Implicit function spaces versus intersection types : [[The-Agda-Language|Link1]], [[Dependent-Type-Theory-Foundations|Link2]]
   - Automatic insertion of metavariables for omitted implicit arguments : [[Metavariables-and-Implicit-Arguments|Link]]

4. **Module Systems for Dependently Typed Languages** : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Separation of scope checking from type checking
   - Hierarchical modules, qualified names, and opening modules : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Private definitions and their effect on displayed normal forms : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Name modifiers: using, hiding, and renaming : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Re-exporting names with public opens : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Parameterised modules as sections with abstracted telescopes : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Module application and the open-module shorthand : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Splitting programs across files via import : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Records as parameterised projection modules : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Record subtyping and its interaction with metavariables : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Scope-checking algorithm: scope stacks and name spaces : [[Dependent-Type-Theory-Foundations|Link]]
   - Type-checking translation of sections and module applications : [[Module-Systems-for-Dependently-Typed-Languages|Link]]

5. **The Agda Language** : [[The-Agda-Language|Link]]
   - Names, operators, and mixfix syntax : [[The-Agda-Language|Link]]
   - Interaction points as unsolved metavariables : [[The-Agda-Language|Link]]
   - Implicit syntax and underscore placeholders : [[The-Agda-Language|Link]]
   - Datatype and function declarations with strict positivity : [[The-Agda-Language|Link]]
   - Inductive families and dotted (inaccessible) patterns : [[The-Agda-Language|Link]]
   - Record declarations and generated projection modules : [[The-Agda-Language|Link]]
   - Local and private helper definitions : [[The-Agda-Language|Link]]
   - Mutual inductive-recursive definitions : [[The-Agda-Language|Link]]
   - An internal certified solver for commutative monoid equations : [[The-Agda-Language|Link]]
   - Normalisation of monoid expressions and soundness of normalisation
   - Chain reasoning combinators for equational proofs

6. **Connecting Type Theory to First-Order Automation** : [[Connecting-Type-Theory-to-First-Order-Automation|Link]]
   - The logical framework $MLF_{Prop}$ with propositions and proof types : [[Connecting-Type-Theory-to-First-Order-Automation|Link]]
   - Translation of open formulas to first-order logic : [[Connecting-Type-Theory-to-First-Order-Automation|Link]]
   - Geometrical formulas and their intuitionistic clausification : [[Connecting-Type-Theory-to-First-Order-Automation|Link]]
   - The resolution and restricted paramodulation calculus : [[Connecting-Type-Theory-to-First-Order-Automation|Link]]
   - Well-typedness preservation under unification and resolution
   - The conservativity theorem connecting FOL proofs to framework derivations
   - The plug-in mechanism for external tool integration : [[Connecting-Type-Theory-to-First-Order-Automation|Link]]
   - The FOL plug-in and the Gandalf theorem prover
   - Human-readable proof traces as a design goal

7. **Related and Prior Work in Type Theory Implementations** : [[Related-and-Prior-Work-in-Type-Theory-Implementations|Link]]
   - Cayenne and undecidable type checking under general recursion
   - McBride's thesis and the Epigram programming model : [[Related-and-Prior-Work-in-Type-Theory-Implementations|Link]]
   - The Delphin language and higher-order pattern matching
   - Coq as a programming language and the Russell layer : [[Related-and-Prior-Work-in-Type-Theory-Implementations|Link]]
   - Module systems of Haskell, Cayenne, and Coq compared
   - Dependent ML, GADTs, and other limited dependent extensions

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 11–26)

**Summary:** Sets the scene by motivating dependent types for programming, surveying prior and contemporary approaches (Cayenne, Epigram, Delphin, Coq-as-programming-language), and presenting the basic dependent type theory $UTT_\Sigma$ together with a bidirectional type-checking algorithm that the rest of the thesis extends.

**Key Definitions & Concepts by Section:**
- **1.1 Overview of the thesis** — roadmap of the thesis's five main contributions (pattern matching, metavariables, module system, FOL connection, Agda implementation).
- **1.2 Context** — dependent type theory's history since Martin-Löf (1972); proof assistants Coq, NuPrl, Alf, Agda, Lego; two routes to dependently typed programming (theory-to-language vs. language-plus-dependent-types).
- **1.3 A basic dependent type theory** — $UTT_\Sigma$ (telescope $(x_1:A_1)\ldots(x_n:A_n)$, dependent function/$\Pi$-type $(x:A)\to B$, dependent pair/$\Sigma$-type $(x:A)\times B$, universe hierarchy $\mathrm{Set}_i$, cumulative subtyping); typing, subtyping, and conversion rules ($\beta\eta$-equality). : [[Dependent-Type-Theory-Foundations|Link]]
- **1.4 Type checking** — bidirectional judgements $\Gamma \vdash e \downarrow A ; t$ (inference) and $\Gamma \vdash e \uparrow A ; t$ (checking); weak head normal form; syntax-directed subtyping and conversion checking on neutral/normal terms. : [[Dependent-Type-Theory-Foundations|Link1]], [[Module-Systems-for-Dependently-Typed-Languages|Link2]], [[Pattern-Matching-over-Inductive-Families|Link3]]
- **1.5 Extensions to the theory** — inductive families via `data` declarations, the identity type `Id` and the K axiom (uniqueness of identity proofs), record types as Sigma-type sugar, implicit function spaces $\{x:A\}\to B$.

**Key Questions:**
1. Why does the bidirectional algorithm require type information when checking $\lambda$-abstractions and dependent pairs, and what does this imply for checking $\beta$-redexes?
2. What is the K axiom, and why is it not derivable from the ordinary elimination rule for the identity type even though it is expected to hold under pattern matching?
3. In what sense does the subtyping relation for $\Sigma$ and $\Pi$ remain invariant rather than co/contravariant, and what alternative could be chosen?

---

### Chapter 2: Pattern Matching (pp. 27–48)

**Summary:** Develops a type-checking algorithm for definitions by pattern matching over inductive families, where matching on one value can instantiate the types and values of other variables in context; introduces accessible/inaccessible patterns, context splitting, coverage checking with overlapping clauses, and the `with` construct for matching on intermediate expressions. : [[Pattern-Matching-over-Inductive-Families|Link1]], [[The-Agda-Language|Link2]]

**Key Definitions & Concepts by Section:**
- **2.1 Type checking pattern match equations** — context mappings $\sigma:\Delta\to\Gamma$ as linear lists of patterns; matching $\mathrm{Match}(\sigma,\bar p)\Rightarrow\bar q$; unification relative to flexible variables (rules U-Var, U-Fail, U-Occ, U-Con, U-Tel, U-Conv); context splitting $\mathrm{Split}(\bar p,\Delta)\Rightarrow\sigma$; accessible vs. inaccessible ($\lfloor t\rfloor$) patterns; refuting elements of empty/caseless types with the absurd pattern $\emptyset$. : [[The-Agda-Language|Link1]], [[Dependent-Type-Theory-Foundations|Link2]]
- **2.2 Coverage checking** — overlapping, prioritized clauses (first-match semantics); translation to a case tree; the Covering algorithm (Match/Missed/Split rules); Berry's majority function as an example where clauses hold only as a covering, not as definitional equalities; connection to uniqueness of identity proofs via the K axiom. : [[Pattern-Matching-over-Inductive-Families|Link]]
- **2.3 The `with` construct** — introduced by McBride and McKinna; adds an extra argument abstracted from an intermediate expression; compiled to an auxiliary function; examples: filtering lists with a sublist proof, rewriting via `with`, and the `Parity` view for splitting a number into $2k$/$2k{+}1$ cases.

**Key Questions:**
1. Why does pattern matching on an inductive family instantiate not just the scrutinee but also the surrounding context, and how does this give rise to "non-linear" patterns?
2. How does the covering algorithm reconcile user-given overlapping clauses (e.g. the equality function `==`) with the requirement that pattern matching compile to a definitionally-behaved case tree?
3. What problem does the `with` construct solve that plain case expressions on the right-hand side cannot, and why must the abstracted expression be generalized out of the goal type before pattern matching on it?

---

### Chapter 3: Metavariables (pp. 49–74)

**Summary:** Presents a novel type-checking algorithm for a dependently typed logical framework MLF extended with metavariables, guaranteeing that all constructed substitutions remain well-typed by replacing potentially ill-typed subterms with well-typed "guarded constants," and proves the algorithm sound and terminating. : [[Metavariables-and-Implicit-Arguments|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 Introduction** — the problem of ill-typed intermediate terms arising from unresolved equality constraints in the presence of dependent types; contrast with prior approaches (Alf, early Agda) that tolerate partial correctness.
- **3.2 The underlying logic MLF** — Martin-Löf's logical framework as a simplified base theory; uniqueness of types, constructor inversion, substitution, subject reduction, and strengthening lemmas.
- **3.3 The type checking algorithm** — signature operations (Lookup, AddMeta, instantiation, AddConst); guarded constant $p:A=s\text{ when }C$; bidirectional judgements extended with conversion producing constraint sets $C$; MLF restriction $|\Sigma|$ of a signature. : [[Dependent-Type-Theory-Foundations|Link1]], [[Pattern-Matching-over-Inductive-Families|Link2]]
- **3.4 Examples** — a fully solvable example; an example requiring guarded constants (`caseNat`); the `coerce` example showing why omitting guarded constants would allow constructing a non-normalising term (a type-theoretic analogue of $\Omega$).
- **3.5 Proof of correctness** — soundness without constraint solving (Theorem 3.5.5), consistent signatures, soundness of constraint solving, approximation and refinement of user expressions, the main soundness theorem (3.5.18).
- **3.6 Implicit arguments** — the implicit function space $\{x:A\}\to B$; automatic metavariable insertion via the judgement $\Gamma\vdash A\,@\,\bar e\downarrow B;\bar s$. : [[Connecting-Type-Theory-to-First-Order-Automation|Link1]], [[Metavariables-and-Implicit-Arguments|Link2]], [[The-Agda-Language|Link3]]
- **3.7 Extending the underlying theory** — extensions to Sigma/unit types, function types as terms, universe hierarchy, and pattern matching.
- **3.8 Summary** — algorithm decidable and sound; implemented and tested with several thousand metavariables in Agda.

**Key Questions:**
1. Why is it unsafe, in the presence of dependent types, to allow ill-typed intermediate terms during type checking, and how does the `coerce`/`Ω` example demonstrate the danger concretely?
2. What role does a "guarded constant" play, and how does its computation rule (reducing to its candidate value only once its guard is solved) preserve both progress and type safety?
3. What is the difference between metavariable instantiation via unification and constraint solving via guarded constants, and why must both be proven to preserve signature consistency?

---

### Chapter 4: Module System (pp. 75–96)

**Summary:** Presents a simple but expressive module system for dependently typed languages whose central design principle is to separate name-space management (scope checking) entirely from type checking, supporting nested and parameterised modules, name modifiers, and record-based algebraic structures, illustrated by a lattice-theory library. : [[Module-Systems-for-Dependently-Typed-Languages|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Introduction** — comparison with the Haskell, Cayenne, and Coq module systems; the decision to let modules be defined solely by implementations (no separate interfaces).
- **4.2 Description** — hierarchical modules and qualified names; opening modules; private definitions and their effect on printed normal forms; name modifiers `using`, `hiding`, `renaming`; re-exporting via `open ... public`; parameterised modules as sections generalizing Coq sections; module application; splitting programs across files via `import`.
- **4.3 Equipment for record types** — records as Sigma-types compared by name; automatic generation of a parameterised projection module per record. : [[Dependent-Type-Theory-Foundations|Link1]], [[Module-Systems-for-Dependently-Typed-Languages|Link2]]
- **4.4 An example** — a lattice theory library (`PartialOrder`, `SemiLattice`, `Lattice`) exploiting parameterised modules and renaming to derive dual properties (join from meet) for free; **4.4.1** a note on record subtyping and why naive coercion-based subtyping interacts badly with metavariables.
- **4.5 Implementation** — the scope-checking algorithm: scope stacks, name spaces, push/pop, `Using`/`Hiding`/`Renaming` operators on name spaces, and the type-checking treatment of sections and module applications (parameter abstraction/lambda-lifting).
- **4.6 Summary** — the module system reduces, after scope checking, to name-space management plus lambda-lifting, independent of the underlying type theory.

**Key Questions:**
1. Why does the thesis choose to decouple the module system entirely from the type checker, and what practical benefits (e.g. separate compilation, simplicity) does this separation buy?
2. How do parameterised modules combined with renaming let the lattice-theory example derive the join semilattice's laws from the meet semilattice's laws "for free"?
3. What specific problem arises when combining record subtyping via automatic coercion with metavariable-based implicit arguments, and why is the module system's alternative (turning a parameter into a field) preferred?

---

### Chapter 5: The Agda Language (pp. 97–124)

**Summary:** Describes Agda — the language implementing the ideas of the previous chapters — from a user's perspective, covering its concrete syntax, then develops an extended literate-Agda example: an internally certified decision procedure for equations in a commutative monoid. : [[The-Agda-Language|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Language description** — names and mixfix operators (`if_then_else_`); interaction points (`?`, `{! !}`) as unsolved metavariables; implicit syntax with `_`; function and lambda syntax; implicit arguments `{x : A}` and named implicit application; `data` declarations, strict positivity, and inductive families with dotted (inaccessible) patterns; `record` declarations and generated projection modules; local (`where`) versus private helper definitions; mutual inductive-recursive definitions; the module system in practice. : [[The-Agda-Language|Link]]
- **5.2 A bigger example** — building, module by module, a certified commutative-monoid equation solver: **5.2.1** basic logical connectives; **5.2.2** basic datatypes (`Bool`, `Nat`, `Fin`, `List`, `Vec`) and BUILTIN pragmas; **5.2.3** equivalence and decidable-equivalence relation libraries with instances for `Fin` and `List`; **5.2.4** the `Chain` module for readable equational reasoning (`chain>_`, `_===_by_`, `_qed`); **5.2.5** `Monoid` and `CommutativeMonoid` records; **5.2.6** representing monoid expressions (`Expr`), normal forms as sorted lists, and deciding provability (`IsProvable`); **5.2.7** the semantics of expressions, soundness of normalisation (`normalise-sound`), and the `prove` function that produces an actual monoid-equation proof from a decision procedure. : [[The-Agda-Language|Link]]

**Key Questions:**
1. How does the `Chain` module's `chain>_ / _===_by_ / _qed` combinator improve readability over directly nested calls to transitivity, and what trick (a private wrapper datatype) makes its implicit arguments solvable?
2. In the monoid-equation solver, what is the role of the soundness lemma `normalise-sound`, and why is the *decision* that an equation holds (via comparing normal forms) enough to obtain an actual proof term without further computation?
3. What distinguishes an inaccessible (dotted) pattern from an ordinary pattern in Agda's concrete syntax, and why is this distinction necessary when pattern matching on inductive families such as `IsEven`?

---

### Chapter 6: First-order Logic (pp. 125–152)

**Summary:** Presents a way to connect a dependently typed logical framework $MLF_{Prop}$ to a first-order resolution theorem prover (Gandalf), so that trivial propositional and first-order reasoning steps can be automated while high-level proof structure (induction, case analysis) remains explicit in the framework; proves a conservativity metatheorem justifying the connection and demonstrates it on examples from relational algebra, category theory, and computer algebra. : [[Connecting-Type-Theory-to-First-Order-Automation|Link]]

**Key Definitions & Concepts by Section:**
- **6.1 Introduction** — motivation for combining interactive frameworks with automatic FOL provers; the problem of unreadable resolution proofs after skolemisation/clausification; restricting to open and geometrical formulas to avoid this.
- **6.2 The Logical Framework $MLF_{Prop}$** — syntax with `Set`, `El`, `Prop`, `Prf`; proof types and set contexts; the `fol` rule and its side condition $\Gamma\vdash_{FOL}T$; natural deduction signature $\Sigma_{nd}$ and classical signature $\Sigma_{class}$ (law of excluded middle). : [[Connecting-Type-Theory-to-First-Order-Automation|Link]]
- **6.3 Translation from $MLF_{Prop}$ to FOL** — translating universally quantified, quantifier-free proof types to open first-order formulas; geometrical formulas; the resolution calculus (ax, sub, res, refl, para rules) and restricted paramodulation; **6.3.3** proof of correctness — well-typedness preservation under unification (Lemma 6.3.1), lifting resolution/paramodulation steps to the framework, and the conservativity theorem (6.3.5); **6.3.4** worked examples (induction over naturals, Warshall's algorithm). : [[Connecting-Type-Theory-to-First-Order-Automation|Link]]
- **6.4 Implementation** — a Haskell prototype; **6.4.1** implicit arguments easing heavy LF notation; **6.4.2** the general plug-in mechanism; **6.4.3** the FOL plug-in and its typing rule for `fol-plugin(...)`.
- **6.5 Examples** — **6.5.1** relational algebra (symmetry of transitive closure); **6.5.2** category theory (epi morphisms); **6.5.3** computer algebra (nilpotency in an integral ring), after M. Beeson.
- **6.6 Related Work** — comparison with Smith & Tammet, Huang et al.'s $\Omega$-MKRP, Wick & McCune's implicit typing, Bezem/Hendriks/de Nivelle, Hurd's Gandalf tactic for HOL, JProver, Meng & Paulson's Vampire–Isabelle integration. : [[Related-and-Prior-Work-in-Type-Theory-Implementations|Link]]
- **6.7 Future Work** — extending to Sigma-types, datatypes, more plug-ins, and internally certified provers as an alternative to external plug-ins.

**Key Questions:**
1. Why does restricting the connection to open, geometrical formulas make first-order resolution proofs both readable and intuitionistically valid, whereas general FOL formulas would not have this property?
2. What is the conservativity theorem (6.3.5) actually claiming, and why is the well-typedness-preservation lemma for most general unifiers (6.3.1) the technical crux of its proof?
3. Why must paramodulation from a variable be forbidden in the restricted calculus used here, and what ill-typed term could otherwise be derived?

---

### Chapter 7: Conclusions (pp. 153–156)

**Summary:** Summarizes the thesis's contributions chapter by chapter (pattern matching, metavariables, module system, automation, Agda) and closes with directions for future work: program compilation with type-directed optimization, effectful programming, multi-stage programming/reflection, and — most importantly in the author's view — the open challenge of learning to program effectively with dependent types.

**Key Definitions & Concepts by Section:**
- Flat summary (no subsections): recap of pattern-matching algorithm liberalized to allow overlapping clauses; metavariable algorithm's soundness and scalability; module system's independence from the underlying language; automation via geometrical-formula translation and conservativity; Agda as the integrating implementation; future work directions — compilation (citing Brady), effects, reflection/multi-stage programming (citing Brady & Hammond), and the pedagogical challenge of dependently typed programming (citing McBride & McKinna).

**Key Questions:**
1. Across the four technical contributions (pattern matching, metavariables, modules, automation), what common design principle recurs — of separating a feature cleanly from the core type checker — and why does the author see this as key to practicality?
2. What future-work direction does the author consider "perhaps the most important challenge," and why does he view Agda as only "a good step along the way" rather than a solution to it?
