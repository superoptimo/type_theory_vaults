# Dependently Typed Functional Programs and their Proofs — Guidelines

## Header

**Title:** Dependently Typed Functional Programs and their Proofs
**Author(s):** Conor McBride
**Publication:** PhD thesis, University of Edinburgh (LFCS), 1999/2000

**Brief Summary:**
This thesis develops technology for programming with dependent inductive families of datatypes in intensional type theory, and for proving those programs correct, by exploiting elimination rules as the central organizing tool for both construction and reasoning. It introduces $\mathrm{OLEG}$, a type theory with explicitly bound "holes" (metavariables) for representing partial proofs/programs entirely within the judgments of the calculus, a systematic technique for constructing and deploying elimination rules in refinement proof (the `eliminate` tactic), a treatment of "no confusion" and "no cycle" properties for arbitrary dependent datatypes, and a proof that dependent pattern matching (as in ALF) is admissible over ordinary type theory once equipped with the uniqueness-of-identity-proofs axiom. The central worked example is a first-order unification algorithm shown to be structurally recursive precisely because dependent types let the number of free variables live in the index of the term datatype.

**Intent of the Author:**
McBride's stated purpose is to show the advantage a dependent type system lends to "principled programming" — using type indices not merely to state theorems but to make illegal states unrepresentable and thereby make recursion structural, termination arguments unnecessary, and program correctness proofs short. He explicitly wants to close the open question (posed by Coquand, and by Hofmann–Streicher's non-conservativity result) of exactly what must be added to a conventional type theory to license ALF-style dependent pattern matching.

---

## Topic List

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

## Chapter Summaries

### Chapter 1: Introduction (pp. 6–15)

**Summary:** McBride states the thesis's purpose — exploiting dependent type theory's computational aspects for programming, not just theorem-proving — and surveys prior treatments of dependent datatypes (Luo's UTT, Coquand/ALF pattern matching, Agda's restricted families, Coq's Case/Fix split), situating his own contribution (OLEG, elimination-rule technology, object-level unification for pattern matching) against them.

**Key Definitions & Concepts:**
- **1.1 overview** — OLEG (a type theory with "holes"/metavariables), derived elimination rules as specification/programming tool, Case/Fix separation (Giménez), the plan of chapters 2–7.
- **1.2 this thesis in context** — Luo's UTT and its elimination-constant style; ALF-style pattern matching and its non-conservativity (Hofmann–Streicher: implies uniqueness of identity proofs); Agda's restriction forbidding constructors from constraining their return type; Cayenne's unrestricted recursion; Cornes' Coq `Cases` macro and its gap for subfamily case analysis, which this thesis fills.
- **1.3 implementation** — the LEGO-based OLEG prototype and its relationship to the theory presented. : [[Implementation-and-Reflection|Link]]

**Key Questions:**
1. Why does Agda's restriction on constructor return types trade away expressiveness (e.g. the identity type) for a simpler unification-free pattern matching story?
2. In what precise sense does dependent pattern matching require more than conventional type theory provides, per Hofmann–Streicher?

---

### Chapter 2: OLEG, a Type Theory with Holes (pp. 16–51)

**Summary:** Defines the OLEG core calculus (essentially Luo's ECC with local definition) and its "development calculus" superstructure, which represents a theorem prover's state — assumptions, proved theorems, unproved claims, partial proofs — directly as a context of typed judgments, with holes bound explicitly (à la Miller's mixed-prefix unification) rather than tracked via an external ledger with explicit substitution. : [[The-OLEG-Type-Theory-of-Holes|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 the OLEG core** — universes ($\mathrm{Prop}$, $\mathrm{Type}_j$), bindings ($\forall$, $\lambda$, let), contexts and judgments, contraction schemes ($\beta$, $\eta$, $\zeta$), cumulativity, the core inference rules, metatheorems (Church–Rosser, strengthening, subject reduction, strong normalisation, cut). : [[The-OLEG-Type-Theory-of-Holes|Link]]
- **2.2 the OLEG development calculus** — states/components/partial constructions, the four binding forms (assumption, definition, hole, guess), development-calculus judgments, the "replacement property" that any partial construction may be swapped for another of the same type. : [[The-OLEG-Type-Theory-of-Holes|Link]]
  - **2.2.1 positions and replacement** — positions as one-hole contexts over partial constructions; the replacement metatheorem. : [[The-OLEG-Type-Theory-of-Holes|Link]]
  - **2.2.2 the state information order** — the $\sqsubseteq$ preorder on states and the monotonicity metatheorem. : [[The-OLEG-Type-Theory-of-Holes|Link]]
- **2.3 life of a hole** — the four basic replacement operations: claim (birth), try (marriage), regret (divorce), solve (death). : [[The-OLEG-Type-Theory-of-Holes|Link]]
- **2.4 displaying an OLEG state** — a tree/spine visualisation of states, with "clouds" for hiding uninteresting subtrees.
- **2.5 basic component manipulations** — assume, justify, claim, try, regret, solve, cut, abandon, postpone as qualified state transitions.
- **2.6 moving holes** — attack, intro-$\forall$/intro-!, retreat, raise-$\forall$/raise-! ("raising" after Miller). : [[The-OLEG-Type-Theory-of-Holes|Link]]
- **2.7 refinement and unification** — naïve-refine, the need for genuine unification (not mere matching) once dependent types are involved, the `unify` and `unify-refine` tactics built atop an imported first-order unifier. : [[The-OLEG-Type-Theory-of-Holes|Link]]
- **2.8 discharge and other permutations** — the "four discharges" reconstructing LEGO's Discharge tactic; permuting/deleting arguments of functional holes. : [[The-OLEG-Type-Theory-of-Holes|Link]]
- **2.10 sequences, telescopes, families, triangles** — telescope notation for dependent sequences of types, telescope application, indexed families, the "free telescope" of a family, and "triangles" (telescopes of type families) for abstracting over telescopes themselves. : [[The-OLEG-Type-Theory-of-Holes|Link]]

**Key Questions:**
1. Why does binding holes explicitly in the context (rather than via an external ledger plus explicit substitution) let OLEG avoid the scope-leakage problems that plague systems like LEGO and TypeLab/ALF?
2. What is the "replacement property" for partial constructions, and why is it the load-bearing metatheorem that makes refinement-style theorem proving in OLEG sound?
3. Why must ?-bindings be forbidden from leaking into types, and what would go wrong if they were not?

---

### Chapter 3: Elimination Rules for Refinement Proof (pp. 52–86)

**Summary:** Develops a systematic vocabulary (target, scheme, aperture, patterns, cases, case data, inductive hypotheses) for elimination rules of every kind — datatype induction, inversion/case-analysis, recursion induction on functions — and builds the `eliminate` tactic, which refines a goal by a chosen elimination rule, automatically constructing and simplifying the constrained scheme required when the goal is more specific than the rule's full aperture. : [[Elimination-Rules-for-Refinement-Proof|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 propositional equality (definition deferred)** — motivates the need for a relaxed equality (later '$\simeq$'/"John Major" equality) that can compare elements of intensionally distinct but propositionally equal types.
- **3.2 anatomy of an elimination rule** — target, scheme, aperture, indices, patterns, pattern variables, cases, case data, inductive hypotheses/recursive calls; Gentzen/Prawitz's inversion principle as the conceptual ancestor. : [[Elimination-Rules-for-Refinement-Proof|Link]]
- **3.3 examples of elimination rules** — parameterised elimination (`listElim`), case-analysis/inversion principles (for $\le$), Peano-style injectivity/conflict as inversion rules, recursion induction (`NEqRecI`), extensional "introduction rules" via propositional equality and their corresponding inversion principles for rewriting blocked computations. : [[Elimination-Rules-for-Refinement-Proof|Link]]
- **3.4 legitimate targets** — targets must be declared by the rule's "manufacturer" (via boxed/`?`-annotated occurrences), since a machine cannot infer what a rule eliminates from its type alone. : [[Elimination-Rules-for-Refinement-Proof|Link]]
- **3.5 scheming with constraints** — constructing a basic constrained scheme by abstracting all premises and equating indices to instantiated patterns; telescopic equations for aperture constraints. : [[Elimination-Rules-for-Refinement-Proof|Link]]
  - **3.5.1 simplification by coalescence** — collapsing a fresh $\forall$-bound variable constrained equal to an index.
  - **3.5.2 what to fix, what to abstract** — redundancy criteria for omitting premises from the scheme.
  - **3.5.3 abstracting patterns from the goal** — using boxed indices to trigger rewriting-style abstraction. : [[Pattern-Matching-for-Dependent-Types|Link]]
  - **3.5.4 constraints in inductive proofs** — "friendly" (unification) versus "unfriendly" (matching) constraints, and the unfold/fold correspondence this reveals.
- **3.6 an elimination tactic** — the five-stage `eliminate` tactic: preparing the application, fingering targets, constructing the scheme, proving the goal, tidying up. : [[Elimination-Rules-for-Refinement-Proof|Link]]
- **3.7 an example — NEq** — the running worked example: building `NEq` by nested elimination, then proving its recursion-induction principle, its inversion principle `NEqInv`, and its extensional "introduction rules". : [[Elimination-Rules-for-Refinement-Proof|Link]]

**Key Questions:**
1. Why must a rule's manufacturer explicitly annotate what counts as a "legitimate target," rather than the machine inferring it from the rule's type?
2. What is the difference between a "friendly" and an "unfriendly" equational constraint arising during scheme construction, and why does that distinction correspond exactly to unification versus matching?
3. How does the `eliminate` tactic's automatic scheme-pruning recover, by mechanical means, the same scheme a human would write by hand?

---

### Chapter 4: Inductive Datatypes (pp. 87–116)

**Summary:** Gives a formal, uniform account of strictly-positive inductive datatypes and families (simple, parameterised, higher-order-recursive, dependent-indexed, proof-irrelevant relations, records), each equipped with a mechanically generated elimination rule and $\iota$-reduction, then shows how to derive from the traditional one-step eliminator the more useful Coq-style `Case`/`Fix` pair — including the "guarded fixpoint" construction that lets recursion decompose an auxiliary data structure rather than the original argument (motivated by the Fibonacci counterexample). : [[Inductive-Datatypes-and-Their-Elimination|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 construction of inductive datatypes** — the four components of any datatype definition: type former, constructors, elimination rule, $\iota$-reductions. : [[Inductive-Datatypes-and-Their-Elimination|Link]]
  - **4.1.1 simple inductive datatypes like N** — general schema for non-indexed datatypes and their `IndElim`. : [[Inductive-Datatypes-and-Their-Elimination|Link]]
  - **4.1.2 parameterised datatypes like list** — parameters fixed once for the whole definition. : [[Inductive-Datatypes-and-Their-Elimination|Link]]
  - **4.1.3 datatypes with higher-order recursive arguments, like ord** — strictly-positive higher-order arguments and families of recursion hypotheses (ordinal numbers example). : [[Inductive-Datatypes-and-Their-Elimination|Link]]
  - **4.1.4 dependent inductive families like the fins** — genuinely indexed families (`fin`), mutual definition across index instances, the general `Fam`/`FamElim` schema. : [[Inductive-Datatypes-and-Their-Elimination|Link]]
  - **4.1.5 inductively defined relations like <** — proof irrelevance, strong vs. weak induction principles. : [[Inductive-Datatypes-and-Their-Elimination|Link]]
  - **4.1.6 record types** — records as one-constructor, no-recursion datatypes; "spot" projection notation; the `R[x]:t` opening sugar. : [[Inductive-Datatypes-and-Their-Elimination|Link]]
- **4.2 a compendium of inductive datatypes** — standard finite types, sums/maybe, vectors. : [[Inductive-Datatypes-and-Their-Elimination|Link]]
- **4.3 abolishing $\Sigma$-types and reinventing them** — presenting dependent pairs as a parameterised record rather than a primitive; tactics for $\Sigma$ in goals. : [[Inductive-Datatypes-and-Their-Elimination|Link]]
  - **4.3.1 the blunderbuss tactic** — depth-first search tactic exploiting hypotheses under $\forall$ and $\Sigma$, including `blunder-refl` for equational premises.
- **4.4 constructing Case and Fix** : [[Inductive-Datatypes-and-Their-Elimination|Link]]
  - **4.4.1 case analysis for datatypes and relations** — deriving `Case` from the full eliminator via "hubris": prove something false, postpone, discharge. : [[Inductive-Datatypes-and-Their-Elimination|Link]]
  - **4.4.2 the guarded fixpoint principle** — the Fibonacci-function motivating example for why one-step elimination is insufficient; the notion of "guarded" arguments; constructing an auxiliary data structure `Aux` to carry exactly the recursive information needed. : [[Inductive-Datatypes-and-Their-Elimination|Link]]

**Key Questions:**
1. Why does the traditional one-step eliminator fail to support the natural (Burstall–Darlington-transformed) definition of Fibonacci, and how does the guarded-fixpoint construction repair this?
2. In what sense are Case and Fix a strictly more convenient decomposition of the traditional elimination rule, without loss of expressive power?
3. Why is it preferable to present dependent pairs as a degenerate record type rather than as a primitive type-theoretic construct?

---

### Chapter 5: Equality and Object-Level Unification (pp. 117–151)

**Summary:** Gives a formal treatment of "John Major" equality ($\simeq$) — a relaxed propositional equality allowing comparison of elements of different types, equivalent to Martin-Löf equality plus uniqueness of identity proofs but far more convenient for telescopic (sequence) equations — then builds a complete, terminating, most-general-unifier-computing algorithm for constructor-form equations, including automatically generated "no confusion" (conflict/injectivity) and "no cycle" theorems for any inductive datatype. : [[Equality-and-Object-Level-Unification|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 two nearly inductive definitions of equality** : [[Equality-and-Object-Level-Unification|Link]]
  - **5.1.1 Martin-Löf's identity type** — `idElim` ("J"), `idSubst` and its substitution/coercion sugar. : [[Equality-and-Object-Level-Unification|Link]]
  - **5.1.2 uniqueness of identity proofs** — Altenkirch–Streicher's `idUnique` ("K"), independence from `idElim` (Hofmann–Streicher). : [[Equality-and-Object-Level-Unification|Link]]
  - **5.1.3 ', or 'John Major' equality** — $\simeq$ defined via `eqElim`, contrasted with the useless "fully inductive" `eqIndElim`. : [[Equality-and-Object-Level-Unification|Link]]
  - **5.1.4 equality for sequences** — telescopic equations $\vec r \simeq \vec s$, telescopic substitution (`eqSubstn`) and uniqueness (`eqUniquen`) constructed by recursion on telescope length. : [[Equality-and-Object-Level-Unification|Link]]
  - **5.1.5 the relationship between = and '** — mutual constructions showing $\simeq$ and ($=$ plus uniqueness) are equivalent, via the `sproj` lemma on cell-packaged pairs. : [[Equality-and-Object-Level-Unification|Link]]
- **5.2 first-order unification for constructor forms** — the `Qnify`-style tactic extended to dependent types. : [[Equality-and-Object-Level-Unification|Link]]
  - **5.2.1 transition rules for first-order unification** — identity, coalescence, substitution, conflict, injectivity, cycle; the decision table by leading-equation shape. : [[Equality-and-Object-Level-Unification|Link]]
  - **5.2.2 an algorithm for constructor form unification problems** — termination by a three-part lexicographic measure; correctness in terms of most general unifiers. : [[Equality-and-Object-Level-Unification|Link]]
  - **5.2.3 conflict and injectivity** — the "Peano concerto" construction computing, by case analysis, the appropriate conflict/injectivity theorem for any pair of constructors of any family at once. : [[Equality-and-Object-Level-Unification|Link]]
  - **5.2.4 cycle** — why naïve induction fails for non-symmetric cycles; the generalised "not a proper subterm" predicate and its recursive construction proving absence of cyclic equations for any datatype.
  - **5.2.5 a brief look beyond constructor form problems** — the undecidable general case; non-constructor-form indices; using a function's own recursion-induction principle (e.g. `plus`'s) to recover constructor-form subgoals. : [[Equality-and-Object-Level-Unification|Link]]

**Key Questions:**
1. Why is John Major equality strictly more convenient than iterating Martin-Löf equality when stating equality of telescopes/sequences under type dependency?
2. How does the "Peano concerto" construction avoid the need for $n^2$ separately-proved conflict/injectivity theorems per datatype?
3. Why does a naïve inductive proof of "no cycles" fail for asymmetric cycle patterns, and what strengthening (the "not a proper subterm" predicate) repairs it?

---

### Chapter 6: Pattern Matching for Dependent Types (pp. 152–183)

**Summary:** Reviews Coquand's ALF-style characterisation of admissible pattern-matching programs (no nesting, guarded recursion, covering by case-splitting via unification), then proves the chapter's central metatheorem: any such program can be constructed intensionally faithfully from OLEG's datatype elimination rules (guarded fixpoints, case analysis, first-order unification), and gives interactive tactics (`program`, `split`, `return`) that build such programs step by step, alongside a discussion of which programs can be mechanically *recognised* as admissible from their equations alone. : [[Pattern-Matching-for-Dependent-Types|Link]]

**Key Definitions & Concepts by Section:**
- **6.1 pattern matching in ALF** — Coquand's conditions (no nesting, guarded recursion, covering); elementary covering and covering defined via unification-driven case-splitting; Berry's majority-function counterexample distinguishing extensional from intensional (realisable) pattern sets. : [[Pattern-Matching-for-Dependent-Types|Link]]
- **6.2 interactive pattern matching in OLEG** : [[Pattern-Matching-for-Dependent-Types|Link]]
  - **6.2.1 computational aspects of elimination** — unfolding and folding as the technique for verifying a candidate implementation's intensional behaviour against its intended equations. : [[Pattern-Matching-for-Dependent-Types|Link]]
  - **6.2.2 conservativity of pattern-matching over OLEG** — the main theorem: any ALF-admissible covering built by constructor-form-unification case-splitting can be replayed via `FamFix`/`FamCase`/unification in OLEG with the same intensional behaviour. : [[Pattern-Matching-for-Dependent-Types|Link]]
  - **6.2.3 constructing programs** — the `program`, `split`, `return` tactics, illustrated by building `vlast` (last element of a nonempty vector), including the subtlety that splitting the length index (rather than the vector) yields a shorter, more surprising definition. : [[Pattern-Matching-for-Dependent-Types|Link]]
- **6.3 recognising programs** — the harder converse problem: given only equations, recover the justification. : [[Pattern-Matching-for-Dependent-Types|Link]]
  - **6.3.1 recursion spotting** — checking the guardedness intersection condition to find a valid recursion argument. : [[Pattern-Matching-for-Dependent-Types|Link]]
  - **6.3.2 exact problems** / **6.3.3 splitting problems** / **6.3.4 empty problems** — measuring progress by constructor-symbol excess; the undecidable problem of recognising non-obviously-empty cases. : [[Pattern-Matching-for-Dependent-Types|Link]]
- **6.4 extensions**
  - **6.4.1 functions with varying arity** — dependently-typed functions whose arity varies across equations (e.g. `sum`). : [[Pattern-Matching-for-Dependent-Types|Link]]
  - **6.4.2 more exotic recursion** — lexicographic recursion (Ackermann's function) built from nested guarded eliminations. : [[Pattern-Matching-for-Dependent-Types|Link]]

**Key Questions:**
1. What is Berry's majority-function counterexample, and why does it show that "constructor-form, exhaustive, disjoint" patterns are not sufficient to guarantee *intensionally* correct pattern matching?
2. In the conservativity theorem, what precise role do unfolding and folding play in showing that the OLEG-constructed term has the same computational behaviour as the pattern-matching equations demand?
3. Why does recognising an *empty* case from equations alone run into undecidability, and what pragmatic one-step-split heuristic does McBride adopt instead?

---

### Chapter 7: Some Programs and Proofs (pp. 184–239)

**Summary:** Applies all preceding technology to two substantial, previously-unavailable examples: a monadic treatment of capture-avoiding substitution for the untyped $\lambda$-calculus with de Bruijn indices (via `thin`/`thick`), and — the thesis's centerpiece — a first-order unification algorithm on trees that is *structurally recursive* (no external termination ordering) precisely because terms are indexed by their finite variable count, verified correct via an "optimistic optimisation" framework and inversion-principle-driven proofs of `FlexFlex`/`FlexRigid`.

**Key Definitions & Concepts by Section:**
- **7.1 concrete categories, functors and monads** — records `Concrete`, `Functor`, `Monad`/Kleisli-triple packaging arrows as data with an extensional interpretation, to organize the syntax-manipulation functions to follow. : [[Concrete-Categories-Functors-and-Monads-for-Syntax|Link]]
  - **7.1.1–7.1.3** — records for categories, functors, and "concrete" monads (Manes' Kleisli triples), with `maybeF`/`maybeM` as the running example.
- **7.2 substitution for the untyped $\lambda$-calculus** — `Lam n` (terms over $n$ free variables via `fin`), the `Rename` functor and `SubstM` monad. : [[Concrete-Categories-Functors-and-Monads-for-Syntax|Link]]
  - **7.2.1 lift, thin and thick** — `lift` (functorial action on renamings under a binder), `thin` (inserting a new variable), `thick` (its partial inverse distinguishing "old" vs. "the new" variable), with inversion principles `liftInv`/`thickInv` central to later blocked-computation unblocking; the `[x↦t]` "knockout" substitution. : [[Concrete-Categories-Functors-and-Monads-for-Syntax|Link]]
  - **7.2.2 the substitution monad splits the renaming functor** — a single generalized structural `map` function (parametric in a target family `T`) implements both renaming and substitution at once, avoiding Altenkirch–Reus's duplicated non-structural definitions; proofs that renaming is functorial and substitution monadic (`Split`, `BackC`, etc.), all via `mapEq` plus recursion induction/inversion. : [[Concrete-Categories-Functors-and-Monads-for-Syntax|Link]]
- **7.3 a correct first-order unification algorithm** — the thesis's main example. : [[A-Structurally-Recursive-Unification-Algorithm|Link1]], [[Equality-and-Object-Level-Unification|Link2]]
  - **7.3.1 optimistic optimisation** — general framework: `Closed` constraints, `Maximal` solutions, the `Optimist` lemma showing a conjunction of closed constraints can be optimised by solving each in turn against an accumulated bound.
  - **7.3.2 optimistic unification** — casting unification as optimisation in the Kleisli category of substitutions; `mgu` defined via an accumulator-passing `bmgu`.
  - **7.3.3 dependent types to the rescue** — the key insight: indexing `tree` (and the accumulator) by variable count makes the recursion *structural* on the variable count, with no need for an external well-founded ordering or occurs-count lemma. : [[Pattern-Matching-for-Dependent-Types|Link1]], [[The-OLEG-Type-Theory-of-Holes|Link2]]
  - **7.3.4 correctness of mgu** — `mguInv`/`bmguInv` inversion principles; case-by-case correctness (rigid-rigid conflict/injectivity via `Optimist`, flexible cases via accumulator unloading), reducing correctness to that of `FlexFlex` and `FlexRigid`. : [[A-Structurally-Recursive-Unification-Algorithm|Link]]
  - **7.3.5 what substitution tells us about the occurs check** — the occurs check reconceived as *computing a witness* (the `Knockout` lemma) rather than a boolean; `FlexFlex` via `thick`.
  - **7.3.6 positions** — `pos n`, a "reversed zipper" datatype of one-hole tree contexts, `goes`/`then`, and the `NoCycle` lemma (a term can only contain itself at the root position). : [[Concrete-Categories-Functors-and-Monads-for-Syntax|Link]]
  - **7.3.7 check and FlexRigid** — `check` (pushing `thick` through a tree) with inversion principle `checkInv`; completing `FlexRigid` and its correctness proof using `Knockout` and `NoCycle`. : [[A-Structurally-Recursive-Unification-Algorithm|Link]]
  - **7.3.8 comment** — comparison with prior unification verifications (Manna–Waldinger, Paulson, Rouyer, Bove), crediting the indexed-datatype approach with internalising the termination argument that all prior treatments needed external orderings for.

**Key Questions:**
1. Why does indexing `tree` by its number of free variables turn unification from a generally-recursive algorithm (needing an external termination ordering) into a structurally recursive one?
2. What is the "optimistic optimisation" framework's `Optimist` lemma, and why does it justify solving a conjunction of downward-closed constraints by accumulating a bound one constraint at a time?
3. How does reframing the occurs check as computing a `Knockout` witness (via `thick`) do double duty as both a decision procedure and a proof of unifier maximality?

---

### Chapter 8: Conclusion (pp. 240–244)

**Summary:** Summarises the thesis's contributions — OLEG's hole-in-context treatment, the demonstration that uniqueness of identity proofs suffices for dependent pattern matching, John Major equality, the automatically-derivable no-confusion/no-cycle theorems, and the general methodology of using elimination rules to specify and reason about programs abstractly — and argues that dependent types deserve wider adoption in functional programming because they make more recursion structural by putting "the right structure" into the data itself.

**Key Definitions & Concepts:**
- **8.1 further work** — recognising a genuine dependently-typed programming language (handling empty cases robustly), an ML-style type-inference algorithm as a natural next optimisation problem, and derived elimination rules ("views," after Wadler) as a programming (not just proof) technique — "the left [-hand side] came into its own." : [[Implementation-and-Reflection|Link]]

**Key Questions:**
1. In what sense does McBride argue that "if my recursion is not structural, I am using the wrong structure" — and how does the unification example in chapter 7 embody that mantra?
2. What specification methodology does McBride advocate going forward, and how does it extend the elimination-rule philosophy of chapter 3 from proof to program derivation?

---

### Appendix A: Implementation (pp. 245–246)

**Summary:** Notes on the LEGO-based OLEG prototype: partial constructions were not rigidly separated from terms in the implementation, LEGO's own unification algorithm was reused (so scoping conditions on holes were not separately enforced, relying instead on LEGO's independent typechecker), the `eliminate` tactic's abstraction facility for derived (non-datatype) elimination rules was never implemented, and John Major equality postdates the prototype, so the implementation uses traditional equality plus uniqueness throughout.
