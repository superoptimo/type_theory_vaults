# A HoTT Approach to Computational Effects — Guidelines

## Header

**Title:** A HoTT Approach to Computational Effects
**Author(s):** Phillip A. Wells (advised by Nathan Fox)
**Publication:** Senior Independent Study Thesis, The College of Wooster, 2019 (Senior Independent Study Theses, Paper 8566)

**Brief Summary:**
This undergraduate thesis develops a model for describing computational effects — mutations of real-world state produced by a computation — within homotopy type theory (HoTT), rather than within the more common categorical (monad) or algebraic-effects frameworks. It first builds up the necessary HoTT machinery (types as spaces, identity types, the Univalence Axiom), surveys classical models of computation (automata, Turing machines, uncountability results) and their type-theoretic reinterpretation, introduces the Coq proof assistant as the vehicle for formalization, and finally defines an "action" type — a triple of `bind`, `eval`, and `transform` functions satisfying an eval-bind law — instantiated for identity, interactive input, and exception-handling effects.

**Intent of the Author:**
The author wants to show that homotopy type theory's distinctive treatment of equality (via the Univalence Axiom) offers a viable, isomorphism-invariant foundation for describing effectful programs as total functions over values, and to provide initial evidence — through worked examples — that this "action" model captures familiar computational effects such as I/O and exception handling.

---

## Topic List

1. **Computational Effects and Existing Models** : [[Computational-Effects-and-Existing-Models|Link]]
   - Computational effects as mutations of real-world state : [[Computational-Effects-and-Existing-Models|Link]]
   - Pure versus impure functional programming
   - Monads as programmable semicolons
   - Limitations of monads from a type-theoretic perspective
   - Algebraic effects and the separation of declaration from handling : [[Computational-Effects-and-Existing-Models|Link]]
   - Motivation for unifying a theory of effects with a theory of types
2. **Foundations of Homotopy Type Theory** : [[Foundations-of-Homotopy-Type-Theory|Link]]
   - Types as topological spaces : [[Type-Formers|Link]]
   - Judgments of typing and judgmental equality : [[Propositions-as-Types|Link]]
   - Universes and the cumulative hierarchy
   - Typical ambiguity
   - Function types and currying : [[Equivalence-and-Univalence|Link1]], [[Type-Formers|Link2]]
   - Constant functions and fibers
   - Totality and continuity of type-theoretic functions
3. **Type Formers** : [[Type-Formers|Link]]
   - Sum types as disjoint unions : [[Type-Formers|Link]]
   - Product types as ordered pairs : [[Type-Formers|Link]]
   - The empty type : [[Type-Formers|Link]]
   - The unit type : [[Type-Formers|Link]]
   - Constructing finite types from empty and unit types : [[Type-Formers|Link]]
   - Dependent types as type families : [[Type-Formers|Link]]
   - Dependent product types : [[Type-Formers|Link]]
   - Dependent sum types : [[Type-Formers|Link]]
4. **Propositions as Types** : [[Propositions-as-Types|Link]]
   - The Curry-Howard correspondence
   - Identity types and propositional equality : [[Propositions-as-Types|Link]]
   - Reflexivity and path induction
   - Propositions as contractible types : [[Propositions-as-Types|Link]]
   - Truncation of non-propositional types : [[Propositions-as-Types|Link]]
   - Encoding predicate logic (implication, negation, conjunction, disjunction, quantifiers) as types
5. **Equivalence and Univalence** : [[Equivalence-and-Univalence|Link]]
   - Homotopy between functions : [[Equivalence-and-Univalence|Link1]], [[Foundations-of-Homotopy-Type-Theory|Link2]]
   - Quasi-inverse and homotopy equivalence : [[Equivalence-and-Univalence|Link]]
   - Singleton types : [[Propositions-as-Types|Link]]
   - Fibers and the definition of equivalence : [[Equivalence-and-Univalence|Link]]
   - The Univalence Axiom
   - Sets as types identified only by reflexivity : [[Equivalence-and-Univalence|Link]]
6. **Models of Computation** : [[Models-of-Computation|Link]]
   - Formal languages and alphabets : [[Cardinality-and-Uncountability|Link1]], [[Models-of-Computation|Link2]]
   - Finite automata and regular languages
   - Pushdown automata and context-free languages
   - Non-determinism and computational power : [[Models-of-Computation|Link]]
   - Turing machines and decidable languages : [[Models-of-Computation|Link]]
   - Recursively enumerable languages
   - The halting problem
7. **Cardinality and Uncountability** : [[Cardinality-and-Uncountability|Link]]
   - Countable infinity
   - Bijections between infinite sets : [[Cardinality-and-Uncountability|Link]]
   - Cantor's diagonalization argument : [[Cardinality-and-Uncountability|Link]]
   - Uncountability of the power set of a countably infinite set
   - Existence of non-Turing-recognizable languages : [[Cardinality-and-Uncountability|Link]]
8. **Computation Within HoTT** : [[Computation-Within-HoTT|Link]]
   - Open problem of a computational interpretation of univalence
   - Reasoning about computation models internally to HoTT
   - Turing machines encoded as functions : [[Computation-Within-HoTT|Link]]
   - Encoding partiality with a sum type
   - Turing categories as an alternative categorical model
9. **The Coq Proof Assistant** : [[The-Coq-Proof-Assistant|Link]]
   - Inductive type definitions : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link1]], [[The-Coq-Proof-Assistant|Link2]]
   - The Set universe
   - Constructors and automatically generated induction principles
   - Basic proof commands (Theorem, Proof, reflexivity, intros, exact, Qed)
   - Record types for dependent sums : [[The-Coq-Proof-Assistant|Link]]
   - Function definitions via pattern matching : [[The-Coq-Proof-Assistant|Link]]
   - The HoTT library for Coq : [[The-Coq-Proof-Assistant|Link]]
10. **A Type-Theoretic Model of Actions and Effects** : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link]]
    - Referential transparency for effectful programs : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link]]
    - Definition of an action as bind, eval, and transform functions
    - The eval-bind identity law
    - Lifting ordinary functions to functions on effects : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link]]
    - The Identity Action : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link]]
    - Interactive Input as an action : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link]]
    - Exception Handling as an action : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link]]
    - Safe-division example with exception transform

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 1–6)

**Summary:** Motivates the thesis by contrasting impure imperative code, pure functional programming, monads, and algebraic effects as prior approaches to computational effects, then argues for modeling effects within homotopy type theory because of its treatment of equality via the Univalence Axiom.

**Key Definitions & Concepts:**
- Computational effect — any mutation of real-world state occurring as a byproduct of computation.
- Monad — a pair of operations plus a construction method that generalizes sequencing of effectful computations; described as a "programmable semicolon."
- Algebraic effects — a model (Plotkin and Power) separating effect declaration from effect handling, typically written as programs of type $A \to^{\epsilon} B$.
- Univalence Axiom — identifies the identity of types with the equivalence of types, providing isomorphism invariance for a theory of effects.

**Key Questions:**
1. Why does the author consider monads "unsatisfying from a type theorist's perspective," despite their practical success in Haskell and F#?
2. What advantage does treating "effectful actions as values in and of themselves" (rather than as a separate entity bound to a value) offer, according to the introduction?

---

### Chapter 2: Homotopy Type Theory (pp. 7–26)

**Summary:** Introduces the reader to the notation and structures of intensional (homotopy) type theory, presenting each construct alongside its topological analogue, and builds up to the identity type, propositions-as-types, and the Univalence Axiom. : [[Foundations-of-Homotopy-Type-Theory|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 Type and Space** — the judgments $a : A$ and $A \equiv B$; universes and the cumulative hierarchy $\mathcal{U}_0 : \mathcal{U}_1 : \mathcal{U}_2 : \dots$; typical ambiguity; function types $f : A \to B$ and currying; constant functions and fibers; sum types $A + B$ with injections $\mathrm{inl}$/$\mathrm{inr}$; product types $A \times B$; the empty type $0$ and unit type $1$; dependent types $f : A \to \mathcal{U}$; dependent product ($\Pi$) types; dependent sum ($\Sigma$) types. : [[Type-Formers|Link]]
- **2.2 Proof and Logic** — the Curry-Howard correspondence; identity types $a = b$ and the witness/path interpretation; reflexivity ($\mathrm{refl}$) and path induction; propositions as contractible types, formalized as $\mathrm{Prop} :\equiv \prod_{a,b:A}(a=b)$; truncation $\|A\|$; predicate logic encoded via product (conjunction), sum (disjunction), function (implication), $0$ (falsehood/negation), $\Pi$ (universal quantifier), $\Sigma$ (existential quantifier); homotopy $f \sim g$ between functions; quasi-inverse and homotopy equivalence; singleton types; equivalence defined via singleton fibers; the Univalence Axiom $(A=B) \simeq (A \simeq B)$; sets as types identified only by reflexivity.

**Key Questions:**
1. Why are the judgments $a : A$ and $a \equiv a$ said to be neither provable nor disprovable, but rather syntactically valid or invalid?
2. How does the chapter's definition of `Prop` (via contractibility) prevent the paradoxes that arise when any type is allowed to represent a proposition?
3. What does the Univalence Axiom assert about the function `idToEq : (A = B) → (A ≃ B)`, and why does the author call this "remarkable"?

---

### Chapter 3: Computation (pp. 27–46)

**Summary:** Surveys classical models of computation — finite automata, pushdown automata, and Turing machines — alongside cardinality arguments for the sizes of infinity, then examines what it means to reason about computation inside homotopy type theory, including Turing machines encoded as functions and Turing categories as an alternative. : [[Models-of-Computation|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 Formal Languages and Automata** — formal language, alphabet, finite automaton (states, transition function, accept states), regular language, pushdown automaton (adds a stack), context-free language, non-determinism, Turing machine (adds an infinite tape), decidable/recursive languages, Turing-recognizable languages, recursively enumerable languages. : [[Cardinality-and-Uncountability|Link1]], [[Models-of-Computation|Link2]]
- **3.2 The Sizes of Infinity** — countable infinity ($\aleph_0$); bijections between infinite sets; Cantor's diagonalization argument; Proposition (the power set of a countably infinite set is uncountable); the uncountability of the set of all languages, implying non-Turing-recognizable languages exist. : [[Cardinality-and-Uncountability|Link]]
- **3.3 Computation in HoTT** — the open problem of a computational interpretation of the Univalence Axiom; reasoning about computation models internally; encoding Turing machines as functions with an appended step-count argument to handle partiality; Turing categories (Vinogradova, Felty, Scott) as a categorical alternative that restricts to computable functions directly. : [[Computation-Within-HoTT|Link]]

**Key Questions:**
1. Why is it insufficient to represent a possibly-non-halting program simply as a function $f : \mathbb{N} \times \mathbb{N} \to \mathbb{N} + 1$, and how does adding a step-count argument address this?
2. How does Cantor's diagonalization argument establish that the set of all formal languages is uncountable, and what does this imply about Turing-recognizable languages?
3. In what sense is "reasoning about computation in HoTT" distinct from HoTT itself admitting a computational interpretation, according to Section 3.3?

---

### Chapter 4: The Coq Proof Assistant (pp. 47–54)

**Summary:** Introduces the syntax and style of Coq proofs — inductive type definitions, basic tactic-based proofs, record types, and pattern-matching function definitions — as preparation for the formalized examples used later in the thesis, and points to the HoTT library for Coq used throughout. : [[The-Coq-Proof-Assistant|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Inductive Types** — the `Inductive` keyword; the `Set` universe; constructors (e.g. `O` and `S` for `nat`); automatically generated induction principles; distinctness of constructors. : [[The-Coq-Proof-Assistant|Link]]
- **4.2 Basic Proofs** — `Theorem`, `Proof`, `reflexivity`, `intros`, `exact`, `Qed`; a worked proof that $A \times B \to A$. : [[The-Coq-Proof-Assistant|Link]]
- **4.3 Records** — record types as a convenience for representing dependent sums; a constructive representation of the rationals; automatically generated `Build_<name>` constructors.
- **4.4 Functions** — function definitions via `Definition` and `match`/`end` pattern-matching blocks.
- **4.5 HoTT in Coq** — the HoTT library for Coq, which re-implements the standard library with Univalence and HoTT-specific structures. : [[The-Coq-Proof-Assistant|Link]]

**Key Questions:**
1. What role does the automatically generated induction principle for `nat` play in proving properties of natural numbers in Coq?
2. Why does the author prefer Record types over direct $\Sigma$-type induction when representing structures like the rationals?

---

### Chapter 5: Actions and Effects (pp. 55–62)

**Summary:** Presents the thesis's central contribution: a type-theoretic definition of an effectful "action" as a triple of functions (`bind`, `eval`, `transform`) satisfying a single coherence law, then instantiates this definition for three concrete effects — the Identity Action, Interactive Input, and Exception Handling — each with an accompanying invariance proof. : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link]]

**Key Definitions & Concepts by Section:**
- **(unsectioned introduction)** — referential transparency; Definition 1 (an action over $\Phi(A)$ comprises $\mathrm{bind}: A \to \Phi(A)$, $\mathrm{eval}: \Phi(A) \to A$, $\mathrm{transform}: \Phi(A) \to \Phi(A)$, and the law $\prod_{a:A} \mathrm{eval}(\mathrm{bind}\ a) = a$); Proposition 2 (lifting any $f : A \to A$ to $f_{\Phi(A)} : \Phi(A) \to \Phi(A)$ via $\lambda\varphi.\ \mathrm{bind}(f(\mathrm{eval}\ \varphi))$).
- **5.1 Applications** — the general goal of showing the action type captures fundamental effects.
- **5.1.1 Identity Action** — $I(A)$ with constructor $\mathrm{Return}$; the no-op effect. : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link]]
- **5.1.2 Interactive Input** — $In(A)$ with constructors $\mathrm{Init}$ and $\mathrm{Input}$; the starred value $a^*$ marking user-dependent evaluation. : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link]]
- **5.1.3 Exception Handling** — $E(A)$ with constructors $\mathrm{Except}$ and $\mathrm{Return}$; a worked safe-division example where `transform` routes zero-denominator pairs to `Except`. : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link]]

**Key Questions:**
1. What does the single law $\prod_{a:A} \mathrm{eval}(\mathrm{bind}\ a) = a$ guarantee about an action, and why is this the only axiom required in Definition 1?
2. In the Interactive Input action, why is the transformed value marked $a^*$ rather than treated as a fixed, known element of $A$?
3. How does the safe-division example use `transform` (rather than `bind` or `eval`) to implement exception-raising behavior?

---

### Chapter 6: Conclusion (pp. 63)

**Summary:** Briefly reflects on the evidence provided by Chapter 5's examples for the viability of the action-type model, and outlines open work: proving completeness of the model, implementing it in a real language, and relating it to other effect models.

**Key Definitions & Concepts:**
- (No new definitions; a summary chapter reflecting on the action-type model's scope and open questions.)

**Key Questions:**
1. What specific claims does the author leave unproven, and what would "completeness" of the action model mean in this context?

---

### Appendix A: 3-State Busy Beaver in Coq (pp. 65–80)

**Summary:** Provides a Coq implementation (using coinductive lists and a `Delay` monad for potentially non-terminating computation) of a generic Turing machine simulator, `TM`/`compute`, and a specific 3-state busy beaver instantiation, supporting the Turing-machine-as-function discussion in Chapter 3.

**Key Definitions & Concepts:**
- Coinductive list (`CoList`) — used to represent the (potentially infinite) tape.
- `Delay` type — a coinductive type (`HERE`/`LATER`) used to represent a computation that may take an unbounded number of steps to produce a result.
- `TM` — the single-step transition function combining state, tape, and the transition relation `delta`.
- `compute` — a coinductive fixpoint that repeatedly applies `TM` until a final state is reached.

**Key Questions:**
1. Why does the busy beaver implementation need a coinductive `Delay` type rather than an ordinary (inductive) option or termination proof?
