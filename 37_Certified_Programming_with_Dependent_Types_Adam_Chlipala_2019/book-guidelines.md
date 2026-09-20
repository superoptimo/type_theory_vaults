# Certified Programming with Dependent Types — Guidelines

## Header

**Title:** Certified Programming with Dependent Types

**Author(s):** Adam Chlipala

**Publication:** Free online book (PDF/HTML, generated from literate Coq source via `coqdoc`), copyright Adam Chlipala 2008–2013, 2015, 2017; licensed under a Creative Commons Attribution-Noncommercial-No Derivative Works 3.0 Unported License. This edition dated April 21, 2019. Also published in print by MIT Press (the online edition remains free even after print publication). Code examples were tested against Coq 8.9.0. Companion home page: adam.chlipala.net/cpdt/.

**Brief Summary:**
The book teaches "certified programming" — writing programs in the Coq proof assistant together with machine-checked proofs (or with dependent types) guaranteeing they meet their specifications. It centers on two recurring techniques: programming with rich dependent types, so correctness is captured directly in types and the need for explicit proof is minimized, and Ltac-scripted proof automation, so any proofs that remain are robust, maintainable single-tactic scripts rather than long brittle manual tactic sequences. It progresses from basic inductive and coinductive types and predicates, through dependently typed programming and general recursion, into the foundational subtleties of equality, universes, and axioms, then into proof-engineering techniques (logic programming, Ltac, proof by reflection, module-based large-scale organization), and closes with a case study in reasoning about programming-language syntax.

**Intent of the Author:**
Chlipala wants to convince readers that program verification technology is mature enough today to be used routinely as a support tool in computer science research, and to serve as a practical handbook for engineering certified programs in Coq. He aims to disseminate the "design patterns" — chiefly dependently typed functions and custom Ltac decision procedures — that let practitioners avoid the unreadable, unmaintainable proof scripts that give tactic-based theorem proving a bad reputation.

---

## Topic List

1. **The Coq Proof Assistant and Certified Programming** : [[The-Coq-Proof-Assistant-and-Certified-Programming|Link]]
   - Certified versus certifying programs
   - Comparison of proof assistants : [[The-Coq-Proof-Assistant-and-Certified-Programming|Link]]
   - The de Bruijn criterion : [[The-Coq-Proof-Assistant-and-Certified-Programming|Link]]
   - Coq versus Agda and Epigram : [[The-Coq-Proof-Assistant-and-Certified-Programming|Link]]
   - Design patterns for readable and maintainable proofs : [[The-Coq-Proof-Assistant-and-Certified-Programming|Link]]
   - The Calculus of Inductive Constructions and Gallina : [[Techniques-for-General-Recursion|Link]]
   - Strong normalization and relative consistency

2. **The Curry–Howard Correspondence** : [[The-Curry-Howard-Correspondence|Link]]
   - Proofs as programs and propositions as types
   - Propositional and first-order logic encoded as inductive types
   - Constructive versus classical logic
   - Program extraction from constructive proofs : [[The-Curry-Howard-Correspondence|Link]]

3. **Inductive Types** : [[Inductive-Types|Link]]
   - Enumerations and simple recursive types : [[Inductive-Types|Link]]
   - Parameterized and polymorphic types : [[Inductive-Types|Link]]
   - Mutually inductive types and their induction principles : [[Inductive-Types|Link]]
   - Reflexive types and higher-order abstract syntax : [[Reasoning-About-Programming-Language-Syntax|Link1]], [[Inductive-Types|Link2]]
   - The strict positivity requirement : [[Inductive-Types|Link]]
   - Nested inductive types : [[Inductive-Types|Link]]
   - Manual construction of induction principles : [[Coinductive-Types-and-Infinite-Data|Link1]], [[Datatype-Generic-Programming|Link2]]

4. **Inductive Predicates and Judgments** : [[Inductive-Predicates-and-Judgments|Link]]
   - Judgments as inductively defined predicates : [[Inductive-Predicates-and-Judgments|Link]]
   - Equality as an inductive type : [[Inductive-Types|Link]]
   - Rule induction : [[Inductive-Predicates-and-Judgments|Link]]
   - Quantifier ordering and its effect on induction hypotheses : [[The-Curry-Howard-Correspondence|Link1]], [[Inductive-Predicates-and-Judgments|Link2]]
   - Case analysis pitfalls of destruct versus inversion : [[Inductive-Predicates-and-Judgments|Link]]

5. **Coinductive Types and Infinite Data** : [[Coinductive-Types-and-Infinite-Data|Link]]
   - Streams and co-fixpoints : [[Coinductive-Types-and-Infinite-Data|Link]]
   - The guardedness condition and productivity : [[Coinductive-Types-and-Infinite-Data|Link]]
   - Bisimulation and co-inductive equality : [[Coinductive-Types-and-Infinite-Data|Link]]
   - Co-induction principles : [[Coinductive-Types-and-Infinite-Data|Link]]
   - Co-inductive operational semantics for non-termination : [[Techniques-for-General-Recursion|Link]]

6. **Dependent Types for Program Correctness** : [[Dependent-Types-for-Program-Correctness|Link]]
   - Subset types and proof erasure : [[Dependent-Types-for-Program-Correctness|Link]]
   - Decidable propositions and sumbool : [[Dependent-Types-for-Program-Correctness|Link1]], [[Proof-by-Reflection|Link2]]
   - Partial subset types and sumor
   - Monadic notations for dependently typed computation
   - Certified type checkers
   - Length-indexed lists and the fin index type
   - Heterogeneous lists and the member type family : [[Dependent-Types-for-Program-Correctness|Link]]
   - The convoy pattern : [[Dependent-Types-for-Program-Correctness|Link]]
   - Dependently typed red-black trees : [[Dependent-Types-for-Program-Correctness|Link]]
   - Certified regular expression matching : [[Dependent-Types-for-Program-Correctness|Link]]
   - The one rule of dependent pattern matching : [[Dependent-Types-for-Program-Correctness|Link]]
   - Tagless interpreters via type-indexed syntax
   - Recursive versus reflexive encodings of dependent data structures : [[Dependent-Types-for-Program-Correctness|Link]]

7. **Techniques for General Recursion** : [[Techniques-for-General-Recursion|Link]]
   - Well-founded recursion and the accessibility predicate : [[Techniques-for-General-Recursion|Link]]
   - Domain-theoretic non-termination monads : [[Techniques-for-General-Recursion|Link]]
   - Co-inductive non-termination monads : [[Techniques-for-General-Recursion|Link]]
   - Comparing general recursion encodings : [[Techniques-for-General-Recursion|Link]]

8. **Reasoning About Equality Proofs** : [[Reasoning-About-Equality-Proofs|Link]]
   - Definitional versus propositional equality
   - Unicity of identity proofs and Streicher's axiom K
   - Heterogeneous equality : [[Reasoning-About-Equality-Proofs|Link]]
   - Equivalence of Coq's equality axioms
   - Function extensionality : [[Reasoning-About-Equality-Proofs|Link]]

9. **Datatype-Generic Programming** : [[Datatype-Generic-Programming|Link]]
   - Reifying datatype definitions as universe types : [[Datatype-Generic-Programming|Link]]
   - Recursion schemes as reified induction principles : [[Datatype-Generic-Programming|Link]]
   - Generic proofs about generic programs : [[Datatype-Generic-Programming|Link]]

10. **Universes and Axioms** : [[Universes-and-Axioms|Link]]
    - The Type hierarchy and predicativity
    - Girard's paradox
    - Parameters versus indices in inductive definitions
    - The Prop universe and the elimination restriction
    - Impredicativity of Prop
    - Axioms of classical logic and choice
    - Axioms and stuck computation : [[Universes-and-Axioms|Link]]
    - Techniques for avoiding axioms : [[Universes-and-Axioms|Link]]

11. **Proof Automation by Logic Programming** : [[Proof-Automation-by-Logic-Programming|Link]]
    - The auto and eauto tactics
    - Backtracking and unification in proof search : [[Proof-Automation-by-Logic-Programming|Link]]
    - Hint databases and hint kinds : [[Proof-Automation-by-Logic-Programming|Link]]
    - Program synthesis via inductive relations : [[Proof-Automation-by-Logic-Programming|Link]]
    - Rewrite hints and autorewrite : [[Proof-Automation-by-Logic-Programming|Link]]

12. **The Ltac Tactic Language** : [[The-Ltac-Tactic-Language|Link]]
    - The match goal construct and its backtracking semantics
    - Ltac as a functional and imperative hybrid language : [[The-Ltac-Tactic-Language|Link]]
    - Continuation-passing style in Ltac
    - Custom recursive proof search tactics : [[The-Ltac-Tactic-Language|Link]]
    - Explicit unification variable allocation and forward reasoning : [[The-Ltac-Tactic-Language|Link]]

13. **Proof by Reflection** : [[Proof-by-Reflection|Link]]
    - Verified decision procedures : [[Proof-by-Reflection|Link]]
    - Syntax reification of Gallina propositions
    - Injecting uninterpreted atoms into reified syntax
    - Reification under variable binders : [[Proof-by-Reflection|Link]]
    - Proof term size as a design metric

14. **Engineering Large Proof Developments** : [[Engineering-Large-Proof-Developments|Link]]
    - Ltac anti-patterns and maintainable proof style : [[The-Coq-Proof-Assistant-and-Certified-Programming|Link1]], [[Engineering-Large-Proof-Developments|Link2]]
    - Debugging and profiling proof automation
    - The Coq module system and functors
    - Build processes for multi-file projects

15. **Reasoning About Programming Language Syntax** : [[Reasoning-About-Programming-Language-Syntax|Link]]
    - Dependent de Bruijn indices : [[Reasoning-About-Programming-Language-Syntax|Link]]
    - Lifting and weakening operations
    - Higher-order abstract syntax and parametric HOAS : [[Reasoning-About-Programming-Language-Syntax|Link]]
    - Term well-formedness and parametricity
    - Verifying program transformations

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 6–16)

**Summary:** Chlipala motivates certified/certifying programming (producing machine-checked proofs that a program meets its spec), surveys competing proof assistants (ACL2, Coq, Isabelle/HOL, PVS, Twelf) and dependently typed languages (Agda, Epigram), and argues for Coq based on its higher-order functional foundation, rich dependent types, adherence to the de Bruijn criterion, programmable proof automation (Ltac), and support for proof by reflection; closes with prerequisites and practical setup instructions.

**Key Definitions & Concepts by Section:**
- **1.1 Whence This Book?** — certified program (a program paired with a formal certificate/proof that it meets its specification, distinct from governmental "certification"); certifying program (a program that outputs both an answer and a proof of its correctness on each run, composing with a proof checker to yield a certified program); criteria for a serious proof assistant (intended for software use, well-engineered, has an external user community); listed tools: ACL2, Coq, Isabelle/HOL, PVS, Twelf.
- **1.2 Why Coq?** — dependent types (types that may contain or reference program terms, e.g. an array type parameterized by its size, enabling correctness properties to be captured directly in types); the de Bruijn criterion (a proof assistant satisfies it if it produces proof terms checkable by a small trusted kernel, regardless of how complex or extensible the search procedures used to find them are); `Ltac` (Coq's domain-specific tactic/decision-procedure language, able to extend automation without ever weakening trust in the kernel); proof by reflection (using Coq's unified syntactic class of programs and proof terms to write programs that *compute* proofs, exploiting dependent types so the type of a decision procedure guarantees correctness of any run). : [[Techniques-for-General-Recursion|Link1]], [[The-Coq-Proof-Assistant-and-Certified-Programming|Link2]], [[The-Ltac-Tactic-Language|Link3]]
- **1.3 Why Not a Different Dependently Typed Language?** — comparison with Agda/Epigram: those tools favor being programming languages over proof assistants and lack mature tactic-based theorem proving, which Chlipala argues is unavoidable when a correctness proof's structure doesn't mirror the program's structure (e.g. compiler correctness proved by induction on execution traces).
- **1.4 Engineering with a Proof Assistant** — the book's central thesis: design patterns for avoiding unreadable, unmaintainable Coq proof scripts, built around two techniques: dependently typed functions and custom Ltac decision procedures. : [[Engineering-Large-Proof-Developments|Link1]], [[The-Coq-Proof-Assistant-and-Certified-Programming|Link2]]
- **1.6 Using This Book** — the book is generated from literate Coq source files via `coqdoc`; a bundled tactic library (`CpdtTactics.v`, home of the `crush` tactic) is used from the first chapter onward, though Chlipala recommends readers build their own project-specific tactic libraries rather than reusing his.

**Key Questions:**
1. What does it mean for a proof assistant to satisfy the de Bruijn criterion, and why does Chlipala treat this as a dividing line between tools like Coq/Isabelle/HOL and tools like ACL2/PVS?
2. In what sense do dependent types let a programmer write certified programs without writing anything that looks like a proof, and why is this not always sufficient, i.e. why is scripted proof automation still needed?
3. Why does Chlipala prefer Coq over Agda/Epigram despite those languages having less implementation baggage and being easier for some dependently typed programming tasks?

---

### Chapter 2: Some Quick Examples (pp. 17–38)

**Summary:** A whirlwind, non-bottom-up demo chapter building two certified compilers — from arithmetic expressions to a stack machine, then from statically typed expressions to a type-indexed stack machine — to advertise the book's style (dependent types plus Ltac automation) before later chapters explain the underlying mechanisms in detail.

**Key Definitions & Concepts by Section:**
- **2.1 Arithmetic Expressions Over Natural Numbers** — `Inductive` (Coq's keyword for defining algebraic/inductive datatypes, far more expressive than ML/Haskell's `data`/`datatype`); `Set` (the universe of program-level types, as opposed to universes for proofs); source language `exp`/`binop` with denotation functions `binopDenote`/`expDenote` (an interpreter as trivial semantics); target stack-machine language `instr`/`prog`/`stack` with `instrDenote`/`progDenote` (returns `option stack`, `None` on stack underflow); `compile` (the compiler function); the Calculus of Inductive Constructions (CIC, Coq's theoretical foundation, an extension of the Calculus of Constructions) and its metatheoretic properties strong normalization and relative consistency (with ZF-like set theory); Gallina (Coq's term language, an extension of CIC); `Ltac` (tactic language) versus Vernacular (the top-level command language: `Inductive`, `Definition`, `Theorem`, etc.); proof-state anatomy: subgoals, hypotheses above the double-dashed line, conclusion below; core tactics `induction`, `intros`, `unfold`, `simpl`, `fold`, `reflexivity`, `rewrite`; the semicolon tactic combinator (`t1; t2`, applies `t2` to every subgoal left by `t1`, the basis of compositional automation) versus the period terminator (single-step, exploratory); the `crush` tactic (the book's custom highly automated tactic, not part of Coq's standard library); `Qed` (checks and seals a completed proof term); the strengthened-induction-hypothesis pattern (proving an auxiliary, more general lemma — `compile_correct'` — to make an induction go through, then deriving the original theorem `compile_correct`); `Hint Rewrite` (registers a lemma as a rewrite hint so `crush` can use it automatically); program extraction (generating executable OCaml from Coq definitions via the `Extraction` command).
- **2.2 Typed Expressions** — indexed type family / indexed inductive type (e.g. `tbinop : type -> type -> type -> Set`, where constructors can fix indices to specific values, unlike ML/Haskell datatypes indexed only by top-level type variables); comparison to GADTs (which lift the "indices must be bound type variables" restriction but still forbid indexing by arbitrary terms, unlike Coq); dependent pattern matching (case bodies whose expected type depends on the matched value); meta language versus object language (the proof assistant's language versus the language being formalized); `texp t` (well-typed-by-construction expression family) and its denotation via `typeDenote`/`tbinopDenote`/`texpDenote`; type-indexed target language `tstack`/`tinstr`/`tprog`/`vstack` (stack types and instructions indexed so that stack-underflow and type-mismatch become statically impossible, eliminating the `option`/`None` machinery needed in 2.1); implicit arguments (Coq inferring underscore-elided arguments, here flow-of-control-like stack-type information); the idiom of pushing function parameters whose type depends on a matched value inside match branches, needed for definitions like `tinstrDenote` to type-check; `tconcat`/`tcompile` and their correctness proof `tcompile_correct'`, proved automatically via `induction e; crush` once a helper lemma (`tconcat_correct`) is registered as a rewrite hint.

**Key Questions:**
1. Why did the compiler-correctness proof in 2.1 need an auxiliary, more general lemma (`compile_correct'`, quantified over an arbitrary continuation program `p`) rather than being provable directly by induction on the original theorem statement?
2. How does moving from the untyped stack machine (2.1, using `option stack` to handle underflow) to the type-indexed stack machine (2.2, using `tstack`-indexed `tinstr`/`tprog`/`vstack`) change what has to be proved versus what is guaranteed for free by type-checking?
3. What is the practical difference between the period-terminated, exploratory proof style shown for `compile_correct'` in 2.1 and the single `induction e; crush` proof used to prove the analogous `tcompile_correct'` in 2.2, and what does this contrast illustrate about the book's overall proof-automation thesis?

---

### Chapter 3: Introducing Inductive Types (pp. 40–67)

**Summary:** Introduces Coq's Calculus of Inductive Constructions foundation, showing how proofs and programs are unified via the Curry–Howard correspondence, and works through the taxonomy of inductive type definitions (enumerations, recursive types, parameterized types, mutually inductive types, reflexive types, nested types) along with how to construct and use their automatically generated induction principles. : [[Inductive-Types|Link1]], [[Inductive-Predicates-and-Judgments|Link2]], [[The-Curry-Howard-Correspondence|Link3]]

**Key Definitions & Concepts by Section:**
- **3.1 Proof Terms** — Curry–Howard correspondence (theorems as types, proofs as programs that type-check at that type); proof term (any Gallina term of a logical type); `True`/`I` and `False`/`Empty_set` as Curry–Howard duals of `unit`/`tt` and the empty type.
- **3.2 Enumerations** — `Inductive` command; `Set` (type of programs) versus `Prop` (type of proofs/propositions); induction principle `T_ind` auto-generated per `Inductive T`; `destruct` (case analysis) versus `induction`; `discriminate` tactic (proves inequality of differently constructed values).
- **3.3 Simple Recursive Types** — `nat` via `O`/`S`; `Fixpoint` (recursive function definition); `injection` tactic (extracts equality of constructor arguments); `congruence` tactic (decision procedure for equality plus uninterpreted functions); recursive list/tree types (`nat_list`, `nat_btree`); `crush` (CpdtTactics automation tactic). : [[Inductive-Types|Link]]
- **3.4 Parameterized Types** — polymorphic inductive types (`list T`); `Section`/`Variable` mechanism for sharing a parameter across definitions; `Arguments` command for implicit-argument inference. : [[Inductive-Types|Link]]
- **3.5 Mutually Inductive Types** — types defined via mutual `Inductive ... with ...`; the auto-generated `T_ind` is not mutually-inductive-hypothesis-aware; `Scheme` command to generate proper mutual induction principles. : [[Inductive-Types|Link]]
- **3.6 Reflexive Types** — reflexive type (a constructor takes a function returning the same type); higher-order abstract syntax (HOAS) for encoding binders/quantifiers; strict positivity requirement (the defined type may not occur to the left of an arrow in a constructor argument's type) — rejects naive HOAS encodings of lambda-calculus terms to preserve termination/consistency. : [[Inductive-Types|Link]]
- **3.7 An Interlude on Induction Principles** — `T_rect`/`T_rec`/`T_ind` family (recursion principle for `Type`/`Set`/`Prop`); `fix` keyword (anonymous recursive Gallina function); dependently typed pattern matching (`match ... as ... return ...`); manual reimplementation of induction principles via `Section`+`Hypothesis`+`Fixpoint`. : [[Inductive-Types|Link]]
- **3.8 Nested Inductive Types** — nested inductive type (recursive type used as argument to a parameterized type family, e.g. `list nat_tree` inside `nat_tree`); need for hand-written induction principles using nested `fix`; `All` predicate (holds of every list element); `Hint Extern` for custom automation patterns. : [[Inductive-Types|Link]]
- **3.9 Manual Proofs About Constructors** — manual reconstruction of what `discriminate`/`injection` do internally, using `red`, `change`, `rewrite ←`; illustrates the minimality of Coq's core proof-checking rules as a design philosophy. : [[Inductive-Types|Link]]

**Key Questions:**
1. Why does the Curry–Howard correspondence let `->` mean both function type and logical implication, and what breaks if `Prop` and `Set` are collapsed into one universe?
2. Why must inductive type definitions satisfy strict positivity, and what specific inconsistency would follow from accepting a naive HOAS encoding of the untyped lambda calculus?
3. Why is the automatically generated induction principle insufficient for mutually inductive and nested inductive types, and what is the general recipe (`Scheme`, or manual `Section`+`Fixpoint`) for repairing it?

---

### Chapter 4: Inductive Predicates (pp. 68–85)

**Summary:** Shows how the same inductive-definition mechanism used for datatypes builds logical predicates and connectives, covering propositional logic, the constructive (intuitionistic) character of Coq's logic, first-order quantification, and the subtleties of case-analyzing/inducting on predicates whose indices carry information (motivating `inversion` and induction-hypothesis generalization). : [[Inductive-Predicates-and-Judgments|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Propositional Logic** — `True`/`False`/`not` (`not A := A -> False`) as inductive types; `and`/`conj`, `or`/`or_introl`/`or_intror` as inductive connectives with Curry–Howard analogues `prod`/sum types; tactics `constructor`, `destruct`, `split`, `left`/`right`, `tauto` (complete decision procedure for constructive propositional logic), `intuition` (propositional simplification generalizing `tauto`).
- **4.2 What Does It Mean to Be Constructive?** — constructive/intuitionistic logic versus classical logic; classical tautologies ($\neg\neg P \rightarrow P$, $P \lor \neg P$) fail in general, only holding when $P$ is decidable; why a general law of excluded middle would solve the halting problem; distinction between `bool` (decidable, evaluates) and `Prop` (may be undecidable); program extraction (writing programs by proving theorems).
- **4.3 First-Order Logic** — $\forall$ as Coq's dependent function type; implication $P \rightarrow Q$ as a degenerate $\forall x : P, Q$; existential quantifier `ex`/`ex_intro` from the standard library; `exists` tactic; `firstorder` tactic. : [[Reasoning-About-Programming-Language-Syntax|Link]]
- **4.4 Predicates with Implicit Equality** — judgment (an inductively defined predicate presented via natural-deduction-style inference rules); indexed inductive predicate (e.g. `isZero : nat -> Prop`); equality `eq`/`eq_refl` defined as just another inductive type (equality as the least reflexive relation); pitfall: `destruct`/`induction` on an indexed hypothesis generalizes the index to a fresh variable, losing information; `inversion` tactic (case analysis that preserves index constraints, detects impossible cases).
- **4.5 Recursive Predicates** — recursively defined predicates (e.g. `even`); `Hint Constructors`; `auto`/`eauto`; rule induction (inducting on the structure of a proof of a predicate rather than on a plain data argument); the rule governing what stays fixed versus varies in the inductive hypothesis based on the position of quantifiers before versus after the induction target; `apply ... with`, `eapply`. : [[Inductive-Predicates-and-Judgments|Link]]

**Key Questions:**
1. Why does Coq's constructive logic reject $P \lor \neg P$ as a general theorem, and how does this connect to the halting problem via Curry–Howard?
2. What specifically goes wrong when you `destruct` a hypothesis like `isZero 1`, and why does `inversion` avoid that failure mode?
3. Why does the position of a quantified variable relative to the induction target in a theorem statement determine whether it stays fixed or can vary in the inductive hypothesis, and why does this matter for whether a proof by induction on `n` versus induction on a proof of a predicate succeeds?

---

### Chapter 5: Infinite Data and Proofs (pp. 86–101)

**Summary:** Introduces co-inductive types and co-fixpoints as Coq's terminating-yet-productive mechanism for lazy/infinite data (streams), explains the dual guardedness condition that keeps co-recursion consistent, and develops co-inductive equality/bisimulation and co-induction principles needed to prove properties of infinite streams and non-terminating program semantics. : [[Coinductive-Types-and-Infinite-Data|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Computing with Infinite Data** — `CoInductive` types (e.g. `stream`); `CoFixpoint` (co-recursive definition); guardedness condition (every co-recursive call must be a direct argument to a constructor, not nested inside other function calls); productivity (outputs forceable to any finite approximation in finite time); why unrestricted general recursion (e.g. `Fixpoint bad u := bad u`) would make CIC inconsistent by proving any proposition. : [[Coinductive-Types-and-Infinite-Data|Link]]
- **5.2 Infinite Proofs** — ordinary `eq` cannot prove stream equality (only finite syntactic arguments); co-inductive predicate `stream_eq`; `cofix` tactic; `Guarded` command (checks guardedness mid-proof); the `frob` trick (an identity-like function that forces `match`-triggered reduction of a `cofix`); bisimulation (a relation $R$ enforcing equal heads and hereditary $R$-ness of tails); Park's co-induction principle (`stream_eq_coind`), and specialized variants (`stream_eq_loop`, `stream_eq_onequant`) to avoid manually choosing $R$; caution that generic automation (`auto`/`crush`) can produce guardedness-violating "proofs."
- **5.3 Simple Modeling of Non-Terminating Programs** — co-inductive big-step operational semantics (`evalCmd`) that relates non-terminating program executions to all final states, contrasted with inductive semantics which cannot capture non-termination; deriving a co-induction principle for `evalCmd` before use; proof of correctness of a trivial "$0 + e \to e$" optimizer across both terminating and non-terminating executions via `optCmd_correct1`/`optCmd_correct2`. : [[Coinductive-Types-and-Infinite-Data|Link1]], [[Techniques-for-General-Recursion|Link2]]

**Key Questions:**
1. Why is the guardedness condition for `CoFixpoint` the dual of the positivity/recursive-argument restriction for `Fixpoint`, and what inconsistency would unrestricted co-recursion introduce (via Curry–Howard) that mirrors the `Fixpoint bad` example from Chapter 3?
2. Why can't ordinary `eq` express that two streams are equal, and what property must a relation $R$ have to serve as a valid choice for a co-induction principle (bisimulation)?
3. Why does modeling program semantics co-inductively (relating non-terminating executions to all final states) allow one correctness proof to cover both terminating and non-terminating programs uniformly, where an inductive semantics could not?

---

### Chapter 6: Subset Types and Variations (pp. 103–120)

**Summary:** This chapter introduces techniques for fusing programming, specification, and proof into a single artifact using dependent "subset" types, building a series of increasingly refined implementations of a dependently typed natural number predecessor function and culminating in a certified type checker for a small expression language. : [[Dependent-Types-for-Program-Correctness|Link]]

**Key Definitions & Concepts by Section:**
- **6.1 Introducing Subset Types** — dependent function type where an argument's type depends on a value (e.g. $n > 0 \to \text{nat}$); the `sig` type family (`Inductive sig (A : Type) (P : A -> Prop) : Type := exist : forall x : A, P x -> sig P`), a Curry–Howard twin of `ex` living in `Type` rather than `Prop` so its values survive extraction; the `{x : A | P}` notation for subset types; proof erasure during extraction (`Extraction` strips proof components from compiled OCaml); `refine` tactic for building a partial proof/program term with underscore holes that become proof subgoals; `Defined` (marks a definition transparent/unfoldable) versus `Qed` (opaque); the `abstract` tactic modifier for abstracting subgoals into named lemmas to keep terms small; `Program Definition` as an alternative streamlined syntax for subset-typed definitions. : [[Dependent-Types-for-Program-Correctness|Link1]], [[Inductive-Types|Link2]]
- **6.2 Decidable Proposition Types** — `sumbool` (`{A} + {B}`), an inductive type capturing which of two propositions holds, with `left`/`right` constructors; `Yes`/`No`/`Reduce` notations for sumbool-based case analysis; Coq's generalized overloading of `if` to any two-constructor inductive type; the `decide equality` tactic for automatically proving decidable equality; `Extract Inductive` for mapping Coq inductive types (e.g. `sumbool`) onto native OCaml types (e.g. `bool`) during extraction; construction of "smart" Boolean operators and a certified list-membership decision procedure (`In_dec`). : [[Proof-by-Reflection|Link]]
- **6.3 Partial Subset Types** — the `maybe` type family (a `sig` variant permitting obligation-free failure, with `Unknown`/`Found` constructors) and its notations; the `sumor` type family (`A + {B}`, values are either an `A` or a proof of `B`), used to build a maximally expressive possibly-failing predecessor whose type rules out vacuous implementations. : [[Dependent-Types-for-Program-Correctness|Link]]
- **6.4 Monadic Notations** — treating `maybe` informally as a failure monad analogous to Haskell's `Maybe`; bind-like notations for composing richly typed procedures without manual case-matching.
- **6.5 A Type-Checking Example** — a typed expression language (`exp`, `type`) with an inductively defined typing relation `hasType`; `Hint Constructors` to register constructor lemmas for automation; an assertion notation that fails if a decision procedure fails; a certified `typeCheck`; a determinism lemma `hasType_det` (an expression has at most one type) used together with `eauto` to build a stronger `typeCheck'` whose sumor-based type also proves it fails only on ill-typed inputs.

**Key Questions:**
1. Why does the same predecessor function extract to identical OCaml code across several increasingly precise Coq types, and what does that reveal about proof erasure?
2. What is the practical difference between `sig`, `maybe`, and `sumor`, and why does moving from `maybe` to `sumor` yield a maximally expressive type for a possibly-failing function?
3. Why must `Defined` rather than `Qed` be used to close proofs built via `refine`, and what would break if `Qed` were used instead?

---

### Chapter 7: General Recursion (pp. 121–138)

**Summary:** Because Gallina's built-in termination checker only accepts primitive (structural) recursion, this chapter develops three alternative techniques — well-founded recursion, a domain-theory-inspired non-termination monad, and two co-inductive non-termination monads — for encoding general recursive functions such as merge sort, then compares their tradeoffs. : [[Techniques-for-General-Recursion|Link]]

**Key Definitions & Concepts by Section:**
- **7.1 Well-Founded Recursion** — primitive recursion restriction (recursive calls only on syntactic subterms); well-foundedness (`well_founded`) defined via the accessibility predicate `Acc`; a co-inductive characterization of "no infinite decreasing chains" used to justify that accessible elements admit no such chains; the `Fix` combinator for defining functions recursive in the structure of `Acc` proofs; the concrete `lengthOrder` well-founded relation used to define `mergeSort`; the requirement that well-foundedness/subterm-order proofs be closed with `Defined` (not `Qed`) so `Fix` can unwind them computationally; `Fix_eq` and the associated need to prove functional extensionality of the recursive body, since general function extensionality is neither provable nor disprovable in Coq; `well_founded_induction` as the associated induction principle. : [[Techniques-for-General-Recursion|Link]]
- **7.2 A Non-Termination Monad Inspired by Domain Theory** — domain theory's approximation ordering on computation results; the `computation` type as a monotone function from "approximation level" to optional result, paired with a monotonicity proof; `runTo`/`run` relations for characterizing when/what a computation yields; `Bottom` (never terminates), `Return`, and `Bind` as the monad operations, with proofs of the monad laws under an approximation-level equality; the `leq` information order on `option A`; a domain-theoretic `Fix` combinator requiring a `continuous` hypothesis on the recursive body instead of a termination proof; this technique supports functions that may fail to terminate on some inputs while retaining ordinary reasoning. : [[Techniques-for-General-Recursion|Link]]
- **7.3 Co-Inductive Non-Termination Monads** — the `thunk` co-inductive type (`Answer`/`Think`, proposed by Capretta), its `TBind`, and its severe limitation to tail recursion; the `frob`/`frob_eq` idiom for provoking reduction of co-recursive calls; the `comp` co-inductive type (`Ret`/`Bnd`, Megacz's proposal) which makes bind itself a constructor, supporting non-tail recursion but suffering a fatal predicativity restriction / universe inconsistency that blocks higher-order recursive functions. : [[Techniques-for-General-Recursion|Link]]
- **7.4 Comparing the Alternatives** — a systematic comparison of the four techniques along axes: compatibility with normal Coq typing/computation; separability of function definition from termination argument; naturalness of recursive syntax; kind and cost of proof obligations; support for common functional idioms; and whether inversion lemmas require axioms.

**Key Questions:**
1. Why does Coq's `Fix` combinator require the well-foundedness proof and derived order lemmas to be proved with `Defined` rather than `Qed`?
2. What specific limitation of the `thunk` monad makes it unable to express a non-tail-recursive Fibonacci definition, and how does the `comp` monad fix that problem, at what cost?
3. Across the four general-recursion techniques, what is the fundamental tradeoff between functional-programming expressiveness/compatibility with native Coq computation, and the burden of proof obligations imposed at definition time?

---

### Chapter 8: More Dependent Types (pp. 139–164)

**Summary:** This chapter moves beyond subset types into genuinely dependent inductive datatypes indexed by non-propositional data (lengths, types, colors), showing through length-indexed lists, a tagless interpreter, dependently typed red-black trees, and a certified regular-expression matcher how Coq's expressive inductive definitions let types themselves encode and enforce deep program invariants. : [[Dependent-Types-for-Program-Correctness|Link1]], [[Reasoning-About-Equality-Proofs|Link2]], [[The-Coq-Proof-Assistant-and-Certified-Programming|Link3]], [[The-Curry-Howard-Correspondence|Link4]]

**Key Definitions & Concepts by Section:**
- **8.1 Length-Indexed Lists** — `ilist : nat -> Set` indexed by length; breaking the phase distinction between compile-time and run-time data as the hallmark of true dependent typing; `in`/`return`/`as` match annotations for expressing how a match's result type depends on the discriminee's value (`return`) and the discriminee's type-family arguments (`in`); the restriction that `in`-clause positions must be variables, tied to the undecidability of higher-order unification; the match-with-a-match-typed-return-annotation idiom used to write `hd` for non-empty length-indexed lists safely.
- **8.2 The One Rule of Dependent Pattern Matching in Coq** — the single mechanical typing rule for dependent matches (a match's body must have the return-clause type with the discriminee and type-family indices substituted appropriately); parameters versus regular arguments of inductive families (parameters get wildcards in `in` clauses, cannot be matched on); the practical heuristic that a useful `return` clause must mention variables bound by `in`/`as`. : [[Dependent-Types-for-Program-Correctness|Link]]
- **8.3 A Tagless Interpreter** — an indexed expression type `exp : type -> Set` encoding typing rules directly in syntax; `typeDenote`/`expDenote` compiling object-language types/expressions to native Coq types/values via type-level computation; notation scopes for disambiguating overloaded notations; a precursor to the convoy pattern (`pairOutType`/`pairOut`) for extracting components of a dependently typed pair when direct `in`-clause matching is impossible; constant folding (`cfold`) and its correctness proof, which requires the `dep_destruct` tactic (built on `dependent destruction`) to perform case analysis on dependently typed terms that plain `destruct` cannot handle.
- **8.4 Dependently Typed Red-Black Trees** — `rbtree : color -> nat -> Set` indexed by root color and black depth, statically enforcing the red-black invariants; balance proofs requiring induction-hypothesis strengthening via an auxiliary lemma split on root color; the convoy pattern proper — encoding a match's result as a function over free variables whose types need refinement, so a `return` clause can express the needed type connection between sibling subtrees; `rtree` (a tree with one potentially invalid top-level red node) and `sigT` (a dependent pair of a value and a non-propositional dependently typed payload) used to type the rebalancing operations and insertion; extraction to OCaml requiring `Obj.magic` unsafe casts because OCaml's simpler type system cannot express insert's dependently typed return. : [[Dependent-Types-for-Program-Correctness|Link]]
- **8.5 A Certified Regular Expression Matcher** — the `star` inductive predicate formalizing Kleene-star semantics over strings; an indexed `regexp : (string -> Prop) -> Type` (needing `Type`, not `Set`, because of Coq's restriction against "large" non-propositional inductive types quantifying over `Type`-level indices) encoding regex syntax together with the language it denotes; helper decision procedures implementing certified linear search over string splittings; the final certified matcher returning a sumbool-typed answer. : [[Dependent-Types-for-Program-Correctness|Link]]

**Key Questions:**
1. What exactly is "the one rule of dependent pattern matching" in Coq, and why does understanding it dispel the impression that Coq's type checker performs open-ended reasoning about programmer intent?
2. How does the convoy pattern let a function refine the type of a variable already in scope, given that Coq's `match` annotations can only describe dependencies on the discriminee itself?
3. Why do the dependently typed red-black tree operations guarantee balance "for free" through their types alone, and what does the necessary use of `Obj.magic` during OCaml extraction reveal about the gap between Coq's and OCaml's type systems?

---

### Chapter 9: Dependent Data Structures (pp. 165–184)

**Summary:** Returning to length-indexed and heterogeneous lists in more depth, this chapter surveys three competing encoding strategies for dependent data structures — ordinary indexed inductive types, recursively defined ("type-level computation") types, and reflexive (function-indexed) encodings — using a lambda-calculus interpreter and a variable-arity conditional-expression optimizer as running examples, and closes by comparing the strategies' tradeoffs. : [[Dependent-Types-for-Program-Correctness|Link]]

**Key Definitions & Concepts by Section:**
- **9.1 More Length-Indexed Lists** — revisiting `ilist`; the `fin n` type family (isomorphic to `{m : nat | m < n}`) for statically bounded indices, with constructors `First`/`Next`; the fully worked derivation of a certified `get` function via nested convoy-pattern matches on both the index and the list, needed because the termination checker cannot otherwise see that a recursive call's implicit argument is unchanged; `imap` and the `get_imap` "distributes over" theorem, provable with the `dep_destruct` tactic.
- **9.2 Heterogeneous Lists** — `hlist : list A -> Type` parameterized by an index type and an index-indexed type family, storing elements of differing types; the `member` type family (an index-carrying analogue of list membership, defined in `Type` rather than `Prop` so it can be computationally decomposed); `hget` built with a two-element convoy binding both the head value and the recursive selector. : [[Dependent-Types-for-Program-Correctness|Link]]
  - **9.2.1 A Lambda Calculus Interpreter** — a simply typed lambda calculus encoded via de Bruijn indices as `member` values; `exp ts t` (expressions typed `t` with free-variable types `ts`); `typeDenote`/`expDenote` giving a complete syntax, typing, and evaluation semantics with zero proof obligations, deriving type safety "for free" from Coq's own metatheory (CIC) rather than by separate proof.
- **9.3 Recursive Type Definitions** — a type-level-computation alternative: `filist`/`ffin`/`fget` defined by recursion on `nat` rather than as separate inductive families, needing only automatically inferred match annotations; the analogous `fhlist`/`fmember`/`fhget` for heterogeneous lists, using a sum type for `fmember` and pattern-matching on an `eq_refl` proof to license type-correct projection. : [[Inductive-Predicates-and-Judgments|Link1]], [[Inductive-Types|Link2]]
- **9.4 Data Structures as Index Functions** — variable-arity branching trees and the problem of too-weak auto-generated induction principles for nested inductive types; the failed attempt to use a recursively defined `filist` inside such a tree (rejected for non-strict-positivity); the reflexive encoding solution representing children as a function from indices to subtrees; generic folds; the resulting ability to prove properties directly via ordinary induction once the reflexive encoding is adopted, and the general advantage that reflexive encodings often admit direct, non-recursive implementations of operations.
  - **9.4.1 Another Interpreter Example** — a variable-arity `Cond` (Scheme `cond`-like) construct encoded reflexively; a helper function implementing the semantics; a constant-folding optimizer and its correctness lemma, together with an extensionality lemma proved by hand (since general function extensionality is unprovable in Coq) used to prove overall correctness.
- **9.5 Choosing Between Representations** — a comparative summary: ordinary inductive types are most pleasant once helper lemmas/match annotations exist and integrate best with Coq's tactics; recursive type-level-computation types require less initial effort but interact poorly with `simpl`/proof automation and only apply when an index fully determines a value's skeleton; reflexive function-indexed encodings are rare and can produce hard-to-read code but avoid the need for hand-written induction principles and sometimes enable direct implementations.

**Key Questions:**
1. Why does the lambda-calculus interpreter built with `hlist`/`member`/de Bruijn indices achieve type safety "for free," without a single line of proof, and what does that reveal about the relationship between deep embeddings and CIC's own metatheoretic guarantees?
2. Why does the naive variable-arity tree definition (using `ilist` of children) yield an unusably weak automatically generated induction principle, and how does re-encoding children as a function of a bounded index (a reflexive encoding) fix this?
3. What are the concrete costs and benefits of choosing recursive type-level-computation definitions over ordinary inductive definitions for the same data structure?

---

### Chapter 10: Reasoning About Equality Proofs (pp. 185–206)

**Summary:** This chapter surveys Coq's multiple notions of equality (definitional, propositional, heterogeneous) and the recurring difficulties of manipulating equality proofs as data inside dependently typed programs, presenting design patterns (generalization, JMeq, UIP-based axioms) for circumventing "second-order unification" failures. : [[Reasoning-About-Equality-Proofs|Link]]

**Key Definitions & Concepts by Section:**
- **10.1 The Definitional Equality** — Coq's untyped definitional equality underlying CIC typing (allows concluding $E : T$ from $E : T'$ plus a proof that $T$ and $T'$ are definitionally equal); reduction rules named by Greek letters: alpha (bound-variable renaming, handled via de Bruijn representation), beta (function application), delta (unfolding global definitions), iota (simplifying a match), zeta (replacing a `let` by its body); the `cbv`/`lazy` tactics for controlled reduction and `compute` for full reduction; recursive-argument/`struct` annotations and why beta-reduction of a `fix` is blocked until the recursive argument's top-level structure is known; propositional equality (`eq`) as a reification of definitional equality into a proposition, contrasted with axiomatic first-order equality. : [[Reasoning-About-Equality-Proofs|Link]]
- **10.2 Heterogeneous Lists Revisited** — revisits `fhlist`/`fmember` from Chapter 9; the "cannot solve a second-order unification problem" error from `destruct` on a dependent equality hypothesis; using `case` in place of `destruct` for single-constructor types; `UIP_refl` (unicity of identity proofs) from the `Eqdep` module; the axiom `eq_rect_eq` (matches on proofs of $p = p$ are superfluous) as the underlying unprovable assumption; Streicher's axiom K as an equivalent, more well-known formulation; `Eqdep_dec` derives `UIP_refl` without axioms for types with decidable equality. : [[Dependent-Types-for-Program-Correctness|Link]]
- **10.3 Type-Casts in Theorem Statements** — Coq's equality is intensional, so type-level facts (e.g. list-append associativity) must be threaded explicitly as equality proofs inside theorem statements rather than applied silently by the type checker; proof techniques of `injection`, `generalize` (turning concrete subterms/proofs into variables so dependent match construction succeeds), and rewriting with a structural lemma before applying `UIP_refl`, since `UIP_refl` only applies when an equality's two sides are syntactically equal. : [[Reasoning-About-Equality-Proofs|Link]]
- **10.4 Heterogeneous Equality** — `JMeq` ("John Major equality," coined by Conor McBride): an equality predicate relating terms of possibly different types, definitionally `JMeq_refl : JMeq x x`; notation `==`; the axiom `JMeq_eq` (heterogeneous equality implies homogeneous equality when types agree), not provable in CIC though consistent; using JMeq to state theorems that would otherwise fail to type-check; limits of JMeq — `rewrite` under JMeq still needs goals rearranged into polymorphic form, and non-polymorphic functions block this, pushing proofs back toward axiom use. : [[Reasoning-About-Equality-Proofs|Link]]
- **10.5 Equivalence of Equality Axioms** — the major Coq equality axioms (`UIP_refl`/axiom K and `JMeq_eq`) are logically inter-derivable, so asserting one is as strong as any other; a note on the inconsistency risk of combining unrelated axioms even when each is individually consistent. : [[Reasoning-About-Equality-Proofs|Link]]
- **10.6 Equality of Functions** — function extensionality ($(\forall x, f\,x = g\,x) \to f = g$) is not derivable in CIC and must be assumed as an axiom from the standard library (consistent with CIC and other equality axioms); used together with `change` to prove equality "under quantifiers"; no way to derive this axiom even for decidable-equality types, motivating alternate representations where extensionality is provable. : [[Reasoning-About-Equality-Proofs|Link]]

**Key Questions:**
1. Why does Coq's intensional equality force programmers to thread explicit type-cast/equality proofs through theorem statements, rather than letting the type checker silently apply known equalities like list-append associativity?
2. What is the difference between `UIP_refl`/axiom K and `JMeq_eq`, and in what sense are all of Coq's major equality axioms "equivalent" even though they look superficially different?
3. Why does introducing `JMeq` sometimes still fail to make a proof "free," and what property of a function determines whether `rewrite` under JMeq needs to fall back on the `JMeq_eq` axiom?

---

### Chapter 11: Generic Programming (pp. 207–222)

**Summary:** The chapter shows how to do datatype-generic programming and generic proof in Coq without extra language support, by reifying inductive datatype definitions as first-class data (a "universe type" of constructors) and writing recursion schemes and metatheorems that are parameterized over any datatype satisfying suitable well-formedness evidence. : [[Datatype-Generic-Programming|Link]]

**Key Definitions & Concepts by Section:**
- **11.1 Reifying Datatype Definitions** — "universe types" (not to be confused with CIC universes, covered next chapter): syntactic representations of Coq types enabling case analysis on reified type descriptions rather than on types directly; a `constructor` record encoding a constructor as a non-recursive-argument type plus the arity of same-type recursive arguments; `datatype := list constructor`; example encodings for `Empty_set`, `unit`, `bool`, `nat`, `list`, and a binary tree type; `constructorDenote`, mapping a constructor encoding to a concrete function type; `datatypeDenote` (a heterogeneous list of per-constructor denotations) serving as evidence that a concrete type matches an encoding; reliance on `ilist`/`hlist` from Chapter 8. : [[Datatype-Generic-Programming|Link]]
- **11.2 Recursive Definitions** — `fixDenote`, a reified recursion-scheme type analogous to the automatically generated `T_rect` induction principle; `hmake` (builds an `hlist` from a uniform per-element function) used to build generic functions like a generic size-counting function; demonstration that generic definitions specialize, under Coq's ordinary reduction, to exactly the natural hand-written recursive functions for each example type; use of targeted `cbv` flags to inspect specialized definitions without over-reducing. : [[Inductive-Predicates-and-Judgments|Link]]
  - **11.2.1 Pretty-Printing** — a `print_constructor` record pairing a constructor name with a renderer for its non-recursive data; `hmap` (heterogeneous-list-preserving map) used to build a generic `print` function.
  - **11.2.2 Mapping** — a generic `map` analogous to `List.map`, built by composing `fixDenote` with `hmap`; illustrates specialization across the example types, including an example showing the mapping is applied at every level of the inductive structure, including the base constructor.
- **11.3 Proving Theorems about Recursive Definitions** — `datatypeDenoteOk`: a well-formedness condition asserting the reified evidence supports genuine structural induction; `fixDenoteOk`: a well-formedness condition asserting a recursion scheme behaves correctly on any constructor application; a proof that a generic size function is always positive, via `pattern`+`apply` to invoke the encoded induction principle, since ordinary `induction` cannot see that a generic type is inductively defined; a proof that generic `map` applied to the identity function is itself the identity, using `f_equal` and an inner induction over the `hlist` of recursive results combined with the outer induction hypothesis. : [[Engineering-Large-Proof-Developments|Link]]

**Key Questions:**
1. What problem does reifying a datatype's constructors as a first-class `datatype`/`constructor` encoding solve that ordinary Coq inductive definitions and pattern matching cannot, and why is a heterogeneous list the natural representation for "evidence" that a concrete type matches an encoding?
2. Why can't ordinary `induction` be used directly to prove properties about a generically defined function, and what role do `datatypeDenoteOk` and `pattern` play in supplying a substitute induction principle?
3. In the generic-map-identity proof, why is an inner induction over the heterogeneous list of recursive call results needed in addition to the outer structural induction hypothesis?

---

### Chapter 12: Universes and Axioms (pp. 223–251)

**Summary:** This chapter exposes the subtleties of CIC's underlying logic that normally stay hidden — the stratified `Type` universe hierarchy and predicativity that keep Gallina consistent, the special status of `Prop` (elimination restriction, extraction erasure, impredicativity) that separates proofs from programs, and the practice of extending Gallina with axioms (excluded middle, proof irrelevance, functional extensionality, choice) along with the costs axioms impose on computation and trust. : [[Universes-and-Axioms|Link]]

**Key Definitions & Concepts by Section:**
- **12.1 The Type Hierarchy** — every Gallina term has a type, up to `Set : Type` and `Type : Type` at higher levels; the paradox of an unstratified `Type : Type` (Girard's paradox) is avoided by an infinite hierarchy $\text{Type}_0, \text{Type}_1, \text{Type}_2, \ldots$ with implicit universe variables and subtyping; `Set Printing Universes` reveals hidden universe annotations and constraints; the rule that the universe of $\forall x : T_1, T_2$ is the max of $T_1$'s and $T_2$'s universes; predicativity (quantifiers may never be instantiated with the very object being defined, avoiding Russell's-paradox-style inconsistency); universe inconsistency errors as symptoms of predicativity being enforced via a background constraint-solving system over universe variables.
  - **12.1.1 Inductive Definitions** — "large" inductive types (a constructor argument's type has type `Type`) must themselves live in `Type`, not `Set`; parameters (shared by all constructors) versus indices (can vary per constructor) — parameterized types induce only less-than-or-equal universe constraints and thus support more flexible nesting than index-based analogues, which induce strict less-than constraints and can trigger universe inconsistency; Coq's automatic-cloning polymorphism, silently specializing an inductive definition's `Type` occurrences to `Set` or `Prop` depending on use context. : [[Universes-and-Axioms|Link]]
  - **12.1.2 Deciphering Baffling Messages About Inability to Unify** — `Set Printing All` reveals implicit-argument/notation-hidden unification failures; unification-variable scoping: a metavariable's eventual instantiation may not mention variables introduced after it, illustrated via a failed-then-fixed proof.
- **12.2 The Prop Universe** — contrasts `sig` (a Type-valued Curry–Howard existential, a "program") with `ex` (a Prop-valued existential, a "proof"); the elimination restriction: pattern-matching on a `Prop`-sorted discriminee is forbidden when the match's result type is not also in `Prop`, enforcing an information-flow boundary between proofs and programs; extraction erases `Prop`-typed values entirely while preserving `Set`/`Type` program content, making Prop-based proof irrelevant to runtime cost; impredicativity of `Prop` — unlike `Type`/`Set`, a `Prop` may quantify over `Prop` (including itself) without moving to a higher universe, essential for stating propositional tautologies, and combined with the elimination restriction to remain consistent. : [[Universes-and-Axioms|Link]]
- **12.3 Axioms** — an `Axiom`/`Parameter` asserts a proposition or object without proof; risk of inconsistent axiom sets (any set implying `False` makes every theorem provable); `Print Assumptions` to audit which axioms a theorem depends on.
  - **12.3.1 The Basics** — the law of the excluded middle, not provable in Coq's default constructive logic but consistent to assume, safe specifically because the Prop elimination restriction blocks such proofs from being executed as programs; proof irrelevance and its corollaries `UIP_refl`/`UIP` derivable from `eq_rect_eq`; `Eqdep_dec` derives UIP without axioms for decidable-equality types; functional extensionality and its `predicate_extensionality` corollary, likewise unprovable in bare CIC but consistent to assume.
  - **12.3.2 Axioms of Choice** — `constructive_definite_description`, an axiom-free choice-like operator for countable sets via brute-force enumeration guarded by a uniqueness proof; `dependent_unique_choice` and `choice`, stronger axioms converting relational specifications into functions; observes that in Coq's constructive setting these "axioms" are often trivial repackagings unless combined with excluded middle; the `-impredicative-set` flag and the elimination restriction it requires to avoid inconsistency.
  - **12.3.3 Axioms and Computation** — axioms block computational reduction: casting a value with an axiom-derived equality proof leaves `Eval compute` stuck on an opaque match over the proof, whereas a `Defined`-terminated, tactic/structural equality proof allows the cast to reduce normally. : [[Universes-and-Axioms|Link]]
  - **12.3.4 Methods for Avoiding Axioms** — motivations for minimizing axiom use: preserving computational behavior and reducing the trusted base; techniques: unfolding an opaque function definition instead of invoking proof irrelevance; refactoring a dependent case-analysis goal via the convoy pattern so all matched terms have variable-typed indices; and redefining a function so that necessary properties hold by construction on a rebuilt value rather than via an externally supplied, opaque equality proof. : [[Universes-and-Axioms|Link]]

**Key Questions:**
1. Why must `Prop` be impredicative while `Set`/`Type` are predicative, and how does the elimination restriction on `Prop` prevent that impredicativity from reintroducing Girard's/Russell's-style paradoxes?
2. Why is it "safe" to assume classical axioms like excluded middle or proof irrelevance in Coq even though they are unprovable and non-constructive, and what specific mechanism makes them harmless to a program's runtime behavior?
3. Why does an axiom-based equality proof cause `Eval compute` to get "stuck," and what two general strategies let a development avoid or work around this?

---

### Chapter 13: Proof Search by Logic Programming (pp. 253–271)

**Summary:** This chapter introduces logic programming as a paradigm for automated proof search in Coq, showing how the `auto`/`eauto` tactics perform Prolog-style backtracking search over registered hint databases, and how inductive relations (rather than functions) let a "logic program" be run in multiple directions to synthesize values or even whole programs. : [[Proof-Automation-by-Logic-Programming|Link]]

**Key Definitions & Concepts by Section:**
- **13.1 Introducing Logic Programming** — relational versus functional definitions of a function (e.g. `plusR` as an inductive relation mirroring `plus`); `auto`/`auto n` (bounded-depth exhaustive proof-tree search over hint constructors, default depth 5); `info auto`/`debug eauto` (trace of found proof steps); backtracking and unification as the two key logic-programming mechanisms; `apply` versus `eapply` (the latter introduces unification variables for undetermined arguments, deferring their instantiation); `Hint Constructors`, `Hint Immediate`, `Hint Resolve`; named hint databases to segregate expensive hints and avoid exponential blowups from unrestricted transitivity. : [[Proof-Automation-by-Logic-Programming|Link]]
- **13.2 Searching for Underconstrained Values** — using `eauto` to find witnesses for existentials by treating a function's defining lemmas as hints; the problem of non-instantiated existential variables left over when a proof succeeds without pinning down all unification variables; `Show Proof` to inspect partial proof terms with unresolved variables; `Hint Extern` (a custom hint: a goal pattern plus a tactic to try, with an explicit priority number determining search order).
- **13.3 Synthesizing Programs** — using inductive `eval` relations for a toy expression language plus staged/alternate constructor lemmas to let `eauto` synthesize an expression matching a target semantics, not merely verify one; program synthesis as the "run backwards" analog of executing a relation.
- **13.4 More on auto Hints** — full taxonomy of hint kinds (`Hint Immediate`, `Resolve`, `Constructors`, `Unfold`, and the general primitive `Extern`) and how `crush` derives its extensibility from a default hint database; `Hint Extern` with embedded `match goal` for goals plain `auto`/hints alone cannot dispatch; the restriction that the head symbol of an `Extern` pattern must be statically determinable.
- **13.5 Rewrite Hints** — `Hint Rewrite` (adds to the default `core` autorewrite database) versus `autorewrite with db` (requires an explicit database); nontermination and "garden path" rewriting risks when hint rewrite rules interact unexpectedly, unlike `auto`, which never un-solves a goal; `Hint Rewrite ... using tac` to attach a side-condition-discharging tactic to a conditional rewrite; `autorewrite with db in *` for rewriting hypotheses too. : [[Proof-Automation-by-Logic-Programming|Link]]

**Key Questions:**
1. Why does expressing a computation as an inductive relation, rather than a function, make it usable for logic-programming-style search in both directions, and why can't a plain functional definition support this as directly?
2. What is the difference in guarantees between `auto` and `eauto`/`autorewrite` regarding whether adding a new hint can ever break a previously working proof, and why does this distinction matter for maintaining large hint databases?
3. Why must the head symbol of a `Hint Extern` pattern be statically determinable, and what does this imply about how Coq's `auto` hint database is internally organized?

---

### Chapter 14: Proof Search in Ltac (pp. 272–296)

**Summary:** This chapter gives a bottom-up tour of Ltac, Coq's tactic-scripting language, focusing on the `match goal` construct's unusual backtracking pattern-matching semantics, Ltac's dual nature as a functional language whose values can be first-class tactic scripts, and techniques (continuation-passing style, explicit unification-variable allocation) for writing custom recursive/forward-reasoning proof-search procedures. : [[Proof-Automation-by-Logic-Programming|Link1]], [[The-Ltac-Tactic-Language|Link2]]

**Key Definitions & Concepts by Section:**
- **14.1 Some Built-In Automation Tactics** — overview of `intuition`, `congruence` (equality/congruence-closure plus constructor disjointness), `omega` (decision procedure for quantifier-free linear/Presburger arithmetic), `ring`/`field` (algebraic simplification for (semi)rings/fields), `fourier` (real-number inequalities), and the setoid facility for registering custom equivalence relations usable by `rewrite`.
- **14.2 Ltac Programming Basics** — `match goal` for finding case-analysis targets; `context[...]` patterns for matching subterms anywhere in a goal; tacticals like `repeat` and their danger with always-succeeding tactics; the critical semantic difference from ML pattern matching: `match goal` backtracks into later patterns (or different bindings of the same pattern) when the chosen branch's tactic body fails, rather than propagating the failure; `fail n` for failing past n levels of enclosing backtracking; the `first [t1 | t2 | ...]` tactical; the subtlety that Ltac unification variables cannot be bound to terms containing locally bound variables, which silently changes matching behavior between wildcard and named patterns. : [[Datatype-Generic-Programming|Link]]
- **14.3 Functional Programming in Ltac** — Ltac as an untyped, Lisp-like functional language with imperative tactic scripts as one first-class "datatype"; syntactic conventions: pattern variables need `?` prefixes, and Gallina terms must be built via the `constr:(...)` escape; `let ... := ... in` for naming intermediate values; anonymous Ltac functions; why naive attempts to mix imperative tactic sequencing with functional value-returning code produce dynamic type errors, and the fix via continuation-passing style; an analogy (and disanalogy) with Haskell's IO monad — Ltac's mutable state is purely local and fully undone on backtracking. : [[The-Ltac-Tactic-Language|Link1]], [[Proof-Automation-by-Logic-Programming|Link2]]
- **14.4 Recursive Proof Search** — a bounded-chain-length instantiation-search tactic for first-order quantifiers, illustrating how a failing recursive call inside `match goal` triggers renewed search for alternate unifications; a from-scratch implication-simplification "matcher" tactic inspired by separation-logic resource cancellation, using associativity/commutativity lemmas to bring arbitrary conjuncts to the head of a goal, the `||` orelse tactical, and `progress` to detect a no-op tactic application. : [[The-Ltac-Tactic-Language|Link]]
- **14.5 Creating Unification Variables** — `evar (x : T)` to allocate a fresh unification variable; tactics for instantiating a universally quantified hypothesis with placeholders for later unification (forward reasoning, dual to `eauto`'s backward reasoning); special-casing `Prop`-sorted quantifiers (treated as proof obligations dispatched by a user tactic) versus data-sorted ones; `instantiate (n := term)` for naming and assigning a specific existential variable; the `equate` tactic (asserting equality purely for its unification side effect) as a more robust alternative to brittle `instantiate` calls. : [[The-Ltac-Tactic-Language|Link1]], [[Universes-and-Axioms|Link2]]

**Key Questions:**
1. How does Ltac's `match goal` differ from ML-style pattern matching in its treatment of a matched branch's failure, and why is this behavior essential to implementing backtracking search procedures?
2. Why does mixing debug-printing into a function meant to return a Gallina term cause a dynamic type error, and what does the continuation-passing-style rewrite reveal about Ltac's dual functional/imperative nature?
3. Why does a naive instantiation tactic (matching any $\forall x : T, \ldots$) go wrong on hypotheses whose quantified variable is actually a proof obligation, and how does distinguishing `Prop`-sorted from other quantifiers fix it?

---

### Chapter 15: Proof by Reflection (pp. 297–316)

**Summary:** This chapter presents proof by reflection — writing verified Gallina decision procedures and reifying goal syntax into inductive datatypes so that Coq can discharge whole classes of theorems by computation rather than by explicit application of inference rules, yielding proof terms of constant or linear size instead of the superlinear/quadratic blow-up typical of pure-Ltac or built-in tactics like `tauto`. : [[Proof-by-Reflection|Link]]

**Key Definitions & Concepts by Section (flat, no deep subsections beyond top level):**
- **15.1 Proving Evenness** — contrasts a naive `repeat constructor`-based Ltac evenness prover (proof term size superlinear in the input) with a reflective version: a `partial P` type (`Proved`/`Uncertain`), a certified decision procedure `check_even` (dependently typed so it can never return a positive answer for odd inputs), and a function that extracts a proof from a positive case via a dependent match, giving constant-size-overhead proofs; reflection denotes translating a Gallina `Prop` into syntax the program can analyze, and translating back.
- **15.2 Reifying the Syntax of a Trivial Tautology Language** — reification of `Prop` connectives ($\text{True}, \land, \lor, \rightarrow$) into an inductive syntax type `taut`; a denotation function `tautDenote`; a universal correctness theorem `tautTrue`; an Ltac reification function; assembling a reflective tactic that reifies the goal and applies `tautTrue` directly, versus `tauto`'s explicit natural-deduction proof term.
- **15.3 A Monoid Expression Simplifier** — injecting uninterpreted subterms via a `Var` "catch-all" constructor, enabling reflection over goals that mix recognized structure (monoid `+`/identity) with opaque atoms; normalizing expressions to lists via associativity for canonical-form comparison; a `monoid` tactic using `change` to swap the goal for its reified form, closing with `reflexivity` on the canonicalized sides; this pattern underlies Coq's built-in `ring`/`field` tactics.
- **15.4 A Smarter Tautology Solver** — extending reflection to full propositional logic with injected atomic formulas that must support equality comparison, via the `quote` tactic/library and its `index`/`varmap` types; dependently typed deconstruction functions implementing a real, verified tautology-checking decision procedure, contrasted with `tauto`'s proof-term blow-up. **15.4.1 Manual Reification of Terms with Variables** reimplements `quote`'s reification purely in Ltac, representing variables as list positions via nested-tuple encoded lists.
- **15.5 Building a Reification Tactic that Recurses Under Binders** — the challenge of reifying terms containing binders where subterms reference different free-variable sets; the special Ltac pattern form `@?X` (allows a matched metavariable to depend on explicitly listed newly introduced local variables, unlike a plain `?X`); a dependently typed term language using Coq functions (HOAS-style) to represent object-language binding; a working reification tactic that treats every subterm as a function of the free variables collected so far, growing a product type to track them. : [[Proof-by-Reflection|Link]]

**Key Questions:**
1. Why does a proof by reflection have a proof-term size that doesn't grow superlinearly with the size or repetition in the goal, in contrast to a Ltac tactic like `repeat constructor` or the built-in `tauto`?
2. What problem does introducing a `Var`/`Atomic` catch-all constructor solve for reflection, and why is genuine equality comparison between injected atomic subterms necessary for a tautology solver but not for the simpler `taut` language of Section 15.2?
3. Why does a naive reification tactic that matches a lambda term fail to correctly handle the bound variable, and how does the `@?X` pattern form paired with a growing product type of free variables solve this?

---

### Chapter 16: Proving in the Large (pp. 318–339)

**Summary:** This chapter distills practical lessons for structuring and maintaining large Coq developments, arguing that fully automated, single-tactic proofs are far more robust and maintainable than manual step-by-step proof scripts, and covers Coq's module system and multi-file build processes for scaling projects.

**Key Definitions & Concepts by Section:**
- **16.1 Ltac Anti-Patterns** — manual/unstructured proof scripts (brittle to renaming of auto-generated hypotheses); intro patterns for controlling generated names; the danger of `trivial` silently doing nothing and shifting subsequent tactics onto the wrong subgoal; single-tactic ("fully automated") proofs built via `;` sequencing as the book's preferred style, contrasted with per-case bulleted scripts; hint lemmas as a way to name and isolate the "big idea" of a proof step; declarative proof style (Isar) as a competing philosophy favoring explicit subgoal/name structure over adaptive automation; the claim that proof automation and program synthesis differ because proof correctness has a trivial checkable criterion while program correctness criteria are rarely exhaustive. : [[Engineering-Large-Proof-Developments|Link]]
- **16.2 Debugging and Maintaining Automation** — recommended workflow of writing exploratory/manual proofs first, then refining into automated Ltac tactics via `match goal` patterns and `dep destruct`; `Debug On` and its limited practical usefulness; the `info` command for viewing which primitive tactics an automation invocation actually executed, used to localize a bad `Hint Rewrite`; performance regressions from adding transitivity-style hints that blow up `eauto`'s search space, diagnosed with `debug eauto`; caution around `Require Import` silently importing hint databases; the `abstract` tactical for forcing tactic-proof "thunks" early to reduce peak memory use. : [[Engineering-Large-Proof-Developments|Link]]
- **16.3 Modules** — Coq's module system, modeled on ML/OCaml modules and functors; `Module Type` (signatures) capturing algebraic structures, e.g. a `GROUP` signature (carrier set, associative op, left identity, left inverse) and a corresponding theorems signature; functors as functions from modules to modules, proving generic theorems once and applying them to instances (e.g. integers under `+`); opaque ascription versus transparent ascription, and the `with` clause for selectively exposing implementation details; the second-class nature of Coq modules (no runtime computation over module values) as what makes them easier to use than equivalent dependent-record encodings despite adding no fundamental expressiveness.
- **16.4 Build Processes** — organizing a Coq project into multiple `.v` files/libraries; using `coq_makefile` and a project `Makefile` to compile a library, with a flag associating a directory with a logical module path; `Require` (loads a compiled module) versus `Import` (brings a loaded module's names into scope) versus `Load` (verbatim file insertion); aggregating a library's submodules behind one umbrella file; per-project editor configuration, and the `_CoqProject` file for centralizing project settings. : [[Engineering-Large-Proof-Developments|Link]]

**Key Questions:**
1. Why does the author argue that single-tactic, semicolon-composed automated proofs are more maintainable than traditional multi-step, period-terminated proof scripts, even though the latter look more "readable" line by line?
2. What specific problem does the `abstract` tactical solve, and what restriction limits when it can be applied?
3. In what sense do Coq modules add no expressiveness over dependent record types, and why are they nonetheless preferred for large developments?

---

### Chapter 17: A Taste of Reasoning About Programming Language Syntax (pp. 340–358)

**Summary:** As a capstone case study, this chapter formalizes a small simply typed lambda calculus (with naturals) twice — once using dependent de Bruijn indices and once using parametric higher-order abstract syntax (PHOAS) — and compares how each representation choice affects the difficulty of implementing and proving correct three program transformations (identity, constant-folding, and let-removal/substitution). : [[Reasoning-About-Programming-Language-Syntax|Link]]

**Key Definitions & Concepts by Section:**
- **17.1 Dependent de Bruijn Indices** — representing terms as a type family `term` indexed by a typing context, with variables as `member` values (from Chapter 9) rather than raw numbers; a `termDenote` interpreter into Coq values via an `hlist` environment; straightforward transformations (identity, constant-folding) that don't touch binding structure; the harder let-removal transformation, which requires lifting — a de Bruijn "weakening" operation for inserting a new variable into a typing context — plus several correctness lemmas built up before the final soundness theorem; this style is called first-order because it encodes variable identity explicitly, incurring bookkeeping overhead for any transformation that rearranges binding structure. : [[Reasoning-About-Programming-Language-Syntax|Link]]
- **17.2 Parametric Higher-Order Abstract Syntax** — higher-order encodings represent object-language binders using the meta-language's own binders instead of explicit variable identities; naive HOAS (a binder argument of type `term dom -> term ran`) is rejected by Coq's strict positivity restriction; parametric HOAS (PHOAS) fixes this by parameterizing the term type over an abstract `var` family standing for variable representation, with closed terms defined as functions polymorphic in `var`. : [[Reasoning-About-Programming-Language-Syntax|Link]]
  - **17.2.1 Functional Programming with PHOAS** — the core technique of choosing different instantiations of `var` to compute different things (unit for counting variables, string for pretty-printing, `term var` itself for substitution, and a denotation type for the interpreter); shows PHOAS has the same expressive power as first-order encodings while making many operations easier. : [[Proof-Automation-by-Logic-Programming|Link]]
  - **17.2.2 Verifying Program Transformations** — reimplementing the identity, constant-folding, and let-removal transformations in PHOAS; the identity/constant-folding proofs are direct inductions; let-removal's correctness needs a genuinely new proof technique because two instantiations of the same closed term must be related, motivating a well-formedness relation.
  - **17.2.3 Establishing Term Well-Formedness** — the `wf` inductive relation asserting two terms (built over different `var` families) are structurally identical up to a variable-tag isomorphism; a well-formedness condition for closed PHOAS terms, related to parametricity theorems about polymorphic types; proving `wf` is monotone and that let-removal preserves it; discussion of whether `wf` proofs are themselves a form of disguised first-order reasoning.
  - **17.2.4 A Few More Remarks** — custom Coq notations to make PHOAS terms read close to ordinary syntax; PHOAS works well because the toy object language embeds straightforwardly into terminating Gallina, with open research territory in encoding Turing-complete object languages.

**Key Questions:**
1. Why does naive higher-order abstract syntax get rejected by Coq, and how does parameterizing over an abstract `var` family in PHOAS sidestep that restriction?
2. Why is the let-removal/substitution transformation easy for the identity and constant-folding transformations but requires new well-formedness machinery specifically for let-removal in the PHOAS encoding?
3. In what sense do dependent de Bruijn's lifting operation and PHOAS's well-formedness relation play the same role, and which tradeoff does the author say favors PHOAS in practice?

---

### Conclusion (p. 359)

The Conclusion frames the book's two central, unusual techniques — programming with dependent types and proof automation via scripted tactics — as the author's answer to the lack of established practice for keeping large Coq developments maintainable. Chlipala emphasizes that Coq's logical core (CIC) is small even though its practical surface (tactics, libraries, patterns) is vast, and that mastering this surface pays off by making many proofs easier to write and more trustworthy than paper proofs. He closes by urging readers to study the Coq manual for breadth, engage with the Coq community, and, above all, start building something they care about, since the learning process in this domain never ends.
