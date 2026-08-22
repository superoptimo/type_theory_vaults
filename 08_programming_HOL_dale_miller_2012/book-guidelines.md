# Programming with Higher-Order Logic — Guidelines

## Header

**Title:** Programming with Higher-Order Logic
**Author(s):** Dale Miller, Gopalan Nadathur
**Publication:** Cambridge University Press, 2012 (ISBN 978-0-521-87940-8)

**Brief Summary:**
This book develops a proof-theoretic account of logic programming and shows how a simply typed version of higher-order logic — realized as the language $\lambda$Prolog — provides an elegant, declarative foundation for computing over syntactic structures that involve variable binding. It proceeds in four conceptual stages: first-order logic programming foundations (terms, unification, Horn clauses, hereditary Harrop formulas), the generalization of these to higher-order logic (typed $\lambda$-terms, higher-order unification, higher-order Horn clauses and hereditary Harrop formulas), practical language mechanisms for structuring programs (modules), and finally a sequence of applications — encoding proof systems, functional programs, and the $\pi$-calculus — that showcase computing directly on $\lambda$-terms via $\lambda$-tree syntax.

**Intent of the Author:**
The authors aim to show that treating formulas, terms, and proofs as first-class computational objects — organized around Gentzen's sequent calculus rather than resolution or model theory — yields a uniquely well-suited framework for specifying and animating computations over syntax with binding, a problem that is notoriously awkward to handle correctly at the level of ordinary first-order representations.

---

## Topic List

1. **[[Logic-Programming-as-Proof-Search|Logic Programming as Proof Search]]**
   - Computation-as-model versus computation-as-deduction
   - [[The-Simply-Typed-Lambda-Calculus|Proof normalization versus proof search as computational paradigms]]
   - [[Logic-Programming-as-Proof-Search|Sequents as the unit of computational state]]
   - [[Logic-Programming-as-Proof-Search|Goal-directed search and the fixed search semantics of logical connectives]]
   - [[Logic-Programming-as-Proof-Search|Backchaining against program clauses]]
   - The cut rule and Gentzen's cut-elimination theorem
   - [[Logic-Programming-as-Proof-Search|Uniform proofs and abstract logic programming languages]]
   - [[Implementing-Proof-Systems|Focused proof systems]]

2. **[[Typed-First-Order-Terms-and-Type-Structure|Typed First-Order Terms and Type Structure]]**
   - [[Typed-First-Order-Terms-and-Type-Structure|Sorts, type constructors, and kinds]]
   - [[Typed-First-Order-Terms-and-Type-Structure|Type expressions, target and argument types]]
   - [[Typed-First-Order-Terms-and-Type-Structure|The order of a type]]
   - [[Typed-First-Order-Terms-and-Type-Structure|Typed first-order terms and the type assignment calculus]]
   - [[Polymorphic-and-Pervasive-Constants|Polymorphic and pervasive constants]]
   - [[Typed-First-Order-Terms-and-Type-Structure|Parametric versus nonparametric polymorphism]]
   - [[Lambda-Tree-Syntax-and-Computation-over-Binders|Representing structured data with value constructors]]
   - Representing linguistic objects such as formulas and imperative programs
   - Type declarations and operator declarations in $\lambda$Prolog

3. **[[First-Order-Unification|First-Order Unification]]**
   - [[First-Order-Unification|Unification problems as multisets of equations]]
   - [[First-Order-Unification|Most general unifiers and solved form]]
   - [[First-Order-Unification|Rigid terms and the term-reduction, reorientation, and variable-elimination transformations]]
   - The occurs-check and constant clashes
   - [[First-Order-Unification|Unification problems read as quantified formulas]]

4. **[[First-Order-Horn-Clause-Logic-Programming|First-Order Horn Clause Logic Programming]]**
   - The fohc language of definite goals and clauses
   - Signatures, programs, and goals as sequent components
   - [[First-Order-Horn-Clause-Logic-Programming|Right-introduction and left-introduction proof rules]]
   - [[First-Order-Horn-Clause-Logic-Programming|Answer substitutions]]
   - [[First-Order-Horn-Clause-Logic-Programming|Completeness of fohc for classical and intuitionistic logic]]
   - Predicate-indexed clauses and the Warren Abstract Machine
   - [[First-Order-Horn-Clause-Logic-Programming|The operational role of types beyond static well-formedness]]
   - [[First-Order-Unification|Determinate and transparent types]]

5. **[[Hereditary-Harrop-Formulas-and-Modular-Search|Hereditary Harrop Formulas and Modular Search]]**
   - The fohh language admitting implications and universal quantifiers in goals
   - [[Hereditary-Harrop-Formulas-and-Modular-Search|The disjunction and existential property of hereditary Harrop formulas]]
   - [[Logic-Programming-as-Proof-Search|Program and signature augmentation during proof search]]
   - [[Hereditary-Harrop-Formulas-and-Modular-Search|Hypothetical reasoning via implicational goals]]
   - [[Hereditary-Harrop-Formulas-and-Modular-Search|Eigenvariables and the generic reading of universal goals]]
   - [[Hereditary-Harrop-Formulas-and-Modular-Search|Minimal logic, intuitionistic logic, and ex falso quodlibet]]
   - [[Hereditary-Harrop-Formulas-and-Modular-Search|Open-world versus closed-world assumption]]
   - [[Hereditary-Harrop-Formulas-and-Modular-Search|Scope extrusion and the failure of fohh under classical logic]]

6. **[[The-Simply-Typed-Lambda-Calculus|The Simply Typed $\lambda$-Calculus]]**
   - [[The-Simply-Typed-Lambda-Calculus|Abstraction, application, and the type assignment calculus for $\lambda$-terms]]
   - [[The-Simply-Typed-Lambda-Calculus|$\alpha$-, $\beta$-, and $\eta$-conversion]]
   - [[The-Simply-Typed-Lambda-Calculus|$\beta$-normal form and $\lambda$-normal form]]
   - Church numerals and the complexity of $\beta$-normalization
   - [[The-Simply-Typed-Lambda-Calculus|Quantifiers as abstractions over formulas of type $o$]]

7. **[[Higher-Order-Unification|Higher-Order Unification]]**
   - [[First-Order-Unification|Unification problems as quantified equalities with mixed quantifier prefixes]]
   - Raising as the dual of Skolemization
   - Unifiers versus solutions under nonempty-domain assumptions
   - [[Higher-Order-Unification|Rigid and flexible terms, and the classification of equations]]
   - Undecidability via Post correspondence and Hilbert's Tenth Problem
   - [[Higher-Order-Unification|Huet's pre-unification procedure and matching trees]]
   - Imitation and projection substitutions
   - Absence of most general unifiers and of finite complete sets of unifiers
   - The $L_\lambda$ pattern subset and its decidable, unitary unification

8. **[[Higher-Order-Logic-Programming-Languages|Higher-Order Logic Programming Languages]]**
   - hohc, hohh, and hohh$^+$ as higher-order extensions of fohc and fohh
   - [[Higher-Order-Logic-Programming-Languages|Rigid versus flexible atoms and the restriction on clause heads]]
   - The Herbrand universe for higher-order programs
   - Predicate-name hiding via essentially universal clause heads
   - Flexible goals and strategies for handling them
   - [[Higher-Order-Logic-Programming-Languages|Defining logical constants and negation-as-failure within the language]]
   - [[Higher-Order-Logic-Programming-Languages|Functions represented as $\lambda$-terms and functional difference lists]]
   - [[Higher-Order-Logic-Programming-Languages|Limits of higher-order unification as a general-purpose programming tool]]
   - [[Higher-Order-Logic-Programming-Languages|Comparison with higher-order functional programming]]

9. **[[Modular-Program-Structuring|Modular Program Structuring]]**
   - [[Modular-Program-Structuring|Modules and signatures as $\lambda$Prolog's units of structuring]]
   - [[Modular-Program-Structuring|Accumulation of modules and of signatures]]
   - [[Modular-Program-Structuring|Signature elaboration and module well-formedness]]
   - [[Modular-Program-Structuring|E-formulas and existential quantification over program clauses]]
   - Static scoping of hidden constants and the module query interpretation
   - Abstract datatypes and code extensibility through modules
   - Module parametrization by accumulated signatures
   - Resolution of the call/1 ambiguity through logical module semantics

10. **[[Lambda-Tree-Syntax-and-Computation-over-Binders|$\lambda$-Tree Syntax and Computation over Binders]]**
    - [[Lambda-Tree-Syntax-and-Computation-over-Binders|Representing binding structure via second-order constants paired with abstraction]]
    - [[Lambda-Tree-Syntax-and-Computation-over-Binders|Object-level substitution realized as meta-level $\beta$-conversion]]
    - [[Lambda-Tree-Syntax-and-Computation-over-Binders|Mobility of binders across term, formula, and proof level]]
    - Eigenvariable-based recursion under a binder
    - [[Lambda-Tree-Syntax-and-Computation-over-Binders|Higher-order abstract syntax versus $\lambda$-tree syntax]]
    - De Bruijn representations and their translation
    - [[Lambda-Tree-Syntax-and-Computation-over-Binders|Signature-dependent copy clauses for substitution]]
    - The $L_\lambda$ subset as the computational core of $\lambda$-tree syntax programs

11. **[[Implementing-Proof-Systems|Implementing Proof Systems]]**
    - [[Implementing-Proof-Systems|Loop-free reformulation of sequent calculus rules as decision procedures]]
    - [[Implementing-Proof-Systems|Natural deduction proof objects and the # typing-style relation]]
    - Hypothetical judgments and eigenvariable freshness in encoded rules
    - [[Implementing-Proof-Systems|A sequent calculus for classical logic and its zoned sequent structure]]
    - Iterative deepening for completeness under existential instantiation
    - [[Implementing-Proof-Systems|Goals, tactics, and tacticals as a theorem-proving architecture]]
    - [[Logic-Programming-as-Proof-Search|Invertible rules in proof search]]

12. **[[Computing-over-Functional-Programs|Computing over Functional Programs]]**
    - [[Typed-First-Order-Terms-and-Type-Structure|The miniFP language and its type-neutral, then type-restricted, representation]]
    - [[Computing-over-Functional-Programs|Big-step versus evaluation-context (small-step) specifications of evaluation]]
    - Fixpoint evaluation by unfolding
    - [[Computing-over-Functional-Programs|Intensional term equality versus structural program equality]]
    - [[Computing-over-Functional-Programs|Partial evaluation and mixed evaluation under a binder]]
    - [[Computing-over-Functional-Programs|Continuation-passing style transformation and administrative redexes]]

13. **[[Encoding-the-Pi-Calculus|Encoding the $\pi$-Calculus]]**
    - [[Lambda-Tree-Syntax-and-Computation-over-Binders|$\lambda$-tree syntax representation of process syntax and name binding]]
    - Free-action and bound-action one-step transition relations
    - [[Hereditary-Harrop-Formulas-and-Modular-Search|Declarative encoding of freshness and scope-extrusion side conditions]]
    - [[Higher-Order-Unification|Traces and the animation of process behavior]]
    - [[Encoding-the-Pi-Calculus|May-judgments versus must-judgments]]
    - The unsoundness of a naive simulation encoding
    - Encoding the call-by-name $\lambda$-calculus translation into the $\pi$-calculus

14. **[[The-Teyjus-Implementation|The Teyjus Implementation]]**
    - Compiler, emulator, linker, and disassembler toolchain
    - [[The-Teyjus-Implementation|The read-prove-print loop and type inference at the top level]]
    - Realizing the modules language through separate compilation
    - [[The-Teyjus-Implementation|exportdef and useonly module-interface disciplines]]
    - Built-in arithmetic, stream I/O, cut, and negation predicates
    - Deviations from the idealized language, including partial higher-order unification

---

## Chapter Summaries

### Introduction (pp. 1–9)

**Summary:** Surveys the landscape connecting logic and computation, situates the book's proof-search view of logic programming against proof normalization and computation-as-model approaches, disambiguates three senses of "higher-order logic," and lays out the book's four-part organization.

**Key Definitions & Concepts:**
- Computation-as-model (logic used externally to describe computational structures) versus computation-as-deduction (logical expressions directly constitute the computation)
- Proof normalization approach (computation as $\beta$-reduction of a proof term to normal form; basis of functional programming) versus proof search approach (computation as search for a derivation of a sequent; basis of logic programming)
- Sequent $\Sigma; P \longrightarrow G$: a signature $\Sigma$, a program $P$, and a goal $G$
- The cut rule and Gentzen's cut-elimination theorem, and its exclusion from logic-program execution while remaining part of the metatheory
- Goal-directed search: fixed "search semantics" for non-atomic goals versus backchaining against the program for atomic goals
- Three senses of "higher-order logic": second-order logic in the philosophical sense; the proof-theoretic sense (predicate quantification and comprehension); the implementer's sense ($\lambda$-terms and quantification at higher-order types)
- The book's logic: a simplified intuitionistic Simple Theory of Types (Church), omitting extensionality, infinity, and choice, with equality based on $\beta$- and $\eta$-conversion
- The book's four-part dependency structure: first-order foundations (Chapters 1–3), higher-order foundations (Chapters 4–5), the programming system (Chapter 6 and the Appendix), and $\lambda$-terms as data (Chapters 7–11)

**Key Questions:**
1. What distinguishes the proof-search view of computation from the proof-normalization view, and why does the cut rule occupy a special, excluded role in the former?
2. In what sense is the book's higher-order logic higher order in the "implementer's sense" but deliberately not pursued in the full second-order (predicate-quantification-rich) sense for programming purposes?

---

### Chapter 1: First-Order Terms and Representations of Data (pp. 10–33)

**Summary:** Introduces the typed first-order term language of $\lambda$Prolog (sorts, type constructors, kinds, type expressions, terms) and first-order unification as the mechanism for decomposing and constructing data, illustrated through representations of lists, binary trees, logical formulas, and imperative programs.

**Key Definitions & Concepts by Section:**
- **1.1 Sorts and type constructors** — sort (atomic, unanalyzable type, e.g. $\mathtt{int}$, $\mathtt{real}$, $\mathtt{string}$, $\mathtt{o}$ for formulas); type constructor (e.g. $\mathtt{list}$, produces new types from arguments); kind (the "type" of types; $\mathtt{kind\_exp} ::= \mathtt{type} \mid \mathtt{type} \to \mathtt{kind\_exp}$); kind declaration
- **1.2 Type expressions** — type variables versus type constructors; target type and argument types of a type expression; functional versus nonfunctional type; primitive type; the order of a type $\mathrm{ord}(\tau)$, and its potential increase under substitution for type variables
- **1.3 Typed first-order terms** — constant and value constructor; pervasive constants; polymorphic constants; type and operator declarations; term variables; well-formed application; typed first-order term; the type assignment calculus judgment $\Sigma;\Gamma \vdash t:\tau$; most general typing; canonical form of a term, with head and arguments
- **1.4 Representing symbolic objects** — encoding data classes with distinct value constructors sharing a target type; parametric versus nonparametric polymorphism; representing logical formulas (the $\mathtt{var}$ constructor for object-level variables, and the fundamental limitation that first-order encodings of quantifiers cannot capture true binding force); representing imperative programs via type-neutral encodings
- **1.5 Unification of typed first-order terms** — unification problem as a multiset of equations; unifier and most general unifier; solved form; rigid term; the term-reduction, reorientation, and variable-elimination transformations; constant clash; occurs-check; reading unification problems as $\forall\exists$-quantified formulas
- **1.6 Bibliographic notes** — Robinson's, Martelli–Montanari's, and Paterson–Wegman's unification algorithms; $\lambda$Prolog as the first polymorphically typed logic programming language; the LF/Twelf dependently typed alternative

**Key Questions:**
1. Why does $\lambda$Prolog need typed first-order terms rather than untyped Prolog-style terms, and what practical property (parametric polymorphism) does this buy for data representation?
2. Why can first-order term representations of quantified formulas not capture the true binding behavior of a quantifier, and what does this foreshadow about Chapter 7?
3. What is the role of the occurs-check in variable elimination, and why might practical Prolog systems omit it despite the unsoundness this introduces?

---

### Chapter 2: First-Order Horn Clauses (pp. 34–73)

**Summary:** Develops an abstract framework for logic programming — signatures, program clauses, goals, and a sequent calculus with fixed search semantics — then instantiates it as fohc, the logic of first-order Horn clauses, exploring its programming use, its pragmatics, its relationship to classical and intuitionistic provability, and the operational role played by types.

**Key Definitions & Concepts by Section:**
- **2.1 First-order formulas** — relation symbol; first-order atomic formula; logical constants ($\top$, $\wedge$, $\vee$, $\supset$); universal and existential quantification written via the binding operators $\mathtt{pi}$ and $\mathtt{sigma}$; $\alpha$-convertibility of formulas; the typed first-order $\Sigma$-formula judgment
- **2.2 Logic programming and search semantics** — the four ingredients of a logic programming setting (signatures, program clauses, goals, a proof calculus); the sequent $\Sigma;P \longrightarrow G$; reduction rules per connective (AND, OR, INSTAN, AUGMENT, GENERIC, TRUE); definite formulas; answer substitution; fohc as the logic underlying Prolog
- **2.3 Horn clauses and their computational interpretation** — the fohc goal and clause grammars; backchaining and its proof rules (decide, initial, $\supset L$, $\wedge L$, $\forall L$); the flat, global signature-and-program property of fohc
- **2.4 Programming with first-order Horn clauses** — implicit universal quantification of clause variables; modules as named collections of declarations and clauses; the read-prove-print loop; recursive relation definitions and encoding provability relations as fohc programs
- **2.5 Pragmatic aspects of computing with Horn clauses** — the need for a fixed, predictable search strategy for programming transparency; program as an ordered list; logic variables; predicate-indexed clause compilation
- **2.6 The relationship with logical notions** — the cut rule as lemma introduction; cut-elimination for fohc; alternative equivalent presentations of fohc clauses and the exponential blow-up tradeoffs among them
- **2.7 The meaning and use of types** — types as classifying, not evaluating, expressions; transparent and determinate types; type checking versus type inference via unification
- **2.8 Bibliographic notes** — uniform proofs and abstract logic programming languages; focused proof systems; the Warren Abstract Machine

**Key Questions:**
1. What is the precise sense in which goal-directed search fixes a search semantics for logical connectives independently of the program, and how does this differ from how atomic goals are handled via backchaining?
2. Why is fohc complete for both classical and intuitionistic logic, and what design choices in its syntax avoid the completeness problems that unrestricted disjunction would otherwise cause?
3. In what sense do types in $\lambda$Prolog play a role beyond static well-formedness checking, and why does this matter operationally?

---

### Chapter 3: First-Order Hereditary Harrop Formulas (pp. 75–95)

**Summary:** Extends fohc by admitting implications and universal quantifiers inside goal formulas, yielding fohh — a logic in which the program and signature can grow and shrink dynamically during proof search — enabling hypothetical reasoning and local auxiliary clauses, and relates fohh's operational semantics precisely to minimal and intuitionistic (but not classical) provability.

**Key Definitions & Concepts by Section:**
- **3.1 The syntax of goals and program clauses** — the fohh goal and clause grammars admitting $\supset$ and $\forall$ in goals; positive and negative subformula occurrence; the disjunction and existential property characterizing hereditary Harrop formulas; clausal order of a formula
- **3.2 Implicational goals** — the AUGMENT rule and stack-discipline program growth; hypothetical reasoning via implicational goals; risk of nontermination under depth-first search
- **3.3 Universally quantified goals** — the GENERIC rule and eigenvariables; intensional versus extensional readings of universal quantification; capture-avoiding substitution; logic variables occurring inside program clauses
- **3.4 The relationship with logical notions** — logical equivalence versus preserved computational behavior; fohh's soundness and completeness for intuitionistic but not classical logic; scope extrusion and Peirce's formula as a counterexample; minimal logic versus intuitionistic logic; logic program inconsistency; syntactic subsets of fohh
- **3.5 Bibliographic notes** — Harrop formulas versus hereditary Harrop formulas; open-world versus closed-world assumption; Kripke models; the $\nabla$-quantifier for generic quantification under a closed-world assumption

**Key Questions:**
1. Why does allowing implications and universal quantifiers into goal formulas require giving up fohc's flat, global signature-and-program property, and what computational capability does this buy?
2. Why is classical logic unsound for fohh's operational semantics even though it was sound for fohc, and what specific classical equivalence is responsible?
3. What is the difference between the intensional (eigenvariable) and extensional (instance-checking) readings of a universally quantified goal, and why can fohh's GENERIC rule alone not prove universal facts about inductively defined types?

---

### Chapter 4: Typed $\lambda$-Terms and Formulas (pp. 96–117)

**Summary:** Introduces the simply typed $\lambda$-calculus underlying the book's higher-order logic — abstraction, application, the type assignment calculus, and $\alpha$-, $\beta$-, $\eta$-conversion — then reframes unification problems as quantified equality formulas with mixed quantifier prefixes, closing with two undecidability results establishing the expressive power of higher-order unification.

**Key Definitions & Concepts by Section:**
- **4.1 Syntax for $\lambda$-terms and formulas** — abstraction and the type assignment calculus judgment $\Sigma;\Gamma \vdash t:\tau$; well-formed $\Sigma$-term; simply typed $\lambda$-term; formula as a term of type $o$; quantifiers defined via abstraction
- **4.2 The rules of $\lambda$-conversion** — the "free for" substitution proviso; $\alpha$-, $\beta$-, and $\eta$-conversion; $\lambda$-conversion as the logic's notion of equality
- **4.3 Some properties of $\lambda$-conversion** — $\beta$-redex and $\eta$-redex; $\beta$-normal form and $\lambda$-normal form; Church numerals; the potential superexponential blow-up of term size under normalization, and three reasons this is avoided in practice
- **4.4 Unification problems as quantified equalities** — the generalized unification problem with mixed $\forall/\exists$ prefixes; raising as a dual operation to Skolemization; the distinction between a unifier and a solution; the significance of empty types
- **4.5 Solving unification problems** — $\beta$-normal form structure (binder, head, arguments); rigid versus flexible terms; the classification of equations as rigid-rigid, rigid-flexible, and flexible-flexible
- **4.6 Some hard unification problems** — reduction of the Post correspondence problem and of Hilbert's Tenth Problem to higher-order unification, establishing its undecidability
- **4.7 Bibliographic notes** — Church's invention of the $\lambda$-calculus and Simple Theory of Types; Huet's first systematic study of higher-order unification

**Key Questions:**
1. Why is a "solution" to a unification problem a strictly stronger notion than a "unifier" in this higher-order intuitionistic setting?
2. What is raising, how is it dual to Skolemization, and why is it needed to bring a unification problem's quantifier prefix into normal form?
3. What three properties of realistic logic-program unification problems keep $\lambda$-normalization tractable in practice, given that unrestricted $\beta$-reduction can blow up superexponentially?

---

### Chapter 5: Using Quantification at Higher-Order Types (pp. 118–149)

**Summary:** Builds the higher-order logic programming languages hohc, hohh, and hohh$^+$ by extending fohc/fohh's atomic formulas to admit $\lambda$-terms while restricting where flexible atoms and logical symbols may occur, then explores the practical programming power this yields, including reasoning about higher-order programs, defining logical constants, and using $\lambda$-terms as functions.

**Key Definitions & Concepts by Section:**
- **5.1 Atomic formulas in higher-order logic programs** — rigid versus flexible atoms; inconsistent theory; why flexible clause heads are disallowed; polarity of a logical symbol occurrence
- **5.2 Higher-order logic programming languages** — the Herbrand universes for hohc and hohh; hohc and hohh grammars; hohh$^+$ and its liberalized, essentially universally quantified clause heads
- **5.3 Examples of higher-order programming** — predicate-quantified library predicates; continuation-passing-style transformation of Horn programs; hohh$^+$ memoization examples
- **5.4 Flexible atoms as goals** — three strategies for handling flexible goals (suspension, eager solving, run-time error)
- **5.5 Reasoning about higher-order programs** — proving symmetry of a hidden-predicate definition of $\mathtt{reverse}$, requiring metatheoretic reasoning beyond operational semantics
- **5.6 Defining some of the logical constants** — partial, right-introduction-only definitions of $\bot$, $\top$, $\vee$, $\exists$ via hohc clauses
- **5.7 The conditional and negation-as-failure** — cut-based definitions of $\mathtt{if}$ and $\mathtt{not}$, and the logical properties they break
- **5.8 Using $\lambda$-terms as functions** — running "function evaluation" backward via unification; difference lists and functional difference lists
- **5.9 Higher-order unification is not a panacea** — cautionary examples of spurious or redundant solutions, favoring explicit structural recursion instead
- **5.10 Comparison with functional programming** — nonpredicate function variables and directly expressible intensional predicate equality
- **5.11 Bibliographic notes** — Church's Simple Theory of Types; the shared 1987 origin of $\lambda$Prolog and LF/Twelf

**Key Questions:**
1. Why must the head of a program clause be a rigid atom in hohc/hohh, and what concretely goes wrong if flexible clause heads were allowed?
2. What is the practical difference between hohh and hohh$^+$, and how does hohh$^+$'s relaxation enable predicate-name hiding?
3. Why does higher-order unification make a poor general-purpose tool for tasks like constant extraction or term rewriting, and what alternative does the book recommend?

---

### Chapter 6: Mechanisms for Structuring Large Programs (pp. 150–173)

**Summary:** Develops a module system for $\lambda$Prolog entirely from the logical connectives of hohh$^+$, using existential quantification over program clauses to formalize the hiding of local names, and shows the system supports abstract datatypes, code extensibility, parametrization, and principled higher-order predicate visibility.

**Key Definitions & Concepts by Section:**
- **6.1 Desiderata for modular programming** — programming-in-the-small versus programming-in-the-large; representation independence
- **6.2 A modules language** — module and signature declarations; pervasive constants; accumulation of modules and of signatures
- **6.3 Matching signatures and modules** — signature elaboration; mergeable signatures; module well-formedness; implicit signature and matching
- **6.4 The logical interpretation of modules** — E-formulas extending hohh$^+$ syntax; the four-part sequent $\Sigma;P \dashv \Theta \to G$; translation of a module into an E-formula; static scoping via existential quantification; module elaboration as compile-time inlining
- **6.5 Some programming aspects of the modules language** — abstract datatypes; code extensibility across modules; signature accumulation as module parametrization; resolution of the call/1 naming-ambiguity problem
- **6.6 Implementation considerations** — module elaboration versus a separate-compilation, link-time inlining strategy
- **6.7 Bibliographic notes** — algebra-of-composition versus logic-extension approaches to modules; comparison to Standard ML structures and existential types

**Key Questions:**
1. Why does the book define modules and signatures via a translation into E-formulas inside hohh$^+$ rather than as an independent syntactic layer?
2. How does the existential-quantifier-based semantics of modules resolve the classic Prolog call/1 ambiguity between calling context and defining context?
3. What is the difference between accumulating a module and accumulating only its signature, and why is the latter the right choice for a parametrized module?

---

### Chapter 7: Computations over $\lambda$-Terms (pp. 175–210)

**Summary:** Shows how $\lambda$-abstraction can encode syntactic objects with binding structure so that object-level substitution reduces to meta-level $\beta$-conversion, develops the "mobility of binders" idiom for computing under binders, introduces $\lambda$-tree syntax, and identifies the $L_\lambda$ subset of hohh in which only simple $\beta_0$-reduction is needed.

**Key Definitions & Concepts by Section:**
- **7.1 Representing objects with binding structure** — encoding quantifiers and untyped $\lambda$-terms via second-order constants paired with meta-level abstraction, folding $\alpha$-, $\beta$-, and $\eta$-conversion into equality
- **7.2 Realizing object-level substitution** — object-level instantiation via $\beta$-conversion; call-by-name and call-by-value evaluation predicates for untyped $\lambda$-terms
- **7.3 Mobility of binders** — term-level binding moving to formula-level then proof-level binding via eigenvariables; the general hohh idiom for recursing under a binder
- **7.4 Computing with untyped $\lambda$-terms** — $\beta$-normal and $\beta$-body-normal forms; path-based reduction; type inference and the subject-reduction theorem; translation to and from de Bruijn syntax
- **7.5 Computations over first-order formulas** — negation normal form and prenex normal form; recognizing fohc/fohh syntactic classes
- **7.6 Specifying object-level substitution** — substitution via direct $\beta$-reduction versus signature-dependent copy clauses; substitution as a relation, not a function
- **7.7 The $\lambda$-tree approach to abstract syntax** — higher-order abstract syntax versus $\lambda$-tree syntax, and structural analyzability
- **7.8 The $L_\lambda$ subset of $\lambda$Prolog** — essentially universal versus essentially existential variable occurrences; the pattern condition; $\beta_0$-conversion as the only reduction needed
- **7.9 Bibliographic notes** — origins of $\lambda$-tree syntax, higher-order abstract syntax, de Bruijn representations, and nominal logic

**Key Questions:**
1. What does it mean for a term-level binder to become a formula-level then proof-level binder during proof search, and why does this mobility make recursive computation under binders possible?
2. Why is object-level substitution "free" in this framework, and what does the copy-clause-based definition buy over raw $\beta$-reduction?
3. What exactly distinguishes $\lambda$-tree syntax from other forms of higher-order abstract syntax, and why does the distinction matter for structural analysis?

---

### Chapter 8: Unification of $\lambda$-Terms (pp. 211–228)

**Summary:** Studies the algorithmic properties of higher-order unification, showing it is undecidable and admits neither most general unifiers nor finite complete sets of unifiers in general, then develops Huet's pre-unification procedure and shows that restricting to the $L_\lambda$ pattern subset recovers decidability and most general unifiers.

**Key Definitions & Concepts by Section:**
- **8.1 Properties of the higher-order unification problem** — the $\forall\exists\forall$ prefix normal form; absence of most general unifiers; complete sets of unifiers; undecidability of unifiability
- **8.2 A procedure for checking for unifiability** — simplification of rigid-rigid equations; imitation and projection substitutions for flexible-rigid equations; pre-unification; matching trees; potential nontermination
- **8.3 Higher-order pattern unification** — the $L_\lambda$ condition restated as the pattern property; deterministic substitution choice; variable elimination generalized to the pattern case
- **8.4 Pragmatic aspects of higher-order unification** — the cost of dynamic raising and delayed raising as an optimization; dynamic $L_\lambda$ programming
- **8.5 Bibliographic notes** — Huet's dissertation and pre-unification procedure; undecidability results at various orders; identification of higher-order pattern unification and its linear-time algorithm

**Key Questions:**
1. Why can higher-order unification problems fail to have a most general unifier or even a finite complete set of unifiers?
2. What is the difference between imitation and projection substitutions in Huet's procedure, and why does the $L_\lambda$ restriction make the choice between them essentially deterministic?
3. In what sense is higher-order pattern unification computationally similar to first-order unification?

---

### Chapter 9: Implementing Proof Systems (pp. 229–246)

**Summary:** Shows how $\lambda$Prolog can specify and implement proof systems — sequent-calculus decision procedures, natural-deduction proof checkers and provers for intuitionistic logic, a sequent-style prover for classical logic, and a general goals/tactics/tacticals architecture for building controllable theorem provers.

**Key Definitions & Concepts by Section:**
- **9.1 Deduction in propositional intuitionistic logic** — loop-free reformulation of sequent-calculus rules as a decision procedure; the naive-translation nontermination problem
- **9.2 Encoding natural deduction for intuitionistic logic** — proof objects as typed $\lambda$Prolog terms; the # relation encoding hypothetical judgments and eigenvariable freshness
- **9.3 A theorem prover for classical logic** — the four-zone sequent for classical logic in negation normal form; iterative deepening for completeness; pitfalls of combining cut with free logic variables
- **9.4 A general architecture for theorem provers** — primitive versus compound goals; tactics and tacticals; invertible rules
- **9.5 Bibliographic notes** — origins of the sequent calculus and its contraction rule; the # relation as an analogue of LF typing judgments; the LCF tactics/tacticals tradition

**Key Questions:**
1. Why does a direct translation of a sequent calculus into $\lambda$Prolog clauses typically fail to be a complete proof procedure, and what kind of reformulation restores it?
2. How does the # relation encode natural-deduction proof objects and the eigenvariable discipline of rules like $\supset I$, $\vee E$, and $\exists E$?
3. What problem does the goals/tactics/tacticals architecture solve that a direct provability predicate cannot?

---

### Chapter 10: Computations over Functional Programs (pp. 247–260)

**Summary:** Illustrates $\lambda$Prolog's ability to represent and compute over program syntax by defining miniFP, a small typed functional language, giving it contrasting big-step and small-step operational semantics, and showing how the representation supports program transformations including partial evaluation and continuation-passing-style transformation.

**Key Definitions & Concepts by Section:**
- **10.1 The miniFP programming language** — $\lambda$-tree syntax encoding of miniFP; the separate $\mathtt{typeof}$ judgment restricting to well-typed programs
- **10.2 Specifying evaluation for miniFP programs** — big-step versus evaluation-context small-step specifications; fixpoint evaluation by unfolding; the mismatch between raw term equality and structural program equality
- **10.3 Manipulating functional programs** — partial evaluation by unfolding; mixed evaluation under a binder; the continuation-passing-style transformation and administrative redexes
- **10.4 Bibliographic notes** — denotational versus operational semantics traditions; Plotkin's structural operational semantics and Kahn's natural semantics; Fischer's CPS transformation

**Key Questions:**
1. Why must miniFP's term representation first be defined untyped and then constrained by a separate $\mathtt{typeof}$ relation?
2. What is the practical difference between the big-step and evaluation-context specifications of miniFP evaluation?
3. Why does equating miniFP values via raw $\lambda$Prolog term equality overshoot the usual notion of functional-program equality?

---

### Chapter 11: Encoding a Process Calculus Language (pp. 261–275)

**Summary:** Encodes the $\pi$-calculus in $\lambda$Prolog using $\lambda$-tree syntax, showing that its name-binding and scope-extrusion phenomena can be captured through $\lambda$Prolog's binders and generic quantification, develops transition semantics and simulation, and exposes a genuine limitation of logic programming for universally quantified "must" properties.

**Key Definitions & Concepts by Section:**
- **11.1 Representing the expressions of the $\pi$-calculus** — $\lambda$-tree syntax encoding of process syntax using binding constructs for input and restriction
- **11.2 Specifying one-step transitions** — free-action and bound-action transition predicates; declarative encoding of freshness side-conditions via nested quantifiers
- **11.3 Animating $\pi$-calculus expressions** — using the transition predicates as an interpreter; traces
- **11.4 May- versus must-judgments** — the natural expressibility of may-judgments versus the unsoundness of a naive simulation encoding for must-judgments
- **11.5 Mapping the $\lambda$-calculus into the $\pi$-calculus** — a compositional $\lambda$Prolog specification of Milner's call-by-name translation
- **11.6 Bibliographic notes** — origins of the $\pi$-calculus; the $L_\lambda$ fragment and Sangiorgi's $\pi I$ calculus; the $\nabla$ quantifier as a fix for must-judgments

**Key Questions:**
1. How does $\lambda$Prolog's use of nested quantifiers automatically enforce freshness and no-capture side-conditions in the transition rules?
2. Why does the direct logic-programming style naturally support may-judgments but fail to give a sound, declarative account of must-judgments like simulation?
3. In what sense does the $\lambda$-tree syntax encoding of the $\lambda$-calculus-to-$\pi$-calculus translation avoid a separate case for free variables?

---

### Appendix: The Teyjus System (pp. 277–288)

**Summary:** A practical, non-formal introduction to Teyjus, the reference implementation of $\lambda$Prolog used to run the programs presented throughout the book, covering its compilation and execution model, its interactive top level, its realization of the modules language, and its deviations from the idealized language of the main text.

**Key Definitions & Concepts by Section:**
- **A.1 An overview of the Teyjus system** — the virtual-machine-plus-compiler architecture; the toolchain of $\mathtt{tjcc}$, $\mathtt{tjsim}$, $\mathtt{tjlink}$, $\mathtt{tjdis}$, $\mathtt{tjdepend}$
- **A.2 Interacting with the Teyjus system** — the read-prove-print loop; type inference at the top level; the restriction against embedded implications in top-level goals
- **A.3 Using modules within the Teyjus system** — accumulation and the two-stage compile-then-link process; $\mathtt{exportdef}$ and $\mathtt{useonly}$ interface disciplines
- **A.4 Special features of the Teyjus system** — built-in arithmetic, comparison, and stream I/O predicates; the absence of assert/retract; partial (pattern-restricted) higher-order unification as a deviation from the idealized language

**Key Questions:**
1. Why does Teyjus's reliance on pattern unification rather than full higher-order unification mean that some of the book's own illustrative examples cannot be run as-is?
