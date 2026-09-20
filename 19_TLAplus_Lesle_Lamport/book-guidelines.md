# Specifying Systems — Guidelines

## Header

**Title:** Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers
**Author(s):** Leslie Lamport
**Publication:** Addison-Wesley, first printing July 2002 (copyright 2003 by Pearson Education, Inc.)

**Brief Summary:**
This book teaches engineers how to write precise, formal specifications of computer systems using TLA+, a language Lamport built from ordinary first-order logic and set theory plus a minimal temporal logic (TLA) for describing a system's allowed behaviors. It proceeds from a worked-example introduction covering everything most engineers need (Part I), through advanced topics like liveness, real time, and composing specifications (Part II), to reference documentation for the associated tools — the Syntactic Analyzer, the $\text{TLATEX}$ typesetter, and the $\text{TLC}$ model checker (Part III) — and a complete formal semantics of the TLA+ language itself (Part IV).

**Intent of the Author:**
Lamport wants to convince engineers that writing rigorous specifications is both practical and worthwhile, using mathematics they mostly already know rather than a special-purpose formalism resembling a programming language; he expects most readers to need only Part I (the first 83 pages) to become competent at specifying real systems.

---

## Topic List

1. **Elementary Mathematical Foundations for Specification** : [[Elementary-Mathematical-Foundations-for-Specification|Link]]
   - Propositional logic and truth tables : [[Elementary-Mathematical-Foundations-for-Specification|Link]]
   - Set theory primitives and operators : [[Formal-Semantics-of-the-TLA+-Language|Link1]], [[Elementary-Mathematical-Foundations-for-Specification|Link2]]
   - Predicate logic and bounded versus unbounded quantification : [[Elementary-Mathematical-Foundations-for-Specification|Link]]
   - Functions, domains, and function construction : [[Elementary-Mathematical-Foundations-for-Specification|Link]]
   - Records and tuples as functions : [[Elementary-Mathematical-Foundations-for-Specification|Link]]
   - Recursive function definitions : [[Elementary-Mathematical-Foundations-for-Specification|Link]]
   - The choose operator and Hilbert's epsilon : [[Elementary-Mathematical-Foundations-for-Specification|Link1]], [[Formal-Semantics-of-the-TLA+-Language|Link2]]
   - TLA+ as an untyped formalism : [[Elementary-Mathematical-Foundations-for-Specification|Link]]

2. **The Syntax of TLA+** : [[The-Syntax-of-TLA+|Link]]
   - Ascii versus typeset notation : [[The-Syntax-of-TLA+|Link]]
   - The BNF grammar and module structure : [[The-Syntax-of-TLA+|Link]]
   - Lexemes, tokens, and reserved words : [[The-Syntax-of-TLA+|Link]]
   - Operator precedence as a range : [[The-Syntax-of-TLA+|Link]]
   - Aligned conjunction and disjunction lists : [[The-Syntax-of-TLA+|Link]]
   - Comment forms and typesetting conventions : [[The-Syntax-of-TLA+|Link]]
   - Syntactic anomalies in parsing : [[The-Syntax-of-TLA+|Link]]

3. **Formal Semantics of the TLA+ Language** : [[Formal-Semantics-of-the-TLA+-Language|Link]]
   - Meaning of an expression via primitive operators : [[Formal-Semantics-of-the-TLA+-Language|Link]]
   - Interpretations of Boolean operators on non-Boolean values : [[Formal-Semantics-of-the-TLA+-Language|Link]]
   - Arity, order, and level of an operator : [[Formal-Semantics-of-the-TLA+-Language|Link]]
   - Lambda expressions as metalanguage : [[Formal-Semantics-of-the-TLA+-Language|Link]]
   - Contexts and the meaning of a module : [[Formal-Semantics-of-the-TLA+-Language|Link]]
   - Module extension : [[Formal-Semantics-of-the-TLA+-Language|Link]]
   - Instantiation and capture-avoiding substitution : [[Formal-Semantics-of-the-TLA+-Language|Link]]
   - Semantic correctness as formula validity : [[Formal-Semantics-of-the-TLA+-Language|Link]]

4. **States, Actions, and Behaviors** : [[Formal-Semantics-of-the-TLA+-Language|Link1]], [[States-Actions-and-Behaviors|Link2]]
   - States as assignments to variables : [[States-Actions-and-Behaviors|Link]]
   - Actions and next-state relations : [[States-Actions-and-Behaviors|Link]]
   - Stuttering steps and invariance under stuttering : [[States-Actions-and-Behaviors|Link]]
   - Enabling conditions : [[States-Actions-and-Behaviors|Link]]
   - Action composition : [[States-Actions-and-Behaviors|Link]]
   - The grain of atomicity : [[States-Actions-and-Behaviors|Link1]], [[Writing-Specifications-Engineering-Practice|Link2]]

5. **Specifying Safety Properties** : [[Specifying-Safety-Properties|Link]]
   - The canonical specification form : [[Specifying-Safety-Properties|Link]]
   - Type invariants as ordinary invariants : [[Specifying-Safety-Properties|Link]]
   - Inductive invariants versus invariants of a specification : [[Specifying-Safety-Properties|Link]]
   - Initial predicates and next-state actions : [[States-Actions-and-Behaviors|Link1]], [[Advanced-Specification-Examples|Link2]]
   - Silly expressions in an untyped language : [[Specifying-Safety-Properties|Link]]

6. **Temporal Logic and Liveness** : [[Temporal-Logic-and-Liveness|Link]]
   - The always and eventually operators : [[Formal-Semantics-of-the-TLA+-Language|Link]]
   - Temporal tautologies versus temporal proof rules : [[Temporal-Logic-and-Liveness|Link]]
   - The leads-to operator
   - Weak fairness : [[Real-Time-Specification|Link1]], [[Temporal-Logic-and-Liveness|Link2]]
   - Strong fairness : [[Temporal-Logic-and-Liveness|Link]]
   - Machine closure : [[Composing-Specifications|Link1]], [[Real-Time-Specification|Link2]], [[Temporal-Logic-and-Liveness|Link3]]
   - Temporal quantification and hiding : [[Temporal-Logic-and-Liveness|Link]]

7. **Real-Time Specification** : [[Real-Time-Specification|Link]]
   - The now variable : [[Real-Time-Specification|Link]]
   - Real-time bounds on actions : [[Real-Time-Specification|Link]]
   - Zeno specifications : [[Real-Time-Specification|Link]]
   - Hybrid system specifications and differential equations : [[Real-Time-Specification|Link]]

8. **Refinement and Implementation** : [[Refinement-and-Implementation|Link]]
   - Implementation as logical implication : [[Refinement-and-Implementation|Link]]
   - Refinement mappings : [[Refinement-and-Implementation|Link]]
   - Step simulation : [[Refinement-and-Implementation|Link]]
   - Interface refinement : [[Refinement-and-Implementation|Link]]
   - Data refinement : [[Refinement-and-Implementation|Link]]

9. **Composing Specifications** : [[Composing-Specifications|Link]]
   - Interleaving versus noninterleaving composition : [[Composing-Specifications|Link]]
   - Disjoint-state versus shared-state composition : [[Composing-Specifications|Link]]
   - Joint actions : [[Composing-Specifications|Link]]
   - Compositional hiding : [[Composing-Specifications|Link]]
   - Open-system versus closed-system specifications : [[Composing-Specifications|Link]]
   - Rely-guarantee contracts between system and environment

10. **Advanced Specification Examples** : [[Advanced-Specification-Examples|Link]]
    - Specifying data structures such as graphs : [[Advanced-Specification-Examples|Link]]
    - Solving differential equations in TLA+ : [[Advanced-Specification-Examples|Link]]
    - BNF grammars as TLA+ modules : [[Advanced-Specification-Examples|Link]]
    - Multiprocessor memory correctness conditions : [[Advanced-Specification-Examples|Link]]
    - Linearizability, serializability, and sequential consistency

11. **Writing Specifications: Engineering Practice** : [[Writing-Specifications-Engineering-Practice|Link]]
    - Why and what to specify : [[Writing-Specifications-Engineering-Practice|Link]]
    - Choosing the grain of atomicity : [[Writing-Specifications-Engineering-Practice|Link]]
    - Choosing a data-structure abstraction level : [[Writing-Specifications-Engineering-Practice|Link]]
    - Common style pitfalls : [[Writing-Specifications-Engineering-Practice|Link]]
    - Writing specifications during design : [[Writing-Specifications-Engineering-Practice|Link]]

12. **The Standard Modules** : [[The-Standard-Modules|Link]]
    - The Sequences module : [[The-Standard-Modules|Link]]
    - The FiniteSets module : [[The-Standard-Modules|Link]]
    - The Bags module : [[The-Standard-Modules|Link]]
    - The Peano and ProtoReals foundation modules : [[The-Standard-Modules|Link]]
    - The Naturals, Integers, and Reals modules

13. **The TLA+ Tools** : [[The-TLA+-Tools|Link]]
    - The Syntactic Analyzer : [[The-TLA+-Tools|Link]]
    - The $\text{TLATEX}$ typesetter : [[The-TLA+-Tools|Link]]
    - The $\text{TLC}$ model checker : [[The-TLA+-Tools|Link]]
    - TLC values and expression evaluation : [[Formal-Semantics-of-the-TLA+-Language|Link]]
    - Model-checking mode versus simulation mode : [[The-TLA+-Tools|Link]]
    - Views, fingerprints, and symmetry : [[The-TLA+-Tools|Link]]
    - Limitations of liveness checking under a finite model : [[The-TLA+-Tools|Link]]
    - Practical debugging advice for TLC : [[The-TLA+-Tools|Link]]

---

## Chapter Summaries

### Chapter 1: A Little Simple Math (pp. 9–14)

**Summary:** A refresher on the small amount of elementary mathematics — propositional logic, sets, and predicate logic — needed before writing TLA+ specifications, aimed at readers whose formal-math background may be thin.

**Key Definitions & Concepts by Section:**
- **1.1 Propositional Logic** — the five Boolean operators $\land$ (conjunction), $\lor$ (disjunction), $\lnot$ (negation), $\Rightarrow$ (implication), $\equiv$ (equivalence, "equality for Booleans"); precedence and associativity/commutativity of $\land$/$\lor$; tautology (a propositional formula true for all truth-value assignments to its identifiers); truth tables as a decision procedure. : [[Elementary-Mathematical-Foundations-for-Specification|Link]]
- **1.2 Sets** — set and the membership relation $\in$ taken as undefined primitives; set equality by extensionality; empty set $\{\}$; the operators $\cap$ (intersection), $\cup$ (union), $\subseteq$ (subset), $\setminus$ (set difference).
- **1.3 Predicate Logic** — universal ($\forall$) and existential ($\exists$) quantification, bounded ($\forall x \in S : F$) vs. unbounded ($\forall x : F$) quantification; the duality $(\exists x \in S : F) \equiv \lnot(\forall x \in S : \lnot F)$; $\forall$ as generalized conjunction and $\exists$ as generalized disjunction; bound vs. free variables/occurrences. : [[Elementary-Mathematical-Foundations-for-Specification|Link]]
- **1.4 Formulas and Language** — the distinction between a formula as a noun (a value-denoting expression that may be true or false) versus a formula used as a statement asserting truth; a heuristic (substitute a name and check grammaticality) for telling which role a formula plays in a sentence. : [[Formal-Semantics-of-the-TLA+-Language|Link]]

**Key Questions:**
1. Why does classical logic define $F \Rightarrow G$ to be true whenever $F$ is false, and why does this match the ordinary meaning of "if F then G"?
2. What is the difference between bounded and unbounded quantification, and why does the book recommend bounded quantification in specifications?

---

### Chapter 2: Specifying a Simple Clock (pp. 15–22)

**Summary:** Introduces the core TLA modeling vocabulary — behaviors, states, actions, stuttering steps — by building up the specification of a trivial hour clock, first informally and then in TLA+ syntax. : [[Specifying-Safety-Properties|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 Behaviors** — a state is an assignment of values to (all) variables; a behavior is an infinite sequence of states; a system is specified as a set of allowed behaviors. : [[States-Actions-and-Behaviors|Link]]
- **2.2 An Hour Clock** — step (a pair of successive states); initial predicate (e.g. $HCini$) and next-state relation/action (e.g. $HCnxt$, containing both unprimed and primed variables); action (a formula relating old and new state values); the temporal operator $\Box$ ("box"), $\Box F$ asserting $F$ is always true; stuttering step ($hr' = hr$) and the bracket notation $[HCnxt]_{hr}$ standing for $HCnxt \lor (hr' = hr)$; a specification takes the form $HCini \land \Box[HCnxt]_{hr}$; behaviors are always infinite, with termination modeled as infinite stuttering. : [[Composing-Specifications|Link1]], [[Refinement-and-Implementation|Link2]]
- **2.3 A Closer Look at the Specification** — a state as a potential assignment to *all* variables in the universe, not just the ones "of interest"; temporal formula (an assertion about behaviors); theorem (a temporal formula satisfied by every behavior, distinguished from a *valid* formula by requiring provability). : [[Composing-Specifications|Link1]], [[Real-Time-Specification|Link2]]
- **2.4 The Specification in TLA+** — the correspondence between typeset and ASCII TLA+ syntax; module structure (`module`/`MODULE`, `extends`/`EXTENDS`); the $\stackrel{\Delta}{=}$ ("is defined to equal") definition symbol; `variable`/`VARIABLE` declarations; the $i \mathbin{{.}{.}} j$ integer-range operator from the Naturals module; `theorem`/`THEOREM` statements. : [[Composing-Specifications|Link1]], [[Real-Time-Specification|Link2]], [[Advanced-Specification-Examples|Link3]], [[Specifying-Safety-Properties|Link4]]
- **2.5 An Alternative Specification** — the modulus operator `%`; the general principle that a specification is a piece of mathematics admitting many equivalent formulations, and that equivalent formulations should be judged only by readability. : [[Real-Time-Specification|Link]]

**Key Questions:**
1. Why must a clock specification explicitly allow stuttering steps, and what would go wrong (compositionally) if it didn't?
2. In what sense does the formula $HC$, not $HCini$ alone, constitute "the" specification of the hour clock, and why does TLA+ itself not distinguish which definition in a module carries that special status?

---

### Chapter 3: An Asynchronous Interface (pp. 23–34)

**Summary:** Specifies a two-phase handshake protocol between a sender and receiver, using it as a vehicle to introduce abstraction as a design choice, type invariants, records, the `EXCEPT` construct, and the scoping rules for TLA+ definitions.

**Key Definitions & Concepts by Section:**
- **3.1 The First Specification** — abstraction (a specification deliberately omits physical detail, e.g. treating simultaneous voltage changes on separate wires as a single step); constant parameter (e.g. `constant Data`) as a way of leaving something unspecified; state function (a variable/constant expression with no primes or $\Box$); state predicate (a Boolean-valued state function); invariant of a specification $Spec$ (a state predicate $Inv$ such that $Spec \Rightarrow \Box Inv$ is a theorem); type of a variable $v$ in $Spec$ (a set $T$ such that $v \in T$ is an invariant); `unchanged v`/`UNCHANGED v` (abbreviation for $v' = v$); enabling condition (the condition under which an action can be taken). : [[Composing-Specifications|Link1]], [[Real-Time-Specification|Link2]]
- **3.2 Another Specification** — records as an alternative to tuples for structured state, written $[val : Data, rdy : \{0,1\}, ack : \{0,1\}]$ for the record *type* and $r.val$ for field access; the record-construction/`EXCEPT` idiom $[chan \text{ except } !.val = d,\ !.rdy = 1-@]$, where `!` denotes the record being formed and `@` denotes the old field value. : [[Real-Time-Specification|Link]]
- **3.3 Types: A Reminder** — reiterates that TLA+ is untyped: a variable's "type" is just an ordinary invariant, with no special formal status.
- **3.4 Definitions** — a definition $Id \stackrel{\Delta}{=} exp$ makes $Id$ synonymous with $exp$ (substitution after parsing, not textual); operator definitions of the form $Id(p_1,\dots,p_n) \stackrel{\Delta}{=} exp$; symbol (identifier or operator symbol); scope of a declaration/definition (extends to the end of the enclosing module or expression); the rule against re-declaring a symbol already in scope. : [[Real-Time-Specification|Link]]
- **3.5 Comments** — TLA+'s two comment forms, `(* ... *)` (nestable, block) and `\*` (end-of-line); the use of comments and module-splitting to control the order in which a specification is read, independent of the definition-before-use ordering `EXTENDS` imposes.

**Key Questions:**
1. Why does the book insist a variable's "type" is not a real type-system concept but merely the name given to a particular invariant?
2. What decision (grain of atomicity / signal granularity) was made when representing `val` and `rdy` as changing in a single step, and what real-world detail does that decision hide?

---

### Chapter 4: A FIFO (pp. 35–44)

**Summary:** Builds a FIFO buffer out of two instances of the asynchronous-channel module from Chapter 3, introducing sequence operators, the `instance`/`INSTANCE` construct for module reuse and parametrization, variable hiding via existential quantification, and the closed-system vs. open-system distinction.

**Key Definitions & Concepts by Section:**
- **4.1 The Inner Specification** — Sequences module operators: $Seq(S)$ (all sequences over $S$), $Head(s)$, $Tail(s)$, $Append(s,e)$, $s \circ t$ (concatenation), $Len(s)$; the `instance`/`INSTANCE` statement for reusing a module's definitions under a substitution (e.g. `InChan == INSTANCE Channel WITH Data <- Message, chan <- in`), producing qualified names like $InChan\,!Init$. : [[Composing-Specifications|Link1]], [[Real-Time-Specification|Link2]]
- **4.2 Instantiation Examined** *(section for readers wanting the underlying semantics; skippable)*
  - **4.2.1 Instantiation Is Substitution** — every defined symbol has a "real" (fully expanded) definition in terms of the module's parameters; instantiation substitutes actual expressions for those parameters throughout. : [[Formal-Semantics-of-the-TLA+-Language|Link]]
  - **4.2.2 Parametrized Instantiation** — an instance can itself take a parameter, e.g. $Chan(ch) \stackrel{\Delta}{=} \text{instance } Channel \text{ with } chan \leftarrow ch$, letting one instantiation stand for a family of instances. : [[Formal-Semantics-of-the-TLA+-Language|Link]]
  - **4.2.3 Implicit Substitutions** — a substitution $\Sigma \leftarrow \Sigma$ for a parameter $\Sigma$ can be omitted, since it is implied whenever the instantiation occurs in scope of a same-named symbol.
  - **4.2.4 Instantiation Without Renaming** — an `instance` statement issued with no assigned name (rather than `Id == instance ...`) instantiates a module's definitions directly, without qualification, useful when only one instance is needed. : [[Formal-Semantics-of-the-TLA+-Language|Link]]
- **4.3 Hiding the Queue** — hiding an internal variable with the temporal existential quantifier $\exists$ (informally: "there exists some assignment to the hidden variable across the behavior making the formula true"); the standard TLA+ idiom of a wrapping module with a parametrized inner instance to hide a variable that can't be directly existentially quantified in its own declaring module.
- **4.4 A Bounded FIFO** — reusing an existing module (rather than copying it) to build a stricter variant by conjoining an extra enabling condition; `assume`/`ASSUME` statements for stating hypotheses about constants (never about variables); the fact that in TLA+ (built on ZF set theory) every value is formally a set, so constant parameters need not be assumed to be sets.
- **4.5 What We're Specifying** — closed-system (complete-system) specification (describes correct behavior of both system and environment) vs. open-system specification (describes only the system's correct behavior, tolerant of environment misbehavior); system steps vs. environment steps as an informal (non-formal) decomposition of the next-state action.

**Key Questions:**
1. Why can't the internal variable $q$ simply be hidden by writing $\exists q : Spec$ inside the same module that declares $q$, and how does the book's wrapping-module idiom get around this?
2. What is the practical difference between a closed-system and an open-system specification, and why does the book recommend defaulting to closed-system specifications despite them being "philosophically less satisfying"?

---

### Chapter 5: A Caching Memory (pp. 45–64)

**Summary:** A long worked example — a linearizable memory interface, a write-through cache implementation, and a sketch of the refinement-mapping proof that the cache implements the memory — that introduces functions, records-as-functions, recursive function definitions, and the notion of implementation as logical implication.

**Key Definitions & Concepts by Section:**
- **5.1 The Memory Interface** — declaring operators as constant parameters (e.g. `constant Send(_,_,_,_)`) to stand for unspecified actions, since TLA+ has no action parameters; `assume`/`ASSUME` used to constrain a declared operator's result type (e.g. to `boolean`); the built-in `boolean` set $\{true, false\}$; the memory-request record type $MReq$ built from read/write record-set unions; `choose x : F` used to define an arbitrary value satisfying a property, e.g. $NoVal \stackrel{\Delta}{=} \text{choose } v : v \notin Val$.
- **5.2 Functions** — function terminology: $\mathrm{domain}\, f$, application $f[x]$, range, equality by matching domain and pointwise values; function-set notation $[S \to T]$; function-constructor notation $[x \in S \mapsto e]$; records as functions whose domain is a finite set of strings, with $r.c$ an abbreviation for $r[\text{"c"}]$; the general `EXCEPT` construct $[f \text{ except } ![c]=e]$ and its multi-field/nested/multi-argument generalizations; functions of multiple arguments as functions over tuples.
- **5.3 A Linearizable Memory** — linearizable memory (a memory where each request's effect on `mem` may occur at any point between the request and its response); an internal ("Inner") specification exposing implementation-detail variables versus a public spec hiding them via existential quantification, mirroring the Chapter 4 hiding idiom.
- **5.4 Tuples as Functions** — an $n$-tuple as, formally, a function with domain $\{1,\dots,n\}$; the Cartesian product operator $\times$; sequences as functions with domain $1\,..\,Len(s)$; nonrecursive definitions of $Head$, $Tail$, and $\circ$ in terms of ordinary function construction.
- **5.5 Recursive Function Definitions** — the recursive function-definition syntax $f[x \in S] \stackrel{\Delta}{=} e}$ (illegal as an ordinary $[x\in S \mapsto e]$ definition, since $f$ would be used before being defined), illustrated with $fact$ and a two-argument Ackermann-style example. : [[Elementary-Mathematical-Foundations-for-Specification|Link]]
- **5.6 A Write-Through Cache** — the `let`/`in` local-definition construct for structuring and abbreviating action definitions; a full worked specification (module `WriteThroughCache`) with actions `Req`, `Rsp`, `RdMiss`, `DoRd`, `DoWr`, `MemQWr`, `MemQRd`, `Evict`; the coherence property (`Coherence`) as a state predicate distinct from the type invariant. : [[Refinement-and-Implementation|Link]]
- **5.7 Invariance** — inductive invariant (a predicate $Inv$ that is itself an invariant of the next-state action, i.e. $Inv \land [Next]_v \Rightarrow Inv'$) versus an invariant of the whole specification that need not be preserved by every individual next-state step (illustrated by `Coherence`, which fails as an invariant of `Next` alone); the general proof obligation $Init \Rightarrow Inv$, $Inv \land [Next]_v \Rightarrow Inv'$, $Inv \Rightarrow P$ for proving a property $P$ invariant.
- **5.8 Proving Implementation** — implementation as implication ($Sys \Rightarrow Spec$); refinement mapping (a tuple of state functions substituted for a lower-level spec's hidden variables to prove a higher-level spec follows); step simulation (the requirement that each concrete next-state step either simulates an abstract step or leaves the abstract-level state unchanged). : [[Refinement-and-Implementation|Link]]

**Key Questions:**
1. Why is `Coherence` an invariant of the whole specification `Spec` but *not* an invariant of the bare next-state action `Next`, and what does this reveal about the difference between "invariant of a specification" and "inductive invariant"?
2. In what precise sense does "implementation" reduce to logical implication in TLA, and what role does a refinement mapping play in proving that implication when the two specifications use different internal variables?

---

### Chapter 6: Some More Math (pp. 65–74)

**Summary:** Fills in the remaining mathematical machinery — advanced set operators, the untyped nature of TLA+, the precise meaning of recursive definitions, and the `choose` operator — and clarifies the fundamental distinction between functions and operators.

**Key Definitions & Concepts by Section:**
- **6.1 Sets** — $\mathrm{union}\, S$ (flattened union of a set of sets) and $\mathrm{subset}\, S$ (the power set of $S$); set-builder notations $\{x \in S : p\}$ and $\{e : x \in S\}$; the standard `FiniteSets` module operators $Cardinality(S)$ and $IsFiniteSet(S)$; Russell's paradox and the informal criterion for a collection being "too big to be a set" (existence of an injective map from all sets into the collection).
- **6.2 Silly Expressions** — TLA+ as an untyped formalism in which every syntactically well-formed expression has *some* (possibly unspecified) meaning; a "silly" expression like $3/0$ or $3/\text{"abc"}$ does not invalidate a formula whose truth doesn't depend on that expression's value; explicit trade-off argument for why specifications benefit from omitting a type system even though programming languages benefit from having one. : [[Specifying-Safety-Properties|Link]]
- **6.3 Recursion Revisited** — the semantics of $f[x \in S] \stackrel{\Delta}{=} e$ as sugar for $f \stackrel{\Delta}{=} \text{choose } f : f = [x \in S \mapsto e]$; a recursive definition need not determine a unique (or any sensible) value, illustrated by a self-contradictory example; TLA+'s prohibition on mutually recursive definitions, and the standard workaround of packaging mutually-recursive functions as fields of one record-valued recursive function.
- **6.4 Functions versus Operators** — functions are values with a domain that must be a set, while operators are not values (an operator applied to no arguments is not itself an expression) and may take other operators as arguments; operators cannot be defined recursively in TLA+ (only functions can), motivating the standard trick of defining a recursive helper function (e.g. $C_S[T \in \mathrm{subset}\, S]$) to implement operators like $Cardinality$; TLA+ disallows infix *function* definitions (only operators can be infix). : [[Elementary-Mathematical-Foundations-for-Specification|Link]]
- **6.5 Using Functions** — the difference between defining a function's *value* directly (e.g. $f' = [i \in Nat \mapsto i+1]$, which pins down $f'$ uniquely) versus only constraining its values pointwise (e.g. $\forall i \in Nat : f'[i] = i+1$, which under-determines $f'$). : [[Composing-Specifications|Link1]], [[States-Actions-and-Behaviors|Link2]]
- **6.6 Choose** — Hilbert's $\varepsilon$-style semantics of `choose x : p`: a deterministic (not nondeterministic) but generally unspecified value; the common idiom `choose x <belongs to> S : p` as sugar for `choose x : (x <belongs to> S) /\ p`; the contrast between a specification pinning a variable to a fixed `choose`-defined value versus a nondeterministic specification allowing the variable to vary freely over a set.

**Key Questions:**
1. Why can `Cardinality` not be defined directly as a recursive operator in TLA+, and how does defining a recursive *function* instead get around this restriction?
2. Why does the book insist that `choose` is not a nondeterministic operator, and what confusion does this dispel about specifications that use `choose`?

---

### Chapter 7: Writing a Specification: Some Advice (pp. 75–84)

**Summary:** A practical, non-formal chapter of engineering advice on choosing what to specify, at what grain of atomicity and level of data-structure detail, plus a checklist of stylistic pitfalls to avoid when writing TLA+. : [[Writing-Specifications-Engineering-Practice|Link]]

**Key Definitions & Concepts by Section:**
- **7.1 Why Specify** — three justifications for writing a specification: aiding the design process, communicating a design precisely, and enabling tool-assisted error-finding (e.g. via TLC, Chapter 14). : [[Writing-Specifications-Engineering-Practice|Link]]
- **7.2 What to Specify** — a specification models a chosen *view* of part of a system, not the whole system; TLA+'s particular strength at catching concurrency errors as a guide to where to focus specification effort. : [[Writing-Specifications-Engineering-Practice|Link]]
- **7.3 The Grain of Atomicity** — grain of atomicity (the choice of what real-world change corresponds to one behavior step); the action-composition operator $A \cdot B$ (sequential composition of two actions into a single step); commuting actions (actions $A, B$ commute iff $A\cdot B \equiv B\cdot A$), with a sufficient condition (disjoint variable footprints, no mutual enabling/disabling); using commutativity to argue that a coarser-grained specification's behaviors correspond to a finer-grained one's. : [[States-Actions-and-Behaviors|Link1]], [[Writing-Specifications-Engineering-Practice|Link2]]
- **7.4 The Data Structures** — trade-off between precise, low-level data-structure modeling (reduces certain classes of error at the cost of specification complexity) and abstract modeling, decided by which errors the specification is meant to catch. : [[Advanced-Specification-Examples|Link1]], [[Writing-Specifications-Engineering-Practice|Link2]]
- **7.5 Writing the Specification** — a recommended order of steps for writing any specification: pick variables and define type invariant/initial predicate, write the next-state action as a disjunction of named actions, add temporal/fairness conditions, then assert theorems. : [[Writing-Specifications-Engineering-Practice|Link]]
- **7.6 Some Further Hints** — style rules: don't be too clever (prefer $v' = exp$ or $v' \in exp$ forms over indirect equational constraints); a type invariant is a derived property, not an assumption usable inside actions; don't be too abstract (illustrated by the keyboard `KeyStroke` vs. `Press`/`Release` example — abstraction can silently hide real system behaviors like two keys pressed simultaneously); don't assume differently-shaped values are automatically unequal (use tagged records, e.g. a `type` field, to force distinctness); move quantifiers ($\exists$/$\forall$) to the outside of disjunctions/conjunctions for readability; be careful about what a prime attaches to (e.g. $f[e]' = f'[e']$, not generally $f'[e]$); write comments as comments, not as vacuous logical disjuncts.
- **7.7 When and How to Specify** — recommends writing specifications *during* design (incrementally, deliberately incomplete at first) rather than only after a design is finalized, since precise description itself aids clear thinking.

**Key Questions:**
1. Under what condition can a sequence of fine-grained steps be safely collapsed into one coarse-grained step without changing what the specification "really" says, and why is commutativity central to that argument?
2. Why does the book warn that a defined type invariant provides no logical guarantee inside an action definition (e.g. that $n' > 7$ does not imply $n'$ is a natural number)?

---

### Chapter 8: Liveness and Fairness (pp. 87–116)

**Summary:** This chapter introduces temporal logic rigorously so that specifications can express liveness properties — requirements that something eventually happens — using the operators $\Box$ (always) and $\Diamond$ (eventually), and formalizes the notions of weak and strong fairness that let a safety specification be strengthened into a complete one. : [[Temporal-Logic-and-Liveness|Link]]

**Key Definitions & Concepts by Section:**
- **8.1 Temporal Formulas** — a temporal formula $F$ is a function from behaviors to Boolean, written $\sigma \models F$; state predicates, $\Box P$, and $\Box[N]_v$ as the three basic kinds of temporal formulas; $\sigma^{+n}$ (the suffix of $\sigma$ starting at state $n$); a formula is *invariant under stuttering* iff adding/deleting stuttering steps never changes its truth value — TLA allows only such formulas; $\langle A \rangle_v \triangleq A \wedge (v' \neq v)$ (a non-stuttering $A$ step). : [[Temporal-Logic-and-Liveness|Link]]
- **8.2 Temporal Tautologies** — a *temporal tautology* is true under any substitution for its identifiers (distinct from a plain temporal theorem); $\Diamond F \triangleq \neg\Box\neg F$; $F \leadsto G \triangleq \Box(F \Rightarrow \Diamond G)$ ("leads to"); duality law: replacing $\Box \leftrightarrow \Diamond$, $\wedge \leftrightarrow \vee$ and reversing implications turns any tautology into its dual; $\Diamond\Box F$ ("eventually always") and $\Box\Diamond F$ ("infinitely often") as key derived idioms. : [[Temporal-Logic-and-Liveness|Link]]
- **8.3 Temporal Proof Rules** — a *proof rule* differs from a *tautology*: the Generalization Rule (from $F$ infer $\Box F$) and the Implies Generalization Rule (from $F \Rightarrow G$ infer $\Box F \Rightarrow \Box G$) do not correspond to tautologies the way Modus Ponens does in propositional logic. : [[Temporal-Logic-and-Liveness|Link]]
- **8.4 Weak Fairness** — $\mathrm{enabled}\,A$ (predicate: action $A$ is currently possible); $WF_v(A) \triangleq \Box(\Box\,\mathrm{enabled}\,\langle A\rangle_v \Rightarrow \Diamond\langle A\rangle_v)$, i.e. if $A$ becomes forever enabled, an $A$ step must eventually occur. : [[Real-Time-Specification|Link1]], [[Temporal-Logic-and-Liveness|Link2]]
- **8.5 The Memory Specification** — applying $WF$ to the linearizable memory's $Do(p)$/$Rsp(p)$ actions (§8.5.1); the **WF Conjunction Rule** and **WF Quantifier Rule** (§8.5.2–8.5.3): $WF_v(A) \wedge WF_v(B) \equiv WF_v(A \vee B)$ when the two actions satisfy a mutual-non-preemption condition (DR1/DR2), generalized to $n$ actions and to quantification. : [[Composing-Specifications|Link1]], [[Real-Time-Specification|Link2]]
- **8.6 Strong Fairness** — $SF_v(A) \triangleq \Box\Diamond\,\mathrm{enabled}\,\langle A\rangle_v \Rightarrow \Box\Diamond\langle A\rangle_v$; strong fairness requires an action be repeatedly (not necessarily continuously) enabled before a step must occur; weak and strong fairness coincide when an enabled action can only be disabled by its own occurrence; the analogous SF Conjunction/Quantifier Rules. : [[Temporal-Logic-and-Liveness|Link]]
- **8.7 The Write-Through Cache** — worked example choosing weak vs. strong fairness per action based on whether other components can repeatedly re-disable it. : [[Refinement-and-Implementation|Link]]
- **8.8 Quantification** — bound ("rigid") variables vs. TLA "flexible" variables; the temporal existential quantifier $\exists$ as a hiding operator (distinct from ordinary $\exists$ over constants); temporal $\forall x : F \triangleq \neg\exists x : \neg F$ (rarely used). : [[Real-Time-Specification|Link]]
- **8.9 Temporal Logic Examined** — the canonical specification shape $\mathrm{Init} \wedge \Box[\mathrm{Next}]_{vars} \wedge \mathrm{Liveness}$ (§8.9.1); **machine closure** (§8.9.2): a specification is machine closed iff its liveness conjunct constrains neither the initial state nor which steps may occur — guaranteed when Liveness is a conjunction of fairness properties on *subactions* of Next; **subaction** (every $A$ step is a $\mathrm{Next}$ step); machine closure as a possibility condition (§8.9.3); refinement mappings don't commute automatically with $WF$/$SF$ under substitution, requiring direct computation via enabling rules (§8.9.4); the practical unimportance of liveness relative to safety (§8.9.5); a caution against unrestrained use of temporal logic outside the canonical form (§8.9.6). : [[Temporal-Logic-and-Liveness|Link]]

**Key Questions:**
1. Why does machine closure require fairness conditions to be stated only on subactions of the next-state action, and what concretely goes wrong (as in the $x=0$ example) when this is violated?
2. What is the precise difference between weak fairness ("continuously enabled") and strong fairness ("continually/repeatedly enabled"), and under what condition are they provably equivalent for a given action?
3. Why is a temporal proof rule not the same thing as a temporal tautology, and why does conflating the two lead to errors (e.g., with the Generalization Rule)?

---

### Chapter 9: Real Time (pp. 117–134)

**Summary:** This chapter extends TLA+ specifications with a real-valued clock variable `now` so that upper- and lower-bound timing constraints on actions can be expressed, generalizing weak fairness to quantitative time bounds while showing how to avoid degenerate ("Zeno") specifications. : [[Real-Time-Specification|Link]]

**Key Definitions & Concepts by Section:**
- **9.1 The Hour Clock Revisited** — introducing the variable `now` to represent real time, changing in discrete but arbitrarily fine steps; a real-time requirement is split into an upper bound (clock ticks at least once every $3600+\rho$ seconds) and a lower bound (ticks at most once every $3600-\rho$ seconds); using a hidden timer variable $t$ and a submodule/parametrized instantiation to hide it, culminating in $\mathrm{RTHC} = HC \wedge RTnow \wedge (\exists t : I(t)!HCTime)$. : [[Composing-Specifications|Link1]], [[Refinement-and-Implementation|Link2]]
- **9.2 Real-Time Specifications in General** — $RTBound(A, v, \delta, \varepsilon)$: an $\langle A\rangle_v$ step cannot occur before $\langle A\rangle_v$ has been continuously enabled for $\delta$ time units, and must occur before it has been enabled for $\varepsilon$ units; $RTBound$ with $\varepsilon < \mathrm{Infinity}$ implies weak fairness of $A$; $SRTBound$ (the strong-fairness analog) is noted but judged impractical. : [[Real-Time-Specification|Link]]
- **9.3 A Real-Time Caching Memory** — applying $RTBound$ to an abstract $Respond(p)$ action for the memory interface vs. applying real-time bounds to concrete subactions (round-robin scheduling via `canGoNext`, `position`) for an implementable write-through cache; illustrates that real bounds on shared-resource actions generally require a scheduling discipline. : [[Real-Time-Specification|Link]]
- **9.4 Zeno Specifications** — a behavior in which time never advances by more than a bounded total amount even though infinitely many steps occur; **non-Zeno** specifications (equivalently, machine closed with respect to time) are guaranteed when $RTBound$ conditions apply to actions that are subactions of Next and are pairwise disjoint. : [[Real-Time-Specification|Link]]
- **9.5 Hybrid System Specifications** — representing continuously varying physical quantities (not just time) via an $\mathrm{Integrate}$ operator solving differential equations, replacing $RTnow(v)$ with a next-state action driven by numerical integration. : [[Real-Time-Specification|Link]]
- **9.6 Remarks on Real Time** — real-time constraints as a strong form of liveness; practical real-time specifications tend to be simple; $RTnow$/$RTBound$ suffice for essentially all cases the author encountered. : [[Real-Time-Specification|Link]]

**Key Questions:**
1. Why must a real-time bound formula always be stated on an action of the form $\langle A\rangle_v$ (with a subscript) rather than on a bare action $A$?
2. What makes a specification "Zeno," and why is a Zeno specification a symptom of a likely modeling error rather than a legitimate abstraction?
3. Why is it easier to add a real-time bound to a high-level abstract action (as in the memory specification) than to bound the individual subactions directly (as attempted for the write-through cache), and what technique (round-robin scheduling) resolves the difficulty?

---

### Chapter 10: Composing Specifications (pp. 135–168)

**Summary:** This chapter shows how to write a system specification as the conjunction of separate component specifications rather than as one monolithic next-state action, covering disjoint-state, shared-state, and joint-action composition, interface refinement, and open- vs. closed-system specifications. : [[Composing-Specifications|Link]]

**Key Definitions & Concepts by Section:**
- **10.1–10.2 Composing Two/Many Specifications** — composing specifications means conjoining their formulas; **interleaving** vs. **noninterleaving** specifications (whether simultaneous multi-component steps are allowed); the general **Composition Rule**: $(\forall k \in C : v_k' = v_k) \equiv (v' = v)$ implies a monolithic reformulation of $\forall k \in C : I_k \wedge \Box[N_k]_{v_k}$; using `except` and $IsFcnOn$ to keep an array-valued variable a well-formed function across components.
- **10.3 The FIFO** — worked noninterleaving composite specification of Sender/Buffer/Receiver, using a submodule to hide the internal queue `q`; three ways to state cross-component initial-state requirements (redundantly, assigned to one component, or as a separate conjunct).
- **10.4 Composition with Shared State** — **disjoint-state** vs. **shared-state** composition; §10.4.1 *Explicit State Changes*: splitting responsibility for a shared variable (e.g. `buf`) between components via auxiliary actions $\sigma$/$\rho$ describing "changes not caused by me," yielding the **Shared-State Composition Rule**; §10.4.2 *Composition with Joint Actions*: a **joint action** is a single step simultaneously attributed to two components (e.g. Send/Reply on `memInt`), needed when an abstract interface variable can't be partitioned between components. : [[Composing-Specifications|Link]]
- **10.5 A Brief Review** — the three independent classification axes (§10.5.1): interleaving/noninterleaving, disjoint-state/shared-state, joint-action/separate-action; §10.5.2 argues the interleaving choice is mostly a matter of convenience unless implementing a lower-level interleaving spec; §10.5.3 notes joint actions arise mainly from abstracting away two-step communication into one. : [[Composing-Specifications|Link]]
- **10.6 Liveness and Hiding** — §10.6.1: an interleaving composition of machine-closed components is usually machine closed, but a noninterleaving (esp. joint-action) composition may not be, illustrated by the Zeno hour-clock example from Chapter 9 reread as a 3-component joint-action composition; §10.6.2: the **Compositional Hiding Rule**, showing when $\exists h : S_1 \wedge S_2$ can itself be decomposed into separate hidden-variable specifications. : [[Composing-Specifications|Link]]
- **10.7 Open-System Specifications** — a **complete-system specification** ($E \wedge M$) vs. an **open-system specification**, which must serve as a contract between user and implementer; plain implication $E \Rightarrow M$ is too weak; the new temporal operator $E \overset{+}{\leadsto} M$ (asserting $M$ stays true at least one step longer than $E$) is used instead; also called *rely-guarantee* or *assume-guarantee* specifications. : [[Composing-Specifications|Link]]
- **10.8 Interface Refinement** — an **interface refinement** $IR$ relates a lower-level variable $l$ to a higher-level variable $h$ via $LSpec \triangleq \exists h : IR \wedge HSpec$; worked examples: a binary (bit-vector) hour clock (§10.8.1) and refining a value-channel into a bit-by-bit channel (§10.8.2); **data refinement** as the simplest case where $IR = \Box P$ expresses $h$ as a pure function of the current $l$ (§10.8.3); combining interface refinement with open-system liveness requires attributing blame for stalled lower-level behavior to system or environment via $\mathrm{Liveness} \Rightarrow (\exists h : IR \wedge HSpec)$ (§10.8.4). : [[Refinement-and-Implementation|Link]]
- **10.9 Should You Compose?** — composition is mostly a matter of taste for specifications written from scratch (monolithic is usually clearer); it becomes useful when reusing existing component specifications or writing genuine open-system contracts.

**Key Questions:**
1. Why does an interleaving composition of machine-closed components tend to preserve machine closure, while a joint-action (noninterleaving) composition need not — as shown by the Zeno hour-clock example?
2. What problem does the operator $E \overset{+}{\leadsto} M$ solve that plain implication $E \Rightarrow M$ does not, when specifying a contract between a system and its environment?
3. In the memory interface example, why couldn't the Send/Reply communication be split into two separate per-component actions the way ordinary shared-state composition (Section 10.4.1) requires, forcing the use of joint actions instead?

---

### Chapter 11: Advanced Examples (pp. 169–204)

**Summary:** This chapter works through two categories of harder specification problems — reusable data-structure modules (graphs, differential equations, BNF grammars) and genuinely high-level system correctness conditions — using progressively more realistic multiprocessor memory specifications to show how subtle "what does correctness mean" questions are formalized. : [[Advanced-Specification-Examples|Link]]

**Key Definitions & Concepts by Section:**
- **11.1.1 Local Definitions** — the `local` modifier restricts a definition (or `instance` statement) to its own module, so it is not re-exported by `extends`/`instance`; cannot be applied to `constant`/`variable` declarations or plain `extends`. : [[Advanced-Specification-Examples|Link]]
- **11.1.2 Graphs** — representing a directed graph as a record with `node`/`edge` fields; `IsDirectedGraph`, `DirectedSubgraph`, `IsUndirectedGraph`, `Path`, `AreConnectedIn`, `IsStronglyConnected`, `IsTreeWithRoot` as reusable operators, illustrating why one defines "is-a-graph" predicates rather than "the set of all graphs."
- **11.1.3 Solving Differential Equations** — defining $\mathrm{Integrate}(D, a, b, \mathit{InitVals})$ via `choose` over a function $g$ encoding a solution and its derivatives, using an inductively defined $\mathrm{IsDeriv}(n, df, f)$ built from a first-derivative $\varepsilon$-$\delta$ definition ($\mathrm{IsFirstDeriv}$); demonstrates expressing genuinely sophisticated (real-analysis) mathematics in TLA+. : [[Advanced-Specification-Examples|Link]]
- **11.1.4 BNF Grammars** — representing a grammar as a function $G$ from strings to languages ($\mathrm{Grammar} \triangleq [\mathrm{string} \to \mathrm{subset}\ \mathrm{Seq}(\mathrm{string})]$); operators $\&$ (concatenation of sentence sets), $|$ (union), $L^+$, $L^*$, $\mathrm{Nil}$, $\mathrm{tok}$/$\mathrm{Tok}$; $\mathrm{LeastGrammar}(P)$ as the smallest grammar satisfying a system of productions, used to formalize a BNF grammar as a fixed-point-style `choose`. : [[Advanced-Specification-Examples|Link1]], [[The-Syntax-of-TLA+|Link2]]
- **11.2.1 The Interface** — a register-based multiprocessor memory interface (`regFile`, `RegisterInterface` module) supporting multiple outstanding requests per processor.
- **11.2.2 The Correctness Condition** — refining the informal notion "acts as if operations were executed in some sequential order" to require per-processor program order be respected; working through scenarios to decide (i) whether infinite behaviors must have a single global total order or only per-finite-prefix orders, (ii) whether the memory may predict future writes, and (iii) whether its explanation of past reads may change over time. : [[Advanced-Specification-Examples|Link]]
- **11.2.3 A Serial Memory** — a memory that cannot predict the future and cannot revise its explanations; introduces the general history-variable technique (`opQ`, `opId`, `opOrder`) and the state predicate `Serializable` asserting existence of a consistent total order extending `opOrder`; liveness requires both eventual response and eventual full ordering of every pair of operations. : [[Advanced-Specification-Examples|Link]]
- **11.2.4 A Sequentially Consistent Memory** — a simpler but *non-machine-closed* specification: reads may return an arbitrary value, with a hidden `Internal` action later constrained (via liveness) to dequeue only reads whose returned value matches `mem`; illustrates that non-machine-closed specifications can be simpler while being non-directly-implementable. : [[Advanced-Specification-Examples|Link]]
- **11.2.5 The Memory Specifications Considered** — direct (if impractical) implementability of the linearizable and serial memory specifications, versus the sequentially consistent memory's fundamental non-implementability (it would require guessing future writes); a non-machine-closed specification is sometimes the simplest correct way to state a very high-level requirement, despite the general preference for machine closure. : [[Composing-Specifications|Link1]], [[Real-Time-Specification|Link2]], [[Advanced-Specification-Examples|Link3]], [[Specifying-Safety-Properties|Link4]]

**Key Questions:**
1. Why is the sequentially consistent memory specification simpler to write than the serial memory specification, yet not machine closed / not directly implementable?
2. What three independent design decisions (about global vs. per-prefix ordering, prediction of the future, and revisability of explanations) distinguish the different possible formalizations of "multiprocessor memory correctness," and how does each choice rule out or permit specific scenarios?
3. Why does defining `LeastGrammar` as a `choose` over the *smallest* grammar satisfying a set of productions correctly capture the meaning of a BNF grammar, rather than simply asserting the productions as equalities?

---

### Chapter 12: The Syntactic Analyzer (pp. 207–210)

**Summary:** A short reference chapter on the Syntactic Analyzer (`SANY`), the Java front-end tool that parses a TLA+ specification and checks it for syntactic and semantic errors before other tools (like TLC) are run. : [[The-TLA+-Tools|Link]]

**Key Definitions & Concepts:**
- `SANY` — the Syntactic Analyzer, a Java program (by Jean-Charles Grégoire and David Jefferson) that parses and checks a TLA+ spec; also serves as a front end for other tools such as `TLC`.
- syntactic error — an error that makes the specification grammatically incorrect: it violates the BNF grammar or the precedence/alignment rules (Chapter 15).
- semantic error — an error that violates the legality conditions of Chapter 17 (e.g. an undefined/mistyped identifier); despite the name, it does not mean "wrong meaning" — it means the spec has no meaning at all.
- residual stack trace — the parse-tree trace `SANY` prints on a syntax error, showing where in the grammar it was when parsing failed, used to locate errors that may be reported far from their actual source.
- `-s` option — restrict checking to syntax errors only (useful early in writing a spec).
- `-d` option — enter a debugging mode after checking, to inspect the spec's structure (e.g. where an identifier is defined).
- divide-and-conquer debugging — the recommended technique of removing parts of a module to isolate an otherwise hard-to-find syntax error.

**Key Questions:**
1. Why does the book insist that "semantic error" is a misleading term for what `SANY` reports?
2. Why might `SANY` report a syntax error at a point in the file far from the actual mistake, and what tool output helps you find the real location?

---

### Chapter 13: The TLATEX Typesetter (pp. 211–220)

**Summary:** Documents `TLATEX`, the Java tool that calls LaTeX to typeset a TLA+ module into readable, publication-quality mathematical notation (as used throughout this book), covering its command-line options, how it formats specification text versus comments, and how to fix or customize its output. : [[The-TLA+-Tools|Link]]

**Key Definitions & Concepts by Section:**
- **13.1 Introduction** — `TLATEX` (based on ideas by Dmitri Samborski) calls the external `LaTeX` program, producing a `dvi` file (device-independent typeset output) that can be converted to PostScript or PDF; run via `java tlatex.TLA [options] fileName`; `help`/`info` options list usage.
- **13.2 Comment Shading** — the `shade` option typesets comments in shaded boxes; `-grayLevel`, `-ps`/`-nops`, `-psCommand` control shading darkness and PostScript/PDF generation.
- **13.3 How It Typesets the Specification** — preserves meaningful alignments (e.g. aligning $\land$ and $=$ symbols in a conjunction list); treats zero and one space between symbols identically; `noProlog`/`noEpilog` suppress typesetting of text outside the module; does not itself check syntactic correctness (though it flags illegal lexemes). : [[Real-Time-Specification|Link1]], [[Composing-Specifications|Link2]]
- **13.4 How It Typesets Comments** — one-line vs. multi-line comments (three input styles); the escape markers `` `~ ~' `` (omit part of a comment from typeset output), `` `^ ^' `` (force ordinary-text/LaTeX-command formatting), and `` `. .' `` (force fixed-width/verbatim typesetting, e.g. for diagrams); guidance on paragraph formatting and quote handling. : [[The-Syntax-of-TLA+|Link]]
- **13.5 Adjusting the Output Format** — `-ptSize`, `-textwidth`/`-textheight`, `-hoffset`/`-voffset` control font size and page geometry.
- **13.6 Output Files** — `-out` (names the `.tex`/`.dvi`/`.log`/`.aux` files LaTeX produces), `-alignOut` (a separate alignment file for trouble-shooting), `-tlaOut` (writes an ascii-readable version with `` `^ ^' `` regions stripped), `-style` (substitutes a custom LaTeX package for the tlatex style).
- **13.7 Trouble-Shooting** — `TLATEX` invokes LaTeX (and optionally a PostScript/PDF converter) as external processes up to three times; failures in these can silently produce no output or hang; log files and the `-alignOut` option help diagnose this. : [[Formal-Semantics-of-the-TLA+-Language|Link]]
- **13.8 Using LATEX Commands** — text enclosed in `` `^ ^' `` is passed verbatim to LaTeX, allowing custom formatting (e.g. a `describe` environment for label/definition lists) inside comments, at the cost of ascii readability — mitigated by pairing with an ascii version wrapped in `` `~ ~' ``.

**Key Questions:**
1. Why does `TLATEX` typeset a specification's alignment (spacing) faithfully but treat zero and one space as equivalent — what does this imply about how you should write specification whitespace?
2. What is the difference in purpose between the three comment-formatting escapes `` `~ ~' ``, `` `^ ^' ``, and `` `. .' ``?

---

### Chapter 14: The TLC Model Checker (pp. 221–264)

**Summary:** The longest and most detailed tool chapter, `TLC` is a model checker (by Yuan Yu, with Lamport, Mark Hayden, and Mark Tuttle) for finding errors in TLA+ specifications by exhaustively or randomly exploring reachable states; the chapter explains what `TLC` can and cannot evaluate, precisely how it checks safety and liveness properties, and gives extensive practical advice for using it effectively, using the alternating bit protocol as a running example. : [[The-TLA+-Tools|Link]]

**Key Definitions & Concepts by Section:**
- **14.1 Introduction to TLC** — `TLC` handles specs of the standard form $\mathit{Init} \land \Box[\mathit{Next}]_{\mathit{vars}} \land \mathit{Temporal}$; cannot handle the temporal hiding operator $\exists$ (existential quantification) directly — checked instead via a refinement mapping; checks for "silliness" errors and deadlock (absence of which is expressed as $\Box(\mathit{enabled}\ \mathit{Next})$); configuration file specifies `SPECIFICATION`/`INIT`+`NEXT`, `PROPERTY`/`PROPERTIES`, `INVARIANT`/`INVARIANTS`, and `CONSTANT`/`CONSTANTS` assignments; model — an assignment of values to a spec's constant parameters, needed because `TLC` works by generating behaviors; model checking mode (default, tries to find all reachable states) vs. simulation mode (randomly generates behaviors); constraint — a state predicate bounding the model to make the reachable-state set finite; reachable states — states appearing in a behavior satisfying $\mathit{Init} \land \Box[\mathit{Next}]_{\mathit{vars}} \land \Box\mathit{Constr}$; ex post facto specification — a correctness specification written after the fact, to check a system design lacking a formal spec; when checking a `PROPERTY`, `TLC` actually checks that the safety part of the spec implies the safety part of the property and that the whole spec implies the property's liveness part — so `TLC` cannot check a non-machine-closed spec against a safety property (see machine closure, §8.9.2).
- **14.2 What TLC Can Cope With** — : [[The-TLA+-Tools|Link]]
  - **14.2.1 TLC Values** — `TLC` computes only TLC values: Booleans, Integers, Strings, and Model Values (introduced via `CONSTANT` in the configuration file, each distinct by name), plus finite sets and functions of comparable TLC values built inductively; comparable — roughly, values whose equality is determined by TLA+ semantics (e.g. strings and numbers are not comparable).
  - **14.2.2 How TLC Evaluates Expressions** — evaluates left-to-right/short-circuit for $\land$, $\lor$, $\Rightarrow$, `if/then/else`; cannot evaluate unbounded quantifiers/`choose` ($\exists x: p$, $\forall x: p$, $\mathit{choose}\ x: p$) or any expression whose value is not a TLC value; can sometimes evaluate an expression even when a subexpression alone is unevaluable; evaluates recursively defined functions by direct substitution, which can loop forever on certain (rewritable) legal mutual-recursion definitions.
  - **14.2.3 Assignment and Replacement** — `CONSTANT` statement assignments `c = v` give a value to a constant parameter or override a definition `TLC` can't compute; replacements `c <- d` substitute one defined/declared symbol for another (e.g. to supply an operator parameter's value, or to swap a simple-but-slow definition for an equivalent one `TLC` evaluates efficiently). : [[Refinement-and-Implementation|Link1]], [[States-Actions-and-Behaviors|Link2]]
  - **14.2.4 Evaluating Temporal Formulas** — a temporal formula is "nice" (necessary for `TLC` to evaluate it) iff it's a conjunction of: state predicates, invariance formulas ($\Box P$), box-action formulas ($\Box[A]_v$), or simple temporal formulas (built from temporal state formulas and simple action formulas $\mathit{WF}_v(A)$, $\mathit{SF}_v(A)$, $\Box\Diamond\langle A\rangle_v$, $\Diamond\Box[A]_v$ via simple Boolean operators); a `SPECIFICATION` formula must contain exactly one box-action conjunct. : [[Temporal-Logic-and-Liveness|Link]]
  - **14.2.5 Overriding Modules** — `TLC` overrides standard modules (`Naturals`, `Integers`, `Sequences`, `FiniteSets`, `Bags`, `TLC`) with hand-written Java classes for correctness and speed rather than evaluating their TLA+ definitions. : [[Formal-Semantics-of-the-TLA+-Language|Link1]], [[The-Standard-Modules|Link2]]
  - **14.2.6 How TLC Computes States** — computing successor states means evaluating the next-state action with unprimed variables bound and no primed variables yet assigned; disjunctions and bounded existentials split the computation into separate branches rather than evaluating left-to-right; an unassigned primed variable $x'$ in $x' = e$ triggers assignment; $\mathit{unchanged}\ e$ is expanded to $e' = e$. : [[The-TLA+-Tools|Link]]
- **14.3 How TLC Checks Properties** — defines `Init`, `Next`, `Temporal`, `Invariant`, `ImpliedInit`, `ImpliedAction`, `ImpliedTemporal`, `Constraint`, `ActionConstraint` from the configuration file's statements.
  - **14.3.1 Model-Checking Mode** — maintains a directed graph $G$ of found states and a queue $U$ of states awaiting successor computation; precise invariants of the algorithm and its step-by-step procedure (check `ASSUME`s, compute initial states, breadth-first expand successors, checking `Invariant`/`ImpliedInit`/`ImpliedAction` and reporting errors/deadlock); can use multiple worker threads. : [[Real-Time-Specification|Link1]], [[The-TLA+-Tools|Link2]]
  - **14.3.2 Simulation Mode** — repeatedly builds and checks single random behaviors up to a fixed maximum length (`depth`, default 100), using a pseudorandom seed and "aril" for reproducibility. : [[The-TLA+-Tools|Link]]
  - **14.3.3 Views and Fingerprints** — view — a state function (default: the tuple of all declared variables) whose value is what `TLC` actually stores as a graph node, letting states that agree on the view be treated as one, trading completeness (may miss states, and may mis-check `ImpliedTemporal`) for a smaller state space; fingerprint — a 64-bit hash of a view used internally as the graph node, subject to a (usually negligible) collision probability that `TLC` estimates at the end of a run both theoretically and empirically. : [[The-TLA+-Tools|Link]]
  - **14.3.4 Taking Advantage of Symmetry** — permutation of a finite set, symmetry — a specification is symmetric w.r.t. permutation $\pi$ if $\sigma$ satisfies it iff $\sigma^\pi$ does; `SYMMETRY` statement + `Permutations(S)` (from the standard `TLC` module) let `TLC` keep only one state per equivalence class under a symmetry set $\Pi$, reducing the state space by up to $n!$ for $n$-element symmetric sets; correct for safety checking but can be unreliable for `ImpliedTemporal` checking, and can cause "Failed to recover the state from its fingerprint" if the symmetry assumption is violated.
  - **14.3.5 Limitations of Liveness Checking** — a finite model can make it impossible to detect a genuine liveness-property violation, because all generated infinite behaviors reduce to stuttering and thus vacuously satisfy fairness-implication properties; recommends checking that `TLC` *does* report an error for known-false liveness properties as a sanity check. : [[The-TLA+-Tools|Link]]
- **14.4 The TLC Module** — the standard `TLC` module (overridden by Java) defines debugging/utility operators: `Print`, `Assert`, `JavaTime` (wall-clock time), `:>`/`@@` (single-point function / function-merge operators, used to print function values), `Permutations(S)`, and `SortSeq(s, \prec)` (used to build efficient overriding definitions like `FastSort`). : [[The-TLA+-Tools|Link]]
- **14.5 How to Use TLC** — : [[The-TLA+-Tools|Link]]
  - **14.5.1 Running TLC** — command-line options including `-deadlock`, `-simulate`, `-depth`, `-seed`, `-aril`, `-coverage`, `-recover`, `-cleanup`, `-difftrace`, `-terse`, `-workers`, `-config`, `-nowarning`. : [[Elementary-Mathematical-Foundations-for-Specification|Link]]
  - **14.5.2 Debugging a Specification** — describes normal progress/output messages (state counts, queue size, diameter of $G$, checkpoint messages) and error reports (parse exceptions from `SANY`, invariant-violation traces with minimal-length counterexamples, "silly expression" errors with a nested-expression location trace). : [[Composing-Specifications|Link1]], [[Real-Time-Specification|Link2]]
  - **14.5.3 Hints on Using TLC Effectively** — Start Small (begin with tiny models before scaling up); Be Suspicious of Success (a vacuous/do-nothing spec can trivially satisfy safety properties — use the `coverage` option and deliberately-false properties as sanity checks); Let TLC Help You Figure Out What Went Wrong (use `Print`, or restart from an `ErrorState` built from the last state of an error trace); Don't Start Over After Every Error (use checkpoints and the `recover` option); Check Everything You Can (test as many invariants as possible, not just the top-level correctness property); Be Creative (e.g. replace an infinite set like `Nat` with a finite one via replacement, even though this changes the spec's meaning, just to get `TLC` to run); Use TLC as a TLA+ Calculator (check small `ASSUME` statements to test your understanding of TLA+ semantics or look for counterexamples to conjectures).
- **14.6 What TLC Doesn't Do** — bounded integer range ($-2^{31}$ to $2^{31}-1$); `TLC` deviates from TLA+ semantics in two ways: it does not guarantee `choose x \in S : P` gives the same value for syntactically different but set-equal $S$, and it treats strings as primitive values rather than as sequences (so `"abc"[2]` is an error in `TLC` despite being legal TLA+). : [[The-TLA+-Tools|Link]]
- **14.7 The Fine Print** — : [[The-TLA+-Tools|Link]]
  - **14.7.1 The Grammar of the Configuration File** — the configuration file's grammar is itself given formally as a TLA+ module (`ConfigFileGrammar`, using the `BNFGrammars` module of §11.1.4); additional restrictions (e.g. at most one `INIT`, `NEXT`, `VIEW`, `SYMMETRY` statement; multiple `INVARIANT` statements are equivalent to one combined statement).
  - **14.7.2 Comparable TLC Values** — the precise recursive rules defining when two TLC values are comparable (matching primitive type; model values comparable-but-unequal to everything; sets comparable by element count and pairwise element comparability; functions comparable by domain comparability and, if domains are equal, pointwise comparability).

**Key Questions:**
1. Why can `TLC` correctly verify a safety property is violated but, in general, be unable to detect a genuine violation of a liveness property using only a finite model?
2. What is the tradeoff `TLC`'s `VIEW` and `SYMMETRY` mechanisms make between state-space size and the reliability of `ImpliedTemporal` (liveness) checking?
3. Why does the book insist that the goal of running `TLC` is "not to verify that a specification is correct; it's to find errors" — how does this reframe practices like starting with tiny models or deliberately checking false properties?

---

### Chapter 15: The Syntax of TLA+ (pp. 275–290)

**Summary:** Gives the syntax of the ascii version of TLA+ in the computer scientist's sense (grammatical well-formedness, independent of whether identifiers are defined) — first a simple BNF grammar ignoring precedence/indentation/comments, then the informal detail needed to complete it, then the lexer rules turning characters into lexemes. : [[The-Syntax-of-TLA+|Link]]

**Key Definitions & Concepts by Section:**
- **15.1 The Simple Grammar** — the module `TLAPlusGrammar` written in BNF using the `BNFGrammars` constructs from Section 11.1.4; lexeme (an atomic character sequence, e.g. `|->`); token (a one-lexeme sentence); `ReservedWord`; `Name` vs `Identifier` (a `Name` that isn't reserved); `PrefixOp`/`InfixOp`/`PostfixOp` token sets; the full BNF productions for `G.Module`, `G.Unit`, `G.OperatorDefinition`, `G.Expression`, etc.
- **15.2 The Complete Grammar** — completes the grammar with details BNF can't express cleanly. : [[The-Syntax-of-TLA+|Link]]
  - **15.2.1 Precedence and Associativity** — operator precedence as a *range* of numbers (not a single value); an expression is illegal if two overlapping, non-associative precedence ranges leave the parse ambiguous (e.g. $a/b*c$); function application has precedence 16–16; Cartesian product $\times$ acts like a non-associative infix construct; undelimited constructs (`choose`, `if/then/else`, `case`, `let/in`, quantifiers) extend as far as possible; subscript notation (`[A]_e`, `\langle A \rangle_e`).
  - **15.2.2 Alignment** — the aligned conjunction/disjunction list notation: a conjunct is delimited by column position of the `/\`, not by explicit terminators; robustness of the notation even under minor misalignment; discouragement of tab characters.
  - **15.2.3 Comments** — delimited comments `(* ... *)` (recursively nestable) vs. end-of-line comments `\* ...`.
  - **15.2.4 Temporal Formulas** — syntactic well-formedness of temporal formulas depends on substituting out all defined operators first (can't be captured by a simple BNF grammar); double-priming-style illegality patterns. : [[Temporal-Logic-and-Liveness|Link]]
  - **15.2.5 Two Anomalies** — the `-`/`-.`  ambiguity between infix and prefix minus when an operator is used "bare" (as a higher-order argument or in an instance substitution); the `{x \in S : y \in T}` ambiguity, resolved in favor of the subset-of-$S$ reading.
- **15.3 The Lexemes of TLA+** — how a character stream becomes a lexeme stream: module boundaries marked by `----MODULE` and `====`; the "largest legal lexeme" rule; the special exclusion of `Name`s beginning with `WF_`/`SF_` (to keep `WF_x(A)` parseable as separate lexemes representing $WF_x(A)$).

**Key Questions:**
1. Why does TLA+ define operator precedence as a *range* rather than a single number, and what does it mean for an expression to be "illegal" because two ranges overlap?
2. Why can't "syntactic correctness" of a temporal formula (e.g. ruling out $\Box(x' = x+1)$) be captured by an ordinary BNF grammar, and what extra machinery (from Chapter 17) is needed?
3. What real ambiguity does the `WF_`/`SF_` lexeme exclusion rule prevent, and why is a lexical (not merely syntactic) fix required?

---

### Chapter 16: The Operators of TLA+ (pp. 291–316)

**Summary:** A reference-manual chapter giving both an informal explanation and a rigorous formal semantics for every built-in TLA+ operator, constant and nonconstant, culminating in the formal meaning of states, transitions, actions, and temporal formulas over behaviors. : [[Elementary-Mathematical-Foundations-for-Specification|Link]]

**Key Definitions & Concepts by Section:**
- **16.1 Constant Operators** — operators of ordinary (non-temporal) mathematics; **Formal Semantics** approach: define $[[e]]$, the meaning of expression $e$, inductively from a chosen set of *primitive* operators, using TLA+ itself as the metalanguage. : [[States-Actions-and-Behaviors|Link]]
  - **16.1.1 Boolean Operators** — `boolean` $= \{\text{true}, \text{false}\}$; $\land, \lor, \lnot, \Rightarrow, \equiv$; aligned conjunction/disjunction lists; unbounded ($\forall x : p$) vs. bounded ($\forall x \in S : p$) quantifiers; bounded quantification over tuples; formal semantics takes unbounded $\exists$/$\forall$ as primitive and defines all general/bounded forms in terms of them. : [[Formal-Semantics-of-the-TLA+-Language|Link]]
  - **16.1.2 The Choose Operator** — `choose x : p` (Hilbert's $\varepsilon$) as an arbitrary witness or an arbitrary value if none exists; bounded `choose x \in S : p` defined via the unbounded form; the two defining rules (existence implies the chosen value satisfies $P$; extensional equality of choices for equivalent predicates); the surprising consequence that $1/0 = 2/0$ under the naive `choose`-based definition of division, and the `Choice` operator as a fix.
  - **16.1.3 Interpretations of Boolean Operators** — three ways to interpret Boolean operators on non-Boolean arguments (e.g. $2 \land \langle 5 \rangle$): *conservative* (value totally unspecified, laws of logic hold only for genuine Booleans), *liberal* (value is always Boolean and all logic tautologies hold unconditionally), *moderate* (only expressions involving literal `true`/`false` behave as expected); TLA+'s semantics commits to the moderate interpretation as valid, permits liberal, forbids relying on more. : [[Formal-Semantics-of-the-TLA+-Language|Link]]
  - **16.1.4 Conditional Constructs** — `if p then e1 else e2` and `case p1 -> e1 [] ... [] pn -> en [] other -> e`; both defined formally in terms of `choose`; unspecified behavior of `case` without `other` when no arm matches or several do. : [[Elementary-Mathematical-Foundations-for-Specification|Link]]
  - **16.1.5 The Let/In Construct** — `let ... in e`; sequential definitional scoping equivalent to nested single-definition `let`s.
  - **16.1.6 The Operators of Set Theory** — $\in, \notin, \cup, \cap, \subseteq, \setminus,$ `union`, `subset`; set-builder constructs $\{e_1,\ldots,e_n\}$, $\{x \in S : p\}$, $\{e : x \in S\}$, including tuple-bound variants; Zermelo–Fränkel foundation with $\in$ as the only true primitive, other operators given by defining axioms (e.g. $\forall x : (x \in S \cup T) \equiv (x \in S) \lor (x \in T)$).
  - **16.1.7 Functions** — $f[v]$, `domain f`, $[S \to T]$; explicit function construction $[x \in S \mapsto e]$ and recursive function definitions $fcn[x \in S] = e$; the `except` construct $[f \text{ except } ![u]=a]$ and its multi-argument/nested forms, with `@` denoting the original value; multi-argument functions as functions on tuples; formal semantics via the primitive `IsAFcn` operator (a function equals the function built from its own domain and values) and defining rules for each construct.
  - **16.1.8 Records** — records as functions whose domain is a finite set of strings; `r.h` as sugar for `r["h"]`; record constructors $[h_1 \mapsto e_1, \ldots]$ and record sets $[h_1 : S_1, \ldots]$; `except` generalized to mix function application and field access.
  - **16.1.9 Tuples** — an $n$-tuple as a function with domain $\{1,\ldots,n\}$; Cartesian product $S_1 \times \cdots \times S_n$; non-associativity of $\times$ (triples vs. nested pairs are formally distinct, and equality between them is left unspecified); the 0-tuple $\langle\rangle$ and the (formally distinct-from-$e$) 1-tuple $\langle e \rangle$.
  - **16.1.10 Strings** — a string as a tuple of characters; the primitive, version-dependent set `Char`; `string` $=$ `Seq(Char)`; illustrative use of `choose` to map characters to ascii codes.
  - **16.1.11 Numbers** — numerals pre-defined independent of any standard module; the set `Nat` and its successor structure from module `Peano`; decimal numbers defined arithmetically via `ProtoReals`.
  - **16.2 Nonconstant Operators** — action operators (Table 3) and temporal operators (Table 4) are what make TLA+ more than ordinary math; understanding them requires reasoning about their arguments (states, transitions, behaviors), not just isolated meanings.
  - **16.2.1 Basic Constant Expressions** — a *formula* is a Boolean-valued expression; *validity* of a basic constant formula (true for every assignment to its declared constants) as a primitive notion built from primitive-operator meanings. : [[Formal-Semantics-of-the-TLA+-Language|Link]]
  - **16.2.2 The Meaning of a State Function** — a state as a function from variable names to values; a (basic) state function's meaning $s[[e]]$ as a mapping from states to constant expressions; state predicate = Boolean-valued state function, valid iff true in every state; discussion of why "the set of all states" cannot exist (Russell's-paradox-style argument) and the resulting semi-formal treatment. : [[Formal-Semantics-of-the-TLA+-Language|Link1]], [[Specifying-Safety-Properties|Link2]], [[Advanced-Specification-Examples|Link3]]
  - **16.2.3 Action Operators** — transition function (built via priming $'$ and action operators) assigns a value to a *step* (pair of states); action = Boolean-valued transition function; $[A]_e \equiv A \lor (e'=e)$; $\langle A \rangle_e \equiv A \land (e' \neq e)$; `enabled A` (existence of a successor state making $A$ true); `unchanged e` $\equiv e'=e$; action composition $A \cdot B$ (sequential composition through an intermediate state); illustrative computation of `enabled` on a non-Boolean-in-some-states action. : [[States-Actions-and-Behaviors|Link1]], [[Formal-Semantics-of-the-TLA+-Language|Link2]]
  - **16.2.4 Temporal Operators** — behavior = sequence of states; temporal formula meaning = predicate on behaviors ($\sigma \models F$); $\Box F$ true iff $F$ holds on every suffix; $\Diamond F \equiv \lnot\Box\lnot F$; $WF_e(A)$ and $SF_e(A)$ defined via $\Box\Diamond$/$\Diamond\Box$ combinations of `enabled` and $\langle A \rangle_e$; leads-to $F \leadsto G \equiv \Box(F \Rightarrow \Diamond G)$; temporal existential quantification $\exists x : F$ as a hiding operator defined via a stuttering-equivalence relation $\sim_x$ on behaviors; $\forall x : F \equiv \lnot\exists x : \lnot F$; the real-time operator $F \stackrel{+}{\leadsto} G$ (introduced fully in Ch. 10) formalized via finite-prefix satisfaction. : [[Formal-Semantics-of-the-TLA+-Language|Link1]], [[Temporal-Logic-and-Liveness|Link2]]

**Key Questions:**
1. Why does TLA+'s formal semantics commit only to the *moderate* interpretation of Boolean operators on non-Boolean values, rather than the philosophically cleaner conservative interpretation or the more convenient liberal one — and what breaks under conservative if you don't add explicit `= true` checks?
2. Why does $\times$ (Cartesian product) fail to be associative even though it "acts like" an infix operator, and what does this say about the definition of tuples as functions?
3. How does the moderate/`choose`-based definition of division make $1/0 = 2/0$ provable, and why is this considered an acceptable (if "disquieting") consequence of treating `choose` as Hilbert's $\varepsilon$?

---

### Chapter 17: The Meaning of a Module (pp. 317–338)

**Summary:** Builds on Chapter 16's semantics of basic expressions to define the full meaning of a TLA+ module — arity/order/level of operators, λ-expressions as the metalanguage for higher-order definitions, contexts, and finally the precise (capture-avoiding) semantics of module extension and instantiation. : [[Formal-Semantics-of-the-TLA+-Language|Link]]

**Key Definitions & Concepts by Section:**
- **17.1 Operators and Expressions** : [[Formal-Semantics-of-the-TLA+-Language|Link]]
  - **17.1.1 The Arity and Order of an Operator** — every TLA+ operator is 0th-, 1st-, or 2nd-order; arity as a tuple describing the number/order of arguments (e.g. arity $\langle\langle\_,\_\rangle,\_,\_\rangle$ for a 2nd-order operator taking a 2-ary operator and two expressions); TLA+ disallows 3rd-order+ operators to keep level-checking tractable; TLA+ remains a first-order logic since quantification is only over 0th-order operators. : [[Formal-Semantics-of-the-TLA+-Language|Link]]
  - **17.1.2 $\lambda$ Expressions** — generalizing expressions so that any operator (including 1st/2nd-order) can be "written down" as a value, e.g. $\lambda x, y : x \cup \{z,y\}$; $\lambda$-parameters as bound identifiers subject to $\alpha$-conversion; $\beta$-reduction as the rule for evaluating $\lambda$-application; λ expressions are metalanguage only, never legal TLA+ syntax. : [[Formal-Semantics-of-the-TLA+-Language|Link]]
  - **17.1.3 Simplifying Operator Application** — showing every syntactic operator-application form (infix, prefix, variable-arity constructs, bound-variable constructs, instantiation-qualified names, `let`) can be normalized to $Op(e_1,\ldots,e_n)$ form for uniform semantic treatment. : [[Refinement-and-Implementation|Link]]
  - **17.1.4 Expressions** — the inductive definition of "expression" built from 0th-order operators and arity-correct applications; only 1st-order $\lambda$ expressions can appear inside expressions (as arguments to 2nd-order operators).
- **17.2 Levels** — the four basic levels of an expression: 0 (constant), 1 (state), 2 (transition), 3 (temporal); level-correctness rules forbidding nonsensical constructs like double-priming $(x'+y)'$; levels of expressions vs. of operators (a rule mapping argument levels to a result level); constant-level operators/expressions as those built entirely from constants and constant-level built-ins; level-correctness of an expression is independent of whether its free identifiers are declared constants or variables (only the resulting *level* depends on that).
- **17.3 Contexts** — a context = declarations (arity+level) + definitions ($\lambda$-expression assignments) + module definitions, subject to consistency conditions (C1–C4: no double declare/define, no shadowing of context operators by $\lambda$ parameters, every free operator in a definition is declared, no module name double-defined); the "illegal" pseudo-definition $Op \stackrel{\Delta}{=} \mathord{?}$ marking a name as forbidden.
- **17.4 The Meaning of a λ Expression** — the inductive definition of $C[[e]]$ (substituting all defined names by their definitions, then $\beta$-reducing) that ultimately reduces `let` (the one construct Chapter 16 leaves undefined) to ordinary λ-application. : [[Formal-Semantics-of-the-TLA+-Language|Link]]
- **17.5 The Meaning of a Module** — a module's meaning as six sets: `Dcl` (declarations), `GDef`/`LDef` (global/local definitions), `MDef` (submodule definitions), `Ass` (assumptions), `Thm` (theorems); computed by an algorithm processing module statements in order against a growing "current context" `CC`. : [[Formal-Semantics-of-the-TLA+-Language|Link]]
  - **17.5.1 Extends** — merges in another module's six sets; legality requires no true name clashes (chains of `extends` sharing a common ancestor definition are allowed).
  - **17.5.2 Declarations** — `constant`/`variable` statements add to `Dcl`.
  - **17.5.3 Operator Definitions** — global vs. `local` operator definitions, added to `GDef`/`LDef` respectively as $\lambda$-expressions. : [[Real-Time-Specification|Link]]
  - **17.5.4 Function Definitions** — $Op[fcnargs] \stackrel{\Delta}{=} exp$ reduced to an equivalent `choose`-based operator definition. : [[Elementary-Mathematical-Foundations-for-Specification|Link]]
  - **17.5.5 Instantiation** — the core substitution semantics: `INSTANCE N WITH q1 <- e1, ...`; constant vs. nonconstant modules; the level-correctness condition on substituted arguments needed to preserve validity when instantiating a nonconstant module; naming with `I!Op`; assumption-guarded import of theorems ($A_1 \land \cdots \land A_k \Rightarrow T$); `local instance`. : [[Formal-Semantics-of-the-TLA+-Language|Link]]
  - **17.5.6 Theorems and Assumptions** — `theorem`/`assume` statements and their addition to `Thm`/`Ass`.
  - **17.5.7 Submodules** — a nested complete module contributes to the parent's `MDef`, usable in `instance` statements later in scope, but not propagated to modules that further instantiate the parent. : [[The-Standard-Modules|Link]]
- **17.6 Correctness of a Module** — semantic correctness = validity of $A \Rightarrow T$ for every theorem $T$ and the conjoined assumptions $A$; this reduces *any* meaningful question about a specification to a question of formula validity. : [[Formal-Semantics-of-the-TLA+-Language|Link]]
- **17.7 Finding Modules** — how a tool resolves `extends`/`instance` module names (typically to files named `N.tla`); circular module dependency makes a module syntactically incorrect. : [[The-Standard-Modules|Link1]], [[Formal-Semantics-of-the-TLA+-Language|Link2]]
- **17.8 The Semantics of Instantiation** — the precise, capture-avoiding definition of substitution: naive substitution breaks validity both for classic variable capture (illustrated with $(n \in \text{Nat}) \Rightarrow (\exists m \in \text{Nat} : m \geq n)$) and, more subtly, for TLA+'s *implicit* binders inside `enabled A` and $A \cdot B$; the level-correctness rule preventing substitution of a variable for a declared constant in a nonconstant module (illustrated with $\Box[c'=c]_c$ becoming invalid under such a substitution); the `$q` renaming trick that protects primed/bound occurrences inside `enabled`/`\cdot` before substitution; which operators instantiation *distributes over* (all constant operators, priming, $\Box$) versus not (`enabled`, `WF`, `SF`, `\cdot`, $\stackrel{+}{\leadsto}$). : [[Formal-Semantics-of-the-TLA+-Language|Link]]

**Key Questions:**
1. Why must TLA+ cap operators at 2nd-order, and how does this choice keep the level-correctness/arity-correctness machinery tractable while still letting TLA+ remain, in the logician's sense, a first-order logic?
2. What exactly goes wrong with "naive" substitution inside an `enabled A` expression during instantiation, and why is the fix (replacing primed occurrences with a fresh `$q` symbol before substituting) necessary rather than just an implementation convenience?
3. Why does level-correctness of an expression not depend on whether a given identifier is declared constant or variable, yet the *level* of the expression does — and how does this distinction do the work of ruling out things like $\Box[c'=c]_c$ becoming false after instantiating $c$ with a variable?

---

### Chapter 18: The Standard Modules (pp. 339–348)

**Summary:** Documents the standard library modules of TLA+ — `Sequences`, `FiniteSets`, `Bags`, and the layered numeric modules `Peano`/`ProtoReals`/`Naturals`/`Integers`/`Reals` — showing how ordinary mathematical structures are built up formally and kept mutually consistent. : [[The-Standard-Modules|Link]]

**Key Definitions & Concepts by Section:**
- **18.1 Module Sequences** — sequences as tuples (functions on $1..n$); previously unexplained operators `SubSeq(s,m,n)` (subsequence from $m$ to $n$) and `SelectSeq(s,Test)` (filter by predicate); `local instance Naturals` as a way to import definitions without re-exporting them to modules that extend/instantiate `Sequences`; the `local` modifier's general export-suppressing effect. : [[The-Standard-Modules|Link]]
- **18.2 Module FiniteSets** — `IsFiniteSet(S)` (existence of an enumerating finite sequence) and `Cardinality(S)` (defined only for finite sets, via a recursive `choose`-and-remove construction). : [[The-Standard-Modules|Link]]
- **18.3 Module Bags** — a bag/multiset as a function into the positive integers; operators `IsABag`, `BagToSet`, `SetToBag`, `BagIn` (the bag $\in$), `EmptyBag`, `CopiesIn`, bag union $\oplus$, bag difference $\ominus$ (written $\; \bar\ominus\;$ in source), `BagUnion(S)` (union over a set of bags, analog of `union`), bag containment $\sqsubseteq$ (analog of $\subseteq$), `SubBag(B)` (analog of `subset`), `BagOfAll(F,B)` (analog of the mapped-set construct $\{F(x):x\in B\}$), `BagCardinality(B)`; local helper `Sum(f)` for summing a function's range. : [[The-Standard-Modules|Link]]
- **18.4 The Numbers Modules** — the challenge of keeping multiple modules' definitions of shared operators (like `+`) mutually consistent when both are (transitively) extended; solved by routing all definitions through a single shared module `ProtoReals`, locally instantiated by `Naturals`/`Integers`/`Reals`; `Naturals` defines `+`, `*`, `<`, $\leq$, `Nat`, $\div$ (integer division), `-` (binary minus), `^` (exponentiation), `>`, $\geq$, `..` (interval), `%` (modulus), with $a\%b \in 0\,..\,(b-1)$ and $a = b\cdot(a\div b) + (a\%b)$; `Integers` extends `Naturals` adding `Int` and unary minus; `Reals` extends `Integers` adding `Real`, division `/`, and `Infinity` (with $-\text{Infinity} < r < \text{Infinity}$ for all reals $r$, and $-(-\text{Infinity})=\text{Infinity}$); module `Peano` defines `Nat`/`Zero`/`Succ` abstractly via Peano's axioms so that the definitions of tuples and strings (which rest on natural numbers) avoid circularity; module `ProtoReals` defines the reals as the essentially-unique complete ordered field containing the naturals (via `IsModelOfReals`, an `IsAbelianGroup` helper, and a least-upper-bound axiom), then derives `Naturals`, `Integers`, `Reals` from it — noting that operators like `R!+` obtained by named instantiation are unreadable, which is why one should avoid defining infix operators in modules meant to be instantiated under a name. : [[The-Standard-Modules|Link]]

**Key Questions:**
1. Why is the natural-number module `Peano` deliberately kept independent of tuples and strings, when TLA+ elsewhere defines tuples and strings in terms of natural numbers?
2. Why do `Naturals`, `Integers`, and `Reals` all locally instantiate a shared `ProtoReals` module rather than each defining `+` independently — what specifically breaks if a module extends two of them and they disagree?
3. How does defining `Cardinality` and `Sum` via `choose`-driven recursion over decreasing subsets avoid needing a built-in "recursion over naturals" primitive, and what does this reveal about how much of TLA+'s "obvious" math is actually built from `choose` and set theory?
