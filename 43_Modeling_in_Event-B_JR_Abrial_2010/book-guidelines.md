# Modeling in Event-B — Guidelines

## Header

**Title:** Modeling in Event-B: System and Software Engineering
**Author(s):** Jean-Raymond Abrial
**Publication:** Cambridge University Press, 2010

**Brief Summary:**
This book teaches a systematic, proof-based approach to modeling discrete systems — sequential, concurrent, and distributed programs as well as electronic circuits — using Event-B, a simplification and extension of the B formalism. The central organizing idea is that a correct final system is reached not by writing a program directly but by building a sequence of gradually more concrete mathematical models (via horizontal and vertical refinement), each one analyzed and proved correct with respect to a carefully written requirements document, so that the final implementation is "correct by construction." The book is organized as a sequence of nearly self-contained worked examples — controllers, protocols, distributed algorithms, circuits, and sequential programs — each introducing new notation and mathematical vocabulary as needed, with all proofs verified using the open-source Rodin Platform tool set.

**Intent of the Author:**
Abrial wrote the book to give practitioners and students hands-on insight into modeling and formal reasoning as activities that precede and de-risk coding, showing through many concrete examples how proof failures act as a diagnostic tool that reveals missing guards, missing invariants, or gaps in the requirements themselves. He wants readers to come away able to construct their own formal models of real systems — not just to appreciate formal methods in the abstract — and repeatedly emphasizes that modeling, not programming, is the system engineer's primary task.

---

## Topic List

1. **Formal Methods and the Modeling Philosophy** : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]
   - Formal methods versus testing : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]
   - Modeling as blueprint construction : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]
   - Requirements document structure and traceability labels : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]
   - Explanatory text versus reference text : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]
   - Solution validation versus problem validation : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]
   - Discovering requirements through failed proofs : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]

2. **Discrete Transition Systems** : [[Discrete-Transition-Systems|Link]]
   - State as a set of variables : [[Discrete-Transition-Systems|Link]]
   - Events as guards and actions : [[Discrete-Transition-Systems|Link]]
   - Deterministic and non-deterministic actions : [[Discrete-Transition-Systems|Link]]
   - Before-after predicates : [[Discrete-Transition-Systems|Link]]
   - Invariants and gluing invariants : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Discrete-Transition-Systems|Link2]], [[Refinement-Theory|Link3]]
   - Conditional invariants : [[Discrete-Transition-Systems|Link]]
   - Deadlock and deadlock freedom : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Discrete-Transition-Systems|Link2]]
   - Closed models of a controller and its environment : [[Discrete-Transition-Systems|Link]]

3. **The Event-B Notation** : [[The-Event-B-Notation|Link]]
   - Machines and contexts : [[The-Event-B-Notation|Link]]
   - Sees extends and refines relationships : [[The-Event-B-Notation|Link]]
   - Carrier sets constants and axioms : [[The-Event-B-Notation|Link]]
   - Event parameters and witnesses : [[The-Event-B-Notation|Link]]
   - Convergent anticipated and ordinary events : [[The-Event-B-Notation|Link]]
   - Numeric and finite-set variants : [[The-Event-B-Notation|Link]]
   - Functional override and non-deterministic assignment : [[The-Event-B-Notation|Link]]

4. **Proof Obligation Rules** : [[Proof-Obligation-Rules|Link]]
   - Invariant preservation : [[Proof-Obligation-Rules|Link]]
   - Feasibility : [[Proof-Obligation-Rules|Link]]
   - Guard strengthening : [[Proof-Obligation-Rules|Link]]
   - Guard merging : [[Proof-Obligation-Rules|Link]]
   - Simulation : [[Proof-Obligation-Rules|Link]]
   - Convergence via natural-number or finite-set variants : [[The-Event-B-Notation|Link1]], [[Proof-Obligation-Rules|Link2]]
   - Witness feasibility : [[Proof-Obligation-Rules|Link]]
   - Theorem and well-definedness obligations : [[Proof-Obligation-Rules|Link]]
   - Relative deadlock freedom : [[Discrete-Transition-Systems|Link]]

5. **The Sequent Calculus and Logical Inference** : [[The-Sequent-Calculus-and-Logical-Inference|Link]]
   - Sequents rules of inference and proof trees : [[The-Sequent-Calculus-and-Logical-Inference|Link]]
   - Theories as sets of inference rules
   - Propositional inference rules : [[The-Sequent-Calculus-and-Logical-Inference|Link1]], [[Sequential-Program-Derivation|Link2]]
   - Predicate language and quantifier rules : [[The-Sequent-Calculus-and-Logical-Inference|Link]]
   - Equality and one point rules : [[The-Sequent-Calculus-and-Logical-Inference|Link]]
   - Proof by cases

6. **The Set-Theoretic Mathematical Language** : [[The-Set-Theoretic-Mathematical-Language|Link]]
   - Set comprehension and the extensionality axiom
   - Binary relation operators : [[The-Set-Theoretic-Mathematical-Language|Link]]
   - Domain and range restriction and subtraction
   - Partial and total functions
   - Lambda abstraction and function application
   - Boolean and arithmetic language : [[The-Set-Theoretic-Mathematical-Language|Link]]
   - Well-definedness conditions : [[The-Set-Theoretic-Mathematical-Language|Link]]
   - Peano axioms for natural numbers

7. **Advanced Data Structures** : [[Advanced-Data-Structures|Link]]
   - Irreflexive transitive closure : [[Advanced-Data-Structures|Link]]
   - Strongly connected graphs : [[Advanced-Data-Structures|Link]]
   - Infinite and finite lists : [[Advanced-Data-Structures|Link]]
   - Rings
   - Infinite finite-depth and free trees : [[Advanced-Data-Structures|Link]]
   - Tree induction and list induction : [[Advanced-Data-Structures|Link1]], [[Case-Study-Distributed-Network-Algorithms|Link2]]
   - Well-founded relations : [[Exercises-Projects-and-Mathematical-Developments|Link]]

8. **Refinement Theory** : [[Refinement-Theory|Link]]
   - Horizontal refinement
   - Vertical or data refinement : [[Case-Study-Communication-Protocols|Link1]], [[Case-Study-Distributed-Network-Algorithms|Link2]], [[Refinement-Theory|Link3]]
   - Superposition refinement
   - Splitting and merging events : [[Refinement-Theory|Link]]
   - New events and convergence : [[Refinement-Theory|Link]]
   - Forward and backward simulation : [[Refinement-Theory|Link]]
   - Trace semantics of refinement : [[Refinement-Theory|Link]]
   - Gluing invariants linking abstract and concrete state
   - External and internal variables : [[Refinement-Theory|Link]]

9. **Design Patterns for Reactive Controllers** : [[Design-Patterns-for-Reactive-Controllers|Link]]
   - The action-reaction pattern : [[Design-Patterns-for-Reactive-Controllers|Link]]
   - Weak synchronization of an action and a reaction : [[Design-Patterns-for-Reactive-Controllers|Link]]
   - Strong synchronization of an action and a reaction : [[Design-Patterns-for-Reactive-Controllers|Link]]
   - Composing synchronization patterns across two action-reaction pairs : [[Design-Patterns-for-Reactive-Controllers|Link]]

10. **Case Study: Bridge and Press Controllers** : [[Case-Study-Bridge-and-Press-Controllers|Link]]
    - Controlling cars on a one-way bridge : [[Case-Study-Bridge-and-Press-Controllers|Link]]
    - Traffic lights and car sensors
    - The mechanical press controller : [[Case-Study-Bridge-and-Press-Controllers|Link]]
    - Motor clutch and door safety constraints

11. **Case Study: Communication Protocols** : [[Case-Study-Communication-Protocols|Link]]
    - The two-phase handshake file transfer protocol : [[Case-Study-Communication-Protocols|Link]]
    - The bounded retransmission protocol : [[Case-Study-Communication-Protocols|Link]]
    - Fault tolerance and timer-based abortion
    - The alternating bit and parity optimizations
    - Anticipated events in protocol development : [[Case-Study-Communication-Protocols|Link1]], [[Exercises-Projects-and-Mathematical-Developments|Link2]], [[Sequential-Program-Derivation|Link3]]

12. **Case Study: Concurrent Programs and Electronic Circuits** : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
    - Simpson's four-slot fully asynchronous mechanism : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
    - Interleaving of concurrent instructions : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]
    - Writing and reading traces : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
    - Synchronous electronic circuit modeling : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
    - Circuit-environment coupling and the bool operator : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link1]], [[Case-Study-Distributed-Network-Algorithms|Link2]]
    - The single pulser and the arbiter circuits
    - The road traffic light circuit : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]

13. **Case Study: Distributed Network Algorithms** : [[Case-Study-Distributed-Network-Algorithms|Link]]
    - Leader election on a ring-shaped network : [[Case-Study-Distributed-Network-Algorithms|Link]]
    - Phase synchronization on a tree-shaped network : [[Case-Study-Distributed-Network-Algorithms|Link]]
    - Mobile agent routing with logical clocks : [[Case-Study-Distributed-Network-Algorithms|Link]]
    - Leader election on a connected graph network : [[Case-Study-Distributed-Network-Algorithms|Link]]
    - Contention resolution and symmetry breaking

14. **Sequential Program Derivation** : [[Sequential-Program-Derivation|Link]]
    - Naked events and implicit scheduling : [[Sequential-Program-Derivation|Link]]
    - Anticipated and convergent event status : [[Sequential-Program-Derivation|Link]]
    - Merging rules for if-statements and while-loops : [[Sequential-Program-Derivation|Link1]], [[Formal-Methods-and-the-Modeling-Philosophy|Link2]]
    - Binary search and sorting derivations : [[Sequential-Program-Derivation|Link]]
    - Pointer-based linked-list derivation : [[Sequential-Program-Derivation|Link]]
    - Generic function inversion and instantiation : [[Sequential-Program-Derivation|Link]]

15. **Case Study: Access Control and Train Systems** : [[Case-Study-Access-Control-and-Train-Systems|Link]]
    - The location access controller : [[Case-Study-Bridge-and-Press-Controllers|Link1]], [[Design-Patterns-for-Reactive-Controllers|Link2]], [[Case-Study-Access-Control-and-Train-Systems|Link3]]
    - Card readers turnstiles and doors
    - Physical versus logical variables
    - The train network safety system
    - Routes blocks signals and points

16. **Exercises Projects and Mathematical Developments** : [[Exercises-Projects-and-Mathematical-Developments|Link]]
    - End-of-book exercises and larger projects : [[Exercises-Projects-and-Mathematical-Developments|Link]]
    - Well-founded induction and fixpoint theory : [[Exercises-Projects-and-Mathematical-Developments|Link]]
    - The Cantor-Bernstein theorem : [[Exercises-Projects-and-Mathematical-Developments|Link]]
    - Zermelo's well-ordering theorem : [[Exercises-Projects-and-Mathematical-Developments|Link]]

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 1–23)

**Summary:** A non-technical chapter that motivates the book's approach to formal modeling, explains what "formal method" and "blueprint" mean in this context, argues for the importance of a well-structured requirements document, and gives an informal preview of the discrete-model vocabulary (state, events, guards, actions, invariants, refinement, decomposition, generic development) used throughout the rest of the book. : [[Discrete-Transition-Systems|Link]]

**Key Definitions & Concepts by Section:**
- **1.1 Motivation** — Event-B (a simplification/extension of the B formalism), correctness by construction, abstraction and refinement introduced as central themes.
- **1.2 Overview of the chapters** — Brief synopsis of Chapters 1–18; introduces the Rodin Platform as the tool used throughout.
- **1.3 How to use this book** — Suggested introductory vs. advanced course syllabi.
- **1.4 Formal methods** — Discusses common objections to formal methods; identifies four real difficulties: thinking before coding, integrating formal methods into development process, distinguishing modeling from (pseudo-)programming, and the need for proof alongside description; also flags weak requirements documents as a major difficulty. : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]
- **1.5 A little detour: blueprints** — blueprint (an artifact used to reason about a future system during construction, not a mock-up); blueprints are built incrementally, decomposed for readability, and reused via libraries.
- **1.6 The requirements document** — life cycle phases (system analysis, requirements document, technical specification, design, implementation, tests, maintenance); distinction between explanatory text and reference text; labeled/numbered requirement fragments (e.g. FUN, ENV, SAF, DEG, DEL) and traceability. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Communication-Protocols|Link2]], [[Formal-Methods-and-the-Modeling-Philosophy|Link3]]
- **1.7 Definition of the term "formal method" as used in this book** — formal model (a blueprint built with classical logic and set theory); complex systems (many interacting parts, high correctness demands); discrete systems / transition systems (behavior abstracted as steady states with sudden jumps); contrasts test reasoning (laboratory execution) with model (blueprint) reasoning.
- **1.8 Informal overview of discrete models** — state (constants and variables), event (guard + action), deadlock, external non-determinism, determinism, invariant (a permanently-holding condition on state), modality/reachability; closed model (controller + environment together); the three complexity-management concepts: refinement (Section 1.8.5, including data refinement), decomposition (Section 1.8.6), and generic development/instantiation (Section 1.8.7).

**Key Questions:**
1. Why does the author insist that a model of a program is fundamentally different from the program itself, and what practical consequence does this have for how proofs are used to "debug" a model?
2. What is the difference between the "explanatory text" and "reference text" of a requirements document, and why does the author consider this separation essential to good requirements engineering?
3. How are refinement, decomposition, and generic instantiation related to one another as complexity-management techniques (the text says "we refine a model to later decompose it... and we decompose it to further refine it")?

---

### Chapter 2: Controlling cars on a bridge (pp. 24–99)

**Summary:** A complete worked example — a controller for cars crossing a one-way bridge to an island — used to introduce, from scratch, the Event-B notation, the sequent calculus, and the core proof obligation rules (INV, FIS-adjacent reasoning, DLF, GRD, VAR) through four successive models (initial model plus three refinements). : [[Case-Study-Bridge-and-Press-Controllers|Link]]

**Key Definitions & Concepts by Section:**
- **2.2 Requirements document** — requirement labels FUN (functional) and ENV (environment): FUN-1 (bridge control), FUN-2 (limited number of cars), FUN-3 (one-way bridge), ENV-1/2/3 (traffic lights), ENV-4/5 (sensors); later FUN-4 (non-blocking / liveness) and FUN-5 (controller must be fast enough) are discovered and added during development. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Communication-Protocols|Link2]], [[Formal-Methods-and-the-Modeling-Philosophy|Link3]]
- **2.3 Refinement strategy** — the ordering of requirements across the four development stages. : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
- **2.4 Initial model: limiting the number of cars** — context/constant $d$, variable $n$; invariant, before–after predicate; proof obligation rule INV (invariant preservation): $A(c), I(c,v) \vdash I_i(c, E(c,v))$; sequent (hypotheses $\vdash$ goal, turnstile $\vdash$); rule of inference, antecedent/consequent, meta-variable; guard (necessary condition for an event to be enabled), event enabling; initialization event `init` and the invariant establishment rule (INV without invariants as hypotheses); deadlock / deadlock freedom and the DLF proof obligation rule; basic inference rules MON, P1, P2, P2', P3, INC, DEC, OR_L, OR_R1, OR_R2, HYP, FALSE_L, EQ_LR, EQ_RL, EQL. : [[Case-Study-Bridge-and-Press-Controllers|Link]]
- **2.5 First refinement: introducing the one-way bridge** — abstract state/variable vs. concrete state/variable; gluing invariant; refinement, guard strengthening proof obligation rule GRD (concrete guard implies abstract guard); correct refinement / INV rule for refinements; empty action `skip` (used when a new event refines a "do nothing" abstract transition); convergence / variant and the non-divergence proof obligations NAT and VAR (new events must decrease a variant so they cannot indefinitely postpone old events); relative deadlock freedom (DLF for refinements: abstract guards disjunction implies concrete guards disjunction); additional inference rules OR_R, AND_L, AND_R. : [[Case-Study-Bridge-and-Press-Controllers|Link]]
- **2.6 Second refinement: introducing the traffic lights** — conditional/implicative invariants; superposition (a refinement scheme where abstract variables are kept unchanged in the concrete state while new ones are added) and its adapted proof obligation rule SIM (simulation: equality of abstract/concrete expressions assigned to common variables); inference rules IMP_L, IMP_R, NOT_L. : [[Case-Study-Bridge-and-Press-Controllers|Link]]
- **2.7 Third refinement: introducing car sensors** — closed model architecture: controller, environment, output channels, input channels; distinguishes controller variables, environment (physical) variables, and channel variables; sensor states on/off; models the time lag between physical reality and the controller's approximate knowledge of it via input-channel invariants. : [[Case-Study-Bridge-and-Press-Controllers|Link]]

**Key Questions:**
1. How does the failure of a proof (e.g. for `ML_out / inv0_2 / INV`) function as a diagnostic tool that reveals a missing guard or missing axiom, and why does the author call this "the heart of the modeling method"?
2. What distinguishes an ordinary refinement (Section 2.5, where the abstract variable $n$ disappears entirely) from a superposition refinement (Section 2.6, where $a,b,c$ are kept and new variables $ml\_tl, il\_tl$ are added), and why does superposition require the additional SIM proof obligation?
3. Why must the controller's internal counters ($a,b,c$) in the third refinement be allowed to diverge from the true physical counts ($A,B,C$), and what invariants (inv3_21–inv3_32) guarantee that the controller nonetheless keeps the system safe?

---

### Chapter 3: A mechanical press controller (pp. 100–148)

**Summary:** Develops a controller for a mechanical press (motor, clutch, door) by first abstracting the recurring "action/reaction" communication idiom into two reusable, formally verified design patterns, then instantiating and composing these patterns across seven refinements to build the full controller while discovering (via failed proofs) the exact guards needed to satisfy the safety requirements. : [[Case-Study-Bridge-and-Press-Controllers|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 Informal description** — equipment (slide, motor, connecting rod, clutch), buttons B1–B4, user actions, and the rationale for inserting a controller and a safety door between commands and equipment. : [[Case-Study-Distributed-Network-Algorithms|Link1]], [[Formal-Methods-and-the-Modeling-Philosophy|Link2]]
- **3.2 Design patterns** — action/reaction paradigm; weak synchronization (Section 3.2.2: pattern where the reaction need not track every up/down transition of the action — modeled with counters $ca, cr$ and invariant $cr \le ca$); strong synchronization / retro-acting reaction (Section 3.2.3: reaction tracks the action tightly — invariant $ca \le cr+1$); both patterns derived by letting failed invariant-preservation proofs dictate the needed guards. : [[Design-Patterns-for-Reactive-Controllers|Link]]
- **3.3 Requirements of the mechanical press** — EQP_1–3 (equipment), FUN_1–2 (weak/strong synchronization requirements), SAF_1–2 (safety: clutch engaged $\Rightarrow$ motor works; clutch engaged $\Rightarrow$ door closed), FUN_3–5 (constraints between clutch and door). : [[Case-Study-Bridge-and-Press-Controllers|Link1]], [[Case-Study-Access-Control-and-Train-Systems|Link2]]
- **3.4 Refinement strategy** — ordered list of the (initially) seven planned refinements. : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
- **3.5–3.7 Initial model / first / second refinement** — instantiating the strong pattern for controller↔motor and controller↔clutch; instantiating the weak pattern for button↔controller; convention: controller events prefixed `treat_`; "false" events (needed when a button-press superposed on an existing event finds the underlying condition false, but the impulse variable must still be set).
- **3.8 Another design pattern: weak synchronization of two strong reactions** — synchronizing two independent strong action/reaction pairs $(a,r)$ and $(b,s)$ so that $s=1 \Rightarrow r=1$, without modifying the reacting events themselves — solved purely by strengthening the guards of the *acting* events $a\_off$ and $b\_on$ and adding invariants (culminating in the single invariant $b=1 \lor s=1 \Rightarrow a=1 \land r=1$). : [[Design-Patterns-for-Reactive-Controllers|Link]]
- **3.9 Third refinement** — instantiates the above pattern for SAF_1 (clutch engaged $\Rightarrow$ motor works). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **3.10–3.11 Fourth / fifth refinement** — connects controller to the door; discovers a missing requirement SAF_3 (motor stopped $\Rightarrow$ door open, equivalently SAF_3': door closed $\Rightarrow$ motor works); shows SAF_1 is in fact redundant, given SAF_2 and SAF_3', simplifying the refinement strategy.
- **3.12 Another design pattern: strong synchronization of two strong reactions** — a stronger pattern needed for FUN_3/FUN_4 (door cannot be closed/clutch cannot be disengaged repeatedly without the other event occurring); solved by introducing an auxiliary mediating variable $m$ and invariants relating counter pairs $(ca,cb)$ and $(cr,cs)$. : [[Design-Patterns-for-Reactive-Controllers|Link]]
- **3.13–3.14 Sixth / seventh refinement** — instantiates the strong–strong pattern for clutch/door; connects the clutch buttons B3/B4.

**Key Questions:**
1. How do the two basic action/reaction patterns (Section 3.2) differ in what they claim about synchronization, and why does going from "weak" to "strong" synchronization require strengthening guards rather than just adding invariants?
2. Why does the design-pattern approach forbid modifying the "reacting" events (e.g. $s\_on$, $r\_off$) directly when adding a new cross-pattern synchronization constraint, and how is the same effect achieved instead?
3. In what sense does the discovery that SAF_1 is derivable from SAF_2 and SAF_3' (Section 3.11) illustrate the broader claim that formal proof can reveal redundancy or gaps in a requirements document?

---

### Chapter 4: A simple file transfer protocol (pp. 149–175)

**Summary:** Models the classical two-phase handshake protocol for transferring a sequential file between a sender and a receiver, progressing from a non-distributed "magic copy" abstraction through three refinements that gradually introduce piece-by-piece transfer, real message channels, and a final data-compression optimization (sending parities instead of full counters); also introduces functions/relations vocabulary, universal quantification, and the notion of anticipated events. : [[Case-Study-Communication-Protocols|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Requirements** — FUN-1 (copy a file between sites), FUN-2 (file is a sequence of items), FUN-3 (file sent piece by piece, i.e. a distributed program). : [[Refinement-Theory|Link]]
- **4.2 Refinement strategy** — outline: initial model (final result only), first refinement (sender/receiver split, but receiver still "cheats" by reading the sender's memory directly), second refinement (real message-based communication), third refinement (optimization). : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
- **4.3 Protocol initial model** — carrier set $D$; total function $f \in 1..n \to D$ representing the file; partial function $g$; event `final` as an abstract "snapshot" that need not correspond to any real single execution step; math reminders: interval $a..b$, ordered pair $a \to b$, Cartesian product $S \times T$, power set $\mathcal{P}(S)$, binary relation $S \leftrightarrow T$, $\mathrm{dom}(r)$, $\mathrm{ran}(r)$, partial function $S \nrightarrow T$, total function $S \to T$; generic inference rule SET used informally for set-theoretic proof steps. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **4.4 Protocol first refinement** — new event `receive`, status convergent; domain restriction $s \triangleleft r$, domain subtraction $s \mathbin{\triangleleft\!-} r$, range restriction $r \triangleright t$, range subtraction $r \mathbin{\triangleright\!-} t$; convergence proof via variant $n+1-r$ (rules NAT, VAR); relative deadlock freedom for the refinement. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **4.5 Protocol second refinement** — full distributed model with a data channel (carrying index $s$ and item $d$) and an acknowledgment channel (carrying index $r$); sender counter $s$, receiver counter $r$, invariant $s \in r\,..\,r+1$. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **4.6 Protocol third refinement** — optimization: transmit only parities $p = \mathrm{parity}(s)$, $q = \mathrm{parity}(r)$ instead of full counters, justified by theorem thm3_1; universally quantified predicates and inference rules ALL_L, ALL_R (with the side condition that the quantified variable must not occur free in the hypotheses for ALL_R). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **4.7 Development revisited** — anticipated event (a new event, introduced in a refinement, that must not increase a not-yet-required variant, and need not decrease it until it becomes convergent in a later refinement); reworks the whole development starting from event `receive` as anticipated in the initial model, avoiding the artificial auxiliary variables $h$ and $b$ used in the first pass.

**Key Questions:**
1. Why does the initial model deliberately let the receiver "cheat" by having direct access to the sender's file, and what is gained by removing this cheating only in the second refinement rather than all at once?
2. What is an anticipated event, and how does reformulating `receive` as anticipated in the initial model (Section 4.7) eliminate the need for the auxiliary variables $h$ and $b$ used in the original development?
3. Why is it mathematically valid to replace the full counters $s$ and $r$ with their parities $p$ and $q$ in the third refinement (Section 4.6), and what specific structural property of the protocol (invariant inv2_2, $s \in r\,..\,r+1$) makes this optimization sound?

---

### Chapter 5: The Event-B modeling notation and proof obligation rules (pp. 176–203)

**Summary:** The formal reference chapter of the book: it systematically defines the full Event-B notation (machines, contexts, events, actions) and then presents, in general schematic form, every proof obligation rule used throughout the book (INV, FIS, GRD, MRG, SIM, NAT, FIN, VAR, WFIS, THM, WD), illustrated with a small running search example. : [[Proof-Obligation-Rules|Link]]

**Key Definitions & Concepts by Section:**
- **5.1.1 Introduction: machines and contexts** — model (complete mathematical development of a Discrete Transition System); machine (dynamic parts: variables, invariants, theorems, variant, events) vs. context (static parts: carrier sets, constants, axioms, theorems); modeling elements. : [[The-Event-B-Notation|Link]]
- **5.1.2 Machine and context relationships** — refines (machine-to-machine), extends (context-to-context, transitive), sees (machine-to-context, implicitly inherited through extended contexts); visibility rules, including that a machine refines at most one other machine and refines/extends must not create cycles. : [[The-Event-B-Notation|Link]]
- **5.1.3–5.1.4 Context structure / example** — clauses: extends, sets, constants, axioms, theorems; carrier sets are implicitly non-empty and pairwise disjoint.
- **5.1.5–5.1.6 Machine structure / example** — clauses: refines, sees, variables, invariants (gluing invariant: one mentioning both abstract and concrete variables), theorems, variant, events.
- **5.1.7 Events** — clauses: status (ordinary, convergent, anticipated), refines, any (parameters), where/when (guards), with (witnesses — a witness for a disappearing parameter/variable $a$ is $a: P(a)$, deterministic if $P(a)$ is $a=E$), then (actions); every machine must have an `initialization` event.
- **5.1.8 Actions** — deterministic assignment $x := E$; functional override shorthand $f(E_1):=E_2 \equiv f := f \mathbin{-\!\triangleleft} \{E_1 \to E_2\}$; non-deterministic action $x :| BA$ (before-after predicate, primed variables denote after-values); non-deterministic membership $x :\in S \equiv x :| x' \in S$; the non-deterministic before-after form as the general normalized form for all actions; simultaneity of actions in the same list; disjointness requirement on variables assigned in one action list.
- **5.1.9 Examples of events** — illustrates the compact "boxed" presentation style used throughout the book, and demonstrates a refinement with witnesses and a variant.
- **5.2.1 Introduction** — proof obligation generator; static checkers (lexical analyzer, syntactic analyzer, type checker); provers; the schematic event used throughout: `evt any x where G(s,c,v,x) then v :| BA(s,c,v,x,v') end`. : [[Discrete-Transition-Systems|Link]]
- **5.2.2 INV** — invariant preservation: $A(s,c), I(s,c,v), G(s,c,v,x), BA(s,c,v,x,v') \vdash inv(s,c,v')$; also given for refinements with abstract invariant $I$, concrete invariant $J$, witness predicates $W2$.
- **5.2.3 FIS** — feasibility of a non-deterministic action: $A(s,c), I(s,c,v), G(s,c,v,x) \vdash \exists v' \cdot BA(s,c,v,x,v')$.
- **5.2.4 GRD** — guard strengthening: concrete guards (with witness predicates for parameters) must imply each abstract guard.
- **5.2.5 MRG** — guard merging: for a concrete event merging two abstract events with identical parameters/actions, the concrete guard must imply the disjunction of the two abstract guards.
- **5.2.6 SIM** — simulation: the concrete before-after predicate (with witness predicates) must imply the abstract before-after predicate; covers both the general case (disjoint variable sets, via witnesses) and the case where abstract variables are kept unchanged in the concrete machine.
- **5.2.7 NAT** — a proposed numeric variant, under a convergent/anticipated event's guards, must be a natural number.
- **5.2.8 FIN** — a proposed finite-set variant must be finite under the event's guards.
- **5.2.9 VAR** — a convergent event's variant must strictly decrease (numeric: $n(v') < n(v)$; set: $t(v') \subset t(v)$); an anticipated event's variant must not increase (numeric: $n(v') \le n(v)$; set: $t(v') \subseteq t(v)$).
- **5.2.10 WFIS** — non-deterministic witness feasibility: $\exists x \cdot W(x,s,c,w,y,w')$ must hold given the concrete guards and before-after predicate.
- **5.2.11 THM** — a stated context/machine theorem must be provable from preceding axioms/theorems/invariants.
- **5.2.12 WD** — well-definedness: table of side conditions for potentially ill-defined constructs, e.g. $\bigcap S$ requires $S \ne \emptyset$; $f(E)$ requires $E \in \mathrm{dom}(f)$; $E/F$ requires $F \ne 0$; $E \bmod F$ requires $0 \le E \land 0 < F$; $\mathrm{card}(S)$ requires $S$ finite; $\min(S)$/$\max(S)$ require $S$ non-empty and bounded.

**Key Questions:**
1. What is the structural difference between the INV rule for a single (non-refining) event and the INV rule for a refining event, and why do witness predicates ($W2$) appear only in the latter?
2. Why does guard strengthening (GRD) alone not suffice to prove that a refinement is correct — what additional guarantee does the SIM (simulation) rule provide that GRD does not?
3. What is the operational difference between a convergent and an anticipated event with respect to the VAR proof obligation, and why would a modeler introduce an anticipated event instead of making it convergent immediately (compare with Chapter 4's use of anticipated events)?

---

### Chapter 6: Bounded re-transmission protocol (pp. 204–226)

**Summary:** This chapter extends the Chapter 4 file-transfer example to unreliable data and acknowledgment channels, developing the "bounded re-transmission protocol" (BRP) through an initial model and six refinements, formally deriving fault-tolerant behavior (timers, retry counters, alternating bits) from a requirements document rather than an ad hoc pseudo-code design. : [[Case-Study-Communication-Protocols|Link]]

**Key Definitions & Concepts by Section:**
- **6.1 Informal presentation** — normal behavior (sender/receiver exchange data and acknowledgment via SND_snd, RCV_rcv, RCV_snd, SND_rcv); unreliability of communications (sender's timer wakes after delay $dl$ when no acknowledgment arrives, triggering re-transmission); protocol abortion (retry counter reaching limit $M$ aborts on sender's side; receiver's own timer, set to at least $(M+1)\times dl$, lets it detect abortion indirectly); alternating bit (accompanies each data item to let the receiver distinguish a re-transmission from a genuinely new, coincidentally identical item); final situations (three possible end states — both succeed, sender aborts while receiver succeeds, or both abort — with the fourth combination, receiver aborts while sender does not, being impossible). : [[Proof-Obligation-Rules|Link1]], [[Case-Study-Distributed-Network-Algorithms|Link2]]
- **6.2 Requirements document** — FUN-1 to FUN-8: goal is total/partial transfer of a non-empty file (total = exact copy, partial = a prefix); each site ends believing terminated-successfully or aborted; sender-success implies receiver-success and receiver-abort implies sender-abort; sender may abort while receiver believes success; receiver's belief is always true (matches actual state of its copy). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Communication-Protocols|Link2]], [[Formal-Methods-and-the-Modeling-Philosophy|Link3]]
- **6.3 Refinement strategy** — plan: initial model + six refinements, each incrementally introducing FUN-4, then FUN-5/6, the file (FUN-1–3), the sender, channel unreliability, and a final optimization (parity bit). : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
- **6.4 Initial model** — carrier set $STATUS = \{working, success, failure\}$; variables $s\_st, r\_st$; observer event brp; anticipated events SND_progress/RCV_progress (technique from Chapter 4 §7). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **6.5 First and second refinements** — invariant $s\_st = success \Rightarrow r\_st = success$; events split into SND_success/SND_failure and RCV_success/RCV_failure, proved convergent via variants $\{success,failure\}\setminus\{s\_st\}$ and $\{success,failure\}\setminus\{r\_st\}$ ("cheating" events referencing the other participant's status). : [[Case-Study-Communication-Protocols|Link]]
- **6.6 Third refinement** — introduces original file $f \in 1..n \to D$ and transmitted file $g$ (prefix invariant $g = 1..r \lhd f$); $r\_st = success \Leftrightarrow r = n$; variant $n-r$. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **6.7 Fourth refinement** — introduces sender pointer $s$, activation bit $w$, data channel container $d$; events SND_snd_data, RCV_rcv_current_data/RCV_success, SND_rcv_current_ack/SND_success, SND_time_out_current. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **6.8 Fifth refinement** — introduces channel unreliability via activation bits $db$ (data), $ab$ (acknowledgment), $v$ (receiver), mutual-exclusion invariants; last-item indicator $l$; constant $MAX$ and retry counter $c$ (failure iff $c = MAX+1$); daemon events DMN_data_channel/DMN_ack_channel modeling message loss; SND_timer/RCV_timer events. : [[Case-Study-Bridge-and-Press-Controllers|Link1]], [[Case-Study-Communication-Protocols|Link2]]
- **6.9 Sixth refinement** — optimization sending only the parity of pointers $s$ and $r$ instead of full values (left as exercise). : [[Case-Study-Bridge-and-Press-Controllers|Link1]], [[Case-Study-Communication-Protocols|Link2]]

**Key Questions:**
1. Why must the receiver's timer delay be at least $(M+1)\times dl$, and how does this bound alone guarantee that the receiver never misdiagnoses an active sender as aborted?
2. Why is the fourth combination (receiver aborts, sender does not) provably impossible, given only requirements FUN-5 and FUN-6?
3. In the fifth refinement, why are events like SND_success and RCV_failure allowed to "cheat" by referencing the other participant's variables, and what proof obligation (convergence via variant) legitimizes this during refinement?

---

### Chapter 7: Development of a concurrent program (pp. 227–257)

**Summary:** Using H.R. Simpson's "Four-slot Fully Asynchronous Mechanism" (a lock-free writer/reader shared-memory protocol) as a running example, this chapter contrasts concurrent with distributed programming, shows why interleaving analysis is combinatorially infeasible, and develops a systematic Event-B refinement strategy — via writing/reading traces — that ends with one event per atomic instruction of the final concurrent program. : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]

**Key Definitions & Concepts by Section:**
- **7.1 Comparing distributed and concurrent programs** — distributed programs: cooperating agents on different computers achieving a shared goal via well-defined communication; concurrent programs: competing agents on the same computer sharing a resource, interruptible at points determined by hardware atomicity. : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
- **7.2 The proposed example** — Simpson's mechanism: shared variables $data \in \{0,1\}\to(\{0,1\}\to D)$, $reading$, $latest$, $slot$; Writer/Reader pidgin programs; non-concurrent animations showing the reader always reads the last written data, may repeat reads, and may miss writes; atomicity definition $pair\_w = reading \Rightarrow indx\_w \neq indx\_r$ (writer and reader never touch the same slot simultaneously). : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
- **7.3 Interleaving** — interleaving of Writer/Reader instructions; recurrence $U(m,n) = U(m-1,n)+U(m,n-1)$, $U(m,0)=U(0,n)=1$, computed via dynamic programming, showing the number of interleavings explodes (overflows `INT_MAX` already at $U(25,15)$), motivating a specification-based rather than case-enumeration approach.
- **7.4 Specifying the concurrent program** — writing trace $wt$ and reading trace $rd$; function $f$ (maps reading index to writing index, $rd = f\,;\,wt$); function $g$ (writing-trace position just before a given read); progress invariants $f(i)\le g(i)$ and $g(i)\le f(i+1)$; initial events write/read. : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
- **7.5 Refinement strategy** — plan: split write/read into per-instruction events using address counters $adr\_w \in 1..5$, $adr\_r \in 1..3$, matching the final Writer_1..5/Reader_1..3 events to the pidgin program's five/three instructions. : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
- **7.6 First refinement** — address counters introduced; reading trace forgotten in favor of $u = g(r)$, $m = f(r)$; reader split into Reader_1/2/3 (Reader_2 refines abstract read); writer's concrete trace $wtp$ (with $wt \subseteq wtp$) and split into Writer_1..3, Writer_41/42, Writer_51/52. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **7.7 Second refinement** — Simpson's data structures (reading, pair_w, latest, indx_r, indx_wp, slot, idata) introduced; idata holds a writing-trace index (not yet the final data value). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **7.8 Third refinement** — writing trace $wtp$ removed, replaced by variable $Data$ holding actual values (gluing invariant relates $wtp(idata(x)(y))$ to $Data(x)(y)$); Writer_41/42 and Writer_51/52 become identical (later merged). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **7.9 Fourth refinement** — final touch: $Data\to data$, $indx\_wp\to indx\_w$; Writer_1 split into Writer_1/2; invariant inv4_7 formalizes the no-simultaneous-read/write-at-same-slot atomicity condition required in §7.2.3. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]

**Key Questions:**
1. Why does the specification choose to define correctness via the relationship between writing and reading *traces* (with functions $f$ and $g$) rather than directly axiomatizing the shared-memory data structure?
2. Why is event Reader_2 — not Reader_3 — chosen to refine the abstract read event, and what does this choice reveal about what "the moment of reading" formally means in this model?
3. The chapter shows $U(m,n)$ grows explosively; what does this imply about the soundness of any verification strategy for concurrent programs based on exhaustive execution-trace enumeration versus the trace-invariant approach used here?

---

### Chapter 8: Development of electronic circuits (pp. 258–305)

**Summary:** This chapter presents a systematic Event-B methodology for developing deterministic, deadlock-free synchronous electronic circuits — modeling a circuit and its environment as alternating `cir`/`env` modes with dynamic (event-based) and static (invariant-based) views — then applies it to three worked examples: the Single Pulser, the (binary) Arbiter, and a road traffic light built from connected Priority and Light sub-circuits. : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]

**Key Definitions & Concepts by Section:**
- **8.1 Introduction** — synchronous circuit as a box with $cir\_state$, input/output lines, clock alternating low/high; coupling circuit and environment via alternating modes $mode \in \{env, cir\}$; dynamic view (cir_event_i / env_event_j guarded by $GC_i$/$GE_j$, acting via $PC_i$/$PE_j$); static view via conditions $C$ (established by circuit) and $D$ (established by environment); consistency conditions linking dynamics and statics; final construction conditions (all variables boolean, deadlock-free, internally deterministic, externally deterministic i.e. mutually exclusive guards, environment/circuit each touch only their own state plus the shared line); operator $bool(P)$ defined by $E = bool(P) \Leftrightarrow (P\Rightarrow E{=}TRUE)\wedge(\neg P \Rightarrow E{=}FALSE)$, used to merge deterministic guarded events into one circuit event. : [[Discrete-Transition-Systems|Link]]
- **8.2 First example: the Single Pulser** — informal spec (assert output for one clock pulse per button press); initial model with counters $push, pop, flash$ (invariants bounding their drift by 1); two deterministic refinements PULSER1 (flash as early as possible) and PULSER2 (flash as late as possible); concrete Boolean $input$/$output$/register $reg$; final merged circuits `PULSER1`/`PULSER2` with $output := bool(input=TRUE \wedge reg=FALSE)$ (etc.). : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
- **8.3 Second example: the Arbiter** — FUN-1–8 requirements (two inputs $i\_1,i\_2$, two outputs $o\_1,o\_2$; TRUE input = resource request; output TRUE only if input TRUE; mutual exclusion; bounded wait of at most one extra pulse; requester keeps requesting until served; no output without a request); initial model with request/ack counters $r_1,r_2,a_1,a_2$ and pending-flags $p_1,p_2$; deadlock-freedom theorem thm0_1; successive refinements introducing binary outputs $o_1,o_2$ (via $b\_2\_01$), then proper Boolean inputs $i_1,i_2$, then removing non-determinism (fixed winner on simultaneous request) with theorem thm3_1; final merged `arbiter` event. : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
- **8.4–8.5 Third example: road traffic light** — separation of concerns into a Priority circuit (decides when priority shifts between main/small road, via inputs $car$, $clk$ and outputs $chg$, $prt$, governed by Rules 1–4) and a Light circuit (sequences colors green→orange→red per Rules 5–6, with symmetric red split into $rd1$/$rd2$); IF-gate notation for predicates of shape $(P\wedge Q)\vee(\neg P\wedge R)$; upper (single-light) abstraction refined to add Lower circuit outputs for both roads, with safety theorems thm1_1/thm1_2 (red on one road iff green-or-orange on the other).

**Key Questions:**
1. Why must the environment be developed together with the circuit rather than the circuit being verified in isolation, and how do the static conditions $C$/$D$ plus the consistency proof obligations formalize this coupling?
2. In the merging construction of §8.1.7, why does mutual exclusion of the circuit guards ($GC_i \Rightarrow \neg GC_j$) suffice to prove that the merged event using $bool(\ldots)$ is a correct refinement of each individual $cir\_event_i$?
3. For the Pulser, what precisely distinguishes PULSER1 from PULSER2 as valid (but different) refinements of the same abstract non-deterministic specification, and why does the specification permit both?

---

### Chapter 9: Mathematical language (pp. 306–352)

**Summary:** A self-contained formal reference chapter defining the book's mathematical foundations: the sequent calculus and notion of proof, then a layered mathematical language (propositional → predicate → equality → set-theoretic → boolean/arithmetic), concluding with axiomatic definitions of advanced data structures (closures, graphs, lists, rings, trees) used throughout the rest of the book. : [[The-Sequent-Calculus-and-Logical-Inference|Link1]], [[The-Set-Theoretic-Mathematical-Language|Link2]]

**Key Definitions & Concepts by Section:**
- **9.1 Sequent calculus** — sequent: "something to prove"; inference rule with antecedent $A$ (finite set of sequents) and consequent $C$ (a single sequent), written $\dfrac{A}{C}\,R1$; theory: a set of inference rules; proof: a finite tree of nodes $(s,r)$ where $r$'s consequent is $s$ and $r$'s children are the antecedent sequents; sequent for the mathematical language written $H \vdash G$ ("goal $G$ holds under hypotheses $H$"); initial theory rules: $\text{HYP}$: $\dfrac{}{H,P\vdash P}$; $\text{MON}$: $\dfrac{H\vdash Q}{H,P\vdash Q}$; $\text{CUT}$: $\dfrac{H\vdash P \quad H,P\vdash Q}{H\vdash Q}$. : [[The-Sequent-Calculus-and-Logical-Inference|Link]]
- **9.2 The propositional language** — syntax: $predicate ::= \bot \mid \neg predicate \mid predicate \wedge predicate \mid predicate \vee predicate \mid predicate \Rightarrow predicate$ (later $\top$, $\Leftrightarrow$ added); left/right rules for each connective (FALSE_L/R, NOT_L/R, AND_L/R, OR_L/R, IMP_L/R); derived rule $\text{CASE}$: $\dfrac{H,Q\vdash P \quad H,\neg Q\vdash P}{H\vdash P}$; generalized rules $\text{CT\_L}$, $\text{CT\_R}$; $\top \equiv \neg\bot$, $P\Leftrightarrow Q \equiv (P\Rightarrow Q)\wedge(Q\Rightarrow P)$. : [[The-Sequent-Calculus-and-Logical-Inference|Link]]
- **9.3 The predicate language** — adds variables, expressions ($E\to F$ pairing), universal/existential quantification $\forall x\cdot P$, $\exists x\cdot P$; rules $\text{ALL\_L}$: $\dfrac{H,\forall x\cdot P,[x:=E]P \vdash Q}{H,\forall x\cdot P \vdash Q}$; $\text{ALL\_R}$: $\dfrac{H\vdash P}{H\vdash \forall x\cdot P}$ ($x$ not free in $H$); $\text{XST\_L}$, $\text{XST\_R}$ (dual, with matching side conditions); derived rule $\text{CUT\_XST}$.
- **9.4 Introducing equality** — $E = F$; rules $\text{EQ\_LR}$, $\text{EQ\_RL}$ (substitute using an equality hypothesis in either direction); rewriting rules $E=E \rightsquigarrow \top$, $E\to F = G\to H \rightsquigarrow E=G \wedge F=H$; "one point rules" $\forall x\cdot x{=}E\Rightarrow P \rightsquigarrow [x:=E]P$ and $\exists x\cdot x{=}E\wedge P \rightsquigarrow [x:=E]P$.
- **9.5 The set-theoretic language** — membership $E\in S$; Cartesian product $S\times T$, power set $\mathbb{P}(S)$, set comprehension $\{x\cdot P \mid E\}$; extensionality axiom $S=T \rightsquigarrow S\in\mathbb{P}(T)\wedge T\in\mathbb{P}(S)$; elementary operators $\subseteq, \cup, \cap, \setminus$, set extension $\{a,\dots,b\}$, $\emptyset$; generalized union/intersection $\bigcup(S)$, $\bigcap(S)$ and quantified forms; binary relation operators $S\leftrightarrow T$, $dom$, $ran$, total/surjective/bijective relation sets ($S\twoheadleftrightarrow T$ etc.), converse $r^{-1}$, domain/range restriction and subtraction ($S\lhd r$, $r\rhd T$, $S\lhd\!\!-\, r$, $r\rhd\!\!-\, T$), relational image $r[U]$, forward/backward composition ($f\,;\,g$, $g\circ f$), overriding $f\,\overline{\lhd}\, g$, direct product $\otimes$, parallel product $\parallel$; function operator sets: partial/total functions ($S\to T$, $S\twoheadrightarrow T$, $S\rightarrowtail T$ etc.), injections, surjections, bijections; identity $id$; projections $prj_1$, $prj_2$; lambda abstraction $\lambda x\cdot P \mid E$ and function invocation $f(E)$ with well-definedness condition $f^{-1}\,;\,f\subseteq id \wedge E\in dom(f)$. : [[The-Set-Theoretic-Mathematical-Language|Link]]
- **9.6 Boolean and arithmetic language** — $BOOL=\{TRUE,FALSE\}$, $TRUE\neq FALSE$; Peano-style axioms for $\mathbb{N}$ via $0$ and bijective $succ$; recursive definitions of $+$, $*$, exponentiation; comparison operators $\le,<,\ge,>$; interval $a..b$; subtraction, division, modulo (with well-definedness conditions, e.g. $a/b$ requires $b\neq 0$); $finite(s)$, $card(s)$, $max(s)$, $min(s)$ (all with well-definedness conditions). : [[The-Set-Theoretic-Mathematical-Language|Link]]
- **9.7 Advanced data structures** — irreflexive transitive closure $cl(r)$ (smallest relation containing $r$ closed under composition with $r$); strongly connected graphs (defined via $cl(r)$, and equivalently via $\forall S\cdot S\neq\emptyset \wedge r[S]\subseteq S \Rightarrow V\subseteq S$); infinite lists (bijection $n: V \rightarrowtail V\setminus\{f\}$, no-cycle axiom $\forall S\cdot S\subseteq n[S]\Rightarrow S=\emptyset$) with derived list-induction rule $\text{IND\_LIST}$; finite lists (bijection between $f$ and $l$); rings (bijection that is strongly connected); infinite trees (parent function $p$, top $t$) with tree-induction rule $\text{IND\_TREE}$; finite-depth trees (leaves set $L$); free trees (symmetric, irreflexive, connected, acyclic graph $g$, with an auxiliary asymmetric sub-relation $h$ to eliminate the symmetry when proving acyclicity); well-founded relations/DAGs mentioned as a generalization left to the reader. : [[Advanced-Data-Structures|Link]]

**Key Questions:**
1. How does the tree structure of a "proof" (§9.1.1) relate to the notion of an inference-rule theory, and why must every leaf of a proof tree correspond to a rule with an empty antecedent?
2. Why is the "one point rule" for set comprehension ($E\in\{x\mid P\}\rightsquigarrow[x:=E]P$) only a special case of the general set-comprehension rewriting rule, and what side condition ($x$ not free in $E$) makes the general form necessary?
3. What distinguishes the axiomatization of a ring from that of an infinite list or a free tree (in terms of which "no backward chain / no cycle" axiom is used), and how does thm_1 of §9.7.5 relate ring-connectivity back to the general strongly-connected-graph characterization of §9.7.2?

---

### Chapter 10: Leader election on a ring-shaped network (pp. 353–366)

**Summary:** A distributed leader-election protocol for agents arranged on a unidirectional, buffered, re-orderable ring, where the leader must be the agent with the largest name; the chapter builds this via a non-deterministic abstraction and one refinement that formalizes an informal "names moving through buffers" argument, with full semi-formal proofs (SIM, INV, variant, deadlock-freeness). : [[Case-Study-Distributed-Network-Algorithms|Link]]

**Key Definitions & Concepts by Section:**
- **10.1 Requirement document** — ENV-1 (finite oriented ring of nodes), ENV-2 (each node sends to the next), ENV-3 (messages buffered per node), ENV-4 (messages can be re-ordered in buffer), ENV-5 (same code at every node — homogeneity), FUN-1 (a unique node must be elected leader), ENV-6 (node names are distinct natural numbers), FUN-2 (leader = node with largest name). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Communication-Protocols|Link2]], [[Formal-Methods-and-the-Modeling-Philosophy|Link3]]
- **10.2 Initial model** — constant $N$ (finite non-empty set of names), variable $w$ (winner), event `elect` sets $w := \max(N)$ in one shot. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **10.3 Discussion** — three informal attempts to solve the problem (forward-all-names; count $n$ known nodes; forward-only-if-greater), converging on an informal proof by defining a partial function $a$ ("the buffer function") linking a name $x$ to the agent $a(x)$ still holding it, and the key lemma: for $x \in \text{dom}(a)$, $x$ is the maximum of the ring interval from $x$ to $n^{-1}(a(x))$.
- **10.4 First refinement** — ring formalized via bijection $n$ (next-node function) and interval operator $\texttt{itvr}(x)(y)$ (borrowed from Ch.9 §7.5); variable $a$ (partial function $N \to N$, invariant inv1_2: $\forall f \in \text{dom}(a) \cdot f = \max(\texttt{itvr}(f)(n^{-1}(a(f))))$); events `elect` (refined, parameterized), `accept` (moves $x$ forward: $a(x) := n(a(x))$ when $a(x) < x$), `reject` (eliminates $x$ from domain when $x < a(x)$). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **10.5 Proofs** — proof of `elect` via rule SIM; proof of `accept` preserving inv1_1/inv1_2 via rule INV, case split on the overriding operator; convergence variant $\texttt{variant1} = \sum_{x \in \text{dom}(a)} \texttt{card}(\texttt{itvr}(a(x))(x))$; deadlock-freeness relies on new invariant $\text{dom}(a) \neq \emptyset$ (inv1_3).

**Key Questions:**
1. Why does the "obvious" first attempt (each agent waits until it sees its own name return) fail once messages can be re-ordered in buffers (ENV-4), and how does the "transmit only if strictly greater" strategy sidestep this without needing agents to know the ring size $n$?
2. What is the semantic role of the partial function $a$ — why must it be a function at all (rather than a relation), and how does invariant inv1_2 encode the entire correctness argument for "election by comparison"?
3. Why is it advantageous to replace the decrease of a cardinal-valued variant with the strict set-inclusion decrease of $\{x \to y \mid x \in \text{dom}(a) \land y \in \texttt{itvr}(a(x))(x)\}$ when proving convergence of `accept`/`reject`?

---

### Chapter 11: Synchronizing a tree-shaped network (pp. 367–386)

**Summary:** Develops a phase-synchronization algorithm on a finite tree where every process must stay within one phase of every other, progressively localizing a globally-quantified guard into neighbor-only comparisons using two counters (ascending/descending waves) and finally a parity encoding, all justified via tree induction (IND_TREE). : [[Case-Study-Distributed-Network-Algorithms|Link]]

**Key Definitions & Concepts by Section:**
- **11.1 Introduction** — ENV-1 (finite tree of nodes), FUN-1 (each node has a natural-number counter = phase), FUN-2 (any two counters differ by at most 1), FUN-3 (a node reads only its immediate neighbors' counters), FUN-4 (a node modifies only its own counter); notes that early abstractions may violate the locality constraint FUN-3, to be fixed by later refinement. : [[Discrete-Transition-Systems|Link]]
- **11.2 Initial model** — variable $c \in N \to \mathbb{N}$ (counter function), inv0_2: $\forall x,y \cdot c(x) \le c(y)+1$ (synchronization invariant); event `increment` (renamed `ascending` later) fires on node $n$ when $c(n) \le c(m)$ for all $m$ — a globally-quantified guard. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **11.3 First refinement** — tree defined via root $r$, leaves $L$, parent function $f$ (constants borrowed from Ch.9 §9.7.7), tree induction rule IND_TREE; invariant inv1_1: $\forall m \ne r \cdot c(f(m)) \le c(m)$ (ascending wave); theorem thm1_1: $c(r) \le c(m)$ for all $m$, proved by tree induction; event `ascending` refines `increment` with guard localized to $c(n)=c(r)$ and comparison to children only (still touches root $r$, not fully local). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **11.4 Second refinement** — introduces second counter $d$ (descending wave) with own invariant inv2_2 (diff $\le 1$); event `descending` increments $d(n)$ when it's the local minimum, mirroring `increment`'s structure. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **11.5 Third refinement** — invariants inv3_1 ($d(m) \le d(f(m))$), inv3_2 ($d(r) \le c(r)$), inv3_3 ($c(n) \in d(n)..d(n)+1$, the key connecting invariant); `ascending`'s guard becomes fully local: $c(n)=d(n)$ (proved to imply $c(n)=c(r)$ via thm1_2/thm3_1/thm3_4); `descending` splits into `descending_1` (non-root node, guard $d(n)=d(f(n))$) and `descending_2` (root, guard $d(r)=c(r)$) — both now local per FUN-3. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **11.6 Fourth refinement** — observes all guards only ever compare values that differ by at most 1 (table of justifying theorems: inv3_3, thm1_3, thm3_2, thm3_4), so replaces counters $c,d$ by their parities $p,q \in N \to \{0,1\}$ (functions `parity`), giving bounded-state final events (echoes the file-transfer/bounded-retransmission parity trick from Chapters 4/6). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]

**Key Questions:**
1. How does the pair of invariants inv1_1 ($c(f(m)) \le c(m)$) and the tree induction rule IND_TREE jointly establish the global property $c(r) \le c(m)$ for every node, and why is tree induction the natural proof technique here (versus, say, well-founded induction on a linear order)?
2. What is the precise role of invariant inv3_3 ($c(n) \in d(n)..d(n)+1$) in bridging the ascending and descending waves, and why does it make the parity replacement in Section 11.6 sound?
3. Why does splitting the abstract `descending` event into `descending_1`/`descending_2` (rather than keeping one parameterized event) become necessary once the FUN-3 locality constraint is enforced on the root?

---

### Chapter 12: Routing algorithm for a mobile agent (pp. 387–405)

**Summary:** Constructs a message-routing protocol that lets fixed sites forward messages toward a mobile agent M whose location changes over time, progressing from an idealized instantaneous-knowledge model through a dynamically-changing tree of forwarding pointers to a realistic model using logical clocks and timestamped service messages to prevent stale/out-of-order updates from creating routing cycles. : [[Case-Study-Distributed-Network-Algorithms|Link]]

**Key Definitions & Concepts by Section:**
- **12.1 Informal description** — successive informal refinements: (1) fixed agents instantly know M's location; (2) only M's *previous* site knows, forming a dynamic tree of forwarding channels rooted at M's current site; (3) service messages (informing a site of M's new location) travel non-instantaneously and can arrive out of order, creating a contention/cycle hazard; (4) solution: M carries a logical clock, stamps each service message with a timestamp, and receiving sites discard stamps not exceeding their locally recorded last-visit time. : [[Case-Study-Distributed-Network-Algorithms|Link1]], [[Formal-Methods-and-the-Modeling-Philosophy|Link2]]
- **12.2 Initial model** — carrier sets $S$ (sites), $M$ (messages); constant $il$ (initial location); variables $l$ (mobile's location), $c \in S\setminus\{l\} \to S$ (forwarding channel, a tree rooted at $l$), $p$ (partial function, message pool); tree invariant inv0_4: $\forall T \cdot T \subseteq c^{-1}[T] \Rightarrow T=\emptyset$; events `rcv_agt` (mobile moves instantaneously), `snd_msg`, `fwd_msg`, `dlv_msg`. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **12.3 First refinement** — mobile's move split into `leave_agt` and `rcv_agt` (no longer instantaneous); new variable $d$ (concrete channel, only updated on receipt of a service message) and $a$ (the "magic" service channel, a partial function that always keeps at most one pending service message per destination — inv1_3: $c = d \mathbin{\lhd} a$); $da$ tracks sites awaiting a service message (inv1_4). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **12.4 Second refinement** — implements the "magic" of $a$ concretely via a logical clock $k \in \mathbb{N}$, per-site last-visit time $t \in S \to \mathbb{N}$, and a richer service channel $b \in S \to (\mathbb{N} \to S)$ holding possibly many stamped pending messages per site; key invariants: inv2_4 (abstract $a(s)$ = the max-timestamped entry of $b(s)$), inv2_9 (if a message's stamp exceeds $t(s)$, it is guaranteed to be the maximum pending one — the correctness core of the timestamp filter), inv2_6–inv2_8 (clock/time bookkeeping); events `rcv_agt` increments $k$ and records $t$; `rcv_srv` accepts a service message only if its stamp exceeds $t(s)$. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **12.5 Third refinement (data refinement)** — replaces the set $da$ by a Boolean function $dab \in S \to \texttt{BOOL}$ (inv3_2), localizing the "awaiting service message" information per site. : [[Case-Study-Distributed-Network-Algorithms|Link]]
- **12.6 Fourth refinement** — left as an exercise (implementing effective migration of forwarded messages). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]

**Key Questions:**
1. Why is the abstract service channel $a$ (Section 12.3) described as having "magic" behavior — specifically, why must inserting $\{l \to s\}$ into $a$ silently discard any prior pending pair with the same first component, and what real-world failure (illustrated in Figs. 12.4–12.6) does this magic prevent?
2. How exactly does invariant inv2_9 ($t(s) < n \Rightarrow n = \max(\text{dom}(b(s)))$) let a site determine, using only local information, that an arriving service message is the most recent one — without ever seeing the full set of pending messages?
3. What is the essential difference between the tree structure in Chapter 11 (static, given by axioms) and the one here (dynamically re-rooted at the mobile's current location, an invariant rather than an axiom) — how does that difference show up in the proof obligations?

---

### Chapter 13: Leader election on a connected graph network (pp. 406–416)

**Summary:** Models the IEEE-1394 leader-election protocol on a free-tree network topology, progressively refining an abstract "elect any node" event into a fully distributed, message-based algorithm that removes non-leader ("outer") nodes one at a time, and finally addresses the symmetric contention problem (two candidates racing) via a virtual contention channel and randomized-timer daemon. : [[Case-Study-Distributed-Network-Algorithms|Link]]

**Key Definitions & Concepts by Section:**
- **13.1 Initial model** — finite set $N$ of nodes; variable $l$; event `elect` picks $l$ non-deterministically ($l :\in N$) — a placeholder for the eventual result. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **13.2 First refinement** — constant graph $g$ axiomatized as a free tree (irreflexive, symmetric, connected with no proper closed subset — axm1_1–axm1_5, borrowed from Ch.9 §7.8); variable $n \subseteq N$ (candidate set, shrinking); invariant inv1_2 (the induced subgraph on $n$ remains a free tree); event `progress` (status: convergent) removes an outer node $x$ (a node with exactly one neighbor in the shrinking subtree) from $n$; `elect` fires when $n = \{x\}$. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **13.3 Second refinement** — introduces message channel $m$ (partial function $n \to n$, $m \subseteq g$); event `send_msg` (outer node $x$ sends to its unique remaining neighbor $y$); `progress` refined to require receipt of the message ($x \to y \in m$) and that $y$ itself hasn't sent ($y \notin \text{dom}(m)$). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **13.4 Third refinement (contention)** — the symmetric case where both $x \to y$ and $y \to x \in m$ (both think the other is the outer node) is unresolvable by the base protocol; introduces contention channel $c$ and set $bm = \text{dom}(m \cup c)$; new events `discover_contention` and `solve_contention`; informal description of the real IEEE-1394 solution using randomized/short-vs-long timer delays to break symmetry with probability 1 (in the limit). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **13.5 Fourth refinement (simplification)** — data-refines by replacing $n$ with function $d \in n \to \mathbb{P}(n)$, $d(x) = g[\{x\}] \cap n$ (a node's current neighbor set within the shrinking subgraph), simplifying the guard $g[\{x\}] \cap n = \{y\}$. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **13.6 Fifth refinement (cardinality)** — replaces the singleton/empty test on $d(x)$ with an integer counter $r(x) = \texttt{card}(d(x))$, checked via $r(x)=1$ or $r(x)=0$ instead of set operations — a pure efficiency-oriented data refinement. : [[Case-Study-Bridge-and-Press-Controllers|Link1]], [[Case-Study-Communication-Protocols|Link2]], [[Case-Study-Distributed-Network-Algorithms|Link3]]

**Key Questions:**
1. Why is the connected-graph network required to be specifically a free tree (irreflexive, symmetric, no proper closed subset) rather than an arbitrary connected graph, and how does that structural guarantee underpin the existence of "outer nodes" used to drive `progress`?
2. What exactly is the contention scenario formalized in Section 13.4, why can no local deterministic rule resolve it without external randomness/timers, and how does the model's introduction of channel $c$ capture "both nodes have discovered the symmetric conflict" without modeling probability directly in Event-B?
3. Across the fourth and fifth refinements, how do the data refinements ($d$, then $r$) preserve the exact same guard semantics while eliminating repeated recomputation of $g[\{x\}] \cap n$ — what proof obligations must be discharged to certify this transformation is faithful?

---

### Chapter 14: Mathematical models for proof obligations (pp. 417–445)

**Summary:** Provides the formal set-theoretic semantics underlying every proof obligation rule used throughout the book (INV, FIS, GRD, SIM, DLF, MRG, NAT, VAR, FIN, WFIS, THM, WD), first for plain invariant preservation and then for general (data) refinement via trace semantics and forward/backward simulation. : [[Proof-Obligation-Rules|Link]]

**Key Definitions & Concepts by Section:**
- **14.1 Introduction** — table mapping proof obligation rules (INV, FIS, GRD, MRG, SIM, NAT, FIN, VAR, WFIS, THM, WD, DLF) to their formal treatment location in this chapter vs. their informal introduction in Chapter 5. : [[Discrete-Transition-Systems|Link]]
- **14.2 Proof obligation rules for invariant preservation** — model as $S = \{v \mid I(v)\}$ (state space cut by invariant), $L = \{v \mid K(v)\}$ (initializing set, from after-predicate $K(v')$), $a_{e_i} = \{v \to v' \mid I(v) \land G_i(v) \land R_i(v,v')\}$ (event transition relation, from guard $G_i$ and before-after predicate $R_i$). Requirements $L \subseteq S$, $L \neq \emptyset$, $a_{e_i} \in S \leftrightarrow S$ translate directly into: : [[Proof-Obligation-Rules|Link]]
  $$\text{FIS (init)}:\ \exists v \cdot K(v) \qquad \text{INV (init)}:\ K(v) \vdash I(v)$$
  $$\text{FIS (event)}:\ I(v),\,G_i(v) \vdash \exists v' \cdot R_i(v,v') \qquad \text{INV (event)}:\ I(v),\,G_i(v),\,R_i(v,v') \vdash I(v')$$
  Deadlock-freeness: with global relation $a_e = a_{e_1}\cup\cdots\cup a_{e_n}$, requiring $\text{dom}(a_e) = S$ gives $\text{DLF}:\ I(v) \vdash G_1(v)\lor\cdots\lor G_n(v)$.
- **14.3 Traces** — a trace is a finite, non-empty recorded sequence of observed states, starting in the initial set and consecutively related by the events' before-after predicates; illustrated via the action/weak-reaction pattern and its graph of evolution. Formal definition: given carrier set $S$, initializing set $L$, transition relation $a_e$,
  $$n \to t \in T(L \to a_e) \iff n \in \mathbb{N}_1 \land t \in 1..n \to S \land t(1) \in L \land \forall i \in 1..n{-}1 \cdot t(i)\to t(i{+}1) \in a_e.$$
  Every non-empty prefix of a trace is itself a trace.
- **14.4 Simple refinement by traces** — illustrated via action/strong-reaction; a refined model's traces must all be traces of the abstraction, and it must not introduce deadlocks not present in the abstraction ("relative deadlock freedom"). Formal sufficient conditions (I): $M \subseteq L$, $M \neq \emptyset$, $re \subseteq ae$, $\text{dom}(ae) \subseteq \text{dom}(re)$; refined per-event as conditions (II). Introduces external/internal variables: only the projection of state onto an external set $E$ (via total function $f \in S \to E$) is compared for refinement purposes (conditions III, using relation composition $f^{-1}\,;\,re_i\,;\,f \subseteq f^{-1}\,;\,ae_i\,;\,f$). : [[Refinement-Theory|Link]]
- **14.5 General refinement set-theoretic representation** — full data refinement: abstract state space $S$ projects via $f$ to external set $E$; concrete space $T$ projects via $g$ to external set $F$; a total function $h \in F \to E$ relates the external sets (reconstructs abstract observations from concrete ones). Formal refinement definition (IV): $g[M] \subseteq h^{-1}[f[L]]$, $M\neq\emptyset$, $g^{-1}\,;\,re_i\,;\,g \subseteq h\,;\,f^{-1}\,;\,ae_i\,;\,f\,;\,h^{-1}$, and a domain condition. Forward simulation: gluing invariant $r \in T \leftrightarrow S$ (total relation) satisfying : [[Case-Study-Communication-Protocols|Link]]
  $$C1:\ r^{-1}\,;\,g \subseteq f\,;\,h^{-1}\qquad C2:\ r^{-1}\,;\,re_i \subseteq ae_i\,;\,r^{-1}\qquad C3:\ g^{-1}\subseteq h\,;\,f^{-1}\,;\,r^{-1}$$
  are sufficient for refinement (C3 derivable from C1 given $r$ total); condition $C2$, instantiated against the standard `with`-clause event pattern ($H_i(w)$ guard, witness $P(v',w,w')$, before-after $S_i(w,w')$), decomposes exactly into rules GRD, WFIS, SIM, INV for refinement, plus relative-deadlock rule DLF. Backward simulation gives an alternate condition $C2'$: $r^{-1}\,;\,re_i^{-1} \subseteq ae_i^{-1}\,;\,r^{-1}$ (not used further in the book). Section 14.5.5 shows forward simulation composes across trace steps ($a_{e_i}\,;\,a_{e_j}$ refined by $re_i\,;\,re_j$).
- **14.6 Breaking the one-to-one relationship between abstract and concrete events** — splitting (one abstract event refined by several concrete ones, each proved to refine it); merging (several abstract events $ae_i, ae_j$ merged into one concrete event refining $ae_i \cup ae_j$, yielding rule MRG: $I(v), R(v) \vdash P(v)\lor Q(v)$); new events (no abstract counterpart, must refine `skip`: $r^{-1}\,;\,ne_k \subseteq r^{-1}$), requiring adapted INV, modified DLF (guards of new events added to the disjunction), and convergence rules NAT/VAR (a natural-number variant $V(w)$ strictly decreases) or FIN (a finite set $S(w)$ strictly shrinks) to bound how many new events may fire between two "old" events.

**Key Questions:**
1. How does the set-theoretic construction $a_{e_i} = \{v \to v' \mid I(v)\land G_i(v)\land R_i(v,v')\}$ mechanically force the FIS and INV proof obligations to be exactly what they are — i.e., in what precise sense are FIS and INV *not* independent design choices but forced consequences of defining "invariant preservation" as $a_{e_i} \in S \leftrightarrow S$?
2. Why is "the set of refined traces is a subset of the set of abstract traces" too strong a definition of refinement on its own (admitting an empty-trace refinement of anything), and how do relative deadlock freedom plus $M \neq \emptyset$ repair this?
3. In the forward simulation conditions C1–C3, what is the specific role of $r$ being a total relation (as opposed to merely a relation) in deriving C3 from C1, and why does this matter for guaranteeing that every concrete state has a corresponding abstract state under the gluing invariant?

---

### Chapter 15: Development of sequential programs (pp. 446–480)

**Summary:** This chapter presents a systematic Event-B method for deriving sequential imperative programs (loops, conditionals) from formal specifications, via anticipated/convergent event refinement followed by mechanical "merging rules," and illustrates the method on nine worked examples (searching, sorting, reversing, numerical algorithms). : [[Sequential-Program-Derivation|Link]]

**Key Definitions & Concepts by Section:**
- **15.1 A systematic approach to sequential program development** — sequential program (assignments glued by sequencing, while, if), naked events (guarded actions with scheduling left to an implicit hidden scheduler), Hoare-triple $\{Pre\}\ P\ \{Post\}$ (pre-condition encoded as axioms on constants, post-condition as guards of a final skip event), three-phase approach (specification phase with an anticipated event, development phase adding/refining events, merging phase combining events into one program). : [[Sequential-Program-Derivation|Link]]
- **15.2 A very simple example** — search program specification (find index $r$ with $f(r)=v$), progress anticipated event (non-deterministic placeholder later made convergent), refinement narrowing invariant $v \notin f[1..r-1]$ with variant $n-r$.
- **15.3 Merging rules** — M_IF (merges two complementary-guarded events into an if-statement), M_WHILE (merges a convergent "body" event with its complement into a while loop; requires the body event to be new/convergent one refinement level below and to preserve the common guard), M_ELSIF (variant of M_IF combining with a nested if), M_INIT (prepends the initialization event to the final merged pseudo-event). : [[Sequential-Program-Derivation|Link]]
- **15.4 Example: binary search in a sorted array** — introduces two moving bounds $p,q$ narrowing the search interval, convergent events inc/dec refining an anticipated progress event, final merged program using $(1+n)/2$ midpoint selection. : [[Sequential-Program-Derivation|Link]]
- **15.5 Example: minimum of an array of natural numbers** — indices $p \le q$ narrowing toward the minimum via comparison of $f(p)$ and $f(q)$.
- **15.6 Example: array partitioning** — Quicksort-style partition around pivot $x$ using indices $k,j$ and array swap notation, three convergent events (progress_1/2/3) refining one anticipated event.
- **15.7 Example: simple sorting** — selection-sort-style development with sorted prefix, index $k$, and nested search for the minimum (index $l$, then $j$) via a doubly-nested loop after merging. : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
- **15.8 Example: array reversing** — two converging indices $i,j$ swapping elements, invariant $i+j=n+1$.
- **15.9 Example: reversing a linked list** — pointer-based (not array-based) development using chain relations, irreflexive transitive closure $cl$, successive refinements introducing chains $a,b$, then $bn$/nil sentinel, then a single chain $e$.
- **15.10 Example: simple numerical program computing the square root** — computes integer square root by defect ($r^2 \le n < (r+1)^2$) via incremental loop, then optimized via incremental update of $(r+1)^2$ and $2r+3$ to avoid recomputation.
- **15.11 Example: the inverse of an injective numerical function** — generalizes binary search to invert any strictly increasing function $f$; includes instantiation to derive square-root and integer-division programs "for free" from the generic development.

**Key Questions:**
1. Why must the "body" event of a while-loop merge (M_WHILE) be convergent one refinement level below the level of the guard-negation event, and how does this guarantee loop termination in the final program?
2. In what sense is the naked-events approach "essentially one where we favor an initial implicit distribution of the computation over a centralized explicit one," and why does deferring scheduling to the merging phase make development easier than transforming a single monolithic specification formula?
3. How does the instantiation technique in Section 15.11 let two very different-looking programs (square root, integer division) be derived "for free" from a single generic refinement — what properties must an instantiated constant satisfy?

---

### Chapter 16: A location access controller (pp. 481–507)

**Summary:** This chapter develops a complete access-control system (people, locations, card readers, turnstiles/doors) through an informal requirements document followed by four refinements, and uses the proof process itself to discover missing safety requirements (deadlock/blockage) not present in the original informal specification. : [[Case-Study-Bridge-and-Press-Controllers|Link1]], [[Design-Patterns-for-Reactive-Controllers|Link2]], [[Case-Study-Access-Control-and-Train-Systems|Link3]]

**Key Definitions & Concepts by Section:**
- **16.1 Requirement document** — requirements taxonomy FUN (functional), EQP (equipment); people/locations, permanent authorization ($aut$), magnetic cards, card readers with green/red lights, one-way turnstiles, timing rules (30s green window, 2s red refusal). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Communication-Protocols|Link2]], [[Formal-Methods-and-the-Modeling-Philosophy|Link3]]
- **16.2 Discussion** — sharing out of control (decentralized vs. centralized), closed model construction, behavior-of-equipment assumptions, safety questions (can people be blocked forever?), synchronization problems (timing gaps between events), functioning at the limits (hostile/abnormal user behavior).
- **16.3 Initial model of the system** — carrier sets $P$ (people), $L$ (locations) plus special location $out$; constant $aut \in P \leftrightarrow L$; variable $sit \in P \to L$ (invariant $sit \subseteq aut$, formalizing FUN-3); single abstract event pass. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **16.4 First refinement** — constant $com \in L \leftrightarrow L$ (direct communication between locations); refined pass event requiring $sit(p) \to l \in com$; deadlock freeness proof failure reveals SAF-1 ("no person must remain blocked in a location"); derived invariant conditions leading to SAF-2 (authorized exit via a communicating location) and, via a tree-structured exit function, SAF-3 (authorized path all the way to outside); revisits deadlock freeness for people outside (entry guarantee, axm1_7). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **16.5 Second refinement** — introduces doors (carrier set $D$, functions $org$, $dst$), variable $dap$ (person-door temporary connection), $grn$/$red$ (lit-door sets), new events accept/refuse/off_grn/off_red; proof obligation splits into "pass not less often" (provable) and "new events cannot indefinitely block pass" (impossible to prove — risk of permanent obstruction); discusses and rejects two mitigation proposals (forcing compliance, confiscating cards) in favor of accepting the residual risk as an explicit, documented decision. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **16.6 Third refinement** — introduces card readers as physical devices; blocked-reader set $BLR$, message channels $mCard$ (card→system) and $mAckn$ (acknowledgement); new physical events CARD and ACKN; partition invariants (inv3_4–inv3_6) tracking message progression. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **16.7 Fourth refinement** — introduces physical door hardware: green chain ($mAccept$, $GRN$, $mOff\_grn$, $mPass$) and red chain ($mRefuse$, $RED$, $mOff\_red$); new physical events ACCEPT, PASS, OFF_GRN, REFUSE, OFF_RED; explicit gap between logical acceptance (software) and physical acceptance (hardware) as a paradigm of distributed-systems reasoning. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]

**Key Questions:**
1. Why is the proof that "the pass event does not happen less often than its abstraction" straightforward, while the proof that "new events (refuse, off_grn) cannot indefinitely block pass" is described as "quite simply impossible" — and what does the author's final decision to accept this risk (rather than force compliance or confiscate cards) reveal about the limits of formal proof versus engineering judgment?
2. How does the failed deadlock-freeness proof in Section 16.4.2 mechanically derive SAF-1, SAF-2, and eventually SAF-3 — turning a proof obligation failure into a discovered requirement rather than a modeling error?
3. What is the significance of maintaining a clear separation between "physical" (uppercase) and "logical" (lowercase) variables/events throughout the refinements, and why must physical events' guards eventually depend only on physical variables?

---

### Chapter 17: Train system (pp. 508–549)

**Summary:** This chapter presents a large case study modeling a train-network safety controller, giving a highly detailed informal requirements document (environment, functional, safety, movement, train, and failure requirements) followed by an initial model and four refinements that progressively introduce physical tracks, route readiness, signals, and points, always keeping the software model synchronized with a model of its physical environment. : [[Case-Study-Access-Control-and-Train-Systems|Link]]

**Key Definitions & Concepts by Section:**
- **17.1 Informal introduction** — requirement taxonomy ENV/FUN/SAF/MVT/TRN/FLR; points (left/right/unknown positions, direct/diverted track), crossings, blocks (occupied/unoccupied via track circuits), routes (ordered sequences of adjacent blocks with distinctness/continuity/no-cycle properties, first/last block uniqueness constraints ENV-8/9), signals (red/green, protecting a route's first block, auto-reset to red — ENV-15), route/block reservation process in three phases (block reservation, point positioning/route formation, signal-to-green), safety conditions (SAF-1 block reserved for at most one route, SAF-2 green signal only when reserved+unoccupied+points positioned, SAF-3 points repositioned only on reserved-not-formed routes, SAF-4 no occupied blocks on a reserved-not-formed route), moving conditions (MVT-1/2/3 progressive freeing of blocks/routes), train assumptions (TRN-1 no splitting, TRN-2 no backward movement, TRN-3 no mid-route entry, TRN-4 no mid-route disappearance), failure handling (FLR-1..5, automatic train protection system, mechanical bindings, track-circuit reporting delay). : [[Case-Study-Distributed-Network-Algorithms|Link]]
- **17.2 Refinement strategy** — 39 total requirements across six categories; stepwise plan: logical blocks/routes → physical blocks → route readiness (abstract green) → physical signals → points. : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
- **17.3 Initial model** — carrier sets $B$ (blocks), $R$ (routes); constants $rtbl$ (block-route relation), $nxt$ (block succession per route, injective), $fst$/$lst$ (first/last block functions) with continuity/no-cycle axioms (axm0_8, axm0_9) and non-overlap axioms (axm0_10/11); logical variables $resrt$ (reserved routes), $resbl$ (reserved blocks), $rsrtbl$ (reserved-block→reserved-route function), physical variable $OCC$ (occupied blocks); partition of a reserved route's blocks into free/occupied/reserved-unoccupied regions ($M,N,P$) with monotone-transition invariants; events route_reservation, route_freeing, FRONT_MOVE_1, FRONT_MOVE_2, BACK_MOVE. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **17.4 First refinement** — physical variables $TRK$ (physical track succession, partial injection), $frm$ (formed routes), $LBT$ (last blocks of trains); key invariant inv1_6 linking logical succession $nxt(r)$ to physical $TRK$ on formed routes; new events point_positioning and route_formation; BACK_MOVE split into BACK_MOVE_1/2; discussion of physical vs. logical variable/event separation (Remarks 1–3). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **17.5 Second refinement** — variable $rdy$ (ready routes: formed, fully reserved, fully unoccupied); route_formation extended to add readiness; FRONT_MOVE_1 strengthened to require $r \in rdy$. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **17.6 Third refinement** — carrier set $S$ (signals), constant $SIG$ (bijection from first-blocks to signals); variable $GRN$ (green signals) data-refining $rdy$; route_formation now turns the signal green; FRONT_MOVE_1 now reacts to a green signal (physical condition), realizing ENV-13/15. : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **17.7 Fourth refinement** — constants $blpt$ (blocks with points), $lft$/$rht$ (point connections), functionality constraints per route (axm4_5–7); point_positioning revisited; notes remaining unfinished refinements (decomposing route_reservation/formation/point_positioning into atomic loop-driving events). : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Case-Study-Bridge-and-Press-Controllers|Link2]], [[Case-Study-Communication-Protocols|Link3]], [[Case-Study-Distributed-Network-Algorithms|Link4]]
- **17.8–17.9 Conclusion / References** — discusses fault prevention vs. fault tolerance emphasis, notes FLR-1/3 addressed by automatic train protection, FLR-4/5 left untreated (would require a stop-and-inspect recovery phase), and situates the work relative to prior "Action System" methodology studies.

**Key Questions:**
1. How does the model maintain the safety property that no two trains ever occupy the same block despite decentralizing control across the environment (points, signals, track circuits) and the software controller — which specific invariants (inv0_5, SAF-1, SAF-2) jointly guarantee this?
2. Why must "physical" events' guards and actions eventually reference only physical variables (per the "important remark" in 17.3.2 and Remarks 1–3 in 17.4.2), and what does the chapter's staged introduction of logical/physical duality (readiness → green signal, reservation → point position) teach about modeling a controller together with its environment?
3. What is the role of the invariant $M \to M, M \to N, N \to N, N \to P, P \to P$ transition structure (Section 17.3.1) in encoding the train assumptions TRN-1 to TRN-4, and why would violating any single train assumption break this invariant?

---

### Chapter 18: Problems (pp. 550–583)

**Summary:** This final chapter is a collection of exercises, projects, and pure-mathematics developments for readers to formalize and prove themselves using the Rodin Platform, rather than expository content — it is organized into three difficulty/purpose tiers.

**Key Definitions & Concepts by Section (brief — topic areas only):**
- **18.1 Exercises** — small sequential-program and simple-system developments: bank account management, birthday book (with page-based refinement), zero-row matrix search, ordered-matrix search, celebrity problem, common element in intersecting sets, a simple access control system, a simple library (with borrowing/waiting queues), a simple electronic circuit (boolean logic with environment/circuit event merging), a telephone alarm clock, and continuous-signal-to-step-signal analysis.
- **18.2 Projects** — larger case studies requiring a full requirements document and refinement strategy: an electronic hotel key system, an Earley parser (grammars, productions, match relation, scanner/predictor/completer), the Schorr–Waite graph-marking algorithm, linear list encapsulation, concurrent queue access, almost-linear sorting, Dijkstra–Scholten termination detection, distributed mutual exclusion (precedence relations, rings), a lift/elevator controller, and a business negotiation protocol (design patterns, unreliable channels).
- **18.3 Mathematical developments** — pure-math proof exercises: well-founded sets/relations and induction, fixpoints (Knaster–Tarski theorem, least/greatest fixpoint), well-founded recursion, transitive closure via fixpoints, filters and ultrafilters, topology (open/closed sets, neighborhoods, interior/closure/border, continuous functions), the Cantor–Bernstein theorem, and Zermelo's well-ordering theorem. : [[Exercises-Projects-and-Mathematical-Developments|Link]]

**Key Questions:**
1. Given only an informal (and sometimes deliberately "clumsy") requirements description, can the reader produce a properly labeled requirements document (EQP/FUN/SAF taxonomy) and a staged refinement strategy before touching the formal model, in the style demonstrated in Chapters 16 and 17?
2. Can the reader carry a generic Event-B refinement/merging development (naked events, anticipated/convergent status, merging rules) through to a correct, provable sequential program or system model, and separately, can they complete non-trivial interactive proofs (e.g., Knaster–Tarski, Cantor–Bernstein, Zermelo) that go beyond what the Rodin provers discharge automatically?

---
