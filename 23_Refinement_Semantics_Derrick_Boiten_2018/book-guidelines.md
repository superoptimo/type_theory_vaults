# Refinement: Semantics, Languages and Applications — Guidelines

## Header

**Title:** Refinement: Semantics, Languages and Applications
**Author(s):** John Derrick, Eerke Boiten
**Publication:** Springer International Publishing AG, 2018 (Texts in Theoretical Computer Science, an EATCS Series)

**Brief Summary:**
This monograph surveys refinement — the process of moving from an abstract specification to a more concrete one while preserving observable behaviour — across the major semantic models and specification languages of formal methods. Part I develops refinement from first principles in simple models of computation (labelled transition systems, automata, state-based relational systems), showing how differing notions of *observation* (traces, completed traces, failures, refusals, divergence) give rise to a whole spectrum of distinct refinement relations, and introduces simulations (forward and backward) as the central proof technique. Part II shows how these semantic foundations are realised concretely in specification languages: the process algebras CSP, CCS and LOTOS; the state-based languages Z and B; and Event-B and Abstract State Machines (ASM). Part III addresses the natural question raised by this diversity — why are there so many different refinement relations, and how do they relate to one another? — by embedding process-algebraic and automata-theoretic refinement into a common relational framework, from which simulation rules for each refinement relation can be systematically derived, culminating in "process data types," a fully general relational model that incorporates both blocking (deadlock) and non-blocking (divergence) semantics simultaneously.

**Intent of the Author:**
The authors, both long-time contributors to the theory of relational and concurrent refinement, wrote this book as a monograph and graduate-level text aimed at researchers, academics and industrial practitioners of formal methods. Their goal is not to survey every specification notation exhaustively, but to be representative of the major paradigms (process algebra vs. state-based/relational) and to give readers both an intuitive and technically precise understanding of *why* different refinement relations exist, where they come from semantically, and how simulations can be used practically to verify them — including reconciling relational (Z/B/Event-B-style) and behavioural (CSP/CCS-style) views of refinement, which the authors' own research programme on "relational concurrent refinement" was built to unify.

---

## Topic List

1. **Refinement as Reduction of Non-Determinism and Behavioural Consistency** : [[Refinement-as-Reduction-of-Non-Determinism-and-Behavioural-Consistency|Link]]
   - Refinement as the relation between abstract and concrete specifications : [[Beyond-This-Book-Related-Refinement-Theories|Link]]
   - The reduction of non-determinism : [[Refinement-as-Reduction-of-Non-Determinism-and-Behavioural-Consistency|Link]]
   - Consistency of observable behaviour at a system's interface
   - Preorders and their induced equivalence relations : [[Refinement-as-Reduction-of-Non-Determinism-and-Behavioural-Consistency|Link]]
   - Testing scenarios as a way to characterize what a refinement relation observes : [[Refinement-as-Reduction-of-Non-Determinism-and-Behavioural-Consistency|Link]]
   - Safety versus liveness properties : [[Refinement-as-Reduction-of-Non-Determinism-and-Behavioural-Consistency|Link]]

2. **Labelled Transition Systems and the Spectrum of Observational Refinement** : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link]]
   - Labelled transition systems as a model of computation : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link]]
   - Trace refinement : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link1]], [[Relating-Process-Algebraic-and-Relational-Refinement|Link2]]
   - Completed trace refinement : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link1]], [[Relating-Process-Algebraic-and-Relational-Refinement|Link2]]
   - Failures refinement and refusal sets : [[Relating-Process-Algebraic-and-Relational-Refinement|Link]]
   - Readiness refinement : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link]]
   - Failure trace refinement : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link1]], [[Relating-Process-Algebraic-and-Relational-Refinement|Link2]]
   - Ready trace refinement : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link]]
   - Conformance and extension relations : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link]]
   - Infinite and completed infinite trace refinement : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link1]], [[Relating-Process-Algebraic-and-Relational-Refinement|Link2]]
   - Deadlock and non-determinism in an LTS : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link]]

3. **Automata and Simulations** : [[Automata-and-Simulations|Link]]
   - Automata as a semantic model with initial-state sets and internal actions : [[Automata-and-Simulations|Link]]
   - Finite invisible non-determinism and image-finiteness
   - Simple simulations as functional retrieve relations : [[State-Based-and-Relational-Models-of-Refinement|Link]]
   - Forward simulations : [[Automata-and-Simulations|Link1]], [[Relating-Data-Refinement-and-Failures-Divergences-Refinement|Link2]], [[State-Based-Specification-Languages-Z-and-B|Link3]]
   - Backward simulations : [[Automata-and-Simulations|Link1]], [[Relating-Data-Refinement-and-Failures-Divergences-Refinement|Link2]]
   - Soundness and (partial) completeness of forward and backward simulations : [[Relating-Data-Refinement-and-Failures-Divergences-Refinement|Link1]], [[Automata-and-Simulations|Link2]]
   - Joint completeness of forward and backward simulations : [[Automata-and-Simulations|Link1]], [[Relating-Data-Refinement-and-Failures-Divergences-Refinement|Link2]]
   - Forward-backward simulations as a single complete simulation relation : [[Automata-and-Simulations|Link]]
   - Bisimulation and weak bisimulation : [[Perspicuity-Error-Behaviour-and-Divergence|Link1]], [[Process-Algebras-CSP-LOTOS-and-CCS|Link2]]

4. **State-Based and Relational Models of Refinement** : [[State-Based-and-Relational-Models-of-Refinement|Link]]
   - Concrete state machines with anonymous transitions
   - Observations, termination and partial correctness
   - Total correctness and relational observations : [[State-Based-and-Relational-Models-of-Refinement|Link]]
   - State abstraction and abstraction functions : [[State-Based-and-Relational-Models-of-Refinement|Link]]
   - Relational data types and abstract data types : [[Perspicuity-Error-Behaviour-and-Divergence|Link]]
   - Data refinement as inclusion of program behaviour : [[State-Based-and-Relational-Models-of-Refinement|Link1]], [[Beyond-This-Book-Related-Refinement-Theories|Link2]]
   - Forward and backward simulation for relational data types : [[Automata-and-Simulations|Link]]
   - Totalisation of partial relations: blocking versus non-blocking interpretation : [[State-Based-and-Relational-Models-of-Refinement|Link]]
   - Simulation rules for partial relations : [[Process-Data-Types-A-General-Model-of-Concurrent-Refinement|Link1]], [[State-Based-and-Relational-Models-of-Refinement|Link2]]
   - Completeness (and its failure) of simulation rules under the blocking interpretation : [[State-Based-and-Relational-Models-of-Refinement|Link]]

5. **Perspicuity, Error Behaviour and Divergence** : [[Perspicuity-Error-Behaviour-and-Divergence|Link]]
   - Perspicuous operations and stuttering : [[Perspicuity-Error-Behaviour-and-Divergence|Link]]
   - Catastrophic versus non-catastrophic error interpretations : [[Perspicuity-Error-Behaviour-and-Divergence|Link]]
   - Divergence as unobservable infinite behaviour : [[Perspicuity-Error-Behaviour-and-Divergence|Link]]
   - Internal operations and their relationship to choice : [[Perspicuity-Error-Behaviour-and-Divergence|Link1]], [[Process-Data-Types-A-General-Model-of-Concurrent-Refinement|Link2]]
   - Stable states : [[Perspicuity-Error-Behaviour-and-Divergence|Link]]
   - Weak data refinement and embeddings of internal operations
   - Livelock and divergence from internal operations : [[Perspicuity-Error-Behaviour-and-Divergence|Link]]

6. **Process Algebras: CSP, LOTOS and CCS** : [[Process-Algebras-CSP-LOTOS-and-CCS|Link]]
   - CSP language constructs: prefixing, external and internal choice, parallel composition, hiding
   - CSP traces, stable failures and failures-divergences-infinite-traces (FDI) semantics
   - CSP trace, stable failures and FDI refinement
   - LOTOS language and its data/behavioural parts : [[State-Based-and-Relational-Models-of-Refinement|Link]]
   - Conformance, reduction and extension in LOTOS
   - Testing equivalence
   - CCS language, ports and bi-party synchronisation : [[Process-Algebras-CSP-LOTOS-and-CCS|Link]]
   - Strong bisimulation and strong equivalence in CCS : [[Process-Algebras-CSP-LOTOS-and-CCS|Link]]
   - Weak bisimulation and observational equivalence in CCS : [[Perspicuity-Error-Behaviour-and-Divergence|Link1]], [[Refinement-as-Reduction-of-Non-Determinism-and-Behavioural-Consistency|Link2]], [[Process-Algebras-CSP-LOTOS-and-CCS|Link3]]
   - Must and may testing

7. **State-Based Specification Languages: Z and B** : [[State-Based-Specification-Languages-Z-and-B|Link]]
   - The Z schema calculus and states-and-operations style : [[State-Based-Specification-Languages-Z-and-B|Link]]
   - Operation preconditions and input/output signatures
   - Relational semantics of a Z specification : [[State-Based-Specification-Languages-Z-and-B|Link]]
   - Forward and backward simulation rules for Z (non-blocking and blocking) : [[Automata-and-Simulations|Link]]
   - Completeness of Z simulation rules : [[Automata-and-Simulations|Link]]
   - The B-Method and Abstract Machine Notation (AMN) : [[Event-B-and-Abstract-State-Machines-ASM|Link]]
   - Machine consistency and weakest preconditions : [[Event-B-and-Abstract-State-Machines-ASM|Link]]
   - Refinement machines and linking invariants in B
   - Proof obligations for refinement in B : [[State-Based-Specification-Languages-Z-and-B|Link]]
   - Implementation machines : [[State-Based-Specification-Languages-Z-and-B|Link]]

8. **Event-B and Abstract State Machines (ASM)** : [[Event-B-and-Abstract-State-Machines-ASM|Link]]
   - Event-B machines, contexts and guarded events : [[Event-B-and-Abstract-State-Machines-ASM|Link]]
   - Proof obligations: invariant preservation and feasibility : [[State-Based-Specification-Languages-Z-and-B|Link]]
   - Forward and backward simulation (guard strengthening, event correctness, deadlock freedom) : [[Automata-and-Simulations|Link]]
   - Splitting and merging events in a refinement : [[Event-B-and-Abstract-State-Machines-ASM|Link]]
   - Introducing new (perspicuous) events: convergent and anticipated status, variants
   - ASM transition systems and control-state ASMs
   - Preservation of partial and total correctness in ASM
   - Generalised (m:n) forward simulation in ASM : [[Event-B-and-Abstract-State-Machines-ASM|Link]]

9. **Relating Process-Algebraic and Relational Refinement** : [[Relating-Process-Algebraic-and-Relational-Refinement|Link]]
   - Embedding concurrent refinement relations into a relational framework via finalisation
   - Trace, completed trace, failure, failure trace, extension and conformance embeddings
   - Simulation rules derived from each embedding
   - Correspondences between relational refinement and process semantics (traces-divergences, singleton failures)
   - Automata and IO automata embeddings : [[Relating-Process-Algebraic-and-Relational-Refinement|Link]]
   - Weakly quiescent traces and the IOTS refinement preorder : [[State-Based-Specification-Languages-Z-and-B|Link]]
   - Demonic versus angelic process semantics for under-specified inputs
   - Embedding internal events and divergence into the relational framework : [[State-Based-Specification-Languages-Z-and-B|Link]]

10. **Relating Data Refinement and Failures-Divergences Refinement** : [[Relating-Data-Refinement-and-Failures-Divergences-Refinement|Link]]
    - The basic relational embedding of refusals
    - Backward simulation with refusals and strengthened applicability : [[Automata-and-Simulations|Link]]
    - Blocking versus non-blocking models of traces, refusals and divergence
    - Extended finalisations for input and output
    - Demonic versus angelic models of output non-determinism : [[Relating-Data-Refinement-and-Failures-Divergences-Refinement|Link]]
    - Maximal refusal sets and the Sim/Maxsim characterisation : [[Relating-Data-Refinement-and-Failures-Divergences-Refinement|Link]]
    - Summary table of forward and backward simulation conditions : [[Automata-and-Simulations|Link1]], [[Relating-Data-Refinement-and-Failures-Divergences-Refinement|Link2]]
    - Why standard data refinement does not coincide with failures-divergences refinement : [[Relating-Data-Refinement-and-Failures-Divergences-Refinement|Link]]

11. **Process Data Types: A General Model of Concurrent Refinement** : [[Process-Data-Types-A-General-Model-of-Concurrent-Refinement|Link]]
    - Program controlled ADTs : [[Process-Data-Types-A-General-Model-of-Concurrent-Refinement|Link]]
    - Output embeddings and refusal embeddings : [[Process-Data-Types-A-General-Model-of-Concurrent-Refinement|Link]]
    - Process data types: normal, blocking and divergent partitions of an operation : [[Process-Data-Types-A-General-Model-of-Concurrent-Refinement|Link]]
    - Embedding of a process data type into a total relational data type : [[State-Based-Specification-Languages-Z-and-B|Link1]], [[Perspicuity-Error-Behaviour-and-Divergence|Link2]]
    - Forward and backward simulation for process data types : [[Automata-and-Simulations|Link]]
    - Embedding internal operations (τ-data types) into process data types : [[Perspicuity-Error-Behaviour-and-Divergence|Link1]], [[Process-Data-Types-A-General-Model-of-Concurrent-Refinement|Link2]]
    - Failures-divergences semantics of τ-data types
    - Simulation conditions with internal operations, blocking and non-blocking : [[Perspicuity-Error-Behaviour-and-Divergence|Link]]
    - Adding outputs: refinement conditions for output embeddings
    - Outputs in the blocking and non-blocking approaches : [[State-Based-Specification-Languages-Z-and-B|Link]]

12. **Beyond This Book: Related Refinement Theories** : [[Beyond-This-Book-Related-Refinement-Theories|Link]]
    - Weakest precondition semantics and action systems : [[Beyond-This-Book-Related-Refinement-Theories|Link]]
    - VDM and Object-Z : [[Beyond-This-Book-Related-Refinement-Theories|Link]]
    - RAISE and Alloy
    - The refinement calculus and Circus : [[Beyond-This-Book-Related-Refinement-Theories|Link]]
    - Temporal logic approaches (TLA/TLA+)
    - Action refinement and non-atomic refinement : [[Beyond-This-Book-Related-Refinement-Theories|Link]]
    - Timed refinement models : [[Beyond-This-Book-Related-Refinement-Theories|Link1]], [[Process-Algebras-CSP-LOTOS-and-CCS|Link2]], [[Process-Data-Types-A-General-Model-of-Concurrent-Refinement|Link3]], [[State-Based-and-Relational-Models-of-Refinement|Link4]]
    - Probabilistic refinement : [[Beyond-This-Book-Related-Refinement-Theories|Link]]

---

## Chapter Summaries

### Chapter 1: Labeled Transition Systems and Their Refinement (pp. 3–26)

**Summary:** Introduces labelled transition systems (LTS) as the simplest model of computation for studying refinement, and develops a spectrum of refinement relations — trace, completed trace, failures, readiness, failure trace and ready trace refinement — each corresponding to a different notion of what an observer can see, together with the testing-scenario intuition behind each. : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link]]

**Key Definitions & Concepts by Section:**
- **1.2 Labelled Transition Systems** — labelled transition system (LTS) $L = (States, Act, T, Init)$; enabled actions $next(p)$; deadlock; non-determinism (two transitions on the same action to different states) : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link]]
- **1.3 Trace Refinement** — trace of a process $\sigma \in Act^*$; trace refinement $p \sqsubseteq_{tr} q$ iff $\mathcal{T}(q) \subseteq \mathcal{T}(p)$; preorders and their induced equivalence; safety vs. liveness properties : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link1]], [[Relating-Process-Algebraic-and-Relational-Refinement|Link2]]
- **1.4 Completed Trace Refinement** — completed trace (a maximal trace ending in deadlock); completed trace refinement requiring both trace and completed-trace inclusion : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link1]], [[Relating-Process-Algebraic-and-Relational-Refinement|Link2]]
- **1.5 Failures Refinement** — failure $(\sigma, X)$ recording a trace and a refusal set; failures refinement; deterministic processes characterised via failures : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link1]], [[Relating-Data-Refinement-and-Failures-Divergences-Refinement|Link2]], [[Relating-Process-Algebraic-and-Relational-Refinement|Link3]]
- **1.6 Readiness Refinement** — readiness sets (the *maximal* set of enabled actions after a trace) as a dual to refusal sets : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link]]
- **1.7 Failure Trace Refinement** — refusal information recorded between every action in a trace, not just at the end : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link1]], [[Relating-Process-Algebraic-and-Relational-Refinement|Link2]]
- **1.8 Ready Trace Refinement** — combining ready sets with the failure-trace idea : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link]]
- **1.9 Conformance and Extension** — $P \; conf \; Q$ and extension refinement, motivated by LOTOS-style testing : [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Link1]], [[Relating-Process-Algebraic-and-Relational-Refinement|Link2]]
- **1.10 Data and Infinite Traces** — adding data/parameters to events; infinite trace refinement; infinite completed trace refinement

**Key Questions:**
1. Why is trace refinement too weak to distinguish some processes that are intuitively different (e.g. Example 1.6), and how does completed trace refinement partially address this?
2. What is the relationship between a refinement relation and a "testing scenario," and why does this framing help justify each relation's definition?
3. Why can failures refinement detect non-determinism when trace refinement cannot?

---

### Chapter 2: Automata - Introducing Simulations (pp. 27–38)

**Summary:** Introduces automata as a semantic model closely related to LTS but with multiple initial states and an internal action $\tau$, and uses this setting to introduce simulations — simple, forward, and backward — as the central technique for verifying trace refinement, culminating in results about their soundness, incompleteness individually, and joint completeness. : [[Automata-and-Simulations|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 Introduction** — automaton $A = (States, Act, T, Start)$; finite invisible non-determinism (fin); forest; trace refinement extended to finite/infinite traces ($\sqsubseteq_{tr^*}$, $\sqsubseteq_{tr^\omega}$, $\sqsubseteq_{tr}$)
- **2.2 Refinement and Simulations** — simple simulation (a function from concrete to abstract states); forward simulation; backward simulation (requiring totality of $R$); soundness; partial completeness results; joint completeness of forward+backward simulations via an intermediate specification; forward-backward simulation as a single complete relation : [[State-Based-Specification-Languages-Z-and-B|Link1]], [[State-Based-and-Relational-Models-of-Refinement|Link2]]
- **2.3 Bisimulation** — bisimulation $R$ requiring mutual step-simulation with the *same* relation; bisimulation as an equivalence stronger than trace refinement : [[Automata-and-Simulations|Link]]

**Key Questions:**
1. Why are neither forward nor backward simulations complete on their own, and what does "jointly complete" mean in this context (Example 2.6)?
2. Why does backward simulation require totality of the retrieve relation while forward simulation does not?
3. How does bisimulation differ from the refinement relations of Chapter 1 in what it compares (observations vs. simulations) and in its strength?

---

### Chapter 3: Simple State-Based Refinement (pp. 39–49)

**Summary:** Introduces a complementary, state-centred model — the Concrete State Machine with Anonymous Transitions (CSMAT) — where observations are about *what is* (state values) rather than *what happens* (events), developing notions of safety, partial and total correctness refinement, state abstraction, and motivating the move toward labelled relational models in the next chapter. : [[State-Based-and-Relational-Models-of-Refinement|Link]]

**Key Definitions & Concepts by Section:**
- **3.2 A Basic Model with Refinement** — CSMAT $(State, Init, T)$ with $T$ reflexive and transitive ("stuttering"); observations $O(M)$; safety refinement : [[State-Based-and-Relational-Models-of-Refinement|Link1]], [[Process-Algebras-CSP-LOTOS-and-CCS|Link2]], [[Process-Data-Types-A-General-Model-of-Concurrent-Refinement|Link3]]
- **3.3 Termination and Refinement** — terminating states $term(M)$; partial correctness refinement; nonterminating and "may fail to terminate" states : [[State-Based-and-Relational-Models-of-Refinement|Link1]], [[Relating-Process-Algebraic-and-Relational-Refinement|Link2]]
- **3.4 More than One Observation** — state trace semantics $ST(M)$ : [[Refinement-as-Reduction-of-Non-Determinism-and-Behavioural-Consistency|Link]]
- **3.5 Towards Total Correctness** — motivating a stronger correctness notion than partial correctness : [[State-Based-and-Relational-Models-of-Refinement|Link]]
- **3.6 Observations Including Initial States** — relational observations $R(M)$; relational trace and partial correctness refinement; total correctness refinement
- **3.7 State Abstraction** — state abstraction via a total function $f$; perspicuous step (a concrete state change that abstracts to stuttering) : [[State-Based-and-Relational-Models-of-Refinement|Link]]
- **3.8 State Variables and Observation** — observable vs. local/auxiliary variables; connection to Hoare and He's Unifying Theories of Programming : [[Relating-Process-Algebraic-and-Relational-Refinement|Link]]
- **3.9 Programs and Labeled Transitions** — motivating the move to labelled, non-transitive relational models (Chapter 4) via elementary transitions ("repertoire"/alphabet) and programs

**Key Questions:**
1. Why does the CSMAT model characterise termination *implicitly* via stuttering states rather than via explicit accepting states?
2. What is a "perspicuous step," and why does it complicate the implicit notion of termination?
3. What practical limitations of the single-transition-relation CSMAT model motivate introducing labelled operations and a repertoire of elementary transitions?

---

### Chapter 4: A Relational View of Refinement (pp. 51–67)

**Summary:** Develops the relational model of abstract data types (ADTs) — state, initialisation, indexed operations and finalisation — defines data refinement as inclusion of program behaviour, derives forward and backward simulation rules for total relations, and then extends the theory to partial relations via the blocking and non-blocking totalisation interpretations, showing that joint completeness of simulations holds for the non-blocking but not the blocking interpretation. : [[State-Based-and-Relational-Models-of-Refinement|Link1]], [[Relating-Process-Algebraic-and-Relational-Refinement|Link2]]

**Key Definitions & Concepts by Section:**
- **4.1 Introduction** — relational notation: domain/range, restriction/subtraction, relational image, overriding, composition, transitive/reflexive closure, parallel composition
- **4.2 Relational Data Types** — data type $(State, Init, \{Op_i\}_{i \in I}, Fin)$; total and canonical data types; conformal data types; programs as sequences of operation indices : [[Perspicuity-Error-Behaviour-and-Divergence|Link]]
- **4.3 Relational Refinement** — data refinement $A \sqsubseteq_{data} C$ iff $p_C \subseteq p_A$ for all programs $p$; forward simulation (initialisation, finalisation, correctness conditions); backward simulation; functional simulations coincide; soundness; joint completeness via an intermediate ADT : [[Relating-Process-Algebraic-and-Relational-Refinement|Link1]], [[State-Based-and-Relational-Models-of-Refinement|Link2]]
- **4.4 From Total to Partial Relational Refinement** — non-blocking (contract) totalisation vs. blocking (behavioural) totalisation of a partial operation; forward/backward simulation for partial relations (initialisation, finalisation, applicability, correctness); joint completeness holds in the non-blocking interpretation but *fails* in the blocking interpretation (Theorem 4.6 and its counterexample); a fully partial relational theory without totalisation : [[State-Based-and-Relational-Models-of-Refinement|Link1]], [[Relating-Process-Algebraic-and-Relational-Refinement|Link2]]

**Key Questions:**
1. What is the difference between the "non-blocking" (contract) and "blocking" (behavioural) interpretations of a partial operation, and how does each affect what "$\bot$" means semantically?
2. Why does joint completeness of forward and backward simulation rules hold for the non-blocking interpretation of partial relations but fail for the blocking interpretation (Example in Fig. 4.6)?
3. How do forward and backward simulation conditions for partial relations differ between the blocking and non-blocking models?

---

### Chapter 5: Perspicuity, Divergence, and Internal Operations (pp. 69–80)

**Summary:** Completes the theory begun in Chapters 3–4 by addressing the two dimensions left open — operations with no abstract state change ("perspicuous" operations) and operations with no observable event (internal operations) — and their shared consequence: the possibility of divergence, formalised for LTS via internal $\tau$-transitions and weak bisimulation. : [[Perspicuity-Error-Behaviour-and-Divergence|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Perspicuous Operations** — a concrete operation refining "skip" at the abstract level; data refinement with perspicuous operations; link to Event-B's introduction of new events : [[Perspicuity-Error-Behaviour-and-Divergence|Link]]
- **5.2 Error Behaviour: Catastrophic or Not?** — catastrophic/chaotic interpretation of error (non-blocking) vs. non-catastrophic (blocking); three general strategies for handling problematic behaviour
- **5.3 Divergence** — divergent state; strictly divergent trace; general Definition 5.2
- **5.4 Internal Operations** — internal operation $\tau$; weak bisimulation; $\tau$-data type; weak data refinement; stable state; internal actions and choice in LTS (three ways to represent choice, and why weak bisimulation fails to be a pre-congruence, Fig. 5.2); divergence in LTS defined via the largest fixed point of $\lambda S.\, dom(\tau \triangleright S)$; livelock : [[Perspicuity-Error-Behaviour-and-Divergence|Link1]], [[Process-Data-Types-A-General-Model-of-Concurrent-Refinement|Link2]]

**Key Questions:**
1. Why does the introduction of perspicuous or internal operations create a risk of divergence that did not exist for the basic relational or LTS models?
2. Why is weak bisimulation *not* a pre-congruence, and what does Fig. 5.2's three-way comparison of choice representations reveal about this?
3. What are the three general strategies (partial correctness, proof obligations, explicit modelling) for handling problematic/erroneous behaviour in a refinement theory?

---

### Chapter 6: Process Algebra (pp. 85–120)

**Summary:** Introduces CSP as the canonical process algebra — its language of prefixing, choice, parallel composition and hiding, its traces/stable-failures/failures-divergences-infinite-traces (FDI) semantic models, and the corresponding refinement relations — then compares this with the closely related process algebras LOTOS and CCS, highlighting differences in synchronisation style (multi-party vs. bi-party) and in their preferred equivalences (testing-based refinement vs. bisimulation). : [[Perspicuity-Error-Behaviour-and-Divergence|Link1]], [[Process-Algebras-CSP-LOTOS-and-CCS|Link2]], [[Relating-Process-Algebraic-and-Relational-Refinement|Link3]]

**Key Definitions & Concepts by Section:**
- **6.1 CSP - The Language** — $stop$, $skip$, event prefix $a \to P$, input/output ($c!v \to P$, $c?v : T \to P$), external choice $P_1 \square P_2$, internal choice $P_1 \sqcap P_2$, recursion, interleaving $P_1 \| P_2$, interface parallel $P_1 \Vert_A P_2$, hiding $P \setminus L$, renaming
- **6.2 CSP - The Semantics** — trace semantics computed compositionally; the CSP failures model (stable failures, well-formedness conditions T1–T2, F1–F4); the failures-divergences-infinite-traces (FDI) semantics (F1–F4, D1–D4, I1–I2); compositional definitions of $F$, $D$, $I$ per operator : [[Process-Algebras-CSP-LOTOS-and-CCS|Link]]
- **6.3 CSP - Refinement** — trace refinement $\sqsubseteq_{tr}$, stable failures refinement $\sqsubseteq_{sf}$, FDI refinement $\sqsubseteq_{fdi}$ : [[Process-Algebras-CSP-LOTOS-and-CCS|Link]]
- **6.4 LOTOS - Language, Semantics and Refinement** — full vs. basic LOTOS; explicit internal action $i$; choice $P[]Q$; general parallelism $P_1 |[x_1,\dots,x_n]| P_2$; refusals $Ref_P(\sigma)$; conformance ($conf$, not a preorder); reduction ($red$); extension ($ext$); testing equivalence : [[Process-Algebras-CSP-LOTOS-and-CCS|Link1]], [[Relating-Process-Algebraic-and-Relational-Refinement|Link2]]
- **6.5 CCS - Language, Semantics and Refinement** — inaction $0$; prefixing $a.P$; ports and input/output $c(v).P$; bi-party synchronisation via complementary actions $a$/$\bar a$; restriction vs. hiding; strong bisimulation/strong equivalence ($\sim$); weak bisimulation/observational equivalence ($\approx$); algebraic laws and congruence properties : [[Process-Algebras-CSP-LOTOS-and-CCS|Link]]

**Key Questions:**
1. How do the failures-divergences-infinite-traces (FDI) semantics improve on stable failures alone, and why is a "catastrophic" interpretation of divergence used?
2. Why is conformance in LOTOS not a preorder, and how does reduction repair this while retaining the same intuition?
3. What is the essential difference between CCS's bi-party synchronisation with hidden interaction and CSP/LOTOS's multi-party synchronisation, and how does this affect what compositions can express?

---

### Chapter 7: State-Based Languages: Z and B (pp. 121–147)

**Summary:** Introduces Z's schema-based specification style and derives its standard forward/backward simulation rules from the relational theory of Chapter 4 using the non-blocking interpretation, then introduces the B-Method's Abstract Machine Notation and its weakest-precondition-based proof obligations for refinement, showing the correspondence between B's proof obligations and Z-style forward simulation. : [[State-Based-Specification-Languages-Z-and-B|Link]]

**Key Definitions & Concepts by Section:**
- **7.1 Z - The Language** — given sets, axiomatic definitions, schemas, $\Delta State$, the Z schema calculus, operation precondition $pre\,Op$, input/output signature ($?Op$, $!Op$), standard Z ADT : [[State-Based-Specification-Languages-Z-and-B|Link]]
- **7.2 Z – Refinement** — relational semantics of a Z specification (state/init/operations/finalisation embedding input-output sequences); forward simulation for Z (initialisation, applicability, correctness); backward simulation for Z; refinement in Z as weakening precondition/strengthening postcondition; changing the state space in refinement; completeness of Z simulation rules (complete in non-blocking, incomplete in blocking/Object-Z interpretation, Example 7.4) : [[State-Based-Specification-Languages-Z-and-B|Link]]
- **7.3 The B-Method** — Abstract Machine Notation (AMN); machines, variables, invariant, initialisation, operations with explicit `PRE`/`THEN`; machine consistency proof obligations; weakest precondition notation $[S]P$
- **7.4 Refinement in the B-Method** — refinement machines (`REFINEMENT`/`REFINES`), linking invariant; proof obligations for initialisation, correctness and precondition strengthening expressed via weakest preconditions; implementation machines (no state of their own, no non-determinism) : [[State-Based-Specification-Languages-Z-and-B|Link]]

**Key Questions:**
1. Why does Z's standard refinement theory use the non-blocking interpretation of partiality while Object-Z uses the blocking interpretation, and what practical consequence does this have for completeness of simulation rules (Example 7.4)?
2. In what two distinct ways can refinement change a Z specification (Examples 7.1 vs. 7.2), and how does each connect to weakening precondition / strengthening postcondition?
3. How do B's refinement proof obligations, expressed via weakest preconditions, correspond to the forward simulation conditions derived for Z?

---

### Chapter 8: State-Based Languages: Event-B and ASM (pp. 149–176)

**Summary:** Introduces Event-B's machine/context structure and guarded-event style, derives its forward and backward simulation proof obligations (including the novel possibility of splitting, merging, or introducing new perspicuous events with convergent/anticipated status to control divergence), then introduces Abstract State Machines (ASM) and their more general "$m$:$n$" simulations that drop the assumption of one-to-one correspondence between abstract and concrete steps. : [[Event-B-and-Abstract-State-Machines-ASM|Link1]], [[State-Based-Specification-Languages-Z-and-B|Link2]], [[State-Based-and-Relational-Models-of-Refinement|Link3]]

**Key Definitions & Concepts by Section:**
- **8.1 Event-B** — machines and contexts; guarded events (`when`/`then`); event status (ordinary, convergent, anticipated); invariant preservation (`INV`) and feasibility (`FIS`) proof obligations : [[Event-B-and-Abstract-State-Machines-ASM|Link]]
- **8.2 Refinement in Event-B** — gluing invariant; guard strengthening (`GRD`) and event correctness (`SIM`); relative deadlock freedom (`DLF`); relational semantics for Event-B (observations as sequences of states, not events; the "$X = Y$" dropping of conformality); splitting/merging events in a refinement; introducing new (perspicuous) events, their convergent/anticipated status, and the variant $V$ with `NAT`/`VAR` proof obligations to rule out divergence : [[Event-B-and-Abstract-State-Machines-ASM|Link1]], [[State-Based-Specification-Languages-Z-and-B|Link2]]
- **8.3 ASM** — control-state ASM; final states, traces, runs; partial and total I/O behaviour ($PIO$, $TIO$); preservation of partial correctness; preservation of total correctness; partial/total preservation of traces via a correspondence relation $IO$; generalised ($m$:$n$) forward simulation using temporal operators $AF$/$EF$/$AF^+$/$EF^+$ and well-founded decrease conditions to rule out divergence

**Key Questions:**
1. Why does Event-B not require conformality between abstract and concrete machines, and how does this enable splitting/merging events in a refinement step?
2. What is the role of the "convergent" vs. "anticipated" event status, and how do the `NAT`/`VAR` proof obligations prevent perspicuous new events from causing divergence?
3. How does ASM's generalised forward simulation (allowing $m$ abstract steps to correspond to $n$ concrete steps) differ from the strict one-to-one commuting-square simulations of Z, Event-B and B, and why is this needed?

---

### Chapter 9: Relational Concurrent Refinement (pp. 179–204)

**Summary:** Opens Part III by developing a systematic method — embedding a concurrent (process-algebraic or automata) refinement relation into the relational ADT framework by choosing an appropriate finalisation — which is applied in turn to trace, completed trace, failure, failure-trace, extension, and IOTS refinement, in each case proving the correspondence with data refinement and extracting the corresponding simulation rules, and separately surveys the dual question of which process semantics correspond to *standard* (blocking/non-blocking) data refinement. : [[State-Based-and-Relational-Models-of-Refinement|Link1]], [[Process-Data-Types-A-General-Model-of-Concurrent-Refinement|Link2]], [[Relating-Process-Algebraic-and-Relational-Refinement|Link3]]

**Key Definitions & Concepts by Section:**
- **9.3 Relating Process Algebraic and Relational Refinement** — trace embedding and Theorem 9.1 (data refinement = trace preorder); completed trace embedding; failures embedding; failure trace embedding; extension embedding (and why conformance, not being a preorder, cannot be embedded this way) : [[Relating-Process-Algebraic-and-Relational-Refinement|Link]]
- **9.4 Relating Data Refinement to Process Algebraic Refinement** — the "dual" question; traces-divergences semantics; singleton failures semantics; non-blocking data refinement corresponds to traces-divergences refinement (via a `process(A)` CSP translation); blocking data refinement corresponds to singleton failures refinement (via `processb(A)`/`inputProcessb(A)`) : [[Relating-Process-Algebraic-and-Relational-Refinement|Link1]], [[Relating-Data-Refinement-and-Failures-Divergences-Refinement|Link2]]
- **9.5 Relating Automata and Relational Refinement** — automata embedding (equivalent to trace embedding); IO automata, partitioned automata; weakly quiescent traces $\delta$–traces; IOTS refinement preorder $\sqsubseteq_{iot}$; demonic vs. angelic process semantics for under-specified inputs; IOTS simulation rules : [[Relating-Process-Algebraic-and-Relational-Refinement|Link]]
- **9.6 Internal Events and Divergence** — embedding trace refinement in the CSP failures-divergences model with a distinguished divergence value $\omega$

**Key Questions:**
1. Why does the "obvious" natural pairing (blocking ↔ failures, non-blocking ↔ traces-divergences) *not* hold, and what surprising correspondences does the summary table in Sect. 9.4 reveal instead?
2. How does choosing the finalisation of a relational embedding determine which process-algebraic refinement relation the resulting data refinement corresponds to?
3. Why can conformance not be captured as a data-refinement embedding, while extension can?

---

### Chapter 10: Relating Data Refinement and Failures-Divergences Refinement (pp. 207–232)

**Summary:** Deepens the failures embedding of Chapter 9 to include input and output, showing that this requires strengthening backward simulation's applicability condition and introducing demonic vs. angelic models of output non-determinism, and derives a complete summary table of forward/backward simulation conditions needed to recover failures-divergences refinement in each combination of blocking/non-blocking and demonic/angelic/no-output models. : [[Relating-Data-Refinement-and-Failures-Divergences-Refinement|Link]]

**Key Definitions & Concepts by Section:**
- **10.2 The Basic Relational Embedding** — backward simulation with refusals (strengthened applicability, Definition 10.1); blocking model (traces/refusals, no divergence) vs. non-blocking model (all traces possible, divergence from precondition violation); Theorems 10.1–10.2 (relational refinement with extended finalisations = failures-divergences refinement) : [[State-Based-Specification-Languages-Z-and-B|Link]]
- **10.3 Dealing with Input and Output** — events as $Op.i.o$ triples; demonic choice of outputs (refusable) vs. angelic choice (not refusable); extended finalisation (Definition 10.2, angelic and demonic embeddings) : [[Relating-Data-Refinement-and-Failures-Divergences-Refinement|Link1]], [[Relating-Process-Algebraic-and-Relational-Refinement|Link2]]
- **10.3.2 Deriving the New Simulation Rules** — maximal refusal sets; $Sim$ type and $Maxsim$ predicate; backward simulation for demonic outputs (Definition 10.3); forward simulation unaffected by refusals except in the angelic model : [[Process-Data-Types-A-General-Model-of-Concurrent-Refinement|Link]]
- **10.4 Summary of Simulation Conditions** — full table of forward simulation conditions (`FS.Init`, `FS.App`, `FS.CorrNonBlock`/`FS.CorrBlock`, `FS.FinAng`) and backward simulation conditions (`BS.Init`, `BS.AppBlock`, `BS.CorrNonBlock`/`BS.CorrBlock`, `BS.FinRef`/`BS.FinDem`/`BS.FinAng`) across none/demonic/angelic output models : [[Automata-and-Simulations|Link1]], [[Process-Algebras-CSP-LOTOS-and-CCS|Link2]]
- **10.4.1 Discussion** — worked examples (Figs. 10.6–10.7) showing exactly where and why extra conditions are needed in each combination of blocking/non-blocking and with/without outputs

**Key Questions:**
1. Why does observing refusals strengthen the *backward* simulation applicability condition but leave the *forward* simulation conditions essentially unchanged (except under angelic outputs)?
2. What is the difference between the demonic and angelic models of output non-determinism, and how does each affect whether output values can be refused?
3. Using the guest-house example (Example 10.3), why can two ADTs be standard-refinement-equivalent yet fail to be failures-divergences equivalent?

---

### Chapter 11: Process Data Types - A Fully General Model of Concurrent Refinement (pp. 235–261)

**Summary:** Generalises the entire framework of Chapters 9–10 into a single unifying relational model — the "process data type," in which every operation is a triple (normal, blocking, divergent) partition of the state — deriving forward and backward simulation rules once and for all by embedding into total relations, and then specialising this general theory back down to concrete cases with internal operations (τ-data types) and with outputs, in both blocking and non-blocking interpretations. : [[Process-Data-Types-A-General-Model-of-Concurrent-Refinement|Link]]

**Key Definitions & Concepts by Section:**
- **11.1 Introduction** — program controlled ADT; output embedding; refusal embedding
- **11.2 A Relational ADT with Divergence and Blocking** — process data type $(State, Inits, \{Op_i\}_{i\in I}, Fin)$ with each $Op_i = (N,B,D)$ a normal/blocking/divergent partition; reduction; embedding into a total data type with special values $\bot$ (blocking), $\omega$ (divergence), $no$; choice-ordering table (divergence as a zero of choice)
- **11.2.1–11.2.2 Forward/Backward Simulation for Process Data Types** — Theorems 11.1–11.2 giving the general simulation conditions (initialisation, finalisation correctness/applicability, and per-operation correctness/blocking/divergence conditions) derived once for the general model
- **11.3 Using Process Data Types** — embedding a basic data type with internal operations ($\tau$-data type) into a process data type; notations $State{\downarrow}$ (stable states), $\tau^*$, $\overset{\leftrightarrow}{Op}$, $State{\uparrow}$ (divergent states), $liv\,Op$; failures-divergences semantics of a $\tau$-data type (Definition 11.8); simulation rules for the blocking approach (`FS.Init.τ`, `FS.App.τ`, `FS.CorrBlock.τ`, `FS.DivStates`, `FS.DivOp` and backward counterparts) and the non-blocking approach : [[Process-Data-Types-A-General-Model-of-Concurrent-Refinement|Link]]
- **11.4 Adding in a Consideration of Outputs** — output embeddings' effect on refinement conditions; outputs in the blocking approach (`FS.FinDemBlock.τ`, `BS.FinDemBlock.τ`, with Example 11.1 as a counterexample to omitting them); outputs in the non-blocking approach (`Maxsimtot`, `FS.FinDemNonBlock.τ`, `BS.FinDemNonBlock.τ`) : [[Relating-Data-Refinement-and-Failures-Divergences-Refinement|Link]]

**Key Questions:**
1. How does the process data type's (N, B, D) partition of an operation subsume both the blocking and non-blocking totalisation interpretations of Chapter 4 as special cases?
2. Why do internal operations require notation like $State{\uparrow}$ (divergent states) and $liv\,Op$ (states from which an operation might lead to divergence), and how do these feed into the `DivStates`/`DivOp` proof obligations?
3. What does Example 11.1 demonstrate about why finalisation conditions on refusals remain necessary even after all the "ordinary" simulation conditions are satisfied?

---

### Chapter 12: Conclusions (pp. 263–267)

**Summary:** Reviews the book's overall arc from LTS-based observational refinement (Part I) through concrete specification languages (Part II) to the unifying relational-concurrent framework (Part III), and surveys related refinement theories not covered in depth — weakest-precondition/action-systems semantics, VDM, Object-Z, RAISE, Alloy, the refinement calculus and Circus, TLA/TLA+, action and non-atomic refinement, timed refinement, and probabilistic refinement.

**Key Definitions & Concepts:**
- Action systems and predicate transformer (weakest precondition) semantics as an alternative semantic basis to the relational model
- VDM's refinement as forward simulation restricted to total surjective functions (hence incomplete, lacking backward simulation)
- Object-Z as an object-oriented extension of Z with a relational refinement methodology
- RAISE (Rigorous Approach to Industrial Software Engineering) as a wide-spectrum integration language
- The refinement calculus (specification statements: precondition, postcondition, frame) and its Z-integrated descendants ZRC and Circus
- TLA/TLA+ and temporal-logic-based refinement
- Action refinement / non-atomic refinement (dropping conformality, refining one operation into several) and coupled simulations
- Timed refinement models (timed failures, timed failure-stability)
- Probabilistic refinement

**Key Questions:**
1. What distinguishes VDM's refinement methodology from Z's, and why does the restriction to total surjective forward simulations make VDM's method incomplete?
2. How does "action refinement" (or non-atomic refinement) relax the conformality assumption used throughout the rest of the book, and what technique (coupled simulations) is used to verify it?
3. What semantic basis do action systems and the refinement calculus share, and how does it differ from the relational ADT model used for most of this book?
