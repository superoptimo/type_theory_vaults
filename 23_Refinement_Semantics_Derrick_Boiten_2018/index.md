# Refinement: Semantics, Languages and Applications — Index

[[book-guidelines|↩ Back to guidelines]]

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
