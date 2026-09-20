# Verification and Control of Hybrid Systems: A Symbolic Approach — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Systems as the Common Mathematical Model** : [[Systems-as-the-Common-Mathematical-Model|Link]]
   - Systems as sextuples of states, initial states, inputs, transitions, outputs, and output maps
   - Finite-state versus infinite-state systems : [[Systems-as-the-Common-Mathematical-Model|Link]]
   - Internal versus external behavior : [[Systems-as-the-Common-Mathematical-Model|Link]]
   - Blocking, nonblocking, deterministic, and output-deterministic systems
   - Composition of systems via an interconnection relation : [[Feedback-Composition-and-Controller-Synthesis|Link]]
   - Dynamical systems, control systems, and hybrid systems modeled as systems : [[Systems-as-the-Common-Mathematical-Model|Link]]

2. **Verification and Control Problems** : [[Verification-and-Control-Problems|Link]]
   - The equivalence problem : [[Verification-and-Control-Problems|Link]]
   - The pre-order (containment) problem : [[Verification-and-Control-Problems|Link]]
   - The control problem for equivalence : [[Verification-and-Control-Problems|Link]]
   - The control problem for pre-order : [[Verification-and-Control-Problems|Link]]
   - Exact versus approximate notions of equivalence and containment : [[Verification-and-Control-Problems|Link]]

3. **Exact System Relationships** : [[Exact-System-Relationships|Link]]
   - Behavioral inclusion and behavioral equivalence : [[Exact-System-Relationships|Link]]
   - The behavioral matching game : [[Feedback-Composition-and-Controller-Synthesis|Link]]
   - Reachable states and outputs
   - Modeling abstraction and modeling refinement
   - Simulation relations and simulation preorder : [[Feedback-Composition-and-Controller-Synthesis|Link1]], [[Exact-System-Relationships|Link2]]
   - Bisimulation relations and bisimilarity
   - Quotient systems as symbolic models : [[Approximate-Symbolic-Models-for-Verification-and-Control|Link]]
   - Alternating simulation relations : [[Feedback-Composition-and-Controller-Synthesis|Link]]
   - Extended alternating simulation relations : [[Feedback-Composition-and-Controller-Synthesis|Link]]
   - Alternating bisimulation : [[Fixed-Point-Methods-for-Verification|Link]]

4. **Fixed-Point Methods for Verification** : [[Fixed-Point-Methods-for-Verification|Link]]
   - Myhill–Nerode construction for output determinism : [[Fixed-Point-Methods-for-Verification|Link]]
   - Monotone set operators characterizing simulation and bisimulation : [[Fixed-Point-Methods-for-Verification|Link]]
   - Maximal fixed-points as maximal simulation and bisimulation relations
   - Polynomial-time computability for finite-state systems : [[Exact-Symbolic-Models-for-Control|Link]]

5. **Feedback Composition and Controller Synthesis** : [[Feedback-Composition-and-Controller-Synthesis|Link]]
   - Controllable versus uncontrollable inputs
   - Concurrent control/disturbance input model
   - Controllers as output-history maps : [[Feedback-Composition-and-Controller-Synthesis|Link]]
   - Feedback composition via alternating simulation : [[Feedback-Composition-and-Controller-Synthesis|Link]]
   - Safety games and least restrictive controllers : [[Feedback-Composition-and-Controller-Synthesis|Link]]
   - Reachability games and the absence of a minimally restrictive controller : [[Feedback-Composition-and-Controller-Synthesis|Link]]
   - Behavioral games : [[Feedback-Composition-and-Controller-Synthesis|Link]]
   - Simulation games and bisimulation games : [[Feedback-Composition-and-Controller-Synthesis|Link]]
   - Safety versus liveness properties

6. **Lattice and Fixed-Point Theory** : [[Lattice-and-Fixed-Point-Theory|Link]]
   - Pre-orders, partial orders, and total orders
   - Lattices and complete lattices
   - Monotone, sup-continuous, and inf-continuous functions : [[Lattice-and-Fixed-Point-Theory|Link]]
   - Tarski's fixed-point theorem : [[Lattice-and-Fixed-Point-Theory|Link]]
   - Constructive computation of extremal fixed-points by iteration : [[Lattice-and-Fixed-Point-Theory|Link]]

7. **Hybrid Dynamical Systems** : [[Hybrid-Dynamical-Systems|Link]]
   - Dynamical systems and their trajectories : [[Hybrid-Dynamical-Systems|Link]]
   - Hybrid dynamical systems: invariants, guards, resets : [[Hybrid-Dynamical-Systems|Link]]
   - Discrete transitions versus continuous flows : [[Hybrid-Dynamical-Systems|Link]]
   - Modeling hybrid dynamical systems as systems : [[Hybrid-Dynamical-Systems|Link]]

8. **Timed Automata and Quotient-Based Abstraction** : [[Timed-Automata-and-Quotient-Based-Abstraction|Link]]
   - Timed automata as a restricted class of hybrid dynamical systems : [[Hybrid-Dynamical-Systems|Link1]], [[Order-Minimal-Structures-and-Definability|Link2]]
   - Refining an equivalence relation to respect invariants, guards, resets, and flow : [[Timed-Automata-and-Quotient-Based-Abstraction|Link]]
   - Existence of finite-state bisimilar models for timed automata

9. **Order-Minimal Structures and Definability** : [[Order-Minimal-Structures-and-Definability|Link]]
   - Order minimal structures over the reals : [[Order-Minimal-Structures-and-Definability|Link]]
   - Semi-linear, semi-algebraic, and semi-exponential-algebraic sets
   - Definable sets and definable maps : [[Order-Minimal-Structures-and-Definability|Link]]
   - Uniform finiteness theorem : [[Order-Minimal-Structures-and-Definability|Link]]
   - Definable finite equivalence relations
   - Eigenvalue conditions for finite-state bisimilar linear systems : [[Order-Minimal-Structures-and-Definability|Link]]
   - Strict feed-forward form and locally finite dynamical systems : [[Order-Minimal-Structures-and-Definability|Link]]
   - Phi-relatedness and linearization by embedding : [[Order-Minimal-Structures-and-Definability|Link]]

10. **Sign-Based Abstractions** : [[Sign-Based-Abstractions|Link]]
    - Sign conditions induced by smooth real-valued functions : [[Sign-Based-Abstractions|Link]]
    - Lie derivatives and their role in constraining sign transitions
    - Closure/saturation with respect to the sign of the Lie derivative
    - Tightness of sign-based abstractions : [[Sign-Based-Abstractions|Link]]

11. **Barrier Certificates and Reachable Set Computation** : [[Barrier-Certificates-and-Reachable-Set-Computation|Link]]
    - Barrier certificates as a direct, Lyapunov-like safety proof : [[Barrier-Certificates-and-Reachable-Set-Computation|Link]]
    - Sum-of-squares search for polynomial barrier certificates
    - Zonotopes as a set representation : [[Barrier-Certificates-and-Reachable-Set-Computation|Link]]
    - Over-approximation of reachable sets for linear dynamics : [[Approximate-System-Relationships|Link]]

12. **Exact Symbolic Models for Control** : [[Exact-Symbolic-Models-for-Control|Link]]
    - Discrete-time and continuous-time control systems as systems : [[Exact-Symbolic-Models-for-Control|Link]]
    - Controllability and the controllability matrix
    - Controller refinement from an abstraction to the original system : [[Exact-Symbolic-Models-for-Control|Link1]], [[Hybrid-Dynamical-Systems|Link2]], [[Timed-Automata-and-Quotient-Based-Abstraction|Link3]]
    - Alternating bisimilar abstractions and two-way controller existence
    - Adapted sets and adapted partitions for discrete-time linear systems : [[Exact-Symbolic-Models-for-Control|Link]]
    - The Pre operator and partition-refinement algorithms : [[Exact-Symbolic-Models-for-Control|Link]]
    - Multi-affine control systems on n-rectangles : [[Exact-Symbolic-Models-for-Control|Link1]], [[Approximate-Symbolic-Models-for-Verification-and-Control|Link2]]
    - The rectangular invariant problem and the control-to-facet problem : [[Exact-Symbolic-Models-for-Control|Link]]
    - Vertex-based feedback synthesis

13. **Approximate System Relationships** : [[Approximate-System-Relationships|Link]]
    - Metric systems : [[Approximate-System-Relationships|Link]]
    - Epsilon-approximate simulation and bisimulation : [[Approximate-System-Relationships|Link]]
    - Epsilon-inflation of a set : [[Approximate-System-Relationships|Link]]
    - Precision accumulation under composition of approximate relations : [[Approximate-System-Relationships|Link]]
    - Epsilon-approximate alternating simulation and bisimulation : [[Approximate-System-Relationships|Link]]

14. **Stability Theory for Approximate Abstraction** : [[Stability-Theory-for-Approximate-Abstraction|Link]]
    - Asymptotically stable and globally asymptotically stable equilibria : [[Stability-Theory-for-Approximate-Abstraction|Link]]
    - Lyapunov functions and weak Lyapunov functions : [[Approximate-Symbolic-Models-for-Verification-and-Control|Link1]], [[Stability-Theory-for-Approximate-Abstraction|Link2]]
    - Incremental global asymptotic stability (delta-GAS)
    - Input-to-state stability (ISS) : [[Stability-Theory-for-Approximate-Abstraction|Link]]
    - Incremental global input-to-state stability (delta-ISS) : [[Stability-Theory-for-Approximate-Abstraction|Link]]
    - Class K, K-infinity, and KL comparison functions : [[Stability-Theory-for-Approximate-Abstraction|Link]]
    - Necessity of Lyapunov functions for approximate bisimulation : [[Approximate-System-Relationships|Link]]

15. **Approximate Symbolic Models for Verification and Control** : [[Approximate-Symbolic-Models-for-Verification-and-Control|Link]]
    - Time-triggered sampled systems : [[Approximate-Symbolic-Models-for-Verification-and-Control|Link]]
    - Time-and-space quantized systems
    - Precision/time/space quantization trade-offs
    - Sampled-data (piecewise-constant input) abstractions and input quantization : [[Approximate-Symbolic-Models-for-Verification-and-Control|Link]]
    - Reachable-set-based disturbance quantization
    - Approximate feedback composition and controller refinement : [[Feedback-Composition-and-Controller-Synthesis|Link]]
    - Switched affine systems and common Lyapunov functions : [[Approximate-Symbolic-Models-for-Verification-and-Control|Link]]
    - Dwell time : [[Exact-Symbolic-Models-for-Control|Link]]

---
