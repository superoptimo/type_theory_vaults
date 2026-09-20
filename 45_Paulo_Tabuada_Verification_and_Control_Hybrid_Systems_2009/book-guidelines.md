# Verification and Control of Hybrid Systems: A Symbolic Approach — Guidelines

## Header

**Title:** Verification and Control of Hybrid Systems: A Symbolic Approach
**Author(s):** Paulo Tabuada (Foreword by Rajeev Alur)
**Publication:** Springer, 2009 (DOI: 10.1007/978-1-4419-0224-5)

**Brief Summary:**
This book develops a unified, symbolic-model approach to the verification and control of hybrid systems — systems combining finite-state (software/discrete) and infinite-state (differential-equation/continuous) dynamics. Its organizing idea is the notion of *system* as a labeled transition structure, related to other systems through *simulation* and *bisimulation* relations (and their alternating, control-oriented counterparts), which together provide a common language for both exact and approximate abstraction. The book proceeds from finite-state verification and control theory (Parts I–II), through exact symbolic (bisimilar) models of infinite-state dynamical, hybrid, and control systems (Part III), to approximate symbolic models built from stability/Lyapunov arguments for systems that admit no exact finite-state bisimulation (Part IV).

**Intent of the Author:**
Tabuada aims to show that many seemingly disparate results in hybrid-systems verification and control — timed automata, order-minimal abstractions, sign-based abstractions, barrier certificates, symbolic models for linear and multi-affine control, approximate bisimulation — are instances of one recurring theme: constructing simulation or bisimulation relations (exact or approximate) between an infinite-state system and a finite-state symbolic model, and then solving verification/control problems on the finite model via fixed-point algorithms.

---

## Topic List

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

## Chapter Summaries

### Chapter 1: Systems (pp. 3–21)

**Summary:** Introduces the book's central mathematical object — the *system*, a sextuple of states, initial states, inputs, transitions, outputs, and an output map — general enough to model finite-state automata, discrete- and continuous-time dynamical and control systems, and hybrid systems, and equips it with a composition operation for building larger systems from smaller ones.

**Key Definitions & Concepts by Section:**
- **1.1 System definition** — system $S = (X, X_0, U, \to, Y, H)$; finite-state vs. infinite-state system; $u$-successor/predecessor, $\mathrm{Post}_u(x)$; blocking/nonblocking; deterministic and output-deterministic systems; nondeterministic systems. : [[Order-Minimal-Structures-and-Definability|Link1]], [[Sign-Based-Abstractions|Link2]], [[Systems-as-the-Common-Mathematical-Model|Link3]], [[Timed-Automata-and-Quotient-Based-Abstraction|Link4]]
- **1.2 System behavior** — finite and infinite internal behavior; initialized behavior; external behavior via the output map $H$; finite external behavior $B(S)$ and infinite external behavior $B^\omega(S)$; extending a system's state to record inputs. : [[Exact-System-Relationships|Link]]
- **1.3 Examples** — finite-state systems (communication protocol, software averaging loop); infinite-state dynamical systems (national income model, rigid-body Euler equations) and control systems (controlled national income, satellite with gas jets); hybrid systems (real-time scheduling task with clocks/invariants/guards/resets, boost DC-DC converter).
- **1.4 Composing systems** — composition $S_a \times_I S_b$ with interconnection relation $I \subseteq X_a\times X_b\times U_a\times U_b$; trivial interconnection $S_a \times S_b$; behavior inclusion under composition, $B(S_a\times_I S_b) \subseteq B(S_a)\times B(S_b)$. : [[Feedback-Composition-and-Controller-Synthesis|Link1]], [[Systems-as-the-Common-Mathematical-Model|Link2]]

**Key Questions:**
1. Why does the notion of system deliberately use a *relation* rather than a function for transitions, and what does this buy when later modeling disturbances and nondeterminism?
2. How does treating "time" itself as an input for continuous-time dynamical/control systems reconcile with the discrete, symbolic notion of "input" used for finite-state systems?
3. In the real-time scheduling and DC-DC converter examples, what distinguishes a *discrete transition* from a *continuous flow*, and why does modeling both require augmenting the state with a finite and an infinite part?

---

### Chapter 2: Verification Problems (pp. 23–24)

**Summary:** Poses the book's two canonical verification questions — equivalence and pre-order (containment) between a system and a specification — that all later verification techniques answer for specific classes of systems and specific notions of equivalence/pre-order. : [[Verification-and-Control-Problems|Link]]

**Key Definitions & Concepts:**
- Equivalence problem: given $S_a, S_b$, when does $S_a \cong S_b$? Interpreted either as design-conforms-to-specification or as two candidate models of the same phenomenon.
- Pre-order problem: given $S_a, S_b$, when does $S_a \preceq S_b$ ("$S_a$ is included in $S_b$")?
- Distinction between exact equivalence (outputs must match exactly) and approximate equivalence (outputs may differ up to a precision), the latter natural for infinite-state systems.

**Key Questions:**
1. Why is the pre-order problem introduced as a *weaker* alternative to equivalence, and in what circumstances would equivalence be an unreasonable requirement to impose on a designed system $S_a$?
2. What is gained, for infinite-state dynamical/control/hybrid systems specifically, by relaxing exact equivalence to approximate equivalence?

---

### Chapter 3: Control Problems (pp. 25–26)

**Summary:** Extends the two verification problems to controller-synthesis problems, asking for the existence and construction of a controller system $S_c$ and interconnection relation such that the composition of $S_c$ with a plant $S_a$ meets a specification $S_b$, either exactly or up to a pre-order. : [[Exact-Symbolic-Models-for-Control|Link1]], [[Verification-and-Control-Problems|Link2]]

**Key Definitions & Concepts:**
- Control problem for equivalence: find $S_c, I$ such that $S_c \times_I S_a \cong S_b$.
- Control problem for pre-order: find $S_c, I$ such that $S_c \times_I S_a \preceq S_b$.
- The observation that once $S_c$ is designed to enforce the specification, no further formal verification of $S_c \times_I S_a$ against $S_b$ is needed — synthesis subsumes verification.
- Why $S_b \preceq S_c \times_I S_a$ (the "opposite" control problem) is uninteresting: composing with $S_c$ can only further constrain $S_a$.

**Key Questions:**
1. Why does successfully solving the control-for-equivalence problem eliminate the need for a separate verification step on the closed-loop system?
2. Why is $S_b \preceq S_c\times_I S_a$ never a meaningful control objective, given that composition can only restrict $S_a$'s behavior?

---

### Chapter 4: Exact System Relationships (pp. 29–42)

**Summary:** Introduces the precise formal relationships — behavioral inclusion/equivalence, simulation/bisimulation, and alternating simulation/bisimulation — used throughout the book to compare two systems, laying the mathematical vocabulary for both verification (Chapter 5) and control (Chapter 6). : [[Exact-System-Relationships|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Behavioral relationships** — behavioral inclusion $S_a \preceq_B S_b$ ($B^\omega(S_a) \subseteq B^\omega(S_b)$); behavioral equivalence $S_a \cong_B S_b$; the "behavioral matching game" interpretation; reachable states/outputs and $\mathrm{Reach}(S)$; the safety problem ($\mathrm{Reach}(S_a) \cap B = \emptyset$ for unsafe set $B$); modeling abstraction and modeling refinement. : [[Exact-System-Relationships|Link]]
- **4.2 Similarity relationships** — simulation relation (respects initial states, outputs, and transitions); simulation $S_a \preceq_S S_b$; simulation implies behavioral inclusion but not conversely in general (partial converse when $S_b$ output deterministic and $S_a$ nonblocking); bisimulation relation and bisimilarity $S_a \cong_S S_b$; quotient system $S/Q$ as a symbolic model; correspondence between quotienting and bisimulation (Theorem 4.18). : [[Exact-System-Relationships|Link]]
- **4.3 Alternating similarity relationships** — alternating simulation relation; alternating simulation $S_a \preceq_{AS} S_b$; extended alternating simulation relation $R^e \subseteq X_a\times X_b\times U_a\times U_b$; alternating bisimulation $S_a \cong_{AS} S_b$; coincidence with ordinary simulation for deterministic systems. : [[Exact-System-Relationships|Link]]

**Key Questions:**
1. Why does simulation ($S_a \preceq_S S_b$) not follow automatically from behavioral inclusion in general, and under what determinism/nonblocking assumptions does the gap close?
2. What is the intuitive difference between a simulation relation and an *alternating* simulation relation, and why is the alternating notion the one needed once "input" is reinterpreted as a controllable choice?
3. In what sense is the quotient system $S/Q$ guaranteed to be bisimilar to $S$ (rather than merely simulating it) only when $Q$ is itself a bisimulation relation on $S$?

---

### Chapter 5: Verification (pp. 43–50)

**Summary:** Shows how to reduce the behavioral verification problem to a similarity (simulation/bisimulation) problem by making the specification output-deterministic via a Myhill–Nerode-style construction, then shows that the maximal simulation and bisimulation relations between two finite-state systems can be computed as maximal fixed-points of monotone set operators. : [[Verification-and-Control-Problems|Link1]], [[Fixed-Point-Methods-for-Verification|Link2]]

**Key Definitions & Concepts by Section:**
- **5.1 Behavioral relations** — a property $P$ as a subset of $Y_b^\omega$; reduction of $B^\omega(S_a) \subseteq B^\omega(S_b)$ to $S_a \preceq_S S_b$; Proposition 5.1: any $S_b$ has a behaviorally equivalent output-deterministic system $S_c$, built from Myhill–Nerode equivalence classes.
- **5.2 Similarity relations** — the monotone operator $F$ characterizing simulation relations as pre-fixed-points; Theorem 5.3: the maximal simulation relation is the maximal fixed-point $Z = \lim_{i\to\infty} F^i(X_a\times X_b)$, polynomial-time computable; the analogous operator $G$ whose maximal fixed-point characterizes the maximal bisimulation relation (Theorem 5.6). : [[Approximate-System-Relationships|Link]]

**Key Questions:**
1. Why is it "without loss of generality" to assume the specification system $S_b$ is output deterministic, and how does the Myhill–Nerode construction guarantee this while preserving behavioral equivalence?
2. Why must iterating the operator $F$ start from the full set $X_a \times X_b$ (rather than $\emptyset$) to converge to the *maximal* simulation relation?
3. Why does the chapter avoid discussing liveness specifications, and where does liveness reappear in the book?

---

### Chapter 6: Control (pp. 51–70)

**Summary:** Develops the control counterpart of Chapter 5: defines feedback composition via alternating simulation relations, then poses and fixed-point-solves four classes of controller-synthesis games (safety, reachability, similarity/simulation, bisimulation), showing which give a unique "least restrictive" controller and which (reachability) do not.

**Key Definitions & Concepts by Section:**
- **6.1 Feedback composition** — controllable vs. uncontrollable inputs; the concurrent control/disturbance input model adopted in the book; controller as a map $\varphi: X^* \to 2^U$; feedback composability (existence of an alternating simulation relation from $S_c$ to $S_a$); feedback composition $S_c \times_F S_a$. : [[Feedback-Composition-and-Controller-Synthesis|Link]]
- **6.2 Safety games** — safety game (find $S_c$ with $S_c\times_F S_a$ nonblocking and $\mathrm{Reach}(S_c\times_F S_a)\subseteq W$); operator $F_W$, maximal fixed-point $Z=\lim_i F_W^i(X_a)$ characterizing solvability (Theorem 6.6); the canonical controller built from the maximal fixed-point is least restrictive (Proposition 6.8). : [[Feedback-Composition-and-Controller-Synthesis|Link]]
- **6.3 Reachability games** — reachability game (every maximal behavior must eventually visit $W$); operator $G_W$, minimal fixed-point (Theorem 6.10); no minimally-restrictive controller exists in general (Example 6.12) — reachability is a liveness property. : [[Feedback-Composition-and-Controller-Synthesis|Link]]
- **6.4 Behavioral games** — behavior inclusion game, reducible to a simulation game when the specification is output deterministic. : [[Feedback-Composition-and-Controller-Synthesis|Link]]
- **6.5 Similarity games** — simulation game and operator $F_C$, Theorem 6.15; bisimulation game and operator $G_C$, Theorem 6.19; both solvable in polynomial time via maximal fixed-points for finite-state systems.

**Key Questions:**
1. Why must the interconnection relation used for control be the extended relation of an *alternating* simulation relation rather than an ordinary simulation relation?
2. Why does the safety game admit a unique least-restrictive (optimal) controller while the reachability game does not, and how does this connect to the safety/liveness distinction?
3. How do the operators $F_C$ and $G_C$ generalize $F$ and $G$ from Chapter 5, and why does the bisimulation game's solvability condition differ in form from the simulation game's?

---

### Chapter 7: Exact Symbolic Models for Verification (pp. 73–110)

**Summary:** Shows how to construct finite-state systems that are exactly bisimilar (or simulating) to infinite-state dynamical and hybrid dynamical systems, using several complementary techniques — quotienting by equivalence relations respecting the dynamics (timed automata, order-minimal structures), sign-based abstractions from Lie derivatives, barrier certificates for direct safety proofs, and reachable-set over-approximation via zonotopes. : [[Exact-Symbolic-Models-for-Control|Link1]], [[Approximate-Symbolic-Models-for-Verification-and-Control|Link2]]

**Key Definitions & Concepts by Section:**
- **7.1 Dynamical and hybrid dynamical systems as systems** — dynamical system $\Sigma=(\mathbb{R}^n,f)$ and its flow $\theta$; the system $S_Q^L(\Sigma)$ built from a finite equivalence relation $Q$ (output changes sampled as transitions, with a repeated-output rule keeping unbounded trajectories non-blocking); hybrid dynamical system with invariants, guards, resets; discrete transitions vs. continuous flows; the associated system $S_Q^L(\Sigma)$. : [[Hybrid-Dynamical-Systems|Link1]], [[Systems-as-the-Common-Mathematical-Model|Link2]]
- **7.2 Timed automata** — timed automaton (rational-constant clock invariants/guards, resets to $x$ or $0$, unit-slope dynamics); Lemma 7.7 (sufficient conditions for a finite bisimilar system to exist); Theorem 7.8 (quotient-based abstractions always exist for timed automata). : [[Order-Minimal-Structures-and-Definability|Link1]], [[Timed-Automata-and-Quotient-Based-Abstraction|Link2]]
- **7.3 Order minimal hybrid dynamical systems** — order minimal structure $\mathcal{S}=\{S_n\}$; definable sets/maps; Theorem 7.11 (Uniform finiteness); Theorem 7.13 (any complete system with definable flow has a finite-state bisimilar quotient for any definable finite equivalence relation); Corollary 7.14 (real or diagonalizable-imaginary eigenvalues suffice); a spiraling counterexample showing the eigenvalue condition is tight; Corollary 7.16 (strict feed-forward form dynamics); Corollary 7.17 (extension to hybrid systems with constant reset maps). : [[Hybrid-Dynamical-Systems|Link]]
- **7.4 Sign based abstractions** — sign conditions $g: P\to\{1,0,-1\}$; Lie derivative $L_f p$; the finite-state system $S_P^L(\Sigma)$; Proposition 7.21 ($S_{\bar PL}(\Sigma)\preceq_S S_{PL}(\Sigma)$ — always sound for safety); closure/saturation with respect to the sign of the Lie derivative and Theorem 7.25 (tight abstraction bound once closed). : [[Sign-Based-Abstractions|Link]]
- **7.5 Barrier certificates** — barrier certificate $E$ (Theorem 7.27: sign conditions on $E$ and $L_fE\le 0$ imply safety); connection to sum-of-squares convex optimization. : [[Barrier-Certificates-and-Reachable-Set-Computation|Link]]
- **7.6 Computation of reachable sets** — zonotope $Z=(c,\langle v_1,\dots,v_k\rangle)$; Proposition 7.31 (a bloated zonotope over-approximates $R_{[0,\tau]}(Z)$ for linear dynamics); iterative construction over a time-discretization. : [[Barrier-Certificates-and-Reachable-Set-Computation|Link]]
- **7.7 Advanced topics** — $\varphi$-relatedness of dynamical systems; locally finite dynamical system; Theorem 7.36 (every locally finite system is $\varphi$-related to a linear system on a higher-dimensional space). : [[Order-Minimal-Structures-and-Definability|Link]]

**Key Questions:**
1. Why does the transition relation of $S_Q^L(\Sigma)$ need a special self-loop rule for trajectories whose output never changes, and what pathology would arise without it?
2. What role does order-minimality (Theorem 7.11, Uniform Finiteness) play in guaranteeing a *finite*-state bisimilar quotient, and why does the spiraling counterexample (eigenvalues $0.1\pm i$) fail this?
3. How do sign-based abstractions and barrier certificates differ in what they require you to construct for a sound safety proof, and when might one be preferred over the other?

---

### Chapter 8: Exact Symbolic Models for Control (pp. 113–142)

**Summary:** Extends Chapter 7's exact-abstraction techniques from verification to control: shows how a controller synthesized on a finite-state abstraction can be refined to control the original infinite-state system (via alternating simulation), and develops two concrete classes of finite-state-abstractable control systems — discrete-time linear systems (via "adapted" partitions) and continuous-time multi-affine systems on rectangles (via facet-crossing/invariance conditions). : [[Exact-Symbolic-Models-for-Control|Link]]

**Key Definitions & Concepts by Section:**
- **8.1 Control systems as systems** — discrete-time control system $\Sigma=(\mathbb{R}^n,\mathbb{R}^m,f)$ and $S_Q(\Sigma)$; controllability and its rank characterization via the controllability matrix (Theorem 8.4); continuous-time control system, feedback law, closed-loop system. : [[Approximate-Symbolic-Models-for-Verification-and-Control|Link1]], [[Exact-Symbolic-Models-for-Control|Link2]], [[Systems-as-the-Common-Mathematical-Model|Link3]]
- **8.2 Controller refinement** — Proposition 8.7 ($S_c\preceq_{AS}S_a \wedge S_a\preceq_{AS}S_b \Rightarrow S_c\times_F S_a \preceq_{AS} S_b$): a controller synthesized on an abstraction can be refined to control the original system; the stronger two-way guarantee when the abstraction is alternatingly bisimilar to the original. : [[Exact-Symbolic-Models-for-Control|Link]]
- **8.3 Discrete-time linear control systems** — adapted sets/partitions (Definition 8.8); Theorem 8.10 (any adapted partition yields a finite-state bisimilar quotient); the $\mathrm{Pre}$ operator and Algorithm 8.1 (partition refinement to maximal self-bisimulation); a long worked Mars-rover camera/heater example combining a linear abstraction, a finite-state heater model, their composition, a string specification, and controller refinement — illustrating the full abstract-synthesize-refine pipeline. : [[Exact-Symbolic-Models-for-Control|Link]]
- **8.4 Continuous-time multi-affine control systems** — multi-affine vector fields; $n$-rectangles and vertex sets $V(E)$; the rectangular invariant problem (Theorem 8.22) and the control-to-facet problem (Theorem 8.23), both checkable at vertices; completion of a rectangle collection into a partition; the finite-state system $S_{\mathcal E}(\Sigma)$ and Theorem 8.26 ($S_{\mathcal E}(\Sigma)\preceq_S S_Q(\Sigma)$, also alternating). : [[Exact-Symbolic-Models-for-Control|Link]]

**Key Questions:**
1. Why must controller refinement use *alternating* simulation from the abstraction to the original system, and why does only the *bisimilar* case give a two-way existence guarantee?
2. What is the role of the vectors $c_r$ and integers $\nu_r$ in the definition of adapted sets, and why does Theorem 8.10 require the partition to be *adapted* rather than arbitrary?
3. In the rectangular-invariant and control-to-facet problems, why is it sufficient to check sign/direction conditions only at the vertices of an $n$-rectangle, and how does multi-affinity make this possible?

---

### Chapter 9: Approximate System Relationships (pp. 145–149)

**Summary:** Generalizes the exact similarity relationships of Chapter 4 to a metric setting, relaxing the requirement that related states produce identical outputs to one where outputs may differ by at most a precision $\varepsilon$ — the foundation for all abstraction results in Part IV. : [[Approximate-System-Relationships|Link]]

**Key Definitions & Concepts by Section:**
- **9.1 Approximate similarity relationships** — metric system; $\varepsilon$-approximate simulation relation (Definition 9.2) and $S_a\preceq_S^\varepsilon S_b$ (reduces to exact simulation at $\varepsilon=0$); Proposition 9.4 ($S_a\preceq_S^\varepsilon S_b \Rightarrow \mathrm{Reach}(S_a)\subseteq\mathrm{Reach}^\varepsilon(S_b)$); $\varepsilon$-approximate bisimulation $S_a\cong_S^\varepsilon S_b$; composition of approximate relations accumulates precision ($a\varepsilon_b + b\varepsilon_c$). : [[Approximate-System-Relationships|Link]]
- **9.2 Approximate alternating similarity relationships** — $\varepsilon$-approximate alternating simulation relation and $S_a\preceq_{AS}^\varepsilon S_b$; extended $\varepsilon$-approximate alternating simulation relation; $\varepsilon$-approximate alternating bisimulation. : [[Approximate-System-Relationships|Link]]

**Key Questions:**
1. Why does $\varepsilon=0$ collapse approximate simulation exactly back to exact simulation, and what does this tell us about approximate relations as a strict generalization?
2. Why does composing two approximate (bi)simulation relations *add* their precisions, and what consequence does this have for chaining several layers of abstraction?
3. How does Proposition 9.4 turn an approximate-simulation relationship into a usable sufficient condition for safety verification?

---

### Chapter 10: Approximate Symbolic Models for Verification (pp. 151–166)

**Summary:** Constructs finite-state (or countable) systems that are $\varepsilon$-approximately bisimilar to affine and nonlinear dynamical systems, by quantizing time and space and using Lyapunov-function-based stability estimates to bound the approximation error — a fundamentally different strategy from Chapter 7's exact quotient-based abstractions, working for any sufficiently stable system rather than only definable ones. : [[Approximate-Symbolic-Models-for-Verification-and-Control|Link]]

**Key Definitions & Concepts by Section:**
- **10.1 Stability of linear dynamical systems** — asymptotically stable equilibrium (Definition 10.1) and its eigenvalue characterization (Theorem 10.2); Lyapunov function and weak Lyapunov function; Theorem 10.4 (Lyapunov function existence iff stability); Proposition 10.5 (norm-equivalence and generalized-triangle-inequality bounds for quadratic-form Lyapunov functions). : [[Hybrid-Dynamical-Systems|Link]]
- **10.2 Dynamical systems as systems** — the time-triggered sampled system $S_\tau(\Sigma)$ contrasted with the output-triggered $S_Q^L(\Sigma)$ of Chapter 7. : [[Hybrid-Dynamical-Systems|Link1]], [[Order-Minimal-Structures-and-Definability|Link2]], [[Systems-as-the-Common-Mathematical-Model|Link3]]
- **10.3 Symbolic models for affine dynamical systems** — the time-and-space-quantized system $S_{\tau\eta}(\Sigma)$; Theorem 10.8 (for any $\varepsilon,\tau$ there is a space quantization $\eta$ satisfying a trade-off inequality making $S_{\tau\eta}(\Sigma)$ an $\varepsilon$-approximate bisimulation of $S_\tau(\Sigma)$); Corollary 10.10 (affine extension); Proposition 10.11 (partial converse — such bisimulations for all $\varepsilon,\tau$ imply existence of a weak Lyapunov function). : [[Approximate-Symbolic-Models-for-Verification-and-Control|Link]]
- **10.4 Advanced topics** — class $\mathcal{K}_\infty$/$\mathcal{KL}$ comparison functions; globally asymptotically stable (GAS) equilibrium; incremental global asymptotic stability ($\delta$-GAS, Definition 10.13); $\delta$-GAS Lyapunov function and Theorem 10.15; Theorem 10.16 (nonlinear generalization of Theorem 10.8). : [[Order-Minimal-Structures-and-Definability|Link]]

**Key Questions:**
1. Why is asymptotic stability essential to Theorem 10.8's construction — what breaks in the trade-off inequality if the decay rate $\lambda=0$?
2. In what sense does Proposition 10.11 show that Lyapunov functions are an *essential ingredient*, not just a convenient proof technique, of approximate bisimulation?
3. Why does the nonlinear generalization require the *stronger* notion of incremental stability ($\delta$-GAS) rather than ordinary GAS?

---

### Chapter 11: Approximate Symbolic Models for Control (pp. 167–189)

**Summary:** Extends the approximate-abstraction machinery of Chapter 10 to control and switched systems, introducing approximate feedback composition/refinement and constructing finite-state approximately (bi)similar models for affine control systems (with and without disturbances) and switched affine systems, using input-to-state stability and (common) Lyapunov functions; a worked DC-DC converter example closes the chapter. : [[Approximate-Symbolic-Models-for-Verification-and-Control|Link]]

**Key Definitions & Concepts by Section:**
- **11.1 Stability of linear control systems** — affine control system with control input $\chi$ and disturbance input $\delta$; input-to-state stability (ISS, Definition 11.1); ISS-Lyapunov function and Theorem 11.3. : [[Exact-Symbolic-Models-for-Control|Link1]], [[Approximate-Symbolic-Models-for-Verification-and-Control|Link2]]
- **11.2 Control and switched systems as systems** — $S_\tau(\Sigma)$ for control systems; switched affine system (Definition 11.5); supervisory controller; $S_\tau(\Sigma)$ for switched affine systems. : [[Exact-Symbolic-Models-for-Control|Link]]
- **11.3 Approximate feedback composition and controller refinement** — approximate composition $S_a\times_I^\varepsilon S_b$ with averaged output map, commutative and generalizing exact composition; Proposition 11.8 ($\tfrac12\varepsilon$-approximate simulations to each side); approximate feedback composition; Proposition 11.10 (approximate refinement, precisions add). : [[Feedback-Composition-and-Controller-Synthesis|Link]]
- **11.4 Symbolic models for affine control systems** — quantized system $S_{\tau\eta}(\Sigma)$; Theorem 11.12 (surjective $\varepsilon$-approximate alternating simulation given a Lyapunov function); piecewise-constant/sampled-data system $S_{\tau\eta\omega}(\Sigma)$; Theorem 11.14 (strengthens to bisimulation for ISS systems); worked safety-game and trajectory-search examples; disturbance handling via reachable-set quantization $S_{\tau\eta\eta}(\Sigma)$ and Theorem 11.18. : [[Approximate-Symbolic-Models-for-Verification-and-Control|Link]]
- **11.5 Symbolic models for switched affine systems** — $S_{\tau\eta}(\Sigma)$ for switched systems; common Lyapunov function; Corollary 11.20 (approximate bisimulation given a common Lyapunov function); boost DC-DC converter worked example. : [[Approximate-Symbolic-Models-for-Verification-and-Control|Link]]
- **11.6 Advanced topics** — incremental global asymptotic stability ($\delta$-GAS) and incremental input-to-state stability ($\delta$-ISS) for control systems; Theorem 11.25 (equivalence with Lyapunov functions); Theorem 11.26 (nonlinear generalization of Theorems 11.12/11.14). : [[Order-Minimal-Structures-and-Definability|Link]]

**Key Questions:**
1. Why does approximate feedback composition average the output maps $\tfrac12(H_a+H_b)$ rather than projecting to either side, and how does this yield $\tfrac12\varepsilon$-approximate simulations to both sides?
2. What is the essential difference between $S_{\tau\eta}(\Sigma)$ (arbitrary curves) and $S_{\tau\eta\omega}(\Sigma)$ (piecewise-constant, quantized inputs), and why does only the latter support the stronger bisimulation result?
3. Why is a *common* Lyapunov function required for the switched-system result (Corollary 11.20), and what alternative (dwell time) is needed when each mode has only its own Lyapunov function?

---

### Appendix: Lattice Theory and Fixed-Points (pp. 191–193)

**Summary:** A short reference appendix reviewing the order-theoretic and fixed-point machinery — culminating in Tarski's fixed-point theorem — that underlies all the fixed-point algorithms used for verification and control synthesis throughout Chapters 5, 6, and 8. : [[Approximate-Symbolic-Models-for-Verification-and-Control|Link]]

**Key Definitions & Concepts:**
- Pre-order, partial order, total order; supremum and infimum; lattice and complete lattice (e.g. $(2^Z,\subseteq)$).
- Monotone, sup-continuous, and inf-continuous functions on a complete lattice.
- **Tarski's fixed-point theorem** (Theorem A.4): a monotone $f$ on a complete lattice has fixed points, and $\sup Y$/$\inf Y$ of the fixed-point set $Y$ are themselves fixed points, characterized as $\sup\{x\mid x\sqsubseteq f(x)\}$ and $\inf\{x\mid f(x)\sqsubseteq x\}$.
- Constructive computation of extremal fixed points by iteration (Theorem A.5); on a finite lattice every monotone function is automatically sup- and inf-continuous, justifying the "iterate until fixed" algorithms used earlier in the book.

**Key Questions:**
1. Why does Tarski's theorem guarantee that the maximal/minimal fixed-point of a monotone operator is itself a fixed point, rather than merely an upper/lower bound on the fixed-point set?
2. Why does finiteness of the underlying lattice automatically make every monotone operator sup- and inf-continuous, and why does this matter for the termination of the book's verification/control algorithms?
