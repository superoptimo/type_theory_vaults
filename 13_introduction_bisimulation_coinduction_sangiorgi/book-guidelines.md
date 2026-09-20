# Introduction to Bisimulation and Coinduction — Guidelines

## Header

**Title:** Introduction to Bisimulation and Coinduction
**Author(s):** Davide Sangiorgi
**Publication:** Cambridge University Press, 2012 (ISBN 978-1-107-00363-7)

**Brief Summary:**
This book is a foundational introduction to bisimulation and coinduction, the two central ideas that let computer scientists define and reason about potentially infinite objects — most prominently processes in concurrency theory. It develops coinduction and its duality with induction from fixed-point theory over complete lattices, then builds up the theory of bisimulation as a behavioural equivalence for processes, comparing it systematically with alternative notions of behavioural equivalence (trace, testing, failure, ready, simulation-based equivalences). Along the way it introduces a core process calculus (essentially Milner's CCS) to illustrate the interplay between inductive syntax and coinductive semantics, and closes with a general method — barbed congruence — for deriving bisimilarity-based equalities in arbitrary process languages.

**Intent of the Author:**
Sangiorgi wrote the book (with a companion, more advanced volume co-edited with Jan Rutten) to fill a gap he perceived in the literature: no textbook offered newcomers a comprehensive, self-contained treatment of bisimulation and coinduction, despite their rapidly growing relevance well beyond concurrency theory (in mathematics, modal logic, AI, and elsewhere).

---

## Topic List

1. **Coinduction and the Duality with Induction** : [[Coinduction-and-the-Duality-with-Induction|Link]]
   - Least and greatest fixed points of monotone functions : [[Coinduction-and-the-Duality-with-Induction|Link]]
   - Posets, complete lattices, joins and meets : [[Coinduction-and-the-Duality-with-Induction|Link]]
   - The Fixed-point Theorem : [[Coinduction-and-the-Duality-with-Induction|Link]]
   - Induction and coinduction proof principles : [[Coinduction-and-the-Duality-with-Induction|Link]]
   - Sets defined inductively and coinductively by rules : [[Coinduction-and-the-Duality-with-Induction|Link]]
   - Forward closure versus backward closure : [[Coinduction-and-the-Duality-with-Induction|Link]]
   - Rule induction and rule coinduction : [[Coinduction-and-the-Duality-with-Induction|Link]]
   - Continuity and cocontinuity of functionals : [[Coinduction-and-the-Duality-with-Induction|Link]]
   - Constructive iteration over natural numbers and ordinals : [[Coinduction-and-the-Duality-with-Induction|Link]]
   - Well-founded versus non-well-founded proof trees : [[Coinduction-and-the-Duality-with-Induction|Link]]
   - Game-theoretic characterisations of inductive and coinductive sets : [[Coinduction-and-the-Duality-with-Induction|Link]]

2. **Processes and Labelled Transition Systems** : [[Processes-and-Labelled-Transition-Systems|Link]]
   - Why concurrent programs cannot be modeled as functions
   - Interaction as the basis of concurrent computation : [[Processes-and-Labelled-Transition-Systems|Link]]
   - Labelled transition systems : [[Processes-and-Labelled-Transition-Systems|Link]]
   - Image-finiteness, finite branching, determinism : [[Processes-and-Labelled-Transition-Systems|Link]]
   - Sort of a process : [[Processes-and-Labelled-Transition-Systems|Link]]

3. **Bisimulation and Bisimilarity** : [[Bisimulation-and-Bisimilarity|Link]]
   - Definition of bisimulation via matching transitions : [[Bisimulation-and-Bisimilarity|Link]]
   - Bisimilarity as the union of all bisimulations : [[Bisimulation-and-Bisimilarity|Link]]
   - The bisimulation proof method : [[Bisimulation-and-Bisimilarity|Link]]
   - Bisimilarity as an equivalence relation : [[Bisimulation-and-Bisimilarity|Link]]
   - Bisimilarity as the largest bisimulation : [[Bisimulation-and-Bisimilarity|Link]]
   - Bisimulation up-to techniques : [[Bisimulation-and-Bisimilarity|Link]]
   - Stratification of bisimilarity by approximants : [[Bisimulation-and-Bisimilarity|Link]]
   - The bisimulation game : [[Bisimulation-and-Bisimilarity|Link]]

4. **Alternative Notions of Equality on Behaviour** : [[Alternative-Notions-of-Equality-on-Behaviour|Link]]
   - Graph isomorphism as too strong an equivalence : [[Alternative-Notions-of-Equality-on-Behaviour|Link]]
   - Trace equivalence from automata theory : [[Alternative-Notions-of-Equality-on-Behaviour|Link]]
   - Deadlock insensitivity of trace equivalence : [[Weak-Bisimulation-and-Internal-Activity|Link1]], [[Alternative-Notions-of-Equality-on-Behaviour|Link2]]
   - Similarity and simulation equivalence : [[Alternative-Notions-of-Equality-on-Behaviour|Link]]

5. **CCS and Algebraic Properties of Bisimilarity** : [[CCS-and-Algebraic-Properties-of-Bisimilarity|Link]]
   - The core CCS operators: nil, prefixing, parallel composition, choice, restriction
   - Structured operational semantics via inference rules : [[CCS-and-Algebraic-Properties-of-Bisimilarity|Link]]
   - The Expansion Lemma : [[CCS-and-Algebraic-Properties-of-Bisimilarity|Link]]
   - Bisimilarity as a congruence : [[Barbed-Bisimilarity-and-Congruence|Link1]], [[CCS-and-Algebraic-Properties-of-Bisimilarity|Link2]]
   - The De Simone format for transition rules : [[CCS-and-Algebraic-Properties-of-Bisimilarity|Link]]
   - Axiomatisation of strong bisimilarity on finite CCS : [[CCS-and-Algebraic-Properties-of-Bisimilarity|Link]]
   - Full standard form and head standard form
   - Free and bound names : [[CCS-and-Algebraic-Properties-of-Bisimilarity|Link]]

6. **Weak Bisimulation and Internal Activity** : [[Weak-Bisimulation-and-Internal-Activity|Link]]
   - Weak transitions and abstraction from $\tau$-actions
   - Weak bisimilarity : [[Barbed-Bisimilarity-and-Congruence|Link1]], [[Weak-Bisimulation-and-Internal-Activity|Link2]]
   - Divergence and fair abstraction from divergence : [[Weak-Bisimulation-and-Internal-Activity|Link]]
   - Failure of weak bisimilarity to be preserved by choice : [[Barbed-Bisimilarity-and-Congruence|Link1]], [[Weak-Bisimulation-and-Internal-Activity|Link2]]
   - Rooted weak bisimilarity : [[Barbed-Bisimilarity-and-Congruence|Link]]
   - Axiomatisation of rooted weak bisimilarity : [[Barbed-Bisimilarity-and-Congruence|Link1]], [[CCS-and-Algebraic-Properties-of-Bisimilarity|Link2]]
   - Prebisimilarity with divergence : [[Weak-Bisimulation-and-Internal-Activity|Link]]
   - Dynamic bisimilarity : [[Weak-Bisimulation-and-Internal-Activity|Link]]
   - Branching, $\eta$-, and delay bisimilarity : [[Weak-Bisimulation-and-Internal-Activity|Link]]

7. **Testing and Trace-Based Behavioural Equivalences** : [[Testing-and-Trace-Based-Behavioural-Equivalences|Link]]
   - The testing scenario and observable outcomes : [[Testing-and-Trace-Based-Behavioural-Equivalences|Link]]
   - Bisimilarity as a testing equivalence : [[Testing-and-Trace-Based-Behavioural-Equivalences|Link]]
   - May, must, and testing preorders and equivalences : [[Testing-and-Trace-Based-Behavioural-Equivalences|Link]]
   - Complete trace equivalence : [[Alternative-Notions-of-Equality-on-Behaviour|Link1]], [[Testing-and-Trace-Based-Behavioural-Equivalences|Link2]], [[Refinements-of-Simulation|Link3]]
   - Failure equivalence : [[Testing-and-Trace-Based-Behavioural-Equivalences|Link]]
   - Ready equivalence : [[Testing-and-Trace-Based-Behavioural-Equivalences|Link]]
   - Equivalences induced by SOS rule formats
   - Non-interleaving equivalences : [[Testing-and-Trace-Based-Behavioural-Equivalences|Link]]
   - The variety of behavioural equivalences in concurrency theory : [[Testing-and-Trace-Based-Behavioural-Equivalences|Link]]

8. **Refinements of Simulation** : [[Refinements-of-Simulation|Link]]
   - Complete simulation : [[Refinements-of-Simulation|Link]]
   - Ready simulation : [[Refinements-of-Simulation|Link]]
   - Two-nested simulation equivalence : [[Refinements-of-Simulation|Link]]
   - Weak simulation variants : [[Refinements-of-Simulation|Link]]
   - Coupled simulation : [[Refinements-of-Simulation|Link]]
   - The linear-time/branching-time equivalence spectrum

9. **Barbed Bisimilarity and Congruence** : [[Barbed-Bisimilarity-and-Congruence|Link]]
   - Limits of ad hoc labelled bisimilarity on new interaction models
   - Late versus early bisimilarity in value-passing calculi : [[Barbed-Bisimilarity-and-Congruence|Link]]
   - Higher-order process languages : [[Barbed-Bisimilarity-and-Congruence|Link]]
   - Reduction bisimilarity and reduction congruence : [[Barbed-Bisimilarity-and-Congruence|Link1]], [[CCS-and-Algebraic-Properties-of-Bisimilarity|Link2]]
   - Always-divergent processes
   - Observability predicates (barbs)
   - Barbed bisimilarity and barbed congruence : [[Barbed-Bisimilarity-and-Congruence|Link]]
   - Characterisation of barbed congruence via labelled bisimilarity
   - The Context Lemma for barbed congruence : [[Barbed-Bisimilarity-and-Congruence|Link]]
   - Weak barbed relations : [[Barbed-Bisimilarity-and-Congruence|Link]]
   - Reduction-closed barbed congruence : [[Barbed-Bisimilarity-and-Congruence|Link]]

---

## Chapter Summaries

### General Introduction (pp. 1–10)

**Summary:** Motivates coinduction as the dual of induction, surveys its applications across computer science, mathematics, and philosophy, and lays out the book's objectives, structure, and the basic set-theoretic and relational notation used throughout.

**Key Definitions & Concepts:**
- **Extensional equality** — an equality identifying elements exactly when no observation distinguishes them.
- **Relation properties** — reflexive, symmetric, transitive, well-founded/non-well-founded, and the standard order/preorder/equivalence classifications.
- **Ordinal numbers** — used for transfinite iterative constructions of fixed points later in the book.

**Key Questions:**
1. Why does induction stratify constructions while coinduction allows circularity, and how does this connect to least versus greatest fixed points?
2. In what sense is coinduction "the dual" of induction, and why was its discovery in computer science comparatively late?

---

### Chapter 1: Towards Bisimulation (pp. 11–27)

**Summary:** Argues that concurrent programs cannot be adequately modeled as input/output functions because such a semantics is not compositional, then develops labelled transition systems as the right model of process behaviour, and shows why graph isomorphism and trace equivalence both fail as behavioural equalities before introducing bisimulation as the solution. : [[Bisimulation-and-Bisimilarity|Link1]], [[Refinements-of-Simulation|Link2]]

**Key Definitions & Concepts by Section:**
- **1.1 From functions to processes** — non-compositionality of the programs-as-functions view under parallel composition; a semantics not preserved by context is not a congruence. : [[Processes-and-Labelled-Transition-Systems|Link]]
- **1.2 Interaction and behaviour** — labelled transition system (LTS) as a triple $(Pr, Act, \rightarrow)$; derivative, multi-step derivative; image-finite, finitely branching, finite-state, finite, deterministic LTSs; sort of a process. : [[Alternative-Notions-of-Equality-on-Behaviour|Link1]], [[Processes-and-Labelled-Transition-Systems|Link2]]
- **1.3 Equality of behaviours** — graph isomorphism (too fine-grained a distinction is avoided but too coarse an identification results); trace equivalence (fails to respect deadlock). : [[Alternative-Notions-of-Equality-on-Behaviour|Link]]
- **1.4 Bisimulation** — bisimulation as a process relation satisfying the matching-transition clauses; bisimilarity $\sim$ as the union of all bisimulations; the bisimulation proof method; $\sim$ is an equivalence relation and is itself the largest bisimulation (impredicative definition); similarity (Exercise 1.4.17); bisimulation up-to $\sim$ (Exercise 1.4.18). : [[Bisimulation-and-Bisimilarity|Link]]

**Key Questions:**
1. Why is the interpretation of concurrent programs as functions unsatisfactory, and how does this failure motivate representing processes via labelled transition systems?
2. What precisely distinguishes bisimilarity from trace equivalence, and why does the vending-machine example show trace equivalence is too coarse for concurrency?
3. Why is the definition of bisimilarity "impredicative," and what proof technique does this style of definition suggest?

---

### Chapter 2: Coinduction and the Duality with Induction (pp. 28–88)

**Summary:** The theoretical core of the book: develops fixed-point theory on complete lattices to give a rigorous, unified account of induction and coinduction, derives the corresponding proof principles, applies them to rule-based definitions (rule induction/coinduction), and uses the framework to re-derive bisimilarity — including its stratification via approximants and a game-theoretic characterisation. : [[Coinduction-and-the-Duality-with-Induction|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 Examples of induction and coinduction** — finite traces (inductive) versus $\omega$-traces (coinductive) on processes; convergence/divergence in the $\lambda$-calculus; finite and infinite lists. : [[Coinduction-and-the-Duality-with-Induction|Link]]
- **2.3 Fixed points in complete lattices** — poset; upper/lower bound, least/greatest element; complete lattice (all joins exist, hence all meets, plus bottom $\bot$ and top $\top$); the Fixed-point Theorem: a monotone endofunction on a complete lattice has a complete lattice of fixed points, with the least fixed point equal to the meet of pre-fixed points and the greatest equal to the join of post-fixed points. : [[Coinduction-and-the-Duality-with-Induction|Link]]
- **2.4 Inductively and coinductively defined sets** — $F_{\mathrm{ind}}$ (meet of pre-fixed points) and $F_{\mathrm{coind}}$ (join of post-fixed points); induction and coinduction proof principles as corollaries. : [[Coinduction-and-the-Duality-with-Induction|Link]]
- **2.5 Definitions by means of rules** — rule functionals as monotone endofunctions on $\wp(X)$; rule induction and rule coinduction. : [[Coinduction-and-the-Duality-with-Induction|Link]]
- **2.7 Other induction and coinduction principles** — mathematical, structural, derivation-proof, transition, and well-founded induction all cast as instances of the general fixed-point schema; recursion and corecursion. : [[Coinduction-and-the-Duality-with-Induction|Link]]
- **2.8 Constructive proofs of least/greatest fixed points** — continuity and cocontinuity of endofunctions; the Continuity/Cocontinuity Theorem; transfinite iteration over the ordinals when cocontinuity fails. : [[Coinduction-and-the-Duality-with-Induction|Link]]
- **2.9 Continuity and cocontinuity, for rules** — finite in the premises (FP) and finite in the conclusions (FC) conditions on rule sets, and their link to continuity/cocontinuity. : [[Coinduction-and-the-Duality-with-Induction|Link]]
- **2.10 Bisimilarity as a fixed point** — stratification of bisimilarity $\sim_n$, $\sim_\omega$ by approximants; on finitely-branching LTSs, $\sim = \sim_\omega$; image-finiteness up-to $\sim$; transfinite stratification $\sim_\infty = \sim$ in general. : [[Coinduction-and-the-Duality-with-Induction|Link1]], [[CCS-and-Algebraic-Properties-of-Bisimilarity|Link2]], [[Bisimulation-and-Bisimilarity|Link3]]
- **2.11 Proofs of membership** — least fixed-point membership corresponds to a well-founded proof tree; greatest fixed-point membership corresponds to a (possibly infinite) proof tree. : [[Coinduction-and-the-Duality-with-Induction|Link]]
- **2.12–2.14 Game interpretations** — the inductive game $G^{\mathrm{ind}}$ and coinductive game $G^{\mathrm{coind}}$ between a verifier V and a refuter R; winning strategies characterise least/greatest fixed-point membership; specialisation to the bisimulation game.

**Key Questions:**
1. How does the Fixed-point Theorem unify the seemingly different constructions of inductive sets (as least fixed points / smallest forward-closed sets) and coinductive sets (as greatest fixed points / largest backward-closed sets)?
2. Why does bisimilarity coincide with its approximant limit $\sim_\omega$ only under a finite-branching (or similar) hypothesis, and what does Example 2.10.11 show goes wrong without it?
3. In the game-theoretic view, why is an infinite play a win for the verifier in the coinductive game but a win for the refuter in the inductive game, and how does this connect to well-foundedness of proof trees?

---

### Chapter 3: Algebraic Properties of Bisimilarity (pp. 89–107)

**Summary:** Introduces the CCS process operators (nil, prefixing, parallel composition, choice, restriction) with their SOS inference rules, proves bisimilarity is a congruence for CCS, and gives a complete algebraic axiomatisation of strong bisimilarity on finite CCS terms. : [[CCS-and-Algebraic-Properties-of-Bisimilarity|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 Basic process operators** — names/conames/$\tau$; the five CCS operators and their SOS rules (Pre, ParL, ParR, Com, SumL, SumR, Res). : [[CCS-and-Algebraic-Properties-of-Bisimilarity|Link]]
- **3.2 CCS** — the CCS grammar; constants for infinite behaviour; finCCS (no constants, hence only finite processes).
- **3.4 Some algebraic laws** — head standard form; the Expansion Lemma, rewriting a parallel composition of head-standard-form processes into head standard form.
- **3.5 Compositionality properties** — congruence: bisimilarity is preserved by every CCS context (Congruence Theorem); the De Simone format as a general sufficient condition for congruence of bisimilarity.
- **3.6 Algebraic characterisation** — the axiom system $SB$ (summation, restriction, and Expansion laws); $P \sim Q$ iff $SB \vdash P = Q$ on finCCS; full standard form; non-finite-axiomatisability without auxiliary operators (Moller's result) and prime process decompositions. : [[Coinduction-and-the-Duality-with-Induction|Link]]

**Key Questions:**
1. Why does the Expansion Lemma let us eliminate parallel composition in favor of a sum of prefixed alternatives, and what are the two sources of summands it produces?
2. What makes the proof of the Congruence Theorem require both an inductive argument (on context structure) and a coinductive one (on bisimilarity), and how does the De Simone format generalise this result to other operators?
3. Why is the axiom system $SB$ not finitely axiomatisable as stated, and what auxiliary construct restores finite axiomatisability?

---

### Chapter 4: Processes with Internal Activities (pp. 108–132)

**Summary:** Refines bisimilarity to abstract from internal ($\tau$) computation, developing weak bisimilarity and diagnosing its failure to be a congruence for choice; introduces rooted weak bisimilarity to repair this, discusses divergence-sensitivity, and surveys several further variants (dynamic, branching, $\eta$-, delay bisimilarity) that respect branching structure more closely. : [[Weak-Bisimulation-and-Internal-Activity|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Weak LTSs and weak transitions** — weak transition relations $\Rightarrow$ (silent closure) and $\stackrel{\mu}{\Rightarrow}$ (visible action padded by silent moves); image-finiteness under weak transitions. : [[Testing-and-Trace-Based-Behavioural-Equivalences|Link1]], [[Weak-Bisimulation-and-Internal-Activity|Link2]]
- **4.2 Weak bisimulation** — weak bisimilarity $\approx$, matching weak transitions instead of single steps; equivalence relation properties. : [[Weak-Bisimulation-and-Internal-Activity|Link]]
- **4.3 Divergence** — divergence predicate $\Uparrow$ as the largest set closed under performing a further $\tau$; weak bisimilarity's insensitivity to $\tau$-cycles ("fair abstraction from divergence"). : [[Testing-and-Trace-Based-Behavioural-Equivalences|Link]]
- **4.4 Rooted weak bisimilarity** — weak bisimilarity fails to be preserved by choice (e.g. $\tau.a \approx a$ but $\tau.a + b \not\approx a + b$); rooted weak bisimilarity $\approx^c$ requiring the first step to be a genuine (non-silent-collapsed) match; characterisation via all contexts. : [[Barbed-Bisimilarity-and-Congruence|Link]]
- **4.5 Axiomatisation** — algebraic characterisation of rooted weak bisimilarity on finCCS via axiom system $WB$. : [[Weak-Bisimulation-and-Internal-Activity|Link]]
- **4.6–4.9 Variants** — removing the challenge on $\tau$-moves ($\approx_\tau$-bisimulation); prebisimilarity with divergence (divergence-sensitive); dynamic bisimilarity (answering with $\stackrel{\tau}{\Rightarrow}$ rather than $\Rightarrow$); branching, $\eta$-, and delay bisimilarity, which more finely respect the branching structure around silent moves.

**Key Questions:**
1. Why must weak bisimilarity abstract from $\tau$-cycles under a "fair abstraction" reading, and what practical justification (e.g., busy-waiting, lossy media) supports this choice?
2. Concretely, why is weak bisimilarity not preserved by the choice operator, and how does the rooted variant repair congruence while still abstracting internal steps everywhere else?
3. What is the difference between weak, dynamic, and branching bisimilarity in terms of what each requires of the matching silent transitions, and why do they form a strict hierarchy?

---

### Chapter 5: Other Approaches to Behavioural Equivalences (pp. 133–167)

**Summary:** Recasts bisimilarity as a testing equivalence relative to a suitably rich language of tests, then explores what happens as the observational power of the tester is weakened — yielding the may/must/testing preorders, and, via complete traces and refusal sets, failure and ready equivalence — comparing all of these systematically with bisimilarity and with each other across classes of SOS operator formats. : [[Testing-and-Trace-Based-Behavioural-Equivalences|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 A testing scenario** — a run of a test $T$ on process $P$; operational outcomes $O^{op}(T,P) \subseteq \{\checkmark, \bot\}$; denotational versus operational definition of outcomes. : [[Testing-and-Trace-Based-Behavioural-Equivalences|Link]]
- **5.2 Bisimulation via testing** — characterisation of strong bisimilarity as a testing equivalence with a sufficiently rich test language. : [[Bisimulation-and-Bisimilarity|Link]]
- **5.5 Testing preorders** — may pass / must pass a test; the $\leq_{\mathrm{may}}$ and $\leq_{\mathrm{must}}$ preorders and their induced equivalences $\simeq_{\mathrm{may}}$, $\simeq_{\mathrm{must}}$, $\simeq_{\mathrm{test}}$. : [[Testing-and-Trace-Based-Behavioural-Equivalences|Link]]
- **5.7 Characterisations of may, must, testing** — trace-based characterisation: $\leq_{\mathrm{may}}$ is trace inclusion; $\leq_{\mathrm{must}}$ via a "must $A$" refusal-style condition on traces; $\simeq_{\mathrm{must}}$ coincides with $\simeq_{\mathrm{test}}$. : [[Testing-and-Trace-Based-Behavioural-Equivalences|Link]]
- **5.10 Failure equivalence** — complete traces (maximal action sequences); a failure as a pair (trace, refused action set); failure equivalence coincides with testing equivalence on strong LTSs. : [[Testing-and-Trace-Based-Behavioural-Equivalences|Link]]
- **5.11 Ready equivalence** — ready set of a process; ready pairs; ready equivalence implies (strictly) failure equivalence. : [[Testing-and-Trace-Based-Behavioural-Equivalences|Link]]
- **5.12 Equivalences induced by SOS formats** — De Simone, GSOS, tyft/tyxt, ntyft/ntyxt formats; richer operator classes induce finer congruences, up to bisimilarity itself.
- **5.14 Varieties in concurrency** — synthesis comparing all equivalences discussed, discussing when to prefer bisimilarity versus a coarser equivalence, and situating the chapter's results in the wider "equivalence spectrum" literature (van Glabbeek). : [[CCS-and-Algebraic-Properties-of-Bisimilarity|Link]]

**Key Questions:**
1. How does making the observer's testing power progressively weaker generate the spectrum from bisimilarity down through testing, failure, and ready equivalence to plain trace equivalence?
2. Why does complete trace equivalence fail to be compositional, and how does adding refusal sets (failure equivalence) restore a well-behaved, deadlock-sensitive notion?
3. What general principle explains why enlarging the class of admissible SOS operator formats (De Simone → GSOS → tyft/tyxt) makes the induced congruence finer, potentially collapsing to bisimilarity?

---

### Chapter 6: Refinements of Simulation (pp. 168–181)

**Summary:** Explores simulation-based alternatives to bisimilarity that retain a coinductive flavour and yield a genuine preorder, while repairing similarity's insensitivity to deadlock — culminating in ready simulation and coupled simulation, and closing with a diagram summarising the full equivalence spectrum developed across the book. : [[Refinements-of-Simulation|Link]]

**Key Definitions & Concepts by Section:**
- **6.1 Complete simulation** — a simulation additionally requiring that stopped processes are matched by stopped processes; complete similarity $\leq_{\mathrm{comp}}$. : [[Refinements-of-Simulation|Link]]
- **6.2 Ready simulation** — a simulation additionally requiring equal ready sets at every related pair; identified by Bloom–Istrail–Meyer as the finest congruence induced by complete traces over GSOS-definable operators. : [[Refinements-of-Simulation|Link]]
- **6.3 Two-nested simulation equivalence** — simulation equivalence strengthened by a second layer of simulation requirement. : [[Refinements-of-Simulation|Link]]
- **6.5 Coupled simulation** — a pair of simulations $(R_1, R_2)$ linked by a "coupling" condition forcing weak ties between the two directions; rooted coupled simulation equivalence for a congruence over CCS. : [[Refinements-of-Simulation|Link]]
- **6.6 The equivalence spectrum** — summary diagram (Figure 6.2) ordering all equivalences from the book by relative fineness. : [[Alternative-Notions-of-Equality-on-Behaviour|Link1]], [[Refinements-of-Simulation|Link2]]

**Key Questions:**
1. Why is ordinary simulation equivalence unsuitable as a behavioural equality (what deadlock-related problem does it inherit from trace equivalence), and how do complete and ready simulation repair this while remaining coarser than bisimilarity?
2. What is the "coupling" condition in coupled simulation meant to guarantee, and why is a single simulation relation not enough to capture it?
3. Looking at the full equivalence spectrum, what tradeoffs (discriminating power vs. algorithmic efficiency vs. robustness to context) explain why bisimilarity remains the default choice despite being the finest equivalence considered?

---

### Chapter 7: Basic Observables (pp. 182–198)

**Summary:** Develops a general, language-independent method for deriving a satisfactory bisimilarity — barbed bisimilarity and barbed congruence — for essentially any process language given only a reduction relation and a notion of observable action (a "barb"), and shows this contextual definition coincides with ordinary labelled bisimilarity on CCS.

**Key Definitions & Concepts by Section:**
- **7.1 Labelled bisimilarities: examples of problems** — late versus early bisimilarity in value-passing CCS; difficulties defining bisimulation directly in higher-order process languages.
- **7.2 Reduction congruence** — reduction bisimulation (bisimulation played only on $\tau$-transitions); reduction congruence as its context closure; always-divergent processes are reduction congruent but not necessarily bisimilar — showing reduction congruence alone is too coarse. : [[Barbed-Bisimilarity-and-Congruence|Link]]
- **7.3 Barbed congruence** — observability predicate / barb $\downarrow_\ell$; barb-preserving relation; barbed bisimilarity $\dot\sim$ (reduction bisimulation plus barb preservation); barbed congruence $\simeq$ as the context closure of barbed bisimilarity; Characterisation Theorem: on image-finite CCS processes, barbed congruence coincides with ordinary labelled bisimilarity. : [[Barbed-Bisimilarity-and-Congruence|Link]]
- **7.4 Barbed equivalence** — a Context Lemma reducing the quantification over all contexts needed to establish barbed congruence. : [[Bisimulation-and-Bisimilarity|Link]]
- **7.5–7.6 Weak variants** — weak barbed bisimilarity/congruence (characterising weak bisimilarity); reduction-closed barbed congruence, which folds context-closure directly into the bisimulation clause and again coincides with strong bisimilarity.

**Key Questions:**
1. Why is reduction congruence, despite being contextual, still too coarse a behavioural equality, and what specific extra ingredient (barbs) does barbed bisimilarity add to fix this?
2. What does the Characterisation Theorem for barbed congruence buy us in practice, given that barbed congruence's definition via universal quantification over contexts is hard to work with directly?
3. Why do information-hiding features (polymorphic types, encryption, abstract data types) tend to make the labelled bisimilarity that characterises barbed congruence diverge from the naive syntactic matching of Definition 1.4.2?

---
