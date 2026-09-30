# Pushdown Automata and Inclusion Problems — Guidelines

## Header

**Title:** Pushdown Automata and Inclusion Problems
**Author(s):** Nguyen Van Tang (supervised by Professor Mizuhito Ogawa)
**Publication:** PhD dissertation, Japan Advanced Institute of Science and Technology (JAIST), School of Information Science, March 2009

**Brief Summary:**
This dissertation studies the language inclusion problem $L(A) \subseteq L(B)$ for subclasses of pushdown automata (PDAs), motivated by the automata-theoretic approach to model checking, where checking that a system satisfies a specification reduces to checking language inclusion between the automata that model them. Because general PDAs are not closed under intersection or complementation and the general inclusion problem is undecidable, the thesis studies restricted subclasses — superdeterministic PDAs (SPDAs) and visibly pushdown automata (VPAs) — for which inclusion is decidable, and contributes: a simplified product construction for the PDA-vs-SPDA inclusion decision procedure; counterexamples refuting claimed determinizability results for two proposed VPA extensions; practical antichain-based and on-the-fly algorithms (with a working implementation) for VPA universality and inclusion checking; and a new automaton class, event-clock visibly pushdown automata (ECVPAs), for which the inclusion problem against timed visibly pushdown automata (TVPAs) is decidable.

**Intent of the Author:**
The author aims to push the boundary of decidable language-inclusion problems for pushdown-based models, refining existing proofs to be more direct and implementable, and delivering algorithms with actual prototype implementations and experimental validation rather than purely theoretical decidability results — with an eye toward practical applications in pushdown model checking and XML stream validation.

---

## Topic List

1. **Pushdown Automata Foundations** : [[Pushdown-Automata-Foundations|Link]]
   - Pushdown automata as finite automata with a stack : [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link]]
   - Configurations, computations, and stacking computations : [[Pushdown-Automata-Foundations|Link]]
   - Real-time and deterministic PDAs : [[Pushdown-Automata-Foundations|Link]]
   - Normalized pushdown automata : [[Visibly-Pushdown-Automata|Link1]], [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link2]], [[Pushdown-Automata-Foundations|Link3]], [[Superdeterministic-Pushdown-Automata|Link4]]
   - Closure properties and undecidability of PDA inclusion : [[Visibly-Pushdown-Automata|Link]]
   - Emptiness checking via P-automata and post* reachability : [[Pushdown-Automata-Foundations|Link]]

2. **Model Checking via the Automata-Theoretic Approach** : [[Model-Checking-via-the-Automata-Theoretic-Approach|Link]]
   - Model checking as an automated verification technique : [[Model-Checking-via-the-Automata-Theoretic-Approach|Link]]
   - The automata-theoretic reduction of model checking to language inclusion : [[Model-Checking-via-the-Automata-Theoretic-Approach|Link]]
   - Pushdown model checking for regular properties : [[Pushdown-Automata-Foundations|Link]]
   - Pushdown model checking for context-free properties : [[Pushdown-Automata-Foundations|Link]]
   - CaRet as a temporal logic for non-regular properties

3. **Superdeterministic Pushdown Automata** : [[Superdeterministic-Pushdown-Automata|Link]]
   - Superdeterministic pushdown automata as finite-delay deterministic PDAs : [[Superdeterministic-Pushdown-Automata|Link]]
   - Superdeterministic languages and generalized parenthesis languages
   - Decidability of the PDA-vs-SPDA inclusion problem : [[Timed-Automata-and-Their-Pushdown-Extensions|Link]]
   - The alternate stacking technique : [[Superdeterministic-Pushdown-Automata|Link]]
   - The Key Lemma bounding stack-length divergence : [[Superdeterministic-Pushdown-Automata|Link]]
   - Product construction of a simulating pushdown automaton : [[Superdeterministic-Pushdown-Automata|Link1]], [[Visibly-Pushdown-Automata|Link2]], [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link3]]
   - Soundness and completeness of the simulating construction : [[Superdeterministic-Pushdown-Automata|Link]]
   - Double-exponential time complexity of the decision procedure : [[Antichain-Based-Decision-Procedures|Link]]

4. **Visibly Pushdown Automata** : [[Visibly-Pushdown-Automata|Link]]
   - Visibly pushdown automata as input-driven stack automata : [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link1]], [[Visibly-Pushdown-Automata|Link2]]
   - Partition of the alphabet into call, return, and internal symbols
   - Well-matched, call-matched, and return-matched words : [[Visibly-Pushdown-Automata|Link]]
   - Congruence-based characterization of visibly pushdown languages
   - Determinization of visibly pushdown automata : [[Visibly-Pushdown-Automata|Link1]], [[Superdeterministic-Pushdown-Automata|Link2]], [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link3]], [[Timed-Automata-and-Their-Pushdown-Extensions|Link4]]
   - Closure under union, intersection, and complementation
   - EXPTIME-completeness of universality and inclusion for VPAs
   - Height-determinism and synchronization of pushdown automata : [[Superdeterministic-Pushdown-Automata|Link]]

5. **Extensions of Visibly Pushdown Automata and Their Limits** : [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link]]
   - Multi-stack visibly pushdown automata : [[Visibly-Pushdown-Automata|Link1]], [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link2]]
   - Ordered n-visibly pushdown automata : [[Visibly-Pushdown-Automata|Link]]
   - 2-visibly pushdown automata and synchronized communication symbols : [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link1]], [[Timed-Automata-and-Their-Pushdown-Extensions|Link2]], [[Pushdown-Automata-Foundations|Link3]], [[Visibly-Pushdown-Automata|Link4]]
   - Undecidability of emptiness for unrestricted 2-VPAs
   - Counterexample refuting determinizability of 2-OVPAs : [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link]]
   - Visibly stack automata as an extension combining visibility and stack automata : [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link]]
   - Counterexample refuting determinizability of visibly stack automata : [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link]]
   - Non-closure under complementation of non-determinizable extensions

6. **Antichain-Based Decision Procedures** : [[Antichain-Based-Decision-Procedures|Link]]
   - Antichains as sets of pairwise incomparable elements
   - The lattice of antichains and monotone Post functions
   - Implicit determinization via least fixed points : [[Visibly-Pushdown-Automata|Link]]
   - Forward antichain algorithm for universality of finite automata : [[Antichain-Based-Decision-Procedures|Link]]
   - Antichain algorithm for inclusion of finite automata : [[Antichain-Based-Decision-Procedures|Link]]
   - On-the-fly simultaneous determinization and reachability checking : [[Antichain-Based-Decision-Procedures|Link]]
   - Ordering over determinized VPA states and stack symbols
   - Minimal configurations and the antichain-based VPA algorithm
   - Experimental comparison of standard, on-the-fly, and antichain-based methods

7. **Timed Automata and Their Pushdown Extensions** : [[Timed-Automata-and-Their-Pushdown-Extensions|Link]]
   - Timed automata and clock constraints : [[Timed-Automata-and-Their-Pushdown-Extensions|Link]]
   - Undecidability of general timed automata inclusion
   - Event-clock automata and event-recording/event-predicting clocks : [[Timed-Automata-and-Their-Pushdown-Extensions|Link]]
   - Timed pushdown automata : [[Timed-Automata-and-Their-Pushdown-Extensions|Link]]
   - Timed visibly pushdown automata : [[Visibly-Pushdown-Automata|Link]]
   - Undecidability of TVPA inclusion : [[Timed-Automata-and-Their-Pushdown-Extensions|Link]]
   - Event-clock visibly pushdown automata : [[Timed-Automata-and-Their-Pushdown-Extensions|Link]]
   - Untimed and timed translations between ECVPA and VPA
   - Decidability of the TVPA-vs-ECVPA inclusion problem : [[Timed-Automata-and-Their-Pushdown-Extensions|Link]]
   - Duration automata as a subclass of ECVPAs : [[Timed-Automata-and-Their-Pushdown-Extensions|Link]]

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 1–10)

**Summary:** Motivates the thesis via model checking and the automata-theoretic approach of Vardi and Wolper, which reduces verification to the language inclusion problem $L(A) \subseteq L(B)$; surveys why this fails for general pushdown automata against non-regular specifications and previews the thesis's four main contributions across superdeterministic PDAs, visibly pushdown automata extensions, antichain algorithms, and timed extensions.

**Key Definitions & Concepts by Section:**
- **1.1 Model Checking** — model checking (automatic verification against a temporal-logic specification), Kripke structures, CTL, LTL, SMV/NuSMV and SPIN as example tools. : [[Model-Checking-via-the-Automata-Theoretic-Approach|Link1]], [[Pushdown-Automata-Foundations|Link2]]
- **1.2 Inclusion Problems and Model Checking** — automata-theoretic approach ($P \models \varphi \iff L(P^a) \subseteq L(A_\varphi) \iff L(P^a) \cap L(A_{\neg\varphi}) = \emptyset$), pushdown model checking for regular vs. context-free properties, CaRet logic, motivation for visibly pushdown automata. : [[Pushdown-Automata-Foundations|Link]]
- **1.3 Contributions** — overview of Chapters 2–6: P-automata (Ch. 2), refined alternate-stacking proof for SPDA inclusion (Ch. 3), counterexamples on VPA-extension determinizability (Ch. 4), antichain/on-the-fly algorithms (Ch. 5), event-clock visibly pushdown automata (Ch. 6).

**Key Questions:**
1. Why does the automata-theoretic complement-and-intersect method for checking $L(A) \subseteq L(B)$ work when $A$ is extended to a PDA but fail when $B$ is?
2. What decidability property does the automata-theoretic approach to model checking crucially rely on, and why is it preserved for regular but not context-free specifications?

---

### Chapter 2: Pushdown Automata (pp. 11–17)

**Summary:** Establishes the formal definitions, normal forms, and basic decidability results for pushdown automata that the rest of the thesis builds on, including the P-automata technique for computing reachable configurations. : [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link1]], [[Pushdown-Automata-Foundations|Link2]], [[Superdeterministic-Pushdown-Automata|Link3]], [[Timed-Automata-and-Their-Pushdown-Extensions|Link4]]

**Key Definitions & Concepts by Section:**
- **2.1 Definition of Pushdown Automata** — PDA as a tuple $(Q, \Sigma, \Gamma, Z_0, \Delta, q_0, F)$; push/internal/pop rules; blocking and reading modes; real-time PDA (RPDA) and deterministic PDA (DPDA); configurations, stacking computations ($c_1 \uparrow (w) c_2$); accessible and live configurations; finite delay; acceptance by final state and empty stack. : [[Superdeterministic-Pushdown-Automata|Link1]], [[Visibly-Pushdown-Automata|Link2]]
- **2.2 Properties of Pushdown Automata** — emptiness decidable in polynomial time; PDA closed under union but not intersection/complementation; PDA inclusion undecidable in general but decidable against a finite automaton specification; normalized PDA form (every mode either purely $\varepsilon$ or purely on $\Sigma$, and never blocking). : [[Visibly-Pushdown-Automata|Link1]], [[Superdeterministic-Pushdown-Automata|Link2]], [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link3]], [[Pushdown-Automata-Foundations|Link4]]
- **2.3 Deciding Emptiness of PDAs** — P-automaton (a finite automaton over stack alphabet $\Gamma$ encoding infinite sets of PDA configurations); the $\text{post}^*$ saturation procedure computing reachable configurations; Moped as an implementation.
- **2.4 Applications to Pushdown Model Checking** — pushdown models abstracting recursive procedure calls; DEXPTIME-completeness of pushdown CTL model checking vs. polynomial LTL model checking. : [[Pushdown-Automata-Foundations|Link]]

**Key Questions:**
1. How does a P-automaton represent an infinite set of pushdown configurations, and how does the saturation procedure compute $\text{post}^*(C)$?
2. Why is normalizing a PDA (Definition 2.9) a useful preprocessing step for later constructions in the thesis?

---

### Chapter 3: Superdeterministic Pushdown Automata (pp. 18–31)

**Summary:** Refines Greibach and Friedman's alternate stacking technique for deciding $L(A) \subseteq L(B)$ where $A$ is a PDA and $B$ is a superdeterministic PDA (SPDA), replacing the original stack-symbol encoding with a direct product construction of a simulating PDA that eliminates the need for a separate "liveness" side-condition and yields a simpler soundness/completeness proof. : [[Superdeterministic-Pushdown-Automata|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 Superdeterministic Pushdown Automata** — SPDA as a finite-delay DPDA where same-state, same-symbol transitions preserve control-state equality and relative stack-length change; superdeterministic language; decidability of "is this PDA an SPDA?" vs. undecidability of "is this CFL superdeterministic?"; the Key Lemma (Lemma 3.1) bounding $|c_1'| - |c_2'|$ by a computable constant $k$. : [[Superdeterministic-Pushdown-Automata|Link]]
- **3.2 Alternate Stacking Technique** — Valiant's alternate stacking (interweaving two PDAs' stacks in a single machine $M$); the simulating PDA $M(A,B,r)$ built as a direct product of states/stack-content/transitions of $A$ and $B$ (Definition 3.3), parameterized by a segment bound $r$; stacking-fail transitions; six transition-rule cases (internal, push, pop, empty-$A$-stack, $\varepsilon$-simulation, $B$-blocked). : [[Superdeterministic-Pushdown-Automata|Link]]
- **3.3 Soundness and Completeness** — Lemma 3.2 (soundness: $L(A) \not\subseteq L(B) \Rightarrow L(M) \neq \emptyset$), Lemma 3.3 (completeness, via contradiction against the Key Lemma when $r = k+1$), Lemma 3.4 ($L(A) \subseteq L(B) \iff L(M(A,B,k+1)) = \emptyset$), Theorem 3.5 (decidability with $2^{2^{p(h)}}$ time complexity). : [[Superdeterministic-Pushdown-Automata|Link]]
- **3.4 Related Work** — DPDA equivalence decidability (Sénizergues 1997, Stirling); acceptance condition sensitivity of SPDA inclusion (undecidable by final state alone, decidable by final state + empty stack); comparison to XML/regular hedge grammar inclusion algorithms of Minamide and Tozawa.

**Key Questions:**
1. What role does the "liveness" condition play in the original Greibach–Friedman proof, and how does the product construction of $M$ in this thesis eliminate the need for it?
2. Why must the segment bound $r$ be set to exactly $k+1$ (from the Key Lemma) for the simulating PDA construction to be both sound and complete?

---

### Chapter 4: Visibly Pushdown Automata and Its Extensions (pp. 32–44)

**Summary:** Recalls the definition and good closure/decidability properties of visibly pushdown automata (VPAs), then shows via detailed counterexamples that two proposed extensions — 2-visibly pushdown automata (2-VPAs/2-OVPAs) and the newly introduced visibly stack automata (VSAs) — are not determinizable, contrary to a prior published claim for 2-OVPAs. : [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Visibly Pushdown Automata** — VPA as $(Q, Q_0, \Gamma, \Delta, F)$ over a partitioned alphabet $\Sigma = \Sigma_c \cup \Sigma_r \cup \Sigma_i$ (call/return/internal); push/pop/internal transitions insensitive to top-of-stack (for calls) or defined even on empty stack (for returns); well-matched, call-matched, return-matched words; congruence-based determinizability criterion (Theorem 4.2); the congruence-based determinization construction $M^d$ (Definition 4.5) with double-exponential state/alphabet blowup; closure under union, intersection, and complementation (Theorem 4.5); EXPTIME-completeness of universality and inclusion (Theorem 4.6). : [[Visibly-Pushdown-Automata|Link]]
- **4.2 Language Extensions of VPA Are Difficult** — 2-pushdown alphabets and synchronized communication symbols; 2-VPA transition relation (push/2push/pop/2pop/internal/sync); ordered 2-VPA (2-OVPA, restricting pops on the second stack); Counter-example 1 refuting 2-OVPA/2-VPA determinizability (interleaving actions across two stacks break summary-edge reachability); visibly stack automaton (VSA, combining visibility with a head that moves up/down a stack); Counter-example 2 refuting VSA determinizability.
- **4.3 Related Work** — height-deterministic PDAs and synchronization (Nowotka and Srba); Caucal's Boolean-algebra extension of VPLs via transducer synchronization; open conjecture that inclusion for 2-OVPAs/VSAs is undecidable.

**Key Questions:**
1. What property of VPAs (visibility: stack action fixed by the input symbol) is essential for the congruence-based determinization to work, and why does interleaving two stacks in a 2-VPA break the analogous construction?
2. In Counter-example 1, why does reaching "the same configuration" on two different prefixes force a determinized 2-OVPA into a contradiction when a suffix is appended?

---

### Chapter 5: Checking Universality and Inclusion of Visibly Pushdown Automata (pp. 45–66)

**Summary:** Develops and experimentally validates practical algorithms for the EXPTIME-complete universality and inclusion problems for VPAs, progressing from a standard explicit-determinization approach (too slow in practice) to an on-the-fly method and finally an antichain-based method that keeps determinization implicit and only tracks minimal configurations. : [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link1]], [[Visibly-Pushdown-Automata|Link2]]

**Key Definitions & Concepts by Section:**
- **5.1 Checking Universality and Inclusion of Finite Automata** — subset construction; antichain (a set of pairwise $\subseteq$-incomparable subsets); the lattice of antichains $(L, \sqsubseteq, \sqcup, \sqcap)$; the monotone $\text{Post}$ function and $\text{Post}^i$ approximants; Tarski's fixed-point theorem giving $\text{Post}^*$; Theorem 5.4 (an NFA is not universal iff some $s \in \text{Post}^*(p_0)$ is disjoint from $F$); the forward antichain algorithm; richer antichain lattice over $Q_A \times 2^{Q_B}$ for inclusion checking (Theorem 5.5).
- **5.2 Checking Universality and Inclusion of Visibly Pushdown Automata** — standard method (determinize then check reachability via P-automata, Fig. 5.4); on-the-fly method interleaving determinization and P-automaton construction (Theorem 5.6, Algorithm 2); antichain-based method: an ordering over determinized VPA states/stack symbols/configurations (Definitions 5.7–5.8), the Key Lemma (Lemma 5.10) showing the ordering is preserved by runs, and the Main Theorem (5.11) that only minimal non-accepting configurations need be tracked (Algorithm 3). : [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link1]], [[Visibly-Pushdown-Automata|Link2]]
- **5.3 Implementation and Experiments** — prototype in Java/NetBeans; randomly generated VPAs; comparison of STANDARD, ON-THE-FLY, and ANTICHAIN on universality (Tables 5.1–5.3) and inclusion (Table 5.4) checking; STANDARD times out almost universally; ANTICHAIN generally outperforms ON-THE-FLY, especially for universal VPAs.
- **5.4 Related Work** — antichains for tree automata (Bouajjani et al.) and Büchi automata (ALASKA tool); comparison to the VPAlib implementation, which lacks on-the-fly determinization.

**Key Questions:**
1. Why does keeping only *minimal* configurations (per the ordering of Definition 5.8) suffice for correctly deciding universality, instead of tracking all reachable configurations?
2. Why is the antichain approach for infinite-state VPAs (Section 5.2) structurally different from the finite-lattice antichain approach for finite automata (Section 5.1), and what workaround (P-automata) makes it feasible?

---

### Chapter 6: Timed Extensions of Visibly Pushdown Automata (pp. 67–80)

**Summary:** Introduces event-clock visibly pushdown automata (ECVPAs) as a determinizable, Boolean-closed timed extension of VPAs modeled on event-clock automata, proves a translation between ECVPAs and untimed VPAs that transfers VPA decidability results, and uses this translation to show that the inclusion problem $L(A) \subseteq L(B)$ is decidable when $A$ is a timed visibly pushdown automaton (TVPA) and $B$ is an ECVPA — despite general TVPA inclusion being undecidable. : [[Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Link1]], [[Timed-Automata-and-Their-Pushdown-Extensions|Link2]], [[Visibly-Pushdown-Automata|Link3]]

**Key Definitions & Concepts by Section:**
- **6.1 Event-Clock Visibly Pushdown Automata** — timed words and timed languages; event-recording clock $x_a$ and event-predicting clock $y_a$; event-clock constraints $\Phi(C_\Sigma)$; ECVPA as $(Q, \Sigma, Q_0, \Gamma, \Delta, F)$ with clock-guarded push/pop/internal transitions; deterministic ECVPA (Definition 6.6); duration automata (DAs) as a subclass of ECAs, hence of ECVPAs. : [[Timed-Automata-and-Their-Pushdown-Extensions|Link]]
- **6.2 Properties of Event-Clock Visibly Pushdown Automata** — interval-based alphabet $\Pi$ encoding clock guards discretely; untimed transformation $ut(M)$ turning an ECVPA into a VPA (Lemma 6.1: $tw(L(ut(M))) = L(M)$); timed transformation $ec(N)$ turning a VPA back into an ECVPA (Lemma 6.2); round-trip Theorem 6.3 ($L(ec(ut(M))) = L(M)$); resulting closure under Boolean operations (Theorem 6.5) and EXPTIME-completeness of ECVPA inclusion (Theorem 6.6). : [[Timed-Automata-and-Their-Pushdown-Extensions|Link]]
- **6.3 Related Classes of Timed Pushdown Automata** — timed visibly pushdown automaton (TVPA) with explicit clocks $X$ and reset sets $\lambda$ on transitions; non-determinizability of TVPAs; undecidability of TVPA-vs-TVPA inclusion even with one clock (Theorem 6.7, Emmi–Majumdar); translation of event clocks to original clocks (turning an ECA into a timed automaton); Lemma 6.8 (every ECVPA translates to an equivalent TVPA); Theorem 6.9 (TVPA-vs-ECVPA inclusion is decidable, via determinize-complement-translate-intersect-check-emptiness). : [[Superdeterministic-Pushdown-Automata|Link1]], [[Visibly-Pushdown-Automata|Link2]], [[Timed-Automata-and-Their-Pushdown-Extensions|Link3]]
- **6.4 Related Work** — Ouaknine–Worrell's one-clock timed automata inclusion decidability via well-structured transition systems; undecidability over infinite timed words even with one clock; EventClockTL and DSouza's MSO characterization of event-clock automata.

**Key Questions:**
1. Why is it essential that ECVPA clock valuations depend only on the input timed word (not on transition choices), in contrast to TVPA clocks, for ECVPAs to be determinizable and Boolean-closed?
2. How does the untimed/timed translation pair ($ut$ and $ec$) let the thesis "borrow" VPA decidability results for ECVPAs without re-proving them from scratch, and where does this translation break down for full TVPAs?

---

### Chapter 7: Conclusion (pp. 81–83)

**Summary:** Summarizes the thesis's four main contributions (refined SPDA inclusion proof, VPA-extension non-determinizability counterexamples, antichain-based VPA algorithms, and ECVPAs) and proposes two directions for future work: BDD-based data structures to speed up the VPA implementation, and applying the VPA/antichain machinery to XML stream validation.

**Key Definitions & Concepts by Section:**
- **7.1 Summary of Contributions** — recap of Chapters 3–6 results.
- **7.2 Further Research** — Binary Decision Diagrams (BDDs) as a compact, canonical representation for Boolean functions (used in MONA, ALASKA); the XML stream validation problem and its reduction to VPA decision problems; the XML stream firewalling problem (Benedikt et al.) as a target for extension to recursive DTDs via VPAs instead of finite automata.

**Key Questions:**
1. Why might a BDD-based representation of VPA transitions substantially improve on the thesis's prototype implementation, given where the experiments (Chapter 5) showed the standard method's bottleneck to be?
2. What property of VPAs (beyond finite automata) makes them a better fit than finite automata for validating XML streams against recursive DTDs?

---
