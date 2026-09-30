# Pushdown Automata and Inclusion Problems — Index

[[book-guidelines|↩ Back to guidelines]]

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
