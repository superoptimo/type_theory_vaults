# Propositions as Sessions — Guidelines

## Header

**Title:** Propositions as Sessions
**Author(s):** Philip Wadler
**Publication:** Journal version (under consideration for the *Journal of Functional Programming*) of Wadler, P., "Propositions as Sessions," *ICFP '12: Proceedings of the 17th ACM SIGPLAN International Conference on Functional Programming*, ACM, pp. 273–286, 2012.

**Brief Summary:**
This paper connects classical linear logic to session-typed concurrent programming via a Curry-Howard correspondence: propositions as session types, proofs as processes, and cut elimination as communication. It presents CP, a process calculus derived directly from one-sided sequents of classical linear logic, and GV, a linear functional language with session-typed channels, together with a type-preserving translation from GV into CP. Because both calculi arise from a logic with a strongly normalizing cut-elimination procedure, both are guaranteed free of race conditions and deadlock — the central technical payoff of grounding concurrency in Curry-Howard.

**Intent of the Author:**
Wadler seeks to give concurrent/session-typed programming as firm a logical foundation as λ-calculus gives functional programming, resolving a "twist" in prior work (Caires and Pfenning) that had not previously been connected explicitly to session types, and showing that letting cut elimination dictate the process calculus's reduction rules (rather than forcing a tight match to traditional π-calculus) yields a system that is simultaneously simple, symmetric, and provably deadlock-free.

---

## Topic List

1. **[[The-Curry-Howard-Correspondence-for-Concurrency|The Curry-Howard Correspondence for Concurrency]]**
   - [[The-Curry-Howard-Correspondence-for-Concurrency|Propositions as types and proofs as programs]]
   - [[CP-a-Classical-Linear-Logic-Process-Calculus|Propositions as session types and proofs as processes]]
   - [[Commuting-Conversions-and-Cut-Elimination|Cut elimination as communication]]
   - [[The-Curry-Howard-Correspondence-for-Concurrency|Deadlock freedom as a consequence of proof normalization]]
   - [[CP-a-Classical-Linear-Logic-Process-Calculus|Prior translations from linear logic to process calculi]]

2. **[[The-Twist-Reinterpreting-the-Linear-Connectives|The Twist Reinterpreting the Linear Connectives]]**
   - The pairing interpretation of tensor and par
   - [[Related-Work-and-Extensions-to-CP|The session-typed interpretation of tensor and par]]
   - Channel identity preserved across hypothesis and conclusion
   - Why the twist yields an intuitive reading of par
   - Intuitionistic versus classical presentations of the twist

3. **[[CP-a-Classical-Linear-Logic-Process-Calculus|CP a Classical Linear Logic Process Calculus]]**
   - [[CP-a-Classical-Linear-Logic-Process-Calculus|The grammar of propositions as session types]]
   - Duality of propositions
   - [[CP-a-Classical-Linear-Logic-Process-Calculus|The grammar of processes]]
   - [[CP-a-Classical-Linear-Logic-Process-Calculus|The axiom rule as forwarding]]
   - [[CP-a-Classical-Linear-Logic-Process-Calculus|The cut rule as parallel composition]]
   - [[CP-a-Classical-Linear-Logic-Process-Calculus|Structural cut equivalences for swap and associativity]]

4. **[[Output-and-Input-via-the-Multiplicatives|Output and Input via the Multiplicatives]]**
   - [[Output-and-Input-via-the-Multiplicatives|The tensor rule for output]]
   - [[Output-and-Input-via-the-Multiplicatives|The par rule for input]]
   - [[Commuting-Conversions-and-Cut-Elimination|Principal cut reduction between output and input]]
   - [[Output-and-Input-via-the-Multiplicatives|The multiplicative units]]
   - A buying and selling protocol example

5. **[[Selection-and-Choice-via-the-Additives|Selection and Choice via the Additives]]**
   - [[Selection-and-Choice-via-the-Additives|The plus rule for selection]]
   - [[Selection-and-Choice-via-the-Additives|The with rule for choice]]
   - [[Output-and-Input-via-the-Multiplicatives|Principal cut reduction between selection and choice]]
   - [[Selection-and-Choice-via-the-Additives|The additive units]]
   - [[Selection-and-Choice-via-the-Additives|Combining services with selection and choice]]

6. **[[Servers-and-Clients-via-the-Exponentials|Servers and Clients via the Exponentials]]**
   - [[Servers-and-Clients-via-the-Exponentials|Server accept and client request]]
   - [[Servers-and-Clients-via-the-Exponentials|Weakening for no clients]]
   - [[Servers-and-Clients-via-the-Exponentials|Contraction for multiple clients]]
   - [[Output-and-Input-via-the-Multiplicatives|Principal cut reductions for exponentials]]
   - [[Servers-and-Clients-via-the-Exponentials|A replicated server serving multiple clients]]

7. **[[Polymorphism-in-CP|Polymorphism in CP]]**
   - Existential quantification as type instantiation
   - [[Translating-GV-into-CP|Universal quantification as type generalisation]]
   - [[Output-and-Input-via-the-Multiplicatives|Principal cut reduction for quantifiers]]
   - [[Polymorphism-in-CP|Church numerals encoded via polymorphism]]

8. **[[Commuting-Conversions-and-Cut-Elimination|Commuting Conversions and Cut Elimination]]**
   - [[Commuting-Conversions-and-Cut-Elimination|Commuting conversions pushing cuts inside communication]]
   - The anti-Barendregt naming convention
   - [[Commuting-Conversions-and-Cut-Elimination|Top-level cut elimination]]
   - Subject reduction
   - [[Related-Work-and-Extensions-to-CP|Cut elimination corresponding to deadlock freedom]]

9. **[[GV-a-Session-Typed-Functional-Language|GV a Session-Typed Functional Language]]**
   - [[CP-a-Classical-Linear-Logic-Process-Calculus|The grammar of session types]]
   - [[Translating-GV-into-CP|Duality of session types]]
   - Linear versus unlimited types
   - [[GV-a-Session-Typed-Functional-Language|The term grammar for channel operations]]
   - [[GV-a-Session-Typed-Functional-Language|Connect and terminate for channel creation and deallocation]]
   - Differences from Gay and Vasconcelos's original system

10. **[[Translating-GV-into-CP|Translating GV into CP]]**
    - [[Translating-GV-into-CP|Continuation-passing style translation of terms]]
    - [[Translating-GV-into-CP|The surprising duality in the translation of session types]]
    - [[Translating-GV-into-CP|Translation of general types]]
    - [[Translating-GV-into-CP|The translation preserves types]]

11. **[[Related-Work-and-Extensions-to-CP|Related Work and Extensions to CP]]**
    - [[CP-a-Classical-Linear-Logic-Process-Calculus|The history of session types]]
    - [[Related-Work-and-Extensions-to-CP|Alternative approaches to deadlock freedom]]
    - [[Related-Work-and-Extensions-to-CP|Linear types for process calculi]]
    - [[Related-Work-and-Extensions-to-CP|Linear proof search and logic programming]]
    - [[Related-Work-and-Extensions-to-CP|DILL versus CLL as competing foundations]]
    - The Mix rule and Binary Cut as reintroducing races and deadlock
    - [[Translating-GV-into-CP|Multiparty session types as future work]]

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 1–3)

**Summary:** Sets the stage by recalling how λ-calculus grounds functional programming in the Curry-Howard correspondence, then asks what could give concurrent programming as firm a foundation; surveys the line of work from Abramsky and Bellin-Scott through Honda to Caires and Pfenning, and previews the paper's three contributions — the calculus CP, the calculus GV, and a type-preserving translation between them with a tighter connection to cut elimination than prior translations achieved.

**Key Definitions & Concepts:**
- Curry-Howard correspondence — propositions *as* types, proofs *as* programs, normalisation of proofs *as* evaluation of programs
- $\pi$DILL — Caires and Pfenning's calculus based on dual intuitionistic linear logic, with propositions as session types and cut elimination as communication
- CP — this paper's classical linear logic process calculus, using one-sided sequents ("Classical Processes")
- GV — this paper's linear functional language with session types ("Good Variation"), designed to be free of races and deadlock
- Deadlock freedom as identifying a fragment of process calculi for which computation always progresses, echoing how well-typed $\lambda$-terms always terminate
- Commuting conversions as the aspect of cut elimination that prior translations (Bellin and Scott; Caires and Pfenning) fail to capture tightly

**Key Questions:**
1. In what precise sense do prior translations from linear logic to $\pi$-calculus (Abramsky; Bellin and Scott) fall short of a full Curry-Howard correspondence, and what does Caires and Pfenning's twist fix?
2. Why does the paper let cut elimination directly specify the reduction rules for CP, rather than aiming for a tight match to traditional $\pi$-calculus?
3. Why does a Curry-Howard foundation for concurrency guarantee freedom from both races and deadlock, and why is that a meaningful payoff?

---

### Chapter 2: The Twist (pp. 3–5)

**Summary:** Isolates the small but crucial difference between Abramsky/Bellin-Scott's process interpretation of linear logic and Caires-Pfenning's session-typed interpretation: whether the hypotheses and conclusion of the $\otimes$ and $\parr$ rules refer to the same channel or to different channels.

**Key Definitions & Concepts:**
- The pairing interpretation (Abramsky; Bellin and Scott) — $A\otimes B$ is the type of a channel outputting a pair, with hypotheses using fresh names $y,z$ distinct from the conclusion's $x$
- The session-typed interpretation (Caires and Pfenning, adopted here) — $A\otimes B$ is the type of a channel that outputs an $A$ and then behaves as $B$, with hypothesis and conclusion reusing the same channel name $x$
- The channel's type evolving as communication proceeds, the intuition underlying session types
- The apparent unnaturality of interpreting $A\otimes B$ and $A\parr B$ asymmetrically, resolved by the isomorphism $A\otimes B \cong B\otimes A$
- Intuitionistic $\pi$DILL (two-sided sequents, duplicated $\otimes$-L/$\multimap$-R rules for output) versus classical CP (one-sided sequents, a single rule per connective)

**Key Questions:**
1. Concretely, which channel names appear in the premises versus the conclusion of the Abramsky/Bellin-Scott $\otimes$ rule, and how does that differ in Caires and Pfenning's rule?
2. Why does using two-sided (intuitionistic) sequents force $\pi$DILL to give output two separate rules, and why is this a practical usability problem for connecting servers and clients?
3. How does reusing the channel name $x$ across premises and conclusion correspond to the idea of a session type "evolving"?

---

### Chapter 3: Classical linear logic as a process calculus (pp. 5–22)

**Summary:** Presents CP in full: the grammar of propositions/session types, duality, the process grammar, and the core typing rules, followed by seven subsections working through structural rules, each dual pair of connectives, polymorphism, commuting conversions, and cut elimination, interleaved with worked internet-commerce examples.

**Key Definitions & Concepts by Section:**
- **3 (front matter)** — CP; the propositions/session types grammar ($X$, $X^\perp$, $A\otimes B$, $A\parr B$, $A\oplus B$, $A\& B$, $!A$, $?A$, $\exists X.B$, $\forall X.B$, $1$, $\bot$, $0$, $\top$); duality $(\cdot)^\perp$ as an involution; substitution $B\{A/X\}$; environments $\Gamma,\Delta,\Theta$ under linear maintenance; the process grammar (link, parallel composition, output, input, selection, choice, server accept, client request, type output/input, empty forms); judgments $P \vdash x_1:A_1,\dots,x_n:A_n$
- **3.1 Structural rules** — Axiom as forwarding along dual channels; Cut as parallel composition with name restriction; structural equivalences (Swap), (Assoc); reduction (AxCut) simplifying a cut against an axiom
- **3.2 Output and input** — the $\otimes$ rule (output $A$ then behave as $B$); the $\parr$ rule (input $A$ then behave as $B$); principal reduction $(\beta_{\otimes\parr})$ corresponding to communication; the isomorphism $A\otimes B \cong B\otimes A$; the multiplicative units $1$ and $\bot$; a worked buy/sell commerce example
- **3.3 Selection and choice** — the $\oplus$ rules (left/right selection); the $\&$ rule (offering a choice); principal reduction $(\beta_{\oplus\&})$; the additive units $0$ (no rule, no reduction) and $\top$; worked shop/quote and combined select/choice examples
- **3.4 Servers and clients** — the $!$ rule (server accept, spawning a fresh copy per request); the three client rules for $?$ (dereliction, weakening, contraction); principal reductions $(\beta_{!?})$, $(\beta_{!W})$, $(\beta_{!C})$; the priming convention for replicated names; a worked replicated-server example
- **3.5 Polymorphism** — the $\exists$ rule (instantiation, transmitting a proposition); the $\forall$ rule (generalisation, receiving a proposition); principal reduction $(\beta_{\exists\forall})$; Church numerals encoded via polymorphic quantification
- **3.6 Commuting conversions** — pushing a cut inside a communication operation; the anti-Barendregt naming convention; why $(\kappa_\parr)$, pushing a cut inside input, remains sound
- **3.7 Cut elimination** — congruence rules for cuts; Theorem 1 (subject reduction — well-typed processes reduce to well-typed processes); Theorem 2 (top-level cut elimination — every process reduces to a non-cut process); the correspondence between top-level cut elimination and deadlock freedom

**Key Questions:**
1. Why must the environments $\Gamma$ and $\Delta$ in the Cut rule be disjoint, and how does that disjointness guarantee freedom from races?
2. Walk through the principal cut reduction $(\beta_{\otimes\parr})$: what does it mean computationally, and how does it correspond to a $\pi$-calculus communication step?
3. Why is there no rule for the additive unit $0$, and what does its absence say about a process offering "no alternatives"?
4. What distinguishes a server ($!$) from its clients ($?$) in terms of which structural rules apply, and why must a server communicate only with other replicable processes?
5. In what precise sense does Theorem 2 establish that CP is deadlock-free?

---

### Chapter 4: A session-typed functional language (pp. 23–31)

**Summary:** Introduces GV, a linear functional language with session-typed channel primitives, modifying Gay and Vasconcelos's original system (splitting `end` into dual $\mathsf{end}_!$/$\mathsf{end}_?$, replacing accept/request/fork with connect/terminate) to guarantee deadlock freedom, then gives its full continuation-passing-style translation into CP.

**Key Definitions & Concepts by Section:**
- **4 (front matter)** — GV's typing rules (Id, Unit, Weaken, Contract, $\multimap$-I/E, $\to$-I/E, $\otimes$-I/E, Send, Receive, Select, Case, Connect, Terminate); differences from Gay and Vasconcelos (splitting `end` into $\mathsf{end}_!/\mathsf{end}_?$; replacing accept/request/fork with with-connect-to/terminate); the session types grammar ($!T.S$, $?T.S$, $\oplus\{l_i:S_i\}$, $\&\{l_i:S_i\}$, $\mathsf{end}_!$, $\mathsf{end}_?$); duality of session types; the general type grammar (session types, tensor product, linear and unlimited function types, Unit); linear versus unlimited classification; the term grammar (identifier, unit, abstraction, application, pair construction/deconstruction, send, receive, select, case, connect, terminate); the Send and Receive typing rules and why channels thread linearly through operations; the Connect rule (creating a channel at dual types $S$ and $\overline S$) and Terminate rule (deallocating an exhausted channel); a worked buy/sell example re-expressed in GV
- **4.1 Translation** — the translation of session types into CP propositions and its surprising duality (GV output translates to CP $\parr$, GV input to CP $\otimes$); the translation of general types; the continuation-passing-style translation of terms $\llbracket M \rrbracket z$; Theorem 3 (the translation preserves types)

**Key Questions:**
1. Why does GV split Gay and Vasconcelos's single `end` type into two dual terminators, and why does that matter for deadlock freedom?
2. Why does GV's output session type $!T.S$ translate to the CP connective $\parr$ (normally read as input) rather than $\otimes$ — what intuition about arguments versus results explains this inversion?
3. What does Theorem 3 guarantee about GV programs, and how does that transfer GV's race- and deadlock-freedom from CP's cut-elimination result?

---

### Chapter 5: Related work (pp. 31–33)

**Summary:** Situates CP and GV against the broader literature — the origins and development of session types, alternative approaches to guaranteeing deadlock freedom, linear type systems for process calculi, the analogy between logic programming and proof search, polymorphic extensions, and, at greatest length, a comparison between Caires-Pfenning's intuitionistic DILL-based approach and this paper's classical CLL-based approach.

**Key Definitions & Concepts:**
- Session types (Honda; Takeuchi, Honda and Kubo; Yoshida and Vasconcelos); subtyping for session types (Gay and Hole); GV's origin in Gay and Vasconcelos's linear functional language
- Alternative deadlock-freedom guarantees via a partial order on time tags (Sumii and Kobayashi) or constraints on dependency graphs (Carbone and Debois)
- Linear type systems surveyed for process calculi (Kobayashi); embedding session types into a linearly-typed $\pi$-calculus (Kobayashi, Pierce and Turner)
- Linear proof search and its analogy to logic programming (Miller; Kobayashi and Yonezawa)
- The polymorphic $\pi$-calculus (Turner) underlying CP's polymorphism; Church-style versus Curry-style polymorphism for session types
- Locality — names received along a channel usable only to send, not to receive — as DILL's advantage over CLL, and DILL's better prospects for extension to dependent types

**Key Questions:**
1. What is locality, and why do Caires, Pfenning and Toninho argue it favors a DILL-based (intuitionistic) formulation over a CLL-based (classical) one like CP?
2. How do Sumii-Kobayashi's and Carbone-Debois's approaches to deadlock freedom differ structurally from CP's approach via cut elimination?

---

### Chapter 6: Conclusion (pp. 33–34)

**Summary:** Reflects on why $\lambda$-calculus succeeds as a foundation partly because it spans both a terminating fragment and a Turing-complete fragment, poses the analogous question for concurrency, and sketches two extensions — Mix and Binary Cut — that recover more general (racy or deadlocking) concurrency at the cost of leaving CP's deadlock-free fragment.

**Key Definitions & Concepts:**
- The analogy between typed/untyped $\lambda$-calculus (termination versus Turing-completeness) and race/deadlock-free CP versus more general process calculi
- The Mix rule (Girard) — composing $P$ and $Q$ with no channels in common, equivalent to provability of $A\otimes B \multimap A\parr B$, implementable via a primitive $\mathsf{par}_{y,z}$
- The Binary Cut rule (Abramsky, Gay and Nagarajan) — composing $P$ and $Q$ sharing two channels, equivalent to provability of $A\parr B \multimap A\otimes B$, permitting races and deadlock via communication loops
- Compactness — having both Mix and Binary Cut lets $A\otimes B$ and $A\parr B$ be derived from each other, connecting to an embedding of full untyped $\pi$-calculus into a compact linear system
- Multiparty session types as an open direction for extending the logical foundation

**Key Questions:**
1. Why do Mix and Binary Cut individually still preserve deadlock freedom, yet together make CP "compact" in a way that recovers the full untyped $\pi$-calculus?
2. What analogy does the author draw between recursive types (solving $X \simeq X \to X$) in $\lambda$-calculus and the search for principled extensions of CP supporting full concurrency?

---
