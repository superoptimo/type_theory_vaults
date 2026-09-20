# Domain-Aware Session Types (Extended Version) — Guidelines

## Header

**Title:** Domain-Aware Session Types (Extended Version)
**Author(s):** Luís Caires (Universidade Nova de Lisboa), Jorge A. Pérez (University of Groningen), Frank Pfenning (Carnegie Mellon University), Bernardo Toninho (Universidade Nova de Lisboa)
**Publication:** CONCUR 2019 (extended version with appendices), arXiv:1907.01318v1 [cs.LO], 2 Jul 2019

**Brief Summary:**
This paper generalizes the Curry-Howard interpretation of binary session types (Caires–Pfenning) by extending linear logic with hybrid logic's modal worlds, reinterpreted as *domains*. A parametric Kripke-style accessibility relation governs which domains a process may migrate to or communicate with, giving a logically-founded, statically-checked notion of domain-aware, message-passing concurrency. Well-typed processes retain session fidelity, global progress, and termination, and additionally are guaranteed to respect domain accessibility. The framework is then lifted to multiparty session types via a domain-aware global-type construct (`p moves q̃ to ω for G1;G2`) and *medium processes* that give it a precise, compositional semantics reducible to the binary theory.

**Intent of the Author:**
The authors aim to close a gap in existing (binary and multiparty) session type frameworks: none of them can express or statically enforce domain-related requirements (e.g., "payment data may only be exchanged after entering a secure domain"), even though real distributed systems are pervasively domain-aware. They want to show that hybrid linear logic gives a principled, minimal extension that adds this expressiveness while preserving all classical correctness guarantees, and that the binary theory's guarantees transfer cleanly to a multiparty setting.

---

## Topic List

1. **Session Types via the Curry–Howard Correspondence** : [[Session-Types-via-the-Curry-Howard-Correspondence|Link]]
   - Propositions as session types : [[Applications-and-Worked-Examples|Link1]], [[Hybrid-Linear-Logic-and-Domain-Aware-Types|Link2]], [[Multiparty-Session-Types|Link3]], [[Session-Types-via-the-Curry-Howard-Correspondence|Link4]]
   - Proofs as typing derivations : [[Typing-Judgments-and-Rules|Link]]
   - Proof reduction as process communication : [[Session-Types-via-the-Curry-Howard-Correspondence|Link]]
   - Linear logic connectives as session constructors : [[Session-Types-via-the-Curry-Howard-Correspondence|Link]]
   - Session fidelity as type preservation : [[Session-Types-via-the-Curry-Howard-Correspondence|Link]]
   - Global progress as deadlock freedom : [[Session-Types-via-the-Curry-Howard-Correspondence|Link]]

2. **Hybrid Linear Logic and Domain-Aware Types** : [[Hybrid-Linear-Logic-and-Domain-Aware-Types|Link]]
   - Modal worlds reinterpreted as domains
   - The $@_\omega A$ connective for domain migration : [[Hybrid-Linear-Logic-and-Domain-Aware-Types|Link]]
   - Universal and existential quantification over domains
   - The "here" operator binding the current domain : [[Hybrid-Linear-Logic-and-Domain-Aware-Types|Link1]], [[Multiparty-Session-Types|Link2]]
   - Kripke-style accessibility relations between domains
   - Well-formed sequents and the domain accessibility invariant
   - Conservativity over non-hybrid session types : [[Hybrid-Linear-Logic-and-Domain-Aware-Types|Link]]

3. **The Domain-Aware Session $\pi$-Calculus** : [[The-Domain-Aware-Session-Pi-Calculus|Link]]
   - Process syntax with explicit domain migration prefixes
   - Domain output and input as first-class communication
   - Forwarding as a copycat process : [[The-Domain-Aware-Session-Pi-Calculus|Link]]
   - Labeled choice and selection : [[The-Domain-Aware-Session-Pi-Calculus|Link]]
   - Structural congruence : [[The-Domain-Aware-Session-Pi-Calculus|Link]]
   - Reduction semantics : [[The-Domain-Aware-Session-Pi-Calculus|Link]]
   - Labeled transition system : [[The-Domain-Aware-Session-Pi-Calculus|Link]]

4. **Typing Judgments and Rules** : [[Typing-Judgments-and-Rules|Link]]
   - Linear and unrestricted typing contexts
   - Domain-indexed type assignments
   - The accessibility judgment : [[Typing-Judgments-and-Rules|Link]]
   - The cut rule as process composition : [[Session-Types-via-the-Curry-Howard-Correspondence|Link]]
   - Domain substitution : [[Typing-Judgments-and-Rules|Link]]

5. **Type Safety and Correctness Results** : [[Type-Safety-and-Correctness-Results|Link]]
   - Type preservation : [[Session-Types-via-the-Curry-Howard-Correspondence|Link1]], [[Type-Safety-and-Correctness-Results|Link2]]
   - Global progress : [[Session-Types-via-the-Curry-Howard-Correspondence|Link1]], [[Type-Safety-and-Correctness-Results|Link2]]
   - Termination via linear logical relations : [[Type-Safety-and-Correctness-Results|Link]]
   - Domain preservation : [[Type-Safety-and-Correctness-Results|Link]]

6. **Multiparty Session Types** : [[Multiparty-Session-Types|Link]]
   - Global types and local types : [[Multiparty-Session-Types|Link]]
   - Merge-based projection : [[Multiparty-Session-Types|Link]]
   - Domain-aware migration in global types : [[Hybrid-Linear-Logic-and-Domain-Aware-Types|Link1]], [[Applications-and-Worked-Examples|Link2]]
   - Local type fusion : [[Multiparty-Session-Types|Link]]
   - Well-formed global types : [[Multiparty-Session-Types|Link]]

7. **Medium Processes** : [[Medium-Processes|Link]]
   - Medium process semantics for global types : [[Medium-Processes|Link]]
   - Fusion of processes : [[Medium-Processes|Link]]
   - Compositional typing : [[Medium-Processes|Link]]
   - Characterization theorems relating global types and typed mediums : [[Medium-Processes|Link]]

8. **Applications and Worked Examples** : [[Applications-and-Worked-Examples|Link]]
   - Secure e-commerce checkout protocol
   - Domain-aware middleware offloading : [[Applications-and-Worked-Examples|Link]]
   - Negotiation procedure with trusted sub-protocols : [[Applications-and-Worked-Examples|Link]]
   - Spatial distribution as a generalization of $\lambda 5$

9. **Related Work and Positioning** : [[Related-Work-and-Positioning|Link]]
   - Logical foundations of concurrency
   - Ambient calculi and distributed $\pi$-calculus : [[Related-Work-and-Positioning|Link]]
   - Shared session types with worlds : [[Multiparty-Session-Types|Link1]], [[Applications-and-Worked-Examples|Link2]], [[Hybrid-Linear-Logic-and-Domain-Aware-Types|Link3]]
   - Nested multiparty protocols : [[Related-Work-and-Positioning|Link]]

---

## Chapter Summaries

### Section 1: Introduction (pp. 1–3)

**Summary:** Motivates domain-awareness in message-passing systems (services span heterogeneous, partially-known software/hardware domains) and argues that existing session type frameworks — even Curry-Howard-based ones — cannot express domain-related requirements such as privilege escalation before contacting a trusted server. Introduces the paper's approach (hybrid linear logic with modal worlds as domains) via a running middleware/client/server example, previews the domain-aware multiparty construct, and lists the three main contributions.

**Key Definitions & Concepts:**
- **Session fidelity** — type preservation: well-typed processes evolve only to well-typed processes.
- **Global progress** — deadlock freedom: well-typed processes never get stuck.
- **Domain** — an abstraction (location, principal, administrative/security level, etc.) attached to session channels, subject to an accessibility relation.
- **Domain migration** — moving a process's/session's locus of interaction to another (accessible) domain.
- **Global type with domain migration** — `p moves q̃ to ω for G1;G2`, the paper's new multiparty construct for domain-scoped sub-protocols.

**Key Questions:**
1. Why is "Shipper resides in domain AmazonUS"-style information inexpressible in prior session type frameworks, and what concrete correctness problem does that cause?
2. In the offload example, what does moving to domain `wpriv` guarantee that a plain (non-domain-aware) delegation to the server would not?

---

### Section 2: Process Model (pp. 3–4)

**Summary:** Introduces a synchronous, domain-aware $\pi$-calculus: a session $\pi$-calculus extended with explicit prefixes for domain migration (`x⟨y@ω⟩.P`, `x(y@ω).P`) and domain communication (`x⟨ω⟩.P`, `x(α).P`), on top of the standard constructs (inaction, parallel composition, restriction, output/input, replication, forwarding, labeled choice/selection). Gives structural congruence and reduction rules; reduction at this stage is untyped and permits synchronization regardless of domain, deferring domain discipline to the type system.

**Key Definitions & Concepts:**
- **Process syntax (Def. 2.1)** — $P ::= 0 \mid P|Q \mid (\nu y)P \mid x\langle y\rangle.P \mid x(y).P \mid {!}x(y).P \mid [x\leftrightarrow y] \mid x\triangleright\{l_i:P_i\}_{i\in I} \mid x\triangleleft l_i;P \mid x\langle y@\omega\rangle.P \mid x(y@\omega).P \mid x\langle\omega\rangle.P \mid x(\alpha).P$
- **Forwarding $[x\leftrightarrow y]$** — a primitive copycat process equating channels $x$ and $y$.
- **Labeled choice/selection** — $x\triangleright\{l_i:P_i\}_{i\in I}$ offers a branch; $x\triangleleft l;P$ selects one.
- **Domain migration prefixes** — $x\langle y@\omega\rangle.P$ (offer to migrate) / $x(y@\omega).P$ (signal migration), always paired with a fresh session channel.
- **Domain communication prefixes** — $x\langle\omega\rangle.P$ (send a domain) / $x(\alpha).P$ (receive a domain variable).
- **Reduction ($P\to Q$)** — closed under structural congruence; defines process computation, including domain-tagged communication rules.

**Key Questions:**
1. Why does the untyped reduction relation allow synchronization "independently of the domains of their subjects," and what later component of the system restores domain discipline?
2. What is the operational difference between the domain-migration prefixes ($x\langle y@\omega\rangle$) and the domain-communication prefixes ($x\langle\omega\rangle$)?

---

### Section 3: Domain-Aware Session Types via Hybrid Logic (pp. 4–9)

**Summary:** The technical core of the paper. Develops the type syntax (linear logic connectives plus hybrid operators $@_\omega A$, $\forall\alpha.A$, $\exists\alpha.A$, $\downarrow\alpha.A$), the two typing judgments (accessibility $\Omega \vdash \omega_1 \prec \omega_2$ and process typing $\Omega;\Gamma;\Delta \vdash P :: z{:}A[\omega]$), and the well-formedness invariant tying every session in $\Delta$ to domains accessible from the offered session's domain. Walks through key typing rules (multiplicative, additive, exponential, and especially the four hybrid rules), illustrates the framework on a secured web-store/payment example, and states the four main safety theorems.

**Key Definitions & Concepts by Section:**
- **Types (Def. 3.1)** — $A ::= 1 \mid A\multimap B \mid A\otimes B \mid \&\{l_i:A_i\} \mid \oplus\{l_i:A_i\} \mid {!}A \mid @_\omega A \mid \forall\alpha.A \mid \exists\alpha.A \mid \downarrow\alpha.A$; propositions of intuitionistic linear logic with labeled n-ary additives, extended with hybrid connectives.
- **Accessibility environment $\Omega$** — hypotheses $\omega_1 \prec \omega_2$ ("$\omega_2$ accessible from $\omega_1$"); $\prec^*$ is its reflexive-transitive closure.
- **Type assignment $x{:}A[\omega]$** — channel $x$ used per session $A$, located at domain $\omega$.
- **Linear vs. unrestricted contexts ($\Delta$, $\Gamma$)** — $\Delta$ obeys linear (no weakening/contraction) discipline; $\Gamma$ is unrestricted.
- **Well-formed sequent** — $\Omega;\Gamma;\Delta \vdash P :: z{:}C[\omega_1]$ is well-formed iff $\Omega \vdash \omega_1 \prec^* \omega_2$ for every $x{:}A[\omega_2]\in\Delta$ (written $\Omega\vdash\omega_1\prec^*\Delta$); this invariant is preserved bottom-up by every rule and statically excludes interaction between inaccessible domains.
- **(cut) rule** — composes $P$ offering $x{:}A[\omega_2]$ with $Q$ using it, requiring $\omega_1\prec^*\omega_2$ and $\omega_1\prec^*\Delta_1$.
- **$@_{\omega_2}A$ (domain migration type)** — a session available by first moving to the directly accessible domain $\omega_2$; typed by rules (@R)/(@L).
- **$\forall\alpha.A$ / $\exists\alpha.A$ (domain quantification)** — a service parametric in, or committing to, a fresh accessible domain.
- **$\downarrow\alpha.A$ ("here")** — binds the session's *current* domain $\omega$ to $\alpha$ in $A$; produces no process-level action.
- **(whyp)** — the base accessibility rule; adding reflexivity/transitivity/symmetry rules yields an equivalence-relation instantiation of accessibility.
- **Type preservation (Theorem 3.3)** — typing is preserved by reduction.
- **Domain substitution (Lemma 3.2)** — substituting an accessible domain for a bound domain variable preserves typing; underlies safe domain communication.
- **Global progress (Theorem 3.4)** — a live, well-typed process with empty contexts can always reduce.
- **Live process** — $\mathrm{live}(P)$ iff $P\equiv(\nu\tilde n)(\pi.Q\mid R)$ for a non-replicated guarded process $\pi.Q$.
- **Termination (Theorem 3.5)** — every well-typed process terminates (no infinite reduction path), via linear logical relations.
- **Domain preservation (Theorems 3.6–3.7)** — well-formedness is preserved by sub-derivations, and reduction only ever moves sessions to domains transitively accessible from their prior domain.

**Key Questions:**
1. Why must the (@R) rule check that *all* domains in $\Delta$ remain accessible from $\omega_2$, not just that $\omega_1\prec\omega_2$?
2. In the WStore$_{sec}$ example, why is `c ≺ ws; ·; Payment[sec] ⊢ Client′ :: z:T[c]` underivable, and what real-world guarantee does that formally express?
3. What exactly does $\downarrow\alpha.A$ add to the type language given that it has no operational content at the process level?
4. How does the well-formedness invariant (Ω ⊢ ω₁ ≺* Δ) differ in its treatment of the linear context Δ versus the unrestricted context Γ, and why is that asymmetry justified?

---

### Section 4: Domain-Aware Multiparty Session Types (pp. 9–13)

**Summary:** Extends the framework to multiparty session types by adding global types, local types (reusing the hybrid connectives from § 3), and merge-based projection, with a genuinely new global-type construct for domain-scoped sub-protocols: `p moves q̃ to ω for G1;G2`. Rather than building a separate type system for the process calculus of § 2, multiparty protocols are given semantics via *medium processes* (extending Caires–Pérez's prior medium-based account) that orchestrate participants' interactions and inherit all of § 3's correctness guarantees. States and sketches the two characterization theorems connecting well-formed global types, typed mediums, and independently-typed participant implementations.

**Key Definitions & Concepts by Section:**
- **Global/local types (Def. 4.1)** — $G ::= \mathrm{end} \mid p\to q{:}\{l_i\langle U_i\rangle.G_i\} \mid p\ \mathrm{moves}\ \tilde q\ \mathrm{to}\ \omega\ \mathrm{for}\ G_1;G_2$; $T ::= \mathrm{end}\mid p?\{\ldots\}\mid p!\{\ldots\}\mid\forall\alpha.T\mid\exists\alpha.T\mid @_\alpha T\mid\downarrow\alpha.T$.
- **`p moves q̃ to ω for G1;G2`** — participants $p,\tilde q$ migrate to domain $\omega$ (led by $p$) to run sub-protocol $G_1$, then migrate back to run $G_2$; distinguished from delegation by supporting domain-scoped sub-protocols with participant return.
- **Merge operator ($T_1\sqcup T_2$, Def. 4.3)** — combines local types that may differ across branches but remain compatible, enabling flexible (non-identical) projections.
- **Local type fusion ($T_1\circ T_2$, Def. 4.4)** — sequentially appends one local type's behavior after another's, used to splice $G_1$'s and $G_2$'s local behavior together.
- **Merge-based projection ($G{\upharpoonright}r$, Def. 4.5)** — projects a global type onto participant $r$; for the migration construct, produces types of the shape $\downarrow\beta.(\exists/\forall\alpha.@_\alpha G_1{\upharpoonright}r)\circ @_\beta G_2{\upharpoonright}r$.
- **Well-formed global type (Def. 4.6)** — projection is defined for every participant.

**Key Questions:**
1. How does the domain-aware migration construct `p moves q̃ to ω for G1;G2` differ semantically from ordinary session delegation, and why does the paper insist this is "a different idiom altogether"?
2. Why does projecting the leader `p` use $\exists\alpha$ while projecting a follower $q_i \in \tilde q$ uses $\forall\alpha$ in the migration construct's projection rule?
3. What role does the merge operator play in making projection total on more global types than a naive "identical branches only" projection would allow?

---

### Section 4 (cont.): Medium Processes (pp. 11–13)

**Summary:** Defines medium processes $M^{\tilde\omega}\llbracket G\rrbracket(\tilde c)$, well-typed processes from § 2 that faithfully mediate the communication behavior specified by a global type, using participant-indexed names. Gives process fusion (mirroring local-type fusion) for the migration case, works a full running example (the middleware/client/server offload protocol), and states the two characterization results connecting well-formed global types to compositionally-typed mediums and vice versa.

**Key Definitions & Concepts:**
- **Medium process (Def. 4.8)** — inductively defined on $G$; for $p\to q:\{\ldots\}$ it relays the chosen label and payload between $p$ and $q$; for the migration construct it exchanges the fresh domain identifier, migrates all of $p,\tilde q$, runs the medium for $G_1$, migrates back, and runs the medium for $G_2$.
- **Fusion of processes ($\circ$, Def. 4.7)** — a partial operator splicing one process's continuation after another's, dual to local type fusion.
- **Compositional typing (Def. 4.9)** — a typing $\Omega;\Gamma;\Delta\vdash M^{\tilde\omega}\llbracket G\rrbracket(\tilde c) :: z{:}1$ where $\Delta$'s domain is exactly $\mathrm{npart}(G)$ and the medium offers no behavior of its own.
- **Local-types-to-binary-types mapping ($\langle\!\langle\cdot\rangle\!\rangle$, Def. 4.10)** — erases participant information from local types to yield ordinary binary session types.
- **Theorem 4.11 (Global Types → Typed Mediums)** — every well-formed $G$ has a compositionally-typed medium using the projected/erased binary types.
- **Theorem 4.12 (Well-Typed Mediums → Global Types)** — the converse: any compositionally-typed medium arises (up to the $\sqsupset_\downarrow$ pre-congruence) from some well-formed global type.

**Key Questions:**
1. Why must a compositional typing (Def. 4.9) require $C=1$ (the medium offers nothing of its own) — what would break if the medium were allowed to offer a residual behavior?
2. In the medium for the migration construct, why are the migrated participants' session handles ($y_p, y_{q_1},\ldots$) threaded through *both* the sub-medium for $G_1$ and, via fusion, the continuation medium for $G_2$?

---

### Section 5: Related Work (pp. 13–14)

**Summary:** Positions the paper against prior logical foundations of session-based concurrency (Caires–Pfenning, Wadler, Dal Lago–Di Giamberardino), medium-based multiparty accounts (Caires–Pérez), Ambient calculi (mobility of administrative domains but no structured-interaction guarantees), the distributed $\pi$-calculus, nested multiparty protocols (Demangeon–Honda, structurally similar but without domain-awareness), and shared session types with worlds (Balzer, Toninho, Pfenning — a non-conservative, partial-order-based alternative aimed purely at deadlock-freedom).

**Key Definitions & Concepts:**
- **Ambient calculus** — models mobility of administrative domains (ambients) but not structured/session-typed interaction.
- **Distributed $\pi$-calculus (D$\pi$)** — flat locations, local communication, process migration; contrasted with the paper's domain hierarchy and accessibility relation.
- **Nested multiparty protocols (Demangeon–Honda)** — a syntactically similar nesting construct aimed at modularity, without domains or migration.
- **Shared session types with worlds (Balzer et al.)** — accessibility as a partial order over shared sessions for deadlock-freedom, not conservative over linear logic.

**Key Questions:**
1. In what precise sense is the paper's system "conservative" with respect to prior Curry–Howard session type theories, and why does the Balzer et al. system lack this property?
2. Why does the paper consider structured, session-typed interaction (not just domain mobility) to be its key differentiator from Ambient calculi?

---

### Section 6: Concluding Remarks (p. 14)

**Summary:** Recaps the contribution (a Curry-Howard interpretation of hybrid linear logic as domain-aware session types, with strong correctness guarantees carried through to a multiparty setting via mediums) and sketches future work: contract-enforcing/monitoring mediums, and the relationship between domain accessibility enforcement and information-flow analyses for multiparty sessions.

**Key Definitions & Concepts:**
- **Contract-enforcing mediums** — proposed future extension where mediums act as runtime monitors enforcing a domain-aware protocol specification.
- **Information-flow analysis connection** — noted similarity to (but non-identity with) information-flow control for multiparty sessions, since the accessibility relation lacks directionality.

**Key Questions:**
1. Why does the paper explicitly note that its accessibility-based enforcement "does not capture the directionality needed" for information-flow analyses — what would directionality add?

---

### Appendix A: Omitted Definitions and Proofs (pp. 18–25)

**Summary:** Supplies the full technical apparatus omitted from the main text: structural congruence, the labeled transition system (LTS), the remaining typing rules (additive/exponential/cut-with-replication), the additional reduction lemmas needed for type preservation (for $\forall$, $\exists$, $@$), the pre-congruence $\sqsupset_\downarrow$ on local types used in Theorem 4.12, and full proofs of the medium characterization theorems (4.11, 4.12) by induction on global-type structure.

**Key Definitions & Concepts by Section:**
- **A.1 Structural Congruence** — standard $\pi$-calculus laws (associativity/commutativity of $\mid$, scope extrusion, $\alpha$-equivalence, forwarding symmetry).
- **A.2 Labeled Transition System** — early LTS extended with labels for choice, migration ($x.y@\omega$), and domain communication; establishes coincidence of $\tau$-labeled transitions with reduction up to $\equiv$.
- **A.3 Omitted Typing Rules** — full additive rules (&R, &L₁, &L₂, ⊕R₁, ⊕R₂, ⊕L), exponential rules (!L, !R), and the replication-aware cut (cut!).
- **A.4 Additional Lemmas for Type Preservation** — reduction lemmas per connective (⊗, ∀, ∃, @) relating a process step to a corresponding logical proof reduction through (cut).
- **A.5 Pre-congruence on Local Types ($\sqsupset_\downarrow$, Def. A.7)** — relates local types up to merge and spurious/required "here" ($\downarrow\alpha$) operators; needed because mediums may silently introduce or omit $\downarrow$.
- **A.6 Proofs of Medium Characterization** — full inductive proofs of Theorems 4.11–4.12, using Proposition A.8 (fusing two compositional typings) as the key composition lemma.

**Key Questions:**
1. Why does proving Theorem 4.11 for the migration case require using Proposition A.8 (process/typing fusion) rather than a direct single typing derivation?
2. What silent typing rules (e.g., (&L₂), (↓L)) create the need for the pre-congruence $\sqsupset_\downarrow$ instead of exact syntactic equality between projected local types and medium-derived types?

---

### Appendix B: Extended Examples (pp. 25–27)

**Summary:** Three worked multiparty examples exercising domain migration: a negotiation procedure between a client, agent, and instrument (adapted from Demangeon–Honda) with a trusted negotiation sub-domain; the middleware/client/server offloading protocol from the introduction, spelled out with its full medium process; and a minimal "secure communication domain" excerpt showing that domain movement gates *who can interact with whom*, not just *what is communicated*.

**Key Definitions & Concepts:**
- **Negotiation procedure ($\mathrm{Nego}_{p,q}$)** — a request/proposition/accept-or-counter-offer sub-protocol run in a trusted domain shared by two of three participants.
- **Domain-scoped trust modeling** — using `moves ... to ω for ...` to model that certain participants must be jointly present in a private domain to negotiate or transact.
- **Data-flow capture via mediums** — the medium specification captures all data flows between mutually inaccessible participants (e.g., client and bank) even though they cannot interact directly.

**Key Questions:**
1. In the negotiation example, what would go wrong (in terms of the type system) if the agent tried to run the negotiation sub-protocol with the client without both first migrating to domain $d_n$?

---

### Appendix C: Examples of Domain-Aware Binary Sessions (pp. 27–29)

**Summary:** Two extended binary examples. C.1 revisits the secured web-store/payment example from § 3 in full detail, including universally- and existentially-quantified payment domains (avoiding hardwiring the payment domain in the type). C.2 shows that the framework strictly generalizes Murphy et al.'s Curry-Howard interpretation of modal logic S5 ($\lambda 5$) for spatially distributed computation, by encoding $\Box A$ and $\Diamond A$ as $\forall\alpha.@_\alpha A$ and $\exists\alpha.@_\alpha A$ respectively, and gives process realizations of the S5 axioms K$\Diamond$, T, and 5 — resolving $\lambda 5$'s original "action at a distance" problem because all communication in this system is explicit.

**Key Definitions & Concepts:**
- **$\mathrm{WStore}_\exists$ / $\mathrm{WStore}_\forall$** — existentially/universally domain-quantified refinements of the web-store type, avoiding a hardwired payment domain.
- **$\Box A = \forall\alpha.@_\alpha A$** — "usable in any domain," the modal-necessity reading.
- **$\Diamond A = \exists\alpha.@_\alpha A$** — "offered in some (hidden) domain," the modal-possibility reading.
- **S5 axioms as processes (K$\Diamond$, T, 5)** — explicit process terms realizing the characteristic S5 axioms, relying on accessibility being reflexive, transitive, and symmetric.
- **Action at a distance (resolved)** — the original $\lambda 5$ had implicit, non-communicative effects at disjunction elimination; this system's explicit process-level communication for every domain move avoids that issue.

**Key Questions:**
1. Why does realizing the S5 "5" axiom specifically require accessibility to be an *equivalence* relation (not just reflexive/transitive), and where does that requirement show up in the process term for `5`?
2. How does encoding $\Box A$ as $\forall\alpha.@_\alpha A$ capture the intuition "usable in any (accessible) domain," and why is $\Diamond A$ dually existential rather than universal?

---
