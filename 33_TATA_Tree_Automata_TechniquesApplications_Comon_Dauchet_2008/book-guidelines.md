# Tree Automata Techniques and Applications — Guidelines

## Header

**Title:** Tree Automata Techniques and Applications (TATA)
**Author(s):** Hubert Comon, Max Dauchet, Rémi Gilleron, Florent Jacquemard, Denis Lugiez, Christof Löding, Sophie Tison, Marc Tommasi
**Publication:** Open-access monograph, 262 pp., version of November 18, 2008 (HAL id hal-03367725)

**Brief Summary:**
TATA is a comprehensive reference monograph on finite tree automata — the natural generalization of finite word automata to trees/terms. It develops the core theory of bottom-up and top-down tree automata over ranked trees (recognizability, closure, minimization, complexity), then extends it in several directions: automata on tuples of trees and their connection to weak monadic second-order logic (WSkS), automata with equality/disequality constraints for non-linear patterns, tree-set automata for set constraints, tree transducers, alternating tree automata, and finally automata for unranked trees (hedge automata) motivated by XML. Throughout, the guiding theme is that tree automata serve as a decision-procedure engine for logical theories and program-analysis problems over terms.

**Intent of the Author:**
The authors wrote TATA because, despite the field's liveness and many advances since Gécseg and Steinby's out-of-print monograph, there was no up-to-date single reference on finite tree automata. They aim to give a simple, constructive, algorithm-oriented presentation of the operational aspects of tree automata (deliberately excluding automata on infinite trees) that is useful both to newcomers (e.g. PhD students) and as a technical reference, showing how variations on the basic idea of tree automata solve difficult problems in rewriting, program verification, XML, and constraint solving.

---

## Topic List

1. **Terms, Trees, and Contexts** : [[Terms-Trees-and-Contexts|Link]]
   - Ranked alphabets and arity : [[Terms-Trees-and-Contexts|Link]]
   - Terms as ground or variable-containing expressions
   - Ordered ranked trees as partial functions on positions : [[Terms-Trees-and-Contexts|Link]]
   - Subterms, substitutions, and contexts : [[Terms-Trees-and-Contexts|Link]]
   - Term size and height

2. **Recognizable Tree Languages and Finite Tree Automata** : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]
   - Bottom-up nondeterministic finite tree automata
   - Runs, moves, and acceptance
   - Determinization by subset construction : [[Automata-for-Unranked-Trees|Link]]
   - Reduced and complete automata
   - Closure under union, intersection, and complementation : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link1]], [[Automata-with-Constraints|Link2]]
   - Tree homomorphisms and linearity : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]
   - The pumping lemma for tree languages : [[Context-Free-Tree-Languages|Link]]
   - Myhill-Nerode theorem and minimal tree automata : [[Alternating-Tree-Automata|Link1]], [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link2]]
   - Top-down tree automata and the determinism gap : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link1]], [[Applications-of-Tree-Automata-to-Term-Rewriting|Link2]]
   - Complexity of membership, emptiness, and inclusion

3. **Regular Tree Grammars and Expressions** : [[Regular-Tree-Grammars-and-Expressions|Link]]
   - Regular tree grammars and derivations : [[Regular-Tree-Grammars-and-Expressions|Link]]
   - Equivalence of regularity and recognizability : [[Regular-Tree-Grammars-and-Expressions|Link]]
   - Regular tree expressions and Kleene's theorem for trees : [[Regular-Tree-Grammars-and-Expressions|Link]]
   - Substitution and iteration through placeholder symbols
   - Regular equation systems and least fixed points : [[Regular-Tree-Grammars-and-Expressions|Link]]
   - Derivation trees of context-free word grammars : [[Context-Free-Tree-Languages|Link1]], [[Regular-Tree-Grammars-and-Expressions|Link2]]
   - The Yield operator and context-free word languages : [[Regular-Tree-Grammars-and-Expressions|Link]]
   - Local tree languages versus regular tree languages : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]

4. **Context-Free Tree Languages** : [[Context-Free-Tree-Languages|Link]]
   - Context-free tree grammars with argument-taking nonterminals : [[Context-Free-Tree-Languages|Link]]
   - The IO and OI derivation strategies
   - Non-linearity as the source of IO/OI divergence
   - Closure properties of IO tree languages : [[Context-Free-Tree-Languages|Link1]], [[Alternating-Tree-Automata|Link2]]

5. **Automata on Tuples of Trees** : [[Automata-on-Tuples-of-Trees|Link]]
   - Three notions of recognizability for relations : [[Regular-Tree-Grammars-and-Expressions|Link]]
   - The overlap coding of tuples into a single term
   - Ground Tree Transducers and shared-context relations : [[Automata-on-Tuples-of-Trees|Link]]
   - Closure under composition and transitive closure : [[Automata-on-Tuples-of-Trees|Link]]
   - Projection and cylindrification : [[Automata-on-Tuples-of-Trees|Link]]

6. **Weak Monadic Second-Order Logic and Tree Automata** : [[Weak-Monadic-Second-Order-Logic-and-Tree-Automata|Link]]
   - Syntax and semantics of WSkS : [[Weak-Monadic-Second-Order-Logic-and-Tree-Automata|Link]]
   - Coding finite sets of positions as trees : [[Weak-Monadic-Second-Order-Logic-and-Tree-Automata|Link]]
   - Definable sets equal recognizable sets
   - Decidability of WSkS
   - Non-elementary complexity of the decision procedure : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]

7. **Applications of Tree Automata to Term Rewriting** : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]
   - Order-sorted signatures as automata with subsort transitions : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]
   - Encompassment and the reducibility theory : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]
   - Ground reducibility : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]
   - Decidability of the first-order theory of a reduction relation : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]
   - Sequentiality and optimal reduction strategies : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]
   - Rigid E-unification : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]
   - Higher-order matching and 2-automata : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]

8. **Automata with Constraints** : [[Automata-with-Constraints|Link]]
   - Equality and disequality constraints between subtrees
   - Non-linear pattern recognition
   - Undecidability of emptiness for the general constrained class : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]
   - Automata with constraints between brothers : [[Automata-with-Constraints|Link1]], [[Tree-Set-Automata-and-Set-Constraints|Link2]]
   - Reduction automata and bounded equality depth : [[Automata-with-Constraints|Link1]], [[Applications-of-Tree-Automata-to-Term-Rewriting|Link2]]
   - Ground normal forms of term rewriting systems : [[Automata-with-Constraints|Link]]

9. **Tree Set Automata and Set Constraints** : [[Tree-Set-Automata-and-Set-Constraints|Link]]
   - Generalized tree sets as valuations into a finite set
   - Tree set automata and their acceptance via range conditions : [[Tree-Set-Automata-and-Set-Constraints|Link]]
   - Deterministic, strongly deterministic, and simple automata
   - Regular generalized tree sets
   - Emptiness and satisfiability of set constraint systems : [[Tree-Set-Automata-and-Set-Constraints|Link]]
   - Least solutions of positive set constraints : [[Tree-Set-Automata-and-Set-Constraints|Link]]

10. **Tree Transducers** : [[Tree-Transducers|Link]]
    - Rational word transducers and the bimorphism theorem
    - Bottom-up versus top-down tree transducers : [[Automata-on-Tuples-of-Trees|Link]]
    - Copy-then-process versus process-then-copy behavior
    - Linearity and determinism as sources of good closure properties : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]
    - The infinite hierarchy under transducer composition : [[Tree-Transducers|Link]]
    - Recognizability of transducer domains and images : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]
    - Tree bimorphisms and delabelings : [[Tree-Transducers|Link]]

11. **Alternating Tree Automata** : [[Alternating-Tree-Automata|Link]]
    - Positive Boolean transition formulas : [[Alternating-Tree-Automata|Link]]
    - Complementation without determinization
    - Equivalence to deterministic bottom-up automata : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]
    - Complexity of emptiness and membership
    - Correspondence with Horn clauses and definite set constraints : [[Tree-Set-Automata-and-Set-Constraints|Link]]
    - Two-way alternating tree automata : [[Alternating-Tree-Automata|Link]]
    - Two-way automata versus pushdown automata : [[Alternating-Tree-Automata|Link1]], [[XML-Schema-Formalisms|Link2]]

12. **Automata for Unranked Trees** : [[Automata-for-Unranked-Trees|Link]]
    - Unranked trees and hedges : [[Automata-for-Unranked-Trees|Link]]
    - Hedge automata with regular horizontal languages : [[Automata-for-Unranked-Trees|Link]]
    - Determinism and the subset construction for hedges : [[Automata-for-Unranked-Trees|Link]]
    - First-child-next-sibling and extension encodings into ranked trees : [[Automata-for-Unranked-Trees|Link]]
    - Weak monadic second-order logic over child and sibling relations : [[Weak-Monadic-Second-Order-Logic-and-Tree-Automata|Link]]
    - Representations of horizontal languages and their complexity
    - Minimization and the failure of the naive Myhill-Nerode congruence
    - Stepwise hedge automata and the @-congruence : [[Automata-for-Unranked-Trees|Link]]

13. **XML Schema Formalisms** : [[XML-Schema-Formalisms|Link]]
    - Document Type Definitions as local languages : [[XML-Schema-Formalisms|Link]]
    - Deterministic content models : [[XML-Schema-Formalisms|Link]]
    - Extended DTDs and typed alphabets
    - XML Schema and single-type extended DTDs : [[XML-Schema-Formalisms|Link]]
    - Relax NG as an unranked regular tree grammar : [[Regular-Tree-Grammars-and-Expressions|Link1]], [[Automata-for-Unranked-Trees|Link2]]
    - The interleave operator and its complexity cost

---

## Chapter Summaries

### Preliminaries (pp. 15–17)

**Summary:** Fixes the book's vocabulary for terms and trees: ranked alphabets, the term set $T(F,X)$, ordered ranked trees as partial functions on positions, subterms, substitutions, and contexts.

**Key Definitions & Concepts:**
- **Ranked alphabet** — a pair $(F,\mathrm{Arity})$; $F_p$ is the set of symbols of arity $p$; arity-0 symbols are constants.
- **Term** $t\in T(F,X)$ — smallest set containing $F_0$, $X$, and closed under $f(t_1,\dots,t_p)$ for $f\in F_p$; **linear** term has each variable at most once.
- **Tree as partial function** — $t:\mathrm{Pos}(t)\subseteq\mathbb{N}^*\to F\cup X$, $\mathrm{Pos}(t)$ prefix-closed, with out-degree at each position matching the label's arity.
- **Subterm** $t|_p$, replacement $t[u]_p$, subterm ordering $\trianglelefteq$.
- **Size** $\|t\|$ and **height** $\mathrm{Height}(t)$, defined inductively on term structure.
- **Substitution** $\sigma: X\to T(F,X)$, extended homomorphically; postfix notation $t\sigma$.
- **Context** — a linear term $C\in T(F,X_n)$; $C[t_1,\dots,t_n]$ is $C$ with $x_i$ replaced by $t_i$.

**Key Questions:**
1. Why must a context be required to be *linear* for $C[t_1,\dots,t_n]$ to unambiguously mean "plug $t_i$ in at the $i$-th designated hole," and what would go wrong with a non-linear context?
2. How does treating a word over a finite alphabet as a unary term make tree automata theory a strict generalization of word automata theory?

---

### Chapter 1: Recognizable Tree Languages and Finite Tree Automata (pp. 19–49)

**Summary:** This chapter develops the fundamental theory of tree automata operating on ground terms over a ranked alphabet $F$, defining recognizable tree languages as the natural generalization of regular word languages, and establishes their basic structural results (determinization, closure properties, minimization, top-down automata, decidability/complexity of core decision problems). : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]

**Key Definitions & Concepts by Section:**
- **1.1 Finite Tree Automata** — NFTA $A=(Q,F,Q_f,\Delta)$ with rules $f(q_1(x_1),\dots,q_n(x_n))\to q(f(x_1,\dots,x_n))$; move relation $\to_A$; a term is accepted if it rewrites to some $q(t)$, $q\in Q_f$; $L(A)$ recognizable; $\epsilon$-rules eliminable without loss of power; deterministic (DFTA), complete, and reduced automata; determinization (subset construction, Theorem 1.1.9) can blow up exponentially; complete DFTA $\equiv$ finite $F$-algebra. : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]
- **1.2 Pumping Lemma** — every recognizable $L$ has a bound $k$ such that any accepted term taller than $k$ decomposes as $C[C'[u]]$, pumpable at $C'$; used to prove non-recognizability; corollaries bound emptiness/infiniteness witnesses by $|Q|$. : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]
- **1.3 Closure Properties** — recognizable languages closed under union, intersection (product automaton), and complementation (via complete DFTA). : [[Alternating-Tree-Automata|Link1]], [[Automata-on-Tuples-of-Trees|Link2]], [[Context-Free-Tree-Languages|Link3]], [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link4]]
- **1.4 Tree Homomorphisms** — $h_F(f)=t_f$ extended homomorphically; **linear** homomorphisms preserve recognizability under direct image (Theorem 1.4.3); any homomorphism preserves recognizability under *inverse* image (Theorem 1.4.4); non-linear direct images can destroy recognizability. : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link1]], [[Tree-Transducers|Link2]]
- **1.5 Minimizing Tree Automata** — congruence on $T(F)$ of finite index; **Myhill-Nerode theorem for trees**: $L$ recognizable iff $\equiv_L$ has finite index; unique minimal DFTA up to renaming. : [[Alternating-Tree-Automata|Link1]], [[Applications-of-Tree-Automata-to-Term-Rewriting|Link2]], [[Automata-for-Unranked-Trees|Link3]], [[Automata-on-Tuples-of-Trees|Link4]]
- **1.6 Top-Down Tree Automata** — top-down NFTA equi-expressive with bottom-up NFTA, but top-down **DFTA are strictly weaker** (Proposition 1.6.2: $\{f(a,b),f(b,a)\}$ has no top-down DFTA) — deterministic top-down automata express only *path-closed* properties. : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link1]], [[Alternating-Tree-Automata|Link2]]
- **1.7 Decision Problems and Complexity** — membership linear/polynomial; emptiness linear time, P-complete; intersection non-emptiness of $n$ automata EXPTIME-complete; universality (complement emptiness) EXPTIME-complete for NFTA, polynomial for complete DFTA; inclusion/equivalence EXPTIME-complete for NFTA. : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]

**Key Questions:**
1. Why does nondeterminism cost nothing (via subset construction) for *bottom-up* tree automata, yet strictly reduce expressive power for *top-down* tree automata?
2. Trace exactly where the proof that linear homomorphisms preserve recognizability under direct image breaks down for non-linear homomorphisms. What does this say about duplication versus recognizability generally?
3. The pumping lemma pumps a unary context nested along a single path. Why is this sufficient to certify non-recognizability of languages defined by matching or counting properties?

---

### Chapter 2: Regular Grammars and Regular Expressions (pp. 51–71)

**Summary:** This chapter takes the generative dual view of Chapter 1's acceptor view: it introduces regular tree grammars, proves regularity = recognizability, develops a Kleene-style regular-expression calculus and least-fixed-point equation systems for tree languages, relates regular tree languages to context-free word languages via derivation trees and the Yield operator, and closes with the strictly more powerful class of context-free tree languages and the IO/OI evaluation-order distinction. : [[Regular-Tree-Grammars-and-Expressions|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 Tree Grammar** — $G=(S,N,F,R)$; **regular tree grammar** restricts nonterminals to arity 0; derivation $\to_G$, $L(G)$; reduced and normalized grammars ($A\to f(A_1,\dots,A_n)$ or $A\to a$); Theorem 2.1.5: regular $\iff$ recognizable, via normalized-grammar/top-down-automaton correspondence. : [[Context-Free-Tree-Languages|Link1]], [[Regular-Tree-Grammars-and-Expressions|Link2]]
- **2.2 Regular Expressions, Kleene's Theorem** — placeholder constants $K=\{\square_1,\dots\}$; substitution and closure ($L^{*,\square}$) of tree languages; **Kleene's theorem for trees** (Theorem 2.2.8): recognizable iff denotable by a regular tree expression. : [[Regular-Tree-Grammars-and-Expressions|Link]]
- **2.3 Regular Equations** — regular equation systems $X_i=s_{i1}+\dots+s_{im_i}$; least fixed point of a continuous operator $TS$ (Knaster–Tarski) yields regular tree languages; converse also holds. : [[Regular-Tree-Grammars-and-Expressions|Link]]
- **2.4 Context-Free Word Languages and Regular Tree Languages** — $\mathrm{Yield}$ operator reads leaves left to right; derivation trees of a CF word grammar form a regular tree language, and $\mathrm{Yield}$ of a regular tree language is context-free; but derivation-tree languages (**local tree languages**) are a *strict* subclass of regular tree languages, related by an alphabetic homomorphism. : [[Context-Free-Tree-Languages|Link1]], [[Regular-Tree-Grammars-and-Expressions|Link2]]
- **2.5 Context-free Tree Languages** — nonterminals of positive arity taking arguments; **IO** (innermost-outermost, call-by-value) vs **OI** (outermost-innermost, call-by-name) derivation strategies; Theorem 2.5.3: $L(\text{IO-}G)\subseteq L(\text{OI-}G)$, strict in general, coinciding exactly when the grammar is linear. : [[Context-Free-Tree-Languages|Link]]

**Key Questions:**
1. Why does an alphabetic homomorphism suffice to recover full regularity from local (derivation-tree) languages, and what precisely is missing from local languages that a term like $s(g(a),g(b))$ exposes?
2. Why does the IO/OI distinction disappear exactly when a grammar's rules are linear, and how does this connect to why linear tree homomorphisms preserve recognizability under direct image but non-linear ones don't (Chapter 1)?

---

### Chapter 3: Logic, Automata and Relations (pp. 73–111)

**Summary:** This chapter extends tree automata theory from single terms to tuples of terms/relations, develops three notions of recognizability for relations, the weak monadic second-order logic WSkS, the Thatcher–Wright correspondence "definable = recognizable," and surveys applications (sorts, encompassment/reducibility, ground rewriting theories, reduction strategies, rigid E-unification, higher-order matching) — establishing tree automata as a general decision-procedure engine for logical theories over trees. : [[Alternating-Tree-Automata|Link1]], [[Weak-Monadic-Second-Order-Logic-and-Tree-Automata|Link2]]

**Key Definitions & Concepts by Section:**
- **3.2 Automata on Tuples of Finite Trees** — three notions: $\mathrm{Rec}^\times$ (finite unions of products of recognizable sets), $\mathrm{Rec}$ (via overlap-coding tuples into one term over a padded alphabet), and **GTT** (Ground Tree Transducers: a pair of bottom-up automata sharing synchronization states); strict inclusions $\mathrm{Rec}^\times\subset\mathrm{Rec}$, $\mathrm{GTT}\subset\mathrm{Rec}$, with GTT and $\mathrm{Rec}^\times$ incomparable; closure under Boolean operations, projection, cylindrification; **Theorem 3.2.14**: GTT relations closed under transitive closure and composition (unlike plain Rec). : [[Automata-on-Tuples-of-Trees|Link]]
- **3.3 The Logic WSkS** — terms over successor symbols $1,\dots,k$; atomic formulas $s=t$, $s\le t$, $t\in X$; **Lemma 3.3.4 / 3.3.6**: definable sets = recognizable sets (Thatcher–Wright, Theorem 3.3.8: WSkS decidable); complexity is a tower of exponentials in the quantifier alternation depth, non-elementary even for $k=1$.
- **3.4 Examples of Applications** — order-sorted signatures as automata with subsort $\epsilon$-transitions; **encompassment** $t\!\cdot\!\!\preceq u$ and the reducibility theory (decidable for linear terms via Prop 3.4.3); ground reducibility; decidability of the first-order theory of $\xrightarrow{*}_R$ when rules share no variables (via GTT, Prop 3.4.7); **sequentiality** and optimal reduction strategies (Huet–Lévy theory), decidable when the relevant predicate is WSkS-definable; simultaneous rigid $E$-unification with one variable is EXPTIME-complete via NFTA-recognizable solution sets; higher-order matching via **2-automata** (a hole symbol fillable by different terms per occurrence).

**Key Questions:**
1. Why does the second notion of recognizability (Rec) fail to be closed under transitive closure, and what does GTT buy that Rec cannot?
2. Trace how the completeness direction of the Thatcher–Wright correspondence encodes an existential second-order quantifier as "guessing an accepting run" via a state partition.
3. Why is GTT's closure under composition and iteration essential specifically when rewrite rules share no variables — and why does dropping that restriction motivate Chapter 4's constrained automata?

---

### Chapter 4: Automata with Constraints (pp. 113–135)

**Summary:** Ordinary tree automata cannot recognize non-linear patterns like $\{f(t,t)\mid t\in T(F)\}$ because sibling subtrees are processed independently. This chapter extends bottom-up automata with equality/disequality tests between subtree positions to handle non-linear rewriting, sorts, and reducibility, then carves out decidable subclasses since the fully general class has undecidable emptiness. : [[Automata-with-Constraints|Link]]

**Key Definitions & Concepts by Section:**
- **4.2 Automata with Equality and Disequality Constraints (AWEDC)** — rules $f(q_1,\dots,q_n)\xrightarrow{c}q$ with $c$ a Boolean combination of position (dis)equalities; completable and determinizable (exponential blowup) and closed under all Boolean operations; **Theorem 4.2.10**: emptiness is **undecidable** (reduction from Post Correspondence Problem). : [[Tree-Set-Automata-and-Set-Constraints|Link1]], [[Automata-with-Constraints|Link2]]
- **4.3 Automata with Constraints Between Brothers (AWCBB)** — constraints restricted to sibling positions; closed under Boolean operations; **Theorem 4.3.5**: emptiness decidable in polynomial time for deterministic AWCBB (bounding witnesses per state by $\mathrm{maxar}(F)$); **Theorem 4.3.6**: EXPTIME-complete for nondeterministic AWCBB. : [[Automata-with-Constraints|Link1]], [[Tree-Set-Automata-and-Set-Constraints|Link2]]
- **4.4 Reduction Automata** — states ordered so equality-constrained rules strictly increase order (bounding equality checks per branch, disequalities unrestricted); **Theorem 4.4.5**: emptiness decidable for complete deterministic reduction automata (pumping argument with "close" vs "remote" equalities); **Theorem 4.4.7**: emptiness undecidable for nondeterministic reduction automata (2-counter machine encoding) — hence reduction automata **cannot be determinized** (Corollary 4.4.8); ground normal forms of any TRS are recognized by a reduction automaton (Prop 4.4.10); full reducibility theory decidable for arbitrary (non-linear) terms. : [[Automata-with-Constraints|Link]]
- **4.5 Other Decidable Subclasses** — disequality-only AWEDC decidable in DEXPTIME; generalized reduction automata combining AWCBB-style sibling constraints with the reduction ordering, the largest known decidable subclass. : [[Automata-with-Constraints|Link]]

**Key Questions:**
1. What structural property of reduction automata makes determinization impossible, and how does the 2-counter-machine encoding exploit exactly this gap?
2. Trace why the bound of $\mathrm{maxar}(F)$ witnesses per state (Lemma 4.3.4) depends on determinism, and how its failure for the nondeterministic case forces an EXPTIME rather than PTIME result.
3. Compare the GTT-based decidability of rewriting theories under "no shared variables" (Chapter 3) with the reduction-automaton-based decidability of ground reducibility. Why can't either mechanism simply substitute for the other?

---

### Chapter 5: Tree Set Automata (pp. 137–158)

**Summary:** Chapter 5 introduces Generalized Tree Set Automata (GTSA), an acceptor model for mappings from ground terms into a finite label set, built to give an automata-theoretic decision procedure for systems of set constraints — a formalism used in program type inference / set-based analysis. : [[Tree-Set-Automata-and-Set-Constraints|Link]]

**Key Definitions & Concepts by Section:**
- **5.2 Definitions and Examples** — a **generalized tree set (GTS)** is a mapping $g:T(F)\to E$; a **GTSA** $\mathcal{A}=(Q,\Delta,\Omega)$ accepts $g$ if some run's *range* lies in $\Omega\subseteq 2^Q$; **deterministic**, **strongly deterministic**, **complete**, and **simple** (subset-closed $\Omega$) variants; GTSA-recognizable tuples need not be regular; **regular GTS** defined via a context-closed classifier; the three classes $\mathcal{R}_{GTS}\supsetneq\mathcal{R}_{DGTS},\mathcal{R}_{SGTS}$ are pairwise distinct.
- **5.3 Closure and Decision Properties** — closed under union/intersection/projection/cylindrification; **not** closed under complementation in general, and non-determinism cannot be reduced; **Theorem 5.3.7 / Proposition 5.3.9**: emptiness decidable, NP-complete for simple GTSA (via a polynomial witness-size bound); inclusion, equivalence, singleton-ness, and fixed-cardinality properties decidable for deterministic GTSA. : [[Alternating-Tree-Automata|Link1]], [[Automata-on-Tuples-of-Trees|Link2]], [[Context-Free-Tree-Languages|Link3]], [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link4]]
- **5.4 Applications to Set Constraints** — set expressions over $\top,\bot,\sim,\cup,\cap$; **Proposition 5.4.1**: any system of $n$ set constraints has a deterministic (simple, if positive-only) GTSA whose language is exactly its solution set; consequences: satisfiability, existence of a regular solution, inclusion, unicity, and least-solution existence for positive systems are all decidable. : [[Terms-Trees-and-Contexts|Link1]], [[Tree-Set-Automata-and-Set-Constraints|Link2]], [[Automata-with-Constraints|Link3]]

**Key Questions:**
1. Why does the "simple" restriction on $\Omega$ prevent a GTSA from expressing non-emptiness-type properties, and how does this explain why simple GTSA correspond to *positive* set constraints while general GTSA are needed for negation?
2. Why is Proposition 5.2.7 (a non-empty recognizable set contains a regular member) enough to get decidability results without reasoning about non-regular members directly?
3. How does the failure of GTSA closure under complementation block a naive automata-based decision procedure for negative set constraints, and how does Proposition 5.4.1 work around it?

---

### Chapter 6: Tree Transducers (pp. 161–181)

**Summary:** Chapter 6 introduces tree transducers as the generalization of finite-state string transducers to trees, motivated by syntax-directed translation. It reviews the well-behaved word case (rational transducers, Nivat's bimorphism theorem), then shows the tree case is considerably messier: bottom-up and top-down tree transducers are structurally incomparable, general classes are not closed under composition, and copying interacts with nondeterminism to create a genuine infinite hierarchy. : [[Tree-Transducers|Link]]

**Key Definitions & Concepts by Section:**
- **6.2 The Word Case** — rational transducers, closure under union/composition but not intersection; **Theorem 6.2.4 (Nivat's Bimorphism Theorem)**: rational transducers and bimorphisms $(\Phi,L,\Psi)$ define the same relations. : [[Terms-Trees-and-Contexts|Link1]], [[Tree-Transducers|Link2]]
- **6.3 Introduction to Tree Transducers** — compiler-pass example illustrating bottom-up transducers computing synthesized attributes and top-down transducers computing inherited attributes; a homomorphism is a one-state transducer viewable both ways. : [[Tree-Transducers|Link1]], [[Automata-on-Tuples-of-Trees|Link2]]
- **6.4 Properties of Tree Transducers** — bottom-up (NUTT) and top-down (NDTT) transducers, with auxiliary properties linear/complete/deterministic/$\epsilon$-free; **Theorem 6.4.3 (Comparison Theorem)**: NUTT and NDTT are incomparable in general, coincide under linearity; bottom-up transducers exhibit "process-then-copy," top-down exhibit "copy-then-process"; **Theorem 6.4.4 (Hierarchy Theorem)**: composing NUTT yields a genuinely infinite hierarchy; **Theorem 6.4.5 (Composition Theorem)**: the hierarchy collapses under linearity or determinism; **Theorem 6.4.6**: transducer domains are always recognizable, and images under linear transducers are recognizable; emptiness PTIME-complete (bottom-up) vs DEXPTIME-complete (top-down); equivalence decidable for deterministic transducers. : [[Tree-Transducers|Link]]
- **6.5 Homomorphisms and Tree Transducers** — **Theorem 6.5.1**: bottom-up transductions $\equiv$ bimorphisms with a delabeling left component; Nivat's clean symmetry is lost for trees (non-linearity permits copy-and-process but not equality checking); **Theorem 6.5.2**: strict-then-collapsing composition hierarchies for restricted bimorphism classes (LCFB, LB). : [[Tree-Transducers|Link1]], [[Automata-on-Tuples-of-Trees|Link2]], [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link3]]

**Key Questions:**
1. Why does the copy-before/after-processing ordering difference between bottom-up and top-down transducers make the two classes structurally incomparable, and why does linearity erase the distinction?
2. What is it about non-linearity and non-determinism *jointly* that drives the infinite composition hierarchy, and why do practical compiler-style transducers typically avoid triggering it?
3. Precisely which symmetry of Nivat's Bimorphism Theorem is lost when moving to trees, and how does the LCFB/LB hierarchy result illustrate this?

---

### Chapter 7: Alternating Tree Automata (pp. 183–196)

**Summary:** This chapter introduces alternating tree automata, which generalize nondeterministic tree automata by allowing both conjunctions and disjunctions in transition right-hand sides. This restores a symmetry that makes complementation trivial (no determinization needed), at the cost of harder decision problems; the chapter also connects automata to Horn logic, set constraints, and two-way automata. : [[Alternating-Tree-Automata|Link]]

**Key Definitions & Concepts by Section:**
- **7.2 Definitions and Examples** — alternating word automata with transitions $Q\times A\to\mathcal{B}^+(Q)$ (positive Boolean formulas); alternating tree automata $\Delta:Q\times F\to\mathcal{B}^+(Q\times\mathbb{N})$, top-down formulation; runs as trees over $Q\times\mathbb{N}^*$ satisfying the transition formula at each node; nondeterministic automata are the disjunction-only special case.
- **7.3 Closure Properties** — union, intersection, and **complementation all in linear time**, complementation via the dual automaton (swap $\land/\lor$, true/false). : [[Alternating-Tree-Automata|Link1]], [[Automata-on-Tuples-of-Trees|Link2]], [[Context-Free-Tree-Languages|Link3]], [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link4]]
- **7.4 From Alternating to Deterministic Automata** — **Theorem 7.4.1**: alternating automata have exactly the power of deterministic bottom-up automata, but conversion costs deterministic exponential time, unavoidably. : [[Alternating-Tree-Automata|Link]]
- **7.5 Decision Problems** — **Theorem 7.5.1**: emptiness and universality DEXPTIME-complete; membership PTIME. : [[Alternating-Tree-Automata|Link1]], [[Automata-for-Unranked-Trees|Link2]], [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link3]]
- **7.6 Horn Logic, Set Constraints, Two-Way Automata** — states as unary predicates, transitions as Horn clauses; alternation corresponds to variable-sharing in clause bodies; equivalence with definite set constraint formalisms; **two-way alternating tree automata** (push/pop/intersection clauses) do not increase expressive power beyond ordinary automata (Theorem 7.6.3), though conversion is exponential; two-way automata remain strictly weaker than pushdown automata despite superficial similarity.
- **7.7 Application** — modeling the Dolev-Yao intruder in cryptographic protocol analysis with two-way automata.

**Key Questions:**
1. Why does adding conjunction make complementation free (linear time) while nondeterministic-automaton complementation requires exponential determinization, without contradicting that alternating and nondeterministic automata have the same expressive power?
2. In what precise sense do two-way alternating tree automata not increase expressive power, and why do pushdown automata — built from a superficially similar push/pop encoding — recognize a strictly larger class?
3. Where exactly does the DNF-based translation between alternating automata, Horn clauses, and definite set constraints break down, requiring two-way automata when right-hand sides are non-variable terms?

---

### Chapter 8: Automata for Unranked Trees (pp. 199–242)

**Summary:** This chapter develops automata theory for finite ordered trees with unbounded, label-independent branching (unranked trees/hedges), the natural model for XML documents. It centers on the hedge automaton model, relates it to ranked tree automata via two encodings, and studies logic, decision complexity, minimization, and practical XML schema formalisms through this lens. : [[Automata-for-Unranked-Trees|Link]]

**Key Definitions & Concepts by Section:**
- **8.2 Definitions and Examples** — unranked trees and hedges (sequences of trees); **NFHA** with transitions $a(R)\to q$, $R$ a regular "horizontal" language over states; **Theorem 8.2.8**: every NFHA has an equivalent DFHA via subset construction (exponential).
- **8.3 Encodings and Closure Properties** — **first-child-next-sibling (FCNS)** encoding into binary ranked trees (a bijection on hedges); **extension operator** $@$ and its encoding (a bijection on trees, Theorem 8.3.7: hedge recognizable iff extension-image recognizable); closure under union, intersection, complementation, projection, inverse projection. : [[Alternating-Tree-Automata|Link1]], [[Automata-on-Tuples-of-Trees|Link2]], [[Context-Free-Tree-Languages|Link3]], [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link4]]
- **8.4 Weak Monadic Second Order Logic** — signature with $\mathrm{child}(x,y)$ and $\mathrm{next\text{-}sibling}(x,y)$ replacing direct successor; **Theorem 8.4.2**: WMSO-definable iff recognizable. : [[Weak-Monadic-Second-Order-Logic-and-Tree-Automata|Link]]
- **8.5 Decision Problems and Complexity** — horizontal languages represented as NFA, AFA (alternating), or $RE_\Vert$ (with shuffle); uniform membership PTIME for NFHA(NFA)/DFHA(AFA), NP-complete for NFHA(AFA)/NFHA($RE_\Vert$); emptiness PTIME except PSPACE-complete for NFHA(AFA); inclusion ranges from PTIME (DFHA(DFA)) to EXPTIME-complete (NFHA(NFA)). : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]
- **8.6 Minimization** — the naive $\equiv_L$ congruence fails to characterize recognizability (Example 8.6.2); no unique minimal DFHA when horizontal-language size is counted (Example 8.6.3); **stepwise hedge automata (DSHA)**, reading children one state at a time, restore a genuine Myhill-Nerode-style characterization via the **@-congruence** (Theorem 8.6.9) and a unique minimal automaton (Theorem 8.6.8).
- **8.7 XML Schema Languages** — **DTDs** as local languages, a strict subclass of recognizable languages; **deterministic (1-unambiguous) content models**; **extended DTDs (EDTDs)** with typed alphabets capture full hedge-automaton expressiveness; **XML Schema** as single-type deterministic EDTDs; **Relax NG** as an essentially unrestricted regular tree grammar over hedges, supporting the interleave/shuffle operator at the cost of NP-complete membership. : [[XML-Schema-Formalisms|Link]]

**Key Questions:**
1. Why does the naive $\equiv_L$ congruence fail to characterize recognizability for unranked trees, while the @-congruence succeeds — what does this reveal about where a hedge automaton's real state information lives?
2. Why does the stepwise automaton model restore a unique minimal representation where plain DFHA(DFA) minimization does not?
3. Theorem 8.5.6 shows uniform membership is PTIME for DFHA(AFA) but NP-complete for NFHA(AFA), with no polynomial translation to alternating tree automata on encodings (Corollary 8.5.7). Where exactly does the general "transfer via encoding" strategy of this chapter break down, and why?
