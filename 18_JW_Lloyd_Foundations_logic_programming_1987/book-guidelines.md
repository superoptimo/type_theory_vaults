# Foundations of Logic Programming — Guidelines

## Header

**Title:** Foundations of Logic Programming (2nd Edition)
**Author(s):** John Wylie Lloyd
**Publication:** Springer-Verlag, 1987 (1st edition 1984)

**Brief Summary:**
This book gives a rigorous, self-contained mathematical account of the theoretical foundations of logic programming and PROLOG. Starting from first-order logic, unification and fixpoint theory, it builds up the declarative and procedural (SLD-resolution) semantics of definite programs, proves their soundness and completeness, and then extends the theory in successive chapters to negation (the closed world assumption, negation as failure, program completion, SLDNF-resolution), to programs and goals with arbitrary first-order-formula bodies, to declarative error diagnosis, to deductive database systems (typed logic, query evaluation, integrity constraints), and finally to a semantics for non-terminating "perpetual processes." Throughout, the organizing idea is the sharp separation of declarative meaning (models, logical consequence, correct answers) from procedural mechanism (SLD/SLDNF-resolution), with soundness and completeness theorems relating the two.

**Intent of the Author:**
Lloyd set out to give PROLOG programmers and researchers "what every PROLOG programmer should know" — proofs of essentially all the results needed to understand logic programming as an instance of first-order logic — while candidly flagging the more speculative material (concurrent/perpetual processes) as an area still under development.

---

## Topic List

1. **First-Order Logic as a Foundation for Logic Programming** : [[First-Order-Logic-as-a-Foundation-for-Logic-Programming|Link]]
   - Alphabets, terms, and well-formed formulas : [[First-Order-Logic-as-a-Foundation-for-Logic-Programming|Link]]
   - Clausal form and clausal notation : [[First-Order-Logic-as-a-Foundation-for-Logic-Programming|Link]]
   - Interpretations, models, and logical consequence : [[First-Order-Logic-as-a-Foundation-for-Logic-Programming|Link]]
   - Herbrand universes, Herbrand bases, and Herbrand interpretations
   - Prenex conjunctive normal form
   - Typed (many-sorted) first-order theories : [[First-Order-Logic-as-a-Foundation-for-Logic-Programming|Link]]
2. **Unification** : [[Unification|Link]]
   - Substitutions and instances : [[Unification|Link]]
   - Composition of substitutions
   - Variants and renaming substitutions
   - Most general unifiers : [[Unification|Link]]
   - The unification algorithm and the occur check : [[Unification|Link]]
   - Worst-case exponential behaviour of unification
3. **Fixpoint Theory** : [[Fixpoint-Theory|Link]]
   - Partial orders and complete lattices
   - Monotonic and continuous mappings : [[Fixpoint-Theory|Link]]
   - Least and greatest fixpoints (Knaster–Tarski theorem)
   - Ordinal powers of a mapping
   - Kleene's characterisation of least fixpoints for continuous mappings
4. **Declarative Semantics of Definite Programs** : [[Declarative-Semantics-of-Definite-Programs|Link]]
   - Definite program clauses, definite programs, and definite goals
   - The least Herbrand model and the model intersection property : [[Declarative-Semantics-of-Definite-Programs|Link]]
   - The immediate consequence operator $T_P$ : [[Declarative-Semantics-of-Definite-Programs|Link]]
   - Fixpoint characterisation of the least Herbrand model : [[Declarative-Semantics-of-Definite-Programs|Link]]
   - Correct answers : [[Declarative-Semantics-of-Definite-Programs|Link]]
5. **SLD-Resolution** : [[SLD-Resolution|Link]]
   - Resolvents, SLD-derivations, and SLD-refutations : [[SLD-Resolution|Link]]
   - Computed answers : [[SLD-Resolution|Link]]
   - Soundness of SLD-resolution : [[SLD-Resolution|Link]]
   - The mgu lemma and the lifting lemma
   - Completeness of SLD-resolution : [[SLD-Resolution|Link1]], [[Negation-in-Logic-Programs|Link2]]
   - Independence of the computation rule and the switching lemma : [[SLD-Resolution|Link]]
   - SLD-trees, search rules, and fairness
   - Depth-first search and incompleteness in practical PROLOG systems
   - Coroutining and automatic control generation
   - The cut control facility and safe versus unsafe cuts
6. **Computational Adequacy of Logic Programs** : [[Computational-Adequacy-of-Logic-Programs|Link]]
   - Encoding partial recursive functions as definite programs : [[Declarative-Semantics-of-Definite-Programs|Link]]
   - Composition, primitive recursion, and minimalisation as program schemas
7. **The Occur Check Problem** : [[The-Occur-Check-Problem|Link]]
   - Unsoundness of unification without the occur check : [[Integrity-Constraint-Checking|Link]]
   - Difference lists and circular bindings : [[The-Occur-Check-Problem|Link]]
   - Programming methodologies to contain occur-check errors
8. **Negation in Logic Programs** : [[Negation-in-Logic-Programs|Link]]
   - The closed world assumption
   - Non-monotonic inference rules : [[Negation-in-Logic-Programs|Link]]
   - The SLD finite failure set and its characterisations
   - Fair derivations and fair SLD-trees
   - The negation as failure rule : [[Negation-in-Logic-Programs|Link]]
   - Program completion and the equality theory : [[Negation-in-Logic-Programs|Link]]
   - Normal programs, normal goals, and program clauses with negative literals
   - Hierarchical and stratified programs
   - SLDNF-resolution and the safeness condition on literal selection
   - Floundering and the allowedness condition
   - Soundness and completeness of the negation as failure rule : [[Semantics-of-Perpetual-Processes|Link]]
   - Soundness and completeness of SLDNF-resolution for hierarchical programs : [[Negation-in-Logic-Programs|Link]]
   - Effect of cut on soundness in normal programs
9. **Programs and Goals with Arbitrary First-Order Bodies** : [[Programs-and-Goals-with-Arbitrary-First-Order-Bodies|Link]]
   - Program statements with arbitrary formula bodies : [[Programs-and-Goals-with-Arbitrary-First-Order-Bodies|Link]]
   - Completion of a program : [[Negation-in-Logic-Programs|Link1]], [[Programs-and-Goals-with-Arbitrary-First-Order-Bodies|Link2]]
   - Transformation of a program into normal form : [[Programs-and-Goals-with-Arbitrary-First-Order-Bodies|Link]]
   - Soundness and completeness of the negation as failure rule and SLDNF-resolution for programs
10. **Declarative Error Diagnosis** : [[Declarative-Error-Diagnosis|Link]]
    - Intended interpretations and program correctness : [[First-Order-Logic-as-a-Foundation-for-Logic-Programming|Link]]
    - Uncovered atoms and incorrect statement instances
    - The declarative error diagnoser (wrong and missing predicates) : [[Declarative-Error-Diagnosis|Link]]
    - The top-down version of the diagnoser and its use of an oracle
    - Comparison with single-stepping and divide-and-query algorithms
    - Soundness and completeness of the error diagnoser : [[Declarative-Error-Diagnosis|Link1]], [[Semantics-of-Perpetual-Processes|Link2]]
11. **Deductive Database Theory** : [[Deductive-Database-Theory|Link]]
    - Database statements, databases, and queries
    - Typed first-order theories for database semantics
    - Integrity constraints and the model-theoretic versus proof-theoretic view : [[Deductive-Database-Theory|Link]]
    - Hierarchical and stratified databases : [[Negation-in-Logic-Programs|Link]]
    - Transformation of typed formulas into type-free form
    - Soundness and completeness of query evaluation : [[Deductive-Database-Theory|Link]]
    - Domain closure axioms : [[Deductive-Database-Theory|Link]]
12. **Integrity Constraint Checking** : [[Integrity-Constraint-Checking|Link]]
    - Transactions as sequences of additions and deletions
    - The simplification theorem for integrity constraint checking : [[Integrity-Constraint-Checking|Link]]
    - Computing the atom sets that capture model differences
    - Stopping rules for practical implementation
13. **Semantics of Perpetual Processes** : [[Semantics-of-Perpetual-Processes|Link]]
    - Possibly-infinite terms and atoms as labelled trees : [[Semantics-of-Perpetual-Processes|Link]]
    - The complete Herbrand universe and complete Herbrand base : [[First-Order-Logic-as-a-Foundation-for-Logic-Programming|Link]]
    - Compactness under the ultrametric on terms
    - The mapping $T'_P$ on complete Herbrand interpretations
    - Closedness and weak continuity of $T'_P$
    - Atoms computable at infinity : [[Semantics-of-Perpetual-Processes|Link]]
    - Soundness of SLD-resolution for perpetual processes : [[Semantics-of-Perpetual-Processes|Link1]], [[SLD-Resolution|Link2]]

---

## Chapter Summaries

### Chapter 1: Preliminaries (pp. 1–34)

**Summary:** This chapter lays the first-order-logic groundwork the rest of the book depends on: the syntax of alphabets, terms and formulas (including the clausal notation used throughout for program clauses and goals), the semantics of interpretations and models with special emphasis on Herbrand interpretations, the unification algorithm used to compute variable bindings, and the fixpoint theory (complete lattices, monotonic/continuous mappings, ordinal powers) that will characterise the meaning of a logic program in chapter 2.

**Key Definitions & Concepts by Section:**
- **§1 Introduction** — logic programming (Kowalski, Colmerauer, 1972), the logic/control split, "system" vs. "application" languages, the process and database interpretations of logic.
- **§2 First Order Theories** — alphabet, term, (well-formed) formula, first order language, bound/free occurrence, closed formula, universal/existential closure $V(F)$/$\exists(F)$, positive/negative occurrence of an atom, literal, clause, clausal notation $A_1,\ldots,A_k \leftarrow B_1,\ldots,B_n$, definite program clause, unit clause, definite program, definite goal, empty clause $\square$, Horn clause, typed (many-sorted) first order theory.
- **§3 Interpretations and Models** — pre-interpretation, interpretation, variable assignment, term assignment, model, consistent theory, logical consequence (Proposition 3.1: $F$ is a logical consequence of $S$ iff $S \cup \{\lnot F\}$ is unsatisfiable), ground term/atom, Herbrand universe $U_L$, Herbrand base $B_L$, Herbrand interpretation, Herbrand model (Propositions 3.2–3.3: unsatisfiability can be checked via Herbrand models alone, for sets of clauses), prenex conjunctive normal form, logically equivalent formulas.
- **§4 Unification** — substitution, ground/variable-pure substitution, instance of an expression, composition of substitutions, identity substitution $\varepsilon$, variant, renaming substitution, unifier, most general unifier (mgu), disagreement set, the unification algorithm, the occur check, the Unification Theorem (4.3).
- **§5 Fixpoints** — relation, partial order, upper/lower bound, least upper bound/greatest lower bound, complete lattice, monotonic mapping, directed set, continuous mapping, least/greatest fixpoint, the Knaster–Tarski fixpoint theorem (Proposition 5.1), ordinal powers $T{\uparrow}\alpha$ and $T{\downarrow}\alpha$, closure ordinal, Kleene's theorem that $\mathrm{lfp}(T)=T{\uparrow}\omega$ for continuous $T$ (Proposition 5.4).

**Key Questions:**
1. Why must unsatisfiability proofs for sets of *clauses* be reducible to Herbrand interpretations, and why does this reduction fail for arbitrary closed formulas?
2. What is the difference between a monotonic and a continuous mapping on a complete lattice, and why does Kleene's theorem require continuity rather than mere monotonicity to guarantee $\mathrm{lfp}(T)=T{\uparrow}\omega$?
3. Why is the unification algorithm inherently worst-case exponential when it must explicitly print an mgu, and what design choice (from Martelli–Montanari-style algorithms) avoids this?

---

### Chapter 2: Definite Programs (pp. 35–70)

**Summary:** This chapter develops the full theory of definite programs: it defines the least Herbrand model as the declarative meaning of a program, gives its fixpoint characterisation via the operator $T_P$, defines correct and computed answers, and proves the central soundness and completeness theorems linking SLD-resolution (the procedural semantics) to logical consequence. It closes with practical concerns — the danger of omitting the occur check, the structure of SLD-trees and search strategies, and the semantics and pitfalls of the cut control facility. : [[Declarative-Semantics-of-Definite-Programs|Link1]], [[Negation-in-Logic-Programs|Link2]]

**Key Definitions & Concepts by Section:**
- **§6 Declarative Semantics** — least Herbrand model $M_P$ (via the model intersection property, Proposition 6.1), the operator $T_P$, van Emden–Kowalski fixpoint characterisation $M_P=\mathrm{lfp}(T_P)=T_P{\uparrow}\omega$ (Theorem 6.5), answer, correct answer.
- **§7 Soundness of SLD-Resolution** — derived goal/resolvent, SLD-derivation, standardising variables apart, SLD-refutation, unrestricted SLD-refutation, success/failed/infinite derivation, success set, computed answer, Soundness of SLD-Resolution (Theorem 7.1), the occur-check problem illustrated with difference lists.
- **§8 Completeness of SLD-Resolution** — the Mgu Lemma (8.1) and Lifting Lemma (8.2), success set $=$ least Herbrand model (Theorem 8.3), Completeness (Theorem 8.4: unsatisfiability implies a refutation exists), Completeness of SLD-Resolution for correct answers (Theorem 8.6).
- **§9 Independence of the Computation Rule** — computation rule, R-computed answer, the Switching Lemma (9.1), Independence of the Computation Rule (Theorem 9.2), Computational Adequacy of Definite Programs (Theorem 9.6: every partial recursive function is computed by some definite program).
- **§10 SLD-Refutation Procedures** — SLD-tree, success/infinite/failure branches, search rule, SLD-refutation procedure, fairness, the depth-first-search incompleteness problem (illustrated with slowsort and a program requiring dynamic clause reordering), coroutining and automatic control generation (NU-PROLOG "when" declarations).
- **§11 Cuts** — cut ("!"), parent goal, safe vs. unsafe use of cut, the declarative-vs-procedural gap introduced by cut (cut does not affect declarative semantics of definite programs but can destroy completeness, and can be abused to hide missing tests).

**Key Questions:**
1. Why does "every correct answer is an instance of a computed answer" (rather than an exact equality), and where in the proof of Theorem 8.6 does this asymmetry arise?
2. What does the Independence of the Computation Rule theorem actually guarantee, and why doesn't it, by itself, make depth-first PROLOG systems complete?
3. In what precise sense does a cut "not affect the declarative semantics" of a definite program, yet still make some programs declaratively incorrect (as in the `max` example)?

---

### Chapter 3: Normal Programs (pp. 71–106)

**Summary:** This chapter tackles negative information. It introduces the closed world assumption and the negation as failure rule as non-monotonic inference rules for deriving negative facts, defines normal programs (clause bodies as conjunctions of literals) and the completion of a program as the declarative counterpart of negation as failure, and proves soundness (always) and completeness (only for the restricted class of hierarchical programs) of SLDNF-resolution. : [[Programs-and-Goals-with-Arbitrary-First-Order-Bodies|Link]]

**Key Definitions & Concepts by Section:**
- **§12 Negative Information** — the closed world assumption (CWA), non-monotonic inference rule, SLD finite failure set, the negation as failure rule (weaker than the CWA), the need for negative literals in clause bodies (e.g. `different/2`).
- **§13 Finite Failure** — finitely failed by depth $d$ ($F_P^d$), finite failure set $F_P$ ($=B_P\setminus T_P{\downarrow}\omega$, Proposition 13.1), SLD finite failure set, fairness of an SLD-derivation/tree, equivalence of finite failure characterisations (Theorem 13.6).
- **§14 Programming with the Completion** — program clause with literal body, normal program, normal goal, the completion $\mathrm{comp}(P)$ of a normal program (via the transformation to $\exists\vec y((x_1=t_1)\land\cdots\land L_1\land\cdots)$), the equality theory (axioms 1–8), correct answer for $\mathrm{comp}(P)\cup\{G\}$, the operator $T_P^J$ (generally non-monotonic), level mapping, hierarchical program, stratified program (Apt–Blair–Walker / Van Gelder), minimal normal Herbrand model of a stratified program's completion (Corollary 14.8).
- **§15 Soundness of SLDNF-Resolution** — SLDNF-refutation/finitely failed SLDNF-tree of rank $k$ (mutually recursive definition), the safeness condition (only ground negative literals selected), computed answer for normal programs, floundering, admissible/allowed clauses and goals, Soundness of the Negation as Failure Rule (Theorem 15.4), Soundness of SLDNF-Resolution (Theorem 15.6), how an unsafe cut can break soundness for normal programs (`subset` example).
- **§16 Completeness of SLDNF-Resolution** — Completeness of the Negation as Failure Rule for definite programs (Theorem 16.1, via a non-Herbrand model construction), the Herbrand rule (a third, intermediate rule between CWA and negation as failure — Figure 6 shows $\mathrm{CWA} \Rightarrow \mathrm{Herbrand\ rule} \Rightarrow \mathrm{negation\ as\ failure}$ in decreasing strength), safe computation rule, Completeness of SLDNF-Resolution for Hierarchical Programs (Theorem 16.3), why completeness fails outright for stratified (non-hierarchical) programs.

**Key Questions:**
1. Why is the negation as failure rule strictly weaker than the closed world assumption, and where does the Herbrand rule sit between them?
2. Why does completeness of SLDNF-resolution require restricting to *hierarchical* (not merely stratified) programs, and what concretely breaks for a merely-stratified program (see the `q`/`r`/`p` example)?
3. Why must only *ground* negative literals be selected (the safeness condition), and what goes wrong — concretely — if this restriction is dropped?

---

### Chapter 4: Programs (pp. 107–140)

**Summary:** This chapter generalises normal programs to programs whose clause bodies (and goal bodies) may be arbitrary first-order formulas, arguing this is both theoretically natural and practically useful (expert systems, deductive databases). It shows every such program can be transformed into an equivalent normal program, uses this to lift the soundness/completeness results of chapter 3, and then develops a declarative error diagnoser — an "algorithmic debugger" that locates bugs using only the programmer's intended interpretation, without any understanding of the underlying computational/control behaviour.

**Key Definitions & Concepts by Section:**
- **§17 Introduction to Programs** — program statement $A\leftarrow W$ (arbitrary formula body), program, goal $\leftarrow W$, completed definition of a predicate for arbitrary-body statements, correct answer, level mapping, hierarchical/stratified programs (generalised), the operator $T_P^J$ for arbitrary programs.
- **§18 SLDNF-Resolution for Programs** — transformation of a goal via a fresh `answer` predicate, the ten normal-form transformations (a)–(j) (De Morgan-style rewriting plus Skolemisation of $\exists$ into a new predicate), termination of the transformation process (Proposition 18.2, via a multiset well-founded ordering), normal form of a program/program-and-goal, floundering and allowedness for arbitrary programs, Soundness of the Negation as Failure Rule (18.6) and of SLDNF-Resolution (18.7) for programs, Completeness for hierarchical programs (18.9).
- **§19 Declarative Error Diagnosis** — algorithmic debugging (Shapiro), intended interpretation, program correct/incorrect wrt an interpretation, uncovered atom, incorrect statement instance (and incorrect clause instance), the declarative diagnoser (`wrong`/`missing` meta-predicates operating over a symbolic representation of formulas), the top-down version using `succeed`/`fail` oracle-backed metacalls, comparison with Shapiro's single-stepping (bottom-up, $O(n)$ queries) and divide-and-query ($O(\log n)$ queries) algorithms and their respective query-complexity trade-offs.
- **§20 Soundness and Completeness of the Diagnoser** — connected positively/negatively (an atom's reachability relation to a formula through the program), Soundness of the Error Diagnoser (Theorem 20.1), Completeness of the Error Diagnoser (Theorem 20.5, via Lemmas 20.2–20.4).

**Key Questions:**
1. Why does every program admit a normal form (i.e., why does the rewriting process in §18 always terminate), and what role does the multiset ordering play in that proof?
2. In what precise sense is the error diagnoser "declarative" — what does the programmer need to know (and *not* need to know) to use it — and why does this break down for programs relying on cut, assert, or retract?
3. How do the top-down, single-stepping, and divide-and-query diagnosis algorithms trade off worst-case query complexity against how well they exploit locality of the actual error?

---

### Chapter 5: Deductive Databases (pp. 141–172)

**Summary:** This chapter recasts deductive database theory as an application of the programs-and-goals framework of chapter 4, using a typed first-order theory so that types capture the domain concept of relational databases. It defines databases, queries, correct answers, and integrity constraints from a proof-theoretic (rather than model-theoretic) standpoint, proves soundness and completeness of a query evaluation process built by reducing typed formulas to type-free ones, and proves a simplification theorem that lets integrity constraints be checked incrementally after a database update rather than re-verified from scratch. : [[Deductive-Database-Theory|Link]]

**Key Definitions & Concepts by Section:**
- **§21 Introduction to Deductive Databases** — database statement, database, query, answer, integrity constraint, completed definition of a predicate in a typed theory, the typed equality theory (including domain closure axioms 9), database satisfies/violates an integrity constraint, model-theoretic vs. proof-theoretic view of databases, normal/definite query, database clause, definite database clause, level mapping, hierarchical/stratified database.
- **§22 Soundness of Query Evaluation** — type-free form $W^*$ of a typed formula, type theory $\Phi$ (with type predicate symbols), Soundness of Query Evaluation (Theorem 22.6, via a long model-construction Lemma 22.1 that builds a model $M^*$ for the type-free completion from a model $M$ of the typed completion), floundering-freedom for query evaluation (Proposition 22.8).
- **§23 Completeness of Query Evaluation** — the converse type-lowering construction (Lemma 23.1), Completeness of Query Evaluation for Definite Databases (Theorem 23.4), Completeness of Query Evaluation for Hierarchical Databases (Theorem 23.5, giving finite, terminating SLDNF-trees).
- **§24 Integrity Constraints** — using query evaluation to check integrity constraints (Theorems 24.1–24.2), transaction (sequence of additions/deletions), the atom sets $\mathrm{pos}_{D,D'}$ and $\mathrm{neg}_{D,D'}$ capturing the difference between models of $\mathrm{comp}(D)$ and $\mathrm{comp}(D')$, the Simplification Theorem for Integrity Constraint Checking (Theorem 24.5, plus Corollaries 24.6–24.7 for single addition/deletion), stopping rules for computing the atom sets in practice.

**Key Questions:**
1. Why does the book adopt a proof-theoretic (rather than model-theoretic) view of databases, and what advantages does this give once databases go beyond ground facts (relational databases)?
2. Why are domain closure axioms essential to the completion of a database, and what breaks (concretely, per the example in §22) if they are omitted?
3. How does the simplification theorem reduce integrity-constraint checking after an update to checking only finitely many *instances* of a constraint, and why is this only guaranteed to terminate for stratified databases with an appropriate stopping rule?

---

### Chapter 6: Perpetual Processes (pp. 173–194)

**Summary:** This final, more speculative chapter develops a semantics for definite programs that run forever while still doing "useful" infinite computation — perpetual processes — by extending the Herbrand universe/base to admit infinite terms and atoms, showing this complete Herbrand universe is a compact metric space, and defining when an infinite atom is "computable at infinity." The main result is a soundness theorem placing the set of atoms computable at infinity inside the greatest fixpoint of the (compactness-enriched) immediate consequence operator $T'_P$, though full completeness remains open. : [[Semantics-of-Perpetual-Processes|Link]]

**Key Definitions & Concepts by Section:**
- **§25 Complete Herbrand Interpretations** — tree (over $\omega^*$), (possibly infinite) term over a signature, depth of a term, truncation $\sigma_n(t)$, ultrametric space, the metric $d(s,t)=2^{-\alpha(s,t)}$ on terms, compactness, complete Herbrand universe $U'_P$ (compact iff the signature is finite — Proposition 25.2), (possibly infinite) atom, complete Herbrand base $B'_P$, ground substitution and ground instance for infinite atoms, complete Herbrand interpretation, complete Herbrand model, the operator $T'_P$.
- **§26 Properties of $T'_P$** — Model Intersection Property for $T'_P$, continuity of $T'_P$, the least complete Herbrand model $M'_P$, Closedness of $T'_P$ (Theorem 26.5, Andreka–van Emden–Nemeti–Tiuryn), limit superior of a sequence of sets ($\mathrm{LS}$), Weak Continuity of $T'_P$ (Theorem 26.7), the Intersection Property for $T'_P$ (Corollary 26.8), the key result $\mathrm{gfp}(T'_P)=T'_P{\downarrow}\omega$ (Theorem 26.9(a) — contrasting with ordinary $T_P$, where $\mathrm{gfp}(T_P)\neq T_P{\downarrow}\omega$ in general), characterisation of $\bigcap_{k\in\omega}T_P{\downarrow}k$ via fair derivations (Theorem 26.12).
- **§27 Semantics of Perpetual Processes** — computable at infinity ($d(A,B\theta_1\cdots\theta_k)\to 0$), the set $C_P$ of atoms computable at infinity, the Fibonacci and Hamming-sequence programs as worked examples of perpetual processes, the metric-free characterisation of $C_P$ via $\bigcap_k[[B\theta_1\cdots\theta_k]]=\{A\}$ (Proposition 27.1), why a weaker "membership only" definition of $C_P$ fails to capture genuine infinite computation (counterexample with `p(f(x)) <- p(f(x))`), Soundness of SLD-Resolution for Perpetual Processes (Theorem 27.2: $C_P\subseteq \mathrm{gfp}(T'_P)$), and why full completeness ($C_P=\mathrm{gfp}(T'_P)\setminus B_P$) fails without further restrictions (three counterexamples), with $\mathrm{gfp}(T'_P)$ proposed as the intended interpretation of a perpetual process.

**Key Questions:**
1. Why is compactness of the complete Herbrand universe the crucial fact that makes $\mathrm{gfp}(T'_P)=T'_P{\downarrow}\omega$ true for infinite terms, when the analogous equality fails for the ordinary (finite-term) operator $T_P$?
2. What exactly does "computable at infinity" mean, and why does the book insist on convergence ($d(A,B\theta_1\cdots\theta_k)\to 0$) rather than mere set membership ($A\in\bigcap_k[[B\theta_1\cdots\theta_k]]$) to rule out the `p(f(x)) <- p(f(x))` counterexample?
3. Given that $C_P\subseteq \mathrm{gfp}(T'_P)$ is only a soundness result, what do the chapter's counterexamples reveal about why completeness fails, and what kind of restriction on programs (or redefinition of $C_P$/$T'_P$) might be needed to recover it?
