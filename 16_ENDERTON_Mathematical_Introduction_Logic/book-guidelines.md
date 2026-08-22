# A Mathematical Introduction to Logic — Guidelines

## Header

**Title:** A Mathematical Introduction to Logic
**Author(s):** Herbert B. Enderton
**Publication:** Harcourt/Academic Press, 2nd Edition, 2001 (1st edition 1972)

**Brief Summary:**
This book presents the core concepts and results of mathematical logic — proofs, truth, and computability — for a reader with mathematical background but no prior exposure to logic. It builds two successive formal models of deductive reasoning: sentential (propositional) logic, deliberately simple and inadequate, and first-order logic, which is shown to be adequate for mirroring the deductions of working mathematicians. The central organizing idea is the interplay between semantic notions (truth, models, logical implication) and syntactic notions (deduction, provability), crystallized in the soundness and completeness theorems, and pushed to its limits in Chapter 3's study of undecidability and Gödel's incompleteness theorems. A closing chapter surveys second-order logic as a more expressive but semantically less well-behaved alternative.

**Intent of the Author:**
Enderton wrote the book as an introductory textbook for junior-senior mathematics students, aiming to present the important concepts and theorems of logic and explain their significance for the reader's broader mathematical work, without presupposing that the reader already "knows how to think" or needs remedial instruction in reasoning. The second edition sought to make the material more accessible to typical undergraduates, to give instructors more flexibility via optional sections, and to reflect computer science's growing influence on logic by taking computability issues more seriously.

---

## Topic List

1. **Foundational Set-Theoretic Apparatus**
   - Sets relations functions and operations
   - Ordered pairs and finite sequences
   - Equivalence relations and ordering relations
   - Countability and finiteness
   - Trees as informal pictures of structure
   - Zorns lemma and the axiom of choice
   - Cardinal numbers and cardinal arithmetic
   - The Schröder–Bernstein theorem

2. **Sentential (Propositional) Logic**
   - The formal language of sentential logic
   - Well-formed formulas and unique readability
   - Truth assignments and the extension theorem
   - Tautological implication and tautological equivalence
   - Truth tables as a decision procedure
   - The P versus NP problem as a limit on truth-table efficiency

3. **Induction and Recursion on Freely Generated Sets**
   - Sets generated from a base by operations
   - The abstract induction principle
   - Free generation and the recursion theorem
   - The unique readability theorem for wffs

4. **Sentential Connectives and Their Completeness**
   - Boolean functions and their realization by wffs
   - Disjunctive and conjunctive normal form
   - Complete sets of connectives
   - Duality and the interpolation theorem

5. **Switching Circuits**
   - Boolean functions as circuit behavior
   - Delay and cost of a circuit
   - Circuit minimization and available device catalogs

6. **Compactness for Sentential Logic**
   - Finite satisfiability versus satisfiability
   - Maximal finitely satisfiable sets
   - Zorns lemma as an alternative existence proof

7. **First-Order Languages**
   - Logical symbols versus parameters
   - Terms atomic formulas and well-formed formulas
   - Free and bound variable occurrence
   - Translating English and set theory into first-order form
   - The parsing algorithm and unique readability for terms and wffs

8. **Structures Truth and Satisfaction**
   - Structures as interpretations of a language
   - Satisfaction of a formula by a structure and assignment
   - The independence of satisfaction from irrelevant variable values
   - Logical implication logical validity and logical equivalence
   - Substitution alphabetic variants and quantifier capture

9. **The Deductive Calculus for First-Order Logic**
   - Logical axioms and modus ponens
   - Deductions as finite construction sequences
   - Generalization on constants and the deduction theorem
   - Substitutability of a term for a variable

10. **Soundness and Completeness**
    - The soundness theorem
    - Henkin witnesses and complete consistent extensions
    - The completeness theorem
    - The compactness theorem for first-order logic
    - The Löwenheim–Skolem theorem
    - The enumerability of validities

11. **Models of Theories**
    - Finite models and arbitrarily large finite models
    - Elementarily definable classes EC and ECΔ
    - Decidability of the theory of a finite structure
    - Elimination of quantifiers
    - Definable sets and the diagonal argument for undefinability
    - Elementary equivalence and elementary substructures
    - The Tarski–Vaught test
    - Categoricity and Łoś–Vaught test for completeness
    - Noncreative definitions and well-definedness

12. **Interpretations Between Theories**
    - Relative interpretability of one theory in another
    - Translating quantifiers and defined relations across languages
    - Faithful interpretations

13. **Nonstandard Analysis**
    - Nonstandard models of the reals via compactness
    - Infinitesimals finite and infinite elements
    - The relation of being infinitely close
    - Standard parts and transfer of properties

14. **The Language and Structure of Number Theory**
    - The intended structure N and its reducts
    - Definability of relations in N and its reducts
    - Numerals and naming every natural number
    - The three guiding questions decidability definability nonstandard models

15. **Weak Fragments of Number Theory**
    - Successor arithmetic and its decidability
    - Presburger arithmetic and its decidability
    - Elimination of quantifiers for weak theories
    - Z-chains in nonstandard models

16. **Arithmetization of Syntax**
    - Gödel numbering of expressions and sequences
    - Recursively numbered languages
    - Representable relations and functions
    - Coding deductions as numbers

17. **Representability and Recursive Functions**
    - Representable versus functionally representable relations
    - Primitive recursion and minimization
    - The catalog of representable functions
    - Church's thesis
    - Universal machines Kleene's normal form theorem
    - Decidable semidecidable and recursively enumerable sets

18. **Gödel's Incompleteness Theorems**
    - The fixed-point lemma and self-reference
    - Tarski's undefinability theorem
    - The first Gödel incompleteness theorem
    - The self-reference diagonalization and computability approaches compared
    - Provability predicates and derivability conditions
    - The second Gödel incompleteness theorem and consistency statements
    - Sufficiently strong theories

19. **Representing Exponentiation and the Gödel β-Function**
    - Pairing and projection functions
    - The Chinese remainder theorem
    - The Gödel β-function as a sequence-decoding device
    - Strong undecidability of arithmetic with multiplication

20. **Second-Order Logic**
    - Predicate and function variables and quantification over them
    - Absolute second-order semantics
    - Categoricity results for the natural numbers and the reals
    - Failure of compactness and Löwenheim–Skolem for second-order logic
    - Comprehension formulas

21. **Skolem Functions and Normal Forms**
    - Skolem normal form for second-order formulas
    - Skolemization and equal satisfiability
    - Undecidability of universal and existential first-order sentences

22. **Many-Sorted and General Second-Order Logic**
    - Many-sorted first-order languages simulating second order
    - Membership and evaluation parameters
    - General structures and general models
    - Recovery of compactness Löwenheim–Skolem and enumerability
    - Analysis as second-order number theory and ω-models

---

## Chapter Summaries

### Chapter Zero: Useful Facts about Sets (pp. 1–10)

**Summary:** A reference chapter, not meant to be read straight through, that fixes the set-theoretic notation and results used throughout the book — from basic set operations through cardinal arithmetic — so that later chapters can call on them without digression.

**Key Definitions & Concepts:**
- Extensionality — $A = B$ iff $A$ and $B$ have exactly the same members.
- $A; t$ — the set $A \cup \{t\}$, adjoining one extra element.
- Power set $\mathcal{P}A = \{x \mid x \subseteq A\}$.
- Ordered pair $\langle x, y \rangle = \{\{x\}, \{x,y\}\}$; $n$-tuples defined recursively from pairs.
- Finite sequence (string), segment, initial segment, proper segment.
- Relation, domain, range, field of a relation; $n$-ary relation; restriction of a relation.
- Function, $F : A \to B$, one-to-one, onto; $n$-ary operation on $A$; closure of $B$ under $f$.
- Reflexive, symmetric, transitive relations; trichotomy; equivalence relation; ordering relation; equivalence class $[x]$.
- Countable set; Theorem 0B — the set of finite sequences over a countable set is countable.
- Trees (informal) and their underlying finite partial ordering, root, labeling function.
- Zorn's lemma, stated via chains and maximal elements.
- Equinumerous sets ($A \sim B$), cardinal number $\operatorname{card} A$, dominance ($A \preceq B$).
- Schröder–Bernstein theorem — mutual domination implies equinumerosity.
- $\aleph_0$, $2^{\aleph_0}$, cardinal addition and multiplication; the Cardinal Arithmetic Theorem (sum/product of infinite cardinals is the larger one).
- Theorem 0D — for infinite $A$, the set of finite sequences from $A$ has cardinality $\operatorname{card} A$.

**Key Questions:**
1. Why does extensionality make "having the same members" the *only* thing that can distinguish two sets, and how does this license identifying $\{x,y\}$ with $\{y,x\}$?
2. What is the precise difference between $A \sim B$ (equinumerosity) and $\operatorname{card} A \le \operatorname{card} B$ (dominance), and why does the Schröder–Bernstein theorem need a genuinely nontrivial proof to connect them?

---

### Chapter One: Sentential Logic (pp. 11–66)

**Summary:** Enderton builds sentential logic as a first, deliberately crude, mathematical model of deduction: a formal language with a precise notion of well-formed formula, a semantics via truth assignments, and a proof (via unique readability and the recursion theorem) that this semantics is well-defined. The chapter culminates in the compactness theorem and a discussion of the limits of brute-force decision procedures (truth tables, and the P vs. NP problem).

**Key Definitions & Concepts by Section:**
- **1.0 Informal Remarks on Formal Languages** — the three components of a formal language (alphabet, grammar/wffs, translation to English); illustration via chemistry-lab example sentences.
- **1.1 The Language of Sentential Logic** — sentential connective symbols $\neg, \wedge, \vee, \rightarrow, \leftrightarrow$; sentence symbols (parameters); expression, concatenation; well-formed formula (wff) defined via the formula-building operations $E_\neg, E_\wedge, E_\vee, E_\rightarrow, E_\leftrightarrow$; construction sequence; the Induction Principle for wffs.
- **1.2 Truth Assignments** — truth values $\{F,T\}$; truth assignment $v : S \to \{F,T\}$; the extension $\bar v$ satisfying conditions 0–5 (Theorem 12A); satisfies; tautological implication ($\Gamma \models \tau$); tautology ($\models \tau$); tautological equivalence ($\sigma \mathbin{|\!=\!|} \tau$); statement of the Compactness Theorem (proved later); truth tables as a decision procedure; a selected list of standard tautologies (De Morgan's laws, contraposition, exportation, etc.).
- **1.3 A Parsing Algorithm** — Lemma 13A (balanced parentheses) and Lemma 13B (no proper initial segment of a wff is a wff); the four-step parsing algorithm and its correctness (unique readability, informally); Polish notation; conventions for omitting parentheses.
- **1.4 Induction and Recursion** — sets generated from a base $B$ by functions $f,g$ (defined "top down," via inductive sets, and "bottom up," via construction sequences, shown equivalent); the general Induction Principle; freely generated sets; the Recursion Theorem, and its proof via the union of "acceptable" partial functions; the Unique Readability Theorem restated as: the wffs are freely generated from the sentence symbols by the five formula-building operations.
- **1.5 Sentential Connectives** — Boolean function; realizing a Boolean function by a wff; disjunctive/conjunctive normal form; complete set of connectives; examples of complete and incomplete sets ($\{\wedge,\vee,\neg\}$, Sheffer stroke $\mid$, NOR $\downarrow$); duality; the interpolation theorem.
- **1.6 Switching Circuits** — Boolean function realized by a device/circuit; AND, OR, NOT gates; delay (depth) of a circuit; circuit minimization; relay circuits and bridge circuits; literal, implicant, prime implicant.
- **1.7 Compactness and Effectiveness** — finitely satisfiable set; proof of the Compactness Theorem via a maximal finitely satisfiable extension $\Gamma^*$ and the truth assignment it induces; discussion of effectiveness and decidability of the set of tautologies.

**Key Questions:**
1. Why is the existence of a unique extension $\bar v$ of a truth assignment $v$ not obvious, and what two facts (about freely generated sets) does its proof actually rest on?
2. How does the two-part proof of the Compactness Theorem (extend to a maximal finitely satisfiable $\Gamma^*$, then build $v$ from membership in $\Gamma^*$) use the fact that $\Gamma^*$ decides every wff or its negation?
3. What is the difference between a set of connectives being merely expressive enough to translate English and being *complete* in Enderton's technical sense, and why is completeness a genuinely stronger requirement?

---

### Chapter Two: First-Order Logic (pp. 67–181)

**Summary:** The chapter's central chapter, presenting first-order logic — syntax, structures/models, a Hilbert-style deductive calculus, and the soundness and completeness theorems that show the calculus captures exactly logical implication — before applying the resulting machinery to models of theories, interpretations between theories, and nonstandard analysis.

**Key Definitions & Concepts by Section:**
- **2.0 Preliminary Remarks** — motivation for moving beyond sentential logic; informal translation examples (number theory, set theory) motivating quantifiers and predicate/function symbols.
- **2.1 First-Order Languages** — logical symbols (parentheses, $\rightarrow, \neg$, variables $v_1,v_2,\dots$, optional equality $=$) versus parameters (quantifier symbol $\forall$, predicate symbols, constant symbols, function symbols); term and wff defined inductively; free versus bound variable occurrence; example languages (pure predicate, set theory, elementary number theory).
- **2.2 Truth and Models** — structure $\mathfrak{A}$ assigning a universe $|\mathfrak{A}|$ and interpretations to parameters; satisfaction $\models_{\mathfrak{A}} \varphi[s]$ defined by recursion on terms, atomic formulas, and connectives/quantifiers; Theorem 22A (satisfaction depends only on free variables); logical implication $\Gamma \models \tau$, validity, logical equivalence.
- **2.3 A Parsing Algorithm** — unique readability for terms and wffs of first-order languages, extending the Chapter 1 result.
- **2.4 A Deductive Calculus** — deduction as proof-substitute; logical axioms $\Lambda$ in six groups (tautologies; $\forall x\,\alpha \rightarrow \alpha^t_x$ with substitutability; distribution of $\forall$ over $\rightarrow$; vacuous quantification; equality axioms $x=x$ and substitution of equals); modus ponens as sole rule of inference; deduction $\Gamma \vdash \varphi$; substitutable term $t$ for $x$ in $\alpha$, guarding against quantifier capture.
- **2.5 Soundness and Completeness Theorems** — Soundness Theorem ($\Gamma \vdash \varphi \Rightarrow \Gamma \models \varphi$) via validity of logical axioms and the Substitution Lemma; consistency; the Completeness Theorem ($\Gamma \models \varphi \Rightarrow \Gamma \vdash \varphi$) via Henkin's method of adding witnessing constants and extending to a complete consistent set; derived Compactness Theorem, Löwenheim–Skolem Theorem, and Enumerability Theorem for first-order logic.
- **2.6 Models of Theories** — Theorem 26A (arbitrarily large finite models imply an infinite model, via compactness); elementary class $\mathrm{EC}$ and $\mathrm{EC}_\Delta$; theory of a structure $\mathrm{Th}\,\mathfrak{A}$; decidability of finite structures' theories; elimination of quantifiers; elementary equivalence and elementary substructure; the Tarski–Vaught test; noncreative definitions and well-definedness (Theorem 27A).
- **2.7 Interpretations Between Theories** — relative strength of theories in different languages; translating quantifiers and defined relations (e.g. $(\mathbb{Z};+,\cdot)$ interpreting $(\mathbb{N};0,S)$ via Lagrange's four-square theorem); faithful interpretation.
- **2.8 Nonstandard Analysis** — nonstandard model $^*\mathbb{R}$ of the reals obtained via compactness; finite elements $F$, infinitesimals $I$; $F$ a subring, $I$ an ideal in $F$; infinitely close ($x \simeq y$); Theorem 28D — every finite $x$ is infinitely close to a unique standard real (its standard part).

**Key Questions:**
1. Why does the Soundness Theorem reduce entirely to showing that every logical axiom is valid and that modus ponens preserves logical implication — and where exactly does the Substitution Lemma enter that argument?
2. In what sense does the Completeness Theorem turn the compactness and enumerability theorems from independent facts into consequences of a single deductive calculus?
3. How does the transfer principle implicit in nonstandard analysis (via compactness) let one reason about infinitesimals using ordinary first-order properties of $\mathbb{R}$?

---

### Chapter Three: Undecidability (pp. 182–281)

**Summary:** Enderton develops the arithmetization of syntax for the language of number theory, uses it to build self-referential sentences via the fixed-point lemma, and derives Tarski's undefinability theorem, Gödel's first and second incompleteness theorems, and the undecidability of arithmetic — presenting the results from three complementary angles (self-reference, diagonalization, and computability) and connecting them to the theory of recursive functions.

**Key Definitions & Concepts by Section:**
- **3.0 Number Theory** — the intended structure $\mathfrak{N} = (\mathbb{N}; 0, S, <, +, \cdot, E)$ and its reducts $\mathfrak{N}_S, \mathfrak{N}_L, \mathfrak{N}_A, \mathfrak{N}_M$; numerals $S^k0$; Gödel number $\sharp\alpha$; preview of the self-reference, diagonalization, and computability approaches to incompleteness; Theorem 30A and Corollary 30B (undefinability of $\mathrm{Th}\,\mathfrak{N}$'s Gödel-number set); Theorem 30C/30D previewing undecidability and non-enumerability of $\mathrm{Th}\,\mathfrak{N}$.
- **3.1 Natural Numbers with Successor** — the weak structure $\mathfrak{N}_S = (\mathbb{N};0,S)$; decidability of $\mathrm{Th}\,\mathfrak{N}_S$; Z-chains in nonstandard models.
- **3.2 Other Reducts of Number Theory** — $\mathfrak{N}_L$ (adding $<$) and $\mathfrak{N}_A$ (adding $+$, i.e. Presburger arithmetic); decidability results and quantifier elimination for these weaker theories.
- **3.3 A Subtheory of Number Theory** — axiom set $A_E$; primitive recursion, minimization; catalog of representable functions; representable and functionally representable relations/functions.
- **3.4 Arithmetization of Syntax** — Gödel numbering $h$ of symbols and $\sharp$ of expressions; recursively numbered language; showing syntactic relations (e.g. "is the Gödel number of a term/wff/deduction") are representable in $\mathrm{Cn}\,A_E$.
- **3.5 Incompleteness and Undecidability** — the Fixed-Point Lemma ($A_E \vdash \sigma \leftrightarrow \beta(S^{\sharp\sigma}0)$); Tarski's Undefinability Theorem (1933); Corollary 35A (undecidability of $\mathrm{Th}\,\mathfrak{N}$); Gödel's (First) Incompleteness Theorem (1931); Lemma 35B (recursiveness preserved under adding axioms); the Strong Undecidability of $\mathrm{Cn}\,A_E$.
- **3.6 Recursive Functions** — Church's thesis; closure of recursive functions under composition and minimization; the normal form theorem, universal relation $T_1$/function $U$; decidable, semidecidable, and recursively enumerable sets.
- **3.7 Second Incompleteness Theorem** — the provability predicate $\mathrm{Prb}_T\sigma$; Lemma 37A (reflection); sufficiently strong theories and the three derivability conditions; the consistency sentence $\mathrm{Cons}\,T$; the Second Incompleteness Theorem — a sufficiently strong consistent theory cannot prove its own consistency.
- **3.8 Representing Exponentiation** — representability of exponentiation in $\mathrm{Cn}\,A_M$; the pairing function $J$ and projections $K,L$; the Gödel $\beta$-function and the Chinese Remainder Theorem (Lemma 38A/38B); Theorem 38C; summary Table X comparing decidability/definability across the reducts of $\mathfrak{N}$.

**Key Questions:**
1. How does the Fixed-Point Lemma let one construct a sentence $\sigma$ that "talks about itself," and why is this not literal self-reference but rather an artifact of Gödel numbering plus representability?
2. Walk through why Tarski's Undefinability Theorem, the (first) Gödel Incompleteness Theorem, and the undecidability of $\mathrm{Th}\,\mathfrak{N}$ are three closely related but logically distinct consequences of the same fixed-point construction.
3. What do the three "derivability conditions" for a sufficiently strong theory buy you, and why is it exactly this formalized reflection that makes the Second Incompleteness Theorem possible?

---

### Chapter Four: Second-Order Logic (pp. 282–306)

**Summary:** The closing chapter studies second-order logic, which gains expressive power (categorical characterizations of $\mathbb{N}$ and $\mathbb{R}$) by quantifying over predicate and function variables, at the cost of losing compactness, the Löwenheim–Skolem theorem, and effective enumerability of validity under the standard ("absolute") semantics; an alternative many-sorted ("general") semantics recovers these metatheorems by giving up full categoricity.

**Key Definitions & Concepts by Section:**
- **4.1 Second-Order Languages** — predicate and function variables $X_i^n, F_i^n$; individual variables; extended satisfaction clauses for $\forall X^n\varphi$ and $\forall F^n\varphi$; categorical second-order characterizations of $(\mathbb{N};0,S)$ via the Peano induction postulate, and of the real ordered field via the least-upper-bound sentence; relation/function comprehension formulas; Theorem 41A (failure of compactness); Theorem 41B (a sentence true exactly in sets of cardinality $2^{\aleph_0}$); Theorem 41C (non-definability, hence non-enumerability, of second-order validity).
- **4.2 Skolem Functions** — Skolem function for a formula $\forall x \exists y\, \varphi$ in a structure; the Skolem Normal Form Theorem (any first-order formula is logically equivalent to a second-order $\exists^*\forall^*$ formula); Corollary 42A (reduction to equisatisfiable universal formulas via Skolemization); Corollary 42B (undecidability of satisfiability for universal, and validity for existential, first-order sentences).
- **4.3 Many-Sorted Logic** — recasting second-order logic as a many-sorted first-order language with sorts for individuals, $n$-place predicates, and $n$-place functions; membership parameters $\varepsilon^n$ and evaluation parameters $E^n$; Theorem 44A relating many-sorted structures to genuine second-order structures via a homomorphism.
- **4.4 General Structures** — general pre-structure (relation and function universes added to an ordinary structure) and general structure (one satisfying all comprehension sentences); satisfaction $\models^G_{\mathfrak{A}}$ via the many-sorted translation; recovered Löwenheim–Skolem, Compactness, and Enumerability Theorems for general second-order logic; absolute versus general second-order semantics compared; models of analysis and $\omega$-models.

**Key Questions:**
1. Why does the very expressiveness that lets second-order logic categorically characterize $\mathbb{N}$ and $\mathbb{R}$ simultaneously force the failure of compactness and the Löwenheim–Skolem theorem for its (absolute) semantics?
2. How does Skolemization turn a first-order satisfiability question into a second-order existence question about Skolem functions, and why does this yield an undecidability result purely for first-order universal sentences?
3. In what precise sense does reinterpreting second-order logic as many-sorted first-order logic (general semantics) trade categoricity for the recovery of compactness, Löwenheim–Skolem, and enumerability?
