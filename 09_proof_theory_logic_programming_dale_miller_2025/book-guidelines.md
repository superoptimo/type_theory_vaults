# Proof Theory and Logic Programming: Computation as Proof Search — Guidelines

## Header

**Title:** Proof Theory and Logic Programming: Computation as Proof Search
**Author(s):** Dale Miller
**Publication:** Cambridge University Press, December 2025 (DOI 10.1017/9781009561280). Free online draft dated 30 December 2025, Inria Saclay and LIX.

**Brief Summary:**
The book develops Gentzen-style sequent calculus proof systems for classical, intuitionistic, and linear logic, over first-order and higher-order quantification, and uses them to design and analyze logic programming languages in which computation is the search for a cut-free proof. Goal-directed search (uniform proofs) and backchaining (focused proofs) give Prolog (Horn clauses), $\lambda$Prolog (hereditary Harrop formulas), Lolli, and Forum, all of which are shown to sit inside higher-order linear logic. The first part (Chapters 1–9) builds the proof theory, including cut elimination for focused systems. The second part (Chapters 10–13) applies it to automata, static analysis of Horn clauses, security protocols, and operational semantics.

**Intent of the Author:**
Miller wants to show that logic programs can be read as formulas and computation as proof construction, so that features such as modules, higher-order programming, abstract data types, state, and concurrency come from proof theory instead of ad hoc extensions. The reader should come away able to design a logic programming language from a sequent calculus and to reason about its programs with cut elimination and substitution.

---

## Topic List

1. **Computation as Proof Search** : [[Computation-as-Proof-Search|Link]]
   - Computation as model versus computation as deduction : [[Computation-as-Proof-Search|Link]]
   - Proof normalization versus proof search : [[Computation-as-Proof-Search|Link]]
   - Sequents as computation states : [[Computation-as-Proof-Search|Link]]
   - Resolution refutation as an unfortunate foundation : [[Computation-as-Proof-Search|Link]]
   - Programming equals logic : [[Computation-as-Proof-Search|Link]]
   - Don't-know and don't-care nondeterminism : [[Classical-Intuitionistic-and-Minimal-Logics|Link1]], [[Computation-as-Proof-Search|Link2]]

2. **Simply Typed Lambda-Terms and Church's Types** : [[Simply-Typed-Lambda-Terms-and-Churchs-Types|Link]]
   - Untyped $\lambda$-terms and conversion : [[Simply-Typed-Lambda-Terms-and-Churchs-Types|Link]]
   - Simple types and the order of a type : [[Simply-Typed-Lambda-Terms-and-Churchs-Types|Link]]
   - Signatures and typing judgments : [[Simply-Typed-Lambda-Terms-and-Churchs-Types|Link]]
   - Formulas as terms of type $o$ : [[Simply-Typed-Lambda-Terms-and-Churchs-Types|Link]]
   - Clausal order and polarity of subformulas : [[Simply-Typed-Lambda-Terms-and-Churchs-Types|Link]]
   - Curry's paradox : [[Simply-Typed-Lambda-Terms-and-Churchs-Types|Link]]
   - Substitution and capture-avoiding binding

3. **Sequent Calculus Proof Systems** : [[Sequent-Calculus-Proof-Systems|Link]]
   - Sequents with signatures and eigenvariables : [[Sequent-Calculus-Proof-Systems|Link]]
   - Structural, identity, and introduction rules
   - Additive and multiplicative rules : [[Sequent-Calculus-Proof-Systems|Link]]
   - Derivations and proofs : [[Sequent-Calculus-Proof-Systems|Link]]
   - Permutation of inference rules : [[Sequent-Calculus-Proof-Systems|Link]]
   - Invertible rules : [[Sequent-Calculus-Proof-Systems|Link]]
   - Frege proofs versus sequent proofs : [[Sequent-Calculus-Proof-Systems|Link]]

4. **Cut Elimination and Its Consequences** : [[Cut-Elimination-and-Its-Consequences|Link]]
   - Cut as lemma use : [[Cut-Elimination-and-Its-Consequences|Link]]
   - Consistency from cut elimination : [[Cut-Elimination-and-Its-Consequences|Link]]
   - Subformula property : [[Cut-Elimination-and-Its-Consequences|Link1]], [[Higher-Order-Quantification|Link2]]
   - Size explosion of cut-free proofs : [[Cut-Elimination-and-Its-Consequences|Link]]
   - Duality of cut and initial : [[Cut-Elimination-and-Its-Consequences|Link]]
   - Admissible versus derivable rules : [[Cut-Elimination-and-Its-Consequences|Link]]
   - Logical equivalence and replacement of subformulas : [[Cut-Elimination-and-Its-Consequences|Link]]

5. **Classical, Intuitionistic, and Minimal Logics** : [[Classical-Intuitionistic-and-Minimal-Logics|Link]]
   - C-proofs and I-proofs : [[Classical-Intuitionistic-and-Minimal-Logics|Link]]
   - Excluded middle and structural rules on the right : [[Classical-Intuitionistic-and-Minimal-Logics|Link]]
   - Atomic initial rules : [[Classical-Intuitionistic-and-Minimal-Logics|Link]]
   - Negation as implication of falsity : [[Linear-Logic|Link]]
   - Minimal logic and ex falso quodlibet : [[Classical-Intuitionistic-and-Minimal-Logics|Link]]
   - Gentzen's LK and LJ : [[Classical-Intuitionistic-and-Minimal-Logics|Link]]
   - Search choices in Gentzen's calculus : [[Classical-Intuitionistic-and-Minimal-Logics|Link]]

6. **Uniform Proofs and Abstract Logic Programming Languages** : [[Uniform-Proofs-and-Abstract-Logic-Programming-Languages|Link]]
   - Goal-directed proof search : [[Uniform-Proofs-and-Abstract-Logic-Programming-Languages|Link]]
   - Uniform proofs : [[Uniform-Proofs-and-Abstract-Logic-Programming-Languages|Link]]
   - Abstract logic programming languages : [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link1]], [[Uniform-Proofs-and-Abstract-Logic-Programming-Languages|Link2]]
   - Disjunction and existence properties : [[Uniform-Proofs-and-Abstract-Logic-Programming-Languages|Link]]
   - Harrop formulas : [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link1]], [[Uniform-Proofs-and-Abstract-Logic-Programming-Languages|Link2]]

7. **Horn Clauses and Hereditary Harrop Formulas** : [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link]]
   - First-order Horn clauses as program clauses and goals : [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link]]
   - Hereditary Harrop formulas : [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link1]], [[Uniform-Proofs-and-Abstract-Logic-Programming-Languages|Link2]]
   - Clausal order of programs : [[Simply-Typed-Lambda-Terms-and-Churchs-Types|Link1]], [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link2]], [[Operational-Semantics-in-Logic|Link3]]
   - Dynamics of proof search for fohc and fohh : [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link]]
   - Scoped clauses and modular programming : [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link]]
   - Scope extrusion in classical logic : [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link]]
   - Expressive limits of fohc and fohh : [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link]]

8. **Focused Proof Systems and Backchaining** : [[Focused-Proof-Systems-and-Backchaining|Link]]
   - Focus and the decide rule : [[Focused-Proof-Systems-and-Backchaining|Link]]
   - Right-introduction and left-introduction phases : [[Focused-Proof-Systems-and-Backchaining|Link]]
   - Paths in formulas : [[Focused-Proof-Systems-and-Backchaining|Link]]
   - Synthetic inference rules : [[Focused-Proof-Systems-and-Backchaining|Link1]], [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link2]], [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link3]]
   - Border sequents : [[Focused-Proof-Systems-and-Backchaining|Link1]], [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link2]]
   - Admissibility of initial and cut in focused systems : [[Focused-Proof-Systems-and-Backchaining|Link]]
   - Completeness of focused proofs : [[Focused-Proof-Systems-and-Backchaining|Link1]], [[Higher-Order-Quantification|Link2]]
   - Disjunctive and existential goals as nonlogical constants : [[Focused-Proof-Systems-and-Backchaining|Link]]

9. **Kripke Semantics and Canonical Models** : [[Kripke-Semantics-and-Canonical-Models|Link]]
   - Worlds and Kripke models : [[Kripke-Semantics-and-Canonical-Models|Link]]
   - Satisfaction versus provability of implication : [[Kripke-Semantics-and-Canonical-Models|Link]]
   - Canonical Kripke model : [[Kripke-Semantics-and-Canonical-Models|Link]]
   - Cut admissibility as truth coinciding with provability : [[Kripke-Semantics-and-Canonical-Models|Link]]

10. **Linear Logic** : [[Linear-Logic|Link]]
    - Resource reading of connectives : [[Linear-Logic|Link1]], [[Sequent-Calculus-Proof-Systems|Link2]]
    - Additive and multiplicative connectives : [[Sequent-Calculus-Proof-Systems|Link]]
    - Exponentials and structural rules : [[Linear-Logic|Link1]], [[Sequent-Calculus-Proof-Systems|Link2]], [[Formal-Metatheory-of-Focused-Linear-Logic|Link3]]
    - Duality and polarity : [[Linear-Logic|Link]]
    - Linear and intuitionistic implication : [[Linear-Logic|Link]]
    - One-sided and two-sided sequent systems : [[Linear-Logic|Link]]
    - Girard's translation and cut-free translations from intuitionistic logic : [[Specifying-Proof-Systems-in-a-Metalogic|Link]]
    - Origin of linear logic in LK versus LJ : [[Linear-Logic|Link]]

11. **Multi-Zone Sequents and Linear Logic Programming Languages** : [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link]]
    - Left-unbounded and left-bounded zones : [[Multiset-Rewriting-in-Linear-Logic|Link]]
    - The Lolli language
    - The Forum language
    - Multiple-conclusion uniform proofs : [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link]]
    - Conservativity over fohh
    - Lazy splitting of contexts by input and output lists : [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link]]
    - Subexponentials : [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link]]

12. **Formal Metatheory of Focused Linear Logic** : [[Formal-Metatheory-of-Focused-Linear-Logic|Link]]
    - Generalized paths and introduction phases : [[Focused-Proof-Systems-and-Backchaining|Link]]
    - Confluence of right-introduction phases : [[Focused-Proof-Systems-and-Backchaining|Link1]], [[Formal-Metatheory-of-Focused-Linear-Logic|Link2]]
    - Admissibility of generalized initial : [[Formal-Metatheory-of-Focused-Linear-Logic|Link1]], [[Focused-Proof-Systems-and-Backchaining|Link2]]
    - Four cut rules and the key cut : [[Formal-Metatheory-of-Focused-Linear-Logic|Link]]
    - Cut elimination by induction on cut measures : [[Cut-Elimination-and-Its-Consequences|Link]]
    - Soundness and completeness of focusing : [[Formal-Metatheory-of-Focused-Linear-Logic|Link]]

13. **Multiset Rewriting in Linear Logic** : [[Multiset-Rewriting-in-Linear-Logic|Link]]
    - Encoding multisets as formulas : [[Multiset-Rewriting-in-Linear-Logic|Link]]
    - Rewriting on the left : [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link1]], [[Multiset-Rewriting-in-Linear-Logic|Link2]]
    - Rewriting on the right : [[Formal-Metatheory-of-Focused-Linear-Logic|Link1]], [[Multiset-Rewriting-in-Linear-Logic|Link2]]
    - Permutation of lists : [[Cut-Elimination-and-Its-Consequences|Link1]], [[Sequent-Calculus-Proof-Systems|Link2]]
    - Numerals as multisets : [[Automata-Encoded-as-Multisets|Link1]], [[Multiset-Rewriting-in-Linear-Logic|Link2]]
    - Petri net reachability

14. **Specifying Proof Systems in a Metalogic** : [[Specifying-Proof-Systems-in-a-Metalogic|Link]]
    - Context management in theorem provers
    - Contraction-free implication rules
    - Sequents as metalevel formulas : [[Specifying-Proof-Systems-in-a-Metalogic|Link]]
    - Synthetic rules as object-level inference rules : [[Focused-Proof-Systems-and-Backchaining|Link1]], [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link2]], [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link3]]
    - Object-level cut and initial : [[Specifying-Proof-Systems-in-a-Metalogic|Link]]

15. **Higher-Order Quantification** : [[Higher-Order-Quantification|Link]]
    - Higher-order linear logic : [[Classical-Intuitionistic-and-Minimal-Logics|Link1]], [[Linear-Logic|Link2]], [[Higher-Order-Quantification|Link3]], [[Higher-Order-Programming-and-Hiding-of-Specifications|Link4]]
    - Instantiation and the loss of the subformula property : [[Cut-Elimination-and-Its-Consequences|Link1]], [[Higher-Order-Quantification|Link2]]
    - Near-focused proofs : [[Higher-Order-Quantification|Link]]
    - Cut elimination by candidates of reducibility : [[Cut-Elimination-and-Its-Consequences|Link]]
    - Definability of connectives by quantification : [[Higher-Order-Quantification|Link]]
    - Leibniz equality : [[Higher-Order-Quantification|Link]]
    - Flexible versus rigid atoms : [[Higher-Order-Quantification|Link]]
    - Higher-order Horn clauses and hereditary Harrop formulas : [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link]]

16. **Higher-Order Programming and Hiding of Specifications** : [[Higher-Order-Programming-and-Hiding-of-Specifications|Link]]
    - Higher-order predicates : [[Higher-Order-Programming-and-Hiding-of-Specifications|Link]]
    - Tactics and tacticals : [[Higher-Order-Programming-and-Hiding-of-Specifications|Link]]
    - Hiding predicates by quantification : [[Higher-Order-Programming-and-Hiding-of-Specifications|Link]]
    - Reasoning about programs with cut and substitution : [[Higher-Order-Programming-and-Hiding-of-Specifications|Link]]
    - Symmetry of reverse : [[Higher-Order-Programming-and-Hiding-of-Specifications|Link]]

17. **Automata Encoded as Multisets** : [[Automata-Encoded-as-Multisets|Link]]
    - Words as terms of type $o \to o$ : [[Simply-Typed-Lambda-Terms-and-Churchs-Types|Link]]
    - Finite automata as linear logic theories : [[Automata-Encoded-as-Multisets|Link]]
    - Pushdown automata : [[Automata-Encoded-as-Multisets|Link]]
    - Closure under homomorphism : [[Automata-Encoded-as-Multisets|Link]]
    - Alternating automata : [[Cut-Elimination-and-Its-Consequences|Link]]

18. **Collection Analysis of Horn Clauses** : [[Collection-Analysis-of-Horn-Clauses|Link]]
    - Approximating data structures by multisets and sets : [[Kripke-Semantics-and-Canonical-Models|Link]]
    - Substituting for predicates and constructors
    - Multiset and set judgments : [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link]]
    - Automated proof of collection statements
    - Approximating lists by lists : [[Collection-Analysis-of-Horn-Clauses|Link]]
    - Complexity of multiset analysis

19. **Process Calculi and Security Protocols** : [[Process-Calculi-and-Security-Protocols|Link]]
    - Par as a forum for synchronization
    - The finite $\pi$-calculus as linear logic : [[Process-Calculi-and-Security-Protocols|Link]]
    - Agent clauses and agent theories : [[Process-Calculi-and-Security-Protocols|Link]]
    - Encryption as an abstract data type
    - Needham–Schroeder shared key protocol : [[Process-Calculi-and-Security-Protocols|Link]]
    - Hiding agent states by existential quantification : [[Higher-Order-Programming-and-Hiding-of-Specifications|Link1]], [[Process-Calculi-and-Security-Protocols|Link2]]
    - Agents as nested implications : [[Process-Calculi-and-Security-Protocols|Link]]

20. **Operational Semantics in Logic** : [[Operational-Semantics-in-Logic|Link]]
    - Multiset rewriting, structural semantics, and abstract machines
    - Programs as higher-order abstract syntax : [[Operational-Semantics-in-Logic|Link]]
    - Big-step call-by-value evaluation
    - Small-step $\pi$-calculus transitions : [[Operational-Semantics-in-Logic|Link]]
    - Binary clauses and continuation passing : [[Operational-Semantics-in-Logic|Link]]
    - Abstract evaluation systems : [[Operational-Semantics-in-Logic|Link]]
    - State and concurrency in linear logic : [[Operational-Semantics-in-Logic|Link]]

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 3–10)

**Summary:** Classifies logics along two axes (quantification order and classical, intuitionistic, or linear) and places the book's niche, computation as proof search, among other ways logic specifies computation. It also states why sequent calculus replaces resolution as the foundation for logic programming.

**Key Definitions & Concepts by Section:**
- **1.1 A spectrum of logics** — first-order vs higher-order (quantifiers over primitive non-propositional types vs all types); classical logic (truth values), intuitionistic logic (constructive proof), linear logic (resources); formulas as terms of type $o$ following Church. : [[Linear-Logic|Link]]
- **1.2 Logic and the specification of computations** — computation-as-model (logic describes external structures, e.g. Hoare triples), computation-as-deduction; proof-normalization approach (state is a proof term, computing is $\beta$-reduction or cut elimination); proof-search approach (state is a sequent, computing is bottom-up proof construction). : [[Higher-Order-Programming-and-Hiding-of-Specifications|Link1]], [[Specifying-Proof-Systems-in-a-Metalogic|Link2]]
- **1.3 Proof search and logic programming** — SLD resolution as the original foundation; three objections: refutation not proof, dependence on clausal and Skolem normal forms, and most general unifiers that may not exist for typed $\lambda$-terms. : [[Uniform-Proofs-and-Abstract-Logic-Programming-Languages|Link]]
- **1.4 Designing logic programming languages** — Kowalski's equation $\text{Algorithm} = \text{Logic} + \text{Control}$; the proposal to satisfy $\text{Programming} = \text{Logic}$; Prolog's cut $!$ is a different notion from sequent-calculus cut. : [[Uniform-Proofs-and-Abstract-Logic-Programming-Languages|Link1]], [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link2]], [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link3]]
- **1.5 Why use logic to write programs?** — meaning-preserving substitution and replacement, multiple descriptions of provability, abstraction mechanisms that compose, and universally accepted semantics.
- **1.6 The structure of this book** — Part I (Chapters 1–9) is sequential; Part II (Chapters 10–13) consists of independent applications.

**Key Questions:**
1. What are the two ways of specifying computation by deduction, and which of them is "state = sequent"?
2. Why does the author consider resolution refutation an unfortunate foundation for logic programming?

---

### Chapter 2: Terms, formulas, and sequents (pp. 11–22)

**Summary:** Fixes the syntax: simply typed $\lambda$-terms in $\beta\eta$-long normal form, formulas as terms of type $o$, and sequents with typed eigenvariable signatures and multiset contexts. : [[Simply-Typed-Lambda-Terms-and-Churchs-Types|Link1]], [[Specifying-Proof-Systems-in-a-Metalogic|Link2]], [[Focused-Proof-Systems-and-Backchaining|Link3]]

**Key Definitions & Concepts by Section:**
- **2.1 Untyped $\lambda$-terms** — $\alpha$-conversion; $\beta$-redex $(\lambda x.M)N$; $\eta$-redex; capture-avoiding substitution $M[N/x]$; $\beta$-normal form $\lambda x_1\ldots\lambda x_n.(h\,t_1\cdots t_m)$ with binder, head, arguments; substitution $\theta$ applied as $s\theta$; Curry's paradox via $Y = \lambda f.(\lambda x.f(xx))(\lambda x.f(xx))$. : [[Simply-Typed-Lambda-Terms-and-Churchs-Types|Link]]
- **2.2 Types** — primitive types (sorts) $S$ and arrow types $\tau \to \sigma$; argument types and target type; $ord(\tau)=0$ if $\tau\in S$ and $ord(\tau_1\to\tau_2)=\max(ord(\tau_1)+1, ord(\tau_2))$; simple types are syntactic categories, not function spaces.
- **2.3 Signatures and typed terms** — signature $\Sigma$ as determinate set of $x:\tau$; typing judgment $\Sigma \Vdash t:\tau$ restricted to $\beta$-normal, $\eta$-long terms (so $\lambda x.x : (i\to i)\to i\to i$ is not typable but $\lambda x.\lambda y.xy$ is). : [[Simply-Typed-Lambda-Terms-and-Churchs-Types|Link]]
- **2.4 Formulas** — logical signature $\Sigma_{-1}$, non-logical signature $\Sigma_0$; quantifiers $\forall_\tau, \exists_\tau : (\tau\to o)\to o$; predicate vs function symbols; propositional, first-order, and higher-order logics; clausal order $order(B_1\supset B_2)=\max(order(B_1)+1, order(B_2))$; positive and negative subformula occurrences. : [[Focused-Proof-Systems-and-Backchaining|Link1]], [[Uniform-Proofs-and-Abstract-Logic-Programming-Languages|Link2]]
- **2.5 Sequents** — sequent $\Sigma :: \Gamma \vdash \Delta$; one-sided vs two-sided; multisets as default; eigenvariables bound over a sequent; matching $B,\Gamma'$ and $\Gamma',\Gamma''$ against lists, multisets, and sets. : [[Classical-Intuitionistic-and-Minimal-Logics|Link]]
- **2.6 Bibliographic notes** — Church's Simple Theory of Types vs the Elementary Theory of Types; differences from Gentzen (arrow notation, multisets, locally bound eigenvariables). : [[Automata-Encoded-as-Multisets|Link1]], [[Sequent-Calculus-Proof-Systems|Link2]]

**Key Questions:**
1. Why are only $\beta$-normal, $\eta$-long terms given types, and what does that do to the identification of formulas with terms?
2. How do clausal order and polarity differ, and which one governs the shape of program clauses later on?

---

### Chapter 3: Sequent calculus proof rules (pp. 23–38)

**Summary:** Introduces sequent calculus proofs as the abstract execution model, the three classes of rules, additive and multiplicative treatment of contexts, permutations and invertibility, and the first discussion of focusing and cut elimination. : [[Sequent-Calculus-Proof-Systems|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 Sequent calculus and proof search** — a sequent as a "sheet of paper" with assumptions above and goal below; multiple-conclusion reading $\forall\bar x.[(B_1\wedge B_2\wedge B_3)\supset(C_1\vee C_2)]$. : [[Sequent-Calculus-Proof-Systems|Link]]
- **3.2 Inference rules** — structural rules (exchange, contraction $cL/cR$, weakening $wL/wR$); identity rules $init$ and $cut$ (reflexivity and transitivity of $\vdash$); introduction rules with left and right versions; $\forall R$ moves a binder from the sequent (eigenvariable) to the formula; no axioms, only initial sequents. : [[Focused-Proof-Systems-and-Backchaining|Link1]], [[Higher-Order-Programming-and-Hiding-of-Specifications|Link2]], [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link3]], [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link4]]
- **3.3 Additive and multiplicative rules** — subject occurrence vs context occurrence; additive (context copied to every premise), multiplicative (context split); cost trade-off in proof building vs proof search. : [[Sequent-Calculus-Proof-Systems|Link]]
- **3.4 Sequent calculus proofs** — derivation, proof, endsequent, open leaf; $\Sigma :: \Gamma \vdash_{\mathcal X} \Delta$. : [[Sequent-Calculus-Proof-Systems|Link]]
- **3.5 Permutations of inference rules** — rules that permute prune redundant search; invertible rule (conclusion provable implies all premises provable). : [[Sequent-Calculus-Proof-Systems|Link]]
- **3.6 Focused and unfocused proof systems** — goal-reduction and backchaining phases, uniform proofs, Andreoli's invertible vs non-invertible phases; focus marked with $\Downarrow$. : [[Focused-Proof-Systems-and-Backchaining|Link]]
- **3.7 Cut-elimination and its consequences** — cut as lemma; cut-elimination theorem; consistency; subformula property (fails in higher-order); hyperexponential growth of cut-free proofs; cut-free proofs as computation traces; reasoning about programs by cut elimination. : [[Cut-Elimination-and-Its-Consequences|Link]]
- **3.8 Bibliographic notes** — Statman's hyperexponential blow-up; focused proofs used to prove cut elimination. : [[Automata-Encoded-as-Multisets|Link1]], [[Sequent-Calculus-Proof-Systems|Link2]]

**Key Questions:**
1. Why is the multiplicative treatment of contexts cheap for building proofs but expensive for searching proofs?
2. How does cut elimination yield consistency, and why does the author say cut-free proofs are computation traces rather than mathematical arguments?

---

### Chapter 4: Classical and intuitionistic logics (pp. 39–59)

**Summary:** Presents C-proofs and I-proofs as variants of Gentzen's LK and LJ, characterizes intuitionistic provability as the absence of right structural rules plus a restriction on $\supset L$ and cut, and examines identity elimination, invertibility, and the choices that make naive proof search unmanageable. : [[Classical-Intuitionistic-and-Minimal-Logics|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Classical and intuitionistic inference rules** — connectives $\{f, t, \wedge, \vee, \supset, \forall, \exists\}$; C-proof (multiple-conclusion) and I-proof (single-conclusion, no $cR$ or $wR$, right formula moves to the right premise of $\supset L$ and cut); excluded-middle proof uses $wR$ and $cR$; signature inhabiting the set of types. : [[Classical-Intuitionistic-and-Minimal-Logics|Link1]], [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link2]]
- **4.2 The identity rules and their elimination** — atomic initial rules suffice; cut-elimination case analysis (conjunction, implication, universal); "tonk" connective; definitions breaking cut elimination. : [[Formal-Metatheory-of-Focused-Linear-Logic|Link]]
- **4.3 Cut elimination and its consequences** — Gentzen's theorem; duality of $init$ and $cut$ through $B\supset B$; exponential size blow-up for $p(f^{2^n}a)$; logical equivalence $B\equiv C$ and replacement of subformulas; invertibility of $tR, \vee L, \wedge R, fL, \forall R, \exists L, \supset R$ proved from cut. : [[Cut-Elimination-and-Its-Consequences|Link]]
- **4.4 Derivable and admissible rules** — derivable rule built from primitives; admissible rule leaves the set of provable sequents unchanged; strengthening; $instan$ rule at the level of terms. : [[Cut-Elimination-and-Its-Consequences|Link]]
- **4.5 Negation, false, and minimal logic** — $\neg B$ abbreviates $B\supset f$; Gentzen's LJ with negation translates to I-proofs; M-proofs omit $fL$. : [[Classical-Intuitionistic-and-Minimal-Logics|Link]]
- **4.6 Choices to consider during the search for proofs** — choices from cut, structural rules, which formula to introduce, and term instantiation; don't-know vs don't-care nondeterminism.
- **4.7 Bibliographic notes** — Ketonen on invertibility, undecidability of first-order logic, co-NP completeness of classical propositional and PSPACE completeness of intuitionistic propositional logic. : [[Automata-Encoded-as-Multisets|Link1]], [[Sequent-Calculus-Proof-Systems|Link2]]

**Key Questions:**
1. Which two restrictions on a C-proof make it an I-proof, and what do they anticipate about linear logic?
2. What is the difference between a derivable and an admissible rule, and how is cut elimination phrased in those terms?

---

### Chapter 5: Two abstract logic programming languages (pp. 61–104)

**Summary:** Defines uniform proofs and abstract logic programming languages, shows that first-order Horn clauses (fohc) and first-order hereditary Harrop formulas (fohh) qualify, then develops the focused $\Downarrow$fohh system, its cut elimination and completeness, a canonical Kripke model, synthetic inference rules, and the expressive limits of both languages. : [[Uniform-Proofs-and-Abstract-Logic-Programming-Languages|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Goal-directed proof search** — program $P$, goal $G$, state $\Sigma :: P \vdash G$; uniform proof (non-atomic right side is concluded by a right-introduction rule); abstract logic programming language $\langle \mathcal D, \mathcal G, \vdash_{\mathcal X}\rangle$; disjunction and existence properties. : [[Uniform-Proofs-and-Abstract-Logic-Programming-Languages|Link]]
- **5.2 Horn clauses** — classical definition with at most one positive literal; $G ::= A \mid G\wedge G$, $D ::= A \mid G\supset A \mid \forall x.D$ and richer variants (5.2), (5.3); curry/uncurry equivalences; Proposition 5.5: Horn sequents classically provable are intuitionistically provable. : [[Collection-Analysis-of-Horn-Clauses|Link1]], [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link2]], [[Uniform-Proofs-and-Abstract-Logic-Programming-Languages|Link3]]
- **5.3 Hereditary Harrop formulas** — $G ::= A \mid G\wedge G \mid D\supset G \mid \forall x.G$ and $D ::= A \mid G\supset A \mid \forall x.D$ (mutual recursion, negative subformulas of $G$ are $D$); fohh as abstract logic programming language; Harrop formulas. : [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link1]], [[Uniform-Proofs-and-Abstract-Logic-Programming-Languages|Link2]]
- **5.4 Backchaining as focused rule application** — $\Downarrow$fohh sequents $\Sigma :: P \Downarrow D \vdash A$; $decide$ rule; right-introduction phase (goal reduction), left-introduction phase (backchaining); soundness; focused proofs need not be smallest.
- **5.5 Completeness of focused proofs** — $\mathcal L_0=\{t,\wedge,\supset,\forall\}$; paths $B \uparrow P$ with target, arguments, and bound variables; Propositions 5.19 and 5.20 (phases described by paths); admissibility of initial (Thm 5.22); cut and key cut $cut_k$ and the measure on cut formulas (Lemmas 5.24–5.27); cut elimination (Thm 5.28) and completeness (Thm 5.29). : [[Focused-Proof-Systems-and-Backchaining|Link1]], [[Higher-Order-Quantification|Link2]]
- **5.6 A canonical Kripke model** — worlds $\langle\Sigma,P\rangle$ ordered by inclusion; satisfaction clauses for $\supset$ and $\forall$; canonical model whose atoms are cut-free provable; Lemma 5.32: cut and $instan$ admissible iff truth equals provability. : [[Kripke-Semantics-and-Canonical-Models|Link]]
- **5.7 Synthetic inference rules** — $|\Gamma|_\Sigma$ set of pairs $\langle\Delta,D\rangle$ and the $BC$ rule; border sequents; clauses of order at most 2 yield rules mentioning only atoms. : [[Focused-Proof-Systems-and-Backchaining|Link1]], [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link2]], [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link3]]
- **5.8 Disjunctive and existential goals** — encoding $\vee$ and $\exists$ with nonlogical constants $\hat\vee$ and $\hat\exists_\tau$ and Horn clauses; Proposition 5.38 completeness for fohh. : [[Focused-Proof-Systems-and-Backchaining|Link]]
- **5.9–5.12 Examples and dynamics** — fohc programs for arithmetic, lists, sorting, graphs; fohh sterile-jar and reverse examples; modular goals $misc \supset ((classify\supset G_1)\wedge\ldots)$; fohc keeps signature and program fixed while fohh lets both grow; eigenvariables act as scoped constants.
- **5.13 Limitations** — monotonicity prevents expressing maximum of a multiset in left context, non-reachability, substitution of all occurrences, and signature-independent inequality. : [[Process-Calculi-and-Security-Protocols|Link]]
- **5.14 Bibliographic notes** — LJF and polarity of atoms (backchaining vs forward chaining), Harrop's disjunction property, Teyjus and Elpi implementations, programs as inductive definitions. : [[Automata-Encoded-as-Multisets|Link1]], [[Sequent-Calculus-Proof-Systems|Link2]]

**Key Questions:**
1. What property of $\mathcal L_0$-formulas lets a left-introduction phase be described by a path, and how is that used to prove admissibility of initial and cut?
2. Why can fohh not specify non-reachability in a graph given by atomic facts, and what change of perspective on programs would fix it?
3. How does the canonical Kripke model show that cut admissibility and the coincidence of truth with provability are the same statement?

---

### Chapter 6: Linear logic (pp. 105–136)

**Summary:** Motivates linear logic from the role of structural rules in LK vs LJ, presents its sequent calculus, polarity, and implications, introduces two-zone sequents to define Lolli ($\mathcal L_1$) and Forum ($\mathcal L_2$) as abstract logic programming languages, and shows a lazy-splitting model of resource consumption. : [[Automata-Encoded-as-Multisets|Link1]], [[Classical-Intuitionistic-and-Minimal-Logics|Link2]], [[Collection-Analysis-of-Horn-Clauses|Link3]], [[Formal-Metatheory-of-Focused-Linear-Logic|Link4]]

**Key Definitions & Concepts by Section:**
- **6.1 Reflections on the structural inference rules** — controlling contraction gives decidability; invertible rules never need contraction; additive vs multiplicative connectives; collision of cut with contraction and weakening makes cut elimination nondeterministic. : [[Sequent-Calculus-Proof-Systems|Link]]
- **6.2 LK vs LJ: an origin story** — intuitionistic implication hides $!$: $B\supset C$ reads as $(!B)\multimap C$; $!$ and $?$ mark formulas that may be weakened and contracted. : [[Linear-Logic|Link]]
- **6.3 Sequent calculus proof systems for linear logic** — proof system $L$; resource reading (fonts example) of $\otimes$ and $\&$; MALL connectives $\top,1,0,\bot,\&,\otimes,\oplus,\mathbin{⅋}$; exponentials with $!W,!C,!D,!R$ and $?W,?C,?D,?L$ (dereliction and promotion); equivalences $!(B\&C)\dashv\vdash !B\otimes !C$; seven exponential prefixes; De Morgan duality and negation normal form; one-sided system; polarity (negative: $\bot,\top,\mathbin{⅋},\&,\forall,?$; positive: $1,0,\otimes,\oplus,\exists,!$); linear implication $B\multimap C = B^\perp \mathbin{⅋} C$ and intuitionistic implication $B\Rightarrow C=(!B)\multimap C$. : [[Sequent-Calculus-Proof-Systems|Link]]
- **6.4 Introducing zones into sequents** — $\Sigma :: \Psi;\Gamma \vdash B$ with left-unbounded zone $\Psi$ and left-bounded zone $\Gamma$; proof system $P$ for $\mathcal L_1=\{\top,\&,\multimap,\Rightarrow,\forall\}$; $absorb$ rule; $\Downarrow\mathcal L_1$ with $decide_!$ and $decide_l$; backchaining as $BC$; bounded zone changes arbitrarily during search. : [[Classical-Intuitionistic-and-Minimal-Logics|Link]]
- **6.5 Embedding fohh into linear logic** — Lolli $=\langle\mathcal L_1,\mathcal L_1,\vdash_L\rangle$; Girard's translation $(\cdot)^0$; cut-free translations $(\cdot)^+$ and $(\cdot)^-$ (Prolog comma becomes $\otimes$, $:-$ the converse of $\multimap$). : [[Process-Calculi-and-Security-Protocols|Link1]], [[Multiset-Rewriting-in-Linear-Logic|Link2]], [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link3]], [[Collection-Analysis-of-Horn-Clauses|Link4]]
- **6.6 A model of resource consumption** — lazy splitting with $[I\parallel O]$ input and output lists of option formulas, $pick$ and $subcontext$; IO proof system sound (Prop. 6.19).
- **6.7 Multiple-conclusion uniform proofs** — $\mathcal L_2=\mathcal L_1\cup\{\bot,\mathbin{⅋},?\}$ (Forum); $\Downarrow\mathcal L_2$ sequents $\Sigma :: \Psi;\Gamma\vdash\Delta;\Upsilon$ with four zones; right rules additive and permutable, left rules multiplicative; $decide_?$ and $init_?$. : [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link]]
- **6.8 Conservativity results** — $\Downarrow\mathcal L_2$ conservative over $\Downarrow\mathcal L_1$ and $\Downarrow\mathcal L_0$.
- **6.9 Generalizing synthetic inference rules** — switch toggling as the synthetic rules from $step1 :- off, on \multimap step2$ or $step1 \parallel off :- on \parallel step2$. : [[Focused-Proof-Systems-and-Backchaining|Link1]], [[Horn-Clauses-and-Hereditary-Harrop-Formulas|Link2]], [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link3]]
- **6.10 Bibliographic notes** — Lafont's restaurant semantics, polarity (Andreoli, Girard), subexponentials, multifocusing, classical vs intuitionistic linear logic. : [[Automata-Encoded-as-Multisets|Link1]], [[Sequent-Calculus-Proof-Systems|Link2]]

**Key Questions:**
1. How does the shape of I-proofs motivate $!$ and $?$ and explain why $\supset L$ is special among intuitionistic rules?
2. What does polarity say about which introduction rules need information from an oracle, and how does this classify atoms and exponentials?
3. Why do the two zones make $\Rightarrow$ and $\multimap$ available as proper connectives with one-connective-per-rule introduction rules?

---

### Chapter 7: Formal properties of linear logic focused proofs (pp. 139–165)

**Summary:** Proves, following the plan of Section 5.5, that $\Downarrow\mathcal L_2$ admits generalized initial and four cut rules, eliminates cut, and is sound and complete for the unfocused system $L$, yielding cut elimination for $L$. : [[Formal-Metatheory-of-Focused-Linear-Logic|Link1]], [[Linear-Logic|Link2]]

**Key Definitions & Concepts by Section:**
- **7.1 Generalized paths and introduction phases** — paths with normal form $\forall\bar x.[C_1\Rightarrow\cdots\Rightarrow C_n\Rightarrow B_1\multimap\cdots\multimap B_m\multimap A_1\mathbin{⅋}\cdots\mathbin{⅋} A_p\mathbin{⅋} ?E_1\mathbin{⅋}\cdots\mathbin{⅋} ?E_q]$ (intuitionistic arguments, linear arguments, atomic targets, $?$-targets); right-introduction phase as a confluent, terminating rewriting of multisets of sequents (Prop. 7.1); phases described by paths (Props. 7.2, 7.3). : [[Focused-Proof-Systems-and-Backchaining|Link]]
- **7.2 Admissibility of the general initial rule** — Theorem 7.4: $B$ proves $B$, members of $\Psi$ or $\Upsilon$ are provable on the right or left. : [[Formal-Metatheory-of-Focused-Linear-Logic|Link]]
- **7.3 Cut rules and cut elimination** — $cut_!$, $cut_?$, $cut_l$, key cut $cut_k$; special status of $?$; thread, rank, and measure $\langle d,q,w\rangle$ in lexicographic order; Lemmas 7.9–7.14; Theorem 7.15; no collision of cut with weakening in focused systems. : [[Formal-Metatheory-of-Focused-Linear-Logic|Link]]
- **7.4 The focused proof system is sound and complete** — translations $(\cdot)^\triangledown$ and $(\cdot)^\blacktriangledown$ from $L$-formulas to $\mathcal L_2$; soundness (Prop. 7.16); invertibility of right rules (Lemma 7.17); completeness (Thm 7.18); cut elimination for $L$ (Thm 7.19). : [[Focused-Proof-Systems-and-Backchaining|Link]]
- **7.5 Bibliographic notes** — Andreoli's one-sided focused system with asynchronous and synchronous phases; Chaudhuri's admissibility-based proof style; mechanized proofs by Felty et al. : [[Automata-Encoded-as-Multisets|Link1]], [[Sequent-Calculus-Proof-Systems|Link2]]

**Key Questions:**
1. Why does the measure for cut elimination include the number of $cut_?$ occurrences and the rank, not only the cut formula degree?
2. How is completeness of focusing derived from admissibility of generalized initial and cut?

---

### Chapter 8: Linear logic programming (pp. 167–180)

**Summary:** Shows small Lolli and Forum programs: permuting lists by loading and unloading the bounded zone, multiset rewriting on either side, contraction-free theorem provers, and encodings of sequent calculi in $\mathcal L_2$. : [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link]]

**Key Definitions & Concepts by Section:**
- **8.1 Encoding multisets as formulas** — conjunctive encoding ($1$, $\otimes$, left side) vs disjunctive encoding ($\bot$, $\mathbin{⅋}$, right side); multiset inclusion as $S \mathbin{⅋} 0 \multimap T$ or $\exists q.(S\mathbin{⅋} q\multimap T)$. : [[Multiset-Rewriting-in-Linear-Logic|Link]]
- **8.2 A syntax for Lolli programs** — $\Rightarrow$ as ``=>'', $\multimap$ as ``-o'', $\&$, $\top$ as ``erase'', and positive connectives defined via clauses for $true$, comma, semicolon, $exists$, $bang$. : [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link1]], [[Operational-Semantics-in-Logic|Link2]], [[Specifying-Proof-Systems-in-a-Metalogic|Link3]]
- **8.3 Permuting a list** — $load$ and $unload$ with $item$ atoms; $perm\ L\ K \Leftarrow load\ L\ K$ forces an empty bounded zone via $!$. : [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link]]
- **8.4 Multiset rewriting on the left** — rewrite system $H=\{\langle L_i,R_i\rangle\}$, relation $M\Longrightarrow_H N$; encoding by $rew$ clauses. : [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link]]
- **8.5 Context management in a theorem prover** — intuitionistic metalogic keeps hypotheses too long; Lolli specification of G3ip and the contraction-free G4ip replacement rules ($\supset L_1$–$\supset L_4$) giving a decision procedure.
- **8.6 Multiset rewriting on the right** — clause $a\mathbin{⅋} b \multimap c\mathbin{⅋} d\mathbin{⅋} e$; subgoals right of $\Leftarrow$ get empty bounded zones; $sumall$ and $acc$. : [[Multi-Zone-Sequents-and-Linear-Logic-Programming-Languages|Link1]], [[Multiset-Rewriting-in-Linear-Logic|Link2]]
- **8.7 Specification of sequent calculus proof systems** — object sequents encoded with $\lfloor\cdot\rfloor$, $\lceil\cdot\rceil$ and $?$ marking contractible formulas; set $J$ for intuitionistic logic; synthetic rules reproduce the object-level rules; $\Leftarrow$ vs $\multimap$ in $cut$ and $\supset L$. : [[Sequent-Calculus-Proof-Systems|Link]]
- **8.8 Bibliographic notes** — Gamma, chemical abstract machine, Petri nets, Lygon, ACL, parsing with gap threading. : [[Automata-Encoded-as-Multisets|Link1]], [[Sequent-Calculus-Proof-Systems|Link2]]

**Key Questions:**
1. How does placing a goal under $!$ force the bounded zone to be empty, and why is this needed for $perm$?
2. How do $\Leftarrow$ and $\multimap$ differ in the specification of object-level cut?

---

### Chapter 9: Higher-order quantification (pp. 181–208)

**Summary:** Extends $\mathcal L_2$ to quantification at all types ($\mathcal L_2^\omega$), explains why instantiation breaks focusing and the subformula property, introduces near-focused proofs to recover a focused system, and shows higher-order programming and hiding of predicates by quantification. : [[Higher-Order-Quantification|Link]]

**Key Definitions & Concepts by Section:**
- **9.1 Introduction** — logic with $\forall_\tau$ for arbitrary $\tau$; Gödel incompleteness irrelevant since meaning is given by proof systems; consistency by cut admissibility via Girard's candidates of reducibility; instantiating $\forall p.\,p\Rightarrow p$ can grow formulas; subformula property trivialized; connectives can occur inside nonlogical contexts.
- **9.2 Higher-order quantification** — $C^\omega$ and $I^\omega$; $\forall_o P.P \equiv f$; $\forall_o p.(p\supset p)$ simulates cut; Leibniz equality $\forall P.(P\,t\supset P\,s)$. : [[Higher-Order-Quantification|Link]]
- **9.3 Near-focused proofs** — proof system $\Downarrow N$ allowing nonatomic $init$ and decide; atomic instances; Lemmas 9.5–9.8; Proposition 9.9: near-focused proofs convert to $\Downarrow\mathcal L_2^\omega$ proofs; Corollary 9.10. : [[Higher-Order-Quantification|Link]]
- **9.4 The proof theory of higher-order quantification** — substitution (Lemma 9.11, Prop. 9.12); cut elimination for $\Downarrow N^+$ (Thm 9.13, not proved) and cut admissibility for $\Downarrow\mathcal L_2^\omega$ (Thm 9.14). : [[Higher-Order-Quantification|Link]]
- **9.5 Examples using quantification of type $o$** — $0\dashv\vdash\forall p.p$, $\top\dashv\vdash\exists p.p$, $1\dashv\vdash\forall p.p\multimap p$, $\bot\dashv\vdash\exists p.p\otimes p^\perp$, definitions of $\&$ and $\oplus$; Leibniz equality with $\Rightarrow$ or $\multimap$. : [[Higher-Order-Programming-and-Hiding-of-Specifications|Link]]
- **9.6 Higher-order programming** — $forevery$, $forsome$, $mappred$, $sublist$, closures; goals as $trueg$, $cc$, $allg$; tactics as relations on goals; tacticals $maptac$, $then$, $orelse$, $repeat$. : [[Higher-Order-Programming-and-Hiding-of-Specifications|Link]]
- **9.7 Proving that reverse is symmetric** — specification with hidden $rv$; instantiate with $\lambda x\lambda y.(rv\,y\,x)^\perp$; contrapositive; no induction needed.
- **9.8 Exploiting the hiding of specification details** — hiding $rev$ with $\forall rev$; instantiating it to obtain a different specification of reverse. : [[Higher-Order-Programming-and-Hiding-of-Specifications|Link]]
- **9.9 Synthetic rules and higher-order logic** — clausal order and atomicity not stable under instantiation; rigid vs flexible atoms; higher-order Horn clauses and hereditary Harrop formulas defined with rigid heads. : [[Focused-Proof-Systems-and-Backchaining|Link]]
- **9.10 Bibliographic notes** — Huet's unification, TPS, Isabelle, Elf, higher-order pattern unification and decidability, cut simulation, extensional vs non-extensional models. : [[Automata-Encoded-as-Multisets|Link1]], [[Sequent-Calculus-Proof-Systems|Link2]]

**Key Questions:**
1. Why do atomic initial and the atomic-right-zone invariant fail under substitution of predicate variables, and how do near-focused proofs repair this?
2. How can instantiating a hidden predicate with a negated, argument-swapped formula prove symmetry of reverse without induction?
3. Why must the heads of higher-order Horn clauses be rigid?

---

### Chapter 10: Specifying computations using multisets (pp. 209–220)

**Summary:** Encodes numerals, words, finite automata, and pushdown automata with multiset rewriting in $\mathcal L_2^\omega$ and proves faithfulness of the finite automaton encoding. : [[Computation-as-Proof-Search|Link1]], [[Specifying-Proof-Systems-in-a-Metalogic|Link2]], [[Process-Calculi-and-Security-Protocols|Link3]]

**Key Definitions & Concepts by Section:**
- **10.1 Numerals as multisets** — Church-style numerals as atoms $succ^n(zero)$; $\star^n$ as multiplicity; Fibonacci program $f\,z$, $f(s\,z)\mathbin{⅋}\star$, $\forall x.(f\,x\multimap f(s\,x)\multimap f(s(s\,x)))$; arithmetic with $star$ tokens. : [[Automata-Encoded-as-Multisets|Link1]], [[Multiset-Rewriting-in-Linear-Logic|Link2]]
- **10.2 Letters and words** — letters of type $o\to o$, words as $\lambda x.(u(v(u\,x)))$; concatenation as composition. : [[Automata-Encoded-as-Multisets|Link]]
- **10.3 Encoding finite automata** — $F=\langle Q,\Lambda,\delta,s,F\rangle$ with $\delta\subseteq Q\times\Lambda^*\times Q$; theory $T(\delta)$ with clauses $\forall x.[q\mathbin{⅋} x\multimap p\mathbin{⅋}(w\,x)]$; Prop. 10.4: $p\xrightarrow{w}{}^* q$ iff the clause for $w$ is provable, and acceptance via $(f_1\&\cdots\&f_n)$. : [[Automata-Encoded-as-Multisets|Link]]
- **10.4 Properties about finite automata** — closure under homomorphism (Prop. 10.6) by substituting eigenvariables for letters; splitting transitions with an existential state; nondeterminism as $\oplus$ and alternating automata as $\&$.
- **10.5 Encoding pushdown automata** — $\delta\subseteq Q\times\Lambda^*\times\Omega^*\times Q\times\Omega^*$; clause $\forall x\forall y.[q\mathbin{⅋} x\mathbin{⅋}(\gamma' y)\multimap p\mathbin{⅋}(w\,x)\mathbin{⅋}(\gamma\,y)]$. : [[Automata-Encoded-as-Multisets|Link]]
- **10.6 Bibliographic notes** — Kanovich on Fibonacci and machine models, Huet's undecidability of third-order unification, Lambek calculus and noncommutative linear logic. : [[Automata-Encoded-as-Multisets|Link1]], [[Sequent-Calculus-Proof-Systems|Link2]]

**Key Questions:**
1. Why can letters and states both be typed $o$ or $o\to o$ without any other primitive type, and what does function composition mean on words?
2. How does substitution into proofs give closure of regular languages under homomorphism almost for free?

---

### Chapter 11: Collection analysis for Horn clauses (pp. 221–236)

**Summary:** Presents a proof-theoretic static analysis: replace list structures and predicates in a Horn program by multiset or set expressions and judgments in linear logic, and prove the resulting formulas to obtain invariants such as "sort preserves the multiset of items". : [[Collection-Analysis-of-Horn-Clauses|Link]]

**Key Definitions & Concepts by Section:**
- **11.1 Introduction** — approximate lists by multisets to establish partial correctness statically.
- **11.2 The undercurrents** — open set of analyses instead of one type system; constants and eigenvariables differ only in scope; linear logic as common substrate. : [[Collection-Analysis-of-Horn-Clauses|Link]]
- **11.3 Abstraction and substitution in proof theory** — substitution for types, for nonlogical constants (predicates mapped to formulas), and for assumptions via cut. : [[Collection-Analysis-of-Horn-Clauses|Link]]
- **11.4 Multiset approximations** — multiset expressions from $item$, $\mathbin{⅋}$, and $\bot$; judgments inclusion $\sqsubseteq$ and equality $\stackrel{m}{=}$; translations $S \mathbin{⅋} 0 \multimap T$ for inclusion and $S \dashv\vdash T$ for equality; Prop. 11.1 (provable translation implies valid statement, converse fails); substitutions $nil\mapsto\bot$, $::\ \mapsto\lambda x\lambda y.\,item\,x\mathbin{⅋} y$, $append\mapsto\lambda x\lambda y\lambda z.(x\mathbin{⅋} y)\dashv\vdash z$. : [[Collection-Analysis-of-Horn-Clauses|Link]]
- **11.5 Formalizing the method** — three steps (approximate data, assign judgments to predicates, prove translated clauses); comparison with the model-theoretic argument.
- **11.6 Set approximations** — set expressions with $\&$ and $\top$; judgments $\subseteq$ and $\stackrel{s}{=}$; sort that drops duplicates; Prop. 11.3. : [[Collection-Analysis-of-Horn-Clauses|Link]]
- **11.7 Automation of analysis** — specialized proof systems for set (Fig. 11.6) and multiset statements (Fig. 11.7); decidable for sets; multiset analysis is multiset rewriting and Petri-net reachability so TOWER-hard in the worst case.
- **11.8 List approximations** — encoding lists as $\lambda l.\,((R\,l)\multimap l)\multimap item\,x$; Prop. 11.6; few natural judgments beyond equality. : [[Collection-Analysis-of-Horn-Clauses|Link]]
- **11.9 Bibliographic notes** — typing in $\lambda$Prolog, Ciao preprocessor, set-constraint systems. : [[Automata-Encoded-as-Multisets|Link1]], [[Sequent-Calculus-Proof-Systems|Link2]]

**Key Questions:**
1. Why is proving the linear-logic translation of a multiset statement sufficient but not necessary for its validity?
2. What does cut (substitution for assumptions) contribute to turning a proof of a predicate atom into a proof of the approximating formula?

---

### Chapter 12: Encoding security protocols (pp. 237–251)

**Summary:** Uses the $\mathbin{⅋}$ connective as a rendezvous to encode concurrent processes, first the finite $\pi$-calculus (with its flaws) and then asynchronous protocols such as Needham–Schroeder, ending with agents as nested implications. : [[Process-Calculi-and-Security-Protocols|Link]]

**Key Definitions & Concepts by Section:**
- **12.1 Communicating processes** — $\mathbin{⅋}$ as forum; $\otimes$ and $\mathbin{⅋}$ as dual views of pointers and processes; $\pi$-calculus agents $\bar x z.P$, $x(y).Q$, scope restriction $(x)P$ and scope extrusion; mapping $\langle\langle\cdot\rangle\rangle$ with $send$, $get$, $or$, $match$; flaws due to $\oplus$ and $\forall x\forall y.P\,xy\vdash\forall x.P\,xx$. : [[Computation-as-Proof-Search|Link]]
- **12.2 Specifying communication protocols** — message $A\to B:M$ as network atom $N\,M$; static key distribution as $\exists$; dynamic creation as $\forall$ (new); table mapping $\mid$, units, $\to$, new, local to $\mathbin{⅋},\bot,\multimap,\forall,\exists$ (disjunctive and conjunctive styles); encryption as abstract data type with keys of type $d\to d$. : [[Process-Calculi-and-Security-Protocols|Link]]
- **12.3 Protocols as theories in linear logic** — agent state predicate $\rho_i$; agent clauses $\forall\bar x.[a_1\mathbin{⅋}\cdots\mathbin{⅋} a_m\multimap\forall\bar y.[b_1\mathbin{⅋}\cdots\mathbin{⅋} b_n]]$; agent theory $\exists\bar x[C_1\otimes\cdots\otimes C_s]$; NS protocol encoding; unification with function-variable patterns $K\,M$ shows guessing. : [[Process-Calculi-and-Security-Protocols|Link]]
- **12.4 Abstracting internal states** — hide agent states by $\exists$ over predicates; logical equivalence turns state-passing into nested $\multimap$.
- **12.5 Agents as nested implications** — grammar $H ::= A \mid \bot \mid H\mathbin{⅋} H$, $K ::= H \mid H\multimap K \mid \forall x.K$; alternation of output on the right and input on the left; agent formulas for Alice, Bob, and the server; persistent agents with $\Leftarrow$. : [[Process-Calculi-and-Security-Protocols|Link]]
- **12.6 Bibliographic notes** — Miller 1993, MSR by Cervesato et al., bipolar compilation by Andreoli. : [[Automata-Encoded-as-Multisets|Link1]], [[Sequent-Calculus-Proof-Systems|Link2]]

**Key Questions:**
1. Why is the $\pi$-calculus $+$ encoded with a nonlogical constant instead of $\oplus$?
2. How does existential quantification at predicate type remove explicit agent state predicates and yield nested implications?

---

### Chapter 13: Formalizing operational semantics (pp. 253–272)

**Summary:** Shows how three frameworks for operational semantics (multiset rewriting, structural operational semantics, abstract machines) are specified by Horn clauses, hereditary Harrop formulas, binary clauses, and linear logic, with binders handled by $\lambda$-tree syntax. : [[Operational-Semantics-in-Logic|Link]]

**Key Definitions & Concepts by Section:**
- **13.1 Three frameworks for operational semantics** — multiset rewriting (Gamma, chemical abstract machine), small-step and big-step SOS, abstract machines such as SECD; binary clauses. : [[Operational-Semantics-in-Logic|Link]]
- **13.2 The abstract syntax of programs-as-terms** — untyped $\lambda$-calculus as $tm$ with $app$ and $abs$; $\alpha$-convertible iff $\beta\eta$-convertible encodings; finite $\pi$-calculus constructors $null$, $taup$, $plus$, $par$, $match$, $out$, $nu$, $in$. : [[Operational-Semantics-in-Logic|Link]]
- **13.3 Big-step semantics** — $eval\,(app\,M\,N)\,V :- eval\,M\,(abs\,R),\ eval\,N\,U,\ eval\,(R\,U)\,V$; substitution by built-in $\beta$. : [[Operational-Semantics-in-Logic|Link]]
- **13.4 Small-step semantics** — late transition system for the finite $\pi$-calculus as clauses $D_\pi$ with free actions ($\to$) and bound actions ($\rightharpoonup$); side conditions disappear thanks to quantifier scope; adequacy (Prop. 13.1). : [[Operational-Semantics-in-Logic|Link]]
- **13.5 Binary clauses** — CPS transformation of Horn clauses, $evalc$ with a continuation; abstract evaluation systems $(\Sigma,R,\rho,S)$ with load, rewrite, unload; Krivine machine and SECD machine as binary clauses. : [[Operational-Semantics-in-Logic|Link]]
- **13.6 Linear logic** — global counter by $E_1,E_2,E_3$ with hidden register $r$ and equivalence (Prop. 13.2); references; CML-style primitives $spawn$, $newchan$, $sync$, $transmit$, $receive$, $choose$, $wrap$, $guard$, $poll$ using threads as multisets. : [[Automata-Encoded-as-Multisets|Link1]], [[Classical-Intuitionistic-and-Minimal-Logics|Link2]], [[Collection-Analysis-of-Horn-Clauses|Link3]], [[Formal-Metatheory-of-Focused-Linear-Logic|Link4]]
- **13.7 Bibliographic notes** — static vs dynamic semantics, type inference in logic programming, Hindley–Milner. : [[Automata-Encoded-as-Multisets|Link1]], [[Sequent-Calculus-Proof-Systems|Link2]]

**Key Questions:**
1. How does representing object-level binders by meta-level $\lambda$-abstraction remove the freshness side conditions of the $\pi$-calculus transition rules?
2. What does the CPS transformation to binary clauses buy for specifying side effects, and what does linear logic add on top?

---
