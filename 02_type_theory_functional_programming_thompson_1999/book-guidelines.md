# Type Theory and Functional Programming — Guidelines

## Header

**Title:** Type Theory and Functional Programming
**Author(s):** Simon Thompson
**Publication:** Addison-Wesley International Computer Science Series, 1991 (out of print; this edition is an unaltered March 1999 electronic reissue by the author, Computing Laboratory, University of Kent).

**Brief Summary:**
This book gives both a first and a second course in Per Martin-Löf's constructive type theory, developed as the system in which logic and functional programming coincide via the Curry–Howard (propositions-as-types) correspondence. It opens with short surveys of classical/constructive logic, the untyped and typed $\lambda$-calculus, and constructive mathematics, then presents the formal system of type theory itself ($TT_0$) in full, works through its metatheory (normalisation, decidability, equality), applies it at length to programming and program verification, surveys the many proposals to augment the basic system (subsets, quotients, well-founded and general recursion, inductive and co-inductive types), and closes with a foundational/comparative chapter relating type theory to proof theory, model theory, and sibling systems such as Nuprl and the Calculus of Constructions.

**Intent of the Author:**
Thompson wrote the book because, as of the early 1990s, type theory existed mainly as scattered conference and research papers, and he wanted to set down its state of development "in a form accessible to interested final-year undergraduates, graduate students, research workers and teachers." He aims not just to present the formal system but to justify it, explore its mathematical properties, and give the reader "a much more developed sense of the potential of type theory" as a unified vehicle for programming, specification, and proof.

---

## Topic List

1. **The Curry–Howard Isomorphism (Propositions as Types)** : [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Link]]
   - Judgements of the form p : P : [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Link1]], [[The-Lambda-Calculus|Link2]]
   - Proof objects for the logical connectives
   - Propositions as tasks versus a truth-functional semantics : [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Link]]
   - Formation, introduction, elimination and computation rules : [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Link]]
   - Extracting programs from constructive proofs

2. **Natural Deduction and Predicate Logic** : [[Natural-Deduction-and-Predicate-Logic|Link]]
   - Introduction and elimination rules for the connectives : [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Link]]
   - Discharge of assumptions : [[Natural-Deduction-and-Predicate-Logic|Link]]
   - Rules for the quantifiers and variable capture : [[Natural-Deduction-and-Predicate-Logic|Link]]
   - Classical extensions: excluded middle, double negation, proof by contradiction

3. **The Lambda Calculus** : [[The-Lambda-Calculus|Link]]
   - The untyped $\lambda$-calculus, reduction and normal forms
   - The Church–Rosser property : [[The-Lambda-Calculus|Link]]
   - Convertibility and $\beta$/$\eta$-conversion : [[The-Lambda-Calculus|Link1]], [[The-Formal-System-of-Type-Theory-(TT0)|Link2]], [[Contexts,-Derivability-and-Type-Uniqueness|Link3]]
   - The simply typed $\lambda$-calculus and strong normalisation : [[The-Lambda-Calculus|Link]]
   - The reducibility (Tait) method : [[The-Lambda-Calculus|Link]]

4. **Constructive Mathematics** : [[Constructive-Mathematics|Link]]
   - Existence proofs and the rejection of proof by contradiction
   - The principle of complete presentation : [[Constructive-Mathematics|Link]]
   - Constructive typing of mathematical objects : [[Constructive-Mathematics|Link]]
   - Apartness in place of inequality : [[Constructive-Mathematics|Link]]

5. **The Formal System of Type Theory ($TT_0$)** : [[The-Formal-System-of-Type-Theory-(TT0)|Link]]
   - Judgements, proofs and derivations : [[The-Formal-System-of-Type-Theory-(TT0)|Link]]
   - The four kinds of rule for each type former : [[Equality-in-Type-Theory|Link]]
   - The identity (equality) type : [[The-Formal-System-of-Type-Theory-(TT0)|Link]]
   - Convertibility and the rules of substitution : [[The-Formal-System-of-Type-Theory-(TT0)|Link]]

6. **Base Types and Data Types** : [[Base-Types-and-Data-Types|Link]]
   - Booleans and finite types : [[Base-Types-and-Data-Types|Link]]
   - The unit and empty types : [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Link]]
   - Natural numbers and primitive recursion : [[The-Lambda-Calculus|Link]]
   - Well-founded algebraic types such as trees : [[Base-Types-and-Data-Types|Link]]

7. **Quantifiers and Dependent Types** : [[Quantifiers-and-Dependent-Types|Link]]
   - The dependent function type as universal quantifier : [[Quantifiers-and-Dependent-Types|Link]]
   - The dependent sum type as existential quantifier : [[Quantifiers-and-Dependent-Types|Link]]
   - Curried versus uncurried representations : [[Quantifiers-and-Dependent-Types|Link]]
   - Weak versus strong elimination rules for disjunction and existence : [[Programming-in-Type-Theory|Link1]], [[Quantifiers-and-Dependent-Types|Link2]]

8. **Contexts, Derivability and Type Uniqueness** : [[Contexts,-Derivability-and-Type-Uniqueness|Link]]
   - Assumptions, discharge and consistency of contexts : [[Contexts,-Derivability-and-Type-Uniqueness|Link]]
   - Naming and abbreviation conventions : [[Contexts,-Derivability-and-Type-Uniqueness|Link]]
   - Derivability of "A is a type" from "a : A" : [[Contexts,-Derivability-and-Type-Uniqueness|Link]]
   - Uniqueness of types : [[Contexts,-Derivability-and-Type-Uniqueness|Link]]

9. **Normalisation and Computational Properties** : [[Normalisation-and-Computational-Properties|Link]]
   - Restricted reduction and the system $TT_0^*$ : [[Normalisation-and-Computational-Properties|Link]]
   - Combinator and supercombinator abstraction; the system $TT_0^c$ : [[Normalisation-and-Computational-Properties|Link]]
   - The normalisation theorem and its corollaries : [[Normalisation-and-Computational-Properties|Link]]
   - Decidability of convertibility and of derivability

10. **Equality in Type Theory** : [[Equality-in-Type-Theory|Link]]
    - Definitional equality, convertibility, and the identity type : [[Equality-in-Type-Theory|Link1]], [[The-Formal-System-of-Type-Theory-(TT0)|Link2]]
    - Equality functions and formal decidability : [[Programming-in-Type-Theory|Link]]
    - Extensional equality defined inside an intensional theory : [[Equality-in-Type-Theory|Link]]
    - Martin-Löf's extensional identity rule and its cost : [[Equality-in-Type-Theory|Link]]

11. **Universes and Well-Founded Types** : [[Universes-and-Well-Founded-Types|Link]]
    - The hierarchy of universes and Girard's paradox
    - Type families and quantification over a universe : [[Universes-and-Well-Founded-Types|Link]]
    - Closure axioms and parametricity : [[Universes-and-Well-Founded-Types|Link]]
    - The W type and its relation to algebraic types : [[Universes-and-Well-Founded-Types|Link]]

12. **Programming in Type Theory** : [[Programming-in-Type-Theory|Link]]
    - Course-of-values recursion : [[Programming-in-Type-Theory|Link]]
    - Verified program development
    - Dependent types for vectors, modules and type classes
    - Program transformation and tail-recursive (imperative) form : [[Programming-in-Type-Theory|Link]]

13. **Specification in Type Theory** : [[Specification-in-Type-Theory|Link]]
    - What a specification is : [[Specification-in-Type-Theory|Link]]
    - Skolemising the quantifiers of a specification : [[Specification-in-Type-Theory|Link]]
    - Computational irrelevance and lazy evaluation : [[Specification-in-Type-Theory|Link]]
    - Proof extraction and top-down derivation : [[Specification-in-Type-Theory|Link]]

14. **The Subset Type and Its Difficulties** : [[The-Subset-Type-and-Its-Difficulties|Link]]
    - The naive subset type and its weak elimination rule : [[The-Subset-Type-and-Its-Difficulties|Link]]
    - Non-derivability results for subset comprehension : [[The-Formal-System-of-Type-Theory-(TT0)|Link]]
    - Propositions as distinct from types : [[The-Subset-Type-and-Its-Difficulties|Link]]
    - Whether subsets are necessary at all : [[The-Subset-Type-and-Its-Difficulties|Link]]

15. **Quotient and Congruence Types** : [[Quotient-and-Congruence-Types|Link]]
    - The quotient type formed from a base type and an equivalence relation
    - Congruence types : [[Quotient-and-Congruence-Types|Link]]
    - Case study: the rationals and the constructive real numbers : [[Quotient-and-Congruence-Types|Link]]

16. **Strengthened and Polymorphic Rules** : [[Strengthened-and-Polymorphic-Rules|Link]]
    - Strong elimination rules and hypothetical hypotheses : [[The-Inversion-Principle|Link1]], [[Programming-in-Type-Theory|Link2]], [[Quantifiers-and-Dependent-Types|Link3]], [[Strengthened-and-Polymorphic-Rules|Link4]]
    - The polymorphic type constructor : [[Strengthened-and-Polymorphic-Rules|Link]]
    - Non-termination introduced by extensional polymorphism : [[Strengthened-and-Polymorphic-Rules|Link1]], [[The-Subset-Type-and-Its-Difficulties|Link2]], [[Quantifiers-and-Dependent-Types|Link3]]

17. **Well-Founded and General Recursion** : [[Well-Founded-and-General-Recursion|Link]]
    - Well-founded orderings and the accessible part of a relation : [[Well-Founded-and-General-Recursion|Link]]
    - Adding well-founded recursion to type theory : [[Well-Founded-and-General-Recursion|Link]]
    - Inductively defined types as least fixed points : [[Well-Founded-and-General-Recursion|Link]]
    - Co-inductive types, streams and partial objects : [[Well-Founded-and-General-Recursion|Link1]], [[The-Lambda-Calculus|Link2]]

18. **Foundations and Related Systems** : [[Foundations-and-Related-Systems|Link]]
    - Realizability and conservativity over Heyting Arithmetic
    - Model theory: term models, type-free interpretations, inductive definitions
    - The inversion principle relating introduction and elimination rules
    - Related systems: Nuprl, TK, PX, AUTOMATH, System F, the Calculus of Constructions

---

## Chapter Summaries

### Introduction (pp. 1–6)

**Summary:** Motivates constructive type theory by arguing that correct programming requires a more expressive type system, one strong enough to state full logical specifications, and that constructive logic's demand for evidence (rather than truth-functional validity) supplies exactly this, via the Curry–Howard identification of propositions with types and proofs with programs.

**Key Definitions & Concepts:**
- Correctness by construction versus post-hoc verification; the analogy with static type-checking
- The constructive (proof-functional) reading of $\wedge$, $\Rightarrow$, $\vee$, $\neg$, $\forall$, $\exists$
- The judgement $p:P$ read as "p is a proof of P" and "p is a member of type P"
- The dependent function type $(\forall x:A).B(x)$ and dependent sum type $(\exists x:A).B(x)$
- Programs-from-proofs and the misleading reading of $p:P$ as "p meets specification P" for arbitrary P

**Key Questions:**
1. Why does a simple typing like $plus : N \Rightarrow N \Rightarrow N$ fail to be an adequate *specification* of addition, even though it is a perfectly good *type*?
2. How does insisting that every type contains at least one value (under general recursion) conflict with the goal of guaranteed total correctness?

---

### Chapter 1: Introduction to Logic (pp. 7–28)

**Summary:** Gives a self-contained natural-deduction presentation of propositional and predicate logic, establishing the notation, the discharge-of-assumptions mechanism, and the treatment of bound variables and substitution that the rest of the book reuses for type theory. : [[Natural-Deduction-and-Predicate-Logic|Link1]], [[The-Subset-Type-and-Its-Difficulties|Link2]], [[Quantifiers-and-Dependent-Types|Link3]]

**Key Definitions & Concepts by Section:**
- **1.1 Propositional Logic** — formulas built from $\wedge, \Rightarrow, \vee, \bot, \Leftrightarrow, \neg$; the Assumption rule; introduction/elimination rules for $\wedge$, $\Rightarrow$, $\vee$; discharge of assumptions and labelling; $\bot$-elimination (ex falso quodlibet); classical extensions — excluded middle, double negation, proof by contradiction : [[Natural-Deduction-and-Predicate-Logic|Link]]
- **1.2 Predicate Logic** — terms and atomic formulas; the quantifiers $\forall$, $\exists$ : [[Natural-Deduction-and-Predicate-Logic|Link]]
  - **1.2.1 Variables and substitution** — bound vs. free occurrences; variable capture and its avoidance; the substitution notation $A[t/x]$ : [[Natural-Deduction-and-Predicate-Logic|Link]]
  - **1.2.2 Quantifier rules** — the "arbitrary variable" reading behind $\forall$-introduction; $\forall$-elimination; $\exists$-introduction and $\exists$-elimination with its side condition; the reading of $\forall/\exists$ as infinite conjunction/disjunction : [[Natural-Deduction-and-Predicate-Logic|Link]]
  - **1.2.3 Examples** — worked derivations including the reordering-of-quantifiers example $\exists y.\forall x.A(x,y) \Rightarrow \forall x.\exists y.A(x,y)$ : [[Natural-Deduction-and-Predicate-Logic|Link]]

**Key Questions:**
1. Why does $\forall$-introduction require that the variable not occur free in any undischarged assumption, and what does it mean for a variable to be "arbitrary"?
2. Why is the converse of $\exists y.\forall x.A(x,y) \Rightarrow \forall x.\exists y.A(x,y)$ not derivable, and what do the side conditions on the rules have to do with this?

---

### Chapter 2: Functional Programming and $\lambda$-Calculi (pp. 29–58)

**Summary:** Surveys functional programming practice and then develops the untyped and simply typed $\lambda$-calculus in detail — substitution, reduction, normal forms, Church–Rosser, and strong normalisation by Tait's reducibility method — establishing the computational vocabulary (redex, convertibility, computation vs. equivalence rules) that type theory reuses throughout.

**Key Definitions & Concepts by Section:**
- **2.1 Functional Programming** — first-class functions, strong/polymorphic typing, algebraic types, modularity, strict vs. lazy evaluation : [[Programming-in-Type-Theory|Link]]
- **2.2 The untyped $\lambda$-calculus** — variables, application, abstraction; bound/free occurrences, substitution avoiding variable capture; $\beta$-reduction and redexes; curried functions : [[The-Lambda-Calculus|Link]]
- **2.3 Evaluation** — normal form, head normal form, weak head normal form; the Church–Rosser theorem; structural induction; uniqueness of normal forms; leftmost-outermost reduction and the normalisation theorem; $\eta$-reduction : [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Link]]
- **2.4 Convertibility** — the relations $\leftrightarrow$ and $\leftrightarrow_{\beta\eta}$; extensionality via $\eta$ : [[The-Lambda-Calculus|Link]]
- **2.5 Expressiveness** — Turing-completeness; Church numerals; fixed-point combinators : [[The-Lambda-Calculus|Link]]
- **2.6 Typed $\lambda$-calculus** — simple types; typing rules relative to a context $\Gamma$ : [[The-Lambda-Calculus|Link]]
- **2.7 Strong normalisation** — Theorem 2.21; the method of induction over types; stability, and the proof that all terms are stable : [[The-Lambda-Calculus|Link]]
- **2.8 Further type constructors: the product** — pairs, projections; computation rules vs. equivalence (extensionality) rules
- **2.9 Base Types: Natural Numbers** — the primitive recursor $Prec$ : [[Base-Types-and-Data-Types|Link]]
- **2.10 General Recursion** — the fixed-point operator $R$ and non-termination : [[The-Lambda-Calculus|Link1]], [[Well-Founded-and-General-Recursion|Link2]]
- **2.11 Evaluation revisited** — order of a type; printable (ground, closed, normal) values; the justification for distinguishing computation rules from equivalence rules

**Key Questions:**
1. Why does the strong normalisation proof require an induction over the *structure of types* (the reducibility/stability method) rather than a plain structural induction over terms?
2. What is the difference between a "computation rule" (like $\beta$-reduction or $fst(p,q)\to p$) and an "equivalence rule" (like $(fst\,p,snd\,p)\to p$), and why does this distinction matter for what counts as a printable value?

---

### Chapter 3: Constructive Mathematics (pp. 59–66)

**Summary:** Explains the philosophical and mathematical basis of the conflict between constructive and classical mathematics — what counts as a proof of existence, what counts as a mathematical object, and what it means for objects to be equal — setting up the motivation for type theory's insistence on complete, computationally meaningful presentations. : [[Constructive-Mathematics|Link]]

**Key Definitions & Concepts:**
- **Existence and Logic** — the constructivist rejection of proof by contradiction for existentials; the proof conditions for $\wedge, \vee, \Rightarrow, \neg, \exists, \forall$; the limited principle of omniscience
- **Mathematical objects** — the critique of the classical set-theoretic reduction of all objects to sets; the tenet that every constructive object is finite or has a finitary description; constructive mathematics as naturally typed
- The Principle of Complete Presentation — an object of type A must carry sufficient witnessing information for the assertion to be verified
- Replacing negative assertions ($\neq$) by positive ones (apartness, $\#$)
- The classical vs. constructive Intermediate Value Theorem, as a worked illustration

**Key Questions:**
1. Why does Bishop's example of the set $\{r_n\}$ show that the classical least-upper-bound property implies instances of the law of excluded middle?
2. In what sense is constructive mathematics "naturally typed," and how does this motivate rejecting the classical set-theoretic encoding of all mathematical objects as sets?

---

### Chapter 4: Introduction to Type Theory (pp. 67–124)

**Summary:** The pivotal chapter: gives an informal reading of propositional proofs, formalises the notions of judgement and derivation, and then presents the complete rule system of $TT_0$ — propositional connectives, quantifiers, base types, natural numbers, well-founded trees, and the identity type — reading each rule twice, once as logic and once as a typed functional programming language, and closing with the theory of convertibility that links the two readings. : [[Specification-in-Type-Theory|Link1]], [[Equality-in-Type-Theory|Link2]], [[Programming-in-Type-Theory|Link3]], [[The-Formal-System-of-Type-Theory-(TT0)|Link4]]

**Key Definitions & Concepts by Section:**
- **4.1 Propositional Logic: an Informal View** — proof objects for $\wedge, \Rightarrow, \vee, \bot$; $\neg A \equiv_{df} A\Rightarrow\bot$ : [[Natural-Deduction-and-Predicate-Logic|Link]]
- **4.2 Judgements, Proofs and Derivations** — the judgement $p:P$; formation rules as syntax; derivations built by rule application : [[The-Formal-System-of-Type-Theory-(TT0)|Link]]
- **4.3 The Rules for Propositional Calculus** — formation/introduction/elimination/computation rules for $\wedge$ (pairs, $fst$/$snd$), $\Rightarrow$ ($\lambda$-abstraction, application, $\beta$-reduction), $\vee$ (inl/inr, cases), $\bot$ (abort); the Rule of Assumption : [[Natural-Deduction-and-Predicate-Logic|Link]]
- **4.4 The Curry Howard Isomorphism** — the systematic re-reading of "is a formula" as "is a type," of proofs as programs : [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Link]]
- **4.5 Some examples** — the identity function, composition (transitivity of implication), multiple proofs/derivations of the same proposition, De Morgan-style results : [[Natural-Deduction-and-Predicate-Logic|Link1]], [[Universes-and-Well-Founded-Types|Link2]]
- **4.6 Quantifiers** — formation/introduction/elimination/computation for $\forall$ (dependent function space) and $\exists$ (dependent pairs, with weak projections $Fst$/$Snd$); worked examples including the S-combinator and the axiom-of-choice-flavoured equivalence $((\exists x:X).P)\Rightarrow Q \Leftrightarrow (\forall x:X).(P\Rightarrow Q)$ : [[Natural-Deduction-and-Predicate-Logic|Link1]], [[Quantifiers-and-Dependent-Types|Link2]]
- **4.7 Base Types** — booleans; finite types $N_n$ and their $n$-way case switch; $\top$ and $\bot$ as the $n=1$ and $n=0$ special cases : [[Base-Types-and-Data-Types|Link]]
- **4.8 The natural numbers** — $0$, $succ$; the primitive recursor $prim$ and its dual role as primitive recursion and mathematical induction; the Ackermann function as a higher-order example : [[Base-Types-and-Data-Types|Link1]], [[The-Lambda-Calculus|Link2]]
- **4.9 Well-founded types — trees** — structural induction and primitive recursion over an algebraic tree type as a template for general well-founded types : [[Base-Types-and-Data-Types|Link]]
- **4.10 Equality** — the identity type $I(A,a,b)$ (written $a=_Ab$); formation depending on typed premises; Leibniz's law derived via the elimination operator $J$; symmetry/transitivity of equality as derived rules; equality over base types (every boolean is true or false); inequalities via an explicit axiom; dependent types built from equality; equality over the I-types itself : [[Equality-in-Type-Theory|Link]]
- **4.11 Convertibility** — free subexpressions and redexes defined relative to the typed system; the reduction relation $\to$ and its closures $\twoheadrightarrow, \leftrightarrow$; substitution rules licensing convertible terms to replace each other; the strengthened I-introduction rule; worked examples proving `addone` equals `succ` and that natural number equality is well-behaved : [[The-Lambda-Calculus|Link]]

**Key Questions:**
1. How does reading the very same four rules once as "formula/proof" and once as "type/program" constitute the Curry–Howard isomorphism, and where (if anywhere) does the correspondence show strain in this chapter?
2. Why must the formation rule for the identity type $I(A,a,b)$ mention typed premises $a:A, b:A$, breaking the pattern of every earlier formation rule — and what does this reveal about the interdependence of syntax and derivation in type theory?
3. Why is $succ(n)$ propositionally, but not judgementally (definitionally), equal to $addone(n)$, and what does the derivation of this fact reveal about the role of the substitution rules?

---

### Chapter 5: Exploring Type Theory (pp. 125–194)

**Summary:** Steps back from using $TT_0$ to studying it as a formal object: tightens the treatment of assumptions and contexts, proves derivability and uniqueness-of-type results, establishes strong normalisation, the Church–Rosser property and decidability of derivability for two reformulated systems ($TT_0^*$ and the combinator-based $TT_0^c$), surveys the different notions of equality culminating in a definition of extensional equality inside an intensional theory, adds a hierarchy of universes, gives the general well-founded (W) type, and closes with a critical look at where the Curry–Howard isomorphism strains (named assumptions, proof normal forms). : [[Programming-in-Type-Theory|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Assumptions** — contexts as ordered, consistent lists of assumptions; the rule that discharge must remove every occurrence of a named assumption : [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Link]]
- **5.2 Naming and abbreviations** — definitional naming, pattern-style equational definitions, constrained recursive definitions : [[Contexts,-Derivability-and-Type-Uniqueness|Link]]
- **5.3 Revising the rules** — variable-binding forms of $\vee$- and $\exists$-elimination (`vcases`, `Cases`); the generalised (dependent) elimination rules $(\vee E'')$, $(\exists E)$; the definition of the full system $TT_0$
- **5.4 Derivability** — Theorem 5.5 ("A is a type" derivable from "a : A"); Theorem 5.6 (uniqueness of types up to convertibility) : [[The-Lambda-Calculus|Link1]], [[Contexts,-Derivability-and-Type-Uniqueness|Link2]]
- **5.5 Computation** — printable/ground values; **5.5.2** the restricted-reduction system $TT_0^*$, strongly normalising (Troelstra) but not Church–Rosser; **5.5.3** combinator and supercombinator abstraction and the system $TT_0^c$
- **5.6 $TT_0^c$: Normalisation and its corollaries** — the normalisation theorem (Theorem 5.14); corollaries: existence of a model, uniqueness of normal forms, the Church–Rosser property, decidability of convertibility and of derivability (Theorems 5.15–5.21); **5.6.1** polymorphism vs. monomorphism (Salvesen's counterexamples) : [[Normalisation-and-Computational-Properties|Link]]
- **5.7 Equalities and Identities** — definitional equality, convertibility, the identity type, equality functions; formally decidable and representable predicates (Theorem 5.26); characterising equality via elimination rules : [[Quantifiers-and-Dependent-Types|Link]]
- **5.8 Different Equalities** — the functional-programming perspective on equational reasoning; extensional equality and Martin-Löf's rule $(IE_{ext})$ and its cost (undecidability, loss of strong normalisation); Turner's alternative; **5.8.3** defining an extensional relation $\simeq_A$ by induction over types inside the intensional theory, and the class of "extensional propositions" over which substitution is safe
- **5.9 Universes** — the inconsistency of a type of all types (Girard's paradox, via Burali-Forti); the hierarchy $U_0, U_1,\ldots$; **5.9.1** type families defined by case analysis into a universe; **5.9.2** quantifying over universes (parametric polymorphism, abstract types); **5.9.3** closure axioms and non-parametric functions; **5.9.4** transfinite universes : [[Universes-and-Well-Founded-Types|Link]]
- **5.10 Well-founded types** — **5.10.1** lists as a worked example; **5.10.2** the general $W$ type $(Wx:A).B(x)$, its formation/introduction/elimination/computation rules, and its correspondence with algebraic types; **5.10.3** Miranda algebraic types compared, including non-well-founded (negative-occurrence) types : [[Base-Types-and-Data-Types|Link1]], [[Universes-and-Well-Founded-Types|Link2]]
- **5.11 Expressibility** — representable functions lie strictly between primitive recursive and total recursive; Theorem 5.45 (representable in $TT_0$ iff provably total in $PA$/$HA$) : [[The-Lambda-Calculus|Link]]
- **5.12 The Curry Howard Isomorphism?** — **5.12.1** the mismatch between named and anonymous discharge of assumptions; **5.12.2** proof normal forms (Prawitz) and the extra "commutation" reductions beyond the ordinary computation rules : [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Link]]

**Key Questions:**
1. Why does the system $TT_0^*$ (no reduction under a $\lambda$) fail to be Church–Rosser, and how does moving to combinator/supercombinator abstraction ($TT_0^c$) repair this while still making all the same redexes eventually reachable?
2. How can a genuinely extensional equality relation $\simeq_A$ be defined *inside* an intensional type theory without sacrificing decidability of convertibility, and what is the "class of extensional propositions" over which it is safe to substitute?
3. Why must a hierarchy of universes replace a single type of all types, and in what sense does the hierarchy remain "open-ended" by omitting closure axioms?

---

### Chapter 6: Applying Type Theory (pp. 195–252)

**Summary:** Puts $TT$ to work as a programming language: shows how ordinary and course-of-values recursion, and non-primitive-recursive functions in general, are encoded; develops and verifies quicksort end to end; surveys the uses of dependent quantified types for polymorphism, abstract data types, type classes, and modules, illustrated by a vector library; shows how proof objects can be suppressed during "top-down" goal-directed derivation and later extracted; solves the Polish/Dutch national flag problem; demonstrates algebraic program transformation on the maximum-segment-sum problem; and relates tail recursion to imperative programming. : [[Equality-in-Type-Theory|Link1]], [[Programming-in-Type-Theory|Link2]]

**Key Definitions & Concepts by Section:**
- **6.1 Recursion** — **6.1.1** simultaneous/generalised primitive recursion (`add`), course-of-values recursion (`power`) via an auxiliary list of prior values; **6.1.2** defining propositions/types directly by recursion into a universe (`nonzero`, `nonempty`, the `<` relation); **6.1.3–6.1.4** head/tail over non-empty lists via four alternative typing strategies, list indexing with an in-range proof obligation : [[Programming-in-Type-Theory|Link]]
- **6.2 A Case Study – Quicksort** — **6.2.1** `qsort` defined via a course-of-values-recursive `qsort0` carrying a length-bound proof; **6.2.2** the full correctness proof (`sorted`, `perm`, auxiliary lemmas) by induction mirroring the function's own recursion : [[Programming-in-Type-Theory|Link]]
- **6.3 Dependent types and quantifiers** — **6.3.1** two ways dependency enters (via the identity type; via recursion into a universe); **6.3.2–6.3.3** $\exists$ as subset/sum/module type, $\forall$ as dependent function space; **6.3.4** implementing a proof-checked logic as an abstract data type (the LCF/Nuprl-style `proof` type with `prf`); **6.3.5–6.3.6** quantification over universes for polymorphism, abstract types, weak (Church-encoded) products, type classes (à la Haskell) and (multiple) inheritance : [[Programming-in-Type-Theory|Link1]], [[Quantifiers-and-Dependent-Types|Link2]]
- **6.4 A Case Study – Vectors** — finite types $C_n$ defined uniformly via a total order; vectors as functions $C_n\Rightarrow A$; `const`, `update`, `reduce` : [[Programming-in-Type-Theory|Link]]
- **6.5 Proof Extraction; Top-Down Proof** — reading rules "backwards" (bottom-up construction of a top-down derivation); proof-free derivations for propositional/predicate logic and for $N$-elimination : [[Specification-in-Type-Theory|Link]]
- **6.6 Program Development – Polish National Flag** — the specification via $\exists f.\forall l.\ldots$ derived from a $\forall\exists$ form by the axiom of choice; the correctness proof by list induction, yielding the `split` function : [[Specification-in-Type-Theory|Link]]
- **6.7 Program Transformation** — `map`/`fold`/`foldr` laws (Theorems 6.11–6.18); the naive quadratic `maxsub` and its linear-time transformed form : [[Programming-in-Type-Theory|Link]]
- **6.8 Imperative Programming** — tail-recursive functions and their identification with `while`-loops; the transformation `tprim` of any primitive-recursive function into tail-recursive form : [[Programming-in-Type-Theory|Link]]
- **6.9 Examples in the literature** — survey of Martin-Löf, Göteborg, Backhouse et al., Nuprl and Calculus of Constructions example developments

**Key Questions:**
1. In the quicksort development, why does the auxiliary function `qsort0` need to carry an explicit proof that the list length is bounded by its recursion parameter, and how does this proof information disappear again once the top-level `qsort` is defined?
2. What is the difference between the weak existential elimination rule underlying Miranda's `abstype` and the strong rule that MacQueen argues is needed for extensible modules?
3. Why does the maximum-segment-sum transformation depend crucially on carrying non-emptiness proofs through `map'`/`fold'`, and why do these proofs vanish from the final linear-time program?

---

### Chapter 7: Augmenting Type Theory (pp. 253–314)

**Summary:** Surveys, chapter-length, the many proposals in the literature to extend $TT$ beyond what Chapters 4–6 presented — subset and quotient types, strengthened/hypothetical/polymorphic rules, well-founded and general recursion, inductively and co-inductively defined types, partial objects — evaluating each proposal's cost against the metamathematical properties (consistency, normalisation, decidability) established in Chapter 5, and closing with a comparison of "add new rules" versus "build an explicit model" for domain-specific structures like semigroups. : [[Programming-in-Type-Theory|Link1]], [[Specification-in-Type-Theory|Link2]]

**Key Definitions & Concepts by Section:**
- **7.1 Background** — **7.1.1** what a specification is: $(\exists o:T).P$ read as "o meets P, witnessed by p"; Skolemising a $\forall\exists$ specification into $\exists f.\forall x$ via the axiom of choice; **7.1.2** computational irrelevance and the argument that lazy (normal-order) evaluation already ignores irrelevant proof information
- **7.2 The subset type** — $\{x:A\mid B\}$, its formation/introduction/(weak) elimination rules $(SetE)$; Theorems 7.2–7.4 relating $TT_0^S$ and $TT_0$, and the key non-derivability result: the witness for $B(x)$ cannot in general be recovered; **7.2.1** the extensional theory's stronger behaviour and stable predicates : [[Foundations-and-Related-Systems|Link1]], [[Programming-in-Type-Theory|Link2]], [[The-Subset-Type-and-Its-Difficulties|Link3]]
- **7.3 Propositions not types** — **7.3.1** squash types $\|A\|$ and where they fail (universal generalisation); **7.3.2** the Göteborg subset theory, adding judgements `P prop`/`P is true` distinct from `A set`/`a:A`, interpreted inside a basic extensional theory; **7.3.3** the Gödel double-negation interpretation of propositions as a subclass of types : [[The-Subset-Type-and-Its-Difficulties|Link]]
- **7.4 Are subsets necessary?** — the argument that naming (Skolemising) the sought function, rather than adding a subset type, already separates computation from proof, illustrated on the flag problem and a root-finding specification : [[The-Subset-Type-and-Its-Difficulties|Link]]
- **7.5 Quotient or Congruence Types** — **7.5** the quotient type $A/\!/E_{x,y}$ (formation requires proof that $E$ is an equivalence relation; elimination requires respecting $E$); **7.5.1** congruence types as a lighter-weight alternative stated via equations : [[Quotient-and-Congruence-Types|Link]]
- **7.6 Case Study – The Real Numbers** — reals as regular Cauchy sequences of rationals, `Real`, paired with computationally irrelevant regularity proofs; equality `Eq` and the quotient `Real_q` : [[Quotient-and-Congruence-Types|Link]]
- **7.7 Strengthened rules; polymorphism** — **7.7.1–7.7.2** Dyckhoff's strong elimination rules (e.g. $(\vee SE)$ / `decide`) and Backhouse's "hypothetical hypotheses" notation; **7.7.3** the polymorphic type $A\mapsto B$; **7.7.4** non-termination introduced by combining polymorphism with extensionality : [[Strengthened-and-Polymorphic-Rules|Link]]
- **7.8–7.9 Well-founded recursion** — partial orders, well-founded orderings and infinite descending chains (Definition 7.7); the accessible part $Acc(A,\prec)$; well-founded recursion (Definition 7.12) and course-of-values generalisation; **7.9.1** Paulson's operator $\Xi$ characterising well-foundedness inside $TT$; **7.9.2** Nordström/Saaman–Malcolm's `Acc` type with an internalised membership predicate `∈`
- **7.10 Inductive types** — least fixed points of monotonic type operators; positivity conditions guaranteeing monotonicity; formation/(no introduction)/elimination/computation rules for `Fix Θ`; relation to $W$-types : [[Well-Founded-and-General-Recursion|Link]]
- **7.11 Co-inductions** — greatest fixed points; infinite lists/streams via `Xif`; guarded corecursive definitions guaranteeing a defined head; deadlock-freedom as a consequence of totality : [[Well-Founded-and-General-Recursion|Link]]
- **7.12 Partial Objects and Types** — adding a type $\bar T$ of possibly-non-terminating computations of $T$ without collapsing the logic to inconsistency : [[Universes-and-Well-Founded-Types|Link1]], [[Well-Founded-and-General-Recursion|Link2]], [[The-Subset-Type-and-Its-Difficulties|Link3]]
- **7.13 Modelling** — comparing an explicit abstract-data-type model of a structure (e.g. semigroups) against adding new primitive rules for it directly

**Key Questions:**
1. Why does theorem 7.4 (Smith–Salvesen) show that the naive subset type's elimination rule is "very weak," and what concretely goes wrong if one tries to derive `head`/`tail` functions typed over the subset of non-empty lists?
2. How does the Göteborg subset theory's separation of `A set` into a base-set/predicate pair let it validate $(\forall x:\{y:A\mid P(y)\}).P(x)$ where the naive subset type could not?
3. Why must a co-inductively defined stream's recursive equation always supply a defined head on the right-hand side, and how does this rule out the partial (undefined-tail) lists familiar from lazy functional programming?

---

### Chapter 8: Foundations (pp. 315–330)

**Summary:** Steps back a second time to relate $TT_0$/$TT$ to the wider landscape of proof theory and semantics — comparing it proof-theoretically with Heyting Arithmetic via realizability, surveying the different styles of model construction that have been given for Martin-Löf's theories, and presenting the inversion principle by which elimination and computation rules can be mechanically generated from a type's introduction rules. : [[Foundations-and-Related-Systems|Link]]

**Key Definitions & Concepts by Section:**
- **8.1 Proof Theory** — **8.1.1** Heyting Arithmetic ($HA$) and its finite-type extension ($HA^\omega$); embeddings, interpretations, and conservative extensions; Theorem 8.8 ($TT_0$ is a conservative extension of $HA$); the inconsistency of $HA^\omega$ + choice + extensionality + full continuity, and its corollary for $TT_0$; **8.1.2** Kleene realizability ($e \Vdash \phi$) and the soundness theorem; **8.1.3** the strong existential-elimination rule shown equivalent to the weak rule plus the axiom of choice (Swaen) : [[Foundations-and-Related-Systems|Link]]
- **8.2 Model Theory** — why a semantics matters (consistency, delimiting proof-theoretic strength, licensing extensions); **8.2.1** term models (canonical/normal forms) as used in Chapter 5; **8.2.2** type-free interpretations (Smith, Aczel's Frege structures); **8.2.3** Allen's inductive-definition semantics for the extensional theory : [[Model-Theory|Link]]
- **8.3 A General Framework for Logics** — presenting type theory's binding operators as constants typed in a meta-theoretic dependent $\lambda$-calculus (the Edinburgh LF style) : [[Foundations-and-Related-Systems|Link]]
- **8.4 The Inversion Principle** — Schroeder-Heister/Dybjer's idea that elimination and computation rules can be generated automatically, by inversion, from a type's introduction rules; worked for $\vee$ and $\wedge$; the need for "hypothetical hypotheses" to invert rules (like $\Rightarrow$-introduction) that discharge an assumption; the principle's failure for the naive subset-elimination rule : [[The-Inversion-Principle|Link]]

**Key Questions:**
1. What does it mean for $TT_0$ to be a "conservative extension" of Heyting Arithmetic, and why does this result depend on the realizability method rather than a direct syntactic argument?
2. How does the inversion principle mechanically derive the elimination and computation rules for $\vee$ from its two introduction rules, and why does the same mechanical procedure fail for the naive subset type's elimination rule?

---

### Chapter 9: Conclusions (pp. 331–338)

**Summary:** Closes the book with a comparative survey of systems related to Martin-Löf type theory — Nuprl, TK, PX, AUTOMATH, System F, and the Calculus of Constructions — and a concluding reflection on the cost/benefit balance of augmenting type theory, and on functional/type-theoretic programming as the natural successor to imperative program verification.

**Key Definitions & Concepts by Section:**
- **9.1 Related Work** — **9.1.1** Nuprl: an extensional, LCF-tactic-driven implementation adding subsets, quotients, partial types and strong/direct-computation rules; **9.1.2** TK (Henson and Turner): separates sets from logical assertions and permits partial terms, using realizability for program extraction; **9.1.3** PX: a type-free computational logic over Feferman's $T_0$, with px-realizability and "Rank 0" (proof-irrelevant) formulas; **9.1.4** AUTOMATH: de Bruijn's pioneering system, its type/prop distinction, and de Bruijn indices for $\alpha$-conversion-free implementation; **9.1.5** System F (the second-order/polymorphic $\lambda$-calculus) and the Calculus of Constructions, and how the latter's `Prop`-free universe hierarchy avoids Girard's paradox while still defining strong quantifier-encoded connectives
- **9.2 Concluding Remarks** — the recurring moral that every augmentation of type theory (Chapter 7) buys expressiveness at the price of complexity or lost metatheoretic properties; the case for type theory as a unifying foundation for program development, transformation and verification, in contrast to the stalled state of imperative program verification

**Key Questions:**
1. What is the essential difference in orientation between Nuprl (an LCF-style, extensional, tactic-driven proof assistant) and the intensional, program-construction-first $TT$ presented in this book?
2. How does the Calculus of Constructions manage to define type operators like $\Pi C.((A\Rightarrow C)\Rightarrow(B\Rightarrow C)\Rightarrow C)$ directly within the calculus, and why can System F not do the same?
