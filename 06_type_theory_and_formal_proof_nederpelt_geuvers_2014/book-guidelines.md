# Type Theory and Formal Proof: An Introduction — Guidelines

## Header

**Title:** Type Theory and Formal Proof: An Introduction
**Author(s):** Rob Nederpelt (Eindhoven University of Technology) and Herman Geuvers (Radboud University Nijmegen and Eindhoven University of Technology); foreword by Henk Barendregt
**Publication:** Cambridge University Press, 2014 (ISBN 978-1-107-03650-5)

**Brief Summary:**
The book builds type theory from scratch: it starts with untyped $\lambda$-calculus, climbs through the systems of Barendregt's $\lambda$-cube ($\lambda\to$, $\lambda 2$, $\lambda\omega$, $\lambda P$) to the Calculus of Constructions $\lambda C$, and then extends $\lambda C$ with a formal definition mechanism (descriptive and primitive definitions, $\delta$-reduction) to obtain the system $\lambda D$. The organizing idea is propositions-as-types and proofs-as-terms: well-typedness of a formalised text implies the logical and mathematical correctness of the original content, and type checking is decidable, so proof checking is mechanisable. The second half tests $\lambda D$ on natural deduction, equality, sets, integer arithmetic and a full formalisation of Bézout's Lemma, written in a flag-style natural-deduction format.

**Intent of the Author:**
The authors want a gentle, example-driven introduction that lets students of mathematics and computer science understand the machinery behind proof checkers and formalisation of mathematics, including the role of logical rules, definitions and well-structured proofs. They want the reader to come away able to see how a concise dependent type theory (Automath plus the $\lambda$-cube) can represent mathematics in a way close to ordinary mathematical practice, and prepared to use proof assistants.

---

## Topic List

1. **Untyped Lambda Calculus** : [[Untyped-Lambda-Calculus|Link]]
   - Abstraction and application : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link1]], [[Untyped-Lambda-Calculus|Link2]]
   - Free and bound variables : [[Untyped-Lambda-Calculus|Link]]
   - Alpha conversion and substitution : [[Untyped-Lambda-Calculus|Link]]
   - Variable capture : [[Untyped-Lambda-Calculus|Link]]
   - Beta reduction and beta conversion : [[Untyped-Lambda-Calculus|Link]]
   - Normal forms : [[Untyped-Lambda-Calculus|Link]]
   - Confluence and the Church–Rosser theorem : [[Untyped-Lambda-Calculus|Link]]
   - Fixed point theorem : [[Untyped-Lambda-Calculus|Link]]
   - Turing completeness : [[Untyped-Lambda-Calculus|Link]]
2. **Simple Types and the Simply Typed Lambda Calculus** : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link]]
   - Simple types built from type variables and arrows : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link]]
   - Church typing versus Curry typing : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link]]
   - Derivation rules for $\lambda\to$ : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link]]
   - Judgements, statements and contexts : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link]]
   - Type checking, well-typedness and term finding : [[Backward-Goal-Directed-Well-Typedness-with-Flags|Link]]
   - Subject reduction and strong normalisation : [[Untyped-Lambda-Calculus|Link]]
   - Uniqueness of types : [[Dependent-Types|Link]]
3. **Polymorphism and Higher-Order Typed Lambda Calculi** : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link]]
   - Terms depending on types : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link]]
   - Second order abstraction and application : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link]]
   - $\Pi$-types : [[Dependent-Types|Link1]], [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link2]]
   - The system $\lambda 2$ and System F : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link]]
   - Types depending on types : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link]]
   - Type constructors and kinds : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link]]
   - The system $\lambda\omega$ and the conversion rule : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link]]
   - Impredicativity : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link]]
4. **Dependent Types** : [[Dependent-Types|Link]]
   - Types depending on terms : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link]]
   - The system $\lambda P$ : [[Dependent-Types|Link1]], [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link2]], [[Propositions-as-Types-and-the-Curry-Howard-Isomorphism|Link3]], [[Type-Theory-with-Definitions|Link4]]
   - Predicates as type-valued functions
   - Dependent function types : [[Dependent-Types|Link]]
5. **The Calculus of Constructions and the Lambda Cube** : [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link]]
   - The Barendregt cube : [[Historical-Context|Link1]], [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link2]]
   - Sorts and the formation rule : [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link]]
   - A single rule set for eight systems : [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link]]
   - Pure Type Systems : [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link]]
   - Properties of $\lambda C$ : [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link]]
   - Decidability of type checking : [[Proof-Assistants-and-Applications-of-Type-Theory|Link1]], [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link2]], [[Type-Theory-with-Definitions|Link3]], [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link4]]
6. **Propositions as Types and the Curry–Howard Isomorphism** : [[Propositions-as-Types-and-the-Curry-Howard-Isomorphism|Link]]
   - Propositions as types and proofs as terms : [[Propositions-as-Types-and-the-Curry-Howard-Isomorphism|Link1]], [[Sets-Subsets-Relations-and-Maps|Link2]]
   - Implication as function type : [[Propositions-as-Types-and-the-Curry-Howard-Isomorphism|Link]]
   - Universal quantification as $\Pi$ : [[Propositions-as-Types-and-the-Curry-Howard-Isomorphism|Link1]], [[Dependent-Types|Link2]]
   - Proof objects : [[Propositions-as-Types-and-the-Curry-Howard-Isomorphism|Link]]
   - Minimal predicate logic in $\lambda P$ : [[Propositions-as-Types-and-the-Curry-Howard-Isomorphism|Link]]
7. **Encoding Logic in the Calculus of Constructions** : [[Encoding-Logic-in-the-Calculus-of-Constructions|Link]]
   - Absurdity and negation : [[Encoding-Logic-in-the-Calculus-of-Constructions|Link1]], [[Propositions-as-Types-and-the-Curry-Howard-Isomorphism|Link2]]
   - Second order encoding of conjunction and disjunction : [[Propositions-as-Types-and-the-Curry-Howard-Isomorphism|Link]]
   - Second order encoding of existential quantification : [[Propositions-as-Types-and-the-Curry-Howard-Isomorphism|Link1]], [[Encoding-Logic-in-the-Calculus-of-Constructions|Link2]], [[Dependent-Types|Link3]]
   - Constructive versus classical logic : [[Encoding-Logic-in-the-Calculus-of-Constructions|Link1]], [[Natural-Deduction-and-Flag-Style-Proofs|Link2]], [[Propositions-as-Types-and-the-Curry-Howard-Isomorphism|Link3]]
   - Excluded third and double negation as axioms
   - Natural deduction introduction and elimination rules : [[Encoding-Logic-in-the-Calculus-of-Constructions|Link1]], [[Sets-Subsets-Relations-and-Maps|Link2]], [[Natural-Deduction-and-Flag-Style-Proofs|Link3]]
8. **Definitions and Abbreviations** : [[Definitions-and-Abbreviations|Link]]
   - The nature of definitions : [[Definitions-and-Abbreviations|Link]]
   - Descriptive and primitive definitions : [[Definitions-and-Abbreviations|Link]]
   - Definitions in a context with parameter lists : [[Definitions-and-Abbreviations|Link]]
   - Variables, parameters and constants : [[Definitions-and-Abbreviations|Link]]
   - Naming proofs and lemmas : [[Definitions-and-Abbreviations|Link]]
   - Inductive and recursive definitions : [[Definitions-and-Abbreviations|Link]]
9. **Type Theory with Definitions** : [[Type-Theory-with-Definitions|Link]]
   - Environments and extended judgements : [[Type-Theory-with-Definitions|Link]]
   - Rules for adding and instantiating definitions : [[Type-Theory-with-Definitions|Link]]
   - Delta reduction and delta conversion : [[Type-Theory-with-Definitions|Link]]
   - The conversion rule extended with delta : [[Type-Theory-with-Definitions|Link]]
   - Axioms and primitive notions : [[Type-Theory-with-Definitions|Link]]
   - The system $\lambda D$ : [[Numbers-and-Arithmetic|Link1]], [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link2]], [[Proof-Assistants-and-Applications-of-Type-Theory|Link3]], [[Type-Theory-with-Definitions|Link4]]
   - Legality, thinning and generation lemmas
   - Normalisation and confluence in $\lambda D$ : [[Type-Theory-with-Definitions|Link]]
10. **Natural Deduction and Flag-Style Proofs** : [[Natural-Deduction-and-Flag-Style-Proofs|Link]]
    - Flag-style linear derivations : [[Natural-Deduction-and-Flag-Style-Proofs|Link]]
    - Context management through flags : [[Natural-Deduction-and-Flag-Style-Proofs|Link]]
    - Suppressing unaltered parameter lists : [[Natural-Deduction-and-Flag-Style-Proofs|Link]]
    - Logic rules for constructive and classical logic : [[Natural-Deduction-and-Flag-Style-Proofs|Link]]
    - Natural deduction as the logic underlying mathematical reasoning : [[Natural-Deduction-and-Flag-Style-Proofs|Link]]
11. **Formalising Elementary Mathematics** : [[Formalising-Elementary-Mathematics|Link]]
    - Equality and Leibniz equality : [[Formalising-Elementary-Mathematics|Link]]
    - Reflexivity, substitutivity and the congruence property : [[Formalising-Elementary-Mathematics|Link]]
    - Orders : [[Formalising-Elementary-Mathematics|Link]]
    - Unique existence : [[Formalising-Elementary-Mathematics|Link]]
    - The descriptor $\iota$ : [[Formalising-Elementary-Mathematics|Link]]
    - Irrelevance of proof : [[Formalising-Elementary-Mathematics|Link1]], [[Numbers-and-Arithmetic|Link2]]
12. **Sets, Subsets, Relations and Maps** : [[Sets-Subsets-Relations-and-Maps|Link]]
    - Types versus sets : [[Sets-Subsets-Relations-and-Maps|Link]]
    - Subsets as predicates : [[Sets-Subsets-Relations-and-Maps|Link]]
    - Decidability of typing and uniqueness of types : [[Proof-Assistants-and-Applications-of-Type-Theory|Link1]], [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link2]]
    - Set-theoretic notions : [[Type-Theory-with-Definitions|Link]]
    - Relations : [[Sets-Subsets-Relations-and-Maps|Link]]
    - Maps
    - Alternative treatments of subsets : [[Natural-Deduction-and-Flag-Style-Proofs|Link]]
13. **Numbers and Arithmetic** : [[Numbers-and-Arithmetic|Link]]
    - Peano axioms for natural numbers : [[Numbers-and-Arithmetic|Link]]
    - Axiomatic integers with successor and predecessor : [[Numbers-and-Arithmetic|Link]]
    - Mathematical induction on the integers : [[Definitions-and-Abbreviations|Link]]
    - Recursion Theorem as substitute for recursive definitions
    - Addition, subtraction, multiplication and divisibility : [[Numbers-and-Arithmetic|Link]]
    - Order relations on the integers
14. **Large-Scale Formalisation** : [[Large-Scale-Formalisation|Link]]
    - Bézout's Lemma
    - Minimum Theorem : [[Large-Scale-Formalisation|Link]]
    - Division Theorem : [[Large-Scale-Formalisation|Link]]
    - Gaps in informal proofs : [[Large-Scale-Formalisation|Link]]
    - Proof size and readability : [[Large-Scale-Formalisation|Link]]
15. **Proof Assistants and Applications of Type Theory** : [[Proof-Assistants-and-Applications-of-Type-Theory|Link]]
    - Proof checking versus proof development
    - Decidable type checking algorithm : [[Type-Theory-with-Definitions|Link]]
    - Automath and its descendants : [[Historical-Context|Link1]], [[Proof-Assistants-and-Applications-of-Type-Theory|Link2]], [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link3]]
    - Proof assistants based on type theory : [[Proof-Assistants-and-Applications-of-Type-Theory|Link]]
    - Formalised mathematics and verified software : [[Formalising-Elementary-Mathematics|Link]]
    - Future of the field : [[Proof-Assistants-and-Applications-of-Type-Theory|Link]]
16. **Historical Context** : [[Historical-Context|Link]]
    - Russell's ramified type theory : [[Historical-Context|Link]]
    - Church's simple type theory : [[Historical-Context|Link]]
    - Automath and de Bruijn : [[Historical-Context|Link]]
    - Girard's System F and $F\omega$ : [[Historical-Context|Link]]
    - Martin-Löf type theory : [[Historical-Context|Link]]
    - Barendregt's cube : [[Historical-Context|Link]]

---

## Chapter Summaries

### Chapter 1: Untyped lambda calculus (pp. 1–32)

**Summary:** Introduces $\lambda$-calculus as the calculus of function abstraction and application, with careful treatment of binding, $\alpha$-conversion and substitution, and of $\beta$-reduction with its metatheory. Closes with the positive and negative aspects of the untyped system, motivating types. : [[Untyped-Lambda-Calculus|Link]]

**Key Definitions & Concepts by Section:**
- **1.1–1.2 Input–output behaviour; the essence of functions** — function as an input–output rule; abstraction $\lambda x . M$ (the function sending $x$ to $M$) and application $M N$ as the two construction principles.
- **1.3 Lambda-terms** — $\lambda$-terms $\Lambda ::= V \mid (\Lambda\Lambda) \mid (\lambda V . \Lambda)$; application associates to the left, abstraction extends as far right as possible; subterms and syntactic identity $\equiv$. : [[Untyped-Lambda-Calculus|Link]]
- **1.4 Free and bound variables** — $FV(M)$; binding occurrence, bound occurrence, closed term (combinator). : [[Untyped-Lambda-Calculus|Link]]
- **1.5 Alpha conversion** — $\lambda x . M =_\alpha \lambda y . M[x := y]$ for $y$ not free in $M$; renaming of bound variables. : [[Untyped-Lambda-Calculus|Link]]
- **1.6 Substitution** — $M[x := N]$ defined by recursion on $M$; variable capture problem; Barendregt's variable convention of choosing bound variable names distinct from free ones.
- **1.7 Lambda-terms modulo $\alpha$-equivalence** — terms are identified up to $\alpha$-equivalence; working with representatives. : [[Untyped-Lambda-Calculus|Link]]
- **1.8 Beta reduction** — $(\lambda x . M)N \to_\beta M[x := N]$ (redex, contractum); one-step $\to_\beta$, multi-step $\twoheadrightarrow_\beta$, and $\beta$-conversion $=_\beta$ as the equivalence closure. : [[Untyped-Lambda-Calculus|Link]]
- **1.9 Normal forms and confluence** — $\beta$-normal form (no redex); weak and strong normalisation; $\omega \equiv (\lambda x . x x)(\lambda x . x x)$ has no normal form; Church–Rosser theorem (confluence: $M \twoheadrightarrow_\beta N_1$, $M \twoheadrightarrow_\beta N_2$ implies a common reduct $N_3$); uniqueness of normal forms. : [[Type-Theory-with-Definitions|Link1]], [[Untyped-Lambda-Calculus|Link2]]
- **1.10 Fixed Point Theorem** — every $F$ has a fixed point $X$ with $F X =_\beta X$, given by $X \equiv (\lambda x . F(x x))(\lambda x . F(x x))$; fixed point combinator $Y \equiv \lambda f . (\lambda x . f(x x))(\lambda x . f(x x))$; encoding of Church numerals and Turing completeness. : [[Untyped-Lambda-Calculus|Link]]
- **1.11 Conclusions** — positives: clean binding, confluence, unique normal forms, fixed points for recursion; negatives: self-application, possible non-termination, every term has a fixed point. : [[Encoding-Logic-in-the-Calculus-of-Constructions|Link]]

**Key Questions:**
1. Why is substitution subtle, and how do $\alpha$-conversion and the variable convention prevent variable capture?
2. What does confluence guarantee about $\beta$-normal forms, and why does it not guarantee that they exist?
3. How does the fixed point theorem let the untyped calculus express recursion, and why is this a drawback for a logical foundation?

---

### Chapter 2: Simply typed lambda calculus (pp. 33–68)

**Summary:** Adds simple types to $\lambda$-calculus in Church's explicit style, gives its derivation system in tree and flag formats, and shows that typing removes self-application, non-termination and arbitrary fixed points, at the cost of expressive weakness. : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link]]

**Key Definitions & Concepts by Section:**
- **2.1–2.2 Adding types; simple types** — $\mathbb{T} ::= V \mid \mathbb{T} \to \mathbb{T}$; $\to$ associates to the right; a type annotates every bound variable.
- **2.3 Church-typing and Curry-typing** — explicit typing à la Church ($\lambda x : \sigma . M$) versus implicit typing à la Curry (types inferred for untyped terms); pre-typed terms. : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link]]
- **2.4 Derivation rules for Church's $\lambda\to$** — statement $M : \sigma$ (subject, predicate); declaration $x : \sigma$; context $\Gamma$; judgement $\Gamma \vdash M : \sigma$; rules (var), (appl), (abst): : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link]]
  $$\frac{\Gamma \vdash M : \sigma \to \tau \quad \Gamma \vdash N : \sigma}{\Gamma \vdash M N : \tau} \qquad \frac{\Gamma, x : \sigma \vdash M : \tau}{\Gamma \vdash \lambda x : \sigma . M : \sigma \to \tau}$$
  legal term; inhabitant.
- **2.5 Different formats for a derivation** — tree format versus flag format with flagpoles for contexts. : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link]]
- **2.6–2.9 Problems in type theory; well-typedness; type checking; term finding** — Well-Typedness (WT), Type Checking (TC: $\Gamma \vdash M : \sigma$?), Term Finding (TF: inhabitation of $\sigma$); decidability of each in $\lambda\to$.
- **2.10 General properties of $\lambda\to$** — Free Variables Lemma, Renaming, Weakening, Strengthening, Permutation, Substitution Lemma, Thinning, Generation Lemma, Uniqueness of Types. : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link]]
- **2.11 Reduction and $\lambda\to$** — Subject Reduction ($\Gamma \vdash M : \sigma$ and $M \to_\beta N$ imply $\Gamma \vdash N : \sigma$); Strong Normalisation (Termination) Theorem; Church–Rosser. : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link]]
- **2.12 Consequences** — no self-application, no infinite reductions, no fixed point combinator; decidability of well-typedness and type checking; weak expressive power (not all computable functions).

**Key Questions:**
1. Why does the Generation Lemma matter for deciding type checking, and how does it give uniqueness of types?
2. What does Subject Reduction say, and why is it needed for computation to preserve correctness of proofs?
3. Which defects of untyped $\lambda$-calculus does $\lambda\to$ remove, and what does it lose in return?

---

### Chapter 3: Second order typed lambda calculus (pp. 69–84)

**Summary:** Extends $\lambda\to$ with terms that abstract over types, yielding polymorphism, $\Pi$-types and the system $\lambda 2$ (Girard's System F), while keeping the good metatheory. : [[Untyped-Lambda-Calculus|Link1]], [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link2]], [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link3]]

**Key Definitions & Concepts by Section:**
- **3.1 Type-abstraction and type-application** — $\lambda\alpha : * . M$ and $M A$ with $A$ a type; the polymorphic identity $\lambda\alpha : * . \lambda x : \alpha . x$; the sort $*$ of types and the super-type $\square$. : [[Untyped-Lambda-Calculus|Link1]], [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link2]], [[Proof-Assistants-and-Applications-of-Type-Theory|Link3]]
- **3.2 $\Pi$-types** — $\Pi\alpha : * . B$ as the type of functions from types to terms; $A \to B$ as the special case $\Pi x : A . B$ with $x \notin FV(B)$. : [[Dependent-Types|Link1]], [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link2]]
- **3.3 Second order abstraction and application rules** — (appl$_2$) and (abst$_2$): $\Gamma \vdash M : \Pi\alpha : * . B$ and $\Gamma \vdash A : *$ give $\Gamma \vdash M A : B[\alpha := A]$. : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link]]
- **3.4 The system $\lambda 2$** — types $\mathbb{T}_2 ::= V \mid \mathbb{T}_2 \to \mathbb{T}_2 \mid \Pi V : * . \mathbb{T}_2$; rules (sort), (var), (weak), (form), (appl), (abst). : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link]]
- **3.5 Example derivation in $\lambda 2$** — derivation of polymorphic identity and composition. : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link]]
- **3.6 Properties of $\lambda 2$** — Subject Reduction, Strong Normalisation (proved with reducibility candidates), decidability of type checking; type inhabitation and Church numerals as $\Pi\alpha : * . (\alpha \to \alpha) \to \alpha \to \alpha$. : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link]]

**Key Questions:**
1. How does polymorphism change the shape of the type of the identity function, and what is the $\Pi$-type of the polymorphic identity?
2. In what sense is $A \to B$ a special case of $\Pi x : A . B$?
3. Why is the quantifier $\Pi\alpha : * . \ldots$ called impredicative?

---

### Chapter 4: Types dependent on types (pp. 85–102)

**Summary:** Extends $\lambda\to$ in a different direction with type constructors (functions from types to types) and kinds, giving $\lambda\omega$, and introduces the conversion rule so that convertible types are interchangeable. : [[Dependent-Types|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Type constructors** — functions delivering types when applied; kinds $\kappa ::= * \mid \kappa \to \kappa$; four levels: terms, types, kinds and the sort $\square$. : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link]]
- **4.2 Sort-rule and var-rule** — (sort) $\emptyset \vdash * : \square$; (var) $\Gamma, x : A \vdash x : A$ when $A$'s type is a sort $s$. : [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link]]
- **4.3 The weakening rule** — (weak): add an unused declaration $x : C$ to the context when $C : s$. : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link1]], [[Natural-Deduction-and-Flag-Style-Proofs|Link2]], [[Untyped-Lambda-Calculus|Link3]]
- **4.4 The formation rule** — (form): $A : *$ or $\square$ and $B : *$ or $\square$ give $A \to B$ of the same sort. : [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link]]
- **4.5 Application and abstraction rules** — single rules (appl) and (abst), usable for terms and for type constructors. : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link]]
- **4.6 Shortened derivations** — omitting routine side derivations. : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link1]], [[Backward-Goal-Directed-Well-Typedness-with-Flags|Link2]]
- **4.7 The conversion rule** — (conv): $\Gamma \vdash A : B$, $\Gamma \vdash B' : s$, $B =_\beta B'$ give $\Gamma \vdash A : B'$. : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link1]], [[Type-Theory-with-Definitions|Link2]]
- **4.8 Properties of $\lambda\omega$** — Subject Reduction, Strong Normalisation, Church–Rosser; Uniqueness of Types holds only up to $\beta$-conversion. : [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link]]

**Key Questions:**
1. What is the difference between a type constructor and a type, and what role do kinds play?
2. Why is the conversion rule necessary once types can contain redexes, and how does it weaken Uniqueness of Types?
3. Why can (appl) and (abst) be single rules in $\lambda\omega$, but need to be doubled in $\lambda 2$?

---

### Chapter 5: Types dependent on terms (pp. 103–122)

**Summary:** Adds types depending on terms to obtain $\lambda P$, the first genuinely dependent system, and uses it to introduce propositions-as-types and the Curry–Howard reading of minimal predicate logic. : [[Dependent-Types|Link1]], [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link2]]

**Key Definitions & Concepts by Section:**
- **5.1 The missing extension** — the fourth way to extend $\lambda\to$, namely a type $B(x)$ indexed by terms $x$; examples such as vectors of length $n$ and predicates $P : S \to *$. : [[Definitions-and-Abbreviations|Link]]
- **5.2 Derivation rules of $\lambda P$** — $\Pi x : A . B$ with $A : *$ and $B : *$ or $\square$; (form) restricted to $s_1 = *$; (appl) with substitution $B[x := N]$. : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link1]], [[Dependent-Types|Link2]]
- **5.3 Example derivation in $\lambda P$** — derivation with a predicate over a set. : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link1]], [[Backward-Goal-Directed-Well-Typedness-with-Flags|Link2]], [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link3]]
- **5.4 Minimal predicate logic in $\lambda P$** — propositions-as-types (PAT) and proofs-as-terms; $\Rightarrow$ as $\to$; $\forall x : S . P x$ as $\Pi x : S . P x$; predicates as terms of $S \to *$; introduction and elimination rules as abstraction and application; the Curry–Howard isomorphism. : [[Propositions-as-Types-and-the-Curry-Howard-Isomorphism|Link]]
- **5.5 Logical derivation example** — natural-deduction proof turned into a $\lambda P$ term. : [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link1]], [[Dependent-Types|Link2]]

**Key Questions:**
1. How does the PAT principle assign meaning to a type, to an inhabitant, and to $\Pi$?
2. Why is $\lambda P$ suited to predicates and why can it not yet express $\bot$, $\wedge$, $\vee$ or $\exists$?
3. How do natural-deduction introduction and elimination rules for $\Rightarrow$ and $\forall$ correspond to (abst) and (appl)?

---

### Chapter 6: The Calculus of Constructions (pp. 123–136)

**Summary:** Combines the four extensions into the $\lambda$-cube, shows all eight systems are given by one rule set parameterised by the allowed $(s_1, s_2)$ pairs in (form), and singles out $\lambda C$ with all pairs allowed. : [[Encoding-Logic-in-the-Calculus-of-Constructions|Link1]], [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link2]]

**Key Definitions & Concepts by Section:**
- **6.1 The system $\lambda C$** — sorts $* , \square$; pseudo-expressions $\mathbb{E} ::= V \mid * \mid \square \mid (\mathbb{E}\mathbb{E}) \mid (\lambda V : \mathbb{E} . \mathbb{E}) \mid (\Pi V : \mathbb{E} . \mathbb{E})$; the rules (sort), (var), (weak), (form), (appl), (abst), (conv); $s_1, s_2 \in \{*, \square\}$ all allowed. : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link1]], [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link2]], [[Type-Theory-with-Definitions|Link3]], [[Dependent-Types|Link4]]
- **6.2 The $\lambda$-cube** — eight systems from rule pairs $(*,*)$ (always), $(*,\square)$ (types depending on terms: $\lambda P$), $(\square,*)$ (terms depending on types: $\lambda 2$), $(\square,\square)$ (types depending on types: $\lambda\omega$); $\lambda\to$ at the base, $\lambda C$ at the top; Automath roughly $\lambda P$ plus parts of $\lambda 2$, $\lambda\omega$ and definitions. : [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link]]
- **6.3 Properties of $\lambda C$** — Free Variables, Start, Context, Thinning, Substitution and Generation Lemmas; Uniqueness of Types (up to $=_\beta$); Subject Reduction; Church–Rosser; Strong Normalisation; Decidability of well-typedness and type checking; Correctness of Types ($A : B$ implies $B \equiv \square$ or $B : s$). : [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link]]

**Key Questions:**
1. How does the choice of allowed $(s_1, s_2)$ pairs in (form) select a corner of the cube?
2. Which properties of $\lambda C$ make it suitable as a basis for a proof checker?
3. What does Correctness of Types establish about the typing of types?

---

### Chapter 7: The encoding of logical notions in λC (pp. 137–164)

**Summary:** Shows how absurdity, negation, conjunction, disjunction, classical principles, and the existential quantifier are encoded as second order types in $\lambda C$, matching natural-deduction introduction and elimination rules. : [[Encoding-Logic-in-the-Calculus-of-Constructions|Link]]

**Key Definitions & Concepts by Section:**
- **7.1 Absurdity and negation** — $\bot \equiv \Pi\alpha : * . \alpha$ (ex falso gives $\bot$-elimination for free); $\neg A \equiv A \to \bot$; $\bot$-intro and $\neg$-elim as instances of $\Rightarrow$-elim. : [[Encoding-Logic-in-the-Calculus-of-Constructions|Link1]], [[Propositions-as-Types-and-the-Curry-Howard-Isomorphism|Link2]]
- **7.2 Conjunction and disjunction** — $A \wedge B \equiv \Pi C : * . (A \to B \to C) \to C$; $A \vee B \equiv \Pi C : * . (A \to C) \to (B \to C) \to C$; terms $\langle M, N\rangle$ and injections; elimination as application to a motive $C$. : [[Encoding-Logic-in-the-Calculus-of-Constructions|Link1]], [[Propositions-as-Types-and-the-Curry-Howard-Isomorphism|Link2]]
- **7.3 Example of propositional logic** — a tautology proved by a $\lambda C$ term. : [[Encoding-Logic-in-the-Calculus-of-Constructions|Link1]], [[Simple-Types-and-the-Simply-Typed-Lambda-Calculus|Link2]]
- **7.4 Classical logic** — constructive logic needs no axiom; classical logic adds excluded third (ET) $\Pi\alpha : * . (\alpha \vee \neg\alpha)$ or double negation (DN) $\Pi\alpha : * . (\neg\neg\alpha \to \alpha)$ as an assumption at the front of the context. : [[Encoding-Logic-in-the-Calculus-of-Constructions|Link1]], [[Natural-Deduction-and-Flag-Style-Proofs|Link2]]
- **7.5 Predicate logic** — $\forall x : S . P x$ as $\Pi x : S . P x$; $\exists x : S . P x \equiv \Pi\alpha : * . (\Pi x : S . (P x \to \alpha)) \to \alpha$. : [[Dependent-Types|Link1]], [[Encoding-Logic-in-the-Calculus-of-Constructions|Link2]], [[Natural-Deduction-and-Flag-Style-Proofs|Link3]], [[Propositions-as-Types-and-the-Curry-Howard-Isomorphism|Link4]]
- **7.6 Example of predicate logic** — a quantified derivation. : [[Natural-Deduction-and-Flag-Style-Proofs|Link1]], [[Dependent-Types|Link2]], [[Encoding-Logic-in-the-Calculus-of-Constructions|Link3]], [[Propositions-as-Types-and-the-Curry-Howard-Isomorphism|Link4]]
- **7.7 Conclusions** — proof terms grow long, which motivates definitions. : [[Encoding-Logic-in-the-Calculus-of-Constructions|Link]]

**Key Questions:**
1. Why does defining $\bot$ as $\Pi\alpha : * . \alpha$ yield $\bot$-elimination?
2. In what sense is the second order encoding of $\wedge$ more general than $\neg(A \to \neg B)$?
3. What axiom must be added to $\lambda C$ to obtain classical logic, and where does it live in the context?

---

### Chapter 8: Definitions (pp. 165–188)

**Summary:** Argues that definitions are indispensable for any serious formalisation and develops an informal and then a precise format for definitions in a context, with parameters, instantiation, and named proofs. : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link]]

**Key Definitions & Concepts by Section:**
- **8.1 The nature of definitions** — abbreviation, naming of a notion for later reference; definiendum and definiens. : [[Definitions-and-Abbreviations|Link]]
- **8.2 Inductive and recursive definitions** — noted but deliberately excluded from $\lambda D$ to keep the system simple and avoid soundness checks for each definition. : [[Definitions-and-Abbreviations|Link]]
- **8.3 The format of definitions** — $a := E$; definitions relative to a context. : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link1]], [[Untyped-Lambda-Calculus|Link2]], [[Type-Theory-with-Definitions|Link3]]
- **8.4 Instantiations of definitions** — substituting actual arguments for parameters. : [[Definitions-and-Abbreviations|Link]]
- **8.5 A formal format** — $\Gamma \vdash a(\ldots) := M : N$ with parameter list in context order. : [[Definitions-and-Abbreviations|Link]]
- **8.6 Definitions depending on assumptions** — variables versus parameters versus constants. : [[Definitions-and-Abbreviations|Link]]
- **8.7 Giving names to proofs** — a lemma as a defined constant whose type is the statement and whose body is the proof.
- **8.8 A general proof and a specialised version** — instantiating a general lemma. : [[Definitions-and-Abbreviations|Link]]
- **8.9 Mathematical statements as formal definitions** — theorem as definition. : [[Definitions-and-Abbreviations|Link]]

**Key Questions:**
1. Why can a type theory with $\Pi$-types still not do without definitions in practice?
2. How are variables, parameters and constants distinguished in a definition-in-a-context?
3. How does naming a proof as a defined constant turn a lemma into a reusable object?

---

### Chapter 9: Extension of λC with definitions (pp. 189–210)

**Summary:** Formalises descriptive definitions by adding an environment $\Delta$ to judgements and rules to add and instantiate definitions, together with $\delta$-reduction, yielding $\lambda D_0$. : [[Type-Theory-with-Definitions|Link1]], [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link2]]

**Key Definitions & Concepts by Section:**
- **9.1 Extension of $\lambda C$ to $\lambda D_0$** — new expression form $a(U_1, \ldots, U_n)$ for defined constants.
- **9.2 Judgements extended with definitions** — $\Delta ; \Gamma \vdash M : N$ with environment $\Delta$ a list of definitions $x : A \vdash a(x) := M : N$. : [[Type-Theory-with-Definitions|Link]]
- **9.3 The rule for adding a definition** — (def): from $\Delta ; \Gamma \vdash K : L$ and $\Delta ; x : A \vdash M : N$ obtain $\Delta, x : A \vdash a(x) := M : N ; \Gamma \vdash K : L$ when $a \notin \Delta$. : [[Type-Theory-with-Definitions|Link]]
- **9.4 The rule for instantiating a definition** — (inst): $\Delta ; \Gamma \vdash U : A[x := U]$ gives $\Delta ; \Gamma \vdash a(U) : N[x := U]$. : [[Definitions-and-Abbreviations|Link1]], [[Type-Theory-with-Definitions|Link2]]
- **9.5 Definition unfolding and $\delta$-conversion** — $a(U) \to_\delta M[x := U]$; $\delta$-normal form (no proper constants); $=_{\beta\delta}$. : [[Type-Theory-with-Definitions|Link]]
- **9.6 Examples of $\delta$-conversion** — unfolding nested definitions. : [[Type-Theory-with-Definitions|Link]]
- **9.7 The conversion rule extended** — (conv) uses $B =_{\beta}^{\Delta} B'$, convertibility under $\beta$ and $\delta$. : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link1]], [[Type-Theory-with-Definitions|Link2]]
- **9.8–9.9 Derivation rules for $\lambda D_0$ and a closer look** — role of the premise $\Delta ; \Gamma \vdash * : \square$ in (inst) and the derived (par) rule.

**Key Questions:**
1. Why is the environment $\Delta$ separate from the context $\Gamma$?
2. What does the (inst) rule demand of the actual parameters, and why is the premise $\Gamma \vdash * : \square$ included?
3. How does $\delta$-conversion enter the conversion rule, and how does it relate to definitional equality?

---

### Chapter 10: Rules and properties of λD (pp. 211–224)

**Summary:** Adds primitive definitions (axioms and axiomatic notions without a body) to form $\lambda D$ and lists its metatheory. : [[Polymorphism-and-Higher-Order-Typed-Lambda-Calculi|Link1]], [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link2]]

**Key Definitions & Concepts by Section:**
- **10.1 Descriptive versus primitive definitions** — a primitive definition has the form $\Delta ; \Gamma \vdash a(x) := \perp\!\!\!\perp : N$ (body "PN") and cannot be unfolded. : [[Definitions-and-Abbreviations|Link]]
- **10.2 Axioms and axiomatic notions** — an axiom is a primitive constant whose type is a proposition; examples such as excluded third and the Peano axioms. : [[Type-Theory-with-Definitions|Link]]
- **10.3 Rules for primitive definitions** — (def-prim) and (inst-prim). : [[Natural-Deduction-and-Flag-Style-Proofs|Link1]], [[Definitions-and-Abbreviations|Link2]]
- **10.4 Properties of $\lambda D$** — legal expression, environment, context and combination; Legality Lemma; Legal Environment Lemma; Start, Thinning, Condensing, Generation (including a clause for $a(U)$), Uniqueness of Types up to $\beta\delta$-conversion, Substitution Lemma, Subject Reduction. : [[The-Calculus-of-Constructions-and-the-Lambda-Cube|Link]]
- **10.5 Normalisation and confluence** — weak and strong normalisation of $\to_\delta$ and of $\to_{\beta\delta}$; Church–Rosser for $\beta\delta$; uniqueness of $\beta\delta$-normal forms; proofs referred to Geuvers (2014). : [[Type-Theory-with-Definitions|Link]]

**Key Questions:**
1. How does a primitive definition differ from a descriptive one with respect to unfolding?
2. Why does adding axioms preserve normalisation and decidability in $\lambda D$?
3. What is the role of the Generation Lemma in deciding type checking when constants are present?

---

### Chapter 11: Flag-style natural deduction in λD (pp. 225–256)

**Summary:** Introduces the flag-style linear format for $\lambda D$ derivations and shows how introduction and elimination rules of natural deduction become defined constants for constructive and classical propositional and predicate logic. : [[Natural-Deduction-and-Flag-Style-Proofs|Link]]

**Key Definitions & Concepts by Section:**
- **11.1–11.2 Formal derivations; formal versus flag-style** — a flag declares a variable or assumption in the context, a line records a definition $a := M : N$; comparison with tree format.
- **11.3 Conventions about flag-style proofs** — abbreviation of obvious steps; nested flagpoles for nested contexts. : [[Natural-Deduction-and-Flag-Style-Proofs|Link]]
- **11.4 Introduction and elimination rules** — each connective given by an axiomatised pair $\wedge\text{-in}$, $\wedge\text{-el}$, etc. : [[Natural-Deduction-and-Flag-Style-Proofs|Link]]
- **11.5 Constructive propositional logic** — rules for $\Rightarrow$, $\bot$, $\neg$, $\wedge$, $\vee$ as defined constants. : [[Natural-Deduction-and-Flag-Style-Proofs|Link]]
- **11.6–11.7 Examples; suppressing parameter lists** — shorter display of $a(\ldots)$.
- **11.8 Classical propositional logic** — adding ET or DN as an axiom. : [[Natural-Deduction-and-Flag-Style-Proofs|Link1]], [[Encoding-Logic-in-the-Calculus-of-Constructions|Link2]]
- **11.9 Alternative rules for $\vee$** — variants of elimination. : [[Natural-Deduction-and-Flag-Style-Proofs|Link]]
- **11.10–11.11 Constructive and classical predicate logic** — $\forall$-in/el and $\exists$-in/el.

**Key Questions:**
1. How does a flag with a context correspond to a natural-deduction subproof with an assumption?
2. How are connectives introduced as defined constants rather than built into the system?
3. What exactly differs between the constructive and classical rule sets in $\lambda D$?

---

### Chapter 12: Mathematics in λD: a first attempt (pp. 257–278)

**Summary:** Applies $\lambda D$ to a small mathematical example, which forces the formalisation of equality, orders, unique existence and Frege's descriptor $\iota$.

**Key Definitions & Concepts by Section:**
- **12.1 An example to start with** — a definition and lemma about "least element".
- **12.2 Equality** — Leibniz equality $x =_S y$ (all predicates true of $x$ are true of $y$); reflexivity, substitutivity, symmetry and transitivity derived.
- **12.3 Congruence property of equality** — equal arguments give equal function values. : [[Formalising-Elementary-Mathematics|Link]]
- **12.4–12.5 Orders** — reflexive, transitive, antisymmetric relations; partial and linear orders; least element.
- **12.6 Unique existence** — $\exists! x : S . P x$ as existence plus uniqueness. : [[Formalising-Elementary-Mathematics|Link]]
- **12.7 The descriptor $\iota$** — $\iota(S, P, u)$, the unique element of $S$ satisfying $P$ given a proof $u$ of unique existence, introduced axiomatically with $\iota$-prop. : [[Formalising-Elementary-Mathematics|Link]]

**Key Questions:**
1. Why do symmetry and transitivity of Leibniz equality follow from reflexivity and substitutivity?
2. How does the descriptor $\iota$ let us name uniquely existing objects, and what does its use require as argument?
3. Why can a lemma such as "least element is unique" justify speaking of "the minimum"?

---

### Chapter 13: Sets and subsets (pp. 279–304)

**Summary:** Resolves the clash between sets (undecidable membership, elements in many sets) and types (decidable typing, unique types) by representing subsets as predicates over a type, then builds basic set theory, relations and maps on this basis. : [[Sets-Subsets-Relations-and-Maps|Link]]

**Key Definitions & Concepts by Section:**
- **13.1 Dealing with subsets in $\lambda D$** — conflict with Uniqueness of Types and decidability; choice to retain both; a subset of $S$ is a predicate $S \to *$, the type $\wp(S)$ written $ps(S)$; membership $x \varepsilon P \equiv P x$.
- **13.2 Basic set-theoretic notions** — inclusion $\subseteq$, equality of subsets, union, intersection, complement, difference. : [[Type-Theory-with-Definitions|Link]]
- **13.3 Special subsets** — empty set, full set, singleton, and so on. : [[Sets-Subsets-Relations-and-Maps|Link]]
- **13.4 Relations** — relations on a type as binary predicates; domain, range, properties of relations. : [[Sets-Subsets-Relations-and-Maps|Link]]
- **13.5 Maps** — functions as total, single-valued relations; injective, surjective, bijective maps; composition and inverse.
- **13.6 Representation of mathematical notions** — conventions for sets as types and elements as terms.
- **13.7–13.8 Conclusions; alternatives** — other views of subsets, for example sigma-types and set-theoretic foundations.

**Key Questions:**
1. Why are subsets-as-types incompatible with decidability of type checking, using the square root example?
2. How does the predicate view of subsets recover membership, and what is the cost?
3. How is a map represented as a relation with proofs of totality and unique values?

---

### Chapter 14: Numbers and arithmetic in λD (pp. 305–348)

**Summary:** Builds arithmetic in $\lambda D$ with an axiomatic integer type that has both successor and predecessor, defines naturals as a subset, and proves the standard laws of addition, subtraction, order, multiplication and divisibility, with attention to proof irrelevance. : [[Numbers-and-Arithmetic|Link]]

**Key Definitions & Concepts by Section:**
- **14.1 Peano axioms for natural numbers** — $0$, successor $S$, injectivity, $S\,n \neq 0$, induction. : [[Numbers-and-Arithmetic|Link]]
- **14.2 Integers the axiomatic way** — type $\mathbb{Z}$ with $0$, successor $s$, predecessor $p$, $s(p\,x) = x = p(s\,x)$, symmetric induction principle, and the axiom that $p(0) \notin \mathbb{N}$. : [[Numbers-and-Arithmetic|Link]]
- **14.3 Basic properties of the new $\mathbb{N}$** — $\mathbb{N}$ as a subset of $\mathbb{Z}$; translation of Peano's axioms into theorems.
- **14.4–14.8 Addition, computation, laws, closure, subtraction** — addition defined via the Recursion Theorem (since $\lambda D$ lacks recursive definitions); commutativity, associativity.
- **14.9–14.12 Opposite, inequality, multiplication, divisibility** — $-x$, $\leq$ on $\mathbb{Z}$, tripartition property, product and divisibility $d \mid n$.
- **14.13 Irrelevance of proof** — objects such as $\gcd(m, n, s, t)$ depend on proofs $s, t$ but not on their content; handled by $\iota$ rather than a general proof-irrelevance axiom. : [[Formalising-Elementary-Mathematics|Link1]], [[Numbers-and-Arithmetic|Link2]]

**Key Questions:**
1. How does adding a predecessor symmetrise induction on $\mathbb{Z}$, and why is the extra axiom about $p(0)$ needed?
2. Why is the Recursion Theorem needed to define addition, and how is it used in $\lambda D$?
3. When is proof irrelevance a consequence of the theory, and why do the authors decline to add it generally?

---

### Chapter 15: An elaborated example (pp. 349–378)

**Summary:** Formalises a complete proof of Bézout's Lemma together with the Minimum and Division Theorems, exposing hidden assumptions and showing how closely the formal text tracks the informal one. : [[Type-Theory-with-Definitions|Link1]], [[Definitions-and-Abbreviations|Link2]], [[Natural-Deduction-and-Flag-Style-Proofs|Link3]]

**Key Definitions & Concepts by Section:**
- **15.1–15.2 Formalising Bézout's Lemma; preparatory work** — statement of the lemma: $\gcd$ of positive integers is an integer linear combination of them; auxiliary notions and lemmas.
- **15.3–15.5 Parts I–III of the proof** — set of positive combinations, least element, divisibility argument.
- **15.6 The holes in the proof** — implicit facts about existence, positivity and divisibility that the formalisation forced into the open. : [[Large-Scale-Formalisation|Link]]
- **15.7 The Minimum Theorem for $\mathbb{Z}$** — every non-empty subset of $\mathbb{N}$ (bounded below) has a least element, via induction. : [[Large-Scale-Formalisation|Link]]
- **15.8 The Division Theorem** — for $d > 0$ there exist $q, r$ with $m = q \cdot d + r$ and $0 \leq r < d$. : [[Large-Scale-Formalisation|Link]]

**Key Questions:**
1. Which implicit steps of the textbook proof of Bézout's Lemma turned out to be "holes" requiring explicit lemmas?
2. How does induction on the integers give the Minimum Theorem?
3. How does the formal proof size compare with the informal one, and what makes flag-style presentation feasible?

---

### Chapter 16: Further perspectives (pp. 379–390)

**Summary:** Surveys what $\lambda D$ supports, proof assistants based on type theory, and where formalised mathematics is heading.

**Key Definitions & Concepts by Section:**
- **16.1 Useful applications of $\lambda D$** — formalising mathematics, verifying software and systems, archiving of knowledge. : [[Proof-Assistants-and-Applications-of-Type-Theory|Link]]
- **16.2 Proof assistants based on type theory** — proof checking (decide $p : A$) versus proof development; type checking algorithm; Automath, Coq, Agda, Lean and related systems; interactive proof development with tactics. : [[Proof-Assistants-and-Applications-of-Type-Theory|Link]]
- **16.3 Future of the field** — mathematical libraries, large formalisations such as the Four Colour Theorem, usability of proof assistants. : [[Proof-Assistants-and-Applications-of-Type-Theory|Link]]
- **16.4 Conclusions** — summary of design points: $\lambda$-calculus-based syntax, types as sets, PAT, decidable type checking, first-class definitions, explicit contexts, flags. : [[Encoding-Logic-in-the-Calculus-of-Constructions|Link]]

**Key Questions:**
1. Why does decidability of type checking give decidability of proof checking?
2. What are the main arguments for formalising mathematics in type theory?
3. What obstacles keep proof assistants from being standard tools for mathematicians?

---

### Appendices A–D (pp. 391–410)

**Summary:** Reference material: A lists the logic rules of $\lambda D$ (constructive and classical, propositional and predicate); B lists arithmetical axioms, definitions and lemmas; C gives two complete example proofs (closure under addition in $\mathbb{N}$, Minimum Theorem); D gives the derivation rules of $\lambda D$ (sort, var, weak, form, appl, abst, conv, def, def-prim, inst, inst-prim, and the derived par rule).

**Key Questions:**
1. How does the (inst) rule in Appendix D relate to the (appl) rule for $\Pi$-types?
2. Which of the rules in Appendix D are the only ones that touch the environment $\Delta$?
