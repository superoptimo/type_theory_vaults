# Type Theory and Formal Proof: An Introduction — Guidelines

## Header

**Title:** Type Theory and Formal Proof: An Introduction
**Author(s):** Rob Nederpelt (Eindhoven University of Technology) and Herman Geuvers (Radboud University Nijmegen and Eindhoven University of Technology); foreword by Henk Barendregt
**Publication:** Cambridge University Press, first published 2014, ISBN 978-1-107-03650-5 (hardback)

**Brief Summary:**
The book is a step-by-step introduction to type theory as the meeting point of logic, computer science, and mathematics. It begins with the untyped $\lambda$-calculus, builds the standard hierarchy of typed systems (simply typed $\lambda$-calculus, $\lambda 2$, $\lambda\omega$, $\lambda P$), culminates in the Calculus of Constructions ($\lambda C$), and then extends it with a formal machinery for definitions and axioms, yielding the system $\lambda D$. Its organizing idea is that propositions are types and proofs are terms, and that definitions — treated as first-class citizens with parameter lists, instantiations, and unfolding — are indispensable for feasible formalisation. The book tests $\lambda D$ by formalising logic, sets, arithmetic, and finally a complete proof of Bézout's Lemma.

**Intent of the Author:**
The authors want to lower the steep learning curve of formalisation by giving a gentle, self-contained exposition that shows what a proof *is*, how definitions work, and how mathematics can be encoded so that well-formedness implies correctness. They aim to prepare readers — from advanced undergraduates to researchers — for using and understanding proof assistants, while keeping the presentation independent of any particular software tool.

---

## Topic List

1. **[[The-Untyped-Lambda-Calculus|The Untyped Lambda Calculus]]**
   - [[The-Untyped-Lambda-Calculus|Functions as abstraction and application]]
   - [[The-Untyped-Lambda-Calculus|Syntax of lambda terms and subterm structure]]
   - [[The-Untyped-Lambda-Calculus|Free and bound variables and variable binding]]
   - [[The-Untyped-Lambda-Calculus|Alpha conversion and renaming of bound variables]]
   - Capture avoiding substitution
   - [[The-Untyped-Lambda-Calculus|Beta reduction and redex contraction]]
   - [[Metatheory-of-Typed-Lambda-Calculi|Normal forms and normalisation]]
   - Church–Rosser theorem and confluence
   - [[The-Untyped-Lambda-Calculus|Fixed points and fixed point combinators]]
   - Church numerals and data encodings
   - Turing completeness and Church's thesis

2. **[[The-Simply-Typed-Lambda-Calculus|The Simply Typed Lambda Calculus]]**
   - [[The-Simply-Typed-Lambda-Calculus|Simple types and arrow types]]
   - Explicit typing à la Church and implicit typing à la Curry
   - Derivation rules for variables application and abstraction
   - [[The-Simply-Typed-Lambda-Calculus|Tree style and flag style derivations]]
   - Well typedness type checking and term finding problems
   - [[Metatheory-of-Typed-Lambda-Calculi|Uniqueness of types and subject reduction]]
   - [[Metatheory-of-Typed-Lambda-Calculi|Strong normalisation of typed terms]]

3. **[[The-Lambda-Cube-of-Type-Systems|The Lambda Cube of Type Systems]]**
   - [[The-Lambda-Cube-of-Type-Systems|Second order abstraction and application in $\lambda 2$]]
   - [[The-Lambda-Cube-of-Type-Systems|Pi types as binders for types]]
   - [[The-Lambda-Cube-of-Type-Systems|Type constructors and kinds in $\lambda\omega$]]
   - [[The-Lambda-Cube-of-Type-Systems|Types depending on terms in $\lambda P$]]
   - [[The-Lambda-Cube-of-Type-Systems|Calculus of Constructions as the union of all extensions]]
   - [[The-Lambda-Cube-of-Type-Systems|Barendregt cube and pure type systems]]
   - Sorts and admissible formation rule combinations

4. **[[Metatheory-of-Typed-Lambda-Calculi|Metatheory of Typed Lambda Calculi]]**
   - [[Metatheory-of-Typed-Lambda-Calculi|Free variables thinning condensing and permutation lemmas]]
   - [[Metatheory-of-Typed-Lambda-Calculi|Generation lemma and syntax directedness]]
   - [[Metatheory-of-Typed-Lambda-Calculi|Substitution lemma]]
   - [[Metatheory-of-Typed-Lambda-Calculi|Subject reduction and type reduction]]
   - [[Metatheory-of-Typed-Lambda-Calculi|Conversion rule and uniqueness of types up to conversion]]
   - [[Metatheory-of-Typed-Lambda-Calculi|Weak and strong normalisation]]
   - [[Metatheory-of-Typed-Lambda-Calculi|Confluence and uniqueness of normal forms]]
   - [[Metatheory-of-Typed-Lambda-Calculi|Decidability of type checking and undecidability of inhabitation]]

5. **[[The-Curry-Howard-Isomorphism|The Curry–Howard Isomorphism]]**
   - [[The-Curry-Howard-Isomorphism|Propositions as types interpretation]]
   - [[The-Curry-Howard-Isomorphism|Proofs as terms and proof objects]]
   - [[The-Curry-Howard-Isomorphism|Implication as function type]]
   - [[The-Curry-Howard-Isomorphism|Universal quantification as Pi type]]
   - Second order encodings of conjunction disjunction and existence
   - [[The-Curry-Howard-Isomorphism|Absurdity and negation]]
   - [[The-Curry-Howard-Isomorphism|Classical logic via excluded middle or double negation]]

6. **[[Natural-Deduction-in-Flag-Style|Natural Deduction in Flag Style]]**
   - [[Natural-Deduction-in-Flag-Style|Introduction and elimination rules for the connectives]]
   - Flag style proofs with contexts and scope
   - [[Natural-Deduction-in-Flag-Style|Constructive propositional and predicate logic]]
   - [[Natural-Deduction-in-Flag-Style|Classical propositional and predicate logic]]
   - [[Natural-Deduction-in-Flag-Style|Alternative rules for disjunction and existence]]
   - [[Natural-Deduction-in-Flag-Style|Proof by contradiction]]

7. **[[Formal-Definitions-in-Type-Theory|Formal Definitions in Type Theory]]**
   - Nature and purpose of mathematical definitions
   - [[Formal-Definitions-in-Type-Theory|Descriptive definitions with definiendum and definiens]]
   - [[Formal-Definitions-in-Type-Theory|Primitive definitions for axioms and axiomatic notions]]
   - [[Formal-Definitions-in-Type-Theory|Parameter lists and instantiation]]
   - [[Formal-Definitions-in-Type-Theory|Definition unfolding and delta reduction]]
   - [[Formal-Definitions-in-Type-Theory|Delta conversion and beta delta conversion]]
   - [[Formal-Definitions-in-Type-Theory|Extended judgements with environments]]
   - [[Formal-Definitions-in-Type-Theory|Derivation rules for adding and instantiating definitions]]
   - [[Formal-Definitions-in-Type-Theory|Naming proofs and applying theorems]]
   - [[Formal-Definitions-in-Type-Theory|Normalisation and confluence in $\lambda D$]]

8. **[[Formalising-Elementary-Mathematics|Formalising Elementary Mathematics]]**
   - [[Formalising-Elementary-Mathematics|Leibniz equality and its properties]]
   - [[Formalising-Elementary-Mathematics|Substitutivity and congruence]]
   - [[Formalising-Elementary-Mathematics|Partial orders and order relations]]
   - [[Formalising-Elementary-Mathematics|Unique existence quantifiers]]
   - [[Formalising-Elementary-Mathematics|The iota descriptor operator]]
   - [[Formalising-Elementary-Mathematics|Irrelevance of proof]]
   - [[Formal-Definitions-in-Type-Theory|Mathematical statements in definition format]]

9. **[[Sets-Relations-and-Maps|Sets Relations and Maps]]**
   - [[Sets-Relations-and-Maps|Sets as types and subsets as predicates]]
   - Powerset and elementhood
   - [[Sets-Relations-and-Maps|Set operations and special subsets]]
   - [[Sets-Relations-and-Maps|Equivalence relations and equivalence classes]]
   - [[Sets-Relations-and-Maps|Maps as functional relations]]
   - Injectivity surjectivity and bijectivity
   - [[Sets-Relations-and-Maps|Image and origin of a subset]]

10. **[[Arithmetic-in-Type-Theory|Arithmetic in Type Theory]]**
    - [[Arithmetic-in-Type-Theory|Peano axioms for the natural numbers]]
    - [[Arithmetic-in-Type-Theory|Axiomatic introduction of the integers]]
    - [[Arithmetic-in-Type-Theory|Symmetric induction over the integers]]
    - [[Arithmetic-in-Type-Theory|Recursion theorem for $\mathbb{Z}$]]
    - [[Arithmetic-in-Type-Theory|Addition subtraction and opposites]]
    - [[Arithmetic-in-Type-Theory|Multiplication and distributivity]]
    - [[Arithmetic-in-Type-Theory|Inequality relations on the integers]]
    - [[Arithmetic-in-Type-Theory|Divisibility and greatest common divisor]]
    - [[Arithmetic-in-Type-Theory|Minimum and maximum theorems]]
    - Division theorem with quotient and remainder

11. **[[Formal-Proof-Development-in-Practice|Formal Proof Development in Practice]]**
    - [[Formal-Proof-Development-in-Practice|Bézout's Lemma as a worked example]]
    - [[Formal-Proof-Development-in-Practice|Proof specialisation by parameter instantiation]]
    - [[Formal-Proof-Development-in-Practice|Holes and deferred proof obligations]]
    - [[Formal-Proof-Development-in-Practice|Skeleton proofs and proof hints]]
    - [[Formal-Proof-Development-in-Practice|Fully detailed formal proofs]]

12. **[[Proof-Assistants-and-the-Future-of-Formalisation|Proof Assistants and the Future of Formalisation]]**
    - [[Proof-Assistants-and-the-Future-of-Formalisation|Automath and the de Bruijn criterion]]
    - [[Proof-Assistants-and-the-Future-of-Formalisation|Proof checking as type checking]]
    - [[Proof-Assistants-and-the-Future-of-Formalisation|Interactive proving with tactics]]
    - [[Proof-Assistants-and-the-Future-of-Formalisation|Libraries of formalised mathematics]]
    - Automation and machine learning for proving
    - High level explanation of formal proofs

---

## Chapter Summaries

### Chapter 1: Untyped lambda calculus (pp. 1–32)

**Summary:** Introduces the untyped $\lambda$-calculus as the abstract machinery of functions — abstraction, application, substitution, $\beta$-reduction, normal forms, confluence and fixed points — and closes by listing the pathologies (self-application, non-termination, universal fixed points) that motivate the introduction of types.

**Key Definitions & Concepts by Section:**
- **1.1–1.2 Input–output behaviour / The essence of functions** — abstraction ($\lambda x. M$), application ($M N$), $\beta$-reduction ($( \lambda x. M) N \to M[x:=N]$), Currying (turning multi-argument functions into chains of one-argument functions)
- **1.3 Lambda-terms** — $\Lambda$ (inductive set of $\lambda$-terms: variables, application, abstraction), syntactical identity ($\equiv$), subterms ($Sub(M)$), proper subterm
- **1.4 Free and bound variables** — binding/bound/free occurrences, $FV(M)$ (set of free variables), closed $\lambda$-term / combinator, $\Lambda^0$ (closed terms)
- **1.5 Alpha conversion** — renaming ($M^{x \to y}$), $\alpha$-equivalence ($=_{\alpha}$), $\alpha$-convertible terms, $\alpha$-variants, side conditions preventing capture
- **1.6 Substitution** — $M[x:=N]$ (capture-avoiding substitution), simultaneous vs sequential substitution, substitution-swap lemma
- **1.7 Lambda-terms modulo $\alpha$-equivalence** — identifying $\alpha$-variants, Barendregt convention (distinct names for binders, disjoint from free variables)
- **1.8 Beta reduction** — one-step reduction ($\to_\beta$), redex, contractum, zero-or-more-step reduction ($\twoheadrightarrow_\beta$), $\beta$-conversion ($=_\beta$)
- **1.9 Normal forms and confluence** — $\beta$-normal form, $\beta$-normalising, weak vs strong normalisation, reduction path, Church–Rosser Theorem (CR / confluence), uniqueness of $\beta$-normal forms
- **1.10 Fixed Point Theorem** — fixed point ($L M =_\beta M$), fixed point combinator $Y \equiv \lambda y.(\lambda x. y(x x))(\lambda x. y(x x))$, solvability of recursive equations
- **1.11–1.12 Conclusions / Further reading** — pros and cons of the untyped calculus, Church's thesis, Turing completeness, de Bruijn indices, reduction strategies (e.g. leftmost reduction)

**Key Questions:**
1. How do abstraction and application jointly model the input–output behaviour of functions?
2. Why must substitution avoid variable capture, and how does $\alpha$-conversion enable this?
3. What does the Church–Rosser theorem guarantee about the outcome of a calculation, regardless of reduction order?
4. Why does every $\lambda$-term have a fixed point in the untyped calculus, and why is that counter-intuitive?
5. Which defects of the untyped calculus are removed by adding types?

---

### Chapter 2: Simply typed lambda calculus (pp. 33–68)

**Summary:** Adds simple types to $\lambda$-calculus, presents the Church-style derivation system for $\lambda\to$ in tree and flag formats, works through the three canonical typing problems, and proves the metatheory (uniqueness of types, subject reduction, strong normalisation) that eliminates the untyped pathologies.

**Key Definitions & Concepts by Section:**
- **2.1–2.2 Adding types / Simple types** — set of simple types $T$ ($V \mid T \to T$), arrow type ($\sigma \to \tau$), typing statement ($M : \sigma$), typable term, right-associative arrow
- **2.3 Church-typing and Curry-typing** — typing à la Church (explicit), typing à la Curry (implicit), declaration, context/basis $\Gamma$, judgement ($\Gamma \vdash M : \sigma$)
- **2.4 Derivation rules for Church's $\lambda\to$** — pre-typed $\lambda$-terms ($\Lambda T$), rules (var), (appl), (abst), legal term
- **2.5 Different formats for a derivation** — tree format, linear format, flag notation (flags mark context declarations whose scope follows the flag pole)
- **2.6 Kinds of problems** — Well-typedness ($?\vdash \text{term}:?$), Type Assignment, Type Checking, Term Finding (inhabitation)
- **2.7–2.9 Worked examples** — flag-style derivations for each problem type; PAT-interpretation preview (inhabiting $A \to B \to A$)
- **2.10 General properties** — domain ($dom$), subcontext, permutation, projection; Free Variables Lemma; Thinning / Condensing / Permutation Lemmas; Generation Lemma (syntax-directedness); Subterm Lemma; Uniqueness of Types
- **2.11 Reduction and $\lambda\to$** — Substitution Lemma, one-step $\beta$-reduction for $\Lambda T$, Church–Rosser for $\lambda\to$, Subject Reduction ($L \twoheadrightarrow_\beta L'$ preserves type), Strong Normalisation (Termination) Theorem
- **2.12 Consequences** — no self-application ($x x$ untypable), normal forms always exist, not every function has a fixed point
- **2.14 Further reading** — Russell's RTT, Church 1940, principal type algorithm (Hindley–Curry–Milner), PCF with fixed point constant $Y_\sigma$, history of normalisation proofs (Turing, Sanchis, Tait)

**Key Questions:**
1. How do (appl) and (abst) mirror modus ponens and $\Rightarrow$-introduction in natural deduction?
2. What distinguishes explicit Church typing from implicit Curry typing, and what decidability consequences follow?
3. Why does Uniqueness of Types matter for decidable proof checking?
4. How does Strong Normalisation rule out infinite computations, and what do we lose by it?

---

### Chapter 3: Second order typed lambda calculus (pp. 69–84)

**Summary:** Extends $\lambda\to$ with terms depending on types (System F / $\lambda 2$), motivated by the polymorphic identity and generic composition; introduces $\Pi$-types to type type-abstractions and gives the new derivation rules and properties.

**Key Definitions & Concepts by Section:**
- **3.1 Type-abstraction and type-application** — polymorphic identity ($\lambda \alpha : *. \lambda x : \alpha. x$), polymorphic functions, second order abstraction/application, iteration and composition examples
- **3.2 $\Pi$-types** — $\Pi$-binder ($\Pi \alpha : *. A$), binding type variables so that $\alpha$-equivalent terms have $\alpha$-equivalent types
- **3.3 Second order rules** — (abst2) and (appl2) ($M B : A[\alpha := B]$ when $M : \Pi \alpha : *. A$ and $B : *$)
- **3.4 The system $\lambda 2$** — types $T_2$, terms $\Lambda T_2$, $\lambda 2$-contexts (all type variables must be declared before use), revised (var), (form) rule ($\Gamma \vdash B : *$)
- **3.5 Example derivation** — typing $\lambda \alpha : *. \lambda f : \alpha \to \alpha. \lambda x : \alpha. f(f x) : \Pi \alpha : *. (\alpha \to \alpha) \to \alpha \to \alpha$
- **3.6 Properties** — extended $\alpha$-conversion (renaming of type variables), extended $\beta$-reduction (second order basis $(\lambda \alpha : *. M) T \to_\beta M[\alpha := T]$), transfer of all $\lambda\to$ properties
- **3.8 Further reading** — Girard's System F, impredicativity, parametricity (Reynolds), undecidability of type inference in $\lambda 2$ (Wells), polymorphic Church numerals and data types (Böhm–Berarducci)

**Key Questions:**
1. Why does polymorphism force the introduction of the $\Pi$-binder instead of reusing the arrow?
2. How does (appl2) instantiate a polymorphic term at a concrete type?
3. What does impredicativity mean for a type such as $\Pi \alpha : *. \alpha \to \alpha$, and why is it consistent?
4. Why is self-application partially expressible in $\lambda 2$ (e.g. $\lambda x : (\Pi \alpha : *. \alpha \to \alpha). x(\sigma \to \sigma)(x \sigma)$)?

---

### Chapter 4: Types dependent on types (pp. 85–102)

**Summary:** Extends $\lambda\to$ with types depending on types, producing $\lambda\omega$; introduces type constructors, kinds, the sort $\Box$, the (sort)/(var)/(weak)/(form) rule machinery, shortened derivations, and the conversion rule.

**Key Definitions & Concepts by Section:**
- **4.1 Type constructors** — type constructor (e.g. $\lambda \alpha : *. \alpha \to \alpha : * \to *$), kinds ($K = * \mid K \to K$), super-super-type $\Box$, sorts ($*, \Box$), proper constructor, four levels (terms, constructors, kinds, $\Box$)
- **4.2 Sort-rule and var-rule** — (sort) ($\emptyset \vdash * : \Box$), (var) with double role ($s$ ranges over both sorts), fresh variable condition $x \notin \Gamma$
- **4.3 The weakening rule** — (weak): extending a context at the end with a well-formed declaration preserves derivability
- **4.4 The formation rule** — (form) constructing both types and kinds ($A \to B : s$)
- **4.5 Application and abstraction rules** — (appl) and (abst) with double role; checking well-formedness of $A \to B$ as second premiss of (abst)
- **4.6 Shortened derivations** — suppressing administrative steps ((sort), (var), (weak), (form))
- **4.7 The conversion rule** — (conv): replacing a type by a well-formed $\beta$-convertible one; distinction between Subject Reduction (reduce subject), Type Reduction (reduce type), and Conversion
- **4.8 Properties** — Uniqueness of Types up to Conversion ($B_1 =_\beta B_2$)
- **4.10 Further reading** — Girard's $F\omega$, type constructors in Haskell, $\lambda\omega$ as a transition system

**Key Questions:**
1. What separates a type from a kind, and what is the role of the sort $\Box$?
2. Why is the conversion rule necessary once types themselves can reduce?
3. Why must the second premiss of (conv) check that $B'$ is well-formed?
4. How do the double-role rules of $\lambda\omega$ cover both term-level and kind-level computation?

---

### Chapter 5: Types dependent on terms (pp. 103–122)

**Summary:** Extends $\lambda\to$ with types depending on terms, producing $\lambda P$; this enables families of types, predicates, and the propositions-as-types / proofs-as-terms (PAT) interpretation, coding minimal predicate logic (implication and universal quantification) directly into the derivation rules.

**Key Definitions & Concepts by Section:**
- **5.1 The missing extension** — family of types / indexed type ($\lambda n : nat. S_n$), set-valued function, proposition-valued function, predicate ($P : S \to *$)
- **5.2 Derivation rules of $\lambda P$** — $\Pi$-types over terms ($\Pi x : A. B$), upgraded (form) with extended context, (appl) yielding $B[x:=N]$, (abst); downgrading: $A$ must have type $*$, so $A \to \Box$ is a legal kind
- **5.3 An example derivation** — constructing $\lambda x : A. \lambda y : P x. y : \Pi x : A. P x \to P x$
- **5.4 Minimal predicate logic in $\lambda P$** — PAT-interpretation (propositions as types, proofs as terms, proof object), coding of sets ($S : *$), propositions ($A : *$), predicates ($P : S \to *$); implication $A \Rightarrow B$ as $A \to B$; universal quantification $\forall x \in S(P(x))$ as $\Pi x : S. P x$; ($\Rightarrow$-elim)/(∀-elim) as (appl), ($\Rightarrow$-intro)/(∀-intro) as (abst)
- **5.5 Example of a logical derivation** — proof of $\forall x \forall y(Q(x,y)) \Rightarrow \forall u(Q(u,u))$ with Currying of binary predicates
- **5.7 Further reading** — Automath, Curry–Howard–de Bruijn embedding, Logical Framework interpretation, Martin-Löf's intuitionistic type theory, $\Sigma$-types, inductive types

**Key Questions:**
1. How does $\Pi x : A. B$ unify function spaces (when $x \notin FV(B)$) and dependent products?
2. What does it mean that a proposition is inhabited, and how does this encode truth?
3. How do (appl) and (abst) specialise to the natural deduction rules for $\forall$?
4. Why can $\lambda P$ not express conjunction, disjunction or $\exists$?

---

### Chapter 6: The Calculus of Constructions (pp. 123–136)

**Summary:** Combines all three extensions of $\lambda\to$ into the Calculus of Constructions $\lambda C$, presents the Barendregt $\lambda$-cube whose eight systems differ only in the allowed $(s_1, s_2)$ combinations of the formation rule, and states the central metatheoretic properties of $\lambda C$.

**Key Definitions & Concepts by Section:**
- **6.1 The system $\lambda C$** — generalised (form) rule with independent sorts $s_1, s_2 \in \{*, \Box\}$; the four dependency combinations $( *, * )$, $(\Box, *)$, $(\Box, \Box)$, $(*, \Box)$ corresponding to $\lambda\to$, $\lambda 2$, $\lambda\omega$, $\lambda P$
- **6.2 The $\lambda$-cube** — eight systems ($\lambda\to$, $\lambda 2$, $\lambda\omega$, $\lambda P$, $\lambda\underline{\omega}$, $\lambda P2$, $\lambda P\omega$, $\lambda C$), Barendregt cube, one unified rule set ((sort), (var), (weak), (form), (appl), (abst), (conv)); position of Automath
- **6.3 Properties of $\lambda C$** — expressions $E$, well-formed context, Free Variables Lemma, Thinning/Permutation/Condensing, Generation Lemma (four cases), legal expression, Subexpression Lemma, Uniqueness of Types up to Conversion, Substitution Lemma, Church–Rosser, Subject Reduction, Strong Normalisation; decidability of Well-typedness and Type Checking; undecidability of Term Finding (via Church–Turing); proof assistants
- **6.5 Further reading** — CC as basis of Coq, Calculus of Inductive Constructions, Extended Calculus of Constructions with universes $\Box_i$ and cumulativity

**Key Questions:**
1. How does the single choice of permitted $(s_1, s_2)$ pairs select one of the eight cube systems?
2. Why is Term Finding undecidable in $\lambda C$, and what does that imply about the limits of automated proving?
3. Why does the type of $\Pi x : A. B$ inherit the sort $s_2$ of its body?

---

### Chapter 7: The encoding of logical notions in $\lambda C$ (pp. 137–164)

**Summary:** Encodes propositional and predicate logic inside $\lambda C$ using (second order) type-theoretic definitions — $\bot$, $\neg$, $\wedge$, $\vee$, $\Leftrightarrow$, $\forall$, $\exists$ — verifies that these satisfy the natural deduction introduction/elimination rules, and obtains classical logic by adding excluded middle or double negation as an axiom.

**Key Definitions & Concepts by Section:**
- **7.1 Absurdity and negation** — $\bot \equiv \Pi \alpha : *. \alpha$, ex falso / $\bot$-elimination for free, $\neg A \equiv A \to \bot$; $\bot$-intro and $\neg$-rules as special cases of $\Rightarrow$-rules
- **7.2 Conjunction and disjunction** — second order encodings $A \wedge B \equiv \Pi C : *. (A \to B \to C) \to C$ and $A \vee B \equiv \Pi C : *. (A \to C) \to (B \to C) \to C$; verification of ($\wedge$-intro), ($\wedge$-elim-left/right), ($\vee$-intro-left/right), ($\vee$-elim); alternative abstracted connectives ($\wedge \equiv \lambda \alpha : *. \lambda \beta : *. \ldots$)
- **7.3 An example of propositional logic** — full $\lambda C$-derivation of $(A \vee B) \Rightarrow (\neg A \Rightarrow B)$
- **7.4 Classical logic in $\lambda C$** — constructive vs classical logic, excluded third (ET), double negation (DN), adding ET as an inhabitant $i_{ET} : \Pi \alpha : *. \alpha \vee \neg \alpha$, derivation of DN from ET
- **7.5 Predicate logic in $\lambda C$** — $\forall$ as $\Pi$ (from Chapter 5), second order encoding $\exists x \in S(P(x)) \equiv \Pi \alpha : *. ((\Pi x : S. (P x \to \alpha)) \to \alpha)$, verification of ($\exists$-elim) and ($\exists$-intro), side condition $x \notin FV(A)$
- **7.6 An example of predicate logic** — derivation of $\neg(\exists x : S. P x) \Rightarrow \forall y : S. \neg(P y)$; growth of proof terms motivates definitions
- **7.7–7.8 Conclusions / Further reading** — proof checking = type checking; advantages/disadvantages of type-theoretic logic; natural deduction (Gentzen, Jaśkowski), sequent calculus, Hilbert systems; Fitch style; Prawitz proof theory

**Key Questions:**
1. Why are $\wedge$, $\vee$ and $\exists$ given second order encodings rather than first order ones?
2. How does ex falso follow immediately from the definition $\bot \equiv \Pi \alpha : *. \alpha$?
3. How is classical logic obtained from constructive logic within $\lambda C$?
4. Why is the condition $x \notin FV(A)$ essential in $\exists$-elimination?
5. Why do proof terms grow so large that a definition mechanism becomes necessary?

---

### Chapter 8: Definitions (pp. 165–188)

**Summary:** Analyses the nature, usage and indispensability of definitions in mathematics, develops a formal format with contexts and parameter lists ($\Gamma \Vdash a(\overline{x}) := M : N$), argues against primitive inductive/recursive definitions, and shows that proofs too can and should be given names so that theorems can be instantiated and applied.

**Key Definitions & Concepts by Section:**
- **8.1 The nature of definitions** — naming useful concepts, mnemonics, avoidance of exponential blow-up without definitions, variables vs defined names
- **8.2 Inductive and recursive definitions** — why they are not primitive in this system (definable via higher order logic or the $\iota$-descriptor; trade-off: $fac(3) = 6$ requires a proof)
- **8.3 The format of definitions** — $a := E$, definiendum / defined name / defined constant ($a$), definiens ($E$), parameter list, empty parameter list convention
- **8.4 Instantiations of definitions** — instantiation of parameters, identity instantiation, cumulative typing conditions on instantiations, two life stages of a constant
- **8.5 A formal format for definitions** — $\Gamma \Vdash a(x_1, \ldots, x_n) := M : N$, overlining notation ($\overline{x}$, $\overline{A}$), dependence order between definitions
- **8.6 Definitions depending on assumptions** — contexts containing assumptions (e.g. $u : \text{partially-ordered}(S, R)$)
- **8.7 Giving names to proofs** — definitions of proofs ($b(\ldots) := E_4 : P$), $*_s$ vs $*_p$ sugaring, four kinds of definitions (sets, objects, propositions, proofs), applying Bézout's Lemma by instantiation
- **8.8 A general proof and a specialised version** — general vs specialised proof of Bézout's Lemma; instantiating proof names instead of copying proofs
- **8.9 Mathematical statements as formal definitions** — transforming judgements $\Gamma \vdash M : N$ into definition format $\Gamma \Vdash a(\ldots) := M : N$; a formalised text as a list of definitions
- **8.11 Further reading** — definitions as meta-level abbreviations in logic, Severi & Poll, local definitions, Automath treatment

**Key Questions:**
1. Why are definitions practically inevitable once a formalised theory grows?
2. How do parameters, variables, and constants differ in role and scope?
3. Why must instantiation respect cumulative typing conditions across a parameter list?
4. Why is giving names to proofs essential for applying theorems?
5. What is lost and gained by excluding inductive and recursive definitions as primitives?

---

### Chapter 9: Extension of $\lambda C$ with definitions (pp. 189–210)

**Summary:** Turns $\lambda C$ into $\lambda D_0$ by adding descriptive definitions as first-class citizens: extended judgements $\Delta ; \Gamma \vdash M : N$ with environments, the (def) and (inst) rules, definition unfolding via $\delta$-reduction, and an extended conversion rule for $\beta\delta$-conversion.

**Key Definitions & Concepts by Section:**
- **9.1 Extension to $\lambda D_0$** — expressions $E_{\lambda D}$ (adding constants $C$ with instantiated parameter lists), descriptive definition ($\overline{x} : \overline{A} \Vdash a(\overline{x}) := M : N$), environment $\Delta$
- **9.2 Judgements extended with definitions** — extended judgement ($\Delta ; \Gamma \vdash M : N$), accumulated dependencies (constants may occur in later definitions, types, terms)
- **9.3 The rule for adding a definition** — (def): append a well-formed definition to the environment, $a$ fresh
- **9.4 The rule for instantiating a definition** — instantiation requirement $U_i : A_i[\overline{x} := \overline{U}]$, (inst-pos) for non-empty parameter lists, (inst-zero) for empty lists with premiss $\Delta ; \Gamma \vdash * : \Box$, combined (inst) rule
- **9.5 Definition unfolding and $\delta$-conversion** — one-step unfolding ($\to_\Delta$: $a(\overline{U}) \to_\Delta M[\overline{x} := \overline{U}]$), folding, zero-or-more-step $\delta$-reduction ($\twoheadrightarrow_\Delta$), $\delta$-conversion ($=_\Delta$), unfoldable constant, $\delta$-normal form
- **9.6 Examples of $\delta$-conversion** — unfolding diagrams for nested constants ($a(a(x,x), a(y,y))$)
- **9.7 The conversion rule extended** — one-step $\beta$-reduction for $\lambda D_0$, $\beta\delta$-conversion ($=_{\Delta\beta}$), (βδ-conv) rule
- **9.8 The derivation rules for $\lambda D_0$** — complete rule set (Figure 9.3)
- **9.9 A closer look at the rules** — (weak) vs (def) as weakening rules for contexts/environments; (var) vs (inst) as typing rules for basic expressions; derived rule (par) for the pure form $a(\overline{x}) : N$

**Key Questions:**
1. Why do judgements need an environment $\Delta$ in front of the context $\Gamma$?
2. How does the (inst) rule handle the cumulative effect of instantiation on dependent types?
3. What distinguishes $\delta$-reduction (unfolding one occurrence) from $\beta$-reduction (substituting for all bound occurrences)?
4. Why is the extra premiss $\Delta ; \Gamma \vdash * : \Box$ needed only for constants with empty parameter lists?

---

### Chapter 10: Rules and properties of $\lambda D$ (pp. 211–224)

**Summary:** Adds primitive definitions (axioms and axiomatic notions, written with the empty definiens $\bot\bot$) to $\lambda D_0$, yielding the final system $\lambda D$, and establishes its properties, including normalisation and confluence for the combined $\beta\delta$-reduction.

**Key Definitions & Concepts by Section:**
- **10.1 Descriptive versus primitive definitions** — primitive constants have only a type and cannot be unfolded
- **10.2 Axioms and axiomatic notions** — $\bot\bot$ (non-existing definiens), examples: $N, 0, s$, induction, ET/DN; caution: primitive definitions can make a system inconsistent and need external justification
- **10.3 Rules for primitive definitions** — (def-prim) with premiss $\Delta ; \overline{x} : \overline{A} \vdash N : s$, (inst-prim)
- **10.4 Properties of $\lambda D$** — inclusion of $\lambda C \subseteq \lambda D_0 \subseteq \lambda D$; Free Variables and Constants Lemma; legal expression/environment/combination/context; Legality Lemma; Legal Environment Lemma; Start Lemma (for declarations and definitions); Thinning and Condensing Lemmas; Generation Lemma (five cases, including instantiated constants); Uniqueness of Types up to $\beta\delta$-conversion; Substitution Lemma; Subject Reduction
- **10.5 Normalisation and confluence in $\lambda D$** — Weak and Strong Normalisation of $\to_\Delta$, $\delta$-confluence, uniqueness of $\delta$-normal forms; Church–Rosser for $\twoheadrightarrow_{\Delta\beta}$, uniqueness of $\beta\delta$-normal forms; Weak and Strong Normalisation for $\twoheadrightarrow_{\Delta\beta}$
- **10.7 Further reading** — Automath primitive notions (PN), type checking algorithms, connection to logical consistency (no closed term of type $\bot$)

**Key Questions:**
1. How do primitive definitions differ formally and philosophically from descriptive ones?
2. Why can a syntactically correct $\lambda D$ text still be mathematically meaningless or inconsistent?
3. What do strong normalisation and confluence of $\twoheadrightarrow_{\Delta\beta}$ guarantee for a type-checking implementation?
4. How does one prove consistency of a given environment of primitive notions?

---

### Chapter 11: Flag-style natural deduction in $\lambda D$ (pp. 225–256)

**Summary:** Shows that $\lambda D$ can host natural deduction: the introduction and elimination rules for all connectives and quantifiers are defined as $\lambda D$-constants, flag-style conventions are fixed (definitions as the only format, parameter list convention), and both constructive and classical propositional and predicate logic are worked out with examples.

**Key Definitions & Concepts by Section:**
- **11.1 Formal derivations in $\lambda D$** — definitions of $\bot$, $\neg$, $\wedge$ derived via (form) and (par); copying $\lambda C$ derivations into $\lambda D_0$
- **11.2 Comparing formal and flag-style $\lambda D$** — condensing administrative lines; definitions absorb derivability claims
- **11.3 Conventions about flag-style proofs** — flags extend/shrink the context like a stack; the environment only grows (no erasure of definitions); everything written in definition format
- **11.4 Introduction and elimination rules** — naming natural deduction rules inside derivations for transparency
- **11.5 Rules for constructive propositional logic** — $\Rightarrow$-in/$\Rightarrow$-el, $\bot$-in/$\bot$-el, $\neg$-in/$\neg$-el, $\wedge$-in/$\wedge$-el1/$\wedge$-el2, $\vee$-in1/$\vee$-in2/$\vee$-el, $\Leftrightarrow$-in/$\Leftrightarrow$-el1/$\Leftrightarrow$-el2; type-theoretic style (short proof objects) vs natural deduction style; example $A \Rightarrow \neg\neg A$
- **11.6 Examples of logical derivations** — $(A \vee B) \Rightarrow (\neg A \Rightarrow B)$ in explicit natural deduction style; commutativity of $\vee$ ($sym\text{-}\vee$)
- **11.7 Suppressing unaltered parameter lists** — parameter list convention (suppress lists that literally mirror the context)
- **11.8 Rules for classical propositional logic** — primitive axiom exc-thrd$(A) := \bot\bot : A \vee \neg A$; derivation of doub-neg$(A) : \neg\neg A \Rightarrow A$; derived rules $\neg\neg$-in and $\neg\neg$-el; proof by contradiction; example $(\neg A \Rightarrow B) \Rightarrow (A \vee B)$
- **11.9 Alternative natural deduction rules for $\vee$** — $\vee$-in-alt1/alt2 (from $\neg A \Rightarrow B$ or $\neg B \Rightarrow A$) and $\vee$-el-alt1/alt2; examples proving $\neg(A \wedge B) \Leftrightarrow (\neg A \vee \neg B)$
- **11.10 Rules for constructive predicate logic** — $\forall$-in/$\forall$-el, $\exists$-in/$\exists$-el with the $\exists$-elimination proof-search strategy; examples $\exists x. P x \Rightarrow \forall y. (P y \Rightarrow Q y) \Rightarrow \exists z. Q z$ and $\exists \Rightarrow \neg \forall \neg$
- **11.11 Rules for classical predicate logic** — $\exists \Leftrightarrow \neg \forall \neg$ and $\forall \Leftrightarrow \neg \exists \neg$; alternative rules $\exists$-in-alt (from $\neg \forall x. \neg P x$ without a witness) and $\exists$-el-alt; example $\neg \forall x. P x \Rightarrow \exists y. \neg P y$

**Key Questions:**
1. How do flags encode the scope of assumptions and variables in a linear proof?
2. When is the natural deduction style preferable to the type-theoretic style for proof objects?
3. How is the classical rule $\neg\neg$-el justified from the primitive excluded third axiom?
4. How does the $\exists$-elimination strategy structure proof search when an existential hypothesis is available?
5. Why do the alternative classical rules for $\vee$ and $\exists$ avoid the need to produce witnesses?

---

### Chapter 12: Mathematics in $\lambda D$: a first attempt (pp. 257–278)

**Summary:** Formalises a first mathematical result — uniqueness of the least element of a partially ordered set — discovering and filling the missing foreknowledge along the way: Leibniz equality with substitutivity and congruence, partial orders, unique existence quantifiers, and the primitive $\iota$-descriptor for uniquely existing objects.

**Key Definitions & Concepts by Section:**
- **12.1 An example to start with** — least element lemma; the five questions (equality, proof objects, existence, uniqueness, proof)
- **12.2 Equality** — Leibniz equality $eq(S, x, y) \equiv \Pi P : S \to *. (P x \Leftrightarrow P y)$, notation $x =_S y$, eq-refl, substitutivity (eq-subs)
- **12.3 The congruence property of equality** — congruence for function application (eq-cong1 by unfolding the goal; eq-cong2 via the clever predicate $Q_1 \equiv \lambda z : S. (f x =_T f z)$)
- **12.4 Orders** — relations $\leq : S \to S \to *_p$, refl, trans, pre-ord, antisymm, part-ord; infix sugaring $x \leq_S y$
- **12.5 A proof about orders** — full flag-style proof of the first part of the lemma; deriving eq-sym and eq-trans from reflexivity + substitutivity (predicates $Q_2$, $Q_3$)
- **12.6 Unique existence** — Least predicate; quantifiers $\exists_{\geq 1}$, $\exists_{\leq 1}$ ($\forall y, z. (P y \Rightarrow P z \Rightarrow y = z)$), $\exists_1 \equiv \exists_{\geq 1} \wedge \exists_{\leq 1}$; completed formal lemma
- **12.7 The descriptor $\iota$** — primitive $\iota(S, P, u) := \bot\bot : S$ with $u : \exists_1 x : S. P x$; $\iota$-prop (the described element satisfies $P$); irrelevance of proof for $\iota$; defining the minimum operator Min
- **12.9 Further reading** — Church 1940, Russell's definite descriptions, Hilbert's $\varepsilon$-operator vs $\iota$, Axiom of Choice

**Key Questions:**
1. How does Leibniz's indiscernibility principle become a second order definition in $\lambda D$?
2. How do substitutivity and congruence differ in what they allow one to replace?
3. Why must unique existence be established before the $\iota$-descriptor may be used?
4. Why does the value of $\iota(S, P, u)$ not depend on which proof $u$ of uniqueness is supplied?

---

### Chapter 13: Sets and subsets (pp. 279–304)

**Summary:** Confronts the conflict between set-theoretic practice (undecidable membership, elements in many sets) and type theory (decidable typing, uniqueness of types), and resolves it by choosing the subsets-as-predicates approach; then formalises set operations, relations, equivalence classes, and maps, with proofs.

**Key Definitions & Concepts by Section:**
- **13.1 Dealing with subsets in $\lambda D$** — why subsets cannot be types (violates Uniqueness of Types and decidability); subsets as predicates $V : S \to *_p$; powerset $ps(S) := S \to *_p$; elementhood $x \ \varepsilon_S V \equiv V x$; $\subseteq$, $\cup$
- **13.2 Basic set-theoretic notions** — restricted quantification conventions ($\forall x \in V(P x) \leadsto \forall x : S. (x \varepsilon V \Rightarrow P x)$; $\exists x \in V(P x) \leadsto \exists x : S. (x \varepsilon V \wedge P x)$); set comprehension notation $\{x : S \mid V x\}$; subset equality $IS$, union, intersection, difference, complement; $\varepsilon$-in/$\varepsilon$-el; Leibniz equality on the powerset ($\hat{=}_{ps(S)}$) and axiom IS-prop
- **13.3 Special subsets** — empty set $\emptyset(S) \equiv \{x : S \mid \bot\}$, full-set $\{x : S \mid \neg \bot\}$; proof $\emptyset_S \subseteq V \subseteq \text{full-set}(S)$; $(V = \emptyset_S) \Leftrightarrow \exists x : S. (x \varepsilon V)$
- **13.4 Relations** — binary relations as $R : S \to S \to *_p$ (Curried), reflexive, symmetric, transitive, equivalence-relation; equivalence classes $[x]_R$; three characteristics of a partition; proof that overlapping classes coincide
- **13.5 Maps** — maps as functional relations ($\forall x \in S. \exists_1 y \in T. F x y$) vs type-theoretic functions ($F : S \to T$); connection via $\iota$; injective, surjective, bijective, inverse inv; functions on subsets ($F : \Pi x : S. (x \varepsilon V) \to T$); image and origin
- **13.6 Representation of mathematical notions** — many-to-one map of mathematics into $\lambda D$; ambiguity resolved by $*_s$/$*_p$ sugaring
- **13.8 Further reading** — ZF set theory, Russell's ramified type theory, alternatives rejected: powersets as types (inconsistent in $\lambda D$), $\Sigma$-types (Coq, PVS), subsets via embeddings

**Key Questions:**
1. Why does treating subsets as types break decidability of typing and Uniqueness of Types?
2. How does the subsets-as-predicates choice keep proof checking decidable?
3. How are bounded quantifiers $\forall x \in V$ and $\exists x \in V$ encoded over the ambient type?
4. How are type-theoretic functions and functional relations interconvertible?

---

### Chapter 14: Numbers and arithmetic in $\lambda D$ (pp. 305–348)

**Summary:** Builds arithmetic from the ground up: first Peano's axioms for $\mathbb{N}$, then an axiomatic theory of the integers $\mathbb{Z}$ with a bijective successor, a predecessor defined via $\iota$, and symmetric induction; $\mathbb{N}$ is recovered as the smallest subset of $\mathbb{Z}$ satisfying the natural-number condition; addition, subtraction, opposites, multiplication, inequalities and divisibility are defined via the Recursion Theorem for $\mathbb{Z}$ and a library of lemmas is proved.

**Key Definitions & Concepts by Section:**
- **14.1 The Peano axioms for natural numbers** — why Church numerals are rejected (induction not derivable, awkward predecessor, no integers); primitive $N, 0, s$; ax-nat1 ($\neg(s x = 0)$), ax-nat2 (injectivity of $s$), ax-nat3 (induction); Lemma $n = 0 \vee \exists m. (n = s m)$
- **14.2 Introducing integers the axiomatic way** — primitive $Z, 0, s$; ax-int1 ($s$ bijective); predecessor $p(y) := \iota x : Z. (s x = y)$; s-p-annihilation ($s(p y) = y$) and p-s-annihilation; ax-int2 (symmetric induction over $\mathbb{Z}$); $\mathbb{N}$ defined as $\lambda x : Z. \Pi P : Z \to *. (nat\text{-}cond(P) \Rightarrow P x)$; nat-smallest; ax-int3 ($\neg(p 0 \varepsilon N)$) rules out finite loop models
- **14.3 Basic properties of the 'new' $\mathbb{N}$** — nat-prop1/nat-prop2 (Peano axioms as theorems); nat-ind (induction for $\mathbb{N}$ as subset, proved by upgrading $P$ to $Q \equiv \lambda z. (z \varepsilon N \wedge P z)$); nat-split, pos ($p x \varepsilon N$), neg ($\neg(x \varepsilon N)$), tripartition property
- **14.4 Integer addition** — recursive equations $+m(0) = m$, $+m(s n) = s(+m n)$; the downward equation is derivable; Recursion Theorem for $\mathbb{Z}$ (Theorem 14.4.3) and restricted version with bijection (Theorem 14.4.5); $+m$ defined via $\iota$; plus-i/ii/iii
- **14.5 An example of a basic computation** — fully formal proof that $1 + 2 = 3$ using eq-refl, eq-cong1, eq-trans; suggestion of many-fold transitivity lemmas
- **14.6 Arithmetical laws for addition** — reversals (plus-i/ii/iii-alt) by symmetric induction; commutativity, associativity, Left/Right Cancellation Laws
- **14.7 Closure under addition** — closure of $\mathbb{N}$ under addition (proof by nat-ind); characterisation of negative numbers ($neg(x) \Leftrightarrow \exists y. (pos(y) \wedge x + y = 0)$); closure of negatives
- **14.8 Integer subtraction** — uniqueness of difference; $x - y := \iota z : Z. (z + y = x)$; subtr-prop1/2; cancellation laws; $x - s y = p(x - y)$ etc.
- **14.9 The opposite of an integer** — $-x := 0 - x$; lemmas $(-x) + x = 0$, $-(x + y) = (-x) - y$, $-(-x) = x$; $pos(x) \Leftrightarrow neg(-x)$; $\mathbb{Z}$ consists of naturals and their opposites
- **14.10 Inequality relations on $\mathbb{Z}$** — $x \leq y \equiv (y - x) \varepsilon N$, $x < y \equiv (x \leq y \wedge x \neq y)$, $\geq$, $>$ as reverses; partial order properties; lower bound lw-bnd; $0$ is a lower bound of every subset of $\mathbb{N}$
- **14.11 Multiplication of integers** — recursion scheme $\times_m(0) = 0$, $\times_m(s n) = \times_m n + m$ defined via the Recursion Theorem with bijection $f \equiv \lambda v. (v + m)$; times-i/ii/iii; Right/Left Distributivity; commutativity, associativity; sign rules; product zero lemma; cancellation with $z \neq 0$
- **14.12 Divisibility** — $div(m, n) \equiv \exists q : Z. (m \cdot q = n)$, notation $m \mid n$; properties with $0$; com-div, gcd-prop, coprime; gcd defined via $\iota$ using the Maximum Theorem; gcd-pos
- **14.13 Irrelevance of proof** — objects defined with $\iota$ do not depend on the particular proof supplied; no global proof-irrelevance axiom is added

**Key Questions:**
1. Why are the integers introduced axiomatically instead of through Church numerals or quotients of $\mathbb{N} \times \mathbb{N}$?
2. What does symmetric induction state for $\mathbb{Z}$, and why does it need both $s$ and $p$ steps?
3. How does the Recursion Theorem for $\mathbb{Z}$ license recursive definitions without primitive recursion in the syntax?
4. How is $\mathbb{N}$ characterised as the smallest subset of $\mathbb{Z}$ satisfying nat-cond?
5. What would go wrong without ax-int3 ($\neg(p 0 \varepsilon N)$)?
6. Why is proof irrelevance automatic for gcd and subtraction as defined here?

---

### Chapter 15: An elaborated example (pp. 349–378)

**Summary:** The capstone formalisation: a complete $\lambda D$ proof of the restricted Bézout's Lemma (coprime positive $m, n$ imply $\exists x, y \in \mathbb{Z}. (m x + n y = 1)$), after developing the required foreknowledge — the minimum operator for subsets, the Minimum Theorem, and the Division Theorem — then filling nine deferred proof holes and demonstrating specialisation to $m = 55, n = 28$.

**Key Definitions & Concepts by Section:**
- **15.1 Formalising a proof of Bézout's Lemma** — statement of the restricted theorem; inventory of implicit foreknowledge (intersection, minimum, Minimum Theorem, Division Theorem, arithmetic)
- **15.2 Preparatory work** — least element of a subset ($least(S, R, T, m) \equiv m \varepsilon T \wedge \text{lw-bnd}$), leastZ, uniqueness ($\exists_{\leq 1}$), min via $\iota$; formulation of the Minimum Theorem (min-the, min-uni-the, minimum, min-prop); formulation of the Division Theorem (div-the: $\exists q, r. (m = q \cdot d + r \wedge 0 \leq r < d)$)
- **15.3 Part I of the proof** — context ($m, n : Z$, ass1: $m > 0$, ass2: $n > 0$, ass3: coprime$(m, n)$); set $S$ of linear combinations; $N^+$; $S^+ := S \cap N^+$; non-emptiness via witness $m$; lower bound $1$; $d := \text{minimum}(S^+)$
- **15.4 Part II of the proof** — $d \varepsilon S^+$ gives $d = m x_0 + n y_0$ and $d > 0$; Division Theorem gives $m = q d + r$; computation shows $r \in S$; contradiction ($r < d$ vs $r \geq d$) yields $r = 0$; hence $d \mid m$
- **15.5 Part III of the proof** — $d \mid n$ obtained by swapping parameters in the previous derivation ($a37(n, m, ass2, ass1, a38)$); coprimality forces $d = 1$; hence $1 \varepsilon S$; conclusion; instantiating the proof at $m = 55, n = 28$; discussion of full unfolding vs compact proof term
- **15.6 The holes in the proof** — nine holes (#1 $\leq$ is a partial order on $\mathbb{Z}$; #2 $m = m \cdot 1 + n \cdot 0$; #3 lower bound of $S^+$; #4–#5 algebraic rewrites; #6–#7 order reasoning; #8 arithmetic; #9 symmetry of coprime)
- **15.7 The Minimum Theorem for $\mathbb{Z}$** — proof strategy: climb upward from a lower bound until hitting $T$; formally prove existence of a maximal lower bound $z$ ($\text{lw-bnd}(T, z) \wedge \neg \text{lw-bnd}(T, s z)$) by contradiction using the variant of symmetric induction starting at $l$, then show $z \varepsilon T$ by contradiction
- **15.8 The Division Theorem** — proved via the Maximum Theorem (mirror of the Minimum Theorem, using $\geq$): the set $D$ of multiples of $d$ below $m$ is non-empty and bounded above; its maximum $l = q \cdot d$ gives quotient $q$ and remainder $r := m - q \cdot d$; $r < d$ shown by contradiction ($(q+1) \cdot d \in D$ would exceed the maximum)

**Key Questions:**
1. How does parameter instantiation turn the general proof $a44(m, n, ass1, ass2, ass3)$ into a specialised proof for $55$ and $28$?
2. Why must non-emptiness and boundedness of $S^+$ be explicitly proved in the formal version but not in the informal one?
3. How do the Minimum Theorem and the Division Theorem enter the proof of Bézout's Lemma?
4. What is the methodological role of holes, hints, and skeleton proofs in a large formalisation?
5. Why is the Maximum Theorem proved from the Minimum Theorem rather than from scratch?

---

### Chapter 16: Further perspectives (pp. 379–390)

**Summary:** Summarises why $\lambda D$ is a practical foundation for formalising mathematics (precision, decidability of proof checking, definitions and proofs as first-class citizens, flag-style contexts), reviews proof assistants based on type theory and the de Bruijn criterion, and sketches future challenges: automation, high-level explanation, proof sketches, cross-assistant export, and didactics.

**Key Definitions & Concepts by Section:**
- **16.1 Useful applications of $\lambda D$** — formalisation of mathematics, checking of mathematics (correctness handled by the system, relevance left to the user), proof development guided by flag contexts, libraries of definitions and theorems
- **16.2 Proof assistants based on type theory** — computer-checked proofs (type of $p$ computed and compared with the claimed statement $A$ via $\beta\delta$-conversion); Automath as origin; interactive proving (term refinement, holes); Coq, Nuprl, Agda; automation and tactics; de Bruijn criterion (every generated proof term is re-checked by a small kernel); technical assistance (sugaring, search); comparison with CIC's inductive types; state of the art (Four Color Theorem, Odd-Order Theorem, Flyspeck)
- **16.3 Future of the field** — increasing use of proof assistants; challenges: automation (combining symbolic theorem proving and machine learning), high-level explanation and folding/unfolding of proof parts, step-wise proof development (formal proof sketches), export between proof assistants, didactics for novices
- **16.5 Further reading** — historical lineage (Russell/Whitehead, Church, de Bruijn/Automath, Martin-Löf, Girard), Coq/Lego/LF/HOL/Isabelle/Agda/Matita/Nuprl, Homotopy Type Theory and Univalent Foundations

**Key Questions:**
1. What is the de Bruijn criterion, and why does it make tactics trustworthy regardless of how clever they are?
2. How does the schematic proof-checking pipeline (informal proof $\to$ formal term $\to$ computed type $\to$ compare with statement) work?
3. What distinguishes $\lambda D$'s treatment of recursion and data types from Coq's inductive types?
4. Which obstacles currently prevent proof assistants from becoming standard tools for working mathematicians?

---

### Appendices (pp. 391–409)

**Summary:** Reference material consolidating the book's formal apparatus.

- **Appendix A: Logic in $\lambda D$ (pp. 391–396)** — complete list of natural deduction rules: constructive propositional logic ($\Rightarrow$, $\bot$, $\neg$, $\wedge$, $\vee$, $\Leftrightarrow$ with all in/el rules), classical propositional logic (exc-thrd, $\neg\neg$-in, doub-neg, $\neg\neg$-el, alternative $\vee$ rules), constructive predicate logic ($\forall$-in/el, $\exists$-in/el with strategies), classical predicate logic ($\exists$-in-alt, $\exists$-el-alt)
- **Appendix B: Arithmetical axioms, definitions and lemmas (pp. 397–402)** — catalogue of all arithmetic results of Chapter 14 (axioms ax-int1/2/3, definitions of $N$, $pos$, $neg$, $+$, $-$, $\cdot$, $\leq$, $<$, div, gcd, and all numbered lemmas)
- **Appendix C: Two complete example proofs in $\lambda D$ (pp. 403–408)** — fully worked-out proofs (all hints replaced by proof objects): closure of $\mathbb{N}$ under addition, and the Minimum Theorem
- **Appendix D: Derivation rules for $\lambda D$ (p. 409)** — the complete rule set: (sort), (var), (weak), (form), (appl), (abst), (conv), (def), (def-prim), (inst), (inst-prim), plus the derived rule (par)

**Key Questions:**
1. How do the constructive and classical rule sets in Appendix A differ, and which rules depend on the exc-thrd axiom?
2. In the complete proofs of Appendix C, how are the logical natural deduction rules instantiated compared with the shortened versions in the main text?
3. Which rules distinguish $\lambda D$ from the underlying $\lambda$-cube rules of Figure 6.4?
