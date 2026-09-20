# Programming in Martin-Löf's Type Theory: An Introduction — Guidelines

## Header

**Title:** Programming in Martin-Löf's Type Theory: An Introduction
**Author(s):** Bengt Nordström, Kent Petersson, Jan M. Smith
**Publication:** Oxford University Press, 1990. Out of print; a free electronic version is distributed by the authors (Department of Computing Sciences, University of Göteborg / Chalmers).

**Brief Summary:**
This book gives a self-contained, semantics-first introduction to Per Martin-Löf's type theory as a formalism in which specifications, programs, and proofs of program correctness all live in the same language. Its organizing idea is the identification of propositions with sets (a Curry–Howard correspondence): a specification is a set, a program satisfying it is an element of that set, and a constructive proof that the specification is satisfiable literally *is* the program. The book develops this idea in four stages — a polymorphic basic set theory, a separate subset theory needed to recover a usable comprehension principle, a monomorphic theory built from a still more primitive notion of type, and a closing sequence of worked examples of program derivation and abstract data type specification.

**Intent of the Author:**
The authors, students and later collaborators of Martin-Löf, wrote the book to make his type theory accessible "from a computing science perspective" to researchers and graduate students interested in the foundations of computing, after ten years of using the theory in practice had forced them to refine and stabilize its presentation. They aim to justify every rule of the formal system directly from a computational semantics, rather than presenting the rules as an unexplained calculus.

---

## Topic List

1. **Propositions as Sets (The Curry–Howard Correspondence)** : [[Propositions-as-Sets-(The-Curry-Howard-Correspondence)|Link]]
   - The four basic judgement forms of type theory : [[Propositions-as-Sets-(The-Curry-Howard-Correspondence)|Link]]
   - Heyting's constructive interpretation of the logical constants : [[Propositions-as-Sets-(The-Curry-Howard-Correspondence)|Link]]
   - Propositions as tasks and specifications of programs : [[Propositions-as-Sets-(The-Curry-Howard-Correspondence)|Link]]
   - Historical formulations of Martin-Löf's type theory : [[Propositions-as-Sets-(The-Curry-Howard-Correspondence)|Link]]
   - Type theory versus the Calculus of Constructions : [[Propositions-as-Sets-(The-Curry-Howard-Correspondence)|Link]]

2. **The Theory of Expressions** : [[The-Theory-of-Expressions|Link]]
   - Application, abstraction, combination and selection : [[Specification-of-Abstract-Data-Types|Link]]
   - Arities as a discipline against self-application : [[The-Theory-of-Expressions|Link]]
   - Definitional equality between expressions : [[The-Theory-of-Expressions|Link1]], [[Equality-Sets|Link2]], [[The-Cartesian-Product-of-Two-Sets-and-Conjunction|Link3]]
   - Definitions, definiendum and definiens : [[The-Theory-of-Expressions|Link]]

3. **The Semantics of Judgement Forms** : [[The-Semantics-of-Judgement-Forms|Link]]
   - Canonical and noncanonical expressions : [[The-Semantics-of-Judgement-Forms|Link]]
   - Categorical judgements about sets and elements : [[The-Semantics-of-Judgement-Forms|Link]]
   - Hypothetical judgements and contexts : [[The-Semantics-of-Judgement-Forms|Link1]], [[the_semantic_judge_forms_qwen|Link2]]
   - Extensionality of propositional functions : [[The-Semantics-of-Judgement-Forms|Link]]

4. **General Proof Rules** : [[General-Proof-Rules|Link]]
   - Formation, introduction, elimination and equality rules : [[Natural-Numbers-and-Lists|Link1]], [[Equality-Sets|Link2]]
   - Natural deduction style presentation : [[General-Proof-Rules|Link]]
   - The assumption rule : [[General-Proof-Rules|Link]]
   - Substitution rules : [[Natural-Numbers-and-Lists|Link1]], [[General-Proof-Rules|Link2]]

5. **Enumeration Sets, Truth and Falsity** : [[Enumeration-Sets,-Truth-and-Falsity|Link]]
   - Finite enumeration sets and case analysis : [[Enumeration-Sets,-Truth-and-Falsity|Link]]
   - The empty set and absurdity : [[Enumeration-Sets,-Truth-and-Falsity|Link]]
   - The one-element set and the true proposition : [[Enumeration-Sets,-Truth-and-Falsity|Link]]
   - The set Bool : [[Enumeration-Sets,-Truth-and-Falsity|Link]]

6. **The Cartesian Product of a Family and the Universal Quantifier** : [[The-Cartesian-Product-of-a-Family-and-the-Universal-Quantifier|Link]]
   - Functions as canonical elements of a $\Pi$-set : [[The-Cartesian-Product-of-a-Family-and-the-Universal-Quantifier|Link]]
   - The selector apply and the alternative selector funsplit : [[The-Cartesian-Product-of-a-Family-and-the-Universal-Quantifier|Link]]
   - The restricted function set and implication : [[The-Cartesian-Product-of-a-Family-and-the-Universal-Quantifier|Link]]
   - Structural induction versus $\beta$-reduction as elimination principles : [[The-Cartesian-Product-of-a-Family-and-the-Universal-Quantifier|Link]]

7. **Equality Sets** : [[Equality-Sets|Link]]
   - Intensional equality and its induction principle : [[The-Cartesian-Product-of-Two-Sets-and-Conjunction|Link1]], [[Equality-Sets|Link2]]
   - Extensional equality and the strong elimination rule : [[Equality-Sets|Link]]
   - Decidability of judgemental equality : [[Equality-Sets|Link]]
   - $\eta$-equality for functions : [[Equality-Sets|Link]]

8. **Natural Numbers and Lists** : [[Natural-Numbers-and-Lists|Link]]
   - Primitive recursion via natrec : [[Natural-Numbers-and-Lists|Link]]
   - Mathematical induction as N-elimination : [[Natural-Numbers-and-Lists|Link]]
   - List recursion via listrec
   - Peano's axioms in type theory : [[Natural-Numbers-and-Lists|Link1]], [[Propositions-as-Sets-(The-Curry-Howard-Correspondence)|Link2]], [[The-Universe-of-Small-Sets|Link3]]

9. **The Cartesian Product of Two Sets and Conjunction** : [[The-Cartesian-Product-of-Two-Sets-and-Conjunction|Link]]
   - Pairing and the selector split : [[The-Cartesian-Product-of-Two-Sets-and-Conjunction|Link]]
   - Projections fst and snd : [[The-Cartesian-Product-of-Two-Sets-and-Conjunction|Link]]
   - Extensional equality of functions in a $\Pi$-set : [[The-Cartesian-Product-of-Two-Sets-and-Conjunction|Link]]

10. **Disjoint Unions and the Existential Quantifier** : [[Disjoint-Unions-and-the-Existential-Quantifier|Link]]
    - Disjoint union of two sets and disjunction : [[Disjoint-Unions-and-the-Existential-Quantifier|Link]]
    - Disjoint union of a family and the existential quantifier : [[Disjoint-Unions-and-the-Existential-Quantifier|Link]]
    - The selector when : [[Disjoint-Unions-and-the-Existential-Quantifier|Link]]

11. **The Universe of Small Sets** : [[The-Universe-of-Small-Sets|Link]]
    - Coding sets as elements of the universe : [[The-Universe-of-Small-Sets|Link]]
    - The decoding family Set
    - Peano's fourth axiom and its dependence on a universe : [[The-Universe-of-Small-Sets|Link1]], [[Specification-of-Abstract-Data-Types|Link2]]
    - Structural induction on the universe via urec : [[The-Universe-of-Small-Sets|Link]]
    - Non-normalizing terms under extensional equality : [[Well-Orderings-and-General-Trees|Link1]], [[Subsets-and-the-Subset-Theory|Link2]], [[Equality-Sets|Link3]]

12. **Well-Orderings and General Trees** : [[Well-Orderings-and-General-Trees|Link]]
    - The well-order set constructor : [[Well-Orderings-and-General-Trees|Link]]
    - Representing inductively defined sets as well-orderings
    - The need for extensional equality : [[Well-Orderings-and-General-Trees|Link]]
    - General trees for mutually dependent inductive definitions
    - Trees as the least fixed point of a set equation

13. **Subsets and the Subset Theory** : [[Subsets-and-the-Subset-Theory|Link]]
    - Subsets by comprehension in the basic set theory : [[Subsets-and-the-Subset-Theory|Link]]
    - The weakness of subset-elimination in the basic theory : [[Subsets-and-the-Subset-Theory|Link]]
    - The subset theory as a translated second theory : [[Subsets-and-the-Subset-Theory|Link]]
    - Stable predicates and comprehension under extensional equality : [[Subsets-and-the-Subset-Theory|Link]]
    - Universes and propositions in the subset theory : [[Subsets-and-the-Subset-Theory|Link]]

14. **The Theory of Types (Monomorphic Type Theory)** : [[The-Theory-of-Types-(Monomorphic-Type-Theory)|Link]]
    - Types as a more primitive notion than sets : [[Natural-Numbers-and-Lists|Link]]
    - The type Set and the family El : [[The-Theory-of-Types-(Monomorphic-Type-Theory)|Link]]
    - Families of types and function types : [[The-Theory-of-Types-(Monomorphic-Type-Theory)|Link]]
    - Assumptions as objects of an arbitrary type : [[Specification-of-Abstract-Data-Types|Link]]

15. **Programming as Program Derivation** : [[Programming-as-Program-Derivation|Link]]
    - Program verification versus program derivation : [[Programming-as-Program-Derivation|Link]]
    - Tactics obtained by reading rules bottom-up : [[Programming-as-Program-Derivation|Link]]
    - Top-down goal-directed derivation
    - Stronger elimination rules : [[Programming-as-Program-Derivation|Link]]
    - Decidable predicates : [[Programming-as-Program-Derivation|Link]]

16. **Specification of Abstract Data Types** : [[Specification-of-Abstract-Data-Types|Link]]
    - Modules as dependent tuples : [[Specification-of-Abstract-Data-Types|Link]]
    - Specifying a stack using dependent sums and the universe : [[Specification-of-Abstract-Data-Types|Link]]
    - Parameterized modules : [[Specification-of-Abstract-Data-Types|Link]]
    - Computable equality on a set : [[Specification-of-Abstract-Data-Types|Link]]

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 1–8)

**Summary:** Introduces type theory as a formalism, developed by Per Martin-Löf, for program construction in which specifications and programs are expressed in the same language; previews the book's four-part structure and its semantics-first methodology. : [[Natural-Numbers-and-Lists|Link]]

**Key Definitions & Concepts by Section:**
- **1.1 Using type theory for programming** — program verification (proving a given program correct) vs. program derivation (deriving a program from a specification), specification as a set, program as an element, canonical/noncanonical program forms, constructors and selectors, lazy evaluation
- **1.2 Constructive mathematics** — Brouwer's intuitionism, Bishop's constructive analysis, a constructive proof of $(\forall x\in A)(\exists y\in B)P(x,y)$ read directly as a program
- **1.3 Different formulations of type theory** — the Curry–Howard interpretation of propositions as types/sets, Martin-Löf's successive formulations from 1971 to 1986, Girard's paradox refuting the axiom $V\in V$, the Calculus of Constructions (Prop, Type) : [[Propositions-as-Sets-(The-Curry-Howard-Correspondence)|Link]]
- **1.4 Implementations of programming logics** — AUTOMATH, LCF, Nuprl, Edinburgh LF, Isabelle, the Calculus of Constructions

**Key Questions:**
1. In what sense is type theory simultaneously a programming language, a specification language, and a programming logic?
2. Why does the requirement that every well-typed program terminates distinguish type theory from languages like ML or Hope?
3. What inconsistency forced Martin-Löf to abandon the reflexive universe $V\in V$ of his 1971 formulation?

---

### Chapter 2: The identification of sets, propositions and specifications (pp. 9–12)

**Summary:** Explains the propositions-as-sets identification via Heyting's constructive semantics of the logical connectives, and independently via Kolmogorov's problem/task interpretation, showing how each connective corresponds to a set-forming operation. : [[Propositions-as-Sets-(The-Curry-Howard-Correspondence)|Link1]], [[The-Semantics-of-Judgement-Forms|Link2]]

**Key Definitions & Concepts:**
- **2.1 Propositions as sets** — a proof of $A\supset B$ as a function; $A\ \&\ B$ identified with $A\times B$; $A\vee B$ identified with $A+B$; negation $\neg A \equiv A\supset\bot$; $(\exists x\in A)B(x)$ identified with $(\Sigma x\in A)B(x)$; $(\forall x\in A)B(x)$ identified with $(\Pi x\in A)B(x)$; the equality set $a=_A b$ : [[Propositions-as-Sets-(The-Curry-Howard-Correspondence)|Link]]
- **2.2 Propositions as tasks and specifications of programs** — Kolmogorov's interpretation of propositions as problems/tasks, and its extension to specifying programs : [[Propositions-as-Sets-(The-Curry-Howard-Correspondence)|Link]]

**Key Questions:**
1. Why is the law of excluded middle not valid under the constructive reading of disjunction?
2. How does identifying $(\exists x\in A)B(x)$ with $(\Sigma x\in A)B(x)$ turn an existence proof into a program that computes a witness?

---

### Chapter 3: Expressions and definitional equality (pp. 13–22)

**Summary:** Develops Martin-Löf's general theory of syntactic expressions — application, abstraction, combination and selection — and introduces arities as a discipline that rules out unrestricted self-application, guaranteeing that definitional equality is decidable. : [[General-Proof-Rules|Link1]], [[The-Theory-of-Expressions|Link2]], [[Equality-Sets|Link3]]

**Key Definitions & Concepts by Section:**
- **3.1 Application** — application of an expression to arguments, $e(e_1,\ldots,e_n)$ : [[The-Cartesian-Product-of-a-Family-and-the-Universal-Quantifier|Link]]
- **3.2 Abstraction** — functional abstraction $(x)e$, definitional (intensional) equality $\equiv$
- **3.3 Combination** — combination $e_1,e_2,\ldots,e_n$ : [[Natural-Numbers-and-Lists|Link]]
- **3.4 Selection** — selection $(e).i$ : [[Disjoint-Unions-and-the-Existential-Quantifier|Link]]
- **3.5 Combinations with named components** — named combinations $i_1:e_1,\ldots,i_n:e_n$ : [[Subsets-and-the-Subset-Theory|Link]]
- **3.6 Arities** — Definition 1 (arities: $0$; $(\alpha_1\otimes\cdots\otimes\alpha_n)$; $(\alpha\to\beta)$); why unrestricted self-application such as $((x)x(x))((x)x(x))$ makes definitions ineliminable
- **3.7 Definitions** — definiendum, definiens, abbreviatory definitions $c\equiv e$ : [[The-Cartesian-Product-of-a-Family-and-the-Universal-Quantifier|Link]]
- **3.8 Definition of expressions of a certain arity** — the seven formation clauses for variables, constants, application, abstraction, combination and selection
- **3.9 Definition of equality between expressions** — the fifteen equality rules, including $\beta$-, $\xi$-, $\alpha$-, $\eta$-rules for abstraction, and reflexivity/symmetry/transitivity : [[The-Theory-of-Expressions|Link]]

**Key Questions:**
1. Why must every expression carry an arity, and how does this rule out ill-formed expressions like $succ(succ)$?
2. Why is decidability of definitional equality essential for a formal system of proof rules such as Modus Ponens?

---

### Chapter 4: The semantics of the judgement forms (pp. 25–34)

**Summary:** Gives the direct, computation-based semantics of type theory's four categorical judgement forms and their hypothetical (context-dependent) generalizations, grounding "$A$ is a set" in knowing how to form and identify canonical elements rather than in any prior mathematical theory. : [[The-Semantics-of-Judgement-Forms|Link]]

**Key Definitions & Concepts by Section:**
- Canonical and noncanonical expressions; evaluated vs. fully evaluated expressions; normal-order (lazy) evaluation
- **4.1 Categorical judgements** — the four forms $A\ set$, $A=B$, $a\in A$, $a=b\in A$, and the propositional readings $A\ prop$, $A\ true$ : [[The-Semantics-of-Judgement-Forms|Link1]], [[the_semantic_judge_forms_qwen|Link2]]
- **4.2 Hypothetical judgements with one assumption** — contexts; extensionality of a family under an assumption : [[The-Semantics-of-Judgement-Forms|Link]]
- **4.3 Hypothetical judgements with several assumptions** — meaning of a judgement in a context of length $n$, by induction on context length : [[The-Semantics-of-Judgement-Forms|Link1]], [[the_semantic_judge_forms_qwen|Link2]]

**Key Questions:**
1. What does it mean, at the semantic level, "to know that $A$ is a set" — and why does this explanation not presuppose any other mathematical theory?
2. Why must a propositional function $A(x)$ be extensional as part of what it means to be a family of sets?

---

### Chapter 5: General rules (pp. 35–40)

**Summary:** Introduces the four-part schema — formation, introduction, elimination and equality rules — repeated for every set former in the book, together with the general structural rules (assumption, equality, substitution) justified directly from the semantics of Chapter 4. : [[General-Proof-Rules|Link]]

**Key Definitions & Concepts by Section:**
- The four kinds of rules for each set former: formation, introduction, elimination, equality
- **5.1 Assumptions** — the Assumption rule : [[The-Cartesian-Product-of-a-Family-and-the-Universal-Quantifier|Link]]
- **5.2 Propositions as sets** — the Proposition as set rule : [[Propositions-as-Sets-(The-Curry-Howard-Correspondence)|Link]]
- **5.3 Equality rules** — reflexivity, symmetry, transitivity, for both element and set equality : [[Equality-Sets|Link1]], [[The-Theory-of-Expressions|Link2]]
- **5.4 Set rules** — Set equality : [[Equality-Sets|Link1]], [[Natural-Numbers-and-Lists|Link2]]
- **5.5 Substitution rules** — substitution in sets, elements, equal sets, equal elements; simultaneous substitution of $n$ variables : [[Natural-Numbers-and-Lists|Link1]], [[General-Proof-Rules|Link2]]

**Key Questions:**
1. Why does the elimination rule for a set correspond to a structural-induction principle, and what role does the selector play?
2. Why are simultaneous ($n$-variable) substitution rules needed in addition to single-variable substitution?

---

### Chapter 6: Enumeration sets (pp. 41–46)

**Summary:** Introduces finite enumeration sets $\{i_1,\ldots,i_n\}$ as the simplest set former, and derives the empty set/absurdity, the one-element set/truth, and the booleans as special cases. : [[Enumeration-Sets,-Truth-and-Falsity|Link]]

**Key Definitions & Concepts by Section:**
- Enumeration set $\{i_1,\ldots,i_n\}$, selector $case$
- **6.1 Absurdity and the empty set** — $\emptyset\equiv\{\}$, $\bot\equiv\{\}$, $\bot$-elimination (ex falso quodlibet) : [[Enumeration-Sets,-Truth-and-Falsity|Link]]
- **6.2 The one-element set and the true proposition** — $T\equiv\{tt\}$, truth introduction/elimination : [[Enumeration-Sets,-Truth-and-Falsity|Link]]
- **6.3 The set Bool** — $Bool\equiv\{true,false\}$, conditional $if\ b\ then\ c\ else\ d$, the distinction between the canonical element $true\in Bool$ and the judgement "$C\ true$" : [[Enumeration-Sets,-Truth-and-Falsity|Link]]

**Key Questions:**
1. Why does the empty set have no introduction rule yet still has an elimination rule, and what natural-deduction principle does it correspond to?
2. What is the difference between the canonical element $true\in Bool$ and the judgement "the proposition $C$ is true"?

---

### Chapter 7: Cartesian product of a family of sets (pp. 47–56)

**Summary:** Introduces the dependent function set $\Pi(A,B)$, whose result type may depend on the argument's value, and shows it interprets both the universal quantifier and the non-dependent function space, implication included. : [[The-Cartesian-Product-of-Two-Sets-and-Conjunction|Link1]], [[The-Cartesian-Product-of-a-Family-and-the-Universal-Quantifier|Link2]]

**Key Definitions & Concepts by Section:**
- $\Pi(A,B)$, $(\Pi x\in A)B(x)$, canonical elements $\lambda(b)$, selector $apply$, infix $x\cdot y$
- **7.1 The formal rules and their justification** — $\Pi$-formation/introduction/elimination 1/equality 1; syntactic function (abstraction) vs. function element
- **7.2 An alternative primitive non-canonical form** — $funsplit$, justified by structural induction rather than $\beta$-reduction; $\Pi$-elimination 2/equality 2 : [[the_semantic_judge_forms_qwen|Link]]
- **7.3 Constants defined in terms of the $\Pi$ set** — 7.3.1 the universal quantifier $\forall\equiv\Pi$; 7.3.2 the function set $A\to B$; 7.3.3 implication $\supset\ \equiv\ \to$ and Schroeder-Heister's weakened formation rule

**Key Questions:**
1. Why is the generality of $\Pi(A,B)$ essential for interpreting the universal quantifier and for expressing dependent specifications like sorting?
2. What is the difference between the selector $apply$ and $funsplit$, and why does the book introduce both?

---

### Chapter 8: Equality sets (pp. 57–62)

**Summary:** Introduces two competing set-theoretic renderings of propositional equality — intensional $Id(A,a,b)$, with a genuine induction-style elimination rule, and extensional $Eq(A,a,b)$, with a strong (non-structural) elimination rule that makes judgemental equality undecidable. : [[Equality-Sets|Link]]

**Key Definitions & Concepts by Section:**
- **8.1 Intensional equality** — $Id(A,a,b)$, $id(a)$, selector $idpeel$, derived rules $symm$, $trans$, $subst$ : [[Equality-Sets|Link]]
- **8.2 Extensional equality** — $Eq(A,a,b)$, strong Eq-elimination, the derived induction rule for Eq, convertibility and decidability : [[Equality-Sets|Link1]], [[Subsets-and-the-Subset-Theory|Link2]], [[The-Cartesian-Product-of-Two-Sets-and-Conjunction|Link3]], [[Well-Orderings-and-General-Trees|Link4]]
- **8.3 $\eta$-equality for elements in a $\Pi$ set** — judgemental $\eta$-equality is derivable using $Eq$ but not from $Id$ alone : [[The-Cartesian-Product-of-Two-Sets-and-Conjunction|Link1]], [[The-Cartesian-Product-of-a-Family-and-the-Universal-Quantifier|Link2]]

**Key Questions:**
1. Why does the strong elimination rule for $Eq$ make judgemental equality undecidable, and why is $Id$ preferred "when possible"?
2. How are the derived rules $symm$, $trans$ and $subst$ for propositional equality built purely from $Id$-elimination?

---

### Chapter 9: Natural numbers (pp. 63–66)

**Summary:** Introduces $N$ with constructors $0$ and $succ$, the recursor $natrec$ for primitive recursion, and shows how N-elimination justifies mathematical induction (Peano's fifth axiom) and lets addition and multiplication be defined. : [[Natural-Numbers-and-Lists|Link1]], [[Well-Orderings-and-General-Trees|Link2]]

**Key Definitions & Concepts:**
- $N$, $0$, $succ$, selector $natrec$; defined operations $\oplus$ (addition), $*$ (multiplication)
- N-elimination and its correspondence to Peano's fifth axiom (mathematical induction)
- Peano's third axiom (injectivity of successor) as a derived rule using $pred$
- Peano's fourth axiom ($0\neq succ(n)$), whose proof is deferred to the universe (Chapter 14)

**Key Questions:**
1. How does the computation rule for $natrec$ simultaneously justify primitive recursion and mathematical induction?
2. Why can't Peano's fourth axiom be proved without a universe?

---

### Chapter 10: Lists (pp. 67–72)

**Summary:** Introduces $List(A)$ with constructors $nil$ and $cons$ and the recursor $listrec$, and works through a full formal proof that list append is associative as an extended example of propositional equality reasoning.

**Key Definitions & Concepts:**
- $List(A)$, $nil$, $cons$ (written $a.l$), selector $listrec$; List-elimination/equality rules
- Worked example: $append$ ($@$) and the formal proof of associativity of $@$, using List-elimination, $Id$-introduction, $subst$ and $trans$

**Key Questions:**
1. Why does proving associativity of append require switching from judgemental to propositional equality partway through the induction step?
2. What is the correspondence between the informal calculational proof and the formal derivation using $listrec$?

---

### Chapter 11: Cartesian product of two sets (pp. 73–78)

**Summary:** Introduces the non-dependent pair set $A\times B$ as a special case of $\Sigma$, defines projections via the selector $split$, interprets conjunction, and proves that $Eq$ (but not $Id$) validates extensionality of functions. : [[The-Cartesian-Product-of-Two-Sets-and-Conjunction|Link]]

**Key Definitions & Concepts by Section:**
- $A\times B$, pairs $\langle a,b\rangle$, selector $split$, projections $fst$, $snd$; $\times$-formation/introduction/elimination/equality
- Conjunction $\&\ \equiv\ \times$; logical equivalence $\Leftrightarrow$
- **11.2 Extensional equality on functions** — the theorem $(\forall x\in A)Eq(B(x),f\cdot x,g\cdot x)\Leftrightarrow Eq(\Pi(A,B),f,g)$, proved using $\eta$-conversion : [[The-Cartesian-Product-of-Two-Sets-and-Conjunction|Link]]

**Key Questions:**
1. Why can $\langle fst(z),snd(z)\rangle=_{A\times B} z$ be proved propositionally even though it does not hold judgementally?
2. Why is functional extensionality provable using $Eq$ but not expected for $Id$?

---

### Chapter 12: Disjoint union of two sets (pp. 79–80)

**Summary:** Introduces $A+B$ with constructors $inl$/$inr$ and selector $when$, interpreting disjunction and giving its natural deduction rules. : [[Disjoint-Unions-and-the-Existential-Quantifier|Link]]

**Key Definitions & Concepts:**
- $A+B$, $inl$, $inr$, selector $when$; $+$-formation/introduction/elimination/equality
- Disjunction $\vee\ \equiv\ +$ and its natural deduction rules

**Key Questions:**
1. Why must a proof of $A\vee B$ record which disjunct was proved, unlike the classical reading of disjunction?

---

### Chapter 13: Disjoint union of a family of sets (pp. 81–82)

**Summary:** Generalizes the pair set to the dependent sum $\Sigma(A,B)$, interpreting the existential quantifier and reusing the selector $split$. : [[Disjoint-Unions-and-the-Existential-Quantifier|Link]]

**Key Definitions & Concepts:**
- $\Sigma(A,B)$, $(\Sigma x\in A)B(x)$; $\Sigma$-formation/introduction/elimination/equality
- Existential quantifier $\exists\ \equiv\ (\Sigma x\in A)B(x)$, $\exists$-introduction/elimination in natural deduction form
- Worked example: every element of a $\Sigma$-set is propositionally a pair $\langle a,b\rangle$

**Key Questions:**
1. How does an element of $(\Sigma x\in A)B(x)$ serve simultaneously as a witness and a proof under the existential-quantifier reading?

---

### Chapter 14: The set of small sets (The first universe) (pp. 83–96)

**Summary:** Introduces the universe $U$, a set of codes reflecting the set-forming operations onto the object level, needed to state and prove Peano's fourth axiom and to specify data types, then reworks the enumeration-set primitives so a genuine structural-induction elimination rule ($urec$) can be justified for $U$. : [[The-Universe-of-Small-Sets|Link]]

**Key Definitions & Concepts by Section:**
- **14.1 Formal rules** — $U$, the decoding family $Set(x)$, the eight paired U-introduction/Set-introduction rules (for enumeration sets, $N$, $List$, $Id$, $+$, $\Pi$, $\Sigma$, $W$); worked examples: Peano's fourth axiom, the tautology function `taut`, a non-terminating well-typed term exhibited using $Eq$ and the universe : [[The-Cartesian-Product-of-Two-Sets-and-Conjunction|Link]]
- **14.2 Elimination rule** — replacing arbitrary enumeration sets by $\emptyset$ and $T$ combined via $+$; the primitive set-former $S$; the recursor $urec$; U-elimination and the nine U-equality rules : [[Enumeration-Sets,-Truth-and-Falsity|Link1]], [[Equality-Sets|Link2]], [[Programming-as-Program-Derivation|Link3]], [[Subsets-and-the-Subset-Theory|Link4]]

**Key Questions:**
1. Why is it impossible to state a structural induction principle for the original (unbounded-arity) formulation of $U$, and how does replacing general enumeration sets by $\emptyset$/$T$/$+$ fix this?
2. What does the "expression without normal form" example show about the interaction of extensional equality with non-termination?

---

### Chapter 15: Well-orderings (pp. 97–102)

**Summary:** Introduces the well-order (W-type) set constructor for representing well-founded trees via a constructor set and a selector family, and shows how it can represent binary trees and, with extensional equality, the natural numbers. : [[Well-Orderings-and-General-Trees|Link]]

**Key Definitions & Concepts by Section:**
- $W(A,B)$, $(Wx\in A)B(x)$, canonical elements $sup(a,b)$, selector $wrec$; W-formation/introduction/elimination/equality
- Worked examples: `BinTree` as a well-order, counting nodes via $wrec$, representing $N$ as a well-order
- **15.1 Representing inductively defined sets by well-orderings** — binary trees carrying natural numbers at their nodes

**Key Questions:**
1. Why does representing the natural numbers as a well-order fail under intensional equality, producing "extra" elements that correspond to no natural number?
2. How does choosing $B(a)$ to be the empty set encode a leaf constructor without a separate introduction rule?

---

### Chapter 16: General trees (pp. 103–110)

**Summary:** Generalizes well-orderings to a family of mutually dependent inductive sets, $Tree(A,B,C,d)$, indexed by a name set — needed for mutually recursive definitions like ML datatypes — and shows W-types are the single-index special case. : [[Well-Orderings-and-General-Trees|Link]]

**Key Definitions & Concepts by Section:**
- Name set $A$, constructor family $B$, selector family $C$, component-set-name function $d$; $Tree(A,B,C,d)(a)$, canonical elements $tree(a,b,c)$, selector $treerec$; Tree-formation/introduction/elimination/equality
- **16.2 Relation to the well-order set constructor** — $W$ recovered as $Tree$ over a one-element name set : [[Well-Orderings-and-General-Trees|Link]]
- **16.3 A variant of the tree set constructor** — $Tree'$, $tree'$, $treerec'$, with the index moved from the element to the recursor : [[Well-Orderings-and-General-Trees|Link]]
- **16.4 Examples of different tree sets** — mutually recursive Odd/Even numbers; the infinite family `Array(A,n)` via $Tree'$

**Key Questions:**
1. What extra information does `Tree` carry, compared to `W`, that lets it represent mutually dependent inductive definitions such as Odd/Even?
2. What does the `Array(E,n)` example illustrate about infinite families of inductively defined sets?

---

### Chapter 17: Subsets in the basic set theory (pp. 113–116)

**Summary:** Attempts to add comprehension-formed subsets $\{x\in A\mid B(x)\}$ directly as a primitive set former, and shows this supports only a weak elimination rule from which $(\forall x\in\{z\in A\mid P(z)\})P(x)$ cannot in general be derived, motivating the separate subset theory of the next chapter. : [[Subsets-and-the-Subset-Theory|Link]]

**Key Definitions & Concepts:**
- $\{x\in A\mid B(x)\}$; Subset-formation, Subset-introduction 1/2, Subset-elimination 1
- Stable predicates; the unprovability result (cited from Smith [90]) for $(\forall x\in\{z\in A\mid P(z)\})P(x)$ in the intensional theory

**Key Questions:**
1. Why can't a satisfactory elimination rule be given for subsets when comprehension is added directly to the basic set theory?
2. Why is provability of $(\forall x\in\{z\in A\mid P(z)\})P(x)$ important for modular, lemma-based program derivation?

---

### Chapter 18: The subset theory (pp. 117–134)

**Summary:** Redefines the judgement "$A\ set$" as a pair of a base set and a propositional function, giving propositions a status separate from sets, and re-derives every judgement form and set former's semantics by translation into the basic set theory, yielding the strong comprehension-elimination rule Chapter 17 could not achieve. : [[Subsets-and-the-Subset-Theory|Link]]

**Key Definitions & Concepts by Section:**
- **18.1–18.2** — sets as pairs $(A^0,A^{00})$; judgements without and with assumptions translated into the basic set theory
- **18.3 General rules in the subset theory** — cut rules for propositions, sets, and elements : [[Subsets-and-the-Subset-Theory|Link]]
- **18.4 The propositional constants in the subset theory** — logical connectives and quantifiers defined via $A^0/A^{00}$; propositional equality : [[Subsets-and-the-Subset-Theory|Link]]
- **18.5 Subsets formed by comprehension** — Subset-formation/introduction/elimination for sets and for propositions (the strengthened rule) : [[Subsets-and-the-Subset-Theory|Link]]
- **18.6 The individual set formers in the subset theory** — enumeration sets, equality sets, $N$, $\Pi$, $+$, $\Sigma$, lists, well-orderings, each re-interpreted : [[Subsets-and-the-Subset-Theory|Link]]
- **18.7 Subsets with a universe** — the subset universe $U$ and proposition universe $P$, interpreted via the basic theory's universe : [[Subsets-and-the-Subset-Theory|Link]]

**Key Questions:**
1. How does splitting "$A\ set$" into a base-set/propositional-function pair let the subset theory derive $(\forall x\in\{z\in A\mid P(z)\})P(x)$?
2. Why must lists and well-orderings be given semantics using the universe $U$ in the subset theory, and what alternative (`Listrec`) is proposed to avoid this?

---

### Chapter 19: Types (pp. 137–146)

**Summary:** Introduces the more primitive notion of type — a collection with an equivalence relation, without a fixed inductive structure like $U$ — together with the type $Set$, the family $El$, and function types, enabling fully formal statements of schematic assumptions like "let $A$ be a set."

**Key Definitions & Concepts by Section:**
- **19.1 Types and objects** — $A\ type$, $a:A$, $a=b:A$, $A=B$ : [[The-Theory-of-Types-(Monomorphic-Type-Theory)|Link]]
- **19.2 The types of sets and elements** — $Set\ type$; $El(A)$; abbreviations $A\ set\equiv A:Set$, $a\in A\equiv a:El(A)$ : [[The-Theory-of-Types-(Monomorphic-Type-Theory)|Link]]
- **19.3 Families of types** — contexts $x_1:A_1,\ldots,x_n:A_n$; the extensionality requirement : [[The-Theory-of-Types-(Monomorphic-Type-Theory)|Link]]
- **19.4 General rules** — reflexivity, symmetry, transitivity, type identity; substitution rules : [[General-Proof-Rules|Link]]
- **19.5 Assumptions** — formalizing "let $X$ be a set" as $X:Set\ [X:Set]$ : [[The-Cartesian-Product-of-a-Family-and-the-Universal-Quantifier|Link]]
- **19.6 Function types** — $(x:A)B$; application, abstraction, and the $\beta$/$\xi$/$\alpha$/$\eta$ rules : [[The-Theory-of-Types-(Monomorphic-Type-Theory)|Link]]

**Key Questions:**
1. Why is $U$ inadequate for formalizing an assumption like "let $X$ be an arbitrary set," and how does the type $Set$ solve this?
2. How does the theory of types allow more elegant formulations of the elimination rules for $\Pi$ and well-orderings?

---

### Chapter 20: Defining sets in terms of types (pp. 147–152)

**Summary:** Sketches a monomorphic reformulation of the familiar set formers ($\Pi$, $\Sigma$, $+$, $Id$, finite sets, $N$, $List$) as explicitly-typed, self-describing constants, trading polymorphic economy for judgements that carry all information needed to reconstruct their own derivation.

**Key Definitions & Concepts by Section:**
- Monomorphic vs. polymorphic constants (e.g. a four-argument `apply`); curried, prefix constants
- **20.1–20.7** — typed constants and equalities for $\Pi$/$\lambda$/apply, $\Sigma$/pair/split, $+$/inl/inr/when, $Id$/id/idpeel, finite sets, $N$/0/succ/natrec, $List$/nil/cons/listrec
- The "stripping" function relating monomorphic derivations to polymorphic ones, and Salvesen's result that not every polymorphic derivable judgement arises this way

**Key Questions:**
1. What is gained and what is lost by making every constant carry its set arguments explicitly, as in the monomorphic theory?
2. In what sense is the "stripping" map from monomorphic to polymorphic derivations not a full correspondence?

---

### Chapter 21: Some small examples (pp. 155–165)

**Summary:** Works several complete example derivations — division by 2, evenness testing, case-splitting on Bool, decidability of a predicate — each first as an informal natural-deduction proof and then translated into an explicit type-theoretic program, closing with the family of "strong" elimination rules.

**Key Definitions & Concepts by Section:**
- **21.1 Division by 2** — deriving `half` from induction on $N$ using $\Sigma$ and $+$ rather than a subset, because subset-elimination is too weak to mirror $\exists$-elimination
- **21.2 Even or odd** — deriving `even` via the lemma $(\exists x)(P(x)\vee Q(x))\supset(\exists x)P(x)\vee(\exists x)Q(x)$ : [[Programming-as-Program-Derivation|Link1]], [[Well-Orderings-and-General-Trees|Link2]]
- **21.3 Bool has only the elements true and false** — $(\exists b\in Bool)P(b)\supset(P(true)\vee P(false))$, and analogous inversion principles for $N$, $List$, $+$, $\times$ : [[Specification-of-Abstract-Data-Types|Link1]], [[Enumeration-Sets,-Truth-and-Falsity|Link2]]
- **21.4 Decidable predicates** — $Decidable(A,B)\equiv(\Pi x\in A)B(x)\vee\neg B(x)$; a decision procedure for $x=_N 0$ : [[Programming-as-Program-Derivation|Link]]
- **21.5 Stronger elimination rules** — Strong $\Sigma$/$\Pi$/$+$/Bool-elimination, each adding an equality hypothesis to the ordinary elimination premise, derived via $id$ and $apply$ : [[Programming-as-Program-Derivation|Link]]

**Key Questions:**
1. Why does deriving `half` require using $\Sigma$ rather than a subset, given that a subset is the more natural specification of "the integer part of $n/2$"?
2. What extra premise distinguishes a "strong" elimination rule from the ordinary one, and why is it useful?

---

### Chapter 22: Program derivation (pp. 167–178)

**Summary:** Reformulates the proof rules of type theory as goal-directed tactics obtained by reading each rule bottom-up, and carries out a fully worked top-down derivation of a program solving Dijkstra's Dutch national flag (list-partitioning) problem, with auxiliary lemmas about permutations. : [[Programming-as-Program-Derivation|Link]]

**Key Definitions & Concepts by Section:**
- Goals corresponding to each judgement form; tactics as rules read bottom-up
- **22.1.1 Basic tactics** — tactics for &-introduction, $\times$-introduction, $\times$-elimination, $\Pi$-introduction, List-elimination
- **22.1.2 Derived tactics** — reusing a proved hypothetical judgement as a one-step tactic : [[Programming-as-Program-Derivation|Link]]
- **22.2 A partitioning problem** — full derivation of a Dutch-flag partitioning program: specification `S` via $\Pi$ and a subset `Flag(l)`; induction on the input list; case split on `colour(x)`; Lemmas 1–3 about list permutation and append : [[Natural-Numbers-and-Lists|Link]]

**Key Questions:**
1. Why is top-down, goal-directed derivation better programming methodology than building a proof bottom-up from axioms?
2. In the Dutch flag derivation, why is the specification `Flag(l)` expressed as a subset of `Reds×Whites×Blues` rather than as a plain $\Sigma$-type?

---

### Chapter 23: Specification of abstract data types (pp. 179–184)

**Summary:** Shows how the universe together with $\Sigma$-types lets one specify modules and abstract data types entirely inside type theory, illustrated by a stack, a parameterized stack, and a module for finite sets built on a "computable equality" module. : [[Specification-of-Abstract-Data-Types|Link]]

**Key Definitions & Concepts by Section:**
- Module as a dependent tuple $\langle A_1,\ldots,A_n\rangle$; the fifth reading of "$A\ set$" as "$A$ is a module specification" and "$a\in A$" as "$a$ is an implementation"
- Stack specification via nested $\Sigma$, and, more economically, via a subset for the computationally irrelevant proof component
- **23.1 Parameterized modules** — `STACK` specified via $\Pi A\in U$ : [[Specification-of-Abstract-Data-Types|Link]]
- **23.2 A module for sets with a computable equality** — `CompEq`; `FSET` built by parameterizing over `CompEq` : [[Specification-of-Abstract-Data-Types|Link]]
- Discussion of the missing quotient-set former needed for observational equality of modules

**Key Questions:**
1. Why does using a subset instead of a $\Sigma$-type for the last component of the stack specification remove computationally uninteresting information from an implementation?
2. What extra set-forming operation, absent from this book's theory, would be needed to identify stacks that are merely observationally rather than definitionally equal?
