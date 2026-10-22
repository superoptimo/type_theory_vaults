# A Complete Proof Synthesis Method for the Cube of Type Systems — Guidelines

## Header

**Title:** A Complete Proof Synthesis Method for the Cube of Type Systems
**Author(s):** Gilles Dowek (INRIA)
**Publication:** arXiv:2306.05835v1 [cs.LO], 9 June 2023 (30 pp.). This is a late arXiv posting of an early-1990s INRIA paper; the bibliography runs to 1992 and the work is supervised by Gérard Huet and supported by ESPRIT Basic Research Action "Logical Frameworks".

**Brief Summary:**
The paper gives a complete proof synthesis (term-inhabitation search) procedure for the eight systems of Barendregt's $\lambda$-cube extended with $\eta$-conversion, including the Calculus of Constructions. Because these systems follow the proofs-as-objects paradigm, proofs and terms live in a single syntactic category, so resolution and unification collapse into one process: enumerate $\beta\eta$-normal $\eta$-long terms by guessing a head variable, creating fresh existential variables for the arguments, and recording a typing constraint. The paper proves soundness and completeness, lists pruning heuristics, presents an incomplete but finitely branching "weak splitting" variant, and shows how the method yields a (ground) unification algorithm.

**Intent of the Author:**
Dowek generalizes Huet's constrained resolution for higher-order logic to dependent and polymorphic type systems. He wants to show that the richer term structure of these systems simplifies, rather than complicates, automated proof search, because a single mechanism of term enumeration under type constraints underlies both unification and resolution.

---

## Topic List

1. **Proofs-as-Objects and Proof Synthesis** : [[Proofs-as-Objects-and-Proof-Synthesis|Link]]
   - Proofs as terms through Heyting semantics and the Curry–Howard isomorphism
   - Proof synthesis as finding an inhabitant of a type
   - Heterogeneous proof trees versus a single syntactic category
   - Proof synthesis as a semi-decision procedure : [[Proofs-as-Objects-and-Proof-Synthesis|Link]]
2. **Pure Type Systems and Barendregt's Cube** : [[Pure-Type-Systems-and-Barendregts-Cube|Link]]
   - Sorts, axioms and rules
   - Functional type systems : [[Unification-in-Type-Systems|Link]]
   - The eight systems of the cube : [[Pure-Type-Systems-and-Barendregts-Cube|Link]]
   - Typing judgments and the conversion rule : [[Pure-Type-Systems-and-Barendregts-Cube|Link]]
   - $\beta\eta$-conversion and normalization
   - Normal $\eta$-long forms : [[Pure-Type-Systems-and-Barendregts-Cube|Link]]
   - Atomic terms and head variables
   - Calculus of Constructions with universes and without cumulativity
3. **Contexts, Quantifiers and Constraints** : [[Contexts-Quantifiers-and-Constraints|Link]]
   - Constrained quantified contexts : [[Contexts-Quantifiers-and-Constraints|Link]]
   - Miller's mixed prefixes
   - Equivalence modulo constraints : [[Contexts-Quantifiers-and-Constraints|Link]]
   - Well-typedness without using the constraints : [[Contexts-Quantifiers-and-Constraints|Link]]
   - Rigid and flexible terms : [[Contexts-Quantifiers-and-Constraints|Link]]
   - Success and failure contexts : [[Contexts-Quantifiers-and-Constraints|Link]]
4. **Meta Type System and Existential Variables** : [[Meta-Type-System-and-Existential-Variables|Link]]
   - Embedding a cube system in the Meta type system : [[Meta-Type-System-and-Existential-Variables|Link1]], [[Pure-Type-Systems-and-Barendregts-Cube|Link2]]
   - Variables standing for arbitrary well-typed terms
   - Existential variables as metavariables with dependency on the local context : [[Meta-Type-System-and-Existential-Variables|Link]]
5. **Substitutions Under Quantified Contexts** : [[Substitutions-Under-Quantified-Contexts|Link]]
   - Substitutions carrying an existential context : [[Substitutions-Under-Quantified-Contexts|Link]]
   - Applying and composing substitutions
   - Well-typed substitutions : [[Soundness-and-Completeness|Link]]
   - Preservation of typing under substitution : [[Substitutions-Under-Quantified-Contexts|Link]]
6. **Higher-Order Unification and Resolution** : [[Higher-Order-Unification-and-Resolution|Link]]
   - Huet's enumeration of normal $\eta$-long terms
   - Flexible-rigid and flexible-flexible equations : [[Contexts-Quantifiers-and-Constraints|Link1]], [[Unification-in-Type-Systems|Link2]]
   - Introduction-resolution on hereditary Horn clauses : [[Higher-Order-Unification-and-Resolution|Link1]], [[Weak-Splitting-and-Incomplete-Variants|Link2]]
   - The splitting rule
   - Resolution and unification merged into one process
7. **Elementary Substitutions and the Search Tree** : [[Elementary-Substitutions-and-the-Search-Tree|Link]]
   - Head variable choice and fresh argument variables
   - Typing constraints for well-typedness : [[Contexts-Quantifiers-and-Constraints|Link]]
   - Splitting degree
   - Product and sort substitutions : [[Elementary-Substitutions-and-the-Search-Tree|Link1]], [[Substitutions-Under-Quantified-Contexts|Link2]]
   - Derivations and search trees : [[Elementary-Substitutions-and-the-Search-Tree|Link]]
   - Interleaving an infinitely branching tree
8. **Soundness and Completeness** : [[Soundness-and-Completeness|Link]]
   - Solutions and normal solutions of a context : [[Meta-Type-System-and-Existential-Variables|Link1]], [[Substitutions-Under-Quantified-Contexts|Link2]], [[Higher-Order-Unification-and-Resolution|Link3]]
   - Soundness of derivations : [[Soundness-and-Completeness|Link]]
   - Completeness by induction on the size of a substitution
   - A well-founded order on terms and types
9. **Search Efficiency and Pruning** : [[Search-Efficiency-and-Pruning|Link]]
   - Incremental simplification of rigid-rigid constraints
   - Priority for flexible-rigid constraints : [[Search-Efficiency-and-Pruning|Link1]], [[Contexts-Quantifiers-and-Constraints|Link2]]
   - Delaying instantiation until the type has a rigid head
   - Priority to the rightmost variable : [[Search-Efficiency-and-Pruning|Link]]
   - Decidable unification fragments as heuristics
   - Avoiding splitting in the $\lambda\Pi$-calculus
   - Sort variables and floating universes : [[Meta-Type-System-and-Existential-Variables|Link]]
10. **Weak Splitting and Incomplete Variants** : [[Weak-Splitting-and-Incomplete-Variants|Link]]
    - Algorithm with weak splitting : [[Weak-Splitting-and-Incomplete-Variants|Link1]], [[Search-Efficiency-and-Pruning|Link2]]
    - Relation to introduction-resolution : [[Weak-Splitting-and-Incomplete-Variants|Link]]
    - Completeness of the transitive closure : [[Weak-Splitting-and-Incomplete-Variants|Link]]
11. **Unification in Type Systems** : [[Unification-in-Type-Systems|Link]]
    - Ground unifiability versus open unifiability
    - Empty types and inhabitation : [[Unification-in-Type-Systems|Link]]
    - Undecidability of flexible-flexible unification under a quantified prefix : [[Substitutions-Under-Quantified-Contexts|Link]]

---

## Chapter Summaries

The paper is a single article, not a book. Its numbered sections are treated as chapters; boundaries are the paper's own section headings. Page numbers are the PDF's printed page numbers.

### Chapter 0: Abstract and Introduction (p. 1)

**Summary:** Motivates generalizing Huet's higher-order resolution to the systems of the cube. The claim is that proofs-as-objects simplifies proof search by merging resolution and unification.

**Key Definitions & Concepts:**
- **Proofs-as-objects** — proofs are terms of the type theory, so a proof of $P$ is a term of type $P$.
- **Calculus of Constructions** — $\lambda$-calculus with dependent types, polymorphism and type constructors, an extension of Church higher-order logic.
- **Proof synthesis** — finding a term of a given type.

**Key Questions:**
1. Why would a richer term language make proof synthesis algorithmically simpler, not harder?
2. What are the four contributions announced (complete method, efficiency improvements, incomplete variant, unification algorithm)?

---

### Chapter 1: Outline of the Method (pp. 1–6)

**Summary:** Reviews unification and resolution in first-order and higher-order logic, shows both rest on enumerating normal $\eta$-long terms, and sketches the single-level method for type systems.

**Key Definitions & Concepts by Section:**
- **1.1 Resolution and Unification** — in FOL/HOL proofs are heterogeneous trees mixing proof rules and term rules such as $\to$-elim and $\forall$-elim; resolution searches proof trees and calls unification for term trees. In type systems both are one category. : [[Higher-Order-Unification-and-Resolution|Link]]
- **1.2 Higher Order Unification** — enumeration of normal $\eta$-long terms $t = [x_1:P_1]\dots[x_n:P_n](w\,(h_1\,x_1\dots x_n)\dots(h_p\,x_1\dots x_n))$ with fresh $h_i$ (try all head variables, generate new variables, generate a typing constraint, recurse); flexible-rigid equations instantiate the head, rigid-rigid equations simplify, flexible-flexible are trivially solved. : [[Higher-Order-Unification-and-Resolution|Link]]
- **1.3 Higher Order Resolution** — Horn clauses $Q_1\to\dots\to Q_n\to Q$; resolution rule (unify atomic goal with clause head, emit subgoals $\sigma Q_i$); introduction rule; incompleteness without Huet's splitting rule; hereditary Horn clauses. : [[Higher-Order-Unification-and-Resolution|Link]]
- **1.4 Introduction-Resolution in Type Systems** — propositions as hereditary Horn clauses with $\to$ generalized to dependent product; Introduction: prove $(x:P_1)P$ in $\Gamma$ by proving $P$ in $\Gamma[x:P_1]$ and abstracting; Resolution: for $f:(x_1:Q_1)\dots(x_n:Q_n)Q$ unify $P$ and $Q$ and prove remaining $\sigma Q_i$; worked example with transitivity of $R$; alternative presentation using holes $h_i$ and equations $Q[x_i\leftarrow h_i]=P$. : [[Weak-Splitting-and-Incomplete-Variants|Link1]], [[Unification-in-Type-Systems|Link2]]
- **1.5 A Method to Enumerate the Terms of a Given Type** — elementary substitutions $x\leftarrow[x_1:P_1]\dots[x_n:P_n](w\,(h_1\,\vec x)\dots(h_p\,\vec x))$ or a product form; the well-typedness equation is kept in the context as a constraint, giving a one-level merge of resolution and unification.
- **1.6 Number of Applications** — in polymorphic systems $(w\,c_1\dots c_q)$ may still have a product type, so arbitrarily many extra applications are needed (infinite branching, handled by interleaving).
- **1.7 Variables in the Proposition to be Proved** — instantiate dependent holes (e.g. the witness's proof) before their dependencies, e.g. for $\exists x{:}Nat.(P\,x)$; delay instantiation until the type head is rigid. : [[Contexts-Quantifiers-and-Constraints|Link]]
- **1.8 $\eta$-conversion** — needed to keep the set of elementary substitutions small.

**Key Questions:**
1. What are the four steps common to term enumeration in higher-order unification and in introduction-resolution?
2. Why is plain introduction-resolution incomplete in polymorphic systems, and what replaces the splitting rule here?
3. Why should the body of an existential like $\exists x{:}Nat.(P\,x)$ be solved before the witness?

---

### Chapter 2: Pure Type Systems Extended with $\eta$-conversion (pp. 6–9)

**Summary:** Fixes the object theory: pure type systems with $S=\{Prop, Type\}$, their typing rules, normalization facts and $\eta$-long normal forms, plus the Meta type system needed to state the algorithm. : [[Pure-Type-Systems-and-Barendregts-Cube|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 Definition** — pure type system $(S, Ax, R)$ with $Ax\subseteq S\times S$, $R\subseteq S\times S\times S$ (Def. 1–2); functional type system (axioms and rules are functions); $S=\{Prop,Type\}$, $Ax=\{\langle Prop,Type\rangle\}$, $\langle Prop,Prop,Prop\rangle\in R$ and $s'=s''$ for all rules — the eight cube systems (simply typed $\lambda$-calculus, $\lambda\Pi$, System F, $F\omega$, CC). Syntax $T ::= s \mid x \mid (T\,T) \mid [x:T]T \mid (x:T)T$; $T\to T'$ when $x$ not free in $T'$. Context (Def. 3). Typing rules Empty, Declaration, Sort, Variable, Product, Abstraction, Application, Conversion (Def. 4). Propositions 1–3: types of types, strong normalization and confluence of $\beta\eta$, unique type modulo $\beta\eta$. Atomic term $(u\,c_1\dots c_n)$ with head $u$ (Def. 7); normal well-typed terms are abstractions, products or atomic (Prop. 4); normal types are $(x_1:P_1)\dots(x_n:P_n)P$ with $P$ atomic (Prop. 5); $\eta$-long form and normal $\eta$-long form (Def. 8–9); subterms labeled by contexts (Def. 10). : [[Substitutions-Under-Quantified-Contexts|Link]]
- **2.2 The Meta Type System** — $Meta$ with sorts $\{Prop,Type,Extern\}$, axioms $Prop{:}Type$, $Type{:}Extern$ and extra rules, so that variables ranging over $Prop$ or $Type$ and abstractions over arbitrary terms are well-typed; its normalization is deduced from CC with universes (identify $Extern$ with $Type_1$) and $\beta\eta$ is conjectured. : [[Meta-Type-System-and-Existential-Variables|Link]]

**Key Questions:**
1. Which restrictions on $(S,Ax,R)$ yield exactly the eight systems of the cube, and why does functionality give unique types?
2. Why is a Meta type system unavoidable for expressing "a variable of type $Type$"?

---

### Chapter 3: Constrained Quantified Contexts and Substitution (pp. 9–13)

**Summary:** Extends contexts with $\forall/\exists$ declarations and equational constraints, and defines substitutions that carry their own existential contexts and preserve typing. : [[Contexts-Quantifiers-and-Constraints|Link1]], [[Substitutions-Under-Quantified-Contexts|Link2]]

**Key Definitions & Concepts by Section:**
- **3.1 Constrained Quantified Contexts** — quantified declaration $Qx:T$ and constraint $a=b$ (Def. 12), generalizing Miller's mixed prefixes; $\equiv_\Gamma$ as the smallest congruence containing $\beta\eta$ and the context's constraints (Def. 13); modified Declaration, Variable, Product, Abstraction rules and a Constraint rule, and Conversion using $\equiv_\Gamma$ (Def. 14); well-typed without using the constraints, which implies strong normalization (Def. 15, Prop. 7); normal form of a context (Def. 16, Prop. 8); ground terms (Def. 17); rigid versus flexible terms by head variable universal or existential (Def. 18); success context (only universal variables, trivial constraints) and failure context (a constraint between distinct ground normal terms) (Def. 19); Prop. 9: any non-terminal normal context has an existential variable whose type is $(\vec x{:}\vec P)P$ with $P$ atomic rigid. : [[Contexts-Quantifiers-and-Constraints|Link]]
- **3.2 Substitution** — existential context (Def. 20); substitution as a set of triples $\langle x,\gamma,t\rangle$ (Def. 21–22); application to terms and contexts (Def. 23–24); well-typed substitution: $\sigma\Gamma$ well-formed, no universal variable bound, $(\sigma\Delta)\gamma\vdash t:\sigma T$ (Def. 25); Props. 10–13: substitution preserves $\equiv_\Gamma$ and typing; composition $\tau\circ\sigma$ (Def. 26, Props. 14–16). : [[Elementary-Substitutions-and-the-Search-Tree|Link1]], [[Weak-Splitting-and-Incomplete-Variants|Link2]]

**Key Questions:**
1. Why must a substitution carry an existential context $\gamma$ rather than just a term?
2. How does the quantifier order in a context control which variables a solution for an existential may depend on?
3. Why does Prop. 9 guarantee progress in the search?

---

### Chapter 4: A Complete Method (pp. 13–15)

**Summary:** Defines the elementary substitutions $\Sigma(\Gamma)$, derivations and the search tree, which together constitute the semi-decision procedure. : [[Soundness-and-Completeness|Link]]

**Key Definitions & Concepts:**
- **Search objective** — find a substitution $\sigma$ well-typed in $\Gamma[\exists x{:}T]$ with $\sigma(\Gamma[\exists x{:}T])$ a success context.
- **Elementary substitutions with $r$-splitting (Def. 27)** — for each universal variable $w$ (to the left of $x$, or some $x_i$) of type $(y_1:Q_1)\dots(y_q:Q_q)Q$, build $t=[\vec x{:}\vec P](w\,(h_1\,\vec x)\dots(h_{q+r}\,\vec x))$; new existentials $h_i$ in $\varphi$; for each splitting step $i\le r$, $\chi_i$ introduces $H_i,K_i$, the constraint forcing the type of the partial application to be a product, and the next $h_{q+i}$; final well-typedness constraint $\psi$.
- **Sort and product substitutions** — if $P$ is a sort, also instantiate by $[\vec x{:}\vec P]s$ for $\langle s,P\rangle\in Ax$, or by a product $(y:(h\,\vec x))(k\,\vec x\,y)$ for $\langle s,s',P\rangle\in R$.
- **Derivation (Def. 28)** and **search tree (Def. 29)** — success nodes correspond bijectively to derivations; finite branching is recovered by delaying nodes with $r$-splitting by $r$ generations.

**Key Questions:**
1. What do the variables $H_i,K_i$ encode, and why are they needed only in polymorphic systems?
2. How does the well-typedness constraint $\psi$ play the role of "the unification step" of resolution?

---

### Chapter 5: Examples (pp. 16–17)

**Summary:** Two traced runs: a first-order antisymmetry proof and a proof requiring splitting and a product substitution.

**Key Definitions & Concepts by Section:**
- **5.1 A First Order Example** — goal $(Eq\,a\,b)$ from $Antisym:(x)(y)(R\,x\,y)\to(R\,y\,x)\to(Eq\,x\,y)$, $u:(R\,a\,b)$, $v:(R\,b\,a)$; derivation yields $(Antisym\;a\;b\;u\;v)$ with all other branches immediately hopeless. : [[Elementary-Substitutions-and-the-Search-Tree|Link]]
- **5.2 An Example with Splitting** — $u:(P:Prop)((I\,P)\to P)$, $v:(I\,(A\to B))$, $w:A$, goal $B$; a 1-splitting substitution $p\leftarrow(u\,h_1\,h_2\,h_3)$ plus a product substitution for $h_1$ yields $(u\,(A\to B)\,v\,w)$. : [[Elementary-Substitutions-and-the-Search-Tree|Link]]

**Key Questions:**
1. In 5.2, why does the proof require applying $u$ to three arguments although its type has only two products?
2. Which constraint discovers that $h_1$ must be $A\to B$?

---

### Chapter 6: Properties (pp. 17–23)

**Summary:** Proves well-typedness of elementary substitutions, then soundness and completeness of the method.

**Key Definitions & Concepts by Section:**
- **6.1 Well-typedness** — Props. 17–19: $\Delta\gamma$ is well-formed in Meta, $\Delta\gamma\vdash t:T$, hence each elementary substitution is well-typed in $\Gamma$.
- **6.2 Soundness** — solution (well-typed with $\theta\Gamma$ a success context) and normal solution (Def. 30–32); Lemma 1: a derivation denotes a normal solution; Props. 23–25: solutions typed in Meta are typed in the original system $\mathcal T$ (all products obey $R$, only $Prop$ occurs as a sort); **Theorem 1 (Soundness)**: a derivation of $\Gamma[\exists x{:}P]$ gives a proof $t$ of $P$ in $\Gamma$ in $\mathcal T$. : [[Soundness-and-Completeness|Link]]
- **6.3 Completeness** — well-founded relation $<$ (strict subterm, or type before term) (Def. 33); size of a term and of a substitution (Def. 34–35); failure contexts stay failures (Prop. 26); Lemma 2: every normal solution is denoted by a derivation, by induction on size, decomposing $\theta=\theta'\circ\sigma$ with $|\theta'|<|\theta|$; **Theorem 2 (Completeness)**: if $\Gamma\vdash t:P$ there is a derivation denoting the normal $\eta$-long form of $t$. : [[Soundness-and-Completeness|Link]]

**Key Questions:**
1. Why must well-typedness be shown in Meta before being transferred to $\mathcal T$, and what conditions make the transfer valid?
2. How does the size measure on terms (which includes the sizes of their types) justify the induction in Lemma 2?
3. Why does completeness give the *normal $\eta$-long* proof and not an arbitrary one?

---

### Chapter 7: Efficiency Improvements (pp. 24–25)

**Summary:** Heuristics to prune the search tree and order variable instantiation. : [[Search-Efficiency-and-Pruning|Link]]

**Key Definitions & Concepts by Section:**
- **7.1 Incremental Partial Checking of Constraints** — constraints become triples $\langle\delta,a,b\rangle$; Simplification (Def. 36) decomposes rigid-rigid constraints (abstraction/abstraction, product/product, same-head atomic) and fails otherwise, pruning the branch. : [[Search-Efficiency-and-Pruning|Link]]
- **7.2 Flexible-Rigid Constraints** — solve the flexible head first; candidates are only bound variables and the rigid term's head. : [[Search-Efficiency-and-Pruning|Link1]], [[Contexts-Quantifiers-and-Constraints|Link2]]
- **7.3 Flexible-Flexible Constraints** — solve a head if possible; it may turn the constraint flexible-rigid and unfreezes ill-typed constraints. : [[Search-Efficiency-and-Pruning|Link]]
- **7.4 Avoiding Splitting** — if $Q\dots$ is rigid, all $r\neq0$ substitutions are hopeless; in the $\lambda\Pi$-calculus splitting is never needed. : [[Search-Efficiency-and-Pruning|Link]]
- **7.5 Solving Decidable Unification Problems** — first-order, argument-restricted, second-order matching and related fragments solved by terminating algorithms.
- **7.6 Priority to the Rightmost Variable** — instantiate $y:(P\,x)$ before $x$ to avoid enumerating $x=0,1,2,\dots$. : [[Search-Efficiency-and-Pruning|Link]]
- **7.7 Normalizing some ill-typed terms** — recognizing normalizable ill-typed terms would let constraints be used more. : [[Search-Efficiency-and-Pruning|Link]]

**Key Questions:**
1. Why is rightmost-first instantiation exponentially better in the $(P\,x)$ example?
2. When can splitting be dropped without losing completeness?

---

### Chapter 8: Extension to the Calculus of Constructions With Universes (pp. 25–26)

**Summary:** Sketches the extension to CC with an infinite hierarchy of non-cumulative universes.

**Key Definitions & Concepts:**
- **Calculus of Constructions with universes, without cumulativity (Def. 37)** — sorts $Prop, Type_0, Type_1,\dots$; axioms $Prop:Type_0$, $Type_i:Type_{i+1}$; rules $\langle Prop,Prop,Prop\rangle$, $\langle Type_i,Prop,Prop\rangle$, $\langle Prop,Type_i,Type_i\rangle$, $\langle Type_i,Type_j,Type_{\max\{i,j\}}\rangle$.
- **No Meta system needed** since every term considered is already well-typed; generally a Meta system is required only per target system $\mathcal T$.
- **Sort variables and universe constraints** (floating universes) to tame infinitely many product substitutions.

**Key Questions:**
1. Why does the universe hierarchy create infinitely many product substitutions for a variable of type $Prop$?
2. What replaces enumeration over universe levels?

---

### Chapter 9: An Incomplete but more Efficient Method (pp. 26–27)

**Summary:** Restricts elementary substitutions to 0-splitting (weak splitting), giving a finitely branching search at the cost of completeness.

**Key Definitions & Concepts:**
- **Weak splitting** — only 0-splitting with $0\ldots n$ abstractions; contrast with strong splitting of Chapter 4.
- **Induction loading** — weak splitting finds $(u\,(A\to B)\,v)$ for goal $A\to B$ but not for $B$, since the instantiation is only visible from the goal's type.
- **Relation to introduction-resolution** — strictly stronger (e.g. synthesizes $(u\,(B\to C)\,[x{:}B](v\,x))$); introduction-resolution corresponds to forbidding product substitutions.
- **Transitive closure** — completeness of the closure [9]: every proof splits into synthesizable pieces.

**Key Questions:**
1. What kind of proof (what shape of axiom) defeats weak splitting?
2. In what sense is an incomplete method "complete up to lemmas"?

---

### Chapter 10: Unification (pp. 27–28)

**Summary:** Turns proof synthesis into a (ground) unification procedure and explains why open unification is hard and of little interest. : [[Unification-in-Type-Systems|Link]]

**Key Definitions & Concepts by Section:**
- **10.1 Ground Unification** — unification problem under a context with no constraints; types may be empty, so unifiability differs from ground unifiability; apply the method to $\Gamma[a=b]$ to semi-decide ground unifiability and enumerate all ground unifiers; flexible-flexible equations must be solved and are undecidable under a quantified prefix [26]. : [[Unification-in-Type-Systems|Link]]
- **10.2 Toward Open Unification** — example with $\exists x:(P:Prop)P$ and $a=(x\,(A\to B)\,u)$, $b=(x\,B)$ flexible-flexible with no solution; open unifiability is hard with small interest. : [[Unification-in-Type-Systems|Link]]

**Key Questions:**
1. Why is unifiability equivalent to ground unifiability in simply typed $\lambda$-calculus but not in dependent type systems?
2. Why does the flexible-flexible example have no solution?

---

### Chapter 11: Conclusion (p. 28)

**Summary:** Places the method in the lineage of Herbrand-style enumeration, Robinson resolution and Huet's constrained resolution; the contribution is blind enumeration of proof terms regulated by failure anticipation via type constraints.

**Key Definitions & Concepts:**
- **Naive semi-decision** — enumerate strings until a proof checks; correct but useless.
- **Resolution as pruning** — instantiate $x$ in a premise $\forall x.(P\,x)$ only when $(P\,t)$ matches the goal or another premise's hypothesis.

**Key Questions:**
1. In what sense is the method "blind enumeration with failure anticipation"?
