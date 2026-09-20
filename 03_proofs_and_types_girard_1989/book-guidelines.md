# Proofs and Types — Guidelines

## Header

**Title:** Proofs and Types
**Author(s):** Jean-Yves Girard; translated and with appendices by Paul Taylor and Yves Lafont
**Publication:** Cambridge University Press, Cambridge Tracts in Theoretical Computer Science 7, 1989 (reprinted with minor corrections 1990; reprinted for the Web 2003)

**Brief Summary:**
A compact graduate-level treatment of the Curry-Howard correspondence between proofs and typed programs, built up through natural deduction, the simply typed $\lambda$-calculus, sequent calculus and cut elimination, Gödel's system T, coherence-space denotational semantics, and the polymorphic system F. Its central thesis is that proofs and programs are, at bottom, the same finitary, dynamic objects, and that the deep symmetries of logic (introduction/elimination, cut-elimination) are exactly what make this correspondence more than an accident. The book culminates in the Representation Theorem (system F represents precisely the functions provably total in second-order arithmetic) and two appendices — a rigorous coherence-space semantics for system F and an introduction to linear logic, which Girard discovered while trying to give coherence semantics to the sum type.

**Intent of the Author:**
Girard states in the preface that the book grew out of a short 1986–7 graduate course on typed $\lambda$-calculus at Université Paris VII, and was deliberately not meant to be encyclopedic — the topic selection is admittedly "haphazard." His deeper methodological aim, set out in chapter 1, is to rebalance logic's historical over-investment in static, denotational semantics by taking the finite, dynamic, syntactic side of proofs (their computational content) equally seriously, treating proof theory as a source of genuine algorithmic insight rather than a formal game.

---

## Topic List

1. **Sense and Denotation** : [[Sense-and-Denotation|Link]]
   - Frege's dichotomy between sense and denotation : [[Sense-and-Denotation|Link]]
   - The algebraic Tarskian tradition of truth-functional semantics : [[Sense-and-Denotation|Link]]
   - The syntactic Heyting tradition of proof-based semantics : [[Sense-and-Denotation|Link]]
   - Proofs as the constructive content behind a true sentence

2. **Natural Deduction** : [[Natural-Deduction|Link]]
   - Deductions as trees with hypotheses that are alive or discharged : [[Natural-Deduction|Link]]
   - Introduction and elimination rules : [[Natural-Deduction|Link]]
   - Identification of deductions by proof reduction : [[Natural-Deduction|Link]]
   - The subformula property of normal deductions : [[Parcels-and-Subformulas|Link1]], [[Natural-Deduction|Link2]]
   - Commuting conversions for disjunction and existence : [[Natural-Deduction|Link]]
   - The parasitic context problem in the elimination rules for bottom, or, and exists : [[Natural-Deduction|Link]]

3. **The Curry-Howard Isomorphism** : [[The-Curry-Howard-Isomorphism|Link]]
   - Types as formulas and terms as proofs : [[The-Curry-Howard-Isomorphism|Link]]
   - The simply typed $\lambda$-calculus : [[Coherence-Space-Semantics|Link1]], [[Gödel's-System-T|Link2]], [[System-F-and-Polymorphism|Link3]]
   - Denotational versus operational significance of a type : [[The-Curry-Howard-Isomorphism|Link]]
   - A type as a plugging instruction for modules : [[The-Curry-Howard-Isomorphism|Link]]
   - Redexes, contracta, and normal forms : [[The-Curry-Howard-Isomorphism|Link]]
   - Extension of the isomorphism to second-order quantification : [[The-Curry-Howard-Isomorphism|Link]]

4. **Normalisation Theorems** : [[Normalisation-Theorems|Link]]
   - The Church-Rosser confluence property
   - Weak normalisation and decidability of term equality : [[Normalisation-Theorems|Link]]
   - Strong normalisation and Tait's reducibility method : [[Normalisation-Theorems|Link]]
   - Reducibility candidates and the CR conditions : [[Normalisation-Theorems|Link]]
   - König's lemma and bounds on reduction length
   - Strong normalisation for system F and its link to Gödel's second incompleteness theorem : [[Normalisation-Theorems|Link]]

5. **Sequent Calculus and Cut Elimination** : [[Sequent-Calculus-and-Cut-Elimination|Link]]
   - Sequents and the structural rules of exchange, weakening, and contraction : [[Sequent-Calculus-and-Cut-Elimination|Link]]
   - The intuitionistic restriction on sequents : [[Sequent-Calculus-and-Cut-Elimination|Link]]
   - The identity axiom and the cut rule as dual expressions of identity
   - The subformula property of cut-free proofs : [[Sequent-Calculus-and-Cut-Elimination|Link]]
   - Translation between sequent calculus and natural deduction : [[Sequent-Calculus-and-Cut-Elimination|Link]]
   - Gentzen's Hauptsatz and the hyperexponential cost of cut elimination
   - Resolution and Horn clauses : [[Sequent-Calculus-and-Cut-Elimination|Link]]

6. **Gödel's System T** : [[Gödel's-System-T|Link]]
   - Integers and booleans as primitive types
   - The recursor and the weaker iterator : [[Gödel's-System-T|Link]]
   - The predecessor problem : [[Gödel's-System-T|Link1]], [[System-F-and-Polymorphism|Link2]]
   - Provably total functions in Peano Arithmetic : [[Gödel's-System-T|Link1]], [[System-F-and-Polymorphism|Link2]]

7. **System F and Polymorphism** : [[System-F-and-Polymorphism|Link]]
   - Universal type quantification : [[Semantics-of-System-F|Link]]
   - Uniformity of polymorphic terms
   - Representation of products, sums, and existential types : [[Semantics-of-System-F|Link]]
   - Free structures and the general scheme for inductive types : [[System-F-and-Polymorphism|Link]]
   - Church encodings of integers, lists, and trees : [[System-F-and-Polymorphism|Link]]
   - The Representation Theorem and provable totality in second-order arithmetic : [[Gödel's-System-T|Link]]
   - Turing-style diagonalisation against a universal normalisation function : [[System-F-and-Polymorphism|Link]]

8. **Coherence Space Semantics** : [[Coherence-Space-Semantics|Link]]
   - Coherence spaces, webs, tokens, and the coherence relation : [[Coherence-Space-Semantics|Link]]
   - Stable functions and the pullback preservation condition : [[Coherence-Space-Semantics|Link]]
   - The Parallel Or example and sequentiality : [[Coherence-Space-Semantics|Link]]
   - The trace representation of the function space : [[Coherence-Space-Semantics|Link]]
   - The Berry order versus the pointwise order : [[Coherence-Space-Semantics|Link]]
   - Lazy natural numbers and the interpretation of recursion
   - The fixed-point object and general recursion in the model : [[Coherence-Space-Semantics|Link]]

9. **Semantics of System F** : [[Semantics-of-System-F|Link]]
   - The size problem in interpreting universal quantification : [[Semantics-of-System-F|Link]]
   - Rigid embeddings and finite approximation of domains : [[Semantics-of-System-F|Link]]
   - Uniformity of polymorphic denotations under automorphisms : [[Semantics-of-System-F|Link]]
   - Tokens and universal abstraction as a generalized trace : [[Semantics-of-System-F|Link]]
   - Non-syntactic points in the denotation of booleans and integers
   - Totality candidates and total domains

10. **Linear Logic** : [[Linear-Logic|Link]]
    - The algorithmic inconsistency of classical cut elimination : [[Linear-Logic|Link1]], [[Sequent-Calculus-and-Cut-Elimination|Link2]]
    - Removing weakening and contraction from sequent calculus : [[Linear-Logic|Link]]
    - Tensor and with as the two linear conjunctions : [[Semantics-of-System-F|Link1]], [[Linear-Logic|Link2]]
    - Linear implication and linear negation : [[Linear-Logic|Link]]
    - The exponential modalities of course and why not
    - Proof nets as a graphical, order-independent proof representation
    - Local and parallel cut elimination in proof nets : [[Linear-Logic|Link]]
    - Linear decomposition of the intuitionistic sum type

---

## Chapter Summaries

### Chapter 1: Sense, Denotation and Semantics (pp. 1–7)

**Summary:** Introduces Frege's sense/denotation dichotomy and the two rival traditions of semantics — Tarskian (denotational, model-theoretic) and Heyting (proof-based, constructive) — framing the book's project of treating proofs as computational, finitary objects rather than mere truth-values. : [[Sense-and-Denotation|Link]]

**Key Definitions & Concepts by Section:**
- **1.1 Sense and denotation in logic** — sense (the syntactic instructions determining meaning) versus denotation (the ideal result); Frege's dichotomy; the associations sense/syntax/proofs versus denotation/truth/semantics. : [[Sense-and-Denotation|Link]]
  - **1.1.1 The algebraic tradition** — the denotation-only approach (Boole, Löwenheim's theorem of 1916), giving rise to Model Theory. : [[Sense-and-Denotation|Link]]
  - **1.1.2 The syntactic tradition** — sense-focused; formalism described as "soft camembert" (no true structure); Gentzen's theorem (1934) on cut elimination as evidence of syntactic symmetries; Herbrand's theorem (1930). : [[Sense-and-Denotation|Link]]
- **1.2 The two semantic traditions** : [[Sense-and-Denotation|Link]]
  - **1.2.1 Tarski** — denotational truth-table semantics for the connectives and quantifiers $\land,\lor,\Rightarrow,\neg,\forall,\exists$.
  - **1.2.2 Heyting** — proof-based (BHK-style) semantics: a proof of $A\land B$ is a pair of proofs, a proof of $A\lor B$ is a tagged proof, a proof of $A\Rightarrow B$ is a function from proofs to proofs, a proof of $\forall\xi.A$ is a function, a proof of $\exists\xi.A$ is a witness-proof pair, and $\neg A$ is defined as $A\Rightarrow\bot$; connects to Brouwer's intuitionistic logic; excluded middle $A\lor\neg A$ is not provable in general.

**Key Questions:**
1. What is the difference between the sense and the denotation of a sentence, and why does Girard say denotation has been "much more developed" than sense?
2. How does Heyting's proof-semantics for $A\Rightarrow B$ differ fundamentally from the Tarskian truth-table semantics for $A\Rightarrow B$?
3. Why can't $A\lor\neg A$ be proved in Heyting semantics, and what logic does this correspond to?

---

### Chapter 2: Natural Deduction (pp. 8–13)

**Summary:** Presents Prawitz's natural deduction system for the $(\land,\Rightarrow,\forall)$ intuitionistic fragment, showing deductions as trees whose hypotheses are either "alive" or "discharged," then reinterprets the rules computationally via Heyting semantics, deriving the correspondence between deduction and $\lambda$-term construction that anticipates Curry-Howard. : [[Natural-Deduction|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 The calculus** — deduction as a finite tree; hypothesis (alive leaf) versus discharged (dead) hypothesis; introduction rules ($\land I$, $\Rightarrow I$, $\forall I$) and elimination rules ($\land_1E$/$\land_2E$, $\Rightarrow E$, called modus ponens, and $\forall E$); the introduction/elimination symmetry as the system's fundamental symmetry.
- **2.2 Computational significance** — a formula $A$ read as the set of its deductions ($\delta\in A$); parcels of hypotheses (occurrences of the same formula sharing a variable); the deduction-to-term interpretation: hypothesis maps to variable, $\land I$ to a pair, $\land E$ to a projection ($\pi_1$, $\pi_2$), $\Rightarrow I$ to $\lambda$-abstraction (binding corresponds to discharge), $\Rightarrow E$ to application. : [[The-Curry-Howard-Isomorphism|Link]]
  - **2.2.1 Interpretation of the rules** — the equations $\pi_1\langle u,v\rangle=u$, $\pi_2\langle u,v\rangle=v$, $\langle\pi_1t,\pi_2t\rangle=t$, $(\lambda x.v)u=v[u/x]$, $\lambda x.tx=t$. : [[Parcels-and-Subformulas|Link]]
  - **2.2.2 Identification of deductions** — deduction equalities (proof reduction) mirror these term equations; substituting a whole discharged parcel by copies of the argument deduction. : [[Natural-Deduction|Link]]

**Key Questions:**
1. What does it mean for a hypothesis to be "alive" versus "discharged," and how does the $\Rightarrow I$ rule illustrate that natural deduction is only "vaguely" tree-like?
2. How does reading a deduction as a $\lambda$-term make the equation $(\lambda x.v)u = v[u/x]$ correspond to a proof-identification (reduction) step rather than just a computation rule?
3. Why does Girard defer disjunction and existence to chapter 10 despite calling them "the two most typically intuitionistic connectors"?

---

### Chapter 3: The Curry-Howard Isomorphism (pp. 14–21)

**Summary:** Formalizes the simply typed $\lambda$-calculus — types are formulas of the $(\land,\Rightarrow)$ fragment, terms are proofs — and establishes the precise bijection between natural-deduction proofs and typed terms, arguing this is a genuine isomorphism because the normalisation and conversion structure matches independently on both sides. : [[The-Curry-Howard-Isomorphism|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 Lambda Calculus** — types (atomic types, product $U\times V$, arrow $U\to V$) corresponding to $(\land,\Rightarrow)$ formulas; terms (variables, pairs $\langle u,v\rangle$, projections $\pi_1t$/$\pi_2t$, abstraction $\lambda x.v$, application $tu$) corresponding to proofs. : [[Natural-Deduction|Link]]
- **3.2 Denotational significance** — types as specifications of functions and pairs; primary equations ($\beta$-reduction and projection laws) versus secondary equations ($\eta$ and surjective pairing); a consistency and decidability theorem for the term equality system. : [[The-Curry-Howard-Isomorphism|Link]]
- **3.3 Operational significance** — types as "plugging instructions" for modules; terms as programs; the still-embryonic state of true operational semantics; motivates studying normalisation. : [[The-Curry-Howard-Isomorphism|Link]]
- **3.4 Conversion** — normal term (no redex subterm); redex and contractum; reduction as the reflexive-transitive closure of conversion; the head normal form lemma; a corollary that closed terms are abstractions.
- **3.5 Description of the isomorphism** — the explicit bijection: a hypothesis in parcel $i$ maps to the variable $x_i^A$, $\land I$ maps to pairing, $\land E$ to projection, $\Rightarrow I$ to abstraction (discharge equals binding), $\Rightarrow E$ to application. : [[The-Curry-Howard-Isomorphism|Link]]
- **3.6 Relevance of the isomorphism** — a normal proof (no introduction/elimination redex sequence) matches a normal term independently; a genuine isomorphism, not a mere bijection, since the conversion, normality, and reduction structures coincide; methodological consequences: constructive logic must have an operational side, and type-system "improvements" divorced from logical symmetries tend to fail. : [[The-Curry-Howard-Isomorphism|Link]]

**Key Questions:**
1. Why does Girard insist the Curry-Howard correspondence is a true isomorphism rather than "just" a bijection between proofs and terms?
2. What is the difference between the "primary" equations (beta-reduction, projections) and the "secondary" equations (eta, surjective pairing), and why does the book say the latter "have never been given adequate status"?
3. In what sense is a type a "plugging instruction," and how does this operational reading differ from treating a type merely as a specification?

---

### Chapter 4: The Normalisation Theorem (pp. 22–27)

**Summary:** Establishes that the typed $\lambda$-calculus behaves computationally well by proving Church-Rosser (uniqueness of normal form, stated without proof) and the weak normalisation theorem (existence, via a degree-based termination argument), then previews strong normalisation (all reduction strategies terminate) as the subject of chapter 6. : [[Normalisation-Theorems|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 The Church-Rosser property** — the confluence theorem ($t\rightsquigarrow u,v$ implies there is $w$ with $u,v\rightsquigarrow w$); uniqueness of normal forms as a corollary; consistency of the calculus (not every equation is derivable) as a further corollary. : [[Linear-Logic|Link1]], [[Normalisation-Theorems|Link2]]
- **4.2 The weak normalisation theorem** — existence of a normal form, necessarily unique; decidability of denotational equality by computing and comparing normal forms; distinguishes weak (some strategy terminates) from strong normalisation. : [[Normalisation-Theorems|Link]]
- **4.3 Proof of the weak normalisation theorem** — the degree $\partial(T)$ of a type, the degree of a redex, and the degree $d(t)$ of a term; the proof proceeds by double induction on $\mu(t)=(n,m)$ (maximum redex degree, count of redexes at that degree), using lemmas on substitution, conversion, and conversion of maximal-degree redexes. : [[Normalisation-Theorems|Link]]
- **4.4 The strong normalisation theorem** — a strongly normalisable term (no infinite reduction sequence); a lemma via König's lemma relating strong normalisability to a uniform bound $\nu(t)$ on reduction length; previews two proof methods, internalisation (Gandy) and reducibility (the method used in chapter 6). : [[Normalisation-Theorems|Link]]

**Key Questions:**
1. Why is Church-Rosser (confluence) a separate result from normalisation, and what does each one individually guarantee about the calculus?
2. How does the degree-based measure $\mu(t)=(n,m)$ ensure termination of the specific reduction strategy chosen in the weak normalisation proof?
3. What is the difference between weak and strong normalisation, and why does König's lemma bridge "no infinite reduction sequence" to "a uniform bound on reduction length"?

---

### Chapter 5: Sequent Calculus (pp. 28–40)

**Summary:** Introduces Gentzen's sequent calculus as the fullest syntactic embodiment of logic's left/right symmetry, subsuming both intuitionistic and classical logic, analyzes its structural, identity, and logical rules, and shows a precise but non-invertible translation from sequent proofs to natural-deduction terms, culminating in the "normal equals cut-free" slogan that anticipates the Hauptsatz. : [[Linear-Logic|Link1]], [[Sequent-Calculus-and-Cut-Elimination|Link2]]

**Key Definitions & Concepts by Section:**
- **5.1 The calculus** — a sequent $A\vdash B$ (finite sequences of formulae); the naïve denotational reading, that the conjunction of the $A_i$ implies the disjunction of the $B_j$.
  - **5.1.1 Sequents.**
  - **5.1.2 Structural rules** — exchange, weakening, and contraction on both sides; called the most important rules despite appearing trivial; restricting them motivates linear logic. : [[Sequent-Calculus-and-Cut-Elimination|Link]]
  - **5.1.3 The intuitionistic case** — an intuitionistic sequent has at most one formula on the right; this loses left/right symmetry, regained by forbidding contraction and weakening altogether.
  - **5.1.4 The "identity" group** — the identity axiom $C\vdash C$; the cut rule as its dual; cut elimination, deferred to chapter 13, as the syntactic counterpart of normalisation. : [[Sequent-Calculus-and-Cut-Elimination|Link]]
  - **5.1.5 Logical rules** — left/right rule pairs for negation, conjunction, disjunction, implication, and the quantifiers; any invented connective must respect left/right symmetry (cut-eliminability) or be a "logical atrocity." : [[Sequent-Calculus-and-Cut-Elimination|Link]]
- **5.2 Some properties of the system without cut**
  - **5.2.1 The last rule** — the Disjunction Property and the Existence Property as consequences of cut-free intuitionistic proofs.
  - **5.2.2 Subformula property** — cut-free proofs use only subformulae of the end-sequent; cut is the only rule violating this. : [[Natural-Deduction|Link1]], [[Parcels-and-Subformulas|Link2]], [[Sequent-Calculus-and-Cut-Elimination|Link3]]
  - **5.2.3 Asymmetrical interpretation** — the signature of an occurrence; splitting a formula into left and right readings once cut is removed, anticipating linear logic's finer semantics.
- **5.3 Sequent Calculus and Natural Deduction** — translation of cut-free and cut proofs into natural-deduction terms; parcels correspond to left-rule contraction and weakening; right rules map to introductions and left rules to eliminations; exchange corresponds to nothing; cut corresponds to growth at the root, not a natural-deduction rule. : [[Sequent-Calculus-and-Cut-Elimination|Link1]], [[Natural-Deduction|Link2]]
- **5.4 Properties of the translation** — the translation from sequent calculus to deduction is many-to-one, not invertible; the "normal equals cut-free" moral equivalence, though some proofs with cut also translate to normal deductions.

**Key Questions:**
1. Why are the structural rules — exchange, weakening, and contraction, which "seem not to say anything at all" — actually the most important rules of the sequent calculus?
2. How does the subformula property of cut-free proofs relate to automated deduction, and why doesn't it alone make predicate logic decidable?
3. In what precise sense is the translation from sequent calculus to natural deduction many-to-one, and why does this make the cut rule correspond to nothing in natural deduction except growth at the root?

---

### Chapter 6: Strong Normalisation Theorem (pp. 41–45)

**Summary:** Proves strong normalisation for the simply typed $\lambda$-calculus via Tait's reducibility method, a technique deliberately introduced here rather than a simpler proof-theoretic argument because it generalises to system F in chapter 14; establishes the CR1-4 properties that characterize reducibility candidates. : [[Normalisation-Theorems|Link]]

**Key Definitions & Concepts by Section:**
- **6.1 Reducibility** — $\mathrm{RED}_T$ defined by induction on type: an atomic type is reducible iff strongly normalisable, a product type is reducible iff both projections are reducible, an arrow type is reducible iff application to every reducible argument is reducible; notes the essential logical complexity (negation plus universal quantifier) keeping this outside arithmetic, relevant to strong normalisation implying PA-consistency via Gödel's system T.
- **6.2 Properties of reducibility** — a neutral term is not a pair or abstraction; the conditions CR1 (reducible implies strongly normalisable), CR2 (reducibility closed under reduction), CR3 (a neutral term is reducible if all its one-step converts are), and CR4 (neutral and normal implies reducible).
  - **6.2.1 Atomic types** — verifies CR1-3.
  - **6.2.2 Product type** — verifies CR1-3 via projections.
  - **6.2.3 Arrow type** — verifies CR1-3 via application to a fresh variable and to reducible arguments.
- **6.3 Reducibility theorem** : [[Normalisation-Theorems|Link]]
  - **6.3.1 Pairing** — lemma: if $u,v$ are reducible, so is $\langle u,v\rangle$.
  - **6.3.2 Abstraction** — lemma: if $v[u/x]$ is reducible for every reducible $u$, then $\lambda x.v$ is reducible. : [[Natural-Deduction|Link]]
  - **6.3.3 The theorem** — all terms are reducible, proved via a substitution proposition by induction on term structure, giving strong normalisation as a corollary. : [[Parcels-and-Subformulas|Link]]

**Key Questions:**
1. Why can't the reducibility argument be directly formalised in arithmetic, and how does this connect strong normalisation of Gödel's system T to the consistency of Peano Arithmetic?
2. What role does the notion of "neutral" term play in properties CR3 and CR4, and why is it needed to get the induction on arrow types to close?
3. Why does Girard choose the reducibility method here instead of a simpler proof-theoretic strong normalisation argument, given that a simpler method exists for the simply typed case?

---

### Chapter 7: Gödel's System T (pp. 46–52)

**Summary:** Extends the simply typed calculus with constants Int and Bool plus recursion and case operators to gain real expressive power, including Ackermann-style growth, while flagging this as a conceptual "step backwards" — an ad hoc extension not corresponding to a logical scheme — that system F will later resolve more elegantly. : [[Gödel's-System-T|Link]]

**Key Definitions & Concepts by Section:**
- **7.1 The calculus** — the types Int and Bool; Int-introduction ($O$, $St$), Int-elimination (the recursor $R\,u\,v\,t$), Bool-introduction ($T$, $F$), Bool-elimination (definition by cases $D\,u\,v\,t$); intended meanings, including primitive recursion $Ruv0=u$, $Ruv(n+1)=v(Ruvn)n$; new conversion rules for $R$ and $D$.
- **7.2 Normalisation theorem** — extends Church-Rosser and reducibility (with extended neutrality) to T; the recursor case is the first genuine use of induction on the reducibility predicate itself. : [[Normalisation-Theorems|Link]]
- **7.3 Expressive power: examples** : [[Gödel's-System-T|Link]]
  - **7.3.1 Booleans** — definable connectives negation, disjunction, and conjunction via $D$; the open question of a symmetric disjunction, resolved negatively in section 9.3.1.
  - **7.3.2 Integers** — numerals $S^nO$; addition, multiplication, and predicate definitions via $R$; the iterator as a weaker special case of $R$; the predecessor requires the full recursor, not just iteration; super-primitive-recursive growth via recursion on higher types.
- **7.4 Expressive power: results** : [[Gödel's-System-T|Link]]
  - **7.4.1 Canonical forms** — closed normal terms of type Int, Bool, product, or arrow have the expected canonical shape, justifying that Int and Bool really do represent integers and booleans. : [[Gödel's-System-T|Link]]
  - **7.4.2 Representable functions** — a closed term of type $\mathrm{Int}\to\mathrm{Int}$ induces a total recursive function via normalisation; T represents exactly the functions provably total in Peano Arithmetic. : [[Gödel's-System-T|Link1]], [[System-F-and-Polymorphism|Link2]]

**Key Questions:**
1. Why does Girard call systems like T a "step backwards from the logical viewpoint" even though they gain real expressive power over the simply typed calculus?
2. Why can the predecessor function be defined using the full recursor but not using the weaker iterator, and what does this reveal about the cost of computing the predecessor?
3. What is the precise sense in which system T represents exactly the functions provably total in Peano Arithmetic, and why does this make T's expressive power "enormous" relative to what is computationally feasible?

---

### Chapter 8: Coherence Spaces (pp. 53–65)

**Summary:** Develops coherence-space semantics — a denotational model based on stability, not mere Scott continuity — as an alternative to Scott domains, motivated by giving "function" a mathematically precise but computationally faithful meaning; builds up types as coherence spaces, stable functions, the trace representation of the function space, and the Berry order, ending with the Parallel Or example showing stability rules out non-sequential functions. : [[Coherence-Space-Semantics|Link1]], [[Linear-Logic|Link2]]

**Key Definitions & Concepts by Section:**
- **8.1 General ideas** — denotational semantics interprets reduction by equality; surveys candidate notions of type, including sets (too coarse), Kreisel's hereditarily effective operations (too syntactic), and Scott's topological spaces (function-space topology problems), motivating coherence spaces.
- **8.2 Coherence Spaces** — a coherence space is a down-closed, binary-complete set of sets; examples Bool and Int; better viewed as reflexive-symmetric graphs. : [[Coherence-Space-Semantics|Link1]], [[Linear-Logic|Link2]]
  - **8.2.1 The web of a coherence space** — the web, tokens, and the coherence relation; a bijection between coherence spaces and graphs; points as cliques; flat domains. : [[Coherence-Space-Semantics|Link1]], [[Linear-Logic|Link2]]
  - **8.2.2 Interpretation** — points interpret terms; finite approximants form a directed set; total versus partial objects; totality is not simply maximality for complex types. : [[Parcels-and-Subformulas|Link1]], [[Sense-and-Denotation|Link2]]
- **8.3 Stable functions** — the stability conditions: monotonicity, continuity, and the pullback condition for coherent unions; stability as a functor preserving filtered colimits and pullbacks, with no topological analogue for the pullback condition. : [[Coherence-Space-Semantics|Link]]
  - **8.3.1 Stable functions on a flat space** — classification into constants "by vocation" and partial-function liftings. : [[Coherence-Space-Semantics|Link]]
  - **8.3.2 Parallel Or** — the classic example: only sequential disjunctions are stable, and Parallel Or is excluded by stability, illustrating the principle of least data.
- **8.4 Direct product of two coherence spaces** — binary stability; the product, later called "with," corresponding to binary stable functions. : [[Coherence-Space-Semantics|Link]]
- **8.5 The Function-Space** — represents $A\to B$ as a coherence space via traces. : [[Coherence-Space-Semantics|Link]]
  - **8.5.1 The trace of a stable function** — every value has a unique least finite witness; the trace and the application formula recovering $F$ from its trace. : [[Coherence-Space-Semantics|Link]]
  - **8.5.2 Representation of the function space** — the traces of stable functions are exactly the points of a coherence space. : [[Coherence-Space-Semantics|Link]]
  - **8.5.3 The Berry order** — an order on stable functions via trace inclusion, contrasting with the pointwise order. : [[Coherence-Space-Semantics|Link]]
  - **8.5.4 Partial functions** — computes $\mathrm{Int}\to\mathrm{Int}$ as partial functions plus constants by vocation; contrasts with Scott's pointwise order at a simple type, modeling a test program that distinguishes reading its input from ignoring it. : [[Coherence-Space-Semantics|Link]]

**Key Questions:**
1. Why does Scott's topological approach to domains run into trouble defining function spaces, and what extra condition, stability, does Girard add to fix this?
2. What exactly does the Parallel Or example show about the limits of stable-function semantics, and why is this considered a feature, sequentiality, rather than a bug?
3. Why is the Berry order finer than the pointwise Scott order, and what does the identity-versus-constant example reveal about the difference between the two orders operationally?

---

### Chapter 9: Denotational Semantics of T (pp. 66–71)

**Summary:** Interprets the simply typed calculus and Gödel's T inside coherence spaces, verifies that conversion becomes denotational equality, identifies the model with a Cartesian closed category of coherence spaces and stable maps, then confronts a real obstruction — Int must be enriched to a "lazy naturals" space to correctly interpret recursion — and closes with the fixed-point and infinity object. : [[Coherence-Space-Semantics|Link]]

**Key Definitions & Concepts by Section:**
- **9.1 Simple typed calculus** — $\lambda$-abstraction and application as mutually inverse trace and application operations. : [[Gödel's-System-T|Link1]], [[Coherence-Space-Semantics|Link2]], [[System-F-and-Polymorphism|Link3]]
  - **9.1.1 Types** — products interpreted via "with," arrows via the function-space construction. : [[Gödel's-System-T|Link]]
  - **9.1.2 Terms** — compositional interpretation of variables, pairing, projections, abstraction, and application, all shown stable. : [[Gödel's-System-T|Link]]
- **9.2 Properties of the interpretation** — soundness, that reduction implies denotational equality, via a substitution lemma; the secondary equations also hold semantically; coherence spaces and stable maps form a Cartesian closed category.
- **9.3 Gödel's system** : [[Gödel's-System-T|Link]]
  - **9.3.1 Booleans** — interprets $T$ and $F$; a ternary stable function for $D$; proves Parallel Or is not T-definable, since it would denote a non-stable function.
  - **9.3.2 Integers** — the naive interpretation of Int fails for recursion; the fix is a "lazy naturals" space with extra tokens meaning "greater than $p$"; reinterprets $O$, $S$, and constructs the recursor via monotone extension to infinite points.
  - **9.3.3 Infinity and fixed point** — the infinite point as a fixed point of successor; connects to a nonconvergent rule and to the fixed-point combinator via a recursive definition of its trace in terms of finite trees. : [[Coherence-Space-Semantics|Link]]

**Key Questions:**
1. Why does the naive interpretation of Int as the flat coherence space fail to correctly model recursion, and what does the lazy-naturals fix actually add semantically?
2. How does the fact that Parallel Or is not stable give a semantic, rather than syntactic, proof that it cannot be defined in Gödel's system T?
3. In what sense does the coherence-space model make the fixed-point combinator and general recursion available even though they have no place in the typed syntax of T?

---

### Chapter 10: Sums in Natural Deduction (pp. 72–80)

**Summary:** Completes natural deduction with absurdity, disjunction, and existence, and shows why this fragment is "not so pretty": elimination rules carry a parasitic context formula, forcing extra commuting conversions beyond the standard introduction/elimination redexes, and complicating but not breaking the subformula property and normalisation; closes by giving the associated $\lambda$-calculus (an empty type and a sum type with pattern-matching) for Curry-Howard on this fragment. : [[Natural-Deduction|Link]]

**Key Definitions & Concepts by Section:**
- The introduction rules are presented, with no introduction rule for absurdity; the elimination rules are criticized for a "parasitic" context formula unrelated to the eliminated formula.
- **10.1 Defects of the system** — elimination rules force identifying different-looking deductions, requiring commuting conversions; "true deductions are equivalence classes modulo commutation"; natural deduction's tree form cannot directly express connectives that conceptually have two conclusions reunited later. : [[Gödel's-System-T|Link1]], [[Semantics-of-System-F|Link2]]
- **10.2 Standard conversions** — the standard redexes for disjunction and existential introduction meeting their eliminations; only "principal premise" introduction/elimination pairs count as redexes.
- **10.3 The need for extra conversions**
  - **10.3.1 Subformula Property** — the theorem and the notion of principal branch, proved cleanly for the conjunction/implication/universal fragment. : [[Natural-Deduction|Link1]], [[Parcels-and-Subformulas|Link2]], [[Sequent-Calculus-and-Cut-Elimination|Link3]]
  - **10.3.2 Extension to the full fragment** — breaks down because an elimination's conclusion need not be a subformula of its principal premise; distinguishes "good" from "bad" eliminations; a counterexample shows the naive subformula property fails without commuting conversions. : [[Natural-Deduction|Link]]
- **10.4 Commuting conversions** — explicit commutation rules moving an outer elimination inward past a bad elimination. : [[Natural-Deduction|Link]]
- **10.5 Properties of conversion** — Church-Rosser still holds; extension to the full calculus works but is "boring," and strong normalisation still holds; Girard's editorial view that this fragment is not sacrosanct and may deserve different treatment, foreshadowing linear logic's single symmetric rules.
- **10.6 The associated functional calculus** — Curry-Howard terms for this fragment. : [[Natural-Deduction|Link]]
  - **10.6.1 Empty type** — the empty type and its canonical elimination map, with five commutation equations.
  - **10.6.2 Sum type** — the sum type, its injections, and a case term matching pattern matching in a functional language, with standard and commuting conversions matching the natural-deduction rules exactly.
  - **10.6.3 Additional conversions** — eta-like laws, noting the "natural" reduction direction is actually the reverse of the denotational equality.

**Key Questions:**
1. Why does Girard call the elimination rules for disjunction, existence, and absurdity "catastrophic," and what specifically does the parasitic context formula break?
2. What is a commuting conversion, and why is it necessary in addition to the standard introduction/elimination redexes to recover a working subformula property?
3. How does the case term for the sum type correspond to pattern matching in a language like ML, and how do its conversion rules mirror the natural-deduction commuting conversions?

---

### Chapter 11: System F (pp. 81–93)

**Summary:** Introduces system F, the polymorphic $\lambda$-calculus discovered independently by Girard in proof theory and Reynolds in computer science, extending simple types with universal type quantification, and shows its signature payoff — booleans, products, sums, and full inductive data types are all definable from the bare implication and universal-quantification fragment via a uniform "free structure" encoding, with no primitive data types needed. : [[Normalisation-Theorems|Link1]], [[Semantics-of-System-F|Link2]], [[System-F-and-Polymorphism|Link3]]

**Key Definitions & Concepts by Section:**
- **11.1 The calculus** — types built from type variables via arrow and universal quantification; terms: variables, application, $\lambda$-abstraction, universal abstraction (with a freeness restriction), and universal application; a new conversion rule for universal application.
- **11.2 Comments** — the variable restriction on universal abstraction, illustrated by the polymorphic identity; the circularity problem in the naive "function on all types" reading of a universal type; the intuition of "uniformity" for polymorphic functions.
- **11.3 Representation of simple types** — booleans, products, the empty type, sum types, and existential types all encoded as universal types with explicit introduction and elimination terms; notes the translation does not interpret commuting or secondary conversions. : [[Coherence-Space-Semantics|Link]]
- **11.4 Representation of a free structure** — the general theory of encoding an inductively free algebraic structure generated by typed constructors, where the structure occurs only positively. : [[System-F-and-Polymorphism|Link1]], [[Coherence-Space-Semantics|Link2]], [[Parcels-and-Subformulas|Link3]]
  - **11.4.1 Free structure.** : [[System-F-and-Polymorphism|Link]]
  - **11.4.2 Representation of the constructors** — explicit definition of each constructor using a canonical function. : [[Coherence-Space-Semantics|Link]]
  - **11.4.3 Induction** — definition of the induction and recursion principle; the representation traced to a 1970 Martin-Löf manuscript. : [[Natural-Deduction|Link]]
- **11.5 Representation of inductive types** — instantiates the general scheme for booleans, products, sums, and the empty type, then more complex cases. : [[Coherence-Space-Semantics|Link1]], [[System-F-and-Polymorphism|Link2]], [[Parcels-and-Subformulas|Link3]]
  - **11.5.1 Integers** — Church numerals and the iterator, and how the full recursor, needed for the predecessor, can only be simulated "by values," a genuine defect.
  - **11.5.2 Lists** — nil and cons, the iterator, concatenation and reversal as exercises.
  - **11.5.3 Binary trees.**
  - **11.5.4 Trees of branching type U** — transfinite iteration and modularity illustrated via a polymorphic combinator.
- **11.6 The Curry-Howard Isomorphism** — extends Curry-Howard to second-order quantification, with the variable restriction on universal abstraction matching exactly the eigenvariable restriction on universal introduction in natural deduction. : [[The-Curry-Howard-Isomorphism|Link]]

**Key Questions:**
1. Why does the naive "function on all types" reading of a universal type run into a circularity problem, and what weaker notion, uniformity, does Girard offer instead?
2. How does the general free-structure encoding let system F represent integers, lists, and trees uniformly from a single scheme, without any built-in data types?
3. Why can the predecessor function on Church-encoded integers only be defined "by values" rather than satisfying its defining equation outright, and what does this reveal as a genuine expressive limitation of system F?

---

### Chapter 12: Coherence Semantics of the Sum (pp. 94–103)

**Summary:** Attempts to give coherence-space semantics to the sum type and discovers that the naive direct sum cannot interpret the case-elimination scheme, forcing a sequence of fixes that culminates in decomposing the sum using the exponential and direct-sum operators — the discovery that gives birth to linear logic's core connectives and the notion of linearity. : [[Coherence-Space-Semantics|Link]]

**Key Definitions & Concepts by Section:**
- The empty type is interpreted as the empty-web coherence space, which is not an initial object.
- **12.1 Direct sum** — the naive direct sum, an amalgamated disjoint union with the undefined element identified; a casewise definition fails at the undefined element since the two component functions need not agree there.
- **12.2 Lifted sum** — a fix via tags enabling a casewise definition; interprets the standard conversions but not the eta-like equation except on special elements, so the semantics is rejected as unconvincing.
  - **12.2.1 dI-domains** — an alternative fix abandoning coherence spaces for event structures with an added partial order; works but sacrifices coherence-space simplicity and is non-associative.
- **12.3 Linearity** — discovered via the strictness of application; a linear stable function has a trace consisting only of singleton pairs. : [[Linear-Logic|Link]]
  - **12.3.1 Characterisation in terms of preservation** — linear functions preserve unions, not just directed unions.
  - **12.3.2 Linear implication** — the coherence space of linear maps; linear negation; an antisymmetry and duality isomorphism analogous to transposition in linear algebra. : [[Linear-Logic|Link]]
- **12.4 Linearisation** — the "of course" space of finite points; the key fact that every stable function becomes linear once its source is exponentiated. : [[Linear-Logic|Link]]
- **12.5 Linearised sum** — the final fix, combining the exponential with the direct sum; a well-defined casewise definition with no conflict at the undefined element; verifies all the conversions, including the previously failing one. : [[Linear-Logic|Link]]
- **12.6 Tensor product and units** — the tensor product and its dual "par"; four units for the four binary connectives, which collapse pairwise for coherence spaces. : [[Linear-Logic|Link]]

**Key Questions:**
1. Why does the naive direct sum fail to interpret the case-elimination scheme, and what specifically goes wrong at the empty or undefined approximant?
2. What does it mean for a stable function to be "linear," preserving unions rather than just directed unions, and why does the discovery that ordinary implication reduces to a linear one show that linearity is the general phenomenon underneath ordinary implication?
3. How does the fix for the sum type foreshadow linear logic's decomposition of intuitionistic connectives into linear ones?

---

### Chapter 13: Cut Elimination (Hauptsatz) (pp. 104–112)

**Summary:** Proves Gentzen's 1934 Hauptsatz, cut elimination, for the sequent calculus, working through the symmetric key cases where matching right and left logical rules meet at a cut, building the principal lemma by induction on proof height, then bounding the hyperexponential cost of full elimination and connecting the restricted form of the theorem to Robinson's resolution and PROLOG. : [[Linear-Logic|Link1]], [[Sequent-Calculus-and-Cut-Elimination|Link2]]

**Key Definitions & Concepts by Section:**
- **13.1 The key cases** — the symmetric reduction cases pairing right and left rules on the same connective, each replacing a cut on a compound formula by one or two cuts of lower degree; the implication case is the only one needing two cuts. : [[Sequent-Calculus-and-Cut-Elimination|Link]]
- **13.2 The principal lemma** — the degree of a formula and of a proof, and the height of a proof; the principal lemma states that a top-level cut of a given degree can be replaced by a proof of lower degree, proved by induction on the sum of the two premise-proofs' heights. : [[Sequent-Calculus-and-Cut-Elimination|Link]]
- **13.3 The Hauptsatz** — the proposition that any proof of positive degree can be reduced to lower degree; Gentzen's theorem that the cut rule is eliminable; a cost analysis showing cut elimination is hyperexponential in the worst case, "effective but not feasible."
- **13.4 Resolution** — extends the Hauptsatz to proofs with nontrivial proper axioms, restricting cut to instances of proper axioms; specializes to Horn clauses and PROLOG goals; a lemma eliminating contraction and weakening from atomic-sequent proofs; connects to Robinson's resolution method.

**Key Questions:**
1. Why is the implication case the only key case requiring two cuts instead of one, and what does that reveal about implication's asymmetric two-premise left rule?
2. Why is the cost of fully eliminating cuts hyperexponential in the worst case, and what does Girard mean by calling the resulting algorithm "effective but not feasible"?
3. How does the restricted, axiom-relative form of the Hauptsatz specialize to justify PROLOG and Horn-clause resolution?

---

### Chapter 14: Strong Normalisation for F (pp. 113–118)

**Summary:** Extends Tait's reducibility method to system F to prove strong normalisation, overcoming the circularity of "reducible at a universal type iff reducible at every instance" by quantifying over arbitrary reducibility candidates rather than a single "true" reducibility predicate — a proof that must, by Gödel's second incompleteness theorem, go beyond what second-order arithmetic can itself prove, essentially using the comprehension axiom scheme. : [[Normalisation-Theorems|Link]]

**Key Definitions & Concepts by Section:**
- The main theorem, that all F-terms are strongly normalisable with a unique normal form, is tied to the consistency of second-order Peano arithmetic, hence unprovable within that system by Gödel's second incompleteness theorem, forcing a proof strategy that goes outside it.
- **14.1 Idea of the proof** — why naive self-referential reducibility for a universal type fails.
  - **14.1.1 Reducibility candidates** — a reducibility candidate is any predicate satisfying CR1-3, not just the "true" one; a term at a universal type is reducible iff for every type and every candidate of that type, its instantiation is reducible using that candidate.
  - **14.1.2 Remarks** — the CR conditions were found by trial and error; no single formula can express reducibility uniformly; essential use of comprehension to treat a reducibility set itself as a candidate.
  - **14.1.3 Definitions** — the extended neutral term; the reducibility candidate conditions; the arrow-type candidate construction.
- **14.2 Reducibility with parameters** — parametric reducibility defined by induction on type structure, including the universal-type case quantifying over all candidates. : [[Normalisation-Theorems|Link]]
  - **14.2.1 Substitution** — a substitution lemma using comprehension to treat a reducibility set as a parameter.
  - **14.2.2 Universal abstraction** — a lemma establishing reducibility of universal abstractions. : [[Semantics-of-System-F|Link]]
  - **14.2.3 Universal application** — a lemma establishing reducibility of universal applications.
- **14.3 Reducibility theorem** — a reducible term is defined via strongly-normalisable candidates for free type variables; the theorem that all F-terms are reducible, and the corollary of strong normalisation, proved via a doubly-parametric substitution proposition. : [[Normalisation-Theorems|Link]]

**Key Questions:**
1. Why does the naive definition, that a universal-type term is reducible iff each instance is reducible, collapse into circularity, and how does quantifying over arbitrary reducibility candidates escape it?
2. In what precise sense does this proof necessarily go beyond what is provable in second-order Peano arithmetic, and how does Gödel's second incompleteness theorem force that conclusion?
3. Where exactly does the comprehension axiom scheme get used essentially in the proof, and why is this unavoidable for system F's reducibility argument?

---

### Chapter 15: Representation Theorem (pp. 119–130)

**Summary:** Pins down exactly which functions system F can represent, proving the Representation Theorem that F-representable functions are exactly the functions provably total in second-order Peano arithmetic — via a diagonal argument showing F cannot represent its own normalisation function, a proof that representability implies provable totality, and a converse translating proofs of Heyting second-order arithmetic into F terms using realizability ideas from Martin-Löf, cleaned up to avoid "junk" terms. : [[Normalisation-Theorems|Link1]], [[Parcels-and-Subformulas|Link2]]

**Key Definitions & Concepts by Section:**
- **15.1 Representable functions** : [[Gödel's-System-T|Link1]], [[System-F-and-Polymorphism|Link2]]
  - **15.1.1 Numerals** — a proposition that closed normal terms of type Int are numerals, proved via head-normal-form analysis; a remark on syntactic imperfections in variant encodings.
  - **15.1.2 Total recursive functions** — a proposition that there is a total recursive function not representable in F, namely the normalisation function itself, shown non-representable via a Turing-style diagonal argument; connects to Turing's theorem that no total recursive function enumerates all total recursive functions. : [[Gödel's-System-T|Link1]], [[System-F-and-Polymorphism|Link2]]
  - **15.1.3 Provably total functions** — provable totality defined via a termination formula; a proposition that F-representable functions are provably total in second-order Peano arithmetic, proved by examining the mathematical principles used in chapter 14's strong-normalisation proof. : [[Gödel's-System-T|Link1]], [[System-F-and-Polymorphism|Link2]]
- **15.2 Proofs into programs** — the converse Representation Theorem, proved by translating from Heyting second-order arithmetic, closer to system F than classical second-order arithmetic, via a Gödel double-negation translation preserving provability of totality statements. : [[Sequent-Calculus-and-Cut-Elimination|Link]]
  - **15.2.1 Formulation of HA2** — two sorts of variables, for integers and for sets; the universal-elimination rule essentially amounting to the Comprehension Scheme; an impredicative definition of the natural numbers predicate recovering induction without a primitive induction scheme. : [[Normalisation-Theorems|Link]]
  - **15.2.2 Translation of HA2 into F** — a type translation and a term translation of deductions, respecting all conversion rules.
  - **15.2.3 Representation of provably total functions** — the canonical deduction of a numeral's naturalness; the construction extracting a representing term from a totality proof — flagged as erroneous as stated, since one axiom has no genuine F-interpretation without a "junk" term. : [[Gödel's-System-T|Link1]], [[System-F-and-Polymorphism|Link2]]
  - **15.2.4 Proof without undefined objects** — fixes the gap with a translation of types and terms eliminating junk by threading an inhabitant through, completing the Representation Theorem properly.

**Key Questions:**
1. How does the diagonal argument in section 15.1.2 show that system F cannot represent its own normalisation function, and how is this a typed-lambda-calculus echo of Turing's theorem on enumerating total recursive functions?
2. Why does the initial proof of "proofs into programs" fail, and what is the role of the "junk" term in patching it before the cleaner solution?
3. Why is Heyting second-order arithmetic, rather than the classical system directly, the natural system to translate into F, and what does the Gödel double-negation translation buy in connecting the two systems' provability of totality statements?

---

### Appendix A: Semantics of System F (pp. 131–148), by Paul Taylor

**Summary:** Constructs a genuine coherence-space semantics for system F's universal quantifier, solving the "size problem" of too many types to index a function over via finite approximation and rigid embeddings, formalizing "uniformity" — a polymorphic term must behave coherently across isomorphic instantiations — as the technical key, and using this to explicitly compute the denotations of the empty, singleton, boolean, and integer types, revealing surprising extra points beyond the syntactically definable terms. : [[Normalisation-Theorems|Link1]], [[Parcels-and-Subformulas|Link2]]

**Key Definitions & Concepts by Section:**
- **A.1 Terms of universal type** — the size problem in interpreting a universal type as a literal function on all types.
  - **A.1.1 Finite approximation** — solving size via continuity, defining universal terms as directed limits over countably many finite domains.
  - **A.1.2 Saturated domains** — the alternative "universal domain" approach and its pitfalls, chiefly a failure of uniformity across isomorphic type representations.
  - **A.1.3 Uniformity** — the central technical notion: a polymorphic construction must be invariant under automorphisms of the type, illustrated by an argument using the sum of a domain with itself and an analogy to Galois-theoretic separability.
- **A.2 Rigid Embeddings** — formalizes "one domain approximates another" via embedding-projection pairs, adapted from Scott domain theory to the stable, Berry-order setting.
  - **A.2.1 Functoriality of arrow** — makes the arrow constructor functorial, needed so approximation behaves correctly through function types.
- **A.3 Interpretation of Types** — types with free variables become functors, by induction on type structure.
  - **A.3.1 Tokens for universal types** — continuity and stability of the interpretation; every token has a least defining finite subspace, so tokens are describable via finite graphs and hence countable.
  - **A.3.2 Linear notation for tokens** — reuses chapter 12's linear-logic connectives to notate tokens compactly, with a positive/negative occurrence criterion.
  - **A.3.3 The three simplest types** — computes the denotations of the simplest universal types; strikingly, the boolean type has a third, non-syntactic point (intersection) besides true and false, resolved by moving to "linear booleans."
- **A.4 Interpretation of terms** — the full formal coherence-space semantics of F terms.
  - **A.4.1 Variable coherence spaces** — the monotonicity and stability condition on type-indexed objects, proved via a separability lemma.
  - **A.4.2 Coherence of tokens** — coherence and atomicity conditions pinning down exactly which pairs are genuine tokens of a universal type.
  - **A.4.3 Interpretation of F** — the full compositional semantics summary for all five term-forming schemes.
- **A.5 Examples** — concrete computations.
  - **A.5.1 Of course** — computes product, sum, and existential-type denotations, revealing an intersection-like "test" operation as an extra, non-syntactic point.
  - **A.5.2 Natural Numbers** — even the numeral one turns out to have a surprisingly rich token structure.
  - **A.5.3 Linear numerals** — a cleaner linear variant of the natural numbers whose tokens are literal finite chains.
- **A.6 Total domains** — parallels reducibility and realizability: totality candidates for coherence spaces, giving propositions that closed F-terms denote total objects, and that the total objects of the boolean and integer types are exactly the truth values and numerals.

**Key Questions:**
1. What is the "size problem" in trying to interpret a universal type as a literal function defined on all types, and how does finite approximation via countably many finite domains solve it?
2. What does "uniformity" mean for a polymorphic term's denotation, and how does the argument using the sum of a domain with itself make this notion precise via stability and the separability property?
3. Why does the coherence-space model of the boolean type turn out to have a third point besides true and false, and what does moving to "linear booleans" do to eliminate this extra, non-syntactic point?

---

### Appendix B: What is Linear Logic? (pp. 149–160), by Yves Lafont

**Summary:** Motivates and formally presents linear logic, born from coherence semantics in chapter 12, as the result of removing weakening and contraction from sequent calculus, diagnosed via classical logic's algorithmic inconsistency, builds the full one-sided linear sequent calculus with its dual connective pairs and exponential modalities, then introduces proof nets as a geometric, order-independent, parallel proof representation with purely local, confluent, terminating cut elimination, closing with the observation that proof nets are natural deduction done right for linear logic. : [[Normalisation-Theorems|Link1]], [[Parcels-and-Subformulas|Link2]]

**Key Definitions & Concepts by Section:**
- **B.1 Classical logic is not constructive** — why classical proofs cannot be read as algorithms: two different cut-elimination paths through weakening and contraction identify all proofs of a formula denotationally, since classical cut elimination is not Church-Rosser and can even diverge; two fixes: go asymmetric, yielding intuitionistic logic, or drop the structural rules except exchange, yielding linear logic.
- **B.2 Linear Sequent Calculus** — drops weakening and contraction; needs two conjunctions and two disjunctions, tensor and with, and their duals par and plus; one-sided sequents via linear negation, de Morgan-style and involutive; linear implication defined from par and negation; four units for the four binary connectives; exponential modalities "of course" and "why not" reintroducing weakening, contraction, and dereliction in controlled, logically-dressed form; a translation of intuitionistic connectives into linear logic underlying the coherence semantics of earlier chapters.
- **B.3 Proof nets** — restricts to the multiplicative fragment where rule contexts are conservative; motivates proof nets as sequent proofs stripped of redundant context bookkeeping and rule ordering, defined as graphs built from links, cuts, and logical-rule nodes, with a correctness criterion, the long trip condition, picking out genuine proof nets.
- **B.4 Cut elimination** — purely local graph-rewriting conversions for each cut configuration; every proof net reduces to a unique cut-free net, proved via termination and confluence; crucially, cuts can be eliminated in any order, a parallel process, unlike sequential sequent-calculus cut elimination; the cut-free normal form interpreted as an involutive permutation on atoms, with cut composing permutations, the seed of the later geometry-of-interaction program.
- **B.5 Proof nets and natural deduction** — proof nets are natural deduction for linear logic, but cleaner: linearity removes the need for parcels of hypotheses, and linear negation removes the need for discharge or separate elimination rules; modus ponens for linear implication is literally the implication-introduction rule turned upside down.

**Key Questions:**
1. Why does classical logic's cut-elimination process fail to be Church-Rosser, and how does this technically force the collapse of all proofs of the same formula into one?
2. What is the structural difference between the two conjunctions, tensor and with, and why does linear logic need both once weakening and contraction are removed?
3. How do proof nets eliminate the redundancy of sequent-calculus proofs, and why does this let cut elimination proceed in parallel, in any order, rather than sequentially?
