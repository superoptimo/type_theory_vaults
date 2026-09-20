# Typechecking in the λΠ-Calculus Modulo: Theory and Practice — Guidelines

## Header

**Title:** Typechecking in the λΠ-Calculus Modulo: Theory and Practice (Vérification de typage pour le λΠ-Calcul Modulo : théorie et pratique)
**Author(s):** Ronan Saillard
**Publication:** PhD thesis (Doctorat ParisTech), École Nationale Supérieure des Mines de Paris (MINES ParisTech), defended 25 September 2015. Advisors: Pierre Jouvelot (directeur de thèse) and Olivier Hermant (maître de thèse). Jury included Andreas Abel, Brigitte Pientka (rapporteurs), Bruno Barras, Delia Kesner (présidente).

**Brief Summary:**
This thesis gives a complete theoretical foundation for DEDUKTI, a logic-agnostic proof checker built on the λΠ-Calculus Modulo — a dependently-typed λ-calculus extended with user-defined rewrite rules that generalize the usual β-conversion into a βΓ-conversion. Saillard re-presents the calculus (originally due to Cousineau and Dowek) with an untyped notion of rewriting and an iterative, explicit account of how rewrite rules themselves get typed, closing a long-standing gap between the calculus's theory and its actual DEDUKTI implementation. The central technical throughline is finding sufficient conditions — product compatibility and well-typedness of rewrite rules — under which the type system enjoys subject reduction, uniqueness of types, and decidable type-checking, since both properties are shown to be undecidable in general. Successive chapters generalize the class of admissible rewrite rules (non-algebraic and ill-typed left-hand sides, rewriting under binders via encoding into Higher-Order Rewrite Systems, non-left-linear rules via a weak/colored typing discipline) while preserving these guarantees, culminating in sound, complete, and terminating type-checking algorithms actually implemented in DEDUKTI.

**Intent of the Author:**
Saillard aims to close the gap between the original, purely motivational presentation of the λΠ-Calculus Modulo (Cousineau–Dowek 2007) and what DEDUKTI actually implements, by giving a complete, implementation-faithful meta-theoretical study: making explicit exactly which conditions on rewrite rules and global contexts guarantee soundness and decidability of type-checking, and providing algorithms and criteria practitioners can use to verify those conditions on concrete rewrite systems.

---

## Topic List

1. **Abstract Rewriting and Confluence Theory** : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
   - Abstract reduction systems and their basic properties : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
   - Local confluence versus confluence : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
   - Newman's Lemma : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
   - Term rewriting systems over first-order signatures : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
   - Critical pairs and the Critical Pair Theorem : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
   - Orthogonality and left-linearity as confluence criteria : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
   - Parallel reduction and the Parallel Closure Theorem
   - Modularity of confluence for disjoint signatures
   - The untyped λ-calculus and β-reduction : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
   - Combining term rewriting with the λ-calculus via currification
   - Loss of confluence from non-left-linear rules combined with β-reduction
   - Turing's fixed-point combinator as a source of non-confluence counterexamples

2. **The λΠ-Calculus Modulo** : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link1]], [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link2]]
   - Objects, types, kinds and the syntactic stratification of terms
   - Local contexts versus global contexts : [[The-lambda-Pi-Calculus-Modulo|Link]]
   - Rewrite rules as first-class citizens of the global context
   - Untyped rewriting as a departure from the original Cousineau–Dowek presentation : [[The-lambda-Pi-Calculus-Modulo|Link]]
   - Beta reduction and Gamma reduction
   - The generalized conversion rule and definitional equality modulo a rewrite system
   - Stratification of the conversion relation
   - Well-typed terms and the typing judgment : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Well-formed local contexts : [[The-lambda-Pi-Calculus-Modulo|Link]]

3. **Subject Reduction, Product Compatibility and Uniqueness of Types** : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link]]
   - Subject reduction as type preservation under reduction : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link1]], [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link2]]
   - Product compatibility as the key property enabling subject reduction for beta : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link]]
   - Product compatibility from confluence : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link1]], [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link2]]
   - Well-typed rewrite rules and permanently well-typed rewrite rules : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Strongly well-formed rewrite rules and strongly well-formed global contexts : [[The-lambda-Pi-Calculus-Modulo|Link]]
   - Uniqueness of types and its equivalence with right product compatibility : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link]]
   - Reduction to a convertibility check once uniqueness of types holds : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link]]
   - Undecidability of product compatibility and of subject reduction : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link]]
   - Undecidability of uniqueness of types : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link]]
   - Reduction from an undecidable word problem to establish these undecidability results

4. **The λΠ-Calculus Modulo as a Logical Framework** : [[The-lambda-Pi-Calculus-Modulo-as-a-Logical-Framework|Link]]
   - Shallow versus deep encodings of a source logic into a target calculus
   - Encoding of constructive predicate logic via the judgment-as-type correspondence : [[The-lambda-Pi-Calculus-Modulo-as-a-Logical-Framework|Link]]
   - Encoding of the Calculus of Constructions with universes and product representatives : [[The-lambda-Pi-Calculus-Modulo-as-a-Logical-Framework|Link]]
   - Encoding of Heyting Arithmetic with an induction principle : [[The-lambda-Pi-Calculus-Modulo-as-a-Logical-Framework|Link]]
   - Soundness and conservativity theorems for an embedding
   - The Calculus of Constructions Modulo as a polymorphic extension with type operators : [[The-lambda-Pi-Calculus-Modulo-as-a-Logical-Framework|Link]]
   - Toward Pure Type Systems Modulo as a further generalization

5. **Well-Typedness of Rewrite Rules** : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Algebraic left-hand sides as the simplest sufficient condition : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Bidirectional typing as type synthesis and type checking
   - Weakening the algebraicity restriction using bidirectional inference on left-hand sides : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Weakening the well-typedness restriction on left-hand sides : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Typing constraints collected while inferring the type of a left-hand side
   - Most general solutions and pre-solutions of a set of constraints modulo conversion : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Fine-grained typing of rewrite rules using pre-solutions
   - Static symbols versus definable symbols
   - Safe global contexts : [[The-lambda-Pi-Calculus-Modulo|Link]]
   - Permanent pre-solutions and weakly well-formed rewrite rules : [[Type-Inference-and-Type-Checking-Algorithms|Link]]
   - Weakly well-formed global contexts : [[The-lambda-Pi-Calculus-Modulo|Link1]], [[Type-Inference-and-Type-Checking-Algorithms|Link2]]
   - Linearization of non-left-linear rewrite rules justified by typing constraints : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link]]
   - Optimizing dependent pattern matching by dropping redundant constructors
   - An exact characterization of well-typedness as inclusion between solution sets of unification problems
   - Undecidability of well-typedness for rewrite rules via undecidability of higher-order unification : [[Well-Typedness-of-Rewrite-Rules|Link]]

6. **Rewriting Modulo β and Higher-Order Rewrite Systems** : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
   - Loss of confluence from rewrite rules with abstractions on their left-hand side
   - Failure modes of a naive definition of rewriting modulo beta : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
   - Higher-Order Rewrite Systems as a meta-language separating beta-reduction from rewriting : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
   - Preterms, patterns and Miller's decidability of higher-order pattern unification : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
   - Encoding the λΠ-Calculus Modulo into Higher-Order Rewrite Systems : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
   - Uniform terms and λΠ-patterns : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
   - Definition of rewriting modulo beta via the encoding : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
   - Subject reduction and preservation of the congruence for rewriting modulo beta
   - Product compatibility from confluence of rewriting modulo beta : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link]]
   - Beta-well-formed global contexts : [[The-lambda-Pi-Calculus-Modulo|Link]]
   - Higher-order critical pairs and overlapping patterns
   - The Development Closure Theorem as a confluence criterion for left-linear systems
   - Applications to equation solving, negation normal form and universe reflection
   - Compiling pattern matching modulo beta to decision trees : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
   - Soundness and completeness of the compilation to decision trees

7. **Non-Left-Linear Rewriting and Weak Typing** : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link]]
   - Product compatibility for object-level rewrite systems independently of confluence
   - The postponement lemma and the commutation lemma : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link]]
   - Pi-producing rewrite rules as the obstruction to extending the object-level result
   - Weak types and the stripping function from dependent types to simple types : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link]]
   - Non-confusing rewrite rules : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Weak typing as a simply-typed approximation of the full type system
   - The Colored λΠ-Calculus Modulo with a weakly well-typed conversion rule : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link]]
   - Black and white terms, positions and rewrite rules : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Internal reduction and external reduction as a refinement of postponement and commutation : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link]]
   - A general criterion for product compatibility mixing non-left-linear and Pi-producing rules : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link]]
   - Limits of the criterion when reasoning departs from weakly well-typed conversions

8. **Type Inference and Type-Checking Algorithms** : [[Type-Inference-and-Type-Checking-Algorithms|Link]]
   - A bidirectional inference algorithm for terms : [[Type-Inference-and-Type-Checking-Algorithms|Link]]
   - Soundness, termination and completeness of type inference : [[Type-Inference-and-Type-Checking-Algorithms|Link]]
   - A safe inference variant avoiding reliance on subject reduction : [[Type-Inference-and-Type-Checking-Algorithms|Link]]
   - Type checking reduced to inference plus a convertibility test : [[Type-Inference-and-Type-Checking-Algorithms|Link]]
   - Well-formedness checking for local contexts : [[Type-Inference-and-Type-Checking-Algorithms|Link]]
   - Solving unification constraints via a Herbrand-style presolution algorithm
   - Checking weak well-formedness of rewrite rules algorithmically : [[Well-Typedness-of-Rewrite-Rules|Link]]
   - Checking well-typedness of global contexts via a confluence oracle : [[The-lambda-Pi-Calculus-Modulo|Link1]], [[Type-Inference-and-Type-Checking-Algorithms|Link2]]
   - Termination guarantees contingent on strong normalization of the rewrite relation
   - Implementation of these algorithms in the DEDUKTI proof checker

---

## Chapter Summaries

### Chapter 1: Preliminaries (pp. 20–26)

**Summary:** A short review chapter establishing the classical rewriting-theory vocabulary — abstract reduction systems, first-order term rewriting systems, the untyped λ-calculus, and their combination — needed throughout the thesis, with particular emphasis on confluence results and the subtle loss of confluence when non-left-linear rewrite rules meet β-reduction.

**Key Definitions & Concepts by Section:**
- **1.1 Abstract Reduction Systems** — abstract reduction system (a set with a binary relation), joinability ($x \downarrow y$), normal elements, local (weak) confluence vs. confluence, (weak) normalization, termination (strong normalization); Newman's Lemma (a terminating ARS is confluent iff locally confluent). : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
- **1.2 Term Rewriting Systems** — signature, first-order term, substitution, rewrite rule $(l \hookrightarrow r)$, term rewriting system (TRS); position and subterm, most general substitution/unifier, critical pair (from overlapping left-hand sides), the Critical Pair Theorem (a TRS is locally confluent iff its critical pairs are joinable); linearity, left-linearity, orthogonality (left-linear + no critical pairs) implies confluence; parallel reduction $\Rightarrow_R$, parallel-closed TRS, the Parallel Closure Theorem; Modularity of Confluence for TRSs over disjoint signatures. : [[Abstract-Rewriting-and-Confluence-Theory|Link]]
- **1.3 The λ-Calculus** — λ-terms, free/bound variables, capture-avoiding substitution, head β-reduction vs. general β-reduction; confluence of $\to_\beta$ (Church–Rosser); the standardization theorem. : [[Abstract-Rewriting-and-Confluence-Theory|Link1]], [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link2]]
- **1.4 Combining Term Rewriting Systems and the λ-Calculus** — applicative TRS, currification of a TRS (preserves confluence); embedding first-order terms as λ-terms, the $\lambda R$-calculus; confluence of $\to_{\beta R}$ for left-linear, non-variable-applying TRSs; Turing's $\Omega$ fixed-point combinator, used to exhibit concrete non-confluence for non-left-linear rules (e.g. `minus n n → 0`, `eq n n → true`) combined with β-reduction. : [[Abstract-Rewriting-and-Confluence-Theory|Link]]

**Key Questions:**
1. Why does orthogonality (left-linearity plus absence of critical pairs) suffice for confluence, and why does dropping left-linearity typically break confluence once β-reduction is added to the mix?
2. What role does Newman's Lemma play as the connecting bridge between local confluence (a locally checkable property) and full confluence, and why is termination essential to that bridge?

---

### Chapter 2: The λΠ-Calculus Modulo (pp. 27–64)

**Summary:** Introduces a new presentation of the λΠ-Calculus Modulo — the calculus underlying DEDUKTI — built on untyped rewriting with an explicit, iterative account of how rewrite rules are themselves typed. The chapter develops the full type system (terms, local and global contexts, substitutions), gives worked examples (Peano arithmetic, list `map`, Brouwer ordinals), and proves the central meta-theoretic results: subject reduction and uniqueness of types both reduce to two conditions — product compatibility and well-typedness of rewrite rules — which are shown undecidable in general. The chapter closes by using the calculus as a logical framework (encoding constructive predicate logic, the Calculus of Constructions, Heyting Arithmetic) and introduces the Calculus of Constructions Modulo, a polymorphic extension. : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link1]], [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link2]]

**Key Definitions & Concepts by Section:**
- **2.2 Terms, Contexts and Rewrite Rules** — objects, types, kinds and the term $\Lambda$ syntactically stratified into these categories (Figure 2.1); local context $\Delta$; global context $\Gamma$ holding constant declarations and batches of rewrite rules $\Xi$; rewrite rules as pairs of objects or pairs of types (departing from Cousineau–Dowek's context-indexed quadruple presentation). : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
- **2.3 Rewriting** — β-reduction $\to_\beta$; Γ-reduction $\to_\Gamma$ generated by a global context's rewrite rules, closed under substitution and subterm reduction; $\to_{\beta\Gamma}$, $\equiv_{\beta\Gamma}$; the untyped (rather than typed) notion of rewriting as a deliberate departure from the original presentation, closer to DEDUKTI's actual implementation; Stratification of the Conversion (Lemma 2.3.5) — conversion respects the object/type/kind syntactic classes.
- **2.4 Type System** — the typing judgment $\Gamma; \Delta \vdash t : A$ (Figure 2.4: Sort, Variable, Constant, Application, Abstraction, Product, Conversion); well-formed local context $\Gamma \vdash^{ctx} \Delta$; **Subject Reduction** ($SR_r(\Gamma)$) — reduction preserves typing; **Product Compatibility** ($PC(\Gamma)$) — convertible product types have convertible domains/codomains; **Well-Typed Rewrite Rules** — $(u \hookrightarrow v)$ preserves typing under any substitution; **Strongly Well-Formed Rewrite Rule** — algebraic left-hand side with both sides sharing a type in some context; **Well-Typed Global Context** — well-typed declarations + product compatibility + well-typed rewrite rules; **Strongly Well-Formed Global Context** (Figure 2.6) — an inductively-checkable sufficient condition for well-typedness. : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link]]
- **2.5 Examples** — Peano integers with `plus`/`mult` rewrite rules; lists and `map`; Brouwer ordinals with `o_plus`; illustrates that orthogonality is sufficient but not necessary for confluence (associativity/commutativity rules remain confluent by Theorem 1.4.7 though non-orthogonal, but commutativity alone is non-terminating).
- **2.6 Properties** — Inversion lemma; local/global weakening; **Product Compatibility from Confluence** (Theorem 2.6.11); permanently well-typed rewrite rules (well-typed in every well-typed extension); strongly well-formed global contexts are well-typed (Theorem 2.6.19); **Subject Reduction** for $\to_\beta$ and $\to_\Gamma$ separately, then combined (Theorem 2.6.22); **Uniqueness of Types** ($UT(\Gamma)$) — all types of a term are convertible, reducing type-checking to type inference plus a convertibility test; **Right Product Compatibility** ($R\text{-}PC(\Gamma)$) — equivalent to uniqueness of types (weaker than full product compatibility); **Undecidability Results** — product compatibility, subject reduction and uniqueness of types are all undecidable, proved by reduction from Matijasevitch's equational word problem (Theorem 2.6.35).
- **2.7 Applications** — shallow vs. deep encodings; embeddings of Constructive Predicate Logic (`prf` as a type of proofs, natural-deduction-style rewrite rules), the Calculus of Constructions (via explicit universes $U_{Type}$, $U_{Kind}$ and decoding functions $\epsilon$), and Heyting Arithmetic (Peano integers plus an induction principle `rec`); soundness and conservativity theorems for each embedding.
- **2.8 The Calculus Of Constructions Modulo** — extends the λΠ-Calculus Modulo with polymorphism and type operators (mixing the λΠ-calculus's rewriting extension with the Calculus of Constructions's polymorphism); most Chapter 2 properties transfer with minor modification; **2.8.5 Toward Pure Type Systems Modulo** — conjectures the results generalize to arbitrary functional Pure Type Systems, modulo the loss of the object/type/kind syntactic classification. : [[The-lambda-Pi-Calculus-Modulo-as-a-Logical-Framework|Link]]
- **2.9 Related Work** — traces the lineage from Breazu-Tannen's confluence-preservation result through the General Schemata, HORPO, and the Calculus of Algebraic Constructions.

**Key Questions:**
1. Why does the thesis insist on an *untyped* notion of rewriting rather than the context-and-type-indexed rewrite rules of the original Cousineau–Dowek presentation, and what proof obligation does this choice push onto subject reduction?
2. What exactly is the relationship between product compatibility, right product compatibility, subject reduction for β, and uniqueness of types — which implications are equivalences and which are strict?
3. In what precise sense is the λΠ-Calculus Modulo "logic-agnostic," and what does a soundness-and-conservativity pair of theorems buy you when embedding a logic like Heyting Arithmetic?

---

### Chapter 3: Typing Rewrite Rules (pp. 65–96)

**Summary:** Having reduced well-typedness of global contexts to well-typedness of individual rewrite rules, this chapter systematically generalizes the sufficient criterion for that property — from the restrictive "strongly well-formed" (algebraic, well-typed left-hand side) notion to a much broader "weakly well-formed" notion permitting non-algebraic and even ill-typed left-hand sides — while justifying, along the way, the type-safe linearization of non-left-linear rewrite rules whose non-linearity is an artifact of typing constraints rather than intended behavior. The chapter closes with an exact characterization of well-typedness as an inclusion problem between unification-constraint solution sets, from which undecidability follows. : [[Well-Typedness-of-Rewrite-Rules|Link]]

**Key Definitions & Concepts by Section:**
- **3.2 Strongly Well-Formed Rewrite Rules** — proof that strongly well-formed rewrite rules are permanently well-typed (Theorem 3.2.1), via a "main lemma" technique reused throughout the chapter: showing a well-typed redex forces the matching substitution to be well-typed. : [[Well-Typedness-of-Rewrite-Rules|Link1]], [[The-lambda-Pi-Calculus-Modulo|Link2]]
- **3.3 Left-Hand Sides Need not be Algebraic** — motivating example (`getCst (λx:nat.n) → n`) that a strongly well-formed criterion rejects but which is intuitively well-typed; **bidirectional typing** — synthesis judgment $\Gamma;\Delta_1;\Sigma \Rightarrow_i t \Rightarrow T,\Delta_2$ and checking judgment $\Rightarrow_c t \Leftarrow T \mid \Delta_2$ (Figure 3.1); Theorem 3.3.3 generalizes well-typedness to left-hand sides whose type (and free variables' types) can be *inferred* rather than required to be algebraic. : [[Well-Typedness-of-Rewrite-Rules|Link]]
- **3.4 Left-Hand Sides Need not be Well-Typed** — soundness of the bidirectional system w.r.t. $\vdash$ (Theorem 3.4.1); motivates dropping the well-typed-left-hand-side requirement via the non-confluent `head`/vector example, whose non-left-linearity is purely an artifact of dependent typing. : [[Well-Typedness-of-Rewrite-Rules|Link]]
- **3.5 Taking Advantage of Typing Constraints** — Typing Constraints as a set of term pairs / unification problem modulo $\equiv_{\beta\Gamma}$; **Most General Solution (MGS)** and, since MGSs need not exist modulo conversion, the weaker notion of **Pre-Solution**; the augmented bidirectional system (Figures 3.3–3.4) that *records* constraints instead of discarding them; Theorem 3.5.8 generalizes well-typedness using pre-solutions, justifying the linearization of `tail`'s rewrite rule.
- **3.6 Weakly Well-Formed Global Contexts** — the naive notion of "permanent pre-solution" collapses to the identity substitution; **Static and Definable Symbols** partition constants; **Safe Global Context** — well-typed, confluent, and rewrite rules only fire on definable-symbol heads; refined **Permanent Pre-Solution** (quantified over safe extensions); **Weakly Well-Formed Rewrite Rule** and **Weakly Well-Formed Global Context** (Figure 3.5); Theorem 3.6.9 — weakly well-formed contexts are safe (hence well-typed); worked examples (vector functions, simply typed λ-calculus embedding); §3.6.5 connects this linearization technique to dependent-pattern-matching optimizations used in Agda. : [[The-lambda-Pi-Calculus-Modulo|Link1]], [[Type-Inference-and-Type-Checking-Algorithms|Link2]]
- **3.7 Characterisation of Well-Typedness of Rewrite Rules** — an extended type-constraint-recording system $\stackrel{e}{\Rightarrow}$ (Figure 3.6) that always synthesizes a type, introducing fresh type-level metavariables when needed; **Solutions of a Set of Typing Constraints** as triples $(\Delta, \sigma, \tau)$; Theorem 3.7.8 — well-typedness of $(u \hookrightarrow v)$ is *equivalent* to an inclusion of unification-constraint solution sets ($Sol(V_u, C_u) \subseteq$ extendable to $Sol(V_u \cup V_v, C_u \cup C_v \cup \{T_u = T_v\})$); applications recovering well-typedness of the Identity, η-reduction, and Trivial β-redex rules that no earlier criterion could handle. : [[Well-Typedness-of-Rewrite-Rules|Link]]
- **3.7.5 Undecidability** — undecidability of higher-order unification modulo $\equiv_\beta$ (via reduction from Hilbert's tenth problem, using Church numerals) implies **Undecidability of Well-Typedness for Rewrite Rules** (Theorem 3.7.13).

**Key Questions:**
1. Why is linearizing a non-left-linear rewrite rule (replacing repeated variable occurrences by fresh ones) type-safe precisely when the non-linearity arises from typing constraints, but *not* type-safe when the non-linearity is semantically intended (e.g. `eq n n → true`)?
2. What is the technical role of a "pre-solution" as opposed to a most general unifier, and why does unification modulo $\equiv_{\beta\Gamma}$ force this weaker notion?
3. How does casting well-typedness of rewrite rules as an inclusion problem between two unification-constraint solution sets make the undecidability proof (Theorem 3.7.13) essentially a corollary of undecidable higher-order unification?

---

### Chapter 4: Rewriting Modulo β (pp. 97–118)

**Summary:** Addresses a structural problem left open by Chapter 3: rewrite rules with λ-abstractions on their left-hand side (needed to match "under binders") almost always destroy confluence when combined with β-reduction. Saillard resolves this by defining rewriting *modulo* β — matching up to β-equivalence — through a faithful encoding of the λΠ-Calculus Modulo into Nipkow's Higher-Order Rewrite Systems (HRS), importing HRS confluence machinery (critical pairs, the Development Closure Theorem) into the λΠ setting, and shows this new relation still yields subject reduction, product compatibility from confluence, and an efficient implementation via compilation to (β-aware) decision trees. : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]

**Key Definitions & Concepts by Section:**
- **4.2 A Naive Definition of Rewriting Modulo β** — a naive "match up to $\equiv_\beta$" definition breaks subject reduction, can introduce free variables, and still fails to provide confluence — motivating a principled construction instead. : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
- **4.3 Higher-Order Rewrite Systems** — Nipkow's HRS: simple types, preterms, restricted η-expansion, HRS-terms (βη-normal forms); **Pattern** (Miller pattern: every free occurrence of a metavariable applied to pairwise-distinct bound variables) — the crucial property enabling decidable, unique-most-general-unifier higher-order (pattern) unification; HRS rewrite rule and HRS rewrite relation. : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
- **4.4 An Encoding of the λΠ-Calculus Modulo into HRS** — signature $\mathrm{Sig}(\lambda\Pi)$ with `App`, `Lam`, `Pi`; encoding $\|.\|$ of λΠ-terms as HRS terms (a bijection onto well-typed HRS terms), compositional with substitution; the `(beta)` HRS rule simulating β-reduction; **Uniform Terms** (arity-consistent free-variable occurrences) and **λΠ-patterns**; **Encoding of Rewrite Rules** requiring the left-hand side be a λΠ-pattern with matching arity constraints; $\mathrm{HRS}(\Gamma)$, $\mathrm{HRS}(\beta\Gamma)$. : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
- **4.5 Rewriting Modulo β** — **Rewriting Modulo β** ($\to_{\Gamma b}$, $\to_{\beta\Gamma b}$) defined via the encoding; $\to_{\beta\Gamma b} = \to_{\Gamma b} \cup \to_\beta$; the introductory `D`/`fMult` example now closes its critical peak; **Subject Reduction for $\to_{\Gamma b}$** (Theorem 4.5.4), proved by lifting HRS-level β-steps back to λΠ-level rewriting; the congruence $\equiv_{\beta\Gamma b}$ coincides with $\equiv_{\beta\Gamma}$ (Theorem 4.5.6); **Product Compatibility from Confluence of $\mathrm{HRS}(\beta\Gamma)$** (Theorem 4.5.7); **β-Well-Formed Global Contexts** (Figure 4.1) generalizing weakly well-formed contexts by requiring confluence only modulo β. : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
- **4.6 Proving Confluence of Rewriting Modulo β** — **Overlapping Patterns** and **Higher-Order Critical Pair**; Nipkow's theorem (terminating HRS confluent iff critical pairs joinable) is of limited use since `(beta)` is non-terminating; **Simultaneous Reduction** and the **Development Closure Theorem** (van Oostrom) — a left-linear HRS is confluent if root critical pairs are joinable by simultaneous reduction and inner critical pairs commute with it; Corollary 4.6.7 applies this to $\to_{\Gamma b}$. : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
- **4.7 Applications** — parsing/solving linear equations via λΠ-patterns that inspect terms under binders; negation normal form via rewrite rules with abstractions pushing negation through quantifiers; universe reflection (Assaf) as an application requiring confluence modulo β.
- **4.8 Compiling Rewrite Rules for Rewriting Modulo β** — extends Maranget's compilation of pattern matching to decision trees to handle matching modulo β; **Decision Tree** syntax (`Leaf`, `Switch`) generalized to record flexible-rigid equations $x_i \vec{y}_i = t_i$ at leaves instead of solved-form equations; matrix specialization operators $S_{(u,n)}$, $S_\lambda$, default matrix $D$; **Soundness of CC** (Theorem 4.8.20) and **Completeness of CC** (Theorem 4.8.22) for the compiled decision-tree semantics against the `Match` relation.

**Key Questions:**
1. Why does encoding the λΠ-Calculus Modulo into Higher-Order Rewrite Systems — rather than defining rewriting modulo β directly — let the thesis reuse existing confluence machinery (critical pairs, the Development Closure Theorem) instead of reproving it from scratch?
2. What specifically goes wrong with the "naive" definition of rewriting modulo β (matching up to $\equiv_\beta$ directly), and how does the HRS encoding's restriction to patterns and uniform terms avoid each failure mode?
3. Why must the decision-tree leaves for matching modulo β carry flexible-rigid equations rather than the solved-form equations sufficient for ordinary syntactic pattern matching, and what does that change about solution uniqueness?

---

### Chapter 5: Non-Left-Linear Systems (pp. 119–140)

**Summary:** Turns to rewrite systems that are genuinely, semantically non-left-linear (not merely artifacts of typing constraints, as in Chapter 3) — where confluence is almost always lost once combined with β-reduction, cutting off the thesis's main tool for proving product compatibility. Saillard first shows product compatibility holds unconditionally (without confluence) for purely object-level rewrite systems, then — for the harder case mixing non-left-linear rules with type-producing ("Π-producing") rules — introduces a weak/simply-typed approximation of the type system, the resulting "Colored" λΠ-Calculus Modulo with a weakly-well-typed conversion rule, and a general criterion for product compatibility phrased in terms of "black" (potentially non-confluent) and "white" (safe) subterms and positions. : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link]]

**Key Definitions & Concepts by Section:**
- **5.2 Object-Level Rewrite Systems** — **Π-Producing Rewrite Rules** (a rule whose right-hand side introduces a product type not hidden under an abstraction's annotation); Theorem 5.2.4 — global contexts without Π-producing rules satisfy product compatibility regardless of confluence (adapting Barbanera–Geuvers–Fernández); proved via a **Postponement Lemma** (Γ-reductions toward a product type can be postponed after head-β-reductions) and a **Commutation Lemma** ($\to_\Gamma$ and head-β commute); illustrated with a `minus` example that is product-compatible yet demonstrably non-confluent. : [[Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Link]]
- **5.3 Towards a New Criterion For Product Compatibility** — motivating polymorphic-pairs example mixing a Π-producing rewrite rule (universe decoding) with an intentionally non-left-linear surjectivity rule, where the two rule sets act on disjoint "layers" of types and should not interact. : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link1]], [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link2]]
- **5.4 Weak Typing** — **Weak Types** built from `Kind`, `Type`, `Black`, `White`, and arrows (Figure 5.2); the **Stripping Function** $\|.\|$ collapsing dependent types/kinds to weak types, ignoring object-level dependencies; **Color** of a weak type (`Black`/`White`, propagated through arrow codomains); **Non-Confusing Rewrite Rules** (preserve color); **Weak Typing** judgment $\Gamma;\Delta \vdash^w t : T$ (a simply-typed approximation, Figure 5.3) such that full typing implies weak typing of the stripped type (Lemma 5.4.11) but not conversely. : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link]]
- **5.5 The Colored λΠ-Calculus Modulo** — **Weakly Well-Typed Conversion** ($\vdash^w t_1 \equiv t_2$, restricted to steps through weakly-well-typed intermediate terms); the **Restricted Conversion** typing rule (Figure 5.5) replacing ordinary (Conversion) to define $\vdash'$; $\vdash' \subseteq \vdash$ always, and $\vdash' = \vdash$ whenever the underlying rewrite relation is confluent. : [[Non-Left-Linear-Rewriting-and-Weak-Typing|Link]]
- **5.6 A General Criterion for Product Compatibility for the Colored λΠ-Calculus Modulo** — **Black and White Rewrite Rules** (colored by their head symbol's weak return type) and **Black/White Positions and Terms**; Theorem 5.6.5's four hypotheses (weakly well-typed context, left-linear black rules, confluence of black-rules-plus-β, non-variable subterms of black left-hand sides occur only at black positions); the **Internal Reduction** $\to_{in}$ (reduction inside white subterms) and **External Reduction** $\to_{out}$ (its complement, contained in $\to_\beta \cup \to_{Black}$); a postponement/commutation/product-types trio of lemmas mirroring §5.2's proof strategy but relativized to black/white; §5.6.3 verifies the polymorphic-pairs example satisfies all four hypotheses; §5.6.4 gives a counterexample (`choose`/`T`) showing the criterion does *not* transfer back to the unmodified (uncolored) λΠ-Calculus Modulo — the weakly-well-typed restriction on conversion is doing essential work.

**Key Questions:**
1. Why does product compatibility hold unconditionally for object-level (non-Π-producing) rewrite systems even when confluence fails outright, and what exactly breaks once a Π-producing rule is added?
2. What problem does "weak typing" (the Black/White stripping discipline) solve that full dependent typing cannot, and why does collapsing all type constants down to just two colors maximize the criterion's applicability?
3. In the counterexample of §5.6.4, precisely which step of the standard product-compatibility argument fails once the intermediate term in the conversion path is *not* weakly well-typed?

---

### Chapter 6: Type Inference (pp. 141–151)

**Summary:** Assembles the meta-theory of the previous chapters into concrete, pseudocode type-checking algorithms — for terms, local contexts, rewrite rules, and global contexts — and proves each sound, and (under confluence and termination assumptions) complete and terminating. These are the algorithms actually implemented in DEDUKTI, closing the loop between the thesis's theoretical development and the tool that motivated it. : [[Type-Inference-and-Type-Checking-Algorithms|Link]]

**Key Definitions & Concepts by Section:**
- **6.2 Type Inference** — `infer`, a bidirectional-style structural algorithm implementing the typing rules directly (Conversion is never invoked explicitly; instead the inferred type of a function is normalized to expose a product type before the Application case fires); **Soundness of infer** (Theorem 6.2.2, relying on subject reduction); `safe_infer`, a variant that re-checks the normalized type instead of assuming subject reduction, dropping the well-typedness precondition on $\Gamma,\Delta$; Theorem 6.2.4 shows `infer` is also sound with respect to the Colored calculus's $\vdash'$ from Chapter 5, letting Theorem 5.6.5 substitute for full product compatibility when needed; **Termination of infer** (recursive calls only on strict subterms, so termination reduces to termination of `normalize`); **Completeness of infer** requires both confluence and termination of $\to_{\beta\Gamma}$. : [[Type-Inference-and-Type-Checking-Algorithms|Link]]
- **6.3 Type Checking** — `check`, reducing type-checking to inference plus a convertibility test, justified by uniqueness of types; soundness, termination and completeness theorems mirroring §6.2's. : [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Link1]], [[Type-Inference-and-Type-Checking-Algorithms|Link2]]
- **6.4 Well-Formedness Checking for Local Contexts** — `local_wf`, structurally checking each declared variable's type infers to `Type`; soundness/termination/completeness via induction on the local context. : [[Type-Inference-and-Type-Checking-Algorithms|Link]]
- **6.5 Well-Typedness Checking for Rewrite Rules** — `find_presolution`, a Herbrand-style unification algorithm (syntactic decomposition, occur check, dropping unsolvable-but-ignorable rigid/definable-symbol equations) computing a permanent pre-solution, using `bounded_normalize` since inputs may be ill-typed; `infer_lhs`/`check_lhs` implementing (a partial version of) the constraint-recording bidirectional system of Chapter 3; `rewrite_wf`, combining these to soundly (and terminatingly) check weak well-formedness of a rewrite rule. : [[Well-Typedness-of-Rewrite-Rules|Link]]
- **6.6 Checking Well-Typedness for Global Contexts** — `is_confluent` as an (undecidable-in-general, three-valued) confluence oracle approximating the Development Closure Theorem; `global_wf`, the top-level algorithm combining `infer`, `rewrite_wf` and `is_confluent` to check β-well-formedness (hence well-typedness, via Theorem 4.5.10) of an entire global context, proved sound and terminating by structural induction on $\Gamma$. : [[The-lambda-Pi-Calculus-Modulo|Link]]

**Key Questions:**
1. Why can type-checking be reduced to type inference plus a single convertibility test, and what specific meta-theoretic property (proved back in Chapter 2) makes that reduction sound?
2. What is the practical trade-off between `infer` (which assumes subject reduction) and `safe_infer` (which re-verifies it at each application), and why does the thesis prefer `infer` for an actual implementation?
3. Since confluence and well-typedness of rewrite rules are both undecidable in general (Chapters 2–3), how do `is_confluent` and `find_presolution` remain sound *algorithms* despite operating on an undecidable problem — what do they give up to stay total and correct?

---

### Conclusion (p. 152)

**Summary:** Recaps the thesis's chapter-by-chapter contributions (new presentation of the calculus, generalized well-typedness criteria for rewrite rules, rewriting modulo β via HRS encoding, product-compatibility criteria for non-left-linear systems, and sound/complete/terminating algorithms implemented in DEDUKTI) and outlines four directions for future work: studying termination of the rewrite system on well-typed terms (not addressed in the thesis), rewriting modulo a general equational theory (e.g. commutativity) rather than just modulo β, moving to a *typed* notion of conversion to potentially recover confluence-independent results more broadly, and extending the Calculus of Constructions Modulo with universes toward a rewriting-based proof assistant in the spirit of Chrząszcz and Walukiewicz-Chrząszcz's work on Coq. : [[Type-Inference-and-Type-Checking-Algorithms|Link]]

**Key Questions:**
1. Why does the author single out termination as the one major decidability-relevant property left entirely unaddressed by this thesis, given how central confluence and well-typedness are to everything else?
