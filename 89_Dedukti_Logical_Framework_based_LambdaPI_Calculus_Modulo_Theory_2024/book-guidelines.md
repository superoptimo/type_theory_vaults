# Dedukti: a Logical Framework based on the λΠ-Calculus Modulo Theory — Guidelines

## Header

**Title:** Dedukti: a Logical Framework based on the λΠ-Calculus Modulo Theory
**Author(s):** Ali Assaf, Guillaume Burel, Raphaël Cauderlier, David Delahaye, Gilles Dowek, Catherine Dubois, Frédéric Gilbert, Pierre Halmagrand, Olivier Hermant, Ronan Saillard
**Publication:** arXiv:2311.07185v1 [cs.LO], 13 Nov 2023 (Deducteam)

**Brief Summary:**
This is a 36-page survey paper, not a book — it has ten numbered sections rather than chapters, and this guide treats each top-level section as a chapter unit. The paper presents Dedukti, a proof-checker implementing the λΠ-calculus modulo theory (dependent types plus user-declared rewrite rules), and argues that a single logical framework of this kind can host many otherwise-independent logical systems: constructive and classical predicate logic, Simple type theory, Pure type systems including the Calculus of (Inductive) Constructions with universes, and even programming-language semantics. Its central thesis is that using rewrite rules to encode a theory's connectives, quantifiers, and computation rules yields *shallow* embeddings — ones that preserve binding, typing, and reduction — which in turn let large proof libraries from independent systems (Zenon, iProverModulo, FoCaLiZe, HOL Light, Matita) be translated into Dedukti and checked by a single, small, trusted kernel.

**Intent of the Author:**
The authors want to demonstrate, empirically and not just via adequacy theorems, that the λΠ-calculus modulo theory scales to real, large-scale proof libraries — moving the field from "what is a good system to express mathematics?" toward the more specific question "which definitions, axioms, and rewrite rules are needed to prove which theorem?" — as a first step toward interoperability and reverse engineering of proofs across independently-developed systems.

---

## Topic List

1. **The λΠ-Calculus and Its Typing Judgments** : [[Lambda-Pi-Calculus-and-Its-Typing-Judgments|Link]]
   - Dependent types and the sorts Type and Kind : [[Lambda-Pi-Calculus-and-Its-Typing-Judgments|Link]]
   - Contexts, well-formedness, and local versus global contexts : [[Lambda-Pi-Calculus-and-Its-Typing-Judgments|Link]]
   - Typing rules for variables, products, abstraction, and application
   - The conversion rule and definitional equality up to β-reduction : [[Lambda-Pi-Calculus-and-Its-Typing-Judgments|Link]]

2. **The λΠ-Calculus Modulo Theory** : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
   - Rewrite rules as part of the global context : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link1]], [[Lambda-Pi-Calculus-and-Its-Typing-Judgments|Link2]]
   - Conversion extended by a user-declared congruence : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
   - Subject reduction and its dependence on well-typed rules and product compatibility
   - Uniqueness of types modulo conversion
   - Rule schemes and finite contexts for infinite theories : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]

3. **Decidability via Effective Subsystems** : [[Decidability-via-Effective-Subsystems|Link]]
   - Confluence as a prerequisite proved before termination or typing
   - Higher-order rewriting and rewriting modulo β-equivalence : [[Decidability-via-Effective-Subsystems|Link]]
   - Miller's pattern unification as the tractable fragment for left-hand sides
   - Static versus definable symbols and injectivity : [[Decidability-via-Effective-Subsystems|Link]]
   - Most general typing substitutions for non-well-typed left-hand sides : [[Decidability-via-Effective-Subsystems|Link]]
   - The effectiveness theorem linking confluence and termination to decidable type-checking

4. **The Dedukti System and Concrete Syntax** : [[The-Dedukti-System-and-Concrete-Syntax|Link]]
   - Dedukti as a proof-checker rather than a proof-development environment
   - Variable and rewrite-rule declaration syntax
   - Definable symbols, static symbols, wildcards, and guards : [[Decidability-via-Effective-Subsystems|Link]]
   - Confluence checking deferred to external tools via TPDB export : [[The-Dedukti-System-and-Concrete-Syntax|Link]]

5. **Embedding Predicate Logic in a Logical Framework** : [[Embedding-Predicate-Logic-in-a-Logical-Framework|Link]]
   - Language, term, and proposition embeddings : [[Embedding-Predicate-Logic-in-a-Logical-Framework|Link]]
   - Propositions as types versus propositions as a subtype of types (the epsilon embedding)
   - Deep encoding via a universe of propositions versus shallow Type-level encoding
   - Deduction modulo theory as rewrite-rule-defined connectives and quantifiers : [[Embedding-Predicate-Logic-in-a-Logical-Framework|Link]]
   - Comprehension schemes and skolemization : [[Embedding-Predicate-Logic-in-a-Logical-Framework|Link]]

6. **Classical Logic via Double-Negation Connectives** : [[Classical-Logic-via-Double-Negation-Connectives|Link]]
   - The distinction between classical proofs and classical connectives
   - Negative translation and the introduction of an explicit atom-embedding connective
   - Defining classical connectives and quantifiers from constructive ones : [[Classical-Logic-via-Double-Negation-Connectives|Link]]
   - Avoiding critical pairs when translating classical rewrite rules : [[Classical-Logic-via-Double-Negation-Connectives|Link]]
   - Zenon and Zenon Modulo as tableaux-based classical proof producers : [[Classical-Logic-via-Double-Negation-Connectives|Link]]

7. **Simple Type Theory and Pure Type Systems** : [[Simple-Type-Theory-and-Pure-Type-Systems|Link]]
   - Simple type theory as an independent system versus as an instance of a Pure type system : [[Simple-Type-Theory-and-Pure-Type-Systems|Link]]
   - Indexing quantifiers and connectives by a term-level representation of types
   - Pure type system specifications via sorts, axioms, and rules
   - Tarski-style universes and the embedding of terms, types, and contexts : [[Simple-Type-Theory-and-Pure-Type-Systems|Link]]
   - Preservation of computation, preservation of typing, and conservativity results

8. **Embedding Programming Languages** : [[Embedding-Programming-Languages|Link]]
   - Shallow embeddings preserving binding, typing, and operational semantics
   - The untyped and simply-typed λ-calculus with an explicit fixpoint operator
   - The ς-calculus, object records, and the preobject technique for partial construction : [[Embedding-Programming-Languages|Link]]
   - ML pattern matching via destructors and recursion via a call-freezing operator : [[Embedding-Programming-Languages|Link]]
   - FoCaLiZe as a certified-program environment delegating proofs to Zenon Modulo

9. **Inductive Types and Universe Hierarchies** : [[Inductive-Types-and-Universe-Hierarchies|Link]]
   - Constructors and primitive recursion/elimination operators (Gödel's system T style)
   - The Calculus of Inductive Constructions as an extension with inductive types
   - Cumulative universe hierarchies and explicit lifting operators : [[Inductive-Types-and-Universe-Hierarchies|Link]]
   - Ensuring unique term representations under cumulativity
   - Matita's Calculus of Constructions with universes and proof irrelevance

10. **Interoperability and Reverse Engineering of Proofs** : [[Interoperability-and-Reverse-Engineering-of-Proofs|Link]]
    - Translating and checking large external proof libraries as validation of expressivity
    - The role of a small trusted kernel in auditing proofs from independent systems
    - Combining lemmas developed in different theories and systems : [[Interoperability-and-Reverse-Engineering-of-Proofs|Link]]
    - Reverse engineering as identifying the minimal theory a proof actually needs

---

## Chapter Summaries

### Section 1: Introduction (pp. 1–3)

**Summary:** Motivates a single logical framework for expressing many theories by listing the advantages of predicate logic as a framework (definitions proved once, partial ordering between theories, combining lemmas across theories) and the specific limitations of predicate logic itself (no arbitrary binders, no propositions-as-types, no deduction/computation distinction, no uniform notion of cut, classical-only) that led to independent, mutually incompatible logical systems. Introduces the λΠ-calculus modulo theory as the combination of the Logical framework (solving binder and propositions-as-types problems) and Deduction modulo theory (solving the deduction/computation distinction) that addresses four of these five limitations.

**Key Definitions & Concepts by Section:**
- **Predicate logic limitations** — no bound variables beyond $\forall,\exists$; no propositions-as-types; no deduction/computation distinction; no uniform cut notion; classical-only.
- **Logical framework** ($\lambda\Pi$-calculus) — extension of predicate logic with dependent types, solving limitations 1 and 2.
- **Deduction modulo theory** — extension solving limitations 3 and 4 (computation as rewriting alongside deduction).
- **$\lambda\Pi$-calculus modulo theory** — combination of the two, a variant of Martin-Löf's logical framework.

**Key Questions:**
1. Why does predicate logic's inability to bind variables outside $\forall/\exists$ force systems like Peano arithmetic's $2\times 2$ computation to proceed by deduction steps rather than direct computation?
2. In what precise sense do the Logical framework and Deduction modulo theory each solve a disjoint subset of predicate logic's five listed limitations, and why does combining them yield a framework solving four of the five?

---

### Section 2: The λΠ-Calculus Modulo Theory (pp. 3–9)

**Summary:** Presents the formal typing system in two layers: first the plain $\lambda\Pi$-calculus (dependent types, $Type$/$Kind$ sorts, the eight typing rules), then its extension with rewrite rules declared in the global context, which changes what counts as definitional equality in the conversion rule. Establishes that subject reduction and uniqueness of types are consequences of well-typed rewrite rules and product compatibility, then works through the decidability question: since arbitrary rewriting makes the congruence undecidable in general, effective subsystems restrict rewrite rules to Miller's pattern fragment combined with higher-order rewriting, giving confluence (proved first, independent of termination) and hence decidable conversion when also terminating.

**Key Definitions & Concepts by Section:**
- **2.1 The λΠ-calculus** — $Type$, $Kind$, dependent product $\Pi x:A\,B$; typing judgments for well-formedness, variable, product (for kinds/types), abstraction (for type families/objects), application, and conversion (via $\equiv_\beta$). : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
- **2.2.1 Local and global contexts** — global contexts hold variable declarations and rewrite rules; local contexts ($\Delta$) hold only object-variable declarations; a rewrite rule is a pair $\langle l,r\rangle$ with local context $\Delta$, written $l \longrightarrow_\Delta r$. : [[Lambda-Pi-Calculus-and-Its-Typing-Judgments|Link1]], [[The-Lambda-Pi-Calculus-Modulo-Theory|Link2]]
- **2.2.2 Conversion** — rewriting relation $\to_{\beta\Gamma}$ generated by $\beta$-reduction plus declared rules; congruence $\equiv_{\beta\Gamma}$ is its reflexive-symmetric-transitive closure; conversion rule uses $\equiv_{\beta\Gamma}$ in place of $\equiv_\beta$.
- **2.2.3 Subject reduction** — well-typedness of rewrite rules (Definition 2: rule is type-preserving for any substitution) and product compatibility (Definition 3: convertible products have convertible domains/codomains) together imply Subject Reduction (Lemma 4) and Uniqueness of Types (Lemma 5). : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
- **2.2.4 Rules and rule schemes** — theories with infinitely many symbols/rules (recognized by an algorithm) are handled since any single derivation only ever uses a finite context. : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
- **2.3.1 Higher-order rewriting** — plain first-order confluence with $\beta$ can fail once $\lambda$-abstraction appears in left-hand sides (the differentiation-rule critical-peak example); the fix is higher-order rewriting via higher-order matching, decidable when restricted to **Miller's patterns** (Definition 6: a $\beta$-normal term $f\,u_1\dots u_n$ is a pattern w.r.t. $\Delta$ if $f\notin\Delta$ and $\Delta$-variables are applied to pairwise distinct bound variables). : [[Decidability-via-Effective-Subsystems|Link]]
- **2.3.2 Typing rewrite rules** — static vs. definable symbol distinction implicit here via injectivity; the *Tail* example shows why requiring $l$ itself to be well-typed is too restrictive, motivating the **most general typing substitution** $\tau$ (a substitution making $\tau l$ well-typed, used instead of $l$ directly) and the resulting well-typedness rule; Effectiveness Theorem (Theorem 8): strongly well-formed context + confluent higher-order rewriting $\Rightarrow$ subject reduction; if additionally terminating on well-typed terms $\Rightarrow$ typing is decidable. : [[Decidability-via-Effective-Subsystems|Link]]

**Key Questions:**
1. Why must confluence be established *before* termination or well-typedness assumptions in this system, rather than the more familiar order of proving termination first?
2. Work through the $Tail\,n\,(Cons\,m\,a\,l) \longrightarrow l$ example: why does the naive rule (requiring $l$ well-typed) reject this rule, and what does the most general typing substitution $\tau = \{p/m, p/n\}$ buy you that makes it acceptable?
3. Why does allowing $\lambda$-abstraction inside rewrite-rule left-hand sides break ordinary first-order confluence, and how does restricting to Miller's pattern fragment restore a decidable notion of matching?

---

### Section 3: Dedukti (pp. 9–11)

**Summary:** Introduces Dedukti's concrete syntax for the calculus of Section 2: variable/rewrite-rule declarations, the single root-level constant `Type`, definitions, static vs. definable symbols, wildcards, and guards — the last being a mechanism to accept rules whose well-typedness depends on injectivity Dedukti cannot verify automatically, deferring that check to run time.

**Key Definitions & Concepts by Section:**
- **3.1 A proof-checker** — Dedukti checks proofs developed elsewhere rather than assisting in their construction; `->` for $\Pi$-types, `def` for definable symbols, `=>` for $\lambda$-abstraction; rules sharing a head symbol can be declared "all at once" (single trailing dot) versus incrementally, affecting whether earlier rules can type-check later ones; confluence checking is delegated to external tools via TPDB export. : [[Embedding-Programming-Languages|Link]]
- **3.2 Static and definable symbols** — static symbols (declared without `def`) may never appear at the head of a rewrite rule and are therefore guaranteed injective w.r.t. $\equiv_{\beta\Gamma}$; definable symbols (declared with `def`) may be rewrite-rule heads. : [[Decidability-via-Effective-Subsystems|Link]]
- **3.3 Wildcards** — the `_` pattern for unnamed, matched-but-unused variables in a left-hand side.
- **3.4 Guards** — bracket notation `{n}` lets a user assert a subterm's shape (needed for well-typedness but not decidable by Dedukti itself); Dedukti type-checks as if unguarded but rewrites using the guard-stripped linear rule, re-verifying the guard's typing constraint at every use and failing if violated.

**Key Questions:**
1. Why does declaring rewrite rules for the same head symbol "all at once" versus incrementally change which rules are available to type-check which others?
2. What problem do guards solve that wildcards cannot, and why can Dedukti not statically verify a guard's validity in general?

---

### Section 4: Constructive Predicate Logic and Deduction Modulo Theory (pp. 11–17)

**Summary:** Shows how to embed constructive predicate logic into Dedukti in two stages: first minimal predicate logic directly via the propositions-as-types principle (Section 4.1), then full constructive predicate logic (Section 4.2) by introducing a universe `o` of propositions and an explicit `eps` embedding into `Type`, with connectives and quantifiers given "second-order" rewrite-rule definitions that turn a deep encoding into a shallow, Type-level one. Section 4.3 extends this to full Deduction modulo theory (e.g., Heyting arithmetic via nine rewrite rules), and Section 4.4 describes iProverModulo, which compiles classical resolution/narrowing proofs into Dedukti terms and has been used at the scale of thousands of TPTP problems.

**Key Definitions & Concepts by Section:**
- **4.1 Minimal predicate logic** — Language embedding (Definition 9): sorts become `Type`-valued variables, function/predicate symbols become curried arrows. Term embedding (Definition 10) and proposition embedding (Definition 12) for the $\{\Rightarrow,\forall\}$ fragment, directly using `Type` as the type of propositions. Proof embedding theorem (Theorem 14): provability in Natural deduction $\iff$ existence of a (normal) inhabiting $\lambda$-term. : [[Embedding-Predicate-Logic-in-a-Logical-Framework|Link]]
- **4.2 Constructive predicate logic** — universe `o : Type` of propositions ("à la Tarski"), `eps : o -> Type` embedding; connectives (`imp`, `and`, `or`, `top`, `bot`, `not`) and quantifiers (`fa_s`, `ex_s`) declared as `o`-valued symbols with rewrite rules defining `eps` on them via **second-order encodings** (e.g. conjunction as $\forall z.(A\to B\to z)\to z$); Language/Proposition embedding (Definitions 15–16); Theorem 18 (embedding of proofs); key distinction that propositions are types but not all types are propositions (only those convertible to `eps p` for `p : o`). : [[Embedding-Predicate-Logic-in-a-Logical-Framework|Link]]
- **4.3 Deduction modulo theory** — a theory is just its rewrite rules; comprehension schemes $\forall\vec{x}\exists c\,\forall y(y\in c \Leftrightarrow A)$ and their skolemized form, expressible via `i -> o` without a separate class sort; Heyting arithmetic example with nine rules including a **numberness** predicate `N` defined by an impredicative (second-order) rewrite rule. : [[Embedding-Predicate-Logic-in-a-Logical-Framework|Link]]
- **4.4 iProverModulo** — iProver as ordered-resolution-with-selection prover for classical predicate logic; clauses translated as multiary-disjunction Dedukti terms $\llbracket C\rrbracket$; one-way clauses simulate proposition rewrite rules, a Narrowing rule handles term rewrite rules; worked resolution/factoring example producing an explicit Dedukti derivation; scale note: 3383 TPTP problems, 38.1 MB gzipped output.

**Key Questions:**
1. Why is a separate universe `o` with an explicit `eps : o -> Type` embedding needed once you move past minimal predicate logic (with only $\Rightarrow,\forall$) to full connectives like $\wedge,\vee,\exists$, and why can't the $\lambda\Pi$-calculus express these directly as inductive/Cartesian-product types?
2. Walk through the second-order rewrite-rule definition of conjunction, `eps (and x y) --> z:o -> (eps x -> eps y -> eps z) -> eps z`. What proof-theoretic principle does this encode, and why does it make `eps` a *shallow* rather than *deep* embedding?
3. In the numberness rule for `N n` (line 760–763), what is being universally quantified over, and how does this rewrite rule encode mathematical induction without a primitive induction principle?

---

### Section 5: Classical Predicate Logic (pp. 17–21)

**Summary:** Addresses the fifth limitation from Section 1 — predicate logic's exclusively classical character — by distinguishing *classical connectives* ($\lor_c, \neg_c$, etc.) from *constructive* ones rather than attaching classicality to proofs. Introduces a new atom-embedding connective $\triangleright$ so the usual negative-translation trick (doubling negations before/after each connective) has somewhere to attach at the atomic level, avoiding the standard problem that atomic propositions need $\neg\neg P$ with no natural home for the negations. Section 5.3 covers Zenon/Zenon Modulo, a tableaux-based classical prover whose output — one Dedukti lemma per tableaux rule — has been validated against a 9,994-problem, 5.5 GiB benchmark from the B Method.

**Key Definitions & Concepts by Section:**
- **5.1 Classical connectives and quantifiers** — three-category syntax (terms/atoms/propositions) with an explicit atom-to-proposition connective $\triangleright$; classical versions defined via Kolmogorov-style double negation: $\triangleright_c A = \neg\neg\triangleright A$, $A\wedge_c B = \neg\neg(A\wedge B)$, etc., all expressed in Dedukti as double-negated versions of the constructive connectives (`atom_c`, `top_c`, `not_c`, `and_c`, `or_c`, `imp_c`, `fa_s_c`, `ex_s_c`). : [[Classical-Logic-via-Double-Negation-Connectives|Link]]
- **5.2 Classical Deduction modulo theory** — translating a classical Deduction-modulo rewrite rule directly would create a critical pair between the rule and the $\triangleright_c \to \neg\neg\triangleright$ unfolding; the fix is to strip the two head negations from both sides of the rule before declaring it, i.e. use the *constructive* head connective on both `l` and `r`. : [[Embedding-Predicate-Logic-in-a-Logical-Framework|Link]]
- **5.3 Zenon** — tableaux method with one-sided sequents; Theorem 21 (constructive/classical provability $\iff$ inhabitation of `eps |A|` / `eps |A|_c`); Zenon Modulo produces a term of type `eps (not_c |G|_c) -> eps bot`, converted to `eps |G|_c` via $\neg\neg\neg A\Rightarrow\neg A$ applied twice; one Dedukti lemma per tableaux rule (e.g. the `Ror` lemma for $\vee_c$-elimination); scale note: B Method benchmark, 595 MB gzipped output; ~50 B-Method set-theory axioms turned into rewrite rules.

**Key Questions:**
1. Why does attaching classicality to *connectives* rather than to *proofs* let constructive and classical reasoning coexist in a single mixed logic, and what does it mean for $\forall x\,(\triangleright x\in\{y,z\}\Leftrightarrow\dots)$ and its subscripted-$c$ counterpart to be genuinely different propositions?
2. Why does directly declaring the negative-translated form of a classical Deduction-modulo rewrite rule create a critical pair with the connective's own double-negation unfolding, and why does removing the head negations from both sides resolve it without losing classical validity?
3. Why does a proof of `eps (not_c |G|_c) -> eps bot` need exactly two applications of $\neg\neg\neg A \Rightarrow \neg A$ to become a proof of `eps |G|_c`, given that `|G|_c` itself already starts with a negation?

---

### Section 6: Simple Type Theory (pp. 21–22)

**Summary:** Shows two routes to embedding Simple type theory (Higher-order logic): via Deduction modulo theory (Section 4.3) or directly as a Pure type system (Section 8.1); develops the direct route, representing the (finitely many, but here type-indexed) simple types as Dedukti terms of a type `type`, rather than declaring infinitely many `Type`-level symbols, and connects this to HOL Light proof-checking via the HOLiDe translator.

**Key Definitions & Concepts by Section:**
- **6.1 Expressing simple type theory** — `type : Type`, base types `o`/`i`, `arrow`, indexed `term : type -> Type` with `term (arrow a b) --> term a -> term b`; term embedding (Definition 22) mapping variables, `imp`, `forall`, application and $\lambda$-abstraction; `eps : term o -> Type` with rewrite rules unfolding `imp`/`forall`; Theorem 23: provability in Simple type theory $\iff$ existence of an inhabiting Dedukti term, with the term a straightforward encoding of the original proof tree. : [[Simple-Type-Theory-and-Pure-Type-Systems|Link]]
- **6.2 HOL Light proofs** — extending the embedding to classical variants like Q0 (equality-as-primitive); HOLiDe translator building on the Open Theory project, handling prenex polymorphism, constant/type definitions; scale note: 10 MB OpenTheory library $\to$ 21.5 MB gzipped Dedukti library.

**Key Questions:**
1. Why does Simple type theory's finite-but-many simple types force a representation as *terms* of a `type` type (indexing a single `term` and `forall` symbol) rather than declaring one `Type`-level symbol per simple type, and how does the rewrite rule `term (arrow a b) --> term a -> term b` bridge the two levels?
2. What must HOLiDe additionally handle (beyond the core embedding of Section 6.1) to check real HOL Light libraries, and why do prenex polymorphism and type definitions matter for that?

---

### Section 7: Programming Languages (pp. 22–28)

**Summary:** Because rewriting is Turing-complete, the same framework can embed programming languages' operational semantics, giving proofs of program properties (not proofs about resource usage, since the embeddings are shallow). Works through the untyped $\lambda$-calculus with an explicit fixpoint operator, Abadi–Cardelli's $\varsigma$-calculus for object-oriented programming (introducing the *preobject* technique for partially-constructed, dependently-typed records), ML's pattern matching (via per-constructor *destructors*) and general recursion (via a call-freezing `@` operator), and finally FoCaLiZe, a certified-programming environment whose proofs are largely discharged by Zenon Modulo, with non-first-order obligations (like induction principles) instantiated directly in embedded Dedukti code.

**Key Definitions & Concepts by Section:**
- **7.1 Lambda-calculus** — `Term`, `lam`, `app` with $\beta$-rule `app (lam f) t --> f t`; discussion of why non-terminating rewrite systems (from preserving program reduction) don't break Dedukti's soundness, since soundness depends only on product compatibility (Lemma 7), not termination — termination is only needed where types themselves depend on non-terminating terms; worked `fix`/`mod2` example with the `#CONV` directive for checking convertibility. : [[Lambda-Pi-Calculus-and-Its-Typing-Judgments|Link1]], [[The-Lambda-Pi-Calculus-Modulo-Theory|Link2]]
- **7.2 The ς-calculus** — Obj₁ (Abadi–Cardelli), records-of-methods with self-binding $\varsigma$ binders; **preobject** technique (`Preobj A B`, `prenil`, `precons`) to represent partially-built objects as dependently-typed lists, since a sublist of a well-typed object is not itself well-typed under a naive representation; `mem` as an inductive membership relation driving structural recursion for `preselect`/`preupdate`; Lemma 25: the encoding preserves binding, typing, and operational semantics. : [[Embedding-Programming-Languages|Link]]
- **7.3 ML** — arity-one constructors (via tupling); **destructors** (Definition 26) generalizing if-then-else per constructor, giving semantics-preserving pattern matching (Lemma 27) without complex match-compilation; the `@` operator freezing evaluation of recursive calls until an argument is headed by a constructor, avoiding spurious non-termination on open terms (Lemma 28).
- **7.4 FoCaLiZe** — ML implementation language + classical predicate-logic specification language + static OO features; `mod2`/`twice` worked example with induction (`nat_induction`) instantiated by writing the Dedukti proof term directly (`dedukti proof {* ... *}`) since Zenon Modulo cannot instantiate non-first-order statements; scale note: >98% of the FoCaLiZe standard library checked, 1.89 MB gzipped.

**Key Questions:**
1. Why does Dedukti's soundness not depend on the termination of the rewrite system embedding a programming language's reduction, and under exactly what condition (types depending on non-terminating terms) can this become a real problem in practice?
2. What problem does the *preobject* representation solve that a plain dependently-typed list of methods could not, and how does the `Preobj A B` two-type-parameter design track "how much of the object has been built so far"?
3. Why can FoCaLiZe's own prover (Zenon Modulo) not discharge the `nat_induction` proof obligation, and what does it mean to "write the instantiation directly in Dedukti" as a workaround?

---

### Section 8: The Calculus of Inductive Constructions with Universes (pp. 28–32)

**Summary:** Extends the framework to Pure type systems in general (Section 8.1, with the Calculus of Constructions as the running example), then to inductive types via constructors plus a primitive elimination/recursion operator in the style of Gödel's System T (Section 8.2), and finally to cumulative universe hierarchies with explicit lifting operators to preserve unique term representations under cumulativity (Section 8.3). Section 8.4 reports on Matita library translation via the Krajono tool, noting that proof irrelevance — used by Matita but not yet expressible in Dedukti — limits full coverage.

**Key Definitions & Concepts by Section:**
- **8.1 Pure type systems** — a PTS specification $(S,A,R)$ embedded via per-sort universes `U_s`/`e_s`, per-axiom `u_s1 : U_s2` with `e_s2 u_s1 --> U_s1`, per-rule `pi_s1s2` dependent-product formers with unfolding rewrite rules; term/type embedding (Definition 29); Lemma 30 (preservation of computation), Lemma 31 (preservation of typing), Lemma 32 (conservativity/adequacy), Theorem 33 (equivalence of provability); worked Calculus of Constructions instantiation with a concrete derivation example. : [[Inductive-Types-and-Universe-Hierarchies|Link1]], [[Simple-Type-Theory-and-Pure-Type-Systems|Link2]]
- **8.2 Inductive types** — constructors (`nil`, `cons`) plus a primitive-recursion eliminator `elim_list`, parameterized by the motive `P` and computation rules reducing the eliminator when applied to each constructor; worked `append` definition via `elim_list`; noted that the full Calculus of Inductive Constructions needs infinitely many rules but any single proof only invokes finitely many. : [[Inductive-Types-and-Universe-Hierarchies|Link]]
- **8.3 Universes** — infinite cumulative hierarchy $U_0 \subseteq U_1 \subseteq \cdots$ via the typing rule $\Gamma\vdash M:U_i \Rightarrow \Gamma\vdash M:U_{i+1}$; indexing `U`, `eps`, `u`, `pi` by natural numbers rather than declaring one variable per universe level; explicit **lift** operators $\uparrow_i$ (since $U_i$ cannot be identified with $U_{i+1}$, as $U_i$ itself is not a member of $U_i$); the multiple-representation problem for a single semantic type (`lift i (pi i A B)` vs. `pi (S i) (lift i A) (...)`) and the extra rewrite rule needed to force a canonical representation.
- **8.4 Matita proofs** — Coq's library not directly checkable (modules, universe polymorphism not yet expressed); Matita's Calculus of Constructions-with-universes-and-proof-irrelevance library translated by Krajono for files avoiding explicit proof irrelevance; scale note: 1.11 MB gzipped arithmetic library. : [[Inductive-Types-and-Universe-Hierarchies|Link]]

**Key Questions:**
1. In the Pure type system embedding, why is a separate pair `U_s`/`e_s` needed per sort, and how do the axiom- and rule-indexed families `u_s1` and `pi_s1s2` reconstruct the PTS's typing judgments for sorts and products respectively?
2. Why can't universe cumulativity be implemented by simply identifying $U_i$ with $U_{i+1}$, and what specific failure (multiple representations of the same semantic type) does introducing explicit `lift` operators create, and how is it repaired?
3. What exactly does the `elim_list` eliminator's type express about the relationship between a base case, an inductive step, and the final conclusion, and how do the two computation rules make this an actual (not just postulated) recursion principle?

---

### Section 9: Contributions (pp. 32–33)

**Summary:** A historical attribution section tracing the framework's lineage — from Cousineau and Dowek's 2007 introduction of the $\lambda\Pi$-calculus modulo theory, through three successive Dedukti implementations (Boespflug, Carbonneaux, Saillard), to the individual theses and papers that added each embedding (Assaf for STT/CIC, Burel for iProverModulo, Halmagrand/Gilbert/Cauderlier for classical logic, Cauderlier for FoCaLiZe).

**Key Definitions & Concepts by Section:**
- Flat list (no natural subsections): the paper traces authorship of the $\lambda\Pi$-calculus modulo theory (Cousineau–Dowek 2007), the three Dedukti implementations (Boespflug 2008–2011, Carbonneaux 2012, Saillard 2012–2015), the first Calculus of Inductive Constructions expression (Boespflug–Burel 2011), the Simple type theory/CIC expression and HOL Light/Matita translations (Assaf 2012–2015), the HOLiDe graphical front-end (Wang 2015), iProverModulo's Dedukti output (Burel 2013), Zenon Modulo's Dedukti output (Halmagrand), classical connectives without axioms (Halmagrand, Gilbert, Cauderlier), and the FoCaLiZe/program-properties direction (Cauderlier, from 2013).

**Key Questions:**
1. Which single 2007 result underlies essentially every later embedding described in Sections 4–8, and what did it originally establish about Pure type systems?

---

### Section 10: Conclusion and Future Work (pp. 33–34)

**Summary:** Summarizes the five translated libraries and their sizes as evidence that the approach scales, then lays out future directions: expressing more proof sources (Coq, PVS, SMT solvers), reverse-engineering existing proofs to find the weakest theory that actually proves them (noting many "classical" HOL Light proofs are in fact constructive, and many Matita proofs don't need the full power of CIC-with-universes), and ultimately reframing the field's central question from "what is a good system to express mathematics?" to "which definitions, axioms, and rewrite rules are needed to prove which theorem?"

**Key Definitions & Concepts by Section:**
- Flat list: library-size summary table (iProverModulo/TPTP 38.1 MB, Zenon Modulo/B Set Theory 595 MB, Focalide 1.89 MB, Holide 21.5 MB, Matita arithmetic 1.11 MB); reverse engineering of proofs as identifying minimal sufficient theories; combining lemmas across systems via a shared logical framework as the long-term interoperability goal.

**Key Questions:**
1. In what sense is "reverse engineering" a proof — as the paper uses the term for the HOL Light and Matita libraries — a mechanizable question, and why does having a single logical framework with rewrite-rule-expressed theories make that question tractable in a way it wouldn't be if each proof stayed inside its native system?
2. How does the paper's closing reframing ("which definitions, axioms and rewrite rules are needed to prove which theorem?") follow directly from treating a *theory* as nothing more than a finite set of declarations and rewrite rules in a shared context, as set up back in Section 2.2.4?

---
