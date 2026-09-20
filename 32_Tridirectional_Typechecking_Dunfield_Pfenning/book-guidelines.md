# Tridirectional Typechecking — Guidelines

## Header

**Title:** Tridirectional Typechecking
**Author(s):** Jana Dunfield and Frank Pfenning (Carnegie Mellon University)
**Publication:** POPL '04, January 14–16, 2004, Venice, Italy

**Brief Summary:**
This paper gives a decidable, bidirectionally-inspired formulation of a rich pure type-assignment system (from the authors' prior work) that includes intersections, unions, and universally/existentially quantified index-refined dependent types. Because unions and existential quantification require visiting subterms in evaluation position before the surrounding context, the resulting system needs a "third direction" beyond checking and synthesis — a tridirectional system — and completeness with respect to the original type-assignment system requires a new device, contextual typing annotations, adapted from the study of principal typings.

**Intent of the Author:**
The authors want to make their earlier, inherently undecidable pure type-assignment system for refinement types practically checkable, by developing an annotation discipline and typechecking algorithm that is provably sound, complete, and decidable — closing the gap between rich program-property type systems and programmer-usable typecheckers.

**Intended readership:** researchers and language implementors familiar with type theory, natural deduction/sequent calculus, and prior work on refinement and intersection/union types; this is a dense, rule-heavy conference paper.

---

## Topic List

1. **Bidirectional Typechecking Design Principles** : [[Bidirectional-Typechecking-Design-Principles|Link]]
   - Checking versus synthesis judgments
   - Avoiding unification via mode-correct rules : [[Related-Work-on-Refinement-Intersection-and-Union-Types|Link]]
   - Introduction rules as checking and elimination rules as synthesis
   - The subsumption rule bridging synthesis and checking
2. **The Core Language and Its Bidirectional Typing** : [[The-Core-Language-and-Its-Bidirectional-Typing|Link]]
   - Syntax and call-by-value operational semantics : [[The-Core-Language-and-Its-Bidirectional-Typing|Link]]
   - Products units functions and datatypes
   - Evaluation contexts : [[Indefinite-Property-Types-and-the-Third-Direction|Link1]], [[The-Core-Language-and-Its-Bidirectional-Typing|Link2]], [[The-Left-Tridirectional-System|Link3]]
   - Alternative bidirectional formulations : [[The-Core-Language-and-Its-Bidirectional-Typing|Link]]
3. **Definite Property Types** : [[Definite-Property-Types|Link]]
   - Intersection types and the value restriction : [[Definite-Property-Types|Link]]
   - The greatest type as a nullary intersection : [[Definite-Property-Types|Link]]
   - Refined datatypes and datasorts : [[Definite-Property-Types|Link]]
   - Index refinements and constraint domains : [[Related-Work-on-Refinement-Intersection-and-Union-Types|Link]]
   - Dependent products over index variables : [[Definite-Property-Types|Link]]
4. **Indefinite Property Types and the Third Direction** : [[Indefinite-Property-Types-and-the-Third-Direction|Link]]
   - Union types and their elimination via evaluation contexts : [[Indefinite-Property-Types-and-the-Third-Direction|Link]]
   - The empty or void type
   - Existential dependent sum types over indices
   - The direct rule as the unary indefinite elimination
   - Why the third direction is needed for typechecking : [[Bidirectional-Typechecking-Design-Principles|Link]]
5. **Contextual Typing Annotations** : [[Contextual-Typing-Annotations|Link]]
   - The problem of checking against intersections : [[Definite-Property-Types|Link]]
   - Index variable scoping inside annotations : [[Contextual-Typing-Annotations|Link]]
   - Comma-separated alternative annotations : [[The-Core-Language-and-Its-Bidirectional-Typing|Link1]], [[Contextual-Typing-Annotations|Link2]]
   - Contextual subtyping : [[Contextual-Typing-Annotations|Link]]
   - Term extension and light extension : [[Contextual-Typing-Annotations|Link]]
   - Monotonicity under annotation : [[Contextual-Typing-Annotations|Link]]
6. **Soundness and Completeness of the Simple Tridirectional System** : [[Soundness-and-Completeness-of-the-Simple-Tridirectional-System|Link]]
   - Soundness via erasure to the type-assignment system : [[Soundness-and-Completeness-of-the-Simple-Tridirectional-System|Link]]
   - Synthesizing form and extension of a term : [[Soundness-and-Completeness-of-the-Simple-Tridirectional-System|Link]]
   - The completeness theorem and its corollary : [[Soundness-and-Completeness-of-the-Simple-Tridirectional-System|Link]]
7. **The Left Tridirectional System** : [[The-Left-Tridirectional-System|Link]]
   - Linear contexts and linear variables : [[The-Left-Tridirectional-System|Link]]
   - The directL rule as the sole source of linearity : [[The-Left-Tridirectional-System|Link]]
   - Left rules replacing contextual rules
   - Soundness and completeness relative to the simple tridirectional system : [[Soundness-and-Completeness-of-the-Simple-Tridirectional-System|Link]]
   - Decidability of left tridirectional typing : [[The-Core-Language-and-Its-Bidirectional-Typing|Link1]], [[The-Left-Tridirectional-System|Link2]]
   - Type safety via composition with the type-assignment system : [[The-Left-Tridirectional-System|Link]]
8. **Related Work on Refinement Intersection and Union Types** : [[Related-Work-on-Refinement-Intersection-and-Union-Types|Link]]
   - Datasort refinement and the refinement restriction : [[Definite-Property-Types|Link1]], [[Related-Work-on-Refinement-Intersection-and-Union-Types|Link2]]
   - The value restriction on intersection introduction : [[Definite-Property-Types|Link1]], [[Related-Work-on-Refinement-Intersection-and-Union-Types|Link2]]
   - Index refinements and elaboration of existential scope : [[Related-Work-on-Refinement-Intersection-and-Union-Types|Link]]
   - Local type inference and partial inference strategies : [[Related-Work-on-Refinement-Intersection-and-Union-Types|Link]]
   - Principal typings : [[Related-Work-on-Refinement-Intersection-and-Union-Types|Link]]

---

## Chapter Summaries

### Section 1: Introduction (p. 1)

**Summary:** Motivates the paper by recalling the authors' prior undecidable pure type-assignment system for property types, explains why simple bidirectional checking is insufficient for unions and existential quantification, and previews the tridirectional system, contextual typing annotations, and the left tridirectional decidability result.

**Key Definitions & Concepts:**
- Pure type assignment system — a system (from prior work) where terms carry no types at all, encompassing intersections, unions, and quantified dependent (index-refined) types; inherently undecidable.
- Tridirectional system — extends bidirectional (synthesis/checking) typing with a third capability: visiting a subterm in evaluation position, synthesizing its type, before analyzing the surrounding expression.
- Contextual typing annotation — an annotation of the form $(e : \Gamma_1 \vdash A_1, \ldots, \Gamma_n \vdash A_n)$, allowing several context/type pairs, introduced to recover completeness in the presence of intersections and quantifier scoping.

**Key Questions:**
1. Why does the presence of union and existential types force a "third direction" beyond simple bidirectional checking?
2. What two ideas does the paper use to establish decidability despite this added nondeterminism?

---

### Section 2: The Core Language (pp. 2–3)

**Summary:** Establishes the base bidirectional type system — syntax, call-by-value operational semantics, and the design principle that introduction forms are checked while elimination forms synthesize — before property types are layered on top in later sections.

**Key Definitions & Concepts:**
- Synthesis judgment $e \uparrow A$ and checking judgment $e \downarrow A$ — the two core bidirectional judgments; mode correctness (borrowed from logic programming) requires that a rule's conclusion type be fully determined by its premises for synthesis, and known in advance for checking.
- Subsumption rule (sub) — bridges the two directions: if $e \uparrow A'$ and $A' \le A$ then $e \downarrow A$.
- Evaluation context $E$ — a term with a hole, used to describe where reduction may occur; central to later union/existential elimination rules.
- Mode correctness principle — introduction rules (constructors) are checked; elimination rules (destructors) synthesize, following Curry-Howard.

**Key Questions:**
1. Why is avoiding unification described as "fundamental to the design" of this bidirectional system, and what two motivations does the paper give?
2. How does the subsumption rule (sub) let the system incorporate subtyping without complex constraint management?

---

### Section 3: Property Types (pp. 3–5)

**Summary:** Extends the core language with "definite" property types — intersections, the greatest type $\top$, refined datatypes indexed by a constraint domain, and universal dependent products $\Pi$ — each given bidirectional introduction and elimination rules following the logical principle established in Section 2.

**Key Definitions & Concepts by Section:**
- **3.1 Intersections** — $A \wedge B$: introduction checks a value against both $A$ and $B$ (value-restricted, due to unsoundness with mutable references); elimination synthesizes either conjunct. : [[Definite-Property-Types|Link]]
- **3.2 Greatest Type** — $\top$ as the 0-ary form of intersection; no elimination or left subtyping rule. : [[Definite-Property-Types|Link]]
- **3.3 Refined Datatypes** — datasorts $\delta$ refining datatypes; index refinements $\delta(i)$; the entailment relation $\Gamma \models P$; the datasort subtyping relation $\sqsubseteq$; unreachable case arms detected via $\Gamma \models \bot$; the dependent product $\Pi a{:}\gamma. A$ over index variables. : [[Definite-Property-Types|Link]]
- **3.4 Indefinite Property Types** (transitional, leading into Section 3.6) — motivating example: `filter`'s indeterminate result length, requiring existential $\Sigma a{:}\gamma. A$.

**Key Questions:**
1. Why must the intersection introduction rule $(\wedge I)$ be restricted to values rather than arbitrary expressions?
2. How does the constraint domain's entailment judgment $\Gamma \models P$ let the system avoid typechecking statically-unreachable case arms?

---

### Section 3 (continued): Indefinite Property Types and the Tridirectional Rule (pp. 5–6)

**Summary:** Introduces union types, the void type, and existential dependent sums as "indefinite" property types whose elimination cannot proceed by simple structural decomposition, motivating the (direct)/(∨E)/(⊥E)/(ΣE) rules that require decomposing a term into an evaluation context and a synthesizing subterm — the paper's namesake "third direction."

**Key Definitions & Concepts:**
- Union type $A \vee B$ — introduction checks against either disjunct; elimination $(\vee E)$ requires finding an evaluation context $E$ around a subterm $e'$ that synthesizes $A \vee B$, then checking $E[x]$ and $E[y]$ against $C$ under both hypotheses.
- Void/empty type $\bot$ — the 0-ary indefinite type, no introduction rules; elimination $(\bot E)$ analogous to $(\vee E)$.
- Existential dependent sum $\Sigma a{:}\gamma. A$ — introduction via the analysis judgment; elimination $(\Sigma E)$ again requires an evaluation-context decomposition.
- The rule (direct) — the unary version of $(\vee E)$/$(\bot E)$, considered "the tridirectional rule"; shown not to be admissible via a worked `append`/`filterpos` counterexample.

**Key Questions:**
1. Why is rule (direct) not admissible, and what does the `append [42] (filterpos [...])` example demonstrate about needing to move to a subterm's evaluation position?
2. In what sense do the union, void, and existential elimination rules all follow "the third direction," compared to the purely structural elimination rules of Section 3 (intersection, $\Pi$)?

---

### Section 4: Contextual Typing Annotations (pp. 6–8)

**Summary:** Identifies two subtle problems with naive type annotations — checking a single annotated subterm against an intersection's several conjuncts, and index variable scoping inside annotations — and solves both with contextual typing annotations, a generalized notion of annotation carrying its own local context, together with a contextual subtyping relation used to validate them; proves soundness and completeness of the resulting system.

**Key Definitions & Concepts by Section:**
- **4.1 Checking Against Intersections** — the `cons42` example showing a single plain annotation cannot serve both conjuncts of an intersection type; motivates comma-separated alternative annotations $(e : A_1, A_2, \ldots)$ (following Pierce, Reynolds, Davies). : [[Definite-Property-Types|Link]]
- **4.2 Index Variable Scoping** — the `id` list-identity example showing a naive annotation would violate $\alpha$-conversion of bound index variables. : [[Contextual-Typing-Annotations|Link]]
- **4.3 Contextual Subtyping** — annotations of the form $(e : \Gamma_1 \vdash A_1, \ldots, \Gamma_n \vdash A_n)$; the contextual subtyping relation $\rhd$ (contravariant in contexts); rule (ctx-anno); Lemma 1 and Corollary 2 (reflexivity of $\rhd$). : [[Contextual-Typing-Annotations|Link]]
- **4.4 Soundness** — Theorem 3 (Soundness, Tridirectional): erasure of annotations from a tridirectional derivation yields a type-assignment derivation.
- **4.5 Completeness** — Definitions of synthesizing form, term extension $e' \sqsupseteq e$, light extension $e' \sqsupseteq_\ell e$; Lemma 10 (Monotonicity under Annotation); Theorem 11 (Completeness, Tridirectional) and Corollary 12. : [[Soundness-and-Completeness-of-the-Simple-Tridirectional-System|Link]]

**Key Questions:**
1. Why does the `cons42` example show that even comma-separated plain type annotations $(e : A, B)$ are insufficient, and why does adding contexts to each alternative (contextual annotations) fix this?
2. Why must reflexivity of the contextual subtyping relation $\rhd$ (Corollary 2) hold for the completeness proof to go through, given that requiring the programmer to write out an entire context verbatim would be impractical?
3. What does the failure of naive monotonicity ("if $e \downarrow A$ and $e' \sqsupseteq e$ then $e' \downarrow A$") for `(() : (⊢ ⊤))` versus `()` reveal about how annotation lists must be used?

---

### Section 5: The Left Tridirectional System (pp. 8–11)

**Summary:** Replaces the highly nondeterministic contextual rules of the simple tridirectional system with a single (directL) rule plus several left rules operating on a linear context of freshly-introduced linear variables, then proves this "left tridirectional system" sound and complete relative to the simple system, decidable, and (by composition with prior results) type safe.

**Key Definitions & Concepts by Section:**
- **(intro)** — linear context $\Delta$; linear variables appearing exactly once, in evaluation position, in a term; rule (directL) as the sole source of linearity, replacing (direct); left rules $(\vee L)$, $(\bot L)$, $(\Sigma L)$, $(\wedge L_1/L_2)$, $(\Pi L)$.
- **5.1 Soundness** — Definition 17 (renaming); Theorem 18 (Soundness, Left Rule System), translating a left-tridirectional derivation back to a simple tridirectional one via renaming.
- **5.2 Completeness** — Lemma 19; Theorem 20 (Completeness, Left Rule System). : [[Soundness-and-Completeness-of-the-Simple-Tridirectional-System|Link]]
- **5.3 Decidability of Typing** — Theorem 21, proved via a lexicographic ordering on term size, judgment direction, and type-constructor counts in the linear context.
- **5.4 Type Safety** — combines Theorem 18 (soundness of left system), Theorem 3 (soundness of tridirectional system), and prior work's Type Preservation and Progress to conclude that a well-typed left-tridirectional program either diverges or evaluates to a value of the expected type. : [[The-Left-Tridirectional-System|Link]]

**Key Definitions:**
- Linear context $\Delta$ — tracks variables that must appear exactly once, in evaluation position, in the term being typed.
- The judgment $\Delta \sqsubset e$ / $\Delta \Subset e$ — formalize "linear variables appear exactly once, in evaluation position."

**Key Questions:**
1. Why is (directL) — unlike (direct) — restricted so that the subterm being "brought out" cannot itself be a linear variable, and what problem would arise without this restriction?
2. How does the induction measure in Theorem 21 handle the fact that a synthesis judgment's type can grow larger across a rule application while still guaranteeing termination?
3. How do Theorems 18, 3, and prior Type Preservation/Progress results compose to give type safety for the left tridirectional system (Section 5.4)?

---

### Section 6: Related Work (p. 11)

**Summary:** Situates the paper relative to prior work on datasort refinements, intersection/union type assignment, index refinements, local type inference, and principal typings, highlighting where the tridirectional approach admits strictly more programs or takes a different technical path.

**Key Definitions & Concepts:**
- Datasort refinement (Freeman and Pfenning) — full type inference decidable under the "refinement restriction," using abstract-interpretation techniques.
- Value restriction on intersection introduction (Davies and Pfenning) — first addressed effects in call-by-value soundly.
- Local type inference (Pierce and Turner) — a bidirectional partial-inference strategy for subtyping and impredicative polymorphism; contrasted with this paper's avoidance of nonlocal unification for type arguments.
- Principal typing (Jim; Wells) — a pair $(\Gamma, A)$ representing all valid typing pairs for a term; the paper's contextual typing annotations echo the idea of assigning a "typing" rather than a single type.

**Key Questions:**
1. How does the paper's tridirectional system admit strictly more programs than Xi's let-normal-form translation approach to index refinement scoping, according to the authors?
2. In what sense do contextual typing annotations "appear in our system" as an analogue of principal typings, according to the discussion?

---

### Section 7: Conclusion (p. 11)

**Summary:** Summarizes the paper's transformation of an undecidable pure type-assignment system into a decidable tridirectional one via contextual annotations, and outlines future work on a let-normal left tridirectional system and a prototype implementation to evaluate practical annotation burden and typechecking efficiency.

**Key Definitions & Concepts:**
- (No new formal definitions; summarizes contributions and outlines a planned let-normal variant of the left tridirectional system to further reduce nondeterminism in (directL).)

**Key Questions:**
1. What three practical questions do the authors identify as needing empirical answers once a prototype implementation exists?
