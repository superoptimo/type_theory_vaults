# Elaboration in Dependent Type Theory — Guidelines

## Header

**Title:** Elaboration in Dependent Type Theory
**Author(s):** Leonardo de Moura, Jeremy Avigad, Soonho Kong, and Cody Roux
**Publication:** arXiv:1505.04324v2 [cs.LO], December 18, 2015

**Brief Summary:**
This paper describes the elaboration algorithm implemented in the Lean theorem prover — the process of turning a partially specified, quasi-formal user expression into a fully specified, type-correct term of dependent type theory. It surveys the outward-facing tasks the elaborator must perform (type/implicit-argument inference, higher-order unification, respecting computational reduction, type class inference, ad hoc overloading, coercions, and tactic integration), and then presents the internal algorithm — data structures, a constraint-simplification procedure, a preprocessing phase, and a nonchronological-backtracking constraint solver — that carries them out together as one unified constraint-solving problem.

**Intent of the Author:**
The authors aim to fill an expository gap: elaboration algorithms for dependent type theory are used in practice but rarely documented in the literature, making the subject "something of a dark art." They want to describe the problem clearly, present Lean's working solution, and explain the design choices that balance completeness, efficiency, and usability.

---

## Topic List

1. **The Elaboration Task** : [[The-Elaboration-Task|Link]]
   - Elaboration as passing from a partial expression to a fully specified term
   - Type inference and implicit arguments
   - Placeholders and underscore-inferred arguments
   - Generalizing Hindley–Milner type inference to dependent types
2. **Higher-Order Unification** : [[Higher-Order-Unification|Link]]
   - First-order vs. higher-order unification problems in implicit argument synthesis
   - Undecidability of second-order unification : [[Higher-Order-Unification|Link]]
   - Inferring substitution contexts and induction predicates
   - Miller patterns : [[Higher-Order-Unification|Link]]
   - Huet's unification algorithm : [[Higher-Order-Unification|Link]]
   - Imitation and projection case splits
   - Quasi-patterns and reduced case-split search
3. **Computational Behavior and Reduction** : [[Computational-Behavior-and-Reduction|Link]]
   - Definitional equality and $\beta$/$\iota$-reduction : [[Computational-Behavior-and-Reduction|Link]]
   - Weak head normal form and stuck terms : [[Computational-Behavior-and-Reduction|Link]]
   - Unfolding of defined constants during elaboration
   - Reducibility annotations: irreducible, reducible, semireducible
   - Definition depth and delta-constraint unfolding heuristics
4. **Type Classes and Class Inference** : [[Type-Classes-and-Class-Inference|Link]]
   - Haskell-style type classes in a dependently typed setting
   - Instance declarations and backward-chaining Prolog-like search
   - The algebraic hierarchy via structure extension
   - Fully bundled structures and coercion-based projection : [[Type-Classes-and-Class-Inference|Link]]
   - The decidable class and constructive/classical interplay
   - Ondemand choice constraints for class resolution : [[Constraints-and-Justifications|Link1]], [[Tactics-and-Proof-Structuring|Link2]]
5. **Overloading and Coercions** : [[Overloading-and-Coercions|Link]]
   - Ad hoc polymorphism versus parametric polymorphism
   - Notation and identifier overloading across namespaces
   - Namespace disambiguation
   - Coercion between families of types : [[Overloading-and-Coercions|Link]]
   - Coercion to the class of sorts
   - Coercion to the class of function types : [[Overloading-and-Coercions|Link]]
6. **Tactics and Proof Structuring** : [[Tactics-and-Proof-Structuring|Link]]
   - Tactic blocks interleaved with term-mode expressions
   - The have and show structuring keywords : [[Tactics-and-Proof-Structuring|Link]]
   - Local surgical tactics versus global constraint-based elaboration
   - Sectioning long proof terms into independent elaboration problems
7. **Term Representation and Core Data Structures** : [[Term-Representation-and-Core-Data-Structures|Link]]
   - Locally nameless variable representation : [[Term-Representation-and-Core-Data-Structures|Link]]
   - De Bruijn indices for bound variables
   - Metavariables as holes with unique identifiers and types
   - Closed-term-only metavariable assignment : [[Term-Representation-and-Core-Data-Structures|Link]]
   - Environments, declarations, and constants : [[Term-Representation-and-Core-Data-Structures|Link]]
8. **Constraints and Justifications** : [[Constraints-and-Justifications|Link]]
   - Unification constraints versus choice constraints
   - Asserted, assumption, and join justifications : [[Constraints-and-Justifications|Link]]
   - Substitutions as metavariable assignments with justification tracking : [[Constraints-and-Justifications|Link]]
   - Regular versus ondemand choice constraints : [[Constraints-and-Justifications|Link]]
9. **The Constraint Simplification Procedure** : [[The-Constraint-Simplification-Procedure|Link]]
   - The simp procedure for decomposing unification constraints
   - Constraint categories: delta, pattern, quasi-pattern, flex-rigid, flex-flex, recursor : [[Higher-Order-Unification|Link]]
   - Symmetric case elision in the simp pseudocode
10. **The Preprocessing Phase** : [[The-Preprocessing-Phase|Link]]
    - Converting preterms to terms with metavariables and constraints
    - ensurefun and function-type inference
    - Coercion insertion during application elaboration
    - Implicit-argument metavariable creation
11. **The Constraint Solving Procedure** : [[The-Constraint-Solving-Procedure|Link]]
    - Priority queue ordering over constraint categories : [[The-Constraint-Solving-Procedure|Link]]
    - The metavariable-to-constraint mapping U
    - Nonchronological backtracking and case-split stacks : [[The-Constraint-Solving-Procedure|Link]]
    - Pure data structures for constant-time state copies
    - The visit, resolve, and process procedures : [[The-Constraint-Solving-Procedure|Link]]
12. **Performance and Implementation Optimizations** : [[Performance-and-Implementation-Optimizations|Link]]
    - Cost of the locally nameless approach
    - Bound tracking to optimize instantiate
    - Free-variable bits to optimize abstract
    - Compilation time comparison with and without optimizations
13. **Related Work and Positioning** : [[Related-Work-and-Positioning|Link]]
    - Miller-style pattern unification and pruning : [[Higher-Order-Unification|Link]]
    - Dependency erasure and first-order approximation in Coq's unifier
    - Type classes and canonical structures in Coq and Matita : [[Related-Work-and-Positioning|Link]]
    - Axiomatic type classes and locales in Isabelle : [[Related-Work-and-Positioning|Link1]], [[Type-Classes-and-Class-Inference|Link2]]
    - Elaboration via theorem-proving analogy in Idris : [[Related-Work-and-Positioning|Link]]

---

## Chapter Summaries

### Section 1: Introduction (p. 1)

**Summary:** Introduces the Lean theorem prover and its dependent type theory foundation, framing elaboration as the process of resolving implicit information in quasi-formal mathematical expressions, and previews the paper's structure.

**Key Definitions & Concepts:**
- Elaboration — the process of passing from a quasi-formal, partially-specified expression to a completely precise, formal term.
- Propositions-as-types paradigm — using a single dependent type theory to express both function definitions and proofs.
- Lean — the interactive theorem prover whose elaborator is described, based on the Calculus of Inductive Constructions with Universes.

**Key Questions:**
1. Why does the paper describe elaboration as something of a "dark art," and what expository gap does the paper aim to fill?
2. In what sense does elaboration unify the tasks of writing definitions and writing proofs under propositions-as-types?

---

### Section 2: The Elaboration Task (pp. 2–12)

**Summary:** Surveys, from the outside, everything the elaborator must accomplish: type and implicit-argument inference, higher-order unification, respecting computational reduction, type class inference, overloading, coercions, and tactic integration — culminating in an example that combines all these features at once.

**Key Definitions & Concepts by Section:**
- **2.1 Type inference and implicit arguments** — implicit arguments (inferred via underscore or curly-bracket declaration), generalization of Hindley–Milner inference to dependent types.
- **2.2 Higher-order unification** — higher-order unification problem (inferring an element of a $\Pi$-type), Miller patterns as the well-behaved fragment, undecidability of second-order unification, examples via `subst`/induction/recursion needing inferred predicates. : [[Higher-Order-Unification|Link]]
- **2.3 Computational behavior** — definitional equality (e.g. $(\lambda x, t)\, s \equiv t[s/x]$), the three reducibility annotations (irreducible, reducible, semireducible) that control unfolding during elaboration only (not kernel type checking). : [[Computational-Behavior-and-Reduction|Link]]
- **2.4 Type classes** — `has_mul`-style class declarations, instance search as backward-chaining Prolog-like resolution, the algebraic hierarchy (semigroup, monoid, group), fully bundled structures, the `decidable` class bridging constructive and classical reasoning. : [[Related-Work-and-Positioning|Link1]], [[Type-Classes-and-Class-Inference|Link2]]
- **2.5 Overloading** — ad hoc polymorphism (overloaded notation/identifiers) versus parametric polymorphism (type classes); namespace-based disambiguation with `#<namespace>`. : [[Overloading-and-Coercions|Link]]
- **2.6 Coercions** — three kinds of coercions: between families of types, to the class of sorts, to the class of function types. : [[Overloading-and-Coercions|Link]]
- **2.7 Tactics and structuring mechanisms** — tactic blocks (`begin...end`, `by`), the `have`/`show` keywords, `proof...qed` for sectioning elaboration problems. : [[Tactics-and-Proof-Structuring|Link]]
- **2.8 Combining the various components** — an extended natural-transformation-composition example showing coercions, overloading, type class inference, and unification interacting in one term.

**Key Questions:**
1. Why is inferring the predicate in `subst e H` a genuinely higher-order unification problem rather than a first-order one, and why is such a solution inherently ambiguous?
2. What is the practical purpose of the irreducible/reducible/semireducible annotations, and why do they only matter to the elaborator and not the kernel type checker?
3. How does type class inference in Lean function as a backward-chaining Prolog-like search, and how does this let generic theorems about semigroups apply automatically to groups?

---

### Section 3: The Elaboration Procedure (pp. 12–24)

**Summary:** Presents the internal algorithm: term representation and data structures, support functions, a constraint simplification procedure (simp), the preprocessing phase that turns preterms into terms-with-constraints, and the constraint-solving procedure built on a priority queue and nonchronological backtracking, including a Huet-style treatment of flex-rigid constraints.

**Key Definitions & Concepts by Section:**
- **3.1 Overview** — the two main steps, preprocessing and constraint resolution, and their interaction with tactic invocation.
- **3.2 Main data structures** — the term grammar $t, s ::= \ell \mid x \mid f \mid ?m \mid \mathrm{Type}_u \mid t\,s \mid \lambda x{:}s, t \mid \Pi x{:}s, t$; locally nameless representation with de Bruijn indices; metavariables and closed-term-only assignment; unification constraints $\langle t \approx s, j\rangle$ and choice constraints $\langle ?m\,\ell : t \text{ in } f, j\rangle$; justifications (asserted, assumption, join); stuck terms (stuck application, stuck recursor). : [[Term-Representation-and-Core-Data-Structures|Link]]
- **3.3 Support functions** — `typeof`, `abstract`$_\lambda$/`abstract`$_\Pi$, `unfold` (δ-reduction), `whnf`, `ensurefun`, the dangling-bound-variable invariant, and the bound-tracking/free-variable-bit optimizations for `instantiate`/`abstract`.
- **3.4 The constraint simplification procedure** — the `simp` procedure and pseudocode; the six resulting constraint categories: delta, pattern, quasi-pattern, flex-rigid, flex-flex, recursor. : [[The-Constraint-Simplification-Procedure|Link]]
- **3.5 Preprocessing** — converting preterms into terms with metavariables and constraints; coercion insertion via `ensurefun`/`simp`; implicit-argument metavariable creation; ondemand choice constraints for class inference (a "simple $\lambda$-Prolog interpreter"). : [[The-Preprocessing-Phase|Link]]
- **3.6 The constraint solving procedure** — the priority queue $Q$ (with total order pattern ≺ ready ≺ regular ≺ delta ≺ quasi-pattern ≺ flex-rigid ≺ recursor ≺ postponed ≺ flex-flex), the metavariable-constraint map $U$, the case-split stack $C$, `visit`/`visiteq`/`visitchoice`, and the `resolve` error-backtracking procedure. : [[The-Constraint-Solving-Procedure|Link]]
- **3.7 Processing constraints** — the `process` procedure, handling of delta constraints via two-alternative lazy lists, Huet's algorithm adapted for flex-rigid constraints (imitation vs. projection case splits), heuristics for quasi-patterns, and the approximate treatment of recursor constraints. : [[The-Preprocessing-Phase|Link1]], [[The-Constraint-Solving-Procedure|Link2]]

**Key Questions:**
1. What is the division of labor between the preprocessing phase and the constraint-solving phase, and why does the paper say this division is "slightly too simplistic"?
2. How does nonchronological backtracking (via the case-split stack and justification tracking) let the solver avoid needlessly re-exploring parts of the search space after a failure?
3. In Huet's algorithm as adapted here, what are imitation and projection case splits, and why are two complications (unfolding of defined constants, and recursors) required beyond the classical algorithm?

---

### Section 4: Related Work and Conclusions (pp. 24–26)

**Summary:** Reports on Lean's standard and homotopy type theory libraries as evidence the algorithm works in practice, then compares the approach to Abel & Pientka's pruning-based pattern unification, Ziliani & Sozeau's Coq unifier (dependency erasure, first-order approximation), type-class mechanisms in Coq/Matita/Isabelle, and Brady's Idris elaborator, before summarizing the paper's contributions.

**Key Definitions & Concepts:**
- Pruning — Abel and Pientka's technique of removing metavariable arguments outside the Miller pattern fragment to find more unification solutions.
- Dependency erasure / first-order approximation — Ziliani and Sozeau's more aggressive unification heuristics in Coq, which trade uniqueness of solution for solvability.
- Locales / axiomatic type classes — Isabelle's simple-type-theory mechanisms for algebraic structures, contrasted with Lean's dependently typed approach.

**Key Questions:**
1. Why does the paper argue that representing algebraic structures depending on a parameter (e.g. integers modulo $m$) is difficult in Isabelle's simple type theory but natural in Lean's dependent type theory?
2. What tradeoff do Ziliani and Sozeau accept with dependency erasure and first-order approximation that Lean's backtracking-based approach avoids, and at what cost?
