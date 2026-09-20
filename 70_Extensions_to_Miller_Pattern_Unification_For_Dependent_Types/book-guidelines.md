# Extensions to Miller's Pattern Unification for Dependent Types and Records — Guidelines

## Header

**Title:** Extensions to Miller's Pattern Unification for Dependent Types and Records
**Author(s):** Andreas Abel, Brigitte Pientka
**Publication:** Mathematical Structures in Computer Science (journal); extended version of the TLCA 2011 conference paper "Higher-order dynamic pattern unification for dependent types and records" (Abel and Pientka, 2011). Received 2 May 2018.

**Brief Summary:**
The article gives a comprehensive, correctness-proven algorithm for higher-order pattern unification in the $\lambda\Pi\Sigma$-calculus, extending Miller's decidable pattern fragment to dependent function types, dependent pair (Σ) types, and an extensional unit type. Its central technical device is exploiting type isomorphisms — in particular $\Pi z:(\Sigma x{:}A.B).C \cong \Pi x{:}A.\Pi y{:}B.[(x,y)/z]C$ — to rewrite unification problems containing dependent records into equivalent problems containing only dependent function types, which the classical pattern algorithm can then solve. The algorithm is presented as an inference system of small constraint-rewriting steps (decomposition, η-contraction, lowering, pruning, flattening) and is proved to terminate, preserve solutions, and preserve well-typedness.

**Intent of the Author:**
The authors aim to give the first comprehensive, formally correct treatment of constraint-based higher-order pattern unification extended to dependent records — filling gaps left by earlier informal or non-terminating treatments (notably Dowek et al. 1996 and Reed 2009b) — so that real systems (Agda, Beluga) can rely on a provably correct unifier for practical dependent type reconstruction.

---

## Topic List

1. **Higher-Order Pattern Unification** : [[Higher-Order-Pattern-Unification|Link]]
   - The Miller pattern fragment : [[Higher-Order-Pattern-Unification|Link]]
   - Undecidability of full higher-order unification : [[Higher-Order-Pattern-Unification|Link]]
   - The dynamic pattern fragment and constraint postponement : [[Higher-Order-Pattern-Unification|Link]]
   - Unification as an inference system of rewrite rules on constraint sets : [[Constraint-Based-Unification-as-an-Inference-System|Link]]

2. **The λΠΣ-Calculus with Meta-Variables** : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]
   - Dependent function types and dependent pair types
   - Neutral terms, normal terms, and evaluation contexts
   - Meta-variables as closures under a suspended substitution : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]
   - Contextual objects and contextual types : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]
   - Rigid, flexible, and strongly rigid occurrences : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]
   - Hereditary substitution : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]
   - Meta-substitution : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]
   - Bidirectional typing for neutral and normal terms : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]

3. **Type Isomorphisms for Dependent Records** : [[Type-Isomorphisms-for-Dependent-Records|Link]]
   - The Sigma-Pi type isomorphism : [[Type-Isomorphisms-for-Dependent-Records|Link]]
   - Translating a record-typed function into a pair of functions
   - Flattening Σ-types in a meta-variable's context : [[Extension-to-the-Unit-and-Singleton-Types|Link1]], [[Type-Isomorphisms-for-Dependent-Records|Link2]], [[Constraint-Based-Unification-as-an-Inference-System|Link3]]
   - Eliminating projections via type isomorphism : [[Type-Isomorphisms-for-Dependent-Records|Link]]

4. **Constraint-Based Unification as an Inference System** : [[Constraint-Based-Unification-as-an-Inference-System|Link]]
   - Constraints and constraint sets : [[Constraint-Based-Unification-as-an-Inference-System|Link]]
   - Typing modulo a constraint set : [[Constraint-Based-Unification-as-an-Inference-System|Link]]
   - Local simplification by decomposition : [[Constraint-Based-Unification-as-an-Inference-System|Link]]
   - η-contraction of meta-variable substitutions : [[Inverting-Substitutions|Link1]], [[Constraint-Based-Unification-as-an-Inference-System|Link2]], [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link3]]
   - Orientation of equations
   - Lowering meta-variables to smaller types : [[Constraint-Based-Unification-as-an-Inference-System|Link]]
   - Solved versus active meta-variables

5. **Pruning and the Occurs Check** : [[Pruning-and-the-Occurs-Check|Link]]
   - Free variables escaping the range of a substitution
   - Bad occurrences and eliminable rigid occurrences : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]
   - The pruning judgement and context pruning : [[Extension-to-the-Unit-and-Singleton-Types|Link1]], [[Pruning-and-the-Occurs-Check|Link2]]
   - Failing occurs check and unsolvability : [[Pruning-and-the-Occurs-Check|Link]]
   - Non-linear patterns and intersection of substitutions : [[Pruning-and-the-Occurs-Check|Link]]
   - Recursive meta-variable occurrences

6. **Inverting Substitutions** : [[Inverting-Substitutions|Link]]
   - Invertibility of a variable substitution for a term : [[Inverting-Substitutions|Link1]], [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link2]]
   - Soundness and completeness of inverse substitution : [[Inverting-Substitutions|Link]]
   - Linearity as sufficient but not necessary for invertibility

7. **Correctness of the Unification Algorithm** : [[Correctness-of-the-Unification-Algorithm|Link]]
   - Termination via an ordinal-valued measure : [[Correctness-of-the-Unification-Algorithm|Link]]
   - Transitions preserve solutions (forward and backward closure)
   - Transitions preserve typing and well-formedness : [[Correctness-of-the-Unification-Algorithm|Link]]
   - Typing modulo equality : [[Constraint-Based-Unification-as-an-Inference-System|Link]]

8. **Extension to the Unit and Singleton Types** : [[Extension-to-the-Unit-and-Singleton-Types|Link]]
   - The extensional unit type and its single inhabitant : [[Extension-to-the-Unit-and-Singleton-Types|Link]]
   - Singleton types : [[Extension-to-the-Unit-and-Singleton-Types|Link]]
   - Type-directed η-contraction to a variable head : [[Extension-to-the-Unit-and-Singleton-Types|Link]]
   - Eliminating singleton subterms and singleton variables

9. **Related Unification Algorithms and Applications** : [[Related-Unification-Algorithms-and-Applications|Link]]
   - Comparison to Huet-style unification with Σ-types : [[Constraint-Based-Unification-as-an-Inference-System|Link]]
   - Comparison to simply-typed extended pattern unification : [[Higher-Order-Pattern-Unification|Link]]
   - Context blocks in Beluga, Twelf, and Delphin
   - Record and Σ-type unification in Agda : [[Correctness-of-the-Unification-Algorithm|Link1]], [[Higher-Order-Pattern-Unification|Link2]]

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 1–3)

**Summary:** Introduces higher-order pattern unification, Miller's decidable pattern fragment, and the practical need to go beyond it — both for delayed/dynamic constraints and for dependent record ($\Sigma$-)types — motivating the paper's core idea of using type isomorphisms to reduce Σ-type unification to pure pattern unification. : [[Type-Isomorphisms-for-Dependent-Records|Link]]

**Key Definitions & Concepts:**
- **Higher-order unification** — unification of terms containing applied meta-variables (logic variables), undecidable in general (Goldfarb, 1981).
- **Pattern (Miller pattern)** — a unification problem where every meta-variable is applied only to a list of pairwise-distinct bound variables; decidable and has a most general unifier.
- **Non-pattern examples** — a meta-variable applied non-linearly ($X\,x\,x$), applied to another meta-variable ($X\,(Y\,x)$), or applied to a non-variable term ($X\,(\mathrm{suc}\,y)$).
- **Dynamic pattern fragment** — postponing sub-problems outside the pattern fragment until further constraint solving simplifies them into the fragment (Michaylov and Pfenning, 1992).
- **Type isomorphism for Σ** — $\Pi z{:}(\Sigma x{:}A.B).C \cong \Pi x{:}A.\Pi y{:}B.[(x,y)/z]C$, letting a function into a record type be split into two component functions.

**Key Questions:**
1. Why is the pattern fragment decidable while full higher-order unification is not, and what precisely distinguishes a pattern from a non-pattern term?
2. Why do practical systems need a *dynamic* pattern fragment rather than just rejecting non-pattern constraints outright?
3. What is the key type-theoretic idea that lets a Σ-type unification problem be reduced to one involving only Π-types?

---

### Chapter 2: The λΠΣ-Calculus with Meta-Variables (pp. 3–5)

**Summary:** Fixes the object calculus — the $\lambda\Pi\Sigma$-calculus extended with meta-variables represented as closures over contextual objects — and its bidirectional typing discipline, together with the vocabulary of rigid/flexible/strongly-rigid occurrences needed to state the unification algorithm precisely. : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]

**Key Definitions & Concepts:**
- **Grammar of λΠΣ** — atomic types $P = a\,\vec M$; types $A,B ::= P \mid \Pi x{:}A.B \mid \Sigma x{:}A.B$; neutral terms $R = E[H]$ or $E[u[\sigma]]$; normal terms $M,N ::= R \mid \lambda x.M \mid (M,N)$.
- **Evaluation context $E$** — a term with a hole, generalizing "spine" notation to include projections ($E ::= \bullet \mid EN \mid \pi E$).
- **Meta-variable closure $u[\sigma]$** — a meta-variable under a suspended explicit substitution.
- **Contextual object $\hat\Psi.M$** — a term $M$ whose free variables are confined to the variable list $\hat\Psi$; the value that a meta-variable of contextual type stands for.
- **Weakening substitution $\mathrm{wk}_\Phi$** — the substitution embedding a sub-context $\Phi$ into a larger one.
- **Rigid vs. flexible occurrence** — an occurrence is rigid if not inside a meta-variable's delayed substitution, flexible otherwise; a rigid occurrence is *strongly rigid* if it is not itself inside the evaluation context applied to a free variable.
- **Bidirectional typing** ($\Rightarrow$ / $\Leftarrow$ judgements) — neutral terms have inferred (synthesized) types, normal terms are checked against a given type; complete for β-normal forms.
- **Hereditary substitution** — a substitution operation that resolves newly created redexes on the fly rather than substituting-then-normalizing, exploiting strong normalization of λΠΣ.
- **Meta-substitution $[\![\hat\Psi.M/u]\!]N$** — replacing a meta-variable by a contextual object, restoring β-normality and commuting with binders since meta-substitutions are closed w.r.t. LF variables.

**Key Questions:**
1. Why does representing meta-variables as closures over contextual objects (rather than as plain higher-order variables applied to arguments) avoid the need to construct explicit λ-prefixes when instantiating them?
2. What distinguishes a *rigid* from a *strongly rigid* occurrence of a variable, and why does the distinction matter for whether that occurrence can ever "disappear" during unification?
3. How does hereditary substitution differ operationally from naive substitute-then-normalize, and why is that difference necessary here?

---

### Chapter 3: Constraint-Based Unification (pp. 5–17)

**Summary:** The technical core of the paper: constraints and constraint sets are defined, "typing modulo constraints" is introduced to allow provisionally ill-typed intermediate states, and the unification algorithm proper is given as two families of rewrite rules — local simplification (decomposition, η-contraction, projection elimination) and meta-variable-directed steps (lowering, Σ-flattening, pruning, same-meta-variable, solving) — together with the auxiliary machinery of substitution inversion and the pruning judgement needed to make those steps sound. : [[Constraint-Based-Unification-as-an-Inference-System|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 Typing modulo** — **Typing modulo constraints ($\vdash_K$)** replaces strict η-equality checks by equality modulo the constraint set $K$ ($\alpha =_K \beta$ iff $[\![\theta]\!]\alpha =_\eta [\![\theta]\!]\beta$ for every ground solution $\theta$ of $K$), letting the algorithm decompose a constraint before knowing it is fully well-typed — necessary because postponing constraints is essential for practical dependent type reconstruction. Lemmas 3.1–3.3 establish that typing modulo is stable under substitution and meta-substitution. : [[Constraint-Based-Unification-as-an-Inference-System|Link]]
- **3.2 The unification algorithm** — **Constraint** forms: trivial ($\top$), inconsistent ($\bot$), term equality ($\Psi \vdash M = N : C$), evaluation-context equality ($\Psi \mid R{:}A \vdash E = E'$), and solved meta-variable ($\Psi \vdash u \leftarrow M : C$). **Solved vs. active meta-variable** — a meta-variable is solved once a constraint $u \leftarrow M$ exists for it and it no longer occurs elsewhere. **Local simplification** (Fig. 3) — decomposition of functions, pairs, and neutrals into smaller constraints; η-contraction of $u[\sigma]$ when $\sigma$ contains an η-expanded subterm; elimination of projections via the Sigma-Pi isomorphism (splitting a variable of Σ-type into two variables of the component types). **Lowering** — replacing a meta-variable of function or pair type by a fresh meta-variable(s) of the codomain/component type(s), used to expose more structure. **Flattening Σ-types** — eliminating a Σ-type from a meta-variable's own context by splitting the corresponding context variable into two variables via the isomorphism. : [[Constraint-Based-Unification-as-an-Inference-System|Link1]], [[Correctness-of-the-Unification-Algorithm|Link2]], [[Related-Unification-Algorithms-and-Applications|Link3]], [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link4]]
- **3.3 Inverting substitutions** — **Invertibility** — a variable substitution $\rho$ is invertible for $M$ if there is a unique $M'$ with $[\rho]M' = M$; linearity of $\rho$ restricted to $\mathrm{FV}(M)$ is sufficient but not necessary. **Inverse substitution $[\rho/\hat\Phi]^{-1}\alpha$** — a partial, directly-computed operation avoiding the detour through computing free variables and checking invertibility explicitly (Lemmas 3.4–3.6: commutes with meta-substitution, sound, complete). : [[Inverting-Substitutions|Link]]
- **3.4 Pruning** — **Pruning** — given $u[\sigma] = M$ with $\mathrm{FV}(M) \not\subseteq \mathrm{FV}(\sigma)$, find the most general meta-substitution $\eta$ removing the offending free variables from $M$. **Bad occurrence** ($\mathrm{bad\,occ}_x\,M$) — a rigid occurrence of $x$ in $M$ that cannot be eliminated by any future instantiation of the surrounding meta-variables, hence blocks pruning; contrasted with rigid-but-eliminable occurrences (e.g. under an application that a later meta-variable solution could reduce away). Three documented failure modes of pruning: offending variable occurs (non-eliminably) rigidly; the offending occurrence is nested under another meta-variable (non-unique minimal pruning substitutions exist); the offending occurrence is eliminable by the correct future solution. : [[Pruning-and-the-Occurs-Check|Link]]
- **3.5 Same meta-variable** — For a constraint $u[\rho] = u[\xi]$, the **intersection** $\rho \cap \xi : \Phi \Rightarrow \Phi'$ computes the sub-context of variables on which $\rho$ and $\xi$ agree; $u$ can then be replaced by a new meta-variable depending only on $\Phi'$ (Lemma 3.9: soundness of intersection). Intersection does not extend beyond variable substitutions because general substitution need not be injective. : [[Constraint-Based-Unification-as-an-Inference-System|Link1]], [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link2]]
- **Occurs check and Solving** — a constraint $u[\rho] = M$ (with $\rho$ a variable substitution) is solved by inverting $\rho$ on $M$, provided the occurs check succeeds: $u$ must not occur in $M$ at all (flexibly is tolerated only if resolvable via other constraints), and a *recursive strongly-rigid* self-occurrence signals unsolvability (only an infinite term would solve it).

**Key Questions:**
1. Why must the algorithm give up strict well-typedness at every intermediate step and instead adopt "typing modulo constraints," and what concrete example in the text shows well-typedness would otherwise block a legitimate decomposition?
2. Walk through why $u[x] = \mathrm{suc}(v[x,y])$ can be solved by pruning $v$'s second argument, but $u[x] = \mathrm{suc}(v[x, w[y]])$ cannot be pruned by the technique of this paper — what exactly makes the nested-meta-variable case different?
3. In the "same meta-variable" case $u[\rho] = u[\xi]$, why is it sound to replace $u$ by a new meta-variable that depends only on the sub-context where $\rho$ and $\xi$ agree, rather than on all of $u$'s original context?
4. Why does a *strongly rigid* recursive occurrence of $u$ in its own definition force unsolvability, while a merely *rigid* (non-strongly-rigid) occurrence does not (cf. the $f:\mathrm{nat}\to\mathrm{nat} \vdash u[f] = \mathrm{suc}(f(u[\lambda x.\mathrm{zero}]))$ example)?

---

### Chapter 4: Correctness (pp. 18–21)

**Summary:** Proves the three correctness properties promised in the introduction — termination, preservation of solutions, and preservation of well-typedness — establishing that the constraint-rewriting system is a sound and complete decision procedure (up to postponement) for the extended pattern fragment.

**Key Definitions & Concepts by Section:**
- **Termination** — defined via an ordinal-valued weight on unification problems (term size counting $\lambda$-nodes twice so η-expansion strictly decreases weight; Σ-types given extra weight to "pay for" flattening); every transition strictly decreases this weight, so the algorithm always reaches a solved, stuck, or failed ($\bot$) state.
- **4.1 Solutions to unification** — A **solution** $\theta$ to $\Delta \gg K$ is a meta-substitution making every constrained equation hold and instantiating every solved meta-variable as required. Lemma 4.2 and Theorem 4.3 show each transition step both preserves existing solutions (forward closure) and introduces no new ones inconsistent with existing solutions (backward closure) — i.e., transitions neither create nor destroy solutions. : [[Higher-Order-Pattern-Unification|Link]]
- **4.2 Transitions preserve types** — Lemma 4.4 (equality modulo is preserved), Lemma 4.5 (typing is preserved under the meta-substitution induced by a transition), and Theorem 4.8 (well-formedness of the whole constraint set is preserved) together show the algorithm never derives an ill-typed intermediate state from a well-typed one. : [[Correctness-of-the-Unification-Algorithm|Link]]

**Key Questions:**
1. Why is it necessary to use an *ordinal*-valued (rather than natural-number) measure to prove termination, and what specific role does giving Σ-types "large weight" play in that measure?
2. What is the difference between "transitions preserve solutions" (Theorem 4.3, part 1) and "transitions are backward closed" (part 2), and why must both directions be proved separately for the algorithm to be correct?
3. Why does proving that transitions preserve typing (Lemma 4.5) require the auxiliary result that equality modulo constraints is itself preserved by transitions (Lemma 4.4)?

---

### Chapter 5: Extension to Unit Type (pp. 22–26)

**Summary:** Extends the algorithm to the extensional unit type $1$ (needed to represent empty records via $\Sigma$-types) and, more generally, to arbitrary singleton types, whose defining property — every inhabitant is η-equal to every other — breaks the assumption that η-equality preserves free variables, forcing type-directed refinements to η-contraction, the occurs check, and pruning. : [[Extension-to-the-Unit-and-Singleton-Types|Link]]

**Key Definitions & Concepts:**
- **Unit type $1$** — the type with a single inhabitant $\star$ up to η-equality; any $M : 1$ satisfies $M =_\eta \star$.
- **Singleton type ($A\,\mathrm{sing}$)** — any type with exactly one inhabitant up to η, defined structurally (unit, and closed under $\Pi$ and $\Sigma$ when the codomain/component is a singleton), together with its canonical inhabitant $\star_A$ (Lemma 5.1: soundness of the singleton predicate).
- **Type-directed η-contraction to a variable ($\Psi \vdash M \gg E[x] \Leftarrow A$)** — an algorithm that η-contracts a term of non-singleton type to a neutral term headed by a variable, needed to decide whether an arbitrary substitution appearing in a constraint is equivalent to a variable substitution (Lemma 5.2: soundness, completeness, termination, decidability).
- **Eliminating singleton subterms** — rewriting the right-hand side of a constraint to replace all subterms of singleton type by their canonical inhabitant, since such subterms could otherwise spuriously trip the occurs check or pruning.
- **Solving singleton metas** — a meta-variable of singleton type can always be solved immediately with the canonical inhabitant, with no further constraint solving needed.

**Key Questions:**
1. Why does introducing the unit (and more generally singleton) type break the invariant that η-equality preserves the set of free variables, and what concrete problem would arise for the occurs check if this were not accounted for?
2. What is the purpose of the auxiliary judgement $\Psi \vdash M \gg E[x] \Leftarrow A$, and why must it be *type-directed* rather than a single uniform η-contraction rule?
3. Why can meta-variables of singleton type always be solved "on the spot," independent of any other constraint on them?

---

### Chapter 6: Related Work (p. 26)

**Summary:** Positions the paper's algorithm relative to prior extensions of higher-order pattern unification to product/record types — Elliott's Huet-style algorithm with Σ-types, Fettig and Löchner's finite-product unification (which normalizes projections similarly but without exploiting type isomorphisms as systematically), and Duggan's extended patterns allowing repeated projected-variable arguments — arguing this work is the first comprehensive, correctness-proven treatment for the full dependently-typed $\lambda\Pi\Sigma$ setting.

**Key Definitions & Concepts:**
- **Huet-style unification with Σ-types (Elliott, 1990)** — an earlier, less formally justified treatment of product types in higher-order unification.
- **Fettig and Löchner's finite-product pattern unification** — normalizes projection-headed abstractions (e.g. $\lambda x.\mathrm{fst}\,x \to \lambda(x_1,x_2).x_1$) without exploiting Σ/Π isomorphisms as a general translation mechanism.
- **Duggan's extended patterns** — generalizes Miller's restriction in the simply-typed setting by allowing repeated variable occurrences prefixed by distinct projection sequences.

**Key Questions:**
1. What distinguishes this paper's use of type *isomorphisms* to translate Σ-type problems into Π-type problems from Fettig and Löchner's approach of directly normalizing projection-headed terms?

---

### Chapter 7: Conclusion (pp. 26–27)

**Summary:** Summarizes the paper's contributions — a formally correct pruning operation for the dependently typed case that trades some generality (relative to Reed's more ambitious but non-terminating proposal) for guaranteed termination, and the first Σ-type extension of pattern unification with a full correctness proof — and reports that the techniques have been used in practice to implement context-block flattening in Beluga and Σ-type/record unification in Agda 2, noting the open problem of scaling "typing modulo" correctness to systems (like Agda) with large eliminations and type-level unification.

**Key Definitions & Concepts:**
- **Practical deployments** — Beluga's context-block flattening (Pientka, 2013) and Agda's extended unification algorithm for records (via the techniques of this paper), both cited as evidence of practical relevance.
- **Limits of "typing modulo" correctness** — the correctness proof relies on λΠΣ's strong normalization even for ill-typed terms; this does not extend to systems like Agda with large eliminations, where Norell's alternative approach (blocking normalization on unsolved constraints) is used instead.

**Key Questions:**
1. In what specific sense is this paper's pruning strategy "less ambitious" than Reed's, and what correctness property does that sacrifice buy in return?
2. Why doesn't the "typing modulo constraints" correctness technique used here scale directly to a system like Agda, and what alternative strategy (Norell's) does Agda use instead?

---
