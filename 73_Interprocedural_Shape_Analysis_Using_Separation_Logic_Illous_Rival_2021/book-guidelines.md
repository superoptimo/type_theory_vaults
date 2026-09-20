# Interprocedural Shape Analysis Using Separation Logic-based Transformer Summaries — Guidelines

## Header

**Title:** Interprocedural Shape Analysis Using Separation Logic-based Transformer Summaries
**Author(s):** Hugo Illous, Matthieu Lemerre, Xavier Rival
**Publication:** SAS 2020 — 27th Static Analysis Symposium (Nov 2020, Chicago/Virtual); HAL preprint hal-03081558

**Brief Summary:**
This is a 25-page research paper, not a book, so its "chapters" below are its numbered sections; boundaries follow the paper's own table of contents exactly (no inference needed). It proposes a shape analysis for heap-manipulating programs (linked lists, trees) that abstracts *transformations* between input and output memory states, rather than sets of states, using logical connectors inspired by separation logic. These abstract transformations serve as composable procedure summaries: the paper builds abstract intersection and composition operators over them and uses these to drive a top-down, modular interprocedural analysis that reuses a procedure's summary across call sites instead of reanalyzing its body every time it is called.

**Intent of the Author:**
The authors want to show that a genuinely relational (input/output) abstraction for separation-logic-style heap properties is both formalizable with soundness guarantees and practically effective — cutting analysis time drastically versus a call-string/inlining approach — by supplying the missing composition algorithm and top-down summary-inference/application protocol that earlier transformation-abstraction work (their own prior NASA Formal Methods paper) lacked.

---

## Topic List

1. **Interprocedural Analysis via Procedure Summaries** : [[Interprocedural-Analysis-via-Procedure-Summaries|Link]]
   - The relational approach to interprocedural analysis : [[Modular-Interprocedural-Call-Analysis|Link]]
   - State analyses versus transformation analyses : [[Interprocedural-Analysis-via-Procedure-Summaries|Link]]
   - Tabulation of pre/post-condition pairs and its precision limits
   - Global transformation summaries : [[Relational-Shape-Abstraction-Transformation-Domain|Link1]], [[Intraprocedural-Transformation-Analysis|Link2]]
   - Context transformation summaries : [[Relational-Shape-Abstraction-Transformation-Domain|Link1]], [[Intraprocedural-Transformation-Analysis|Link2]]
   - Top-down versus bottom-up summary inference : [[Interprocedural-Analysis-via-Procedure-Summaries|Link]]

2. **Separation Logic for Shape Analysis** : [[Separation-Logic-for-Shape-Analysis|Link]]
   - Abstract heaps as separating conjunctions of region predicates
   - Points-to predicates over symbolic names
   - Summary predicates for list segments and singly-linked lists
   - Inductive unfolding of summary predicates : [[Separation-Logic-for-Shape-Analysis|Link]]
   - Concretization of abstract states via valuations : [[Separation-Logic-for-Shape-Analysis|Link]]

3. **Relational Shape Abstraction (Transformation Domain)** : [[Relational-Shape-Abstraction-Transformation-Domain|Link]]
   - Abstract transformations as identity, input-output pairs, and separating conjunction
   - The transformation-level separating connector distinguished from the state-level connector
   - Concretization of abstract transformations : [[Relational-Shape-Abstraction-Transformation-Domain|Link1]], [[Abstract-Intersection-and-Composition-Algorithms|Link2]], [[Separation-Logic-for-Shape-Analysis|Link3]]
   - Soundness statement for abstract transformer semantics : [[Relational-Shape-Abstraction-Transformation-Domain|Link]]
   - Widening over abstract transformations : [[Intraprocedural-Transformation-Analysis|Link1]], [[Relational-Shape-Abstraction-Transformation-Domain|Link2]], [[Abstract-Intersection-and-Composition-Algorithms|Link3]]
   - Inclusion testing over abstract transformations : [[Relational-Shape-Abstraction-Transformation-Domain|Link]]

4. **Intraprocedural Transformation Analysis** : [[Intraprocedural-Transformation-Analysis|Link]]
   - Forward abstract interpretation over transformations rather than states
   - Localization and mutation of pointer cells during assignment analysis : [[Intraprocedural-Transformation-Analysis|Link]]
   - Unfolding summaries to resolve modified cells
   - Weakening of transformations at loop widening points : [[Intraprocedural-Transformation-Analysis|Link]]
   - Variable introduction and removal transfer functions : [[Intraprocedural-Transformation-Analysis|Link]]

5. **Abstract Intersection and Composition Algorithms** : [[Abstract-Intersection-and-Composition-Algorithms|Link]]
   - Abstract intersection of two abstract heaps : [[Abstract-Intersection-and-Composition-Algorithms|Link]]
   - Rewriting rules for structural intersection reasoning
   - Abstract composition of two abstract transformations : [[Abstract-Intersection-and-Composition-Algorithms|Link]]
   - Rewriting rules for composition, including weakening rules
   - Soundness of abstract intersection and composition : [[Abstract-Intersection-and-Composition-Algorithms|Link]]
   - Composition as a mechanism for both application and sequencing

6. **Modular Interprocedural Call Analysis** : [[Modular-Interprocedural-Call-Analysis|Link]]
   - Procedure footprint extraction via the output-projection operator : [[Modular-Interprocedural-Call-Analysis|Link]]
   - Relevance slicing of an abstract heap with respect to call parameters
   - Context summary coverage testing via abstract inclusion
   - Summary application at a call site : [[Modular-Interprocedural-Call-Analysis|Link]]
   - Inference and generalization of a new context summary via widening
   - Analysis of recursive procedure calls via fixpoint iteration on summaries : [[Modular-Interprocedural-Call-Analysis|Link]]

7. **Experimental Evaluation of Summary-Based Shape Analysis** : [[Experimental-Evaluation-of-Summary-Based-Shape-Analysis|Link]]
   - Frama-C-based implementation for a fragment of C
   - Comparison against a call-string (inlining) based analysis
   - Precision preservation relative to state analysis : [[Separation-Logic-for-Shape-Analysis|Link1]], [[Experimental-Evaluation-of-Summary-Based-Shape-Analysis|Link2]]
   - Scalability and total analysis time : [[Experimental-Evaluation-of-Summary-Based-Shape-Analysis|Link]]
   - Effectiveness of summary reuse versus reanalysis frequency
   - Validation on recursive list and tree algorithms : [[Experimental-Evaluation-of-Summary-Based-Shape-Analysis|Link]]

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 1–3)

**Summary:** Motivates transformation-based (relational) interprocedural analysis over classical state-based tabulation, using a numeric interval-vs-polyhedra example to show why relational domains compose better, then explains why separation logic resists this treatment and outlines the paper's contributions (composition algorithm, top-down modular protocol). : [[Intraprocedural-Transformation-Analysis|Link]]

**Key Definitions & Concepts:**
- state analyses / transformation analyses — abstractions of reachable states vs. abstractions of the input–output relation of a program fragment.
- relational approach to interprocedural analysis — reusing a composable abstraction of a procedure's effect across call sites, following Sharir and Pnueli.
- tabulation approach — representing a summary as a table of abstract pre-/post-condition pairs; imprecise unless tables grow large.
- procedure summary (informal) — a reusable description of a procedure's effect that avoids reanalyzing its body per call.

**Key Questions:**
1. Why does a relational numeric abstract domain (e.g. polyhedra) compose more gracefully across call sites than a table of interval pre/post-conditions?
2. Why can't separation logic connectors be reused unchanged to express a relation between two distinct states (input and output)?

---

### Chapter 2: Overview (pp. 3–5)

**Summary:** Walks through `append`/`double_append` on linked lists to contrast state-analysis-by-inlining (which reanalyzes `append`'s body once per call) with transformation-based analysis, where the summary for `append` is computed once and then applied by abstract composition; also previews the case-split and summary-generalization issues that a top-down protocol must resolve.

**Key Definitions & Concepts:**
- $lseg(\alpha_0, \alpha_1)$ — a summary predicate for a (possibly empty) list segment from symbolic address $\alpha_0$ to $\alpha_1$.
- $list(\alpha)$ — shorthand for $lseg(\alpha, 0x0)$, a complete singly-linked list.
- $n \cdot f \mapsto n'$ — a points-to predicate: a memory cell at address $n$ (offset by field $f$) holding value $n'$.
- $*_S$ vs. $*_T$ — separating conjunction at the state level vs. at the transformation level (the paper's notational device for stressing the distinction).
- application vs. composition — applying a transformation to a state (to get a post-state) vs. composing two transformations (to get a summary of their sequential effect).

**Key Questions:**
1. In the `append` example, what does the abstract transformation of Figure 2(a) assert is preserved versus modified, and why does this let the analysis skip reanalyzing `append`'s body for `double_append`?
2. Why does summarizing `double_append` require *composing* two transformations rather than merely *applying* one transformation to one state?

---

### Chapter 3: Abstraction of Sets of States and State Transformations (pp. 5–7)

**Summary:** Formalizes the small imperative language and concrete memory-state semantics, then defines the syntax and concretization of abstract heaps (separation-logic-style states) and of abstract transformations, establishing the two-level abstraction (states, then transformations over states) the rest of the paper builds on. : [[Abstract-Intersection-and-Composition-Algorithms|Link]]

**Key Definitions & Concepts:**
- memory state $\sigma \in M$ — a partial function from variable/heap addresses to values; $\sigma_0 \uplus \sigma_1$ appends two states with disjoint domains.
- abstract heap $h^\sharp \in H$ — separating conjunction of region predicates (emp, points-to, or inductive summary), possibly constrained by numerical predicates $c^\sharp$.
- symbolic names $n \in N$ — either a variable address $\&x$ or a symbolic value $\alpha \in A$.
- valuation $\nu: N \to V$ — ties abstract symbolic names to concrete values/addresses for concretization.
- $\gamma_H$ — concretization function for abstract heaps; unfolds summary predicates recursively via the rewrite relation $\to_U$.
- abstract transformation $t^\sharp \in T$ — $Id(h^\sharp)$ (identity/unchanged region), $[h^\sharp_i \dashrightarrow h^\sharp_o]$ (input-output pair), or a $*_T$-conjunction of transformations.
- $\gamma_T$ — concretization of abstract transformations into triples $(\sigma_i, \sigma_o, \nu)$; the $*_T$ case additionally enforces cross-disjointness between the pre-heap of one conjunct and the post-heap of the other.
- $\to_U$ / $\to_{U[\alpha]}$ — the unfolding rewrite relation for summary predicates, used uniformly over heaps and transformations.

**Key Questions:**
1. Why must the $*_T$ concretization rule require disjointness not just within each state but *across* the pre- and post-states of the two conjuncts?
2. What is the role of the shared valuation $\nu$ in tying together the concretizations of two separately-defined transformation conjuncts?

---

### Chapter 4: Procedure Summarization (pp. 7–9)

**Summary:** Introduces two notions of summary — an unconditionally sound global summary of a procedure's whole input/output relation, and a context summary that pairs a transformation with an over-approximation of the input states actually observed — and argues, via the crashing `getnext` example, why the context component is necessary to soundly account for inputs that lead to non-termination or error.

**Key Definitions & Concepts:**
- $f \trianglerighteq R$ — notation stating a semantic function $f$ is over-approximated by relation $R$ (used to define soundness of a summary).
- global transformation summary — an abstract transformation $t^\sharp$ over-approximating a whole procedure's semantics $[\hspace{-1pt}[C]\hspace{-1pt}]^T$.
- context transformation summary $(h^\sharp_f, t^\sharp_f)$ — a pair of an abstract precondition heap and an abstract transformation, sound with respect to the procedure's semantics *restricted* to states satisfying $h^\sharp_f$.

**Key Questions:**
1. Why does a bare global summary $t^\sharp$ fail to answer "does this summary already cover this new calling context?" — what information is missing that only the context-summary's $h^\sharp_f$ component supplies?
2. In the `getnext` example, why can a sound $(h^\sharp_f, t^\sharp_f)$ pair include a precondition ($h^\sharp_f$) describing states that never appear in the transformation's concretization at all?

---

### Chapter 5: Intraprocedural Analysis (pp. 9–10)

**Summary:** Sketches the forward abstract interpretation carried out *over transformations* (rather than states) that computes the effect of each command on top of the transformation accumulated so far, states the soundness invariant this must satisfy, and illustrates it with the `append` loop, whose widening over transformations both introduces summary predicates and stabilizes into the loop invariant. : [[Intraprocedural-Transformation-Analysis|Link]]

**Key Definitions & Concepts:**
- $[\hspace{-1pt}[C]\hspace{-1pt}]^{T\sharp}$ — the abstract transformer for command $C$: takes the transformation for computation-so-far and returns the transformation extended by $C$'s effect.
- localization — rewriting a pre-transformation to expose the cell an assignment target/source refers to, unfolding a summary predicate ($\to_U$) when the cell is hidden inside one.
- widening over transformations $t^\sharp_0 \triangledown_T t^\sharp_1$ — commutes with $Id$ and $*_T$ where possible, otherwise weakens conjuncts into $[\dashrightarrow]$ form; introduces summary predicates to guarantee termination.
- inclusion test over transformations $\sqsubseteq_T$ — a sound, conservative test that $\gamma_T(t^\sharp_0) \subseteq \gamma_T(t^\sharp_1)$ implies $t^\sharp_0 \sqsubseteq_T t^\sharp_1$.
- $newV_T^\sharp$ / $delV_T^\sharp$ — transfer functions adding/removing variables from a transformation's output state.

**Key Questions:**
1. What soundness equation (Eq. 1) must every command's abstract transformer satisfy, and how does it formalize the intuition that the transformer's input acts as "the dual of a continuation"?
2. Why does widening a loop's transformations need to introduce summary predicates on the state side, not merely widen the transformation connectors themselves?

---

### Chapter 6: Abstract Composition (pp. 10–13)

**Summary:** Develops the two rewriting-rule-based algorithms the whole modular approach depends on: abstract intersection $\sqcap$ of two abstract heaps (needed to reason about overlapping preconditions) and abstract composition $\#$ of two abstract transformations (needed to sequence one procedure's effect after another's, or to apply a transformation to a state). Both are proved sound; both admit multiple derivations depending on rule-application order, so the implementation follows a precision-oriented strategy. : [[Abstract-Intersection-and-Composition-Algorithms|Link]]

**Key Definitions & Concepts:**
- $h^\sharp_0 \sqcap h^\sharp_1 \sqcap H$ — abstract intersection predicate: intersecting two heaps may yield a disjunction $H$ of possible results.
- intersection rules $\sqcap_{*_S}$, $\sqcap_=$, $\sqcap_{[l,s]}$, $\sqcap_{[s,s]}$, $\sqcap_U$ — local reasoning, identical-term shortcut, summary-vs-segment structural matching, and forced unfolding, respectively.
- $inter^\sharp$ — the partial algorithm computing $\sqcap$ via proof search over the rewriting rules; returns either argument unchanged if it cannot find a better solution (Definition 3).
- Theorem 1 (soundness of abstract intersection) — $\gamma_H(h^\sharp_0) \cap \gamma_H(h^\sharp_1) \subseteq \gamma_H(inter^\sharp(h^\sharp_0, h^\sharp_1))$.
- $t^\sharp_0 \# t^\sharp_1 \# T$ — abstract composition predicate: sequencing two transformations may yield a disjunction $T$ of results.
- composition rules $\#_{*_T}$, $\#_{Id}$, $\#_{99K}$, $\#_{Id,99K,l}$, $\#_{weak,Id,l}$, $\#_{weak,*_T,l}$, $\#_{unf,l}$ (plus symmetric right-versions) — local composition, matching identities, matching modifications, mixed identity/modification matching, weakening $Id$ into $[\dashrightarrow]$, weakening a $*_T$-pair into one merged $[\dashrightarrow]$, and unfolding to enable a match.
- $comp^\sharp$ — the partial algorithm computing $\#$ (Definition 4).
- Theorem 2 (soundness of abstract composition) — sequential concretizations of $t^\sharp_0$ then $t^\sharp_1$ are captured by some transformation in $comp^\sharp(t^\sharp_0, t^\sharp_1)$.

**Key Questions:**
1. Why does composing $t^\sharp_0$ then $t^\sharp_1$ sometimes require *weakening* an $Id$ or $*_T$-pair before a matching rule applies, and what precision cost does that weakening incur?
2. How does treating "apply transformation $t^\sharp$ to state $h^\sharp$" as a special case of composition ($Id(h^\sharp) \# t^\sharp$) unify the two operations the Overview section (Ch. 2) introduced separately?

---

### Chapter 7: Interprocedural Analysis Based on Function Summaries (pp. 13–17)

**Summary:** Assembles Sections 3–6 into the full modular call-analysis algorithm: given an existing context summary for a callee, the analysis passes parameters, extracts the callee-relevant footprint via projection and relevance-slicing, tests whether the existing summary's precondition covers this call's context, and either applies the summary (by composition) or first widens the context and reanalyzes the callee body to obtain a more general summary before applying it; recursive calls are handled by iterating this to a fixpoint. : [[Interprocedural-Analysis-via-Procedure-Summaries|Link]]

**Key Definitions & Concepts:**
- parameter passing transformation $t^\sharp_{pars}$ — composes $newV_T^\sharp$ and successive assignment transformers to bind actual arguments to formal parameters.
- footprint operator $O: T \to H$ — projects the "output" abstract state out of a transformation ($O(Id(h^\sharp)) = h^\sharp$, $O([h^\sharp_0 \dashrightarrow h^\sharp_1]) = h^\sharp_1$, distributing over $*_T$ and $\wedge$).
- relevance rules $R[h^\sharp]$ — the least set of symbolic names reachable from a call's formal parameters via points-to/summary edges in $h^\sharp$.
- slicing $R[p_0,\ldots,p_k](h^\sharp)$ / $I[p_0,\ldots,p_k](h^\sharp)$ — the callee-relevant fragment of $h^\sharp$ vs. the remainder, with $h^\sharp = R[\ldots](h^\sharp) *_S I[\ldots](h^\sharp)$.
- context summary coverage test — $h^\sharp_{in,f} \sqsubseteq_H h^\sharp_f$, a sound abstract-state inclusion test deciding whether the existing summary's precondition subsumes this call's actual input footprint.
- summary application — $delV_T^\sharp[p_0,\ldots,p_k](comp^\sharp(t^\sharp_{pars}, t^\sharp_f *_T Id(h^\sharp_{rem})))$: compose the parameter-passing transformation with the summary (applied to the relevant part, identity on the remainder), then drop the formal parameters.
- new-summary inference (when coverage fails) — widen the precondition, $h^\sharp_f \leftarrow h^\sharp_f \triangledown_H h^\sharp_{in,f}$, then recompute $t^\sharp_f \leftarrow [\hspace{-1pt}[C]\hspace{-1pt}]^{T\sharp}(Id(h^\sharp_f \triangledown_H h^\sharp_{in,f}))$ by reanalyzing the callee body.
- Theorem 3 (soundness of call analysis) — the returned post-transformation over-approximates the call's effect *and* the updated context summary itself remains a valid summary accounting for this call.
- recursive-call handling — treat an unmatched recursive call by widening $h^\sharp_f$ and using the current $t^\sharp_f$ directly; widen $t^\sharp_f$ against its previous value at the end of each body analysis and iterate to a fixpoint.

**Key Questions:**
1. Why does the algorithm need both a relevance slice $R[\ldots]$ *and* an inclusion test $h^\sharp_{in,f} \sqsubseteq_H h^\sharp_f$ — what would go wrong if the coverage test were run directly against the whole projected output $O(t^\sharp_{pars})$ instead of just its relevant fragment?
2. What guarantees convergence when a recursive call repeatedly fails the coverage test, and why is widening required on *both* the $h^\sharp_f$ and $t^\sharp_f$ components rather than just one?
3. Concretely, in Example 10's `append(a,b); append(a,c)` scenario, why does the first call's summary (for a length-1 first argument) fail to cover the second call, and what generalization step fixes this?

---

### Chapter 8: Experimental Evaluation (pp. 17–19, data in Appendix A)

**Summary:** Reports a Frama-C-based implementation evaluated on a ~3kLOC fragment of GNU Emacs and on classical recursive list/tree algorithms, measuring whether the summary-based analysis stays as precise as a state-based analysis, how much faster it is than a call-string (inlining) approach, and how often summaries actually need to be recomputed versus reused. : [[Experimental-Evaluation-of-Summary-Based-Shape-Analysis|Link]]

**Key Definitions & Concepts:**
- call-string-based analysis (baseline) — a competing implementation that inlines procedures at every call site instead of using summaries.
- precision comparison metric — whether the transformation computed for the whole procedure body from its context summary's entry state is at least as precise as the state-analysis post-condition; "irrel." marks call-free functions where the comparison doesn't apply.
- scalability result — total analysis time 14.20s (summary-based) vs. 877.12s (state-based) on the Emacs `Fx_show_tip` fragment.
- reuse-effectiveness metrics (#state, #total, #recomp, #reuse) — respectively, state-analysis reanalysis count, total call-site encounters, summary recomputations, and summary reuses without recomputation.

**Key Questions:**
1. Why does the transformation-based analysis show low or even negative speedup for some low-call-tree-depth functions, while showing very high gain for functions near the top of the call graph?
2. What does the near-universal "computed once, reused many times" pattern (e.g. `Fcons` needing only 3 recomputations against 44 reuses) say about how quickly top-down context summaries tend to stabilize in practice?

---

### Chapter 9: Related Works and Conclusion (pp. 19–20)

**Summary:** Positions the paper against prior interprocedural analysis lineages — Sharir/Pnueli's relational framework, primed-variable TVLA-style relational shape analysis, tabulation-based separation-logic summaries, and graph/points-to-based summary techniques — and closes by naming bi-abduction, bottom-up summary inference, and cut-point-based stack/heap abstraction as complementary directions the transformation-based approach could be combined with.

**Key Definitions & Concepts:**
- primed-variable technique — TVLA's approach (Jeannet, Loginov, Reps, Sagiv) to relational shape analysis, distinguishing input/output variables by priming rather than by a dedicated transformation connector.
- bi-abduction — a technique (Calcagno, Distefano, O'Hearn, Yang) for inferring a procedure's abstract precondition together with its postcondition; noted as orthogonal to the choice of state vs. transformation domain, hence potentially portable to this paper's setting.
- cut-points — a device (Rinetzky, Sagiv, Yahav et al.) for describing heap structures tightly intertwined with the stack frame; the authors argue their preserved-region transformations reduce the need to reason about cut-points explicitly.
- frame problem — the general problem of describing what a program fragment leaves *unchanged*; the paper frames its intersection operator as opening a path toward resolving this via graph representations of states/transformations.

**Key Questions:**
1. Why does the paper argue that separation logic's regional-formula semantics is fundamentally harder to adapt to relational (primed-variable-style) summaries than a numeric relational domain like polyhedra?
2. In what sense is bi-abduction "orthogonal to the choice of state abstract domain," and what would have to change to apply it to this paper's transformation-based summaries instead of O'Hearn et al.'s original state-based setting?

---
