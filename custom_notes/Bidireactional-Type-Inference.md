# Introduction

Type inference and checking _are_ proof search and proof checking, once you fix the right reading of the judgments. The correspondence is tight in some places and breaks down, or becomes undecidable, in others.

## The dictionary

Under Curry-Howard-Lambek, a typing judgment is a sequent with a proof term attached:

$$\Gamma \vdash M : A \quad\text{reads as}\quad \Gamma \text{ proves } A \text{ with witness (proof object) } M$$

|Logic|Type theory|
|---|---|
|Proposition $A$|Type $A$|
|Proof of $A$|Term $M : A$|
|Hypothesis context|Typing context $\Gamma$|
|$A \Rightarrow B$|$A \to B$|
|$\forall x{:}A.,P(x)$|$\Pi x{:}A.,P(x)$|
|$\exists x{:}A.,P(x)$|$\Sigma x{:}A.,P(x)$|
|Equality|Identity type $\mathrm{Id}_A(a,b)$|
|Proof normalization|$\beta$-reduction|

## Two modes: checking and inference

The bidirectional presentation maps neatly onto the two logical activities.

**Checking** ($\Gamma \vdash M \Leftarrow A$) is proof verification. You are given a proposition and a candidate proof, and you confirm the proof is valid. This is decidable for essentially all the systems we care about.

**Synthesis** ($\Gamma \vdash M \Rightarrow A$) is extracting the proposition proved by a given proof object. Here the term is the input and the type is the output.

**Inhabitation** is the genuinely search-like problem: given $A$, find some $M$ with $\Gamma \vdash M : A$. This is proof search, and it is a different problem from inference, which asks for the type of a _given_ term. Calling "type inference" the whole of proof search conflates the two. Inference is mostly deterministic proof reconstruction. Inhabitation is where the real search happens.

## Where the correspondence is faithful

**Quantifiers.** The introduction and elimination rules for $\Pi$ and $\Sigma$ are the usual ones:

$$\dfrac{\Gamma, x{:}A \vdash M : B}{\Gamma \vdash \lambda x{:}A.,M : \Pi x{:}A.,B}\ (\Pi\text{-I})  
\qquad  
\dfrac{\Gamma \vdash M : \Pi x{:}A.,B \quad \Gamma \vdash N : A}{\Gamma \vdash M,N : B[N/x]}\ (\Pi\text{-E})$$

$$\dfrac{\Gamma \vdash a : A \quad \Gamma \vdash b : B[a/x]}{\Gamma \vdash (a,b) : \Sigma x{:}A.,B}\ (\Sigma\text{-I})$$

Proving $\forall$ means building a function, and proving $\exists$ means supplying a witness together with a proof about it. Dependent types are what make the proof constructive: the $\Sigma$-introduction literally contains the witness.

**Conversion.** The rule

$$\dfrac{\Gamma \vdash M : A \quad A \equiv_{\beta\eta} B}{\Gamma \vdash M : B}\ (\mathsf{Conv})$$

says a proof of $A$ is a proof of anything computationally equal to $A$. In logical terms, definitional equality is free: propositions that differ only by computation are the _same_ proposition. This is also why checking $\Gamma \vdash M : \mathrm{Vec}(2+2)$ against $\mathrm{Vec}(4)$ succeeds with no extra proof. Normalization of types becomes part of the logic, which is the main thing that separates dependent type theory from first-order logic with a separate proof language.

**Subsumption.** In systems with subtyping or cumulative universes, e.g. $\mathsf{Type}_i \le \mathsf{Type}_{i+1}$, subsumption corresponds to a weakening-like admissible rule: a proof at one universe level is accepted at a higher one.

$$\dfrac{\Gamma \vdash M : A \quad A \le B}{\Gamma \vdash M : B}\ (\mathsf{Sub})$$

This is logically harmless but has to be handled carefully so the system stays decidable and coherent.

## Where the picture gets harder

**1. Decidability collapses with expressiveness.** The landscape of inference problems:

- Simply typed $\lambda$-calculus: inference is decidable (Hindley-Milner gives principal types for the let-polymorphic fragment).
- System F: inference is undecidable (Wells, 1999), which is why practical languages require annotations at polymorphic binders.
- Dependent types: inference requires solving higher-order unification problems, which is undecidable in general. Practical systems (Coq, Agda, Lean) use bidirectional checking plus unification heuristics and ask the user for annotations at the hard spots.
- Inhabitation: for simple types it is decidable (propositional intuitionistic logic, PSPACE-complete). For dependent types it is undecidable, since it amounts to proving arbitrary theorems of the theory.

So "wholesome proof searching" is only a _semi_-decision procedure in the dependent case, and tactic languages and elaborators exist because of this.

**2. Inference is not purely deductive.** Type inference for polymorphic or dependent systems involves unification: generating metavariables (existential placeholders) and solving constraints. That is closer to _proof construction with unknowns_ than to pure derivation. The elaborator fills in implicit arguments, so the final proof term is more detailed than what the user wrote.

**3. Proof relevance.** Under propositions-as-types, proofs are first-class and distinct. Two terms of type $A$ may be different proofs. Systems like Coq and Lean separate computationally relevant types from the proof-irrelevant $\mathsf{Prop}$ universe to keep extraction and definitional equality manageable. Without that distinction, "proving $A$" and "computing a value of type $A$" are the same activity.

**4. Equality is the delicate part.** Definitional equality (checked by $\mathsf{Conv}$) is a _meta-level_ notion, while propositional equality $\mathrm{Id}_A(a,b)$ is an _object-level_ proposition requiring proof. Whether to make them coincide (extensional type theory, which gives up decidable checking) or keep them apart (intensional, as in HoTT and Coq) is one of the major design choices.

## A worked example

Take the proposition $\forall A, B.;(A \times B) \to (B \times A)$. Proof search reads the goal structure and proceeds by the introduction rules:

$$\begin{aligned}  
&\lambda A.,\lambda B.,\lambda p.,(\pi_2,p,\ \pi_1,p) \  
&\quad : \Pi A{:}\mathsf{Type}.,\Pi B{:}\mathsf{Type}.,(A \times B) \to (B \times A)  
\end{aligned}$$

Each step is forced by the shape of the goal: $\Pi$-I three times, then $\times$-I, then $\times$-E to fill each component. This is the "easy" end, where the search is essentially deterministic (focused proof search).

## Summary

The right slogan is:

- **Type checking** is proof checking.
- **Type synthesis** is reading off what a proof proves.
- **Inhabitation / elaboration** is proof search.
- **Conversion** is built-in computation inside the logic.

Treating inference as the whole logical process is a fair description of what a proof assistant's elaborator does end to end, since it combines these activities. But keeping them separate matters, because they have very different decidability and complexity profiles, and that separation explains most of the design of real systems.
___

# Bidirectional Types and Proof Search

Now we will explain bidirectional rules for $\Pi/\Sigma$ in full, how unification and metavariables fit the proof-search picture, or the $\mathsf{Prop}$ versus $\mathsf{Type}$ split.

Here are all three, since they fit together: bidirectional rules say how a checker is organized, metavariables say how the gaps get filled, and the $\mathsf{Prop}$/$\mathsf{Type}$ split says which parts of a proof the system cares about.

## 1. Bidirectional rules for $\Pi$ and $\Sigma$

A bidirectional checker has two judgments:

- $\Gamma \vdash M \Leftarrow A$ (**check**): $A$ is an input, and you verify $M$ against it.
- $\Gamma \vdash M \Rightarrow A$ (**synthesize**): $M$ is an input, and $A$ is an output.

The guiding principle is that **introduction forms are checked and elimination forms are synthesized**. A $\lambda$ or a pair does not carry enough information to determine its own type ($\lambda x.\,x$ has many types), but it can be checked against a known goal. An application or projection has a head whose type determines everything else.

**Formation:**

$$\dfrac{\Gamma \vdash A \Leftarrow \mathsf{Type} \quad \Gamma, x{:}A \vdash B \Leftarrow \mathsf{Type}}{\Gamma \vdash \Pi x{:}A.\,B \Rightarrow \mathsf{Type}}\ (\Pi\text{-F})$$

**$\Pi$ introduction (check).** The binder needs no annotation, because the domain comes from the goal:

$$\dfrac{\Gamma, x{:}A \vdash M \Leftarrow B}{\Gamma \vdash \lambda x.\,M \Leftarrow \Pi x{:}A.\,B}\ (\Pi\text{-I})$$

**$\Pi$ elimination (synthesize).** Synthesize the head, reduce its type to weak head normal form to expose the $\Pi$, then check the argument against the domain:

$$\dfrac{\Gamma \vdash M \Rightarrow C \quad C \longrightarrow^{*} \Pi x{:}A.\,B \quad \Gamma \vdash N \Leftarrow A}{\Gamma \vdash M\,N \Rightarrow B[N/x]}\ (\Pi\text{-E})$$

**$\Sigma$ introduction (check).** The type of the second component depends on the first, so the checker must use the first component's *value*:

$$\dfrac{\Gamma \vdash a \Leftarrow A \quad \Gamma \vdash b \Leftarrow B[a/x]}{\Gamma \vdash (a,b) \Leftarrow \Sigma x{:}A.\,B}\ (\Sigma\text{-I})$$

**$\Sigma$ elimination (synthesize).** The second projection's type mentions the first projection:

$$\dfrac{\Gamma \vdash p \Rightarrow C \quad C \longrightarrow^{*} \Sigma x{:}A.\,B}{\Gamma \vdash \pi_1\,p \Rightarrow A}\ (\Sigma\text{-E}_1)
\qquad
\dfrac{\Gamma \vdash p \Rightarrow C \quad C \longrightarrow^{*} \Sigma x{:}A.\,B}{\Gamma \vdash \pi_2\,p \Rightarrow B[\pi_1\,p/x]}\ (\Sigma\text{-E}_2)$$

Two rules glue the modes together:

$$\dfrac{\Gamma \vdash M \Rightarrow A' \quad A' \equiv_{\beta\eta} A}{\Gamma \vdash M \Leftarrow A}\ (\mathsf{Switch})
\qquad
\dfrac{\Gamma \vdash A \Leftarrow \mathsf{Type} \quad \Gamma \vdash M \Leftarrow A}{\Gamma \vdash (M : A) \Rightarrow A}\ (\mathsf{Ann})$$

$(\mathsf{Switch})$ is where **conversion** happens. It is the only place the checker needs to decide $\equiv_{\beta\eta}$. $(\mathsf{Ann})$ is where the user pays for lost inference, by writing a type annotation.

In proof terms, the forward reasoning (eliminations) is synthesized, and the goal-directed reasoning (introductions) is checked. This is why "apply a lemma, then split the goal" looks the way it does in a proof assistant.

## 2. Unification and metavariables as proof search

Users do not write every argument. In `id 3` the polymorphic argument $A$ is implicit. The elaborator inserts a **metavariable** $?A$ in its place:

$$\mathsf{id}\ ?A\ 3 \quad\text{with } \Gamma \vdash ?A : \mathsf{Type}$$

Checking $3 \Leftarrow\ ?A$ produces the constraint $?A \equiv \mathbb{N}$, and solving it instantiates $?A := \mathbb{N}$.

**The logical reading.** A metavariable is an *existential placeholder in a proof*. It is a hole in the proof term, and it comes with the context $\Gamma$ it may use and the type (proposition) it must have:

$$?m \;:\; (\Gamma \vdash A)$$

This is exactly what a **goal** is in a proof assistant. The two activities are the same machinery:

| Activity | What happens |
|---|---|
| Elaboration | Metavariables are created for implicit arguments and solved by unification |
| Tactic proving | Tactics (`apply`, `refine`) create new metavariables for subgoals and instantiate old ones |
| Proof state | A set of unsolved metavariables (open goals) |
| Finished proof | A term with no unsolved metavariables |

Instantiating $?m := t$ is the dependent analogue of providing a witness in an $\exists$-introduction, except the witness is discovered by constraint solving rather than supplied.

**Why it is hard.** Constraints can involve applied metavariables, such as $?F\ x\ y \equiv t$. In general this is higher-order unification, which is undecidable and may have no most general solution. The workhorse is **Miller pattern unification**: when $?F$ is applied to *distinct bound variables*, the solution is unique and most general:

$$?F\ x\ y \equiv t \quad\Longrightarrow\quad ?F := \lambda x.\,\lambda y.\,t$$

(provided $t$ mentions no other free variables). Constraints outside the pattern fragment are postponed until more is known, or solved by heuristics, and that is why elaboration is sometimes unpredictable and users sometimes must supply an annotation.

**Trust boundary.** The elaborator is heuristic and may be wrong or incomplete. After it finishes, the *kernel* re-checks the fully elaborated, metavariable-free term using only the simple rules above. Soundness depends on the small kernel, not on the elaborator. This is the "de Bruijn criterion."

## 3. $\mathsf{Prop}$ versus $\mathsf{Type}$

**The problem.** Under propositions-as-types, proofs are ordinary terms, so two proofs of the same proposition may be *different elements*. This is usually unwanted. Consider the "subset" $\Sigma x{:}\mathbb{N}.\,\mathrm{Even}(x)$. Its elements are pairs $(n, p)$ where $p$ proves $n$ even. If proofs are relevant, $(4, p)$ and $(4, q)$ are distinct elements for distinct proofs $p, q$, even though we only care that $4$ is even.

**The fix.** Systems like Coq and Lean add a separate universe of propositions, $\mathsf{Prop}$ (written $\mathsf{Sort}\ 0$ in Lean, with $\mathsf{Type}_i = \mathsf{Sort}\ (i+1)$), with a special rule:

$$\dfrac{\Gamma \vdash P : \mathsf{Prop} \quad \Gamma \vdash p : P \quad \Gamma \vdash q : P}{\Gamma \vdash p \equiv q : P}\ (\mathsf{Proof\ Irrelevance})$$

Any two proofs of a $\mathsf{Prop}$ are definitionally equal. Inhabitation of $P$ is then a yes/no matter rather than a question of *which* inhabitant.

**Consequences:**

1. **Erasure.** Computation never depends on a proof, so $\mathsf{Prop}$ terms can be deleted when extracting a program. A subset $\Sigma x{:}A.\,P(x)$ with $P : \mathsf{Prop}$ then carries the same data as $A$ itself.

2. **Impredicativity.** $\mathsf{Prop}$ is closed under quantification over *any* universe:

$$\dfrac{\Gamma \vdash A : \mathsf{Sort}\ i \quad \Gamma, x{:}A \vdash B : \mathsf{Prop}}{\Gamma \vdash \Pi x{:}A.\,B : \mathsf{Prop}}$$

   So $\forall X{:}\mathsf{Type}.\,P(X)$ is still a proposition. This is the logical analogue of System F's impredicative polymorphism.

3. **Restricted elimination.** The price is that you cannot freely turn a proof into data. Compare the two existentials:

| | $\exists x{:}A.\,P(x)$ in $\mathsf{Prop}$ | $\Sigma x{:}A.\,P(x)$ in $\mathsf{Type}$ |
|---|---|---|
| Meaning | "some such $x$ exists" | "here is such an $x$, with proof" |
| Can extract the witness? | No (squashed) | Yes, via $\pi_1$ |
| Different proofs distinguishable? | No | Yes |

   A proof of the $\mathsf{Prop}$-valued $\exists$ can only be used to prove *other propositions*, not to compute a witness. There are exceptions ("singleton elimination") for proof types that carry no information, such as $\mathsf{False}$, conjunction, and equality.

4. **Classical axioms stay safe.** Because $\mathsf{Prop}$ is erased, adding excluded middle there does not break computation. Adding it to informative $\mathsf{Type}$ would give non-computable "witnesses" and, together with impredicativity, can cause inconsistency.

**The homotopy-theoretic version.** Univalent foundations achieve the same separation differently. A *mere proposition* is a type with at most one inhabitant, and the propositional truncation $\lVert A \rVert$ plays the role of the $\mathsf{Prop}$-valued $\exists$, while $\Sigma$ stays the informative version.

## Connecting back to your question

Putting the three pieces together: bidirectional rules organize *checking* the proof, metavariables handle the *search* for missing pieces, and $\mathsf{Prop}$ versus $\mathsf{Type}$ decides which parts of the proof are real data and which are only ever asked "does one exist?"

If you want, I can work a full example through the bidirectional rules with metavariables, or show how the predicative/impredicative choice affects the encoding of $\wedge$, $\vee$, $\exists$.