---
title: "Taxonomy of Typed Lambda Calculus and Logic aliases"
source: "Nederpelt Geuvers, Type Theory and Formal Proof"
tags: [lambda-calculus,type-theory,logic]
---

# Taxonomy of Typed Lambda Calculus and Logic

Definitions follow Nederpelt & Geuvers. The note is organised in layers: [[#1. Object-language syntax]] → [[#2. Judgements]] → [[#3. Inference systems]] → [[#4. Derivations]] → [[#5. Clauses and definitions]] → [[#6. Cross-cutting distinctions]].

> [!summary] Order of the concepts type → pre-typed term → statement → declaration → context → judgement → derivation → legal term

> [!warning] Terminology A term with a type annotation is **not** a _sentence_. It is a [[#Statement]] $M:\sigma$. In logic, a _sentence_ is a closed formula (see [[#Formula and sentence]]).

---

## 1. Object-language syntax

### Variables and terms

> [!definition] Term (untyped) Fix an infinite set $V$ of variables. The set $\Lambda$ of $\lambda$-terms is the least set such that:
> 
> 1. (Variable) $u \in V \Rightarrow u \in \Lambda$
> 2. (Application) $M, N \in \Lambda \Rightarrow (M,N) \in \Lambda$
> 3. (Abstraction) $u \in V,\ M \in \Lambda \Rightarrow (\lambda u.,M) \in \Lambda$

In grammar form:

$$\Lambda = V \mid (\Lambda\Lambda) \mid (\lambda V.,\Lambda)$$

The three numbered items are the **clauses** of an [[#Inductive definition]]. Related notions: free and bound variables, closed terms, substitution, $\alpha$-equivalence.

### Types

> [!definition] Type The set $\mathbb{T}$ of simple types is generated over a set of type variables: $$\mathbb{T} = V \mid (\mathbb{T} \to \mathbb{T})$$

Example: $\alpha \to \beta$ and $(\alpha \to \beta) \to \alpha$.

### Pre-typed terms

> [!definition] Pre-typed term (Def. 2.4.1) Since bound variables now carry types, the term set changes: $$\Lambda_{\mathbb{T}} = V \mid (\Lambda_{\mathbb{T}},\Lambda_{\mathbb{T}}) \mid (\lambda V{:}\mathbb{T}.,\Lambda_{\mathbb{T}})$$

They are "pre-typed" because being syntactically valid does not mean being typable: $\lambda x{:}\alpha.,x,x$ belongs to $\Lambda_{\mathbb{T}}$ but is not legal, since $x,x$ would need $\alpha = \alpha \to \beta$.

### Statement

> [!definition] Statement A **statement** is $M:\sigma$ with $M \in \Lambda_{\mathbb{T}}$ and $\sigma \in \mathbb{T}$. The term $M$ is the **subject** and $\sigma$ is the **type**.

A statement is syntax: a pair (subject, type) in $\Lambda_{\mathbb{T}} \times \mathbb{T}$. It can be false or unprovable.

> [!note] Statement versus term A statement is **not** a specialization of a term. It is a pair that _contains_ a term as its subject. The specialization relation holds between statements and declarations.

### Declaration

> [!definition] Declaration A **declaration** is a statement whose subject is a variable: $x:\sigma$.

### Context

> [!definition] Context A **context** $\Gamma$ is a finite list of declarations with distinct subjects: $$\Gamma = x_1{:}\sigma_1,\ \dots,\ x_n{:}\sigma_n$$

### Formula and sentence

These belong to the logic side of the correspondence.

|Concept|Definition|Example|
|---|---|---|
|Formula|Well-formed expression of the logic's grammar (denotes a proposition)|$\forall x.,P(x) \Rightarrow Q(x)$|
|Sentence|A _closed_ formula (no free variables)|$\forall x.,P(x)$|
|First-order term|Expression denoting an object|$f(x,y)$|

Under the [[#Curry–Howard correspondence]], types play the role of formulas and the statement $M:A$ reads "$M$ is a proof of $A$".

### Summary table

|Concept|Definition|Example|
|---|---|---|
|Type|element of $\mathbb{T}$|$\alpha \to \beta$|
|Pre-typed term|element of $\Lambda_{\mathbb{T}}$|$\lambda x{:}\alpha.,x,x$|
|Statement|$M:\sigma$|$\lambda x{:}\alpha.,x : \alpha \to \alpha$|
|Declaration|$x:\sigma$|$x:\alpha$|
|Context|list of declarations|$x{:}\alpha,\ y{:}\alpha \to \beta$|

---

## 2. Judgements

> [!definition] Judgement A **judgement** is an assertion whose form is fixed by the system. It is a different category from a formula: it cannot be nested under connectives.

A [[#Statement]] is not yet a judgement. The judgement $\Gamma \vdash M:\sigma$ asserts that the statement $M:\sigma$ is **derivable** from the declarations in $\Gamma$.

|Judgement form|Meaning|
|---|---|
|$\Gamma \vdash M:\sigma$|Typing judgement: under $\Gamma$, $M$ has type $\sigma$|
|$\Gamma \vdash A$|Intuitionistic sequent (logical reading, proof term erased)|
|$\Gamma \vdash \Delta$|Classical sequent (Gentzen): from all of $\Gamma$, at least one of $\Delta$|
|$\Gamma \vdash A\ \mathsf{type}$, $\Gamma\ \mathsf{ctx}$|Well-formedness judgements (dependent types)|
|$M \to_\beta N$, $M =_\beta N$|Reduction and equality judgements|
|$M \Downarrow v$|Evaluation judgement (big-step)|

Terminology: $\Gamma$ is the **antecedent**, $\Delta$ is the **succedent**, and $\vdash$ is the **turnstile**. In simply typed $\lambda$-calculus the right side is a single type, and the multi-conclusion form only appears in classical sequent calculus.

---

## 3. Inference systems

> [!definition] Inference rule A rule has the form $$\dfrac{J_1 \quad \cdots \quad J_n}{J}\ (\mathsf{Name})$$ where $J_1,\dots,J_n$ are the **premises** (judgements, not necessarily formulas) and $J$ is the **conclusion**.

- **Axiom**: a rule with zero premises.
- **Side condition**: a restriction that is not a judgement, for example $x \notin \mathrm{dom}(\Gamma)$.
- **Rule schema versus instance**: metavariables $\Gamma, A, M$ are instantiated to give concrete instances.
- **Inference system (calculus)**: a set of rules that inductively defines which judgements are derivable.
- **Rule families**: introduction and elimination (natural deduction), left and right (sequent calculus), structural rules (weakening, contraction, exchange), and cut.

The rules of simply typed $\lambda$-calculus:

$$\dfrac{}{\Gamma,, x{:}A \vdash x : A}\ (\mathsf{Var})$$

$$\dfrac{\Gamma,, x{:}A \vdash M : B}{\Gamma \vdash \lambda x{:}A.,M : A \to B}\ (\to\mathrm{I})$$

$$\dfrac{\Gamma \vdash M : A \to B \quad \Gamma \vdash N : A}{\Gamma \vdash M,N : B}\ (\to\mathrm{E})$$

---

## 4. Derivations

> [!definition] Derivation tree A **derivation tree** (proof tree) is a finite tree whose nodes are judgements, where each node follows from its children by an instance of a rule. Leaves are axioms (or discharged hypotheses) and the root is the **end-judgement**.

Example:

$$\dfrac{\dfrac{}{x{:}A \vdash x : A}\ (\mathsf{Var})}{\vdash \lambda x{:}A.,x : A \to A}\ (\to\mathrm{I})$$

A derivation with an application, for $\lambda x{:}A \to B.,\lambda y{:}A.,x,y$. Write $\Gamma_0 = x{:}A \to B,\ y{:}A$:

$$\dfrac{\dfrac{\dfrac{\dfrac{}{\Gamma_0 \vdash x : A \to B}\ (\mathsf{Var}) \quad \dfrac{}{\Gamma_0 \vdash y : A}\ (\mathsf{Var})}{\Gamma_0 \vdash x,y : B}\ (\to\mathrm{E})}{x{:}A \to B \vdash \lambda y{:}A.,x,y : A \to B}\ (\to\mathrm{I})}{\vdash \lambda x{:}A \to B.,\lambda y{:}A.,x,y : (A \to B) \to A \to B}\ (\to\mathrm{I})$$

- **Derivable, provable, inhabited**: $\Gamma \vdash M:\sigma$ has a derivation. A type is _inhabited_ if some closed term has it.
- **Legal (typable) term**: there exist $\Gamma$ and $\sigma$ such that $\Gamma \vdash M:\sigma$ is derivable. This is where pre-typed terms become legal terms.
- **Properties of derivations**: height, size, and admissible versus derivable rules (cut elimination is the key example).
- **Induction on derivations** is the standard proof technique: weakening, substitution, subject reduction.

---

## 5. Clauses and definitions

### Clause

"Clause" has two common meanings.

1. **Logic programming and resolution**: a disjunction of literals $L_1 \vee \cdots \vee L_n$. A _Horn clause_ has at most one positive literal, and a _definite clause_ has exactly one: $H \leftarrow B_1,\dots,B_n$. This has the same shape as an [[#3. Inference systems|inference rule]].
2. **Definitions by cases**: each equation or rule of an inductive or recursive definition. The three clauses of $\Lambda$ are an example, and so are the clauses defining substitution:

$$\begin{aligned} x[x:=N] &= N \ y[x:=N] &= y \quad (y \neq x) \ (M_1,M_2)[x:=N] &= M_1[x:=N]\ M_2[x:=N] \end{aligned}$$

### Kinds of definition

#### Inductive definition

The smallest set closed under given rules: grammars, derivability, reduction. Example: $\Lambda$, $\mathbb{T}$, $\Lambda_{\mathbb{T}}$.

#### Recursive definition

A function defined by structural recursion on an inductive set. Examples: substitution, free variables, type erasure.

#### Definitional equality

- $\equiv$ and $:=$ are meta-level (abbreviation, syntactic identity).
- $=_\beta$ is object-level equality, derived by rules.

> [!note] Meta-level versus object-level The calculus is the **object language**. Everything used to talk about it (induction, definitions, informal proofs) is the **metalanguage**.

---

## 6. Cross-cutting distinctions

|Dimension|Options|
|---|---|
|Typing style|**Church** (annotated: $\lambda x{:}A.,M$) versus **Curry** (unannotated: $\lambda x.,M$, types inferred)|
|Proof system|Natural deduction, sequent calculus, Hilbert-style|
|Logic|Intuitionistic (single succedent) versus classical (multiple succedents)|
|Dynamics|Reduction ($\beta$, $\eta$), normalization, confluence|
|Metatheory|Subject reduction, progress, strong normalization, canonicity|

### Curry–Howard correspondence

|Type theory|Logic|
|---|---|
|type|formula|
|term|proof|
|inhabited type|provable formula|
|$\beta$-reduction|proof normalization|

---

## Related notes

- Simply Typed Lambda Calculus
- Natural Deduction
- Sequent Calculus
- Curry–Howard Correspondence
- Substitution and Alpha-Equivalence