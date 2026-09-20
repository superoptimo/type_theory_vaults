---
title: Pyrosome's Design Philosophy
source: A Framework for Modular, Extensible, Equivalence-Preserving Compilation (Jamner, 2022)
chapter: "Abstract; 3.1 Language Specifications"
pages: "iii, 21–24"
tags: [type-theory, generalized-algebraic-theories, pyrosome, syntax-representation]
---

[[book-guidelines|↩ Back to guidelines]]

## Why name a compiler-verification framework after a sea creature?

The thesis opens with a footnote that is doing real conceptual work, not just naming trivia: *pyrosomes are tiny colonial organisms that connect to each other to form tube-shaped colonies up to 60 feet in length*. Each individual pyrosome (a "zooid") is a complete, independently functioning organism; the colony is not one big animal designed top-down, it's many small identical units that happen to compose into something large. The author's framework takes its name from this because it makes the same architectural bet about compilers: **a large, feature-rich verified compiler should be assembled from many small, independently-verified pieces, not designed and proved as one monolithic artifact.**

This is the same idea as [[The-Problem-of-Extensible-Compiler-Verification]], but stated as a design *commitment* rather than a critique of prior work. Two concrete choices follow from taking it seriously, and this article covers both: (1) how to *represent* a language such that "one small independent piece" is even a well-defined, addable unit, and (2) how to keep that representation faithful to what a language designer would write on paper, so the formalism doesn't become its own new source of rigidity.

**What breaks without this commitment:** if you instead pick a representation where "the language" is one big recursively-defined datatype (the classic approach — a single `Expr` enum, or a single mutually-recursive set of inductive definitions in Coq), then *by construction* there is no such thing as "one small independent piece" — every definition and every proof by structural induction over that datatype has to mention every constructor, because the datatype itself doesn't have modular boundaries. This is precisely the "expression problem" (Wadler 1998; Krishnamurthi et al. 1998): once you fix your representation as one closed inductive type, you can add new *operations* over it easily (write a new function) but not new *cases* (extending the datatype) without touching every existing function that pattern-matches on it exhaustively. Pyrosome's answer is to represent a language as *data* — a list — rather than as a fixed inductive type, precisely so a "new case" is an append, not a structural change.

## Generalized algebraic theories: languages as lists of inference rules

The formal vehicle for this is a **generalized algebraic theory (GAT)**, following Sterling (2019). The choice is deliberate and stated explicitly: the author considered alternative generic formalizations (Felleisen's expressive-power framework, discussed in [[Related-Frameworks-and-Future-Directions]]) but picked GATs because their presentation matches how researchers already write languages on paper — as **lists of inference rules** — while still being precise enough to support machine-checked, extensible metatheory. This is not a formalism chosen for its cleverness; it's chosen because staying close to the paper-and-pencil presentation is what keeps the framework usable, and because "list" is a data structure with an obvious, cheap notion of extension (concatenation) — exactly the operation [[The-Problem-of-Extensible-Compiler-Verification]] identified as missing from prior work.

## Terms: n-ary syntax trees, tagged with sorts

Pyrosome's core syntactic representation is deliberately minimal:

$$
\begin{aligned}
x, c &\in \mathrm{string} \\
\mathrm{term} &::= \#c\ \mathrm{term}\ldots \;\mid\; x \;\mid\; (\mathrm{term})
\end{aligned}
$$

Every term is either (a) a **named syntactic form** `#c term...` — a constructor name `c` applied to zero or more subterms — or (b) a bare **metavariable** `x`. That's the entire grammar of terms, for *any* object language you might define. Nothing about "lambda," "application," or "if-then-else" is baked into this grammar; those are all just particular constructor names `c` that a specific language module chooses to declare. This is what "deeply embedded" means in the abstract's phrase "a formal, deeply embedded notion of programming languages": the framework doesn't have a notion of "an expression" or "a type" wired into its metatheory at all — it has one uniform notion of "n-ary tagged tree," and object languages are just *data* that says which tags exist and what they mean.

Each term additionally carries a **sort** — the combination of its syntactic class (is this a type? an expression? a value?) and the well-formedness judgment that governs that class. Sorts, like terms, are user-declared, not fixed by the framework.

## The one distinction that has to be built in by hand: object variables vs. metavariables

There is exactly one place where the framework's syntax needs a distinction that isn't just "more user-declared structure," and getting it right is what makes the rest of the design work: **object-language variables** (the `x` a programmer writes in `λx. e`, subject to binding, scoping, and alpha-equivalence) versus **framework-level metavariables** (the `x` that stands for "any term of a given sort, to be filled in later" — the same device used throughout term rules and compiler definitions, per [[Compilers-as-Finite-Maps]]).

Most programming-languages formalisms leave this distinction informal — a metavariable in an inference rule "obviously" means "any term of that shape," and the reader is trusted to keep it apart from object-language variable binding by context. Pyrosome makes the distinction *syntactic and explicit*: metavariables are first-class citizens of the term grammar (the bare `x` case above), while object-language binding structure is defined entirely *inside* a user-declared language module and never touches the framework's own metavariable machinery. The framework doesn't need to know anything about how a particular language binds variables — that's the language module's problem, not the metatheory's.

In the actual Coq mechanization, **object-language variables are represented with de Bruijn indices** (position-based, rather than name-based, so alpha-equivalent terms are represented identically and substitution avoids capture bugs) — but the thesis *presents* everything in named-variable form throughout the rest of the document, for readability. Concretely: the term you'd write on paper as $\lambda(x:A).\langle x, x\rangle$ is represented internally as

```
#"lambda" "A" (#"pair" #"hd" #"hd")
```

where `"A"` is a metavariable (a placeholder for "whatever type gets supplied"), and `#"hd"` is de Bruijn index $0$ — literally "the head of the environment, viewed as a list" — standing for the innermost bound variable both times `x` is used. The named-form presentation and the de Bruijn internal encoding are two views of the *same* term; the thesis picks whichever is more legible for the point being made, and the reader should mentally translate between them rather than treating named form as a separate, informal thing.

**What breaks without a de Bruijn (or equivalent) encoding:** name-based representations of bound variables require capture-avoiding substitution, alpha-renaming machinery, and a notion of "fresh variable" scattered throughout every proof that touches binders — a well-known, large source of subtle bugs in mechanized metatheory (the "POPLmark challenge" exists specifically because this is hard to get right). De Bruijn indices sidestep the entire category of bugs by making alpha-equivalent terms *syntactically identical*, at the cost of index-shifting arithmetic during substitution — a cost the thesis pays once, generically, in its substitution calculus (see [[Extending-the-Case-Study]]'s treatment of explicit substitution), rather than per-language.

## Implicit vs. explicit subterms

A term rule (see [[Language-Specifications-as-Equational-Theories]] for the full definition) lists every metavariable it depends on *above* the line — but not every one of those has to be something a user writes down when constructing a term. Pyrosome lets a term rule mark some subterms as **inferred** rather than **explicit**, listed after the syntactic form's name below the line. For application, the environment and both types are inferable from context, so a user only supplies `"e"` and `"e'"`; for lambda, the thesis chooses to require the input type `"A"` be written explicitly, trading a small amount of verbosity for simpler inference (deferred to tactics — see [[Proof-Automation-and-Elaboration]]).

This is a genuinely bidirectional-typing-flavored design decision, even though the thesis doesn't frame it in those terms: "explicit" subterms are the ones a user provides as *input* (checking mode), and "inferred" subterms are the ones the elaboration machinery must *produce* as output (inference mode) before a term rule's obligations can be discharged. Recognizing term rules this way is directly relevant to this workbench's elaborator project — the explicit/inferred split here is structurally the same design point as which arguments a bidirectional type-checker takes in synthesis mode vs. checking mode.

## Grounding: what this design looks like as code

**Rust (primary).** The term grammar as a single, uniform enum — the "deeply embedded" idea made concrete:

```rust
/// One grammar for EVERY object language: a tagged n-ary tree, or a metavariable.
/// Object languages differ only in which constructor *names* they populate —
/// nothing here is STLC-specific, CPS-specific, or otherwise fixed.
enum Term {
    Meta(String),                    // framework-level metavariable
    Node(String, Vec<Term>),         // #c term... — tag + subterms
}

/// Object-language variables live INSIDE a language's own encoding,
/// as de Bruijn indices, represented just like any other constructor:
/// e.g. `Node("hd", vec![])`, `Node("succ", vec![Node("hd", vec![])])` for index 1.
/// The framework's `Term` type has no special case for "a bound variable" —
/// that distinction is entirely a convention of the language module using it.
```

A traditional "one big `Expr` enum per language" design would instead give every language its own hardcoded Rust type — exactly the rigidity this framework is designed to avoid. The uniform `Term` type here is what makes "a language is a list of rules about tags" a coherent, checkable notion at all: **language extension is `Vec::extend` on a rule list, never a change to `Term` itself.**

**Lean (secondary — GATs and inductive families).** Lean users building dependent inductive families already work with a close cousin of a sort-indexed GAT: a Lean inductive type indexed by another type is exactly "a sort with a well-formedness judgment classifying its terms." The thesis's `#"exp" "G" "A"` (the sort of expressions in context `G` at type `A`) reads naturally as a Lean-style indexed family `Exp : Ctx → Ty → Type`, and the term rules read as that family's constructors — except that in Pyrosome, the "constructors" are themselves data (list entries), not baked into a fixed `inductive` declaration, which is precisely what makes them extensible after the fact in a way a closed Lean `inductive` block is not.

**Python (tertiary sketch).**

```python
# A GAT-style term, mirroring the two-case grammar exactly.
class Meta:
    def __init__(self, name): self.name = name

class Node:
    def __init__(self, tag, subterms): self.tag, self.subterms = tag, subterms

# lambda(x:A). <x, x>  as de Bruijn form:
term = Node("lambda", [Meta("A"), Node("pair", [Node("hd", []), Node("hd", [])])])
```

## Where this leads

Everything downstream depends on this representation choice being right: [[Language-Specifications-as-Equational-Theories]] formalizes what a "list of rules" actually contains (sort rules, term rules, equation rules); [[Compilers-as-Finite-Maps]] reuses the same metavariable machinery to define compilation; and [[The-Preserving-Predicate-and-Modularity-Theorems]] is only provable "one goal per rule" *because* a language is represented as a list of independently-meaningful rules rather than a closed inductive type.

For the workbench's elaborator project (`type-theory`): the explicit/inferred subterm split previewed here is the same design axis your bidirectional elaborator will need for every syntactic form — deciding, per constructor, which arguments the surface syntax supplies and which the unifier must solve for.
