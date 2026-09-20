---
title: Language Specifications as Equational Theories
source: A Framework for Modular, Extensible, Equivalence-Preserving Compilation (Jamner, 2022)
chapter: "3.1 Language Specifications"
pages: "21–24"
tags: [type-theory, automated-reasoning, equational-theories, generalized-algebraic-theories]
---

[[book-guidelines|↩ Back to guidelines]]

## What does it mean to "define a language" as a list?

[[Pyrosomes-Design-Philosophy]] establishes the term grammar (n-ary tagged trees plus metavariables) and explains *why* a list-shaped representation is the right one for extensibility. This article covers what actually goes *in* that list: the three kinds of rules a language specification is built from, and how STLC — the running example throughout the thesis — looks once fully spelled out in this form.

**What breaks without a uniform rule format:** if sort rules, term rules, and equations were three structurally different kinds of objects with no common shape, you couldn't concatenate a source language's rule list with a target language's the way [[Compilers-as-Finite-Maps]] and [[The-Preserving-Predicate-and-Modularity-Theorems]] both rely on doing. The whole "language extension = list concatenation" story requires all rules — no matter what they're declaring — to be items of one common, appendable collection.

## The three rule kinds

A **language specification** in Pyrosome is an ordered list of inference rules, each one being one of:

1. **Sort rules** — declare a new syntactic class together with its well-formedness judgment (e.g., "there is a sort of types," "there is a sort of expressions in a given context at a given type").
2. **Term rules** — declare a new syntactic form (a new tag `c` in the `#c term...` grammar) and the conditions, above the line, under which a term built with that tag is well-formed. As covered in [[Pyrosomes-Design-Philosophy]], each term rule also marks which of its metavariables must be *written down* by a user (explicit) versus *inferred* (implicit).
3. **Equation rules** — declare that two terms of the same sort are equal, under some context of premises. This is the mechanism by which operational behavior (beta-reduction, eta-expansion, heap-access semantics) enters the picture — *not* as a separate reduction relation bolted onto the syntax, but as more entries in the very same list.

### Worked example: STLC as a Pyrosome rule list

The thesis presents STLC first in ordinary inference-rule notation (Figure 3-1):

$$
\dfrac{\vdash A\ \mathrm{type} \qquad \vdash B\ \mathrm{type}}{\vdash A \to B\ \mathrm{type}}
\qquad
\dfrac{\Gamma \vdash e : A \to B \qquad \Gamma \vdash e' : A}{\Gamma \vdash e\,e' : B}
$$

$$
\dfrac{\Gamma, x{:}A \vdash e : B}{\Gamma \vdash \lambda(x{:}A).\,e : A \to B}
\qquad
\dfrac{\Gamma, A \vdash e : B \qquad \Gamma \vdash v : A}{\Gamma \vdash (\lambda(x{:}A).e)\,v = e[v/x] : B}
$$

— then encodes each rule almost verbatim as a Pyrosome list entry (Figure 3-2), for instance the application rule:

```
[:| "G" : #"env",
    "A" : #"ty",
    "B" : #"ty",
    "e" : #"exp" "G" (#"->" "A" "B"),
    "e'" : #"exp" "G" "A"
    -----------------------------------------------
    #"app" "e" "e'" : #"exp" "G" "B"                ];
```

and the beta rule as an *equation* entry (note the `:=` marking it as an equation rule, versus `:|` for term/sort rules, and the rule name `"beta"` in parentheses):

```
[:= "G" : #"env", "A" : #"ty", "B" : #"ty",
    "e" : #"exp" (#"ext" "G" "A") "B",
    "v" : #"val" "G" "A"
    ----------------------------------------------- ("beta")
    #"app" (#"ret" (#"lambda" "A" "e")) (#"ret" "v")
    = #"exp_subst" (#"snoc" #"id" "v") "e"
    : #"exp" "G" "B"                               ]]
```

Two details in this encoding matter beyond faithfully mirroring the paper presentation:

- **Every metavariable above the line must be given an explicit sort.** This is not optional bookkeeping — it's what lets the framework state well-formedness and equivalence-preservation obligations generically over *any* rule, without special-casing what kind of thing a metavariable happens to stand for.
- **STLC's own value/expression distinction is maintained explicitly**, via separate sorts (`#"val"` vs `#"exp"`) and an explicit `#"ret"` operator that injects a value into the expression sort. This isn't incidental — it's the same distinction that later makes the call-by-value restriction on beta ([[Equivalence-Preservation-versus-Contextual-Equivalence]]) statable at all: you need "value" to be a syntactically distinguishable category before you can restrict a rule to apply only when an argument is one.

## Closing an equational theory: reflexive-transitive-symmetric-congruence closure

A raw list of equation rules like `"beta"` above are *axioms* — they say two specific term shapes are equal, but they don't yet say anything about, e.g., two terms that are equal by *chaining* several axioms, or by applying an axiom *inside* a larger surrounding term. Pyrosome closes the set of declared axioms under:

- **Reflexivity** — every term is equal to itself.
- **Transitivity** — if $t_1 = t_2$ and $t_2 = t_3$, then $t_1 = t_3$.
- **Symmetry** — if $t_1 = t_2$ then $t_2 = t_1$.
- **Congruence** — if $t_1 = t_2$, then $C[t_1] = C[t_2]$ for any surrounding context $C$ built from the language's own term rules.

The result is a genuine equivalence relation, and it's this closed relation — not the raw axiom list — that [[The-Preserving-Predicate-and-Modularity-Theorems]] requires a compiler to preserve. Notably, congruence is the one closure property that, per [[Compilers-as-Finite-Maps]], comes "for free" during the equivalence-preservation proof, precisely because compilers are defined via substitution-invariant finite maps rather than arbitrary functions.

**What breaks without full closure, specifically congruence:** if a compiler only had to preserve the *literal listed axioms* and not their congruence closure, it would be sound to compile $(\lambda x.e)\,v$ and $e[v/x]$ to equivalent target terms while compiling, say, `f applied to (λx.e) v` and `f applied to e[v/x]` to *unrelated* target terms — because "beta holds inside a function argument position" was never separately asserted. Real programs use equations deep inside larger expressions constantly; without congruence, compiler correctness would only ever apply to top-level redexes, which is close to useless.

## Implicit vs. explicit subterms, revisited as a term-rule mechanism

[[Pyrosomes-Design-Philosophy]] introduced the explicit/implicit distinction conceptually; here it's worth being precise about *where* it lives syntactically. In `#"app" "e" "e'" : #"exp" "G" "B"`, the term rule's conclusion lists only `"e"` and `"e'"` after the tag name `#"app"` — even though `"G"`, `"A"`, and `"B"` are all declared as metavariables above the line and are logically part of the term's full specification. Pyrosome's convention is: **everything above the line is a genuine subterm of the AST; only the ones repeated below the line (next to the tag) are ones a user must supply directly** — the rest must be recoverable by inference machinery (see [[Proof-Automation-and-Elaboration]]). This is a per-rule design decision, not a global one: `#"lambda"` requires its input type `"A"` explicitly (Figure 3-2), trading brevity for simpler inference, exactly as covered in the design-philosophy article.

## Extension: languages compose by list concatenation

Because a language specification is *just* a list, extending STLC with a global-store feature (Figure 3-3 — `get`/`set`, heap-indexed equations $\Gamma \vdash \langle H, E[\mathrm{get}\ n]\rangle = \langle H, E[H(n)]\rangle : A$) is literally list concatenation: take STLC's list, append State's rules (plus State's own dependencies — heaps and evaluation contexts, detailed in [[Extending-the-Case-Study]]). The thesis writes this as $L_1 + L_2$, e.g. $\mathrm{STLC} + \mathrm{State}$.

One structural constraint makes this safe: **a rule can only reference sorts, terms, and metavariables declared *earlier* in the list.** This ordering discipline is what guarantees that appending new rules at the end never invalidates anything already proved about the earlier prefix — a later rule literally cannot mention (and therefore cannot break an invariant about) something that didn't exist yet when the prefix was checked. It's the same discipline that makes Theorem 1 (compiler extension, in [[The-Preserving-Predicate-and-Modularity-Theorems]]) provable at all.

## Grounding: what this looks like as code

**Rust (primary) — a language as a `Vec` of rule variants:**

```rust
enum Rule {
    Sort { name: String /* + well-formedness judgment, elided */ },
    Term {
        tag: String,
        premises: Vec<(String, Sort)>,   // metavariables + their sorts, above the line
        explicit: Vec<String>,           // which of those the user must write down
        conclusion_sort: Sort,
    },
    Equation {
        name: String,
        premises: Vec<(String, Sort)>,
        lhs: Term,
        rhs: Term,
        sort: Sort,
    },
}

type Language = Vec<Rule>;

/// Extension really is concatenation — the whole point.
fn extend(base: &Language, addition: &Language) -> Language {
    let mut l = base.clone();
    l.extend(addition.iter().cloned());
    l
}
```

The ordering constraint ("only reference earlier entries") would be enforced by validating each new `Rule`'s premises against only the prefix of the `Vec` that precedes it — a check you'd want to run once, at definition time, rather than trust by convention.

**Lean (secondary) — equational theories as `Setoid`/quotient reasoning.** The reflexive-transitive-symmetric-congruence closure of a set of axioms is exactly what Lean's `Setoid` machinery (or a hand-rolled inductive `Eq'` relation with those four constructors plus a per-term-rule congruence constructor) captures. If you've ever proven `Trans`, `Symm`, and congruence lemmas to get `simp` or `rw` to work smoothly through a custom equivalence, you've already built a smaller instance of exactly this closure.

```lean
inductive TermEq : Term → Term → Prop
  | refl (t) : TermEq t t
  | symm {t1 t2} : TermEq t1 t2 → TermEq t2 t1
  | trans {t1 t2 t3} : TermEq t1 t2 → TermEq t2 t3 → TermEq t1 t3
  | beta {A e v} : TermEq (app (ret (lam A e)) (ret v)) (subst v e)
  | congr_app {e1 e2 e1' e2'} :
      TermEq e1 e1' → TermEq e2 e2' → TermEq (app e1 e2) (app e1' e2')
  -- one congr_* constructor per term rule, in general
```

**Python (tertiary sketch)** — a language as literal appendable data:

```python
stlc = [sort("ty"), sort("exp"), term_rule("app", ...), equation_rule("beta", ...)]
stlc_state = stlc + [term_rule("get", ...), term_rule("set", ...), equation_rule("get-eval", ...)]
```

## Where this leads

This rule-list representation is the concrete object that [[Compilers-as-Finite-Maps]] compiles against (one table entry per term rule) and that [[The-Preserving-Predicate-and-Modularity-Theorems]] proves properties of (one proof obligation per rule). The ordering discipline introduced here — "only reference earlier entries" — reappears as the enabling condition for the compiler-extension theorem.

For the workbench's elaborator/refinement-type project (`type-theory`): this is a template for how to represent your own surface language's typing rules as *extensible data* rather than a fixed Rust enum with exhaustive matches — directly useful if the refinement-type surface language is expected to grow features (new base types, new logical connectives in refinements) without invalidating prior soundness proofs.
