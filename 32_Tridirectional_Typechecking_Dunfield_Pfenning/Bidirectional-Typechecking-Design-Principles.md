---
title: Bidirectional Typechecking Design Principles
source: Tridirectional Typechecking (Dunfield & Pfenning, POPL '04)
chapters: Introduction, Section 2 ("The Core Language"), pp. 1-3
tags: [type-theory, bidirectional-typechecking, judgments, mode-correctness, curry-howard]
---

[[book-guidelines|↩ Back to guidelines]]

# Bidirectional Typechecking Design Principles

## The problem: where do the types in a checker come from?

Suppose you're writing a typechecker for a language with a rich type system — intersections, unions, dependent products indexed by refinements. The obvious algorithmic shape is a function `infer(e) -> Type` that walks a term and produces its type. That works fine for `x + y`, but it breaks almost immediately on anything higher-order. Take `λx. x`. What's its type? You can't infer `A → A` from the syntax of the lambda alone — `A` is genuinely underdetermined by the term. Full type inference (à la Hindley-Milner) solves this with **unification**: collect constraints as you walk the term, then solve a system of equations to pin down the unknowns.

The paper's stance, stated bluntly in Section 2, is that unification is off the table:

> "Avoiding unification or similar techniques associated with full type inference is fundamental to the design of the bidirectional system we propose here."

Two reasons are given, and both matter for anyone building a real checker. First, for the expressive systems under consideration — intersections, unions, index-refined dependent types — full type inference is often **undecidable**, so a unification-based approach isn't just inconvenient, it can fail to terminate or fail to exist as an algorithm at all. Second, even where inference *is* decidable, unification is a **global** propagation mechanism: a type variable gets pinned down by a constraint that might come from anywhere in the term, so when something goes wrong, the error message points at the unification failure site, not at the place a programmer would recognize as the actual mistake. If you've ever stared at an OCaml or Haskell type error that blames the wrong line, that's this exact failure mode.

**What breaks without a fix:** if you try to build a checker for intersections, unions, and quantified refinements using naive unification-based inference, you get an algorithm that may not terminate, and when it does terminate and reports an error, the error is often useless. The alternative the paper proposes doesn't eliminate the need for *some* input — annotations still have to come from somewhere — but it makes that need explicit and local instead of implicit and global.

## The fix: split one judgment into two

Bidirectional typechecking's central move is deceptively simple: stop asking "what is the type of `e`?" as a single question, and instead recognize that a checker actually needs to answer two different questions depending on what it already knows.

In a pure type-assignment system the judgment is just `e : A` — "term `e` has type `A`," with no notion of direction. A bidirectional system splits this into two judgments:

$$e \uparrow A \qquad \text{("$e$ synthesizes $A$")}$$
$$e \downarrow A \qquad \text{("$e$ checks against $A$")}$$

Read operationally, these correspond to two mutually recursive functions. `synth(e) -> Option<Type>` takes a term and either produces a type or fails — this is genuine inference, but only ever invoked where the term actually carries enough information to succeed. `check(e, A) -> bool` takes a term *and* a candidate type, and only has to verify consistency — a strictly easier problem, because it never has to invent information the term doesn't provide.

This immediately answers the "where do the types come from" question: they come from the *type being checked against*, which is available because checking is only ever invoked in a context where something upstream — a top-level annotation, a lambda's parameter type inside a checked function type, a case scrutinee's branch — already supplies it. The system never needs to solve for an unknown; it only ever propagates a known one downward, or reads a known one back upward.

```rust
enum Term {
    Var(String),
    Lam(String, Box<Term>),
    App(Box<Term>, Box<Term>),
    Pair(Box<Term>, Box<Term>),
    Fst(Box<Term>),
    Snd(Box<Term>),
    Unit,
    Ann(Box<Term>, Type), // (e : A)
}

fn synth(ctx: &Context, e: &Term) -> Result<Type, TypeError> { /* e ↑ A */ }
fn check(ctx: &Context, e: &Term, expected: &Type) -> Result<(), TypeError> { /* e ↓ A */ }
```

## The design principle: mode correctness, and where it comes from

Splitting the judgment into two directions is not yet a design *principle* — it's just a syntactic convenience unless something disciplines which rules go in which bucket. The paper calls the discipline **mode correctness**, a term borrowed from logic programming:

- For any rule with conclusion $e \uparrow A$, the premises must be enough to *determine* $A$ — you should never need to guess it.
- For any rule with premise $e \downarrow A$, $A$ must be *known in advance*, before the rule recurses into $e$.

This is a consistency requirement — it tells you a rule set won't get stuck asking for information it doesn't have — but by itself it's not yet a recipe for *which* rules to write. For that, the paper reaches into natural deduction and its **introduction/elimination** structure, which happens to line up with mode correctness almost perfectly:

- An **introduction rule** builds a value of a type from its parts — read bottom-up, it *decomposes* the goal type into subgoals. Since the type being built is known before you start (it's the goal), checking a term against its type using the type's own introduction rule is automatically mode correct.
- An **elimination rule** consumes a value of a type to produce something else — read top-down, it *uses* a type that's already available from a synthesized subterm. So synthesizing a type for a term using an elimination rule is automatically mode correct too, because the type being eliminated came from a recursive `synth` call, not from nowhere.

Under Curry-Howard, introduction rules correspond to a type's **constructors** and elimination rules to its **destructors**. So the recipe crystallizes into one sentence: *constructors are checked, destructors synthesize.*

Concretely, for products $A * B$:

$$\dfrac{\Gamma \vdash e_1 \downarrow A_1 \qquad \Gamma \vdash e_2 \downarrow A_2}{\Gamma \vdash (e_1, e_2) \downarrow A_1 * A_2} \; (*I) \qquad\qquad \dfrac{\Gamma \vdash e \uparrow A * B}{\Gamma \vdash \mathrm{fst}(e) \uparrow A} \; (*E_1) \qquad \dfrac{\Gamma \vdash e \uparrow A * B}{\Gamma \vdash \mathrm{snd}(e) \uparrow B} \; (*E_2)$$

Building a pair is checked (the pair's type is decomposed into the types of its components); projecting from a pair is synthesized (the pair already carries a known type, from which the projection reads off half). And for functions:

$$\dfrac{\Gamma, x{:}A \vdash e \downarrow B}{\Gamma \vdash \lambda x. e \downarrow A \to B} \; (\to I) \qquad\qquad \dfrac{\Gamma \vdash e_1 \uparrow A \to B \qquad \Gamma \vdash e_2 \downarrow A}{\Gamma \vdash e_1\,e_2 \uparrow B} \; (\to E)$$

A lambda is checked against its arrow type — the argument type $A$ is read off the goal and used to extend the context, then the body is checked against $B$. Application synthesizes: the function position must synthesize an arrow type (it's presumed to already be "known," typically a variable or a nested application), and once you know the arrow's domain, you can *check* the argument against it — this is why, in practice, applications like `e1 e2` rarely need their own annotation: the function head bottoms out in a variable lookup, which synthesizes by the `(var)` rule.

```lean
-- The correspondence is exact: an introduction rule *is* a checking rule,
-- an elimination rule *is* a synthesizing rule.
inductive Synth : Ctx → Term → Ty → Prop
  | var   : Ctx.lookup Γ x = some A → Synth Γ (.var x) A
  | app   : Synth Γ f (.arrow A B) → Check Γ a A → Synth Γ (.app f a) B
  | fst   : Synth Γ e (.prod A B) → Synth Γ (.fst e) A

inductive Check : Ctx → Term → Ty → Prop
  | lam   : Check (Γ.extend x A) e B → Check Γ (.lam x e) (.arrow A B)
  | pair  : Check Γ e1 A → Check Γ e2 B → Check Γ (.pair e1 e2) (.prod A B)
```

This is worth pausing on if you're used to Lean or Coq: their kernel elaborators make exactly this same directional split internally (often called "elaboration with expected type" vs. "synthesis mode"), even though the surface language doesn't always advertise it. When Lean's elaborator processes `fun x => x + 1` against an expected type `Nat → Nat`, it's running a checking-mode elaboration in the same sense as `(\lambda I)$ above; when it elaborates a bare application `f x` with no expected type, it's running synthesis, bottoming out at `f`'s already-known type the same way `(\to E)$ does.

## Where the two directions meet: subsumption

Checking and synthesis are not sealed off from each other — most terms need to cross between them at some point. The bridge is the **subsumption rule**:

$$\dfrac{\Gamma \vdash e \uparrow A' \qquad \Gamma \vdash A' \le A}{\Gamma \vdash e \downarrow A} \; (\mathrm{sub})$$

Read it as: "if you're asked to check $e$ against $A$, but $e$ is actually something that synthesizes — a variable, a projection, an application — then synthesize its type $A'$ and confirm $A' \le A$." In the simplest case without subtyping, this collapses to checking $A' = A$; with subtyping in the picture, it's enough that every value of $A'$ is also a value of $A$.

This is where the paper's "avoid unification" claim earns its keep. By the time `(sub)` fires, *both* types are already fully known — $A'$ from the synthesis premise, $A$ from the ambient checking goal — so the subtyping judgment $A' \le A$ never has to invent or solve for anything; it's a pure decision procedure over two concrete types. No constraint set, no substitution to compute, no occurs-check. This is the structural reason bidirectional systems sidestep unification's machinery entirely: subsumption is the *only* place the two modes touch, and at that single point, both sides of the comparison are already closed terms in the syntax of types.

```rust
fn check(ctx: &Context, e: &Term, expected: &Type) -> Result<(), TypeError> {
    match e {
        Term::Lam(x, body) => { /* (→I): decompose expected, recurse checking */ }
        Term::Pair(e1, e2) => { /* (*I): decompose expected, recurse checking */ }
        _ => {
            // Fallback: subsumption. e doesn't match a checking rule,
            // so synthesize and compare.
            let synthesized = synth(ctx, e)?;
            subtype(ctx, &synthesized, expected)
        }
    }
}
```

**What breaks without subsumption:** without it, checking and synthesis would be two disconnected judgments — you could never use a variable (which only synthesizes) where a checked position is expected (e.g. as a function argument), which would make the two modes useless in practice. Subsumption is precisely the glue that lets a single term language support both.

## The gap: what still needs annotations

Mode correctness explains how the two directions cooperate, but it doesn't make annotations disappear entirely. The paper is explicit about where the discipline still needs help: a fully "normal" term (in the proof-theoretic sense — no destructor applied directly to a constructor, no redex) needs no annotations beyond the outermost one, because the introduction/elimination alternation carries information down and back up cleanly. But wherever a *destructor is applied to a constructor* — a redex, like `fst((e1, e2))` written directly instead of through a variable — the system momentarily needs a type it can't derive purely by the checking/synthesis handoff, and an explicit annotation `(e : A)` has to supply it. This gap is exactly what Section 4 ("[[Contextual-Typing-Annotations|Contextual Typing Annotations]]") exists to close in a much more general form, once intersections and quantified index types make even that naive annotation insufficient.

## Where this leads

This design-principle layer is the foundation the rest of the paper builds on, and it's worth tracking three separate threads forward:

- **Section 2's concrete syntax and semantics** (the sibling article, "[[The-Core-Language-and-Its-Bidirectional-Typing|The Core Language and Its Bidirectional Typing]]") instantiates this exact checking/synthesis split for the base language — products, functions, unit, datatypes — with the operational semantics needed to later prove type safety.
- **Section 3's property types** (intersections, refined datatypes, dependent products) all extend the language *while preserving* the introduction/elimination discipline established here — e.g. intersection introduction is checked because it behaves like an introduction rule, even though (unusually) it isn't itself a genuine Curry-Howard correspondence.
- **Section 3's indefinite property types** (unions, existentials) are exactly the place where this two-judgment discipline *stops being sufficient* — mode correctness alone can't handle a term that needs its evaluation-position subterm visited and synthesized *before* the surrounding checking judgment can proceed. That gap is the motivation for the paper's namesake "third direction," covered in "[[Indefinite-Property-Types-and-the-Third-Direction|Indefinite Property Types and the Third Direction]]."

For the elaborator/verifier project this vault is building toward, this is the load-bearing idea: bidirectional typing *is* the mechanism by which a checker avoids running general unification for ordinary typing, reserving unification-like machinery (metavariables, pattern unification) for the strictly harder problem of implicit-argument and instance resolution during elaboration — exactly the boundary Lean's elaborator draws between its bidirectional core and its metavariable-context unifier.
