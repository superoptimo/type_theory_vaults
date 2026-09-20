---
title: Term Representation and Core Data Structures
source: Elaboration in Dependent Type Theory (de Moura, Avigad, Kong, Roux, 2015)
chapter: Section 3.1–3.2, pp. 12–15
tags: [elaboration, dependent-type-theory, term-representation, de-bruijn, metavariables, constraints, lean]
---

[[book-guidelines|↩ Back to guidelines]]

# Term Representation and Core Data Structures

## Why the algorithm needs a vocabulary before it needs a procedure

Section 2 of the paper described elaboration entirely from the *outside*: what it has to accomplish — infer implicit arguments, solve higher-order unification problems, respect reduction, resolve type classes, disambiguate overloads, insert coercions — without saying anything about how a program would actually carry any of that out. Section 3 turns to the *inside*, and before it can describe an algorithm it first has to answer a much more basic question: what is a "term" as a piece of data the elaborator actually manipulates, and what does a "hole" — the thing elaboration is supposed to fill in — look like as a value in memory?

This matters because the naive answer is expensive. If you represent a partially-elaborated expression the way a textbook would — variables as names, holes as some kind of sentinel, substitution as a recursive tree-walk — you end up paying for renaming, capture-avoidance, and context bookkeeping at every single step of a search procedure that will backtrack over that expression thousands of times per definition. The paper is explicit about this concern: it says the goal of Section 3 is to describe an algorithm that both does everything Section 2 asked for *and* "is quite fast." Data structure design is not incidental to that goal — it's the first lever they pull.

So Section 3.2 lays out four things, in order: the term grammar itself, the *locally nameless* representation strategy used to implement variables, the treatment of metavariables (holes) and environments, and the vocabulary of [[Constraints-and-Justifications|constraints and justifications]] that the rest of the algorithm is built on. This article covers all four, deliberately stopping short of the runtime behavior *of* reduction (weak head normal form, unfolding, stuck-term resolution) — that's [[Computational-Behavior-and-Reduction]]'s territory, using these same terms as its raw material.

## The term grammar

The paper fixes a single grammar for every term the elaborator will ever touch, elaborated or not:

$$t, s ::= \ell \mid x \mid f \mid {?m} \mid \mathrm{Type}_u \mid t\,s \mid \lambda x{:}s,\, t \mid \Pi x{:}s,\, t$$

Reading this left to right: $\ell$ is a *free variable* (also called a local constant), $x$ is a *bound variable*, $f$ is a *constant* — a reference into a global environment, parametrized by a list of universe terms — $?m$ is a *metavariable* (a hole), $\mathrm{Type}_u$ is a universe at level $u$, $t\,s$ is application, $\lambda x{:}s, t$ is abstraction, and $\Pi x{:}s, t$ is the dependent function type.

Two things are worth pausing on before moving to representation. First, notice that *metavariables are first-class citizens of the grammar itself* — a hole isn't a side-channel annotation bolted onto the term language, it's a production of the grammar on equal footing with variables and application. This is what makes it possible to write down a term like `?m x y` and have it just be a term, typeable and substitutable like any other. Second, the grammar deliberately doesn't distinguish "preterms" (what the parser hands off, still containing ambiguity the user meant to leave implicit) from fully-elaborated terms — a preterm becomes a term of *this* grammar with metavariables standing in for the not-yet-resolved parts, and "term" and "preterm-with-holes" are, structurally, the same kind of object at different stages of instantiation.

If you've worked with an AST in a compiler before, the closest intuition is: this is what your AST looks like *after* it's already been converted from surface syntax, and it's also literally your representation of "syntax with typed holes" — no separate `Hole` node needed, since `?m` already is one.

### A Rust sketch

```rust
enum Term {
    Local(LocalId),                 // ℓ — free variable / local constant
    Bound(u32),                     // x — de Bruijn index
    Const(GlobalId, Vec<Universe>), // f — a constant, with universe params
    Meta(MetaId),                   // ?m — a metavariable (hole)
    Sort(Universe),                 // Type_u
    App(Box<Term>, Box<Term>),      // t s
    Lambda(Box<Term>, Box<Term>),   // λx:s, t  — domain, then body with x bound
    Pi(Box<Term>, Box<Term>),       // Πx:s, t
}
```

Notice `Bound` carries a raw `u32`, not a name — that's the de Bruijn index discussed next — while `Local` and `Meta` carry opaque identifiers rather than inline data. That split is the whole point of "locally nameless," and it's worth understanding *why* the paper insists on it before looking at the code that implements it.

## Locally nameless: why two different representations for two different kinds of variable

A naive term representation uses names for every variable — bound and free alike — the way source code does. This is simple to read but creates two persistent headaches for an implementation: *capture-avoidance* (renaming a bound variable when it would otherwise shadow a free one during substitution) and *alpha-equivalence* (deciding that `λx, x` and `λy, y` are "the same term" requires either normalizing names or writing every comparison up to renaming).

The paper's answer is to use **different representations for the two roles a variable can play**:

- **Bound variables** are represented as **de Bruijn indices** — plain numbers counting binder depth, with no name at all. There is exactly one canonical bound variable of index $k$; alpha-equivalence becomes literal structural equality, and there's nothing to accidentally capture because there's no name to collide.
- **Free variables** (the paper's "local constants," $\ell$) instead carry a **unique identifier and their own type**, stored right there in the variable rather than looked up in an ambient context.

This is the "locally nameless" style: *locally* (under a binder) you're nameless (de Bruijn indices), *globally* (outside any binder, or once a bound variable has been temporarily pulled out from under its binder to be worked on) you have a name (a unique free-variable id). Storing the type directly on the free variable is a deliberate design choice with a real payoff the paper calls out explicitly: it "remov[es] the need to carry around contexts in the type checker and normalizer." A term is self-describing — you never need to thread an environment mapping variables to types alongside every term you inspect, because a free variable already knows its own type.

The paper credits this approach (citing prior work, reference [21] in the paper) with simplifying the implementation considerably, specifically by minimizing the number of places explicit de Bruijn index arithmetic has to happen — shifting indices up when you push a term under a new binder, or down when you pull a substituted term out from one, are exactly the error-prone, off-by-one-prone operations that locally nameless representations are designed to quarantine into a small number of well-tested functions (`abstract` and `instantiate`, covered in [[Computational-Behavior-and-Reduction]]) rather than scattering them across the whole codebase.

### The intuition in Python, before the formalism

If you've ever implemented a tiny interpreter with closures, you've probably felt this tension already. A purely name-based environment representation:

```python
# Name-based: simple, but capture-prone
class Lambda:
    def __init__(self, param_name, body):
        self.param_name = param_name
        self.body = body

def substitute(term, name, replacement):
    # must worry: does `replacement` contain a free variable
    # that collides with a binder inside `term`? Need alpha-renaming.
    ...
```

versus a locally-nameless-flavored one:

```python
class Bound:            # de Bruijn index — no name, no collision possible
    def __init__(self, index):
        self.index = index

class Local:             # free variable — unique id AND its type, self-contained
    def __init__(self, uid, ty):
        self.uid = uid
        self.type = ty

def substitute(term, target_uid, replacement):
    # only Local(uid) nodes matching target_uid are touched;
    # Bound indices are untouched by substitution of a free variable,
    # and shifted only when crossing a binder — a single well-tested rule.
    ...
```

The second version can't accidentally capture a variable, because there's no name-collision to have — a bound variable is just "the thing 3 binders up," full stop, regardless of what any enclosing lambda happens to be called.

### And in Lean itself

Lean's own kernel term representation (the very language this paper's elaborator is targeting) follows exactly this discipline — bound variables as de Bruijn indices, free variables/local constants carrying their own type — which is part of why the paper can lean on "the standard locally nameless approach" as prior art rather than re-justifying it from scratch. A Lean-style expression like

```lean
-- conceptually: λ (x : Nat), f x  — the bound x has no name at the term level,
-- it is purely positional (de Bruijn index 0 inside the body)
fun x => f x
```

is, underneath the pretty-printer, exactly the `Bound`/binder pair from the Rust sketch above — the surface name `x` is a display convenience the parser/pretty-printer maintains, not something the underlying term representation stores.

## What a metavariable actually is, and the "closed terms only" rule

A metavariable $?m$ represents a hole: some piece of information — an implicit argument, an inferred predicate, an as-yet-unknown proof term — that elaboration is responsible for filling in. Structurally a metavariable is just another kind of variable, with **a unique identifier and a type**, exactly parallel to how free variables carry an identifier and a type. The one operation that matters for a metavariable is *instantiation*: assigning it a concrete term.

Here the paper makes a design decision that has real teeth: **only closed terms — terms with no free (bound) variables dangling loose — may ever be assigned to a metavariable.** The justification given is precise and worth quoting the shape of: this restriction "guarantees that operations such as $\beta$-reduction and metavariable instantiation commute." In plain terms — if you could assign a metavariable an *open* term (one that still refers to variables bound somewhere in its original context), then whether you reduce first and then instantiate, or instantiate first and then reduce, could give you different answers, because instantiating would need to correctly re-index or re-capture those dangling bound variables relative to wherever the metavariable itself sits. Forcing metavariable assignments to be closed sidesteps that whole class of bug by construction: a closed term means the same thing no matter where in a larger term it gets plugged in.

But this creates an obvious problem: most interesting holes genuinely *do* depend on their surrounding context. A hole for an implicit argument inside `λ(x:A)(y:B), _` obviously needs to be able to mention `x` and `y` to be useful — you can't fill it with a closed term if the right answer is literally `x`. The paper's resolution: **on creation, a metavariable is immediately applied to the free variables of the context where it appears.** A hole inside the context $(x:A)(y:B)$ isn't represented as a bare `?m` — it's represented as `?m x y`, and the type of `?m` itself is the *closed* Pi-type $\Pi(x{:}A)(y{:}B), C$ (where $C$ is whatever the hole's expected type is). The metavariable `?m` is closed and generic over any $x, y$; the *application* `?m x y` is what actually stands in for the context-dependent hole, and it's the application — not the bare metavariable — that later gets to look like it "depends on" $x$ and $y$.

There's a further wrinkle worth surfacing because it shows the same trick applied a level up: if even the hole's *expected type* $C$ isn't known yet at preprocessing time, the elaborator doesn't stall — it manufactures *another* fresh metavariable, $?m_t : \Pi(x{:}A)(y{:}B), \mathrm{Type}_{?u}$ (itself parametrized by a fresh universe metavariable $?u$, for the same reason), giving $?m : \Pi(x{:}A)(y{:}B), ?m_t\,x\,y$. Not knowing the type of a hole is handled by exactly the same mechanism as not knowing its value — another closed, context-generic metavariable, applied to the context.

A term is called **fully elaborated** when it contains no metavariables at all — that's the terminal state the whole solving procedure ([[The-Constraint-Solving-Procedure]]) is driving toward.

```python
# Illustrating the "apply to context" trick, not literal Lean/paper code
class MetaVar:
    def __init__(self, uid, closed_type):
        self.uid = uid
        self.type = closed_type   # e.g. Π(x:A)(y:B), C — always closed

def hole_in_context(context_vars, expected_type):
    # expected_type may itself be unknown — represented by a further metavariable
    m = MetaVar(fresh_id(), pi_over(context_vars, expected_type))
    return App.chain(Meta(m.uid), context_vars)  # ?m x y — this is the actual hole
```

## Environments, declarations, constants

Outside of local binders, the elaborator works against a persistent **environment**: a sequence of **declarations**. The kernel recognizes exactly three kinds — *axioms*, *definitions*, and *inductive families* — each with a unique identifier and, potentially, a list of universe parameters it's polymorphic over. Every axiom carries a type; every definition carries both a type and a value (its body). A **constant** ($f$ in the grammar) is simply a reference into this environment by identifier, instantiated at a particular choice of universe arguments — it's the mechanism by which a term can refer to something defined once, elsewhere, rather than inlining its whole definition everywhere it's used. Whether and when a constant gets *unfolded* back to its definition during elaboration is governed by reducibility annotations, which belong to [[Computational-Behavior-and-Reduction]] rather than here — this article is only concerned with the fact that constants exist as a distinct case in the grammar and point somewhere.

## Constraints and justifications: the currency the solver runs on

The preprocessing phase (covered fully in [[The-Preprocessing-Phase]]) doesn't just create metavariables — it emits **constraints** that record what those metavariables are obligated to satisfy. Two kinds exist, and getting their shape right here matters because the entire solving procedure in [[The-Constraint-Solving-Procedure]] is essentially a loop that consumes and rewrites exactly these two data types.

**Unification constraints** enforce typing/definitional-equality obligations — "this term must equal that term." Written $\langle t \approx s, j\rangle$, where $j$ is a **justification**. A justification isn't optional bookkeeping; it's what makes error messages point at real code and what makes *non-chronological backtracking* possible (the search strategy detailed in [[The-Constraint-Solving-Procedure]]) — by recording *why* a constraint exists, the solver can, on failure, jump back past irrelevant choice points directly to the one that's actually implicated, instead of undoing decisions one at a time in the order they were made. There are three kinds of justification:

- **asserted** — attached to constraints generated directly during preprocessing (this constraint exists because the source code said so);
- **assumption** — attached fresh whenever the solver makes a genuine choice (a case split): "if this branch is wrong, the assumption made *here* is the thing to blame";
- **join**, written $j_1 \bowtie j_2$ — the union of two justifications, produced whenever a step of reasoning draws on two prior facts at once.

A **substitution** is a finite map from metavariables to *justified* assignments, $?m \mapsto \langle t, j\rangle$, with $t$ necessarily closed (per the rule above) and $j$ recording why the assignment was made. Substitutions aren't inert data — applying one to a constraint is itself justification-preserving: applying $?m \mapsto \langle t, j_m\rangle$ to $\langle r \approx s, j\rangle$ doesn't just substitute $t$ for $?m$ in $r$ and $s$, it produces the new constraint $\langle r[?m := t] \approx s[?m := t],\ j \bowtie j_m\rangle$ — the provenance trail grows every time information flows through a constraint, so that by the time a constraint is finally resolved (or fails), its justification is a complete, traceable history of every fact that contributed to it.

**Choice constraints** are the other kind, and they're the mechanism behind overloading, coercion resolution, and — critically — type class inference (see [[Type-Classes-and-Class-Inference]] and [[Overloading-and-Coercions]] for the mechanisms built on top of this primitive). Written $\langle ?m\,\ell : t \text{ in } f,\ j\rangle$: $?m$ is the metavariable to be resolved, $\ell$ the free variables of its context (exactly the "applied to context" trick from above), $t$ the type of $?m\,\ell$, and $f$ a *procedure* — given the hole, its type, and a substitution, $f$ produces a (possibly unbounded) *stream of alternatives*, each alternative itself being a list of constraints representing one candidate way of filling the hole. This is the structural seed of "try each overload/instance/coercion in turn, backtracking on failure" — a choice constraint doesn't pick an answer, it enumerates a search space.

One refinement matters enough to flag here even though its full payoff belongs to later articles: a choice constraint can be marked **ondemand**. An ondemand constraint's procedure $f$ is only invoked once every metavariable in its type $t$ has already been instantiated by other means — it's *ready* once $t$ is metavariable-free, and *postponed* otherwise. A choice constraint without this flag is a **regular** choice constraint, used directly for resolving overloaded symbols where there's no reason to wait. The ondemand flag is precisely what lets type class inference wait until enough type information has accumulated to search meaningfully, rather than firing a Prolog-style search over the entire class hierarchy the instant a class constraint is created — the mechanism [[Type-Classes-and-Class-Inference]] builds on.

## How this fits into the rest of the paper

```
Section 2: what elaboration must accomplish
        │
        ▼
Section 3.2 (THIS ARTICLE): the vocabulary —
    term grammar, locally-nameless variables,
    metavariables (closed-only, applied-to-context),
    unification & choice constraints, justifications
        │
        ├──► Section 3.3 → reduction, unfolding, stuck terms  [[Computational-Behavior-and-Reduction]]
        ├──► Section 3.4 → simp: constraint simplification     [[The-Constraint-Simplification-Procedure]]
        ├──► Section 3.5 → preprocessing: preterm → term+constraints  [[The-Preprocessing-Phase]]
        └──► Sections 3.6–3.7 → the solver: priority queue,
             nonchronological backtracking over these very
             constraint/justification objects                 [[The-Constraint-Solving-Procedure]]
```

Everything downstream in the paper is, in a real sense, just operations *over* the data structures fixed here: `simp` rewrites constraints into simpler constraints of the same two shapes; preprocessing is the process that manufactures the first batch of them; the solver is a loop that picks one off a queue, tries to satisfy it, and on failure walks back through exactly the justification chains this section defined. Getting the representation right — de Bruijn indices for the cheap, capture-free case; self-typed free variables to avoid context-threading; closed-only metavariables for a commuting reduction/instantiation story; and justification-carrying constraints for principled backtracking — is what makes it possible for the rest of the algorithm to be, as the paper insists it must be, both correct and fast.
