---
title: "Statics and Dynamics"
source: "Practical Foundations for Programming Languages (Robert Harper, 2012)"
chapters: "Chapter 4 (Statics, pp. 39–44); Chapter 5 (Dynamics, pp. 45–54); Chapter 7 (Evaluation Dynamics, pp. 61–66)"
tags: [type-theory, programming-languages, operational-semantics, statics, dynamics, harper-pfpl]
---

# [[Symbols-and-Dynamic-Binding#Statics|Statics]] and [[Exceptions#Dynamics|Dynamics]]

[[book-guidelines|↩ Back to guidelines]]

## Why a language needs two definitions, not one

Suppose you want to define a programming language with total precision — precise enough that "is this program legal?" and "what does this program do?" are both mathematical questions with mathematical answers, not appeals to what some particular compiler happens to do. You need two separate specifications, because those are two separate questions:

1. **Which programs are well-formed?** — a question you can answer by *inspecting the program's text*, without running anything.
2. **What does a well-formed program do when executed?** — a question you can only answer by *simulating execution*.

Harper calls the first the **statics** and the second the **dynamics**. This split is not a stylistic preference; it reflects something real about how essentially every practical language processor works: a compiler or interpreter first parses and type-checks (rejecting some programs outright), and only then executes what's left. Harper names this the **phase distinction**:

> "Most programming languages exhibit a phase distinction between the static and dynamic phases of processing. The static phase consists of parsing and type checking to ensure that the program is well-formed; the dynamic phase consists of execution of well-formed programs."

If you've used any statically-typed language, you already live inside this distinction daily: `cargo build` fails on a type error *before* your program ever runs a single instruction; `python foo.py` might crash at runtime on a `TypeError` that a static checker could have caught in principle. The entire pitch of a type system is that it lets the static phase *predict* something about the dynamic phase — specifically, that certain classes of nonsense (adding a number to a string, calling something that isn't a function) will never arise once execution starts. Whether that prediction is *actually kept* is a separate theorem — **[[Type-Safety|type safety]]** — which is the subject of the next chapter in the book (and the next topic in this vault) and depends on statics and dynamics being defined so that they *cohere*. This article is about how each of the two is defined in isolation, and how the book gives you three genuinely different (but provably equivalent) ways to define dynamics.

Harper works throughout Chapter 4–5 with a small illustrative language, $\mathcal{L}\{\texttt{num str}\}$ — numbers and strings, with addition, multiplication, concatenation, length, and a `let` binder. It's deliberately minimal so the *machinery* of statics/dynamics is visible without being buried in language features.

---

## Part I — Statics: type systems as inductive definitions of typing judgments

### The typing judgment

The static phase is not "a set of ad hoc checks" — it is itself an **inductive definition** in exactly the sense built up in the earlier chapters on judgments and rules (see [[Inductive Definitions and Rule Induction]] and [[Hypothetical and General Judgments]] if you've covered those). The book is explicit about this continuity: the statics of $\mathcal{L}\{\texttt{num str}\}$ "consists of an inductive definition of generic hypothetical judgments of the form"

$$\vec{x} \mid \Gamma \vdash e : \tau,$$

where $\Gamma$ is a **typing context** — a finite map from variables to types, written as a comma-separated list of hypotheses $x:\tau$ — and $\vec{x}$ is the (generic) set of variables in scope. Reading this judgment as a sentence: "under the assumptions in $\Gamma$, the expression $e$ has type $\tau$."

Why does the type of `x` in `x + n` depend on *context* at all, rather than being some intrinsic property of the syntax alone? Because `x` is a variable — a placeholder — and placeholders only make sense relative to an environment that says what they stand for. This is precisely why the judgment is *hypothetical*: it's an assertion made under assumptions, structurally the same move as "assume $x$ is a natural number, then prove ...". If you've written a type checker, `Γ` is exactly the symbol table you thread through your `typecheck` function.

**[[Plotkins-PCF-and-Partial-Computation#Grounding|Grounding]] — the typing context as an environment.** In Rust, Python, and Lean, this is the same idea realized three ways:

```rust
// Rust: Γ is literally a HashMap from variable names to types.
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
enum Ty { Num, Str }

#[derive(Debug)]
enum Expr {
    Var(String),
    NumLit(i64),
    StrLit(String),
    Plus(Box<Expr>, Box<Expr>),
    Cat(Box<Expr>, Box<Expr>),
    Let(Box<Expr>, String, Box<Expr>),
}

// Γ ⊢ e : τ  as a partial function of (Γ, e) to τ (or failure)
fn typecheck(ctx: &HashMap<String, Ty>, e: &Expr) -> Option<Ty> {
    match e {
        Expr::Var(x) => ctx.get(x).cloned(),                 // Rule (4.1a)
        Expr::NumLit(_) => Some(Ty::Num),                    // Rule (4.1c)
        Expr::StrLit(_) => Some(Ty::Str),                    // Rule (4.1b)
        Expr::Plus(e1, e2) => {                               // Rule (4.1d)
            if typecheck(ctx, e1)? == Ty::Num && typecheck(ctx, e2)? == Ty::Num {
                Some(Ty::Num)
            } else { None }
        }
        Expr::Cat(e1, e2) => {                                // Rule (4.1f)
            if typecheck(ctx, e1)? == Ty::Str && typecheck(ctx, e2)? == Ty::Str {
                Some(Ty::Str)
            } else { None }
        }
        Expr::Let(e1, x, e2) => {                             // Rule (4.1h)
            let t1 = typecheck(ctx, e1)?;
            let mut ctx2 = ctx.clone();
            ctx2.insert(x.clone(), t1);
            typecheck(&ctx2, e2)
        }
    }
}
```

```python
# Python: same structure, dynamically typed host language, but the
# *judgment* it encodes is the statically-typed object language above.
def typecheck(ctx: dict, e) -> str | None:
    match e:
        case ("var", x):
            return ctx.get(x)
        case ("num", _):
            return "num"
        case ("str", _):
            return "str"
        case ("plus", e1, e2):
            t1, t2 = typecheck(ctx, e1), typecheck(ctx, e2)
            return "num" if t1 == t2 == "num" else None
        case ("let", e1, x, e2):
            t1 = typecheck(ctx, e1)
            if t1 is None:
                return None
            return typecheck({**ctx, x: t1}, e2)
```

```lean
-- Lean: the typing judgment as an actual inductive *relation*,
-- mirroring Harper's Rules (4.1) almost symbol-for-symbol.
inductive Ty where
  | num
  | str

inductive Expr where
  | var   : String → Expr
  | numLit : Nat → Expr
  | strLit : String → Expr
  | plus  : Expr → Expr → Expr
  | cat   : Expr → Expr → Expr
  | letIn : Expr → String → Expr → Expr

abbrev Ctx := List (String × Ty)

inductive HasType : Ctx → Expr → Ty → Prop
  | var {Γ x τ} (h : (x, τ) ∈ Γ) : HasType Γ (.var x) τ           -- (4.1a)
  | numLit {Γ n} : HasType Γ (.numLit n) .num                      -- (4.1c)
  | strLit {Γ s} : HasType Γ (.strLit s) .str                      -- (4.1b)
  | plus {Γ e1 e2}
      (h1 : HasType Γ e1 .num) (h2 : HasType Γ e2 .num) :
      HasType Γ (.plus e1 e2) .num                                 -- (4.1d)
  | letIn {Γ e1 x e2 τ1 τ2}
      (h1 : HasType Γ e1 τ1) (h2 : HasType ((x, τ1) :: Γ) e2 τ2) :
      HasType Γ (.letIn e1 x e2) τ2                                -- (4.1h)
```

The Lean version makes the point sharpest: `HasType` *is* the judgment $\Gamma \vdash e : \tau$, not a metaphor for it. The Rust and Python functions are algorithms that *decide* the same relation — which is only legitimate once you've proved (as Harper does) that the relation is functional in $\tau$, i.e. **unicity of typing**: for every $\Gamma, e$ there is *at most one* $\tau$ with $\Gamma \vdash e : \tau$ (Lemma 4.1). Without unicity, "the" type of an expression wouldn't even be well-defined, and a `typecheck` function returning a single `Option<Ty>` would be nonsensical.

### Introduction vs. elimination, and the structural properties

Harper flags a classification that recurs for the rest of the book: every construct in $\mathcal{L}\{\texttt{num str}\}$ is either **introductory** (it *produces* a value of a type — numerals and string literals) or **eliminatory** (it *consumes* a value of a type to produce something else — `plus`, `times`, `cat`, `len`). This isn't cosmetic bookkeeping; it's the seed of an idea that will govern function types (introduction = $\lambda$, elimination = application), [[Sum-Types|sum types]], and eventually the entire propositions-as-types correspondence: *eliminatory forms are inverse to introductory forms*. Once dynamics is defined (Part II below), this inversion becomes the operational content of computation — an elimination form applied to an introduction form is precisely what a computation step *does*.

The statics also validates three **structural properties**, all proved by rule induction on Rules (4.1):

- **Weakening** (Lemma 4.3): if $\Gamma \vdash e : \tau$, then $\Gamma, x:\tau' \vdash e : \tau$ for fresh $x$ — adding unused hypotheses never invalidates a typing.
- **Substitution** (Lemma 4.4): if $\Gamma, x:\tau \vdash e' : \tau'$ and $\Gamma \vdash e : \tau$, then $\Gamma \vdash [e/x]e' : \tau'$.
- **Decomposition** (Lemma 4.5), the converse of substitution: any subexpression can be isolated as a separate "module" by naming it with a fresh variable.

Substitution is worth pausing on because it is literally the mathematics of **linking**. Read $e'$ as a client program with a free variable $x$ standing for an as-yet-unimplemented component, and $e$ as the implementation of that component. The substitution lemma says: if the client type-checks assuming $x$ has type $\tau$, and the implementation genuinely has type $\tau$, then the *linked* program $[e/x]e'$ type-checks too, at the same result type. This is why static typing composes — you can type-check modules independently against their interfaces and know the whole will type-check once linked, without re-checking everything from scratch. (Weakening, footnoted by Harper, is *not* free in every type system — languages that track resource usage, like linear or affine type systems, deliberately reject it; those are called *sub-structural* type systems.)

---

## Part II — Dynamics: three equivalent ways to say "how a program runs"

Harper opens Chapter 5 by naming three methods, each of which fully determines execution but does so with a different *shape* of judgment:

> "The most important way to define the dynamics of a language is by the method of **structural dynamics** ... Another method ... called **contextual dynamics** ... An **equational dynamics** presents the dynamics of a language equationally."

And a fourth appears later (Chapter 7) once the first three are in place: **evaluation dynamics**, further refined into **cost dynamics**. All four define *the same* notion of execution for $\mathcal{L}\{\texttt{num str}\}$; the book proves formal equivalence theorems between them. Why bother with four formulations of one idea? Because each is best suited to a different job: structural dynamics is the workhorse for metatheory (proving [[Dynamic-Classification#Safety|safety]]), contextual dynamics simplifies certain proofs by keeping every transition between *complete programs*, equational dynamics matches the "solve it like algebra" intuition useful for reasoning about program equality, and evaluation/cost dynamics are what you'd actually want in a reference manual or a complexity analysis — nobody wants to read a language spec that talks about one machine instruction at a time.

### 1. Transition systems — the common scaffolding

Before any of the four dynamics is defined, Harper first defines the general notion they will all instantiate: a **transition system**, given by four judgment forms:

1. $s\ \mathsf{state}$ — $s$ is a state.
2. $s\ \mathsf{initial}$ — $s$ may begin a computation.
3. $s\ \mathsf{final}$ — $s$ is a terminated state (by convention, final states never transition further).
4. $s \mapsto s'$ — $s$ may step to $s'$.

A state from which no transition is possible is called **stuck**; every final state is stuck by convention, but (crucially, for the [[State-and-Assignables#Safety|safety]] theorem in the next topic) a transition system *can* have [[Type-Safety#Stuck states|stuck states]] that are *not* final — those are the ill-defined programs a type system is supposed to rule out. A **transition sequence** is $s_0, \ldots, s_n$ with $s_0\ \mathsf{initial}$ and each $s_i \mapsto s_{i+1}$; it is **maximal** if it cannot be extended, and **complete** if maximal *and* $s_n\ \mathsf{final}$. The book writes $s \Downarrow$ for "there exists a complete sequence starting at $s$."

The reflexive-transitive closure $s \mapsto^* s'$ is itself given by an ordinary inductive definition —

$$
\dfrac{}{s \mapsto^* s} \qquad\qquad \dfrac{s \mapsto s' \quad s' \mapsto^* s''}{s \mapsto^* s''}
$$

— which means rule induction applies to it exactly as it did to typing derivations: proving a property $P$ of $\mapsto^*$ reduces to showing $P$ is reflexive and closed under **head expansion** (if $s \mapsto s'$ and $P(s', s'')$ then $P(s, s'')$) — a pattern that resurfaces verbatim when relating evaluation dynamics back to structural dynamics below.

A transition system is **deterministic** if every state has at most one successor. This matters practically: determinacy is exactly the property that makes "the value of this program" well-defined independent of *which* order the interpreter happens to pick when multiple reductions are possible.

**[[Recursive-Types#Grounding|Grounding]].** A transition system is nothing more than a labeled graph with designated start/accept-adjacent nodes — the same object underlying a Rust/Python state-machine `enum` with a `step` function, or a Lean `Prop`-valued step relation:

```rust
trait TransitionSystem {
    type State;
    fn is_initial(&self, s: &Self::State) -> bool;
    fn is_final(&self, s: &Self::State) -> bool;
    fn step(&self, s: &Self::State) -> Option<Self::State>; // None ⇒ stuck (if not also final)
}
```

### 2. Structural dynamics — step-by-step, via instruction and search rules

The first, most detailed instantiation takes **states = closed expressions**, all states are initial, and **final states = values**. Values are picked out by an inductive judgment $e\ \mathsf{val}$ — for $\mathcal{L}\{\texttt{num str}\}$, just the numerals and literals:

$$\dfrac{}{\mathsf{num}[n]\ \mathsf{val}} \qquad \dfrac{}{\mathsf{str}[s]\ \mathsf{val}}$$

The transition judgment $e \mapsto e'$ then splits, rule by rule, into exactly two kinds, and this split is the heart of "structural dynamics":

- **Instruction transitions** perform a primitive computation step, e.g.
$$\dfrac{n_1+n_2=n\ \mathsf{nat}}{\mathsf{plus}(\mathsf{num}[n_1];\mathsf{num}[n_2]) \mapsto \mathsf{num}[n]}\qquad(5.4\mathrm{a})$$
- **Search transitions** don't compute anything themselves; they steer *where* the next instruction happens, by recursing into a subexpression:
$$\dfrac{e_1 \mapsto e_1'}{\mathsf{plus}(e_1;e_2)\mapsto \mathsf{plus}(e_1';e_2)}\qquad(5.4\mathrm{b}) \qquad\qquad \dfrac{e_1\ \mathsf{val}\quad e_2\mapsto e_2'}{\mathsf{plus}(e_1;e_2)\mapsto \mathsf{plus}(e_1;e_2')}\qquad(5.4\mathrm{c})$$

Notice what rules (5.4b)–(5.4c) *encode*: they force the left argument of `plus` to reduce to a value before the right argument is touched — this is exactly how "left-to-right evaluation order" gets built into the semantics, as a fact about which search rules exist, not as some separate policy layered on top. The `let` rule is the most interesting case because it has a genuine choice point:

$$\dfrac{e_1 \mapsto e_1'}{\mathsf{let}(e_1;x.e_2)\mapsto\mathsf{let}(e_1';x.e_2)}\ [\text{by-value only}]\qquad(5.4\mathrm{g}) \qquad\qquad \dfrac{[e_1\ \mathsf{val}]}{\mathsf{let}(e_1;x.e_2)\mapsto[e_1/x]e_2}\qquad(5.4\mathrm{h})$$

Include the bracketed rule/premise and you get **call-by-value**: `e1` is reduced to a value first, then substituted. Omit them and you get **call-by-name**: `e1` is substituted immediately, unevaluated, and only forced later wherever it's actually used. This single toggle — "does the search rule for `let`'s bound expression exist?" — is the formal essence of the by-value/by-name distinction that reappears everywhere in the book (function application in Chapter 8, [[Product-Types|product types]] in Chapter 11, etc.). If you know Rust's eager evaluation versus a lazy/thunked language like Haskell, this is precisely that dichotomy, expressed as "which rules are in the inductive definition."

**Grounding — an interpreter *is* a proof search for $e \mapsto^* v$.**

```rust
fn step(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Plus(e1, e2) => match (&**e1, &**e2) {
            (Expr::NumLit(n1), Expr::NumLit(n2)) => Some(Expr::NumLit(n1 + n2)), // instruction, (5.4a)
            (e1, _) if !is_val(e1) => {
                let e1p = step(e1)?;
                Some(Expr::Plus(Box::new(e1p), e2.clone()))                     // search, (5.4b)
            }
            (_, e2) => {
                let e2p = step(e2)?;
                Some(Expr::Plus(e1.clone(), Box::new(e2p)))                     // search, (5.4c)
            }
        },
        Expr::Let(e1, x, e2) if is_val(e1) => Some(subst(e1, x, e2)),           // instruction, (5.4h), by-value
        Expr::Let(e1, x, e2) => {
            let e1p = step(e1)?;
            Some(Expr::Let(Box::new(e1p), x.clone(), e2.clone()))               // search, (5.4g)
        }
        _ => None, // stuck, or already a value
    }
}
```

Each recursive call to `step` is literally constructing a derivation of $e \mapsto e'$ — the "two-dimensional structure" Harper mentions (width = number of transition steps taken, height = size of the derivation tree justifying each individual step).

### 3. Contextual dynamics — factoring "where" from "what" via evaluation contexts

Structural dynamics has a redundancy: rules like (5.4b)/(5.4c) exist purely to *locate* the next instruction — they carry no computational content of their own. **Contextual dynamics** factors this out explicitly. First, it isolates the actual computational rules into a separate judgment, **instruction transition** $e_1 \to e_2$ (note the different arrow, a small but meaningful notational choice — it marks *primitive* steps, distinct from the *state* transition $\mapsto$):

$$\dfrac{m+n=p\ \mathsf{nat}}{\mathsf{plus}(\mathsf{num}[m];\mathsf{num}[n]) \to \mathsf{num}[p]} \qquad\qquad \mathsf{let}(e_1;x.e_2) \to [e_1/x]e_2$$

Then it defines **evaluation contexts** — expressions with exactly one designated hole $\circ$ marking "the next place execution will happen":

$$\dfrac{}{\circ\ \mathsf{ectxt}} \qquad\qquad \dfrac{E_1\ \mathsf{ectxt}}{\mathsf{plus}(E_1;e_2)\ \mathsf{ectxt}} \qquad\qquad \dfrac{e_1\ \mathsf{val}\quad E_2\ \mathsf{ectxt}}{\mathsf{plus}(e_1;E_2)\ \mathsf{ectxt}}$$

and a "fill the hole" judgment $e' = E\{e\}$ (plug expression $e$ into evaluation context $E$). With these in hand, the *entire* dynamics collapses to one rule:

$$\dfrac{e = E\{e_0\}\quad e_0 \to e_0''\quad e' = E\{e_0''\}}{e \mapsto e'}\qquad(5.8)$$

...or, in the more familiar compact notation the book also gives: $\dfrac{e_0 \to e_0''}{E\{e_0\} \mapsto E\{e_0''\}}$. Read informally: decompose the whole program into (a context, a redex); reduce the redex by one instruction step; re-plug the result into the same spot. This is a *decompose / step / recompose* discipline — exactly the shape of a "zipper" data structure that walks into a tree, edits one node, and reconstructs the tree. Harper proves (Theorem 5.4) that this is provably equivalent to structural dynamics; the deeper payoff (beyond notational economy) is that every transition in contextual dynamics is between *whole programs of the same type*, never between some intermediate fragment of unclear type — which simplifies later metatheoretic arguments considerably.

**Grounding — evaluation contexts as a zipper.**

```rust
enum EvalCtx {
    Hole,
    PlusL(Box<EvalCtx>, Expr),      // plus(E, e2)
    PlusR(Expr, Box<EvalCtx>),      // plus(v1, E), requires v1 is a value
}

fn fill(ctx: &EvalCtx, e: Expr) -> Expr {
    match ctx {
        EvalCtx::Hole => e,
        EvalCtx::PlusL(c, e2) => Expr::Plus(Box::new(fill(c, e)), Box::new(e2.clone())),
        EvalCtx::PlusR(v1, c) => Expr::Plus(Box::new(v1.clone()), Box::new(fill(c, e))),
    }
}
// "decompose" walks down the expression building up an EvalCtx until
// it finds the redex — the sub-expression at the hole — exactly the
// search rules of structural dynamics, but reified as data.
```

```lean
-- Lean: `EvalCtx` and `fill` as data + function, with the equivalence
-- to structural dynamics stated as an actual theorem to prove.
inductive EvalCtx where
  | hole : EvalCtx
  | plusL : EvalCtx → Expr → EvalCtx
  | plusR : Expr → EvalCtx → EvalCtx  -- side condition: the Expr is a value

def fill : EvalCtx → Expr → Expr
  | .hole, e => e
  | .plusL c e2, e => .plus (fill c e) e2
  | .plusR v1 c, e => .plus v1 (fill c e)
```

### 4. Equational dynamics — computation as definitional equality

The third style abandons "state transition" altogether and instead defines a **congruence relation** $\Gamma \vdash e \equiv e' : \tau$ — "definitional equality" — as the smallest equivalence relation that (a) respects every syntactic constructor (a *congruence*) and (b) contains the primitive computation rules directly as axioms:

$$\dfrac{n_1+n_2=n\ \mathsf{nat}}{\Gamma \vdash \mathsf{plus}(\mathsf{num}[n_1];\mathsf{num}[n_2]) \equiv \mathsf{num}[n] : \mathsf{num}} \qquad\qquad \Gamma \vdash \mathsf{let}(e_1;x.e_2) \equiv [e_1/x]e_2 : \tau$$

plus reflexivity, symmetry, transitivity, and congruence rules for `plus`, `cat`, `let`. This is deliberately the same style of reasoning as high-school algebra: you're allowed to replace any subexpression with something definitionally equal to it, anywhere, and chain such replacements to *calculate* — Harper calls this **symbolic evaluation**. Theorem 5.5 confirms this coincides with the other dynamics: $e \equiv e' : \tau$ iff both reduce (via $\mapsto^*$) to a *common* value.

The book is careful to flag equational dynamics' limitation, and this is one of the sharper conceptual payoffs of the chapter: definitional equality is **too weak** to prove general laws with free variables. You can derive every *closed instance* of commutativity, $\bar{n}_1 + \bar{n}_2 \equiv \bar{n}_2 + \bar{n}_1 : \mathsf{num}$ for concrete numerals $n_1, n_2$ — just run both sides — but you cannot derive the *general* statement $x_1 + x_2 \equiv x_2 + x_1 : \mathsf{num}$ for a free variable $x_1, x_2$, because there's no computation rule that lets you swap the arguments of an *unevaluated* `plus`. Closing that gap requires a strictly stronger notion — **semantic equivalence**, built on mathematical induction over the dynamics — which the book develops much later (Chapter 47's [[Equational Reasoning]] topic). This distinction (definitional equality, purely syntactic/computational, versus semantic/observational equivalence, which needs induction) is exactly the same distinction a Lean or Coq user runs into: `rfl` (definitional equality, decided by computation) proves far less than a full inductive `theorem`.

### 5. Evaluation dynamics — collapsing the trace to (input, output)

Chapter 7 introduces a fourth style motivated by a practical complaint: nobody writing a language reference manual wants to describe execution one micro-step at a time. **Evaluation dynamics** defines a single inductive judgment $e \Downarrow v$ — "$e$ evaluates to value $v$" — directly, suppressing every intermediate state:

$$\dfrac{e_1 \Downarrow \mathsf{num}[n_1] \quad e_2 \Downarrow \mathsf{num}[n_2] \quad n_1+n_2=n\ \mathsf{nat}}{\mathsf{plus}(e_1;e_2) \Downarrow \mathsf{num}[n]} \qquad\qquad \dfrac{[e_1/x]e_2 \Downarrow v_2}{\mathsf{let}(e_1;x.e_2) \Downarrow v_2}$$

Notice the `let` rule is *not syntax-directed* — its premise, $[e_1/x]e_2$, is not a syntactic subexpression of the conclusion, so ordinary structural induction on $e$ does not apply to proofs about $\Downarrow$; you must use rule induction on the definition of $\Downarrow$ itself (exactly the general principle from Chapter 2, applied here concretely). The book proves this is exactly as expressive as structural dynamics (Theorem 7.2: $e \mapsto^* v \iff e \Downarrow v$), via two lemmas that are worth internalizing because the pattern — "chain individual steps to build an evaluation derivation" one direction, "head expansion / converse evaluation" the other — recurs throughout the book's metatheory:

- Lemma 7.3 ($e \Downarrow v \Rightarrow e \mapsto^* v$): induction on the evaluation derivation, chaining together the sub-evaluations into one transition sequence.
- Lemma 7.4 ($e \mapsto e'$ and $e' \Downarrow v \Rightarrow e \Downarrow v$): "converse evaluation," proved by induction on the *transition* — this is the head-expansion property flagged back in the transition-systems section.

But evaluation dynamics has a real, structural cost, and the book is unusually direct about naming it: it **cannot express progress**. Preservation transfers fine ($e \Downarrow v$ and $e:\tau$ implies $v:\tau$), but "progress" for a transition system means "a well-typed non-value can always take a step" — and evaluation dynamics has no notion of an intermediate, partially-evaluated state to make that claim about. You could try to state progress as "every well-typed $e$ has *some* $v$ with $e \Downarrow v$," but that's a much stronger claim than progress — it asserts *termination*, which is simply false for languages with general recursion or run-time errors (Chapters 8 and 10 introduce exactly such languages). The book's workaround — introducing an explicit "goes wrong" judgment $e\Uparrow$ just to have something to prove doesn't happen — is presented as a real methodological weakness (Section 7.3): you must remember to include a rule for every possible way to go wrong, and nothing in the framework checks that you did. Structural/contextual dynamics don't have this problem: an ill-typed program just gets stuck automatically, with no bookkeeping required, and the progress theorem (next topic, [[Type Safety]]) rules that out wholesale for well-typed programs.

### 6. Cost dynamics — recovering complexity from evaluation dynamics

Evaluation dynamics throws away the step count along with the intermediate states — which means it cannot express *time complexity* either. **Cost dynamics** patches this by annotating the judgment with a natural number: $e \Downarrow^k v$, "$e$ evaluates to $v$ in $k$ steps," where the cost of a compound expression is simply the sum of its parts' costs plus one for the instruction step at the top:

$$\dfrac{}{\mathsf{num}[n] \Downarrow^0 \mathsf{num}[n]} \qquad\qquad \dfrac{e_1 \Downarrow^{k_1} \mathsf{num}[n_1] \quad e_2 \Downarrow^{k_2} \mathsf{num}[n_2]}{\mathsf{plus}(e_1;e_2) \Downarrow^{k_1+k_2+1} \mathsf{num}[n_1+n_2]}$$

Theorem 7.7 pins down exactly what "$k$" means operationally: $e \Downarrow^k v$ iff $e \mapsto^k v$ (reaches $v$ in exactly $k$ structural-dynamics steps). So cost dynamics is not a new idea about execution — it's a bookkeeping refinement of evaluation dynamics that recovers precisely the information structural dynamics carried around for free (the length of the transition sequence), while retaining evaluation dynamics' more readable "input maps to output" shape. This is the seed of the *cost graphs* and asymptotic-complexity machinery Harper builds up much later for reasoning about parallel algorithms (Chapter 31) — counting structural-dynamics steps is, quite literally, how the book defines "how many operations does this program take."

**Grounding — cost dynamics as an instrumented interpreter.**

```rust
fn eval_with_cost(e: &Expr) -> (Value, u64) {
    match e {
        Expr::NumLit(n) => (Value::Num(*n), 0),
        Expr::Plus(e1, e2) => {
            let (Value::Num(n1), k1) = eval_with_cost(e1) else { panic!() };
            let (Value::Num(n2), k2) = eval_with_cost(e2) else { panic!() };
            (Value::Num(n1 + n2), k1 + k2 + 1)
        }
        // ...
        _ => unimplemented!(),
    }
}
```

This is exactly what you'd write to instrument an interpreter for a "how many primitive reductions did this program take" profiler — and Theorem 7.7 is the guarantee that the number this function returns matches "how many times would `step` from the structural-dynamics interpreter above have been called."

---

## Synthesis: how this chapter organizes everything that follows

Two structural facts from this topic recur, unchanged in spirit, for the rest of the book:

- **Every new language feature Harper introduces gets exactly this treatment**: a statics (a typing judgment, given as an inductive definition, validated by weakening/substitution) paired with a dynamics (usually structural, occasionally contextual for convenience). Function types, product types, sum types, [[Recursive-Types|recursive types]], polymorphism — all of Chapters 6 through 26 are literally "statics + dynamics" instances of the *methodology* laid down here, not new methodologies.
- **The coherence between the two halves is not automatic** — it's a theorem, and its name is *type safety*, proved via **preservation** (dynamics respects the statics' predictions) and **progress** (statics rules out stuck states). That's the very next topic in this book, and it directly consumes the machinery built here: preservation is proved by rule induction on the *dynamics* (Rules (5.4) or (5.5)), and progress by rule induction on the *statics* (Rules (4.1)) using a **canonical forms** lemma that characterizes what a value of each type must look like.

```
Statics (Ch. 4)                         Dynamics (Ch. 5, 7)
─────────────────                       ─────────────────────
Γ ⊢ e : τ                               structural:  e ↦ e'   (instruction + search)
  inductive judgment                    contextual:   e = E{e₀}, e₀ → e₀'' ⇒ e ↦ E{e₀''}
  weakening / substitution              equational:   Γ ⊢ e ≡ e' : τ  (congruence + axioms)
                                         evaluation:   e ⇓ v            (suppresses steps)
                                         cost:         e ⇓ᵏ v           (evaluation + step count)
        \                                        /
         \                                      /
          \___________  Type Safety  __________/
             preservation (induct on dynamics)
             progress     (induct on statics, via canonical forms)
```

If you're building a language implementation (interpreter, verifier, or elaborator) as your own project, the practical lesson to carry forward is this: pick **structural or contextual dynamics** as your ground-truth semantics when you need to *prove* things about your language (safety, determinacy), because they alone expose the "stuck state" concept that progress theorems are about — but implement your actual interpreter closer to **evaluation/cost dynamics**, since that's the shape a real `eval` function naturally takes, and lean on Theorem 7.2/7.7 (proved once, here, for a toy language, but the *pattern* of proof transfers to any language you extend this way) as your license that the two views agree.
