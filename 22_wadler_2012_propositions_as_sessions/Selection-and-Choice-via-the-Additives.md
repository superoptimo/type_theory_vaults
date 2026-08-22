---
title: Selection and Choice via the Additives
source: 22_wadler_2012_propositions_as_sessions (Wadler, "Propositions as Sessions")
chapter: "§3.3 Selection and Choice (pp. 14–16)"
tags: [linear-logic, session-types, process-calculus, curry-howard, cut-elimination]
---

[[book-guidelines|↩ Back to guidelines]]

# Selection and Choice via the Additives

$\otimes$ and $\parr$ (see [[Output-and-Input-via-the-Multiplicatives|Output and Input via the Multiplicatives]]) give CP mandatory, sequential communication: send this, then behave as that — no branching, no alternatives. The additives, $\oplus$ ("plus") and $\&$ ("with"), are where CP gets *branching protocols*: a channel that can select from among several continuations, or offer a choice among several. They are dual: $A\oplus B$ **selects** from $A$ or $B$; $A\&B$ **offers a choice** of $A$ or $B$.

## What problem this solves

A protocol built only from $\otimes/\parr$ is a straight line — every session runs through the exact same sequence of sends and receives. Real protocols branch: a server that can sell an item *or* quote its price; a client that decides, at runtime, which of two services it wants. You need a connective where **one side of the cut gets to decide**, and the other side has committed in advance to handling whatever gets decided.

That asymmetry — one side picks, the other side is ready for either pick — is exactly what $\oplus$ and $\&$ formalize. It's the session-typed analogue of a tagged union crossed with pattern matching: the *selector* commits to one branch and only needs to provide that branch's continuation; the *offerer* must be prepared to run either branch, because it doesn't know in advance which one is coming.

## The selection rules

$$
\frac{P \vdash \Gamma, x:A}{x[\mathsf{inl}].P \vdash \Gamma, x:A\oplus B}\;\oplus_1
\qquad\qquad
\frac{P \vdash \Gamma, x:B}{x[\mathsf{inr}].P \vdash \Gamma, x:A\oplus B}\;\oplus_2
$$

Read bottom-up: to build a process of type $A\oplus B$ on channel $x$, you need a *single* process $P$ that already knows which branch it wants — $P$ communicates along $x$ obeying protocol $A$ (or, symmetrically, $B$). The composite process $x[\mathsf{inl}].P$ transmits along $x$ a request to select the left option, then runs $P$. Unlike $\otimes$'s output rule, there's no allocation of a fresh channel and no splitting into two disjoint processes — selection doesn't send a *value*, it sends a *decision*, and then keeps going as the chosen continuation.

## The choice rule

$$
\frac{Q \vdash \Delta, x:A \qquad R \vdash \Delta, x:B}{x.\mathsf{case}(Q,R) \vdash \Delta, x:A\&B}\;\&
$$

The offering side is where the asymmetry with $\otimes/\parr$ really shows: this rule needs **two entire processes**, $Q$ and $R$, each ready to run if their respective branch gets selected — but both $Q$ and $R$ communicate along the *same* environment $\Delta$ (unlike $\otimes$'s $\Gamma,\Delta$ split). That's not a bookkeeping accident: only one of $Q$ or $R$ will ever actually execute, so there's no danger of them fighting over $\Delta$'s resources — whichever branch loses simply never runs.

**Type evolution, same story as always.** For selection, channel $x$ has type $A$ (or $B$) in the component process $P$, and type $A\oplus B$ in the composite. For choice, $x$ has type $A$ in $Q$, type $B$ in $R$, and type $A\&B$ in the composite $x.\mathsf{case}(Q,R)$. This is the same session-type-as-evolving-channel-type reading from [[The-Twist-Reinterpreting-the-Linear-Connectives|The Twist]] and from $\otimes/\parr$: the channel's type shrinks to "whatever's left" once the branching decision resolves.

### Rust grounding: `enum` selection, `match` offering

This maps almost too cleanly onto Rust's sum types and pattern matching — arguably more directly than $\otimes/\parr$ mapped onto ownership:

```rust
// A channel typed A ⊕ B is a value the *sender* has already committed to
// one variant of — exactly a constructed enum, ready to be sent.
enum Selection<A, B> {
    Inl(A), // x[inl].P  — commit to protocol A, continue as P
    Inr(B), // x[inr].P  — commit to protocol B, continue as P
}

fn select_left<A, B>(p: A) -> Selection<A, B> {
    Selection::Inl(p) // the process ALREADY decided; no ambiguity survives
}

// A channel typed A & B is a value the *receiver* must be ready to handle
// either way — exactly a match arm pair, each a live continuation.
fn offer_choice<A, B, T>(
    incoming: Selection<A, B>,
    handle_a: impl FnOnce(A) -> T, // Q : Δ, x:A
    handle_b: impl FnOnce(B) -> T, // R : Δ, x:B
) -> T {
    match incoming {
        Selection::Inl(a) => handle_a(a), // only one branch ever runs
        Selection::Inr(b) => handle_b(b),
    }
}
```

The reason `handle_a` and `handle_b` are allowed to both close over the *same* outer state (analogous to $Q$ and $R$ sharing $\Delta$) is precisely because `match` guarantees mutual exclusion — only one arm's captured environment is ever actually used at runtime, so there's no real contention even though both closures are legal to write down. That's the process-calculus content of the $\&$ rule's shared $\Delta$, stated as a Rust borrow-checker fact instead of a typing-rule side condition.

## The principal reduction: picking an alternative

Cut a selection against a choice and the logic *becomes* a decision, resolved on the spot:

$$
x[\mathsf{inl}].P \;\mid\; x.\mathsf{case}(Q,R) \;\Longrightarrow\; \nu x.(P \mid Q) \qquad (\beta_{\oplus\&})
$$

(The rule for selecting the right option is symmetric: $x[\mathsf{inr}].P \mid x.\mathsf{case}(Q,R) \Longrightarrow \nu x.(P\mid R)$.)

This is deliberately the simplest reduction in the whole system — simpler even than $(\beta_{\otimes\parr})$, because no name allocation or substitution happens. All the rule does is *discard the branch that wasn't picked*: $R$ vanishes entirely from the reduct when $\mathsf{inl}$ is selected. Operationally, this is a runtime cost that a compiler can specialize away — once the selector's tag is known, the untaken branch is dead code, exactly as an `enum` `match` compiles to a jump table that never touches the unreached arm's body.

```mermaid
sequenceDiagram
    participant Sel as x[inl].P (already decided)
    participant Off as x.case(Q,R) (offers both)
    Sel->>Off: transmit tag "inl" along x
    Note over Off: R is discarded — never instantiated
    Off-->>Sel: continue as νx.(P | Q)
```

## The additive units: $0$ and $\top$

$\oplus$ and $\&$ need identity elements too, for the degenerate cases of "select from nothing" and "offer nothing":

- $0$ is the session type of a channel that **selects from among no alternatives**.
- $\top$ is the session type of a channel that **offers a choice among no alternatives**.
- Dual, as expected: $0^\perp = \top$.

Here the story diverges sharply from $1/\bot$. There is **no rule for $0$** — look back at Figure 1 in the paper (referenced from [[CP-a-Classical-Linear-Logic-Process-Calculus|CP's core rules]]) and every other connective has an introduction rule; $0$ has none. This isn't an oversight, it's *forced*: a rule for $0$ would have to be a selection rule with zero disjuncts to select from, and there is no way to write down "commit to one of zero options." A process typed at $0$ is a logical impossibility — you cannot construct one, full stop, which is exactly the point: $0$ is *False* in the propositions-as-types reading, and there should be no proof of *False*.

Because there's no rule for $0$, there's consequently **no principal reduction for $0$ against $\top$** either — you can't reduce a cut whose $0$-side doesn't exist. The paper notes this explicitly: "there is also no reduction for a cut of an empty selection against an empty choice." $\top$, by contrast, *does* have a rule (offering a choice with zero branches, `x.case()` — trivially satisfiable, since it's never asked to actually run any branch), it just never gets to interact with anything on the $0$ side because nothing ever inhabits $0$.

```rust
// 0 is the uninhabited type — Rust's `!` (never type) or an empty enum.
enum Void {} // no constructors possible: matches CP's "no rule for 0"

// ⊤ *is* constructible: it's a value that offers to handle zero cases —
// vacuously well-typed because it's never called upon to produce anything.
fn offer_nothing(never: Void) -> ! {
    match never {} // exhaustive: there are no variants to handle
}
```

## Worked example: a second protocol, then combining both

**A second independent protocol.** Before combining anything, Wadler introduces a second $\otimes/\parr$ protocol — a price-quote service, structurally identical in shape to buy/sell but semantically distinct:

$$
\begin{aligned}
\mathsf{Shop} &\triangleq \mathsf{Name}\otimes(\mathsf{Price}^\perp \parr \bot) \\
\mathsf{Quote} &\triangleq \mathsf{Name}^\perp\parr(\mathsf{Price}\otimes 1)
\end{aligned}
$$

with $\mathsf{Shop} = \mathsf{Quote}^\perp$, and processes $\mathsf{shop}_x \triangleq x[u].(\mathsf{put\text{-}name}_u \mid x(v).\mathsf{get\text{-}price}_v)$ and $\mathsf{quote}_x \triangleq x(u).x[v].(\mathsf{lookup}_{u,v} \mid x[\,].0)$ that reduce, by the same $(\beta_{\otimes\parr})$/$(\beta_{1\bot})$ machinery from the multiplicatives article, to $\nu u.(\mathsf{put\text{-}name}_u \mid \nu v.(\mathsf{lookup}_{u,v} \mid \mathsf{get\text{-}price}_v))$.

**Now combine them with $\oplus/\&$.** A single server offers *either* service; a single client picks which one it wants:

$$
\begin{aligned}
\mathsf{Select} &\triangleq \mathsf{Buy} \oplus \mathsf{Shop} \\
\mathsf{Choice} &\triangleq \mathsf{Sell} \,\&\, \mathsf{Quote}
\end{aligned}
$$

$$
\begin{aligned}
\mathsf{select\text{-}buy}_x &\triangleq x[\mathsf{inl}].\mathsf{buy}_x \\
\mathsf{select\text{-}shop}_x &\triangleq x[\mathsf{inr}].\mathsf{shop}_x \\
\mathsf{choice}_x &\triangleq x.\mathsf{case}(\mathsf{sell}_x, \mathsf{quote}_x)
\end{aligned}
$$

with $\mathsf{Select} = \mathsf{Choice}^\perp$, so they cut together. One application of $(\beta_{\oplus\&})$ resolves the branching *before* any of the underlying $\otimes/\parr$ communication even starts:

$$
\nu x.(\mathsf{select\text{-}buy}_x \mid \mathsf{choice}_x) \;\Longrightarrow\; \nu x.(\mathsf{buy}_x \mid \mathsf{sell}_x)
$$

(and symmetrically, $\nu x.(\mathsf{select\text{-}shop}_x \mid \mathsf{choice}_x) \Longrightarrow \nu x.(\mathsf{shop}_x \mid \mathsf{quote}_x)$). The $\mathsf{quote}_x$ process in the first reduction, and $\mathsf{sell}_x$ in the second, are simply *discarded* — never instantiated, never run — exactly the "untaken branch vanishes" behavior of $(\beta_{\oplus\&})$, now demonstrated composing with an entire pre-built multiplicative protocol as the payload of each branch.

### Rust sketch: one endpoint, a service enum, dispatch to the matching handler

```rust
enum Service {
    Buy { name: String, credit: CardNumber },   // Select = Buy ⊕ Shop
    Shop { name: String },
}

enum ServiceReply {
    Receipt(Receipt),
    Price(u32),
}

// choice_x = x.case(sell_x, quote_x): must be ready for either variant.
fn choice(req: Service) -> ServiceReply {
    match req {
        Service::Buy { name, credit } => ServiceReply::Receipt(sell(name, credit)), // sell_x
        Service::Shop { name } => ServiceReply::Price(quote(name)),                  // quote_x
    }
}

// select_buy_x = x[inl].buy_x: the client already knows which arm it wants.
fn select_buy(name: String, credit: CardNumber) -> Service {
    Service::Buy { name, credit }
}
```

Notice `choice` never runs both `sell` and `quote` "just in case" — Rust's `match` exhaustiveness check guarantees every arm is *typeable*, but only the arm matching the incoming tag is ever *executed*. That's $(\beta_{\oplus\&})$'s "discard the other branch" behavior, made concrete as ordinary dead-branch elimination.

## Where this leads

$\oplus/\&$ complete CP's two "core" dual pairs — $\otimes/\parr$ for mandatory sequencing, $\oplus/\&$ for branching — and together they're already enough to encode realistic request/response protocols with alternatives, as the combined buy-or-shop example shows. The next connective pair, $!/?$ (see [[Servers-and-Clients-via-the-Exponentials|Servers and Clients via the Exponentials]]), adds *repetition*: a server that can be selected from or communicated with by an unbounded number of clients, rather than exactly once. Structurally, $!/?$'s [[Servers-and-Clients-via-the-Exponentials#The three client rules|three client-side rules]] (dereliction, weakening, contraction) are closely related to how $\&$ demands readiness without commitment — a server offering $!A$ must, like a $\&$-offering process, stay agnostic about who shows up and how many times.

For the mechanism-minded reader: the "one side decides, one side must be ready for either" shape here is precisely the shape of a type-directed dispatch table — the same discipline that shows up later when [[Translating-GV-into-CP|Translating GV into CP]] translates [[GV-a-Session-Typed-Functional-Language|GV]]'s `Select`/`Case` constructs directly onto $\oplus_i$/$\&$, with no inversion (unlike the surprising $\otimes \leftrightarrow \parr$ swap for send/receive) — evidence that selection and choice already have the "obviously right" polarity in both systems.
