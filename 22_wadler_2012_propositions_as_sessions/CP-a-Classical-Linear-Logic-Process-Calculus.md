---
title: "CP: A Classical Linear Logic Process Calculus"
source: "22_wadler_2012_propositions_as_sessions"
chapter: "Section 3 (front matter) and 3.1 Structural Rules"
pages: "pp. 5–10"
tags: [type-theory, linear-logic, session-types, process-calculus, curry-howard, sequent-calculus]
---

[[book-guidelines|↩ Back to guidelines]]

# CP: A Classical Linear Logic Process Calculus

## The problem this solves

Once you accept that a session type should describe a communication *protocol* rather than a static value shape — "first send a `Credit`, then receive a `Receipt`, then you're done" — you need three things simultaneously:

1. A grammar of **propositions** that can express protocols like that (send-then, receive-then, offer-a-choice, ...).
2. A grammar of **processes** — actual runnable programs — that can perform those actions.
3. A set of **rules** tying the two together, so that "this process has this session type" is a checkable judgment, not just an intuition.

CP (Classical Processes) is Wadler's answer, and its defining feature is that it doesn't invent these three things independently and then hope they line up. It takes the rules of classical linear logic *exactly as Girard wrote them in 1987* and reads them as a type system for a process calculus. A logical proof, on this reading, simply *is* a well-typed process — Curry-Howard, but with concurrent programs playing the role that functional programs play in the usual correspondence. Everything in this article — the grammar, the environments, the two structural rules (Axiom and Cut) — is the scaffolding that later articles' connective-by-connective rules (⊗/⅋, ⊕/&, !/?, ∃/∀) all plug into, so it's worth being precise about it once, here, rather than re-deriving it five times.

## The grammar of propositions-as-session-types

Propositions $A, B, C$ are built from this grammar:

$$
A, B, C ::= X \mid X^\perp \mid A \otimes B \mid A \parr B \mid A \oplus B \mid A \& B \mid {!A} \mid {?A} \mid \exists X.B \mid \forall X.B \mid 1 \mid \bot \mid 0 \mid \top
$$

Read as *session types* — protocols for a channel to obey — each piece means:

| Proposition | Reads as | Session-type meaning |
|---|---|---|
| $X$ | a propositional variable | an abstract, as-yet-unspecified protocol |
| $X^\perp$ | dual of a variable | the *opposite* of that protocol (syntactically primitive — see below) |
| $A \otimes B$ | "times" | output an $A$, then behave as $B$ |
| $A \parr B$ | "par" | input an $A$, then behave as $B$ |
| $A \oplus B$ | "plus" | select — the channel picks $A$ or $B$ |
| $A \& B$ | "with" | offer — the channel lets its partner pick $A$ or $B$ |
| $!A$ | "of course!" | a *server*: repeatably accept requests for $A$ |
| $?A$ | "why not?" | a *collection of clients*: may request $A$, zero or more times |
| $\exists X.B$ | existential | output a proposition, then behave as $B$ |
| $\forall X.B$ | universal | input a proposition, then behave as $B$ |
| $1$ | unit for $\otimes$ | send an empty signal, then stop |
| $\bot$ | unit for $\parr$ | receive an empty signal, then stop |
| $0$ | unit for $\oplus$ | select from *no* alternatives — uninhabited |
| $\top$ | unit for $\&$ | offer a choice among *no* alternatives — trivially satisfiable |

Don't worry yet about *how* processes implement each of these — that's the job of the next several articles, one dual pair at a time ($\otimes/\parr$, $\oplus/\&$, $!/?$, $\exists/\forall$). What matters here is that this is the complete alphabet: every connective in CP is one of these fourteen forms, nothing more.

**Rust grounding.** Because this is a *closed* recursive grammar with no surprises, it drops directly into a Rust `enum`:

```rust
#[derive(Clone, Debug, PartialEq)]
enum Prop {
    Var(String),                     // X
    DualVar(String),                 // X⊥ — dual of a variable is primitive syntax
    Times(Box<Prop>, Box<Prop>),     // A ⊗ B
    Par(Box<Prop>, Box<Prop>),       // A ⅋ B
    Plus(Box<Prop>, Box<Prop>),      // A ⊕ B
    With(Box<Prop>, Box<Prop>),      // A & B
    OfCourse(Box<Prop>),             // !A
    WhyNot(Box<Prop>),               // ?A
    Exists(String, Box<Prop>),       // ∃X. B
    Forall(String, Box<Prop>),       // ∀X. B
    One,                             // 1
    Bot,                             // ⊥
    Zero,                            // 0
    Top,                             // ⊤
}
```

If you've ever written a `TypeExpr` enum for a toy compiler, this is that, just with communication verbs (`Times`/`Par`) standing in for the usual product/sum types — which is exactly the point the rest of this article is building toward.

## Duality: the mechanism that makes protocols match

Every proposition $A$ has a dual $A^\perp$:

$$
\begin{aligned}
(X)^\perp &= X^\perp & (X^\perp)^\perp &= X \\
(A \otimes B)^\perp &= A^\perp \parr B^\perp & (A \parr B)^\perp &= A^\perp \otimes B^\perp \\
(A \oplus B)^\perp &= A^\perp \& B^\perp & (A \& B)^\perp &= A^\perp \oplus B^\perp \\
({!A})^\perp &= {?A^\perp} & ({?A})^\perp &= {!A^\perp} \\
(\exists X.B)^\perp &= \forall X.B^\perp & (\forall X.B)^\perp &= \exists X.B^\perp \\
1^\perp &= \bot & \bot^\perp &= 1 \\
0^\perp &= \top & \top^\perp &= 0
\end{aligned}
$$

Two things are worth pulling out. First, $(X)^\perp = X^\perp$ is not a *computed* fact — $X^\perp$ is part of the syntax itself, the way `!x` is syntax rather than something you evaluate. This is what makes duality total and uniform: you never get stuck trying to compute the dual of an unresolved variable. Second, **duality is an involution**: $(A^\perp)^\perp = A$ for every proposition, always. That's not a footnote — it's the entire reason a session-typed handshake works. If channel $x$ obeys $A$ on one end, its partner obeying $A^\perp$ on the other end is running the *exact complementary* protocol: your sends are its receives, your selections are its offered choices, and — crucially — if you flip the connection around, you're back to running $A$ again. A protocol has exactly one "other side," never two nested layers of otherness.

**Lean grounding.** This is precisely the shape of a recursively-defined function paired with a proof of an algebraic law — bread and butter for a kernel/elaborator project:

```lean
inductive Prop : Type
  | var     : String → Prop
  | dualVar : String → Prop
  | times   : Prop → Prop → Prop
  | par     : Prop → Prop → Prop
  | plus    : Prop → Prop → Prop
  | with_   : Prop → Prop → Prop
  | ofCourse : Prop → Prop
  | whyNot   : Prop → Prop
  | exists_  : String → Prop → Prop
  | forall_  : String → Prop → Prop
  | one | bot | zero | top

def dual : Prop → Prop
  | .var x       => .dualVar x
  | .dualVar x   => .var x
  | .times a b   => .par (dual a) (dual b)
  | .par a b     => .times (dual a) (dual b)
  | .plus a b    => .with_ (dual a) (dual b)
  | .with_ a b   => .plus (dual a) (dual b)
  | .ofCourse a  => .whyNot (dual a)
  | .whyNot a    => .ofCourse (dual a)
  | .exists_ x b => .forall_ x (dual b)
  | .forall_ x b => .exists_ x (dual b)
  | .one => .bot | .bot => .one
  | .zero => .top | .top => .zero

theorem dual_dual (A : Prop) : dual (dual A) = A := by
  induction A <;> simp_all [dual]
```

`dual_dual` is the formal statement of "flip it twice and you're home" — the same shape as a `NNF`-normalization or `neg_neg` lemma you'd write for a classical propositional prover, which is no accident: CP *is* classical logic, so its negation (duality) behaves exactly like the one your prover already needs.

## Substitution: how a proposition can *have* a variable

Where $\exists X.B$ or $\forall X.B$ bind a propositional variable, the paper writes $B\{A/X\}$ for "substitute $A$ for $X$ in $B$." Assuming $X \neq Y$:

$$
X\{A/X\} = A \qquad X^\perp\{A/X\} = A^\perp \qquad Y\{A/X\} = Y \qquad Y^\perp\{A/X\} = Y^\perp
$$

with the obvious structural clauses elsewhere, e.g. $(A \otimes B)\{C/X\} = A\{C/X\} \otimes B\{C/X\}$. Notice the second clause: substituting into a *dual* variable produces the *dual* of what you substituted — $X^\perp\{A/X\} = A^\perp$, not $A$. This single design choice is what makes duality and substitution commute cleanly: $B\{A/X\}^\perp = B^\perp\{A/X\}$. You'll want that identity later (Section 3.5, in the article on polymorphism) when a cut against an instantiated quantifier needs its two sides to still be exact duals of each other after the substitution goes through.

## Environments: linear typing contexts, made structurally explicit

$\Gamma$, $\Delta$, $\Theta$ range over **environments** — finite maps from distinct channel names to propositions, e.g. $\Gamma = x_1{:}A_1, \ldots, x_n{:}A_n$. Two facts about environments carry all the weight:

- **Order is ignored** — an environment is a set of bindings, not a sequence. (This is why CP needs no separate Exchange rule; Section 3.1, below, only needs Axiom and Cut.)
- **Environments use *linear maintenance*.** Writing $\Gamma, \Delta$ to combine two environments is only legal when $\mathsf{fn}(\Gamma) \cap \mathsf{fn}(\Delta) = \emptyset$ — no channel name may appear in both. There is no rule anywhere in CP that lets a linear channel binding be silently duplicated or dropped.

**What breaks without this.** If two environments being combined were allowed to share a channel name $x$ with two *different* uses, you'd have two processes both believing they have exclusive rights to communicate along $x$ — which is precisely a data race. Disjointness isn't a bookkeeping nicety; it's the single invariant that later lets Section 3.1's Cut rule promise race-freedom, and it's why $!A$/$?A$ (Section 3.4) need their own dedicated Weaken/Contract rules rather than treating every proposition as freely shareable.

**Rust grounding.** This is, almost verbatim, what the borrow checker enforces for owned values. An environment is a set of *resources each owned exactly once*; combining two environments is only sound if their resource sets are disjoint — exactly like `std::mem::take`-style consumption, or moving two different `Vec<T>`s into a function that must not receive aliases of the same buffer:

```rust
struct Env(Vec<(String, Prop)>);

impl Env {
    /// Combine two environments — the Rust-borrow-checker analogue of
    /// CP's "Γ, Δ" environment-combination requiring fn(Γ) ∩ fn(Δ) = ∅.
    fn combine(self, other: Env) -> Result<Env, String> {
        for (name, _) in &self.0 {
            if other.0.iter().any(|(n, _)| n == name) {
                return Err(format!("channel {name} used on both sides — a race"));
            }
        }
        let mut merged = self.0;
        merged.extend(other.0);
        Ok(Env(merged))
    }
}
```

A linear channel binding is a value you can *move* out of a `Vec` exactly once; trying to use it twice is a compile error in Rust for the same underlying reason it's a typing error in CP.

## The process grammar

Processes $P, Q, R$ are:

$$
\begin{array}{lll}
P,Q,R ::= & x \leftrightarrow y & \text{link} \\
 & \nu x{:}A.(P \mid Q) & \text{parallel composition} \\
 & x[y].(P \mid Q) & \text{output} \\
 & x(y).P & \text{input} \\
 & x[\mathsf{inl}].P \;\mid\; x[\mathsf{inr}].P & \text{left / right selection} \\
 & x.\mathsf{case}(P,Q) & \text{choice} \\
 & {!x(y).P} & \text{server accept} \\
 & {?x[y].P} & \text{client request} \\
 & x[A].P & \text{output a type} \\
 & x(X).P & \text{input a type} \\
 & x[\,].0 \;\mid\; x().P \;\mid\; x.\mathsf{case}() & \text{empty output / input / choice}
\end{array}
$$

This is a variant of Milner's $\pi$-calculus, but with one deliberate departure worth flagging because it trips people up: **both output and input names are bound.** In ordinary $\pi$-calculus, $\bar x\langle y \rangle.P$ *sends* the already-existing free name $y$; here, $x[y].(P \mid Q)$ *allocates a fresh* $y$, transmits that, and only then runs $P$ and $Q$. Concretely: `x[y].(P | Q)` behaves like the $\pi$-calculus term $\nu y.\, x\langle y \rangle.(P \mid Q)$ — the binder is baked into the output form itself. (Square brackets mark output, round brackets mark input — the paper considered the alternative $\pi$-calculus-style overline notation $\bar x(y).P$ and rejected it because overlines are easy to typo-miss on a whiteboard or in a diff, while bracket-shape is unambiguous.)

Bound-name summary: in $\nu x{:}A.(P \mid Q)$, $x$ is bound in *both* $P$ and $Q$; in $x[y].(P \mid Q)$, $y$ is bound only in $P$; in $x(y).P$, $?x[y].P$, and $!x(y).P$, $y$ is bound in $P$; in $x(X).P$, the *propositional* variable $X$ is bound in $P$. $\mathsf{fn}(P)$ denotes $P$'s free names.

**Rust grounding**, continuing the AST theme:

```rust
enum Proc {
    Link(String, String),                          // x ↔ y
    Cut(String, Prop, Box<Proc>, Box<Proc>),        // νx:A.(P | Q)
    Output(String, String, Box<Proc>, Box<Proc>),   // x[y].(P | Q)
    Input(String, String, Box<Proc>),               // x(y).P
    SelectL(String, Box<Proc>),                     // x[inl].P
    SelectR(String, Box<Proc>),                     // x[inr].P
    Case(String, Box<Proc>, Box<Proc>),             // x.case(P, Q)
    ServerAccept(String, String, Box<Proc>),        // !x(y).P
    ClientRequest(String, String, Box<Proc>),       // ?x[y].P
    TypeOutput(String, Prop, Box<Proc>),            // x[A].P
    TypeInput(String, String, Box<Proc>),           // x(X).P
    EmptyOutput(String),                            // x[].0
    EmptyInput(String, Box<Proc>),                  // x().P
    EmptyCase(String),                              // x.case()
}
```

Every variant here will get exactly one typing rule in the sections that follow, and every typing rule introduces exactly one connective from the `Prop` grammar above — the two enums are designed to be in lockstep, which is the whole point of reading proofs as programs.

## Judgments, and what erasure reveals

Typing judgments in CP take the form

$$
P \vdash x_1{:}A_1, \ldots, x_n{:}A_n
$$

read as: *process $P$ communicates along each channel $x_i$, obeying the protocol $A_i$.* This is where the Curry-Howard payoff becomes literal rather than metaphorical: **erase the process term and the channel names from any CP derivation, and what's left is a valid derivation of** $\vdash A_1, \ldots, A_n$ **in ordinary one-sided classical linear logic, exactly as Girard presented it in 1987.** Every rule shown in this article and the next several is simultaneously a typing rule for a process *and* an inference rule of a proof system — they're not two systems bolted together, they're one system read two ways.

## Axiom: forwarding

$$
\dfrac{}{w \leftrightarrow x \;\vdash\; w{:}A^\perp,\, x{:}A} \;\; \mathsf{Ax}
$$

Read $x \leftrightarrow y$ as *forwarding*: anything received on $x$ is retransmitted on $y$, and vice versa — a channel splice. Duality is what makes this typeable at all: the two ends necessarily carry dual protocols, because whatever one end sends, the other must be ready to receive.

It's worth contrasting this with Bellin and Scott's (1994) earlier version of the same idea, because the difference previews a theme (generality vs. restriction) that recurs throughout CP. They restrict the axiom to *atomic* propositional-variable types only, and encode it as the $\pi$-calculus term $w(y).x\langle y\rangle.0$ — a link that forwards **exactly once**, and only in the direction from $X$ to $X^\perp$. CP's axiom, by contrast, forwards **any number of times, in either direction**, and at **every** type, not just variables. That generality is precisely what Wadler needs to give the axiom a uniform interpretation at all fourteen connectives (Section 3.7 leans on this for polymorphism, where a link at an *instantiated* type variable must still behave sensibly) — the cost of Bellin and Scott's restriction, as the paper notes, is that it makes parametric polymorphism awkward to support at all.

## Cut: parallel composition, and the seam that must not leak

$$
\dfrac{P \vdash \Gamma, x{:}A \qquad Q \vdash \Delta, x{:}A^\perp}{\nu x{:}A.(P \mid Q) \;\vdash\; \Gamma, \Delta} \;\; \mathsf{Cut}
$$

Read as: $P$ communicates along $x$ obeying $A$; $Q$ communicates along the *same* $x$ obeying the dual protocol $A^\perp$; run them concurrently, with $x$ restricted (private) between them. Two details matter enough to dwell on:

**$\Gamma$ and $\Delta$ must be disjoint.** This is exactly the linear-environment-combination rule from two sections up, applied at the moment two processes are wired together. **What breaks without it:** if $P$ and $Q$ could share some other channel $z$ in addition to $x$, then $z$ would offer a *second* communication path between them, alongside $x$ — and two independent, unordered communication paths between the same pair of processes is the textbook setup for a race (which one fires first?) or a deadlock (each waits on the other's channel). Disjointness is what pins $P$ and $Q$ to *exactly one* shared channel, $x$, making their interaction fully determined. (There is one narrow, deliberate exception the paper introduces later: once exponentials are in play, $\Gamma$ and $\Delta$ *may* share channels of type $?B$ — because those only ever talk to a *replicable* server, which by construction behaves identically no matter how many clients dial in, so sharing one doesn't reintroduce the race. That's covered in the article on servers and clients.)

**$x$ has different types on the two sides — $A$ in $P$, but $A^\perp$ in $Q$.** This looks like a typo until you notice it's the same "session type evolves, but the identity of the channel doesn't" idea introduced in the article on the twist: the *syntax* $\nu x{:}A.(\ldots)$ deliberately carries the type $A$ so that, given the type of every free name, a CP term has a **unique** type derivation — you never have to guess which rule produced a given term.

**Lean grounding.** If you're building an elaborator, Cut is worth recognizing as *exactly* the shape of a lemma-composition or a `have`-block splitting a proof context: you prove a fact using context $\Gamma$, prove another using disjoint context $\Delta$, and combine them — the Lean tactic-state analogue of `Γ ⊢ A` and `Δ ⊢ A → B` combining via `apply`. The disjointness side-condition is what a linear-logic-aware elaborator would need to check that no hypothesis got silently reused.

## Structural equivalences: Swap and Assoc

Cut elimination — proof normalization — corresponds to process *reduction*. Before any reduction can fire, two purely *structural* equivalences let you rearrange cuts without changing meaning:

**(Swap)** — a cut is symmetric:

$$
\nu x{:}A.(P \mid Q) \;\equiv\; \nu x{:}A^\perp.(Q \mid P)
$$

This plays the same role as the $\pi$-calculus law $P \mid Q \equiv Q \mid P$: which process you list first is bookkeeping, not meaning.

**(Assoc)** — cuts can be reordered:

$$
\nu y.(\nu x.(P \mid Q) \mid R) \;\equiv\; \nu x.(P \mid \nu y.(Q \mid R))
$$

This plays the combined role of $\pi$-calculus associativity, $(P \mid Q) \mid R \equiv P \mid (Q \mid R)$, *and* scope extrusion, $(\nu x.P) \mid Q \equiv \nu x.(P \mid Q)$ when $x \notin \mathsf{fn}(Q)$ — a three-way process composition can be regrouped however is convenient, as long as each private channel's scope is respected.

## Reduction (AxCut): the first real computation step

$$
\dfrac{\overline{w \leftrightarrow x \vdash w{:}A^\perp, x{:}A}\;\;\mathsf{Ax} \qquad P \vdash \Gamma, x{:}A^\perp}{\nu x.(w \leftrightarrow x \mid P) \vdash \Gamma, w{:}A^\perp} \;\; \mathsf{Cut} \quad\Longrightarrow\quad P\{w/x\} \vdash \Gamma, w{:}A^\perp
$$

A cut against a bare forwarding link is pointless — the link does nothing but relay, so cutting $P$ against it should be the same as just renaming $P$'s channel from $x$ to $w$ directly. That's exactly what (AxCut) says: the whole two-node derivation on the left collapses to $P\{w/x\}$, substitution of $w$ for $x$ throughout $P$.

<svg viewBox="0 0 620 210" xmlns="http://www.w3.org/2000/svg" font-family="ui-monospace, monospace" font-size="14">
  <!-- Left: Ax feeding Cut -->
  <rect x="10" y="20" width="230" height="46" rx="6" fill="#4a5568" stroke="#888888" stroke-width="1.5"/>
  <text x="125" y="48" text-anchor="middle" fill="#f5f5f5">w ↔ x ⊢ w:A⊥, x:A</text>
  <text x="248" y="48" fill="#888888" font-size="12">Ax</text>

  <rect x="10" y="90" width="230" height="46" rx="6" fill="#4a5568" stroke="#888888" stroke-width="1.5"/>
  <text x="125" y="118" text-anchor="middle" fill="#f5f5f5">P ⊢ Γ, x:A⊥</text>

  <line x1="125" y1="66" x2="125" y2="150" stroke="#888888" stroke-width="1.5"/>
  <line x1="60" y1="150" x2="190" y2="150" stroke="#888888" stroke-width="1.5"/>
  <rect x="20" y="158" width="210" height="42" rx="6" fill="#3b4b5c" stroke="#888888" stroke-width="1.5"/>
  <text x="125" y="184" text-anchor="middle" fill="#f5f5f5" font-size="12">νx.(w↔x | P) ⊢ Γ, w:A⊥</text>
  <text x="248" y="184" fill="#888888" font-size="12">Cut</text>

  <!-- Arrow -->
  <line x1="290" y1="105" x2="360" y2="105" stroke="#888888" stroke-width="2"/>
  <polygon points="360,100 372,105 360,110" fill="#888888"/>
  <text x="325" y="90" text-anchor="middle" fill="#888888" font-size="12">reduces to</text>

  <!-- Right: substituted result -->
  <rect x="390" y="85" width="220" height="46" rx="6" fill="#5b7c99" stroke="#888888" stroke-width="1.5"/>
  <text x="500" y="113" text-anchor="middle" fill="#f5f5f5">P{w/x} ⊢ Γ, w:A⊥</text>
</svg>

*A two-node derivation (a bare link cut against a process $P$) collapses to $P$ with $x$ renamed to $w$ — the link itself disappears entirely.*

This is the whole calculus's very first example of the Curry-Howard slogan made computational: **normalizing a proof is running a program.** Every subsequent article in this vault on CP's connectives (⊗/⅋, ⊕/&, !/?, ∃/∀) introduces exactly one more reduction rule of this same shape — a "principal cut" between a connective and its dual, collapsing to something smaller and more computed. (AxCut) is the simplest possible instance; the article on [[Commuting-Conversions-and-Cut-Elimination|commuting conversions and cut elimination]] is where the *general* theorem — every process eventually reduces to a cut-free one, i.e., every program eventually finishes computing — gets proved.

## Where this leads

This article is the fixed backdrop against which every later CP article operates: the fourteen-connective grammar, duality-as-involution, linear environments, the process grammar, and the two structural rules Axiom and Cut. Concretely, it feeds forward as:

- **Output/input, selection/choice, servers/clients, and polymorphism** (the next four articles) each add exactly one *principal* cut-reduction rule — a case where the cut variable's type was introduced by matching connectives on both sides — following the same "collapse to something smaller" pattern as (AxCut) above.
- **Commuting conversions and cut elimination** proves the general theorem that *every* CP process reduces to a cut-free one — the formal statement of "this calculus cannot deadlock," built entirely out of the (Swap), (Assoc), and reduction machinery introduced here.
- For the standing elaborator/verifier project: the linear-environment-splitting check in `Env::combine` above is *exactly* the side-condition a type-checker for CP (or for any linearly-typed IR) has to implement at every rule with more than one premise — it's the mechanical form of "no channel gets used twice," and it will reappear, unchanged in spirit, anywhere a Hoare-triple-style resource-tracking checker needs to split a context between two subgoals.
