---
title: GV — A Session-Typed Functional Language
source: "Propositions as Sessions (Wadler)"
chapter: "Chapter 4 (front matter), pp. 23–27"
tags: [type-theory, linear-logic, session-types, process-calculus, GV, functional-programming]
---

[[book-guidelines|↩ Back to guidelines]]

# GV: A Session-Typed Functional Language

## The problem: you don't want to program directly in CP

Everything [[CP-a-Classical-Linear-Logic-Process-Calculus|CP]] gives you — $\otimes$, $\parr$, $\oplus$, $\&$, $!$, $?$, cut elimination as communication, a proof that well-typed processes never deadlock — is a *logic*. It's the target you'd compile to, not the language you'd sit down and write a payment-processing script in. CP's processes are proof terms; nobody wants to hand-write proof terms for their business logic any more than they want to hand-write assembly.

What programmers actually want is a functional language — the kind with `let`, function application, pairs — that happens to have channels as first-class values, where the *type* of a channel tells you, statically, what you're allowed to do with it next. That's GV. It's not a new logic; it's an ordinary(-ish) linear $\lambda$-calculus with six extra term forms for talking down a channel, and — this is the payoff the paper is actually after — every well-typed GV program compiles into CP, inheriting CP's race- and deadlock-freedom for free. (That compilation is a separate, meaty topic in its own right — see the companion article, [[Translating-GV-into-CP]] — this article stays entirely on GV's home turf.)

GV is Wadler's own variant of a language originally due to Gay and Vasconcelos (2010); the name is a pun — "GV" for Gay–Vasconcelos, but Wadler glosses his version as "Good Variation," because a few changes to their original design are exactly what make the deadlock-freedom guarantee possible. We'll flag those changes as we go, because they're not cosmetic — they're where the paper's actual argument lives.

## Session types: the grammar of "what a channel promises to do next"

A **session type** describes a protocol — a sequence of things you're allowed to do down a channel, in order, where each action changes what's allowed next. The grammar is:

$$
S ::= \; !T.S \mid {?T.S} \mid \oplus\{l_i:S_i\}_{i\in I} \mid \&\{l_i:S_i\}_{i\in I} \mid \mathsf{end}_! \mid \mathsf{end}_?
$$

Read each constructor as an instruction plus a continuation:

- $!T.S$ — **send** a value of type $T$, then the channel behaves as $S$.
- $?T.S$ — **receive** a value of type $T$, then the channel behaves as $S$.
- $\oplus\{l_i:S_i\}_{i\in I}$ — **choose** one of the labels $l_i$ to send, then behave as the corresponding $S_i$.
- $\&\{l_i:S_i\}_{i\in I}$ — **offer** a choice among the labels; whichever the other end selects, behave as that $S_i$.
- $\mathsf{end}_!$ / $\mathsf{end}_?$ — the protocol is **over**; nothing more may be sent or received on this channel.

That last pair is the first place GV departs from Gay and Vasconcelos, and it's worth pausing on, because the reason is not stylistic. Gay and Vasconcelos have a single, self-dual `end`. Wadler splits it into two: $\mathsf{end}_!$, "convenient for use after a send or select," and $\mathsf{end}_?$, "convenient for use after a receive or case." Concretely, once you've *sent* your last message, your side of the protocol is naturally described as $\mathsf{end}_!$; once you've *received* your last message, your side is $\mathsf{end}_?$. The two are duals of each other — $\overline{\mathsf{end}_!} = \mathsf{end}_?$ — so the two parties on a finished channel always agree that it's finished, just from complementary vantage points. This split isn't decoration: it's what makes GV translate cleanly into CP's own multiplicative units $1$ and $\bot$ (see the translation article), and — as we'll see below — it's tied to *how* a finished channel gets deallocated.

**Duality** extends over the whole grammar, and it's what makes two session types *compatible partners* — one side's protocol should be exactly the mirror image of the other's:

$$
\overline{!T.S} = {?T.\overline S} \qquad \overline{?T.S} = {!T.\overline S}
$$
$$
\overline{\oplus\{l_i:S_i\}} = \&\{l_i:\overline{S_i}\} \qquad \overline{\&\{l_i:S_i\}} = \oplus\{l_i:\overline{S_i}\}
$$
$$
\overline{\mathsf{end}_!} = \mathsf{end}_? \qquad \overline{\mathsf{end}_?} = \mathsf{end}_!
$$

Input is dual to output, select is dual to offer, and the two terminators are dual to each other — but duality does *not* flip the payload type $T$ itself. If I send an `Int`, you receive an `Int`; duality only flips the *direction* of the action, never the data.

## Session types are types, but not every type is a session type

Session types sit inside a larger grammar of ordinary functional types:

$$
T, U, V ::= S \mid T \otimes U \mid T \multimap U \mid T \to U \mid \mathsf{Unit}
$$

So every session type $S$ is automatically a type $T$, but you also get an ordinary tensor product $T \otimes U$ (for pairs), a **linear** function space $T \multimap U$, an **unlimited** function space $T \to U$, and a unit type. GV then classifies every type as linear or unlimited:

$$
\mathsf{lin}(S) \quad \mathsf{lin}(T\otimes U) \quad \mathsf{lin}(T \multimap U) \quad \mathsf{un}(T \to U) \quad \mathsf{un}(\mathsf{Unit})
$$

Session types, tensor products, and linear functions are **linear** — a value of that type must be used *exactly once*. Unlimited functions and `Unit` are **unlimited** — those can be duplicated or dropped freely, and they're the types that support the structural rules `Weaken` and `Contract` in Figure 6. The intuition matches the physical picture: a channel is a real, singular resource — you can't duplicate a half-finished conversation any more than you can duplicate a half-eaten sandwich — so it *has* to be linear, and that linearity propagates to anything containing a channel.

## The term grammar: six familiar forms, six new ones

$$
L, M, N ::= x \mid \mathsf{unit} \mid \lambda x.N \mid LM \mid (M,N) \mid \mathsf{let}\,(x,y)=M\,\mathsf{in}\,N
$$
$$
\mid\; \mathsf{send}\,M\,N \mid \mathsf{receive}\,M \mid \mathsf{select}\,l\,M \mid \mathsf{case}\,M\,\mathsf{of}\,\{l_i:x.N_i\}_{i\in I} \mid \mathsf{with}\,x\,\mathsf{connect}\,M\,\mathsf{to}\,N \mid \mathsf{terminate}\,M
$$

The first six are just a linear $\lambda$-calculus: identifiers, the unit constant, abstraction, application, pair construction, pair deconstruction. Nothing here should surprise anyone who has used a linear or affine type system before. The typing rules for these (Figure 6: `Id`, `Unit`, `Weaken`, `Contract`, $\multimap$-I/E, $\to$-I/E, $\otimes$-I/E) are the standard ones, with one small wrinkle worth flagging: GV does **not** give unlimited functions their own separate application rule. Instead, an unlimited function may simply be *treated as* a linear one and applied via the linear rule. This is a real simplification over Gay and Vasconcelos, who needed two versions of `send` to cope with currying complications — GV sidesteps that by making `send` a genuine language construct (not a curried function constant), so one rule for `send` suffices.

The last six forms are where GV actually talks to channels, and this is the part worth reading closely.

## The key design decision: operations consume a channel and return the next one

Here is the sentence that governs everything else in this section, straight from the paper:

> "Channels are managed linearly, so each operation on channels takes the channel before the operation as an argument, and returns the channel after the operation as the result."

Every single channel operation is threaded this way. Look at the rule for output:

$$
\frac{\Phi \vdash M : T \qquad \Psi \vdash N : {!T.S}}{\Phi,\Psi \vdash \mathsf{send}\ M\ N : S} \quad \text{Send}
$$

`send M N` takes the payload $M$ (of type $T$) and the channel $N$ (currently at session type $!T.S$, i.e., "I'm ready to send a $T$"), and evaluating it *hands back a new channel* — now at type $S$, the continuation of the protocol *after* the send. You didn't get "the same" channel back with a mutated type annotation; you got a genuinely new value, and the old one is gone. The rule for input is the dual:

$$
\frac{\Phi \vdash M : {?T.S}}{\Phi \vdash \mathsf{receive}\ M : T \otimes S} \quad \text{Receive}
$$

`receive M` takes a channel ready to receive, and returns a *pair*: the value received (type $T$) and the updated channel (type $S$). The pair has to be linear, because it contains a channel, and channels can't be discarded or duplicated for free.

### This is exactly Rust's typestate / consuming-builder pattern

If you've ever written a Rust API where a builder method takes `self` by value and returns `Self` — so the compiler statically prevents you from calling `.build()` before `.set_required_field()` — you've already built a GV channel. The direct translation:

```rust
// Each session type S becomes a distinct Rust type.
// "send a Name, then behave as S" becomes a struct parameterized by
// the *next* state, so the compiler tracks protocol position in the type.
struct Send<T, S> { channel: RawChannel, _marker: PhantomData<(T, S)> }
struct Recv<T, S> { channel: RawChannel, _marker: PhantomData<(T, S)> }
struct End;                     // corresponds to end_! or end_? — two
struct EndRecv;                 // distinct marker types, mirroring GV's split

impl<T, S> Send<T, S> {
    // Consumes `self` (the old session state) — you cannot call `send`
    // twice on the same channel, because the old value is gone after this.
    fn send(self, value: T) -> S {
        self.channel.write(value);
        // SAFETY: protocol invariant — the raw channel now speaks `S`.
        unsafe { std::mem::transmute(self.channel) }
    }
}

impl<T, S> Recv<T, S> {
    fn receive(self) -> (T, S) {
        let value = self.channel.read();
        (value, unsafe { std::mem::transmute(self.channel) })
    }
}

// Buy ≜ !Name.!Credit.?Receipt.end_?
type Buy = Send<Name, Send<Credit, Recv<Receipt, EndRecv>>>;
```

The point isn't the `unsafe`/`transmute` plumbing (a real crate like `rumpsteak` or `session_types` hides that behind a safe API) — the point is what the *types* buy you. Because `send` consumes `self: Send<T, S>` and returns `S`, there is no way to call `send` again on the value you already sent through; the old typestate is gone, moved out from under you, exactly as GV's linear typing forbids using a channel twice. A protocol violation — sending when you should be receiving, or using a channel after `end` — isn't a runtime error to catch; it's a type error the compiler catches before the program runs. GV's `Send`/`Receive` typing rules *are* Rust's ownership discipline, specialized to the shape of a communication protocol instead of the shape of a resource handle.

(For readers more comfortable thinking in terms of typing judgments than borrow-checker mechanics: in Lean, you'd model this as an indexed family `Channel : SessionType → Type`, with `send : Channel (SessionType.send T S) → T → Channel S` — the session type literally indexes which operations are even well-typed to call, the same way `Vector n` indexes over length so `head` is only callable on `Vector (n+1)`.)

`select` and `case` follow the identical shape for the additive session types $\oplus$/$\&$ — `select l M` commits to branch $l$ and narrows the channel's type from the full offering down to just $S_l$; `case M of {l_i : x.N_i}$ pattern-matches on whichever branch the *other* end selected. Both are standard once you've internalized the send/receive pattern; the paper calls them "similar to Send and Receive, and standard."

## Creating and closing channels: `Connect` and `Terminate`

Two operations don't fit the "take a channel, return the next one" template, because they're about the channel's *birth* and *death* rather than a step in its middle.

**Connect** creates a brand-new channel, splitting it into two dual ends used by two concurrently-running subterms:

$$
\frac{\Phi, x:S \vdash M : \mathsf{end}_! \qquad \Psi, x:\overline S \vdash N : T}{\Phi, \Psi \vdash \mathsf{with}\ x\ \mathsf{connect}\ M\ \mathsf{to}\ N : T} \quad \text{Connect}
$$

`with x connect M to N` allocates a fresh channel named $x$; inside $M$ it's used at session type $S$, and inside $N$ (the *same name*, but a *different* term) it's used at the dual type $\overline S$. $M$ and $N$ run concurrently. Notice the asymmetry in the conclusion's typing: $M$ must finish having exhausted its side down to $\mathsf{end}_!$ — this is exactly why $\mathsf{end}_!$ is "convenient for use after a send" — while $N$'s result of type $T$ is what actually gets passed on to the rest of the program. As the paper puts it: "as is usual when forking off a value, only one of the two subterms returns a value that is passed to the rest of the program."

**Terminate** is what actually deallocates a channel once its protocol is exhausted:

$$
\frac{\Phi \vdash M : \mathsf{end}_?}{\Phi \vdash \mathsf{terminate}\ M : \mathsf{Unit}} \quad \text{Terminate}
$$

`terminate M` consumes a channel that's finished on the *receiving* end ($\mathsf{end}_?$) and gives back `Unit` — a value so uninteresting it's `un`-classified, meaning you're free to discard it (which you usually do, via a `let unit = ... in`).

### Why not the more obvious design?

You might reasonably ask: why not just have `connect` return *both* ends of the channel as a pair, of type $S \otimes \overline S$, and have a single `close` that consumes a pair `end_! ⊗ end_?` and returns unit? Wadler considers exactly this alternative and rejects it, for a reason that matters a great deal:

> "Both of these designs are difficult to translate into CP, which suggests they may suffer from deadlock."

That sentence is doing a lot of work, and it's the real payoff of this whole design. `Connect`/`Terminate` aren't an arbitrary API choice — they were *reverse-engineered from the requirement that the translation into CP go through cleanly*, because it's exactly that translation (companion article: [[Translating-GV-into-CP]]) that inherits CP's proof of deadlock-freedom. An API that merely "feels" more symmetric but doesn't map onto a legal CP derivation is an API that might let you write a program that deadlocks — the type system would accept it, but the runtime behavior would hang. This is why GV replaces Gay and Vasconcelos's original `accept`/`request`/`fork` triple with `with-connect-to`/`terminate`: the new pair is the one that provably compiles into deadlock-free CP processes.

## Worked example: buy/sell, now as a program you could actually run

This is the same commerce scenario used throughout the paper's CP sections, re-expressed entirely in GV's surface syntax:

$$
\mathsf{Buy} \triangleq {!\mathsf{Name}.{!\mathsf{Credit}.{?\mathsf{Receipt}.\mathsf{end}_?}}}
\qquad
\mathsf{Sell} \triangleq {?\mathsf{Name}.{?\mathsf{Credit}.{!\mathsf{Receipt}.\mathsf{end}_!}}}
$$

Read $\mathsf{Buy}$ as: send a product name, send a credit-card number, receive a receipt, done (as the receiving side, hence $\mathsf{end}_?$). $\mathsf{Sell}$ is exactly its dual, and indeed $\mathsf{Buy} = \overline{\mathsf{Sell}}$.

```text
buy_x  ≜  let u        = get-name    in
          let x1       = send u x    in
          let v        = get-credit  in
          let x2       = send v x1   in
          let (w, x3)  = receive x2  in
          let unit     = terminate x3 in
          put-receipt w

sell_x ≜  let (u, x1) = receive x   in
          let (v, x2) = receive x1  in
          let w        = compute u v in
          send w x2
```

Watch the channel variable thread through: `x`, then `x1`, then `x2`, then `x3` — a fresh name at every step, because each operation genuinely consumes the old channel value and produces a new one. This isn't the same variable mutated in place; `x1` and `x2` are different bindings with different (session) types, which is precisely the "typestate" property from the Rust analogy above made visible in the surface syntax itself. Assuming environments

$$
\Phi \triangleq \mathsf{get\text{-}name}:\mathsf{Name},\ \mathsf{get\text{-}credit}:\mathsf{Credit},\ \mathsf{put\text{-}receipt}:\mathsf{Receipt}\to\mathsf{Rest}
$$
$$
\Psi \triangleq \mathsf{compute}:\mathsf{Name}\to\mathsf{Credit}\to\mathsf{Receipt}
$$

the two sides typecheck as $\Psi, x:\mathsf{Sell} \vdash \mathsf{sell}_x : \mathsf{end}_!$ and $\Phi, x:\mathsf{Buy} \vdash \mathsf{buy}_x : \mathsf{Rest}$, and since $\mathsf{Buy} = \overline{\mathsf{Sell}}$, `Connect` applies directly:

$$
\frac{\Psi, x:\mathsf{Sell} \vdash \mathsf{sell}_x : \mathsf{end}_! \qquad \Phi, x:\mathsf{Buy} \vdash \mathsf{buy}_x : \mathsf{Rest}}{\Psi,\Phi \vdash \mathsf{with}\ x\ \mathsf{connect}\ \mathsf{sell}_x\ \mathsf{to}\ \mathsf{buy}_x : \mathsf{Rest}} \quad \text{Connect}
$$

Run this program and the type system has already guaranteed, before a single message crosses the channel, that the seller will never try to send a receipt before receiving a credit card number, the buyer will never try to receive twice in a row, and neither side will forget to close its end.

## Where this leads

GV is the *source* language of the paper's other headline construction: a type-preserving translation $\llbracket\,\cdot\,\rrbracket$ from GV terms into CP processes (Theorem 3, companion article [[Translating-GV-into-CP]]). That translation is where GV's promise gets cashed in — because CP satisfies top-level cut elimination (see [[Commuting-Conversions-and-Cut-Elimination]]), and the translation preserves typing, every well-typed GV program compiles to a CP process that is *provably* free of races and deadlock, with zero extra proof burden on the GV programmer. The `Connect`/`Terminate` design choice documented above only makes sense in light of that destination — it's worth re-reading this article's "why not the more obvious design" section after working through the translation, once you can see concretely which CP derivation each GV construct lands on.

For the reader building toward a Rust verifier: GV's `Send`/`Receive` rules are a genuine, minimal instance of "typing judgment as static protocol checker" — the same shape of problem as verifying a Hoare-triple-annotated API's calling convention, just specialized to communication instead of general pre/post-conditions. The linear threading of channel values through `let`-bindings is the same substitution-and-context-management discipline that soundness proofs for such systems lean on throughout.
