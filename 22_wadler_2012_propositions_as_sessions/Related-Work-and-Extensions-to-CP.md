---
title: Related Work and Extensions to CP
source: "Propositions as Sessions — Philip Wadler (2012)"
chapters: "5–6, pp. 31–34"
tags: [type-theory, linear-logic, session-types, process-calculus, curry-howard, cut-elimination]
---

[[book-guidelines|↩ Back to guidelines]]

# Related Work and Extensions to CP

Every article so far in this vault has stayed *inside* CP and GV: building the connectives, proving cut elimination, translating one calculus into the other. This one steps outside. Wadler's closing two sections do two different things, and it's worth being clear about which is which before diving in. Chapter 5 (Related Work) answers "where does this sit among everyone else's attempts at the same problem?" Chapter 6 (Conclusion) answers a more provocative question: "what did we give up to get deadlock freedom, and what happens if we deliberately take it back?"

That second question is the more interesting one to sit with, so it's worth previewing the shape of the answer before the details: CP is deadlock-free *because* its Cut rule forces every parallel composition to share exactly one channel, and because that channel gets used in a disciplined, [[CP-a-Classical-Linear-Logic-Process-Calculus#Axiom: forwarding|forwarding]]-safe way. Loosen either constraint and you get a strictly more expressive calculus — and you lose the guarantee. This mirrors something you already know from ordinary $\lambda$-calculus: simply-typed $\lambda$-calculus always terminates, but you can recover full Turing-completeness by relaxing typing (or by allowing a fixpoint combinator). The same trick works here.

## Where CP and GV Sit in the Literature

### The session-types lineage

Session types predate this paper by two decades. Honda (1993) introduced them; Takeuchi, Honda, and Kubo (1994) and Honda, Vasconcelos, and Kubo (1998) developed the associated language primitives and type discipline; Yoshida and Vasconcelos (2007) revisited the design. Gay and Hole (2005) added subtyping. GV itself — the functional language you met in [[GV-a-Session-Typed-Functional-Language]] — descends directly from Gay and Vasconcelos (2010); Wadler's version is a *simplified and deadlock-hardened* variant of theirs, as [[GV-a-Session-Typed-Functional-Language]] and [[Translating-GV-into-CP]] both discussed. Fähndrich et al. (2006) even took session types out of the research literature and into Singularity OS, describing real operating-system services with them.

The point worth absorbing: session types as an *engineering* discipline (a type system that catches protocol violations) existed well before anyone connected them tightly to a logic. CP's contribution isn't inventing session types — it's showing that a particular, careful choice of session-type discipline *is* a proof system, with cut elimination *as* the safety argument, rather than session types merely being *inspired by* linear logic's flavor.

### Alternative routes to deadlock freedom

CP is not the only system that promises deadlock freedom for session-typed processes — it's just the only one that gets it from cut elimination for free. Sumii and Kobayashi (1998) achieve it by attaching a separate partial order on *time tags* to processes and requiring communications to respect that order. Carbone and Debois (2010) achieve it by imposing a constraint on the *dependency graph* between channels — essentially, forbidding cyclic waiting directly, as a graph-theoretic side condition.

Both of these are perfectly valid engineering solutions, but notice the difference in *kind*. They add a bespoke mechanism — a time-tag calculus, a graph acyclicity check — bolted onto an otherwise ordinary session-typed system, and then prove (by hand, as a separate theorem) that the mechanism prevents deadlock. CP proves nothing extra: deadlock freedom for CP is a *corollary* of Theorem 2 from [[Commuting-Conversions-and-Cut-Elimination]], which is itself just the statement that a well-formed proof of classical linear logic normalizes. The safety property isn't a bolt-on constraint you have to invent and separately justify — it falls out of trusting that the underlying logic is consistent. That's the entire thesis of the paper compressed into one comparison.

### Linear types for process calculi, more broadly

Kobayashi (2002) surveys a wide range of linear type systems for process calculi generally — most of which, Wadler notes, look rather different from session types. Kobayashi, Pierce, and Turner (1996) is the closest ancestor: an embedding of session types into a $\pi$-calculus equipped with linear types for channels, predating (and partially prefiguring) the logic-first approach CP takes.

### Linear proof search, briefly

There's a tidy analogy buried in a short paragraph here, worth pulling out because it clarifies what CP is *not* doing. Functional programming, under Curry-Howard, arises from associating *program evaluation* with *proof normalization* (this is CP and GV's whole story). Logic programming, by contrast, arises from associating program evaluation with *proof search* — finding a proof at all, rather than simplifying one you already have. Miller (1992) and Kobayashi and Yonezawa (1993, 1994, 1995) explore linear-logic-based logic-programming systems with some structural resemblance to CP, but they're solving a different problem: search, not normalization. If you've ever wondered how Prolog-style unification-driven search relates to type-checking, this is the two-sentence version of the relationship — and it's a distinction worth keeping in mind if your own elaborator project ever needs to decide whether a piece of it is "checking a proof" (normalization-flavored) or "finding a proof" (search-flavored, closer to what a metavariable-resolution pass does).

### Polymorphism: Church-style versus Curry-style

CP's $\exists$/$\forall$ (from [[Polymorphism-in-CP]]) trace back to Turner's polymorphic $\pi$-calculus (1995), discussed further by Pierce and Turner (2000) and Pierce and Sangiorgi (2000). Caires, Pérez, Pfenning, and Toninho (2013) extend session types with polymorphism and establish logical relations for *parametricity* — the formal statement that a polymorphic process genuinely can't inspect the type it was instantiated with, only use it abstractly (this is the session-typed analogue of Reynolds' parametricity theorem for System F).

All of the systems just named — CP included — use **explicit, Church-style polymorphism**: the type argument is a real syntactic thing transmitted along a channel (recall `x[A].P` from [[Polymorphism-in-CP]] — you *see* the proposition $A$ get sent). Berger, Honda, and Yoshida (2005) instead build a polymorphically-typed session calculus with **implicit, Curry-style polymorphism** — no term-level trace of the type argument at all, inference does the work. If your elaborator project cares about implicit-argument resolution (per your standing goals), this is the fork in the road to be aware of: CP shows you the *explicit* discipline, where type application is a real reduction step you can point to; a Curry-style system instead pushes all of that work into a unification/elaboration pass that never appears in the reduced term. Seeing both ends of that spectrum — one where instantiation is a first-class computational step, one where it's erased before you ever see a "reduction" — is useful calibration for deciding how much of your own elaborator's work should stay visible in the core term language versus get compiled away before type-checking proper begins.

### Linear logic as a process calculus, and CP's direct ancestors

Abramsky (1993, 1994) and Abramsky, Gay, and Nagarajan (1996) proposed various interpretations of linear logic as a process calculus, with the second elaborated in detail by Bellin and Scott (1994) — this is the "pairing interpretation" you already met in [[The-Twist-Reinterpreting-the-Linear-Connectives]].

CP's immediate lineage, though, runs through Caires, Pfenning, Toninho, and Pérez:

- Caires and Pfenning (2010) first identified the correspondence between linear-logic formulas and session types — this is $\pi$DILL, the calculus that motivates everything in this paper.
- Pfenning, Caires, and Toninho (2011) extend the correspondence to **dependent types**, in a stratified system with concurrent communication at the outer level and a dependently-typed functional language at the inner level; a companion paper adds proof-carrying code and proof irrelevance.
- Toninho, Caires, and Pfenning (2012) explore encoding $\lambda$-calculus *into* $\pi$DILL.
- Pérez, Caires, Pfenning, and Toninho (2012) introduce logical relations on linear-typed processes to prove *termination* and *contextual equivalence* — a strengthening beyond the deadlock-freedom guarantee CP gives you.
- Caires, Pfenning, and Toninho (2012a) is an invited-talk survey tying the above together.
- Two papers postdating the ICFP version of this paper: Caires, Pérez, Pfenning, and Toninho (2013) add polymorphism and parametricity (the paper cited above); Toninho, Caires, and Pfenning (2013) use *monads* to integrate a functional language with a session-typed process calculus — worth knowing about if you ever want your own elaborator to interleave effectful and session-typed computation cleanly.

Mazurak and Zdancewic (2010) take a genuinely different route to a Curry-Howard reading of session types: **Lolliproc**, which relates `call/cc`-style control operators to communication via a double-negation operator on types. It's a reminder that "propositions as sessions" isn't the only Curry-Howard story you could tell about concurrency — classical logic's double-negation elimination has its own operational reading, distinct from the cut-elimination-as-communication story CP tells.

### DILL versus CLL: the paper's most consequential design argument

This is the part of the Related Work section that earns the most space, and for good reason — it's a direct rebuttal to a design choice CP explicitly rejects, made by the very people CP is built on top of.

Caires, Pfenning, and Toninho (2012b) formulate a variant of $\pi$DILL using **one-sided sequents of classical linear logic**, which they call $\pi$CLL — structurally very close to CP. But they differ in three particulars Wadler flags explicitly:

1. $\pi$CLL's bookkeeping is more elaborate, using *two* zones (one linear, one intuitionistic) rather than CP's single environment.
2. $\pi$CLL has **no axiom rule**, so it cannot easily support polymorphism the way CP's Axiom-plus-$\exists/\forall$ can (recall from [[Polymorphism-in-CP]] how central the Axiom rule turned out to be for the flip-derivation trick and for instantiation).
3. $\pi$CLL does not support reductions corresponding to the commuting conversions (recall [[Commuting-Conversions-and-Cut-Elimination]]) — a real loss, since commuting conversions are what let *every* cut reduce, not just cuts adjacent to a matching principal pair.

And then there's the deeper argument, about **locality**: Caires, Pfenning, and Toninho state a preference for DILL over CLL because DILL satisfies a locality property for replicated input, while CLL (and hence CP) does not.

**What locality means, concretely.** A calculus satisfies locality if a name *received* along a channel can only be *used to send* on it afterward — never to receive again. Put differently: once you've been handed a channel endpoint, you're only allowed to act as the "output" party on it from then on; you can never turn around and listen on a name someone else gave you. This is a genuinely restrictive discipline. It matters for two reasons Wadler cites:

- **Implementation.** A runtime that knows every received name will only ever be used for sending can specialize its channel representation — there's an entire class of "who's allowed to read this?" bookkeeping it never has to do.
- **Extra observational equivalences.** Merro and Sangiorgi (2004) show that a process calculus restricted to locality satisfies *more* observational equivalences than one without the restriction — informally, more programs become provably interchangeable, because there are fewer ways a received name can be (mis)used to distinguish them.

Caires et al. only restrict *replicated* input specifically (not all input), because restricting all input turns out to be too severe a constraint for a usable session-typed calculus. But — and this is the honest caveat Wadler includes rather than glossing over — the good properties of locality have only actually been *studied* in the stronger, all-input-restricted setting. Whether locality-for-replicated-input-only buys you the same benefits is, as of this paper, an open question.

**Why CP doesn't bother.** CP just doesn't impose locality at all. This is a real, acknowledged cost of choosing the classical (CLL) formulation over the intuitionistic (DILL) one — you buy simplicity, symmetry, a single environment, an axiom rule, and full commuting conversions, and you pay for it by giving up whatever implementation and equivalence benefits locality would have bought you. Wadler doesn't pretend this is a free lunch; he's explicit that DILL vs. CLL is a genuine trade-off, not a strictly-better-strictly-worse comparison.

**The dependent-types remark.** One more data point, reported as a private communication from Pfenning: he believes DILL is likely to extend more gracefully to *dependent* types, while he suspects CLL is not, because strong sums (roughly, $\Sigma$-types) become degenerate in some classical settings — a result due to Herbelin (2005). Against that, Girard (1991) has argued that linear logic generally is more amenable to constructive treatment than traditional classical logic — so it's genuinely unclear, as the paper stands, whether CP's classical foundation is a dead end or a viable path for a future dependently-typed session calculus.

```lean
-- A rough sketch of what "locality" would forbid, if you tried to encode
-- it as a discipline on how a Lean-style kernel handles channel-like values.
-- Once a value has been *received* (its provenance marked `Received`),
-- locality says you may only ever eliminate it in "output" position —
-- you can never re-bind it as something you *receive from* again.
inductive Provenance
  | owned      -- this channel endpoint originated here
  | received   -- this channel endpoint was received from elsewhere

-- A (deliberately partial) locality check: a `received` endpoint may be
-- used to *send*, never to *receive* again. CP's Axiom rule and its
-- single shared linear environment make no such distinction — any name,
-- however it arrived, may appear on either side of an input or output
-- rule. That absence of a "how did this arrive" tag is exactly what CP
-- gives up by choosing CLL over DILL.
def canReceiveOn : Provenance → Bool
  | .owned    => true
  | .received => false   -- DILL enforces this; CP does not
```

If you're weighing DILL-vs-CLL-style trade-offs for your own verifier — say, deciding whether "a value received as a function argument may only be used, never pattern-matched-into-and-re-exported" is a discipline worth enforcing — this is exactly the kind of design decision this section is modeling: a genuine expressiveness/property trade-off, decided by which downstream guarantees (locality's implementation/equivalence benefits vs. CP's polymorphism/commuting-conversion completeness) you care about more.

## Breaking the Guarantee on Purpose: Mix and Binary Cut

The Conclusion opens with an analogy worth sitting with directly, because it reframes everything you've learned in this vault as *one point on a spectrum* rather than as the final word.

**Why does $\lambda$-calculus work so well as a foundation?** Partly *because* it isn't just one calculus — it's a family spanning a fragment that's guaranteed to terminate (simply-typed $\lambda$-calculus, System F, ...) and a fragment that can compute anything a Turing machine can (untyped $\lambda$-calculus, or a typed calculus with a general fixpoint operator bolted on). And critically, the terminating fragment isn't unrelated to the Turing-complete one — untyped $\lambda$-calculus can be *modeled* as a solution to the recursive type equation $X \simeq X \to X$ (a type that is isomorphic to the type of functions from itself to itself). The typed fragment, pushed to its logical extreme via recursive types with recursion in negative position, *becomes* the untyped fragment.

Wadler poses the obvious parallel question: **a foundation for concurrency based on linear logic is similarly limited in value if it only ever models race-free, deadlock-free processes.** Are there extensions of CP that recover more general forms of concurrency, the way recursive types recover untyped $\lambda$-calculus from the typed fragment?

He offers two, both due to prior authors, both expressible as small additions to CP's rule set.

### The Mix rule: composing without sharing

```
P ⊢ Γ    Q ⊢ Δ
--------------- Mix
 P | Q ⊢ Γ, Δ
```

Mix (Girard 1987) differs from ordinary Cut in exactly one respect: **zero** channels in common between $P$ and $Q$, rather than exactly one. It's logically equivalent to provability of $A \otimes B \multimap A \parr B$ for arbitrary $A$ and $B$ — a proposition that isn't provable in plain CP, since nothing in CP's rules lets you turn "output $A$ then $B$" into "input $A$ then $B$" without doing actual communication.

Crucially, **Mix does not reintroduce deadlock.** Composing two totally independent processes — neither one able to affect or block the other — can't create a cycle of waiting, because there's no channel between them for a cycle to run through. What Mix buys you is the ability to express genuinely independent concurrent structure, which plain Cut (always requiring exactly one shared channel) can't directly express. You actually met a disguised instance of this already, in [[Output-and-Input-via-the-Multiplicatives]]'s discussion of the multiplicative units: the primitive

$$\mathsf{par}_{y,z} \vdash y:1,\, z:1$$

(which sends an empty signal along both $y$ and $z$ in parallel) is *equivalent* to Mix. You can define general Mix in terms of this primitive:

$$P \mid Q \;\triangleq\; \nu z.(\nu y.(\mathsf{par}_{y,z} \mid y().P) \mid z().Q)$$

or conversely define the primitive in terms of Mix:

$$\mathsf{par}_{y,z} \;\triangleq\; y[\,].0 \mid z[\,].0$$

— two totally inert processes, sitting side by side, sharing nothing. (Caires, Pfenning, and Toninho (2012a) separately note that a less restrictive variant of the rules for $1$ and $\bot$ surprisingly derives something similar to Mix on its own.)

```rust
// Mix, concretely: composing two Rust computations that share
// *no* channel endpoints at all. Ordinary CP's Cut always forces
// exactly one shared endpoint — like requiring every `thread::spawn`
// to be paired with exactly one channel connecting it back. Mix lifts
// that requirement: you can just run two fully independent tasks
// side by side with nothing wiring them together.
fn mix<A, B>(p: impl FnOnce() -> A + Send, q: impl FnOnce() -> B + Send) -> (A, B)
where
    A: Send + 'static,
    B: Send + 'static,
{
    std::thread::scope(|s| {
        let ha = s.spawn(p);
        let hb = s.spawn(q);
        (ha.join().unwrap(), hb.join().unwrap())
    })
}
// No deadlock risk here for the same reason Mix is safe in CP:
// there is no channel between `p` and `q` for a wait-cycle to run through.
```

### Binary Cut: composing with two shared channels, and inviting deadlock back in

```
P ⊢ Γ, x:A, y:B     Q ⊢ Δ, x:A⊥, y:B⊥
--------------------------------------- BiCut
    νx:A,y:B.(P | Q) ⊢ Γ, Δ
```

Binary Cut (Abramsky, Gay, and Nagarajan 1996 — a special case of a more general *Multicut*) is the mirror image: **two** channels in common between $P$ and $Q$, rather than one. It's equivalent to provability of $A \parr B \multimap A \otimes B$ — notice this is the *converse* implication from Mix's, and, unlike Mix, this direction is *not* safe. Binary Cut is exactly what lets you build a system where communications between $P$ and $Q$ form a genuine **loop**: $P$ might need to receive on $x$ before it can send on $y$, while $Q$ needs to receive on $y$ before it can send on $x$ — a cycle of mutual waiting, i.e. deadlock, or, if the timing shifts, a race.

```rust
// Binary Cut, concretely: two computations sharing *two* channel
// endpoints, wired so each can wait on the other. This is precisely
// the shape that CP's ordinary Cut rule (Γ, Δ disjoint except for one
// shared name) structurally forbids — recall from
// "CP a Classical Linear Logic Process Calculus" that disjointness of
// the two sides' environments was exactly what ruled out this kind
// of two-channel entanglement.
use std::sync::mpsc;

fn binary_cut_deadlock() {
    let (tx1, rx1) = mpsc::channel::<()>();
    let (tx2, rx2) = mpsc::channel::<()>();

    let p = std::thread::spawn(move || {
        rx2.recv().unwrap(); // P waits on the SECOND shared channel...
        tx1.send(()).unwrap(); // ...before it can send on the first.
    });
    let q = std::thread::spawn(move || {
        rx1.recv().unwrap(); // Q waits on the FIRST shared channel...
        tx2.send(()).unwrap(); // ...before it can send on the second.
    });
    // Both threads are now waiting on each other. This is exactly the
    // communication loop Binary Cut makes expressible — and exactly
    // what CP's single-shared-channel Cut rule was designed to prevent.
    p.join().unwrap();
    q.join().unwrap();
}
```

### Compactness, and the same $X \simeq X \to X$ move all over again

Here's where the analogy from the top of this section pays off. A system with **both** Mix and Binary Cut is called *compact*: from either of $A \otimes B$ or $A \parr B$ you can derive the other (Mix gives you one direction, Binary Cut the other), so the two connectives collapse into being mutually inter-derivable. Abramsky, Gay, and Nagarajan (1996) show that such a compact linear system admits a translation of the **full, untyped $\pi$-calculus** into it — every process, deadlocking or racing ones included.

This is structurally *identical* to the $\lambda$-calculus story that opened the Conclusion: just as untyped $\lambda$-calculus embeds into typed $\lambda$-calculus via the recursive-type isomorphism $X \simeq X \to X$, the full untyped $\pi$-calculus embeds into CP-plus-Mix-plus-BinaryCut via the connective isomorphism $A \otimes B \simeq A \parr B$. In both cases, adding just enough extra structure to a disciplined, terminating/deadlock-free core recovers the full, undisciplined, Turing-complete/racy calculus you started by refining away from. Wadler leaves "searching for principled extensions of CP that support the unfettered power of the full $\pi$-calculus" as an explicit topic for future work — Mix and Binary Cut are existence proofs that it's *possible*, not a finished design.

## One More Open Direction: Multiparty Sessions

A final, briefer pointer: session types have grown substantially since Honda (1993) first introduced them, and the single most significant direction is **multiparty session types** (Honda, Yoshida, and Carbone 2008 and much subsequent work) — protocols among *more than two* participants, rather than the strictly two-endpoint channels CP and GV model throughout this vault. Whether the CP/GV logical foundation extends to multiparty protocols is left as an open question. If you ever find yourself wanting to model a protocol among three or more parties using the machinery from this vault, this is the honest answer: the paper doesn't cover it, and as of 2012, nobody had shown it worked.

## Where This Leads

Zooming back out across the whole vault: CP and GV are a small, complete, *honest* worked example of a specific move — **take a logic with a cut-elimination theorem, read propositions as a typing discipline, and get your safety proof for free as a corollary of that theorem, rather than having to invent and separately verify a bespoke safety argument.** [[Commuting-Conversions-and-Cut-Elimination]] is where that move actually happens (Theorem 2, top-level cut elimination, *is* the deadlock-freedom proof); every other article in this vault exists to build up either the logic ([[CP-a-Classical-Linear-Logic-Process-Calculus]] through [[Polymorphism-in-CP]]) or the more programmer-friendly surface language sitting on top of it ([[GV-a-Session-Typed-Functional-Language]], [[Translating-GV-into-CP]]).

This chapter's job was to show you the edges of that move: what it cost relative to a competing formulation (DILL's locality, lost by choosing CLL), and what happens when you deliberately relax the very constraint (Cut's exactly-one-shared-channel discipline) that made the safety proof work (Mix and Binary Cut). That's the most useful shape to carry forward into your own projects. Before you build a soundness proof for a Rust verifier or a bidirectional elaborator by hand — inventing a progress lemma, a preservation lemma, a termination argument from scratch — it's worth asking whether there's a logic underneath your type system whose *own* cut-elimination or normalization theorem would hand you that proof for free, the way it did here. And if you do relax a typing discipline for more expressiveness, this chapter is the reminder to ask, explicitly, which specific structural rule you loosened (a shared-environment constraint, an axiom restriction, an occurs-check) — because that's usually exactly where the safety guarantee you're giving up was hiding.
