---
title: Future Directions in Automata-Based Programming
source: Programming using Automata and Transducers (D'Antoni, PhD thesis 2015)
chapter: "Chapter 6: Future work (pp. 185–189)"
tags: [automata, transducers, open-problems, data-parallelism, static-analysis]
---

[[book-guidelines|↩ Back to guidelines]]

# Future Directions in Automata-Based Programming

## Reading a "future work" chapter as a map of unresolved trade-offs

A concluding chapter is easy to skim past, but this one is worth reading carefully for a specific reason: **every direction it names is a genuine, still-open instance of the thesis's own central tension** — expressiveness versus closure/decidability versus efficient executability — applied to a domain or algorithmic question the dissertation didn't have room to close. Read this way, Chapter 6 isn't a grab-bag of ideas; it's the thesis pointing at exactly the seams where its own restriction-and-recover methodology (Cartesian guards, regular look-ahead, call/return-only binary predicates, single-use restriction) hasn't yet been tried, or has been tried but not yet made tight.

## Declarative languages: separating syntax from semantics

BEX and FAST (Chapters 2–3) are **near-isomorphic frontends** — a BEX rule's syntax translates almost mechanically into an S-EFT transition; a FAST `trans` block into an S-TTR rule. This is a deliberate simplicity, but it caps how *programmable* the language can be: the user is essentially writing the automaton directly, just with nicer syntax.

**What breaks without a declarative layer.** Regular expressions are the classical counterexample worth having in mind: nobody writes a DFA directly when a regex compiles to one, because the declarative layer (concatenation, union, Kleene star as combinators) is dramatically more succinct and closer to how a human thinks about the property, while the compilation to an executable automaton is a solved, hidden step. BEX and FAST, by contrast, ask the programmer to think in terms of states and transitions from the start.

The thesis reports concrete follow-on progress here, not just a wish: Alur, Freilich, and Raghothaman identified a **combinator set that captures exactly the class of regular string-to-string transformations**, and — in joint work with Alur and Raghothaman — the author built **DReX**, a declarative language built on those combinators, compiled into (Chapter 2-style) transducers, and statically analyzable and efficiently executable exactly like BEX. The open direction this leaves for tree/hierarchical models: no analogous declarative combinator characterization yet exists for S-TTR- or STT-definable transformations, or for S-VPA-definable properties — extending DReX's approach to those richer models is exactly the kind of "close the same gap one level up" project this thesis's methodology invites.

## Algorithms: tightening bounds the thesis leaves open

Two specific gaps, named explicitly:

- **Minimizing symbolic automata** was already advanced by the author's own prior joint work with Veanes — cited as a genuinely solved sub-problem, in contrast to what follows.
- **Streaming (tree and string) transducer equivalence has only an upper bound, no matching lower bound.** Chapter 5's Theorem 5.28 establishes NEXPTIME as the first *elementary* upper bound for STT functional equivalence — a major result relative to prior non-elementary bounds — but the thesis is explicit that no complexity-theoretic lower bound rules out equivalence being solvable much faster. **This is a genuinely different kind of open problem than "we don't have an algorithm" — an algorithm exists; what's missing is proof that a *better* one couldn't exist.** Closing this gap (either finding a faster algorithm, or proving NEXPTIME-hardness) is flagged as an active research direction the thesis explicitly did not resolve.

## New models: counters and infinite domains

Two natural axes the thesis's models don't cover:

- **Infinite strings and trees** (as opposed to finite ones) — none of S-EFTs, S-TTRs, S-VPAs, or STTs are defined over $\omega$-words or infinite trees, which matter for reasoning about non-terminating reactive systems.
- **Counters** — none of the thesis's models can count and compare counts (e.g., "the number of `a`'s equals the number of `b`'s" is a classic example *outside* regular languages, requiring a counter or a stack used non-visibly). The thesis notes joint work (with Alur, Deshmukh, Raghothaman, and Yuan) on **numerical extensions of streaming transducers** — call this out specifically because it's the most direct bridge to the `sat-smt-csp` focus area's interest in integer/non-linear constraint domains: a transducer model extended with counters is immediately adjacent to constraint automata used as abstract domains for arithmetic reasoning.

**What breaks without counters, concretely**: any property phrased as "these two quantities stay equal/related throughout execution" — a very common shape for a loop invariant — is invisible to every model in this thesis unless it happens to be expressible via the specific mechanisms already available (an S-VPA's call/return binary predicate captures *pairwise* relations at matching positions, but not a running arithmetic accumulation across arbitrarily many positions).

## Data-parallelism: a structural insight with a name

This section describes the single most concrete, implementation-oriented idea in the chapter, joint work with Veanes, Mytkowicz, Molnar, and Livshits: **a transducer's transition relation can be represented as a matrix, and running the transducer on an input becomes matrix multiplication.** The genuinely surprising consequence: in this representation, **the explicit state component disappears** — state transitions are absorbed into the matrix structure itself, rather than tracked as a separate discrete value.

**Why this matters for parallelism specifically.** A matrix-multiplication formulation is *associative* — $(AB)C = A(BC)$ — which means the input can be **split into arbitrary chunks, each chunk's corresponding sub-matrix computed independently and in parallel, and the results merged** via ordinary matrix multiplication, regardless of chunk boundaries. This is exactly the property a naive state-machine simulation *lacks*: normally you can't start processing chunk $k$ until you know what state chunk $k{-}1$ left you in, which serializes the whole computation. Representing the transition relation as a matrix sidesteps this by computing, for *every possible* starting state simultaneously (that's what the matrix encodes), letting the merge step pick out the actually-relevant path after the fact.

```rust
// The key move: instead of "run the transducer starting from state q,"
// compute the ENTIRE transition matrix for a chunk — what would happen
// starting from every possible state — so that composing chunk results
// doesn't require knowing which state you actually arrived at until the
// final merge. This is what makes chunk processing embarrassingly parallel.
struct TransitionMatrix<State> {
    // matrix[from][to] = the (possibly-guarded, possibly-outputting)
    // transformation applied when starting in `from` and ending in `to`
    entries: Vec<Vec<TransducerStep<State>>>,
}
// Chunks can be matrix-multiplied independently, then merged:
// result = chunk1_matrix * chunk2_matrix * chunk3_matrix * ...
```

The thesis flags XML processing specifically as a promising target for data-parallel models built this way — a natural next step, since Chapter 4's S-VPAs already process XML-shaped nested words, but as a strictly single-pass, sequential computation.

## New applications: five concrete, unfinished extensions

The chapter closes with five [[Symbolic-Visibly-Pushdown-Automata-for-Hierarchical-Data#Applications|applications]], each explicitly framed as *in-progress or aspirational*, not completed thesis contributions — worth reading as a direct list of "here is where this methodology should go next":

1. **DMA verification in device drivers** (joint work with Albarghouthi, Cerny, and Ryzhyk, in progress at time of writing) — direct memory access makes the *entire memory* part of a driver's reachable state space, defeating explicit-state techniques. The stated research problem is precisely the thesis's recurring one: extend the transducer models to handle counters and data values (needed to model DMA packet queues) **without losing decidability** — i.e., find the DMA-specific analogue of the Cartesian/regular-look-ahead/call-return restrictions that made every earlier chapter's extension tractable.

2. **Networking, via NetKAT** — a contemporaneous language (Anderson et al.) modeling networks as automata with Kleene Algebra with Tests (KAT) for actions, itself automata-theoretically founded but restricted to *finite* alphabets, requiring explicit per-packet-field disjoint predicate enumeration. The thesis's proposed contribution: apply symbolic-automata succinctness techniques to let NetKAT represent packet predicates directly, rather than exploding them into finite-alphabet disjunctions — cleanly separating "querying a packet's fields" from "reasoning about network topology," the same separation-of-concerns pattern seen in Chapter 4's XML validation (tree shape in states, leaf content in predicates).

3. **Deep packet inspection**, revisited as a forward-looking direction beyond §2.7.2's demonstration (see [[Program-Analysis-Applications-of-Transducer-Based-Languages]]): combining symbolic automata with **BDDs (Binary Decision Diagrams)** specifically to exploit the bit-vector structure packets already have — a concrete algorithmic-engineering proposal, not just "apply the existing model," since packet headers/payloads are natively bit-vector-shaped in a way BDDs are already specialized to represent efficiently.

4. **Binary assemblers and disassemblers** — proposed as a direct adaptation of Chapter 2's string-coder verification machinery (an assembler/disassembler pair is structurally an encoder/decoder pair, exactly BEX's target shape) to bit-pattern-heavy binary formats, with a further speculative connection to **deobfuscation** (recovering readable code from obfuscated binaries) as a byproduct of modeling the disassembly transformation explicitly enough to reason about.

5. **Binary code similarity analysis** (malware fingerprinting) — citing contemporaneous work (Dalla Preda, Giacobazzi, Lakhotia, Mastroieni) treating **symbolic automata as an abstract-interpretation domain**: represent programs as automata, then apply *abstraction operations* (in the abstract-interpretation sense — losing precision deliberately) iteratively to make structurally-different-but-semantically-similar programs' automata converge toward each other, exposing shared malicious code despite compiler-introduced structural noise. The thesis's own proposed extension: use **S-VPAs specifically** to lift this technique from straight-line/non-recursive code to **recursive programs** — a direct, named application of Chapter 4's hierarchical model to a problem area (malware analysis) the rest of the thesis never otherwise touches.

## Where this leads

```mermaid
mindmap
  root((Thesis methodology:<br/>restrict to recover<br/>closure + decidability))
    Declarative front-ends
      DReX for strings — done
      Tree/hierarchical analogue — open
    Sharper bounds
      STT equivalence upper bound found
      Matching lower bound — open
    New models
      Infinite strings/trees — open
      Counters — open, bridges to sat-smt-csp
    Data-parallelism
      Matrix representation eliminates state
      Chunked, parallel execution
    New domains
      DMA verification
      NetKAT / networking
      DPI + BDDs
      Binary (dis)assembly
      Malware similarity via abstract interpretation
```

Every branch here is the same question asked of a new setting: *what is the minimal structural restriction that recovers decidability and closure without giving up the expressiveness this specific application actually needs?* That is the thesis's one real methodological export, and this chapter is the clearest evidence that the author saw it that way too — not as five unrelated add-ons, but as five instances of one repeatable question.

For the `sat-smt-csp` and `static-analysis` focus areas specifically: the **counters/numerical-extensions** direction and the **binary-similarity-as-abstract-interpretation** direction are the two threads here most directly relevant to a refinement-type compiler's CSP kernel and abstract-interpretation passes. A counter-extended symbolic transducer is a plausible model for the kind of automata/grammar-shaped abstract domain your project's specification calls for (representing complex data structures as DFA-like domains); and treating automata themselves as an abstract-interpretation domain — with explicit abstraction/refinement operations over the automaton's structure — is a genuinely different, and underused, way to think about invariant generation compared to the more familiar numeric-lattice abstract domains, worth keeping in mind as an alternative representation when the invariant you're trying to infer is fundamentally about *shape* (a data structure's grammar) rather than about numeric ranges.
