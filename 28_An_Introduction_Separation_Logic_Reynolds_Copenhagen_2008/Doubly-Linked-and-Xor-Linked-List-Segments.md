---
title: "Doubly-Linked and Xor-Linked List Segments"
book: "An Introduction to Separation Logic (Reynolds, 2008)"
chapter: "Chapter 4, §4.8–4.9"
pages: "146–160"
tags: [separation-logic, hoare-logic, data-structures, frame-rule, procedures]
---

# Doubly-Linked and Xor-Linked List Segments

[[book-guidelines|↩ Back to guidelines]]

## Why this section exists: singly-linked segments aren't enough

Everything up to this point in Chapter 4 — `lseg`, `list`, the mergesort proof — was built on a single forward pointer per node. That's already a substructural triumph: the separating conjunction let `list α i` decompose recursively without any explicit non-aliasing side conditions. But a huge fraction of real data structures (deques, LRU caches, doubly-linked freelists, the kernel `list_head` pattern in Linux) need to walk *backward* as well as forward. The moment you add a second pointer field, you've doubled the bookkeeping a naive Hoare-logic invariant would need — except separation logic's whole point is that it shouldn't.

So this section is really a stress test for the machinery already built: can the same discipline (inductive segment predicates, the frame rule, procedures with a fixed modifies-clause) scale to two-linked structures without the proofs becoming twice as ugly? Reynolds's answer is yes, but with one genuinely new and important wrinkle: for the first time, two different procedures can satisfy the *exact same Hoare triple* and yet not be interchangeable in a larger proof, because the frame rule cares about which variables a command is allowed to touch, not just what it establishes.

The xor-linked variant pushes the same idea further: can you literally halve the storage for the two links by encoding "predecessor and successor" as a single value, using bitwise `xor`, and does the same predicate/procedure discipline survive? The section closes on a beautiful invariant of xor-linking: a doubly-linked list's *reversal* becomes a no-op on the heap.

## The `dlseg` predicate

### What breaks without a segment (not just a whole list) predicate

You could define a "doubly-linked list" (`dlist`) outright, the way `list α i` was defined for singly-linked lists. But insertion and deletion happen in the *middle* of a structure, and you need to reason about a contiguous chunk that isn't itself a self-contained list — it has dangling backward and forward pointers at its two ends that connect it to whatever is outside. That's exactly the motivation `lseg` already solved for the singly-linked case (§4.1); `dlseg` is the two-directional analogue.

### The definition

The book writes `dlseg α (i, i0, j, j0)` for: starting at address `i`, whose *backward* pointer is `i0`, there's a forward-linked chain of three-field records representing the sequence `α`, ending just before address `j`, whose *backward* pointer is `j0`. Pictorially, if `α = a₁, ..., aₙ`:

$$
i \xrightarrow{\ } a_1 \leftrightarrow a_2 \leftrightarrow \cdots \leftrightarrow a_n \xrightarrow{\ } j, \qquad \text{with } a_1\text{'s back-pointer} = i_0,\ \ n\text{'s successor-slot} = j_0
$$

Each record is now a **triple** `(value, forward, backward)`. Formally, by structural induction on `α`:

$$
\begin{aligned}
\mathrm{dlseg}_{\varepsilon}(i, i_0, j, j_0) &\stackrel{\mathrm{def}}{=} \mathrm{emp} \wedge i = j \wedge i_0 = j_0 \\
\mathrm{dlseg}_{a\cdot\alpha}(i, i_0, k, k_0) &\stackrel{\mathrm{def}}{=} \exists j.\ i \mapsto a, j, i_0 \;*\; \mathrm{dlseg}_\alpha(j, i, k, k_0)
\end{aligned}
$$

Read the recursive case carefully: the head record at `i` stores `a` (the value), `j` (its forward pointer, the *next* node), and `i₀` (its backward pointer, exactly the parameter that was passed in — this is the segment's own external predecessor). Then the *recursive call*'s backward parameter becomes `i`, not `i₀` — because from the second node onward, the backward pointer of each record is genuinely the previous node in the chain. This is the crux of getting a two-directional inductive definition right: **the forward recursion silently carries the "correct" backward-pointer value forward as an extra argument**, the same trick a functional accumulator pattern uses to thread state through a fold.

If you've built recursive-descent parsers or written a `fold`-with-extra-context in Rust, this should feel familiar:

```rust
// The shape of dlseg's induction, made concrete: walking forward while
// threading the *correct* predecessor pointer as an explicit parameter,
// exactly the way `i0` becomes `i` on the next call.
#[derive(Debug)]
struct Node {
    value: i64,
    next: Option<usize>,
    prev: Option<usize>,
}

// Checks the doubly-linked invariant along one segment [i, j), given the
// expected trailing back-pointer i0 for the *first* node — dlseg's ghost ledger.
fn check_dlseg(heap: &[Node], i: Option<usize>, i0: Option<usize>, j: Option<usize>) -> bool {
    match i {
        None => i == j, // dlseg_ε: emp ∧ i = j (i0 = j0 checked by the caller)
        Some(idx) if i == j => true, // reached the segment's own boundary
        Some(idx) => {
            let node = &heap[idx];
            node.prev == i0 && check_dlseg(heap, node.next, Some(idx), j)
            //                                              ^^^^^^^^^ the i0 → i thread
        }
    }
}
```

Notice this Rust check is *exactly* the kind of thing `dlseg` licenses you to prove holds — but separation logic's version additionally guarantees, via `*`, that the records in `[i, j)` are *disjoint* from whatever else the surrounding assertion talks about. That disjointness is not something the Rust code above enforces or even expresses; it's free in the logic and would need a borrow-checker-level argument (or an explicit ghost "ownership" proof) to recover in Rust.

### Composition and emptiness — both directions

Since a doubly-linked segment has two ends, you get **two independent notions of emptiness**, one from the forward direction and one from the backward:

$$
\begin{aligned}
\mathrm{dlseg}_\alpha(i,i_0,j,j_0) &\Rightarrow (i = \mathrm{nil} \Rightarrow (\alpha = \varepsilon \wedge j = \mathrm{nil} \wedge i_0 = j_0)) \\
\mathrm{dlseg}_\alpha(i,i_0,j,j_0) &\Rightarrow (j_0 = \mathrm{nil} \Rightarrow (\alpha = \varepsilon \wedge i_0 = \mathrm{nil} \wedge i = j))
\end{aligned}
$$

This is the two-directional generalization of `lseg`'s single emptiness law (`lseg`'s segment is empty exactly when `i = j`); here you can detect emptiness by *either* endpoint going `nil`, which matters because insertion/deletion programs often only have direct evidence about one side.

Composition mirrors `lseg`'s composition law, but every join now needs *two* boundary addresses instead of one:

$$
\mathrm{dlseg}_{\alpha\cdot\beta}(i,i_0,k,k_0) \Leftrightarrow \exists j, j_0.\ \mathrm{dlseg}_\alpha(i,i_0,j,j_0) * \mathrm{dlseg}_\beta(j,j_0,k,k_0)
$$

A whole doubly-linked *list* (as opposed to a segment) is then just the special case with both ends `nil`:

$$
\mathrm{dlist}_\alpha(i, j_0) \stackrel{\mathrm{def}}{=} \mathrm{dlseg}_\alpha(i, \mathrm{nil}, \mathrm{nil}, j_0)
$$

Reynolds flags something structurally important here: **you cannot define `dlist` directly by structural induction**, because no proper sub-structure of a doubly-linked list is itself a doubly-linked list (chop off the head, and the new head's back-pointer is no longer `nil`). `dlseg` is the load-bearing inductive object; `dlist` is a derived, non-recursive specialization of it. This is a lesson worth internalizing generally: when a "whole" structure resists direct induction, look for the segment/fragment generalization that *does* admit induction, and define the whole as its degenerate case. (The same pattern will reappear, in a much more consequential form, for the Schorr-Waite spine invariant and for `array`'s relationship to arbitrary sub-ranges.)

## The key episode: `lookuprpt` vs. `setrpt`, or why "same Hoare triple" isn't "interchangeable"

This is the section's real payload, and it's a direct, hands-on illustration of *why the frame rule's side condition about modified variables is not bureaucratic overhead — it's doing essential proof work.*

Two tiny nonrecursive procedures examine/change the far end of a left-anchored segment `dlseg α (i, nil, j0, j0)` (a segment starting at `i` with `nil` backward pointer, ending at `j0`):

```
lookuprpt(j; i, j0){α, j0} =
  {dlseg α (i, nil, j0, j0)}
  if j0 = nil then j := i
  else j := [j0 + 1]
  {dlseg α (i, nil, j0, j0) ∧ j = j0}

setrpt(i; j, j0){α, j0} =
  {dlseg α (i, nil, j0, j0)}
  if j0 = nil then i := j
  else [j0 + 1] := j
  {dlseg α (i, nil, j, j0)}
```

Read the parameter lists precisely — this is the book's own notation for a procedure's *modifies-clause*: everything left of the semicolon is a variable the call is permitted to assign to; everything to the right (up to the `{...}`) is read-only; the braced list is ghost/ specification-only parameters. `lookuprpt(j; i, j0)` may modify only `j`. `setrpt(i; j, j0)` may modify only `i`.

Now here's the trap: **the postcondition of `lookuprpt` implies the postcondition of `setrpt`** (`α (i, nil, j0, j0) ∧ j = j0` implies `dlseg α (i, nil, j, j0)`, just by substituting `j0` for `j`). Since both procedures share the same precondition, weakening the consequent shows:

$$
\{\mathrm{dlseg}_\alpha(i,\mathrm{nil},j_0,j_0)\}\ \mathrm{lookuprpt}(j; i, j_0)\{\alpha, j_0\}\ \{\mathrm{dlseg}_\alpha(i,\mathrm{nil},j,j_0)\}
$$

— i.e. **`lookuprpt` satisfies the exact Hoare triple that `setrpt` was specified to satisfy.** As pure input/output behavior on this triple, they're interchangeable. And yet, in the larger insertion program (below), swapping one for the other breaks the proof. Why? Because the insertion program applies the **frame rule** to add a disjoint conjunct — a second `dlseg` segment sitting in memory next to the one being manipulated — and the frame rule's soundness depends on the command *not modifying any variable free in the framed-off part*. `lookuprpt(l; i, j)` modifies `l`; if `l` happens to occur free in the frame (which, in the actual insertion program, it does, since `l` is exactly the variable the surrounding proof is threading through the second segment), the frame rule's side condition is violated and the whole compositional argument collapses — even though the *specification* of the command, taken in isolation, was never violated.

This is a precise, worked counterexample to a tempting but wrong intuition: **"same Hoare triple" is not "safe to substitute inside a larger proof."** Substitutability under the frame rule additionally requires agreement on the *footprint of variables*, not just the footprint of heap cells. This is exactly the kind of "local correctness in isolation doesn't imply compositional correctness" failure mode that shows up constantly in effect systems and borrow-checking: two functions with identical types can still not be swappable if one of them captures/mutates something the type doesn't mention (a `&mut` alias, an ambient global, a hidden `Cell`).

```rust
// A Rust echo of the lesson: these two closures have the same *signature*
// (same "Hoare triple" for their return value), but they differ in what
// they capture and mutate — which is exactly what a frame-rule-style
// compositional argument needs to check before it can treat them as
// interchangeable inside a larger expression.
fn lookuprpt_like(i: i64, j0: i64) -> i64 {
    // "reads" i, j0; assigns to nothing external — analogous to modifying only `j`
    if j0 == 0 { i } else { j0 /* stand-in for [j0+1] */ }
}

fn setrpt_like(i: &mut i64, j: i64, j0: i64) {
    // mutates `i` in place — analogous to modifying only `i`
    if j0 == 0 { *i = j; }
    // else: writes through j0's slot, external to `i`
}
```
If some surrounding code holds a live borrow on the variable that plays the role of `l` (the modified variable) while calling one of these, the borrow checker would reject exactly the substitution that breaks Reynolds's proof — Rust's aliasing discipline and separation logic's frame rule are, at this level, checking the same invariant from two different formal angles.

`lookuplpt`/`setlpt` are the mirror-image procedures for the *left* end of a right-anchored segment, defined and used completely symmetrically — Reynolds doesn't re-derive the argument, having made the point once.

## Deletion and insertion: putting `dlseg` and the frame rule to work

The deletion program (an element at address `k`, with neighbors `j` and `l` discovered by lookups) is worked out in full annotation. Its shape is worth internalizing because it's the generic pattern for "modify the middle of a two-ended structure":

1. **Look up** the two neighbor addresses (`l := [k+1]; j := [k+2]`) — this converts implicit existentially-quantified logical variables into concrete program variables you can case on.
2. **Deallocate** the target record's three fields.
3. **Case-split on whether either neighbor is `nil`** (i.e., whether the deletion is at a boundary) — this is exactly the "either direction of linkage" emptiness condition from `dlseg`'s axioms doing real work, not just decoration.
4. In the "interior" case, use `dlseg`'s composition law (implicitly, via the frame rule) to isolate just the one record whose pointer needs patching, patch it, and let the frame rule re-assemble the full picture.

The insertion program is even more instructive because it explicitly uses `lookuprpt`, `setrpt`, `setlpt` as callable procedures, and its annotated proof is where the frame-rule/GCALL argument for `lookuprpt` vs. `setrpt` (above) actually gets deployed. The final specification achieved is:

$$
\{\exists j,l.\ \mathrm{dlseg}_\alpha(i,\mathrm{nil},k,j) * k \mapsto b,l,j * \mathrm{dlseg}_\beta(l,k,\mathrm{nil},m)\}\ \cdots\ \{\mathrm{dlseg}_{\alpha\cdot\beta}(i,\mathrm{nil},\mathrm{nil},m)\}
$$

— exactly the composition law for `dlseg`, established not as an axiom but as the *output* of running the program. This is the same "local reasoning gives you the composition law for free" phenomenon you saw with `lseg` and the frame rule in earlier chapters, now surviving the jump to two linkage directions.

## Xor-linked segments: halving the storage, keeping the discipline

### The idea, first principles

A doubly-linked node stores *two* pointer-sized fields for structural bookkeeping (forward and backward), on top of its payload. Xor-linking is a classic space-optimization: since `x ⊕ y ⊕ y = x`, if a node stores the single value `next ⊕ prev` instead of both fields separately, then a **traversal that already knows the address it came from** can recover the other neighbor by XOR-ing the stored value against the address it came from:

$$
\text{stored} \oplus \text{came-from} = (\text{next} \oplus \text{prev}) \oplus \text{prev} = \text{next}
$$

The catch (mirrored faithfully in the predicate below) is that you can never reconstruct *both* neighbors from the node alone — you always need the address of the neighbor you just visited as external context. This is why the recursive definition passes exactly that context along, precisely paralleling `dlseg`'s `i0`-threading trick:

$$
\begin{aligned}
\mathrm{xlseg}_{\varepsilon}(i,i_0,j,j_0) &\stackrel{\mathrm{def}}{=} \mathrm{emp} \wedge i = j \wedge i_0 = j_0 \\
\mathrm{xlseg}_{a\cdot\alpha}(i,i_0,k,k_0) &\stackrel{\mathrm{def}}{=} \exists j.\ i \mapsto a, (j \oplus i_0) * \mathrm{xlseg}_\alpha(j, i, k, k_0)
\end{aligned}
$$

Compare directly against `dlseg`: the only change is that the two pointer fields `j, i0` collapse into the single stored value `j ⊕ i0` — the predicate's *shape* (same recursive skeleton, same two boundary parameters, same threading of `i` into the next call's backward slot) is completely unchanged. This is a good illustration of how separation logic's inductive predicates are robust to changing the *representation* of a link while preserving the *abstract shape* of the data — a distinction any compiler engineer will recognize as the difference between an abstract data type's interface and its concrete layout.

```python
# A tiny illustrative sketch (not load-bearing, just for intuition):
# walking an xor-linked list forward, given only the head and a "prev = None" seed.
def xor_walk(heap, i, i0):
    result = []
    while i is not None:
        stored = heap[i].link  # link = next ^ prev, as addresses (use 0 for "nil")
        nxt = stored ^ (i0 or 0)
        result.append(heap[i].value)
        i, i0 = nxt if nxt != 0 else None, i
    return result
```

All the same laws carry over almost verbatim, with `⊕` replacing the pair `(forward, backward)`:

$$
\mathrm{xlseg}_{\alpha\cdot\beta}(i,i_0,k,k_0) \Leftrightarrow \exists j,j_0.\ \mathrm{xlseg}_\alpha(i,i_0,j,j_0) * \mathrm{xlseg}_\beta(j,j_0,k,k_0)
$$

and the emptiness conditions are *word-for-word identical in form* to `dlseg`'s.

### `xsetrpt`, and a genuinely new complication

The analogue of `setrpt` for xor-linked segments, `xsetrpt`, has to *read the old combined value before it can overwrite it*, because — unlike `dlseg`, where the forward and backward pointers live in separate fields you can overwrite independently — here overwriting the link means computing a *new* xor-combination that must undo the old neighbor's contribution and splice in the new one:

```
xsetrpt(i; j, j0, k){α} =
  ...
  newvar x in
    (x := [j0 + 1];              -- x = j ⊕ k0 (the old combined link)
     [j0 + 1] := x ⊕ j ⊕ k)      -- new link = old ⊕ (undo old j) ⊕ (splice in new k)
```

This little `read, then write x ⊕ j ⊕ k` idiom is the entire "cost" of the space optimization: you trade one pointer field for one extra memory read per mutation. It's the same trade-off that motivates real xor-linked-list implementations (and, more broadly, any "packed" or "compressed" representation) — you always pay for the compression either in reconstruction cost (reads) or in write complexity (recompute-on-write), never for free.

### The payoff: reversal becomes free

The section ends with the single most striking fact about xor-linking, proved by structural induction on `α`:

$$
\mathrm{xlseg}_\alpha(i, i_0, j, j_0) \Leftrightarrow \mathrm{xlseg}_{\alpha^\dagger}(j_0, j, i_0, i)
$$

(where `α†` is the reflection/reverse of the sequence `α`). Because the stored value at each node is `next ⊕ prev`, and xor is commutative, *the exact same stored bits* simultaneously witness the list read forward and the list read backward — reversing "which end you call the head" costs **zero heap writes**. This is a genuinely elegant payoff of the representation, and a nice concrete instance of a recurring theme in this book: sometimes the right representation makes an entire class of operations (here, reversal) not just efficient but literally free, purely as a consequence of how a predicate is defined.

## Where this leads

- The `lookuprpt`/`setrpt` interchangeability trap is this book's cleanest illustration that **the frame rule's soundness is about variable footprints, not just heap footprints** — a fact that becomes essential again in Chapter 6's iterated-conjunction proofs ([[Case-Studies-in-Program-Verification#Partition|Partition]], Quicksort) where many small procedure calls are chained together via the frame rule under tight modifies-clauses.
- The "define the segment, derive the whole structure as its degenerate case" pattern (here, `dlist` from `dlseg`) is the same move Chapter 1's Schorr-Waite proof and Chapter 6's array/cyclic-buffer predicates make; recognizing it early makes those later, harder constructions feel like variations rather than new tricks.
- For a Rust-based verifier: the `lookuprpt`/`setrpt` distinction is a direct argument for why a checker's specification language needs an explicit, checked *modifies/footprint clause* on procedures — not just pre/postconditions — if it wants frame-rule-style compositional reasoning (the exact mechanism a Viper- or Prusti-style separation-logic-based Rust verifier relies on, and the same discipline your own toolchain's procedure-call rule (Chapter 4's `GCALL`) would need to check before letting a caller apply the frame rule around a call).
