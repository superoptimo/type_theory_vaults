---
title: "Hoare Triples and Specifications"
book: "An Introduction to Separation Logic (Reynolds, 2008)"
chapter: "Chapter 3, §3.1 (pp. 57–58), with Chapter 1, §1.3 and §1.5 (pp. 8–20)"
tags: [separation-logic, hoare-triples, memory-safety, partial-correctness, total-correctness]
---

[[book-guidelines|↩ Back to guidelines]]

## From assertions about states to specifications about commands

[[The-Separation-Logic-Assertion-Language|Assertions]] describe *states* — a store and a heap at one instant. But the object you actually want to verify is a *command*: does running `x := cons(1,2); y := [x]` do what you claim it does? That requires a second layer of notation sitting on top of assertions — a **specification** relating a *before* state and an *after* state via the command that connects them. This is the Hoare triple, and this article covers three things the notes deliberately keep close together even though they're spread across two chapters: (1) the programming language's heap-manipulating commands and their memory-fault semantics (§1.3), (2) the overview of Hoare triples and why "well-specified programs don't go wrong" is the central design decision of the whole logic (§1.5), and (3) the compact formal definition of partial and total correctness triples (§3.1).

## The heap-manipulating commands and memory faults

Reynolds extends Hoare's simple imperative language with four new commands, none of which is an ordinary assignment even though three of them are written with `:=`:

```
⟨comm⟩ ::= ···
   | ⟨var⟩ := cons(⟨exp⟩, …, ⟨exp⟩)   allocation
   | ⟨var⟩ := [⟨exp⟩]                  lookup
   | [⟨exp⟩] := ⟨exp⟩                  mutation
   | dispose ⟨exp⟩                     deallocation
```

The state model splits into a **store** (variables → values, exactly as in ordinary Hoare logic) and a **heap** (a *finite partial* map from addresses to values — addresses and non-address integers coexist in one flat `Values = Integers` domain, so that unrestricted address arithmetic is legal). Memory management is fully explicit — there is no garbage collector — and every heap-manipulating command can fault:

```
Store: x:3, y:4          Store: x:37, y:4         Store: x:37, y:1        Store: x:37, y:1
Heap:  empty     alloc   Heap: 37:1,38:2   lookup  Heap: 37:1,38:2  mut.   Heap: 37:1,38:3
  x:=cons(1,2) ⇒                y:=[x]    ⇒               [x+1]:=3 ⇒
```

...and dereferencing or deallocating an *inactive* address transitions to the special terminal configuration $\mathrm{abort}$, rather than continuing or raising a catchable exception. Two subtleties matter enormously for everything that follows:

1. **Expressions never touch the heap.** `cons`, `[e]` are part of *command* syntax, never expression syntax, so they can't be nested (you can't write `[x] + [y]` as an expression) and expressions remain side-effect-free, exactly as in classical Hoare logic. This is precisely what licenses using expressions freely inside assertions with the same algebraic freedom as ordinary mathematics.
2. **Allocation addresses are indeterminate.** `cons(e1,...,en)` activates $n$ *consecutive*, *previously-inactive* cells — but which consecutive run of addresses gets chosen is left completely unspecified. This single design choice turns out to be the mechanism that (together with fault-sensitivity, below) forces programs to respect record boundaries without the logic ever needing an explicit non-aliasing side condition.

### Grounding: this is exactly `malloc`/`free` semantics, minus garbage collection

```rust
// The book's cons/[e]/[e]:=/dispose map almost directly onto a raw,
// unsafe allocator interface — and Rust's own memory model is built
// entirely around ruling out exactly the fault this section describes.
unsafe fn model_of_book_commands() {
    let ptr = alloc(Layout::new::<[i64; 2]>()) as *mut i64; // cons(1, 2)
    *ptr = 1; *ptr.add(1) = 2;
    let y = *ptr;                 // y := [x]  (lookup)
    *ptr.add(1) = 3;              // [x+1] := 3  (mutation)
    dealloc(ptr as *mut u8, Layout::new::<[i64; 2]>()); // dispose x
    let _ = *ptr;                 // use-after-free — exactly Reynolds's `abort`,
                                   // except Rust's type system, not a program logic,
                                   // is what's supposed to make this unreachable.
}
```

Reynolds's `abort` is the semantic ground truth that a Rust-style *ownership type system* is trying to make statically unreachable, and that a separation-logic-based verifier (Verus, Prusti, Viper) is trying to make provably unreachable via Hoare triples instead of via a type system baked into the compiler. Both approaches are attacking the exact same fault; separation logic's contribution is doing it with assertions general enough to describe *arbitrary* heap shapes, not just the specific ownership discipline a fixed type system enforces.

## Hoare triples: two flavors

A specification is one of two forms, both surrounding a command with a precondition and postcondition assertion:

```
⟨specification⟩ ::=
     {⟨assertion⟩} ⟨command⟩ {⟨assertion⟩}    (partial correctness)
   | [⟨assertion⟩] ⟨command⟩ [⟨assertion⟩]    (total correctness)
```

**Partial correctness**, $\{p\}\ c\ \{q\}$, is valid iff: starting from any state satisfying $p$, no execution of $c$ aborts, *and* every execution of $c$ that *does* terminate ends in a state satisfying $q$. It says nothing about executions that loop forever.

**Total correctness**, $[p]\ c\ [q]$, adds the extra demand that *every* execution of $c$ (from a $p$-state) terminates. Both forms are — Reynolds is explicit about this — implicitly universally quantified over *every* initial state satisfying $p$ and *every* possible execution from it (not just one), because allocation's indeterminacy means a single command can genuinely have multiple distinct executions from the same starting state, differing in which concrete addresses got allocated. A specification's truth value doesn't depend on any particular state — it's simply true or false, exactly like a validity claim about a single assertion.

Some worked examples make the ordinary-Hoare-logic-plus-heap flavor concrete:

$$\{x - y > 3\}\ x := x - y\ \{x > 3\} \qquad \{\mathrm{emp}\}\ x := \mathrm{cons}(1,2)\ \{x \mapsto 1, 2\}$$
$$\{x \mapsto 1, 2\}\ y := [x]\ \{x \mapsto 1, 2 \wedge y = 1\} \qquad \{x \mapsto 1, 3 \wedge y=1\}\ \mathrm{dispose}\ x\ \{x{+}1 \mapsto 3 \wedge y = 1\}$$

— note the last one: after `dispose x`, the heap no longer contains cell $x$, but it still contains $x{+}1$, and the assertion reflects exactly that (not `emp`!). And a case where partial and total correctness genuinely diverge:

$$\{x \le 10\}\ \mathrm{while}\ x \neq 10\ \mathrm{do}\ x := x{+}1\ \{x = 10\} \qquad(\text{also valid as total})$$
$$\{\mathrm{true}\}\ \mathrm{while}\ x \neq 10\ \mathrm{do}\ x := x{+}1\ \{x = 10\} \qquad (*)\ (\text{partial-only: } x > 10 \text{ loops forever})$$

## "Well-specified programs don't go wrong" — the central design decision

Here is the sentence that, more than any single piece of notation, explains why separation logic's Hoare triples are shaped the way they are: **any execution that faults falsifies the specification, in both flavors.** As O'Hearn paraphrased Milner, *well-specified programs don't go wrong*. The practical consequence is enormous: once a program is proved to satisfy a specification (and is only ever run from states meeting the precondition), **no runtime memory-fault checking is required at all** — not even activity bits on heap cells. Detecting faults is explicitly *not* the implementor's job; avoiding them is the *programmer's* job, and separation logic is the tool for discharging that responsibility statically, before the program ever runs.

This single design decision, combined with allocation's indeterminacy, is what makes record-boundary violations provably unreachable without ever writing an explicit non-aliasing side condition. Consider:

$$c_0;\ x := \mathrm{cons}(1,2);\ c_1;\ [x{+}2] := 7$$

No matter what $c_0$ or $c_1$ do, nothing guarantees that the address $x{+}2$ was ever allocated by *this* `cons` call (it allocates only 2 cells, at $x$ and $x{+}1$) — and since allocation addresses are indeterminate, there is no way to *rule out* the possibility that `x+2` lands on an inactive address on some execution. Consequently there is **no valid postcondition whatsoever** for $\{\mathrm{true}\}\ c_0;\ x:=\mathrm{cons}(1,2);\ c_1;\ [x{+}2]:=7\ \{?\}$ — the specification is simply invalid for any $q$, because *some* execution aborts. The logic doesn't need to say "$x{+}2$ might alias something else's cell" — the mere possibility of an out-of-bounds write, amplified by indeterminate allocation ranging over infinitely many address choices, is already enough to kill every specification. This is the mechanism by which "well-specified programs don't go wrong" quietly enforces record-boundary discipline for free.

At the same time, the notion of a fixed record boundary can dissolve when a program is genuinely careful, as in the record-gluing example (used again, with its complete annotated proof, in Chapter 3's own worked illustration):

$$\{x \mapsto - * y \mapsto -\}$$
$$\ \mathrm{if}\ y = x{+}1\ \mathrm{then}\ \mathrm{skip}\ \mathrm{else}$$
$$\quad\ \mathrm{if}\ x = y{+}1\ \mathrm{then}\ x := y\ \mathrm{else}$$
$$\qquad(\mathrm{dispose}\ x;\ \mathrm{dispose}\ y;\ x := \mathrm{cons}(1,2))$$
$$\{x \mapsto -, -\}$$

— a program that, depending on runtime layout, either discovers the two records are *already* adjacent, or tears both down and reallocates a fresh adjacent pair. This is explicitly noted as going beyond what a fixed-record-boundary type system for mutable data could express — the specification is uniform even though the *mechanism* that achieves it differs by execution path.

## Which classical rules survive, and which one doesn't

Beyond [[Hoare-Logic-Foundations#The command-specific rules|the command-specific rules]], the ordinary *structural* inference rules of Hoare logic remain sound essentially unchanged — Strengthening Precedent, Weakening Consequent, Existential Quantification (ghost-variable elimination), Conjunction, and Substitution (with the standard "modified variable can't appear free elsewhere" side condition) are listed and hold for both partial and total correctness identically.

**One classical rule does not survive**, and identifying exactly why is one of the two or three most important ideas in the entire book. The "rule of constancy" —

$$\frac{\{p\}\ c\ \{q\}}{\{p \wedge r\}\ c\ \{q \wedge r\}} \quad (\text{no variable free in } r \text{ modified by } c) \quad \textbf{unsound}$$

— has long been the mechanism classical Hoare logic uses for scalability: extend a *local* specification by conjoining an arbitrary fact about untouched variables. In separation logic it fails outright:

$$\frac{\{x \mapsto -\}\ [x] := 4\ \{x \mapsto 4\}}{\{x \mapsto - \wedge y \mapsto 3\}\ [x] := 4\ \{x \mapsto 4 \wedge y \mapsto 3\}} \quad \text{invalid}$$

The premiss is genuinely valid; the conclusion is not, because its precondition doesn't rule out $x = y$ — and if they alias, mutating cell $x$ silently falsifies $y \mapsto 3$ even though $y$ is (syntactically) untouched by the command. The rule of constancy's soundness in classical Hoare logic silently assumed that "$r$ mentions no variable modified by $c$" was enough to guarantee $r$ survives execution of $c$; separation logic's heap breaks that assumption the moment aliasing through the heap becomes possible, because $r$ can depend on heap *cells* that $c$ modifies even when $r$ mentions no *variable* that $c$ modifies.

O'Hearn's fix — replacing $\wedge$ with $*$ — is the **frame rule**:

$$\frac{\{p\}\ c\ \{q\}}{\{p * r\}\ c\ \{q * r\}} \quad (\text{no variable free in } r \text{ modified by } c)$$

Now the side condition does real work: $p * r$ *asserts* that $r$'s heap portion is *disjoint* from whatever $c$ might touch, rather than merely hoping variable-non-mention implies heap-non-interference. This is the mechanism this article's job is only to *introduce* — its soundness proof, in terms of two underlying programming-language properties (*safety monotonicity* and the *frame property*), belongs to a later topic ([[The-Frame-Rule-and-Local-Reasoning|the frame rule and local reasoning]]), but the shape of the fix — swap $\wedge$ for $*$ — is exactly why the assertion language needed a separating connective in the first place, tying this whole article back to [[The-Separation-Logic-Assertion-Language|the first one]].

### Grounding: the frame rule is what a borrow checker gives you automatically

```rust
// The frame rule, concretely: verifying [x] := 4 only requires reasoning
// about the cell `x` points to. Anything disjoint (r) is *automatically*
// preserved -- exactly as Rust's aliasing rules guarantee that mutating
// through one exclusive borrow cannot affect memory a disjoint borrow
// still holds, with zero extra proof obligation at each call site.
fn mutate_one_cell(cell: &mut i32) { *cell = 4; }

fn frame_rule_in_action(a: &mut i32, disjoint_rest: &[i32]) {
    // {a |-> -}  mutate_one_cell(a)  {a |-> 4}      <- local spec
    mutate_one_cell(a);
    // {a |-> 4 * (disjoint_rest unchanged)}          <- framed automatically;
    // the type system, not a manual side-condition check, already proved
    // `a` and `disjoint_rest` don't overlap.
    let _ = disjoint_rest[0];
}
```

Where separation logic needs an explicit inference rule (with an explicit side condition to check by hand, or by an automated frame-inference algorithm) to license "the rest of the heap is untouched," Rust's borrow checker gives you the *same guarantee* baked into the type system for the one specific ownership discipline it enforces. If your compiler project is building a Hoare-triple-style verifier on top of a Rust-like language, this is exactly where a large chunk of your automatic frame inference will live: given a local specification for a function, statically determine its *footprint* (the cells/variables it might touch) so the frame rule's side condition can be checked — or discharged for free — rather than demanded of the user by hand.

## Where this leads

This article deliberately stays at the level of *specification syntax and the two central design decisions* — fault-sensitivity forcing "well-specified programs don't go wrong," and the rule-of-constancy-to-frame-rule swap. The full proof theory this sets up — Hoare's remaining structural rules formalized precisely, the frame rule's soundness proof from safety monotonicity and the frame property, and the complete local/global/backward-reasoning triples of rules for mutation, deallocation, allocation, and lookup — is Chapter 3's proper subject matter (§3.2 onward), building directly on [[Semantics-Of-Assertions|the satisfaction relation]] and [[Special-Classes-Of-Assertions|the precise/intuitionistic/supported taxonomy]] from Chapter 2 to prove each rule sound. For a verifier that checks Hoare-triple or refinement-style contracts against a Rust-like language: this is the layer where you decide what a *specification* is (partial vs. total, and whether your VCs ever need total-correctness's termination obligation at all, given how rarely Reynolds himself reaches for it) and where the fault-sensitivity design decision — treat every possible runtime memory fault as immediately falsifying the enclosing specification — has to be baked into your semantics before a single inference rule can be proved sound against it.
