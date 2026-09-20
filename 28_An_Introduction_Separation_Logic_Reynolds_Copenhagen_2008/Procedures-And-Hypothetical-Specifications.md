---
title: "Procedures and Hypothetical Specifications"
source: "An Introduction to Separation Logic (Reynolds, 2008)"
chapter: "Chapter 4, §4.5–4.6"
pages: "121–133"
tags: [separation-logic, hoare-logic, procedures, recursion, typing-contexts, proof-theory]
---

# Procedures and Hypothetical Specifications

[[book-guidelines|↩ Back to guidelines]]

## Why a program logic needs a *context*, not just a triple

Everything up through Chapter 3 verifies commands built from assignment, sequencing, conditionals, loops, and heap primitives — a closed universe where a Hoare triple $\{p\}\,c\,\{q\}$ is simply true or false, full stop, given the semantics of $c$. The moment you add procedures, that stops working. Consider

```
letrec fact(r; n) = if n = 0 then skip else (r := n*r; fact(r; n-1))
in fact(z; 5)
```

To prove anything about the call `fact(z; 5)`, you first need to know what `fact` *means* — but `fact`'s own body calls `fact` recursively, so proving a specification for the body requires already knowing a specification for the call inside it. You can't bottom this out by unfolding: the recursion may not terminate in general (or terminates but you don't want to reason about infinitely many unfoldings).

This is precisely [[Case-Studies-in-Program-Verification#The problem|the problem]] a type checker faces with `letrec` bindings, and precisely the problem a proof assistant's kernel faces when it lets you write recursive definitions: you need to be able to state and use a specification for a not-yet-fully-justified name, track that specification in something like a context, and discharge the obligation that the specification is actually consistent with the body — all before you're allowed to use the name unrestricted. Reynolds's answer is the **hypothetical specification**: a Hoare triple relativized to a context of assumptions about procedure names,
$$
\Gamma \vdash \{p\}\; c\; \{q\},
$$
which is defined to be true iff $\{p\}\,c\,\{q\}$ holds in every *environment* (an interpretation of procedure names as procedure meanings) that satisfies every specification listed in $\Gamma$. If you've seen a typing judgment $\Gamma \vdash e : T$, this is the same shape of idea, specialized to correctness assertions instead of types: $\Gamma$ is a context of assumed facts about free "variables" (here, procedure names instead of term variables), and the judgment says "given those assumptions, this fact holds."

## Simple procedures: the restrictions that make the theory tractable

Reynolds first pins down a restricted procedure mechanism — "simple" procedures — precisely so that hypothetical specifications stay well-behaved:

- Parameters are variables/expressions only (no passing commands or other procedures as parameters — no higher-order procedures yet).
- No global variables: every free variable of the body must be a formal parameter.
- Procedures are proper (calls are commands, not expressions).
- Calls are restricted to prevent aliasing between actual parameters.

The one genuinely novel piece of syntax is that formal parameters are split into two groups, syntactically: $v_1,\dots,v_m$ (which *may* be modified by the body) and $v_1',\dots,v_n'$ (which may *not*). A definition looks like
$$
\mathrm{let}\ h(v_1,\dots,v_m; v_1',\dots,v_n') = c\ \mathrm{in}\ c_0
$$
(nonrecursive) or `letrec` (recursive), and a call looks like $h(w_1,\dots,w_m; e_1',\dots,e_n')$ — actual modifiable parameters must be *variables* (you need somewhere to write the result back to), while actual unmodifiable parameters can be arbitrary expressions. This modifiable/unmodifiable split isn't cosmetic — it's what later lets the frame rule and the substitution rule combine cleanly when reasoning about a call site (see the `multfact` example below, and it resurfaces critically in the doubly-linked list procedures of §4.8, where swapping a modifying accessor for a non-modifying one silently breaks a surrounding proof despite both satisfying "the same" triple).

## Lifting the whole rule set into hypothetical form

Once specifications carry a context, every existing rule needs a $\Gamma \vdash$ prefix. Reynolds notes this lift is *trivial* — mechanically thread $\Gamma$ through:
$$
\text{Strengthening Precedent (SP):}\quad \frac{p \Rightarrow q \qquad \Gamma \vdash \{q\}\,c\,\{r\}}{\Gamma \vdash \{p\}\,c\,\{r\}}
\qquad\qquad
\text{Substitution (SUB):}\quad \frac{\Gamma \vdash \{p\}\,c\,\{q\}}{\Gamma \vdash \{p/\delta\}\,(c/\delta)\,\{q/\delta\}}
$$
with the same side-conditions on $\delta$ as before, and crucially, **substitutions never touch procedure names** — $\Gamma$'s bindings are opaque, like a constant's type signature.

Two new rules do the real work. **Hypothesis (HYPO)** says you may use anything already sitting in the context:
$$
\Gamma,\ \{p\}\,c\,\{q\},\ \Gamma' \vdash \{p\}\,c\,\{q\}.
$$
This is the separation-logic analogue of the variable rule $\Gamma, x{:}T, \Gamma' \vdash x : T$ — a judgment is trivially derivable if it's literally already an assumption.

**Simple Procedures (SPROC)**, the nonrecursive introduction rule, says: prove the body against the *outer* context, then you're licensed to add a hypothesis about the *call* when reasoning about the scope:
$$
\frac{\Gamma \vdash \{p\}\,c\,\{q\} \qquad \Gamma,\ \{p\}\,h(\vec v;\vec v')\,\{q\} \vdash \{p'\}\,c'\,\{q'\}}
{\Gamma \vdash \{p'\}\;\mathrm{let}\ h(\vec v;\vec v') = c\ \mathrm{in}\ c'\;\{q'\}}
$$
(side condition: $h$ not free in $\Gamma$). This is unremarkable — it's just "prove [[Doubly-Linked-and-Xor-Linked-List-Segments#The definition|the definition]], then use it as an assumed fact in the rest of the program," structurally identical to a `let`-typing rule.

**Simple Recursive Procedures (SRPROC)** is where the real content is:
$$
\frac{\Gamma,\ \{p\}\,h(\vec v;\vec v')\,\{q\} \vdash \{p\}\,c\,\{q\} \qquad \Gamma,\ \{p\}\,h(\vec v;\vec v')\,\{q\} \vdash \{p'\}\,c'\,\{q'\}}
{\Gamma \vdash \{p'\}\;\mathrm{letrec}\ h(\vec v;\vec v') = c\ \mathrm{in}\ c'\;\{q'\}}
$$
Notice the left premiss: to prove the body $c$ satisfies $\{p\}\,c\,\{q\}$, you're *allowed to assume* $\{p\}\,h(\vec v;\vec v')\,\{q\}$ — the very specification you're trying to establish, applied to any recursive call inside $c$. This is a **recursion hypothesis**, structurally the coinductive trick underlying every soundness argument for recursive definitions: you guess a specification, add it to the context as an assumption, discharge the body under that assumption, and if it closes, the guess was consistent. (Reynolds flags — correctly — that this only works for *partial* correctness. For total correctness you'd need a well-founded measure decreasing on recursive calls, exactly the guardedness/termination check a proof assistant's kernel must separately enforce before it will accept a recursive definition as productive; SRPROC alone gives you no such guarantee, deliberately.)

## Calls: HYPO specialized, then generalized by substitution

**Call (CALL)** is just HYPO restricted to a call command — trivial when actual parameters exactly match the formals. The useful rule is **General Call (GCALL)**, which composes CALL with SUB to reach an arbitrary legal (nonaliasing) call:
$$
\Gamma,\ \{p\}\,h(v_1,\dots,v_m; v_1',\dots,v_n')\,\{q\},\ \Gamma' \;\vdash\; \{p/\delta\}\;h(w_1,\dots,w_m; e_1',\dots,e_n')\;\{q/\delta\},
$$
where $\delta = v_1{\to}w_1,\dots,v_m{\to}w_m,\ v_1'{\to}e_1',\dots,v_n'{\to}e_n',\ v_1''{\to}e_1'',\dots$ — and that last piece, $v_1''\to e_1'', \dots$, is the mechanism for **ghost parameters**: variables occurring free in $p$ or $q$ that are *not* formal parameters of the procedure at all, just extra bookkeeping the specification needs (a bound on a value, an auxiliary sequence standing for the abstract data the procedure manipulates). Ghost parameters carry no operational content — they never appear in the code, only in the proof — which should feel familiar: they are exactly a specification-level analogue of an implicit/erased argument. GCALL is, mechanically, "instantiate a polymorphic/parametric signature at a call site via simultaneous substitution," the same move an elaborator performs when it specializes a function's type at an application.

## The `multfact` example: the frame rule standing in for constancy

Reynolds's worked example is a recursive procedure multiplying `r` by `n!`, called to compute `5! × 10`:
$$
\begin{aligned}
&\{z = 10\}\\
&\mathrm{letrec}\ \mathrm{multfact}(r; n)\{r_0\} = \\
&\quad \{n \ge 0 \wedge r = r_0\}\\
&\quad \mathrm{if}\ n = 0\ \mathrm{then}\ \{n=0 \wedge r=r_0\}\ \mathrm{skip}\ \{r = n!\times r_0\}\\
&\quad \mathrm{else}\ \{n{-}1\ge 0 \wedge n{\times}r = n{\times}r_0\}\ r := n{\times}r;\ \{n{-}1\ge 0 \wedge r = n{\times}r_0\}\\
&\qquad\quad \mathrm{multfact}(r; n{-}1)\{n{\times}r_0\}\ \{r = (n{-}1)!\times n\times r_0\}\\
&\quad \{r = n!\times r_0\}\\
&\mathrm{in}\ \{5\ge 0 \wedge z=10\}\ \mathrm{multfact}(z; 5)\{10\}\ \{z = 5!\times 10\}
\end{aligned}
$$
Here $r_0$ is a ghost parameter recording the *initial* value of $r$, needed because $r$ is modified by the procedure and the postcondition wants to talk about "what $r$ started as." SRPROC generates the hypothesis $\{n\ge0 \wedge r=r_0\}\ \mathrm{multfact}(r;n)\{r_0\}\ \{r=n!\times r_0\}$; GCALL instantiates it at the recursive call site to get a specification for `multfact(r; n-1){n*r0}`. But that instantiated triple mentions only `r` and `n`, and to combine it with the surrounding proof you need to know that the recursive call *doesn't disturb* the fact `n-1 ≥ 0`. Since `n` isn't modified by the call, **the frame rule** licenses conjoining `n-1 ≥ 0` onto both sides for free — and because this frame is a pure (heap-independent) assertion, the separating conjunction it introduces collapses to ordinary conjunction. Reynolds is explicit about the moral: *the frame rule is doing the job the unsound rule of constancy used to do in classical Hoare logic*, but doing it soundly, because its side condition (the frame is untouched — no aliasing, no footprint overlap) is exactly what constancy failed to check.

## Annotated hypothetical specifications: the bidirectional-typing connection (§4.6)

Section 3.12 built machinery connecting *formal proofs* to *[[Annotated-Specifications|annotated specifications]]* (proof outlines) via two functions: $\Phi$, which takes a formal proof and reconstructs the annotations it implies, and $\Psi$, which takes an annotated specification and reconstructs (checks) the formal proof it encodes. Section 4.6 re-does this for the hypothetical setting. The key new device is the **annotated context** $\hat\Gamma$: instead of a bare hypothesis $\{p\}\,h(\vec v;\vec v')\,\{q\}$, an annotated hypothesis also lists the *ghost parameters* explicitly, $\{p\}\,h(\vec v;\vec v')\{v_1'',\dots,v_k''\}\,\{q\}$ — because an annotated call site must specify the *entire* substitution $\delta$, ghosts included, not leave them to be inferred.

This is worth pausing on, because it's a clean instance of the bidirectional-typing pattern this project cares about. $\Phi$ (proof $\to$ annotation) is the *inference* direction: given a fully-elaborated derivation, synthesize the annotations (including which ghost values were used) that make it locally checkable. $\Psi$ (annotation $\to$ proof) is the *checking* direction: given the annotations — the "he wrote down what he meant" version — verify that a real formal proof exists underneath, filling in exactly the premisses (verification conditions, frame instances) the annotation doesn't spell out. The generalization needed for procedures is that $\Psi$ must now walk the annotated context alongside the annotated command, in lock-step — precisely the discipline an elaborator needs when checking a call to an already-declared (or mutually-recursive, still-being-checked) function against its recorded signature.

## Grounding

**Rust.** The modifiable/unmodifiable parameter split maps almost literally onto `&mut` vs. `&`:

```rust
// {n >= 0 && *r == r0}  multfact(r, n) {*r == n! * r0}
// r0 is a ghost — it exists only in the contract, not the signature.
fn multfact(r: &mut u64, n: u64) {
    if n == 0 {
        // skip
    } else {
        *r *= n;
        multfact(r, n - 1); // recursion hypothesis assumed here,
                             // exactly as SRPROC assumes it in the proof
    }
}
```
A contract-checking tool (Prusti, Creusot) attaches a `requires`/`ensures` pair to this signature and, to verify the recursive call, must do precisely what GCALL + the frame rule do: instantiate the assumed contract at the smaller argument, and separately discharge that nothing the contract depends on was invalidated by call-incompatible aliasing (Rust's borrow checker enforces the *non-aliasing* precondition GCALL requires purely at the type level, for free, which separation logic has to state as an explicit assertion).

**Lean.** The correspondence to a typing judgment is exact enough to state directly: $\Gamma \vdash \{p\}\,c\,\{q\}$ is playing the role of $\Gamma \vdash e : T$, with procedure names as opaque constants of a known "type" (here, a Hoare-triple signature rather than a `Sort`). SRPROC's recursion hypothesis is the same move Lean's kernel performs (via well-founded or structural recursion) when it lets a recursive definition refer to itself: assume a specification for the recursive call, discharge the body, and separately verify termination so the "assumption" isn't circular vacuously. The ghost parameters here are a direct analogue of implicit arguments resolved by unification rather than passed explicitly — GCALL's substitution $\delta$, which must be inferred from the specification even though it plays no role in the executable call, is exactly the kind of metavariable instantiation problem (find $\delta$ making $p/\delta$ match the goal) a bidirectional elaborator solves via Miller-pattern unification.

**Python**, briefly, as an executable sketch of the same recursion structure without the proof apparatus:
```python
def multfact(r, n):
    if n == 0:
        return r
    return multfact(r * n, n - 1)
```
The contract $\{n\ge 0 \wedge r=r_0\}\ \dots\ \{r = n! \times r_0\}$ is invisible here — which is exactly the point: this is what you get if you erase the specification apparatus, leaving only the operational content GCALL/SRPROC were reasoning *about*.

## Where this leads

This section is the load-bearing prerequisite for essentially everything else built on top of lists, trees, and dags in Chapters 4–5: `mergesort`/`merge` (§4.7), the doubly- and xor-linked list procedures (§4.8–4.9), `copytree` and `subst1` in Chapter 5, and the array algorithms of Chapter 6 are all *recursive procedures with hypothetical specifications* — none of them could be stated, let alone proved, without SRPROC's recursion-hypothesis mechanism and GCALL's controlled substitution. Chapter 5's `copytree` in particular pushes ghost parameters further: it needs an **assertion variable** (a ghost parameter ranging over heap *properties*, not values) as the fix for a recursion hypothesis that's otherwise too weak to prove itself — the direct sequel to this topic, and the subject of the next article. If you're building a verifier: the pattern here — a context of assumed signatures, a well-founded-recursion side condition kept deliberately separate from the logical soundness argument, and an annotation layer whose two directions are literally inference and checking — is the same architecture your elaborator will need for handling recursive and mutually-recursive function declarations against a trusted kernel.
