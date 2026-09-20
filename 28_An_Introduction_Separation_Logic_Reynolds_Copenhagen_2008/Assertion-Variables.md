---
title: "Assertion Variables"
source: "An Introduction to Separation Logic (Reynolds, 2008)"
chapter: "Chapter 5, §5.3–5.5"
pages: "169–177"
tags: [separation-logic, assertion-variables, ghost-state, recursion-hypotheses, substitution, unification]
---

# Assertion Variables

[[book-guidelines|↩ Back to guidelines]]

## The gap this closes: a recursion hypothesis that talks about "everything else"

The previous topic ended at a genuine impasse. `copytree(j; i)` provably does satisfy $\{\mathrm{dag}_\tau(i)\}\ \mathrm{copytree}(j;i)\{\tau\}\ \{\mathrm{dag}_\tau(i)*\mathrm{tree}_\tau(j)\}$, but *proving* it by the standard recursive-procedure technique (SRPROC: assume this exact specification as your recursion hypothesis, then discharge the body) fails, because the hypothesis is silent about whether a recursive call preserves shared substructure it isn't supposed to touch. What's missing is a way for the specification to say: *"whatever else was true of the heap when I started, is still true of it (outside the freshly-built copy) when I finish — for any such 'whatever else.'"* That's a universally-quantified-over-properties statement, and stating it requires a new kind of variable: one that ranges not over values, but over **properties of heaps** — i.e., over assertions themselves.

This is the single idea of this section, and it's worth being precise about why it's a new *kind* of variable rather than just another ghost parameter of the usual sort. A value-ghost-parameter (like `r0` in the `multfact` example, or `τ` here) lets a specification talk about a fixed but unknown *value*. An **assertion variable** lets a specification talk about a fixed but unknown *predicate* — closer in spirit to a variable ranging over propositions/types than one ranging over data, and it is introduced with exactly that generality: it can be instantiated by *any* assertion whatsoever at a call site.

## Extending state with an assertion store

Formally, the state gets a third component, an **assertion store** mapping assertion variables to heap properties:
$$
\mathrm{AStores}_A = A \to (\mathrm{Heaps}\to\mathbb{B})
\qquad\qquad
\mathrm{States}_{AV} = \mathrm{AStores}_A \times \mathrm{Stores}_V \times \mathrm{Heaps},
$$
where $A$ is a finite set of assertion variables. Since assertion variables are *always* ghosts, the assertion store affects only the *meaning* of assertions, never the execution of commands — this is the same discipline as ordinary ghost variables and the field-count heap auxiliary from the previous topic: extra structure available to the proof, invisible to the program. Satisfaction becomes a three-place relation $as, s, h \models p$ (generalizing $s,h\models p$ from Chapter 2, with every existing satisfaction clause carried over unchanged on its left side), plus one new clause defining what it means for an assertion variable itself to be used as an assertion:
$$
as, s, h \models a \iff as(a)(h).
$$
That is: to check whether the assertion-variable-as-assertion $a$ holds of heap $h$, look up what property $as$ currently associates with $a$, and apply it to $h$.

## The generalized substitution law: two substitution targets at once

Chapter 2's Partial Substitution Law for Assertions handled ordinary variable-for-expression substitution. **Proposition 18** generalizes it to a *simultaneous* substitution $\delta$ that maps assertion variables to assertions *and* ordinary variables to expressions in one pass:
$$
\delta = a_1 \to p_1,\dots,a_m \to p_m,\ v_1\to e_1,\dots,v_n\to e_n.
$$
The law says: satisfaction of $p/\delta$ under a store $s$ and assertion store $as$ (with domains large enough to cover the free variables and assertion variables involved) equals satisfaction of the *original* $p$ under an *updated* store $\hat s = [s \mid v_1{:}[\![e_1]\!] \mid \cdots]$ and an updated assertion store
$$
\widehat{as} = [as \mid a_1 : \lambda h.\,(as,s,h\models p_1) \mid \cdots \mid a_m : \lambda h.\,(as,s,h\models p_m)].
$$
Read that closure carefully: substituting the assertion $p_i$ in for the assertion variable $a_i$ doesn't just textually replace $a_i$ by $p_i$ — it installs, in the assertion store, a *function of the heap* that decides membership by evaluating $p_i$ under the *original* $s, as$. This is exactly what you need for the substitution to be sound under later heap growth or further substitution: $a_i$ now behaves as an opaque name for "the property $p_i$ evaluated in this specific closing context," not as a literal syntactic stand-in. This is a genuinely higher-order substitution — you are substituting a *predicate* for a *predicate variable*, which is precisely the operation second-order/higher-order unification has to invert when it goes the other direction (given the substituted form, recover what $p_i$ must have been).

Substitution (SUB) is correspondingly extended: $a_1,\dots,a_m$ range over the assertion variables free in $p$ or $q$, $v_1,\dots,v_n$ over the ordinary variables, with the same aliasing-avoiding side condition on the $e_i$'s as before (an $e_i$ replacing a modified $v_i$ must not occur free in any other $e_j$ *or in any $p_j$*) — the annotated form (SUBan) is identical but threads through an annotation $A$ as well. Reynolds gives a sharp minimal example showing the substitution really is order- and identity-sensitive: in $\{a\}\ x:=y\ \{a\}$, substituting $a\to(y=z),\ x\to x,\ y\to y$ correctly yields $\{y=z\}\ x:=y\ \{y=z\}$ (valid — $y$ isn't modified by the assignment, so "$y=z$" survives), but substituting $a\to(x=z)$ instead would (incorrectly) claim $\{x=z\}\ x:=y\ \{x=z\}$ — which is false in general, since $x$ *is* modified. The side condition on which variables the substituted assertion may mention is what rules this out; it's the exact discipline that prevents variable capture in any substitution-based semantics, now generalized to catch capture through an assertion-variable instantiation as well as through an ordinary one.

## Copying dags to trees: the fix in action (§5.4)

With assertion variables in hand, the strengthened specification for `copytree` is
$$
\{p \wedge \mathrm{dag}_\tau(i)\}\ \mathrm{copytree}(j;i)\{\tau,p\}\ \{p * \mathrm{tree}_\tau(j)\},
$$
where $p$ is an assertion-variable ghost parameter. Read the postcondition carefully: $p$ (whatever heap property was true *before* the call, restricted to the part of the heap not newly allocated) now holds **separately** (via $*$) from the newly created tree — i.e., the call is asserted to add a disjoint new region without disturbing whatever $p$ was witnessing beforehand. Substituting $\mathrm{dag}_\tau(i)$ for $p$ recovers exactly the specification from the previous topic, $\{\mathrm{dag}_\tau(i)\}\ \mathrm{copytree}(j;i)\{\tau,\mathrm{dag}_\tau(i)\}\ \{\mathrm{dag}_\tau(i)*\mathrm{tree}_\tau(j)\}$ — but *this* time as a derived weaker consequence of a universally-quantified stronger fact, not as the (unprovable, as we saw) starting hypothesis itself. The universal quantification over $p$ is what makes the recursion hypothesis strong enough to survive its own recursive call, because now the hypothesis you get to assume, for the sibling recursive call on $\tau_2$, includes the fact that whatever held about the sibling's region — including "there's a dag for $\tau_2$ sitting right there" — is preserved unchanged.

Working through the pair case: after reading off the two children, the current state satisfies (roughly, ignoring pure conjuncts) $p \wedge (i\mapsto i_1,i_2 * (\mathrm{dag}_{\tau_1}(i_1)\wedge\mathrm{dag}_{\tau_2}(i_2)))$. Distributing $p\,\wedge\,\text{--}$ across $*$ (a valid direction of the semidistributive law from Chapter 2) and then across the inner $\wedge$ gives, among the resulting conjuncts, $p \wedge \mathrm{dag}_{\tau_2}(i_2) \wedge \mathrm{dag}_{\tau_1}(i_1)$ — meaning the recursive call `copytree(j1; i1){τ1}` can now be given the *conjunction* $(\tau=(\tau_1\cdot\tau_2) \wedge p \wedge \mathrm{dag}_{\tau_2}(i_2))$ as its own assertion-variable instantiation. That is, the "everything else preserved" clause for the *inner* call is literally "everything the outer call promised to preserve, plus the sibling subdag" — a strictly bigger property than $p$ alone, and exactly the extra information the naive proof lacked. After both recursive calls return, their postconditions — each of the form (old stuff preserved) $*$ (new tree) — combine via $*$-introduction into $(\tau=(\tau_1\cdot\tau_2)\wedge p) * \mathrm{tree}_{\tau_1}(j_1) * \mathrm{tree}_{\tau_2}(j_2)$, and `cons`-ing $j_1,j_2$ together folds the two new trees into one, closing the proof. One derivation step is marked with the fact that $\mathrm{dag}_\tau(i)$ is *intuitionistic* (from the previous topic): $\mathrm{true} * \mathrm{dag}_\tau(i) \Rightarrow \mathrm{dag}_\tau(i)$ is exactly what licenses dropping an unneeded $*\,\mathrm{true}$ frame introduced by the semidistributive-law manipulation.

## Substitution in S-expressions (§5.5): the payoff procedure

`subst1(i; a, j)` substitutes the dag at `j` for every occurrence of atom `a` in the tree at `i`, producing (destructively, in place) a tree for the substituted S-expression:
$$
\{\mathrm{tree}_\tau(i) * (p\wedge\mathrm{dag}_{\tau'}(j))\}\ \mathrm{subst1}(i; a,j)\{\tau,\tau',p\}\ \{\mathrm{tree}_{\tau/a\to\tau'}(i) * p\}.
$$
Notice this specification *needs* the assertion-variable fix even though `subst1` isn't `copytree` — because `subst1` calls `copytree` internally (once per occurrence of `a` in the tree) to duplicate the dag at `j` at that occurrence, and each such call must not disturb the *other* not-yet-visited occurrences still waiting to be copied, nor the fact that `j`'s dag is preserved for the *next* occurrence. This is the general lesson: once one part of a program's correctness proof needs "preserves an arbitrary caller-supplied property," *every* caller of that part inherits the same need, transitively — assertion variables propagate upward through the call graph exactly the way an effect or a capability requirement propagates through a type signature.

The proof structure otherwise mirrors §5.4 closely — case-split on `isatom(i)`, and within that on `i = a`; in the matching-atom leaf case, invoke `copytree(i; j){τ', p}` directly (with roles of `i`/`j` swapped from `copytree`'s own signature, since here it's the *tree*'s cell being overwritten with a fresh copy of the dag); in the pair case, recurse on both children in sequence, each call instantiating the assertion variable with "$p$ conjoined with whatever the sibling subtree/dag facts established so far" — the same "each sibling call gets a strictly larger preserved-property than the caller received" pattern as before. Two steps in the annotated proof (marked $(*)$ and $(**)$ in the source) are justified by exactly the same semidistributive-law-then-intuitionistic-collapse argument used in §5.4, now applied twice (once for the left recursive call, once for the right) — worth recognizing as a reusable proof idiom rather than two unrelated derivations.

## Grounding

**Rust.** There is no native Rust construct for "a variable ranging over an arbitrary predicate on the heap" — but the pattern assertion variables encode (a recursive call's contract universally quantified over an arbitrary caller-supplied invariant on everything it doesn't touch) is exactly the shape of a **frame condition expressed via a generic trait bound** in a verification tool like Creusot: a specification like `#[ensures(old(p(*self)) == p(*self))]` for an arbitrary predicate `p` the caller supplies is a direct (if informal) Rust rendering of "$p$ is preserved," and a generic function `fn copy_shared<P: HeapProp>(...)` parameterized over an arbitrary property witness is the closest structural analogue — quantifying over the property, not fixing it, is what makes the contract compositional across arbitrarily many call sites the same way universally quantifying over $p$ makes `copytree`'s contract compositional across arbitrarily many recursive calls.

**Lean.** This is the section where the correspondence to **metavariables and unification** is most direct and worth naming explicitly. An assertion variable $p$, universally quantified in a specification and *instantiated by substitution at each use site* (with an arbitrary assertion, chosen so the surrounding proof goes through), is structurally a **second-order metavariable**: a placeholder standing for an unknown predicate, resolved by unification against the shape of the goal at hand. The generalized substitution law (Proposition 18) — install a *closure* $\lambda h.\,(as,s,h\models p_i)$ into the assertion store rather than literally substituting text — is exactly how an elaborator must instantiate a higher-order metavariable: not by naive textual substitution (which risks capturing free variables of the surrounding context incorrectly) but by closing over the context at the point the metavariable's value is determined, the same discipline **Miller's pattern unification** exists to make tractable for exactly this class of problem (a metavariable applied to a list of distinct bound variables, instantiated by a term built from those variables). Each recursive call in §5.4/§5.5 choosing "$p$ conjoined with the sibling's facts" as its instantiation of the assertion-variable parameter is, concretely, a unification problem being solved by hand: find an assertion $p'$ such that substituting it for the callee's assertion-variable parameter makes the callee's postcondition match what the caller's proof needs at that point. A proof assistant automating this (rather than requiring the human proof, as Reynolds does here) would need exactly a higher-order-pattern unifier for assertions.

**Python**, sketching (informally, no proof) what "preserve an arbitrary caller property" looks like operationally:
```python
def copy_dag_to_tree(root, preserved_invariant):
    # preserved_invariant: Callable[[Heap], bool] — stands in for the assertion variable p.
    # Contract (informal): preserved_invariant(heap_before) == preserved_invariant(heap_after \ new_tree)
    ...
```

## Where this leads

Assertion variables close out the sharing problem this chapter opened with `dag`, and the mechanism — a ghost parameter ranging over predicates, substituted in via a closure-respecting generalized substitution law — doesn't reappear as its own named topic later in the book, but the *pattern* it establishes (a recursive procedure's specification universally quantified over "whatever else was true, preserved") is silently assumed wherever later chapters verify procedures that traverse shared or aliased structure without disturbing it (the Schorr-Waite algorithm's use of separating implication in Chapter 1's overview gestures at a closely related device for a different purpose: expressing "restore this modified structure back to its original shape"). If you're building a checker with a metavariable-based elaborator: this section is a compact, fully worked case study of exactly the substitution discipline your unifier needs — closures over the *instantiating* context rather than naive text substitution, and an explicit, checkable side-condition (the one guarding SUB) for exactly when a proposed instantiation would capture variables it shouldn't. Getting that side-condition right here, by hand, on paper, is the same correctness property a pattern-unification implementation has to get right, mechanically, at every metavariable assignment.
