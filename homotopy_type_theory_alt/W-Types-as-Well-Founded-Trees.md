---
title: "W-Types as Well-Founded Trees"
book: "Homotopy Type Theory: Univalent Foundations of Mathematics"
source: "sources/14_homotopy_type_theory/book.pdf"
chapters: "Chapter 5, §5.3 (printed pp. 154–157)"
tags: [hott, type-theory, inductive-types, w-types, recursion]
---

[[book-guidelines|↩ Back to guidelines]] · parent topic: [[Inductive-Types]]

# W-Types as Well-Founded Trees

## 1. Why the book introduces them

Inductive types come in endless variety: $\mathbb{N}$, lists, binary trees, rose trees, abstract syntax trees. Studying them one at a time scales badly. The book (§5.3) points out that they "can all be formally reduced to a few special cases", and that one of these is Martin-Löf's **W-type**, which "encapsulates the recursion aspect of any inductive type". The book does not carry out the reduction in general. It presents W-types as one concrete, fully explicit family that shows what "an inductive type" boils down to.

The idea is that every inductive element is a **tree**. Each node carries a *label*, and the label determines how many children the node has. Everything else (how you build elements, how you define functions out of them, how you prove things about them) follows from that shape.

## 2. The two parameters

A particular W-type is fixed by

- a type of labels $A : \mathcal{U}$, and
- a family $B : A \to \mathcal{U}$ recording the **arity** of each label.

It is written $\mathsf{W}_{(a:A)}\, B(a)$. A node labelled $a : A$ has "$B(a)$-many" branches, one per element $b : B(a)$. The children are packaged as a function
$$f : B(a) \to \mathsf{W}_{(x:A)}\, B(x),$$
where $f(b)$ is the $b$-th child. Using a function rather than a list is the key design choice: it allows infinite branching (take $B(a) = \mathbb{N}$) and finite branching in the same framework ($B(a)$ a finite type).

The single constructor is
$$\mathsf{sup} : \prod_{a:A} \Big(B(a) \to \mathsf{W}_{(x:A)} B(x)\Big) \to \mathsf{W}_{(x:A)} B(x).$$
"Sup" abbreviates *supremum*. The book reserves the word "constructor" for the actual functions in an inductive definition, and calls the elements of $A$ *labels*.

## 3. Encoding the natural numbers

Take $A :\equiv \mathbf{2}$, with labels $0_{\mathbf{2}}$ ("zero") and $1_{\mathbf{2}}$ ("successor"). Arity is defined by simple elimination on $\mathbf{2}$ into the universe: $\mathsf{rec}_{\mathbf{2}}(\mathcal{U}, \mathbf{0}, \mathbf{1})$ returns the empty type for $0_{\mathbf{2}}$ and the unit type for $1_{\mathbf{2}}$. So
$$\mathbb{N}^{\mathsf{w}} :\equiv \mathsf{W}_{(b:\mathbf{2})}\, \mathsf{rec}_{\mathbf{2}}(\mathcal{U}, \mathbf{0}, \mathbf{1}, b).$$
(The superscript $\mathsf{w}$ distinguishes this encoding from the primitive $\mathbb{N}$.) The elements are:
$$0^{\mathsf{w}} :\equiv \mathsf{sup}\big(0_{\mathbf{2}},\ \lambda x.\ \mathsf{rec}_{\mathbf{0}}(\mathbb{N}^{\mathsf{w}}, x)\big)$$
$$1^{\mathsf{w}} :\equiv \mathsf{sup}\big(1_{\mathbf{2}},\ \lambda x.\ 0^{\mathsf{w}}\big) \qquad \mathsf{succ}^{\mathsf{w}} :\equiv \lambda n.\ \mathsf{sup}(1_{\mathbf{2}},\ \lambda x.\ n).$$

Zero is a node with no children: its child function is the empty function $\mathbf{0} \to \mathbb{N}^{\mathsf{w}}$, produced by elimination on $\mathbf{0}$. Successor is a node with exactly one child, its predecessor, indexed by $\mathbf{1}$. A natural number *is* a degenerate tree, a path.

**Lists** follow the same pattern. The book takes $1 + A$ labels (one nullary for the empty list, plus one unary label per $a : A$ for "cons $a$"):
$$\mathsf{List}(A) :\equiv \mathsf{W}_{(x:\,\mathbf{1}+A)}\ \mathsf{rec}_{\mathbf{1}+A}(\mathcal{U}, \mathbf{0}, \lambda a.\ \mathbf{1}, x).$$
Binary trees would use labels with arity $\mathbf{2}$.

## 4. Induction and recursion

**Induction.** To prove $E : \mathsf{W}_{(x:A)} B(x) \to \mathcal{U}$ for every tree, it suffices to prove it for $\mathsf{sup}(a, f)$ *assuming it holds for every child* $f(b)$. Formally one must supply
$$e : \prod_{a:A}\ \prod_{f : B(a) \to \mathsf{W}}\ \Big(\prod_{b : B(a)} E(f(b))\Big) \to E(\mathsf{sup}(a, f)).$$
The hypothesis $g : \prod_{b:B(a)} E(f(b))$ is the inductive hypothesis. It quantifies over $B(a)$ because each $b$ indexes one child.

**Recursion and its computation rule** (judgmental, not merely propositional):
$$\mathsf{rec}_{\mathsf{W}}(E, e, \mathsf{sup}(a, f)) \equiv e\big(a, f, \lambda b.\ \mathsf{rec}_{\mathsf{W}}(E, e, f(b))\big).$$
The recursor applies itself to every child, packages the results as a function $g$, and hands $(a, f, g)$ to the step function $e$.

### Worked example: $\mathsf{double}$ on $\mathbb{N}^{\mathsf{w}}$

Write $B :\equiv \mathsf{rec}_{\mathbf{2}}(\mathcal{U}, \mathbf{0}, \mathbf{1})$. The step function does case analysis on the label:
$$e :\equiv \lambda a.\ \mathsf{ind}_{\mathbf{2}}(C, e_0, e_1, a), \qquad C :\equiv \lambda a.\ \prod_{f : B(a) \to \mathbb{N}^{\mathsf{w}}}\ \prod_{g : B(a) \to \mathbb{N}^{\mathsf{w}}}\ \mathbb{N}^{\mathsf{w}}$$
$$e_0 :\equiv \lambda f.\lambda g.\ 0^{\mathsf{w}} \qquad e_1 :\equiv \lambda f.\lambda g.\ \mathsf{succ}^{\mathsf{w}}\big(\mathsf{succ}^{\mathsf{w}}(g(\star))\big).$$
Then $\mathsf{double} :\equiv \mathsf{rec}_{\mathbb{N}^{\mathsf{w}}}(\mathbb{N}^{\mathsf{w}}, e)$. For the zero label, $B(0_{\mathbf{2}}) = \mathbf{0}$, so $f$ and $g$ are irrelevant. For the successor label, $B(1_{\mathbf{2}}) = \mathbf{1}$, so there is a single recursive result $g(\star)$ for the predecessor. The book then unfolds $\mathsf{double}(1^{\mathsf{w}}) \equiv \mathsf{succ}^{\mathsf{w}}(\mathsf{succ}^{\mathsf{w}}(0^{\mathsf{w}}))$ step by step using the computation rule.

**Uniqueness (Theorem 5.3.1).** If $g, h : \prod_{w} E(w)$ both satisfy the recurrence $e$ *propositionally*, i.e. $g(\mathsf{sup}(a,f)) = e(a, f, \lambda b.\, g(f(b)))$ and likewise for $h$ (for all $a, f$), then $g = h$. This is the reason recursion defines a function uniquely, which §5.4 then recasts as initiality.

## 5. Grounding in code

**Lean.** Lean's kernel generates exactly this shape of recursor for any inductive type, and Mathlib ships `WType`. A direct transcription (the book's recursor is the dependent one):

```lean
universe u

inductive W (A : Type) (B : A → Type) where
  | sup (a : A) (f : B a → W A B) : W A B

def W.rec' {A : Type} {B : A → Type} {E : W A B → Sort u}
    (e : (a : A) → (f : B a → W A B) → ((b : B a) → E (f b)) → E (W.sup a f)) :
    (w : W A B) → E w
  | .sup a f => e a f (fun b => W.rec' e (f b))

def NatB : Bool → Type
  | false => Empty
  | true  => Unit

abbrev Nw := W Bool NatB

def zeroW : Nw := W.sup false (fun x => nomatch x)
def succW (n : Nw) : Nw := W.sup true (fun _ => n)

def doubleW : Nw → Nw :=
  W.rec' (E := fun _ => Nw) fun a _ g =>
    match a with
    | false => zeroW
    | true  => succW (succW (g ()))
```

The equation for `W.rec'` is the computation rule, read as a definition by structural recursion.

**Rust.** A Rust `enum` is a sum of labelled nodes, and `Box` makes the recursion finite-sized. The type family $B(a)$ is modelled here by a `Vec` of children, which only captures *finitely* branching W-types. A true $B(a) \to \mathsf{W}$ needs a closure or an indexed store.

```rust
struct W<A> {
    label: A,
    children: Vec<W<A>>, // models f : B(label) -> W, with B(label) = 0..children.len()
}

// Non-dependent recursor: fold with a step function e(label, results).
fn fold<A, R>(w: &W<A>, e: &impl Fn(&A, Vec<R>) -> R) -> R {
    let results = w.children.iter().map(|c| fold(c, e)).collect();
    e(&w.label, results)
}

fn double(n: &W<bool>) -> W<bool> {
    fold(n, &|label, mut g: Vec<W<bool>>| {
        if !*label {
            W { label: false, children: vec![] }
        } else {
            let pred = g.pop().unwrap();
            let succ = |x| W { label: true, children: vec![x] };
            succ(succ(pred))
        }
    })
}
```

`fold` is the shape of the book's computation rule: recurse on every child, then combine with $e$. Note it is only the *non-dependent* recursor. Rust has no way to express the dependent induction principle.

**Python.** Here children are a genuine function, so infinite branching is representable (lazily):

```python
from dataclasses import dataclass
from typing import Callable, Any

@dataclass
class Sup:
    label: Any
    f: Callable[[Any], "Sup"]   # f : B(label) -> W

def rec(e, w: Sup):
    # e(a, f, g) with g = lambda b: rec(e, f(b))  -- the computation rule
    return e(w.label, w.f, lambda b: rec(e, w.f(b)))

def zero_w():
    return Sup(False, lambda x: (_ for _ in ()).throw(ValueError("B(0) is empty")))

def succ_w(n):
    return Sup(True, lambda _x: n)

def double_step(a, f, g):
    return zero_w() if not a else succ_w(succ_w(g(())))   # () plays the role of star

two_times_one = rec(double_step, succ_w(zero_w()))
```

## 6. How it fits

```
Inductive types (§5.1)
   └─ every one is a tree of labelled nodes
        └─ W-types (§5.3): A = labels, B = arities, one constructor sup
             ├─ induction / recursion principle + judgmental computation rule
             ├─ Theorem 5.3.1: recursion is unique (propositionally)
             └─ §5.4: this uniqueness = (homotopy-)initial algebra
```

**What it depends on.** $\Pi$-types and $\Sigma$-types (the arity family and function-typed children), $\mathbf{0}$, $\mathbf{1}$, $\mathbf{2}$, and a universe (to state $B : A \to \mathcal{U}$).

**What depends on it.** The initial-algebra reading in §5.4 and the general syntax of inductive definitions in §5.6. Both reuse the "children as a function out of an arity type" idea.

### Bearing on the compiler project (Focus Area: `type-theory`)

- **Kernel representation.** Everything the elaborator's kernel must know about an inductive declaration (constructor arities, recursive argument positions) is in the pair $(A, B)$. Lean's recursor generation is, in essence, the specialization of `W.rec'` to a concrete $(A, B)$. This is why W-types are a useful *specification* for what your kernel's inductive-type checker must produce, even if you never implement W-types themselves.
- **Strict positivity.** The occurrence of the W-type in the codomain of $f : B(a) \to \mathsf{W}$ is exactly the positive position the checker has to enforce. The book discusses this in §5.6, not in §5.3, so treat the link as a pointer rather than something this section proves.
- **Rust grounding.** The `fold` above is the non-dependent recursor and is the template for a generated `match`-based eliminator. The dependent version has no direct Rust counterpart, which is a fair indicator that the kernel's recursor must live in your term language, not be borrowed from the host language.

The section has no proof-search or solver content, so no `automated-reasoning`, `sat-smt-csp` or `static-analysis` connection is claimed.
