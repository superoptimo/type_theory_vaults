---
title: "Dependent Types"
book: "04_TAPL_Pierce_2002"
chapter: "Chapter 30, §30.5 \"Going Further: Dependent Types\""
pages: "462-466"
tags: [type-theory, dependent-types, pi-types, logical-frameworks, propositions-as-types, curry-howard, TAPL]
---

[[book-guidelines|↩ Back to guidelines]]

# Dependent Types

## The one combination TAPL hasn't used yet

Chapter 30 spends four sections (30.1–30.4) building $F^\omega$ and then, in its last two pages of actual content, steps back and points at something it deliberately does *not* build. That's an unusual move for a book this careful, and the way it sets up the gap is worth taking seriously before looking at the gap itself.

Pierce's framing: every abstraction mechanism introduced so far is a way of describing a *family of expressions, indexed by other expressions*. An ordinary function $\lambda x{:}T_1.t_2$ is a family of terms, one for every term $s$ you could substitute for $x$ — write it $[x \mapsto s]t_2$ and you get a different term for every $s$. A type abstraction $\lambda X{::}K_1.t_2$ (System F, Chapter 23) is the same idea one level up: a family of terms indexed by *types* rather than terms — plug in `Nat`, get one term; plug in `Bool`, get another. And a type operator $\lambda X{::}K_1.T_2$ ($\lambda^\omega$, Chapter 29) is a family of *types* indexed by types — `Pair` is a different type for every pair of types you apply it to.

$$
\begin{array}{lll}
\lambda x{:}T_1.t_2 & \text{family of \emph{terms}, indexed by \emph{terms}} & (\lambda_\to,\ \text{Ch. 9})\\
\lambda X{::}K_1.t_2 & \text{family of \emph{terms}, indexed by \emph{types}} & (\text{System F, Ch. 23})\\
\lambda X{::}K_1.T_2 & \text{family of \emph{types}, indexed by \emph{types}} & (\lambda^\omega,\ \text{Ch. 29})
\end{array}
$$

Lay these three out and the fourth cell of the table is conspicuously empty: a family of **types**, indexed by **terms**. That's the whole content of "dependent types" as a slogan — not a new *kind* of abstraction, but the one entry in an otherwise-completed $2\times2$ grid that the book has been avoiding. And the reason it's been avoided isn't oversight; TAPL is explicit that this cell buys real expressive power at a real computational cost, and spends the section explaining both sides honestly rather than building the system out (this is, refreshingly, a place where the book tells you what it's *not* going to formalize, and why).

## Types indexed by terms: the motivating example

Suppose a language has a built-in `FloatList` type with the usual operations:

$$
\begin{aligned}
\texttt{nil} &: \texttt{FloatList}\\
\texttt{cons} &: \texttt{Float} \to \texttt{FloatList} \to \texttt{FloatList}\\
\texttt{hd} &: \texttt{FloatList} \to \texttt{Float}\\
\texttt{tl} &: \texttt{FloatList} \to \texttt{FloatList}\\
\texttt{isnil} &: \texttt{FloatList} \to \texttt{Bool}
\end{aligned}
$$

This is a perfectly ordinary simply-typed interface, and it is also uninformative in a specific way: nothing in the *type* `FloatList` tells you the length of the list you're holding, so `hd`/`tl` must be partial (undefined on `nil`) and every caller needs a runtime `isnil` check before touching either. **What breaks without dependent types** is exactly this: the type system cannot express "this operation is only defined for non-empty [[Recursive-Types#Lists|lists]]," so that invariant either gets enforced by a runtime check (as here) or not at all.

Dependent types let you refine `FloatList` into a *family* `FloatList n` — one type per natural number `n`, the type of lists of exactly `n` elements. `nil` gets the precise type `FloatList 0`. The interesting move is `cons`: its result type depends on the length of the list it's given, and that dependency has to be *named* to be expressed. TAPL introduces exactly the notation needed for this:

$$
\Pi n{:}\texttt{Nat}.\ T
$$

read as "for each term $n$ of type `Nat`, a value of type $T$" — where, critically, $T$ is allowed to *mention* $n$. This is the **dependent function type**, and TAPL is careful to frame it as a generalization, not a replacement, of the ordinary arrow: $\Pi x{:}T_1.T_2$ is a more precise arrow $T_1 \to T_2$, in which the argument gets a name so the result type can refer to it. In the degenerate case where $T_2$ doesn't mention $x$ at all, $\Pi x{:}T_1.T_2$ *is* $T_1 \to T_2$ — so every ordinary function type is a dependent function type that happens not to use the dependency.

With $\Pi$ in hand, the whole interface gets sharpened:

$$
\begin{aligned}
\texttt{nil} &: \texttt{FloatList}\ 0\\
\texttt{cons} &: \Pi n{:}\texttt{Nat}.\ \texttt{Float} \to \texttt{FloatList}\ n \to \texttt{FloatList}\ (\texttt{succ}\ n)\\
\texttt{hd} &: \Pi n{:}\texttt{Nat}.\ \texttt{FloatList}\ (\texttt{succ}\ n) \to \texttt{Float}\\
\texttt{tl} &: \Pi n{:}\texttt{Nat}.\ \texttt{FloatList}\ (\texttt{succ}\ n) \to \texttt{FloatList}\ n
\end{aligned}
$$

Read `cons`'s type left to right: take a number $n$, a `Float`, and a list of length exactly $n$; return a list of length exactly $\texttt{succ}\ n$. `hd` and `tl` now *require* their argument to have type `FloatList (succ n)` for some $n$ — i.e., to be provably non-empty — so `isnil` disappears entirely as a runtime primitive: to know whether a `FloatList n` is empty, ask the typechecker whether $n = 0$. The runtime check has moved into the type, checked once, statically, instead of on every access.

TAPL then shows a function actually inhabiting one of these dependent types, to make the point concrete:

$$
\texttt{consthree} = \lambda n{:}\texttt{Nat}.\ \lambda f{:}\texttt{Float}.\ \lambda l{:}\texttt{FloatList}\ n.\ \texttt{cons}\ (\texttt{succ}(\texttt{succ}\ n))\ f\ (\texttt{cons}\ (\texttt{succ}\ n)\ f\ (\texttt{cons}\ n\ f\ l))
$$

with type $\Pi n{:}\texttt{Nat}.\ \texttt{Float} \to \texttt{FloatList}\ n \to \texttt{FloatList}\ (\texttt{succ}(\texttt{succ}(\texttt{succ}\ n)))$. Notice that each of the three inner `cons` calls is applied to a *different* natural-number index (`n`, then `succ n`, then `succ(succ n)`) — the term-level arithmetic tracking exactly how the list's length grows is fully explicit and fully checked, because it's living inside the type, not just the value.

TAPL leaves this as a self-contained appetizer and assigns generalizing it (§30.5.1) as an exercise: fix `FloatList` to `List T` for an arbitrary type operator argument `T`, combining this section's term-indexing with $\lambda^\omega$'s type-indexing. The book doesn't work the exercise itself — a sign of how far it intends to develop the mechanism here.

### Grounding: length-indexed lists in Lean, Rust, and Python

**Lean** is the most literal translation available, because Lean's `Vector` type (and the standard demonstration of dependent types in any dependently-typed language) *is* this exact example, with `Nat` indices baked into the type by a $\Pi$-type under the hood:

```lean
-- Lean's own indexed-vector type is essentially FloatList reified
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

-- `cons`'s constructor signature IS TAPL's Πn:Nat. type, spelled with Lean's
-- implicit-argument binder {n : Nat} standing in for the explicit Πn:Nat.
def head : Vec α (n + 1) → α
  | Vec.cons x _ => x
-- `head Vec.nil` is a TYPE ERROR, not a runtime crash: `Vec.nil : Vec α 0`
-- does not unify with the expected argument type `Vec α (n + 1)` for any n.
```

This is precisely the payoff TAPL describes in words: `head` on an empty vector doesn't need to be partial or checked at runtime, because `Vec α 0` and `Vec α (n+1)` are *never* unifiable, for any $n$ — the typechecker rejects the ill-typed call before the program runs. Lean's kernel is doing exactly the definitional-equality check that $\Pi$-types demand: to accept `Vec.cons x xs : Vec α (n+1)` as an argument where `Vec α (m+1)` is expected, it must check `n + 1` and `m + 1` are the same *term*, via the same $\beta$/$\delta$-reduction machinery this book has used throughout for type equivalence — the only difference from $F^\omega$'s type-level equivalence (§30.3) is that the things being compared for equality now live at the *term* level, embedded inside a type index.

**Rust** cannot express this exactly — Rust has no general $\Pi$-type — but const generics get you a fixed-size version of the same idea, which is exactly the right place to feel what dependent types add beyond it:

```rust
// Const generics index by a compile-time constant, not an arbitrary term —
// this is "types indexed by a restricted sublanguage of terms," not full Π.
struct FloatList<const N: usize> {
    data: [f32; N],
}

impl<const N: usize> FloatList<N> {
    fn cons(x: f32, tail: FloatList<N>) -> FloatList<{ N + 1 }> { /* ... */ }
}

fn head<const N: usize>(l: &FloatList<N>) -> f32 where [(); N - 1]: Sized {
    l.data[0]
    // The `where` bound is the tell: Rust can't say "N is provably > 0"
    // directly, so it leans on `N - 1` typechecking (which panics/fails
    // to compile for N = 0 in const-eval) as a proxy. TAPL's Πn:Nat form
    // states the precondition directly; Rust's const generics simulate it
    // through arithmetic side-effects of the type-level computation.
}
```

The comparison is the point: Rust's const generics are dependent typing's restricted, tractable cousin — indices are compile-time constants, checked by a small closed arithmetic theory, not arbitrary terms of the language. That's not a limitation stumbled into by accident; it's precisely the tradeoff TAPL flags below as the reason production languages restrict dependent types rather than adopting them wholesale.

**Python** has no useful static analogue here at all — its type system, insofar as it's checked before runtime, doesn't track values in types — so the only honest Python illustration is a *runtime* mirror of the invariant, which is worth including specifically to show what gets lost:

```python
class FloatList:
    def __init__(self, items: list[float]):
        self._items = items          # length is a runtime fact, not a type
    def hd(self) -> float:
        if not self._items:          # the check TAPL's Πn:Nat. FloatList(succ n) form
            raise ValueError("hd of empty list")   # eliminates statically
        return self._items[0]
```

This is exactly the pre-dependent-types `FloatList` from the top of the section, `isnil`-style check and all — a faithful sketch of the failure mode, not the fix.

## The two-edged sword: correctness by construction, and why it doesn't come free

TAPL immediately generalizes the pattern: `sort : Πn:Nat. FloatList n → FloatList n` tells you, statically, that sorting preserves length — and, the book notes, if you refine the type family enough (e.g. indexing by *sortedness* as well as length), you could write a `sort` whose type asserts the output is sorted. Checking that some candidate function inhabits that type would then **be** a proof that the function meets its specification. This is the "programs are proofs" picture pushed to its natural conclusion: a constructive proof of "for every $x$ there exists a $y$ such that $P$" is exactly a function from $x$ to $y$, bundled with a certificate that $P(y)$ holds — and dependent $\Pi/\Sigma$-types are precisely rich enough to state that certificate as part of the type itself.

This is a strict generalization of the [[The-Curry-Howard-Correspondence|Curry-Howard correspondence]] this book introduces back in §9.4 for simple types. There, the correspondence is between simple implication ($T_1 \to T_2$) and [[The-Simply-Typed-Lambda-Calculus#Function types|function types]] — propositions with no internal structure beyond "if-then." Dependent function types extend the same idea to *quantified* propositions: $\Pi x{:}T_1.T_2(x)$ reads simultaneously as a type ("a function taking an $x{:}T_1$ and returning a $T_2(x)$") and as a proposition ("for all $x$ of type $T_1$, $T_2(x)$ holds") — universal quantification, not just implication, now has a type-theoretic reading. This "propositions as types, proofs as programs" reading, restated for the dependent case, is the whole content of the section's third subtopic (logical frameworks) below.

But TAPL is unusually blunt about the cost, and this honesty is worth preserving rather than smoothing over: **blurring the line between typechecking and theorem-proving does not make theorem-proving easy — it makes typechecking hard.** Working mathematicians using mechanical proof assistants don't type a theorem and get an instant yes/no; they write proof scripts and tactics, often at great length, to *guide* the tool to a proof. Carried to its limit, correctness-by-construction asks ordinary programmers to do the same: annotate programs with the same kind of guiding detail proof-assistant users supply, an effort TAPL judges justified for safety-critical code and "almost certainly too costly" for everyday programming.

This is the "what breaks without restriction" case *in reverse* — not "what breaks without dependent types" but "what breaks if you adopt them without limit": typechecking stops being a mechanical, always-terminating procedure and becomes, in the worst case, exactly as hard as automated theorem proving in general (undecidable). Every practical dependently-typed system since has had to choose a point on this tradeoff curve. TAPL names the ones known at time of writing, and the pattern across all of them is the same — restrict *which* terms are allowed to appear in types, in exchange for tractable, more-automatable typechecking:

- **Dependent ML** (Xi and Pfenning) and **Dependently Typed Assembly Language** (Xi and Harper) index types only by terms drawn from a decidable *linear arithmetic* fragment — enough to eliminate array-bounds checks statically, not enough to encode arbitrary theorems, so the "theorem proving" the typechecker does is just linear-constraint solving, for which fast decision procedures exist.
- **Module systems with sharing** (Pebble, the ML module systems of MacQueen/Harper/Mitchell/Stone) use dependency at the level of *kinds* ("singleton kinds") to track which modules share which type components, rather than indexing ordinary value types by arbitrary terms.
- **Cayenne** and **Russell** take the opposite bet — full, unrestricted dependent types, accepting that typechecking may not terminate in general.

## Logical frameworks and propositions as types, formalized

The section's final move is to name the *un*-restricted end of this spectrum properly. A simple type system that includes dependent types — full $\Pi$-types, nothing else exotic added — is called a **logical framework**; the canonical example is **LF** (Harper, Honsell, Plotkin), "the pure simply typed calculus with dependent types." LF and its relatives, especially the **calculus of constructions** (Coquand and Huet), are the technical basis of a long lineage of proof assistants and theorem-proving environments TAPL lists by name: AutoMath (the historical first), NuPRL, LEGO, Coq, ALF, ELF. This list is not incidental trivia — it is the direct ancestry of essentially every proof assistant in active use today, including Lean, whose kernel is a descendant of exactly this calculus-of-constructions lineage.

The reason a logical framework is well-suited to *encoding logics themselves*, rather than just typed programs, is the propositions-as-types reading pushed all the way through: a logic's inference rules become type-forming rules, its judgments become type inhabitants, and — the piece that only dependent types add over simple Curry-Howard — its *quantifiers* ($\forall$, $\exists$) become $\Pi$- and $\Sigma$-types. Encoding "prove this formula" as "find a term with this type" turns *proof search* into *program search under a type*, letting a single typechecker (LF's, or the calculus of constructions') double as a proof checker for whatever object logic has been encoded into it — which is exactly why these frameworks are called *logical* frameworks, rather than just dependently-typed programming languages.

## The Barendregt cube: four abstraction axes, eight corners

TAPL closes the chapter by observing that the four forms of abstraction it has now surveyed — plain term abstraction (always present), term abstraction over types (System F's polymorphism), type abstraction over types (type operators, $\lambda^\omega$), and type abstraction over terms (dependent types, this section) — combine independently, in any subset, to produce eight systems. This is the **Barendregt cube** (Barendregt called it the "lambda cube"):

<svg viewBox="0 0 560 380" xmlns="http://www.w3.org/2000/svg" font-family="Georgia, serif" font-size="16">
  <!-- Front face (z = no dependent types): lambda->, F, lambda-omega, F-omega -->
  <!-- Back face (z = + dependent types), offset up-and-right for isometric depth: LF, dot, dot, CC -->
  <!-- front face square -->
  <line x1="90" y1="320" x2="290" y2="320" stroke="#888" stroke-width="1.5"/>
  <line x1="90" y1="320" x2="90" y2="140" stroke="#888" stroke-width="1.5"/>
  <line x1="290" y1="320" x2="290" y2="140" stroke="#888" stroke-width="1.5"/>
  <line x1="90" y1="140" x2="290" y2="140" stroke="#888" stroke-width="1.5"/>
  <!-- back face square, shifted +150 x, -80 y for depth -->
  <line x1="240" y1="240" x2="440" y2="240" stroke="#888" stroke-width="1.5"/>
  <line x1="240" y1="240" x2="240" y2="60" stroke="#888" stroke-width="1.5"/>
  <line x1="440" y1="240" x2="440" y2="60" stroke="#888" stroke-width="1.5"/>
  <line x1="240" y1="60" x2="440" y2="60" stroke="#888" stroke-width="1.5"/>
  <!-- depth edges connecting front to back (the dependent-types axis) -->
  <line x1="90" y1="320" x2="240" y2="240" stroke="#4a90d9" stroke-width="2"/>
  <line x1="290" y1="320" x2="440" y2="240" stroke="#4a90d9" stroke-width="2"/>
  <line x1="90" y1="140" x2="240" y2="60" stroke="#4a90d9" stroke-width="2"/>
  <line x1="290" y1="140" x2="440" y2="60" stroke="#4a90d9" stroke-width="2"/>
  <!-- front face nodes (no dependent types) -->
  <circle cx="90" cy="320" r="5" fill="#d9534f"/>
  <circle cx="290" cy="320" r="5" fill="#d9534f"/>
  <circle cx="90" cy="140" r="5" fill="#d9534f"/>
  <circle cx="290" cy="140" r="5" fill="#d9534f"/>
  <!-- back face nodes (+ dependent types) -->
  <circle cx="240" cy="240" r="5" fill="#5cb85c"/>
  <circle cx="440" cy="240" r="5" fill="#999"/>
  <circle cx="240" cy="60" r="5" fill="#999"/>
  <circle cx="440" cy="60" r="5" fill="#5cb85c"/>
  <!-- labels -->
  <text x="35" y="345" fill="currentColor">λ→</text>
  <text x="300" y="345" fill="currentColor">F</text>
  <text x="35" y="130" fill="currentColor">λω</text>
  <text x="300" y="130" fill="currentColor">Fω</text>
  <text x="185" y="262" fill="currentColor">LF</text>
  <text x="450" y="245" fill="#999">·</text>
  <text x="185" y="55" fill="#999">·</text>
  <text x="450" y="50" fill="currentColor">CC</text>
  <!-- axis labels -->
  <text x="110" y="375" fill="#d9534f" font-size="13">right: term abstraction over types (polymorphism)</text>
  <text x="20" y="240" fill="#888" font-size="13" transform="rotate(-90 30 240)">up: type abstraction over types (operators)</text>
  <text x="290" y="290" fill="#4a90d9" font-size="13">back: type abstraction over terms (dependent types)</text>
</svg>

Every corner includes ordinary term abstraction — that axis is never optional; it's the shared floor all eight systems stand on. The **front face** (red dots) is exactly the fragment hierarchy from §30.4: $\lambda_\to$ at the origin, $F$ (System F) with polymorphism added, $\lambda^\omega$ with type operators added, $F^\omega$ with both — the whole system Chapter 30 spent four sections actually building, and it has no dependent types anywhere on it. Pushing back along the third axis — the one this section is about — adds dependent types to each: $\lambda_\to$ plus dependent types alone is exactly $LF$ ("the pure simply typed calculus with dependent types," as advertised), and $F^\omega$ plus dependent types, at the far corner where all three axes meet, is the **calculus of constructions** — polymorphism, type operators, and dependent types simultaneously, the most expressive and least automatically-checkable point on the cube. TAPL leaves the two remaining corners (dependent types + polymorphism only; dependent types + operators only) unlabeled, since neither is a system it discusses elsewhere. In closing, TAPL notes that the cube's eight systems are themselves a special case of a still more general uniform presentation, **pure type systems**, which parametrize the whole design space by a small set of combinatorial choices rather than enumerating corners by hand.

## Where this leads

Within TAPL itself, this section is explicitly a *survey*, not a foundation the rest of the book builds on — no later TAPL chapter formalizes $\Pi$-types or proves a preservation/progress theorem for a dependent calculus, and the sibling article on [[Higher-Order-Polymorphism-(System-F-omega)|System $F^\omega$]] only needs the Barendregt cube's shape to locate $F^\omega$ relative to LF and CC, not this section's formal content. Structurally, dependent types are the fourth cell of the family-indexing table that $\lambda_\to$, System F, and $\lambda^\omega$ jointly complete — so everything upstream (substitution, the shape of typing judgments, the idea of a type-equivalence relation from §30.3) is a direct prerequisite for reading *any* treatment of $\Pi$-types elsewhere, even though TAPL itself stops short of building one.

For the standing elaborator/unifier project, this section is unusually load-bearing despite its brevity: a real dependently-typed elaborator (Lean's kernel among them) is doing, at every step, exactly the definitional-equality check on term-level indices that the `Vec.cons`/`head` example above turns on — `isDefEq` deciding whether two type indices reduce to the same term is the mechanism that makes or breaks whether `head` type-checks. Understanding *why* that check is the hard part (undecidable in general, tractable only once you restrict which terms may appear as indices, as DML/DTAL do) is the direct lesson to carry into building a smaller, purpose-built elaborator: pick your restricted index language deliberately, the way DML picks linear arithmetic, rather than accidentally inheriting full undecidability. For the Rust verifier target, the const-generics comparison above is the honest scoping question to keep asking: every time a checked precondition looks like it wants a $\Pi$-type, the practical choice is not "add full dependent types" but "which decidable index theory (arithmetic, as in DML; or refinement predicates, as in later refinement-type systems) is expressive enough for this specific contract" — precisely the tradeoff this section spends its second half making explicit.
