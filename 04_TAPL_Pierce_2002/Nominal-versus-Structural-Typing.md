---
title: Nominal versus Structural Typing
book: Types and Programming Languages (Pierce, 2002)
chapter: "Chapter 19 — Case Study: Featherweight Java"
pages: pp. 247–264
tags: [type-theory, tapl, featherweight-java, nominal-typing, structural-typing, subtyping, object-encodings]
---

[[book-guidelines|↩ Back to guidelines]]

## The question Chapter 19 is really asking

Every calculus in the first eighteen chapters of TAPL shares a habit you've probably stopped noticing: types are *structures*, and names for them are just clipboard shortcuts. When Pierce writes

$$\texttt{NatPair} = \{\texttt{fst}:\texttt{Nat}, \texttt{snd}:\texttt{Nat}\}$$

`NatPair` isn't a new thing — it's a label you could delete everywhere and replace with the record type it stands for, and nothing in the formal system would notice. [[Subtyping|Subtyping]] between two record types is decided by comparing their *fields*, never their names.

Java doesn't work that way, and neither does most of the software you've actually shipped. If you write `class Pair extends Object { Object fst; Object snd; ... }`, the type `Pair` is not shorthand for a record shape — it is a freestanding entity that exists because *you declared it to exist*, and it is a subtype of `Object` only because you wrote `extends Object`, not because anyone compared field [[Recursive-Types#Lists|lists]]. Two classes with byte-for-byte identical fields and methods, one declared `extends Shape` and the other with no relation declared at all, are unrelated types as far as the compiler is concerned.

That's the whole topic in one sentence: **is "being a subtype" a fact about a type's declared name, or a fact about its structure?** Chapter 19 answers by building Featherweight Java (FJ) — a stripped-down formal core of Java — specifically to give this distinction (§19.3, "Nominal and Structural Type Systems") a rigorous home, and then works through how nominal typing changes classes, casts, and even what "encoding an object" means.

**What breaks without this distinction being made explicit:** if you tried to give Java's type system the same *structural* subtyping TAPL used for records in Chapter 15, you'd get a language where any two classes with matching method signatures become interchangeable — including classes the original authors never intended to be related. Java's designers wanted the opposite guarantee: a `Fahrenheit` wrapper and a `Celsius` wrapper, even with identical internal `double` fields, must never accidentally satisfy each other's type. Nominality buys you that; pure structural subtyping would take it away.

## Two ways to decide "is A a subtype of B?"

### Structural: read the shapes

Under structural typing (everything up through Chapter 18), the subtype relation $S <: T$ is a *derived* fact — computed from the internal shape of $S$ and $T$. For records, width/depth/permutation subtyping (§15.2) says $S <: T$ if $S$'s fields are a superset of $T$'s, with each field's type in the right subtype relation. A type is fully "self-describing": handed the type expression alone, with no other context, you can decide subtyping questions about it. Rust's trait bound system is the closest thing you already know to this instinct, but not quite the mechanism — more on that below.

### Nominal: read the declaration graph

Under nominal typing, $C <: D$ holds only if that fact was *asserted*, directly or transitively, by a chain of `extends` declarations recorded in the class table. Figure 19-1 gives it as an inference system over class names:

$$
\dfrac{}{C <: C} \qquad\qquad \dfrac{C <: D \quad D <: E}{C <: E} \qquad\qquad \dfrac{\mathrm{CT}(C) = \texttt{class } C \texttt{ extends } D \{\ldots\}}{C <: D}
$$

Reflexivity and transitivity are the only "structural" ingredients — everything else bottoms out in a lookup into $\mathrm{CT}$, the class table, which is a global, mutable (at compile time) mapping from names to declarations. Note what's *not* here: no rule inspects the fields or methods of $C$ and $D$ to decide the relation. You cannot answer "$C <: D$?" from $C$ and $D$ alone — you need the whole program's class table. That's the "verbose" cost Pierce flags directly (p. 254): a nominal type is not a closed, self-contained expression the way a structural one is; it's an index into a global declaration set.

```rust
// Rust's trait objects and structs are nominal in the same sense Java classes are:
// impl relations are declared, not inferred from shape.
struct Fahrenheit(f64);
struct Celsius(f64);

trait Temperature { fn to_kelvin(&self) -> f64; }

impl Temperature for Fahrenheit {
    fn to_kelvin(&self) -> f64 { (self.0 - 32.0) * 5.0/9.0 + 273.15 }
}
// Celsius does NOT automatically satisfy `Temperature` just because it could —
// you must write `impl Temperature for Celsius { ... }` yourself.
// Structural duck typing would let any single-f64-field type through; Rust, like FJ,
// requires the declaration.
```

This is exactly the "spurious subsumption" defense Pierce names on p. 253: nominal systems (and Rust's trait-impl requirement, though Rust is really structural-plus-coherence rather than classically nominal) prevent two types that merely *happen* to share a shape from silently becoming interchangeable.

## Featherweight Java: the calculus built to make this precise

FJ is designed with an almost obsessive minimalism (p. 247): five term forms only — variable, field access, method invocation, object creation, cast — no assignment, no interfaces, no `super` calls outside constructors, no exceptions, no primitive types. Pierce is explicit about the tradeoff: every feature that would lengthen the safety proof without changing its *character* was cut. What's left is small enough that "syntax, typing rules, and [[Operational-Semantics|operational semantics]] fit comfortably on a single letter-sized page," yet expressive enough to be a genuine, executable subset of real Java — "every FJ program is literally an executable Java program" (p. 248).

### Syntax (Figure 19-1)

$$
\begin{aligned}
\texttt{CL} &::= \texttt{class } C \texttt{ extends } C\ \{\overline{C\ f}; K\ \overline{M}\} &&\text{class declaration}\\
K &::= C(\overline{C\ f})\ \{\texttt{super}(\overline{f}); \texttt{this}.\overline{f}=\overline{f};\} &&\text{constructor (one stylized form only)}\\
M &::= C\ m(\overline{C\ x})\ \{\texttt{return } t;\} &&\text{method}\\
t &::= x \mid t.f \mid t.m(\overline{t}) \mid \texttt{new } C(\overline t) \mid (C)\,t &&\text{terms: var, field access, invoke, new, cast}\\
v &::= \texttt{new } C(\overline v) &&\text{values: fully-evaluated objects}
\end{aligned}
$$

The overbar notation ($\overline{C\ f}$, $\overline{t}$) is Pierce's standard shorthand for sequences (§19.4) — read $\overline{C\ f}$ as "$C_1\ f_1, \ldots, C_n\ f_n$."

A few design choices worth dwelling on because they're where FJ's minimalism does real work:

- **Constructors are entirely mechanical.** A constructor's body is *forced* to be `super(g); this.f=f;` — call the superclass constructor with the inherited fields, then assign the new fields from identically-named parameters. There is no freedom here; the typing rule for classes (`C OK` in Figure 19-4) literally checks the constructor has this exact shape. This is a genuine simplification relative to Java (where you could do arbitrary computation in a constructor), traded away specifically so the safety proof stays small.
- **No assignment anywhere.** FJ is a "functional" fragment of Java (p. 250) — fields are set once, at construction, forever. This means FJ's evaluation needs no heap/store model at all (contrast Chapter 13's references, which needed a store $\mu$ and store typings $\Sigma$ threaded through everything): evaluation is pure term rewriting, just like the untyped lambda-calculus.
- **`this` is a variable, not a keyword** (footnote 1, p. 249) — syntactically ordinary, but implicitly bound in every method body, and substituted for at invocation time.

**What breaks without the "everything is an object" restriction:** Pierce draws the parallel to the lambda-calculus explicitly (p. 250): just as application evaluation assumes the function position has already reduced to a lambda-abstraction, FJ's evaluation rules assume the receiver of a field access, method call, or cast has already reduced to a `new C(...)` value. Drop that invariant (e.g. by allowing evaluation to proceed on an object whose runtime shape is still unknown) and you lose the clean small-step semantics FJ is built around.

### The three computation rules (Figure 19-3)

$$
\dfrac{\mathrm{fields}(C) = \overline{C\ f}}{(\texttt{new } C(\overline v)).f_i \to v_i} \;(\text{E-ProjNew})
\qquad
\dfrac{\mathrm{mbody}(m, C) = (\overline x, t_0)}{(\texttt{new } C(\overline v)).m(\overline u) \to [\overline x \mapsto \overline u,\ \texttt{this} \mapsto \texttt{new } C(\overline v)]\,t_0} \;(\text{E-InvkNew})
$$
$$
\dfrac{C <: D}{(D)(\texttt{new } C(\overline v)) \to \texttt{new } C(\overline v)} \;(\text{E-CastNew})
$$

Field access is pure positional projection — because constructors are stylized, the compiler (and the metatheory) knows exactly which constructor argument corresponds to which field name. Method invocation is a direct analogue of beta-reduction (E-AppAbs): substitute actual arguments for formals, *and* substitute the receiver object for `this` — this is the mechanism supporting both **method override** (which class's `mbody` you look up is determined by the receiver's actual runtime class) and **open recursion through self** (the substituted `this` lets a method call other methods on "the same object," dispatching dynamically). Pierce notes the resemblance to Abadi–Cardelli's $\varsigma$-reduction rule (footnote 2, p. 251) — if you've seen the object calculus, FJ's `E-InvkNew` is its class-based cousin.

Casting is where nominality shows its teeth operationally: `(D)(new C(v))` reduces to `new C(v)` — the cast just vanishes — provided $C <: D$ holds *in the class table*, i.e. is a fact you can look up, not derive from structure. If $C \not<: D$ the term is simply **stuck** — no rule applies, denoting a runtime type error (this is FJ's substitute for Java throwing `ClassCastException`).

```python
# The three FJ reduction rules as one Python-level evaluator sketch —
# illustrative only, not load-bearing (per the workbench grounding preference,
# this is the "five-line sketch," not the real implementation target).
def step(term, class_table):
    match term:
        case FieldAccess(receiver=New(cls, args), f=fname):
            i = fields(cls, class_table).index(fname)
            return args[i]
        case Invoke(receiver=New(cls, args), m=mname, actuals=vs):
            params, body = mbody(mname, cls, class_table)
            subst = dict(zip(params, vs)); subst["this"] = New(cls, args)
            return substitute(body, subst)
        case Cast(target=D, subject=New(cls, args)):
            if is_subtype(cls, D, class_table):
                return New(cls, args)
            raise Stuck(f"{cls} is not a subtype of {D}")
        # ... congruence rules recurse into subterms not yet reduced ...
```

### Typing (Figure 19-4) and the auxiliary lookups (Figure 19-2)

The typing judgment $\Gamma \vdash t : C$ needs four auxiliary, class-table-indexed functions defined in Figure 19-2:

- $\mathrm{fields}(C)$ — the sequence of (type, name) pairs for every field of $C$, inherited chain included, bottoming out at $\mathrm{fields}(\texttt{Object}) = \bullet$ (empty).
- $\mathrm{mtype}(m, C)$ — the argument/result type signature $\overline B \to B$ of method $m$ as seen from $C$, walking up to the superclass if $m$ isn't declared locally.
- $\mathrm{mbody}(m, C)$ — the parameters and body term of $m$ as seen from $C$, same inheritance walk.
- $\mathrm{override}(m, D, \overline C \to C')$ — a *side condition*, not a function returning a value: it holds either if $D$ (and its ancestors) don't define $m$ at all, or if they define it with the *exact same* signature $\overline C \to C'$. This is what stops FJ's Java from silently allowing covariant-return or contravariant-argument overriding — a subclass method with the same name but a different signature is simply ill-formed.

The term-typing rules are unremarkable variants of what you've seen since Chapter 9 — `T-Var`, `T-Field`, `T-Invk`, `T-New` all just chain subtype checks through `<:` — except that `<:` here means "declared nominal subtype," and **there is no subsumption rule** (`T-Sub`) at all. Instead, subtyping checks are threaded directly into the premises of individual rules (`T-Invk` requires each argument's type be `<:` the declared parameter type; `T-New` similarly). This is the *algorithmic* style from §16.1, chosen here not as an optimization over a declarative presentation but because it's forced: full Java itself commits to an algorithmic typing relation (this is even the subject of Exercise 19.4.6, which shows interfaces plus conditional expressions force it).

### Casts: three rules, and the "stupid" one

$$
\dfrac{\Gamma \vdash t_0 : D \quad C <: D}{\Gamma \vdash (C)\,t_0 : C} \;(\text{T-UCast, upcast})
\qquad
\dfrac{\Gamma \vdash t_0 : D \quad C <: D \quad C \ne D}{\Gamma \vdash (C)\,t_0 : C} \;(\text{T-DCast, downcast})
$$
$$
\dfrac{\Gamma \vdash t_0 : D \quad C \not<: D \quad D \not<: C \quad \textit{stupid warning}}{\Gamma \vdash (C)\,t_0 : C} \;(\text{T-SCast, stupid cast})
$$

The distinguishing condition across the three rules is where $C$ (the cast's target) and $D$ (the subject term's static type) sit in the subtype order: **upcast** (`T-UCast`) — target $C$ is a *superclass* of the subject's static type $D$, i.e. $C <: D$ read the other way ($D <: C$... actually the book's premise is $C<:D$ meaning the *result* type $C$ is a supertype reached by going up — concretely: casting `(Object) somePair` widens `Pair` to `Object`, always safe, this is what subsumption would do if FJ had a `T-Sub` rule); **downcast** (`T-DCast`) — target $C$ is a *proper subclass* of the subject's static type $D$ ($C <: D$, $C \ne D$), i.e. narrowing to something more specific, which may fail at runtime — this is the "trust me" cast; **stupid cast** (`T-SCast`) — target and subject's static type are unrelated in *either* direction ($C \not<: D$ and $D \not<: C$). A stupid cast is one no sensible programmer would write and the real Java compiler rejects outright — `(Pair)someString` for unrelated classes `Pair` and `String`.

So why does FJ's *formal* type system accept stupid casts (with a mere "stupid warning" side annotation) when the Java compiler rejects them? This is one of the sharpest, most instructive points in the chapter (§19.4, p. 259):

> a sensible term may be reduced to one containing a stupid cast.

Example, using the trivial classes `A extends Object` and `B extends Object` from §19.2:

$$(A)(\texttt{Object})\,\texttt{new } B() \;\longrightarrow\; (A)\,\texttt{new } B()$$

The *original* term is perfectly well-typed Java (an upcast to `Object` inside a downcast to `A`) — but after one step of reduction, the inner cast evaporates (by `E-CastNew`, since `Object <: Object`... actually since the upcast target matches) and what's left, `(A) new B()`, is a stupid cast: `A` and `B` are unrelated siblings. **If the type system rejected stupid casts outright, type preservation would fail** — a well-typed term would reduce to an ill-typed one, wrecking the very safety theorem Chapter 19 exists to prove. So FJ's designers made a small, deliberate concession: allow stupid casts in the *formal* system (tagged with a `stupid warning` hypothesis you can filter on afterward) purely so preservation goes through cleanly, while noting that "an FJ typing corresponds to a legal Java typing only if it does not contain this rule" (p. 260). This is a small, beautifully concrete illustration of a recurring tension in type-safety metatheory: sometimes the *proof technique* (small-step preservation) forces you to be formally more permissive than the language you're actually modeling, and you patch the gap with a side condition rather than distorting the semantics.

**What breaks without stupid casts:** you'd either have to abandon small-step semantics for FJ (switch to big-step, as Nipkow and Oheimb did for their similar calculus, per the Notes on p. 263) or find some other way to dodge the intermediate ill-typed state — both real design choices other Java-safety papers actually made, cited by Pierce in §19.7.

## Type safety, restated for a nominal, cast-bearing calculus

The safety story is the familiar progress + preservation pattern from Chapter 8 onward, but reshaped by casts:

**Preservation (19.5.1):** if $\Gamma \vdash t : C$ and $t \to t'$, then $\Gamma \vdash t' : C'$ for some $C' <: C$ — note this is *not* "same type," but "a subtype of the original type." A term's type can only get *more precise* as evaluation proceeds (an upcast disappearing, e.g., can make the runtime-visible type narrower than the static type suggested) — this is the same "weakening under evaluation" flavor as elsewhere in the book, adapted to a world where casts can shed static imprecision.

**Progress (19.5.4):** a closed, well-typed term in normal form is either a value, or it's stuck specifically at a failing downcast — formalized via **evaluation contexts** $E$ (Definition 19.5.3), a device that names "the next subterm to be reduced" so the theorem can point precisely at *where* the failure sits inside a larger term, rather than declaring the whole term simply "stuck." This machinery — evaluation contexts as a way to isolate "the redex" inside a large term — is a general technique worth recognizing: it's the same idea used later (and in modern operational-semantics presentations generally) to talk about *where* in a term evaluation is currently happening, without rewriting the whole grammar as a stack machine.

Put together: **a well-typed FJ program containing no downcasts (and no stupid casts) can never get stuck.** Only downcasts introduce genuine runtime risk — exactly matching the intuition every Java programmer already has about `instanceof`/cast-related `ClassCastException`s being the one place static typing "gives up" and defers to a runtime check.

```rust
// The Rust analogue of "safe unless you downcast" is downcasting via Any:
use std::any::Any;

fn handle(obj: &dyn Any) {
    // upcast to &dyn Any is implicit and always safe (like FJ's T-UCast)
    if let Some(pair) = obj.downcast_ref::<Pair>() {
        // downcast_ref is FJ's (C)t: it can fail, and here Rust makes
        // the "stuck" case explicit as None rather than a runtime panic.
        println!("got a Pair");
    }
}
```
Rust makes FJ's "stuck" outcome for a failed downcast into an ordinary, checked `Option` value instead of a language-level stuck state or a thrown exception — arguably the more disciplined resolution of the same tension Pierce is describing.

## Nominal vs. structural: the tradeoffs, made concrete

Pierce runs through this symmetrically (§19.3, pp. 252–254) — it's worth holding both columns in your head at once rather than picking a "winner":

| | Nominal (FJ / Java) | Structural (most of TAPL) |
|---|---|---|
| Subtype fact lives in | the declaration (`extends`), looked up in $\mathrm{CT}$ | the shape of the type itself |
| Type expression is | not self-contained — needs global $\mathrm{CT}$ context | closed — carries its own meaning |
| Runtime type tags | natural: tag = pointer to the compile-time type descriptor | possible but a *separate* mechanism bolted on |
| [[Recursive-Types|Recursive types]] | free — `List` can mention `List` in its own declaration, no bookkeeping | requires real machinery ($\mu$-types, Chapter 20) to avoid infinite unfolding |
| Subtype checking cost | cheap per-check (one lookup up a precomputed chain); the real work (validating declarations) happens once, at definition time | must be recomputed against structure each time, though good implementations cache this (p. 222) |
| Spurious subsumption | prevented — unrelated-but-similar types stay unrelated unless declared otherwise | permitted — anything with a matching shape typechecks, which the field misuse example illustrates |
| Type-level abstraction (generics, ADTs, functors) | awkward — `List(T)` resists being treated as an atomic *name* | natural — this is why the *research* literature skews structural |

Two of these deserve a second look because they cut against the "structural is just more elegant" instinct you might default to:

**Recursive types come free nominally, expensive structurally.** In FJ, class `A`'s declaration can mention `B` in a field or method type while `B`'s declaration mentions `A` back — no special machinery, because names are assumed to exist "from the beginning" independent of the order you declare them (p. 253). In a structural calculus, a genuinely recursive type needs the $\mu$-binder apparatus of Chapter 20 (`fold`/`unfold`, or the coinductive equi-recursive treatment of Chapter 21) precisely *because* a structural type has to be a self-contained expression — and a self-contained expression that refers to itself needs an explicit fixed-point construct to avoid being infinitely large. Pierce is careful to note ML "bundles" this away for programmers (algebraic datatypes give you the ergonomics of nominal recursion on top of a structural core) — but the *foundational* mechanism underneath is still doing real, non-trivial work that FJ's `class` declarations sidestep entirely.

**Why research PL theory still mostly stays structural anyway.** Not (mainly) elegance for its own sake — it's that the field's central objects of study (parametric polymorphism, ADTs, functors, higher-order type operators — everything from Chapters 23 onward) genuinely resist being squeezed into atomic names. `List(T)` "seems irreducibly compound" (p. 254): there's exactly one definition of the `List` constructor, and understanding `List(T)` requires unfolding that definition, which is exactly the structural move. A few languages hybridize (Java generics/GJ being the direct example Pierce cites, footnote-adjacent to the FJ lineage itself), but Pierce is candid that these end up "complex hybrids," not clean extensions of pure nominal typing.

## Encodings versus primitives: closing the loop with Chapter 18

Section 19.6 is short but structurally important: it's Pierce explicitly stepping back to compare **two whole methodologies**, not just two typing disciplines.

- **Chapter 18's approach:** *encode* objects, classes, inheritance, and self out of more primitive ingredients you already have — records, references, subtyping, and a fixed-point operator for open recursion. The payoff is explanatory: you see *why* objects work, because you built them out of parts whose behavior you already understand structurally. It's also the strategy that connects most directly to *compilation* — an encoding is close to what a compiler literally does when it lowers a high-level OO language to closures and vtables.
- **Chapter 19's approach:** take objects, classes, method dispatch, and casting as **primitive** — new syntax, new typing rules, new evaluation rules, defined directly rather than derived. The payoff is design clarity: FJ's rules can be read as a direct specification of Java's intended behavior, with none of the accidental complexity encoding introduces (e.g. Chapter 18 needed a whole detour through thunks and evaluation-order bugs — §18.11 — just to get `self` to work by open recursion via `fix`; FJ's `E-InvkNew` gets the identical effect for free, as one substitution).

Pierce's own synthesis (p. 263) is that the *ideal* is neither alone: a high-level primitive-object language (Ch. 19-style) plus a *provably correct translation* down to a lower-level encoded language (Ch. 18-style), with a theorem that the translation preserves both typing and evaluation behavior. That translation-correctness exercise has actually been carried out for FJ itself (League, Trifonov, and Shao, 2001, cited in §19.6) and for several related object calculi. The chapter frames this less as "which is right" and more as "these are two different, complementary tools for two different jobs" — encodings for understanding *mechanism* and connecting to lower levels, primitives for understanding *intended high-level behavior* and specifying language design.

## Where this leads

Structurally, Chapter 19 is a deliberate detour — a case study, not a link in the book's main technical chain — but it earns its place for two reasons that matter beyond FJ itself. First, it's the book's one moment of confronting *how real, mainstream languages typically diverge from the structural convention the rest of the book assumes* — everything from Chapter 20 (Recursive Types) onward returns to structural systems, but now you understand exactly what nominality would have bought (or cost) at each step, especially for recursive types, which Chapter 20 has to build with real machinery precisely because it stays structural. Second, its closing methodological point (encodings vs. primitives) directly previews Chapters 26/32 ([[Purely-Functional-Object-Encodings|Purely Functional Object Encodings]]), where the book returns to encoding objects — this time via [[Existential-Types|existential types]] and higher-order [[Bounded-Quantification|bounded quantification]] rather than references — reusing exactly the framing §19.6 sets up here.

**On your standing projects:** this chapter is lower-priority scaffolding rather than a direct prerequisite for the Rust verifier or the elaborator — FJ's algorithmic, subsumption-free typing style (no `T-Sub`, subtyping checks threaded into individual rules) is nonetheless a concrete precedent worth remembering for your verifier's typing-rule design: it shows one real, working way to build a syntax-directed judgment form without a separate subsumption step, at the cost of duplicating subtype-check premises across rules. The `mtype`/`mbody`/`fields` auxiliary functions, each defined by walking the class hierarchy with a fallback to the superclass, are also a small, clean example of context-indexed lookup — structurally similar to how a bidirectional elaborator looks up declared signatures from a global environment rather than inferring them locally. Neither connection is load-bearing the way substitution or unification are elsewhere in the book, but both are useful reference points.
