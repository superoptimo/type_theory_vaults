---
title: "The Theory of Expressions"
book: "Programming in Martin-Löf's Type Theory: An Introduction (Nordström, Petersson, Smith, 1990)"
chapter: "Chapter 3, pp. 13–22"
tags: [type-theory, martin-lof, expressions, arities, definitional-equality, syntax, mltt]
---

[[book-guidelines|↩ Back to guidelines]]

# The Theory of Expressions

## Why a logic needs a syntax layer before it needs a logic

Every later chapter of this book states its rules the same way: "if $a$ and $b$ are expressions such that such-and-such, then $\ldots$." Formation rules, introduction rules, elimination rules, [[Propositions-as-Sets-(The-Curry-Howard-Correspondence)#Equality|equality]] rules — all of them are conditions on *expressions*, and all of them lean on one relation between expressions: $\equiv$, definitional (or intensional) equality. Before any of that machinery can be trusted, two much more basic questions have to be settled:

1. What counts as a well-formed expression at all?
2. Given two well-formed expressions, can a machine *decide*, in finite time, whether they are "the same" in the syntactic sense [[Equality-Sets#The rules|the rules]] require?

Chapter 3 answers both, and it does so *before* the book has said a single word about sets, propositions, or judgements. That ordering is deliberate. Martin-Löf's theory of expressions (first given at the Brouwer symposium in 1981, refined in Siena in 1983) is not type-theoretic content — it's a general theory of syntax, abbreviation, and definitional equality that happens to be a prerequisite for type theory, in exactly the way a parser and an AST are a prerequisite for a compiler's type checker. You could use this chapter's machinery to formalize ALGOL 68 programs or predicate-logic formulas; the book does both, as warm-up examples, before ever using it for type theory.

**What breaks without this layer.** If "definitional equality" is left as an informal, "you know it when you see it" notion — the way most programming-language semantics implicitly treat syntactic identity — then a formal system of proof rules cannot be mechanized. Modus ponens,
$$
\frac{A\supset B \qquad A}{B}
$$
==requires checking that the antecedent of the major premise is *the same* $A$ as the minor premise== %%That means that the solver needs to determine that A is the same premise as found in A->B ?? %%. If sameness here isn't decidable, this single rule — the simplest one in the whole system — can't be mechanically verified, and everything built on top of it (formation rules, elimination rules, an actual proof checker) inherits that failure. So the entire book's claim to be implementable rests on what Chapter 3 proves: that its notion of expression and its notion of $\equiv$ are decidable. This is the direct ancestor of `isDefEq` in a real proof assistant's kernel, and it's worth reading this chapter with that translation running in your head throughout.

## Building expressions: four operations, one running example

The chapter's method is instructive on its own: ==rather than starting from a grammar==%%Why Formal verification books start introducing grammar or syntax notation rules? %%, it starts from ordinary mathematical notation and asks what *operations* are implicitly at work in it. Take
$$
y + \sin y.
$$
This is the application of a binary operator $+$ to two arguments, one of which — $\sin(y)$ — is itself the application of a unary operator to $y$. Generalizing, the book writes application of an expression $e$ to arguments $e_1,\ldots,e_n$ as
$$
e(e_1,\ldots,e_n),
$$
so the example becomes $+(y,\sin(y))$, drawn as a syntax tree (the book's Figure 3.1). The `while` loop `while x>0 do x:=x-1; f(x) od` from ALGOL 68 gets the identical treatment: `while(>(x,0), ;(:=(x,-(x,1)), call(f,x)))`. The point of both examples is the same: *any* piece of notation, mathematical or programming-language, can be re-read as a tree of applications once you stop privileging infix/mixfix surface syntax.

**Grounding.** This is precisely what a compiler's AST is, and the correspondence is worth making literal from the start, because the rest of the chapter is really specifying the invariants such an AST has to satisfy.

```rust
// The book's e(e1, ..., en): application of an operator expression
// to a fixed list of argument expressions.
enum Expr {
    Var(VarId),
    Const(ConstId),
    App(Box<Expr>, Vec<Expr>),   // e(e1, ..., en)
    // Abs, Comb, Sel — added below as the chapter introduces them
}
```

In Lean's kernel (`Lean.Expr`), the corresponding constructor is `Expr.app`, curried to binary application (`f x y` is `app (app f x) y`) rather than the book's flat $n$-ary form — a real implementation choice the book leaves open (§3.6 mentions this "shorthand for repeated binary application" as one legitimate reading of $e(e_1,\ldots,e_n)$, alongside the flat-combination reading it actually adopts).

### Abstraction: naming a placeholder, and the first sighting of $\equiv$

$+(y,\sin(y))$ handles application, but not every operator is a fixed constant like $+$ or $\sin$ — some are built on the spot by *abstracting* a variable out of an expression. In
$$
\int_1^x (y+\sin y)\,dy,
$$
the $y$ is a pure placeholder: renaming it to $u$ or $z$ throughout changes nothing about what the integral denotes. The book introduces
$$
(x)e
$$
for "the expression obtained by functional abstraction of the variable $x$ in $e$" — read every free occurrence of $x$ in $e$ as a hole. The integral above becomes $\int\big(((y)+(y,\sin(y))),\,1,\,x\big)$: the integrand is a *unary operator* built by abstracting $y$, and $\int$ is applied to three arguments — that operator and the two bounds.

This is where the chapter earns its title. Once you have both application and abstraction, the same object can be written in more than one syntactic form: an expression $e$ can equally be written $((x)e)(x)$ — abstract $x$ out, then immediately re-apply. The book calls two expressions that are "syntactical synonyms" in this sense **definitionally**, or **intensionally**, **equal**, written with $\equiv$:
$$
e \equiv ((x)e)(x).
$$
Two things about this definition matter more than they might look like they do at first pass. First, $\equiv$ is explicitly *not* about meaning — =="definitional equality is a syntactical notion and has nothing to do with the meaning of the syntactical entities"== (the book's own words). Second, it is going to have to be *decidable*, which is exactly why the rest of the chapter exists: an informal "same up to obviously-equivalent rewriting" relation is not something a checker can implement.

**Grounding.** This distinction — syntactic sameness-up-to-a-fixed-set-of-rules versus semantic sameness — is exactly the line Lean draws between *definitional equality* (`Eq` up to `rfl`, decided by the kernel's `isDefEq`) and *propositional equality* (an `Eq` proof term you have to construct, possibly using `rw`, `simp`, induction, anything). `rfl` succeeds exactly when the kernel's decision procedure for $\equiv$ says the two sides are the same expression by the rules this chapter is about to lay out — nothing more.

```lean
example : 2 + 2 = 4 := rfl        -- kernel reduces both sides to the same normal form: ≡
example (n : Nat) : n + 0 = n := rfl        -- true by the *definition* of +, no induction needed
example (n : Nat) : 0 + n = n := by induction n <;> simp  -- NOT rfl: needs a real proof
```
The last line is the sharpest illustration of $\equiv$'s limits: $n+0\equiv n$ definitionally (by how `+` is defined by recursion on its second argument), but $0+n\equiv n$ is *not* definitionally true — it's only propositionally true, provable by induction. That gap between "true by unfolding definitions" and "true but requiring a proof" is exactly the gap this chapter is drawing between $\equiv$ and everything the rest of the book calls a proposition.

### Combination and selection: tuples and their projections, as primitive syntax

Application handles operators applied to a fixed argument list. But the book also wants to talk about combined objects that are *not* being applied to anything — an ordered pair, an ordering $\langle A,\le\rangle$, a finite-state machine $\langle S,s_0,\Sigma,\delta\rangle$. Rather than treat these as instances of some `Pair`/`Tuple` constant (which would just push the question back a level — what's the arity of `Pair`?), the book introduces **combination** as a third primitive syntactic operation in its own right:
$$
e_1, e_2, \ldots, e_n
$$
and its inverse, **selection**:
$$
(e).i \equiv e_i \quad\text{when } e = (e_1,\ldots,e_n).
$$
This is a real design decision, flagged explicitly in §3.3: you *could* treat $e(e_1,\ldots,e_n)$ as shorthand for repeated binary application, or treat $n$-ary application as a primitive with no separate combination notion — the book picks a third route, giving combination its own syntactic status, distinct from application, because later chapters need dependent tuples ($\Sigma$-types) whose components can't be uniformly modeled as "a function applied to arguments."

§3.5 briefly introduces **named combinations**, $i_1:e_1,\ldots,i_n:e_n$, selected by name rather than position — record syntax, essentially — but the book explicitly declines to develop it further ("we will not need combinations with named components in this monograph"). Worth noting anyway: this is the shape modules and abstract data types will eventually take in Chapter 23 (a dependent tuple *is* a combination), so the positional form pulls real structural weight even though the named variant stays dormant.

**Grounding.** Combination-and-selection is a tuple with projections, and it's worth building it as a genuinely separate `Expr` variant rather than folding it into application, exactly because the book does:

```rust
enum Expr {
    Var(VarId),
    Const(ConstId),
    App(Box<Expr>, Vec<Expr>),
    Abs(VarId, Box<Expr>),          // (x)e
    Comb(Vec<Expr>),                // e1, ..., en
    Sel(Box<Expr>, usize),          // (e).i   — 1-indexed, as in the book
}
```

In Lean's `Expr`, this is `Expr.proj` — a genuinely separate constructor from `Expr.app`, used for structure projections (`.1`, `.fst`, `h.left`), and the kernel's `isDefEq` has dedicated logic for it (including a projection/constructor computation rule and a *structure-eta* rule — you'll meet both again below, because the book has exact analogues). A Python sketch of the whole four-operation grammar, just to see it as a plain recursive datatype without Rust's ceremony:

```python
class Var:  __match_args__ = ("name",)
class Const: __match_args__ = ("name",)
class App:  __match_args__ = ("op", "args")      # e(e1, ..., en)
class Abs:  __match_args__ = ("var", "body")     # (x)e
class Comb: __match_args__ = ("parts",)          # e1, ..., en
class Sel:  __match_args__ = ("expr", "i")       # (e).i
```

## The trouble with no restrictions: self-application

Section 3.6 opens with the "obvious" next move: let expressions be built from variables and primitive constants by application, abstraction, combination, and selection, with *no further restriction* — exactly the analysis Church and Curry used for combinatory logic. The book then spends a paragraph showing why this is a trap.

Two failure modes, one syntactic and one semantic:

- **Syntactic nonsense becomes expressible.** With no restriction, nothing stops you from writing $succ(succ)$ — applying the successor function to *itself*, even though $succ$ is meant to take one argument and return one result, and "itself" is not [[Natural-Numbers-and-Lists|a natural number]]. Nothing stops you from selecting the fifth component of a pair, either.
- **Self-application makes definitions non-eliminable.** This is the deeper problem. With the $\beta$-rule for abstraction,
$$
((x)d)(a) \equiv d[x:=a],
$$
you can write the self-application term $((x)x(x))\big((x)x(x)\big)$ and watch it fail to normalize:
$$
((x)x(x))((x)x(x)) \equiv \underbrace{((x)x(x))((x)x(x))}_{\text{same expression}} \equiv \cdots
$$
The reduction loops forever, revisiting the exact same syntactic form. And Church's own result on combinatory logic says that once expressions are analyzed this unrestrictedly, definitional equality of two arbitrary expressions is not decidable — full stop. That kills the plan from the previous section: without decidable $\equiv$, Modus Ponens (and every other rule) can't be mechanically checked.

**Why self-application specifically is the culprit, spelled out.** It's worth pushing on *why* $x(x)$ is the offending pattern, because the book's fix (arities, next section) makes the most sense once you see this. For $x(x)$ to be a well-formed application, $x$ has to simultaneously play two roles: the *operator* position, which demands $x$ have some "function-shaped" classification (call it $\alpha\to\beta$, the argument-type paired with a result-type), and the *operand* position, which demands $x$ have exactly the argument-type $\alpha$. So $x$'s single classification would have to satisfy $\alpha\to\beta = \alpha$ — the classification would have to be a proper part of itself. If classifications are required to be finite, well-founded trees (which is exactly what an inductive definition like the one about to appear gives you), no such $\alpha$ exists, and $x(x)$ is simply never well-formed in the first place. The divergence never gets a chance to happen, because the offending term never parses.

If that reasoning feels familiar, it should: it's the same "occurs check" argument that stops a first-order unification algorithm from building an infinite term by solving $X \doteq f(X)$. Ruling out $x(x)$ by finite-classification is unification's occurs-check, one level up, applied to the syntax of expressions themselves rather than to metavariables during elaboration — the same shape of argument will resurface, named explicitly, whenever this book series gets to unification and elaboration.

## Arities: a discipline against self-application

The fix, credited back to Frege, is to associate an **arity** with every expression — a syntactic classification of "what shape of expression this is," independent of and prior to anything about sets or types. This is worth sitting with, because it is easy to conflate with the type theory the book is about to build: **arities are not the sets/types of Chapters 5 onward.** They're a much smaller, purely syntactic discipline that exists only to keep the *expression layer* well-formed — closer to how a compiler's parser enforces "an `if` needs a condition and two arms" than to how its type checker later enforces "the condition must be `bool`." Arities get decided once, structurally, before a single semantic rule has been stated. Definition 1, verbatim in shape:

> **Definition 1 (Arities).**
> 1. $0$ is an arity — the arity of a *single, saturated* expression (nothing more can be applied to it or selected from it).
> 2. If $\alpha_1,\ldots,\alpha_n$ ($n\ge 2$) are arities, then $(\alpha_1\otimes\cdots\otimes\alpha_n)$ is an arity — the arity of a *combined* expression with $n$ components.
> 3. If $\alpha$ and $\beta$ are arities, then $(\alpha\to\beta)$ is an arity — the arity of an *unsaturated* expression that can be applied to an argument of arity $\alpha$ to yield an expression of arity $\beta$.

Two arities are equal exactly when they are syntactically identical (no computation here — this is the base case the rest of the machinery is built on top of). Precedence: $\to$ binds looser than $\otimes$, so $0\to 0\otimes 0$ parses as $(0\to(0\otimes 0))$.

| Expression | Arity |
|---|---|
| $y$, $x$, $1$ | $0$ |
| $\sin$, $succ$ | $0\to 0$ |
| $+$ | $0\otimes 0\to 0$ |
| $\int$ | $((0\to 0)\otimes 0\otimes 0)\to 0$ |
| $\sin(y)$, $+(y,\sin(y))$, $succ(x)$ | $0$ |
| $(y)+(y,\sin(y))$ | $0\to 0$ |

With arities in hand, $succ(succ)$ is simply rejected: $succ$ has arity $0\to 0$, so it can only be applied to an expression of arity $0$; $succ$ itself has arity $0\to 0 \ne 0$. Likewise $succ(x)(x)$ — $succ(x)$ has arity $0$, which is saturated, so nothing at all can be applied to it. Both failures are caught by inspecting the arity tree alone, with zero evaluation.

This is a genuinely finite, inductively-defined space (Definition 1's three clauses are exactly a BNF grammar), which is exactly why it's decidable to check and exactly why $x(x)$ has no solution — there is no finite arity $\alpha$ with $\alpha = \alpha\to\beta$, by structural induction on Definition 1 itself.

**Grounding.** This is close to a miniature simply-typed lambda calculus living *underneath* the object language, checked before anything about the book's actual type theory gets involved:

```rust
#[derive(Clone, PartialEq, Debug)]
enum Arity {
    Base,                       // 0
    Product(Vec<Arity>),        // (a1 ⊗ ... ⊗ an), n >= 2
    Arrow(Box<Arity>, Box<Arity>),  // (a -> b)
}

fn arity_of(e: &Expr, ctx: &ArityCtx) -> Result<Arity, ArityError> {
    match e {
        Expr::Var(x)   => ctx.lookup_var(x),
        Expr::Const(c) => ctx.lookup_const(c),
        Expr::App(op, args) => {
            let mut cur = arity_of(op, ctx)?;
            for a in args {
                let a_arity = arity_of(a, ctx)?;
                match cur {
                    Arity::Arrow(want, result) if *want == a_arity => cur = *result,
                    _ => return Err(ArityError::NotApplicable),
                }
            }
            Ok(cur)
        }
        Expr::Abs(x, body) => {
            let alpha = ctx.lookup_var(x)?;
            let beta = arity_of(body, ctx)?;
            Ok(Arity::Arrow(Box::new(alpha), Box::new(beta)))
        }
        Expr::Comb(parts) => {
            let arities: Result<Vec<_>, _> = parts.iter().map(|p| arity_of(p, ctx)).collect();
            Ok(Arity::Product(arities?))
        }
        Expr::Sel(e, i) => match arity_of(e, ctx)? {
            Arity::Product(parts) if *i >= 1 && *i <= parts.len() => Ok(parts[*i - 1].clone()),
            _ => Err(ArityError::BadSelection),
        },
    }
}
```

Feed this `App(succ, vec![succ])` and it returns `Err(NotApplicable)` before any notion of "value" or "evaluation" exists — exactly the guarantee Chapter 3 is after. This is also the layer your Rust verifier's AST needs *first*, ahead of full dependent-type checking: arity-checking is a cheap, total, structural pass that rejects a whole category of ill-formed terms (wrong argument counts, out-of-range projections, self-application) before the expensive elaboration/unification machinery ever runs on them. It's the AST-validity pass, not the type-checking pass — and the book is explicit that the two are different jobs, done at different times, with arities settled first.

In Lean, there is no separate "arity-checking" phase with its own datatype, because Lean's `Expr` already bakes well-scopedness in structurally: `Expr.app` always takes exactly one function and one argument (curried, so $n$-ary application is $n$ nested `app`s, each individually well-formed by construction), `bvar` indices are checked against binder depth, and `proj` carries an explicit structure name and field index checked against that structure's declared field count. What the book does with an explicit `Arity` type and Definition 1, Lean's kernel does implicitly through the shape of the `Expr` inductive type itself plus a scope-checking pass — same job (rule out ill-formed asymmetric applications and out-of-range projections structurally, before semantic type checking), different implementation choice (explicit classification type vs. baked into the term representation).

## Definitions: definiendum and definiens

Section 3.7 is short but structurally important: it licenses **abbreviatory definitions** (macros),
$$
c \equiv e,
$$
where $c$ is a fresh identifier and $e$ a closed expression (no free variables). The left-hand side $c$ is the **definiendum**; the right-hand side $e$ is the **definiens**. The book immediately introduces the curried-parameter shorthand it will use constantly from here on:
$$
c(x_1,\ldots,x_n) \equiv e \quad\text{abbreviates}\quad c \equiv (x_1,\ldots,x_n)e.
$$
This one clause is what makes $\equiv$ do double duty for the rest of the book: it's simultaneously "these two expressions are syntactic synonyms" (the $((x)e)(x)$ sense from §3.2) *and* "this new name unfolds to this definition" (the macro sense here). Both readings get folded into a single equality rule in §3.9 — "if $a$ is a definiendum with definiens $b$, then $a\equiv b$" — precisely because both are the same kind of fact: two spellings of one object.

**Grounding — this is delta-reduction, named explicitly.** In any kernel with a notion of `def`, unfolding a defined constant to its body is exactly this rule, and it is usually literally called *delta-reduction* ($\delta$) in the literature, sitting alongside $\beta$ and $\eta$ as one of the reduction rules a definitional-equality checker must perform. Lean:

```lean
def double (n : Nat) : Nat := n + n

example : double 3 = 3 + 3 := rfl   -- unfolds `double` (delta) then normalizes: definiendum ≡ definiens
```
`rfl` here succeeds by unfolding `double` — exactly the book's "$a$ is a definiendum with definiens $b$, therefore $a\equiv b$" — and then checking the results are the same by the remaining rules below. Every `def` you write in Lean, and every named function in a compiler's constant table, is an instance of the definiendum/definiens pattern this section formalizes.

## The formal grammar: seven clauses for "expression of arity $\alpha$"

Section 3.8 restates everything above as a single inductive definition — a fully precise BNF-with-side-conditions for "$e$ is an expression of arity $\alpha$," which the book writes $e:\alpha$:

1. **Variables.** $x$ a variable of arity $\alpha$ $\implies$ $x:\alpha$.
2. **Primitive constants.** $c$ a primitive constant of arity $\alpha$ $\implies$ $c:\alpha$.
3. **Defined constants.** If the definiens in an abbreviatory definition has arity $\alpha$, so does the definiendum.
4. **Application.** $d:\alpha\to\beta$ and $a:\alpha$ $\implies$ $d(a):\beta$.
5. **Abstraction.** $b:\beta$, $x$ a variable of arity $\alpha$ $\implies$ $((x)b):\alpha\to\beta$.
6. **Combination.** $a_1:\alpha_1,\ldots,a_n:\alpha_n$ ($n\ge 2$) $\implies$ $(a_1,\ldots,a_n):\alpha_1\otimes\cdots\otimes\alpha_n$.
7. **Selection.** $a:\alpha_1\otimes\cdots\otimes\alpha_n$, $1\le i\le n$ $\implies$ $(a).i:\alpha_i$.

Every one of these seven clauses is a one-to-one match against a variant of the `Expr` enum built up over the last few sections, and clause 4's binary form is exactly the fold performed inside `arity_of`'s `App` case above. This is worth noticing explicitly: the book is not being informal here — Section 3.8 *is* the formal grammar a parser/arity-checker implements, stated as inference rules rather than as code.

## Definitional equality, formally: fifteen rules in four families

Section 3.9 gives fifteen numbered rules for $a\equiv b:\alpha$ ("$a$ and $b$ are equal expressions of arity $\alpha$"). Read as a flat list they're a lot to hold at once, but they fall cleanly into four families, and naming the families is what makes the list legible — and, not coincidentally, is exactly how a real `isDefEq` implementation is structured internally.

**Base cases (rules 1–3).** Every atomic expression is equal to itself, and a definiendum is equal to its definiens:
$$
x\equiv x:\alpha \qquad c\equiv c:\alpha \qquad a\equiv b:\alpha \ \text{(if $a$ is a definiendum with definiens $b$)}.
$$

**Congruence rules (4, 6, 9, 11) — equality propagates through structure.** If the pieces are equal, the wholes built the same way are equal:
$$
\frac{a\equiv a':\alpha\to\beta \quad b\equiv b':\alpha}{a(b)\equiv a'(b'):\beta} \qquad\text{(Application 1)}
$$
$$
\frac{x:\alpha \quad b\equiv b':\beta}{(x)b\equiv (x)b':\alpha\to\beta} \qquad\text{(Abstraction 1, the $\xi$-rule)}
$$
plus the analogous rules for combination (rule 9) and selection (rule 11). These are the rules that let you build equal wholes from equal parts — the recursive-descent backbone of any equality checker.

**Computation rules (5, 10) — the actual "doing something" rules.**
$$
((x)b)(a) \equiv b[x:=a] : \beta \qquad\text{(Application 2, the $\beta$-rule)}
$$
"provided that no free variable in $a$ becomes bound in $b[x:=a]$" — i.e., capture-avoiding substitution, stated as an explicit proviso rather than assumed. And the tuple-computation dual:
$$
(e).1,(e).2,\ldots,(e).n \equiv e : \alpha_1\otimes\cdots\otimes\alpha_n \qquad\text{(Combination 2)}
$$
— reassembling all of $e$'s projections gives back $e$ itself. This second rule is exactly what a kernel calls **structure eta**: rebuilding a value out of all of its own projections is definitionally the identity, and it's the direct combination-and-selection analogue of the abstraction-side $\eta$-rule two rules later.

**Binder-management rules (7, 8) — what makes bound variables well-behaved.**
$$
(x)b \equiv (y)(b[x:=y]) : \alpha\to\beta \quad\text{provided $y$ not free in $b$} \qquad\text{(Abstraction 2, the $\alpha$-rule)}
$$
$$
(x)(b(x)) \equiv b : \alpha\to\beta \quad\text{provided $x$ not free in $b$} \qquad\text{(Abstraction 3, the $\eta$-rule)}
$$
The $\alpha$-rule says bound-variable *names* carry no information — $(x)x$ and $(y)y$ are the same expression, just spelled differently. The $\eta$-rule says a function is definitionally equal to the abstraction that just re-applies it — "wrapping and immediately unwrapping" is the identity, function-side, matching Combination 2's tuple-side version exactly.

**Equivalence closure (13–15).** Reflexivity, symmetry, transitivity — $\equiv$ is required to be an honest equivalence relation on top of everything above, which is what licenses chaining a sequence of the other fourteen rules into a single equality judgement.

The book closes the section by noting, correctly, that this is "from a formal point of view [...] similar to typed $\lambda$-calculus," that the decidability proof for typed-$\lambda$-calculus equality carries over to $\equiv$, and that a normal-form theorem holds (an expression with no subexpressions of the shapes $((x)b)(a)$ or $(a_1,\ldots,a_n).i$ is fully evaluated with respect to $\equiv$, and every expression is $\equiv$ to one in that form).

**Grounding — this is `isDefEq`, rule for rule.** The four families map onto a real kernel's equality checker almost without translation:

```lean
-- Roughly the shape of Lean's isDefEq (heavily simplified):
-- 1. base cases: same fvar/bvar/const/literal        -- rules 1, 2
-- 2. delta: unfold a `def` on either side and retry   -- rule 3
-- 3. beta-reduce both sides to whnf, then:
--    - same head constructor -> recurse congruently   -- rules 4, 6, 9, 11
--    - beta/iota-redex present -> reduce and retry     -- rule 5 (+ iota, not in this book)
--    - eta for lambdas / eta for structures            -- rules 7 (alpha is free via de Bruijn), 8, 10
-- 4. reflexivity / symmetry / transitivity are structural properties
--    of how isDefEq is called, not separate cases      -- rules 13-15
```

One genuine implementation detail worth flagging because it's a real simplification over the book: production kernels almost universally represent bound variables with **de Bruijn indices** rather than names, precisely so that Abstraction 2 (the $\alpha$-rule) stops being a rule you have to check at all — $(x)x$ and $(y)y$ are *literally the same term*, `Lam(Var(0))`, once names are erased in favor of "how many binders out." The book states $\alpha$-equivalence as an explicit equality rule because it's working with named variables (the more readable choice for a textbook); a real implementation usually chooses a representation that makes rule 7 true by construction instead of true by proof. The other fourteen rules survive translation far more directly — $\beta$, $\eta$, $\delta$, and the congruence/equivalence rules are exactly what you still have to implement.

## Two views of the same syntax tree

The syntax-tree picture from §3.1 (the book's Figure 3.1, for $+(y,\sin(y))$) is worth redrawing with arities attached at every node, since that's the invariant this whole chapter is protecting:

![[syntax_tree.svg]]

Every application node in this tree only type-checks (arity-checks) because the operator's arrow arity matches its argument's arity at each step: $+$ wants $0\otimes 0$, gets $y{:}0$ and $\sin(y){:}0$, both match, result is $0$. Try to build $succ(succ)$ this way and the tree simply cannot be assembled — there's no node you can draw for it, because clause 4 of Section 3.8 has no premise it satisfies. That's the whole discipline in one picture: arity-checking is a structural precondition for the tree to exist, not a separate pass that runs on an already-built tree and rejects it after the fact.

## Where this leads

Everything from Chapter 4 onward — [[The-Semantics-of-Judgement-Forms#Canonical and noncanonical expressions|canonical and noncanonical expressions]], [[the_semantic_judge_forms_qwen#The four categorical judgement forms|the four categorical judgement forms]], every formation/introduction/elimination/equality rule for every set former in the rest of the book — is stated as a condition on *expressions in the sense of this chapter*, checked for sameness using *exactly the $\equiv$ of this chapter*. When Chapter 5's substitution rules or Chapter 7's $\beta$-rule for $\Pi$-elimination invoke "the same expression" or "definitionally equal," they are invoking Section 3.9's fifteen rules, not some new notion introduced later. Arities themselves get retired once real sets/types take over classifying expressions from Chapter 4 on — but the *discipline* Section 3.6 introduces (classify expressions structurally, before doing anything semantic with them, specifically to keep self-reference out and equality decidable) reappears, essentially unchanged in spirit, as the reason type formation rules exist at all.

**Direct connection to the two target systems.** This chapter is the syntactic substrate both of your projects sit on top of:

- The **Rust verifier's `Expr`/AST type** is a direct descendant of the `Expr` enum built up across this article — and the arity-checking pass (`arity_of` above) is a template for the cheap, total, structural validity pass that should run *before* real dependent type-checking, exactly as arities are settled here before any of the book's actual set theory begins.
- The **Lean-style elaborator's `isDefEq`** is, almost rule for rule, Section 3.9's fifteen equality rules: reflexivity/symmetry/transitivity as the equivalence closure, the four congruence rules as the recursive-descent structure, $\beta$ (Application 2) and $\delta$ (definiendum $\equiv$ definiens, rule 3) as the two "actually compute something" rules, and $\eta$/structure-eta (Abstraction 3 / Combination 2) as the two "different-looking-but-really-the-same" rules a decidable equality checker has to special-case. The one place a real implementation typically diverges from the book's presentation — de Bruijn indices making the $\alpha$-rule free instead of checked — is worth remembering precisely *because* it's a genuine implementation choice with a real payoff (fewer cases in the equality checker), not a simplification that loses anything essential.
