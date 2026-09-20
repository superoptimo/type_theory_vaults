---
title: Compilers as Finite Maps
source: A Framework for Modular, Extensible, Equivalence-Preserving Compilation (Jamner, 2022)
chapter: "3.2 Compilers and Correctness"
pages: "25–27"
tags: [type-theory, automated-reasoning, compilers, pyrosome, substitution]
---

[[book-guidelines|↩ Back to guidelines]]

## What problem is a "compiler" trying to be a solution to, here?

Forget verification for a second and just ask: what *is* a compiler, structurally? The obvious answer — "a function from source ASTs to target ASTs" — is true but useless, because it hides the two properties Pyrosome actually needs and that most compiler implementations get informally, accidentally, and unverifiably right:

1. **It has to work on *open* terms.** A real compiler doesn't just compile whole, closed programs — it has to compile a function body that mentions free variables bound somewhere else, a library module that will be linked against unknown client code, a single expression pulled out for separate compilation. If your compiler is only defined as "closed source program → closed target program," you can't even *state* a linking theorem, because linking is precisely the act of combining separately-compiled open pieces.
2. **It has to commute with substitution.** If compiling `e` and then substituting the compiled value for `x` gives a different result than substituting first and then compiling, your compiler is unsound the moment two compiled fragments get linked together. This is the thing that quietly breaks in ad-hoc compiler implementations that special-case "the whole program" as an assumption baked into environment handling, closure allocation order, or global counters.

**What breaks without this:** imagine a compiler that assigns each function a unique integer ID by counting occurrences during a whole-program pass. Compile two modules separately, then link them — your IDs collide, because each module's compiler ran in its own numbering universe with no notion that it was ever going to be substituted into a larger context. The compiler was only ever proved correct as a *closed, whole-program* transformation; nothing about its definition, let alone its correctness proof, extends to the open, substitution-compatible setting linking requires.

Pyrosome's answer is to *define* "compiler" narrowly enough that both properties come for free by construction, rather than proving them as afterthought lemmas about an otherwise-unconstrained function.

## The definition: a compiler is a finite map from constructors to target templates

A **compiler** in Pyrosome is a finite map from source-language sort and term *names* (constructors, like `"get"`, `"lambda"`, `"zero"`) to target-language sorts and terms. Crucially, the target term on the right-hand side of each mapping is written using the framework's *metavariables* — the same device the language specification itself uses for "the subterm goes here" (see [[Language-Specifications-as-Equational-Theories]] for how term rules distinguish object-language variables from metavariables). A metavariable in a mapping's right-hand side is a placeholder that gets filled in with *the already-compiled version* of the corresponding source subterm.

Concretely, the book's running example: compiling STLC's `get` construct (reading a memory cell) into a CPS-style calculus with an explicit global store. The compiler table has an entry roughly of the shape

$$
\texttt{"get"} \;\triangleq\; \texttt{bind } x := e; \; \texttt{get } x \; \texttt{as } y \; \texttt{in} \; k\,y
$$

where $e$ is a metavariable standing for "whatever the (already-compiled) subterm of the source `get` node was." Nothing here says anything about *which* term $e$ ends up being — the entry is a *template*, reusable no matter what expression the programmer actually wrote inside `get`.

### Compilation as bottom-up traversal + substitution

Given that table, compiling an actual term is mechanical:

1. Walk the source term's syntax tree from the **leaves up** (bottom-up traversal — you need the compiled children before you can build the compiled parent, exactly like a post-order tree walk).
2. At each node, look up its constructor in the table to get the target-language template.
3. **Metavariables in the term being compiled pass through unchanged**; metavariables in the *template* get filled with the already-compiled subterms.

The book's own worked micro-example: compiling `#"get" "v"` where `"v"` is itself a metavariable (i.e., an open term — we don't know what "v" resolves to, and we don't need to). Since `"v"` is a metavariable, step 3 says it compiles to itself. Then we look up `"get"` in the table, take the template `bind x := e; get x as y in k y`, and substitute `"v"` for the template's own metavariable `e`, yielding `bind x := v; get x as y in k y`.

Notice what *didn't* happen: nothing inspected what `"v"` "really was." The whole procedure is oblivious to whether `v` is a literal, a bound variable, or a hole waiting to be linked against a completely different module. That obliviousness *is* the open-terms property from above — it isn't proved separately, it falls straight out of the fact that compilation is defined purely as constructor-by-constructor table lookup plus metavariable substitution, with no other mechanism available to peek at term structure.

**What breaks without metavariable-based templates:** if instead each compiler case were an arbitrary Coq/Rust function of type `SourceTerm -> TargetTerm` (rather than a metavariable-templated table entry), nothing would stop you from writing a case that pattern-matches deep into a subterm's *shape* — e.g., "if this argument is literally the constant zero, do something special." That function would be perfectly well-typed but would silently break substitution invariance: compile-then-substitute and substitute-then-compile could diverge, because a substituted metavariable might turn "the argument was a metavariable" into "the argument is now literally zero," triggering a code path that wasn't available at compile time. Restricting compilers to the finite-map/metavariable-template shape is a discipline that makes this kind of bug *inexpressible*, not just absent-by-diligence.

## The invariant this buys you: substitution invariance

The formal property is stated as:

$$
\lfloor \gamma(e) \rfloor \;=\; \lfloor \gamma \rfloor(\lfloor e \rfloor)
$$

Read this named term by term, because the notation packs in more than it looks like:

- $e$ is a source term (possibly open, containing metavariables).
- $\gamma$ is a **metavariable substitution** — a mapping from metavariable names to source terms, the same notion of substitution used throughout the equational theory.
- $\gamma(e)$ is "apply that substitution to $e$" — ordinary substitution, done *before* compiling.
- $\lfloor - \rfloor$ is the compiler (the book's own bracket notation for "compile this").
- $\lfloor \gamma \rfloor$ is "the substitution you get by compiling every term $\gamma$ maps to" — i.e., push the compiler *through* the substitution, compiling its range, not its domain (metavariable names themselves aren't source syntax, so they aren't compiled).

So the equation says: **it doesn't matter whether you substitute first and then compile, or compile first (leaving the metavariables as placeholders) and then substitute in the compiled replacements.** Both orders land in the same target term.

This is exactly the property that made the bottom-up traversal work correctly above — it's the reason "compile the children, then compile the parent using the children's *compiled* output as a metavariable-filler" is even a coherent thing to do. If substitution invariance failed, the entire recursive-descent compilation procedure would give a *different* answer than defining the compiler for the whole term at once, and "compile bottom-up" would just be a bug, not an algorithm.

It's also, per the book, exactly what makes **congruence "come for free"** during the equivalence-preservation proof (Theorem 2 / section 3.3): when you need to show that compiling two source terms related by a congruence rule ($e_1 = e_2 \Rightarrow C[e_1] = C[e_2]$ for some context $C$) still gives you related target terms, you'd naively need a separate proof obligation for every context shape $C$ could take. Substitution invariance collapses all of those into one argument, because "plugging into a context" is itself just an instance of metavariable substitution.

## Extension: compilers as append-only tables

Just as a **language** in Pyrosome is a list of rules, extended by list concatenation ($L_1 + L_2$, see [[Language-Specifications-as-Equational-Theories]]), a **compiler** is extended the same way: by *appending new mappings* to the finite map. Compiling STLC-plus-recursion is: take the STLC compiler's table, append entries for the new recursion-related constructors, done. No existing entry is touched, no existing case is revisited.

This is the mechanical realization of the "prove once, reuse forever" promise that motivates the whole framework (see [[The-Problem-of-Extensible-Compiler-Verification]]): if a compiler is *just data* — a finite map — then "extending the compiler" is a data operation (append) rather than a proof operation. The proof work of showing the extended table still satisfies $\mathrm{Preserving}$ is handled separately, per-entry, by the machinery in [[The-Preserving-Predicate-and-Modularity-Theorems]] — but the *compiler itself*, as an artifact, is trivially extensible because finite maps are trivially extensible.

## Grounding: what this looks like as code

**Rust (primary).** The finite-map structure is almost embarrassingly literal:

```rust
use std::collections::HashMap;

/// A target-language term template. `Meta(n)` stands for
/// "the compiled n-th subterm of whatever source node this rule fires on" —
/// exactly Pyrosome's framework metavariables.
#[derive(Clone)]
enum Template {
    Meta(usize),
    Node(String, Vec<Template>),
}

/// A compiler: source constructor name -> target template.
/// Extension is literally `HashMap::extend`, i.e. list-append-shaped.
struct Compiler {
    table: HashMap<String, Template>,
}

impl Compiler {
    /// Bottom-up: compile children first, then splice them into the
    /// looked-up template. This function makes no case distinction
    /// on what a child *is* — only on the parent's constructor name —
    /// which is precisely the discipline that keeps substitution invariance
    /// mechanically enforced rather than separately proved.
    fn compile(&self, source: &SourceTerm) -> Template {
        match source {
            SourceTerm::Meta(n) => Template::Meta(*n), // metavariables pass through
            SourceTerm::Node(ctor, children) => {
                let compiled_children: Vec<Template> =
                    children.iter().map(|c| self.compile(c)).collect();
                let template = self.table.get(ctor).expect("unmapped constructor");
                splice(template, &compiled_children) // fill Meta(i) with compiled_children[i]
            }
        }
    }

    /// Extension is append — no existing entries are inspected or changed.
    fn extend(&mut self, new_rules: HashMap<String, Template>) {
        self.table.extend(new_rules);
    }
}
# enum SourceTerm { Meta(usize), Node(String, Vec<SourceTerm>) }
# fn splice(t: &Template, args: &[Template]) -> Template { t.clone() }
```

The `HashMap::extend` call is not a cute coincidence — it's the same operation, for the same reason, as `Vec::extend`-ing a language's rule list. Both are "append to a flat, order-respecting collection," and both extensions are proof-compatible for the same underlying reason: nothing about existing entries had to change.

**Lean (secondary — this *is* a substitution lemma).** If you've built anything with a kernel-level `subst` operation, this is exactly the lemma shape you already know as commutativity of substitution with a structurally recursive function:

```lean
-- Schematically: a "compile" function defined by structural recursion
-- on source syntax, and the substitution-invariance lemma about it.
def compile : SourceTerm → TargetTerm := sorry

theorem compile_subst_comm (γ : MetaSubst) (e : SourceTerm) :
    compile (γ.apply e) = (γ.compileRange compile).apply (compile e) := by
  induction e <;> simp_all [compile, MetaSubst.apply]
```

This is structurally the same lemma Lean's own elaborator relies on constantly when it pushes a metavariable assignment through a partially-elaborated term — `isDefEq`-style reasoning depends on definitional equality being stable under exactly this kind of substitution-then-normalize / normalize-then-substitute commutation. If you're building the elaborator described in this workbench's learning goals, this is the same proof obligation you'll discharge when justifying that solving a metavariable and then re-checking a term gives the same type as checking with the (still-unsolved) metavariable and substituting afterward.

**Python (tertiary sketch).** A five-line illustration of the same table-lookup-and-splice idea, useful only for seeing the shape quickly:

```python
def compile(term, table):
    if is_metavar(term):
        return term  # pass through unchanged
    ctor, children = term
    compiled_children = [compile(c, table) for c in children]
    return splice(table[ctor], compiled_children)
```

## Where this leads

This finite-map/substitution-invariant definition of "compiler" is the load-bearing artifact for nearly everything downstream in the thesis: it's the *object* that [[The-Preserving-Predicate-and-Modularity-Theorems]] proves properties about, the reason congruence needs no separate proof case in the equivalence-preservation theorem, and — per the book's own section 5.3 — the very rigidity that makes standard translation-time *optimizations* hard to express (an optimizer typically wants exactly the kind of shape-inspecting cleverness that substitution invariance rules out), motivating the "intralanguage optimization pass" idea floated in [[Related-Frameworks-and-Future-Directions]].

For this workbench's compiler/elaborator project (`type-theory`, `automated-reasoning`): this is the direct ancestor of any translation or lowering pass your Rust compiler will run, and the substitution-invariance proof obligation is structurally identical to the metavariable-substitution commutation lemmas your elaborator's unifier will need whenever it resolves an implicit argument mid-elaboration and has to justify that resolving it earlier vs. later doesn't change the final elaborated term.
