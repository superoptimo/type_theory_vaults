---
title: Deductive Database Theory
source: Lloyd, "Foundations of Logic Programming" (1987)
chapters: Chapter 5, §21–23 (pp. 141–158)
tags: [deductive-databases, typed-logic, query-evaluation, domain-closure, proof-theoretic-semantics]
---

[[book-guidelines|↩ Back to guidelines]]

## Databases as an application, not a new theory

Nothing in this chapter is logically new. Every definition — database statement, query, correct answer, completion, query evaluation — is a direct relabeling of [[Programs-and-Goals-with-Arbitrary-First-Order-Bodies]]'s program-statement machinery: a "database" is a program, a "query" is a goal, and query evaluation is SLDNF-resolution. What *is* new is the discipline of **typing**, introduced specifically because relational database semantics has a concept the untyped theory doesn't: a **domain** (customer names live in one universe, supplier cities in another, and a query comparing them across domains is a category error, not merely a false statement). This chapter is the payoff of chapter 1's brief, then-unmotivated detour into typed (many-sorted) first-order logic — and it is worth treating as a serious case study in how far you can push "add types as a well-formedness discipline over an already-correct untyped core" before you need something genuinely new.

## Model-theoretic vs. proof-theoretic: a foundational choice with real consequences

Lloyd is explicit about a fork in database theory that most treatments gloss over. The **model-theoretic view** (standard relational algebra) treats the database *as* a model — its facts directly constitute an interpretation, and a query is evaluated by checking truth in that interpretation. The **proof-theoretic view** (which this chapter adopts) treats the database as a *first-order theory*, and answering a query means *proving* it a logical consequence of that theory. For ground-fact-only relational databases these views coincide (the facts *are* an Herbrand interpretation). They diverge the moment you add **rules** (recursive views, derived predicates) — a database with rules has no single canonical "the database as a structure"; there's only "the set of things provable from it." Lloyd's stated reasons for preferring proof-theoretic: it scales cleanly to non-ground information, incomplete/null-value reasoning, and (crucially, per this chapter's core content) recursive views, none of which have a natural model-theoretic reading once you leave pure relational algebra.

**This is exactly the choice you face designing a specification language for a verifier**: do you give your `requires`/`ensures` contracts a *model-theoretic* semantics (a fixed structure — e.g. a concrete operational-semantics trace space — against which "the program satisfies the spec" means literal truth), or a *proof-theoretic* one (satisfaction means *provability* in some proof system, e.g. Hoare logic or a CHC solver's derivation)? Lloyd's chapter is a fully worked argument for why proof-theoretic wins once recursion enters the picture — precisely the situation your refinement-type system's recursive/inductive predicates will be in.

## Typed syntax, revisited with real stakes

Recall from [[First-Order-Logic-as-a-Foundation-for-Logic-Programming]] that typed logic is formally eliminable — a convenience, not an extra expressive power. This chapter shows *why the convenience matters practically*: a supplier–part–job schema
```prolog
supplier    : sno x sname x city
spj         : sno x pno x jno x quantity
major_supplier(S) :- ∀J/jno ∃Q/quantity (spj(S,_,J,Q) ∧ Q≥100).
```
without types, nothing stops you from writing `spj(city_of(S1), P, J, Q)` — accidentally passing a city where a supplier-number belongs — and the *untyped* theory would happily accept this as a syntactically well-formed (if semantically nonsensical) query. The typed grammar rejects it at the syntax level, exactly the way a static type system rejects `int + string` before any evaluation happens. This is Lloyd's version of "**well-typed programs don't go wrong**," applied to query languages instead of programming languages: a correctly-typed query cannot accidentally conflate domains, a genuine (if modest) *semantic integrity* guarantee purchased entirely by syntax-level discipline.

## Domain closure axioms: the piece typed program-statement theory didn't need

The completion machinery generalizes cleanly (typed quantifiers, a typed equality predicate $=_\tau$ per sort, a typed equality theory, axioms 1–8 exactly mirroring [[Negation-in-Logic-Programs]]'s untyped equality theory) — **except for one genuinely new axiom scheme, axiom 9, the domain closure axioms**:
$$\forall x/\tau\; \Big( (x =_\tau a_1) \lor \cdots \lor (x =_\tau a_k) \lor \exists \vec x_1/\vec\tau_1\,(x =_\tau f_1(\vec x_1)) \lor \cdots \Big)$$
— every element of type $\tau$ is *one of the known constants of that type, or built from a known function symbol of that range type*. This is not optional decoration; Lloyd shows explicitly (§22 counterexample) that without it, soundness of query evaluation *fails*: the query $\forall x/\tau\, p(x)$ over a database containing only `p(a).` is **not** a logical consequence of the completion without a domain closure axiom pinning down that $\tau$'s only element is $a$ — the completion alone leaves room for models with "extra," unnamed elements of type $\tau$ that $p$ needn't hold of.

**This is precisely the closed-world assumption applied one level up — to the domain itself, not just to predicates.** Where negation-as-failure ([[Negation-in-Logic-Programs]]) closes off *what's true of the named individuals*, domain closure closes off *what individuals exist at all*. And this is exactly the role an inductive type's constructor set plays in a dependently-typed kernel: `inductive Nat where | zero | succ (n : Nat)` is *itself* a domain closure axiom, built into the type former rather than bolted on as a separate axiom scheme — it asserts that every `Nat` is `zero` or `succ` of something, licensing exhaustive pattern matching and structural induction. Lloyd's domain closure axioms are the first-order-logic version of the same commitment, made explicit precisely because untyped first-order logic has no native notion of "these are all the constructors."

## Query evaluation: soundness via a genuinely nontrivial model construction

Query evaluation works by transforming everything — database, query, integrity constraints — to **type-free form** ($W^*$: replace $\forall x/\tau\, V$ by $\forall x\,(V \land \tau(x))$, using a fresh unary type predicate per sort), adding the **type theory** $\Phi$ (Horn-style facts $\tau(a)$ and rules $\tau(f(\vec x)) \leftarrow \tau_1(x_1) \land \cdots$ generating exactly the domain-closure-licensed elements), then running ordinary SLDNF-resolution ([[Negation-in-Logic-Programs]], [[Programs-and-Goals-with-Arbitrary-First-Order-Bodies]]) on the untyped result.

**Soundness (Theorem 22.6) requires Lemma 22.1**, whose proof is genuinely elaborate and worth understanding at least at the level of its strategy, because the technique — *build a "richer" model by closing a given model under a term-reduction/quotient construction* — recurs constantly in completeness proofs for logics with equality: given a model $M$ of the typed completion, Lloyd builds $M^*$ for the type-free completion by taking *all* terms formable from $M$'s elements and $M$'s function interpretations (ignoring type restrictions), defining a reduction relation, proving every term has a *unique irreducible form* (a confluence-style lemma, Lemma 22.2 — structurally identical to proving a rewriting system terminates and is confluent, hence has unique normal forms), and quotienting by "reduces to the same irreducible form." **This is literally constructing a term model via reduction to normal form and confluence** — the exact technique used to build canonical models for equational theories, and the exact technique underlying how a dependently-typed kernel's definitional equality check (reduce both sides to normal form, or use a confluent reduction strategy, and compare) is *proved* to be a genuine congruence in the first place.

**Completeness (Theorem 23.4) holds unconditionally for definite databases** (ground correct answers are always findable), but full termination/enumerability (**Theorem 23.5**) again needs the **hierarchical** restriction from [[Negation-in-Logic-Programs]] — the same completeness ceiling recurring for exactly the same structural reason (negation-as-failure cannot both bind variables and terminate-with-completeness on unrestricted recursive negation).

## Grounding: typed Horn clauses as a schema-checked query IR

```rust
// A typed predicate signature — this is your schema, and type-checking a
// query against it before ever running SLDNF-resolution is exactly the
// "well-typed queries don't go wrong" discipline this chapter formalizes.
struct Sort(String);
struct PredSig { name: String, arg_sorts: Vec<Sort> }

fn typecheck_atom(atom: &Atom, sig: &HashMap<String, PredSig>, ctx: &TypeContext) -> Result<(), String> {
    let expected = &sig[&atom.pred].arg_sorts;
    for (arg, sort) in atom.args.iter().zip(expected) {
        if ctx.sort_of(arg) != *sort {
            return Err(format!("{arg:?} has sort {:?}, expected {sort:?}", ctx.sort_of(arg)));
        }
    }
    Ok(())
}

// Domain closure as an explicit generative rule set — this is literally
// how you'd encode "every value of this sort is a known constructor" as
// Horn-clause facts, feeding a bottom-up evaluator exactly as chapter 5 does.
fn domain_closure_facts(sort: &Sort, constants: &[Term], constructors: &[FnSig]) -> Vec<Clause> {
    let mut facts: Vec<Clause> = constants.iter()
        .map(|c| Clause::fact(format!("{}({c:?})", sort.0)))
        .collect();
    for f in constructors {
        facts.push(Clause::rule(
            format!("{}({}(Xs...))", sort.0, f.name),
            f.arg_sorts.iter().map(|s| format!("{}(X)", s.0)).collect(),
        ));
    }
    facts
}
```

**In Lean**, the type-free-transformation-plus-type-theory-axioms strategy is exactly **type erasure with an explicit runtime type-tag reconstruction** — compiling a dependently- or simply-typed term down to an untyped core (Lean's kernel ultimately reduces to a much smaller untyped-ish calculus for actual computation) while carrying enough auxiliary information (here, the $\tau(x)$ predicates; there, runtime type representations for `Decidable`/`Inhabited`-style typeclass resolution) to reconstruct the typed reasoning when needed. The domain closure axiom scheme is, again, precisely what an `inductive` declaration's constructor list gives you for free — worth noticing that first-order logic *needs an axiom scheme* to express what a dependently-typed kernel gets as a *primitive language feature*, a good illustration of why richer type theories exist: they internalize reasoning principles (induction, exhaustiveness, domain closure) that classical first-order logic can only bolt on axiomatically, per-sort, by hand.

## Where this leads

- **Directly load-bearing:** the proof-theoretic-vs-model-theoretic fork is a decision your compiler's specification semantics needs to make explicitly, and this chapter is a fully worked argument for why the proof-theoretic choice is the right one once recursive predicates (recursive refinement types, recursive invariants) are on the table.
- Domain closure axioms are the first-order-logic shadow of what your inductive-type kernel gives natively — recognizing this connection tells you *when* you actually need an explicit closure axiom in a verification-condition (whenever you reason about a domain that isn't backed by an honest inductive type in your host type theory, e.g. reasoning about "all possible heap states" or "all possible traces") versus when the type system already supplies it for free.
- [[Integrity-Constraint-Checking]] builds directly on this chapter's query-evaluation soundness result, using it as the base case for a genuinely new theorem (incremental re-verification after an update) that this chapter doesn't touch.
