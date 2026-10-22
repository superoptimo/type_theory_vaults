# Metavariables of the object level

Proof assistants and unification algorithms use unknowns, or holes, written $?m$, which stand for a term to be found later. This is where capture becomes interesting, because here you often _want_ something that looks like capture.

**Instantiation is not capture-avoiding substitution.** Take a hole created inside a binder:

$$\lambda x{:}A.,?m$$

If elaboration decides $?m := x$, the result should be $\lambda x{:}A.,x$. Ordinary capture-avoiding substitution would rename the binder to avoid this, giving $\lambda x'{:}A.,x$, which is the wrong answer. The hole was created in a context containing $x$, so it is _allowed_ to depend on $x$.

**So a metavariable carries its context.** A hole is declared with the context it lives in:

$$?m : (\Gamma,\ x{:}A \vdash B)$$

and is only allowed to be solved by a term whose free variables lie in that context. This is the _scope check_:

$$?m := t \text{ is legal only if } \mathrm{FV}(t) \subseteq \operatorname{dom}(\Gamma,\ x{:}A)$$

The opposite case is an error. If $?n$ was created in $\Gamma$ alone and appears as $\lambda x{:}A.,?n$, then solving $?n := x$ would let $x$ escape its scope, and the scope check rejects it. This is the contextual version of the book's idea that context subjects bind free variables: a hole's context determines which names it may mention.

## How systems implement this

|Approach|How capture is handled|
|---|---|
|Named, delayed substitution ($?m[\sigma]$)|The hole is paired with a substitution $\sigma$ from its own context to the current one. It is applied only once the hole is solved, and the renaming happens then. Coq's existential variables work roughly this way.|
|Pattern unification (Miller)|Holes are applied to distinct bound variables, $?m,x_1\cdots x_n$. Solving $?m,x_1\cdots x_n \doteq t$ gives $?m := \lambda x_1 \ldots x_n.,t$, so the solution is closed by a $\lambda$ and no variable can be captured.|
|De Bruijn indices|A solution stored in the hole's own context must be shifted by $\uparrow^{k}$ when it is placed under $k$ extra binders. Forgetting this shift is a classic bug.|
|Contextual modal type theory|The hole's context becomes part of its _type_, so scope errors are type errors.|

# Where holes come from

Holes appear whenever the algorithm needs a term or type it doesn't have yet, and the derivation determines them by turning every "these two things must be equal" side condition into an equation and solving the equations.

A fresh metavariable $?m$ is created at each of these points:

1. **Missing annotations.** Typing $\lambda x.,M$ with no domain gives $x$ the type $?A$, so the context becomes $\Gamma,\ x{:}?A$.
2. **Instantiating polymorphism or implicit arguments.** If $\mathsf{id} : \Pi \alpha{:}\ast.,\alpha \to \alpha$ is used as $\mathsf{id}\ 3$, the elaborator inserts $\mathsf{id}\ ?\alpha\ 3$.
3. **Applications whose function type is unknown.** The application rule needs the function's type to be a $\Pi$-type, so the algorithm invents one.
4. **User-written holes and tactics.** An underscore `_` or a `refine` step creates a hole with a stated goal.

Each hole is created together with the context it lives in, which is what the scope check from my previous message uses.

## How the derivation produces equations

The typing rules are read as a constraint generator. For application, the rule

$$\dfrac{\Gamma \vdash F : C \qquad \Gamma \vdash a : A}{\Gamma \vdash F,a : B}$$

has a hidden side condition that $C$ is a $\Pi$-type whose domain matches $A$. The algorithm records this as an equation with a fresh hole for the codomain:

$$C \doteq \Pi x{:}A.,?B$$

Bidirectional checking reduces the number of holes. When the expected type is known, it is pushed into the term, so the $\lambda$ gets its domain from the expected $\Pi$-type instead of a fresh hole.

## Worked example: $\lambda f.,\lambda x.,f,x$ (simple types)

1. Open both binders: $f{:}?A,\ x{:}?B$.
2. Type the body $f,x$. We have $f : ?A$ and $x : ?B$, so the application requires $?A \doteq ?B \to ?C$, with $?C$ fresh.
3. Solve: $?A := ?B \to ?C$.
4. Read off the result:

$$\lambda f{:}(?B \to ?C).,\lambda x{:}?B.,f,x ;:; (?B \to ?C) \to ?B \to ?C$$

Nothing forces $?B$ or $?C$, so they remain unsolved. A Hindley–Milner system generalizes them to type variables $\forall \beta,\gamma.\ (\beta \to \gamma) \to \beta \to \gamma$. A proof assistant would instead report an unresolved hole, or wait for later use to fix them.

## How the equations are solved

The solver keeps a set of equations and repeatedly applies these cases:

|Case|Action|
|---|---|
|Same rigid head on both sides|Decompose into equations on the arguments.|
|Different rigid heads|Fail with a type error.|
|Hole against a term, $?m \doteq t$|Assign $?m := t$ after the two checks below.|
|Hole against hole|Assign one to the other, preferring the one with the larger context.|
|Not a pattern, or blocked on another hole|Postpone and retry after other holes are solved.|

An assignment $?m := t$ is legal only if both checks pass:

- **Occurs check:** $?m$ does not occur in $t$. Otherwise the solution would be an infinite term.
- **Scope check:** $\mathrm{FV}(t) \subseteq \operatorname{dom}(\Gamma_{?m})$, where $\Gamma_{?m}$ is the context in which $?m$ was created.

## Holes under binders: Miller patterns

A hole created under binders cannot see the binder's variable from outside, so it is treated as a function of those variables: $?m,x_1 \cdots x_n$ with the $x_i$ distinct bound variables. Such an equation has exactly one most general solution:

$$?m,x_1 \cdots x_n \doteq t \quad\Longrightarrow\quad ?m := \lambda x_1 \ldots x_n.,t$$

subject to $\mathrm{FV}(t) \subseteq {x_1,\ldots,x_n} \cup \operatorname{dom}(\Gamma_{?m})$.

For example, take $?m,x \doteq x,y$.

- If $y \in \operatorname{dom}(\Gamma_{?m})$, the solution is $?m := \lambda x.,x,y$, because $y$ is visible to $?m$.
- If $y$ was introduced after $?m$ was created, the scope check fails and $y$ cannot escape into $?m$. The algorithm may try to _prune_ $y$ from the other hole that depends on it, or it reports an error.

This is exactly where the capture problem from the start of our conversation reappears. Closing the solution with $\lambda x_1 \ldots x_n$ and checking scopes is what prevents any variable from being captured or escaping.

## What "determined" means

- **Result.** The algorithm outputs a substitution $\sigma$ from holes to terms. The final judgment is the original one with $\sigma$ applied throughout.
- **Uniqueness.** First-order unification and Miller's pattern fragment give a _most general_ solution, so every other solution is an instance of it. General higher-order unification is undecidable (Huet), so real systems postpone non-pattern problems and may leave them unsolved.
- **Ordering.** In dependent type theory the type of a hole can itself mention other holes, for example $?a : ?A$. A hole can only be solved after the holes its type depends on, so the solver processes them in dependency order.
- **Leftovers.** A hole that is still unsolved at the end is generalized (Hindley–Milner), defaulted (numeric literals), turned into a proof obligation (Coq, Lean, Agda), or reported as ambiguous.

# Meta-Variable Local Context

Short answer: a hole stands for a term that is not written yet, and a term only makes sense relative to a context. Lean stores that context inside the hole so scope is checked from the hole's own declaration. I'm going from memory of Lean 4's internals (`MetavarDecl`, `LocalContext`, `MetavarContext`), so check the names against your version.

## What is stored

Each metavariable declaration records, roughly, its type, its `LocalContext`, and some bookkeeping such as its kind and a depth counter. The judgment it represents is

$$\Gamma_{?m} \vdash\ ?m : B$$

with both $\Gamma_{?m}$ and $B$ stored. This is the idea behind contextual modal type theory, where the context is part of the hole's type.

## Why store it

**1. The scope check needs it.** Assigning $?m := t$ is legal only if

$$\mathrm{FV}(t) \subseteq \operatorname{dom}(\Gamma_{?m})$$

Without the stored context, the algorithm could not tell whether a free variable of $t$ is visible to $?m$.

**2. It avoids representing holes as $?m,x_1 \cdots x_n$.** In the Miller-style presentation, a hole under binders is applied to the variables it may depend on. Lean instead uses a locally nameless representation. When the elaborator enters $\lambda x{:}A.,\ldots$, it opens the binder with a fresh free variable (an `fvar` with a unique id) and creates the hole in the extended context $\Gamma, x{:}A$. A solution can mention that `fvar` directly, so there is no application to track. Because every `fvar` is unique, the freshness condition from the beginning of our conversation is satisfied automatically, and a solution cannot be captured by a binder.

**3. Types depend on the context.** The type $B$ of a hole may mention variables from $\Gamma_{?m}$, such as $?m : P(x)$. That type is only well formed in that context, so the two must be stored together.

**4. Goals are holes.** In tactic mode a goal is a metavariable, and its local context is the list of hypotheses displayed above the turnstile. A tactic like `intro` creates a new hole with an extended context and assigns the old goal in terms of it.

## What happens when the binder closes

The cost of this design appears when the binder closes. If you abstract $x$ out of a term that still contains an unsolved hole whose context mentions $x$, the hole would escape its scope. Lean's abstraction step handles this by creating a new hole $?n$ with the smaller context and assigning

$$?m := ?n\ x$$

This is exactly the Miller form, but it is created _on demand_, only when a binder actually closes over a hole. Tactic blocks use a related mechanism, delayed assignments, for the same purpose.

## Unification and context size

When unifying $?m \doteq ?n$, the rule is about contexts. If $\Gamma_{?n}$ is contained in $\Gamma_{?m}$, then $?n$'s eventual value could use fewer variables, so you assign the hole with the _larger_ context to the one with the _smaller_ context. The surviving hole has the more restrictive scope, so its solution is valid for both. Note that this corrects my wording in the last message, where I said to prefer the hole with the larger context. That was ambiguous. The larger-context hole is the one that gets assigned.

For $?m := t$ where $t$ contains a variable outside $\Gamma_{?m}$, the checker does not always fail immediately. It may first try to restrict the other holes inside $t$ to variables in $\Gamma_{?m}$ (pruning), and it reports an error only if pruning cannot remove the offending variable.

## Comparison with other designs

|Design|Where scope information lives|
|---|---|
|Lean, Coq evars (roughly)|In the hole's own declared context|
|Miller patterns, Agda|In arguments, as $?m,x_1 \cdots x_n$|
|Contextual modal type theory|In the hole's type, with an explicit substitution|

Storing the context makes holes cheap to create under binders and makes the scope check a set inclusion. The trade-off is the extra work when closing a binder around an unsolved hole, as described above.

I can walk through the case $\lambda x{:}A.,?m$ closing with $?m$ still unsolved, showing the new hole $?n$ and the assignment $?m := ?n,x$ step by step, if you want to see it concretely.

# Living Example

Here is the full trace. The example is deliberately tiny so every step is visible. It follows my memory of Lean 4's behavior (`mkLambdaFVars` and its dependency elimination), so the names may differ in your version.

## Setup

Let $\Gamma$ contain $A : \mathsf{Type}$. We elaborate

$$\lambda x{:}A.\ ?m \quad\text{against the expected type}\quad A \to A$$

where $?m$ is a hole the user wrote, or one the elaborator created, because the body is not known yet.

## Step 1: open the binder

The elaborator does not work with the bound variable. It creates a fresh free variable $x_1$ (a unique id) and enters the extended context

$$\Gamma_1 ;=; \Gamma,\ x_1{:}A$$

The body is checked against the codomain $A$.

## Step 2: create the hole inside the extended context

The new hole is declared together with its context and type:

$$?m ;:; (\Gamma_1 \vdash A)$$

So $\Gamma_{?m} = \Gamma_1$, and any solution of $?m$ may mention $x_1$.

## Step 3: close the binder (the critical step)

Now we abstract $x_1$ to build the $\lambda$. The body is still $?m$, and its context mentions $x_1$. If we simply replaced $x_1$ by a bound variable in the body, nothing would change, because $?m$ is an opaque symbol with no visible occurrence of $x_1$. A later solution $?m := x_1$ would then contain a free $x_1$ outside any binder. That is the escape problem.

So the abstraction step does the following.

1. It sees that $?m$'s context depends on $x_1$, which is being abstracted.
2. It creates a new hole $?n$ in the smaller context $\Gamma$, with the type of $?m$ closed over $x_1$:

$$?n ;:; (\Gamma \vdash \Pi x{:}A.\ A)$$

3. It assigns $?m$ in terms of the new hole:

$$?m ;:=; ?n\ x_1$$

Now the body is $?n\ x_1$, and the variable $x_1$ is visible as an argument. Abstracting it gives

$$\lambda x{:}A.\ ?n\ x$$

and the hole $?n$ lives in $\Gamma$, where $x_1$ does not exist.

## Step 4: why $?n$ cannot mention $x$

Suppose the elaborator later tries $?n := x_1$.

$$\mathrm{FV}(x_1) = {x_1} \not\subseteq \operatorname{dom}(\Gamma)$$

The scope check fails, so the assignment is rejected. This is the guarantee we wanted. Whatever solves $?n$ is a closed term over $\Gamma$, and all use of $x$ has to go through the argument position.

## Step 5: solve the hole by unification

Suppose a later part of the program forces the body to equal $x$ (for example, the user finishes with `exact x`, or the expected term is the identity). The constraint arrives in the extended context as

$$?n\ x_1 ;\doteq; x_1$$

This is a Miller pattern: the hole is applied to distinct free variables ($x_1$ only). The solution is to abstract the right-hand side over those variables:

$$?n ;:=; \lambda y{:}A.\ y$$

and the checks pass:

- Occurs check: $?n$ does not occur in $\lambda y{:}A.,y$.
- Scope check: $\mathrm{FV}(\lambda y{:}A.,y) = \varnothing \subseteq \operatorname{dom}(\Gamma)$.

Notice the bound name $y$. Abstracting over $x_1$ produces a term where the variable is bound, and its name is irrelevant (the Barendregt convention again).

## Step 6: instantiate and reduce

Substituting the assignments, the term becomes

$$\lambda x{:}A.\ (\lambda y{:}A.\ y)\ x$$

Lean's instantiation step performs a head beta reduction when it substitutes a $\lambda$ into an application position, so the result is

$$\lambda x{:}A.\ x ;:; A \to A$$

which is the identity function, as intended.

## Summary of the state at each step

|Step|Holes|Context of the new hole|Term so far|
|---|---|---|---|
|2|$?m$|$\Gamma, x_1{:}A$|$?m$|
|3|$?m$ assigned, $?n$ new|$\Gamma$|$\lambda x{:}A.\ ?n\ x$|
|5|$?n$ assigned||$\lambda x{:}A.\ (\lambda y{:}A.,y),x$|
|6|none||$\lambda x{:}A.\ x$|

## The same trace with de Bruijn indices

If the bound variable is a de Bruijn index, the term in Step 3 is $\lambda A.\ ?n\ 0$. The hole $?n$ is applied to the index $0$, which points at the binder, and the solution in Step 5 is $\lambda A.\ 0$. Beta reduction then substitutes $0$ for the index of the inner $\lambda$ and shifts, giving $\lambda A.\ 0$. In Lean this is exactly the kind of case where the shifts happen inside the instantiation code.

## Tactic blocks use a variant

For holes that stand for goals (`syntheticOpaque` holes in Lean), the assignment $?m := ?n,x_1$ is not made immediately, because tactics need $?m$ to stay unassigned until the proof is finished. Lean records a _delayed assignment_, which says "$?m$ will become $?n\ x_1$ once $?n$ is solved". The scoping logic is the same, only the time of the assignment differs.

I can extend the example to a dependent case, where $?m$ has a type like $P\ x$ so that the type of $?n$ becomes $\Pi x{:}A.\ P\ x$, if you want to see how the types follow the context.