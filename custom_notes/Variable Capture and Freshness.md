
## The idea: a context binds like a λ

In an untyped term, $\lambda x.,M$ binds free occurrences of $x$ in $M$. In a typed judgment

$$x_1{:}A_1,\ \ldots,\ x_n{:}A_n \vdash M : B$$

the term $M$ may contain free variables, and the context supplies their types. The book calls $x_i$ the _subject_ and $A_i$ the _predicate_ of the declaration $x_i{:}A_i$. So the subjects of the context play the role of binders for the free variables of $M$, just not written inside the term. The requirement is that the free variables of $M$ must all occur among the subjects of the context:

$$\mathrm{FV}(M) \subseteq {x_1,\ldots,x_n}$$

This is the typed analogue of "a closed term is one with no free variables". A term is closed relative to its context.

## How capture is avoided

Three mechanisms work together.

**1. Contexts have distinct subjects.** A context is a list of declarations whose subject variables are pairwise different. So a free variable $x$ in $M$ refers to exactly one declaration, and there is no ambiguity about its type.

**2. Freshness conditions in the rules.** The rules that extend a context require the new variable to be fresh. For example, the abstraction rule has the shape

$$\dfrac{\Gamma,\ x{:}A \vdash M : B}{\Gamma \vdash \lambda x{:}A.,M : \Pi x{:}A.,B}$$

where $x$ is implicitly not already a subject of $\Gamma$. Likewise, in the dependent-type systems, the start and weakening rules only extend $\Gamma$ with $x{:}A$ when $x \notin \mathrm{dom}(\Gamma)$. This stops a newly introduced binder from accidentally capturing or shadowing a variable already declared in the context.

**3. The Barendregt (variable) convention.** Terms are identified up to $\alpha$-conversion. In any discussion, bound variables are assumed to be chosen different from the free variables, and, in the typed setting, different from the subjects of the context. If a clash would occur, say a substitution $M[x:=N]$ where a binder in $M$ coincides with a free variable of $N$, you silently rename the bound variable first. Substitution is then defined without worrying about capture:

$$(\lambda y.,P)[x:=N] \equiv \lambda y.,(P[x:=N]) \quad \text{provided } y \notin \mathrm{FV}(N) \text{ and } y \neq x$$

and the proviso can always be met by renaming $y$.

## Why this matters in dependent types

When types can depend on terms, later declarations may mention earlier subjects:

$$x{:}A,\ y{:}B(x) \vdash \ldots$$

Here the context is ordered and each subject binds in everything to its right, like a nested $\Pi x{:}A.,\Pi y{:}B(x).,\ldots$. Distinct subjects plus renaming up to $\alpha$ guarantee that $x$ in $B(x)$ is always the one declared earlier, and that applying the substitution lemma never captures a variable.

## Summary

Capture is avoided by combining three things:

1. Contexts act as binders for free variables.
2. Their subjects are kept distinct and fresh.
3. The Barendregt convention lets you rename bound variables whenever needed.
___

### About the Freshness Conditions

> Explain the Freshness conditions, What I understand is that the abstraction rule takes out a free variable name from context for converting it to a bound variable in the lambda abstraction, right?


**Claude:** Yes, with one refinement: the variable is _discharged_ from the context, and freshness is the condition that makes this unambiguous.

## Reading the rule

$$\dfrac{\Gamma,\ x{:}A \vdash M : B}{\Gamma \vdash \lambda x{:}A.,M : \Pi x{:}A.,B}\ (\mathsf{abst})$$

- **Premise:** $x$ is a subject of the context, so it acts as a free variable of $M$ with assumed type $A$.
- **Conclusion:** $x{:}A$ has left the context. The binder $\lambda x{:}A$ in the term now plays the role of that declaration, so $x$ is no longer free in $\lambda x{:}A.,M$.

So the declaration $x{:}A$ moves from the context into the term. The type $A$ also moves, into the binder annotation and into the $\Pi$-type. What was a hypothesis ("assume $x$ has type $A$") becomes a function ("for any $x$ of type $A$").

## What the freshness condition says

In the premise $\Gamma, x{:}A$ must be a legal context, which means

$$x \notin \operatorname{dom}(\Gamma)$$

that is, $x$ is not already a subject of $\Gamma$. The condition is on the premise, because that is where the context is extended. Reading the rule bottom-up when building a derivation, you can only add $x{:}A$ if $x$ is not already declared.

## Why it is needed

Suppose $\Gamma = y{:}C$ and you want to type $\lambda y{:}A.,y$. The premise would need the context $y{:}C,\ y{:}A$, which has two declarations with the same subject. Then a later occurrence of $y$ could refer to either, and the type of $y$ would be ambiguous.

Barendregt's convention is the escape hatch. Since $\lambda y{:}A.,y \equiv_\alpha \lambda z{:}A.,z$, you rename the bound variable to a fresh $z$ and the premise becomes $y{:}C,\ z{:}A \vdash z : A$, which is fine. The conclusion is the same function up to $\alpha$-equivalence. The condition is therefore never a real restriction on which terms are typable, because you can always rename.

## The same condition elsewhere

The start rule, which gives $\Gamma, x{:}A \vdash x : A$, and the weakening rule, which adds a declaration unrelated to the judgment, carry the same condition. Every place a context grows requires the new subject to be fresh. This maintains the invariant that all subjects in a context are pairwise distinct, and the invariant is what makes "context subjects act as binders for the free variables" well defined.

If it helps, I can work through a full derivation of something like $\vdash \lambda x{:}A.,\lambda y{:}B.,x : A \to B \to A$, showing the context growing and then being discharged one declaration at a time.


____

> What if binders in lambda terms, have a distinct syntax rule that differentiates them from free variables in the context ? F.E. a grammar rule that imposes a prefix symbol on every free variable telling that every $v \in FV(\Gamma)$ should start with the symbol `@`, and every bound variable at lambda terms should start with alphabetic letters like `y`, `a`etc. 
> So if there is a lambda term declared as $\gamma y:A.M$, it won't collide with another `y` in $\Gamma$ since the most similar free variable would be named as `@y:B` .

What you describe is a real technique. It is the old distinction between **parameters** and **bound variables** (Gentzen's eigenvariables in predicate logic). Modern formalizations call it a _two-sorted_ or _locally nameless_ presentation (McKinna and Pollack, and later Charguéraud). It does remove the specific clash you describe, but it doesn't remove the need for something like the Barendregt convention. I'll show what changes and what remains.

## What the grammar becomes

There are two syntactic classes of variables:

- parameters $@x, @y, \ldots$, which are the only things allowed as subjects of a context
- bound variables $x, y, \ldots$, which only appear under a binder

Then $@y{:}B \in \Gamma$ and $\lambda y{:}A.,M$ cannot collide, as you say.

## The abstraction rule has to change

The rule can no longer simply move $x{:}A$ from the context into the binder, because the name in the context ($@x$) is a different symbol from the name in the binder ($x$). The rule needs an explicit conversion step:

$$\dfrac{\Gamma,\ @x{:}A \vdash M : B}{\Gamma \vdash \lambda y{:}A.,M[@x := y] : \Pi y{:}A.,B[@x := y]}\ (\mathsf{abst})$$

Reading it bottom-up, the term in the conclusion is obtained from $M$ by _closing_ it: the parameter $@x$ is replaced by a bound variable. Reading it top-down, to type a $\lambda$ you _open_ its body by replacing the bound variable with a fresh parameter and then extend the context with that parameter. This is the locally nameless idea: parameters name the hypotheses, and binders are for the abstraction.

## What it fixes

The statement "subjects of the context bind the free variables" becomes literally true, because the free variables of a term are exactly the parameters, and these are exactly the context's subjects. Substitution of a parameter, $M[@x := N]$, can never be captured. No binder in $M$ uses a parameter name, so no binder can ever bind a variable that arrives from $N$.

## What it does not fix

**1. Freshness is still needed.** You still need $@x \notin \operatorname{dom}(\Gamma)$ in the premise. Two declarations $@x{:}A, @x{:}B$ would be just as ambiguous as before. The rule for choosing a fresh parameter name is now trivial, since you only have to avoid other parameters.

**2. Bound variables can still capture each other.** Consider substituting for a _bound_ variable, as $\beta$-reduction does. Suppose we reduce under a binder:

$$\lambda z.,(\lambda y.,\lambda z.,y),z ;\to_\beta; \lambda z.,\lambda z.,z$$

Here $\lambda y.\lambda z.y$ applied to $z$ should give a function that returns the _outer_ $z$. The result instead returns the inner one, so it is wrong. The syntactic prefix doesn't help, because both $z$'s are bound variables. This is the same capture problem, one level up.

The locally nameless approach avoids it with a discipline: _never reduce or substitute under a binder with an exposed bound variable_. Whenever you enter a binder you first open it, replacing the bound variable with a fresh parameter. Then every term you substitute is locally closed (it has no loose bound variables), and capture cannot happen. Barendregt's convention does the same job informally, by renaming the bound variables so they differ from all free ones.

**3. $\alpha$-equivalence of binders remains.** Is $\lambda y{:}A.,y$ the same as $\lambda a{:}A.,a$? You either quotient by $\alpha$-conversion, which is the book's approach, or you use de Bruijn indices for bound variables, which is the "nameless" part of locally nameless. In the latter case $\alpha$-equivalent terms are syntactically identical, and the bound variable names (the alphabetic letters in your proposal) disappear.

## Trade-offs

||Book (one sort + Barendregt)|Two-sorted / locally nameless|
|---|---|---|
|Free vs. bound clash|avoided by renaming|impossible by syntax|
|Bound vs. bound clash|avoided by renaming|avoided by opening binders|
|Abstraction rule|simple|needs open/close operations|
|Metatheory proofs|informal, readable|more rigorous, more bookkeeping|

The book's choice is pedagogical. It keeps the rules short and delegates renaming to the convention. Two-sorted presentations pay for their rigor with more machinery in each rule, which is why they appear mostly in formalizations in proof assistants.


## A correction on "α-conversion"

Turning a parameter $@y$ into a bound variable is not α-conversion. α-conversion renames a variable that is _already bound_. Abstraction is a different operation, usually called **closing** (or _binding_):

$$M ;\longmapsto; M[@y := y]$$

and its inverse is **opening**, which replaces a bound variable with a fresh parameter. α-conversion enters only when the name you want is taken. For example, if $@y$ is already in $\Gamma$, you pick a different parameter $@y'$ to open the binder, and the resulting term is α-equivalent to the original. So freshness becomes a choice of parameter name at opening time, and the bound name in the binder is irrelevant.

## Composing abstractions

You're right that composing abstractions needs a procedure for the internal terms. With named bound variables, building $\lambda x{:}A.,\lambda y{:}B.,M$ means closing $M$ in two stages:

$$M ;\to; M[@y := y] ;\to; (M[@y := y])[@x := x]$$

Closing $@x$ must not touch the $y$ already introduced, and the bound names $x, y$ must be distinct. So you still need a renaming discipline for bound names, which is the part that locally nameless leaves unsolved by syntax alone and that the Barendregt convention handles informally.

## Why de Bruijn indices remove this

With indices, a variable is a number counting the binders between it and its own binder. For example:

$$\lambda x{:}A.,\lambda y{:}B.,x ;;\rightsquigarrow;; \lambda A.,\lambda B.,1$$

(counting from $0$). Now:

- α-equivalent terms are syntactically identical, so there is no renaming.
- Freshness side conditions disappear, since there are no names to clash.
- The context is just a list of types, and the abstraction rule becomes

$$\dfrac{A \cdot \Gamma \vdash M : B}{\Gamma \vdash \lambda A.,M : \Pi A.,B}\ (\mathsf{abst})$$

where $A \cdot \Gamma$ means $A$ is pushed on the front of $\Gamma$.

## What you pay instead

The name bookkeeping becomes **shifting** bookkeeping.

**1. Substitution must shift indices.** When a term is moved under a binder, its free indices must be incremented so they keep pointing at the same declarations. β-reduction is

$$(\lambda A.,M),N ;\to_\beta; \uparrow^{-1}\big(M[0 := \uparrow^{1} N]\big)$$

where $\uparrow^{k}$ shifts the free indices by $k$.

**2. The variable rule must shift types.** In a dependent system, the type stored in the context lives in the prefix of the context that follows it, so when you use it you must shift it into the current context:

$$\dfrac{\Gamma(k) = A}{\Gamma \vdash k : \uparrow^{k+1} A}\ (\mathsf{var})$$

**3. Readability and off-by-one errors.** Terms are hard for humans to read, and errors in shift amounts are the classic failure mode in formalizations.

## What real systems do

Systems compromise. The Coq kernel uses de Bruijn indices for bound variables. Lean's kernel is locally nameless: bound variables are de Bruijn indices, and free variables (parameters) are named. This is your two-sorted idea with the bound side made nameless, so it gets α-equivalence for free while keeping contexts readable and opening/closing simple.

For a textbook, Nederpelt and Geuvers choose named variables plus the Barendregt convention. The reason is exposition: the rules look like the mathematics people actually write. For a formalization in a proof assistant, your conclusion is the usual one, and locally nameless or de Bruijn representations are the practical choice.

___

