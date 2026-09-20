In Martin-Löf’s Type Theory (MLTT), Per Martin-Löf (drawing on Frege's notions of "functionality" and "unsaturated expressions") introduced **arities** at the purely syntactic level to avoid the unnatural consequences of unrestricted expression-building found in untyped combinatory logic.

### Why Every Expression Must Carry an Arity

1. **Ensuring Decidability of Definitional Equality:** In MLTT, checking the validity of a derivation step (such as matching an implicand in a rule) requires that **definitional (intensional) equality** (\(\equiv\)) be decidable and that definitions be completely eliminable. Unrestricted syntactic frameworks, like combinatory logic, fail to guarantee this.
2. **Establishing Grammatical Categories:** Rather than treating all expressions under a single category, arities divide raw syntax into distinct categories indicating which operations are applicable. Expressions are divided into:
    - **Saturated expressions** (single, complete objects that cannot be further applied or selected from, carrying arity \(0\)).
    - **Combined expressions** (carrying product arities \(\alpha_1 \otimes \dots \otimes \alpha_n\), allowing component selection).
    - **Unsaturated expressions** (carrying operator arities \(\alpha \to \beta\), allowing application to an argument of arity \(\alpha\)).
3. **Preventing Syntactic Nonsense:** Without arity restrictions, one could syntactically apply a single-argument operator to multiple arguments—producing nonsensical trees like \(succ(x_1, x_2, x_3)\)—or select components from a non-combined expression.

---

### How Arity Rules Out Ill-Formed Expressions Like \(succ(succ)\)

The system prevents ill-formed expressions through a rigid, inductive **application rule**: $$\text{If } d : \alpha \to \beta \quad \text{and} \quad a : \alpha, \quad \text{then } d(a) : \beta$$
 Every variable and primitive constant is assigned a unique, fixed arity. Under this rule:

- The successor constant \(succ\) is defined as an unsaturated operator with the arity **\(0 \to 0\)** (meaning it expects an argument of arity \(0\) and yields a result of arity \(0\)).
- In the proposed expression \(succ(succ)\), the first \(succ\) acts as the operator (\(d\)) and the second \(succ\) acts as the argument (\(a\)).
- For this application to be well-formed, the argument \(a\) must match the expected domain arity (\(\alpha\)) of the operator. Since the operator \(succ\) has arity \(0 \to 0\), it expects an argument of arity **\(0\)**.
- However, the argument (\(succ\)) is itself an unsaturated constant with the arity **\(0 \to 0\)**, which is syntactically distinct from \(0\).

Because the arity of the argument (\(0 \to 0\)) does not match the expected domain arity of the operator (\(0\)), the application rule cannot be applied. Consequently, **\(succ(succ)\) is rejected at the very base of the syntax** and cannot be formed as a valid expression in the language.

---
