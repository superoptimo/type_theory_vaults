In Martin-Löf's Type Theory (MLTT), syntax is handled through a rigorous, two-level approach: first, by establishing a general, uniform theory of mathematical expressions at the purely syntactic level, and second, by inextricably linking the well-formedness of types to typing derivations.

The details of how MLTT structures and manages syntax are outlined below.

---

### 1. The General Theory of Expressions and Arities

Rather than specifying syntax solely for type-theoretic terms, Per Martin-Löf formulated a **uniform, general theory of mathematical expressions**.

- **Arities instead of Single Categories**: Unlike systems like combinatory logic that utilize a single syntactic category of expressions, MLTT divides expressions into different categories based on their **arities**. Inspired by Frege's notion of "functionality," an arity dictates which syntactic operations are applicable to an expression. Formally, these arities act like types in a typed \(\lambda\)-calculus, but they operate strictly at the level of raw syntax.
- **Inductive Formation**: Expressions of a certain arity are built up inductively from variables and primitive constants (each carrying a designated arity). The syntax defines five ways to form these expressions:
    1. **Variables**: A variable \(x\) of arity \(\alpha\) is a syntactic expression of arity \(\alpha\).
    2. **Primitive Constants**: A constant \(c\) of arity \(\alpha\) is an expression of arity \(\alpha\).
    3. **Defined Constants (Macros)**: If a defined abbreviation's right-hand side (_definiens_) is an expression of arity \(\alpha\), its left-hand side (_definiendum_) is also of arity \(\alpha\).
    4. **Application**: If \(d\) is an expression of arity \(\alpha \to \beta\) and \(a\) is an expression of arity \(\alpha\), then the application \(d(a)\) is an expression of arity \(\beta\).
    5. **Abstraction**: If \(b\) is an expression of arity \(\beta\) and \(x\) is a variable of arity \(\alpha\), then \((x)b\) is an abstraction of arity \(\alpha \to \beta\).

---

### 2. Decidable Definitional Equality

The raw syntax is governed by a strict notion of **definitional (or intensional) equality** (\(\equiv\)).

- This combinatory equality is defined for expressions of a given arity and includes standard equivalence properties (reflexivity, symmetry, transitivity) and computation rules like the \(\beta\)-rule for abstractions.
- Crucially, to prevent arbitrary or non-terminating expansions during syntactical checking, definitional equality must be algorithmically decidable, and definitions (macros) must be eliminable.

---

### 3. Syntactic Abstractions vs. Type-Theoretic Functions

MLTT maintains a sharp conceptual distinction between the syntactic structure of a function and its type-theoretic representation:

- **Syntactic Abstraction**: This is the basic syntactic notion of a function, defined as "an expression with holes in it" (an unsaturated expression). Abstractions are used at the very base of the syntax to write down type constructors themselves, such as when formulating the dependent product \(\Pi(A, B)\) or the function space \(A \to B\).
- **Function Element**: This is an actual element residing inside a type-theoretic set (such as a member of the cartesian product \(\Pi(A, B)\) or the function set \(A \to B\)).

---

### 4. Inextricable Mixing of Syntax and Derivations

In simple type systems, one can define the syntax of formulas independently of the rules of derivation. In MLTT, however, the **syntax of types and formulas is inextricably mixed with typing derivations**.

- Because MLTT supports dependent types, the grammatical well-formedness of certain types depends on whether terms inhabit other types.
- For example, the identity type \(I(A, a, b)\) (the proposition that \(a\) and \(b\) are equal elements of the type \(A\)) is only grammatically well-formed if \(a\) and \(b\) are first derived as valid terms of type \(A\). Thus, one cannot generate the syntax of types separately from the typing derivations of the system.

---

### 5. Internalizing Syntax Trees (The `Tree` Constructor)

To represent syntax trees and mutually dependent grammars _internally_ within the type theory, Martin-Löf introduced the `Tree` set constructor. This constructor models the components of a context-free grammar directly as type-theoretic elements:

- Non-terminals are represented by a set of names \(A\).
- The alternative productions defining a non-terminal \(x\) are named by a set \(B(x)\).
- The positions of non-terminals in a production alternative \(y\) are named by a selector family \(C(x, y)\).
- The specific non-terminal corresponding to a position \(z\) in an alternative \(y\) is identified by \(d(x, y, z)\).
- The start symbol of the grammar is represented by a term \(a\).

---

💡 **Would you like to explore how Martin-Löf’s semantic judgements (such as showing that a type is a well-formed set) are built on top of this syntactic foundation?**