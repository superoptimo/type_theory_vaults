---
title: The Syntax of TLA+
book: Specifying Systems (Leslie Lamport)
chapters: "Chapter 15, pp. 275–290 (with the ASCII/typeset correspondence from Chapter 2, §2.4, pp. 19–20)"
tags: [tla+, syntax, grammar, bnf, formal-methods, parsing]
---

[[book-guidelines|↩ Back to guidelines]]

## Why TLA+ needs a chapter on syntax at all

Most books that teach a specification language spend a paragraph on syntax and move on, because most specification languages are small, purpose-built grammars where "well-formed" is easy to pin down. TLA+ is different in a way that has real consequences for anyone who wants to *parse* it (which, per this book's own emphasis on mechanism, is exactly the reading you should be doing): it deliberately imitates the richness of ordinary handwritten mathematical notation — juxtaposed subscripts, unterminated `if`/`then`/`else`, indentation-sensitive lists, operators with no fixed precedence number — instead of the clean, terminator-delimited style of a programming language. Lamport is explicit about the trade he's making: readability for the working engineer costs the tool-builder a much more irregular grammar.

That trade shows up as a two-layer definition of "syntactically correct":

- **The computer scientist's syntax** — is this token sequence (with its layout) generable by the grammar, independent of whether any identifier in it is actually defined? This is what Chapter 15 covers, and what a parser front-end like `SANY` checks first.
- **The mathematician's syntax** — is every identifier in the expression actually defined or declared in the surrounding context? Lamport calls this a *semantic* condition (Chapters 16–17), even though a mathematician would call an expression referencing an undefined symbol simply "meaningless," not "syntactically fine but semantically broken."

This article is about the first layer only — grammatical well-formedness — because that's genuinely separable from meaning, and TLA+'s own reference grammar treats it that way.

**What breaks without this separation:** if you tried to build one BNF grammar that simultaneously rejected `⟨a, a⟩` when `a` is undefined *and* decided operator precedence *and* decided which `⟨A⟩_x` binds tighter, you'd end up with a grammar formalism that's really a full type/scope checker wearing a BNF costume. Keeping layers separate is what lets Chapter 15's grammar be a genuine, checkable, non-Turing-complete artifact — and it's the same layering a real compiler front-end uses: lexer → parser (pure grammar) → name resolution/typechecking (semantics). If you're building a Rust front-end for a similar language, this chapter is effectively specifying your `lexer.rs` and `parser.rs` boundary, with `resolve.rs`/`typeck.rs` left for later chapters.

## ASCII versus typeset notation

TLA+ has always had two renderings of the same underlying language: the **typeset** form (using real mathematical symbols: $\land$, $\in$, $\Rightarrow$, $\Box$) that appears throughout this book, and the **ASCII** form, which is the *only one that actually exists as source text* — you cannot type $\in$ on a keyboard, so every TLA+ file on disk is ASCII, and the typeset version is something a tool (`TLATEX`, Chapter 13) derives from it.

The book introduces this correspondence early, in §2.4, using the hour-clock module as the first worked example:

```
---------------------- MODULE HourClock ----------------------
EXTENDS Naturals
VARIABLE hr
HCini == hr \in (1 .. 12)
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1
HC == HCini /\ [][HCnxt]_hr
--------------------------------------------------------------
THEOREM HC => []HCini
================================================================
```

which typesets as $\mathit{HCini} \triangleq hr \in (1\,..\,12)$, $\mathit{HCnxt} \triangleq hr' = (\text{if } hr \neq 12 \text{ then } hr+1 \text{ else } 1)$, $HC \triangleq \mathit{HCini} \land \Box[\mathit{HCnxt}]_{hr}$, and $\vdash HC \Rightarrow \Box \mathit{HCini}$.

Three correspondence rules, stated in the book almost as a decoder key:

1. **Reserved words** shown typeset in small caps (`module`, `extends`, `variable`, `theorem`) become ordinary upper-case ASCII keywords (`MODULE`, `EXTENDS`, `VARIABLE`, `THEOREM`).
2. **When a pictorial ASCII rendering exists, use it.** $\Box$ becomes `[]` (a literal picture of a box); $\neq$ becomes `#` (or `/=`); $\lor$ becomes `\/`, $\land$ becomes `/\` (both are meant to look like the symbol they replace, rotated slightly for ASCII art).
3. **When there's no good pictorial option, fall back to TeX-style backslash escapes.** $\in$ becomes `\in`, $\forall$ becomes `\A`, $\exists$ becomes `\E`. The one deliberate exception is the definition symbol $\triangleq$ ("is defined to equal"), which is written `==` rather than something like `\deq` — frequent enough to deserve its own pictorial-ish shorthand instead of an escape.

The book's Table 8 (p. 273) is the exhaustive lookup table for every symbol; this three-rule breakdown is what lets you *predict* an unfamiliar symbol's ASCII spelling instead of having to memorize the whole table.

**[[Elementary-Mathematical-Foundations-for-Specification#Grounding|Grounding]] — this is exactly a lexer's symbol table.** In Rust terms, this correspondence is nothing more than the mapping a `Token` enum's `Display` impl (or its reverse, a keyword/symbol trie in the lexer) would encode:

```rust
enum Token {
    And,        // typeset ∧,  ascii /\
    Or,         // typeset ∨,  ascii \/
    Box_,       // typeset □,  ascii []
    Neq,        // typeset ≠,  ascii # or /=
    In,         // typeset ∈,  ascii \in
    Forall,     // typeset ∀,  ascii \A
    DefEq,      // typeset ≜,  ascii ==
    // ...
}
```

The interesting engineering point buried in rule 2 vs. rule 3 is a lexer-design lesson: TLA+'s designers chose ASCII spellings to *minimize lexical ambiguity and maximize mnemonic value* — `[]` visually resembles a box, `\/` and `/\` visually resemble the symbols they stand for — rather than picking arbitrary short tokens. A hand-rolled lexer for a similar DSL should take the same care: good ASCII surface syntax is a a genuine (if easily dismissed) usability decision, not an afterthought.

## Module structure and the BNF grammar

The chapter's formal centerpiece is a TLA+ module named `TLAPlusGrammar`, itself written using a small grammar-description module (`BNFGrammars`, introduced back in §11.1.4) — TLA+'s grammar is specified *in TLA+ itself*, treating a grammar as a value: a set of sentences (sequences of lexemes) closed under a system of production rules, computed as `LeastGrammar(P)` — the smallest grammar satisfying the given equations. This is worth pausing on: `LeastGrammar` is a fixed-point construction (the *least* set of sentences closed under the productions), exactly analogous to how an inductive datatype in Lean is the least type closed under its constructors.

**BNFGrammars vocabulary used throughout:**

| Notation | Meaning |
|---|---|
| $L \mathbin{\vert} M$ | sentence is an $L$ or an $M$ |
| $L^{*}$ | zero or more concatenated $L$'s |
| $L^{+}$ | one or more concatenated $L$'s |
| $L \mathbin{\&} M$ | concatenation (juxtaposition would be ambiguous, so `&` is explicit) |
| $\mathit{Nil}$ | the empty sentence, so $\mathit{Nil} \mathbin{\&} L = L$ |
| $\mathrm{tok}(s)$ | the singleton set containing the one-lexeme token $\langle s \rangle$ |
| $\mathrm{Tok}(S)$ | tokens $\langle s \rangle$ for every lexeme $s \in S$ |

Two derived helpers appear constantly:

$$\mathit{CommaList}(L) \triangleq L \mathbin{\&} (\mathrm{tok}(\text{","}) \mathbin{\&} L)^{*}$$

(an $L$, or several $L$'s separated by commas — this is why every comma-separated construct in TLA+, from `VARIABLE x, y, z` to function-set arguments, is really one grammar idiom reused everywhere), and `AtLeast4("-")`, which generates the `----` (four-or-more dashes) module-boundary marker.

**Module structure**, as an actual production:

$$G.\mathit{Module} ::= \mathrm{AtLeast4}(\text{"-"}) \mathbin{\&} \mathrm{tok}(\text{"MODULE"}) \mathbin{\&} \mathit{Name} \mathbin{\&} \mathrm{AtLeast4}(\text{"-"})$$
$$\mathbin{\&} (\mathit{Nil} \mathbin{\vert} \mathrm{tok}(\text{"EXTENDS"}) \mathbin{\&} \mathit{CommaList}(\mathit{Name}))$$
$$\mathbin{\&} (G.\mathit{Unit})^{*} \mathbin{\&} \mathrm{AtLeast4}(\text{"="})$$

In prose: a module is `----`, `MODULE`, a name, `----`, an optional `EXTENDS` clause, zero or more *units*, and a closing `====`. A **unit** is one top-level statement: a variable/constant declaration, an operator/function definition, an `INSTANCE` statement, a module definition, an `ASSUME`, a `THEOREM`, a nested module, or a bare `----` divider (purely cosmetic, as seen after the hour-clock's theorem). This is precisely a compiler's *item* concept — the things that can appear at top level in a translation unit — and the grammar spells that out as an explicit alternation, which is exactly how you'd encode it as a Rust `enum Item { VarDecl(..), ConstDecl(..), OpDef(..), Instance(..), Theorem(..), .. }`.

**Grounding — Lean.** Because `TLAPlusGrammar` is defined as a *least fixed point* of a system of set-equations (`LeastGrammar(P)`), it is structurally the same object as an inductively-defined family in Lean:

```lean
inductive Expr : Type
  | ident   : String → Expr
  | apply   : Expr → List Expr → Expr
  | prefixOp : String → Expr → Expr
  | infixOp  : Expr → String → Expr → Expr
  | ite      : Expr → Expr → Expr → Expr
  -- ...
```

The BNF alternation `|` is Lean's constructor alternation, `&` (concatenation) is a constructor's positional arguments, and `*`/`+` are `List`/nonempty-`List`-typed fields. The one real disanalogy is that TLA+'s grammar is a grammar over *token sequences with position information* (row/column matter — see Alignment, below), whereas an ordinary Lean inductive type has no notion of "column," so the correspondence is exact only for the alignment-insensitive fragment of the grammar (§15.1's "simple grammar").

## Lexemes, tokens, and reserved words

Before any grammar production can fire, the character stream has to become a **lexeme stream**. A *lexeme* is an atomic character sequence like `|->`; a *token* is a one-lexeme sentence, written $\langle s \rangle$. The book is careful to keep these two levels distinct because TLA+'s lexer rule is unusually simple and unusually important:

> The next lexeme begins at the next text character that is not part of a comment, and consists of the *largest* sequence of consecutive characters that form a legal TLA+ lexeme.

This is the **maximal-munch** rule familiar from every hand-written lexer (it's why `<=` lexes as one token, not `<` followed by `=`), and TLA+ needs one specific, deliberate *exception* to it, discussed below under reserved words.

**Reserved words** — thirty-odd identifiers that can never be used as user-defined names: `ASSUME`, `ASSUMPTION`, `AXIOM`, `CASE`, `CHOOSE`, `CONSTANT(S)`, `DOMAIN`, `ELSE`, `ENABLED`, `EXCEPT`, `EXTENDS`, `IF`, `IN`, `INSTANCE`, `LET`, `LOCAL`, `MODULE`, `OTHER`, `SF_`, `SUBSET`, `THEN`, `THEOREM`, `UNCHANGED`, `UNION`, `VARIABLE(S)`, `WF_`, `WITH`. Notably, `boolean`, `true`, `false`, and `string` are *not* reserved — they're ordinary predefined identifiers, meaning a (very unwise) specification could locally redefine `TRUE`. This is TLA+ staying maximally minimal: reserving a word is a real language-design cost (it shrinks the identifier namespace forever), so Lamport reserves only what the *grammar itself* needs to disambiguate, not everything that happens to have a fixed meaning.

**Names and identifiers**, formally:

$$\mathit{Letter} \triangleq \mathrm{OneOf}(\text{"a...zA...Z"}) \qquad \mathit{Numeral} \triangleq \mathrm{OneOf}(\text{"0...9"}) \qquad \mathit{NameChar} \triangleq \mathit{Letter} \cup \mathit{Numeral} \cup \{\text{"\_"}\}$$

$$\mathit{Name} \triangleq \mathrm{Tok}\big((\mathit{NameChar}^{*} \mathbin{\&} \mathit{Letter} \mathbin{\&} \mathit{NameChar}^{*}) \setminus (\{\text{"WF\_"},\text{"SF\_"}\} \mathbin{\&} \mathit{NameChar}^{+})\big)$$

$$\mathit{Identifier} \triangleq \mathit{Name} \setminus \mathrm{Tok}(\mathit{ReservedWord})$$

A `Name` is any letters/digits/underscore string containing at least one letter — *except* one that begins with (but isn't exactly) `WF_` or `SF_`. That set-subtraction is the maximal-munch exception mentioned above: without it, the lexer would greedily swallow `WF_x` as one 4-character `Name` lexeme, and then `WFx(A)` — the fairness-formula syntax $WF_x(A)$ — could never be parsed as the four separate pieces `WF_`, `x`, `(`, `A`, `)` that the grammar's `WF_`/`SF_` production expects. The one-line fix (subtract those two prefixed families out of `Name`, and separately reserve `WF_`/`SF_` as their own tokens) is a small, elegant patch to maximal munch precisely at the one place ordinary greedy lexing would silently swallow a needed token boundary.

**Grounding — the corresponding lexer code.** In Rust, this is the classic "identifier-vs-keyword" lexer branch, plus one extra special case:

```rust
fn lex_name(chars: &mut Peekable<Chars>) -> Token {
    let s: String = take_name_chars(chars); // greedy: letters, digits, '_'
    match s.as_str() {
        "WF_" | "SF_" => Token::FairnessPrefix(s),
        _ if s.starts_with("WF_") || s.starts_with("SF_") => {
            // back off: only the WF_/SF_ prefix is a lexeme,
            // the rest re-lexes as a fresh Name/Identifier
            unreachable!("excluded from Name by construction")
        }
        _ if RESERVED.contains(&s.as_str()) => Token::Keyword(s),
        _ => Token::Identifier(s),
    }
}
```

In practice you wouldn't hit the greedy case at all if, like TLA+'s own definition, you exclude `WF_`/`SF_`-prefixed strings from the `Name` lexeme class *before* running maximal munch — exactly what the set-difference in [[Real-Time-Specification#The formal definition|the formal definition]] does. This is a nice small case study in why "longest match" is a *default*, not a law: any lexer for a language with an ambiguous shared prefix between a keyword-like construct and ordinary identifiers needs the same kind of carve-out.

Two more token families round out the lexeme layer: **`Number`** literals (decimal `63`, `63.00`, or radix-prefixed `\b111111`/`\o77`/`\h3f` for binary/octal/hex) and **`String`** literals (`"foo"`, with escaping rules deferred to §16.1.10). And three disjoint token sets classify every built-in symbol by fixity: `PrefixOp` (`-`, `~`, `\lnot`, `[]`, `<>`, `DOMAIN`, `ENABLED`, `SUBSET`, `UNCHANGED`, `UNION`), a long `InfixOp` list (arithmetic, set, and named-symbol operators like `\cup`, `\subseteq`, `\o`), and `PostfixOp` (`^+`, `^*`, `^#`, and prime `'`). These sets are exactly what a Pratt/precedence-climbing parser needs as its dispatch tables — which is the natural segue into precedence itself.

## Operator precedence as a range, not a number

Ordinary parser textbooks assign each operator a single precedence integer. TLA+ deliberately does not: **every operator's precedence is a closed interval of integers**, e.g. `$` has precedence 9–13 while `:>` has precedence 7–7 (a "range" that happens to be a single point). Application order between two operators is well-defined only when their intervals don't overlap; the operator with the (entirely) higher interval binds tighter.

**What problem does a range solve that a single number doesn't?** It gives the grammar designer a principled way to make an expression outright *illegal* rather than force an arbitrary tie-break. If precedence were a single total order (as in almost every programming language, where `*` simply beats `+` and that's that), *every* pair of operators would have a defined relative order, including pairs where the "obvious" order is actually ambiguous to a human reader. TLA+ instead asks: do these two operators' ranges overlap? If they do (and they're not two uses of the same associative infix operator), the expression is rejected at parse time rather than silently resolved by an arbitrary rule the reader has to memorize.

Worked example from the book: $a + b * c' \mathbin{\%} d$. Since `'` (postfix) outranks `*`, which outranks both `+` and `%`, this reduces to $a + (b * (c')) \mathbin{\%} d$ — but `+` has range 10–10 and `%` has range 10–11, and those ranges *overlap*, so the expression is illegal: nothing tells you whether it means $(a + (b*(c')))\mathbin{\%}d$ or $a + ((b*(c'))\mathbin{\%}d)$. Similarly `*` and `/` overlap, so `a/b*c` is illegal even though `a*b/c` would be numerically unambiguous under the usual definitions — TLA+ doesn't know or care that `*` and `/` happen to associate nicely for numbers; the *syntax* layer can't see semantics, so it refuses on principle.

**What breaks without this design:** a single global precedence order would force TLA+ to make an arbitrary, non-obvious choice for operators like `$` — a user-definable infix symbol with no inherent mathematical meaning — and users would then have to memorize (or constantly look up) exactly where an unfamiliar operator sits relative to every other operator. Ranges let unconventional operators default to a *wide* range (so they clash with almost everything and force explicit parenthesization) without the language designer having to hand-pick one precise number for every possible pairwise interaction.

There are precedence special cases the range table alone doesn't capture:
- **Function application** is treated as an operator of range 16–16 — higher than everything except record-field `.` (period) — so `a + b.c[d]'` parses as $a + (((b.c)[d])')$.
- **Cartesian product `\X`/`\times`** acts like an *associative* infix operator of range 10–13 for interaction with other operators (so `A \X B \subseteq C` parses as `(A \X B) \subseteq C`), but is *not itself* associative as a construct: $A \times B \times C$, $(A\times B)\times C$, and $A \times (B \times C)$ denote three genuinely different sets (a set of triples vs. two different sets of nested pairs), so `A \X B \X C` is one indivisible parse-tree shape, not a left-fold of binary `\X`.
- **Subscript notation** — $[A]_e$, $\langle A \rangle_e$, $WF_e(A)$, $SF_e(A)$ — written with `_` in ASCII, has a genuinely ambiguity-prone corner: `<<A>>_x /\ B` could parse as $\langle A \rangle_{(x \land B)}$ instead of the intended $(\langle A \rangle_x) \land B$. The book's advice is pragmatic rather than grammatical: always parenthesize the subscript unless it's a bare identifier or already delimiter-enclosed.

**Grounding — precedence climbing / Pratt parsing in Rust.** A conventional precedence-climbing parser keys each operator to one `(u8, Associativity)` pair. TLA+'s range model asks for a small variant: store `(u8, u8)` (min, max) per operator, and *before* combining two adjacent operators, check interval disjointness rather than simple numeric comparison:

```rust
fn combine_ok(left: (u8, u8), right: (u8, u8), same_associative_op: bool) -> bool {
    if same_associative_op { return true; } // e.g. a - b - c, a /\ b /\ c
    let (l_lo, l_hi) = left;
    let (r_lo, r_hi) = right;
    l_hi < r_lo || r_hi < l_lo   // ranges must be disjoint (one strictly above the other)
}
```

A parser encountering two operators whose ranges overlap (and which aren't the same associative operator) should emit a *parse error*, not guess — which is a genuinely unusual, and genuinely nice, design decision for a language grammar to bake in structurally rather than leave to a linter.

**Undelimited constructs** compound the precedence story: `CHOOSE`, `IF`/`THEN`/`ELSE`, `CASE`, `LET`/`IN`, and the quantifiers have no closing keyword, so they're treated as prefix operators of the *lowest possible* precedence — they swallow everything until one of a small set of terminating lexemes (`THEN`, `ELSE`, `IN`, `,`, `:`, `→`, module-unit boundaries, unmatched delimiters, or — see Alignment below — a conjunction/disjunction-list boundary) is reached. So `∀x : P if x then A else B` — wait, more precisely, the book's own example: $\forall x \in S : P(x) \lor Q$ parses as $\forall x \in S : (P(x) \lor Q)$, because nothing terminates the quantifier's scope before the end of the whole expression. This is a deliberate readability trade: no `END` keyword clutters the source, at the cost of the scope-extension rule being something you have to learn once and then trust.

## Aligned conjunction and disjunction lists

This is, in the book's own words, "the most novel aspect of TLA+ syntax," and it's the syntax feature every TLA+ specification actually leans on visually:

```
Next ==
  \/ /\ x' = x + 1
     /\ y' = y
  \/ /\ y' = y + 1
     /\ x' = x
```

The rule: a conjunction list is an expression beginning with $\land$ (`/\`). Let $c$ be the *column* where that `/` character sits. Each conjunct runs until one of:

1. another `/\` whose `/` sits in column $c$ *and* is the first non-space character on its line — this starts the *next* conjunct in the same list;
2. any non-space character in column $c$ or to its left — this *ends the whole list*;
3. a right delimiter whose matching left delimiter precedes the list;
4. the start of the next module unit.

In other words: **column position, not an explicit terminator, is the delimiter.** This is genuinely unusual among mainstream grammars — it's closer to Python's or Haskell's *offside rule* for block structure than to anything in C-family or Lisp-family syntax, except that here it operates at the level of individual boolean conjuncts/disjuncts rather than whole statement blocks, and it composes with ordinary parenthesization rather than replacing it.

**What breaks without alignment sensitivity:** without a column rule, nested conjunction/disjunction lists like the `Next` example above would need explicit grouping — parentheses around every clause, or an infix-only rendering: `(x' = x+1 /\ y' = y) \/ (y' = y+1 /\ x' = x)`. For a `Next` action with a dozen top-level disjuncts, each itself a conjunction of a dozen sub-conditions (utterly ordinary in real specifications), that infix rendering becomes unreadable; the aligned bullet-list form is what makes large TLA+ actions actually scannable by eye, which is presumably why Lamport calls it the most novel part of the syntax rather than a footnote.

Two failure modes worth internalizing because they're exactly where a hand-rolled parser (or a careless human) gets bitten:

**Under-indentation collapses the list.** If a continuation conjunct places its `/` to the *left* of the list's own `/\`, the list ends early:

```
/\ x'
= y
/\ y'=x
```

Column rule 2 fires: `=` is a non-space character in a column left of (or equal to) $c$, so the first conjunction list ends right there — as `∧ x'`, a *single-conjunct* list — and everything after is reparsed as ordinary infix expression continuation (`= y`), then a second, unrelated `/\` acting as an *infix* $\land$. The result is not a parse error; it's a silently different (and wrong) parse tree, e.g. `((∧ x') = y) ∧ (y' = x)`.

**Robustness under small misalignment.** Off-by-one-space misalignment is graceful rather than catastrophic:

```
/\ A
/\ B
/\ C
```
with `B`'s `/` one column left of `A`'s and `C`'s `/` one column right — this still evaluates to something logically equivalent to $A \land B \land C$, even though the *parse tree* the grammar assigns is a lopsided nest of a one-conjunct list infix-`∧`-ed with the next. The book is explicit that this robustness is a deliberate design property, not an accident: typos in long conjunction lists are common (these lists can run to dozens of lines in real specs), and the grammar is engineered so that plausible typos still parse to the logically intended formula even when the *literal* parse tree the alignment rule computes looks different from what you'd draw by hand.

**Tabs are explicitly discouraged** because a tab occupies an unspecified number of columns beyond "the same leading tab/space sequence occupies the same number of columns as an identical sequence elsewhere" — mixing tabs and spaces in a conjunction list's leading whitespace can silently misalign or realign conjuncts.

**Grounding — implementing an offside-style delimiter.** A parser for this feature needs to track `(line, column)` for every token (not just token identity — this is the one place where TLA+'s grammar genuinely isn't a pure BNF grammar over a token stream), and treat the recorded column of a leading `/\`/`\/` as a piece of parser *state* that a recursive-descent conjunct-parsing loop consults on every new line:

```rust
fn parse_conjunction_list(p: &mut Parser) -> Expr {
    let col = p.peek_col(); // column of the '/' in the first '/\'
    let mut conjuncts = vec![parse_one_conjunct(p, col)];
    while p.peek_is_infix_and_op() == Some(Token::And)
        && p.peek_col() == col
        && p.is_first_nonspace_on_line()
    {
        p.advance();
        conjuncts.push(parse_one_conjunct(p, col));
    }
    Expr::And(conjuncts)
}

fn parse_one_conjunct(p: &mut Parser, list_col: usize) -> Expr {
    // parse an expression, but any token at column <= list_col
    // (that isn't a matching '/\' starting the next conjunct)
    // terminates this conjunct's extent, not just its own subexpression.
    parse_expr_bounded(p, list_col)
}
```

This is a real instance of *layout-sensitive parsing*, the same family of technique used for Python's and Haskell's indentation rules — except TLA+'s version is unusually local (per-list, not per-block) and unusually forgiving (robust-under-misalignment is a stated design goal, not an incidental property).

## Comment forms and typesetting conventions

Two comment forms, both introduced back in §3.5 and formalized here:

- **Delimited comments** `(* ... *)`, defined *recursively*: a delimited comment is `(*`, then zero or more pieces each either (a) plain text containing neither `(*` nor `*)`, or (b) a nested delimited comment, then `*)`. Nesting is exact and matched — `(* (* inner *) still commented *)` is one comment, not two.
- **End-of-line comments** `\* ...` running to the end of the physical line.

The nestable-block-comment choice matters practically: it lets you comment out a chunk of a specification that itself already contains `(* ... *)` comments, without having to hunt down and strip the inner ones first — a genuine convenience most C-family languages (with non-nesting `/* */`) deny you.

There's a neat typesetting-versus-grammar distinction the book flags explicitly with this example:

```
BufRcv == /\ InChan!Rcv                              (*********************************)
          /\ q' = Append(q, in.val)                  (* Receive message from channel *)
          /\ out                                     (* 'in' and append to tail of q. *)
                                                       (*********************************)
```

*Grammatically*, this is four distinct, unrelated delimited comments (two of them the identical `(***...***)` border string). A human reader, and `TLATEX`, both treat it as one visual box spanning four lines. The lesson: TLA+'s comment *grammar* only has to define what a legal comment lexeme is; the "this reads as one logical comment" convention lives entirely in typesetting/formatting tooling, not in the language's syntax. `TLATEX` (Chapter 13) preserves meaningful alignment when it typesets a specification — it treats zero and one space between symbols as equivalent, but faithfully reproduces genuinely intentional spacing like the comment-box example above.

**Grounding — Python.** A five-line sketch of the recursive nested-comment lexer, since Rust's ceremony would obscure the (genuinely simple) point here:

```python
def skip_delimited_comment(src, i):
    assert src[i:i+2] == "(*"
    depth, i = 1, i + 2
    while depth > 0:
        if src[i:i+2] == "(*": depth += 1; i += 2
        elif src[i:i+2] == "*)": depth -= 1; i += 2
        else: i += 1
    return i
```

## Syntactic anomalies in parsing

The chapter closes by naming two genuine ambiguities in the grammar, both given ad hoc (not principled) resolutions — worth knowing precisely *because* they're the two places TLA+'s grammar isn't fully context-free-clean, and any parser implementation has to special-case them by hand rather than derive the behavior from a general rule.

**Anomaly 1 — bare `-` versus `-.`.** `-` is used both as an infix operator (`2 - 2`) and a prefix operator (`2 + -2`). Inside an ordinary expression this is never ambiguous (the grammar production position tells you which one is meant), but there are two contexts where an operator symbol appears *by itself*, with no operand to disambiguate it:

- as the argument of a higher-order operator: `HOp(+, -)`
- in an instance substitution: `INSTANCE M WITH Plus <- +, Minus <- -`

In both, bare `-` is resolved as the *infix* minus; you must write `-.` to name the *prefix* minus operator, and `-.` is likewise required if you ever define a new prefix-minus-shaped operator yourself:

$$-.\,a \triangleq \mathit{UMinus}(a)$$

In an ordinary expression, though, you just type `-` for both roles as usual — the special two-character spelling `-.` is needed *only* in the "operator named without an operand" positions.

**Anomaly 2 — `{x \in S : y \in T}`.** This unusual-looking expression is syntactically ambiguous between two legitimate readings of the set-builder grammar:

$$\text{let } p(x) \triangleq y \in T \text{ in } \{x \in S : p(x)\} \qquad\text{(a subset of } S\text{)}$$
$$\text{let } p(y) \triangleq x \in S \text{ in } \{p(y) : y \in T\} \qquad\text{(a subset of } \textit{boolean}\text{)}$$

TLA+ resolves this in favor of the first reading — it's always parsed as the *subset-of-$S$* form. Since `{x \in S : y \in T}` is a genuinely unlikely thing to write on purpose (you'd almost never want a set of Booleans built this way), the resolution is really "pick the reading that matches the far more common idiom" rather than an argument from any deep grammatical principle.

**Why call these "anomalies" rather than just "rules"?** Because unlike precedence ranges or the alignment column rule — general mechanisms that predict behavior for *any* expression built the same way — these two are irreducibly one-off patches: a context-sensitive lookup ("is this operator symbol standing alone with no operand?") and an arbitrary tie-break between two grammatically equal parses. A real parser implementation has to hard-code exactly these two checks; no amount of generalizing the precedence or alignment machinery would derive them for free. This is a useful, honest admission from the language designer: even a syntax this carefully engineered ends up with a couple of irreducible special cases, and knowing exactly where they are (rather than being surprised by them at parse time) is worth more than pretending the grammar is perfectly uniform.

## Where this leads

Chapter 15's grammar is the direct ancestor of everything Part IV builds: Chapter 16's formal semantics assigns *meaning* to exactly the expressions this grammar accepts, and Chapter 17's legality conditions add the "mathematician's syntax" layer (identifier scoping, level-correctness of temporal formulas) that Chapter 15 explicitly declines to check. Practically, this chapter *is* the specification of `SANY`'s parser front end (Chapter 12) — a syntax error is, by the book's own definition, exactly a violation of the BNF grammar or the precedence/alignment rules given here, as distinct from `SANY`'s "semantic errors" (undefined identifiers, arity mismatches), which come from Chapter 17.

**Bearing on the standing project (`type-theory`, `automated-reasoning`):** this chapter is the cleanest available illustration, from a *non-type-theoretic* source, of the lexer/parser/elaborator layering your Rust compiler needs: a pure, position-aware grammar (Chapter 15) sitting strictly below a separate legality/scoping pass (Chapter 17) sitting strictly below a semantics-assignment pass (Chapter 16). The `LeastGrammar`-as-fixed-point construction is worth carrying over directly into how you think about your own AST's inductive definition in Lean or Rust. The two "anomalies" are also a good small case study for the elaborator project: even a language engineered from [[Elementary-Mathematical-Foundations-for-Specification#First principles|first principles]] for parseability ends up needing a couple of context-sensitive, hand-coded disambiguation rules that no amount of grammar-level cleverness eliminates — the same will likely be true of your own surface syntax once implicit-argument and operator-overload resolution enter the picture. This topic itself, being pure syntax and typesetting convention, doesn't connect to the CSP/abstract-interpretation side of the project (`sat-smt-csp`, `static-analysis`) — that's expected and fine.
