# The Power of Symbolic Automata and Transducers — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Effective Boolean Algebras** : [[Effective-Boolean-Algebras|Link]]
   - Domain, predicates, and denotation function as the algebraic foundation : [[Effective-Boolean-Algebras|Link]]
   - Decidable satisfiability as the core effectiveness requirement : [[Effective-Boolean-Algebras|Link]]
   - The equality algebra as a minimal example : [[Effective-Boolean-Algebras|Link]]
   - The SMT algebra as a practical example built on a solver
   - Label algebras extending Boolean algebras with function terms : [[Effective-Boolean-Algebras|Link]]

2. **Symbolic Finite Automata (s-FA)** : [[Symbolic-Finite-Automata|Link]]
   - Definition as predicate-labeled finite automata : [[Symbolic-Finite-Transducers|Link]]
   - Determinism and the a-transition uniqueness condition
   - Normalized representation and per-state-pair transition functions : [[Symbolic-Finite-Automata|Link]]
   - Complete versus partial states and automata
   - Determinizability and the predicate space explosion : [[Symbolic-Finite-Automata|Link]]
   - Closure under Boolean operations (complement, intersection) : [[Symbolic-Finite-Automata|Link]]
   - Decidability of emptiness and language equivalence : [[Symbolic-Finite-Automata|Link]]
   - Minimization, language inclusion, forward bisimulation, and learning algorithms

3. **Minterms and Alphabet Equivalence Classes** : [[Minterms-and-Alphabet-Equivalence-Classes|Link]]
   - Minterms as maximal satisfiable Boolean combinations of predicates : [[Minterms-and-Alphabet-Equivalence-Classes|Link]]
   - Predicate abstraction and compiling an s-FA into a classic finite automaton : [[Minterms-and-Alphabet-Equivalence-Classes|Link]]
   - Bounds on the number of minterms for general and deterministic automata

4. **Parametric Complexity of Symbolic Algorithms** : [[Parametric-Complexity-of-Symbolic-Algorithms|Link]]
   - Complexity depending jointly on state/transition count and alphabet-theory satisfiability cost
   - Predicate growth from repeated Boolean combination
   - Moore's versus Hopcroft's minimization algorithms in the symbolic setting
   - Trade-offs between state complexity and alphabet complexity : [[Parametric-Complexity-of-Symbolic-Algorithms|Link]]

5. **Variants of Symbolic Automata** : [[Variants-of-Symbolic-Automata|Link]]
   - Symbolic alternating finite automata (s-AFA) : [[Variants-of-Symbolic-Automata|Link]]
   - Multiple initial states for nondeterministic s-FAs : [[Variants-of-Symbolic-Automata|Link]]
   - Symbolic tree automata (s-TA) : [[Variants-of-Symbolic-Automata|Link]]
   - Symbolic visibly pushdown automata (s-VPA) over nested words : [[Variants-of-Symbolic-Automata|Link]]
   - Symbolic extended finite automata (s-EFA) and multi-character transitions : [[Variants-of-Symbolic-Automata|Link]]
   - Cartesian s-EFAs and monadic decomposition : [[Variants-of-Symbolic-Automata|Link]]
   - Loss of closure and decidability properties in s-EFAs : [[Symbolic-Finite-Automata|Link]]

6. **Symbolic Automata in Practice** : [[Symbolic-Automata-in-Practice|Link]]
   - Modeling Unicode/UTF16 alphabets with BDDs or bit-vector SMT theories : [[Symbolic-Automata-in-Practice|Link]]
   - Parametrized unit testing, SQL query exploration, password generation
   - Alternation for Boolean combinations of regular expressions in text processing : [[Symbolic-Automata-in-Practice|Link]]
   - Regular expression and XML code generation : [[Symbolic-Automata-in-Practice|Link]]
   - Symbolic visibly pushdown automata for control-flow graph recovery : [[Symbolic-Automata-in-Practice|Link]]

7. **Symbolic Finite Transducers (s-FT)** : [[Symbolic-Finite-Transducers|Link1]], [[Variants-of-Symbolic-Transducers|Link2]]
   - Function terms, term composition, and equality predicates over terms
   - Definition as predicate-and-output-labeled automata : [[Symbolic-Finite-Transducers|Link]]
   - Transduction relation, domain, and range : [[Symbolic-Finite-Transducers|Link]]
   - Deterministic and functional (single-valued) transducers
   - Quantifier elimination and domain/range language computability : [[Symbolic-Finite-Transducers|Link]]
   - Non-regularity of transducer ranges : [[Symbolic-Transducers-in-Practice|Link1]], [[Variants-of-Symbolic-Transducers|Link2]]
   - Closure under sequential composition : [[Symbolic-Finite-Transducers|Link]]
   - Type-checking via composition and closure properties : [[Symbolic-Finite-Transducers|Link]]
   - Decidable functionality and functional equivalence : [[Symbolic-Finite-Transducers|Link]]
   - Undecidable injectivity for symbolic (versus classic) transducers

8. **Variants of Symbolic Transducers** : [[Variants-of-Symbolic-Transducers|Link]]
   - Finalizers and subsequential transducers : [[Variants-of-Symbolic-Transducers|Link]]
   - Initial outputs and minimality : [[Variants-of-Symbolic-Transducers|Link]]
   - Symbolic extended finite transducers (s-EFT) and their weaker closure properties : [[Variants-of-Symbolic-Transducers|Link1]], [[Variants-of-Symbolic-Automata|Link2]]
   - Symbolic transducers with bounded look-back and roll-back (s-RT) : [[Variants-of-Symbolic-Transducers|Link]]
   - Symbolic transducers with registers for loop-carried state : [[Variants-of-Symbolic-Transducers|Link]]
   - Branching transitions and if-then-else structured transducers : [[Variants-of-Symbolic-Transducers|Link]]
   - Symbolic tree transducers (s-TT) : [[Variants-of-Symbolic-Transducers|Link]]

9. **Symbolic Transducers in Practice** : [[Symbolic-Transducers-in-Practice|Link]]
   - Analysis of string sanitizers and cross-site-scripting defense : [[Symbolic-Transducers-in-Practice|Link]]
   - Commutativity, idempotence, and safe-range checks for sanitizers
   - BASE64/UTF encoder-decoder correctness via extended transducers
   - Learning symbolic automata/transducers to extract models of input filters : [[Symbolic-Transducers-in-Practice|Link1]], [[Variants-of-Symbolic-Transducers|Link2]]
   - Static analysis of list- and tree-manipulating functional programs : [[Symbolic-Transducers-in-Practice|Link]]
   - Data-parallel computation via matrix-multiplication views of transition functions
   - Code generation and log/data processing pipelines using registers and branching : [[Symbolic-Transducers-in-Practice|Link]]
   - DReX and declarative regular string transformation : [[Symbolic-Transducers-in-Practice|Link]]

10. **Open Problems in Symbolic Models** : [[Open-Problems-in-Symbolic-Models|Link]]
    - Adapting finite-alphabet algorithms (Hopcroft, Paige-Tarjan, unambiguous equivalence) to the symbolic setting
    - Practical subclasses of s-EFAs with good properties : [[Open-Problems-in-Symbolic-Models|Link]]
    - Learning theory for symbolic automata : [[Open-Problems-in-Symbolic-Models|Link]]
    - Algebraic and co-algebraic treatments of symbolic automata theory : [[Open-Problems-in-Symbolic-Models|Link]]
    - Combining symbolic automata with nominal automata for data words : [[Open-Problems-in-Symbolic-Models|Link]]
    - SMT solving over sequences and integration with solvers like Z3 : [[Open-Problems-in-Symbolic-Models|Link]]
    - Security applications: modeling program binaries and reflective code : [[Open-Problems-in-Symbolic-Models|Link]]

---
