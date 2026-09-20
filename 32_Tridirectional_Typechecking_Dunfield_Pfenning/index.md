# Tridirectional Typechecking — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Bidirectional Typechecking Design Principles** : [[Bidirectional-Typechecking-Design-Principles|Link]]
   - Checking versus synthesis judgments
   - Avoiding unification via mode-correct rules : [[Related-Work-on-Refinement-Intersection-and-Union-Types|Link]]
   - Introduction rules as checking and elimination rules as synthesis
   - The subsumption rule bridging synthesis and checking
2. **The Core Language and Its Bidirectional Typing** : [[The-Core-Language-and-Its-Bidirectional-Typing|Link]]
   - Syntax and call-by-value operational semantics : [[The-Core-Language-and-Its-Bidirectional-Typing|Link]]
   - Products units functions and datatypes
   - Evaluation contexts : [[Indefinite-Property-Types-and-the-Third-Direction|Link1]], [[The-Core-Language-and-Its-Bidirectional-Typing|Link2]], [[The-Left-Tridirectional-System|Link3]]
   - Alternative bidirectional formulations : [[The-Core-Language-and-Its-Bidirectional-Typing|Link]]
3. **Definite Property Types** : [[Definite-Property-Types|Link]]
   - Intersection types and the value restriction : [[Definite-Property-Types|Link]]
   - The greatest type as a nullary intersection : [[Definite-Property-Types|Link]]
   - Refined datatypes and datasorts : [[Definite-Property-Types|Link]]
   - Index refinements and constraint domains : [[Related-Work-on-Refinement-Intersection-and-Union-Types|Link]]
   - Dependent products over index variables : [[Definite-Property-Types|Link]]
4. **Indefinite Property Types and the Third Direction** : [[Indefinite-Property-Types-and-the-Third-Direction|Link]]
   - Union types and their elimination via evaluation contexts : [[Indefinite-Property-Types-and-the-Third-Direction|Link]]
   - The empty or void type
   - Existential dependent sum types over indices
   - The direct rule as the unary indefinite elimination
   - Why the third direction is needed for typechecking : [[Bidirectional-Typechecking-Design-Principles|Link]]
5. **Contextual Typing Annotations** : [[Contextual-Typing-Annotations|Link]]
   - The problem of checking against intersections : [[Definite-Property-Types|Link]]
   - Index variable scoping inside annotations : [[Contextual-Typing-Annotations|Link]]
   - Comma-separated alternative annotations : [[The-Core-Language-and-Its-Bidirectional-Typing|Link1]], [[Contextual-Typing-Annotations|Link2]]
   - Contextual subtyping : [[Contextual-Typing-Annotations|Link]]
   - Term extension and light extension : [[Contextual-Typing-Annotations|Link]]
   - Monotonicity under annotation : [[Contextual-Typing-Annotations|Link]]
6. **Soundness and Completeness of the Simple Tridirectional System** : [[Soundness-and-Completeness-of-the-Simple-Tridirectional-System|Link]]
   - Soundness via erasure to the type-assignment system : [[Soundness-and-Completeness-of-the-Simple-Tridirectional-System|Link]]
   - Synthesizing form and extension of a term : [[Soundness-and-Completeness-of-the-Simple-Tridirectional-System|Link]]
   - The completeness theorem and its corollary : [[Soundness-and-Completeness-of-the-Simple-Tridirectional-System|Link]]
7. **The Left Tridirectional System** : [[The-Left-Tridirectional-System|Link]]
   - Linear contexts and linear variables : [[The-Left-Tridirectional-System|Link]]
   - The directL rule as the sole source of linearity : [[The-Left-Tridirectional-System|Link]]
   - Left rules replacing contextual rules
   - Soundness and completeness relative to the simple tridirectional system : [[Soundness-and-Completeness-of-the-Simple-Tridirectional-System|Link]]
   - Decidability of left tridirectional typing : [[The-Core-Language-and-Its-Bidirectional-Typing|Link1]], [[The-Left-Tridirectional-System|Link2]]
   - Type safety via composition with the type-assignment system : [[The-Left-Tridirectional-System|Link]]
8. **Related Work on Refinement Intersection and Union Types** : [[Related-Work-on-Refinement-Intersection-and-Union-Types|Link]]
   - Datasort refinement and the refinement restriction : [[Definite-Property-Types|Link1]], [[Related-Work-on-Refinement-Intersection-and-Union-Types|Link2]]
   - The value restriction on intersection introduction : [[Definite-Property-Types|Link1]], [[Related-Work-on-Refinement-Intersection-and-Union-Types|Link2]]
   - Index refinements and elaboration of existential scope : [[Related-Work-on-Refinement-Intersection-and-Union-Types|Link]]
   - Local type inference and partial inference strategies : [[Related-Work-on-Refinement-Intersection-and-Union-Types|Link]]
   - Principal typings : [[Related-Work-on-Refinement-Intersection-and-Union-Types|Link]]

---
