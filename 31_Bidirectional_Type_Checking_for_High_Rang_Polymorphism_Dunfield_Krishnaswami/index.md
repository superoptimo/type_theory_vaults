# Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Bidirectional Typechecking Foundations** : [[Bidirectional-Typechecking-Foundations|Link]]
   - Checking mode versus synthesis mode : [[Declarative-Type-System|Link]]
   - Proof-theoretic grounding via focalization : [[Bidirectional-Typechecking-Foundations|Link]]
   - Normal forms and neutral terms corresponding to checking and synthesis
   - Type annotations required only at redexes : [[Bidirectional-Typechecking-Foundations|Link]]
   - Application judgment for spine-form applications : [[Declarative-Type-System|Link1]], [[The-Problem-of-Polymorphism-in-Bidirectional-Systems|Link2]]
2. **The Problem of Polymorphism in Bidirectional Systems** : [[The-Problem-of-Polymorphism-in-Bidirectional-Systems|Link]]
   - Failure of type assignment System F to preserve typability under $\eta$-reduction : [[The-Problem-of-Polymorphism-in-Bidirectional-Systems|Link]]
   - Undecidability of subtyping for impredicative polymorphism : [[The-Problem-of-Polymorphism-in-Bidirectional-Systems|Link1]], [[Declarative-Type-System|Link2]]
   - Restriction to predicative polymorphism : [[The-Problem-of-Polymorphism-in-Bidirectional-Systems|Link]]
   - Modeling instantiation via subtyping : [[The-Problem-of-Polymorphism-in-Bidirectional-Systems|Link]]
3. **Declarative Type System** : [[Declarative-Type-System|Link]]
   - Checking, synthesis, and application judgments : [[Declarative-Type-System|Link]]
   - Subtyping as a more-polymorphic-than relation : [[Declarative-Type-System|Link]]
   - The $\forall L$ and $\forall R$ subtyping rules
   - Let-generalization and the cut rule : [[Declarative-Type-System|Link]]
   - Relationship to type assignment System F : [[Declarative-Type-System|Link]]
   - Substitution and inverse substitution theorems : [[Declarative-Type-System|Link]]
   - Annotation removal theorem : [[Declarative-Type-System|Link]]
   - Soundness of the $\eta$ law
4. **Algorithmic Contexts** : [[Algorithmic-Contexts|Link]]
   - Ordered contexts with existential type variables
   - Unsolved versus solved existential variables
   - Complete contexts : [[Algorithmic-Contexts|Link]]
   - Context application as substitution : [[Algorithmic-Contexts|Link]]
   - Hole notation for contexts : [[Algorithmic-Contexts|Link]]
   - Input and output contexts : [[Algorithmic-Contexts|Link]]
5. **Algorithmic Subtyping and Instantiation** : [[Algorithmic-Subtyping-and-Instantiation|Link]]
   - Algorithmic subtyping rules : [[Algorithmic-Subtyping-and-Instantiation|Link1]], [[Algorithmic-Typing|Link2]]
   - Articulation of existential variables : [[Algorithmic-Subtyping-and-Instantiation|Link]]
   - The instantiation judgment : [[Metatheory-of-the-Algorithm|Link]]
   - Instantiate-to-subtype and instantiate-to-supertype : [[Algorithmic-Subtyping-and-Instantiation|Link]]
   - The reach rules for scope-constrained existentials : [[Algorithmic-Subtyping-and-Instantiation|Link]]
6. **Algorithmic Typing** : [[Algorithmic-Typing|Link]]
   - Typing rules mirroring the declarative system : [[Declarative-Type-System|Link1]], [[Algorithmic-Typing|Link2]]
   - The existential-application rule with no declarative analogue : [[Metatheory-of-the-Algorithm|Link1]], [[Algorithmic-Typing|Link2]]
   - Context extension as a metatheoretic invariant : [[Algorithmic-Typing|Link]]
7. **Metatheory of the Algorithm** : [[Metatheory-of-the-Algorithm|Link]]
   - Context extension judgment : [[Metatheory-of-the-Algorithm|Link1]], [[Algorithmic-Contexts|Link2]], [[Algorithmic-Typing|Link3]]
   - Decidability of instantiation : [[Algorithmic-Subtyping-and-Instantiation|Link1]], [[Metatheory-of-the-Algorithm|Link2]]
   - Decidability of subtyping : [[Algorithmic-Typing|Link]]
   - Decidability of algorithmic typing : [[Metatheory-of-the-Algorithm|Link1]], [[Algorithmic-Typing|Link2]]
   - Soundness of instantiation subtyping and typing : [[Metatheory-of-the-Algorithm|Link]]
   - Completeness of instantiation subtyping and typing : [[Metatheory-of-the-Algorithm|Link]]
8. **Design Variations** : [[Design-Variations|Link]]
   - Eliminating type inference for a no-inference bidirectional system
   - Extending toward full Damas-Milner type inference : [[Design-Variations|Link]]
   - Tradeoffs among the $\eta$-law impredicativity and the System F type language : [[Design-Variations|Link]]
9. **Related Approaches to Higher-Rank Type Inference** : [[Related-Approaches-to-Higher-Rank-Type-Inference|Link]]
   - MLF and bounded quantification
   - HML and FPH as System-F-typed alternatives
   - Local type inference and colored local type inference
   - Greedy instantiation and its incompleteness : [[Metatheory-of-the-Algorithm|Link]]
   - Context-based type inference and mixed-prefix unification

---
