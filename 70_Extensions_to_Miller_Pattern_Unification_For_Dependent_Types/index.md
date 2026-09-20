# Extensions to Miller's Pattern Unification for Dependent Types and Records — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Higher-Order Pattern Unification** : [[Higher-Order-Pattern-Unification|Link]]
   - The Miller pattern fragment : [[Higher-Order-Pattern-Unification|Link]]
   - Undecidability of full higher-order unification : [[Higher-Order-Pattern-Unification|Link]]
   - The dynamic pattern fragment and constraint postponement : [[Higher-Order-Pattern-Unification|Link]]
   - Unification as an inference system of rewrite rules on constraint sets : [[Constraint-Based-Unification-as-an-Inference-System|Link]]

2. **The λΠΣ-Calculus with Meta-Variables** : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]
   - Dependent function types and dependent pair types
   - Neutral terms, normal terms, and evaluation contexts
   - Meta-variables as closures under a suspended substitution : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]
   - Contextual objects and contextual types : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]
   - Rigid, flexible, and strongly rigid occurrences : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]
   - Hereditary substitution : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]
   - Meta-substitution : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]
   - Bidirectional typing for neutral and normal terms : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]

3. **Type Isomorphisms for Dependent Records** : [[Type-Isomorphisms-for-Dependent-Records|Link]]
   - The Sigma-Pi type isomorphism : [[Type-Isomorphisms-for-Dependent-Records|Link]]
   - Translating a record-typed function into a pair of functions
   - Flattening Σ-types in a meta-variable's context : [[Extension-to-the-Unit-and-Singleton-Types|Link1]], [[Type-Isomorphisms-for-Dependent-Records|Link2]], [[Constraint-Based-Unification-as-an-Inference-System|Link3]]
   - Eliminating projections via type isomorphism : [[Type-Isomorphisms-for-Dependent-Records|Link]]

4. **Constraint-Based Unification as an Inference System** : [[Constraint-Based-Unification-as-an-Inference-System|Link]]
   - Constraints and constraint sets : [[Constraint-Based-Unification-as-an-Inference-System|Link]]
   - Typing modulo a constraint set : [[Constraint-Based-Unification-as-an-Inference-System|Link]]
   - Local simplification by decomposition : [[Constraint-Based-Unification-as-an-Inference-System|Link]]
   - η-contraction of meta-variable substitutions : [[Inverting-Substitutions|Link1]], [[Constraint-Based-Unification-as-an-Inference-System|Link2]], [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link3]]
   - Orientation of equations
   - Lowering meta-variables to smaller types : [[Constraint-Based-Unification-as-an-Inference-System|Link]]
   - Solved versus active meta-variables

5. **Pruning and the Occurs Check** : [[Pruning-and-the-Occurs-Check|Link]]
   - Free variables escaping the range of a substitution
   - Bad occurrences and eliminable rigid occurrences : [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link]]
   - The pruning judgement and context pruning : [[Extension-to-the-Unit-and-Singleton-Types|Link1]], [[Pruning-and-the-Occurs-Check|Link2]]
   - Failing occurs check and unsolvability : [[Pruning-and-the-Occurs-Check|Link]]
   - Non-linear patterns and intersection of substitutions : [[Pruning-and-the-Occurs-Check|Link]]
   - Recursive meta-variable occurrences

6. **Inverting Substitutions** : [[Inverting-Substitutions|Link]]
   - Invertibility of a variable substitution for a term : [[Inverting-Substitutions|Link1]], [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|Link2]]
   - Soundness and completeness of inverse substitution : [[Inverting-Substitutions|Link]]
   - Linearity as sufficient but not necessary for invertibility

7. **Correctness of the Unification Algorithm** : [[Correctness-of-the-Unification-Algorithm|Link]]
   - Termination via an ordinal-valued measure : [[Correctness-of-the-Unification-Algorithm|Link]]
   - Transitions preserve solutions (forward and backward closure)
   - Transitions preserve typing and well-formedness : [[Correctness-of-the-Unification-Algorithm|Link]]
   - Typing modulo equality : [[Constraint-Based-Unification-as-an-Inference-System|Link]]

8. **Extension to the Unit and Singleton Types** : [[Extension-to-the-Unit-and-Singleton-Types|Link]]
   - The extensional unit type and its single inhabitant : [[Extension-to-the-Unit-and-Singleton-Types|Link]]
   - Singleton types : [[Extension-to-the-Unit-and-Singleton-Types|Link]]
   - Type-directed η-contraction to a variable head : [[Extension-to-the-Unit-and-Singleton-Types|Link]]
   - Eliminating singleton subterms and singleton variables

9. **Related Unification Algorithms and Applications** : [[Related-Unification-Algorithms-and-Applications|Link]]
   - Comparison to Huet-style unification with Σ-types : [[Constraint-Based-Unification-as-an-Inference-System|Link]]
   - Comparison to simply-typed extended pattern unification : [[Higher-Order-Pattern-Unification|Link]]
   - Context blocks in Beluga, Twelf, and Delphin
   - Record and Σ-type unification in Agda : [[Correctness-of-the-Unification-Algorithm|Link1]], [[Higher-Order-Pattern-Unification|Link2]]

---
