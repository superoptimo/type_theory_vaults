# Better Together: Unifying Datalog and Equality Saturation — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Fixpoint Reasoning Frameworks** : [[Fixpoint-Reasoning-Frameworks|Link]]
   - Datalog as a bottom-up recursive query language over relations : [[Fixpoint-Reasoning-Frameworks|Link1]], [[Related-Formalisms-and-Positioning|Link2]]
   - The immediate consequence operator : [[Formal-Semantics-of-egglog|Link]]
   - Least fixpoint semantics of Datalog programs : [[Formal-Semantics-of-egglog|Link]]
   - Equality saturation as term rewriting without destructive replacement
   - Phase-ordering problem in traditional term rewriting
   - Shared setup of rules plus initial facts driving both paradigms

2. **The E-Graph Data Structure** : [[The-E-Graph-Data-Structure|Link]]
   - E-nodes as function symbols over e-classes : [[The-E-Graph-Data-Structure|Link]]
   - E-classes as sets of equivalent e-nodes : [[The-E-Graph-Data-Structure|Link]]
   - Terms represented compactly via shared e-classes
   - Congruence induced by e-graph equivalence : [[Case-Study-Unification-Based-Points-to-Analysis|Link]]
   - E-matching as pattern matching modulo equality : [[The-E-Graph-Data-Structure|Link]]
   - Multi-patterns for simultaneous pattern matching : [[The-E-Graph-Data-Structure|Link]]
   - E-class analyses for semantic abstraction over terms : [[The-E-Graph-Data-Structure|Link1]], [[Fixpoint-Reasoning-Frameworks|Link2]]
   - Limitations of single, upward-only e-class analyses in egg

3. **The egglog Language Model** : [[The-egglog-Language-Model|Link]]
   - Functions as maps enforcing functional dependency : [[Equivalence-and-Canonicalization|Link]]
   - Relations as functions to the unit type : [[The-egglog-Language-Model|Link]]
   - The merge expression for functional-dependency repair : [[Equivalence-and-Canonicalization|Link]]
   - Default expressions and get-or-make-set semantics : [[The-egglog-Language-Model|Link]]
   - Sorts as uninterpreted domains of opaque ids
   - The union action for asserting equivalence : [[Case-Study-Unification-Based-Points-to-Analysis|Link]]
   - Datatypes as sugar for sorts and constructor functions
   - Rewrite rules desugaring to query-and-union rules
   - Rules as query plus actions rather than body plus head : [[The-egglog-Language-Model|Link]]

4. **Equivalence and Canonicalization** : [[Equivalence-and-Canonicalization|Link]]
   - Union-find as the backing structure for sorts : [[Equivalence-and-Canonicalization|Link]]
   - Canonical representatives and canonicalization functions : [[Equivalence-and-Canonicalization|Link]]
   - Congruence closure via functional-dependency conflicts : [[Equivalence-and-Canonicalization|Link]]
   - The rebuilding procedure and its relation to e-graph rebuilding : [[Equivalence-and-Canonicalization|Link]]
   - Iterating rebuilding to a fixpoint : [[Equivalence-and-Canonicalization|Link]]
   - Avoiding joins modulo equivalence through active canonicalization : [[Equivalence-and-Canonicalization|Link]]

5. **Formal Semantics of egglog** : [[Formal-Semantics-of-egglog|Link]]
   - Core egglog syntax of programs, rules, atoms, and patterns
   - Instances as a database paired with an equivalence relation : [[Formal-Semantics-of-egglog|Link]]
   - The inflationary immediate consequence operator : [[Formal-Semantics-of-egglog|Link]]
   - Pre-instances and the need for rebuilding : [[Formal-Semantics-of-egglog|Link]]
   - The expanded database ordering over instances
   - Monotonic convergence of the immediate-consequence-then-rebuild sequence
   - The inductive fixpoint as program meaning
   - Under-approximating an infinite fixpoint by bounded iteration

6. **Incremental Evaluation** : [[Incremental-Evaluation|Link]]
   - Semi-naïve evaluation and differential databases : [[Formal-Semantics-of-egglog|Link1]], [[Incremental-Evaluation|Link2]]
   - Delta rules derived from ordinary rules
   - Equivalence of semi-naïve and naïve evaluation results : [[Incremental-Evaluation|Link1]], [[Formal-Semantics-of-egglog|Link2]]
   - Incremental e-matching as a byproduct of semi-naïve evaluation : [[Query-Evaluation-and-E-Matching|Link1]], [[Incremental-Evaluation|Link2]]

7. **Query Evaluation and E-Matching** : [[Query-Evaluation-and-E-Matching|Link]]
   - Relational e-matching reducing pattern matching to database queries : [[Query-Evaluation-and-E-Matching|Link]]
   - Worst-case optimal join algorithms (Generic Join) : [[Query-Evaluation-and-E-Matching|Link]]
   - The dual-representation problem in prior relational e-matching : [[Query-Evaluation-and-E-Matching|Link]]
   - Functional database design avoiding e-graph/database synchronization

8. **Language-Based System Design** : [[Language-Based-System-Design|Link]]
   - Typechecked rules versus host-language guard code : [[Language-Based-System-Design|Link]]
   - Multiple datatypes and multiple analyses versus a single ad-hoc type
   - egglog as both a language and a library : [[The-egglog-Language-Model|Link]]

9. **Case Study: Unification-Based Points-to Analysis** : [[Case-Study-Unification-Based-Points-to-Analysis|Link]]
   - Steensgaard-style analysis as nearly linear unification-based points-to analysis : [[Case-Study-Unification-Based-Points-to-Analysis|Link]]
   - Andersen-style subset-based analysis as precise but quadratic
   - Join modulo equivalence as a Datalog performance pathology : [[Case-Study-Unification-Based-Points-to-Analysis|Link]]
   - Union-find–backed relations in Souffle (eqrel) : [[Equivalence-and-Canonicalization|Link]]
   - Choice domain and subsumptive rules as a complex Datalog encoding of Steensgaard analysis
   - Soundness bugs from ad hoc equivalence encodings

10. **Case Study: Sound Floating-Point Rewriting** : [[Case-Study-Sound-Floating-Point-Rewriting|Link]]
    - Herbie's use of equality saturation for floating-point accuracy : [[Fixpoint-Reasoning-Frameworks|Link]]
    - Unsound rewrite rules and their validation/discard workaround
    - Interval analysis for bounding terms during rewriting : [[Case-Study-Sound-Floating-Point-Rewriting|Link]]
    - Not-equals analysis built on interval analysis and rewriting facts : [[Case-Study-Sound-Floating-Point-Rewriting|Link]]
    - Composable multiple analyses versus a fused monolithic analysis

11. **Unification and Logic Programming in egglog** : [[Unification-and-Logic-Programming-in-egglog|Link]]
    - Fresh ids as logic variables representing unknown information : [[Unification-and-Logic-Programming-in-egglog|Link1]], [[The-E-Graph-Data-Structure|Link2]]
    - Demand-driven top-down simulation without explicit demand relations
    - Injectivity rules propagating unification through inductive types : [[Unification-and-Logic-Programming-in-egglog|Link]]
    - Occurs check implemented independently of the unification mechanism
    - Hindley-Milner type inference via unification of type variables : [[Unification-and-Logic-Programming-in-egglog|Link]]
    - Contrast with Prolog-style backtracking and SMT-style theory combination

12. **Related Formalisms and Positioning** : [[Related-Formalisms-and-Positioning|Link]]
    - The chase and tuple/equality-generating dependencies
    - Datalog with lattices and recursive aggregates (Flix) : [[Related-Formalisms-and-Positioning|Link]]
    - egglog's relation to concurrent categorical formalizations of Datalog with equality
    - Termination as an open problem for egglog : [[Related-Formalisms-and-Positioning|Link]]
    - Congruence closure as dual to unification : [[Related-Formalisms-and-Positioning|Link]]

---
