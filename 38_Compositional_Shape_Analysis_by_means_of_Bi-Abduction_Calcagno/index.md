# Compositional Shape Analysis by means of Bi-Abduction — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Abductive Inference** : [[Abductive-Inference|Link]]
   - Abduction as inference of missing explanatory hypotheses
   - Peirce's original philosophical formulation of abduction : [[Abductive-Inference|Link]]
   - Abduction in classical logic versus separation logic : [[Abductive-Inference|Link]]
   - Abducibility constraints such as consistency and minimality : [[Abductive-Inference|Link]]
   - Abduction for generating procedure preconditions : [[Abductive-Inference|Link]]

2. **Bi-Abduction** : [[Bi-Abduction|Link]]
   - Bi-abduction as joint inference of anti-frames and frames : [[Bi-Abduction|Link]]
   - Bi-abduction as an inverse to the frame problem : [[Bi-Abduction|Link]]
   - The bi-abductive question $\Delta * ?\text{anti-frame} \vdash H * ?\text{frame}$ : [[Quality-and-Ordering-of-Abduction-Solutions|Link1]], [[Bi-Abduction|Link2]]
   - The BiAbd algorithm combining Abduce and Frame inference : [[Bi-Abduction|Link]]
   - The bi-abductive frame rule for program analysis : [[Bi-Abduction|Link]]

3. **Separation Logic Foundations** : [[Separation-Logic-Foundations|Link]]
   - The separating conjunction and points-to predicate : [[Separation-Logic-Foundations|Link]]
   - The frame rule and its role in local reasoning : [[Separation-Logic-Foundations|Link]]
   - The principle of local reasoning and footprints : [[Related-Work-and-Positioning|Link]]
   - Symbolic heaps as a restricted assertion fragment : [[Separation-Logic-Foundations|Link]]
   - Simple lists and higher-order list instantiations : [[Separation-Logic-Foundations|Link]]
   - Semantics of symbolic heaps over stacks and heaps
   - Abstraction functions for symbolic heaps : [[Separation-Logic-Foundations|Link]]
   - Precise predicates and minimal satisfying states

4. **Proof Systems and Algorithms for Abduction** : [[Proof-Systems-and-Algorithms-for-Abduction|Link]]
   - A heuristic proof system for abductive inference : [[Proof-Systems-and-Algorithms-for-Abduction|Link]]
   - Reading proof rules bottom-up as a search algorithm : [[Proof-Systems-and-Algorithms-for-Abduction|Link]]
   - Rule ordering to minimize the inferred anti-frame : [[Proof-Systems-and-Algorithms-for-Abduction|Link]]
   - Incompleteness of the heuristic abduction algorithm : [[Proof-Systems-and-Algorithms-for-Abduction|Link]]
   - Generalizing abduction rules to arbitrary inductive predicates : [[Proof-Systems-and-Algorithms-for-Abduction|Link]]
   - A systematic algorithm for the points-to-only fragment : [[Proof-Systems-and-Algorithms-for-Abduction|Link]]
   - Compatible solutions and the compatible preorder : [[Proof-Systems-and-Algorithms-for-Abduction|Link]]
   - Computing incompatible solutions via Incompat : [[Proof-Systems-and-Algorithms-for-Abduction|Link]]
   - Subtraction and the min operator for minimal solutions : [[Proof-Systems-and-Algorithms-for-Abduction|Link]]

5. **Quality and Ordering of Abduction Solutions** : [[Quality-and-Ordering-of-Abduction-Solutions|Link]]
   - The spatial betterness ordering on candidate solutions : [[Quality-and-Ordering-of-Abduction-Solutions|Link]]
   - Minimal solutions and the min function : [[Proof-Systems-and-Algorithms-for-Abduction|Link1]], [[Quality-and-Ordering-of-Abduction-Solutions|Link2]]
   - Existence and characterization of the best solution : [[Quality-and-Ordering-of-Abduction-Solutions|Link]]
   - Why the semantic best solution is impractical to compute directly : [[Quality-and-Ordering-of-Abduction-Solutions|Link]]
   - Ordering bi-abductive solutions by anti-frame then frame quality : [[Quality-and-Ordering-of-Abduction-Solutions|Link]]

6. **Compositional Program Analysis Algorithms** : [[Compositional-Program-Analysis-Algorithms|Link]]
   - Procedures represented as control-flow graphs with Hoare-triple summaries : [[Compositional-Program-Analysis-Algorithms|Link]]
   - The PreGen algorithm for precondition generation
   - AbduceAndAdapt and variable adaptation at call sites : [[Compositional-Program-Analysis-Algorithms|Link]]
   - The assume-as-assert heuristic for path-sensitive preconditions : [[Compositional-Program-Analysis-Algorithms|Link]]
   - The PostGen algorithm as a standard forwards analysis
   - The InferSpecs algorithm combining PreGen and PostGen : [[Bi-Abduction|Link]]
   - Filtering unsafe candidate preconditions by re-execution : [[Compositional-Program-Analysis-Algorithms|Link]]
   - Abstraction and its role in terminating loop analysis
   - Partial concretization for precise abductive matching
   - Disjunctive frame rule and multiple abduction solutions
   - Termination behavior and preconditions that avoid divergence : [[Compositional-Program-Analysis-Algorithms|Link]]
   - Bottom-up recipe for compositional analysis of a call tree : [[Compositional-Program-Analysis-Algorithms|Link]]

7. **Soundness and Semantic Models** : [[Soundness-and-Semantic-Models|Link]]
   - Concrete procedure meanings as state-to-powerset functions : [[Soundness-and-Semantic-Models|Link]]
   - Relational analysis and over-approximation of procedure meaning : [[Abductive-Inference|Link]]
   - The abstract domain of procedure summaries as Hoare-triple sets : [[Compositional-Program-Analysis-Algorithms|Link1]], [[Soundness-and-Semantic-Models|Link2]]
   - The soundness theorem for InferSpecs : [[Soundness-and-Semantic-Models|Link]]
   - Footprints as the minimal safe states of a command

8. **The Abductor Tool and Case Studies** : [[The-Abductor-Tool-and-Case-Studies|Link]]
   - Small linked-list program benchmarks and discovered preconditions : [[The-Abductor-Tool-and-Case-Studies|Link]]
   - The merge.c failure case and its explanation : [[The-Abductor-Tool-and-Case-Studies|Link]]
   - The IEEE 1394 Firewire device driver case study : [[The-Abductor-Tool-and-Case-Studies|Link]]
   - Large-scale open source case studies including the Linux kernel
   - Scalability, timeouts, and graceful imprecision in large codebases
   - The Cyrus imapd footprint example and specification pictures : [[The-Abductor-Tool-and-Case-Studies|Link]]
   - Memory leak detection as a byproduct of proof failure : [[The-Abductor-Tool-and-Case-Studies|Link]]
   - Caveats on concurrency, libraries, code pointers, and arrays

9. **Related Work and Positioning** : [[Related-Work-and-Positioning|Link]]
   - Comparison with whole-program shape analyses : [[Related-Work-and-Positioning|Link]]
   - Backwards versus forwards approaches to precondition discovery
   - Comparison with CEGAR-style counterexample-guided refinement
   - Giacobazzi's abductive analysis of logic programs : [[Related-Work-and-Positioning|Link]]
   - Follow-on work on bottom-up shape analysis without re-execution

---
