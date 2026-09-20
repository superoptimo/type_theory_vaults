# Inductive Logic Programming At 30: A New Introduction — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Logic Programming Foundations** : [[Logic-Programming-Foundations|Link]]
   - Syntax of terms, atoms, literals, and clauses : [[Logic-Programming-Foundations|Link]]
   - Horn clauses and definite clauses
   - Substitution and unification : [[Logic-Programming-Foundations|Link]]
   - Herbrand universe, base, and interpretation : [[ILP-Problem-Formulations|Link]]
   - Herbrand models and logical consequence
   - Entailment as the core ILP relation
   - Prolog, Datalog, and answer set programming as representation languages
   - Monotonic versus non-monotonic logic
   - Negation as failure and the closed world assumption
   - Stable model and answer set semantics : [[Building-an-ILP-System|Link]]

2. **Generality and $\theta$-Subsumption** : [[Generality-and-Theta-Subsumption|Link]]
   - The generality order over hypotheses : [[Search-Methods-Over-the-Hypothesis-Space|Link]]
   - Clausal subsumption as a syntactic proxy for entailment
   - Decidability of subsumption versus undecidability of entailment
   - Weak versus strong subsumption : [[Generality-and-Theta-Subsumption|Link]]
   - The subsumption lattice over a hypothesis space : [[Search-Methods-Over-the-Hypothesis-Space|Link]]
   - Refinement operators for specialisation and generalisation : [[Search-Methods-Over-the-Hypothesis-Space|Link]]
   - Least general generalisation (LGG)
   - Relative least general generalisation (RLGG)

3. **ILP Problem Formulations** : [[ILP-Problem-Formulations|Link]]
   - Background knowledge, positive examples, and negative examples : [[Building-an-ILP-System|Link]]
   - Learning from entailment : [[ILP-Problem-Formulations|Link]]
   - Completeness and consistency of a hypothesis
   - Learning from interpretations : [[ILP-Problem-Formulations|Link]]
   - Coverage of an example by a hypothesis : [[Representative-ILP-Systems|Link]]
   - Multi-clause learning : [[ILP-Problem-Formulations|Link]]

4. **Building an ILP System** : [[Building-an-ILP-System|Link]]
   - The four design choices of an ILP system : [[Building-an-ILP-System|Link1]], [[Representative-ILP-Systems|Link2]]
   - Representation language choice for background knowledge and hypotheses
   - Normal programs and negation as failure in hypotheses : [[Building-an-ILP-System|Link]]
   - Learning answer set programs : [[Building-an-ILP-System|Link]]
   - Higher-order program representations : [[Building-an-ILP-System|Link]]
   - Background knowledge as relational, non-tabular data : [[Building-an-ILP-System|Link]]
   - Constraints as encoded prior knowledge : [[Building-an-ILP-System|Link]]
   - The too-little versus too-much background knowledge trade-off : [[Building-an-ILP-System|Link1]], [[Open-Limitations-and-Future-Directions|Link2]]

5. **Language Bias** : [[Language-Bias|Link]]
   - Inductive bias and the need to restrict the hypothesis space
   - Syntactic bias versus semantic bias : [[Language-Bias|Link]]
   - Mode declarations : [[Language-Bias|Link]]
   - Recall, and input/output/ground argument types
   - Metarules as second-order program schemata : [[Language-Bias|Link]]
   - The Blumer bound and the bias trade-off : [[Language-Bias|Link]]

6. **Search Methods Over the Hypothesis Space** : [[Search-Methods-Over-the-Hypothesis-Space|Link]]
   - Top-down (general-to-specific) search : [[Search-Methods-Over-the-Hypothesis-Space|Link]]
   - Bottom-up (specific-to-general) search : [[Search-Methods-Over-the-Hypothesis-Space|Link]]
   - Meta-level ILP as a declarative reformulation of search
   - Bottom clause construction : [[Representative-ILP-Systems|Link]]
   - The covering algorithm for multi-clause hypotheses
   - Trade-offs between top-down, bottom-up, and meta-level approaches

7. **ILP System Features** : [[ILP-System-Features|Link]]
   - Noise handling: noisy examples, noisy background knowledge, imperfect background knowledge
   - Occamist bias and minimal-hypothesis learning : [[ILP-System-Features|Link]]
   - Cost-minimal and optimal program learning : [[ILP-System-Features|Link]]
   - The grounding bottleneck and infinite domains : [[ILP-System-Features|Link]]
   - Recursion and its role in generalisation from few examples : [[ILP-System-Features|Link]]
   - Meta-interpretive learning (MIL) : [[ILP-Problem-Formulations|Link]]

8. **Predicate Invention** : [[Predicate-Invention|Link]]
   - Motivation: automatically introducing auxiliary predicate symbols
   - Inverse resolution : [[Predicate-Invention|Link]]
   - Placeholders / prescriptive predicate invention : [[Predicate-Invention|Link]]
   - Metarule-driven predicate invention : [[Predicate-Invention|Link]]
   - Lifelong and dependent learning via predicate reuse : [[Predicate-Invention|Link1]], [[Open-Limitations-and-Future-Directions|Link2]]
   - Theory refinement, compression, and restructuring : [[Predicate-Invention|Link]]
   - Auto-encoding logic programs : [[ILP-in-the-Broader-Landscape|Link1]], [[Logic-Programming-Foundations|Link2]]
   - Program refactoring

9. **Representative ILP Systems** : [[Representative-ILP-Systems|Link]]
   - Aleph and inverse entailment : [[Representative-ILP-Systems|Link]]
   - Bottom clause construction and mode-bounded search in Aleph : [[Representative-ILP-Systems|Link]]
   - TILDE as a first-order generalisation of decision trees : [[Representative-ILP-Systems|Link]]
   - Information gain and lookahead in TILDE
   - ASPAL and meta-level encoding as an ASP problem : [[Representative-ILP-Systems|Link]]
   - Metagol and Prolog meta-interpretation : [[Representative-ILP-Systems|Link]]
   - Comparative advantages and disadvantages of the four systems

10. **Applications of ILP** : [[Applications-of-ILP|Link]]
    - Bioinformatics and drug design : [[Applications-of-ILP|Link]]
    - The Robot Scientist : [[Applications-of-ILP|Link]]
    - Ecology and trophic relation discovery
    - Program analysis and SQL query synthesis
    - Data curation and string transformation synthesis
    - Learning from interpretation transitions (LFIT) : [[ILP-Problem-Formulations|Link]]
    - Natural language grammar and parser induction : [[Applications-of-ILP|Link]]
    - Physics-informed and robotics learning : [[Applications-of-ILP|Link]]
    - Game rule induction

11. **ILP in the Broader Landscape** : [[ILP-in-the-Broader-Landscape|Link]]
    - ILP as a form of inductive program synthesis : [[ILP-in-the-Broader-Landscape|Link]]
    - Deductive versus inductive program synthesis : [[ILP-in-the-Broader-Landscape|Link]]
    - Universal induction methods
    - Statistical relational AI and probabilistic logic programming
    - Neural approaches to ILP : [[ILP-in-the-Broader-Landscape|Link]]
    - Representation learning and its relation to predicate invention : [[ILP-in-the-Broader-Landscape|Link]]

12. **Open Limitations and Future Directions** : [[Open-Limitations-and-Future-Directions|Link]]
    - The need for user-friendly, standardised tooling
    - Automatically identifying suitable language biases
    - Predicate invention and abstraction toward human-level AI : [[Open-Limitations-and-Future-Directions|Link]]
    - Lifelong learning, relevance, and catastrophic remembering : [[Open-Limitations-and-Future-Directions|Link]]
    - Handling noisy background knowledge : [[Open-Limitations-and-Future-Directions|Link]]
    - Probabilistic ILP : [[Open-Limitations-and-Future-Directions|Link]]
    - Explainability and ultra-strong machine learning : [[Open-Limitations-and-Future-Directions|Link]]
    - Learning from raw sensory data : [[Open-Limitations-and-Future-Directions|Link]]

---
