# AI Models for Type Inference, Type Checking and Term Synthesis in Typed Lambda Calculi: State of the Art (October 2026)

Yes. Research exists on all three tasks, but few models are trained specifically on the pure lambda calculus, and the results are uneven. The systems that work best are hybrids: a learned model proposes types or terms, and a symbolic type checker, unifier or inhabitation search makes the result sound. Neural networks used alone can predict types well on in-distribution STLC terms. They fail on deeper or out-of-distribution terms. Even Claude-3.7-sonnet, the best of 64 LLMs tested on TF-Bench_pure, reaches only 55.85% on clean System F (Haskell) type inference.

## TL;DR

- **Type inference/typability:** The main lambda-calculus-specific work is IBM's 2021/2023 transformer study on STLC (Miranda et al.). It reached near-perfect accuracy only on terms of the same depth as training. TF-Bench (NeurIPS 2025) found that the best of 64 LLMs reaches 55.85% on NL-free System F / Haskell type inference. For real languages, learned inference (LambdaNet, Type4Py, TypeT5, and LLM + Mypy loops, where GPT-4.1-mini, O3-Mini and O4-Mini each produce Mypy-consistent annotations for about 88.6% of snippets) is mature as an *annotation suggestion* tool, not as a sound inference engine.
- **Type checking:** In practice nobody replaces the checker with a network, because checking is decidable and cheap for STLC and Hindley–Milner and is the trusted kernel in proof assistants. The checker's role is as an oracle inside learning systems: a constraint during decoding (type-constrained decoding, PLDI 2025), a filter in generate–check–repair loops, or the reward signal in RL with verifiable rewards (DeepSeek-Prover-V2, Kimina, Seed-Prover).
- **Term finding / inhabitation / type elaboration:** This is the most active area, via Curry–Howard. Neural-guided proof-term search for intuitionistic propositional logic (93.2% on large proofs, Sekiyama & Suenaga 2018; 84% vs `tauto`'s 52%, Kusumoto et al. 2018) has grown into LLM provers for Lean, Coq and Agda trained with type-checker rewards (DeepSeek-Prover-V2: 88.9% miniF2F-test). Symbolic inhabitation solvers (Canonical, ITP 2025) remain strong baselines that are sound by construction. Elaborating or completing types for partially annotated terms is mostly done with typed holes and language-server context (Hazel, OOPSLA 2024) plus type-constrained decoding, not by dedicated neural models.

## Key Findings

### 0. The three problems, stated precisely

For a typed $\lambda$-calculus with judgments $\Gamma \vdash M : A$, the user's three tasks are:

1. **Type inference / synthesis (typability):** given $M$ (and possibly $\Gamma$), find $A$ (ideally the principal type) such that $\Gamma \vdash M : A$, or report that no such $A$ exists.
2. **Type checking:** given $\Gamma$, $M$ and $A$, decide whether $\Gamma \vdash M : A$ holds.
3. **Inhabitation / term finding:** given $\Gamma$ and $A$, find $M$ such that $\Gamma \vdash M : A$. Under Curry–Howard this is proof search: $A$ is a proposition and $M$ is a proof.

For the simply typed $\lambda$-calculus (STLC) the core rules are:

$$
\dfrac{x : A \in \Gamma}{\Gamma \vdash x : A}
\qquad
\dfrac{\Gamma, x : A \vdash M : B}{\Gamma \vdash \lambda x.\, M : A \to B}
\qquad
\dfrac{\Gamma \vdash M : A \to B \quad \Gamma \vdash N : A}{\Gamma \vdash M\, N : B}
$$

A full derivation, here for the inhabitant of $A \to B \to A$ (the $K$ combinator), shows the tree-shaped object every neural method must implicitly produce or certify:

$$
\dfrac{\dfrac{x : A,\, y : B \vdash x : A}{x : A \vdash \lambda y.\, x : B \to A}}{\vdash \lambda x.\, \lambda y.\, x : A \to B \to A}
$$

Bidirectional systems split the judgment into synthesis $\Gamma \vdash M \Rightarrow A$ and checking $\Gamma \vdash M \Leftarrow A$. Type elaboration with holes adds judgments such as $\Gamma \vdash\, ?_h : A$, where the hole $?_h$ must later be filled with a term of type $A$. These are the problems that typed-hole LLM assistants and type-constrained decoders solve in practice.

Complexity explains where learning helps. STLC type inference is PTIME, which Miranda et al. call "trivial". The same authors note that inference for OCaml or Scala is EXPTIME, and that "in more expressive type theories … type inference becomes undecidable in general."\[1\] STLC inhabitation is PSPACE-complete.\[2\] Inhabitation is undecidable for intersection types (rank $k > 2$) and for dependent type theory.\[3\]\[4\] So neural guidance pays off mainly for **inhabitation** (search) and for **inference in rich or unsound real-world type systems**. It pays off much less for decidable checking.

### 1. Type inference / typability

**Pure lambda-calculus models (sparse but direct)**

- **Miranda, Shinnar, Pestun, Trager (and Fulton in the PDF), IBM Research, arXiv 2304.10500 (2023; PDF dated Aug 2021).** This is the only study I found that trains transformers specifically for STLC type inference. An encoder–decoder transformer reads a breadth-first serialization of the term and emits the type's grammar rules. The authors propose STLC type inference as a few-shot and length-generalization benchmark: "a transformer that understands the formal language … should be able to perform type inference on the simply typed lambda calculus."\[5\] Results:
  - Optimization is fragile: "the optimization landscape is difficult even in this simple setting." With Adam at learning rate $10^{-3}$, train accuracy is only 0.09–0.31. Adafactor reaches perfect train accuracy about 11× faster than Adam.\[5\]\[6\]
  - Validation accuracy reaches 0.99–1.0, but validation uses terms of the same depth as training. The authors conjecture the model would not generalize systematically to deeper terms and did not test it.\[5\]
- **TF-Bench (He, Yang, Gonzalo, Chen; NeurIPS 2025, arXiv 2509.23686).** This is the main 2025 benchmark of LLMs on type inference grounded in System F.\[7\]
  - It has 188 function-level tasks from the Haskell Prelude: 26.6% monomorphic, 32.4% parametric, 41.0% bounded/ad-hoc polymorphism. All type dependencies are supplied, so each task is a closed deduction.\[7\]
  - TF-Bench_pure "alpha-rewrites" away natural-language type and variable names, which removes memorization cues.\[7\]
  - Across 64 LLMs, "the best-performing LLM (Claude-3.7-sonnet) achiev[es] only 55.85% accuracy on TF-Bench_pure."\[7\]
  - Models fine-tuned on code "tend to overfit NL cues," while math-tuned models are "more likely to solve the task through reasoning."\[7\]
  - **Interpretation:** strong LLMs still fail on roughly half of small, closed Hindley–Milner-style inference problems once surface cues are removed. Exact symbolic inference is not something LLMs reliably reproduce.

**Learned type inference for real languages (mature, but a different problem)**

These systems predict *annotations* for gradually or optionally typed code, where the ground truth is what developers wrote rather than a principal type.

| System | Year / venue | Approach | Reported result |
|---|---|---|---|
| LambdaNet (Wei, Goyal, Durrett, Dillig) | ICLR 2020 | GNN over a "type dependency graph" linking type variables via logical constraints and naming | 64.2% top-1, 84.5% top-5 on TypeScript; +14% absolute on library types over prior work\[8\]\[9\] |
| OptTyper (Pandi et al.) | arXiv 2004.00348 (2020) | Optimises logical (type-rule) plus natural (naming) constraints jointly | Top-1 accuracy on par with LambdaNet, with outputs constrained by type rules\[10\] |
| Type4Py | ICSE 2022 | Deep similarity learning | 75.8% exact match on ManyTypes4Py\[11\] |
| TypeT5 (Wei, Durrett, Dillig) | ICLR 2023 | CodeT5 seq2seq plus static-analysis context plus iterative decoding | Outperforms Typilus, Type4Py and HiTyper; fewer type-checker errors\[12\]\[13\] |
| LLM + Mypy generate–check–repair (Bharti et al.) | arXiv 2508.00422 (2025) | Zero-shot LLM, Mypy verifies, errors fed back | Up to 70.5% exact match and 79.1% base-type accuracy on 6,000 ManyTypes4Py snippets, with under one repair iteration on average and no task-specific training |

**How these relate to the symbolic setting.** They treat inference as classification or generation over a type vocabulary, informed by names and usage. They are not principal-type derivation. They are unsound by design, and the best ones put a checker back in the loop: TypeT5 counts type errors, and the LLM + Mypy pipeline repairs until the checker accepts. The architectural lesson carries over to lambda calculi: graph or tree encodings of the constraint structure (LambdaNet's hyperedges; LambdaNet accuracy rises from 13.6% to 64.2% as GNN message-passing iterations go from 0 to 6) beat flat token sequences.\[14\] The most reliable ML type inference is "learned proposal + symbolic verification."

### 2. Type checking

- **No serious line of work replaces a type checker with a neural network.** For STLC, Hindley–Milner and the kernels of Lean, Coq and Agda, checking is decidable and is the trust base. A learned approximation would only add unsoundness.
- **The checker as oracle is pervasive and is where the action is:**
  - **Type-constrained decoding (Mündler, He, Wang, Sen, Song, Vechev; PLDI 2025).** This turns the type system into a prefix automaton for LLM decoding.\[15\]
    - They formalize it on "a foundational simply-typed language" and extend it to TypeScript. At each token they decide whether the partial program can still be completed into a well-typed one. This requires a type-reachability search, which they describe as "solving the challenging problem of type inhabitation … in the novel context of LLM-based code generation."\[15\]
    - The search is proven **sound** (Lemma 3: if $\mathrm{reachable}(T, G)$ then some extension $y$ gives $\Gamma \vdash e \circ y : G$). It is deliberately **incomplete**, because a pruning heuristic guarantees termination.\[15\]
    - Results: 94% of compilation errors in LLM-generated TypeScript are type errors and only 6% are syntax errors. Type constraining cut compilation errors by 75.3% (HumanEval) and 52.1% (MBPP). It raised pass@1 by 3.5% for synthesis, 5.0% for translation and 37% for repair. Runtime overhead was 39–52%.\[15\]
    - Limitations: the method needs logit access (closed APIs cannot use it), it is hand-built per language, and it can loop when the model "is unable to recover."\[15\]
  - **Checker-in-the-loop repair.** Generate–check–repair (Mypy, TypeScript `tsc`, GHC) is now the default in practical systems.
  - **Checker as RL reward.** See §4.
- **LLMs judging well-typedness directly** is only measured indirectly. TF-Bench measures inference rather than checking. The PLDI 2025 paper cites an external evaluation reporting 40–60% compilation-error rates for frontier models on OCaml and Haskell tasks.\[15\] That figure is second-hand and should be treated as indicative, but it confirms that LLMs' implicit "type checking" is unreliable in low-resource typed functional languages.

### 3. Term finding: inhabitation, type-directed synthesis, proof-term generation

**(a) Neural inhabitation directly on STLC / intuitionistic propositional logic**

- **Sekiyama, Imanishi, Suenaga (arXiv 1706.06462, 2017).** A seq2seq "neural machine translation" from propositions to $\lambda$-term proofs. It proved "around 50%" of benchmark formulas.\[16\]\[17\]
- **Sekiyama & Suenaga, "Automated Proof Synthesis for the Minimal Propositional Logic with Deep Neural Networks" (APLAS 2018, LNCS 11275; arXiv 1805.11799).**\[18\]
  - Setting: STLC with products and sums. A tree-convolution network over the proposition's AST predicts which of 8 inference rules to apply next to fill a hole in a partial proof term. Best-first search uses this prediction, and GHCi type-checks candidates.\[16\]
  - Training data: 167,744 normal-form proof terms. Rule-prediction accuracy is 96.79%.\[16\]
  - On propositions whose proofs have size $> 9$, it synthesizes proofs for **93.2%**, versus 31.4% for the earlier seq2seq approach, at 4.56 s vs 29.03 s average.\[16\]
  - This is the closest published match to "an AI model specialized in synthesizing lambda terms for a given type."
- **Kusumoto, Yahata, Sakai (Preferred Networks; arXiv 1811.00796, 2018).**
  - Method: deep RL (approximate policy iteration) over Dyckhoff's LJT sequent calculus, with a gated graph neural network value function over a term-merging graph representation of sequents.\[19\]\[20\]
  - "Within the specified time limit, our prover solved 84% of the theorems in a benchmark library, while tauto was able to solve only 52%."\[21\]
  - Caveats: the authors acknowledge that the tableau prover fCube proves most of these theorems in milliseconds.\[20\] I found no peer-reviewed venue.

**(b) Neural-guided and symbolic type-directed program synthesis**

- **TyGAR / H+ (Guo, James, Justo, Zhou, Wang, Jhala, Polikarpova; POPL 2020)** and **Hoogle+ (OOPSLA 2020).** These reduce Hoogle-style component synthesis to type inhabitation over Petri nets with type-guided abstraction refinement, handling polymorphism and type classes.\[22\]\[23\] Over 291 Haskell components, H+ returned a useful solution in the top five for 33 of 44 queries, with a median time to first solution of 1.4 s.\[24\] **Hoogle⋆ (ECOOP 2023)** adds constants and $\lambda$-abstractions via symbolic execution.\[23\] These are purely symbolic; their ranking of many well-typed "junk" solutions is the obvious place to insert learned guidance.\[25\]
- **LambdaBeam (NeurIPS 2023).** Described as "the first neural search method for programming by example that is able to synthesize" programs with arbitrary lambda functions. A neural policy with a pointer network picks arguments and lambda constructions during bottom-up search over STLC-style terms. It contrasts itself with $\lambda^2$ (type-directed, symbolic).\[26\]
- **Canonical (Norman & Avigad; ITP 2025, LIPIcs 352).** "The first solver for type inhabitation in dependent type theory."\[4\] It searches exhaustively over $\Pi$-types, inductive types and structures, following Dowek's sound and complete procedure.\[27\]\[28\]
  - On the Natural Number Game it solves 84% in 51 s total, versus Aesop 36% and Duper 61%. Its proofs are on average 251× shorter.\[4\]\[27\]
  - From the type signature alone it synthesizes functions such as length-indexed `Vec` append.\[28\]
  - A 2026 follow-up, *Canonical-min* (arXiv 2603.01463), is a sound and complete inhabitation and unification solver in 185 lines of Lean.\[29\]
  - It is not neural. It matters here as the symbolic baseline any neural inhabitation model should beat, and as a natural target for learned guidance.

**(c) Neural proof-term and tactic generation in proof assistants (Curry–Howard at scale)**

- **Graph2Tac (Blaauwbroek, Olšák, Rute et al.; ICML 2024; Tactician for Coq).** A GNN over a faithful graph representation of Coq terms, trained on 520k definitions (260k theorems) from 120 packages.\[30\]\[31\]
  - Its online "definition task" embeds unseen definitions on the fly and raises theorems solved from 17.4% to 26.1%.\[32\]
  - Combined with an online k-NN, it beats CoqHammer, Proverbot9001 and a transformer baseline by at least 1.48×.\[33\]
- **Kogkalidis, Melkonian, Bernardy, "Learning Structure-Aware Representations of Dependent Types" (NeurIPS 2024).** Released the first large Agda dataset (agda2train), which records proof states at the sub-type level.\[34\]\[35\] Proposes QUILL, a structure-aware attention architecture with de Bruijn-style nameless references for dependently typed terms, evaluated on premise selection.\[35\]\[36\]\[37\]\[38\]
- **LLM provers with type-checker rewards (2024–2026).** DeepSeek-Prover-V1.5 (proof-assistant feedback plus RL plus MCTS), DeepSeek-Prover-V2 (Ren et al., arXiv 2504.21801, 2025), Kimina-Prover, Leanabell-Prover-V2, BFS-Prover, Seed-Prover and Seed-Prover 1.5.\[39\]\[40\]
  - DeepSeek-Prover-V2-671B reports 88.9% on miniF2F-test (pass@8192) and 49/658 PutnamBench problems. It uses GRPO with binary Lean-verification rewards and subgoal decomposition.\[41\] The arXiv abstract by Ren et al. confirms these figures: "reaching 88.9% pass ratio on the MiniF2F-test and solving 49 out of 658 problems from PutnamBench."
  - The Lean kernel, a type checker, is the verifier.\[42\] Every accepted output is a well-typed proof term, so these are the most capable "term finders for a given type" in existence. They are optimized for mathematics, not for $\lambda$-calculus inhabitation as such.

### 4. Elaborating types and completing partial terms (typed holes, constrained decoding, RL with verifiers)

- **Hazel + LLMs (Blinn, Li, Kim, Omar; OOPSLA 2024).** The Hazel language server gives the expected type and typing context of the hole $?_h$, which is always available thanks to total error recovery. It transitively retrieves relevant type definitions and headers for the prompt, then iterates with the checker. Static contextualization "can be more precise and robust than RAG." The authors propose ChatLSP so mainstream language servers can expose this.\[43\]\[44\]\[45\] They also found LLMs writing Hazel "borrow syntactic forms and library functions from OCaml and Elm."\[44\] This is evidence that LLMs pattern-match on surface syntax rather than on the type theory.
- **Type-constrained decoding (PLDI 2025, above).** Effectively performs type elaboration and inhabitation online during generation.
- **RL with compiler / language-server feedback.** RLCSF (arXiv 2510.22907) turns diagnostics from type checkers and language servers into dense, potential-based transition rewards.\[46\]\[47\] Earlier work (CompCoder, RLTF, RLCF) used compilability as a reward.\[48\]\[49\] This is the generalization of "type checker as reward" from Lean to ordinary typed languages.

## Comparison of approaches

| Approach | Tasks covered | Soundness | Strength | Weakness |
|---|---|---|---|---|
| Pure seq2seq/transformer on $\lambda$-terms (Miranda et al.; Flach et al.) | Inference, reduction | None | Near-perfect in-distribution | No evidence of depth/length generalization; fragile optimization |
| GNN / structure-aware encoders (LambdaNet, Graph2Tac, QUILL, Kusumoto et al.) | Inference, premise/tactic selection, proof search | Via external checker | Respects binding and dependency structure; handles unseen definitions | Engineering-heavy; per-system data extraction |
| Neural-guided search with checker (Sekiyama & Suenaga; LambdaBeam) | Inhabitation | Sound (checker-verified) | 93.2% on larger IPL proofs | Small logics; benchmarks are synthetic |
| LLM + generate–check–repair | Inference, synthesis | Sound on acceptance | No training needed; general | Many iterations; fails on low-resource typed FP |
| Type-constrained decoding | Synthesis, elaboration | Sound, incomplete | Cuts compilation errors by more than half on HumanEval and MBPP, including for 30B+ open-weight models | Needs logits; per-language engineering |
| RL with verifier reward (Lean/Coq provers) | Inhabitation (proof terms) | Sound | SOTA proof search | Math-centric; very high compute (pass@8192) |
| Symbolic inhabitation (Canonical, H+/Hoogle+, Hoogle⋆) | Inhabitation, synthesis | Sound (complete for Canonical) | Strong, fast baselines | Ranking/relevance of many solutions; exponential worst case |

A related result on reduction rather than typing: Flach, Moreira and Lamb (arXiv 2304.09276) trained a seq2seq transformer on **untyped** $\lambda$-calculus normal-order $\beta$-reduction. They report 88.89% one-step accuracy on random terms and 99.73% on Church-encoded Booleans, and 97.70% full normalization on open Boolean terms.\[50\]\[51\] Cross-distribution transfer collapses: models trained on Boolean terms score 0–0.17% on random terms.\[51\] That is the same out-of-distribution failure seen in type inference.

## What is mature vs. open

**Mature**
- Using type checkers (Lean, Coq, Agda, GHC, `tsc`, Mypy) as verifiers, filters and RL rewards for generated terms.
- Neural annotation prediction for TypeScript and Python, as assistance rather than inference.
- Type-constrained decoding for simply-typed-core languages, proven sound.
- Neural-guided proof search for intuitionistic propositional logic, and large-scale LLM proof-term generation in Lean.
- Symbolic inhabitation in dependent type theory (Canonical) and polymorphic component synthesis (H+/Hoogle+).

**Open**
- **Systematic generalization.** No published model learns STLC or Hindley–Milner inference that provably or empirically extrapolates to deeper terms. The IBM study never tested it, and the untyped-reduction study shows transfer collapsing. General length-generalization theory (e.g., the RASP conjecture of Zhou et al., ICLR 2024) suggests success only where a short algorithm aligns with the architecture.\[52\]\[53\] Unification with an occurs-check and substitution is a hard case for that.
- **Principal types and polymorphism.** LLMs reach only 55.85% on TF-Bench_pure. No benchmark targets System F *typability* (undecidable), rank-$n$ types or dependent-type *inference* (elaborating implicit arguments) with neural methods.
- **Learned guidance for $\lambda$-calculus inhabitation at scale.** Neither Canonical nor Hoogle+ has been coupled with a learned policy in a published evaluation that I found.
- **Standard benchmarks** for the three tasks over $\lambda$-calculi, with length splits and an untyped/ill-typed class. Today's evidence comes from one-off synthetic datasets.
- **Type-constrained decoding beyond simple types:** polymorphism, higher-order types (currently pruned), dependent types, and closed-API models.

## Recommendations

1. **To build a "type-inference AI":** don't train a network to output types end to end. Use a learned model for the *search* decisions (which unification order, which annotation, which subterm to generalize) and keep Algorithm W/J or a bidirectional checker as the arbiter. Expect wins mainly on ill-typed or partially annotated programs (error localization, annotation suggestion), not on clean inference, which is already PTIME or effectively fast.
2. **For term finding:**
   - Start from a sound and complete symbolic baseline: Canonical for dependent types, an LJT-style prover for STLC, Hoogle+ for polymorphic components.
   - Add a learned policy over hole-filling actions, as in Sekiyama & Suenaga and Kusumoto et al., using tree- or graph-structured encoders.
   - Train with RL where the type checker gives a binary reward. This is the recipe proven at scale by Lean provers.
3. **For elaboration with LLMs:** combine typed-hole context retrieval (Hazel/ChatLSP-style) with type-constrained decoding when logits are available, and with checker-in-the-loop repair otherwise.
4. **For evaluation:** report results on terms deeper or larger than training, on NL-free variants (as TF-Bench does), and on ill-typed inputs. Compare against symbolic solvers on time-to-solution, not just accuracy.

## Caveats

- Several key lambda-calculus-specific papers (Miranda et al.; Kusumoto et al.; Flach et al.) are arXiv preprints without a confirmed peer-reviewed venue. Miranda et al. report mostly *train* accuracy.\[5\]
- TF-Bench has only 188 tasks. The 55.85% top score is for models available in 2025,\[7\] and newer reasoning models may score higher.
- The PLDI paper's OCaml/Haskell error rates come from a cited third-party evaluation.
- Kusumoto et al.'s 84% vs 52% comparison is restricted to LJT-based provers; fCube solves most of the same theorems in milliseconds.\[20\]
- Neural ML type inference for Python/TypeScript is measured against developer annotations, not principal types. Its accuracy figures are not comparable to $\lambda$-calculus inference accuracy.

## Sources

1. [Transformer Models for Type Inference in the Simply Typed Lambda Calculus: A Case Study in Deep Learning for Code](https://arxiv.org/pdf/2304.10500)
2. [On Long Normal Inhabitants of a Type](https://www.researchgate.net/publication/31048467_On_Long_Normal_Inhabitants_of_a_Type)
3. [Type-Based Synthesis and the Inhabitation Problem](http://cs.ipm.ac.ir/asoc2017/Content/LectureNote/day_5/Rehof_day5_p2_1.pdf)
4. [Canonical for Automated Theorem Proving in Lean Chase Norman # Ñ](https://drops.dagstuhl.de/storage/00lipics/lipics-vol352-itp2025/LIPIcs.ITP.2025.14/LIPIcs.ITP.2025.14.pdf)
5. <https://arxiv.org/pdf/2304.10500v1>
6. [Transformer Models for Type Inference in the Simply Typed Lambda Calculus: A Case Study in Deep Learning for Code](https://arxiv.org/abs/2304.10500)
7. <https://arxiv.org/html/2509.23686>
8. [LAMBDANET: PROBABILISTIC TYPE INFERENCE](https://openreview.net/attachment?id=Hkx6hANtwH&name=original_pdf)
9. [LambdaNet: Probabilistic Type Inference Using Graph Neural Networks](https://mlanthology.org/iclr/2020/wei2020iclr-lambdanet/)
10. [Probabilistic Type Inference by Optimising Logical and Natural Constraints⋆](https://arxiv.org/pdf/2004.00348)
11. [Automated Type Annotation in Python Using Large Language Models Varun Bharti∗](https://arxiv.org/pdf/2508.00422)
12. [Published as a conference paper at ICLR 2023 TYPET5: SEQ2SEQ TYPE INFERENCE](https://arxiv.org/pdf/2303.09564)
13. [Published as a conference paper at ICLR 2023 TYPET5: SEQ2SEQ TYPE INFERENCE](https://www.cs.utexas.edu/~isil/TypeT5.pdf)
14. [\[Quick Review\] LambdaNet: Probabilistic Type Inference using Graph Neural Networks](https://liner.com/review/lambdanet-probabilistic-type-inference-using-graph-neural-networks)
15. <https://arxiv.org/pdf/2504.09246>
16. <https://arxiv.org/pdf/1805.11799>
17. [Towards Proof Synthesis Guided by Neural Machine Translation for Intuitionistic Propositional Logic](https://arxiv.org/pdf/1706.06462)
18. [Automated Proof Synthesis for the Minimal Propositional Logic with Deep Neural Networks](https://link.springer.com/chapter/10.1007/978-3-030-02768-1_17)
19. [Automated Theorem Proving](https://www.emergentmind.com/topics/automated-theorem-proving)
20. <https://arxiv.org/pdf/1811.00796v1>
21. [Automated Theorem Proving in Intuitionistic Propositional Logic by Deep Reinforcement Learning](https://arxiv.org/abs/1811.00796)
22. [205 Digging for Fold: Synthesis-Aided API Discovery for Haskell](https://dl.acm.org/doi/pdf/10.1145/3428273)
23. [Hoogle⋆: Constants and λ-abstractions in Petri-net-based Synthesis using Symbolic Execution](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2023.4)
24. [\[1911.04091\] Program Synthesis by Type-Guided Abstraction Refinement](https://arxiv.org/abs/1911.04091)
25. [Nadia Polikarpova - Haskell Foundation](https://haskell.foundation/podcast/10/)
26. [LAMBDABEAM: Neural Program Search with Higher-Order Functions and Lambdas](https://proceedings.neurips.cc/paper_files/paper/2023/file/a10da26f47120217c1b7c2aeb2979048-Paper-Conference.pdf)
27. [Canonical for Automated Theorem Proving in Lean](https://arxiv.org/html/2504.06239v1)
28. [arxiv.org](https://arxiv.org/html/2504.06239v2)
29. [\[2603.01463\] Implementing Dependent Type Theory Inhabitation and Unification](https://arxiv.org/abs/2603.01463)
30. [Announcing Graph2Tac, a prover based on Tactician's new API - Announcements - Rocq Prover](https://discourse.rocq-prover.org/t/announcing-graph2tac-a-prover-based-on-tacticians-new-api/2171)
31. [Publications](https://coq-tactician.github.io/publications/)
32. [Changelog posts](https://coq-tactician.github.io/changelog/)
33. [Graph2Tac: Online Representation Learning of Formal Math Concepts](https://chatpaper.com/chatpaper/paper/35874)
34. [Learning Structure-Aware Representations of Dependent Types - Aalto University's research portal](https://research.aalto.fi/en/publications/learning-structure-aware-representations-of-dependent-types)
35. [Learning Structure-Aware Representations of Dependent Types \[Quick Review\]](https://liner.com/review/learning-structureaware-representations-of-dependent-types)
36. [Learning Structure-Aware Representations of Dependent Types](https://mlanthology.org/neurips/2024/kogkalidis2024neurips-learning/)
37. [Learning Structure-Aware Representations of Dependent Types — Machine Learning](https://awesomepapers.io/machine-learning/papers/2402.02104)
38. [Learning Structure-Aware Representations of Dependent Types](http://aitp-conference.org/2025/abstract/AITP_2025_paper_5.pdf)
39. [Leanabell-Prover-V2: Verifier-integrated Reasoning for Formal Theorem Proving via Reinforcement Learning](https://arxiv.org/pdf/2507.08649)
40. [Seed-Prover 1.5: Mastering Undergraduate-Level Theorem Proving via Learning from Experience](https://arxiv.org/pdf/2512.17260)
41. [DeepSeek-Prover-V2 - Srikanth Bhakthan](https://bhakthan.substack.com/p/deepseek-prover-v2)
42. [DeepSeek-Prover V2](https://learn.engineering.vips.edu/ai-models/deepseek-prover-v2)
43. [Statically Contextualizing Large Language Models with Typed Holes (SPLASH 2024 - OOPSLA 2024) - SPLASH 2024](https://2024.splashcon.org/details/splash-2024-oopsla/71/Statically-Contextualizing-Large-Language-Models-with-Typed-Holes)
44. [Statically Contextualizing Large Language Models with Typed Holes](https://dl.acm.org/doi/10.1145/3689728)
45. [Paper page - Statically Contextualizing Large Language Models with Typed Holes](https://huggingface.co/papers/2409.00921)
46. [Reinforcement Learning from Compiler and Language Server Feedback](https://arxiv.org/html/2510.22907)
47. [Reinforcement Learning from Compiler and Language Server Feedback](https://arxiv.org/pdf/2510.22907)
48. [Coarse-Tuning Models of Code with Reinforcement Learning Feedback](https://arxiv.org/pdf/2305.18341)
49. [A Survey on Large Language Models for Code Generation](https://arxiv.org/pdf/2406.00515)
50. [(PDF) A Neural Lambda Calculus: Neurosymbolic AI meets the foundations of computing and functional programming](https://www.researchgate.net/publication/370127419_A_Neural_Lambda_Calculus_Neurosymbolic_AI_meets_the_foundations_of_computing_and_functional_programming)
51. [Towards a Neural Lambda Calculus: Neurosymbolic AI Applied to the Foundations of Functional Programming](https://arxiv.org/pdf/2304.09276)
52. [\[2310.16028\] What Algorithms can Transformers Learn? A Study in Length Generalization](https://arxiv.org/abs/2310.16028)
53. [What Algorithms can Transformers Learn? A Study in Length Generalization](https://ee.stanford.edu/event/03-07-2024/what-algorithms-can-transformers-learn-study-length-generalization)
