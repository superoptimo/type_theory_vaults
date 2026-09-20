# A Semantic Framework for Proof Evidence — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Foundational Proof Certificates (FPC) Framework** : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]
   - Proof certificates as exported documents of proof evidence : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]
   - The four desiderata for a general notion of proof certificate : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]
   - The five FPC parameters: polarization, certificate terms, indexes, clerks, experts
   - Kernels as trusted implementations of an augmented focused proof system : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]
   - Proof checking as computation and interaction : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]
   - Proof reconstruction versus mere provability checking : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]

2. **Focused Sequent Calculus** : [[Focused-Sequent-Calculus|Link]]
   - Atoms of inference versus molecules (synthetic inference rules) : [[Focused-Sequent-Calculus|Link]]
   - Asynchronous and synchronous phases
   - Polarized formulas and connective polarity
   - The LKF focused proof system for first-order classical logic
   - The LJF focused proof system for first-order intuitionistic logic
   - Structural rules: store, release, decide, cut
   - Completeness and cut-elimination for focused systems : [[Focused-Sequent-Calculus|Link]]
   - LKneg and LKpos as invertible and non-invertible restrictions of LKF

3. **Clerks and Experts as an Augmented Kernel** : [[Clerks-and-Experts-as-an-Augmented-Kernel|Link]]
   - Augmenting LKF and LJF into LKFa and LJFa
   - Clerk predicates governing the asynchronous phase
   - Expert predicates governing the synchronous phase
   - The tax-office clerks-and-experts analogy : [[Clerks-and-Experts-as-an-Augmented-Kernel|Link]]
   - Deterministic versus non-deterministic certificate behavior : [[Clerks-and-Experts-as-an-Augmented-Kernel|Link]]
   - Indexes as the addressing mechanism for stored formulas : [[Clerks-and-Experts-as-an-Augmented-Kernel|Link]]

4. **Case Studies in Proof Certificate Design** : [[Case-Studies-in-Proof-Certificate-Design|Link]]
   - A CNF decision procedure as an FPC : [[Case-Studies-in-Proof-Certificate-Design|Link]]
   - Oracle strings for LKpos proofs : [[Case-Studies-in-Proof-Certificate-Design|Link]]
   - Binary resolution refutations as an FPC : [[Case-Studies-in-Proof-Certificate-Design|Link]]
   - Simply typed $\lambda$-terms in $\eta$-long $\beta$-normal form as certificates : [[Case-Studies-in-Proof-Certificate-Design|Link]]
   - Justified Horn clause proofs : [[Case-Studies-in-Proof-Certificate-Design|Link]]
   - Frege proofs encoded via Horn clause entailment : [[Case-Studies-in-Proof-Certificate-Design|Link]]
   - The mimic FPC and completeness of atomic initial rules : [[Case-Studies-in-Proof-Certificate-Design|Link]]

5. **Relating Classical and Intuitionistic Proof Checking** : [[Relating-Classical-and-Intuitionistic-Proof-Checking|Link]]
   - Hosting an LKFa kernel on an LJFa kernel
   - Chaudhuri's translation between LKF and LJF formulas : [[Relating-Classical-and-Intuitionistic-Proof-Checking|Link]]
   - Phase correspondence between classical and intuitionistic focusing : [[Relating-Classical-and-Intuitionistic-Proof-Checking|Link]]
   - Double-negation translations of classical into intuitionistic logic : [[Relating-Classical-and-Intuitionistic-Proof-Checking|Link]]

6. **Logic Programming as an Implementation Substrate** : [[Logic-Programming-as-an-Implementation-Substrate|Link]]
   - $\lambda$Prolog as the specification language for FPCs
   - $\lambda$-tree syntax and higher-order abstract syntax for bindings
   - Hypothetical reasoning for managing storage contexts
   - Unification and backtracking search in proof reconstruction : [[Logic-Programming-as-an-Implementation-Substrate|Link]]
   - Teyjus and other $\lambda$Prolog implementations : [[Logic-Programming-as-an-Implementation-Substrate|Link]]

7. **Trusted Kernels and Proof Sharing** : [[Trusted-Kernels-and-Proof-Sharing|Link]]
   - LCF-style provers and the abstract datatype of theorems
   - The de Bruijn criterion for trustworthy theorem provers : [[Trusted-Kernels-and-Proof-Sharing|Link]]
   - Grammars as an analogy for standardizing proof structure
   - Existing proof-sharing standards: OpenTheory, LFSC, MMT, Dedukti : [[Trusted-Kernels-and-Proof-Sharing|Link]]

8. **Extensions and Open Problems** : [[Extensions-and-Open-Problems|Link]]
   - Equational rewriting and paramodulation certificates : [[Case-Studies-in-Proof-Certificate-Design|Link]]
   - Linear logic, the LKU system, and unifying multiple logics
   - Multifocusing, expansion trees, and proof nets
   - The multicut rule and independent lemma reuse
   - FPCs for modal logics and dependently typed calculi
   - Certificates for model checking and inductive theorem proving

---
