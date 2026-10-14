# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_mass_bounds-a1`
- Child DAG node: `root.compactness_mass_bounds-a1.testform_separable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 3 (countable dense families). It is carried out through coefficient vectors, so only the finite-dimensional space ℝ^(Fin n → Fin P) is needed. Covector (Eucl P) n has no FiniteDimensional or SecondCountableTopology instance at this Mathlib pin.

Notation: |α| := covectorEuclideanNorm α; e_i := EuclideanSpace.basisFun (Fin P) ℝ i; 𝓘 := Fin n → Fin P and N := #𝓘. ℝ^𝓘 carries the sup norm ‖·‖_∞.

1. (Coefficient map.) Define c : Covector (Eucl P) n → ℝ^𝓘 by c(α) := (α(e_{I(0)},…,e_{I(n−1)}))_{I∈𝓘}. Each coordinate of c is evaluation at a fixed tuple, so c is linear and continuous. Since |c(α)_I| ≤ ‖c(α)‖_∞ (norm_le_pi_norm), |α|² = Σ_{I strictly increasing} c(α)_I² ≤ N·‖c(α)‖_∞². Hence |α| ≤ √N·‖c(α)‖_∞.
2. (Embedding.) Let K := closure(W), which is compact by hypothesis; regard it as a compact metric space. Let D := {ω ∈ TestFormOn U n : tsupport ω ⊆ W}. For ω ∈ D define F_ω ∈ C(K, ℝ^𝓘) by F_ω(x) := c(ω(x)). It is continuous because ω is smooth, hence continuous, and c is continuous.
3. (Second countability.) C(K, ℝ^𝓘) is second countable: K is compact and metrizable, hence second countable and locally compact, and ℝ^𝓘 is second countable (ContinuousMap.instSecondCountableTopology, Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean). Its topology is given by the sup metric, and dist(F(x), G(x)) ≤ dist(F, G) for x ∈ K (ContinuousMap.dist_apply_le_dist).
4. (Countable dense subset of the image.) The set A := {F_ω : ω ∈ D} is separable (TopologicalSpace.IsSeparable.of_separableSpace). Since C(K, ℝ^𝓘) is metrizable, there is a countable S ⊆ A with A ⊆ closure(S) (TopologicalSpace.IsSeparable.exists_countable_dense_subset).
5. (Definition of E.) For every s ∈ S choose ω_s ∈ D with F_{ω_s} = s, and let E := {ω_s : s ∈ S}. E is countable, being the range of a map on the countable set S. Also E ⊆ D, so every η ∈ E belongs to TestFormOn U n and has tsupport η ⊆ W.
6. (Density.) Let ω ∈ TestFormOn U n with tsupport ω ⊆ W (so ω ∈ D), let ε > 0, and put δ := ε/(√N + 1) > 0. Since F_ω ∈ closure(S), there is s ∈ S with dist(F_ω, s) < δ. Let η := ω_s ∈ E, so F_η = s.
- For x ∈ K: by linearity of c, ‖c(ω(x) − η(x))‖_∞ = ‖F_ω(x) − F_η(x)‖_∞ ≤ dist(F_ω, F_η) < δ. By Step 1, |ω(x) − η(x)| ≤ √N·δ ≤ ε.
- For x ∉ K: x ∉ tsupport ω and x ∉ tsupport η, since both are ⊆ W ⊆ K. So ω(x) = η(x) = 0 and |ω(x) − η(x)| = 0 ≤ ε. ∎

## Key steps

1. The coefficient map c : Covector → ℝ^(Fin n → Fin P) is continuous and linear, with |α| ≤ √N·‖c(α)‖_∞.
2. ω ↦ c∘ω embeds D_W into C(closure W, ℝ^(Fin n → Fin P)), which is second countable.
3. Take a countable dense subset of the image and choose preimages to form E ⊆ D_W.
4. Sup-distance < δ on closure W gives |ω − η| ≤ ε everywhere, since both forms vanish off closure W.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch06/Contract.lean project/GMT/Ch06/Submission.lean and workspace GMT/Ch06/Contract.lean (all ea3ee0ddd08be5db60dced2b002e9f60fd87091910069abcfcbd7e34db89853d)`
- `sed -n 240,345p book/chapter-06.txt (Simon 2.6-2.15 and the Banach-Alaoglu paragraph before 2.15)`
- `cat simongmt Poincare/SimonGMT/Chapter06/{Mass,FormSupNorm,Currents,Forms,FormsDuality,Representation,CurrentLocalEquality,FixedSupportCurrentTopology,CurrentDistributionEquivalence}.lean`
- `rg -n 'theorem exists_open_between_and_isCompact_closure|theorem IsCompact.tendsto_subseq|theorem dist_normed_convolution_le|theorem support_convolution_subset|theorem Integrable.bdd_mul|uniformContinuous_of_continuous' mathlib/Mathlib`
- `rg -n 'exists_contDiff_support_eq_eq_one_iff|exists_contDiff_tsupport_subset|exists_smooth_tsupport_subset' mathlib/Mathlib`
- `cat mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean; sed -n 60,100p mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `sed -n 60,90p mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean; rg -n 'isSeparable' mathlib/Mathlib/Topology/Bases.lean`
- `sed -n 900,925p mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean (Module.Basis.ext_alternating)`
- `rg -n '^theorem (continuous_infE[dD]ist|infE[dD]ist_zero_of_mem|mem_closure_iff_infE[dD]ist_zero)' mathlib/Mathlib`
- `#synth CompleteSpace / FiniteDimensional / SecondCountableTopology / ProperSpace (Covector (Eucl P) n); BorelSpace (Eucl P); Fintype (SimonMultiIndex n P); FirstCountableTopology (E -> R) for countable E`
- `python3 listing of dag.json lean_name values; nodes/root-federer-fleming-a1/decomposition-v1.json (should_split false)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement and gmt-compare.py contract_scope/child_modules for all 8 children`
- `lake env lean Scratch/Ch_<key>.lean for the 8 generated NodeChallenge modules (0 errors)`
- `lake env lean Scratch/{Stmts,ContForms,Repr,Weak,Leaves,Cov,Sep,Final}.lean; #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Representation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FixedSupportCurrentTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentDistributionEquivalence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-federer-fleming-a1/decomposition-v1.json`
- `/tmp/cmb_decomp_scratch/Scratch/Final.lean`
- `/tmp/cmb_decomp_scratch/Scratch/Leaves.lean`
- `/tmp/cmb_decomp_scratch/Scratch/Cov.lean`
- `/tmp/cmb_decomp_scratch/Scratch/Sep.lean`
- `/tmp/cmb_decomp_scratch/Scratch/Weak.lean`
- `/tmp/cmb_decomp_scratch/Scratch/Repr.lean`
- `/tmp/cmb_decomp_scratch/Scratch/ContForms.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. Contract and Submission are byte-identical (sha256 ea3ee0dd…). They state CompactnessUnderMassBounds over SimonGMT's GeometricCurrentOn, TestFormOn, massOn, WeaklyConvergesOn, covectorEuclideanNorm and IsMeasureRepresentation.

SimonGMT provides GeometricCurrentOn.le_massOn, WeaklyConvergesOn.massOn_le_liminf (2.14), wedgeCovectors_apply_det, euclideanCovectorCoordinate and covectorEuclideanNorm_neg. It has no compactness, separability, mollification or representation-extension lemma (no match).

Mathlib provides exists_open_between_and_isCompact_closure, exists_contDiff_support_eq_eq_one_iff, UniformContinuous.exists_contDiff_dist_le (SmoothApprox, needs an extra import), HasCompactSupport.uniformContinuous_of_continuous, IsCompact.tendsto_subseq, isCompact_univ_pi, ContinuousMap.instSecondCountableTopology (extra import), IsSeparable.exists_countable_dense_subset, Module.Basis.ext_alternating, AlternatingMap.map_perm, Tuple.monotone_sort, OrderEmbedding.range_inj_of_wellFoundedLT, Metric.infEDist lemmas and Integrable.bdd_mul.

Covector (Eucl P) n has a CompleteSpace instance but no FiniteDimensional or SecondCountableTopology instance.

In a scratch build of the frozen project:
- all 8 exact child statements pass the validator and elaborate as comparator NodeChallenge modules;
- each statement is proved with no sorry, each composite only from its declared siblings;
- CompactnessUnderMassBounds follows from weak_subseq and continuous_form_conv, with axioms [propext, Classical.choice, Quot.sound].

The DAG reserves only the 12 depth-1 names, so the cmb_ names are free.
