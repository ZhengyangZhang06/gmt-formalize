# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_mass_bounds-a1`
- Child DAG node: `root.compactness_mass_bounds-a1.exhaustion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 1 (exhaustion). The parent's condition B̄_{1/i}(x) ⊆ U is expressed here through the extended distance to ℝ^P∖U, so no convention for dist(x, ∅) is needed. The index is shifted to avoid 1/0.

Notation: |x| is the Euclidean norm on ℝ^P = Eucl P. For x ∈ ℝ^P let d(x) := inf{edist(x, y) : y ∈ ℝ^P∖U} ∈ [0, ∞] (Lean: Metric.infEDist x Uᶜ). If U = ℝ^P then d ≡ ∞.

1. d is continuous (Metric.continuous_infEDist). Since ℝ^P∖U is closed (U is open), d(x) = 0 iff x ∈ closure(ℝ^P∖U) = ℝ^P∖U (Metric.mem_closure_iff_infEDist_zero). In particular d(x) > 0 for every x ∈ U.
2. For i ∈ ℕ define W_i := {x : |x| < i} ∩ {x : (i+1)⁻¹ < d(x)}, where (i+1)⁻¹ ∈ (0, ∞).
3. W_i is open: it is the intersection of the preimages of the open sets (−∞, i) and ((i+1)⁻¹, ∞] under the continuous maps x ↦ |x| and d.
4. W_i ⊆ B̄_i(0), and B̄_i(0) is closed, so closure(W_i) ⊆ B̄_i(0). B̄_i(0) is compact because ℝ^P is proper, so closure(W_i) is compact as a closed subset of a compact set.
5. F_i := {x : (i+1)⁻¹ ≤ d(x)} is closed (d is continuous) and contains W_i, so closure(W_i) ⊆ F_i. Suppose some x ∈ closure(W_i) is not in U. Then d(x) = 0 by Step 1, while x ∈ F_i gives d(x) ≥ (i+1)⁻¹ > 0 (since i+1 < ∞), a contradiction. Hence closure(W_i) ⊆ U. Together with Steps 3 and 4, CompactlyContainedOpen W_i U holds for every i.
6. Let K ⊆ U be compact. If K = ∅ then K ⊆ W_0. Otherwise:
- K is bounded, so there is R ∈ ℝ with |x| ≤ R for all x ∈ K. Choose i₁ ∈ ℕ with i₁ > R.
- d is continuous and K is compact and nonempty, so d attains its minimum on K at some x₀ ∈ K (IsCompact.exists_isMinOn). Since x₀ ∈ U, Step 1 gives m := d(x₀) > 0.
- Choose i₂ ∈ ℕ with (i₂)⁻¹ < m (ENNReal.exists_inv_nat_lt).
- Put i := max(i₁, i₂). For x ∈ K we have |x| ≤ R < i₁ ≤ i and (i+1)⁻¹ ≤ (i₂)⁻¹ < m ≤ d(x), so x ∈ W_i. Hence K ⊆ W_i.
7. Steps 5 and 6 show that (W_i)_{i∈ℕ} has both required properties. ∎

## Key steps

1. d(x) := infEDist(x, ℝ^P∖U) is continuous and vanishes exactly off U.
2. W_i := {|x| < i} ∩ {d > (i+1)⁻¹} is open.
3. closure W_i ⊆ closedBall(0,i) ∩ {d ≥ (i+1)⁻¹}, which is compact and contained in U.
4. A compact K ⊆ U is bounded and min_K d > 0, so K ⊆ W_i for large i.

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
