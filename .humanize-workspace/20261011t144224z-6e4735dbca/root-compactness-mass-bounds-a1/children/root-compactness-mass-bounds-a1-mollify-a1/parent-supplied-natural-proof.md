# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_mass_bounds-a1`
- Child DAG node: `root.compactness_mass_bounds-a1.mollify-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the final sentence of parent proof Step 7: a continuous compactly supported form supported in an open set is a uniform limit of test forms supported there, by mollification. Here the mollification is followed by multiplication with a smooth cutoff, which keeps the support exactly inside V.

Notation: |α| := covectorEuclideanNorm α; ‖α‖ is the operator norm of α ∈ Covector (Eucl P) n; e_i := EuclideanSpace.basisFun (Fin P) ℝ i; N := #(Fin n → Fin P).

1. (Norm comparison.) For every covector α and every I : Fin n → Fin P, |α(e_{I(0)},…,e_{I(n−1)})| ≤ ‖α‖·∏_j‖e_{I(j)}‖ = ‖α‖ (ContinuousAlternatingMap.le_opNorm and ‖e_i‖ = 1). Hence |α|² ≤ N‖α‖², i.e. |α| ≤ √N‖α‖. Put c := √N + 1 > 0.
2. (Intermediate open set.) K := tsupport ω is compact (HasCompactSupport ω) and K ⊆ V. Choose an open V' with K ⊆ V', closure(V') compact and closure(V') ⊆ V (exists_open_between_and_isCompact_closure; ℝ^P is locally compact and regular).
3. (Cutoff.) Choose a C^∞ function χ : ℝ^P → [0,1] with support χ = V' and χ(x) = 1 ⇔ x ∈ K (exists_contDiff_support_eq_eq_one_iff with the open set V', the closed set K ⊆ V' and smoothness order ⊤). Then tsupport χ = closure(V') ⊆ V, and tsupport χ is compact.
4. (Mollification.) ω is continuous with compact support, hence uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous). Convolving ω with a normalized C^∞ bump of small enough radius gives a C^∞ map g : ℝ^P → Covector (Eucl P) n with ‖g(x) − ω(x)‖ < ε/c for every x (UniformContinuous.exists_contDiff_dist_le in Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean, whose proof is exactly this convolution). It applies because ℝ^P is finite-dimensional and Covector (Eucl P) n is complete.
5. (The test form.) Let η(x) := χ(x)·g(x).
- η is C^∞ (ContDiff.smul).
- tsupport η ⊆ tsupport χ = closure(V') ⊆ V ⊆ U (tsupport_smul_subset_left).
- tsupport η is compact, being a closed subset of the compact set closure(V').
Hence η ∈ TestFormOn U n (smooth, compactly supported, tsupport ⊆ U) and tsupport η ⊆ V.
6. (Estimate.) If x ∈ K, then χ(x) = 1, so ω(x) − η(x) = ω(x) − g(x) and ‖ω(x) − η(x)‖ < ε/c. If x ∉ K, then ω(x) = 0, so ‖ω(x) − η(x)‖ = χ(x)‖g(x)‖ ≤ ‖g(x)‖ = ‖g(x) − ω(x)‖ < ε/c, using 0 ≤ χ(x) ≤ 1. So ‖ω(x) − η(x)‖ ≤ ε/c for every x, and by Step 1, |ω(x) − η(x)| ≤ √N·ε/c ≤ ε. ∎

## Key steps

1. |α| ≤ √N‖α‖ in terms of the operator norm.
2. Choose V' with tsupport ω ⊆ V' and closure V' ⊆ V compact, and a smooth cutoff χ with χ = 1 exactly on tsupport ω and support χ = V'.
3. Mollification gives a smooth g with ‖g − ω‖ < ε/c everywhere (UniformContinuous.exists_contDiff_dist_le).
4. η := χ·g is a test form with tsupport ⊆ V and |ω − η| ≤ ε.

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
