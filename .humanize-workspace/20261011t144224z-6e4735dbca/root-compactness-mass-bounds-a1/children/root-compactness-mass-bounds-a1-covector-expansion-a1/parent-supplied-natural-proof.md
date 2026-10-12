# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_mass_bounds-a1`
- Child DAG node: `root.compactness_mass_bounds-a1.covector_expansion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Fact A in the parent proof's conventions (an alternating n-linear map is determined by its values on increasing tuples of basis vectors, and dx^β(e_γ) = δ_{βγ}), proved here in full.

Notation:
- e_i := EuclideanSpace.single i 1 = EuclideanSpace.basisFun (Fin P) ℝ i (EuclideanSpace.basisFun_apply).
- For a tuple v : Fin n → Fin P, e_v := (e_{v(0)},…,e_{v(n−1)}).
- I(n,P) := SimonMultiIndex n P = Fin n ↪o Fin P, a finite type.
- For β ∈ I(n,P), α(e_β) := euclideanCovectorCoordinate α β and dx^β := wedgeCovectors n (fun j => EuclideanSpace.proj (β j)).

1. (Kronecker property.) Let β, γ ∈ I(n,P). By wedgeCovectors_apply_det, dx^β(e_γ) = det M, where M_{ij} = proj(β(i))(e_{γ(j)}) is 1 if β(i) = γ(j) and 0 otherwise.
(a) If β = γ, then M_{ij} = 1 iff β(i) = β(j) iff i = j (β is injective). So M is the identity matrix and dx^β(e_β) = 1.
(b) If β ≠ γ, there is i with β(i) ∉ {γ(0),…,γ(n−1)}. Otherwise range β ⊆ range γ. Both ranges have exactly n elements because β and γ are injective (Set.ncard_range_of_injective), so range β = range γ (Set.eq_of_subset_of_ncard_le). An order embedding of the well-order Fin n is determined by its range (OrderEmbedding.range_inj_of_wellFoundedLT), so β = γ, a contradiction. For this i, row i of M is zero, hence det M = 0 (Matrix.det_eq_zero_of_row_eq_zero).
Thus dx^β(e_γ) = δ_{βγ}.
2. (Agreement on increasing tuples.) Let R := Σ_{β∈I(n,P)} α(e_β)·dx^β, a continuous alternating n-linear map. For γ ∈ I(n,P), Step 1 gives R(e_γ) = Σ_β α(e_β)·δ_{βγ} = α(e_γ).
3. (Agreement on injective tuples.) Let v : Fin n → Fin P be injective, and let σ := Tuple.sort v, a permutation of Fin n with v∘σ monotone (Tuple.monotone_sort). Since v∘σ is also injective, it is strictly increasing, so γ := v∘σ defines an element of I(n,P) (OrderEmbedding.ofStrictMono) with e_γ = e_v∘σ. For every alternating map f, f(e_v∘σ) = sign(σ)·f(e_v) (AlternatingMap.map_perm). Applying this to α and to R and using Step 2 gives sign(σ)·α(e_v) = α(e_γ) = R(e_γ) = sign(σ)·R(e_v). Acting with sign(σ)⁻¹ (inv_smul_smul) yields α(e_v) = R(e_v).
4. (Conclusion.) Two alternating multilinear maps on ℝ^P that agree on all tuples (e_{v(0)},…,e_{v(n−1)}) with v injective are equal (Module.Basis.ext_alternating, applied to the basis (EuclideanSpace.basisFun (Fin P) ℝ).toBasis). Hence α and R are equal as alternating maps, and therefore as continuous alternating maps (ContinuousAlternatingMap.toAlternatingMap_injective). So α = Σ_β α(e_β)·dx^β.
5. (Degenerate cases.) Steps 1–4 cover them. For n = 0, I(0,P) has one element, dx^β is the constant covector 1, and the identity reads α = α(())·1. For n > P, I(n,P) is empty, so R = 0, and no injective v exists, so Step 4 gives α = 0 = R. ∎

## Key steps

1. dx^β(e_γ) = det[δ_{β(i)γ(j)}] = δ_{βγ} for increasing β, γ.
2. R := Σ_β α(e_β)dx^β agrees with α on increasing basis tuples.
3. Sorting an injective tuple (Tuple.sort, AlternatingMap.map_perm) gives agreement on all injective basis tuples.
4. Module.Basis.ext_alternating gives α = R.

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
