# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.fiber_sum_glue-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

This is the summation device of steps 5, 6 and 7 of the parent proof (summing the area identities over the disjoint balls D_{j,m}, over the disjoint chart pieces A_j, and discarding the null part A_∞ whose f-image is null), isolated as one general measure-theoretic lemma. All sums are unordered sums in [0,∞] (∑' over subtypes), which may be regrouped arbitrarily.

1. (Fibre decomposition off f(Z).) Fix y ∉ f(Z). Then {x : x ∈ A ∧ f(x) = y} = ⋃_m {x : x ∈ B_m ∧ f(x) = y}, and the sets on the right are pairwise disjoint. Indeed, if x ∈ A and f(x) = y, then by (d) either x ∈ Z, which is impossible because then y = f(x) ∈ f(Z), or x ∈ B_m for some m. Conversely B_m ⊆ A by (a). Disjointness follows from (b).
2. (Sums over disjoint unions.) For pairwise disjoint sets S_m, the unordered [0,∞]-sum of h over ⋃_m S_m equals Σ_m of the sums over S_m: transport the sum along the equivalence ⋃_m S_m ≃ Σ_m S_m (Set.unionEqSigmaOfDisjoint; use Equiv.tsum_eq for its inverse, whose underlying point is the second component) and split the sum over the sigma type (ENNReal.tsum_sigma'). By step 1, N_A(y) = Σ_m N_{B_m}(y) for every y ∉ f(Z). (The subtype {x // x ∈ S ∧ f x = y} is definitionally the coercion of the set {x | x ∈ S ∧ f x = y}.)
3. (A.e. identity.) By (f), ν-a.e. y lies outside f(Z) (measure_eq_zero_iff_ae_notMem), so N_A = Σ_m N_{B_m} ν-a.e. No measurability of f(Z) is needed.
4. (Measurability, first conclusion.) Each N_{B_m} is ν-a.e. measurable by (g); a countable sum of a.e.-measurable [0,∞]-valued functions is a.e. measurable (AEMeasurable.ennreal_tsum, a deprecated alias that still compiles; or AEMeasurable.tsum); a function ν-a.e. equal to an a.e.-measurable function is a.e. measurable (AEMeasurable.congr with step 3). Hence N_A is ν-a.e. measurable.
5. (Target side.) ∫ N_A dν = ∫ Σ_m N_{B_m} dν (lintegral_congr_ae with step 3) = Σ_m ∫ N_{B_m} dν (lintegral_tsum, using the a.e.-measurability from (g)) = Σ_m ∫_{B_m} F dμ (by (g)).
6. (Source side.) A and ⋃_m B_m differ by a μ-null set: (⋃_m B_m) ∖ A = ∅ by (a), and A ∖ ⋃_m B_m ⊆ Z by (d), with μ(Z) = 0 by (e). Hence A =ᵐ[μ] ⋃_m B_m (ae_eq_set) and μ⌞A = μ⌞⋃_m B_m (Measure.restrict_congr_set). The B_m are μ-null-measurable by (c) and pairwise disjoint, hence pairwise a.e.-disjoint, so countable additivity of the set integral gives ∫_{⋃_m B_m} F dμ = Σ_m ∫_{B_m} F dμ for the arbitrary function F ≥ 0 (lintegral_iUnion₀; no measurability of F is required).
7. (Second conclusion.) By steps 5 and 6, ∫_A F dμ = Σ_m ∫_{B_m} F dμ = ∫_Y N_A dν. ∎

## Key steps

1. For y ∉ f(Z), the A-fibre over y is the disjoint union of the B_m-fibres (uses A ⊆ Z ∪ ⋃B_m and B_m ⊆ A).
2. Unordered [0,∞]-sums split over disjoint unions (unionEqSigmaOfDisjoint + ENNReal.tsum_sigma'), so N_A = Σ_m N_{B_m} off f(Z).
3. ν(f(Z)) = 0 gives N_A = Σ_m N_{B_m} ν-a.e.; AEMeasurable.ennreal_tsum + congr gives a.e.-measurability of N_A.
4. lintegral_tsum and the piecewise identities give ∫ N_A dν = Σ_m ∫_{B_m} F dμ.
5. A =ᵐ[μ] ⋃B_m (difference ⊆ Z), restrict_congr_set and lintegral_iUnion₀ give ∫_A F dμ = Σ_m ∫_{B_m} F dμ.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3 json read of nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1/parent-child-handoff.json and nodes/root-lipschitz-pushforward-im-a1/decomposition-v1.json (frozen parent and uncle statements)`
- `python3 scan of dag.json lean_name fields for collisions with lpf_raf_* (none)`
- `contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py to build the exact child scope; lean_contract.validate_lean_statement on all 8 child statements`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean (weighted_area_formula_lipschitzOn_fiberSum, aemeasurable_weightedAreaFiberSum_lipschitzOn, ae_fderivWithin_eq_of_lipschitz_extension, exists_lipschitz_extension_finiteDimensional, areaJacobianWithin)`
- `grep -rn 'def weightedAreaFiberSum|def areaFiber|def areaJacobianAt' simongmt/Poincare/SimonGMT`
- `sed -n 1,140p simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean (NVector, covectorPullback, nVectorPushforward, simpleNVector, nVectorPushforward_simple)`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, HasWeightedApproximateTangentSpaceAt, HasWeightedApproximateTangentSpaceAt.unique)`
- `grep -n '^theorem' simongmt/Poincare/SimonGMT/Chapter02/{Lipschitz,LipschitzMeasurability}.lean (euclideanHausdorffMeasure_image_le_of_lipschitzOn)`
- `grep -n 'def normDet|normDet_sq_eq_det_gram|normDet_comp|ContinuousLinearMap.normDet_sq' mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `grep -rn 'euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_def|hausdorffMeasure_image_le' mathlib/Mathlib`
- `grep -rn 'continuous_compContinuousLinearMapCLM|compContinuousLinearMapCLM' mathlib/Mathlib`
- `grep -rn 'MeasurableSet.image_of_continuousOn_injOn|ContinuousOn.measurable_piecewise|nullMeasurableSet_restrict|countable_cover_nhdsWithin|def gram|basisFun_apply|locallyLipschitzOn' mathlib/Mathlib`
- `sed -n 320,445p book/chapter-03.txt (Simon Ch. 3 §2, 2.1–2.6 printed area-formula proof)`
- `lake env lean Scratch/Probe1.lean Scratch/Probe2.lean Scratch/Probe3.lean Scratch/Probe4.lean (child scope: LinearMap.normDet, Matrix.gram and AreaDomain lemmas absent from the frozen closure but present after importing Poincare.SimonGMT.Chapter02.AreaDomain; Real.sqrt, Matrix.det, EuclideanSpace.single, simpleNVector, nVectorPushforward, euclideanHausdorffMeasure_image_le_of_lipschitzOn, continuous_compContinuousLinearMapCLM available; NormSMulClass ℝ (NVector ..) not synthesized)`
- `lake env lean Scratch/Stmts.lean (all 8 child statements elaborate in the comparator child scope, only sorry warnings)`
- `lake env lean Scratch/Assembly.lean (frozen parent type from 4 uncle stubs + children; Assembly.parent has no sorry)`
- `lake env lean Scratch/K1.lean ... Scratch/K8.lean (K1,K3,K5,K8 fully proved; K2 from K1; K4 from K2,K3; K6 from K3,K5; K7 from K2,K4)`
- `lake env lean Scratch/Axioms.lean (#print axioms of the SimonGMT area-formula lemmas: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/lakefile.toml`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/LipschitzMeasurability.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/raf_scratch/Scratch/Stmts.lean`
- `/tmp/raf_scratch/Scratch/Assembly.lean`
- `/tmp/raf_scratch/Scratch/K1.lean`
- `/tmp/raf_scratch/Scratch/K2.lean`
- `/tmp/raf_scratch/Scratch/K3.lean`
- `/tmp/raf_scratch/Scratch/K4.lean`
- `/tmp/raf_scratch/Scratch/K5.lean`
- `/tmp/raf_scratch/Scratch/K6.lean`
- `/tmp/raf_scratch/Scratch/K7.lean`
- `/tmp/raf_scratch/Scratch/K8.lean`
- `/tmp/raf_scratch/Scratch/Axioms.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c, with SimonGMT pinned at 2b36630. The frozen child scope (import GMT.Ch06.Submission plus the replayed namespace GMT.Ch06 and its opens) provides:
- simpleNVector, nVectorPushforward and nVectorPushforward_simple;
- IsRectifiableTriple, HasWeightedApproximateTangentSpaceAt and its .unique;
- SimonGMT Ch02 Lipschitz, including euclideanHausdorffMeasure_image_le_of_lipschitzOn;
- Mathlib's continuous_compContinuousLinearMapCLM, μHE = volume on Eucl n, Real.sqrt, Matrix.det and EuclideanSpace.single.

It does not provide LinearMap.normDet, Matrix.gram or the SimonGMT Ch02 AreaDomain area formula. Child statements therefore use Gram-determinant Jacobians √det(⟨T e_i, T e_j⟩). The local_lipschitz_area proof imports Poincare.SimonGMT.Chapter02.AreaDomain, which transitively brings in NormDet and changes no frozen type. Through that import it bridges to:
- weighted_area_formula_lipschitzOn_fiberSum and aemeasurable_weightedAreaFiberSum_lipschitzOn;
- ae_fderivWithin_eq_of_lipschitz_extension;
- LinearMap.normDet_sq_eq_det_gram.
All of these use standard axioms only.

No SimonGMT or Mathlib declaration states the rectifiable area formula, its chart decomposition or the n-vector Jacobian identity, so these are the new children.

Scratch Lean checks in the exact comparator scope:
- all 8 statements elaborate and validate;
- the frozen parent follows from the 4 uncles plus children K1, K6, K7, K8;
- every child is proved from its declared siblings (K1, K3, K5, K8 outright).

No lpf_raf_* name collides with dag.json.
