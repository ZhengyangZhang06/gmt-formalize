# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_structure-a1.piece_density_blowup-a1`
- Child DAG node: `root.tangent_structure-a1.piece_density_blowup-a1.linear_range_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof, step 6, in its stated alternative form 'from (R2c): Hⁿ⌞T is the image under A of normDet(A)·Lⁿ', with the area factor normDet(A) abstracted to any j ≥ 0 satisfying the image identity. No errata apply.

Conventions. n, ℓ ∈ ℕ; E := Ambient n ℓ = EuclideanSpace ℝ (Fin (n+ℓ)); ℝⁿ := EuclideanSpace ℝ (Fin n) with Lebesgue measure Lⁿ := volume; Hⁿ := μHE[n] (on E, and also on ℝⁿ, where μHE[n] = volume by Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume n); finrank ℝ ℝⁿ = n (finrank_euclideanSpace_fin); B_ρ(z) := closedBall z ρ; ω_n := omega n = (Lⁿ(ball 0 1)).toReal, and Lⁿ(ball 0 1) = ofReal(ω_n) because Lⁿ(ball 0 1) < ∞ (ENNReal.ofReal_toReal). Hypotheses: A: ℝⁿ → E is a continuous linear map (injectivity is not needed); j ≥ 0; (H) Hⁿ(A(S)) = ofReal(j)·Lⁿ(S) for every S ⊆ ℝⁿ; f ∈ C_c(E, ℝ). Write range A = A(ℝⁿ) (as a set, the carrier of LinearMap.range A).

Proof.
1. Measure identity. We show Hⁿ⌞(range A) = A_#(ofReal(j)·Lⁿ) as measures on E. A is continuous, hence Borel measurable. Let T ⊆ E be Borel. Then (Hⁿ⌞range A)(T) = Hⁿ(T ∩ range A) (Measure.restrict_apply). Elementarily T ∩ range A = A(A⁻¹(T)): if y = A(u) ∈ T then u ∈ A⁻¹(T); conversely A(A⁻¹(T)) ⊆ T ∩ range A. By (H) with S := A⁻¹(T), Hⁿ(A(A⁻¹(T))) = ofReal(j)·Lⁿ(A⁻¹(T)) = (ofReal(j)·Lⁿ)(A⁻¹(T)) = (A_#(ofReal(j)·Lⁿ))(T) (Measure.smul_apply, Measure.map_apply). As this holds for all Borel T, the measures are equal (Measure.ext).
2. Integral. By step 1, ∫_{range A} f dHⁿ = ∫ f d(A_#(ofReal(j)·Lⁿ)). Since A is measurable and f is continuous (hence a.e. strongly measurable), MeasureTheory.integral_map gives ∫ f d(A_#(ofReal(j)·Lⁿ)) = ∫ f(A(u)) d(ofReal(j)·Lⁿ)(u), and integral_smul_measure gives this equals (ofReal(j)).toReal·∫ f(A(u)) dLⁿ(u). Since j ≥ 0, (ofReal(j)).toReal = j. Hence ∫_{range A} f dHⁿ = j·∫_{ℝⁿ} f(A(u)) dLⁿ(u). These are unconditional identities of Bochner integrals (equalities of measures), so no integrability assumption is needed. ∎

## Key steps

1. T ∩ range A = A(A⁻¹T) for every T ⊆ E
2. Hence Hⁿ⌞range A = A_#(ofReal(j)·Lⁿ) by the area-factor hypothesis applied to S = A⁻¹T and Measure.ext
3. integral_map and integral_smul_measure give ∫_{range A} f dHⁿ = j·∫ f(Au) du

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; sha256sum <snapshot>/project/GMT/Ch04/Contract.lean GMT/Ch04/Contract.lean`
- `sed -n 1,30p .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (frozen import closure: only Chapter02.Lipschitz)`
- `grep -rn 'theorem weighted_area_formula_lipschitz_injOn|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn|theorem continuous_normDet|theorem measurable_areaJacobianAt|def areaJacobianAt' .lake/packages/simongmt/Poincare/SimonGMT/`
- `grep -n 'theorem|def ' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `rg -n 'theorem euclideanHausdorffMeasure_eq_volume|theorem volume_closedBall|theorem addHaar_closedBall\b|theorem finrank_euclideanSpace_fin|theorem integral_comp_smul\b|exists_antilipschitzWith|theorem integral_map\b|theorem integral_smul_measure|theorem integral_withDensity_eq_integral_toReal_smul' <snapshot>/mathlib/Mathlib`
- `rg -n 'integral_mul_left_eq_self|setIntegral_comp_smul|addHaar_preimage_smul|addHaar_smul' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -n 'uniformContinuous' <snapshot>/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean`
- `rg -n 'theorem Integrable.comp_smul\b|theorem Integrable.comp_mul_left\b|theorem hasFDerivAt_iff_isLittleO_nhds_zero|bounded_above_of_compact_support|exists_bound_of_continuousOn|theorem integral_indicator_one|theorem norm_integral_le_of_norm_le\b|theorem integrable_indicator_iff|ContinuousOn.integrableOn_compact' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem measure_sdiff |alias measure_diff :=' mathlib/Mathlib/MeasureTheory`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/pdb-decomp/olean/GMT/Ch04/Submission.olean`
- `python3 gen.py (gmt-compare.child_modules contract mode) then lean /tmp/pdb-decomp/final/challenges/Challenge_*.lean`
- `lean /tmp/pdb-decomp/final/F1_frozen.lean (parent from 5 sorry'd children, frozen imports only)`
- `lean /tmp/pdb-decomp/final/F2_full.lean (all 5 children + parent fully proved; #print axioms)`
- `lean P1.lean / P2.lean with set_option pp.all true; cmp of #check outputs across import sets`
- `python3 lean_contract.validate_lean_statement on each child type; dag.json lean_name collision check`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1/decomposition-v1.json`
- `/tmp/pdb-decomp/final/F1_frozen.lean`
- `/tmp/pdb-decomp/final/F2_full.lean`

Contract and pins:
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean (single sha256).
- Submission.lean is the frozen copy. The manifest pins the project at ff75f52 and Mathlib at 25730c7c; SimonGMT is at 2b36630.

Frozen statement scope:
- Chapter03.Rectifiable imports only Chapter02.Lipschitz, so LinearMap.normDet and Chapter02.areaJacobianAt cannot appear in child types.
- The children therefore carry the Jacobian as an existential J with the area-factor identity Hⁿ(DF(v)(S)) = ofReal(J v)·Lⁿ(S).

Cited library results (all exist with the stated meaning):
- SimonGMT Chapter02: euclideanHausdorffMeasure_image_le_of_lipschitzOn (Lipschitz.lean:216), weighted_area_formula_lipschitz_injOn and injective_area_formula_lipschitz (AreaLipschitz.lean:101 ff.), continuous_normDet and measurable_areaJacobianAt (AreaApproximation.lean:28, 44), areaJacobianAt_eq_normDet (Area.lean).
- Mathlib NormDet and volume: LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume and normDet_nonneg; EuclideanSpace.euclideanHausdorffMeasure_eq_volume; Measure.addHaar_closedBall; Measure.addHaar_preimage_smul; Measure.integral_comp_smul; integral_add_left_eq_self (the to_additive form of integral_mul_left_eq_self).
- Mathlib integration: integral_map; integral_smul_measure; integral_withDensity_eq_integral_toReal_smul; Integrable.comp_smul; integrable_indicator_iff; ContinuousOn.integrableOn_compact; norm_integral_le_of_norm_le.
- Mathlib analysis: LinearMap.exists_antilipschitzWith; CompactlySupportedContinuousMapClass.uniformContinuous; hasFDerivAt_iff_isLittleO_nhds_zero; measure_sdiff (measure_diff is a deprecated alias).

Lean checks:
- All five child types are valid one-line statements and compile as comparator challenge files in the frozen scope.
- The parent's exact frozen type is proved from them (F1).
- All five children and the parent are fully proved with the extra imports (F2). Axioms are only propext, Classical.choice and Quot.sound.
- The pp.all types are identical across the two import sets.
- No lean_name collides with any of the 79 DAG nodes.
