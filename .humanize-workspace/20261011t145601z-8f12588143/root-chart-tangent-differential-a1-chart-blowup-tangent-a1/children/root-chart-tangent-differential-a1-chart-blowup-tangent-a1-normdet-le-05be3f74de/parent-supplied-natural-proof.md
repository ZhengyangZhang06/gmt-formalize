# Parent-supplied natural-language proof

- Parent DAG node: `root.chart_tangent_differential-a1.chart_blowup_tangent-a1`
- Child DAG node: `root.chart_tangent_differential-a1.chart_blowup_tangent-a1.normdet_le_opnorm_pow-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Selected-node proof step 3(b): the bound on the area Jacobian used for domination, obtained from the linear area formula (Simon Ch. 2, (3.1)) and the Lipschitz image estimate for Hausdorff measure.

Notation. Lⁿ := volume on ℝⁿ; Hᵐ := μHE[m] (Euclidean Hausdorff measure); S := B̄₁(0) ⊆ ℝⁿ (closed unit ball); m := finrank ℝ ℝⁿ, so m = n (finrank_euclideanSpace_fin); ‖A‖ is the operator norm and ‖A‖₊ its ℝ≥0-valued version.

1. Linear area formula (Simon (3.1); Mathlib LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume applied to A as a linear map and the set S): Hᵐ(A(S)) = ofReal(normDet A)·Lⁿ(S) in [0, ∞].

2. Lipschitz estimate. A is ‖A‖₊-Lipschitz on ℝⁿ (ContinuousLinearMap.lipschitzWith), in particular on S, so the Hausdorff-measure image estimate (SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn with exponent m) gives Hᵐ(A(S)) ≤ ‖A‖₊ᵐ·Hᵐ(S). Since m = finrank ℝⁿ, Hᵐ = Lⁿ on ℝⁿ (InnerProductSpace.euclideanHausdorffMeasure_eq_volume), so Hᵐ(A(S)) ≤ ‖A‖₊ᵐ·Lⁿ(S).

3. Cancellation. Steps 1 and 2 give ofReal(normDet A)·Lⁿ(S) ≤ ‖A‖₊ᵐ·Lⁿ(S). The closed unit ball satisfies 0 < Lⁿ(S) (Metric.measure_closedBall_pos, radius 1 > 0) and Lⁿ(S) < ∞ (measure_closedBall_lt_top), so the factor Lⁿ(S) cancels (ENNReal.mul_le_mul_iff_left): ofReal(normDet A) ≤ ‖A‖₊ᵐ = ‖A‖₊ⁿ.

4. Back to ℝ. The coercion of ‖A‖₊ to [0, ∞] is ofReal ‖A‖, and ofReal(‖A‖)ⁿ = ofReal(‖A‖ⁿ) (ENNReal.ofReal_pow, ‖A‖ ≥ 0). Hence ofReal(normDet A) ≤ ofReal(‖A‖ⁿ), and since ‖A‖ⁿ ≥ 0, ENNReal.ofReal_le_ofReal_iff yields normDet(A) ≤ ‖A‖ⁿ. (For n = 0 the same argument applies verbatim: ℝ⁰ = {0} = S, L⁰(S) = 1, and both sides equal 1.) ∎

Formalization aid (optional; the numbered proof above is complete on its own). The following Lean script for exactly this frozen statement was compiled by the parent decomposition session against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b36630) in the contract scope shown; `#print axioms` reported only propext, Classical.choice, Quot.sound.

```lean
import GMT.Ch03.Submission
open Filter MeasureTheory Module Set
open scoped CompactlySupported ENNReal NNReal Topology
namespace GMT.Ch03
open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt HasWeightedApproximateTangentSpaceAt PurelyUnrectifiable blowUpMap)

theorem Submission.chartTD_normDet_le_opNorm_pow : (∀ (n N : ℕ) (A : Rn n →L[ℝ] Rn N), A.toLinearMap.normDet ≤ ‖A‖ ^ n) := by
  intro n N A
  have hfin : finrank ℝ (Rn n) = n := finrank_euclideanSpace_fin
  set S : Set (Rn n) := Metric.closedBall 0 1 with hS
  have h1 := LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume A.toLinearMap S
  have h2 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
    (finrank ℝ (Rn n)) (A.lipschitzWith.lipschitzOnWith (s := S))
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h2
  have hcoe : (A.toLinearMap : Rn n → Rn N) '' S = A '' S := rfl
  rw [← hcoe, h1] at h2
  have hpos : 0 < volume S := Metric.measure_closedBall_pos _ _ one_pos
  have hfinite : volume S < ∞ := measure_closedBall_lt_top
  have h3 : ENNReal.ofReal A.toLinearMap.normDet ≤ (‖A‖₊ : ℝ≥0∞) ^ finrank ℝ (Rn n) :=
    (ENNReal.mul_le_mul_iff_left hpos.ne' hfinite.ne).mp h2
  rw [hfin] at h3
  have h4 : ENNReal.ofReal A.toLinearMap.normDet ≤ ENNReal.ofReal (‖A‖ ^ n) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _)]
    simpa [ofReal_norm, enorm_eq_nnnorm] using h3
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h4

end GMT.Ch03
```

## Key steps

1. Linear area formula on the closed unit ball S: Hⁿ(A(S)) = normDet(A)·Lⁿ(S).
2. A is ‖A‖-Lipschitz, so Hⁿ(A(S)) ≤ ‖A‖ⁿ·Hⁿ(S) = ‖A‖ⁿ·Lⁿ(S) (SimonGMT Lipschitz image bound, Hⁿ = Lⁿ on ℝⁿ).
3. Cancel 0 < Lⁿ(S) < ∞ and pass from [0, ∞] back to ℝ.

## Reference use

### local-project

Queries:
- `cat local-references/d498d77b74ea2063/manifest.json (project d09bc8a, Mathlib 25730c7c)`
- `rg -n "blowUpMap|HasApproximateTangentSpaceAt" project/GMT/Ch03/Contract.lean`
- `rg -n "chartTD_|approx_tangent" project/GMT (no match)`
- `rg -n "theorem normDet_nonneg|theorem _root_.ContinuousLinearMap.normDet_sq|theorem euclideanHausdorffMeasure_image_eq_normDet_mul_volume|theorem normDet_eq_prod_singularValues|theorem normDet_of_subsingleton" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `rg -n "continuous_normDet|normDet_le|normDet.*opNorm" mathlib/Mathlib (no continuity lemma or operator-norm bound for normDet in Mathlib; only normDet_smul)`
- `rg -n "setIntegral.*image.*normDet|integral_image_eq_integral_abs_det_fderiv_smul" mathlib/Mathlib (only the equidimensional |det| change of variables in MeasureTheory/Function/Jacobian.lean)`
- `rg -n "theorem norm_fderiv_le_of_lipschitzOn|theorem HasFDerivAt.lim" mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `rg -n "theorem measurable_fderiv" mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `rg -n "theorem ContinuousLinearMap.continuous_det" mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `rg -n "euclideanHausdorffMeasure_eq_volume" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "theorem MeasurableSet.image_of_continuousOn_injOn" mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `rg -n "theorem integral_withDensity_eq_integral_smul|theorem integral_comp_smul|theorem tendsto_integral_filter_of_dominated_convergence" mathlib/Mathlib/MeasureTheory`
- `grep -n "def blowUpMap|def HasApproximateTangentSpaceAt|theorem hasApproximateTangentSpaceAt_submodule" simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (pinned package)`
- `grep -rn "normDet" simongmt/Poincare/SimonGMT | grep theorem (found Chapter02.continuous_normDet in AreaApproximation.lean)`
- `grep -rn "normDet[^\n]*≤|areaJacobianAt[^\n]*≤|≤[^\n]*normDet" simongmt/Poincare/SimonGMT (no operator-norm bound for normDet)`
- `grep -rn "areaJacobianAt" simongmt/Poincare/SimonGMT | grep theorem (found areaJacobianAt_eq_normDet and measurable_areaJacobianAt)`
- `grep -n "theorem" simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean (found integral_area_formula_of_injective_derivative)`
- `grep -rn "theorem.*blowUpMap|theorem.*HasApproximateTangentSpaceAt|Remark 1" simongmt/Poincare/SimonGMT/Chapter03 (no C¹-chart Remark 1.5(2) lemma)`
- `grep -n "theorem weighted_area_formula_lipschitzOn_fiberSum|def weightedAreaFiberSum|def areaFiber|def areaJacobianWithin" simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `grep -n "theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn" simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `lake env lean GMT/Scratch/CBTLibVis*.lean (SimonGMT continuous_normDet / integral_area_formula_of_injective_derivative / measurable_areaJacobianAt: not visible after import GMT.Ch03.Submission alone; visible after adding import Poincare.SimonGMT.Chapter02.AreaDomain)`
- `lake env lean GMT/Scratch/CBTComparatorScope4.lean (four frozen statements in the replayed comparator scope)`
- `lake env lean GMT/Scratch/CBTFullCheck4.lean and GMT/Scratch/CBTNoAreaDomain4.lean (all child proofs, the assembly, and #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/SingularValues.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`

Snapshot manifest: project d09bc8a (Contract.lean byte-identical to the workspace) and Mathlib 25730c7c; SimonGMT is the pinned simongmt package (2b36630). Used from Mathlib: LinearMap.normDet with normDet_nonneg, ContinuousLinearMap.normDet_sq and euclideanHausdorffMeasure_image_eq_normDet_mul_volume; norm_fderiv_le_of_lipschitzOn, HasFDerivAt.lim, measurable_fderiv, ContinuousLinearMap.continuous_det, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, MeasurableSet.image_of_continuousOn_injOn (Lusin-Souslin), integral_withDensity_eq_integral_smul, Measure.integral_comp_smul and tendsto_integral_filter_of_dominated_convergence. Used from SimonGMT: blowUpMap and HasApproximateTangentSpaceAt (Def. 1.4); weighted_area_formula_lipschitzOn_fiberSum and areaJacobianWithin (AreaDomain); weightedAreaFiberSum and areaFiber (AreaMultiplicity, reached through the same import); continuous_normDet (AreaApproximation, reachable through the AreaDomain import); and euclideanHausdorffMeasure_image_le_of_lipschitzOn, which is visible from GMT.Ch03.Submission. Because SimonGMT already proves continuous_normDet, normDet continuity is cited rather than made a child. SimonGMT integral_area_formula_of_injective_derivative (WeightedArea) covers injective maps that are differentiable with injective derivative. The chart_area_integral child keeps the supplied step 4's Lipschitz-domain version, whose hypotheses are incomparable with the library lemma's. No match in Mathlib or SimonGMT for an operator-norm bound on normDet, for the blow-up limit of chart integrals, or for Remark 1.5(2) on C¹ charts; SimonGMT has only the flat-plane case, hasApproximateTangentSpaceAt_submodule. No existing chartTD_* declarations exist in the project. The four statements elaborate in the comparator scope replayed by the verifier's contract_scope, and their proofs compile with standard axioms only.
