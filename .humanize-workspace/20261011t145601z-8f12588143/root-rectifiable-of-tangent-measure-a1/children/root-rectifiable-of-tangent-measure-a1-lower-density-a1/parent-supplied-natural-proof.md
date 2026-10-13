# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiable_of_tangent_measure-a1`
- Child DAG node: `root.rectifiable_of_tangent_measure-a1.lower_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the lower half of Step 3 (5′) of the parent proof, i.e. Simon, Remark 1.5(3) (chapter-03.txt lines 91–97: test functions f ∈ C_c with values in [0, 1] comparing ∫ f∘η_{x,ρ} with the mass of a ball), written with multiplicity θ and for every n ≥ 0. Only the lower bound for μ(B_ρ(x)) is needed by the parent, so no two-sided density limit is proved.

Notation. |·| is the Euclidean norm, B_ρ(x) the open and B̄_ρ(x) the closed ball, and ν := Hⁿ⌞P = μHE[n].restrict P, so that ∫_P f dHⁿ = ∫ f dν.

1. Test function. Define g(w) := max(0, 1 − |w|) for w ∈ ℝ^N. Then g is continuous, 0 ≤ g ≤ 1, g(w) = 0 whenever |w| ≥ 1, and g(w) > 0 whenever |w| < 1. Since g vanishes outside the compact set B̄_1(0), g ∈ C_c(ℝ^N, ℝ).

2. The plane measure. Because finrank P = n, the measure ν is regular, in particular finite on compact sets, and its support is exactly P (SimonGMT `Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule` and `support_euclideanHausdorffMeasure_restrict_submodule`; mathematically: the isometric inclusion P ↪ ℝ^N carries μHE[n] of the n-dimensional inner product space P, which is its Lebesgue (Haar) measure, onto ν). Consequently g, being continuous with compact support, is ν-integrable.

3. ∫_P g dHⁿ > 0. Since 0 ∈ P = spt ν and B_1(0) is a neighbourhood of 0, ν(B_1(0)) > 0. Moreover g ≥ 0 and {w : g(w) ≠ 0} ⊇ B_1(0). A nonnegative integrable function has positive integral as soon as its support has positive measure (Mathlib `integral_pos_iff_support_of_nonneg`), so ∫_P g dHⁿ = ∫ g dν > 0.

4. Choice of c. Put L := θ ∫_P g dHⁿ; then L > 0 because θ > 0. Put c := L/2 > 0. By the hypothesis applied to f = g, (ρⁿ)⁻¹ I(ρ) → L as ρ ↓ 0, where I(ρ) := ∫ g(η_{x,ρ}(y)) dμ(y). Since L/2 < L, there is ρ₀ > 0 such that (ρⁿ)⁻¹ I(ρ) > L/2 for every ρ ∈ (0, ρ₀); multiplying by ρⁿ > 0 gives c ρⁿ < I(ρ) for ρ ∈ (0, ρ₀).

5. Comparison with the ball. Fix ρ ∈ (0, ρ₀). The closed ball B̄_ρ(x) is compact, so μ(B_ρ(x)) ≤ μ(B̄_ρ(x)) < ∞. If y ∉ B_ρ(x), then |η_{x,ρ}(y)| = |y − x|/ρ ≥ 1 and hence g(η_{x,ρ}(y)) = 0; if y ∈ B_ρ(x), then g(η_{x,ρ}(y)) ≤ 1. Hence 0 ≤ g∘η_{x,ρ} ≤ 1_{B_ρ(x)} pointwise. The indicator 1_{B_ρ(x)} is μ-integrable (finite measure), so monotonicity of the integral for a nonnegative minorant (Mathlib `integral_mono_of_nonneg`) gives I(ρ) ≤ ∫ 1_{B_ρ(x)} dμ = μ(B_ρ(x)) (the latter as a finite real number; Mathlib `integral_indicator_one`).

6. Conclusion. For every ρ ∈ (0, ρ₀) we have c ρⁿ < I(ρ) ≤ μ(B_ρ(x)) < ∞, hence ENNReal.ofReal(c ρⁿ) ≤ μ(B_ρ(x)). Thus c > 0 and the inequality holds eventually in 𝓝[>] 0. (For n = 0 nothing changes: ρ⁰ = 1, P = {0} and ν = H⁰⌞{0} is the unit point mass at 0.) ∎

Formalization appendix (verified, supplementary to the proof above). The following Lean proof of exactly this frozen statement compiled without errors or sorry against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b366308), placed after `import GMT.Ch03.Submission` inside `namespace GMT.Ch03` with the contract's opens (`open Filter MeasureTheory Module Set`, `open scoped CompactlySupported ENNReal NNReal Topology`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt HasWeightedApproximateTangentSpaceAt PurelyUnrectifiable blowUpMap)`); `#print axioms` reports only [propext, Classical.choice, Quot.sound]. It follows the numbered steps above.

```lean
theorem Submission.tangentMeasure_eventually_lower_density : (∀ (N n : ℕ) (μ : Measure (Rn N)) (x : Rn N) (P : Submodule ℝ (Rn N)) (θ : ℝ), (∀ K : Set (Rn N), IsCompact K → μ K < ∞) → 0 < θ → HasApproxTangentPlaneWithMultiplicity n μ x P θ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (c * ρ ^ n) ≤ μ (Metric.ball x ρ)) := by
  intro N n μ x P θ hfin hθ hP
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hfin⟩
  obtain ⟨hdim, hlim⟩ := hP
  let g0 : Rn N → ℝ := fun w => max 0 (1 - ‖w‖)
  have g0_cont : Continuous g0 := continuous_const.max (continuous_const.sub continuous_norm)
  have g0_supp : HasCompactSupport g0 := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Rn N) 1)
    intro w hw
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hw
    exact max_eq_left (by linarith)
  let g : C_c(Rn N, ℝ) := ⟨⟨g0, g0_cont⟩, g0_supp⟩
  have hg : ∀ w, g w = g0 w := fun w => rfl
  have g0_nonneg : ∀ w, 0 ≤ g0 w := fun w => le_max_left _ _
  have g0_le_one : ∀ w, g0 w ≤ 1 := fun w => max_le zero_le_one (by linarith [norm_nonneg w])
  haveI hreg := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
    (E := Rn N) hdim
  have hint_pos : 0 < ∫ y in (P : Set (Rn N)), g y ∂μHE[n] := by
    have hgi : Integrable (fun y => g y) ((μHE[n] : Measure (Rn N)).restrict (P : Set (Rn N))) :=
      g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
    rw [integral_pos_iff_support_of_nonneg (f := fun y => g y) (fun y => g0_nonneg y) hgi]
    have hsub : Metric.ball (0 : Rn N) 1 ⊆ Function.support (fun y => g y) := by
      intro w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      simp only [Function.mem_support, hg, g0]
      apply ne_of_gt
      exact lt_max_of_lt_right (by linarith)
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    have h0 : (0 : Rn N) ∈ ((μHE[n] : Measure (Rn N)).restrict (P : Set (Rn N))).support := by
      rw [Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hdim]
      exact P.zero_mem
    exact (Measure.mem_support_iff_forall _).mp h0 _ (Metric.ball_mem_nhds 0 one_pos)
  set L := θ * ∫ y in (P : Set (Rn N)), g y ∂μHE[n] with hLdef
  have hL : 0 < L := mul_pos hθ hint_pos
  refine ⟨L / 2, half_pos hL, ?_⟩
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), L / 2 < (r ^ n)⁻¹ * ∫ y, g (blowUpMap x r y) ∂μ :=
    (hlim g).eventually (lt_mem_nhds (half_lt_self hL))
  filter_upwards [hev, self_mem_nhdsWithin] with ρ hρ hρpos
  have hρpos' : (0 : ℝ) < ρ := hρpos
  have hρn : 0 < ρ ^ n := pow_pos hρpos' n
  have h1 : L / 2 * ρ ^ n < ∫ y, g (blowUpMap x ρ y) ∂μ := by
    have := mul_lt_mul_of_pos_left hρ hρn
    rwa [← mul_assoc, mul_inv_cancel₀ hρn.ne', one_mul, mul_comm] at this
  have hball : μ (Metric.ball x ρ) < ∞ :=
    (measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall x ρ).measure_lt_top
  have hpt : ∀ y, g (blowUpMap x ρ y) ≤ (Metric.ball x ρ).indicator 1 y := by
    intro y
    by_cases hy : y ∈ Metric.ball x ρ
    · rw [Set.indicator_of_mem hy]; exact g0_le_one _
    · rw [Set.indicator_of_notMem hy]
      rw [Metric.mem_ball, dist_eq_norm, not_lt] at hy
      have h1' : 1 ≤ ‖blowUpMap x ρ y‖ := by
        simp only [blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρpos']
        rw [le_inv_mul_iff₀ hρpos']; linarith
      show g0 _ ≤ 0
      exact le_of_eq (max_eq_left (by linarith))
  have h2 : ∫ y, g (blowUpMap x ρ y) ∂μ ≤ μ.real (Metric.ball x ρ) := by
    rw [← integral_indicator_one measurableSet_ball]
    apply integral_mono_of_nonneg
    · exact Eventually.of_forall fun y => g0_nonneg _
    · exact (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_const hball.ne)
    · exact Eventually.of_forall hpt
  calc ENNReal.ofReal (L / 2 * ρ ^ n) ≤ ENNReal.ofReal (μ.real (Metric.ball x ρ)) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = μ (Metric.ball x ρ) := ENNReal.ofReal_toReal hball.ne
```

## Key steps

1. Test function g(w) = max(0, 1 − |w|) ∈ C_c(ℝ^N, ℝ) with 0 ≤ g ≤ 1, g = 0 off B_1(0) and g > 0 on B_1(0).
2. Since finrank P = n, Hⁿ⌞P is finite on compacts with support P, so ∫_P g dHⁿ > 0 and L := θ∫_P g dHⁿ > 0.
3. The tangent limit with f = g gives ∫ g∘η_{x,ρ} dμ > (L/2)ρⁿ for all small ρ > 0.
4. Pointwise 0 ≤ g∘η_{x,ρ} ≤ 1_{B_ρ(x)} and local finiteness give ∫ g∘η_{x,ρ} dμ ≤ μ(B_ρ(x)); conclude with c = L/2.

## Reference use

### local-project

Queries:
- `cat local-references/d498d77b74ea2063/manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); diff project/GMT/Ch03/Contract.lean against the workspace contract (identical)`
- `grep -n theorem/def simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, countablyRectifiable_iUnion, countablyRectifiable_range, blowUpMap, regular_euclideanHausdorffMeasure_restrict_submodule, support_euclideanHausdorffMeasure_restrict_submodule)`
- `grep -n theorem simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean (locallyFinite_planeMeasure, planeMeasure_unit_closedBall, tangentDensityCutoff, one_le_density_of_approximateTangent)`
- `grep -rn "μHE\[" mathlib/Mathlib; read mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_def, isAddHaarMeasure_euclideanHausdorffMeasure, Isometry.map_euclideanHausdorffMeasure, euclideanHausdorffMeasure_smul₀, InnerProductSpace.euclideanHausdorffMeasure_eq_volume)`
- `grep -rn "LipschitzOnWith.extend_real|LipschitzOnWith.extend_pi|extend_finite_dimension" mathlib/Mathlib`
- `grep -rn "IsSigmaCompact.measurableSet|isSigmaCompact_range" mathlib/Mathlib (no IsSigmaCompact.measurableSet; isSigmaCompact_range in Topology/Compactness/SigmaCompact.lean)`
- `grep -rn "countable_meas_pos" mathlib/Mathlib (Measure.countable_meas_pos_of_disjoint_iUnion in Typeclasses/SFinite.lean); grep sigmaFinite_of_locallyFinite`
- `grep -n "starProjection_norm_le|norm_starProjection_apply_le|starProjection_eq_self_iff|orthogonalProjectionOnto|starProjection_apply" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `grep IsSeparable.exists_countable_dense_subset, IsSeparable.of_separableSpace, exists_countable_dense, Dense.exists_dist_lt, exists_linearIndependent_of_le_finrank, finrank_span_eq_card, stdOrthonormalBasis/reindex, nhdsGT_basis, Antitone.measure_iInter, tendsto_measure_iInter_atTop, nullSingletonClass_hausdorff, mem_support_iff_forall, infDist_lt_iff, continuous_infDist_pt, integral_pos_iff_support_of_nonneg, integral_mono_of_nonneg, integral_indicator_one, integrableOn_const, Continuous.integrable_of_hasCompactSupport, ofReal_le_ofReal_iff'`
- `sed -n 60,280p book/chapter-03.txt (Remark 1.5(3) lines 91-105; proof of 1.6 '⇐' lines 145-274)`
- `python: contract_scope() and validate_lean_statement() from verifier/gmt-compare.py and verifier/lean_contract.py applied to every proposed lean_statement`
- `grep -rl for each proposed lean_name over .humanize, GMT and simongmt/Poincare (no match); dag.json lean_name listing`
- `lake env lean /tmp/rtm_scratch/Challenge.lean, /tmp/rtm_scratch/Assembly.lean, /tmp/rtm_scratch/ChildrenCDEF.lean, /tmp/rtm_scratch/ChildrenAB.lean, /tmp/rtm_scratch/Full.lean (with #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Dimension/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Order/LeftRightNhds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-rectifiable-of-tangent-measure-a1/parent-child-handoff.json`
- `/tmp/rtm_scratch/Challenge.lean`
- `/tmp/rtm_scratch/Assembly.lean`
- `/tmp/rtm_scratch/Full.lean`

Snapshot: project d09bc8a (Contract.lean identical to the workspace copy), Mathlib 25730c7c, pinned simongmt. Found and used: SimonGMT Chapter03 CountablyRectifiable, countablyRectifiable_iUnion, countablyRectifiable_range, blowUpMap, regular_euclideanHausdorffMeasure_restrict_submodule and support_euclideanHausdorffMeasure_restrict_submodule (plane measure Hⁿ⌞P is regular with support P when finrank P = n); Mathlib LipschitzOnWith.extend_finite_dimension (Lipschitz extension into finite-dimensional targets, replacing Simon Ch. 2 Thm 1.2), Measure.countable_meas_pos_of_disjoint_iUnion with sigmaFinite_of_locallyFinite (countable atoms), isSigmaCompact_range (Borel measurability of Lipschitz images), Measure.nullSingletonClass_hausdorff (no atoms for n ≥ 1), Submodule.norm_starProjection_apply_le / starProjection_eq_self_iff, IsSeparable.exists_countable_dense_subset, exists_linearIndependent_of_le_finrank, Antitone.measure_iInter, tendsto_measure_iInter_atTop, infDist_lt_iff, integral_pos_iff_support_of_nonneg, integral_mono_of_nonneg. No match: Mathlib has no IsSigmaCompact.measurableSet (σ-compact sets are handled by unfolding into a countable union of compacts), no countable rectifiability, and no Kirszbraun theorem (not needed: componentwise/finite-dimensional extension suffices); SimonGMT has no approximate-tangent-measure (HasApproxTangentPlaneWithMultiplicity) results. The six child propositions pass the verifier's statement validator and elaborate in the comparator's replayed contract scope; with the children as sorry stubs the parent glue compiles; and complete proofs of all six children plus the parent compile sorry-free using only propext, Classical.choice and Quot.sound. No proposed name is used elsewhere in the active DAG or the libraries.
