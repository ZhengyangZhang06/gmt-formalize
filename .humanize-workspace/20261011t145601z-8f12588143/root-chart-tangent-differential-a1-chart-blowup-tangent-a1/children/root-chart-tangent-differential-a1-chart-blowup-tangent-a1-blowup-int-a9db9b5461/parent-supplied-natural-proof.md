# Parent-supplied natural-language proof

- Parent DAG node: `root.chart_tangent_differential-a1.chart_blowup_tangent-a1`
- Child DAG node: `root.chart_tangent_differential-a1.chart_blowup_tangent-a1.blowup_integral_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Selected-node proof steps 5-9 (with the facts of steps 1 and 3): the blow-up of the pulled-back chart integral and dominated convergence (Simon Ch. 3, proof of Theorem 1.6 '⇒' and Remark 1.5(2), chapter-03.txt lines 87-90 and 113-143, for a single bi-Lipschitz C¹ chart). Uses the siblings fderiv_bounds (Submission.chartTD_chart_fderiv_bounds) and normdet_le_opnorm_pow (Submission.chartTD_normDet_le_opNorm_pow). No extra import is needed.

Notation. Lⁿ := volume on ℝⁿ; Dψ(v) := fderiv ℝ ψ v; L := Dψ(u); Jψ(v) := normDet(Dψ(v)); J := Jψ(u); for r > 0, η_r(z) := blowUpMap (ψ u) r z = r⁻¹•(z − ψ(u)).

1. Facts about ψ and Jψ. (a) Jψ ≥ 0 (LinearMap.normDet_nonneg). (b) The map A ↦ normDet(A) on ℝⁿ →L ℝᴺ is continuous. Indeed normDet(A) ≥ 0 and normDet(A)² = det(A* ∘L A) (ContinuousLinearMap.normDet_sq; over ℝ the scalar cast is the identity), so normDet(A) = √det(A* ∘L A) (Real.sqrt_sq). That is a composition of continuous maps: A ↦ A* (the adjoint is a linear isometric equivalence), A ↦ A* ∘L A (Continuous.clm_comp), det on ℝⁿ →L ℝⁿ (ContinuousLinearMap.continuous_det) and √ (Real.continuous_sqrt). (This is also SimonGMT Chapter02.continuous_normDet, visible after `import Poincare.SimonGMT.Chapter02.AreaDomain`.) Since v ↦ Dψ(v) is measurable (measurable_fderiv), Jψ = normDet ∘ Dψ is Borel on ℝⁿ. (c) For v ∈ B, Jψ(v) ≤ ‖Dψ(v)‖ⁿ ≤ Kⁿ, by the sibling normdet_le_opnorm_pow and the bound ‖Dψ(v)‖ ≤ K from the sibling fderiv_bounds (pow_le_pow_left₀, norms being ≥ 0). (d) Jψ is continuous at u: v ↦ Dψ(v) is continuous on the open set B (ContDiffOn.continuousOn_fderiv_of_isOpen with 1 ≤ 1), hence continuous at u ∈ B, and normDet is continuous by 1(b). (e) ψ is continuous on B (Lipschitz on B), and ψ has Fréchet derivative L at u (ψ is C¹ on the open set B ∋ u, so ContDiffOn.differentiableOn and DifferentiableOn.differentiableAt apply).

2. Constants from f. f is continuous with compact support. Choose M with |f(z)| ≤ M for all z ∈ ℝᴺ (HasCompactSupport.exists_bound_of_continuous); then M ≥ |f(0)| ≥ 0. The compact set tsupport f is bounded, so tsupport f ⊆ B̄_R(0) for some R (IsCompact.isBounded, Bornology.IsBounded.subset_closedBall); hence f(z) ≠ 0 implies |z| ≤ R (subset_tsupport).

3. Substitution. Fix r > 0 and define h_r(v) := f(η_r(ψ(v)))·Jψ(v) and G_r(y) := (1_B·h_r)(u + r•y), where 1_B·h_r denotes the indicator B.indicator h_r. Since B is Borel, ∫_B h_r = ∫_{ℝⁿ} 1_B·h_r (integral_indicator). By the scaling formula for Haar measure (Measure.integral_comp_smul, applied to y ↦ (1_B·h_r)(u + y) and the scalar r), ∫ (1_B·h_r)(u + r•y) dy = |(r^{finrank ℝⁿ})⁻¹|·∫ (1_B·h_r)(u + y) dy, and by translation invariance (integral_add_left_eq_self) ∫ (1_B·h_r)(u + y) dy = ∫ (1_B·h_r)(y) dy. Since finrank ℝⁿ = n and r > 0, |(rⁿ)⁻¹| = (rⁿ)⁻¹. Hence, for every r > 0,
   (rⁿ)⁻¹·∫_B f(η_r(ψ(v)))·Jψ(v) dv = ∫_{ℝⁿ} G_r(y) dy.
(These are identities of Bochner integrals valid without integrability assumptions.)

4. Measurability of G_r (r > 0). Let S_r := {y : u + r•y ∈ B}, the preimage of the open set B under the continuous map y ↦ u + r•y; S_r is open. By the definition of the indicator, G_r = 1_{S_r}·(y ↦ h_r(u + r•y)). On S_r, y ↦ f(η_r(ψ(u + r•y))) is continuous (f and η_r are continuous, ψ is continuous on B, and u + r•y ∈ B for y ∈ S_r), hence a.e.-strongly measurable for Lⁿ⌞S_r (ContinuousOn.aestronglyMeasurable); y ↦ Jψ(u + r•y) is Borel by 1(b). Their product is a.e.-strongly measurable for Lⁿ⌞S_r, and therefore G_r is a.e.-strongly measurable for Lⁿ (aestronglyMeasurable_indicator_iff, S_r Borel).

5. Domination. Let β(y) := M·Kⁿ·1_{B̄_{R/c}(0)}(y) ≥ 0. β is Lⁿ-integrable: it is a constant on the closed ball B̄_{R/c}(0), which has finite measure (integrableOn_const with measure_closedBall_lt_top, then IntegrableOn.integrable_indicator). Claim: |G_r(y)| ≤ β(y) for every r > 0 and every y. If u + r•y ∉ B, then G_r(y) = 0 ≤ β(y). If u + r•y ∈ B and f(η_r(ψ(u + r•y))) = 0, then again G_r(y) = 0. Otherwise u + r•y ∈ B and f(η_r(ψ(u + r•y))) ≠ 0, so by step 2, |η_r(ψ(u + r•y))| = r⁻¹·|ψ(u + r•y) − ψ(u)| ≤ R, i.e. |ψ(u + r•y) − ψ(u)| ≤ r·R. The lower bound applied to u + r•y, u ∈ B gives c·r·|y| = c·|(u + r•y) − u| ≤ |ψ(u + r•y) − ψ(u)| ≤ r·R; dividing by r·c > 0 yields |y| ≤ R/c, i.e. y ∈ B̄_{R/c}(0), so β(y) = M·Kⁿ. In this case |G_r(y)| = |f(η_r(ψ(u + r•y)))|·Jψ(u + r•y) ≤ M·Kⁿ = β(y), by step 2 and 1(a), 1(c).

6. Pointwise limit. Fix y ∈ ℝⁿ and let r → 0⁺ (filter 𝓝[>]0). (i) u + r•y → u, and B ∈ 𝓝 u, so eventually u + r•y ∈ B and then G_r(y) = f(η_r(ψ(u + r•y)))·Jψ(u + r•y). (ii) η_r(ψ(u + r•y)) = r⁻¹•(ψ(u + r•y) − ψ(u)) → L y: apply HasFDerivAt.lim to the derivative L of ψ at u (1(e)) with direction y and scalars c(r) = r⁻¹, using |r⁻¹| = r⁻¹ → +∞ as r → 0⁺ (tendsto_inv_nhdsGT_zero) and (c(r))⁻¹ = r. (For y = 0 both sides are 0.) (iii) By continuity of f, f(η_r(ψ(u + r•y))) → f(L y). (iv) By 1(d) and (i), Jψ(u + r•y) → Jψ(u) = J. Hence G_r(y) → f(L y)·J (the limit of the product, transferred to G_r by the eventual equality in (i)).

7. Dominated convergence. The filter 𝓝[>]0 is countably generated. By steps 4, 5 and 6 (measurability and domination for all r > 0, i.e. eventually in 𝓝[>]0; pointwise convergence for every y), tendsto_integral_filter_of_dominated_convergence gives ∫ G_r(y) dy → ∫ f(L y)·J dy as r → 0⁺. Moreover ∫ f(L y)·J dy = (∫ f(L y) dy)·J = J·∫ f(L y) dy (integral_mul_const, valid without integrability assumptions).

8. Conclusion. By step 3, the function r ↦ (rⁿ)⁻¹·∫_B f(η_r(ψ(v)))·Jψ(v) dv agrees with r ↦ ∫ G_r for every r > 0, i.e. on a set belonging to 𝓝[>]0 (self_mem_nhdsWithin). Since eventually equal functions have the same limits (Tendsto.congr'), step 7 yields (rⁿ)⁻¹·∫_B f(η_r(ψ(v)))·Jψ(v) dv → Jψ(u)·∫_{ℝⁿ} f(Dψ(u) y) dy as r → 0⁺. (The case n = 0 needs no separate treatment.) ∎

Formalization aid (optional; the numbered proof above is complete on its own). The following Lean script for exactly this frozen statement was compiled by the parent decomposition session against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b36630) in the contract scope shown; `#print axioms` reported only propext, Classical.choice, Quot.sound. It cites the sibling declarations Submission.chartTD_normDet_le_opNorm_pow, Submission.chartTD_chart_fderiv_bounds by their frozen names.

```lean
import GMT.Ch03.Submission
open Filter MeasureTheory Module Set
open scoped CompactlySupported ENNReal NNReal Topology
namespace GMT.Ch03
open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt HasWeightedApproximateTangentSpaceAt PurelyUnrectifiable blowUpMap)

theorem Submission.chartTD_chart_blowup_integral_tendsto : (∀ (n N : ℕ) (B : Set (Rn n)) (ψ : Rn n → Rn N) (K : ℝ≥0) (c : ℝ), IsOpen B → ContDiffOn ℝ 1 ψ B → LipschitzOnWith K ψ B → 0 < c → (∀ u ∈ B, ∀ u' ∈ B, c * ‖u - u'‖ ≤ ‖ψ u - ψ u'‖) → ∀ u ∈ B, ∀ f : C_c(Rn N, ℝ), Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ v in B, f (blowUpMap (ψ u) r (ψ v)) * (fderiv ℝ ψ v).toLinearMap.normDet) (𝓝[>] 0) (𝓝 ((fderiv ℝ ψ u).toLinearMap.normDet * ∫ y, f (fderiv ℝ ψ u y)))) := by
  intro n N B ψ K c hB hψ hLip hc hlow u hu f
  set J : Rn n → ℝ := fun v => (fderiv ℝ ψ v).toLinearMap.normDet with hJdef
  set L := fderiv ℝ ψ u with hLdef
  have hBmeas : MeasurableSet B := hB.measurableSet
  have hND : Continuous (fun A : Rn n →L[ℝ] Rn N ↦ A.toLinearMap.normDet) := by
    have key : ∀ A : Rn n →L[ℝ] Rn N, A.toLinearMap.normDet =
        Real.sqrt ((ContinuousLinearMap.adjoint A ∘L A).det) := by
      intro A
      rw [← A.normDet_sq]
      simp [Real.sqrt_sq (LinearMap.normDet_nonneg _)]
    simp_rw [key]
    exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id))
  have hJmeas : Measurable J := hND.measurable.comp (measurable_fderiv ℝ ψ)
  have hJnn : ∀ v, 0 ≤ J v := fun v => LinearMap.normDet_nonneg _
  have hJle : ∀ v ∈ B, J v ≤ (K : ℝ) ^ n := fun v hv =>
    (Submission.chartTD_normDet_le_opNorm_pow n N _).trans
      (pow_le_pow_left₀ (norm_nonneg _)
        (Submission.chartTD_chart_fderiv_bounds n N B ψ K c hB hψ hLip hlow v hv).1 n)
  have hJcont : ContinuousAt J u := by
    have h1 : ContinuousAt (fderiv ℝ ψ) u :=
      (hψ.continuousOn_fderiv_of_isOpen hB le_rfl).continuousAt (hB.mem_nhds hu)
    exact hND.continuousAt.comp h1
  have hψcont : ContinuousOn ψ B := hLip.continuousOn
  have hd : HasFDerivAt ψ L u :=
    ((hψ.differentiableOn one_ne_zero).differentiableAt (hB.mem_nhds hu)).hasFDerivAt
  obtain ⟨M, hM⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  obtain ⟨R, hR⟩ : ∃ R, ∀ z, f z ≠ 0 → ‖z‖ ≤ R := by
    obtain ⟨R, hR⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
    exact ⟨R, fun z hz => by simpa using hR (subset_tsupport _ hz)⟩
  let h : ℝ → Rn n → ℝ := fun r v => f (blowUpMap (ψ u) r (ψ v)) * J v
  let G : ℝ → Rn n → ℝ := fun r y => B.indicator (h r) (u + r • y)
  have hsub : ∀ r : ℝ, 0 < r →
      (r ^ n)⁻¹ * ∫ v in B, f (blowUpMap (ψ u) r (ψ v)) * J v = ∫ y, G r y := by
    intro r hr
    rw [← integral_indicator hBmeas]
    have h1 := Measure.integral_comp_smul (volume : Measure (Rn n))
      (fun y => B.indicator (h r) (u + y)) r
    rw [integral_add_left_eq_self (fun y => B.indicator (h r) y) u] at h1
    rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hr n)), smul_eq_mul] at h1
    exact h1.symm
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hDCT : Tendsto (fun r => ∫ y, G r y) (𝓝[>] 0) (𝓝 (∫ y, f (L y) * J u)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => (Metric.closedBall (0 : Rn n) (R / c)).indicator (fun _ => M * (K : ℝ) ^ n) y)
      ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have haff : Continuous (fun y : Rn n => u + r • y) := by fun_prop
      set S : Set (Rn n) := (fun y : Rn n => u + r • y) ⁻¹' B with hSdef
      have hSopen : IsOpen S := hB.preimage haff
      have hGS : G r = S.indicator (fun y => h r (u + r • y)) := by
        funext y
        by_cases hy : u + r • y ∈ B
        · simp [G, S, Set.indicator_of_mem, hy]
        · simp [G, S, Set.indicator_of_notMem, hy]
      rw [hGS, aestronglyMeasurable_indicator_iff hSopen.measurableSet]
      have h1 : ContinuousOn (fun y : Rn n => f (blowUpMap (ψ u) r (ψ (u + r • y)))) S := by
        have hb : Continuous (fun z : Rn N => blowUpMap (ψ u) r z) := by
          unfold blowUpMap; fun_prop
        exact (f.continuous.comp hb).comp_continuousOn
          (hψcont.comp haff.continuousOn (fun y hy => hy))
      have h2 : Measurable (fun y : Rn n => J (u + r • y)) := hJmeas.comp haff.measurable
      exact (h1.aestronglyMeasurable hSopen.measurableSet).mul
        h2.aestronglyMeasurable.restrict
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : (0:ℝ) < r := hr
      refine Eventually.of_forall (fun y => ?_)
      by_cases hy : u + r • y ∈ B
      · have hGy : G r y = f (blowUpMap (ψ u) r (ψ (u + r • y))) * J (u + r • y) := by
          simp [G, h, Set.indicator_of_mem, hy]
        rw [hGy]
        by_cases hf0 : f (blowUpMap (ψ u) r (ψ (u + r • y))) = 0
        · rw [hf0, zero_mul, norm_zero]
          exact Set.indicator_nonneg (fun _ _ => by positivity) _
        · have hRb := hR _ hf0
          have hyball : y ∈ Metric.closedBall (0 : Rn n) (R / c) := by
            rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hc]
            have h1 := hlow (u + r • y) hy u hu
            rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr'.le] at h1
            unfold blowUpMap at hRb
            rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr'.le)] at hRb
            have h2 : ‖ψ (u + r • y) - ψ u‖ ≤ r * R := by
              rw [inv_mul_le_iff₀ hr'] at hRb; linarith
            nlinarith
          rw [Set.indicator_of_mem hyball, norm_mul, Real.norm_of_nonneg (hJnn _)]
          exact mul_le_mul (hM _) (hJle _ hy) (hJnn _) hM0
      · have hGy : G r y = 0 := by simp [G, Set.indicator_of_notMem, hy]
        rw [hGy, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => by positivity) _
    · exact (integrableOn_const (measure_closedBall_lt_top (x := (0 : Rn n)) (r := R / c)).ne).integrable_indicator
        measurableSet_closedBall
    · refine Eventually.of_forall (fun y => ?_)
      have hlin : Tendsto (fun r : ℝ => u + r • y) (𝓝[>] 0) (𝓝 u) := by
        have : Tendsto (fun r : ℝ => u + r • y) (𝓝 0) (𝓝 (u + (0:ℝ) • y)) :=
          ((continuous_const.add (continuous_id.smul continuous_const)).tendsto 0)
        simpa using this.mono_left nhdsWithin_le_nhds
      have hevB : ∀ᶠ r in 𝓝[>] (0:ℝ), u + r • y ∈ B := hlin (hB.mem_nhds hu)
      have hq : Tendsto (fun r : ℝ => blowUpMap (ψ u) r (ψ (u + r • y))) (𝓝[>] 0) (𝓝 (L y)) := by
        have := hd.lim y (c := fun r : ℝ => r⁻¹) (l := 𝓝[>] (0:ℝ)) (by
          refine (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).congr' ?_
          filter_upwards [self_mem_nhdsWithin] with t ht
          simp [abs_of_pos (show (0:ℝ) < t from ht)])
        simpa [blowUpMap, inv_inv] using this
      have hlim : Tendsto (fun r : ℝ => f (blowUpMap (ψ u) r (ψ (u + r • y))) * J (u + r • y))
          (𝓝[>] 0) (𝓝 (f (L y) * J u)) :=
        ((f.continuous.tendsto _).comp hq).mul (hJcont.tendsto.comp hlin)
      refine hlim.congr' ?_
      filter_upwards [hevB] with r hr
      simp [G, h, Set.indicator_of_mem, hr]
  rw [integral_mul_const, mul_comm] at hDCT
  refine hDCT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hsub r hr).symm

end GMT.Ch03
```

## Key steps

1. normDet = √det(A*A) is continuous, so Jψ is Borel and continuous at u; 0 ≤ Jψ ≤ Kⁿ on B (siblings fderiv_bounds, normdet_le_opnorm_pow); ψ has derivative L = Dψ(u) at u.
2. Substitution v = u + r y (integral_comp_smul, integral_add_left_eq_self): r⁻ⁿ∫_B f(η_r(ψ v))Jψ(v) dv = ∫ G_r(y) dy with G_r(y) = (1_B·h_r)(u + r y).
3. G_r is a.e.-strongly measurable and |G_r| ≤ M Kⁿ 1_{B̄_{R/c}(0)} (lower bound: f ≠ 0 forces |y| ≤ R/c), an integrable bound independent of r.
4. Pointwise G_r(y) → f(L y)·Jψ(u) (HasFDerivAt.lim, continuity of f and of Jψ at u).
5. Dominated convergence along 𝓝[>]0 and integral_mul_const give the limit Jψ(u)·∫ f(L y) dy.

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
