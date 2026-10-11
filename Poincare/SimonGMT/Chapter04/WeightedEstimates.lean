module

public import Poincare.SimonGMT.Chapter04.WeightedCutoff

@[expose] public section

/-!
# Simon GMT, Chapter 4, (5.2)--(5.3): weighted radial estimates

All norms are norms of the actual tangential gradient and curvature field.
The compactly supported energy terms are proved integrable before their
Bochner integrals are compared.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

theorem continuousOn_gradient {U : Set E} (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) : ContinuousOn (gradient h) U := by
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
    (hh.continuousOn_fderiv_of_isOpen hU le_rfl)

theorem tangentialGradient_aemeasurableOn {U : Set E} (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) {K : Set E}
    (hK : MeasurableSet K) (hKU : K ⊆ U) :
    AEMeasurable (V.tangentialGradient h) (V.weight.restrict K) := by
  have hgrad := ((continuousOn_gradient hU hh).mono hKU).aemeasurable hK (μ := V.weight)
  exact ContinuousLinearMap.measurable_apply₂.comp_aemeasurable
    (V.tangentProjection_aemeasurable_weight.restrict.prodMk hgrad)

theorem norm_tangentialGradient_le (h : E → ℝ) (x : E) :
    ‖V.tangentialGradient h x‖ ≤ ‖gradient h x‖ :=
  (V.tangentAt x).norm_starProjection_apply_le _

/-- The gradient contribution in (5.2)--(5.3) is integrable, by compact
boundedness of the ambient gradient and the norm-one tangent projection. -/
theorem integrable_weightedCutoff_gradientEnergy {U : Set E} (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    Integrable (fun x ↦ scaledRadialCutoff ξ φ ρ x *
      (‖x - ξ‖ * ‖V.tangentialGradient h x‖)) V.weight := by
  obtain ⟨S, hρS, hSball⟩ := exists_larger_closedBall_subset hU ξ (mul_pos hρ hA).le hball
  have hS : 0 < S := (mul_pos hρ hA).trans hρS
  obtain ⟨B, hB⟩ := (isCompact_closedBall ξ S).exists_bound_of_continuousOn
    ((continuousOn_gradient hU hh).mono hSball)
  apply (V.hasDerivAt_integral_scaledRadialCutoff_mul_local ξ hφ hA hcutoff hρ hρS
    (q := fun x ↦ ‖x - ξ‖ * ‖V.tangentialGradient h x‖) (B := S * max B 0)
    (((continuous_id.sub continuous_const).norm.aemeasurable.mul
      (V.tangentialGradient_aemeasurableOn hU hh measurableSet_closedBall hSball).norm).aestronglyMeasurable)
    ?_).1
  intro x hx
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  apply mul_le_mul
    (show ‖x - ξ‖ ≤ S by simpa only [mem_closedBall, dist_eq_norm] using hx)
    ((V.norm_tangentialGradient_le h x).trans ((hB x hx).trans (le_max_left B 0)))
    (norm_nonneg _) hS.le

/-- Local `L¹` curvature controls the norm pairing against every continuous
compactly supported vector field in its domain. -/
theorem HasGeneralizedMeanCurvatureIn.integrable_norm_mul_norm
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    {X : E → E} (hX : Continuous X) (hcompact : HasCompactSupport X)
    (hsupport : tsupport X ⊆ U) :
    Integrable (fun x ↦ ‖X x‖ * ‖H x‖) V.weight := by
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuous hX
  have hHint := hH.1.integrableOn_compact_subset hsupport hcompact
  have hint : IntegrableOn (fun x ↦ ‖X x‖ * ‖H x‖) (tsupport X) V.weight := by
    apply (hHint.norm.const_mul C).mono'
    · exact (hX.norm.aestronglyMeasurable.mul hHint.norm.aestronglyMeasurable)
    · filter_upwards with x
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  apply hint.integrable_of_forall_notMem_eq_zero
  intro x hx
  simp only [image_eq_zero_of_notMem_tsupport hx, norm_zero, zero_mul]

theorem HasGeneralizedMeanCurvatureIn.integrable_weightedCutoff_curvatureEnergy
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hhnonneg : ∀ x ∈ U, 0 ≤ h x) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφnonneg : ∀ t, 0 ≤ φ t) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    Integrable (fun x ↦ scaledRadialCutoff ξ φ ρ x * (‖x - ξ‖ * (h x * ‖H x‖))) V.weight := by
  let η : ℝ → ℝ := fun t ↦ φ (t / ρ ^ 2)
  have hη : ContDiff ℝ 1 η := hφ.comp (contDiff_id.div_const (ρ ^ 2))
  have hηcutoff : ∀ t, (ρ * A) ^ 2 ≤ t → η t = 0 := by
    intro t ht
    apply hcutoff
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
    nlinarith [ht]
  let X := squaredRadialVectorField ξ η
  have hX : ContDiff ℝ 1 X := contDiff_squaredRadialVectorField ξ hη
  have hcompact : HasCompactSupport X :=
    hasCompactSupport_squaredRadialVectorField ξ (mul_pos hρ hA).le hηcutoff
  have hsupport : tsupport X ⊆ U :=
    (tsupport_squaredRadialVectorField_subset_closedBall ξ (mul_pos hρ hA).le hηcutoff).trans hball
  have hint := HasGeneralizedMeanCurvatureIn.integrable_norm_mul_norm (V := V) hH
    (contDiff_smul_of_tsupport_subset hU hh hX hsupport).continuous hcompact.smul_left
    ((tsupport_smul_subset_right h X).trans hsupport)
  apply hint.congr
  filter_upwards with x
  by_cases hx : x ∈ closedBall ξ (ρ * A)
  · simp only [X, squaredRadialVectorField, norm_smul, Real.norm_of_nonneg (hhnonneg x (hball hx)),
      η, Real.norm_of_nonneg (hφnonneg _), scaledRadialCutoff]
    ring
  · have hz := scaledRadialCutoff_eq_zero_of_notMem_closedBall ξ hA hcutoff hρ hx
    change ‖h x • (scaledRadialCutoff ξ φ ρ x • (x - ξ))‖ * ‖H x‖ = _
    simp only [hz, zero_smul, smul_zero, norm_zero, zero_mul]

/-- Exact Simon (5.3): the radial error is bounded below by the integral
of `r(|∇ᴹh|+h|H|)`. No bounded-curvature hypothesis is introduced. -/
theorem HasGeneralizedMeanCurvatureIn.weightedCutoffPairing_lower_bound
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hhnonneg : ∀ x ∈ U, 0 ≤ h x) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφnonneg : ∀ t, 0 ≤ φ t) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    -(∫ x, scaledRadialCutoff ξ φ ρ x *
      (‖x - ξ‖ * (‖V.tangentialGradient h x‖ + h x * ‖H x‖)) ∂V.weight) / ρ ^ (n + 1) ≤
        V.weightedCutoffGradientCurvaturePairing ξ h H φ ρ / ρ ^ (n + 1) := by
  have hg := V.integrable_weightedCutoff_gradientEnergy hU hh ξ hφ hA hcutoff hρ hball
  have hc := HasGeneralizedMeanCurvatureIn.integrable_weightedCutoff_curvatureEnergy
    (V := V) hH hU hh hhnonneg ξ hφ hφnonneg hA hcutoff hρ hball
  have he : Integrable (fun x ↦ scaledRadialCutoff ξ φ ρ x *
      (‖x - ξ‖ * (‖V.tangentialGradient h x‖ + h x * ‖H x‖))) V.weight := by
    convert hg.add hc using 1
    funext x
    simp only [Pi.add_apply]
    ring
  have hp := (HasGeneralizedMeanCurvatureIn.weightedCutoffMass_deriv_identity
    (V := V) hH hU hh ξ hφ hA hcutoff hρ hball).1
  apply div_le_div_of_nonneg_right ?_ (pow_pos hρ _).le
  rw [← integral_neg]
  apply integral_mono he.neg hp
  intro x
  by_cases hx : x ∈ closedBall ξ (ρ * A)
  · have h := mul_le_mul_of_nonneg_left (V.weighted_radialPairing_lower_bound ξ x h H
      (hhnonneg x (hball hx))) (hφnonneg (‖x - ξ‖ ^ 2 / ρ ^ 2))
    dsimp [scaledRadialCutoff] at h ⊢
    linarith
  · simp only [Pi.neg_apply, scaledRadialCutoff_eq_zero_of_notMem_closedBall ξ hA hcutoff hρ hx,
      zero_mul, neg_zero, le_rfl]

/-- Corrected (5.2). A cutoff supported in `r≤Aρ` gives the coefficient
`AΛ` multiplying `Ĩ/ρⁿ`; at `A=1` this is `Λ`, not the printed `Λρ`.
The curvature bound is required only on the varifold carrier in `U`. -/
theorem HasGeneralizedMeanCurvatureIn.weightedCutoffPairing_lower_bound_of_bounded
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hhnonneg : ∀ x ∈ U, 0 ≤ h x) (ξ : E)
    {Λ : ℝ} (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφnonneg : ∀ t, 0 ≤ φ t) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    -(∫ x, scaledRadialCutoff ξ φ ρ x * (‖x - ξ‖ * ‖V.tangentialGradient h x‖) ∂V.weight) /
        ρ ^ (n + 1) - A * Λ * (V.weightedCutoffMass ξ h φ ρ / ρ ^ n) ≤
      V.weightedCutoffGradientCurvaturePairing ξ h H φ ρ / ρ ^ (n + 1) := by
  have hg := V.integrable_weightedCutoff_gradientEnergy hU hh ξ hφ hA hcutoff hρ hball
  have hc := HasGeneralizedMeanCurvatureIn.integrable_weightedCutoff_curvatureEnergy
    (V := V) hH hU hh hhnonneg ξ hφ hφnonneg hA hcutoff hρ hball
  have hi := (V.weightedCutoff_derivatives hU hh ξ hφ hA hcutoff hρ hball).1.1
  let Ig := ∫ x, scaledRadialCutoff ξ φ ρ x * (‖x - ξ‖ * ‖V.tangentialGradient h x‖) ∂V.weight
  let Ic := ∫ x, scaledRadialCutoff ξ φ ρ x * (‖x - ξ‖ * (h x * ‖H x‖)) ∂V.weight
  have hIc : Ic ≤ ρ * A * Λ * V.weightedCutoffMass ξ h φ ρ := by
    rw [weightedCutoffMass, ← integral_const_mul]
    apply integral_mono_ae hc (hi.const_mul (ρ * A * Λ))
    have hcarrier : ∀ᵐ x ∂V.weight, x ∈ V.carrier :=
      V.ae_weight_of_ae_restrict (ae_restrict_mem V.measurable_carrier)
    filter_upwards [hcarrier] with x hxcarrier
    by_cases hx : x ∈ closedBall ξ (ρ * A)
    · have hr : ‖x - ξ‖ ≤ ρ * A := by simpa only [mem_closedBall, dist_eq_norm] using hx
      have hh0 := hhnonneg x (hball hx)
      have hHbound := hbound x ⟨hxcarrier, hball hx⟩
      have hm := mul_le_mul hr hHbound (norm_nonneg _) (mul_pos hρ hA).le
      have hm' := mul_le_mul_of_nonneg_left hm
        (mul_nonneg (hφnonneg (‖x - ξ‖ ^ 2 / ρ ^ 2)) hh0)
      dsimp [scaledRadialCutoff] at hm' ⊢
      nlinarith
    · simp only [scaledRadialCutoff_eq_zero_of_notMem_closedBall ξ hA hcutoff hρ hx, zero_mul,
        mul_zero, le_rfl]
  have hR := HasGeneralizedMeanCurvatureIn.weightedCutoffPairing_lower_bound
    (V := V) hH hU hh hhnonneg ξ hφ hφnonneg hA hcutoff hρ hball
  have heq : (fun x ↦ scaledRadialCutoff ξ φ ρ x *
      (‖x - ξ‖ * (‖V.tangentialGradient h x‖ + h x * ‖H x‖))) =
      (fun x ↦ scaledRadialCutoff ξ φ ρ x * (‖x - ξ‖ * ‖V.tangentialGradient h x‖) +
        scaledRadialCutoff ξ φ ρ x * (‖x - ξ‖ * (h x * ‖H x‖))) := by
    funext x
    ring
  rw [heq, integral_add hg hc] at hR
  change -(Ig + Ic) / ρ ^ (n + 1) ≤ _ at hR
  change -Ig / ρ ^ (n + 1) - A * Λ * (V.weightedCutoffMass ξ h φ ρ / ρ ^ n) ≤ _
  calc
    _ = (-Ig - ρ * A * Λ * V.weightedCutoffMass ξ h φ ρ) / ρ ^ (n + 1) := by
      rw [pow_succ]
      field_simp
    _ ≤ -(Ig + Ic) / ρ ^ (n + 1) :=
      div_le_div_of_nonneg_right (by linarith) (pow_pos hρ _).le
    _ ≤ _ := hR

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
