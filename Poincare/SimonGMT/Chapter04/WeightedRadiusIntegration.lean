module

public import Poincare.SimonGMT.Chapter04.WeightedEstimates

@[expose] public section

/-!
# Radius integration for Simon Chapter 4, (5.4)--(5.5)

The compact-ball energy is genuinely integrable, even when its singular
potential is infinite.  The inequalities below are derived from weighted
first variation, not assumed as radial comparison hypotheses.
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

theorem integrableOn_norm_tangentialGradient {U : Set E} (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    IntegrableOn (fun x ↦ ‖V.tangentialGradient h x‖) K V.weight := by
  have hg : IntegrableOn (fun x ↦ ‖gradient h x‖) K V.weight :=
    ((continuousOn_gradient hU hh).mono hKU).norm.integrableOn_compact hK
  apply hg.mono'
    (V.tangentialGradient_aemeasurableOn hU hh hK.measurableSet hKU).norm.aestronglyMeasurable
  filter_upwards with x
  simpa only [norm_norm] using V.norm_tangentialGradient_le h x

theorem HasGeneralizedMeanCurvatureIn.integrableOn_weightedEnergy
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    IntegrableOn (fun x ↦ ‖V.tangentialGradient h x‖ + h x * ‖H x‖) K V.weight := by
  apply (V.integrableOn_norm_tangentialGradient hU hh hK hKU).add
  exact IntegrableOn.continuousOn_mul (hh.continuousOn.mono hKU)
    (hH.1.integrableOn_compact_subset hKU hK).norm hK

/-- A useful localization identity: cutoffs supported in the smaller ball
can be integrated after truncating an arbitrary weight to the larger ball. -/
theorem scaledRadialCutoff_mul_indicator (ξ : E) {φ : ℝ → ℝ}
    {A t S : ℝ} (hA : 0 < A) (hcutoff : ∀ z, A ^ 2 ≤ z → φ z = 0)
    (ht : 0 < t) (htS : t * A ≤ S) (q : E → ℝ) :
    (fun x ↦ scaledRadialCutoff ξ φ t x * (closedBall ξ S).indicator q x) =
      (fun x ↦ scaledRadialCutoff ξ φ t x * q x) := by
  classical
  funext x
  by_cases hx : x ∈ closedBall ξ S
  · rw [indicator_of_mem hx]
  · have hx' : x ∉ closedBall ξ (t * A) :=
      fun hx' ↦ hx (closedBall_subset_closedBall htS hx')
    simp only [scaledRadialCutoff_eq_zero_of_notMem_closedBall ξ hA hcutoff ht hx', zero_mul]

/-- Continuity in the radius only needs integrability of the weight on a
fixed support ball; boundedness of that weight is unnecessary. -/
theorem continuousOn_integral_scaledRadialCutoff_mul
    (ξ : E) {φ : ℝ → ℝ} (hφ : Continuous φ) (hφrange : ∀ z, φ z ∈ Icc 0 1)
    {A σ ρ : ℝ} (hA : 0 < A) (hcutoff : ∀ z, A ^ 2 ≤ z → φ z = 0)
    (hσ : 0 < σ) {q : E → ℝ} (hq : IntegrableOn q (closedBall ξ (ρ * A)) V.weight) :
    ContinuousOn (fun t ↦ ∫ x, scaledRadialCutoff ξ φ t x * q x ∂V.weight) (Icc σ ρ) := by
  classical
  let q' := (closedBall ξ (ρ * A)).indicator q
  have hq' : Integrable q' V.weight := hq.integrable_indicator measurableSet_closedBall
  have hcont : ContinuousOn (fun t ↦ ∫ x, scaledRadialCutoff ξ φ t x * q' x ∂V.weight)
      (Icc σ ρ) := by
    apply continuousOn_of_dominated (bound := fun x ↦ ‖q' x‖)
    · intro t ht
      exact ((hφ.comp (by fun_prop : Continuous (fun x : E ↦ ‖x - ξ‖ ^ 2 / t ^ 2))).aestronglyMeasurable.mul
        hq'.aestronglyMeasurable)
    · intro t ht
      filter_upwards with x
      rw [norm_mul, scaledRadialCutoff, Real.norm_of_nonneg (hφrange _).1]
      exact (mul_le_mul_of_nonneg_right (hφrange _).2 (norm_nonneg _)).trans_eq (one_mul _)
    · exact hq'.norm
    · filter_upwards with x
      apply ContinuousOn.mul ?_ continuousOn_const
      exact hφ.comp_continuousOn (continuousOn_const.div (continuousOn_id.pow 2)
        (fun t ht ↦ pow_ne_zero _ (hσ.trans_le ht.1).ne'))
  apply hcont.congr
  intro t ht
  dsimp only [q']
  rw [scaledRadialCutoff_mul_indicator ξ hA hcutoff (hσ.trans_le ht.1)
    (mul_le_mul_of_nonneg_right ht.2 hA.le)]

/-- Dominated convergence for an integrable weight, including all mass on
the boundary sphere in the limiting closed ball. -/
theorem tendsto_integral_scaledRadialCutoff_mul_integrable
    (ξ : E) {ρ : ℝ} (hρ : 0 < ρ) {q : E → ℝ} (hq : Integrable q V.weight) :
    Tendsto (fun ε ↦ ∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) ρ x * q x ∂V.weight)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in closedBall ξ ρ, q x ∂V.weight)) := by
  classical
  rw [← integral_indicator measurableSet_closedBall]
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖q x‖)
  · exact Eventually.of_forall fun ε ↦
      (((contDiff_monotonicityCutoff ε).continuous.comp
        (by fun_prop : Continuous (fun x : E ↦ ‖x - ξ‖ ^ 2 / ρ ^ 2))).aestronglyMeasurable.mul
        hq.aestronglyMeasurable)
  · apply Eventually.of_forall
    intro ε
    filter_upwards with x
    rw [norm_mul, scaledRadialCutoff,
      Real.norm_of_nonneg (monotonicityCutoff_mem_Icc ε _).1]
    exact (mul_le_mul_of_nonneg_right (monotonicityCutoff_mem_Icc ε _).2
      (norm_nonneg _)).trans_eq (one_mul _)
  · exact hq.norm
  · filter_upwards with x
    convert (tendsto_scaledRadialCutoff ξ x hρ).mul_const (q x) using 1
    by_cases hx : x ∈ closedBall ξ ρ <;> simp [hx]

theorem tendsto_integral_scaledRadialCutoff_mul_local
    (ξ : E) {ρ S : ℝ} (hρ : 0 < ρ) (hρS : ρ < S) {q : E → ℝ}
    (hq : IntegrableOn q (closedBall ξ S) V.weight) :
    Tendsto (fun ε ↦ ∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) ρ x * q x ∂V.weight)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in closedBall ξ ρ, q x ∂V.weight)) := by
  classical
  let q' := (closedBall ξ S).indicator q
  have hq' : Integrable q' V.weight := hq.integrable_indicator measurableSet_closedBall
  have hlim := V.tendsto_integral_scaledRadialCutoff_mul_integrable ξ hρ hq'
  have heq : (∫ x in closedBall ξ ρ, q' x ∂V.weight) =
      ∫ x in closedBall ξ ρ, q x ∂V.weight := by
    apply setIntegral_congr_fun measurableSet_closedBall
    intro x hx
    exact indicator_of_mem (closedBall_subset_closedBall hρS.le hx) q
  rw [heq] at hlim
  apply hlim.congr'
  have hδ : 0 < S / ρ - 1 := by rw [sub_pos, lt_div_iff₀ hρ]; simpa using hρS
  filter_upwards [self_mem_nhdsWithin,
    (gt_mem_nhds hδ).filter_mono inf_le_left] with ε hε hsmall
  change 0 < ε at hε
  have hA : 0 < 1 + ε := by linarith
  have hsmall' : ρ * (1 + ε) ≤ S := by
    have := (lt_div_iff₀ hρ).mp (show 1 + ε < S / ρ by linarith)
    nlinarith
  dsimp only [q']
  rw [scaledRadialCutoff_mul_indicator ξ hA (monotonicityCutoff_cutoff hε) hρ hsmall']

/-- The integrated smooth-cutoff form of the inequality immediately
preceding Simon (5.5). All terms here are finite by local `L¹` curvature. -/
theorem HasGeneralizedMeanCurvatureIn.weightedCutoff_radius_inequality
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hhnonneg : ∀ x ∈ U, 0 ≤ h x) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφanti : Antitone φ)
    (hφrange : ∀ z, φ z ∈ Icc 0 1) {A σ ρ : ℝ} (hA : 0 < A)
    (hcutoff : ∀ z, A ^ 2 ≤ z → φ z = 0) (hσ : 0 < σ) (hσρ : σ ≤ ρ)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    V.weightedCutoffMass ξ h φ σ / σ ^ n ≤
      V.weightedCutoffMass ξ h φ ρ / ρ ^ n +
        ∫ t in σ..ρ, (∫ x, scaledRadialCutoff ξ φ t x *
          (‖x - ξ‖ * (‖V.tangentialGradient h x‖ + h x * ‖H x‖)) ∂V.weight) / t ^ (n + 1) := by
  let q := fun x ↦ ‖x - ξ‖ * (‖V.tangentialGradient h x‖ + h x * ‖H x‖)
  have hq : IntegrableOn q (closedBall ξ (ρ * A)) V.weight :=
    IntegrableOn.continuousOn_mul
      (show ContinuousOn (fun x : E ↦ ‖x - ξ‖) (closedBall ξ (ρ * A)) by fun_prop)
      (HasGeneralizedMeanCurvatureIn.integrableOn_weightedEnergy (V := V) hH hU hh
        (isCompact_closedBall _ _) hball) (isCompact_closedBall _ _)
  let e := fun t ↦ (∫ x, scaledRadialCutoff ξ φ t x * q x ∂V.weight) / t ^ (n + 1)
  have he : ContinuousOn e (Icc σ ρ) :=
    (V.continuousOn_integral_scaledRadialCutoff_mul ξ hφ.continuous hφrange hA hcutoff hσ hq).div
      (continuousOn_id.pow _) (fun t ht ↦ pow_ne_zero _ (hσ.trans_le ht.1).ne')
  let f := fun t ↦ V.weightedCutoffMass ξ h φ t / t ^ n
  have hd : ∀ t ∈ Icc σ ρ, DifferentiableAt ℝ f t := by
    intro t ht
    exact (HasGeneralizedMeanCurvatureIn.hasDerivAt_normalizedWeightedCutoffMass
      (V := V) hH hU hh ξ hφ hA hcutoff (hσ.trans_le ht.1)
      ((closedBall_subset_closedBall (mul_le_mul_of_nonneg_right ht.2 hA.le)).trans hball)).differentiableAt
  have hle : ∀ t ∈ Icc σ ρ, -e t ≤ deriv f t := by
    intro t ht
    have ht0 := hσ.trans_le ht.1
    have htball := (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right ht.2 hA.le)).trans hball
    have hb := HasGeneralizedMeanCurvatureIn.weightedCutoffPairing_lower_bound
      (V := V) hH hU hh hhnonneg ξ hφ (fun z ↦ (hφrange z).1) hA hcutoff ht0 htball
    have hb' : -e t ≤ V.weightedCutoffGradientCurvaturePairing ξ h H φ t / t ^ (n + 1) := by
      simpa only [e, neg_div, q] using hb
    exact hb'.trans
      (HasGeneralizedMeanCurvatureIn.deriv_normalizedWeightedCutoffMass_ge
        (V := V) hH hU hh hhnonneg ξ hφ hφanti hA hcutoff ht0 htball)
  have hi := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hσρ
    (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt.hasDerivWithinAt)
    (he.neg.integrableOn_Icc) (fun t ht ↦ hle t ⟨ht.1.le, ht.2.le⟩)
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at hi
  change - (∫ t in σ..ρ, e t) ≤ f ρ - f σ at hi
  change f σ ≤ f ρ + ∫ t in σ..ρ, e t
  linarith

/-- The integrating-factor version of the preceding inequality. The
coefficient is `AΛ`, as forced by the actual curvature bound on `r≤At`. -/
theorem HasGeneralizedMeanCurvatureIn.weightedCutoff_exp_radius_inequality
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hhnonneg : ∀ x ∈ U, 0 ≤ h x) (ξ : E)
    {Λ : ℝ} (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφanti : Antitone φ)
    (hφrange : ∀ z, φ z ∈ Icc 0 1) {A σ ρ : ℝ} (hA : 0 < A)
    (hcutoff : ∀ z, A ^ 2 ≤ z → φ z = 0) (hσ : 0 < σ) (hσρ : σ ≤ ρ)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    Real.exp (A * Λ * σ) * (V.weightedCutoffMass ξ h φ σ / σ ^ n) ≤
      Real.exp (A * Λ * ρ) * (V.weightedCutoffMass ξ h φ ρ / ρ ^ n) +
        ∫ t in σ..ρ, Real.exp (A * Λ * t) *
          ((∫ x, scaledRadialCutoff ξ φ t x * (‖x - ξ‖ * ‖V.tangentialGradient h x‖) ∂V.weight) /
            t ^ (n + 1)) := by
  let q := fun x ↦ ‖x - ξ‖ * ‖V.tangentialGradient h x‖
  have hq : IntegrableOn q (closedBall ξ (ρ * A)) V.weight :=
    IntegrableOn.continuousOn_mul
      (show ContinuousOn (fun x : E ↦ ‖x - ξ‖) (closedBall ξ (ρ * A)) by fun_prop)
      (V.integrableOn_norm_tangentialGradient hU hh (isCompact_closedBall _ _) hball)
      (isCompact_closedBall _ _)
  let e := fun t ↦ (∫ x, scaledRadialCutoff ξ φ t x * q x ∂V.weight) / t ^ (n + 1)
  have he : ContinuousOn e (Icc σ ρ) :=
    (V.continuousOn_integral_scaledRadialCutoff_mul ξ hφ.continuous hφrange hA hcutoff hσ hq).div
      (continuousOn_id.pow _) (fun t ht ↦ pow_ne_zero _ (hσ.trans_le ht.1).ne')
  let f := fun t ↦ V.weightedCutoffMass ξ h φ t / t ^ n
  have hd : ∀ t ∈ Icc σ ρ, DifferentiableAt ℝ f t := by
    intro t ht
    exact (HasGeneralizedMeanCurvatureIn.hasDerivAt_normalizedWeightedCutoffMass
      (V := V) hH hU hh ξ hφ hA hcutoff (hσ.trans_le ht.1)
      ((closedBall_subset_closedBall (mul_le_mul_of_nonneg_right ht.2 hA.le)).trans hball)).differentiableAt
  have hle : ∀ t ∈ Icc σ ρ, -e t - A * Λ * f t ≤ deriv f t := by
    intro t ht
    have ht0 := hσ.trans_le ht.1
    have htball := (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right ht.2 hA.le)).trans hball
    have hb := HasGeneralizedMeanCurvatureIn.weightedCutoffPairing_lower_bound_of_bounded
      (V := V) hH hU hh hhnonneg ξ hbound hφ (fun z ↦ (hφrange z).1) hA hcutoff ht0 htball
    have hb' : -e t - A * Λ * f t ≤
        V.weightedCutoffGradientCurvaturePairing ξ h H φ t / t ^ (n + 1) := by
      simpa only [e, neg_div, q, f] using hb
    exact hb'.trans (HasGeneralizedMeanCurvatureIn.deriv_normalizedWeightedCutoffMass_ge
      (V := V) hH hU hh hhnonneg ξ hφ hφanti hA hcutoff ht0 htball)
  let g := fun t ↦ Real.exp (A * Λ * t) * f t
  let g' := fun t ↦ Real.exp (A * Λ * t) * (A * Λ * f t + deriv f t)
  have hg : ∀ t ∈ Icc σ ρ, HasDerivAt g (g' t) t := by
    intro t ht
    convert ((hasDerivAt_const_mul (A * Λ) (x := t)).exp).mul (hd t ht).hasDerivAt using 1 <;>
      dsimp only [g, g'] <;> ring
  have he' : ContinuousOn (fun t ↦ -(Real.exp (A * Λ * t) * e t)) (Icc σ ρ) :=
    ((show ContinuousOn (fun t ↦ Real.exp (A * Λ * t)) (Icc σ ρ) by fun_prop).mul he).neg
  have hi := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hσρ
    (fun t ht ↦ (hg t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hg t ⟨ht.1.le, ht.2.le⟩).hasDerivWithinAt)
    he'.integrableOn_Icc (fun t ht ↦ show -(Real.exp (A * Λ * t) * e t) ≤ g' t from by
      dsimp only [g']
      have hb := mul_le_mul_of_nonneg_left (hle t ⟨ht.1.le, ht.2.le⟩)
        (Real.exp_pos (A * Λ * t)).le
      nlinarith)
  rw [intervalIntegral.integral_neg] at hi
  change -(∫ t in σ..ρ, Real.exp (A * Λ * t) * e t) ≤ g ρ - g σ at hi
  change g σ ≤ g ρ + ∫ t in σ..ρ, Real.exp (A * Λ * t) * e t
  linarith

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
