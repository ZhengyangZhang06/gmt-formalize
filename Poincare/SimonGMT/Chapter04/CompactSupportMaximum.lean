module

public import Poincare.SimonGMT.Chapter04.MeanCurvature

@[expose] public section

/-!
# Simon GMT, Chapter 4, Lemma 6.1

The compact-support maximum principle uses an increasing radial test inside
an outer cutoff which is identically one near the support of the weight.
All curvature hypotheses are restricted to the open exterior of the closed
ball; no extension of the curvature with additional regularity is assumed.
As in the source's positive-dimensional varifold convention, `0 < n`.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

namespace RectifiableVarifold

variable {V : RectifiableVarifold (E := E) n}

/-- A compactly supported varifold cannot extend beyond a closed ball if
the radial component of its mean curvature is strictly less than `n` in
absolute value on the exterior. This is Simon 4.6.1, with its curvature
condition written equivalently as `|H · (x-ξ)| < n`. -/
theorem HasGeneralizedMeanCurvatureIn.support_subset_closedBall_of_radial_lt
    (hn : 0 < n) {ξ : E} {R : ℝ} (hR : 0 ≤ R) {H : E → E}
    (hH : V.HasGeneralizedMeanCurvatureIn (closedBall ξ R)ᶜ H)
    (hcompact : IsCompact V.weight.support)
    (hcurv : ∀ᵐ x ∂V.weight.restrict (closedBall ξ R)ᶜ,
      |inner ℝ (H x) (x - ξ)| < (n : ℝ)) :
    V.weight.support ⊆ closedBall ξ R := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcurv' := (ae_restrict_iff' isClosed_closedBall.isOpen_compl.measurableSet).1 hcurv
  have hlarge : ∀ r : ℝ, R < r → V.weight.support ⊆ closedBall ξ r := by
    intro r hRr
    have hr : 0 < r := lt_of_le_of_lt hR hRr
    obtain ⟨S, hrS, hS⟩ := hcompact.isBounded.subset_ball_lt r ξ
    have hS0 : 0 < S := hr.trans hrS
    let γ : ℝ → ℝ := fun t ↦ expNegInvGlue (t - r ^ 2)
    let η : ℝ → ℝ := fun t ↦ γ t * (1 - Real.smoothTransition (t - S ^ 2))
    have hγ : ContDiff ℝ 1 γ := expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)
    have hη : ContDiff ℝ 1 η := hγ.mul
      (contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)))
    have hγmono : Monotone γ := expNegInvGlue.monotone.comp (fun _ _ h ↦ sub_le_sub_right h _)
    have hηcut : ∀ t, (S + 1) ^ 2 ≤ t → η t = 0 := by
      intro t ht
      have htrans : Real.smoothTransition (t - S ^ 2) = 1 :=
        Real.smoothTransition.one_of_one_le (by nlinarith)
      simp [η, htrans]
    have hηeq {t : ℝ} (ht : t < S ^ 2) : η =ᶠ[𝓝 t] γ := by
      filter_upwards [gt_mem_nhds ht] with s hs
      simp [η, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hs.le)]
    let X : E → E := squaredRadialVectorField ξ η
    have hX : ContDiff ℝ 1 X := contDiff_squaredRadialVectorField ξ hη
    have hXc : HasCompactSupport X :=
      hasCompactSupport_squaredRadialVectorField ξ (by positivity) hηcut
    have hXs : tsupport X ⊆ (closedBall ξ R)ᶜ := by
      have hs : tsupport X ⊆ {x : E | r ≤ ‖x - ξ‖} := by
        apply closure_minimal _ (isClosed_le continuous_const (by fun_prop))
        intro x hx
        by_contra h
        have hlt : ‖x - ξ‖ < r := lt_of_not_ge h
        have hγzero : γ (‖x - ξ‖ ^ 2) = 0 :=
          expNegInvGlue.zero_of_nonpos (by nlinarith [norm_nonneg (x - ξ)])
        exact hx (by simp [X, squaredRadialVectorField, η, hγzero])
      intro x hx hball
      have hlow := hs hx
      have hupp : ‖x - ξ‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hball
      exact (not_le_of_gt hRr) (hupp.trans' hlow)
    let F : E → ℝ := fun x ↦ V.tangentialDivergence X x + inner ℝ (X x) (H x)
    have hFi : Integrable F V.weight :=
      (V.tangentialDivergence_integrable_of_isAdmissible hX hXc).add
        (HasGeneralizedMeanCurvatureIn.integrable_inner V hH hX.continuous hXc hXs)
    have hFint : ∫ x, F x ∂V.weight = 0 := by
      rw [integral_add (V.tangentialDivergence_integrable_of_isAdmissible hX hXc)
        (HasGeneralizedMeanCurvatureIn.integrable_inner V hH hX.continuous hXc hXs)]
      rw [HasGeneralizedMeanCurvatureIn.integral_tangentialDivergence V hH hX hXc hXs]
      ring
    have hFformula : ∀ᵐ x ∂V.weight,
        F x = ((n : ℝ) + inner ℝ (x - ξ) (H x)) * γ (‖x - ξ‖ ^ 2) +
          2 * deriv γ (‖x - ξ‖ ^ 2) * ‖V.tangentProjection x (x - ξ)‖ ^ 2 := by
      filter_upwards [V.weight.support_mem_ae, V.tangent_finrank_ae_weight] with x hx hxrank
      have hnorm : ‖x - ξ‖ < S := by simpa only [mem_ball, dist_eq_norm] using hS hx
      have hsquare : ‖x - ξ‖ ^ 2 < S ^ 2 := by nlinarith [norm_nonneg (x - ξ)]
      have heq := hηeq hsquare
      have hderiv : deriv η (‖x - ξ‖ ^ 2) = deriv γ (‖x - ξ‖ ^ 2) := heq.deriv_eq
      dsimp only [F, X]
      rw [V.tangentialDivergence_squaredRadialVectorField ξ x
        ((hη.differentiable (by simp) _).hasDerivAt) hxrank,
        hderiv, heq.eq_of_nhds]
      simp only [squaredRadialVectorField, real_inner_smul_left, heq.eq_of_nhds]
      ring
    have hFpos : ∀ᵐ x ∂V.weight,
        0 ≤ F x ∧ (0 < γ (‖x - ξ‖ ^ 2) → 0 < F x) := by
      filter_upwards [hFformula, hcurv'] with x hx hcx
      rw [hx]
      have hterm : 0 ≤ 2 * deriv γ (‖x - ξ‖ ^ 2) *
          ‖V.tangentProjection x (x - ξ)‖ ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num) hγmono.deriv_nonneg) (sq_nonneg _)
      have hγnonneg : 0 ≤ γ (‖x - ξ‖ ^ 2) := expNegInvGlue.nonneg _
      by_cases hg : γ (‖x - ξ‖ ^ 2) = 0
      · simp only [hg, mul_zero, zero_add, lt_self_iff_false, false_implies, and_true]
        exact hterm
      · have hgpos : 0 < γ (‖x - ξ‖ ^ 2) := lt_of_le_of_ne hγnonneg (Ne.symm hg)
        have hxext : x ∈ (closedBall ξ R)ᶜ := by
          have ht : r ^ 2 < ‖x - ξ‖ ^ 2 :=
            sub_pos.mp (lt_of_not_ge (fun h ↦ hg (expNegInvGlue.zero_of_nonpos h)))
          simp only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le]
          nlinarith [norm_nonneg (x - ξ)]
        have hh := (abs_lt.mp (hcx hxext)).1
        rw [real_inner_comm (x - ξ) (H x)] at hh
        have hcoeff : 0 < (n : ℝ) + inner ℝ (x - ξ) (H x) := by linarith
        have hpos := add_pos_of_pos_of_nonneg (mul_pos hcoeff hgpos) hterm
        exact ⟨hpos.le, fun _ ↦ hpos⟩
    have hFzero := (integral_eq_zero_iff_of_nonneg_ae (hFpos.mono fun _ h ↦ h.1) hFi).1 hFint
    have hγzero : ∀ᵐ x ∂V.weight, γ (‖x - ξ‖ ^ 2) = 0 := by
      filter_upwards [hFpos, hFzero] with x hx hz
      by_contra h
      have := hx.2 (lt_of_le_of_ne (expNegInvGlue.nonneg _) (Ne.symm h))
      simp only [hz, Pi.zero_apply, lt_self_iff_false] at this
    have hzeroSupport : V.weight.support ⊆ {x | γ (‖x - ξ‖ ^ 2) = 0} :=
      V.weight.support_subset_of_isClosed
        (isClosed_eq (hγ.continuous.comp (by fun_prop)) continuous_const) hγzero
    intro x hx
    have hz : ‖x - ξ‖ ^ 2 ≤ r ^ 2 := by
      simpa only [mem_ofPred_eq, γ, expNegInvGlue.zero_iff_nonpos, sub_nonpos] using hzeroSupport hx
    simp only [mem_closedBall, dist_eq_norm]
    nlinarith [norm_nonneg (x - ξ)]
  intro x hx
  simp only [mem_closedBall, dist_eq_norm]
  by_contra h
  have hRx : R < ‖x - ξ‖ := lt_of_not_ge h
  have := hlarge ((R + ‖x - ξ‖) / 2) (by linarith) hx
  simp only [mem_closedBall, dist_eq_norm] at this
  linarith

/-- Simon 4.6.1 with the source's normalized radial-curvature hypothesis. -/
theorem HasGeneralizedMeanCurvatureIn.support_subset_closedBall
    (hn : 0 < n) {ξ : E} {R : ℝ} (hR : 0 ≤ R) {H : E → E}
    (hH : V.HasGeneralizedMeanCurvatureIn (closedBall ξ R)ᶜ H)
    (hcompact : IsCompact V.weight.support)
    (hcurv : ∀ᵐ x ∂V.weight.restrict (closedBall ξ R)ᶜ,
      (n : ℝ)⁻¹ * |inner ℝ (H x) (x - ξ)| < 1) :
    V.weight.support ⊆ closedBall ξ R := by
  apply hH.support_subset_closedBall_of_radial_lt hn hR hcompact
  filter_upwards [hcurv] with x hx
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rwa [← div_eq_inv_mul, div_lt_one hn'] at hx

/-- The stationary special case of the compact-support maximum principle. -/
theorem IsStationaryIn.support_subset_closedBall
    (hn : 0 < n) {ξ : E} {R : ℝ} (hR : 0 ≤ R)
    (hV : V.IsStationaryIn (closedBall ξ R)ᶜ)
    (hcompact : IsCompact V.weight.support) :
    V.weight.support ⊆ closedBall ξ R := by
  apply HasGeneralizedMeanCurvatureIn.support_subset_closedBall_of_radial_lt hn hR
    ((V.hasGeneralizedMeanCurvature_zero_iff _).2 hV) hcompact
  filter_upwards with x
  simpa only [Pi.zero_apply, inner_zero_left, abs_zero] using
    (show (0 : ℝ) < n by exact_mod_cast hn)

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
