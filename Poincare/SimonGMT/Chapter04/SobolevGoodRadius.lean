module

public import Poincare.SimonGMT.Chapter04.CompactRadius
public import Poincare.SimonGMT.Chapter04.SobolevCovering

@[expose] public section

/-!
# Actual weighted good balls for Simon (5.7)

The finite-interval calculus lemma is applied to the genuine weighted
ball mass and energy. Its coefficient is deliberately nonsharp: four
times the coefficient printed in Simon's proof. No density limit or
bounded mean curvature is assumed.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
theorem monotone_ballIntegral_of_nonneg (μ : Measure E) (ξ : E)
    {q : E → ℝ} (hq : Integrable q μ) (hq0 : ∀ x, 0 ≤ q x) :
    Monotone (fun r : ℝ ↦ ∫ x in closedBall ξ r, q x ∂μ) := by
  intro r s hrs
  exact integral_mono_measure
    (Measure.restrict_mono (closedBall_subset_closedBall hrs) le_rfl)
    (Eventually.of_forall hq0) hq.restrict

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

/-- The radial first-variation error is bounded by the actual energy
distribution divided by `t^n`, on every positive finite interval. -/
theorem HasGeneralizedMeanCurvatureIn.weightedBall_energy_radius_inequality_compact
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hc : HasCompactSupport h) (hs : tsupport h ⊆ U)
    (hhnonneg : ∀ x, 0 ≤ h x) (ξ : E)
    {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) :
    (∫ x in closedBall ξ σ, h x ∂V.weight) / σ ^ n ≤
      (∫ x in closedBall ξ ρ, h x ∂V.weight) / ρ ^ n +
        ∫ t in σ..ρ, (∫ x in closedBall ξ t,
          ‖V.tangentialGradient h x‖ + h x * ‖H x‖ ∂V.weight) / t ^ n := by
  let q := fun x ↦ ‖V.tangentialGradient h x‖ + h x * ‖H x‖
  have hq0 : ∀ x, 0 ≤ q x := fun x ↦
    add_nonneg (norm_nonneg _) (mul_nonneg (hhnonneg x) (norm_nonneg _))
  have hq : Integrable q V.weight :=
    HasGeneralizedMeanCurvatureIn.integrable_weightedEnergy_of_hasCompactSupport
      (V := V) hH hU hh hc hs
  have hqr : Integrable (fun x ↦ ‖x - ξ‖ * q x) V.weight :=
    HasGeneralizedMeanCurvatureIn.integrable_radialWeightedEnergy_of_hasCompactSupport
      (V := V) hH hU hh hc hs ξ
  have hi := HasGeneralizedMeanCurvatureIn.weightedBall_radius_inequality_compact
    (V := V) hH hU hh hc hs hhnonneg ξ hσ hσρ
  apply hi.trans (add_le_add le_rfl ?_)
  apply intervalIntegral.integral_mono_on hσρ
    (intervalIntegrable_radiusQuotient_of_monotoneOn (n + 1)
      ((monotone_ballIntegral_of_nonneg V.weight ξ hqr
        (fun x ↦ mul_nonneg (norm_nonneg _) (hq0 x))).monotoneOn _) hσ hσρ)
    (intervalIntegrable_radiusQuotient_of_monotoneOn n
      ((monotone_ballIntegral_of_nonneg V.weight ξ hq hq0).monotoneOn _) hσ hσρ)
  intro t ht
  have ht0 := hσ.trans_le ht.1
  have hmass : (∫ x in closedBall ξ t, ‖x - ξ‖ * q x ∂V.weight) ≤
      t * ∫ x in closedBall ξ t, q x ∂V.weight := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hqr.restrict (hq.const_mul t).restrict measurableSet_closedBall
    intro x hx
    exact mul_le_mul_of_nonneg_right
      (by simpa only [mem_closedBall, dist_eq_norm] using hx) (hq0 x)
  calc
    _ ≤ (t * ∫ x in closedBall ξ t, q x ∂V.weight) / t ^ (n + 1) :=
      div_le_div_of_nonneg_right hmass (pow_pos ht0 _).le
    _ = _ := by rw [pow_succ]; dsimp only [q]; field_simp

/-- A good ball at a genuine approximate-tangent point of `{h ≥ 1}`.
All hypotheses are the geometric and regularity hypotheses used in (5.7).
In particular, positivity of the total mass is proved from lower density. -/
theorem HasGeneralizedMeanCurvatureIn.exists_weighted_goodRadius
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    (hn : 2 ≤ n) (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hc : HasCompactSupport h) (hs : tsupport h ⊆ U)
    (hhnonneg : ∀ x, 0 ≤ h x) {ξ : E} (hξ : ξ ∈ U)
    {P : Submodule ℝ E} (hP : Chapter03.HasApproximateTangentSpaceAt n V.carrier ξ P)
    (hvalue : 1 ≤ h ξ) :
    ∃ r : ℝ, 0 < r ∧
      r ≤ 2 * ((∫ x, h x ∂V.weight) /
        (Chapter01.realUnitBallVolume (n : ℝ)).toReal) ^ ((n : ℝ)⁻¹) ∧
      (∫ x in closedBall ξ (5 * r), h x ∂V.weight) ≤
        (4 * 5 ^ n * ((∫ x, h x ∂V.weight) /
          (Chapter01.realUnitBallVolume (n : ℝ)).toReal) ^ ((n : ℝ)⁻¹)) *
          ∫ x in closedBall ξ r, ‖V.tangentialGradient h x‖ + h x * ‖H x‖ ∂V.weight := by
  let ω := (Chapter01.realUnitBallVolume (n : ℝ)).toReal
  have hω : 0 < ω := ENNReal.toReal_pos
    (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)).ne'
    (Chapter01.realUnitBallVolume_ne_top _)
  let f : ℝ → ℝ := fun r ↦ (∫ x in closedBall ξ r, h x ∂V.weight) / ω
  let q := fun x ↦ ‖V.tangentialGradient h x‖ + h x * ‖H x‖
  let g : ℝ → ℝ := fun r ↦ (∫ x in closedBall ξ r, q x ∂V.weight) / ω
  let M := (∫ x, h x ∂V.weight) / ω
  have hhi : Integrable h V.weight :=
    (contDiff_of_tsupport_subset hU hh hs).continuous.integrable_of_hasCompactSupport hc
  have hq : Integrable q V.weight :=
    HasGeneralizedMeanCurvatureIn.integrable_weightedEnergy_of_hasCompactSupport
      (V := V) hH hU hh hc hs
  have hq0 : ∀ x, 0 ≤ q x := fun x ↦
    add_nonneg (norm_nonneg _) (mul_nonneg (hhnonneg x) (norm_nonneg _))
  have hfbound : ∀ r : ℝ, 0 < r → f r ≤ M := by
    intro r _
    exact div_le_div_of_nonneg_right
      (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hhnonneg) hhi) hω.le
  have hlower : ∀ᶠ r : ℝ in 𝓝[>] 0, (1 / 2 : ℝ) < f r / r ^ n := by
    simpa only [f, weightedBallAverage, div_div] using
      V.eventually_lt_weightedBallAverage_of_one_le_value hU (by omega) hθ
        hh.continuousOn hξ hP hvalue (by norm_num : (1 / 2 : ℝ) < 1)
  have hM : 0 < M := by
    obtain ⟨r, hr, hr0⟩ := (hlower.and self_mem_nhdsWithin).exists
    have hrpos : 0 < r := hr0
    have hfr : 0 < f r := (div_pos_iff_of_pos_right (pow_pos hrpos n)).mp
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr)
    exact hfr.trans_le (hfbound r hrpos)
  have hg : MonotoneOn g (Ioi 0) := by
    intro r _ s _ hrs
    exact div_le_div_of_nonneg_right
      (monotone_ballIntegral_of_nonneg V.weight ξ hq hq0 hrs) hω.le
  have hineq : ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ →
      f σ / σ ^ n ≤ f ρ / ρ ^ n + ∫ t in σ..ρ, g t / t ^ n := by
    intro σ ρ hσ hσρ
    have hi := div_le_div_of_nonneg_right
      (HasGeneralizedMeanCurvatureIn.weightedBall_energy_radius_inequality_compact
        (V := V) hH hU hh hc hs hhnonneg ξ hσ hσρ) hω.le
    rw [add_div, ← intervalIntegral.integral_div] at hi
    simpa only [f, g, q, div_div, mul_comm _ ω] using hi
  obtain ⟨r, hr0, hrM, hr⟩ := exists_goodRadius_of_finite_interval_inequality n hn f g
    hM hfbound hg hlower hineq
  refine ⟨r, hr0, hrM, ?_⟩
  change (_ / ω) ≤ _ * (_ / ω) at hr
  rw [← mul_div_assoc] at hr
  exact (div_le_div_iff_of_pos_right hω).mp hr

/-- The superlevel estimate at the end of the covering argument on
printed page 99. The approximate tangent exists only almost everywhere;
the covering theorem removes that exceptional set. The coefficient is
four times the printed coefficient, as in the corrected calculus lemma. -/
theorem HasGeneralizedMeanCurvatureIn.weighted_superlevel_integral_le
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    (hn : 2 ≤ n) (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hc : HasCompactSupport h) (hs : tsupport h ⊆ U)
    (hhnonneg : ∀ x, 0 ≤ h x) :
    (∫ x in {x | 1 ≤ h x}, h x ∂V.weight) ≤
      (4 * 5 ^ n * ((∫ x, h x ∂V.weight) /
        (Chapter01.realUnitBallVolume (n : ℝ)).toReal) ^ ((n : ℝ)⁻¹)) *
        ∫ x, ‖V.tangentialGradient h x‖ + h x * ‖H x‖ ∂V.weight := by
  let M := (∫ x, h x ∂V.weight) / (Chapter01.realUnitBallVolume (n : ℝ)).toReal
  let C := 4 * 5 ^ n * M ^ ((n : ℝ)⁻¹)
  let q := fun x ↦ ‖V.tangentialGradient h x‖ + h x * ‖H x‖
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg
      (div_nonneg (integral_nonneg hhnonneg) ENNReal.toReal_nonneg) _)
  have hh' := contDiff_of_tsupport_subset hU hh hs
  have hhi : Integrable h V.weight := hh'.continuous.integrable_of_hasCompactSupport hc
  have hq : Integrable q V.weight :=
    HasGeneralizedMeanCurvatureIn.integrable_weightedEnergy_of_hasCompactSupport
      (V := V) hH hU hh hc hs
  have hq0 : ∀ x, 0 ≤ q x := fun x ↦
    add_nonneg (norm_nonneg _) (mul_nonneg (hhnonneg x) (norm_nonneg _))
  have hA : MeasurableSet {x | 1 ≤ h x} :=
    (isClosed_le continuous_const hh'.continuous).measurableSet
  have hgood : ∀ᵐ ξ ∂V.weight, ξ ∈ {x | 1 ≤ h x} → ∃ r : ℝ,
      0 < r ∧ r ≤ 2 * M ^ ((n : ℝ)⁻¹) ∧
        (∫⁻ x in closedBall ξ (5 * r), ENNReal.ofReal (h x) ∂V.weight) ≤
          ENNReal.ofReal C * ∫⁻ x in closedBall ξ r, ENNReal.ofReal (q x) ∂V.weight := by
    filter_upwards [V.ae_weight_of_ae_restrict V.approximate_tangent] with ξ hξ hvalue
    have hξU : ξ ∈ U := hs (subset_tsupport h (by
      change h ξ ≠ 0
      change 1 ≤ h ξ at hvalue
      linarith))
    obtain ⟨r, hr0, hrM, hr⟩ := HasGeneralizedMeanCurvatureIn.exists_weighted_goodRadius
      (V := V) hH hU hn hθ hh hc hs hhnonneg hξU hξ hvalue
    refine ⟨r, hr0, hrM, ?_⟩
    have hr' := ENNReal.ofReal_le_ofReal hr
    change ENNReal.ofReal _ ≤ ENNReal.ofReal (C * _) at hr'
    rwa [ENNReal.ofReal_mul hC,
      ofReal_integral_eq_lintegral_ofReal hhi.restrict (Eventually.of_forall hhnonneg),
      ofReal_integral_eq_lintegral_ofReal hq.restrict (Eventually.of_forall hq0)] at hr'
  have hle := lintegral_le_of_ae_exists_good_radius V.weight _ hA
    (fun x ↦ ENNReal.ofReal (h x)) (fun x ↦ ENNReal.ofReal (q x)) hgood
  rw [← ofReal_integral_eq_lintegral_ofReal hhi.restrict (Eventually.of_forall hhnonneg),
    ← ofReal_integral_eq_lintegral_ofReal hq (Eventually.of_forall hq0),
    ← ENNReal.ofReal_mul hC] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (integral_nonneg hq0))).mp hle

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
