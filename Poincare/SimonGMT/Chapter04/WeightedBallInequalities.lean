module

public import Poincare.SimonGMT.Chapter04.RadialPotential
public import Poincare.SimonGMT.Chapter04.WeightedBoundedIntegration

@[expose] public section

/-!
# Simon Chapter 4, weighted ball inequalities (5.4)--(5.5)

The source's exact constants, ball radii, and local `C¹` hypotheses are
retained. The singular errors are nonnegative extended integrals: no
extra finiteness hypothesis or default-zero Bochner integral is used.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ}

theorem ofReal_normalized_radius_energy_le_potential (μ : Measure E) [SFinite μ]
    (ξ : E) (hn : 0 < n) {σ ρ ω : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hω : 0 ≤ ω)
    {q : E → ℝ} (hq : IntegrableOn q (closedBall ξ ρ) μ)
    (hq0 : ∀ x ∈ closedBall ξ ρ, 0 ≤ q x) :
    ENNReal.ofReal ((∫ t in σ..ρ,
      (∫ x in closedBall ξ t, ‖x - ξ‖ * q x ∂μ) / t ^ (n + 1)) / ω) ≤
      ENNReal.ofReal (1 / ((n : ℝ) * ω)) *
        ∫⁻ x in closedBall ξ ρ, ENNReal.ofReal (q x / ‖x - ξ‖ ^ (n - 1)) ∂μ := by
  let R := ∫ t in σ..ρ, (∫ x in closedBall ξ t, ‖x - ξ‖ * q x ∂μ) / t ^ (n + 1)
  let P := ∫⁻ x in closedBall ξ ρ, ENNReal.ofReal (q x / ‖x - ξ‖ ^ (n - 1)) ∂μ
  have hR : ENNReal.ofReal R ≤ ENNReal.ofReal ((n : ℝ)⁻¹) * P := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simpa only [R, P, Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.add_assoc] using
      ofReal_radius_energy_le_potential μ ξ m hσ hσρ hq hq0
  change ENNReal.ofReal (R / ω) ≤ ENNReal.ofReal (1 / ((n : ℝ) * ω)) * P
  calc
    _ = ENNReal.ofReal ω⁻¹ * ENNReal.ofReal R := by
      rw [div_eq_mul_inv, ENNReal.ofReal_mul' (inv_nonneg.mpr hω), mul_comm]
    _ ≤ ENNReal.ofReal ω⁻¹ * (ENNReal.ofReal ((n : ℝ)⁻¹) * P) := by gcongr
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hω)]
      congr 2
      simp only [one_div, mul_inv_rev]

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

/-- The normalized weighted ball integral used on both sides of
Simon (5.4)--(5.5). The normalizing constant is the book's `ωₙ`. -/
def weightedBallAverage (ξ : E) (h : E → ℝ) (ρ : ℝ) : ℝ :=
  (∫ x in closedBall ξ ρ, h x ∂V.weight) /
    ((Chapter01.realUnitBallVolume (n : ℝ)).toReal * ρ ^ n)

/-- The potential in (5.4)--(5.5). It is extended-valued so a divergent
error makes the inequality trivial, not falsely stronger. -/
def radialWeightedPotential (ξ : E) (q : E → ℝ) (ρ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in closedBall ξ ρ, ENNReal.ofReal (q x / ‖x - ξ‖ ^ (n - 1)) ∂V.weight

theorem weightedBallAverage_nonneg (ξ : E) {h : E → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hh : ∀ x ∈ closedBall ξ ρ, 0 ≤ h x) : 0 ≤ V.weightedBallAverage ξ h ρ := by
  apply div_nonneg ?_ (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hρ _))
  apply setIntegral_nonneg measurableSet_closedBall hh

/-- Simon (5.5), with the literal singular error, arbitrary locally
integrable generalized curvature, and no finiteness assumption on the
error. Equality of the two positive radii is also allowed. -/
theorem HasGeneralizedMeanCurvatureIn.weightedBall_le_potential
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    (hn : 0 < n) {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U)
    (hhnonneg : ∀ x ∈ U, 0 ≤ h x) (ξ : E)
    {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hball : closedBall ξ ρ ⊆ U) :
    ENNReal.ofReal (V.weightedBallAverage ξ h σ) ≤
      ENNReal.ofReal (V.weightedBallAverage ξ h ρ) +
        ENNReal.ofReal (1 / ((n : ℝ) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal)) *
          V.radialWeightedPotential ξ (fun x ↦ ‖V.tangentialGradient h x‖ + h x * ‖H x‖) ρ := by
  let ω := (Chapter01.realUnitBallVolume (n : ℝ)).toReal
  let q := fun x ↦ ‖V.tangentialGradient h x‖ + h x * ‖H x‖
  let R := ∫ t in σ..ρ, (∫ x in closedBall ξ t, ‖x - ξ‖ * q x ∂V.weight) / t ^ (n + 1)
  have hq := HasGeneralizedMeanCurvatureIn.integrableOn_weightedEnergy (V := V) hH hU hh
    (isCompact_closedBall ξ ρ) hball
  have hq0 : ∀ x ∈ closedBall ξ ρ, 0 ≤ q x := fun x hx ↦
    add_nonneg (norm_nonneg _) (mul_nonneg (hhnonneg x (hball hx)) (norm_nonneg _))
  have hR : ENNReal.ofReal (R / ω) ≤ ENNReal.ofReal (1 / ((n : ℝ) * ω)) *
      V.radialWeightedPotential ξ q ρ :=
    ofReal_normalized_radius_energy_le_potential V.weight ξ hn hσ hσρ ENNReal.toReal_nonneg hq hq0
  have hb : V.weightedBallAverage ξ h σ ≤ V.weightedBallAverage ξ h ρ + R / ω := by
    have hs := div_le_div_of_nonneg_right
      (HasGeneralizedMeanCurvatureIn.weightedBall_radius_inequality
        (V := V) hH hU hh hhnonneg ξ hσ hσρ hball) (show 0 ≤ ω from ENNReal.toReal_nonneg)
    convert hs using 1 <;> dsimp only [weightedBallAverage, R, q, ω] <;> ring
  exact ((ENNReal.ofReal_le_ofReal hb).trans ENNReal.ofReal_add_le).trans (add_le_add le_rfl hR)

/-- Simon (5.4), derived from the corrected radial curvature estimate
(5.2). The exponential and singular-kernel constants are exactly those
printed in (5.4), and the singular gradient integral may be infinite. -/
theorem HasGeneralizedMeanCurvatureIn.weightedBall_le_potential_of_bounded
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    (hn : 0 < n) {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U)
    (hhnonneg : ∀ x ∈ U, 0 ≤ h x) (ξ : E)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ)
    {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hball : closedBall ξ ρ ⊆ U) :
    ENNReal.ofReal (V.weightedBallAverage ξ h σ) ≤ ENNReal.ofReal (Real.exp (Λ * ρ)) *
      (ENNReal.ofReal (V.weightedBallAverage ξ h ρ) +
        ENNReal.ofReal (1 / ((n : ℝ) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal)) *
          V.radialWeightedPotential ξ (fun x ↦ ‖V.tangentialGradient h x‖) ρ) := by
  let ω := (Chapter01.realUnitBallVolume (n : ℝ)).toReal
  let q := fun x ↦ ‖V.tangentialGradient h x‖
  let R := ∫ t in σ..ρ, (∫ x in closedBall ξ t, ‖x - ξ‖ * q x ∂V.weight) / t ^ (n + 1)
  have hq := V.integrableOn_norm_tangentialGradient hU hh (isCompact_closedBall ξ ρ) hball
  have hR : ENNReal.ofReal (R / ω) ≤ ENNReal.ofReal (1 / ((n : ℝ) * ω)) *
      V.radialWeightedPotential ξ q ρ :=
    ofReal_normalized_radius_energy_le_potential V.weight ξ hn hσ hσρ ENNReal.toReal_nonneg hq
      (fun x _ ↦ norm_nonneg _)
  have hb : V.weightedBallAverage ξ h σ ≤
      Real.exp (Λ * ρ) * (V.weightedBallAverage ξ h ρ + R / ω) := by
    have hs := div_le_div_of_nonneg_right
      (HasGeneralizedMeanCurvatureIn.weightedBall_bounded_radius_inequality
        (V := V) hH hU hh hhnonneg ξ hΛ hbound hσ hσρ hball)
      (show 0 ≤ ω from ENNReal.toReal_nonneg)
    convert hs using 1 <;> dsimp only [weightedBallAverage, R, q, ω] <;> ring
  apply (ENNReal.ofReal_le_ofReal hb).trans
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hs : ENNReal.ofReal (V.weightedBallAverage ξ h ρ + R / ω) ≤
      ENNReal.ofReal (V.weightedBallAverage ξ h ρ) +
        ENNReal.ofReal (1 / ((n : ℝ) * ω)) * V.radialWeightedPotential ξ q ρ :=
    ENNReal.ofReal_add_le.trans (add_le_add le_rfl hR)
  exact mul_le_mul_right hs _

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
