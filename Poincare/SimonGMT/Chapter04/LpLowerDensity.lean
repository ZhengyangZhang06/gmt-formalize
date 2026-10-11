module

public import Poincare.SimonGMT.Chapter04.LpDensity
public import Poincare.SimonGMT.Chapter04.LowerDensityTangents

@[expose] public section

/-!
# Local uniform lower density under local `Lᵖ` mean curvature

This proves the lower mass bound used in Simon 4.6.3. Its centers are
explicitly localized near the fixed interior point, as required when the
curvature is only locally `Lᵖ`.
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

theorem HasGeneralizedMeanCurvatureIn.one_le_stationaryDensityReal_ae_lp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    (hU : IsOpen U) (hn : 0 < n) {p : ℝ} (hpn : (n : ℝ) < p)
    (hLp : ∀ K : Set E, IsCompact K → K ⊆ U → MemLp H (ENNReal.ofReal p) (V.weight.restrict K))
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x) :
    ∀ᵐ ξ ∂V.weight.restrict U, 1 ≤ V.stationaryDensityReal ξ := by
  rw [ae_restrict_iff' hU.measurableSet]
  filter_upwards [V.ae_weight_of_ae_restrict V.approximate_tangent] with ξ hξ hξU
  exact V.one_le_density_of_approximateTangent hU hn hθ hξU hξ
    (HasGeneralizedMeanCurvatureIn.tendsto_densityQuotient_real_lp (V := V) hH hpn hU hLp hξU)

theorem HasGeneralizedMeanCurvatureIn.one_le_stationaryDensityReal_of_mem_support_lp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    (hU : IsOpen U) (hn : 0 < n) {p : ℝ} (hpn : (n : ℝ) < p)
    (hLp : ∀ K : Set E, IsCompact K → K ⊆ U → MemLp H (ENNReal.ofReal p) (V.weight.restrict K))
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    {ξ : E} (hξ : ξ ∈ U) (hsupp : ξ ∈ V.weight.support) :
    1 ≤ V.stationaryDensityReal ξ := by
  by_contra hnot
  have hlt : V.stationaryDensityReal ξ < 1 := lt_of_not_ge hnot
  have hupper := HasGeneralizedMeanCurvatureIn.upperSemicontinuousOn_stationaryDensityReal_lp
    (V := V) hH hpn hU hLp ξ hξ 1 hlt
  rw [hU.nhdsWithin_eq hξ] at hupper
  have hneigh : {x | V.stationaryDensityReal x < 1 ∧ x ∈ U} ∈ 𝓝 ξ :=
    hupper.and (hU.mem_nhds hξ)
  have hpos := (Measure.mem_support_iff_forall (μ := V.weight) ξ).mp hsupp _ hneigh
  have hae := hH.one_le_stationaryDensityReal_ae_lp hU hn hpn hLp hθ
  rw [ae_restrict_iff' hU.measurableSet] at hae
  have hzero : V.weight {x | V.stationaryDensityReal x < 1 ∧ x ∈ U} = 0 := by
    apply measure_mono_null (t := {x | ¬ (x ∈ U → 1 ≤ V.stationaryDensityReal x)})
    · intro x hx hgood
      exact (not_le_of_gt hx.1) (hgood hx.2)
    · exact ae_iff.mp hae
  exact hpos.ne' hzero

/-- The local version of (6.3)(1): one radius controls every nearby
support center and every smaller positive scale. -/
theorem HasGeneralizedMeanCurvatureIn.exists_uniform_lower_ball_mass_lp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    (hU : IsOpen U) (hn : 0 < n) {p : ℝ} (hpn : (n : ℝ) < p)
    (hLp : ∀ K : Set E, IsCompact K → K ⊆ U → MemLp H (ENNReal.ofReal p) (V.weight.restrict K))
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    {x : E} (hx : x ∈ U) :
    ∃ R : ℝ, 0 < R ∧ closedBall x (2 * R) ⊆ U ∧
      ∀ ξ ∈ V.weight.support ∩ closedBall x R, ∀ r : ℝ, 0 < r → r ≤ R →
        (Chapter01.realUnitBallVolume (n : ℝ)).toReal / 2 * r ^ n ≤
          V.weight.real (closedBall ξ r) := by
  obtain ⟨S, hS, hSU⟩ := exists_pos_closedBall_subset hU hx
  have hp : 1 < p := lt_of_le_of_lt (by exact_mod_cast (Nat.succ_le_iff.mpr hn)) hpn
  have hLpS := hLp _ (isCompact_closedBall x S) hSU
  let ω := (Chapter01.realUnitBallVolume (n : ℝ)).toReal
  have hω : 0 < ω := ENNReal.toReal_pos
    (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)).ne'
    (Chapter01.realUnitBallVolume_ne_top _)
  let Λ := V.scaledLpMeanCurvature x H p S / lpMeanCurvatureKappa n p
  have hscale : V.scaledLpMeanCurvature x H p S ≤ lpMeanCurvatureKappa n p * Λ := by
    dsimp [Λ]
    rw [mul_div_cancel₀ _ (lpMeanCurvatureKappa_pos hpn).ne']
  have hlim : Tendsto (fun r ↦ lpMonotonicityFactor n p (S / 2) Λ r * (ω / 2 + 1))
      (𝓝[>] 0) (𝓝 (ω / 2 + 1)) := by
    simpa only [one_mul] using
      (tendsto_lpMonotonicityFactor (n := n) (R := S / 2) hpn Λ).mul_const (ω / 2 + 1)
  obtain ⟨δ, hδ, hδgood⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hlim.eventually (gt_mem_nhds (show ω / 2 + 1 < ω + 1 by linarith)))
  let R := min (S / 2) (δ / 2)
  have hR : 0 < R := lt_min (half_pos hS) (half_pos hδ)
  have hRS : R ≤ S / 2 := min_le_left _ _
  have hRδ : R < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  refine ⟨R, hR, (closedBall_subset_closedBall (by linarith)).trans hSU, ?_⟩
  intro ξ hξ r hr hrR
  have hξS : closedBall ξ (S / 2) ⊆ closedBall x S := by
    apply closedBall_subset_closedBall'
    have hdist : dist ξ x ≤ R := hξ.2
    linarith
  have hξU : ξ ∈ U := hSU (hξS (mem_closedBall_self (half_pos hS).le))
  have hLpξ := hLpS.mono_measure (Measure.restrict_mono hξS le_rfl)
  have hscaleξ : V.scaledLpMeanCurvature ξ H p (S / 2) ≤ lpMeanCurvatureKappa n p * Λ :=
    (V.scaledLpMeanCurvature_mono_ball hpn (half_pos hS).le
      (half_le_self hS.le) hξS hLpS).trans hscale
  have hd := hH.one_le_stationaryDensityReal_of_mem_support_lp hU hn hpn hLp hθ hξU hξ.1
  have hωd : ω ≤ (V.lowerDensityMassRatio ξ).toReal := by
    simp only [stationaryDensityReal, stationaryDensity, ENNReal.toReal_div] at hd
    change 1 ≤ (V.lowerDensityMassRatio ξ).toReal / ω at hd
    simpa only [one_mul] using (le_div_iff₀ hω).mp hd
  have hmon := HasGeneralizedMeanCurvatureIn.lowerDensityMassRatio_toReal_le_lp_correctedBallMass
    (V := V) hH ξ hp hpn (half_pos hS) (hξS.trans hSU) hLpξ hscaleξ hr (hrR.trans hRS)
  have hfactor := hδgood (show r ∈ Ioo 0 δ from ⟨hr, hrR.trans_lt hRδ⟩)
  change lpMonotonicityFactor n p (S / 2) Λ r * (ω / 2 + 1) < ω + 1 at hfactor
  have hfpos : 0 < lpMonotonicityFactor n p (S / 2) Λ r := Real.exp_pos _
  have hquot : ω / 2 ≤ V.weight.real (closedBall ξ r) / r ^ n := by
    by_contra hnot
    have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge hnot) hfpos
    dsimp only [lpMonotonicityError] at hmon
    nlinarith
  exact (le_div_iff₀ (pow_pos hr n)).mp hquot

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
