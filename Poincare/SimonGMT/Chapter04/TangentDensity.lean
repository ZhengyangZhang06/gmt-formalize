module

public import Poincare.SimonGMT.Chapter04.WeightedDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import all Poincare.SimonGMT.Chapter03.Rectifiable

@[expose] public section

/-!
# Approximate tangent planes and the lower density needed in (5.6)

The geometric comparison uses the actual blow-up map in Chapter 3,
Hausdorff scaling, and the Euclidean volume of a unit ball in the plane.
-/

open Filter Function Metric Set MeasureTheory
open scoped CompactlySupported ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

private theorem blowUpMap_apply (ξ : E) (r : ℝ) (x : E) :
    Chapter03.blowUpMap ξ r x = r⁻¹ • (x - ξ) := rfl

theorem hausdorff_blowUp_image (ξ : E) {r : ℝ} (hr : 0 < r) (S : Set E) :
    (Measure.euclideanHausdorffMeasure n) (Chapter03.blowUpMap ξ r '' S) =
      ENNReal.ofReal (r⁻¹) ^ n * (Measure.euclideanHausdorffMeasure n) S := by
  have hshift : Isometry (fun y : E ↦ y - ξ) := by
    apply Isometry.of_dist_eq
    intro x y
    simp only [dist_eq_norm]
    congr 1
    abel
  have himage : Chapter03.blowUpMap ξ r '' S =
      AffineMap.homothety (0 : E) r⁻¹ '' ((fun y : E ↦ y - ξ) '' S) := by
    rw [← image_comp]
    congr 1
    funext y
    simp [blowUpMap_apply, AffineMap.homothety_apply]
  rw [himage, euclideanHausdorffMeasure_homothety_image n (0 : E) (inv_ne_zero hr.ne'),
    hshift.euclideanHausdorffMeasure_image]
  simp only [ENNReal.smul_def, ENNReal.coe_pow]
  congr 2
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm,
    Real.norm_of_nonneg (inv_pos.mpr hr).le]

theorem blowUp_image_inter_closedBall (ξ : E) {r A : ℝ} (hr : 0 < r) (S : Set E) :
    Chapter03.blowUpMap ξ r '' (closedBall ξ (r * A) ∩ S) =
      closedBall (0 : E) A ∩ (Chapter03.blowUpMap ξ r '' S) := by
  have hmem : ∀ x : E, Chapter03.blowUpMap ξ r x ∈ closedBall (0 : E) A ↔
      x ∈ closedBall ξ (r * A) := by
    intro x
    simp only [mem_closedBall, dist_eq_norm, sub_zero, blowUpMap_apply, norm_smul,
      Real.norm_of_nonneg (inv_pos.mpr hr).le]
    rw [← div_eq_inv_mul, div_le_iff₀ hr]
    rw [mul_comm r A]
  ext y
  constructor
  · rintro ⟨x, ⟨hxB, hxS⟩, rfl⟩
    exact ⟨(hmem x).mpr hxB, mem_image_of_mem _ hxS⟩
  · rintro ⟨hyB, x, hxS, rfl⟩
    exact ⟨x, ⟨(hmem x).mp hyB, hxS⟩, rfl⟩

theorem hausdorff_blowUp_ball (ξ : E) {r A : ℝ} (hr : 0 < r) (S : Set E) :
    (Measure.euclideanHausdorffMeasure n)
      (closedBall (0 : E) A ∩ (Chapter03.blowUpMap ξ r '' S)) =
      ENNReal.ofReal (r⁻¹) ^ n * (Measure.euclideanHausdorffMeasure n) (closedBall ξ (r * A) ∩ S) := by
  rw [← blowUp_image_inter_closedBall ξ hr S, hausdorff_blowUp_image ξ hr]

theorem locallyFinite_planeMeasure {P : Submodule ℝ E} (hP : Module.finrank ℝ P = n) :
    IsLocallyFiniteMeasure ((Measure.euclideanHausdorffMeasure n).restrict (P : Set E)) := by
  have hrange : range (P.subtypeₗᵢ : P → E) = (P : Set E) := by ext x; simp
  have hmap : (Measure.euclideanHausdorffMeasure n : Measure P).map (P.subtypeₗᵢ : P → E) =
      (Measure.euclideanHausdorffMeasure n).restrict (P : Set E) := by
    rw [← hrange]
    exact P.subtypeₗᵢ.isometry.map_euclideanHausdorffMeasure
  letI : IsFiniteMeasureOnCompacts ((Measure.euclideanHausdorffMeasure n).restrict (P : Set E)) := by
    constructor
    intro K hK
    rw [← hmap, Measure.map_apply P.subtypeₗᵢ.continuous.measurable hK.measurableSet]
    letI : IsFiniteMeasureOnCompacts (Measure.euclideanHausdorffMeasure n : Measure P) := by
      rw [← hP]
      infer_instance
    exact (P.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isCompact_preimage hK).measure_lt_top
  infer_instance

theorem planeMeasure_unit_closedBall (hn : 0 < n) {P : Submodule ℝ E}
    (hP : Module.finrank ℝ P = n) :
    ((Measure.euclideanHausdorffMeasure n).restrict (P : Set E)) (closedBall (0 : E) 1) =
      Chapter01.realUnitBallVolume (n : ℝ) := by
  letI : Nontrivial P := Module.nontrivial_of_finrank_pos (hP.symm ▸ hn)
  have hrange : range (P.subtypeₗᵢ : P → E) = (P : Set E) := by ext x; simp
  rw [← hrange, ← P.subtypeₗᵢ.isometry.map_euclideanHausdorffMeasure,
    Measure.map_apply P.subtypeₗᵢ.continuous.measurable measurableSet_closedBall]
  have hpre : (P.subtypeₗᵢ : P → E) ⁻¹' closedBall (0 : E) 1 = closedBall (0 : P) 1 := by
    ext x
    simp [mem_closedBall, dist_eq_norm]
  rw [hpre, ← hP, InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
    InnerProductSpace.volume_closedBall, hP, ENNReal.ofReal_one, one_pow, one_mul,
    Chapter01.realUnitBallVolume_eq]
  congr 2
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
  congr 1
  ring

open RectifiableVarifold

/-- A continuous compact test function equal to one on the unit ball,
with values in `[0,1]` and support in the ball of radius `1+ε`. -/
def tangentDensityCutoff (ε : ℝ) (hε : 0 < ε) : C_c(E, ℝ) where
  toFun x := monotonicityCutoff ε (‖x - 0‖ ^ 2)
  continuous_toFun := (contDiff_monotonicityCutoff ε).continuous.comp
    ((continuous_id.sub continuous_const).norm.pow 2)
  hasCompactSupport' := hasCompactSupport_squaredRadialScalar (0 : E)
    (by linarith : 0 ≤ 1 + ε) (monotonicityCutoff_cutoff hε)

theorem tangentDensityCutoff_mem_Icc {ε : ℝ} (hε : 0 < ε) (x : E) :
    tangentDensityCutoff ε hε x ∈ Icc 0 1 :=
  monotonicityCutoff_mem_Icc ε _

theorem tangentDensityCutoff_eq_one {ε : ℝ} (hε : 0 < ε) {x : E}
    (hx : x ∈ closedBall (0 : E) 1) : tangentDensityCutoff ε hε x = 1 := by
  apply monotonicityCutoff_one hε
  have hx' : ‖x - 0‖ ≤ 1 := by simpa [mem_closedBall, dist_eq_norm] using hx
  nlinarith [norm_nonneg (x - 0)]

theorem tangentDensityCutoff_eq_zero {ε : ℝ} (hε : 0 < ε) {x : E}
    (hx : x ∉ closedBall (0 : E) (1 + ε)) : tangentDensityCutoff ε hε x = 0 := by
  apply monotonicityCutoff_cutoff hε
  have hx' : 1 + ε < ‖x - 0‖ := by simpa [mem_closedBall, dist_eq_norm] using hx
  nlinarith [norm_nonneg (x - 0)]

theorem unitBallVolume_le_integral_tangentDensityCutoff (hn : 0 < n)
    {P : Submodule ℝ E} (hP : Module.finrank ℝ P = n) {ε : ℝ} (hε : 0 < ε) :
    (Chapter01.realUnitBallVolume (n : ℝ)).toReal ≤
      ∫ x in (P : Set E), tangentDensityCutoff ε hε x
        ∂Measure.euclideanHausdorffMeasure n := by
  letI := locallyFinite_planeMeasure hP
  have hle := setIntegral_le_integral (s := closedBall (0 : E) 1)
    ((tangentDensityCutoff (E := E) ε hε).integrable
      (μ := (Measure.euclideanHausdorffMeasure n).restrict (P : Set E)))
    (Eventually.of_forall (fun x ↦ (tangentDensityCutoff_mem_Icc hε x).1))
  have heq : (∫ x in closedBall (0 : E) 1, tangentDensityCutoff ε hε x
      ∂(Measure.euclideanHausdorffMeasure n).restrict (P : Set E)) =
      (Chapter01.realUnitBallVolume (n : ℝ)).toReal := by
    rw [setIntegral_congr_fun measurableSet_closedBall
      (fun x hx ↦ tangentDensityCutoff_eq_one hε hx)]
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ,
      planeMeasure_unit_closedBall hn hP]
  rwa [heq] at hle

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

/-- Comparison of a bounded compact blow-up test with the actual varifold
mass. The source multiplicity assumption is used as a measure inequality. -/
theorem integral_blowUp_le_scaled_weight {U : Set E} (hU : MeasurableSet U)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    (ξ : E) {r A : ℝ} (hr : 0 < r) (hball : closedBall ξ (r * A) ⊆ U)
    (f : E → ℝ) (hf : ∀ x, f x ∈ Icc 0 1)
    (hsupp : ∀ x, x ∉ closedBall (0 : E) A → f x = 0) :
    (∫ x in Chapter03.blowUpMap ξ r '' V.carrier, f x
      ∂Measure.euclideanHausdorffMeasure n) ≤
        r⁻¹ ^ n * V.weight.real (closedBall ξ (r * A)) := by
  let ν := (Measure.euclideanHausdorffMeasure n).restrict
    (Chapter03.blowUpMap ξ r '' V.carrier)
  have hmass := V.carrierMeasure_restrict_le_weight_restrict hU hθ
    (closedBall ξ (r * A))
  rw [Measure.restrict_apply measurableSet_closedBall,
    Measure.restrict_apply measurableSet_closedBall, inter_eq_left.mpr hball,
    Measure.restrict_apply measurableSet_closedBall] at hmass
  have hfinite : (Measure.euclideanHausdorffMeasure n)
      (closedBall ξ (r * A) ∩ V.carrier) < ∞ :=
    hmass.trans_lt (isCompact_closedBall ξ (r * A)).measure_lt_top
  have hscale : ν (closedBall (0 : E) A) = ENNReal.ofReal (r⁻¹) ^ n *
      (Measure.euclideanHausdorffMeasure n) (closedBall ξ (r * A) ∩ V.carrier) := by
    dsimp only [ν]
    rw [Measure.restrict_apply measurableSet_closedBall, hausdorff_blowUp_ball ξ hr]
  have hνfinite : ν (closedBall (0 : E) A) < ∞ := by
    rw [hscale]
    exact ENNReal.mul_lt_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top).lt_top hfinite
  have hnorm := norm_setIntegral_le_of_norm_le_const_ae (f := f) hνfinite
    (Eventually.of_forall (fun x ↦ show ‖f x‖ ≤ 1 by
      rw [Real.norm_of_nonneg (hf x).1]
      exact (hf x).2))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, one_mul] at hnorm
  have hreal : ν.real (closedBall (0 : E) A) ≤
      r⁻¹ ^ n * V.weight.real (closedBall ξ (r * A)) := by
    rw [measureReal_def, hscale, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (inv_pos.mpr hr).le]
    exact mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (isCompact_closedBall ξ (r * A)).measure_lt_top.ne hmass)
      (pow_nonneg (inv_pos.mpr hr).le n)
  exact (le_abs_self _).trans (hnorm.trans hreal)

/-- At an actual approximate-tangent point, `θ≥1` forces every existing
finite normalized weight density to be at least one. No density/multiplicity
identity is assumed. -/
theorem one_le_density_of_approximateTangent {U : Set E} (hU : IsOpen U)
    (hn : 0 < n) (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    {ξ : E} (hξ : ξ ∈ U) {P : Submodule ℝ E}
    (hP : Chapter03.HasApproximateTangentSpaceAt n V.carrier ξ P) {d : ℝ}
    (hd : Tendsto (fun r ↦ V.weight.real (closedBall ξ r) /
      ((Chapter01.realUnitBallVolume (n : ℝ)).toReal * r ^ n))
      (𝓝[>] (0 : ℝ)) (𝓝 d)) : 1 ≤ d := by
  let ω := (Chapter01.realUnitBallVolume (n : ℝ)).toReal
  have hω : 0 < ω := ENNReal.toReal_pos
    (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)).ne'
    (Chapter01.realUnitBallVolume_ne_top _)
  obtain ⟨R, hR, hBR⟩ := exists_pos_closedBall_subset hU hξ
  have hall : ∀ ε : ℝ, 0 < ε → ω ≤ (1 + ε) ^ n * ω * d := by
    intro ε hε
    let A := 1 + ε
    have hA : 0 < A := by dsimp [A]; linarith
    have hrA : Tendsto (fun r : ℝ ↦ r * A) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa only [zero_mul, id_eq] using
          (tendsto_id.mono_left inf_le_left : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0)).mul_const A
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact mul_pos hr hA
    have hscale : Tendsto (fun r ↦ r⁻¹ ^ n * V.weight.real (closedBall ξ (r * A)))
        (𝓝[>] (0 : ℝ)) (𝓝 (A ^ n * ω * d)) := by
      apply ((hd.comp hrA).const_mul (A ^ n * ω)).congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [Function.comp_apply, mul_pow]
      change A ^ n * ω * (V.weight.real (closedBall ξ (r * A)) /
        (ω * (r ^ n * A ^ n))) = r⁻¹ ^ n * V.weight.real (closedBall ξ (r * A))
      simp only [inv_pow]
      field_simp [hr.ne', hA.ne', hω.ne']
    have hcut := hP.2 (tangentDensityCutoff (E := E) ε hε)
    have hle : (∫ x in (P : Set E), tangentDensityCutoff ε hε x
        ∂Measure.euclideanHausdorffMeasure n) ≤ A ^ n * ω * d := by
      apply le_of_tendsto_of_tendsto hcut hscale
      filter_upwards [Ioc_mem_nhdsGT (div_pos hR hA)] with r hr
      have hrA' : r * A ≤ R := (le_div_iff₀ hA).mp hr.2
      exact V.integral_blowUp_le_scaled_weight hU.measurableSet hθ ξ hr.1
        ((closedBall_subset_closedBall hrA').trans hBR) _
        (tangentDensityCutoff_mem_Icc hε) (fun _ hx ↦ tangentDensityCutoff_eq_zero hε hx)
    exact (unitBallVolume_le_integral_tangentDensityCutoff hn hP.finrank_eq hε).trans hle
  have hlim : Tendsto (fun ε : ℝ ↦ (1 + ε) ^ n * ω * d)
      (𝓝[>] (0 : ℝ)) (𝓝 (ω * d)) := by
    have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
    simpa only [id_eq, add_zero, one_pow, one_mul] using
      (((hone.add
        (tendsto_id.mono_left inf_le_left : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0))).pow n).mul_const ω).mul_const d
  have hle : ω ≤ ω * d := ge_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin] with ε hε using hall ε hε)
  nlinarith

theorem HasGeneralizedMeanCurvatureIn.one_le_stationaryDensityReal_ae
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    (hU : IsOpen U) (hn : 0 < n) {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x) :
    ∀ᵐ ξ ∂V.weight.restrict U, 1 ≤ V.stationaryDensityReal ξ := by
  rw [ae_restrict_iff' hU.measurableSet]
  filter_upwards [V.ae_weight_of_ae_restrict V.approximate_tangent] with ξ hξ hξU
  exact V.one_le_density_of_approximateTangent hU hn hθ hξU hξ
    (HasGeneralizedMeanCurvatureIn.tendsto_densityQuotient_real (V := V) hH hbound hU hξU)

/-- Upper semicontinuity extends the a.e. lower bound to every support
point. This proves the geometric assertion used before Simon (5.6), under
the bounded-curvature hypotheses already present there. -/
theorem HasGeneralizedMeanCurvatureIn.one_le_stationaryDensityReal_of_mem_support
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    (hU : IsOpen U) (hn : 0 < n) {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    {ξ : E} (hξ : ξ ∈ U) (hsupp : ξ ∈ V.weight.support) :
    1 ≤ V.stationaryDensityReal ξ := by
  by_contra hnot
  have hlt : V.stationaryDensityReal ξ < 1 := lt_of_not_ge hnot
  have hupper := HasGeneralizedMeanCurvatureIn.upperSemicontinuousOn_stationaryDensityReal
    (V := V) hH hbound hU ξ hξ 1 hlt
  rw [hU.nhdsWithin_eq hξ] at hupper
  have hneigh : {x | V.stationaryDensityReal x < 1 ∧ x ∈ U} ∈ 𝓝 ξ :=
    hupper.and (hU.mem_nhds hξ)
  have hpos := (Measure.mem_support_iff_forall (μ := V.weight) ξ).mp hsupp _ hneigh
  have hae := HasGeneralizedMeanCurvatureIn.one_le_stationaryDensityReal_ae
    (V := V) hH hU hn hbound hθ
  rw [ae_restrict_iff' hU.measurableSet] at hae
  have hzero : V.weight {x | V.stationaryDensityReal x < 1 ∧ x ∈ U} = 0 := by
    apply measure_mono_null (t := {x | ¬ (x ∈ U → 1 ≤ V.stationaryDensityReal x)})
    · intro x hx hgood
      exact (not_le_of_gt hx.1) (hgood hx.2)
    · exact ae_iff.mp hae
  exact hpos.ne' hzero

/-- The source pointwise estimate preceding (5.6), now with its lower
density derived from multiplicity and approximate tangents. -/
theorem HasGeneralizedMeanCurvatureIn.value_le_weightedPotential_of_multiplicity
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    (hn : 0 < n) {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U)
    (hhnonneg : ∀ x ∈ U, 0 ≤ h x) {ξ : E} (hsupp : ξ ∈ V.weight.support)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall ξ ρ ⊆ U) :
    ENNReal.ofReal (h ξ) ≤ ENNReal.ofReal (Real.exp (Λ * ρ)) *
      (ENNReal.ofReal (V.weightedBallAverage ξ h ρ) +
        ENNReal.ofReal (1 / ((n : ℝ) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal)) *
          V.radialWeightedPotential ξ (fun x ↦ ‖V.tangentialGradient h x‖) ρ) :=
  HasGeneralizedMeanCurvatureIn.value_le_weightedPotential_of_one_le_density
    (V := V) hH hU hn hh hhnonneg ξ hΛ hbound hρ hball
    (HasGeneralizedMeanCurvatureIn.one_le_stationaryDensityReal_of_mem_support
      (V := V) hH hU hn hbound hθ (hball (mem_closedBall_self hρ.le)) hsupp)

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
