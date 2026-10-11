module

public import Poincare.SimonGMT.Chapter04.TangentDensity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import all Poincare.SimonGMT.Chapter03.Rectifiable

@[expose] public section

/-!
# The actual weight in a weighted approximate-tangent blow-up

This change of variables connects Simon's Chapter 3 definition of a
weighted approximate tangent with the rescaled actual varifold measure.
-/

open Filter Function Metric Set MeasureTheory
open scoped CompactlySupported ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

/-- The blow-up is a homeomorphism at every positive scale. -/
def blowUpHomeomorph (ξ : E) {r : ℝ} (hr : 0 < r) : E ≃ₜ E where
  toFun := Chapter03.blowUpMap ξ r
  invFun y := ξ + r • y
  left_inv y := by simp [Chapter03.blowUpMap, smul_smul, hr.ne']
  right_inv y := by simp [Chapter03.blowUpMap, smul_smul, hr.ne']
  continuous_toFun := by unfold Chapter03.blowUpMap; fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem blowUpHomeomorph_apply (ξ : E) {r : ℝ} (hr : 0 < r) (y : E) :
    blowUpHomeomorph ξ hr y = Chapter03.blowUpMap ξ r y := rfl

@[simp] theorem blowUpHomeomorph_symm_apply (ξ : E) {r : ℝ} (hr : 0 < r) (y : E) :
    (blowUpHomeomorph ξ hr).symm y = ξ + r • y := rfl

/-- Pushing the Hausdorff measure of a blown-up carrier back to the
original coordinates gives exactly the Hausdorff scaling factor. -/
theorem map_inverse_blowUp_carrier (ξ : E) {r : ℝ} (hr : 0 < r) (M : Set E) :
    ((Measure.euclideanHausdorffMeasure n).restrict (Chapter03.blowUpMap ξ r '' M)).map
      (blowUpHomeomorph ξ hr).symm =
      (ENNReal.ofReal (r⁻¹) ^ n) • (Measure.euclideanHausdorffMeasure n).restrict M := by
  let b := blowUpHomeomorph ξ hr
  ext A hA
  rw [Measure.map_apply b.symm.continuous.measurable hA,
    Measure.restrict_apply (b.symm.continuous.measurable hA),
    Measure.smul_apply, Measure.restrict_apply hA]
  have heq : b.symm ⁻¹' A ∩ Chapter03.blowUpMap ξ r '' M =
      Chapter03.blowUpMap ξ r '' (A ∩ M) := by
    change b.symm ⁻¹' A ∩ b '' M = b '' (A ∩ M)
    ext z
    constructor
    · rintro ⟨hz, y, hy, rfl⟩
      exact ⟨y, ⟨by simpa only [mem_preimage, b.symm_apply_apply] using hz, hy⟩, rfl⟩
    · rintro ⟨y, ⟨hyA, hyM⟩, rfl⟩
      exact ⟨by simpa only [mem_preimage, b.symm_apply_apply] using hyA, y, hyM, rfl⟩
  rw [heq, hausdorff_blowUp_image ξ hr]
  rfl

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

/-- Integration against the weight is integration against multiplicity
on the carrier, for arbitrary real-valued integrands. -/
theorem integral_weight_eq_integral_multiplicity (f : E → ℝ) :
    ∫ x, f x ∂V.weight =
      ∫ x in V.carrier, f x * V.multiplicity x ∂Measure.euclideanHausdorffMeasure n := by
  rw [V.weight_eq_carrier_withDensity,
    integral_withDensity_eq_integral_toReal_smul₀
      V.multiplicity_hypotheses.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem V.measurable_carrier] with x hx
  rw [ENNReal.toReal_ofReal (V.multiplicity_hypotheses.positive hx).le, smul_eq_mul, mul_comm]

/-- Exact weighted blow-up change of variables. -/
theorem integral_weighted_blowUp (ξ : E) {r : ℝ} (hr : 0 < r) (f : E → ℝ) :
    (∫ y in Chapter03.blowUpMap ξ r '' V.carrier,
      f y * V.multiplicity (ξ + r • y) ∂Measure.euclideanHausdorffMeasure n) =
      r⁻¹ ^ n * ∫ x, f (Chapter03.blowUpMap ξ r x) ∂V.weight := by
  let b := blowUpHomeomorph ξ hr
  have hi := b.symm.measurableEmbedding.integral_map
    (μ := (Measure.euclideanHausdorffMeasure n).restrict (Chapter03.blowUpMap ξ r '' V.carrier))
    (fun x ↦ f (b x) * V.multiplicity x)
  rw [map_inverse_blowUp_carrier ξ hr V.carrier, integral_smul_measure,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (inv_pos.mpr hr).le, smul_eq_mul] at hi
  rw [V.integral_weight_eq_integral_multiplicity]
  simp only [Homeomorph.apply_symm_apply] at hi
  simpa only [b, blowUpHomeomorph_apply, blowUpHomeomorph_symm_apply] using hi.symm

/-- The source weighted approximate tangent gives convergence of compact
continuous tests against the rescaled actual varifold weight. -/
theorem tendsto_rescaled_weight_of_weighted_approximateTangent
    {ξ : E} {P : Submodule ℝ E}
    (hP : Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.multiplicity ξ P)
    (f : C_c(E, ℝ)) :
    Tendsto (fun r : ℝ ↦ r⁻¹ ^ n * ∫ x, f (Chapter03.blowUpMap ξ r x) ∂V.weight)
      (𝓝[>] 0)
      (𝓝 (V.multiplicity ξ * ∫ y in (P : Set E), f y ∂Measure.euclideanHausdorffMeasure n)) := by
  apply (hP.2 f).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact V.integral_weighted_blowUp ξ hr f

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
