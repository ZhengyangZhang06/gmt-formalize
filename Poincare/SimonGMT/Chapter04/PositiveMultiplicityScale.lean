module

public import Poincare.SimonGMT.Chapter04.TangentDensity
import all Poincare.SimonGMT.Chapter04.Basic
import all Poincare.SimonGMT.Chapter03.Rectifiable

@[expose] public section

/-!
# Positive rescaling of varifold multiplicity

The carrier and its actual approximate tangent field are unchanged. The
weight is multiplied by the same positive constant.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

private theorem scaled_weightDensity {c : ℝ} (hc : 0 ≤ c) :
    (Measure.euclideanHausdorffMeasure n).withDensity
      (V.carrier.indicator fun x ↦ ENNReal.ofReal (c * V.multiplicity x)) =
      ENNReal.ofReal c • V.weight := by
  have hf : V.carrier.indicator (fun x ↦ ENNReal.ofReal (c * V.multiplicity x)) =
      ENNReal.ofReal c • V.carrier.indicator (fun x ↦ ENNReal.ofReal (V.multiplicity x)) := by
    ext x
    by_cases hx : x ∈ V.carrier <;> simp [hx, ENNReal.ofReal_mul hc]
  rw [hf, withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  rw [weight]

/-- Multiply a rectifiable varifold's positive multiplicity by a positive
real constant, retaining its carrier and tangent representative. -/
def scaleMultiplicity (c : ℝ) (hc : 0 < c) : RectifiableVarifold (E := E) n where
  carrier := V.carrier
  measurable_carrier := V.measurable_carrier
  rectifiable_carrier := V.rectifiable_carrier
  multiplicity x := c * V.multiplicity x
  multiplicity_hypotheses := by
    unfold Chapter03.IsLocallyIntegrableMultiplicity
    exact ⟨V.measurable_carrier,
      fun x hx ↦ mul_pos hc (V.multiplicity_hypotheses.positive hx),
      aemeasurable_const.mul V.multiplicity_hypotheses.aemeasurable,
      fun K hK ↦ (V.multiplicity_hypotheses.integrableOn_inter_compact hK).const_mul c⟩
  tangent := V.tangent
  approximate_tangent := V.approximate_tangent
  tangentProjection_aemeasurable := by
    rw [V.scaled_weightDensity hc.le]
    exact (aemeasurable_smul_measure_iff (ENNReal.ofReal_pos.mpr hc).ne').2
      V.tangentProjection_aemeasurable_weight
  locallyFiniteWeight := by
    rw [V.scaled_weightDensity hc.le]
    let : IsFiniteMeasureOnCompacts (ENNReal.ofReal c • V.weight) := ⟨fun K hK ↦ by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top⟩
    infer_instance

@[simp] theorem scaleMultiplicity_carrier (c : ℝ) (hc : 0 < c) :
    (V.scaleMultiplicity c hc).carrier = V.carrier := rfl

@[simp] theorem scaleMultiplicity_multiplicity (c : ℝ) (hc : 0 < c) (x : E) :
    (V.scaleMultiplicity c hc).multiplicity x = c * V.multiplicity x := rfl

theorem scaleMultiplicity_weight (c : ℝ) (hc : 0 < c) :
    (V.scaleMultiplicity c hc).weight = ENNReal.ofReal c • V.weight := by
  rw [weight]
  exact V.scaled_weightDensity hc.le

/-- The lower-density comparison from the actual tangent works for any
strictly positive lower multiplicity, not only the normalized bound one. -/
theorem lowerMultiplicity_le_density_of_approximateTangent
    {U : Set E} (hU : IsOpen U) (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, α ≤ V.multiplicity x)
    {ξ : E} (hξ : ξ ∈ U) {P : Submodule ℝ E}
    (hP : Chapter03.HasApproximateTangentSpaceAt n V.carrier ξ P) {d : ℝ}
    (hd : Tendsto (fun r ↦ V.weight.real (closedBall ξ r) /
      ((Chapter01.realUnitBallVolume (n : ℝ)).toReal * r ^ n))
      (𝓝[>] 0) (𝓝 d)) : α ≤ d := by
  let W := V.scaleMultiplicity α⁻¹ (inv_pos.mpr hα)
  have hθW : ∀ᵐ x ∂W.weight.restrict U, 1 ≤ W.multiplicity x := by
    rw [show W.weight = ENNReal.ofReal α⁻¹ • V.weight from V.scaleMultiplicity_weight _ _,
      Measure.restrict_smul, Measure.ae_ennreal_smul_measure_iff
        (ENNReal.ofReal_pos.mpr (inv_pos.mpr hα)).ne']
    filter_upwards [hθ] with x hx
    change 1 ≤ α⁻¹ * V.multiplicity x
    rw [← div_eq_inv_mul, one_le_div hα]
    exact hx
  have hlimit : Tendsto (fun r ↦ W.weight.real (closedBall ξ r) /
      ((Chapter01.realUnitBallVolume (n : ℝ)).toReal * r ^ n))
      (𝓝[>] 0) (𝓝 (α⁻¹ * d)) := by
    apply (hd.const_mul α⁻¹).congr
    intro r
    rw [show W.weight = ENNReal.ofReal α⁻¹ • V.weight from V.scaleMultiplicity_weight _ _]
    simp only [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_pos.mpr hα).le]
    ring
  have hle := W.one_le_density_of_approximateTangent hU hn hθW hξ hP hlimit
  rwa [← div_eq_inv_mul, one_le_div hα] at hle

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
