module

public import Poincare.SimonGMT.Chapter04.WeightedBallInequalities

@[expose] public section

/-!
# Measure-theoretic multiplicity bridges for Simon (5.6)--(5.7)

These results use the actual positive multiplicity defining the varifold
weight. They do not identify normalized ball density with multiplicity;
that geometric step is separate.
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

theorem weight_eq_carrier_withDensity :
    V.weight = ((Measure.euclideanHausdorffMeasure n).restrict V.carrier).withDensity
      (fun x ↦ ENNReal.ofReal (V.multiplicity x)) := by
  ext A hA
  rw [V.weight_apply hA, withDensity_apply _ hA, lintegral_indicator V.measurable_carrier,
    Measure.restrict_comm V.measurable_carrier]

/-- Positive multiplicity gives equivalence, not just one-way absolute
continuity, of weight-null and carrier-Hausdorff-null assertions. -/
theorem ae_weight_iff_ae_carrier {p : E → Prop} :
    (∀ᵐ x ∂V.weight, p x) ↔
      ∀ᵐ x ∂(Measure.euclideanHausdorffMeasure n).restrict V.carrier, p x := by
  rw [V.weight_eq_carrier_withDensity,
    ae_withDensity_iff' V.multiplicity_hypotheses.aemeasurable.ennreal_ofReal]
  constructor
  · intro hp
    filter_upwards [hp, ae_restrict_mem V.measurable_carrier] with x hx hxc
    exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (V.multiplicity_hypotheses.positive hxc)))
  · intro hp
    exact hp.mono fun _ hx _ ↦ hx

theorem ae_weight_restrict_iff_ae_carrier_restrict {U : Set E}
    (hU : MeasurableSet U) {p : E → Prop} :
    (∀ᵐ x ∂V.weight.restrict U, p x) ↔
      ∀ᵐ x ∂((Measure.euclideanHausdorffMeasure n).restrict V.carrier).restrict U, p x := by
  rw [ae_restrict_iff' hU, ae_restrict_iff' hU, V.ae_weight_iff_ae_carrier]

/-- The source hypothesis `θ≥1` implies an actual inequality of measures
on the indicated domain; it is not interpreted as a density assumption. -/
theorem carrierMeasure_restrict_le_weight_restrict {U : Set E} (hU : MeasurableSet U)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x) :
    ((Measure.euclideanHausdorffMeasure n).restrict V.carrier).restrict U ≤ V.weight.restrict U := by
  have hθ' := (V.ae_weight_restrict_iff_ae_carrier_restrict hU).mp hθ
  rw [V.weight_eq_carrier_withDensity, restrict_withDensity hU]
  have hden : (fun _ : E ↦ (1 : ℝ≥0∞)) ≤ᵐ[
      ((Measure.euclideanHausdorffMeasure n).restrict V.carrier).restrict U]
      (fun x ↦ ENNReal.ofReal (V.multiplicity x)) := by
    filter_upwards [hθ'] with x hx
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hx
  have hm := withDensity_mono hden
  change (((Measure.euclideanHausdorffMeasure n).restrict V.carrier).restrict U).withDensity 1 ≤ _ at hm
  rwa [withDensity_one] at hm

/-- In particular the carrier Hausdorff measure is finite on every
compact subset of a domain where the source lower multiplicity bound holds. -/
theorem carrierMeasure_lt_top_on_compact {U K : Set E} (hU : MeasurableSet U)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    (Measure.euclideanHausdorffMeasure n) (K ∩ V.carrier) < ∞ := by
  have hle := V.carrierMeasure_restrict_le_weight_restrict hU hθ K
  rw [Measure.restrict_apply hK.measurableSet,
    Measure.restrict_apply hK.measurableSet, inter_eq_left.mpr hKU,
    Measure.restrict_apply hK.measurableSet] at hle
  exact hle.trans_lt hK.measure_lt_top

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
