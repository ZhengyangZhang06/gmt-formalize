module

public import Poincare.SimonGMT.Chapter01.GeneralDifferentiation
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section

/-!
# Simon GMT, Chapter 1, differentiation of measures

The abstract Radon--Nikodym derivative is identified with the actual
closed-ball density.  The argument uses (3.15) and the nonnegative form of
(3.17), with open sigma-finite localization, and imposes no countability
condition on the ambient metric space.
-/

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology Classical

namespace Poincare.SimonGMT.Chapter01

variable {X : Type*} [MetricSpace X]

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

/-- Open sigma-finiteness passes to a smaller outer measure. -/
theorem IsOpenSigmaFinite.mono {μ ν : OuterMeasure X}
    (hμ : IsOpenSigmaFinite μ) (hνμ : ν ≤ μ) : IsOpenSigmaFinite ν := by
  obtain ⟨U, hU, hcover⟩ := (isOpenSigmaFinite_iff μ).mp hμ
  exact (isOpenSigmaFinite_iff ν).mpr ⟨U, fun j => ⟨(hU j).1,
    (hνμ _).trans_lt (hU j).2⟩, hcover⟩

/-- The local nonnegative differentiation theorem, with local
integrability encoded by an open finite-mass cover for the weighted measure. -/
theorem ae_tendsto_setLIntegral_div_of_openSigmaFinite_withDensity
    (ν : Measure X) (hopenν : IsOpenSigmaFinite ν.toOuterMeasure)
    (hV : HasSymmetricVitaliProperty ν.toOuterMeasure)
    {f : X → ℝ≥0∞} (hf : Measurable f)
    (hopenf : IsOpenSigmaFinite (ν.withDensity f).toOuterMeasure) :
    ∀ᵐ x ∂ν, Tendsto (fun r : ℝ => (∫⁻ y in closedBall x r, f y ∂ν) /
      ν (closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  obtain ⟨U, hU, hcover⟩ := (isOpenSigmaFinite_iff _).mp hopenf
  have hlocal : ∀ j : ℕ, ∀ᵐ x ∂ν, x ∈ U j →
      Tendsto (fun r : ℝ => (∫⁻ y in closedBall x r, f y ∂ν) /
        ν (closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
    intro j
    have hfin : ∫⁻ y, (U j).indicator f y ∂ν ≠ ∞ := by
      rw [lintegral_indicator (hU j).1.measurableSet]
      simpa only [Measure.toOuterMeasure_apply, withDensity_apply _ (hU j).1.measurableSet]
        using (hU j).2.ne
    filter_upwards [ae_tendsto_setLIntegral_div_of_measurable ν hopenν hV
      (hf.indicator (hU j).1.measurableSet) hfin] with x hx hxU
    rw [indicator_of_mem hxU] at hx
    apply hx.congr'
    obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp ((hU j).1.mem_nhds hxU)
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr
    congr 1
    exact setLIntegral_congr_fun measurableSet_closedBall fun y hy =>
      indicator_of_mem (hRU ((closedBall_subset_closedBall hr.2.le) hy)) f
  filter_upwards [ae_all_iff.mpr hlocal] with x hx
  obtain ⟨j, hxj⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
  exact hx j hxj

/-- The density of a singular open-sigma-finite measure vanishes almost
everywhere for a reference measure with the symmetric Vitali property. -/
theorem ae_tendsto_outerRelativeDensityQuotient_zero_of_mutuallySingular
    (μ ν : Measure X) (hopenμ : IsOpenSigmaFinite μ.toOuterMeasure)
    (hopenν : IsOpenSigmaFinite ν.toOuterMeasure)
    (hV : HasSymmetricVitaliProperty ν.toOuterMeasure) (hsing : μ ⟂ₘ ν) :
    ∀ᵐ x ∂ν, Tendsto (outerRelativeDensityQuotient μ.toOuterMeasure ν.toOuterMeasure x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hμ := measure_toOuterMeasure_isBorelRegular μ
  have hν := measure_toOuterMeasure_isBorelRegular ν
  obtain ⟨S, _, hμS, hνSc⟩ := hsing
  have hnull := measure_pos_outerRelativeUpperDensity_inter_eq_zero
    μ.toOuterMeasure ν.toOuterMeasure hμ hν hopenμ hopenν hV S hμS
  have hden : ∀ᵐ x ∂ν, x ∈ S →
      outerRelativeUpperDensity μ.toOuterMeasure ν.toOuterMeasure x = 0 := by
    rw [ae_iff]
    simpa only [not_imp, Measure.toOuterMeasure_apply] using hnull
  have hSae : ∀ᵐ x ∂ν, x ∈ S := by
    rw [ae_iff]
    exact hνSc
  filter_upwards [hden, hSae] with x hx hxS
  exact tendsto_outerRelativeDensityQuotient_zero_of_upperDensity_zero _ _ _ (hx hxS)

/-- The actual density quotient converges to the abstract Radon--Nikodym
derivative under precisely the source's local measure hypotheses. -/
theorem ae_tendsto_outerRelativeDensityQuotient_rnDeriv
    (μ ν : Measure X) (hopenμ : IsOpenSigmaFinite μ.toOuterMeasure)
    (hopenν : IsOpenSigmaFinite ν.toOuterMeasure)
    (hV : HasSymmetricVitaliProperty ν.toOuterMeasure) :
    ∀ᵐ x ∂ν, Tendsto (outerRelativeDensityQuotient μ.toOuterMeasure ν.toOuterMeasure x)
      (𝓝[>] (0 : ℝ)) (𝓝 (μ.rnDeriv ν x)) := by
  have hμ := measure_toOuterMeasure_isBorelRegular μ
  have hν := measure_toOuterMeasure_isBorelRegular ν
  have hμeq : hμ.toBorelMeasure = μ := by ext S hS; exact hμ.toBorelMeasure_apply_all S
  have hνeq : hν.toBorelMeasure = ν := by ext S hS; exact hν.toBorelMeasure_apply_all S
  let : SigmaFinite μ := hμeq ▸ hμ.toBorelMeasure_sigmaFinite hopenμ
  let : SigmaFinite ν := hνeq ▸ hν.toBorelMeasure_sigmaFinite hopenν
  have hopenS : IsOpenSigmaFinite (μ.singularPart ν).toOuterMeasure := hopenμ.mono (by
    intro S
    simpa only [Measure.toOuterMeasure_apply] using μ.singularPart_le ν S)
  have hopenD : IsOpenSigmaFinite (ν.withDensity (μ.rnDeriv ν)).toOuterMeasure := hopenμ.mono (by
    intro S
    simpa only [Measure.toOuterMeasure_apply] using μ.withDensity_rnDeriv_le ν S)
  filter_upwards [ae_tendsto_outerRelativeDensityQuotient_zero_of_mutuallySingular
    (μ.singularPart ν) ν hopenS hopenν hV (μ.mutuallySingular_singularPart ν),
    ae_tendsto_setLIntegral_div_of_openSigmaFinite_withDensity ν hopenν hV
      (μ.measurable_rnDeriv ν) hopenD] with x hxS hxD
  have ht := hxS.add hxD
  simp only [zero_add] at ht
  apply ht.congr
  intro r
  simp only [outerRelativeDensityQuotient, Measure.toOuterMeasure_apply]
  rw [← withDensity_apply _ measurableSet_closedBall, ← ENNReal.add_div,
    ← Measure.add_apply, ← μ.haveLebesgueDecomposition_add ν]

/-- The Borel-measure form of the density identification, for the source's
outer measures. -/
theorem ae_outerRelativeDensityQuotient_tendsto_rnDeriv
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ν) :
    ∀ᵐ x ∂hν.toBorelMeasure, Tendsto (outerRelativeDensityQuotient μ ν x)
      (𝓝[>] (0 : ℝ)) (𝓝 (hμ.toBorelMeasure.rnDeriv hν.toBorelMeasure x)) := by
  simpa only [hμ.toOuterMeasure_toBorelMeasure, hν.toOuterMeasure_toBorelMeasure] using
    ae_tendsto_outerRelativeDensityQuotient_rnDeriv hμ.toBorelMeasure hν.toBorelMeasure
      (by simpa only [hμ.toOuterMeasure_toBorelMeasure] using hopenμ)
      (by simpa only [hν.toOuterMeasure_toBorelMeasure] using hopenν)
      (by simpa only [hν.toOuterMeasure_toBorelMeasure] using hV)

/-- Borel regularity turns an almost-everywhere assertion into a pointwise
assertion outside a Borel null set, even for nonmeasurable predicates. -/
theorem IsBorelRegularOuterMeasure.exists_borel_null_exception
    {μ : OuterMeasure X} (hμ : IsBorelRegularOuterMeasure μ) {P : X → Prop}
    (hP : ∀ᵐ x ∂hμ.toBorelMeasure, P x) :
    ∃ S : Set X, MeasurableSet S ∧ μ S = 0 ∧ ∀ x ∉ S, P x := by
  have hnull : μ {x | ¬ P x} = 0 := by
    simpa only [ae_iff, hμ.toBorelMeasure_apply_all] using hP
  obtain ⟨S, hsub, hS, heq⟩ := hμ.exists_borel_superset {x | ¬ P x}
  exact ⟨S, hS, heq.trans hnull, fun x hx => by
    by_contra hnot
    exact hx (hsub hnot)⟩

/-- Simon (3.23)(ii): existence and finiteness of the pointwise density
outside a Borel reference-null set, and Borel measurability there. -/
theorem simon_theorem_3_23_ii
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ν) :
    ∃ S : Set X, MeasurableSet S ∧ ν S = 0 ∧
      (∀ x ∉ S, Tendsto (outerRelativeDensityQuotient μ ν x)
        (𝓝[>] (0 : ℝ)) (𝓝 (outerRelativeUpperDensity μ ν x)) ∧
        outerRelativeUpperDensity μ ν x < ∞) ∧
      Measurable (fun x : {x // x ∉ S} => outerRelativeUpperDensity μ ν (x : X)) := by
  let : SigmaFinite hμ.toBorelMeasure := hμ.toBorelMeasure_sigmaFinite hopenμ
  have hae : ∀ᵐ x ∂hν.toBorelMeasure,
      Tendsto (outerRelativeDensityQuotient μ ν x) (𝓝[>] (0 : ℝ))
        (𝓝 (hμ.toBorelMeasure.rnDeriv hν.toBorelMeasure x)) ∧
      hμ.toBorelMeasure.rnDeriv hν.toBorelMeasure x < ∞ :=
    (ae_outerRelativeDensityQuotient_tendsto_rnDeriv μ ν hμ hν hopenμ hopenν hV).and
      (hμ.toBorelMeasure.rnDeriv_lt_top hν.toBorelMeasure)
  obtain ⟨S, hS, hνS, hpoint⟩ := hν.exists_borel_null_exception hae
  have heq : ∀ x ∉ S, outerRelativeUpperDensity μ ν x =
      hμ.toBorelMeasure.rnDeriv hν.toBorelMeasure x := fun x hx => (hpoint x hx).1.limsup_eq
  refine ⟨S, hS, hνS, fun x hx => ?_, ?_⟩
  · rw [heq x hx]
    exact hpoint x hx
  · have hfun : (fun x : {x // x ∉ S} => outerRelativeUpperDensity μ ν (x : X)) =
        (fun x : {x // x ∉ S} => hμ.toBorelMeasure.rnDeriv hν.toBorelMeasure (x : X)) :=
      funext fun x => heq x x.property
    rw [hfun]
    exact (hμ.toBorelMeasure.measurable_rnDeriv hν.toBorelMeasure).comp measurable_subtype_coe

/-- At numerator-almost every point, the density is the reciprocal of the
reverse Radon--Nikodym derivative, including the infinite-density case. -/
theorem ae_outerRelativeDensityQuotient_tendsto_inv_rnDeriv
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty μ) :
    ∀ᵐ x ∂hμ.toBorelMeasure, Tendsto (outerRelativeDensityQuotient μ ν x)
      (𝓝[>] (0 : ℝ)) (𝓝 ((hν.toBorelMeasure.rnDeriv hμ.toBorelMeasure x)⁻¹)) := by
  have hzero : ∀ᵐ x ∂hμ.toBorelMeasure, x ∉ zeroBallRegion μ := by
    rw [ae_iff, hμ.toBorelMeasure_apply_all]
    simpa only [not_not, ofPred_mem_eq] using hV.zeroBallRegion_eq_zero_of_openSigmaFinite hopenμ
  filter_upwards [ae_outerRelativeDensityQuotient_tendsto_rnDeriv
    ν μ hν hμ hopenν hopenμ hV, hzero] with x hx hxzero
  apply (tendsto_inv_iff.mpr hx).congr'
  filter_upwards [eventually_closedBall_measure_ne_top μ hopenμ x,
    self_mem_nhdsWithin] with r hrfin hrpos
  exact ENNReal.inv_div (Or.inl hrfin) (Or.inl (fun h => hxzero ⟨r, hrpos, h⟩))

/-- Simon (3.23)(i): pointwise existence outside a Borel numerator-null
set, with Borel measurability on its complement. -/
theorem simon_theorem_3_23_i
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty μ) :
    ∃ S : Set X, MeasurableSet S ∧ μ S = 0 ∧
      (∀ x ∉ S, Tendsto (outerRelativeDensityQuotient μ ν x)
        (𝓝[>] (0 : ℝ)) (𝓝 (outerRelativeUpperDensity μ ν x))) ∧
      Measurable (fun x : {x // x ∉ S} => outerRelativeUpperDensity μ ν (x : X)) := by
  obtain ⟨S, hS, hμS, hpoint⟩ := hμ.exists_borel_null_exception
    (ae_outerRelativeDensityQuotient_tendsto_inv_rnDeriv μ ν hμ hν hopenμ hopenν hV)
  have heq : ∀ x ∉ S, outerRelativeUpperDensity μ ν x =
      (hν.toBorelMeasure.rnDeriv hμ.toBorelMeasure x)⁻¹ := fun x hx => (hpoint x hx).limsup_eq
  refine ⟨S, hS, hμS, fun x hx => ?_, ?_⟩
  · rw [heq x hx]
    exact hpoint x hx
  · have hfun : (fun x : {x // x ∉ S} => outerRelativeUpperDensity μ ν (x : X)) =
        (fun x : {x // x ∉ S} => (hν.toBorelMeasure.rnDeriv hμ.toBorelMeasure (x : X))⁻¹) :=
      funext fun x => heq x x.property
    rw [hfun]
    exact ((hν.toBorelMeasure.measurable_rnDeriv hμ.toBorelMeasure).comp
      measurable_subtype_coe).inv

end Poincare.SimonGMT.Chapter01
