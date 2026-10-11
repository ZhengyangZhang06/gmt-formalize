module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

@[expose] public section

/-!
# Signed scalar Riesz representation for locally bounded functionals

This supplies the scalar component construction needed for the vector
Riesz representation in Simon (8.2.5)--(8.2.6). The positive part is
constructed as the supremum over an order interval, its additivity is
proved by the pointwise lattice decomposition, and Mathlib's positive
Riesz--Markov theorem supplies the two locally finite Radon measures.
-/

open Set MeasureTheory CompactlySupportedContinuousMap
open scoped CompactlySupported BoundedContinuousFunction ENNReal NNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
variable {X : Type*} [TopologicalSpace X]

/-- Local uniform-norm boundedness on each compact-support space. -/
def CcLocallyBounded (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ K : Set X, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
    ∀ f : C_c(X, ℝ), tsupport f ⊆ K → |L f| ≤ C * ‖f.toBoundedContinuousFunction‖

/-- The order intervals needed in the positive-part construction are
bounded under a locally bounded functional. -/
theorem CcLocallyBounded.bddAbove_orderInterval
    {L : C_c(X, ℝ) →ₗ[ℝ] ℝ} (hL : CcLocallyBounded L) (f : C_c(X, ℝ≥0)) :
    BddAbove (L '' Icc 0 f.toReal) := by
  obtain ⟨C, hC, hc⟩ := hL (tsupport f.toReal) f.toReal.hasCompactSupport
  refine ⟨C * ‖f.toReal.toBoundedContinuousFunction‖, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  have hsupport : tsupport g ⊆ tsupport f.toReal := by
    apply closure_mono
    intro x hx
    change g x ≠ 0 at hx
    change f.toReal x ≠ 0
    intro hzero
    exact hx (le_antisymm (hzero ▸ hg.2 x) (hg.1 x))
  have hnorm : ‖g.toBoundedContinuousFunction‖ ≤ ‖f.toReal.toBoundedContinuousFunction‖ := by
    apply BoundedContinuousFunction.norm_le (norm_nonneg _) |>.mpr
    intro x
    change ‖g x‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (hg.1 x)]
    exact (hg.2 x).trans
      ((le_abs_self (f.toReal x)).trans (f.toReal.toBoundedContinuousFunction.norm_coe_le_norm x))
  exact (le_abs_self (L g)).trans ((hc g hsupport).trans
    (mul_le_mul_of_nonneg_left hnorm hC))

namespace ScalarRiesz

variable (L : C_c(X, ℝ) →ₗ[ℝ] ℝ)

def positivePartValue (f : C_c(X, ℝ≥0)) : ℝ := sSup (L '' Icc 0 f.toReal)

theorem orderInterval_nonempty (f : C_c(X, ℝ≥0)) :
    (L '' Icc 0 f.toReal).Nonempty :=
  ⟨0, 0, ⟨le_rfl, toReal_nonneg⟩, L.map_zero⟩

variable {L} (hL : CcLocallyBounded L)
include hL

theorem le_positivePartValue (f : C_c(X, ℝ≥0)) (g : C_c(X, ℝ))
    (hg0 : 0 ≤ g) (hgf : g ≤ f.toReal) : L g ≤ positivePartValue L f :=
  le_csSup (hL.bddAbove_orderInterval f) ⟨g, ⟨hg0, hgf⟩, rfl⟩

theorem positivePartValue_nonneg (f : C_c(X, ℝ≥0)) : 0 ≤ positivePartValue L f := by
  simpa only [map_zero] using le_positivePartValue hL f 0 le_rfl toReal_nonneg

omit hL in
theorem positivePartValue_le (f : C_c(X, ℝ≥0)) {C : ℝ}
    (hC : ∀ g : C_c(X, ℝ), 0 ≤ g → g ≤ f.toReal → L g ≤ C) :
    positivePartValue L f ≤ C :=
  csSup_le (orderInterval_nonempty L f) (by rintro _ ⟨g, hg, rfl⟩; exact hC g hg.1 hg.2)

@[simp] theorem positivePartValue_zero : positivePartValue L 0 = 0 := by
  apply le_antisymm (positivePartValue_le 0 ?_) (positivePartValue_nonneg hL 0)
  intro g hg0 hg
  have hz : (0 : C_c(X, ℝ≥0)).toReal = 0 := by
    ext x
    simp only [toReal_apply, CompactlySupportedContinuousMap.zero_apply, NNReal.coe_zero]
  have : g = 0 := le_antisymm (hz ▸ hg) hg0
  simp [this]

theorem positivePartValue_add (f g : C_c(X, ℝ≥0)) :
    positivePartValue L (f + g) = positivePartValue L f + positivePartValue L g := by
  apply le_antisymm
  · apply positivePartValue_le
    intro k hk0 hkle
    let k₁ := k ⊓ f.toReal
    let k₂ := k - k₁
    have hk₁0 : 0 ≤ k₁ := le_inf hk0 toReal_nonneg
    have hk₁f : k₁ ≤ f.toReal := inf_le_right
    have hk₂0 : 0 ≤ k₂ := sub_nonneg.mpr inf_le_left
    have hk₂g : k₂ ≤ g.toReal := by
      intro x
      change k x - min (k x) (f.toReal x) ≤ g.toReal x
      rcases le_total (k x) (f.toReal x) with hx | hx
      · rw [min_eq_left hx, sub_self]
        exact toReal_nonneg x
      · rw [min_eq_right hx]
        have hh := hkle x
        simp only [toReal_add, coe_add, Pi.add_apply] at hh
        linarith
    have h1 := le_positivePartValue hL f k₁ hk₁0 hk₁f
    have h2 := le_positivePartValue hL g k₂ hk₂0 hk₂g
    have heq : L k₂ = L k - L k₁ := L.map_sub k k₁
    linarith
  · have hleft : positivePartValue L f ≤
        positivePartValue L (f + g) - positivePartValue L g := by
      apply positivePartValue_le
      intro a ha0 haf
      have hright : positivePartValue L g ≤ positivePartValue L (f + g) - L a := by
        apply positivePartValue_le
        intro b hb0 hbg
        have h := le_positivePartValue hL (f + g) (a + b)
          (add_nonneg ha0 hb0) (by simpa only [toReal_add] using add_le_add haf hbg)
        rw [map_add] at h
        linarith
      linarith
    linarith

theorem positivePartValue_smul_le (c : ℝ≥0) (f : C_c(X, ℝ≥0)) :
    positivePartValue L (c • f) ≤ c * positivePartValue L f := by
  by_cases hc : c = 0
  · simp [hc, positivePartValue_zero hL]
  have hcpos : 0 < (c : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
  apply positivePartValue_le
  intro g hg0 hgf
  let k : C_c(X, ℝ) := (c : ℝ)⁻¹ • g
  have hk0 : 0 ≤ k := fun x ↦ mul_nonneg (inv_nonneg.mpr hcpos.le) (hg0 x)
  have hkf : k ≤ f.toReal := by
    intro x
    change (c : ℝ)⁻¹ * g x ≤ f.toReal x
    have h := hgf x
    simp only [toReal_apply, CompactlySupportedContinuousMap.smul_apply,
      smul_eq_mul, NNReal.coe_mul] at h
    apply (inv_mul_le_iff₀ hcpos).mpr
    simpa only [toReal_apply] using h
  have hk := le_positivePartValue hL f k hk0 hkf
  have heq : L k = (c : ℝ)⁻¹ * L g := L.map_smul _ _
  rw [heq] at hk
  exact (inv_mul_le_iff₀ hcpos).mp hk

theorem positivePartValue_smul (c : ℝ≥0) (f : C_c(X, ℝ≥0)) :
    positivePartValue L (c • f) = c * positivePartValue L f := by
  by_cases hc : c = 0
  · simp [hc, positivePartValue_zero hL]
  have hcpos : 0 < (c : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
  apply le_antisymm (positivePartValue_smul_le hL c f)
  have h := positivePartValue_smul_le hL c⁻¹ (c • f)
  rw [inv_smul_smul₀ hc] at h
  simp only [NNReal.coe_inv] at h
  exact (le_inv_mul_iff₀ hcpos).mp h

/-- The positive-part cone functional, with additivity proved using the
Riesz lattice decomposition of the interval `[0,f+g]`. -/
def positivePartNNReal : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 where
  toFun f := ⟨positivePartValue L f, positivePartValue_nonneg hL f⟩
  map_add' f g := NNReal.eq (positivePartValue_add hL f g)
  map_smul' c f := NNReal.eq (positivePartValue_smul hL c f)

def positivePart : C_c(X, ℝ) →ₚ[ℝ] ℝ := toRealPositiveLinear (positivePartNNReal hL)

theorem le_positivePart {f : C_c(X, ℝ)} (hf : 0 ≤ f) : L f ≤ positivePart hL f := by
  have hfeq : f.nnrealPart.toReal = f := by
    ext x
    rw [toReal_apply, nnrealPart_apply]
    exact Real.coe_toNNReal (f x) (hf x)
  have heq := eq_toRealPositiveLinear_toReal (positivePartNNReal hL) f.nnrealPart
  change positivePart hL f.nnrealPart.toReal = positivePartValue L f.nnrealPart at heq
  rw [hfeq] at heq
  rw [heq]
  exact le_positivePartValue hL f.nnrealPart f hf hfeq.ge

/-- The second positive functional is the positive part minus the original
functional. Positivity follows from the defining supremum. -/
def negativePart : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ ((positivePart hL).toLinearMap - L)
    (fun _f hf ↦ sub_nonneg.mpr (le_positivePart hL hf))

theorem positivePart_sub_negativePart (f : C_c(X, ℝ)) :
    positivePart hL f - negativePart hL f = L f := by
  change positivePart hL f - (positivePart hL f - L f) = L f
  ring

section Measures
variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The first positive Radon measure in the scalar component construction. -/
def positiveMeasure : Measure X := RealRMK.rieszMeasure (positivePart hL)

/-- The second positive Radon measure in the scalar component construction. -/
def negativeMeasure : Measure X := RealRMK.rieszMeasure (negativePart hL)

instance : (positiveMeasure hL).Regular := RealRMK.regular_rieszMeasure _
instance : (negativeMeasure hL).Regular := RealRMK.regular_rieszMeasure _
instance : IsLocallyFiniteMeasure (positiveMeasure hL) := inferInstance
instance : IsLocallyFiniteMeasure (negativeMeasure hL) := inferInstance

/-- Signed scalar Riesz representation, constructed from local boundedness
and the positive Riesz--Markov theorem, without a signed-measure premise. -/
theorem integral_positiveMeasure_sub_integral_negativeMeasure (f : C_c(X, ℝ)) :
    (∫ x, f x ∂positiveMeasure hL) - (∫ x, f x ∂negativeMeasure hL) = L f := by
  rw [positiveMeasure, negativeMeasure, RealRMK.integral_rieszMeasure,
    RealRMK.integral_rieszMeasure]
  exact positivePart_sub_negativePart hL f

end Measures

end ScalarRiesz
end
end Poincare.SimonGMT.Chapter08
