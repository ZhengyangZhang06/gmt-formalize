module

public import Poincare.SimonGMT.Chapter08.FirstVariationExtension
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

@[expose] public section

/-!
# Recovering a polar measure from compactly supported unit tests

Radial truncation to the closed unit ball preserves compact support and
controls the approximation error. Consequently continuous compactly
supported unit fields recover the full mass of a finite Radon measure
paired with a measurable unit polar field. This supplies the reverse
inequality in Simon (8.2.5).
-/

open Set MeasureTheory CompactlySupportedContinuousMap
open scoped CompactlySupported ENNReal NNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
variable {N : ℕ}

/-- Continuous radial truncation to the closed Euclidean unit ball. -/
def radialUnitTruncation (v : Euclidean N) : Euclidean N := (max 1 ‖v‖)⁻¹ • v

theorem continuous_radialUnitTruncation : Continuous (@radialUnitTruncation N) := by
  exact ((continuous_const.max continuous_norm).inv₀
    (fun x ↦ ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖x‖)))).smul continuous_id

@[simp] theorem radialUnitTruncation_zero : radialUnitTruncation (0 : Euclidean N) = 0 := by
  simp [radialUnitTruncation]

theorem norm_radialUnitTruncation_le_one (v : Euclidean N) : ‖radialUnitTruncation v‖ ≤ 1 := by
  have hc : 0 < max 1 ‖v‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [radialUnitTruncation, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
  exact (inv_mul_le_iff₀ hc).mpr (by simp)

/-- The retraction has error at most twice the error to any unit-ball
target. This pointwise estimate is enough for `L¹` approximation. -/
theorem norm_sub_radialUnitTruncation_le (u v : Euclidean N) (hu : ‖u‖ ≤ 1) :
    ‖u - radialUnitTruncation v‖ ≤ 2 * ‖u - v‖ := by
  by_cases hv : ‖v‖ ≤ 1
  · simp only [radialUnitTruncation, max_eq_left hv, inv_one, one_smul]
    linarith [norm_nonneg (u - v)]
  have hvpos : 0 < ‖v‖ := lt_trans zero_lt_one (lt_of_not_ge hv)
  have hret : ‖v - radialUnitTruncation v‖ = ‖v‖ - 1 := by
    rw [radialUnitTruncation, max_eq_right (le_of_not_ge hv)]
    have heq : v - ‖v‖⁻¹ • v = (1 - ‖v‖⁻¹) • v := by module
    rw [heq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ((inv_le_one₀ hvpos).mpr (le_of_not_ge hv)))]
    rw [sub_mul, one_mul, inv_mul_cancel₀ hvpos.ne']
  have hnv : ‖v‖ - 1 ≤ ‖u - v‖ := by
    have htri := norm_add_le (v - u) u
    rw [sub_add_cancel, norm_sub_rev v u] at htri
    linarith
  calc
    ‖u - radialUnitTruncation v‖ ≤ ‖u - v‖ + ‖v - radialUnitTruncation v‖ :=
      by simpa only [sub_add_sub_cancel] using norm_add_le (u - v) (v - radialUnitTruncation v)
    _ ≤ 2 * ‖u - v‖ := by rw [hret]; linarith

/-- Continuous compactly supported unit tests detect the whole mass of
a finite Radon measure when paired with a measurable unit field. -/
theorem measureReal_univ_le_of_unit_polar_tests
    {X : Type*} [TopologicalSpace X] [NormalSpace X] [R1Space X]
    [WeaklyLocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular]
    (ν : X → Euclidean N) (hν : AEStronglyMeasurable ν μ)
    (hunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1) (C : ℝ)
    (hbound : ∀ f : C_c(X, Euclidean N), (∀ x, ‖f x‖ ≤ 1) →
      |∫ x, inner ℝ (ν x) (f x) ∂μ| ≤ C) : μ.real univ ≤ C := by
  have hνint : Integrable ν μ :=
    (integrable_const (1 : ℝ)).mono' hν (hunit.mono fun _ hx ↦ hx.le)
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  obtain ⟨g, hgc, hge, hgt, hgi⟩ :=
    hνint.exists_hasCompactSupport_integral_sub_le (half_pos hε)
  let f : C_c(X, Euclidean N) :=
    ⟨⟨fun x ↦ radialUnitTruncation (g x), continuous_radialUnitTruncation.comp hgt⟩,
      hgc.comp_left radialUnitTruncation_zero⟩
  have hfunit : ∀ x, ‖f x‖ ≤ 1 := fun x ↦ norm_radialUnitTruncation_le_one (g x)
  have hfi : Integrable f μ := f.integrable
  have hinner : Integrable (fun x ↦ inner ℝ (ν x) (f x)) μ := by
    apply hfi.norm.mono' (hν.inner f.continuous.aestronglyMeasurable)
    filter_upwards [hunit] with x hx
    exact (norm_inner_le_norm _ _).trans (by rw [hx, one_mul])
  have herr : (∫ x, ‖ν x - f x‖ ∂μ) ≤ ε := by
    calc
      _ ≤ ∫ x, 2 * ‖ν x - g x‖ ∂μ := by
        apply integral_mono_ae (hνint.sub hfi).norm ((hνint.sub hgi).norm.const_mul 2)
        filter_upwards [hunit] with x hx
        exact norm_sub_radialUnitTruncation_le (ν x) (g x) hx.le
      _ = 2 * ∫ x, ‖ν x - g x‖ ∂μ := integral_const_mul _ _
      _ ≤ ε := by linarith
  have hpoint : ∀ᵐ x ∂μ, (1 : ℝ) - inner ℝ (ν x) (f x) ≤ ‖ν x - f x‖ := by
    filter_upwards [hunit] with x hx
    have hi : inner ℝ (ν x) (ν x) = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
    rw [← hi, ← inner_sub_right]
    exact (real_inner_le_norm _ _).trans (by rw [hx, one_mul])
  have hi := integral_mono_ae ((integrable_const (1 : ℝ)).sub hinner) (hνint.sub hfi).norm hpoint
  change (∫ x, (1 : ℝ) - inner ℝ (ν x) (f x) ∂μ) ≤ (∫ x, ‖ν x - f x‖ ∂μ) at hi
  rw [integral_sub (integrable_const _) hinner, integral_const, smul_eq_mul, mul_one] at hi
  have hb := hbound f hfunit
  have hle := le_abs_self (∫ x, inner ℝ (ν x) (f x) ∂μ)
  change μ.real univ ≤ C + ε
  linarith

end
end Poincare.SimonGMT.Chapter08
