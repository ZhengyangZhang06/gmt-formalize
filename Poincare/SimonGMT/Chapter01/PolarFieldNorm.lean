module

public import Poincare.SimonGMT.Chapter01.VectorFunctionalL1
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# The unit-norm step in Simon 4.14

A unit-ball-valued field representing the functional must have norm one
almost everywhere on every compact set.  For an inner-regular envelope
measure this gives a global almost-everywhere statement.  In particular it
applies when the envelope measure is finite or sigma-finite.  The proof is
localized by compactly supported cutoffs and never assumes that a global
unit field is integrable.
-/

open CompactlySupportedContinuousMap Set Filter MeasureTheory TopologicalSpace
open scoped CompactlySupported ENNReal NNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The exact envelope identity forces a bounded representing field to
have unit norm almost everywhere on each compact set. -/
theorem norm_eq_one_on_compact_of_envelope_representation
    (L : C_c(X, H) →ₗ[ℝ] ℝ) (hL : IsLocallyBoundedCcFunctional L)
    (ν : X → H) (hν : AEStronglyMeasurable ν (vectorFunctionalEnvelopeMeasure L hL))
    (hνle : ∀ᵐ x ∂vectorFunctionalEnvelopeMeasure L hL, ‖ν x‖ ≤ 1)
    (hrep : ∀ ω : C_c(X, H), L ω =
      ∫ x, inner ℝ (ω x) (ν x) ∂vectorFunctionalEnvelopeMeasure L hL)
    {K : Set X} (hK : IsCompact K) :
    ∀ᵐ x ∂vectorFunctionalEnvelopeMeasure L hL, x ∈ K → ‖ν x‖ = 1 := by
  let μ := vectorFunctionalEnvelopeMeasure L hL
  obtain ⟨g, hgK, hgc, _, _⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
  let gCc : C_c(X, ℝ) := ⟨g, hgc⟩
  let f : C_c(X, ℝ≥0) := gCc.nnrealPart
  have hfK (x : X) (hx : x ∈ K) : (f x : ℝ) = 1 := by
    simp only [f, nnrealPart_apply, Real.coe_toNNReal']
    change max (g x) 0 = 1
    rw [hgK hx]
    norm_num
  have hfi : Integrable (fun x => (f x : ℝ)) μ := by
    exact (NNReal.continuous_coe.comp f.continuous).integrable_of_hasCompactSupport
      (f.hasCompactSupport.comp_left (by simp))
  have hfν : Integrable (fun x => (f x : ℝ) * ‖ν x‖) μ := by
    apply hfi.mono' (hfi.aestronglyMeasurable.mul hν.norm)
    filter_upwards [hνle] with x hx
    change ‖(f x : ℝ) * ‖ν x‖‖ ≤ (f x : ℝ)
    rw [Real.norm_of_nonneg (mul_nonneg (f x).coe_nonneg (norm_nonneg _))]
    exact mul_le_of_le_one_right (f x).coe_nonneg hx
  have hupper : (fun x => (f x : ℝ) * ‖ν x‖) ≤ᵐ[μ] (fun x => (f x : ℝ)) := by
    filter_upwards [hνle] with x hx
    exact mul_le_of_le_one_right (f x).coe_nonneg hx
  have hlower : (∫ x, (f x : ℝ) ∂μ) ≤ ∫ x, (f x : ℝ) * ‖ν x‖ ∂μ := by
    rw [← simon_theorem_4_14_positive_envelope L hL f]
    apply vectorFunctionalEnvelope_le
    intro ω hω
    have hωi := ω.continuous.integrable_of_hasCompactSupport (μ := μ) ω.hasCompactSupport
    have hinner : Integrable (fun x => inner ℝ (ω x) (ν x)) μ := by
      apply hωi.norm.mono' (hωi.aestronglyMeasurable.inner hν)
      filter_upwards [hνle] with x hx
      exact (norm_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hx)
    rw [hrep]
    apply integral_mono_ae hinner hfν
    exact Eventually.of_forall fun x => (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hω x) (norm_nonneg _))
  have heq : (fun x => (f x : ℝ) * ‖ν x‖) =ᵐ[μ] (fun x => (f x : ℝ)) :=
    (integral_eq_iff_of_ae_le hfν hfi hupper).mp
      (le_antisymm (integral_mono_ae hfν hfi hupper) hlower)
  filter_upwards [heq] with x hx hxK
  simpa only [hfK x hxK, one_mul] using hx

/-- Global unit norm follows from full inner regularity.  This hypothesis
is displayed explicitly; it is automatic for finite or sigma-finite Radon
measures, but is not silently inferred from the printed general setting. -/
theorem norm_eq_one_ae_of_innerRegular_envelope_representation
    (L : C_c(X, H) →ₗ[ℝ] ℝ) (hL : IsLocallyBoundedCcFunctional L)
    [Measure.InnerRegular (vectorFunctionalEnvelopeMeasure L hL)]
    (ν : X → H) (hν : StronglyMeasurable ν)
    (hνle : ∀ᵐ x ∂vectorFunctionalEnvelopeMeasure L hL, ‖ν x‖ ≤ 1)
    (hrep : ∀ ω : C_c(X, H), L ω =
      ∫ x, inner ℝ (ω x) (ν x) ∂vectorFunctionalEnvelopeMeasure L hL) :
    ∀ᵐ x ∂vectorFunctionalEnvelopeMeasure L hL, ‖ν x‖ = 1 := by
  let μ := vectorFunctionalEnvelopeMeasure L hL
  have hS : MeasurableSet {x | ‖ν x‖ ≠ 1} :=
    (measurableSet_eq_fun hν.norm.measurable measurable_const).compl
  rw [ae_iff]
  by_contra hbad
  obtain ⟨K, hKS, hK, hKpos⟩ :=
    Measure.InnerRegular.innerRegular (μ := μ) hS 0 (pos_iff_ne_zero.mpr hbad)
  have hlocal := norm_eq_one_on_compact_of_envelope_representation L hL ν
    hν.aestronglyMeasurable hνle hrep hK
  have hnull : ∀ᵐ x ∂μ, x ∉ K := by
    filter_upwards [hlocal] with x hx hxK
    exact hKS hxK (hx hxK)
  have hμK : μ K = 0 := measure_eq_zero_iff_ae_notMem.mpr hnull
  rw [hμK] at hKpos
  exact lt_irrefl 0 hKpos

end Poincare.SimonGMT.Chapter01
