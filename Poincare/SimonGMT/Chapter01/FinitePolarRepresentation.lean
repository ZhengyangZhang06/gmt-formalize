module

public import Poincare.SimonGMT.Chapter01.FiniteL1Dual
public import Poincare.SimonGMT.Chapter01.PolarFieldNorm

@[expose] public section

/-!
# Simon 4.14 when the envelope measure is finite

The measurable unit polar field is constructed, not assumed.  The proof
combines the source's exact envelope construction and its `L¹` extension
with finite-measure Hilbert duality and the localized unit-norm argument.

The finite-envelope hypothesis is explicit.  It is automatic for a compact
domain, giving a complete compact-domain case of the printed theorem.
This file does not claim the unrestricted locally compact case.
-/

open CompactlySupportedContinuousMap Set MeasureTheory TopologicalSpace
open scoped CompactlySupported ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Complete polar representation when the Radon envelope has finite total
mass.  The result applies to any real Hilbert space, including the source's
finite-dimensional spaces. -/
theorem simon_theorem_4_14_of_finite_envelope
    (L : C_c(X, H) →ₗ[ℝ] ℝ) (hL : IsLocallyBoundedCcFunctional L)
    [IsFiniteMeasure (vectorFunctionalEnvelopeMeasure L hL)] :
    ∃ ν : X → H, StronglyMeasurable ν ∧
      (∀ᵐ x ∂vectorFunctionalEnvelopeMeasure L hL, ‖ν x‖ = 1) ∧
      ∀ f : C_c(X, H), L f =
        ∫ x, inner ℝ (f x) (ν x) ∂vectorFunctionalEnvelopeMeasure L hL := by
  let μ := vectorFunctionalEnvelopeMeasure L hL
  obtain ⟨T, hT, hText⟩ := simon_theorem_4_14_l1_extension L hL
  let ν := finiteL1DualField μ T
  have hν : StronglyMeasurable (ν : X → H) := Lp.stronglyMeasurable ν
  have hνle : ∀ᵐ x ∂μ, ‖ν x‖ ≤ 1 := finiteL1DualField_norm_le_one μ T hT
  have hrep : ∀ f : C_c(X, H), L f = ∫ x, inner ℝ (f x) (ν x) ∂μ := by
    intro f
    let hf : MemLp (f : X → H) 2 μ :=
      f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
    rw [← hText f]
    exact finiteL1DualField_represents μ T hf
  exact ⟨ν, hν,
    norm_eq_one_ae_of_innerRegular_envelope_representation L hL ν hν hνle hrep, hrep⟩

/-- A complete compact-domain form of Simon 4.14.  Compactness is an
explicit additional hypothesis, not attributed to the printed theorem. -/
theorem simon_theorem_4_14_compact [CompactSpace X]
    (L : C_c(X, H) →ₗ[ℝ] ℝ) (hL : IsLocallyBoundedCcFunctional L) :
    ∃ (μ : Measure X) (ν : X → H), IsRadonOuterMeasure μ.toOuterMeasure ∧
      StronglyMeasurable ν ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
      ∀ f : C_c(X, H), L f = ∫ x, inner ℝ (f x) (ν x) ∂μ := by
  let μ := vectorFunctionalEnvelopeMeasure L hL
  let : IsFiniteMeasure μ := ⟨isCompact_univ.measure_lt_top⟩
  obtain ⟨ν, hν, hunit, hrep⟩ := simon_theorem_4_14_of_finite_envelope L hL
  exact ⟨μ, ν, vectorFunctionalEnvelopeMeasure_isRadon L hL, hν, hunit, hrep⟩

end Poincare.SimonGMT.Chapter01
