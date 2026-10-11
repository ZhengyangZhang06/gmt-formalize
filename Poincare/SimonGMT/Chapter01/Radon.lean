module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.Regular
public import Poincare.SimonGMT.Chapter01.Densities

public section

/-!
# Simon GMT, Chapter 1, §4: Radon measures and representation

Mathlib's `Measure.Regular` packages exactly Simon's three Radon conditions:
finiteness on compact sets, outer regularity, and compact inner regularity of
open sets.  The Riesz--Markov--Kakutani construction below is the scalar case
of Simon's representation theorem.
-/

open CompactlySupportedContinuousMap Set TopologicalSpace
open scoped CompactlySupported ENNReal MeasureTheory Topology

namespace Poincare.SimonGMT.Chapter01

universe u

variable {X : Type u} [TopologicalSpace X] [MeasurableSpace X]

/-- Simon Definition 4.6, represented by Mathlib's regular-measure class. -/
abbrev IsRadonMeasure (mu : MeasureTheory.Measure X) : Prop :=
  MeasureTheory.Measure.Regular mu

section Regularity

variable [T2Space X] [BorelSpace X]
  (mu : MeasureTheory.Measure X) [IsRadonMeasure mu]

/-- Simon (R1): a Radon measure is finite on compact sets. -/
theorem radon_measure_lt_top_of_isCompact {K : Set X} (hK : IsCompact K) :
    mu K < ∞ :=
  hK.measure_lt_top

/-- Simon (R2): outer approximation of every set by open supersets. -/
theorem radon_measure_eq_iInf_isOpen (A : Set X) :
    mu A = ⨅ (U : Set X) (_ : A ⊆ U) (_ : IsOpen U), mu U :=
  A.measure_eq_iInf_isOpen mu

/-- Simon (R3): compact inner approximation of open sets. -/
theorem radon_isOpen_measure_eq_iSup_isCompact {U : Set X} (hU : IsOpen U) :
    mu U = ⨆ (K : Set X) (_ : K ⊆ U) (_ : IsCompact K), mu K :=
  hU.measure_eq_iSup_isCompact mu

/-- Simon Lemma 4.7: finite measurable sets admit compact inner
approximation. -/
theorem radon_measurable_measure_eq_iSup_isCompact_of_ne_top
    {A : Set X} (hA : MeasurableSet A) (hAfin : mu A ≠ ∞) :
    mu A = ⨆ (K : Set X) (_ : K ⊆ A) (_ : IsCompact K), mu K :=
  hA.measure_eq_iSup_isCompact_of_ne_top hAfin

end Regularity

section Riesz

variable [T2Space X] [BorelSpace X] [LocallyCompactSpace X]

/-- The representing Radon measure in the real-valued positive-functional
case of Simon Theorem 4.12. -/
noncomputable abbrev rieszRepresentingMeasure
    (Lambda : C_c(X, ℝ) →ₚ[ℝ] ℝ) : MeasureTheory.Measure X :=
  RealRMK.rieszMeasure Lambda

/-- Simon Theorem 4.12: the representing measure integrates every compactly
supported continuous function back to the functional. -/
@[simp] theorem integral_rieszRepresentingMeasure
    (Lambda : C_c(X, ℝ) →ₚ[ℝ] ℝ) (f : C_c(X, ℝ)) :
    ∫ x, f x ∂(rieszRepresentingMeasure Lambda) = Lambda f :=
  RealRMK.integral_rieszMeasure Lambda f

/-- The measure supplied by Riesz representation is a Simon Radon measure. -/
theorem rieszRepresentingMeasure_isRadon
    (Lambda : C_c(X, ℝ) →ₚ[ℝ] ℝ) :
    IsRadonMeasure (rieszRepresentingMeasure Lambda) := by
  infer_instance

/-- Uniqueness in scalar Riesz representation: regular measures agreeing on
all compactly supported continuous test functions are equal. -/
theorem radon_ext_of_integral_eq
    {mu nu : MeasureTheory.Measure X} [IsRadonMeasure mu] [IsRadonMeasure nu]
    (h : ∀ f : C_c(X, ℝ), ∫ x, f x ∂mu = ∫ x, f x ∂nu) :
    mu = nu :=
  MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported h

end Riesz

end Poincare.SimonGMT.Chapter01
