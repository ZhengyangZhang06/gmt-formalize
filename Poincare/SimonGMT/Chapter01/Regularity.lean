module

public import Mathlib.MeasureTheory.Measure.Regular
public import Poincare.SimonGMT.Chapter01.Basic

public section

/-!
# Simon GMT, Chapter 1, Theorems 1.15--1.16

This module transfers Simon's Borel-regular outer measure to its associated
Borel measure and applies Mathlib's regular-measure machinery.  The theorems
below state the outer-regular conclusion for every set and the inner-regular
conclusions first for Borel sets.  The completion step from Borel sets to all
Carathéodory-measurable sets is kept separate rather than hidden in notation.
-/

open Filter Set
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u

variable {X : Type u} [TopologicalSpace X]

/-- An open `σ`-finite cover makes the Borel measure associated to a Simon
Borel-regular outer measure locally finite. -/
theorem IsBorelRegularOuterMeasure.toBorelMeasure_isLocallyFinite
    {μ : MeasureTheory.OuterMeasure X} (hμ : IsBorelRegularOuterMeasure μ)
    (hopen : IsOpenSigmaFinite μ) :
    @MeasureTheory.IsLocallyFiniteMeasure X (borel X) _
      hμ.toBorelMeasure := by
  rcases (isOpenSigmaFinite_iff μ).mp hopen with ⟨V, hV, hcover⟩
  constructor
  intro x
  have hx : x ∈ ⋃ n, V n := by rw [hcover]; exact mem_univ x
  obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
  refine ⟨V n, (hV n).1.mem_nhds hxn, ?_⟩
  simpa using (hV n).2

/-- The same open cover gives `σ`-finiteness of the associated Borel
measure. -/
theorem IsBorelRegularOuterMeasure.toBorelMeasure_sigmaFinite
    {μ : MeasureTheory.OuterMeasure X} (hμ : IsBorelRegularOuterMeasure μ)
    (hopen : IsOpenSigmaFinite μ) :
    @MeasureTheory.SigmaFinite X (borel X) hμ.toBorelMeasure := by
  rcases (isOpenSigmaFinite_iff μ).mp hopen with ⟨V, hV, hcover⟩
  apply MeasureTheory.sigmaFinite_iff.mpr
  refine ⟨{
    set := V
    set_mem := fun _ ↦ mem_univ _
    finite := fun n ↦ ?_
    spanning := hcover }⟩
  simpa using (hV n).2

section Metrizable

variable [TopologicalSpace.PseudoMetrizableSpace X] [SecondCountableTopology X]

/-- Simon Theorem 1.15(1): outer approximation by open supersets.  The
conclusion is stated directly for the original outer measure and holds for
arbitrary, not necessarily measurable, sets. -/
theorem IsBorelRegularOuterMeasure.measure_eq_iInf_isOpen
    {μ : MeasureTheory.OuterMeasure X} (hμ : IsBorelRegularOuterMeasure μ)
    (hopen : IsOpenSigmaFinite μ) (A : Set X) :
    μ A = ⨅ (U : Set X) (_ : A ⊆ U) (_ : IsOpen U), μ U := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  letI : MeasureTheory.IsLocallyFiniteMeasure hμ.toBorelMeasure :=
    hμ.toBorelMeasure_isLocallyFinite hopen
  letI : MeasureTheory.Measure.WeaklyRegular hμ.toBorelMeasure := by
    infer_instance
  simpa only [hμ.toBorelMeasure_apply_all] using
    A.measure_eq_iInf_isOpen hμ.toBorelMeasure

/-- The Borel-set case of Simon Theorem 1.15(2): inner approximation by
closed subsets. -/
theorem IsBorelRegularOuterMeasure.borel_measure_eq_iSup_isClosed
    {μ : MeasureTheory.OuterMeasure X} (hμ : IsBorelRegularOuterMeasure μ)
    (hopen : IsOpenSigmaFinite μ) {A : Set X}
    (hA : @MeasurableSet X (borel X) A) :
    μ A = ⨆ (C : Set X) (_ : C ⊆ A) (_ : IsClosed C), μ C := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  letI : MeasureTheory.IsLocallyFiniteMeasure hμ.toBorelMeasure :=
    hμ.toBorelMeasure_isLocallyFinite hopen
  letI : MeasureTheory.SigmaFinite hμ.toBorelMeasure :=
    hμ.toBorelMeasure_sigmaFinite hopen
  letI : MeasureTheory.Measure.WeaklyRegular hμ.toBorelMeasure := by
    infer_instance
  have hinner : MeasureTheory.Measure.InnerRegularWRT hμ.toBorelMeasure
      IsClosed (@MeasurableSet X (borel X)) :=
    MeasureTheory.Measure.InnerRegularWRT.trans
      MeasureTheory.Measure.WeaklyRegular.innerRegular_measurable
      MeasureTheory.Measure.InnerRegularWRT.of_sigmaFinite
  simpa only [hμ.toBorelMeasure_apply_all] using hinner.measure_eq_iSup hA

/-- Simon Remark 1.16 for Borel sets: on a `σ`-compact space, closed inner
approximants can be replaced by compact ones. -/
theorem IsBorelRegularOuterMeasure.borel_measure_eq_iSup_isCompact
    [SigmaCompactSpace X]
    {μ : MeasureTheory.OuterMeasure X} (hμ : IsBorelRegularOuterMeasure μ)
    (hopen : IsOpenSigmaFinite μ) {A : Set X}
    (hA : @MeasurableSet X (borel X) A) :
    μ A = ⨆ (K : Set X) (_ : K ⊆ A) (_ : IsCompact K), μ K := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  letI : MeasureTheory.IsLocallyFiniteMeasure hμ.toBorelMeasure :=
    hμ.toBorelMeasure_isLocallyFinite hopen
  letI : MeasureTheory.SigmaFinite hμ.toBorelMeasure :=
    hμ.toBorelMeasure_sigmaFinite hopen
  letI : MeasureTheory.Measure.WeaklyRegular hμ.toBorelMeasure := by
    infer_instance
  have hclosed : MeasureTheory.Measure.InnerRegularWRT hμ.toBorelMeasure
      IsClosed (@MeasurableSet X (borel X)) :=
    MeasureTheory.Measure.InnerRegularWRT.trans
      MeasureTheory.Measure.WeaklyRegular.innerRegular_measurable
      MeasureTheory.Measure.InnerRegularWRT.of_sigmaFinite
  have hcompact : MeasureTheory.Measure.InnerRegularWRT hμ.toBorelMeasure
      IsCompact (@MeasurableSet X (borel X)) :=
    (MeasureTheory.Measure.InnerRegularWRT.isCompact_isClosed
      hμ.toBorelMeasure).trans hclosed
  simpa only [hμ.toBorelMeasure_apply_all] using hcompact.measure_eq_iSup hA

end Metrizable

end Poincare.SimonGMT.Chapter01
