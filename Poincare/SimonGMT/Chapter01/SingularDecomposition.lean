module

public import Poincare.SimonGMT.Chapter01.GeneralDensity
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

@[expose] public section

/-!
# Simon GMT, Chapter 1, Lemma 3.19 and Remark 3.20

The reference measure in Lemma 3.19 need not be sigma-finite.  The proof
therefore constructs a maximal reference-null set directly, before
passing from a finite numerator measure to an equivalent finite measure.
-/

open Filter Set MeasureTheory
open scoped ENNReal Topology Classical

namespace Poincare.SimonGMT.Chapter01

section Abstract

variable {X : Type*} [MeasurableSpace X]

/-- The finite-measure step of Simon (3.19), with no finiteness condition
on the reference measure. -/
theorem exists_null_set_restrict_absolutelyContinuous_of_finite
    (μ ν : Measure X) [IsFiniteMeasure μ] :
    ∃ B : Set X, MeasurableSet B ∧ ν B = 0 ∧ μ.restrict Bᶜ ≪ ν := by
  let M : Set ℝ≥0∞ := {a | ∃ A : Set X, MeasurableSet A ∧ ν A = 0 ∧ μ A = a}
  have hM : M.Nonempty := ⟨0, ∅, MeasurableSet.empty, measure_empty, measure_empty⟩
  obtain ⟨u, _, hu, huM⟩ := exists_seq_tendsto_sSup hM (OrderTop.bddAbove M)
  choose A hA hνA hμA using huM
  let B := ⋃ j, A j
  have hB : MeasurableSet B := MeasurableSet.iUnion hA
  have hνB : ν B = 0 := measure_iUnion_null hνA
  have hBmass : μ B = sSup M := by
    apply le_antisymm (le_sSup (show μ B ∈ M from ⟨B, hB, hνB, rfl⟩))
    apply le_of_tendsto hu
    exact Eventually.of_forall fun j => (hμA j).symm.trans_le (measure_mono (subset_iUnion A j))
  refine ⟨B, hB, hνB, Measure.AbsolutelyContinuous.mk ?_⟩
  intro S hS hνS
  rw [Measure.restrict_apply hS, ← Set.sdiff_eq,
    measure_sdiff' S hB.nullMeasurableSet (measure_ne_top μ B)]
  apply tsub_eq_zero_of_le
  rw [hBmass]
  exact le_sSup (show μ (S ∪ B) ∈ M from
    ⟨S ∪ B, hS.union hB, measure_union_null hνS hνB, rfl⟩)

/-- The maximal-null-set conclusion of Simon (3.19) holds even for an
s-finite numerator, while the reference measure remains arbitrary. -/
theorem exists_null_set_restrict_absolutelyContinuous_of_sFinite
    (μ ν : Measure X) [SFinite μ] :
    ∃ B : Set X, MeasurableSet B ∧ ν B = 0 ∧ μ.restrict Bᶜ ≪ ν := by
  obtain ⟨η, hηfin, hμη, _⟩ := exists_isFiniteMeasure_absolutelyContinuous μ
  let : IsFiniteMeasure η := hηfin
  obtain ⟨B, hB, hνB, hηB⟩ := exists_null_set_restrict_absolutelyContinuous_of_finite η ν
  exact ⟨B, hB, hνB, (hμη.restrict Bᶜ).trans hηB⟩

end Abstract

variable {X : Type*} [TopologicalSpace X]

/-- A countable cover by arbitrary finite-outer-mass sets makes the
canonical Borel measure sigma-finite.  The cover need not be Borel or open. -/
theorem IsBorelRegularOuterMeasure.toBorelMeasure_sigmaFinite_of_cover
    {μ : OuterMeasure X} (hμ : IsBorelRegularOuterMeasure μ)
    (S : ℕ → Set X) (hS : ∀ j, μ (S j) < ∞) (hcover : ⋃ j, S j = univ) :
    SigmaFinite hμ.toBorelMeasure := by
  apply sigmaFinite_iff.mpr
  exact ⟨{
    set := S
    set_mem := fun _ => mem_univ _
    finite := fun j => by simpa only [hμ.toBorelMeasure_apply_all] using hS j
    spanning := hcover }⟩

/-- Simon Lemma (3.19), including the stated absolute-continuity
conclusion on every subset of the ambient space.  Only the numerator
measure is sigma-finite, represented by its arbitrary finite-mass cover. -/
theorem simon_lemma_3_19
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν)
    (S : ℕ → Set X) (hS : ∀ j, μ (S j) < ∞) (hcover : ⋃ j, S j = univ) :
    ∃ B : Set X, @MeasurableSet X (borel X) B ∧ ν B = 0 ∧
      ∀ A : Set X, ν A = 0 → μ (A \ B) = 0 := by
  let : MeasurableSpace X := borel X
  let : SigmaFinite hμ.toBorelMeasure := hμ.toBorelMeasure_sigmaFinite_of_cover S hS hcover
  obtain ⟨B, hB, hνB, hμB⟩ := exists_null_set_restrict_absolutelyContinuous_of_sFinite
    hμ.toBorelMeasure hν.toBorelMeasure
  refine ⟨B, hB, by simpa only [hν.toBorelMeasure_apply_all] using hνB, ?_⟩
  intro A hνA
  have hA := hμB (show hν.toBorelMeasure A = 0 by
    simpa only [hν.toBorelMeasure_apply_all] using hνA)
  simpa only [Measure.restrict_apply' hB.compl,
    hμ.toBorelMeasure_apply_all, ← Set.sdiff_eq] using hA

/-- Simon Remark (3.20): the exceptional set is unique modulo numerator
null sets, and the absolutely continuous restriction is unique. -/
theorem simon_remark_3_20
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    {B C : Set X} (hB : @MeasurableSet X (borel X) B)
    (hC : @MeasurableSet X (borel X) C) (hνB : ν B = 0) (hνC : ν C = 0)
    (hACB : ∀ A : Set X, ν A = 0 → μ (A \ B) = 0)
    (hACC : ∀ A : Set X, ν A = 0 → μ (A \ C) = 0) :
    μ (symmDiff B C) = 0 ∧ OuterMeasure.restrict Bᶜ μ = OuterMeasure.restrict Cᶜ μ := by
  let : MeasurableSpace X := borel X
  have hBC : hμ.toBorelMeasure (B \ C) = 0 := by
    simpa only [hμ.toBorelMeasure_apply_all] using hACC B hνB
  have hCB : hμ.toBorelMeasure (C \ B) = 0 := by
    simpa only [hμ.toBorelMeasure_apply_all] using hACB C hνC
  have hset : B =ᵐ[hμ.toBorelMeasure] C := ae_eq_set.mpr ⟨hBC, hCB⟩
  constructor
  · simpa only [symmDiff_def, sup_eq_union, hμ.toBorelMeasure_apply_all] using measure_union_null hBC hCB
  · have heq := Measure.restrict_congr_set (Filter.EventuallyEqSet.compl hset)
    have houter := congrArg Measure.toOuterMeasure heq
    simpa only [Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict hB.compl,
      Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict hC.compl,
      hμ.toOuterMeasure_toBorelMeasure] using houter

end Poincare.SimonGMT.Chapter01
