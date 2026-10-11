module

public import Poincare.SimonGMT.Chapter01.RadonOuterMeasure
public import Mathlib.MeasureTheory.Measure.Support

@[expose] public section

/-!
# Compact localization for the Carathéodory sigma-algebra

Simon's general locally compact setting need not be sigma-finite.  A set
is nevertheless measurable for a Radon outer measure if its intersection
with each compact set is measurable.  This is a localization principle for
the full Carathéodory sigma-algebra, not a claim of Borel measurability.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/-- Compact-local Carathéodory measurability implies global Carathéodory
measurability, without a countability assumption on the space or measure. -/
theorem IsRadonOuterMeasure.isCaratheodory_of_inter_isCompact
    {μ : OuterMeasure X} (hμ : IsRadonOuterMeasure μ) {S : Set X}
    (hS : ∀ K : Set X, IsCompact K → μ.IsCaratheodory (S ∩ K)) :
    μ.IsCaratheodory S := by
  apply (μ.isCaratheodory_iff_le').mpr
  intro E
  by_cases hE : μ E = ∞
  · simp [hE]
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let ν := hμ.borel_regular.toBorelMeasure
  let : ν.Regular := hμ.toBorelMeasure_regular
  obtain ⟨B, hEB, hB, hμB⟩ := hμ.borel_regular.exists_borel_superset E
  have hBfin : ν B ≠ ∞ := by
    simpa only [ν, hμ.borel_regular.toBorelMeasure_apply_all, hμB] using hE
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨K, _, hK, hBK⟩ := hB.exists_isCompact_sdiff_lt (μ := ν) hBfin
    (ENNReal.coe_ne_zero.mpr hε.ne')
  have htail : μ (B \ K) ≤ (ε : ℝ≥0∞) := by
    exact le_of_lt (by simpa only [ν,
      hμ.borel_regular.toBorelMeasure_apply_all] using hBK)
  have hsub : E ∩ S ⊆ (E ∩ (S ∩ K)) ∪ (B \ K) := by
    intro x hx
    by_cases hxK : x ∈ K
    · exact Or.inl ⟨hx.1, hx.2, hxK⟩
    · exact Or.inr ⟨hEB hx.1, hxK⟩
  calc
    μ (E ∩ S) + μ (E \ S) ≤
        (μ (E ∩ (S ∩ K)) + μ (B \ K)) + μ (E \ (S ∩ K)) := by
      exact add_le_add ((μ.mono hsub).trans (measure_union_le (μ := μ) _ _))
        (μ.mono (sdiff_subset_sdiff_right inter_subset_left))
    _ = μ E + μ (B \ K) := by rw [hS K hK E]; ac_rfl
    _ ≤ μ E + (ε : ℝ≥0∞) := add_le_add le_rfl htail

/-- A function whose measurable preimages are compact-locally measurable
is measurable for the full Carathéodory sigma-algebra. -/
theorem IsRadonOuterMeasure.measurable_of_inter_isCompact
    {μ : OuterMeasure X} (hμ : IsRadonOuterMeasure μ)
    {Y : Type v} [MeasurableSpace Y] {f : X → Y}
    (hf : ∀ K : Set X, IsCompact K → ∀ A : Set Y, MeasurableSet A →
      μ.IsCaratheodory (f ⁻¹' A ∩ K)) :
    @Measurable X Y μ.caratheodory _ f := by
  intro A hA
  exact hμ.isCaratheodory_of_inter_isCompact fun K hK => hf K hK A hA

end Poincare.SimonGMT.Chapter01
