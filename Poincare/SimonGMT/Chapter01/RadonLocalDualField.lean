module

public import Poincare.SimonGMT.Chapter01.RadonFieldGluing
public import Poincare.SimonGMT.Chapter01.LocalFiniteL1Dual

@[expose] public section

/-!
# A compatible bounded dual field for a general Radon measure

Finite Hilbert duality and the compact-support decomposition construct one
Carathéodory-measurable field that agrees with the finite dual field on every
compact set.  Its norm is bounded by one pointwise.  No sigma-finiteness,
second countability, global Borel representative, or globally null remainder
is assumed.

This is the bounded-field gluing step toward Simon 4.14.  The unit-norm polar
representation on the full Carathéodory measure is not asserted here.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.Regular]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The finite dual field on a compact set. -/
noncomputable def compactL1DualField (C : Set X) (hC : IsCompact C)
    (T : Lp H 1 μ →L[ℝ] ℝ) (hT : ‖T‖ ≤ 1) : X → H := by
  letI : Fact (μ C < ∞) := ⟨hC.measure_lt_top⟩
  exact boundedFiniteRestrictedL1Field μ hC.measurableSet T hT

omit [LocallyCompactSpace X] in
theorem compactL1DualField_stronglyMeasurable (C : Set X) (hC : IsCompact C)
    (T : Lp H 1 μ →L[ℝ] ℝ) (hT : ‖T‖ ≤ 1) :
    StronglyMeasurable (compactL1DualField μ C hC T hT) := by
  let : Fact (μ C < ∞) := ⟨hC.measure_lt_top⟩
  exact (boundedFiniteRestrictedL1Field_spec μ hC.measurableSet T hT).1

omit [LocallyCompactSpace X] in
theorem compactL1DualField_norm_le_one (C : Set X) (hC : IsCompact C)
    (T : Lp H 1 μ →L[ℝ] ℝ) (hT : ‖T‖ ≤ 1) (x : X) :
    ‖compactL1DualField μ C hC T hT x‖ ≤ 1 := by
  let : Fact (μ C < ∞) := ⟨hC.measure_lt_top⟩
  exact (boundedFiniteRestrictedL1Field_spec μ hC.measurableSet T hT).2.1 x

omit [LocallyCompactSpace X] in
theorem compactL1DualField_ae_eq_inter (C : Set X) (hC : IsCompact C)
    (D : Set X) (hD : IsCompact D) (T : Lp H 1 μ →L[ℝ] ℝ) (hT : ‖T‖ ≤ 1) :
    compactL1DualField μ C hC T hT =ᵐ[μ.restrict (C ∩ D)]
      compactL1DualField μ D hD T hT := by
  let : Fact (μ C < ∞) := ⟨hC.measure_lt_top⟩
  let : Fact (μ D < ∞) := ⟨hD.measure_lt_top⟩
  exact boundedFiniteRestrictedL1Field_ae_eq_inter μ hC.measurableSet hD.measurableSet T hT

/-- Finite-piece representatives glue to one globally Carathéodory-measurable,
pointwise bounded field agreeing with the finite dual on every compact set.
The last almost-everywhere assertion is taken separately on each compact. -/
theorem exists_radon_local_L1_dual_field [MeasurableSpace H] [BorelSpace H]
    (T : Lp H 1 μ →L[ℝ] ℝ) (hT : ‖T‖ ≤ 1) :
    ∃ ν : X → H, @Measurable X H μ.toOuterMeasure.caratheodory _ ν ∧
      (∀ x, ‖ν x‖ ≤ 1) ∧
      ∀ (C : Set X) (hC : IsCompact C),
        ν =ᵐ[μ.restrict C] compactL1DualField μ C hC T hT := by
  obtain ⟨ι, K, hK, hdisj, hcount, hcover⟩ :=
    exists_compact_support_local_decomposition μ
  let f : ι → X → H := fun i => compactL1DualField μ (K i) (hK i).1 T hT
  have hf (i : ι) : Measurable (f i) :=
    (compactL1DualField_stronglyMeasurable μ (K i) (hK i).1 T hT).measurable
  obtain ⟨ν, hν, hνK, hvalues⟩ := exists_measurable_gluing_on_compact_supports μ K
    (fun i => (hK i).1) hdisj f hf 0
  refine ⟨ν, hν, ?_, ?_⟩
  · intro x
    rcases hvalues x with hx | ⟨i, _, hx⟩
    · simp [hx]
    · rw [hx]
      exact compactL1DualField_norm_le_one μ (K i) (hK i).1 T hT x
  · intro C hC
    let J : Set ι := {i | ((μ.restrict (K i)).support ∩ C).Nonempty}
    have hJ : J.Countable := hcount C hC
    have hae : ∀ᵐ x ∂μ, ∀ i ∈ J,
        x ∈ K i → x ∈ C → ν x = compactL1DualField μ C hC T hT x := by
      apply (ae_ball_iff hJ).mpr
      intro i _
      have hi := compactL1DualField_ae_eq_inter μ (K i) (hK i).1 C hC T hT
      filter_upwards [(ae_restrict_iff' (hK i).1.measurableSet).mp (hνK i),
        (ae_restrict_iff' ((hK i).1.measurableSet.inter hC.measurableSet)).mp hi]
        with x hx hxi hxK hxC
      exact (hx hxK).trans (hxi ⟨hxK, hxC⟩)
    apply (ae_restrict_iff' hC.measurableSet).mpr
    filter_upwards [ae_le_set.mpr (hcover C hC), hae] with x hx hxi hxC
    obtain ⟨i, hxS⟩ := mem_iUnion.mp (hx hxC)
    exact hxi i ⟨x, hxS, hxC⟩
      (support_restrict_subset_of_isCompact μ (hK i).1 hxS) hxC

end Poincare.SimonGMT.Chapter01
