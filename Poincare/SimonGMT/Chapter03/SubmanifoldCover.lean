module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Compactness.Lindelof
public import Poincare.SimonGMT.Chapter02.Submanifold
public import Poincare.SimonGMT.Chapter03.Rectifiable

public section

/-!
# Simon GMT, Chapter 3, Lemma 1.2: the submanifold-cover direction

This file proves the complete easy direction of Lemma 1.2.  A `C¹` chart is
exhausted by compact pieces, is Lipschitz on each piece, and each restricted
map is extended to the whole Euclidean parameter space.  Lindelöf then reduces
the local chart cover of an embedded submanifold to countably many charts.

The converse direction (decomposing arbitrary Lipschitz images into `C¹`
submanifolds off a null set) uses the `C¹` approximation theorem and the full
noninjective area formula, and remains a separate theorem.
-/

open Filter Function MeasureTheory Module Set
open scoped NNReal

namespace Poincare.SimonGMT.Chapter03

universe u

variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- Sigma-compact subsets of a finite-dimensional Borel space are
measurable, since they are countable unions of compact (hence closed) sets. -/
theorem measurableSet_of_isSigmaCompact_borel {S : Set F} (hS : IsSigmaCompact S) :
    MeasurableSet S := by
  obtain ⟨K, hK, rfl⟩ := hS
  exact MeasurableSet.iUnion fun j ↦ (hK j).measurableSet

/-- The image of an open Euclidean domain under a `C¹` map is countably
rectifiable.  Compact exhaustion makes the map Lipschitz piecewise, and the
finite-dimensional extension theorem supplies the global parametrizations
required by Simon Definition 1.1. -/
theorem countablyRectifiable_image_contDiffOn_open
    {n : ℕ} {V : Set (EuclideanSpace ℝ (Fin n))}
    {phi : EuclideanSpace ℝ (Fin n) → F} (hV : IsOpen V)
    (hphi : ContDiffOn ℝ 1 phi V) :
    CountablyRectifiable n (phi '' V) := by
  letI : LocallyCompactSpace V := hV.locallyCompactSpace
  letI : SigmaCompactSpace V := inferInstance
  obtain ⟨K, hKcompact, hKcover⟩ := SigmaCompactSpace.exists_compact_covering (X := V)
  let C : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun j ↦ ((↑) : V → _) '' K j
  have hCcompact : ∀ j, IsCompact (C j) := by
    intro j
    exact (hKcompact j).image continuous_subtype_val
  have hCsub : ∀ j, C j ⊆ V := by
    intro j x hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2
  have hCcover : ⋃ j, C j = V := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      exact hCsub j hxj
    · intro hx
      have hx' : (⟨x, hx⟩ : V) ∈ ⋃ j, K j := by simp [hKcover]
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx'
      exact mem_iUnion_of_mem j ⟨⟨x, hx⟩, hxj, rfl⟩
  have hLip : ∀ j, ∃ L : ℝ≥0, LipschitzOnWith L phi (C j) := by
    intro j
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hCcompact j)
    intro x hx
    obtain ⟨L, t, ht, hphit⟩ :=
      (hphi.contDiffAt (hV.mem_nhds (hCsub j hx))).exists_lipschitzOnWith
    exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hphit⟩
  choose L hLip using hLip
  choose g hgLip hgEq using fun j ↦ (hLip j).extend_finite_dimension
  apply (countablyRectifiable_iUnion (fun j ↦ range (g j))
    (fun j ↦ countablyRectifiable_range (hgLip j))).mono
  intro y hy
  obtain ⟨x, hxV, rfl⟩ := hy
  have hxC : x ∈ ⋃ j, C j := by simpa [hCcover] using hxV
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hxC
  exact mem_iUnion_of_mem j ⟨x, (hgEq j hxj).symm⟩

/-- Every embedded Simon `C¹` `n`-submanifold is countably
`n`-rectifiable. -/
theorem countablyRectifiable_of_isSimonSubmanifold
    {n : ℕ} {N : Set F}
    (hN : Chapter02.IsSimonSubmanifold
      (E := EuclideanSpace ℝ (Fin n)) 1 N) :
    CountablyRectifiable n N := by
  rcases N.eq_empty_or_nonempty with rfl | hne
  · exact countablyRectifiable_of_measure_zero measure_empty
  letI : Nonempty N := hne.to_subtype
  choose V W phi hyW hrep using fun y : N ↦ hN.exists_localRepresentation y.2
  have hcover : N ⊆ ⋃ y : N, W y := by
    intro y hy
    exact mem_iUnion_of_mem ⟨y, hy⟩ (hyW ⟨y, hy⟩)
  obtain ⟨c, hc⟩ :=
    (HereditarilyLindelofSpace.isLindelof N).indexed_countable_subcover
      W (fun y ↦ (hrep y).isOpen_target) hcover
  have hrect : ∀ j, CountablyRectifiable n (W (c j) ∩ N) := by
    intro j
    have h := countablyRectifiable_image_contDiffOn_open
      (hrep (c j)).isOpen_source (hrep (c j)).contDiffOn
    rwa [(hrep (c j)).image_eq] at h
  apply (countablyRectifiable_iUnion (fun j ↦ W (c j) ∩ N) hrect).mono
  intro y hy
  obtain ⟨j, hyW⟩ := mem_iUnion.mp (hc hy)
  exact mem_iUnion_of_mem j ⟨hyW, hy⟩

/-- An embedded Simon `C¹` submanifold is Borel measurable.  Each local
chart image is sigma-compact, and the Lindelöf property supplies a countable
chart cover. -/
theorem measurableSet_of_isSimonSubmanifold
    {n : ℕ} {N : Set F}
    (hN : Chapter02.IsSimonSubmanifold
      (E := EuclideanSpace ℝ (Fin n)) 1 N) :
    MeasurableSet N := by
  rcases N.eq_empty_or_nonempty with rfl | hne
  · exact MeasurableSet.empty
  letI : Nonempty N := hne.to_subtype
  choose V W phi hyW hrep using fun y : N ↦ hN.exists_localRepresentation y.2
  have hcover : N ⊆ ⋃ y : N, W y := by
    intro y hy
    exact mem_iUnion_of_mem ⟨y, hy⟩ (hyW ⟨y, hy⟩)
  obtain ⟨c, hc⟩ :=
    (HereditarilyLindelofSpace.isLindelof N).indexed_countable_subcover
      W (fun y ↦ (hrep y).isOpen_target) hcover
  have hpiece : ∀ j, MeasurableSet (W (c j) ∩ N) := by
    intro j
    rw [← (hrep (c j)).image_eq]
    apply measurableSet_of_isSigmaCompact_borel
    letI : LocallyCompactSpace (V (c j)) := (hrep (c j)).isOpen_source.locallyCompactSpace
    letI : SigmaCompactSpace (V (c j)) := inferInstance
    exact (isSigmaCompact_iff_sigmaCompactSpace.mpr (by infer_instance)).image_of_continuousOn
      (hrep (c j)).contDiffOn.continuousOn
  have hEq : N = ⋃ j, W (c j) ∩ N := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨j, hyW⟩ := mem_iUnion.mp (hc hy)
      exact mem_iUnion_of_mem j ⟨hyW, hy⟩
    · exact iUnion_subset fun _ ↦ inter_subset_right
  rw [hEq]
  exact MeasurableSet.iUnion hpiece

/-- Simon Lemma 1.2, `C¹`-cover-to-rectifiable direction.  A null set and
countably many embedded `C¹` `n`-submanifolds cover only a countably
`n`-rectifiable set. -/
theorem countablyRectifiable_of_submanifold_cover
    {n : ℕ} {M N0 : Set F} {N : ℕ → Set F}
    (hN0 : μHE[n] N0 = 0)
    (hN : ∀ j, Chapter02.IsSimonSubmanifold
      (E := EuclideanSpace ℝ (Fin n)) 1 (N j))
    (hcover : M ⊆ N0 ∪ ⋃ j, N j) :
    CountablyRectifiable n M := by
  have hN0rect : CountablyRectifiable n N0 :=
    countablyRectifiable_of_measure_zero hN0
  let C : ℕ → Set F := fun k ↦ match k with
    | 0 => N0
    | j + 1 => N j
  have hC : ∀ k, CountablyRectifiable n (C k) := by
    intro k
    cases k with
    | zero => exact hN0rect
    | succ j => exact countablyRectifiable_of_isSimonSubmanifold (hN j)
  have hall : CountablyRectifiable n (N0 ∪ ⋃ j, N j) := by
    have hEq : (⋃ k, C k) = N0 ∪ ⋃ j, N j := by
      ext x
      constructor
      · intro hx
        obtain ⟨k, hxk⟩ := mem_iUnion.mp hx
        cases k with
        | zero => exact Or.inl hxk
        | succ j => exact Or.inr (mem_iUnion_of_mem j hxk)
      · rintro (hx0 | hxN)
        · exact mem_iUnion_of_mem 0 hx0
        · obtain ⟨j, hxj⟩ := mem_iUnion.mp hxN
          exact mem_iUnion_of_mem (j + 1) hxj
    rw [← hEq]
    exact countablyRectifiable_iUnion C hC
  exact hall.mono hcover

end Poincare.SimonGMT.Chapter03
