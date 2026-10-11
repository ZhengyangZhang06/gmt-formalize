module

public import Poincare.SimonGMT.Chapter03.Rectifiable

public section

/-!
# Simon GMT, Chapter 3, Remark 1.3: disjointifying a rectifiable cover

Remark 1.3 replaces the null-set/manifold cover supplied by Lemma 1.2 with a
measurable disjoint partition.  The construction is purely set-theoretic: a
point is assigned to the first member of the cover which contains it.  This
file proves the construction once, independently of how the cover was
obtained, and records the Hausdorff-null conclusion for the zeroth piece.
-/

open MeasureTheory Set

namespace Poincare.SimonGMT.Chapter03

universe u

variable {X : Type u}

/-- The part of `M` assigned to the `j`th member of a countable cover.  Earlier
cover members are removed, exactly as in the inductive construction printed
in Simon Remark 1.3. -/
def disjointCoverPiece (M : Set X) (N : ℕ → Set X) (j : ℕ) : Set X :=
  (M ∩ N j) \ ⋃ i : Fin j, N i

theorem disjointCoverPiece_subset_left (M : Set X) (N : ℕ → Set X) (j : ℕ) :
    disjointCoverPiece M N j ⊆ M := by
  intro x hx
  exact hx.1.1

theorem disjointCoverPiece_subset_right (M : Set X) (N : ℕ → Set X) (j : ℕ) :
    disjointCoverPiece M N j ⊆ N j := by
  intro x hx
  exact hx.1.2

/-- Distinct first-cover pieces are disjoint. -/
theorem disjointCoverPiece_pairwiseDisjoint (M : Set X) (N : ℕ → Set X) :
    (Set.univ : Set ℕ).PairwiseDisjoint (disjointCoverPiece M N) := by
  rw [Set.pairwiseDisjoint_iff]
  intro i _ j _ hnonempty
  obtain ⟨x, hxi, hxj⟩ := hnonempty
  by_contra hij
  rcases Nat.lt_or_gt_of_ne hij with hij | hji
  · have hxprev : x ∈ ⋃ k : Fin j, N k :=
      mem_iUnion_of_mem ⟨i, hij⟩ hxi.1.2
    exact hxj.2 hxprev
  · have hxprev : x ∈ ⋃ k : Fin i, N k :=
      mem_iUnion_of_mem ⟨j, hji⟩ hxj.1.2
    exact hxi.2 hxprev

/-- The first-cover pieces exhaust `M` whenever the given family covers
`M`.  The reverse inclusion holds without any measurability assumptions. -/
theorem iUnion_disjointCoverPiece_eq
    (M : Set X) (N : ℕ → Set X) (hcover : M ⊆ ⋃ j, N j) :
    ⋃ j, disjointCoverPiece M N j = M := by
  classical
  apply Subset.antisymm
  · exact iUnion_subset fun j ↦ disjointCoverPiece_subset_left M N j
  · intro x hxM
    have hex : ∃ j, x ∈ N j := mem_iUnion.mp (hcover hxM)
    let j := Nat.find hex
    refine mem_iUnion_of_mem j ⟨⟨hxM, Nat.find_spec hex⟩, ?_⟩
    intro hxEarlier
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxEarlier
    exact (Nat.find_min hex i.isLt) hxi

theorem measurableSet_disjointCoverPiece
    [MeasurableSpace X] {M : Set X} {N : ℕ → Set X}
    (hM : MeasurableSet M) (hN : ∀ j, MeasurableSet (N j)) (j : ℕ) :
    MeasurableSet (disjointCoverPiece M N j) := by
  exact (hM.inter (hN j)).diff (MeasurableSet.iUnion fun i ↦ hN i)

theorem nullMeasurableSet_disjointCoverPiece
    [MeasurableSpace X] {M : Set X} {N : ℕ → Set X} {mu : Measure X}
    (hM : NullMeasurableSet M mu) (hN : ∀ j, NullMeasurableSet (N j) mu)
    (j : ℕ) :
    NullMeasurableSet (disjointCoverPiece M N j) mu := by
  exact (hM.inter (hN j)).diff (NullMeasurableSet.iUnion fun i ↦ hN i)

/-- Simon Remark 1.3.  Given the null-set/manifold cover produced by Lemma
1.2, the sets `M j` may be chosen measurable, pairwise disjoint, subordinate
to the corresponding `N j`, and with null zeroth piece.  The statement is
measure-generic; instantiate `mu` with `muHE[n]` for the book's formulation.
-/
theorem simon_remark_1_3
    [MeasurableSpace X] {mu : Measure X} {M : Set X} {N : ℕ → Set X}
    (hM : MeasurableSet M) (hN : ∀ j, MeasurableSet (N j))
    (hN0 : mu (N 0) = 0) (hcover : M ⊆ ⋃ j, N j) :
    ∃ P : ℕ → Set X,
      (⋃ j, P j) = M ∧
      (Set.univ : Set ℕ).PairwiseDisjoint P ∧
      (∀ j, P j ⊆ N j) ∧
      (∀ j, MeasurableSet (P j)) ∧
      mu (P 0) = 0 := by
  refine ⟨disjointCoverPiece M N, iUnion_disjointCoverPiece_eq M N hcover,
    disjointCoverPiece_pairwiseDisjoint M N, ?_, ?_, ?_⟩
  · exact fun j ↦ disjointCoverPiece_subset_right M N j
  · exact fun j ↦ measurableSet_disjointCoverPiece hM hN j
  · exact measure_mono_null (disjointCoverPiece_subset_right M N 0) hN0

/-- Simon Remark 1.3 in the completed-measure formulation used by the book.
Unlike `simon_remark_1_3`, this version only asks for null measurability; in
particular the null exceptional cover member need not be Borel measurable. -/
theorem simon_remark_1_3_nullMeasurable
    [MeasurableSpace X] {mu : Measure X} {M : Set X} {N : ℕ → Set X}
    (hM : NullMeasurableSet M mu) (hN : ∀ j, NullMeasurableSet (N j) mu)
    (hN0 : mu (N 0) = 0) (hcover : M ⊆ ⋃ j, N j) :
    ∃ P : ℕ → Set X,
      (⋃ j, P j) = M ∧
      (Set.univ : Set ℕ).PairwiseDisjoint P ∧
      (∀ j, P j ⊆ N j) ∧
      (∀ j, NullMeasurableSet (P j) mu) ∧
      mu (P 0) = 0 := by
  refine ⟨disjointCoverPiece M N, iUnion_disjointCoverPiece_eq M N hcover,
    disjointCoverPiece_pairwiseDisjoint M N, ?_, ?_, ?_⟩
  · exact fun j ↦ disjointCoverPiece_subset_right M N j
  · exact fun j ↦ nullMeasurableSet_disjointCoverPiece hM hN j
  · exact measure_mono_null (disjointCoverPiece_subset_right M N 0) hN0

end Poincare.SimonGMT.Chapter03
