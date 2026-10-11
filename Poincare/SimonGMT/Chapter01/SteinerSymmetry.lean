module

public import Poincare.SimonGMT.Chapter01.SteinerVolume

@[expose] public section

/-!
# Successive coordinate symmetrizations

A finite sequence of compact Steiner replacements makes a compact set
centrally symmetric, without increasing diameter or decreasing volume.
-/

open Metric Set MeasureTheory
open scoped ENNReal

namespace Poincare.SimonGMT.Chapter01

/-- Reflection in the `j`-th coordinate hyperplane. -/
def simonCoordinateReflection {n : ℕ} (j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (Function.update x.ofLp j (-x j))

@[simp] theorem simonCoordinateReflection_same {n : ℕ} (j : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : simonCoordinateReflection j x j = -x j := by
  simp [simonCoordinateReflection]

theorem simonCoordinateReflection_of_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (x : EuclideanSpace ℝ (Fin n)) : simonCoordinateReflection j x i = x i :=
  Function.update_of_ne hij _ _

@[simp] theorem simonCoordinateReflection_involutive {n : ℕ} (j : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    simonCoordinateReflection j (simonCoordinateReflection j x) = x := by
  ext i
  by_cases hij : i = j
  · subst i
    simp
  · simp only [simonCoordinateReflection_of_ne hij]

/-- Coordinate reflection is continuous. -/
theorem continuous_simonCoordinateReflection {n : ℕ} (j : Fin n) :
    Continuous (simonCoordinateReflection j : EuclideanSpace ℝ (Fin n) → _) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
  apply continuous_pi
  intro i
  by_cases hij : i = j
  · subst i
    simpa only [Function.update_self] using
      (show Continuous (fun x : EuclideanSpace ℝ (Fin n) => -x j) by fun_prop)
  · simpa only [Function.update_of_ne hij] using
      (show Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) by fun_prop)

theorem simonCoordinateSlice_reflection_same {n : ℕ} (j : Fin n)
    (A : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    simonCoordinateSlice j A (simonCoordinateReflection j x) = simonCoordinateSlice j A x := by
  ext t
  change (WithLp.toLp 2 (Function.update (Function.update x.ofLp j (-x j)) j t) ∈ A) ↔ _
  rw [Function.update_idem]
  rfl

theorem simonCoordinateReflection_update {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    simonCoordinateReflection i (WithLp.toLp 2 (Function.update x.ofLp j t)) =
      WithLp.toLp 2 (Function.update (simonCoordinateReflection i x).ofLp j t) := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [simonCoordinateReflection, hij]
  · by_cases hkj : k = j
    · subst k
      simp [simonCoordinateReflection, hij, Ne.symm hij]
    · simp [simonCoordinateReflection, Function.update_apply, hki, hkj]

theorem simonCoordinateSlice_reflection_of_symmetry {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : ∀ x ∈ A, simonCoordinateReflection i x ∈ A)
    (x : EuclideanSpace ℝ (Fin n)) :
    simonCoordinateSlice j A (simonCoordinateReflection i x) = simonCoordinateSlice j A x := by
  ext t
  change (WithLp.toLp 2 (Function.update (simonCoordinateReflection i x).ofLp j t) ∈ A) ↔
    WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A
  rw [← simonCoordinateReflection_update hij]
  constructor
  · intro h
    simpa only [simonCoordinateReflection_involutive] using hA _ h
  · exact hA _

/-- Symmetrization creates reflection symmetry in its chosen coordinate. -/
theorem simonSteinerSymmetrization_reflection {n : ℕ} (j : Fin n)
    (A : Set (EuclideanSpace ℝ (Fin n))) :
    ∀ x ∈ simonSteinerSymmetrization j A,
      simonCoordinateReflection j x ∈ simonSteinerSymmetrization j A := by
  intro x hx
  change simonCoordinateReflection j x j ∈
    simonCenteredSlice (simonCoordinateSlice j A (simonCoordinateReflection j x))
  rw [simonCoordinateReflection_same, simonCoordinateSlice_reflection_same]
  exact neg_mem_simonCenteredSlice hx

/-- Symmetrization preserves reflection symmetry in every other coordinate. -/
theorem simonSteinerSymmetrization_preserves_reflection {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : ∀ x ∈ A, simonCoordinateReflection i x ∈ A) :
    ∀ x ∈ simonSteinerSymmetrization j A,
      simonCoordinateReflection i x ∈ simonSteinerSymmetrization j A := by
  intro x hx
  change simonCoordinateReflection i x j ∈
    simonCenteredSlice (simonCoordinateSlice j A (simonCoordinateReflection i x))
  rw [simonCoordinateReflection_of_ne hij.symm, simonCoordinateSlice_reflection_of_symmetry hij hA]
  exact hx

theorem coordinate_reflection_mem_closure {n : ℕ} (i : Fin n)
    {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : ∀ x ∈ A, simonCoordinateReflection i x ∈ A) :
    ∀ x ∈ closure A, simonCoordinateReflection i x ∈ closure A := by
  intro x hx
  have hsub : A ⊆ simonCoordinateReflection i ⁻¹' closure A :=
    fun y hy => subset_closure (hA y hy)
  exact closure_minimal hsub
    (isClosed_closure.preimage (continuous_simonCoordinateReflection i)) hx

theorem simonCompactSteiner_reflection {n : ℕ} (j : Fin n)
    (A : Set (EuclideanSpace ℝ (Fin n))) :
    ∀ x ∈ simonCompactSteiner j A,
      simonCoordinateReflection j x ∈ simonCompactSteiner j A :=
  coordinate_reflection_mem_closure j (simonSteinerSymmetrization_reflection j A)

theorem simonCompactSteiner_preserves_reflection {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : ∀ x ∈ A, simonCoordinateReflection i x ∈ A) :
    ∀ x ∈ simonCompactSteiner j A,
      simonCoordinateReflection i x ∈ simonCompactSteiner j A :=
  coordinate_reflection_mem_closure i (simonSteinerSymmetrization_preserves_reflection hij hA)

/-- Reflection symmetry in every coordinate implies central symmetry. -/
theorem neg_mem_of_coordinate_reflections {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : ∀ i, ∀ x ∈ A, simonCoordinateReflection i x ∈ A) :
    ∀ x ∈ A, -x ∈ A := by
  intro x hx
  have hmem (s : Finset (Fin n)) :
      WithLp.toLp 2 (fun k => if k ∈ s then -x k else x k) ∈ A := by
    induction s using Finset.induction_on with
    | empty => simpa using hx
    | @insert i s hi ih =>
      have h := hA i _ ih
      convert h using 1
      ext k
      by_cases hki : k = i
      · subst k
        simp [simonCoordinateReflection, hi]
      · simp [simonCoordinateReflection, hki]
  have heq : (WithLp.toLp 2 fun k => -x k) = -x := by
    ext k
    rfl
  simpa only [Finset.mem_univ, ite_true, heq] using hmem Finset.univ

/-- Successive coordinate symmetrizations produce a centrally symmetric
compact replacement with no larger diameter and no smaller volume. -/
theorem exists_centrally_symmetric_compact_replacement {n : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A) :
    ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧ ediam K ≤ ediam A ∧
      volume A ≤ volume K ∧ ∀ x ∈ K, -x ∈ K := by
  have hfinite (s : Finset (Fin n)) :
      ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧ ediam K ≤ ediam A ∧
        volume A ≤ volume K ∧ ∀ i ∈ s, ∀ x ∈ K, simonCoordinateReflection i x ∈ K := by
    induction s using Finset.induction_on with
    | empty => exact ⟨A, hA, le_rfl, le_rfl, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨K, hK, hdiam, hvol, hsym⟩ := ih
      refine ⟨simonCompactSteiner i K, isCompact_simonCompactSteiner i hK,
        (ediam_simonCompactSteiner_le i K).trans hdiam,
        hvol.trans (volume_le_volume_simonCompactSteiner i hK), ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with hki | hk
      · subst k
        exact simonCompactSteiner_reflection i K
      · apply simonCompactSteiner_preserves_reflection
        · intro hki
          subst k
          exact hi hk
        · exact hsym k hk
  obtain ⟨K, hK, hdiam, hvol, hsym⟩ := hfinite Finset.univ
  exact ⟨K, hK, hdiam, hvol,
    neg_mem_of_coordinate_reflections (fun i => hsym i (Finset.mem_univ i))⟩

end Poincare.SimonGMT.Chapter01
