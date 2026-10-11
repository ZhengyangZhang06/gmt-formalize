module

public import Poincare.SimonGMT.Chapter03.Differential
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# Simon GMT, Chapter 3, Lemma 3.3: coordinate projections

This file proves the finite-dimensional linear-algebra claim at the start of
the proof of Lemma 3.3.  Every `n`-plane in a coordinate Euclidean space has
`n` distinct coordinate directions for which the corresponding coordinate
projection restricts to an isomorphism on the plane.
-/

open Function Module Set

namespace Poincare.SimonGMT.Chapter03

noncomputable section

/-- The `j`th ambient coordinate, restricted to a linear subspace. -/
def coordinateFunctional {N : ℕ}
    (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (j : Fin N) : Module.Dual ℝ P :=
  (EuclideanSpace.projₗ j).comp P.subtype

@[simp] theorem coordinateFunctional_apply {N : ℕ}
    (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (j : Fin N) (x : P) :
    coordinateFunctional P j x = (x : EuclideanSpace ℝ (Fin N)) j :=
  rfl

/-- Extract the selected coordinates of a vector in `P`. -/
def selectedCoordinateMap {n N : ℕ}
    (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (j : Fin n → Fin N) :
    P →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun i ↦ coordinateFunctional P (j i)

@[simp] theorem selectedCoordinateMap_apply {n N : ℕ}
    (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (j : Fin n → Fin N)
    (x : P) (i : Fin n) :
    selectedCoordinateMap P j x i = (x : EuclideanSpace ℝ (Fin N)) (j i) :=
  rfl

/-- The ambient coordinate functionals span the dual of every subspace. -/
theorem span_range_coordinateFunctional_eq_top {N : ℕ}
    (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))) :
    Submodule.span ℝ (Set.range (coordinateFunctional P)) = ⊤ := by
  apply Submodule.span_eq_top_of_ne_zero
  intro x hx
  have hex : ∃ j : Fin N, (x : EuclideanSpace ℝ (Fin N)) j ≠ 0 := by
    by_contra! h
    apply hx
    ext j
    exact h j
  obtain ⟨j, hj⟩ := hex
  exact ⟨coordinateFunctional P j, Set.mem_range_self j, by simpa using hj⟩

/-- The linear-algebra assertion used in Simon Lemma 3.3: some `n` distinct
ambient coordinates give an isomorphism on every `n`-plane.  The map here is
the coordinate form of the orthogonal projection onto the span of the chosen
standard basis vectors. -/
theorem exists_bijective_selectedCoordinateMap {n N : ℕ}
    (P : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (hP : finrank ℝ P = n) :
    ∃ j : Fin n → Fin N, Function.Injective j ∧
      Function.Bijective (selectedCoordinateMap P j) := by
  have hspan := span_range_coordinateFunctional_eq_top P
  have hdual : finrank ℝ (Module.Dual ℝ P) = n := by
    rw [Subspace.dual_finrank_eq, hP]
  obtain ⟨f, hf_mem, hf_span, hf_indep⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ
      (Set.range (coordinateFunctional P))
  rw [hspan, finrank_top, hdual] at f hf_mem hf_span hf_indep
  choose j hj using hf_mem
  have hj_inj : Function.Injective j := by
    intro a b hab
    apply hf_indep.injective
    rw [← hj a, ← hj b, hab]
  have hmap_inj : Function.Injective (selectedCoordinateMap P j) := by
    intro x y hxy
    let z : P := x - y
    have hzmap : selectedCoordinateMap P j z = 0 := by
      dsimp [z]
      rw [map_sub, hxy, sub_self, map_zero]
    have hzfi (i : Fin n) : f i z = 0 := by
      rw [← hj i]
      exact congrFun hzmap i
    have hle : Submodule.span ℝ (Set.range f) ≤
        LinearMap.ker (Module.Dual.eval ℝ P z) := by
      rw [Submodule.span_le]
      rintro g ⟨i, rfl⟩
      rw [LinearMap.mem_ker]
      exact hzfi i
    have heval : Module.Dual.eval ℝ P z = 0 := by
      apply LinearMap.ext
      intro g
      have hg : g ∈ Submodule.span ℝ (Set.range f) := by rw [hf_span]; trivial
      exact LinearMap.mem_ker.mp (hle hg)
    have hz : z = 0 := by
      apply (Module.evalEquiv ℝ P).injective
      simpa using heval
    exact sub_eq_zero.mp hz
  have hdim : finrank ℝ P = finrank ℝ (Fin n → ℝ) := by
    simpa [hP]
  refine ⟨j, hj_inj, hmap_inj, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hmap_inj

end

end Poincare.SimonGMT.Chapter03
