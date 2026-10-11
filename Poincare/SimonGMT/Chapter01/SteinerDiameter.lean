module

public import Poincare.SimonGMT.Chapter01.SteinerSliceBounds

@[expose] public section

/-!
# Coordinate Steiner symmetrization does not increase diameter

The coordinate slices are centered using their actual Lebesgue outer lengths.
This is Simon's geometric diameter step.  No measurability hypothesis is
needed for this step; volume preservation of the assembled higher-dimensional
set is a separate obligation.
-/

open Metric Set MeasureTheory
open scoped ENNReal

namespace Poincare.SimonGMT.Chapter01

/-- Replacing one coordinate changes squared Euclidean distance by exactly
the change in that coordinate's squared distance. -/
theorem euclidean_dist_sq_coordinate_update {n : ℕ} (j : Fin n)
    (x y : EuclideanSpace ℝ (Fin n)) (a b : ℝ) :
    dist (WithLp.toLp 2 (Function.update x.ofLp j a))
      (WithLp.toLp 2 (Function.update y.ofLp j b)) ^ 2 =
      dist x y ^ 2 - dist (x j) (y j) ^ 2 + dist a b ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
  have hsum := Finset.sum_erase_add Finset.univ
    (fun i : Fin n => dist (x i) (y i) ^ 2) (Finset.mem_univ j)
  have hsum' := Finset.sum_erase_add Finset.univ
    (fun i : Fin n => dist (Function.update x.ofLp j a i)
      (Function.update y.ofLp j b i) ^ 2) (Finset.mem_univ j)
  have hrest : (∑ i ∈ Finset.univ.erase j,
      dist (Function.update x.ofLp j a i) (Function.update y.ofLp j b i) ^ 2) =
      ∑ i ∈ Finset.univ.erase j, dist (x i) (y i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [hrest, Function.update_self, Function.update_self] at hsum'
  linarith

/-- The real slice through `x`, parallel to the `j`-th coordinate axis. -/
def simonCoordinateSlice {n : ℕ} (j : Fin n)
    (A : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) : Set ℝ :=
  {t | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A}

/-- Simon's coordinate Steiner symmetrization: each nonempty coordinate
slice is replaced by the centered interval of the same length. -/
noncomputable def simonSteinerSymmetrization {n : ℕ} (j : Fin n)
    (A : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x j ∈ simonCenteredSlice (simonCoordinateSlice j A x)}

/-- Steiner symmetrization along one coordinate does not increase extended
diameter, for any set in finite-dimensional Euclidean space. -/
theorem ediam_simonSteinerSymmetrization_le {n : ℕ} (j : Fin n)
    (A : Set (EuclideanSpace ℝ (Fin n))) :
    ediam (simonSteinerSymmetrization j A) ≤ ediam A := by
  by_cases hfin : ediam A = ∞
  · rw [hfin]
    exact le_top
  have hbounded : Bornology.IsBounded A := isBounded_iff_ediam_ne_top.mpr hfin
  have hdiam : ediam (simonSteinerSymmetrization j A) ≤ ENNReal.ofReal (diam A) := by
    apply ediam_le_of_forall_dist_le
    intro x hx y hy
    change x j ∈ simonCenteredSlice (simonCoordinateSlice j A x) at hx
    change y j ∈ simonCenteredSlice (simonCoordinateSlice j A y) at hy
    let D : ℝ := diam A ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2
    have hsq (a : ℝ) (ha : a ∈ simonCoordinateSlice j A x)
        (b : ℝ) (hb : b ∈ simonCoordinateSlice j A y) : dist a b ^ 2 ≤ D := by
      have hd := dist_le_diam_of_mem hbounded ha hb
      have hsq' : dist (WithLp.toLp 2 (Function.update x.ofLp j a))
          (WithLp.toLp 2 (Function.update y.ofLp j b)) ^ 2 ≤ diam A ^ 2 :=
        pow_le_pow_left₀ dist_nonneg hd 2
      rw [euclidean_dist_sq_coordinate_update] at hsq'
      dsimp [D]
      linarith
    have hD : 0 ≤ D := by
      obtain ⟨a, ha⟩ := hx.1
      obtain ⟨b, hb⟩ := hy.1
      exact (sq_nonneg (dist a b)).trans (hsq a ha b hb)
    have hcross : ∀ a ∈ simonCoordinateSlice j A x,
        ∀ b ∈ simonCoordinateSlice j A y, dist a b ≤ Real.sqrt D := by
      intro a ha b hb
      have h := hsq a ha b hb
      have hsqrt := Real.sq_sqrt hD
      nlinarith [dist_nonneg (x := a) (y := b), Real.sqrt_nonneg D]
    have hcentered := dist_le_simonCenteredSlice hcross hx hy
    have hsqrt := Real.sq_sqrt hD
    have hcentered_sq : dist (x j) (y j) ^ 2 ≤ D := by
      nlinarith [dist_nonneg (x := x j) (y := y j), Real.sqrt_nonneg D]
    dsimp [D] at hcentered_sq
    nlinarith [dist_nonneg (x := x) (y := y), diam_nonneg (s := A)]
  simpa only [diam, ENNReal.ofReal_toReal hfin] using hdiam

end Poincare.SimonGMT.Chapter01
