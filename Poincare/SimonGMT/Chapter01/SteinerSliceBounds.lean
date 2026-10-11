module

public import Poincare.SimonGMT.Chapter01.IsodiametricBounds

@[expose] public section

/-!
# The one-dimensional slice step for Steiner symmetrization

Centering two nonempty real slices, while preserving their lengths, cannot
increase the largest distance between them.  These lemmas use actual Lebesgue
outer measure and do not require the slices to be measurable.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Poincare.SimonGMT.Chapter01

/-- If every point of one nonempty real slice is within `d` of every point
of another, the sum of their outer lengths is at most `2d`. -/
theorem volume_add_le_twice_of_cross_dist_le
    {A B : Set ℝ} (hA : A.Nonempty) (hB : B.Nonempty) {d : ℝ}
    (hcross : ∀ a ∈ A, ∀ b ∈ B, dist a b ≤ d) :
    volume A + volume B ≤ ENNReal.ofReal (2 * d) := by
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  have hdist (a : ℝ) (ha : a ∈ A) (b : ℝ) (hb : b ∈ B) :
      a - b ≤ d ∧ b - a ≤ d :=
    abs_sub_le_iff.mp (by simpa only [Real.dist_eq] using hcross a ha b hb)
  have hAl : BddBelow A := ⟨b₀ - d, fun a ha => by have := (hdist a ha b₀ hb₀).2; linarith⟩
  have hAu : BddAbove A := ⟨b₀ + d, fun a ha => by have := (hdist a ha b₀ hb₀).1; linarith⟩
  have hBl : BddBelow B := ⟨a₀ - d, fun b hb => by have := (hdist a₀ ha₀ b hb).1; linarith⟩
  have hBu : BddAbove B := ⟨a₀ + d, fun b hb => by have := (hdist a₀ ha₀ b hb).2; linarith⟩
  have hAB : sSup A ≤ d + sInf B := by
    apply csSup_le ⟨a₀, ha₀⟩
    intro a ha
    have h : a - d ≤ sInf B := le_csInf ⟨b₀, hb₀⟩ fun b hb => by
      have := (hdist a ha b hb).1
      linarith
    linarith
  have hBA : sSup B ≤ d + sInf A := by
    apply csSup_le ⟨b₀, hb₀⟩
    intro b hb
    have h : b - d ≤ sInf A := le_csInf ⟨a₀, ha₀⟩ fun a ha => by
      have := (hdist a ha b hb).2
      linarith
    linarith
  have hwidthA : 0 ≤ sSup A - sInf A :=
    sub_nonneg.mpr ((csInf_le hAl ha₀).trans (le_csSup hAu ha₀))
  have hwidthB : 0 ≤ sSup B - sInf B :=
    sub_nonneg.mpr ((csInf_le hBl hb₀).trans (le_csSup hBu hb₀))
  calc
    volume A + volume B ≤
        volume (Icc (sInf A) (sSup A)) + volume (Icc (sInf B) (sSup B)) :=
      add_le_add (measure_mono (subset_Icc_csInf_csSup hAl hAu))
        (measure_mono (subset_Icc_csInf_csSup hBl hBu))
    _ = ENNReal.ofReal ((sSup A - sInf A) + (sSup B - sInf B)) := by
      rw [Real.volume_Icc, Real.volume_Icc, ENNReal.ofReal_add hwidthA hwidthB]
    _ ≤ ENNReal.ofReal (2 * d) := ENNReal.ofReal_le_ofReal (by linarith)

/-- Centering two real slices does not increase the maximal cross-distance. -/
theorem dist_le_of_abs_le_half_volume
    {A B : Set ℝ} (hA : A.Nonempty) (hB : B.Nonempty) {d : ℝ}
    (hcross : ∀ a ∈ A, ∀ b ∈ B, dist a b ≤ d) {x y : ℝ}
    (hx : |x| ≤ (volume A).toReal / 2) (hy : |y| ≤ (volume B).toReal / 2) :
    dist x y ≤ d := by
  have hsum := volume_add_le_twice_of_cross_dist_le hA hB hcross
  have hfin : volume A + volume B ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
  have hAfin : volume A ≠ ∞ := (ENNReal.add_ne_top.mp hfin).1
  have hBfin : volume B ≠ ∞ := (ENNReal.add_ne_top.mp hfin).2
  have hd : 0 ≤ d := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    exact dist_nonneg.trans (hcross a ha b hb)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
  rw [ENNReal.toReal_add hAfin hBfin, ENNReal.toReal_ofReal (by positivity)] at hreal
  calc
    dist x y = |x - y| := Real.dist_eq _ _
    _ ≤ |x| + |y| := abs_sub _ _
    _ ≤ (volume A).toReal / 2 + (volume B).toReal / 2 := add_le_add hx hy
    _ ≤ d := by linarith

/-- The centered interval replacing a real slice in Simon's Steiner
construction; an empty slice remains empty. -/
noncomputable def simonCenteredSlice (A : Set ℝ) : Set ℝ :=
  {x | A.Nonempty ∧ |x| ≤ (volume A).toReal / 2}

/-- The centered slice is a Borel set. -/
theorem isClosed_simonCenteredSlice (A : Set ℝ) : IsClosed (simonCenteredSlice A) := by
  by_cases hA : A.Nonempty
  · simpa [simonCenteredSlice, hA] using
      isClosed_le continuous_abs (continuous_const (y := (volume A).toReal / 2))
  · simp [simonCenteredSlice, hA]

/-- Centering preserves the outer length of every finite-length real slice. -/
theorem volume_simonCenteredSlice {A : Set ℝ} (hfin : volume A ≠ ∞) :
    volume (simonCenteredSlice A) = volume A := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp [simonCenteredSlice]
  · have hinterval : simonCenteredSlice A =
        Icc (-(volume A).toReal / 2) ((volume A).toReal / 2) := by
      ext x
      simp [simonCenteredSlice, hA, abs_le, neg_div]
    rw [hinterval, Real.volume_Icc]
    convert ENNReal.ofReal_toReal hfin using 1
    congr 1
    ring

/-- Each centered slice is invariant under reflection. -/
theorem neg_mem_simonCenteredSlice {A : Set ℝ} {x : ℝ} (hx : x ∈ simonCenteredSlice A) :
    -x ∈ simonCenteredSlice A := by
  simpa only [simonCenteredSlice, mem_ofPred_eq, abs_neg] using hx

/-- The cross-distance bound survives centering, including empty slices. -/
theorem dist_le_simonCenteredSlice
    {A B : Set ℝ} {d : ℝ} (hcross : ∀ a ∈ A, ∀ b ∈ B, dist a b ≤ d)
    {x y : ℝ} (hx : x ∈ simonCenteredSlice A) (hy : y ∈ simonCenteredSlice B) :
    dist x y ≤ d :=
  dist_le_of_abs_le_half_volume hx.1 hy.1 hcross hx.2 hy.2

end Poincare.SimonGMT.Chapter01
