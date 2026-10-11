module

public import Poincare.SimonGMT.Chapter04.SobolevTruncation
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

@[expose] public section

/-!
# The zero-shift step in the Sobolev argument

Continuity from below removes a strictly positive shift in the level sets.
Only the level is shifted; no positive constant is added to a function on
an infinite-measure space.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

/-- A uniform estimate for every positive shift of the strict superlevel
sets passes to the unshifted distribution integral. Neither finite total
measure nor measurability of the underlying function is needed here. -/
theorem lintegral_superlevel_le_of_positive_shifts
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (h : X → ℝ)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) {C : ℝ≥0∞}
    (hbound : ∀ ε : ℝ, 0 < ε →
      (∫⁻ t in Ioi 0, g t * μ {x | t + ε < h x}) ≤ C) :
    (∫⁻ t in Ioi 0, g t * μ {x | t < h x}) ≤ C := by
  let ε : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hεpos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hεanti : Antitone ε := by
    intro i j hij
    dsimp [ε]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hsets (t : ℝ) : Monotone (fun k : ℕ ↦ {x | t + ε k < h x}) := by
    intro i j hij x hx
    change t + ε i < h x at hx
    change t + ε j < h x
    linarith [hεanti hij]
  have hunion (t : ℝ) : {x | t < h x} = ⋃ k : ℕ, {x | t + ε k < h x} := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact mem_iUnion.mpr ⟨k, by dsimp [ε]; linarith⟩
    · intro hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      exact (lt_add_of_pos_right t (hεpos k)).trans hk
  have hmeasure (t : ℝ) : μ {x | t < h x} = ⨆ k : ℕ, μ {x | t + ε k < h x} := by
    rw [hunion]
    exact (hsets t).measure_iUnion
  have hdist (k : ℕ) : Antitone (fun t : ℝ ↦ μ {x | t + ε k < h x}) := by
    intro s t hst
    apply measure_mono
    intro x hx
    change t + ε k < h x at hx
    change s + ε k < h x
    linarith
  have hmono : Monotone (fun k : ℕ ↦ fun t : ℝ ↦ g t * μ {x | t + ε k < h x}) := by
    intro i j hij t
    exact mul_le_mul' le_rfl (measure_mono (hsets t hij))
  calc
    _ = ∫⁻ t in Ioi 0, ⨆ k : ℕ, g t * μ {x | t + ε k < h x} := by
      apply lintegral_congr
      intro t
      rw [hmeasure, ENNReal.mul_iSup]
    _ = ⨆ k : ℕ, ∫⁻ t in Ioi 0, g t * μ {x | t + ε k < h x} :=
      lintegral_iSup (fun k ↦ hg.mul (hdist k).measurable) hmono
    _ ≤ C := iSup_le fun k ↦ hbound (ε k) (hεpos k)

/-- The final real-power cancellation in the Sobolev proof, including
the zero-moment case. -/
theorem rpow_one_sub_le_of_le_rpow_mul {M a C : ℝ} (hM : 0 ≤ M)
    (ha : a < 1) (hC : 0 ≤ C) (hbound : M ≤ C * M ^ a) :
    M ^ (1 - a) ≤ C := by
  rcases eq_or_lt_of_le hM with hzero | hpos
  · rw [← hzero, Real.zero_rpow (by linarith : 1 - a ≠ 0)]
    exact hC
  · rw [Real.rpow_sub hpos, Real.rpow_one]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hpos a)).mpr hbound

end

end Poincare.SimonGMT.Chapter04
