module

public import Poincare.SimonGMT.Chapter04.SobolevCovering

@[expose] public section

/-!
# The all-radius lower-bound error in printed Lemma 5.8

On printed page 98, `f` is bounded on `(0,∞)` while the displayed
hypothesis requires `1 ≤ σ⁻ⁿ f(σ)` for every `0 < σ < ρ < ∞`.
For positive dimension these hypotheses are inconsistent. This file
proves that obstruction; it does not claim the useful good-radius lemma
from a corrected lower-limit hypothesis.
-/

open Set

namespace Poincare.SimonGMT.Chapter04

/-- An all-positive-radius normalized lower bound is incompatible with
bounded mass when the dimension is positive. -/
theorem not_bddAbove_of_one_le_normalized (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ)
    (hlower : ∀ r : ℝ, 0 < r → 1 ≤ f r / r ^ n) :
    ¬ BddAbove (f '' Ioi 0) := by
  rintro ⟨B, hB⟩
  let r := max (B + 1) 1
  have hr1 : 1 ≤ r := le_max_right _ _
  have hr : 0 < r := zero_lt_one.trans_le hr1
  have hrB : B < r := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hpow : r ≤ r ^ n := le_self_pow₀ hr1 hn.ne'
  have hfr : r ^ n ≤ f r := by
    simpa only [one_mul] using (le_div_iff₀ (pow_pos hr n)).mp (hlower r hr)
  exact (hrB.trans_le (hpow.trans hfr)).not_ge (hB (mem_image_of_mem f hr))

/-- The literal lower-bound part of Simon 5.8 already contradicts its
boundedness assumption for `n>0`; no properties of `g` are needed. -/
theorem calculusLemma_printed_lower_bound_inconsistent
    (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ) (hf : BddAbove (f '' Ioi 0))
    (hlower : ∀ σ ρ : ℝ, 0 < σ → σ < ρ → 1 ≤ f σ / σ ^ n) : False := by
  apply not_bddAbove_of_one_le_normalized n hn f _ hf
  intro σ hσ
  exact hlower σ (σ + 1) hσ (by linarith)

end Poincare.SimonGMT.Chapter04
