module

public import Poincare.SimonGMT.Chapter04.GoodRadiusSource
public import Poincare.SimonGMT.Chapter04.LowerDensityTangents

@[expose] public section

/-!
# A nonvacuous good-radius lemma replacing printed Simon 5.8

The hypotheses use the lower-density information actually available in
5.7 and the finite-interval inequality preceding 5.5. No integral starting
at zero, finite density limit, or globally bounded normalized mass is
assumed. The elementary supremum proof gives a nonsharp constant four
times the printed good-radius constant, sufficient for the unspecified
dimensional constant in the Sobolev theorem.
-/

open Filter Function Set MeasureTheory
open scoped Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

/-- Local-radius good-ball selection. The normalized mass is only
required to exceed `1/2` at arbitrarily small positive radii (here stated
eventually), while the total mass is at most `R^n/4`. -/
theorem exists_goodRadius_of_local_radius_inequality
    (n : ℕ) (f g : ℝ → ℝ) {R : ℝ} (hR : 0 < R)
    (hbound : ∀ r : ℝ, 0 < r → f r ≤ R ^ n / 4)
    (hlower : ∀ᶠ r : ℝ in 𝓝[>] 0, (1 / 2 : ℝ) < f r / r ^ n)
    (hgi : ∀ σ : ℝ, 0 < σ → σ ≤ R →
      IntervalIntegrable (fun t ↦ g t / t ^ n) volume σ R)
    (hineq : ∀ σ : ℝ, 0 < σ → σ ≤ R →
      f σ / σ ^ n ≤ f R / R ^ n + ∫ t in σ..R, g t / t ^ n) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ f (5 * r) ≤ (2 * 5 ^ n * R) * g r := by
  by_contra hnone
  push Not at hnone
  obtain ⟨σ, hσlower, hσ⟩ := (hlower.and (Ioc_mem_nhdsGT hR)).exists
  let F : ℝ → ℝ := fun r ↦ f r / r ^ n
  let S := sSup (F '' Icc σ R)
  have hset : (F '' Icc σ R).Nonempty := ⟨F σ, mem_image_of_mem F ⟨le_rfl, hσ.2⟩⟩
  have hbdd : BddAbove (F '' Icc σ R) := by
    refine ⟨(R ^ n / 4) / σ ^ n, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    have hr0 := hσ.1.trans_le hr.1
    exact (div_le_div_of_nonneg_right (hbound r hr0) (pow_pos hr0 n).le).trans
      (div_le_div_of_nonneg_left (by positivity) (pow_pos hσ.1 n)
        (pow_le_pow_left₀ hσ.1.le hr.1 n))
  have hsup : ∀ r ∈ Icc σ R, F r ≤ S := fun r hr ↦
    le_csSup hbdd (mem_image_of_mem F hr)
  let B := max S (1 / 4 : ℝ)
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hF : ∀ t ∈ Icc σ R, F (5 * t) ≤ B := by
    intro t ht
    have ht0 := hσ.1.trans_le ht.1
    have h5t : 0 < 5 * t := by positivity
    by_cases h5R : 5 * t ≤ R
    · exact (hsup _ ⟨by linarith [ht.1], h5R⟩).trans (le_max_left _ _)
    · have hR5 : R ≤ 5 * t := (lt_of_not_ge h5R).le
      have hdiv : F (5 * t) ≤ (1 / 4 : ℝ) := by
        change f (5 * t) / (5 * t) ^ n ≤ _
        apply (div_le_iff₀ (pow_pos h5t n)).mpr
        have hp := pow_le_pow_left₀ hR.le hR5 n
        linarith [hbound (5 * t) h5t]
      exact hdiv.trans (le_max_right _ _)
  have hg : ∀ t ∈ Icc σ R, g t / t ^ n ≤ B / (2 * R) := by
    intro t ht
    have ht0 := hσ.1.trans_le ht.1
    have hK : 0 < (2 : ℝ) * 5 ^ n * R := by positivity
    have hbad : g t ≤ f (5 * t) / (2 * 5 ^ n * R) := by
      apply (le_div_iff₀ hK).mpr
      simpa only [mul_comm (g t)] using (hnone t ht0 ht.2).le
    calc
      g t / t ^ n ≤ (f (5 * t) / (2 * 5 ^ n * R)) / t ^ n :=
        div_le_div_of_nonneg_right hbad (pow_pos ht0 n).le
      _ = F (5 * t) / (2 * R) := by
        dsimp only [F]
        rw [mul_pow]
        field_simp
      _ ≤ B / (2 * R) := div_le_div_of_nonneg_right (hF t ht) (by positivity)
  have hFR : F R ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (pow_pos hR n)).mpr
    linarith [hbound R hR]
  have hS : S ≤ (1 / 4 : ℝ) + B / 2 := by
    apply csSup_le hset
    rintro _ ⟨τ, hτ, rfl⟩
    have hτ0 := hσ.1.trans_le hτ.1
    have hi : (∫ t in τ..R, g t / t ^ n) ≤ B / 2 := by
      calc
        _ ≤ ∫ _ in τ..R, B / (2 * R) :=
          intervalIntegral.integral_mono_on hτ.2 (hgi τ hτ0 hτ.2)
            intervalIntegrable_const (fun t ht ↦ hg t ⟨hτ.1.trans ht.1, ht.2⟩)
        _ = (R - τ) * (B / (2 * R)) := by rw [intervalIntegral.integral_const, smul_eq_mul]
        _ ≤ R * (B / (2 * R)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = B / 2 := by field_simp
    exact (hineq τ hτ0 hτ.2).trans (add_le_add hFR hi)
  have hhalf : S ≤ (1 / 2 : ℝ) := by
    dsimp only [B] at hS
    rcases le_total S (1 / 4 : ℝ) with h | h
    · linarith
    · rw [max_eq_left h] at hS
      linarith
  exact (hσlower.trans_le ((hsup σ ⟨le_rfl, hσ.2⟩).trans hhalf)).false

/-- Monotonicity of the energy distribution supplies genuine integrability
on every positive compact radius interval. -/
theorem intervalIntegrable_radiusQuotient_of_monotoneOn
    (n : ℕ) {g : ℝ → ℝ} (hg : MonotoneOn g (Ioi 0))
    {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) :
    IntervalIntegrable (fun t ↦ g t / t ^ n) volume σ ρ := by
  have hsub : uIcc σ ρ ⊆ Ioi 0 := by
    rw [uIcc_of_le hσρ]
    exact fun t ht ↦ hσ.trans_le ht.1
  have hgi := (hg.mono hsub).intervalIntegrable (μ := volume)
  simpa only [div_eq_mul_inv, Pi.inv_apply, Pi.pow_apply, id_eq] using hgi.mul_continuousOn
    ((continuousOn_id.pow n).inv₀ (fun t ht ↦ pow_ne_zero _ (hsub ht).ne'))

/-- A quantitative corrected version usable in (5.7): with total mass
at most `M`, choose a radius at most `2 M^(1/n)`. The constant is explicitly
four times the printed one; no sharp-constant claim is made. -/
theorem exists_goodRadius_of_finite_interval_inequality
    (n : ℕ) (hn : 2 ≤ n) (f g : ℝ → ℝ) {M : ℝ} (hM : 0 < M)
    (hbound : ∀ r : ℝ, 0 < r → f r ≤ M) (hg : MonotoneOn g (Ioi 0))
    (hlower : ∀ᶠ r : ℝ in 𝓝[>] 0, (1 / 2 : ℝ) < f r / r ^ n)
    (hineq : ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ →
      f σ / σ ^ n ≤ f ρ / ρ ^ n + ∫ t in σ..ρ, g t / t ^ n) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 2 * M ^ ((n : ℝ)⁻¹) ∧
      f (5 * r) ≤ (4 * 5 ^ n * M ^ ((n : ℝ)⁻¹)) * g r := by
  let R := 2 * M ^ ((n : ℝ)⁻¹)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hn0 : n ≠ 0 := by omega
  have hRpow : R ^ n = 2 ^ n * M := by
    dsimp only [R]
    rw [mul_pow, Real.rpow_inv_natCast_pow hM.le hn0]
  have hfour : (4 : ℝ) ≤ 2 ^ n := by
    calc
      (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  have hb : ∀ r : ℝ, 0 < r → f r ≤ R ^ n / 4 := by
    intro r hr
    have hmul := mul_le_mul_of_nonneg_right hfour hM.le
    rw [hRpow]
    linarith [hbound r hr]
  obtain ⟨r, hr, hrR, hgood⟩ := exists_goodRadius_of_local_radius_inequality n f g hR hb hlower
    (fun σ hσ hσR ↦ intervalIntegrable_radiusQuotient_of_monotoneOn n hg hσ hσR)
    (fun σ hσ hσR ↦ hineq σ R hσ hσR)
  refine ⟨r, hr, hrR, ?_⟩
  convert hgood using 1 <;> dsimp only [R] <;> ring

end

end Poincare.SimonGMT.Chapter04
