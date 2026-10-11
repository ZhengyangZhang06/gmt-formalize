module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Simon GMT, Appendix B: algebra in the stability argument

This file kernel-checks two finite-dimensional numerical/algebraic components
of Appendix B: the nonnegativity behind the defect in (B.10), and the uniform
choice of the final exponent on printed p. 234.  The differential-geometric
Simons identity (B.8) and the cone estimate (B.11) still require a developed
hypersurface/covariant-derivative API and are not claimed here.
-/

open scoped BigOperators

namespace Poincare.SimonGMT.AppendixB

/-- `|A|²` in the coordinate notation of Appendix B. -/
def secondFundamentalNormSq {n : ℕ} (h : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, (h i j) ^ 2

/-- `∑ᵢⱼ hᵢⱼ hᵢⱼ;ₖ`, the derivative of `|A|` before normalization. -/
def contraction {n : ℕ} (h : Fin n → Fin n → ℝ)
    (dh : Fin n → Fin n → Fin n → ℝ) (k : Fin n) : ℝ :=
  ∑ i, ∑ j, h i j * dh i j k

/-- `∑ᵢⱼₖ h²ᵢⱼ;ₖ`. -/
def derivativeNormSq {n : ℕ} (dh : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ k, ∑ i, ∑ j, (dh i j k) ^ 2

/-- The quantity `D` in (B.10), written where `|A|² > 0`. -/
noncomputable def simonsDefect {n : ℕ} (h : Fin n → Fin n → ℝ)
    (dh : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  derivativeNormSq dh -
    ∑ k, (contraction h dh k) ^ 2 / secondFundamentalNormSq h

theorem secondFundamentalNormSq_nonneg {n : ℕ} (h : Fin n → Fin n → ℝ) :
    0 ≤ secondFundamentalNormSq h := by
  unfold secondFundamentalNormSq
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg (h i j)

/-- The Cauchy--Schwarz step implicit in the rearrangement following (B.10). -/
theorem contraction_sq_le {n : ℕ} (h : Fin n → Fin n → ℝ)
    (dh : Fin n → Fin n → Fin n → ℝ) (k : Fin n) :
    (contraction h dh k) ^ 2 ≤
      secondFundamentalNormSq h * (∑ i, ∑ j, (dh i j k) ^ 2) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun p ↦ h p.1 p.2) (fun p ↦ dh p.1 p.2 k)
  have hsum (f : Fin n × Fin n → ℝ) :
      (∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)), f p) =
        ∑ i, ∑ j, f (i, j) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [hsum (fun p ↦ h p.1 p.2 * dh p.1 p.2 k),
    hsum (fun p ↦ (h p.1 p.2) ^ 2),
    hsum (fun p ↦ (dh p.1 p.2 k) ^ 2)] at hc
  simpa [contraction, secondFundamentalNormSq] using hc

/-- In particular, the defect (B.10) is nonnegative.  Lemma B.11 strengthens
this for cones by exploiting the radial Codazzi identities. -/
theorem simonsDefect_nonneg {n : ℕ} (h : Fin n → Fin n → ℝ)
    (dh : Fin n → Fin n → Fin n → ℝ)
    (hA : 0 < secondFundamentalNormSq h) :
    0 ≤ simonsDefect h dh := by
  have hk : ∀ k : Fin n,
      (contraction h dh k) ^ 2 / secondFundamentalNormSq h ≤
        ∑ i, ∑ j, (dh i j k) ^ 2 := by
    intro k
    apply (div_le_iff₀ hA).2
    simpa [mul_comm] using contraction_sq_le h dh k
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) ↦ hk k
  simpa [simonsDefect, derivativeNormSq, sub_nonneg] using hsum

/-- Numerical check in Remark B.3: the seven-dimensional Simons cone meets
the stability threshold `|x|²|A|² ≤ (n-2)²/4`. -/
theorem simons_cone_dimension_seven_threshold :
    (6 : ℝ) ≤ ((7 : ℝ) - 2) ^ 2 / 4 := by
  norm_num

/-- The simultaneous strict inequalities used in the last paragraph of the
proof of B.2.  The concrete choice `ε = 1/10` works uniformly for `2 ≤ n ≤ 6`. -/
theorem exists_final_exponent (n : ℕ) (hn₂ : 2 ≤ n) (hn₆ : n ≤ 6) :
    ∃ ε : ℝ, 0 < ε ∧
      (((n : ℝ) / 2 - 2 + ε) ^ 2 < 2) ∧ ((1 + ε) ^ 2 < 2) := by
  refine ⟨1 / 10, by norm_num, ?_, by norm_num⟩
  interval_cases n <;> norm_num at hn₂ hn₆ ⊢

end Poincare.SimonGMT.AppendixB
