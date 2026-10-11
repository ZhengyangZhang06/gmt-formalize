module

public import Poincare.SimonGMT.AppendixB.SimonsInequalities
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Simon GMT, Appendix B: the algebraic identity in (B.10)

This file proves the finite Lagrange identity used when Simon rewrites the
defect between the full covariant-derivative norm and the derivative of
`|A|`.  It then gives the literal sum-of-squares representation of the
quantity `D` in (B.10), with no geometric assertion hidden in the algebra.
-/

open scoped BigOperators

namespace Poincare.SimonGMT.AppendixB

/-- The finite Lagrange identity, in the normalization used in Simon (B.10). -/
theorem finite_lagrange_identity {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) :
    (∑ i, (a i) ^ 2) * (∑ i, (b i) ^ 2) - (∑ i, a i * b i) ^ 2 =
      (1 / 2 : ℝ) * ∑ i, ∑ j, (a i * b j - a j * b i) ^ 2 := by
  classical
  have h₁ : (∑ i, ∑ j, (a i * b j) ^ 2) =
      (∑ i, (a i) ^ 2) * (∑ j, (b j) ^ 2) := by
    simp_rw [mul_pow]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have h₂ : (∑ i, ∑ j, (a j * b i) ^ 2) =
      (∑ i, (a i) ^ 2) * (∑ j, (b j) ^ 2) := by
    calc
      (∑ i, ∑ j, (a j * b i) ^ 2) =
          (∑ i, (b i) ^ 2) * (∑ j, (a j) ^ 2) := by
            simp_rw [mul_pow]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = _ := by ring
  have h₃ : (∑ i, ∑ j, (a i * b j) * (a j * b i)) =
      (∑ i, a i * b i) ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hmul : (∑ i, ∑ j, 2 * ((a i * b j) * (a j * b i))) =
      2 * (∑ i, ∑ j, (a i * b j) * (a j * b i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have h₄ : (∑ i, ∑ j, (a i * b j - a j * b i) ^ 2) =
      (∑ i, ∑ j, (a i * b j) ^ 2) -
        2 * (∑ i, ∑ j, (a i * b j) * (a j * b i)) +
        (∑ i, ∑ j, (a j * b i) ^ 2) := by
    calc
      (∑ i, ∑ j, (a i * b j - a j * b i) ^ 2) =
          ∑ i, ∑ j, ((a i * b j) ^ 2 -
            2 * ((a i * b j) * (a j * b i)) + (a j * b i) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = (∑ i, ∑ j, (a i * b j) ^ 2) -
          (∑ i, ∑ j, 2 * ((a i * b j) * (a j * b i))) +
          (∑ i, ∑ j, (a j * b i) ^ 2) := by
            simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = _ := by rw [hmul]
  calc
    (∑ i, (a i) ^ 2) * (∑ i, (b i) ^ 2) - (∑ i, a i * b i) ^ 2 =
        (1 / 2 : ℝ) *
          ((∑ i, ∑ j, (a i * b j) ^ 2) -
            2 * (∑ i, ∑ j, (a i * b j) * (a j * b i)) +
            (∑ i, ∑ j, (a j * b i) ^ 2)) := by rw [h₁, h₂, h₃]; ring
    _ = (1 / 2 : ℝ) * ∑ i, ∑ j, (a i * b j - a j * b i) ^ 2 := by
      rw [h₄]

/-- The unnormalized antisymmetric sum of squares associated with a fixed
covariant-derivative direction. -/
def simonsSkewSum {n : ℕ} (h : Fin n → Fin n → ℝ)
    (dh : Fin n → Fin n → Fin n → ℝ) (k : Fin n) : ℝ :=
  ∑ i, ∑ j, ∑ r, ∑ s,
    (h r s * dh i j k - h i j * dh r s k) ^ 2

theorem simonsSkewSum_nonneg {n : ℕ} (h : Fin n → Fin n → ℝ)
    (dh : Fin n → Fin n → Fin n → ℝ) (k : Fin n) :
    0 ≤ simonsSkewSum h dh k := by
  unfold simonsSkewSum
  exact Finset.sum_nonneg fun i _ ↦
    Finset.sum_nonneg fun j _ ↦
      Finset.sum_nonneg fun r _ ↦
        Finset.sum_nonneg fun s _ ↦ sq_nonneg _

/-- Simon's rearrangement following (B.10), before division by `|A|²`. -/
theorem simonsSkewSum_eq {n : ℕ} (h : Fin n → Fin n → ℝ)
    (dh : Fin n → Fin n → Fin n → ℝ) (k : Fin n) :
    secondFundamentalNormSq h * (∑ i, ∑ j, (dh i j k) ^ 2) -
        (contraction h dh k) ^ 2 =
      (1 / 2 : ℝ) * simonsSkewSum h dh k := by
  let ι := Fin n × Fin n
  have hsum (f : ι → ℝ) : (∑ q, f q) = ∑ i, ∑ j, f (i, j) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have H := finite_lagrange_identity
    (fun q : ι ↦ dh q.1 q.2 k) (fun q : ι ↦ h q.1 q.2)
  simp_rw [hsum] at H
  simpa [secondFundamentalNormSq, contraction, simonsSkewSum, mul_comm] using H

/-- Exact sum-of-squares form of the defect `D` in Simon (B.10). -/
theorem simonsDefect_eq_sum_skew {n : ℕ} (h : Fin n → Fin n → ℝ)
    (dh : Fin n → Fin n → Fin n → ℝ)
    (hA : 0 < secondFundamentalNormSq h) :
    simonsDefect h dh =
      (1 / (2 * secondFundamentalNormSq h)) * ∑ k, simonsSkewSum h dh k := by
  unfold simonsDefect derivativeNormSq
  have hA0 : secondFundamentalNormSq h ≠ 0 := ne_of_gt hA
  have hk (k : Fin n) := simonsSkewSum_eq h dh k
  calc
    (∑ k, ∑ i, ∑ j, (dh i j k) ^ 2) -
          ∑ k, (contraction h dh k) ^ 2 / secondFundamentalNormSq h =
        ∑ k, ((∑ i, ∑ j, (dh i j k) ^ 2) -
          (contraction h dh k) ^ 2 / secondFundamentalNormSq h) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ k, ((1 / (2 * secondFundamentalNormSq h)) * simonsSkewSum h dh k) := by
      apply Finset.sum_congr rfl
      intro k _
      have hAk := hk k
      field_simp
      nlinarith
    _ = _ := by
      simp only [Finset.mul_sum]

end Poincare.SimonGMT.AppendixB
