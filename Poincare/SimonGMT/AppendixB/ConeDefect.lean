module

public import Poincare.SimonGMT.AppendixB.LagrangeIdentity
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Simon GMT, Appendix B: the radial algebra in the cone estimate

This file isolates the finite-coordinate calculation used in (B.11).  The
last coordinate is the radial direction and the first `n` coordinates are
tangent to the link.  The statements below do not assume the geometric
construction of a cone: they record exactly the radial vanishing and Codazzi
identities that the geometric argument supplies.
-/

open scoped BigOperators

namespace Poincare.SimonGMT.AppendixB

private theorem sum_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) :
    (∑ i, ∑ j, a i * b j) = (∑ i, a i) * ∑ j, b j := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- The squared norm of the tangential block of a bilinear form on
`Fin (n + 1)`. -/
def tangentialSecondFundamentalNormSq {n : ℕ}
    (h : Fin (n + 1) → Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, (h i.castSucc j.castSucc) ^ 2

/-- The part of Simon's skew sum in which the second copy of the second
fundamental form has one radial index. -/
def radialSkewSum {n : ℕ} (h : Fin (n + 1) → Fin (n + 1) → ℝ)
    (dh : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ) : ℝ :=
  ∑ k : Fin (n + 1), ∑ i : Fin n, ∑ j : Fin n, ∑ r : Fin n,
    (h r.castSucc (Fin.last n) * dh i.castSucc j.castSucc k -
      h i.castSucc j.castSucc * dh r.castSucc (Fin.last n) k) ^ 2

private abbrev ConeFullIndex (n : ℕ) :=
  Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1)

private abbrev ConeSelectedIndex (n : ℕ) :=
  (Bool × Bool) × Fin (n + 1) × Fin n × Fin n × Fin n

/-- The four disjoint placements of one radial index used in Simon's factor
`4` argument. -/
private def coneSelectedIndex {n : ℕ} (q : ConeSelectedIndex n) : ConeFullIndex n :=
  let tag := q.1
  let k := q.2.1
  let i := q.2.2.1
  let j := q.2.2.2.1
  let r := q.2.2.2.2
  match tag with
  | (false, false) => (k, i.castSucc, j.castSucc, r.castSucc, Fin.last n)
  | (false, true) => (k, i.castSucc, j.castSucc, Fin.last n, r.castSucc)
  | (true, false) => (k, r.castSucc, Fin.last n, i.castSucc, j.castSucc)
  | (true, true) => (k, Fin.last n, r.castSucc, i.castSucc, j.castSucc)

private theorem coneSelectedIndex_injective {n : ℕ} :
    Function.Injective (coneSelectedIndex (n := n)) := by
  rintro ⟨⟨a, b⟩, k, i, j, r⟩ ⟨⟨a', b'⟩, k', i', j', r'⟩ hq
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp [coneSelectedIndex] at hq ⊢ <;> aesop

private def simonsSkewTerm {n : ℕ}
    (h : Fin (n + 1) → Fin (n + 1) → ℝ)
    (dh : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ)
    (q : ConeFullIndex n) : ℝ :=
  (h q.2.2.2.1 q.2.2.2.2 * dh q.2.1 q.2.2.1 q.1 -
    h q.2.1 q.2.2.1 * dh q.2.2.2.1 q.2.2.2.2 q.1) ^ 2

private theorem selected_skew_le_full {n : ℕ}
    (h : Fin (n + 1) → Fin (n + 1) → ℝ)
    (dh : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ) :
    (∑ q : ConeSelectedIndex n, simonsSkewTerm h dh (coneSelectedIndex q)) ≤
      ∑ q : ConeFullIndex n, simonsSkewTerm h dh q := by
  let e : ConeSelectedIndex n ↪ ConeFullIndex n :=
    ⟨coneSelectedIndex, coneSelectedIndex_injective⟩
  change (∑ q ∈ Finset.univ, simonsSkewTerm h dh (e q)) ≤
    ∑ q ∈ Finset.univ, simonsSkewTerm h dh q
  rw [← Finset.sum_map]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · simp
  · intro q _ _
    exact sq_nonneg _

private theorem full_skew_sum_eq {n : ℕ}
    (h : Fin (n + 1) → Fin (n + 1) → ℝ)
    (dh : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ) :
    (∑ q : ConeFullIndex n, simonsSkewTerm h dh q) =
      ∑ k, simonsSkewSum h dh k := by
  simp only [ConeFullIndex, Fintype.sum_prod_type, simonsSkewTerm, simonsSkewSum]

private theorem selected_skew_sum_eq {n : ℕ}
    (h : Fin (n + 1) → Fin (n + 1) → ℝ)
    (dh : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ)
    (h_flip : ∀ r : Fin n,
      h (Fin.last n) r.castSucc = h r.castSucc (Fin.last n))
    (dh_flip : ∀ (r : Fin n) (k : Fin (n + 1)),
      dh (Fin.last n) r.castSucc k = dh r.castSucc (Fin.last n) k) :
    (∑ q : ConeSelectedIndex n, simonsSkewTerm h dh (coneSelectedIndex q)) =
      4 * radialSkewSum h dh := by
  have hswap :
      (∑ k : Fin (n + 1), ∑ i : Fin n, ∑ j : Fin n, ∑ r : Fin n,
        (h i.castSucc j.castSucc * dh r.castSucc (Fin.last n) k -
          h r.castSucc (Fin.last n) * dh i.castSucc j.castSucc k) ^ 2) =
        radialSkewSum h dh := by
    unfold radialSkewSum
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hbase :
      (∑ k : Fin (n + 1), ∑ i : Fin n, ∑ j : Fin n, ∑ r : Fin n,
        (h r.castSucc (Fin.last n) * dh i.castSucc j.castSucc k -
          h i.castSucc j.castSucc * dh r.castSucc (Fin.last n) k) ^ 2) =
        radialSkewSum h dh := rfl
  simp only [ConeSelectedIndex, Fintype.sum_prod_type, Fintype.sum_bool,
    coneSelectedIndex, simonsSkewTerm]
  simp_rw [h_flip, dh_flip]
  rw [hswap, hbase]
  ring

/-- The four radial placements are disjoint terms of the full skew sum.  This
is the exact factor `4` used between Simon's equations (B.10) and (B.11). -/
theorem four_mul_radialSkewSum_le {n : ℕ}
    (h : Fin (n + 1) → Fin (n + 1) → ℝ)
    (dh : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ)
    (h_flip : ∀ r : Fin n,
      h (Fin.last n) r.castSucc = h r.castSucc (Fin.last n))
    (dh_flip : ∀ (r : Fin n) (k : Fin (n + 1)),
      dh (Fin.last n) r.castSucc k = dh r.castSucc (Fin.last n) k) :
    4 * radialSkewSum h dh ≤ ∑ k, simonsSkewSum h dh k := by
  rw [← selected_skew_sum_eq h dh h_flip dh_flip, ← full_skew_sum_eq h dh]
  exact selected_skew_le_full h dh

/-- If both radial rows and columns vanish, the full squared norm is the
squared norm of the tangential block. -/
theorem secondFundamentalNormSq_eq_tangential {n : ℕ}
    (h : Fin (n + 1) → Fin (n + 1) → ℝ)
    (h_last_left : ∀ j, h (Fin.last n) j = 0)
    (h_last_right : ∀ i, h i (Fin.last n) = 0) :
    secondFundamentalNormSq h = tangentialSecondFundamentalNormSq h := by
  unfold secondFundamentalNormSq tangentialSecondFundamentalNormSq
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  simp [h_last_left, h_last_right]

/-- The radial Codazzi identities turn the selected skew terms into exactly
`ρ⁻² |A|⁴`.  This is the numerical heart of the lower bound in (B.11). -/
theorem radialSkewSum_eq {n : ℕ}
    (h : Fin (n + 1) → Fin (n + 1) → ℝ)
    (dh : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ)
    (ρ : ℝ)
    (h_last_right : ∀ i, h i (Fin.last n) = 0)
    (dh_radial : ∀ (r : Fin n) (k : Fin (n + 1)),
      dh r.castSucc (Fin.last n) k = -(ρ⁻¹ * h r.castSucc k)) :
    radialSkewSum h dh =
      (ρ⁻¹) ^ 2 * (tangentialSecondFundamentalNormSq h) ^ 2 := by
  unfold radialSkewSum tangentialSecondFundamentalNormSq
  simp_rw [h_last_right, zero_mul, zero_sub, dh_radial, mul_neg, neg_neg, mul_pow]
  rw [Fin.sum_univ_castSucc]
  simp only [h_last_right, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
    Finset.sum_const_zero, add_zero]
  have hreorder :
      (∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ r : Fin n,
          h i.castSucc j.castSucc ^ 2 *
            ((ρ⁻¹) ^ 2 * h r.castSucc k.castSucc ^ 2)) =
        ∑ i : Fin n, ∑ j : Fin n, ∑ r : Fin n, ∑ k : Fin n,
          h i.castSucc j.castSucc ^ 2 *
            ((ρ⁻¹) ^ 2 * h r.castSucc k.castSucc ^ 2) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  rw [hreorder]
  let I := Fin n × Fin n
  have hsum (f : I → ℝ) : (∑ q, f q) = ∑ i, ∑ j, f (i, j) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hp := sum_product
    (fun q : I ↦ h q.1.castSucc q.2.castSucc ^ 2)
    (fun q : I ↦ (ρ⁻¹) ^ 2 * h q.1.castSucc q.2.castSucc ^ 2)
  simp_rw [hsum] at hp
  rw [hp]
  have hscale :
      (∑ i : Fin n, ∑ j : Fin n,
          (ρ⁻¹) ^ 2 * h i.castSucc j.castSucc ^ 2) =
        (ρ⁻¹) ^ 2 * ∑ i : Fin n, ∑ j : Fin n, h i.castSucc j.castSucc ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [hscale]
  ring

/-- Codazzi symmetry and radial homogeneity imply the radial derivative
identity used by `radialSkewSum_eq`. -/
theorem radial_derivative_of_codazzi {n : ℕ}
    (h : Fin (n + 1) → Fin (n + 1) → ℝ)
    (dh : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ)
    (ρ : ℝ)
    (codazzi : ∀ i j k, dh i j k = dh i k j)
    (radial_homogeneity : ∀ i j,
      dh i j (Fin.last n) = -(ρ⁻¹ * h i j)) :
    ∀ (r : Fin n) (k : Fin (n + 1)),
      dh r.castSucc (Fin.last n) k = -(ρ⁻¹ * h r.castSucc k) := by
  intro r k
  rw [codazzi]
  exact radial_homogeneity _ _

/-- Coordinate form of Simon's cone defect estimate (B.11).  The geometric
cone calculation supplies the hypotheses: radial rows vanish, the second
fundamental form and its derivative are symmetric in their first two slots,
and radial differentiation is multiplication by `-ρ⁻¹`. -/
theorem cone_simonsDefect_lower_bound {n : ℕ}
    (h : Fin (n + 1) → Fin (n + 1) → ℝ)
    (dh : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ)
    (ρ : ℝ)
    (h_last_left : ∀ j, h (Fin.last n) j = 0)
    (h_last_right : ∀ i, h i (Fin.last n) = 0)
    (h_flip : ∀ r : Fin n,
      h (Fin.last n) r.castSucc = h r.castSucc (Fin.last n))
    (dh_flip : ∀ (r : Fin n) (k : Fin (n + 1)),
      dh (Fin.last n) r.castSucc k = dh r.castSucc (Fin.last n) k)
    (dh_radial : ∀ (r : Fin n) (k : Fin (n + 1)),
      dh r.castSucc (Fin.last n) k = -(ρ⁻¹ * h r.castSucc k))
    (hA : 0 < secondFundamentalNormSq h) :
    2 * (ρ⁻¹) ^ 2 * secondFundamentalNormSq h ≤ simonsDefect h dh := by
  have hnorm := secondFundamentalNormSq_eq_tangential h h_last_left h_last_right
  have hrad := radialSkewSum_eq h dh ρ h_last_right dh_radial
  have hfour := four_mul_radialSkewSum_le h dh h_flip dh_flip
  rw [hrad, ← hnorm] at hfour
  rw [simonsDefect_eq_sum_skew h dh hA]
  have hA0 : secondFundamentalNormSq h ≠ 0 := ne_of_gt hA
  have hcoef : 0 ≤ 1 / (2 * secondFundamentalNormSq h) := by positivity
  calc
    2 * (ρ⁻¹) ^ 2 * secondFundamentalNormSq h =
        (1 / (2 * secondFundamentalNormSq h)) *
          (4 * ((ρ⁻¹) ^ 2 * (secondFundamentalNormSq h) ^ 2)) := by
            field_simp
            ring
    _ ≤ (1 / (2 * secondFundamentalNormSq h)) *
        ∑ k, simonsSkewSum h dh k :=
      mul_le_mul_of_nonneg_left hfour hcoef

end Poincare.SimonGMT.AppendixB
