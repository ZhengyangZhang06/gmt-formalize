module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section

/-!
# Compact convex hulls in finite-dimensional Euclidean space

Carathéodory's theorem represents the convex hull as a finite union of
continuous images of compact spaces of weighted configurations. This keeps
the convex-hull conclusion in Simon 4.6.2 literal: no closure is inserted.
-/

open Set Metric
open scoped BigOperators

namespace Poincare.SimonGMT.Chapter04

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A compact subset of a finite-dimensional real inner product space has
a compact (not merely relatively compact) convex hull. -/
theorem isCompact_convexHull_of_isCompact {K : Set E} (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  classical
  let W : ℕ → Set E := fun j ↦
    (fun p : (Fin j → ℝ) × (Fin j → E) ↦ ∑ i, p.1 i • p.2 i) ''
      ((Icc (0 : Fin j → ℝ) 1 ∩ {w | ∑ i, w i = 1}) ×ˢ
        (univ.pi fun _ : Fin j ↦ K))
  have hW : ∀ j, IsCompact (W j) := by
    intro j
    apply IsCompact.image _ (by fun_prop)
    apply IsCompact.prod
    · exact isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)
    · convert isCompact_pi_infinite (fun _ : Fin j ↦ hK) using 1
      ext z
      simp only [mem_pi, mem_univ, forall_true_left, mem_ofPred_eq]
  have hWeq : convexHull ℝ K = ⋃ j ∈ Finset.range (Module.finrank ℝ E + 2), W j := by
    apply subset_antisymm
    · intro x hx
      rw [convexHull_eq_union] at hx
      simp only [mem_iUnion, exists_prop] at hx
      obtain ⟨t, htK, htind, hxt⟩ := hx
      obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.1 hxt
      have hcard : t.card ≤ Module.finrank ℝ E + 1 := by
        simpa only [Fintype.card_coe] using
          htind.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      let e : t ≃ Fin t.card := by simpa only [Fintype.card_coe] using Fintype.equivFin t
      let a : Fin t.card → ℝ := fun i ↦ w (e.symm i)
      let z : Fin t.card → E := fun i ↦ (e.symm i : E)
      have hsum : ∑ i, a i = 1 := by
        rw [← Equiv.sum_comp e]
        simpa only [a, Equiv.symm_apply_apply, Finset.univ_eq_attach, Finset.sum_attach] using hw1
      have hsumx : ∑ i, a i • z i = x := by
        rw [← Equiv.sum_comp e]
        simp only [a, z, Equiv.symm_apply_apply, Finset.univ_eq_attach]
        change (∑ i ∈ t.attach, (fun y : E ↦ w y • y) ↑i) = x
        exact (Finset.sum_attach t (fun y : E ↦ w y • y)).trans hwx
      have ha0 : ∀ i, 0 ≤ a i := fun i ↦ hw0 _ (e.symm i).property
      have ha1 : ∀ i, a i ≤ 1 := by
        intro i
        rw [← hsum]
        exact Finset.single_le_sum (fun j _ ↦ ha0 j) (Finset.mem_univ i)
      simp only [mem_iUnion, exists_prop]
      refine ⟨t.card, Finset.mem_range.mpr (by omega), ?_⟩
      exact ⟨(a, z), ⟨⟨⟨ha0, ha1⟩, hsum⟩, fun i _ ↦ htK (e.symm i).property⟩, hsumx⟩
    · simp only [iUnion_subset_iff]
      intro j _ x hx
      obtain ⟨⟨a, z⟩, ⟨⟨ha, hsum⟩, hz⟩, rfl⟩ := hx
      exact (convex_convexHull ℝ K).sum_mem (fun i _ ↦ ha.1 i) hsum
        (fun i _ ↦ subset_convexHull ℝ K (hz i (mem_univ i)))
  rw [hWeq]
  exact (Finset.finite_toSet _).isCompact_biUnion fun j _ ↦ hW j

/-- A point outside a nonempty compact convex set can be excluded by a
closed ball containing the whole set. -/
theorem exists_closedBall_separating_of_compact_convex {K : Set E}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    {x : E} (hx : x ∉ K) :
    ∃ (ξ : E) (R : ℝ), 0 ≤ R ∧ K ⊆ closedBall ξ R ∧ x ∉ closedBall ξ R := by
  obtain ⟨y, hy, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hK.isClosed.isComplete hconv x
  have hsep := (norm_eq_iInf_iff_real_inner_le_zero hconv hy).1 hmin
  have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun h ↦ hx (h ▸ hy)))
  obtain ⟨B, hB, hKB⟩ := hK.isBounded.subset_ball_lt 0 y
  let t : ℝ := (B ^ 2 + 1) / ‖x - y‖ ^ 2
  have ht : 0 < t := div_pos (by positivity) (sq_pos_of_pos hd)
  have htd : t * ‖x - y‖ ^ 2 = B ^ 2 + 1 := div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hd))
  let ξ := y - t • (x - y)
  let R := Real.sqrt (B ^ 2 + t ^ 2 * ‖x - y‖ ^ 2)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = B ^ 2 + t ^ 2 * ‖x - y‖ ^ 2 := Real.sq_sqrt (by positivity)
  refine ⟨ξ, R, hR, ?_, ?_⟩
  · intro z hz
    have hnorm : ‖z - y‖ < B := by simpa only [mem_ball, dist_eq_norm] using hKB hz
    have hi : inner ℝ (z - y) (x - y) ≤ 0 := by
      simpa only [real_inner_comm (z - y) (x - y)] using hsep z hz
    have heq : z - ξ = (z - y) + t • (x - y) := by dsimp [ξ]; abel
    have hsquare : ‖z - ξ‖ ^ 2 ≤ R ^ 2 := by
      rw [heq, norm_add_sq_real, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht, hR2]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos ht.le hi, norm_nonneg (z - y)]
    simp only [mem_closedBall, dist_eq_norm]
    nlinarith [norm_nonneg (z - ξ)]
  · have heq : x - ξ = (1 + t) • (x - y) := by dsimp [ξ]; module
    have hnorm : ‖x - ξ‖ = (1 + t) * ‖x - y‖ := by
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    simp only [mem_closedBall, dist_eq_norm, not_le]
    rw [hnorm]
    nlinarith [sq_nonneg ((1 + t) * ‖x - y‖ + R)]

end

end Poincare.SimonGMT.Chapter04
