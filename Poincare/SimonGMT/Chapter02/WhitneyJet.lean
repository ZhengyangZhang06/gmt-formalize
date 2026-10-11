module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-!
# Simon GMT, Chapter 2, §1: compatible first-order Whitney data

This file records the actual compatibility hypothesis of Theorem 1.6 and
proves the affine error estimates used in its construction.  Derivatives
are represented as continuous linear maps; in Euclidean space this is
equivalent to the book's gradient representation.

The nearest-anchor affine construction below interpolates the value and
derivative at every point of the closed set.  It is only a preliminary
construction: no continuity away from the set, or global C¹ extension,
is asserted here.
-/

open Filter Set Metric
open scoped Topology

namespace Poincare.SimonGMT.Chapter02

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Simon's continuous value and gradient data, with the normalized Taylor
remainder tending uniformly to zero as the base point ranges over each
compact subset.  The values of `h` and `D` outside `A` are irrelevant. -/
structure HasWhitneyC1Compatibility
    (A : Set E) (h : E → ℝ) (D : E → E →L[ℝ] ℝ) : Prop where
  continuous_value : ContinuousOn h A
  continuous_derivative : ContinuousOn D A
  remainder : ∀ K : Set E, IsCompact K → K ⊆ A →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ K, ∀ y ∈ A, dist x y < δ →
        ‖h y - h x - D x (y - x)‖ ≤ ε * ‖y - x‖

/-- The affine first-order polynomial attached to an anchor. -/
def whitneyAffine (h : E → ℝ) (D : E → E →L[ℝ] ℝ) (a x : E) : ℝ :=
  h a + D a (x - a)

@[simp] theorem whitneyAffine_self
    (h : E → ℝ) (D : E → E →L[ℝ] ℝ) (a : E) : whitneyAffine h D a a = h a := by
  simp [whitneyAffine]

/-- The difference of two anchor polynomials is a Whitney remainder plus
the difference of their derivative fields applied to the residual vector. -/
theorem whitneyAffine_sub_eq
    (h : E → ℝ) (D : E → E →L[ℝ] ℝ) (a b x : E) :
    whitneyAffine h D b x - whitneyAffine h D a x =
      (h b - h a - D a (b - a)) + (D b - D a) (x - b) := by
  have hx : x - a = (x - b) + (b - a) := by abel
  simp only [whitneyAffine, hx, map_add, ContinuousLinearMap.sub_apply]
  ring

theorem norm_whitneyAffine_sub_le
    (h : E → ℝ) (D : E → E →L[ℝ] ℝ) (a b x : E) :
    ‖whitneyAffine h D b x - whitneyAffine h D a x‖ ≤
      ‖h b - h a - D a (b - a)‖ + ‖D b - D a‖ * ‖x - b‖ := by
  rw [whitneyAffine_sub_eq]
  exact (norm_add_le _ _).trans
    (add_le_add le_rfl ((D b - D a).le_opNorm (x - b)))

/-- Compact-uniform compatibility in particular gives the prescribed
derivative within the closed set at each point. -/
theorem HasWhitneyC1Compatibility.hasFDerivWithinAt
    {A : Set E} {h : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (H : HasWhitneyC1Compatibility A h D) {a : E} (ha : a ∈ A) :
    HasFDerivWithinAt h (D a) A a := by
  apply HasFDerivWithinAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  obtain ⟨δ, hδ, hrem⟩ := H.remainder {a} isCompact_singleton
    (singleton_subset_iff.mpr ha) ε hε
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds a hδ)] with y hyA hy
  exact hrem a (by simp) y hyA (by simpa only [Metric.mem_ball, dist_comm] using hy)

section NearestAnchor

variable [ProperSpace E] {A : Set E}

/-- Compact-uniform compatibility gives a simultaneous Taylor estimate for
all pairs of anchors near a fixed point of the closed set. This is the part
that would be false for merely pointwise compatibility. -/
theorem HasWhitneyC1Compatibility.exists_local_uniform_estimate
    {h : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (H : HasWhitneyC1Compatibility A h D) (hA : IsClosed A)
    {a : E} (ha : a ∈ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∀ b ∈ A, dist b a < δ → ‖D b - D a‖ ≤ ε) ∧
      ∀ b ∈ A, dist b a < δ → ∀ c ∈ A, dist c a < δ →
        ‖h c - h b - D b (c - b)‖ ≤ ε * ‖c - b‖ := by
  let K := A ∩ closedBall a 1
  have hK : IsCompact K := (isCompact_closedBall a 1).inter_left hA
  obtain ⟨r, hr, hrem⟩ := H.remainder K hK inter_subset_left ε hε
  obtain ⟨η, hη, hD⟩ := Metric.continuousWithinAt_iff.mp
    (H.continuous_derivative a ha) ε hε
  let δ := min 1 (min η (r / 3))
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min hη (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδη : δ ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hδr : δ ≤ r / 3 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, hδ1, ?_, ?_⟩
  · intro b hb hba
    simpa only [dist_eq_norm] using (hD hb (hba.trans_le hδη)).le
  · intro b hb hba c hc hca
    have hbK : b ∈ K := ⟨hb, hba.le.trans hδ1⟩
    apply hrem b hbK c hc
    have htri := dist_triangle b a c
    rw [dist_comm a c] at htri
    linarith

/-- A genuine nearest anchor exists because the set is closed in a proper
space.  It is not claimed that this choice is continuous. -/
def whitneyNearestAnchor (hA : IsClosed A) (hne : A.Nonempty) (x : E) : E :=
  Classical.choose (hA.exists_infDist_eq_dist hne x)

theorem whitneyNearestAnchor_mem (hA : IsClosed A) (hne : A.Nonempty) (x : E) :
    whitneyNearestAnchor hA hne x ∈ A :=
  (Classical.choose_spec (hA.exists_infDist_eq_dist hne x)).1

theorem dist_whitneyNearestAnchor_eq_infDist
    (hA : IsClosed A) (hne : A.Nonempty) (x : E) :
    dist x (whitneyNearestAnchor hA hne x) = infDist x A :=
  (Classical.choose_spec (hA.exists_infDist_eq_dist hne x)).2.symm

theorem dist_whitneyNearestAnchor_le
    (hA : IsClosed A) (hne : A.Nonempty) (x : E) {a : E} (ha : a ∈ A) :
    dist x (whitneyNearestAnchor hA hne x) ≤ dist x a := by
  rw [dist_whitneyNearestAnchor_eq_infDist]
  exact infDist_le_dist_of_mem ha

@[simp] theorem whitneyNearestAnchor_eq_self
    (hA : IsClosed A) (hne : A.Nonempty) {a : E} (ha : a ∈ A) :
    whitneyNearestAnchor hA hne a = a := by
  have h := dist_whitneyNearestAnchor_le hA hne a ha
  rw [dist_self] at h
  exact (dist_eq_zero.mp (le_antisymm h dist_nonneg)).symm

theorem dist_whitneyNearestAnchor_point_le
    (hA : IsClosed A) (hne : A.Nonempty) (x : E) {a : E} (ha : a ∈ A) :
    dist (whitneyNearestAnchor hA hne x) a ≤ 2 * dist x a := by
  calc
    dist (whitneyNearestAnchor hA hne x) a ≤
        dist (whitneyNearestAnchor hA hne x) x + dist x a := dist_triangle _ _ _
    _ = dist x (whitneyNearestAnchor hA hne x) + dist x a := by rw [dist_comm]
    _ ≤ dist x a + dist x a :=
      add_le_add_left (dist_whitneyNearestAnchor_le hA hne x ha) _
    _ = 2 * dist x a := by ring

/-- First-stage value extension by the affine polynomial at a nearest
anchor.  The derivative at each anchor is correct; smoothing on the
complement is still required for a C¹ extension. -/
def whitneyNearestAffineExtension
    (hA : IsClosed A) (hne : A.Nonempty)
    (h : E → ℝ) (D : E → E →L[ℝ] ℝ) (x : E) : ℝ :=
  whitneyAffine h D (whitneyNearestAnchor hA hne x) x

@[simp] theorem whitneyNearestAffineExtension_eq
    (hA : IsClosed A) (hne : A.Nonempty)
    (h : E → ℝ) (D : E → E →L[ℝ] ℝ) {a : E} (ha : a ∈ A) :
    whitneyNearestAffineExtension hA hne h D a = h a := by
  simp only [whitneyNearestAffineExtension, whitneyNearestAnchor_eq_self hA hne ha,
    whitneyAffine_self]

/-- The nearest-anchor extension has the prescribed full ambient
derivative at every point of the closed set.  This assertion does not
claim its derivative is continuous on the complement. -/
theorem HasWhitneyC1Compatibility.hasFDerivAt_nearestAffineExtension
    {h : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (H : HasWhitneyC1Compatibility A h D)
    (hA : IsClosed A) (hne : A.Nonempty) {a : E} (ha : a ∈ A) :
    HasFDerivAt (whitneyNearestAffineExtension hA hne h D) (D a) a := by
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have he : 0 < ε / 3 := by positivity
  obtain ⟨δ, hδ, hrem⟩ := H.remainder {a} isCompact_singleton
    (singleton_subset_iff.mpr ha) (ε / 3) he
  obtain ⟨η, hη, hD⟩ := Metric.continuousWithinAt_iff.mp
    (H.continuous_derivative a ha) (ε / 3) he
  have hsmall : 0 < min δ η / 3 := div_pos (lt_min hδ hη) (by norm_num)
  filter_upwards [Metric.ball_mem_nhds a hsmall] with x hx
  have hxa : dist x a < min δ η / 3 := hx
  let b := whitneyNearestAnchor hA hne x
  have hbA : b ∈ A := whitneyNearestAnchor_mem hA hne x
  have hba : dist b a ≤ 2 * dist x a := dist_whitneyNearestAnchor_point_le hA hne x ha
  have hxb : dist x b ≤ dist x a := dist_whitneyNearestAnchor_le hA hne x ha
  have hbaδ : dist a b < δ := by
    rw [dist_comm]
    linarith [min_le_left δ η, dist_nonneg (x := x) (y := a)]
  have hbaη : dist b a < η := by
    linarith [min_le_right δ η, dist_nonneg (x := x) (y := a)]
  have hremb := hrem a (by simp) b hbA hbaδ
  have hDb : ‖D b - D a‖ ≤ ε / 3 := by
    simpa only [dist_eq_norm] using (hD hbA hbaη).le
  have hbaNorm : ‖b - a‖ ≤ 2 * ‖x - a‖ := by simpa only [dist_eq_norm] using hba
  have hxbNorm : ‖x - b‖ ≤ ‖x - a‖ := by simpa only [dist_eq_norm] using hxb
  have hid : whitneyNearestAffineExtension hA hne h D x -
      whitneyNearestAffineExtension hA hne h D a - D a (x - a) =
      whitneyAffine h D b x - whitneyAffine h D a x := by
    rw [whitneyNearestAffineExtension_eq hA hne h D ha]
    dsimp only [whitneyNearestAffineExtension, b, whitneyAffine]
    ring
  rw [hid]
  calc
    ‖whitneyAffine h D b x - whitneyAffine h D a x‖ ≤
        ‖h b - h a - D a (b - a)‖ + ‖D b - D a‖ * ‖x - b‖ :=
      norm_whitneyAffine_sub_le h D a b x
    _ ≤ (ε / 3) * ‖b - a‖ + (ε / 3) * ‖x - b‖ :=
      add_le_add hremb (mul_le_mul_of_nonneg_right hDb (norm_nonneg _))
    _ ≤ (ε / 3) * (2 * ‖x - a‖) + (ε / 3) * ‖x - a‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hbaNorm he.le)
        (mul_le_mul_of_nonneg_left hxbNorm he.le)
    _ = ε * ‖x - a‖ := by ring

end NearestAnchor

end

end Poincare.SimonGMT.Chapter02
