module

public import Poincare.SimonGMT.Chapter04.WeightedBallInequalities
public import Poincare.SimonGMT.Chapter01.DensityCovering

@[expose] public section

/-!
# The five-times covering step in Simon's proof of (5.7)

The local good-radius inequalities are explicit hypotheses. The disjoint
selection, countability, covering, summation, and removal of almost-everywhere
exceptional sets are proved here. `SobolevGoodRadius` supplies these hypotheses
from the corrected calculus lemma and the geometric lower-density input.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace.SeparableSpace E]

/-- The exact measure-theoretic covering/summation argument on printed
page 99: a good ball at each point gives a countable disjoint subfamily,
whose fivefold dilates cover the set. The constant is unchanged. -/
theorem measure_le_of_fiveTimes_ball_bounds (η ν : Measure E)
    (A : Set E) (r : E → ℝ) {R : ℝ}
    (hr : ∀ x ∈ A, 0 < r x) (hR : ∀ x ∈ A, r x ≤ R)
    {C : ℝ≥0∞} (hball : ∀ x ∈ A,
      η (closedBall x (5 * r x)) ≤ C * ν (closedBall x (r x))) :
    ∃ D ⊆ A, D.Countable ∧ D.PairwiseDisjoint (fun x ↦ closedBall x (r x)) ∧
      A ⊆ ⋃ x ∈ D, closedBall x (5 * r x) ∧ η A ≤ C * ν univ := by
  obtain ⟨D, hDA, hdisj, hcover⟩ := Chapter01.exists_fiveTimesCovering A id r
    (fun x hx ↦ (hr x hx).le) (2 * R)
    (fun x hx ↦ (diam_closedBall (hr x hx).le).trans (by nlinarith [hR x hx]))
  have hDcount : D.Countable := hdisj.countable_of_nonempty_interior fun x hx ↦
    (nonempty_ball.mpr (hr x (hDA hx))).mono ball_subset_interior_closedBall
  have hcoverA : A ⊆ ⋃ x ∈ D, closedBall x (5 * r x) := by
    intro x hx
    obtain ⟨y, hy, _, _, hxy⟩ := hcover x hx
    exact mem_iUnion₂.mpr ⟨y, hy, hxy (mem_closedBall_self (hr x hx).le)⟩
  refine ⟨D, hDA, hDcount, hdisj, hcoverA, ?_⟩
  let : Countable D := hDcount.to_subtype
  have hdisj' : Pairwise (fun x y : D ↦
      Disjoint (closedBall x.val (r x)) (closedBall y.val (r y))) :=
    fun x y hxy ↦ hdisj x.property y.property (Subtype.coe_ne_coe.mpr hxy)
  have hsub : A ⊆ ⋃ x : D, closedBall x.val (5 * r x) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcoverA hx)
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩
  calc
    η A ≤ η (⋃ x : D, closedBall x.val (5 * r x)) := measure_mono hsub
    _ ≤ ∑' x : D, η (closedBall x.val (5 * r x)) := measure_iUnion_le _
    _ ≤ ∑' x : D, C * ν (closedBall x.val (r x)) :=
      ENNReal.tsum_le_tsum fun x ↦ hball x.val (hDA x.property)
    _ = C * ∑' x : D, ν (closedBall x.val (r x)) := ENNReal.tsum_mul_left
    _ = C * ν (⋃ x : D, closedBall x.val (r x)) := by
      rw [measure_iUnion hdisj' (fun _ ↦ measurableSet_closedBall)]
    _ ≤ C * ν univ := mul_le_mul_right (measure_mono (subset_univ _)) _

/-- The weighted version used in (5.7): from selected-radius control of
`∫_{B(5r)} h` by `C ∫_{B(r)} q`, derive the global superlevel estimate.
Extended integrals allow infinite energy without a false Bochner default. -/
theorem lintegral_le_of_fiveTimes_ball_bounds (μ : Measure E)
    (A : Set E) (hA : MeasurableSet A) (h q : E → ℝ≥0∞) (r : E → ℝ)
    {R : ℝ} (hr : ∀ x ∈ A, 0 < r x) (hR : ∀ x ∈ A, r x ≤ R)
    {C : ℝ≥0∞} (hball : ∀ x ∈ A,
      (∫⁻ y in closedBall x (5 * r x), h y ∂μ) ≤
        C * ∫⁻ y in closedBall x (r x), q y ∂μ) :
    (∫⁻ x in A, h x ∂μ) ≤ C * ∫⁻ x, q x ∂μ := by
  obtain ⟨D, hDA, hDcount, hdisj, hcover, hle⟩ := measure_le_of_fiveTimes_ball_bounds
    (μ.withDensity h) (μ.withDensity q) A r hr hR (C := C) (fun x hx ↦ by
      simpa only [withDensity_apply _ measurableSet_closedBall] using hball x hx)
  simpa only [withDensity_apply _ hA, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using hle

/-- Existential good radii suffice; a choice of radii is made inside the
proof. This is the precise interface needed after Simon's calculus lemma. -/
theorem lintegral_le_of_exists_good_radius (μ : Measure E)
    (A : Set E) (hA : MeasurableSet A) (h q : E → ℝ≥0∞) {R : ℝ} {C : ℝ≥0∞}
    (hgood : ∀ x ∈ A, ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      (∫⁻ y in closedBall x (5 * r), h y ∂μ) ≤
        C * ∫⁻ y in closedBall x r, q y ∂μ) :
    (∫⁻ x in A, h x ∂μ) ≤ C * ∫⁻ x, q x ∂μ := by
  classical
  choose r hrpos hrR hrbound using hgood
  let r' : E → ℝ := fun x ↦ if hx : x ∈ A then r x hx else 1
  apply lintegral_le_of_fiveTimes_ball_bounds μ A hA h q r' (R := R)
  · intro x hx
    simpa only [r', dite_eq_left hx] using hrpos x hx
  · intro x hx
    simpa only [r', dite_eq_left hx] using hrR x hx
  · intro x hx
    simpa only [r', dite_eq_left hx] using hrbound x hx

/-- Good radii are needed only almost everywhere. A measurable null
superset of the exceptional set is removed before selecting the balls;
no measurability of the pointwise good-radius predicate is assumed. -/
theorem lintegral_le_of_ae_exists_good_radius (μ : Measure E)
    (A : Set E) (hA : MeasurableSet A) (h q : E → ℝ≥0∞) {R : ℝ} {C : ℝ≥0∞}
    (hgood : ∀ᵐ x ∂μ, x ∈ A → ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      (∫⁻ y in closedBall x (5 * r), h y ∂μ) ≤
        C * ∫⁻ y in closedBall x r, q y ∂μ) :
    (∫⁻ x in A, h x ∂μ) ≤ C * ∫⁻ x, q x ∂μ := by
  obtain ⟨N, hNsub, hNm, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  have hle := lintegral_le_of_exists_good_radius μ (A \ N) (hA.diff hNm) h q
    (R := R) (C := C) (by
      intro x hx
      exact Classical.not_not.mp (fun hbad ↦ hx.2 (hNsub hbad)) hx.1)
  rwa [setLIntegral_congr (sdiff_null_ae_eq_self hNzero)] at hle

end

end Poincare.SimonGMT.Chapter04
