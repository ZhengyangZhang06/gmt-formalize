module

public import Mathlib.MeasureTheory.Covering.Vitali

public section

/-!
# Simon GMT, Chapter 1, §3: the five-times covering lemma

The size bound in (3.4) is a bound on the actual diameters of the balls,
not a bound on their chosen radii.  This distinction matters in a general
metric space.  The selection below retains the intersection and diameter
comparison in the source's stronger conclusion (⋆).
-/

open Metric Set
open scoped ENNReal

namespace Poincare.SimonGMT.Chapter01

variable {X ι : Type*} [PseudoMetricSpace X]

/-- Simon (3.4), including the stronger intersection/diameter assertion.
Zero-radius balls are allowed as well as the positive-radius source balls;
neither separability nor a bound on the chosen radii is assumed. -/
theorem exists_fiveTimesCovering
    (B : Set ι) (c : ι → X) (r : ι → ℝ)
    (hr : ∀ i ∈ B, 0 ≤ r i) (R : ℝ)
    (hR : ∀ i ∈ B, diam (closedBall (c i) (r i)) ≤ R) :
    ∃ D ⊆ B,
      D.PairwiseDisjoint (fun i => closedBall (c i) (r i)) ∧
      ∀ i ∈ B, ∃ j ∈ D,
        (closedBall (c i) (r i) ∩ closedBall (c j) (r j)).Nonempty ∧
        diam (closedBall (c i) (r i)) ≤ 2 * diam (closedBall (c j) (r j)) ∧
        closedBall (c i) (r i) ⊆ closedBall (c j) (5 * r j) := by
  obtain ⟨D, hDB, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun i => closedBall (c i) (r i)) B
      (fun i => diam (closedBall (c i) (r i))) 2 (by norm_num)
      (fun _ _ => diam_nonneg) R hR
      (fun i hi => ⟨c i, mem_closedBall_self (hr i hi)⟩)
  refine ⟨D, hDB, hdisj, fun i hi => ?_⟩
  obtain ⟨j, hj, hij, hdiam⟩ := hcover i hi
  refine ⟨j, hj, hij, hdiam, fun z hz => ?_⟩
  obtain ⟨w, hwi, hwj⟩ := hij
  have hzw := dist_le_diam_of_mem isBounded_closedBall hz hwi
  have hrj := hr j (hDB hj)
  have hdj : diam (closedBall (c j) (r j)) ≤ 2 * r j :=
    diam_le_of_forall_dist_le (by positivity) fun y hy z hz =>
      (dist_triangle y (c j) z).trans (by
        have hy' := mem_closedBall.mp hy
        have hz' := mem_closedBall.mp hz
        rw [dist_comm (c j) z]
        linarith)
  have hwj' := mem_closedBall.mp hwj
  have htri := dist_triangle z w (c j)
  rw [mem_closedBall]
  linarith

/-- The covering assertion in Simon (3.4), extracted from its stronger
selection property. -/
theorem fiveTimesCovering_covers
    (B D : Set ι) (c : ι → X) (r : ι → ℝ)
    (hcover : ∀ i ∈ B, ∃ j ∈ D,
      closedBall (c i) (r i) ⊆ closedBall (c j) (5 * r j)) :
    (⋃ i ∈ B, closedBall (c i) (r i)) ⊆
      ⋃ j ∈ D, closedBall (c j) (5 * r j) := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
  obtain ⟨j, hj, hij⟩ := hcover i hi
  exact mem_iUnion₂.mpr ⟨j, hj, hij hxi⟩

/-- Simon (3.5).  Fineness is stated using the actual diameters, as in the
text.  Every finite selection can be discarded at the cost of retaining
the five-times enlargements of the remaining selected balls. -/
theorem fiveTimesCovering_finite_remainder
    (A : Set X) (B D : Set ι) (c : ι → X) (r : ι → ℝ)
    (hfine : ∀ x ∈ A, ∀ ε > 0, ∃ i ∈ B,
      x ∈ closedBall (c i) (r i) ∧ diam (closedBall (c i) (r i)) < ε)
    (hcover : ∀ i ∈ B, ∃ j ∈ D,
      (closedBall (c i) (r i) ∩ closedBall (c j) (r j)).Nonempty ∧
      closedBall (c i) (r i) ⊆ closedBall (c j) (5 * r j))
    (F : Finset ι) :
    A \ (⋃ j ∈ F, closedBall (c j) (r j)) ⊆
      ⋃ j ∈ D \ (F : Set ι), closedBall (c j) (5 * r j) := by
  classical
  intro x hx
  have hclosed : IsClosed (⋃ j ∈ F, closedBall (c j) (r j)) :=
    isClosed_biUnion_finset fun _ _ => isClosed_closedBall
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hx.2)
  obtain ⟨i, hi, hxi, hdiam⟩ := hfine x hx.1 ε hε
  have hiout : closedBall (c i) (r i) ⊆
      (⋃ j ∈ F, closedBall (c j) (r j))ᶜ := by
    intro y hy
    exact hball ((dist_le_diam_of_mem isBounded_closedBall hy hxi).trans_lt hdiam)
  obtain ⟨j, hj, hij, hsub⟩ := hcover i hi
  refine mem_iUnion₂.mpr ⟨j, ⟨hj, ?_⟩, hsub hxi⟩
  intro hjF
  obtain ⟨y, hyi, hyj⟩ := hij
  exact hiout hyi (mem_iUnion₂.mpr ⟨j, hjF, hyj⟩)

/-- Simon Definition (3.10), for an outer measure and arbitrary finite-mass
sets.  The indexed balls have positive radii and centers in `A`; fineness
is centered fineness, exactly as in the source's parenthetical formula.
The selected collection is permitted to be finite or empty. -/
@[expose] def HasSymmetricVitaliProperty (μ : MeasureTheory.OuterMeasure X) : Prop :=
  ∀ (A : Set X), μ A < ∞ → ∀ (B : Set (X × ℝ)),
    (∀ b ∈ B, b.1 ∈ A ∧ 0 < b.2) →
    (∀ x ∈ A, ∀ ε > 0, ∃ r ∈ Set.Ioo 0 ε, (x, r) ∈ B) →
    ∃ D ⊆ B, D.Countable ∧
      D.PairwiseDisjoint (fun b => closedBall b.1 b.2) ∧
      μ (A \ ⋃ b ∈ D, closedBall b.1 b.2) = 0

end Poincare.SimonGMT.Chapter01
