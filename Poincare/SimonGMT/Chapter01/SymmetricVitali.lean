module

public import Poincare.SimonGMT.Chapter01.DensityComparison

@[expose] public section

/-!
# Simon GMT, Chapter 1, symmetric Vitali covering and relative density

This module works with the literal symmetric Vitali property of (3.10).
The doubling hypothesis below belongs only to the sufficient condition
printed in Remark (3.11)(2), not to the subsequent comparison theorems.
-/

open Filter Metric Set MeasureTheory
open scoped ENNReal NNReal Topology Classical

namespace Poincare.SimonGMT.Chapter01

variable {X : Type*} [PseudoMetricSpace X]

/-- The finite-mass step of Simon Remark (3.11)(1).  A finely covered
subset of the zero-ball region is null under the symmetric Vitali property. -/
theorem HasSymmetricVitaliProperty.measure_inter_zeroBallRegion_eq_zero
    {μ : OuterMeasure X} (hV : HasSymmetricVitaliProperty μ)
    {S : Set X} (hS : μ S < ∞) : μ (S ∩ zeroBallRegion μ) = 0 := by
  let A := S ∩ zeroBallRegion μ
  let B : Set (X × ℝ) := {b | b.1 ∈ A ∧ 0 < b.2 ∧ μ (closedBall b.1 b.2) = 0}
  have hfine : ∀ x ∈ A, ∀ ε > 0, ∃ r ∈ Ioo 0 ε, (x, r) ∈ B := by
    intro x hx ε hε
    obtain ⟨R, hR, hμR⟩ := hx.2
    let r := min R (ε / 2)
    have hr : 0 < r := lt_min hR (half_pos hε)
    refine ⟨r, ⟨hr, (min_le_right _ _).trans_lt (half_lt_self hε)⟩,
      hx, hr, ?_⟩
    exact measure_mono_null (closedBall_subset_closedBall (min_le_left _ _)) hμR
  obtain ⟨D, hDB, hDcount, _, hDnull⟩ := hV A
    ((μ.mono inter_subset_left).trans_lt hS) B
    (fun b hb => ⟨hb.1, hb.2.1⟩) hfine
  have hballs : μ (⋃ b ∈ D, closedBall b.1 b.2) = 0 :=
    (measure_biUnion_null_iff hDcount).mpr fun b hb => (hDB hb).2.2
  exact (measure_sdiff_null hballs).symm.trans hDnull

/-- Simon Remark (3.11)(1), the sigma-finite symmetric-Vitali case.
The finite-mass cover need not consist of measurable or open sets. -/
theorem HasSymmetricVitaliProperty.zeroBallRegion_eq_zero_of_countable_cover
    {μ : OuterMeasure X} (hV : HasSymmetricVitaliProperty μ)
    (S : ℕ → Set X) (hS : ∀ j, μ (S j) < ∞) (hcover : ⋃ j, S j = univ) :
    μ (zeroBallRegion μ) = 0 := by
  have heq : zeroBallRegion μ = ⋃ j, S j ∩ zeroBallRegion μ := by
    rw [← iUnion_inter, hcover, univ_inter]
  rw [heq]
  exact measure_iUnion_null fun j => hV.measure_inter_zeroBallRegion_eq_zero (hS j)

/-- The open-sigma-finite instance of (3.11)(1) used in (3.13)--(3.17). -/
theorem HasSymmetricVitaliProperty.zeroBallRegion_eq_zero_of_openSigmaFinite
    {μ : OuterMeasure X} (hV : HasSymmetricVitaliProperty μ)
    (hopen : IsOpenSigmaFinite μ) : μ (zeroBallRegion μ) = 0 := by
  obtain ⟨S, hS, hcover⟩ := (isOpenSigmaFinite_iff μ).mp hopen
  exact hV.zeroBallRegion_eq_zero_of_countable_cover S (fun j => (hS j).2) hcover

/-- The literal `C³` enlargement estimate in Simon Remark (3.11)(2). -/
theorem fiveTimes_mass_le_of_doubling
    (μ : OuterMeasure X) (C : ℝ≥0)
    (hdouble : ∀ x r, 0 < r → μ (closedBall x (2 * r)) ≤ C * μ (closedBall x r))
    (x : X) {r : ℝ} (hr : 0 < r) :
    μ (closedBall x (5 * r)) ≤ (C : ℝ≥0∞) ^ 3 * μ (closedBall x r) := by
  calc
    μ (closedBall x (5 * r)) ≤ μ (closedBall x (2 * (2 * (2 * r)))) :=
      μ.mono (closedBall_subset_closedBall (by linarith))
    _ ≤ C * μ (closedBall x (2 * (2 * r))) := hdouble x _ (by positivity)
    _ ≤ C * (C * μ (closedBall x (2 * r))) := by gcongr; exact hdouble x _ (by positivity)
    _ ≤ C * (C * (C * μ (closedBall x r))) := by gcongr; exact hdouble x r hr
    _ = (C : ℝ≥0∞) ^ 3 * μ (closedBall x r) := by ring

/-- Simon Remark (3.11)(2), under precisely the source's separability,
finite-total-mass and doubling assumptions.  The measure and the set of
centers need not be complete or Borel measurable respectively. -/
theorem hasSymmetricVitaliProperty_of_finite_doubling
    [TopologicalSpace.SeparableSpace X]
    (μ : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ) (hfin : μ univ < ∞)
    (C : ℝ≥0)
    (hdouble : ∀ x r, 0 < r → μ (closedBall x (2 * r)) ≤ C * μ (closedBall x r)) :
    HasSymmetricVitaliProperty μ := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let ν := hμ.toBorelMeasure
  let : IsFiniteMeasure ν := ⟨by simpa only [ν, hμ.toBorelMeasure_apply_all] using hfin⟩
  intro A _ B hB hfine
  have htriple : ∀ b ∈ B,
      ν (closedBall b.1 (3 * b.2)) ≤ (C ^ 2 : ℝ≥0) * ν (closedBall b.1 b.2) := by
    intro b hb
    simp only [ν, hμ.toBorelMeasure_apply_all, ENNReal.coe_pow]
    calc
      μ (closedBall b.1 (3 * b.2)) ≤ μ (closedBall b.1 (2 * (2 * b.2))) :=
        μ.mono (closedBall_subset_closedBall (by have := (hB b hb).2; linarith))
      _ ≤ C * μ (closedBall b.1 (2 * b.2)) := hdouble _ _ (by have := (hB b hb).2; positivity)
      _ ≤ C * (C * μ (closedBall b.1 b.2)) := by gcongr; exact hdouble _ _ (hB b hb).2
      _ = (C : ℝ≥0∞) ^ 2 * μ (closedBall b.1 b.2) := by ring
  have hinterior : ∀ b ∈ B, (interior (closedBall b.1 b.2)).Nonempty := by
    intro b hb
    exact ⟨b.1, ball_subset_interior_closedBall (mem_ball_self (hB b hb).2)⟩
  have hfine' : ∀ x ∈ A, ∀ ε > 0, ∃ b ∈ B, b.2 ≤ ε ∧ b.1 = x := by
    intro x hx ε hε
    obtain ⟨r, hr, hxr⟩ := hfine x hx ε hε
    exact ⟨(x, r), hxr, hr.2.le, rfl⟩
  obtain ⟨D, hDB, hDcount, hDdisj, hDnull⟩ := Vitali.exists_disjoint_covering_ae ν A B
    (C ^ 2) Prod.snd Prod.fst (fun b => closedBall b.1 b.2)
    (fun _ _ => Subset.rfl) htriple hinterior (fun _ _ => isClosed_closedBall) hfine'
  exact ⟨D, hDB, hDcount, hDdisj, by
    simpa only [ν, hμ.toBorelMeasure_apply_all] using hDnull⟩

end Poincare.SimonGMT.Chapter01
