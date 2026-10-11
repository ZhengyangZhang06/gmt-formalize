module

public import Poincare.SimonGMT.Chapter01.LebesgueOuterUniqueness
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

/-!
# The upper comparison in Simon (2.9)

This proves the sharp upper bound by Lebesgue measure for the literal
Gamma-normalized content at every positive scale, in every positive integer
dimension.  It does not identify the remaining Haar scalar with one: the
reverse bound is the separate isodiametric problem.
-/

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

/-- Bounds on arbitrarily small balls suffice for domination of outer measures
in a Besicovitch space. -/
theorem outerMeasure_le_of_small_closedBall_le
    {E : Type*} [MetricSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [HasBesicovitchCovering E]
    (μ : OuterMeasure E) (ν : Measure E) [SFinite ν] [ν.OuterRegular]
    {R : ℝ} (hR : 0 < R)
    (hball : ∀ x r, 0 < r → r < R → μ (closedBall x r) ≤ ν (closedBall x r)) :
    μ ≤ ν.toOuterMeasure := by
  intro s
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨t, r, ht, _, hr, hcover, hsum⟩ :=
    Besicovitch.exists_closedBall_covering_tsum_measure_le ν
      (show (ε : ℝ≥0∞) ≠ 0 by exact_mod_cast hε.ne') (fun _ => Ioo 0 R) s
      (by
        intro x hx δ hδ
        have hmin : 0 < min R δ := lt_min hR hδ
        refine ⟨min R δ / 2, ⟨half_pos hmin, ?_⟩, half_pos hmin, ?_⟩
        · exact (half_lt_self hmin).trans_le (min_le_left _ _)
        · exact (half_lt_self hmin).trans_le (min_le_right _ _))
  let : Countable t := ht.to_subtype
  calc
    μ s ≤ μ (⋃ x ∈ t, closedBall x (r x)) := measure_mono hcover
    _ = μ (⋃ x : t, closedBall (x : E) (r x)) := by rw [biUnion_eq_iUnion]
    _ ≤ ∑' x : t, μ (closedBall (x : E) (r x)) := measure_iUnion_le _
    _ ≤ ∑' x : t, ν (closedBall (x : E) (r x)) :=
      ENNReal.tsum_le_tsum fun x => hball x (r x) (hr x x.property).1 (hr x x.property).2
    _ ≤ ν s + ε := hsum

/-- Simon's natural-dimensional Gamma constant equals the coefficient in
Mathlib's Euclidean ball-volume formula. -/
theorem realUnitBallVolume_nat_eq (n : ℕ) :
    realUnitBallVolume (n : ℝ) =
      ENNReal.ofReal (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)) := by
  have hpow : Real.pi ^ ((n : ℝ) / 2) = Real.sqrt Real.pi ^ n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1
    ring
  rw [realUnitBallVolume, hpow]

/-- The Euclidean ball formula with exactly Simon's normalization. -/
theorem volume_euclidean_closedBall_eq {n : ℕ} (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    volume (closedBall x r) = realUnitBallVolume (n : ℝ) * ENNReal.ofReal r ^ n := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [EuclideanSpace.volume_closedBall, Fintype.card_fin, realUnitBallVolume_nat_eq, mul_comm]

/-- The open Euclidean ball formula with exactly Simon's normalization. -/
theorem volume_euclidean_ball_eq {n : ℕ} (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    volume (ball x r) = realUnitBallVolume (n : ℝ) * ENNReal.ofReal r ^ n := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [EuclideanSpace.volume_ball, Fintype.card_fin, realUnitBallVolume_nat_eq, mul_comm]

/-- The extended diameter bound for a closed ball, with a real radius. -/
theorem ediam_closedBall_le_ofReal_twice
    {E : Type*} [PseudoMetricSpace E] (x : E) (r : ℝ) :
    ediam (closedBall x r) ≤ ENNReal.ofReal (2 * r) := by
  apply ediam_le_of_forall_dist_le
  intro u hu v hv
  calc
    dist u v ≤ dist u x + dist x v := dist_triangle _ _ _
    _ ≤ r + r := add_le_add hu (by simpa only [mem_closedBall, dist_comm] using hv)
    _ = 2 * r := (two_mul r).symm

/-- A sufficiently small Euclidean ball has normalized content no larger
than its Lebesgue measure. -/
theorem simonHausdorffContent_closedBall_le_volume
    {n : ℕ} (hn : 0 < n) {δ : ℝ≥0∞} (x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hsmall : ENNReal.ofReal (2 * r) < δ) :
    simonHausdorffContentOuter (n : ℝ) δ (closedBall x r) ≤ volume (closedBall x r) := by
  have hd := ediam_closedBall_le_ofReal_twice x r
  have hrad : ediam (closedBall x r) / 2 ≤ ENNReal.ofReal r := by
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr
    calc
      ediam (closedBall x r) ≤ ENNReal.ofReal (2 * r) := hd
      _ = ENNReal.ofReal r * 2 := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_comm]
  have hcost : simonHausdorffCoverCost (n : ℝ) δ (closedBall x r) =
      (ediam (closedBall x r) / 2) ^ (n : ℝ) :=
    extend_eq (m := fun C (_ : ediam C < δ) => (ediam C / 2) ^ (n : ℝ))
      (s := closedBall x r) (hd.trans_lt hsmall)
  rw [simonHausdorffContentOuter, smul_apply, smul_eq_mul,
    volume_euclidean_closedBall_eq hn]
  have hle : OuterMeasure.boundedBy (simonHausdorffCoverCost (n : ℝ) δ) (closedBall x r) ≤
      ENNReal.ofReal r ^ n :=
    (OuterMeasure.boundedBy_le _).trans (by
      rw [hcost, ENNReal.rpow_natCast]
      exact pow_le_pow_left' hrad n)
  gcongr

/-- The upper half of Simon (2.9), at every positive extended scale and on
every set, with the literal normalization and strict diameter bound. -/
theorem simonHausdorffContentOuter_euclidean_le_volume
    {n : ℕ} (hn : 0 < n) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    simonHausdorffContentOuter (X := EuclideanSpace ℝ (Fin n)) (n : ℝ) δ ≤
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toOuterMeasure := by
  obtain ⟨d, _, hd, hdδ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ
  have hdpos : 0 < d := ENNReal.ofReal_pos.mp hd
  apply outerMeasure_le_of_small_closedBall_le _ volume (R := d / 2) (half_pos hdpos)
  intro x r hr hrd
  apply simonHausdorffContent_closedBall_le_volume hn x
  exact (ENNReal.ofReal_lt_ofReal_iff hdpos).mpr (by linarith) |>.trans hdδ

/-- The upper comparison for the limiting literal Hausdorff outer measure
in every positive integer dimension. -/
theorem simonHausdorffOuterMeasureReal_euclidean_le_volume
    {n : ℕ} (hn : 0 < n) :
    simonHausdorffOuterMeasureReal (X := EuclideanSpace ℝ (Fin n)) (n : ℝ) ≤
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toOuterMeasure := by
  rw [simonHausdorffOuterMeasureReal]
  exact iSup_le fun δ => iSup_le fun hδ => simonHausdorffContentOuter_euclidean_le_volume hn hδ

end Poincare.SimonGMT.Chapter01
