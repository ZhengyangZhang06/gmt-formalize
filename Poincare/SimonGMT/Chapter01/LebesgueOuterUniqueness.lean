module

public import Poincare.SimonGMT.Chapter01.Hausdorff
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

@[expose] public section

/-!
# Simon GMT, Chapter 1, (2.8): uniqueness of Lebesgue outer measure

The competing object is an arbitrary outer measure, not a Borel measure.
Exact countable ball coverings first give domination by volume.  Finite-volume
exhaustion and cancellation then give equality on measurable sets, and the
displayed open-set approximation property gives equality on every set.
-/

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

/-- In a Besicovitch space, upper bounds on positive-radius closed balls imply
domination of an outer measure by an outer-regular s-finite measure.  No
measurability condition on the competing outer measure is needed. -/
theorem outerMeasure_le_of_closedBall_le
    {E : Type*} [MetricSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [HasBesicovitchCovering E]
    (μ : OuterMeasure E) (ν : Measure E) [SFinite ν] [ν.OuterRegular]
    (hball : ∀ x r, 0 < r → μ (closedBall x r) ≤ ν (closedBall x r)) :
    μ ≤ ν.toOuterMeasure := by
  intro s
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨t, r, ht, _, hr, hcover, hsum⟩ :=
    Besicovitch.exists_closedBall_covering_tsum_measure_le ν
      (show (ε : ℝ≥0∞) ≠ 0 by exact_mod_cast hε.ne') (fun _ => Ioi 0) s
      (fun _ _ δ hδ => ⟨δ / 2, half_pos hδ, half_pos hδ, half_lt_self hδ⟩)
  let : Countable t := ht.to_subtype
  calc
    μ s ≤ μ (⋃ x ∈ t, closedBall x (r x)) := measure_mono hcover
    _ = μ (⋃ x : t, closedBall (x : E) (r x)) := by rw [biUnion_eq_iUnion]
    _ ≤ ∑' x : t, μ (closedBall (x : E) (r x)) := measure_iUnion_le _
    _ ≤ ∑' x : t, ν (closedBall (x : E) (r x)) :=
      ENNReal.tsum_le_tsum fun x => hball x (r x) (hr x x.property)
    _ ≤ ν s + ε := hsum

/-- Domination plus agreement on a finite-measure increasing exhaustion forces
agreement on every measurable set, even when the dominated object is only an
outer measure. -/
theorem outerMeasure_eq_on_measurable_of_le_of_exhaustion
    {E : Type*} [MeasurableSpace E] (μ : OuterMeasure E) (ν : Measure E)
    (hdom : μ ≤ ν.toOuterMeasure) (K : ℕ → Set E) (hmono : Monotone K)
    (hcover : ⋃ k, K k = univ) (hfinite : ∀ k, ν (K k) ≠ ∞)
    (hK : ∀ k, μ (K k) = ν (K k)) {s : Set E} (hs : MeasurableSet s) :
    μ s = ν s := by
  refine le_antisymm (hdom s) ?_
  have hlocal (k : ℕ) : ν (K k ∩ s) ≤ μ s := by
    apply ENNReal.le_of_add_le_add_right
      (measure_lt_top_of_subset sdiff_subset (hfinite k)).ne
    calc
      ν (K k ∩ s) + ν (K k \ s) = ν (K k) := measure_inter_add_sdiff _ hs
      _ = μ (K k) := (hK k).symm
      _ ≤ μ (K k ∩ s) + μ (K k \ s) := measure_le_inter_add_sdiff μ _ _
      _ ≤ μ s + ν (K k \ s) := add_le_add (measure_mono inter_subset_right) (hdom _)
  have hmono' : Monotone (fun k => K k ∩ s) :=
    fun i j hij => inter_subset_inter_left s (hmono hij)
  have hcover' : (⋃ k, K k ∩ s) = s := by rw [← iUnion_inter, hcover, univ_inter]
  calc
    ν s = ν (⋃ k, K k ∩ s) := congrArg ν hcover'.symm
    _ = ⨆ k, ν (K k ∩ s) := hmono'.measure_iUnion
    _ ≤ μ s := iSup_le hlocal

/-- Agreement with the open-box formula already determines the outer measure
of every positive-radius ball in the coordinate sup metric. -/
theorem outerMeasure_ball_eq_volume_of_openBox
    {n : ℕ} (μ : OuterMeasure (Fin n → ℝ))
    (hbox : ∀ a b : Fin n → ℝ, (∀ i, a i < b i) →
      μ (pi univ fun i => Ioo (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i))
    (x : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    μ (ball x r) = volume (ball x r) := by
  rw [ball_pi x hr]
  simp_rw [Real.ball_eq_Ioo]
  rw [hbox (fun i => x i - r) (fun i => x i + r) (by intro i; linarith)]
  exact (lebesgueMeasure_openBox n _ _).symm

/-- The open-box formula alone bounds an arbitrary outer measure above by
Lebesgue outer measure on all sets. -/
theorem outerMeasure_le_volume_of_openBox
    {n : ℕ} (μ : OuterMeasure (Fin n → ℝ))
    (hbox : ∀ a b : Fin n → ℝ, (∀ i, a i < b i) →
      μ (pi univ fun i => Ioo (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i)) :
    μ ≤ (volume : Measure (Fin n → ℝ)).toOuterMeasure := by
  apply outerMeasure_le_of_closedBall_le
  intro x r hr
  rw [Real.volume_pi_closedBall x hr.le]
  have hcont : Continuous (fun R : ℝ => ENNReal.ofReal ((2 * R) ^ Fintype.card (Fin n))) :=
    ENNReal.continuous_ofReal.comp ((continuous_const.mul continuous_id).pow _)
  apply ge_of_tendsto (x := 𝓝[>] r)
    (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [eventually_mem_nhdsWithin] with R hR
  calc
    μ (closedBall x r) ≤ μ (ball x R) := measure_mono (closedBall_subset_ball hR)
    _ = volume (ball x R) := outerMeasure_ball_eq_volume_of_openBox μ hbox x (hr.trans hR)
    _ = ENNReal.ofReal ((2 * R) ^ Fintype.card (Fin n)) := Real.volume_pi_ball x (hr.trans hR)

/-- Simon (2.8), uniqueness direction with the literal two properties.  The
candidate is only an outer measure; Borel measurability is not an assumption. -/
theorem lebesgueOuterMeasure_unique
    {n : ℕ} (μ : OuterMeasure (Fin n → ℝ))
    (hbox : ∀ a b : Fin n → ℝ, (∀ i, a i < b i) →
      μ (pi univ fun i => Ioo (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i))
    (hopen : ∀ A : Set (Fin n → ℝ),
      μ A = ⨅ (U : Set (Fin n → ℝ)) (_ : A ⊆ U) (_ : IsOpen U), μ U) :
    μ = (volume : Measure (Fin n → ℝ)).toOuterMeasure := by
  have hdom := outerMeasure_le_volume_of_openBox μ hbox
  have hmeas {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) : μ s = volume s := by
    apply outerMeasure_eq_on_measurable_of_le_of_exhaustion μ volume hdom
      (fun k : ℕ => ball 0 (k + 1 : ℝ))
    · intro i j hij
      exact ball_subset_ball (by exact_mod_cast Nat.add_le_add_right hij 1)
    · exact iUnion_ball_nat_succ 0
    · intro k
      rw [Real.volume_pi_ball (0 : Fin n → ℝ) (by positivity)]
      exact ENNReal.ofReal_ne_top
    · intro k
      exact outerMeasure_ball_eq_volume_of_openBox μ hbox 0 (by positivity)
    · exact hs
  apply OuterMeasure.ext
  intro A
  change μ A = volume A
  rw [hopen A, lebesgueMeasure_eq_iInf_isOpen n A]
  apply iInf_congr
  intro U
  apply iInf_congr
  intro _
  apply iInf_congr
  intro hU
  exact hmeas hU.measurableSet

/-- Simon (2.8): the box-volume and open-superset infimum formulas uniquely
characterize Lebesgue measure among all outer measures on `ℝⁿ`. -/
theorem simon_theorem_2_8 (n : ℕ) (μ : OuterMeasure (Fin n → ℝ)) :
    μ = (volume : Measure (Fin n → ℝ)).toOuterMeasure ↔
      (∀ a b : Fin n → ℝ, (∀ i, a i < b i) →
        μ (pi univ fun i => Ioo (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i)) ∧
      (∀ A : Set (Fin n → ℝ),
        μ A = ⨅ (U : Set (Fin n → ℝ)) (_ : A ⊆ U) (_ : IsOpen U), μ U) := by
  constructor
  · rintro rfl
    exact ⟨fun a b _ => lebesgueMeasure_openBox n a b, lebesgueMeasure_eq_iInf_isOpen n⟩
  · rintro ⟨hbox, hopen⟩
    exact lebesgueOuterMeasure_unique μ hbox hopen

end Poincare.SimonGMT.Chapter01
