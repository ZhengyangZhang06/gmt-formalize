module

public import Poincare.SimonGMT.Chapter08.StationaryMonotonicity
public import Poincare.SimonGMT.Chapter08.ConstancySupport
public import Poincare.SimonGMT.Chapter01.Hausdorff
public import Mathlib.Topology.Compactness.Lindelof

@[expose] public section

/-!
# Hausdorff absolute continuity of stationary varifold weights

The absolute-continuity step in Simon (8.4.1), printed pp. 214--215,
follows already from stationary monotonicity. No rectifiability or
manifold density is needed for this step. We first turn actual uniform
small-ball growth into domination by Hausdorff measure, then obtain that
growth from the checked first-variation monotonicity formula.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The zero-radius endpoint of a small-ball growth bound. This includes
dimension zero and does not assume that the measure has no atoms. -/
theorem closedBall_zero_growth_bound
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (x : X) {n : ℕ} {R : ℝ} (hR : 0 < R)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ∀ r : ℝ, 0 < r → r ≤ R → μ (closedBall x r) ≤ C * (ENNReal.ofReal r) ^ n) :
    μ (closedBall x 0) ≤ C * (0 : ℝ≥0∞) ^ n := by
  have hid : Tendsto (fun r : ℝ ↦ r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hlim : Tendsto (fun r : ℝ ↦ C * (ENNReal.ofReal r) ^ n) (𝓝[>] 0)
      (𝓝 (C * (0 : ℝ≥0∞) ^ n)) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.Tendsto.const_mul
        (ENNReal.Tendsto.pow (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hid))
        (Or.inr hC)
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  exact (measure_mono (closedBall_subset_closedBall hr.1.le)).trans (h r hr.1 hr.2.le)

/-- A local Frostman comparison, proved from diameter covers and actual
small-ball estimates. All sets, not just measurable sets, are controlled. -/
theorem restrict_le_smul_hausdorff_of_ball_growth
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) {K : Set X} (hK : MeasurableSet K)
    {n : ℕ} {R : ℝ} (hR : 0 < R) {C : ℝ≥0∞} (hC : C ≠ ∞) (hC₀ : C ≠ 0)
    (h : ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ R →
      μ (closedBall x r) ≤ C * (ENNReal.ofReal r) ^ n) :
    μ.restrict K ≤ C • Measure.hausdorffMeasure (n : ℝ) := by
  have hdiam (s : Set X) (hs : ediam s ≤ ENNReal.ofReal R) :
      (μ.restrict K).toOuterMeasure s ≤ C * (ediam s) ^ n := by
    rw [Measure.toOuterMeasure_apply, Measure.restrict_apply' hK]
    rcases (s ∩ K).eq_empty_or_nonempty with he | ⟨x, hxs, hxK⟩
    · simp only [he, measure_empty, zero_le]
    have hsfin : ediam s ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
    have hdR : (ediam s).toReal ≤ R := ENNReal.toReal_le_of_le_ofReal hR.le hs
    have hsub : s ∩ K ⊆ closedBall x (ediam s).toReal := by
      intro y hy
      change dist y x ≤ (ediam s).toReal
      simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using
        (ENNReal.toReal_mono hsfin (edist_le_ediam_of_mem hy.1 hxs))
    apply (measure_mono hsub).trans
    by_cases hd : 0 < (ediam s).toReal
    · simpa only [ENNReal.ofReal_toReal hsfin] using h x hxK _ hd hdR
    · have hd0 : (ediam s).toReal = 0 := le_antisymm (not_lt.mp hd) ENNReal.toReal_nonneg
      have hed0 : ediam s = 0 := by
        rw [← ENNReal.ofReal_toReal hsfin, hd0, ENNReal.ofReal_zero]
      rw [hd0, hed0]
      exact closedBall_zero_growth_bound μ x hR hC (h x hxK)
  have hm := OuterMeasure.le_mkMetric (fun d : ℝ≥0∞ ↦ C * d ^ n)
    (μ.restrict K).toOuterMeasure (ENNReal.ofReal R) (ENNReal.ofReal_pos.mpr hR) hdiam
  have hcost : (fun d : ℝ≥0∞ ↦ C * d ^ n) = C • (fun d : ℝ≥0∞ ↦ d ^ (n : ℝ)) := by
    funext d
    simp only [Pi.smul_apply, smul_eq_mul, ENNReal.rpow_natCast]
  rw [hcost, OuterMeasure.mkMetric_smul _ hC hC₀] at hm
  rw [← Measure.toOuterMeasure_le, Measure.smul_toOuterMeasure]
  simpa only [Measure.hausdorffMeasure, Measure.mkMetric_toOuterMeasure] using hm

/-- Countable-cover globalization of local absolute continuity. -/
theorem absolutelyContinuous_of_local_restrictions
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ ν : Measure X} {D : Set X} (hD : ∀ᵐ x ∂μ, x ∈ D)
    (hloc : ∀ x ∈ D, ∃ A : Set X, IsOpen A ∧ x ∈ A ∧ μ.restrict A ≪ ν) :
    μ ≪ ν := by
  classical
  choose A hAo hxA hc using fun x : D ↦ hloc x x.2
  have hcover : D ⊆ ⋃ x : D, A x := fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hxA ⟨x, hx⟩⟩
  obtain ⟨T, hTc, hTD⟩ := (HereditarilyLindelofSpace.isLindelof D).elim_countable_subcover
    A hAo hcover
  intro s hs
  have hlocal : ∀ᵐ x ∂μ.restrict (⋃ i ∈ T, A i), x ∉ s := by
    apply (ae_restrict_biUnion_iff A hTc (fun x ↦ x ∉ s)).mpr
    intro i _
    simpa only [ae_iff, not_not, ofPred_mem_eq] using hc i hs
  have hglobal := ae_restrict_of_ae_restrict_of_subset hTD hlocal
  rw [Measure.restrict_eq_self_of_ae_mem hD] at hglobal
  simpa only [ae_iff, not_not, ofPred_mem_eq] using hglobal

namespace Varifold
variable {N n : ℕ} {U : Set (Euclidean N)}

/-- Uniform growth at all centers in an interior ball, obtained from
stationary monotonicity and the mass of one larger compact ball. -/
theorem Stationary.exists_uniform_ball_growth {V : Varifold N n U}
    (hV : V.Stationary) (a : Euclidean N) {R : ℝ} (hR : 0 < R)
    (hball : closedBall a (3 * R) ⊆ U) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ∞ ∧ ∀ x ∈ ball a R, ∀ r : ℝ,
      0 < r → r ≤ R → V.weight (closedBall x r) ≤ C * (ENNReal.ofReal r) ^ n := by
  let C : ℝ≥0∞ := 1 + V.weight (closedBall a (2 * R)) / ENNReal.ofReal (R ^ n)
  have hden : ENNReal.ofReal (R ^ n) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hR n)).ne'
  have hsmall : closedBall a (2 * R) ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans hball
  have hC : C ≠ ∞ := ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top,
    ENNReal.div_ne_top (V.weight_finite_on_compact _ (isCompact_closedBall a (2 * R)) hsmall) hden⟩
  refine ⟨C, (lt_of_lt_of_le zero_lt_one (le_add_right le_rfl)).ne', hC, ?_⟩
  intro x hx r hr hrR
  have hxball : closedBall x (2 * R) ⊆ U := by
    intro y hy
    apply hball
    change dist y a ≤ 3 * R
    have hxa : dist x a < R := hx
    have hyx : dist y x ≤ 2 * R := hy
    linarith [dist_triangle y x a]
  have hmass : V.weight (closedBall x R) ≤ V.weight (closedBall a (2 * R)) := by
    apply measure_mono
    intro y hy
    change dist y a ≤ 2 * R
    have hxa : dist x a < R := hx
    have hyx : dist y x ≤ R := hy
    linarith [dist_triangle y x a]
  have hmono := (hV.stationaryOn (ball x (2 * R))).normalizedBallMass_monotoneOn hxball
    (show r ∈ Ioo 0 (2 * R) from ⟨hr, by linarith⟩)
    (show R ∈ Ioo 0 (2 * R) from ⟨hR, by linarith⟩) hrR
  have hbound : V.weight (closedBall x r) / ENNReal.ofReal (r ^ n) ≤ C := by
    apply hmono.trans
    change V.weight (closedBall x R) / ENNReal.ofReal (R ^ n) ≤ C
    exact (ENNReal.div_le_div_right hmass _).trans (le_add_left le_rfl)
  have hrden : ENNReal.ofReal (r ^ n) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr n)).ne'
  have hgrowth := (ENNReal.div_le_iff hrden ENNReal.ofReal_ne_top).mp hbound
  simpa only [ENNReal.ofReal_pow hr.le] using hgrowth

/-- Every stationary general `n`-varifold has weight absolutely
continuous with respect to `n`-dimensional Hausdorff measure. -/
theorem Stationary.weight_absolutelyContinuous_hausdorff {V : Varifold N n U}
    (hV : V.Stationary) : V.weight ≪ Measure.hausdorffMeasure (n : ℝ) := by
  apply absolutelyContinuous_of_local_restrictions (D := U)
  · rw [ae_iff]
    change V.weight Uᶜ = 0
    rw [V.weight_apply V.isOpen_domain.measurableSet.compl]
    exact V.supported
  · intro a ha
    obtain ⟨s, hs, hsU⟩ := nhds_basis_closedBall.mem_iff.mp (V.isOpen_domain.mem_nhds ha)
    have hR : 0 < s / 3 := by positivity
    have hball : closedBall a (3 * (s / 3)) ⊆ U := by
      simpa only [show 3 * (s / 3) = s by ring] using hsU
    obtain ⟨C, hC₀, hC, hgrowth⟩ := hV.exists_uniform_ball_growth a hR hball
    refine ⟨ball a (s / 3), isOpen_ball, mem_ball_self hR, ?_⟩
    exact Measure.absolutelyContinuous_of_le_smul
      (restrict_le_smul_hausdorff_of_ball_growth V.weight measurableSet_ball hR hC hC₀ hgrowth)

/-- The same result with Simon's literal `ωₙ / 2ⁿ` normalization. -/
theorem Stationary.weight_absolutelyContinuous_simonHausdorff {V : Varifold N n U}
    (hV : V.Stationary) : V.weight ≪ Chapter01.simonHausdorffMeasureReal (n : ℝ) := by
  apply hV.weight_absolutelyContinuous_hausdorff.trans
  apply Measure.absolutelyContinuous_smul
  exact ENNReal.div_ne_zero.mpr
    ⟨(Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)).ne', by simp⟩

/-- The support hypothesis localizes the reference measure to the actual
carrier, without assuming a density or an integral representation. -/
theorem Stationary.weight_absolutelyContinuous_carrier {V : Varifold N n U}
    (hV : V.Stationary) {M : Set (Euclidean N)} (hM : U ∩ V.weight.support ⊆ M) :
    V.weight ≪ (Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict M := by
  have hU : ∀ᵐ x ∂V.weight, x ∈ U := by
    rw [ae_iff]
    change V.weight Uᶜ = 0
    rw [V.weight_apply V.isOpen_domain.measurableSet.compl]
    exact V.supported
  have hcarrier : ∀ᵐ x ∂V.weight, x ∈ M := by
    filter_upwards [hU, V.weight.support_mem_ae] with x hx hs
    exact hM ⟨hx, hs⟩
  have h := hV.weight_absolutelyContinuous_simonHausdorff.restrict M
  rwa [Measure.restrict_eq_self_of_ae_mem hcarrier] at h

end Varifold
end
end Poincare.SimonGMT.Chapter08
