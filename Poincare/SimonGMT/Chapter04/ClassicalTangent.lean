module

public import Poincare.SimonGMT.Chapter04.LpLowerDensity
public import Poincare.SimonGMT.Chapter04.WeightedBlowUp
import all Poincare.SimonGMT.Chapter03.Rectifiable

@[expose] public section

/-!
# Simon GMT, Chapter 4, Lemma 6.3

The tangent in the distance expression is the affine plane through the
base point: its distance from `y` is `infDist (y-x) P` for the linear
approximate tangent `P`. No compact support of the varifold is assumed.
-/

open Filter Function Metric Set MeasureTheory
open scoped CompactlySupported ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

theorem norm_normalProjection_eq_infDist (P : Submodule ℝ E) (y : E) :
    ‖Pᗮ.starProjection y‖ = infDist y (P : Set E) := by
  simpa only [Submodule.orthogonal_orthogonal] using Pᗮ.norm_starProjection_eq_infDist y

theorem infDist_submodule_smul (P : Submodule ℝ E) (c : ℝ) (y : E) :
    infDist (c • y) (P : Set E) = |c| * infDist y (P : Set E) := by
  rw [← norm_normalProjection_eq_infDist, map_smul, norm_smul, Real.norm_eq_abs,
    norm_normalProjection_eq_infDist]

/-- A compact continuous distance test, equal to plane distance on the
unit ball and zero on the plane. -/
def planeDistanceCutoff (P : Submodule ℝ E) : C_c(E, ℝ) where
  toFun y := tangentDensityCutoff 1 (by norm_num) y * infDist y (P : Set E)
  continuous_toFun := (tangentDensityCutoff 1 (by norm_num)).continuous.mul
    (continuous_infDist_pt _)
  hasCompactSupport' := (tangentDensityCutoff 1 (by norm_num)).hasCompactSupport.mul_right

theorem planeDistanceCutoff_nonneg (P : Submodule ℝ E) (y : E) :
    0 ≤ planeDistanceCutoff P y :=
  mul_nonneg (tangentDensityCutoff_mem_Icc (by norm_num : (0 : ℝ) < 1) y).1 infDist_nonneg

theorem planeDistanceCutoff_eq_infDist (P : Submodule ℝ E) {y : E}
    (hy : y ∈ closedBall (0 : E) 1) :
    planeDistanceCutoff P y = infDist y (P : Set E) := by
  change tangentDensityCutoff 1 (by norm_num) y * _ = _
  rw [tangentDensityCutoff_eq_one (by norm_num) hy, one_mul]

theorem planeDistanceCutoff_eq_zero (P : Submodule ℝ E) {y : E} (hy : y ∈ P) :
    planeDistanceCutoff P y = 0 := by
  change tangentDensityCutoff 1 (by norm_num) y * _ = _
  rw [infDist_zero_of_mem hy, mul_zero]

namespace RectifiableVarifold

variable {V : RectifiableVarifold (E := E) n}

/-- The epsilon form of Simon 4.6.3, initially using a half-radius ball
so that every detecting ball stays inside the unit blow-up cutoff. -/
theorem HasGeneralizedMeanCurvatureIn.eventually_support_flatness_half
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    (hU : IsOpen U) (hn : 0 < n) {p : ℝ} (hpn : (n : ℝ) < p)
    (hLp : ∀ K : Set E, IsCompact K → K ⊆ U → MemLp H (ENNReal.ofReal p) (V.weight.restrict K))
    (hθ : ∀ᵐ z ∂V.weight.restrict U, 1 ≤ V.multiplicity z)
    {x : E} (hx : x ∈ U) {P : Submodule ℝ E}
    (hP : Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.multiplicity x P)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ y ∈ V.weight.support ∩ closedBall x (r / 2),
      infDist (y - x) (P : Set E) ≤ ε * r := by
  obtain ⟨R, hR, _, hlower⟩ := hH.exists_uniform_lower_ball_mass_lp hU hn hpn hLp hθ hx
  let ω := (Chapter01.realUnitBallVolume (n : ℝ)).toReal
  have hω : 0 < ω := ENNReal.toReal_pos
    (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)).ne'
    (Chapter01.realUnitBallVolume_ne_top _)
  let α := min (ε / 2) (1 / 4)
  have hα : 0 < α := lt_min (half_pos hε) (by norm_num)
  have hαε : α ≤ ε / 2 := min_le_left _ _
  have hαq : α ≤ 1 / 4 := min_le_right _ _
  let c := ε / 2 * (ω / 2) * α ^ n
  have hc : 0 < c := mul_pos (mul_pos (half_pos hε) (half_pos hω)) (pow_pos hα n)
  let f := planeDistanceCutoff P
  have hplane : ∫ z in (P : Set E), f z ∂Measure.euclideanHausdorffMeasure n = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun _ hz ↦ planeDistanceCutoff_eq_zero P hz)
  have hlim : Tendsto (fun r : ℝ ↦ r⁻¹ ^ n * ∫ z, f (Chapter03.blowUpMap x r z) ∂V.weight)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [hplane, mul_zero] using V.tendsto_rescaled_weight_of_weighted_approximateTangent hP f
  filter_upwards [hlim.eventually (gt_mem_nhds hc), Ioc_mem_nhdsGT hR] with r hsmall hr
  intro y hy
  by_contra hnot
  have hoff : ε * r < infDist (y - x) (P : Set E) := lt_of_not_ge hnot
  have hyr : dist y x ≤ r / 2 := hy.2
  have hαr : 0 < α * r := mul_pos hα hr.1
  have hαrR : α * r ≤ R := by nlinarith [hr.1, hr.2]
  have hymem : y ∈ V.weight.support ∩ closedBall x R :=
    ⟨hy.1, show dist y x ≤ R by linarith [hr.1, hr.2]⟩
  have hmass := hlower y hymem (α * r) hαr hαrR
  let b := blowUpHomeomorph x hr.1
  have hfi : Integrable (fun z ↦ f (Chapter03.blowUpMap x r z)) V.weight :=
    (f.continuous.comp b.continuous).integrable_of_hasCompactSupport
      (f.hasCompactSupport.comp_homeomorph b)
  have hpoint : ∀ z ∈ closedBall y (α * r), ε / 2 ≤ f (Chapter03.blowUpMap x r z) := by
    intro z hz
    have hzy : dist z y ≤ α * r := hz
    have hzx : dist z x ≤ r := by
      have ht := dist_triangle z y x
      nlinarith [hr.1]
    have hB : Chapter03.blowUpMap x r z ∈ closedBall (0 : E) 1 := by
      simp only [mem_closedBall, dist_eq_norm, Chapter03.blowUpMap, sub_zero,
        norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr.1)]
      have hz' : ‖z - x‖ ≤ r := by simpa only [dist_eq_norm] using hzx
      rw [← div_eq_inv_mul, div_le_one hr.1]
      exact hz'
    rw [planeDistanceCutoff_eq_infDist P hB]
    have hd : infDist (y - x) (P : Set E) ≤ infDist (z - x) (P : Set E) + dist z y := by
      simpa only [dist_sub_right, dist_comm y z] using
        (infDist_le_infDist_add_dist (x := y - x) (y := z - x) (s := (P : Set E)))
    have hdist : (ε / 2) * r ≤ infDist (z - x) (P : Set E) := by
      nlinarith [mul_le_mul_of_nonneg_right hαε hr.1.le]
    rw [Chapter03.blowUpMap, infDist_submodule_smul, abs_of_pos (inv_pos.mpr hr.1),
      ← div_eq_inv_mul, le_div_iff₀ hr.1]
    exact hdist
  have hint : (ε / 2) * V.weight.real (closedBall y (α * r)) ≤
      ∫ z, f (Chapter03.blowUpMap x r z) ∂V.weight := by
    calc
      _ = ∫ _ in closedBall y (α * r), ε / 2 ∂V.weight := by
        simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, measureReal_def]
        ring
      _ ≤ ∫ z in closedBall y (α * r), f (Chapter03.blowUpMap x r z) ∂V.weight :=
        setIntegral_mono_on (integrableOn_const (isCompact_closedBall y (α * r)).measure_lt_top.ne)
          hfi.integrableOn measurableSet_closedBall hpoint
      _ ≤ _ := setIntegral_le_integral hfi
        (Eventually.of_forall fun z ↦ planeDistanceCutoff_nonneg P _)
  have hmul := mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left hmass (half_pos hε).le).trans hint)
    (pow_pos (inv_pos.mpr hr.1) n).le
  have hcancel : r⁻¹ ^ n * (ε / 2 * (ω / 2 * (α * r) ^ n)) = c := by
    dsimp only [c]
    rw [mul_pow, inv_pow]
    field_simp [hr.1.ne']
  change r⁻¹ ^ n * (ε / 2 * (ω / 2 * (α * r) ^ n)) ≤ _ at hmul
  rw [hcancel] at hmul
  exact (not_lt_of_ge hmul) hsmall

/-- Every sufficiently small support ball lies in an arbitrarily thin
relative tube around the affine approximate tangent. -/
theorem HasGeneralizedMeanCurvatureIn.eventually_support_flatness
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    (hU : IsOpen U) (hn : 0 < n) {p : ℝ} (hpn : (n : ℝ) < p)
    (hLp : ∀ K : Set E, IsCompact K → K ⊆ U → MemLp H (ENNReal.ofReal p) (V.weight.restrict K))
    (hθ : ∀ᵐ z ∂V.weight.restrict U, 1 ≤ V.multiplicity z)
    {x : E} (hx : x ∈ U) {P : Submodule ℝ E}
    (hP : Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.multiplicity x P)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ y ∈ V.weight.support ∩ closedBall x r,
      infDist (y - x) (P : Set E) ≤ ε * r := by
  have hdouble : Tendsto (fun r : ℝ ↦ 2 * r) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero, id_eq] using
        ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0)).const_mul 2)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos (by norm_num) hr
  have ht := hdouble.eventually
    (hH.eventually_support_flatness_half hU hn hpn hLp hθ hx hP (half_pos hε))
  filter_upwards [ht] with r hr
  have hrad : 2 * r / 2 = r := by ring
  have hfactor : ε / 2 * (2 * r) = ε * r := by ring
  simpa only [hrad, hfactor] using hr

/-- The normalized maximal distance of the support ball to an affine
plane through `x`. Empty support balls have excess zero. -/
def supportPlaneExcess (V : RectifiableVarifold (E := E) n) (x : E)
    (P : Submodule ℝ E) (r : ℝ) : ℝ :=
  sSup ((fun y ↦ r⁻¹ * infDist (y - x) (P : Set E)) ''
    (V.weight.support ∩ closedBall x r))

theorem supportPlaneExcess_le_of_forall {x : E} {P : Submodule ℝ E}
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    (hflat : ∀ y ∈ V.weight.support ∩ closedBall x r,
      infDist (y - x) (P : Set E) ≤ a * r) :
    V.supportPlaneExcess x P r ≤ a := by
  unfold supportPlaneExcess
  apply Real.sSup_le _ ha
  rintro _ ⟨y, hy, rfl⟩
  dsimp only []
  rw [← div_eq_inv_mul, div_le_iff₀ hr]
  exact hflat y hy

theorem supportPlaneExcess_nonneg {x : E} {P : Submodule ℝ E}
    {r : ℝ} (hr : 0 < r) : 0 ≤ V.supportPlaneExcess x P r := by
  unfold supportPlaneExcess
  apply Real.sSup_nonneg
  rintro _ ⟨y, _, rfl⟩
  exact mul_nonneg (inv_pos.mpr hr).le infDist_nonneg

/-- Simon 4.6.3, literally as convergence of the supremum of normalized
distances from support points to the affine approximate tangent plane. -/
theorem HasGeneralizedMeanCurvatureIn.classical_tangent
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    (hU : IsOpen U) (hn : 0 < n) {p : ℝ} (hpn : (n : ℝ) < p)
    (hLp : ∀ K : Set E, IsCompact K → K ⊆ U → MemLp H (ENNReal.ofReal p) (V.weight.restrict K))
    (hθ : ∀ᵐ z ∂V.weight.restrict U, 1 ≤ V.multiplicity z)
    {x : E} (hx : x ∈ U) {P : Submodule ℝ E}
    (hP : Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.multiplicity x P) :
    Tendsto (fun r : ℝ ↦ sSup ((fun y ↦ r⁻¹ * infDist (y - x) (P : Set E)) ''
      (V.weight.support ∩ closedBall x r))) (𝓝[>] 0) (𝓝 0) := by
  change Tendsto (V.supportPlaneExcess x P) _ _
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact ha.trans_le (supportPlaneExcess_nonneg (V := V) hr)
  · intro a ha
    filter_upwards [self_mem_nhdsWithin,
      hH.eventually_support_flatness hU hn hpn hLp hθ hx hP (half_pos ha)] with r hr hflat
    exact (supportPlaneExcess_le_of_forall hr (half_pos ha).le hflat).trans_lt (half_lt_self ha)

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
