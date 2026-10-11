module

public import Poincare.SimonGMT.Chapter08.WeightedRadialIdentity

@[expose] public section

/-!
# Stationary cutoff identities on the Grassmann bundle

These are the cutoff and dominated-limit steps for Simon (8.3.3)--(8.3.4)
with zero first variation. Every measure is the actual general varifold
measure; no rectifiability or finiteness at the domain boundary is used.
-/

open Set Filter MeasureTheory Function Metric
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08.Varifold
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
open Chapter04.RectifiableVarifold
variable {N n : ℕ} {U : Set (Euclidean N)}

/-- Vanishing first variation for test fields supported in the specified
region. This allows local stationarity in the source's enclosing ball. -/
def StationaryOn (V : Varifold N n U) (W : Set (Euclidean N)) : Prop :=
  ∀ X : TestVectorField (N := N) U, tsupport X.toFun ⊆ W → V.firstVariation X = 0

theorem Stationary.stationaryOn {V : Varifold N n U} (hV : V.Stationary)
    (W : Set (Euclidean N)) : V.StationaryOn W := fun X _ ↦ hV X

def cutoffMass (V : Varifold N n U) (ξ : Euclidean N) (φ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  V.weightedCutoffMass ξ (fun _ ↦ 1) φ ρ

/-- Stationarity, with admissibility of the radial test field proved
from its cutoff, gives the normalized cutoff derivative. -/
theorem StationaryOn.hasDerivAt_normalizedCutoffMass {V : Varifold N n U}
    {ξ : Euclidean N} {R : ℝ} (hV : V.StationaryOn (ball ξ R))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {A : ℝ} (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ * A < R) (hball : closedBall ξ R ⊆ U) :
    HasDerivAt (fun t ↦ V.cutoffMass ξ φ t / t ^ n)
      ((∫ z, scaledRadialCutoffDeriv ξ φ ρ z.1 * z.2.radialNormalSq ξ z.1 ∂V.measure) /
        ρ ^ n) ρ := by
  have hs := weightedRadialVectorField_support ξ (fun _ ↦ 1) hA hcutoff hρ
  have hzero : V.firstVariation (weightedRadialVectorField ξ (fun _ ↦ 1) φ ρ) = 0 :=
    hV ⟨_, contDiff_weightedRadialVectorField ξ contDiff_const hφ ρ,
      ((isCompact_closedBall ξ (ρ * A)).of_isClosed_subset (isClosed_tsupport _) hs)
      , hs.trans ((closedBall_subset_closedBall hρR.le).trans hball)⟩
      (hs.trans (closedBall_subset_ball hρR))
  have hJ := (V.hasDerivAt_weightedCutoffNormalMass ξ (h := fun _ ↦ 1) continuous_const hφ hA hcutoff
    hρ hρR hball).2
  have hd := V.hasDerivAt_normalized_weightedCutoffMass ξ (h := fun _ ↦ 1) contDiff_const hφ hA hcutoff
    hρ hρR hball
  simpa only [cutoffMass, hzero, hJ.deriv, weightedRadialGradientTerm, fderiv_const_apply,
    zero_apply, mul_zero, integral_zero, sub_self, zero_div, add_zero,
    mul_one] using hd

/-- Outward cutoffs converge to the closed-ball integral. Domination
takes place in an arbitrary larger compact ball contained in the domain. -/
theorem tendsto_integral_radialCutoff (V : Varifold N n U) (ξ : Euclidean N)
    {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hball : closedBall ξ R ⊆ U)
    {q : Euclidean N × Grassmannian N n → ℝ} {B : ℝ}
    (hq : AEStronglyMeasurable q V.measure)
    (hqb : ∀ z, z.1 ∈ closedBall ξ R → ‖q z‖ ≤ B) :
    Tendsto (fun ε ↦ ∫ z, scaledRadialCutoff ξ (monotonicityCutoff ε) ρ z.1 * q z ∂V.measure)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z in closedBall ξ ρ ×ˢ (univ : Set (Grassmannian N n)), q z ∂V.measure)) := by
  classical
  let K : Set (Euclidean N × Grassmannian N n) := closedBall ξ R ×ˢ univ
  let bound := K.indicator (fun _ ↦ B)
  have hbound : Integrable bound V.measure :=
    (integrableOn_const (V.finite_on_compact _ (isCompact_closedBall ξ R) hball)).integrable_indicator
      (measurableSet_closedBall.prod MeasurableSet.univ)
  have hscale : Tendsto (fun ε : ℝ ↦ ρ * (1 + ε)) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    have hsum : Tendsto (fun ε : ℝ ↦ 1 + ε) (𝓝[>] (0 : ℝ)) (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hid
    simpa using hsum.const_mul ρ
  rw [← integral_indicator (measurableSet_closedBall.prod MeasurableSet.univ)]
  refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbound ?_
  · exact Eventually.of_forall fun ε ↦
      (((contDiff_monotonicityCutoff ε).continuous.comp
        (show Continuous (fun z : Euclidean N × Grassmannian N n ↦ ‖z.1 - ξ‖ ^ 2 / ρ ^ 2)
          by fun_prop)).aestronglyMeasurable.mul hq)
  · filter_upwards [self_mem_nhdsWithin, hscale.eventually (gt_mem_nhds hρR)] with ε hε hεR
    filter_upwards with z
    by_cases hz : z ∈ K
    · rw [show bound z = B by simp [bound, hz], norm_mul]
      have hc := monotonicityCutoff_mem_Icc ε (‖z.1 - ξ‖ ^ 2 / ρ ^ 2)
      have hnorm : ‖scaledRadialCutoff ξ (monotonicityCutoff ε) ρ z.1‖ ≤ 1 := by
        rw [scaledRadialCutoff, Real.norm_eq_abs, abs_of_nonneg hc.1]
        exact hc.2
      exact (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans
        (by simpa only [one_mul] using hqb z hz.1)
    · have hr : R < ‖z.1 - ξ‖ := by
        simpa only [K, mem_prod, mem_univ, and_true, mem_closedBall, dist_eq_norm, not_le] using hz
      have ha : (1 + ε) ^ 2 ≤ ‖z.1 - ξ‖ ^ 2 / ρ ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
        have hs := (sq_lt_sq₀ (mul_pos hρ (by linarith [show 0 < ε from hε] : 0 < 1 + ε)).le
          (norm_nonneg _)).mpr (hεR.trans hr)
        nlinarith [hs]
      simp [bound, hz, scaledRadialCutoff, monotonicityCutoff_cutoff hε _ ha]
  · filter_upwards with z
    convert (tendsto_scaledRadialCutoff ξ z.1 hρ).mul_const (q z) using 1
    by_cases hz : z.1 ∈ closedBall ξ ρ <;> simp [hz]

theorem tendsto_cutoffMass (V : Varifold N n U) (ξ : Euclidean N)
    {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hball : closedBall ξ R ⊆ U) :
    Tendsto (fun ε ↦ V.cutoffMass ξ (monotonicityCutoff ε) ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 (V.weight.real (closedBall ξ ρ))) := by
  simpa only [cutoffMass, weightedCutoffMass, mul_one, setIntegral_const, smul_eq_mul,
    measureReal_def, ← V.weight_apply measurableSet_closedBall] using
      V.tendsto_integral_radialCutoff ξ hρ hρR hball
        (q := fun _ ↦ 1) (B := 1) aestronglyMeasurable_const (fun _ _ ↦ by simp)

/-- The bounded tilt weight used to justify integration on annuli. -/
def truncatedRadialDefect (ξ : Euclidean N) (c : ℝ)
    (z : Euclidean N × Grassmannian N n) : ℝ :=
  z.2.radialNormalSq ξ z.1 / (max c ‖z.1 - ξ‖) ^ n

theorem measurable_truncatedRadialDefect (ξ : Euclidean N) (c : ℝ) :
    Measurable (truncatedRadialDefect (n := n) ξ c) :=
  (Grassmannian.measurable_radialNormalSq ξ).div (by fun_prop)

theorem norm_truncatedRadialDefect_le (ξ : Euclidean N) {c : ℝ} (hc : 0 < c)
    (z : Euclidean N × Grassmannian N n) :
    ‖truncatedRadialDefect ξ c z‖ ≤ (c ^ n)⁻¹ := by
  have hm : 0 < max c ‖z.1 - ξ‖ := hc.trans_le (le_max_left _ _)
  rw [truncatedRadialDefect, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (z.2.radialNormalSq_nonneg ξ z.1) (pow_pos hm n).le), ← one_div]
  apply (div_le_div_iff₀ (pow_pos hm n) (pow_pos hc n)).mpr
  calc
    z.2.radialNormalSq ξ z.1 * c ^ n ≤ 1 * c ^ n :=
      mul_le_mul_of_nonneg_right (z.2.radialNormalSq_le_one ξ z.1) (pow_pos hc n).le
    _ ≤ 1 * max c ‖z.1 - ξ‖ ^ n := by gcongr; exact le_max_left _ _

/-- The pointwise tilt squeeze on the support of the scale derivative. -/
theorem scaledRadialCutoffDeriv_defect_bounds (ξ : Euclidean N)
    (z : Euclidean N × Grassmannian N n) {ε c ρ : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hcρ : c ≤ ρ) :
    scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) ρ z.1 * truncatedRadialDefect ξ c z ≤
        (scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) ρ z.1 * z.2.radialNormalSq ξ z.1) / ρ ^ n ∧
      (scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) ρ z.1 * z.2.radialNormalSq ξ z.1) / ρ ^ n ≤
        (1 + ε) ^ n *
          (scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) ρ z.1 * truncatedRadialDefect ξ c z) := by
  by_cases hz : scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) ρ z.1 = 0
  · simp [hz]
  have hρ : 0 < ρ := hc.trans_le hcρ
  obtain ⟨hrlo, hrhi⟩ := scaledRadialCutoffDeriv_support ξ z.1 hε hρ hz
  have hr : 0 < ‖z.1 - ξ‖ := hρ.trans_le hrlo
  have hpowlo := pow_le_pow_left₀ hρ.le hrlo n
  have hpowhi := pow_le_pow_left₀ (norm_nonneg (z.1 - ξ)) hrhi n
  rw [mul_pow] at hpowhi
  have hzpos : 0 ≤ scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) ρ z.1 *
      z.2.radialNormalSq ξ z.1 :=
    mul_nonneg (scaledRadialCutoffDeriv_nonneg ξ z.1 (monotonicityCutoff_antitone hε) hρ)
      (z.2.radialNormalSq_nonneg ξ z.1)
  rw [truncatedRadialDefect, max_eq_right (hcρ.trans hrlo), ← mul_div_assoc, ← mul_div_assoc]
  constructor
  · exact (div_le_div_iff₀ (pow_pos hr n) (pow_pos hρ n)).mpr
      (mul_le_mul_of_nonneg_left hpowlo hzpos)
  · apply (div_le_div_iff₀ (pow_pos hρ n) (pow_pos hr n)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hpowhi hzpos]

private theorem radial_sub_le_sub_of_hasDerivAt_le {a b : ℝ} (hab : a ≤ b)
    {f g f' g' : ℝ → ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hle : ∀ t ∈ Icc a b, f' t ≤ g' t) : f b - f a ≤ g b - g a := by
  have hm : MonotoneOn (fun t ↦ g t - f t) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun t ht ↦ ((hg t ht).sub (hf t ht)).continuousAt.continuousWithinAt)
    · intro t ht
      exact ((hg t (interior_subset ht)).sub
        (hf t (interior_subset ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [((hg t (interior_subset ht)).sub (hf t (interior_subset ht))).deriv]
      exact sub_nonneg.mpr (hle t (interior_subset ht))
  have h := hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  linarith

/-- Integrating the actual stationary derivative squeezes the cutoff
mass difference between the two cutoff tilt differences. -/
theorem StationaryOn.cutoff_squeeze {V : Varifold N n U}
    {ξ : Euclidean N} {R : ℝ} (hV : V.StationaryOn (ball ξ R))
    {ε σ ρ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hσρ : σ ≤ ρ)
    (hρR : ρ * (1 + ε) < R) (hball : closedBall ξ R ⊆ U) :
    let G := fun t ↦ ∫ z, scaledRadialCutoff ξ (monotonicityCutoff ε) t z.1 *
      truncatedRadialDefect ξ σ z ∂V.measure
    G ρ - G σ ≤ V.cutoffMass ξ (monotonicityCutoff ε) ρ / ρ ^ n -
      V.cutoffMass ξ (monotonicityCutoff ε) σ / σ ^ n ∧
    V.cutoffMass ξ (monotonicityCutoff ε) ρ / ρ ^ n -
      V.cutoffMass ξ (monotonicityCutoff ε) σ / σ ^ n ≤ (1 + ε) ^ n * (G ρ - G σ) := by
  let q := truncatedRadialDefect (n := n) ξ σ
  let G := fun t ↦ ∫ z, scaledRadialCutoff ξ (monotonicityCutoff ε) t z.1 * q z ∂V.measure
  let G' := fun t ↦ ∫ z, scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) t z.1 * q z ∂V.measure
  let F := fun t ↦ V.cutoffMass ξ (monotonicityCutoff ε) t / t ^ n
  let F' := fun t ↦ (∫ z, scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) t z.1 *
    z.2.radialNormalSq ξ z.1 ∂V.measure) / t ^ n
  have hA : 0 < 1 + ε := by linarith
  have hscale : ∀ t ∈ Icc σ ρ, t * (1 + ε) < R :=
    fun t ht ↦ (mul_le_mul_of_nonneg_right ht.2 hA.le).trans_lt hρR
  have hG : ∀ t ∈ Icc σ ρ, HasDerivAt G (G' t) t := by
    intro t ht
    exact (V.hasDerivAt_integral_radialCutoff_of_radius ξ (contDiff_monotonicityCutoff ε)
      hA (monotonicityCutoff_cutoff hε) (hσ.trans_le ht.1) (hscale t ht) hball
      (measurable_truncatedRadialDefect ξ σ).aestronglyMeasurable
      (fun z _ ↦ norm_truncatedRadialDefect_le ξ hσ z)).2
  have hF : ∀ t ∈ Icc σ ρ, HasDerivAt F (F' t) t := by
    intro t ht
    exact hV.hasDerivAt_normalizedCutoffMass (contDiff_monotonicityCutoff ε)
      hA (monotonicityCutoff_cutoff hε) (hσ.trans_le ht.1) (hscale t ht) hball
  have hbounds : ∀ t ∈ Icc σ ρ, G' t ≤ F' t ∧ F' t ≤ (1 + ε) ^ n * G' t := by
    intro t ht
    have hgint := (V.hasDerivAt_integral_radialCutoff_of_radius ξ
      (contDiff_monotonicityCutoff ε) hA (monotonicityCutoff_cutoff hε)
      (hσ.trans_le ht.1) (hscale t ht) hball
      (measurable_truncatedRadialDefect ξ σ).aestronglyMeasurable
      (fun z _ ↦ norm_truncatedRadialDefect_le ξ hσ z)).1
    have hfint := (V.hasDerivAt_integral_radialCutoff_of_radius ξ
      (contDiff_monotonicityCutoff ε) hA (monotonicityCutoff_cutoff hε)
      (hσ.trans_le ht.1) (hscale t ht) hball
      (Grassmannian.measurable_radialNormalSq ξ).aestronglyMeasurable (B := 1) (fun z _ ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (z.2.radialNormalSq_nonneg ξ z.1)]
        exact z.2.radialNormalSq_le_one ξ z.1)).1
    constructor
    · simpa only [G', F', q, integral_div] using
        integral_mono hgint (hfint.div_const (t ^ n))
          (fun z ↦ (scaledRadialCutoffDeriv_defect_bounds ξ z hε hσ ht.1).1)
    · simpa only [G', F', q, integral_div, integral_const_mul] using
        integral_mono (hfint.div_const (t ^ n)) (hgint.const_mul ((1 + ε) ^ n))
          (fun z ↦ (scaledRadialCutoffDeriv_defect_bounds ξ z hε hσ ht.1).2)
  constructor
  · exact radial_sub_le_sub_of_hasDerivAt_le hσρ hG hF (fun t ht ↦ (hbounds t ht).1)
  · have h := radial_sub_le_sub_of_hasDerivAt_le hσρ hF
      (fun t ht ↦ (hG t ht).const_mul ((1 + ε) ^ n)) (fun t ht ↦ (hbounds t ht).2)
    simpa only [mul_sub] using h

end
end Poincare.SimonGMT.Chapter08.Varifold
