module

public import Poincare.SimonGMT.Chapter08.RadialFirstVariation

@[expose] public section

/-!
# Differentiating radial cutoff integrals on a varifold

The compact domination is constructed inside the actual domain; there is
no ambient local-finiteness assumption at its boundary. This supplies the
differentiation-under-the-integral step in Simon (8.3.3)--(8.3.5).
-/

open Set Filter MeasureTheory Function Metric
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

section CompactDifferentiation
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]

theorem integrable_continuous_mul_of_finite_compact (μ : Measure Y)
    {K : Set Y} (hK : IsCompact K) (hfinite : μ K ≠ ∞)
    {F q : Y → ℝ} (hF : Continuous F) (hzero : ∀ x ∉ K, F x = 0)
    (hq : AEStronglyMeasurable q μ) {B : ℝ} (hqb : ∀ x ∈ K, ‖q x‖ ≤ B) :
    Integrable (fun x ↦ F x * q x) μ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  have hint : IntegrableOn (fun x ↦ F x * q x) K μ := by
    apply μ.integrableOn_of_bounded (M := max C 0 * B) hfinite (hF.aestronglyMeasurable.mul hq)
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    change ‖F x * q x‖ ≤ max C 0 * B
    rw [norm_mul]
    exact mul_le_mul ((hC x hx).trans (le_max_left C 0)) (hqb x hx)
      (norm_nonneg _) (le_max_right C 0)
  apply hint.integrable_of_forall_notMem_eq_zero
  intro x hx
  rw [hzero x hx, zero_mul]

/-- Compactness supplies a common integrable majorant for the scale
derivative; its existence is proved, not added as an analytic premise. -/
theorem hasDerivAt_integral_mul_of_finite_compact (μ : Measure Y)
    {F F' : ℝ → Y → ℝ} {a b ρ : ℝ} (hρ : ρ ∈ Ioo a b)
    {K : Set Y} (hK : IsCompact K) (hfinite : μ K ≠ ∞)
    (hF : ∀ t, Continuous (F t)) (hF' : ∀ t, Continuous (F' t))
    (hjoint : ContinuousOn (fun p : ℝ × Y ↦ F' p.1 p.2) (Icc a b ×ˢ K))
    (hzero : ∀ t ∈ Icc a b, ∀ x ∉ K, F t x = 0)
    (hzero' : ∀ t ∈ Icc a b, ∀ x ∉ K, F' t x = 0)
    (hderiv : ∀ t ∈ Icc a b, ∀ x, HasDerivAt (fun s ↦ F s x) (F' t x) t)
    {q : Y → ℝ} {B : ℝ} (hq : AEStronglyMeasurable q μ)
    (hqb : ∀ x ∈ K, ‖q x‖ ≤ B) :
    Integrable (fun x ↦ F' ρ x * q x) μ ∧
      HasDerivAt (fun t ↦ ∫ x, F t x * q x ∂μ) (∫ x, F' ρ x * q x ∂μ) ρ := by
  classical
  have hρcc : ρ ∈ Icc a b := ⟨hρ.1.le, hρ.2.le⟩
  have hFint := integrable_continuous_mul_of_finite_compact μ hK hfinite
    (hF ρ) (hzero ρ hρcc) hq hqb
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hjoint
  let bound : Y → ℝ := K.indicator (fun _ ↦ max C 0 * B)
  have hboundint : Integrable bound μ :=
    (integrableOn_const hfinite).integrable_indicator hK.measurableSet
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x ↦ F t x * q x) (F' := fun t x ↦ F' t x * q x)
    (Icc_mem_nhds hρ.1 hρ.2)
    (Eventually.of_forall fun t ↦ (hF t).aestronglyMeasurable.mul hq)
    hFint ((hF' ρ).aestronglyMeasurable.mul hq) ?_ hboundint ?_
  · filter_upwards with x
    intro t ht
    by_cases hx : x ∈ K
    · simp only [bound, indicator_of_mem hx, norm_mul]
      exact mul_le_mul ((hC (t, x) ⟨ht, hx⟩).trans (le_max_left C 0))
        (hqb x hx) (norm_nonneg _) (le_max_right C 0)
    · simp [bound, hx, hzero' t ht x hx]
  · filter_upwards with x
    intro t ht
    exact (hderiv t ht x).mul_const (q x)

end CompactDifferentiation

namespace Varifold
open Chapter04.RectifiableVarifold
variable {N n : ℕ} {U : Set (Euclidean N)}

/-- Differentiation of the actual bundle integral, locally at every
positive scale whose cutoff support lies inside the enclosing ball.
The profile is parametrized by squared radius. -/
theorem hasDerivAt_integral_radialCutoff_of_radius (V : Varifold N n U) (ξ : Euclidean N)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0)
    {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ * A < R) (hball : closedBall ξ R ⊆ U)
    {q : Euclidean N × Grassmannian N n → ℝ} {B : ℝ}
    (hq : AEStronglyMeasurable q V.measure)
    (hqb : ∀ z, z.1 ∈ closedBall ξ R → ‖q z‖ ≤ B) :
    Integrable (fun z ↦ scaledRadialCutoffDeriv ξ φ ρ z.1 * q z) V.measure ∧
      HasDerivAt (fun t ↦ ∫ z, scaledRadialCutoff ξ φ t z.1 * q z ∂V.measure)
        (∫ z, scaledRadialCutoffDeriv ξ φ ρ z.1 * q z ∂V.measure) ρ := by
  have hρR' : ρ < R / A := (lt_div_iff₀ hA).mpr hρR
  let K : Set (Euclidean N × Grassmannian N n) := closedBall ξ R ×ˢ univ
  have hscale : ∀ t ∈ Icc (ρ / 2) ((ρ + R / A) / 2), 0 < t := by
    intro t ht
    linarith [ht.1]
  have hout : ∀ t ∈ Icc (ρ / 2) ((ρ + R / A) / 2), ∀ z ∉ K,
      A ^ 2 < ‖z.1 - ξ‖ ^ 2 / t ^ 2 := by
    intro t ht z hz
    have hz' : R < ‖z.1 - ξ‖ := by
      simpa only [K, mem_prod, mem_univ, and_true, mem_closedBall, dist_eq_norm, not_le] using hz
    have htA : t * A < R := (lt_div_iff₀ hA).mp (by linarith [ht.2])
    have htz : t * A < ‖z.1 - ξ‖ := htA.trans hz'
    apply (lt_div_iff₀ (sq_pos_of_pos (hscale t ht))).mpr
    nlinarith [(sq_lt_sq₀ (mul_pos (hscale t ht) hA).le (norm_nonneg _)).mpr htz]
  apply hasDerivAt_integral_mul_of_finite_compact V.measure
    (F := fun t z ↦ scaledRadialCutoff ξ φ t z.1)
    (F' := fun t z ↦ scaledRadialCutoffDeriv ξ φ t z.1)
    (K := K) (show ρ ∈ Ioo (ρ / 2) ((ρ + R / A) / 2) by constructor <;> linarith)
    ((isCompact_closedBall ξ R).prod isCompact_univ)
    (V.finite_on_compact _ (isCompact_closedBall ξ R) hball)
    (fun t ↦ hφ.continuous.comp (by fun_prop))
    (fun t ↦ by dsimp [scaledRadialCutoffDeriv]; fun_prop)
    ?_ ?_ ?_ ?_ hq (fun z hz ↦ hqb z hz.1)
  · dsimp [scaledRadialCutoffDeriv]
    have hn : ContinuousOn (fun p : ℝ × (Euclidean N × Grassmannian N n) ↦ ‖p.2.1 - ξ‖ ^ 2)
        (Icc (ρ / 2) ((ρ + R / A) / 2) ×ˢ K) := by fun_prop
    have hne : ∀ p ∈ Icc (ρ / 2) ((ρ + R / A) / 2) ×ˢ K, p.1 ≠ 0 :=
      fun p hp ↦ (hscale p.1 hp.1).ne'
    exact ((continuousOn_const.mul hn).div (continuousOn_fst.pow 3)
      (fun p hp ↦ pow_ne_zero 3 (hne p hp))).mul
      (hφ.continuous_deriv_one.continuousOn.comp
        (hn.div (continuousOn_fst.pow 2) (fun p hp ↦ pow_ne_zero 2 (hne p hp)))
        (fun _ _ ↦ mem_univ _))
  · intro t ht z hz
    exact hcutoff _ (hout t ht z hz).le
  · intro t ht z hz
    simp [scaledRadialCutoffDeriv, deriv_eq_zero_of_cutoff hcutoff (hout t ht z hz)]
  · intro t ht z
    exact hasDerivAt_scaledRadialCutoff ξ z.1 hφ (hscale t ht).ne'

/-- The unit-cutoff specialization used in the weighted radial identity. -/
theorem hasDerivAt_integral_radialCutoff (V : Varifold N n U) (ξ : Euclidean N)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hcutoff : ∀ t, 1 ≤ t → φ t = 0)
    {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hball : closedBall ξ R ⊆ U)
    {q : Euclidean N × Grassmannian N n → ℝ} {B : ℝ}
    (hq : AEStronglyMeasurable q V.measure)
    (hqb : ∀ z, z.1 ∈ closedBall ξ R → ‖q z‖ ≤ B) :
    Integrable (fun z ↦ scaledRadialCutoffDeriv ξ φ ρ z.1 * q z) V.measure ∧
      HasDerivAt (fun t ↦ ∫ z, scaledRadialCutoff ξ φ t z.1 * q z ∂V.measure)
        (∫ z, scaledRadialCutoffDeriv ξ φ ρ z.1 * q z ∂V.measure) ρ := by
  exact V.hasDerivAt_integral_radialCutoff_of_radius ξ hφ (A := 1) (by norm_num)
    (by simpa using hcutoff) hρ (by simpa using hρR) hball hq hqb

end Varifold
end
end Poincare.SimonGMT.Chapter08
