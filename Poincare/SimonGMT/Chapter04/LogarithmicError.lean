module

public import Poincare.SimonGMT.Chapter04.MeanCurvature
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-!
# Simon GMT, Chapter 4, formula (3.18)

The logarithmic mean-curvature error is obtained directly from radial first
variation. Neither the simultaneous `F,G` identity (3.17) nor a
density/multiplicity identification is an assumption. Balls are closed.
-/

open Filter Function Metric Set
open scoped ENNReal MeasureTheory Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

/-- The scale-invariant `L¹` curvature quantity in Simon (4.3.18), written
using natural powers. At positive radii it is `ρ^(1-n) ∫ |H|`. -/
def normalizedMeanCurvatureMass (ξ : E) (H : E → E) (ρ : ℝ) : ℝ :=
  ρ * (∫ x in closedBall ξ ρ, ‖H x‖ ∂V.weight) / ρ ^ n

theorem normalizedMeanCurvatureMass_eq (ξ : E) (H : E → E) {ρ : ℝ} (hρ : 0 < ρ) :
    V.normalizedMeanCurvatureMass ξ H ρ =
      ρ ^ (1 - (n : ℝ)) * ∫ x in closedBall ξ ρ, ‖H x‖ ∂V.weight := by
  rw [Real.rpow_sub hρ, Real.rpow_one, Real.rpow_natCast]
  simp only [normalizedMeanCurvatureMass]
  ring

/-- The radial pairing is bounded by the `L¹` curvature in the support
ball. No pointwise bound on the mean-curvature field is used. -/
theorem HasGeneralizedMeanCurvatureIn.abs_cutoffMeanCurvaturePairing_le_integral_norm
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {φ : ℝ → ℝ} (hφrange : ∀ t, φ t ∈ Icc 0 1)
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    |V.cutoffMeanCurvaturePairing ξ H φ ρ| ≤
      ρ * A * ∫ x in closedBall ξ (ρ * A), ‖H x‖ ∂V.weight := by
  have hint := (hH.1.integrableOn_compact_subset hball
    (isCompact_closedBall ξ (ρ * A))).norm
  have hbint := MeasureTheory.IntegrableOn.integrable_indicator
    (hint.const_mul (ρ * A)) measurableSet_closedBall
  have hbound : ∀ x : E,
      ‖scaledRadialCutoff ξ φ ρ x * inner ℝ (x - ξ) (H x)‖ ≤
        (closedBall ξ (ρ * A)).indicator (fun x ↦ ρ * A * ‖H x‖) x := by
    intro x
    by_cases hx : x ∈ closedBall ξ (ρ * A)
    · have hφx : 0 ≤ scaledRadialCutoff ξ φ ρ x := (hφrange _).1
      rw [indicator_of_mem hx, norm_mul, Real.norm_eq_abs, abs_of_nonneg hφx]
      have hr : ‖x - ξ‖ ≤ ρ * A := by
        simpa only [mem_closedBall, dist_eq_norm] using hx
      calc
        scaledRadialCutoff ξ φ ρ x * ‖inner ℝ (x - ξ) (H x)‖ ≤
            1 * ‖inner ℝ (x - ξ) (H x)‖ :=
          mul_le_mul_of_nonneg_right (hφrange _).2 (norm_nonneg _)
        _ ≤ ρ * A * ‖H x‖ := by
          simpa only [one_mul] using (norm_inner_le_norm (x - ξ) (H x)).trans
            (mul_le_mul_of_nonneg_right hr (norm_nonneg _))
    · rw [scaledRadialCutoff_eq_zero_of_notMem_closedBall ξ hA hcutoff hρ hx,
        zero_mul, norm_zero, indicator_of_notMem hx]
  have h := MeasureTheory.norm_integral_le_of_norm_le hbint (Eventually.of_forall hbound)
  simpa only [Real.norm_eq_abs, cutoffMeanCurvaturePairing,
    MeasureTheory.integral_indicator measurableSet_closedBall,
    MeasureTheory.integral_const_mul] using h

theorem HasGeneralizedMeanCurvatureIn.abs_cutoffMeanCurvatureError_le_normalizedMass
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {φ : ℝ → ℝ} (hφrange : ∀ t, φ t ∈ Icc 0 1)
    {A ρ δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0)
    (hball : closedBall ξ (ρ * A) ⊆ U)
    (hbound : V.normalizedMeanCurvatureMass ξ H (ρ * A) ≤ δ) :
    |V.cutoffMeanCurvatureError ξ H φ ρ| ≤ δ * A ^ n / ρ := by
  rw [cutoffMeanCurvatureError, abs_div, abs_of_pos (pow_pos hρ (n + 1))]
  calc
    |V.cutoffMeanCurvaturePairing ξ H φ ρ| / ρ ^ (n + 1) ≤
        (ρ * A * ∫ x in closedBall ξ (ρ * A), ‖H x‖ ∂V.weight) / ρ ^ (n + 1) :=
      div_le_div_of_nonneg_right
        (HasGeneralizedMeanCurvatureIn.abs_cutoffMeanCurvaturePairing_le_integral_norm
          (V := V) hH ξ hφrange hA hρ hcutoff hball) (pow_pos hρ _).le
    _ = V.normalizedMeanCurvatureMass ξ H (ρ * A) * (A ^ n / ρ) := by
      dsimp [normalizedMeanCurvatureMass]
      rw [mul_pow, pow_succ]
      field_simp
    _ ≤ δ * (A ^ n / ρ) :=
      mul_le_mul_of_nonneg_right hbound (div_nonneg (pow_pos hA _).le hρ.le)
    _ = δ * A ^ n / ρ := by ring

private theorem sub_le_sub_of_hasDerivAt_le {a b : ℝ} (hab : a ≤ b)
    {f g f' g' : ℝ → ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hle : ∀ t ∈ Icc a b, f' t ≤ g' t) : f b - f a ≤ g b - g a := by
  have hmono : MonotoneOn (fun t ↦ g t - f t) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun t ht ↦ ((hg t ht).sub (hf t ht)).continuousAt.continuousWithinAt)
    · intro t ht
      exact ((hg t (interior_subset ht)).sub (hf t (interior_subset ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [((hg t (interior_subset ht)).sub (hf t (interior_subset ht))).deriv]
      exact sub_nonneg.mpr (hle t (interior_subset ht))
  have h := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  linarith

/-- The cutoff form of (4.3.18). The logarithm comes from integrating the
scale-invariant `L¹` curvature bound; the tilt prefactors are the corrected
ones for the outward cutoff, as in `FirstVariation.lean`. -/
theorem HasGeneralizedMeanCurvatureIn.cutoff_logarithmic_squeeze
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {ε σ ρ δ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hσρ : σ ≤ ρ)
    (hball : closedBall ξ (ρ * (1 + ε)) ⊆ U)
    (hbound : ∀ t ∈ Icc σ (ρ * (1 + ε)),
      V.normalizedMeanCurvatureMass ξ H t ≤ δ) :
    let G := fun t ↦ ∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) t x *
      V.truncatedRadialDefect ξ σ x ∂V.weight
    let D := V.cutoffMass ξ (monotonicityCutoff ε) ρ / ρ ^ n -
      V.cutoffMass ξ (monotonicityCutoff ε) σ / σ ^ n
    G ρ - G σ - δ * (1 + ε) ^ n * (Real.log ρ - Real.log σ) ≤ D ∧
      D ≤ (1 + ε) ^ n * (G ρ - G σ) +
        δ * (1 + ε) ^ n * (Real.log ρ - Real.log σ) := by
  let q := V.truncatedRadialDefect ξ σ
  let G := fun t ↦ ∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) t x * q x ∂V.weight
  let G' := fun t ↦ ∫ x, scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) t x * q x ∂V.weight
  let F := fun t ↦ V.cutoffMass ξ (monotonicityCutoff ε) t / t ^ n
  let N := fun t ↦ (∫ x, scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) t x *
    V.radialNormalSq ξ x ∂V.weight) / t ^ n
  let K := fun t ↦ V.cutoffMeanCurvatureError ξ H (monotonicityCutoff ε) t
  let C := δ * (1 + ε) ^ n
  have hA : 0 < 1 + ε := by linarith
  have hG : ∀ t ∈ Icc σ ρ, HasDerivAt G (G' t) t := by
    intro t ht
    exact (V.hasDerivAt_integral_scaledRadialCutoff_mul ξ (contDiff_monotonicityCutoff ε)
      hA (monotonicityCutoff_cutoff hε) (hσ.trans_le ht.1)
      (V.truncatedRadialDefect_aemeasurable ξ σ).aestronglyMeasurable
      (V.norm_truncatedRadialDefect_le ξ hσ)).2
  have hF : ∀ t ∈ Icc σ ρ, HasDerivAt F (N t + K t) t := by
    intro t ht
    exact HasGeneralizedMeanCurvatureIn.hasDerivAt_normalizedCutoffMass
      (V := V) hH ξ (contDiff_monotonicityCutoff ε) hA
      (monotonicityCutoff_cutoff hε) (hσ.trans_le ht.1)
      ((closedBall_subset_closedBall (mul_le_mul_of_nonneg_right ht.2 hA.le)).trans hball)
  have hlog : ∀ t ∈ Icc σ ρ, HasDerivAt (fun t ↦ C * Real.log t) (C / t) t := by
    intro t ht
    simpa only [div_eq_mul_inv] using
      (Real.hasDerivAt_log (hσ.trans_le ht.1).ne').const_mul C
  have hK : ∀ t ∈ Icc σ ρ, |K t| ≤ C / t := by
    intro t ht
    apply HasGeneralizedMeanCurvatureIn.abs_cutoffMeanCurvatureError_le_normalizedMass
      (V := V) hH ξ (monotonicityCutoff_mem_Icc ε) hA (hσ.trans_le ht.1)
      (monotonicityCutoff_cutoff hε)
      ((closedBall_subset_closedBall (mul_le_mul_of_nonneg_right ht.2 hA.le)).trans hball)
    apply hbound
    constructor
    · calc
        σ ≤ t := ht.1
        _ ≤ t * (1 + ε) := by nlinarith [mul_pos (hσ.trans_le ht.1) hε]
    · exact mul_le_mul_of_nonneg_right ht.2 hA.le
  have hN : ∀ t ∈ Icc σ ρ, G' t ≤ N t ∧ N t ≤ (1 + ε) ^ n * G' t := by
    intro t ht
    have hgint := (V.hasDerivAt_integral_scaledRadialCutoff_mul ξ
      (contDiff_monotonicityCutoff ε) hA (monotonicityCutoff_cutoff hε) (hσ.trans_le ht.1)
      (V.truncatedRadialDefect_aemeasurable ξ σ).aestronglyMeasurable
      (V.norm_truncatedRadialDefect_le ξ hσ)).1
    have hnint := (V.hasDerivAt_integral_scaledRadialCutoff_mul ξ
      (contDiff_monotonicityCutoff ε) hA (monotonicityCutoff_cutoff hε) (hσ.trans_le ht.1)
      (V.radialNormalSq_aemeasurable ξ).aestronglyMeasurable (fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (V.radialNormalSq_nonneg ξ x)]
        exact V.radialNormalSq_le_one ξ x)).1
    constructor
    · simpa only [G', N, q, MeasureTheory.integral_div] using
        MeasureTheory.integral_mono hgint (hnint.div_const (t ^ n))
          (fun x ↦ (V.scaledRadialCutoffDeriv_defect_bounds ξ x hε hσ ht.1).1)
    · simpa only [G', N, q, MeasureTheory.integral_div, MeasureTheory.integral_const_mul] using
        MeasureTheory.integral_mono (hnint.div_const (t ^ n)) (hgint.const_mul ((1 + ε) ^ n))
          (fun x ↦ (V.scaledRadialCutoffDeriv_defect_bounds ξ x hε hσ ht.1).2)
  constructor
  · have h := sub_le_sub_of_hasDerivAt_le hσρ hG
      (fun t ht ↦ (hF t ht).add (hlog t ht)) (fun t ht ↦ by
        have h₁ := (hN t ht).1
        have h₂ := (abs_le.mp (hK t ht)).1
        linarith)
    dsimp [F, G, q, C] at h ⊢
    linarith
  · have h := sub_le_sub_of_hasDerivAt_le hσρ hF
      (fun t ht ↦ ((hG t ht).const_mul ((1 + ε) ^ n)).add (hlog t ht))
      (fun t ht ↦ by
        have h₁ := (hN t ht).2
        have h₂ := (abs_le.mp (hK t ht)).2
        linarith)
    dsimp [F, G, q, C] at h ⊢
    nlinarith

/-- The outward cutoff difference converges to the integral over the
closed-ball annulus, including the outer sphere and excluding the inner one. -/
theorem tendsto_cutoffDefect_difference (ξ : E) {σ ρ : ℝ}
    (hσ : 0 < σ) (hσρ : σ ≤ ρ) :
    Tendsto (fun ε ↦
      (∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) ρ x *
        V.truncatedRadialDefect ξ σ x ∂V.weight) -
      ∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) σ x *
        V.truncatedRadialDefect ξ σ x ∂V.weight)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x in closedBall ξ ρ \ closedBall ξ σ,
        V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight)) := by
  have hρ := hσ.trans_le hσρ
  have hlim := (V.tendsto_integral_scaledRadialCutoff_mul ξ hρ
    (V.truncatedRadialDefect_aemeasurable ξ σ).aestronglyMeasurable
    (V.norm_truncatedRadialDefect_le ξ hσ)).sub
      (V.tendsto_integral_scaledRadialCutoff_mul ξ hσ
        (V.truncatedRadialDefect_aemeasurable ξ σ).aestronglyMeasurable
        (V.norm_truncatedRadialDefect_le ξ hσ))
  rw [← MeasureTheory.setIntegral_sdiff measurableSet_closedBall
    (V.integrableOn_truncatedRadialDefect ξ hσ ρ) (closedBall_subset_closedBall hσρ)] at hlim
  convert hlim using 2
  apply MeasureTheory.setIntegral_congr_fun (measurableSet_closedBall.diff measurableSet_closedBall)
  intro x hx
  have hr : σ < ‖x - ξ‖ := by
    simpa only [mem_closedBall, dist_eq_norm, not_le] using hx.2
  simp only [truncatedRadialDefect, max_eq_right hr.le]

/-- Interior-radius version of Simon (4.3.18). The larger-radius hypothesis
is removed in `logarithmic_monotonicity_error` below by continuity from above. -/
theorem HasGeneralizedMeanCurvatureIn.logarithmic_monotonicity_error_of_lt
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {R σ ρ δ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hρR : ρ < R)
    (hball : closedBall ξ R ⊆ U)
    (hbound : ∀ t ∈ Icc σ R, V.normalizedMeanCurvatureMass ξ H t ≤ δ) :
    |(V.weight.real (closedBall ξ ρ) / ρ ^ n -
        V.weight.real (closedBall ξ σ) / σ ^ n) -
      ∫ x in closedBall ξ ρ \ closedBall ξ σ,
        V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight| ≤ δ * Real.log (ρ / σ) := by
  have hρ := hσ.trans_le hσρ
  let G := fun ε t ↦ ∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) t x *
    V.truncatedRadialDefect ξ σ x ∂V.weight
  let D := fun ε ↦ V.cutoffMass ξ (monotonicityCutoff ε) ρ / ρ ^ n -
    V.cutoffMass ξ (monotonicityCutoff ε) σ / σ ^ n
  have hGlim := V.tendsto_cutoffDefect_difference ξ hσ hσρ
  have hDlim := ((V.tendsto_cutoffMass ξ hρ).div_const (ρ ^ n)).sub
    ((V.tendsto_cutoffMass ξ hσ).div_const (σ ^ n))
  have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hsum : Tendsto (fun ε : ℝ ↦ 1 + ε) (𝓝[>] (0 : ℝ)) (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add hid
  have hAlim : Tendsto (fun ε : ℝ ↦ (1 + ε) ^ n) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [add_zero, one_pow] using hsum.pow n
  have hscale : Tendsto (fun ε : ℝ ↦ ρ * (1 + ε)) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    simpa only [add_zero, mul_one] using hsum.const_mul ρ
  have hClim := (hAlim.const_mul δ).mul_const (Real.log ρ - Real.log σ)
  have hsqueeze : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      G ε ρ - G ε σ - δ * (1 + ε) ^ n * (Real.log ρ - Real.log σ) ≤ D ε ∧
      D ε ≤ (1 + ε) ^ n * (G ε ρ - G ε σ) +
        δ * (1 + ε) ^ n * (Real.log ρ - Real.log σ) := by
    filter_upwards [self_mem_nhdsWithin, hscale.eventually (gt_mem_nhds hρR)] with ε hε hεR
    exact HasGeneralizedMeanCurvatureIn.cutoff_logarithmic_squeeze
      (V := V) hH ξ hε hσ hσρ ((closedBall_subset_closedBall hεR.le).trans hball)
      (fun t ht ↦ hbound t ⟨ht.1, ht.2.trans hεR.le⟩)
  have hlo := le_of_tendsto_of_tendsto (hGlim.sub hClim) hDlim
    (hsqueeze.mono fun _ h ↦ h.1)
  have hhi := le_of_tendsto_of_tendsto hDlim ((hAlim.mul hGlim).add hClim)
    (hsqueeze.mono fun _ h ↦ h.2)
  simp only [one_mul, mul_one] at hlo hhi
  rw [Real.log_div hρ.ne' hσ.ne', abs_le]
  constructor <;> linarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- A closed ball contained in an open domain can be enlarged slightly.
This is the support margin needed by the outward cutoffs at an endpoint. -/
theorem exists_larger_closedBall_subset {U : Set E} (hU : IsOpen U) (ξ : E)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hball : closedBall ξ ρ ⊆ U) :
    ∃ R : ℝ, ρ < R ∧ closedBall ξ R ⊆ U := by
  obtain ⟨r, hr, hsub⟩ := (isCompact_closedBall ξ ρ).exists_cthickening_subset_open hU hball
  refine ⟨r + ρ, by linarith, ?_⟩
  rwa [cthickening_closedBall hr.le hρ] at hsub

/-- The closed-ball curvature bound extends a little beyond its endpoint
after any strict relaxation of its constant. This uses only local `L¹`
integrability, not bounded curvature or zero mass on spheres. -/
theorem HasGeneralizedMeanCurvatureIn.exists_larger_radius_curvature_bound
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    (hU : IsOpen U) (ξ : E) {σ ρ δ δ' : ℝ}
    (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hδ : δ < δ')
    (hball : closedBall ξ ρ ⊆ U)
    (hbound : ∀ t ∈ Icc σ ρ, V.normalizedMeanCurvatureMass ξ H t ≤ δ) :
    ∃ R : ℝ, ρ < R ∧ closedBall ξ R ⊆ U ∧
      ∀ t ∈ Icc σ R, V.normalizedMeanCurvatureMass ξ H t ≤ δ' := by
  have hρ := hσ.trans_le hσρ
  obtain ⟨R₀, hρR₀, hR₀ball⟩ := exists_larger_closedBall_subset hU ξ hρ.le hball
  let r : ℕ → ℝ := fun k ↦ ρ + (R₀ - ρ) / ((k : ℝ) + 1)
  have hrpos : ∀ k, ρ < r k := fun k ↦ lt_add_of_pos_right _
    (div_pos (sub_pos.mpr hρR₀) (by positivity))
  have hrzero : r 0 = R₀ := by simp [r]
  have hranti : Antitone r := by
    intro i j hij
    dsimp [r]
    apply add_le_add_right
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hρR₀.le) (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hrle : ∀ k, r k ≤ R₀ := fun k ↦ by
    simpa only [hrzero] using hranti (Nat.zero_le k)
  have hrlim : Tendsto r atTop (𝓝 ρ) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (R₀ - ρ)).const_add ρ
    simpa only [mul_zero, add_zero, mul_one_div] using h
  have hinter : (⋂ k, closedBall ξ (r k)) = closedBall ξ ρ := by
    ext x
    simp only [mem_iInter, mem_closedBall]
    constructor
    · intro hx
      exact ge_of_tendsto hrlim (Eventually.of_forall hx)
    · exact fun hx k ↦ hx.trans (hrpos k).le
  have hHint : MeasureTheory.IntegrableOn (fun x ↦ ‖H x‖) (closedBall ξ R₀) V.weight :=
    (hH.1.integrableOn_compact_subset hR₀ball (isCompact_closedBall ξ R₀)).norm
  have hmass := MeasureTheory.tendsto_setIntegral_of_antitone
    (μ := V.weight) (f := fun x ↦ ‖H x‖)
    (fun k ↦ measurableSet_closedBall)
    (fun i j hij ↦ closedBall_subset_closedBall (hranti hij))
    (show ∃ k, MeasureTheory.IntegrableOn (fun x ↦ ‖H x‖) (closedBall ξ (r k)) V.weight from
      ⟨0, by simpa only [hrzero] using hHint⟩)
  rw [hinter] at hmass
  have hlim := (hrlim.mul hmass).div_const (ρ ^ n)
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds
    ((hbound ρ ⟨hσρ, le_rfl⟩).trans_lt hδ))).exists
  refine ⟨r k, hrpos k, (closedBall_subset_closedBall (hrle k)).trans hR₀ball, ?_⟩
  intro t ht
  by_cases htρ : t ≤ ρ
  · exact (hbound t ⟨ht.1, htρ⟩).trans hδ.le
  have hρt : ρ ≤ t := (lt_of_not_ge htρ).le
  have hMle : (∫ x in closedBall ξ t, ‖H x‖ ∂V.weight) ≤
      ∫ x in closedBall ξ (r k), ‖H x‖ ∂V.weight := by
    apply MeasureTheory.setIntegral_mono_set
      (hHint.mono_set (closedBall_subset_closedBall (hrle k)))
    · exact Eventually.of_forall (fun x ↦ norm_nonneg (H x))
    · exact Eventually.of_forall (closedBall_subset_closedBall ht.2)
  have hMnonneg : 0 ≤ ∫ x in closedBall ξ t, ‖H x‖ ∂V.weight :=
    MeasureTheory.integral_nonneg (fun x ↦ norm_nonneg (H x))
  apply le_trans ?_ hk.le
  dsimp [normalizedMeanCurvatureMass]
  calc
    t * (∫ x in closedBall ξ t, ‖H x‖ ∂V.weight) / t ^ n ≤
        t * (∫ x in closedBall ξ t, ‖H x‖ ∂V.weight) / ρ ^ n :=
      div_le_div_of_nonneg_left (mul_nonneg (hρ.trans_le hρt).le hMnonneg)
        (pow_pos hρ n) (pow_le_pow_left₀ hρ.le hρt n)
    _ ≤ r k * (∫ x in closedBall ξ (r k), ‖H x‖ ∂V.weight) / ρ ^ n :=
      div_le_div_of_nonneg_right
        (mul_le_mul ht.2 hMle hMnonneg (hρ.trans (hrpos k)).le) (pow_pos hρ n).le

/-- Simon (4.3.18), printed page 93: the exact closed-ball logarithmic
error estimate under only the stated scale-invariant local `L¹` bound.
No curvature hypothesis outside `[σ,ρ]` is added. -/
theorem HasGeneralizedMeanCurvatureIn.logarithmic_monotonicity_error
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    (hU : IsOpen U) (ξ : E) {σ ρ δ : ℝ}
    (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hball : closedBall ξ ρ ⊆ U)
    (hbound : ∀ t ∈ Icc σ ρ,
      t ^ (1 - (n : ℝ)) * (∫ x in closedBall ξ t, ‖H x‖ ∂V.weight) ≤ δ) :
    |(V.weight.real (closedBall ξ ρ) / ρ ^ n -
        V.weight.real (closedBall ξ σ) / σ ^ n) -
      ∫ x in closedBall ξ ρ \ closedBall ξ σ,
        V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight| ≤ δ * Real.log (ρ / σ) := by
  have hbound' : ∀ t ∈ Icc σ ρ, V.normalizedMeanCurvatureMass ξ H t ≤ δ := by
    intro t ht
    rw [V.normalizedMeanCurvatureMass_eq ξ H (hσ.trans_le ht.1)]
    exact hbound t ht
  have hid : Tendsto (fun η : ℝ ↦ η) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hlim : Tendsto (fun η : ℝ ↦ (δ + η) * Real.log (ρ / σ))
      (𝓝[>] (0 : ℝ)) (𝓝 (δ * Real.log (ρ / σ))) := by
    simpa only [add_zero] using (hid.const_add δ).mul_const (Real.log (ρ / σ))
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hηpos : 0 < η := hη
  obtain ⟨R, hρR, hRball, hRbound⟩ :=
    HasGeneralizedMeanCurvatureIn.exists_larger_radius_curvature_bound
      (V := V) hH hU ξ hσ hσρ (show δ < δ + η by linarith) hball hbound'
  exact HasGeneralizedMeanCurvatureIn.logarithmic_monotonicity_error_of_lt
    (V := V) hH ξ hσ hσρ hρR hRball hRbound

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
