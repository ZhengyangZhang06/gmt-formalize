module

public import Poincare.SimonGMT.Chapter08.RadialCutoffDifferentiation

@[expose] public section

/-!
# Weighted radial first variation and the sign in Simon (8.3.5)

For `X(y)=h(y)φ(|y-ξ|²/ρ²)(y-ξ)`, the pointwise expansion is
`div_S X = nφh - ρ∂ρφh + ρ∂ρφ h |p⊥r|² + φ Dh(p_S(y-ξ))`.
Consequently the differentiated normalized mass contains **minus**
`δV(X)`. The plus sign printed in (8.3.5) is incompatible with the book's
definition `δV(X)=∫div_S X`; it disappears in the stationary case.

Source: `Simon-gmt new.pdf`, printed p. 211, PDF object 217.
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

/-- The weighted radial source test field, using a smooth squared-radius
profile so the field is smooth at the centre as well. -/
def weightedRadialVectorField (ξ : Euclidean N) (h : Euclidean N → ℝ)
    (φ : ℝ → ℝ) (ρ : ℝ) (y : Euclidean N) : Euclidean N :=
  h y • squaredRadialVectorField ξ (fun t ↦ φ (t / ρ ^ 2)) y

theorem contDiff_weightedRadialVectorField (ξ : Euclidean N)
    {h : Euclidean N → ℝ} (hh : ContDiff ℝ 1 h)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (ρ : ℝ) :
    ContDiff ℝ 1 (weightedRadialVectorField ξ h φ ρ) :=
  hh.smul (contDiff_squaredRadialVectorField ξ (hφ.comp (contDiff_id.div_const _)))

/-- The complete pointwise calculation behind (8.3.5), including the
centre, before any integration or monotonicity argument. -/
theorem tangentialDivergence_weightedRadialVectorField (ξ y : Euclidean N)
    (S : Grassmannian N n) {h : Euclidean N → ℝ} (hh : ContDiff ℝ 1 h)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    tangentialDivergence (weightedRadialVectorField ξ h φ ρ) y S =
      n * (scaledRadialCutoff ξ φ ρ y * h y) -
        ρ * (scaledRadialCutoffDeriv ξ φ ρ y * h y) +
        ρ * (scaledRadialCutoffDeriv ξ φ ρ y * (S.radialNormalSq ξ y * h y)) +
        scaledRadialCutoff ξ φ ρ y * (fderiv ℝ h y) (S.project (y - ξ)) := by
  let η : ℝ → ℝ := fun t ↦ φ (t / ρ ^ 2)
  have hη : ContDiff ℝ 1 η := hφ.comp (contDiff_id.div_const _)
  have hdη : HasDerivAt η (deriv φ (‖y - ξ‖ ^ 2 / ρ ^ 2) / ρ ^ 2) (‖y - ξ‖ ^ 2) := by
    convert ((hφ.differentiable_one _).hasDerivAt).comp (‖y - ξ‖ ^ 2)
      ((hasDerivAt_id _).div_const (ρ ^ 2)) using 1 <;> simp [η, div_eq_mul_inv, Function.comp_def]
  change tangentialDivergence (fun z ↦ h z • squaredRadialVectorField ξ η z) y S = _
  rw [tangentialDivergence_smul h _ y S hh.differentiable_one.differentiableAt
    (contDiff_squaredRadialVectorField ξ hη).differentiable_one.differentiableAt,
    tangentialDivergence_squaredRadialVectorField ξ y S hdη, S.norm_project_radial_sq]
  simp only [squaredRadialVectorField, Grassmannian.project, map_smul, smul_eq_mul,
    η, scaledRadialCutoff, scaledRadialCutoffDeriv]
  field_simp
  ring

/-- The `Ĩ` in (8.3.5), expressed on the Grassmann bundle. -/
def weightedCutoffMass (V : Varifold N n U) (ξ : Euclidean N)
    (h : Euclidean N → ℝ) (φ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  ∫ z, scaledRadialCutoff ξ φ ρ z.1 * h z.1 ∂V.measure

/-- The weighted normal-radial cutoff integral in (8.3.5). -/
def weightedCutoffNormalMass (V : Varifold N n U) (ξ : Euclidean N)
    (h : Euclidean N → ℝ) (φ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  ∫ z, scaledRadialCutoff ξ φ ρ z.1 * (z.2.radialNormalSq ξ z.1 * h z.1) ∂V.measure

theorem weightedCutoffMass_eq_weight_integral (V : Varifold N n U) (ξ : Euclidean N)
    {h : Euclidean N → ℝ} (hh : Continuous h) {φ : ℝ → ℝ} (hφ : Continuous φ) (ρ : ℝ) :
    V.weightedCutoffMass ξ h φ ρ = ∫ y, scaledRadialCutoff ξ φ ρ y * h y ∂V.weight := by
  have hm : AEStronglyMeasurable (fun y ↦ scaledRadialCutoff ξ φ ρ y * h y)
      (V.measure.map Prod.fst) :=
    (show Continuous (fun y ↦ scaledRadialCutoff ξ φ ρ y * h y) from
      (hφ.comp (by fun_prop)).mul hh).aestronglyMeasurable
  exact (integral_map measurable_fst.aemeasurable hm).symm

theorem hasDerivAt_weightedCutoffMass (V : Varifold N n U) (ξ : Euclidean N)
    {h : Euclidean N → ℝ} (hh : Continuous h) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {A : ℝ} (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ * A < R) (hball : closedBall ξ R ⊆ U) :
    Integrable (fun z ↦ scaledRadialCutoffDeriv ξ φ ρ z.1 * h z.1) V.measure ∧
    HasDerivAt (V.weightedCutoffMass ξ h φ)
      (∫ z, scaledRadialCutoffDeriv ξ φ ρ z.1 * h z.1 ∂V.measure) ρ := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall ξ R).exists_bound_of_continuousOn hh.continuousOn
  exact V.hasDerivAt_integral_radialCutoff_of_radius ξ hφ hA hcutoff hρ hρR hball
    (hh.comp continuous_fst).aestronglyMeasurable (fun z hz ↦ hB z.1 hz)

theorem hasDerivAt_weightedCutoffNormalMass (V : Varifold N n U) (ξ : Euclidean N)
    {h : Euclidean N → ℝ} (hh : Continuous h) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {A : ℝ} (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ * A < R) (hball : closedBall ξ R ⊆ U) :
    Integrable (fun z ↦ scaledRadialCutoffDeriv ξ φ ρ z.1 *
      (z.2.radialNormalSq ξ z.1 * h z.1)) V.measure ∧
    HasDerivAt (V.weightedCutoffNormalMass ξ h φ)
      (∫ z, scaledRadialCutoffDeriv ξ φ ρ z.1 *
        (z.2.radialNormalSq ξ z.1 * h z.1) ∂V.measure) ρ := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall ξ R).exists_bound_of_continuousOn hh.continuousOn
  apply V.hasDerivAt_integral_radialCutoff_of_radius ξ hφ hA hcutoff hρ hρR hball (B := B)
    ((Grassmannian.measurable_radialNormalSq ξ).aestronglyMeasurable.mul
      (hh.comp continuous_fst).aestronglyMeasurable)
  intro z hz
  change ‖z.2.radialNormalSq ξ z.1 * h z.1‖ ≤ B
  rw [norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (z.2.radialNormalSq_nonneg ξ z.1)]
  exact (mul_le_mul_of_nonneg_right (z.2.radialNormalSq_le_one ξ z.1) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hB z.1 hz)

theorem integrable_weightedCutoff (V : Varifold N n U) (ξ : Euclidean N)
    {h : Euclidean N → ℝ} (hh : Continuous h) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {A : ℝ} (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ * A < R) (hball : closedBall ξ R ⊆ U) :
    Integrable (fun z ↦ scaledRadialCutoff ξ φ ρ z.1 * h z.1) V.measure := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall ξ R).exists_bound_of_continuousOn hh.continuousOn
  apply integrable_continuous_mul_of_finite_compact V.measure
    ((isCompact_closedBall ξ R).prod isCompact_univ)
    (V.finite_on_compact _ (isCompact_closedBall ξ R) hball)
    (hφ.continuous.comp (by fun_prop)) ?_
    (hh.comp continuous_fst).aestronglyMeasurable (fun z hz ↦ hB z.1 hz.1)
  intro z hz
  have hz' : R < ‖z.1 - ξ‖ := by
    simpa only [mem_prod, mem_univ, and_true, mem_closedBall, dist_eq_norm, not_le] using hz
  apply hcutoff
  apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
  nlinarith [(sq_lt_sq₀ (mul_pos hρ hA).le (norm_nonneg _)).mpr (hρR.trans hz')]

theorem weightedRadialVectorField_support (ξ : Euclidean N)
    (h : Euclidean N → ℝ) {φ : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0)
    {ρ : ℝ} (hρ : 0 < ρ) :
    tsupport (weightedRadialVectorField ξ h φ ρ) ⊆ closedBall ξ (ρ * A) := by
  apply (closure_mono (Function.support_smul_subset_right h
    (squaredRadialVectorField ξ (fun t ↦ φ (t / ρ ^ 2))))).trans
  apply tsupport_squaredRadialVectorField_subset_closedBall ξ (mul_pos hρ hA).le
  intro t ht
  exact hcutoff _ ((le_div_iff₀ (sq_pos_of_pos hρ)).mpr (by nlinarith [ht]))

/-- The gradient correction `G` in the weighted radial identity. -/
def weightedRadialGradientTerm (ξ : Euclidean N) (h : Euclidean N → ℝ)
    (φ : ℝ → ℝ) (ρ : ℝ) (z : Euclidean N × Grassmannian N n) : ℝ :=
  scaledRadialCutoff ξ φ ρ z.1 * (fderiv ℝ h z.1) (z.2.project (z.1 - ξ))

/-- Before differentiating normalized mass, the actual first variation is
`nI - ρI′ + ρJ′ + G`. All summands are proved integrable. -/
theorem weightedRadial_firstVariation_identity (V : Varifold N n U) (ξ : Euclidean N)
    {h : Euclidean N → ℝ} (hh : ContDiff ℝ 1 h) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {A : ℝ} (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ * A < R) (hball : closedBall ξ R ⊆ U) :
    Integrable (weightedRadialGradientTerm ξ h φ ρ) V.measure ∧
    V.firstVariation (weightedRadialVectorField ξ h φ ρ) =
      n * V.weightedCutoffMass ξ h φ ρ -
        ρ * (∫ z, scaledRadialCutoffDeriv ξ φ ρ z.1 * h z.1 ∂V.measure) +
        ρ * (∫ z, scaledRadialCutoffDeriv ξ φ ρ z.1 *
          (z.2.radialNormalSq ξ z.1 * h z.1) ∂V.measure) +
        ∫ z, weightedRadialGradientTerm ξ h φ ρ z ∂V.measure := by
  let X := weightedRadialVectorField ξ h φ ρ
  have hs := weightedRadialVectorField_support ξ h hA hcutoff hρ
  have hc : HasCompactSupport X :=
    (isCompact_closedBall ξ (ρ * A)).of_isClosed_subset (isClosed_tsupport _) hs
  have hdiv := V.integrable_tangentialDivergence X
    (contDiff_weightedRadialVectorField ξ hh hφ ρ) hc
    (hs.trans ((closedBall_subset_closedBall hρR.le).trans hball))
  have hI := V.integrable_weightedCutoff ξ hh.continuous hφ hA hcutoff hρ hρR hball
  have hI' := (V.hasDerivAt_weightedCutoffMass ξ hh.continuous hφ hA hcutoff hρ hρR hball).1
  have hJ' := (V.hasDerivAt_weightedCutoffNormalMass ξ hh.continuous hφ hA hcutoff hρ hρR hball).1
  let A := fun z : Euclidean N × Grassmannian N n ↦
    n * (scaledRadialCutoff ξ φ ρ z.1 * h z.1) -
      ρ * (scaledRadialCutoffDeriv ξ φ ρ z.1 * h z.1) +
      ρ * (scaledRadialCutoffDeriv ξ φ ρ z.1 * (z.2.radialNormalSq ξ z.1 * h z.1))
  have hA : Integrable A V.measure := ((hI.const_mul n).sub' (hI'.const_mul ρ)).add (hJ'.const_mul ρ)
  have hpoint : ∀ z : Euclidean N × Grassmannian N n,
      tangentialDivergence X z.1 z.2 = A z + weightedRadialGradientTerm ξ h φ ρ z := by
    intro z
    exact tangentialDivergence_weightedRadialVectorField ξ z.1 z.2 hh hφ hρ.ne'
  have hG : Integrable (weightedRadialGradientTerm ξ h φ ρ) V.measure := by
    refine (hdiv.sub' hA).congr (Eventually.of_forall fun z ↦ ?_)
    change tangentialDivergence X z.1 z.2 - A z = _
    rw [hpoint]
    ring
  refine ⟨hG, ?_⟩
  rw [firstVariation, integral_congr_ae (Eventually.of_forall hpoint), integral_add hA hG]
  change (∫ z, (n * (scaledRadialCutoff ξ φ ρ z.1 * h z.1) -
      ρ * (scaledRadialCutoffDeriv ξ φ ρ z.1 * h z.1)) +
      ρ * (scaledRadialCutoffDeriv ξ φ ρ z.1 * (z.2.radialNormalSq ξ z.1 * h z.1))
      ∂V.measure) + _ = _
  rw [integral_add ((hI.const_mul n).sub' (hI'.const_mul ρ)) (hJ'.const_mul ρ),
    integral_sub (hI.const_mul n) (hI'.const_mul ρ)]
  simp only [integral_const_mul, weightedCutoffMass]

/-- The convention-consistent version of Simon (8.3.5), with the
necessary minus sign before `δV(X)`. The derivatives and every integral
are obtained from compact domination and actual varifold first variation. -/
theorem hasDerivAt_normalized_weightedCutoffMass (V : Varifold N n U) (ξ : Euclidean N)
    {h : Euclidean N → ℝ} (hh : ContDiff ℝ 1 h) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {A : ℝ} (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ * A < R) (hball : closedBall ξ R ⊆ U) :
    HasDerivAt (fun t ↦ V.weightedCutoffMass ξ h φ t / t ^ n)
      (deriv (V.weightedCutoffNormalMass ξ h φ) ρ / ρ ^ n +
        ((∫ z, weightedRadialGradientTerm ξ h φ ρ z ∂V.measure) -
          V.firstVariation (weightedRadialVectorField ξ h φ ρ)) / ρ ^ (n + 1)) ρ := by
  have hI := (V.hasDerivAt_weightedCutoffMass ξ hh.continuous hφ hA hcutoff hρ hρR hball).2
  have hJ := (V.hasDerivAt_weightedCutoffNormalMass ξ hh.continuous hφ hA hcutoff hρ hρR hball).2
  have hid := (V.weightedRadial_firstVariation_identity ξ hh hφ hA hcutoff hρ hρR hball).2
  have hd := hI.fun_div ((hasDerivAt_id ρ).pow n) (pow_ne_zero n hρ.ne')
  convert hd using 1
  · rfl
  · rw [hJ.deriv, hid]
    simp only [id_eq, mul_one, Pi.pow_apply]
    have hp : (n : ℝ) * ρ ^ (n - 1) * ρ = n * ρ ^ n := by
      cases n with
      | zero => simp
      | succ m => simp [pow_succ, mul_assoc]
    field_simp
    simp only [pow_succ]
    linear_combination (ρ ^ n * V.weightedCutoffMass ξ h φ ρ) * hp

end
end Poincare.SimonGMT.Chapter08.Varifold
