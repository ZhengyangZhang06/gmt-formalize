module

public import Poincare.SimonGMT.Chapter04.LayerCake
public import Poincare.SimonGMT.Chapter04.LpRemarks
public import Mathlib.Analysis.Calculus.Gradient.Basic

@[expose] public section

/-!
# Simon GMT, Chapter 4, §5: weighted first variation

The tangential gradient is the orthogonal projection of the actual ambient
gradient. Multiplication by a `C¹` function on the open domain is justified
using the compact support of the test field; no regularity outside the
domain is required.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

/-- Simon's `∇ᴹh`: the gradient projected onto the approximate tangent
plane of the varifold, not an independently supplied vector field. -/
def tangentialGradient (h : E → ℝ) (x : E) : E :=
  V.tangentProjection x (gradient h x)

theorem inner_tangentialGradient (h : E → ℝ) (x v : E) :
    inner ℝ v (V.tangentialGradient h x) = fderiv ℝ h x (V.tangentProjection x v) := by
  rw [tangentialGradient, tangentProjection,
    ← Submodule.inner_starProjection_left_eq_right, inner_gradient_right]
  rfl

/-- The tangential product rule responsible for the extra gradient term
at the start of §5. -/
theorem tangentialDivergence_smul {h : E → ℝ} {X : E → E} {x : E}
    (hh : DifferentiableAt ℝ h x) (hX : DifferentiableAt ℝ X x) :
    V.tangentialDivergence (fun y ↦ h y • X y) x =
      h x * V.tangentialDivergence X x + inner ℝ (X x) (V.tangentialGradient h x) := by
  rw [inner_tangentialGradient, tangentialDivergence, fderiv_fun_smul hh hX]
  have heq :
      ((h x • fderiv ℝ X x + (fderiv ℝ h x).smulRight (X x)).toLinearMap.comp
        (V.tangentProjection x).toLinearMap) =
      h x • ((fderiv ℝ X x).toLinearMap.comp (V.tangentProjection x).toLinearMap) +
        ((fderiv ℝ h x).toLinearMap.comp (V.tangentProjection x).toLinearMap).smulRight (X x) := by
    ext y
    simp
  rw [heq, map_add, map_smul, LinearMap.trace_smulRight]
  rfl

/-- A domain-wise `C¹` multiplier times an admissible field is globally
`C¹`, since the field vanishes on a neighborhood of every point outside
its support. -/
theorem contDiff_smul_of_tsupport_subset {U : Set E} (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) {X : E → E} (hX : ContDiff ℝ 1 X)
    (hsupport : tsupport X ⊆ U) : ContDiff ℝ 1 (fun x ↦ h x • X x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hh.contDiffAt (hU.mem_nhds hx)).smul hX.contDiffAt
  · have hnot : x ∉ tsupport X := fun hx' ↦ hx (hsupport hx')
    apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with y hy
    simp only [hy, Pi.zero_apply, smul_zero]

theorem tangentialDivergence_smul_of_tsupport_subset {U : Set E} (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) {X : E → E} (hX : ContDiff ℝ 1 X)
    (hsupport : tsupport X ⊆ U) (x : E) :
    V.tangentialDivergence (fun y ↦ h y • X y) x =
      h x * V.tangentialDivergence X x + inner ℝ (X x) (V.tangentialGradient h x) := by
  by_cases hx : x ∈ U
  · exact V.tangentialDivergence_smul
      ((hh.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) (hX.differentiable (by simp) x)
  · have hnot : x ∉ tsupport X := fun hx' ↦ hx (hsupport hx')
    have hnot' : x ∉ tsupport (fun y ↦ h y • X y) := fun hx' ↦
      hnot (tsupport_smul_subset_right h X hx')
    simp only [tangentialDivergence, fderiv_of_notMem_tsupport ℝ hnot,
      fderiv_of_notMem_tsupport ℝ hnot', ContinuousLinearMap.toLinearMap_zero,
      LinearMap.zero_comp, map_zero, mul_zero, image_eq_zero_of_notMem_tsupport hnot,
      inner_zero_left, add_zero]

/-- Weighted first variation with the literal domain-wise regularity of
§5. The integrand on the left is genuinely integrable. -/
theorem HasGeneralizedMeanCurvatureIn.integral_weighted_firstVariation
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) {X : E → E} (hX : ContDiff ℝ 1 X)
    (hcompact : HasCompactSupport X) (hsupport : tsupport X ⊆ U) :
    Integrable (fun x ↦ h x * V.tangentialDivergence X x +
      inner ℝ (X x) (V.tangentialGradient h x)) V.weight ∧
    (∫ x, h x * V.tangentialDivergence X x +
      inner ℝ (X x) (V.tangentialGradient h x) ∂V.weight) =
      -∫ x, h x * inner ℝ (X x) (H x) ∂V.weight := by
  have hc := contDiff_smul_of_tsupport_subset hU hh hX hsupport
  have hcomp : HasCompactSupport (fun x ↦ h x • X x) := hcompact.smul_left
  have hs : tsupport (fun x ↦ h x • X x) ⊆ U :=
    (tsupport_smul_subset_right h X).trans hsupport
  have heq : (fun x ↦ h x * V.tangentialDivergence X x +
      inner ℝ (X x) (V.tangentialGradient h x)) =
      V.tangentialDivergence (fun x ↦ h x • X x) := by
    funext x
    exact (V.tangentialDivergence_smul_of_tsupport_subset hU hh hX hsupport x).symm
  rw [heq]
  refine ⟨V.tangentialDivergence_integrable_of_isAdmissible hc hcomp, ?_⟩
  simpa only [real_inner_smul_left] using
    HasGeneralizedMeanCurvatureIn.integral_tangentialDivergence (V := V) hH hc hcomp hs

/-- The precise weighted radial first-variation relation used to derive
(5.1), with the tangential-radial square separated into its normal defect.
The function `h` need only be `C¹` on `U`. -/
theorem HasGeneralizedMeanCurvatureIn.integral_weighted_squaredRadial_normal
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (ξ : E)
    {R : ℝ} (hR : 0 ≤ R) (hball : closedBall ξ R ⊆ U)
    {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η)
    (hcutoff : ∀ t, R ^ 2 ≤ t → η t = 0) :
    (∫ x, h x * (n * η (‖x - ξ‖ ^ 2) +
      2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2 * (1 - V.radialNormalSq ξ x)) +
      η (‖x - ξ‖ ^ 2) * inner ℝ (x - ξ) (V.tangentialGradient h x) ∂V.weight) =
        -∫ x, h x * η (‖x - ξ‖ ^ 2) * inner ℝ (x - ξ) (H x) ∂V.weight := by
  have heq := HasGeneralizedMeanCurvatureIn.integral_weighted_firstVariation
    (V := V) hH hU hh (contDiff_squaredRadialVectorField ξ hη)
    (hasCompactSupport_squaredRadialVectorField ξ hR hcutoff)
    ((tsupport_squaredRadialVectorField_subset_closedBall ξ hR hcutoff).trans hball)
  have hi : (fun x ↦ h x * V.tangentialDivergence (squaredRadialVectorField ξ η) x +
      inner ℝ (squaredRadialVectorField ξ η x) (V.tangentialGradient h x)) =ᵐ[V.weight]
      (fun x ↦ h x * (n * η (‖x - ξ‖ ^ 2) +
        2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2 * (1 - V.radialNormalSq ξ x)) +
        η (‖x - ξ‖ ^ 2) * inner ℝ (x - ξ) (V.tangentialGradient h x)) := by
    filter_upwards [V.tangent_finrank_ae_weight] with x hx
    rw [V.tangentialDivergence_squaredRadialVectorField_normal ξ x
      ((hη.differentiable (by simp) _).hasDerivAt) hx]
    simp only [squaredRadialVectorField, real_inner_smul_left]
  rw [integral_congr_ae hi] at heq
  simpa only [squaredRadialVectorField, real_inner_smul_left, mul_assoc] using heq.2

/-- The pointwise Cauchy--Schwarz estimate behind (5.3), for the actual
tangential gradient and the actual mean-curvature vector. -/
theorem weighted_radialPairing_lower_bound (ξ x : E) (h : E → ℝ) (H : E → E)
    (hh : 0 ≤ h x) :
    -‖x - ξ‖ * (‖V.tangentialGradient h x‖ + h x * ‖H x‖) ≤
      inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) := by
  have hg := (abs_le.mp (abs_real_inner_le_norm (x - ξ) (V.tangentialGradient h x))).1
  have hH := (abs_le.mp (abs_real_inner_le_norm (x - ξ) (H x))).1
  rw [inner_add_right, real_inner_smul_right]
  nlinarith [mul_le_mul_of_nonneg_left hH hh]

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
