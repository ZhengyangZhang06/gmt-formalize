module

public import Poincare.SimonGMT.Chapter04.GoodRadius

@[expose] public section

/-!
# Compact-support globalization for Simon (5.7)

The multiplier, rather than the entire radial ball, is supported in the
curvature domain. This justifies radial testing at arbitrary positive
radii without extending the varifold's curvature equation outside `U`.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

theorem contDiff_of_tsupport_subset {U : Set E} (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hs : tsupport h ⊆ U) : ContDiff ℝ 1 h := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hh.contDiffAt (hU.mem_nhds hx)
  · have hn : x ∉ tsupport h := fun hx' ↦ hx (hs hx')
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hn)

theorem tangentialGradient_eq_zero_of_notMem_tsupport {h : E → ℝ} {x : E}
    (hx : x ∉ tsupport h) : V.tangentialGradient h x = 0 := by
  rw [tangentialGradient, gradient, fderiv_of_notMem_tsupport ℝ hx, map_zero, map_zero]

theorem weightedEnergy_eq_zero_of_notMem_tsupport {h : E → ℝ} {H : E → E} {x : E}
    (hx : x ∉ tsupport h) : ‖V.tangentialGradient h x‖ + h x * ‖H x‖ = 0 := by
  rw [V.tangentialGradient_eq_zero_of_notMem_tsupport hx,
    image_eq_zero_of_notMem_tsupport hx, norm_zero, zero_mul, add_zero]

theorem HasGeneralizedMeanCurvatureIn.integrable_weightedEnergy_of_hasCompactSupport
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hc : HasCompactSupport h) (hs : tsupport h ⊆ U) :
    Integrable (fun x ↦ ‖V.tangentialGradient h x‖ + h x * ‖H x‖) V.weight := by
  have hi := HasGeneralizedMeanCurvatureIn.integrableOn_weightedEnergy (V := V) hH hU hh hc hs
  apply hi.integrable_of_forall_notMem_eq_zero
  exact fun x hx ↦ V.weightedEnergy_eq_zero_of_notMem_tsupport hx

theorem HasGeneralizedMeanCurvatureIn.integrable_radialWeightedEnergy_of_hasCompactSupport
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hc : HasCompactSupport h) (hs : tsupport h ⊆ U)
    (ξ : E) : Integrable (fun x ↦ ‖x - ξ‖ *
      (‖V.tangentialGradient h x‖ + h x * ‖H x‖)) V.weight := by
  have hi : IntegrableOn (fun x ↦ ‖x - ξ‖ *
      (‖V.tangentialGradient h x‖ + h x * ‖H x‖)) (tsupport h) V.weight :=
    IntegrableOn.continuousOn_mul (by fun_prop)
      (HasGeneralizedMeanCurvatureIn.integrableOn_weightedEnergy (V := V) hH hU hh hc hs) hc
  apply hi.integrable_of_forall_notMem_eq_zero
  intro x hx
  rw [V.weightedEnergy_eq_zero_of_notMem_tsupport hx, mul_zero]

/-- The test field may have arbitrary support: multiplication by `h`
makes it an admissible field supported inside the curvature domain. -/
theorem HasGeneralizedMeanCurvatureIn.integral_weighted_firstVariation_of_compact_multiplier
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hc : HasCompactSupport h) (hs : tsupport h ⊆ U)
    {X : E → E} (hX : ContDiff ℝ 1 X) :
    Integrable (fun x ↦ h x * V.tangentialDivergence X x +
      inner ℝ (X x) (V.tangentialGradient h x)) V.weight ∧
    (∫ x, h x * V.tangentialDivergence X x +
      inner ℝ (X x) (V.tangentialGradient h x) ∂V.weight) =
      -∫ x, h x * inner ℝ (X x) (H x) ∂V.weight := by
  have hh' := contDiff_of_tsupport_subset hU hh hs
  have hprod : ContDiff ℝ 1 (fun x ↦ h x • X x) := hh'.smul hX
  have hcomp : HasCompactSupport (fun x ↦ h x • X x) := hc.smul_right
  have hsupport : tsupport (fun x ↦ h x • X x) ⊆ U :=
    (tsupport_smul_subset_left h X).trans hs
  have heq : (fun x ↦ h x * V.tangentialDivergence X x +
      inner ℝ (X x) (V.tangentialGradient h x)) =
      V.tangentialDivergence (fun x ↦ h x • X x) := by
    funext x
    exact (V.tangentialDivergence_smul (hh'.differentiable (by simp) x)
      (hX.differentiable (by simp) x)).symm
  rw [heq]
  refine ⟨V.tangentialDivergence_integrable_of_isAdmissible hprod hcomp, ?_⟩
  simpa only [real_inner_smul_left] using
    HasGeneralizedMeanCurvatureIn.integral_tangentialDivergence (V := V) hH hprod hcomp hsupport

/-- The weighted cutoff identity at every positive radius. The proof
uses the actual first variation in `U`, not a fictitious global curvature. -/
theorem HasGeneralizedMeanCurvatureIn.weightedCutoffMass_deriv_identity_compact
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hc : HasCompactSupport h) (hs : tsupport h ⊆ U)
    (ξ : E) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun x ↦ scaledRadialCutoff ξ φ ρ x *
      inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x)) V.weight ∧
    n * V.weightedCutoffMass ξ h φ ρ - ρ * deriv (V.weightedCutoffMass ξ h φ) ρ =
      -ρ * deriv (V.weightedCutoffNormalMass ξ h φ) ρ -
        V.weightedCutoffGradientCurvaturePairing ξ h H φ ρ := by
  have hh' := contDiff_of_tsupport_subset hU hh hs
  let η : ℝ → ℝ := fun t ↦ φ (t / ρ ^ 2)
  have hη : ContDiff ℝ 1 η := hφ.comp (contDiff_id.div_const (ρ ^ 2))
  have hηderiv : ∀ t, deriv η t = deriv φ (t / ρ ^ 2) / ρ ^ 2 := by
    intro t
    have hd := ((hφ.differentiable (by simp) _).hasDerivAt).comp t
      ((hasDerivAt_id t).div_const (ρ ^ 2))
    simpa [η, Function.comp_def, div_eq_mul_inv] using hd.deriv
  have hpoint : ∀ x : E, 2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2 =
      -ρ * scaledRadialCutoffDeriv ξ φ ρ x := by
    intro x
    rw [hηderiv, scaledRadialCutoffDeriv]
    field_simp
  let X := squaredRadialVectorField ξ η
  have hX : ContDiff ℝ 1 X := contDiff_squaredRadialVectorField ξ hη
  have hfv := HasGeneralizedMeanCurvatureIn.integral_weighted_firstVariation_of_compact_multiplier
    (V := V) hH hU hh hc hs hX
  obtain ⟨hI, hJ⟩ := V.weightedCutoff_derivatives isOpen_univ hh'.contDiffOn ξ hφ hA hcutoff hρ
    (subset_univ _)
  let main := fun x ↦ n * (scaledRadialCutoff ξ φ ρ x * h x) -
    ρ * (scaledRadialCutoffDeriv ξ φ ρ x * h x) +
      ρ * (scaledRadialCutoffDeriv ξ φ ρ x * (h x * V.radialNormalSq ξ x))
  let grad := fun x ↦ scaledRadialCutoff ξ φ ρ x * inner ℝ (x - ξ) (V.tangentialGradient h x)
  let curv := fun x ↦ scaledRadialCutoff ξ φ ρ x * h x * inner ℝ (x - ξ) (H x)
  have hmain : Integrable main V.weight :=
    ((hI.1.const_mul n).sub (hI.2.1.const_mul ρ)).add (hJ.2.1.const_mul ρ)
  have hT : (fun x ↦ h x * V.tangentialDivergence X x +
      inner ℝ (X x) (V.tangentialGradient h x)) =ᵐ[V.weight] fun x ↦ main x + grad x := by
    filter_upwards [V.tangent_finrank_ae_weight] with x hx
    rw [V.tangentialDivergence_squaredRadialVectorField_normal ξ x
      ((hη.differentiable (by simp) _).hasDerivAt) hx, hpoint]
    simp only [X, squaredRadialVectorField, real_inner_smul_left, main, grad, scaledRadialCutoff, η]
    ring
  have hgrad : Integrable grad V.weight := by
    apply ((hfv.1.congr hT).sub hmain).congr
    filter_upwards with x
    change (main x + grad x) - main x = grad x
    ring
  have hcurv : Integrable curv V.weight := by
    have hi := HasGeneralizedMeanCurvatureIn.integrable_inner (V := V) hH
      (hh'.smul hX).continuous hc.smul_right ((tsupport_smul_subset_left h X).trans hs)
    apply hi.congr
    filter_upwards with x
    simp only [Pi.smul_apply', curv, X, squaredRadialVectorField, real_inner_smul_left,
      scaledRadialCutoff, η]
    ring
  have hpair : (fun x ↦ scaledRadialCutoff ξ φ ρ x *
      inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x)) = fun x ↦ grad x + curv x := by
    funext x
    simp only [grad, curv, inner_add_right, real_inner_smul_right]
    ring
  refine ⟨by rw [hpair]; exact hgrad.add hcurv, ?_⟩
  have heq := hfv.2
  rw [integral_congr_ae hT, integral_add hmain hgrad] at heq
  have hmainint : (∫ x, main x ∂V.weight) = n * V.weightedCutoffMass ξ h φ ρ -
      ρ * (∫ x, scaledRadialCutoffDeriv ξ φ ρ x * h x ∂V.weight) +
      ρ * (∫ x, scaledRadialCutoffDeriv ξ φ ρ x * (h x * V.radialNormalSq ξ x) ∂V.weight) := by
    dsimp only [main]
    have hsub : Integrable (fun x ↦ n * (scaledRadialCutoff ξ φ ρ x * h x) -
        ρ * (scaledRadialCutoffDeriv ξ φ ρ x * h x)) V.weight :=
      (hI.1.const_mul n).sub (hI.2.1.const_mul ρ)
    rw [integral_add hsub (hJ.2.1.const_mul ρ),
      integral_sub (hI.1.const_mul n) (hI.2.1.const_mul ρ)]
    simp only [integral_const_mul, weightedCutoffMass]
  have hcurvfun : (fun x ↦ h x * inner ℝ (X x) (H x)) = curv := by
    funext x
    simp only [curv, X, squaredRadialVectorField, real_inner_smul_left, scaledRadialCutoff, η]
    ring
  rw [hmainint, hcurvfun] at heq
  rw [hI.2.2.deriv, hJ.2.2.deriv, weightedCutoffGradientCurvaturePairing, hpair,
    integral_add hgrad hcurv]
  linarith

theorem HasGeneralizedMeanCurvatureIn.hasDerivAt_normalizedWeightedCutoffMass_compact
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hc : HasCompactSupport h) (hs : tsupport h ⊆ U)
    (ξ : E) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun t ↦ V.weightedCutoffMass ξ h φ t / t ^ n)
      (deriv (V.weightedCutoffNormalMass ξ h φ) ρ / ρ ^ n +
        V.weightedCutoffGradientCurvaturePairing ξ h H φ ρ / ρ ^ (n + 1)) ρ := by
  have hh' := contDiff_of_tsupport_subset hU hh hs
  have hI := (V.weightedCutoff_derivatives isOpen_univ hh'.contDiffOn ξ hφ hA hcutoff hρ
    (subset_univ _)).1.2.2
  have hrel := (HasGeneralizedMeanCurvatureIn.weightedCutoffMass_deriv_identity_compact
    (V := V) hH hU hh hc hs ξ hφ hA hcutoff hρ).2
  rw [hI.deriv] at hrel
  have hp : HasDerivAt (fun t : ℝ ↦ t ^ n) (n * ρ ^ n / ρ) ρ := by
    convert (hasDerivAt_id ρ).pow n using 1
    · rfl
    · cases n with
      | zero => simp
      | succ m => simp [pow_succ, hρ.ne', mul_div_assoc]
  convert hI.fun_div hp (pow_ne_zero n hρ.ne') using 1
  · rw [pow_succ]
    field_simp
    linear_combination hrel

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
