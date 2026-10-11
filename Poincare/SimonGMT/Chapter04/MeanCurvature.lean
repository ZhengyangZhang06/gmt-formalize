module

public import Poincare.SimonGMT.Chapter04.Density
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

@[expose] public section

/-!
# Simon GMT, Chapter 4, §3: the mean-curvature error term

The cutoff identities are derived from the actual first variation and its
generalized mean-curvature representation. They do not assume stationarity,
an error identity, or a density/multiplicity identification.

## Source sign correction

With Simon's convention (3.14), `δV(X) = -∫ X·H`, radial first variation gives
`n I - ρ I' = -ρ J' - K`, where `K = ∫ φ (x-ξ)·H`. Consequently
`(I/ρⁿ)' = J'/ρⁿ + K/ρⁿ⁺¹`. The minus sign in printed (3.16), repeated in
(4.1), is incompatible with the stated definition of `E₀`. We prove the plus
sign and retain the source's absolute error estimate. An integrating factor
for an equation with this convention is `exp (-∫ E)`, not `exp (∫ E)`;
the symmetric bounds on that factor are unchanged.
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

theorem HasGeneralizedMeanCurvatureIn.integral_tangentialDivergence
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    {X : E → E} (hX : ContDiff ℝ 1 X) (hcompact : HasCompactSupport X)
    (hsupport : tsupport X ⊆ U) :
    ∫ x, V.tangentialDivergence X x ∂V.weight =
      -∫ x, inner ℝ (X x) (H x) ∂V.weight := by
  simpa only [firstVariation, meanCurvaturePairing] using
    hH.2 X ⟨hX, hcompact, hsupport⟩

/-- The radial divergence identity with generalized mean curvature, before
separating its normal-radial term. -/
theorem HasGeneralizedMeanCurvatureIn.integral_squaredRadial_tangential
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {R : ℝ} (hR : 0 ≤ R) (hball : closedBall ξ R ⊆ U)
    {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η)
    (hcutoff : ∀ t, R ^ 2 ≤ t → η t = 0) :
    ∫ x, (n * η (‖x - ξ‖ ^ 2) +
      2 * deriv η (‖x - ξ‖ ^ 2) * ‖V.tangentProjection x (x - ξ)‖ ^ 2) ∂V.weight =
      -∫ x, η (‖x - ξ‖ ^ 2) * inner ℝ (x - ξ) (H x) ∂V.weight := by
  have heq := HasGeneralizedMeanCurvatureIn.integral_tangentialDivergence (V := V) hH
    (contDiff_squaredRadialVectorField ξ hη)
    (hasCompactSupport_squaredRadialVectorField ξ hR hcutoff)
    ((tsupport_squaredRadialVectorField_subset_closedBall ξ hR hcutoff).trans hball)
  have hae : (fun x ↦ V.tangentialDivergence (squaredRadialVectorField ξ η) x) =ᵐ[V.weight]
      (fun x ↦ n * η (‖x - ξ‖ ^ 2) +
        2 * deriv η (‖x - ξ‖ ^ 2) * ‖V.tangentProjection x (x - ξ)‖ ^ 2) := by
    filter_upwards [V.tangent_finrank_ae_weight] with x hx
    exact V.tangentialDivergence_squaredRadialVectorField ξ x
      ((hη.differentiable (by simp) _).hasDerivAt) hx
  rw [MeasureTheory.integral_congr_ae hae] at heq
  simpa only [squaredRadialVectorField, real_inner_smul_left] using heq

theorem HasGeneralizedMeanCurvatureIn.integral_squaredRadial_normal
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {R : ℝ} (hR : 0 ≤ R) (hball : closedBall ξ R ⊆ U)
    {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η)
    (hcutoff : ∀ t, R ^ 2 ≤ t → η t = 0) :
    n * (∫ x, η (‖x - ξ‖ ^ 2) ∂V.weight) +
      (∫ x, 2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2 ∂V.weight) =
      (∫ x, 2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2 *
        V.radialNormalSq ξ x ∂V.weight) -
      ∫ x, η (‖x - ξ‖ ^ 2) * inner ℝ (x - ξ) (H x) ∂V.weight := by
  have hsq : Continuous (fun x : E ↦ ‖x - ξ‖ ^ 2) := by fun_prop
  have hηint : MeasureTheory.Integrable (fun x ↦ η (‖x - ξ‖ ^ 2)) V.weight :=
    (hη.continuous.comp hsq).integrable_of_hasCompactSupport
      (hasCompactSupport_squaredRadialScalar ξ hR hcutoff)
  have hdint : MeasureTheory.Integrable
      (fun x ↦ 2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2) V.weight :=
    (((hη.continuous_deriv_one.comp hsq).const_mul 2).mul hsq).integrable_of_hasCompactSupport
      (hasCompactSupport_squaredRadialScalar_deriv ξ hR hcutoff).mul_left.mul_right
  have hnint := hdint.mul_bdd (V.radialNormalSq_aemeasurable ξ).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ (by
      rw [Real.norm_eq_abs, abs_of_nonneg (V.radialNormalSq_nonneg ξ x)]
      exact V.radialNormalSq_le_one ξ x : ‖V.radialNormalSq ξ x‖ ≤ 1))
  have heq := HasGeneralizedMeanCurvatureIn.integral_squaredRadial_tangential
    (V := V) hH ξ hR hball hη hcutoff
  have hpoint : (fun x ↦ n * η (‖x - ξ‖ ^ 2) +
      2 * deriv η (‖x - ξ‖ ^ 2) * ‖V.tangentProjection x (x - ξ)‖ ^ 2) =
      (fun x ↦ (n * η (‖x - ξ‖ ^ 2) +
        2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2) -
          2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2 * V.radialNormalSq ξ x) := by
    funext x
    rw [V.norm_tangentProjection_radial_sq]
    ring
  have hsumint : MeasureTheory.Integrable
      (fun x ↦ n * η (‖x - ξ‖ ^ 2) +
        2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2) V.weight :=
    (hηint.const_mul (n : ℝ)).add hdint
  rw [hpoint, MeasureTheory.integral_sub hsumint hnint,
    MeasureTheory.integral_add (hηint.const_mul n) hdint,
    MeasureTheory.integral_const_mul] at heq
  linarith

/-- The unnormalized radial pairing `K(ρ) = ∫ φ(r/ρ) (x-ξ)·H`. The profile
here is parametrized by squared radius, exactly as in `cutoffMass`. -/
def cutoffMeanCurvaturePairing (ξ : E) (H : E → E) (φ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  ∫ x, scaledRadialCutoff ξ φ ρ x * inner ℝ (x - ξ) (H x) ∂V.weight

/-- Simon's stated `E₀`, whose sign in the differentiated identity must be
positive under the convention (3.14). -/
def cutoffMeanCurvatureError (ξ : E) (H : E → E) (φ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  V.cutoffMeanCurvaturePairing ξ H φ ρ / ρ ^ (n + 1)

/-- The mean-curvature pairing against every continuous compactly supported
field in the domain is a genuine integrable function. No measurability or
integrability of `H` outside that domain is assumed. -/
theorem HasGeneralizedMeanCurvatureIn.integrable_inner
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    {X : E → E} (hX : Continuous X) (hcompact : HasCompactSupport X)
    (hsupport : tsupport X ⊆ U) :
    MeasureTheory.Integrable (fun x ↦ inner ℝ (X x) (H x)) V.weight := by
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuous hX
  have hHint := hH.1.integrableOn_compact_subset hsupport hcompact
  have hpair : MeasureTheory.IntegrableOn (fun x ↦ inner ℝ (X x) (H x))
      (tsupport X) V.weight := by
    apply (hHint.norm.const_mul C).mono'
    · exact (hX.aemeasurable.inner hHint.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    · filter_upwards with x
      exact (norm_inner_le_norm (X x) (H x)).trans
        (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  apply hpair.integrable_of_forall_notMem_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport hx, inner_zero_left]

theorem integrable_scaledRadialCutoff (ξ : E) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {A : ℝ} (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0)
    {ρ : ℝ} (hρ : 0 < ρ) :
    MeasureTheory.Integrable (scaledRadialCutoff ξ φ ρ) V.weight := by
  let η : ℝ → ℝ := fun t ↦ φ (t / ρ ^ 2)
  have hηcutoff : ∀ t, (ρ * A) ^ 2 ≤ t → η t = 0 := by
    intro t ht
    apply hcutoff
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
    nlinarith [ht]
  change MeasureTheory.Integrable (fun x : E ↦ η (‖x - ξ‖ ^ 2)) V.weight
  have hηcont : Continuous η := hφ.continuous.comp (continuous_id.div_const (ρ ^ 2))
  have hsq : Continuous (fun x : E ↦ ‖x - ξ‖ ^ 2) := by fun_prop
  exact (hηcont.comp hsq).integrable_of_hasCompactSupport
    (hasCompactSupport_squaredRadialScalar ξ (η := η) (mul_pos hρ hA).le hηcutoff)

theorem HasGeneralizedMeanCurvatureIn.integrable_cutoffMeanCurvaturePairing
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    MeasureTheory.Integrable
      (fun x ↦ scaledRadialCutoff ξ φ ρ x * inner ℝ (x - ξ) (H x)) V.weight := by
  let η : ℝ → ℝ := fun t ↦ φ (t / ρ ^ 2)
  have hη : ContDiff ℝ 1 η := hφ.comp (contDiff_id.div_const (ρ ^ 2))
  have hηcutoff : ∀ t, (ρ * A) ^ 2 ≤ t → η t = 0 := by
    intro t ht
    apply hcutoff
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
    nlinarith [ht]
  simpa only [squaredRadialVectorField, real_inner_smul_left, η, scaledRadialCutoff] using
    HasGeneralizedMeanCurvatureIn.integrable_inner (V := V) hH
      (contDiff_squaredRadialVectorField ξ hη).continuous
      (hasCompactSupport_squaredRadialVectorField ξ (mul_pos hρ hA).le hηcutoff)
      ((tsupport_squaredRadialVectorField_subset_closedBall ξ (mul_pos hρ hA).le hηcutoff).trans hball)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem scaledRadialCutoff_eq_zero_of_notMem_closedBall
    (ξ : E) {φ : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ)
    {x : E} (hx : x ∉ closedBall ξ (ρ * A)) : scaledRadialCutoff ξ φ ρ x = 0 := by
  apply hcutoff
  have hr : ρ * A < ‖x - ξ‖ := by
    simpa only [mem_closedBall, dist_eq_norm, not_le] using hx
  apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
  nlinarith [sq_nonneg (‖x - ξ‖ + ρ * A),
    mul_pos (sub_pos.mpr hr)
      (add_pos_of_nonneg_of_pos (norm_nonneg (x - ξ)) (mul_pos hρ hA))]

/-- The source's carrier-wise bound `|H| ≤ Λ` gives the exact cutoff error
estimate. The field is not required to satisfy that bound off the carrier. -/
theorem abs_cutoffMeanCurvaturePairing_le
    {U : Set E} {H : E → E} {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφnonneg : ∀ t, 0 ≤ φ t)
    {A : ℝ} (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall ξ (ρ * A) ⊆ U) :
    |V.cutoffMeanCurvaturePairing ξ H φ ρ| ≤ ρ * A * Λ * V.cutoffMass ξ φ ρ := by
  have hφint := V.integrable_scaledRadialCutoff ξ hφ hA hcutoff hρ
  have hcarrier : ∀ᵐ x ∂V.weight, x ∈ V.carrier :=
    V.ae_weight_of_ae_restrict (MeasureTheory.ae_restrict_mem V.measurable_carrier)
  have hb : ∀ᵐ x ∂V.weight,
      ‖scaledRadialCutoff ξ φ ρ x * inner ℝ (x - ξ) (H x)‖ ≤
        (ρ * A * Λ) * scaledRadialCutoff ξ φ ρ x := by
    filter_upwards [hcarrier] with x hxM
    by_cases hx : x ∈ closedBall ξ (ρ * A)
    · have hr : ‖x - ξ‖ ≤ ρ * A := by
        simpa only [mem_closedBall, dist_eq_norm] using hx
      have hHx := hbound x ⟨hxM, hball hx⟩
      have hφx : 0 ≤ scaledRadialCutoff ξ φ ρ x := hφnonneg _
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hφx]
      calc
        scaledRadialCutoff ξ φ ρ x * ‖inner ℝ (x - ξ) (H x)‖ ≤
            scaledRadialCutoff ξ φ ρ x * ((ρ * A) * Λ) :=
          mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
            (mul_le_mul hr hHx (norm_nonneg _) (mul_pos hρ hA).le)) hφx
        _ = (ρ * A * Λ) * scaledRadialCutoff ξ φ ρ x := by ring
    · rw [scaledRadialCutoff_eq_zero_of_notMem_closedBall ξ hA hcutoff hρ hx]
      simp only [zero_mul, norm_zero, mul_zero, le_refl]
  have h := MeasureTheory.norm_integral_le_of_norm_le (hφint.const_mul (ρ * A * Λ)) hb
  simpa only [cutoffMeanCurvaturePairing, Real.norm_eq_abs, MeasureTheory.integral_const_mul,
    cutoffMass] using h

/-- The absolute estimate following corrected (3.16): for a cutoff supported
below radius `Aρ`, `|E₀(ρ)| ≤ A Λ ρ⁻ⁿ I(ρ)`. Simon takes `A = 1+ε`. -/
theorem abs_cutoffMeanCurvatureError_le
    {U : Set E} {H : E → E} {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφnonneg : ∀ t, 0 ≤ φ t)
    {A : ℝ} (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall ξ (ρ * A) ⊆ U) :
    |V.cutoffMeanCurvatureError ξ H φ ρ| ≤ A * Λ * (V.cutoffMass ξ φ ρ / ρ ^ n) := by
  rw [cutoffMeanCurvatureError, abs_div, abs_of_pos (pow_pos hρ (n + 1))]
  calc
    |V.cutoffMeanCurvaturePairing ξ H φ ρ| / ρ ^ (n + 1) ≤
        (ρ * A * Λ * V.cutoffMass ξ φ ρ) / ρ ^ (n + 1) :=
      div_le_div_of_nonneg_right
        (V.abs_cutoffMeanCurvaturePairing_le hbound ξ hφ hφnonneg hA hcutoff hρ hball)
        (pow_pos hρ (n + 1)).le
    _ = A * Λ * (V.cutoffMass ξ φ ρ / ρ ^ n) := by
      rw [pow_succ]
      field_simp

theorem HasGeneralizedMeanCurvatureIn.cutoffMass_deriv_identity
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    n * V.cutoffMass ξ φ ρ - ρ * deriv (V.cutoffMass ξ φ) ρ =
      -ρ * deriv (V.cutoffNormalMass ξ φ) ρ - V.cutoffMeanCurvaturePairing ξ H φ ρ := by
  let η : ℝ → ℝ := fun t ↦ φ (t / ρ ^ 2)
  have hη : ContDiff ℝ 1 η := hφ.comp (contDiff_id.div_const (ρ ^ 2))
  have hηcutoff : ∀ t, (ρ * A) ^ 2 ≤ t → η t = 0 := by
    intro t ht
    apply hcutoff
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
    nlinarith [ht]
  have hηderiv : ∀ t, deriv η t = deriv φ (t / ρ ^ 2) / ρ ^ 2 := by
    intro t
    have h := ((hφ.differentiable (by simp) _).hasDerivAt).comp t
      ((hasDerivAt_id t).div_const (ρ ^ 2))
    simpa [η, Function.comp_def, div_eq_mul_inv] using h.deriv
  have heq := HasGeneralizedMeanCurvatureIn.integral_squaredRadial_normal (V := V) hH ξ
    (mul_pos hρ hA).le hball hη hηcutoff
  have hpoint : ∀ x : E, 2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2 =
      -ρ * scaledRadialCutoffDeriv ξ φ ρ x := by
    intro x
    rw [hηderiv, scaledRadialCutoffDeriv]
    field_simp
  simp_rw [hpoint, mul_assoc (-ρ), MeasureTheory.integral_const_mul] at heq
  rw [(V.hasDerivAt_cutoffMass ξ hφ hA hcutoff hρ).deriv,
    (V.hasDerivAt_cutoffNormalMass ξ hφ hA hcutoff hρ).deriv]
  simpa only [cutoffMass, cutoffMeanCurvaturePairing, scaledRadialCutoff, η,
    neg_mul, ← sub_eq_add_neg] using heq

/-- Corrected Simon (4.3.16), also (4.4.1): the normalized cutoff mass has
normal-radial derivative **plus** the stated mean-curvature error. Only local
integrability of `H` is required here; boundedness is used in the estimate. -/
theorem HasGeneralizedMeanCurvatureIn.hasDerivAt_normalizedCutoffMass
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    HasDerivAt (fun t ↦ V.cutoffMass ξ φ t / t ^ n)
      ((∫ x, scaledRadialCutoffDeriv ξ φ ρ x * V.radialNormalSq ξ x ∂V.weight) /
        ρ ^ n + V.cutoffMeanCurvatureError ξ H φ ρ) ρ := by
  have hI := V.hasDerivAt_cutoffMass ξ hφ hA hcutoff hρ
  have hJ := V.hasDerivAt_cutoffNormalMass ξ hφ hA hcutoff hρ
  have hrel := HasGeneralizedMeanCurvatureIn.cutoffMass_deriv_identity (V := V) hH ξ
    hφ hA hcutoff hρ hball
  rw [hI.deriv, hJ.deriv] at hrel
  have hp : HasDerivAt (fun t : ℝ ↦ t ^ n) (n * ρ ^ n / ρ) ρ := by
    convert (hasDerivAt_id ρ).pow n using 1
    · rfl
    · cases n with
      | zero => simp
      | succ m => simp [pow_succ, hρ.ne', mul_div_assoc]
  convert hI.fun_div hp (pow_ne_zero n hρ.ne') using 1
  · simp only [cutoffMeanCurvatureError, pow_succ]
    field_simp
    linear_combination hrel

/-! ### Exponentially corrected monotonicity -/

/-- The differential inequality behind the bounded-mean-curvature density
conclusions: an exponential correction makes the cutoff ratio monotone. -/
theorem HasGeneralizedMeanCurvatureIn.exp_normalizedCutoffMass_monotoneOn
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφnonneg : ∀ t, 0 ≤ φ t)
    (hφanti : Antitone φ) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {σ ρ : ℝ}
    (hσ : 0 < σ) (_hσρ : σ ≤ ρ) (hball : closedBall ξ (ρ * A) ⊆ U) :
    MonotoneOn (fun t ↦ Real.exp (A * Λ * t) * (V.cutoffMass ξ φ t / t ^ n)) (Icc σ ρ) := by
  let F := fun t ↦ V.cutoffMass ξ φ t / t ^ n
  let N := fun t ↦ (∫ x, scaledRadialCutoffDeriv ξ φ t x * V.radialNormalSq ξ x ∂V.weight) / t ^ n
  let D := fun t ↦ Real.exp (A * Λ * t) *
    (A * Λ * F t + N t + V.cutoffMeanCurvatureError ξ H φ t)
  have hderiv : ∀ t ∈ Icc σ ρ,
      HasDerivAt (fun t ↦ Real.exp (A * Λ * t) * F t) (D t) t := by
    intro t ht
    have htb : closedBall ξ (t * A) ⊆ U :=
      (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right ht.2 hA.le)).trans hball
    have hF := HasGeneralizedMeanCurvatureIn.hasDerivAt_normalizedCutoffMass
      (V := V) hH ξ hφ hA hcutoff (hσ.trans_le ht.1) htb
    have he := (hasDerivAt_const_mul (A * Λ) (x := t)).exp
    convert he.mul hF using 1
    dsimp [D, F, N]
    ring
  have hD : ∀ t ∈ Icc σ ρ, 0 ≤ D t := by
    intro t ht
    have htpos := hσ.trans_le ht.1
    have htb : closedBall ξ (t * A) ⊆ U :=
      (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right ht.2 hA.le)).trans hball
    have hE := (abs_le.mp (V.abs_cutoffMeanCurvatureError_le hbound ξ
      hφ hφnonneg hA hcutoff htpos htb)).1
    have hN : 0 ≤ N t := div_nonneg (MeasureTheory.integral_nonneg fun x ↦
      mul_nonneg (scaledRadialCutoffDeriv_nonneg ξ x hφanti htpos)
        (V.radialNormalSq_nonneg ξ x)) (pow_pos htpos n).le
    apply mul_nonneg (Real.exp_pos _).le
    dsimp [F] at hE ⊢
    linarith
  apply monotoneOn_of_deriv_nonneg (convex_Icc σ ρ)
    (fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hderiv t (interior_subset ht)).deriv]
    exact hD t (interior_subset ht)

/-- The closed-ball monotonicity consequence of Simon (4.3.17), derived by
letting the outward cutoff width tend to zero. This is not the full `F,G`
annular identity of that theorem. -/
theorem HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) (ξ : E) {R : ℝ}
    (hball : closedBall ξ R ⊆ U) :
    MonotoneOn (fun ρ ↦ Real.exp (Λ * ρ) * (V.weight.real (closedBall ξ ρ) / ρ ^ n))
      (Ioo 0 R) := by
  intro σ hσ ρ hρ hσρ
  have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hsum : Tendsto (fun ε : ℝ ↦ 1 + ε) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hid
  have hlim {t : ℝ} (ht : 0 < t) :
      Tendsto (fun ε ↦ Real.exp ((1 + ε) * Λ * t) *
        (V.cutoffMass ξ (monotonicityCutoff ε) t / t ^ n)) (𝓝[>] (0 : ℝ))
        (𝓝 (Real.exp (Λ * t) * (V.weight.real (closedBall ξ t) / t ^ n))) := by
    have he := Real.continuous_exp.continuousAt.tendsto.comp ((hsum.mul_const Λ).mul_const t)
    simpa only [one_mul, Function.comp_apply] using
      he.mul ((V.tendsto_cutoffMass ξ ht).div_const (t ^ n))
  have hscale : Tendsto (fun ε : ℝ ↦ ρ * (1 + ε)) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    simpa only [mul_one] using hsum.const_mul ρ
  apply le_of_tendsto_of_tendsto (hlim hσ.1) (hlim hρ.1)
  filter_upwards [self_mem_nhdsWithin, hscale.eventually (gt_mem_nhds hρ.2)] with ε hε hεR
  have hεpos : 0 < ε := hε
  have hmono := HasGeneralizedMeanCurvatureIn.exp_normalizedCutoffMass_monotoneOn
    (V := V) hH hbound ξ (contDiff_monotonicityCutoff ε)
    (fun t ↦ (monotonicityCutoff_mem_Icc ε t).1) (monotonicityCutoff_antitone hε)
    (show 0 < 1 + ε by linarith) (monotonicityCutoff_cutoff hεpos) hσ.1 hσρ
    ((closedBall_subset_closedBall hεR.le).trans hball)
  exact hmono ⟨le_rfl, hσρ⟩ ⟨hσρ, le_rfl⟩ hσρ

/-- The density-existence consequence of Simon (4.3.17), before the factor
`ωₙ`. The limiting number is real and nonnegative, with no density assumption
on the varifold. -/
theorem HasGeneralizedMeanCurvatureIn.exists_tendsto_normalizedBallMass_real
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) (ξ : E) {R : ℝ}
    (hR : 0 < R) (hball : closedBall ξ R ⊆ U) :
    ∃ d : ℝ, 0 ≤ d ∧ Tendsto (fun ρ ↦ V.weight.real (closedBall ξ ρ) / ρ ^ n)
      (𝓝[>] (0 : ℝ)) (𝓝 d) := by
  let F := fun ρ ↦ Real.exp (Λ * ρ) * (V.weight.real (closedBall ξ ρ) / ρ ^ n)
  have hnonneg : ∀ ρ ∈ Ioo 0 R, 0 ≤ F ρ := by
    intro ρ hρ
    exact mul_nonneg (Real.exp_pos _).le
      (div_nonneg ENNReal.toReal_nonneg (pow_pos hρ.1 n).le)
  have hne : (Ioo (0 : ℝ) R).Nonempty := ⟨R / 2, half_pos hR, half_lt_self hR⟩
  have hFlim := MonotoneOn.tendsto_nhdsWithin_Ioo_right hne
    (HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn
      (V := V) hH hbound ξ hball)
    (show BddBelow (F '' Ioo 0 R) from ⟨0, by rintro _ ⟨ρ, hρ, rfl⟩; exact hnonneg ρ hρ⟩)
  refine ⟨sInf (F '' Ioo 0 R), le_csInf (hne.image F) ?_, ?_⟩
  · rintro _ ⟨ρ, hρ, rfl⟩
    exact hnonneg ρ hρ
  · have he : Tendsto (fun ρ : ℝ ↦ Real.exp (Λ * ρ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
      have hc : Continuous (fun ρ : ℝ ↦ Real.exp (Λ * ρ)) := by fun_prop
      have hreal : Tendsto (fun ρ : ℝ ↦ Real.exp (Λ * ρ))
          (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp (Λ * 0))) :=
        (hc.tendsto 0).mono_left inf_le_left
      simpa only [mul_zero, Real.exp_zero] using hreal
    have hlim := hFlim.div he (by norm_num)
    have heq : (F / fun ρ : ℝ ↦ Real.exp (Λ * ρ)) =
        (fun ρ ↦ V.weight.real (closedBall ξ ρ) / ρ ^ n) := by
      funext ρ
      exact mul_div_cancel_left₀ _ (Real.exp_ne_zero _)
    rw [heq, div_one] at hlim
    exact hlim

theorem tendsto_normalizedBallMass_of_tendsto_real {ξ : E} {d : ℝ}
    (h : Tendsto (fun ρ ↦ V.weight.real (closedBall ξ ρ) / ρ ^ n)
      (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    Tendsto (V.normalizedBallMass ξ) (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal d)) := by
  apply (ENNReal.tendsto_ofReal h).congr'
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  exact V.ofReal_normalizedBallMass_real ξ hρ

/-- Bounded generalized mean curvature gives the same canonical density
limit used in the stationary case; this is a consequence of (4.3.17). -/
theorem HasGeneralizedMeanCurvatureIn.tendsto_normalizedBallMass
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) (ξ : E) {R : ℝ}
    (hR : 0 < R) (hball : closedBall ξ R ⊆ U) :
    Tendsto (V.normalizedBallMass ξ) (𝓝[>] (0 : ℝ))
      (𝓝 (V.lowerDensityMassRatio ξ)) := by
  obtain ⟨d, _, hd⟩ := HasGeneralizedMeanCurvatureIn.exists_tendsto_normalizedBallMass_real
    (V := V) hH hbound ξ hR hball
  have hlim := V.tendsto_normalizedBallMass_of_tendsto_real hd
  have heq : V.lowerDensityMassRatio ξ = ENNReal.ofReal d := hlim.liminf_eq
  rw [heq]
  exact hlim

theorem HasGeneralizedMeanCurvatureIn.lowerDensityMassRatio_ne_top
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) (hU : IsOpen U)
    {ξ : E} (hξ : ξ ∈ U) : V.lowerDensityMassRatio ξ ≠ ⊤ := by
  obtain ⟨R, hR, hball⟩ := exists_pos_closedBall_subset hU hξ
  obtain ⟨d, _, hd⟩ := HasGeneralizedMeanCurvatureIn.exists_tendsto_normalizedBallMass_real
    (V := V) hH hbound ξ hR hball
  have heq : V.lowerDensityMassRatio ξ = ENNReal.ofReal d :=
    (V.tendsto_normalizedBallMass_of_tendsto_real hd).liminf_eq
  rw [heq]
  exact ENNReal.ofReal_ne_top

theorem HasGeneralizedMeanCurvatureIn.stationaryDensity_ne_top
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) (hU : IsOpen U)
    {ξ : E} (hξ : ξ ∈ U) : V.stationaryDensity ξ ≠ ⊤ := by
  exact ENNReal.div_ne_top
    (HasGeneralizedMeanCurvatureIn.lowerDensityMassRatio_ne_top (V := V) hH hbound hU hξ)
    (ne_of_gt (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)))

/-- The full `ωₙ`-normalized real density exists and is finite at every
point of an open domain with bounded generalized mean curvature. -/
theorem HasGeneralizedMeanCurvatureIn.tendsto_densityQuotient_real
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) (hU : IsOpen U)
    {ξ : E} (hξ : ξ ∈ U) :
    Tendsto (fun ρ ↦ V.weight.real (closedBall ξ ρ) /
      ((Chapter01.realUnitBallVolume (n : ℝ)).toReal * ρ ^ n))
      (𝓝[>] (0 : ℝ)) (𝓝 (V.stationaryDensityReal ξ)) := by
  obtain ⟨R, hR, hball⟩ := exists_pos_closedBall_subset hU hξ
  have hnorm := HasGeneralizedMeanCurvatureIn.tendsto_normalizedBallMass
    (V := V) hH hbound ξ hR hball
  have hquot : Tendsto (V.densityQuotient ξ) (𝓝[>] (0 : ℝ))
      (𝓝 (V.stationaryDensity ξ)) :=
    (ENNReal.continuous_div_const _
      (ne_of_gt (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)))).continuousAt.tendsto.comp hnorm
  have hreal := (ENNReal.tendsto_toReal
    (HasGeneralizedMeanCurvatureIn.stationaryDensity_ne_top (V := V) hH hbound hU hξ)).comp hquot
  apply hreal.congr'
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  simp only [Function.comp_apply, V.densityQuotient_eq ξ hρ, ENNReal.toReal_div,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hρ) n),
    MeasureTheory.measureReal_def]

/-- The exponentially corrected ball ratio, with extended nonnegative
values so that upper semicontinuity and density comparison remain literal. -/
def expNormalizedBallMass (Λ : ℝ) (ξ : E) (ρ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (Λ * ρ)) * V.normalizedBallMass ξ ρ

theorem ofReal_expNormalizedBallMass_real (Λ : ℝ) (ξ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    ENNReal.ofReal (Real.exp (Λ * ρ) * (V.weight.real (closedBall ξ ρ) / ρ ^ n)) =
      V.expNormalizedBallMass Λ ξ ρ := by
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, V.ofReal_normalizedBallMass_real ξ hρ]
  rfl

theorem HasGeneralizedMeanCurvatureIn.expNormalizedBallMass_monotoneOn
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) (ξ : E) {R : ℝ}
    (hball : closedBall ξ R ⊆ U) :
    MonotoneOn (V.expNormalizedBallMass Λ ξ) (Ioo 0 R) := by
  intro σ hσ ρ hρ hσρ
  rw [← V.ofReal_expNormalizedBallMass_real Λ ξ hσ.1,
    ← V.ofReal_expNormalizedBallMass_real Λ ξ hρ.1]
  exact ENNReal.ofReal_le_ofReal
    (HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn
      (V := V) hH hbound ξ hball hσ hρ hσρ)

theorem HasGeneralizedMeanCurvatureIn.tendsto_expNormalizedBallMass
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) (ξ : E) {R : ℝ}
    (hR : 0 < R) (hball : closedBall ξ R ⊆ U) :
    Tendsto (V.expNormalizedBallMass Λ ξ) (𝓝[>] (0 : ℝ))
      (𝓝 (V.lowerDensityMassRatio ξ)) := by
  have he : Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal (Real.exp (Λ * ρ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ≥0∞)) := by
    have hc : Continuous (fun ρ : ℝ ↦ Real.exp (Λ * ρ)) := by fun_prop
    have hreal : Tendsto (fun ρ : ℝ ↦ Real.exp (Λ * ρ))
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp (Λ * 0))) :=
      (hc.tendsto 0).mono_left inf_le_left
    simpa only [mul_zero, Real.exp_zero, ENNReal.ofReal_one] using
      ENNReal.tendsto_ofReal hreal
  change Tendsto (fun ρ ↦ ENNReal.ofReal (Real.exp (Λ * ρ)) * V.normalizedBallMass ξ ρ)
    (𝓝[>] (0 : ℝ)) (𝓝 (V.lowerDensityMassRatio ξ))
  simpa only [one_mul] using
    ENNReal.Tendsto.mul he (Or.inl one_ne_zero)
      (HasGeneralizedMeanCurvatureIn.tendsto_normalizedBallMass (V := V) hH hbound ξ hR hball)
      (Or.inr ENNReal.one_ne_top)

theorem HasGeneralizedMeanCurvatureIn.lowerDensityMassRatio_le_expNormalizedBallMass
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) {ξ : E} {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hball : closedBall ξ R ⊆ U) :
    V.lowerDensityMassRatio ξ ≤ V.expNormalizedBallMass Λ ξ ρ := by
  apply le_of_tendsto
    (HasGeneralizedMeanCurvatureIn.tendsto_expNormalizedBallMass
      (V := V) hH hbound ξ (hρ.trans hρR) hball)
  filter_upwards [Ioo_mem_nhdsGT hρ] with t ht
  exact HasGeneralizedMeanCurvatureIn.expNormalizedBallMass_monotoneOn
    (V := V) hH hbound ξ hball ⟨ht.1, ht.2.trans hρR⟩ ⟨hρ, hρR⟩ ht.2.le

theorem upperSemicontinuous_expNormalizedBallMass (Λ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    UpperSemicontinuous (fun ξ : E ↦ V.expNormalizedBallMass Λ ξ ρ) := by
  exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_upperSemicontinuous
    (V.upperSemicontinuous_normalizedBallMass hρ) (fun _ _ h ↦ mul_le_mul_right h _)

theorem HasGeneralizedMeanCurvatureIn.upperSemicontinuousAt_lowerDensityMassRatio
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) (hU : IsOpen U)
    {ξ : E} (hξ : ξ ∈ U) : UpperSemicontinuousAt V.lowerDensityMassRatio ξ := by
  obtain ⟨R, hR, hball⟩ := exists_pos_closedBall_subset hU hξ
  intro a ha
  have hlim := HasGeneralizedMeanCurvatureIn.tendsto_expNormalizedBallMass
    (V := V) hH hbound ξ hR hball
  obtain ⟨ρ, hmass, hρ⟩ :=
    ((hlim.eventually (gt_mem_nhds ha)).and (Ioo_mem_nhdsGT (half_pos hR))).exists
  filter_upwards [(V.upperSemicontinuous_expNormalizedBallMass Λ hρ.1) ξ a hmass,
    ball_mem_nhds ξ (half_pos hR)] with η hηmass hη
  apply lt_of_le_of_lt
    (HasGeneralizedMeanCurvatureIn.lowerDensityMassRatio_le_expNormalizedBallMass
      (V := V) hH hbound hρ.1 hρ.2 ?_) hηmass
  apply subset_trans (closedBall_subset_closedBall' (x := η) (y := ξ) ?_) hball
  have hdist : dist η ξ < R / 2 := hη
  linarith

/-- The upper-semicontinuity conclusion following Simon (4.3.17), under the
source bounded-mean-curvature hypotheses and with closed-ball densities. -/
theorem HasGeneralizedMeanCurvatureIn.upperSemicontinuousOn_stationaryDensity
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) (hU : IsOpen U) :
    UpperSemicontinuousOn V.stationaryDensity U := by
  apply (ENNReal.continuous_div_const _
    (ne_of_gt (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)))).comp_upperSemicontinuousOn
  · intro ξ hξ
    exact (HasGeneralizedMeanCurvatureIn.upperSemicontinuousAt_lowerDensityMassRatio
      (V := V) hH hbound hU hξ).upperSemicontinuousWithinAt U
  · exact fun _ _ h ↦ ENNReal.div_le_div_right h _

theorem HasGeneralizedMeanCurvatureIn.upperSemicontinuousOn_stationaryDensityReal
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) (hU : IsOpen U) :
    UpperSemicontinuousOn V.stationaryDensityReal U := by
  intro ξ hξ a ha
  have hapos : 0 < a := ENNReal.toReal_nonneg.trans_lt ha
  have hlt : V.stationaryDensity ξ < ENNReal.ofReal a := by
    apply (ENNReal.toReal_lt_toReal
      (HasGeneralizedMeanCurvatureIn.stationaryDensity_ne_top (V := V) hH hbound hU hξ)
      ENNReal.ofReal_ne_top).mp
    simpa only [stationaryDensityReal, ENNReal.toReal_ofReal hapos.le] using ha
  filter_upwards [HasGeneralizedMeanCurvatureIn.upperSemicontinuousOn_stationaryDensity
    (V := V) hH hbound hU ξ hξ (ENNReal.ofReal a) hlt,
    self_mem_nhdsWithin] with η hη hηU
  have h := (ENNReal.toReal_lt_toReal
    (HasGeneralizedMeanCurvatureIn.stationaryDensity_ne_top (V := V) hH hbound hU hηU)
    ENNReal.ofReal_ne_top).mpr hη
  simpa only [stationaryDensityReal, ENNReal.toReal_ofReal hapos.le] using h

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
