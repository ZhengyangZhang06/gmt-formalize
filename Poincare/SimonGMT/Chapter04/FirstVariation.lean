module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.Monotone
public import Poincare.SimonGMT.Chapter04.Basic

@[expose] public section

/-!
# Simon GMT, Chapter 4, §§2--3: first variation and monotonicity data

The first variation below is the integral of the trace of the ambient
derivative restricted to the approximate tangent plane.  Thus stationarity
and generalized mean curvature are predicates on the actual rectifiable
varifold, rather than placeholders on an unrelated real-valued function.

The fundamental monotonicity formula is derived from stationarity by the
radial divergence calculation, dominated scale differentiation, a cutoff
squeeze, and dominated convergence. `SatisfiesStationaryMonotonicity` records
the resulting identity, and `IsStationaryIn.satisfiesStationaryMonotonicity`
proves it for the actual weight and tangent projection. All balls in that
identity are closed, following Simon's notation. The reversed prefactors
in the printed intermediate squeeze (4.3.5) are corrected explicitly below;
the limiting formula (4.3.6) is unchanged.
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

/-- Orthogonal projection onto the approximate tangent plane at `x`. -/
def tangentProjection (x : E) : E →L[ℝ] E :=
  (V.tangentAt x).starProjection

/-- Orthogonal projection onto the normal complement of the approximate
tangent plane at `x`. -/
def normalProjection (x : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - V.tangentProjection x

/-! ### The radial first-variation calculation -/

/-- The squared-radius radial vector field used below.  Replacing Simon's
`r = ‖x-ξ‖` by `r²` avoids the nonsmoothness of the norm at the centre; the
resulting first-variation identity is equivalent after reparametrizing the
one-variable cutoff. -/
def squaredRadialVectorField (ξ : E) (η : ℝ → ℝ) (x : E) : E :=
  η (‖x - ξ‖ ^ 2) • (x - ξ)

/-- A `C¹` scalar cutoff gives a `C¹` squared-radius radial vector field. -/
theorem contDiff_squaredRadialVectorField (ξ : E) {η : ℝ → ℝ}
    (hη : ContDiff ℝ 1 η) :
    ContDiff ℝ 1 (squaredRadialVectorField ξ η) := by
  have hsub : ContDiff ℝ 1 (fun x : E ↦ x - ξ) := contDiff_id.sub contDiff_const
  exact (hη.comp (hsub.norm_sq ℝ)).smul hsub

/-- A scalar cutoff vanishing beyond `R²` produces a radial field supported
in the closed ball of radius `R`. This supplies the support hypothesis in
the stationary radial-cutoff argument from the scalar cutoff itself. -/
theorem tsupport_squaredRadialVectorField_subset_closedBall
    (ξ : E) {R : ℝ} (hR : 0 ≤ R) {η : ℝ → ℝ}
    (hcutoff : ∀ t, R ^ 2 ≤ t → η t = 0) :
    tsupport (squaredRadialVectorField ξ η) ⊆ closedBall ξ R := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hball
  have hnorm : R < ‖x - ξ‖ := by
    simpa only [mem_closedBall, dist_eq_norm, not_le] using hball
  have hzero : η (‖x - ξ‖ ^ 2) = 0 :=
    hcutoff _ (by nlinarith [norm_nonneg (x - ξ)])
  exact hx (by simp [squaredRadialVectorField, hzero])

/-- Such a cutoff gives a compactly supported radial field in finite
dimensional Euclidean space. -/
theorem hasCompactSupport_squaredRadialVectorField
    (ξ : E) {R : ℝ} (hR : 0 ≤ R) {η : ℝ → ℝ}
    (hcutoff : ∀ t, R ^ 2 ≤ t → η t = 0) :
    HasCompactSupport (squaredRadialVectorField ξ η) :=
  (isCompact_closedBall ξ R).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_squaredRadialVectorField_subset_closedBall ξ hR hcutoff)

/-- The derivative of the squared-radius radial vector field. -/
theorem hasFDerivAt_squaredRadialVectorField
    (ξ x : E) {η : ℝ → ℝ} {η' : ℝ}
    (hη : HasDerivAt η η' (‖x - ξ‖ ^ 2)) :
    HasFDerivAt (squaredRadialVectorField ξ η)
      (η (‖x - ξ‖ ^ 2) • ContinuousLinearMap.id ℝ E +
        (2 * η') • (innerSL ℝ (x - ξ)).smulRight (x - ξ)) x := by
  have hsub : HasFDerivAt (fun y : E ↦ y - ξ) (ContinuousLinearMap.id ℝ E) x :=
    hasFDerivAt_sub_const ξ
  have hsq := hsub.norm_sq
  have hηComp := hη.comp_hasFDerivAt x hsq
  convert hηComp.smul hsub using 1
  · rfl
  · ext w
    simp [mul_smul]
    module

/-- The trace of orthogonal projection onto a finite-dimensional subspace is
the dimension of that subspace. -/
theorem trace_starProjection (P : Submodule ℝ E) :
    LinearMap.trace ℝ E P.starProjection.toLinearMap =
      (Module.finrank ℝ P : ℝ) := by
  rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp]
  rw [LinearMap.trace_comp_comm']
  have hcomp : P.orthogonalProjectionOnto.toLinearMap.comp P.subtypeL.toLinearMap =
      LinearMap.id := by
    ext x
    simp
  rw [hcomp, LinearMap.trace_id]

/-- Trace of the sum of a scalar endomorphism and a rank-one endomorphism,
after restriction to a plane. -/
theorem trace_radialEndomorphism (P : Submodule ℝ E) (a b : ℝ)
    (f : E →L[ℝ] ℝ) (v : E) :
    LinearMap.trace ℝ E
        (((a • ContinuousLinearMap.id ℝ E) + b • f.smulRight v).toLinearMap.comp
          P.starProjection.toLinearMap) =
      a * (Module.finrank ℝ P : ℝ) + b * f (P.starProjection v) := by
  change LinearMap.trace ℝ E
      (((a • LinearMap.id) + b • f.toLinearMap.smulRight v).comp
        P.starProjection.toLinearMap) = _
  have hcomp :
      (((a • LinearMap.id) + b • f.toLinearMap.smulRight v).comp
          P.starProjection.toLinearMap) =
        a • P.starProjection.toLinearMap +
          b • (f.toLinearMap.comp P.starProjection.toLinearMap).smulRight v := by
    ext w
    simp
  rw [hcomp, map_add, map_smul, map_smul, LinearMap.trace_smulRight,
    trace_starProjection]
  simp

/-- The inner product of a vector with its orthogonal projection is the
squared norm of that projection. -/
theorem inner_starProjection_eq_norm_sq (P : Submodule ℝ E) (v : E) :
    inner ℝ v (P.starProjection v) = ‖P.starProjection v‖ ^ 2 := by
  rw [← P.inner_starProjection_left_eq_right v v]
  simpa using P.re_inner_starProjection_eq_normSq v

/-- Simon (4.2.3): tangential divergence is the trace of `DX` restricted to
the approximate tangent plane. -/
def tangentialDivergence (X : E → E) (x : E) : ℝ :=
  LinearMap.trace ℝ E
    ((fderiv ℝ X x).toLinearMap.comp (V.tangentProjection x).toLinearMap)

/-- Simon (4.3.2), in the squared-radius parametrization: the tangential
divergence of a radial vector field is the dimension term plus the squared
tangential-radial term. -/
theorem tangentialDivergence_squaredRadialVectorField
    (ξ x : E) {η : ℝ → ℝ} {η' : ℝ}
    (hη : HasDerivAt η η' (‖x - ξ‖ ^ 2))
    (hrank : Module.finrank ℝ (V.tangentAt x) = n) :
    V.tangentialDivergence (squaredRadialVectorField ξ η) x =
      n * η (‖x - ξ‖ ^ 2) +
        2 * η' * ‖V.tangentProjection x (x - ξ)‖ ^ 2 := by
  rw [tangentialDivergence,
    (hasFDerivAt_squaredRadialVectorField ξ x hη).fderiv, tangentProjection,
    trace_radialEndomorphism]
  rw [hrank, innerSL_apply_apply, inner_starProjection_eq_norm_sq]
  simp only [mul_assoc]
  ring

/-- Tangential divergence computed with an explicitly supplied tangent-plane
representative. -/
def tangentialDivergenceAlong (P : E → Submodule ℝ E)
    (X : E → E) (x : E) : ℝ :=
  LinearMap.trace ℝ E
    ((fderiv ℝ X x).toLinearMap.comp (P x).starProjection.toLinearMap)

/-- Tangential divergence is independent, weight-almost everywhere, of the
chosen approximate-tangent representative. -/
theorem tangentialDivergenceAlong_ae_eq
    (P : E → Submodule ℝ E)
    (hP : ∀ᵐ x
      ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n).restrict V.carrier,
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt
          n V.carrier x (P x)) (X : E → E) :
    tangentialDivergenceAlong P X =ᵐ[V.weight]
      V.tangentialDivergence X := by
  filter_upwards [V.tangentField_ae_eq_weight P hP] with x hx
  simp [tangentialDivergenceAlong, tangentialDivergence, tangentProjection, hx]

/-- Consequently, the first-variation integral is unchanged by replacing the
chosen tangent field with any other approximate-tangent representative. -/
theorem integral_tangentialDivergenceAlong_eq
    (P : E → Submodule ℝ E)
    (hP : ∀ᵐ x
      ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n).restrict V.carrier,
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt
          n V.carrier x (P x)) (X : E → E) :
    ∫ x, tangentialDivergenceAlong P X x ∂V.weight =
      ∫ x, V.tangentialDivergence X x ∂V.weight :=
  MeasureTheory.integral_congr_ae (V.tangentialDivergenceAlong_ae_eq P hP X)

/-- The trace of an ambient linear map restricted to a tangent plane is
bounded by the ambient dimension times its operator norm. -/
theorem abs_trace_comp_tangentProjection_le (A : E →L[ℝ] E) (x : E) :
    |LinearMap.trace ℝ E
      (A.toLinearMap.comp (V.tangentProjection x).toLinearMap)| ≤
        (Module.finrank ℝ E : ℝ) * ‖A‖ := by
  let b := stdOrthonormalBasis ℝ E
  rw [LinearMap.trace_eq_sum_inner _ b]
  calc
    |∑ i, inner ℝ (b i) (A (V.tangentProjection x (b i)))| ≤
        ∑ i, |inner ℝ (b i) (A (V.tangentProjection x (b i)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i, ‖A‖ := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        |inner ℝ (b i) (A (V.tangentProjection x (b i)))| ≤
            ‖b i‖ * ‖A (V.tangentProjection x (b i))‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ 1 * (‖A‖ * ‖V.tangentProjection x (b i)‖) := by
          gcongr
          · exact le_of_eq (b.orthonormal.norm_eq_one i)
          · exact A.le_opNorm _
        _ ≤ 1 * (‖A‖ * ‖b i‖) := by
          gcongr
          exact (V.tangentAt x).norm_starProjection_apply_le _
        _ = ‖A‖ := by rw [b.orthonormal.norm_eq_one]; simp
    _ = (Module.finrank ℝ E : ℝ) * ‖A‖ := by simp

/-- Measurability of the tangent projection and continuity of the derivative
make the tangential divergence measurable for the varifold weight. -/
theorem tangentialDivergence_aemeasurable {X : E → E}
    (hX : ContDiff ℝ 1 X) :
    AEMeasurable (V.tangentialDivergence X) V.weight := by
  let b := stdOrthonormalBasis ℝ E
  have hDX : AEMeasurable (fderiv ℝ X) V.weight :=
    (hX.fderiv_right (m := 0) (by simp)).continuous.aemeasurable
  rw [show V.tangentialDivergence X =
      fun x ↦ ∑ i, inner ℝ (b i)
        (fderiv ℝ X x (V.tangentProjection x (b i))) by
    funext x
    exact LinearMap.trace_eq_sum_inner _ b]
  have hs := Finset.aemeasurable_sum Finset.univ (fun i _ ↦
    (innerSL ℝ (b i)).measurable.comp_aemeasurable
      (ContinuousLinearMap.measurable_apply₂.comp_aemeasurable
        (hDX.prodMk
          (V.tangentProjection_aemeasurable_weight.apply_continuousLinearMap (b i)))))
  refine hs.congr ?_
  filter_upwards with x
  simp [Function.comp_def, tangentProjection]

/-- Simon (4.2.2): the first variation evaluated on a compactly supported
`C¹` vector field.  The proof arguments prevent forming this integral for an
arbitrary field for which measurability/integrability is not known. -/
def firstVariation (X : E → E) (_hX : ContDiff ℝ 1 X)
    (_hcompact : HasCompactSupport X) : ℝ :=
  ∫ x, V.tangentialDivergence X x ∂V.weight

/-- The integrand defining first variation is genuinely Bochner integrable.
This is derived from measurable tangent projection, local finiteness of the
weight, `C¹` regularity, and compact support; it is not extra varifold data. -/
theorem tangentialDivergence_integrable_of_isAdmissible
    {X : E → E} (hX : ContDiff ℝ 1 X) (hcompact : HasCompactSupport X) :
    MeasureTheory.Integrable (V.tangentialDivergence X) V.weight := by
  have hDint : MeasureTheory.Integrable (fderiv ℝ X) V.weight :=
    (hX.fderiv_right (m := 0) (by simp)).continuous.integrable_of_hasCompactSupport
      (hcompact.fderiv ℝ)
  refine (hDint.norm.const_mul (Module.finrank ℝ E : ℝ)).mono
    (V.tangentialDivergence_aemeasurable hX).aestronglyMeasurable ?_
  filter_upwards with x
  simpa [tangentialDivergence, Real.norm_eq_abs] using
    V.abs_trace_comp_tangentProjection_le (fderiv ℝ X x) x

@[simp] theorem tangentialDivergence_zero (x : E) :
    V.tangentialDivergence 0 x = 0 := by
  simp [tangentialDivergence, fderiv_zero]

@[simp] theorem firstVariation_zero
    (hX : ContDiff ℝ 1 (0 : E → E)) (hcompact : HasCompactSupport (0 : E → E)) :
    V.firstVariation 0 hX hcompact = 0 := by
  simp [firstVariation]

/-- The `C¹` vector fields compactly supported in `U` used in Simon
Definition 4.2.4. -/
def IsAdmissibleVectorField (U : Set E) (X : E → E) : Prop :=
  ContDiff ℝ 1 X ∧ HasCompactSupport X ∧ tsupport X ⊆ U

/-- Simon Definition 4.2.4: `V` is stationary in `U` precisely when its first
variation vanishes on every compactly supported `C¹` vector field in `U`. -/
def IsStationaryIn (U : Set E) : Prop :=
  ∀ X, ∀ hX : IsAdmissibleVectorField U X,
    V.firstVariation X hX.1 hX.2.1 = 0

/-- Stationarity gives the concrete tangential-divergence integral identity
for every admissible vector field. This is the starting point of Simon's
radial-cutoff proof of monotonicity. -/
theorem IsStationaryIn.integral_tangentialDivergence_eq_zero
    {U : Set E} (hV : V.IsStationaryIn U) {X : E → E}
    (hX : ContDiff ℝ 1 X) (hcompact : HasCompactSupport X)
    (hsupport : tsupport X ⊆ U) :
    ∫ x, V.tangentialDivergence X x ∂V.weight = 0 := by
  simpa [firstVariation] using hV X ⟨hX, hcompact, hsupport⟩

/-- The radial first-variation integrand is genuinely integrable, by its
almost-everywhere equality with the integrable tangential divergence. -/
theorem squaredRadial_tangential_integrable
    (ξ : E) {η η' : ℝ → ℝ} (hη : ContDiff ℝ 1 η)
    (hη' : ∀ t, HasDerivAt η (η' t) t)
    (hcompact : HasCompactSupport (squaredRadialVectorField ξ η)) :
    MeasureTheory.Integrable
      (fun x ↦ n * η (‖x - ξ‖ ^ 2) +
        2 * η' (‖x - ξ‖ ^ 2) * ‖V.tangentProjection x (x - ξ)‖ ^ 2)
      V.weight := by
  apply (V.tangentialDivergence_integrable_of_isAdmissible
    (contDiff_squaredRadialVectorField ξ hη) hcompact).congr
  filter_upwards [V.tangent_finrank_ae_weight] with x hx
  exact V.tangentialDivergence_squaredRadialVectorField
    ξ x (hη' (‖x - ξ‖ ^ 2)) hx

/-- The stationary radial first-variation identity underlying Simon (4.3.3),
written with a squared-radius cutoff.  This is obtained from stationarity,
not assumed as extra varifold data. -/
theorem IsStationaryIn.integral_squaredRadial_tangential_eq_zero
    {U : Set E} (hV : V.IsStationaryIn U) (ξ : E)
    {η η' : ℝ → ℝ} (hη : ContDiff ℝ 1 η)
    (hη' : ∀ t, HasDerivAt η (η' t) t)
    (hcompact : HasCompactSupport (squaredRadialVectorField ξ η))
    (hsupport : tsupport (squaredRadialVectorField ξ η) ⊆ U) :
    ∫ x, (n * η (‖x - ξ‖ ^ 2) +
        2 * η' (‖x - ξ‖ ^ 2) *
          ‖V.tangentProjection x (x - ξ)‖ ^ 2) ∂V.weight = 0 := by
  calc
    ∫ x, (n * η (‖x - ξ‖ ^ 2) +
        2 * η' (‖x - ξ‖ ^ 2) *
          ‖V.tangentProjection x (x - ξ)‖ ^ 2) ∂V.weight =
        ∫ x, V.tangentialDivergence
          (squaredRadialVectorField ξ η) x ∂V.weight := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [V.tangent_finrank_ae_weight] with x hx
      exact (V.tangentialDivergence_squaredRadialVectorField
        ξ x (hη' (‖x - ξ‖ ^ 2)) hx).symm
    _ = 0 := IsStationaryIn.integral_tangentialDivergence_eq_zero (V := V) hV
      (contDiff_squaredRadialVectorField ξ hη) hcompact hsupport

/-- Simon's stationary radial first-variation identity with admissibility
derived from a scalar cutoff supported below `R²` and a closed ball inside
the stationarity domain. No radial integral identity is assumed. -/
theorem IsStationaryIn.integral_squaredRadial_eq_zero_of_cutoff
    {U : Set E} (hV : V.IsStationaryIn U) (ξ : E)
    {R : ℝ} (hR : 0 ≤ R) (hball : closedBall ξ R ⊆ U)
    {η η' : ℝ → ℝ} (hη : ContDiff ℝ 1 η)
    (hη' : ∀ t, HasDerivAt η (η' t) t)
    (hcutoff : ∀ t, R ^ 2 ≤ t → η t = 0) :
    ∫ x, (n * η (‖x - ξ‖ ^ 2) +
        2 * η' (‖x - ξ‖ ^ 2) *
          ‖V.tangentProjection x (x - ξ)‖ ^ 2) ∂V.weight = 0 :=
  IsStationaryIn.integral_squaredRadial_tangential_eq_zero (V := V) hV ξ hη hη'
    (hasCompactSupport_squaredRadialVectorField ξ hR hcutoff)
    ((tsupport_squaredRadialVectorField_subset_closedBall ξ hR hcutoff).trans hball)

/-- The stationary first-variation identity is likewise independent of the
chosen approximate-tangent representative. -/
theorem IsStationaryIn.integral_tangentialDivergenceAlong_eq_zero
    {U : Set E} (hV : V.IsStationaryIn U)
    (P : E → Submodule ℝ E)
    (hP : ∀ᵐ x
      ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n).restrict V.carrier,
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt
          n V.carrier x (P x)) {X : E → E}
    (hX : ContDiff ℝ 1 X) (hcompact : HasCompactSupport X)
    (hsupport : tsupport X ⊆ U) :
    ∫ x, tangentialDivergenceAlong P X x ∂V.weight = 0 := by
  rw [V.integral_tangentialDivergenceAlong_eq P hP X]
  exact IsStationaryIn.integral_tangentialDivergence_eq_zero
    (V := V) hV hX hcompact hsupport

/-- Pairing of a vector field with a candidate generalized mean-curvature
field against the varifold weight. -/
def meanCurvaturePairing (X H : E → E) : ℝ :=
  ∫ x, inner ℝ (X x) (H x) ∂V.weight

/-- Simon Definition 4.3.14: `H` is a generalized mean-curvature field when
it is locally integrable and represents first variation by
`δV(X) = -∫ X·H dμ_V`. -/
def HasGeneralizedMeanCurvatureIn (U : Set E) (H : E → E) : Prop :=
  MeasureTheory.LocallyIntegrableOn H U V.weight ∧
    ∀ X, ∀ hX : IsAdmissibleVectorField U X,
      V.firstVariation X hX.1 hX.2.1 = -V.meanCurvaturePairing X H

/-- The zero generalized mean-curvature identity is exactly stationarity;
local integrability of the zero field follows from local finiteness of the
weight. -/
theorem hasGeneralizedMeanCurvature_zero_iff (U : Set E) :
    V.HasGeneralizedMeanCurvatureIn U 0 ↔ V.IsStationaryIn U := by
  constructor
  · intro h X hX
    simpa [meanCurvaturePairing] using h.2 X hX
  · intro h
    constructor
    · intro x hx
      exact MeasureTheory.integrableAtFilter_zero
    · intro X hX
      simpa [meanCurvaturePairing] using h X hX

/-! ### The concrete stationary monotonicity identity -/

/-- The normal part of the radial direction appearing in (4.3.5)--(4.3.6).
At the centre it is set to zero; every annulus used below excludes the
centre. -/
def radialNormalSq (ξ x : E) : ℝ :=
  by
    classical
    exact if x = ξ then 0 else
      ‖V.normalProjection x ((‖x - ξ‖)⁻¹ • (x - ξ))‖ ^ 2

/-- The normal projection used here really is orthogonal projection onto
the orthogonal complement of the approximate tangent plane. -/
theorem normalProjection_eq_starProjection_orthogonal (x : E) :
    V.normalProjection x = (V.tangentAt x)ᗮ.starProjection := by
  rw [Submodule.starProjection_orthogonal]
  rfl

/-- The harmless value at the centre agrees with the same projection
expression, since the normalized zero vector is zero. -/
theorem radialNormalSq_eq (ξ x : E) :
    V.radialNormalSq ξ x =
      ‖V.normalProjection x ((‖x - ξ‖)⁻¹ • (x - ξ))‖ ^ 2 := by
  classical
  by_cases hx : x = ξ
  · subst x
    simp [radialNormalSq]
  · simp [radialNormalSq, hx]

theorem radialNormalSq_nonneg (ξ x : E) :
    0 ≤ V.radialNormalSq ξ x := by
  rw [V.radialNormalSq_eq]
  positivity

/-- The squared normal component of a unit radial vector lies in `[0,1]`,
including the chosen value zero at the centre. -/
theorem radialNormalSq_le_one (ξ x : E) :
    V.radialNormalSq ξ x ≤ 1 := by
  rw [V.radialNormalSq_eq, V.normalProjection_eq_starProjection_orthogonal]
  have hnorm : ‖(‖x - ξ‖)⁻¹ • (x - ξ)‖ ≤ 1 := by
    by_cases hx : x - ξ = 0
    · simp [hx]
    · simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hp := ((V.tangentAt x)ᗮ.norm_starProjection_apply_le
    ((‖x - ξ‖)⁻¹ • (x - ξ))).trans hnorm
  nlinarith [norm_nonneg ((V.tangentAt x)ᗮ.starProjection
    ((‖x - ξ‖)⁻¹ • (x - ξ)))]

/-- The normal-radial square is measurable for the actual varifold weight.
No continuity of the approximate tangent field is required. -/
theorem radialNormalSq_aemeasurable (ξ : E) :
    AEMeasurable (V.radialNormalSq ξ) V.weight := by
  have hnormal : AEMeasurable (V.normalProjection) V.weight :=
    aemeasurable_const.sub V.tangentProjection_aemeasurable_weight
  have hradial : Measurable (fun x : E ↦ (‖x - ξ‖)⁻¹ • (x - ξ)) := by
    fun_prop
  have h := (ContinuousLinearMap.measurable_apply₂.comp_aemeasurable
    (hnormal.prodMk hradial.aemeasurable)).norm.pow_const 2
  exact h.congr (Filter.Eventually.of_forall fun x ↦ (V.radialNormalSq_eq ξ x).symm)

/-- Pythagoras for the tangential and normal parts of the unnormalized
radial vector. This also holds at the centre without division by zero. -/
theorem tangent_radial_sq_add_normal_radial_sq (ξ x : E) :
    ‖V.tangentProjection x (x - ξ)‖ ^ 2 +
      ‖V.normalProjection x (x - ξ)‖ ^ 2 = ‖x - ξ‖ ^ 2 := by
  rw [V.normalProjection_eq_starProjection_orthogonal]
  exact ((V.tangentAt x).norm_sq_eq_add_norm_sq_starProjection (x - ξ)).symm

/-- Removing the normalization from Simon's `|D^⊥r|²`. -/
theorem norm_normalProjection_radial_sq (ξ x : E) :
    ‖V.normalProjection x (x - ξ)‖ ^ 2 =
      ‖x - ξ‖ ^ 2 * V.radialNormalSq ξ x := by
  rw [V.radialNormalSq_eq, map_smul, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  by_cases hx : x - ξ = 0
  · simp [hx]
  · field_simp [norm_ne_zero_iff.mpr hx]

/-- The projection identity between Simon (4.3.2) and (4.3.3), with the
factor `r²` making it valid at the centre as well. -/
theorem norm_tangentProjection_radial_sq (ξ x : E) :
    ‖V.tangentProjection x (x - ξ)‖ ^ 2 =
      ‖x - ξ‖ ^ 2 * (1 - V.radialNormalSq ξ x) := by
  have h := V.tangent_radial_sq_add_normal_radial_sq ξ x
  rw [V.norm_normalProjection_radial_sq] at h
  nlinarith

/-- The normal-radial form of the pointwise divergence calculation (4.3.2).
With `γ(r)=η(r²)`, its last two terms are precisely
`r γ'(r) (1-|D^⊥r|²)`. -/
theorem tangentialDivergence_squaredRadialVectorField_normal
    (ξ x : E) {η : ℝ → ℝ} {η' : ℝ}
    (hη : HasDerivAt η η' (‖x - ξ‖ ^ 2))
    (hrank : Module.finrank ℝ (V.tangentAt x) = n) :
    V.tangentialDivergence (squaredRadialVectorField ξ η) x =
      n * η (‖x - ξ‖ ^ 2) +
        2 * η' * ‖x - ξ‖ ^ 2 * (1 - V.radialNormalSq ξ x) := by
  rw [V.tangentialDivergence_squaredRadialVectorField ξ x hη hrank,
    V.norm_tangentProjection_radial_sq]
  ring

/-- A radial scalar cutoff has compact support, not merely the radial
vector field to which it gives rise. -/
theorem hasCompactSupport_squaredRadialScalar (ξ : E) {R : ℝ} (hR : 0 ≤ R)
    {η : ℝ → ℝ} (hcutoff : ∀ t, R ^ 2 ≤ t → η t = 0) :
    HasCompactSupport (fun x : E ↦ η (‖x - ξ‖ ^ 2)) := by
  refine (isCompact_closedBall ξ R).of_isClosed_subset (isClosed_tsupport _) ?_
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hxR
  have hr : R < ‖x - ξ‖ := by
    simpa only [mem_closedBall, dist_eq_norm, not_le] using hxR
  exact hx (hcutoff _ (by nlinarith [norm_nonneg (x - ξ)]))

/-- A one-variable cutoff has zero derivative strictly beyond its cutoff
radius. The value at the endpoint is not needed for the support argument. -/
theorem deriv_eq_zero_of_cutoff {η : ℝ → ℝ} {a t : ℝ}
    (hcutoff : ∀ s, a ≤ s → η s = 0) (ht : a < t) : deriv η t = 0 := by
  have hzero : η =ᶠ[𝓝 t] fun _ ↦ 0 := by
    filter_upwards [lt_mem_nhds ht] with s hs
    exact hcutoff s hs.le
  exact hzero.deriv_eq.trans (deriv_const t 0)

/-- The derivative-weighted radial cutoff is compactly supported as well. -/
theorem hasCompactSupport_squaredRadialScalar_deriv (ξ : E) {R : ℝ} (hR : 0 ≤ R)
    {η : ℝ → ℝ} (hcutoff : ∀ t, R ^ 2 ≤ t → η t = 0) :
    HasCompactSupport (fun x : E ↦ deriv η (‖x - ξ‖ ^ 2)) := by
  refine (isCompact_closedBall ξ R).of_isClosed_subset (isClosed_tsupport _) ?_
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hxR
  have hr : R < ‖x - ξ‖ := by
    simpa only [mem_closedBall, dist_eq_norm, not_le] using hxR
  exact hx (deriv_eq_zero_of_cutoff hcutoff (by nlinarith [norm_nonneg (x - ξ)]))

/-- Simon (4.3.3), in the smooth squared-radius parametrization
`γ(r)=η(r²)`. All three terms are genuine integrals: compact support and
local finiteness establish their integrability before splitting the
stationary divergence integral. -/
theorem IsStationaryIn.integral_squaredRadial_normal
    {U : Set E} (hV : V.IsStationaryIn U) (ξ : E)
    {R : ℝ} (hR : 0 ≤ R) (hball : closedBall ξ R ⊆ U)
    {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η)
    (hcutoff : ∀ t, R ^ 2 ≤ t → η t = 0) :
    n * (∫ x, η (‖x - ξ‖ ^ 2) ∂V.weight) +
      (∫ x, 2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2 ∂V.weight) =
      ∫ x, 2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2 *
        V.radialNormalSq ξ x ∂V.weight := by
  have hsq : Continuous (fun x : E ↦ ‖x - ξ‖ ^ 2) := by fun_prop
  have hηint : MeasureTheory.Integrable (fun x ↦ η (‖x - ξ‖ ^ 2)) V.weight :=
    (hη.continuous.comp hsq).integrable_of_hasCompactSupport
      (hasCompactSupport_squaredRadialScalar ξ hR hcutoff)
  have hdint : MeasureTheory.Integrable
      (fun x ↦ 2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2) V.weight :=
    (((hη.continuous_deriv_one.comp hsq).const_mul 2).mul hsq).integrable_of_hasCompactSupport
      (hasCompactSupport_squaredRadialScalar_deriv ξ hR hcutoff).mul_left.mul_right
  have hnint := hdint.mul_bdd (V.radialNormalSq_aemeasurable ξ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ (by
      rw [Real.norm_eq_abs, abs_of_nonneg (V.radialNormalSq_nonneg ξ x)]
      exact V.radialNormalSq_le_one ξ x : ‖V.radialNormalSq ξ x‖ ≤ 1))
  have heq := IsStationaryIn.integral_squaredRadial_eq_zero_of_cutoff
    (V := V) hV ξ hR hball hη
    (fun t ↦ (hη.differentiable (by simp) t).hasDerivAt) hcutoff
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
    (hηint.const_mul n).add hdint
  rw [hpoint, MeasureTheory.integral_sub hsumint hnint,
    MeasureTheory.integral_add (hηint.const_mul n) hdint,
    MeasureTheory.integral_const_mul] at heq
  exact sub_eq_zero.mp heq

/-! ### Differentiation of the scaled cutoff integrals -/

/-- A squared-radius cutoff at scale `ρ`. Thus a profile supported below
`A²` gives a spatial cutoff supported in the ball of radius `ρ A`. -/
def scaledRadialCutoff (ξ : E) (φ : ℝ → ℝ) (ρ : ℝ) (x : E) : ℝ :=
  φ (‖x - ξ‖ ^ 2 / ρ ^ 2)

/-- The scale derivative of `scaledRadialCutoff`. -/
def scaledRadialCutoffDeriv (ξ : E) (φ : ℝ → ℝ) (ρ : ℝ) (x : E) : ℝ :=
  (-2 * ‖x - ξ‖ ^ 2 / ρ ^ 3) * deriv φ (‖x - ξ‖ ^ 2 / ρ ^ 2)

theorem hasDerivAt_scaledRadialCutoff (ξ x : E) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    HasDerivAt (fun t ↦ scaledRadialCutoff ξ φ t x)
      (scaledRadialCutoffDeriv ξ φ ρ x) ρ := by
  have hquot : HasDerivAt (fun t : ℝ ↦ ‖x - ξ‖ ^ 2 / t ^ 2)
      (-2 * ‖x - ξ‖ ^ 2 / ρ ^ 3) ρ := by
    convert (hasDerivAt_const ρ (‖x - ξ‖ ^ 2)).fun_div
      ((hasDerivAt_id ρ).pow 2) (pow_ne_zero 2 hρ) using 1
    · rfl
    · simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
        pow_one, mul_one, zero_mul, zero_sub]
      field_simp
  have h := ((hφ.differentiable (by simp) _).hasDerivAt).comp ρ hquot
  convert h using 1
  · rfl
  · simp only [scaledRadialCutoffDeriv]
    ring

/-- The compact-support version of differentiation under the integral
needed below. The dominating function is constructed, using compactness,
and its integrability uses local finiteness. -/
private theorem hasDerivAt_integral_mul_of_compact
    {F F' : ℝ → E → ℝ} {a b ρ : ℝ} (hρ : ρ ∈ Ioo a b)
    {K : Set E} (hK : IsCompact K)
    (hF : ∀ t, Continuous (F t)) (hF' : ∀ t, Continuous (F' t))
    (hjoint : ContinuousOn (fun p : ℝ × E ↦ F' p.1 p.2) (Icc a b ×ˢ K))
    (hzero : ∀ t ∈ Icc a b, ∀ x ∉ K, F t x = 0)
    (hzero' : ∀ t ∈ Icc a b, ∀ x ∉ K, F' t x = 0)
    (hderiv : ∀ t ∈ Icc a b, ∀ x, HasDerivAt (fun s ↦ F s x) (F' t x) t)
    {q : E → ℝ} {B : ℝ} (hq : MeasureTheory.AEStronglyMeasurable q V.weight)
    (hqb : ∀ x, ‖q x‖ ≤ B) :
    MeasureTheory.Integrable (fun x ↦ F' ρ x * q x) V.weight ∧
      HasDerivAt (fun t ↦ ∫ x, F t x * q x ∂V.weight)
        (∫ x, F' ρ x * q x ∂V.weight) ρ := by
  classical
  have hρcc : ρ ∈ Icc a b := ⟨hρ.1.le, hρ.2.le⟩
  have hsupport : HasCompactSupport (F ρ) :=
    HasCompactSupport.of_support_subset_isCompact hK (by
      intro x hx
      by_contra hxK
      exact hx (hzero ρ hρcc x hxK))
  have hFint := ((hF ρ).integrable_of_hasCompactSupport hsupport).mul_bdd hq
    (Filter.Eventually.of_forall hqb)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hjoint
  let bound : E → ℝ := K.indicator (fun _ ↦ max C 0 * B)
  have hboundint : MeasureTheory.Integrable bound V.weight :=
    (MeasureTheory.integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x ↦ F t x * q x) (F' := fun t x ↦ F' t x * q x)
    (Icc_mem_nhds hρ.1 hρ.2)
    (Filter.Eventually.of_forall fun t ↦ (hF t).aestronglyMeasurable.mul hq)
    hFint ((hF' ρ).aestronglyMeasurable.mul hq) ?_ hboundint ?_
  · filter_upwards with x
    intro t ht
    by_cases hx : x ∈ K
    · simp only [bound, indicator_of_mem hx, norm_mul]
      exact mul_le_mul ((hC (t, x) ⟨ht, hx⟩).trans (le_max_left C 0))
        (hqb x) (norm_nonneg _) (le_max_right C 0)
    · simp [bound, hx, hzero' t ht x hx]
  · filter_upwards with x
    intro t ht
    exact (hderiv t ht x).mul_const (q x)

/-- Differentiation of either Simon's `I` or `J` under the integral sign.
Taking `q=1` gives `I`; taking `q=|D^⊥r|²` gives `J`. The hypotheses on
`q` are just measurability and the pointwise bound, and the analytic
domination is derived from the cutoff and the locally finite weight. -/
theorem hasDerivAt_integral_scaledRadialCutoff_mul
    (ξ : E) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {A : ℝ} (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0)
    {ρ : ℝ} (hρ : 0 < ρ) {q : E → ℝ} {B : ℝ}
    (hq : MeasureTheory.AEStronglyMeasurable q V.weight) (hqb : ∀ x, ‖q x‖ ≤ B) :
    MeasureTheory.Integrable (fun x ↦ scaledRadialCutoffDeriv ξ φ ρ x * q x) V.weight ∧
      HasDerivAt (fun t ↦ ∫ x, scaledRadialCutoff ξ φ t x * q x ∂V.weight)
        (∫ x, scaledRadialCutoffDeriv ξ φ ρ x * q x ∂V.weight) ρ := by
  let K : Set E := closedBall ξ (2 * ρ * A)
  have hscale : ∀ t ∈ Icc (ρ / 2) (2 * ρ), 0 < t := by
    intro t ht
    linarith [ht.1]
  have hout : ∀ t ∈ Icc (ρ / 2) (2 * ρ), ∀ x ∉ K,
      A ^ 2 < ‖x - ξ‖ ^ 2 / t ^ 2 := by
    intro t ht x hx
    have hx' : 2 * ρ * A < ‖x - ξ‖ := by
      simpa only [K, mem_closedBall, dist_eq_norm, not_le] using hx
    have htx : t * A < ‖x - ξ‖ :=
      (mul_le_mul_of_nonneg_right ht.2 hA.le).trans_lt hx'
    apply (lt_div_iff₀ (sq_pos_of_pos (hscale t ht))).mpr
    nlinarith [sq_nonneg (‖x - ξ‖ + t * A),
      mul_pos (sub_pos.mpr htx)
        (add_pos_of_nonneg_of_pos (norm_nonneg (x - ξ)) (mul_pos (hscale t ht) hA))]
  refine hasDerivAt_integral_mul_of_compact V
    (F := scaledRadialCutoff ξ φ) (F' := scaledRadialCutoffDeriv ξ φ) (K := K)
    (show ρ ∈ Ioo (ρ / 2) (2 * ρ) by constructor <;> linarith)
    (isCompact_closedBall ξ (2 * ρ * A))
    (fun t ↦ hφ.continuous.comp (by fun_prop))
    (fun t ↦ by
      have hd := hφ.continuous_deriv_one
      change Continuous (fun x : E ↦
        (-2 * ‖x - ξ‖ ^ 2 / t ^ 3) * deriv φ (‖x - ξ‖ ^ 2 / t ^ 2))
      fun_prop)
    ?_ ?_ ?_ ?_ hq hqb
  · dsimp [scaledRadialCutoffDeriv]
    have hnorm : ContinuousOn (fun p : ℝ × E ↦ ‖p.2 - ξ‖ ^ 2)
        (Icc (ρ / 2) (2 * ρ) ×ˢ K) := by fun_prop
    have hnonzero : ∀ p ∈ Icc (ρ / 2) (2 * ρ) ×ˢ K, p.1 ≠ 0 :=
      fun p hp ↦ (hscale p.1 hp.1).ne'
    exact ((continuousOn_const.mul hnorm).div (continuousOn_fst.pow 3)
      (fun p hp ↦ pow_ne_zero 3 (hnonzero p hp))).mul
      (hφ.continuous_deriv_one.continuousOn.comp
        (hnorm.div (continuousOn_fst.pow 2) (fun p hp ↦ pow_ne_zero 2 (hnonzero p hp)))
        (fun _ _ ↦ mem_univ _))
  · intro t ht x hx
    exact hcutoff _ (hout t ht x hx).le
  · intro t ht x hx
    simp [scaledRadialCutoffDeriv, deriv_eq_zero_of_cutoff hcutoff (hout t ht x hx)]
  · intro t ht x
    exact hasDerivAt_scaledRadialCutoff ξ x hφ (hscale t ht).ne'

/-- Simon's cutoff mass `I(ρ)`, with squared-radius profile. -/
def cutoffMass (ξ : E) (φ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  ∫ x, scaledRadialCutoff ξ φ ρ x ∂V.weight

/-- Simon's normal-weighted cutoff mass `J(ρ)`. -/
def cutoffNormalMass (ξ : E) (φ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  ∫ x, scaledRadialCutoff ξ φ ρ x * V.radialNormalSq ξ x ∂V.weight

theorem hasDerivAt_cutoffMass (ξ : E) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {A : ℝ} (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0)
    {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (V.cutoffMass ξ φ)
      (∫ x, scaledRadialCutoffDeriv ξ φ ρ x ∂V.weight) ρ := by
  change HasDerivAt (fun t ↦ ∫ x, scaledRadialCutoff ξ φ t x ∂V.weight) _ _
  simpa only [mul_one, cutoffMass] using
    (V.hasDerivAt_integral_scaledRadialCutoff_mul ξ hφ hA hcutoff hρ
      (q := fun _ ↦ 1) (B := 1) MeasureTheory.aestronglyMeasurable_const
      (fun _ ↦ by simp)).2

theorem hasDerivAt_cutoffNormalMass (ξ : E) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {A : ℝ} (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0)
    {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (V.cutoffNormalMass ξ φ)
      (∫ x, scaledRadialCutoffDeriv ξ φ ρ x * V.radialNormalSq ξ x ∂V.weight) ρ := by
  exact (V.hasDerivAt_integral_scaledRadialCutoff_mul ξ hφ hA hcutoff hρ
    (V.radialNormalSq_aemeasurable ξ).aestronglyMeasurable (fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (V.radialNormalSq_nonneg ξ x)]
      exact V.radialNormalSq_le_one ξ x)).2

/-- The identity `nI - ρI' = -ρJ'` immediately preceding Simon (4.3.4).
Both derivatives are computed from the actual integrals, not supplied as
additional hypotheses. -/
theorem IsStationaryIn.cutoffMass_deriv_identity
    {U : Set E} (hV : V.IsStationaryIn U) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    n * V.cutoffMass ξ φ ρ - ρ * deriv (V.cutoffMass ξ φ) ρ =
      -ρ * deriv (V.cutoffNormalMass ξ φ) ρ := by
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
  have heq := IsStationaryIn.integral_squaredRadial_normal (V := V) hV ξ
    (mul_pos hρ hA).le hball hη hηcutoff
  have hpoint : ∀ x : E, 2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2 =
      -ρ * scaledRadialCutoffDeriv ξ φ ρ x := by
    intro x
    rw [hηderiv, scaledRadialCutoffDeriv]
    field_simp
  simp_rw [hpoint, mul_assoc (-ρ), MeasureTheory.integral_const_mul] at heq
  rw [(V.hasDerivAt_cutoffMass ξ hφ hA hcutoff hρ).deriv,
    (V.hasDerivAt_cutoffNormalMass ξ hφ hA hcutoff hρ).deriv]
  simpa only [cutoffMass, scaledRadialCutoff, η, neg_mul, ← sub_eq_add_neg] using heq

/-- Simon (4.3.4): the scale derivative of the normalized cutoff mass is
the correspondingly normalized derivative of the normal-weighted cutoff
mass. This theorem derives the full identity from stationarity. -/
theorem IsStationaryIn.hasDerivAt_normalizedCutoffMass
    {U : Set E} (hV : V.IsStationaryIn U) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    HasDerivAt (fun t ↦ V.cutoffMass ξ φ t / t ^ n)
      ((∫ x, scaledRadialCutoffDeriv ξ φ ρ x * V.radialNormalSq ξ x ∂V.weight) /
        ρ ^ n) ρ := by
  have hI := V.hasDerivAt_cutoffMass ξ hφ hA hcutoff hρ
  have hJ := V.hasDerivAt_cutoffNormalMass ξ hφ hA hcutoff hρ
  have hrel := IsStationaryIn.cutoffMass_deriv_identity (V := V) hV ξ
    hφ hA hcutoff hρ hball
  rw [hI.deriv, hJ.deriv] at hrel
  have hp : HasDerivAt (fun t : ℝ ↦ t ^ n) (n * ρ ^ n / ρ) ρ := by
    convert (hasDerivAt_id ρ).pow n using 1
    · rfl
    · cases n with
      | zero => simp
      | succ m => simp [pow_succ, hρ.ne', mul_div_assoc]
  convert hI.fun_div hp (pow_ne_zero n hρ.ne') using 1
  · field_simp
    linear_combination hrel

/-! ### The smooth cutoffs and their closed-ball limit -/

/-- A concrete smooth family decreasing towards the indicator of
`(-∞,1]` as `ε ↓ 0`, as required in the passage from (4.3.5) to (4.3.6).
It is a profile in the squared radius. -/
def monotonicityCutoff (ε t : ℝ) : ℝ :=
  1 - Real.smoothTransition ((t - 1) / ε)

theorem contDiff_monotonicityCutoff (ε : ℝ) :
    ContDiff ℝ 1 (monotonicityCutoff ε) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const ε))

theorem monotonicityCutoff_mem_Icc (ε t : ℝ) :
    monotonicityCutoff ε t ∈ Icc 0 1 := by
  constructor <;> dsimp [monotonicityCutoff]
  · linarith [Real.smoothTransition.le_one ((t - 1) / ε)]
  · linarith [Real.smoothTransition.nonneg ((t - 1) / ε)]

theorem monotonicityCutoff_antitone {ε : ℝ} (hε : 0 < ε) :
    Antitone (monotonicityCutoff ε) := by
  intro s t hst
  have h := Real.smoothTransition.monotone
    (div_le_div_of_nonneg_right (sub_le_sub_right hst 1) hε.le)
  dsimp [monotonicityCutoff]
  linarith

theorem monotonicityCutoff_one {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ 1) :
    monotonicityCutoff ε t = 1 := by
  rw [monotonicityCutoff, Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hε.le), sub_zero]

theorem monotonicityCutoff_zero {ε t : ℝ} (hε : 0 < ε) (ht : 1 + ε ≤ t) :
    monotonicityCutoff ε t = 0 := by
  rw [monotonicityCutoff, Real.smoothTransition.one_of_one_le
    ((one_le_div hε).mpr (by linarith)), sub_self]

theorem monotonicityCutoff_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∀ t, (1 + ε) ^ 2 ≤ t → monotonicityCutoff ε t = 0 := by
  intro t ht
  apply monotonicityCutoff_zero hε
  nlinarith [sq_nonneg ε]

theorem deriv_monotonicityCutoff_eq_zero_below_one {ε t : ℝ}
    (hε : 0 < ε) (ht : t < 1) : deriv (monotonicityCutoff ε) t = 0 := by
  have heq : monotonicityCutoff ε =ᶠ[𝓝 t] fun _ ↦ 1 := by
    filter_upwards [gt_mem_nhds ht] with s hs
    exact monotonicityCutoff_one hε hs.le
  exact heq.deriv_eq.trans (deriv_const t 1)

theorem tendsto_monotonicityCutoff (t : ℝ) :
    Tendsto (fun ε ↦ monotonicityCutoff ε t) (𝓝[>] (0 : ℝ))
      (𝓝 ((Iic 1).indicator (fun _ : ℝ ↦ 1) t)) := by
  classical
  by_cases ht : t ≤ 1
  · simp only [indicator_apply, mem_Iic, ht, ite_true]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (monotonicityCutoff_one hε ht).symm
  · simp only [indicator_apply, mem_Iic, ht, ite_false]
    apply tendsto_const_nhds.congr'
    have hδ : 0 < t - 1 := by linarith
    filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds hδ).filter_mono inf_le_left] with ε hε hsmall
    exact (monotonicityCutoff_zero hε (by linarith)).symm

theorem tendsto_scaledRadialCutoff (ξ x : E) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun ε ↦ scaledRadialCutoff ξ (monotonicityCutoff ε) ρ x)
      (𝓝[>] (0 : ℝ)) (𝓝 ((closedBall ξ ρ).indicator (fun _ : E ↦ 1) x)) := by
  have hmem : ‖x - ξ‖ ^ 2 / ρ ^ 2 ≤ 1 ↔ x ∈ closedBall ξ ρ := by
    rw [div_le_one (sq_pos_of_pos hρ), mem_closedBall, dist_eq_norm]
    exact sq_le_sq₀ (norm_nonneg _) hρ.le
  have heq : (Iic 1).indicator (fun _ : ℝ ↦ (1 : ℝ)) (‖x - ξ‖ ^ 2 / ρ ^ 2) =
      (closedBall ξ ρ).indicator (fun _ : E ↦ (1 : ℝ)) x := by
    classical
    by_cases hx : x ∈ closedBall ξ ρ
    · rw [indicator_of_mem (show ‖x - ξ‖ ^ 2 / ρ ^ 2 ∈ Iic 1 from hmem.mpr hx),
        indicator_of_mem hx]
    · rw [indicator_of_notMem (show ‖x - ξ‖ ^ 2 / ρ ^ 2 ∉ Iic 1 from
        fun h ↦ hx (hmem.mp h)), indicator_of_notMem hx]
  rw [← heq]
  exact tendsto_monotonicityCutoff (‖x - ξ‖ ^ 2 / ρ ^ 2)

/-- The dominated cutoff limit for any bounded measurable weight. In
particular this applies to the constant weight and to the truncated tilt
weight used in the annular identity. The limit includes the boundary
sphere, exactly as in Simon's closed-ball convention. -/
theorem tendsto_integral_scaledRadialCutoff_mul (ξ : E) {ρ : ℝ} (hρ : 0 < ρ)
    {q : E → ℝ} {B : ℝ} (hq : MeasureTheory.AEStronglyMeasurable q V.weight)
    (hqb : ∀ x, ‖q x‖ ≤ B) :
    Tendsto (fun ε ↦ ∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) ρ x * q x ∂V.weight)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in closedBall ξ ρ, q x ∂V.weight)) := by
  classical
  let bound : E → ℝ := (closedBall ξ (2 * ρ)).indicator (fun _ ↦ B)
  have hboundint : MeasureTheory.Integrable bound V.weight :=
    (MeasureTheory.integrableOn_const (C := B)
      (isCompact_closedBall ξ (2 * ρ)).measure_lt_top.ne).integrable_indicator measurableSet_closedBall
  rw [← MeasureTheory.integral_indicator measurableSet_closedBall]
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hboundint ?_
  · exact Filter.Eventually.of_forall fun ε ↦
      (((contDiff_monotonicityCutoff ε).continuous.comp
        (show Continuous (fun x : E ↦ ‖x - ξ‖ ^ 2 / ρ ^ 2) by fun_prop)).aestronglyMeasurable.mul hq)
  · filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left] with ε hε hεone
    filter_upwards with x
    by_cases hx : x ∈ closedBall ξ (2 * ρ)
    · rw [show bound x = B by simp [bound, hx], norm_mul]
      have hcut := monotonicityCutoff_mem_Icc ε (‖x - ξ‖ ^ 2 / ρ ^ 2)
      have hnorm : ‖scaledRadialCutoff ξ (monotonicityCutoff ε) ρ x‖ ≤ 1 := by
        rw [scaledRadialCutoff, Real.norm_eq_abs, abs_of_nonneg hcut.1]
        exact hcut.2
      calc
        ‖scaledRadialCutoff ξ (monotonicityCutoff ε) ρ x‖ * ‖q x‖ ≤ 1 * ‖q x‖ :=
          mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
        _ ≤ B := by simpa using hqb x
    · have hr : 2 * ρ < ‖x - ξ‖ := by
        simpa only [mem_closedBall, dist_eq_norm, not_le] using hx
      have hsquare : (2 * ρ) ^ 2 < ‖x - ξ‖ ^ 2 :=
        (sq_lt_sq₀ (by positivity) (norm_nonneg _)).mpr hr
      have harg : 1 + ε ≤ ‖x - ξ‖ ^ 2 / ρ ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
        nlinarith [mul_nonneg (by linarith : 0 ≤ 3 - ε) (sq_nonneg ρ)]
      simp [bound, hx, scaledRadialCutoff, monotonicityCutoff_zero hε harg]
  · filter_upwards with x
    convert (tendsto_scaledRadialCutoff ξ x hρ).mul_const (q x) using 1
    by_cases hx : x ∈ closedBall ξ ρ <;> simp [hx]

/-- The cutoff masses converge to the mass of Simon's closed ball. -/
theorem tendsto_cutoffMass (ξ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun ε ↦ V.cutoffMass ξ (monotonicityCutoff ε) ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 (V.weight.real (closedBall ξ ρ))) := by
  simpa only [cutoffMass, mul_one, MeasureTheory.setIntegral_const, smul_eq_mul, mul_one] using
    V.tendsto_integral_scaledRadialCutoff_mul ξ hρ
      (q := fun _ ↦ 1) (B := 1) MeasureTheory.aestronglyMeasurable_const (fun _ ↦ by simp)

/-- A bounded version of the defect weight. On an annulus whose inner
radius is `c>0`, it agrees exactly with `|D^⊥r|²/rⁿ`. -/
def truncatedRadialDefect (ξ : E) (c : ℝ) (x : E) : ℝ :=
  V.radialNormalSq ξ x / (max c ‖x - ξ‖) ^ n

theorem truncatedRadialDefect_aemeasurable (ξ : E) (c : ℝ) :
    AEMeasurable (V.truncatedRadialDefect ξ c) V.weight :=
  (V.radialNormalSq_aemeasurable ξ).div (by fun_prop)

theorem norm_truncatedRadialDefect_le (ξ : E) {c : ℝ} (hc : 0 < c) (x : E) :
    ‖V.truncatedRadialDefect ξ c x‖ ≤ (c ^ n)⁻¹ := by
  have hm : 0 < max c ‖x - ξ‖ := hc.trans_le (le_max_left _ _)
  rw [truncatedRadialDefect, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (V.radialNormalSq_nonneg ξ x) (pow_pos hm n).le), ← one_div]
  apply (div_le_div_iff₀ (pow_pos hm n) (pow_pos hc n)).mpr
  calc
    V.radialNormalSq ξ x * c ^ n ≤ 1 * c ^ n :=
      mul_le_mul_of_nonneg_right (V.radialNormalSq_le_one ξ x) (pow_pos hc n).le
    _ ≤ 1 * max c ‖x - ξ‖ ^ n := by
      gcongr
      exact le_max_left _ _

theorem scaledRadialCutoffDeriv_nonneg (ξ x : E) {φ : ℝ → ℝ}
    (hφ : Antitone φ) {ρ : ℝ} (hρ : 0 < ρ) :
    0 ≤ scaledRadialCutoffDeriv ξ φ ρ x := by
  apply mul_nonneg_of_nonpos_of_nonpos _ hφ.deriv_nonpos
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)) (pow_pos hρ 3).le

/-- The derivative of Simon's cutoff is supported where `ρ≤r≤(1+ε)ρ`. -/
theorem scaledRadialCutoffDeriv_support (ξ x : E) {ε ρ : ℝ}
    (hε : 0 < ε) (hρ : 0 < ρ)
    (hne : scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) ρ x ≠ 0) :
    ρ ≤ ‖x - ξ‖ ∧ ‖x - ξ‖ ≤ (1 + ε) * ρ := by
  constructor
  · by_contra h
    have hr : ‖x - ξ‖ < ρ := lt_of_not_ge h
    have ht : ‖x - ξ‖ ^ 2 / ρ ^ 2 < 1 := by
      rw [div_lt_one (sq_pos_of_pos hρ)]
      exact (sq_lt_sq₀ (norm_nonneg _) hρ.le).mpr hr
    exact hne (by simp [scaledRadialCutoffDeriv,
      deriv_monotonicityCutoff_eq_zero_below_one hε ht])
  · by_contra h
    have hr : (1 + ε) * ρ < ‖x - ξ‖ := lt_of_not_ge h
    have ht : (1 + ε) ^ 2 < ‖x - ξ‖ ^ 2 / ρ ^ 2 := by
      apply (lt_div_iff₀ (sq_pos_of_pos hρ)).mpr
      have hs := (sq_lt_sq₀ (by positivity) (norm_nonneg _)).mpr hr
      nlinarith [hs]
    exact hne (by simp [scaledRadialCutoffDeriv,
      deriv_eq_zero_of_cutoff (monotonicityCutoff_cutoff hε) ht])

/-- The correct pointwise squeeze for the source's outward cutoff:
`r⁻ⁿ ≤ ρ⁻ⁿ ≤ (1+ε)ⁿ r⁻ⁿ` on its scale-derivative support.
The factors in the displayed source (4.3.5) are reversed; these are the
valid bounds for the stated cutoff, with the same limit as `ε↓0`. -/
theorem scaledRadialCutoffDeriv_defect_bounds (ξ x : E) {ε c ρ : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hcρ : c ≤ ρ) :
    scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) ρ x * V.truncatedRadialDefect ξ c x ≤
        (scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) ρ x * V.radialNormalSq ξ x) / ρ ^ n ∧
      (scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) ρ x * V.radialNormalSq ξ x) / ρ ^ n ≤
        (1 + ε) ^ n *
          (scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) ρ x * V.truncatedRadialDefect ξ c x) := by
  by_cases hz : scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) ρ x = 0
  · simp [hz]
  have hρ : 0 < ρ := hc.trans_le hcρ
  obtain ⟨hrlo, hrhi⟩ := scaledRadialCutoffDeriv_support ξ x hε hρ hz
  have hr : 0 < ‖x - ξ‖ := hρ.trans_le hrlo
  have hpowlo := pow_le_pow_left₀ hρ.le hrlo n
  have hpowhi := pow_le_pow_left₀ (norm_nonneg (x - ξ)) hrhi n
  rw [mul_pow] at hpowhi
  have hzpos : 0 ≤ scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) ρ x *
      V.radialNormalSq ξ x :=
    mul_nonneg (scaledRadialCutoffDeriv_nonneg ξ x (monotonicityCutoff_antitone hε) hρ)
      (V.radialNormalSq_nonneg ξ x)
  rw [truncatedRadialDefect, max_eq_right (hcρ.trans hrlo), ← mul_div_assoc,
    ← mul_div_assoc]
  constructor
  · exact (div_le_div_iff₀ (pow_pos hr n) (pow_pos hρ n)).mpr
      (mul_le_mul_of_nonneg_left hpowlo hzpos)
  · apply (div_le_div_iff₀ (pow_pos hρ n) (pow_pos hr n)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hpowhi hzpos]

/-- Integrating a derivative comparison on a compact interval. This is
the one-dimensional mean-value form of the integration step in (4.3.5). -/
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

/-- The integrated cutoff squeeze used to prove (4.3.6). This is the
corrected prefactor version of (4.3.5) for the source's stated outward
cutoff: `G(ρ)-G(σ) ≤ F(ρ)-F(σ) ≤ (1+ε)ⁿ(G(ρ)-G(σ))`.
Here `F=ρ⁻ⁿI` and `G` uses the bounded defect weight; it agrees with the
untruncated weight wherever the scale derivative is nonzero. -/
theorem IsStationaryIn.cutoff_squeeze
    {U : Set E} (hV : V.IsStationaryIn U) (ξ : E) {ε σ ρ : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hσρ : σ ≤ ρ)
    (hball : closedBall ξ (ρ * (1 + ε)) ⊆ U) :
    let G := fun t ↦ ∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) t x *
      V.truncatedRadialDefect ξ σ x ∂V.weight
    G ρ - G σ ≤ V.cutoffMass ξ (monotonicityCutoff ε) ρ / ρ ^ n -
      V.cutoffMass ξ (monotonicityCutoff ε) σ / σ ^ n ∧
    V.cutoffMass ξ (monotonicityCutoff ε) ρ / ρ ^ n -
      V.cutoffMass ξ (monotonicityCutoff ε) σ / σ ^ n ≤ (1 + ε) ^ n * (G ρ - G σ) := by
  let q := V.truncatedRadialDefect ξ σ
  let G := fun t ↦ ∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) t x * q x ∂V.weight
  let G' := fun t ↦ ∫ x, scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) t x * q x ∂V.weight
  let F := fun t ↦ V.cutoffMass ξ (monotonicityCutoff ε) t / t ^ n
  let F' := fun t ↦ (∫ x, scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) t x *
    V.radialNormalSq ξ x ∂V.weight) / t ^ n
  have hA : 0 < 1 + ε := by linarith
  have hG : ∀ t ∈ Icc σ ρ, HasDerivAt G (G' t) t := by
    intro t ht
    exact (V.hasDerivAt_integral_scaledRadialCutoff_mul ξ (contDiff_monotonicityCutoff ε)
      hA (monotonicityCutoff_cutoff hε) (hσ.trans_le ht.1)
      (V.truncatedRadialDefect_aemeasurable ξ σ).aestronglyMeasurable
      (V.norm_truncatedRadialDefect_le ξ hσ)).2
  have hF : ∀ t ∈ Icc σ ρ, HasDerivAt F (F' t) t := by
    intro t ht
    apply IsStationaryIn.hasDerivAt_normalizedCutoffMass (V := V) hV ξ
      (contDiff_monotonicityCutoff ε) hA (monotonicityCutoff_cutoff hε) (hσ.trans_le ht.1)
    exact (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right ht.2 hA.le)).trans hball
  have hbounds : ∀ t ∈ Icc σ ρ, G' t ≤ F' t ∧ F' t ≤ (1 + ε) ^ n * G' t := by
    intro t ht
    have hgint := (V.hasDerivAt_integral_scaledRadialCutoff_mul ξ
      (contDiff_monotonicityCutoff ε) hA (monotonicityCutoff_cutoff hε) (hσ.trans_le ht.1)
      (V.truncatedRadialDefect_aemeasurable ξ σ).aestronglyMeasurable
      (V.norm_truncatedRadialDefect_le ξ hσ)).1
    have hfint := (V.hasDerivAt_integral_scaledRadialCutoff_mul ξ
      (contDiff_monotonicityCutoff ε) hA (monotonicityCutoff_cutoff hε) (hσ.trans_le ht.1)
      (V.radialNormalSq_aemeasurable ξ).aestronglyMeasurable (fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (V.radialNormalSq_nonneg ξ x)]
        exact V.radialNormalSq_le_one ξ x)).1
    constructor
    · simpa only [G', F', q, MeasureTheory.integral_div] using
        MeasureTheory.integral_mono hgint (hfint.div_const (t ^ n))
          (fun x ↦ (V.scaledRadialCutoffDeriv_defect_bounds ξ x hε hσ ht.1).1)
    · simpa only [G', F', q, MeasureTheory.integral_div, MeasureTheory.integral_const_mul] using
        MeasureTheory.integral_mono (hfint.div_const (t ^ n)) (hgint.const_mul ((1 + ε) ^ n))
          (fun x ↦ (V.scaledRadialCutoffDeriv_defect_bounds ξ x hε hσ ht.1).2)
  constructor
  · exact sub_le_sub_of_hasDerivAt_le hσρ hG hF (fun t ht ↦ (hbounds t ht).1)
  · have h := sub_le_sub_of_hasDerivAt_le hσρ hF
      (fun t ht ↦ (hG t ht).const_mul ((1 + ε) ^ n)) (fun t ht ↦ (hbounds t ht).2)
    simpa only [mul_sub] using h

/-- The truncated tilt weight is integrable on every compact ball, by its
explicit bound and the local finiteness of the varifold weight. -/
theorem integrableOn_truncatedRadialDefect (ξ : E) {c : ℝ} (hc : 0 < c) (ρ : ℝ) :
    MeasureTheory.IntegrableOn (V.truncatedRadialDefect ξ c) (closedBall ξ ρ) V.weight := by
  apply (MeasureTheory.integrableOn_const (C := (c ^ n)⁻¹)
    (isCompact_closedBall ξ ρ).measure_lt_top.ne).mono'
  · exact (V.truncatedRadialDefect_aemeasurable ξ c).aestronglyMeasurable.mono_measure
      MeasureTheory.Measure.restrict_le_self
  · exact Filter.Eventually.of_forall (V.norm_truncatedRadialDefect_le ξ hc)

/-- On a positive-inner-radius annulus, the actual defect integrand is
integrable. In particular its nonnegative integral is finite. -/
theorem integrableOn_radialDefect_annulus (ξ : E) {σ : ℝ} (hσ : 0 < σ) (ρ : ℝ) :
    MeasureTheory.IntegrableOn (fun x ↦ V.radialNormalSq ξ x / ‖x - ξ‖ ^ n)
      (closedBall ξ ρ \ closedBall ξ σ) V.weight := by
  apply ((V.integrableOn_truncatedRadialDefect ξ hσ ρ).mono_set sdiff_subset).congr_fun _
    (measurableSet_closedBall.diff measurableSet_closedBall)
  intro x hx
  have hr : σ < ‖x - ξ‖ := by
    simpa only [mem_closedBall, dist_eq_norm, not_le] using hx.2
  simp only [truncatedRadialDefect, max_eq_right hr.le]

/-- Simon (4.3.6), as an equality of finite real integrals, obtained by
letting the smooth cutoff width tend to zero in the corrected squeeze.
No monotonicity predicate or radial integral identity is assumed. -/
theorem IsStationaryIn.stationaryMonotonicity_real
    {U : Set E} (hV : V.IsStationaryIn U) (ξ : E) {R σ ρ : ℝ}
    (hball : closedBall ξ R ⊆ U) (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hρR : ρ < R) :
    V.weight.real (closedBall ξ ρ) / ρ ^ n - V.weight.real (closedBall ξ σ) / σ ^ n =
      ∫ x in closedBall ξ ρ \ closedBall ξ σ,
        V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight := by
  have hρ : 0 < ρ := hσ.trans_le hσρ
  let q := V.truncatedRadialDefect ξ σ
  let G := fun ε t ↦ ∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) t x * q x ∂V.weight
  have hGρ := V.tendsto_integral_scaledRadialCutoff_mul ξ hρ
    (V.truncatedRadialDefect_aemeasurable ξ σ).aestronglyMeasurable
    (V.norm_truncatedRadialDefect_le ξ hσ)
  have hGσ := V.tendsto_integral_scaledRadialCutoff_mul ξ hσ
    (V.truncatedRadialDefect_aemeasurable ξ σ).aestronglyMeasurable
    (V.norm_truncatedRadialDefect_le ξ hσ)
  have hGlim : Tendsto (fun ε ↦ G ε ρ - G ε σ) (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ x in closedBall ξ ρ, q x ∂V.weight) -
        ∫ x in closedBall ξ σ, q x ∂V.weight)) := hGρ.sub hGσ
  have hFlim := ((V.tendsto_cutoffMass ξ hρ).div_const (ρ ^ n)).sub
    ((V.tendsto_cutoffMass ξ hσ).div_const (σ ^ n))
  have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hsum : Tendsto (fun ε : ℝ ↦ 1 + ε) (𝓝[>] (0 : ℝ)) (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add hid
  have hAlim : Tendsto (fun ε : ℝ ↦ (1 + ε) ^ n) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [add_zero, one_pow] using hsum.pow n
  have hscale : Tendsto (fun ε : ℝ ↦ ρ * (1 + ε)) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    simpa only [add_zero, mul_one] using hsum.const_mul ρ
  have hsqueeze : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      G ε ρ - G ε σ ≤ V.cutoffMass ξ (monotonicityCutoff ε) ρ / ρ ^ n -
        V.cutoffMass ξ (monotonicityCutoff ε) σ / σ ^ n ∧
      V.cutoffMass ξ (monotonicityCutoff ε) ρ / ρ ^ n -
        V.cutoffMass ξ (monotonicityCutoff ε) σ / σ ^ n ≤
          (1 + ε) ^ n * (G ε ρ - G ε σ) := by
    filter_upwards [self_mem_nhdsWithin, hscale.eventually (gt_mem_nhds hρR)] with ε hε hεR
    exact IsStationaryIn.cutoff_squeeze (V := V) hV ξ hε hσ hσρ
      ((closedBall_subset_closedBall hεR.le).trans hball)
  have heq : V.weight.real (closedBall ξ ρ) / ρ ^ n -
        V.weight.real (closedBall ξ σ) / σ ^ n =
      (∫ x in closedBall ξ ρ, q x ∂V.weight) - ∫ x in closedBall ξ σ, q x ∂V.weight := by
    apply le_antisymm
    · simpa only [one_mul] using
        le_of_tendsto_of_tendsto hFlim (hAlim.mul hGlim) (hsqueeze.mono fun _ h ↦ h.2)
    · exact le_of_tendsto_of_tendsto hGlim hFlim (hsqueeze.mono fun _ h ↦ h.1)
  rw [← MeasureTheory.setIntegral_sdiff measurableSet_closedBall
    (V.integrableOn_truncatedRadialDefect ξ hσ ρ) (closedBall_subset_closedBall hσρ)] at heq
  rw [heq]
  apply MeasureTheory.setIntegral_congr_fun (measurableSet_closedBall.diff measurableSet_closedBall)
  intro x hx
  have hr : σ < ‖x - ξ‖ := by
    simpa only [mem_closedBall, dist_eq_norm, not_le] using hx.2
  simp only [truncatedRadialDefect, max_eq_right hr.le]

/-- The normalized ball-mass ratio in Simon (4.3.6), without the optional
normalizing factor `ωₙ`. Simon's notation `Bρ` denotes a **closed** ball
(Notation, PDF object 5); in particular no sphere-nullness is presumed. -/
def normalizedBallMass (ξ : E) (ρ : ℝ) : ℝ≥0∞ :=
  V.weight (closedBall ξ ρ) / ENNReal.ofReal (ρ ^ n)

/-- At every positive radius the normalized ball mass is finite.  This uses
the local finiteness carried by a rectifiable varifold. -/
theorem normalizedBallMass_ne_top (ξ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    V.normalizedBallMass ξ ρ ≠ ⊤ := by
  apply ENNReal.div_ne_top (isCompact_closedBall ξ ρ).measure_lt_top.ne
  exact (ENNReal.ofReal_pos.mpr (pow_pos hρ n)).ne'

/-- The nonnegative annular tilt term on the right side of Simon (4.3.6). -/
def monotonicityDefect (ξ : E) (σ ρ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in closedBall ξ ρ \ closedBall ξ σ,
    ENNReal.ofReal (V.radialNormalSq ξ x / ‖x - ξ‖ ^ n) ∂V.weight

/-- The fundamental identity (4.3.6), specialized to the actual weight and
tangent planes of `V`. It is a proved consequence of `IsStationaryIn`
below, not an assumption in the definition of a rectifiable varifold. -/
def SatisfiesStationaryMonotonicity (ξ : E) (R : ℝ) : Prop :=
  ∀ ⦃σ ρ : ℝ⦄, 0 < σ → σ ≤ ρ → ρ < R →
    V.normalizedBallMass ξ σ + V.monotonicityDefect ξ σ ρ =
      V.normalizedBallMass ξ ρ

theorem ofReal_normalizedBallMass_real (ξ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    ENNReal.ofReal (V.weight.real (closedBall ξ ρ) / ρ ^ n) =
      V.normalizedBallMass ξ ρ := by
  rw [normalizedBallMass, ENNReal.ofReal_div_of_pos (pow_pos hρ n),
    MeasureTheory.measureReal_def, ENNReal.ofReal_toReal (isCompact_closedBall ξ ρ).measure_lt_top.ne]

/-- Simon's fundamental stationary monotonicity theorem (4.3.6), with the
exact closed-ball annulus and normal-radial defect. Its hypotheses are
stationarity and the source's enclosing ball inside the domain. -/
theorem IsStationaryIn.satisfiesStationaryMonotonicity
    {U : Set E} (hV : V.IsStationaryIn U) (ξ : E) {R : ℝ}
    (hball : closedBall ξ R ⊆ U) : V.SatisfiesStationaryMonotonicity ξ R := by
  intro σ ρ hσ hσρ hρR
  have hρ : 0 < ρ := hσ.trans_le hσρ
  have heq := IsStationaryIn.stationaryMonotonicity_real (V := V) hV ξ hball hσ hσρ hρR
  have hnonneg : ∀ x : E, 0 ≤ V.radialNormalSq ξ x / ‖x - ξ‖ ^ n :=
    fun x ↦ div_nonneg (V.radialNormalSq_nonneg ξ x) (pow_nonneg (norm_nonneg _) n)
  have hintnonneg : 0 ≤ ∫ x in closedBall ξ ρ \ closedBall ξ σ,
      V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight :=
    MeasureTheory.integral_nonneg hnonneg
  have hsum : V.weight.real (closedBall ξ σ) / σ ^ n +
      (∫ x in closedBall ξ ρ \ closedBall ξ σ,
        V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) =
      V.weight.real (closedBall ξ ρ) / ρ ^ n := by linarith
  have h := congrArg ENNReal.ofReal hsum
  have hmassnonneg : 0 ≤ V.weight.real (closedBall ξ σ) / σ ^ n := by
    rw [MeasureTheory.measureReal_def]
    exact div_nonneg ENNReal.toReal_nonneg (pow_pos hσ n).le
  rw [ENNReal.ofReal_add hmassnonneg hintnonneg,
    V.ofReal_normalizedBallMass_real ξ hσ, V.ofReal_normalizedBallMass_real ξ hρ,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (V.integrableOn_radialDefect_annulus ξ hσ ρ) (Filter.Eventually.of_forall hnonneg)] at h
  exact h

/-- The defect in (4.3.6) is nonnegative. -/
theorem monotonicityDefect_nonneg (ξ : E) (σ ρ : ℝ) :
    0 ≤ V.monotonicityDefect ξ σ ρ :=
  bot_le

/-- Simon (4.3.8): the stationary normalized ball-mass ratio is monotone.
This is the direct consequence of the concrete fundamental identity. -/
theorem normalizedBallMass_monotoneOn {ξ : E} {R : ℝ}
    (h : V.SatisfiesStationaryMonotonicity ξ R) :
    MonotoneOn (V.normalizedBallMass ξ) (Ioo 0 R) := by
  intro σ hσ ρ hρ hσρ
  rw [← h hσ.1 hσρ hρ.2]
  exact le_add_right le_rfl

/-- Simon (4.3.8), now directly from stationarity rather than from an
assumed monotonicity identity. -/
theorem IsStationaryIn.normalizedBallMass_monotoneOn
    {U : Set E} (hV : V.IsStationaryIn U) (ξ : E) {R : ℝ}
    (hball : closedBall ξ R ⊆ U) :
    MonotoneOn (V.normalizedBallMass ξ) (Ioo 0 R) :=
  V.normalizedBallMass_monotoneOn
    (IsStationaryIn.satisfiesStationaryMonotonicity (V := V) hV ξ hball)

/-- Equality of two normalized ratios forces the intervening nonnegative
defect to vanish. -/
theorem monotonicityDefect_eq_zero {ξ : E} {R σ ρ : ℝ}
    (h : V.SatisfiesStationaryMonotonicity ξ R)
    (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hρ : ρ < R)
    (heq : V.normalizedBallMass ξ σ = V.normalizedBallMass ξ ρ) :
    V.monotonicityDefect ξ σ ρ = 0 := by
  have hid := h hσ hσρ hρ
  rw [← heq] at hid
  let a := V.normalizedBallMass ξ σ
  let b := V.monotonicityDefect ξ σ ρ
  have ha : a ≠ ⊤ := V.normalizedBallMass_ne_top ξ hσ
  have hb : b ≠ ⊤ := by
    intro hb
    have : (⊤ : ℝ≥0∞) = a := by simpa [a, b, hb] using hid
    exact ha this.symm
  have hreal := congrArg ENNReal.toReal hid
  rw [ENNReal.toReal_add ha hb] at hreal
  have hb0 : b.toReal = 0 := by linarith
  exact (ENNReal.toReal_eq_zero_iff b).mp hb0 |>.resolve_right hb

/-- The unnormalized density ratio is the infimum of the stationary ball-mass
ratios on `(0,R)`.  The usual Simon density is this value divided by `ωₙ`. -/
def stationaryDensityRatio (ξ : E) (R : ℝ) : ℝ≥0∞ :=
  sInf (V.normalizedBallMass ξ '' Ioo 0 R)

/-- Every positive-radius ratio bounds the density ratio from above. -/
theorem stationaryDensityRatio_le {ξ : E} {R ρ : ℝ}
    (hρ : ρ ∈ Ioo 0 R) :
    V.stationaryDensityRatio ξ R ≤ V.normalizedBallMass ξ ρ := by
  exact sInf_le (mem_image_of_mem (V.normalizedBallMass ξ) hρ)

/-- Simon (4.3.9), without the harmless factor `ωₙ`: concrete monotonicity
gives convergence of the normalized weight ratio as the radius decreases to
zero. -/
theorem tendsto_normalizedBallMass_atRight {ξ : E} {R : ℝ} (hR : 0 < R)
    (h : V.SatisfiesStationaryMonotonicity ξ R) :
    Tendsto (V.normalizedBallMass ξ) (𝓝[>] (0 : ℝ))
      (𝓝 (V.stationaryDensityRatio ξ R)) := by
  apply MonotoneOn.tendsto_nhdsWithin_Ioo_right
    (f := V.normalizedBallMass ξ) (x := (0 : ℝ)) (y := R)
  · exact ⟨R / 2, by linarith, by linarith⟩
  · exact V.normalizedBallMass_monotoneOn h
  · exact ⟨0, by
      rintro y ⟨ρ, hρ, rfl⟩
      exact bot_le⟩

/-- The density ratio supplied by stationary monotonicity is finite at every
interior centre and positive outer radius. -/
theorem stationaryDensityRatio_ne_top {ξ : E} {R : ℝ} (hR : 0 < R) :
    V.stationaryDensityRatio ξ R ≠ ⊤ := by
  apply ne_top_of_le_ne_top (V.normalizedBallMass_ne_top ξ (half_pos hR))
  exact V.stationaryDensityRatio_le ⟨half_pos hR, half_lt_self hR⟩

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
