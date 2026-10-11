module

public import Poincare.SimonGMT.Chapter05.ScalarAreaRemainder
public import Mathlib.Analysis.InnerProductSpace.Calculus

public section

/-!
# Simon GMT, Chapter 5, (1.2)--(1.3): arbitrary-codimension curves

This module extends the scalar calculation to a one-dimensional source and an
arbitrary finite-dimensional Euclidean target.  Thus the derivative matrix has
one row but any codimension.  The determinant integrand reduces to the radial
function `sqrt (1 + ‖p‖²)`, so the fourth-order Taylor remainder and cubic flux
error are estimates for the actual graph-area integrand.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace Poincare.SimonGMT.Chapter05

noncomputable section

/-- The one-row derivative matrix whose only row is `p`. -/
def curveSlope {ℓ : ℕ} (p : EuclideanSpace ℝ (Fin ℓ)) :
    Fin 1 → EuclideanSpace ℝ (Fin ℓ) :=
  fun _ ↦ p

@[simp] theorem frobeniusSq_curveSlope {ℓ : ℕ}
    (p : EuclideanSpace ℝ (Fin ℓ)) :
    frobeniusSq (curveSlope p) = ‖p‖ ^ 2 := by
  simp [frobeniusSq, curveSlope]

@[simp] theorem graphAreaIntegrand_curveSlope {ℓ : ℕ}
    (p : EuclideanSpace ℝ (Fin ℓ)) :
    graphAreaIntegrand (curveSlope p) = Real.sqrt (1 + ‖p‖ ^ 2) := by
  simp [graphAreaIntegrand, graphGram, curveSlope]

/-- The Fréchet derivative of the genuine arbitrary-codimension curve-area
integrand.  Its representing vector is the minimal-graph flux below. -/
theorem hasFDerivAt_graphAreaIntegrand_curveSlope {ℓ : ℕ}
    (p : EuclideanSpace ℝ (Fin ℓ)) :
    HasFDerivAt
      (fun q ↦ graphAreaIntegrand (curveSlope q))
      ((Real.sqrt (1 + ‖p‖ ^ 2))⁻¹ • innerSL ℝ p) p := by
  have hnorm : HasFDerivAt
      (fun q : EuclideanSpace ℝ (Fin ℓ) ↦ ‖q‖ ^ 2)
      (2 • innerSL ℝ p) p :=
    (hasStrictFDerivAt_norm_sq p).hasFDerivAt
  have hsqrt := (hnorm.const_add (1 : ℝ)).sqrt (by positivity)
  convert hsqrt using 1
  · funext q
    simp
  · ext q
    simp
    field_simp

/-- The arbitrary-codimension curve remainder is exactly the scalar radial
remainder evaluated at the length of the derivative vector. -/
@[simp] theorem areaRemainder_curveSlope {ℓ : ℕ}
    (p : EuclideanSpace ℝ (Fin ℓ)) :
    areaRemainder (curveSlope p) = scalarAreaRemainder ‖p‖ := by
  rw [← areaRemainder_scalarSlope]
  simp [areaRemainder]

/-- Simon's fourth-order remainder estimate for a one-dimensional source and
arbitrary codimension, with the explicit constant `1/8`. -/
theorem abs_areaRemainder_curveSlope_le {ℓ : ℕ}
    (p : EuclideanSpace ℝ (Fin ℓ)) :
    |areaRemainder (curveSlope p)| ≤ (1 / 8 : ℝ) * ‖p‖ ^ 4 := by
  simpa using abs_scalarAreaRemainder_le ‖p‖

/-- The minimal-graph flux for a curve with derivative vector `p`. -/
def curveMinimalGraphFlux {ℓ : ℕ} (p : EuclideanSpace ℝ (Fin ℓ)) :
    EuclideanSpace ℝ (Fin ℓ) :=
  (Real.sqrt (1 + ‖p‖ ^ 2))⁻¹ • p

/-- The nonlinear error between the linear harmonic flux and the actual
minimal-graph flux for a curve. -/
def curveHarmonicResidual {ℓ : ℕ} (p : EuclideanSpace ℝ (Fin ℓ)) :
    EuclideanSpace ℝ (Fin ℓ) :=
  p - curveMinimalGraphFlux p

/-- The derivative of the curve graph-area integrand is represented exactly
by the minimal-graph flux vector. -/
theorem hasFDerivAt_graphAreaIntegrand_curveSlope_flux {ℓ : ℕ}
    (p : EuclideanSpace ℝ (Fin ℓ)) :
    HasFDerivAt
      (fun q ↦ graphAreaIntegrand (curveSlope q))
      (innerSL ℝ (curveMinimalGraphFlux p)) p := by
  convert hasFDerivAt_graphAreaIntegrand_curveSlope p using 1
  ext q
  simp [curveMinimalGraphFlux]

@[simp] theorem fderiv_graphAreaIntegrand_curveSlope {ℓ : ℕ}
    (p : EuclideanSpace ℝ (Fin ℓ)) :
    fderiv ℝ (fun q ↦ graphAreaIntegrand (curveSlope q)) p =
      innerSL ℝ (curveMinimalGraphFlux p) :=
  (hasFDerivAt_graphAreaIntegrand_curveSlope_flux p).fderiv

@[simp] theorem curveMinimalGraphFlux_add_residual {ℓ : ℕ}
    (p : EuclideanSpace ℝ (Fin ℓ)) :
    curveMinimalGraphFlux p + curveHarmonicResidual p = p := by
  simp [curveHarmonicResidual]

/-- The derivative of the actual curve-area Taylor remainder is the negative
inner product with the genuine nonlinear harmonic residual. -/
theorem hasFDerivAt_areaRemainder_curveSlope {ℓ : ℕ}
    (p : EuclideanSpace ℝ (Fin ℓ)) :
    HasFDerivAt
      (fun q ↦ areaRemainder (curveSlope q))
      (-(innerSL ℝ (curveHarmonicResidual p))) p := by
  have harea := hasFDerivAt_graphAreaIntegrand_curveSlope p
  have hnorm : HasFDerivAt
      (fun q : EuclideanSpace ℝ (Fin ℓ) ↦ ‖q‖ ^ 2)
      (2 • innerSL ℝ p) p :=
    (hasStrictFDerivAt_norm_sq p).hasFDerivAt
  have h := (harea.sub_const (1 : ℝ)).sub (hnorm.const_mul (1 / 2 : ℝ))
  convert h using 1
  · funext q
    simp [areaRemainder]
  · ext q
    simp [curveHarmonicResidual, curveMinimalGraphFlux]

/-- The arbitrary-codimension curve flux error is cubically small, with the
same explicit constant `1/2` as in the scalar calculation. -/
theorem norm_curveHarmonicResidual_le {ℓ : ℕ}
    (p : EuclideanSpace ℝ (Fin ℓ)) :
    ‖curveHarmonicResidual p‖ ≤ (1 / 2 : ℝ) * ‖p‖ ^ 3 := by
  let s : ℝ := Real.sqrt (1 + ‖p‖ ^ 2)
  have hs : 1 ≤ s := by
    dsimp [s]
    exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖p‖])
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hsq : s ^ 2 = 1 + ‖p‖ ^ 2 := by
    dsimp [s]
    exact Real.sq_sqrt (by positivity)
  have hcoeff : 0 ≤ 1 - s⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hs)
  have heq : 1 - s⁻¹ = ‖p‖ ^ 2 / (s * (s + 1)) := by
    field_simp
    nlinarith
  have hden : 2 ≤ s * (s + 1) := by nlinarith
  have hbound : 1 - s⁻¹ ≤ (1 / 2 : ℝ) * ‖p‖ ^ 2 := by
    rw [heq]
    calc
      ‖p‖ ^ 2 / (s * (s + 1)) ≤ ‖p‖ ^ 2 / 2 :=
        div_le_div_of_nonneg_left (sq_nonneg ‖p‖) (by norm_num) hden
      _ = (1 / 2 : ℝ) * ‖p‖ ^ 2 := by ring
  rw [curveHarmonicResidual, curveMinimalGraphFlux]
  change ‖p - s⁻¹ • p‖ ≤ (1 / 2 : ℝ) * ‖p‖ ^ 3
  rw [show p - s⁻¹ • p = (1 - s⁻¹) • p by
    rw [sub_smul, one_smul], norm_smul]
  change |1 - s⁻¹| * ‖p‖ ≤ (1 / 2 : ℝ) * ‖p‖ ^ 3
  rw [abs_of_nonneg hcoeff]
  nlinarith [norm_nonneg p]

/-- The printed cubic derivative estimate for a one-dimensional source and
arbitrary codimension, stated as an operator-norm bound for the actual
Fréchet derivative of the determinant remainder. -/
theorem norm_fderiv_areaRemainder_curveSlope_le {ℓ : ℕ}
    (p : EuclideanSpace ℝ (Fin ℓ)) :
    ‖fderiv ℝ (fun q ↦ areaRemainder (curveSlope q)) p‖ ≤
      (1 / 2 : ℝ) * ‖p‖ ^ 3 := by
  rw [(hasFDerivAt_areaRemainder_curveSlope p).fderiv, norm_neg,
    innerSL_apply_norm]
  exact norm_curveHarmonicResidual_le p

/-- Squaring the cubic flux estimate gives the sixth-order density bound used
in the harmonic-comparison energy argument. -/
theorem norm_sq_curveHarmonicResidual_le {ℓ : ℕ}
    (p : EuclideanSpace ℝ (Fin ℓ)) :
    ‖curveHarmonicResidual p‖ ^ 2 ≤ (1 / 4 : ℝ) * ‖p‖ ^ 6 := by
  calc
    ‖curveHarmonicResidual p‖ ^ 2 ≤
        ((1 / 2 : ℝ) * ‖p‖ ^ 3) ^ 2 := by
      gcongr
      exact norm_curveHarmonicResidual_le p
    _ = (1 / 4 : ℝ) * ‖p‖ ^ 6 := by ring

/-- Vector-valued curve specialization of Simon (1.3): stationarity of the
actual minimal-graph flux rewrites as the weak harmonic equation with its
genuine cubic residual. -/
theorem curve_stationary_weak_harmonic_identity
    {X : Type*} [MeasurableSpace X] {ℓ : ℕ} (μ : Measure X)
    (p q : X → EuclideanSpace ℝ (Fin ℓ))
    (hflux : Integrable
      (fun x ↦ inner ℝ (curveMinimalGraphFlux (p x)) (q x)) μ)
    (hresidual : Integrable
      (fun x ↦ inner ℝ (curveHarmonicResidual (p x)) (q x)) μ)
    (hstationary :
      (∫ x, inner ℝ (curveMinimalGraphFlux (p x)) (q x) ∂μ) = 0) :
    (∫ x, inner ℝ (p x) (q x) ∂μ) =
      ∫ x, inner ℝ (curveHarmonicResidual (p x)) (q x) ∂μ := by
  calc
    (∫ x, inner ℝ (p x) (q x) ∂μ) =
        ∫ x, (inner ℝ (curveMinimalGraphFlux (p x)) (q x) +
          inner ℝ (curveHarmonicResidual (p x)) (q x)) ∂μ := by
      refine integral_congr_ae ?_
      exact Filter.Eventually.of_forall fun x ↦ by
        change inner ℝ (p x) (q x) =
          inner ℝ (curveMinimalGraphFlux (p x)) (q x) +
            inner ℝ (curveHarmonicResidual (p x)) (q x)
        rw [← inner_add_left, curveMinimalGraphFlux_add_residual]
    _ = (∫ x, inner ℝ (curveMinimalGraphFlux (p x)) (q x) ∂μ) +
        ∫ x, inner ℝ (curveHarmonicResidual (p x)) (q x) ∂μ :=
      integral_add hflux hresidual
    _ = ∫ x, inner ℝ (curveHarmonicResidual (p x)) (q x) ∂μ := by
      rw [hstationary, zero_add]

/-- A `C¹` Euclidean-valued function on a compact interval has an
interval-integrable vector derivative. -/
theorem intervalIntegrable_deriv_of_contDiffOn_Icc_euclidean
    {ℓ : ℕ} {a b : ℝ} {φ : ℝ → EuclideanSpace ℝ (Fin ℓ)}
    (hφ : ContDiffOn ℝ 1 φ (Set.Icc a b)) (hab : a ≤ b) :
    IntervalIntegrable (deriv φ) volume a b := by
  rcases hab.eq_or_lt with rfl | hablt
  · simp
  have hcontinuous :=
    (hφ.derivWithin (m := 0) (uniqueDiffOn_Icc hablt) (by simp)).continuousOn
  apply (hcontinuous.intervalIntegrable_of_Icc (μ := volume) hab).congr_ae
  simp only [hab, Set.uIoc_of_le]
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with x hx
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

/-- Vector-valued one-dimensional specialization of Simon (1.4): an affine
harmonic gradient is weakly orthogonal to every `C¹` interval test vanishing
at the endpoints. -/
theorem curve_affine_harmonic_weak_identity {ℓ : ℕ} {a b : ℝ}
    (hab : a ≤ b) (c : EuclideanSpace ℝ (Fin ℓ))
    {φ : ℝ → EuclideanSpace ℝ (Fin ℓ)}
    (hφ : ContDiffOn ℝ 1 φ (Set.Icc a b))
    (hφa : φ a = 0) (hφb : φ b = 0) :
    (∫ x in a..b, inner ℝ c (deriv φ x)) = 0 := by
  have hint := intervalIntegrable_deriv_of_contDiffOn_Icc_euclidean hφ hab
  change (∫ x in a..b, (innerSL ℝ c) (deriv φ x)) = 0
  rw [(innerSL ℝ c).intervalIntegral_comp_comm hint,
    intervalIntegral.integral_deriv_of_contDiffOn_Icc hφ hab,
    hφa, hφb, sub_self]
  simp

end

end Poincare.SimonGMT.Chapter05
