module

public import Poincare.SimonGMT.Chapter05.GraphAreaExpansion
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

public section

/-!
# Simon GMT, Chapter 5, (1.2): scalar graph remainder

The full matrix estimate in (1.2) is still open.  This module proves both
printed orders, with explicit constants, for a one-dimensional scalar graph.
It is a genuine specialization of the determinant integrand, not an assumed
Taylor interface.
-/

namespace Poincare.SimonGMT.Chapter05

noncomputable section

/-- The graph-area remainder for the scalar slope `p`. -/
def scalarAreaRemainder (p : ℝ) : ℝ :=
  Real.sqrt (1 + p ^ 2) - 1 - (1 / 2 : ℝ) * p ^ 2

/-- The `1 × 1` derivative matrix with scalar entry `p`. -/
def scalarSlope (p : ℝ) : Fin 1 → EuclideanSpace ℝ (Fin 1) :=
  fun _ ↦ EuclideanSpace.single 0 p

@[simp] theorem frobeniusSq_scalarSlope (p : ℝ) :
    frobeniusSq (scalarSlope p) = p ^ 2 := by
  simp [frobeniusSq, scalarSlope]

@[simp] theorem graphAreaIntegrand_scalarSlope (p : ℝ) :
  graphAreaIntegrand (scalarSlope p) = Real.sqrt (1 + p ^ 2) := by
  simp [graphAreaIntegrand, graphGram, scalarSlope]

/-- The scalar formula is definitionally the actual determinant remainder on
`1 × 1` matrices. -/
@[simp] theorem areaRemainder_scalarSlope (p : ℝ) :
    areaRemainder (scalarSlope p) = scalarAreaRemainder p := by
  simp [areaRemainder, scalarAreaRemainder]

/-- Exact rationalized form of the scalar fourth-order remainder. -/
theorem scalarAreaRemainder_eq (p : ℝ) :
    scalarAreaRemainder p =
      -(p ^ 4) / (2 * (Real.sqrt (1 + p ^ 2) + 1) ^ 2) := by
  have hnonneg : 0 ≤ 1 + p ^ 2 := by positivity
  have hsquare : Real.sqrt (1 + p ^ 2) ^ 2 = 1 + p ^ 2 :=
    Real.sq_sqrt hnonneg
  have hden : Real.sqrt (1 + p ^ 2) + 1 ≠ 0 := by positivity
  unfold scalarAreaRemainder
  field_simp
  nlinarith

/-- The first estimate in Simon (1.2), with explicit scalar constant `1/8`.
No smallness assumption is needed in dimension one. -/
theorem abs_scalarAreaRemainder_le (p : ℝ) :
    |scalarAreaRemainder p| ≤ (1 / 8 : ℝ) * |p| ^ 4 := by
  have hsqrt : 1 ≤ Real.sqrt (1 + p ^ 2) := by
    exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg p])
  have hden : 8 ≤ 2 * (Real.sqrt (1 + p ^ 2) + 1) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (1 + p ^ 2) - 1)]
  have hdenpos : 0 < 2 * (Real.sqrt (1 + p ^ 2) + 1) ^ 2 := by positivity
  rw [scalarAreaRemainder_eq, abs_div, abs_neg, abs_pow, abs_of_pos hdenpos]
  have hp : 0 ≤ |p| ^ 4 := by positivity
  calc
    |p| ^ 4 / (2 * (Real.sqrt (1 + p ^ 2) + 1) ^ 2) ≤ |p| ^ 4 / 8 :=
      div_le_div_of_nonneg_left hp (by norm_num) hden
    _ = (1 / 8 : ℝ) * |p| ^ 4 := by ring_nf

/-- Exact derivative of the scalar remainder. -/
theorem hasDerivAt_scalarAreaRemainder (p : ℝ) :
    HasDerivAt scalarAreaRemainder
      (p / Real.sqrt (1 + p ^ 2) - p) p := by
  have hpos : 0 < 1 + p ^ 2 := by positivity
  have hsqrt := ((hasDerivAt_const p (1 : ℝ)).add
    ((hasDerivAt_id p).pow 2)).sqrt hpos.ne'
  have hsqrt' : HasDerivAt (fun x : ℝ ↦ Real.sqrt (1 + x ^ 2))
      (p / Real.sqrt (1 + p ^ 2)) p := by
    convert hsqrt using 1
    · rfl
    · simp only [id_eq, Nat.cast_ofNat, zero_add, mul_one]
      norm_num
      field_simp
  have hquad : HasDerivAt (fun x : ℝ ↦ (1 / 2 : ℝ) * x ^ 2) p p := by
    convert HasDerivAt.const_mul (1 / 2 : ℝ) ((hasDerivAt_id p).pow 2) using 1
    · rfl
    · norm_num
      ring
  exact (hsqrt'.sub_const 1).sub hquad

/-- Rationalized form of the scalar remainder derivative. -/
theorem scalarAreaRemainder_deriv_eq (p : ℝ) :
    p / Real.sqrt (1 + p ^ 2) - p =
      -(p ^ 3) /
        (Real.sqrt (1 + p ^ 2) * (Real.sqrt (1 + p ^ 2) + 1)) := by
  have hnonneg : 0 ≤ 1 + p ^ 2 := by positivity
  have hsquare : Real.sqrt (1 + p ^ 2) ^ 2 = 1 + p ^ 2 :=
    Real.sq_sqrt hnonneg
  have hsqrt : Real.sqrt (1 + p ^ 2) ≠ 0 := by positivity
  have hsum : Real.sqrt (1 + p ^ 2) + 1 ≠ 0 := by positivity
  have hmul : Real.sqrt (1 + p ^ 2) * Real.sqrt (1 + p ^ 2) =
      1 + p ^ 2 := by nlinarith
  field_simp
  ring_nf
  rw [hsquare]
  ring

/-- The derivative estimate in Simon (1.2), with explicit scalar constant
`1/2`. -/
theorem abs_scalarAreaRemainder_deriv_le (p : ℝ) :
    |p / Real.sqrt (1 + p ^ 2) - p| ≤ (1 / 2 : ℝ) * |p| ^ 3 := by
  have hsqrt : 1 ≤ Real.sqrt (1 + p ^ 2) := by
    exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg p])
  have hden : 2 ≤
      Real.sqrt (1 + p ^ 2) * (Real.sqrt (1 + p ^ 2) + 1) := by
    nlinarith [Real.sqrt_nonneg (1 + p ^ 2)]
  have hdenpos : 0 <
      Real.sqrt (1 + p ^ 2) * (Real.sqrt (1 + p ^ 2) + 1) := by positivity
  rw [scalarAreaRemainder_deriv_eq, abs_div, abs_neg, abs_pow,
    abs_of_pos hdenpos]
  have hp : 0 ≤ |p| ^ 3 := by positivity
  calc
    |p| ^ 3 /
        (Real.sqrt (1 + p ^ 2) * (Real.sqrt (1 + p ^ 2) + 1)) ≤
        |p| ^ 3 / 2 :=
      div_le_div_of_nonneg_left hp (by norm_num) hden
    _ = (1 / 2 : ℝ) * |p| ^ 3 := by ring_nf

/-! ## The scalar weak minimal-graph equation -/

/-- The derivative of the scalar graph-area integrand. -/
def scalarMinimalGraphFlux (p : ℝ) : ℝ :=
  p / Real.sqrt (1 + p ^ 2)

/-- The cubic error when the scalar minimal-graph flux is compared with the
linear harmonic flux. -/
def scalarHarmonicResidual (p : ℝ) : ℝ :=
  p - scalarMinimalGraphFlux p

@[simp] theorem scalarMinimalGraphFlux_add_residual (p : ℝ) :
    scalarMinimalGraphFlux p + scalarHarmonicResidual p = p := by
  simp [scalarHarmonicResidual]

/-- The scalar nonlinear-to-harmonic residual is cubically small, with the
same explicit constant as the derivative estimate above. -/
theorem abs_scalarHarmonicResidual_le (p : ℝ) :
    |scalarHarmonicResidual p| ≤ (1 / 2 : ℝ) * |p| ^ 3 := by
  rw [scalarHarmonicResidual, abs_sub_comm]
  exact abs_scalarAreaRemainder_deriv_le p

/-- Scalar specialization of Simon (1.3): stationarity of the actual minimal
graph flux rewrites exactly as a weak harmonic equation with cubic residual.
-/
theorem scalar_stationary_weak_harmonic_identity
    {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (p q : X → ℝ)
    (hflux : MeasureTheory.Integrable
      (fun x ↦ scalarMinimalGraphFlux (p x) * q x) μ)
    (hresidual : MeasureTheory.Integrable
      (fun x ↦ scalarHarmonicResidual (p x) * q x) μ)
    (hstationary :
      (∫ x, scalarMinimalGraphFlux (p x) * q x ∂μ) = 0) :
    (∫ x, p x * q x ∂μ) =
      ∫ x, scalarHarmonicResidual (p x) * q x ∂μ := by
  calc
    (∫ x, p x * q x ∂μ) =
        ∫ x, (scalarMinimalGraphFlux (p x) * q x +
          scalarHarmonicResidual (p x) * q x) ∂μ := by
      refine MeasureTheory.integral_congr_ae ?_
      exact Filter.Eventually.of_forall fun x ↦ by
        change p x * q x = scalarMinimalGraphFlux (p x) * q x +
          scalarHarmonicResidual (p x) * q x
        rw [← add_mul, scalarMinimalGraphFlux_add_residual]
    _ = (∫ x, scalarMinimalGraphFlux (p x) * q x ∂μ) +
        ∫ x, scalarHarmonicResidual (p x) * q x ∂μ :=
      MeasureTheory.integral_add hflux hresidual
    _ = ∫ x, scalarHarmonicResidual (p x) * q x ∂μ := by
      rw [hstationary, zero_add]

/-- One-dimensional scalar specialization of Simon (1.4): every affine
harmonic replacement has the weak harmonic identity against a `C¹` test that
vanishes at the endpoints. -/
theorem scalar_affine_harmonic_weak_identity {a b c : ℝ} (hab : a ≤ b)
    {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ (Set.Icc a b))
    (hφa : φ a = 0) (hφb : φ b = 0) :
    (∫ x in a..b, c * deriv φ x) = 0 := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_deriv_of_contDiffOn_Icc hφ hab, hφa, hφb]
  ring

end

end Poincare.SimonGMT.Chapter05
