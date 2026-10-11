module

public import Poincare.SimonGMT.Chapter05.CurveAreaRemainder
public import Poincare.SimonGMT.Chapter05.HarmonicEnergy
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

public section

/-!
# Simon GMT, Chapter 5, (1.2)--(1.3): scalar-codimension graphs

For an arbitrary-dimensional source and scalar target the graph Gram matrix is
a rank-one update of the identity.  The Weinstein--Aronszajn determinant
identity therefore reduces the genuine graph-area integrand to
`sqrt (1 + ‖p‖²)`.  This yields the printed fourth-order remainder and cubic
Euler--Lagrange error in every source dimension for codimension one.
-/

open scoped RealInnerProductSpace

namespace Poincare.SimonGMT.Chapter05

noncomputable section

/-- A scalar gradient encoded as Simon's family of derivative-row vectors. -/
def scalarCodimensionSlope {n : ℕ} (p : EuclideanSpace ℝ (Fin n)) :
    Fin n → EuclideanSpace ℝ (Fin 1) :=
  fun i ↦ EuclideanSpace.single 0 (p i)

/-- The column matrix used in the rank-one Gram factorization. -/
def scalarSlopeColumn {n : ℕ} (p : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin 1) ℝ :=
  fun i _ ↦ p i

/-- The row matrix used in the rank-one Gram factorization. -/
def scalarSlopeRow {n : ℕ} (p : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin 1) (Fin n) ℝ :=
  fun _ j ↦ p j

theorem graphGram_scalarCodimensionSlope {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n)) :
    graphGram (scalarCodimensionSlope p) =
      1 + scalarSlopeColumn p * scalarSlopeRow p := by
  ext i j
  simp [graphGram, scalarCodimensionSlope, scalarSlopeColumn, scalarSlopeRow,
    Matrix.mul_apply, EuclideanSpace.inner_single_left]

/-- The determinant of the scalar-codimension graph Gram matrix is exactly
`1 + ‖p‖²` in every source dimension. -/
theorem det_graphGram_scalarCodimensionSlope {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n)) :
    Matrix.det (graphGram (scalarCodimensionSlope p)) = 1 + ‖p‖ ^ 2 := by
  rw [graphGram_scalarCodimensionSlope,
    Matrix.det_one_add_mul_comm (scalarSlopeColumn p) (scalarSlopeRow p)]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [scalarSlopeColumn, scalarSlopeRow, Matrix.mul_apply, pow_two]

@[simp] theorem frobeniusSq_scalarCodimensionSlope {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n)) :
    frobeniusSq (scalarCodimensionSlope p) = ‖p‖ ^ 2 := by
  simp [frobeniusSq, scalarCodimensionSlope,
    EuclideanSpace.real_norm_sq_eq]

@[simp] theorem graphAreaIntegrand_scalarCodimensionSlope {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n)) :
    graphAreaIntegrand (scalarCodimensionSlope p) =
      Real.sqrt (1 + ‖p‖ ^ 2) := by
  rw [graphAreaIntegrand, det_graphGram_scalarCodimensionSlope]

@[simp] theorem areaRemainder_scalarCodimensionSlope {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n)) :
    areaRemainder (scalarCodimensionSlope p) = scalarAreaRemainder ‖p‖ := by
  rw [← areaRemainder_scalarSlope]
  simp [areaRemainder]

/-- Simon's fourth-order remainder estimate for scalar-codimension graphs in
every source dimension. -/
theorem abs_areaRemainder_scalarCodimensionSlope_le {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n)) :
    |areaRemainder (scalarCodimensionSlope p)| ≤
      (1 / 8 : ℝ) * ‖p‖ ^ 4 := by
  simpa using abs_scalarAreaRemainder_le ‖p‖

/-- The scalar-codimension minimal-graph flux. -/
def scalarCodimensionMinimalGraphFlux {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (Real.sqrt (1 + ‖p‖ ^ 2))⁻¹ • p

/-- The nonlinear error between scalar-codimension minimal-graph flux and
linear harmonic flux. -/
def scalarCodimensionHarmonicResidual {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  p - scalarCodimensionMinimalGraphFlux p

@[simp] theorem scalarCodimensionMinimalGraphFlux_add_residual {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n)) :
    scalarCodimensionMinimalGraphFlux p +
      scalarCodimensionHarmonicResidual p = p := by
  simp [scalarCodimensionHarmonicResidual]

/-- The Fréchet derivative of the genuine scalar-codimension determinant
integrand is represented by its minimal-graph flux. -/
theorem hasFDerivAt_graphAreaIntegrand_scalarCodimensionSlope {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt
      (fun q ↦ graphAreaIntegrand (scalarCodimensionSlope q))
      (innerSL ℝ (scalarCodimensionMinimalGraphFlux p)) p := by
  have hnorm : HasFDerivAt
      (fun q : EuclideanSpace ℝ (Fin n) ↦ ‖q‖ ^ 2)
      (2 • innerSL ℝ p) p :=
    (hasStrictFDerivAt_norm_sq p).hasFDerivAt
  have hsqrt := (hnorm.const_add (1 : ℝ)).sqrt (by positivity)
  convert hsqrt using 1
  · funext q
    simp
  · ext q
    simp [scalarCodimensionMinimalGraphFlux]
    field_simp

/-- The scalar-codimension harmonic residual is cubically small in every
source dimension. -/
theorem norm_scalarCodimensionHarmonicResidual_le {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n)) :
    ‖scalarCodimensionHarmonicResidual p‖ ≤
      (1 / 2 : ℝ) * ‖p‖ ^ 3 := by
  let s : ℝ := Real.sqrt (1 + ‖p‖ ^ 2)
  have hs : 1 ≤ s := by
    dsimp [s]
    exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖p‖])
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
  rw [scalarCodimensionHarmonicResidual,
    scalarCodimensionMinimalGraphFlux]
  change ‖p - s⁻¹ • p‖ ≤ (1 / 2 : ℝ) * ‖p‖ ^ 3
  rw [show p - s⁻¹ • p = (1 - s⁻¹) • p by
    rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hcoeff]
  nlinarith [norm_nonneg p]

theorem norm_sq_scalarCodimensionHarmonicResidual_le {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n)) :
    ‖scalarCodimensionHarmonicResidual p‖ ^ 2 ≤
      (1 / 4 : ℝ) * ‖p‖ ^ 6 := by
  calc
    ‖scalarCodimensionHarmonicResidual p‖ ^ 2 ≤
        ((1 / 2 : ℝ) * ‖p‖ ^ 3) ^ 2 := by
      gcongr
      exact norm_scalarCodimensionHarmonicResidual_le p
    _ = (1 / 4 : ℝ) * ‖p‖ ^ 6 := by ring

/-- Coordinate form of the sixth-order residual-energy estimate, ready for
the abstract harmonic-comparison theorem in `HarmonicEnergy`. -/
theorem scalarCodimension_residual_energy_le {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n)) :
    (∑ i, ‖scalarCodimensionHarmonicResidual p i‖ ^ 2) ≤
      (1 / 4 : ℝ) * (∑ i, ‖p i‖ ^ 2) ^ 3 := by
  rw [← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq]
  convert norm_sq_scalarCodimensionHarmonicResidual_le p using 1
  ring

/-- The actual Fréchet derivative of the scalar-codimension Taylor remainder
has the cubic bound in Simon (1.2). -/
theorem norm_fderiv_areaRemainder_scalarCodimensionSlope_le {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (fun q ↦ areaRemainder (scalarCodimensionSlope q)) p‖ ≤
      (1 / 2 : ℝ) * ‖p‖ ^ 3 := by
  have hnorm : HasFDerivAt
      (fun q : EuclideanSpace ℝ (Fin n) ↦ ‖q‖ ^ 2)
      (2 • innerSL ℝ p) p :=
    (hasStrictFDerivAt_norm_sq p).hasFDerivAt
  have h := ((hasFDerivAt_graphAreaIntegrand_scalarCodimensionSlope p).sub_const
    (1 : ℝ)).sub (hnorm.const_mul (1 / 2 : ℝ))
  have hactual : HasFDerivAt
      (fun q ↦ areaRemainder (scalarCodimensionSlope q))
      (-(innerSL ℝ (scalarCodimensionHarmonicResidual p))) p := by
    convert h using 1
    · funext q
      simp [areaRemainder]
    · ext q
      simp [scalarCodimensionHarmonicResidual,
        scalarCodimensionMinimalGraphFlux]
  rw [hactual.fderiv, norm_neg, innerSL_apply_norm]
  exact norm_scalarCodimensionHarmonicResidual_le p

/-- Scalar-codimension specialization of Simon (1.3): stationarity of the
actual determinant flux becomes the weak harmonic equation with its genuine
cubic residual, in every source dimension. -/
theorem scalarCodimension_stationary_weak_harmonic_identity
    {X : Type*} [MeasurableSpace X] {n : ℕ} (μ : MeasureTheory.Measure X)
    (p q : X → EuclideanSpace ℝ (Fin n))
    (hflux : MeasureTheory.Integrable
      (fun x ↦ inner ℝ (scalarCodimensionMinimalGraphFlux (p x)) (q x)) μ)
    (hresidual : MeasureTheory.Integrable
      (fun x ↦ inner ℝ (scalarCodimensionHarmonicResidual (p x)) (q x)) μ)
    (hstationary :
      (∫ x, inner ℝ (scalarCodimensionMinimalGraphFlux (p x)) (q x) ∂μ) = 0) :
    (∫ x, inner ℝ (p x) (q x) ∂μ) =
      ∫ x, inner ℝ (scalarCodimensionHarmonicResidual (p x)) (q x) ∂μ := by
  calc
    (∫ x, inner ℝ (p x) (q x) ∂μ) =
        ∫ x, (inner ℝ (scalarCodimensionMinimalGraphFlux (p x)) (q x) +
          inner ℝ (scalarCodimensionHarmonicResidual (p x)) (q x)) ∂μ := by
      refine MeasureTheory.integral_congr_ae ?_
      exact Filter.Eventually.of_forall fun x ↦ by
        change inner ℝ (p x) (q x) =
          inner ℝ (scalarCodimensionMinimalGraphFlux (p x)) (q x) +
            inner ℝ (scalarCodimensionHarmonicResidual (p x)) (q x)
        rw [← inner_add_left,
          scalarCodimensionMinimalGraphFlux_add_residual]
    _ = (∫ x, inner ℝ (scalarCodimensionMinimalGraphFlux (p x)) (q x) ∂μ) +
        ∫ x, inner ℝ (scalarCodimensionHarmonicResidual (p x)) (q x) ∂μ :=
      MeasureTheory.integral_add hflux hresidual
    _ = ∫ x, inner ℝ (scalarCodimensionHarmonicResidual (p x)) (q x) ∂μ := by
      rw [hstationary, zero_add]

/-- Simon (1.5) for the genuine scalar-codimension graph residual.  Once a
harmonic replacement supplies the displayed weak identity and integrability,
the comparison energy is bounded by one quarter of the sixth-power gradient
energy. -/
theorem scalarCodimension_harmonicComparison_energy_le_sixthPower
    {X : Type*} [MeasurableSpace X] {n : ℕ} (μ : MeasureTheory.Measure X)
    (Du Dv : X → EuclideanSpace ℝ (Fin n))
    (hA : MeasureTheory.Integrable
      (dirichletDensity
        (fun x i ↦ scalarCodimensionHarmonicResidual (Du x) i)) μ)
    (hdiff : MeasureTheory.Integrable
      (dirichletDensity (fun x i ↦ Du x i - Dv x i)) μ)
    (hpair : MeasureTheory.Integrable
      (residualPairing
        (fun x i ↦ scalarCodimensionHarmonicResidual (Du x) i)
        (fun x i ↦ Du x i - Dv x i)) μ)
    (hcubic : MeasureTheory.Integrable
      (fun x ↦ (1 / 4 : ℝ) *
        (dirichletDensity (fun y i ↦ Du y i) x) ^ 3) μ)
    (hweak :
      (∫ x, dirichletDensity (fun y i ↦ Du y i - Dv y i) x ∂μ) =
        ∫ x, residualPairing
          (fun y i ↦ scalarCodimensionHarmonicResidual (Du y) i)
          (fun y i ↦ Du y i - Dv y i) x ∂μ) :
    (∫ x, dirichletDensity (fun y i ↦ Du y i - Dv y i) x ∂μ) ≤
      (1 / 4 : ℝ) *
        ∫ x, (dirichletDensity (fun y i ↦ Du y i) x) ^ 3 ∂μ := by
  apply harmonicComparison_energy_le_sixthPower μ
    (fun x i ↦ Du x i) (fun x i ↦ Dv x i)
    (fun x i ↦ scalarCodimensionHarmonicResidual (Du x) i)
    (1 / 4 : ℝ) hA hdiff hpair hcubic hweak
  intro x
  exact scalarCodimension_residual_energy_le (Du x)

end

end Poincare.SimonGMT.Chapter05
