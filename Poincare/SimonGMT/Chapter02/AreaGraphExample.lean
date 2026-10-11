module

public import Poincare.SimonGMT.Chapter02.AreaLiteral
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

/-!
# Simon (3.6)(3): area of a scalar graph

The graph is placed in the Hilbert product, with the Euclidean rather than
the maximum product norm. The rank-one determinant calculation identifies
its actual derivative Jacobian with `sqrt (1 + ‖Du‖²)`.
-/

open Function MeasureTheory Module Set
open scoped ENNReal NNReal InnerProductSpace

namespace Poincare.SimonGMT.Chapter02
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual Euclidean graph parametrization `x ↦ (x,u(x))`. -/
def scalarGraph (u : E → ℝ) (x : E) : WithLp 2 (E × ℝ) :=
  WithLp.toLp 2 (x, u x)

/-- Derivative of the graph parametrization. -/
def scalarGraphLinear (L : E →L[ℝ] ℝ) : E →L[ℝ] WithLp 2 (E × ℝ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ E).prod L)

@[simp] theorem scalarGraphLinear_apply (L : E →L[ℝ] ℝ) (x : E) :
    scalarGraphLinear L x = WithLp.toLp 2 (x, L x) := rfl

theorem scalarGraph_injective (u : E → ℝ) : Injective (scalarGraph u) := by
  intro x y h
  exact congrArg WithLp.fst h

theorem scalarGraphLinear_injective (L : E →L[ℝ] ℝ) :
    Injective (scalarGraphLinear L) := scalarGraph_injective L

theorem hasFDerivAt_scalarGraph {u : E → ℝ} {L : E →L[ℝ] ℝ} {x : E}
    (hu : HasFDerivAt u L x) :
    HasFDerivAt (scalarGraph u) (scalarGraphLinear L) x := by
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk hu)

/-- The Gram determinant for the graph is `det(I + Duᵀ Du) = 1 + ‖Du‖²`. -/
theorem scalarGraphLinear_normDet_sq (L : E →L[ℝ] ℝ) :
    (scalarGraphLinear L).normDet ^ 2 = 1 + ‖L‖ ^ 2 := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let v : Fin (finrank ℝ E) → ℝ := fun i ↦ L (b i)
  have hgram : Matrix.gram ℝ (fun i ↦ scalarGraphLinear L (b i)) =
      1 + Matrix.replicateCol (Fin 1) v * Matrix.replicateRow (Fin 1) v := by
    ext i j
    simp [Matrix.gram, scalarGraphLinear_apply, WithLp.prod_inner_apply,
      orthonormal_iff_ite.mp b.orthonormal, Matrix.one_apply,
      Matrix.mul_apply, v, mul_comm]
  have hsq : (scalarGraphLinear L).normDet ^ 2 =
      (Matrix.gram ℝ (fun i ↦ scalarGraphLinear L (b i))).det := by
    simpa using LinearMap.normDet_sq_eq_det_gram (scalarGraphLinear L).toLinearMap b
  rw [hsq, hgram,
    Matrix.det_one_add_replicateCol_mul_replicateRow, b.norm_dual L]
  simp [dotProduct, v, pow_two]

theorem scalarGraphLinear_normDet (L : E →L[ℝ] ℝ) :
    (scalarGraphLinear L).normDet = Real.sqrt (1 + ‖L‖ ^ 2) := by
  rw [← scalarGraphLinear_normDet_sq]
  exact (Real.sqrt_sq (scalarGraphLinear L).normDet_nonneg).symm

/-- The pointwise Jacobian of the actual scalar graph. -/
theorem areaJacobianAt_scalarGraph {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) :
    areaJacobianAt (scalarGraph u) x = Real.sqrt (1 + ‖fderiv ℝ u x‖ ^ 2) := by
  rw [areaJacobianAt_eq_normDet, (hasFDerivAt_scalarGraph hu.hasFDerivAt).fderiv,
    scalarGraphLinear_normDet]

variable [MeasurableSpace E] [BorelSpace E]

/-- Area of a differentiable scalar graph on a Borel set. Neither a global
Lipschitz bound nor compactness of the source is required. -/
theorem scalar_graph_area_formula {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (hu : ∀ x ∈ s, DifferentiableAt ℝ u x) :
    Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) (scalarGraph u '' s) =
      ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ u x‖ ^ 2)) ∂volume := by
  rw [simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure,
    injective_area_formula_of_injective_derivative hs
      (fun x hx ↦ (hasFDerivAt_scalarGraph (hu x hx).hasFDerivAt).hasFDerivWithinAt)
      (fun x _ ↦ scalarGraphLinear_injective (fderiv ℝ u x))
      (scalarGraph_injective u).injOn,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  exact lintegral_congr (fun x ↦ congrArg ENNReal.ofReal (scalarGraphLinear_normDet _))

/-- Simon's printed graph example for an arbitrary C¹ function on an open
domain, with the usual gradient norm and the exact Hausdorff measure. -/
theorem contDiffOn_scalar_graph_area_formula {Ω : Set E} {u : E → ℝ}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω) :
    Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) (scalarGraph u '' Ω) =
      ∫⁻ x in Ω, ENNReal.ofReal (Real.sqrt (1 + ‖gradient u x‖ ^ 2)) ∂volume := by
  rw [scalar_graph_area_formula hΩ.measurableSet
    (fun x hx ↦ ((hu.differentiableOn one_ne_zero) x hx).differentiableAt (hΩ.mem_nhds hx))]
  apply lintegral_congr
  intro x
  rw [← toDual_gradient]
  simp only [LinearIsometryEquiv.norm_map]

end
end Poincare.SimonGMT.Chapter02
