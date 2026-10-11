module

public import Poincare.SimonGMT.Chapter08.FirstVariationRiesz
public import Poincare.SimonGMT.Chapter04.FirstVariation
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Radial first variation on the Grassmann bundle

The projection and differentiation calculations in Simon (8.3.2), with
both the literal radial profile and the globally smooth squared-radius
profile. All projections are the actual projection matrices of the
Grassmannian. The weighted product rule supplies the pointwise input to
(8.3.5); no monotonicity or integrated identity is assumed.

Source: `Simon-gmt new.pdf`, printed pp. 210--211, PDF object 217.
-/

open Set Filter MeasureTheory Function
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {N n : ℕ}

namespace Grassmannian

theorem projectionLinearMap_eq_starProjection (S : Grassmannian N n) :
    S.projectionLinearMap = S.plane.starProjection.toLinearMap := by
  have hs : S.projectionLinearMap.IsSymmetricProjection :=
    ⟨S.projectionLinearMap_comp_self, S.projectionLinearMap_isSymmetric⟩
  obtain ⟨_, hp⟩ :=
    (LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range).mp hs
  exact hp

theorem project_eq_starProjection (S : Grassmannian N n) (v : Euclidean N) :
    S.project v = S.plane.starProjection v :=
  congrArg (fun f : Euclidean N →ₗ[ℝ] Euclidean N ↦ f v)
    S.projectionLinearMap_eq_starProjection

/-- Orthogonal projection onto the normal complement of the plane. -/
def normalProject (S : Grassmannian N n) (v : Euclidean N) : Euclidean N :=
  S.planeᗮ.starProjection v

theorem norm_project_sq_add_norm_normalProject_sq (S : Grassmannian N n) (v : Euclidean N) :
    ‖S.project v‖ ^ 2 + ‖S.normalProject v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [project_eq_starProjection]
  exact (S.plane.norm_sq_eq_add_norm_sq_starProjection v).symm

theorem inner_project_eq_norm_sq (S : Grassmannian N n) (v : Euclidean N) :
    inner ℝ v (S.project v) = ‖S.project v‖ ^ 2 := by
  rw [project_eq_starProjection]
  exact Chapter04.RectifiableVarifold.inner_starProjection_eq_norm_sq S.plane v

theorem project_apply (S : Grassmannian N n) (v : Euclidean N) (i : Fin N) :
    S.project v i = ∑ j : Fin N, S.1 i j * v j := by
  have hh := LinearMap.toMatrix_mulVec_repr coordinateBasis.toBasis coordinateBasis.toBasis
    S.projectionLinearMap v
  rw [toMatrix_projectionLinearMap] at hh
  exact (congrFun hh i).symm

/-- The displayed projection-matrix quadratic form is the squared norm
of the tangent projection; this uses the actual matrix entries of `S`. -/
theorem projection_matrix_quadratic (S : Grassmannian N n) (v : Euclidean N) :
    (∑ i : Fin N, ∑ j : Fin N, S.1 i j * v i * v j) = ‖S.project v‖ ^ 2 := by
  rw [← S.inner_project_eq_norm_sq, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [S.project_apply]
  simp only [RCLike.inner_apply, conj_trivial, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem normalProject_eq_sub (S : Grassmannian N n) (v : Euclidean N) :
    S.normalProject v = v - S.project v := by
  rw [normalProject, Submodule.starProjection_orthogonal_val, S.project_eq_starProjection]

theorem continuous_project :
    Continuous (fun p : Grassmannian N n × Euclidean N ↦ p.1.project p.2) := by
  have heq : (fun p : Grassmannian N n × Euclidean N ↦ p.1.project p.2) =
      fun p ↦ WithLp.toLp 2 (fun i ↦ ∑ j : Fin N, p.1.1 i j * p.2 j) := by
    funext p
    ext i
    exact project_apply p.1 p.2 i
  rw [heq]
  apply (PiLp.continuous_toLp 2 (fun _ : Fin N ↦ ℝ)).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp ((continuous_apply i).comp
    (continuous_subtype_val.comp continuous_fst))).mul
    ((continuous_apply j).comp ((PiLp.continuous_ofLp 2 (fun _ : Fin N ↦ ℝ)).comp continuous_snd))

theorem continuous_normalProject :
    Continuous (fun p : Grassmannian N n × Euclidean N ↦ p.1.normalProject p.2) := by
  simp_rw [normalProject_eq_sub]
  exact continuous_snd.sub continuous_project

/-- Simon's normalized normal-radial defect. Its value at the centre is
zero, following Lean's total division convention. -/
def radialNormalSq (S : Grassmannian N n) (ξ y : Euclidean N) : ℝ :=
  ‖S.normalProject (‖y - ξ‖⁻¹ • (y - ξ))‖ ^ 2

theorem radialNormalSq_nonneg (S : Grassmannian N n) (ξ y : Euclidean N) :
    0 ≤ S.radialNormalSq ξ y := sq_nonneg _

theorem measurable_radialNormalSq (ξ : Euclidean N) :
    Measurable (fun z : Euclidean N × Grassmannian N n ↦ z.2.radialNormalSq ξ z.1) := by
  have hp : Measurable (fun z : Euclidean N × Grassmannian N n ↦
      (z.2, ‖z.1 - ξ‖⁻¹ • (z.1 - ξ))) :=
    measurable_snd.prodMk
      (((measurable_fst.sub_const ξ).norm.inv).smul (measurable_fst.sub_const ξ))
  exact ((continuous_normalProject.measurable.comp hp).norm).pow_const 2

theorem norm_normalProject_radial_sq (S : Grassmannian N n) (ξ y : Euclidean N) :
    ‖S.normalProject (y - ξ)‖ ^ 2 = ‖y - ξ‖ ^ 2 * S.radialNormalSq ξ y := by
  simp only [radialNormalSq, normalProject, map_smul, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  by_cases hy : y - ξ = 0
  · simp [hy]
  · field_simp [norm_ne_zero_iff.mpr hy]

theorem norm_project_radial_sq (S : Grassmannian N n) (ξ y : Euclidean N) :
    ‖S.project (y - ξ)‖ ^ 2 = ‖y - ξ‖ ^ 2 * (1 - S.radialNormalSq ξ y) := by
  have h := S.norm_project_sq_add_norm_normalProject_sq (y - ξ)
  rw [S.norm_normalProject_radial_sq] at h
  nlinarith

theorem radialNormalSq_le_one (S : Grassmannian N n) (ξ y : Euclidean N) :
    S.radialNormalSq ξ y ≤ 1 := by
  by_cases hy : y = ξ
  · simp [radialNormalSq, normalProject, hy]
  have h := S.norm_project_radial_sq ξ y
  have hn : 0 < ‖y - ξ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hy))
  nlinarith [sq_nonneg ‖S.project (y - ξ)‖]

/-- The projection-matrix identity printed between (8.3.2) and (8.3.3),
with the source's two factors `(ξᵢ-yᵢ)/r`. -/
theorem projection_matrix_radial (S : Grassmannian N n) (ξ y : Euclidean N) (hy : y ≠ ξ) :
    (∑ i : Fin N, ∑ j : Fin N, S.1 i j * ((ξ i - y i) / ‖y - ξ‖) *
      ((ξ j - y j) / ‖y - ξ‖)) = 1 - S.radialNormalSq ξ y := by
  have hn : ‖y - ξ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy)
  have heq : (∑ i : Fin N, ∑ j : Fin N, S.1 i j * ((ξ i - y i) / ‖y - ξ‖) *
      ((ξ j - y j) / ‖y - ξ‖)) =
      (∑ i : Fin N, ∑ j : Fin N, S.1 i j * (y - ξ) i * (y - ξ) j) / ‖y - ξ‖ ^ 2 := by
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [PiLp.sub_apply]
    ring
  rw [heq, S.projection_matrix_quadratic, S.norm_project_radial_sq]
  field_simp

end Grassmannian

namespace Varifold

theorem tangentialDivergence_eq_trace (X : Euclidean N → Euclidean N)
    (y : Euclidean N) (S : Grassmannian N n) :
    tangentialDivergence X y S = LinearMap.trace ℝ (Euclidean N)
      ((fderiv ℝ X y).toLinearMap.comp S.plane.starProjection.toLinearMap) := by
  rw [← S.projectionLinearMap_eq_starProjection,
    LinearMap.trace_eq_matrix_trace ℝ Grassmannian.coordinateBasis.toBasis,
    LinearMap.toMatrix_comp Grassmannian.coordinateBasis.toBasis
      Grassmannian.coordinateBasis.toBasis Grassmannian.coordinateBasis.toBasis,
    Grassmannian.toMatrix_projectionLinearMap]
  rw [tangentialDivergence, jacobian_eq_toMatrix, Matrix.trace_mul_comm]

/-- The literal source field `X(y) = γ(|y-ξ|)(y-ξ)`. -/
def radialVectorField (ξ : Euclidean N) (γ : ℝ → ℝ) (y : Euclidean N) : Euclidean N :=
  γ ‖y - ξ‖ • (y - ξ)

theorem hasFDerivAt_radius (ξ y : Euclidean N) (hy : y ≠ ξ) :
    HasFDerivAt (fun z ↦ ‖z - ξ‖) (‖y - ξ‖⁻¹ • innerSL ℝ (y - ξ)) y := by
  have hd := (hasFDerivAt_sub_const (x := y) ξ).norm_sq
  have hn : ‖y - ξ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy)
  have hh := hd.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg _), ContinuousLinearMap.comp_id] at hh
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply, smul_eq_mul, two_smul, add_apply]
  field_simp
  ring

theorem hasFDerivAt_radialVectorField (ξ y : Euclidean N) (hy : y ≠ ξ)
    {γ : ℝ → ℝ} {γ' : ℝ} (hγ : HasDerivAt γ γ' ‖y - ξ‖) :
    HasFDerivAt (radialVectorField ξ γ)
      (γ ‖y - ξ‖ • ContinuousLinearMap.id ℝ (Euclidean N) +
        (γ' / ‖y - ξ‖) • (innerSL ℝ (y - ξ)).smulRight (y - ξ)) y := by
  have hh := (hγ.comp_hasFDerivAt y (hasFDerivAt_radius ξ y hy)).smul
    (hasFDerivAt_sub_const (x := y) ξ)
  convert hh using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro v
    simp [div_eq_mul_inv, mul_smul]

/-- Simon (8.3.2), in its intrinsic projection form, at the nonzero
radii where the printed unit radial vector is defined. -/
theorem tangentialDivergence_radialVectorField (ξ y : Euclidean N)
    (S : Grassmannian N n) (hy : y ≠ ξ) {γ : ℝ → ℝ} {γ' : ℝ}
    (hγ : HasDerivAt γ γ' ‖y - ξ‖) :
    tangentialDivergence (radialVectorField ξ γ) y S =
      n * γ ‖y - ξ‖ + (γ' / ‖y - ξ‖) * ‖S.project (y - ξ)‖ ^ 2 := by
  rw [tangentialDivergence_eq_trace, (hasFDerivAt_radialVectorField ξ y hy hγ).fderiv,
    Chapter04.RectifiableVarifold.trace_radialEndomorphism, S.finrank_plane,
    innerSL_apply_apply, Chapter04.RectifiableVarifold.inner_starProjection_eq_norm_sq,
    ← S.project_eq_starProjection]
  ring

/-- The normal-radial expression used immediately after (8.3.2). -/
theorem tangentialDivergence_radialVectorField_normal (ξ y : Euclidean N)
    (S : Grassmannian N n) (hy : y ≠ ξ) {γ : ℝ → ℝ} {γ' : ℝ}
    (hγ : HasDerivAt γ γ' ‖y - ξ‖) :
    tangentialDivergence (radialVectorField ξ γ) y S =
      n * γ ‖y - ξ‖ + ‖y - ξ‖ * γ' * (1 - S.radialNormalSq ξ y) := by
  rw [tangentialDivergence_radialVectorField ξ y S hy hγ, S.norm_project_radial_sq]
  field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy)]

/-- Simon (8.3.2), literally in the printed projection-matrix coordinates. -/
theorem tangentialDivergence_radialVectorField_matrix (ξ y : Euclidean N)
    (S : Grassmannian N n) (hy : y ≠ ξ) {γ : ℝ → ℝ} {γ' : ℝ}
    (hγ : HasDerivAt γ γ' ‖y - ξ‖) :
    tangentialDivergence (radialVectorField ξ γ) y S =
      n * γ ‖y - ξ‖ + ‖y - ξ‖ * γ' *
        (∑ i : Fin N, ∑ j : Fin N, S.1 i j * ((ξ i - y i) / ‖y - ξ‖) *
          ((ξ j - y j) / ‖y - ξ‖)) := by
  rw [S.projection_matrix_radial ξ y hy]
  exact tangentialDivergence_radialVectorField_normal ξ y S hy hγ

/-- The same identity for a squared-radius profile, valid at the centre
as well and requiring no differentiability of the norm there. -/
theorem tangentialDivergence_squaredRadialVectorField (ξ y : Euclidean N)
    (S : Grassmannian N n) {η : ℝ → ℝ} {η' : ℝ}
    (hη : HasDerivAt η η' (‖y - ξ‖ ^ 2)) :
    tangentialDivergence (Chapter04.RectifiableVarifold.squaredRadialVectorField ξ η) y S =
      n * η (‖y - ξ‖ ^ 2) + 2 * η' * ‖S.project (y - ξ)‖ ^ 2 := by
  rw [tangentialDivergence_eq_trace,
    (Chapter04.RectifiableVarifold.hasFDerivAt_squaredRadialVectorField ξ y hη).fderiv,
    Chapter04.RectifiableVarifold.trace_radialEndomorphism, S.finrank_plane,
    innerSL_apply_apply, Chapter04.RectifiableVarifold.inner_starProjection_eq_norm_sq,
    ← S.project_eq_starProjection]
  ring

/-- Weighted tangential product rule, the geometric input to (8.3.5). -/
theorem tangentialDivergence_smul (h : Euclidean N → ℝ) (X : Euclidean N → Euclidean N)
    (y : Euclidean N) (S : Grassmannian N n)
    (hh : DifferentiableAt ℝ h y) (hX : DifferentiableAt ℝ X y) :
    tangentialDivergence (fun z ↦ h z • X z) y S =
      h y * tangentialDivergence X y S + (fderiv ℝ h y) (S.project (X y)) := by
  change tangentialDivergence (h • X) y S = _
  rw [tangentialDivergence_eq_trace, tangentialDivergence_eq_trace, fderiv_smul hh hX]
  change LinearMap.trace ℝ (Euclidean N)
    (((h y • (fderiv ℝ X y).toLinearMap) +
      (fderiv ℝ h y).toLinearMap.smulRight (X y)).comp S.plane.starProjection.toLinearMap) = _
  rw [LinearMap.add_comp, LinearMap.smul_comp, map_add, map_smul]
  have heq : ((fderiv ℝ h y).toLinearMap.smulRight (X y)).comp
      S.plane.starProjection.toLinearMap =
      ((fderiv ℝ h y).toLinearMap.comp S.plane.starProjection.toLinearMap).smulRight (X y) := by
    rfl
  rw [heq, LinearMap.trace_smulRight, S.project_eq_starProjection]
  rfl

end Varifold
end
end Poincare.SimonGMT.Chapter08
