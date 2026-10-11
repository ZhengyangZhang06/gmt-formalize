module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Poincare.SimonGMT.Chapter02.Submanifold

public section

/-!
# Simon GMT, Chapter 2, §4: tangential gradient and divergence

This module formalizes the coordinate-free content of Simon (4.16)--(4.20).
For a tangent plane `T`, the tangential gradient is the orthogonal projection
of the ambient gradient onto `T`.  Tangential divergence is the trace of the
ambient derivative after orthogonal projection to `T`.  We prove both of
Simon's displayed coordinate formulas: expansion in an ambient orthonormal
basis and the trace formula in an orthonormal basis of `T`.
-/

open InnerProductSpace Module
open scoped Gradient

namespace Poincare.SimonGMT.Chapter02

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Simon (4.15), at a point where all directional derivatives exist: the
induced differential is a continuous linear map on the tangent plane. -/
abbrev TangentialDifferential (T : Submodule ℝ E) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] :=
  T →L[ℝ] F

/-- The induced tangential differential of an ambient map, obtained by
restricting its Fréchet derivative to the tangent plane. -/
noncomputable def ambientTangentialDifferential
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : Submodule ℝ E) (f : E → F) (x : E) :
    TangentialDifferential T F :=
  (fderiv ℝ f x).domRestrict T

/-- Simon (4.16), intrinsically: the tangential gradient is the Riesz vector
representing a real-valued tangential differential. -/
noncomputable def tangentialGradientOfDifferential (T : Submodule ℝ E)
    (df : TangentialDifferential T ℝ) : E :=
  (((toDual ℝ T).symm df : T) : E)

/-- The orthonormal-basis formula in Simon (4.16). -/
theorem tangentialGradientOfDifferential_eq_sum
    {ι : Type*} [Fintype ι] {T : Submodule ℝ E}
    (b : OrthonormalBasis ι ℝ T) (df : TangentialDifferential T ℝ) :
    tangentialGradientOfDifferential T df =
      ∑ i, df (b i) • (b i : E) := by
  let v : T := (toDual ℝ T).symm df
  have hdf (i : ι) : df (b i) = inner ℝ v (b i) := by
    simp [v]
  simp_rw [hdf]
  have hv : v = ∑ i, inner ℝ v (b i) • b i := by
    calc
      v = ∑ i, inner ℝ (b i) v • b i := (b.sum_repr' v).symm
      _ = ∑ i, inner ℝ v (b i) • b i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_comm]
  calc
    (v : E) = ((∑ i, inner ℝ v (b i) • b i : T) : E) :=
      congrArg Subtype.val hv
    _ = ∑ i, inner ℝ v (b i) • (b i : E) := by simp

/-- Simon (4.18), intrinsically: divergence is the trace of a tangential
differential after projecting its values back to the tangent plane. -/
noncomputable def tangentialDivergenceOfDifferential (T : Submodule ℝ E)
    (dX : TangentialDifferential T E) : ℝ :=
  LinearMap.trace ℝ T
    (T.orthogonalProjectionOnto.toLinearMap.comp dX.toLinearMap)

/-- Simon (4.20) directly for an induced tangential differential. -/
theorem tangentialDivergenceOfDifferential_eq_sum_inner
    {ι : Type*} [Fintype ι] {T : Submodule ℝ E}
    (b : OrthonormalBasis ι ℝ T) (dX : TangentialDifferential T E) :
    tangentialDivergenceOfDifferential T dX =
      ∑ i, inner ℝ (b i : E) (dX (b i)) := by
  rw [tangentialDivergenceOfDifferential,
    LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ (b i)
      (T.orthogonalProjectionOnto (dX (b i))) = _
  exact T.inner_orthogonalProjectionOnto_eq_of_mem_left (b i) (dX (b i))

/-- Simon (4.16): the tangential gradient is the orthogonal projection of the
ambient gradient onto the tangent plane. -/
noncomputable def tangentialGradientAt (T : Submodule ℝ E)
    (f : E → ℝ) (x : E) : E :=
  T.starProjection (gradient f x)

/-- Restricting the ambient differential and applying the intrinsic Riesz
definition gives the orthogonal projection of the ambient gradient. -/
theorem tangentialGradientOfDifferential_ambient
    (T : Submodule ℝ E) (f : E → ℝ) (x : E) :
    tangentialGradientOfDifferential T
        (ambientTangentialDifferential T f x) =
      tangentialGradientAt T f x := by
  let v : T := (toDual ℝ T).symm (ambientTangentialDifferential T f x)
  change (v : E) = T.starProjection (gradient f x)
  rw [T.starProjection_apply]
  congr 1
  apply (toDual ℝ T).injective
  ext t
  calc
    (toDual ℝ T v) t = ambientTangentialDifferential T f x t := by
      simp [v]
    _ = fderiv ℝ f x (t : E) := rfl
    _ = inner ℝ (gradient f x) (t : E) := by
      rw [inner_gradient_left]
    _ = inner ℝ (T.orthogonalProjectionOnto (gradient f x)) t := by
      rw [T.inner_orthogonalProjectionOnto_eq_of_mem_right]
    _ = (toDual ℝ T (T.orthogonalProjectionOnto (gradient f x))) t := by
      rw [toDual_apply_apply]

/-- Simon (4.18): divergence along a tangent plane, expressed without a
choice of coordinates as the trace of `DX` after tangential projection. -/
noncomputable def submanifoldDivergenceAt (T : Submodule ℝ E)
    (X : E → E) (x : E) : ℝ :=
  LinearMap.trace ℝ E
    ((fderiv ℝ X x).toLinearMap.comp T.starProjection.toLinearMap)

/-- Tangential divergence is additive in the ambient vector field at every
point where the two fields are differentiable. -/
theorem submanifoldDivergenceAt_add
    (T : Submodule ℝ E) {X Y : E → E} {x : E}
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x) :
    submanifoldDivergenceAt T (X + Y) x =
      submanifoldDivergenceAt T X x + submanifoldDivergenceAt T Y x := by
  rw [submanifoldDivergenceAt, submanifoldDivergenceAt,
    submanifoldDivergenceAt, fderiv_add hX hY]
  change LinearMap.trace ℝ E
      (((fderiv ℝ X x).toLinearMap + (fderiv ℝ Y x).toLinearMap).comp
        T.starProjection.toLinearMap) = _
  rw [LinearMap.add_comp, map_add]

/-- Tangential divergence is compatible with subtraction. -/
theorem submanifoldDivergenceAt_sub
    (T : Submodule ℝ E) {X Y : E → E} {x : E}
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x) :
    submanifoldDivergenceAt T (X - Y) x =
      submanifoldDivergenceAt T X x - submanifoldDivergenceAt T Y x := by
  rw [submanifoldDivergenceAt, submanifoldDivergenceAt,
    submanifoldDivergenceAt, fderiv_sub hX hY]
  change LinearMap.trace ℝ E
      (((fderiv ℝ X x).toLinearMap - (fderiv ℝ Y x).toLinearMap).comp
        T.starProjection.toLinearMap) = _
  rw [LinearMap.sub_comp, map_sub]

/-- The ambient and intrinsic definitions of tangential divergence agree. -/
theorem tangentialDivergenceOfDifferential_ambient
    (T : Submodule ℝ E) (X : E → E) (x : E) :
    tangentialDivergenceOfDifferential T
        (ambientTangentialDifferential T X x) =
      submanifoldDivergenceAt T X x := by
  let D : E →ₗ[ℝ] E := (fderiv ℝ X x).toLinearMap
  let q : E →ₗ[ℝ] T := T.orthogonalProjectionOnto.toLinearMap
  let i : T →ₗ[ℝ] E := T.subtype
  have hp : i.comp q = T.starProjection.toLinearMap := by
    rfl
  calc
    tangentialDivergenceOfDifferential T
        (ambientTangentialDifferential T X x) =
        LinearMap.trace ℝ T (q.comp (D.comp i)) := by
      rfl
    _ = LinearMap.trace ℝ E ((D.comp i).comp q) :=
      (LinearMap.trace_comp_comm' q (D.comp i)).symm
    _ = LinearMap.trace ℝ E (D.comp (i.comp q)) := by
      rw [LinearMap.comp_assoc]
    _ = submanifoldDivergenceAt T X x := by
      rw [submanifoldDivergenceAt, hp]

/-- Simon (4.17): the tangential gradient has the usual coordinate expansion
in every ambient orthonormal basis. -/
theorem tangentialGradientAt_eq_sum_coordinates
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E)
    (T : Submodule ℝ E) (f : E → ℝ) (x : E) :
    tangentialGradientAt T f x =
      ∑ j, inner ℝ (e j) (tangentialGradientAt T f x) • e j := by
  exact (e.sum_repr' (tangentialGradientAt T f x)).symm

/-- Simon (4.20): tangential divergence is the sum of the directional
derivatives in any orthonormal basis of the tangent plane. -/
theorem submanifoldDivergenceAt_eq_sum_inner
    {ι : Type*} [Fintype ι] {T : Submodule ℝ E}
    (b : OrthonormalBasis ι ℝ T)
    (X : E → E) (x : E) :
    submanifoldDivergenceAt T X x =
      ∑ i, inner ℝ (b i : E) ((fderiv ℝ X x) (b i : E)) := by
  let D : E →ₗ[ℝ] E := (fderiv ℝ X x).toLinearMap
  let q : E →ₗ[ℝ] T := T.orthogonalProjectionOnto.toLinearMap
  let i : T →ₗ[ℝ] E := T.subtype
  have hp : i.comp q = T.starProjection.toLinearMap := by
    rfl
  calc
    submanifoldDivergenceAt T X x =
        LinearMap.trace ℝ E (D.comp (i.comp q)) := by
      rw [submanifoldDivergenceAt, hp]
    _ = LinearMap.trace ℝ E ((D.comp i).comp q) := by
      rw [LinearMap.comp_assoc]
    _ = LinearMap.trace ℝ T (q.comp (D.comp i)) :=
      LinearMap.trace_comp_comm' q (D.comp i)
    _ = ∑ j, inner ℝ (b j) ((q.comp (D.comp i)) (b j)) :=
      LinearMap.trace_eq_sum_inner _ b
    _ = ∑ j, inner ℝ (b j : E) (D (b j : E)) := by
      apply Finset.sum_congr rfl
      intro j _
      change inner ℝ (b j) (T.orthogonalProjectionOnto (D (b j : E))) = _
      exact T.inner_orthogonalProjectionOnto_eq_of_mem_left (b j) (D (b j : E))
    _ = ∑ j, inner ℝ (b j : E) ((fderiv ℝ X x) (b j : E)) := rfl

/-- Simon (4.18)--(4.19): in an ambient orthonormal basis, tangential
divergence is the sum of the tangential derivatives of the coordinate
functions of the vector field. -/
theorem submanifoldDivergenceAt_eq_sum_tangentialGradient
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E)
    (T : Submodule ℝ E) {X : E → E} {x : E}
    (hX : DifferentiableAt ℝ X x) :
    submanifoldDivergenceAt T X x =
      ∑ j, inner ℝ (e j)
        (tangentialGradientAt T (fun y ↦ inner ℝ (e j) (X y)) x) := by
  let D : E →ₗ[ℝ] E := (fderiv ℝ X x).toLinearMap
  rw [submanifoldDivergenceAt, LinearMap.trace_eq_sum_inner _ e]
  apply Finset.sum_congr rfl
  intro j _
  let f : E → ℝ := (innerSL ℝ (e j)) ∘ X
  have hf : HasFDerivAt f ((innerSL ℝ (e j)).comp (fderiv ℝ X x)) x := by
    exact (innerSL ℝ (e j)).hasFDerivAt.comp x hX.hasFDerivAt
  calc
    inner ℝ (e j) ((fderiv ℝ X x) (T.starProjection (e j))) =
        fderiv ℝ f x (T.starProjection (e j)) := by
      rw [hf.fderiv]
      rfl
    _ = inner ℝ (gradient f x) (T.starProjection (e j)) := by
      rw [inner_gradient_left]
    _ = inner ℝ (T.starProjection (e j)) (gradient f x) :=
      real_inner_comm _ _
    _ = inner ℝ (e j) (T.starProjection (gradient f x)) :=
      T.inner_starProjection_left_eq_right (e j) (gradient f x)
    _ = inner ℝ (e j) (tangentialGradientAt T f x) := rfl

/-- Simon (4.12): the area Jacobian of a linear tangential differential. -/
noncomputable def tangentialAreaJacobian
    {F G : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (A : F →ₗ[ℝ] G) : ℝ :=
  A.normDet

/-- The algebraic Jacobian factorization in Simon (4.11).  Here `L` is the
derivative of a local parametrization and `A.domRestrict L.range` is the
induced differential on its tangent space. -/
theorem areaJacobian_comp_eq_parametrization_mul_tangential
    {F G : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (L : E →ₗ[ℝ] F) (A : F →ₗ[ℝ] G) :
    (A.comp L).normDet =
      L.normDet * tangentialAreaJacobian (A.domRestrict L.range) := by
  rw [tangentialAreaJacobian, L.normDet_comp A, mul_comm]

end Poincare.SimonGMT.Chapter02
