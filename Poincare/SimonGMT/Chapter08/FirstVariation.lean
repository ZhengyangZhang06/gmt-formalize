module

public import Poincare.SimonGMT.Chapter08.Varifold
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Simon GMT, Chapter 8, §2: differentiating tangential Jacobians

The pointwise calculation underlying (8.2.2)--(8.2.3) is proved for the
variation `φₜ(x) = x + t X(x)`.  It uses the exact quadratic Gram matrix of
the restricted derivative and the linear coefficient of its determinant.
`FirstVariationIntegral` supplies the integral and pushforward-mass steps,
deriving measurability from the ambient projection-matrix formulas.
`DeformationIntegral` proves independence from arbitrary jointly `C²`
deformation families on the open domain.

Source: `Simon-gmt new.pdf`, printed pp. 208--209.
-/

open scoped Polynomial
open Matrix

namespace Poincare.SimonGMT.Chapter08

/-- Equality of constant and linear coefficients is preserved by a finite
product.  This isolates the elementary coefficient calculation used in the
Gram-determinant proof of Simon (8.2.3). -/
theorem coeff_one_prod_congr {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (f g : ι → R[X])
    (h0 : ∀ i ∈ s, (f i).coeff 0 = (g i).coeff 0)
    (h1 : ∀ i ∈ s, (f i).coeff 1 = (g i).coeff 1) :
    (∏ i ∈ s, f i).coeff 1 = (∏ i ∈ s, g i).coeff 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, Polynomial.mul_coeff_one]
      rw [h0 a (Finset.mem_insert_self a s), h1 a (Finset.mem_insert_self a s)]
      rw [ih (fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ h1 i (Finset.mem_insert_of_mem hi))]
      have hp0 : (∏ i ∈ s, f i).coeff 0 = (∏ i ∈ s, g i).coeff 0 := by
        simp only [Polynomial.coeff_zero_prod]
        exact Finset.prod_congr rfl fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
      rw [hp0]

/-- The derivative at zero of `det(I + t A + t² B)` is `trace A`.
This is the determinant calculation needed for Simon (8.2.3). -/
theorem derivative_eval_zero_det_one_add_X_smul_add_sq_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) :
    (Matrix.det (1 + (Polynomial.X : ℝ[X]) • A.map Polynomial.C +
      (Polynomial.X : ℝ[X]) ^ 2 • B.map Polynomial.C)).derivative.eval 0 =
        Matrix.trace A := by
  let p : ℝ[X] := Matrix.det (1 + (Polynomial.X : ℝ[X]) • A.map Polynomial.C +
      (Polynomial.X : ℝ[X]) ^ 2 • B.map Polynomial.C)
  change p.derivative.eval 0 = _
  rw [← Polynomial.taylor_coeff_one (r := (0 : ℝ)) (f := p), Polynomial.taylor_zero]
  have hcoeff : p.coeff 1 =
      (Matrix.det (1 + (Polynomial.X : ℝ[X]) • A.map Polynomial.C)).coeff 1 := by
    simp only [p, Matrix.det_apply]
    change (Polynomial.lcoeff ℝ 1) (∑ σ, Equiv.Perm.sign σ • ∏ i,
      (1 + (Polynomial.X : ℝ[X]) • A.map Polynomial.C +
        (Polynomial.X : ℝ[X]) ^ 2 • B.map Polynomial.C) (σ i) i) =
      (Polynomial.lcoeff ℝ 1) (∑ σ, Equiv.Perm.sign σ • ∏ i,
      (1 + (Polynomial.X : ℝ[X]) • A.map Polynomial.C) (σ i) i)
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    change (Equiv.Perm.sign σ : ℤ) •
        (∏ i, (1 + (Polynomial.X : ℝ[X]) • A.map Polynomial.C +
          (Polynomial.X : ℝ[X]) ^ 2 • B.map Polynomial.C) (σ i) i).coeff 1 =
      (Equiv.Perm.sign σ : ℤ) •
        (∏ i, (1 + (Polynomial.X : ℝ[X]) • A.map Polynomial.C) (σ i) i).coeff 1
    congr 1
    apply coeff_one_prod_congr Finset.univ
    · intro i hi
      simp
    · intro i hi
      simp
  rw [hcoeff, Matrix.coeff_det_one_add_X_smul_one]

namespace Varifold

noncomputable section

/-- Simon (8.2.2)--(8.2.3), pointwise Jacobian calculation for `id + t X`:
`d/dt J_S(id + t X)(x)|ₜ₌₀ = div_S X(x)`.  Only differentiability of `X`
at the point is needed for this part of the first-variation argument. -/
theorem hasDerivAt_tangentialJacobianReal_id_add_smul
    {N n : ℕ} (X : Euclidean N → Euclidean N) (x : Euclidean N)
    (S : Grassmannian N n) (hX : DifferentiableAt ℝ X x) :
    HasDerivAt
      (fun t : ℝ ↦ tangentialJacobianReal (fun y ↦ y + t • X y) x S)
      (tangentialDivergence X x S) 0 := by
  let b : OrthonormalBasis (Fin n) ℝ S.plane :=
    (stdOrthonormalBasis ℝ S.plane).reindex (finCongr S.finrank_plane)
  let D : S.plane →ₗ[ℝ] Euclidean N :=
    (fderiv ℝ X x).toLinearMap.domRestrict S.plane
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j ↦
    inner ℝ (D (b i)) (b j : Euclidean N) +
      inner ℝ (b i : Euclidean N) (D (b j))
  let B : Matrix (Fin n) (Fin n) ℝ := fun i j ↦
    inner ℝ (D (b i)) (D (b j))
  let p : ℝ[X] := Matrix.det
    (1 + (Polynomial.X : ℝ[X]) • A.map Polynomial.C +
      (Polynomial.X : ℝ[X]) ^ 2 • B.map Polynomial.C)
  have hflow (t : ℝ) : tangentialDerivative (fun y ↦ y + t • X y) x S =
      S.plane.subtype + t • D := by
    apply LinearMap.ext
    intro v
    change (fderiv ℝ (id + t • X) x) (v : Euclidean N) = _
    have hf := (hasFDerivAt_id x).add (hX.hasFDerivAt.const_smul t)
    rw [hf.fderiv]
    rfl
  have hsquare (t : ℝ) :
      tangentialJacobianReal (fun y ↦ y + t • X y) x S ^ 2 = p.eval t := by
    change (tangentialDerivative (fun y ↦ y + t • X y) x S).normDet ^ 2 = _
    calc
      _ = (Matrix.gram ℝ
          (tangentialDerivative (fun y ↦ y + t • X y) x S <| b ·)).det := by
        simpa using LinearMap.normDet_sq_eq_det_gram
          (tangentialDerivative (fun y ↦ y + t • X y) x S) b
      _ = p.eval t := by
        change _ = (Polynomial.evalRingHom t) (Matrix.det
          (1 + (Polynomial.X : ℝ[X]) • A.map Polynomial.C +
            (Polynomial.X : ℝ[X]) ^ 2 • B.map Polynomial.C))
        rw [RingHom.map_det]
        congr 1
        ext i j
        rw [hflow]
        have hb : inner ℝ (b i : Euclidean N) (b j : Euclidean N) =
            if i = j then 1 else 0 := b.inner_eq_ite i j
        change inner ℝ ((b i : Euclidean N) + t • D (b i))
            ((b j : Euclidean N) + t • D (b j)) =
          Polynomial.eval t ((1 : Matrix (Fin n) (Fin n) ℝ[X]) i j +
            Polynomial.X * Polynomial.C (A i j) +
            Polynomial.X ^ 2 * Polynomial.C (B i j))
        simp [Matrix.one_apply, A, B, inner_add_left, inner_add_right,
          inner_smul_left, inner_smul_right, hb, apply_ite]
        ring
  have hpderiv : HasDerivAt (fun t : ℝ ↦ p.eval t) (Matrix.trace A) 0 := by
    convert p.hasDerivAt 0 using 1
    simpa [p] using (derivative_eval_zero_det_one_add_X_smul_add_sq_smul A B).symm
  have hp0 : p.eval 0 = 1 := by
    rw [← hsquare 0]
    simp
  have hsqrt : (fun t : ℝ ↦
      tangentialJacobianReal (fun y ↦ y + t • X y) x S) =
      fun t ↦ Real.sqrt (p.eval t) := by
    funext t
    rw [← hsquare t, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (tangentialJacobianReal_nonneg _ _ _)]
  rw [hsqrt]
  convert hpderiv.sqrt (by simp [hp0]) using 1
  rw [hp0]
  simp only [Real.sqrt_one, mul_one]
  have htrace : Matrix.trace A = 2 * tangentialDivergence X x S := by
    rw [tangentialDivergence_eq_sum_inner X x S b]
    change (∑ i, (inner ℝ ((fderiv ℝ X x) (b i : Euclidean N))
        (b i : Euclidean N) + inner ℝ (b i : Euclidean N)
          ((fderiv ℝ X x) (b i : Euclidean N)))) =
      2 * ∑ i, inner ℝ (b i : Euclidean N)
        ((fderiv ℝ X x) (b i : Euclidean N))
    simp_rw [real_inner_comm ((fderiv ℝ X x) (b _ : Euclidean N))]
    rw [two_mul, Finset.sum_add_distrib]
  rw [htrace]
  ring

end

end Varifold

end Poincare.SimonGMT.Chapter08
