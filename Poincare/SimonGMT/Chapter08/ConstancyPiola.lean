module

public import Poincare.SimonGMT.Chapter08.ConstancyCoordinateTests
public import Poincare.SimonGMT.Chapter08.ConstancyChartVariation
public import Poincare.SimonGMT.Chapter08.DeformationFamily

@[expose] public section

/-!
# The chart Jacobian and tangent coordinate divergence

The differential of the actual metric Jacobian is obtained from the
proved first variation of a plane Jacobian. No coordinate divergence
formula or weak equation is postulated.
-/

open Set Function Filter MeasureTheory
open scoped Topology

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {N n : ℕ}

namespace Varifold

/-- The derivative of the plane Jacobian at the identity is the
tangential trace, for every ambient linear perturbation. -/
theorem fderiv_linearTangentialJacobian_id (S : Grassmannian N n)
    (A : Euclidean N →L[ℝ] Euclidean N) :
    fderiv ℝ (linearTangentialJacobian S) (ContinuousLinearMap.id ℝ (Euclidean N)) A =
      LinearMap.trace ℝ (Euclidean N) (A.toLinearMap.comp S.plane.starProjection.toLinearMap) := by
  have hJ := ((contDiffAt_linearTangentialJacobian_id S).differentiableAt
    one_ne_zero).hasFDerivAt
  have haff : HasDerivAt
      (fun t : ℝ ↦ ContinuousLinearMap.id ℝ (Euclidean N) + t • A) A 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const A).const_add
      (ContinuousLinearMap.id ℝ (Euclidean N))
  have hd := hJ.comp_hasDerivAt_of_eq (0 : ℝ) haff
    (by ext v; simp only [add_apply, smul_apply,
      zero_smul, add_zero])
  have hh := hasDerivAt_tangentialJacobianReal_id_add_smul
    (fun x ↦ A x) 0 S A.differentiableAt
  have he (t : ℝ) : linearTangentialJacobian S
      (ContinuousLinearMap.id ℝ (Euclidean N) + t • A) =
      tangentialJacobianReal (fun y ↦ y + t • A y) 0 S := by
    rw [← linearTangentialJacobian_fderiv]
    congr 1
    exact ((hasFDerivAt_id (0 : Euclidean N)).add (A.hasFDerivAt.const_smul t)).fderiv.symm
  have h := (hd.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ (he t).symm)).unique hh
  simpa only [tangentialDivergence_eq_trace, A.fderiv] using h

/-- Exact factorization near a fixed immersion derivative. The auxiliary
left inverse is algebraic and does not change the metric Jacobian. -/
theorem normDet_eq_mul_linearTangentialJacobian_of_leftInverse
    (A B : Euclidean n →L[ℝ] Euclidean N)
    (R : Euclidean N →L[ℝ] Euclidean n)
    (hRA : R.comp A = ContinuousLinearMap.id ℝ (Euclidean n))
    (hinj : Injective A) :
    B.normDet = A.normDet * linearTangentialJacobian
      (Grassmannian.ofSubmodule (n := n) A.range (by
        simpa using LinearMap.finrank_range_of_inj hinj))
      (ContinuousLinearMap.id ℝ (Euclidean N) + (B - A).comp R) := by
  let S : Grassmannian N n := Grassmannian.ofSubmodule A.range (by
    simpa using LinearMap.finrank_range_of_inj hinj)
  let L := ContinuousLinearMap.id ℝ (Euclidean N) + (B - A).comp R
  have hcomp : L.comp A = B := by
    ext v
    have h := congrArg (fun T : Euclidean n →L[ℝ] Euclidean n ↦ T v) hRA
    change R (A v) = v at h
    simp [L, h]
  have hlin : linearTangentialJacobian S L =
      (L.toLinearMap.domRestrict A.range).normDet := by
    rw [← L.fderiv (x := (0 : Euclidean N)), linearTangentialJacobian_fderiv]
    change ((fderiv ℝ (fun x ↦ L x) 0).toLinearMap.domRestrict S.plane).normDet = _
    rw [show S.plane = A.range from Grassmannian.plane_ofSubmodule _ _]
  change B.normDet = A.normDet * linearTangentialJacobian S L
  rw [hlin, ← mul_comm (L.toLinearMap.domRestrict A.range).normDet]
  exact hcomp ▸ A.toLinearMap.normDet_comp L.toLinearMap

/-- The directional derivative of the actual chart Jacobian. It is
expressed by the Hessian of the chart and any left inverse at the point. -/
theorem fderiv_areaJacobianAt_apply_of_leftInverse
    {φ : Euclidean n → Euclidean N} {a : Euclidean n}
    (hφ : ContDiffAt ℝ 2 φ a) (hinj : Injective (fderiv ℝ φ a))
    (R : Euclidean N →L[ℝ] Euclidean n)
    (hRA : R.comp (fderiv ℝ φ a) = ContinuousLinearMap.id ℝ (Euclidean n))
    (v : Euclidean n) :
    fderiv ℝ (Chapter02.areaJacobianAt φ) a v = Chapter02.areaJacobianAt φ a *
      LinearMap.trace ℝ (Euclidean N)
        (((fderiv ℝ (fderiv ℝ φ) a v).comp R).toLinearMap.comp
          (fderiv ℝ φ a).range.starProjection.toLinearMap) := by
  let A := fderiv ℝ φ a
  let S : Grassmannian N n := Grassmannian.ofSubmodule A.range (by
    simpa [A] using LinearMap.finrank_range_of_inj hinj)
  let L (u : Euclidean n) := ContinuousLinearMap.id ℝ (Euclidean N) +
    (fderiv ℝ φ u - A).comp R
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) a :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hL : HasFDerivAt L
      ((ContinuousLinearMap.compL ℝ (Euclidean N) (Euclidean n) (Euclidean N)).flip R |>.comp
        (fderiv ℝ (fderiv ℝ φ) a)) a := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      (((hd.hasFDerivAt.sub_const A).clm_comp
        (hasFDerivAt_const R a)).const_add (ContinuousLinearMap.id ℝ (Euclidean N)))
  have hLa : L a = ContinuousLinearMap.id ℝ (Euclidean N) := by simp [L, A]
  have hJ₀ := ((contDiffAt_linearTangentialJacobian_id S).differentiableAt
    one_ne_zero).hasFDerivAt
  rw [← hLa] at hJ₀
  have hJ := hJ₀.comp a hL
  have heq : Chapter02.areaJacobianAt φ =
      fun u ↦ A.normDet * linearTangentialJacobian S (L u) := by
    funext u
    rw [Chapter02.areaJacobianAt_eq_normDet]
    exact normDet_eq_mul_linearTangentialJacobian_of_leftInverse A _ R hRA hinj
  have hder := (hJ.const_mul A.normDet).fderiv
  dsimp only [Function.comp_def] at hder
  rw [← heq] at hder
  rw [hder, hLa]
  change A.normDet *
      fderiv ℝ (linearTangentialJacobian S) (ContinuousLinearMap.id ℝ (Euclidean N))
        ((fderiv ℝ (fderiv ℝ φ) a v).comp R) = _
  rw [fderiv_linearTangentialJacobian_id]
  rw [show S.plane = A.range from Grassmannian.plane_ofSubmodule _ _]
  rfl

/-- Tangential trace of a coordinate product derivative. The rank-one
part gives the scalar directional derivative exactly. -/
theorem trace_projection_of_coordinate_product
    (A H : Euclidean n →L[ℝ] Euclidean N)
    (R : Euclidean N →L[ℝ] Euclidean n)
    (L : Euclidean N →L[ℝ] Euclidean N) (ℓ : Euclidean n →L[ℝ] ℝ)
    (c : ℝ) (v : Euclidean n)
    (hRA : R.comp A = ContinuousLinearMap.id ℝ (Euclidean n))
    (hLA : L.comp A = c • H + ℓ.smulRight (A v)) :
    LinearMap.trace ℝ (Euclidean N) (L.toLinearMap.comp A.range.starProjection.toLinearMap) =
      c * LinearMap.trace ℝ (Euclidean N)
        ((H.comp R).toLinearMap.comp A.range.starProjection.toLinearMap) + ℓ v := by
  let P := A.range.starProjection
  have hRA' (w : Euclidean n) : R (A w) = w :=
    congrArg (fun T : Euclidean n →L[ℝ] Euclidean n ↦ T w) hRA
  have hARP (z : Euclidean N) : A (R (P z)) = P z := by
    obtain ⟨w, hw⟩ := A.range.starProjection_apply_mem z
    change A w = P z at hw
    rw [← hw, hRA']
  have hLP : L.toLinearMap.comp P.toLinearMap =
      c • ((H.comp R).toLinearMap.comp P.toLinearMap) +
        (ℓ.comp (R.comp P)).toLinearMap.smulRight (A v) := by
    apply LinearMap.ext
    intro z
    have h := congrArg (fun T : Euclidean n →L[ℝ] Euclidean N ↦ T (R (P z))) hLA
    change L (A (R (P z))) = c • H (R (P z)) + ℓ (R (P z)) • A v at h
    change L (P z) = c • H (R (P z)) + ℓ (R (P z)) • A v
    simpa only [hARP] using h
  change LinearMap.trace ℝ (Euclidean N) (L.toLinearMap.comp P.toLinearMap) = _
  rw [hLP, map_add, map_smul, LinearMap.trace_smulRight]
  have hPAv : P (A v) = A v := A.range.starProjection_eq_self_iff.mpr ⟨v, rfl⟩
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, hPAv, hRA',
    smul_eq_mul]
  rfl

/-- The Jacobian/Piola identity needed in the constancy proof. An
ambient field agreeing along the chart with `(η/Jφ) Dφ(v)` has weighted
tangential divergence equal to the ordinary directional derivative of η. -/
theorem chartTangentialDivergence_coordinate_test
    {M W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    {a : Euclidean n} (ha : a ∈ D)
    {η : Euclidean n → ℝ} (hη : DifferentiableAt ℝ η a)
    {X : Euclidean N → Euclidean N} (hX : DifferentiableAt ℝ X (φ a))
    (v : Euclidean n)
    (heq : (X ∘ φ) =ᶠ[𝓝 a] fun u ↦
      (η u / Chapter02.areaJacobianAt φ u) • fderiv ℝ φ u v) :
    Chapter02.areaJacobianAt φ a * chartTangentialDivergence φ X a =
      fderiv ℝ η a v := by
  let A := fderiv ℝ φ a
  let H := fderiv ℝ (fderiv ℝ φ) a v
  let J := Chapter02.areaJacobianAt φ
  let q (u : Euclidean n) := η u / J u
  have hφa : ContDiffAt ℝ 2 φ a :=
    (hφ.contDiffOn a ha).contDiffAt (hφ.isOpen_source.mem_nhds ha)
  have hJ : DifferentiableAt ℝ J a :=
    (((contDiffOn_areaJacobianAt_simonChart hφ) a ha).contDiffAt
      (hφ.isOpen_source.mem_nhds ha)).differentiableAt one_ne_zero
  have hJne : J a ≠ 0 := (areaJacobianAt_pos_simonChart hφ ha).ne'
  have hq : DifferentiableAt ℝ q a := hη.mul (hJ.inv hJne)
  have hder : DifferentiableAt ℝ (fderiv ℝ φ) a :=
    (hφa.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hAv : HasFDerivAt (fun u ↦ fderiv ℝ φ u v) H a := by
    have h := hder.hasFDerivAt.clm_apply (hasFDerivAt_const v a)
    have hs : (fderiv ℝ (fderiv ℝ φ) a).flip v = H := by
      apply ContinuousLinearMap.ext
      intro w
      exact (hφa.isSymmSndFDerivAt (by norm_num)).eq w v
    simpa only [ContinuousLinearMap.comp_zero, zero_add, hs] using h
  have hprod := hq.hasFDerivAt.smul hAv
  have hcomp := hX.hasFDerivAt.comp a (hφa.differentiableAt (by norm_num)).hasFDerivAt
  have hLA : (fderiv ℝ X (φ a)).comp A =
      q a • H + (fderiv ℝ q a).smulRight (A v) :=
    (hcomp.congr_of_eventuallyEq heq.symm).unique hprod
  obtain ⟨R₀, hR₀⟩ := A.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (hφ.injective_fderiv ha))
  let R := R₀.toContinuousLinearMap
  have hRA : R.comp A = ContinuousLinearMap.id ℝ (Euclidean n) := by
    apply ContinuousLinearMap.ext
    intro w
    exact LinearMap.congr_fun hR₀ w
  have ht := trace_projection_of_coordinate_product A H R (fderiv ℝ X (φ a))
    (fderiv ℝ q a) (q a) v hRA hLA
  have hJder := fderiv_areaJacobianAt_apply_of_leftInverse hφa
    (hφ.injective_fderiv ha) R hRA v
  have hqJ : (fun u ↦ J u * q u) =ᶠ[𝓝 a] η := by
    filter_upwards [hJ.continuousAt.eventually_ne hJne] with u hu
    dsimp only [q]
    exact mul_div_cancel₀ (η u) hu
  have hscalar := ((hJ.hasFDerivAt.mul hq.hasFDerivAt).congr_of_eventuallyEq hqJ.symm).fderiv
  have hv := congrArg (fun T : Euclidean n →L[ℝ] ℝ ↦ T v) hscalar
  change fderiv ℝ η a v = J a * fderiv ℝ q a v + q a * fderiv ℝ J a v at hv
  change J a * LinearMap.trace ℝ (Euclidean N)
    ((fderiv ℝ X (φ a)).toLinearMap.comp A.range.starProjection.toLinearMap) = _
  rw [ht, hv]
  change fderiv ℝ J a v = J a *
    LinearMap.trace ℝ (Euclidean N) ((H.comp R).toLinearMap.comp
      A.range.starProjection.toLinearMap) at hJder
  rw [hJder]
  ring

end Varifold
end
end Poincare.SimonGMT.Chapter08
