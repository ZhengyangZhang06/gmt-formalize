module

public import Poincare.SimonGMT.Chapter08.FirstVariationIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

/-!
# Arbitrary deformation families: the local differential calculation

For a jointly `C²` family, differentiating its spatial differential in time
gives the spatial differential of its initial velocity. Symmetry of second
derivatives proves this identity. The tangential Jacobian therefore has the
same derivative as the affine variation, with no assumption on the family
away from the open domain.

The compact differentiation lemma derives uniform domination and
measurability from local `C¹` regularity on a compact set of finite measure.

Source: Simon, Chapter 8, (2.2)--(2.3), printed pp. 208--209, with
deformation families as in Chapter 2, (5.6), printed pp. 62--63.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal Matrix.Norms.Elementwise

namespace Poincare.SimonGMT.Chapter08

/-- Compactness supplies a common neighborhood and an integrable derivative
bound. No separate measurability or domination hypotheses are needed. -/
theorem hasDerivAt_integral_of_contDiffAt_on_compact
    {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace α] [T2Space α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [SecondCountableTopology α]
    (μ : Measure α) (C : Set α) (hC : IsCompact C) (hμ : μ C ≠ ∞)
    (e : α → E) (he : Continuous e) (g : ℝ × E → ℝ)
    (hg : ∀ z ∈ C, ContDiffAt ℝ 1 g (0, e z)) :
    HasDerivAt (fun t : ℝ ↦ ∫ z in C, g (t, e z) ∂μ)
      (∫ z in C, fderiv ℝ g (0, e z) (1, 0) ∂μ) 0 := by
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ z ∈ C, ContDiffAt ℝ 1 g (t, e z) := by
    apply hC.eventually_forall_of_forall_eventually
    intro z hz
    have hc : ContinuousAt (fun p : ℝ × α ↦ (p.1, e p.2)) (0, z) :=
      (continuous_fst.prodMk (he.comp continuous_snd)).continuousAt
    exact hc.eventually ((hg z hz).eventually (by norm_num))
  obtain ⟨r, hr, hrr⟩ := Metric.mem_nhds_iff.mp hnear
  let T := closedBall (0 : ℝ) (r / 2) ×ˢ C
  have hT : IsCompact T := (isCompact_closedBall _ _).prod hC
  have hcd (p : ℝ × α) (hp : p ∈ T) : ContDiffAt ℝ 1 g (p.1, e p.2) :=
    hrr ((show dist p.1 0 ≤ r / 2 from hp.1).trans_lt (by linarith)) p.2 hp.2
  have hdercont : ContinuousOn (fun p : ℝ × α ↦
      fderiv ℝ g (p.1, e p.2) (1, 0)) T := by
    intro p hp
    exact (((hcd p hp).fderiv_right (m := 0) (by norm_num)).continuousAt.comp
      (f := fun q : ℝ × α ↦ (q.1, e q.2))
      (continuous_fst.prodMk (he.comp continuous_snd)).continuousAt).clm_apply
        continuousAt_const |>.continuousWithinAt
  obtain ⟨B, hB⟩ := hT.exists_bound_of_continuousOn hdercont
  have ht0 : (0 : ℝ) ∈ closedBall 0 (r / 2) := mem_closedBall_self (by linarith)
  have hcont (t : ℝ) (ht : t ∈ closedBall 0 (r / 2)) :
      ContinuousOn (fun z ↦ g (t, e z)) C := by
    intro z hz
    exact ((hcd (t, z) ⟨ht, hz⟩).continuousAt.comp
      (f := fun y : α ↦ (t, e y))
      (continuous_const.prodMk he).continuousAt).continuousWithinAt
  have hcont' : ContinuousOn (fun z ↦ fderiv ℝ g (0, e z) (1, 0)) C := by
    exact hdercont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz ↦ ⟨ht0, hz⟩)
  have hball : ∀ᶠ t : ℝ in 𝓝 0, t ∈ ball 0 (r / 2) :=
    ball_mem_nhds 0 (by linarith)
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ.restrict C) (F := fun t z ↦ g (t, e z))
    (F' := fun t z ↦ fderiv ℝ g (t, e z) (1, 0))
    (bound := fun _ ↦ B) (s := ball 0 (r / 2))
    (ball_mem_nhds 0 (by linarith))
    (hball.mono fun t ht ↦
      (hcont t (ball_subset_closedBall ht)).aestronglyMeasurable hC.measurableSet)
    ((hcont 0 ht0).integrableOn_of_subset_isCompact hC hC.measurableSet Subset.rfl hμ)
    (hcont'.aestronglyMeasurable hC.measurableSet)
    (by
      filter_upwards [ae_restrict_mem hC.measurableSet] with z hz t ht
      exact hB (t, z) ⟨ball_subset_closedBall ht, hz⟩)
    (integrableOn_const hμ)
    (by
      filter_upwards [ae_restrict_mem hC.measurableSet] with z hz t ht
      exact ((hcd (t, z) ⟨ball_subset_closedBall ht, hz⟩).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt t
          ((hasDerivAt_id t).prodMk (hasDerivAt_const t (e z))))
  exact hd

end Poincare.SimonGMT.Chapter08

namespace Poincare.SimonGMT.Chapter08.Varifold
variable {N n : ℕ}
noncomputable section

/-- The spatial partial differential of the uncurried deformation. -/
def familySpatialDerivative (F : ℝ × Euclidean N → Euclidean N)
    (p : ℝ × Euclidean N) : Euclidean N →L[ℝ] Euclidean N :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ ℝ (Euclidean N))

/-- The initial time derivative, identified with `deriv` below. -/
def initialVelocity (F : ℝ × Euclidean N → Euclidean N) (x : Euclidean N) : Euclidean N :=
  fderiv ℝ F (0, x) (1, 0)

theorem familySpatialDerivative_eq_fderiv
    (F : ℝ × Euclidean N → Euclidean N) (t : ℝ) (x : Euclidean N)
    (hF : DifferentiableAt ℝ F (t, x)) :
    familySpatialDerivative F (t, x) = fderiv ℝ (fun y ↦ F (t, y)) x := by
  have hd := hF.hasFDerivAt.comp x ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  exact hd.fderiv.symm

theorem initialVelocity_eq_deriv (F : ℝ × Euclidean N → Euclidean N)
    (x : Euclidean N) (hF : DifferentiableAt ℝ F (0, x)) :
    initialVelocity F x = deriv (fun t ↦ F (t, x)) 0 := by
  exact (hF.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 x))).deriv.symm

/-- Joint `C²` regularity allows interchange of the time and spatial
derivatives, by symmetry of the second Fréchet derivative. -/
theorem hasDerivAt_familySpatialDerivative
    (F : ℝ × Euclidean N → Euclidean N) (x : Euclidean N)
    (hF : ContDiffAt ℝ 2 F (0, x)) :
    HasDerivAt (fun t ↦ familySpatialDerivative F (t, x))
      (fderiv ℝ (initialVelocity F) x) 0 := by
  let D := fderiv ℝ (fderiv ℝ F) (0, x)
  have hd : HasFDerivAt (fderiv ℝ F) D (0, x) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero |>.hasFDerivAt
  have hv : HasFDerivAt (initialVelocity F)
      ((ContinuousLinearMap.apply ℝ (Euclidean N) (1, (0 : Euclidean N))).comp
        (D.comp (ContinuousLinearMap.inr ℝ ℝ (Euclidean N)))) x := by
    exact (ContinuousLinearMap.apply ℝ (Euclidean N) (1, (0 : Euclidean N))).hasFDerivAt.comp x
      (hd.comp x ((hasFDerivAt_const (0 : ℝ) x).prodMk (hasFDerivAt_id x)))
  have ht := hd.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 x))
  have hc : HasDerivAt (fun t ↦ familySpatialDerivative F (t, x))
      ((D (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclidean N))) 0 := by
    simpa [familySpatialDerivative] using
      ht.clm_comp (hasDerivAt_const 0 (ContinuousLinearMap.inr ℝ ℝ (Euclidean N)))
  convert hc using 1
  rw [hv.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  exact (hF.isSymmSndFDerivAt (by norm_num)).eq (0, v) (1, 0)

def linearTangentialJacobian (S : Grassmannian N n)
    (A : Euclidean N →L[ℝ] Euclidean N) : ℝ :=
  Real.sqrt (1 - S.1 + S.1 * (clmToMatrix A).transpose * clmToMatrix A * S.1).det

theorem linearTangentialJacobian_fderiv
    (f : Euclidean N → Euclidean N) (x : Euclidean N) (S : Grassmannian N n) :
    linearTangentialJacobian S (fderiv ℝ f x) = tangentialJacobianReal f x S :=
  (tangentialJacobianReal_eq_sqrt_det_ambientGram f x S).symm

theorem contDiffAt_linearTangentialJacobian_id (S : Grassmannian N n) :
    ContDiffAt ℝ 1 (linearTangentialJacobian S) (ContinuousLinearMap.id ℝ (Euclidean N)) := by
  have hM : ContDiff ℝ 1 (clmToMatrix (N := N)) :=
    clmToMatrix.toContinuousLinearMap.contDiff
  have hgram : ContDiff ℝ 1 (fun A : Euclidean N →L[ℝ] Euclidean N ↦
      (1 - S.1 + S.1 * (clmToMatrix A).transpose * clmToMatrix A * S.1).det) := by
    simp only [Matrix.det_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  apply hgram.contDiffAt.sqrt
  have hid : clmToMatrix (ContinuousLinearMap.id ℝ (Euclidean N)) = 1 := by
    change LinearMap.toMatrix Grassmannian.coordinateBasis.toBasis
      Grassmannian.coordinateBasis.toBasis LinearMap.id = 1
    exact LinearMap.toMatrix_id _
  simp only [hid, Matrix.transpose_one, Matrix.mul_one, S.idempotent, sub_add_cancel,
    Matrix.det_one, ne_eq, one_ne_zero, not_false_eq_true]

theorem contDiffAt_initialVelocity
    (F : ℝ × Euclidean N → Euclidean N) (x : Euclidean N)
    (hF : ContDiffAt ℝ 2 F (0, x)) :
    ContDiffAt ℝ 1 (initialVelocity F) x := by
  exact ((hF.fderiv_right (m := 1) (by norm_num)).comp x
    (contDiffAt_const.prodMk contDiffAt_id)).clm_apply contDiffAt_const

/-- The local calculation in Simon (8.2.3) for an arbitrary jointly `C²`
family initially equal to the identity to first spatial order. -/
theorem hasDerivAt_linearTangentialJacobian_family
    (F : ℝ × Euclidean N → Euclidean N) (x : Euclidean N)
    (S : Grassmannian N n) (hF : ContDiffAt ℝ 2 F (0, x))
    (hzero : familySpatialDerivative F (0, x) = ContinuousLinearMap.id ℝ (Euclidean N)) :
    HasDerivAt (fun t ↦ linearTangentialJacobian S (familySpatialDerivative F (t, x)))
      (tangentialDivergence (initialVelocity F) x S) 0 := by
  let A := fderiv ℝ (initialVelocity F) x
  let L := fderiv ℝ (linearTangentialJacobian S) (ContinuousLinearMap.id ℝ (Euclidean N))
  have hJ : HasFDerivAt (linearTangentialJacobian S) L
      (ContinuousLinearMap.id ℝ (Euclidean N)) :=
    ((contDiffAt_linearTangentialJacobian_id S).differentiableAt one_ne_zero).hasFDerivAt
  have haff : HasDerivAt
      (fun t : ℝ ↦ ContinuousLinearMap.id ℝ (Euclidean N) + t • A) A 0 := by
    have h : HasDerivAt (fun t : ℝ ↦ t • A) A 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const A
    exact h.const_add (ContinuousLinearMap.id ℝ (Euclidean N))
  have hJacaff : HasDerivAt
      (fun t : ℝ ↦ linearTangentialJacobian S
        (ContinuousLinearMap.id ℝ (Euclidean N) + t • A)) (L A) 0 := by
    exact hJ.comp_hasDerivAt_of_eq (f := fun t : ℝ ↦
      ContinuousLinearMap.id ℝ (Euclidean N) + t • A) (0 : ℝ) haff
      (by
        ext v
        simp only [add_apply, smul_apply,
          zero_smul, add_zero])
  have hX : DifferentiableAt ℝ (initialVelocity F) x :=
    (contDiffAt_initialVelocity F x hF).differentiableAt one_ne_zero
  have heq (t : ℝ) : linearTangentialJacobian S
      (ContinuousLinearMap.id ℝ (Euclidean N) + t • A) =
      tangentialJacobianReal (fun y ↦ y + t • initialVelocity F y) x S := by
    rw [← linearTangentialJacobian_fderiv]
    congr 1
    exact ((hasFDerivAt_id x).add (hX.hasFDerivAt.const_smul t)).fderiv.symm
  have hid : L A = tangentialDivergence (initialVelocity F) x S := by
    have hh := hasDerivAt_tangentialJacobianReal_id_add_smul (initialVelocity F) x S hX
    exact (hJacaff.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ (heq t).symm)).unique hh
  rw [← hid]
  exact hJ.comp_hasDerivAt_of_eq 0 (hasDerivAt_familySpatialDerivative F x hF) hzero.symm

def familyJacobian (F : ℝ × Euclidean N → Euclidean N)
    (p : ℝ × (Euclidean N × Matrix (Fin N) (Fin N) ℝ)) : ℝ :=
  Real.sqrt (1 - p.2.2 + p.2.2 *
    (clmToMatrix (familySpatialDerivative F (p.1, p.2.1))).transpose *
    clmToMatrix (familySpatialDerivative F (p.1, p.2.1)) * p.2.2).det

theorem contDiffAt_familyJacobian
    (F : ℝ × Euclidean N → Euclidean N) (x : Euclidean N)
    (S : Grassmannian N n) (hF : ContDiffAt ℝ 2 F (0, x))
    (hzero : familySpatialDerivative F (0, x) = ContinuousLinearMap.id ℝ (Euclidean N)) :
    ContDiffAt ℝ 1 (familyJacobian F) (0, (x, S.1)) := by
  have hd : ContDiffAt ℝ 1 (familySpatialDerivative F) (0, x) :=
    (hF.fderiv_right (m := 1) (by norm_num)).clm_comp contDiffAt_const
  have hq : ContDiff ℝ 1
      (fun p : ℝ × (Euclidean N × Matrix (Fin N) (Fin N) ℝ) ↦ (p.1, p.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hD : ContDiffAt ℝ 1
      (fun p : ℝ × (Euclidean N × Matrix (Fin N) (Fin N) ℝ) ↦
        familySpatialDerivative F (p.1, p.2.1)) (0, (x, S.1)) :=
    ContDiffAt.comp (𝕜 := ℝ) (n := 1) (g := familySpatialDerivative F)
      (f := fun p : ℝ × (Euclidean N × Matrix (Fin N) (Fin N) ℝ) ↦ (p.1, p.2.1))
      (0, (x, S.1)) hd hq.contDiffAt
  have hM : ContDiffAt ℝ 1
      (fun p : ℝ × (Euclidean N × Matrix (Fin N) (Fin N) ℝ) ↦
        clmToMatrix (familySpatialDerivative F (p.1, p.2.1))) (0, (x, S.1)) :=
    clmToMatrix.toContinuousLinearMap.contDiff.comp_contDiffAt _ hD
  have hgram : ContDiffAt ℝ 1
      (fun p : ℝ × (Euclidean N × Matrix (Fin N) (Fin N) ℝ) ↦
        (1 - p.2.2 + p.2.2 *
          (clmToMatrix (familySpatialDerivative F (p.1, p.2.1))).transpose *
          clmToMatrix (familySpatialDerivative F (p.1, p.2.1)) * p.2.2).det)
      (0, (x, S.1)) := by
    simp only [Matrix.det_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  apply hgram.sqrt
  have hid : clmToMatrix (ContinuousLinearMap.id ℝ (Euclidean N)) = 1 := by
    change LinearMap.toMatrix Grassmannian.coordinateBasis.toBasis
      Grassmannian.coordinateBasis.toBasis LinearMap.id = 1
    exact LinearMap.toMatrix_id _
  simp only [hzero, hid, Matrix.transpose_one, Matrix.mul_one, S.idempotent, sub_add_cancel,
    Matrix.det_one, ne_eq, one_ne_zero, not_false_eq_true]

end
end Poincare.SimonGMT.Chapter08.Varifold
