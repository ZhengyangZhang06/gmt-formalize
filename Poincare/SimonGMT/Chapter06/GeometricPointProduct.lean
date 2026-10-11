module

public import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
public import Poincare.SimonGMT.Chapter06.Product

@[expose] public section

/-!
# Point products as continuous domain currents

Simon (6.2.22) is upgraded from the algebraic current API to actual
`GeometricCurrentOn` objects. All derivatives of the point-slice operation
are controlled by a fixed continuous linear operator. This also proves the
degree-zero-factor case of the boundary product identity (6.2.19).
-/

open Filter Function Set
open scoped Topology

namespace Poincare.SimonGMT.Chapter06

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Point evaluation is sequentially continuous in Simon's test topology,
including evaluation outside the common compact support. -/
theorem TestFormOnConverges.tendsto_eval {U : Set E} {n : ℕ}
    {omegaSeq : ℕ → TestFormOn U n} {omega : TestFormOn U n}
    (h : TestFormOnConverges omegaSeq omega) (x : E) :
    Tendsto (fun j => (omegaSeq j : DifferentialForm E n) x) atTop
      (nhds ((omega : DifferentialForm E n) x)) := by
  rcases h with ⟨K, _, _, hseq, homega, hderiv⟩
  by_cases hx : x ∈ K
  · have hzero := (hderiv 0).tendsto_at hx
    have heval := (continuous_eval_const (0 : Fin 0 → E)).tendsto
      (iteratedFDeriv ℝ 0 (omega : DifferentialForm E n) x)
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using heval.comp hzero
  · have hseqzero (j : ℕ) : (omegaSeq j : DifferentialForm E n) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hx' => hx (hseq j hx'))
    have homegazero : (omega : DifferentialForm E n) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hx' => hx (homega hx'))
    simpa only [hseqzero, homegazero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Covector E n)) atTop (nhds 0))

/-- The point `0`-current in a domain, with the required continuity proved. -/
def pointGeometricCurrentOn (U : Set E) (p : E) : GeometricCurrentOn U 0 where
  toCurrent :=
    { toFun := fun omega => (omega : DifferentialForm E 0) p 0
      map_add' := by intro; simp
      map_smul' := by intro; simp }
  continuous' omegaSeq h := by
    have heval := (continuous_eval_const (0 : Fin 0 → E)).tendsto (0 : Covector E 0)
    change Tendsto (fun j => (omegaSeq j : DifferentialForm E 0) p 0) atTop (nhds 0)
    simpa [Function.comp_def] using heval.comp (h.tendsto_eval p)

@[simp] theorem pointGeometricCurrentOn_apply (U : Set E) (p : E)
    (omega : TestFormOn U 0) :
    pointGeometricCurrentOn U p omega = (omega : DifferentialForm E 0) p 0 := rfl

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A point slice is a globally proper affine map. -/
theorem isProperMap_pointSlice (p : E) : IsProperMap (fun y : F => (p, y)) := by
  apply Topology.IsClosedEmbedding.isProperMap
  refine ⟨isEmbedding_prodMkRight p, ?_⟩
  have hrange : range (fun y : F => (p, y)) = {z : E × F | z.1 = p} := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      rfl
    · intro hz
      exact ⟨z.2, Prod.ext hz.symm rfl⟩
  rw [hrange]
  exact isClosed_eq continuous_fst continuous_const

theorem pointSlice_eq_affinePullbackForm (p : E) {n : ℕ}
    (omega : DifferentialForm (E × F) n) :
    pointSlice p omega = affinePullbackForm (ContinuousLinearMap.inr ℝ E F) (p, 0) omega := by
  funext y
  simp [pointSlice, affinePullbackForm]

/-- The slice support is contained in the corresponding section of the
original topological support. -/
theorem tsupport_pointSlice_subset (p : E) {n : ℕ}
    (omega : DifferentialForm (E × F) n) :
    tsupport (pointSlice p omega) ⊆ (fun y => (p, y)) ⁻¹' tsupport omega := by
  rw [pointSlice_eq_affinePullbackForm]
  simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using
    tsupport_affinePullbackForm_subset (ContinuousLinearMap.inr ℝ E F) (p, 0) omega

/-- Point slicing on the actual product-domain test-form space. -/
def pointSliceTestOn (p : E) (U : Set E) (V : Set F) (n : ℕ) :
    TestFormOn (U ×ˢ V) n →ₗ[ℝ] TestFormOn V n where
  toFun omega := by
    refine ⟨pointSlice p (omega : DifferentialForm (E × F) n), ?_⟩
    change IsTestForm (pointSlice p (omega : DifferentialForm (E × F) n)) ∧
      tsupport (pointSlice p (omega : DifferentialForm (E × F) n)) ⊆ V
    refine ⟨pointSlice_isTestForm p omega.property.1, ?_⟩
    intro y hy
    exact (omega.property.2
      (tsupport_pointSlice_subset p (omega : DifferentialForm (E × F) n) hy)).2
  map_add' omega eta := by
    apply Subtype.ext
    funext y
    ext v
    simp [pointSlice]
  map_smul' c omega := by
    apply Subtype.ext
    funext y
    ext v
    simp [pointSlice]

@[simp] theorem pointSliceTestOn_coe (p : E) (U : Set E) (V : Set F) (n : ℕ)
    (omega : TestFormOn (U ×ˢ V) n) :
    (pointSliceTestOn p U V n omega : DifferentialForm F n) = pointSlice p omega := rfl

/-- The all-orders jet formula for point restriction. -/
theorem iteratedFDeriv_pointSlice (p : E) {n : ℕ}
    {omega : DifferentialForm (E × F) n} (homega : IsSmoothForm omega) (k : ℕ) (y : F) :
    iteratedFDeriv ℝ k (pointSlice p omega) y =
      affinePullbackJet (ContinuousLinearMap.inr ℝ E F) n k
        (iteratedFDeriv ℝ k omega (p, y)) := by
  rw [pointSlice_eq_affinePullbackForm]
  simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using
    iteratedFDeriv_affinePullbackForm (ContinuousLinearMap.inr ℝ E F) (p, 0) homega k y

/-- Point slicing is sequentially continuous in Simon's test-form topology. -/
theorem TestFormOnConverges.pointSlice (p : E) {U : Set E} {V : Set F} {n : ℕ}
    {omegaSeq : ℕ → TestFormOn (U ×ˢ V) n} {omega : TestFormOn (U ×ˢ V) n}
    (h : TestFormOnConverges omegaSeq omega) :
    TestFormOnConverges (fun j => pointSliceTestOn p U V n (omegaSeq j))
      (pointSliceTestOn p U V n omega) := by
  rcases h with ⟨K, hK, hKUV, hseq, homega, hderiv⟩
  refine ⟨(fun y => (p, y)) ⁻¹' K, (isProperMap_pointSlice p).isCompact_preimage hK,
    (fun y hy => (hKUV hy).2),
    (fun j => (tsupport_pointSlice_subset p _).trans (preimage_mono (hseq j))),
    (tsupport_pointSlice_subset p _).trans (preimage_mono homega), ?_⟩
  intro k
  have hcomp := (affinePullbackJet_uniformContinuous (ContinuousLinearMap.inr ℝ E F) n k).comp_tendstoUniformlyOn
    ((hderiv k).comp (fun y => (p, y)))
  simpa only [Function.comp_def, pointSliceTestOn_coe,
    ← iteratedFDeriv_pointSlice p omega.property.1.1 k,
    ← iteratedFDeriv_pointSlice p (omegaSeq _ |>.property.1.1) k] using hcomp

/-- Simon (6.2.22) in the full continuous-current space on a product domain. -/
def GeometricCurrentOn.pointProduct {V : Set F} {n : ℕ}
    (T : GeometricCurrentOn V n) (p : E) (U : Set E) : GeometricCurrentOn (U ×ˢ V) n where
  toCurrent := T.toCurrent.comp (pointSliceTestOn p U V n)
  continuous' omegaSeq h := by
    apply T.continuous'
    simpa only [map_zero] using h.pointSlice p

@[simp] theorem GeometricCurrentOn.pointProduct_apply {V : Set F} {n : ℕ}
    (T : GeometricCurrentOn V n) (p : E) (U : Set E) (omega : TestFormOn (U ×ˢ V) n) :
    T.pointProduct p U omega = T (pointSliceTestOn p U V n omega) := rfl

/-- Exterior differentiation commutes with restriction to a point slice. -/
theorem exteriorDerivative_pointSlice (p : E) {n : ℕ}
    {omega : DifferentialForm (E × F) n} (homega : IsSmoothForm omega) :
    exteriorDerivative (pointSlice p omega) = pointSlice p (exteriorDerivative omega) := by
  simp only [pointSlice_eq_affinePullbackForm]
  exact exteriorDerivative_affinePullbackForm _ _ homega

/-- The degree-zero-factor case of Simon's boundary Leibniz formula. -/
theorem GeometricCurrentOn.boundary_pointProduct {V : Set F} {n : ℕ}
    (T : GeometricCurrentOn V (n + 1)) (p : E) (U : Set E) :
    (T.pointProduct p U).boundary = T.boundary.pointProduct p U := by
  apply GeometricCurrentOn.ext
  intro omega
  change T.toCurrent _ = T.toCurrent _
  apply congrArg T.toCurrent
  apply Subtype.ext
  exact (exteriorDerivative_pointSlice p omega.property.1.1).symm

end

end Poincare.SimonGMT.Chapter06
