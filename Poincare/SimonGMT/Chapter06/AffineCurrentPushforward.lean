module

public import Mathlib.Topology.Maps.Proper.Basic
public import Poincare.SimonGMT.Chapter06.Currents

@[expose] public section

/-!
# Proper affine pullback in the test-form topology

This is a concrete analytic building block for Simon (6.2.23)--(6.2.24),
not the general proper-on-current-support construction. For a globally
proper affine map, pullback preserves compactly supported smooth forms and
is sequentially continuous in Simon's topology. Consequently it defines a
genuine geometric current pushforward and commutes with boundary.
-/

open Filter Function Set
open scoped ContDiff Topology

namespace Poincare.SimonGMT.Chapter06

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pullback by the affine map `x ↦ b + L x`. -/
def affinePullbackForm (L : E →L[ℝ] F) (b : F) {n : ℕ}
    (omega : DifferentialForm F n) : DifferentialForm E n :=
  fun x => (omega (b + L x)).compContinuousLinearMap L

/-- Smoothness of affine pullback. -/
theorem affinePullbackForm_isSmoothForm (L : E →L[ℝ] F) (b : F) {n : ℕ}
    {omega : DifferentialForm F n} (homega : IsSmoothForm omega) :
    IsSmoothForm (affinePullbackForm L b omega) := by
  have hf : ContDiff ℝ ∞ (fun x : E => b + L x) := contDiff_const.add L.contDiff
  exact (ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin n) (F := ℝ) L).contDiff.comp
    (homega.comp hf)

/-- Pullback support lies in the preimage of the original support. -/
theorem tsupport_affinePullbackForm_subset (L : E →L[ℝ] F) (b : F) {n : ℕ}
    (omega : DifferentialForm F n) :
    tsupport (affinePullbackForm L b omega) ⊆ (fun x => b + L x) ⁻¹' tsupport omega :=
  (tsupport_comp_subset
    (g := ContinuousAlternatingMap.compContinuousLinearMapCLM L) (map_zero _) _).trans
      (tsupport_comp_subset_preimage omega (continuous_const.add L.continuous))

/-- Global properness is sufficient to preserve compact support. -/
theorem affinePullbackForm_isTestForm (L : E →L[ℝ] F) (b : F)
    (hproper : IsProperMap (fun x => b + L x)) {n : ℕ}
    {omega : DifferentialForm F n} (homega : IsTestForm omega) :
    IsTestForm (affinePullbackForm L b omega) :=
  ⟨affinePullbackForm_isSmoothForm L b homega.1,
    (hproper.isCompact_preimage homega.2).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_affinePullbackForm_subset L b omega)⟩

/-- Affine pullback as an actual linear map of the domain test-form spaces. -/
def affinePullbackTestOn (L : E →L[ℝ] F) (b : F)
    (hproper : IsProperMap (fun x => b + L x)) (V : Set F) (n : ℕ) :
    TestFormOn V n →ₗ[ℝ] TestFormOn ((fun x => b + L x) ⁻¹' V) n where
  toFun omega := by
    refine ⟨affinePullbackForm L b (omega : DifferentialForm F n), ?_⟩
    change IsTestForm (affinePullbackForm L b (omega : DifferentialForm F n)) ∧
      tsupport (affinePullbackForm L b (omega : DifferentialForm F n)) ⊆ (fun x => b + L x) ⁻¹' V
    exact ⟨affinePullbackForm_isTestForm L b hproper omega.property.1,
      (tsupport_affinePullbackForm_subset L b (omega : DifferentialForm F n)).trans
        (preimage_mono omega.property.2)⟩
  map_add' omega eta := by
    apply Subtype.ext
    funext x
    ext v
    simp [affinePullbackForm]
  map_smul' c omega := by
    apply Subtype.ext
    funext x
    ext v
    simp [affinePullbackForm]

@[simp] theorem affinePullbackTestOn_coe (L : E →L[ℝ] F) (b : F)
    (hproper : IsProperMap (fun x => b + L x)) (V : Set F) (n : ℕ)
    (omega : TestFormOn V n) :
    (affinePullbackTestOn L b hproper V n omega : DifferentialForm E n) =
      affinePullbackForm L b omega := rfl

/-- Every derivative of affine pullback is obtained from the corresponding
derivative of the original form by this fixed continuous linear operator. -/
def affinePullbackJet (L : E →L[ℝ] F) (n k : ℕ) :
    (F [×k]→L[ℝ] Covector F n) →L[ℝ] (E [×k]→L[ℝ] Covector E n) :=
  (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => E)
    (Covector F n) (Covector E n) (ContinuousAlternatingMap.compContinuousLinearMapCLM L)).comp
      (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k => L))

theorem affinePullbackJet_uniformContinuous (L : E →L[ℝ] F) (n k : ℕ) :
    UniformContinuous (affinePullbackJet L n k) := by
  let A : (F [×k]→L[ℝ] Covector F n) →+ (E [×k]→L[ℝ] Covector E n) :=
    { toFun := affinePullbackJet L n k
      map_zero' := map_zero _
      map_add' := map_add _ }
  exact uniformContinuous_of_continuousAt_zero A
    (affinePullbackJet L n k).continuous.continuousAt

theorem iteratedFDeriv_affinePullbackForm (L : E →L[ℝ] F) (b : F) {n : ℕ}
    {omega : DifferentialForm F n} (homega : IsSmoothForm omega) (k : ℕ) (x : E) :
    iteratedFDeriv ℝ k (affinePullbackForm L b omega) x =
      affinePullbackJet L n k (iteratedFDeriv ℝ k omega (b + L x)) := by
  change iteratedFDeriv ℝ k
    ((ContinuousAlternatingMap.compContinuousLinearMapCLM L) ∘
      ((fun y => omega (b + y)) ∘ L)) x = _
  have hshift : ContDiff ℝ ∞ (fun y : F => omega (b + y)) :=
    homega.comp (show ContDiff ℝ ∞ (fun y : F => b + y) from contDiff_const.add contDiff_id)
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left
    (ContinuousAlternatingMap.compContinuousLinearMapCLM L)
    (hshift.comp L.contDiff).contDiffAt (by simp)]
  rw [L.iteratedFDeriv_comp_right hshift x (by simp),
    iteratedFDeriv_comp_add_left]
  rfl

/-- Pullback is continuous for the full test-form topology, including all
orders of derivatives and a common compact support. -/
theorem TestFormOnConverges.affinePullback (L : E →L[ℝ] F) (b : F)
    (hproper : IsProperMap (fun x => b + L x)) {V : Set F} {n : ℕ}
    {omegaSeq : ℕ → TestFormOn V n} {omega : TestFormOn V n}
    (h : TestFormOnConverges omegaSeq omega) :
    TestFormOnConverges
      (fun j => affinePullbackTestOn L b hproper V n (omegaSeq j))
      (affinePullbackTestOn L b hproper V n omega) := by
  rcases h with ⟨K, hK, hKV, hseq, homega, hderiv⟩
  refine ⟨(fun x => b + L x) ⁻¹' K, hproper.isCompact_preimage hK, preimage_mono hKV,
    fun j => (tsupport_affinePullbackForm_subset L b _).trans (preimage_mono (hseq j)),
    (tsupport_affinePullbackForm_subset L b _).trans (preimage_mono homega), ?_⟩
  intro k
  have hcomp := (affinePullbackJet_uniformContinuous L n k).comp_tendstoUniformlyOn
    ((hderiv k).comp (fun x => b + L x))
  simpa only [Function.comp_def, affinePullbackTestOn_coe,
    ← iteratedFDeriv_affinePullbackForm L b omega.property.1.1 k,
    ← iteratedFDeriv_affinePullbackForm L b (omegaSeq _ |>.property.1.1) k] using hcomp

/-- Pullback commutes with exterior differentiation, without a properness
assumption at the unbundled form level. -/
theorem exteriorDerivative_affinePullbackForm (L : E →L[ℝ] F) (b : F) {n : ℕ}
    {omega : DifferentialForm F n} (homega : IsSmoothForm omega) :
    exteriorDerivative (affinePullbackForm L b omega) =
      affinePullbackForm L b (exteriorDerivative omega) := by
  have hdf (x : E) : fderiv ℝ (fun y => b + L y) x = L := by
    simp only [fderiv_const_add, L.fderiv]
  funext x
  change extDeriv (fun y => (omega (b + L y)).compContinuousLinearMap L) x = _
  simpa only [hdf, affinePullbackForm, exteriorDerivative] using
    (extDeriv_pullback (r := ∞) (homega.differentiable (by simp)).differentiableAt
      (show ContDiff ℝ ∞ (fun y => b + L y) from contDiff_const.add L.contDiff).contDiffAt
      (by simp) (x := x))

/-- The pullback map commutes with the bundled exterior derivative. -/
theorem affinePullbackTestOn_exteriorDerivative (L : E →L[ℝ] F) (b : F)
    (hproper : IsProperMap (fun x => b + L x)) (V : Set F) (n : ℕ)
    (omega : TestFormOn V n) :
    affinePullbackTestOn L b hproper V (n + 1) (exteriorDerivativeTestOn V n omega) =
      exteriorDerivativeTestOn ((fun x => b + L x) ⁻¹' V) n
        (affinePullbackTestOn L b hproper V n omega) := by
  apply Subtype.ext
  exact (exteriorDerivative_affinePullbackForm L b omega.property.1.1).symm

/-- The globally proper affine case of Simon (6.2.23), as a genuine
continuous current, not merely an algebraic functional. -/
def GeometricCurrentOn.affinePushforward (L : E →L[ℝ] F) (b : F)
    (hproper : IsProperMap (fun x => b + L x)) {V : Set F} {n : ℕ}
    (T : GeometricCurrentOn ((fun x => b + L x) ⁻¹' V) n) :
    GeometricCurrentOn V n where
  toCurrent := T.toCurrent.comp (affinePullbackTestOn L b hproper V n)
  continuous' omegaSeq h := by
    apply T.continuous'
    simpa only [map_zero] using h.affinePullback L b hproper

@[simp] theorem GeometricCurrentOn.affinePushforward_apply (L : E →L[ℝ] F) (b : F)
    (hproper : IsProperMap (fun x => b + L x)) {V : Set F} {n : ℕ}
    (T : GeometricCurrentOn ((fun x => b + L x) ⁻¹' V) n)
    (omega : TestFormOn V n) :
    T.affinePushforward L b hproper omega = T (affinePullbackTestOn L b hproper V n omega) := rfl

/-- Simon (6.2.24)(1) for globally proper affine maps. -/
theorem GeometricCurrentOn.boundary_affinePushforward (L : E →L[ℝ] F) (b : F)
    (hproper : IsProperMap (fun x => b + L x)) {V : Set F} {n : ℕ}
    (T : GeometricCurrentOn ((fun x => b + L x) ⁻¹' V) (n + 1)) :
    (T.affinePushforward L b hproper).boundary = T.boundary.affinePushforward L b hproper := by
  apply GeometricCurrentOn.ext
  intro omega
  simp only [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.affinePushforward_apply,
    affinePullbackTestOn_exteriorDerivative]

end

end Poincare.SimonGMT.Chapter06
