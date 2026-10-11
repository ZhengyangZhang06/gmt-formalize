module

public import Poincare.SimonGMT.Chapter08.ConstancyTangent

@[expose] public section

/-!
# Local `C²` defining maps in the constancy theorem

Simon (8.4.1), proof (1)--(3), uses local manifold defining functions as
global compactly supported tests. This module constructs that extension
by a smooth cutoff and identifies the tangent plane of a regular local
level set directly from the kernel of its derivative.

The defining map need only be `C²` on its open chart and vanish on the
carrier there. Its behavior outside that chart is unrestricted. Converting
Simon's injective-parametrization definition into such normal charts is a
separate inverse-function-theorem bridge, not asserted here.
-/

open Set Filter MeasureTheory Function InnerProductSpace
open scoped Topology

namespace Poincare.SimonGMT.Chapter08.Varifold
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable {N n k : ℕ} {U M W : Set (Euclidean N)}

/-- A compact cutoff globalizes a function smooth only on the chart.
No smoothness of the original function outside that chart is required. -/
theorem contDiff_cutoff_mul_of_contDiffOn {f η : Euclidean N → ℝ}
    (hW : IsOpen W) (hf : ContDiffOn ℝ 2 f W) (hη : ContDiff ℝ 2 η)
    (hηW : tsupport η ⊆ W) : ContDiff ℝ 2 (fun x ↦ η x * f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ W
  · exact hη.contDiffAt.mul ((hf x hx).contDiffAt (hW.mem_nhds hx))
  · have hxη : x ∉ tsupport η := fun ht ↦ hx (hηW ht)
    apply (show ContDiffAt ℝ 2 (fun _ : Euclidean N ↦ (0 : ℝ)) x from
      contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxη] with y hy
    simp only [Pi.zero_apply] at hy
    simp only [hy, zero_mul]

/-- The all-support normal-annihilation conclusion for a genuinely local
defining function. The global admissible test is constructed in the proof. -/
theorem Stationary.project_gradient_eq_zero_of_local_vanishing {V : Varifold N n U}
    (hV : V.Stationary) (hM : U ∩ V.weight.support ⊆ M)
    (hW : IsOpen W) {f : Euclidean N → ℝ} (hf : ContDiffOn ℝ 2 f W)
    (hfM : EqOn f (fun _ ↦ 0) (M ∩ W))
    {z : Euclidean N × Grassmannian N n} (hz : z ∈ V.measure.support)
    (hzU : z.1 ∈ U) (hzW : z.1 ∈ W) : z.2.project (gradient f z.1) = 0 := by
  obtain ⟨η, hηW, hηc, hη, _, hηone⟩ :=
    exists_contDiff_tsupport_subset (n := 2) ((V.isOpen_domain.inter hW).mem_nhds ⟨hzU, hzW⟩)
  have hηW' : tsupport η ⊆ W := hηW.trans inter_subset_right
  have hglobal := contDiff_cutoff_mul_of_contDiffOn hW hf hη hηW'
  have hzero : f z.1 = 0 := hfM ⟨hM ⟨hzU, V.fst_mem_weight_support_of_mem_support hz⟩, hzW⟩
  have hdiff : DifferentiableAt ℝ f z.1 :=
    ((hf z.1 hzW).contDiffAt (hW.mem_nhds hzW)).differentiableAt (by norm_num)
  have hgrad : gradient (fun y ↦ η y * f y) z.1 = gradient f z.1 := by
    simp only [gradient, fderiv_fun_mul
      (hη.differentiable (by norm_num)).differentiableAt hdiff, hηone, hzero,
      one_smul, zero_smul, add_zero]
  have hgM : EqOn (fun y ↦ η y * f y) (fun _ ↦ 0) M := by
    intro x hx
    by_cases hxW : x ∈ W
    · simp only [hfM ⟨hx, hxW⟩, mul_zero]
    · have hxη : x ∉ tsupport η := fun ht ↦ hxW (hηW' ht)
      simp only [image_eq_zero_of_notMem_tsupport hxη, zero_mul]
  have h := hV.project_gradient_eq_zero_of_carrier hM hglobal hηc.mul_right
    ((tsupport_mul_subset_left (f := η) (g := f)).trans (hηW.trans inter_subset_left)) hgM hz
  rwa [hgrad] at h

/-- A local vector-valued defining map forces every support plane into
the kernel of its actual derivative. No spanning family of normals is
assumed: scalar test functions are constructed using inner products. -/
theorem Stationary.plane_le_ker_fderiv_of_local_level_set {V : Varifold N n U}
    (hV : V.Stationary) (hM : U ∩ V.weight.support ⊆ M)
    (hW : IsOpen W) {F : Euclidean N → Euclidean k} (hF : ContDiffOn ℝ 2 F W)
    (hFM : EqOn F (fun _ ↦ 0) (M ∩ W))
    {z : Euclidean N × Grassmannian N n} (hz : z ∈ V.measure.support)
    (hzU : z.1 ∈ U) (hzW : z.1 ∈ W) :
    z.2.plane ≤ (fderiv ℝ F z.1).ker := by
  intro w hw
  let q := fderiv ℝ F z.1 w
  let f : Euclidean N → ℝ := fun y ↦ inner ℝ q (F y)
  have hf : ContDiffOn ℝ 2 f W := by
    simpa only [f, Function.comp_def, innerSL_apply_apply] using
      (innerSL ℝ q).contDiff.comp_contDiffOn hF
  have hfM : EqOn f (fun _ ↦ 0) (M ∩ W) := fun y hy ↦ by
    simp only [f, hFM hy, inner_zero_right]
  have hproj := hV.project_gradient_eq_zero_of_local_vanishing hM hW hf hfM hz hzU hzW
  have hdiff := ((hF z.1 hzW).contDiffAt (hW.mem_nhds hzW)).differentiableAt (by norm_num)
  have hd : fderiv ℝ f z.1 w = inner ℝ q q := by
    have hd' := ((innerSL ℝ q).hasFDerivAt.comp z.1 hdiff.hasFDerivAt).fderiv
    have heval := congrArg (fun L : Euclidean N →L[ℝ] ℝ ↦ L w) hd'
    simpa only [f, q, Function.comp_def, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply] using heval
  have hsymm := z.2.projectionLinearMap_isSymmetric (gradient f z.1) w
  have hinner : inner ℝ (gradient f z.1) w = 0 := by
    rw [z.2.projectionLinearMap_apply_of_mem hw] at hsymm
    change inner ℝ (z.2.project (gradient f z.1)) w = _ at hsymm
    rw [hproj, inner_zero_left] at hsymm
    exact hsymm.symm
  change fderiv ℝ F z.1 w = 0
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [← hd, ← inner_gradient_left]
  exact hinner

/-- Exact tangent identification for a regular local level-set chart.
Only the geometric rank condition is needed in addition to the chart. -/
theorem Stationary.plane_eq_local_levelSetTangent {V : Varifold N n U}
    (hV : V.Stationary) (hM : U ∩ V.weight.support ⊆ M)
    (hW : IsOpen W) {F : Euclidean N → Euclidean k} (hF : ContDiffOn ℝ 2 F W)
    (hFM : EqOn F (fun _ ↦ 0) (M ∩ W))
    {z : Euclidean N × Grassmannian N n} (hz : z ∈ V.measure.support)
    (hzU : z.1 ∈ U) (hzW : z.1 ∈ W)
    (hrank : Module.finrank ℝ (fderiv ℝ F z.1).ker = n) :
    z.2 = Grassmannian.ofSubmodule (fderiv ℝ F z.1).ker hrank := by
  apply Grassmannian.eq_of_plane_eq
  rw [Grassmannian.plane_ofSubmodule]
  exact Submodule.eq_of_le_of_finrank_eq
    (hV.plane_le_ker_fderiv_of_local_level_set hM hW hF hFM hz hzU hzW)
    (z.2.finrank_plane.trans hrank.symm)

end
end Poincare.SimonGMT.Chapter08.Varifold
