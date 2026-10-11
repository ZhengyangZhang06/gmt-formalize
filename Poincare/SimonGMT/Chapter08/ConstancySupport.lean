module

public import Poincare.SimonGMT.Chapter08.RadialFirstVariation
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

/-!
# The nonnegative test in the general-varifold constancy theorem

Simon (8.4.1), proof (1)--(2): for a `C²` function vanishing on the
carrier, stationarity of the test field `f ∇f` forces `p_S ∇f = 0` on
the entire support of the varifold. Integrability, admissibility, and
the passage from almost everywhere to support are all proved here.

This is a construction step, not the full constancy theorem. The
manifold charts, Hausdorff absolute continuity, and constancy of the
resulting density are separate obligations.

Source: `Simon-gmt new.pdf`, printed pp. 213--214, PDF objects 219--221.
-/

open Set Filter MeasureTheory Function InnerProductSpace
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08.Varifold
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {N n : ℕ} {U : Set (Euclidean N)}

theorem contDiff_gradient_of_contDiff_two {f : Euclidean N → ℝ}
    (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (gradient f) :=
  (toDual ℝ (Euclidean N)).symm.contDiff.comp (hf.fderiv_right (by norm_num))

/-- The source field, constructed in the existing `C¹_c(U)` test space. -/
def gradientProductTest {f : Euclidean N → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (hU : tsupport f ⊆ U) : TestVectorField (N := N) U where
  toFun x := f x • gradient f x
  contDiff := (hf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).smul
    (contDiff_gradient_of_contDiff_two hf)
  compactSupport := hc.smul_right
  support_subset := (tsupport_smul_subset_left f (gradient f)).trans hU

theorem ae_fst_mem_weight_support (V : Varifold N n U) :
    ∀ᵐ z ∂V.measure, z.1 ∈ V.weight.support :=
  ae_of_ae_map measurable_fst.aemeasurable V.weight.support_mem_ae

theorem fst_mem_weight_support_of_mem_support (V : Varifold N n U)
    {z : Euclidean N × Grassmannian N n} (hz : z ∈ V.measure.support) :
    z.1 ∈ V.weight.support :=
  Measure.support_subset_of_isClosed
    (V.weight.isClosed_support.preimage continuous_fst) V.ae_fst_mem_weight_support hz

/-- The printed support hypothesis gives concentration on the carrier,
even if the carrier has not been assumed closed or measurable. -/
theorem ae_mem_carrier_of_support_subset (V : Varifold N n U)
    {M : Set (Euclidean N)} (hM : U ∩ V.weight.support ⊆ M) :
    ∀ᵐ z ∂V.measure, z.1 ∈ M := by
  filter_upwards [V.ae_mem_domain, V.ae_fst_mem_weight_support] with z hz hs
  exact hM ⟨hz.1, hs⟩

/-- The pointwise identity used in proof (1), on the zero set of `f`. -/
theorem tangentialDivergence_gradientProductTest {f : Euclidean N → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (hU : tsupport f ⊆ U)
    (x : Euclidean N) (S : Grassmannian N n) (hx : f x = 0) :
    tangentialDivergence (gradientProductTest hf hc hU) x S =
      ‖S.project (gradient f x)‖ ^ 2 := by
  change tangentialDivergence (fun y ↦ f y • gradient f y) x S = _
  rw [tangentialDivergence_smul f (gradient f) x S
    (hf.differentiable (by norm_num)).differentiableAt
    (contDiff_gradient_of_contDiff_two hf).differentiable_one.differentiableAt,
    hx, zero_mul, zero_add, ← inner_gradient_left, S.inner_project_eq_norm_sq]

/-- The nonnegative integral in Simon's proof is genuinely integrable.
No stationarity is required for this first-variation identity. -/
theorem firstVariation_gradientProductTest (V : Varifold N n U)
    {f : Euclidean N → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (hU : tsupport f ⊆ U)
    (hfzero : ∀ᵐ x ∂V.weight, f x = 0) :
    Integrable (fun z : Euclidean N × Grassmannian N n ↦
      ‖z.2.project (gradient f z.1)‖ ^ 2) V.measure ∧
    V.firstVariation (gradientProductTest hf hc hU) =
      ∫ z, ‖z.2.project (gradient f z.1)‖ ^ 2 ∂V.measure := by
  let X := gradientProductTest hf hc hU
  have hEq : (fun z : Euclidean N × Grassmannian N n ↦ tangentialDivergence X z.1 z.2) =ᵐ[V.measure]
      (fun z ↦ ‖z.2.project (gradient f z.1)‖ ^ 2) := by
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hfzero] with z hz
    exact tangentialDivergence_gradientProductTest hf hc hU z.1 z.2 hz
  refine ⟨(V.integrable_tangentialDivergence X X.contDiff X.compactSupport X.support_subset).congr hEq,
    integral_congr_ae hEq⟩

theorem Stationary.ae_project_gradient_eq_zero {V : Varifold N n U}
    (hV : V.Stationary) {f : Euclidean N → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (hU : tsupport f ⊆ U)
    (hfzero : ∀ᵐ x ∂V.weight, f x = 0) :
    ∀ᵐ z ∂V.measure, z.2.project (gradient f z.1) = 0 := by
  obtain ⟨hint, heq⟩ := V.firstVariation_gradientProductTest hf hc hU hfzero
  have hz : (∫ z, ‖z.2.project (gradient f z.1)‖ ^ 2 ∂V.measure) = 0 :=
    heq.symm.trans (hV (gradientProductTest hf hc hU))
  have hae := (integral_eq_zero_iff_of_nonneg (fun z ↦ sq_nonneg _) hint).mp hz
  filter_upwards [hae] with z hz
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

/-- Simon proof (2): continuity upgrades the a.e. conclusion to every
point of the actual measure support, including all plane fibers. -/
theorem Stationary.project_gradient_eq_zero_of_mem_support {V : Varifold N n U}
    (hV : V.Stationary) {f : Euclidean N → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (hU : tsupport f ⊆ U)
    (hfzero : ∀ᵐ x ∂V.weight, f x = 0)
    {z : Euclidean N × Grassmannian N n} (hz : z ∈ V.measure.support) :
    z.2.project (gradient f z.1) = 0 := by
  have hg : Continuous (gradient f) := (contDiff_gradient_of_contDiff_two hf).continuous
  have hpair : Continuous (fun z : Euclidean N × Grassmannian N n ↦
      (z.2, gradient f z.1)) := continuous_snd.prodMk (hg.comp continuous_fst)
  have hcont := (Grassmannian.continuous_project (N := N) (n := n)).comp hpair
  exact Measure.support_subset_of_isClosed (isClosed_eq hcont continuous_const)
    (hV.ae_project_gradient_eq_zero hf hc hU hfzero) hz

theorem Stationary.project_gradient_eq_zero_of_carrier {V : Varifold N n U}
    (hV : V.Stationary) {M : Set (Euclidean N)} (hM : U ∩ V.weight.support ⊆ M)
    {f : Euclidean N → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (hU : tsupport f ⊆ U) (hfM : EqOn f (fun _ ↦ 0) M)
    {z : Euclidean N × Grassmannian N n} (hz : z ∈ V.measure.support) :
    z.2.project (gradient f z.1) = 0 := by
  apply hV.project_gradient_eq_zero_of_mem_support hf hc hU ?_ hz
  have hUW : ∀ᵐ x ∂V.weight, x ∈ U := by
    rw [ae_iff]
    change V.weight Uᶜ = 0
    rw [V.weight_apply V.isOpen_domain.measurableSet.compl]
    exact V.supported
  filter_upwards [hUW, V.weight.support_mem_ae] with x hx hs
  exact hfM (hM ⟨hx, hs⟩)

/-- Compact support of a defining function is not an extra geometric
assumption: a smooth bump in `U` preserves its gradient at a carrier
point and gives the admissible test required above. -/
theorem Stationary.project_gradient_eq_zero_of_vanishing {V : Varifold N n U}
    (hV : V.Stationary) {M : Set (Euclidean N)} (hM : U ∩ V.weight.support ⊆ M)
    {f : Euclidean N → ℝ} (hf : ContDiff ℝ 2 f) (hfM : EqOn f (fun _ ↦ 0) M)
    {z : Euclidean N × Grassmannian N n} (hz : z ∈ V.measure.support) (hzU : z.1 ∈ U) :
    z.2.project (gradient f z.1) = 0 := by
  obtain ⟨η, hηU, hηc, hη, _, hηone⟩ :=
    exists_contDiff_tsupport_subset (n := 2) (V.isOpen_domain.mem_nhds hzU)
  have hzero : f z.1 = 0 := hfM (hM ⟨hzU, V.fst_mem_weight_support_of_mem_support hz⟩)
  have hgrad : gradient (fun y ↦ η y * f y) z.1 = gradient f z.1 := by
    simp only [gradient, fderiv_fun_mul
      (hη.differentiable (by norm_num)).differentiableAt
      (hf.differentiable (by norm_num)).differentiableAt, hηone, hzero,
      one_smul, zero_smul, add_zero]
  have h := hV.project_gradient_eq_zero_of_carrier hM (hη.mul hf) hηc.mul_right
    ((tsupport_mul_subset_left (f := η) (g := f)).trans hηU)
    (fun x hx ↦ by simp [hfM hx]) hz
  rwa [hgrad] at h

end
end Poincare.SimonGMT.Chapter08.Varifold
