module

public import Poincare.SimonGMT.Chapter08.ConstancyTangent
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

/-!
# The weak-derivative step in the constancy theorem

Simon (8.4.1), printed p. 215: a locally integrable scalar density with
zero distributional derivatives is constant on each connected open
coordinate domain. The mollifications used below are constructed from
normalized smooth bump functions, and their convergence is proved using
Mathlib's Lebesgue differentiation theorem.

This analytic step does not by itself supply the manifold charts or
absolute continuity of the original varifold weight.
-/

open Set Filter MeasureTheory Function Metric
open scoped Topology Convolution

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable {n : ℕ} {f : Euclidean n → ℝ} {U W : Set (Euclidean n)}

/-- All weak directional derivatives vanish, tested against genuine
compactly supported `C¹` scalar functions in the specified open region. -/
def WeakDerivativesZero (f : Euclidean n → ℝ) (U : Set (Euclidean n)) : Prop :=
  ∀ (φ : Euclidean n → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
    tsupport φ ⊆ U → ∀ v : Euclidean n,
      (∫ x, f x * fderiv ℝ φ x v) = 0

theorem WeakDerivativesZero.mono (hf : WeakDerivativesZero f U) (hWU : W ⊆ U) :
    WeakDerivativesZero f W :=
  fun φ hφ hc hs v ↦ hf φ hφ hc (hs.trans hWU) v

/-- Restriction away from the new boundary preserves the weak equation;
the derivative of a test function vanishes outside its topological support. -/
theorem WeakDerivativesZero.indicator (hf : WeakDerivativesZero f U)
    (hWU : W ⊆ U) {K : Set (Euclidean n)} (hWK : W ⊆ K) :
    WeakDerivativesZero (K.indicator f) W := by
  classical
  intro φ hφ hc hs v
  calc
    (∫ x, K.indicator f x * fderiv ℝ φ x v) = ∫ x, f x * fderiv ℝ φ x v := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ K
      · simp only [indicator_of_mem hx]
      · have ht : x ∉ tsupport φ := fun ht ↦ hx (hWK (hs ht))
        simp only [fderiv_of_notMem_tsupport ℝ ht, zero_apply, mul_zero]
    _ = 0 := hf φ hφ hc (hs.trans hWU) v

/-- The derivative of a convolution vanishes wherever its reflected
kernel is an admissible test function. In particular this proves the
equation for the mollified density, rather than assuming it. -/
theorem WeakDerivativesZero.fderiv_convolution_eq_zero
    (hw : WeakDerivativesZero f U) (hf : LocallyIntegrable f volume)
    {φ : Euclidean n → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    {x : Euclidean n} (hs : (fun y ↦ x - y) ⁻¹' tsupport φ ⊆ U) :
    fderiv ℝ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) x = 0 := by
  let ψ : Euclidean n → ℝ := fun y ↦ φ (x - y)
  have hψ : ContDiff ℝ 1 ψ := hφ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hψs : tsupport ψ ⊆ U :=
    (tsupport_comp_subset_preimage φ (continuous_const.sub continuous_id)).trans hs
  have hd (y : Euclidean n) :
      fderiv ℝ ψ y = -(fderiv ℝ φ (x - y)) := by
    simpa only [ψ, Function.comp_def, ContinuousLinearMap.comp_neg,
      ContinuousLinearMap.comp_id] using
      ((hφ.differentiable_one (x - y)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).const_sub x)).fderiv
  rw [(hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hφ x).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hf
    (hc.fderiv ℝ) (hφ.continuous_fderiv one_ne_zero)]
  have hz := hw ψ hψ hψc hψs v
  simp only [hd, neg_apply, mul_neg, integral_neg] at hz
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
    zero_apply] using neg_eq_zero.mp hz

/-- A concrete shrinking family; the ratio of outer to inner radii is
always two, as required by the differentiation theorem. -/
def constancyMollifier (r : ℝ) (hr : 0 < r) (k : ℕ) : ContDiffBump (0 : Euclidean n) where
  rIn := (r / (k + 1)) / 2
  rOut := r / (k + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < r / ((k : ℝ) + 1) := by positivity
    linarith

theorem constancyMollifier_rOut_le (r : ℝ) (hr : 0 < r) (k : ℕ) :
    (constancyMollifier (n := n) r hr k).rOut ≤ r := by
  exact div_le_self hr.le (by have := Nat.cast_nonneg (α := ℝ) k; linarith)

theorem constancyMollifier_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun k ↦ (constancyMollifier (n := n) r hr k).rOut) atTop (𝓝 0) := by
  simpa only [constancyMollifier, mul_one_div, mul_zero] using
    tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem ae_constancyMollifier_convolution_tendsto
    (hf : LocallyIntegrable f volume) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ x ∂volume, Tendsto (fun k ↦
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (constancyMollifier (n := n) r hr k).normed volume) x) atTop (𝓝 (f x)) := by
  have hsymm : (ContinuousLinearMap.lsmul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    exact mul_comm b a
  have hlim := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure (Euclidean n))) (K := 2)
    (constancyMollifier_tendsto (n := n) r hr)
    (Eventually.of_forall fun k ↦ by
      change r / ((k : ℝ) + 1) ≤ 2 * (r / ((k : ℝ) + 1) / 2)
      linarith) hf
  simpa only [convolution_symm (ContinuousLinearMap.lsmul ℝ ℝ) hsymm] using hlim

/-- Local weak constancy for a globally locally integrable representative.
The equation is needed only on the ball of twice the radius. -/
theorem WeakDerivativesZero.ae_eq_const_on_ball
    (hw : WeakDerivativesZero f U) (hf : LocallyIntegrable f volume)
    (a : Euclidean n) (r : ℝ) (hr : 0 < r) (hU : ball a (2 * r) ⊆ U) :
    ∃ c : ℝ, ∀ᵐ x ∂volume.restrict (ball a r), f x = c := by
  let φ (k : ℕ) := (constancyMollifier (n := n) r hr k).normed volume
  have hφ (k : ℕ) : ContDiff ℝ 1 (φ k) := ContDiffBump.contDiff_normed _
  have hc (k : ℕ) : HasCompactSupport (φ k) := ContDiffBump.hasCompactSupport_normed _
  have hd (k : ℕ) (x : Euclidean n) (hx : x ∈ ball a r) :
      fderiv ℝ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ k) x = 0 := by
    apply hw.fderiv_convolution_eq_zero hf (hφ k) (hc k)
    intro y hy
    apply hU
    have hxy : dist y x ≤ r := by
      have hy' : x - y ∈ closedBall (0 : Euclidean n)
          (constancyMollifier (n := n) r hr k).rOut := by
        simpa only [φ, mem_preimage, ContDiffBump.tsupport_normed_eq] using hy
      have hnorm := (mem_closedBall_zero_iff.mp hy').trans (constancyMollifier_rOut_le r hr k)
      simpa only [dist_comm y x, dist_eq_norm] using hnorm
    have hxa : dist x a < r := hx
    change dist y a < 2 * r
    calc
      dist y a ≤ dist y x + dist x a := dist_triangle y x a
      _ ≤ r + dist x a := by linarith
      _ < 2 * r := by linarith
  have heq (k : ℕ) {x y : Euclidean n} (hx : x ∈ ball a r) (hy : y ∈ ball a r) :
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ k) x =
        (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ k) y :=
    isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball a r).isPreconnected
      ((hc k).contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf
        (hφ k)).differentiable_one.differentiableOn (hd k) hx hy
  have hlim := ae_constancyMollifier_convolution_tendsto hf r hr
  obtain ⟨x₀, hx₀, hlim₀⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (measure_ball_pos volume a hr).ne' (ae_restrict_of_ae hlim)
  refine ⟨f x₀, ?_⟩
  filter_upwards [ae_restrict_of_ae hlim, ae_restrict_mem measurableSet_ball] with x hx hxb
  apply tendsto_nhds_unique hx
  exact hlim₀.congr' (Eventually.of_forall fun k ↦ heq k hx₀ hxb)

/-- Local integrability only on the original open set is sufficient.
No extension across its boundary is assumed locally integrable. -/
theorem WeakDerivativesZero.exists_ae_eq_const_nhds
    (hw : WeakDerivativesZero f U) (hf : LocallyIntegrableOn f U volume)
    (hU : IsOpen U) {a : Euclidean n} (ha : a ∈ U) :
    ∃ W : Set (Euclidean n), IsOpen W ∧ a ∈ W ∧ W ⊆ U ∧
      ∃ c : ℝ, ∀ᵐ x ∂volume.restrict W, f x = c := by
  classical
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let K := closedBall a (R / 2)
  have hKU : K ⊆ U := (closedBall_subset_ball (by linarith : R / 2 < R)).trans hRU
  have hg : LocallyIntegrable (K.indicator f) volume :=
    ((hf.integrableOn_compact_subset hKU (isCompact_closedBall a (R / 2))).integrable_indicator
      measurableSet_closedBall).locallyIntegrable
  have hwg : WeakDerivativesZero (K.indicator f) (ball a (R / 2)) :=
    hw.indicator (ball_subset_closedBall.trans hKU) ball_subset_closedBall
  have hsmall : ball a (R / 4) ⊆ K :=
    (ball_subset_ball (by linarith : R / 4 ≤ R / 2)).trans ball_subset_closedBall
  obtain ⟨c, hc⟩ := hwg.ae_eq_const_on_ball hg a (R / 4) (by positivity) (by
    rw [show 2 * (R / 4) = R / 2 by ring])
  refine ⟨ball a (R / 4), isOpen_ball, mem_ball_self (by positivity), hsmall.trans hKU, c, ?_⟩
  filter_upwards [hc, ae_restrict_mem measurableSet_ball] with x hx hxb
  simpa only [indicator_of_mem (hsmall hxb)] using hx

/-- Two a.e. constant representatives on open sets have the same value
whenever the sets meet. Positivity of open sets is the essential hypothesis. -/
theorem eq_of_ae_eq_const_on_open_inter
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure] {g : X → ℝ} {A B : Set X} {c d : ℝ}
    (hA : IsOpen A) (hB : IsOpen B) (hne : (A ∩ B).Nonempty)
    (hc : ∀ᵐ x ∂μ.restrict A, g x = c) (hd : ∀ᵐ x ∂μ.restrict B, g x = d) :
    c = d := by
  have hcd : ∀ᵐ x ∂μ.restrict (A ∩ B), c = d := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hc,
      ae_restrict_of_ae_restrict_of_subset inter_subset_right hd] with x hx hy
    exact hx.symm.trans hy
  obtain ⟨_, _, h⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    ((hA.inter hB).measure_pos μ hne).ne' hcd
  exact h

/-- Connected gluing for locally a.e. constant scalar functions. The
countable subcover is essential: arbitrary unions of exceptional null
sets are not silently discarded. This form also applies to chart domains
and manifold measures that are positive on nonempty open sets. -/
theorem ae_eq_const_of_locally_ae_eq_const
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure] {g : X → ℝ} {D : Set X}
    (hD : IsPreconnected D)
    (hloc : ∀ x ∈ D, ∃ A : Set X, IsOpen A ∧ x ∈ A ∧ A ⊆ D ∧
      ∃ c : ℝ, ∀ᵐ y ∂μ.restrict A, g y = c) :
    ∃ c : ℝ, ∀ᵐ x ∂μ.restrict D, g x = c := by
  classical
  choose A hAo hxA hAD c hc using fun x : D ↦ hloc x x.2
  have hlc : IsLocallyConstant c := by
    apply (IsLocallyConstant.iff_eventually_eq c).mpr
    intro x
    have hn : ∀ᶠ y : D in 𝓝 x, (y : X) ∈ A x :=
      continuous_subtype_val.continuousAt ((hAo x).mem_nhds (hxA x))
    filter_upwards [hn] with y hy
    exact eq_of_ae_eq_const_on_open_inter (hAo y) (hAo x)
      ⟨y, hxA y, hy⟩ (hc y) (hc x)
  let : PreconnectedSpace D := isPreconnected_iff_preconnectedSpace.mp hD
  obtain ⟨c₀, hconst⟩ := hlc.exists_eq_const
  have hcover : D ⊆ ⋃ x : D, A x := fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hxA ⟨x, hx⟩⟩
  obtain ⟨T, hTc, hTD⟩ := (HereditarilyLindelofSpace.isLindelof D).elim_countable_subcover
    A hAo hcover
  refine ⟨c₀, ae_restrict_of_ae_restrict_of_subset hTD ?_⟩
  apply (ae_restrict_biUnion_iff A hTc (fun x ↦ g x = c₀)).mpr
  intro x _
  have hcx : c x = c₀ := congrFun hconst x
  simpa only [hcx] using hc x

/-- The full `L¹_loc` distributional constancy statement used in Simon
(8.4.1): the connectedness belongs to the actual open coordinate domain. -/
theorem WeakDerivativesZero.ae_eq_const
    (hw : WeakDerivativesZero f U) (hf : LocallyIntegrableOn f U volume)
    (hU : IsOpen U) (hconn : IsPreconnected U) :
    ∃ c : ℝ, ∀ᵐ x ∂volume.restrict U, f x = c :=
  ae_eq_const_of_locally_ae_eq_const hconn fun _ hx ↦ hw.exists_ae_eq_const_nhds hf hU hx

/-- Integrability of the operator-valued weak-test integrand follows
from local integrability on the domain and compact support of the test. -/
theorem integrable_density_fderiv (hf : LocallyIntegrableOn f U volume)
    {φ : Euclidean n → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U) :
    Integrable (fun x ↦ f x • fderiv ℝ φ x) volume := by
  classical
  have hg : LocallyIntegrable ((tsupport φ).indicator f) volume :=
    ((hf.integrableOn_compact_subset hs hc).integrable_indicator
      (isClosed_tsupport φ).measurableSet).locallyIntegrable
  have hint := hg.integrable_smul_right_of_hasCompactSupport
    (hφ.continuous_fderiv one_ne_zero) (hc.fderiv ℝ)
  apply hint.congr
  filter_upwards with x
  by_cases hx : x ∈ tsupport φ
  · simp only [indicator_of_mem hx]
  · simp only [fderiv_of_notMem_tsupport ℝ hx, smul_zero]

/-- Testing the partial derivatives in any vector-space basis suffices.
This matches the coordinate tests in the printed proof. -/
theorem weakDerivativesZero_of_basis {ι : Type*} (b : Module.Basis ι ℝ (Euclidean n))
    (hf : LocallyIntegrableOn f U volume)
    (hw : ∀ (φ : Euclidean n → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∀ i : ι, (∫ x, f x * fderiv ℝ φ x (b i)) = 0) :
    WeakDerivativesZero f U := by
  intro φ hφ hc hs v
  have hint := integrable_density_fderiv hf hφ hc hs
  let L : Euclidean n →L[ℝ] ℝ := ∫ x, f x • fderiv ℝ φ x
  have hL : L.toLinearMap = 0 := by
    apply b.ext
    intro i
    change (∫ x, f x • fderiv ℝ φ x) (b i) = 0
    rw [ContinuousLinearMap.integral_apply hint]
    exact hw φ hφ hc hs i
  have hv : L v = 0 := LinearMap.congr_fun hL v
  change (∫ x, f x • fderiv ℝ φ x) v = 0 at hv
  rw [ContinuousLinearMap.integral_apply hint] at hv
  exact hv

/-- Source-coordinate version of distributional constancy, without
assuming pointwise differentiability or continuity of the density. -/
theorem ae_eq_const_of_weak_coordinate_derivatives_zero
    (hf : LocallyIntegrableOn f U volume) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hw : ∀ (φ : Euclidean n → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∀ i : Fin n,
        (∫ x, f x * fderiv ℝ φ x ((EuclideanSpace.basisFun (Fin n) ℝ) i)) = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂volume.restrict U, f x = c :=
  (weakDerivativesZero_of_basis (EuclideanSpace.basisFun (Fin n) ℝ).toBasis hf hw).ae_eq_const
    hf hU hconn

end
end Poincare.SimonGMT.Chapter08
