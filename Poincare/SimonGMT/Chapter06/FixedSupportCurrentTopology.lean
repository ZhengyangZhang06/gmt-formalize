module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Topology.Sequences
public import Poincare.SimonGMT.Chapter06.Currents

@[expose] public section

/-!
# The fixed-support topology of a current

This file connects Simon's sequential definition of a current with the actual
locally convex space of smooth forms supported in a fixed compact set. The
restriction of every geometric current is a continuous linear functional on
that space, and consequently is bounded by finitely many uniform derivative
seminorms. This is the analytic prerequisite for the parameter-dependent
slicing construction in (6.2.17); no product current is assumed here.

The regularity order in `ContDiffMapSupportedIn` is `ℕ∞`, so its `⊤` is the
genuine smooth order `∞` after coercion to the `ℕ∞ω` used by `ContDiff`.
-/

open Filter Function Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace Poincare.SimonGMT.Chapter06

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smooth differential forms with support in a fixed compact set, equipped
with the topology of uniform convergence of all finite-order derivatives. -/
abbrev FixedSupportTestForm (K : Compacts E) (n : ℕ) :=
  ContDiffMapSupportedIn E (Covector E n) (⊤ : ℕ∞) K

/-- The actual inclusion of a fixed-support form into Simon's test-form space. -/
def fixedSupportTestFormInclusion {U : Set E} (K : Compacts E)
    (hKU : (K : Set E) ⊆ U) (n : ℕ) :
    FixedSupportTestForm K n →ₗ[ℝ] TestFormOn U n where
  toFun omega := ⟨omega, ⟨omega.contDiff, omega.compact_supp⟩,
    omega.tsupport_subset.trans hKU⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] theorem fixedSupportTestFormInclusion_coe {U : Set E} (K : Compacts E)
    (hKU : (K : Set E) ⊆ U) (n : ℕ) (omega : FixedSupportTestForm K n) :
    (fixedSupportTestFormInclusion K hKU n omega : DifferentialForm E n) = omega := rfl

/-- The fixed-support topology is exactly uniform convergence of every
derivative on the fixed compact set; the derivatives vanish off that set. -/
theorem fixedSupportTestForm_tendsto_iff (K : Compacts E) {n : ℕ}
    {ι : Type*} {l : Filter ι} {omegaSeq : ι → FixedSupportTestForm K n}
    {omega : FixedSupportTestForm K n} :
    Tendsto omegaSeq l (𝓝 omega) ↔ ∀ k : ℕ,
      TendstoUniformlyOn
        (fun j x => iteratedFDeriv ℝ k (omegaSeq j : DifferentialForm E n) x)
        (fun x => iteratedFDeriv ℝ k (omega : DifferentialForm E n) x) l K := by
  constructor
  · intro h k
    have hk := (ContDiffMapSupportedIn.structureMapCLM ℝ (⊤ : ℕ∞) k).continuous.tendsto omega
    have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hk.comp h)
    simpa only [Function.comp_def, ContDiffMapSupportedIn.structureMapCLM_top_apply] using
      hu.tendstoUniformlyOn (s := K)
  · intro h
    apply (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM
      (𝕜 := ℝ) (E := E) (F := Covector E n) (n := (⊤ : ℕ∞))
      (K := K)).isEmbedding.isInducing.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro k
    change Tendsto (fun j => ContDiffMapSupportedIn.structureMapCLM ℝ (⊤ : ℕ∞) k (omegaSeq j))
      l (𝓝 (ContDiffMapSupportedIn.structureMapCLM ℝ (⊤ : ℕ∞) k omega))
    apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
    simp only [ContDiffMapSupportedIn.structureMapCLM_top_apply]
    intro V hV
    filter_upwards [h k V hV] with j hj x
    by_cases hx : x ∈ K
    · exact hj x hx
    · simpa only [omega.iteratedFDeriv_zero_on_compl hx,
        (omegaSeq j).iteratedFDeriv_zero_on_compl hx, Pi.zero_apply] using
        (refl_mem_uniformity hV : ((0 : E [×k]→L[ℝ] Covector E n), 0) ∈ V)

/-- Convergence in the fixed-support locally convex topology implies exactly
the all-derivatives convergence required in Simon's definition. -/
theorem fixedSupportTestFormInclusion_converges {U : Set E} (K : Compacts E)
    (hKU : (K : Set E) ⊆ U) {n : ℕ}
    {omegaSeq : ℕ → FixedSupportTestForm K n} {omega : FixedSupportTestForm K n}
    (h : Tendsto omegaSeq atTop (𝓝 omega)) :
    TestFormOnConverges
      (fun j => fixedSupportTestFormInclusion K hKU n (omegaSeq j))
      (fixedSupportTestFormInclusion K hKU n omega) := by
  refine ⟨K, K.isCompact, hKU, fun j => (omegaSeq j).tsupport_subset,
    omega.tsupport_subset, ?_⟩
  exact (fixedSupportTestForm_tendsto_iff K).mp h

/-- Simon's sequential current condition implies genuine continuity on every
fixed-support smooth-form space. Countably many derivative seminorms make
that space first countable; thus no additional continuity assumption is used. -/
theorem GeometricCurrentOn.continuous_fixedSupport {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn U n) (K : Compacts E) (hKU : (K : Set E) ⊆ U) :
    Continuous (T.toCurrent.comp (fixedSupportTestFormInclusion K hKU n)) := by
  let : FirstCountableTopology (FixedSupportTestForm K n) :=
    (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM
      (𝕜 := ℝ) (E := E) (F := Covector E n) (n := (⊤ : ℕ∞)) (K := K)).isEmbedding.firstCountableTopology
  apply continuous_of_tendsto_nhds_zero
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro omegaSeq hseq
  apply T.continuous'
  simpa only [map_zero] using fixedSupportTestFormInclusion_converges K hKU hseq

/-- A geometric current restricted to a compact support, as a genuine
continuous linear functional on Mathlib's smooth-function space. -/
def GeometricCurrentOn.fixedSupportCLM {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn U n) (K : Compacts E) (hKU : (K : Set E) ⊆ U) :
    FixedSupportTestForm K n →L[ℝ] ℝ where
  toLinearMap := T.toCurrent.comp (fixedSupportTestFormInclusion K hKU n)
  cont := T.continuous_fixedSupport K hKU

@[simp] theorem GeometricCurrentOn.fixedSupportCLM_apply {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn U n) (K : Compacts E) (hKU : (K : Set E) ⊆ U)
    (omega : FixedSupportTestForm K n) :
    T.fixedSupportCLM K hKU omega = T (fixedSupportTestFormInclusion K hKU n omega) := rfl

/-- On each fixed compact support, a current is bounded by a positive constant
times the maximum of the uniform derivative seminorms through some finite
order. This is the finite-order estimate used to justify slicing in (6.2.17). -/
theorem GeometricCurrentOn.exists_fixedSupport_order_bound {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn U n) (K : Compacts E) (hKU : (K : Set E) ⊆ U) :
    ∃ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ omega : FixedSupportTestForm K n,
      |T (fixedSupportTestFormInclusion K hKU n omega)| ≤
        C * ContDiffMapSupportedIn.supSeminorm ℝ E (Covector E n) (⊤ : ℕ∞) K m omega := by
  classical
  let p := ContDiffMapSupportedIn.seminorm ℝ E (Covector E n) (⊤ : ℕ∞) K
  let q := (normSeminorm ℝ ℝ).comp (T.fixedSupportCLM K hKU).toLinearMap
  have hq : Continuous q := continuous_norm.comp (T.fixedSupportCLM K hKU).continuous
  obtain ⟨s, C, hC, hbound⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℝ E (Covector E n) (⊤ : ℕ∞) K) q hq
  refine ⟨s.sup id, C, NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC), ?_⟩
  intro omega
  have hs : s.sup p ≤ (Finset.Iic (s.sup id)).sup p := by
    apply Finset.sup_mono
    intro i hi
    exact Finset.mem_Iic.mpr (Finset.le_sup (f := id) hi)
  calc
    |T (fixedSupportTestFormInclusion K hKU n omega)| = q omega := rfl
    _ ≤ (C • s.sup p) omega := hbound omega
    _ ≤ C * ((Finset.Iic (s.sup id)).sup p) omega :=
      mul_le_mul_of_nonneg_left (hs omega) C.coe_nonneg

/-- The finite-order estimate stated directly for Simon's test forms: on a
fixed compact support, uniform bounds on finitely many derivatives bound the
current's value. The order and constant depend only on the current and compact
set, not on the test form or its derivative bound. -/
theorem GeometricCurrentOn.exists_compact_derivative_bound {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn U n) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (omega : TestFormOn U n) (D : ℝ),
      tsupport (omega : DifferentialForm E n) ⊆ K → 0 ≤ D →
      (∀ k ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (omega : DifferentialForm E n) x‖ ≤ D) →
      |T omega| ≤ C * D := by
  let Kc : Compacts E := ⟨K, hK⟩
  obtain ⟨m, C, hC, hbound⟩ := T.exists_fixedSupport_order_bound Kc hKU
  refine ⟨m, C, hC, ?_⟩
  intro omega D hsupp hD hderiv
  let omegaK : FixedSupportTestForm Kc n :=
    ContDiffMapSupportedIn.of_support_subset omega.property.1.1
      ((subset_tsupport (omega : DifferentialForm E n)).trans hsupp)
  have hincl : fixedSupportTestFormInclusion Kc hKU n omegaK = omega := Subtype.ext rfl
  have hp : ContDiffMapSupportedIn.supSeminorm ℝ E (Covector E n) (⊤ : ℕ∞) Kc m omegaK ≤ D := by
    apply Seminorm.finset_sup_apply_le hD
    intro k hk
    exact (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ hD k omegaK).mpr
      (hderiv k (Finset.mem_Iic.mp hk))
  calc
    |T omega| = |T (fixedSupportTestFormInclusion Kc hKU n omegaK)| := by rw [hincl]
    _ ≤ C * ContDiffMapSupportedIn.supSeminorm ℝ E (Covector E n) (⊤ : ℕ∞) Kc m omegaK :=
      hbound omegaK
    _ ≤ C * D := mul_le_mul_of_nonneg_left hp hC.le

/-- Genuine `C∞` test forms can take any prescribed covector value at an
interior point. In particular these spaces are not restricted to analytic
compactly supported forms. -/
theorem exists_testFormOn_eq_at [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) {n : ℕ} (alpha : Covector E n) :
    ∃ omega : TestFormOn U n, (omega : DifferentialForm E n) x = alpha := by
  obtain ⟨f, hsupport, hcompact, hsmooth, -, hvalue⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hU.mem_nhds hx)
  refine ⟨⟨fun y => f y • alpha, ?_⟩, ?_⟩
  · refine ⟨⟨hsmooth.smul contDiff_const, ?_⟩, ?_⟩
    · exact hcompact.smul_right
    · exact (tsupport_smul_subset_left f (fun _ => alpha)).trans hsupport
  · change f x • alpha = alpha
    rw [hvalue, one_smul]

end

end Poincare.SimonGMT.Chapter06
