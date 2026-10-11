module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.Topology.Order.LiminfLimsup
public import Poincare.SimonGMT.Chapter02.Lipschitz

public section

/-!
# Simon GMT, Chapter 2, §2: locally BV functions

This module records Simon's distributional definition (2.1), the Euclidean
divergence used there, and the variational quantity in (2.4).  The
representation by a vector-valued Radon measure, mollification, and compactness
remain separate obligations.  The variational quantity takes values in
`ℝ≥0∞`, so open sets of infinite variation are represented correctly.
-/

open Filter Function MeasureTheory Set
open scoped CompactlySupported ENNReal NNReal Topology

namespace Poincare.SimonGMT.Chapter02

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The Euclidean divergence of a vector field, defined as the trace of its
Fréchet derivative.  At a point where the derivative does not exist Mathlib's
`fderiv` (and hence this expression) is zero. -/
noncomputable def euclideanDivergence (g : E → E) (x : E) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ g x).toLinearMap

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The coordinate formula for the divergence, with respect to any
orthonormal basis. -/
theorem euclideanDivergence_eq_sum_inner {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (g : E → E) (x : E) :
    euclideanDivergence g x = ∑ i, inner ℝ (b i) (fderiv ℝ g x (b i)) :=
  LinearMap.trace_eq_sum_inner _ b

/-- The totalized derivative used in the distributional pairing is Borel
measurable, including where the field is not differentiable. -/
theorem measurable_euclideanDivergence (g : E → E) :
    Measurable (euclideanDivergence g) := by
  simp only [funext (euclideanDivergence_eq_sum_inner (stdOrthonormalBasis ℝ E) g)]
  exact Finset.measurable_sum _ fun i _ ↦
    measurable_const.inner (measurable_fderiv_apply_const ℝ g _)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The divergence of a `K`-Lipschitz field is bounded by `dim(E) K`.
This pointwise statement also covers the zero derivative assigned at
nondifferentiability points. -/
theorem norm_euclideanDivergence_le_of_lipschitz {g : E → E} {K : ℝ≥0}
    (hg : LipschitzWith K g) (x : E) :
    ‖euclideanDivergence g x‖ ≤ (Module.finrank ℝ E : ℝ) * K := by
  let b := stdOrthonormalBasis ℝ E
  rw [euclideanDivergence_eq_sum_inner b]
  calc
    ‖∑ i, inner ℝ (b i) (fderiv ℝ g x (b i))‖ ≤
        ∑ i, ‖inner ℝ (b i) (fderiv ℝ g x (b i))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E), (K : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ‖inner ℝ (b i) (fderiv ℝ g x (b i))‖ ≤
            ‖b i‖ * ‖fderiv ℝ g x (b i)‖ := norm_inner_le_norm _ _
        _ ≤ ‖b i‖ * (‖fderiv ℝ g x‖ * ‖b i‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ K := by
          simpa only [b.norm_eq_one, one_mul, mul_one] using
            norm_fderiv_le_of_lipschitz ℝ hg (x₀ := x)
    _ = (Module.finrank ℝ E : ℝ) * K := by simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Differentiation does not enlarge topological support. -/
theorem support_euclideanDivergence_subset (g : E → E) :
    support (euclideanDivergence g) ⊆ tsupport g := by
  intro x hx
  by_contra h
  exact hx (by simp [euclideanDivergence, fderiv_of_notMem_tsupport ℝ h])

/-- The supremum norm of a compactly supported continuous vector field. -/
noncomputable def compactlySupportedSupNorm (g : C_c(E, E)) : ℝ :=
  sSup (range fun x ↦ ‖g x‖)

/-- A test vector field of the class used in Simon (2.1): continuously
differentiable and compactly supported.  Compact support is part of `C_c`. -/
def IsC1TestField (g : C_c(E, E)) : Prop :=
  ContDiff ℝ 1 (g : E → E)

/-- A test vector field of the class used in Simon (2.4): Lipschitz and
compactly supported. -/
def IsLipschitzTestField (g : C_c(E, E)) : Prop :=
  ∃ K : ℝ≥0, LipschitzWith K (g : E → E)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Compactly supported `C¹` fields are admissible Lipschitz test fields. -/
theorem IsC1TestField.isLipschitzTestField {g : C_c(E, E)} (hg : IsC1TestField g) :
    IsLipschitzTestField g :=
  ContDiff.lipschitzWith_of_hasCompactSupport g.hasCompactSupport hg one_ne_zero

/-- The relation `W ⊂⊂ U`: the closure of `W` is compact and contained in
`U`. -/
def IsRelativelyCompactIn (W U : Set E) : Prop :=
  IsCompact (closure W) ∧ closure W ⊆ U

/-- Simon (2.1): local bounded variation, expressed through a uniform bound
on `∫ u div g` for every `C¹` vector field supported in each `W ⊂⊂ U`.
The leading local-integrability hypothesis is the source's `u ∈ L¹_loc(U)`.
-/
def IsLocallyBV (U : Set E) (u : E → ℝ) : Prop :=
  IsOpen U ∧ LocallyIntegrableOn u U volume ∧
    ∀ W : Set E, IsOpen W → IsRelativelyCompactIn W U →
      ∃ c : ℝ, 0 ≤ c ∧
        ∀ g : C_c(E, E), IsC1TestField g → tsupport g ⊆ W →
          ∫ x in W, u x * euclideanDivergence (g : E → E) x ∂volume ≤
            c * compactlySupportedSupNorm g

/-- The zero function is locally BV on every open set. -/
theorem isLocallyBV_zero {U : Set E} (hU : IsOpen U) :
    IsLocallyBV U (fun _ ↦ 0) := by
  refine ⟨hU, locallyIntegrableOn_zero, fun W _ _ ↦ ⟨0, le_rfl, ?_⟩⟩
  intro g _ _
  simp

/-- Simon (2.4), before packaging the resulting set function as the Radon
measure `|Du|`: the supremum of `∫ u div g` over compactly supported Lipschitz
fields in `W` having supremum norm at most one. -/
noncomputable def bvVariationOn (u : E → ℝ) (W : Set E) : ℝ≥0∞ :=
  ⨆ (g : C_c(E, E)) (_ : IsLipschitzTestField g) (_ : tsupport g ⊆ W)
    (_ : compactlySupportedSupNorm g ≤ 1),
    ENNReal.ofReal (∫ x in W, u x * euclideanDivergence (g : E → E) x ∂volume)

/-- Each admissible field is bounded above by the variational supremum. -/
theorem ofReal_integral_le_bvVariationOn (u : E → ℝ) (W : Set E)
    (g : C_c(E, E)) (hg : IsLipschitzTestField g) (hs : tsupport g ⊆ W)
    (hn : compactlySupportedSupNorm g ≤ 1) :
    ENNReal.ofReal (∫ x in W, u x * euclideanDivergence (g : E → E) x ∂volume) ≤
      bvVariationOn u W :=
  le_iSup_of_le g <| le_iSup_of_le hg <| le_iSup_of_le hs <| le_iSup_of_le hn le_rfl

@[simp] theorem bvVariationOn_zero (W : Set E) :
    bvVariationOn (fun _ : E ↦ 0) W = 0 := by
  simp [bvVariationOn]

/-- Multiplication by a bounded measurable function preserves convergence
of integrals under `L¹` convergence.  This is the analytic estimate used for
the divergence test fields in Simon 2.5(2) and the last step of 2.6. -/
theorem tendsto_integral_mul_of_lintegral_sub {α ι : Type*}
    [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
    {v : ι → α → ℝ} {u w : α → ℝ} {C : ℝ}
    (hu : AEStronglyMeasurable u μ)
    (hv : ∀ᶠ i in l, Integrable (v i) μ)
    (hw : AEStronglyMeasurable w μ) (hbound : ∀ᵐ x ∂μ, ‖w x‖ ≤ C)
    (hL1 : Tendsto (fun i ↦ ∫⁻ x, ‖v i x - u x‖ₑ ∂μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, v i x * w x ∂μ) l (𝓝 (∫ x, u x * w x ∂μ)) := by
  apply tendsto_integral_of_L1 _ (hu.mul hw)
    (hv.mono fun i hi ↦ hi.mul_bdd hw hbound)
  have hmajor : Tendsto
      (fun i ↦ (∫⁻ x, ‖v i x - u x‖ₑ ∂μ) * ENNReal.ofReal C) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hL1 (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
    (fun _ ↦ zero_le)
  intro i
  calc
    (∫⁻ x, ‖v i x * w x - u x * w x‖ₑ ∂μ) ≤
        ∫⁻ x, ‖v i x - u x‖ₑ * ENNReal.ofReal C ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hbound] with x hx
      rw [← sub_mul, enorm_mul]
      apply mul_le_mul le_rfl _ zero_le zero_le
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hx
    _ = (∫⁻ x, ‖v i x - u x‖ₑ ∂μ) * ENNReal.ofReal C :=
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top

/-- The lower-semicontinuity inequality for the variational right-hand side
of Simon (2.4), under `L¹(W)` convergence.  Identifying this quantity with the
Radon measure `|Du|` remains a separate representation theorem. -/
theorem bvVariationOn_le_liminf_of_L1 {ι : Type*} {l : Filter ι} [NeBot l]
    {W : Set E} {v : ι → E → ℝ} {u : E → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict W))
    (hv : ∀ᶠ i in l, IntegrableOn (v i) W volume)
    (hL1 : Tendsto (fun i ↦ ∫⁻ x in W, ‖v i x - u x‖ₑ ∂volume) l (𝓝 0)) :
    bvVariationOn u W ≤ liminf (fun i ↦ bvVariationOn (v i) W) l := by
  refine iSup_le fun g ↦ iSup_le fun hg ↦ iSup_le fun hs ↦ iSup_le fun hn ↦ ?_
  obtain ⟨K, hK⟩ := hg
  have hpair := tendsto_integral_mul_of_lintegral_sub hu hv
    (measurable_euclideanDivergence (g : E → E)).aestronglyMeasurable
    (ae_of_all _ (norm_euclideanDivergence_le_of_lipschitz hK)) hL1
  have hpair' := ENNReal.continuous_ofReal.tendsto _ |>.comp hpair
  rw [← hpair'.liminf_eq]
  exact liminf_le_liminf <| Eventually.of_forall fun i ↦
    ofReal_integral_le_bvVariationOn (v i) W g ⟨K, hK⟩ hs hn

/-- Convergence in `L¹_loc(U)`, expressed as convergence of the `L¹`
distance on every compact subset of `U`.  This convergence predicate is used
together with the local-integrability hypotheses on the functions. -/
def TendstoLocallyInL1On {ι : Type*} (v : ι → E → ℝ) (u : E → ℝ)
    (U : Set E) (l : Filter ι) : Prop :=
  ∀ K : Set E, IsCompact K → K ⊆ U →
    Tendsto (fun i ↦ ∫⁻ x in K, ‖v i x - u x‖ₑ ∂volume) l (𝓝 0)

/-- Local `L¹` convergence restricts to every relatively compact subset. -/
theorem TendstoLocallyInL1On.on_relativelyCompact {ι : Type*} {l : Filter ι}
    {v : ι → E → ℝ} {u : E → ℝ} {U W : Set E}
    (h : TendstoLocallyInL1On v u U l) (hW : IsRelativelyCompactIn W U) :
    Tendsto (fun i ↦ ∫⁻ x in W, ‖v i x - u x‖ₑ ∂volume) l (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h (closure W) hW.1 hW.2) (fun _ ↦ zero_le)
    (fun _ ↦ lintegral_mono_set subset_closure)

/-- The local form of the variational lower-semicontinuity argument used
in Simon 2.5(2) and at the end of 2.6.  This proves the inequality for the
explicit supremum in (2.4); construction of the variation Radon measure and
subsequence compactness are not assumed or claimed here. -/
theorem bvVariationOn_le_liminf_of_locallyL1 {ι : Type*} {l : Filter ι} [NeBot l]
    {v : ι → E → ℝ} {u : E → ℝ} {U W : Set E}
    (hu : LocallyIntegrableOn u U volume)
    (hv : ∀ᶠ i in l, LocallyIntegrableOn (v i) U volume)
    (hL1 : TendstoLocallyInL1On v u U l) (hW : IsRelativelyCompactIn W U) :
    bvVariationOn u W ≤ liminf (fun i ↦ bvVariationOn (v i) W) l := by
  apply bvVariationOn_le_liminf_of_L1
    ((hu.integrableOn_compact_subset hW.2 hW.1).mono_set subset_closure).1
    (hv.mono fun i hi ↦
      (hi.integrableOn_compact_subset hW.2 hW.1).mono_set subset_closure)
    (hL1.on_relativelyCompact hW)

/-- The limit-closure step of Simon 2.6, stated directly in terms of the
uniform distributional bounds from (2.1).  A local `L¹` limit inherits those
bounds and hence is locally BV.  Extracting a convergent subsequence remains
the compactness obligation. -/
theorem isLocallyBV_of_locallyL1_of_uniform_bound {ι : Type*} {l : Filter ι} [NeBot l]
    {v : ι → E → ℝ} {u : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hu : LocallyIntegrableOn u U volume)
    (hv : ∀ᶠ i in l, LocallyIntegrableOn (v i) U volume)
    (hL1 : TendstoLocallyInL1On v u U l)
    (hbound : ∀ W : Set E, IsOpen W → IsRelativelyCompactIn W U →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ i in l,
        ∀ g : C_c(E, E), IsC1TestField g → tsupport g ⊆ W →
          ∫ x in W, v i x * euclideanDivergence (g : E → E) x ∂volume ≤
            c * compactlySupportedSupNorm g) :
    IsLocallyBV U u := by
  refine ⟨hU, hu, fun W hWopen hW ↦ ?_⟩
  obtain ⟨c, hc, hcbound⟩ := hbound W hWopen hW
  refine ⟨c, hc, fun g hg hs ↦ ?_⟩
  obtain ⟨K, hK⟩ := hg.isLipschitzTestField
  have hpair := tendsto_integral_mul_of_lintegral_sub
    ((hu.integrableOn_compact_subset hW.2 hW.1).mono_set subset_closure).1
    (hv.mono fun i hi ↦
      (hi.integrableOn_compact_subset hW.2 hW.1).mono_set subset_closure)
    (measurable_euclideanDivergence (g : E → E)).aestronglyMeasurable
    (ae_of_all _ (norm_euclideanDivergence_le_of_lipschitz hK))
    (hL1.on_relativelyCompact hW)
  exact le_of_tendsto hpair (hcbound.mono fun i hi ↦ hi g hg hs)

end Poincare.SimonGMT.Chapter02
