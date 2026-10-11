module

public import Poincare.SimonGMT.Chapter08.ConstancyChartVariation
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import all Poincare.SimonGMT.Chapter02.Submanifold

@[expose] public section

/-!
# The missing domain hypothesis in the printed constancy theorem

Simon (8.4.1), PDF object 219, assumes that `M` is connected, but neither
that `M ⊆ U` nor that `M ∩ U` is connected. The proof (object 221) obtains
local constancy only on `M ∩ U` and then uses connectedness of `M`.

The literal statement is false. The positive half-line, regarded as a
one-dimensional varifold in the punctured line, is stationary there. Its
weight is supported on the connected smooth manifold consisting of the
whole line, but is not a constant multiple of the manifold measure on the
domain. All measures and stationarity below use the actual varifold model.
-/

open Set Function MeasureTheory
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08.ConstancyDomainCounterexample
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- Standard isometric coordinates on the one-dimensional ambient space. -/
def coordinateEquiv : ℝ ≃ₗᵢ[ℝ] Euclidean 1 :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr

/-- The ambient open set omits the chosen cut point. -/
def domain (a : ℝ) : Set (Euclidean 1) :=
  coordinateEquiv.symm ⁻¹' ({a} : Set ℝ)ᶜ

theorem isOpen_domain (a : ℝ) : IsOpen (domain a) :=
  isClosed_singleton.isOpen_compl.preimage coordinateEquiv.symm.continuous

/-- The unique full-dimensional tangent plane. -/
def fullPlane : Grassmannian 1 1 :=
  Grassmannian.ofSubmodule ⊤ (by simp)

def bundle (t : ℝ) : Euclidean 1 × Grassmannian 1 1 :=
  (coordinateEquiv t, fullPlane)

theorem measurableEmbedding_bundle : MeasurableEmbedding bundle :=
  coordinateEquiv.toHomeomorph.measurableEmbedding.prodMk_right fullPlane

/-- A genuine varifold, obtained by placing positive-half-line length on
the graph of its tangent plane. -/
def halfLineVarifold (a : ℝ) : Varifold 1 1 (domain a) where
  isOpen_domain := isOpen_domain a
  measure := (volume.restrict (Ioi a)).map bundle
  supported := by
    rw [measurableEmbedding_bundle.map_apply,
      Measure.restrict_apply (measurableEmbedding_bundle.measurable
        ((isOpen_domain a).measurableSet.compl.prod MeasurableSet.univ))]
    have he : bundle ⁻¹' ((domain a)ᶜ ×ˢ (univ : Set (Grassmannian 1 1))) ∩ Ioi a = ∅ := by
      ext t
      simp only [bundle, domain, mem_inter_iff, mem_preimage, mem_prod,
        mem_compl_iff, mem_univ, and_true, LinearIsometryEquiv.symm_apply_apply,
        mem_singleton_iff, not_not, mem_Ioi, mem_empty_iff_false, iff_false]
      rintro ⟨rfl, h⟩
      exact lt_irrefl _ h
    rw [he, measure_empty]
  finite_on_compact := by
    intro K hK _
    rw [measurableEmbedding_bundle.map_apply]
    have he : bundle ⁻¹' (K ×ˢ (univ : Set (Grassmannian 1 1))) =
        coordinateEquiv ⁻¹' K := by ext t; simp [bundle]
    rw [he]
    exact (coordinateEquiv.toHomeomorph.isCompact_preimage.mpr hK).measure_ne_top

theorem weight_halfLineVarifold (a : ℝ) : (halfLineVarifold a).weight =
    (volume.restrict (Ioi a)).map coordinateEquiv := by
  rw [Varifold.weight, halfLineVarifold,
    Measure.map_map measurable_fst measurableEmbedding_bundle.measurable]
  rfl

/-- On the line, tangential divergence is the derivative in isometric
scalar coordinates. This is derived from the actual trace definition. -/
theorem tangentialDivergence_eq_deriv
    {X : Euclidean 1 → Euclidean 1} (hX : ContDiff ℝ 1 X) (t : ℝ) :
    Varifold.tangentialDivergence X (coordinateEquiv t) fullPlane =
      deriv (fun s ↦ coordinateEquiv.symm (X (coordinateEquiv s))) t := by
  have hD : (fderiv ℝ X (coordinateEquiv t)).toLinearMap =
      coordinateEquiv.symm.toLinearEquiv.toLinearMap.smulRight
        ((fderiv ℝ X (coordinateEquiv t)) (coordinateEquiv 1)) := by
    apply LinearMap.ext
    intro x
    change (fderiv ℝ X (coordinateEquiv t)) x =
      coordinateEquiv.symm x • (fderiv ℝ X (coordinateEquiv t)) (coordinateEquiv 1)
    rw [← map_smul]
    congr 1
    rw [← map_smul, smul_eq_mul, mul_one, LinearIsometryEquiv.apply_symm_apply]
  have hd := coordinateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
    t ((hX.differentiable_one (coordinateEquiv t)).hasFDerivAt.comp_hasDerivAt t
      (coordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap.hasDerivAt))
  rw [Varifold.tangentialDivergence_eq_trace]
  simp only [fullPlane, Grassmannian.plane_ofSubmodule, Submodule.starProjection_top,
    ContinuousLinearMap.coe_id, LinearMap.comp_id, hD, LinearMap.trace_smulRight]
  exact hd.deriv.symm

/-- The half-line boundary lies outside the open domain, so its genuine
first variation vanishes on every admissible test vector field. -/
theorem stationary_halfLineVarifold (a : ℝ) : (halfLineVarifold a).Stationary := by
  intro X
  let g : ℝ → ℝ := fun t ↦ coordinateEquiv.symm (X (coordinateEquiv t))
  have hg : ContDiff ℝ 1 g :=
    coordinateEquiv.symm.toContinuousLinearEquiv.contDiff.comp
      (X.contDiff.comp coordinateEquiv.toContinuousLinearEquiv.contDiff)
  have hgc : HasCompactSupport g :=
    (X.compactSupport.comp_homeomorph coordinateEquiv.toHomeomorph).comp_left
      coordinateEquiv.symm.map_zero
  have hXa : X (coordinateEquiv a) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have h0 := X.support_subset h
    simp [domain] at h0
  have hga : g a = 0 := by simp [g, hXa]
  rw [Varifold.firstVariation, halfLineVarifold,
    measurableEmbedding_bundle.integral_map]
  change (∫ t in Ioi a,
    Varifold.tangentialDivergence X (coordinateEquiv t) fullPlane) = 0
  simp_rw [tangentialDivergence_eq_deriv X.contDiff]
  exact (hgc.integral_Ioi_deriv_eq hg a).trans (by rw [hga, neg_zero])

theorem map_coordinate_weight (a : ℝ) :
    (halfLineVarifold a).weight.map coordinateEquiv.symm = volume.restrict (Ioi a) := by
  rw [weight_halfLineVarifold, Measure.map_map coordinateEquiv.symm.continuous.measurable
    coordinateEquiv.continuous.measurable]
  simp only [Function.comp_def, LinearIsometryEquiv.symm_apply_apply, Measure.map_id']

theorem map_volume_restrict_domain (a : ℝ) :
    (volume.restrict (domain a)).map coordinateEquiv.symm =
      volume.restrict ({a} : Set ℝ)ᶜ := by
  rw [domain, ← Measure.restrict_map coordinateEquiv.symm.continuous.measurable
    (measurableSet_singleton a).compl, coordinateEquiv.symm.measurePreserving.map_eq]

/-- Even at the level of weights, no single multiplicity can represent
the positive half-line on both components of the punctured domain. -/
theorem real_halfLine_ne_smul_puncturedVolume (c : ℝ≥0∞) :
    (volume.restrict (Ioi (0 : ℝ))) ≠ c • volume.restrict ({0} : Set ℝ)ᶜ := by
  intro h
  have hneg₁ : (volume.restrict (Ioi (0 : ℝ))) (Ioo (-2) (-1)) = 0 := by
    rw [Measure.restrict_apply measurableSet_Ioo]
    have he : Ioo (-2 : ℝ) (-1) ∩ Ioi 0 = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Ioo, mem_Ioi, mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, hx⟩, hx'⟩
      linarith
    rw [he, measure_empty]
  have hneg₂ : (volume.restrict ({0} : Set ℝ)ᶜ) (Ioo (-2) (-1)) = 1 := by
    rw [Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr (show Ioo (-2 : ℝ) (-1) ⊆ ({0} : Set ℝ)ᶜ from by
        intro x hx
        simp only [mem_compl_iff, mem_singleton_iff]
        linarith [hx.2])]
    norm_num
  have hc := congrArg (fun μ : Measure ℝ ↦ μ (Ioo (-2) (-1))) h
  rw [hneg₁, Measure.smul_apply, hneg₂, smul_eq_mul, mul_one] at hc
  have hpos := congrArg (fun μ : Measure ℝ ↦ μ (Ioo 0 1)) h
  rw [← hc, zero_smul] at hpos
  change (volume.restrict (Ioi (0 : ℝ))) (Ioo 0 1) = 0 at hpos
  rw [Measure.restrict_apply measurableSet_Ioo,
    inter_eq_left.mpr (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ hx ↦ hx.1)] at hpos
  norm_num at hpos

theorem weight_ne_smul_volume (c : ℝ≥0∞) :
    (halfLineVarifold 0).weight ≠ c • volume.restrict (domain 0) := by
  intro h
  have hm := congrArg (fun μ : Measure (Euclidean 1) ↦ μ.map coordinateEquiv.symm) h
  rw [map_coordinate_weight, Measure.map_smul _ coordinateEquiv.symm.continuous.measurable.aemeasurable,
    map_volume_restrict_domain] at hm
  exact real_halfLine_ne_smul_puncturedVolume c hm

/-- The literal Simon normalization does not repair the missing domain
hypothesis: the counterexample excludes every nonnegative extended-real
constant multiple of the correctly restricted Simon measure. -/
theorem weight_ne_smul_simonHausdorff (c : ℝ≥0∞) :
    (halfLineVarifold 0).weight ≠
      c • (Chapter01.simonHausdorffMeasureReal (1 : ℝ)).restrict (domain 0) := by
  have hnorm : (Chapter01.simonHausdorffMeasureReal (1 : ℝ) : Measure (Euclidean 1)) =
      Chapter02.simonAreaNormalization 1 • volume := by
    simpa using Chapter02.simonHausdorffMeasureReal_source_eq_smul_volume (E := Euclidean 1)
  rw [hnorm, Measure.restrict_smul, smul_smul]
  exact weight_ne_smul_volume _

/-- Every open subset of Euclidean space satisfies Simon's actual
full-dimensional submanifold definition, including relative properness. -/
theorem isSimonSubmanifold_of_isOpen {d : ℕ} {M : Set (Euclidean d)} (hM : IsOpen M) :
    Chapter02.IsSimonSubmanifold (E := Euclidean d) 2 M := by
  refine ⟨by norm_num, ?_⟩
  intro y hy
  refine ⟨M, M, id, hy, hM, hM, contDiff_id.contDiffOn, injOn_id M, ?_, ?_, ?_⟩
  · simp
  · intro K hK hKM
    simpa only [preimage_id, inter_eq_right.mpr hKM] using hK
  · intro x _
    rw [(hasFDerivAt_id x).fderiv]
    exact injective_id

/-- The hypotheses printed in Simon (8.4.1) hold, but even the necessary
weight-level constant-multiplicity conclusion fails. The carrier is the
connected smooth entire line; no extra domain-connectedness is inserted. -/
theorem counterexample_constancy_printed_hypotheses :
    ∃ (U M : Set (Euclidean 1)) (V : Varifold 1 1 U),
      IsConnected M ∧ Chapter02.IsSimonSubmanifold (E := Euclidean 1) 2 M ∧
      V.Stationary ∧ U ∩ V.weight.support ⊆ M ∧
      ¬ ∃ c : ℝ≥0∞,
        V.weight = c • (Chapter01.simonHausdorffMeasureReal (1 : ℝ)).restrict (M ∩ U) := by
  refine ⟨domain 0, univ, halfLineVarifold 0, isConnected_univ,
    isSimonSubmanifold_of_isOpen isOpen_univ, stationary_halfLineVarifold 0,
    subset_univ _, ?_⟩
  rintro ⟨c, hc⟩
  exact weight_ne_smul_simonHausdorff c (by simpa only [univ_inter] using hc)

theorem halfLineVarifold_measure_ne_zero (a : ℝ) : (halfLineVarifold a).measure ≠ 0 := by
  intro h
  have hu := congrArg (fun μ : Measure (Euclidean 1 × Grassmannian 1 1) ↦ μ univ) h
  change ((volume.restrict (Ioi a)).map bundle) univ = 0 at hu
  rw [measurableEmbedding_bundle.map_apply, preimage_univ, Measure.restrict_apply_univ,
    Real.volume_Ioi] at hu
  exact ENNReal.top_ne_zero hu

theorem weight_support_subset_halfLine (a : ℝ) :
    (halfLineVarifold a).weight.support ⊆ coordinateEquiv.symm ⁻¹' Ici a := by
  apply Measure.support_subset_of_isClosed (isClosed_Ici.preimage coordinateEquiv.symm.continuous)
  rw [weight_halfLineVarifold]
  apply coordinateEquiv.toHomeomorph.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change a ≤ coordinateEquiv.symm (coordinateEquiv t)
  simpa only [LinearIsometryEquiv.symm_apply_apply] using ht.le

/-- The positive open line is a connected smooth carrier whose omitted
endpoint need not be outside the ambient varifold domain. -/
def positiveCarrier : Set (Euclidean 1) := coordinateEquiv.symm ⁻¹' Ioi (0 : ℝ)

theorem positiveCarrier_eq_image : positiveCarrier = coordinateEquiv '' Ioi (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    exact ⟨coordinateEquiv.symm x, hx, coordinateEquiv.apply_symm_apply x⟩
  · rintro ⟨t, ht, rfl⟩
    simpa only [positiveCarrier, mem_preimage, LinearIsometryEquiv.symm_apply_apply] using ht

theorem isConnected_positiveCarrier : IsConnected positiveCarrier := by
  rw [positiveCarrier_eq_image]
  exact isConnected_Ioi.image _ coordinateEquiv.continuous.continuousOn

theorem zero_mem_closure_positiveCarrier : (0 : Euclidean 1) ∈ closure positiveCarrier := by
  have hcl := coordinateEquiv.toHomeomorph.image_closure (Ioi (0 : ℝ))
  change coordinateEquiv '' closure (Ioi (0 : ℝ)) = closure (coordinateEquiv '' Ioi 0) at hcl
  rw [positiveCarrier_eq_image, ← hcl, closure_Ioi]
  exact ⟨0, le_rfl, coordinateEquiv.map_zero⟩

/-- Remark (8.4.2)(1) also fails under the literal hypotheses of (8.4.1).
Take `U = ℝ \ {1}`, the carrier `(0,∞)`, and the nonzero stationary
varifold carried by `(1,∞)`: the carrier's omitted endpoint `0` lies in `U`. -/
theorem counterexample_relative_closedness_printed_hypotheses :
    ∃ (U M : Set (Euclidean 1)) (V : Varifold 1 1 U),
      IsConnected M ∧ Chapter02.IsSimonSubmanifold (E := Euclidean 1) 2 M ∧
      V.Stationary ∧ U ∩ V.weight.support ⊆ M ∧ V.measure ≠ 0 ∧
      ((closure M \ M) ∩ U).Nonempty := by
  refine ⟨domain 1, positiveCarrier, halfLineVarifold 1, isConnected_positiveCarrier,
    isSimonSubmanifold_of_isOpen (isOpen_Ioi.preimage coordinateEquiv.symm.continuous),
    stationary_halfLineVarifold 1, ?_, halfLineVarifold_measure_ne_zero 1, ?_⟩
  · intro x hx
    have hs := weight_support_subset_halfLine 1 hx.2
    change 1 ≤ coordinateEquiv.symm x at hs
    change 0 < coordinateEquiv.symm x
    linarith
  · refine ⟨0, ⟨zero_mem_closure_positiveCarrier, ?_⟩, ?_⟩
    · simp [positiveCarrier]
    · simp [domain]

end
end Poincare.SimonGMT.Chapter08.ConstancyDomainCounterexample
