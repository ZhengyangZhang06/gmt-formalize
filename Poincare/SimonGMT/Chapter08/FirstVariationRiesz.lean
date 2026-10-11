module

public import Poincare.SimonGMT.Chapter08.VectorRiesz
public import Poincare.SimonGMT.Chapter08.PolarNorm
public import Poincare.SimonGMT.Chapter08.FirstVariationDecomposition

@[expose] public section

/-!
# Construction of the first-variation measure and polar field

The locally bounded first-variation functional is extended to continuous
compactly supported fields, represented by the componentwise signed
Riesz construction, and normalized using actual Radon--Nikodym
derivatives. The resulting Radon measure has precisely the unit-test
supremum in Simon (8.2.5), and the measurable unit field has the minus-sign
representation in (8.2.6). No representation or measure-existence
hypothesis is added to local boundedness.

Source: `Simon-gmt new.pdf`, printed p. 209, PDF object 215.
-/

open Set Filter MeasureTheory Function
open scoped Topology ENNReal CompactlySupported BoundedContinuousFunction

namespace Poincare.SimonGMT.Chapter08.Varifold
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable {N n : ℕ} {U : Set (Euclidean N)}

theorem domainContinuousFirstVariation_locallyBounded (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) :
    VectorCcLocallyBounded (V.domainContinuousFirstVariation hV) :=
  V.domainContinuousFirstVariation_local_bound hV

/-- The constructed Radon measure on the actual open domain. -/
def domainFirstVariationMeasure (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) : Measure U := by
  letI : LocallyCompactSpace U := V.isOpen_domain.locallyCompactSpace
  exact VectorRiesz.variationMeasure (V.domainContinuousFirstVariation_locallyBounded hV)

instance (V : Varifold N n U) (hV : V.HasLocallyBoundedFirstVariation) :
    IsLocallyFiniteMeasure (V.domainFirstVariationMeasure hV) := by
  let : LocallyCompactSpace U := V.isOpen_domain.locallyCompactSpace
  unfold domainFirstVariationMeasure
  infer_instance

instance (V : Varifold N n U) (hV : V.HasLocallyBoundedFirstVariation) :
    (V.domainFirstVariationMeasure hV).Regular := by
  let : LocallyCompactSpace U := V.isOpen_domain.locallyCompactSpace
  infer_instance

/-- Ambient zero extension of the constructed variation measure. -/
def firstVariationRieszMeasure (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) : Measure (Euclidean N) :=
  (V.domainFirstVariationMeasure hV).map Subtype.val

/-- The measurable polar field, extended by zero outside the domain. -/
def firstVariationPolarField (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) : Euclidean N → Euclidean N := by
  letI : LocallyCompactSpace U := V.isOpen_domain.locallyCompactSpace
  exact Subtype.val.extend
    (VectorRiesz.polarField (V.domainContinuousFirstVariation_locallyBounded hV)) 0

theorem measurable_firstVariationPolarField (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) : Measurable (V.firstVariationPolarField hV) := by
  let : LocallyCompactSpace U := V.isOpen_domain.locallyCompactSpace
  exact (MeasurableEmbedding.subtype_coe V.isOpen_domain.measurableSet).measurable_extend
    (VectorRiesz.measurable_polarField (V.domainContinuousFirstVariation_locallyBounded hV))
    measurable_const

theorem firstVariationPolarField_apply (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) (x : U) :
    V.firstVariationPolarField hV x =
      letI : LocallyCompactSpace U := V.isOpen_domain.locallyCompactSpace
      VectorRiesz.polarField (V.domainContinuousFirstVariation_locallyBounded hV) x := by
  exact Subtype.val_injective.extend_apply _ _ x

theorem firstVariationRieszMeasure_comap (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) :
    (V.firstVariationRieszMeasure hV).comap (Subtype.val : U → Euclidean N) =
      V.domainFirstVariationMeasure hV :=
  (MeasurableEmbedding.subtype_coe V.isOpen_domain.measurableSet).comap_map _

theorem firstVariationRieszMeasure_compl (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) : V.firstVariationRieszMeasure hV Uᶜ = 0 := by
  rw [firstVariationRieszMeasure,
    Measure.map_apply measurable_subtype_coe V.isOpen_domain.measurableSet.compl]
  simp

theorem ae_firstVariationPolarField_norm_one (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) :
    ∀ᵐ x ∂V.firstVariationRieszMeasure hV, ‖V.firstVariationPolarField hV x‖ = 1 := by
  let : LocallyCompactSpace U := V.isOpen_domain.locallyCompactSpace
  rw [firstVariationRieszMeasure,
    (MeasurableEmbedding.subtype_coe V.isOpen_domain.measurableSet).ae_map_iff]
  simp_rw [firstVariationPolarField_apply]
  exact VectorRiesz.ae_polarField_norm_one
    (V.domainContinuousFirstVariation_locallyBounded hV)

/-- The constructed representation holds already for the full continuous
compactly supported test space. -/
theorem firstVariationRiesz_continuous (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) (f : continuousFields U) :
    Integrable (fun x ↦ inner ℝ (V.firstVariationPolarField hV x) (f.1 x))
      (V.firstVariationRieszMeasure hV) ∧
    V.continuousFirstVariation hV f =
      -(∫ x, inner ℝ (V.firstVariationPolarField hV x) (f.1 x)
        ∂V.firstVariationRieszMeasure hV) := by
  let : LocallyCompactSpace U := V.isOpen_domain.locallyCompactSpace
  have hemb := MeasurableEmbedding.subtype_coe V.isOpen_domain.measurableSet
  constructor
  · rw [firstVariationRieszMeasure, hemb.integrable_map_iff]
    change Integrable (fun x : U ↦ inner ℝ (V.firstVariationPolarField hV x) (f.1 x))
      (V.domainFirstVariationMeasure hV)
    simp_rw [firstVariationPolarField_apply]
    exact VectorRiesz.integrable_inner_polarField
      (V.domainContinuousFirstVariation_locallyBounded hV) (restrictContinuousField f)
  · rw [firstVariationRieszMeasure, hemb.integral_map]
    simp_rw [firstVariationPolarField_apply]
    have hi := VectorRiesz.neg_integral_inner_polarField
      (V.domainContinuousFirstVariation_locallyBounded hV) (restrictContinuousField f)
    have hf : V.domainContinuousFirstVariation hV (restrictContinuousField f) =
        V.continuousFirstVariation hV f := by
      change V.continuousFirstVariation hV (domainContinuousFieldEquiv V.isOpen_domain
        ((domainContinuousFieldEquiv V.isOpen_domain).symm f)) = _
      rw [LinearEquiv.apply_symm_apply]
    exact (hi.trans hf).symm

/-- Simon (8.2.6) follows from locally bounded first variation alone. -/
theorem isFirstVariationPolarRepresentation_riesz (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) :
    V.IsFirstVariationPolarRepresentation (V.firstVariationRieszMeasure hV)
      (V.firstVariationPolarField hV) := by
  refine ⟨(V.measurable_firstVariationPolarField hV).aestronglyMeasurable,
    V.ae_firstVariationPolarField_norm_one hV, fun X ↦ ?_⟩
  have h := V.firstVariationRiesz_continuous hV X.toContinuousField
  rwa [V.continuousFirstVariation_eq_test hV] at h

theorem firstVariationRieszMeasure_ne_top_of_relativelyCompact
    (V : Varifold N n U) (hV : V.HasLocallyBoundedFirstVariation)
    {W : Set (Euclidean N)} (hWU : IsCompact (closure W) ∧ closure W ⊆ U) :
    V.firstVariationRieszMeasure hV W ≠ ∞ := by
  have hfinite : V.firstVariationRieszMeasure hV (closure W) ≠ ∞ := by
    rw [firstVariationRieszMeasure,
      Measure.map_apply measurable_subtype_coe hWU.1.measurableSet]
    apply IsCompact.measure_ne_top
    apply Topology.IsInducing.subtypeVal.isCompact_preimage' hWU.1
    simpa using hWU.2
  exact ne_top_of_le_ne_top hfinite (measure_mono subset_closure)

/-- The reverse estimate in (8.2.5): compactly supported continuous
approximations of the unit polar field recover all of the local mass. -/
theorem firstVariationRieszMeasure_le_norm (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) (W : Set (Euclidean N)) (hW : IsOpen W)
    (hWU : IsCompact (closure W) ∧ closure W ⊆ U) :
    V.firstVariationRieszMeasure hV W ≤ V.firstVariationNormOn W := by
  let μ := V.firstVariationRieszMeasure hV
  let η : Measure W := μ.comap Subtype.val
  let : LocallyCompactSpace W := hW.locallyCompactSpace
  have hη : η univ = μ W := by
    rw [show η = μ.comap (Subtype.val : W → Euclidean N) from rfl,
      comap_subtype_coe_apply hW.measurableSet]
    simp
  have hμW : μ W ≠ ∞ := V.firstVariationRieszMeasure_ne_top_of_relativelyCompact hV hWU
  let : IsFiniteMeasure η := ⟨by rw [hη]; exact lt_top_iff_ne_top.mpr hμW⟩
  let : η.Regular := inferInstance
  have hunit : ∀ᵐ x : W ∂η, ‖V.firstVariationPolarField hV x‖ = 1 :=
    (ae_restrict_iff_subtype hW.measurableSet).mp
      (ae_restrict_of_ae (V.ae_firstVariationPolarField_norm_one hV))
  have hbound := measureReal_univ_le_of_unit_polar_tests η
    (fun x : W ↦ V.firstVariationPolarField hV x)
    ((V.measurable_firstVariationPolarField hV).comp measurable_subtype_coe).aestronglyMeasurable
    hunit (V.firstVariationNormOn W).toReal
  have hsmall : W ⊆ U := subset_closure.trans hWU.2
  have hfin := hV W hW hWU
  have hmass : η.real univ ≤ (V.firstVariationNormOn W).toReal := by
    apply hbound
    intro f hf
    let fW : continuousFields W := zeroExtendContinuousField hW f
    let fU : continuousFields U := continuousFieldInclusion hsmall fW
    have heq : (∫ x : W, inner ℝ (V.firstVariationPolarField hV x) (f x) ∂η) =
        ∫ x, inner ℝ (V.firstVariationPolarField hV x) (fU.1 x) ∂μ := by
      calc
        _ = ∫ x : W, inner ℝ (V.firstVariationPolarField hV x) (fU.1 x) ∂η := by
          apply integral_congr_ae
          filter_upwards with x
          congr 1
          exact (zeroExtendContinuousField_apply hW f x).symm
        _ = ∫ x in W, inner ℝ (V.firstVariationPolarField hV x) (fU.1 x) ∂μ :=
          integral_subtype_comap (μ := μ) hW.measurableSet
            (fun x ↦ inner ℝ (V.firstVariationPolarField hV x) (fU.1 x))
        _ = ∫ x, inner ℝ (V.firstVariationPolarField hV x) (fU.1 x) ∂μ := by
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro x hx
          change inner ℝ (V.firstVariationPolarField hV x)
            ((zeroExtendContinuousField hW f).1 x) = 0
          rw [zeroExtendContinuousField_apply_of_notMem hW f hx, inner_zero_right]
    rw [heq, ← abs_neg]
    rw [← (V.firstVariationRiesz_continuous hV fU).2]
    have hb := V.continuousFirstVariation_norm_bound hV hsmall hfin fU fW.2.2
    have hnorm : ‖fU‖ ≤ 1 := by
      change ‖zeroExtendContinuousField hW f‖ ≤ 1
      rw [zeroExtendContinuousField_norm]
      exact BoundedContinuousFunction.norm_le zero_le_one |>.mpr hf
    exact hb.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hnorm (ENNReal.toReal_nonneg (a := V.firstVariationNormOn W)))
  change (η univ).toReal ≤ (V.firstVariationNormOn W).toReal at hmass
  rw [hη] at hmass
  calc
    μ W = ENNReal.ofReal (μ W).toReal := (ENNReal.ofReal_toReal hμW).symm
    _ ≤ ENNReal.ofReal (V.firstVariationNormOn W).toReal := ENNReal.ofReal_le_ofReal hmass
    _ = V.firstVariationNormOn W := ENNReal.ofReal_toReal hfin

/-- Simon (8.2.5), with the exact original `C¹` unit-test supremum. -/
theorem firstVariationRieszMeasure_eq_norm (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) (W : Set (Euclidean N)) (hW : IsOpen W)
    (hWU : IsCompact (closure W) ∧ closure W ⊆ U) :
    V.firstVariationRieszMeasure hV W = V.firstVariationNormOn W :=
  le_antisymm (V.firstVariationRieszMeasure_le_norm hV W hW hWU)
    (V.firstVariationNormOn_le_of_polarRepresentation
      (V.isFirstVariationPolarRepresentation_riesz hV) W)

theorem isFirstVariationMeasure_riesz (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) :
    V.IsFirstVariationMeasure (V.firstVariationRieszMeasure hV) := by
  refine ⟨?_, V.firstVariationRieszMeasure_compl hV,
    V.firstVariationRieszMeasure_eq_norm hV⟩
  rw [V.firstVariationRieszMeasure_comap hV]
  infer_instance

/-- Full existence assertion in (8.2.5)--(8.2.6), constructed from the
printed locally bounded first-variation hypothesis. -/
theorem exists_firstVariationMeasure_polar (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) :
    ∃ (μ : Measure (Euclidean N)) (ν : Euclidean N → Euclidean N),
      V.IsFirstVariationMeasure μ ∧ V.IsFirstVariationPolarRepresentation μ ν :=
  ⟨V.firstVariationRieszMeasure hV, V.firstVariationPolarField hV,
    V.isFirstVariationMeasure_riesz hV, V.isFirstVariationPolarRepresentation_riesz hV⟩

/-- The equivalence stated immediately before (8.2.5). -/
theorem hasLocallyBoundedFirstVariation_iff_exists_measure_polar (V : Varifold N n U) :
    V.HasLocallyBoundedFirstVariation ↔
      ∃ (μ : Measure (Euclidean N)) (ν : Euclidean N → Euclidean N),
        V.IsFirstVariationMeasure μ ∧ V.IsFirstVariationPolarRepresentation μ ν := by
  constructor
  · exact V.exists_firstVariationMeasure_polar
  · rintro ⟨μ, ν, hμ, _⟩
    exact hμ.hasLocallyBoundedFirstVariation

/-- Simon (8.2.7), for the measure constructed from local boundedness. -/
theorem firstVariationRiesz_symmetricDensity_spec (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) :
    AEMeasurable (V.symmetricFirstVariationDensity (V.firstVariationRieszMeasure hV)) V.weight ∧
      ∀ᵐ x ∂V.weight,
        Tendsto (fun r : ℝ ↦ V.firstVariationRieszMeasure hV (Metric.closedBall x r) /
          V.weight (Metric.closedBall x r)) (𝓝[>] (0 : ℝ))
          (𝓝 (V.symmetricFirstVariationDensity (V.firstVariationRieszMeasure hV) x)) ∧
        V.symmetricFirstVariationDensity (V.firstVariationRieszMeasure hV) x ≠ ∞ :=
  (V.isFirstVariationMeasure_riesz hV).symmetricDensity_spec

/-- Simon (8.2.8), with no measure- or field-existence premise. -/
theorem firstVariationRiesz_integral_eq_meanCurvature_add_boundary (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) (X : TestVectorField (N := N) U) :
    (∫ x, inner ℝ (V.firstVariationPolarField hV x) (X x) ∂V.firstVariationRieszMeasure hV) =
      (∫ x, inner ℝ (V.symmetricGeneralizedMeanCurvature
        (V.firstVariationRieszMeasure hV) (V.firstVariationPolarField hV) x) (X x) ∂V.weight) +
        ∫ x, inner ℝ (V.firstVariationPolarField hV x) (X x)
          ∂V.symmetricGeneralizedBoundaryMeasure (V.firstVariationRieszMeasure hV) :=
  (V.isFirstVariationMeasure_riesz hV).integral_eq_meanCurvature_add_boundary
    ((V.isFirstVariationPolarRepresentation_riesz hV).2.2 X).1

/-- Simon (8.2.9): the constructed boundary is the actual singular part
on the pointwise symmetric-density infinity set, and that set has zero weight. -/
theorem firstVariationRiesz_boundary_spec (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) :
    V.symmetricGeneralizedBoundaryMeasure (V.firstVariationRieszMeasure hV) =
      (V.firstVariationRieszMeasure hV).singularPart V.weight ∧
    V.weight (V.symmetricGeneralizedBoundarySet (V.firstVariationRieszMeasure hV)) = 0 ∧
    Measure.Regular ((V.symmetricGeneralizedBoundaryMeasure
      (V.firstVariationRieszMeasure hV)).comap (Subtype.val : U → Euclidean N)) :=
  ⟨(V.isFirstVariationMeasure_riesz hV).symmetricBoundaryMeasure_eq_singularPart,
    (V.isFirstVariationMeasure_riesz hV).symmetricBoundarySet_weight_zero,
    (V.isFirstVariationMeasure_riesz hV).symmetricBoundaryMeasure_regular⟩

/-- Both terms of (8.2.10) are integrable from the printed hypothesis. -/
theorem firstVariationRiesz_integrable_meanCurvature_and_boundary (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) (X : TestVectorField (N := N) U) :
    Integrable (fun x ↦ inner ℝ (V.symmetricGeneralizedMeanCurvature
      (V.firstVariationRieszMeasure hV) (V.firstVariationPolarField hV) x) (X x)) V.weight ∧
    Integrable (fun x ↦ inner ℝ (V.firstVariationPolarField hV x) (X x))
      (V.symmetricGeneralizedBoundaryMeasure (V.firstVariationRieszMeasure hV)) :=
  (V.isFirstVariationMeasure_riesz hV).integrable_meanCurvature_inner_and_boundary
    (V.isFirstVariationPolarRepresentation_riesz hV) X

/-- Simon (8.2.10) unconditionally from locally bounded first variation:
the exact source signs and the actual symmetric-density boundary set. -/
theorem firstVariation_eq_meanCurvature_add_boundary_of_locallyBounded
    (V : Varifold N n U) (hV : V.HasLocallyBoundedFirstVariation)
    (X : TestVectorField (N := N) U) :
    V.firstVariation X =
      -(∫ x, inner ℝ (V.symmetricGeneralizedMeanCurvature
        (V.firstVariationRieszMeasure hV) (V.firstVariationPolarField hV) x) (X x) ∂V.weight) -
        ∫ x in V.symmetricGeneralizedBoundarySet (V.firstVariationRieszMeasure hV),
          inner ℝ (V.firstVariationPolarField hV x) (X x)
          ∂V.symmetricGeneralizedBoundaryMeasure (V.firstVariationRieszMeasure hV) :=
  (V.isFirstVariationMeasure_riesz hV).firstVariation_eq_meanCurvature_add_boundary
    (V.isFirstVariationPolarRepresentation_riesz hV) X

end
end Poincare.SimonGMT.Chapter08.Varifold
