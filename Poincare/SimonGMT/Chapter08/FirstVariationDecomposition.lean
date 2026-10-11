module

public import Poincare.SimonGMT.Chapter08.FirstVariationDensity

@[expose] public section

/-!
# Simon GMT, Chapter 8, (2.8)--(2.10): mean curvature and boundary decomposition

The source is printed pp. 209--210, PDF objects 215 and 217. For every
locally finite measure on the open domain, its singular part relative to
varifold weight is its restriction to the *pointwise symmetric-density*
infinity set. This uses reversed differentiation and a genuine infinite
quotient limit at singular-part-almost every point. It does not infer
anything about that set from weight-a.e. equality with an RN representative.

The resulting integral decomposition (2.8) is proved for arbitrary
integrable functions. Formula (2.10) follows for any measure and polar
field satisfying the previously defined (2.5)--(2.6) properties. Existence
of those objects from locally bounded first variation is still separate;
this module neither constructs nor presupposes that existence theorem.

The new `symmetricGeneralized*` definitions use the actual small-ball
density, unlike the older RN-based `generalizedBoundarySet` interface.
They are not identified pointwise with the older definitions. At points
where the quotient has no limit we retain the limsup convention; that
exceptional set is null for both numerator and weight, as proved below.
All ambient measures are zero extensions from the actual domain, so no
finiteness is required at its boundary.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08

/-- The analytic input to Simon (8.2.9): differentiation with the measures
reversed, followed by inversion, proves an actual infinite quotient limit
on the singular part. Positivity and finiteness of sufficiently small
numerator balls justify inversion, including zero denominator balls. -/
theorem ae_tendsto_measureRatio_top_singularPart
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [HasBesicovitchCovering E]
    (μ ν : Measure E) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] :
    ∀ᵐ x ∂μ.singularPart ν,
      Tendsto (fun r : ℝ ↦ μ (closedBall x r) / ν (closedBall x r))
        (𝓝[>] (0 : ℝ)) (𝓝 ∞) := by
  have hac := (Measure.singularPart_le μ ν).absolutelyContinuous
  filter_upwards [hac.ae_le (Besicovitch.ae_tendsto_rnDeriv ν μ),
    ν.rnDeriv_eq_zero_ae_singularPart μ,
    hac.ae_le (Besicovitch.vitaliFamily μ).ae_eventually_measure_pos]
      with x hx hzero hpos
  rw [hzero] at hx
  have hinv : Tendsto
      (fun r : ℝ ↦ (ν (closedBall x r) / μ (closedBall x r))⁻¹)
        (𝓝[>] (0 : ℝ)) (𝓝 ∞) := by
    simpa only [ENNReal.inv_zero] using tendsto_inv_iff.mpr hx
  apply hinv.congr'
  filter_upwards [(Besicovitch.tendsto_filterAt μ x).eventually hpos,
    (Besicovitch.tendsto_filterAt μ x).eventually
      ((Besicovitch.vitaliFamily μ).eventually_measure_lt_top x)] with r hr0 hrt
  exact ENNReal.inv_div (Or.inl hrt.ne) (Or.inl hr0.ne')

namespace Varifold
noncomputable section
variable {N n : ℕ} {U : Set (Euclidean N)}

/-- Simon (8.2.9), intrinsic-domain form: the actual small-ball quotient
converges to infinity at almost every point of the ambient singular part. -/
theorem ae_tendsto_symmetricFirstVariationDensity_top_singularPart
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ] :
    ∀ᵐ x ∂(μ.map Subtype.val).singularPart V.weight,
      Tendsto (fun r : ℝ ↦ (μ.map Subtype.val) (closedBall x r) /
        V.weight (closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 ∞) := by
  let : HasBesicovitchCovering U := hasBesicovitchCovering_subtype U
  have hemb := MeasurableEmbedding.subtype_coe V.isOpen_domain.measurableSet
  have hball (ν : Measure U) (x : U) (r : ℝ) :
      ν.map Subtype.val (closedBall (x : Euclidean N) r) = ν (closedBall x r) := by
    rw [Measure.map_apply measurable_subtype_coe measurableSet_closedBall]
    rfl
  have hlocal : ∀ᵐ (x : U) ∂μ.singularPart V.domainWeight,
      Tendsto (fun r : ℝ ↦ (μ.map Subtype.val) (closedBall (x : Euclidean N) r) /
        V.weight (closedBall (x : Euclidean N) r)) (𝓝[>] (0 : ℝ)) (𝓝 ∞) := by
    filter_upwards [ae_tendsto_measureRatio_top_singularPart μ V.domainWeight] with x hx
    simpa only [← V.map_domainWeight, hball] using hx
  have h : ∀ᵐ x ∂(μ.singularPart V.domainWeight).map Subtype.val,
      Tendsto (fun r : ℝ ↦ (μ.map Subtype.val) (closedBall x r) /
        V.weight (closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 ∞) := hemb.ae_map_iff.mpr hlocal
  rwa [← hemb.singularPart_map, V.map_domainWeight] at h

/-- Simon (8.2.9): the generalized boundary defined using the pointwise
symmetric small-ball density. This is not the RN representative's infinity set. -/
def symmetricGeneralizedBoundarySet (V : Varifold N n U)
    (μ : Measure (Euclidean N)) : Set (Euclidean N) :=
  U ∩ {x | V.symmetricFirstVariationDensity μ x = ∞}

/-- The weight-nullness assertion in Simon (8.2.9), for the actual
symmetric-density infinity set. -/
theorem weight_symmetricGeneralizedBoundarySet
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ] :
    V.weight (V.symmetricGeneralizedBoundarySet (μ.map Subtype.val)) = 0 :=
  measure_mono_null inter_subset_right (V.weight_symmetricFirstVariationDensity_top μ)

/-- The singular measure is carried by Simon's actual generalized boundary. -/
theorem singularPart_ae_mem_symmetricGeneralizedBoundarySet
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ] :
    ∀ᵐ x ∂(μ.map Subtype.val).singularPart V.weight,
      x ∈ V.symmetricGeneralizedBoundarySet (μ.map Subtype.val) := by
  have hU : ∀ᵐ x ∂μ.map (Subtype.val : U → Euclidean N), x ∈ U := by
    rw [(MeasurableEmbedding.subtype_coe V.isOpen_domain.measurableSet).ae_map_iff]
    exact Filter.Eventually.of_forall fun x ↦ x.property
  filter_upwards [V.ae_tendsto_symmetricFirstVariationDensity_top_singularPart μ,
    (Measure.singularPart_le _ _).absolutelyContinuous.ae_le hU] with x hx hxU
  exact ⟨hxU, hx.limsup_eq⟩

/-- Simon (8.2.9): the singular part is precisely restriction of the
numerator measure to the symmetric-density infinity set in the domain.
No measurability of that set is added as a hypothesis. -/
theorem singularPart_eq_restrict_symmetricGeneralizedBoundarySet
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ] :
    (μ.map Subtype.val).singularPart V.weight =
      (μ.map Subtype.val).restrict (V.symmetricGeneralizedBoundarySet (μ.map Subtype.val)) := by
  let : SigmaFinite (μ.map (Subtype.val : U → Euclidean N)) :=
    (MeasurableEmbedding.subtype_coe V.isOpen_domain.measurableSet).sigmaFinite_map
  exact Measure.singularPart_eq_restrict
    (V.singularPart_ae_mem_symmetricGeneralizedBoundarySet μ)
    (V.weight_symmetricGeneralizedBoundarySet μ)

/-- The symmetric quotient also has an actual limit numerator-almost
everywhere. Thus the limsup convention at nonconvergence points does not
affect either measure or the boundary restriction. -/
theorem ae_tendsto_symmetricFirstVariationDensity_numerator
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ] :
    ∀ᵐ x ∂μ.map Subtype.val,
      Tendsto (fun r : ℝ ↦ (μ.map Subtype.val) (closedBall x r) /
        V.weight (closedBall x r)) (𝓝[>] (0 : ℝ))
        (𝓝 (V.symmetricFirstVariationDensity (μ.map Subtype.val) x)) := by
  let : SigmaFinite (μ.map (Subtype.val : U → Euclidean N)) :=
    (MeasurableEmbedding.subtype_coe V.isOpen_domain.measurableSet).sigmaFinite_map
  rw [show ae (μ.map (Subtype.val : U → Euclidean N)) =
    ae ((μ.map Subtype.val).singularPart V.weight +
      V.weight.withDensity ((μ.map Subtype.val).rnDeriv V.weight)) from
        congrArg ae (Measure.haveLebesgueDecomposition_add _ _), ae_add_measure_iff]
  constructor
  · filter_upwards [V.ae_tendsto_symmetricFirstVariationDensity_top_singularPart μ] with x hx
    have hlim : V.symmetricFirstVariationDensity (μ.map Subtype.val) x = ∞ := hx.limsup_eq
    rwa [hlim]
  · exact (withDensity_absolutelyContinuous _ _).ae_le
      (V.ae_tendsto_symmetricFirstVariationDensity μ)

/-- The pointwise boundary set is measurable for the completed numerator
measure; no Borel measurability assumption on a density representative is needed. -/
theorem nullMeasurableSet_symmetricGeneralizedBoundarySet
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ] :
    NullMeasurableSet (V.symmetricGeneralizedBoundarySet (μ.map Subtype.val))
      (μ.map Subtype.val) := by
  let : SigmaFinite (μ.map (Subtype.val : U → Euclidean N)) :=
    (MeasurableEmbedding.subtype_coe V.isOpen_domain.measurableSet).sigmaFinite_map
  let hs := Measure.mutuallySingular_singularPart (μ.map Subtype.val) V.weight
  apply hs.measurableSet_nullSet.compl.nullMeasurableSet.congr
  change ∀ᵐ x ∂μ.map Subtype.val,
    (x ∈ hs.nullSetᶜ) = (x ∈ V.symmetricGeneralizedBoundarySet (μ.map Subtype.val))
  rw [show ae (μ.map (Subtype.val : U → Euclidean N)) =
    ae ((μ.map Subtype.val).singularPart V.weight +
      V.weight.withDensity ((μ.map Subtype.val).rnDeriv V.weight)) from
        congrArg ae (Measure.haveLebesgueDecomposition_add _ _), ae_add_measure_iff]
  constructor
  · have hT : ∀ᵐ x ∂(μ.map Subtype.val).singularPart V.weight, x ∈ hs.nullSetᶜ :=
      measure_eq_zero_iff_ae_notMem.mp hs.measure_nullSet
    filter_upwards [hT, V.singularPart_ae_mem_symmetricGeneralizedBoundarySet μ] with x hx hz
    exact propext (iff_of_true hx hz)
  · apply (withDensity_absolutelyContinuous _ _).ae_le
    have hT : ∀ᵐ x ∂V.weight, x ∉ hs.nullSetᶜ :=
      measure_eq_zero_iff_ae_notMem.mp hs.measure_compl_nullSet
    have hZ := measure_eq_zero_iff_ae_notMem.mp (V.weight_symmetricGeneralizedBoundarySet μ)
    filter_upwards [hT, hZ] with x hx hz
    exact propext (iff_of_false hx hz)

/-- Simon (8.2.9): the generalized boundary measure, restricted to the
actual symmetric-density infinity set. -/
def symmetricGeneralizedBoundaryMeasure (V : Varifold N n U)
    (μ : Measure (Euclidean N)) : Measure (Euclidean N) :=
  μ.restrict (V.symmetricGeneralizedBoundarySet μ)

/-- Simon (8.2.7)--(8.2.8): the generalized mean curvature, using the
symmetric density. Its real scalar is totalized to zero at infinity;
this changes only a weight-null set under the source hypotheses. -/
def symmetricGeneralizedMeanCurvature (V : Varifold N n U)
    (μ : Measure (Euclidean N)) (ν : Euclidean N → Euclidean N)
    (x : Euclidean N) : Euclidean N :=
  (V.symmetricFirstVariationDensity μ x).toReal • ν x

/-- The measure-level content underlying Simon (8.2.8)--(8.2.9), with
both the actual symmetric density and the actual generalized-boundary restriction. -/
theorem symmetricLebesgueDecomposition
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ] :
    μ.map Subtype.val =
      V.weight.withDensity (V.symmetricFirstVariationDensity (μ.map Subtype.val)) +
        V.symmetricGeneralizedBoundaryMeasure (μ.map Subtype.val) := by
  let : SigmaFinite (μ.map (Subtype.val : U → Euclidean N)) :=
    (MeasurableEmbedding.subtype_coe V.isOpen_domain.measurableSet).sigmaFinite_map
  rw [withDensity_congr_ae (V.symmetricFirstVariationDensity_ae_eq_rnDeriv μ),
    symmetricGeneralizedBoundaryMeasure,
    ← V.singularPart_eq_restrict_symmetricGeneralizedBoundarySet μ]
  exact (Measure.rnDeriv_add_singularPart _ _).symm

/-- Both terms of the decomposition are genuinely integrable whenever
the original function is integrable; no separate summand-integrability
assumptions are required in the source first-variation formula. -/
theorem integrable_symmetricDensity_smul_and_boundary
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ]
    {f : Euclidean N → F} (hf : Integrable f (μ.map Subtype.val)) :
    Integrable (fun x ↦ (V.symmetricFirstVariationDensity (μ.map Subtype.val) x).toReal • f x)
        V.weight ∧
      Integrable f (V.symmetricGeneralizedBoundaryMeasure (μ.map Subtype.val)) := by
  have hs := hf
  rw [V.symmetricLebesgueDecomposition μ, integrable_add_measure] at hs
  exact ⟨(integrable_withDensity_iff_integrable_smul₀'
    (V.aemeasurable_symmetricFirstVariationDensity μ)
    ((V.symmetricFirstVariationDensity_ne_top_ae μ).mono fun _ hx ↦ hx.lt_top)).mp hs.1,
    hs.2⟩

/-- Simon (8.2.8), generalized to arbitrary integrable Banach-valued
functions and arbitrary domain-local Radon numerator measures. -/
theorem integral_eq_symmetricDensity_add_boundary
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ]
    {f : Euclidean N → F} (hf : Integrable f (μ.map Subtype.val)) :
    ∫ x, f x ∂μ.map Subtype.val =
      (∫ x, (V.symmetricFirstVariationDensity (μ.map Subtype.val) x).toReal • f x ∂V.weight) +
        ∫ x, f x ∂V.symmetricGeneralizedBoundaryMeasure (μ.map Subtype.val) := by
  have hs := hf
  rw [V.symmetricLebesgueDecomposition μ, integrable_add_measure] at hs
  calc
    _ = ∫ x, f x ∂(V.weight.withDensity
        (V.symmetricFirstVariationDensity (μ.map Subtype.val)) +
          V.symmetricGeneralizedBoundaryMeasure (μ.map Subtype.val)) := by
      rw [← V.symmetricLebesgueDecomposition μ]
    _ = _ := by
      rw [integral_add_measure hs.1 hs.2,
        integral_withDensity_eq_integral_toReal_smul₀
          (V.aemeasurable_symmetricFirstVariationDensity μ)
          ((V.symmetricFirstVariationDensity_ne_top_ae μ).mono fun _ hx ↦ hx.lt_top)]

/-- Simon (8.2.9) for any measure satisfying (8.2.5). This is the actual
symmetric boundary measure, not the older RN-infinity-set helper. -/
theorem IsFirstVariationMeasure.symmetricBoundaryMeasure_eq_singularPart
    {V : Varifold N n U} {μ : Measure (Euclidean N)}
    (hμ : V.IsFirstVariationMeasure μ) :
    V.symmetricGeneralizedBoundaryMeasure μ = μ.singularPart V.weight := by
  let : IsLocallyFiniteMeasure (μ.comap (Subtype.val : U → Euclidean N)) := hμ.1
  have h := V.singularPart_eq_restrict_symmetricGeneralizedBoundarySet (μ.comap Subtype.val)
  rw [hμ.map_comap_eq] at h
  exact h.symm

/-- The source assertion in (8.2.9): the actual generalized boundary has
zero varifold weight. -/
theorem IsFirstVariationMeasure.symmetricBoundarySet_weight_zero
    {V : Varifold N n U} {μ : Measure (Euclidean N)}
    (hμ : V.IsFirstVariationMeasure μ) :
    V.weight (V.symmetricGeneralizedBoundarySet μ) = 0 := by
  let : IsLocallyFiniteMeasure (μ.comap (Subtype.val : U → Euclidean N)) := hμ.1
  have h := V.weight_symmetricGeneralizedBoundarySet (μ.comap Subtype.val)
  rwa [hμ.map_comap_eq] at h

/-- The generalized boundary measure is intrinsically regular on the
open domain; local finiteness is inherited from the numerator there. -/
theorem IsFirstVariationMeasure.symmetricBoundaryMeasure_regular
    {V : Varifold N n U} {μ : Measure (Euclidean N)}
    (hμ : V.IsFirstVariationMeasure μ) :
    Measure.Regular ((V.symmetricGeneralizedBoundaryMeasure μ).comap
      (Subtype.val : U → Euclidean N)) := by
  let : IsLocallyFiniteMeasure (μ.comap (Subtype.val : U → Euclidean N)) := hμ.1
  let : LocallyCompactSpace U := V.isOpen_domain.locallyCompactSpace
  have hemb := MeasurableEmbedding.subtype_coe V.isOpen_domain.measurableSet
  have hle : (V.symmetricGeneralizedBoundaryMeasure μ).comap
      (Subtype.val : U → Euclidean N) ≤ μ.comap Subtype.val := by
    intro s
    rw [hemb.comap_apply, hemb.comap_apply]
    exact Measure.restrict_le_self _
  let : IsLocallyFiniteMeasure ((V.symmetricGeneralizedBoundaryMeasure μ).comap
      (Subtype.val : U → Euclidean N)) := Measure.isLocallyFiniteMeasure_of_le hle
  infer_instance

/-- The mean-curvature and boundary integrands in (8.2.10) are integrable
under (8.2.5)--(8.2.6), without additional hypotheses. -/
theorem IsFirstVariationMeasure.integrable_meanCurvature_inner_and_boundary
    {V : Varifold N n U} {μ : Measure (Euclidean N)}
    (hμ : V.IsFirstVariationMeasure μ) {ν : Euclidean N → Euclidean N}
    (hν : V.IsFirstVariationPolarRepresentation μ ν) (X : TestVectorField (N := N) U) :
    Integrable (fun x ↦ inner ℝ (V.symmetricGeneralizedMeanCurvature μ ν x) (X x)) V.weight ∧
      Integrable (fun x ↦ inner ℝ (ν x) (X x)) (V.symmetricGeneralizedBoundaryMeasure μ) := by
  let : IsLocallyFiniteMeasure (μ.comap (Subtype.val : U → Euclidean N)) := hμ.1
  have h := V.integrable_symmetricDensity_smul_and_boundary (μ.comap Subtype.val)
    (f := fun x ↦ inner ℝ (ν x) (X x))
  rw [hμ.map_comap_eq] at h
  simpa only [symmetricGeneralizedMeanCurvature, real_inner_smul_left, smul_eq_mul] using
    h (hν.2.2 X).1

/-- Simon (8.2.8) with the actual symmetric-density mean curvature and
boundary restriction. For source test fields, integrability is supplied
by the previously defined polar representation. -/
theorem IsFirstVariationMeasure.integral_eq_meanCurvature_add_boundary
    {V : Varifold N n U} {μ : Measure (Euclidean N)}
    (hμ : V.IsFirstVariationMeasure μ) {ν X : Euclidean N → Euclidean N}
    (hint : Integrable (fun x ↦ inner ℝ (ν x) (X x)) μ) :
    (∫ x, inner ℝ (ν x) (X x) ∂μ) =
      (∫ x, inner ℝ (V.symmetricGeneralizedMeanCurvature μ ν x) (X x) ∂V.weight) +
        ∫ x, inner ℝ (ν x) (X x) ∂V.symmetricGeneralizedBoundaryMeasure μ := by
  let : IsLocallyFiniteMeasure (μ.comap (Subtype.val : U → Euclidean N)) := hμ.1
  have h := V.integral_eq_symmetricDensity_add_boundary (μ.comap Subtype.val)
    (f := fun x ↦ inner ℝ (ν x) (X x))
  rw [hμ.map_comap_eq] at h
  simpa only [symmetricGeneralizedMeanCurvature, real_inner_smul_left, smul_eq_mul] using h hint

/-- Simon (8.2.10), with the source minus signs and boundary integration
over the actual symmetric-density infinity set. The only measure/field
premises are the preceding (8.2.5)--(8.2.6) properties; their existence
from locally bounded first variation remains a separate obligation. -/
theorem IsFirstVariationMeasure.firstVariation_eq_meanCurvature_add_boundary
    {V : Varifold N n U} {μ : Measure (Euclidean N)}
    (hμ : V.IsFirstVariationMeasure μ) {ν : Euclidean N → Euclidean N}
    (hν : V.IsFirstVariationPolarRepresentation μ ν) (X : TestVectorField (N := N) U) :
    V.firstVariation X =
      -(∫ x, inner ℝ (V.symmetricGeneralizedMeanCurvature μ ν x) (X x) ∂V.weight) -
        ∫ x in V.symmetricGeneralizedBoundarySet μ, inner ℝ (ν x) (X x)
          ∂V.symmetricGeneralizedBoundaryMeasure μ := by
  rw [(hν.2.2 X).2,
    hμ.integral_eq_meanCurvature_add_boundary (hν.2.2 X).1,
    symmetricGeneralizedBoundaryMeasure, Measure.restrict_restrict_of_subset (subset_refl _)]
  ring

end
end Varifold
end Poincare.SimonGMT.Chapter08
