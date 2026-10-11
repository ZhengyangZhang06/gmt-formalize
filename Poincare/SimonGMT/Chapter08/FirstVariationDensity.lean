module

public import Poincare.SimonGMT.Chapter08.DeformationIntegral
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section

/-!
# Simon GMT, Chapter 8, (2.7): the symmetric small-ball density

The closed-ball quotient of any domain-local Radon measure by varifold
weight has a finite limit at weight-almost every point. The limit agrees
with the RN derivative of the zero extensions, even when these extensions
are not locally finite at the boundary of the open domain.

This is the analytic differentiation assertion used in (2.7). Existence
of the first-variation total-variation measure and polar field in
(2.5)--(2.6) is a separate obligation.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08

/-- Satellite configurations in a metric subspace are configurations in the
ambient space. In particular, Euclidean open domains inherit the full
Besicovitch covering property without any doubling hypothesis. -/
theorem hasBesicovitchCovering_subtype {E : Type*} [MetricSpace E]
    [HasBesicovitchCovering E] (U : Set E) : HasBesicovitchCovering U := by
  obtain ⟨k, τ, hτ, hcfg⟩ := HasBesicovitchCovering.no_satelliteConfig (α := E)
  refine ⟨k, τ, hτ, ⟨fun a ↦ ?_⟩⟩
  let b : Besicovitch.SatelliteConfig E k τ :=
    { c := fun i ↦ (a.c i).1
      r := a.r
      rpos := a.rpos
      h := a.h
      hlast := a.hlast
      inter := a.inter }
  exact hcfg.false b

namespace Varifold
noncomputable section
variable {N n : ℕ} {U : Set (Euclidean N)}

/-- The pointwise symmetric upper density of a measure relative to varifold
weight. At almost every point for the weight it is the genuine limit in
Simon (8.2.7), as proved below. This is not merely a chosen RN representative. -/
def symmetricFirstVariationDensity (V : Varifold N n U)
    (μ : Measure (Euclidean N)) (x : Euclidean N) : ℝ≥0∞ :=
  limsup (fun r : ℝ ↦ μ (closedBall x r) / V.weight (closedBall x r)) (𝓝[>] (0 : ℝ))

/-- Simon (8.2.7), in the stronger form identifying the limit with the RN
derivative, for every Radon measure on the open domain. The numerator is
zero-extended from `U`; no local finiteness at its boundary is imposed.

Applying this to the total-variation measure requires its existence theorem
from (8.2.5), which is not assumed or proved by this declaration. -/
theorem ae_tendsto_firstVariationDensity_of_domainMeasure
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ] :
    ∀ᵐ x ∂V.weight,
      Tendsto (fun r : ℝ ↦ (μ.map Subtype.val) (closedBall x r) /
        V.weight (closedBall x r)) (𝓝[>] (0 : ℝ))
        (𝓝 ((μ.map Subtype.val).rnDeriv V.weight x)) := by
  let : HasBesicovitchCovering U := hasBesicovitchCovering_subtype U
  let : LocallyCompactSpace U := V.isOpen_domain.locallyCompactSpace
  have hemb := MeasurableEmbedding.subtype_coe V.isOpen_domain.measurableSet
  have hRN := hemb.rnDeriv_map μ V.domainWeight
  rw [V.map_domainWeight] at hRN
  have hball (ν : Measure U) (x : U) (r : ℝ) :
      ν.map Subtype.val (closedBall (x : Euclidean N) r) = ν (closedBall x r) := by
    rw [Measure.map_apply measurable_subtype_coe measurableSet_closedBall]
    rfl
  have hlocal : ∀ᵐ (x : U) ∂V.domainWeight,
      Tendsto (fun r : ℝ ↦ (μ.map Subtype.val) (closedBall (x : Euclidean N) r) /
        V.weight (closedBall (x : Euclidean N) r)) (𝓝[>] (0 : ℝ))
        (𝓝 ((μ.map Subtype.val).rnDeriv V.weight x)) := by
    filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ V.domainWeight, hRN] with x hx hRNx
    rw [hRNx]
    simpa only [← V.map_domainWeight, hball] using hx
  have h : ∀ᵐ x ∂V.domainWeight.map Subtype.val,
      Tendsto (fun r : ℝ ↦ (μ.map Subtype.val) (closedBall x r) /
        V.weight (closedBall x r)) (𝓝[>] (0 : ℝ))
        (𝓝 ((μ.map Subtype.val).rnDeriv V.weight x)) := hemb.ae_map_iff.mpr hlocal
  rwa [V.map_domainWeight] at h

theorem symmetricFirstVariationDensity_ae_eq_rnDeriv
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ] :
    V.symmetricFirstVariationDensity (μ.map Subtype.val) =ᵐ[V.weight]
      (μ.map Subtype.val).rnDeriv V.weight := by
  filter_upwards [V.ae_tendsto_firstVariationDensity_of_domainMeasure μ] with x hx
  exact hx.limsup_eq

theorem ae_tendsto_symmetricFirstVariationDensity
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ] :
    ∀ᵐ x ∂V.weight,
      Tendsto (fun r : ℝ ↦ (μ.map Subtype.val) (closedBall x r) /
        V.weight (closedBall x r)) (𝓝[>] (0 : ℝ))
        (𝓝 (V.symmetricFirstVariationDensity (μ.map Subtype.val) x)) := by
  filter_upwards [V.ae_tendsto_firstVariationDensity_of_domainMeasure μ,
    V.symmetricFirstVariationDensity_ae_eq_rnDeriv μ] with x hx he
  rwa [he]

theorem symmetricFirstVariationDensity_ne_top_ae
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ] :
    ∀ᵐ x ∂V.weight, V.symmetricFirstVariationDensity (μ.map Subtype.val) x ≠ ∞ := by
  let : SigmaFinite (μ.map (Subtype.val : U → Euclidean N)) :=
    (MeasurableEmbedding.subtype_coe V.isOpen_domain.measurableSet).sigmaFinite_map
  filter_upwards [V.symmetricFirstVariationDensity_ae_eq_rnDeriv μ,
    Measure.rnDeriv_ne_top (μ.map Subtype.val) V.weight] with x hx hfin
  rwa [hx]

theorem aemeasurable_symmetricFirstVariationDensity
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ] :
    AEMeasurable (V.symmetricFirstVariationDensity (μ.map Subtype.val)) V.weight :=
  (Measure.measurable_rnDeriv _ _).aemeasurable.congr
    (V.symmetricFirstVariationDensity_ae_eq_rnDeriv μ).symm

theorem weight_symmetricFirstVariationDensity_top
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ] :
    V.weight {x | V.symmetricFirstVariationDensity (μ.map Subtype.val) x = ∞} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  exact V.symmetricFirstVariationDensity_ne_top_ae μ

/-- Compatibility with the earlier RN representative. The pointwise
symmetric density and that representative agree only weight-almost everywhere;
one must not infer equality of their pointwise infinity sets. -/
theorem symmetricFirstVariationDensity_ae_eq_firstVariationDensity
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ] :
    V.symmetricFirstVariationDensity (μ.map Subtype.val) =ᵐ[V.weight]
      V.firstVariationDensity (μ.map Subtype.val) :=
  V.symmetricFirstVariationDensity_ae_eq_rnDeriv μ

end
end Varifold
end Poincare.SimonGMT.Chapter08

namespace Poincare.SimonGMT.Chapter08.Varifold
noncomputable section
variable {N n : ℕ} {U : Set (Euclidean N)} {V : Varifold N n U}
  {μ : Measure (Euclidean N)}

theorem IsFirstVariationMeasure.map_comap_eq
    (hμ : V.IsFirstVariationMeasure μ) :
    (μ.comap (Subtype.val : U → Euclidean N)).map Subtype.val = μ := by
  rw [map_comap_subtype_coe V.isOpen_domain.measurableSet]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  exact hμ.2.1

theorem IsFirstVariationMeasure.finite_on_compact
    (hμ : V.IsFirstVariationMeasure μ) {K : Set (Euclidean N)}
    (hK : IsCompact K) (hKU : K ⊆ U) : μ K ≠ ∞ := by
  let : IsLocallyFiniteMeasure (μ.comap (Subtype.val : U → Euclidean N)) := hμ.1
  rw [← hμ.map_comap_eq,
    Measure.map_apply measurable_subtype_coe hK.measurableSet]
  apply IsCompact.measure_ne_top
  apply Topology.IsInducing.subtypeVal.isCompact_preimage' hK
  simpa using hKU

theorem IsFirstVariationMeasure.regular_comap
    (hμ : V.IsFirstVariationMeasure μ) :
    Measure.Regular (μ.comap (Subtype.val : U → Euclidean N)) := by
  let : LocallyCompactSpace U := V.isOpen_domain.locallyCompactSpace
  let : IsLocallyFiniteMeasure (μ.comap (Subtype.val : U → Euclidean N)) := hμ.1
  infer_instance

theorem IsFirstVariationMeasure.sigmaFinite
    (hμ : V.IsFirstVariationMeasure μ) : SigmaFinite μ := by
  let : IsLocallyFiniteMeasure (μ.comap (Subtype.val : U → Euclidean N)) := hμ.1
  rw [← hμ.map_comap_eq]
  exact (MeasurableEmbedding.subtype_coe V.isOpen_domain.measurableSet).sigmaFinite_map

theorem IsFirstVariationMeasure.hasLocallyBoundedFirstVariation
    (hμ : V.IsFirstVariationMeasure μ) : V.HasLocallyBoundedFirstVariation := by
  intro W hW hWU
  rw [← hμ.2.2 W hW hWU]
  exact ne_top_of_le_ne_top (hμ.finite_on_compact hWU.1 hWU.2) (measure_mono subset_closure)

/-- The source's (2.7) for any measure satisfying the exact local
characterization (2.5). The existence of such a measure is separate. -/
theorem IsFirstVariationMeasure.symmetricDensity_spec
    (hμ : V.IsFirstVariationMeasure μ) :
    AEMeasurable (V.symmetricFirstVariationDensity μ) V.weight ∧
      ∀ᵐ x ∂V.weight,
        Tendsto (fun r : ℝ ↦ μ (closedBall x r) / V.weight (closedBall x r))
          (𝓝[>] (0 : ℝ)) (𝓝 (V.symmetricFirstVariationDensity μ x)) ∧
        V.symmetricFirstVariationDensity μ x ≠ ∞ := by
  let : IsLocallyFiniteMeasure (μ.comap (Subtype.val : U → Euclidean N)) := hμ.1
  have hm := V.aemeasurable_symmetricFirstVariationDensity (μ.comap Subtype.val)
  have ht := V.ae_tendsto_symmetricFirstVariationDensity (μ.comap Subtype.val)
  have hf := V.symmetricFirstVariationDensity_ne_top_ae (μ.comap Subtype.val)
  rw [hμ.map_comap_eq] at hm ht hf
  exact ⟨hm, ht.and hf⟩

end
end Poincare.SimonGMT.Chapter08.Varifold
