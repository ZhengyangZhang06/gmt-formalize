module

public import Poincare.SimonGMT.Chapter08.ConstancyNormalCharts
public import Poincare.SimonGMT.Chapter08.ConstancyHausdorffDensity

@[expose] public section

/-!
# The measurable tangent graph in Simon's constancy argument

Compactness of the actual projection-matrix Grassmannian implies that
the projection of the varifold support is exactly the support of its
weight. The singleton-fiber theorem derived from Simon's parametrizations
then constructs a continuous tangent field on that support inside `U`.
Its measurable extension gives the genuine graph-measure identity used
in proof (4) of Simon (8.4.1), with no measurability or tangent-identity
premise. The nonlinear area formula and constancy of the density are not
asserted here.

Source: Simon (8.4.1), proof (4), printed pp. 214--215.
-/

open Set Filter Function MeasureTheory
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {N n : ℕ}

namespace Varifold
variable {U M : Set (Euclidean N)}

/-- Compactness of the Grassmannian prevents a weight-support point
from losing every plane in the bundle support. -/
theorem weight_support_eq_fst_image_support (V : Varifold N n U) :
    V.weight.support = Prod.fst '' V.measure.support := by
  have hc : IsClosed (Prod.fst '' V.measure.support) :=
    isClosedMap_fst_of_compactSpace _ V.measure.isClosed_support
  apply Subset.antisymm
  · apply Measure.support_subset_of_isClosed hc
    change ∀ᵐ x ∂V.measure.map Prod.fst, x ∈ Prod.fst '' V.measure.support
    apply (ae_map_iff measurable_fst.aemeasurable hc.measurableSet).mpr
    filter_upwards [V.measure.support_mem_ae] with z hz
    exact mem_image_of_mem Prod.fst hz
  · rintro _ ⟨z, hz, rfl⟩
    exact V.fst_mem_weight_support_of_mem_support hz

/-- Stationarity and the actual manifold hypothesis construct a
continuous tangent field on the relevant weight support. -/
theorem Stationary.exists_continuous_support_tangent {V : Varifold N n U}
    (hV : V.Stationary) (hM : U ∩ V.weight.support ⊆ M)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M) :
    ∃ T : ↥(U ∩ V.weight.support) → Grassmannian N n,
      Continuous T ∧ ∀ x : ↥(U ∩ V.weight.support),
        ((x : Euclidean N), T x) ∈ V.measure.support := by
  have hex : ∀ x : ↥(U ∩ V.weight.support),
      ∃ S : Grassmannian N n, ((x : Euclidean N), S) ∈ V.measure.support := by
    intro x
    have hx := V.weight_support_eq_fst_image_support.subset x.property.2
    obtain ⟨⟨y, S⟩, hS, hy⟩ := hx
    exact ⟨S, hy ▸ hS⟩
  choose T hT using hex
  refine ⟨T, ?_, hT⟩
  apply continuous_of_isClosed_graph
  have heq : T.graph =
      (fun z : ↥(U ∩ V.weight.support) × Grassmannian N n ↦
        ((z.1 : Euclidean N), z.2)) ⁻¹' V.measure.support := by
    ext z
    change T z.1 = z.2 ↔ ((z.1 : Euclidean N), z.2) ∈ V.measure.support
    constructor
    · intro hz
      rw [← hz]
      exact hT z.1
    · intro hz
      exact hV.support_fiber_subsingleton hM hSM z.1.property.1 (hT z.1) hz
  rw [heq]
  exact V.measure.isClosed_support.preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

/-- A freely chosen plane is used only outside the relevant support.
The actual support planes and the graph measure are constructed. -/
theorem Stationary.exists_measurable_tangentGraph_with_default {V : Varifold N n U}
    (hV : V.Stationary) (hM : U ∩ V.weight.support ⊆ M)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (S₀ : Grassmannian N n) :
    ∃ T : Euclidean N → Grassmannian N n,
      Measurable T ∧ ContinuousOn T (U ∩ V.weight.support) ∧
      (∀ x ∈ U, ∀ S : Grassmannian N n,
        (x, S) ∈ V.measure.support → S = T x) ∧
      V.measure = V.weight.map (fun x ↦ (x, T x)) := by
  classical
  obtain ⟨T, hTc, hT⟩ := hV.exists_continuous_support_tangent hM hSM
  let A := U ∩ V.weight.support
  let T' : Euclidean N → Grassmannian N n :=
    fun x ↦ if hx : x ∈ A then T ⟨x, hx⟩ else S₀
  have hA : MeasurableSet A :=
    V.isOpen_domain.measurableSet.inter V.weight.isClosed_support.measurableSet
  have hT'm : Measurable T' := hTc.measurable.dite measurable_const hA
  have hT'c : ContinuousOn T' A := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : A ↦ T' x)
    simpa [T'] using hTc
  have hplane : ∀ x ∈ U, ∀ S : Grassmannian N n,
      (x, S) ∈ V.measure.support → S = T' x := by
    intro x hx S hS
    have hxA : x ∈ A := ⟨hx, V.fst_mem_weight_support_of_mem_support hS⟩
    change S = if hx' : x ∈ A then T ⟨x, hx'⟩ else S₀
    rw [dite_eq_left hxA]
    exact hV.support_fiber_subsingleton hM hSM hx hS (hT ⟨x, hxA⟩)
  refine ⟨T', hT'm, hT'c, hplane, ?_⟩
  apply V.measure_eq_map_tangentGraph T' hT'm
  filter_upwards [V.measure.support_mem_ae, V.ae_mem_domain] with z hz hzU
  exact hplane z.1 hzU.1 z.2 hz

/-- A nonempty Simon manifold supplies the fallback plane itself, by
taking the range of one genuine chart derivative. -/
theorem Stationary.exists_measurable_tangentGraph {V : Varifold N n U}
    (hV : V.Stationary) (hM : U ∩ V.weight.support ⊆ M)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hne : M.Nonempty) :
    ∃ T : Euclidean N → Grassmannian N n,
      Measurable T ∧ ContinuousOn T (U ∩ V.weight.support) ∧
      (∀ x ∈ U, ∀ S : Grassmannian N n,
        (x, S) ∈ V.measure.support → S = T x) ∧
      V.measure = V.weight.map (fun x ↦ (x, T x)) := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨D, W, φ, hxW, hφ⟩ := hSM.exists_localRepresentation hx
  obtain ⟨a, ha, rfl⟩ : x ∈ φ '' D := by rw [hφ.image_eq]; exact ⟨hxW, hx⟩
  have hrank : Module.finrank ℝ (fderiv ℝ φ a).range = n := by
    simpa using LinearMap.finrank_range_of_inj (hφ.injective_fderiv ha)
  exact hV.exists_measurable_tangentGraph_with_default hM hSM
    (Grassmannian.ofSubmodule (fderiv ℝ φ a).range hrank)

/-- The actual bundle measure has Simon's Hausdorff-density graph
representation. Both the density and measurable support tangent are
constructed; the density is not yet proved constant. -/
theorem Stationary.exists_hausdorffDensity_tangentGraph {V : Varifold N n U}
    (hV : V.Stationary) (hM : U ∩ V.weight.support ⊆ M)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hne : M.Nonempty) :
    ∃ T : Euclidean N → Grassmannian N n,
      Measurable T ∧ ContinuousOn T (U ∩ V.weight.support) ∧
      V.measure =
        (((Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict M).withDensity
          (fun x ↦ ENNReal.ofReal (V.constancyDensity M x))).map (fun x ↦ (x, T x)) := by
  obtain ⟨T, hTm, hTc, _, hgraph⟩ := hV.exists_measurable_tangentGraph hM hSM hne
  refine ⟨T, hTm, hTc, ?_⟩
  rw [(hV.constancyDensity_representation hSM hM).2.2.2]
  exact hgraph

/-- Stationarity becomes the actual weighted tangential-divergence
equation on the manifold, with integrability proved. The further change
to parameter coordinates still requires the nonlinear Jacobian formula. -/
theorem Stationary.exists_constancyDensity_tangent_divergence {V : Varifold N n U}
    (hV : V.Stationary) (hM : U ∩ V.weight.support ⊆ M)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hne : M.Nonempty) :
    ∃ T : Euclidean N → Grassmannian N n,
      Measurable T ∧ ContinuousOn T (U ∩ V.weight.support) ∧
      V.measure = V.weight.map (fun x ↦ (x, T x)) ∧
      ∀ X : TestVectorField (N := N) U,
        Integrable (fun x ↦ V.constancyDensity M x * tangentialDivergence X x (T x))
          ((Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict M) ∧
        (∫ x, V.constancyDensity M x * tangentialDivergence X x (T x)
          ∂(Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict M) = 0 := by
  obtain ⟨T, hTm, hTc, _, hgraph⟩ := hV.exists_measurable_tangentGraph hM hSM hne
  refine ⟨T, hTm, hTc, hgraph, ?_⟩
  intro X
  have hmap : Measurable (fun x ↦ (x, T x)) := measurable_id.prodMk hTm
  have hF := V.integrable_tangentialDivergence X X.contDiff X.compactSupport X.support_subset
  rw [hgraph] at hF
  have hg := hF.comp_measurable hmap
  obtain ⟨hint, heq⟩ := hV.integral_constancyDensity hSM hM
    (fun x ↦ tangentialDivergence X x (T x))
  refine ⟨hint.mpr hg, ?_⟩
  rw [heq]
  calc
    (∫ x, tangentialDivergence X x (T x) ∂V.weight) = V.firstVariation X := by
      rw [firstVariation, hgraph]
      exact (integral_map hmap.aemeasurable hF.aestronglyMeasurable).symm
    _ = 0 := hV X

end Varifold
end
end Poincare.SimonGMT.Chapter08
