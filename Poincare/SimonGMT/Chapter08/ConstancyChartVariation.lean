module

public import Poincare.SimonGMT.Chapter08.ConstancyChartDensity
public import Poincare.SimonGMT.Chapter08.ConstancyTangentGraph

@[expose] public section

/-!
# Stationary first variation in genuine nonlinear chart coordinates

The identified coordinate density transports stationary first variation
to parameter-space volume. The tangent plane is then replaced by the
range of the actual chart derivative, using the already proved support
tangent theorem. The ambient test fields are supported in the chart.

This establishes the weighted coordinate tangential-divergence equation,
not yet the vanishing distributional derivatives of the Hausdorff density.
That final step still needs tangent coordinate test fields and the
Jacobian-weighted divergence identity.
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

/-- Tangential divergence expressed using the range of the actual
parametrization derivative, with no independently supplied tangent field. -/
def chartTangentialDivergence (φ : Euclidean n → Euclidean N)
    (X : Euclidean N → Euclidean N) (u : Euclidean n) : ℝ :=
  LinearMap.trace ℝ (Euclidean N)
    ((fderiv ℝ X (φ u)).toLinearMap.comp
      (fderiv ℝ φ u).range.starProjection.toLinearMap)

/-- The measurable tangent graph and the nonlinear area formula give
the coordinate first-variation equation for every ambient test field
supported in the chart. Integrability is part of the conclusion. -/
theorem Stationary.exists_chart_firstVariation {V : Varifold N n U}
    (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M) (hne : M.Nonempty)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ) :
    ∃ T : Euclidean N → Grassmannian N n,
      Measurable T ∧ ContinuousOn T (U ∩ V.weight.support) ∧
      V.measure = V.weight.map (fun x ↦ (x, T x)) ∧
      ∀ X : TestVectorField (N := N) U, tsupport X ⊆ W →
        IntegrableOn (fun u ↦ V.chartGeometricDensity M φ u *
          tangentialDivergence X (φ u) (T (φ u))) D ∧
        (∫ u in D, V.chartGeometricDensity M φ u *
          tangentialDivergence X (φ u) (T (φ u))) = 0 := by
  obtain ⟨T, hTm, hTc, _, hgraph⟩ := hV.exists_measurable_tangentGraph hM hSM hne
  refine ⟨T, hTm, hTc, hgraph, ?_⟩
  intro X hXW
  have hmap : Measurable (fun x ↦ (x, T x)) := measurable_id.prodMk hTm
  have hF := V.integrable_tangentialDivergence X X.contDiff X.compactSupport X.support_subset
  rw [hgraph] at hF
  have hg := hF.comp_measurable hmap
  obtain ⟨hint, heq⟩ := hV.integral_chartGeometricDensity hSM hM hφ
    (fun x ↦ tangentialDivergence X x (T x))
  refine ⟨hint.mpr hg.integrableOn, ?_⟩
  rw [heq]
  have hMa : ∀ᵐ x ∂V.weight, x ∈ M :=
    (hV.weight_absolutelyContinuous_carrier hM).ae_le
      (ae_restrict_mem (simonSubmanifold_measurableSet hSM))
  have hzero : ∀ᵐ x ∂V.weight,
      x ∉ W ∩ M → tangentialDivergence X x (T x) = 0 := by
    filter_upwards [hMa] with x hxM
    intro hx
    by_contra hdiv
    have hs : (x, T x) ∈ support
        (fun z : Euclidean N × Grassmannian N n ↦ tangentialDivergence X z.1 z.2) := hdiv
    exact hx ⟨hXW ((support_tangentialDivergence_subset X) hs).1, hxM⟩
  rw [setIntegral_eq_integral_of_ae_compl_eq_zero hzero]
  calc
    (∫ x, tangentialDivergence X x (T x) ∂V.weight) = V.firstVariation X := by
      rw [firstVariation, hgraph]
      exact (integral_map hmap.aemeasurable hF.aestronglyMeasurable).symm
    _ = 0 := hV X

/-- An ambient almost-everywhere property pulls back to the actual
chart weight. No measurability of the predicate is needed. -/
theorem ae_chartWeight_of_ae_weight (V : Varifold N n U)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    {p : Euclidean N → Prop} (hp : ∀ᵐ x ∂V.weight, p x) :
    ∀ᵐ u ∂V.chartWeight D φ, u ∈ D ∧ p (φ u) := by
  have he := measurableEmbedding_simonChart hφ
  have hp' : ∀ᵐ x ∂(V.weight.comap (fun u : D ↦ φ u)).map
      (fun u : D ↦ φ u), p x := by
    rw [he.map_comap]
    exact ae_restrict_of_ae hp
  rw [chartWeight, (MeasurableEmbedding.subtype_coe
    hφ.isOpen_source.measurableSet).ae_map_iff]
  filter_upwards [ae_of_ae_map he.measurable.aemeasurable hp'] with u hu
  exact ⟨u.property, hu⟩

/-- On the actual coordinate weight, the measurable support tangent
is exactly the range of the chart derivative. -/
theorem Stationary.chart_tangentGraph_ae_eq_range {V : Varifold N n U}
    (hV : V.Stationary) (hM : U ∩ V.weight.support ⊆ M)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    {T : Euclidean N → Grassmannian N n} (hTm : Measurable T)
    (hgraph : V.measure = V.weight.map (fun x ↦ (x, T x))) :
    ∀ᵐ u ∂V.chartWeight D φ, (T (φ u)).plane = (fderiv ℝ φ u).range := by
  have hmap : Measurable (fun x ↦ (x, T x)) := measurable_id.prodMk hTm
  have hs : ∀ᵐ x ∂V.weight, (x, T x) ∈ V.measure.support := by
    apply ae_of_ae_map hmap.aemeasurable
    rw [← hgraph]
    exact V.measure.support_mem_ae
  have hU : ∀ᵐ x ∂V.weight, x ∈ U := by
    have h := V.ae_mem_domain
    rw [hgraph] at h
    exact (ae_of_ae_map hmap.aemeasurable h).mono (fun _ hx ↦ hx.1)
  filter_upwards [V.ae_chartWeight_of_ae_weight hφ (hs.and hU)] with u hu
  exact hV.plane_eq_parametrizedTangent hM hφ hu.1 hu.2.1 hu.2.2

/-- The genuine nonlinear parameter-coordinate first-variation equation.
The integrand uses Simon's explicit normalization, the constructed
Hausdorff density, the actual metric Jacobian, and the derivative-range
tangent. No density, Jacobian, or tangent identity is assumed. -/
theorem Stationary.chart_firstVariation {V : Varifold N n U}
    (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M) (hne : M.Nonempty)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    (X : TestVectorField (N := N) U) (hXW : tsupport X ⊆ W) :
    IntegrableOn (fun u ↦ V.chartGeometricDensity M φ u *
      chartTangentialDivergence φ X u) D ∧
      (∫ u in D, V.chartGeometricDensity M φ u *
        chartTangentialDivergence φ X u) = 0 := by
  obtain ⟨T, hTm, _, hgraph, hstationary⟩ :=
    hV.exists_chart_firstVariation hSM hM hne hφ
  obtain ⟨hint, hzero⟩ := hstationary X hXW
  have hplane := hV.chart_tangentGraph_ae_eq_range hM hφ hTm hgraph
  rw [hV.chartWeight_eq_withDensity_geometric hSM hM hφ] at hplane
  have hplane' := (ae_withDensity_iff'
    (V.aemeasurable_chartGeometricDensity hφ).ennreal_ofReal).mp hplane
  have heq : (fun u ↦ V.chartGeometricDensity M φ u *
      tangentialDivergence X (φ u) (T (φ u))) =ᵐ[volume.restrict D]
      (fun u ↦ V.chartGeometricDensity M φ u * chartTangentialDivergence φ X u) := by
    filter_upwards [hplane'] with u hu
    by_cases hρ : V.chartGeometricDensity M φ u = 0
    · simp only [hρ, zero_mul]
    · have hρ' : ENNReal.ofReal (V.chartGeometricDensity M φ u) ≠ 0 := by
        intro hz
        have hz' := congrArg ENNReal.toReal hz
        apply hρ
        simpa only [ENNReal.toReal_ofReal (V.chartGeometricDensity_nonneg M φ u),
          ENNReal.toReal_zero] using hz'
      simp only [chartTangentialDivergence, tangentialDivergence_eq_trace, hu hρ']
  exact ⟨hint.congr heq, (integral_congr_ae heq).symm.trans hzero⟩

end Varifold
end
end Poincare.SimonGMT.Chapter08
