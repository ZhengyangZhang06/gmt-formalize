module

public import Poincare.SimonGMT.Chapter08.ConstancyPiola
public import Poincare.SimonGMT.Chapter08.ConstancyTangentTests
public import Poincare.SimonGMT.Chapter08.DistributionalConstancy

@[expose] public section

/-!
# Vanishing weak derivatives of the genuine chart multiplicity

The ambient tangent tests, Piola identity, and actual chart first
variation imply zero weak derivatives. Local integrability and the
proved distributional constancy theorem then give local a.e. constancy.
-/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {N n : ℕ}

namespace Varifold
variable {U M : Set (Euclidean N)}

/-- Stationarity yields every weak directional derivative on a genuine
coordinate neighborhood. No weak-equation premise is used. -/
theorem Stationary.exists_chart_density_weakDerivativesZero
    {V : Varifold N n U} (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    {a : Euclidean n} (ha : a ∈ D) (haU : φ a ∈ U) :
    ∃ B : Set (Euclidean n), IsOpen B ∧ a ∈ B ∧ B ⊆ D ∩ φ ⁻¹' U ∧
      WeakDerivativesZero (fun u ↦ V.constancyDensity M (φ u)) B := by
  obtain ⟨B, hBo, haB, hBD, htests⟩ :=
    exists_supported_tangent_coordinate_tests hφ V.isOpen_domain ha haU
  refine ⟨B, hBo, haB, hBD, ?_⟩
  intro η hη hc hs v
  obtain ⟨X, hXW, hXφ⟩ := htests η hη hc hs v
  have hne : M.Nonempty := by
    have h : φ a ∈ φ '' D := mem_image_of_mem φ ha
    rw [hφ.image_eq] at h
    exact ⟨φ a, h.2⟩
  obtain ⟨_, hzero⟩ := hV.chart_firstVariation hSM hM hne hφ X hXW
  have heq : (fun u ↦ V.chartGeometricDensity M φ u * chartTangentialDivergence φ X u)
      =ᵐ[volume.restrict D] (fun u ↦ (Chapter02.simonAreaNormalization n).toReal *
        (V.constancyDensity M (φ u) * fderiv ℝ η u v)) := by
    filter_upwards [ae_restrict_mem hφ.isOpen_source.measurableSet] with u hu
    have hpi := chartTangentialDivergence_coordinate_test hφ hu
      (hη.differentiable_one u) (X.contDiff.differentiable_one (φ u)) v
      (Filter.mem_of_superset (hφ.isOpen_source.mem_nhds hu) (fun z hz ↦ hXφ z hz))
    dsimp only [chartGeometricDensity]
    rw [show (Chapter02.simonAreaNormalization n).toReal *
        (V.constancyDensity M (φ u) * Chapter02.areaJacobianAt φ u) *
          chartTangentialDivergence φ X u =
        (Chapter02.simonAreaNormalization n).toReal * V.constancyDensity M (φ u) *
          (Chapter02.areaJacobianAt φ u * chartTangentialDivergence φ X u) by ring,
      hpi]
    ring
  rw [integral_congr_ae heq, integral_const_mul] at hzero
  have hk : (Chapter02.simonAreaNormalization n).toReal ≠ 0 :=
    (ENNReal.toReal_pos (Chapter02.simonAreaNormalization_pos n).ne'
      (Chapter02.simonAreaNormalization_ne_top n)).ne'
  have hz := (mul_eq_zero.mp hzero).resolve_left hk
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu ↦ ?_)] at hz
  · exact hz
  · have huts : u ∉ tsupport η := fun ht ↦ hu ((hBD (hs ht)).1)
    rw [fderiv_of_notMem_tsupport ℝ huts]
    simp

/-- The constructed Hausdorff density is a.e. constant on some open
coordinate neighborhood of every point in the actual domain. -/
theorem Stationary.exists_chart_density_ae_eq_const_nhds
    {V : Varifold N n U} (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    {a : Euclidean n} (ha : a ∈ D) (haU : φ a ∈ U) :
    ∃ B : Set (Euclidean n), IsOpen B ∧ a ∈ B ∧ B ⊆ D ∩ φ ⁻¹' U ∧
      ∃ c : ℝ, ∀ᵐ u ∂volume.restrict B, V.constancyDensity M (φ u) = c := by
  obtain ⟨A, hAo, haA, hAD, hw⟩ :=
    hV.exists_chart_density_weakDerivativesZero hSM hM hφ ha haU
  obtain ⟨B, hBo, haB, hBA, c, hc⟩ := hw.exists_ae_eq_const_nhds
    ((hV.locallyIntegrableOn_constancyDensity_comp_chart hSM hM hφ).mono_set hAD) hAo haA
  exact ⟨B, hBo, haB, hBA.trans hAD, c, hc⟩

/-- Connected gluing in any open part of a genuine coordinate chart.
The connectedness concerns the actual coordinate domain mapping into U. -/
theorem Stationary.chart_density_ae_eq_const
    {V : Varifold N n U} (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M)
    {W : Set (Euclidean N)} {D B : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    (hBo : IsOpen B) (hBc : IsPreconnected B) (hBD : B ⊆ D ∩ φ ⁻¹' U) :
    ∃ c : ℝ, ∀ᵐ u ∂volume.restrict B, V.constancyDensity M (φ u) = c := by
  apply ae_eq_const_of_locally_ae_eq_const hBc
  intro a ha
  obtain ⟨A, hAo, haA, _, c, hc⟩ :=
    hV.exists_chart_density_ae_eq_const_nhds hSM hM hφ (hBD ha).1 (hBD ha).2
  exact ⟨A ∩ B, hAo.inter hBo, ⟨haA, ha⟩, inter_subset_right, c,
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hc⟩

end Varifold
end
end Poincare.SimonGMT.Chapter08
