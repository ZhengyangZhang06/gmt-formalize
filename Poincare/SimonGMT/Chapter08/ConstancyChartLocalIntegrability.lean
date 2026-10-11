module

public import Poincare.SimonGMT.Chapter08.ConstancyChartDensity

@[expose] public section

/-!
# Local integrability of the Hausdorff density in genuine chart coordinates

The area formula identifies the chart density with `κ * (θ ∘ φ) * Jφ`.
On compact parameter sets inside the actual varifold domain, the chart
weight is finite. Positivity and continuity of the actual Jacobian then
allow division by `κ * Jφ`, proving `L¹_loc` for `θ ∘ φ` itself.

This supplies the local-integrability hypothesis required by the weak-
derivative constancy theorem in arbitrary codimension. The relevant open
set is precisely `D ∩ φ ⁻¹' U`; no inclusion `M ⊆ U` is assumed.
-/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {N n : ℕ}

theorem continuousOn_areaJacobianAt_simonChart
    {M W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ) :
    ContinuousOn (Chapter02.areaJacobianAt φ) D := by
  have he : Chapter02.areaJacobianAt φ = fun u ↦ (fderiv ℝ φ u).normDet := by
    funext u
    exact Chapter02.areaJacobianAt_eq_normDet φ u
  rw [he]
  exact Chapter02.continuous_normDet.comp_continuousOn
    (hφ.contDiffOn.continuousOn_fderiv_of_isOpen hφ.isOpen_source (by norm_num))

theorem areaJacobianAt_pos_simonChart
    {M W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    {u : Euclidean n} (hu : u ∈ D) : 0 < Chapter02.areaJacobianAt φ u := by
  have hn : Chapter02.areaJacobianAt φ u ≠ 0 := by
    rw [Chapter02.areaJacobianAt_eq_normDet]
    exact ((fderiv ℝ φ u).toLinearMap.normDet_ne_zero_tfae.out 5 1).mp
      (hφ.injective_fderiv hu)
  exact lt_of_le_of_ne (Chapter02.areaJacobianAt_nonneg φ u) hn.symm

namespace Varifold
variable {U M : Set (Euclidean N)}

/-- Chart compact sets have finite pullback weight whenever their whole
image lies in the actual open varifold domain. -/
theorem chartWeight_finite_on_compact (V : Varifold N n U)
    {W : Set (Euclidean N)} {D K : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    (hK : IsCompact K) (hKD : K ⊆ D) (hKU : φ '' K ⊆ U) :
    V.chartWeight D φ K ≠ ⊤ := by
  rw [V.chartWeight_apply hφ, inter_eq_left.mpr hKD]
  exact V.weight_finite_on_compact _
    (hK.image_of_continuousOn (hφ.contDiffOn.continuousOn.mono hKD)) hKU

/-- Integrability of the Hausdorff density itself in parameter volume
on every compact set whose image remains in `U`. Neither integrability
of this composition nor a lower bound for the Jacobian is assumed. -/
theorem Stationary.integrableOn_constancyDensity_comp_chart_of_compact
    {V : Varifold N n U} (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M)
    {W : Set (Euclidean N)} {D K : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    (hK : IsCompact K) (hKD : K ⊆ D) (hKU : φ '' K ⊆ U) :
    IntegrableOn (fun u ↦ V.constancyDensity M (φ u)) K := by
  have hρ : IntegrableOn (V.chartDensity D φ) K :=
    Measure.integrableOn_toReal_rnDeriv (V.chartWeight_finite_on_compact hφ hK hKD hKU)
  have hgeo : IntegrableOn (V.chartGeometricDensity M φ) K := hρ.congr_fun_ae
    (ae_restrict_of_ae_restrict_of_subset hKD (hV.chartDensity_ae_eq_geometric hSM hM hφ))
  have hk : (Chapter02.simonAreaNormalization n).toReal ≠ 0 :=
    (ENNReal.toReal_pos (Chapter02.simonAreaNormalization_pos n).ne'
      (Chapter02.simonAreaNormalization_ne_top n)).ne'
  have hden : ∀ u ∈ K,
      (Chapter02.simonAreaNormalization n).toReal * Chapter02.areaJacobianAt φ u ≠ 0 := by
    intro u hu
    exact mul_ne_zero hk (areaJacobianAt_pos_simonChart hφ (hKD hu)).ne'
  have hcont : ContinuousOn (fun u ↦
      ((Chapter02.simonAreaNormalization n).toReal * Chapter02.areaJacobianAt φ u)⁻¹) K :=
    (continuousOn_const.mul ((continuousOn_areaJacobianAt_simonChart hφ).mono hKD)).inv₀ hden
  apply (hgeo.mul_continuousOn hcont hK).congr_fun _ hK.measurableSet
  intro u hu
  calc
    V.chartGeometricDensity M φ u *
        ((Chapter02.simonAreaNormalization n).toReal * Chapter02.areaJacobianAt φ u)⁻¹ =
      V.constancyDensity M (φ u) *
        (((Chapter02.simonAreaNormalization n).toReal * Chapter02.areaJacobianAt φ u) *
          ((Chapter02.simonAreaNormalization n).toReal * Chapter02.areaJacobianAt φ u)⁻¹) := by
            dsimp only [chartGeometricDensity]
            ring
    _ = _ := by rw [mul_inv_cancel₀ (hden u hu), mul_one]

theorem isOpen_chartDomain_in_domain (V : Varifold N n U)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ) :
    IsOpen (D ∩ φ ⁻¹' U) := by
  apply isOpen_iff_mem_nhds.mpr
  intro u hu
  exact inter_mem (hφ.isOpen_source.mem_nhds hu.1)
    (((hφ.contDiffOn u hu.1).contDiffAt
      (hφ.isOpen_source.mem_nhds hu.1)).continuousAt (V.isOpen_domain.mem_nhds hu.2))

/-- The actual geometric Hausdorff density, expressed in any genuine
nonlinear chart, is locally integrable on exactly the part of the chart
mapping into the varifold's domain. -/
theorem Stationary.locallyIntegrableOn_constancyDensity_comp_chart
    {V : Varifold N n U} (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ) :
    LocallyIntegrableOn (fun u ↦ V.constancyDensity M (φ u)) (D ∩ φ ⁻¹' U) volume := by
  apply (locallyIntegrableOn_iff (V.isOpen_chartDomain_in_domain hφ).isLocallyClosed).mpr
  intro K hK hKc
  apply hV.integrableOn_constancyDensity_comp_chart_of_compact hSM hM hφ hKc
    (hK.trans inter_subset_left)
  rintro _ ⟨u, hu, rfl⟩
  exact (hK hu).2

end Varifold
end
end Poincare.SimonGMT.Chapter08
