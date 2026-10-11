module

public import Poincare.SimonGMT.Chapter08.ConstancyChartTransport
public import Poincare.SimonGMT.Chapter02.AreaNormalization

@[expose] public section

/-!
# Identifying the actual coordinate density in Simon's constancy proof

The nonlinear area formula identifies the previously constructed chart
Radon--Nikodym density with the Hausdorff density times the actual metric
Jacobian. Simon's explicit normalization scalar is retained throughout.
Neither the density identity nor an area-transport premise is assumed.
-/

open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {N n : ℕ}

namespace Varifold
variable {U M : Set (Euclidean N)}

/-- The geometric coordinate expression, with the literal Simon
normalization made explicit. -/
def chartGeometricDensity (V : Varifold N n U) (M : Set (Euclidean N))
    (φ : Euclidean n → Euclidean N) (u : Euclidean n) : ℝ :=
  (Chapter02.simonAreaNormalization n).toReal *
    (V.constancyDensity M (φ u) * Chapter02.areaJacobianAt φ u)

theorem chartGeometricDensity_nonneg (V : Varifold N n U)
    (M : Set (Euclidean N)) (φ : Euclidean n → Euclidean N) (u : Euclidean n) :
    0 ≤ V.chartGeometricDensity M φ u := by
  apply mul_nonneg ENNReal.toReal_nonneg
  exact mul_nonneg ENNReal.toReal_nonneg (Chapter02.areaJacobianAt_nonneg φ u)

theorem aemeasurable_chartGeometricDensity (V : Varifold N n U)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ) :
    AEMeasurable (V.chartGeometricDensity M φ) (volume.restrict D) := by
  have hθ : Measurable (V.constancyDensity M) :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hφm : AEMeasurable φ (volume.restrict D) :=
    hφ.contDiffOn.continuousOn.aemeasurable hφ.isOpen_source.measurableSet
  exact aemeasurable_const.mul
    ((hθ.comp_aemeasurable hφm).mul (Chapter02.measurable_areaJacobianAt φ).aemeasurable)

/-- The chart pullback weight is exactly the geometric Jacobian density
against parameter-space volume, extended by zero off the chart domain. -/
theorem Stationary.chartWeight_eq_withDensity_geometric {V : Varifold N n U}
    (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ) :
    V.chartWeight D φ = (volume.restrict D).withDensity
      (fun u ↦ ENNReal.ofReal (V.chartGeometricDensity M φ u)) := by
  have hD := hφ.isOpen_source.measurableSet
  have hMm := simonSubmanifold_measurableSet hSM
  obtain ⟨hθm, hθ0, _, hweight⟩ := hV.constancyDensity_representation hSM hM
  have hpre : (fun u : D ↦ φ u) ⁻¹' M = univ := by
    apply eq_univ_of_forall
    intro u
    have hu : φ u ∈ φ '' D := mem_image_of_mem φ u.property
    rw [hφ.image_eq] at hu
    exact hu.2
  have hdiff : ∀ u ∈ D, DifferentiableAt ℝ φ u := by
    intro u hu
    exact ((hφ.contDiffOn u hu).contDiffAt
      (hφ.isOpen_source.mem_nhds hu)).differentiableAt (by norm_num)
  have harea := Chapter02.pullback_withDensity_simonHausdorff_eq hD hdiff
    (fun u hu ↦ hφ.injective_fderiv hu) hφ.injOn
    (fun y ↦ ENNReal.ofReal (V.constancyDensity M y))
  have hdim : Module.finrank ℝ (Euclidean n) = n := by simp
  rw [hdim] at harea
  rw [chartWeight, ← hweight, ← restrict_withDensity hMm,
    (measurableEmbedding_simonChart hφ).comap_restrict, hpre, Measure.restrict_univ]
  change (((Chapter01.simonHausdorffMeasureReal (n : ℝ)).withDensity
    (fun y ↦ ENNReal.ofReal (V.constancyDensity M y))).comap
      (D.domRestrict φ)).map Subtype.val = _
  rw [harea]
  congr 1
  funext u
  rw [chartGeometricDensity, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (Chapter02.simonAreaNormalization_ne_top n),
    ENNReal.ofReal_mul (hθ0 (φ u)), mul_comm (ENNReal.ofReal (V.constancyDensity M (φ u)))]

/-- The actual chart weight is carried by its parameter domain. -/
theorem chartWeight_restrict_source (V : Varifold N n U)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ) :
    (V.chartWeight D φ).restrict D = V.chartWeight D φ := by
  ext A hA
  rw [Measure.restrict_apply hA, V.chartWeight_apply hφ, V.chartWeight_apply hφ,
    inter_assoc, inter_self]

/-- Uniqueness of Radon--Nikodym densities identifies the previously
constructed coordinate density with the geometric expression almost
everywhere on the entire chart domain. -/
theorem Stationary.chartDensity_ae_eq_geometric {V : Varifold N n U}
    (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ) :
    V.chartDensity D φ =ᵐ[volume.restrict D] V.chartGeometricDensity M φ := by
  obtain ⟨hρm, hρ0, hρ⟩ := hV.chartDensity_representation hφ
  have hρD := congrArg (fun μ : Measure (Euclidean n) ↦ μ.restrict D) hρ
  rw [restrict_withDensity hφ.isOpen_source.measurableSet,
    V.chartWeight_restrict_source hφ, hV.chartWeight_eq_withDensity_geometric hSM hM hφ] at hρD
  have heq := (withDensity_eq_iff_of_sigmaFinite
    hρm.ennreal_ofReal.aemeasurable
    (V.aemeasurable_chartGeometricDensity hφ).ennreal_ofReal).mp hρD
  filter_upwards [heq] with u hu
  have hreal := congrArg ENNReal.toReal hu
  simpa only [ENNReal.toReal_ofReal (hρ0 u),
    ENNReal.toReal_ofReal (V.chartGeometricDensity_nonneg M φ u)] using hreal

/-- Literal pointwise formula for the constructed chart RN density,
valid almost everywhere with respect to source volume. -/
theorem Stationary.chartDensity_ae_eq_normalization_mul_density_mul_jacobian
    {V : Varifold N n U} (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ) :
    ∀ᵐ u ∂volume.restrict D,
      V.chartDensity D φ u = (Chapter02.simonAreaNormalization n).toReal *
        (V.constancyDensity M (φ u) * Chapter02.areaJacobianAt φ u) :=
  hV.chartDensity_ae_eq_geometric hSM hM hφ

/-- Integration against the genuine chart pullback agrees with integration
over the entire ambient carrier patch. This statement also records the
integrability equivalence and does not require global measurability of the
parametrization outside its source domain. -/
theorem integral_chartWeight (V : Varifold N n U)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    (g : Euclidean N → ℝ) :
    (Integrable (fun u ↦ g (φ u)) (V.chartWeight D φ) ↔
      IntegrableOn g (W ∩ M) V.weight) ∧
      (∫ u, g (φ u) ∂V.chartWeight D φ) = ∫ x in W ∩ M, g x ∂V.weight := by
  have he := measurableEmbedding_simonChart hφ
  have hrange : range (fun u : D ↦ φ u) = W ∩ M := by
    rw [← image_eq_range, hφ.image_eq]
  constructor
  · rw [chartWeight, (MeasurableEmbedding.subtype_coe
      hφ.isOpen_source.measurableSet).integrable_map_iff]
    change Integrable (g ∘ (fun u : D ↦ φ u)) _ ↔ _
    rw [← he.integrable_map_iff, he.map_comap, hrange]
    rfl
  · rw [chartWeight, (MeasurableEmbedding.subtype_coe
      hφ.isOpen_source.measurableSet).integral_map,
      ← he.integral_map g, he.map_comap, hrange]

/-- The constructed geometric density transports arbitrary real-valued
integrals, with integrability on both sides, to the ambient weight on the
chart patch. -/
theorem Stationary.integral_chartGeometricDensity {V : Varifold N n U}
    (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    (g : Euclidean N → ℝ) :
    (IntegrableOn (fun u ↦ V.chartGeometricDensity M φ u * g (φ u)) D ↔
      IntegrableOn g (W ∩ M) V.weight) ∧
      (∫ u in D, V.chartGeometricDensity M φ u * g (φ u)) =
        ∫ x in W ∩ M, g x ∂V.weight := by
  have hm := (V.aemeasurable_chartGeometricDensity hφ).ennreal_ofReal
  have ht : ∀ᵐ u ∂volume.restrict D,
      ENNReal.ofReal (V.chartGeometricDensity M φ u) < ⊤ :=
    Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)
  have hreal : (fun u ↦ (ENNReal.ofReal (V.chartGeometricDensity M φ u)).toReal •
      g (φ u)) = fun u ↦ V.chartGeometricDensity M φ u * g (φ u) := by
    funext u
    rw [ENNReal.toReal_ofReal (V.chartGeometricDensity_nonneg M φ u), smul_eq_mul]
  obtain ⟨hint, heq⟩ := V.integral_chartWeight hφ g
  rw [hV.chartWeight_eq_withDensity_geometric hSM hM hφ] at hint heq
  rw [integrable_withDensity_iff_integrable_smul₀' hm ht, hreal] at hint
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm ht, hreal] at heq
  exact ⟨hint, heq⟩

end Varifold
end
end Poincare.SimonGMT.Chapter08
