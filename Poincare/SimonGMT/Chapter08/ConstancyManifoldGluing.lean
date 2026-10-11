module

public import Poincare.SimonGMT.Chapter08.ConstancyChartWeakDerivatives

@[expose] public section

/-!
# Hausdorff transport and connected gluing for constancy

Regular chart images have positive Hausdorff measure on every nonempty
relatively open patch. The area formula transports chart a.e. constancy,
and a countable-cover argument glues the constants on the actual domain.
-/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {N n : ℕ}

/-- Every nonempty open part of a regular chart has positive literal
Simon-Hausdorff measure. The normalization remains explicit. -/
theorem simonHausdorff_chart_image_pos
    {M W : Set (Euclidean N)} {D B : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    (hBo : IsOpen B) (hne : B.Nonempty) (hBD : B ⊆ D) :
    0 < (Chapter01.simonHausdorffMeasureReal (n : ℝ)) (φ '' B) := by
  have harea := Chapter02.weighted_area_formula_simonHausdorff_volume_of_injective_derivative
    hBo.measurableSet
    (fun u hu ↦ ((hφ.contDiffOn u (hBD hu)).contDiffAt
      (hφ.isOpen_source.mem_nhds (hBD hu))).differentiableAt (by norm_num))
    (fun u hu ↦ hφ.injective_fderiv (hBD hu)) (hφ.injOn.mono hBD)
    (fun _ : Euclidean N ↦ (1 : ℝ≥0∞))
  rw [show Module.finrank ℝ (Euclidean n) = n by simp] at harea
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one] at harea
  rw [harea]
  apply ENNReal.mul_pos (Chapter02.simonAreaNormalization_pos n).ne'
  apply ne_of_gt
  rw [setLIntegral_pos_iff (Chapter02.measurable_areaJacobianAt φ).ennreal_ofReal]
  have heq : support (fun u ↦ ENNReal.ofReal (Chapter02.areaJacobianAt φ u)) ∩ B = B := by
    apply inter_eq_right.mpr
    intro u hu
    exact (ENNReal.ofReal_pos.mpr (areaJacobianAt_pos_simonChart hφ (hBD hu))).ne'
  rw [heq]
  exact hBo.measure_pos volume hne

/-- A volume-a.e. scalar identity in regular coordinates holds
Hausdorff-a.e. on the whole image patch, by the actual area formula. -/
theorem ae_simonHausdorff_chart_image_of_ae_volume
    {M W : Set (Euclidean N)} {D B : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    (hB : MeasurableSet B) (hBD : B ⊆ D)
    {g : Euclidean N → ℝ} (hg : Measurable g) {c : ℝ}
    (hc : ∀ᵐ u ∂volume.restrict B, g (φ u) = c) :
    ∀ᵐ x ∂(Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict (φ '' B), g x = c := by
  let E : Set (Euclidean N) := {x | g x ≠ c}
  have hE : MeasurableSet E := (measurableSet_eq_fun hg measurable_const).compl
  have harea := Chapter02.weighted_area_formula_simonHausdorff_volume_of_injective_derivative
    hB
    (fun u hu ↦ ((hφ.contDiffOn u (hBD hu)).contDiffAt
      (hφ.isOpen_source.mem_nhds (hBD hu))).differentiableAt (by norm_num))
    (fun u hu ↦ hφ.injective_fderiv (hBD hu)) (hφ.injOn.mono hBD)
    (E.indicator (fun _ ↦ (1 : ℝ≥0∞)))
  have hz : (∫⁻ u in B, ENNReal.ofReal (Chapter02.areaJacobianAt φ u) *
      E.indicator (fun _ ↦ (1 : ℝ≥0∞)) (φ u)) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hc] with u hu
    simp only [indicator_of_notMem (show φ u ∉ E from fun hh ↦ hh hu), mul_zero,
      Pi.zero_apply]
  rw [show Module.finrank ℝ (Euclidean n) = n by simp, hz, mul_zero,
    lintegral_indicator hE, lintegral_one] at harea
  exact ae_iff.mpr (by simpa only [Measure.restrict_apply_univ] using harea)

/-- Literal Hausdorff measure on the carrier subtype. -/
def simonManifoldMeasure (n : ℕ) (M : Set (Euclidean N)) : Measure M :=
  (Chapter01.simonHausdorffMeasureReal (n : ℝ)).comap ((↑) : M → Euclidean N)

/-- A genuine Simon manifold's intrinsic Hausdorff measure is positive
on nonempty open sets, with no support or density premise. -/
theorem isOpenPosMeasure_simonManifoldMeasure
    {M : Set (Euclidean N)}
    (hM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M) :
    (simonManifoldMeasure n M).IsOpenPosMeasure := by
  constructor
  intro A hAo hne
  obtain ⟨O, hOo, hO⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hAo
  obtain ⟨x, hx⟩ := hne
  have hxO : (x : Euclidean N) ∈ O := by rw [← hO] at hx; exact hx
  obtain ⟨D, W, φ, hxW, hφ⟩ := hM.exists_localRepresentation x.property
  obtain ⟨a, ha, hax⟩ : (x : Euclidean N) ∈ φ '' D := by
    rw [hφ.image_eq]
    exact ⟨hxW, x.property⟩
  let B : Set (Euclidean n) := D ∩ φ ⁻¹' O
  have hBo : IsOpen B := by
    apply isOpen_iff_mem_nhds.mpr
    intro u hu
    exact inter_mem (hφ.isOpen_source.mem_nhds hu.1)
      (((hφ.contDiffOn u hu.1).contDiffAt
        (hφ.isOpen_source.mem_nhds hu.1)).continuousAt (hOo.mem_nhds hu.2))
  have hpos := simonHausdorff_chart_image_pos hφ hBo
    ⟨a, ha, (by change φ a ∈ O; rwa [hax])⟩ inter_subset_left
  rw [simonManifoldMeasure,
    (MeasurableEmbedding.subtype_coe (simonSubmanifold_measurableSet hM)).comap_apply]
  apply ne_of_gt
  apply hpos.trans_le (measure_mono ?_)
  rintro _ ⟨u, hu, rfl⟩
  have huM : φ u ∈ M := by
    have h : φ u ∈ φ '' D := mem_image_of_mem φ hu.1
    rw [hφ.image_eq] at h
    exact h.2
  refine ⟨⟨φ u, huM⟩, ?_, rfl⟩
  rw [← hO]
  exact hu.2

/-- Connected gluing also works for a nonopen connected subset, since
the locally constant representatives are compared on ambient open
neighborhoods before restricting their common a.e. identity. -/
theorem ae_eq_const_of_locally_ae_eq_const_near
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure] {g : X → ℝ} {D : Set X}
    (hD : IsPreconnected D)
    (hloc : ∀ x ∈ D, ∃ A : Set X, IsOpen A ∧ x ∈ A ∧
      ∃ c : ℝ, ∀ᵐ y ∂μ.restrict A, g y = c) :
    ∃ c : ℝ, ∀ᵐ x ∂μ.restrict D, g x = c := by
  classical
  choose A hAo hxA c hc using fun x : D ↦ hloc x x.2
  have hlc : IsLocallyConstant c := by
    apply (IsLocallyConstant.iff_eventually_eq c).mpr
    intro x
    have hn : ∀ᶠ y : D in 𝓝 x, (y : X) ∈ A x :=
      continuous_subtype_val.continuousAt ((hAo x).mem_nhds (hxA x))
    filter_upwards [hn] with y hy
    exact eq_of_ae_eq_const_on_open_inter (hAo y) (hAo x)
      ⟨y, hxA y, hy⟩ (hc y) (hc x)
  let : PreconnectedSpace D := isPreconnected_iff_preconnectedSpace.mp hD
  obtain ⟨c₀, hconst⟩ := hlc.exists_eq_const
  have hcover : D ⊆ ⋃ x : D, A x := fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hxA ⟨x, hx⟩⟩
  obtain ⟨T, hTc, hTD⟩ := (HereditarilyLindelofSpace.isLindelof D).elim_countable_subcover
    A hAo hcover
  refine ⟨c₀, ae_restrict_of_ae_restrict_of_subset hTD ?_⟩
  apply (ae_restrict_biUnion_iff A hTc (fun x ↦ g x = c₀)).mpr
  intro x _
  have hcx : c x = c₀ := congrFun hconst x
  simpa only [hcx] using hc x

namespace Varifold
variable {U M : Set (Euclidean N)}

/-- Chart volume constancy becomes local Hausdorff constancy on the
actual carrier, including all parts of the carrier in the neighborhood. -/
theorem Stationary.exists_density_ae_eq_const_nhds
    {V : Varifold N n U} (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M)
    {x : Euclidean N} (hxM : x ∈ M) (hxU : x ∈ U) :
    ∃ A : Set (Euclidean N), IsOpen A ∧ x ∈ A ∧ A ⊆ U ∧
      ∃ c : ℝ, ∀ᵐ y ∂(Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict (A ∩ M),
        V.constancyDensity M y = c := by
  obtain ⟨D, W, φ, hxW, hφ⟩ := hSM.exists_localRepresentation hxM
  obtain ⟨a, ha, rfl⟩ : x ∈ φ '' D := by rw [hφ.image_eq]; exact ⟨hxW, hxM⟩
  obtain ⟨B, hBo, haB, hBD, c, hc⟩ :=
    hV.exists_chart_density_ae_eq_const_nhds hSM hM hφ ha hxU
  obtain ⟨A, hAo, _, hA⟩ := hφ.exists_open_image_eq_inter hBo (hBD.trans inter_subset_left)
  have haA : φ a ∈ A := by
    have h : φ a ∈ φ '' B := mem_image_of_mem φ haB
    rw [hA] at h
    exact h.1
  have hctrans := ae_simonHausdorff_chart_image_of_ae_volume hφ hBo.measurableSet
    (hBD.trans inter_subset_left)
    (hV.constancyDensity_representation hSM hM).1 hc
  rw [hA] at hctrans
  refine ⟨A ∩ U, hAo.inter V.isOpen_domain, ⟨haA, hxU⟩, inter_subset_right, c,
    ae_restrict_of_ae_restrict_of_subset ?_ hctrans⟩
  exact fun y hy ↦ ⟨hy.1.1, hy.2⟩

/-- The genuine density has one a.e. value on every connected subset
of the carrier subtype lying in the actual varifold domain. In
particular this applies to each connected component separately. -/
theorem Stationary.density_ae_eq_const_on_preconnected_carrier
    {V : Varifold N n U} (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M)
    {C : Set M} (hC : IsPreconnected C)
    (hCU : C ⊆ ((↑) : M → Euclidean N) ⁻¹' U) :
    ∃ c : ℝ, ∀ᵐ (x : M) ∂(simonManifoldMeasure n M).restrict C,
      V.constancyDensity M (x : Euclidean N) = c := by
  let : (simonManifoldMeasure n M).IsOpenPosMeasure := isOpenPosMeasure_simonManifoldMeasure hSM
  have hMm := simonSubmanifold_measurableSet hSM
  apply ae_eq_const_of_locally_ae_eq_const_near hC
  intro x hx
  obtain ⟨A, hAo, hxA, _, c, hc⟩ :=
    hV.exists_density_ae_eq_const_nhds hSM hM x.property (hCU hx)
  refine ⟨((↑) : M → Euclidean N) ⁻¹' A, hAo.preimage continuous_subtype_val,
    hxA, c, ?_⟩
  have hc' : ∀ᵐ y ∂((Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict A).restrict M,
      V.constancyDensity M y = c := by
    rw [Measure.restrict_restrict hMm, inter_comm]
    exact hc
  have hsub := (ae_restrict_iff_subtype hMm).mp hc'
  rw [(MeasurableEmbedding.subtype_coe hMm).comap_restrict] at hsub
  exact hsub

/-- Componentwise constancy does not identify constants belonging to
different components of `M ∩ U`. -/
theorem Stationary.density_ae_eq_const_on_carrier_component
    {V : Varifold N n U} (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M) (x : M) :
    ∃ c : ℝ, ∀ᵐ (y : M) ∂(simonManifoldMeasure n M).restrict
        (connectedComponentIn (((↑) : M → Euclidean N) ⁻¹' U) x),
      V.constancyDensity M (y : Euclidean N) = c :=
  hV.density_ae_eq_const_on_preconnected_carrier hSM hM isPreconnected_connectedComponentIn
    (connectedComponentIn_subset _ _)

/-- The corrected connectedness hypothesis gives one Hausdorff-a.e.
constant on the actual carrier `M ∩ U`, in arbitrary codimension. -/
theorem Stationary.density_ae_eq_const_of_connected_domain_carrier
    {V : Varifold N n U} (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M) (hconn : IsPreconnected (M ∩ U)) :
    ∃ c : ℝ, ∀ᵐ x ∂(Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict (M ∩ U),
      V.constancyDensity M x = c := by
  have hMm := simonSubmanifold_measurableSet hSM
  have hC : IsPreconnected (((↑) : M → Euclidean N) ⁻¹' U) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    simpa only [Subtype.image_preimage_coe, inter_comm] using hconn
  obtain ⟨c, hc⟩ := hV.density_ae_eq_const_on_preconnected_carrier hSM hM hC Subset.rfl
  change ∀ᵐ (x : M) ∂((Chapter01.simonHausdorffMeasureReal (n : ℝ)).comap
    ((↑) : M → Euclidean N)).restrict (((↑) : M → Euclidean N) ⁻¹' U),
      V.constancyDensity M (x : Euclidean N) = c at hc
  rw [← (MeasurableEmbedding.subtype_coe hMm).comap_restrict] at hc
  have h := (ae_restrict_iff_subtype
    (μ := (Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict U)
    (p := fun y ↦ V.constancyDensity M y = c) hMm).mpr hc
  rw [Measure.restrict_restrict hMm] at h
  exact ⟨c, h⟩

end Varifold
end
end Poincare.SimonGMT.Chapter08
