module

public import Poincare.SimonGMT.Chapter08.ConstancyChartVariation
public import Poincare.SimonGMT.Chapter08.DistributionalConstancy
public import Mathlib.Topology.Connected.LocallyConnected

@[expose] public section

/-!
# Corrected full-dimensional constancy on the actual open domain

For a stationary `N`-varifold in `ℝᴺ`, arbitrary scalar directional tests
are genuine compactly supported vector fields. Their first variations
give zero weak derivatives of the constructed volume density. Thus the
weight has constant multiplicity on every connected open subdomain of
the actual varifold domain. No connectedness of a larger carrier outside
the domain is used.

This is a complete full-dimensional specialization of the corrected
constancy theorem. It does not claim the missing curved, positive-
codimension coordinate-divergence identity.
-/

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {N : ℕ}

namespace Grassmannian

def fullDimensionalPlane (N : ℕ) : Grassmannian N N :=
  ofSubmodule ⊤ (by simp)

theorem plane_eq_top_of_fullDimension (S : Grassmannian N N) : S.plane = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  simpa using S.finrank_plane

theorem eq_fullDimensionalPlane (S : Grassmannian N N) : S = fullDimensionalPlane N := by
  apply eq_of_plane_eq
  rw [plane_eq_top_of_fullDimension, fullDimensionalPlane, plane_ofSubmodule]

end Grassmannian

/-- A full-dimensional Simon submanifold is open. The inverse-function
theorem is applied to the actual injective chart derivative; openness is
not added as an independent manifold hypothesis. -/
theorem isOpen_simonSubmanifold_fullDimension {M : Set (Euclidean N)}
    (hM : Chapter02.IsSimonSubmanifold (E := Euclidean N) 2 M) : IsOpen M := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨D, W, φ, hxW, hφ⟩ := hM.exists_localRepresentation hx
  obtain ⟨a, ha, rfl⟩ : x ∈ φ '' D := by rw [hφ.image_eq]; exact ⟨hxW, hx⟩
  have hφa : ContDiffAt ℝ 2 φ a :=
    (hφ.contDiffOn a ha).contDiffAt (hφ.isOpen_source.mem_nhds ha)
  let e : Euclidean N ≃L[ℝ] Euclidean N :=
    (LinearEquiv.ofBijective (fderiv ℝ φ a).toLinearMap
      ⟨hφ.injective_fderiv ha, LinearMap.surjective_of_injective
        (hφ.injective_fderiv ha)⟩).toContinuousLinearEquiv
  have hd : HasStrictFDerivAt φ e.toContinuousLinearMap a :=
    hφa.hasStrictFDerivAt (by norm_num)
  rw [← hd.map_nhds_eq_of_equiv]
  change φ ⁻¹' M ∈ 𝓝 a
  apply Filter.mem_of_superset (hφ.isOpen_source.mem_nhds ha)
  intro u hu
  have hi : φ u ∈ φ '' D := mem_image_of_mem φ hu
  rw [hφ.image_eq] at hi
  exact hi.2

namespace Varifold
variable {U W : Set (Euclidean N)}

/-- The actual Radon--Nikodym volume density; no density is supplied as
a premise. -/
def ambientVolumeDensity (V : Varifold N N U) (x : Euclidean N) : ℝ :=
  (V.weight.rnDeriv volume x).toReal

theorem Stationary.weight_absolutelyContinuous_volume_of_fullDimension
    {V : Varifold N N U} (hV : V.Stationary) : V.weight ≪ volume := by
  have h := hV.weight_absolutelyContinuous_simonHausdorff
  have he : (Chapter01.simonHausdorffMeasureReal (N : ℝ) : Measure (Euclidean N)) =
      Chapter02.simonAreaNormalization N • volume := by
    simpa using Chapter02.simonHausdorffMeasureReal_source_eq_smul_volume (E := Euclidean N)
  rw [he] at h
  exact h.trans Measure.smul_absolutelyContinuous

theorem Stationary.ambientVolumeDensity_representation {V : Varifold N N U}
    (hV : V.Stationary) :
    Measurable V.ambientVolumeDensity ∧ (∀ x, 0 ≤ V.ambientVolumeDensity x) ∧
      LocallyIntegrableOn V.ambientVolumeDensity U volume ∧
      volume.withDensity (fun x ↦ ENNReal.ofReal (V.ambientVolumeDensity x)) = V.weight := by
  refine ⟨(Measure.measurable_rnDeriv _ _).ennreal_toReal,
    fun _ ↦ ENNReal.toReal_nonneg, ?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.mp (V.isOpen_domain.mem_nhds hx)
    refine ⟨closedBall x r, mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x hr), ?_⟩
    exact Measure.integrableOn_toReal_rnDeriv
      (V.weight_finite_on_compact _ (isCompact_closedBall x r) hrU)
  · change volume.withDensity (fun x ↦ ENNReal.ofReal ((V.weight.rnDeriv volume x).toReal)) = _
    calc
      _ = volume.withDensity (V.weight.rnDeriv volume) := by
        apply withDensity_congr_ae
        filter_upwards [Measure.rnDeriv_ne_top V.weight volume] with x hx
        exact ENNReal.ofReal_toReal hx
      _ = V.weight := Measure.withDensity_rnDeriv_eq _ _
        hV.weight_absolutelyContinuous_volume_of_fullDimension

/-- Every compactly supported scalar test gives an actual admissible
directional vector-field test. -/
def directionalTest {η : Euclidean N → ℝ} (hη : ContDiff ℝ 1 η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (v : Euclidean N) :
    TestVectorField (N := N) U where
  toFun x := η x • v
  contDiff := hη.smul contDiff_const
  compactSupport := hc.smul_right
  support_subset := (tsupport_smul_subset_left η (fun _ : Euclidean N ↦ v)).trans hs

theorem tangentialDivergence_directionalTest {η : Euclidean N → ℝ}
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U)
    (v x : Euclidean N) (S : Grassmannian N N) :
    tangentialDivergence (directionalTest hη hc hs v) x S = fderiv ℝ η x v := by
  have hd : fderiv ℝ (directionalTest hη hc hs v) x = (fderiv ℝ η x).smulRight v :=
    ((hη.differentiable_one x).hasFDerivAt.smul_const v).fderiv
  rw [tangentialDivergence_eq_trace]
  simp only [Grassmannian.plane_eq_top_of_fullDimension, Submodule.starProjection_top,
    ContinuousLinearMap.coe_id, LinearMap.comp_id, hd]
  exact LinearMap.trace_smulRight _ _

theorem firstVariation_directionalTest (V : Varifold N N U)
    {η : Euclidean N → ℝ} (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ U) (v : Euclidean N) :
    V.firstVariation (directionalTest hη hc hs v) = ∫ x, fderiv ℝ η x v ∂V.weight := by
  rw [firstVariation]
  simp_rw [tangentialDivergence_directionalTest]
  rw [weight]
  symm
  apply integral_map measurable_fst.aemeasurable
  exact ((hη.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable

/-- Stationarity supplies all weak directional derivatives, not only a
restricted family of tests and not an assumed weak equation. -/
theorem Stationary.ambientVolumeDensity_weakDerivativesZero {V : Varifold N N U}
    (hV : V.Stationary) : WeakDerivativesZero V.ambientVolumeDensity U := by
  intro η hη hc hs v
  change (∫ x, (V.weight.rnDeriv volume x).toReal * fderiv ℝ η x v) = 0
  rw [integral_toReal_rnDeriv_mul hV.weight_absolutelyContinuous_volume_of_fullDimension,
    ← V.firstVariation_directionalTest hη hc hs v]
  exact hV (directionalTest hη hc hs v)

/-- Analytic constancy applies on the actual connected open subdomain.
No relation between its connectedness and that of a larger carrier is
presupposed. -/
theorem Stationary.ambientVolumeDensity_ae_eq_const {V : Varifold N N U}
    (hV : V.Stationary) (hW : IsOpen W) (hconn : IsPreconnected W) (hWU : W ⊆ U) :
    ∃ c : ℝ, ∀ᵐ x ∂volume.restrict W, V.ambientVolumeDensity x = c := by
  exact (hV.ambientVolumeDensity_weakDerivativesZero.mono hWU).ae_eq_const
    (hV.ambientVolumeDensity_representation.2.2.1.mono_set hWU) hW hconn

/-- A complete measure-level constancy result on every connected open
subdomain, with finite nonnegative multiplicity. -/
theorem Stationary.exists_weight_restrict_eq_const_volume_of_fullDimension
    {V : Varifold N N U} (hV : V.Stationary)
    (hW : IsOpen W) (hconn : IsPreconnected W) (hWU : W ⊆ U) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ V.weight.restrict W = c • volume.restrict W := by
  obtain ⟨c, hc⟩ := hV.ambientVolumeDensity_ae_eq_const hW hconn hWU
  refine ⟨ENNReal.ofReal c, ENNReal.ofReal_ne_top, ?_⟩
  rw [← hV.ambientVolumeDensity_representation.2.2.2, restrict_withDensity hW.measurableSet]
  calc
    _ = (volume.restrict W).withDensity (fun _ ↦ ENNReal.ofReal c) := by
      apply withDensity_congr_ae
      filter_upwards [hc] with x hx
      exact congrArg ENNReal.ofReal hx
    _ = _ := withDensity_const _

/-- The same complete local constancy statement for Simon's literal
Hausdorff measure. Conversion divides by the proved positive finite
normalization scalar; that scalar is not assumed to equal one. -/
theorem Stationary.exists_weight_restrict_eq_const_simonHausdorff_of_fullDimension
    {V : Varifold N N U} (hV : V.Stationary)
    (hW : IsOpen W) (hconn : IsPreconnected W) (hWU : W ⊆ U) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ V.weight.restrict W =
      c • (Chapter01.simonHausdorffMeasureReal (N : ℝ)).restrict W := by
  obtain ⟨c, hc, heq⟩ := hV.exists_weight_restrict_eq_const_volume_of_fullDimension hW hconn hWU
  have hk0 := (Chapter02.simonAreaNormalization_pos N).ne'
  have hk_top := Chapter02.simonAreaNormalization_ne_top N
  have hnorm : (Chapter01.simonHausdorffMeasureReal (N : ℝ) : Measure (Euclidean N)) =
      Chapter02.simonAreaNormalization N • volume := by
    simpa using Chapter02.simonHausdorffMeasureReal_source_eq_smul_volume (E := Euclidean N)
  refine ⟨c / Chapter02.simonAreaNormalization N, ENNReal.div_ne_top hc hk0, ?_⟩
  rw [hnorm, Measure.restrict_smul, smul_smul, ENNReal.div_mul_cancel hk0 hk_top]
  exact heq

/-- Without any connectedness assumption on the open domain, each
actual connected component has its own finite constant multiplicity. -/
theorem Stationary.exists_weight_connectedComponent_eq_const_simonHausdorff
    {V : Varifold N N U} (hV : V.Stationary) (x : Euclidean N) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ V.weight.restrict (connectedComponentIn U x) =
      c • (Chapter01.simonHausdorffMeasureReal (N : ℝ)).restrict (connectedComponentIn U x) :=
  hV.exists_weight_restrict_eq_const_simonHausdorff_of_fullDimension
    V.isOpen_domain.connectedComponentIn isPreconnected_connectedComponentIn
    (connectedComponentIn_subset U x)

/-- The full-dimensional bundle measure is determined by the actual
weight without any additional tangent-graph premise. -/
theorem measure_eq_fullDimensionalGraph (V : Varifold N N U) :
    V.measure = V.weight.map (fun x ↦ (x, Grassmannian.fullDimensionalPlane N)) := by
  apply V.measure_eq_map_tangentGraph _ measurable_const
  exact Eventually.of_forall (fun z ↦ Grassmannian.eq_fullDimensionalPlane z.2)

/-- The corrected full-dimensional constancy theorem on a connected
actual varifold domain, including the entire Grassmann-bundle measure. -/
theorem Stationary.exists_const_volume_fullDimensionalGraph {V : Varifold N N U}
    (hV : V.Stationary) (hconn : IsPreconnected U) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ V.measure =
      (c • volume.restrict U).map (fun x ↦ (x, Grassmannian.fullDimensionalPlane N)) := by
  obtain ⟨c, hc, heq⟩ := hV.exists_weight_restrict_eq_const_volume_of_fullDimension
    V.isOpen_domain hconn Subset.rfl
  have hU : ∀ᵐ x ∂V.weight, x ∈ U := by
    rw [ae_iff]
    change V.weight Uᶜ = 0
    rw [V.weight_apply V.isOpen_domain.measurableSet.compl]
    exact V.supported
  rw [Measure.restrict_eq_self_of_ae_mem hU] at heq
  exact ⟨c, hc, V.measure_eq_fullDimensionalGraph.trans (congrArg
    (fun μ : Measure (Euclidean N) ↦ μ.map
      (fun x ↦ (x, Grassmannian.fullDimensionalPlane N))) heq)⟩

/-- A source-faithful corrected constancy theorem in full dimension:
the connectedness belongs to `M ∩ U`, with `M ⊆ U` neither assumed nor
silently inferred. Manifold openness and the concentration on `M ∩ U`
are both derived from the displayed hypotheses. -/
theorem Stationary.exists_const_simonHausdorff_fullDimensionalCarrier
    {V : Varifold N N U} (hV : V.Stationary) {M : Set (Euclidean N)}
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean N) 2 M)
    (hM : U ∩ V.weight.support ⊆ M) (hconn : IsPreconnected (M ∩ U)) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ V.measure =
      (c • (Chapter01.simonHausdorffMeasureReal (N : ℝ)).restrict (M ∩ U)).map
        (fun x ↦ (x, Grassmannian.fullDimensionalPlane N)) := by
  have hA := (isOpen_simonSubmanifold_fullDimension hSM).inter V.isOpen_domain
  obtain ⟨c, hc, heq⟩ := hV.exists_weight_restrict_eq_const_simonHausdorff_of_fullDimension
    hA hconn inter_subset_right
  have hMA : U ∩ V.weight.support ⊆ M ∩ U := fun _ hx ↦ ⟨hM hx, hx.1⟩
  have hAa : ∀ᵐ x ∂V.weight, x ∈ M ∩ U :=
    (hV.weight_absolutelyContinuous_carrier hMA).ae_le (ae_restrict_mem hA.measurableSet)
  rw [Measure.restrict_eq_self_of_ae_mem hAa] at heq
  exact ⟨c, hc, V.measure_eq_fullDimensionalGraph.trans (congrArg
    (fun μ : Measure (Euclidean N) ↦ μ.map
      (fun x ↦ (x, Grassmannian.fullDimensionalPlane N))) heq)⟩

/-- The alternative explicit repair `M ⊆ U` allows connectedness of
`M` itself, again with the full literal Hausdorff graph measure. -/
theorem Stationary.exists_const_simonHausdorff_fullDimensionalCarrier_of_subset
    {V : Varifold N N U} (hV : V.Stationary) {M : Set (Euclidean N)}
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean N) 2 M)
    (hM : U ∩ V.weight.support ⊆ M) (hMU : M ⊆ U) (hconn : IsPreconnected M) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ V.measure =
      (c • (Chapter01.simonHausdorffMeasureReal (N : ℝ)).restrict M).map
        (fun x ↦ (x, Grassmannian.fullDimensionalPlane N)) := by
  simpa only [inter_eq_left.mpr hMU] using
    hV.exists_const_simonHausdorff_fullDimensionalCarrier hSM hM
      (by simpa only [inter_eq_left.mpr hMU] using hconn)

end Varifold
end
end Poincare.SimonGMT.Chapter08
