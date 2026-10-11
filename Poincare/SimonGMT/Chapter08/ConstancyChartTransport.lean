module

public import Poincare.SimonGMT.Chapter08.ConstancyNormalCharts
public import Poincare.SimonGMT.Chapter08.ConstancyHausdorffDensity
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-!
# Local bi-Lipschitz transport for Simon's actual charts

The inverse-function coordinate left inverse gives a genuine local
bi-Lipschitz parametrization in arbitrary codimension. Relative properness
identifies its image with the entire local carrier. Both directions of
the Hausdorff measure comparison and null-set transport are proved for
every subset of the smaller parameter domain.

The genuine chart pullback weight is proved sigma-finite and absolutely
continuous with respect to source volume, so its measurable nonnegative
coordinate density is constructed by Radon--Nikodym. This does not identify
the nonlinear Jacobian density, and hence does not assert the missing
nonlinear area formula or coordinate weak first-variation transport in
Simon (8.4.1).
-/

open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {N n : ℕ}

/-- A genuine Simon parametrization is a measurable embedding on its
source domain. Relative properness supplies the closed embedding into
the open ambient chart. -/
theorem measurableEmbedding_simonChart
    {M W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ) :
    MeasurableEmbedding (fun u : D ↦ φ u) := by
  have he : Topology.IsClosedEmbedding hφ.chartMap :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      hφ.continuous_chartMap hφ.injective_chartMap hφ.isProperMap_chartMap.isClosedMap
  exact (MeasurableEmbedding.subtype_coe hφ.isOpen_target.measurableSet).comp
    he.measurableEmbedding

/-- Simon's actual representation is locally bi-Lipschitz, with a
`C²` ambient left inverse constructed by the inverse function theorem.
The target neighborhood captures the whole local carrier. -/
theorem exists_local_biLipschitz_chart
    {M W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    {a : Euclidean n} (ha : a ∈ D) :
    ∃ (D₀ : Set (Euclidean n)) (W₀ : Set (Euclidean N))
      (ψ : Euclidean N → Euclidean n) (K L : ℝ≥0),
      IsOpen D₀ ∧ a ∈ D₀ ∧ D₀ ⊆ D ∧
      IsOpen W₀ ∧ W₀ ⊆ W ∧ φ '' D₀ = W₀ ∩ M ∧
      ContDiffAt ℝ 2 ψ (φ a) ∧ LeftInvOn ψ φ D₀ ∧
      LipschitzOnWith K φ D₀ ∧ LipschitzOnWith L ψ (φ '' D₀) := by
  have hφa : ContDiffAt ℝ 2 φ a :=
    (hφ.contDiffOn a ha).contDiffAt (hφ.isOpen_source.mem_nhds ha)
  obtain ⟨ψ, hψ, _, hleft, _⟩ :=
    exists_local_coordinate_leftInverse hφa (hφ.injective_fderiv ha)
  obtain ⟨K, B, hB, hφB⟩ := (hφa.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).exists_lipschitzOnWith
  obtain ⟨L, C, hC, hψC⟩ := (hψ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).exists_lipschitzOnWith
  have hnhds : D ∩ B ∩ φ ⁻¹' C ∩ {u | ψ (φ u) = u} ∈ 𝓝 a :=
    inter_mem (inter_mem (inter_mem (hφ.isOpen_source.mem_nhds ha) hB)
      (hφa.continuousAt hC)) hleft
  obtain ⟨D₀, hD₀, hD₀o, haD₀⟩ := mem_nhds_iff.mp hnhds
  have hD₀D : D₀ ⊆ D := fun u hu ↦ (hD₀ hu).1.1.1
  obtain ⟨W₀, hW₀, hW₀W, himage⟩ := hφ.exists_open_image_eq_inter hD₀o hD₀D
  refine ⟨D₀, W₀, ψ, K, L, hD₀o, haD₀, hD₀D, hW₀, hW₀W,
    himage, hψ, (fun u hu ↦ (hD₀ hu).2),
    hφB.mono (fun u hu ↦ (hD₀ hu).1.1.2), ?_⟩
  apply hψC.mono
  rintro _ ⟨u, hu, rfl⟩
  exact (hD₀ hu).1.2

/-- Lipschitz image control for Simon's literal Gamma-normalized
Hausdorff measure, with the same normalization on source and target. -/
theorem simonHausdorffMeasureReal_image_le_of_lipschitzOn
    {φ : Euclidean n → Euclidean N} {A : Set (Euclidean n)}
    {K : ℝ≥0} (hφ : LipschitzOnWith K φ A) {d : ℝ} (hd : 0 ≤ d) :
    Chapter01.simonHausdorffMeasureReal d (φ '' A) ≤
      (K : ℝ≥0∞) ^ d * Chapter01.simonHausdorffMeasureReal d A := by
  have h := mul_le_mul_right (hφ.hausdorffMeasure_image_le hd)
    (Chapter01.realUnitBallVolume d / (2 : ℝ≥0∞) ^ d)
  simpa only [Chapter01.simonHausdorffMeasureReal, Measure.smul_apply,
    smul_eq_mul, mul_left_comm] using h

/-- Both measure inequalities hold on every subset of a chart with
a Lipschitz left inverse, without a measurability assumption on that subset. -/
theorem simonHausdorffMeasureReal_chart_bounds
    {D : Set (Euclidean n)} {φ : Euclidean n → Euclidean N}
    {ψ : Euclidean N → Euclidean n} {K L : ℝ≥0}
    (hφ : LipschitzOnWith K φ D) (hψ : LipschitzOnWith L ψ (φ '' D))
    (hleft : LeftInvOn ψ φ D) {A : Set (Euclidean n)} (hA : A ⊆ D)
    {d : ℝ} (hd : 0 ≤ d) :
    Chapter01.simonHausdorffMeasureReal d (φ '' A) ≤
        (K : ℝ≥0∞) ^ d * Chapter01.simonHausdorffMeasureReal d A ∧
      Chapter01.simonHausdorffMeasureReal d A ≤
        (L : ℝ≥0∞) ^ d * Chapter01.simonHausdorffMeasureReal d (φ '' A) := by
  refine ⟨simonHausdorffMeasureReal_image_le_of_lipschitzOn (hφ.mono hA) hd, ?_⟩
  have h := simonHausdorffMeasureReal_image_le_of_lipschitzOn
    (hψ.mono (image_mono hA)) hd
  rwa [hleft.image_image' hA] at h

/-- Local chart transport preserves and reflects Hausdorff null sets.
This is weaker than, and does not assume, the nonlinear area formula. -/
theorem simonHausdorffMeasureReal_chart_image_eq_zero_iff
    {D : Set (Euclidean n)} {φ : Euclidean n → Euclidean N}
    {ψ : Euclidean N → Euclidean n} {K L : ℝ≥0}
    (hφ : LipschitzOnWith K φ D) (hψ : LipschitzOnWith L ψ (φ '' D))
    (hleft : LeftInvOn ψ φ D) {A : Set (Euclidean n)} (hA : A ⊆ D)
    {d : ℝ} (hd : 0 ≤ d) :
    Chapter01.simonHausdorffMeasureReal d (φ '' A) = 0 ↔
      Chapter01.simonHausdorffMeasureReal d A = 0 := by
  obtain ⟨hupper, hlower⟩ := simonHausdorffMeasureReal_chart_bounds hφ hψ hleft hA hd
  constructor
  · intro h
    simpa only [h, mul_zero, nonpos_iff_eq_zero] using hlower
  · intro h
    simpa only [h, mul_zero, nonpos_iff_eq_zero] using hupper

/-- The literal Simon measure and Lebesgue volume have exactly the
same null sets in the source dimension. This uses Haar uniqueness and
positivity of Simon's normalization, not an unproved scalar-one formula. -/
theorem simonHausdorffMeasureReal_source_eq_zero_iff_volume
    (A : Set (Euclidean n)) :
    Chapter01.simonHausdorffMeasureReal (n : ℝ) A = 0 ↔ volume A = 0 := by
  let μ : Measure (Euclidean n) := Measure.hausdorffMeasure (n : ℝ)
  have hμvol : μ ≪ volume := Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have hvolμ : volume ≪ μ := Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have hc : Chapter01.realUnitBallVolume (n : ℝ) / (2 : ℝ≥0∞) ^ (n : ℝ) ≠ 0 :=
    ENNReal.div_ne_zero.mpr
      ⟨(Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)).ne', by simp⟩
  change (_ • μ) A = 0 ↔ volume A = 0
  rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero, or_iff_right hc]
  exact ⟨fun h ↦ hvolμ h, fun h ↦ hμvol h⟩

/-- The null-set equivalence is obtained from Simon's actual chart
hypotheses, including identification of the whole smaller carrier patch. -/
theorem exists_local_hausdorff_null_transport
    {M W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    {a : Euclidean n} (ha : a ∈ D) :
    ∃ (D₀ : Set (Euclidean n)) (W₀ : Set (Euclidean N)),
      IsOpen D₀ ∧ a ∈ D₀ ∧ D₀ ⊆ D ∧ IsOpen W₀ ∧ W₀ ⊆ W ∧
      φ '' D₀ = W₀ ∩ M ∧
      ∀ A ⊆ D₀, ∀ d : ℝ, 0 ≤ d →
        (Chapter01.simonHausdorffMeasureReal d (φ '' A) = 0 ↔
          Chapter01.simonHausdorffMeasureReal d A = 0) := by
  obtain ⟨D₀, W₀, ψ, K, L, hD₀, haD₀, hD₀D, hW₀, hW₀W, himage, _, hleft, hφL, hψL⟩ :=
    exists_local_biLipschitz_chart hφ ha
  refine ⟨D₀, W₀, hD₀, haD₀, hD₀D, hW₀, hW₀W, himage, ?_⟩
  intro A hA d hd
  exact simonHausdorffMeasureReal_chart_image_eq_zero_iff hφL hψL hleft hA hd

/-- Local nonlinear chart images preserve and reflect source-volume
null sets in arbitrary codimension. -/
theorem exists_local_volume_null_transport
    {M W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    {a : Euclidean n} (ha : a ∈ D) :
    ∃ (D₀ : Set (Euclidean n)) (W₀ : Set (Euclidean N)),
      IsOpen D₀ ∧ a ∈ D₀ ∧ D₀ ⊆ D ∧ IsOpen W₀ ∧ W₀ ⊆ W ∧
      φ '' D₀ = W₀ ∩ M ∧
      ∀ A ⊆ D₀,
        (Chapter01.simonHausdorffMeasureReal (n : ℝ) (φ '' A) = 0 ↔ volume A = 0) := by
  obtain ⟨D₀, W₀, hD₀, haD₀, hD₀D, hW₀, hW₀W, himage, hnull⟩ :=
    exists_local_hausdorff_null_transport hφ ha
  refine ⟨D₀, W₀, hD₀, haD₀, hD₀D, hW₀, hW₀W, himage, ?_⟩
  intro A hA
  exact (hnull A hA n (Nat.cast_nonneg n)).trans
    (simonHausdorffMeasureReal_source_eq_zero_iff_volume A)

namespace Varifold
variable {U M : Set (Euclidean N)}

/-- Pull the weight back along the actual chart embedding and extend
the resulting source-domain measure by zero. Its all-set evaluation law
is proved below, so the totalized `comap` is not being used without an
embedding certificate. -/
def chartWeight (V : Varifold N n U) (D : Set (Euclidean n))
    (φ : Euclidean n → Euclidean N) : Measure (Euclidean n) :=
  (V.weight.comap (fun u : D ↦ φ u)).map Subtype.val

/-- The coordinate weight evaluates to the weight of the exact image
of the source set. This holds even for nonmeasurable sets. -/
theorem chartWeight_apply (V : Varifold N n U)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    (A : Set (Euclidean n)) :
    V.chartWeight D φ A = V.weight (φ '' (A ∩ D)) := by
  rw [chartWeight,
    (MeasurableEmbedding.subtype_coe hφ.isOpen_source.measurableSet).map_apply,
    (measurableEmbedding_simonChart hφ).comap_apply]
  congr 1
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, ⟨hu, u.property⟩, rfl⟩
  · rintro ⟨u, ⟨huA, huD⟩, rfl⟩
    exact ⟨⟨u, huD⟩, huA, rfl⟩

/-- The stationary weight gives zero mass to the chart image of any
source volume-null set. The conclusion follows from the constructed
local Lipschitz chart and the proved stationary absolute continuity. -/
theorem Stationary.exists_local_chart_weight_null {V : Varifold N n U}
    (hV : V.Stationary)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    {a : Euclidean n} (ha : a ∈ D) :
    ∃ D₀ : Set (Euclidean n), IsOpen D₀ ∧ a ∈ D₀ ∧ D₀ ⊆ D ∧
      ∀ A ⊆ D₀, volume A = 0 →
        V.weight (φ '' A) = 0 := by
  obtain ⟨D₀, W₀, hD₀, haD₀, hD₀D, _, _, _, hnull⟩ :=
    exists_local_volume_null_transport hφ ha
  refine ⟨D₀, hD₀, haD₀, hD₀D, ?_⟩
  intro A hA hzero
  apply hV.weight_absolutelyContinuous_simonHausdorff
  exact (hnull A hA).mpr hzero

/-- The genuine chart pullback of a stationary weight is locally
absolutely continuous with respect to parameter-space volume. This
measure-level transport has no postulated Jacobian or density premise. -/
theorem Stationary.exists_local_chartWeight_absolutelyContinuous {V : Varifold N n U}
    (hV : V.Stationary)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    {a : Euclidean n} (ha : a ∈ D) :
    ∃ D₀ : Set (Euclidean n), IsOpen D₀ ∧ a ∈ D₀ ∧ D₀ ⊆ D ∧
      (V.chartWeight D φ).restrict D₀ ≪ volume := by
  obtain ⟨D₀, hD₀, haD₀, hD₀D, hnull⟩ := hV.exists_local_chart_weight_null hφ ha
  refine ⟨D₀, hD₀, haD₀, hD₀D, ?_⟩
  intro A hA
  rw [Measure.restrict_apply' hD₀.measurableSet, V.chartWeight_apply hφ,
    inter_assoc, inter_eq_left.mpr hD₀D]
  exact hnull (A ∩ D₀) inter_subset_right (measure_mono_null inter_subset_left hA)

/-- Countable localization upgrades the local chart transport to
absolute continuity of the entire coordinate weight. -/
theorem Stationary.chartWeight_absolutelyContinuous {V : Varifold N n U}
    (hV : V.Stationary)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ) :
    V.chartWeight D φ ≪ volume := by
  apply absolutelyContinuous_of_local_restrictions (D := D)
  · rw [ae_iff]
    change V.chartWeight D φ Dᶜ = 0
    rw [V.chartWeight_apply hφ, compl_inter_self, image_empty, measure_empty]
  · intro a ha
    obtain ⟨D₀, hD₀, haD₀, _, hD₀ac⟩ := hV.exists_local_chartWeight_absolutelyContinuous hφ ha
    exact ⟨D₀, hD₀, haD₀, hD₀ac⟩

/-- Sigma-finiteness of the coordinate weight follows from the genuine
measurable embedding and the varifold weight's sigma-finiteness. -/
theorem sigmaFinite_chartWeight (V : Varifold N n U)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ) :
    SigmaFinite (V.chartWeight D φ) := by
  have hf := measurableEmbedding_simonChart hφ
  let μ := V.weight.comap (fun u : D ↦ φ u)
  have hmap : SigmaFinite (μ.map (fun u : D ↦ φ u)) := by
    rw [show μ.map (fun u : D ↦ φ u) = V.weight.restrict (range (fun u : D ↦ φ u))
      from hf.map_comap V.weight]
    infer_instance
  let : SigmaFinite μ := SigmaFinite.of_map μ hf.measurable.aemeasurable hmap
  exact (MeasurableEmbedding.subtype_coe hφ.isOpen_source.measurableSet).sigmaFinite_map

/-- An actual coordinate density, defined as a Radon--Nikodym
derivative. Its identification with the geometric expression involving
the metric Jacobian is a separate, still missing area-formula step. -/
def chartDensity (V : Varifold N n U) (D : Set (Euclidean n))
    (φ : Euclidean n → Euclidean N) : Euclidean n → ℝ :=
  fun u ↦ ((V.chartWeight D φ).rnDeriv volume u).toReal

/-- The stationary chart weight has a constructed measurable
nonnegative source-volume density. No Jacobian identity is assumed. -/
theorem Stationary.chartDensity_representation {V : Varifold N n U}
    (hV : V.Stationary)
    {W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ) :
    Measurable (V.chartDensity D φ) ∧ (∀ u, 0 ≤ V.chartDensity D φ u) ∧
      volume.withDensity (fun u ↦ ENNReal.ofReal (V.chartDensity D φ u)) =
        V.chartWeight D φ := by
  let := V.sigmaFinite_chartWeight hφ
  refine ⟨(Measure.measurable_rnDeriv (V.chartWeight D φ) volume).ennreal_toReal,
    fun _ ↦ ENNReal.toReal_nonneg, ?_⟩
  calc
    volume.withDensity (fun u ↦ ENNReal.ofReal (V.chartDensity D φ u)) =
        volume.withDensity ((V.chartWeight D φ).rnDeriv volume) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_ne_top (V.chartWeight D φ) volume] with u hu
      exact ENNReal.ofReal_toReal hu
    _ = V.chartWeight D φ :=
      Measure.withDensity_rnDeriv_eq _ _ (hV.chartWeight_absolutelyContinuous hφ)

end Varifold
end
end Poincare.SimonGMT.Chapter08
