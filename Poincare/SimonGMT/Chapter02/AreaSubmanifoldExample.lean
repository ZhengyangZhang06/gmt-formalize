module

public import Poincare.SimonGMT.Chapter02.AreaLiteral
public import Poincare.SimonGMT.Chapter02.AreaParametrization
public import Mathlib.Topology.Compactness.Lindelof
import all Poincare.SimonGMT.Chapter02.Submanifold

@[expose] public section

/-!
# Simon (3.6)(2): Riemannian volume of an embedded submanifold

The volume is constructed by integrating the square root of the determinant
of the induced metric in local coordinates. A countable atlas is extracted
from Simon's submanifold hypothesis; its disjoint target pieces are then
glued as measures. The resulting measure is proved independent of the atlas
and equal to ambient Hausdorff measure restricted to the submanifold. It is
not defined to be Hausdorff measure, nor is any area identity a hypothesis.
-/

open Function MeasureTheory Module Set
open scoped ENNReal NNReal

namespace Poincare.SimonGMT.Chapter02
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]

/-- The usual Riemannian coordinate density `sqrt(det(gᵢⱼ))`, where
`gᵢⱼ = Dᵢφ · Dⱼφ` is the induced metric. -/
def chartMetricDensity (φ : E → F) (x : E) : ℝ :=
  Real.sqrt (Matrix.gram ℝ
    (fun i ↦ fderiv ℝ φ x (stdOrthonormalBasis ℝ E i))).det

theorem chartMetricDensity_eq_areaJacobianAt (φ : E → F) (x : E) :
    chartMetricDensity φ x = areaJacobianAt φ x :=
  (areaJacobianAt_eq_sqrt_det_gram φ x (stdOrthonormalBasis ℝ E)).symm

/-- The usual coordinate construction of Riemannian volume in a chart. -/
def chartRiemannianVolume (D : Set E) (φ : E → F) : Measure F :=
  Measure.map φ ((volume.restrict D).withDensity
    (fun x ↦ ENNReal.ofReal (chartMetricDensity φ x)))

/-- Local identification of coordinate Riemannian volume with ambient
Hausdorff measure. -/
theorem IsSimonLocalRepresentation.chartRiemannianVolume_eq
    {r : ℕ∞} {M W : Set F} {D : Set E} {φ : E → F}
    (h : IsSimonLocalRepresentation r M D W φ) (hr : 1 ≤ r) :
    chartRiemannianVolume D φ =
      (Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ)).restrict (W ∩ M) := by
  have hd : ∀ x ∈ D, DifferentiableAt ℝ φ x := fun x hx ↦
    (h.contDiffOn.differentiableOn (by exact_mod_cast (ne_of_gt
      (lt_of_lt_of_le (show (0 : ℕ∞) < 1 by simp) hr))) x hx).differentiableAt
        (h.isOpen_source.mem_nhds hx)
  simp only [chartRiemannianVolume, chartMetricDensity_eq_areaJacobianAt]
  rw [simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, ← h.image_eq,
    ← InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := E)]
  exact map_withDensity_areaJacobian_eq h.isOpen_source.measurableSet hd
    (fun _ hx ↦ h.injective_fderiv hx) h.injOn

/-- Simon's local chart formula in precisely the induced-metric determinant
form, on every Borel subset of the parameter domain. -/
theorem IsSimonLocalRepresentation.area_formula_metric
    {r : ℕ∞} {M W : Set F} {D s : Set E} {φ : E → F}
    (h : IsSimonLocalRepresentation r M D W φ) (hr : 1 ≤ r)
    (hs : MeasurableSet s) (hsD : s ⊆ D) :
    Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) (φ '' s) =
      ∫⁻ x in s, ENNReal.ofReal (chartMetricDensity φ x) ∂volume := by
  simp only [chartMetricDensity_eq_areaJacobianAt,
    simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure]
  exact h.area_formula hr hs hsD

/-- A countable atlas of actual Simon local representations. -/
structure SimonVolumeAtlas (r : ℕ∞) (M : Set F) where
  regularity : 1 ≤ r
  source : ℕ → Set E
  target : ℕ → Set F
  parametrization : ℕ → E → F
  representation : ∀ i, IsSimonLocalRepresentation r M (source i) (target i) (parametrization i)
  covers : M ⊆ ⋃ i, target i

/-- The countable atlas is obtained from second countability, not postulated
as an additional assumption on the submanifold. Empty manifolds are included. -/
theorem IsSimonSubmanifold.nonempty_volumeAtlas
    {r : ℕ∞} {M : Set F} (h : IsSimonSubmanifold (E := E) r M) :
    Nonempty (SimonVolumeAtlas (E := E) r M) := by
  classical
  rcases M.eq_empty_or_nonempty with rfl | hM
  · refine ⟨⟨h.1, fun _ ↦ ∅, fun _ ↦ ∅, fun _ _ ↦ 0, ?_, by simp⟩⟩
    intro i
    simp [IsSimonLocalRepresentation, IsProperOnInto]
  · let : Nonempty M := hM.to_subtype
    choose D W φ hy hrep using fun y : M ↦ h.exists_localRepresentation y.property
    obtain ⟨j, hj⟩ := (HereditarilyLindelofSpace.isLindelof M).indexed_countable_subcover
      W (fun y ↦ (hrep y).isOpen_target) (fun y hyM ↦ mem_iUnion.mpr ⟨⟨y, hyM⟩, hy _⟩)
    exact ⟨⟨h.1, D ∘ j, W ∘ j, φ ∘ j, fun i ↦ hrep (j i), hj⟩⟩

namespace SimonVolumeAtlas

variable {r : ℕ∞} {M : Set F} (a : SimonVolumeAtlas (E := E) r M)

/-- Global Riemannian volume: glue the coordinate-density measures on
disjoint pieces of the countable ambient chart cover. -/
def volume : Measure F :=
  Measure.sum fun i ↦ (chartRiemannianVolume (a.source i) (a.parametrization i)).restrict
    (disjointed a.target i)

/-- The global coordinate construction agrees with Hausdorff measure.
The proof performs the countable disjoint-chart gluing. -/
theorem volume_eq_hausdorff :
    a.volume = (Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ)).restrict M := by
  have hd (i : ℕ) : MeasurableSet (disjointed a.target i) :=
    MeasurableSet.disjointed (fun i ↦ (a.representation i).isOpen_target.measurableSet) i
  have he (i : ℕ) :
      (chartRiemannianVolume (a.source i) (a.parametrization i)).restrict
          (disjointed a.target i) =
        ((Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ)).restrict M).restrict
          (disjointed a.target i) := by
    rw [(a.representation i).chartRiemannianVolume_eq a.regularity,
      Measure.restrict_restrict (hd i), Measure.restrict_restrict (hd i)]
    congr 1
    exact Set.ext fun x ↦ by
      simp only [mem_inter_iff]
      exact ⟨fun hx ↦ ⟨hx.1, hx.2.2⟩,
        fun hx ↦ ⟨hx.1, disjointed_subset a.target i hx.1, hx.2⟩⟩
  simp only [volume, he]
  rw [← Measure.restrict_iUnion (disjoint_disjointed a.target) hd, iUnion_disjointed,
    Measure.restrict_restrict (MeasurableSet.iUnion
      (fun i ↦ (a.representation i).isOpen_target.measurableSet)),
    inter_eq_right.mpr a.covers]

/-- In particular the coordinate-volume construction is independent of
all atlas and disjoint-partition choices. -/
theorem volume_eq (b : SimonVolumeAtlas (E := E) r M) : a.volume = b.volume := by
  rw [a.volume_eq_hausdorff, b.volume_eq_hausdorff]

/-- Simon (3.6)(2) on every subset of the manifold, hence in particular on
all Borel and all completed-Hausdorff-measurable subsets. -/
theorem volume_apply {A : Set F} (hA : A ⊆ M) :
    a.volume A = Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) A := by
  rw [a.volume_eq_hausdorff]
  exact Measure.restrict_eq_self _ hA

end SimonVolumeAtlas

/-- Riemannian volume of a Simon submanifold, constructed from the induced
metric in coordinates and a countable atlas selected from its definition. -/
def IsSimonSubmanifold.riemannianVolume
    {r : ℕ∞} {M : Set F} (h : IsSimonSubmanifold (E := E) r M) : Measure F :=
  (Classical.choice h.nonempty_volumeAtlas).volume

theorem IsSimonSubmanifold.riemannianVolume_eq_hausdorff
    {r : ℕ∞} {M : Set F} (h : IsSimonSubmanifold (E := E) r M) :
    h.riemannianVolume =
      (Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ)).restrict M :=
  (Classical.choice h.nonempty_volumeAtlas).volume_eq_hausdorff

/-- The full global volume equality in Simon's submanifold example. -/
theorem IsSimonSubmanifold.riemannianVolume_apply
    {r : ℕ∞} {M A : Set F} (h : IsSimonSubmanifold (E := E) r M) (hA : A ⊆ M) :
    h.riemannianVolume A = Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) A := by
  rw [h.riemannianVolume_eq_hausdorff]
  exact Measure.restrict_eq_self _ hA

end
end Poincare.SimonGMT.Chapter02
