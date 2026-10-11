module

public import Poincare.SimonGMT.Chapter02.AreaLiteral
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-!
# Simon (6.1): projection coarea, with actual Hausdorff slice measures

Fubini is transported through the Euclidean Hilbert product. Each vertical
slice is identified isometrically with its fiber space, so the inner measure
is the ambient Hausdorff measure required by Simon, not an abstract kernel.
Both completed-measurable sets and nonnegative completed-measurable weights
are covered, with the literal normalization.
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

/-- The affine isometry identifying a projection fiber with its Euclidean
fiber space. -/
def projectionFiberEmbedding (y : E) (z : F) : WithLp 2 (E × F) :=
  WithLp.toLp 2 (y, z)

theorem isometry_projectionFiberEmbedding (y : E) :
    Isometry (projectionFiberEmbedding (F := F) y) := by
  apply Isometry.of_dist_eq
  intro z w
  simp only [dist_eq_norm, projectionFiberEmbedding, ← WithLp.toLp_sub,
    Prod.mk_sub_mk, sub_self, WithLp.norm_toLp_snd]

theorem range_projectionFiberEmbedding (y : E) :
    range (projectionFiberEmbedding (F := F) y) = {p | WithLp.fst p = y} := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    rfl
  · intro hp
    refine ⟨p.snd, ?_⟩
    change WithLp.toLp 2 (y, p.snd) = p
    rw [← hp]
    rfl

/-- The Hausdorff measure of every actual vertical slice is the volume of
its coordinate preimage; no measurability of this individual slice is needed. -/
theorem projection_slice_hausdorff_eq_volume (A : Set (WithLp 2 (E × F))) (y : E) :
    Chapter01.simonHausdorffMeasureReal (finrank ℝ F : ℝ)
        (A ∩ {p | WithLp.fst p = y}) =
      volume ((projectionFiberEmbedding (F := F) y) ⁻¹' A) := by
  rw [simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure,
    ← range_projectionFiberEmbedding]
  simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
    ((isometry_projectionFiberEmbedding (F := F) y).euclideanHausdorffMeasure_preimage
      (d := finrank ℝ F) A).symm

/-- Simon (6.1), on the full Lebesgue-measurable source-set hypothesis. -/
theorem coarea_projection {A : Set (WithLp 2 (E × F))}
    (hA : NullMeasurableSet A volume) :
    (∫⁻ y : E, Chapter01.simonHausdorffMeasureReal (finrank ℝ F : ℝ)
      (A ∩ {p | WithLp.fst p = y}) ∂volume) =
        Chapter01.simonHausdorffMeasureReal (finrank ℝ (WithLp 2 (E × F)) : ℝ) A := by
  simp only [projection_slice_hausdorff_eq_volume,
    simonHausdorffMeasureReal_finrank_eq_volume]
  have ht : NullMeasurableSet ((WithLp.toLp 2) ⁻¹' A)
      ((volume : Measure E).prod (volume : Measure F)) :=
    hA.preimage (WithLp.volume_preserving_toLp E F).quasiMeasurePreserving
  change (∫⁻ y : E, volume (Prod.mk y ⁻¹' (WithLp.toLp 2 ⁻¹' A))) = volume A
  rw [← Measure.prod_apply₀ ht]
  exact (WithLp.volume_preserving_toLp E F).measure_preimage hA

/-- The measure-level identification of a projection fiber. -/
theorem map_volume_projectionFiberEmbedding (y : E) :
    Measure.map (projectionFiberEmbedding (F := F) y) volume =
      (Chapter01.simonHausdorffMeasureReal (finrank ℝ F : ℝ)).restrict
        {p | WithLp.fst p = y} := by
  rw [simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure,
    ← range_projectionFiberEmbedding,
    ← InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := F)]
  exact (isometry_projectionFiberEmbedding (F := F) y).map_euclideanHausdorffMeasure

/-- Integration on a projection fiber is genuine Hausdorff integration,
also for a target weight which is not separately known measurable on that fiber. -/
theorem lintegral_projectionFiber (g : WithLp 2 (E × F) → ℝ≥0∞) (y : E) :
    (∫⁻ p in {p | WithLp.fst p = y}, g p
      ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ F : ℝ)) =
        ∫⁻ z : F, g (projectionFiberEmbedding y z) ∂volume := by
  rw [← map_volume_projectionFiberEmbedding]
  exact (isometry_projectionFiberEmbedding (F := F) y).isClosedEmbedding.measurableEmbedding.lintegral_map g

/-- Weighted projection coarea, the projection case of Simon (6.6), for
nonnegative completed-measurable functions, including infinite values. -/
theorem coarea_projection_lintegral {g : WithLp 2 (E × F) → ℝ≥0∞}
    (hg : AEMeasurable g volume) :
    (∫⁻ p, g p ∂Chapter01.simonHausdorffMeasureReal
      (finrank ℝ (WithLp 2 (E × F)) : ℝ)) =
      ∫⁻ y : E, ∫⁻ p in {p | WithLp.fst p = y}, g p
        ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ F : ℝ) ∂volume := by
  simp only [lintegral_projectionFiber, simonHausdorffMeasureReal_finrank_eq_volume]
  rw [← (WithLp.volume_preserving_toLp E F).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (E × F)).measurableEmbedding g]
  exact lintegral_prod _ (hg.comp_quasiMeasurePreserving
    (WithLp.volume_preserving_toLp E F).quasiMeasurePreserving)

end
end Poincare.SimonGMT.Chapter02
