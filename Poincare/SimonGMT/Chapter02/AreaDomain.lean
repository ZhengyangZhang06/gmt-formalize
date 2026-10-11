module

public import Poincare.SimonGMT.Chapter02.AreaCompletion

@[expose] public section

/-!
# Area formula on the actual Lipschitz domain

No behavior of the map off its stated source domain is required. A
global Lipschitz extension is constructed by coordinatewise real-valued
extension. Its derivative is proved to agree almost everywhere with the
actual within derivative, using density-point uniqueness. Thus neither
the extension nor its Jacobian is supplied as a hypothesis.
-/

open Function MeasureTheory Module Set Filter
open scoped ENNReal NNReal Topology

namespace Poincare.SimonGMT.Chapter02
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]

/-- Simon's Jacobian on a source-only domain uses the within derivative,
and is therefore independent of arbitrary values outside that domain. -/
def areaJacobianWithin (f : E → F) (s : Set E) (x : E) : ℝ :=
  (fderivWithin ℝ f s x).normDet

/-- A global Lipschitz extension is constructed. Its constant need not be
sharp, since the area identity uses no extension constant. -/
theorem exists_lipschitz_extension_finiteDimensional
    {f : E → F} {s : Set E} {K : ℝ≥0} (hL : LipschitzOnWith K f s) :
    ∃ (g : E → F) (L : ℝ≥0), LipschitzWith L g ∧ EqOn f g s := by
  let A := (Basis.ofVectorSpace ℝ F).equivFun.toContinuousLinearEquiv
  obtain ⟨g, hg, he⟩ := (A.lipschitzWith.comp_lipschitzOnWith hL).extend_pi
  refine ⟨A.symm ∘ g, _, A.symm.lipschitzWith.comp hg, ?_⟩
  intro x hx
  change f x = A.symm (g x)
  rw [← he hx]
  exact (A.symm_apply_apply (f x)).symm

/-- Within derivatives are unique at almost every source point of a
Borel set. This is proved using the already established density-point
derivative bound applied to the identically zero difference. -/
theorem ae_eq_of_hasFDerivWithinAt
    {s : Set E} (hs : MeasurableSet s) {f : E → F}
    {L Q : E → E →L[ℝ] F}
    (hL : ∀ x ∈ s, HasFDerivWithinAt f (L x) s x)
    (hQ : ∀ x ∈ s, HasFDerivWithinAt f (Q x) s x) :
    L =ᵐ[volume.restrict s] Q := by
  have ha : _root_.ApproximatesLinearOn (fun _ : E ↦ (0 : F))
      (0 : E →L[ℝ] F) s 0 := by
    intro x hx y hy
    simp
  have hz := area_approximation_norm_fderiv_sub_le volume ha hs (fun x ↦ L x - Q x)
    (fun x hx ↦ ((hL x hx).sub (hQ x hx)).congr
      (fun y _ ↦ (sub_self (f y)).symm) (sub_self (f x)).symm)
  filter_upwards [hz] with x hx
  have hn : ‖L x - Q x‖₊ = 0 := le_antisymm (by simpa only [sub_zero] using hx) bot_le
  exact sub_eq_zero.mp (nnnorm_eq_zero.mp hn)

/-- The derivative of every actual Lipschitz extension agrees almost
everywhere with the intrinsic within derivative on the original
Lebesgue-measurable domain. -/
theorem ae_fderivWithin_eq_of_lipschitz_extension
    {s : Set E} (hs : NullMeasurableSet s volume) {f g : E → F} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hfg : EqOn f g s) :
    fderivWithin ℝ f s =ᵐ[volume.restrict s] fderiv ℝ g := by
  have hgood : NullMeasurableSet (s ∩ {x | DifferentiableAt ℝ g x}) volume :=
    hs.inter (measurableSet_of_differentiableAt ℝ g).nullMeasurableSet
  obtain ⟨t, hts, ht, htae⟩ := hgood.exists_measurable_subset_ae_eq
  have he : t =ᵐ[volume] s := htae.trans (by
    filter_upwards [hg.ae_differentiableAt (μ := volume)] with x hx
    simp only [mem_inter_iff, mem_ofPred_eq, hx, and_true])
  have hder (x : E) (hx : x ∈ t) :
      HasFDerivWithinAt f (fderiv ℝ g x) s x :=
    (hts hx).2.hasFDerivAt.hasFDerivWithinAt.congr hfg (hfg (hts hx).1)
  have hd₁ (x : E) (hx : x ∈ t) :
      HasFDerivWithinAt f (fderivWithin ℝ f s x) t x :=
    (hder x hx).differentiableWithinAt.hasFDerivWithinAt.mono
      (fun _ hy ↦ (hts hy).1)
  have hd₂ (x : E) (hx : x ∈ t) :
      HasFDerivWithinAt f (fderiv ℝ g x) t x :=
    (hder x hx).mono (fun _ hy ↦ (hts hy).1)
  have h := ae_eq_of_hasFDerivWithinAt ht hd₁ hd₂
  rwa [Measure.restrict_congr_set he] at h

theorem weightedAreaFiberSum_congr_map_eqOn {s : Set E} {f g : E → F}
    (hfg : EqOn f g s) (w : E → ℝ≥0∞) (y : F) :
    weightedAreaFiberSum s f w y = weightedAreaFiberSum s g w y := by
  unfold weightedAreaFiberSum areaFiber
  exact (Equiv.subtypeEquivRight (show ∀ x, (x ∈ s ∧ f x = y) ↔ (x ∈ s ∧ g x = y) by
    intro x
    exact and_congr_right (fun hx ↦ by rw [hfg hx]))).tsum_eq (fun x ↦ w x.1)

/-- General nonlinear weighted area on a Lebesgue-measurable source
where the map is only assumed Lipschitz on that source. -/
theorem weighted_area_formula_lipschitzOn_fiberSum
    {s : Set E} (hs : NullMeasurableSet s volume)
    {f : E → F} {K : ℝ≥0} (hL : LipschitzOnWith K f s)
    {w : E → ℝ≥0∞} (hw : AEMeasurable w (volume.restrict s)) :
    (∫⁻ y, weightedAreaFiberSum s f w y ∂μHE[finrank ℝ E]) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianWithin f s x) * w x ∂volume := by
  obtain ⟨g, L, hg, hfg⟩ := exists_lipschitz_extension_finiteDimensional hL
  have hder := ae_fderivWithin_eq_of_lipschitz_extension hs hg hfg
  calc
    _ = ∫⁻ y, weightedAreaFiberSum s g w y ∂μHE[finrank ℝ E] :=
      lintegral_congr (weightedAreaFiberSum_congr_map_eqOn hfg w)
    _ = ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt g x) * w x ∂volume :=
      weighted_area_formula_lipschitz_fiberSum_nullMeasurable hg hs hw
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hder] with x hx
      simp only [areaJacobianWithin, areaJacobianAt_eq_normDet, hx]

theorem aemeasurable_weightedAreaFiberSum_lipschitzOn
    {s : Set E} (hs : NullMeasurableSet s volume)
    {f : E → F} {K : ℝ≥0} (hL : LipschitzOnWith K f s)
    {w : E → ℝ≥0∞} (hw : AEMeasurable w (volume.restrict s)) :
    AEMeasurable (weightedAreaFiberSum s f w) μHE[finrank ℝ E] := by
  obtain ⟨g, L, hg, hfg⟩ := exists_lipschitz_extension_finiteDimensional hL
  have he : weightedAreaFiberSum s f w = weightedAreaFiberSum s g w :=
    funext (weightedAreaFiberSum_congr_map_eqOn hfg w)
  rw [he]
  exact aemeasurable_weightedAreaFiberSum_lipschitz_nullMeasurable hg hs hw

/-- The general multiplicity formula with no global extension hypothesis,
and with the correct source-dimensional target Hausdorff measure. -/
theorem area_formula_lipschitzOn_multiplicity
    {s : Set E} (hs : NullMeasurableSet s volume)
    {f : E → F} {K : ℝ≥0} (hL : LipschitzOnWith K f s) :
    (∫⁻ y, areaMultiplicity s f y ∂μHE[finrank ℝ E]) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianWithin f s x) ∂volume := by
  simpa only [weightedAreaFiberSum_one, mul_one] using
    weighted_area_formula_lipschitzOn_fiberSum hs hL (w := fun _ ↦ 1) aemeasurable_const

/-- Full injective area on Simon's original measurable Lipschitz domain,
without a rank condition or a global map regularity assumption. -/
theorem injective_area_formula_lipschitzOn
    {s : Set E} (hs : NullMeasurableSet s volume)
    {f : E → F} {K : ℝ≥0} (hL : LipschitzOnWith K f s) (hi : InjOn f s) :
    μHE[finrank ℝ E] (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianWithin f s x) ∂volume := by
  obtain ⟨g, L, hg, hfg⟩ := exists_lipschitz_extension_finiteDimensional hL
  have hgi : InjOn g s := fun x hx y hy hxy ↦ hi hx hy (by rwa [hfg hx, hfg hy])
  have him : f '' s = g '' s := hfg.image_eq
  rw [him, injective_area_formula_lipschitz_nullMeasurable hg hs hgi]
  apply lintegral_congr_ae
  filter_upwards [ae_fderivWithin_eq_of_lipschitz_extension hs hg hfg] with x hx
  simp only [areaJacobianWithin, areaJacobianAt_eq_normDet, hx]

/-- Simon (3.5) on the complete original domain and weight hypotheses,
with literal Simon Hausdorff measure on both sides. -/
theorem weighted_area_formula_lipschitzOn_fiberSum_simon
    {s : Set E} (hs : NullMeasurableSet s volume)
    {f : E → F} {K : ℝ≥0} (hL : LipschitzOnWith K f s)
    {w : E → ℝ≥0∞} (hw : AEMeasurable w (volume.restrict s)) :
    (∫⁻ y, weightedAreaFiberSum s f w y
      ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ)) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianWithin f s x) * w x
        ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) := by
  rw [simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure,
    simonHausdorffMeasureReal_source_eq_smul_volume, Measure.restrict_smul,
    lintegral_smul_measure, lintegral_smul_measure,
    weighted_area_formula_lipschitzOn_fiberSum hs hL hw]

/-- Simon (3.2) with his literal source and target Hausdorff measures. -/
theorem injective_area_formula_lipschitzOn_simon
    {s : Set E} (hs : NullMeasurableSet s volume)
    {f : E → F} {K : ℝ≥0} (hL : LipschitzOnWith K f s) (hi : InjOn f s) :
    Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianWithin f s x)
        ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) := by
  rw [simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure,
    simonHausdorffMeasureReal_source_eq_smul_volume, Measure.smul_apply,
    Measure.restrict_smul, lintegral_smul_measure,
    injective_area_formula_lipschitzOn hs hL hi]

/-- The corrected multiplicity formula with a Lebesgue source and
Simon's literal target measure displays the exact normalization factor.
No assertion that this factor equals one is needed. -/
theorem area_formula_lipschitzOn_multiplicity_simon
    {s : Set E} (hs : NullMeasurableSet s volume)
    {f : E → F} {K : ℝ≥0} (hL : LipschitzOnWith K f s) :
    (∫⁻ y, areaMultiplicity s f y
      ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ)) =
      simonAreaNormalization (finrank ℝ E) *
        ∫⁻ x in s, ENNReal.ofReal (areaJacobianWithin f s x) ∂volume := by
  rw [simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure,
    lintegral_smul_measure, area_formula_lipschitzOn_multiplicity hs hL]
  rfl

/-- The source weight may be given as measurable for Simon's actual
Hausdorff measure, exactly as stated in (3.5). Positivity of the proved
normalization transfers this hypothesis to the equivalent volume measure. -/
theorem weighted_area_formula_lipschitzOn_fiberSum_simon_hausdorffWeight
    {s : Set E} (hs : NullMeasurableSet s volume)
    {f : E → F} {K : ℝ≥0} (hL : LipschitzOnWith K f s)
    {w : E → ℝ≥0∞}
    (hw : AEMeasurable w
      ((Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ)).restrict s)) :
    (∫⁻ y, weightedAreaFiberSum s f w y
      ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ)) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianWithin f s x) * w x
        ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) := by
  apply weighted_area_formula_lipschitzOn_fiberSum_simon hs hL
  rw [simonHausdorffMeasureReal_source_eq_smul_volume, Measure.restrict_smul] at hw
  exact hw.mono_ac (Measure.absolutelyContinuous_smul (simonAreaNormalization_pos _).ne')

end
end Poincare.SimonGMT.Chapter02
