module

public import Poincare.SimonGMT.Chapter02.AreaNormalization
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.Analysis.Calculus.Rademacher

@[expose] public section

/-!
# Critical images in arbitrary codimension

The regular injective area theorem is applied to the lifted graph
`x ↦ (f x, ε x)` in the Hilbert product. Projection is 1-Lipschitz,
and the graph Jacobians tend to zero at rank-deficient points. This
provides the critical-image step without assuming an area formula for
singular maps.
-/

open Function MeasureTheory Module Set Filter Metric
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

/-- An injective regularization in a genuine Hilbert product. -/
def areaGraph (f : E → F) (ε : ℝ) (x : E) : WithLp 2 (F × E) :=
  WithLp.toLp 2 (f x, ε • x)

/-- The derivative of the lifted graph. -/
def areaGraphLinear (L : E →L[ℝ] F) (ε : ℝ) : E →L[ℝ] WithLp 2 (F × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ F E).symm.toContinuousLinearMap.comp
    (L.prod (ε • ContinuousLinearMap.id ℝ E))

@[simp] theorem areaGraphLinear_apply (L : E →L[ℝ] F) (ε : ℝ) (x : E) :
    areaGraphLinear L ε x = WithLp.toLp 2 (L x, ε • x) := rfl

theorem areaGraph_injective (f : E → F) {ε : ℝ} (hε : ε ≠ 0) :
    Injective (areaGraph f ε) := by
  intro x y h
  have he : ε • x = ε • y := congrArg WithLp.snd h
  exact (smul_right_injective E hε) he

theorem areaGraphLinear_injective (L : E →L[ℝ] F) {ε : ℝ} (hε : ε ≠ 0) :
    Injective (areaGraphLinear L ε) := areaGraph_injective L hε

theorem hasFDerivAt_areaGraph {f : E → F} {L : E →L[ℝ] F} {x : E}
    (hf : HasFDerivAt f L x) (ε : ℝ) :
    HasFDerivAt (areaGraph f ε) (areaGraphLinear L ε) x := by
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ F E).symm.toContinuousLinearMap.hasFDerivAt.comp x
    (hf.prodMk ((hasFDerivAt_id x).const_smul ε))

theorem continuous_areaGraphLinear :
    Continuous (fun p : (E →L[ℝ] F) × ℝ ↦ areaGraphLinear p.1 p.2) := by
  unfold areaGraphLinear
  apply Continuous.clm_comp continuous_const
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp
    (continuous_fst.prodMk (continuous_snd.smul continuous_const))

theorem areaGraphLinear_normDet_zero {L : E →L[ℝ] F} (hL : ¬ Injective L) :
    (areaGraphLinear L 0).normDet = 0 := by
  apply ((areaGraphLinear L 0).toLinearMap.normDet_eq_zero_tfae.out 6 1).mp
  intro hg
  apply hL
  intro x y hxy
  apply hg
  change areaGraphLinear L 0 x = areaGraphLinear L 0 y
  simp only [areaGraphLinear_apply, zero_smul, hxy]

/-- Projection of the regular graph bounds the area of an arbitrary
noninjective image by the actual regularized Jacobian integral. -/
theorem area_image_le_lintegral_graphJacobian
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) {ε : ℝ} (hε : ε ≠ 0) :
    μHE[finrank ℝ E] (f '' s) ≤
      ∫⁻ x in s, ENNReal.ofReal (areaGraphLinear (fderiv ℝ f x) ε).normDet ∂volume := by
  have hproj : μHE[finrank ℝ E] (f '' s) ≤
      μHE[finrank ℝ E] (areaGraph f ε '' s) := by
    have hp : LipschitzWith 1 (WithLp.fst : WithLp 2 (F × E) → F) :=
      LipschitzWith.of_dist_le_mul (fun x y ↦ by simpa using WithLp.dist_fst_le x y)
    simpa [image_image, Function.comp_def, areaGraph] using
      euclideanHausdorffMeasure_image_le_of_lipschitzOn (finrank ℝ E)
        (hp.lipschitzOnWith (s := areaGraph f ε '' s))
  rw [injective_area_formula_of_injective_derivative hs
    (fun x hx ↦ (hasFDerivAt_areaGraph (hf x hx).hasFDerivAt ε).hasFDerivWithinAt)
    (fun x _ ↦ areaGraphLinear_injective (fderiv ℝ f x) hε)
    (areaGraph_injective f hε).injOn,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at hproj
  exact hproj

/-- The critical-image theorem on a finite-measure source piece with
bounded derivative. No injectivity or positive-rank hypothesis is made. -/
theorem area_image_eq_zero_of_critical_finite
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hcrit : ∀ x ∈ s, ¬ Injective (fderiv ℝ f x))
    (hfinite : volume s ≠ ⊤) {B : ℝ}
    (hB : ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ B) :
    μHE[finrank ℝ E] (f '' s) = 0 := by
  have hc : Continuous (fun p : (E →L[ℝ] F) × ℝ ↦
      (areaGraphLinear p.1 p.2).normDet) :=
    continuous_normDet.comp continuous_areaGraphLinear
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : E →L[ℝ] F) B).prod
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))).exists_bound_of_continuousOn hc.continuousOn
  have hlim : Tendsto (fun ε : ℝ ↦ ∫⁻ x in s,
      ENNReal.ofReal (areaGraphLinear (fderiv ℝ f x) ε).normDet ∂volume)
      (𝓝[>] 0) (𝓝 0) := by
    have hmeas (ε : ℝ) : Measurable (fun x : E ↦
        ENNReal.ofReal (areaGraphLinear (fderiv ℝ f x) ε).normDet) :=
      (hc.measurable.comp ((measurable_fderiv ℝ f).prodMk measurable_const)).ennreal_ofReal
    have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ x ∂volume.restrict s,
        ENNReal.ofReal (areaGraphLinear (fderiv ℝ f x) ε).normDet ≤ ENNReal.ofReal C := by
      have hnear : Icc (-1 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds
        (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
      filter_upwards [hnear] with ε hε
      filter_upwards [ae_restrict_mem hs] with x hx
      apply ENNReal.ofReal_le_ofReal
      exact (le_abs_self _).trans (hC ⟨fderiv ℝ f x, ε⟩
        ⟨by simpa only [mem_closedBall, dist_zero_right] using hB x hx, hε⟩)
    have hfin : (∫⁻ _ : E, ENNReal.ofReal C ∂volume.restrict s) ≠ ⊤ := by
      rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite
    have hpoint : ∀ᵐ x ∂volume.restrict s,
        Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (areaGraphLinear (fderiv ℝ f x) ε).normDet)
          (𝓝[>] 0) (𝓝 0) := by
      filter_upwards [ae_restrict_mem hs] with x hx
      have hc' : Continuous (fun ε : ℝ ↦
          ENNReal.ofReal (areaGraphLinear (fderiv ℝ f x) ε).normDet) :=
        ENNReal.continuous_ofReal.comp (hc.comp (continuous_const.prodMk continuous_id))
      simpa only [areaGraphLinear_normDet_zero (hcrit x hx), ENNReal.ofReal_zero] using
        (hc'.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [lintegral_zero] using
      tendsto_lintegral_filter_of_dominated_convergence (fun _ : E ↦ ENNReal.ofReal C)
        (Eventually.of_forall hmeas) hbound hfin hpoint
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact area_image_le_lintegral_graphJacobian hs hf (ne_of_gt hε)

/-- Rank-deficient differentiability points have null image in source-
dimensional Hausdorff measure, in arbitrary codimension. The finiteness
and derivative bounds of the auxiliary theorem are removed by a genuine
countable exhaustion. -/
theorem area_image_eq_zero_of_critical
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hcrit : ∀ x ∈ s, ¬ Injective (fderiv ℝ f x)) :
    μHE[finrank ℝ E] (f '' s) = 0 := by
  let t : ℕ → Set E := fun k ↦ s ∩ closedBall 0 k ∩ {x | ‖fderiv ℝ f x‖ ≤ k}
  have ht (k : ℕ) : MeasurableSet (t k) :=
    (hs.inter measurableSet_closedBall).inter
      (measurableSet_le (measurable_fderiv ℝ f).norm measurable_const)
  have hts (k : ℕ) : t k ⊆ s := fun _ hx ↦ hx.1.1
  have hcover : s ⊆ ⋃ k, t k := by
    intro x hx
    obtain ⟨k, hk⟩ := exists_nat_gt (max ‖x‖ ‖fderiv ℝ f x‖)
    refine mem_iUnion.mpr ⟨k, ⟨hx, ?_⟩, (le_max_right _ _).trans hk.le⟩
    simpa only [mem_closedBall, dist_zero_right] using (le_max_left _ _).trans hk.le
  have hnull (k : ℕ) : μHE[finrank ℝ E] (f '' t k) = 0 := by
    apply area_image_eq_zero_of_critical_finite (ht k)
      (fun x hx ↦ hf x (hts k hx)) (fun x hx ↦ hcrit x (hts k hx))
    · exact ne_top_of_le_ne_top measure_closedBall_lt_top.ne
        (measure_mono (fun _ hx ↦ hx.1.2))
    · exact fun _ hx ↦ hx.2
  apply measure_mono_null (image_mono hcover)
  rw [image_iUnion]
  exact measure_iUnion_null hnull

theorem areaJacobianAt_eq_zero_iff_not_injective (f : E → F) (x : E) :
    areaJacobianAt f x = 0 ↔ ¬ Injective (fderiv ℝ f x) := by
  rw [areaJacobianAt_eq_normDet]
  exact (fderiv ℝ f x).toLinearMap.normDet_eq_zero_tfae.out 1 6

/-- The full critical set is Borel, and its image is Hausdorff-null.
Only actual differentiability points belong to this set. -/
theorem area_image_criticalSet_eq_zero (f : E → F) :
    μHE[finrank ℝ E]
      (f '' {x | DifferentiableAt ℝ f x ∧ ¬ Injective (fderiv ℝ f x)}) = 0 := by
  apply area_image_eq_zero_of_critical
  · simp_rw [← areaJacobianAt_eq_zero_iff_not_injective]
    exact (measurableSet_of_differentiableAt ℝ f).inter
      (measurableSet_eq_fun (measurable_areaJacobianAt f) measurable_const)
  · exact fun _ hx ↦ hx.1
  · exact fun _ hx ↦ hx.2

end
end Poincare.SimonGMT.Chapter02
