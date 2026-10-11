module

public import Poincare.SimonGMT.Chapter02.AreaFormula
public import Poincare.SimonGMT.Chapter02.Submanifold
public import Mathlib.MeasureTheory.Measure.AEMeasurable

public section

/-!
# Weighted nonlinear area transport in arbitrary codimension

The domain measure with the actual metric-Jacobian density is transported
to Hausdorff measure of the nonlinear image. The resulting change of
variables allows arbitrary nonnegative target weights. The regularity
hypotheses hold for Simon's smooth local submanifold representations.
-/

open Function MeasureTheory Module Set Filter
open scoped ENNReal NNReal Bundle Manifold

namespace Poincare.SimonGMT.Chapter02

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]

/-- The regular nonlinear area formula expressed with the actual totalized
Fréchet area Jacobian. -/
theorem injective_area_formula_areaJacobianAt
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hreg : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hinj : InjOn f s) :
    μHE[finrank ℝ E] (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) ∂μHE[finrank ℝ E] := by
  simpa only [areaJacobianAt_eq_normDet] using
    injective_area_formula_of_injective_derivative hs
      (fun x hx ↦ (hf x hx).hasFDerivAt.hasFDerivWithinAt) hreg hinj

/-- The parametrization restricted to its measurable source domain sends
the Jacobian-weighted source measure to Hausdorff measure of its image. -/
theorem restrict_map_withDensity_areaJacobian_eq
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hreg : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hinj : InjOn f s) :
    Measure.map (s.domRestrict f)
      ((μHE[finrank ℝ E].withDensity (fun x ↦ ENNReal.ofReal (areaJacobianAt f x))).comap
        (Subtype.val : s → E)) = μHE[finrank ℝ E].restrict (f '' s) := by
  have hcont : ContinuousOn f s := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have hemb := hcont.measurableEmbedding hs hinj
  have hsub := MeasurableEmbedding.subtype_coe hs
  ext t ht
  rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
  let B : Set E := Subtype.val '' ((s.domRestrict f) ⁻¹' t)
  have hB : MeasurableSet B := hsub.measurableSet_image' (hemb.measurable ht)
  have hBs : B ⊆ s := by
    rintro x ⟨u, _, rfl⟩
    exact u.property
  change (μHE[finrank ℝ E].withDensity
    (fun x ↦ ENNReal.ofReal (areaJacobianAt f x))) B = _
  rw [withDensity_apply _ hB,
    ← injective_area_formula_areaJacobianAt hB (fun x hx ↦ hf x (hBs hx))
      (fun x hx ↦ hreg x (hBs hx)) (hinj.mono hBs), Measure.restrict_apply ht]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨hu, ⟨u, u.property, rfl⟩⟩
  · rintro ⟨hy, x, hx, rfl⟩
    exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩

/-- Simon (3.5) for an injective regular nonlinear parametrization in
arbitrary codimension. The target weight need not be measurable. -/
theorem weighted_area_formula_of_injective_derivative
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hreg : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hinj : InjOn f s)
    (g : F → ℝ≥0∞) :
    ∫⁻ y in f '' s, g y ∂μHE[finrank ℝ E] =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) * g (f x) ∂μHE[finrank ℝ E] := by
  have hcont : ContinuousOn f s := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  rw [← restrict_map_withDensity_areaJacobian_eq hs hf hreg hinj,
    (hcont.measurableEmbedding hs hinj).lintegral_map]
  change (∫⁻ x : s, (fun x : E ↦ g (f x)) x ∂
    ((μHE[finrank ℝ E].withDensity (fun x ↦ ENNReal.ofReal (areaJacobianAt f x))).comap
      (Subtype.val : s → E))) = _
  rw [lintegral_subtype_comap
    (μ := μHE[finrank ℝ E].withDensity (fun x ↦ ENNReal.ofReal (areaJacobianAt f x)))
    hs (fun x : E ↦ g (f x)),
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
  · rfl
  · simp only [eventually_true, ENNReal.ofReal_lt_top]
  · exact ((measurable_areaJacobianAt f).ennreal_ofReal).aemeasurable

/-- The measure-level nonlinear area formula for the original map, whose
values outside the source set need not be measurable. -/
theorem map_withDensity_areaJacobian_eq
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hreg : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hinj : InjOn f s) :
    Measure.map f ((μHE[finrank ℝ E].restrict s).withDensity
      (fun x ↦ ENNReal.ofReal (areaJacobianAt f x))) =
        μHE[finrank ℝ E].restrict (f '' s) := by
  let J : E → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (areaJacobianAt f x)
  let ν : Measure s := (μHE[finrank ℝ E].withDensity J).comap (Subtype.val : s → E)
  have hν : ν.map (Subtype.val : s → E) = (μHE[finrank ℝ E].restrict s).withDensity J := by
    dsimp only [ν]
    rw [map_comap_subtype_coe hs, restrict_withDensity hs]
  have hfm : AEMeasurable f (ν.map (Subtype.val : s → E)) := by
    rw [hν]
    apply AEMeasurable.mono_ac _ (withDensity_absolutelyContinuous _ _)
    exact (show ContinuousOn f s from
      fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt).aemeasurable hs
  rw [← hν, AEMeasurable.map_map_of_aemeasurable hfm measurable_subtype_coe.aemeasurable]
  exact restrict_map_withDensity_areaJacobian_eq hs hf hreg hinj

/-- Weighted area transport with Euclidean volume as the source measure. -/
theorem weighted_area_formula_volume_of_injective_derivative
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hreg : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hinj : InjOn f s)
    (g : F → ℝ≥0∞) :
    ∫⁻ y in f '' s, g y ∂μHE[finrank ℝ E] =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) * g (f x) ∂volume := by
  simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
    weighted_area_formula_of_injective_derivative hs hf hreg hinj g

/-- Bochner-integrability transport for a regular injective parametrization.
This applies in particular to the signed integrands of first variation. -/
theorem integrableOn_image_iff_integrableOn_areaJacobian_smul
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hreg : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hinj : InjOn f s)
    (g : F → G) :
    IntegrableOn g (f '' s) μHE[finrank ℝ E] ↔
      IntegrableOn (fun x ↦ areaJacobianAt f x • g (f x)) s μHE[finrank ℝ E] := by
  have hcont : ContinuousOn f s := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  rw [IntegrableOn, ← restrict_map_withDensity_areaJacobian_eq hs hf hreg hinj,
    (hcont.measurableEmbedding hs hinj).integrable_map_iff]
  simp only [Set.domRestrict_eq, ← Function.comp_assoc, ENNReal.ofReal]
  rw [← (MeasurableEmbedding.subtype_coe hs).integrable_map_iff, map_comap_subtype_coe hs,
    restrict_withDensity hs, integrable_withDensity_iff_integrable_coe_smul₀]
  · simp_rw [IntegrableOn, Real.coe_toNNReal _ (areaJacobianAt_nonneg f _), Function.comp_apply]
  · exact ((measurable_areaJacobianAt f).real_toNNReal).aemeasurable

/-- The Bochner form of the nonlinear area formula, with the genuine
metric Jacobian multiplying the pulled-back target integrand. -/
theorem integral_area_formula_of_injective_derivative
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hreg : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hinj : InjOn f s)
    (g : F → G) :
    ∫ y in f '' s, g y ∂μHE[finrank ℝ E] =
      ∫ x in s, areaJacobianAt f x • g (f x) ∂μHE[finrank ℝ E] := by
  have hcont : ContinuousOn f s := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  rw [← restrict_map_withDensity_areaJacobian_eq hs hf hreg hinj,
    (hcont.measurableEmbedding hs hinj).integral_map]
  simp only [Set.domRestrict_apply, ← Function.comp_apply (f := g), ENNReal.ofReal]
  rw [← (MeasurableEmbedding.subtype_coe hs).integral_map, map_comap_subtype_coe hs,
    setIntegral_withDensity_eq_setIntegral_smul₀
      (((measurable_areaJacobianAt f).real_toNNReal).aemeasurable) _ hs]
  congr with x
  rw [NNReal.smul_def, Real.coe_toNNReal _ (areaJacobianAt_nonneg f x)]

/-- Pulling a Hausdorff density back along the actual source-domain
embedding yields exactly the density multiplied by the metric Jacobian.
The pullback is extended by zero off the source set. -/
theorem pullback_withDensity_areaJacobian_eq
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hreg : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hinj : InjOn f s)
    (w : F → ℝ≥0∞) :
    (((μHE[finrank ℝ E] : Measure F).withDensity w).comap (s.domRestrict f)).map
        (Subtype.val : s → E) =
      (μHE[finrank ℝ E].restrict s).withDensity
        (fun x ↦ ENNReal.ofReal (areaJacobianAt f x) * w (f x)) := by
  have hcont : ContinuousOn f s := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have hemb := hcont.measurableEmbedding hs hinj
  have hsub := MeasurableEmbedding.subtype_coe hs
  ext t ht
  rw [hsub.map_apply, hemb.comap_apply]
  have himage : (s.domRestrict f) '' ((Subtype.val : s → E) ⁻¹' t) = f '' (t ∩ s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, ⟨hx, x.property⟩, rfl⟩
    · rintro ⟨x, ⟨hxt, hxs⟩, rfl⟩
      exact ⟨⟨x, hxs⟩, hxt, rfl⟩
  have himagemeas : MeasurableSet (f '' (t ∩ s)) :=
    (ht.inter hs).image_of_continuousOn_injOn
      (hcont.mono inter_subset_right) (hinj.mono inter_subset_right)
  rw [himage, withDensity_apply _ himagemeas,
    weighted_area_formula_of_injective_derivative (ht.inter hs)
      (fun x hx ↦ hf x hx.2) (fun x hx ↦ hreg x hx.2)
      (hinj.mono inter_subset_right) w,
    withDensity_apply _ ht, Measure.restrict_restrict ht]

/-- The weighted nonlinear area formula on every measurable subset of a
Simon `C¹` (or smoother) local representation. -/
theorem IsSimonLocalRepresentation.weighted_area_formula
    {r : ℕ∞} {M W : Set F} {D s : Set E} {f : E → F}
    (h : IsSimonLocalRepresentation r M D W f) (hr : 1 ≤ r)
    (hs : MeasurableSet s) (hsD : s ⊆ D) (g : F → ℝ≥0∞) :
    ∫⁻ y in f '' s, g y ∂μHE[finrank ℝ E] =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) * g (f x) ∂μHE[finrank ℝ E] := by
  apply weighted_area_formula_of_injective_derivative hs
  · intro x hx
    apply (h.contDiffOn.differentiableOn
      (by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (show (0 : ℕ∞) < 1 by simp) hr)))
        x (hsD hx)).differentiableAt
    exact h.isOpen_source.mem_nhds (hsD hx)
  · exact fun x hx ↦ h.injective_fderiv (hsD hx)
  · exact h.injOn.mono hsD

/-- The image-measure formula on every measurable part of a regular
Simon representation. -/
theorem IsSimonLocalRepresentation.area_formula
    {r : ℕ∞} {M W : Set F} {D s : Set E} {f : E → F}
    (h : IsSimonLocalRepresentation r M D W f) (hr : 1 ≤ r)
    (hs : MeasurableSet s) (hsD : s ⊆ D) :
    μHE[finrank ℝ E] (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) ∂volume := by
  simpa only [setLIntegral_one, mul_one,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
      h.weighted_area_formula hr hs hsD (fun _ ↦ 1)

/-- Simon's regular space-curve length formula: Hausdorff measure of the
image of an injective regular curve equals the integral of its speed. -/
theorem injective_regular_curve_area_formula
    {s : Set ℝ} {f : ℝ → F} (hs : MeasurableSet s)
    (hf : ∀ t ∈ s, DifferentiableAt ℝ f t)
    (hregular : ∀ t ∈ s, deriv f t ≠ 0) (hinj : InjOn f s) :
    μHE[1] (f '' s) = ∫⁻ t in s, ENNReal.ofReal ‖deriv f t‖ := by
  have hreg : ∀ t ∈ s, Injective (fderiv ℝ f t) := by
    intro t ht
    apply ((fderiv ℝ f t).toLinearMap.normDet_ne_zero_tfae.out 1 5).mp
    have hnorm : (fderiv ℝ f t).normDet = ‖deriv f t‖ := by
      rw [← areaJacobianAt_eq_normDet]
      exact areaJacobianAt_curve_eq_norm_deriv f t
    rw [hnorm, norm_ne_zero_iff]
    exact hregular t ht
  simpa only [finrank_self, areaJacobianAt_curve_eq_norm_deriv, mul_one, setLIntegral_one] using
    weighted_area_formula_volume_of_injective_derivative hs hf hreg hinj (fun _ ↦ 1)

/-- The extended path length of an injective regular curve on a compact
interval is the one-dimensional Hausdorff measure of its image. -/
theorem injective_regular_curve_hausdorff_eq_pathELength
    {f : ℝ → F} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hregular : ∀ t ∈ Icc a b, deriv f t ≠ 0) (hinj : InjOn f (Icc a b)) :
    μHE[1] (f '' Icc a b) = Manifold.pathELength 𝓘(ℝ, F) f a b := by
  rw [injective_regular_curve_area_formula measurableSet_Icc hf hregular hinj,
    ← lintegral_areaJacobianAt_curve_eq_pathELength]
  simp only [areaJacobianAt_curve_eq_norm_deriv]

end
end Poincare.SimonGMT.Chapter02
