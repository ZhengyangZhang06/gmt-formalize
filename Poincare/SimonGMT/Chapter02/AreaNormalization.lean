module

public import Poincare.SimonGMT.Chapter02.WeightedArea

@[expose] public section

/-!
# Area transport for Simon's literal Hausdorff normalization

The literal Gamma-normalized Hausdorff measure and Mathlib's Euclidean
Hausdorff measure differ by an explicitly specified positive finite scalar.
We retain that scalar in source-volume formulas. Its identification with one
in dimensions at least two is the separate Chapter 1 normalization problem.
-/

open Function MeasureTheory Module Set
open scoped ENNReal NNReal

namespace Poincare.SimonGMT.Chapter02

noncomputable section

/-- The exact conversion factor from Euclidean-normalized Hausdorff measure
to Simon's literal Gamma-normalized construction, independent of the ambient
space. No assertion that this number equals one is built into the definition. -/
def simonAreaNormalization (d : ℕ) : ℝ≥0∞ :=
  (Chapter01.realUnitBallVolume (d : ℝ) / (2 : ℝ≥0∞) ^ (d : ℝ)) /
    (Measure.addHaarScalarFactor
      (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d] : ℝ≥0∞)

theorem simonAreaNormalization_pos (d : ℕ) : 0 < simonAreaNormalization d := by
  apply ENNReal.div_pos
  · exact (ENNReal.div_pos
      (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg d)).ne' (by simp)).ne'
  · exact ENNReal.coe_ne_top

theorem simonAreaNormalization_ne_top (d : ℕ) : simonAreaNormalization d ≠ ∞ := by
  apply ENNReal.div_ne_top
  · exact ENNReal.div_ne_top (Chapter01.realUnitBallVolume_ne_top _) (by simp)
  · exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d]).ne'

/-- The conversion formula holds on every ambient metric space, so source
and target use precisely the same normalization scalar. -/
theorem simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (d : ℕ) :
    Chapter01.simonHausdorffMeasureReal (X := X) (d : ℝ) =
      simonAreaNormalization d • (μHE[d] : Measure X) := by
  have hc : (Measure.addHaarScalarFactor
      (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d] : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d]).ne'
  rw [Chapter01.simonHausdorffMeasureReal, Measure.euclideanHausdorffMeasure_def,
    ENNReal.smul_def, smul_smul, simonAreaNormalization,
    ENNReal.div_mul_cancel hc ENNReal.coe_ne_top]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]

/-- Literal Simon-Hausdorff transport has the same metric-Jacobian
integrand when the source carries the same literal normalization. -/
theorem weighted_area_formula_simonHausdorff_of_injective_derivative
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hreg : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hinj : InjOn f s)
    (g : F → ℝ≥0∞) :
    ∫⁻ y in f '' s, g y ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) * g (f x)
        ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) := by
  simp_rw [simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure,
    Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
  rw [weighted_area_formula_of_injective_derivative hs hf hreg hinj g]

/-- For Euclidean source volume, the literal Simon-Hausdorff transport
retains the explicit Chapter 1 normalization factor. -/
theorem weighted_area_formula_simonHausdorff_volume_of_injective_derivative
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hreg : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hinj : InjOn f s)
    (g : F → ℝ≥0∞) :
    ∫⁻ y in f '' s, g y ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) =
      simonAreaNormalization (finrank ℝ E) *
        ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) * g (f x) ∂volume := by
  rw [simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure,
    Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
    weighted_area_formula_volume_of_injective_derivative hs hf hreg hinj g]

/-- The Bochner version of area transport for the literal normalization. -/
theorem integral_area_formula_simonHausdorff_of_injective_derivative
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hreg : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hinj : InjOn f s)
    (g : F → G) :
    ∫ y in f '' s, g y ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) =
      ∫ x in s, areaJacobianAt f x • g (f x)
        ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) := by
  simp_rw [simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure,
    Measure.restrict_smul, integral_smul_measure]
  rw [integral_area_formula_of_injective_derivative hs hf hreg hinj g]

/-- Signed/vector-valued coordinate integration, with the explicit
normalization factor retained when source volume is used. -/
theorem integral_area_formula_simonHausdorff_volume_of_injective_derivative
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hreg : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hinj : InjOn f s)
    (g : F → G) :
    ∫ y in f '' s, g y ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) =
      (simonAreaNormalization (finrank ℝ E)).toReal •
        ∫ x in s, areaJacobianAt f x • g (f x) ∂volume := by
  rw [simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure,
    Measure.restrict_smul, integral_smul_measure,
    integral_area_formula_of_injective_derivative hs hf hreg hinj g,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]

/-- Exact coordinate density of a literal Simon-Hausdorff density under a
regular injective chart. This identifies the actual pullback measure, with
the normalization factor displayed explicitly. -/
theorem pullback_withDensity_simonHausdorff_eq
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hreg : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hinj : InjOn f s)
    (w : F → ℝ≥0∞) :
    (((Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) : Measure F).withDensity w).comap
        (s.domRestrict f)).map (Subtype.val : s → E) =
      (volume.restrict s).withDensity (fun x ↦
        simonAreaNormalization (finrank ℝ E) *
          (ENNReal.ofReal (areaJacobianAt f x) * w (f x))) := by
  rw [simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure,
    withDensity_smul_measure, Measure.comap_smul,
    Measure.map_smul _ measurable_subtype_coe.aemeasurable,
    pullback_withDensity_areaJacobian_eq hs hf hreg hinj w,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  exact (withDensity_smul' _ _ (simonAreaNormalization_ne_top _)).symm

/-- The literal source measure in its own dimension is the same explicitly
specified scalar multiple of volume. -/
theorem simonHausdorffMeasureReal_source_eq_smul_volume :
    (Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) : Measure E) =
      simonAreaNormalization (finrank ℝ E) • volume := by
  rw [simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]

end
end Poincare.SimonGMT.Chapter02
