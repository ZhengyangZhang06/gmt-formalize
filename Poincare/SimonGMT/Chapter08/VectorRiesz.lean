module

public import Poincare.SimonGMT.Chapter08.ScalarRiesz
public import Poincare.SimonGMT.Chapter08.FirstVariationExtension
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# Finite-dimensional Radon representation of continuous test functionals

The scalar components are constructed by the signed scalar Riesz theorem.
Their sum supplies a common locally finite dominating measure, and actual
Radon--Nikodym derivatives give the representing Euclidean vector field.
This is the finite-dimensional construction used in Simon (8.2.5)--(8.2.6).
-/

open Set MeasureTheory CompactlySupportedContinuousMap
open scoped CompactlySupported BoundedContinuousFunction ENNReal NNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Type*} [TopologicalSpace X] {N : ℕ}

/-- Local uniform-norm boundedness for a Euclidean-valued test functional. -/
def VectorCcLocallyBounded (L : C_c(X, Euclidean N) →ₗ[ℝ] ℝ) : Prop :=
  ∀ K : Set X, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
    ∀ f : C_c(X, Euclidean N), tsupport f ⊆ K →
      |L f| ≤ C * ‖f.toBoundedContinuousFunction‖

namespace VectorRiesz

def coordinateLift (i : Fin N) : C_c(X, ℝ) →ₗ[ℝ] C_c(X, Euclidean N) where
  toFun f :=
    { toFun x := f x • EuclideanSpace.basisFun (Fin N) ℝ i
      continuous_toFun := f.continuous.smul continuous_const
      hasCompactSupport' := f.hasCompactSupport.comp_left
        (g := fun r : ℝ ↦ r • EuclideanSpace.basisFun (Fin N) ℝ i)
        (zero_smul ℝ _) }
  map_add' f g := by
    apply CompactlySupportedContinuousMap.ext
    intro x
    change (f x + g x) • EuclideanSpace.basisFun (Fin N) ℝ i = _
    exact add_smul _ _ _
  map_smul' c f := by
    apply CompactlySupportedContinuousMap.ext
    intro x
    change (c * f x) • EuclideanSpace.basisFun (Fin N) ℝ i = _
    exact mul_smul _ _ _

theorem coordinateLift_support (i : Fin N) (f : C_c(X, ℝ)) :
    tsupport (coordinateLift i f) ⊆ tsupport f :=
  closure_mono (Function.support_smul_subset_left _ _)

theorem coordinateLift_norm (i : Fin N) (f : C_c(X, ℝ)) :
    ‖(coordinateLift i f).toBoundedContinuousFunction‖ = ‖f.toBoundedContinuousFunction‖ := by
  simp only [BoundedContinuousFunction.norm_eq_iSup_norm]
  congr 1
  funext x
  change ‖f x • EuclideanSpace.basisFun (Fin N) ℝ i‖ = ‖f x‖
  rw [norm_smul, (EuclideanSpace.basisFun (Fin N) ℝ).norm_eq_one, mul_one]

def coordinateProjection (i : Fin N) : C_c(X, Euclidean N) →ₗ[ℝ] C_c(X, ℝ) where
  toFun f :=
    { toFun x := inner ℝ (EuclideanSpace.basisFun (Fin N) ℝ i) (f x)
      continuous_toFun := continuous_const.inner f.continuous
      hasCompactSupport' := f.hasCompactSupport.comp_left
        (g := fun v : Euclidean N ↦ inner ℝ (EuclideanSpace.basisFun (Fin N) ℝ i) v)
        (inner_zero_right _) }
  map_add' f g := by
    apply CompactlySupportedContinuousMap.ext
    intro x
    change inner ℝ (EuclideanSpace.basisFun (Fin N) ℝ i) (f x + g x) = _
    exact inner_add_right _ _ _
  map_smul' c f := by
    apply CompactlySupportedContinuousMap.ext
    intro x
    change inner ℝ (EuclideanSpace.basisFun (Fin N) ℝ i) (c • f x) = _
    exact inner_smul_right _ _ _

theorem sum_coordinateLift_projection (f : C_c(X, Euclidean N)) :
    ∑ i : Fin N, coordinateLift i (coordinateProjection i f) = f := by
  apply CompactlySupportedContinuousMap.ext
  intro x
  rw [CompactlySupportedContinuousMap.sum_apply]
  change (∑ i : Fin N, inner ℝ (EuclideanSpace.basisFun (Fin N) ℝ i) (f x) •
    EuclideanSpace.basisFun (Fin N) ℝ i) = f x
  exact (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr' (f x)

variable {L : C_c(X, Euclidean N) →ₗ[ℝ] ℝ} (hL : VectorCcLocallyBounded L)
include hL

theorem component_locallyBounded (i : Fin N) : CcLocallyBounded (L.comp (coordinateLift i)) := by
  intro K hK
  obtain ⟨C, hC, hc⟩ := hL K hK
  refine ⟨C, hC, fun f hf ↦ ?_⟩
  have h := hc (coordinateLift i f) ((coordinateLift_support i f).trans hf)
  rwa [coordinateLift_norm] at h

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

def positiveMeasure (i : Fin N) : Measure X :=
  ScalarRiesz.positiveMeasure (component_locallyBounded hL i)

def negativeMeasure (i : Fin N) : Measure X :=
  ScalarRiesz.negativeMeasure (component_locallyBounded hL i)

instance (i : Fin N) : IsLocallyFiniteMeasure (positiveMeasure hL i) := by
  dsimp [positiveMeasure]
  infer_instance

instance (i : Fin N) : IsLocallyFiniteMeasure (negativeMeasure hL i) := by
  dsimp [negativeMeasure]
  infer_instance

/-- A common locally finite dominating measure for all scalar components. -/
def referenceMeasure : Measure X := ∑ i : Fin N, (positiveMeasure hL i + negativeMeasure hL i)

instance : IsFiniteMeasureOnCompacts (referenceMeasure hL) where
  lt_top_of_isCompact {K} hK := by
    simp only [referenceMeasure, Measure.finsetSum_apply, Measure.add_apply]
    exact ENNReal.sum_lt_top.mpr fun i _ ↦ ENNReal.add_lt_top.mpr
      ⟨hK.measure_lt_top, hK.measure_lt_top⟩

instance : IsLocallyFiniteMeasure (referenceMeasure hL) := inferInstance
instance : (referenceMeasure hL).Regular := inferInstance

omit [SecondCountableTopology X] in
theorem positiveMeasure_le_referenceMeasure (i : Fin N) :
    positiveMeasure hL i ≤ referenceMeasure hL := by
  intro s
  rw [referenceMeasure, Measure.finsetSum_apply]
  have hi := Finset.single_le_sum
    (f := fun j : Fin N ↦ (positiveMeasure hL j + negativeMeasure hL j) s)
    (fun j _ ↦ zero_le) (Finset.mem_univ i)
  exact (le_add_right (le_refl ((positiveMeasure hL i) s))).trans hi

omit [SecondCountableTopology X] in
theorem negativeMeasure_le_referenceMeasure (i : Fin N) :
    negativeMeasure hL i ≤ referenceMeasure hL := by
  intro s
  rw [referenceMeasure, Measure.finsetSum_apply]
  have hi := Finset.single_le_sum
    (f := fun j : Fin N ↦ (positiveMeasure hL j + negativeMeasure hL j) s)
    (fun j _ ↦ zero_le) (Finset.mem_univ i)
  exact (le_add_left (le_refl ((negativeMeasure hL i) s))).trans hi

/-- The signed scalar density of a coordinate against the common measure. -/
def componentDensity (i : Fin N) (x : X) : ℝ :=
  ((positiveMeasure hL i).rnDeriv (referenceMeasure hL) x).toReal -
    ((negativeMeasure hL i).rnDeriv (referenceMeasure hL) x).toReal

omit [SecondCountableTopology X] in
theorem measurable_componentDensity (i : Fin N) : Measurable (componentDensity hL i) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal.sub
    (Measure.measurable_rnDeriv _ _).ennreal_toReal

/-- The actual measurable vector density assembled from all coordinates. -/
def density (x : X) : Euclidean N :=
  ∑ i : Fin N, componentDensity hL i x • EuclideanSpace.basisFun (Fin N) ℝ i

theorem measurable_density : Measurable (density hL) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_componentDensity hL i).smul measurable_const

theorem ae_componentDensity_norm_le_one (i : Fin N) :
    ∀ᵐ x ∂referenceMeasure hL, ‖componentDensity hL i x‖ ≤ 1 := by
  filter_upwards [Measure.rnDeriv_le_one_of_le (positiveMeasure_le_referenceMeasure hL i),
    Measure.rnDeriv_le_one_of_le (negativeMeasure_le_referenceMeasure hL i)] with x hp hn
  have hp' : ((positiveMeasure hL i).rnDeriv (referenceMeasure hL) x).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top hp
  have hn' : ((negativeMeasure hL i).rnDeriv (referenceMeasure hL) x).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top hn
  change |(_ : ℝ) - _| ≤ 1
  rw [abs_le]
  constructor <;> linarith [ENNReal.toReal_nonneg
    (a := (positiveMeasure hL i).rnDeriv (referenceMeasure hL) x),
    ENNReal.toReal_nonneg (a := (negativeMeasure hL i).rnDeriv (referenceMeasure hL) x)]

theorem ae_density_norm_le : ∀ᵐ x ∂referenceMeasure hL, ‖density hL x‖ ≤ N := by
  have ha : ∀ᵐ x ∂referenceMeasure hL, ∀ i : Fin N, ‖componentDensity hL i x‖ ≤ 1 :=
    ae_all_iff.mpr (ae_componentDensity_norm_le_one hL)
  filter_upwards [ha] with x hx
  apply (norm_sum_le _ _).trans
  calc
    (∑ i : Fin N, ‖componentDensity hL i x • EuclideanSpace.basisFun (Fin N) ℝ i‖) ≤
        ∑ _i : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, (EuclideanSpace.basisFun (Fin N) ℝ).norm_eq_one, mul_one]
      exact hx i
    _ = N := by simp

theorem integrable_componentDensity_mul (i : Fin N) (f : C_c(X, ℝ)) :
    Integrable (fun x ↦ componentDensity hL i x * f x) (referenceMeasure hL) := by
  have hp := integrable_toReal_rnDeriv_mul_iff
    (positiveMeasure_le_referenceMeasure hL i).absolutelyContinuous |>.mpr f.integrable
  have hn := integrable_toReal_rnDeriv_mul_iff
    (negativeMeasure_le_referenceMeasure hL i).absolutelyContinuous |>.mpr f.integrable
  refine (hp.sub hn).congr ?_
  filter_upwards with x
  change _ - _ = componentDensity hL i x * f x
  simp only [componentDensity, sub_mul]

theorem integral_componentDensity_mul (i : Fin N) (f : C_c(X, ℝ)) :
    (∫ x, componentDensity hL i x * f x ∂referenceMeasure hL) = L (coordinateLift i f) := by
  have hp := integrable_toReal_rnDeriv_mul_iff
    (positiveMeasure_le_referenceMeasure hL i).absolutelyContinuous |>.mpr f.integrable
  have hn := integrable_toReal_rnDeriv_mul_iff
    (negativeMeasure_le_referenceMeasure hL i).absolutelyContinuous |>.mpr f.integrable
  simp only [componentDensity, sub_mul]
  rw [integral_sub hp hn,
    integral_toReal_rnDeriv_mul (positiveMeasure_le_referenceMeasure hL i).absolutelyContinuous,
    integral_toReal_rnDeriv_mul (negativeMeasure_le_referenceMeasure hL i).absolutelyContinuous]
  exact ScalarRiesz.integral_positiveMeasure_sub_integral_negativeMeasure
    (component_locallyBounded hL i) f

omit [SecondCountableTopology X] in
theorem inner_density (f : X → Euclidean N) (x : X) :
    inner ℝ (density hL x) (f x) =
      ∑ i : Fin N, componentDensity hL i x *
        inner ℝ (EuclideanSpace.basisFun (Fin N) ℝ i) (f x) := by
  simp only [density, sum_inner, inner_smul_left, starRingEnd_apply, star_trivial]

theorem integrable_inner_density (f : C_c(X, Euclidean N)) :
    Integrable (fun x ↦ inner ℝ (density hL x) (f x)) (referenceMeasure hL) := by
  simp_rw [inner_density]
  exact integrable_finsetSum _ fun i _ ↦
    integrable_componentDensity_mul hL i (coordinateProjection i f)

/-- The vector integral representation is constructed from the scalar
component measures and their genuine Radon--Nikodym derivatives. -/
theorem integral_inner_density (f : C_c(X, Euclidean N)) :
    (∫ x, inner ℝ (density hL x) (f x) ∂referenceMeasure hL) = L f := by
  simp_rw [inner_density]
  change (∫ x, ∑ i : Fin N, componentDensity hL i x *
    coordinateProjection i f x ∂referenceMeasure hL) = _
  rw [integral_finsetSum _ (fun i _ ↦
    integrable_componentDensity_mul hL i (coordinateProjection i f))]
  calc
    _ = ∑ i : Fin N, L (coordinateLift i (coordinateProjection i f)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_componentDensity_mul hL i (coordinateProjection i f)
    _ = L f := by rw [← map_sum, sum_coordinateLift_projection]

/-- The total-variation measure obtained by taking the norm of the
constructed vector density. Its exact supremum property is established
after the polar-field representation. -/
def variationMeasure : Measure X := (referenceMeasure hL).withDensity (fun x ↦ ‖density hL x‖ₑ)

theorem variationMeasure_le : variationMeasure hL ≤ (N : ℝ≥0∞) • referenceMeasure hL := by
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [ae_density_norm_le hL] with x hx
  rw [← ofReal_norm]
  exact (ENNReal.ofReal_le_ofReal hx).trans_eq (by simp)

instance : IsLocallyFiniteMeasure (variationMeasure hL) := by
  have : IsLocallyFiniteMeasure ((N : ℝ≥0∞) • referenceMeasure hL) :=
    Measure.isLocallyFiniteMeasure_smul _ (by simp)
  exact Measure.isLocallyFiniteMeasure_of_le (variationMeasure_le hL)

instance : (variationMeasure hL).Regular := inferInstance

/-- The sign is chosen for Simon's convention `δV(X) = -∫ν·X d‖δV‖`. -/
def polarField (x : X) : Euclidean N := -(‖density hL x‖⁻¹ • density hL x)

theorem measurable_polarField : Measurable (polarField hL) :=
  ((measurable_density hL).norm.inv.smul (measurable_density hL)).neg

omit [SecondCountableTopology X] in
theorem norm_density_smul_polarField (x : X) :
    ‖density hL x‖ • polarField hL x = -density hL x := by
  by_cases hx : density hL x = 0
  · simp [polarField, hx]
  · simp only [polarField, smul_neg, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

theorem ae_polarField_norm_one : ∀ᵐ x ∂variationMeasure hL, ‖polarField hL x‖ = 1 := by
  rw [variationMeasure, ae_withDensity_iff (measurable_density hL).enorm]
  filter_upwards with x hx
  have hne : density hL x ≠ 0 := by simpa using hx
  simp only [polarField, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]

theorem integrable_inner_polarField (f : C_c(X, Euclidean N)) :
    Integrable (fun x ↦ inner ℝ (polarField hL x) (f x)) (variationMeasure hL) := by
  rw [variationMeasure, integrable_withDensity_iff_integrable_smul'
    (measurable_density hL).enorm (Filter.Eventually.of_forall fun x ↦ enorm_lt_top)]
  have hid : (fun x ↦ (‖density hL x‖ₑ).toReal • inner ℝ (polarField hL x) (f x)) =
      fun x ↦ -inner ℝ (density hL x) (f x) := by
    funext x
    rw [toReal_enorm, smul_eq_mul, ← real_inner_smul_left, norm_density_smul_polarField,
      inner_neg_left]
  rw [hid]
  exact (integrable_inner_density hL f).neg

/-- The signed unit-polar integral representation, built with no measure
or polar-field existence premise. -/
theorem neg_integral_inner_polarField (f : C_c(X, Euclidean N)) :
    -(∫ x, inner ℝ (polarField hL x) (f x) ∂variationMeasure hL) = L f := by
  rw [variationMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_density hL).enorm (Filter.Eventually.of_forall fun x ↦ enorm_lt_top)]
  have hid : (fun x ↦ (‖density hL x‖ₑ).toReal • inner ℝ (polarField hL x) (f x)) =
      fun x ↦ -inner ℝ (density hL x) (f x) := by
    funext x
    rw [toReal_enorm, smul_eq_mul, ← real_inner_smul_left, norm_density_smul_polarField,
      inner_neg_left]
  rw [hid, integral_neg, neg_neg, integral_inner_density]

end VectorRiesz
end
end Poincare.SimonGMT.Chapter08
