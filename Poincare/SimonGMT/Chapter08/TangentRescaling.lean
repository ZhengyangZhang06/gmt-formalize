module

public import Poincare.SimonGMT.Chapter08.StationaryMonotonicity
public import Poincare.SimonGMT.Chapter08.FirstVariationRiesz
public import Poincare.SimonGMT.Chapter08.ConstancyTangent
public import Poincare.SimonGMT.Chapter04.WeightedBlowUp
public import Poincare.SimonGMT.Chapter01.Densities
import all Poincare.SimonGMT.Chapter03.Rectifiable

@[expose] public section

/-!
# Genuine varifold blow-ups at a point of positive finite density

Simon's convention is η_{ξ,r}(y) = r⁻¹ (y − ξ). The Jacobian and
transported plane are calculated from the derivative, so the rescaled
bundle measure below is the actual pushforward, not a proxy measure.
The source density hypothesis gives all fixed-radius ball-mass limits.
No compactness extraction or limit-measure conclusion is assumed here.

Source: `Simon-gmt new.pdf`, printed p. 215, (8.5.1)--(8.5.2).
-/

open Set Filter MeasureTheory Function Metric
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08.Varifold
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {N n : ℕ} {U : Set (Euclidean N)}

/-- A dilation does not rotate the plane component. -/
def blowUpBundleMap (ξ : Euclidean N) (r : ℝ) :
    Euclidean N × Grassmannian N n → Euclidean N × Grassmannian N n :=
  fun z ↦ (Chapter03.blowUpMap ξ r z.1, z.2)

theorem continuous_blowUpBundleMap (ξ : Euclidean N) (r : ℝ) :
    Continuous (blowUpBundleMap (n := n) ξ r) := by
  unfold blowUpBundleMap Chapter03.blowUpMap
  fun_prop

theorem tangentialDerivative_blowUpMap (ξ y : Euclidean N) (r : ℝ)
    (S : Grassmannian N n) :
    tangentialDerivative (Chapter03.blowUpMap ξ r) y S = r⁻¹ • S.plane.subtype := by
  have hd : fderiv ℝ (Chapter03.blowUpMap ξ r) y =
      r⁻¹ • ContinuousLinearMap.id ℝ (Euclidean N) :=
    (((hasFDerivAt_id y).sub_const ξ).const_smul r⁻¹).fderiv
  apply LinearMap.ext
  intro v
  simp only [tangentialDerivative, hd]
  rfl

theorem tangentialJacobianReal_blowUpMap (ξ y : Euclidean N) {r : ℝ}
    (hr : 0 < r) (S : Grassmannian N n) :
    tangentialJacobianReal (Chapter03.blowUpMap ξ r) y S = r⁻¹ ^ n := by
  simp [tangentialJacobianReal, tangentialDerivative_blowUpMap,
    LinearMap.normDet_smul, Grassmannian.finrank_plane,
    Real.norm_eq_abs, abs_of_pos hr]

theorem transportedPlane_blowUpMap (ξ y : Euclidean N) {r : ℝ}
    (hr : 0 < r) (S : Grassmannian N n) :
    transportedPlane (Chapter03.blowUpMap ξ r) y S = S := by
  apply Grassmannian.eq_of_plane_eq
  rw [transportedPlane_eq_image _ _ _
    (by rw [tangentialJacobianReal_blowUpMap ξ y hr S]; positivity),
    tangentialDerivative_blowUpMap, LinearMap.range_smul _ _ (inv_ne_zero hr.ne'),
    Submodule.range_subtype]

theorem imageMap_blowUpMap (ξ : Euclidean N) {r : ℝ} (hr : 0 < r) :
    imageMap (n := n) (Chapter03.blowUpMap ξ r) = blowUpBundleMap ξ r := by
  funext z
  exact Prod.ext rfl (transportedPlane_blowUpMap ξ z.1 hr z.2)

/-- The explicit rescaled bundle measure, defined also at unused scales. -/
def blowUpMeasure (V : Varifold N n U) (ξ : Euclidean N) (r : ℝ) :
    Measure (Euclidean N × Grassmannian N n) :=
  ENNReal.ofReal (r⁻¹ ^ n) • V.measure.map (blowUpBundleMap ξ r)

/-- The rescaling is the genuine Jacobian-weighted varifold pushforward. -/
theorem blowUpMeasure_eq_pushforward (V : Varifold N n U) (ξ : Euclidean N)
    {r : ℝ} (hr : 0 < r) :
    V.blowUpMeasure ξ r = V.pushforwardMeasure (Chapter03.blowUpMap ξ r) := by
  have hJ : (fun z : Euclidean N × Grassmannian N n ↦
      tangentialJacobian (Chapter03.blowUpMap ξ r) z.1 z.2) =
      fun _ ↦ ENNReal.ofReal (r⁻¹ ^ n) := by
    funext z
    rw [tangentialJacobian, tangentialJacobianReal_blowUpMap ξ z.1 hr z.2]
  rw [pushforwardMeasure, imageMap_blowUpMap ξ hr, hJ, withDensity_const,
    Measure.map_smul _ (continuous_blowUpBundleMap ξ r).measurable.aemeasurable]
  rfl

/-- The spatial marginal of the actual bundle blow-up. -/
def blowUpWeight (V : Varifold N n U) (ξ : Euclidean N) (r : ℝ) :
    Measure (Euclidean N) := (V.blowUpMeasure ξ r).map Prod.fst

theorem blowUpWeight_eq (V : Varifold N n U) (ξ : Euclidean N) (r : ℝ) :
    V.blowUpWeight ξ r =
      ENNReal.ofReal (r⁻¹ ^ n) • V.weight.map (Chapter03.blowUpMap ξ r) := by
  have hb : Measurable (Chapter03.blowUpMap ξ r) := by
    unfold Chapter03.blowUpMap
    fun_prop
  rw [blowUpWeight, blowUpMeasure, Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_map measurable_fst (continuous_blowUpBundleMap ξ r).measurable,
    weight, Measure.map_map hb measurable_fst]
  rfl

/-- Exact preimage of a closed ball under Simon's inverse dilation. -/
theorem preimage_closedBall_blowUpMap (ξ : Euclidean N) {r : ℝ} (hr : 0 < r)
    (R : ℝ) :
    Chapter03.blowUpMap ξ r ⁻¹' closedBall 0 R = closedBall ξ (r * R) := by
  ext y
  simp only [mem_preimage, mem_closedBall, dist_eq_norm, sub_zero,
    Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  rw [← div_eq_inv_mul, div_le_iff₀ hr, mul_comm R r]

/-- The weight of a rescaled ball is the original ball mass times r⁻ⁿ. -/
theorem blowUpWeight_closedBall (V : Varifold N n U) (ξ : Euclidean N)
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    V.blowUpWeight ξ r (closedBall 0 R) =
      ENNReal.ofReal (r⁻¹ ^ n) * V.weight (closedBall ξ (r * R)) := by
  rw [V.blowUpWeight_eq, Measure.smul_apply,
    Measure.map_apply (by unfold Chapter03.blowUpMap; fun_prop) measurableSet_closedBall,
    smul_eq_mul]
  rw [preimage_closedBall_blowUpMap ξ hr]

/-- A genuine varifold on the expanding rescaled open domain. No global
local-finiteness assumption at the original boundary is imposed. -/
def blowUp (V : Varifold N n U) (ξ : Euclidean N) {r : ℝ} (hr : 0 < r) :
    Varifold N n (Chapter04.blowUpHomeomorph ξ hr '' U) where
  isOpen_domain := (Chapter04.blowUpHomeomorph ξ hr).isOpenMap U V.isOpen_domain
  measure := V.blowUpMeasure ξ r
  supported := by
    rw [blowUpMeasure, Measure.smul_apply,
      Measure.map_apply (continuous_blowUpBundleMap ξ r).measurable
        (((Chapter04.blowUpHomeomorph ξ hr).isOpenMap U
          V.isOpen_domain).measurableSet.compl.prod MeasurableSet.univ)]
    have he : blowUpBundleMap (n := n) ξ r ⁻¹'
        ((Chapter04.blowUpHomeomorph ξ hr '' U)ᶜ ×ˢ univ) = Uᶜ ×ˢ univ := by
      ext z
      simp only [mem_preimage, blowUpBundleMap, mem_prod, mem_univ, and_true,
        mem_compl_iff, ← Chapter04.blowUpHomeomorph_apply ξ hr,
        (Chapter04.blowUpHomeomorph ξ hr).injective.mem_set_image]
    rw [he, V.supported, smul_zero]
  finite_on_compact := by
    intro K hK hKU
    rw [blowUpMeasure, Measure.smul_apply,
      Measure.map_apply (continuous_blowUpBundleMap ξ r).measurable
        (hK.measurableSet.prod MeasurableSet.univ)]
    have he : blowUpBundleMap (n := n) ξ r ⁻¹' (K ×ˢ univ) =
        (Chapter04.blowUpHomeomorph ξ hr ⁻¹' K) ×ˢ univ := rfl
    rw [he, smul_eq_mul]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply V.finite_on_compact _ ((Chapter04.blowUpHomeomorph ξ hr).isCompact_preimage.mpr hK)
    intro y hy
    exact (Chapter04.blowUpHomeomorph ξ hr).injective.mem_set_image.mp (hKU hy)

@[simp] theorem weight_blowUp (V : Varifold N n U) (ξ : Euclidean N)
    {r : ℝ} (hr : 0 < r) : (V.blowUp ξ hr).weight = V.blowUpWeight ξ r := rfl

/-- The two analytic hypotheses of (8.5.1), using the constructed
first-variation measure. On positive radii, `r / r^n = r^(1-n)`; the
quotient notation also avoids truncating the exponent in natural numbers. -/
structure IsTangentPoint (V : Varifold N n U) (ξ : Euclidean N) (θ : ℝ≥0∞) : Prop where
  mem_domain : ξ ∈ U
  locallyBoundedFirstVariation : V.HasLocallyBoundedFirstVariation
  density_ne_zero : θ ≠ 0
  density_ne_top : θ ≠ ⊤
  density : Chapter01.HasDimensionalDensityAt V.weight.toOuterMeasure (n : ℝ) univ ξ θ
  variation_decay : Tendsto (fun r : ℝ ↦
    (ENNReal.ofReal r / ENNReal.ofReal (r ^ n)) *
      V.firstVariationRieszMeasure locallyBoundedFirstVariation (closedBall ξ r))
    (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- The rescaled ball mass is exactly the original density quotient at
radius rR, multiplied by the target ball's Euclidean volume. -/
theorem blowUpWeight_closedBall_eq_densityQuotient (V : Varifold N n U)
    (ξ : Euclidean N) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    V.blowUpWeight ξ r (closedBall 0 R) =
      Chapter01.dimensionalDensityQuotient V.weight.toOuterMeasure (n : ℝ) univ ξ (r * R) *
        Chapter01.realUnitBallVolume (n : ℝ) * ENNReal.ofReal (R ^ n) := by
  rw [V.blowUpWeight_closedBall ξ hr R, Chapter01.dimensionalDensityQuotient,
    univ_inter, ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (mul_pos hr hR).le,
    mul_pow, ENNReal.ofReal_mul (pow_pos hr n).le,
    inv_pow, ENNReal.ofReal_inv_of_pos (pow_pos hr n), div_eq_mul_inv,
    ENNReal.mul_inv
      (Or.inl (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)).ne')
      (Or.inl (Chapter01.realUnitBallVolume_ne_top _)),
    ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top)]
  change (ENNReal.ofReal (r ^ n))⁻¹ * V.weight (closedBall ξ (r * R)) =
    V.weight (closedBall ξ (r * R)) *
      ((Chapter01.realUnitBallVolume (n : ℝ))⁻¹ *
        ((ENNReal.ofReal (r ^ n))⁻¹ * (ENNReal.ofReal (R ^ n))⁻¹)) *
      Chapter01.realUnitBallVolume (n : ℝ) * ENNReal.ofReal (R ^ n)
  calc
    _ = ((Chapter01.realUnitBallVolume (n : ℝ))⁻¹ *
          Chapter01.realUnitBallVolume (n : ℝ)) *
        ((ENNReal.ofReal (r ^ n))⁻¹ * V.weight (closedBall ξ (r * R))) *
        ((ENNReal.ofReal (R ^ n))⁻¹ * ENNReal.ofReal (R ^ n)) := by
      rw [ENNReal.inv_mul_cancel (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)).ne'
          (Chapter01.realUnitBallVolume_ne_top _),
        ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (pow_pos hR n)).ne'
          ENNReal.ofReal_ne_top, one_mul, mul_one]
    _ = _ := by ac_rfl

/-- The positive finite density in (8.5.1) gives every fixed-radius
rescaled ball-mass limit. The center is zero in the rescaled coordinates. -/
theorem tendsto_blowUpWeight_closedBall_of_density (V : Varifold N n U)
    (ξ : Euclidean N) {θ : ℝ≥0∞}
    (hd : Chapter01.HasDimensionalDensityAt V.weight.toOuterMeasure (n : ℝ) univ ξ θ)
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun r : ℝ ↦ V.blowUpWeight ξ r (closedBall 0 R)) (𝓝[>] (0 : ℝ))
      (𝓝 (θ * Chapter01.realUnitBallVolume (n : ℝ) * ENNReal.ofReal (R ^ n))) := by
  have hs : Tendsto (fun r : ℝ ↦ r * R) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [zero_mul, id_eq] using
        (tendsto_id.mono_left inf_le_left : Tendsto (fun r : ℝ ↦ r)
          (𝓝[>] (0 : ℝ)) (𝓝 0)).mul_const R
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hR
  have ht := ENNReal.Tendsto.mul_const (ENNReal.Tendsto.mul_const (hd.comp hs)
    (Or.inr (Chapter01.realUnitBallVolume_ne_top (n : ℝ))))
    (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (R ^ n) ≠ ⊤))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (V.blowUpWeight_closedBall_eq_densityQuotient ξ hr hR).symm

theorem IsTangentPoint.tendsto_blowUpWeight_closedBall
    {V : Varifold N n U} {ξ : Euclidean N} {θ : ℝ≥0∞}
    (h : V.IsTangentPoint ξ θ) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun r : ℝ ↦ V.blowUpWeight ξ r (closedBall 0 R)) (𝓝[>] (0 : ℝ))
      (𝓝 (θ * Chapter01.realUnitBallVolume (n : ℝ) * ENNReal.ofReal (R ^ n))) :=
  V.tendsto_blowUpWeight_closedBall_of_density ξ h.density hR

end
end Poincare.SimonGMT.Chapter08.Varifold
