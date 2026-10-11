module

public import Poincare.SimonGMT.Chapter02.AreaParametrization
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

public section

/-!
# Sharp Hausdorff estimates for nonlinear linear approximations

These estimates compare a nonlinear map with an injective linear map in
arbitrary codimension. The comparison factor tends to the genuine metric
Jacobian as the Lipschitz error tends to zero.
-/

open Function MeasureTheory Module Set Filter Metric
open scoped ENNReal NNReal Topology

namespace Poincare.SimonGMT.Chapter02

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The metric Jacobian of a linear map depends continuously on the map. -/
theorem continuous_normDet : Continuous (fun L : E →L[ℝ] F ↦ L.normDet) := by
  have heq : (fun L : E →L[ℝ] F ↦ L.normDet) =
      fun L ↦ Real.sqrt ((L.adjoint ∘L L).det) := by
    funext L
    rw [← L.normDet_sq]
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using (Real.sqrt_sq L.normDet_nonneg).symm
  rw [heq]
  exact Real.continuous_sqrt.comp
    (ContinuousLinearMap.continuous_det.comp
      (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]

/-- The totalized area Jacobian is Borel measurable, including at points
where the derivative does not exist. -/
theorem measurable_areaJacobianAt (f : E → F) : Measurable (areaJacobianAt f) := by
  have heq : areaJacobianAt f = fun x ↦ (fderiv ℝ f x).normDet := by
    funext x
    exact areaJacobianAt_eq_normDet f x
  rw [heq]
  exact continuous_normDet.measurable.comp (measurable_fderiv ℝ f)

/-- A comparison of pairwise distances gives a comparison of the measures
of the two images. No measurability of the source subset is needed. -/
theorem euclideanHausdorffMeasure_image_le_of_dist_le
    {f g : E → F} {s : Set E} {K : ℝ≥0}
    (hg : InjOn g s)
    (hfg : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist (g x) (g y))
    (d : ℕ) :
    μHE[d] (f '' s) ≤ (K : ℝ≥0∞) ^ d * μHE[d] (g '' s) := by
  let h : F → F := f ∘ invFunOn g s
  have hh : LipschitzOnWith K h (g '' s) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simpa only [h, comp_apply, hg.leftInvOn_invFunOn hx,
      hg.leftInvOn_invFunOn hy] using hfg x hx y hy
  have himage : h '' (g '' s) = f '' s := by
    rw [show h = f ∘ invFunOn g s from rfl, image_comp,
      hg.invFunOn_image Subset.rfl]
  simpa only [himage] using euclideanHausdorffMeasure_image_le_of_lipschitzOn d hh

/-- The upper sharp comparison for a nonlinear approximation to an
injective linear map. The extra factor is `(1 + δ K)^n`. -/
theorem ApproximatesLinearOn.euclideanHausdorffMeasure_image_le
    {f : E → F} {L : E →L[ℝ] F} {s : Set E} {δ K : ℝ≥0}
    (hf : _root_.ApproximatesLinearOn f L s δ) (hL : AntilipschitzWith K L) :
    μHE[finrank ℝ E] (f '' s) ≤
      ((1 + δ * K : ℝ≥0) : ℝ≥0∞) ^ finrank ℝ E *
        (ENNReal.ofReal L.normDet * μHE[finrank ℝ E] s) := by
  rw [← L.toLinearMap.euclideanHausdorffMeasure_image]
  apply euclideanHausdorffMeasure_image_le_of_dist_le hL.injective.injOn
  intro x hx y hy
  have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
    simpa only [dist_eq_norm] using hL.le_mul_dist x y
  have herror : ‖f x - f y - (L x - L y)‖ ≤
      (δ : ℝ) * K * ‖L x - L y‖ := by
    calc
      _ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hf x hx y hy
      _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
      _ = _ := by ring
  simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
  calc
    ‖f x - f y‖ ≤ ‖f x - f y - (L x - L y)‖ + ‖L x - L y‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ :=
      add_le_add herror le_rfl
    _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring

/-- The reverse comparison has factor `(1 - δ K)⁻ⁿ`. In particular, the
linear model is recovered sharply as `δ` tends to zero. -/
theorem ApproximatesLinearOn.le_euclideanHausdorffMeasure_image
    {f : E → F} {L : E →L[ℝ] F} {s : Set E} {δ K : ℝ≥0}
    (hf : _root_.ApproximatesLinearOn f L s δ) (hL : AntilipschitzWith K L)
    (hδ : δ * K < 1) :
    ENNReal.ofReal L.normDet * μHE[finrank ℝ E] s ≤
      (((1 - δ * K)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ finrank ℝ E *
        μHE[finrank ℝ E] (f '' s) := by
  have hδR : (δ : ℝ) * K < 1 := hδ
  have hdist : ∀ x ∈ s, ∀ y ∈ s, dist (L x) (L y) ≤
      ((1 - δ * K)⁻¹ : ℝ≥0) * dist (f x) (f y) := by
    intro x hx y hy
    have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
      simpa only [dist_eq_norm] using hL.le_mul_dist x y
    have herror : ‖f x - f y - (L x - L y)‖ ≤
        (δ : ℝ) * K * ‖L x - L y‖ := by
      calc
        _ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hf x hx y hy
        _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
        _ = _ := by ring
    have htriangle : ‖L x - L y‖ ≤
        ‖f x - f y‖ + ‖f x - f y - (L x - L y)‖ := by
      simpa only [norm_sub_rev, add_comm] using
        (norm_le_norm_sub_add (L x - L y) (f x - f y))
    simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδ.le,
      NNReal.coe_one, NNReal.coe_mul, inv_mul_eq_div]
    apply (le_div_iff₀ (sub_pos.mpr hδR)).mpr
    nlinarith
  have hfinj : InjOn f s := by
    intro x hx y hy hxy
    apply hL.injective
    apply dist_le_zero.mp
    simpa only [hxy, dist_self, mul_zero] using hdist x hx y hy
  rw [← L.toLinearMap.euclideanHausdorffMeasure_image]
  exact euclideanHausdorffMeasure_image_le_of_dist_le hfinj hdist _

/-- Uniform relative image estimates near any injective linear map. The
constant `q` can be chosen arbitrarily close to one, independently of the
source subset and nonlinear map. -/
theorem exists_radius_area_comparison
    (L : E →L[ℝ] F) (hL : Injective L) {q : ℝ≥0} (hq : 1 < q) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ (s : Set E) (f : E → F),
      _root_.ApproximatesLinearOn f L s δ →
        (μHE[finrank ℝ E] (f '' s) ≤
          q * (ENNReal.ofReal L.normDet * μHE[finrank ℝ E] s)) ∧
        (ENNReal.ofReal L.normDet * μHE[finrank ℝ E] s ≤
          q * μHE[finrank ℝ E] (f '' s)) := by
  obtain ⟨K, _, hK⟩ := L.toLinearMap.exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr hL)
  have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝 0, δ * K < 1 := by
    exact (continuousAt_id.mul continuousAt_const).eventually_lt
      continuousAt_const (by simp)
  have hupper : ∀ᶠ δ : ℝ≥0 in 𝓝 0, (1 + δ * K) ^ finrank ℝ E < q := by
    exact ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
      continuousAt_const (by simpa using hq)
  have hlower : ∀ᶠ δ : ℝ≥0 in 𝓝 0, ((1 - δ * K)⁻¹) ^ finrank ℝ E < q := by
    apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
    apply ContinuousAt.pow
    apply ContinuousAt.inv₀
    · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
    · simp
  have hevent : ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0,
      0 < δ ∧ δ * K < 1 ∧ (1 + δ * K) ^ finrank ℝ E < q ∧
        ((1 - δ * K)⁻¹) ^ finrank ℝ E < q := by
    filter_upwards [self_mem_nhdsWithin,
      hsmall.filter_mono nhdsWithin_le_nhds, hupper.filter_mono nhdsWithin_le_nhds,
      hlower.filter_mono nhdsWithin_le_nhds] with δ hδ hsmall hupper hlower
    exact ⟨hδ, hsmall, hupper, hlower⟩
  obtain ⟨δ, hδ, hδsmall, hδupper, hδlower⟩ := hevent.exists
  refine ⟨δ, hδ, fun s f hf ↦ ⟨?_, ?_⟩⟩
  · refine (ApproximatesLinearOn.euclideanHausdorffMeasure_image_le hf hK).trans ?_
    gcongr
    exact_mod_cast hδupper.le
  · refine (ApproximatesLinearOn.le_euclideanHausdorffMeasure_image hf hK hδsmall).trans ?_
    gcongr
    exact_mod_cast hδlower.le

/-- Choose one approximation radius controlling both the nonlinear image
measure and the metric Jacobian of nearby derivatives. -/
theorem exists_radius_area_and_jacobian_comparison
    (L : E →L[ℝ] F) (hL : Injective L) {q : ℝ≥0} (hq : 1 < q) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      (∀ B : E →L[ℝ] F, ‖B - L‖ ≤ δ →
        ENNReal.ofReal B.normDet ≤ q * ENNReal.ofReal L.normDet ∧
        ENNReal.ofReal L.normDet ≤ q * ENNReal.ofReal B.normDet) ∧
      (∀ (s : Set E) (f : E → F), _root_.ApproximatesLinearOn f L s δ →
        μHE[finrank ℝ E] (f '' s) ≤
            q * (ENNReal.ofReal L.normDet * μHE[finrank ℝ E] s) ∧
          ENNReal.ofReal L.normDet * μHE[finrank ℝ E] s ≤
            q * μHE[finrank ℝ E] (f '' s)) := by
  have hJ : 0 < L.normDet := by
    apply lt_of_le_of_ne L.normDet_nonneg
    exact Ne.symm ((L.toLinearMap.normDet_ne_zero_tfae.out 5 1).mp hL)
  have hqR : (1 : ℝ) < q := hq
  have hmul : L.normDet < (q : ℝ) * L.normDet := by nlinarith
  have hnear : ∀ᶠ B : E →L[ℝ] F in 𝓝 L,
      B.normDet < (q : ℝ) * L.normDet ∧ L.normDet < (q : ℝ) * B.normDet :=
    (continuous_normDet.continuousAt.eventually_lt continuousAt_const hmul).and
      (continuousAt_const.eventually_lt
        (continuousAt_const.mul continuous_normDet.continuousAt) hmul)
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨δ₀, hδ₀, harea⟩ := exists_radius_area_comparison L hL hq
  let δ₁ : ℝ≥0 := ⟨ε / 2, (half_pos hε).le⟩
  refine ⟨min δ₀ δ₁, lt_min hδ₀ (half_pos hε), ?_, ?_⟩
  · intro B hB
    have hdist : dist B L < ε := by
      rw [dist_eq_norm]
      exact hB.trans_lt (lt_of_le_of_lt (by exact_mod_cast min_le_right δ₀ δ₁)
        (half_lt_self hε))
    obtain ⟨hupper, hlower⟩ := hnear hdist
    constructor
    · simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg q), ENNReal.ofReal_coe_nnreal] using
        ENNReal.ofReal_le_ofReal hupper.le
    · simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg q), ENNReal.ofReal_coe_nnreal] using
        ENNReal.ofReal_le_ofReal hlower.le
  · intro s f hf
    exact harea s f (hf.mono_num (min_le_left _ _))

end
end Poincare.SimonGMT.Chapter02
