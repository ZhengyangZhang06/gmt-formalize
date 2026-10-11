module

public import Poincare.SimonGMT.Chapter08.StationaryCutoff

@[expose] public section

/-!
# General-varifold stationary monotonicity

The annular tilt identity and finite density limit are obtained from
vanishing first variation in the enclosing ball, not from a monotonicity
identity premise or rectifiability. Simon uses closed balls throughout.

Source: `Simon-gmt new.pdf`, printed pp. 210--211, (8.3.3)--(8.3.4).
-/

open Set Filter MeasureTheory Function Metric
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08.Varifold
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
open Chapter04.RectifiableVarifold
variable {N n : ℕ} {U : Set (Euclidean N)}

theorem integrableOn_truncatedRadialDefect (V : Varifold N n U) (ξ : Euclidean N)
    {c : ℝ} (hc : 0 < c) {ρ : ℝ} (hball : closedBall ξ ρ ⊆ U) :
    IntegrableOn (truncatedRadialDefect ξ c)
      (closedBall ξ ρ ×ˢ (univ : Set (Grassmannian N n))) V.measure := by
  apply (integrableOn_const (C := (c ^ n)⁻¹)
    (V.finite_on_compact _ (isCompact_closedBall ξ ρ) hball)).mono'
  · exact (measurable_truncatedRadialDefect ξ c).aestronglyMeasurable
  · exact Eventually.of_forall (norm_truncatedRadialDefect_le ξ hc)

theorem integrableOn_radialDefect_annulus (V : Varifold N n U) (ξ : Euclidean N)
    {σ : ℝ} (hσ : 0 < σ) {ρ : ℝ} (hball : closedBall ξ ρ ⊆ U) :
    IntegrableOn (fun z : Euclidean N × Grassmannian N n ↦
      z.2.radialNormalSq ξ z.1 / ‖z.1 - ξ‖ ^ n)
      ((closedBall ξ ρ \ closedBall ξ σ) ×ˢ univ) V.measure := by
  apply ((V.integrableOn_truncatedRadialDefect ξ hσ hball).mono_set
    (prod_mono_left sdiff_subset)).congr_fun _
      ((measurableSet_closedBall.diff measurableSet_closedBall).prod MeasurableSet.univ)
  intro z hz
  have hr : σ < ‖z.1 - ξ‖ := by
    simpa only [mem_closedBall, dist_eq_norm, not_le] using hz.1.2
  simp only [truncatedRadialDefect, max_eq_right hr.le]

/-- The real-valued stationary annular identity, with the exact bundle
integral and without any assumption on sphere masses. -/
theorem StationaryOn.stationaryMonotonicity_real {V : Varifold N n U}
    {ξ : Euclidean N} {R : ℝ} (hV : V.StationaryOn (ball ξ R))
    (hball : closedBall ξ R ⊆ U) {σ ρ : ℝ}
    (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hρR : ρ < R) :
    V.weight.real (closedBall ξ ρ) / ρ ^ n - V.weight.real (closedBall ξ σ) / σ ^ n =
      ∫ z in (closedBall ξ ρ \ closedBall ξ σ) ×ˢ (univ : Set (Grassmannian N n)),
        z.2.radialNormalSq ξ z.1 / ‖z.1 - ξ‖ ^ n ∂V.measure := by
  have hρ : 0 < ρ := hσ.trans_le hσρ
  let q := truncatedRadialDefect (n := n) ξ σ
  let G := fun ε t ↦ ∫ z, scaledRadialCutoff ξ (monotonicityCutoff ε) t z.1 * q z ∂V.measure
  have hGρ := V.tendsto_integral_radialCutoff ξ hρ hρR hball
    (measurable_truncatedRadialDefect ξ σ).aestronglyMeasurable
    (fun z _ ↦ norm_truncatedRadialDefect_le ξ hσ z)
  have hGσ := V.tendsto_integral_radialCutoff ξ hσ (hσρ.trans_lt hρR) hball
    (measurable_truncatedRadialDefect ξ σ).aestronglyMeasurable
    (fun z _ ↦ norm_truncatedRadialDefect_le ξ hσ z)
  have hGlim : Tendsto (fun ε ↦ G ε ρ - G ε σ) (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ z in closedBall ξ ρ ×ˢ univ, q z ∂V.measure) -
        ∫ z in closedBall ξ σ ×ˢ univ, q z ∂V.measure)) := hGρ.sub hGσ
  have hFlim := ((V.tendsto_cutoffMass ξ hρ hρR hball).div_const (ρ ^ n)).sub
    ((V.tendsto_cutoffMass ξ hσ (hσρ.trans_lt hρR) hball).div_const (σ ^ n))
  have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hsum : Tendsto (fun ε : ℝ ↦ 1 + ε) (𝓝[>] (0 : ℝ)) (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add hid
  have hAlim : Tendsto (fun ε : ℝ ↦ (1 + ε) ^ n) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [add_zero, one_pow] using hsum.pow n
  have hscale : Tendsto (fun ε : ℝ ↦ ρ * (1 + ε)) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    simpa only [add_zero, mul_one] using hsum.const_mul ρ
  have hsqueeze : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      G ε ρ - G ε σ ≤ V.cutoffMass ξ (monotonicityCutoff ε) ρ / ρ ^ n -
        V.cutoffMass ξ (monotonicityCutoff ε) σ / σ ^ n ∧
      V.cutoffMass ξ (monotonicityCutoff ε) ρ / ρ ^ n -
        V.cutoffMass ξ (monotonicityCutoff ε) σ / σ ^ n ≤
          (1 + ε) ^ n * (G ε ρ - G ε σ) := by
    filter_upwards [self_mem_nhdsWithin, hscale.eventually (gt_mem_nhds hρR)] with ε hε hεR
    exact hV.cutoff_squeeze hε hσ hσρ hεR hball
  have heq : V.weight.real (closedBall ξ ρ) / ρ ^ n -
        V.weight.real (closedBall ξ σ) / σ ^ n =
      (∫ z in closedBall ξ ρ ×ˢ univ, q z ∂V.measure) -
        ∫ z in closedBall ξ σ ×ˢ univ, q z ∂V.measure := by
    apply le_antisymm
    · simpa only [one_mul] using
        le_of_tendsto_of_tendsto hFlim (hAlim.mul hGlim) (hsqueeze.mono fun _ h ↦ h.2)
    · exact le_of_tendsto_of_tendsto hGlim hFlim (hsqueeze.mono fun _ h ↦ h.1)
  rw [← setIntegral_sdiff (measurableSet_closedBall.prod MeasurableSet.univ)
    (V.integrableOn_truncatedRadialDefect ξ hσ
      ((closedBall_subset_closedBall hρR.le).trans hball))
    (prod_mono_left (closedBall_subset_closedBall hσρ))] at heq
  simp only [prod_sdiff_prod, sdiff_self, prod_empty, empty_union] at heq
  rw [heq]
  apply setIntegral_congr_fun
    ((measurableSet_closedBall.diff measurableSet_closedBall).prod MeasurableSet.univ)
  intro z hz
  have hr : σ < ‖z.1 - ξ‖ := by
    simpa only [mem_closedBall, dist_eq_norm, not_le] using hz.1.2
  simp only [truncatedRadialDefect, max_eq_right hr.le]

/-- Dimension-normalized closed-ball mass, before division by `ωₙ`. -/
def normalizedBallMass (V : Varifold N n U) (ξ : Euclidean N) (ρ : ℝ) : ℝ≥0∞ :=
  V.weight (closedBall ξ ρ) / ENNReal.ofReal (ρ ^ n)

theorem normalizedBallMass_ne_top (V : Varifold N n U) (ξ : Euclidean N)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall ξ ρ ⊆ U) :
    V.normalizedBallMass ξ ρ ≠ ∞ := by
  apply ENNReal.div_ne_top (V.weight_finite_on_compact _ (isCompact_closedBall ξ ρ) hball)
  exact (ENNReal.ofReal_pos.mpr (pow_pos hρ n)).ne'

def annularMonotonicityDefect (V : Varifold N n U) (ξ : Euclidean N) (σ ρ : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in (closedBall ξ ρ \ closedBall ξ σ) ×ˢ (univ : Set (Grassmannian N n)),
    ENNReal.ofReal (z.2.radialNormalSq ξ z.1 / ‖z.1 - ξ‖ ^ n) ∂V.measure

theorem ofReal_normalizedBallMass_real (V : Varifold N n U) (ξ : Euclidean N)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall ξ ρ ⊆ U) :
    ENNReal.ofReal (V.weight.real (closedBall ξ ρ) / ρ ^ n) = V.normalizedBallMass ξ ρ := by
  rw [normalizedBallMass, ENNReal.ofReal_div_of_pos (pow_pos hρ n), measureReal_def,
    ENNReal.ofReal_toReal (V.weight_finite_on_compact _ (isCompact_closedBall ξ ρ) hball)]

/-- The nonnegative form of the stationary annular identity. -/
theorem StationaryOn.stationaryMonotonicity {V : Varifold N n U}
    {ξ : Euclidean N} {R : ℝ} (hV : V.StationaryOn (ball ξ R))
    (hball : closedBall ξ R ⊆ U) {σ ρ : ℝ}
    (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hρR : ρ < R) :
    V.normalizedBallMass ξ σ + V.annularMonotonicityDefect ξ σ ρ = V.normalizedBallMass ξ ρ := by
  have hρ := hσ.trans_le hσρ
  have heq := hV.stationaryMonotonicity_real hball hσ hσρ hρR
  have hnonneg : ∀ z : Euclidean N × Grassmannian N n,
      0 ≤ z.2.radialNormalSq ξ z.1 / ‖z.1 - ξ‖ ^ n :=
    fun z ↦ div_nonneg (z.2.radialNormalSq_nonneg ξ z.1) (pow_nonneg (norm_nonneg _) n)
  have hintnonneg : 0 ≤ ∫ z in (closedBall ξ ρ \ closedBall ξ σ) ×ˢ univ,
      z.2.radialNormalSq ξ z.1 / ‖z.1 - ξ‖ ^ n ∂V.measure := integral_nonneg hnonneg
  have hsum : V.weight.real (closedBall ξ σ) / σ ^ n +
      (∫ z in (closedBall ξ ρ \ closedBall ξ σ) ×ˢ univ,
        z.2.radialNormalSq ξ z.1 / ‖z.1 - ξ‖ ^ n ∂V.measure) =
      V.weight.real (closedBall ξ ρ) / ρ ^ n := by linarith
  have hρU := (closedBall_subset_closedBall hρR.le).trans hball
  have hσU := (closedBall_subset_closedBall hσρ).trans hρU
  have h := congrArg ENNReal.ofReal hsum
  have hmass : 0 ≤ V.weight.real (closedBall ξ σ) / σ ^ n :=
    div_nonneg ENNReal.toReal_nonneg (pow_pos hσ n).le
  rw [ENNReal.ofReal_add hmass hintnonneg,
    V.ofReal_normalizedBallMass_real ξ hσ hσU, V.ofReal_normalizedBallMass_real ξ hρ hρU,
    ofReal_integral_eq_lintegral_ofReal (V.integrableOn_radialDefect_annulus ξ hσ hρU)
      (Eventually.of_forall hnonneg)] at h
  exact h

theorem StationaryOn.normalizedBallMass_monotoneOn {V : Varifold N n U}
    {ξ : Euclidean N} {R : ℝ} (hV : V.StationaryOn (ball ξ R))
    (hball : closedBall ξ R ⊆ U) : MonotoneOn (V.normalizedBallMass ξ) (Ioo 0 R) := by
  intro σ hσ ρ hρ hσρ
  rw [← hV.stationaryMonotonicity hball hσ.1 hσρ hρ.2]
  exact le_add_right le_rfl

/-- The stationary density ratio, before multiplication by `ωₙ⁻¹`.
The following theorem proves this is an actual density limit. -/
def stationaryDensityRatio (V : Varifold N n U) (ξ : Euclidean N) (R : ℝ) : ℝ≥0∞ :=
  sInf (V.normalizedBallMass ξ '' Ioo 0 R)

theorem stationaryDensityRatio_le (V : Varifold N n U) {ξ : Euclidean N} {R ρ : ℝ}
    (hρ : ρ ∈ Ioo 0 R) : V.stationaryDensityRatio ξ R ≤ V.normalizedBallMass ξ ρ :=
  sInf_le (mem_image_of_mem _ hρ)

theorem StationaryOn.tendsto_normalizedBallMass_atRight {V : Varifold N n U}
    {ξ : Euclidean N} {R : ℝ} (hV : V.StationaryOn (ball ξ R))
    (hR : 0 < R) (hball : closedBall ξ R ⊆ U) :
    Tendsto (V.normalizedBallMass ξ) (𝓝[>] (0 : ℝ)) (𝓝 (V.stationaryDensityRatio ξ R)) := by
  apply MonotoneOn.tendsto_nhdsWithin_Ioo_right
    (f := V.normalizedBallMass ξ) (x := (0 : ℝ)) (y := R)
  · exact ⟨R / 2, by linarith, by linarith⟩
  · exact hV.normalizedBallMass_monotoneOn hball
  · exact ⟨0, by rintro y ⟨ρ, hρ, rfl⟩; exact bot_le⟩

theorem stationaryDensityRatio_ne_top (V : Varifold N n U) {ξ : Euclidean N} {R : ℝ}
    (hR : 0 < R) (hball : closedBall ξ R ⊆ U) : V.stationaryDensityRatio ξ R ≠ ∞ := by
  apply ne_top_of_le_ne_top (V.normalizedBallMass_ne_top ξ (half_pos hR)
    ((closedBall_subset_closedBall (half_le_self hR.le)).trans hball))
  exact V.stationaryDensityRatio_le ⟨half_pos hR, half_lt_self hR⟩

end
end Poincare.SimonGMT.Chapter08.Varifold
