module

public import Poincare.SimonGMT.Chapter08.StationaryMonotonicity

@[expose] public section

/-!
# The radial rigidity step in the tangent-cone argument

For a stationary general varifold, equality of all origin-centered mass
ratios forces the radial vector to belong to every support plane. This
is the nonrectifiable equality case of monotonicity used between
(8.5.2) and (8.5.3). No radial-tangency premise is assumed.

Source: `Simon-gmt new.pdf`, printed p. 215.
-/

open Set Filter MeasureTheory Function Metric
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08.Varifold
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {N n : ℕ} {C : Varifold N n (univ : Set (Euclidean N))}

/-- A constant ball-mass ratio makes every nonnegative annular tilt
integral zero. Finiteness is derived from compact finiteness of C. -/
theorem Stationary.annularMonotonicityDefect_eq_zero_of_constant_mass_ratio
    (hC : C.Stationary) {c : ℝ≥0∞}
    (hmass : ∀ R : ℝ, 0 < R → C.normalizedBallMass 0 R = c)
    {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) :
    C.annularMonotonicityDefect 0 σ ρ = 0 := by
  have hρ := hσ.trans_le hσρ
  have hcf : c ≠ ⊤ := by
    rw [← hmass ρ hρ]
    exact C.normalizedBallMass_ne_top 0 hρ (subset_univ _)
  have hi := (hC.stationaryOn (ball 0 (ρ + 1))).stationaryMonotonicity
    (subset_univ _) hσ hσρ (by linarith : ρ < ρ + 1)
  rw [hmass σ hσ, hmass ρ hρ] at hi
  apply (ENNReal.add_left_inj hcf).mp
  calc
    C.annularMonotonicityDefect 0 σ ρ + c = c + C.annularMonotonicityDefect 0 σ ρ := add_comm _ _
    _ = c := hi
    _ = 0 + c := (zero_add c).symm

/-- Vanishing annular defect forces zero normal-radial projection
almost everywhere on the annulus, without a sphere-nullness premise. -/
theorem Stationary.ae_radialNormalSq_eq_zero_on_annulus_of_constant_mass_ratio
    (hC : C.Stationary) {c : ℝ≥0∞}
    (hmass : ∀ R : ℝ, 0 < R → C.normalizedBallMass 0 R = c)
    {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) :
    ∀ᵐ z ∂C.measure, z.1 ∈ closedBall 0 ρ \ closedBall 0 σ →
      z.2.radialNormalSq 0 z.1 = 0 := by
  have hz := hC.annularMonotonicityDefect_eq_zero_of_constant_mass_ratio hmass hσ hσρ
  have hm : Measurable (fun z : Euclidean N × Grassmannian N n ↦
      ENNReal.ofReal (z.2.radialNormalSq 0 z.1 / ‖z.1 - 0‖ ^ n)) :=
    ((Grassmannian.measurable_radialNormalSq 0).div
      ((measurable_fst.sub_const 0).norm.pow_const n)).ennreal_ofReal
  have hAE := (lintegral_eq_zero_iff hm).mp hz
  change ∀ᵐ z ∂C.measure.restrict ((closedBall 0 ρ \ closedBall 0 σ) ×ˢ univ),
    ENNReal.ofReal (z.2.radialNormalSq 0 z.1 / ‖z.1 - 0‖ ^ n) = 0 at hAE
  rw [ae_restrict_iff'
    ((measurableSet_closedBall.diff measurableSet_closedBall).prod MeasurableSet.univ)] at hAE
  filter_upwards [hAE] with z hz hzann
  have hpos : 0 < ‖z.1 - 0‖ ^ n := by
    apply pow_pos
    have hs : σ < ‖z.1 - 0‖ := by
      simpa only [mem_closedBall, dist_eq_norm, not_le] using hzann.2
    exact hσ.trans hs
  have hn := ENNReal.ofReal_eq_zero.mp (hz ⟨hzann, mem_univ _⟩)
  have hle : z.2.radialNormalSq 0 z.1 ≤ 0 := by
    have := (div_le_iff₀ hpos).mp hn
    simpa only [zero_mul] using this
  exact le_antisymm hle (z.2.radialNormalSq_nonneg 0 z.1)

/-- Countably many annuli cover every nonzero point; the normalized
normal projection is defined to be zero at the origin as well. -/
theorem Stationary.ae_radialNormalSq_eq_zero_of_constant_mass_ratio
    (hC : C.Stationary) {c : ℝ≥0∞}
    (hmass : ∀ R : ℝ, 0 < R → C.normalizedBallMass 0 R = c) :
    ∀ᵐ z ∂C.measure, z.2.radialNormalSq 0 z.1 = 0 := by
  have hk : ∀ k : ℕ, ∀ᵐ z ∂C.measure,
      z.1 ∈ closedBall 0 ((k : ℝ) + 1) \ closedBall 0 ((k : ℝ) + 1)⁻¹ →
        z.2.radialNormalSq 0 z.1 = 0 := by
    intro k
    have hp : 0 < (k : ℝ) + 1 := by positivity
    apply hC.ae_radialNormalSq_eq_zero_on_annulus_of_constant_mass_ratio hmass
      (inv_pos.mpr hp)
    have hone : 1 ≤ (k : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg k)
    exact (inv_le_one₀ hp).mpr hone |>.trans hone
  have hall := (ae_all_iff.mpr hk)
  filter_upwards [hall] with z hz
  by_cases hz0 : z.1 = 0
  · simp [Grassmannian.radialNormalSq, Grassmannian.normalProject, hz0]
  have hnorm : 0 < ‖z.1‖ := norm_pos_iff.mpr hz0
  obtain ⟨k, hk⟩ := exists_nat_gt (max ‖z.1‖ ‖z.1‖⁻¹)
  have hup : ‖z.1‖ < (k : ℝ) + 1 := by
    have := (le_max_left ‖z.1‖ ‖z.1‖⁻¹).trans_lt hk
    linarith
  have hlow : ((k : ℝ) + 1)⁻¹ < ‖z.1‖ := by
    apply (inv_lt_comm₀ (by positivity : 0 < (k : ℝ) + 1) hnorm).mpr
    have := (le_max_right ‖z.1‖ ‖z.1‖⁻¹).trans_lt hk
    linarith
  apply hz k
  simp only [Set.mem_sdiff, mem_closedBall, dist_zero_right, not_le]
  exact ⟨hup.le, hlow⟩

/-- The unnormalized radial normal projection vanishes almost everywhere. -/
theorem Stationary.ae_normalProject_eq_zero_of_constant_mass_ratio
    (hC : C.Stationary) {c : ℝ≥0∞}
    (hmass : ∀ R : ℝ, 0 < R → C.normalizedBallMass 0 R = c) :
    ∀ᵐ z ∂C.measure, z.2.normalProject z.1 = 0 := by
  filter_upwards [hC.ae_radialNormalSq_eq_zero_of_constant_mass_ratio hmass] with z hz
  have he := z.2.norm_normalProject_radial_sq 0 z.1
  rw [sub_zero, hz, mul_zero] at he
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp he)

/-- Continuity upgrades the almost-everywhere result to every point of
the actual Grassmann-bundle support. -/
theorem Stationary.radial_mem_plane_of_mem_support_of_constant_mass_ratio
    (hC : C.Stationary) {c : ℝ≥0∞}
    (hmass : ∀ R : ℝ, 0 < R → C.normalizedBallMass 0 R = c)
    {z : Euclidean N × Grassmannian N n} (hz : z ∈ C.measure.support) :
    z.1 ∈ z.2.plane := by
  have hc0 : Continuous (fun w : Euclidean N × Grassmannian N n ↦
      (w.2, w.1)) := continuous_snd.prodMk continuous_fst
  have hc1 := (Grassmannian.continuous_normalProject (N := N) (n := n)).comp hc0
  have hc : IsClosed {w : Euclidean N × Grassmannian N n | w.2.normalProject w.1 = 0} :=
    isClosed_eq hc1 (continuous_const (y := (0 : Euclidean N)))
  have hs : z.2.normalProject z.1 = 0 :=
    (Measure.support_subset_of_isClosed (μ := C.measure) hc
      (hC.ae_normalProject_eq_zero_of_constant_mass_ratio hmass)) hz
  have hp : z.2.project z.1 = z.1 := by
    rw [Grassmannian.normalProject_eq_sub, sub_eq_zero] at hs
    exact hs.symm
  rw [← hp]
  exact ⟨z.1, rfl⟩

end
end Poincare.SimonGMT.Chapter08.Varifold
