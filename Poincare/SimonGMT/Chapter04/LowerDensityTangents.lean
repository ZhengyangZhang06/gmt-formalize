module

public import Poincare.SimonGMT.Chapter04.TangentDensity
import all Poincare.SimonGMT.Chapter03.Rectifiable

@[expose] public section

/-!
# Lower density from approximate tangents, without a curvature bound

For the geometric input to Simon (5.7), bounded mean curvature is not
available. The result below therefore proves a genuine lower-limit
statement, not existence of a finite density or density=multiplicity.
-/

open Filter Function Metric Set MeasureTheory
open scoped CompactlySupported ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

/-- The normalized mass is eventually above every number less than one
at an actual approximate-tangent point with `θ≥1`. There is no curvature
hypothesis, and no density limit is assumed. -/
theorem eventually_lt_densityQuotient_of_approximateTangent
    {U : Set E} (hU : IsOpen U) (hn : 0 < n)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    {ξ : E} (hξ : ξ ∈ U) {P : Submodule ℝ E}
    (hP : Chapter03.HasApproximateTangentSpaceAt n V.carrier ξ P)
    {c : ℝ} (hc : c < 1) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, c < V.weight.real (closedBall ξ r) /
      ((Chapter01.realUnitBallVolume (n : ℝ)).toReal * r ^ n) := by
  let ω := (Chapter01.realUnitBallVolume (n : ℝ)).toReal
  have hω : 0 < ω := ENNReal.toReal_pos
    (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)).ne'
    (Chapter01.realUnitBallVolume_ne_top _)
  have hεlim : Tendsto (fun ε : ℝ ↦ c * (1 + ε) ^ n)
      (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
    simpa only [id_eq, add_zero, one_pow, mul_one] using
      ((hone.add (tendsto_id.mono_left inf_le_left :
        Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0))).pow n).const_mul c
  obtain ⟨ε, heps, hε⟩ := ((hεlim.eventually (gt_mem_nhds hc)).and self_mem_nhdsWithin).exists
  let A := 1 + ε
  have hA : 0 < A := by dsimp [A]; linarith
  have hgap : c * ω * A ^ n <
      ∫ x in (P : Set E), tangentDensityCutoff ε hε x
        ∂Measure.euclideanHausdorffMeasure n := by
    calc
      c * ω * A ^ n = (c * A ^ n) * ω := by ring
      _ < ω := by simpa only [one_mul] using mul_lt_mul_of_pos_right heps hω
      _ ≤ _ := unitBallVolume_le_integral_tangentDensityCutoff hn hP.finrank_eq hε
  have hrA : Tendsto (fun r : ℝ ↦ r / A) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [zero_div, id_eq] using
        (tendsto_id.mono_left inf_le_left : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0)).div_const A
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact div_pos hr hA
  have hevent := ((hP.2 (tangentDensityCutoff (E := E) ε hε)).comp hrA).eventually
    (lt_mem_nhds hgap)
  obtain ⟨R, hR, hBR⟩ := exists_pos_closedBall_subset hU hξ
  filter_upwards [hevent, Ioc_mem_nhdsGT hR] with r hrI hr
  have hball : closedBall ξ ((r / A) * A) ⊆ U := by
    rw [div_mul_cancel₀ _ hA.ne']
    exact (closedBall_subset_closedBall hr.2).trans hBR
  have hcomp := V.integral_blowUp_le_scaled_weight hU.measurableSet hθ ξ
    (div_pos hr.1 hA) hball (tangentDensityCutoff ε hε)
    (tangentDensityCutoff_mem_Icc hε) (fun _ hx ↦ tangentDensityCutoff_eq_zero hε hx)
  rw [div_mul_cancel₀ _ hA.ne'] at hcomp
  have heq : (r / A)⁻¹ ^ n * V.weight.real (closedBall ξ r) =
      (A ^ n * ω) * (V.weight.real (closedBall ξ r) / (ω * r ^ n)) := by
    simp only [inv_pow, div_pow]
    field_simp [hr.1.ne', hA.ne', hω.ne']
  rw [heq] at hcomp
  have hlt := hrI.trans_le hcomp
  have hfactor : 0 < A ^ n * ω := mul_pos (pow_pos hA _) hω
  change c < V.weight.real (closedBall ξ r) / (ω * r ^ n)
  nlinarith

/-- The curvature-free geometric lower-density input holds almost
everywhere for the actual varifold weight. -/
theorem eventually_lt_densityQuotient_ae_of_multiplicity
    {U : Set E} (hU : IsOpen U) (hn : 0 < n)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x) :
    ∀ᵐ ξ ∂V.weight.restrict U, ∀ c : ℝ, c < 1 →
      ∀ᶠ r : ℝ in 𝓝[>] 0, c < V.weight.real (closedBall ξ r) /
        ((Chapter01.realUnitBallVolume (n : ℝ)).toReal * r ^ n) := by
  rw [ae_restrict_iff' hU.measurableSet]
  filter_upwards [V.ae_weight_of_ae_restrict V.approximate_tangent] with ξ hξ hξU c hc
  exact V.eventually_lt_densityQuotient_of_approximateTangent hU hn hθ hξU hξ hc

/-- A continuous weight whose value is at least one at the
centre has weighted lower density at least one there. The conclusion is
expressed as eventual lower bounds, avoiding an unproved limit assertion. -/
theorem eventually_lt_weightedBallAverage_of_one_le_value
    {U : Set E} (hU : IsOpen U) (hn : 0 < n)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    {h : E → ℝ} (hh : ContinuousOn h U) {ξ : E} (hξ : ξ ∈ U)
    {P : Submodule ℝ E} (hP : Chapter03.HasApproximateTangentSpaceAt n V.carrier ξ P)
    (hvalue : 1 ≤ h ξ) {c : ℝ} (hc : c < 1) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, c < V.weightedBallAverage ξ h r := by
  obtain ⟨t, ht, ht1⟩ := exists_between (max_lt hc zero_lt_one)
  have ht0 : 0 < t := (le_max_right c 0).trans_lt ht
  have hct : c < t := (le_max_left c 0).trans_lt ht
  have hnear : {x | t < h x} ∈ 𝓝 ξ :=
    (hh.continuousAt (hU.mem_nhds hξ)).preimage_mem_nhds (lt_mem_nhds (ht1.trans_le hvalue))
  obtain ⟨R, hR, hBR⟩ : ∃ R : ℝ, 0 < R ∧ closedBall ξ R ⊆ {x | t < h x} ∩ U :=
    nhds_basis_closedBall.mem_iff.mp (inter_mem hnear (hU.mem_nhds hξ))
  have hquot := V.eventually_lt_densityQuotient_of_approximateTangent hU hn hθ hξ hP
    ((div_lt_one ht0).mpr hct)
  filter_upwards [hquot, Ioc_mem_nhdsGT hR] with r hratio hr
  have hball : closedBall ξ r ⊆ U := fun x hx ↦
    (hBR ((closedBall_subset_closedBall hr.2) hx)).2
  have hth : ∀ x ∈ closedBall ξ r, t ≤ h x := fun x hx ↦
    (hBR ((closedBall_subset_closedBall hr.2) hx)).1.le
  have hfinite : V.weight (closedBall ξ r) < ∞ := (isCompact_closedBall ξ r).measure_lt_top
  have hhi : IntegrableOn h (closedBall ξ r) V.weight :=
    (hh.mono hball).integrableOn_compact (isCompact_closedBall ξ r)
  have hint := setIntegral_mono_on (μ := V.weight)
    (integrableOn_const hfinite.ne) hhi
    measurableSet_closedBall hth
  have hint' : V.weight.real (closedBall ξ r) * t ≤ ∫ x in closedBall ξ r, h x ∂V.weight := by
    simpa only [integral_const, smul_eq_mul, Measure.restrict_apply_univ, measureReal_def] using hint
  have hω : 0 < (Chapter01.realUnitBallVolume (n : ℝ)).toReal := ENNReal.toReal_pos
    (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)).ne'
    (Chapter01.realUnitBallVolume_ne_top _)
  have havg : t * (V.weight.real (closedBall ξ r) /
      ((Chapter01.realUnitBallVolume (n : ℝ)).toReal * r ^ n)) ≤ V.weightedBallAverage ξ h r := by
    rw [weightedBallAverage]
    calc
      _ = (V.weight.real (closedBall ξ r) * t) /
          ((Chapter01.realUnitBallVolume (n : ℝ)).toReal * r ^ n) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hint' (mul_pos hω (pow_pos hr.1 _)).le
  have hlt := (div_lt_iff₀ ht0).mp hratio
  rw [mul_comm _ t] at hlt
  exact hlt.trans_le havg

/-- The weighted lower-density input for the superlevel set `{h≥1}` in
Simon (5.7), obtained directly from the geometric varifold hypotheses. -/
theorem eventually_lt_weightedBallAverage_ae_of_multiplicity
    {U : Set E} (hU : IsOpen U) (hn : 0 < n)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    {h : E → ℝ} (hh : ContinuousOn h U) :
    ∀ᵐ ξ ∂V.weight.restrict U, 1 ≤ h ξ → ∀ c : ℝ, c < 1 →
      ∀ᶠ r : ℝ in 𝓝[>] 0, c < V.weightedBallAverage ξ h r := by
  rw [ae_restrict_iff' hU.measurableSet]
  filter_upwards [V.ae_weight_of_ae_restrict V.approximate_tangent] with ξ hξ hξU hvalue c hc
  exact V.eventually_lt_weightedBallAverage_of_one_le_value hU hn hθ hh hξU hξ hvalue hc

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
