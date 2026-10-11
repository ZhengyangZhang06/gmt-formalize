module

public import Poincare.SimonGMT.Chapter04.PoincareKernel

@[expose] public section

/-!
# The local truncation and absorption step in Simon (5.6)

The multiplier need not have compact support. Its positive set is small
inside the prescribed ball, exactly as in the printed Poincare theorem.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

/-- The inner radius can be chosen using only the dimension and the
positivity-set deficit. -/
theorem exists_poincare_radius (n : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ β : ℝ, β ∈ Ioo 0 (1 / 2) ∧
      (1 - α ^ 2) / (1 - β) ^ n ≤ 1 - α ^ 2 / 2 := by
  have hc : ContinuousAt (fun β : ℝ ↦ (1 - α ^ 2) / (1 - β) ^ n) 0 :=
    continuousAt_const.div ((continuousAt_const.sub continuousAt_id).pow n) (by simp)
  have hlim : Tendsto (fun β : ℝ ↦ (1 - α ^ 2) / (1 - β) ^ n)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 - α ^ 2)) := by
    simpa only [sub_zero, one_pow, div_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨β, hgap, hβ⟩ := ((hlim.eventually (gt_mem_nhds
    (show 1 - α ^ 2 < 1 - α ^ 2 / 2 by nlinarith [sq_pos_of_pos hα]))).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num))).exists
  exact ⟨β, hβ, hgap.le⟩

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

/-- The deficit in the measure of `{h>0}` absorbs the average term in
the genuine pointwise potential inequality. This is (2) in the proof of
Simon (5.6), with all local hypotheses exposed and no kernel finiteness
assumption. -/
theorem HasGeneralizedMeanCurvatureIn.truncation_gap_le_local_potential
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    (hn : 0 < n) {ξ ζ : E} {ρ Λ α β t : ℝ}
    (hρ : 0 < ρ) (hΛ : 0 ≤ Λ) (hα : α ∈ Ioo 0 1) (hβ : β ∈ Ioo 0 (1 / 2))
    (hgap : (1 - α ^ 2) / (1 - β) ^ n ≤ 1 - α ^ 2 / 2)
    (hball : closedBall ξ (2 * ρ) ⊆ U)
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    (hexp : Real.exp (Λ * ρ) ≤ 1 + α)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U)
    (hmass : V.weight.real ({x | 0 < h x} ∩ closedBall ξ ρ) ≤
      (1 - α) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal * ρ ^ n)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ 1 γ) (hγmono : Monotone γ)
    (hγrange : ∀ s, γ s ∈ Icc 0 1) (hγzero : ∀ s, s ≤ 0 → γ s = 0)
    (ht : 0 ≤ t) (hζ : ζ ∈ closedBall ξ (β * ρ)) (hsupp : ζ ∈ V.weight.support)
    (hvalue : γ (h ζ - t) = 1) :
    ENNReal.ofReal (α ^ 2 / 2) ≤
      ENNReal.ofReal ((1 + α) /
        ((n : ℝ) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal)) *
      ∫⁻ x in closedBall ξ ρ, ENNReal.ofReal
        (deriv γ (h x - t) * ‖V.tangentialGradient h x‖ / ‖x - ζ‖ ^ (n - 1)) ∂V.weight := by
  let ω := (Chapter01.realUnitBallVolume (n : ℝ)).toReal
  let r := (1 - β) * ρ
  let k : E → ℝ := fun x ↦ γ (h x - t)
  let P := ∫⁻ x in closedBall ξ ρ, ENNReal.ofReal
    (deriv γ (h x - t) * ‖V.tangentialGradient h x‖ / ‖x - ζ‖ ^ (n - 1)) ∂V.weight
  have hω : 0 < ω := ENNReal.toReal_pos
    (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)).ne'
    (Chapter01.realUnitBallVolume_ne_top _)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := mul_pos (by linarith [hβ.2]) hρ
  have hβ1 : 0 < 1 - β := by linarith [hβ.2]
  have hsub : closedBall ζ r ⊆ closedBall ξ ρ :=
    closedBall_subset_closedBall' (by
      have hz : dist ζ ξ ≤ β * ρ := hζ
      dsimp only [r]
      nlinarith)
  have houter : closedBall ξ ρ ⊆ U :=
    (closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ)).trans hball
  have hk : ContDiffOn ℝ 1 k U := hγ.comp_contDiffOn (hh.sub contDiffOn_const)
  have havg : V.weightedBallAverage ζ k r ≤ (1 - α) / (1 - β) ^ n := by
    have hmassk := integral_le_measure (μ := V.weight.restrict (closedBall ζ r))
      (s := {x | 0 < h x}) (f := k) (fun x _ ↦ (hγrange _).2) (fun x hx ↦ by
        change ¬ 0 < h x at hx
        exact (hγzero _ (by linarith [le_of_not_gt hx])).le)
    rw [Measure.restrict_apply' measurableSet_closedBall] at hmassk
    have hfinite : V.weight ({x | 0 < h x} ∩ closedBall ξ ρ) ≠ ∞ :=
      (lt_of_le_of_lt (measure_mono inter_subset_right) (isCompact_closedBall ξ ρ).measure_lt_top).ne
    have hmassk' := hmassk.trans (measure_mono (inter_subset_inter_right _ hsub))
    rw [← ENNReal.ofReal_toReal hfinite] at hmassk'
    have hreal : (∫ x in closedBall ζ r, k x ∂V.weight) ≤
        V.weight.real ({x | 0 < h x} ∩ closedBall ξ ρ) :=
      (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hmassk'
    calc
      _ ≤ ((1 - α) * ω * ρ ^ n) / (ω * r ^ n) :=
        div_le_div_of_nonneg_right (hreal.trans hmass) (mul_pos hω (pow_pos hr _)).le
      _ = _ := by
        dsimp only [r]
        rw [mul_pow]
        field_simp
  have hchain (x : E) (hx : x ∈ closedBall ξ ρ) :
      ‖V.tangentialGradient k x‖ = deriv γ (h x - t) * ‖V.tangentialGradient h x‖ := by
    rw [tangentialGradient_comp_sub_const V t
      ((hh.contDiffAt (hU.mem_nhds (houter hx))).differentiableAt (by simp))
      (hγ.differentiable (by simp) _), norm_smul, Real.norm_of_nonneg hγmono.deriv_nonneg]
  have hpotential : V.radialWeightedPotential ζ (fun x ↦ ‖V.tangentialGradient k x‖) r ≤ P := by
    apply (lintegral_mono_set hsub).trans (le_of_eq ?_)
    apply setLIntegral_congr_fun measurableSet_closedBall
    intro x hx
    dsimp only []
    rw [hchain x hx]
  have hexpr : Real.exp (Λ * r) ≤ 1 + α := by
    apply (Real.exp_le_exp.mpr ?_).trans hexp
    apply mul_le_mul_of_nonneg_left _ hΛ
    dsimp only [r]
    nlinarith [hβ.1]
  have hpoint := HasGeneralizedMeanCurvatureIn.value_le_weightedPotential_of_multiplicity
    (V := V) hH hU hn hk (fun x _ ↦ (hγrange _).1) hsupp hΛ hbound hθ hr (hsub.trans houter)
  change ENNReal.ofReal (γ (h ζ - t)) ≤ _ at hpoint
  rw [hvalue, ENNReal.ofReal_one] at hpoint
  have havg0 : 0 ≤ V.weightedBallAverage ζ k r :=
    V.weightedBallAverage_nonneg ζ hr.le (fun x _ ↦ (hγrange _).1)
  have hgap0 : 0 ≤ 1 - α ^ 2 / 2 := by nlinarith [hα.1, hα.2]
  have havgprod : ENNReal.ofReal (Real.exp (Λ * r)) *
      ENNReal.ofReal (V.weightedBallAverage ζ k r) ≤ ENNReal.ofReal (1 - α ^ 2 / 2) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (1 + α) * ((1 - α) / (1 - β) ^ n) := by
        exact mul_le_mul hexpr havg havg0 (by linarith [hα.1])
      _ = (1 - α ^ 2) / (1 - β) ^ n := by ring
      _ ≤ _ := hgap
  have hboundP : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 - α ^ 2 / 2) +
      ENNReal.ofReal ((1 + α) / ((n : ℝ) * ω)) * P := by
    apply hpoint.trans
    rw [mul_add]
    apply add_le_add havgprod
    calc
      _ ≤ ENNReal.ofReal (1 + α) *
          (ENNReal.ofReal (1 / ((n : ℝ) * ω)) * P) := by
        gcongr
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith [hα.1])]
        congr 2
        ring
  apply ENNReal.le_of_add_le_add_left ENNReal.ofReal_ne_top
  calc
    ENNReal.ofReal (1 - α ^ 2 / 2) + ENNReal.ofReal (α ^ 2 / 2) = 1 := by
      rw [← ENNReal.ofReal_add hgap0 (by positivity)]
      norm_num
    _ ≤ _ := hboundP

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
