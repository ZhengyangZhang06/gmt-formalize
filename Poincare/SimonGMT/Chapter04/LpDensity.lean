module

public import Poincare.SimonGMT.Chapter04.LpMeanCurvature

@[expose] public section

/-!
# Simon GMT, Chapter 4, (4.9): densities under `Lᵖ` mean curvature

The density is the existing lower density of the actual weight measure.
Its finite limit and upper semicontinuity follow from the proved corrected
monotonicity. No identification with multiplicity is assumed.
-/

open Filter Function Metric Set
open scoped ENNReal MeasureTheory Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

/-- Zero-dimensional tangential divergence vanishes, so zero-dimensional
varifolds are stationary independently of a curvature hypothesis. This
also covers the endpoint `0<p≤1` in the source condition `p>n`. -/
theorem isStationaryIn_of_zero_dim (V : RectifiableVarifold (E := E) 0) (U : Set E) :
    V.IsStationaryIn U := by
  intro X hX
  change (∫ x, V.tangentialDivergence X x ∂V.weight) = 0
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards [V.tangent_finrank_ae_weight] with x hx
  have ht : V.tangentAt x = ⊥ := Submodule.finrank_eq_zero.mp hx
  simp only [tangentialDivergence, tangentProjection, ht, Submodule.starProjection_bot,
    ContinuousLinearMap.toLinearMap_zero, LinearMap.comp_zero, map_zero, Pi.zero_apply]

theorem scaledLpMeanCurvature_nonneg (ξ : E) (H : E → E) {p R : ℝ} (hR : 0 ≤ R) :
    0 ≤ V.scaledLpMeanCurvature ξ H p R :=
  Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hR _)
    (MeasureTheory.integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg (H x)) _)) _

/-- No smallness assumption is required for existence of density: `Λ` is
chosen from the finite `Lᵖ` norm on a surrounding closed ball. -/
theorem HasGeneralizedMeanCurvatureIn.exists_tendsto_normalizedBallMass_real_of_memLp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R : ℝ} (hp : 1 < p) (hpn : (n : ℝ) < p) (hR : 0 < R)
    (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R))) :
    ∃ d : ℝ, 0 ≤ d ∧ Tendsto (fun ρ ↦ V.weight.real (closedBall ξ ρ) / ρ ^ n)
      (𝓝[>] (0 : ℝ)) (𝓝 d) := by
  apply HasGeneralizedMeanCurvatureIn.exists_tendsto_normalizedBallMass_real_lp
    (V := V) hH ξ hp hpn hR hball hLp
    (Λ := V.scaledLpMeanCurvature ξ H p R / lpMeanCurvatureKappa n p)
  rw [mul_div_cancel₀ _ (lpMeanCurvatureKappa_pos hpn).ne']

theorem HasGeneralizedMeanCurvatureIn.tendsto_normalizedBallMass_of_memLp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R : ℝ} (hp : 1 < p) (hpn : (n : ℝ) < p) (hR : 0 < R)
    (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R))) :
    Tendsto (V.normalizedBallMass ξ) (𝓝[>] (0 : ℝ)) (𝓝 (V.lowerDensityMassRatio ξ)) := by
  obtain ⟨d, _, hd⟩ :=
    HasGeneralizedMeanCurvatureIn.exists_tendsto_normalizedBallMass_real_of_memLp
      (V := V) hH ξ hp hpn hR hball hLp
  have ht := V.tendsto_normalizedBallMass_of_tendsto_real hd
  have heq : V.lowerDensityMassRatio ξ = ENNReal.ofReal d := ht.liminf_eq
  rw [heq]
  exact ht

theorem HasGeneralizedMeanCurvatureIn.lowerDensityMassRatio_ne_top_of_memLp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R : ℝ} (hp : 1 < p) (hpn : (n : ℝ) < p) (hR : 0 < R)
    (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R))) :
    V.lowerDensityMassRatio ξ ≠ ⊤ := by
  obtain ⟨d, _, hd⟩ :=
    HasGeneralizedMeanCurvatureIn.exists_tendsto_normalizedBallMass_real_of_memLp
      (V := V) hH ξ hp hpn hR hball hLp
  have heq : V.lowerDensityMassRatio ξ = ENNReal.ofReal d :=
    (V.tendsto_normalizedBallMass_of_tendsto_real hd).liminf_eq
  rw [heq]
  exact ENNReal.ofReal_ne_top

theorem HasGeneralizedMeanCurvatureIn.tendsto_normalizedBallMass_real_of_memLp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R : ℝ} (hp : 1 < p) (hpn : (n : ℝ) < p) (hR : 0 < R)
    (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R))) :
    Tendsto (fun ρ ↦ V.weight.real (closedBall ξ ρ) / ρ ^ n)
      (𝓝[>] (0 : ℝ)) (𝓝 (V.lowerDensityMassRatio ξ).toReal) := by
  have ht := (ENNReal.tendsto_toReal
    (HasGeneralizedMeanCurvatureIn.lowerDensityMassRatio_ne_top_of_memLp
      (V := V) hH ξ hp hpn hR hball hLp)).comp
    (HasGeneralizedMeanCurvatureIn.tendsto_normalizedBallMass_of_memLp
      (V := V) hH ξ hp hpn hR hball hLp)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  simp only [Function.comp_apply, normalizedBallMass, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (pow_pos hρ n).le, MeasureTheory.measureReal_def]

/-- The full finite density limit, including the source normalization `ωₙ`. -/
theorem HasGeneralizedMeanCurvatureIn.tendsto_densityQuotient_real_of_memLp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R : ℝ} (hp : 1 < p) (hpn : (n : ℝ) < p) (hR : 0 < R)
    (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R))) :
    Tendsto (fun ρ ↦ V.weight.real (closedBall ξ ρ) /
      ((Chapter01.realUnitBallVolume (n : ℝ)).toReal * ρ ^ n))
      (𝓝[>] (0 : ℝ)) (𝓝 (V.stationaryDensityReal ξ)) := by
  have ht := (HasGeneralizedMeanCurvatureIn.tendsto_normalizedBallMass_real_of_memLp
    (V := V) hH ξ hp hpn hR hball hLp).div_const (Chapter01.realUnitBallVolume (n : ℝ)).toReal
  simpa only [stationaryDensityReal, stationaryDensity, ENNReal.toReal_div,
    div_div, mul_comm] using ht

/-- Restricting the surrounding ball decreases its scale-invariant `Lᵖ`
curvature quantity when `p>n`. This permits a single correction near a point. -/
theorem scaledLpMeanCurvature_mono_ball {ξ η : E} {H : E → E} {p R S : ℝ}
    (hp : (n : ℝ) < p) (hR : 0 ≤ R) (hRS : R ≤ S)
    (hballs : closedBall ξ R ⊆ closedBall η S)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall η S))) :
    V.scaledLpMeanCurvature ξ H p R ≤ V.scaledLpMeanCurvature η H p S := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have hint : MeasureTheory.IntegrableOn (fun x ↦ ‖H x‖ ^ p) (closedBall η S) V.weight := by
    change MeasureTheory.Integrable (fun x ↦ ‖H x‖ ^ p) (V.weight.restrict (closedBall η S))
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      hLp.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
  have hI : (∫ x in closedBall ξ R, ‖H x‖ ^ p ∂V.weight) ≤
      ∫ x in closedBall η S, ‖H x‖ ^ p ∂V.weight := by
    exact MeasureTheory.integral_mono_measure (MeasureTheory.Measure.restrict_mono hballs le_rfl)
      (Eventually.of_forall fun x ↦ Real.rpow_nonneg (norm_nonneg _) _) hint
  apply Real.rpow_le_rpow
    (mul_nonneg (Real.rpow_nonneg hR _)
      (MeasureTheory.integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _))
    (mul_le_mul (Real.rpow_le_rpow hR hRS (sub_pos.mpr hp).le) hI
      (MeasureTheory.integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (hR.trans hRS) _))
    (one_div_nonneg.mpr hp0.le)

theorem upperSemicontinuous_normalizedBallMass_real {ρ : ℝ} (hρ : 0 < ρ) :
    UpperSemicontinuous (fun ξ : E ↦ V.weight.real (closedBall ξ ρ) / ρ ^ n) := by
  have heq (ξ : E) : (V.normalizedBallMass ξ ρ).toReal =
      V.weight.real (closedBall ξ ρ) / ρ ^ n := by
    simp only [normalizedBallMass, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (pow_pos hρ n).le, MeasureTheory.measureReal_def]
  intro ξ a ha
  have ha0 : 0 < a := (div_nonneg ENNReal.toReal_nonneg (pow_pos hρ n).le).trans_lt ha
  have hlt : V.normalizedBallMass ξ ρ < ENNReal.ofReal a := by
    apply (ENNReal.toReal_lt_toReal (V.normalizedBallMass_ne_top ξ hρ) ENNReal.ofReal_ne_top).mp
    simpa only [heq, ENNReal.toReal_ofReal ha0.le] using ha
  filter_upwards [(V.upperSemicontinuous_normalizedBallMass hρ) ξ (ENNReal.ofReal a) hlt] with η hη
  have h := (ENNReal.toReal_lt_toReal (V.normalizedBallMass_ne_top η hρ)
    ENNReal.ofReal_ne_top).mpr hη
  simpa only [heq, ENNReal.toReal_ofReal ha0.le] using h

theorem upperSemicontinuous_lp_correctedBallMass {p R Λ ρ : ℝ} (hρ : 0 < ρ) :
    UpperSemicontinuous (fun ξ : E ↦ lpMonotonicityFactor n p R Λ ρ *
      (V.weight.real (closedBall ξ ρ) / ρ ^ n) + lpMonotonicityError n p R Λ ρ) := by
  apply (show Continuous (fun m : ℝ ↦ lpMonotonicityFactor n p R Λ ρ * m +
    lpMonotonicityError n p R Λ ρ) by fun_prop).comp_upperSemicontinuous
    (V.upperSemicontinuous_normalizedBallMass_real hρ)
  intro a b hab
  exact add_le_add (mul_le_mul_of_nonneg_left hab (Real.exp_pos _).le) le_rfl

theorem HasGeneralizedMeanCurvatureIn.tendsto_lp_correctedBallMass
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : 1 < p) (hpn : (n : ℝ) < p) (hR : 0 < R)
    (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R))) :
    Tendsto (fun ρ ↦ lpMonotonicityFactor n p R Λ ρ *
      (V.weight.real (closedBall ξ ρ) / ρ ^ n) + lpMonotonicityError n p R Λ ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 (V.lowerDensityMassRatio ξ).toReal) := by
  have hf := tendsto_lpMonotonicityFactor (n := n) (R := R) hpn Λ
  have hm := HasGeneralizedMeanCurvatureIn.tendsto_normalizedBallMass_real_of_memLp
    (V := V) hH ξ hp hpn hR hball hLp
  simpa only [one_mul, sub_self, add_zero, lpMonotonicityError] using
    (hf.mul hm).add (hf.sub_const 1)

theorem HasGeneralizedMeanCurvatureIn.lowerDensityMassRatio_toReal_le_lp_correctedBallMass
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ ρ : ℝ} (hp : 1 < p) (hpn : (n : ℝ) < p) (hR : 0 < R)
    (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ)
    (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    (V.lowerDensityMassRatio ξ).toReal ≤ lpMonotonicityFactor n p R Λ ρ *
      (V.weight.real (closedBall ξ ρ) / ρ ^ n) + lpMonotonicityError n p R Λ ρ := by
  apply le_of_tendsto (HasGeneralizedMeanCurvatureIn.tendsto_lp_correctedBallMass
    (V := V) hH ξ hp hpn hR hball hLp (Λ := Λ))
  filter_upwards [Ioo_mem_nhdsGT hρ] with t ht
  exact HasGeneralizedMeanCurvatureIn.lp_normalizedBallMass_monotoneOn_Ioc
    (V := V) hH ξ hp hR hball hLp hscale ⟨ht.1, ht.2.le.trans hρR⟩ ⟨hρ, hρR⟩ ht.2.le

/-- The local upper-semicontinuity statement underlying (4.9). A single
`Lᵖ` bound on a surrounding closed ball controls all nearby centers. -/
theorem HasGeneralizedMeanCurvatureIn.upperSemicontinuousAt_lowerDensityMassRatio_toReal_of_memLp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R : ℝ} (hp : 1 < p) (hpn : (n : ℝ) < p) (hR : 0 < R)
    (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R))) :
    UpperSemicontinuousAt (fun η ↦ (V.lowerDensityMassRatio η).toReal) ξ := by
  let Λ := V.scaledLpMeanCurvature ξ H p R / lpMeanCurvatureKappa n p
  have hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ := by
    dsimp [Λ]
    rw [mul_div_cancel₀ _ (lpMeanCurvatureKappa_pos hpn).ne']
  have hhalfball : closedBall ξ (R / 2) ⊆ closedBall ξ R :=
    closedBall_subset_closedBall (half_le_self hR.le)
  have hLphalf := hLp.mono_measure (MeasureTheory.Measure.restrict_mono hhalfball le_rfl)
  have hlim := HasGeneralizedMeanCurvatureIn.tendsto_lp_correctedBallMass
    (V := V) hH ξ hp hpn (half_pos hR) (hhalfball.trans hball) hLphalf (Λ := Λ)
  intro a ha
  obtain ⟨ρ, hmass, hρ⟩ :=
    ((hlim.eventually (gt_mem_nhds ha)).and (Ioo_mem_nhdsGT (half_pos hR))).exists
  filter_upwards [(V.upperSemicontinuous_lp_correctedBallMass
    (p := p) (R := R / 2) (Λ := Λ) hρ.1) ξ a hmass,
    ball_mem_nhds ξ (half_pos hR)] with η hηmass hη
  have hηball : closedBall η (R / 2) ⊆ closedBall ξ R := by
    apply closedBall_subset_closedBall'
    have hdist : dist η ξ < R / 2 := hη
    linarith
  have hLpη := hLp.mono_measure (MeasureTheory.Measure.restrict_mono hηball le_rfl)
  have hscaleη : V.scaledLpMeanCurvature η H p (R / 2) ≤
      lpMeanCurvatureKappa n p * Λ :=
    (V.scaledLpMeanCurvature_mono_ball hpn (half_pos hR).le
      (half_le_self hR.le) hηball hLp).trans hscale
  exact (HasGeneralizedMeanCurvatureIn.lowerDensityMassRatio_toReal_le_lp_correctedBallMass
    (V := V) hH η hp hpn (half_pos hR) (hηball.trans hball) hLpη hscaleη hρ.1 hρ.2.le).trans_lt hηmass

/-- Simon (4.9), for the source local-`Lᵖ` hypothesis on every compact
subset of the open domain. The density is normalized by `ωₙ`. -/
theorem HasGeneralizedMeanCurvatureIn.upperSemicontinuousOn_stationaryDensityReal_lp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    {p : ℝ} (hpn : (n : ℝ) < p) (hU : IsOpen U)
    (hLp : ∀ K : Set E, IsCompact K → K ⊆ U →
      MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict K)) :
    UpperSemicontinuousOn V.stationaryDensityReal U := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    exact IsStationaryIn.upperSemicontinuousOn_stationaryDensityReal
      (V := V) (V.isStationaryIn_of_zero_dim U) hU
  have hp : 1 < p := lt_of_le_of_lt (by exact_mod_cast (Nat.succ_le_iff.mpr hn)) hpn
  have hmass : UpperSemicontinuousOn (fun ξ ↦ (V.lowerDensityMassRatio ξ).toReal) U := by
    intro ξ hξ
    obtain ⟨R, hR, hball⟩ := exists_pos_closedBall_subset hU hξ
    exact (HasGeneralizedMeanCurvatureIn.upperSemicontinuousAt_lowerDensityMassRatio_toReal_of_memLp
      (V := V) hH ξ hp hpn hR hball (hLp _ (isCompact_closedBall ξ R) hball)).upperSemicontinuousWithinAt U
  have hω : 0 ≤ (Chapter01.realUnitBallVolume (n : ℝ)).toReal := ENNReal.toReal_nonneg
  have hc : Continuous (fun d : ℝ ↦ d / (Chapter01.realUnitBallVolume (n : ℝ)).toReal) :=
    continuous_id.div_const _
  have h := hc.comp_upperSemicontinuousOn hmass (fun _ _ h ↦ div_le_div_of_nonneg_right h hω)
  change UpperSemicontinuousOn (fun ξ ↦ (V.stationaryDensity ξ).toReal) U
  simpa only [Function.comp_def, stationaryDensity, ENNReal.toReal_div] using h

/-- The finite `ωₙ`-normalized density exists at every point of the open
local-`Lᵖ` domain, under precisely the same hypotheses as (4.9). -/
theorem HasGeneralizedMeanCurvatureIn.tendsto_densityQuotient_real_lp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    {p : ℝ} (hpn : (n : ℝ) < p) (hU : IsOpen U)
    (hLp : ∀ K : Set E, IsCompact K → K ⊆ U →
      MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict K))
    {ξ : E} (hξ : ξ ∈ U) :
    Tendsto (fun ρ ↦ V.weight.real (closedBall ξ ρ) /
      ((Chapter01.realUnitBallVolume (n : ℝ)).toReal * ρ ^ n))
      (𝓝[>] (0 : ℝ)) (𝓝 (V.stationaryDensityReal ξ)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    exact IsStationaryIn.tendsto_densityQuotient_real
      (V := V) (V.isStationaryIn_of_zero_dim U) hU hξ
  have hp : 1 < p := lt_of_le_of_lt (by exact_mod_cast (Nat.succ_le_iff.mpr hn)) hpn
  obtain ⟨R, hR, hball⟩ := exists_pos_closedBall_subset hU hξ
  exact HasGeneralizedMeanCurvatureIn.tendsto_densityQuotient_real_of_memLp
    (V := V) hH ξ hp hpn hR hball (hLp _ (isCompact_closedBall ξ R) hball)

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
