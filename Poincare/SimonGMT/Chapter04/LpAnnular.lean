module

public import Poincare.SimonGMT.Chapter04.LpCancellation
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-!
# Simon GMT, Chapter 4, (4.7): a simultaneous annular factor

A compact product limit of the genuine cutoff cancellation factors gives
one function of radius, used simultaneously in all annular identities.
The construction does not assume the identity it proves.
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

private theorem eventually_cutoff_radius_lt {ρ R : ℝ} (hρR : ρ < R) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 ∧ ρ * (1 + ε) < R := by
  have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hlim := (hid.const_add 1).const_mul ρ
  have hlt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ρ * (1 + ε) < R :=
    hlim.eventually (gt_mem_nhds (by simpa using hρR))
  filter_upwards [self_mem_nhdsWithin, hid.eventually (gt_mem_nhds zero_lt_one), hlt]
    with ε hε hε1 hεR
  exact ⟨hε, hε1.le, hεR⟩

/-- A single limiting cancellation factor on all interior radii. Its fine
bounds and annular squeeze are inherited from the first-variation identity,
using the same compact product limit for every radius. -/
theorem HasGeneralizedMeanCurvatureIn.exists_cancellationFactor_squeeze_of_lt
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R) (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ) :
    ∃ F : ℝ → ℝ,
      (∀ ρ ∈ Ioo 0 R,
        Real.exp (-Λ / 2 * (ρ / R) ^ (1 - n / p)) ≤ F ρ ∧
        F ρ ≤ Real.exp (Λ / 2 * (ρ / R) ^ (1 - n / p)) ∧
        |F ρ - 1| ≤ (Real.exp (Λ / 2) / 2) * Λ * (ρ / R) ^ (1 - n / p) ∧
        (Λ ≤ 1 → |F ρ - 1| ≤ Λ * (ρ / R) ^ (1 - n / p))) ∧
      ∀ σ ρ, 0 < σ → σ ≤ ρ → ρ < R →
        let D := ∫ x in closedBall ξ ρ \ closedBall ξ σ,
          V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight
        let C := fun t ↦ F t * (V.weight.real (closedBall ξ t) / t ^ n) + (F t - 1)
        Real.exp (-Λ) * D ≤ C ρ - C σ ∧ C ρ - C σ ≤ Real.exp Λ * D := by
  have hΛ : 0 ≤ Λ := nonneg_of_mul_nonneg_right
    ((V.scaledLpMeanCurvature_nonneg ξ H hR.le).trans hscale) (lpMeanCurvatureKappa_pos hp)
  have horder : Real.exp (-Λ) ≤ Real.exp Λ := Real.exp_le_exp.mpr (by linarith)
  let f := fun ε t ↦ V.cutoffCancellationFactor ξ H (monotonicityCutoff ε) t
  let u : ℝ → (ℝ → Icc (Real.exp (-Λ)) (Real.exp Λ)) :=
    fun ε t ↦ Set.projIcc _ _ horder (f ε t)
  let L : Ultrafilter ℝ := Ultrafilter.of (𝓝[>] (0 : ℝ))
  let Fsub := (Ultrafilter.map u L).lim
  let F : ℝ → ℝ := fun t ↦ (Fsub t : ℝ)
  have hL : (L : Filter ℝ) ≤ 𝓝[>] (0 : ℝ) := Ultrafilter.of_le _
  have hu : Tendsto u (L : Filter ℝ) (𝓝 Fsub) :=
    (Ultrafilter.map u L).le_nhds_lim
  have hbound : ∀ ρ ∈ Ioo 0 R, ∀ᶠ ε in (L : Filter ℝ),
      Real.exp (-Λ / 2 * (ρ / R) ^ (1 - n / p)) ≤ f ε ρ ∧
        f ε ρ ≤ Real.exp (Λ / 2 * (ρ / R) ^ (1 - n / p)) := by
    intro ρ hρ
    filter_upwards [hL (eventually_cutoff_radius_lt hρ.2)] with ε hε
    exact HasGeneralizedMeanCurvatureIn.cutoffCancellationFactor_bounds
      (V := V) hH ξ hp hR hball hLp hscale (contDiff_monotonicityCutoff ε)
      (monotonicityCutoff_mem_Icc ε) (by linarith [hε.1]) (by linarith [hε.2.1]) hρ.1
      (monotonicityCutoff_cutoff hε.1) hε.2.2.le
  have hlim : ∀ ρ ∈ Ioo 0 R, Tendsto (fun ε ↦ f ε ρ) (L : Filter ℝ) (𝓝 (F ρ)) := by
    intro ρ hρ
    have hglobal := lpMonotonicityFactor_bounds hp hR hΛ hρ.1 hρ.2.le
    have heq : (fun ε ↦ (u ε ρ : ℝ)) =ᶠ[L] fun ε ↦ f ε ρ := by
      filter_upwards [hbound ρ hρ] with ε hε
      have hm : f ε ρ ∈ Icc (Real.exp (-Λ)) (Real.exp Λ) :=
        ⟨hglobal.1.trans hε.1, hε.2.trans hglobal.2.2.2⟩
      exact congrArg Subtype.val (Set.projIcc_of_mem horder hm)
    exact ((continuous_subtype_val.tendsto _).comp (hu.apply_nhds ρ)).congr' heq
  refine ⟨F, ?_, ?_⟩
  · intro ρ hρ
    refine ⟨ge_of_tendsto (hlim ρ hρ) ((hbound ρ hρ).mono fun _ h ↦ h.1),
      le_of_tendsto (hlim ρ hρ) ((hbound ρ hρ).mono fun _ h ↦ h.2), ?_, ?_⟩
    · apply le_of_tendsto (((hlim ρ hρ).sub_const 1).abs)
      filter_upwards [hL (eventually_cutoff_radius_lt hρ.2)] with ε hε
      exact HasGeneralizedMeanCurvatureIn.abs_cutoffCancellationError_le
        (V := V) hH ξ hp hR hball hLp hscale (contDiff_monotonicityCutoff ε)
        (monotonicityCutoff_mem_Icc ε) (by linarith [hε.1]) (by linarith [hε.2.1])
        hρ.1 hρ.2.le (monotonicityCutoff_cutoff hε.1) hε.2.2.le
    · intro hΛ1
      apply le_of_tendsto (((hlim ρ hρ).sub_const 1).abs)
      filter_upwards [hL (eventually_cutoff_radius_lt hρ.2)] with ε hε
      exact HasGeneralizedMeanCurvatureIn.abs_cutoffCancellationError_le_of_le_one
        (V := V) hH ξ hp hR hΛ1 hball hLp hscale (contDiff_monotonicityCutoff ε)
        (monotonicityCutoff_mem_Icc ε) (by linarith [hε.1]) (by linarith [hε.2.1])
        hρ.1 hρ.2.le (monotonicityCutoff_cutoff hε.1) hε.2.2.le
  · intro σ ρ hσ hσρ hρR
    have hρ := hσ.trans_le hσρ
    have hσR := hσρ.trans_lt hρR
    let Cε := fun ε t ↦ f ε t * (V.cutoffMass ξ (monotonicityCutoff ε) t / t ^ n) + (f ε t - 1)
    let C := fun t ↦ F t * (V.weight.real (closedBall ξ t) / t ^ n) + (F t - 1)
    have hC : ∀ t ∈ Ioo 0 R, Tendsto (fun ε ↦ Cε ε t) (L : Filter ℝ) (𝓝 (C t)) := by
      intro t ht
      exact ((hlim t ht).mul (((V.tendsto_cutoffMass ξ ht.1).mono_left hL).div_const _)).add
        ((hlim t ht).sub_const 1)
    have hCdiff := (hC ρ ⟨hρ, hρR⟩).sub (hC σ ⟨hσ, hσR⟩)
    have hD := (V.tendsto_cutoffDefect_difference ξ hσ hσρ).mono_left hL
    have hid : Tendsto (fun ε : ℝ ↦ ε) (L : Filter ℝ) (𝓝 0) :=
      (tendsto_id.mono_left inf_le_left).mono_left hL
    have hpow : Tendsto (fun ε : ℝ ↦ (1 + ε) ^ n) (L : Filter ℝ) (𝓝 1) := by
      simpa only [add_zero, one_pow] using (hid.const_add 1).pow n
    constructor
    · apply le_of_tendsto_of_tendsto (hD.const_mul (Real.exp (-Λ))) hCdiff
      filter_upwards [hL (eventually_cutoff_radius_lt hρR)] with ε hε
      exact (HasGeneralizedMeanCurvatureIn.cancelledCutoffMass_squeeze
        (V := V) hH ξ hp hR hball hLp hscale hε.1 hε.2.1 hσ hσρ hε.2.2).1
    · apply le_of_tendsto_of_tendsto hCdiff
        (by simpa only [mul_one] using (hpow.const_mul (Real.exp Λ)).mul hD)
      filter_upwards [hL (eventually_cutoff_radius_lt hρR)] with ε hε
      exact (HasGeneralizedMeanCurvatureIn.cancelledCutoffMass_squeeze
        (V := V) hH ξ hp hR hball hLp hscale hε.1 hε.2.1 hσ hσρ hε.2.2).2

/-- A strict relaxation of the smallness constant extends beyond the
closed ball. Continuity from above preserves any mass on its boundary. -/
theorem exists_larger_radius_scaledLpMeanCurvature_le
    (ξ : E) {H : E → E} {p R S Λ Λ' : ℝ}
    (hp : (n : ℝ) < p) (hR : 0 < R) (hRS : R < S)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ S)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ)
    (hΛ : Λ < Λ') :
    ∃ T : ℝ, R < T ∧ T ≤ S ∧
      V.scaledLpMeanCurvature ξ H p T ≤ lpMeanCurvatureKappa n p * Λ' := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  let r : ℕ → ℝ := fun k ↦ R + (S - R) / ((k : ℝ) + 1)
  have hrpos : ∀ k, R < r k := fun k ↦ lt_add_of_pos_right _
    (div_pos (sub_pos.mpr hRS) (by positivity))
  have hrzero : r 0 = S := by simp [r]
  have hranti : Antitone r := by
    intro i j hij
    dsimp [r]
    apply add_le_add_right
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hRS.le) (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hrle : ∀ k, r k ≤ S := fun k ↦ by
    simpa only [hrzero] using hranti (Nat.zero_le k)
  have hrlim : Tendsto r atTop (𝓝 R) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (S - R)).const_add R
    simpa only [mul_zero, add_zero, mul_one_div] using h
  have hinter : (⋂ k, closedBall ξ (r k)) = closedBall ξ R := by
    ext x
    simp only [mem_iInter, mem_closedBall]
    constructor
    · intro hx
      exact ge_of_tendsto hrlim (Eventually.of_forall hx)
    · exact fun hx k ↦ hx.trans (hrpos k).le
  have hint : MeasureTheory.IntegrableOn (fun x ↦ ‖H x‖ ^ p) (closedBall ξ S) V.weight := by
    change MeasureTheory.Integrable (fun x ↦ ‖H x‖ ^ p) (V.weight.restrict (closedBall ξ S))
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      hLp.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
  have hmass := MeasureTheory.tendsto_setIntegral_of_antitone
    (μ := V.weight) (f := fun x ↦ ‖H x‖ ^ p)
    (fun k ↦ measurableSet_closedBall)
    (fun i j hij ↦ closedBall_subset_closedBall (hranti hij))
    (show ∃ k, MeasureTheory.IntegrableOn (fun x ↦ ‖H x‖ ^ p) (closedBall ξ (r k)) V.weight from
      ⟨0, by simpa only [hrzero] using hint⟩)
  rw [hinter] at hmass
  have hlim : Tendsto (fun k ↦ V.scaledLpMeanCurvature ξ H p (r k)) atTop
      (𝓝 (V.scaledLpMeanCurvature ξ H p R)) :=
    ((hrlim.rpow_const (Or.inl hR.ne')).mul hmass).rpow_const (Or.inr (one_div_pos.mpr hp0).le)
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds
    (hscale.trans_lt (mul_lt_mul_of_pos_left hΛ (lpMeanCurvatureKappa_pos hp))))).exists
  exact ⟨r k, hrpos k, hrle k, hk.le⟩

/-- The closed-endpoint simultaneous factor. The additional surrounding
`Lᵖ` ball is the local `Lᵖ` hypothesis in the source, not a null-sphere
assumption. A second common product limit removes every relaxation. -/
theorem HasGeneralizedMeanCurvatureIn.exists_cancellationFactor_squeeze
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R S Λ : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R) (hRS : R < S)
    (hball : closedBall ξ S ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ S)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ) :
    ∃ F : ℝ → ℝ,
      (∀ ρ ∈ Ioc 0 R,
        Real.exp (-Λ / 2 * (ρ / R) ^ (1 - n / p)) ≤ F ρ ∧
        F ρ ≤ Real.exp (Λ / 2 * (ρ / R) ^ (1 - n / p)) ∧
        |F ρ - 1| ≤ (Real.exp (Λ / 2) / 2) * Λ * (ρ / R) ^ (1 - n / p) ∧
        (Λ ≤ 1 → |F ρ - 1| ≤ Λ * (ρ / R) ^ (1 - n / p))) ∧
      ∀ σ ρ, 0 < σ → σ ≤ ρ → ρ ≤ R →
        let D := ∫ x in closedBall ξ ρ \ closedBall ξ σ,
          V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight
        let C := fun t ↦ F t * (V.weight.real (closedBall ξ t) / t ^ n) + (F t - 1)
        Real.exp (-Λ) * D ≤ C ρ - C σ ∧ C ρ - C σ ≤ Real.exp Λ * D := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have hα : 0 ≤ 1 - n / p := sub_nonneg.mpr ((div_le_one hp0).mpr hp.le)
  have hΛ : 0 ≤ Λ := nonneg_of_mul_nonneg_right
    ((V.scaledLpMeanCurvature_nonneg ξ H hR.le).trans hscale) (lpMeanCurvatureKappa_pos hp)
  have hex : ∀ η : ℝ, 0 < η → ∃ F : ℝ → ℝ,
      (∀ ρ ∈ Ioc 0 R,
        Real.exp (-(Λ + η) / 2 * (ρ / R) ^ (1 - n / p)) ≤ F ρ ∧
        F ρ ≤ Real.exp ((Λ + η) / 2 * (ρ / R) ^ (1 - n / p)) ∧
        |F ρ - 1| ≤ (Real.exp ((Λ + η) / 2) / 2) * (Λ + η) * (ρ / R) ^ (1 - n / p)) ∧
      ∀ σ ρ, 0 < σ → σ ≤ ρ → ρ ≤ R →
        let D := ∫ x in closedBall ξ ρ \ closedBall ξ σ,
          V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight
        let C := fun t ↦ F t * (V.weight.real (closedBall ξ t) / t ^ n) + (F t - 1)
        Real.exp (-(Λ + η)) * D ≤ C ρ - C σ ∧ C ρ - C σ ≤ Real.exp (Λ + η) * D := by
    intro η hη
    obtain ⟨T, hRT, hTS, hTscale⟩ := V.exists_larger_radius_scaledLpMeanCurvature_le
      ξ hp hR hRS hLp hscale (show Λ < Λ + η by linarith)
    obtain ⟨F, hF, hsq⟩ :=
      HasGeneralizedMeanCurvatureIn.exists_cancellationFactor_squeeze_of_lt
        (V := V) hH ξ hp (hR.trans hRT) ((closedBall_subset_closedBall hTS).trans hball)
        (hLp.mono_measure (MeasureTheory.Measure.restrict_mono
          (closedBall_subset_closedBall hTS) le_rfl)) hTscale
    refine ⟨F, ?_, fun σ ρ hσ hσρ hρR ↦ hsq σ ρ hσ hσρ (hρR.trans_lt hRT)⟩
    intro ρ hρ
    have hFρ := hF ρ ⟨hρ.1, hρ.2.trans_lt hRT⟩
    have hpow : (ρ / T) ^ (1 - n / p) ≤ (ρ / R) ^ (1 - n / p) :=
      Real.rpow_le_rpow (div_pos hρ.1 (hR.trans hRT)).le
        (div_le_div_of_nonneg_left hρ.1.le hR hRT.le) hα
    have hηΛ : 0 ≤ Λ + η := by linarith
    have hB := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (Λ + η) / 2 by positivity)
    refine ⟨(Real.exp_le_exp.mpr ?_).trans hFρ.1,
      hFρ.2.1.trans (Real.exp_le_exp.mpr hB), hFρ.2.2.1.trans ?_⟩
    · linarith
    · exact mul_le_mul_of_nonneg_left hpow (by positivity)
  choose f hf using hex
  let f' : ℝ → ℝ → ℝ := fun η ↦ if hη : 0 < η then f η hη else fun _ ↦ 1
  have hf' : ∀ η (hη : 0 < η), f' η = f η hη := by
    intro η hη
    simp only [f', dite_eq_left hη]
  have horder : Real.exp (-(Λ + 1)) ≤ Real.exp (Λ + 1) := Real.exp_le_exp.mpr (by linarith)
  let u : ℝ → (ℝ → Icc (Real.exp (-(Λ + 1))) (Real.exp (Λ + 1))) :=
    fun η t ↦ Set.projIcc _ _ horder (f' η t)
  let L : Ultrafilter ℝ := Ultrafilter.of (𝓝[>] (0 : ℝ))
  let Fsub := (Ultrafilter.map u L).lim
  let F : ℝ → ℝ := fun t ↦ (Fsub t : ℝ)
  have hL : (L : Filter ℝ) ≤ 𝓝[>] (0 : ℝ) := Ultrafilter.of_le _
  have hu : Tendsto u (L : Filter ℝ) (𝓝 Fsub) := (Ultrafilter.map u L).le_nhds_lim
  have hid : Tendsto (fun η : ℝ ↦ η) (L : Filter ℝ) (𝓝 0) :=
    (tendsto_id.mono_left inf_le_left).mono_left hL
  have hpos : ∀ᶠ η in (L : Filter ℝ), 0 < η := hL self_mem_nhdsWithin
  have hlim : ∀ ρ ∈ Ioc 0 R, Tendsto (fun η ↦ f' η ρ) (L : Filter ℝ) (𝓝 (F ρ)) := by
    intro ρ hρ
    have hpow : (ρ / R) ^ (1 - n / p) ≤ 1 :=
      Real.rpow_le_one (div_pos hρ.1 hR).le ((div_le_one hR).mpr hρ.2) hα
    have heq : (fun η ↦ (u η ρ : ℝ)) =ᶠ[L] fun η ↦ f' η ρ := by
      filter_upwards [hpos, hid.eventually (gt_mem_nhds zero_lt_one)] with η hη hη1
      have hFρ := (hf η hη).1 ρ hρ
      have hB := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (Λ + η) / 2 by linarith)
      have hm : f' η ρ ∈ Icc (Real.exp (-(Λ + 1))) (Real.exp (Λ + 1)) := by
        rw [hf' η hη]
        exact ⟨(Real.exp_le_exp.mpr (by linarith)).trans hFρ.1,
          hFρ.2.1.trans (Real.exp_le_exp.mpr (by linarith))⟩
      exact congrArg Subtype.val (Set.projIcc_of_mem horder hm)
    exact ((continuous_subtype_val.tendsto _).comp (hu.apply_nhds ρ)).congr' heq
  refine ⟨F, ?_, ?_⟩
  · intro ρ hρ
    have hplus : Tendsto (fun η : ℝ ↦ Λ + η) (L : Filter ℝ) (𝓝 Λ) := by
      simpa only [add_zero] using hid.const_add Λ
    have hlow := (Real.continuous_exp.tendsto _).comp
      ((hplus.neg.div_const 2).mul_const ((ρ / R) ^ (1 - n / p)))
    have hupp := (Real.continuous_exp.tendsto _).comp
      ((hplus.div_const 2).mul_const ((ρ / R) ^ (1 - n / p)))
    have hexp := (Real.continuous_exp.tendsto _).comp (hplus.div_const 2)
    have herr := ((hexp.div_const 2).mul hplus).mul_const
      ((ρ / R) ^ (1 - n / p))
    have he : |F ρ - 1| ≤ (Real.exp (Λ / 2) / 2) * Λ * (ρ / R) ^ (1 - n / p) := by
      apply le_of_tendsto_of_tendsto (((hlim ρ hρ).sub_const 1).abs) herr
      filter_upwards [hpos] with η hη
      rw [hf' η hη]
      exact ((hf η hη).1 ρ hρ).2.2
    refine ⟨?_, ?_, he, ?_⟩
    · apply le_of_tendsto_of_tendsto hlow (hlim ρ hρ)
      filter_upwards [hpos] with η hη
      rw [hf' η hη]
      exact ((hf η hη).1 ρ hρ).1
    · apply le_of_tendsto_of_tendsto (hlim ρ hρ) hupp
      filter_upwards [hpos] with η hη
      rw [hf' η hη]
      exact ((hf η hη).1 ρ hρ).2.1
    · intro hΛ1
      have he2 : Real.exp (Λ / 2) ≤ 2 := by
        have h := Real.abs_exp_sub_one_le (x := Λ / 2) (by
          rw [abs_of_nonneg (by linarith : 0 ≤ Λ / 2)]
          linarith)
        rw [abs_of_nonneg (by linarith : 0 ≤ Λ / 2)] at h
        linarith [le_abs_self (Real.exp (Λ / 2) - 1)]
      apply he.trans
      have hpow0 := Real.rpow_nonneg (div_pos hρ.1 hR).le (1 - n / p)
      nlinarith [mul_le_mul_of_nonneg_right
        (show Real.exp (Λ / 2) / 2 ≤ 1 by linarith) (mul_nonneg hΛ hpow0)]
  · intro σ ρ hσ hσρ hρR
    let D := ∫ x in closedBall ξ ρ \ closedBall ξ σ,
      V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight
    let Cη := fun η t ↦ f' η t * (V.weight.real (closedBall ξ t) / t ^ n) + (f' η t - 1)
    let C := fun t ↦ F t * (V.weight.real (closedBall ξ t) / t ^ n) + (F t - 1)
    have hC : ∀ t ∈ Ioc 0 R, Tendsto (fun η ↦ Cη η t) (L : Filter ℝ) (𝓝 (C t)) := by
      intro t ht
      exact ((hlim t ht).mul_const _).add ((hlim t ht).sub_const 1)
    have hCdiff := (hC ρ ⟨hσ.trans_le hσρ, hρR⟩).sub (hC σ ⟨hσ, hσρ.trans hρR⟩)
    have hplus : Tendsto (fun η : ℝ ↦ Λ + η) (L : Filter ℝ) (𝓝 Λ) := by
      simpa only [add_zero] using hid.const_add Λ
    constructor
    · apply le_of_tendsto_of_tendsto
        (((Real.continuous_exp.tendsto _).comp hplus.neg).mul_const D) hCdiff
      filter_upwards [hpos] with η hη
      dsimp [Cη]
      rw [hf' η hη]
      exact ((hf η hη).2 σ ρ hσ hσρ hρR).1
    · apply le_of_tendsto_of_tendsto hCdiff
        (((Real.continuous_exp.tendsto _).comp hplus).mul_const D)
      filter_upwards [hpos] with η hη
      dsimp [Cη]
      rw [hf' η hη]
      exact ((hf η hη).2 σ ρ hσ hσρ hρR).2

/-- The simultaneous conclusions (4.5)--(4.8). The error is `F-1`, and the
annular integral is the actual closed-ball defect integral of the varifold.
This structure is a conclusion, not a hypothesis on the first variation. -/
structure LpAnnularCorrection (ξ : E) (p R Λ : ℝ) (F : ℝ → ℝ) (G : ℝ → ℝ → ℝ) : Prop where
  factor_bounds : ∀ ρ ∈ Ioc 0 R,
    Real.exp (-Λ) ≤ Real.exp (-Λ / 2 * (ρ / R) ^ (1 - n / p)) ∧
    Real.exp (-Λ / 2 * (ρ / R) ^ (1 - n / p)) ≤ F ρ ∧
    F ρ ≤ Real.exp (Λ / 2 * (ρ / R) ^ (1 - n / p)) ∧
    Real.exp (Λ / 2 * (ρ / R) ^ (1 - n / p)) ≤ Real.exp Λ
  error_bound : ∀ ρ ∈ Ioc 0 R,
    |F ρ - 1| ≤ (Real.exp (Λ / 2) / 2) * Λ * (ρ / R) ^ (1 - n / p)
  error_bound_of_le_one : Λ ≤ 1 → ∀ ρ ∈ Ioc 0 R,
    |F ρ - 1| ≤ Λ * (ρ / R) ^ (1 - n / p)
  annular_factor_bounds : ∀ σ ρ, 0 < σ → σ ≤ ρ → ρ ≤ R →
    G σ ρ ∈ Icc (Real.exp (-Λ)) (Real.exp Λ)
  annular_identity : ∀ σ ρ, 0 < σ → σ ≤ ρ → ρ ≤ R →
    (F ρ * (V.weight.real (closedBall ξ ρ) / ρ ^ n) + (F ρ - 1)) -
      (F σ * (V.weight.real (closedBall ξ σ) / σ ^ n) + (F σ - 1)) =
        G σ ρ * ∫ x in closedBall ξ ρ \ closedBall ξ σ,
          V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight
  monotone : MonotoneOn (fun ρ ↦
    F ρ * (V.weight.real (closedBall ξ ρ) / ρ ^ n) + (F ρ - 1)) (Ioc 0 R)

/-- Corrected Simon (4.7), together with (4.5), (4.6), and (4.8), for one
pair of functions `F,G` at all `0<σ≤ρ≤R`. The two compactness arguments
start from the actual signed curvature pairing in the first variation. -/
theorem HasGeneralizedMeanCurvatureIn.exists_lpAnnularCorrection
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R S Λ : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R) (hRS : R < S)
    (hball : closedBall ξ S ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ S)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ) :
    ∃ F G, V.LpAnnularCorrection ξ p R Λ F G := by
  obtain ⟨F, hF, hsq⟩ := HasGeneralizedMeanCurvatureIn.exists_cancellationFactor_squeeze
    (V := V) hH ξ hp hR hRS hball hLp hscale
  let D := fun σ ρ ↦ ∫ x in closedBall ξ ρ \ closedBall ξ σ,
    V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight
  let C := fun t ↦ F t * (V.weight.real (closedBall ξ t) / t ^ n) + (F t - 1)
  let G := fun σ ρ ↦ if D σ ρ = 0 then 1 else (C ρ - C σ) / D σ ρ
  have hD : ∀ σ ρ, 0 ≤ D σ ρ := fun σ ρ ↦ MeasureTheory.integral_nonneg
    fun x ↦ div_nonneg (V.radialNormalSq_nonneg ξ x) (pow_nonneg (norm_nonneg _) n)
  have hΛ : 0 ≤ Λ := nonneg_of_mul_nonneg_right
    ((V.scaledLpMeanCurvature_nonneg ξ H hR.le).trans hscale) (lpMeanCurvatureKappa_pos hp)
  have hG : ∀ σ ρ, 0 < σ → σ ≤ ρ → ρ ≤ R →
      G σ ρ ∈ Icc (Real.exp (-Λ)) (Real.exp Λ) ∧ C ρ - C σ = G σ ρ * D σ ρ := by
    intro σ ρ hσ hσρ hρR
    have h := hsq σ ρ hσ hσρ hρR
    change Real.exp (-Λ) * D σ ρ ≤ C ρ - C σ ∧ C ρ - C σ ≤ Real.exp Λ * D σ ρ at h
    by_cases hzero : D σ ρ = 0
    · have hc : C ρ - C σ = 0 := by
        simp only [hzero, mul_zero] at h
        exact le_antisymm h.2 h.1
      simp only [G, ite_eq_left hzero, hzero, mul_zero, hc, and_true]
      exact ⟨Real.exp_le_one_iff.mpr (neg_nonpos.mpr hΛ), Real.one_le_exp_iff.mpr hΛ⟩
    · have hdpos : 0 < D σ ρ := lt_of_le_of_ne (hD σ ρ) (Ne.symm hzero)
      dsimp [G]
      rw [ite_eq_right hzero]
      exact ⟨⟨(le_div_iff₀ hdpos).mpr h.1, (div_le_iff₀ hdpos).mpr h.2⟩,
        (div_mul_cancel₀ _ hzero).symm⟩
  refine ⟨F, G, ?_⟩
  constructor
  · intro ρ hρ
    have hb := lpMonotonicityFactor_bounds hp hR hΛ hρ.1 hρ.2
    exact ⟨hb.1, (hF ρ hρ).1, (hF ρ hρ).2.1, hb.2.2.2⟩
  · exact fun ρ hρ ↦ (hF ρ hρ).2.2.1
  · exact fun hΛ1 ρ hρ ↦ (hF ρ hρ).2.2.2 hΛ1
  · exact fun σ ρ hσ hσρ hρR ↦ (hG σ ρ hσ hσρ hρR).1
  · exact fun σ ρ hσ hσρ hρR ↦ (hG σ ρ hσ hσρ hρR).2
  · intro σ hσ ρ hρ hσρ
    exact sub_nonneg.mp ((mul_nonneg (Real.exp_pos _).le (hD σ ρ)).trans
      (hsq σ ρ hσ.1 hσρ hρ.2).1)

/-- Source-domain formulation: an `Lᵖ` curvature field in the open set
provides the surrounding ball automatically. Only the norm on `B_R` is
subject to the corrected smallness condition (4.2). -/
theorem HasGeneralizedMeanCurvatureIn.exists_lpAnnularCorrection_of_memLp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    (hU : IsOpen U) (ξ : E) {p R Λ : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R)
    (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict U))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ) :
    ∃ F G, V.LpAnnularCorrection ξ p R Λ F G := by
  obtain ⟨S, hRS, hSball⟩ := exists_larger_closedBall_subset hU ξ hR.le hball
  exact HasGeneralizedMeanCurvatureIn.exists_lpAnnularCorrection
    (V := V) hH ξ hp hR hRS hSball
    (hLp.mono_measure (MeasureTheory.Measure.restrict_mono hSball le_rfl)) hscale

/-- The same source conclusions for locally `Lᵖ` curvature, stated on
compact subsets to avoid imposing a finite global `Lᵖ` norm. -/
theorem HasGeneralizedMeanCurvatureIn.exists_lpAnnularCorrection_of_locallyLp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    (hU : IsOpen U) (ξ : E) {p R Λ : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R)
    (hball : closedBall ξ R ⊆ U)
    (hLp : ∀ K : Set E, IsCompact K → K ⊆ U →
      MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict K))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ) :
    ∃ F G, V.LpAnnularCorrection ξ p R Λ F G := by
  obtain ⟨S, hRS, hSball⟩ := exists_larger_closedBall_subset hU ξ hR.le hball
  exact HasGeneralizedMeanCurvatureIn.exists_lpAnnularCorrection
    (V := V) hH ξ hp hR hRS hSball (hLp _ (isCompact_closedBall ξ S) hSball) hscale

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
