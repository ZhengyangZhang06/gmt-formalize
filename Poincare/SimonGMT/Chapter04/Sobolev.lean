module

public import Poincare.SimonGMT.Chapter04.SobolevLayerCake

@[expose] public section

/-!
# The compactly supported varifold Sobolev inequality

The final assembly of Simon (5.7) uses the proved good-ball estimate,
smooth truncations, Tonelli, and continuity from below. The dimension
constant is explicit and nonsharp.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

/-- An explicit nonsharp constant for the varifold Sobolev inequality.
It depends only on the intrinsic dimension, not the ambient dimension. -/
def sobolevConstant (n : ℕ) : ℝ :=
  ((n : ℝ) / ((n : ℝ) - 1)) * (4 * 5 ^ n /
    (Chapter01.realUnitBallVolume (n : ℝ)).toReal ^ ((n : ℝ)⁻¹))

theorem sobolevConstant_pos {n : ℕ} (hn : 2 ≤ n) : 0 < sobolevConstant n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hω : 0 < (Chapter01.realUnitBallVolume (n : ℝ)).toReal := ENNReal.toReal_pos
    (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)).ne'
    (Chapter01.realUnitBallVolume_ne_top _)
  exact mul_pos (div_pos (by linarith) (by linarith))
    (div_pos (by positivity) (Real.rpow_pos_of_pos hω _))

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

/-- The total energy of the genuine level truncations is bounded by
the original varifold energy. Curvature is used only on `tsupport h`;
no global measurability or integrability of `H` is imposed. -/
theorem HasGeneralizedMeanCurvatureIn.lintegral_smooth_truncation_energy_le
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hc : HasCompactSupport h) (hs : tsupport h ⊆ U)
    (hh0 : ∀ x, 0 ≤ h x)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ 1 γ) (hγmono : Monotone γ)
    (hγrange : ∀ s, γ s ∈ Icc 0 1) (hγzero : ∀ s, s ≤ 0 → γ s = 0) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (∫ x,
      deriv γ (h x - t) * ‖V.tangentialGradient h x‖ +
        γ (h x - t) * ‖H x‖ ∂V.weight)) ≤
      ENNReal.ofReal (∫ x, ‖V.tangentialGradient h x‖ + h x * ‖H x‖ ∂V.weight) := by
  have hh' := contDiff_of_tsupport_subset hU hh hs
  have hD := V.integrableOn_norm_tangentialGradient hU hh hc hs
  have hK := (hH.1.integrableOn_compact_subset hs hc).norm
  let q : ℝ → E → ℝ := fun t x ↦
    deriv γ (h x - t) * ‖V.tangentialGradient h x‖ + γ (h x - t) * ‖H x‖
  have hq0 (t : ℝ) (x : E) : 0 ≤ q t x :=
    add_nonneg (mul_nonneg hγmono.deriv_nonneg (norm_nonneg _))
      (mul_nonneg (hγrange _).1 (norm_nonneg _))
  have hqi (t : ℝ) : IntegrableOn (q t) (tsupport h) V.weight := by
    exact (IntegrableOn.continuousOn_mul
      ((hγ.continuous_deriv_one.comp (hh'.continuous.sub continuous_const)).continuousOn)
      hD hc).add (IntegrableOn.continuousOn_mul
        ((hγ.continuous.comp (hh'.continuous.sub continuous_const)).continuousOn) hK hc)
  have hqzero (t : ℝ) (ht : 0 ≤ t) (x : E) (hx : x ∉ tsupport h) : q t x = 0 := by
    dsimp only [q]
    rw [V.tangentialGradient_eq_zero_of_notMem_tsupport hx,
      image_eq_zero_of_notMem_tsupport hx, norm_zero, mul_zero,
      hγzero _ (by linarith), zero_mul, add_zero]
  have hqint (t : ℝ) (ht : 0 ≤ t) :
      ENNReal.ofReal (∫ x, q t x ∂V.weight) =
        ∫⁻ x in tsupport h, ENNReal.ofReal (deriv γ (h x - t)) *
          ENNReal.ofReal ‖V.tangentialGradient h x‖ +
          ENNReal.ofReal (γ (h x - t)) * ENNReal.ofReal ‖H x‖ ∂V.weight := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (hqzero t ht),
      ofReal_integral_eq_lintegral_ofReal (hqi t) (Eventually.of_forall (hq0 t))]
    apply lintegral_congr
    intro x
    dsimp only [q]
    rw [ENNReal.ofReal_add (mul_nonneg hγmono.deriv_nonneg (norm_nonneg _))
      (mul_nonneg (hγrange _).1 (norm_nonneg _)),
      ENNReal.ofReal_mul hγmono.deriv_nonneg, ENNReal.ofReal_mul (hγrange _).1]
  have htonelli := Chapter04.lintegral_smooth_truncation_energy_le
    (V.weight.restrict (tsupport h)) hh'.continuous.measurable.aemeasurable hh0
    hD.aemeasurable.ennreal_ofReal hK.aemeasurable.ennreal_ofReal hγ hγmono hγrange hγzero
  have hQ := HasGeneralizedMeanCurvatureIn.integrable_weightedEnergy_of_hasCompactSupport
    (V := V) hH hU hh hc hs
  have hQ0 (x : E) : 0 ≤ ‖V.tangentialGradient h x‖ + h x * ‖H x‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg (hh0 x) (norm_nonneg _))
  have hQint :
      (∫⁻ x in tsupport h, ENNReal.ofReal ‖V.tangentialGradient h x‖ +
        ENNReal.ofReal (h x) * ENNReal.ofReal ‖H x‖ ∂V.weight) =
      ENNReal.ofReal (∫ x, ‖V.tangentialGradient h x‖ + h x * ‖H x‖ ∂V.weight) := by
    simp_rw [← ENNReal.ofReal_mul (hh0 _),
      ← ENNReal.ofReal_add (norm_nonneg _) (mul_nonneg (hh0 _) (norm_nonneg _))]
    rw [← ofReal_integral_eq_lintegral_ofReal hQ.restrict (Eventually.of_forall hQ0),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ V.weightedEnergy_eq_zero_of_notMem_tsupport hx)]
  rw [hQint] at htonelli
  apply le_trans (le_of_eq ?_) htonelli
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hqint t ht.le

/-- The integrated distribution estimate is uniform in the positive
shift of the superlevel sets. Its moment is the unshifted moment of `h`,
which is finite by compact support. -/
theorem HasGeneralizedMeanCurvatureIn.lintegral_shifted_superlevel_le
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    (hn : 2 ≤ n) (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hc : HasCompactSupport h) (hs : tsupport h ⊆ U)
    (hh0 : ∀ x, 0 ≤ h x) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ ((n : ℝ) - 1)⁻¹) *
      V.weight {x | t + ε < h x}) ≤
      ENNReal.ofReal ((4 * 5 ^ n /
        (Chapter01.realUnitBallVolume (n : ℝ)).toReal ^ ((n : ℝ)⁻¹)) *
        (∫ x, h x ^ ((n : ℝ) / ((n : ℝ) - 1)) ∂V.weight) ^ ((n : ℝ)⁻¹) *
        ∫ x, ‖V.tangentialGradient h x‖ + h x * ‖H x‖ ∂V.weight) := by
  let ω := (Chapter01.realUnitBallVolume (n : ℝ)).toReal
  let p := (n : ℝ) / ((n : ℝ) - 1)
  let a := (n : ℝ)⁻¹
  let b := ((n : ℝ) - 1)⁻¹
  let M := ∫ x, h x ^ p ∂V.weight
  let C := 4 * 5 ^ n / ω ^ a
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < p := div_pos (by linarith) (by linarith)
  have hω : 0 < ω := ENNReal.toReal_pos
    (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)).ne'
    (Chapter01.realUnitBallVolume_ne_top _)
  have hC : 0 ≤ C := div_nonneg (by positivity) (Real.rpow_nonneg hω.le _)
  have hM : 0 ≤ M := integral_nonneg (fun x ↦ Real.rpow_nonneg (hh0 x) _)
  have hMa : 0 ≤ M ^ a := Real.rpow_nonneg hM _
  have hh' := contDiff_of_tsupport_subset hU hh hs
  have hsupport : (∫ x in tsupport h, h x ^ p ∂V.weight) = M := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, Real.zero_rpow hp.ne']
  have hfactor (t : ℝ) (ht : 0 ≤ t) :
      t ^ b * (V.weight.real {x | t < h x}) ^ a ≤ M ^ a := by
    have hf := V.sobolev_superlevel_factor_le_compact_moment hn hh'.continuous hc hh0
      (ε := 0) le_rfl ht
    simp only [add_zero] at hf
    change t ^ b * (V.weight.real {x | t < h x}) ^ a ≤
      (∫ x in tsupport h, h x ^ p ∂V.weight) ^ a at hf
    rwa [hsupport] at hf
  obtain ⟨γ, hγ, hγmono, hγrange, hγzero, hγone⟩ := exists_smooth_superlevel_cutoff hε
  let q : ℝ → E → ℝ := fun t x ↦
    deriv γ (h x - t) * ‖V.tangentialGradient h x‖ + γ (h x - t) * ‖H x‖
  have hq0 (t : ℝ) : 0 ≤ ∫ x, q t x ∂V.weight := integral_nonneg (fun x ↦
    add_nonneg (mul_nonneg hγmono.deriv_nonneg (norm_nonneg _))
      (mul_nonneg (hγrange _).1 (norm_nonneg _)))
  have hpoint (t : ℝ) (ht : 0 < t) :
      t ^ b * V.weight.real {x | t + ε < h x} ≤ C * M ^ a * ∫ x, q t x ∂V.weight := by
    have hsup := HasGeneralizedMeanCurvatureIn.superlevel_measure_le_smooth_truncation
      (V := V) hH hU hn hθ hh hc hs hγ hγmono hγrange hγzero hε hγone ht.le
    calc
      _ ≤ t ^ b * ((4 * 5 ^ n * (V.weight.real {x | t < h x} / ω) ^ a) *
          ∫ x, q t x ∂V.weight) :=
        mul_le_mul_of_nonneg_left hsup (Real.rpow_nonneg ht.le _)
      _ = C * (t ^ b * (V.weight.real {x | t < h x}) ^ a) *
          ∫ x, q t x ∂V.weight := by
        rw [Real.div_rpow
          (show 0 ≤ V.weight.real {x | t < h x} from ENNReal.toReal_nonneg) hω.le]
        dsimp only [C]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hfactor t ht.le) hC) (hq0 t)
  change (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ b) * V.weight {x | t + ε < h x}) ≤
    ENNReal.ofReal (C * M ^ a * _)
  calc
    _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (C * M ^ a) *
        ENNReal.ofReal (∫ x, q t x ∂V.weight) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hB : V.weight {x | t + ε < h x} < ∞ :=
        (measure_mono (show {x | t + ε < h x} ⊆ tsupport h from fun x hx ↦
          subset_tsupport h (ne_of_gt ((add_pos ht hε).trans hx)))).trans_lt hc.measure_lt_top
      have hi := ENNReal.ofReal_le_ofReal (hpoint t ht)
      rwa [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
        measureReal_def, ENNReal.ofReal_toReal hB.ne,
        ENNReal.ofReal_mul (mul_nonneg hC hMa)] at hi
    _ = ENNReal.ofReal (C * M ^ a) *
        ∫⁻ t in Ioi 0, ENNReal.ofReal (∫ x, q t x ∂V.weight) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C * M ^ a) * ENNReal.ofReal
        (∫ x, ‖V.tangentialGradient h x‖ + h x * ‖H x‖ ∂V.weight) := by
      exact mul_le_mul' le_rfl
        (HasGeneralizedMeanCurvatureIn.lintegral_smooth_truncation_energy_le
          (V := V) hH hU hh hc hs hh0 hγ hγmono hγrange hγzero)
    _ = _ := (ENNReal.ofReal_mul (mul_nonneg hC hMa)).symm

/-- Simon (5.7), with an explicit dimension-only constant. The full
layer-cake and zero-shift assembly is proved from the actual generalized
mean-curvature equation. The ambient varifold may have infinite weight,
and its mean curvature need only be locally integrable in `U`. -/
theorem HasGeneralizedMeanCurvatureIn.sobolev_inequality
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    (hn : 2 ≤ n) (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hc : HasCompactSupport h) (hs : tsupport h ⊆ U)
    (hh0 : ∀ x, 0 ≤ h x) :
    (∫ x, h x ^ ((n : ℝ) / ((n : ℝ) - 1)) ∂V.weight) ^
        (((n : ℝ) - 1) / (n : ℝ)) ≤
      sobolevConstant n * ∫ x, ‖V.tangentialGradient h x‖ + h x * ‖H x‖ ∂V.weight := by
  let p := (n : ℝ) / ((n : ℝ) - 1)
  let a := (n : ℝ)⁻¹
  let b := ((n : ℝ) - 1)⁻¹
  let M := ∫ x, h x ^ p ∂V.weight
  let Q := ∫ x, ‖V.tangentialGradient h x‖ + h x * ‖H x‖ ∂V.weight
  let C := 4 * 5 ^ n / (Chapter01.realUnitBallVolume (n : ℝ)).toReal ^ a
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hp : 0 < p := div_pos hn0 hn1
  have hpminus : p - 1 = b := by dsimp [p, b]; field_simp; ring
  have hC : 0 ≤ C := div_nonneg (by positivity) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hM : 0 ≤ M := integral_nonneg (fun x ↦ Real.rpow_nonneg (hh0 x) _)
  have hMa : 0 ≤ M ^ a := Real.rpow_nonneg hM _
  have hQ : 0 ≤ Q := integral_nonneg (fun x ↦
    add_nonneg (norm_nonneg _) (mul_nonneg (hh0 x) (norm_nonneg _)))
  have hh' := contDiff_of_tsupport_subset hU hh hs
  have hMi : Integrable (fun x ↦ h x ^ p) V.weight :=
    (hh'.continuous.rpow_const (fun _ ↦ Or.inr hp.le)).integrable_of_hasCompactSupport
      (hc.comp_left (g := fun z : ℝ ↦ z ^ p) (Real.zero_rpow hp.ne'))
  have hdist : (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ b) * V.weight {x | t < h x}) ≤
      ENNReal.ofReal (C * M ^ a * Q) := by
    apply lintegral_superlevel_le_of_positive_shifts V.weight h
      (measurable_id.pow_const b).ennreal_ofReal
    intro ε hε
    exact HasGeneralizedMeanCurvatureIn.lintegral_shifted_superlevel_le
      (V := V) hH hU hn hθ hh hc hs hh0 hε
  have hlayer : ENNReal.ofReal M = ENNReal.ofReal p *
      ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ b) * V.weight {x | t < h x} := by
    rw [ofReal_integral_eq_lintegral_ofReal hMi
      (Eventually.of_forall (fun x ↦ Real.rpow_nonneg (hh0 x) _))]
    simpa only [hpminus, mul_comm] using lintegral_rpow_eq_lintegral_meas_lt_mul
      V.weight (Eventually.of_forall hh0) hh'.continuous.measurable.aemeasurable hp
  have hmoment : M ≤ (p * C * Q) * M ^ a := by
    apply (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg (mul_nonneg hp.le hC) hQ) hMa)).mp
    calc
      ENNReal.ofReal M = _ := hlayer
      _ ≤ ENNReal.ofReal p * ENNReal.ofReal (C * M ^ a * Q) := mul_le_mul' le_rfl hdist
      _ = ENNReal.ofReal ((p * C * Q) * M ^ a) := by
        rw [← ENNReal.ofReal_mul hp.le]
        congr 1
        ring
  have ha : a < 1 := by
    dsimp [a]
    exact (inv_lt_one₀ hn0).mpr (by linarith)
  have hnorm := rpow_one_sub_le_of_le_rpow_mul hM ha
    (mul_nonneg (mul_nonneg hp.le hC) hQ) hmoment
  have hexponent : 1 - a = ((n : ℝ) - 1) / (n : ℝ) := by
    dsimp [a]
    field_simp
  rw [hexponent] at hnorm
  exact hnorm

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
