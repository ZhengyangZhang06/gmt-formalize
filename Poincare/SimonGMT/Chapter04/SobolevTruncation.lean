module

public import Poincare.SimonGMT.Chapter04.SobolevGoodRadius

@[expose] public section

/-!
# Smooth superlevel truncations for Simon (5.7)

The smooth shifted truncation is an admissible compactly supported
multiplier. The chain rule below gives its actual tangential energy,
and the covering estimate controls the strict superlevel measure.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

/-- A concrete smooth cutoff supplies all the truncation hypotheses. -/
theorem exists_smooth_superlevel_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ → ℝ, ContDiff ℝ 1 γ ∧ Monotone γ ∧
      (∀ s, γ s ∈ Icc 0 1) ∧ (∀ s, s ≤ 0 → γ s = 0) ∧
      (∀ s, ε ≤ s → γ s = 1) := by
  refine ⟨fun s ↦ Real.smoothTransition (s / ε),
    Real.smoothTransition.contDiff.comp (contDiff_id.div_const ε), ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right hab hε.le)
  · intro s
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro s hs
    exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hs hε.le)
  · intro s hs
    exact Real.smoothTransition.one_of_one_le ((one_le_div hε).mpr hs)

/-- The fundamental theorem of calculus removes the shifted derivative
in the eventual integration over levels. -/
theorem integral_deriv_shifted_cutoff {γ : ℝ → ℝ} (hγ : ContDiff ℝ 1 γ) (a : ℝ) :
    (∫ t in 0..a, deriv γ (a - t)) = γ a - γ 0 := by
  rw [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
  exact intervalIntegral.integral_deriv_eq_sub
    (fun x _ ↦ hγ.differentiable (by simp) x) (hγ.continuous_deriv_one.intervalIntegrable _ _)

theorem deriv_cutoff_eq_zero_of_neg {γ : ℝ → ℝ}
    (hγzero : ∀ s, s ≤ 0 → γ s = 0) {s : ℝ} (hs : s < 0) : deriv γ s = 0 := by
  have heq : γ =ᶠ[𝓝 s] fun _ ↦ 0 := by
    filter_upwards [gt_mem_nhds hs] with t ht
    exact hγzero t ht.le
  exact heq.deriv_eq.trans (deriv_const s 0)

/-- Integration over all nonnegative levels exactly removes a smooth
truncation derivative; its tail is zero rather than an improper-integral
assumption. -/
theorem lintegral_deriv_shifted_cutoff {γ : ℝ → ℝ} (hγ : ContDiff ℝ 1 γ)
    (hγmono : Monotone γ) (hγzero : ∀ s, s ≤ 0 → γ s = 0) {a : ℝ} (ha : 0 ≤ a) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (deriv γ (a - t))) = ENNReal.ofReal (γ a) := by
  rw [← Ioc_union_Ioi_eq_Ioi ha, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  have htail : (∫⁻ t in Ioi a, ENNReal.ofReal (deriv γ (a - t))) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [deriv_cutoff_eq_zero_of_neg hγzero (sub_neg.mpr ht), ENNReal.ofReal_zero,
      Pi.zero_apply]
  have hcont : Continuous (fun t : ℝ ↦ deriv γ (a - t)) :=
    hγ.continuous_deriv_one.comp (continuous_const.sub continuous_id)
  have hint : IntegrableOn (fun t : ℝ ↦ deriv γ (a - t)) (Ioc 0 a) volume :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [htail, add_zero,
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (fun _ ↦ hγmono.deriv_nonneg)),
    ← intervalIntegral.integral_of_le ha, integral_deriv_shifted_cutoff hγ a,
    hγzero 0 le_rfl, sub_zero]

/-- The curvature multiplier integrates to at most the original value. -/
theorem lintegral_shifted_cutoff_le {γ : ℝ → ℝ}
    (hγle : ∀ s, γ s ≤ 1) (hγzero : ∀ s, s ≤ 0 → γ s = 0) {a : ℝ} (ha : 0 ≤ a) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (γ (a - t))) ≤ ENNReal.ofReal a := by
  rw [← Ioc_union_Ioi_eq_Ioi ha, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  have htail : (∫⁻ t in Ioi a, ENNReal.ofReal (γ (a - t))) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [hγzero _ (sub_nonpos.mpr ht.le), ENNReal.ofReal_zero, Pi.zero_apply]
  rw [htail, add_zero]
  calc
    _ ≤ ∫⁻ _ in Ioc (0 : ℝ) a, (1 : ℝ≥0∞) :=
      lintegral_mono fun t ↦ by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hγle (a - t))
    _ = _ := by simp

/-- Tonelli and the two scalar truncation identities bound the total
energy of all level truncations by the original gradient and curvature
energy. All integrals here are extended nonnegative integrals. -/
theorem lintegral_smooth_truncation_energy_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {h : X → ℝ} (hh : AEMeasurable h μ)
    (hh0 : ∀ x, 0 ≤ h x) {D K : X → ℝ≥0∞}
    (hD : AEMeasurable D μ) (hK : AEMeasurable K μ)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ 1 γ) (hγmono : Monotone γ)
    (hγrange : ∀ s, γ s ∈ Icc 0 1) (hγzero : ∀ s, s ≤ 0 → γ s = 0) :
    (∫⁻ t in Ioi 0, ∫⁻ x, ENNReal.ofReal (deriv γ (h x - t)) * D x +
      ENNReal.ofReal (γ (h x - t)) * K x ∂μ) ≤
        ∫⁻ x, D x + ENNReal.ofReal (h x) * K x ∂μ := by
  let k : X → ℝ → ℝ≥0∞ := fun x t ↦ ENNReal.ofReal (deriv γ (h x - t)) * D x +
    ENNReal.ofReal (γ (h x - t)) * K x
  have hdiff : AEMeasurable (fun z : X × ℝ ↦ h z.1 - z.2)
      (μ.prod (volume.restrict (Ioi 0))) := hh.comp_fst.sub measurable_snd.aemeasurable
  have hk : AEMeasurable (uncurry k) (μ.prod (volume.restrict (Ioi 0))) :=
    (((hγ.continuous_deriv_one.measurable.comp_aemeasurable hdiff).ennreal_ofReal.mul hD.comp_fst).add
      ((hγ.continuous.measurable.comp_aemeasurable hdiff).ennreal_ofReal.mul hK.comp_fst))
  change (∫⁻ t in Ioi 0, ∫⁻ x, k x t ∂μ) ≤ _
  rw [← lintegral_lintegral_swap hk]
  apply lintegral_mono
  intro x
  dsimp only [k]
  have hγm : Measurable γ := hγ.continuous.measurable
  have hγdm : Measurable (deriv γ) := hγ.continuous_deriv_one.measurable
  rw [lintegral_add_left (by fun_prop), lintegral_mul_const _ (by fun_prop),
    lintegral_mul_const _ (by fun_prop), lintegral_deriv_shifted_cutoff hγ hγmono hγzero (hh0 x)]
  have hγle : ENNReal.ofReal (γ (h x)) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hγrange (h x)).2
  have hmass := lintegral_shifted_cutoff_le (fun s ↦ (hγrange s).2) hγzero (hh0 x)
  simpa only [one_mul] using add_le_add
    (mul_le_mul' hγle (le_refl (D x))) (mul_le_mul' hmass (le_refl (K x)))

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

theorem tangentialGradient_comp_sub_const {h : E → ℝ} {γ : ℝ → ℝ} {x : E} (t : ℝ)
    (hh : DifferentiableAt ℝ h x) (hγ : DifferentiableAt ℝ γ (h x - t)) :
    V.tangentialGradient (fun y ↦ γ (h y - t)) x =
      deriv γ (h x - t) • V.tangentialGradient h x := by
  apply ext_inner_left ℝ
  intro v
  rw [inner_tangentialGradient, real_inner_smul_right, inner_tangentialGradient]
  have hd : fderiv ℝ (fun y ↦ γ (h y - t)) x =
      deriv γ (h x - t) • fderiv ℝ h x := by
    simpa only [Function.comp_def] using
      (hγ.hasDerivAt.comp_hasFDerivAt x (hh.hasFDerivAt.sub_const t)).fderiv
  rw [hd]
  rfl

/-- Applying the proved covering estimate to `γ(h-t)` gives the smooth
truncation inequality on printed page 99, with the corrected nonsharp
constant and no extra bound on generalized mean curvature. -/
theorem HasGeneralizedMeanCurvatureIn.superlevel_measure_le_smooth_truncation
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    (hn : 2 ≤ n) (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hc : HasCompactSupport h) (hs : tsupport h ⊆ U)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ 1 γ) (hγmono : Monotone γ)
    (hγrange : ∀ s, γ s ∈ Icc 0 1) (hγzero : ∀ s, s ≤ 0 → γ s = 0)
    {ε t : ℝ} (_hε : 0 < ε) (hγone : ∀ s, ε ≤ s → γ s = 1) (ht : 0 ≤ t) :
    V.weight.real {x | t + ε < h x} ≤
      (4 * 5 ^ n * (V.weight.real {x | t < h x} /
        (Chapter01.realUnitBallVolume (n : ℝ)).toReal) ^ ((n : ℝ)⁻¹)) *
        ∫ x, deriv γ (h x - t) * ‖V.tangentialGradient h x‖ +
          γ (h x - t) * ‖H x‖ ∂V.weight := by
  let k : E → ℝ := fun x ↦ γ (h x - t)
  let A : Set E := {x | t < h x}
  let B : Set E := {x | t + ε < h x}
  have hh' := contDiff_of_tsupport_subset hU hh hs
  have hk : ContDiff ℝ 1 k := hγ.comp (hh'.sub contDiff_const)
  have hzero : (fun z : ℝ ↦ γ (z - t)) 0 = 0 := hγzero _ (by linarith)
  have hkc : HasCompactSupport k := by
    simpa only [Function.comp_def] using hc.comp_left (g := fun z : ℝ ↦ γ (z - t)) hzero
  have hks : tsupport k ⊆ U := by
    exact (tsupport_comp_subset (g := fun z : ℝ ↦ γ (z - t)) hzero h).trans hs
  have hk0 : ∀ x, 0 ≤ k x := fun x ↦ (hγrange _).1
  have hki : Integrable k V.weight := hk.continuous.integrable_of_hasCompactSupport hkc
  have hA : MeasurableSet A := (isOpen_lt continuous_const hh'.continuous).measurableSet
  have hB : MeasurableSet B := (isOpen_lt continuous_const hh'.continuous).measurableSet
  have hAsub : A ⊆ tsupport h := by
    intro x hx
    exact subset_tsupport h (ne_of_gt (ht.trans_lt hx))
  have hAfinite : V.weight A < ∞ := (measure_mono hAsub).trans_lt hc.measure_lt_top
  have hmass : (∫ x, k x ∂V.weight) ≤ V.weight.real A := by
    rw [← integral_indicator_one hA]
    apply integral_mono hki ((integrableOn_const hAfinite.ne).integrable_indicator hA)
    intro x
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      exact (hγrange _).2
    · rw [indicator_of_notMem hx]
      exact (hγzero _ (sub_nonpos.mpr (le_of_not_gt hx))).le
  have hBvalue : ∀ x ∈ B, k x = 1 := by
    intro x hx
    change t + ε < h x at hx
    exact hγone _ (by linarith)
  have hBsub : B ⊆ {x | 1 ≤ k x} := fun x hx ↦ (hBvalue x hx).ge
  have henergy : 0 ≤ ∫ x, ‖V.tangentialGradient k x‖ + k x * ‖H x‖ ∂V.weight :=
    integral_nonneg fun x ↦ add_nonneg (norm_nonneg _) (mul_nonneg (hk0 x) (norm_nonneg _))
  have hchain : ∀ x, ‖V.tangentialGradient k x‖ =
      deriv γ (h x - t) * ‖V.tangentialGradient h x‖ := by
    intro x
    rw [tangentialGradient_comp_sub_const V t (hh'.differentiable (by simp) x)
      (hγ.differentiable (by simp) _), norm_smul,
      Real.norm_of_nonneg (hγmono.deriv_nonneg)]
  calc
    V.weight.real B = ∫ x in B, k x ∂V.weight := by
      rw [setIntegral_congr_fun hB hBvalue]
      simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
        measureReal_def]
    _ ≤ ∫ x in {x | 1 ≤ k x}, k x ∂V.weight :=
      setIntegral_mono_set hki.restrict (Eventually.of_forall hk0) (Eventually.of_forall hBsub)
    _ ≤ (4 * 5 ^ n * ((∫ x, k x ∂V.weight) /
        (Chapter01.realUnitBallVolume (n : ℝ)).toReal) ^ ((n : ℝ)⁻¹)) *
        ∫ x, ‖V.tangentialGradient k x‖ + k x * ‖H x‖ ∂V.weight :=
      HasGeneralizedMeanCurvatureIn.weighted_superlevel_integral_le
        (V := V) hH hU hn hθ hk.contDiffOn hkc hks hk0
    _ ≤ (4 * 5 ^ n * (V.weight.real A /
        (Chapter01.realUnitBallVolume (n : ℝ)).toReal) ^ ((n : ℝ)⁻¹)) *
        ∫ x, ‖V.tangentialGradient k x‖ + k x * ‖H x‖ ∂V.weight := by
      gcongr
      exact div_nonneg (integral_nonneg hk0) ENNReal.toReal_nonneg
    _ = _ := by simp only [hchain, k, A]

/-- The moment bound used after multiplying the truncation inequality
by a power of the level. The auxiliary positive shift is integrated only
over `tsupport h`, which has finite weight even when the varifold does not. -/
theorem superlevel_rpow_mass_le_compact_moment
    {h : E → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (hhnonneg : ∀ x, 0 ≤ h x) {ε t p : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (hp : 0 ≤ p) :
    (t + ε) ^ p * V.weight.real {x | t < h x} ≤
      ∫ x in tsupport h, (h x + ε) ^ p ∂V.weight := by
  let A : Set E := {x | t < h x}
  have hA : MeasurableSet A := (isOpen_lt continuous_const hh).measurableSet
  have hAsub : A ⊆ tsupport h := fun x hx ↦ subset_tsupport h (ne_of_gt (ht.trans_lt hx))
  have hAfinite : V.weight A < ∞ := (measure_mono hAsub).trans_lt hc.measure_lt_top
  have hpow : IntegrableOn (fun x ↦ (h x + ε) ^ p) (tsupport h) V.weight :=
    (((hh.add continuous_const).rpow_const (fun _ ↦ Or.inr hp)).continuousOn).integrableOn_compact hc
  calc
    _ = ∫ _ in A, (t + ε) ^ p ∂V.weight := by
      simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, measureReal_def]
      rw [mul_comm]
    _ ≤ ∫ x in A, (h x + ε) ^ p ∂V.weight :=
      setIntegral_mono_on (integrableOn_const hAfinite.ne) (hpow.mono_set hAsub) hA
        (fun x hx ↦ Real.rpow_le_rpow (add_nonneg ht hε) (add_le_add hx.le le_rfl) hp)
    _ ≤ _ := setIntegral_mono_set hpow
      (Eventually.of_forall (fun x ↦ Real.rpow_nonneg (add_nonneg (hhnonneg x) hε) p))
      (Eventually.of_forall hAsub)

/-- The exact dimension-dependent factor needed to integrate over
levels in the Sobolev proof, with the finite compact-support moment. -/
theorem sobolev_superlevel_factor_le_compact_moment
    (hn : 2 ≤ n) {h : E → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (hhnonneg : ∀ x, 0 ≤ h x) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    (t + ε) ^ ((n : ℝ) - 1)⁻¹ * (V.weight.real {x | t < h x}) ^ ((n : ℝ)⁻¹) ≤
      (∫ x in tsupport h, (h x + ε) ^ ((n : ℝ) / ((n : ℝ) - 1)) ∂V.weight) ^ ((n : ℝ)⁻¹) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnp : 0 ≤ (n : ℝ) / ((n : ℝ) - 1) := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg hn0.le (by linarith)
  have hle := Real.rpow_le_rpow
    (mul_nonneg (Real.rpow_nonneg (add_nonneg ht hε) _) ENNReal.toReal_nonneg)
    (V.superlevel_rpow_mass_le_compact_moment hh hc hhnonneg hε ht hnp) (inv_nonneg.mpr hn0.le)
  rw [Real.mul_rpow (Real.rpow_nonneg (add_nonneg ht hε) _) ENNReal.toReal_nonneg,
    ← Real.rpow_mul (add_nonneg ht hε)] at hle
  convert hle using 1
  congr 2
  field_simp

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
