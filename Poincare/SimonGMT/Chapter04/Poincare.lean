module

public import Poincare.SimonGMT.Chapter04.PoincareTruncation

@[expose] public section

/-!
# Simon (5.6): the local Poincare inequality

Spatial Tonelli integrates the absorbed pointwise potential. A second
Tonelli argument integrates the smooth truncation derivatives over the
levels, and continuity from below removes the positive level shift.
The function is only locally C1; no compact support is required.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

/-- Integration over positive levels removes the smooth truncation
derivative. Almost-everywhere nonnegativity is sufficient, so the lemma
applies to a function restricted to a ball in its regularity domain. -/
theorem lintegral_smooth_truncation_gradient_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {h : X → ℝ} (hh : AEMeasurable h μ)
    (hh0 : ∀ᵐ x ∂μ, 0 ≤ h x) {D : X → ℝ≥0∞} (hD : AEMeasurable D μ)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ 1 γ) (hγmono : Monotone γ)
    (hγle : ∀ s, γ s ≤ 1) (hγzero : ∀ s, s ≤ 0 → γ s = 0) :
    (∫⁻ t in Ioi 0, ∫⁻ x, ENNReal.ofReal (deriv γ (h x - t)) * D x ∂μ) ≤
      ∫⁻ x, D x ∂μ := by
  let k : X → ℝ → ℝ≥0∞ := fun x t ↦ ENNReal.ofReal (deriv γ (h x - t)) * D x
  have hdiff : AEMeasurable (fun z : X × ℝ ↦ h z.1 - z.2)
      (μ.prod (volume.restrict (Ioi 0))) := hh.comp_fst.sub measurable_snd.aemeasurable
  have hk : AEMeasurable (uncurry k) (μ.prod (volume.restrict (Ioi 0))) :=
    (hγ.continuous_deriv_one.measurable.comp_aemeasurable hdiff).ennreal_ofReal.mul hD.comp_fst
  change (∫⁻ t in Ioi 0, ∫⁻ x, k x t ∂μ) ≤ _
  rw [← lintegral_lintegral_swap hk]
  apply lintegral_mono_ae
  filter_upwards [hh0] with x hx
  dsimp only [k]
  rw [lintegral_mul_const _ (by fun_prop),
    lintegral_deriv_shifted_cutoff hγ hγmono hγzero hx]
  have hγone : ENNReal.ofReal (γ (h x)) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hγle (h x))
  simpa only [one_mul] using mul_le_mul' hγone (le_refl (D x))

/-- A choice of inner-radius fraction depending only on the intrinsic
dimension and the positivity-set deficit. -/
def poincareRadius (n : ℕ) (α : ℝ) : ℝ :=
  if hα : 0 < α then (exists_poincare_radius n hα).choose else 1 / 4

theorem poincareRadius_spec (n : ℕ) {α : ℝ} (hα : 0 < α) :
    poincareRadius n α ∈ Ioo 0 (1 / 2) ∧
      (1 - α ^ 2) / (1 - poincareRadius n α) ^ n ≤ 1 - α ^ 2 / 2 := by
  simp only [poincareRadius, dite_eq_left hα]
  exact (exists_poincare_radius n hα).choose_spec

/-- An explicit nonsharp constant depending only on `n`, `α`, and the
outer mass bound `Γ`. The radius `ρ` is excluded from this definition. -/
def poincareConstant (n : ℕ) (α Γ : ℝ) : ℝ :=
  (((1 + α) / ((n : ℝ) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal)) *
    (((n + 1 : ℕ) : ℝ) * ((1 + α) * 2 ^ n * Γ) * 2)) / (α ^ 2 / 2)

theorem poincareConstant_pos {n : ℕ} (hn : 0 < n) {α Γ : ℝ}
    (hα : 0 < α) (hΓ : 0 < Γ) : 0 < poincareConstant n α Γ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hω : 0 < (Chapter01.realUnitBallVolume (n : ℝ)).toReal := ENNReal.toReal_pos
    (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)).ne'
    (Chapter01.realUnitBallVolume_ne_top _)
  dsimp only [poincareConstant]
  positivity

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

/-- The spatial integration step in Simon (5.6). The shifted superlevel
measure is controlled by the actual tangential truncation energy on the
outer ball, using the uniform kernel estimate proved from the outer mass
and bounded-curvature hypotheses. -/
theorem HasGeneralizedMeanCurvatureIn.shifted_superlevel_measure_le_local_energy
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    (hn : 0 < n) {ξ : E} {ρ Λ α Γ β ε t : ℝ}
    (hρ : 0 < ρ) (hΛ : 0 ≤ Λ) (hα : α ∈ Ioo 0 1) (hΓ : 0 ≤ Γ)
    (hβ : β ∈ Ioo 0 (1 / 2))
    (hgap : (1 - α ^ 2) / (1 - β) ^ n ≤ 1 - α ^ 2 / 2)
    (hball : closedBall ξ (2 * ρ) ⊆ U)
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    (hexp : Real.exp (Λ * ρ) ≤ 1 + α)
    (hmass : V.weight.real (closedBall ξ (2 * ρ)) ≤ Γ * ρ ^ n)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U)
    (hpositive : V.weight.real ({x | 0 < h x} ∩ closedBall ξ ρ) ≤
      (1 - α) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal * ρ ^ n)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ 1 γ) (hγmono : Monotone γ)
    (hγrange : ∀ s, γ s ∈ Icc 0 1) (hγzero : ∀ s, s ≤ 0 → γ s = 0)
    (hγone : ∀ s, ε ≤ s → γ s = 1) (ht : 0 ≤ t) :
    ENNReal.ofReal (α ^ 2 / 2) *
        (V.weight.restrict (closedBall ξ (β * ρ))) {x | t + ε < h x} ≤
      ENNReal.ofReal (((1 + α) /
        ((n : ℝ) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal)) *
        (((n + 1 : ℕ) : ℝ) * ((1 + α) * 2 ^ n * Γ) * (2 * ρ))) *
      ∫⁻ x in closedBall ξ ρ, ENNReal.ofReal (deriv γ (h x - t)) *
        ENNReal.ofReal ‖V.tangentialGradient h x‖ ∂V.weight := by
  let μ := V.weight.restrict (closedBall ξ ρ)
  let η := V.weight.restrict (closedBall ξ (β * ρ))
  let A := {x | t + ε < h x}
  let ν := η.restrict A
  let c := (1 + α) / ((n : ℝ) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal)
  let K := ((n + 1 : ℕ) : ℝ) * ((1 + α) * 2 ^ n * Γ) * (2 * ρ)
  let q : E → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (deriv γ (h x - t)) *
    ENNReal.ofReal ‖V.tangentialGradient h x‖
  let k : E → E → ℝ≥0∞ := fun x y ↦ q x * ENNReal.ofReal (1 / ‖y - x‖ ^ (n - 1))
  have houter : closedBall ξ ρ ⊆ U :=
    (closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ)).trans hball
  have hinner : closedBall ξ (β * ρ) ⊆ U :=
    (closedBall_subset_closedBall (by nlinarith [hβ.2] : β * ρ ≤ ρ)).trans houter
  have hhh : AEMeasurable h μ :=
    (hh.continuousOn.mono houter).aemeasurable measurableSet_closedBall
  have hhhinner : AEMeasurable h η :=
    (hh.continuousOn.mono hinner).aemeasurable measurableSet_closedBall
  have hA : NullMeasurableSet A η := nullMeasurableSet_lt aemeasurable_const hhhinner
  have hD : AEMeasurable (fun x ↦ ‖V.tangentialGradient h x‖) μ :=
    (V.tangentialGradient_aemeasurableOn hU hh measurableSet_closedBall houter).norm
  have hq : AEMeasurable q μ :=
    (hγ.continuous_deriv_one.measurable.comp_aemeasurable (hhh.sub_const t)).ennreal_ofReal.mul
      hD.ennreal_ofReal
  have hk : AEMeasurable (uncurry k) (μ.prod ν) :=
    hq.comp_fst.mul (by fun_prop : Measurable
      (fun z : E × E ↦ ENNReal.ofReal (1 / ‖z.2 - z.1‖ ^ (n - 1)))).aemeasurable
  have hquot (x y : E) : ENNReal.ofReal
      (deriv γ (h x - t) * ‖V.tangentialGradient h x‖ / ‖x - y‖ ^ (n - 1)) = k x y := by
    dsimp only [k, q]
    rw [← ENNReal.ofReal_mul hγmono.deriv_nonneg,
      ← ENNReal.ofReal_mul (mul_nonneg hγmono.deriv_nonneg (norm_nonneg _)), norm_sub_rev x y]
    congr 1
    ring
  have hpoint : ∀ᵐ y ∂ν, ENNReal.ofReal (α ^ 2 / 2) ≤
      ENNReal.ofReal c * ∫⁻ x, k x y ∂μ := by
    have hsupp : ∀ᵐ y ∂ν, y ∈ V.weight.support :=
      ae_restrict_of_ae (ae_restrict_of_ae V.weight.support_mem_ae)
    have hmem : ∀ᵐ y ∂ν, y ∈ closedBall ξ (β * ρ) :=
      ae_restrict_of_ae (ae_restrict_mem measurableSet_closedBall)
    filter_upwards [hsupp, hmem, ae_restrict_mem₀ hA] with y hyS hyB hyA
    have hval : γ (h y - t) = 1 := hγone _ (by
      change t + ε < h y at hyA
      linarith)
    have hi := HasGeneralizedMeanCurvatureIn.truncation_gap_le_local_potential
      (V := V) hH hU hn hρ hΛ hα hβ hgap hball hbound hθ hexp hh hpositive
      hγ hγmono hγrange hγzero ht hyB hyS hval
    simpa only [hquot] using hi
  have hkernel : ∀ᵐ x ∂μ, (∫⁻ y, ENNReal.ofReal (1 / ‖y - x‖ ^ (n - 1)) ∂ν) ≤
      ENNReal.ofReal K := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    apply (lintegral_mono' Measure.restrict_le_self le_rfl).trans
    exact HasGeneralizedMeanCurvatureIn.lintegral_local_inverse_kernel_le
      (V := V) hH hn hρ hΛ hα.1.le hΓ (by linarith [hβ.2]) hball hbound hexp hmass hx
  change ENNReal.ofReal (α ^ 2 / 2) * η A ≤ ENNReal.ofReal (c * K) * ∫⁻ x, q x ∂μ
  calc
    _ = ∫⁻ _ : E, ENNReal.ofReal (α ^ 2 / 2) ∂ν := by simp [ν]
    _ ≤ ∫⁻ y, ENNReal.ofReal c * ∫⁻ x, k x y ∂μ ∂ν := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal c * ∫⁻ x, ∫⁻ y, k x y ∂ν ∂μ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_lintegral_swap hk]
    _ ≤ ENNReal.ofReal c * ∫⁻ x, q x * ENNReal.ofReal K ∂μ := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono_ae
      filter_upwards [hkernel] with x hx
      dsimp only [k]
      rw [lintegral_const_mul _ (by fun_prop)]
      exact mul_le_mul' le_rfl hx
    _ = _ := by
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
        ENNReal.ofReal_mul (show 0 ≤ c by
          exact div_nonneg (by linarith [hα.1])
            (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg))]
      ac_rfl

/-- Integrating the shifted superlevel bound over all positive levels
gives an estimate uniform in the shift. All integration takes place on
the two prescribed balls. -/
theorem HasGeneralizedMeanCurvatureIn.lintegral_shifted_superlevel_le_poincare
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    (hn : 0 < n) {ξ : E} {ρ Λ α Γ β ε : ℝ}
    (hρ : 0 < ρ) (hΛ : 0 ≤ Λ) (hα : α ∈ Ioo 0 1) (hΓ : 0 ≤ Γ)
    (hβ : β ∈ Ioo 0 (1 / 2))
    (hgap : (1 - α ^ 2) / (1 - β) ^ n ≤ 1 - α ^ 2 / 2)
    (hball : closedBall ξ (2 * ρ) ⊆ U)
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    (hexp : Real.exp (Λ * ρ) ≤ 1 + α)
    (hmass : V.weight.real (closedBall ξ (2 * ρ)) ≤ Γ * ρ ^ n)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hh0 : ∀ x ∈ U, 0 ≤ h x)
    (hpositive : V.weight.real ({x | 0 < h x} ∩ closedBall ξ ρ) ≤
      (1 - α) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal * ρ ^ n)
    (hε : 0 < ε) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (α ^ 2 / 2) *
      (V.weight.restrict (closedBall ξ (β * ρ))) {x | t + ε < h x}) ≤
      ENNReal.ofReal ((((1 + α) /
        ((n : ℝ) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal)) *
        (((n + 1 : ℕ) : ℝ) * ((1 + α) * 2 ^ n * Γ) * (2 * ρ))) *
        ∫ x in closedBall ξ ρ, ‖V.tangentialGradient h x‖ ∂V.weight) := by
  let μ := V.weight.restrict (closedBall ξ ρ)
  let C := ((1 + α) / ((n : ℝ) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal)) *
    (((n + 1 : ℕ) : ℝ) * ((1 + α) * 2 ^ n * Γ) * (2 * ρ))
  have hC : 0 ≤ C := by
    have hα0 := hα.1.le
    dsimp only [C]
    positivity
  have houter : closedBall ξ ρ ⊆ U :=
    (closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ)).trans hball
  have hhh : AEMeasurable h μ :=
    (hh.continuousOn.mono houter).aemeasurable measurableSet_closedBall
  have hhh0 : ∀ᵐ x ∂μ, 0 ≤ h x := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    exact hh0 x (houter hx)
  have hDi := V.integrableOn_norm_tangentialGradient hU hh (isCompact_closedBall ξ ρ) houter
  obtain ⟨γ, hγ, hγmono, hγrange, hγzero, hγone⟩ := exists_smooth_superlevel_cutoff hε
  have henergy := lintegral_smooth_truncation_gradient_le μ hhh hhh0
    hDi.aemeasurable.ennreal_ofReal hγ hγmono (fun s ↦ (hγrange s).2) hγzero
  change _ ≤ ENNReal.ofReal (C * ∫ x, ‖V.tangentialGradient h x‖ ∂μ)
  calc
    _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal C *
        ∫⁻ x, ENNReal.ofReal (deriv γ (h x - t)) *
          ENNReal.ofReal ‖V.tangentialGradient h x‖ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact HasGeneralizedMeanCurvatureIn.shifted_superlevel_measure_le_local_energy
        (V := V) hH hU hn hρ hΛ hα hΓ hβ hgap hball hbound hθ hexp hmass hh hpositive
        hγ hγmono hγrange hγzero hγone ht.le
    _ = ENNReal.ofReal C * ∫⁻ t in Ioi 0,
        ∫⁻ x, ENNReal.ofReal (deriv γ (h x - t)) *
          ENNReal.ofReal ‖V.tangentialGradient h x‖ ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal ‖V.tangentialGradient h x‖ ∂μ :=
      mul_le_mul' le_rfl henergy
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hDi (Eventually.of_forall (fun x ↦ norm_nonneg _)),
        ← ENNReal.ofReal_mul hC]

/-- The local Poincare inequality for any inner radius satisfying the
explicit absorption condition. Compact support of the function is not
assumed. -/
theorem HasGeneralizedMeanCurvatureIn.poincare_inequality_of_radius
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    (hn : 0 < n) {ξ : E} {ρ Λ α Γ β : ℝ}
    (hρ : 0 < ρ) (hΛ : 0 ≤ Λ) (hα : α ∈ Ioo 0 1) (hΓ : 0 ≤ Γ)
    (hβ : β ∈ Ioo 0 (1 / 2))
    (hgap : (1 - α ^ 2) / (1 - β) ^ n ≤ 1 - α ^ 2 / 2)
    (hball : closedBall ξ (2 * ρ) ⊆ U)
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    (hexp : Real.exp (Λ * ρ) ≤ 1 + α)
    (hmass : V.weight.real (closedBall ξ (2 * ρ)) ≤ Γ * ρ ^ n)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hh0 : ∀ x ∈ U, 0 ≤ h x)
    (hpositive : V.weight.real ({x | 0 < h x} ∩ closedBall ξ ρ) ≤
      (1 - α) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal * ρ ^ n) :
    (∫ x in closedBall ξ (β * ρ), h x ∂V.weight) ≤
      poincareConstant n α Γ * ρ * ∫ x in closedBall ξ ρ, ‖V.tangentialGradient h x‖ ∂V.weight := by
  let η := V.weight.restrict (closedBall ξ (β * ρ))
  let C := ((1 + α) / ((n : ℝ) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal)) *
    (((n + 1 : ℕ) : ℝ) * ((1 + α) * 2 ^ n * Γ) * (2 * ρ))
  let Q := ∫ x in closedBall ξ ρ, ‖V.tangentialGradient h x‖ ∂V.weight
  have hC : 0 ≤ C := by
    have hα0 := hα.1.le
    dsimp only [C]
    positivity
  have hQ : 0 ≤ Q := integral_nonneg (fun _ ↦ norm_nonneg _)
  have hinner : closedBall ξ (β * ρ) ⊆ U :=
    (closedBall_subset_closedBall (by nlinarith [hβ.2] : β * ρ ≤ 2 * ρ)).trans hball
  have hhi : Integrable h η :=
    (hh.continuousOn.mono hinner).integrableOn_compact (isCompact_closedBall ξ (β * ρ))
  have hhh0 : ∀ᵐ x ∂η, 0 ≤ h x := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    exact hh0 x (hinner hx)
  have hdist : (∫⁻ t in Ioi 0, ENNReal.ofReal (α ^ 2 / 2) * η {x | t < h x}) ≤
      ENNReal.ofReal (C * Q) := by
    apply lintegral_superlevel_le_of_positive_shifts η h measurable_const
    intro ε hε
    exact HasGeneralizedMeanCurvatureIn.lintegral_shifted_superlevel_le_poincare
      (V := V) hH hU hn hρ hΛ hα hΓ hβ hgap hball hbound hθ hexp hmass hh hh0 hpositive hε
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_eq_lintegral_meas_lt η hhh0 hhi.aemeasurable,
    ← ofReal_integral_eq_lintegral_ofReal hhi hhh0,
    ← ENNReal.ofReal_mul (show 0 ≤ α ^ 2 / 2 by positivity)] at hdist
  have hreal : (α ^ 2 / 2) * (∫ x, h x ∂η) ≤ C * Q :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC hQ)).mp hdist
  calc
    _ ≤ C * Q / (α ^ 2 / 2) :=
      (le_div_iff₀ (show 0 < α ^ 2 / 2 from div_pos (sq_pos_of_pos hα.1) (by norm_num))).mpr
        (by
          change (∫ x, h x ∂η) * (α ^ 2 / 2) ≤ C * Q
          simpa only [mul_comm] using hreal)
    _ = _ := by dsimp only [C, Q, poincareConstant]; ring

/-- Simon (5.6). Both constants are fixed by `n`, `α`, and `Γ`:
`poincareRadius` belongs to `(0,1/2)` and `poincareConstant` is positive
when `Γ>0`. Neither constant depends on the function, the ball radius,
the varifold, or the ambient dimension. -/
theorem HasGeneralizedMeanCurvatureIn.poincare_inequality
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    (hn : 0 < n) {ξ : E} {ρ Λ α Γ : ℝ}
    (hρ : 0 < ρ) (hα : α ∈ Ioo 0 1) (hΓ : 0 ≤ Γ)
    (hball : closedBall ξ (2 * ρ) ⊆ U)
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x)
    (hexp : Real.exp (Λ * ρ) ≤ 1 + α)
    (hmass : V.weight.real (closedBall ξ (2 * ρ)) ≤ Γ * ρ ^ n)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hh0 : ∀ x ∈ U, 0 ≤ h x)
    (hpositive : V.weight.real ({x | 0 < h x} ∩ closedBall ξ ρ) ≤
      (1 - α) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal * ρ ^ n) :
    (∫ x in closedBall ξ (poincareRadius n α * ρ), h x ∂V.weight) ≤
      poincareConstant n α Γ * ρ * ∫ x in closedBall ξ ρ, ‖V.tangentialGradient h x‖ ∂V.weight := by
  have hexp' : Real.exp (max Λ 0 * ρ) ≤ 1 + α := by
    rcases le_total 0 Λ with hΛ | hΛ
    · simpa only [max_eq_left hΛ] using hexp
    · rw [max_eq_right hΛ, zero_mul, Real.exp_zero]
      linarith [hα.1]
  exact HasGeneralizedMeanCurvatureIn.poincare_inequality_of_radius (V := V) hH hU hn hρ
    (le_max_right Λ 0) hα hΓ (poincareRadius_spec n hα.1).1 (poincareRadius_spec n hα.1).2
    hball (fun x hx ↦ (hbound x hx).trans (le_max_left Λ 0)) hθ hexp' hmass hh hh0 hpositive

end RectifiableVarifold

/-- The existential formulation printed in Simon (5.6). The constants
are chosen before the varifold, curvature field, centre, radius, and
function, so their dependence is exactly `n`, `α`, and `Γ`. -/
theorem exists_poincare_constants (hn : 0 < n) {α Γ : ℝ}
    (hα : α ∈ Ioo 0 1) (hΓ : 0 < Γ) :
    ∃ β c : ℝ, β ∈ Ioo 0 (1 / 2) ∧ 0 < c ∧
      ∀ (V : RectifiableVarifold (E := E) n) (U : Set E) (H : E → E)
        (ξ : E) (ρ Λ : ℝ) (h : E → ℝ),
        V.HasGeneralizedMeanCurvatureIn U H → IsOpen U → 0 < ρ →
        closedBall ξ (2 * ρ) ⊆ U →
        (∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) →
        (∀ᵐ x ∂V.weight.restrict U, 1 ≤ V.multiplicity x) →
        Real.exp (Λ * ρ) ≤ 1 + α →
        V.weight.real (closedBall ξ (2 * ρ)) ≤ Γ * ρ ^ n →
        ContDiffOn ℝ 1 h U → (∀ x ∈ U, 0 ≤ h x) →
        V.weight.real ({x | 0 < h x} ∩ closedBall ξ ρ) ≤
          (1 - α) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal * ρ ^ n →
        (∫ x in closedBall ξ (β * ρ), h x ∂V.weight) ≤
          c * ρ * ∫ x in closedBall ξ ρ, ‖V.tangentialGradient h x‖ ∂V.weight := by
  refine ⟨poincareRadius n α, poincareConstant n α Γ,
    (poincareRadius_spec n hα.1).1, poincareConstant_pos hn hα.1 hΓ, ?_⟩
  intro V U H ξ ρ Λ h hH hU hρ hball hbound hθ hexp hmass hh hh0 hpositive
  exact RectifiableVarifold.HasGeneralizedMeanCurvatureIn.poincare_inequality
    (V := V) hH hU hn hρ hα hΓ.le hball hbound hθ hexp hmass hh hh0 hpositive

end

end Poincare.SimonGMT.Chapter04
