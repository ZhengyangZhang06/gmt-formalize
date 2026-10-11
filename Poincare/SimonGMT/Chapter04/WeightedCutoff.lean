module

public import Poincare.SimonGMT.Chapter04.WeightedFirstVariation

@[expose] public section

/-!
# Simon GMT, Chapter 4, (5.1): differentiation of weighted cutoff mass

Local boundedness on a surrounding compact ball suffices to differentiate
the weighted integrals. No global bound or off-domain regularity of the
multiplier is imposed.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

theorem scaledRadialCutoffDeriv_eq_zero_of_notMem_closedBall
    (ξ : E) {φ : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ)
    {x : E} (hx : x ∉ closedBall ξ (ρ * A)) : scaledRadialCutoffDeriv ξ φ ρ x = 0 := by
  have hr : ρ * A < ‖x - ξ‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hx
  have harg : A ^ 2 < ‖x - ξ‖ ^ 2 / ρ ^ 2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos hρ)).mpr
    nlinarith [sq_nonneg (‖x - ξ‖ + ρ * A),
      mul_pos (sub_pos.mpr hr)
        (add_pos_of_nonneg_of_pos (norm_nonneg (x - ξ)) (mul_pos hρ hA))]
  simp only [scaledRadialCutoffDeriv, deriv_eq_zero_of_cutoff hcutoff harg, mul_zero]

/-- The cutoff differentiation theorem with only local measurability and
boundedness on a surrounding ball. Values outside that ball play no role. -/
theorem hasDerivAt_integral_scaledRadialCutoff_mul_local
    (ξ : E) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {A : ℝ} (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0)
    {ρ S : ℝ} (hρ : 0 < ρ) (hρS : ρ * A < S) {q : E → ℝ} {B : ℝ}
    (hq : AEStronglyMeasurable q (V.weight.restrict (closedBall ξ S)))
    (hqb : ∀ x ∈ closedBall ξ S, ‖q x‖ ≤ B) :
    Integrable (fun x ↦ scaledRadialCutoff ξ φ ρ x * q x) V.weight ∧
    Integrable (fun x ↦ scaledRadialCutoffDeriv ξ φ ρ x * q x) V.weight ∧
      HasDerivAt (fun t ↦ ∫ x, scaledRadialCutoff ξ φ t x * q x ∂V.weight)
        (∫ x, scaledRadialCutoffDeriv ξ φ ρ x * q x ∂V.weight) ρ := by
  let q' := (closedBall ξ S).indicator q
  have hq' : AEStronglyMeasurable q' V.weight :=
    (aestronglyMeasurable_indicator_iff measurableSet_closedBall).mpr hq
  have hqb' : ∀ x, ‖q' x‖ ≤ max B 0 := by
    intro x
    by_cases hx : x ∈ closedBall ξ S
    · simpa only [q', indicator_of_mem hx] using (hqb x hx).trans (le_max_left B 0)
    · simp only [q', indicator_of_notMem hx, norm_zero]
      exact le_max_right B 0
  have hpoint : ∀ t, 0 < t → t * A ≤ S →
      (fun x ↦ scaledRadialCutoff ξ φ t x * q x) =
      (fun x ↦ scaledRadialCutoff ξ φ t x * q' x) := by
    intro t ht htS
    funext x
    by_cases hx : x ∈ closedBall ξ S
    · simp only [q', indicator_of_mem hx]
    · have hx' : x ∉ closedBall ξ (t * A) := fun h ↦ hx (closedBall_subset_closedBall htS h)
      simp only [scaledRadialCutoff_eq_zero_of_notMem_closedBall ξ hA hcutoff ht hx', zero_mul]
  have hpoint' : (fun x ↦ scaledRadialCutoffDeriv ξ φ ρ x * q x) =
      (fun x ↦ scaledRadialCutoffDeriv ξ φ ρ x * q' x) := by
    funext x
    by_cases hx : x ∈ closedBall ξ S
    · simp only [q', indicator_of_mem hx]
    · have hx' : x ∉ closedBall ξ (ρ * A) :=
        fun h ↦ hx (closedBall_subset_closedBall hρS.le h)
      simp only [scaledRadialCutoffDeriv_eq_zero_of_notMem_closedBall ξ hA hcutoff hρ hx', zero_mul]
  have hi := V.hasDerivAt_integral_scaledRadialCutoff_mul ξ hφ hA hcutoff hρ hq' hqb'
  refine ⟨?_, ?_, ?_⟩
  · rw [hpoint ρ hρ hρS.le]
    exact (V.integrable_scaledRadialCutoff ξ hφ hA hcutoff hρ).mul_bdd hq'
      (Eventually.of_forall hqb')
  · rw [hpoint']
    exact hi.1
  · rw [hpoint']
    apply hi.2.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hρ ((lt_div_iff₀ hA).mpr hρS)] with t ht
    rw [hpoint t ht.1 ((lt_div_iff₀ hA).mp ht.2).le]

def weightedCutoffMass (ξ : E) (h : E → ℝ) (φ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  ∫ x, scaledRadialCutoff ξ φ ρ x * h x ∂V.weight

def weightedCutoffNormalMass (ξ : E) (h : E → ℝ) (φ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  ∫ x, scaledRadialCutoff ξ φ ρ x * (h x * V.radialNormalSq ξ x) ∂V.weight

def weightedCutoffGradientCurvaturePairing (ξ : E) (h : E → ℝ) (H : E → E)
    (φ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  ∫ x, scaledRadialCutoff ξ φ ρ x *
    inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight

/-- Both weighted cutoff integrals have their source derivatives, under
the literal `C¹(U)` hypothesis rather than a global boundedness assumption. -/
theorem weightedCutoff_derivatives {U : Set E} (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    (Integrable (fun x ↦ scaledRadialCutoff ξ φ ρ x * h x) V.weight ∧
      Integrable (fun x ↦ scaledRadialCutoffDeriv ξ φ ρ x * h x) V.weight ∧
      HasDerivAt (V.weightedCutoffMass ξ h φ)
        (∫ x, scaledRadialCutoffDeriv ξ φ ρ x * h x ∂V.weight) ρ) ∧
    (Integrable (fun x ↦ scaledRadialCutoff ξ φ ρ x * (h x * V.radialNormalSq ξ x)) V.weight ∧
      Integrable (fun x ↦ scaledRadialCutoffDeriv ξ φ ρ x * (h x * V.radialNormalSq ξ x)) V.weight ∧
      HasDerivAt (V.weightedCutoffNormalMass ξ h φ)
        (∫ x, scaledRadialCutoffDeriv ξ φ ρ x * (h x * V.radialNormalSq ξ x) ∂V.weight) ρ) := by
  obtain ⟨S, hρS, hSball⟩ := exists_larger_closedBall_subset hU ξ (mul_pos hρ hA).le hball
  have hc := hh.continuousOn.mono hSball
  have hm := hc.aemeasurable measurableSet_closedBall (μ := V.weight)
  obtain ⟨B, hB⟩ := (isCompact_closedBall ξ S).exists_bound_of_continuousOn hc
  constructor
  · exact V.hasDerivAt_integral_scaledRadialCutoff_mul_local ξ hφ hA hcutoff hρ hρS
      hm.aestronglyMeasurable hB
  · apply V.hasDerivAt_integral_scaledRadialCutoff_mul_local ξ hφ hA hcutoff hρ hρS
      (q := fun x ↦ h x * V.radialNormalSq ξ x) (B := B)
      (hm.mul (V.radialNormalSq_aemeasurable ξ).restrict).aestronglyMeasurable
    intro x hx
    rw [norm_mul, Real.norm_of_nonneg (V.radialNormalSq_nonneg ξ x)]
    exact (mul_le_mul_of_nonneg_left (V.radialNormalSq_le_one ξ x) (norm_nonneg _)).trans
      (by simpa only [mul_one] using hB x hx)

/-- The weighted analogue of the radial relation before division by
`ρⁿ`. Its gradient and curvature pairing is integrable by first variation
and the already differentiated compactly supported terms. -/
theorem HasGeneralizedMeanCurvatureIn.weightedCutoffMass_deriv_identity
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    Integrable (fun x ↦ scaledRadialCutoff ξ φ ρ x *
      inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x)) V.weight ∧
    n * V.weightedCutoffMass ξ h φ ρ - ρ * deriv (V.weightedCutoffMass ξ h φ) ρ =
      -ρ * deriv (V.weightedCutoffNormalMass ξ h φ) ρ -
        V.weightedCutoffGradientCurvaturePairing ξ h H φ ρ := by
  let η : ℝ → ℝ := fun t ↦ φ (t / ρ ^ 2)
  have hη : ContDiff ℝ 1 η := hφ.comp (contDiff_id.div_const (ρ ^ 2))
  have hηcutoff : ∀ t, (ρ * A) ^ 2 ≤ t → η t = 0 := by
    intro t ht
    apply hcutoff
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
    nlinarith [ht]
  have hηderiv : ∀ t, deriv η t = deriv φ (t / ρ ^ 2) / ρ ^ 2 := by
    intro t
    have hderiv := ((hφ.differentiable (by simp) _).hasDerivAt).comp t
      ((hasDerivAt_id t).div_const (ρ ^ 2))
    simpa [η, Function.comp_def, div_eq_mul_inv] using hderiv.deriv
  have hpoint : ∀ x : E, 2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2 =
      -ρ * scaledRadialCutoffDeriv ξ φ ρ x := by
    intro x
    rw [hηderiv, scaledRadialCutoffDeriv]
    field_simp
  let X := squaredRadialVectorField ξ η
  have hX : ContDiff ℝ 1 X := contDiff_squaredRadialVectorField ξ hη
  have hXcompact : HasCompactSupport X :=
    hasCompactSupport_squaredRadialVectorField ξ (mul_pos hρ hA).le hηcutoff
  have hXsupport : tsupport X ⊆ U :=
    (tsupport_squaredRadialVectorField_subset_closedBall ξ (mul_pos hρ hA).le hηcutoff).trans hball
  have hfv := HasGeneralizedMeanCurvatureIn.integral_weighted_firstVariation
    (V := V) hH hU hh hX hXcompact hXsupport
  obtain ⟨hI, hJ⟩ := V.weightedCutoff_derivatives hU hh ξ hφ hA hcutoff hρ hball
  let main := fun x ↦ n * (scaledRadialCutoff ξ φ ρ x * h x) -
    ρ * (scaledRadialCutoffDeriv ξ φ ρ x * h x) +
      ρ * (scaledRadialCutoffDeriv ξ φ ρ x * (h x * V.radialNormalSq ξ x))
  let grad := fun x ↦ scaledRadialCutoff ξ φ ρ x * inner ℝ (x - ξ) (V.tangentialGradient h x)
  let curv := fun x ↦ scaledRadialCutoff ξ φ ρ x * h x * inner ℝ (x - ξ) (H x)
  have hmain : Integrable main V.weight :=
    ((hI.1.const_mul n).sub (hI.2.1.const_mul ρ)).add (hJ.2.1.const_mul ρ)
  have hT : (fun x ↦ h x * V.tangentialDivergence X x +
      inner ℝ (X x) (V.tangentialGradient h x)) =ᵐ[V.weight] fun x ↦ main x + grad x := by
    filter_upwards [V.tangent_finrank_ae_weight] with x hx
    rw [V.tangentialDivergence_squaredRadialVectorField_normal ξ x
      ((hη.differentiable (by simp) _).hasDerivAt) hx, hpoint]
    simp only [X, squaredRadialVectorField, real_inner_smul_left, main, grad,
      scaledRadialCutoff, η]
    ring
  have hgrad : Integrable grad V.weight := by
    apply ((hfv.1.congr hT).sub hmain).congr
    filter_upwards with x
    change (main x + grad x) - main x = grad x
    ring
  have hcurv : Integrable curv V.weight := by
    have hc := HasGeneralizedMeanCurvatureIn.integrable_inner (V := V) hH
      (contDiff_smul_of_tsupport_subset hU hh hX hXsupport).continuous hXcompact.smul_left
      ((tsupport_smul_subset_right h X).trans hXsupport)
    apply hc.congr
    filter_upwards with x
    simp only [curv, X, squaredRadialVectorField, real_inner_smul_left, scaledRadialCutoff, η]
    ring
  have hpair : (fun x ↦ scaledRadialCutoff ξ φ ρ x *
      inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x)) = fun x ↦ grad x + curv x := by
    funext x
    simp only [grad, curv, inner_add_right, real_inner_smul_right]
    ring
  refine ⟨by rw [hpair]; exact hgrad.add hcurv, ?_⟩
  have heq := hfv.2
  rw [integral_congr_ae hT, integral_add hmain hgrad] at heq
  have hmainint : (∫ x, main x ∂V.weight) = n * V.weightedCutoffMass ξ h φ ρ -
      ρ * (∫ x, scaledRadialCutoffDeriv ξ φ ρ x * h x ∂V.weight) +
      ρ * (∫ x, scaledRadialCutoffDeriv ξ φ ρ x * (h x * V.radialNormalSq ξ x) ∂V.weight) := by
    dsimp [main]
    have hsub : Integrable (fun x ↦ n * (scaledRadialCutoff ξ φ ρ x * h x) -
        ρ * (scaledRadialCutoffDeriv ξ φ ρ x * h x)) V.weight :=
      (hI.1.const_mul n).sub (hI.2.1.const_mul ρ)
    rw [integral_add hsub (hJ.2.1.const_mul ρ),
      integral_sub (hI.1.const_mul n) (hI.2.1.const_mul ρ)]
    simp only [integral_const_mul, weightedCutoffMass]
  have hcurvfun : (fun x ↦ h x * inner ℝ (X x) (H x)) = curv := by
    funext x
    simp only [curv, X, squaredRadialVectorField, real_inner_smul_left, scaledRadialCutoff, η]
    ring
  rw [hmainint, hcurvfun] at heq
  rw [hI.2.2.deriv, hJ.2.2.deriv, weightedCutoffGradientCurvaturePairing, hpair,
    integral_add hgrad hcurv]
  linarith

/-- Simon (5.1), including the actual `∇ᴹh+Hh` term, for the literal
domain-wise `C¹` hypothesis. The sign here agrees with the printed (5.1)
and with the defining first-variation convention. -/
theorem HasGeneralizedMeanCurvatureIn.hasDerivAt_normalizedWeightedCutoffMass
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    HasDerivAt (fun t ↦ V.weightedCutoffMass ξ h φ t / t ^ n)
      (deriv (V.weightedCutoffNormalMass ξ h φ) ρ / ρ ^ n +
        V.weightedCutoffGradientCurvaturePairing ξ h H φ ρ / ρ ^ (n + 1)) ρ := by
  have hI := (V.weightedCutoff_derivatives hU hh ξ hφ hA hcutoff hρ hball).1.2.2
  have hrel := (HasGeneralizedMeanCurvatureIn.weightedCutoffMass_deriv_identity
    (V := V) hH hU hh ξ hφ hA hcutoff hρ hball).2
  rw [hI.deriv] at hrel
  have hp : HasDerivAt (fun t : ℝ ↦ t ^ n) (n * ρ ^ n / ρ) ρ := by
    convert (hasDerivAt_id ρ).pow n using 1
    · rfl
    · cases n with
      | zero => simp
      | succ m => simp [pow_succ, hρ.ne', mul_div_assoc]
  convert hI.fun_div hp (pow_ne_zero n hρ.ne') using 1
  · rw [pow_succ]
    field_simp
    linear_combination hrel

/-- The nonnegative normal-derivative term can be discarded, as in the
inequality immediately after (5.1). -/
theorem HasGeneralizedMeanCurvatureIn.deriv_normalizedWeightedCutoffMass_ge
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hhnonneg : ∀ x ∈ U, 0 ≤ h x) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφanti : Antitone φ) {A : ℝ} (hA : 0 < A)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    V.weightedCutoffGradientCurvaturePairing ξ h H φ ρ / ρ ^ (n + 1) ≤
      deriv (fun t ↦ V.weightedCutoffMass ξ h φ t / t ^ n) ρ := by
  rw [(HasGeneralizedMeanCurvatureIn.hasDerivAt_normalizedWeightedCutoffMass
    (V := V) hH hU hh ξ hφ hA hcutoff hρ hball).deriv]
  have hJ := (V.weightedCutoff_derivatives hU hh ξ hφ hA hcutoff hρ hball).2.2.2
  have hn : 0 ≤ deriv (V.weightedCutoffNormalMass ξ h φ) ρ := by
    rw [hJ.deriv]
    apply integral_nonneg
    intro x
    by_cases hx : x ∈ closedBall ξ (ρ * A)
    · exact mul_nonneg (scaledRadialCutoffDeriv_nonneg ξ x hφanti hρ)
        (mul_nonneg (hhnonneg x (hball hx)) (V.radialNormalSq_nonneg ξ x))
    · simp only [scaledRadialCutoffDeriv_eq_zero_of_notMem_closedBall ξ hA hcutoff hρ hx,
        zero_mul, Pi.zero_apply, le_rfl]
  linarith [div_nonneg hn (pow_pos hρ n).le]

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
