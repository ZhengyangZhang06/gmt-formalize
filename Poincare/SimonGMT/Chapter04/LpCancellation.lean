module

public import Poincare.SimonGMT.Chapter04.LpDensity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# Simon GMT, Chapter 4, (4.3)--(4.6): the cancellation factor

The factor here is the exponential of the integral of the actual signed
cutoff curvature coefficient. Its derivative cancels that coefficient in
the first-variation identity. This is distinct from the explicit majorizing
factor used earlier to prove density existence.
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

/-- The radial curvature pairing is integrable on every compact ball in
the domain, with no hypothesis on `H` outside that ball. -/
theorem HasGeneralizedMeanCurvatureIn.integrableOn_radialPairing
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {R : ℝ} (hball : closedBall ξ R ⊆ U) :
    MeasureTheory.IntegrableOn (fun x ↦ inner ℝ (x - ξ) (H x)) (closedBall ξ R) V.weight := by
  have hHint := hH.1.integrableOn_compact_subset hball (isCompact_closedBall ξ R)
  apply (hHint.norm.const_mul R).mono'
  · exact ((continuous_id.sub continuous_const).aemeasurable.inner
      hHint.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_closedBall] with x hx
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      (show ‖x - ξ‖ ≤ R by simpa only [mem_closedBall, dist_eq_norm] using hx) (norm_nonneg _))

/-- Continuity in radius of the actual cutoff pairing, obtained by
dominated convergence with the locally integrable curvature field. -/
theorem HasGeneralizedMeanCurvatureIn.continuousOn_cutoffMeanCurvaturePairing
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {R : ℝ} (hball : closedBall ξ R ⊆ U)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφrange : ∀ t, φ t ∈ Icc 0 1)
    {A : ℝ} (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) :
    ContinuousOn (V.cutoffMeanCurvaturePairing ξ H φ) (Ioo 0 (R / A)) := by
  let q := fun x ↦ inner ℝ (x - ξ) (H x)
  have hq := HasGeneralizedMeanCurvatureIn.integrableOn_radialPairing (V := V) hH ξ hball
  have hc : ContinuousOn (fun t ↦ ∫ x in closedBall ξ R,
      scaledRadialCutoff ξ φ t x * q x ∂V.weight) (Ioo 0 (R / A)) := by
    apply MeasureTheory.continuousOn_of_dominated (bound := fun x ↦ ‖q x‖)
    · intro t ht
      exact (hφ.continuous.comp (by fun_prop)).aestronglyMeasurable.mul hq.aestronglyMeasurable
    · intro t ht
      filter_upwards with x
      rw [norm_mul, scaledRadialCutoff, Real.norm_of_nonneg (hφrange _).1]
      exact mul_le_mul_of_nonneg_right (hφrange _).2 (norm_nonneg _) |>.trans_eq (one_mul _)
    · exact hq.norm
    · filter_upwards with x
      intro t ht
      exact ((hasDerivAt_scaledRadialCutoff ξ x hφ ht.1.ne').continuousAt.mul
        continuousAt_const).continuousWithinAt
  apply hc.congr
  intro t ht
  symm
  apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hx' : x ∉ closedBall ξ (t * A) :=
    fun h ↦ hx (closedBall_subset_closedBall ((lt_div_iff₀ hA).mp ht.2).le h)
  rw [scaledRadialCutoff_eq_zero_of_notMem_closedBall ξ hA hcutoff ht.1 hx', zero_mul]

theorem HasGeneralizedMeanCurvatureIn.continuousOn_cutoffLpMeanCurvatureError
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {R : ℝ} (hball : closedBall ξ R ⊆ U)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφrange : ∀ t, φ t ∈ Icc 0 1)
    {A : ℝ} (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) :
    ContinuousOn (V.cutoffLpMeanCurvatureError ξ H φ) (Ioo 0 (R / A)) := by
  have hI : ContinuousOn (V.cutoffMass ξ φ) (Ioo 0 (R / A)) := by
    intro t ht
    exact (V.hasDerivAt_cutoffMass ξ hφ hA hcutoff ht.1).continuousAt.continuousWithinAt
  have hN := hI.div (continuousOn_id.pow n) (fun t ht ↦ pow_ne_zero n ht.1.ne')
  have hK := (HasGeneralizedMeanCurvatureIn.continuousOn_cutoffMeanCurvaturePairing
    (V := V) hH ξ hball hφ hφrange hA hcutoff).div
      (continuousOn_id.pow (n + 1)) (fun t ht ↦ pow_ne_zero (n + 1) ht.1.ne')
  apply hK.div (continuousOn_const.add hN)
  intro t ht
  have hmass : 0 ≤ V.cutoffMass ξ φ t := MeasureTheory.integral_nonneg fun x ↦ (hφrange _).1
  exact (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hmass (pow_pos ht.1 n).le)).ne'

/-- In dimension zero the radial curvature pairing vanishes. This fills
the `0<p≤1` case of (4.3), where Hölder conjugate exponents are unavailable. -/
theorem HasGeneralizedMeanCurvatureIn.cutoffMeanCurvaturePairing_eq_zero_of_zero_dim
    {V : RectifiableVarifold (E := E) 0} {U : Set E} {H : E → E}
    (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) (hball : closedBall ξ (ρ * A) ⊆ U) :
    V.cutoffMeanCurvaturePairing ξ H φ ρ = 0 := by
  have h₁ := HasGeneralizedMeanCurvatureIn.cutoffMass_deriv_identity
    (V := V) hH ξ hφ hA hcutoff hρ hball
  have h₂ := IsStationaryIn.cutoffMass_deriv_identity
    (V := V) (V.isStationaryIn_of_zero_dim U) ξ hφ hA hcutoff hρ hball
  linarith

/-- The absolute coefficient estimate in (4.3) under exactly `p>n`.
The zero-dimensional case is included separately, so no `p>1` is added. -/
theorem HasGeneralizedMeanCurvatureIn.abs_cutoffLpMeanCurvatureError_le_of_gt_dim
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R) (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφrange : ∀ t, φ t ∈ Icc 0 1)
    {A ρ : ℝ} (hA : 0 < A) (hA2 : A ≤ 2) (hρ : 0 < ρ)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) (hρA : ρ * A ≤ R) :
    |V.cutoffLpMeanCurvatureError ξ H φ ρ| ≤
      2 * lpMeanCurvatureKappa n p * Λ * R⁻¹ * (ρ / R) ^ (-(n : ℝ) / p) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    have hzero := HasGeneralizedMeanCurvatureIn.cutoffMeanCurvaturePairing_eq_zero_of_zero_dim
      (V := V) hH ξ hφ hA hρ hcutoff ((closedBall_subset_closedBall hρA).trans hball)
    have hκΛ := (V.scaledLpMeanCurvature_nonneg ξ H hR.le).trans hscale
    simp only [cutoffLpMeanCurvatureError, cutoffMeanCurvatureError, hzero, zero_div, abs_zero]
    have h : 0 ≤ 2 * (lpMeanCurvatureKappa 0 p * Λ) * R⁻¹ *
        (ρ / R) ^ (-(0 : ℝ) / p) := by positivity
    simpa only [Nat.cast_zero, mul_assoc] using h
  · have hp1 : 1 < p := lt_of_le_of_lt (by exact_mod_cast (Nat.succ_le_iff.mpr hn)) hp
    exact HasGeneralizedMeanCurvatureIn.abs_cutoffLpMeanCurvatureError_le
      (V := V) hH ξ hp1 hR hball hLp hscale hφ hφrange hA hA2 hρ hcutoff hρA

/-- Corrected (4.3), bundling its actual first-variation identity with the
coefficient estimate for exactly `p>n`, including dimension zero. With the
source's minus-sign notation its `F₀` is the negative of our coefficient. -/
theorem HasGeneralizedMeanCurvatureIn.normalizedCutoffMass_lp_identity_and_bound
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R) (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφrange : ∀ t, φ t ∈ Icc 0 1)
    {A ρ : ℝ} (hA : 0 < A) (hA2 : A ≤ 2) (hρ : 0 < ρ)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) (hρA : ρ * A ≤ R) :
    HasDerivAt (fun t ↦ V.cutoffMass ξ φ t / t ^ n)
      ((∫ x, scaledRadialCutoffDeriv ξ φ ρ x * V.radialNormalSq ξ x ∂V.weight) / ρ ^ n +
        V.cutoffLpMeanCurvatureError ξ H φ ρ * (1 + V.cutoffMass ξ φ ρ / ρ ^ n)) ρ ∧
    |V.cutoffLpMeanCurvatureError ξ H φ ρ| ≤
      2 * lpMeanCurvatureKappa n p * Λ * R⁻¹ * (ρ / R) ^ (-(n : ℝ) / p) := by
  exact ⟨HasGeneralizedMeanCurvatureIn.hasDerivAt_normalizedCutoffMass_lp
      (V := V) hH ξ hφ (fun t ↦ (hφrange t).1) hA hcutoff hρ
      ((closedBall_subset_closedBall hρA).trans hball),
    HasGeneralizedMeanCurvatureIn.abs_cutoffLpMeanCurvatureError_le_of_gt_dim
      (V := V) hH ξ hp hR hball hLp hscale hφ hφrange hA hA2 hρ hcutoff hρA⟩

/-- The genuine cancellation factor: the sign is negative because the
actual first-variation equation contains the plus curvature pairing. -/
def cutoffCancellationFactor (ξ : E) (H : E → E) (φ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  Real.exp (-(∫ t in (0 : ℝ)..ρ, V.cutoffLpMeanCurvatureError ξ H φ t))

def cutoffCancellationError (ξ : E) (H : E → E) (φ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  V.cutoffCancellationFactor ξ H φ ρ - 1

/-- The integrable power majorant for the coefficient in (4.3). -/
def lpCurvatureCoefficientBound (n : ℕ) (p R Λ t : ℝ) : ℝ :=
  2 * lpMeanCurvatureKappa n p * Λ * R⁻¹ * (t / R) ^ (-(n : ℝ) / p)

theorem intervalIntegrable_lpCurvatureCoefficientBound {p R ρ : ℝ}
    (hp : (n : ℝ) < p) (hR : 0 < R) (Λ : ℝ) :
    IntervalIntegrable (lpCurvatureCoefficientBound n p R Λ) MeasureTheory.volume 0 ρ := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have hpow : -1 < -(n : ℝ) / p := by
    rw [lt_div_iff₀ hp0]
    linarith
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ρ / R) hpow).comp_mul_right
    (c := R⁻¹)
  have hi' : IntervalIntegrable (fun t : ℝ ↦ (t / R) ^ (-(n : ℝ) / p))
      MeasureTheory.volume 0 ρ := by
    simpa only [zero_div, div_inv_eq_mul, div_mul_cancel₀ _ hR.ne', zero_mul,
      ← div_eq_mul_inv] using hi
  exact hi'.const_mul _

/-- Integration of the corrected κ gives exactly the coefficient Λ/2
used after (4.4), including all real exponents `p>n`. -/
theorem integral_lpCurvatureCoefficientBound {p R ρ : ℝ}
    (hp : (n : ℝ) < p) (hR : 0 < R) (Λ : ℝ) :
    (∫ t in (0 : ℝ)..ρ, lpCurvatureCoefficientBound n p R Λ t) =
      Λ / 2 * (ρ / R) ^ (1 - n / p) := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have hpow : -1 < -(n : ℝ) / p := by rw [lt_div_iff₀ hp0]; linarith
  have hexp : -(n : ℝ) / p + 1 = 1 - n / p := by ring
  have hα : 0 < 1 - n / p := by rw [sub_pos, div_lt_one hp0]; exact hp
  simp only [lpCurvatureCoefficientBound]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun t : ℝ ↦ t ^ (-(n : ℝ) / p)) hR.ne',
    integral_rpow (Or.inl hpow), zero_div, hexp, Real.zero_rpow hα.ne',
    sub_zero, smul_eq_mul]
  dsimp [lpMeanCurvatureKappa]
  field_simp [hp0.ne', hR.ne', (sub_pos.mpr hp).ne']
  ring

theorem HasGeneralizedMeanCurvatureIn.intervalIntegrable_cutoffLpMeanCurvatureError
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R) (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφrange : ∀ t, φ t ∈ Icc 0 1)
    {A ρ : ℝ} (hA : 0 < A) (hA2 : A ≤ 2) (hρ : 0 < ρ)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) (hρA : ρ * A < R) :
    IntervalIntegrable (V.cutoffLpMeanCurvatureError ξ H φ) MeasureTheory.volume 0 ρ := by
  have hc := HasGeneralizedMeanCurvatureIn.continuousOn_cutoffLpMeanCurvatureError
    (V := V) hH ξ hball hφ hφrange hA hcutoff
  have hsub : Ioc 0 ρ ⊆ Ioo 0 (R / A) := by
    intro t ht
    exact ⟨ht.1, ht.2.trans_lt ((lt_div_iff₀ hA).mpr hρA)⟩
  apply (intervalIntegrable_lpCurvatureCoefficientBound (n := n) (ρ := ρ) hp hR Λ).mono_fun'
  · simpa only [uIoc_of_le hρ.le] using
      (hc.mono hsub).aestronglyMeasurable measurableSet_Ioc
  · rw [uIoc_of_le hρ.le]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    exact HasGeneralizedMeanCurvatureIn.abs_cutoffLpMeanCurvatureError_le_of_gt_dim
      (V := V) hH ξ hp hR hball hLp hscale hφ hφrange hA hA2 ht.1 hcutoff
      ((mul_le_mul_of_nonneg_right ht.2 hA.le).trans hρA.le)

/-- The integrated coefficient bound following (4.4). -/
theorem HasGeneralizedMeanCurvatureIn.abs_integral_cutoffLpMeanCurvatureError_le
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R) (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφrange : ∀ t, φ t ∈ Icc 0 1)
    {A ρ : ℝ} (hA : 0 < A) (hA2 : A ≤ 2) (hρ : 0 < ρ)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) (hρA : ρ * A ≤ R) :
    |∫ t in (0 : ℝ)..ρ, V.cutoffLpMeanCurvatureError ξ H φ t| ≤
      Λ / 2 * (ρ / R) ^ (1 - n / p) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le (f := V.cutoffLpMeanCurvatureError ξ H φ)
    hρ.le (g := lpCurvatureCoefficientBound n p R Λ)
    (Eventually.of_forall fun t ht ↦
      HasGeneralizedMeanCurvatureIn.abs_cutoffLpMeanCurvatureError_le_of_gt_dim
        (V := V) hH ξ hp hR hball hLp hscale hφ hφrange hA hA2 ht.1 hcutoff
        ((mul_le_mul_of_nonneg_right ht.2 hA.le).trans hρA))
    (intervalIntegrable_lpCurvatureCoefficientBound hp hR Λ)
  simpa only [Real.norm_eq_abs, integral_lpCurvatureCoefficientBound hp hR Λ] using h

theorem HasGeneralizedMeanCurvatureIn.hasDerivAt_cutoffCancellationFactor
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R) (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφrange : ∀ t, φ t ∈ Icc 0 1)
    {A ρ : ℝ} (hA : 0 < A) (hA2 : A ≤ 2) (hρ : 0 < ρ)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) (hρA : ρ * A < R) :
    HasDerivAt (V.cutoffCancellationFactor ξ H φ)
      (-V.cutoffCancellationFactor ξ H φ ρ * V.cutoffLpMeanCurvatureError ξ H φ ρ) ρ := by
  have hc := HasGeneralizedMeanCurvatureIn.continuousOn_cutoffLpMeanCurvatureError
    (V := V) hH ξ hball hφ hφrange hA hcutoff
  have hρdom : ρ ∈ Ioo 0 (R / A) := ⟨hρ, (lt_div_iff₀ hA).mpr hρA⟩
  have hi := HasGeneralizedMeanCurvatureIn.intervalIntegrable_cutoffLpMeanCurvatureError
    (V := V) hH ξ hp hR hball hLp hscale hφ hφrange hA hA2 hρ hcutoff hρA
  have hderiv := intervalIntegral.integral_hasDerivAt_right hi
    (hc.stronglyMeasurableAtFilter isOpen_Ioo ρ hρdom)
    (hc.continuousAt (Ioo_mem_nhds hρdom.1 hρdom.2))
  convert hderiv.neg.exp using 1
  · rfl
  · simp only [cutoffCancellationFactor, mul_neg, neg_mul, Pi.neg_apply]

/-- Corrected Simon (4.4): multiplying by the genuine factor cancels the
actual mean-curvature term, leaving only the nonnegative tilt derivative. -/
theorem HasGeneralizedMeanCurvatureIn.hasDerivAt_cancelledCutoffMass
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R) (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφrange : ∀ t, φ t ∈ Icc 0 1)
    {A ρ : ℝ} (hA : 0 < A) (hA2 : A ≤ 2) (hρ : 0 < ρ)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) (hρA : ρ * A < R) :
    HasDerivAt (fun t ↦ V.cutoffCancellationFactor ξ H φ t *
      (V.cutoffMass ξ φ t / t ^ n) + V.cutoffCancellationError ξ H φ t)
      (V.cutoffCancellationFactor ξ H φ ρ *
        ((∫ x, scaledRadialCutoffDeriv ξ φ ρ x * V.radialNormalSq ξ x ∂V.weight) / ρ ^ n)) ρ := by
  have hF := HasGeneralizedMeanCurvatureIn.hasDerivAt_cutoffCancellationFactor
    (V := V) hH ξ hp hR hball hLp hscale hφ hφrange hA hA2 hρ hcutoff hρA
  have hM := HasGeneralizedMeanCurvatureIn.hasDerivAt_normalizedCutoffMass_lp
    (V := V) hH ξ hφ (fun t ↦ (hφrange t).1) hA hcutoff hρ
    ((closedBall_subset_closedBall hρA.le).trans hball)
  convert (hF.mul hM).add (hF.sub_const 1) using 1
  · funext t
    rfl
  · ring

/-- The fine exponential bounds (4.5) for the genuine cancellation factor. -/
theorem HasGeneralizedMeanCurvatureIn.cutoffCancellationFactor_bounds
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R) (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφrange : ∀ t, φ t ∈ Icc 0 1)
    {A ρ : ℝ} (hA : 0 < A) (hA2 : A ≤ 2) (hρ : 0 < ρ)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) (hρA : ρ * A ≤ R) :
    Real.exp (-Λ / 2 * (ρ / R) ^ (1 - n / p)) ≤ V.cutoffCancellationFactor ξ H φ ρ ∧
      V.cutoffCancellationFactor ξ H φ ρ ≤ Real.exp (Λ / 2 * (ρ / R) ^ (1 - n / p)) := by
  have hb := abs_le.mp (HasGeneralizedMeanCurvatureIn.abs_integral_cutoffLpMeanCurvatureError_le
    (V := V) hH ξ hp hR hball hLp hscale hφ hφrange hA hA2 hρ hcutoff hρA)
  constructor <;> apply Real.exp_le_exp.mpr <;> linarith

private theorem abs_exp_sub_one_le_exp_abs_mul_abs (s : ℝ) :
    |Real.exp s - 1| ≤ Real.exp |s| * |s| := by
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hs))]
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-s)) (Real.exp_pos s).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
    nlinarith
  · have hs' : s ≤ 0 := (lt_of_not_ge hs).le
    rw [abs_of_nonpos hs', abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hs'))]
    have h := Real.add_one_le_exp s
    have hmul := mul_le_mul_of_nonneg_right
      (Real.one_le_exp_iff.mpr (neg_nonneg.mpr hs')) (neg_nonneg.mpr hs')
    nlinarith

/-- The error bound (4.5) for the genuine cancellation factor, rather than
for its explicit majorant. -/
theorem HasGeneralizedMeanCurvatureIn.abs_cutoffCancellationError_le
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R) (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφrange : ∀ t, φ t ∈ Icc 0 1)
    {A ρ : ℝ} (hA : 0 < A) (hA2 : A ≤ 2) (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) (hρA : ρ * A ≤ R) :
    |V.cutoffCancellationError ξ H φ ρ| ≤
      (Real.exp (Λ / 2) / 2) * Λ * (ρ / R) ^ (1 - n / p) := by
  let s := -(∫ t in (0 : ℝ)..ρ, V.cutoffLpMeanCurvatureError ξ H φ t)
  have hb : |s| ≤ Λ / 2 * (ρ / R) ^ (1 - n / p) := by
    simpa only [s, abs_neg] using
      HasGeneralizedMeanCurvatureIn.abs_integral_cutoffLpMeanCurvatureError_le
        (V := V) hH ξ hp hR hball hLp hscale hφ hφrange hA hA2 hρ hcutoff hρA
  have hΛ : 0 ≤ Λ := nonneg_of_mul_nonneg_right
    ((V.scaledLpMeanCurvature_nonneg ξ H hR.le).trans hscale) (lpMeanCurvatureKappa_pos hp)
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have hα : 0 ≤ 1 - n / p := sub_nonneg.mpr ((div_le_one hp0).mpr hp.le)
  have hpow := Real.rpow_le_one (div_pos hρ hR).le ((div_le_one hR).mpr hρR) hα
  have hbΛ : |s| ≤ Λ / 2 := hb.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (show 0 ≤ Λ / 2 by positivity))
  change |Real.exp s - 1| ≤ _
  calc
    _ ≤ Real.exp |s| * |s| := abs_exp_sub_one_le_exp_abs_mul_abs s
    _ ≤ Real.exp (Λ / 2) * (Λ / 2 * (ρ / R) ^ (1 - n / p)) :=
      mul_le_mul (Real.exp_le_exp.mpr hbΛ) hb (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

theorem HasGeneralizedMeanCurvatureIn.abs_cutoffCancellationError_le_of_le_one
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R) (hΛ1 : Λ ≤ 1)
    (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφrange : ∀ t, φ t ∈ Icc 0 1)
    {A ρ : ℝ} (hA : 0 < A) (hA2 : A ≤ 2) (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) (hρA : ρ * A ≤ R) :
    |V.cutoffCancellationError ξ H φ ρ| ≤ Λ * (ρ / R) ^ (1 - n / p) := by
  let s := -(∫ t in (0 : ℝ)..ρ, V.cutoffLpMeanCurvatureError ξ H φ t)
  have hb : |s| ≤ Λ / 2 * (ρ / R) ^ (1 - n / p) := by
    simpa only [s, abs_neg] using
      HasGeneralizedMeanCurvatureIn.abs_integral_cutoffLpMeanCurvatureError_le
        (V := V) hH ξ hp hR hball hLp hscale hφ hφrange hA hA2 hρ hcutoff hρA
  have hΛ : 0 ≤ Λ := nonneg_of_mul_nonneg_right
    ((V.scaledLpMeanCurvature_nonneg ξ H hR.le).trans hscale) (lpMeanCurvatureKappa_pos hp)
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have hα : 0 ≤ 1 - n / p := sub_nonneg.mpr ((div_le_one hp0).mpr hp.le)
  have hpow := Real.rpow_le_one (div_pos hρ hR).le ((div_le_one hR).mpr hρR) hα
  have hb1 : |s| ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hpow (show 0 ≤ Λ / 2 by positivity)]
  have he := Real.abs_exp_sub_one_le hb1
  change |Real.exp s - 1| ≤ _
  linarith

private theorem cancellation_sub_le_sub_of_hasDerivAt_le {a b : ℝ} (hab : a ≤ b)
    {f g f' g' : ℝ → ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hle : ∀ t ∈ Icc a b, f' t ≤ g' t) : f b - f a ≤ g b - g a := by
  have hmono : MonotoneOn (fun t ↦ g t - f t) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun t ht ↦ ((hg t ht).sub (hf t ht)).continuousAt.continuousWithinAt)
    · intro t ht
      exact ((hg t (interior_subset ht)).sub
        (hf t (interior_subset ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [((hg t (interior_subset ht)).sub (hf t (interior_subset ht))).deriv]
      exact sub_nonneg.mpr (hle t (interior_subset ht))
  have h := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  linarith

/-- The weighted cutoff squeeze used to pass to the simultaneous annular
identity. The same cancellation factor is used at both radii. -/
theorem HasGeneralizedMeanCurvatureIn.cancelledCutoffMass_squeeze
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R) (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ)
    {ε σ ρ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ : 0 < σ) (hσρ : σ ≤ ρ)
    (hρA : ρ * (1 + ε) < R) :
    let C := fun t ↦ V.cutoffCancellationFactor ξ H (monotonicityCutoff ε) t *
      (V.cutoffMass ξ (monotonicityCutoff ε) t / t ^ n) +
        V.cutoffCancellationError ξ H (monotonicityCutoff ε) t
    let G := fun t ↦ ∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) t x *
      V.truncatedRadialDefect ξ σ x ∂V.weight
    Real.exp (-Λ) * (G ρ - G σ) ≤ C ρ - C σ ∧
      C ρ - C σ ≤ Real.exp Λ * (1 + ε) ^ n * (G ρ - G σ) := by
  let F := V.cutoffCancellationFactor ξ H (monotonicityCutoff ε)
  let C := fun t ↦ F t * (V.cutoffMass ξ (monotonicityCutoff ε) t / t ^ n) +
    V.cutoffCancellationError ξ H (monotonicityCutoff ε) t
  let G := fun t ↦ ∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) t x *
    V.truncatedRadialDefect ξ σ x ∂V.weight
  let G' := fun t ↦ ∫ x, scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) t x *
    V.truncatedRadialDefect ξ σ x ∂V.weight
  let N := fun t ↦ (∫ x, scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) t x *
    V.radialNormalSq ξ x ∂V.weight) / t ^ n
  have hA : 0 < 1 + ε := by linarith
  have hA2 : 1 + ε ≤ 2 := by linarith
  have hΛ : 0 ≤ Λ := nonneg_of_mul_nonneg_right
    ((V.scaledLpMeanCurvature_nonneg ξ H hR.le).trans hscale) (lpMeanCurvatureKappa_pos hp)
  have hG : ∀ t ∈ Icc σ ρ, HasDerivAt G (G' t) t := by
    intro t ht
    exact (V.hasDerivAt_integral_scaledRadialCutoff_mul ξ (contDiff_monotonicityCutoff ε)
      hA (monotonicityCutoff_cutoff hε) (hσ.trans_le ht.1)
      (V.truncatedRadialDefect_aemeasurable ξ σ).aestronglyMeasurable
      (V.norm_truncatedRadialDefect_le ξ hσ)).2
  have hC : ∀ t ∈ Icc σ ρ, HasDerivAt C (F t * N t) t := by
    intro t ht
    exact HasGeneralizedMeanCurvatureIn.hasDerivAt_cancelledCutoffMass
      (V := V) hH ξ hp hR hball hLp hscale (contDiff_monotonicityCutoff ε)
      (monotonicityCutoff_mem_Icc ε) hA hA2 (hσ.trans_le ht.1)
      (monotonicityCutoff_cutoff hε)
      ((mul_le_mul_of_nonneg_right ht.2 hA.le).trans_lt hρA)
  have hN : ∀ t ∈ Icc σ ρ, G' t ≤ N t ∧ N t ≤ (1 + ε) ^ n * G' t := by
    intro t ht
    have hgint := (V.hasDerivAt_integral_scaledRadialCutoff_mul ξ
      (contDiff_monotonicityCutoff ε) hA (monotonicityCutoff_cutoff hε) (hσ.trans_le ht.1)
      (V.truncatedRadialDefect_aemeasurable ξ σ).aestronglyMeasurable
      (V.norm_truncatedRadialDefect_le ξ hσ)).1
    have hnint := (V.hasDerivAt_integral_scaledRadialCutoff_mul ξ
      (contDiff_monotonicityCutoff ε) hA (monotonicityCutoff_cutoff hε) (hσ.trans_le ht.1)
      (V.radialNormalSq_aemeasurable ξ).aestronglyMeasurable (fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (V.radialNormalSq_nonneg ξ x)]
        exact V.radialNormalSq_le_one ξ x)).1
    constructor
    · simpa only [G', N, MeasureTheory.integral_div] using
        MeasureTheory.integral_mono hgint (hnint.div_const (t ^ n))
          (fun x ↦ (V.scaledRadialCutoffDeriv_defect_bounds ξ x hε hσ ht.1).1)
    · simpa only [G', N, MeasureTheory.integral_div, MeasureTheory.integral_const_mul] using
        MeasureTheory.integral_mono (hnint.div_const (t ^ n)) (hgint.const_mul ((1 + ε) ^ n))
          (fun x ↦ (V.scaledRadialCutoffDeriv_defect_bounds ξ x hε hσ ht.1).2)
  have hG'nonneg : ∀ t ∈ Icc σ ρ, 0 ≤ G' t := by
    intro t ht
    apply MeasureTheory.integral_nonneg
    intro x
    apply mul_nonneg (scaledRadialCutoffDeriv_nonneg ξ x
      (monotonicityCutoff_antitone hε) (hσ.trans_le ht.1))
    exact div_nonneg (V.radialNormalSq_nonneg ξ x)
      (pow_nonneg (le_trans hσ.le (le_max_left _ _)) n)
  have hF : ∀ t ∈ Icc σ ρ, Real.exp (-Λ) ≤ F t ∧ F t ≤ Real.exp Λ := by
    intro t ht
    have ht0 := hσ.trans_le ht.1
    have htA := (mul_le_mul_of_nonneg_right ht.2 hA.le).trans_lt hρA
    have htR : t ≤ R := (by nlinarith [mul_pos ht0 hε] : t ≤ t * (1 + ε)).trans htA.le
    have hf := HasGeneralizedMeanCurvatureIn.cutoffCancellationFactor_bounds
      (V := V) hH ξ hp hR hball hLp hscale (contDiff_monotonicityCutoff ε)
      (monotonicityCutoff_mem_Icc ε) hA hA2 ht0 (monotonicityCutoff_cutoff hε) htA.le
    have hb := lpMonotonicityFactor_bounds hp hR hΛ ht0 htR
    exact ⟨hb.1.trans hf.1, hf.2.trans hb.2.2.2⟩
  constructor
  · have h := cancellation_sub_le_sub_of_hasDerivAt_le hσρ
      (fun t ht ↦ (hG t ht).const_mul (Real.exp (-Λ))) hC (fun t ht ↦ by
        apply mul_le_mul (hF t ht).1 (hN t ht).1 (hG'nonneg t ht)
        exact (Real.exp_pos _).le)
    dsimp [C, F, G] at h ⊢
    linarith
  · have h := cancellation_sub_le_sub_of_hasDerivAt_le hσρ hC
      (fun t ht ↦ (hG t ht).const_mul (Real.exp Λ * (1 + ε) ^ n)) (fun t ht ↦ by
        calc
          F t * N t ≤ Real.exp Λ * ((1 + ε) ^ n * G' t) :=
            mul_le_mul (hF t ht).2 (hN t ht).2
              ((hG'nonneg t ht).trans (hN t ht).1) (Real.exp_pos _).le
          _ = _ := by ring)
    dsimp [C, F, G] at h ⊢
    linarith

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
