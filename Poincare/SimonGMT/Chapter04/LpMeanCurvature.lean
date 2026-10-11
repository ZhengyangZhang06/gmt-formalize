module

public import Poincare.SimonGMT.Chapter04.LogarithmicError
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Simon GMT, Chapter 4, §4: the `Lᵖ` curvature estimate

The Hölder estimate is applied to the actual radial first variation. The
coefficient in (4.2) is corrected to `(p-n)/(4p)`: the printed reciprocal
does not yield the claimed integral bound `Λ/2`. The error in (4.3) has the
plus sign dictated by (3.14); its absolute bound is unchanged.
-/

open Filter Function Metric Set
open scoped ENNReal MeasureTheory Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

private theorem integral_mul_cutoff_le {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    {p : ℝ} (hp : 1 < p) {f ψ : α → ℝ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p) μ)
    (hfnonneg : ∀ x, 0 ≤ f x) (hψmeas : MeasureTheory.AEStronglyMeasurable ψ μ)
    (hψ : ∀ x, ψ x ∈ Icc 0 1) :
    (∫ x, f x * ψ x ∂μ) ≤
      (∫ x, f x ^ p ∂μ) ^ (1 / p) * (∫ x, ψ x ∂μ) ^ (1 - 1 / p) := by
  let q := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hψLp : MeasureTheory.MemLp ψ (ENNReal.ofReal q) μ :=
    MeasureTheory.MemLp.of_bound hψmeas 1 (Eventually.of_forall fun x ↦ by
      rw [Real.norm_of_nonneg (hψ x).1]
      exact (hψ x).2)
  have hψint : MeasureTheory.Integrable ψ μ := hψLp.integrable (by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hpq.symm.lt.le)
  have hψpowint : MeasureTheory.Integrable (fun x ↦ ψ x ^ q) μ := by
    have h := hψLp.integrable_norm_rpow'
    simpa only [ENNReal.toReal_ofReal hpq.symm.nonneg,
      Real.norm_of_nonneg (hψ _).1] using h
  have hpowle : (∫ x, ψ x ^ q ∂μ) ≤ ∫ x, ψ x ∂μ :=
    MeasureTheory.integral_mono hψpowint hψint
      (fun x ↦ Real.rpow_le_self_of_le_one (hψ x).1 (hψ x).2 hpq.symm.lt.le)
  have hexp : 1 / q = 1 - 1 / p := by
    simpa only [one_div] using hpq.one_sub_inv.symm
  calc
    _ ≤ (∫ x, f x ^ p ∂μ) ^ (1 / p) * (∫ x, ψ x ^ q ∂μ) ^ (1 / q) :=
      MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hpq
        (Eventually.of_forall hfnonneg) (Eventually.of_forall fun x ↦ (hψ x).1) hf hψLp
    _ ≤ (∫ x, f x ^ p ∂μ) ^ (1 / p) * (∫ x, ψ x ∂μ) ^ (1 / q) := by
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (MeasureTheory.integral_nonneg fun x ↦
          Real.rpow_nonneg (hψ x).1 _) hpowle hpq.symm.one_div_nonneg)
      exact Real.rpow_nonneg (MeasureTheory.integral_nonneg fun x ↦
        Real.rpow_nonneg (hfnonneg x) _) _
    _ = _ := by rw [hexp]

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

/-- The dimensionless `Lᵖ` curvature quantity in (4.2). -/
def scaledLpMeanCurvature (ξ : E) (H : E → E) (p R : ℝ) : ℝ :=
  (R ^ (p - n) * ∫ x in closedBall ξ R, ‖H x‖ ^ p ∂V.weight) ^ (1 / p)

/-- The corrected coefficient required by the integration following (4.4). -/
def lpMeanCurvatureKappa (n : ℕ) (p : ℝ) : ℝ := (p - n) / (4 * p)

theorem lpMeanCurvatureKappa_pos {p : ℝ} (hp : (n : ℝ) < p) :
    0 < lpMeanCurvatureKappa n p := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  exact div_pos (sub_pos.mpr hp) (mul_pos (by norm_num) hp0)

/-- The first displayed Hölder estimate after (4.2), with the cutoff support
factor `A` retained explicitly. -/
theorem HasGeneralizedMeanCurvatureIn.abs_cutoffMeanCurvatureError_le_holder
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R : ℝ} (hp : 1 < p) (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφrange : ∀ t, φ t ∈ Icc 0 1)
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) (hρA : ρ * A ≤ R) :
    |V.cutoffMeanCurvatureError ξ H φ ρ| ≤
      A / ρ ^ n * (∫ x in closedBall ξ R, ‖H x‖ ^ p ∂V.weight) ^ (1 / p) *
        (V.cutoffMass ξ φ ρ) ^ (1 - 1 / p) := by
  let : MeasureTheory.IsFiniteMeasure (V.weight.restrict (closedBall ξ R)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (isCompact_closedBall ξ R).measure_lt_top.ne
  let ψ := scaledRadialCutoff ξ φ ρ
  have hψcont : Continuous ψ := by
    dsimp [ψ, scaledRadialCutoff]
    exact hφ.continuous.comp (by fun_prop)
  have hψrange : ∀ x, ψ x ∈ Icc 0 1 := fun x ↦ hφrange _
  have hψzero : ∀ x, x ∉ closedBall ξ R → ψ x = 0 := by
    intro x hx
    apply scaledRadialCutoff_eq_zero_of_notMem_closedBall ξ hA hcutoff hρ
    exact fun h ↦ hx (closedBall_subset_closedBall hρA h)
  have hψint := V.integrable_scaledRadialCutoff ξ hφ hA hcutoff hρ
  have hHint := (hH.1.integrableOn_compact_subset hball (isCompact_closedBall ξ R)).norm
  have hprodint : MeasureTheory.IntegrableOn (fun x ↦ ‖H x‖ * ψ x)
      (closedBall ξ R) V.weight :=
    hHint.mul_bdd hψcont.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
      rw [Real.norm_of_nonneg (hψrange x).1]
      exact (hψrange x).2)
  have hprodintall : MeasureTheory.Integrable (fun x ↦ ‖H x‖ * ψ x) V.weight :=
    hprodint.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by rw [hψzero x hx, mul_zero])
  have hbound : ∀ x, ‖ψ x * inner ℝ (x - ξ) (H x)‖ ≤ ρ * A * (‖H x‖ * ψ x) := by
    intro x
    by_cases hx : x ∈ closedBall ξ (ρ * A)
    · rw [norm_mul, Real.norm_of_nonneg (hψrange x).1]
      have hr : ‖x - ξ‖ ≤ ρ * A := by simpa only [mem_closedBall, dist_eq_norm] using hx
      calc
        ψ x * ‖inner ℝ (x - ξ) (H x)‖ ≤ ψ x * (ρ * A * ‖H x‖) :=
          mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right hr (norm_nonneg _))) (hψrange x).1
        _ = _ := by ring
    · have hz := scaledRadialCutoff_eq_zero_of_notMem_closedBall ξ hA hcutoff hρ hx
      change ψ x = 0 at hz
      simp only [hz, zero_mul, mul_zero, norm_zero, le_refl]
  have habs : |V.cutoffMeanCurvaturePairing ξ H φ ρ| ≤
      ρ * A * ∫ x in closedBall ξ R, ‖H x‖ * ψ x ∂V.weight := by
    have h := MeasureTheory.norm_integral_le_of_norm_le
      (hprodintall.const_mul (ρ * A)) (Eventually.of_forall hbound)
    rw [MeasureTheory.integral_const_mul] at h
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by rw [hψzero x hx, mul_zero])]
    simpa only [Real.norm_eq_abs, cutoffMeanCurvaturePairing, ψ] using h
  have hholder := integral_mul_cutoff_le (V.weight.restrict (closedBall ξ R)) hp
    hLp.norm (fun x ↦ norm_nonneg (H x)) hψcont.aestronglyMeasurable hψrange
  have hmass : (∫ x in closedBall ξ R, ψ x ∂V.weight) = V.cutoffMass ξ φ ρ := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hψzero]
    rfl
  rw [hmass] at hholder
  rw [cutoffMeanCurvatureError, abs_div, abs_of_pos (pow_pos hρ (n + 1))]
  calc
    _ ≤ (ρ * A * ∫ x in closedBall ξ R, ‖H x‖ * ψ x ∂V.weight) / ρ ^ (n + 1) :=
      div_le_div_of_nonneg_right habs (pow_pos hρ _).le
    _ ≤ (ρ * A * ((∫ x in closedBall ξ R, ‖H x‖ ^ p ∂V.weight) ^ (1 / p) *
        (V.cutoffMass ξ φ ρ) ^ (1 - 1 / p))) / ρ ^ (n + 1) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hholder (mul_pos hρ hA).le) (pow_pos hρ _).le
    _ = _ := by rw [pow_succ]; field_simp

theorem scaledLpMeanCurvature_eq (ξ : E) (H : E → E) {p R : ℝ}
    (hp : 0 < p) (hR : 0 < R) :
    V.scaledLpMeanCurvature ξ H p R = R ^ (1 - n / p) *
      (∫ x in closedBall ξ R, ‖H x‖ ^ p ∂V.weight) ^ (1 / p) := by
  rw [scaledLpMeanCurvature, Real.mul_rpow (Real.rpow_nonneg hR.le _)
    (MeasureTheory.integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul hR.le]
  congr 2
  field_simp

private theorem rpow_normalization {a ρ p : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ) :
    a ^ (1 - 1 / p) / ρ ^ n =
      ρ ^ (-(n : ℝ) / p) * (a / ρ ^ n) ^ (1 - 1 / p) := by
  rw [Real.div_rpow ha (pow_pos hρ n).le, ← Real.rpow_natCast ρ n,
    ← Real.rpow_mul hρ.le]
  calc
    _ = a ^ (1 - 1 / p) * ρ ^ (-(n : ℝ)) := by rw [Real.rpow_neg hρ.le]; rfl
    _ = a ^ (1 - 1 / p) *
        (ρ ^ (-(n : ℝ) / p) * ρ ^ (-((n : ℝ) * (1 - 1 / p)))) := by
      rw [← Real.rpow_add hρ]
      congr 2
      ring
    _ = _ := by rw [Real.rpow_neg hρ.le]; ring

private theorem rpow_le_one_add {a p : ℝ} (ha : 0 ≤ a) (hp : 1 < p) :
    a ^ (1 - 1 / p) ≤ 1 + a := by
  have he0 : 0 ≤ 1 - 1 / p := sub_nonneg.mpr ((div_le_one (by linarith)).mpr hp.le)
  have he1 : 1 - 1 / p ≤ 1 := by
    have : 0 ≤ 1 / p := by positivity
    linarith
  by_cases ha1 : a ≤ 1
  · exact (Real.rpow_le_one ha ha1 he0).trans (by linarith)
  · exact (Real.rpow_le_self_of_one_le (le_of_not_ge ha1) he1).trans (by linarith)

/-- The normalized Hölder estimate, with no lower-density assumption. -/
theorem HasGeneralizedMeanCurvatureIn.abs_cutoffMeanCurvatureError_le_lp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R : ℝ} (hp : 1 < p) (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφrange : ∀ t, φ t ∈ Icc 0 1)
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) (hρA : ρ * A ≤ R) :
    |V.cutoffMeanCurvatureError ξ H φ ρ| ≤
      A * ρ ^ (-(n : ℝ) / p) *
        (∫ x in closedBall ξ R, ‖H x‖ ^ p ∂V.weight) ^ (1 / p) *
        (1 + V.cutoffMass ξ φ ρ / ρ ^ n) := by
  have hmass : 0 ≤ V.cutoffMass ξ φ ρ :=
    MeasureTheory.integral_nonneg fun x ↦ (hφrange _).1
  have hnorm : 0 ≤ V.cutoffMass ξ φ ρ / ρ ^ n := div_nonneg hmass (pow_pos hρ n).le
  calc
    _ ≤ A / ρ ^ n * (∫ x in closedBall ξ R, ‖H x‖ ^ p ∂V.weight) ^ (1 / p) *
        (V.cutoffMass ξ φ ρ) ^ (1 - 1 / p) :=
      HasGeneralizedMeanCurvatureIn.abs_cutoffMeanCurvatureError_le_holder
        (V := V) hH ξ hp hball hLp hφ hφrange hA hρ hcutoff hρA
    _ = A * (∫ x in closedBall ξ R, ‖H x‖ ^ p ∂V.weight) ^ (1 / p) *
        ((V.cutoffMass ξ φ ρ) ^ (1 - 1 / p) / ρ ^ n) := by ring
    _ = A * ρ ^ (-(n : ℝ) / p) *
        (∫ x in closedBall ξ R, ‖H x‖ ^ p ∂V.weight) ^ (1 / p) *
        (V.cutoffMass ξ φ ρ / ρ ^ n) ^ (1 - 1 / p) := by
      rw [rpow_normalization hmass hρ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (rpow_le_one_add hnorm hp) (by positivity)

/-- The signed coefficient in the corrected (4.3). Its denominator is
strictly positive at positive radii because the cutoff is nonnegative. -/
def cutoffLpMeanCurvatureError (ξ : E) (H : E → E) (φ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  V.cutoffMeanCurvatureError ξ H φ ρ / (1 + V.cutoffMass ξ φ ρ / ρ ^ n)

theorem HasGeneralizedMeanCurvatureIn.hasDerivAt_normalizedCutoffMass_lp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφnonneg : ∀ t, 0 ≤ φ t)
    {A : ℝ} (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall ξ (ρ * A) ⊆ U) :
    HasDerivAt (fun t ↦ V.cutoffMass ξ φ t / t ^ n)
      ((∫ x, scaledRadialCutoffDeriv ξ φ ρ x * V.radialNormalSq ξ x ∂V.weight) / ρ ^ n +
        V.cutoffLpMeanCurvatureError ξ H φ ρ * (1 + V.cutoffMass ξ φ ρ / ρ ^ n)) ρ := by
  have hmass : 0 ≤ V.cutoffMass ξ φ ρ := MeasureTheory.integral_nonneg fun x ↦ hφnonneg _
  have hden : 0 < 1 + V.cutoffMass ξ φ ρ / ρ ^ n :=
    add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hmass (pow_pos hρ n).le)
  simpa only [cutoffLpMeanCurvatureError, div_mul_cancel₀ _ hden.ne'] using
    HasGeneralizedMeanCurvatureIn.hasDerivAt_normalizedCutoffMass
      (V := V) hH ξ hφ hA hcutoff hρ hball

private theorem lpScale_coefficient {R ρ p : ℝ} (hR : 0 < R) (hρ : 0 < ρ) :
    ρ ^ (-(n : ℝ) / p) / R ^ (1 - n / p) =
      R⁻¹ * (ρ / R) ^ (-(n : ℝ) / p) := by
  rw [Real.div_rpow hρ.le hR.le, Real.rpow_sub hR, Real.rpow_one,
    div_div_eq_mul_div]
  simp only [neg_div]
  rw [Real.rpow_neg hR.le]
  field_simp

/-- Corrected (4.3), with the absolute coefficient bound following (4.2).
The source uses `A=1+ε≤2`. -/
theorem HasGeneralizedMeanCurvatureIn.abs_cutoffLpMeanCurvatureError_le
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : 1 < p) (hR : 0 < R) (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφrange : ∀ t, φ t ∈ Icc 0 1)
    {A ρ : ℝ} (hA : 0 < A) (hA2 : A ≤ 2) (hρ : 0 < ρ)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) (hρA : ρ * A ≤ R) :
    |V.cutoffLpMeanCurvatureError ξ H φ ρ| ≤
      2 * lpMeanCurvatureKappa n p * Λ * R⁻¹ * (ρ / R) ^ (-(n : ℝ) / p) := by
  have hmass : 0 ≤ V.cutoffMass ξ φ ρ := MeasureTheory.integral_nonneg fun x ↦ (hφrange _).1
  have hden : 0 < 1 + V.cutoffMass ξ φ ρ / ρ ^ n :=
    add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hmass (pow_pos hρ n).le)
  have hbound := HasGeneralizedMeanCurvatureIn.abs_cutoffMeanCurvatureError_le_lp
    (V := V) hH ξ hp hball hLp hφ hφrange hA hρ hcutoff hρA
  have hscale' : (∫ x in closedBall ξ R, ‖H x‖ ^ p ∂V.weight) ^ (1 / p) ≤
      (lpMeanCurvatureKappa n p * Λ) / R ^ (1 - n / p) := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hR _)).mpr
    simpa only [V.scaledLpMeanCurvature_eq ξ H (by linarith : 0 < p) hR, mul_comm] using hscale
  have hLnonneg : 0 ≤ (∫ x in closedBall ξ R, ‖H x‖ ^ p ∂V.weight) ^ (1 / p) := by positivity
  rw [cutoffLpMeanCurvatureError, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  calc
    _ ≤ A * ρ ^ (-(n : ℝ) / p) *
        (∫ x in closedBall ξ R, ‖H x‖ ^ p ∂V.weight) ^ (1 / p) *
        (1 + V.cutoffMass ξ φ ρ / ρ ^ n) := hbound
    _ ≤ (2 * ρ ^ (-(n : ℝ) / p) *
        ((lpMeanCurvatureKappa n p * Λ) / R ^ (1 - n / p))) *
        (1 + V.cutoffMass ξ φ ρ / ρ ^ n) := by
      apply mul_le_mul_of_nonneg_right _ hden.le
      apply mul_le_mul
        (mul_le_mul_of_nonneg_right hA2 (Real.rpow_pos_of_pos hρ _).le) hscale' hLnonneg
      positivity
    _ = _ := by
      have hs := lpScale_coefficient (n := n) (p := p) hR hρ
      calc
        _ = (2 * lpMeanCurvatureKappa n p * Λ *
            (ρ ^ (-(n : ℝ) / p) / R ^ (1 - n / p))) *
            (1 + V.cutoffMass ξ φ ρ / ρ ^ n) := by ring
        _ = _ := by rw [hs]; ring

/-- An explicit majorizing factor for (4.8). This factor is independent of
the cutoff width, so its closed-ball limit needs no choice of subsequence. -/
def lpMonotonicityFactor (n : ℕ) (p R Λ ρ : ℝ) : ℝ :=
  Real.exp (Λ / 2 * (ρ / R) ^ (1 - n / p))

/-- The associated additive correction, as in (4.5). -/
def lpMonotonicityError (n : ℕ) (p R Λ ρ : ℝ) : ℝ :=
  lpMonotonicityFactor n p R Λ ρ - 1

theorem hasDerivAt_lpMonotonicityFactor {p R ρ : ℝ} (hp : 0 < p)
    (hR : 0 < R) (hρ : 0 < ρ) (Λ : ℝ) :
    HasDerivAt (lpMonotonicityFactor n p R Λ)
      (lpMonotonicityFactor n p R Λ ρ *
        (2 * lpMeanCurvatureKappa n p * Λ * R⁻¹ * (ρ / R) ^ (-(n : ℝ) / p))) ρ := by
  have hbase := ((hasDerivAt_id ρ).div_const R).rpow_const
    (p := 1 - (n : ℝ) / p) (Or.inl (div_pos hρ hR).ne')
  have hexp : (1 - (n : ℝ) / p) - 1 = -(n : ℝ) / p := by ring
  have h := (hbase.const_mul (Λ / 2)).exp
  simp only [hexp] at h
  convert h using 1
  · rfl
  · dsimp [lpMonotonicityFactor, lpMeanCurvatureKappa]
    congr 1
    field_simp
    ring

theorem tendsto_lpMonotonicityFactor {p R : ℝ} (hp : (n : ℝ) < p) (Λ : ℝ) :
    Tendsto (lpMonotonicityFactor n p R Λ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have he : 0 < 1 - n / p := sub_pos.mpr ((div_lt_one hp0).mpr hp)
  have hc : Continuous (lpMonotonicityFactor n p R Λ) := by
    apply Real.continuous_exp.comp
    exact continuous_const.mul ((continuous_id.div_const R).rpow_const (fun _ ↦ Or.inr he.le))
  have ht := (hc.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  simpa only [lpMonotonicityFactor, zero_div, Real.zero_rpow he.ne', mul_zero, Real.exp_zero] using ht

/-- The explicit factor satisfies the two exponential bounds of (4.5). -/
theorem lpMonotonicityFactor_bounds {p R Λ ρ : ℝ} (hp : (n : ℝ) < p)
    (hR : 0 < R) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    Real.exp (-Λ) ≤ Real.exp (-Λ / 2 * (ρ / R) ^ (1 - n / p)) ∧
    Real.exp (-Λ / 2 * (ρ / R) ^ (1 - n / p)) ≤ lpMonotonicityFactor n p R Λ ρ ∧
    lpMonotonicityFactor n p R Λ ρ ≤ Real.exp (Λ / 2 * (ρ / R) ^ (1 - n / p)) ∧
    Real.exp (Λ / 2 * (ρ / R) ^ (1 - n / p)) ≤ Real.exp Λ := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have he : 0 ≤ 1 - n / p := sub_nonneg.mpr ((div_le_one hp0).mpr hp.le)
  have ht : (ρ / R) ^ (1 - n / p) ∈ Icc 0 1 :=
    ⟨Real.rpow_nonneg (div_pos hρ hR).le _,
      Real.rpow_le_one (div_pos hρ hR).le ((div_le_one hR).mpr hρR) he⟩
  have hs : 0 ≤ Λ / 2 * (ρ / R) ^ (1 - n / p) := mul_nonneg (by positivity) ht.1
  have hsΛ : Λ / 2 * (ρ / R) ^ (1 - n / p) ≤ Λ := by
    nlinarith [mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ Λ / 2 by positivity)]
  refine ⟨Real.exp_le_exp.mpr (by nlinarith), Real.exp_le_exp.mpr (by
    nlinarith), le_rfl, Real.exp_le_exp.mpr hsΛ⟩

/-- The explicit additive correction satisfies the error estimate in (4.5). -/
theorem abs_lpMonotonicityError_le {p R Λ ρ : ℝ} (hp : (n : ℝ) < p)
    (hR : 0 < R) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    |lpMonotonicityError n p R Λ ρ| ≤
      (Real.exp (Λ / 2) / 2) * Λ * (ρ / R) ^ (1 - n / p) := by
  let s := Λ / 2 * (ρ / R) ^ (1 - n / p)
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have he : 0 ≤ 1 - n / p := sub_nonneg.mpr ((div_le_one hp0).mpr hp.le)
  have ht : (ρ / R) ^ (1 - n / p) ∈ Icc 0 1 :=
    ⟨Real.rpow_nonneg (div_pos hρ hR).le _,
      Real.rpow_le_one (div_pos hρ hR).le ((div_le_one hR).mpr hρR) he⟩
  have hs : 0 ≤ s := mul_nonneg (by positivity) ht.1
  have hsΛ : s ≤ Λ / 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ Λ / 2 by positivity)
  have htangent := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-s)) (Real.exp_pos s).le
  have hexp : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
  rw [hexp] at htangent
  have hle : Real.exp s - 1 ≤ Real.exp s * s := by nlinarith
  have hpos : 0 ≤ Real.exp s - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hs)
  change |Real.exp s - 1| ≤ _
  rw [abs_of_nonneg hpos]
  calc
    _ ≤ Real.exp s * s := hle
    _ ≤ Real.exp (Λ / 2) * s := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsΛ) hs
    _ = _ := by dsimp [s]; ring

/-- The simplified error estimate (4.6), for `Λ≤1`. -/
theorem abs_lpMonotonicityError_le_of_le_one {p R Λ ρ : ℝ} (hp : (n : ℝ) < p)
    (hR : 0 < R) (hΛ : 0 ≤ Λ) (hΛ1 : Λ ≤ 1) (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    |lpMonotonicityError n p R Λ ρ| ≤ Λ * (ρ / R) ^ (1 - n / p) := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have he : 0 ≤ 1 - n / p := sub_nonneg.mpr ((div_le_one hp0).mpr hp.le)
  have ht : (ρ / R) ^ (1 - n / p) ∈ Icc 0 1 :=
    ⟨Real.rpow_nonneg (div_pos hρ hR).le _,
      Real.rpow_le_one (div_pos hρ hR).le ((div_le_one hR).mpr hρR) he⟩
  have hs : 0 ≤ Λ / 2 * (ρ / R) ^ (1 - n / p) := mul_nonneg (by positivity) ht.1
  have hs1 : |Λ / 2 * (ρ / R) ^ (1 - n / p)| ≤ 1 := by
    rw [abs_of_nonneg hs]
    nlinarith [mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ Λ / 2 by positivity)]
  have h := Real.abs_exp_sub_one_le hs1
  rw [abs_of_nonneg hs] at h
  change |Real.exp (Λ / 2 * (ρ / R) ^ (1 - n / p)) - 1| ≤ _
  nlinarith

/-- Corrected monotonicity before removing the cutoff. The hypotheses are
precisely the `Lᵖ` curvature hypothesis and its dimensionless bound (4.2). -/
theorem HasGeneralizedMeanCurvatureIn.lp_normalizedCutoffMass_monotoneOn
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : 1 < p) (hR : 0 < R) (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφrange : ∀ t, φ t ∈ Icc 0 1)
    (hφanti : Antitone φ) {A σ ρ : ℝ} (hA : 0 < A) (hA2 : A ≤ 2)
    (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) (hσ : 0 < σ) (hρA : ρ * A ≤ R) :
    MonotoneOn (fun t ↦ lpMonotonicityFactor n p R Λ t *
      (V.cutoffMass ξ φ t / t ^ n) + lpMonotonicityError n p R Λ t) (Icc σ ρ) := by
  let M := fun t ↦ V.cutoffMass ξ φ t / t ^ n
  let N := fun t ↦ (∫ x, scaledRadialCutoffDeriv ξ φ t x *
    V.radialNormalSq ξ x ∂V.weight) / t ^ n
  let B := fun t ↦ 2 * lpMeanCurvatureKappa n p * Λ * R⁻¹ * (t / R) ^ (-(n : ℝ) / p)
  let D := fun t ↦ lpMonotonicityFactor n p R Λ t *
    (N t + (B t + V.cutoffLpMeanCurvatureError ξ H φ t) * (1 + M t))
  have hderiv : ∀ t ∈ Icc σ ρ, HasDerivAt
      (fun t ↦ lpMonotonicityFactor n p R Λ t * M t + lpMonotonicityError n p R Λ t)
      (D t) t := by
    intro t ht
    have ht0 := hσ.trans_le ht.1
    have htA := (mul_le_mul_of_nonneg_right ht.2 hA.le).trans hρA
    have hm := HasGeneralizedMeanCurvatureIn.hasDerivAt_normalizedCutoffMass_lp
      (V := V) hH ξ hφ (fun t ↦ (hφrange t).1) hA hcutoff ht0
      ((closedBall_subset_closedBall htA).trans hball)
    have hf := hasDerivAt_lpMonotonicityFactor (n := n) (by linarith : 0 < p) hR ht0 Λ
    convert (hf.mul hm).add (hf.sub_const 1) using 1
    · funext t
      rfl
    · dsimp [D, N, B, M]
      ring
  have hnonneg : ∀ t ∈ Icc σ ρ, 0 ≤ D t := by
    intro t ht
    have ht0 := hσ.trans_le ht.1
    have htA := (mul_le_mul_of_nonneg_right ht.2 hA.le).trans hρA
    have hb := (abs_le.mp (HasGeneralizedMeanCurvatureIn.abs_cutoffLpMeanCurvatureError_le
      (V := V) hH ξ hp hR hball hLp hscale hφ hφrange hA hA2 ht0 hcutoff htA)).1
    have hN : 0 ≤ N t := div_nonneg (MeasureTheory.integral_nonneg fun x ↦
      mul_nonneg (scaledRadialCutoffDeriv_nonneg ξ x hφanti ht0)
        (V.radialNormalSq_nonneg ξ x)) (pow_pos ht0 n).le
    have hM : 0 ≤ M t := div_nonneg
      (MeasureTheory.integral_nonneg fun x ↦ (hφrange _).1) (pow_pos ht0 n).le
    exact mul_nonneg (Real.exp_pos _).le
      (add_nonneg hN (mul_nonneg (by dsimp [B]; linarith) (by linarith)))
  apply monotoneOn_of_deriv_nonneg (convex_Icc σ ρ)
    (fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hderiv t (interior_subset ht)).deriv]
    exact hnonneg t (interior_subset ht)

/-- Simon (4.8): an explicit factor and additive error make the closed-ball
mass ratio monotone. Their bounds are proved below. This conclusion is
obtained directly from first variation, without postulating (4.7). -/
theorem HasGeneralizedMeanCurvatureIn.lp_normalizedBallMass_monotoneOn
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : 1 < p) (hR : 0 < R) (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ) :
    MonotoneOn (fun ρ ↦ lpMonotonicityFactor n p R Λ ρ *
      (V.weight.real (closedBall ξ ρ) / ρ ^ n) + lpMonotonicityError n p R Λ ρ) (Ioo 0 R) := by
  intro σ hσ ρ hρ hσρ
  have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hsum : Tendsto (fun ε : ℝ ↦ 1 + ε) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hid
  have hlim {t : ℝ} (ht : 0 < t) :
      Tendsto (fun ε ↦ lpMonotonicityFactor n p R Λ t *
        (V.cutoffMass ξ (monotonicityCutoff ε) t / t ^ n) + lpMonotonicityError n p R Λ t)
        (𝓝[>] (0 : ℝ)) (𝓝 (lpMonotonicityFactor n p R Λ t *
          (V.weight.real (closedBall ξ t) / t ^ n) + lpMonotonicityError n p R Λ t)) :=
    (((V.tendsto_cutoffMass ξ ht).div_const (t ^ n)).const_mul _).add_const _
  have hscaleR : Tendsto (fun ε : ℝ ↦ ρ * (1 + ε)) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    simpa only [mul_one] using hsum.const_mul ρ
  apply le_of_tendsto_of_tendsto (hlim hσ.1) (hlim hρ.1)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num),
    hscaleR.eventually (gt_mem_nhds hρ.2)] with ε hε hεR
  have hmono := HasGeneralizedMeanCurvatureIn.lp_normalizedCutoffMass_monotoneOn
    (V := V) hH ξ hp hR hball hLp hscale (contDiff_monotonicityCutoff ε)
    (monotonicityCutoff_mem_Icc ε) (monotonicityCutoff_antitone hε.1)
    (show 0 < 1 + ε by linarith [hε.1]) (show 1 + ε ≤ 2 by linarith [hε.2])
    (monotonicityCutoff_cutoff hε.1) hσ.1 hεR.le
  exact hmono ⟨le_rfl, hσρ⟩ ⟨hσρ, le_rfl⟩ hσρ

/-- The endpoint `ρ=R` in (4.8) is retained. No null-sphere assumption is
needed: comparison with the full outer closed ball gives the endpoint. -/
theorem HasGeneralizedMeanCurvatureIn.lp_normalizedBallMass_monotoneOn_Ioc
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : 1 < p) (hR : 0 < R) (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ) :
    MonotoneOn (fun ρ ↦ lpMonotonicityFactor n p R Λ ρ *
      (V.weight.real (closedBall ξ ρ) / ρ ^ n) + lpMonotonicityError n p R Λ ρ) (Ioc 0 R) := by
  intro σ hσ ρ hρ hσρ
  by_cases hρR : ρ < R
  · exact HasGeneralizedMeanCurvatureIn.lp_normalizedBallMass_monotoneOn
      (V := V) hH ξ hp hR hball hLp hscale ⟨hσ.1, hσρ.trans_lt hρR⟩ ⟨hρ.1, hρR⟩ hσρ
  have hρeq : ρ = R := le_antisymm hρ.2 (le_of_not_gt hρR)
  subst ρ
  rcases lt_or_eq_of_le hσρ with hσR | rfl
  · have hf := (hasDerivAt_lpMonotonicityFactor (n := n)
      (by linarith : 0 < p) hR hR Λ).continuousAt
    have hlim : Tendsto (fun t ↦ lpMonotonicityFactor n p R Λ t *
        (V.weight.real (closedBall ξ R) / t ^ n) + lpMonotonicityError n p R Λ t)
        (𝓝[<] R) (𝓝 (lpMonotonicityFactor n p R Λ R *
          (V.weight.real (closedBall ξ R) / R ^ n) + lpMonotonicityError n p R Λ R)) := by
      exact ((hf.mul (continuousAt_const.div (continuousAt_id.pow n) (pow_ne_zero n hR.ne'))).add
        (hf.sub continuousAt_const)).tendsto.mono_left inf_le_left
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsLT hσR] with t ht
    have ht0 := hσ.1.trans ht.1
    calc
      _ ≤ lpMonotonicityFactor n p R Λ t *
          (V.weight.real (closedBall ξ t) / t ^ n) + lpMonotonicityError n p R Λ t :=
        HasGeneralizedMeanCurvatureIn.lp_normalizedBallMass_monotoneOn
          (V := V) hH ξ hp hR hball hLp hscale ⟨hσ.1, hσR⟩ ⟨ht0, ht.2⟩ ht.1.le
      _ ≤ _ := by
        apply add_le_add _ le_rfl
        apply mul_le_mul_of_nonneg_left _ (show 0 ≤ lpMonotonicityFactor n p R Λ t from
          (Real.exp_pos _).le)
        apply div_le_div_of_nonneg_right _ (pow_pos ht0 n).le
        exact MeasureTheory.measureReal_mono (closedBall_subset_closedBall ht.2.le)
          (isCompact_closedBall ξ R).measure_lt_top.ne
  · exact le_rfl

/-- The density-existence conclusion preceding (4.9): a finite real limit
follows from the `Lᵖ` hypothesis with `p>n`. -/
theorem HasGeneralizedMeanCurvatureIn.exists_tendsto_normalizedBallMass_real_lp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (ξ : E)
    {p R Λ : ℝ} (hp : 1 < p) (hpn : (n : ℝ) < p) (hR : 0 < R)
    (hball : closedBall ξ R ⊆ U)
    (hLp : MeasureTheory.MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ) :
    ∃ d : ℝ, 0 ≤ d ∧ Tendsto (fun ρ ↦ V.weight.real (closedBall ξ ρ) / ρ ^ n)
      (𝓝[>] (0 : ℝ)) (𝓝 d) := by
  let F := fun ρ ↦ lpMonotonicityFactor n p R Λ ρ *
    (V.weight.real (closedBall ξ ρ) / ρ ^ n) + lpMonotonicityError n p R Λ ρ
  have hnonneg : ∀ ρ ∈ Ioo 0 R, -1 ≤ F ρ := by
    intro ρ hρ
    have hmass : 0 ≤ Real.exp (Λ / 2 * (ρ / R) ^ (1 - n / p)) *
        (V.weight.real (closedBall ξ ρ) / ρ ^ n) :=
      mul_nonneg (Real.exp_pos (Λ / 2 * (ρ / R) ^ (1 - n / p))).le
      (div_nonneg ENNReal.toReal_nonneg (pow_pos hρ.1 n).le)
    have hf := (Real.exp_pos (Λ / 2 * (ρ / R) ^ (1 - n / p))).le
    dsimp [F, lpMonotonicityError, lpMonotonicityFactor]
    linarith
  have hne : (Ioo (0 : ℝ) R).Nonempty := ⟨R / 2, half_pos hR, half_lt_self hR⟩
  have hFlim := MonotoneOn.tendsto_nhdsWithin_Ioo_right hne
    (HasGeneralizedMeanCurvatureIn.lp_normalizedBallMass_monotoneOn
      (V := V) hH ξ hp hR hball hLp hscale)
    (show BddBelow (F '' Ioo 0 R) from ⟨-1, by rintro _ ⟨ρ, hρ, rfl⟩; exact hnonneg ρ hρ⟩)
  have he := tendsto_lpMonotonicityFactor (n := n) (R := R) hpn Λ
  have hE : Tendsto (lpMonotonicityError n p R Λ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    change Tendsto (fun ρ ↦ lpMonotonicityFactor n p R Λ ρ - 1) _ _
    simpa only [sub_self] using he.sub_const 1
  have hlim := (hFlim.sub hE).div he (by norm_num)
  have heq : (fun ρ ↦ (F ρ - lpMonotonicityError n p R Λ ρ) /
      lpMonotonicityFactor n p R Λ ρ) =
      (fun ρ ↦ V.weight.real (closedBall ξ ρ) / ρ ^ n) := by
    funext ρ
    dsimp [F]
    rw [add_sub_cancel_right]
    exact mul_div_cancel_left₀ _ (Real.exp_ne_zero _)
  change Tendsto (fun ρ ↦ (F ρ - lpMonotonicityError n p R Λ ρ) /
    lpMonotonicityFactor n p R Λ ρ) _ _ at hlim
  rw [heq, sub_zero, div_one] at hlim
  refine ⟨sInf (F '' Ioo 0 R), ?_, hlim⟩
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  exact div_nonneg ENNReal.toReal_nonneg (pow_pos hρ n).le

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
