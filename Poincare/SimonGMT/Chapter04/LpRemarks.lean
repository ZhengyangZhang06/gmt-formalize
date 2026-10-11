module

public import Poincare.SimonGMT.Chapter04.LpAnnular

@[expose] public section

/-!
# Simon GMT, Chapter 4, Remark 4.10

The polynomial ball-growth consequence is proved from the simultaneous
annular correction. The printed annular estimate does not follow from
ball growth alone; an explicit measure-theoretic counterexample is recorded.
No density--multiplicity identification is assumed here.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

/-- The unit mass at radius one satisfies the printed polynomial growth
hypothesis with `n=2`, `β=1`, at every positive radius. -/
theorem dirac_one_ball_growth {r : ℝ} (hr : 0 < r) :
    (Measure.dirac (1 : ℝ)).real (closedBall 0 r) ≤ r ^ 2 := by
  by_cases hmem : (1 : ℝ) ∈ closedBall 0 r
  · have h1 : 1 ≤ r := by simpa only [mem_closedBall, Real.dist_eq, sub_zero, abs_one] using hmem
    simp only [measureReal_def, Measure.dirac_apply_of_mem hmem, ENNReal.toReal_one]
    nlinarith
  · simp only [measureReal_def, Measure.dirac_apply, indicator_of_notMem hmem,
      ENNReal.toReal_zero]
    positivity

/-- A concrete failure of the power estimate claimed to follow from
ball growth in (4.10)(2): `n=2`, `α=1`, `σ=7/8`, `ρ=9/8`, `β=1`.
This refutes that measure-theoretic implication; it is not presented as
a construction of a two-dimensional rectifiable varifold. -/
theorem dirac_one_annular_power_counterexample :
    (∫ x in closedBall (0 : ℝ) (9 / 8 : ℝ) \ closedBall 0 (7 / 8 : ℝ),
      |x| ^ (-(1 : ℝ)) ∂Measure.dirac 1) >
        (2 : ℝ) / (2 - 1) * ((9 / 8 : ℝ) ^ ((2 : ℝ) - 1) -
          (7 / 8 : ℝ) ^ ((2 : ℝ) - 1)) := by
  classical
  have hmem : (1 : ℝ) ∈ closedBall (0 : ℝ) (9 / 8 : ℝ) \ closedBall 0 (7 / 8 : ℝ) := by
    norm_num [mem_closedBall, Real.dist_eq]
  rw [setIntegral_dirac, ite_eq_left hmem]
  norm_num

/-- The same growth hypothesis also fails to imply the printed critical
logarithmic estimate (`α=n=2`). -/
theorem dirac_one_annular_log_counterexample :
    (∫ x in closedBall (0 : ℝ) (9 / 8 : ℝ) \ closedBall 0 (7 / 8 : ℝ),
      |x| ^ (-(2 : ℝ)) ∂Measure.dirac 1) > Real.log ((9 / 8 : ℝ) / (7 / 8 : ℝ)) := by
  classical
  have hmem : (1 : ℝ) ∈ closedBall (0 : ℝ) (9 / 8 : ℝ) \ closedBall 0 (7 / 8 : ℝ) := by
    norm_num [mem_closedBall, Real.dist_eq]
  rw [setIntegral_dirac, ite_eq_left hmem]
  norm_num only [abs_one, Real.one_rpow]
  have h := Real.log_le_sub_one_of_pos (show 0 < (9 / 8 : ℝ) / (7 / 8 : ℝ) by norm_num)
  norm_num at h ⊢
  linarith

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

/-- The valid first sentence of Remark (4.10)(2): the same factor as in
(4.7) gives one polynomial mass bound at every radius up to `R`. -/
theorem LpAnnularCorrection.exists_ballGrowthBound
    {ξ : E} {p R Λ : ℝ} {F : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (h : V.LpAnnularCorrection ξ p R Λ F G) (hR : 0 < R) :
    ∃ β : ℝ, 0 < β ∧ ∀ r ∈ Ioc 0 R, V.weight.real (closedBall ξ r) ≤ β * r ^ n := by
  let M := fun r ↦ V.weight.real (closedBall ξ r) / r ^ n
  have hM : ∀ r, 0 ≤ r → 0 ≤ M r := fun r hr ↦ div_nonneg ENNReal.toReal_nonneg (pow_nonneg hr n)
  have hF : ∀ r ∈ Ioc 0 R, Real.exp (-Λ) ≤ F r :=
    fun r hr ↦ (h.factor_bounds r hr).1.trans (h.factor_bounds r hr).2.1
  have hFR : 0 < F R := (Real.exp_pos _).trans_le (hF R ⟨hR, le_rfl⟩)
  let β := F R * (M R + 1) / Real.exp (-Λ)
  have hβ : 0 < β := div_pos (mul_pos hFR (by linarith [hM R hR.le])) (Real.exp_pos _)
  refine ⟨β, hβ, ?_⟩
  intro r hr
  have hm := h.monotone hr ⟨hR, le_rfl⟩ hr.2
  have hFr := hF r hr
  have hFr0 : 0 ≤ F r := (Real.exp_pos _).le.trans hFr
  have hl := mul_le_mul_of_nonneg_right hFr (hM r hr.1.le)
  have hbound : Real.exp (-Λ) * M r ≤ F R * (M R + 1) := by
    dsimp [M] at hl ⊢
    nlinarith
  have hMβ : M r ≤ β := (le_div_iff₀ (Real.exp_pos _)).mpr (by nlinarith [hbound])
  exact (div_le_iff₀ (pow_pos hr.1 n)).mp hMβ

theorem HasGeneralizedMeanCurvatureIn.exists_ballGrowthBound_lp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    (hU : IsOpen U) (ξ : E) {p R Λ : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R)
    (hball : closedBall ξ R ⊆ U)
    (hLp : ∀ K : Set E, IsCompact K → K ⊆ U → MemLp H (ENNReal.ofReal p) (V.weight.restrict K))
    (hscale : V.scaledLpMeanCurvature ξ H p R ≤ lpMeanCurvatureKappa n p * Λ) :
    ∃ β : ℝ, 0 < β ∧ ∀ r ∈ Ioc 0 R, V.weight.real (closedBall ξ r) ≤ β * r ^ n := by
  obtain ⟨F, G, h⟩ := HasGeneralizedMeanCurvatureIn.exists_lpAnnularCorrection_of_locallyLp
    (V := V) hH hU ξ hp hR hball hLp hscale
  exact LpAnnularCorrection.exists_ballGrowthBound (V := V) h hR

/-- The relatively closed density-superlevel conclusion available before
the unresolved density--multiplicity identification in (4.10)(1). -/
theorem HasGeneralizedMeanCurvatureIn.isClosed_densityReal_superlevel_lp
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    {p : ℝ} (hp : (n : ℝ) < p) (hU : IsOpen U)
    (hLp : ∀ K : Set E, IsCompact K → K ⊆ U → MemLp H (ENNReal.ofReal p) (V.weight.restrict K))
    (a : ℝ) : IsClosed {ξ : U | a ≤ V.stationaryDensityReal ξ} := by
  exact (upperSemicontinuousOn_iff_restrict.mpr
    (HasGeneralizedMeanCurvatureIn.upperSemicontinuousOn_stationaryDensityReal_lp
      (V := V) hH hp hU hLp)).isClosed_preimage a

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
