module

public import Poincare.SimonGMT.Chapter08.FirstVariationRiesz
public import Mathlib.Topology.Order.LeftRightNhds

@[expose] public section

/-!
# Ball-wise first-variation bounds

The literal hypothesis (8.3.1) uses the constructed first-variation Radon
measure and the actual varifold weight, on Simon's closed balls. The
finite symmetric differentiation theorem supplies this hypothesis at
weight-almost every point for a positive interval of radii, as used in
Lemma (8.3.6). This is the measure-theoretic input; existence of the
dimension-normalized density still needs monotonicity.

Source: `Simon-gmt new.pdf`, printed pp. 210--211, PDF object 217.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08.Varifold
noncomputable section
variable {N n : ℕ} {U : Set (Euclidean N)}

/-- Simon (8.3.1), for the measure actually constructed from first
variation. The constants and radius positivity are kept separate. -/
def HasBallFirstVariationBound (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) (x : Euclidean N) (R Λ : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → r < R →
    V.firstVariationRieszMeasure hV (closedBall x r) ≤
      ENNReal.ofReal Λ * V.weight (closedBall x r)

/-- The finite ratio limit gives a uniform ball-wise bound on a positive
interval of radii, without imposing positivity of the denominator. -/
theorem exists_ballFirstVariationBound_of_finite_ratio_limit (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) (x : Euclidean N) {D : ℝ≥0∞}
    (hD : D ≠ ∞)
    (ht : Tendsto (fun r : ℝ ↦ V.firstVariationRieszMeasure hV (closedBall x r) /
      V.weight (closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 D)) :
    ∃ R Λ : ℝ, 0 < R ∧ 0 ≤ Λ ∧ V.HasBallFirstVariationBound hV x R Λ := by
  let Λ : ℝ := D.toReal + 1
  have hΛ : 0 < Λ := by dsimp [Λ]; positivity
  have hlt : D < ENNReal.ofReal Λ := by
    rw [← ENNReal.ofReal_toReal hD]
    exact (ENNReal.ofReal_lt_ofReal_iff hΛ).mpr (by dsimp [Λ]; linarith)
  have hev := ht.eventually (gt_mem_nhds hlt)
  obtain ⟨R, hR, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨R, Λ, hR, hΛ.le, fun r hr hrR ↦ ?_⟩
  exact (ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top)
    (Or.inr (ENNReal.ofReal_pos.mpr hΛ).ne')).mp (hsmall ⟨hr, hrR⟩).le

/-- The differentiation-theorem assertion in the parenthesis of (8.3.6):
a finite ball-wise variation-to-weight bound exists near almost every point. -/
theorem ae_exists_ballFirstVariationBound (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) :
    ∀ᵐ x ∂V.weight, ∃ R Λ : ℝ, 0 < R ∧ 0 ≤ Λ ∧
      V.HasBallFirstVariationBound hV x R Λ := by
  filter_upwards [(V.firstVariationRiesz_symmetricDensity_spec hV).2] with x hx
  exact V.exists_ballFirstVariationBound_of_finite_ratio_limit hV x hx.2 hx.1

/-- The radii may be chosen with their closed ambient ball entirely
inside the source domain. No local finiteness at its boundary is imposed. -/
theorem ae_exists_ballFirstVariationBound_inside (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) :
    ∀ᵐ x ∂V.weight, ∃ R Λ : ℝ, 0 < R ∧ 0 ≤ Λ ∧ closedBall x R ⊆ U ∧
      V.HasBallFirstVariationBound hV x R Λ := by
  have hU : ∀ᵐ x ∂V.weight, x ∈ U := by
    rw [ae_iff]
    change V.weight Uᶜ = 0
    rw [V.weight_apply V.isOpen_domain.measurableSet.compl]
    exact V.supported
  filter_upwards [V.ae_exists_ballFirstVariationBound hV, hU] with x hx hxU
  obtain ⟨R, Λ, hR, hΛ, hbound⟩ := hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp V.isOpen_domain x hxU
  refine ⟨min R (r / 2), Λ, lt_min hR (half_pos hr), hΛ, ?_, ?_⟩
  · exact (closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hr))).trans hball
  · intro t ht htR
    exact hbound t ht (htR.trans_le (min_le_left _ _))

/-- At a point in the weight support, a bound near zero extends to every
prescribed compact ball inside the domain, by local finiteness and
positivity of the smaller ball's weight. -/
theorem exists_ballFirstVariationBound_on_closedBall (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) {x : Euclidean N} (hx : x ∈ V.weight.support)
    (hsmall : ∃ r Λ : ℝ, 0 < r ∧ 0 ≤ Λ ∧ V.HasBallFirstVariationBound hV x r Λ)
    {R : ℝ} (hR : 0 < R) (hball : closedBall x R ⊆ U) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ V.HasBallFirstVariationBound hV x R Λ := by
  obtain ⟨r₀, C, hr₀, hC, hsmall⟩ := hsmall
  let ε := min (r₀ / 2) (R / 2)
  have hε : 0 < ε := lt_min (half_pos hr₀) (half_pos hR)
  have hεR : ε < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have hεr₀ : ε < r₀ := (min_le_left _ _).trans_lt (half_lt_self hr₀)
  have hwpos : 0 < V.weight (closedBall x ε) :=
    (Measure.mem_support_iff_forall x).mp hx _ (closedBall_mem_nhds x hε)
  have hwfin : V.weight (closedBall x ε) ≠ ∞ :=
    V.weight_finite_on_compact _ (isCompact_closedBall x ε)
      ((closedBall_subset_closedBall hεR.le).trans hball)
  have hvfin : V.firstVariationRieszMeasure hV (closedBall x R) ≠ ∞ :=
    (V.isFirstVariationMeasure_riesz hV).finite_on_compact (isCompact_closedBall x R) hball
  let D := V.firstVariationRieszMeasure hV (closedBall x R) / V.weight (closedBall x ε)
  have hD : D ≠ ∞ := ENNReal.div_ne_top hvfin hwpos.ne'
  refine ⟨max C D.toReal, le_max_of_le_left hC, fun r hr hrR ↦ ?_⟩
  by_cases hrr₀ : r < r₀
  · exact (hsmall r hr hrr₀).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)
  have hεr : ε ≤ r := hεr₀.le.trans (le_of_not_gt hrr₀)
  calc
    V.firstVariationRieszMeasure hV (closedBall x r) ≤
        V.firstVariationRieszMeasure hV (closedBall x R) :=
      measure_mono (closedBall_subset_closedBall hrR.le)
    _ = D * V.weight (closedBall x ε) := (ENNReal.div_mul_cancel hwpos.ne' hwfin).symm
    _ ≤ ENNReal.ofReal (max C D.toReal) * V.weight (closedBall x r) := by
      apply mul_le_mul'
      · calc
          D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
          _ ≤ ENNReal.ofReal (max C D.toReal) := ENNReal.ofReal_le_ofReal (le_max_right _ _)
      · exact measure_mono (closedBall_subset_closedBall hεr)

/-- The full-radius version of the differentiation input to (8.3.6).
The radius is arbitrary provided its closed ball remains inside `U`. -/
theorem ae_forall_exists_ballFirstVariationBound (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) :
    ∀ᵐ x ∂V.weight, ∀ R : ℝ, 0 < R → closedBall x R ⊆ U →
      ∃ Λ : ℝ, 0 ≤ Λ ∧ V.HasBallFirstVariationBound hV x R Λ := by
  filter_upwards [V.ae_exists_ballFirstVariationBound hV, V.weight.support_mem_ae] with x hx hxs
  exact fun _ hR hball ↦ V.exists_ballFirstVariationBound_on_closedBall hV hxs hx hR hball

end
end Poincare.SimonGMT.Chapter08.Varifold
