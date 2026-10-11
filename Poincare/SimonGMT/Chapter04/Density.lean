module

public import Poincare.SimonGMT.Chapter04.FirstVariation
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.Monotone
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.LiminfLimsup

@[expose] public section

/-!
# Simon GMT, Chapter 4, §3: stationary densities

The density is a radius-independent function of the actual weight measure,
normalized by Simon's `ωₙ`. The stationary monotonicity formula supplies its
finite limit, the full-ball normal-radial defect identity, and upper
semicontinuity. Every ball in this file is closed, as in Simon's notation.

The identification of the positive-density carrier and density multiplicity
with the original rectifiable varifold requires the almost-everywhere density
theorem from §1; it is not built into any definition below.
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

/-- The lower density before division by `ωₙ`, defined independently of an
enclosing radius or a stationarity proof. -/
def lowerDensityMassRatio (ξ : E) : ℝ≥0∞ :=
  liminf (V.normalizedBallMass ξ) (𝓝[>] (0 : ℝ))

/-- Simon's normalized lower density of the varifold weight. For a stationary
varifold in an open domain, it is the finite density in (4.3.9). -/
def stationaryDensity (ξ : E) : ℝ≥0∞ :=
  V.lowerDensityMassRatio ξ / Chapter01.realUnitBallVolume (n : ℝ)

/-- The source's real-valued density, used only after finiteness is proved. -/
def stationaryDensityReal (ξ : E) : ℝ :=
  (V.stationaryDensity ξ).toReal

/-- The normalized density quotient uses the closed ball and Simon's `ωₙ`. -/
def densityQuotient (ξ : E) (ρ : ℝ) : ℝ≥0∞ :=
  V.normalizedBallMass ξ ρ / Chapter01.realUnitBallVolume (n : ℝ)

theorem lowerDensityMassRatio_eq_stationaryDensityRatio {ξ : E} {R : ℝ}
    (hR : 0 < R) (h : V.SatisfiesStationaryMonotonicity ξ R) :
    V.lowerDensityMassRatio ξ = V.stationaryDensityRatio ξ R :=
  (V.tendsto_normalizedBallMass_atRight hR h).liminf_eq

theorem densityQuotient_eq (ξ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    V.densityQuotient ξ ρ = V.weight (closedBall ξ ρ) /
      (Chapter01.realUnitBallVolume (n : ℝ) * ENNReal.ofReal (ρ ^ n)) := by
  simp only [densityQuotient, normalizedBallMass, div_eq_mul_inv]
  rw [ENNReal.mul_inv
    (Or.inl (ne_of_gt (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n))))
    (Or.inr (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hρ n))))]
  ac_rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A positive closed ball can be chosen inside any open neighborhood. -/
theorem exists_pos_closedBall_subset {U : Set E} (hU : IsOpen U)
    {ξ : E} (hξ : ξ ∈ U) : ∃ R : ℝ, 0 < R ∧ closedBall ξ R ⊆ U := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU ξ hξ
  exact ⟨r / 2, half_pos hr, (closedBall_subset_ball (half_lt_self hr)).trans hsub⟩

theorem IsStationaryIn.tendsto_normalizedBallMass
    {U : Set E} (hV : V.IsStationaryIn U) {ξ : E} {R : ℝ}
    (hR : 0 < R) (hball : closedBall ξ R ⊆ U) :
    Tendsto (V.normalizedBallMass ξ) (𝓝[>] (0 : ℝ))
      (𝓝 (V.lowerDensityMassRatio ξ)) := by
  have h := IsStationaryIn.satisfiesStationaryMonotonicity (V := V) hV ξ hball
  rw [V.lowerDensityMassRatio_eq_stationaryDensityRatio hR h]
  exact V.tendsto_normalizedBallMass_atRight hR h

theorem IsStationaryIn.lowerDensityMassRatio_ne_top
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U)
    {ξ : E} (hξ : ξ ∈ U) : V.lowerDensityMassRatio ξ ≠ ⊤ := by
  obtain ⟨R, hR, hball⟩ := exists_pos_closedBall_subset hU hξ
  rw [V.lowerDensityMassRatio_eq_stationaryDensityRatio hR
    (IsStationaryIn.satisfiesStationaryMonotonicity (V := V) hV ξ hball)]
  exact V.stationaryDensityRatio_ne_top hR

theorem IsStationaryIn.lowerDensityMassRatio_le
    {U : Set E} (hV : V.IsStationaryIn U) {ξ : E} {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hball : closedBall ξ R ⊆ U) :
    V.lowerDensityMassRatio ξ ≤ V.normalizedBallMass ξ ρ := by
  rw [V.lowerDensityMassRatio_eq_stationaryDensityRatio (hρ.trans hρR)
    (IsStationaryIn.satisfiesStationaryMonotonicity (V := V) hV ξ hball)]
  exact V.stationaryDensityRatio_le ⟨hρ, hρR⟩

/-- Simon (4.3.9): the normalized density limit exists at every point of the
open stationary domain. No sphere-null hypothesis is imposed. -/
theorem IsStationaryIn.tendsto_densityQuotient
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U)
    {ξ : E} (hξ : ξ ∈ U) :
    Tendsto (V.densityQuotient ξ) (𝓝[>] (0 : ℝ))
      (𝓝 (V.stationaryDensity ξ)) := by
  obtain ⟨R, hR, hball⟩ := exists_pos_closedBall_subset hU hξ
  exact (ENNReal.continuous_div_const _
    (ne_of_gt (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)))).continuousAt.tendsto.comp
      (IsStationaryIn.tendsto_normalizedBallMass (V := V) hV hR hball)

/-- Finiteness is part of Simon (4.3.9), not an extra hypothesis on density. -/
theorem IsStationaryIn.stationaryDensity_ne_top
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U)
    {ξ : E} (hξ : ξ ∈ U) : V.stationaryDensity ξ ≠ ⊤ := by
  exact ENNReal.div_ne_top
    (IsStationaryIn.lowerDensityMassRatio_ne_top (V := V) hV hU hξ)
    (ne_of_gt (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)))

theorem IsStationaryIn.tendsto_densityQuotient_real
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U)
    {ξ : E} (hξ : ξ ∈ U) :
    Tendsto (fun ρ ↦ V.weight.real (closedBall ξ ρ) /
      ((Chapter01.realUnitBallVolume (n : ℝ)).toReal * ρ ^ n))
      (𝓝[>] (0 : ℝ)) (𝓝 (V.stationaryDensityReal ξ)) := by
  have h := (ENNReal.tendsto_toReal
    (IsStationaryIn.stationaryDensity_ne_top (V := V) hV hU hξ)).comp
      (IsStationaryIn.tendsto_densityQuotient (V := V) hV hU hξ)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  simp only [Function.comp_apply, V.densityQuotient_eq ξ hρ, ENNReal.toReal_div,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hρ) n),
    MeasureTheory.measureReal_def]

/-! ### Passing the inner radius to zero -/

/-- The nonnegative normal-radial defect as a measure. Its density is assigned
zero at the centre, consistently with `radialNormalSq`. -/
def radialDefectMeasure (ξ : E) : MeasureTheory.Measure E :=
  V.weight.withDensity (fun x ↦ ENNReal.ofReal (V.radialNormalSq ξ x / ‖x - ξ‖ ^ n))

theorem radialDefectMeasure_apply (ξ : E) {s : Set E} (hs : MeasurableSet s) :
    V.radialDefectMeasure ξ s =
      ∫⁻ x in s, ENNReal.ofReal (V.radialNormalSq ξ x / ‖x - ξ‖ ^ n) ∂V.weight :=
  MeasureTheory.withDensity_apply _ hs

theorem radialDefectMeasure_real (ξ : E) (ρ : ℝ) :
    (V.radialDefectMeasure ξ).real (closedBall ξ ρ) =
      ∫ x in closedBall ξ ρ, V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight := by
  rw [MeasureTheory.measureReal_def, V.radialDefectMeasure_apply ξ measurableSet_closedBall]
  exact (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x ↦
      div_nonneg (V.radialNormalSq_nonneg ξ x) (pow_nonneg (norm_nonneg _) n))
    (((V.radialNormalSq_aemeasurable ξ).div (by fun_prop)).aestronglyMeasurable.restrict)).symm

@[simp] theorem radialDefectMeasure_singleton_center (ξ : E) :
    V.radialDefectMeasure ξ {ξ} = 0 := by
  rw [V.radialDefectMeasure_apply ξ (measurableSet_singleton ξ),
    MeasureTheory.lintegral_singleton]
  simp [radialNormalSq]

/-- The monotone exhaustion of a punctured closed ball by closed-ball annuli
also exhausts its defect measure: the centre has zero defect mass, even when
the weight measure has an atom there. -/
theorem tendsto_radialDefectMeasure_annulus (ξ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun k : ℕ ↦ V.radialDefectMeasure ξ
      (closedBall ξ ρ \ closedBall ξ (ρ / ((k : ℝ) + 1)))) atTop
      (𝓝 (V.radialDefectMeasure ξ (closedBall ξ ρ))) := by
  let σ : ℕ → ℝ := fun k ↦ ρ / ((k : ℝ) + 1)
  have hσpos : ∀ k, 0 < σ k := fun k ↦ div_pos hρ (by positivity)
  have hσanti : Antitone σ := by
    intro i j hij
    exact div_le_div_of_nonneg_left hρ.le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hσlim : Tendsto σ atTop (𝓝 0) := by
    simpa [σ, div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ρ
  let A : ℕ → Set E := fun k ↦ closedBall ξ ρ \ closedBall ξ (σ k)
  have hA : Monotone A := by
    intro i j hij x hx
    exact ⟨hx.1, fun hxj ↦ hx.2 ((closedBall_subset_closedBall (hσanti hij)) hxj)⟩
  have hunion : (⋃ k, A k) = closedBall ξ ρ \ {ξ} := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      refine ⟨hk.1, ?_⟩
      intro hxξ
      have heq : x = ξ := mem_singleton_iff.mp hxξ
      exact hk.2 (by simpa [heq] using (hσpos k).le)
    · intro hx
      have hxne : x ≠ ξ := fun heq ↦ hx.2 (mem_singleton_iff.mpr heq)
      obtain ⟨k, hk⟩ := (hσlim.eventually (gt_mem_nhds (dist_pos.mpr hxne))).exists
      apply mem_iUnion.mpr
      exact ⟨k, hx.1, by simpa only [mem_closedBall, not_le] using hk⟩
  have hlim := MeasureTheory.tendsto_measure_iUnion_atTop
    (μ := V.radialDefectMeasure ξ) hA
  rw [hunion, MeasureTheory.measure_sdiff_null (V.radialDefectMeasure_singleton_center ξ)] at hlim
  exact hlim

/-- Simon (4.3.10), before division by `ωₙ`: the inner radius tends to zero
in the exact stationary monotonicity formula. The defect integral includes
the centre and the boundary of the outer ball. -/
theorem IsStationaryIn.density_add_radialDefectMeasure
    {U : Set E} (hV : V.IsStationaryIn U) {ξ : E} {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hball : closedBall ξ R ⊆ U) :
    V.lowerDensityMassRatio ξ + V.radialDefectMeasure ξ (closedBall ξ ρ) =
      V.normalizedBallMass ξ ρ := by
  let σ : ℕ → ℝ := fun k ↦ ρ / ((k : ℝ) + 1)
  have hσpos : ∀ k, 0 < σ k := fun k ↦ div_pos hρ (by positivity)
  have hσle : ∀ k, σ k ≤ ρ := by
    intro k
    apply (div_le_iff₀ (show 0 < (k : ℝ) + 1 by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hσlim : Tendsto σ atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall hσpos⟩
    simpa [σ, div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ρ
  have hdensity := (IsStationaryIn.tendsto_normalizedBallMass (V := V)
    hV (hρ.trans hρR) hball).comp hσlim
  have hdefect := V.tendsto_radialDefectMeasure_annulus ξ hρ
  have heq : ∀ k : ℕ, V.normalizedBallMass ξ (σ k) + V.radialDefectMeasure ξ
      (closedBall ξ ρ \ closedBall ξ (σ k)) = V.normalizedBallMass ξ ρ := by
    intro k
    rw [V.radialDefectMeasure_apply ξ (measurableSet_closedBall.diff measurableSet_closedBall)]
    exact IsStationaryIn.satisfiesStationaryMonotonicity (V := V) hV ξ hball
      (hσpos k) (hσle k) hρR
  exact tendsto_nhds_unique ((hdensity.add hdefect).congr' (Eventually.of_forall heq))
    tendsto_const_nhds

theorem IsStationaryIn.radialDefectMeasure_closedBall_ne_top
    {U : Set E} (hV : V.IsStationaryIn U) {ξ : E} {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hball : closedBall ξ R ⊆ U) :
    V.radialDefectMeasure ξ (closedBall ξ ρ) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (V.normalizedBallMass_ne_top ξ hρ)
  rw [← IsStationaryIn.density_add_radialDefectMeasure (V := V) hV hρ hρR hball]
  exact le_add_left le_rfl

/-- The finiteness assertion accompanying Simon (4.3.10), in real Bochner
integrability form, with no puncture at the centre. -/
theorem IsStationaryIn.integrableOn_radialDefect_closedBall
    {U : Set E} (hV : V.IsStationaryIn U) {ξ : E} {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hball : closedBall ξ R ⊆ U) :
    MeasureTheory.IntegrableOn (fun x ↦ V.radialNormalSq ξ x / ‖x - ξ‖ ^ n)
      (closedBall ξ ρ) V.weight := by
  apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    (((V.radialNormalSq_aemeasurable ξ).div (by fun_prop)).aestronglyMeasurable.restrict)
    (Eventually.of_forall fun x ↦
      div_nonneg (V.radialNormalSq_nonneg ξ x) (pow_nonneg (norm_nonneg _) n))).mp
  change (∫⁻ x in closedBall ξ ρ,
    ENNReal.ofReal (V.radialNormalSq ξ x / ‖x - ξ‖ ^ n) ∂V.weight) ≠ ⊤
  rw [← V.radialDefectMeasure_apply ξ measurableSet_closedBall]
  exact IsStationaryIn.radialDefectMeasure_closedBall_ne_top (V := V) hV hρ hρR hball

/-- The normalized, nonnegative-integral version of Simon (4.3.10). -/
theorem IsStationaryIn.stationaryDensity_add_defect
    {U : Set E} (hV : V.IsStationaryIn U) {ξ : E} {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hball : closedBall ξ R ⊆ U) :
    V.stationaryDensity ξ +
      (∫⁻ x in closedBall ξ ρ, ENNReal.ofReal (V.radialNormalSq ξ x / ‖x - ξ‖ ^ n)
        ∂V.weight) / Chapter01.realUnitBallVolume (n : ℝ) = V.densityQuotient ξ ρ := by
  rw [stationaryDensity, densityQuotient, ← ENNReal.add_div,
    ← V.radialDefectMeasure_apply ξ measurableSet_closedBall,
    IsStationaryIn.density_add_radialDefectMeasure (V := V) hV hρ hρR hball]

/-- Simon (4.3.10), with the source's real normalization and its full closed
ball. In particular, the integral on the right is finite by the preceding
integrability theorem. -/
theorem IsStationaryIn.stationaryDensity_formula_real
    {U : Set E} (hV : V.IsStationaryIn U) {ξ : E} {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hball : closedBall ξ R ⊆ U) :
    V.weight.real (closedBall ξ ρ) /
      ((Chapter01.realUnitBallVolume (n : ℝ)).toReal * ρ ^ n) -
        V.stationaryDensityReal ξ =
      (Chapter01.realUnitBallVolume (n : ℝ)).toReal⁻¹ *
        ∫ x in closedBall ξ ρ, V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight := by
  have hD := ne_top_of_le_ne_top (V.normalizedBallMass_ne_top ξ hρ)
    (IsStationaryIn.lowerDensityMassRatio_le (V := V) hV hρ hρR hball)
  have hν := IsStationaryIn.radialDefectMeasure_closedBall_ne_top (V := V) hV hρ hρR hball
  have hint := IsStationaryIn.integrableOn_radialDefect_closedBall (V := V) hV hρ hρR hball
  have hnonneg : ∀ x : E, 0 ≤ V.radialNormalSq ξ x / ‖x - ξ‖ ^ n :=
    fun x ↦ div_nonneg (V.radialNormalSq_nonneg ξ x) (pow_nonneg (norm_nonneg _) n)
  have heq := congrArg ENNReal.toReal
    (IsStationaryIn.density_add_radialDefectMeasure (V := V) hV hρ hρR hball)
  rw [ENNReal.toReal_add hD hν, V.radialDefectMeasure_apply ξ measurableSet_closedBall,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnonneg),
    ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg hnonneg), normalizedBallMass,
    ENNReal.toReal_div, ENNReal.toReal_ofReal (pow_pos hρ n).le] at heq
  rw [stationaryDensityReal, stationaryDensity, ENNReal.toReal_div,
    mul_comm (Chapter01.realUnitBallVolume (n : ℝ)).toReal (ρ ^ n), ← div_div, ← sub_div]
  have hsub : V.weight.real (closedBall ξ ρ) / ρ ^ n -
      (V.lowerDensityMassRatio ξ).toReal =
        ∫ x in closedBall ξ ρ, V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight := by
    change (V.lowerDensityMassRatio ξ).toReal + _ = V.weight.real (closedBall ξ ρ) / ρ ^ n at heq
    linarith
  rw [hsub, div_eq_mul_inv, mul_comm]

/-! ### The differentiated identity -/

theorem IsStationaryIn.normalizedBallMass_real_eq_density_add_defect
    {U : Set E} (hV : V.IsStationaryIn U) {ξ : E} {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hball : closedBall ξ R ⊆ U) :
    V.weight.real (closedBall ξ ρ) / ρ ^ n = (V.lowerDensityMassRatio ξ).toReal +
      ∫ x in closedBall ξ ρ, V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight := by
  have hD := ne_top_of_le_ne_top (V.normalizedBallMass_ne_top ξ hρ)
    (IsStationaryIn.lowerDensityMassRatio_le (V := V) hV hρ hρR hball)
  have hν := IsStationaryIn.radialDefectMeasure_closedBall_ne_top (V := V) hV hρ hρR hball
  have heq := congrArg ENNReal.toReal
    (IsStationaryIn.density_add_radialDefectMeasure (V := V) hV hρ hρR hball)
  rw [ENNReal.toReal_add hD hν, normalizedBallMass, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (pow_pos hρ n).le] at heq
  change (V.lowerDensityMassRatio ξ).toReal + (V.radialDefectMeasure ξ).real (closedBall ξ ρ) =
    V.weight.real (closedBall ξ ρ) / ρ ^ n at heq
  rw [V.radialDefectMeasure_real] at heq
  exact heq.symm

theorem IsStationaryIn.radialDefectIntegral_monotoneOn
    {U : Set E} (hV : V.IsStationaryIn U) {ξ : E} {R : ℝ}
    (hball : closedBall ξ R ⊆ U) :
    MonotoneOn (fun ρ ↦ ∫ x in closedBall ξ ρ,
      V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) (Ioo 0 R) := by
  intro σ hσ ρ hρ hσρ
  dsimp only
  rw [← V.radialDefectMeasure_real, ← V.radialDefectMeasure_real]
  exact MeasureTheory.measureReal_mono (closedBall_subset_closedBall hσρ)
    (IsStationaryIn.radialDefectMeasure_closedBall_ne_top (V := V) hV hρ.1 hρ.2 hball)

/-- Both functions in Simon (4.3.7) are locally integrable on `(0,R)`, so
their distributional derivatives are defined. -/
theorem IsStationaryIn.monotonicity_functions_locallyIntegrableOn
    {U : Set E} (hV : V.IsStationaryIn U) {ξ : E} {R : ℝ}
    (hball : closedBall ξ R ⊆ U) :
    MeasureTheory.LocallyIntegrableOn
      (fun ρ ↦ V.weight.real (closedBall ξ ρ) / ρ ^ n) (Ioo 0 R) ∧
    MeasureTheory.LocallyIntegrableOn
      (fun ρ ↦ ∫ x in closedBall ξ ρ, V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight)
      (Ioo 0 R) := by
  have hmono := IsStationaryIn.radialDefectIntegral_monotoneOn (V := V) hV hball
  have hG : MeasureTheory.LocallyIntegrableOn
      (fun ρ ↦ ∫ x in closedBall ξ ρ, V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight)
      (Ioo 0 R) := by
    apply (MeasureTheory.locallyIntegrableOn_iff isOpen_Ioo.isLocallyClosed).mpr
    intro K hK hcompact
    exact (hmono.mono hK).integrableOn_isCompact hcompact
  refine ⟨?_, hG⟩
  apply ((MeasureTheory.locallyIntegrableOn_const (V.lowerDensityMassRatio ξ).toReal).add hG).congr
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with ρ hρ
  exact (IsStationaryIn.normalizedBallMass_real_eq_density_add_defect
    (V := V) hV hρ.1 hρ.2 hball).symm

/-- Simon (4.3.7) in the distribution sense: the difference of the two
locally integrable functions annihilates the derivative of every compactly
supported `C¹` test function in `(0,R)`. This in particular covers all smooth
distribution test functions. -/
theorem IsStationaryIn.stationaryMonotonicity_distributional
    {U : Set E} (hV : V.IsStationaryIn U) {ξ : E} {R : ℝ}
    (hball : closedBall ξ R ⊆ U) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hcompact : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ Ioo 0 R) :
    (∫ ρ : ℝ, (V.weight.real (closedBall ξ ρ) / ρ ^ n -
      ∫ x in closedBall ξ ρ, V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) * deriv ψ ρ) = 0 := by
  have heq : (fun ρ : ℝ ↦ (V.weight.real (closedBall ξ ρ) / ρ ^ n -
      ∫ x in closedBall ξ ρ, V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) * deriv ψ ρ) =
      (fun ρ ↦ (V.lowerDensityMassRatio ξ).toReal * deriv ψ ρ) := by
    funext ρ
    by_cases hρ : ρ ∈ tsupport ψ
    · rw [IsStationaryIn.normalizedBallMass_real_eq_density_add_defect
        (V := V) hV (hsupp hρ).1 (hsupp hρ).2 hball]
      ring
    · rw [deriv_of_notMem_tsupport hρ]
      simp only [mul_zero]
  rw [heq, MeasureTheory.integral_const_mul]
  have hzero : (∫ ρ : ℝ, deriv ψ ρ) = 0 :=
    MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable
      (fun ρ ↦ (hψ.differentiable (by norm_num) ρ).hasDerivAt)
      ((hψ.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcompact.deriv)
      (hψ.continuous.integrable_of_hasCompactSupport hcompact)
  rw [hzero, mul_zero]

/-- Simon (4.3.7) in the classical sense for almost every radius. The
statement supplies actual derivatives of both functions, not merely an
equality of the totalized `deriv` operation at potentially nonsmooth radii. -/
theorem IsStationaryIn.stationaryMonotonicity_ae_hasDerivAt
    {U : Set E} (hV : V.IsStationaryIn U) {ξ : E} {R : ℝ}
    (hball : closedBall ξ R ⊆ U) :
    ∀ᵐ ρ : ℝ ∂MeasureTheory.volume.restrict (Ioo 0 R), ∃ d : ℝ,
      HasDerivAt (fun t ↦ V.weight.real (closedBall ξ t) / t ^ n) d ρ ∧
      HasDerivAt (fun t ↦ ∫ x in closedBall ξ t,
        V.radialNormalSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) d ρ := by
  have hdiff := (IsStationaryIn.radialDefectIntegral_monotoneOn
    (V := V) hV hball).ae_differentiableWithinAt measurableSet_Ioo
  filter_upwards [hdiff, MeasureTheory.ae_restrict_mem measurableSet_Ioo] with ρ hd hρ
  have hdAt := hd.differentiableAt (Ioo_mem_nhds hρ.1 hρ.2)
  refine ⟨_, ?_, hdAt.hasDerivAt⟩
  apply (hdAt.hasDerivAt.const_add (V.lowerDensityMassRatio ξ).toReal).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hρ.1 hρ.2] with t ht
  exact IsStationaryIn.normalizedBallMass_real_eq_density_add_defect
    (V := V) hV ht.1 ht.2 hball

/-! ### Dependence on the centre -/

/-- The mass of a fixed-radius closed ball is upper semicontinuous in its
centre for the locally finite varifold weight. Compactness and outer
regularity avoid assuming that the boundary sphere has zero measure. -/
theorem upperSemicontinuous_closedBall_mass (ρ : ℝ) :
    UpperSemicontinuous (fun ξ : E ↦ V.weight (closedBall ξ ρ)) := by
  intro ξ a ha
  obtain ⟨W, hsub, hW, hmass⟩ := (closedBall ξ ρ).exists_isOpen_lt_of_lt a ha
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_closedBall ξ ρ).exists_thickening_subset_open hW hsub
  filter_upwards [ball_mem_nhds ξ hδ] with η hη
  apply lt_of_le_of_lt (MeasureTheory.measure_mono ?_) hmass
  intro x hx
  apply hthick
  rw [mem_thickening_iff]
  refine ⟨x - η + ξ, ?_, ?_⟩
  · simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right] using hx
  · have heq : x - (x - η + ξ) = η - ξ := by abel
    simpa only [mem_ball, dist_eq_norm, heq] using hη

theorem upperSemicontinuous_normalizedBallMass {ρ : ℝ} (hρ : 0 < ρ) :
    UpperSemicontinuous (fun ξ : E ↦ V.normalizedBallMass ξ ρ) := by
  exact (ENNReal.continuous_div_const _
    (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hρ n)))).comp_upperSemicontinuous
      (V.upperSemicontinuous_closedBall_mass ρ)
      (fun _ _ h ↦ ENNReal.div_le_div_right h _)

theorem IsStationaryIn.upperSemicontinuousAt_lowerDensityMassRatio
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U)
    {ξ : E} (hξ : ξ ∈ U) : UpperSemicontinuousAt V.lowerDensityMassRatio ξ := by
  obtain ⟨R, hR, hball⟩ := exists_pos_closedBall_subset hU hξ
  have hhalfball : closedBall ξ (R / 2) ⊆ U :=
    (closedBall_subset_closedBall (half_le_self hR.le)).trans hball
  intro a ha
  rw [V.lowerDensityMassRatio_eq_stationaryDensityRatio (half_pos hR)
    (IsStationaryIn.satisfiesStationaryMonotonicity (V := V) hV ξ hhalfball),
    stationaryDensityRatio, sInf_lt_iff] at ha
  obtain ⟨_, ⟨ρ, hρ, rfl⟩, hmass⟩ := ha
  filter_upwards [(V.upperSemicontinuous_normalizedBallMass hρ.1) ξ a hmass,
    ball_mem_nhds ξ (half_pos hR)] with η hηmass hη
  apply lt_of_le_of_lt (IsStationaryIn.lowerDensityMassRatio_le (V := V) hV hρ.1 hρ.2 ?_)
    hηmass
  apply subset_trans (closedBall_subset_closedBall' (x := η) (y := ξ) ?_) hball
  have hdist : dist η ξ < R / 2 := hη
  linarith

/-- Simon (4.3.11): density is upper semicontinuous on the stationary open
domain. The density is finite there by (4.3.9). -/
theorem IsStationaryIn.upperSemicontinuousOn_stationaryDensity
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U) :
    UpperSemicontinuousOn V.stationaryDensity U := by
  apply (ENNReal.continuous_div_const _
    (ne_of_gt (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)))).comp_upperSemicontinuousOn
  · intro ξ hξ
    exact (IsStationaryIn.upperSemicontinuousAt_lowerDensityMassRatio
      (V := V) hV hU hξ).upperSemicontinuousWithinAt U
  · exact fun _ _ h ↦ ENNReal.div_le_div_right h _

/-- The real-valued version of Simon (4.3.11); conversion from `ℝ≥0∞` is
justified by the finite-density theorem at every point of the domain. -/
theorem IsStationaryIn.upperSemicontinuousOn_stationaryDensityReal
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U) :
    UpperSemicontinuousOn V.stationaryDensityReal U := by
  intro ξ hξ a ha
  have hapos : 0 < a := ENNReal.toReal_nonneg.trans_lt ha
  have hlt : V.stationaryDensity ξ < ENNReal.ofReal a := by
    apply (ENNReal.toReal_lt_toReal
      (IsStationaryIn.stationaryDensity_ne_top (V := V) hV hU hξ) ENNReal.ofReal_ne_top).mp
    simpa only [stationaryDensityReal, ENNReal.toReal_ofReal hapos.le] using ha
  filter_upwards [IsStationaryIn.upperSemicontinuousOn_stationaryDensity (V := V) hV hU
    ξ hξ (ENNReal.ofReal a) hlt, self_mem_nhdsWithin] with η hη hηU
  have h := (ENNReal.toReal_lt_toReal
    (IsStationaryIn.stationaryDensity_ne_top (V := V) hV hU hηU) ENNReal.ofReal_ne_top).mpr hη
  simpa only [stationaryDensityReal, ENNReal.toReal_ofReal hapos.le] using h

/-- Simon (4.3.11), in its displayed `limsup` form. -/
theorem IsStationaryIn.limsup_stationaryDensity_le
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U)
    {ξ : E} (hξ : ξ ∈ U) :
    limsup V.stationaryDensity (𝓝[U] ξ) ≤ V.stationaryDensity ξ :=
  (IsStationaryIn.upperSemicontinuousOn_stationaryDensity (V := V) hV hU).limsup_le ξ hξ

/-- The canonical positive-density carrier in Simon (4.3.12). Identifying its
rectifiable-varifold representative requires the a.e. density theorem; no
such identification is assumed here. -/
def canonicalDensityCarrier (U : Set E) : Set E :=
  {ξ ∈ U | 0 < V.stationaryDensity ξ}

/-- Simon (4.3.13), first assertion: positive density superlevels are
relatively closed in the stationary domain. In fact every superlevel is. -/
theorem IsStationaryIn.isClosed_stationaryDensity_superlevel
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U) (α : ℝ≥0∞) :
    IsClosed {ξ : U | α ≤ V.stationaryDensity ξ} := by
  exact (upperSemicontinuousOn_iff_restrict.mpr
    (IsStationaryIn.upperSemicontinuousOn_stationaryDensity (V := V) hV hU)).isClosed_preimage α

theorem IsStationaryIn.isClosed_stationaryDensityReal_superlevel
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U) (α : ℝ) :
    IsClosed {ξ : U | α ≤ V.stationaryDensityReal ξ} := by
  exact (upperSemicontinuousOn_iff_restrict.mpr
    (IsStationaryIn.upperSemicontinuousOn_stationaryDensityReal (V := V) hV hU)).isClosed_preimage α

/-- The precise superlevel set displayed in Simon (4.3.13), with the
positive-density carrier from (4.3.12). The following source paragraph's
identification with `spt V ∩ U` additionally requires the a.e. density theorem. -/
theorem IsStationaryIn.isClosed_canonicalDensity_superlevel
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U) {α : ℝ} (hα : 0 < α) :
    IsClosed {ξ : U | (ξ : E) ∈ V.canonicalDensityCarrier U ∧
      α ≤ V.stationaryDensityReal ξ} := by
  have heq : {ξ : U | (ξ : E) ∈ V.canonicalDensityCarrier U ∧
      α ≤ V.stationaryDensityReal ξ} = {ξ : U | α ≤ V.stationaryDensityReal ξ} := by
    ext ξ
    constructor
    · exact fun h ↦ h.2
    · intro h
      exact ⟨⟨ξ.property, (ENNReal.toReal_pos_iff.mp (hα.trans_le h)).1⟩, h⟩
  rw [heq]
  exact IsStationaryIn.isClosed_stationaryDensityReal_superlevel (V := V) hV hU α

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
