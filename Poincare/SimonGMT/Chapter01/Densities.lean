module

public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Poincare.SimonGMT.Chapter01.Hausdorff
public import Poincare.SimonGMT.Chapter01.DensityCovering

@[expose] public section

/-!
# Simon GMT, Chapter 1, §3: densities

This file gives the outer-measure densities and the source-hypothesis
measurability theorem (3.1)--(3.2), the completed-Lebesgue density theorem
(3.8), the exceptional-region conventions (3.9), and the Euclidean covering
results (3.11)(3)--(3.12).  The exact five-times covering statements
(3.4)--(3.5) and Symmetric Vitali definition (3.10) are imported from
`DensityCovering`.

The final uniformly locally doubling section is explicitly a specialization,
not a proof of Simon's full Symmetric-Vitali differentiation theorems.
-/

open Filter Metric Set
open scoped ENNReal MeasureTheory Topology Classical

namespace Poincare.SimonGMT.Chapter01

universe u v

variable {X : Type u} [PseudoMetricSpace X]

/-- Simon (3.1): the normalized closed-ball quotient, for an arbitrary outer
measure and an arbitrary set.  No measurability of `A` is imposed. -/
noncomputable def dimensionalDensityQuotient
    (μ : MeasureTheory.OuterMeasure X) (n : ℝ) (A : Set X) (x : X) (r : ℝ) : ℝ≥0∞ :=
  μ (A ∩ closedBall x r) / (realUnitBallVolume n * ENNReal.ofReal r ^ n)

/-- Simon (3.1), upper `n`-dimensional density, with values in `[0, ∞]`. -/
noncomputable def dimensionalUpperDensity
    (μ : MeasureTheory.OuterMeasure X) (n : ℝ) (A : Set X) (x : X) : ℝ≥0∞ :=
  limsup (dimensionalDensityQuotient μ n A x) (𝓝[>] (0 : ℝ))

/-- Simon (3.1), lower `n`-dimensional density, with values in `[0, ∞]`. -/
noncomputable def dimensionalLowerDensity
    (μ : MeasureTheory.OuterMeasure X) (n : ℝ) (A : Set X) (x : X) : ℝ≥0∞ :=
  liminf (dimensionalDensityQuotient μ n A x) (𝓝[>] (0 : ℝ))

/-- Existence of the dimensional density, including an infinite limiting
value.  The equivalence with equal upper and lower densities is below. -/
def HasDimensionalDensityAt
    (μ : MeasureTheory.OuterMeasure X) (n : ℝ) (A : Set X) (x : X) (d : ℝ≥0∞) : Prop :=
  Tendsto (dimensionalDensityQuotient μ n A x) (𝓝[>] (0 : ℝ)) (𝓝 d)

/-- The restriction identity immediately following Simon (3.1). -/
theorem dimensionalDensityQuotient_restrict
    (μ : MeasureTheory.OuterMeasure X) (n : ℝ) (A : Set X) (x : X) :
    dimensionalDensityQuotient (MeasureTheory.OuterMeasure.restrict A μ) n univ x =
      dimensionalDensityQuotient μ n A x := by
  funext r
  simp [dimensionalDensityQuotient, MeasureTheory.OuterMeasure.restrict_apply, inter_comm]

theorem dimensionalUpperDensity_restrict
    (μ : MeasureTheory.OuterMeasure X) (n : ℝ) (A : Set X) (x : X) :
    dimensionalUpperDensity (MeasureTheory.OuterMeasure.restrict A μ) n univ x =
      dimensionalUpperDensity μ n A x := by
  rw [dimensionalUpperDensity, dimensionalDensityQuotient_restrict, dimensionalUpperDensity]

theorem dimensionalLowerDensity_restrict
    (μ : MeasureTheory.OuterMeasure X) (n : ℝ) (A : Set X) (x : X) :
    dimensionalLowerDensity (MeasureTheory.OuterMeasure.restrict A μ) n univ x =
      dimensionalLowerDensity μ n A x := by
  rw [dimensionalLowerDensity, dimensionalDensityQuotient_restrict, dimensionalLowerDensity]

theorem dimensionalLowerDensity_le_upper
    (μ : MeasureTheory.OuterMeasure X) (n : ℝ) (A : Set X) (x : X) :
    dimensionalLowerDensity μ n A x ≤ dimensionalUpperDensity μ n A x :=
  liminf_le_limsup

/-- The convention following Simon (3.2) agrees with existence of a limit,
also when the common upper and lower value is infinite. -/
theorem hasDimensionalDensityAt_iff
    (μ : MeasureTheory.OuterMeasure X) (n : ℝ) (A : Set X) (x : X) (d : ℝ≥0∞) :
    HasDimensionalDensityAt μ n A x d ↔
      dimensionalLowerDensity μ n A x = d ∧ dimensionalUpperDensity μ n A x = d := by
  constructor
  · intro h
    exact ⟨h.liminf_eq, h.limsup_eq⟩
  · rintro ⟨hi, hs⟩
    exact tendsto_of_liminf_eq_limsup hi hs

/-- The open zero-ball region used as `U₀` or `V₀` in Simon (3.9). -/
def zeroBallRegion (μ : MeasureTheory.OuterMeasure X) : Set X :=
  {x | ∃ r > 0, μ (closedBall x r) = 0}

theorem isOpen_zeroBallRegion (μ : MeasureTheory.OuterMeasure X) :
    IsOpen (zeroBallRegion μ) := by
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨r, hr, hμr⟩ := hx
  refine ⟨r / 2, half_pos hr, fun y hy => ⟨r / 2, half_pos hr, ?_⟩⟩
  apply MeasureTheory.measure_mono_null (t := closedBall x r) ?_ hμr
  intro z hz
  have hzy := mem_closedBall.mp hz
  have hyx := mem_ball.mp hy
  have htri := dist_triangle z y x
  rw [mem_closedBall]
  linarith

theorem eventually_closedBall_measure_zero_of_mem_zeroBallRegion
    {μ : MeasureTheory.OuterMeasure X} {x : X} (hx : x ∈ zeroBallRegion μ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (closedBall x r) = 0 := by
  obtain ⟨R, hR, hμR⟩ := hx
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hR)] with r hr
  exact MeasureTheory.measure_mono_null (closedBall_subset_closedBall hr.le) hμR

/-- Outer-measure form of the quotient in Simon (3.9).  Its filter limits
obey the source's exceptional conventions, as proved below. -/
noncomputable def outerRelativeDensityQuotient
    (μ ν : MeasureTheory.OuterMeasure X) (x : X) (r : ℝ) : ℝ≥0∞ :=
  μ (closedBall x r) / ν (closedBall x r)

/-- Simon (3.9), for the source's outer measures.  `ENNReal` division has
`0 / 0 = 0` and positive-number-over-zero equal to `∞`; the next lemmas
prove the exact three branches of Simon's definition. -/
noncomputable def outerRelativeUpperDensity
    (μ ν : MeasureTheory.OuterMeasure X) (x : X) : ℝ≥0∞ :=
  limsup (outerRelativeDensityQuotient μ ν x) (𝓝[>] (0 : ℝ))

/-- Simon (3.18), with the same exceptional conventions as (3.9). -/
noncomputable def outerRelativeLowerDensity
    (μ ν : MeasureTheory.OuterMeasure X) (x : X) : ℝ≥0∞ :=
  liminf (outerRelativeDensityQuotient μ ν x) (𝓝[>] (0 : ℝ))

theorem tendsto_outerRelativeDensityQuotient_zero
    (μ ν : MeasureTheory.OuterMeasure X) {x : X} (hx : x ∈ zeroBallRegion μ) :
    Tendsto (outerRelativeDensityQuotient μ ν x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_closedBall_measure_zero_of_mem_zeroBallRegion hx] with r hr
  simp [outerRelativeDensityQuotient, hr]

theorem tendsto_outerRelativeDensityQuotient_top
    (μ ν : MeasureTheory.OuterMeasure X) {x : X}
    (hxν : x ∈ zeroBallRegion ν) (hxμ : x ∉ zeroBallRegion μ) :
    Tendsto (outerRelativeDensityQuotient μ ν x) (𝓝[>] (0 : ℝ)) (𝓝 ∞) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_closedBall_measure_zero_of_mem_zeroBallRegion hxν,
    self_mem_nhdsWithin] with r hr hrpos
  have hμ : μ (closedBall x r) ≠ 0 := fun h => hxμ ⟨r, hrpos, h⟩
  simp [outerRelativeDensityQuotient, hr, ENNReal.div_zero, hμ]

/-- The literal three cases of Simon (3.9), including both zero-denominator
regions and their overlap. -/
theorem outerRelativeUpperDensity_eq_piecewise
    (μ ν : MeasureTheory.OuterMeasure X) (x : X) :
    outerRelativeUpperDensity μ ν x =
      if x ∈ zeroBallRegion μ then 0 else
      if x ∈ zeroBallRegion ν then ∞ else
      limsup (outerRelativeDensityQuotient μ ν x) (𝓝[>] (0 : ℝ)) := by
  classical
  split_ifs with hμ hν
  · exact (tendsto_outerRelativeDensityQuotient_zero μ ν hμ).limsup_eq
  · exact (tendsto_outerRelativeDensityQuotient_top μ ν hν hμ).limsup_eq
  · rfl

/-- The literal three cases of Simon (3.18). -/
theorem outerRelativeLowerDensity_eq_piecewise
    (μ ν : MeasureTheory.OuterMeasure X) (x : X) :
    outerRelativeLowerDensity μ ν x =
      if x ∈ zeroBallRegion μ then 0 else
      if x ∈ zeroBallRegion ν then ∞ else
      liminf (outerRelativeDensityQuotient μ ν x) (𝓝[>] (0 : ℝ)) := by
  classical
  split_ifs with hμ hν
  · exact (tendsto_outerRelativeDensityQuotient_zero μ ν hμ).liminf_eq
  · exact (tendsto_outerRelativeDensityQuotient_top μ ν hν hμ).liminf_eq
  · rfl

variable [MeasurableSpace X]

/-- The closed-ball semicontinuity assertion used in Simon (3.2).
Finiteness is assumed on all closed balls, exactly as in that remark;
no separability, properness, or doubling assumption is added. -/
theorem upperSemicontinuous_measure_closedBall [OpensMeasurableSpace X]
    (μ : MeasureTheory.Measure X)
    (hfinite : ∀ x r, μ (closedBall x r) ≠ ∞) (r : ℝ) :
    UpperSemicontinuous (fun x => μ (closedBall x r)) := by
  intro x a ha
  have ht := MeasureTheory.tendsto_measure_biInter_gt
    (μ := μ) (a := r) (s := closedBall x)
    (fun _ _ => measurableSet_closedBall.nullMeasurableSet)
    (fun _ _ _ hij => closedBall_subset_closedBall hij)
    ⟨r + 1, by linarith, hfinite x (r + 1)⟩
  rw [biInter_gt_closedBall] at ht
  obtain ⟨R, hRa, hrR⟩ :=
    ((ht.eventually (gt_mem_nhds ha)).and self_mem_nhdsWithin).exists
  filter_upwards [ball_mem_nhds x (sub_pos.mpr hrR)] with y hy
  apply lt_of_le_of_lt (MeasureTheory.measure_mono ?_) hRa
  intro z hz
  have hzy := mem_closedBall.mp hz
  have hyx := mem_ball.mp hy
  have htri := dist_triangle z y x
  rw [mem_closedBall]
  linarith

/-- The open-ball semicontinuity assertion in Simon (3.2).  The statement
does not require local finiteness. -/
theorem lowerSemicontinuous_measure_ball
    (μ : MeasureTheory.Measure X) (r : ℝ) :
    LowerSemicontinuous (fun x => μ (ball x r)) := by
  intro x a ha
  have hm : Monotone (fun s : Set.Iio r => ball x (s : ℝ)) :=
    fun _ _ h => ball_subset_ball h
  have hu : (⋃ s : Set.Iio r, ball x (s : ℝ)) = ball x r := by
    simpa only [iUnion_subtype, mem_Iio] using biUnion_lt_ball x r
  have heq := hm.measure_iUnion (μ := μ)
  rw [hu] at heq
  change a < μ (ball x r) at ha
  rw [heq] at ha
  obtain ⟨s, hs⟩ := lt_iSup_iff.mp ha
  filter_upwards [ball_mem_nhds x (sub_pos.mpr s.property)] with y hy
  apply lt_of_lt_of_le hs (MeasureTheory.measure_mono ?_)
  intro z hz
  have hzx := mem_ball.mp hz
  have hyx := mem_ball.mp hy
  have htri := dist_triangle z x y
  rw [dist_comm x y] at htri
  rw [mem_ball]
  linarith

omit [MeasurableSpace X] in
/-- Simon (3.2), closed-ball mass for an arbitrary test set `A`: only the
Borel sets, not `A`, must be Caratheodory measurable. -/
theorem upperSemicontinuous_outerMeasure_inter_closedBall
    (μ : MeasureTheory.OuterMeasure X) (hμ : borel X ≤ μ.caratheodory)
    (hfinite : ∀ x r, μ (closedBall x r) ≠ ∞) (A : Set X) (r : ℝ) :
    UpperSemicontinuous (fun x => μ (A ∩ closedBall x r)) := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let ν := MeasureTheory.OuterMeasure.restrict A μ
  have hν : borel X ≤ ν.caratheodory := fun S hS =>
    isCaratheodoryMeasurable_restrict (hμ S hS)
  have happly : ∀ x r, ν.toMeasure hν (closedBall x r) = μ (A ∩ closedBall x r) := by
    intro x r
    rw [MeasureTheory.toMeasure_apply ν hν measurableSet_closedBall]
    simp only [ν, MeasureTheory.OuterMeasure.restrict_apply, inter_comm]
  have hf : ∀ x r, ν.toMeasure hν (closedBall x r) ≠ ∞ := by
    intro x r
    rw [happly]
    exact ne_top_of_le_ne_top (hfinite x r) (μ.mono inter_subset_right)
  simpa only [happly] using upperSemicontinuous_measure_closedBall (ν.toMeasure hν) hf r

omit [MeasurableSpace X] in
/-- The open-ball assertion in Simon (3.2), with the original outer-measure
hypothesis and with no measurability assumption on `A`. -/
theorem lowerSemicontinuous_outerMeasure_inter_ball
    (μ : MeasureTheory.OuterMeasure X) (hμ : borel X ≤ μ.caratheodory)
    (A : Set X) (r : ℝ) :
    LowerSemicontinuous (fun x => μ (A ∩ ball x r)) := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let ν := MeasureTheory.OuterMeasure.restrict A μ
  have hν : borel X ≤ ν.caratheodory := fun S hS =>
    isCaratheodoryMeasurable_restrict (hμ S hS)
  have happly : ∀ x, ν.toMeasure hν (ball x r) = μ (A ∩ ball x r) := by
    intro x
    rw [MeasureTheory.toMeasure_apply ν hν measurableSet_ball]
    simp only [ν, MeasureTheory.OuterMeasure.restrict_apply, inter_comm]
  simpa only [happly] using lowerSemicontinuous_measure_ball (ν.toMeasure hν) r

omit [MeasurableSpace X] in
/-- Right continuity of the closed-ball mass used to pass to countably many
radii in Simon (3.2).  The set `A` is arbitrary. -/
theorem tendsto_outerMeasure_inter_closedBall_right
    (μ : MeasureTheory.OuterMeasure X) (hμ : borel X ≤ μ.caratheodory)
    (hfinite : ∀ x r, μ (closedBall x r) ≠ ∞) (A : Set X) (x : X) (r : ℝ) :
    Tendsto (fun s => μ (A ∩ closedBall x s)) (𝓝[>] r)
      (𝓝 (μ (A ∩ closedBall x r))) := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let ν := MeasureTheory.OuterMeasure.restrict A μ
  have hν : borel X ≤ ν.caratheodory := fun S hS =>
    isCaratheodoryMeasurable_restrict (hμ S hS)
  have happly : ∀ s, ν.toMeasure hν (closedBall x s) = μ (A ∩ closedBall x s) := by
    intro s
    rw [MeasureTheory.toMeasure_apply ν hν measurableSet_closedBall]
    simp only [ν, MeasureTheory.OuterMeasure.restrict_apply, inter_comm]
  have hf : ν.toMeasure hν (closedBall x (r + 1)) ≠ ∞ := by
    rw [happly]
    exact ne_top_of_le_ne_top (hfinite x (r + 1)) (μ.mono inter_subset_right)
  simpa only [biInter_gt_closedBall, Function.comp_def, happly] using
    (MeasureTheory.tendsto_measure_biInter_gt (μ := ν.toMeasure hν)
      (a := r) (s := closedBall x)
      (fun _ _ => measurableSet_closedBall.nullMeasurableSet)
      (fun _ _ _ hij => closedBall_subset_closedBall hij)
      ⟨r + 1, by linarith, hf⟩)

omit [MeasurableSpace X] in
theorem tendsto_dimensionalDensityQuotient_right
    (μ : MeasureTheory.OuterMeasure X) (hμ : borel X ≤ μ.caratheodory)
    (hfinite : ∀ x r, μ (closedBall x r) ≠ ∞)
    {n : ℝ} (hn : 0 ≤ n) (A : Set X) (x : X) {r : ℝ} (hr : 0 < r) :
    Tendsto (dimensionalDensityQuotient μ n A x) (𝓝[>] r)
      (𝓝 (dimensionalDensityQuotient μ n A x r)) := by
  have hp0 : ENNReal.ofReal r ^ n ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr) ENNReal.ofReal_ne_top).ne'
  have hden : Tendsto (fun s : ℝ => realUnitBallVolume n * ENNReal.ofReal s ^ n)
      (𝓝 r) (𝓝 (realUnitBallVolume n * ENNReal.ofReal r ^ n)) :=
    ENNReal.Tendsto.const_mul
      ((ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).tendsto r) (Or.inl hp0)
  have hden0 : realUnitBallVolume n * ENNReal.ofReal r ^ n ≠ 0 :=
    mul_ne_zero (realUnitBallVolume_pos hn).ne' hp0
  exact ENNReal.Tendsto.div
    (tendsto_outerMeasure_inter_closedBall_right μ hμ hfinite A x r)
    (Or.inr hden0) (hden.mono_left nhdsWithin_le_nhds)
    (Or.inr (ne_top_of_le_ne_top (hfinite x r) (μ.mono inter_subset_right)))

/-- A countable positive-rational basis at the positive side of zero. -/
theorem nhdsGT_zero_basis_rat :
    (𝓝[>] (0 : ℝ)).HasBasis (fun q : ℚ => 0 < q)
      (fun q => Set.Ioo 0 (q : ℝ)) := by
  apply (nhdsGT_basis (0 : ℝ)).to_hasBasis
  · intro δ hδ
    obtain ⟨q, hq, hqδ⟩ := exists_pos_rat_lt hδ
    exact ⟨q, hq, Ioo_subset_Ioo_right hqδ.le⟩
  · intro q hq
    exact ⟨(q : ℝ), by exact_mod_cast hq, subset_rfl⟩

/-- A right-continuous extended-valued function has the same supremum on
an open positive-radius interval and on its rational radii. -/
theorem iSup_rat_Ioo_eq_of_tendsto_right
    {Y : Type*} [CompleteLinearOrder Y] [DenselyOrdered Y]
    [TopologicalSpace Y] [OrderTopology Y]
    (f : ℝ → Y) (δ : ℝ)
    (hf : ∀ r ∈ Set.Ioo 0 δ, Tendsto f (𝓝[>] r) (𝓝 (f r))) :
    (⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Set.Ioo 0 δ), f q) =
      ⨆ r : ℝ, ⨆ (_ : r ∈ Set.Ioo 0 δ), f r := by
  apply le_antisymm
  · exact iSup_le fun q => iSup_le fun hq => le_iSup₂_of_le (q : ℝ) hq le_rfl
  · refine iSup_le fun r => iSup_le fun hr => le_of_forall_lt fun a ha => ?_
    obtain ⟨R, hrR, hR⟩ :=
      (nhdsGT_basis r).mem_iff.mp ((hf r hr).eventually (lt_mem_nhds ha))
    obtain ⟨q, hrq, hq⟩ := exists_rat_btwn (lt_min hrR hr.2)
    have hqδ : (q : ℝ) ∈ Set.Ioo 0 δ :=
      ⟨hr.1.trans hrq, hq.trans_le (min_le_right _ _)⟩
    calc
      a < f (q : ℝ) := hR ⟨hrq, hq.trans_le (min_le_left _ _)⟩
      _ ≤ ⨆ s : ℚ, ⨆ (_ : (s : ℝ) ∈ Set.Ioo 0 δ), f s :=
        le_iSup₂_of_le q hqδ le_rfl

omit [MeasurableSpace X] in
/-- The normalized mass at a fixed positive radius is upper semicontinuous,
as asserted in Simon (3.2). -/
theorem upperSemicontinuous_dimensionalDensityQuotient
    (μ : MeasureTheory.OuterMeasure X) (hμ : borel X ≤ μ.caratheodory)
    (hfinite : ∀ x r, μ (closedBall x r) ≠ ∞)
    {n : ℝ} (hn : 0 ≤ n) (A : Set X) {r : ℝ} (hr : 0 < r) :
    UpperSemicontinuous (fun x => dimensionalDensityQuotient μ n A x r) := by
  have hden0 : realUnitBallVolume n * ENNReal.ofReal r ^ n ≠ 0 :=
    mul_ne_zero (realUnitBallVolume_pos hn).ne'
      (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr) ENNReal.ofReal_ne_top).ne'
  exact (ENNReal.continuous_div_const _ hden0).comp_upperSemicontinuous
    (upperSemicontinuous_outerMeasure_inter_closedBall μ hμ hfinite A r)
    (fun _ _ h => ENNReal.div_le_div_right h _)

/-- Simon (3.2): the lower density is Borel measurable.  The underlying
space need not be separable and the set `A` need not be measurable. -/
theorem measurable_dimensionalLowerDensity [OpensMeasurableSpace X]
    (μ : MeasureTheory.OuterMeasure X) (hμ : borel X ≤ μ.caratheodory)
    (hfinite : ∀ x r, μ (closedBall x r) ≠ ∞)
    {n : ℝ} (hn : 0 ≤ n) (A : Set X) :
    Measurable (dimensionalLowerDensity μ n A) := by
  unfold dimensionalLowerDensity
  simp_rw [nhdsGT_zero_basis_rat.liminf_eq_iSup_iInf]
  apply Measurable.iSup fun q => Measurable.iSup fun _ => ?_
  exact (upperSemicontinuous_biInf fun r hr =>
    upperSemicontinuous_dimensionalDensityQuotient μ hμ hfinite hn A hr.1).measurable

/-- Simon (3.2): the upper density is Borel measurable.  Countable rational
radii are justified by right continuity, not by an added separability
assumption on `X`. -/
theorem measurable_dimensionalUpperDensity [OpensMeasurableSpace X]
    (μ : MeasureTheory.OuterMeasure X) (hμ : borel X ≤ μ.caratheodory)
    (hfinite : ∀ x r, μ (closedBall x r) ≠ ∞)
    {n : ℝ} (hn : 0 ≤ n) (A : Set X) :
    Measurable (dimensionalUpperDensity μ n A) := by
  unfold dimensionalUpperDensity
  simp_rw [nhdsGT_zero_basis_rat.limsup_eq_iInf_iSup]
  apply Measurable.iInf fun q => Measurable.iInf fun _ => ?_
  have heq : (fun x => ⨆ r : ℝ, ⨆ (_ : r ∈ Set.Ioo 0 (q : ℝ)),
      dimensionalDensityQuotient μ n A x r) =
      (fun x => ⨆ s : ℚ, ⨆ (_ : (s : ℝ) ∈ Set.Ioo 0 (q : ℝ)),
        dimensionalDensityQuotient μ n A x s) := by
    funext x
    exact (iSup_rat_Ioo_eq_of_tendsto_right _ _ fun r hr =>
      tendsto_dimensionalDensityQuotient_right μ hμ hfinite hn A x hr.1).symm
  rw [heq]
  exact Measurable.iSup fun s => Measurable.iSup fun hs =>
    (upperSemicontinuous_dimensionalDensityQuotient μ hμ hfinite hn A hs.1).measurable

omit [MeasurableSpace X] in
/-- Simon (3.2), with the Borel sigma-algebra explicit and finiteness
required only for positive-radius balls, as in the source.  Neither a
measurable-space choice nor measurability of `A` is an extra hypothesis. -/
theorem borelMeasurable_dimensionalDensities
    (μ : MeasureTheory.OuterMeasure X) (hμ : borel X ≤ μ.caratheodory)
    (hfinite : ∀ x r, 0 < r → μ (closedBall x r) ≠ ∞)
    {n : ℝ} (hn : 0 ≤ n) (A : Set X) :
    @Measurable X ℝ≥0∞ (borel X) _ (dimensionalLowerDensity μ n A) ∧
      @Measurable X ℝ≥0∞ (borel X) _ (dimensionalUpperDensity μ n A) := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  have hf : ∀ x r, μ (closedBall x r) ≠ ∞ := by
    intro x r
    exact ne_top_of_le_ne_top
      (hfinite x (max r 1) (zero_lt_one.trans_le (le_max_right _ _)))
      (μ.mono (closedBall_subset_closedBall (le_max_left _ _)))
  exact ⟨measurable_dimensionalLowerDensity μ hμ hf hn A,
    measurable_dimensionalUpperDensity μ hμ hf hn A⟩

/-- The exceptional open region is exactly the complement of the support;
this identity requires no finiteness or regularity assumption. -/
theorem zeroBallRegion_toOuterMeasure_eq_compl_support (μ : MeasureTheory.Measure X) :
    zeroBallRegion μ.toOuterMeasure = μ.supportᶜ := by
  ext x
  exact (Metric.nhds_basis_closedBall.notMem_measureSupport (μ := μ)).symm

/-- Simon (3.11)(1), separable-metric-space case.  In fact second
countability alone suffices, with no local finiteness assumption. -/
theorem measure_zeroBallRegion_eq_zero [SecondCountableTopology X]
    (μ : MeasureTheory.Measure X) : μ (zeroBallRegion μ.toOuterMeasure) = 0 := by
  rw [zeroBallRegion_toOuterMeasure_eq_compl_support]
  exact μ.measure_compl_support

omit [MeasurableSpace X] in
/-- Simon (3.11)(1) for Borel-regular outer measures on a separable metric
space, rather than only for their measure adapters. -/
theorem outerMeasure_zeroBallRegion_eq_zero [TopologicalSpace.SeparableSpace X]
    (μ : MeasureTheory.OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ) :
    μ (zeroBallRegion μ) = 0 := by
  let : MeasurableSpace X := borel X
  simpa only [hμ.toOuterMeasure_toBorelMeasure, hμ.toBorelMeasure_apply_all] using
    measure_zeroBallRegion_eq_zero hμ.toBorelMeasure

omit [PseudoMetricSpace X] in
/-- For a finite-mass Caratheodory set, the canonical measurable hull
differs by a null set.  This prevents accidentally strengthening Simon's
Lebesgue-measurability hypothesis in (3.8) to Borel measurability. -/
theorem nullMeasurableSet_of_isCaratheodory_of_ne_top
    (μ : MeasureTheory.Measure X) {A : Set X}
    (hA : IsCaratheodoryMeasurable μ.toOuterMeasure A) (hAfin : μ A ≠ ∞) :
    MeasureTheory.NullMeasurableSet A μ := by
  let T := MeasureTheory.toMeasurable μ A
  have hAT : A ⊆ T := MeasureTheory.subset_toMeasurable μ A
  have hT : MeasurableSet T := MeasureTheory.measurableSet_toMeasurable μ A
  have hTm : μ T = μ A := MeasureTheory.measure_toMeasurable A
  have hsplit : μ T = μ A + μ (T \ A) := by
    have h := hA T
    change μ T = μ (T ∩ A) + μ (T \ A) at h
    simpa only [inter_eq_right.mpr hAT] using h
  have hz : μ (T \ A) = 0 := by
    apply (ENNReal.add_left_inj hAfin).mp
    simpa only [zero_add, add_comm] using hsplit.symm.trans hTm
  exact hT.nullMeasurableSet.congr
    ((MeasureTheory.ae_le_set.mpr hz).antisymm hAT.eventuallySubset)

omit [PseudoMetricSpace X] in
/-- In a sigma-finite measure, every source Caratheodory-measurable set is
measurable in the completed measure. -/
theorem nullMeasurableSet_of_isCaratheodory
    (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ] {A : Set X}
    (hA : IsCaratheodoryMeasurable μ.toOuterMeasure A) :
    MeasureTheory.NullMeasurableSet A μ := by
  have hAn : ∀ n : ℕ,
      MeasureTheory.NullMeasurableSet (A ∩ MeasureTheory.spanningSets μ n) μ := by
    intro n
    apply nullMeasurableSet_of_isCaratheodory_of_ne_top μ
    · exact μ.toOuterMeasure.isCaratheodory_inter hA
        (MeasureTheory.le_toOuterMeasure_caratheodory μ _
          (MeasureTheory.measurableSet_spanningSets μ n))
    · exact ((MeasureTheory.measure_mono inter_subset_right).trans_lt
        (MeasureTheory.measure_spanningSets_lt_top μ n)).ne
  simpa only [← inter_iUnion, MeasureTheory.iUnion_spanningSets, inter_univ] using
    MeasureTheory.NullMeasurableSet.iUnion hAn

/-- The Besicovitch density theorem for completed-measurable sets.  This
adapter is only used below in finite-dimensional Euclidean space, where
the covering hypotheses are theorems rather than extra source assumptions. -/
theorem ae_tendsto_measure_inter_div_of_nullMeasurableSet
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [HasBesicovitchCovering E]
    (μ : MeasureTheory.Measure E) [MeasureTheory.IsLocallyFiniteMeasure μ]
    {A : Set E} (hA : MeasureTheory.NullMeasurableSet A μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => μ (A ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (A.indicator 1 x)) := by
  let B := MeasureTheory.toMeasurable μ A
  have hBA : B =ᵐ[μ] A := hA.toMeasurable_ae_eq
  filter_upwards
    [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet μ
      (MeasureTheory.measurableSet_toMeasurable μ A), hBA] with x hx hxBA
  have heq : ∀ r, μ (B ∩ closedBall x r) = μ (A ∩ closedBall x r) :=
    fun r => MeasureTheory.measure_congr (hBA.inter EventuallyEq.rfl)
  change Tendsto (fun r => μ (B ∩ closedBall x r) / μ (closedBall x r))
    (𝓝[>] (0 : ℝ)) (𝓝 (B.indicator 1 x)) at hx
  simpa only [← heq, Set.indicator_apply, hxBA] using hx

/-- The denominator in Simon's Euclidean densities is exactly the
Lebesgue measure of the closed ball, including dimension zero.  This is
the volume-of-balls formula, not the unresolved Hausdorff isodiametric
normalization in (2.9). -/
theorem volume_closedBall_eq_densityNormalization
    (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    MeasureTheory.volume (closedBall x r) =
      realUnitBallVolume (n : ℝ) * ENNReal.ofReal r ^ (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    have hball : closedBall x r = ({x} : Set (EuclideanSpace ℝ (Fin 0))) := by
      ext y
      simp [Subsingleton.elim y x, hr.le]
    rw [← simonHausdorffMeasure_euclidean_eq_volume 0, hball,
      simonHausdorffMeasure_zero_singleton]
    simp
  · let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    have hpi : Real.sqrt Real.pi ^ n = Real.pi ^ ((n : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
      congr 1
      ring
    rw [EuclideanSpace.volume_closedBall, Fintype.card_fin, hpi,
      realUnitBallVolume_eq, ENNReal.rpow_natCast, mul_comm]

/-- Simon (3.8), including every Caratheodory-Lebesgue-measurable set:
the density exists almost everywhere, is one on `A`, and zero off `A`.
There is no finite-total-mass or Borel-set restriction. -/
theorem ae_hasDimensionalDensityAt_volume
    (n : ℕ) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsCaratheodoryMeasurable
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).toOuterMeasure A) :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))),
      HasDimensionalDensityAt MeasureTheory.volume.toOuterMeasure (n : ℝ) A x
        (A.indicator 1 x) := by
  have hAnull := nullMeasurableSet_of_isCaratheodory MeasureTheory.volume hA
  filter_upwards [ae_tendsto_measure_inter_div_of_nullMeasurableSet
    MeasureTheory.volume hAnull] with x hx
  apply hx.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [dimensionalDensityQuotient, MeasureTheory.Measure.toOuterMeasure_apply,
    volume_closedBall_eq_densityNormalization n x hr]

/-- The upper/lower-density form of Simon (3.8). -/
theorem ae_dimensionalDensities_volume
    (n : ℕ) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsCaratheodoryMeasurable
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).toOuterMeasure A) :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))),
      dimensionalLowerDensity MeasureTheory.volume.toOuterMeasure (n : ℝ) A x =
          A.indicator 1 x ∧
      dimensionalUpperDensity MeasureTheory.volume.toOuterMeasure (n : ℝ) A x =
          A.indicator 1 x := by
  filter_upwards [ae_hasDimensionalDensityAt_volume n hA] with x hx
  exact (hasDimensionalDensityAt_iff _ _ _ _ _).mp hx

/-- The observation after Simon (3.9): relative density with respect to
Lebesgue measure is the dimensional density. -/
theorem outerRelativeUpperDensity_volume_eq_dimensional
    (n : ℕ) (μ : MeasureTheory.OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    outerRelativeUpperDensity μ MeasureTheory.volume.toOuterMeasure x =
      dimensionalUpperDensity μ (n : ℝ) univ x := by
  apply Filter.limsup_congr
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [outerRelativeDensityQuotient, dimensionalDensityQuotient,
    MeasureTheory.Measure.toOuterMeasure_apply, univ_inter,
    volume_closedBall_eq_densityNormalization n x hr]

theorem outerRelativeLowerDensity_volume_eq_dimensional
    (n : ℕ) (μ : MeasureTheory.OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    outerRelativeLowerDensity μ MeasureTheory.volume.toOuterMeasure x =
      dimensionalLowerDensity μ (n : ℝ) univ x := by
  apply Filter.liminf_congr
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [outerRelativeDensityQuotient, dimensionalDensityQuotient,
    MeasureTheory.Measure.toOuterMeasure_apply, univ_inter,
    volume_closedBall_eq_densityNormalization n x hr]

/-- A sigma-finite measure in a second-countable Besicovitch space has
Simon's exact centered Symmetric Vitali Property.  No measurability of
the set being covered is assumed. -/
theorem hasSymmetricVitaliProperty_of_hasBesicovitchCovering
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] [HasBesicovitchCovering E]
    (μ : MeasureTheory.Measure E) [MeasureTheory.SFinite μ] :
    HasSymmetricVitaliProperty μ.toOuterMeasure := by
  intro A _ B _ hfine
  have hf : ∀ x ∈ A, ∀ ε > 0,
      ({r : ℝ | (x, r) ∈ B} ∩ Set.Ioo 0 ε).Nonempty := by
    intro x hx ε hε
    obtain ⟨r, hr, hB⟩ := hfine x hx ε hε
    exact ⟨r, hB, hr⟩
  obtain ⟨D, hcount, _, hB, hnull, hdisj⟩ :=
    Besicovitch.exists_disjoint_closedBall_covering_ae_aux μ
      (fun x => {r : ℝ | (x, r) ∈ B}) A hf
  refine ⟨D, ?_, hcount, hdisj, hnull⟩
  intro p hp
  exact hB p hp

/-- Simon (3.11)(3): every Borel-regular outer measure on Euclidean space
which is finite on compact sets has the Symmetric Vitali Property. -/
theorem hasSymmetricVitaliProperty_euclidean
    (n : ℕ) (μ : MeasureTheory.OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : IsBorelRegularOuterMeasure μ)
    (hcompact : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → μ K < ∞) :
    HasSymmetricVitaliProperty μ := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  let ν := hμ.toBorelMeasure
  let : MeasureTheory.IsFiniteMeasureOnCompacts ν := ⟨fun {K} hK => by
    rw [hμ.toBorelMeasure_apply_all]
    exact hcompact K hK⟩
  simpa only [ν, hμ.toOuterMeasure_toBorelMeasure] using
    hasSymmetricVitaliProperty_of_hasBesicovitchCovering ν

/-- Simon (3.12): finitely many pairwise-disjoint subfamilies of a bounded
family of Euclidean closed balls cover every center.  The number of
families is `Besicovitch.multiplicity (EuclideanSpace ℝ (Fin n))`, which
depends only on `n`, not on the radii, centers, or indexing type. -/
theorem exists_besicovitchCovering_families
    (n : ℕ) {ι : Type*} (c : ι → EuclideanSpace ℝ (Fin n)) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (R : ℝ) (hR : ∀ i, r i ≤ R) :
    ∃ D : Fin (Besicovitch.multiplicity (EuclideanSpace ℝ (Fin n))) → Set ι,
      (∀ k, (D k).PairwiseDisjoint (fun i => closedBall (c i) (r i))) ∧
      Set.range c ⊆ ⋃ k, ⋃ i ∈ D k, closedBall (c i) (r i) := by
  let P : Besicovitch.BallPackage ι (EuclideanSpace ℝ (Fin n)) :=
    { c := c, r := r, rpos := hr, r_bound := R, r_le := hR }
  obtain ⟨D, hdisj, hcover⟩ := Besicovitch.exist_disjoint_covering_families
    (Besicovitch.one_lt_goodτ (EuclideanSpace ℝ (Fin n)))
    (Besicovitch.isEmpty_satelliteConfig_multiplicity (EuclideanSpace ℝ (Fin n))) P
  refine ⟨D, hdisj, hcover.trans ?_⟩
  exact iUnion_mono fun _ => iUnion₂_mono fun _ _ => ball_subset_closedBall

/-- Measure-specialized quotient for Simon (3.9).  The exceptional branches
are justified by `outerRelativeUpperDensity_eq_piecewise`. -/
noncomputable def relativeDensityQuotient
    (μ ν : MeasureTheory.Measure X) (x : X) (r : ℝ) : ℝ≥0∞ :=
  μ (closedBall x r) / ν (closedBall x r)

/-- Simon (3.9): relative upper density as a filter limsup. -/
noncomputable def relativeUpperDensity (μ ν : MeasureTheory.Measure X) (x : X) : ℝ≥0∞ :=
  limsup (relativeDensityQuotient μ ν x) (𝓝[>] (0 : ℝ))

/-- Simon (3.18): relative lower density as a filter liminf. -/
noncomputable def relativeLowerDensity (μ ν : MeasureTheory.Measure X) (x : X) : ℝ≥0∞ :=
  liminf (relativeDensityQuotient μ ν x) (𝓝[>] (0 : ℝ))

/-- Simon (3.22): the relative density exists at `x` when the ball-ratio has
a limit.  This formulation retains the limiting value as data and therefore
also covers the extended-real value `∞`. -/
def HasRelativeDensityAt (μ ν : MeasureTheory.Measure X) (x : X) (c : ℝ≥0∞) : Prop :=
  Tendsto (relativeDensityQuotient μ ν x) (𝓝[>] (0 : ℝ)) (𝓝 c)

/-- The measure-specialized API is the exact source outer-measure density. -/
theorem relativeUpperDensity_eq_outer
    (μ ν : MeasureTheory.Measure X) (x : X) :
    relativeUpperDensity μ ν x = outerRelativeUpperDensity μ.toOuterMeasure ν.toOuterMeasure x :=
  rfl

theorem relativeLowerDensity_eq_outer
    (μ ν : MeasureTheory.Measure X) (x : X) :
    relativeLowerDensity μ ν x = outerRelativeLowerDensity μ.toOuterMeasure ν.toOuterMeasure x :=
  rfl

/-- Simon's existence-of-density convention, without excluding `∞`. -/
theorem hasRelativeDensityAt_iff
    (μ ν : MeasureTheory.Measure X) (x : X) (c : ℝ≥0∞) :
    HasRelativeDensityAt μ ν x c ↔
      relativeLowerDensity μ ν x = c ∧ relativeUpperDensity μ ν x = c := by
  constructor
  · intro h
    exact ⟨h.liminf_eq, h.limsup_eq⟩
  · rintro ⟨hi, hs⟩
    exact tendsto_of_liminf_eq_limsup hi hs

section Doubling

variable [SecondCountableTopology X] [BorelSpace X]
  (μ : MeasureTheory.Measure X)
  [MeasureTheory.IsLocallyFiniteMeasure μ]
  [IsUnifLocDoublingMeasure μ]

/-- Uniformly locally doubling specialization of the density-one half of
Simon (3.16).  The set itself may be arbitrary, with almost-everywhere
understood for `μ.restrict S`.  The full source hypothesis of an arbitrary
open-sigma-finite Symmetric-Vitali outer measure is not established here. -/
theorem ae_hasRelativeDensity_restrict_self (S : Set X) :
    ∀ᵐ x ∂μ.restrict S,
      HasRelativeDensityAt (μ.restrict S) μ x 1 := by
  filter_upwards
    [IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div μ S 0]
      with x hx
  have h := hx (fun _ : ℝ ↦ x) id tendsto_id
    (by simp [Metric.mem_closedBall])
  change Tendsto
    (fun r : ℝ ↦ (μ.restrict S) (closedBall x r) / μ (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 1)
  simpa only [MeasureTheory.Measure.restrict_apply,
    measurableSet_closedBall, inter_comm, id_eq] using h

/-- Uniformly locally doubling specialization of Simon (3.17), for
Banach-valued functions.  This does not replace the source's more general
Symmetric-Vitali hypothesis. -/
theorem ae_tendsto_centeredClosedBall_average
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : X → E} (hf : MeasureTheory.LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ,
      Tendsto (fun r : ℝ ↦ ⨍ y in closedBall x r, f y ∂μ)
        (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  filter_upwards
    [IsUnifLocDoublingMeasure.ae_tendsto_average μ hf 0]
      with x hx
  exact hx (fun _ : ℝ ↦ x) id tendsto_id (by simp [Metric.mem_closedBall])

/-- Uniformly locally doubling density/Radon--Nikodym identification.
This is infrastructure for Simon (3.23)--(3.24), not the full source
integral decomposition or its pointwise infinity-density singular set. -/
theorem ae_hasRelativeDensity_rnDeriv (ρ : MeasureTheory.Measure X)
    [MeasureTheory.IsLocallyFiniteMeasure ρ] :
    ∀ᵐ x ∂μ,
      HasRelativeDensityAt ρ μ x (ρ.rnDeriv μ x) := by
  let v := IsUnifLocDoublingMeasure.vitaliFamily μ 0
  filter_upwards [v.ae_tendsto_rnDeriv ρ] with x hx
  apply hx.comp
  exact IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt
    μ (K := 0) (x := x) (fun _ : ℝ ↦ x) id tendsto_id
      (by simp [Metric.mem_closedBall])

end Doubling

end Poincare.SimonGMT.Chapter01
