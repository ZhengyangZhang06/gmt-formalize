module

public import Poincare.SimonGMT.Chapter01.HausdorffDensityBounds

@[expose] public section

/-!
# Simon GMT, Chapter 1, the content-density lower bound

The lower estimate in (3.26)(2) concerns infinite-scale Hausdorff content,
not Hausdorff measure.  Finite content at every positive scale is retained
as the hypothesis; neither finite Hausdorff measure nor separability of
the ambient space is assumed.
-/

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology Classical

namespace Poincare.SimonGMT.Chapter01

variable {X : Type*} [MetricSpace X]

local instance instHausdorffContentDensityMeasurableSpace : MeasurableSpace X := borel X
local instance instHausdorffContentDensityBorelSpace : BorelSpace X := ⟨rfl⟩

/-- Put the normalization inside the generated outer measure. -/
theorem simonHausdorffContentOuter_eq_boundedBy
    (n : ℝ) (δ : ℝ≥0∞) :
    simonHausdorffContentOuter (X := X) n δ =
      OuterMeasure.boundedBy (fun C => realUnitBallVolume n * simonHausdorffCoverCost n δ C) := by
  rw [simonHausdorffContentOuter, OuterMeasure.smul_boundedBy (realUnitBallVolume_ne_top n)]
  rfl

/-- The fixed-scale cost when its diameter test holds. -/
theorem simonHausdorffCoverCost_eq_of_ediam_lt
    (n : ℝ) {δ : ℝ≥0∞} {C : Set X} (hC : ediam C < δ) :
    simonHausdorffCoverCost n δ C = (ediam C / 2) ^ n := by
  rw [simonHausdorffCoverCost]
  exact extend_eq (m := fun C (_ : ediam C < δ) => (ediam C / 2) ^ n) (s := C) hC

/-- The fixed-scale cost when its diameter test fails. -/
theorem simonHausdorffCoverCost_eq_top_of_not_ediam_lt
    (n : ℝ) {δ : ℝ≥0∞} {C : Set X} (hC : ¬ ediam C < δ) :
    simonHausdorffCoverCost n δ C = ∞ := by
  rw [simonHausdorffCoverCost]
  exact extend_eq_top (m := fun C (_ : ediam C < δ) => (ediam C / 2) ^ n) (s := C) hC

/-- Every positive-scale content is bounded above by Hausdorff measure. -/
theorem simonHausdorffContentOuter_le_hausdorff
    (n : ℝ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    simonHausdorffContentOuter (X := X) n δ ≤ simonHausdorffOuterMeasureReal n := by
  rw [simonHausdorffOuterMeasureReal]
  exact le_iSup_of_le δ (le_iSup_of_le hδ le_rfl)

/-- A finite-scale-content set admits a countable cover satisfying the
literal strict diameter constraint, including in dimension zero. -/
theorem exists_countable_small_diameter_cover_of_content_finite
    {n : ℝ} (hn : 0 ≤ n) {δ : ℝ≥0∞} (hδ : 0 < δ) {A : Set X}
    (hfin : simonHausdorffContentOuter n δ A < ∞) :
    ∃ C : ℕ → Set X, A ⊆ ⋃ j, C j ∧ ∀ j, ediam (C j) < δ := by
  rw [simonHausdorffContentOuter_eq_boundedBy, OuterMeasure.boundedBy_apply] at hfin
  obtain ⟨C, hcover, hsum⟩ := (by simpa only [iInf_lt_iff] using hfin)
  refine ⟨C, hcover, fun j => ?_⟩
  rcases (C j).eq_empty_or_nonempty with hj | hj
  · simpa only [hj, ediam_empty] using hδ
  · have hterm : realUnitBallVolume n * simonHausdorffCoverCost n δ (C j) < ∞ :=
      ((le_iSup (fun _ : (C j).Nonempty => _) hj).trans
        (ENNReal.le_tsum (f := fun k => ⨆ _ : (C k).Nonempty,
          realUnitBallVolume n * simonHausdorffCoverCost n δ (C k)) j)).trans_lt hsum
    by_contra hnot
    rw [simonHausdorffCoverCost_eq_top_of_not_ediam_lt n hnot,
      ENNReal.mul_top (realUnitBallVolume_pos hn).ne'] at hterm
    exact hterm.false

/-- Null infinite-scale content implies null content at every positive
scale.  The proof also covers the zero-dimensional cost convention. -/
theorem simonHausdorffContentOuter_eq_zero_of_infinite_content_zero
    {n : ℝ} (hn : 0 ≤ n) {A : Set X}
    (hzero : simonHausdorffContentOuter n ∞ A = 0)
    {δ : ℝ≥0∞} (hδ : 0 < δ) : simonHausdorffContentOuter n δ A = 0 := by
  apply le_antisymm _ bot_le
  apply le_of_forall_gt_imp_ge_of_dense
  intro ε hε
  let w := realUnitBallVolume n
  have hw : 0 < w := realUnitBallVolume_pos hn
  have hcost : 0 < w * (δ / 2) ^ n :=
    pos_iff_ne_zero.mpr (mul_ne_zero hw.ne'
      (ENNReal.rpow_pos_of_nonneg (ENNReal.div_pos hδ.ne' (by norm_num)) hn).ne')
  have hsmall : (OuterMeasure.boundedBy
      (fun C : Set X => w * simonHausdorffCoverCost n ∞ C)) A <
      min ε (w * (δ / 2) ^ n) := by
    rw [← simonHausdorffContentOuter_eq_boundedBy, hzero]
    exact lt_min hε hcost
  rw [OuterMeasure.boundedBy_apply] at hsmall
  obtain ⟨C, hcover, hsum⟩ := (by simpa only [iInf_lt_iff] using hsmall)
  have hdiam : ∀ j, (C j).Nonempty → ediam (C j) < δ ∧ ediam (C j) < ∞ := by
    intro j hj
    have ht : w * simonHausdorffCoverCost n ∞ (C j) < min ε (w * (δ / 2) ^ n) :=
      ((le_iSup (fun _ : (C j).Nonempty => _) hj).trans
        (ENNReal.le_tsum (f := fun k => ⨆ _ : (C k).Nonempty,
          w * simonHausdorffCoverCost n ∞ (C k)) j)).trans_lt hsum
    have htop : ediam (C j) < ∞ := by
      by_contra hnot
      rw [simonHausdorffCoverCost_eq_top_of_not_ediam_lt n hnot, ENNReal.mul_top hw.ne'] at ht
      exact (ht.trans_le le_top).false
    refine ⟨?_, htop⟩
    by_contra hnot
    have hle : w * (δ / 2) ^ n ≤ w * simonHausdorffCoverCost n ∞ (C j) := by
      rw [simonHausdorffCoverCost_eq_of_ediam_lt n htop]
      gcongr
      exact le_of_not_gt hnot
    exact ((ht.trans_le (min_le_right _ _)).not_ge hle)
  calc
    simonHausdorffContentOuter n δ A ≤
        ∑' j, ⨆ _ : (C j).Nonempty, w * simonHausdorffCoverCost n δ (C j) := by
      rw [simonHausdorffContentOuter_eq_boundedBy, OuterMeasure.boundedBy_apply]
      exact iInf_le_of_le C (iInf_le_of_le hcover le_rfl)
    _ = ∑' j, ⨆ _ : (C j).Nonempty, w * simonHausdorffCoverCost n ∞ (C j) := by
      congr 1
      funext j
      apply iSup_congr
      intro hj
      rw [simonHausdorffCoverCost_eq_of_ediam_lt n (hdiam j hj).1,
        simonHausdorffCoverCost_eq_of_ediam_lt n (hdiam j hj).2]
    _ ≤ ε := (hsum.trans_le (min_le_left _ _)).le

/-- Zero infinite-scale content is equivalent to zero Hausdorff measure. -/
theorem simonHausdorff_eq_zero_iff_infinite_content_zero
    {n : ℝ} (hn : 0 ≤ n) (A : Set X) :
    simonHausdorffOuterMeasureReal n A = 0 ↔ simonHausdorffContentOuter n ∞ A = 0 := by
  constructor
  · intro hzero
    exact le_antisymm ((simonHausdorffContentOuter_le_hausdorff n (by simp) A).trans_eq hzero) bot_le
  · intro hzero
    rw [simonHausdorffOuterMeasureReal, OuterMeasure.iSup_apply]
    apply le_antisymm _ bot_le
    refine iSup_le fun δ => ?_
    rw [OuterMeasure.iSup_apply]
    exact iSup_le fun hδ => (simonHausdorffContentOuter_eq_zero_of_infinite_content_zero hn hzero hδ).le

/-- A uniform subcritical ball bound forces a small-diameter subset to
have zero infinite-scale content.  Enlarging a zero-diameter covering set
by positive radii handles dimension zero without a separate exception. -/
theorem infinite_content_eq_zero_of_uniform_ball_bound_of_small_diameter
    {n : ℝ} (hn : 0 ≤ n) {A B : Set X} (hBA : B ⊆ A)
    (hfin : simonHausdorffContentOuter n ∞ A < ∞)
    {t : ℝ≥0∞} (htfin : t ≠ ∞) (ht : t * (2 : ℝ≥0∞) ^ n < 1)
    {R : ℝ} (hR : 0 < R) (hdiam : ediam B < ENNReal.ofReal R)
    (hball : ∀ x ∈ B, ∀ r : ℝ, 0 < r → r < R →
      simonHausdorffContentOuter n ∞ (A ∩ closedBall x r) ≤
        t * (realUnitBallVolume n * ENNReal.ofReal r ^ n)) :
    simonHausdorffContentOuter n ∞ B = 0 := by
  let η : OuterMeasure X := simonHausdorffContentOuter n ∞
  let κ : ℝ≥0∞ := t * (2 : ℝ≥0∞) ^ n
  have hκfin : κ ≠ ∞ := ht.ne_top
  have hle : OuterMeasure.restrict B η ≤ κ • η := by
    rw [show κ • η = OuterMeasure.boundedBy
      (fun C : Set X => κ * (realUnitBallVolume n * simonHausdorffCoverCost n ∞ C)) by
        change κ • simonHausdorffContentOuter n ∞ = _
        rw [simonHausdorffContentOuter_eq_boundedBy, OuterMeasure.smul_boundedBy hκfin]
        rfl]
    apply OuterMeasure.le_boundedBy.mpr
    intro C
    rw [OuterMeasure.restrict_apply]
    rcases (C ∩ B).eq_empty_or_nonempty with hempty | hnonempty
    · simp only [hempty, measure_empty, zero_le]
    obtain ⟨x, hxC, hxB⟩ := hnonempty
    let D := C ∩ B
    have hDdiam : ediam D < ENNReal.ofReal R := (ediam_mono inter_subset_right).trans_lt hdiam
    have hDfin : ediam D ≠ ∞ := hDdiam.ne_top
    let d : ℝ := (ediam D).toReal
    have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
    have hd : ENNReal.ofReal d = ediam D := ENNReal.ofReal_toReal hDfin
    have hdR : d < R := (ENNReal.ofReal_lt_ofReal_iff hR).mp (hd.symm ▸ hDdiam)
    have hlim : Tendsto (fun r : ℝ => t * realUnitBallVolume n * ENNReal.ofReal r ^ n)
        (𝓝[>] d) (𝓝 (t * realUnitBallVolume n * ediam D ^ n)) := by
      have hpow : Tendsto (fun r : ℝ => ENNReal.ofReal r ^ n) (𝓝[>] d)
          (𝓝 (ENNReal.ofReal d ^ n)) :=
        ((ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).tendsto d).mono_left
          nhdsWithin_le_nhds
      simpa only [hd] using ENNReal.Tendsto.const_mul hpow
        (Or.inr (ENNReal.mul_ne_top htfin (realUnitBallVolume_ne_top n)))
    have hmass : η D ≤ t * realUnitBallVolume n * ediam D ^ n := by
      apply ge_of_tendsto hlim
      filter_upwards [Ioo_mem_nhdsGT hdR] with r hr
      have hr0 : 0 < r := hd0.trans_lt hr.1
      have hsub : D ⊆ A ∩ closedBall x r := by
        intro y hy
        refine ⟨hBA hy.2, ?_⟩
        rw [mem_closedBall]
        apply (ENNReal.ofReal_le_ofReal_iff hr0.le).mp
        rw [← edist_dist]
        exact (edist_le_ediam_of_mem hy (show x ∈ D from ⟨hxC, hxB⟩)).trans
          (hd ▸ ENNReal.ofReal_le_ofReal hr.1.le)
      exact ((η.mono hsub).trans (hball x hxB r hr0 hr.2)).trans_eq (mul_assoc _ _ _).symm
    have hcost : (ediam C / 2) ^ n ≤ simonHausdorffCoverCost n ∞ C := by
      by_cases hC : ediam C < ∞
      · rw [simonHausdorffCoverCost_eq_of_ediam_lt n hC]
      · rw [simonHausdorffCoverCost_eq_top_of_not_ediam_lt n hC]
        exact le_top
    calc
      η (C ∩ B) ≤ t * realUnitBallVolume n * ediam D ^ n := hmass
      _ ≤ t * realUnitBallVolume n * ediam C ^ n := by
        gcongr
        exact inter_subset_left
      _ = κ * (realUnitBallVolume n * (ediam C / 2) ^ n) := by
        nth_rw 1 [show ediam C = 2 * (ediam C / 2) by
          rw [mul_comm, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]]
        rw [ENNReal.mul_rpow_of_nonneg _ _ hn]
        dsimp only [κ]
        ac_rfl
      _ ≤ κ * (realUnitBallVolume n * simonHausdorffCoverCost n ∞ C) := by gcongr
  have hBB : η B ≤ κ * η B := by
    simpa only [OuterMeasure.restrict_apply, inter_self, smul_apply, smul_eq_mul] using hle B
  by_contra hne
  have hηBfin : η B ≠ ∞ := ((η.mono hBA).trans_lt hfin).ne
  have hlt := ENNReal.mul_lt_mul_left hne hηBfin ht
  rw [one_mul] at hlt
  exact hlt.not_ge hBB

/-- The uniform-radius subcritical set is Hausdorff-null.  Finite
content at the stated radius is enough to obtain the needed countable
small-diameter cover. -/
theorem hausdorff_eq_zero_of_uniform_content_ball_bound
    {n : ℝ} (hn : 0 ≤ n) {A B : Set X} (hBA : B ⊆ A)
    {R : ℝ} (hR : 0 < R)
    (hfin : simonHausdorffContentOuter n (ENNReal.ofReal R) A < ∞)
    {t : ℝ≥0∞} (htfin : t ≠ ∞) (ht : t * (2 : ℝ≥0∞) ^ n < 1)
    (hball : ∀ x ∈ B, ∀ r : ℝ, 0 < r → r < R →
      simonHausdorffContentOuter n ∞ (A ∩ closedBall x r) ≤
        t * (realUnitBallVolume n * ENNReal.ofReal r ^ n)) :
    simonHausdorffOuterMeasureReal n B = 0 := by
  obtain ⟨C, hcover, hdiam⟩ := exists_countable_small_diameter_cover_of_content_finite
    hn (ENNReal.ofReal_pos.mpr hR) hfin
  have hinftyfin : simonHausdorffContentOuter n ∞ A < ∞ :=
    (simonHausdorffContent_antitone n le_top A).trans_lt hfin
  apply measure_mono_null (t := ⋃ j, B ∩ C j)
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover (hBA hx))
    exact mem_iUnion.mpr ⟨j, hx, hj⟩
  · apply measure_iUnion_null
    intro j
    apply (simonHausdorff_eq_zero_iff_infinite_content_zero hn _).mpr
    exact infinite_content_eq_zero_of_uniform_ball_bound_of_small_diameter hn
      (inter_subset_left.trans hBA) hinftyfin htfin ht hR
      ((ediam_mono inter_subset_right).trans_lt (hdiam j))
      (fun x hx r hr hrR => hball x hx.1 r hr hrR)

/-- Simon (3.26)(2), in null-exceptional-set form.  In fact the covering
argument does not need the printed measurability assumption on `A`. -/
theorem simon_theorem_3_26_ii
    {n : ℝ} (hn : 0 ≤ n) {A : Set X}
    (_hA : IsCaratheodoryMeasurable (simonHausdorffOuterMeasureReal n) A)
    (hfin : ∀ δ : ℝ, 0 < δ → simonHausdorffContentOuter n (ENNReal.ofReal δ) A < ∞) :
    simonHausdorffOuterMeasureReal n {x | x ∈ A ∧
      dimensionalUpperDensity (simonHausdorffContentOuter n ∞) n A x < (2 : ℝ≥0∞) ^ (-n)} = 0 := by
  let E (q R : ℚ) : Set X := {x | x ∈ A ∧ ∀ r : ℝ, 0 < r → r < R →
    simonHausdorffContentOuter n ∞ (A ∩ closedBall x r) ≤
      (Real.toNNReal q : ℝ≥0∞) * (realUnitBallVolume n * ENNReal.ofReal r ^ n)}
  apply measure_mono_null (t := ⋃ (q : ℚ)
    (_ : (Real.toNNReal q : ℝ≥0∞) * (2 : ℝ≥0∞) ^ n < 1),
      ⋃ (R : ℚ) (_ : 0 < R), E q R)
  · intro x hx
    obtain ⟨q, _, hxq, hq⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hx.2
    have htwo0 : (2 : ℝ≥0∞) ^ n ≠ 0 :=
      (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
    have htwofin : (2 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hn (by norm_num)
    have hqmul : (Real.toNNReal q : ℝ≥0∞) * (2 : ℝ≥0∞) ^ n < 1 := by
      simpa only [ENNReal.rpow_neg, ENNReal.inv_mul_cancel htwo0 htwofin] using
        ENNReal.mul_lt_mul_left htwo0 htwofin hq
    obtain ⟨R, hR, hbound⟩ := nhdsGT_zero_basis_rat.mem_iff.mp
      (eventually_lt_of_limsup_lt hxq)
    refine mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hqmul, mem_iUnion.mpr
      ⟨R, mem_iUnion.mpr ⟨hR, hx.1, fun r hr hrR => ?_⟩⟩⟩⟩
    have hdiv : dimensionalDensityQuotient (simonHausdorffContentOuter n ∞) n A x r ≤
        (Real.toNNReal q : ℝ≥0∞) :=
      (show dimensionalDensityQuotient (simonHausdorffContentOuter n ∞) n A x r <
        (Real.toNNReal q : ℝ≥0∞) from hbound ⟨hr, hrR⟩).le
    exact (ENNReal.div_le_iff_le_mul (Or.inl (densityNormalization_ne_zero hn hr))
      (Or.inl (densityNormalization_ne_top hn))).mp hdiv
  · apply measure_iUnion_null
    intro q
    apply measure_iUnion_null
    intro hq
    apply measure_iUnion_null
    intro R
    apply measure_iUnion_null
    intro hR
    have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
    exact hausdorff_eq_zero_of_uniform_content_ball_bound hn (fun _ hx => hx.1)
      hRreal (hfin R hRreal) ENNReal.coe_ne_top hq (fun _ hx => hx.2)

/-- Increasing the numerator outer measure increases upper dimensional
density, independently of any measurability or finiteness conditions. -/
theorem dimensionalUpperDensity_mono_outerMeasure
    {μ ν : OuterMeasure X} (hμν : μ ≤ ν) (n : ℝ) (A : Set X) (x : X) :
    dimensionalUpperDensity μ n A x ≤ dimensionalUpperDensity ν n A x := by
  refine limsup_le_limsup ?_
  exact Eventually.of_forall fun r => ENNReal.div_le_div_right (hμν _) _

/-- The totally bounded special case mentioned parenthetically in
Simon (3.26)(2). -/
theorem simon_theorem_3_26_ii_of_totallyBounded
    {n : ℝ} (hn : 0 ≤ n) {A : Set X}
    (hA : IsCaratheodoryMeasurable (simonHausdorffOuterMeasureReal n) A)
    (hbounded : TotallyBounded A) :
    simonHausdorffOuterMeasureReal n {x | x ∈ A ∧
      dimensionalUpperDensity (simonHausdorffContentOuter n ∞) n A x < (2 : ℝ≥0∞) ^ (-n)} = 0 := by
  apply simon_theorem_3_26_ii hn hA
  intro δ hδ
  exact simonHausdorffContent_lt_top_of_totallyBounded hn (ENNReal.ofReal_pos.mpr hδ) hbounded

/-- The a.e. notation of the printed content-density lower bound. -/
theorem ae_hausdorff_content_dimensionalUpperDensity_ge_two_neg
    {n : ℝ} (hn : 0 ≤ n) {A : Set X}
    (hA : IsCaratheodoryMeasurable (simonHausdorffOuterMeasureReal n) A)
    (hfin : ∀ δ : ℝ, 0 < δ → simonHausdorffContentOuter n (ENNReal.ofReal δ) A < ∞) :
    ∀ᵐ x ∂simonHausdorffMeasureReal n, x ∈ A → (2 : ℝ≥0∞) ^ (-n) ≤
      dimensionalUpperDensity (simonHausdorffContentOuter n ∞) n A x := by
  rw [ae_iff]
  change (simonHausdorffMeasureReal n).toOuterMeasure _ = 0
  rw [simonHausdorffMeasureReal_toOuterMeasure hn]
  simpa only [not_imp, not_le] using simon_theorem_3_26_ii hn hA hfin

/-- Simon Remark (3.27): both sharp bounds for the upper density of a
finite Hausdorff-measurable set.  This is the mathematical consequence
asserted in the remark, not an extra density-existence claim. -/
theorem simon_remark_3_27
    {n : ℝ} (hn : 0 ≤ n) {A : Set X}
    (hA : IsCaratheodoryMeasurable (simonHausdorffOuterMeasureReal n) A)
    (hAfin : simonHausdorffOuterMeasureReal n A < ∞) :
    ∀ᵐ x ∂simonHausdorffMeasureReal n, x ∈ A →
      (2 : ℝ≥0∞) ^ (-n) ≤ dimensionalUpperDensity (simonHausdorffOuterMeasureReal n) n A x ∧
      dimensionalUpperDensity (simonHausdorffOuterMeasureReal n) n A x ≤ 1 := by
  have hfin : ∀ δ : ℝ, 0 < δ → simonHausdorffContentOuter n (ENNReal.ofReal δ) A < ∞ :=
    fun δ hδ => (simonHausdorffContentOuter_le_hausdorff n (ENNReal.ofReal_pos.mpr hδ) A).trans_lt hAfin
  filter_upwards [ae_hausdorff_dimensionalUpperDensity_le_one hn hA hAfin,
    ae_hausdorff_content_dimensionalUpperDensity_ge_two_neg hn hA hfin] with x hxupper hxlower hxA
  exact ⟨(hxlower hxA).trans (dimensionalUpperDensity_mono_outerMeasure
    (simonHausdorffContentOuter_le_hausdorff n (by simp)) n A x), hxupper hxA⟩

end Poincare.SimonGMT.Chapter01
