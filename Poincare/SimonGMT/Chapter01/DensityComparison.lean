module

public import Poincare.SimonGMT.Chapter01.Densities
public import Poincare.SimonGMT.Chapter01.Lusin

@[expose] public section

/-!
# Simon GMT, Chapter 1, the dimensional density comparison

The finite-tail argument below retains the sharp constant in (3.3).
Neither a doubling measure nor a separability hypothesis is used.
-/

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology Classical

namespace Poincare.SimonGMT.Chapter01

variable {X ι : Type*} [PseudoMetricSpace X]

/-- The finite-tail step in Simon's proof of (3.3).  A countable selected
family has finite total cost.  The enlarged balls are needed only on the
tail, so their fixed cost multiplier disappears in the limit. -/
theorem outerMeasure_le_tsum_of_fiveTimesCovering
    (η : OuterMeasure X) (A : Set X) (B D : Set ι) (c : ι → X) (r : ι → ℝ)
    (hD : D.Countable)
    (hfine : ∀ x ∈ A, ∀ ε > 0, ∃ i ∈ B,
      x ∈ closedBall (c i) (r i) ∧ diam (closedBall (c i) (r i)) < ε)
    (hcover : ∀ i ∈ B, ∃ j ∈ D,
      (closedBall (c i) (r i) ∩ closedBall (c j) (r j)).Nonempty ∧
      closedBall (c i) (r i) ⊆ closedBall (c j) (5 * r j))
    (w : D → ℝ≥0∞) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hsum : ∑' j, w j ≠ ∞)
    (hsmall : ∀ j : D, η (closedBall (c j) (r j)) ≤ w j)
    (hlarge : ∀ j : D, η (closedBall (c j) (5 * r j)) ≤ C * w j) :
    η A ≤ ∑' j, w j := by
  let : Countable D := hD.to_subtype
  have htail := ENNReal.tendsto_tsum_compl_atTop_zero hsum
  have hlim : Tendsto
      (fun F : Finset D => (∑' j, w j) + C * ∑' j : {j // j ∉ F}, w j)
      atTop (𝓝 (∑' j, w j)) := by
    simpa using tendsto_const_nhds.add (ENNReal.Tendsto.const_mul htail (Or.inr hC))
  apply ge_of_tendsto' hlim
  intro F
  let F' : Finset ι := F.image Subtype.val
  have hsub : A ⊆ (⋃ j ∈ F, closedBall (c j) (r j)) ∪
      ⋃ j : {j : D // j ∉ F}, closedBall (c j) (5 * r j) := by
    intro x hx
    by_cases hxF : x ∈ ⋃ j ∈ F, closedBall (c j) (r j)
    · exact Or.inl hxF
    · right
      have hxF' : x ∉ ⋃ j ∈ F', closedBall (c j) (r j) := by
        simpa only [F', Finset.mem_image, mem_iUnion, exists_prop,
          exists_exists_and_eq_and] using hxF
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp
        (fiveTimesCovering_finite_remainder A B D c r hfine hcover F' ⟨hx, hxF'⟩)
      have hjF : (⟨j, hj.1⟩ : D) ∉ F := by
        intro h
        exact hj.2 (Finset.mem_image.mpr ⟨⟨j, hj.1⟩, h, rfl⟩)
      exact mem_iUnion.mpr ⟨⟨⟨j, hj.1⟩, hjF⟩, hxj⟩
  calc
    η A ≤ η ((⋃ j ∈ F, closedBall (c j) (r j)) ∪
        ⋃ j : {j : D // j ∉ F}, closedBall (c j) (5 * r j)) := η.mono hsub
    _ ≤ η (⋃ j ∈ F, closedBall (c j) (r j)) +
        η (⋃ j : {j : D // j ∉ F}, closedBall (c j) (5 * r j)) := measure_union_le _ _
    _ ≤ (∑ j ∈ F, w j) + ∑' j : {j : D // j ∉ F}, C * w j := by
      apply add_le_add
      · exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun j _ => hsmall j)
      · exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => hlarge j)
    _ ≤ (∑' j, w j) + C * ∑' j : {j : D // j ∉ F}, w j := by
      rw [ENNReal.tsum_mul_left]
      exact add_le_add (ENNReal.sum_le_tsum F) le_rfl

/-- The extended diameter estimate, also valid for a pseudometric space. -/
theorem ediam_closedBall_le_twice_ofReal (x : X) (r : ℝ) :
    ediam (closedBall x r) ≤ 2 * ENNReal.ofReal r := by
  calc
    ediam (closedBall x r) ≤ ENNReal.ofReal (2 * r) :=
      ediam_le_of_forall_dist_le fun y hy z hz => by
        have hy' := mem_closedBall.mp hy
        have hz' := mem_closedBall.mp hz
        linarith [dist_triangle_right y z x]
    _ = 2 * ENNReal.ofReal r := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num

/-- At a positive radius the density normalization is strictly positive. -/
theorem densityNormalization_ne_zero {n r : ℝ} (hn : 0 ≤ n) (hr : 0 < r) :
    realUnitBallVolume n * ENNReal.ofReal r ^ n ≠ 0 :=
  mul_ne_zero (realUnitBallVolume_pos hn).ne'
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr) ENNReal.ofReal_ne_top).ne'

/-- At a positive radius the density normalization is finite. -/
theorem densityNormalization_ne_top {n r : ℝ} (hn : 0 ≤ n) :
    realUnitBallVolume n * ENNReal.ofReal r ^ n ≠ ∞ :=
  ENNReal.mul_ne_top (realUnitBallVolume_ne_top n)
    (ENNReal.rpow_ne_top_of_nonneg hn ENNReal.ofReal_ne_top)

/-- The ball selection directly from the upper density.  There is no
measurability hypothesis on either the test set or the set of centers. -/
theorem exists_small_ball_of_lt_dimensionalUpperDensity
    (μ : OuterMeasure X) {n : ℝ} (hn : 0 ≤ n) (A : Set X) (x : X)
    {τ : ℝ≥0∞} (hτ : τ < dimensionalUpperDensity μ n A x)
    {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Ioo 0 R,
      τ * (realUnitBallVolume n * ENNReal.ofReal r ^ n) ≤ μ (A ∩ closedBall x r) := by
  obtain ⟨r, hqr, hr⟩ :=
    ((frequently_lt_of_lt_limsup (by isBoundedDefault) hτ).and_eventually
      (Ioo_mem_nhdsGT hR)).exists
  refine ⟨r, hr, ?_⟩
  exact ((ENNReal.lt_div_iff_mul_lt (Or.inl (densityNormalization_ne_zero hn hr.1))
    (Or.inl (densityNormalization_ne_top hn))).mp hqr).le

/-- Density depends only on the test set in a neighborhood of its center. -/
theorem dimensionalUpperDensity_inter_of_mem_nhds
    (μ : OuterMeasure X) (n : ℝ) (A V : Set X) (x : X) (hV : V ∈ 𝓝 x) :
    dimensionalUpperDensity μ n (A ∩ V) x = dimensionalUpperDensity μ n A x := by
  obtain ⟨R, hR, hRV⟩ := nhds_basis_closedBall.mem_iff.mp hV
  apply Filter.limsup_congr
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  have hball : closedBall x r ⊆ V := (closedBall_subset_closedBall hr.2.le).trans hRV
  have hset : (A ∩ V) ∩ closedBall x r = A ∩ closedBall x r := by
    ext y
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hball h.2⟩, h.2⟩⟩
  simp only [dimensionalDensityQuotient, hset]

/-- Removing a closed set not containing the center leaves density
unchanged, as used in Simon's proof of (3.6). -/
theorem dimensionalUpperDensity_sdiff_of_isClosed
    (μ : OuterMeasure X) (n : ℝ) (A : Set X) {C : Set X} (hC : IsClosed C)
    {x : X} (hx : x ∉ C) :
    dimensionalUpperDensity μ n (A \ C) x = dimensionalUpperDensity μ n A x :=
  dimensionalUpperDensity_inter_of_mem_nhds μ n A Cᶜ x (hC.isOpen_compl.mem_nhds hx)

section Metric

variable {Y : Type*} [MetricSpace Y]

/-- The fixed-scale metric construction evaluated on a ball is bounded by
its radius cost whenever the ball satisfies that scale's diameter bound. -/
theorem hausdorffPre_closedBall_le {n : ℝ} (hn : 0 ≤ n) (x : Y) (r : ℝ)
    (δ : ℝ≥0∞) (hδ : 2 * ENNReal.ofReal r ≤ δ) :
    OuterMeasure.mkMetric'.pre
      (fun C : Set Y => realUnitBallVolume n * (ediam C / 2) ^ n) δ
      (closedBall x r) ≤ realUnitBallVolume n * ENNReal.ofReal r ^ n := by
  apply (OuterMeasure.mkMetric'.pre_le
    ((ediam_closedBall_le_twice_ofReal x r).trans hδ)).trans
  gcongr
  calc
    ediam (closedBall x r) / 2 ≤ (2 * ENNReal.ofReal r) / 2 :=
      ENNReal.div_le_div_right (ediam_closedBall_le_twice_ofReal x r) _
    _ = ENNReal.ofReal r := by
      rw [mul_comm, ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]

variable [MeasurableSpace Y] [BorelSpace Y]

/-- The sharp comparison at a strictly smaller density threshold, for a
finite Borel measure.  This intermediate statement needs no measurability
of the set of centers and no geometric assumption on the metric space. -/
theorem simonHausdorff_le_measure_univ_of_lt_upperDensity
    (ν : Measure Y) (hν : ν univ ≠ ∞) {n : ℝ} (hn : 0 ≤ n)
    (A : Set Y) {τ : ℝ≥0∞} (hτ0 : 0 < τ) (hτtop : τ ≠ ∞)
    (hden : ∀ x ∈ A, τ < dimensionalUpperDensity ν.toOuterMeasure n univ x) :
    simonHausdorffOuterMeasureReal n A ≤ ν univ / τ := by
  have hcost : simonHausdorffOuterMeasureReal (X := Y) n =
      OuterMeasure.mkMetric' (fun C : Set Y => realUnitBallVolume n * (ediam C / 2) ^ n) := by
    rw [simonHausdorffOuterMeasureReal_eq_smul_mkMetric,
      ← OuterMeasure.mkMetric_smul _ (realUnitBallVolume_ne_top n)
        (realUnitBallVolume_pos hn).ne']
    rfl
  rw [hcost, OuterMeasure.mkMetric', OuterMeasure.iSup_apply]
  refine iSup_le fun δ => ?_
  rw [OuterMeasure.iSup_apply]
  refine iSup_le fun hδ => ?_
  obtain ⟨R, _, hR0, hRδ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ
  have hR : 0 < R := ENNReal.ofReal_pos.mp hR0
  let B : Set (Y × ℝ) := {b | b.1 ∈ A ∧ 0 < b.2 ∧ b.2 < R / 10 ∧
    τ * (realUnitBallVolume n * ENNReal.ofReal b.2 ^ n) ≤ ν (closedBall b.1 b.2)}
  have hfine : ∀ x ∈ A, ∀ ε > 0, ∃ b ∈ B,
      x ∈ closedBall b.1 b.2 ∧ diam (closedBall b.1 b.2) < ε := by
    intro x hx ε hε
    obtain ⟨r, hr, hmass⟩ := exists_small_ball_of_lt_dimensionalUpperDensity
      ν.toOuterMeasure hn univ x (hden x hx)
      (lt_min (by positivity : 0 < R / 10) (half_pos hε))
    refine ⟨(x, r), ⟨hx, hr.1, hr.2.trans_le (min_le_left _ _), ?_⟩,
      mem_closedBall_self hr.1.le, ?_⟩
    · simpa only [univ_inter, Measure.toOuterMeasure_apply] using hmass
    · exact (diam_closedBall hr.1.le).trans_lt (by
        have := hr.2.trans_le (min_le_right _ _)
        linarith)
  obtain ⟨D, hDB, hdisj, hcover⟩ := exists_fiveTimesCovering B Prod.fst Prod.snd
    (fun b hb => hb.2.1.le) R (fun b hb =>
      (diam_closedBall hb.2.1.le).trans (by have := hb.2.2.1; linarith))
  have hdisj' : Pairwise (fun i j : D =>
      Disjoint (closedBall i.val.1 i.val.2) (closedBall j.val.1 j.val.2)) :=
    fun i j hij => hdisj i.property j.property (Subtype.coe_ne_coe.mpr hij)
  have hpos : ∀ b : D, 0 < ν (closedBall b.val.1 b.val.2) := by
    intro b
    have hb := hDB b.property
    exact (pos_iff_ne_zero.mpr (mul_ne_zero hτ0.ne'
      (densityNormalization_ne_zero hn hb.2.1))).trans_le hb.2.2.2
  have hcount := ν.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top
    (fun b : D => measurableSet_closedBall (x := b.val.1) (ε := b.val.2)) hdisj'
    (ne_top_of_le_ne_top hν (measure_mono (subset_univ _)))
  let : Countable D := countable_univ_iff.mp (by
    simpa only [hpos, ofPred_true] using hcount)
  let w : D → ℝ≥0∞ := fun b => realUnitBallVolume n * ENNReal.ofReal b.val.2 ^ n
  have hsum : (∑' b : D, w b) ≤ ν univ / τ := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hτ0.ne') (Or.inl hτtop)).mpr
    rw [mul_comm, ← ENNReal.tsum_mul_left]
    calc
      (∑' b : D, τ * w b) ≤ ∑' b : D, ν (closedBall b.val.1 b.val.2) :=
        ENNReal.tsum_le_tsum fun b => (hDB b.property).2.2.2
      _ = ν (⋃ b : D, closedBall b.val.1 b.val.2) :=
        (measure_iUnion hdisj' (fun _ => measurableSet_closedBall)).symm
      _ ≤ ν univ := measure_mono (subset_univ _)
  have hsumfin : ∑' b : D, w b ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.div_ne_top hν hτ0.ne') hsum
  refine le_trans (outerMeasure_le_tsum_of_fiveTimesCovering _ A B D Prod.fst Prod.snd
    (Set.to_countable D) hfine (fun b hb => ?_) w (5 ^ n) (by simp) hsumfin
    (fun b => ?_) (fun b => ?_)) hsum
  · obtain ⟨d, hd, hinter, _, hsub⟩ := hcover b hb
    exact ⟨d, hd, hinter, hsub⟩
  · apply hausdorffPre_closedBall_le hn
    calc
      2 * ENNReal.ofReal b.val.2 = ENNReal.ofReal (2 * b.val.2) := by
        rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
      _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal (by
        have := (hDB b.property).2.2.1
        linarith)
      _ ≤ δ := hRδ.le
  · have hbound : 2 * ENNReal.ofReal (5 * b.val.2) ≤ δ := by
      calc
        2 * ENNReal.ofReal (5 * b.val.2) = ENNReal.ofReal (10 * b.val.2) := by
          rw [show (10 : ℝ) * b.val.2 = 2 * (5 * b.val.2) by ring,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal (by
          have := (hDB b.property).2.2.1
          linarith)
        _ ≤ δ := hRδ.le
    apply (hausdorffPre_closedBall_le hn b.val.1 (5 * b.val.2) δ hbound).trans_eq
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ hn]
    norm_num only [ENNReal.ofReal_ofNat]
    exact mul_left_comm _ _ _

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- Sharp upper-density comparison for arbitrary test sets and centers.
Only Caratheodory measurability of Borel sets is needed.  In particular,
neither set is required to be measurable or to have finite mass.  The
threshold is allowed to be infinite as well as a nonnegative real. -/
theorem mul_simonHausdorff_le_of_le_dimensionalUpperDensity
    (μ : OuterMeasure Y) (hμ : borel Y ≤ μ.caratheodory)
    {n : ℝ} (hn : 0 ≤ n) (A₁ A₂ : Set Y) (t : ℝ≥0∞)
    (hden : ∀ x ∈ A₁, t ≤ dimensionalUpperDensity μ n A₂ x) :
    t * simonHausdorffOuterMeasureReal n A₁ ≤ μ A₂ := by
  by_cases hfin : μ A₂ = ∞
  · simp [hfin]
  let : MeasurableSpace Y := borel Y
  let : BorelSpace Y := ⟨rfl⟩
  let θ := OuterMeasure.restrict A₂ μ
  have hθ : borel Y ≤ θ.caratheodory := fun S hS =>
    isCaratheodoryMeasurable_restrict (hμ S hS)
  let ν : Measure Y := θ.toMeasure hθ
  have hνuniv : ν univ = μ A₂ := by
    rw [toMeasure_apply θ hθ MeasurableSet.univ]
    simp [θ, OuterMeasure.restrict_apply]
  have hνball : ∀ x r, ν (closedBall x r) = μ (A₂ ∩ closedBall x r) := by
    intro x r
    rw [toMeasure_apply θ hθ measurableSet_closedBall]
    simp only [θ, OuterMeasure.restrict_apply, inter_comm]
  have hνden : ∀ x, dimensionalUpperDensity ν.toOuterMeasure n univ x =
      dimensionalUpperDensity μ n A₂ x := by
    intro x
    unfold dimensionalUpperDensity
    congr 1
    funext r
    simp only [dimensionalDensityQuotient, univ_inter, Measure.toOuterMeasure_apply, hνball]
  conv_lhs => rw [← ENNReal.iSup_lt_eq_self t]
  simp only [ENNReal.iSup_mul]
  refine iSup_le fun τ => iSup_le fun hτ => ?_
  by_cases hτzero : τ = 0
  · simp [hτzero]
  have hbound := simonHausdorff_le_measure_univ_of_lt_upperDensity ν
    (hνuniv ▸ hfin) hn A₁ (pos_iff_ne_zero.mpr hτzero) hτ.ne_top
    (fun x hx => by rw [hνden]; exact hτ.trans_le (hden x hx))
  rw [hνuniv] at hbound
  exact (mul_comm _ _).le.trans
    ((ENNReal.le_div_iff_mul_le (Or.inl hτzero) (Or.inl hτ.ne_top)).mp hbound)

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- Simon Theorem (3.3), with the printed Borel regularity and nested-set
hypotheses.  The construction is the literal Gamma-normalized Hausdorff
outer measure in every real dimension `n ≥ 0`, including dimension zero. -/
theorem simon_theorem_3_3
    (μ : OuterMeasure Y) (hμ : IsBorelRegularOuterMeasure μ)
    {n : ℝ} (hn : 0 ≤ n) (A₁ A₂ : Set Y) (_hA : A₁ ⊆ A₂)
    {t : ℝ} (_ht : 0 ≤ t)
    (hden : ∀ x ∈ A₁, ENNReal.ofReal t ≤ dimensionalUpperDensity μ n A₂ x) :
    ENNReal.ofReal t * simonHausdorffOuterMeasureReal n A₁ ≤ μ A₂ :=
  mul_simonHausdorff_le_of_le_dimensionalUpperDensity μ hμ.borel_le_caratheodory
    hn A₁ A₂ _ hden

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- The threshold-level assertion in Simon's proof of (3.6).  The set is
measurable in the source's completed, Caratheodory sense. -/
theorem simonHausdorff_upperDensity_level_outside_eq_zero
    (μ : OuterMeasure Y) (hμ : IsBorelRegularOuterMeasure μ)
    {n : ℝ} (hn : 0 ≤ n) {A : Set Y}
    (hA : IsCaratheodoryMeasurable μ A) (hAfin : μ A < ∞)
    {t : ℝ≥0∞} (ht : 0 < t) :
    simonHausdorffOuterMeasureReal n
      {x | x ∉ A ∧ t ≤ dimensionalUpperDensity μ n A x} = 0 := by
  have hmul : t * simonHausdorffOuterMeasureReal n
      {x | x ∉ A ∧ t ≤ dimensionalUpperDensity μ n A x} = 0 := by
    apply le_antisymm _ bot_le
    apply le_of_forall_gt_imp_ge_of_dense
    intro ε hε
    obtain ⟨C, hCA, hCclosed, hCmass⟩ := hμ.exists_isClosed_sdiff_lt_of_finite
      (closedSetsAreGDelta_iff.mpr (fun _ h => h.isGδ)) hA hAfin hε.ne'
    apply le_trans (mul_simonHausdorff_le_of_le_dimensionalUpperDensity μ
      hμ.borel_le_caratheodory hn _ (A \ C) t (fun x hx => ?_)) hCmass.le
    rw [dimensionalUpperDensity_sdiff_of_isClosed μ n A hCclosed
      (fun hxC => hx.1 (hCA hxC))]
    exact hx.2
  exact (mul_eq_zero.mp hmul).resolve_left ht.ne'

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- Simon Theorem (3.6): a finite Caratheodory-measurable set has zero
upper density at Hausdorff-almost every point of its complement.  The
null exceptional-set formulation does not require an ambient measurable
space, local finiteness, separability, or measurability of the density. -/
theorem simon_theorem_3_6
    (μ : OuterMeasure Y) (hμ : IsBorelRegularOuterMeasure μ)
    {n : ℝ} (hn : 0 ≤ n) {A : Set Y}
    (hA : IsCaratheodoryMeasurable μ A) (hAfin : μ A < ∞) :
    simonHausdorffOuterMeasureReal n
      {x | x ∉ A ∧ dimensionalUpperDensity μ n A x ≠ 0} = 0 := by
  apply measure_mono_null (t := ⋃ k : ℕ,
    {x | x ∉ A ∧ (k : ℝ≥0∞)⁻¹ ≤ dimensionalUpperDensity μ n A x})
  · intro x hx
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hx.2
    exact mem_iUnion.mpr ⟨k, hx.1, hk.le⟩
  · apply measure_iUnion_null
    intro k
    exact simonHausdorff_upperDensity_level_outside_eq_zero μ hμ hn hA hAfin (by simp)

/-- The usual a.e. notation for the exact null-set conclusion (3.6). -/
theorem ae_dimensionalUpperDensity_eq_zero_outside
    (μ : OuterMeasure Y) (hμ : IsBorelRegularOuterMeasure μ)
    {n : ℝ} (hn : 0 ≤ n) {A : Set Y}
    (hA : IsCaratheodoryMeasurable μ A) (hAfin : μ A < ∞) :
    ∀ᵐ x ∂simonHausdorffMeasureReal n, x ∉ A → dimensionalUpperDensity μ n A x = 0 := by
  rw [ae_iff]
  change (simonHausdorffMeasureReal n).toOuterMeasure
    {x | ¬(x ∉ A → dimensionalUpperDensity μ n A x = 0)} = 0
  rw [simonHausdorffMeasureReal_toOuterMeasure hn]
  simpa only [not_imp] using simon_theorem_3_6 μ hμ hn hA hAfin

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- Simon Remark (3.7)(1), the important special case `μ = Hⁿ`, with the
literal Gamma normalization and the source's finite-measure hypothesis. -/
theorem simon_remark_3_7_hausdorff
    {n : ℝ} (hn : 0 ≤ n) {A : Set Y}
    (hA : IsCaratheodoryMeasurable (simonHausdorffOuterMeasureReal n) A)
    (hAfin : simonHausdorffOuterMeasureReal n A < ∞) :
    simonHausdorffOuterMeasureReal n
      {x | x ∉ A ∧ dimensionalUpperDensity (simonHausdorffOuterMeasureReal n) n A x ≠ 0} = 0 :=
  simon_theorem_3_6 _ (simonHausdorffOuterMeasureReal_isBorelRegular hn) hn hA hAfin

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- Simon Remark (3.7)(2): an open countable finite-measure cover removes
the assumption `μ A < ∞`.  The set `A` is still allowed to be merely
Caratheodory measurable, as in the source. -/
theorem simon_remark_3_7_of_openSigmaFinite
    (μ : OuterMeasure Y) (hμ : IsBorelRegularOuterMeasure μ)
    (hopen : IsOpenSigmaFinite μ) {n : ℝ} (hn : 0 ≤ n) {A : Set Y}
    (hA : IsCaratheodoryMeasurable μ A) :
    simonHausdorffOuterMeasureReal n
      {x | x ∉ A ∧ dimensionalUpperDensity μ n A x ≠ 0} = 0 := by
  let : MeasurableSpace Y := borel Y
  let : BorelSpace Y := ⟨rfl⟩
  obtain ⟨V, hV, hcover⟩ := (isOpenSigmaFinite_iff μ).mp hopen
  have hlocal : ∀ j : ℕ, simonHausdorffOuterMeasureReal n
      {x | x ∉ A ∩ V j ∧ dimensionalUpperDensity μ n (A ∩ V j) x ≠ 0} = 0 := by
    intro j
    apply simon_theorem_3_6 μ hμ hn
    · exact μ.isCaratheodory_inter hA (hμ.borel_le_caratheodory _ (hV j).1.measurableSet)
    · exact (μ.mono inter_subset_right).trans_lt (hV j).2
  apply measure_mono_null (t := ⋃ j : ℕ,
    {x | x ∉ A ∩ V j ∧ dimensionalUpperDensity μ n (A ∩ V j) x ≠ 0})
  · intro x hx
    have hxV : x ∈ ⋃ j, V j := hcover.symm ▸ mem_univ x
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxV
    refine mem_iUnion.mpr ⟨j, fun h => hx.1 h.1, ?_⟩
    rw [dimensionalUpperDensity_inter_of_mem_nhds μ n A (V j) x
      ((hV j).1.mem_nhds hxj)]
    exact hx.2
  · exact measure_iUnion_null hlocal

/-- The a.e. form of Simon Remark (3.7)(2). -/
theorem ae_dimensionalUpperDensity_eq_zero_outside_of_openSigmaFinite
    (μ : OuterMeasure Y) (hμ : IsBorelRegularOuterMeasure μ)
    (hopen : IsOpenSigmaFinite μ) {n : ℝ} (hn : 0 ≤ n) {A : Set Y}
    (hA : IsCaratheodoryMeasurable μ A) :
    ∀ᵐ x ∂simonHausdorffMeasureReal n, x ∉ A → dimensionalUpperDensity μ n A x = 0 := by
  rw [ae_iff]
  change (simonHausdorffMeasureReal n).toOuterMeasure
    {x | ¬(x ∉ A → dimensionalUpperDensity μ n A x = 0)} = 0
  rw [simonHausdorffMeasureReal_toOuterMeasure hn]
  simpa only [not_imp] using simon_remark_3_7_of_openSigmaFinite μ hμ hopen hn hA

end Metric

end Poincare.SimonGMT.Chapter01
