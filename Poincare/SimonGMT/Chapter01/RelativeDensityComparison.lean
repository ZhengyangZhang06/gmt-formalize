module

public import Poincare.SimonGMT.Chapter01.SymmetricVitali

@[expose] public section

/-!
# Simon GMT, Chapter 1, the general density comparison

The comparison below uses Simon's symmetric Vitali property, not a
doubling or separability substitute.  All set evaluations are outer-measure
evaluations, including evaluations on nonmeasurable comparison sets.
-/

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology Classical

namespace Poincare.SimonGMT.Chapter01

variable {X : Type*} [MetricSpace X]

/-- A strict upper-density bound supplies arbitrarily small comparison
balls.  ENNReal's zero-denominator convention is retained; the inequality
after multiplication remains valid even when the denominator is zero. -/
theorem exists_small_ball_of_lt_outerRelativeUpperDensity
    (μ ν : OuterMeasure X) (x : X) {τ : ℝ≥0∞}
    (hτ : τ < outerRelativeUpperDensity μ ν x) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Ioo 0 R, τ * ν (closedBall x r) ≤ μ (closedBall x r) := by
  obtain ⟨r, hqr, hr⟩ :=
    ((frequently_lt_of_lt_limsup (by isBoundedDefault) hτ).and_eventually
      (Ioo_mem_nhdsGT hR)).exists
  exact ⟨r, hr, ENNReal.mul_le_of_le_div hqr.le⟩

/-- The open-superset estimate in the proof of Simon (3.13), for a
comparison set of finite reference mass.  No measurability of `A` is used. -/
theorem relativeDensityComparison_open_superset
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hV : HasSymmetricVitaliProperty ν)
    (A : Set X) (hAfin : ν A < ∞) (U : Set X) (hU : IsOpen U) (hAU : A ⊆ U)
    (τ : ℝ≥0∞) (hden : ∀ x ∈ A, τ < outerRelativeUpperDensity μ ν x) :
    τ * ν A ≤ μ U := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let B : Set (X × ℝ) := {b | b.1 ∈ A ∧ 0 < b.2 ∧
    closedBall b.1 b.2 ⊆ U ∧ τ * ν (closedBall b.1 b.2) ≤ μ (closedBall b.1 b.2)}
  have hfine : ∀ x ∈ A, ∀ ε > 0, ∃ r ∈ Ioo 0 ε, (x, r) ∈ B := by
    intro x hx ε hε
    obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds (hAU hx))
    obtain ⟨r, hr, hmass⟩ := exists_small_ball_of_lt_outerRelativeUpperDensity
      μ ν x (hden x hx) (lt_min hε hR)
    exact ⟨r, ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩, hx, hr.1,
      (closedBall_subset_closedBall (hr.2.trans_le (min_le_right _ _)).le).trans hRU,
      hmass⟩
  obtain ⟨D, hDB, hDcount, hDdisj, hDnull⟩ :=
    hV A hAfin B (fun b hb => ⟨hb.1, hb.2.1⟩) hfine
  let : Countable D := hDcount.to_subtype
  have hdisj : Pairwise (fun i j : D =>
      Disjoint (closedBall i.val.1 i.val.2) (closedBall j.val.1 j.val.2)) :=
    fun i j hij => hDdisj i.property j.property (Subtype.coe_ne_coe.mpr hij)
  have hsumμ : (∑' b : D, μ (closedBall b.val.1 b.val.2)) =
      μ (⋃ b ∈ D, closedBall b.1 b.2) := by
    simpa only [hμ.toBorelMeasure_apply_all, biUnion_eq_iUnion] using
      (measure_iUnion (μ := hμ.toBorelMeasure) hdisj (fun _ => measurableSet_closedBall)).symm
  have hsumν : (∑' b : D, ν (closedBall b.val.1 b.val.2)) =
      ν (⋃ b ∈ D, closedBall b.1 b.2) := by
    simpa only [hν.toBorelMeasure_apply_all, biUnion_eq_iUnion] using
      (measure_iUnion (μ := hν.toBorelMeasure) hdisj (fun _ => measurableSet_closedBall)).symm
  have hAcover : ν A ≤ ν (⋃ b ∈ D, closedBall b.1 b.2) := by
    have h := measure_le_inter_add_sdiff ν A (⋃ b ∈ D, closedBall b.1 b.2)
    rw [hDnull, add_zero] at h
    exact h.trans (ν.mono inter_subset_right)
  calc
    τ * ν A ≤ τ * ν (⋃ b ∈ D, closedBall b.1 b.2) := by gcongr
    _ = ∑' b : D, τ * ν (closedBall b.val.1 b.val.2) := by
      rw [← hsumν, ENNReal.tsum_mul_left]
    _ ≤ ∑' b : D, μ (closedBall b.val.1 b.val.2) :=
      ENNReal.tsum_le_tsum fun b => (hDB b.property).2.2.2
    _ = μ (⋃ b ∈ D, closedBall b.1 b.2) := hsumμ
    _ ≤ μ U := μ.mono (iUnion₂_subset fun b hb => (hDB hb).2.2.1)

/-- Simon's general comparison for a finite-reference-mass set.  The
threshold is allowed to be infinite; zero and infinity use the literal
extended-real conventions. -/
theorem relativeDensityComparison_of_finite
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hV : HasSymmetricVitaliProperty ν) (A : Set X) (hAfin : ν A < ∞)
    (t : ℝ≥0∞) (hden : ∀ x ∈ A, t ≤ outerRelativeUpperDensity μ ν x) :
    t * ν A ≤ μ A := by
  conv_lhs => rw [← ENNReal.iSup_lt_eq_self t]
  simp only [ENNReal.iSup_mul]
  refine iSup_le fun τ => iSup_le fun hτ => ?_
  rw [hμ.measure_eq_iInf_isOpen_of_closedSetsAreGDelta hopenμ
    (closedSetsAreGDelta_iff.mpr (fun _ h => h.isGδ)) A]
  refine le_iInf fun U => le_iInf fun hAU => le_iInf fun hU => ?_
  exact relativeDensityComparison_open_superset μ ν hμ hν hV A hAfin U hU hAU τ
    (fun x hx => hτ.trans_le (hden x hx))

/-- Simon (3.13), strengthened only by allowing an infinite threshold.
The arbitrary comparison set is exhausted by finite-reference-mass pieces,
so neither global finiteness nor measurability of that set is assumed. -/
theorem mul_measure_le_of_le_outerRelativeUpperDensity
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ν)
    (A : Set X) (t : ℝ≥0∞) (hden : ∀ x ∈ A, t ≤ outerRelativeUpperDensity μ ν x) :
    t * ν A ≤ μ A := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let ρ := hν.toBorelMeasure
  let : SigmaFinite ρ := hν.toBorelMeasure_sigmaFinite hopenν
  have hmono : Monotone (fun j => A ∩ spanningSets ρ j) :=
    fun _ _ hij => inter_subset_inter_right _ (monotone_spanningSets ρ hij)
  have hνeq : ν A = ⨆ j, ν (A ∩ spanningSets ρ j) := by
    simpa only [← inter_iUnion, iUnion_spanningSets, inter_univ, ρ,
      hν.toBorelMeasure_apply_all] using hmono.measure_iUnion (μ := ρ)
  rw [hνeq, ENNReal.mul_iSup]
  refine iSup_le fun j => ?_
  have hfinite : ν (A ∩ spanningSets ρ j) < ∞ := by
    rw [← hν.toBorelMeasure_apply_all]
    exact (measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top ρ j)
  exact (relativeDensityComparison_of_finite μ ν hμ hν hopenμ hV _ hfinite t
    (fun x hx => hden x hx.1)).trans (μ.mono inter_subset_left)

/-- Simon Theorem (3.13), with the printed hypotheses and real threshold. -/
theorem simon_theorem_3_13
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ν)
    (A : Set X) {t : ℝ} (_ht : 0 ≤ t)
    (hden : ∀ x ∈ A, ENNReal.ofReal t ≤ outerRelativeUpperDensity μ ν x) :
    ENNReal.ofReal t * ν A ≤ μ A :=
  mul_measure_le_of_le_outerRelativeUpperDensity μ ν hμ hν hopenμ hopenν hV A _ hden

/-- Simon Corollary (3.14): the relative upper density is finite outside a
reference-null set.  Both measures need only be open sigma-finite. -/
theorem simon_corollary_3_14
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ν) :
    ν {x | outerRelativeUpperDensity μ ν x = ∞} = 0 := by
  obtain ⟨U, hU, hcover⟩ := (isOpenSigmaFinite_iff μ).mp hopenμ
  have hlocal : ∀ j : ℕ, ν ({x | outerRelativeUpperDensity μ ν x = ∞} ∩ U j) = 0 := by
    intro j
    have hbound := mul_measure_le_of_le_outerRelativeUpperDensity μ ν hμ hν hopenμ
      hopenν hV ({x | outerRelativeUpperDensity μ ν x = ∞} ∩ U j) ∞
      (fun x hx => le_of_eq hx.1.symm)
    by_contra hz
    rw [ENNReal.top_mul hz] at hbound
    exact (not_le_of_gt ((μ.mono inter_subset_right).trans_lt (hU j).2)) hbound
  have heq : {x | outerRelativeUpperDensity μ ν x = ∞} =
      ⋃ j, {x | outerRelativeUpperDensity μ ν x = ∞} ∩ U j := by
    rw [← inter_iUnion, hcover, inter_univ]
  rw [heq]
  exact measure_iUnion_null hlocal

/-- The a.e. formulation of Simon (3.14), for the source outer measure's
canonical Borel measure, which agrees on all sets. -/
theorem ae_outerRelativeUpperDensity_lt_top
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ν) :
    ∀ᵐ x ∂hν.toBorelMeasure, outerRelativeUpperDensity μ ν x < ∞ := by
  rw [ae_iff, hν.toBorelMeasure_apply_all]
  simpa only [not_lt, top_le_iff] using simon_corollary_3_14 μ ν hμ hν hopenμ hopenν hV

/-- A finite outer measure has the source's open sigma-finite property. -/
theorem isOpenSigmaFinite_of_univ_lt_top (μ : OuterMeasure X) (hμ : μ univ < ∞) :
    IsOpenSigmaFinite μ :=
  (isOpenSigmaFinite_iff μ).mpr ⟨fun _ => univ, fun _ => ⟨isOpen_univ, hμ⟩,
    iUnion_const univ⟩

/-- A comparison consequence used in Simon (3.15): on a set of zero
numerator mass, positive upper relative density occurs only on a
reference-null subset.  The comparison set need not be measurable. -/
theorem measure_pos_outerRelativeUpperDensity_inter_eq_zero
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ν)
    (A : Set X) (hA : μ A = 0) :
    ν {x | x ∈ A ∧ outerRelativeUpperDensity μ ν x ≠ 0} = 0 := by
  have hlevel : ∀ t : ℝ≥0∞, 0 < t →
      ν {x | x ∈ A ∧ t ≤ outerRelativeUpperDensity μ ν x} = 0 := by
    intro t ht
    have hbound := mul_measure_le_of_le_outerRelativeUpperDensity μ ν hμ hν hopenμ
      hopenν hV {x | x ∈ A ∧ t ≤ outerRelativeUpperDensity μ ν x} t (fun _ hx => hx.2)
    have hzero : μ {x | x ∈ A ∧ t ≤ outerRelativeUpperDensity μ ν x} = 0 :=
      measure_mono_null (fun _ hx => hx.1) hA
    rw [hzero] at hbound
    exact (mul_eq_zero.mp (nonpos_iff_eq_zero.mp hbound)).resolve_left ht.ne'
  apply measure_mono_null (t := ⋃ k : ℕ,
    {x | x ∈ A ∧ (k : ℝ≥0∞)⁻¹ ≤ outerRelativeUpperDensity μ ν x})
  · intro x hx
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hx.2
    exact mem_iUnion.mpr ⟨k, hx.1, hk.le⟩
  · exact measure_iUnion_null fun k => hlevel _ (by simp)

/-- Simon Theorem (3.15), the general upper density theorem, with the
printed finite mass only on `A`, and open sigma-finiteness only on the
reference measure.  No measurability beyond Caratheodory measurability of
`A` and no doubling assumption is imposed. -/
theorem simon_theorem_3_15
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenν : IsOpenSigmaFinite ν)
    (hV : HasSymmetricVitaliProperty ν) {A : Set X}
    (hA : IsCaratheodoryMeasurable μ A) (hAfin : μ A < ∞) :
    ν {x | x ∉ A ∧ outerRelativeUpperDensity (OuterMeasure.restrict A μ) ν x ≠ 0} = 0 := by
  let ρ := OuterMeasure.restrict A μ
  have hρ : IsBorelRegularOuterMeasure ρ := hμ.restrict hA hAfin
  have hopenρ : IsOpenSigmaFinite ρ := isOpenSigmaFinite_of_univ_lt_top ρ (by
    simpa only [ρ, OuterMeasure.restrict_apply, univ_inter] using hAfin)
  have hρAc : ρ Aᶜ = 0 := by simp [ρ, OuterMeasure.restrict_apply]
  exact measure_pos_outerRelativeUpperDensity_inter_eq_zero ρ ν hρ hν hopenρ hopenν hV Aᶜ hρAc

/-- The a.e. form of Simon's general upper density theorem (3.15). -/
theorem ae_outerRelativeUpperDensity_restrict_eq_zero_outside
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenν : IsOpenSigmaFinite ν)
    (hV : HasSymmetricVitaliProperty ν) {A : Set X}
    (hA : IsCaratheodoryMeasurable μ A) (hAfin : μ A < ∞) :
    ∀ᵐ x ∂hν.toBorelMeasure,
      x ∉ A → outerRelativeUpperDensity (OuterMeasure.restrict A μ) ν x = 0 := by
  rw [ae_iff, hν.toBorelMeasure_apply_all]
  simpa only [not_imp] using simon_theorem_3_15 μ ν hμ hν hopenν hV hA hAfin

end Poincare.SimonGMT.Chapter01
