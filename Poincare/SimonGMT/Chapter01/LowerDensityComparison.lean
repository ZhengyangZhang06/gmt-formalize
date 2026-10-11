module

public import Poincare.SimonGMT.Chapter01.GeneralDensity

@[expose] public section

/-!
# Simon GMT, Chapter 1, the lower-density comparison theorem

A single covering argument proves both clauses of (3.21).  The covering
measure may be either the numerator or the reference measure; an auxiliary
absolutely continuous numerator handles the second clause directly.
-/

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology Classical

namespace Poincare.SimonGMT.Chapter01

variable {X : Type*} [MetricSpace X]

/-- Borel restrictions preserve Borel regularity without a finite-mass
assumption. -/
theorem IsBorelRegularOuterMeasure.restrict_borel
    {μ : OuterMeasure X} (hμ : IsBorelRegularOuterMeasure μ)
    {B : Set X} (hB : @MeasurableSet X (borel X) B) :
    IsBorelRegularOuterMeasure (OuterMeasure.restrict B μ) := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  have h := measure_toOuterMeasure_isBorelRegular (hμ.toBorelMeasure.restrict B)
  simpa only [Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict hB,
    hμ.toOuterMeasure_toBorelMeasure] using h

/-- Strict upper bounds on lower density supply arbitrarily small
comparison balls, including the zero-denominator case. -/
theorem exists_small_ball_of_outerRelativeLowerDensity_lt
    (μ ν : OuterMeasure X) (hopenν : IsOpenSigmaFinite ν)
    (x : X) {τ : ℝ≥0∞} (hτfin : τ ≠ ∞)
    (hτ : outerRelativeLowerDensity μ ν x < τ) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Ioo 0 R, μ (closedBall x r) ≤ τ * ν (closedBall x r) := by
  obtain ⟨r, hr⟩ := (((frequently_lt_of_liminf_lt (by isBoundedDefault) hτ).and_eventually
    (eventually_closedBall_measure_ne_top ν hopenν x)).and_eventually
      (Ioo_mem_nhdsGT hR)).exists
  exact ⟨r, hr.2, (ENNReal.div_le_iff_le_mul (Or.inr hτfin) (Or.inl hr.1.2)).mp hr.1.1.le⟩

/-- The open-superset estimate underlying both parts of Simon (3.21).
The auxiliary measure `σ` need only be dominated by the numerator and
absolutely continuous with respect to the covering measure `ρ`. -/
theorem lowerDensityComparison_open_superset
    (μ ν ρ σ : OuterMeasure X) (hν : IsBorelRegularOuterMeasure ν)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ρ)
    (hσle : σ ≤ μ) (hAC : ∀ S : Set X, ρ S = 0 → σ S = 0)
    (A : Set X) (hAfin : ρ A < ∞) (U : Set X) (hU : IsOpen U) (hAU : A ⊆ U)
    (τ : ℝ≥0∞) (hτfin : τ ≠ ∞)
    (hden : ∀ x ∈ A, outerRelativeLowerDensity μ ν x < τ) :
    σ A ≤ τ * ν U := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let B : Set (X × ℝ) := {b | b.1 ∈ A ∧ 0 < b.2 ∧ closedBall b.1 b.2 ⊆ U ∧
    μ (closedBall b.1 b.2) ≤ τ * ν (closedBall b.1 b.2)}
  have hfine : ∀ x ∈ A, ∀ ε > 0, ∃ r ∈ Ioo 0 ε, (x, r) ∈ B := by
    intro x hx ε hε
    obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds (hAU hx))
    obtain ⟨r, hr, hmass⟩ := exists_small_ball_of_outerRelativeLowerDensity_lt μ ν hopenν
      x hτfin (hden x hx) (lt_min hε hR)
    exact ⟨r, ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩, hx, hr.1,
      (closedBall_subset_closedBall (hr.2.trans_le (min_le_right _ _)).le).trans hRU, hmass⟩
  obtain ⟨D, hDB, hDcount, hDdisj, hDnull⟩ :=
    hV A hAfin B (fun b hb => ⟨hb.1, hb.2.1⟩) hfine
  let : Countable D := hDcount.to_subtype
  have hdisj : Pairwise (fun i j : D =>
      Disjoint (closedBall i.val.1 i.val.2) (closedBall j.val.1 j.val.2)) :=
    fun i j hij => hDdisj i.property j.property (Subtype.coe_ne_coe.mpr hij)
  have hsumν : (∑' b : D, ν (closedBall b.val.1 b.val.2)) =
      ν (⋃ b ∈ D, closedBall b.1 b.2) := by
    simpa only [hν.toBorelMeasure_apply_all, biUnion_eq_iUnion] using
      (measure_iUnion (μ := hν.toBorelMeasure) hdisj (fun _ => measurableSet_closedBall)).symm
  have hAcover : σ A ≤ σ (⋃ b ∈ D, closedBall b.1 b.2) := by
    have h := measure_le_inter_add_sdiff σ A (⋃ b ∈ D, closedBall b.1 b.2)
    rw [hAC _ hDnull, add_zero] at h
    exact h.trans (σ.mono inter_subset_right)
  calc
    σ A ≤ σ (⋃ b ∈ D, closedBall b.1 b.2) := hAcover
    _ ≤ ∑' b : D, σ (closedBall b.val.1 b.val.2) := by
      simpa only [biUnion_eq_iUnion] using
        measure_iUnion_le (μ := σ) (fun b : D => closedBall b.val.1 b.val.2)
    _ ≤ ∑' b : D, μ (closedBall b.val.1 b.val.2) := ENNReal.tsum_le_tsum fun b => hσle _
    _ ≤ ∑' b : D, τ * ν (closedBall b.val.1 b.val.2) :=
      ENNReal.tsum_le_tsum fun b => (hDB b.property).2.2.2
    _ = τ * ν (⋃ b ∈ D, closedBall b.1 b.2) := by rw [ENNReal.tsum_mul_left, hsumν]
    _ ≤ τ * ν U := by
      gcongr
      exact iUnion₂_subset fun b hb => (hDB hb).2.2.1

/-- The finite-covering-mass lower-density comparison. -/
theorem lowerDensityComparison_of_finite
    (μ ν ρ σ : OuterMeasure X) (hν : IsBorelRegularOuterMeasure ν)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ρ)
    (hσle : σ ≤ μ) (hAC : ∀ S : Set X, ρ S = 0 → σ S = 0)
    (A : Set X) (hAfin : ρ A < ∞) {t : ℝ} (ht : 0 < t)
    (hden : ∀ x ∈ A, outerRelativeLowerDensity μ ν x ≤ ENNReal.ofReal t) :
    σ A ≤ ENNReal.ofReal t * ν A := by
  have hbound : ∀ τ : ℝ, t < τ → σ A ≤ ENNReal.ofReal τ * ν A := by
    intro τ hτ
    have hτpos : 0 < τ := ht.trans hτ
    rw [hν.measure_eq_iInf_isOpen_of_closedSetsAreGDelta hopenν
      (closedSetsAreGDelta_iff.mpr (fun _ h => h.isGδ)) A]
    simp only [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.mpr hτpos).ne'
      ENNReal.ofReal_ne_top]
    refine le_iInf fun U => le_iInf fun hAU => le_iInf fun hU => ?_
    exact lowerDensityComparison_open_superset μ ν ρ σ hν hopenν hV hσle hAC A hAfin
      U hU hAU _ ENNReal.ofReal_ne_top (fun x hx =>
        (hden x hx).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hτpos).mpr hτ))
  have hlim : Tendsto (fun τ : ℝ => ENNReal.ofReal τ * ν A)
      (𝓝[>] t) (𝓝 (ENNReal.ofReal t * ν A)) :=
    ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal (tendsto_id.mono_left nhdsWithin_le_nhds))
      (Or.inl (ENNReal.ofReal_pos.mpr ht).ne')
  exact ge_of_tendsto hlim (eventually_nhdsWithin_iff.mpr (Eventually.of_forall hbound))

/-- The full lower-density comparison, with an arbitrary comparison set
and arbitrary mass. -/
theorem lowerDensityComparison
    (μ ν ρ σ : OuterMeasure X) (hν : IsBorelRegularOuterMeasure ν)
    (hρ : IsBorelRegularOuterMeasure ρ) (hσ : IsBorelRegularOuterMeasure σ)
    (hopenν : IsOpenSigmaFinite ν) (hopenρ : IsOpenSigmaFinite ρ)
    (hV : HasSymmetricVitaliProperty ρ)
    (hσle : σ ≤ μ) (hAC : ∀ S : Set X, ρ S = 0 → σ S = 0)
    (A : Set X) {t : ℝ} (ht : 0 < t)
    (hden : ∀ x ∈ A, outerRelativeLowerDensity μ ν x ≤ ENNReal.ofReal t) :
    σ A ≤ ENNReal.ofReal t * ν A := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let κ := hρ.toBorelMeasure
  let : SigmaFinite κ := hρ.toBorelMeasure_sigmaFinite hopenρ
  have hmono : Monotone (fun j => A ∩ spanningSets κ j) :=
    fun _ _ hij => inter_subset_inter_right _ (monotone_spanningSets κ hij)
  have hσeq : σ A = ⨆ j, σ (A ∩ spanningSets κ j) := by
    simpa only [← inter_iUnion, iUnion_spanningSets, inter_univ,
      hσ.toBorelMeasure_apply_all] using hmono.measure_iUnion (μ := hσ.toBorelMeasure)
  rw [hσeq]
  refine iSup_le fun j => ?_
  have hfin : ρ (A ∩ spanningSets κ j) < ∞ := by
    rw [← hρ.toBorelMeasure_apply_all]
    exact (measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top κ j)
  exact (lowerDensityComparison_of_finite μ ν ρ σ hν hopenν hV hσle hAC _ hfin ht
    (fun x hx => hden x hx.1)).trans (mul_le_mul_right (ν.mono inter_subset_left) _)

/-- Simon Theorem (3.21)(i), with precisely the printed positive threshold
and symmetric Vitali property for the numerator measure. -/
theorem simon_theorem_3_21_i
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty μ)
    (A : Set X) {t : ℝ} (ht : 0 < t)
    (hden : ∀ x ∈ A, outerRelativeLowerDensity μ ν x ≤ ENNReal.ofReal t) :
    μ A ≤ ENNReal.ofReal t * ν A :=
  lowerDensityComparison μ ν μ μ hν hμ hμ hopenν hopenμ hV le_rfl (fun _ h => h) A ht hden

/-- Simon Theorem (3.21)(ii), for any exceptional Borel set supplied by
Lemma (3.19).  The comparison set itself need not be measurable. -/
theorem simon_theorem_3_21_ii
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (_hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ν)
    {B : Set X} (hB : @MeasurableSet X (borel X) B) (_hνB : ν B = 0)
    (hAC : ∀ S : Set X, ν S = 0 → μ (S \ B) = 0)
    (A : Set X) {t : ℝ} (ht : 0 < t)
    (hden : ∀ x ∈ A, outerRelativeLowerDensity μ ν x ≤ ENNReal.ofReal t) :
    μ (A \ B) ≤ ENNReal.ofReal t * ν A := by
  have h := lowerDensityComparison μ ν ν (OuterMeasure.restrict Bᶜ μ)
    hν hν (hμ.restrict_borel hB.compl) hopenν hopenν hV
    (fun S => by
      rw [OuterMeasure.restrict_apply]
      exact measure_mono inter_subset_left)
    (fun S hS => by simpa only [OuterMeasure.restrict_apply, ← Set.sdiff_eq] using hAC S hS)
    A ht hden
  simpa only [OuterMeasure.restrict_apply, ← Set.sdiff_eq] using h

end Poincare.SimonGMT.Chapter01
