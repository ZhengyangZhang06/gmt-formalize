module

public import Poincare.SimonGMT.Chapter01.RelativeDensityComparison

@[expose] public section

/-!
# Simon GMT, Chapter 1, the general density theorem

The source's symmetric Vitali property and open sigma-finiteness suffice.
No separability, doubling condition, or Borel measurability of the test set
is imposed.  All quotients below use the literal outer measures.
-/

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology Classical

namespace Poincare.SimonGMT.Chapter01

variable {X : Type*} [MetricSpace X]

/-- A restriction quotient depends only on the restricting set near its
center. -/
theorem outerRelativeDensityQuotient_inter_eventuallyEq
    (μ ν : OuterMeasure X) (A V : Set X) (x : X) (hV : V ∈ 𝓝 x) :
    outerRelativeDensityQuotient (OuterMeasure.restrict (A ∩ V) μ) ν x =ᶠ[𝓝[>] (0 : ℝ)]
      outerRelativeDensityQuotient (OuterMeasure.restrict A μ) ν x := by
  obtain ⟨R, hR, hRV⟩ := nhds_basis_closedBall.mem_iff.mp hV
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  have hball : closedBall x r ⊆ V := (closedBall_subset_closedBall hr.2.le).trans hRV
  have hset : closedBall x r ∩ (A ∩ V) = closedBall x r ∩ A := by
    ext y
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hball h.1⟩⟩
  simp only [outerRelativeDensityQuotient, OuterMeasure.restrict_apply, hset]

/-- Open sigma-finiteness removes the finite-set hypothesis from the
general upper-density theorem, by localization in the numerator measure. -/
theorem outerRelativeUpperDensity_restrict_eq_zero_outside_of_openSigmaFinite
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ν)
    {A : Set X} (hA : IsCaratheodoryMeasurable μ A) :
    ν {x | x ∉ A ∧ outerRelativeUpperDensity (OuterMeasure.restrict A μ) ν x ≠ 0} = 0 := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  obtain ⟨U, hU, hcover⟩ := (isOpenSigmaFinite_iff μ).mp hopenμ
  have hlocal : ∀ j : ℕ, ν {x | x ∉ A ∩ U j ∧
      outerRelativeUpperDensity (OuterMeasure.restrict (A ∩ U j) μ) ν x ≠ 0} = 0 := by
    intro j
    exact simon_theorem_3_15 μ ν hμ hν hopenν hV
      (μ.isCaratheodory_inter hA (hμ.borel_le_caratheodory _ (hU j).1.measurableSet))
      ((μ.mono inter_subset_right).trans_lt (hU j).2)
  apply measure_mono_null (t := ⋃ j : ℕ, {x | x ∉ A ∩ U j ∧
    outerRelativeUpperDensity (OuterMeasure.restrict (A ∩ U j) μ) ν x ≠ 0})
  · intro x hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
    refine mem_iUnion.mpr ⟨j, fun h => hx.1 h.1, ?_⟩
    have heq := Filter.limsup_congr
      (outerRelativeDensityQuotient_inter_eventuallyEq μ ν A (U j) x
        ((hU j).1.mem_nhds hxj))
    exact heq.trans_ne hx.2
  · exact measure_iUnion_null hlocal

/-- Vanishing upper density is genuine convergence of the nonnegative
quotient, including the infinite values allowed by outer measures. -/
theorem tendsto_outerRelativeDensityQuotient_zero_of_upperDensity_zero
    (μ ν : OuterMeasure X) (x : X) (h : outerRelativeUpperDensity μ ν x = 0) :
    Tendsto (outerRelativeDensityQuotient μ ν x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_of_le_liminf_of_limsup_le bot_le h.le

/-- The localized general upper-density theorem in limit form. -/
theorem ae_tendsto_outerRelativeDensityQuotient_restrict_zero_outside
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ν)
    {A : Set X} (hA : IsCaratheodoryMeasurable μ A) :
    ∀ᵐ x ∂hν.toBorelMeasure, x ∉ A →
      Tendsto (outerRelativeDensityQuotient (OuterMeasure.restrict A μ) ν x)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hz : ∀ᵐ x ∂hν.toBorelMeasure,
      x ∉ A → outerRelativeUpperDensity (OuterMeasure.restrict A μ) ν x = 0 := by
    rw [ae_iff, hν.toBorelMeasure_apply_all]
    simpa only [not_imp] using
      outerRelativeUpperDensity_restrict_eq_zero_outside_of_openSigmaFinite
        μ ν hμ hν hopenμ hopenν hV hA
  filter_upwards [hz] with x hx hxa
  exact tendsto_outerRelativeDensityQuotient_zero_of_upperDensity_zero _ _ _ (hx hxa)

/-- Under open sigma-finiteness, small closed balls have finite measure
at every point; positivity holds outside the zero-ball region. -/
theorem eventually_closedBall_measure_ne_top
    (μ : OuterMeasure X) (hopen : IsOpenSigmaFinite μ) (x : X) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (closedBall x r) ≠ ∞ := by
  obtain ⟨U, hU, hcover⟩ := (isOpenSigmaFinite_iff μ).mp hopen
  obtain ⟨j, hxj⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp ((hU j).1.mem_nhds hxj)
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  exact ((μ.mono ((closedBall_subset_closedBall hr.2.le).trans hRU)).trans_lt (hU j).2).ne

/-- Simon Theorem (3.16).  The comparison set is allowed to be any
Caratheodory-measurable set, and may have infinite measure. -/
theorem simon_theorem_3_16
    (μ : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hopen : IsOpenSigmaFinite μ) (hV : HasSymmetricVitaliProperty μ)
    {A : Set X} (hA : IsCaratheodoryMeasurable μ A) :
    ∀ᵐ x ∂hμ.toBorelMeasure,
      Tendsto (fun r : ℝ => μ (A ∩ closedBall x r) / μ (closedBall x r))
        (𝓝[>] (0 : ℝ)) (𝓝 (A.indicator (fun _ => (1 : ℝ≥0∞)) x)) := by
  have hzero : ∀ᵐ x ∂hμ.toBorelMeasure, x ∉ zeroBallRegion μ := by
    rw [ae_iff, hμ.toBorelMeasure_apply_all]
    simpa only [not_not, ofPred_mem_eq] using hV.zeroBallRegion_eq_zero_of_openSigmaFinite hopen
  filter_upwards [hzero,
    ae_tendsto_outerRelativeDensityQuotient_restrict_zero_outside μ μ hμ hμ hopen hopen hV hA,
    ae_tendsto_outerRelativeDensityQuotient_restrict_zero_outside μ μ hμ hμ hopen hopen hV
      hA.compl] with x hxzero hxA hxAc
  by_cases hx : x ∈ A
  · simp only [indicator_of_mem hx]
    have ht := (ENNReal.continuous_sub_left (a := 1) (by simp)).continuousAt.tendsto.comp
      (hxAc (by simpa using hx))
    simp only [tsub_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_closedBall_measure_ne_top μ hopen x,
      self_mem_nhdsWithin] with r hrfin hrpos
    have hrzero : μ (closedBall x r) ≠ 0 := fun h => hxzero ⟨r, hrpos, h⟩
    have hadd : μ (A ∩ closedBall x r) / μ (closedBall x r) +
        outerRelativeDensityQuotient (OuterMeasure.restrict Aᶜ μ) μ x r = 1 := by
      simp only [outerRelativeDensityQuotient, OuterMeasure.restrict_apply,
        inter_comm A (closedBall x r), ← ENNReal.add_div]
      rw [← Set.sdiff_eq, ← hA (closedBall x r), ENNReal.div_self hrzero hrfin]
    exact (ENNReal.eq_sub_of_add_eq' (by simp) hadd).symm
  · simp only [indicator_of_notMem hx]
    convert hxA hx using 1
    ext r
    simp only [outerRelativeDensityQuotient, OuterMeasure.restrict_apply, inter_comm]

end Poincare.SimonGMT.Chapter01
