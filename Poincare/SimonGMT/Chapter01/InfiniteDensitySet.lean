module

public import Poincare.SimonGMT.Chapter01.RadonNikodymTheorem

@[expose] public section

/-!
# Borel measurability of the literal infinite-density set

This supplements Simon (3.24)(iii) with the Borel property of its specified
singular set.  Rational radii suffice because the quotient is right
continuous wherever the numerator is nonzero and the two ball masses
are locally finite.  No countability assumption on the metric space is
used.
-/

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology Classical

namespace Poincare.SimonGMT.Chapter01

variable {X : Type*} [MetricSpace X]

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

/-- Closed-ball mass is Borel measurable for an s-finite measure, without
second countability of the metric space. -/
theorem measurable_closedBall_mass_of_sFinite (μ : Measure X) [SFinite μ] (r : ℝ) :
    Measurable (fun x => μ (closedBall x r)) := by
  have heq : (fun x => μ (closedBall x r)) =
      (fun x => ∑' j : ℕ, sfiniteSeq μ j (closedBall x r)) := by
    funext x
    calc
      μ (closedBall x r) = (Measure.sum (sfiniteSeq μ)) (closedBall x r) :=
        congrArg (fun η : Measure X => η (closedBall x r)) (sum_sfiniteSeq μ).symm
      _ = _ := Measure.sum_apply _ measurableSet_closedBall
  rw [heq]
  exact Measurable.tsum fun j =>
    (upperSemicontinuous_measure_closedBall (sfiniteSeq μ j)
      (fun _ _ => measure_ne_top _ _) r).measurable

/-- The relative quotient at a fixed radius is Borel measurable. -/
theorem measurable_outerRelativeDensityQuotient
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (r : ℝ) :
    Measurable (fun x => outerRelativeDensityQuotient μ ν x r) := by
  let : SigmaFinite hμ.toBorelMeasure := hμ.toBorelMeasure_sigmaFinite hopenμ
  let : SigmaFinite hν.toBorelMeasure := hν.toBorelMeasure_sigmaFinite hopenν
  have hm := (measurable_closedBall_mass_of_sFinite hμ.toBorelMeasure r).div
    (measurable_closedBall_mass_of_sFinite hν.toBorelMeasure r)
  change Measurable (fun x => hμ.toBorelMeasure (closedBall x r) /
    hν.toBorelMeasure (closedBall x r)) at hm
  simpa only [outerRelativeDensityQuotient, hμ.toBorelMeasure_apply_all,
    hν.toBorelMeasure_apply_all] using hm

/-- Right continuity of the quotient at a positive-numerator radius,
assuming just a larger finite ball for each of the two measures. -/
theorem tendsto_outerRelativeDensityQuotient_right_of_finite_ball
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (x : X) {r R : ℝ} (hrR : r < R)
    (hμR : μ (closedBall x R) ≠ ∞) (hνR : ν (closedBall x R) ≠ ∞)
    (hμr : μ (closedBall x r) ≠ 0) :
    Tendsto (outerRelativeDensityQuotient μ ν x) (𝓝[>] r)
      (𝓝 (outerRelativeDensityQuotient μ ν x r)) := by
  have hright (η : OuterMeasure X) (hη : IsBorelRegularOuterMeasure η)
      (hηR : η (closedBall x R) ≠ ∞) :
      Tendsto (fun s => η (closedBall x s)) (𝓝[>] r) (𝓝 (η (closedBall x r))) := by
    simpa only [Function.comp_def, biInter_gt_closedBall, hη.toBorelMeasure_apply_all] using
      (tendsto_measure_biInter_gt (μ := hη.toBorelMeasure) (a := r) (s := closedBall x)
        (fun _ _ => measurableSet_closedBall.nullMeasurableSet)
        (fun _ _ _ hij => closedBall_subset_closedBall hij)
        ⟨R, hrR, by simpa only [hη.toBorelMeasure_apply_all] using hηR⟩)
  exact ENNReal.Tendsto.div (hright μ hμ hμR) (Or.inl hμr) (hright ν hν hνR)
    (Or.inl (ne_top_of_le_ne_top hνR (ν.mono (closedBall_subset_closedBall hrR.le))))

/-- This set uses precisely the common-value convention of (3.22). -/
theorem mem_outerInfiniteDensitySet_iff_density_eq_top
    (μ ν : OuterMeasure X) (x : X) :
    x ∈ outerInfiniteDensitySet μ ν ↔
      outerRelativeLowerDensity μ ν x = ∞ ∧ outerRelativeUpperDensity μ ν x = ∞ := by
  constructor
  · intro hx
    exact ⟨hx.liminf_eq, hx.limsup_eq⟩
  · rintro ⟨hi, hs⟩
    exact tendsto_of_liminf_eq_limsup hi hs

/-- A countable-radii characterization uses the full density limit, not
merely its value on a single predetermined sequence of radii. -/
theorem mem_outerInfiniteDensitySet_iff_rational
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (x : X) :
    x ∈ outerInfiniteDensitySet μ ν ↔ x ∉ zeroBallRegion μ ∧
      ∀ n : ℕ, ∃ δ : ℚ, 0 < δ ∧ ∀ q : ℚ, 0 < q → q < δ →
        (n : ℝ≥0∞) < outerRelativeDensityQuotient μ ν x (q : ℝ) := by
  constructor
  · intro hx
    refine ⟨fun hz => ?_, fun n => ?_⟩
    · have hlim := tendsto_outerRelativeDensityQuotient_zero μ ν hz
      have heq : (0 : ℝ≥0∞) = ∞ := tendsto_nhds_unique hlim hx
      exact ENNReal.zero_ne_top heq
    · obtain ⟨δ, hδ, hbound⟩ := nhdsGT_zero_basis_rat.mem_iff.mp
        ((ENNReal.tendsto_nhds_top_iff_nat.mp hx) n)
      exact ⟨δ, hδ, fun q hq hqδ => hbound ⟨by exact_mod_cast hq, by exact_mod_cast hqδ⟩⟩
  · rintro ⟨hxzero, hrat⟩
    change Tendsto _ _ (𝓝 ∞)
    apply ENNReal.tendsto_nhds_top
    intro n
    obtain ⟨δ, hδ, hbound⟩ := hrat (n + 1)
    obtain ⟨R, hμRfin, hνRfin, hRpos⟩ :=
      ((eventually_closedBall_measure_ne_top μ hopenμ x).and
        ((eventually_closedBall_measure_ne_top ν hopenν x).and self_mem_nhdsWithin)).exists
    have hδpos : (0 : ℝ) < δ := by exact_mod_cast hδ
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδpos hRpos)] with r hr
    have hrδ : r < (δ : ℝ) := hr.2.trans_le (min_le_left _ _)
    have hrR : r < R := hr.2.trans_le (min_le_right _ _)
    have hright := tendsto_outerRelativeDensityQuotient_right_of_finite_ball
      μ ν hμ hν x hrR hμRfin hνRfin (fun hz => hxzero ⟨r, hr.1, hz⟩)
    obtain ⟨q, _, hq, htq⟩ := DenseRange.exists_seq_strictAnti_tendsto_of_lt
      (Rat.denseRange_cast : DenseRange (fun q : ℚ => (q : ℝ))) Rat.cast_mono hrδ
    have hqt : Tendsto (fun j => (q j : ℝ)) atTop (𝓝[>] r) :=
      tendsto_nhdsWithin_iff.mpr ⟨htq, Eventually.of_forall fun j => (hq j).1⟩
    have hle : ((n + 1 : ℕ) : ℝ≥0∞) ≤ outerRelativeDensityQuotient μ ν x r :=
      ge_of_tendsto (hright.comp hqt) (Eventually.of_forall fun j =>
        (hbound (q j) (by exact_mod_cast hr.1.trans (hq j).1)
          (by exact_mod_cast (hq j).2)).le)
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hle

/-- The literal infinite-density set is Borel, including points in the
exceptional zero-ball regions of the source's definition. -/
theorem measurableSet_outerInfiniteDensitySet
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) :
    MeasurableSet (outerInfiniteDensitySet μ ν) := by
  have heq : outerInfiniteDensitySet μ ν = (zeroBallRegion μ)ᶜ ∩
      ⋂ n : ℕ, ⋃ δ : ℚ, ⋃ (_ : 0 < δ), ⋂ q : ℚ, ⋂ (_ : 0 < q), ⋂ (_ : q < δ),
        {x | (n : ℝ≥0∞) < outerRelativeDensityQuotient μ ν x (q : ℝ)} := by
    ext x
    simpa only [mem_inter_iff, mem_compl_iff, mem_iInter, mem_iUnion, mem_ofPred_eq,
      exists_prop] using mem_outerInfiniteDensitySet_iff_rational μ ν hμ hν hopenμ hopenν x
  rw [heq]
  exact (isOpen_zeroBallRegion μ).measurableSet.compl.inter
    (MeasurableSet.iInter fun n => MeasurableSet.iUnion fun δ => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
        measurableSet_lt measurable_const
          (measurable_outerRelativeDensityQuotient μ ν hμ hν hopenμ hopenν q))

/-- Simon (3.24)(iii), including Borel measurability of the prescribed
literal infinite-density singular set. -/
theorem simon_theorem_3_24_iii_borel
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hVν : HasSymmetricVitaliProperty ν)
    (hVμ : HasSymmetricVitaliProperty μ) :
    MeasurableSet (outerInfiniteDensitySet μ ν) ∧ ν (outerInfiniteDensitySet μ ν) = 0 ∧
      ∀ A : Set X, MeasurableSet A →
        μ A = (∫⁻ x in A, outerRelativeUpperDensity μ ν x ∂hν.toBorelMeasure) +
          (OuterMeasure.restrict (outerInfiniteDensitySet μ ν) μ) A :=
  ⟨measurableSet_outerInfiniteDensitySet μ ν hμ hν hopenμ hopenν,
    simon_theorem_3_24_iii μ ν hμ hν hopenμ hopenν hVν hVμ⟩

end Poincare.SimonGMT.Chapter01
