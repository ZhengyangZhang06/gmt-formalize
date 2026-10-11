module

public import Poincare.SimonGMT.Chapter01.DensityComparison

@[expose] public section

/-!
# Simon GMT, Chapter 1, the upper bound in (3.26)

The comparison set is Caratheodory measurable, not necessarily Borel.
The ambient metric space is arbitrary, and the dimension is any real
number `n ≥ 0` with Simon's literal Gamma-function normalization.
-/

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology Classical

namespace Poincare.SimonGMT.Chapter01

variable {X : Type*} [MetricSpace X]

/-- The sharp super-unit level-set estimate used in Simon (3.26)(1). -/
theorem hausdorff_upperDensity_superlevel_eq_zero
    {n : ℝ} (hn : 0 ≤ n) {A : Set X}
    (hA : IsCaratheodoryMeasurable (simonHausdorffOuterMeasureReal n) A)
    (hAfin : simonHausdorffOuterMeasureReal n A < ∞)
    {t : ℝ≥0∞} (ht : 1 < t) :
    simonHausdorffOuterMeasureReal n
      {x | x ∈ A ∧ t ≤ dimensionalUpperDensity (simonHausdorffOuterMeasureReal n) n A x} = 0 := by
  let H : OuterMeasure X := simonHausdorffOuterMeasureReal n
  have hH : IsBorelRegularOuterMeasure H := simonHausdorffOuterMeasureReal_isBorelRegular hn
  let η := OuterMeasure.restrict A H
  have hη : IsBorelRegularOuterMeasure η := hH.restrict hA hAfin
  have hopen : IsOpenSigmaFinite η := (isOpenSigmaFinite_iff η).mpr
    ⟨fun _ : ℕ => univ, fun _ => ⟨isOpen_univ, by
      simpa only [η, OuterMeasure.restrict_apply, univ_inter] using hAfin⟩,
      iUnion_const univ⟩
  let E := {x | x ∈ A ∧ t ≤ dimensionalUpperDensity H n A x}
  have hEA : E ⊆ A := fun _ hx => hx.1
  have hηE : η E = H E := by
    rw [OuterMeasure.restrict_apply, inter_eq_left.mpr hEA]
  have hbound : t * H E ≤ H E := calc
    t * H E ≤ ⨅ (U : Set X) (_ : E ⊆ U) (_ : IsOpen U), η U := by
      refine le_iInf fun U => le_iInf fun hEU => le_iInf fun hU => ?_
      have hcomp := mul_simonHausdorff_le_of_le_dimensionalUpperDensity H
        hH.borel_le_caratheodory hn E (A ∩ U) t (fun x hx => by
          rw [dimensionalUpperDensity_inter_of_mem_nhds H n A U x (hU.mem_nhds (hEU hx))]
          exact hx.2)
      simpa only [η, OuterMeasure.restrict_apply, inter_comm U A] using hcomp
    _ = η E := (hη.measure_eq_iInf_isOpen_of_closedSetsAreGDelta hopen
      (closedSetsAreGDelta_iff.mpr fun _ h => h.isGδ) E).symm
    _ = H E := hηE
  by_contra hne
  have hfin : H E ≠ ∞ := ((H.mono hEA).trans_lt hAfin).ne
  have hlt := ENNReal.mul_lt_mul_left hne hfin ht
  rw [one_mul] at hlt
  exact hlt.not_ge hbound

/-- Simon (3.26)(1), in null-exceptional-set form. -/
theorem simon_theorem_3_26_i
    {n : ℝ} (hn : 0 ≤ n) {A : Set X}
    (hA : IsCaratheodoryMeasurable (simonHausdorffOuterMeasureReal n) A)
    (hAfin : simonHausdorffOuterMeasureReal n A < ∞) :
    simonHausdorffOuterMeasureReal n
      {x | x ∈ A ∧ 1 < dimensionalUpperDensity (simonHausdorffOuterMeasureReal n) n A x} = 0 := by
  apply measure_mono_null (t := ⋃ (q : ℚ) (_ : 1 < (Real.toNNReal q : ℝ≥0∞)),
    {x | x ∈ A ∧ (Real.toNNReal q : ℝ≥0∞) ≤
      dimensionalUpperDensity (simonHausdorffOuterMeasureReal n) n A x})
  · intro x hx
    obtain ⟨q, _, hq, hqx⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hx.2
    exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hq, hx.1, hqx.le⟩⟩
  · exact measure_iUnion_null fun _ => measure_iUnion_null fun hq =>
      hausdorff_upperDensity_superlevel_eq_zero hn hA hAfin hq

local instance instHausdorffDensityBoundsMeasurableSpace : MeasurableSpace X := borel X
local instance instHausdorffDensityBoundsBorelSpace : BorelSpace X := ⟨rfl⟩

/-- The a.e. notation of the printed upper-density conclusion. -/
theorem ae_hausdorff_dimensionalUpperDensity_le_one
    {n : ℝ} (hn : 0 ≤ n) {A : Set X}
    (hA : IsCaratheodoryMeasurable (simonHausdorffOuterMeasureReal n) A)
    (hAfin : simonHausdorffOuterMeasureReal n A < ∞) :
    ∀ᵐ x ∂simonHausdorffMeasureReal n,
      x ∈ A → dimensionalUpperDensity (simonHausdorffOuterMeasureReal n) n A x ≤ 1 := by
  rw [ae_iff]
  change (simonHausdorffMeasureReal n).toOuterMeasure _ = 0
  rw [simonHausdorffMeasureReal_toOuterMeasure hn]
  simpa only [not_imp, not_le] using simon_theorem_3_26_i hn hA hAfin

end Poincare.SimonGMT.Chapter01
