module

public import Poincare.SimonGMT.Chapter01.InfiniteDensitySet

@[expose] public section

/-!
# Simon GMT, Chapter 1, Remark (3.25)

The PDF literally cites `(3.23)(iii)` in Remark (3.25)(1), but (3.23) has
only two clauses.  The theorem below explicitly formalizes the intended
reference to (3.24)(iii), rather than silently claiming that the printed
cross-reference exists.  Part (2) supplies terminology, not a new theorem.
-/

open Filter Set MeasureTheory
open scoped ENNReal Topology Classical

namespace Poincare.SimonGMT.Chapter01

/-- Simon's name in (3.25)(2) for the restriction to the singular set
supplied by (3.24).  This definition does not assert that an arbitrary
restriction is singular; that assertion requires the preceding theorem's
conditions on `Z`. -/
noncomputable def simonSingularPart {X : Type*} (μ : OuterMeasure X) (Z : Set X) :
    OuterMeasure X := OuterMeasure.restrict Z μ

theorem simonSingularPart_apply {X : Type*} (μ : OuterMeasure X) (Z A : Set X) :
    simonSingularPart μ Z A = μ (A ∩ Z) :=
  OuterMeasure.restrict_apply Z A μ

/-- Open sigma-finiteness gives compact finiteness, as needed to apply
the Euclidean symmetric-Vitali theorem without extra hypotheses. -/
theorem IsBorelRegularOuterMeasure.finite_on_compacts_of_openSigmaFinite
    {X : Type*} [MetricSpace X] {μ : OuterMeasure X}
    (hμ : IsBorelRegularOuterMeasure μ) (hopen : IsOpenSigmaFinite μ)
    {K : Set X} (hK : IsCompact K) : μ K < ∞ := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let : IsLocallyFiniteMeasure hμ.toBorelMeasure := hμ.toBorelMeasure_isLocallyFinite hopen
  simpa only [hμ.toBorelMeasure_apply_all] using hK.measure_lt_top (μ := hμ.toBorelMeasure)

/-- The Euclidean conclusion intended by (3.25)(1).  The source's
reference `3.23(iii)` is corrected explicitly to `3.24(iii)`. -/
theorem simon_remark_3_25_one_corrected_reference
    (d : ℕ) (μ ν : OuterMeasure (EuclideanSpace ℝ (Fin d)))
    (hμ : IsBorelRegularOuterMeasure μ) (hν : IsBorelRegularOuterMeasure ν)
    (hopenμ : IsOpenSigmaFinite μ) (hopenν : IsOpenSigmaFinite ν) :
    @MeasurableSet _ (borel _) (outerInfiniteDensitySet μ ν) ∧
      ν (outerInfiniteDensitySet μ ν) = 0 ∧
      ∀ A : Set (EuclideanSpace ℝ (Fin d)), @MeasurableSet _ (borel _) A →
        μ A = (∫⁻ x in A, outerRelativeUpperDensity μ ν x ∂hν.toBorelMeasure) +
          simonSingularPart μ (outerInfiniteDensitySet μ ν) A := by
  exact simon_theorem_3_24_iii_borel μ ν hμ hν hopenμ hopenν
    (hasSymmetricVitaliProperty_euclidean d ν hν fun _ hK =>
      hν.finite_on_compacts_of_openSigmaFinite hopenν hK)
    (hasSymmetricVitaliProperty_euclidean d μ hμ fun _ hK =>
      hμ.finite_on_compacts_of_openSigmaFinite hopenμ hK)

end Poincare.SimonGMT.Chapter01
