module

public import Poincare.SimonGMT.Chapter01.RadonNikodymDensity

@[expose] public section

/-!
# Simon GMT, Chapter 1, Theorem (3.24)

The integrand below is the upper density, a total extension of the source's
partially defined density.  Theorem (3.23)(ii) proves that this extension
equals the actual density outside a Borel reference-null set.  Thus its
values at points of nonexistence have no effect on these integrals.
-/

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology Classical

namespace Poincare.SimonGMT.Chapter01

variable {X : Type*} [MetricSpace X]

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

/-- The upper density is a version of the abstract Radon--Nikodym
derivative for the reference measure. -/
theorem ae_outerRelativeUpperDensity_eq_rnDeriv
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ν) :
    outerRelativeUpperDensity μ ν =ᵐ[hν.toBorelMeasure]
      hμ.toBorelMeasure.rnDeriv hν.toBorelMeasure := by
  filter_upwards [ae_outerRelativeDensityQuotient_tendsto_rnDeriv
    μ ν hμ hν hopenμ hopenν hV] with x hx using hx.limsup_eq

/-- Simon (3.24)(i), for every Borel set, with the source's absolute
continuity condition on all subsets. -/
theorem simon_theorem_3_24_i
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ν)
    (hAC : ∀ E : Set X, ν E = 0 → μ E = 0) {A : Set X} (hA : MeasurableSet A) :
    μ A = ∫⁻ x in A, outerRelativeUpperDensity μ ν x ∂hν.toBorelMeasure := by
  let : SigmaFinite hμ.toBorelMeasure := hμ.toBorelMeasure_sigmaFinite hopenμ
  let : SigmaFinite hν.toBorelMeasure := hν.toBorelMeasure_sigmaFinite hopenν
  have hAC' : hμ.toBorelMeasure ≪ hν.toBorelMeasure := fun E hE => by
    rw [hμ.toBorelMeasure_apply_all]
    exact hAC E (by simpa only [hν.toBorelMeasure_apply_all] using hE)
  calc
    μ A = (hν.toBorelMeasure.withDensity
        (hμ.toBorelMeasure.rnDeriv hν.toBorelMeasure)) A := by
      rw [Measure.withDensity_rnDeriv_eq _ _ hAC', hμ.toBorelMeasure_apply_all]
    _ = ∫⁻ x in A, hμ.toBorelMeasure.rnDeriv hν.toBorelMeasure x ∂hν.toBorelMeasure :=
      withDensity_apply _ hA
    _ = ∫⁻ x in A, outerRelativeUpperDensity μ ν x ∂hν.toBorelMeasure :=
      lintegral_congr_ae (ae_restrict_of_ae
        (ae_outerRelativeUpperDensity_eq_rnDeriv μ ν hμ hν hopenμ hopenν hV).symm)

/-- The decomposition formula holds for any set which separates the
singular and reference measures; no measurability of that set is needed
when the evaluated set is Borel. -/
theorem density_decomposition_of_singular_separator
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ν)
    {Z : Set X} (hνZ : ν Z = 0)
    (hσZ : (hμ.toBorelMeasure.singularPart hν.toBorelMeasure) Zᶜ = 0)
    {A : Set X} (hA : MeasurableSet A) :
    μ A = (∫⁻ x in A, outerRelativeUpperDensity μ ν x ∂hν.toBorelMeasure) +
      (OuterMeasure.restrict Z μ) A := by
  let : SigmaFinite hμ.toBorelMeasure := hμ.toBorelMeasure_sigmaFinite hopenμ
  let : SigmaFinite hν.toBorelMeasure := hν.toBorelMeasure_sigmaFinite hopenν
  have hsing : hμ.toBorelMeasure.singularPart hν.toBorelMeasure =
      hμ.toBorelMeasure.restrict Z := Measure.singularPart_eq_restrict hσZ
        (by simpa only [hν.toBorelMeasure_apply_all] using hνZ)
  have heq := ae_outerRelativeUpperDensity_eq_rnDeriv μ ν hμ hν hopenμ hopenν hV
  calc
    μ A = (hν.toBorelMeasure.withDensity
        (hμ.toBorelMeasure.rnDeriv hν.toBorelMeasure) +
        hμ.toBorelMeasure.singularPart hν.toBorelMeasure) A := by
      rw [Measure.rnDeriv_add_singularPart, hμ.toBorelMeasure_apply_all]
    _ = (∫⁻ x in A, hμ.toBorelMeasure.rnDeriv hν.toBorelMeasure x ∂hν.toBorelMeasure) +
        (OuterMeasure.restrict Z μ) A := by
      rw [Measure.add_apply, withDensity_apply _ hA, hsing, Measure.restrict_apply hA,
        hμ.toBorelMeasure_apply_all, OuterMeasure.restrict_apply]
    _ = _ := congrArg (· + (OuterMeasure.restrict Z μ) A)
      (lintegral_congr_ae (ae_restrict_of_ae heq.symm))

/-- Simon (3.24)(ii): a Borel reference-null singular set and the
Lebesgue decomposition written with the actual density. -/
theorem simon_theorem_3_24_ii
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ν) :
    ∃ Z : Set X, MeasurableSet Z ∧ ν Z = 0 ∧ ∀ A : Set X, MeasurableSet A →
      μ A = (∫⁻ x in A, outerRelativeUpperDensity μ ν x ∂hν.toBorelMeasure) +
        (OuterMeasure.restrict Z μ) A := by
  obtain ⟨E, hE, hσE, hνEc⟩ := hμ.toBorelMeasure.mutuallySingular_singularPart hν.toBorelMeasure
  have hνZ : ν Eᶜ = 0 := by simpa only [hν.toBorelMeasure_apply_all] using hνEc
  refine ⟨Eᶜ, hE.compl, hνZ, fun A hA => ?_⟩
  exact density_decomposition_of_singular_separator μ ν hμ hν hopenμ hopenν hV hνZ
    (by simpa only [compl_compl] using hσE) hA

/-- The literal infinite-density set: the full one-sided limit must
exist and equal infinity, not merely the upper density. -/
def outerInfiniteDensitySet (μ ν : OuterMeasure X) : Set X :=
  {x | Tendsto (outerRelativeDensityQuotient μ ν x) (𝓝[>] (0 : ℝ)) (𝓝 ∞)}

/-- The literal infinite-density set is reference-null. -/
theorem outerInfiniteDensitySet_eq_zero
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hV : HasSymmetricVitaliProperty ν) :
    ν (outerInfiniteDensitySet μ ν) = 0 := by
  let : SigmaFinite hμ.toBorelMeasure := hμ.toBorelMeasure_sigmaFinite hopenμ
  have hae : ∀ᵐ x ∂hν.toBorelMeasure, x ∉ outerInfiniteDensitySet μ ν := by
    filter_upwards [ae_outerRelativeDensityQuotient_tendsto_rnDeriv μ ν hμ hν hopenμ hopenν hV,
      hμ.toBorelMeasure.rnDeriv_lt_top hν.toBorelMeasure] with x hx hfin htop
    exact hfin.ne (tendsto_nhds_unique hx htop)
  simpa only [ae_iff, not_not, ofPred_mem_eq, hν.toBorelMeasure_apply_all] using hae

/-- Simon (3.24)(iii): the decomposition formula for the literal set
where the density exists and is infinite. -/
theorem simon_theorem_3_24_iii
    (μ ν : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hν : IsBorelRegularOuterMeasure ν) (hopenμ : IsOpenSigmaFinite μ)
    (hopenν : IsOpenSigmaFinite ν) (hVν : HasSymmetricVitaliProperty ν)
    (hVμ : HasSymmetricVitaliProperty μ) :
    ν (outerInfiniteDensitySet μ ν) = 0 ∧ ∀ A : Set X, MeasurableSet A →
      μ A = (∫⁻ x in A, outerRelativeUpperDensity μ ν x ∂hν.toBorelMeasure) +
        (OuterMeasure.restrict (outerInfiniteDensitySet μ ν) μ) A := by
  let : SigmaFinite hμ.toBorelMeasure := hμ.toBorelMeasure_sigmaFinite hopenμ
  let : SigmaFinite hν.toBorelMeasure := hν.toBorelMeasure_sigmaFinite hopenν
  have hνZ := outerInfiniteDensitySet_eq_zero μ ν hμ hν hopenμ hopenν hVν
  have hσac : hμ.toBorelMeasure.singularPart hν.toBorelMeasure ≪ hμ.toBorelMeasure :=
    Measure.absolutelyContinuous_of_le (Measure.singularPart_le _ _)
  have hσae : ∀ᵐ x ∂(hμ.toBorelMeasure.singularPart hν.toBorelMeasure),
      x ∈ outerInfiniteDensitySet μ ν := by
    filter_upwards [hσac.ae_le
      (ae_outerRelativeDensityQuotient_tendsto_inv_rnDeriv μ ν hμ hν hopenμ hopenν hVμ),
      hν.toBorelMeasure.rnDeriv_eq_zero_ae_singularPart hμ.toBorelMeasure] with x hx hz
    change Tendsto (outerRelativeDensityQuotient μ ν x) (𝓝[>] (0 : ℝ)) (𝓝 ∞)
    simpa only [hz, ENNReal.inv_zero] using hx
  have hσZ : (hμ.toBorelMeasure.singularPart hν.toBorelMeasure)
      (outerInfiniteDensitySet μ ν)ᶜ = 0 := by
    rw [ae_iff] at hσae
    exact hσae
  exact ⟨hνZ, fun A hA => density_decomposition_of_singular_separator
    μ ν hμ hν hopenμ hopenν hVν hνZ hσZ hA⟩

end Poincare.SimonGMT.Chapter01
