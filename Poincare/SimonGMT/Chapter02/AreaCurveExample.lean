module

public import Poincare.SimonGMT.Chapter02.AreaLiteral
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-!
# Simon (3.6)(1): length of an injective C¹ curve

The interval is the actual domain of the curve. No nonvanishing-speed
hypothesis and no assumption on values off the interval is needed. The
stronger Lipschitz version uses the almost-everywhere within derivative.
-/

open Function MeasureTheory Module Set Filter
open scoped ENNReal NNReal

namespace Poincare.SimonGMT.Chapter02
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]

/-- Restricting a Lipschitz map to a smaller Lebesgue-measurable set does
not change its within derivative at almost every point of that smaller set. -/
theorem ae_fderivWithin_eq_of_subset_lipschitzOn
    {s t : Set E} (hs : NullMeasurableSet s volume)
    (ht : NullMeasurableSet t volume) (hst : s ⊆ t)
    {f : E → F} {K : ℝ≥0} (hf : LipschitzOnWith K f t) :
    fderivWithin ℝ f s =ᵐ[volume.restrict s] fderivWithin ℝ f t := by
  obtain ⟨g, L, hg, hfg⟩ := exists_lipschitz_extension_finiteDimensional hf
  have ht' : fderivWithin ℝ f t =ᵐ[volume.restrict s] fderiv ℝ g :=
    ae_restrict_of_ae_restrict_of_subset hst
      (ae_fderivWithin_eq_of_lipschitz_extension ht hg hfg)
  exact (ae_fderivWithin_eq_of_lipschitz_extension hs hg (hfg.mono hst)).trans
    ht'.symm

/-- An injective Lipschitz space curve has the usual speed-integral length
on every Lebesgue-measurable part of its interval domain. -/
theorem injective_lipschitz_curve_area_formula
    {a b : ℝ} {s : Set ℝ} {f : ℝ → F} {K : ℝ≥0}
    (hs : NullMeasurableSet s volume) (hsI : s ⊆ Icc a b)
    (hf : LipschitzOnWith K f (Icc a b)) (hi : InjOn f (Icc a b)) :
    Chapter01.simonHausdorffMeasureReal 1 (f '' s) =
      ∫⁻ t in s, ENNReal.ofReal ‖derivWithin f (Icc a b) t‖ ∂volume := by
  rw [show (1 : ℝ) = (finrank ℝ ℝ : ℝ) by simp,
    injective_area_formula_lipschitzOn_simon_volume hs (hf.mono hsI) (hi.mono hsI)]
  apply lintegral_congr_ae
  filter_upwards [ae_fderivWithin_eq_of_subset_lipschitzOn hs
    measurableSet_Icc.nullMeasurableSet hsI hf] with t ht
  simp only [areaJacobianWithin, ht]
  congr 1
  exact normDet_real_domain (fderivWithin ℝ f (Icc a b) t).toLinearMap

/-- Simon's literal space-curve example: an arbitrary injective C¹ map on
`[a,b]`, including curves whose speed vanishes, with the exact Hausdorff
normalization and every Lebesgue-measurable subset of its domain. -/
theorem injective_contDiffOn_curve_area_formula
    {a b : ℝ} {s : Set ℝ} {f : ℝ → F}
    (hs : NullMeasurableSet s volume) (hsI : s ⊆ Icc a b)
    (hf : ContDiffOn ℝ 1 f (Icc a b)) (hi : InjOn f (Icc a b)) :
    Chapter01.simonHausdorffMeasureReal 1 (f '' s) =
      ∫⁻ t in s, ENNReal.ofReal ‖derivWithin f (Icc a b) t‖ ∂volume := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith one_ne_zero (convex_Icc a b) isCompact_Icc
  exact injective_lipschitz_curve_area_formula hs hsI hK hi

end
end Poincare.SimonGMT.Chapter02
