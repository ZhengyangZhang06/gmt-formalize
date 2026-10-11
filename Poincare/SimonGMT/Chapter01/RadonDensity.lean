module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Poincare.SimonGMT.Chapter01.RadonTopology
public import Poincare.SimonGMT.Chapter01.RadonOuterMeasure

public section

/-!
# Simon GMT, Chapter 1, Theorem 4.10 and Corollary 4.11

Mathlib's compact-support density theorem assumes a normal space.  Simon only
assumes locally compact Hausdorff.  We instead use the compact-set Urysohn lemma
and simple-function density, retaining the source's exact topological scope.
The outer-measure theorem uses the full Caratheodory sigma-algebra.
-/

open MeasureTheory Set TopologicalSpace
open scoped CompactlySupported ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

section MeasureDensity

variable [MeasurableSpace X] [OpensMeasurableSpace X]
  {ν : Measure X} [ν.Regular] {p : ℝ≥0∞}

/-- A compact-set indicator is approximated in `Lᵖ` by compactly supported
continuous functions without assuming that the entire space is normal. -/
theorem exists_compactlySupported_eLpNorm_sub_indicator_le
    (hp : p ≠ ∞) {K : Set X} (hK : IsCompact K) (c : ℝ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : X → ℝ, Continuous g ∧ HasCompactSupport g ∧
      eLpNorm (g - K.indicator (fun _ => c)) p ν ≤ ε := by
  obtain ⟨η, hηpos, hη⟩ := exists_eLpNorm_indicator_le (μ := ν) hp c hε
  have hηpos' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.mpr hηpos
  obtain ⟨V, hKV, hV, _, hVsmall⟩ :=
    hK.measurableSet.exists_isOpen_sdiff_lt (μ := ν)
      (hK.measure_lt_top (μ := ν)).ne hηpos'.ne'
  obtain ⟨f, hfK, hfc, hfV, hfI⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
  have hfzero : ∀ x ∉ V, f x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hfV h))
  have hgc : HasCompactSupport (fun x => f x * c) :=
    (show HasCompactSupport f from hfc).mul_right
  have hgcont : Continuous (fun x => f x * c) := f.continuous.mul continuous_const
  have hgmem : MemLp (fun x => f x * c) p ν :=
    hgcont.memLp_of_hasCompactSupport hgc
  have hgbound : ∀ x, ‖f x * c‖ ≤ ‖c‖ := by
    intro x
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hfI x).1]
    exact mul_le_of_le_one_left (norm_nonneg c) (hfI x).2
  have hdiff : ∀ x,
      ‖f x * c - K.indicator (fun _ => c) x‖ ≤
        ‖(V \ K).indicator (fun _ => c) x‖ := by
    intro x
    by_cases hxK : x ∈ K
    · simp [hxK, hfK hxK]
    · by_cases hxV : x ∈ V
      · simpa [hxK, hxV] using hgbound x
      · simp [hxK, hxV, hfzero x hxV]
  refine ⟨_, hgcont, hgc, ?_⟩
  exact (eLpNorm_mono (hgmem.aestronglyMeasurable.sub
    (aestronglyMeasurable_const.indicator hK.measurableSet)) hdiff).trans
      (hη _ hVsmall.le (hV.measurableSet.diff hK.measurableSet).nullMeasurableSet)

/-- The simple-function density argument for Simon Theorem 4.10.  This
version allows any sigma-algebra containing the Borel sets. -/
theorem exists_hasCompactSupport_eLpNorm_sub_le_of_radon
    (hp : p ≠ ∞) {f : X → ℝ} (hf : MemLp f p ν)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : X → ℝ, eLpNorm (f - g) p ν ≤ ε ∧ Continuous g ∧ HasCompactSupport g := by
  apply hf.induction_dense hp (fun g => Continuous g ∧ HasCompactSupport g) ?_ ?_ hε
  · intro c A hA hAfin δ hδ
    obtain ⟨η, hηpos, hη⟩ := exists_Lp_half ℝ ν p hδ
    obtain ⟨ζ, hζpos, hζ⟩ := exists_eLpNorm_indicator_le (μ := ν) hp c hηpos.ne'
    have hζpos' : (0 : ℝ≥0∞) < ζ := ENNReal.coe_pos.mpr hζpos
    obtain ⟨K, hKA, hK, hsmall⟩ :=
      hA.exists_isCompact_sdiff_lt hAfin.ne hζpos'.ne'
    have herror : eLpNorm (K.indicator (fun _ => c) - A.indicator (fun _ => c)) p ν ≤ η := by
      rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff hKA]
      exact hζ _ hsmall.le (hA.diff hK.measurableSet).nullMeasurableSet
    obtain ⟨g, hgcont, hgc, hg⟩ :=
      exists_compactlySupported_eLpNorm_sub_indicator_le (ν := ν) hp hK c hηpos.ne'
    refine ⟨g, ?_, hgcont, hgc⟩
    convert (hη _ _ hg herror).le using 2
    ext x
    simp
  · intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩

/-- Simon Theorem 4.10 for a regular measure on any sigma-algebra containing
the open sets.  The exponent hypotheses are exactly `1 ≤ p < ∞`. -/
theorem simon_theorem_4_10_measure {p : ℝ≥0∞} (_hp : 1 ≤ p) (hpfin : p < ∞)
    {f : X → ℝ} (hf : MemLp f p ν) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ g : C_c(X, ℝ), eLpNorm (f - (g : X → ℝ)) p ν < ε := by
  obtain ⟨δ, hδpos, hδε⟩ := exists_between hε
  obtain ⟨g, hg, hgcont, hgc⟩ :=
    exists_hasCompactSupport_eLpNorm_sub_le_of_radon hpfin.ne hf hδpos.ne'
  exact ⟨⟨⟨g, hgcont⟩, hgc⟩, hg.trans_lt hδε⟩

end MeasureDensity

/-- Simon Theorem 4.10 in the literal outer-measure formulation: all
Caratheodory-measurable `Lᵖ` functions are included, not only Borel functions. -/
theorem IsRadonOuterMeasure.simon_theorem_4_10
    {μ : OuterMeasure X} (hμ : IsRadonOuterMeasure μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p < ∞) {f : X → ℝ}
    (hf : @MemLp X ℝ μ.caratheodory _ _ f p hμ.toCaratheodoryMeasure)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ g : C_c(X, ℝ),
      @eLpNorm X ℝ _ _ μ.caratheodory (f - (g : X → ℝ)) p
        hμ.toCaratheodoryMeasure < ε := by
  let : MeasurableSpace X := μ.caratheodory
  let : OpensMeasurableSpace X := ⟨hμ.borel_regular.borel_le_caratheodory⟩
  let : Measure.Regular hμ.toCaratheodoryMeasure := hμ.toCaratheodoryMeasure_regular
  exact simon_theorem_4_10_measure hp hpfin hf hε

/-- Simon Corollary 4.11, including both conclusions: density in `L¹` and
extension of the Borel measure to a Radon outer measure.  The extension in
fact agrees with the original measure's outer evaluation on every subset. -/
theorem simon_corollary_4_11 [MeasurableSpace X] [BorelSpace X]
    (hX : OpenSetsAreSigmaCompact X) (ν : Measure X)
    (hfin : ∀ ⦃K : Set X⦄, IsCompact K → ν K < ∞) :
    (∀ (f : X → ℝ), MemLp f 1 ν → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ g : C_c(X, ℝ), eLpNorm (f - (g : X → ℝ)) 1 ν < ε) ∧
    ∃ μ : OuterMeasure X, IsRadonOuterMeasure μ ∧
      ∀ B : Set X, MeasurableSet B → μ B = ν B := by
  have hRadon := simon_lemma_4_9 hX (measure_toOuterMeasure_isBorelRegular ν) hfin
  let : ν.Regular := hRadon.regular_of_toOuterMeasure
  exact ⟨fun _ hf _ hε => simon_theorem_4_10_measure le_rfl (by simp) hf hε,
    ν.toOuterMeasure, hRadon, fun _ _ => rfl⟩

end Poincare.SimonGMT.Chapter01
