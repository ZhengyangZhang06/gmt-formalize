module

public import Poincare.SimonGMT.Chapter01.ExactRegularity
public import Mathlib.MeasureTheory.Function.Egorov
public import Mathlib.Topology.UniformSpace.UniformApproximation

public section

/-!
# Simon GMT, Chapter 1, Theorem 1.17 (Lusin's theorem)

This file proves the finite-measure Lusin theorem under Simon's exact
topological hypothesis that closed sets are countable intersections of open
sets.  The proof follows the source: approximate a measurable function by
finite-range measurable functions, discard sets of arbitrarily small measure
on which those approximants fail to be continuous, and pass to a uniform
limit on the remaining set.
-/

open Filter Set
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u

variable {X : Type u} [TopologicalSpace X]

namespace SimpleFunc

open MeasureTheory

/-- A finite-range measurable real-valued function is continuous on a closed
subset whose complement in a prescribed finite-measure measurable set has
arbitrarily small measure.  This is the finite-level approximation used in
the proof of Simon Theorem 1.17. -/
theorem exists_isClosed_continuousOn
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (nu : Measure X)
    (hreg : ∀ ⦃S : Set X⦄, MeasurableSet S → nu S ≠ ∞ →
      ∀ ⦃δ : ℝ≥0∞⦄, δ ≠ 0 →
        ∃ F : Set X, F ⊆ S ∧ IsClosed F ∧ nu (S \ F) < δ)
    (g : SimpleFunc X ℝ) {A : Set X} (hA : MeasurableSet A)
    (hAfin : nu A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ C : Set X, C ⊆ A ∧ IsClosed C ∧ nu (A \ C) < ε ∧ ContinuousOn g C := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
      letI : IsEmpty X := hX
      refine ⟨∅, empty_subset _, isClosed_empty, ?_, continuousOn_empty g⟩
      simpa only [Subsingleton.elim A ∅, empty_sdiff, measure_empty] using
        (pos_iff_ne_zero.mpr hε)
  | inr hX =>
      letI : Nonempty X := hX
      have hrange : g.range.Nonempty := ⟨g (Classical.choice hX), g.mem_range_self _⟩
      obtain ⟨δ, hδpos, hδsum⟩ :=
        ENNReal.exists_pos_mul_lt
          (a := (g.range.card : ℝ≥0∞)) (b := ε) (by finiteness) hε
      have happ : ∀ y : ℝ, ∃ F : Set X,
          F ⊆ A ∩ g ⁻¹' {y} ∧ IsClosed F ∧ nu ((A ∩ g ⁻¹' {y}) \ F) < δ := by
        intro y
        have hm : MeasurableSet (A ∩ g ⁻¹' {y}) :=
          hA.inter (g.measurableSet_fiber y)
        have hfin : nu (A ∩ g ⁻¹' {y}) ≠ ∞ :=
          ne_top_of_le_ne_top hAfin (measure_mono inter_subset_left)
        obtain ⟨F, hFsub, hFclosed, hFsmall⟩ := hreg hm hfin hδpos.ne'
        exact ⟨F, hFsub, hFclosed, hFsmall⟩
      choose F hFsub hFclosed hFsmall using happ
      let C : Set X := ⋃ y ∈ g.range, F y
      have hCsub : C ⊆ A := by
        rintro x hx
        simp only [C, mem_iUnion] at hx
        obtain ⟨y, _, hxy⟩ := hx
        exact (hFsub y hxy).1
      have hCclosed : IsClosed C := by
        exact isClosed_biUnion_finset fun y _ => hFclosed y
      have hbadsub : A \ C ⊆ ⋃ y ∈ g.range, (A ∩ g ⁻¹' {y}) \ F y := by
        rintro x ⟨hxA, hxC⟩
        refine mem_iUnion₂.mpr ⟨g x, g.mem_range_self x, ?_⟩
        refine ⟨⟨hxA, by simp⟩, ?_⟩
        intro hxF
        exact hxC (mem_iUnion₂.mpr ⟨g x, g.mem_range_self x, hxF⟩)
      have hCsmall : nu (A \ C) < ε := by
        calc
          nu (A \ C) ≤ nu (⋃ y ∈ g.range, (A ∩ g ⁻¹' {y}) \ F y) :=
            measure_mono hbadsub
          _ ≤ ∑ y ∈ g.range, nu ((A ∩ g ⁻¹' {y}) \ F y) :=
            measure_biUnion_finset_le g.range _
          _ < ∑ _y ∈ g.range, δ :=
            ENNReal.sum_lt_sum_of_nonempty hrange fun y _ => hFsmall y
          _ = δ * (g.range.card : ℝ≥0∞) := by simp [mul_comm]
          _ < ε := hδsum
      have hCcontinuous : ContinuousOn g C := by
        intro x hxC
        simp only [C, mem_iUnion] at hxC
        obtain ⟨y, hy, hxy⟩ := hxC
        have hgxy : g x = y := by
          exact (hFsub y hxy).2
        let U : Set X := (⋃ z ∈ g.range.erase y, F z)ᶜ
        have hUopen : IsOpen U := by
          exact (isClosed_biUnion_finset fun z _ => hFclosed z).isOpen_compl
        have hxU : x ∈ U := by
          simp only [U, mem_compl_iff, mem_iUnion, not_exists]
          intro z hz hzx
          have hgz : g x = z := (hFsub z hzx).2
          exact (Finset.mem_erase.mp hz).1 (hgz.symm.trans hgxy)
        have heq : g =ᶠ[𝓝[C] x] (fun _ : X => g x) := by
          filter_upwards [mem_nhdsWithin_of_mem_nhds (hUopen.mem_nhds hxU),
            self_mem_nhdsWithin] with x' hxU' hxC'
          simp only [C, mem_iUnion] at hxC'
          obtain ⟨z, hz, hxz⟩ := hxC'
          have hgz : g x' = z := (hFsub z hxz).2
          have hzy : z = y := by
            by_contra hne
            exact hxU' (mem_iUnion₂.mpr ⟨z, Finset.mem_erase.mpr ⟨hne, hz⟩, hxz⟩)
          simpa [hgz, hzy, hgxy]
        exact continuousWithinAt_const.congr_of_eventuallyEq heq rfl
      exact ⟨C, hCsub, hCclosed, hCsmall, hCcontinuous⟩

end SimpleFunc

open MeasureTheory

/-- Lusin's theorem for a weakly regular measure: a measurable real-valued
function on a finite-measure measurable set is continuous on a closed subset
with arbitrarily small discarded measure. -/
theorem exists_isClosed_continuousOn_of_measurable
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (nu : Measure X)
    (hreg : ∀ ⦃S : Set X⦄, MeasurableSet S → nu S ≠ ∞ →
      ∀ ⦃δ : ℝ≥0∞⦄, δ ≠ 0 →
        ∃ F : Set X, F ⊆ S ∧ IsClosed F ∧ nu (S \ F) < δ)
    {A : Set X} (hA : MeasurableSet A) (hAfin : nu A ≠ ∞)
    {f : X → ℝ} (hf : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ C : Set X, C ⊆ A ∧ IsClosed C ∧ nu (A \ C) < ε ∧ ContinuousOn f C := by
  classical
  let hs : StronglyMeasurable f := hf.stronglyMeasurable
  let g : ℕ → X → ℝ := fun n => hs.approx n
  obtain ⟨η, hηpos, hηtotal⟩ :=
    ENNReal.exists_pos_mul_lt (a := (3 : ℝ≥0∞)) (b := ε) (by simp) hε
  have hweight : ∀ n : ℕ, (η / 2) * 2⁻¹ ^ n ≠ 0 := by
    intro n
    apply mul_ne_zero
    · exact (ENNReal.div_pos hηpos.ne' (by norm_num)).ne'
    · exact ENNReal.pow_ne_zero (ENNReal.inv_ne_zero.2 (by norm_num)) n
  have happ : ∀ n : ℕ, ∃ D : Set X,
      D ⊆ A ∧ IsClosed D ∧ nu (A \ D) < (η / 2) * 2⁻¹ ^ n ∧
        ContinuousOn (g n) D := by
    intro n
    simpa only [g] using
      SimpleFunc.exists_isClosed_continuousOn nu hreg (hs.approx n) hA hAfin (hweight n)
  choose D hDsub hDclosed hDsmall hDcontinuous using happ
  let q : Set X := ⋃ n : ℕ, A \ D n
  have hqmeas : MeasurableSet q := by
    exact MeasurableSet.iUnion fun n => hA.inter (hDclosed n).isOpen_compl.measurableSet
  have hqmeasure : nu q ≤ η := by
    calc
      nu q ≤ ∑' n : ℕ, nu (A \ D n) := by
        exact measure_iUnion_le _
      _ ≤ ∑' n : ℕ, (η / 2) * 2⁻¹ ^ n :=
        ENNReal.tsum_le_tsum fun n => (hDsmall n).le
      _ ≤ η := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two, mul_comm]
        exact ENNReal.mul_div_le
  obtain ⟨t, htA, htmeas, htmeasure, htuniform⟩ :=
    tendstoUniformlyOn_of_ae_tendsto
      (f := g) (g := f) (μ := nu)
      (fun n => (hs.approx n).stronglyMeasurable) hs hA hAfin
      (Filter.Eventually.of_forall fun x _ => hs.tendsto_approx x) hηpos
  let R : Set X := A \ (q ∪ t)
  have hRmeas : MeasurableSet R := hA.inter (hqmeas.union htmeas).compl
  have hRfinite : nu R ≠ ∞ :=
    ne_top_of_le_ne_top hAfin (measure_mono (sdiff_subset.trans (subset_refl A)))
  obtain ⟨C, hCR, hCclosed, hCsmall⟩ := hreg hRmeas hRfinite hηpos.ne'
  have hCA : C ⊆ A := hCR.trans sdiff_subset
  have hCD : ∀ n : ℕ, C ⊆ D n := by
    intro n x hxC
    have hxR := hCR hxC
    by_contra hxD
    exact hxR.2 (Or.inl (mem_iUnion.mpr ⟨n, hxR.1, hxD⟩))
  have hCt : C ⊆ A \ t := by
    intro x hxC
    have hxR := hCR hxC
    exact ⟨hxR.1, fun hxt => hxR.2 (Or.inr hxt)⟩
  have hCcontinuous : ContinuousOn f C := by
    apply (htuniform.mono hCt).continuousOn
    exact Filter.Frequently.of_forall fun n => (hDcontinuous n).mono (hCD n)
  have hdiscard : A \ C ⊆ q ∪ t ∪ (R \ C) := by
    rintro x ⟨hxA, hxC⟩
    by_cases hxq : x ∈ q
    · exact Or.inl (Or.inl hxq)
    by_cases hxt : x ∈ t
    · exact Or.inl (Or.inr hxt)
    · exact Or.inr ⟨⟨hxA, by simpa [hxq, hxt]⟩, hxC⟩
  have hmeasure : nu (A \ C) < ε := by
    calc
      nu (A \ C) ≤ nu (q ∪ t ∪ (R \ C)) := measure_mono hdiscard
      _ ≤ nu q + nu t + nu (R \ C) := by
        exact (measure_union_le _ _).trans <|
          add_le_add (measure_union_le q t) le_rfl
      _ < nu q + nu t + η := by
        apply ENNReal.add_lt_add_left
        · exact ENNReal.add_ne_top.2
            ⟨ne_top_of_le_ne_top (ne_top_of_lt <|
                ENNReal.lt_top_of_mul_ne_top_left
                  (ne_top_of_lt (hηtotal.trans_le le_top)) (by norm_num)) hqmeasure,
              ne_top_of_le_ne_top (ne_top_of_lt <|
                ENNReal.lt_top_of_mul_ne_top_left
                  (ne_top_of_lt (hηtotal.trans_le le_top)) (by norm_num)) htmeasure⟩
        · exact hCsmall
      _ ≤ η + η + η := add_le_add (add_le_add hqmeasure htmeasure) le_rfl
      _ = η * (3 : ℝ≥0∞) := by ring
      _ < ε := hηtotal
  exact ⟨C, hCA, hCclosed, hmeasure, hCcontinuous⟩

/-- The finite-measure regularity step in Simon's proof of Theorem 1.17.
It applies Theorem 1.15 to the finite restricted outer measure, so no global
open-sigma-finiteness assumption is needed. -/
theorem IsBorelRegularOuterMeasure.exists_isClosed_sdiff_lt_of_finite
    {mu : OuterMeasure X} (hmu : IsBorelRegularOuterMeasure mu)
    (hX : ClosedSetsAreGDelta X) {S : Set X}
    (hS : IsCaratheodoryMeasurable mu S) (hSfinite : mu S < ∞)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ C : Set X, C ⊆ S ∧ IsClosed C ∧ mu (S \ C) < δ := by
  let muS : OuterMeasure X := OuterMeasure.restrict S mu
  have hmuS : IsBorelRegularOuterMeasure muS := hmu.restrict hS hSfinite
  have hopenS : IsOpenSigmaFinite muS := by
    apply (isOpenSigmaFinite_iff muS).2
    refine ⟨fun _ => Set.univ, ?_, ?_⟩
    · intro n
      refine ⟨isOpen_univ, ?_⟩
      simpa only [muS, OuterMeasure.restrict_apply, univ_inter] using hSfinite
    · exact Set.iUnion_const Set.univ
  have hSmuS : IsCaratheodoryMeasurable muS S :=
    isCaratheodoryMeasurable_restrict hS
  have heq :=
    hmuS.measure_eq_iSup_isClosed_of_closedSetsAreGDelta hopenS hX hSmuS
  have hmuSS : muS S ≠ ∞ := by
    simpa only [muS, OuterMeasure.restrict_apply, inter_self] using hSfinite.ne
  by_cases hsmall : muS S < δ
  · refine ⟨∅, empty_subset _, isClosed_empty, ?_⟩
    simpa only [sdiff_empty, muS, OuterMeasure.restrict_apply, inter_self] using hsmall
  · have hδle : δ ≤ muS S := le_of_not_gt hsmall
    have hmuSS0 : muS S ≠ 0 := by
      exact fun hz => hδ (nonpos_iff_eq_zero.mp (hz ▸ hδle))
    have hlower : muS S - δ < muS S :=
      ENNReal.sub_lt_self hmuSS hmuSS0 hδ
    obtain ⟨r, hlower_r, hr_mass⟩ := exists_between hlower
    have hrSup : r < ⨆ (C : Set X) (_ : C ⊆ S) (_ : IsClosed C), muS C := by
      rwa [← heq]
    obtain ⟨C, hrC⟩ := lt_iSup_iff.mp hrSup
    obtain ⟨hCS, hrC⟩ := lt_iSup_iff.mp hrC
    obtain ⟨hCclosed, hrC⟩ := lt_iSup_iff.mp hrC
    have hmass_add : muS S < muS C + δ := by
      refine (ENNReal.lt_add_of_sub_lt_right (Or.inl hmuSS) hlower_r).trans_le ?_
      exact add_le_add hrC.le le_rfl
    have hCborel : @MeasurableSet X (borel X) C := by
      letI : MeasurableSpace X := borel X
      letI : OpensMeasurableSpace X := ⟨le_rfl⟩
      exact hCclosed.measurableSet
    have hCcar : IsCaratheodoryMeasurable mu C :=
      hmu.borel_le_caratheodory C hCborel
    letI : MeasurableSpace X := mu.caratheodory
    letI : OpensMeasurableSpace X := ⟨hmu.borel_le_caratheodory⟩
    let nu : Measure X := @OuterMeasure.toMeasure X mu.caratheodory mu le_rfl
    have hnuS : nu S = mu S := MeasureTheory.toMeasure_apply mu le_rfl hS
    have hnuC : nu C = mu C := MeasureTheory.toMeasure_apply mu le_rfl hCcar
    have hmass_add' : nu S < nu C + δ := by
      rw [hnuS, hnuC]
      simpa only [muS, OuterMeasure.restrict_apply,
        inter_self, Set.inter_eq_left.mpr hCS] using hmass_add
    have hnuCfinite : nu C ≠ ∞ :=
      ne_top_of_le_ne_top (by simpa only [hnuS] using hSfinite.ne)
        (measure_mono hCS)
    have hdiff := measure_sdiff_lt_of_lt_add
      hCclosed.nullMeasurableSet hCS hnuCfinite hmass_add'
    have hSmeas : MeasurableSet S := hS
    have hSCmeas : MeasurableSet (S \ C) := hSmeas.diff hCcar
    have hnuSC : nu (S \ C) = mu (S \ C) :=
      MeasureTheory.toMeasure_apply mu le_rfl hSCmeas
    refine ⟨C, hCS, hCclosed, ?_⟩
    rwa [hnuSC] at hdiff

/-- Simon Theorem 1.17 for a real-valued function represented on the ambient
space.  Measurability is with respect to the outer measure's Carathéodory
sigma-algebra, exactly as in the source. -/
theorem IsBorelRegularOuterMeasure.exists_isClosed_continuousOn
    {mu : OuterMeasure X} (hmu : IsBorelRegularOuterMeasure mu)
    (hX : ClosedSetsAreGDelta X) {A : Set X}
    (hA : IsCaratheodoryMeasurable mu A) (hAfin : mu A < ∞)
    {f : X → ℝ} (hf : @Measurable X ℝ mu.caratheodory (borel ℝ) f)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ C : Set X, C ⊆ A ∧ IsClosed C ∧ mu (A \ C) < ε ∧ ContinuousOn f C := by
  letI : MeasurableSpace X := mu.caratheodory
  letI : OpensMeasurableSpace X := ⟨hmu.borel_le_caratheodory⟩
  let nu : Measure X := mu.toMeasure le_rfl
  have hreg : ∀ ⦃S : Set X⦄, MeasurableSet S → nu S ≠ ∞ →
      ∀ ⦃δ : ℝ≥0∞⦄, δ ≠ 0 →
        ∃ F : Set X, F ⊆ S ∧ IsClosed F ∧ nu (S \ F) < δ := by
    intro S hS hSfinite δ hδ
    have hSouter : mu S < ∞ := by
      rw [← MeasureTheory.toMeasure_apply mu le_rfl hS]
      exact hSfinite.lt_top
    obtain ⟨F, hFS, hFclosed, hFsmall⟩ :=
      hmu.exists_isClosed_sdiff_lt_of_finite hX hS hSouter hδ
    have hFborel : @MeasurableSet X (borel X) F := by
      letI : MeasurableSpace X := borel X
      letI : OpensMeasurableSpace X := ⟨le_rfl⟩
      exact hFclosed.measurableSet
    have hFcar : MeasurableSet F := hmu.borel_le_caratheodory F hFborel
    refine ⟨F, hFS, hFclosed, ?_⟩
    have hnuSF : nu (S \ F) = mu (S \ F) :=
      MeasureTheory.toMeasure_apply mu le_rfl (hS.diff hFcar)
    rwa [hnuSF]
  have hA' : MeasurableSet A := hA
  have hAfin' : nu A ≠ ∞ := by
    rw [MeasureTheory.toMeasure_apply mu le_rfl hA']
    exact hAfin.ne
  obtain ⟨C, hCA, hCclosed, hCsmall, hCcontinuous⟩ :=
    exists_isClosed_continuousOn_of_measurable nu hreg hA' hAfin' hf hε
  have hdiff : MeasurableSet (A \ C) := hA'.diff hCclosed.measurableSet
  refine ⟨C, hCA, hCclosed, ?_, hCcontinuous⟩
  rwa [MeasureTheory.toMeasure_apply mu le_rfl hdiff] at hCsmall

/-- Simon Theorem 1.17 in the literal source form, with `f` defined only on
the measurable set `A`.  The final continuity assertion is continuity of the
restriction along the inclusion `C ⊆ A`. -/
theorem IsBorelRegularOuterMeasure.simon_theorem_1_17
    {mu : OuterMeasure X} (hmu : IsBorelRegularOuterMeasure mu)
    (hX : ClosedSetsAreGDelta X) {A : Set X}
    (hA : IsCaratheodoryMeasurable mu A) (hAfin : mu A < ∞)
    (f : A → ℝ)
    (hf : @Measurable A ℝ
      (@Subtype.instMeasurableSpace X (fun x => x ∈ A) mu.caratheodory)
      (borel ℝ) f)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (C : Set X) (hCA : C ⊆ A),
      IsClosed C ∧ mu (A \ C) < ε ∧
        Continuous (fun x : C => f ⟨x.1, hCA x.2⟩) := by
  letI : MeasurableSpace X := mu.caratheodory
  have hAmeas : MeasurableSet A := hA
  have hf' : Measurable f := hf
  let g : X → ℝ := Function.extend ((↑) : A → X) f (fun _ => 0)
  have hg : Measurable g :=
    (MeasurableEmbedding.subtype_coe hAmeas).measurable_extend hf' measurable_const
  obtain ⟨C, hCA, hCclosed, hCsmall, hCcontinuous⟩ :=
    hmu.exists_isClosed_continuousOn hX hA hAfin hg hε
  refine ⟨C, hCA, hCclosed, hCsmall, ?_⟩
  have hgC : Continuous (fun x : C => g x) := hCcontinuous.restrict
  convert hgC using 1
  funext x
  have hext := Subtype.val_injective.extend_apply f (fun _ : X => (0 : ℝ))
    (⟨x.1, hCA x.2⟩ : A)
  exact hext.symm

end Poincare.SimonGMT.Chapter01
