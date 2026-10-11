module

public import Poincare.SimonGMT.Chapter01.RegularityCompletion

public section

/-!
# Simon GMT, Chapter 1, exact regularity hypotheses

Simon Theorem 1.15 assumes only that every closed set is a countable
intersection of open sets.  This file proves the regularity conclusions under
that hypothesis, without adding metrizability or second countability.
-/

open Filter Set
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The topological hypothesis in Simon Theorem 1.15: every closed subset is
a `G_delta` set. -/
@[expose] def ClosedSetsAreGDelta (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ ⦃C : Set X⦄, IsClosed C → IsGδ C

/-- Public introduction and elimination interface for the topological
hypothesis in Simon Theorem 1.15. -/
theorem closedSetsAreGDelta_iff :
    ClosedSetsAreGDelta X ↔ ∀ ⦃C : Set X⦄, IsClosed C → IsGδ C :=
  Iff.rfl

/-- If every closed set is `G_delta`, every open set is an increasing union of
closed sets.  Hence every measure is inner regular on open sets with respect
to closed subsets.  This is the topological core of Simon Theorem 1.15. -/
theorem innerRegularWRT_isClosed_isOpen_of_closedSetsAreGDelta
    [MeasurableSpace X] (nu : MeasureTheory.Measure X)
    (hX : ClosedSetsAreGDelta X) :
    MeasureTheory.Measure.InnerRegularWRT nu IsClosed IsOpen := by
  intro U hU r hr
  obtain ⟨V, hVopen, hUV⟩ := (hX hU.isClosed_compl).eq_iInter_nat
  let F : ℕ → Set X := fun n => ⋃ i ∈ Finset.range n, (V i)ᶜ
  have hFclosed : ∀ n, IsClosed (F n) := by
    intro n
    exact isClosed_biUnion_finset fun i _ => (hVopen i).isClosed_compl
  have hFmono : Monotone F := by
    intro m n hmn x hx
    simp only [F, mem_iUnion, Finset.mem_range, mem_compl_iff] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨i, hi.trans_le hmn, hxi⟩
  have hFUnion : ⋃ n, F n = U := by
    rw [← compl_compl U, hUV, compl_iInter]
    ext x
    simp only [F, mem_iUnion, Finset.mem_range, mem_compl_iff]
    constructor
    · rintro ⟨n, i, hi, hxi⟩
      exact ⟨i, hxi⟩
    · rintro ⟨i, hxi⟩
      exact ⟨i + 1, i, Nat.lt_succ_self i, hxi⟩
  rw [← hFUnion, hFmono.measure_iUnion] at hr
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hr
  exact ⟨F n, (subset_iUnion F n).trans_eq hFUnion, hFclosed n, hn⟩

/-- A Borel measure with an open countable finite-measure cover is weakly
regular whenever closed sets are `G_delta`.  Each finite restriction is weakly
regular by the finite-measure complement argument; outer regularity then
glues across the open cover. -/
theorem weaklyRegular_of_closedSetsAreGDelta_of_open_cover
    [MeasurableSpace X] [BorelSpace X]
    (nu : MeasureTheory.Measure X) (hX : ClosedSetsAreGDelta X)
    (V : ℕ → Set X) (hVopen : ∀ n, IsOpen (V n))
    (hVfinite : ∀ n, nu (V n) < ∞) (hcover : Set.univ ⊆ ⋃ n, V n) :
    MeasureTheory.Measure.WeaklyRegular nu := by
  have hrestrict : ∀ n,
      MeasureTheory.Measure.OuterRegular (nu.restrict (V n)) := by
    intro n
    letI : Fact (nu (V n) < ∞) := ⟨hVfinite n⟩
    letI : MeasureTheory.IsFiniteMeasure (nu.restrict (V n)) := by infer_instance
    exact
      ((innerRegularWRT_isClosed_isOpen_of_closedSetsAreGDelta
        (nu.restrict (V n)) hX).weaklyRegular_of_finite _).toOuterRegular
  letI : MeasureTheory.Measure.OuterRegular nu :=
    MeasureTheory.Measure.OuterRegular.of_restrict
      hrestrict hVopen hcover
  exact ⟨innerRegularWRT_isClosed_isOpen_of_closedSetsAreGDelta nu hX⟩

/-- The Borel measure associated to a Simon Borel-regular outer measure is
weakly regular under the exact hypotheses of Theorem 1.15. -/
theorem IsBorelRegularOuterMeasure.toBorelMeasure_weaklyRegular_of_closedSetsAreGDelta
    {mu : MeasureTheory.OuterMeasure X} (hmu : IsBorelRegularOuterMeasure mu)
    (hopen : IsOpenSigmaFinite mu) (hX : ClosedSetsAreGDelta X) :
    @MeasureTheory.Measure.WeaklyRegular X (borel X) _ hmu.toBorelMeasure := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  obtain ⟨V, hV, hcover⟩ := (isOpenSigmaFinite_iff mu).mp hopen
  apply weaklyRegular_of_closedSetsAreGDelta_of_open_cover
    hmu.toBorelMeasure hX V (fun n => (hV n).1)
  · intro n
    simpa only [hmu.toBorelMeasure_apply_all] using (hV n).2
  · rw [hcover]

/-- Simon Theorem 1.15(1), with precisely the source hypothesis that closed
sets are countable intersections of open sets. -/
theorem IsBorelRegularOuterMeasure.measure_eq_iInf_isOpen_of_closedSetsAreGDelta
    {mu : MeasureTheory.OuterMeasure X} (hmu : IsBorelRegularOuterMeasure mu)
    (hopen : IsOpenSigmaFinite mu) (hX : ClosedSetsAreGDelta X) (A : Set X) :
    mu A = ⨅ (U : Set X) (_ : A ⊆ U) (_ : IsOpen U), mu U := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  letI : MeasureTheory.Measure.WeaklyRegular hmu.toBorelMeasure :=
    hmu.toBorelMeasure_weaklyRegular_of_closedSetsAreGDelta hopen hX
  simpa only [hmu.toBorelMeasure_apply_all] using
    A.measure_eq_iInf_isOpen hmu.toBorelMeasure

/-- Simon Theorem 1.15(2), for every set measurable in the source's
Caratheodory sense and under exactly the source topological hypothesis. -/
theorem IsBorelRegularOuterMeasure.measure_eq_iSup_isClosed_of_closedSetsAreGDelta
    {mu : MeasureTheory.OuterMeasure X} (hmu : IsBorelRegularOuterMeasure mu)
    (hopen : IsOpenSigmaFinite mu) (hX : ClosedSetsAreGDelta X)
    {A : Set X} (hA : IsCaratheodoryMeasurable mu A) :
    mu A = ⨆ (C : Set X) (_ : C ⊆ A) (_ : IsClosed C), mu C := by
  obtain ⟨B, hBA, hB, _, hmuB⟩ :=
    hmu.exists_borel_subset_mod_null hopen hA
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  letI : MeasureTheory.Measure.WeaklyRegular hmu.toBorelMeasure :=
    hmu.toBorelMeasure_weaklyRegular_of_closedSetsAreGDelta hopen hX
  letI : MeasureTheory.SigmaFinite hmu.toBorelMeasure :=
    hmu.toBorelMeasure_sigmaFinite hopen
  have hinner : MeasureTheory.Measure.InnerRegularWRT hmu.toBorelMeasure
      IsClosed (@MeasurableSet X (borel X)) :=
    MeasureTheory.Measure.WeaklyRegular.innerRegular_measurable.trans
      MeasureTheory.Measure.InnerRegularWRT.of_sigmaFinite
  have hinnerB :
      mu B = ⨆ (C : Set X) (_ : C ⊆ B) (_ : IsClosed C), mu C := by
    simpa only [hmu.toBorelMeasure_apply_all] using hinner.measure_eq_iSup hB
  apply le_antisymm
  · rw [← hmuB, hinnerB]
    refine iSup_le fun C => iSup_le fun hCB => iSup_le fun hCclosed => ?_
    exact le_iSup_of_le C <|
      le_iSup_of_le (hCB.trans hBA) <| le_iSup_of_le hCclosed le_rfl
  · refine iSup_le fun C => iSup_le fun hCA => iSup_le fun _ => ?_
    exact mu.mono hCA

/-- Simon Theorem 1.15 in its two-part source form. -/
theorem IsBorelRegularOuterMeasure.simon_theorem_1_15
    {mu : MeasureTheory.OuterMeasure X} (hmu : IsBorelRegularOuterMeasure mu)
    (hopen : IsOpenSigmaFinite mu) (hX : ClosedSetsAreGDelta X) :
    (∀ A : Set X,
      mu A = ⨅ (U : Set X) (_ : A ⊆ U) (_ : IsOpen U), mu U) ∧
    (∀ A : Set X, IsCaratheodoryMeasurable mu A →
      mu A = ⨆ (C : Set X) (_ : C ⊆ A) (_ : IsClosed C), mu C) := by
  exact
    ⟨fun A => hmu.measure_eq_iInf_isOpen_of_closedSetsAreGDelta hopen hX A,
      fun _ hA => hmu.measure_eq_iSup_isClosed_of_closedSetsAreGDelta hopen hX hA⟩

/-- Simon Remark 1.16.  In a Hausdorff sigma-compact space, finite
Caratheodory-measurable sets are inner approximated by compact subsets. -/
theorem IsBorelRegularOuterMeasure.measure_eq_iSup_isCompact_of_closedSetsAreGDelta
    [T2Space X] [SigmaCompactSpace X]
    {mu : MeasureTheory.OuterMeasure X} (hmu : IsBorelRegularOuterMeasure mu)
    (hopen : IsOpenSigmaFinite mu) (hX : ClosedSetsAreGDelta X)
    {A : Set X} (hA : IsCaratheodoryMeasurable mu A) (hAfin : mu A < ∞) :
    mu A = ⨆ (K : Set X) (_ : K ⊆ A) (_ : IsCompact K), mu K := by
  obtain ⟨B, hBA, hB, _, hmuB⟩ :=
    hmu.exists_borel_subset_mod_null hopen hA
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  letI : MeasureTheory.Measure.WeaklyRegular hmu.toBorelMeasure :=
    hmu.toBorelMeasure_weaklyRegular_of_closedSetsAreGDelta hopen hX
  letI : MeasureTheory.SigmaFinite hmu.toBorelMeasure :=
    hmu.toBorelMeasure_sigmaFinite hopen
  have hclosed : MeasureTheory.Measure.InnerRegularWRT hmu.toBorelMeasure
      IsClosed (@MeasurableSet X (borel X)) :=
    MeasureTheory.Measure.WeaklyRegular.innerRegular_measurable.trans
      MeasureTheory.Measure.InnerRegularWRT.of_sigmaFinite
  have hcompact : MeasureTheory.Measure.InnerRegularWRT hmu.toBorelMeasure
      IsCompact (@MeasurableSet X (borel X)) :=
    (MeasureTheory.Measure.InnerRegularWRT.isCompact_isClosed
      hmu.toBorelMeasure).trans hclosed
  have hinnerB :
      mu B = ⨆ (K : Set X) (_ : K ⊆ B) (_ : IsCompact K), mu K := by
    simpa only [hmu.toBorelMeasure_apply_all] using hcompact.measure_eq_iSup hB
  have _hBfinite : mu B < ∞ := hmuB.trans_lt hAfin
  apply le_antisymm
  · rw [← hmuB, hinnerB]
    refine iSup_le fun K => iSup_le fun hKB => iSup_le fun hKcompact => ?_
    exact le_iSup_of_le K <|
      le_iSup_of_le (hKB.trans hBA) <| le_iSup_of_le hKcompact le_rfl
  · refine iSup_le fun K => iSup_le fun hKA => iSup_le fun _ => ?_
    exact mu.mono hKA

end Poincare.SimonGMT.Chapter01
