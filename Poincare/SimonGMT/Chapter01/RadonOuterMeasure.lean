module

public import Mathlib.MeasureTheory.Measure.Content
public import Poincare.SimonGMT.Chapter01.ExactRegularity

public section

/-!
# Simon GMT, Chapter 1, Definition 4.6 and Lemmas 4.7–4.9

Simon's Radon measures are outer measures.  Their measurable sets are the
Caratheodory measurable sets, not just the Borel sets.  This file retains that
distinction and proves the equivalence with regular Borel measures.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Simon Definition 4.6: the three defining conditions (R1), (R2), (R3)
on an outer measure.  The results below assume the source's Hausdorff condition. -/
structure IsRadonOuterMeasure (μ : OuterMeasure X) : Prop where
  borel_regular : IsBorelRegularOuterMeasure μ
  finite_compacts : ∀ ⦃K : Set X⦄, IsCompact K → μ K < ∞
  outer_regular : ∀ A : Set X,
    μ A = ⨅ (U : Set X) (_ : A ⊆ U) (_ : IsOpen U), μ U
  inner_regular : ∀ ⦃U : Set X⦄, IsOpen U →
    μ U = ⨆ (K : Set X) (_ : K ⊆ U) (_ : IsCompact K), μ K

/-- Restricting a Simon Radon outer measure to the Borel sets gives a regular
Borel measure, with no local compactness or countability assumption. -/
theorem IsRadonOuterMeasure.toBorelMeasure_regular
    {μ : OuterMeasure X} (hμ : IsRadonOuterMeasure μ) :
    @Measure.Regular X (borel X) _ hμ.borel_regular.toBorelMeasure := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let ν := hμ.borel_regular.toBorelMeasure
  have hν : ∀ A : Set X, ν A = μ A := hμ.borel_regular.toBorelMeasure_apply_all
  let : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => by
    rw [hν]
    exact hμ.finite_compacts hK⟩
  let : ν.OuterRegular := ⟨fun A _ r hr => by
    rw [hν, hμ.outer_regular] at hr
    simp only [iInf_lt_iff] at hr
    obtain ⟨U, hAU, hU, hr⟩ := hr
    exact ⟨U, hAU, hU, by rwa [hν]⟩⟩
  refine ⟨fun U hU r hr => ?_⟩
  rw [hν, hμ.inner_regular hU] at hr
  simp only [lt_iSup_iff] at hr
  obtain ⟨K, hKU, hK, hr⟩ := hr
  exact ⟨K, hKU, hK, by rwa [hν]⟩

/-- Conversely, the canonical outer measure of a regular Borel measure
satisfies all of Simon's Radon conditions. -/
theorem isRadonOuterMeasure_toOuterMeasure [MeasurableSpace X] [BorelSpace X]
    [T2Space X] (ν : Measure X) [ν.Regular] :
    IsRadonOuterMeasure ν.toOuterMeasure where
  borel_regular := measure_toOuterMeasure_isBorelRegular ν
  finite_compacts := fun _ hK => hK.measure_lt_top
  outer_regular := fun A => A.measure_eq_iInf_isOpen ν
  inner_regular := fun _ hU => hU.measure_eq_iSup_isCompact ν

/-- The source Radon conditions on a measure's canonical outer measure
imply Mathlib regularity on its original sigma-algebra. -/
theorem IsRadonOuterMeasure.regular_of_toOuterMeasure [MeasurableSpace X]
    {ν : Measure X} (hν : IsRadonOuterMeasure ν.toOuterMeasure) : ν.Regular := by
  let : IsFiniteMeasureOnCompacts ν := ⟨hν.finite_compacts⟩
  let : ν.OuterRegular := ⟨fun A _ r hr => by
    change ν.toOuterMeasure A < r at hr
    rw [hν.outer_regular] at hr
    simp only [iInf_lt_iff] at hr
    obtain ⟨U, hAU, hU, hr⟩ := hr
    exact ⟨U, hAU, hU, hr⟩⟩
  refine ⟨fun U hU r hr => ?_⟩
  change r < ν.toOuterMeasure U at hr
  rw [hν.inner_regular hU] at hr
  simp only [lt_iSup_iff] at hr
  obtain ⟨K, hKU, hK, hr⟩ := hr
  exact ⟨K, hKU, hK, hr⟩

/-- Exact agreement between Definition 4.6 and the regular-measure class
used by the pre-existing `IsRadonMeasure` API, for Borel measures. -/
theorem isRadonOuterMeasure_toOuterMeasure_iff [MeasurableSpace X] [BorelSpace X]
    [T2Space X] (ν : Measure X) :
    IsRadonOuterMeasure ν.toOuterMeasure ↔ ν.Regular := by
  constructor
  · exact IsRadonOuterMeasure.regular_of_toOuterMeasure
  · intro hν
    exact isRadonOuterMeasure_toOuterMeasure ν

/-- Simon Lemma 4.7 for every finite Caratheodory-measurable set, including
sets which are not Borel. -/
theorem IsRadonOuterMeasure.simon_lemma_4_7 [T2Space X]
    {μ : OuterMeasure X} (hμ : IsRadonOuterMeasure μ)
    {A : Set X} (hA : IsCaratheodoryMeasurable μ A) (hAfin : μ A < ∞) :
    μ A = ⨆ (K : Set X) (_ : K ⊆ A) (_ : IsCompact K), μ K := by
  obtain ⟨B, hBA, hB, _, hμB⟩ :=
    hμ.borel_regular.exists_borel_subset_mod_null_of_lt_top hA hAfin
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let : Measure.Regular hμ.borel_regular.toBorelMeasure := hμ.toBorelMeasure_regular
  have hBfinite : hμ.borel_regular.toBorelMeasure B ≠ ∞ := by
    rw [hμ.borel_regular.toBorelMeasure_apply_all, hμB]
    exact hAfin.ne
  have hinner : μ B = ⨆ (K : Set X) (_ : K ⊆ B) (_ : IsCompact K), μ K := by
    simpa only [hμ.borel_regular.toBorelMeasure_apply_all] using
      hB.measure_eq_iSup_isCompact_of_ne_top hBfinite
  apply le_antisymm
  · rw [← hμB, hinner]
    refine iSup_le fun K => iSup_le fun hKB => iSup_le fun hK => ?_
    exact le_iSup_of_le K <| le_iSup_of_le (hKB.trans hBA) <|
      le_iSup_of_le hK le_rfl
  · exact iSup_le fun K => iSup_le fun hKA => iSup_le fun _ => μ.mono hKA

/-- A finite, finitely additive restriction of an outer measure to compact
sets is a content.  This is the construction used in Simon Lemma 4.8. -/
noncomputable def compactContent (μ : OuterMeasure X)
    (hfin : ∀ ⦃K : Set X⦄, IsCompact K → μ K < ∞)
    (hadd : ∀ ⦃K L : Set X⦄, IsCompact K → IsCompact L → Disjoint K L →
      μ (K ∪ L) = μ K + μ L) : Content X where
  toFun := fun K => (μ K).toNNReal
  mono' := fun K L hKL => ENNReal.toNNReal_mono (hfin L.isCompact).ne (μ.mono hKL)
  sup_disjoint' := fun K L hd _ _ => by
    change (μ ((K : Set X) ∪ L)).toNNReal = _
    rw [hadd K.isCompact L.isCompact hd,
      ENNReal.toNNReal_add (hfin K.isCompact).ne (hfin L.isCompact).ne]
  sup_le' := fun K L => by
    rw [← ENNReal.toNNReal_add (hfin K.isCompact).ne (hfin L.isCompact).ne]
    exact ENNReal.toNNReal_mono
      (ENNReal.add_ne_top.mpr ⟨(hfin K.isCompact).ne, (hfin L.isCompact).ne⟩)
      (measure_union_le (K : Set X) L)

@[simp] theorem compactContent_apply (μ : OuterMeasure X)
    (hfin : ∀ ⦃K : Set X⦄, IsCompact K → μ K < ∞)
    (hadd : ∀ ⦃K L : Set X⦄, IsCompact K → IsCompact L → Disjoint K L →
      μ (K ∪ L) = μ K + μ L) (K : Compacts X) :
    compactContent μ hfin hadd K = μ K :=
  ENNReal.coe_toNNReal (hfin K.isCompact).ne

/-- Simon Lemma 4.8: (R2), (R3), and finite additivity on disjoint compact
sets imply the full Radon definition, on an arbitrary Hausdorff space. -/
theorem simon_lemma_4_8 [T2Space X] (μ : OuterMeasure X)
    (houter : ∀ A : Set X,
      μ A = ⨅ (U : Set X) (_ : A ⊆ U) (_ : IsOpen U), μ U)
    (hinner : ∀ ⦃U : Set X⦄, IsOpen U →
      μ U = ⨆ (K : Set X) (_ : K ⊆ U) (_ : IsCompact K), μ K)
    (haddfin : ∀ ⦃K L : Set X⦄, IsCompact K → IsCompact L → Disjoint K L →
      μ (K ∪ L) = μ K + μ L ∧ μ K + μ L < ∞) :
    IsRadonOuterMeasure μ := by
  have hfin : ∀ ⦃K : Set X⦄, IsCompact K → μ K < ∞ := by
    intro K hK
    simpa using (haddfin hK isCompact_empty (disjoint_empty K)).2
  let c := compactContent μ hfin (fun {_ _} hK hL hd => (haddfin hK hL hd).1)
  have hc : ∀ U : Opens X, c.innerContent U = μ U := by
    intro U
    rw [hinner U.isOpen, Content.innerContent]
    apply le_antisymm
    · refine iSup_le fun K => iSup_le fun hKU => ?_
      rw [compactContent_apply]
      exact le_iSup_of_le (K : Set X) <| le_iSup_of_le hKU <|
        le_iSup_of_le K.isCompact le_rfl
    · refine iSup_le fun K => iSup_le fun hKU => iSup_le fun hK => ?_
      exact le_iSup_of_le (⟨K, hK⟩ : Compacts X) <| le_iSup_of_le hKU <| by
        rw [compactContent_apply]
        exact le_rfl
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  have hmeasure : c.measure.toOuterMeasure = μ := by
    ext A
    change c.measure A = μ A
    rw [A.measure_eq_iInf_isOpen c.measure, houter A]
    apply iInf_congr fun U => iInf_congr fun _ => iInf_congr fun hU => ?_
    rw [c.measure_apply hU.measurableSet, c.outerMeasure_of_isOpen U hU, hc]
    rfl
  refine ⟨?_, hfin, houter, hinner⟩
  rw [← hmeasure]
  exact measure_toOuterMeasure_isBorelRegular c.measure

/-- The exact topological hypothesis in Simon Lemma 4.9. -/
@[expose] def OpenSetsAreSigmaCompact (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ ⦃U : Set X⦄, IsOpen U → IsSigmaCompact U

/-- Public interface for the topological hypothesis of Lemma 4.9. -/
theorem openSetsAreSigmaCompact_iff :
    OpenSetsAreSigmaCompact X ↔ ∀ ⦃U : Set X⦄, IsOpen U → IsSigmaCompact U :=
  Iff.rfl

/-- The De Morgan implication used in Simon's proof of Lemma 4.9. -/
theorem OpenSetsAreSigmaCompact.closedSetsAreGDelta [T2Space X]
    (hX : OpenSetsAreSigmaCompact X) : ClosedSetsAreGDelta X := by
  apply closedSetsAreGDelta_iff.mpr
  intro C hC
  obtain ⟨K, hK, hcover⟩ := hX hC.isOpen_compl
  have heq : C = ⋂ n, (K n)ᶜ := by
    rw [← compl_iUnion, hcover, compl_compl]
  rw [heq]
  exact IsGδ.iInter_of_isOpen fun n => (hK n).isClosed.isOpen_compl

/-- In a sigma-compact locally compact Hausdorff space, finiteness on
compacts supplies Simon's countable open finite-measure cover. -/
theorem isOpenSigmaFinite_of_finite_compacts [T2Space X] [LocallyCompactSpace X]
    [SigmaCompactSpace X] {μ : OuterMeasure X}
    (hfin : ∀ ⦃K : Set X⦄, IsCompact K → μ K < ∞) : IsOpenSigmaFinite μ := by
  obtain ⟨K, hK, hcover⟩ := isSigmaCompact_univ (X := X)
  choose V hV hKV hVc using fun n =>
    exists_isOpen_superset_and_isCompact_closure (hK n)
  apply (isOpenSigmaFinite_iff μ).2
  refine ⟨V, fun n => ⟨hV n, (μ.mono subset_closure).trans_lt (hfin (hVc n))⟩, ?_⟩
  apply subset_antisymm (subset_univ _)
  rw [← hcover]
  exact iUnion_mono hKV

/-- Simon Lemma 4.9 with precisely the source hypothesis that every open
set is a countable union of compact subsets. -/
theorem simon_lemma_4_9 [T2Space X] [LocallyCompactSpace X]
    (hX : OpenSetsAreSigmaCompact X) {μ : OuterMeasure X}
    (hμ : IsBorelRegularOuterMeasure μ)
    (hfin : ∀ ⦃K : Set X⦄, IsCompact K → μ K < ∞) :
    IsRadonOuterMeasure μ := by
  let : SigmaCompactSpace X := ⟨hX isOpen_univ⟩
  have hopen := isOpenSigmaFinite_of_finite_compacts hfin
  have hG := hX.closedSetsAreGDelta
  refine ⟨hμ, hfin, hμ.measure_eq_iInf_isOpen_of_closedSetsAreGDelta hopen hG, ?_⟩
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  have hinner : Measure.InnerRegularWRT hμ.toBorelMeasure IsCompact IsOpen :=
    (Measure.InnerRegularWRT.isCompact_isClosed hμ.toBorelMeasure).trans
      (innerRegularWRT_isClosed_isOpen_of_closedSetsAreGDelta hμ.toBorelMeasure hG)
  intro U hU
  simpa only [hμ.toBorelMeasure_apply_all] using hinner.measure_eq_iSup hU

/-- The measure on the full Caratheodory sigma-algebra belonging to a Simon
Radon outer measure.  This is the measure used in the literal `Lᵖ(μ)` statement. -/
noncomputable abbrev IsRadonOuterMeasure.toCaratheodoryMeasure
    {μ : OuterMeasure X} (_hμ : IsRadonOuterMeasure μ) :
    @Measure X μ.caratheodory :=
  @OuterMeasure.toMeasure X μ.caratheodory μ le_rfl

/-- The Caratheodory measure agrees with the original outer measure on all
sets, since the latter has equal-measure Borel hulls. -/
theorem IsRadonOuterMeasure.toCaratheodoryMeasure_apply_all
    {μ : OuterMeasure X} (hμ : IsRadonOuterMeasure μ) (A : Set X) :
    hμ.toCaratheodoryMeasure A = μ A := by
  let : MeasurableSpace X := μ.caratheodory
  obtain ⟨B, hAB, hB, hμB⟩ := hμ.borel_regular.exists_borel_superset A
  apply le_antisymm
  · calc
      hμ.toCaratheodoryMeasure A ≤ hμ.toCaratheodoryMeasure B := measure_mono hAB
      _ = μ B := toMeasure_apply μ le_rfl (hμ.borel_regular.borel_le_caratheodory B hB)
      _ = μ A := hμB
  · exact le_toMeasure_apply μ le_rfl A

/-- The measure on the full Caratheodory sigma-algebra is regular as well;
no replacement of completed-measurable functions by Borel functions is needed. -/
theorem IsRadonOuterMeasure.toCaratheodoryMeasure_regular
    {μ : OuterMeasure X} (hμ : IsRadonOuterMeasure μ) :
    @Measure.Regular X μ.caratheodory _ hμ.toCaratheodoryMeasure := by
  let : MeasurableSpace X := μ.caratheodory
  let ν := hμ.toCaratheodoryMeasure
  have hν : ∀ A : Set X, ν A = μ A := hμ.toCaratheodoryMeasure_apply_all
  let : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => by
    rw [hν]
    exact hμ.finite_compacts hK⟩
  let : ν.OuterRegular := ⟨fun A _ r hr => by
    rw [hν, hμ.outer_regular] at hr
    simp only [iInf_lt_iff] at hr
    obtain ⟨U, hAU, hU, hr⟩ := hr
    exact ⟨U, hAU, hU, by rwa [hν]⟩⟩
  refine ⟨fun U hU r hr => ?_⟩
  rw [hν, hμ.inner_regular hU] at hr
  simp only [lt_iSup_iff] at hr
  obtain ⟨K, hKU, hK, hr⟩ := hr
  exact ⟨K, hKU, hK, by rwa [hν]⟩

end Poincare.SimonGMT.Chapter01
