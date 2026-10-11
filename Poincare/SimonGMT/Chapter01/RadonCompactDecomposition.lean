module

public import Poincare.SimonGMT.Chapter01.RadonLocalMeasurability

@[expose] public section

/-!
# Compact-support decompositions for general Radon measures

These localization lemmas do not assume sigma-finiteness.  The supports
of an almost-disjoint family of positive compact pieces meet each compact
set in only countably many members.  This is the countability needed for
local gluing; the family itself is allowed to be uncountable.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.Regular]

omit [T2Space X] [BorelSpace X] [μ.Regular] in
/-- A maximal almost-disjoint family of positive-measure compact sets.
Maximality is with respect to adjoining another positive compact set. -/
theorem exists_maximal_aedisjoint_compacts :
    ∃ F : Set (Set X),
      (∀ K ∈ F, IsCompact K ∧ 0 < μ K) ∧ F.Pairwise (AEDisjoint μ) ∧
      ∀ K : Set X, IsCompact K → 0 < μ K →
        (∀ J ∈ F, AEDisjoint μ K J) → K ∈ F := by
  classical
  let P : Set (Set (Set X)) := {F |
    (∀ K ∈ F, IsCompact K ∧ 0 < μ K) ∧ F.Pairwise (AEDisjoint μ)}
  obtain ⟨F, hF⟩ := zorn_subset P (by
    intro c hc hchain
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => subset_sUnion_of_mem hs⟩
    · intro K hK
      obtain ⟨s, hs, hKs⟩ := mem_sUnion.mp hK
      exact (hc hs).1 K hKs
    · intro K hK J hJ hne
      obtain ⟨s, hs, hKs⟩ := mem_sUnion.mp hK
      obtain ⟨t, ht, hJt⟩ := mem_sUnion.mp hJ
      obtain ⟨w, hw, hsw, htw⟩ := hchain.directedOn s hs t ht
      exact (hc hw).2 (hsw hKs) (htw hJt) hne)
  refine ⟨F, hF.1.1, hF.1.2, ?_⟩
  intro K hK hKpos hdisj
  have hP : insert K F ∈ P := by
    constructor
    · intro J hJ
      rcases mem_insert_iff.mp hJ with rfl | hJ
      · exact ⟨hK, hKpos⟩
      · exact hF.1.1 J hJ
    · intro A hA B hB hne
      rcases mem_insert_iff.mp hA with rfl | hAF
      · rcases mem_insert_iff.mp hB with rfl | hBF
        · exact (hne rfl).elim
        · exact hdisj B hBF
      · rcases mem_insert_iff.mp hB with rfl | hBF
        · exact (hdisj A hAF).symm
        · exact hF.1.2 hAF hBF hne
  exact hF.2 hP (subset_insert K F) (mem_insert K F)

omit [μ.Regular] in
/-- The support of the restriction to a compact set is still contained
in that compact set. -/
theorem support_restrict_subset_of_isCompact {K : Set X} (hK : IsCompact K) :
    (μ.restrict K).support ⊆ K :=
  Measure.support_subset_of_isClosed hK.isClosed (ae_restrict_mem hK.measurableSet)

/-- Removing the support of a restricted compact piece removes only a
null subset of that piece. -/
theorem measure_sdiff_support_restrict_eq_zero {K : Set X} (hK : IsCompact K) :
    μ (K \ (μ.restrict K).support) = 0 := by
  let : (μ.restrict K).Regular :=
    Measure.Regular.restrict_of_measure_ne_top hK.measure_lt_top.ne
  have h := Measure.measure_compl_support_of_regular (μ := μ.restrict K)
  rw [Measure.restrict_apply Measure.isClosed_support.measurableSet.compl] at h
  simpa only [sdiff_eq, inter_comm] using h

variable [LocallyCompactSpace X]

/-- In an arbitrary locally compact space, only countably many supports
from an almost-disjoint compact family can meet a fixed compact set. -/
theorem countable_restricted_supports_meeting_compact
    {ι : Type v} (K : ι → Set X) (hK : ∀ i, IsCompact (K i))
    (hdisj : Pairwise (AEDisjoint μ on K))
    {C : Set X} (hC : IsCompact C) :
    {i | ((μ.restrict (K i)).support ∩ C).Nonempty}.Countable := by
  obtain ⟨U, hU, hCU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hC
  have hUfin : μ U < ∞ := (measure_mono subset_closure).trans_lt hUc.measure_lt_top
  let : Fact (μ U < ∞) := ⟨hUfin⟩
  have hc := Measure.countable_meas_pos_of_disjoint_iUnion₀
    (μ := μ.restrict U) (fun i => (hK i).measurableSet.nullMeasurableSet)
    (fun i j hij => (hdisj hij).of_le Measure.restrict_le_self)
  apply hc.mono
  intro i hi
  obtain ⟨x, hxs, hxC⟩ := hi
  have hp := (Measure.mem_support_iff_forall x).mp hxs U (hU.mem_nhds (hCU hxC))
  rw [Measure.restrict_apply hU.measurableSet] at hp
  change 0 < (μ.restrict U) (K i)
  rw [Measure.restrict_apply (hK i).measurableSet, inter_comm]
  exact hp

/-- The union of the supports of an almost-disjoint compact family is
Borel on every compact set.  The full union is not asserted to be Borel. -/
theorem measurableSet_restricted_supports_iUnion_inter_compact
    {ι : Type v} (K : ι → Set X) (hK : ∀ i, IsCompact (K i))
    (hdisj : Pairwise (AEDisjoint μ on K))
    {C : Set X} (hC : IsCompact C) :
    MeasurableSet ((⋃ i, (μ.restrict (K i)).support) ∩ C) := by
  let J : Set ι := {i | ((μ.restrict (K i)).support ∩ C).Nonempty}
  have hJ : J.Countable := countable_restricted_supports_meeting_compact μ K hK hdisj hC
  have heq : (⋃ i, (μ.restrict (K i)).support) ∩ C =
      ⋃ i ∈ J, (μ.restrict (K i)).support ∩ C := by
    ext x
    constructor
    · rintro ⟨hx, hxC⟩
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨⟨x, hxi, hxC⟩, hxi, hxC⟩⟩
    · intro hx
      obtain ⟨i, _, hxi, hxC⟩ := mem_iUnion₂.mp hx
      exact ⟨mem_iUnion.mpr ⟨i, hxi⟩, hxC⟩
  rw [heq]
  exact MeasurableSet.biUnion hJ fun _ _ =>
    Measure.isClosed_support.measurableSet.inter hC.measurableSet

/-- The possibly uncountable union of restricted supports is measurable
for the full Carathéodory sigma-algebra. -/
theorem isCaratheodory_restricted_supports_iUnion
    {ι : Type v} (K : ι → Set X) (hK : ∀ i, IsCompact (K i))
    (hdisj : Pairwise (AEDisjoint μ on K)) :
    μ.toOuterMeasure.IsCaratheodory (⋃ i, (μ.restrict (K i)).support) := by
  apply (isRadonOuterMeasure_toOuterMeasure μ).isCaratheodory_of_inter_isCompact
  intro C hC
  exact le_toOuterMeasure_caratheodory μ _
    (measurableSet_restricted_supports_iUnion_inter_compact μ K hK hdisj hC)

/-- Maximal almost-disjoint compact pieces have supports covering almost
all of every compact set.  This is a local conullness statement; it does
not conflate local nullness with global nullness for an infinite measure. -/
theorem maximal_aedisjoint_compacts_cover_compact_ae
    (F : Set (Set X)) (hF : ∀ K ∈ F, IsCompact K ∧ 0 < μ K)
    (hdisj : F.Pairwise (AEDisjoint μ))
    (hmax : ∀ K : Set X, IsCompact K → 0 < μ K →
      (∀ J ∈ F, AEDisjoint μ K J) → K ∈ F)
    {C : Set X} (hC : IsCompact C) :
    μ (C \ ⋃ K : F, (μ.restrict K.val).support) = 0 := by
  let S : Set X := ⋃ K : F, (μ.restrict K.val).support
  have hfamily : Pairwise (AEDisjoint μ on fun K : F => K.val) := by
    intro K J hne
    exact hdisj K.property J.property (fun h => hne (Subtype.ext h))
  have hS : μ.toOuterMeasure.IsCaratheodory S :=
    isCaratheodory_restricted_supports_iUnion μ (fun K : F => K.val)
      (fun K => (hF K.val K.property).1) hfamily
  have hCS : μ.toOuterMeasure.IsCaratheodory (C \ S) :=
    μ.toOuterMeasure.isCaratheodory_sdiff
      (le_toOuterMeasure_caratheodory μ C hC.measurableSet) hS
  by_contra hnonzero
  have hpos : 0 < μ.toOuterMeasure (C \ S) := pos_iff_ne_zero.mpr hnonzero
  rw [(isRadonOuterMeasure_toOuterMeasure μ).simon_lemma_4_7 hCS
    ((measure_mono sdiff_subset).trans_lt hC.measure_lt_top)] at hpos
  simp only [lt_iSup_iff] at hpos
  obtain ⟨J, hJCS, hJ, hJpos⟩ := hpos
  have hdisjoint (K : Set X) (hK : K ∈ F) : AEDisjoint μ J K := by
    apply measure_mono_null _ (measure_sdiff_support_restrict_eq_zero μ (hF K hK).1)
    rintro x ⟨hxJ, hxK⟩
    refine ⟨hxK, fun hxs => (hJCS hxJ).2 ?_⟩
    exact mem_iUnion.mpr ⟨⟨K, hK⟩, hxs⟩
  have hJF : J ∈ F := hmax J hJ hJpos hdisjoint
  have hzero : μ J = 0 := by simpa [AEDisjoint] using hdisjoint J hJF
  exact hJpos.ne' hzero

/-- An arbitrary locally finite Radon measure admits compact pieces whose
supports form a compact-locally countable, compact-locally conull family.
The index type need not be countable and no global null remainder is claimed. -/
theorem exists_compact_support_local_decomposition :
    ∃ (ι : Type u) (K : ι → Set X),
      (∀ i, IsCompact (K i) ∧ 0 < μ (K i)) ∧
      Pairwise (AEDisjoint μ on K) ∧
      (∀ C : Set X, IsCompact C →
        {i | ((μ.restrict (K i)).support ∩ C).Nonempty}.Countable) ∧
      (∀ C : Set X, IsCompact C →
        μ (C \ ⋃ i, (μ.restrict (K i)).support) = 0) := by
  obtain ⟨F, hF, hdisj, hmax⟩ := exists_maximal_aedisjoint_compacts μ
  have hfam : Pairwise (AEDisjoint μ on fun K : F => K.val) := by
    intro K J hne
    exact hdisj K.property J.property (fun h => hne (Subtype.ext h))
  refine ⟨F, Subtype.val, fun K => hF K.val K.property, hfam, ?_, ?_⟩
  · intro C hC
    exact countable_restricted_supports_meeting_compact μ Subtype.val
      (fun K => (hF K.val K.property).1) hfam hC
  · intro C hC
    exact maximal_aedisjoint_compacts_cover_compact_ae μ F hF hdisj hmax hC

end Poincare.SimonGMT.Chapter01
