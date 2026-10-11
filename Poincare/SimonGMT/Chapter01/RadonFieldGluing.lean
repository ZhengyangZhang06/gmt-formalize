module

public import Poincare.SimonGMT.Chapter01.RadonCompactDecomposition

@[expose] public section

/-!
# Gluing fields on a compact-locally countable Radon decomposition

The index set in this file need not be countable.  Removing the overlaps
from each restricted compact support gives genuinely disjoint Borel pieces,
without changing any individual piece up to a null set.  The resulting
glued field is measurable for the full Carathéodory sigma-algebra.

All coverage assertions remain compact-local.  No union of uncountably many
null sets is asserted to be null.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u v w

section DisjointCore

variable {X : Type u} {ι : Type v}

/-- The points belonging to one member of a family and to no other member. -/
def disjointCore (S : ι → Set X) (i : ι) : Set X :=
  S i \ ⋃ (j : ι) (_ : j ≠ i), S j

theorem disjointCore_subset (S : ι → Set X) (i : ι) :
    disjointCore S i ⊆ S i := sdiff_subset

/-- Unique-membership cores are disjoint even for an uncountable family. -/
theorem pairwise_disjoint_disjointCore (S : ι → Set X) :
    Pairwise (Disjoint on disjointCore S) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  exact hxi.2 (mem_iUnion₂.mpr ⟨j, hij.symm, hxj.1⟩)

theorem disjointCore_eq_sdiff_biUnion (S : ι → Set X) (i : ι) :
    disjointCore S i =
      S i \ ⋃ j ∈ {j | j ≠ i ∧ (S j ∩ S i).Nonempty}, S j := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro h
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp h
    exact hx.2 (mem_iUnion₂.mpr ⟨j, hj.1, hxj⟩)
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro h
    obtain ⟨j, hji, hxj⟩ := mem_iUnion₂.mp h
    exact hx.2 (mem_iUnion₂.mpr ⟨j, ⟨hji, x, hxj, hx.1⟩, hxj⟩)

variable [MeasurableSpace X] {μ : Measure X}

/-- Countably many neighbors suffice for measurability of each core. -/
theorem measurableSet_disjointCore (S : ι → Set X)
    (hS : ∀ i, MeasurableSet (S i))
    (hcount : ∀ i, {j | (S j ∩ S i).Nonempty}.Countable) (i : ι) :
    MeasurableSet (disjointCore S i) := by
  rw [disjointCore_eq_sdiff_biUnion]
  exact (hS i).diff (MeasurableSet.biUnion
    ((hcount i).mono fun _ h => h.2) fun j _ => hS j)

/-- For an almost-disjoint family with countably many neighbors per piece,
passing to the unique-membership core discards a null set from that piece. -/
theorem disjointCore_ae_eq (S : ι → Set X)
    (hcount : ∀ i, {j | (S j ∩ S i).Nonempty}.Countable)
    (hdisj : Pairwise (AEDisjoint μ on S)) (i : ι) :
    disjointCore S i =ᵐ[μ] S i := by
  rw [disjointCore_eq_sdiff_biUnion]
  apply AEDisjoint.sdiff_ae_eq_left
  change μ (S i ∩ ⋃ j ∈ {j | j ≠ i ∧ (S j ∩ S i).Nonempty}, S j) = 0
  simp only [inter_iUnion]
  apply (measure_biUnion_null_iff ((hcount i).mono fun _ h => h.2)).mpr
  intro j hj
  exact hdisj hj.1.symm

end DisjointCore

section ChoiceGluing

variable {X : Type u} {ι : Type v} {Y : Type w}

/-- Glue fields on disjoint pieces, using a fixed value off their union.
The definition itself is meaningful without the disjointness hypothesis. -/
noncomputable def glueDisjointFields (D : ι → Set X) (f : ι → X → Y)
    (defaultValue : Y) (x : X) : Y := by
  classical
  exact if hx : ∃ i, x ∈ D i then f hx.choose x else defaultValue

theorem glueDisjointFields_of_mem (D : ι → Set X)
    (hD : Pairwise (Disjoint on D)) (f : ι → X → Y) (defaultValue : Y)
    {i : ι} {x : X} (hx : x ∈ D i) :
    glueDisjointFields D f defaultValue x = f i x := by
  classical
  have hex : ∃ i, x ∈ D i := ⟨i, hx⟩
  rw [glueDisjointFields, dite_eq_left hex]
  have hi : hex.choose = i := by
    by_contra hne
    exact (disjoint_left.mp (hD hne)) hex.choose_spec hx
  rw [hi]

theorem glueDisjointFields_of_notMem (D : ι → Set X)
    (f : ι → X → Y) (defaultValue : Y) {x : X}
    (hx : x ∉ ⋃ i, D i) :
    glueDisjointFields D f defaultValue x = defaultValue := by
  classical
  unfold glueDisjointFields
  apply dite_eq_right
  simpa only [mem_iUnion] using hx

/-- Any pointwise property common to the fields and the default survives
gluing, including a pointwise unit-ball or unit-sphere constraint. -/
theorem glueDisjointFields_property (D : ι → Set X) (f : ι → X → Y)
    (defaultValue : Y) {P : Y → Prop} (hdefault : P defaultValue)
    (hf : ∀ i x, x ∈ D i → P (f i x)) (x : X) :
    P (glueDisjointFields D f defaultValue x) := by
  classical
  unfold glueDisjointFields
  split
  · rename_i hx
    exact hf hx.choose x hx.choose_spec
  · exact hdefault

variable [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.Regular] [MeasurableSpace Y]

/-- Disjoint Borel pieces which are countable on every compact set support
global gluing into the full Carathéodory sigma-algebra.  The pieces need not
cover the space or form a countable family. -/
theorem measurable_glueDisjointFields (D : ι → Set X)
    (hD : ∀ i, MeasurableSet (D i)) (hdisj : Pairwise (Disjoint on D))
    (hcount : ∀ C : Set X, IsCompact C → {i | (D i ∩ C).Nonempty}.Countable)
    (f : ι → X → Y) (hf : ∀ i, Measurable (f i)) (defaultValue : Y) :
    @Measurable X Y μ.toOuterMeasure.caratheodory _
      (glueDisjointFields D f defaultValue) := by
  classical
  apply (isRadonOuterMeasure_toOuterMeasure μ).measurable_of_inter_isCompact
  intro C hC A hA
  let J : Set ι := {i | (D i ∩ C).Nonempty}
  have hJ : J.Countable := hcount C hC
  have hunion : MeasurableSet (⋃ i ∈ J, D i) :=
    MeasurableSet.biUnion hJ fun i _ => hD i
  have hpre : MeasurableSet (⋃ i ∈ J, D i ∩ C ∩ (f i ⁻¹' A)) :=
    MeasurableSet.biUnion hJ fun i _ => ((hD i).inter hC.measurableSet).inter (hf i hA)
  have heq : (glueDisjointFields D f defaultValue ⁻¹' A) ∩ C =
      (⋃ i ∈ J, D i ∩ C ∩ (f i ⁻¹' A)) ∪
        (if defaultValue ∈ A then C \ ⋃ i ∈ J, D i else ∅) := by
    ext x
    constructor
    · rintro ⟨hxA, hxC⟩
      by_cases hx : ∃ i, x ∈ D i
      · obtain ⟨i, hxi⟩ := hx
        apply Or.inl
        refine mem_iUnion₂.mpr ⟨i, ⟨x, hxi, hxC⟩, ⟨hxi, hxC⟩, ?_⟩
        simpa only [mem_preimage, glueDisjointFields_of_mem D hdisj f defaultValue hxi]
          using hxA
      · have hxu : x ∉ ⋃ i, D i := by simpa only [mem_iUnion] using hx
        have hd : defaultValue ∈ A := by
          simpa only [mem_preimage, glueDisjointFields_of_notMem D f defaultValue hxu]
            using hxA
        apply Or.inr
        rw [ite_eq_left hd]
        refine ⟨hxC, ?_⟩
        intro h
        obtain ⟨i, _, hxi⟩ := mem_iUnion₂.mp h
        exact hx ⟨i, hxi⟩
    · intro hx
      rcases hx with hx | hx
      · obtain ⟨i, _, ⟨hxi, hxC⟩, hxiA⟩ := mem_iUnion₂.mp hx
        refine ⟨?_, hxC⟩
        simpa only [mem_preimage, glueDisjointFields_of_mem D hdisj f defaultValue hxi]
          using hxiA
      · split_ifs at hx with hd
        · refine ⟨?_, hx.1⟩
          have hxu : x ∉ ⋃ i, D i := by
            intro h
            obtain ⟨i, hxi⟩ := mem_iUnion.mp h
            exact hx.2 (mem_iUnion₂.mpr ⟨i, ⟨x, hxi, hx.1⟩, hxi⟩)
          simpa only [mem_preimage, glueDisjointFields_of_notMem D f defaultValue hxu]
            using hd
        · exact hx.elim
  rw [heq]
  apply le_toOuterMeasure_caratheodory μ
  apply hpre.union
  split_ifs
  · exact hC.measurableSet.diff hunion
  · exact MeasurableSet.empty

end ChoiceGluing

section RadonDecomposition

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.Regular]
  {ι : Type v} (K : ι → Set X) (hK : ∀ i, IsCompact (K i))
  (hdisj : Pairwise (AEDisjoint μ on K))

include hK hdisj

/-- Restricted compact supports have only countably many neighbors. -/
theorem countable_restricted_support_neighbors (i : ι) :
    {j | ((μ.restrict (K j)).support ∩ (μ.restrict (K i)).support).Nonempty}.Countable := by
  apply (countable_restricted_supports_meeting_compact μ K hK hdisj (hK i)).mono
  rintro j ⟨x, hxj, hxi⟩
  exact ⟨x, hxj, support_restrict_subset_of_isCompact μ (hK i) hxi⟩

/-- Every core of a restricted compact support is Borel. -/
theorem measurableSet_restrictedSupportCore (i : ι) :
    MeasurableSet (disjointCore (fun j => (μ.restrict (K j)).support) i) :=
  measurableSet_disjointCore _ (fun _ => Measure.isClosed_support.measurableSet)
    (countable_restricted_support_neighbors μ K hK hdisj) i

/-- The Borel core agrees almost everywhere with the original compact piece.
This is an assertion about one piece at a time. -/
theorem restrictedSupportCore_ae_eq (i : ι) :
    disjointCore (fun j => (μ.restrict (K j)).support) i =ᵐ[μ] K i := by
  have hdisjS : Pairwise (AEDisjoint μ on fun j => (μ.restrict (K j)).support) := by
    intro j k hjk
    exact (hdisj hjk).mono (support_restrict_subset_of_isCompact μ (hK j))
      (support_restrict_subset_of_isCompact μ (hK k))
  apply (disjointCore_ae_eq _ (countable_restricted_support_neighbors μ K hK hdisj)
    hdisjS i).trans
  apply ae_eq_set.mpr
  constructor
  · rw [sdiff_eq_empty.mpr (support_restrict_subset_of_isCompact μ (hK i)), measure_empty]
  · exact measure_sdiff_support_restrict_eq_zero μ (hK i)

/-- Replacing each support by its disjoint core preserves compact-local
coverage.  Countable unions are taken only over the pieces meeting the
particular compact set. -/
theorem restrictedSupportCores_cover_compact_ae
    {C : Set X} (hC : IsCompact C)
    (hcover : μ (C \ ⋃ i, (μ.restrict (K i)).support) = 0) :
    μ (C \ ⋃ i, disjointCore (fun j => (μ.restrict (K j)).support) i) = 0 := by
  let S : ι → Set X := fun i => (μ.restrict (K i)).support
  let J : Set ι := {i | (S i ∩ C).Nonempty}
  have hJ : J.Countable := countable_restricted_supports_meeting_compact μ K hK hdisj hC
  have hae : ∀ᵐ x ∂μ, ∀ i ∈ J, x ∈ K i → x ∈ disjointCore S i := by
    apply (ae_ball_iff hJ).mpr
    intro i _
    filter_upwards [restrictedSupportCore_ae_eq μ K hK hdisj i] with x hx hxi
    exact hx.mpr hxi
  apply ae_le_set.mp
  filter_upwards [ae_le_set.mpr hcover, hae] with x hx hxi hxC
  obtain ⟨i, hxs⟩ := mem_iUnion.mp (hx hxC)
  exact mem_iUnion.mpr ⟨i, hxi i ⟨x, hxs, hxC⟩
    (support_restrict_subset_of_isCompact μ (hK i) hxs)⟩

/-- Borel fields on the finite compact pieces have a single Carathéodory
measurable gluing, agreeing with each field almost everywhere on its piece.
No compatibility or countability of the whole family is required because
the compact pieces are almost disjoint. -/
theorem exists_measurable_gluing_on_compact_supports
    {Y : Type w} [MeasurableSpace Y] (f : ι → X → Y)
    (hf : ∀ i, Measurable (f i)) (defaultValue : Y) :
    ∃ ν : X → Y,
      @Measurable X Y μ.toOuterMeasure.caratheodory _ ν ∧
      (∀ i, ν =ᵐ[μ.restrict (K i)] f i) ∧
      ∀ x, ν x = defaultValue ∨ ∃ i, x ∈ K i ∧ ν x = f i x := by
  classical
  let S : ι → Set X := fun i => (μ.restrict (K i)).support
  let D := disjointCore S
  let ν := glueDisjointFields D f defaultValue
  have hDdisj : Pairwise (Disjoint on D) := pairwise_disjoint_disjointCore S
  have hDcount (C : Set X) (hC : IsCompact C) :
      {i | (D i ∩ C).Nonempty}.Countable := by
    apply (countable_restricted_supports_meeting_compact μ K hK hdisj hC).mono
    rintro i ⟨x, hxi, hxC⟩
    exact ⟨x, hxi.1, hxC⟩
  refine ⟨ν, measurable_glueDisjointFields D
    (measurableSet_restrictedSupportCore μ K hK hdisj) hDdisj hDcount f hf defaultValue,
    ?_, ?_⟩
  · intro i
    apply (ae_restrict_iff' (hK i).measurableSet).mpr
    filter_upwards [restrictedSupportCore_ae_eq μ K hK hdisj i] with x hx hxi
    exact glueDisjointFields_of_mem D hDdisj f defaultValue (hx.mpr hxi)
  · intro x
    by_cases hx : ∃ i, x ∈ D i
    · obtain ⟨i, hxi⟩ := hx
      exact Or.inr ⟨i, support_restrict_subset_of_isCompact μ (hK i) hxi.1,
        glueDisjointFields_of_mem D hDdisj f defaultValue hxi⟩
    · exact Or.inl (glueDisjointFields_of_notMem D f defaultValue
        (by simpa only [mem_iUnion] using hx))

omit hK hdisj

/-- A general Radon measure has an actually disjoint Borel decomposition
which is countable and conull on each compact set.  The Borel pieces agree
with positive compact sets almost everywhere, but a globally null remainder
is deliberately not part of this statement. -/
theorem exists_disjoint_measurable_local_decomposition :
    ∃ (ι : Type u) (K D : ι → Set X),
      (∀ i, IsCompact (K i) ∧ 0 < μ (K i) ∧ MeasurableSet (D i) ∧
        D i ⊆ K i ∧ D i =ᵐ[μ] K i) ∧
      Pairwise (Disjoint on D) ∧
      (∀ C : Set X, IsCompact C → {i | (D i ∩ C).Nonempty}.Countable) ∧
      (∀ C : Set X, IsCompact C → μ (C \ ⋃ i, D i) = 0) := by
  obtain ⟨ι, K, hK, hdisj, hcount, hcover⟩ :=
    exists_compact_support_local_decomposition μ
  let S : ι → Set X := fun i => (μ.restrict (K i)).support
  let D := disjointCore S
  have hKS (i : ι) : S i ⊆ K i := support_restrict_subset_of_isCompact μ (hK i).1
  refine ⟨ι, K, D, ?_, pairwise_disjoint_disjointCore S, ?_, ?_⟩
  · intro i
    exact ⟨(hK i).1, (hK i).2,
      measurableSet_restrictedSupportCore μ K (fun j => (hK j).1) hdisj i,
      (disjointCore_subset S i).trans (hKS i),
      restrictedSupportCore_ae_eq μ K (fun j => (hK j).1) hdisj i⟩
  · intro C hC
    apply (hcount C hC).mono
    rintro i ⟨x, hxi, hxC⟩
    exact ⟨x, hxi.1, hxC⟩
  · intro C hC
    exact restrictedSupportCores_cover_compact_ae μ K (fun j => (hK j).1) hdisj
      hC (hcover C hC)

end RadonDecomposition

end Poincare.SimonGMT.Chapter01
