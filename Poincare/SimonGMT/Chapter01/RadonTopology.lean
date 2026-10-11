module

public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Order.Filter.Bases.Finite

public section

/-!
# Simon GMT, Chapter 1, Lemmas 4.1–4.5

The neighborhood conclusions below are retained literally: the cutoffs and
partition sum are one on an open neighborhood, not merely on the compact set.
-/

open Filter Set TopologicalSpace
open scoped Topology

namespace Poincare.SimonGMT.Chapter01

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/-- Simon Lemma 4.1: finitely many disjoint compact sets have pairwise
disjoint open neighborhoods. -/
theorem simon_lemma_4_1 {ι : Type*} [Finite ι] (K : ι → Set X)
    (hK : ∀ i, IsCompact (K i)) (hd : Pairwise fun i j => Disjoint (K i) (K j)) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i) ∧ K i ⊆ U i) ∧
      Pairwise fun i j => Disjoint (U i) (U j) := by
  have hn : Pairwise fun i j => Disjoint (𝓝ˢ (K i)) (𝓝ˢ (K j)) := by
    intro i j hij
    exact (SeparatedNhds.of_isCompact_isCompact_isClosed
      (hK i) (hK j) (hK j).isClosed (hd hij)).disjoint_nhdsSet
  exact hn.exists_mem_filter_basis_of_disjoint (fun i => hasBasis_nhdsSet (K i))

/-- Simon Corollary 4.2: a compact Hausdorff space is normal. -/
theorem simon_corollary_4_2 [CompactSpace X] {K₁ K₂ : Set X}
    (h₁ : IsClosed K₁) (h₂ : IsClosed K₂) (hd : Disjoint K₁ K₂) :
    ∃ U₁ U₂ : Set X, IsOpen U₁ ∧ IsOpen U₂ ∧ K₁ ⊆ U₁ ∧ K₂ ⊆ U₂ ∧
      Disjoint U₁ U₂ :=
  normal_separation h₁ h₂ hd

variable [LocallyCompactSpace X]

/-- Simon Lemma 4.3: every neighborhood contains the compact closure of
an open neighborhood of the same point. -/
theorem simon_lemma_4_3 {x : X} {V : Set X} (hV : V ∈ 𝓝 x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsCompact (closure U) ∧ closure U ⊆ V := by
  obtain ⟨W, hWV, hW, hxW⟩ := mem_nhds_iff.mp hV
  obtain ⟨U, hU, hxU, hUW, hUc⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hW
      (singleton_subset_iff.mpr hxW)
  exact ⟨U, hU, hxU (mem_singleton x), hUc, hUW.trans hWV⟩

/-- The remark after Simon Lemma 4.3: the neighborhoods in Lemma 4.1 can
be chosen to have compact, pairwise disjoint closures. -/
theorem simon_remark_4_3 {ι : Type*} [Finite ι] (K : ι → Set X)
    (hK : ∀ i, IsCompact (K i)) (hd : Pairwise fun i j => Disjoint (K i) (K j)) :
    ∃ U : ι → Set X,
      (∀ i, IsOpen (U i) ∧ K i ⊆ U i ∧ IsCompact (closure (U i))) ∧
      Pairwise fun i j => Disjoint (closure (U i)) (closure (U j)) := by
  obtain ⟨V, hV, hdV⟩ := simon_lemma_4_1 K hK hd
  choose U hU hKU hUV hUc using fun i =>
    exists_open_between_and_isCompact_closure (hK i) (hV i).1 (hV i).2
  exact ⟨U, fun i => ⟨hU i, hKU i, hUc i⟩,
    fun i j hij => (hdV hij).mono (hUV i) (hUV j)⟩

/-- Simon Lemma 4.4, including the source's neighborhood-one conclusion.
The real-valued continuous map is explicitly constrained to `[0,1]`. -/
theorem simon_lemma_4_4 {K V : Set X} (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ (U W : Set X) (f : C(X, ℝ)),
      IsOpen U ∧ K ⊆ U ∧ IsCompact (closure U) ∧ closure U ⊆ V ∧
      IsOpen W ∧ K ⊆ W ∧ EqOn f 1 W ∧ EqOn f 0 Uᶜ ∧
      (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport f := by
  obtain ⟨U, hU, hKU, hUV, hUc⟩ :=
    exists_open_between_and_isCompact_closure hK hV hKV
  obtain ⟨W, hW, hKW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨f, hfW, hfc, hfU, hfI⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hWc hU hWU
  refine ⟨U, W, f, hU, hKU, hUc, hUV, hW, hKW,
    hfW.mono subset_closure, ?_, hfI, hfc⟩
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (fun h => hx (hfU h))

/-- Simon Corollary 4.5: a finite open cover of a compact set has a compactly
supported continuous partition of unity whose sum is one on a neighborhood. -/
theorem simon_corollary_4_5 {n : ℕ} {K : Set X} {U : Fin n → Set X}
    (hK : IsCompact K) (hU : ∀ i, IsOpen (U i)) (hcover : K ⊆ ⋃ i, U i) :
    ∃ (W : Set X) (φ : Fin n → C(X, ℝ)),
      IsOpen W ∧ K ⊆ W ∧ EqOn (∑ i, φ i) 1 W ∧
      (∀ i, HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ U i) ∧
      ∀ i x, φ i x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨W, hW, hKW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK (isOpen_iUnion hU) hcover
  obtain ⟨φ, hφU, hφsum, hφI, hφc⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact hU hWc hWU
  exact ⟨W, φ, hW, hKW, hφsum.mono subset_closure,
    fun i => ⟨hφc i, hφU i⟩, hφI⟩

end Poincare.SimonGMT.Chapter01
