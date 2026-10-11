module

public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import Poincare.SimonGMT.Chapter02.Submanifold

@[expose] public section

/-!
# Simon GMT, Chapter 2, (4.2): topology of a local representation

This module proves the topological consequence of the relative-properness
hypothesis in Simon's definition: a local representation is a homeomorphism
onto its image, and hence sends open subsets of its parameter domain to sets
open relative to the represented submanifold.
-/

open Function Set

namespace Poincare.SimonGMT.Chapter02

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- A Simon local representation, regarded as a map between its open source
and target chart subtypes. -/
def IsSimonLocalRepresentation.chartMap
    {r : ℕ∞} {M : Set F} {V : Set E} {W : Set F} {φ : E → F}
    (h : IsSimonLocalRepresentation r M V W φ) : V → W :=
  fun x ↦ ⟨φ x, by
    have hx : φ x ∈ φ '' V := ⟨x, x.property, rfl⟩
    rw [h.image_eq] at hx
    exact hx.1⟩

/-- The chart-subtype map is continuous. -/
theorem IsSimonLocalRepresentation.continuous_chartMap
    {r : ℕ∞} {M : Set F} {V : Set E} {W : Set F} {φ : E → F}
    (h : IsSimonLocalRepresentation r M V W φ) :
    Continuous h.chartMap := by
  apply Continuous.subtype_mk
  exact (continuousOn_iff_continuous_domRestrict.mp h.contDiffOn.continuousOn)

/-- The chart-subtype map is injective. -/
theorem IsSimonLocalRepresentation.injective_chartMap
    {r : ℕ∞} {M : Set F} {V : Set E} {W : Set F} {φ : E → F}
    (h : IsSimonLocalRepresentation r M V W φ) :
    Injective h.chartMap := by
  intro x y hxy
  apply Subtype.ext
  exact h.injOn x.property y.property (congrArg Subtype.val hxy)

/-- Relative properness in Simon's definition makes the chart-subtype map a
proper map. -/
theorem IsSimonLocalRepresentation.isProperMap_chartMap
    {r : ℕ∞} {M : Set F} {V : Set E} {W : Set F} {φ : E → F}
    (h : IsSimonLocalRepresentation r M V W φ) :
    IsProperMap h.chartMap := by
  let hrep := h
  have hcontinuous := h.continuous_chartMap
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hcontinuous, ?_⟩
  intro K hK
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have hKval : IsCompact (((↑) : W → F) '' K) :=
    hK.image continuous_subtype_val
  have hKsub : ((↑) : W → F) '' K ⊆ W := by
    rintro _ ⟨z, -, rfl⟩
    exact z.property
  have hcompact := h.isCompact_source_inter_preimage _ hKval hKsub
  have himage :
      ((↑) : V → E) ''
          (hrep.chartMap ⁻¹' K) =
        V ∩ φ ⁻¹' (((↑) : W → F) '' K) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, ⟨hrep.chartMap z, hz, rfl⟩⟩
    · rintro ⟨hxV, z, hzK, hzx⟩
      refine ⟨⟨x, hxV⟩, ?_, rfl⟩
      change hrep.chartMap ⟨x, hxV⟩ ∈ K
      rw [show hrep.chartMap ⟨x, hxV⟩ = z by
        apply Subtype.ext
        exact hzx.symm]
      exact hzK
  rw [himage]
  exact hcompact

/-- A local representation is a topological embedding into its target chart.
This is the homeomorphism-onto-image assertion preceding Simon (4.2). -/
theorem IsSimonLocalRepresentation.isEmbedding_chartMap
    {r : ℕ∞} {M : Set F} {V : Set E} {W : Set F} {φ : E → F}
    (h : IsSimonLocalRepresentation r M V W φ) :
    Topology.IsEmbedding h.chartMap :=
  (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    h.continuous_chartMap h.injective_chartMap h.isProperMap_chartMap.isClosedMap).isEmbedding

/-- Simon (4.2): every open subset of the parameter domain is represented by
intersection of the submanifold with an ambient open subset of the target
chart. -/
theorem IsSimonLocalRepresentation.exists_open_image_eq_inter
    {r : ℕ∞} {M : Set F} {V : Set E} {W : Set F} {φ : E → F}
    (h : IsSimonLocalRepresentation r M V W φ)
    {V₀ : Set E} (hV₀ : IsOpen V₀) (hV₀V : V₀ ⊆ V) :
    ∃ W₀ : Set F, IsOpen W₀ ∧ W₀ ⊆ W ∧ φ '' V₀ = W₀ ∩ M := by
  let s : Set V := ((↑) : V → E) ⁻¹' V₀
  have hs : IsOpen s := hV₀.preimage continuous_subtype_val
  obtain ⟨c, hc, himage⟩ :=
    h.isEmbedding_chartMap.isInducing.image_eq_isOpen_inter_range hs
  let W₀ : Set F := ((↑) : W → F) '' c
  have hW₀ : IsOpen W₀ :=
    h.isOpen_target.isOpenEmbedding_subtypeVal.isOpenMap c hc
  have hW₀W : W₀ ⊆ W := by
    rintro _ ⟨z, -, rfl⟩
    exact z.property
  refine ⟨W₀, hW₀, hW₀W, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hxV₀, rfl⟩
    have hxV : x ∈ V := hV₀V hxV₀
    let xv : V := ⟨x, hxV⟩
    have hxs : xv ∈ s := hxV₀
    have hi : h.chartMap xv ∈ h.chartMap '' s := ⟨xv, hxs, rfl⟩
    rw [himage] at hi
    refine ⟨⟨h.chartMap xv, hi.1, rfl⟩, ?_⟩
    have hmem : φ x ∈ W ∩ M := by
      rw [← h.image_eq]
      exact ⟨x, hxV, rfl⟩
    exact hmem.2
  · rintro ⟨⟨z, hzc, rfl⟩, hzM⟩
    have hzimage : (z : F) ∈ φ '' V := by
      rw [h.image_eq]
      exact ⟨z.property, hzM⟩
    rcases hzimage with ⟨x, hxV, hφx⟩
    let xv : V := ⟨x, hxV⟩
    have hz_eq : z = h.chartMap xv := by
      apply Subtype.ext
      exact hφx.symm
    have hzrange : z ∈ range h.chartMap := ⟨xv, hz_eq.symm⟩
    have hzi : z ∈ c ∩ range h.chartMap := ⟨hzc, hzrange⟩
    rw [← himage] at hzi
    rcases hzi with ⟨u, hu, hfu⟩
    have hux : u = xv := h.injective_chartMap (hfu.trans hz_eq)
    subst u
    exact ⟨x, hu, hφx⟩

end Poincare.SimonGMT.Chapter02
