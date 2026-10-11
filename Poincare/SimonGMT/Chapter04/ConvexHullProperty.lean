module

public import Poincare.SimonGMT.Chapter04.CompactSupportMaximum
public import Poincare.SimonGMT.Chapter04.CompactConvexHull

@[expose] public section

/-!
# Simon GMT, Chapter 4, Theorem 6.2

The full convex-hull property, including the empty-obstacle case. The
ambient space need not be assumed nontrivial: in a zero-dimensional ambient
space a positive-dimensional rectifiable varifold has zero weight.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

namespace RectifiableVarifold

variable {V : RectifiableVarifold (E := E) n}

/-- There is no nonzero compactly supported stationary varifold of
positive dimension in Euclidean space. -/
theorem IsStationaryIn.support_eq_empty_of_isCompact
    (hn : 0 < n) (hV : V.IsStationaryIn univ)
    (hcompact : IsCompact V.weight.support) : V.weight.support = ∅ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hf : ∀ᵐ x ∂V.weight, False := by
      filter_upwards [V.tangent_finrank_ae_weight] with x hx
      have hz : Module.finrank ℝ (V.tangent x) = 0 := Module.finrank_zero_of_subsingleton
      omega
    exact V.weight.support_eq_empty_iff.mpr
      (ae_eq_bot.mp (eventually_false_iff_eq_bot.mp hf))
  · obtain ⟨a, b, hab⟩ := exists_pair_ne E
    have hball : ∀ ξ : E, V.weight.support ⊆ closedBall ξ 0 := by
      intro ξ
      have hs : V.IsStationaryIn (closedBall ξ 0)ᶜ :=
        fun X hX ↦ hV X ⟨hX.1, hX.2.1, subset_univ _⟩
      exact hs.support_subset_closedBall hn le_rfl hcompact
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have ha : x = a := by simpa only [closedBall_zero, mem_singleton_iff] using hball a hx
    have hb : x = b := by simpa only [closedBall_zero, mem_singleton_iff] using hball b hx
    exact hab (ha.symm.trans hb)

/-- Simon 4.6.2: the compact support of a varifold stationary away from a
compact obstacle is contained in that obstacle's convex hull. -/
theorem IsStationaryIn.support_subset_convexHull
    (hn : 0 < n) {K : Set E} (hK : IsCompact K)
    (hV : V.IsStationaryIn Kᶜ) (hcompact : IsCompact V.weight.support) :
    V.weight.support ⊆ convexHull ℝ K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · have hs : V.IsStationaryIn univ := by simpa only [compl_empty] using hV
    rw [hs.support_eq_empty_of_isCompact hn hcompact]
    exact empty_subset _
  · intro x hx
    by_contra hnot
    obtain ⟨ξ, R, hR, hball, hxball⟩ :=
      exists_closedBall_separating_of_compact_convex
        (isCompact_convexHull_of_isCompact hK) (convex_convexHull ℝ K)
        (hne.mono (subset_convexHull ℝ K)) hnot
    have hKB : K ⊆ closedBall ξ R := (subset_convexHull ℝ K).trans hball
    have hs : V.IsStationaryIn (closedBall ξ R)ᶜ := by
      intro X hX
      apply hV X ⟨hX.1, hX.2.1, ?_⟩
      exact hX.2.2.trans (compl_subset_compl.mpr hKB)
    exact hxball (hs.support_subset_closedBall hn hR hcompact hx)

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
