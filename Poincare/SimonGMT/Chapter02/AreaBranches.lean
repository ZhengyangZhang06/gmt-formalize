module

public import Poincare.SimonGMT.Chapter02.AreaLipschitz
public import Poincare.SimonGMT.Chapter02.AreaMultiplicity

@[expose] public section

/-!
# Constructed injective branches and exact fiber sums

The regular set of a differentiable map is partitioned into countably
many Borel injective pieces using actual linear approximations. Fiber
sums are then additive over the disjoint source partition, even though
the images need not be disjoint.
-/

open Function MeasureTheory Module Set Filter
open scoped ENNReal NNReal Topology

namespace Poincare.SimonGMT.Chapter02
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

section Fibers
variable {E F : Type*}

theorem weightedAreaFiberSum_eq_zero_of_not_mem_image
    {s : Set E} {f : E → F} {y : F} (hy : y ∉ f '' s) (w : E → ℝ≥0∞) :
    weightedAreaFiberSum s f w y = 0 := by
  let : IsEmpty (areaFiber s f y) := ⟨fun x ↦ hy ⟨x.1, x.2.1, x.2.2⟩⟩
  simp [weightedAreaFiberSum]

theorem weightedAreaFiberSum_eq_of_injOn {s : Set E} {f : E → F}
    (hi : InjOn f s) (w : E → ℝ≥0∞) {x : E} (hx : x ∈ s) :
    weightedAreaFiberSum s f w (f x) = w x := by
  let x₀ : areaFiber s f (f x) := ⟨x, hx, rfl⟩
  let : Unique (areaFiber s f (f x)) :=
    { default := x₀, uniq z := Subtype.ext (hi z.2.1 hx z.2.2) }
  unfold weightedAreaFiberSum
  calc
    _ = w (default : areaFiber s f (f x)).1 := by simp
    _ = w x₀.1 := congrArg (fun z : areaFiber s f (f x) ↦ w z.1) (Unique.uniq _ _)
    _ = w x := rfl

theorem weightedAreaFiberSum_congr_fiber {s t : Set E} {f : E → F}
    (w : E → ℝ≥0∞) (y : F)
    (h : ∀ x, (x ∈ s ∧ f x = y) ↔ (x ∈ t ∧ f x = y)) :
    weightedAreaFiberSum s f w y = weightedAreaFiberSum t f w y := by
  unfold weightedAreaFiberSum areaFiber
  exact (Equiv.subtypeEquivRight h).tsum_eq (fun x ↦ w x.1)

theorem weightedAreaFiberSum_iUnion {ι : Type*} (t : ι → Set E)
    (hd : Pairwise (Disjoint on t)) (f : E → F) (w : E → ℝ≥0∞) (y : F) :
    weightedAreaFiberSum (⋃ i, t i) f w y = ∑' i, weightedAreaFiberSum (t i) f w y := by
  unfold weightedAreaFiberSum areaFiber
  change (∑' x : ({x | x ∈ ⋃ i, t i ∧ f x = y} : Set E), w x.1) = _
  have he : {x | x ∈ ⋃ i, t i ∧ f x = y} = ⋃ i, {x | x ∈ t i ∧ f x = y} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    aesop
  rw [he]
  apply ENNReal.tsum_biUnion
  intro i _ j _ hij
  exact (hd hij).mono (fun _ hx ↦ hx.1) (fun _ hx ↦ hx.1)

end Fibers

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]

theorem ApproximatesLinearOn.injOn_of_antilipschitz
    {f : E → F} {L : E →L[ℝ] F} {s : Set E} {δ K : ℝ≥0}
    (hf : _root_.ApproximatesLinearOn f L s δ) (hL : AntilipschitzWith K L)
    (hδ : δ * K < 1) : InjOn f s := by
  intro x hx y hy hxy
  have he : ‖L x - L y‖ ≤ (δ : ℝ) * ‖x - y‖ := by
    simpa only [map_sub, hxy, sub_self, zero_sub, norm_neg] using hf x hx y hy
  have hb : ‖x - y‖ ≤ (K : ℝ) * ‖L x - L y‖ := by
    simpa only [dist_eq_norm] using hL.le_mul_dist x y
  have hh : ‖x - y‖ ≤ ((δ : ℝ) * K) * ‖x - y‖ := by
    calc
      _ ≤ (K : ℝ) * ((δ : ℝ) * ‖x - y‖) :=
        hb.trans (mul_le_mul_of_nonneg_left he K.2)
      _ = _ := by ring
  by_contra hne
  have hp : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hsmall : ((δ : ℝ) * K) * ‖x - y‖ < ‖x - y‖ := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right (show (δ : ℝ) * K < 1 from hδ) hp
  exact (not_lt_of_ge hh) hsmall

/-- Countable disjoint Borel injective branches are constructed, not
assumed, from actual full-rank derivatives. -/
theorem exists_injective_partition_of_regular
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hr : ∀ x ∈ s, Injective (fderiv ℝ f x)) :
    ∃ t : ℕ → Set E, (∀ i, MeasurableSet (t i)) ∧ Pairwise (Disjoint on t) ∧
      (⋃ i, t i) = s ∧ ∀ i, InjOn f (t i) := by
  classical
  rcases eq_empty_or_nonempty s with rfl | hne
  · exact ⟨fun _ ↦ ∅, fun _ ↦ MeasurableSet.empty, fun _ _ _ ↦ by simp,
      by simp, fun _ ↦ injOn_empty _⟩
  have hchoice : ∀ L : E →L[ℝ] F, ∃ δ : ℝ≥0, 0 < δ ∧
      (Injective L → ∀ (t : Set E) (g : E → F),
        _root_.ApproximatesLinearOn g L t δ → InjOn g t) := by
    intro L
    by_cases hL : Injective L
    · obtain ⟨K, _, hK⟩ := L.toLinearMap.exists_antilipschitzWith
        (LinearMap.ker_eq_bot.mpr hL)
      have hnear : ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0, δ * K < 1 := nhdsWithin_le_nhds
        ((continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp))
      obtain ⟨δ, hδ, hpos⟩ := (hnear.and self_mem_nhdsWithin).exists
      exact ⟨δ, hpos, fun _ t g hg ↦
        ApproximatesLinearOn.injOn_of_antilipschitz hg hK hδ⟩
    · exact ⟨1, zero_lt_one, fun hi ↦ (hL hi).elim⟩
  choose δ hpos hδ using hchoice
  obtain ⟨t, L, hd, ht, hcover, happrox, hactual⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s (fderiv ℝ f)
      (fun x hx ↦ (hf x hx).hasFDerivAt.hasFDerivWithinAt) δ (fun L ↦ (hpos L).ne')
  refine ⟨fun i ↦ s ∩ t i, fun i ↦ hs.inter (ht i),
    pairwise_disjoint_mono hd (fun _ ↦ inter_subset_right), ?_, ?_⟩
  · rw [← inter_iUnion]
    exact inter_eq_left.mpr hcover
  · intro i
    obtain ⟨x, hx, heq⟩ := hactual hne i
    apply hδ (L i) (heq.symm ▸ hr x hx)
    exact happrox i

/-- Fiber sums on a single Borel injective branch are Borel measurable
for every Borel nonnegative source weight. -/
theorem measurable_weightedAreaFiberSum_of_injOn
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ContinuousOn f s) (hi : InjOn f s) {w : E → ℝ≥0∞} (hw : Measurable w) :
    Measurable (weightedAreaFiberSum s f w) := by
  classical
  have hemb := hf.measurableEmbedding hs hi
  let g : F → ℝ≥0∞ := Function.extend (s.domRestrict f) (fun x : s ↦ w x) (fun _ ↦ 0)
  have hg : Measurable g := hemb.measurable_extend
    (hw.comp measurable_subtype_coe) measurable_const
  have heq : weightedAreaFiberSum s f w = g := by
    funext y
    by_cases hy : y ∈ f '' s
    · obtain ⟨x, hx, rfl⟩ := hy
      rw [weightedAreaFiberSum_eq_of_injOn hi w hx]
      exact (hemb.injective.extend_apply (fun x : s ↦ w x) (fun _ ↦ 0) ⟨x, hx⟩).symm
    · rw [weightedAreaFiberSum_eq_zero_of_not_mem_image hy]
      have hy' : ¬ ∃ a : s, s.domRestrict f a = y := by
        rintro ⟨a, ha⟩
        exact hy ⟨a, a.property, ha⟩
      exact (Function.extend_apply' (f := s.domRestrict f)
        (fun x : s ↦ w x) (fun _ ↦ 0) y hy').symm
  rw [heq]
  exact hg

end
end Poincare.SimonGMT.Chapter02
