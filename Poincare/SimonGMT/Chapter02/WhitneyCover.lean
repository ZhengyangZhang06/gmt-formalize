module

public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# Distance-adapted balls for Whitney extension

The balls constructed here are actual consequences of Vitali selection. Their
radii are one hundredth of the distance to the closed set, capped at one
hundredth. The small balls are disjoint and their fourfold enlargements cover
the complement. The cap is only for the bounded-radius hypothesis in Vitali's
selection theorem.
-/

open Set Metric Filter
open scoped Topology

namespace Poincare.SimonGMT.Chapter02

noncomputable section

section Packing

variable {X : Type*} [MetricSpace X]

/-- A fixed totally bounded set has a uniform finite bound on the cardinality
of its subsets with a fixed positive separation. -/
theorem TotallyBounded.exists_uniform_separated_bound
    {K : Set X} (hK : TotallyBounded K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ s : Set X, s ⊆ K →
      s.Pairwise (fun x y => δ ≤ dist x y) → s.Finite ∧ s.ncard ≤ N := by
  classical
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hK (δ / 2) (by positivity)
  refine ⟨t.ncard, fun s hs hsep => ?_⟩
  have hc : ∀ x : s, ∃ y : t, dist (x : X) y < δ / 2 := by
    intro x
    have hx := hcover (hs x.property)
    simp only [mem_iUnion, mem_ball, exists_prop] at hx
    obtain ⟨y, hyt, hxy⟩ := hx
    exact ⟨⟨y, hyt⟩, hxy⟩
  choose c hc using hc
  have hi : Function.Injective c := by
    intro x y hxy
    by_contra hne
    have hne' : (x : X) ≠ (y : X) := fun h => hne (Subtype.ext h)
    have hd := hsep x.property y.property hne'
    have htri := dist_triangle (x : X) (c x : X) (y : X)
    have hxc := hc x
    have hyc := hc y
    rw [← hxy, dist_comm (y : X) (c x : X)] at hyc
    linarith
  letI : Finite t := ht.to_subtype
  letI : Finite s := Finite.of_injective c hi
  refine ⟨Set.toFinite s, ?_⟩
  exact Nat.card_le_card_of_injective c hi

end Packing

section Radius

variable {X : Type*} [MetricSpace X]

/-- The capped distance scale used in the Whitney-ball construction. -/
def whitneyRadius (A : Set X) (x : X) : ℝ := min 1 (infDist x A) / 100

theorem whitneyRadius_nonneg (A : Set X) (x : X) : 0 ≤ whitneyRadius A x := by
  exact div_nonneg (le_min (by norm_num) infDist_nonneg) (by norm_num)

theorem whitneyRadius_le (A : Set X) (x : X) : whitneyRadius A x ≤ 1 / 100 := by
  exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

theorem whitneyRadius_le_infDist (A : Set X) (x : X) :
    100 * whitneyRadius A x ≤ infDist x A := by
  dsimp [whitneyRadius]
  linarith [min_le_right (1 : ℝ) (infDist x A)]

theorem whitneyRadius_pos {A : Set X} (hA : IsClosed A) (hne : A.Nonempty)
    {x : X} (hx : x ∉ A) : 0 < whitneyRadius A x := by
  exact div_pos (lt_min (by norm_num) ((hA.notMem_iff_infDist_pos hne).mp hx))
    (by norm_num)

theorem whitneyRadius_le_add (A : Set X) (x y : X) :
    whitneyRadius A x ≤ whitneyRadius A y + dist x y / 100 := by
  have h := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
  have h' := (abs_sub_le_iff.mp h).1
  dsimp [whitneyRadius]
  linarith

theorem whitneyRadius_comparable {A : Set X} {x y : X}
    (hxy : dist x y ≤ 10 * whitneyRadius A y) :
    whitneyRadius A y / 2 ≤ whitneyRadius A x ∧
      whitneyRadius A x ≤ 2 * whitneyRadius A y := by
  have h₁ := whitneyRadius_le_add A x y
  have h₂ := whitneyRadius_le_add A y x
  rw [dist_comm y x] at h₂
  have hy := whitneyRadius_nonneg A y
  constructor <;> linarith

theorem whitneyRadius_ball_subset_compl {A : Set X} {x : X}
    (hx : 0 < whitneyRadius A x) : closedBall x (10 * whitneyRadius A x) ⊆ Aᶜ := by
  intro y hy hyA
  have hd : dist x y ≤ 10 * whitneyRadius A x := by
    simpa only [mem_closedBall, dist_comm] using hy
  have hi := infDist_le_dist_of_mem (x := x) hyA
  have hr := whitneyRadius_le_infDist A x
  linarith

/-- A genuinely selected family of Whitney balls, with no covering assumption
added to the source closed set. -/
structure WhitneyBallCover (A : Set X) where
  centers : Set X
  centers_subset : centers ⊆ Aᶜ
  disjoint : centers.PairwiseDisjoint (fun x => ball x (whitneyRadius A x))
  covers : ∀ x ∉ A, ∃ c ∈ centers, dist x c < 4 * whitneyRadius A c

theorem exists_whitneyBallCover {A : Set X} (hA : IsClosed A) (hne : A.Nonempty) :
    Nonempty (WhitneyBallCover A) := by
  obtain ⟨s, hs, hd, hc⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      Aᶜ (fun x : X => x) (whitneyRadius A) (1 / 100)
      (fun x _ => whitneyRadius_le A x) 4 (by norm_num)
  refine ⟨⟨s, hs, hd, fun x hx => ?_⟩⟩
  obtain ⟨c, hcs, hxc⟩ := hc x hx
  exact ⟨c, hcs, hxc (mem_ball_self (whitneyRadius_pos hA hne hx))⟩

end Radius

section LocalFiniteness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {A : Set E}

theorem WhitneyBallCover.radius_le_dist (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty)
    {c d : E} (hc : c ∈ C.centers) (hd : d ∈ C.centers) (hcd : c ≠ d) :
    whitneyRadius A c ≤ dist c d := by
  by_contra h
  have hdc : d ∈ ball c (whitneyRadius A c) := by
    simpa only [mem_ball, dist_comm] using lt_of_not_ge h
  have hdd : d ∈ ball d (whitneyRadius A d) :=
    mem_ball_self (whitneyRadius_pos hA hne (C.centers_subset hd))
  exact Set.disjoint_left.mp (C.disjoint hc hd hcd) hdc hdd

theorem whitneyRadius_near_comparable {x c : E}
    (hxc : dist x c ≤ whitneyRadius A x + 10 * whitneyRadius A c) :
    whitneyRadius A x / 2 ≤ whitneyRadius A c ∧
      whitneyRadius A c ≤ 2 * whitneyRadius A x ∧
      dist x c ≤ 21 * whitneyRadius A x := by
  have h₁ := whitneyRadius_le_add A x c
  have h₂ := whitneyRadius_le_add A c x
  rw [dist_comm c x] at h₂
  have hx := whitneyRadius_nonneg A x
  have hc := whitneyRadius_nonneg A c
  constructor
  · linarith
  constructor <;> linarith

/-- The number of balls near any point of the complement is bounded uniformly
over all closed sets and all Vitali selections. In particular this is stronger
than merely pointwise finiteness. -/
theorem exists_whitneyBallCover_overlap_bound :
    ∃ N : ℕ, ∀ (A : Set E) (hA : IsClosed A) (hne : A.Nonempty)
      (C : WhitneyBallCover A) (x : E), x ∉ A →
      let s := {c | c ∈ C.centers ∧
        dist x c ≤ whitneyRadius A x + 10 * whitneyRadius A c}
      s.Finite ∧ s.ncard ≤ N := by
  obtain ⟨N, hN⟩ := TotallyBounded.exists_uniform_separated_bound
    (isCompact_closedBall (0 : E) 21).totallyBounded (δ := 1 / 2) (by norm_num)
  refine ⟨N, fun A hA hne C x hx => ?_⟩
  dsimp only
  let s := {c | c ∈ C.centers ∧
    dist x c ≤ whitneyRadius A x + 10 * whitneyRadius A c}
  let r := whitneyRadius A x
  have hr : 0 < r := whitneyRadius_pos hA hne hx
  let f : E → E := fun c => r⁻¹ • (c - x)
  have hf : Function.Injective f := by
    intro c d hcd
    have h := congrArg (fun z : E => r • z) hcd
    simpa [f, smul_smul, hr.ne'] using h
  have hnorm : ∀ c ∈ s, ‖f c‖ ≤ 21 := by
    intro c hc
    have hd := (whitneyRadius_near_comparable hc.2).2.2
    rw [dist_comm, dist_eq_norm] at hd
    dsimp [f]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    calc
      r⁻¹ * ‖c - x‖ ≤ r⁻¹ * (21 * r) :=
        mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hr.le)
      _ = 21 := by field_simp
  have hsep : (f '' s).Pairwise (fun y z => 1 / 2 ≤ dist y z) := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ hcd
    have hcd' : c ≠ d := fun h => hcd (congrArg f h)
    have hdist := C.radius_le_dist hA hne hc.1 hd.1 hcd'
    have hrad := (whitneyRadius_near_comparable hc.2).1
    have hlow : r / 2 ≤ ‖c - d‖ := by
      simpa only [dist_eq_norm] using hrad.trans hdist
    have hid : (c - x) - (d - x) = c - d := by abel
    dsimp [f]
    rw [dist_eq_norm, ← smul_sub, hid, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    calc
      (1 : ℝ) / 2 = r⁻¹ * (r / 2) := by field_simp
      _ ≤ r⁻¹ * ‖c - d‖ := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hr.le)
  have hsub : f '' s ⊆ closedBall (0 : E) 21 := by
    rintro _ ⟨c, hc, rfl⟩
    simpa only [mem_closedBall, dist_zero_right] using hnorm c hc
  obtain ⟨hfin, hcard⟩ := hN (f '' s) hsub hsep
  refine ⟨hfin.of_finite_image hf.injOn, ?_⟩
  simpa only [Set.ncard_image_of_injective s hf] using hcard

/-- The tenfold closed balls are locally finite on the actual complement
subtype. They need not be locally finite at boundary points in the ambient
space, where Whitney's compatibility estimates are instead required. -/
theorem WhitneyBallCover.locallyFinite (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) :
    LocallyFinite (fun c : C.centers =>
      {x : (Aᶜ : Set E) | (x : E) ∈ closedBall (c : E) (10 * whitneyRadius A c)}) := by
  obtain ⟨N, hN⟩ := exists_whitneyBallCover_overlap_bound (E := E)
  intro x
  refine ⟨ball x (whitneyRadius A x), ball_mem_nhds x
    (whitneyRadius_pos hA hne x.property), ?_⟩
  have hs := (hN A hA hne C x x.property).1
  apply hs.preimage Subtype.val_injective.injOn |>.subset
  rintro c ⟨y, hyc, hyx⟩
  refine ⟨c.property, ?_⟩
  have h₁ : dist (y : E) c ≤ 10 * whitneyRadius A c := hyc
  have h₂ : dist (y : E) x < whitneyRadius A x := hyx
  have htri := dist_triangle (x : E) (y : E) (c : E)
  rw [dist_comm (x : E) (y : E)] at htri
  linarith

end LocalFiniteness

end

end Poincare.SimonGMT.Chapter02
