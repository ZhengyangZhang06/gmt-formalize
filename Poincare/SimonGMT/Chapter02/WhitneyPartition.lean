module

public import Poincare.SimonGMT.Chapter02.WhitneyCover
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Algebra.BigOperators.Finprod

@[expose] public section

/-!
# Smooth functions on the Whitney balls

We scale one fixed smooth bump rather than choosing unrelated bumps on each
ball. Consequently the first derivatives have a common bound divided by the
Whitney radius. The finite-overlap cover then gives the required quantitative
normalization estimates.
-/

open Set Metric Filter Function
open scoped Topology BigOperators ContDiff NNReal

namespace Poincare.SimonGMT.Chapter02

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def whitneyBaseBump : ContDiffBump (0 : E) where
  rIn := 4
  rOut := 8
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def whitneyBump (A : Set E) (c x : E) : ℝ :=
  (whitneyBaseBump (E := E)) ((whitneyRadius A c)⁻¹ • (x - c))

theorem whitneyBump_contDiff (A : Set E) (c : E) :
    ContDiff ℝ ∞ (whitneyBump A c) := by
  exact (whitneyBaseBump (E := E)).contDiff.comp
    ((contDiff_id.sub contDiff_const).const_smul _)

theorem whitneyBump_nonneg (A : Set E) (c x : E) : 0 ≤ whitneyBump A c x :=
  (whitneyBaseBump (E := E)).nonneg

theorem whitneyBump_le_one (A : Set E) (c x : E) : whitneyBump A c x ≤ 1 :=
  (whitneyBaseBump (E := E)).le_one

theorem whitneyBump_eq_one {A : Set E} {c x : E}
    (hc : 0 < whitneyRadius A c) (hx : dist x c ≤ 4 * whitneyRadius A c) :
    whitneyBump A c x = 1 := by
  apply (whitneyBaseBump (E := E)).one_of_mem_closedBall
  simp only [mem_closedBall, dist_zero_right, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
  change (whitneyRadius A c)⁻¹ * ‖x - c‖ ≤ 4
  rw [dist_eq_norm] at hx
  calc
    (whitneyRadius A c)⁻¹ * ‖x - c‖ ≤
        (whitneyRadius A c)⁻¹ * (4 * whitneyRadius A c) :=
      mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hc.le)
    _ = 4 := by field_simp

theorem whitneyBump_eq_zero {A : Set E} {c x : E}
    (hc : 0 < whitneyRadius A c) (hx : 8 * whitneyRadius A c ≤ dist x c) :
    whitneyBump A c x = 0 := by
  change (whitneyBaseBump (E := E)) ((whitneyRadius A c)⁻¹ • (x - c)) = 0
  apply notMem_support.mp
  rw [(whitneyBaseBump (E := E)).support_eq]
  simp only [mem_ball, dist_zero_right, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hc.le), not_lt]
  change 8 ≤ (whitneyRadius A c)⁻¹ * ‖x - c‖
  rw [dist_eq_norm] at hx
  calc
    (8 : ℝ) = (whitneyRadius A c)⁻¹ * (8 * whitneyRadius A c) := by field_simp
    _ ≤ (whitneyRadius A c)⁻¹ * ‖x - c‖ :=
      mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hc.le)

theorem whitneyBump_ne_zero_dist_lt {A : Set E} {c x : E}
    (hc : 0 < whitneyRadius A c) (hx : whitneyBump A c x ≠ 0) :
    dist x c < 8 * whitneyRadius A c := by
  exact lt_of_not_ge (fun h => hx (whitneyBump_eq_zero hc h))

/-- One constant controls all first derivatives of all the rescaled bumps. -/
theorem exists_whitneyBump_derivative_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (A : Set E) (c : E), 0 < whitneyRadius A c →
      ∀ x : E, ‖fderiv ℝ (whitneyBump A c) x‖ ≤ B / whitneyRadius A c := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (whitneyBaseBump (E := E)).hasCompactSupport
    (show ContDiff ℝ ∞ (whitneyBaseBump (E := E)) from whitneyBaseBump.contDiff)
    (by simp)
  refine ⟨(L : ℝ) + 1, by positivity, fun A c hc x => ?_⟩
  let r : ℝ≥0 := ⟨whitneyRadius A c, hc.le⟩
  have hf : LipschitzWith r⁻¹ (fun y : E => (whitneyRadius A c)⁻¹ • (y - c)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    have hid : (y - c) - (z - c) = y - z := by abel
    simp only [dist_eq_norm, ← smul_sub, hid, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hc.le), NNReal.coe_inv]
    exact le_rfl
  have hg : LipschitzWith (L * r⁻¹) (whitneyBump A c) := hL.comp hf
  have hb := norm_fderiv_le_of_lipschitz ℝ hg (x₀ := x)
  simp only [NNReal.coe_mul, NNReal.coe_inv] at hb
  change ‖fderiv ℝ (whitneyBump A c) x‖ ≤ (L : ℝ) * (whitneyRadius A c)⁻¹ at hb
  refine hb.trans ?_
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hc.le)

variable {A : Set E}

/-- A finite set of indices large enough to contain every active bump on a
whole ambient ball about `x`. -/
def WhitneyBallCover.nearIndices (C : WhitneyBallCover A) (x : E) : Set C.centers :=
  {c | dist x c ≤ whitneyRadius A x + 10 * whitneyRadius A c}

theorem WhitneyBallCover.nearIndices_finite (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) {x : E} (hx : x ∉ A) :
    (C.nearIndices x).Finite := by
  obtain ⟨N, hN⟩ := exists_whitneyBallCover_overlap_bound (E := E)
  apply ((hN A hA hne C x hx).1.preimage
    (Subtype.val_injective (p := (· ∈ C.centers))).injOn).subset
  intro c hc
  exact ⟨c.property, hc⟩

def WhitneyBallCover.nearFinset (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) (x : E) (hx : x ∉ A) : Finset C.centers :=
  (C.nearIndices_finite hA hne hx).toFinset

theorem WhitneyBallCover.bump_eq_zero_of_notMem_nearFinset (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) {x y : E} (hx : x ∉ A)
    (hy : dist y x < whitneyRadius A x) {c : C.centers}
    (hc : c ∉ C.nearFinset hA hne x hx) : whitneyBump A c y = 0 := by
  apply whitneyBump_eq_zero (whitneyRadius_pos hA hne (C.centers_subset c.property))
  have hnot : ¬ dist x c ≤ whitneyRadius A x + 10 * whitneyRadius A c := by
    simpa only [WhitneyBallCover.nearFinset, Finite.mem_toFinset,
      WhitneyBallCover.nearIndices, mem_setOf_eq] using hc
  have ht := dist_triangle x y (c : E)
  rw [dist_comm x y] at ht
  have hr := whitneyRadius_nonneg A (c : E)
  linarith

def whitneyBumpSum (C : WhitneyBallCover A) (x : E) : ℝ :=
  ∑ᶠ c : C.centers, whitneyBump A c x

theorem whitneyBumpSum_eq_near_sum (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) {x y : E} (hx : x ∉ A)
    (hy : dist y x < whitneyRadius A x) :
    whitneyBumpSum C y =
      ∑ c ∈ C.nearFinset hA hne x hx, whitneyBump A c y := by
  apply finsum_eq_sum_of_support_subset
  intro c hc
  by_contra h
  exact hc (C.bump_eq_zero_of_notMem_nearFinset hA hne hx hy h)

theorem whitneyBumpSum_contDiffAt (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) {x : E} (hx : x ∉ A) :
    ContDiffAt ℝ ∞ (whitneyBumpSum C) x := by
  have hs : ContDiff ℝ ∞ (fun y =>
      ∑ c ∈ C.nearFinset hA hne x hx, whitneyBump A c y) :=
    ContDiff.sum (fun c _ => whitneyBump_contDiff A c)
  apply hs.contDiffAt.congr_of_eventuallyEq
  filter_upwards [ball_mem_nhds x (whitneyRadius_pos hA hne hx)] with y hy
  exact whitneyBumpSum_eq_near_sum C hA hne hx hy

theorem one_le_whitneyBumpSum (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) {x : E} (hx : x ∉ A) :
    1 ≤ whitneyBumpSum C x := by
  classical
  have hr := whitneyRadius_pos hA hne hx
  rw [whitneyBumpSum_eq_near_sum C hA hne hx (by simpa using hr)]
  obtain ⟨c, hc, hxc⟩ := C.covers x hx
  let i : C.centers := ⟨c, hc⟩
  have hi : i ∈ C.nearFinset hA hne x hx := by
    simp only [WhitneyBallCover.nearFinset, Finite.mem_toFinset,
      WhitneyBallCover.nearIndices, mem_setOf_eq]
    have hc' := whitneyRadius_nonneg A c
    dsimp [i]
    linarith
  calc
    (1 : ℝ) = whitneyBump A i x :=
      (whitneyBump_eq_one (whitneyRadius_pos hA hne (C.centers_subset hc)) hxc.le).symm
    _ ≤ ∑ c ∈ C.nearFinset hA hne x hx, whitneyBump A c x :=
      Finset.single_le_sum (f := fun c : C.centers => whitneyBump A c x)
        (fun c _ => whitneyBump_nonneg A c x) hi

def whitneyWeight (C : WhitneyBallCover A) (c : C.centers) (x : E) : ℝ :=
  whitneyBump A c x / whitneyBumpSum C x

theorem whitneyWeight_contDiffAt (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) (c : C.centers) {x : E} (hx : x ∉ A) :
    ContDiffAt ℝ ∞ (whitneyWeight C c) x := by
  exact (whitneyBump_contDiff A c).contDiffAt.div
    (whitneyBumpSum_contDiffAt C hA hne hx)
    (ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (one_le_whitneyBumpSum C hA hne hx)))

theorem whitneyWeight_nonneg (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) (c : C.centers) {x : E} (hx : x ∉ A) :
    0 ≤ whitneyWeight C c x := by
  exact div_nonneg (whitneyBump_nonneg A c x)
    (le_trans (by norm_num) (one_le_whitneyBumpSum C hA hne hx))

theorem whitneyWeight_eq_zero_of_notMem_nearFinset (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) {x y : E} (hx : x ∉ A)
    (hy : dist y x < whitneyRadius A x) {c : C.centers}
    (hc : c ∉ C.nearFinset hA hne x hx) : whitneyWeight C c y = 0 := by
  simp only [whitneyWeight, C.bump_eq_zero_of_notMem_nearFinset hA hne hx hy hc, zero_div]

theorem sum_whitneyWeight_near (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) {x y : E} (hx : x ∉ A)
    (hy : dist y x < whitneyRadius A x) :
    ∑ c ∈ C.nearFinset hA hne x hx, whitneyWeight C c y = 1 := by
  have hyA : y ∉ A := by
    intro hyA
    have hi := infDist_le_dist_of_mem (x := x) hyA
    have hr := whitneyRadius_le_infDist A x
    rw [dist_comm x y] at hi
    linarith [whitneyRadius_nonneg A x]
  simp only [whitneyWeight, ← Finset.sum_div,
    ← whitneyBumpSum_eq_near_sum C hA hne hx hy]
  exact div_self (ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le
    (one_le_whitneyBumpSum C hA hne hyA)))

theorem sum_fderiv_whitneyWeight_near (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) {x : E} (hx : x ∉ A) :
    ∑ c ∈ C.nearFinset hA hne x hx, fderiv ℝ (whitneyWeight C c) x = 0 := by
  have heq : (fun y => ∑ c ∈ C.nearFinset hA hne x hx, whitneyWeight C c y)
      =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [ball_mem_nhds x (whitneyRadius_pos hA hne hx)] with y hy
    exact sum_whitneyWeight_near C hA hne hx hy
  have hh := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_const] at hh
  rw [fderiv_fun_sum (fun c _ =>
    (whitneyWeight_contDiffAt C hA hne c hx).differentiableAt (by simp))] at hh
  exact hh

theorem exists_whitney_nearFinset_card_bound :
    ∃ N : ℕ, ∀ (A : Set E) (hA : IsClosed A) (hne : A.Nonempty)
      (C : WhitneyBallCover A) (x : E) (hx : x ∉ A),
      (C.nearFinset hA hne x hx).card ≤ N := by
  obtain ⟨N, hN⟩ := exists_whitneyBallCover_overlap_bound (E := E)
  refine ⟨N, fun A hA hne C x hx => ?_⟩
  rw [WhitneyBallCover.nearFinset,
    ← Set.ncard_eq_toFinset_card (C.nearIndices x) (C.nearIndices_finite hA hne hx)]
  have heq : (C.nearIndices x).ncard =
      {c | c ∈ C.centers ∧ dist x c ≤ whitneyRadius A x + 10 * whitneyRadius A c}.ncard := by
    change {c : C.centers | (c : E) ∈
      {y | dist x y ≤ whitneyRadius A x + 10 * whitneyRadius A y}}.ncard = _
    rw [Set.ncard_subtype]
    congr 1
    ext c
    exact and_comm
  rw [heq]
  exact (hN A hA hne C x hx).2

theorem whitneyBumpSum_fderiv_eq_near_sum (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) {x : E} (hx : x ∉ A) :
    fderiv ℝ (whitneyBumpSum C) x =
      ∑ c ∈ C.nearFinset hA hne x hx, fderiv ℝ (whitneyBump A c) x := by
  have heq : whitneyBumpSum C =ᶠ[𝓝 x]
      (fun y => ∑ c ∈ C.nearFinset hA hne x hx, whitneyBump A c y) := by
    filter_upwards [ball_mem_nhds x (whitneyRadius_pos hA hne hx)] with y hy
    exact whitneyBumpSum_eq_near_sum C hA hne hx hy
  rw [heq.fderiv_eq]
  exact fderiv_fun_sum (fun c _ => (whitneyBump_contDiff A c).differentiable (by simp) x)

theorem norm_fderiv_whitneyWeight_le (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) (c : C.centers) {x : E} (hx : x ∉ A) :
    ‖fderiv ℝ (whitneyWeight C c) x‖ ≤
      ‖fderiv ℝ (whitneyBump A c) x‖ + ‖fderiv ℝ (whitneyBumpSum C) x‖ := by
  let S := whitneyBumpSum C x
  have hS : 1 ≤ S := one_le_whitneyBumpSum C hA hne hx
  have hSpos : 0 < S := lt_of_lt_of_le (by norm_num) hS
  have hSi : S⁻¹ ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hS
  have hSi2 : (S ^ 2)⁻¹ ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (show 1 ≤ S ^ 2 by nlinarith)
  have hb := ((whitneyBump_contDiff A c).differentiable (by simp) x).hasFDerivAt
  have hd := ((whitneyBumpSum_contDiffAt C hA hne hx).differentiableAt (by simp)).hasFDerivAt
  have hi := (hasDerivAt_inv hSpos.ne').comp_hasFDerivAt x hd
  have hprod := hb.fun_mul hi
  have hder : fderiv ℝ (whitneyWeight C c) x =
      whitneyBump A c x • (-(S ^ 2)⁻¹ • fderiv ℝ (whitneyBumpSum C) x) +
        S⁻¹ • fderiv ℝ (whitneyBump A c) x := by
    change fderiv ℝ (fun y => whitneyBump A c y / whitneyBumpSum C y) x = _
    simpa only [whitneyWeight, div_eq_mul_inv, Function.comp_def, S] using hprod.fderiv
  rw [hder]
  have hb0 := whitneyBump_nonneg A c x
  have hb1 := whitneyBump_le_one A c x
  calc
    ‖whitneyBump A c x • (-(S ^ 2)⁻¹ • fderiv ℝ (whitneyBumpSum C) x) +
        S⁻¹ • fderiv ℝ (whitneyBump A c) x‖ ≤
      ‖whitneyBump A c x • (-(S ^ 2)⁻¹ • fderiv ℝ (whitneyBumpSum C) x)‖ +
        ‖S⁻¹ • fderiv ℝ (whitneyBump A c) x‖ := norm_add_le _ _
    _ = whitneyBump A c x * ((S ^ 2)⁻¹ * ‖fderiv ℝ (whitneyBumpSum C) x‖) +
        S⁻¹ * ‖fderiv ℝ (whitneyBump A c) x‖ := by
      rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hb0, norm_neg,
        Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg S)),
        Real.norm_of_nonneg (inv_nonneg.mpr hSpos.le)]
    _ ≤ ‖fderiv ℝ (whitneyBump A c) x‖ + ‖fderiv ℝ (whitneyBumpSum C) x‖ := by
      have h₁ := mul_le_mul_of_nonneg_right hSi (norm_nonneg (fderiv ℝ (whitneyBump A c) x))
      have h₂ := mul_le_mul_of_nonneg_right hSi2 (norm_nonneg (fderiv ℝ (whitneyBumpSum C) x))
      have h₃ := mul_le_mul_of_nonneg_right hb1
        (mul_nonneg (inv_nonneg.mpr (sq_nonneg S)) (norm_nonneg (fderiv ℝ (whitneyBumpSum C) x)))
      linarith

/-- The quantitative estimate needed at the closed-set boundary: the sum of
the first-derivative norms of the normalized weights is at most a fixed
constant divided by the local Whitney radius. -/
theorem exists_sum_norm_fderiv_whitneyWeight_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ (A : Set E) (hA : IsClosed A) (hne : A.Nonempty)
      (C : WhitneyBallCover A) (x : E) (hx : x ∉ A),
      (∑ c ∈ C.nearFinset hA hne x hx, ‖fderiv ℝ (whitneyWeight C c) x‖) ≤
        M / whitneyRadius A x := by
  obtain ⟨B, hB, hb⟩ := exists_whitneyBump_derivative_bound (E := E)
  obtain ⟨N, hN⟩ := exists_whitney_nearFinset_card_bound (E := E)
  refine ⟨2 * B * ((N : ℝ) + 1) ^ 2, by positivity, fun A hA hne C x hx => ?_⟩
  have hr := whitneyRadius_pos hA hne hx
  let T := 2 * B / whitneyRadius A x
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hb' : ∀ c ∈ C.nearFinset hA hne x hx,
      ‖fderiv ℝ (whitneyBump A c) x‖ ≤ T := by
    intro c hc
    have hcr := whitneyRadius_pos hA hne (C.centers_subset c.property)
    have hc' : dist x c ≤ whitneyRadius A x + 10 * whitneyRadius A c := by
      simpa only [WhitneyBallCover.nearFinset, Finite.mem_toFinset,
        WhitneyBallCover.nearIndices, mem_setOf_eq] using hc
    have hlow := (whitneyRadius_near_comparable hc').1
    refine (hb A c hcr x).trans ?_
    calc
      B / whitneyRadius A c ≤ B / (whitneyRadius A x / 2) :=
        div_le_div_of_nonneg_left hB.le (half_pos hr) hlow
      _ = T := by dsimp [T]; ring
  have hcard : ((C.nearFinset hA hne x hx).card : ℝ) ≤ N := by exact_mod_cast hN A hA hne C x hx
  have hsum : ‖fderiv ℝ (whitneyBumpSum C) x‖ ≤ (N : ℝ) * T := by
    rw [whitneyBumpSum_fderiv_eq_near_sum C hA hne hx]
    calc
      ‖∑ c ∈ C.nearFinset hA hne x hx, fderiv ℝ (whitneyBump A c) x‖ ≤
          ∑ c ∈ C.nearFinset hA hne x hx, ‖fderiv ℝ (whitneyBump A c) x‖ := norm_sum_le _ _
      _ ≤ ∑ _c ∈ C.nearFinset hA hne x hx, T := Finset.sum_le_sum hb'
      _ = ((C.nearFinset hA hne x hx).card : ℝ) * T := by simp
      _ ≤ (N : ℝ) * T := mul_le_mul_of_nonneg_right hcard hT
  have hw : ∀ c ∈ C.nearFinset hA hne x hx,
      ‖fderiv ℝ (whitneyWeight C c) x‖ ≤ T + (N : ℝ) * T := by
    intro c hc
    exact (norm_fderiv_whitneyWeight_le C hA hne c hx).trans (add_le_add (hb' c hc) hsum)
  calc
    (∑ c ∈ C.nearFinset hA hne x hx, ‖fderiv ℝ (whitneyWeight C c) x‖) ≤
        ∑ _c ∈ C.nearFinset hA hne x hx, (T + (N : ℝ) * T) := Finset.sum_le_sum hw
    _ = ((C.nearFinset hA hne x hx).card : ℝ) * (T + (N : ℝ) * T) := by simp [mul_add]
    _ ≤ (N : ℝ) * (T + (N : ℝ) * T) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ ((N : ℝ) + 1) ^ 2 * T := by nlinarith
    _ = 2 * B * ((N : ℝ) + 1) ^ 2 / whitneyRadius A x := by dsimp [T]; ring

end

end Poincare.SimonGMT.Chapter02
