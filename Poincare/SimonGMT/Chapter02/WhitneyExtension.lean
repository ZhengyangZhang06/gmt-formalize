module

public import Poincare.SimonGMT.Chapter02.WhitneyJet
public import Poincare.SimonGMT.Chapter02.WhitneyPartition

@[expose] public section

/-!
# Construction of the Whitney first-order extension

The extension is the given function on the closed set and a locally finite
convex combination of its anchor polynomials on the complement. All weights
and their quantitative estimates are constructed in `WhitneyPartition`.
-/

open Set Metric Filter Function
open scoped Topology BigOperators ContDiff

namespace Poincare.SimonGMT.Chapter02

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {A : Set E}

theorem whitneyAffine_contDiff (h : E → ℝ) (D : E → E →L[ℝ] ℝ) (a : E) :
    ContDiff ℝ ∞ (whitneyAffine h D a) := by
  exact contDiff_const.add ((D a).contDiff.comp (contDiff_id.sub contDiff_const))

theorem whitneyAffine_hasFDerivAt (h : E → ℝ) (D : E → E →L[ℝ] ℝ) (a x : E) :
    HasFDerivAt (whitneyAffine h D a) (D a) x := by
  convert ((D a).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)).const_add (h a) using 1
  · rfl
  · simp

theorem norm_sum_smul_le_of_convex_weights
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (v : ι → F) {b : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1)
    (hv : ∀ i ∈ s, ‖v i‖ ≤ b) : ‖∑ i ∈ s, w i • v i‖ ≤ b := by
  calc
    ‖∑ i ∈ s, w i • v i‖ ≤ ∑ i ∈ s, ‖w i • v i‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, w i * ‖v i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_of_nonneg (hw i hi)]
    _ ≤ ∑ i ∈ s, w i * b := Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (hv i hi) (hw i hi)
    _ = b := by rw [← Finset.sum_mul, hs, one_mul]

def whitneyExtension (C : WhitneyBallCover A) (hA : IsClosed A) (hne : A.Nonempty)
    (h : E → ℝ) (D : E → E →L[ℝ] ℝ) (x : E) : ℝ := by
  classical
  exact if x ∈ A then h x else
    ∑ᶠ c : C.centers, whitneyWeight C c x *
      whitneyAffine h D (whitneyNearestAnchor hA hne c) x

@[simp] theorem whitneyExtension_eq_on (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) (h : E → ℝ) (D : E → E →L[ℝ] ℝ)
    {a : E} (ha : a ∈ A) : whitneyExtension C hA hne h D a = h a := by
  simp only [whitneyExtension, if_pos ha]

theorem WhitneyBallCover.dist_near_anchor_le (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) {x : E} (hx : x ∉ A)
    {c : C.centers} (hc : c ∈ C.nearFinset hA hne x hx) :
    dist x (whitneyNearestAnchor hA hne c) ≤ 2 * infDist x A := by
  have hc' : dist x c ≤ whitneyRadius A x + 10 * whitneyRadius A c := by
    simpa only [WhitneyBallCover.nearFinset, Finite.mem_toFinset,
      WhitneyBallCover.nearIndices, mem_setOf_eq] using hc
  have hd := (whitneyRadius_near_comparable hc').2.2
  have hr := whitneyRadius_le_infDist A x
  have hi := infDist_le_infDist_add_dist (s := A) (x := (c : E)) (y := x)
  have ht := dist_triangle x (c : E) (whitneyNearestAnchor hA hne c)
  rw [dist_comm (c : E) x] at hi
  rw [dist_whitneyNearestAnchor_eq_infDist] at ht
  linarith [infDist_nonneg (x := x) (s := A)]

theorem WhitneyBallCover.dist_near_anchor_point_le (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) {x a : E} (hx : x ∉ A) (ha : a ∈ A)
    {c : C.centers} (hc : c ∈ C.nearFinset hA hne x hx) :
    dist (whitneyNearestAnchor hA hne c) a ≤ 3 * dist x a := by
  have hd := C.dist_near_anchor_le hA hne hx hc
  have hi := infDist_le_dist_of_mem (x := x) ha
  have ht := dist_triangle (whitneyNearestAnchor hA hne c) x a
  rw [dist_comm (whitneyNearestAnchor hA hne c) x] at ht
  linarith

theorem whitneyExtension_eq_near_sum (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) (h : E → ℝ) (D : E → E →L[ℝ] ℝ)
    {x y : E} (hx : x ∉ A) (hy : dist y x < whitneyRadius A x) :
    whitneyExtension C hA hne h D y =
      ∑ c ∈ C.nearFinset hA hne x hx, whitneyWeight C c y *
        whitneyAffine h D (whitneyNearestAnchor hA hne c) y := by
  have hyA : y ∉ A := by
    intro hyA
    have hi := infDist_le_dist_of_mem (x := x) hyA
    rw [dist_comm x y] at hi
    linarith [whitneyRadius_le_infDist A x, whitneyRadius_nonneg A x]
  rw [whitneyExtension, if_neg hyA]
  apply finsum_eq_sum_of_support_subset
  intro c hc
  by_contra hc'
  apply hc
  dsimp only
  rw [whitneyWeight_eq_zero_of_notMem_nearFinset C hA hne hx hy hc', zero_mul]

theorem whitneyExtension_eventuallyEq_near_sum (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) (h : E → ℝ) (D : E → E →L[ℝ] ℝ)
    {x : E} (hx : x ∉ A) :
    whitneyExtension C hA hne h D =ᶠ[𝓝 x]
      (fun y => ∑ c ∈ C.nearFinset hA hne x hx, whitneyWeight C c y *
        whitneyAffine h D (whitneyNearestAnchor hA hne c) y) := by
  filter_upwards [ball_mem_nhds x (whitneyRadius_pos hA hne hx)] with y hy
  exact whitneyExtension_eq_near_sum C hA hne h D hx hy

theorem whitneyExtension_contDiffAt_compl (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) (h : E → ℝ) (D : E → E →L[ℝ] ℝ)
    {x : E} (hx : x ∉ A) : ContDiffAt ℝ ∞ (whitneyExtension C hA hne h D) x := by
  have hs : ContDiffAt ℝ ∞ (fun y => ∑ c ∈ C.nearFinset hA hne x hx,
      whitneyWeight C c y * whitneyAffine h D (whitneyNearestAnchor hA hne c) y) x :=
    ContDiffAt.sum (fun c _ => (whitneyWeight_contDiffAt C hA hne c hx).mul
      (whitneyAffine_contDiff h D _).contDiffAt)
  exact hs.congr_of_eventuallyEq (whitneyExtension_eventuallyEq_near_sum C hA hne h D hx)

theorem whitneyExtension_fderiv_eq_near_sum (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) (h : E → ℝ) (D : E → E →L[ℝ] ℝ)
    {x : E} (hx : x ∉ A) :
    fderiv ℝ (whitneyExtension C hA hne h D) x =
      ∑ c ∈ C.nearFinset hA hne x hx,
        (whitneyWeight C c x • D (whitneyNearestAnchor hA hne c) +
          whitneyAffine h D (whitneyNearestAnchor hA hne c) x •
            fderiv ℝ (whitneyWeight C c) x) := by
  rw [(whitneyExtension_eventuallyEq_near_sum C hA hne h D hx).fderiv_eq]
  apply HasFDerivAt.fderiv
  apply HasFDerivAt.fun_sum
  intro c hc
  exact ((whitneyWeight_contDiffAt C hA hne c hx).differentiableAt
    (by simp)).hasFDerivAt.fun_mul (whitneyAffine_hasFDerivAt h D _ x)

theorem whitneyExtension_sub_affine_eq_near_sum (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) (h : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (a : E) {x : E} (hx : x ∉ A) :
    whitneyExtension C hA hne h D x - whitneyAffine h D a x =
      ∑ c ∈ C.nearFinset hA hne x hx, whitneyWeight C c x *
        (whitneyAffine h D (whitneyNearestAnchor hA hne c) x - whitneyAffine h D a x) := by
  have hx' : dist x x < whitneyRadius A x := by simp [whitneyRadius_pos hA hne hx]
  rw [whitneyExtension_eq_near_sum C hA hne h D hx hx']
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_whitneyWeight_near C hA hne hx hx', one_mul]

/-- The constructed smooth combination has the prescribed full derivative at
every point of the closed set. -/
theorem HasWhitneyC1Compatibility.hasFDerivAt_whitneyExtension
    {h : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (H : HasWhitneyC1Compatibility A h D) (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) {a : E} (ha : a ∈ A) :
    HasFDerivAt (whitneyExtension C hA hne h D) (D a) a := by
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have he : 0 < ε / 5 := by positivity
  obtain ⟨δ, hδ, hδ1, hD, hrem⟩ := H.exists_local_uniform_estimate hA ha he
  filter_upwards [ball_mem_nhds a (show 0 < δ / 4 by positivity)] with x hx
  have hxa : dist x a < δ / 4 := hx
  rw [whitneyExtension_eq_on C hA hne h D ha]
  by_cases hxA : x ∈ A
  · rw [whitneyExtension_eq_on C hA hne h D hxA]
    have hr := hrem a ha (by simpa using hδ) x hxA (by linarith)
    exact hr.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · have hid : whitneyExtension C hA hne h D x - h a - D a (x - a) =
        whitneyExtension C hA hne h D x - whitneyAffine h D a x := by
      dsimp [whitneyAffine]
      ring
    rw [hid, whitneyExtension_sub_affine_eq_near_sum C hA hne h D a hxA]
    have hx' : dist x x < whitneyRadius A x := by simp [whitneyRadius_pos hA hne hxA]
    apply norm_sum_smul_le_of_convex_weights (C.nearFinset hA hne x hxA)
      (fun c => whitneyWeight C c x)
      (fun c => whitneyAffine h D (whitneyNearestAnchor hA hne c) x - whitneyAffine h D a x)
      (fun c _ => whitneyWeight_nonneg C hA hne c hxA)
      (sum_whitneyWeight_near C hA hne hxA hx')
    intro c hc
    let b := whitneyNearestAnchor hA hne c
    have hbA : b ∈ A := whitneyNearestAnchor_mem hA hne c
    have hba : dist b a ≤ 3 * dist x a := C.dist_near_anchor_point_le hA hne hxA ha hc
    have hxb : dist x b ≤ 2 * dist x a :=
      (C.dist_near_anchor_le hA hne hxA hc).trans
        (mul_le_mul_of_nonneg_left (infDist_le_dist_of_mem ha) (by norm_num))
    have hbaδ : dist b a < δ := by linarith
    have hDb := hD b hbA hbaδ
    have hr := hrem a ha (by simpa using hδ) b hbA hbaδ
    have hba' : ‖b - a‖ ≤ 3 * ‖x - a‖ := by simpa only [dist_eq_norm] using hba
    have hxb' : ‖x - b‖ ≤ 2 * ‖x - a‖ := by simpa only [dist_eq_norm] using hxb
    calc
      ‖whitneyAffine h D b x - whitneyAffine h D a x‖ ≤
          ‖h b - h a - D a (b - a)‖ + ‖D b - D a‖ * ‖x - b‖ :=
        norm_whitneyAffine_sub_le h D a b x
      _ ≤ (ε / 5) * ‖b - a‖ + (ε / 5) * ‖x - b‖ :=
        add_le_add hr (mul_le_mul_of_nonneg_right hDb (norm_nonneg _))
      _ ≤ (ε / 5) * (3 * ‖x - a‖) + (ε / 5) * (2 * ‖x - a‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hba' he.le)
          (mul_le_mul_of_nonneg_left hxb' he.le)
      _ = ε * ‖x - a‖ := by ring

theorem HasWhitneyC1Compatibility.fderiv_whitneyExtension_on
    {h : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (H : HasWhitneyC1Compatibility A h D) (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) {a : E} (ha : a ∈ A) :
    fderiv ℝ (whitneyExtension C hA hne h D) a = D a :=
  (H.hasFDerivAt_whitneyExtension C hA hne ha).fderiv

theorem HasWhitneyC1Compatibility.differentiable_whitneyExtension
    {h : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (H : HasWhitneyC1Compatibility A h D) (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) :
    Differentiable ℝ (whitneyExtension C hA hne h D) := by
  intro x
  by_cases hx : x ∈ A
  · exact (H.hasFDerivAt_whitneyExtension C hA hne hx).differentiableAt
  · exact (whitneyExtension_contDiffAt_compl C hA hne h D hx).differentiableAt (by simp)

theorem whitneyExtension_fderiv_sub_eq_near_sum (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) (h : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (a b : E) {x : E} (hx : x ∉ A) :
    fderiv ℝ (whitneyExtension C hA hne h D) x - D a =
      (∑ c ∈ C.nearFinset hA hne x hx,
        whitneyWeight C c x • (D (whitneyNearestAnchor hA hne c) - D a)) +
      ∑ c ∈ C.nearFinset hA hne x hx,
        (whitneyAffine h D (whitneyNearestAnchor hA hne c) x - whitneyAffine h D b x) •
          fderiv ℝ (whitneyWeight C c) x := by
  have hx' : dist x x < whitneyRadius A x := by simp [whitneyRadius_pos hA hne hx]
  rw [whitneyExtension_fderiv_eq_near_sum C hA hne h D hx]
  simp_rw [smul_sub, sub_smul]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_smul, ← Finset.smul_sum,
    sum_whitneyWeight_near C hA hne hx hx', sum_fderiv_whitneyWeight_near C hA hne hx,
    one_smul, smul_zero, sub_zero]
  abel

theorem norm_fderiv_whitneyExtension_sub_le (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) (h : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (a b : E) {x : E} (hx : x ∉ A) {e₀ e₁ : ℝ}
    (hD : ∀ c ∈ C.nearFinset hA hne x hx,
      ‖D (whitneyNearestAnchor hA hne c) - D a‖ ≤ e₀)
    (hP : ∀ c ∈ C.nearFinset hA hne x hx,
      ‖whitneyAffine h D (whitneyNearestAnchor hA hne c) x - whitneyAffine h D b x‖ ≤ e₁) :
    ‖fderiv ℝ (whitneyExtension C hA hne h D) x - D a‖ ≤
      e₀ + e₁ * ∑ c ∈ C.nearFinset hA hne x hx, ‖fderiv ℝ (whitneyWeight C c) x‖ := by
  rw [whitneyExtension_fderiv_sub_eq_near_sum C hA hne h D a b hx]
  have hx' : dist x x < whitneyRadius A x := by simp [whitneyRadius_pos hA hne hx]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact norm_sum_smul_le_of_convex_weights (C.nearFinset hA hne x hx)
      (fun c => whitneyWeight C c x)
      (fun c => D (whitneyNearestAnchor hA hne c) - D a)
      (fun c _ => whitneyWeight_nonneg C hA hne c hx)
      (sum_whitneyWeight_near C hA hne hx hx') hD
  · calc
      ‖∑ c ∈ C.nearFinset hA hne x hx,
          (whitneyAffine h D (whitneyNearestAnchor hA hne c) x - whitneyAffine h D b x) •
            fderiv ℝ (whitneyWeight C c) x‖ ≤
        ∑ c ∈ C.nearFinset hA hne x hx,
          ‖(whitneyAffine h D (whitneyNearestAnchor hA hne c) x - whitneyAffine h D b x) •
            fderiv ℝ (whitneyWeight C c) x‖ := norm_sum_le _ _
      _ ≤ ∑ c ∈ C.nearFinset hA hne x hx, e₁ * ‖fderiv ℝ (whitneyWeight C c) x‖ := by
        apply Finset.sum_le_sum
        intro c hc
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hP c hc) (norm_nonneg _)
      _ = e₁ * ∑ c ∈ C.nearFinset hA hne x hx, ‖fderiv ℝ (whitneyWeight C c) x‖ :=
        (Finset.mul_sum ..).symm

/-- The derivatives of the constructed extension approach the prescribed jet
also from the complement. This is where compact-uniform compatibility and the
quantitative partition estimate are both used. -/
theorem HasWhitneyC1Compatibility.continuousAt_fderiv_whitneyExtension
    {h : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (H : HasWhitneyC1Compatibility A h D) (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) {a : E} (ha : a ∈ A) :
    ContinuousAt (fderiv ℝ (whitneyExtension C hA hne h D)) a := by
  obtain ⟨M, hM, hbound⟩ := exists_sum_norm_fderiv_whitneyWeight_bound (E := E)
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let η := ε / (2 * (1 + 700 * M))
  have hη : 0 < η := by dsimp [η]; positivity
  have heq : η * (1 + 700 * M) = ε / 2 := by
    dsimp [η]
    field_simp
  have hηε : η ≤ ε / 2 := by nlinarith
  obtain ⟨δ, hδ, hδ1, hD, hrem⟩ := H.exists_local_uniform_estimate hA ha hη
  refine ⟨δ / 4, by positivity, fun {x} hxa => ?_⟩
  rw [H.fderiv_whitneyExtension_on C hA hne ha, dist_eq_norm]
  apply lt_of_le_of_lt (b := ε / 2) ?_ (by linarith)
  by_cases hxA : x ∈ A
  · rw [H.fderiv_whitneyExtension_on C hA hne hxA]
    exact (hD x hxA (by linarith)).trans hηε
  · have hr := whitneyRadius_pos hA hne hxA
    let b := whitneyNearestAnchor hA hne x
    have hbA : b ∈ A := whitneyNearestAnchor_mem hA hne x
    have hba : dist b a ≤ 2 * dist x a := dist_whitneyNearestAnchor_point_le hA hne x ha
    have hbaδ : dist b a < δ := by linarith
    have hDb := hD b hbA hbaδ
    have hdx : infDist x A ≤ 1 := by
      have hi := infDist_le_dist_of_mem (x := x) ha
      linarith
    have hscale : infDist x A = 100 * whitneyRadius A x := by
      simp only [whitneyRadius, min_eq_right hdx]
      ring
    have hD' : ∀ c ∈ C.nearFinset hA hne x hxA,
        ‖D (whitneyNearestAnchor hA hne c) - D a‖ ≤ η := by
      intro c hc
      apply hD _ (whitneyNearestAnchor_mem hA hne c)
      have hi := C.dist_near_anchor_point_le hA hne hxA ha hc
      linarith
    have hP : ∀ c ∈ C.nearFinset hA hne x hxA,
        ‖whitneyAffine h D (whitneyNearestAnchor hA hne c) x - whitneyAffine h D b x‖ ≤
          700 * η * whitneyRadius A x := by
      intro c hc
      let d := whitneyNearestAnchor hA hne c
      have hdA : d ∈ A := whitneyNearestAnchor_mem hA hne c
      have hda : dist d a ≤ 3 * dist x a := C.dist_near_anchor_point_le hA hne hxA ha hc
      have hdaδ : dist d a < δ := by linarith
      have hxd : dist x d ≤ 2 * infDist x A := C.dist_near_anchor_le hA hne hxA hc
      have hxb : dist x b = infDist x A := dist_whitneyNearestAnchor_eq_infDist hA hne x
      have hdb : dist d b ≤ 3 * infDist x A := by
        have ht := dist_triangle d x b
        rw [dist_comm d x, hxb] at ht
        linarith
      have hDd : ‖D d - D b‖ ≤ 2 * η := by
        calc
          ‖D d - D b‖ = ‖(D d - D a) - (D b - D a)‖ := by congr 1; abel
          _ ≤ ‖D d - D a‖ + ‖D b - D a‖ := norm_sub_le _ _
          _ ≤ η + η := add_le_add (hD' c hc) hDb
          _ = 2 * η := by ring
      have hre := hrem b hbA hbaδ d hdA hdaδ
      have hdb' : ‖d - b‖ ≤ 3 * infDist x A := by simpa only [dist_eq_norm] using hdb
      have hxd' : ‖x - d‖ ≤ 2 * infDist x A := by simpa only [dist_eq_norm] using hxd
      calc
        ‖whitneyAffine h D d x - whitneyAffine h D b x‖ ≤
            ‖h d - h b - D b (d - b)‖ + ‖D d - D b‖ * ‖x - d‖ :=
          norm_whitneyAffine_sub_le h D b d x
        _ ≤ η * ‖d - b‖ + (2 * η) * ‖x - d‖ :=
          add_le_add hre (mul_le_mul_of_nonneg_right hDd (norm_nonneg _))
        _ ≤ η * (3 * infDist x A) + (2 * η) * (2 * infDist x A) :=
          add_le_add (mul_le_mul_of_nonneg_left hdb' hη.le)
            (mul_le_mul_of_nonneg_left hxd' (by positivity))
        _ = 700 * η * whitneyRadius A x := by rw [hscale]; ring
    calc
      ‖fderiv ℝ (whitneyExtension C hA hne h D) x - D a‖ ≤
          η + (700 * η * whitneyRadius A x) *
            ∑ c ∈ C.nearFinset hA hne x hxA, ‖fderiv ℝ (whitneyWeight C c) x‖ :=
        norm_fderiv_whitneyExtension_sub_le C hA hne h D a b hxA hD' hP
      _ ≤ η + (700 * η * whitneyRadius A x) * (M / whitneyRadius A x) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (hbound A hA hne C x hxA) (by positivity))
      _ = η * (1 + 700 * M) := by field_simp
      _ = ε / 2 := heq

theorem HasWhitneyC1Compatibility.contDiff_whitneyExtension
    {h : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (H : HasWhitneyC1Compatibility A h D) (C : WhitneyBallCover A)
    (hA : IsClosed A) (hne : A.Nonempty) :
    ContDiff ℝ 1 (whitneyExtension C hA hne h D) := by
  apply contDiff_one_iff_fderiv.mpr
  refine ⟨H.differentiable_whitneyExtension C hA hne, continuous_iff_continuousAt.mpr ?_⟩
  intro x
  by_cases hx : x ∈ A
  · exact H.continuousAt_fderiv_whitneyExtension C hA hne hx
  · exact (whitneyExtension_contDiffAt_compl C hA hne h D hx).continuousAt_fderiv (by simp)

/-- **Whitney's C¹ extension theorem**, Simon GMT Theorem 1.6, in continuous
linear-map notation for the prescribed gradient. The extension is constructed
from the compatible closed-set data; no extension or partition is assumed. -/
theorem exists_contDiff_one_extension_of_whitney
    {h : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hA : IsClosed A) (H : HasWhitneyC1Compatibility A h D) :
    ∃ g : E → ℝ, ContDiff ℝ 1 g ∧ EqOn g h A ∧
      ∀ a ∈ A, HasFDerivAt g (D a) a := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, contDiff_const, by simp, by simp⟩
  · obtain ⟨C⟩ := exists_whitneyBallCover hA hne
    refine ⟨whitneyExtension C hA hne h D, H.contDiff_whitneyExtension C hA hne,
      fun a ha => whitneyExtension_eq_on C hA hne h D ha,
      fun a ha => H.hasFDerivAt_whitneyExtension C hA hne ha⟩

end

end Poincare.SimonGMT.Chapter02
