# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.cylinder_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and scope. This is Part (a) of the parent proof of iwl_cr_hausdorff_product_formula (node root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1, Steps 1–4), an elementary covering argument. The statement is verbatim the first conjunct of the parent's frozen type. The constants are slightly coarser than the parent's, which changes nothing in the argument and avoids square roots and real exponents:
- box diameters are bounded by 2·d_i instead of √2·d_i;
- each strip is cut into k_i := ⌊1/d_i⌋ + 1 boxes instead of ⌈1/d_i⌉.
No DAG declaration is used.

Conventions.
(C1) Coordinates. E := Eucl P and E′ := Eucl (P+1). For y ∈ E′ put y_0 := (EuclideanSpace.equiv (Fin (P+1)) ℝ y) 0 and π(y) := (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P+1)) ℝ y)). Splitting off the 0-th coordinate (EuclideanSpace.dist_eq, Fin.sum_univ_succ) gives
  dist(y, y′)² = (y_0 − y′_0)² + dist(π y, π y′)².
(C2) Normalization. μH[d] is Mathlib's d-dimensional Hausdorff measure and ediam is the extended diameter (Metric.ediam).
- By Measure.euclideanHausdorffMeasure_def, μHE[k] S = c_k · μH[k] S, where c_k := addHaarScalarFactor (volume on EuclideanSpace ℝ (Fin k)) μH[k] ∈ ℝ≥0.
- c_k ≠ 0 by Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero.
- Hence μHE[k] S = 0 iff μH[k] S = 0. Here μH[k] means μH[(k : ℝ)].
(C3) N̂ := {y ∈ E′ : π(y) ∈ N}.

1. (Case m = 0.) μHE[0] = μH[0] (Measure.euclideanHausdorffMeasure_zero), and μH[0]{x} = 1 for every point x (Measure.hausdorffMeasure_zero_singleton). If some x ∈ N, monotonicity would give 1 ≤ μH[0](N) = μHE[0](N) = 0. Hence N = ∅, so N̂ = ∅ and μHE[1](N̂) = 0.

2. (Case m ≥ 1: reductions.) By (C2), μH[m](N) = 0, and it suffices to show μH[m+1](N̂) = 0.
- Strips. For a ∈ ℤ let S_a := {y ∈ E′ : π(y) ∈ N, a ≤ y_0 ≤ a + 1}. Every y ∈ N̂ lies in S_{⌊y_0⌋}, so N̂ ⊆ ⋃_{a∈ℤ} S_a. By countable subadditivity (measure_iUnion_null) it suffices to fix a ∈ ℤ and show μH[m+1](S_a) = 0.
- Unfolding the measure. By Measure.hausdorffMeasure_apply,
  μH[m+1](S_a) = ⨆_{r>0} ⨅ { Σ_n ⨆_{t_n ≠ ∅} ediam(t_n)^{m+1} : t : ℕ → Set E′, S_a ⊆ ⋃_n t_n, ∀ n, ediam(t_n) ≤ r }.
- Fix r ∈ (0, ∞]. By ENNReal.le_of_forall_pos_le_add it suffices to show that the infimum belonging to r is ≤ η for every real η > 0. Since ⨆_{t_n≠∅} ediam(t_n)^{m+1} ≤ ediam(t_n)^{m+1}, it suffices to produce:
  (★) sets t_n (n ∈ ℕ) with S_a ⊆ ⋃_n t_n, ediam(t_n) ≤ r for all n, and Σ_n ediam(t_n)^{m+1} ≤ η.
- Fix η > 0.

3. (Parameters.) Choose δ ∈ (0, 1/2] with ENNReal.ofReal δ ≤ r: δ := 1/2 if r = ∞, and δ := min(1/2, r/2) otherwise. Put ε := min((δ/2)^m/2, η/2^{m+3}). Then ε > 0, ε < (δ/2)^m and 2^{m+3}·ε ≤ η.

4. (Covering N.) Consider the infimum in hausdorffMeasure_apply for μH[m](N) at the radius ENNReal.ofReal(δ/2) > 0.
- It is ≤ the supremum μH[m](N) = 0 (iSup₂_eq_bot), hence < ofReal ε.
- Unfolding the three infima (iInf_lt_iff) gives C : ℕ → Set E with N ⊆ ⋃_i C_i, ediam(C_i) ≤ ofReal(δ/2) for all i, and Σ_i ⨆_{C_i ≠ ∅} ediam(C_i)^m < ofReal ε.
- As m ≥ 1, ediam(∅)^m = 0, so the factor ⨆_{C_i≠∅} can be dropped (iSup_pos, iSup_neg, ENNReal.rpow_natCast): Σ_i ediam(C_i)^m < ofReal ε.
- Each ediam(C_i) is finite. Put D_i := (ediam C_i).toReal. Then ediam C_i = ofReal D_i and 0 ≤ D_i ≤ δ/2. Also dist(x, x′) ≤ D_i for x, x′ ∈ C_i (edist_le_ediam_of_mem).

5. (Inflated sizes.)
- Put λ_i := (ε/2/2^i)/(δ/2)^m. Then 0 < λ_i ≤ 1, because ε/2/2^i ≤ ε < (δ/2)^m.
- Put ρ_i := (δ/2)·λ_i. Then 0 < ρ_i ≤ δ/2, and ρ_i^m = (δ/2)^m·λ_i^m ≤ (δ/2)^m·λ_i = ε/2/2^i, since λ_i^m ≤ λ_i for 0 ≤ λ_i ≤ 1 and m ≥ 1.
- Put d_i := max(D_i, ρ_i). Then 0 < d_i ≤ δ/2 ≤ 1/4 and D_i ≤ d_i. Also d_i^m ≤ D_i^m + ε/2/2^i (consider which term is the maximum).

6. (Boxes.) Let k_i := ⌊1/d_i⌋ + 1 ∈ ℕ (Nat.floor). Since ⌊1/d_i⌋ ≤ 1/d_i and 1 ≤ 1/d_i, we have k_i ≤ 2/d_i. For j ∈ ℕ put
  Q_{i,j} := {y ∈ E′ : π(y) ∈ C_i, a + j·d_i ≤ y_0 ≤ a + (j+1)·d_i}.
(i) Diameter. For y, y′ ∈ Q_{i,j}, |y_0 − y′_0| ≤ d_i and dist(π y, π y′) ≤ D_i ≤ d_i. By (C1), dist(y, y′)² ≤ 2d_i² ≤ (2d_i)², i.e. dist(y, y′) ≤ 2d_i. Hence ediam Q_{i,j} ≤ ofReal(2d_i) ≤ ofReal δ ≤ r (Metric.ediam_le_of_forall_dist_le).
(ii) Cover. Let y ∈ S_a and choose i with π(y) ∈ C_i. Put u := (y_0 − a)/d_i ∈ [0, 1/d_i] and j := ⌊u⌋. Then j ≤ ⌊1/d_i⌋ < k_i (Nat.floor_le_floor) and j ≤ u < j + 1. Hence a + j·d_i ≤ y_0 < a + (j+1)·d_i, and y ∈ Q_{i,j}.

7. (The countable family.) For n ∈ ℕ with (i, j) := Nat.unpair n, let t_n := Q_{i,j} if j < k_i, and t_n := ∅ otherwise. Thus t(Nat.pair i j) = Q_{i,j} whenever j < k_i (Nat.unpair_pair). By 6(ii), S_a ⊆ ⋃_n t_n. By 6(i) and ediam ∅ = 0, ediam t_n ≤ r for all n.

8. (The sum.) Using Nat.pairEquiv (Equiv.tsum_eq) and ENNReal.tsum_prod,
  Σ_n ediam(t_n)^{m+1} = Σ_i Σ_j ediam(t(Nat.pair i j))^{m+1}.
- Fix i. Only the j < k_i contribute (tsum_eq_sum over Finset.range k_i), each at most ofReal(2d_i)^{m+1}. Using step 5 and ediam(C_i)^m = ofReal(D_i^m), the inner sum is
  ≤ ofReal(k_i·(2d_i)^{m+1}) ≤ ofReal((2/d_i)·2^{m+1}·d_i^{m+1}) = ofReal(2^{m+2}·d_i^m) ≤ ofReal(2^{m+2})·(ediam(C_i)^m + ofReal(ε/2/2^i)).
- Sum over i (ENNReal.tsum_mul_left, ENNReal.tsum_add). We have Σ_i ediam(C_i)^m < ofReal ε (step 4) and Σ_i ofReal(ε/2/2^i) = ofReal ε (tsum_geometric_two', ENNReal.ofReal_tsum_of_nonneg). Hence
  Σ_n ediam(t_n)^{m+1} ≤ ofReal(2^{m+2})·(ofReal ε + ofReal ε) = ofReal(2^{m+3}·ε) ≤ ofReal η = η.
This proves (★).

9. (Conclusion.) By (★) and step 2, μH[m+1](S_a) = 0 for every a ∈ ℤ. Hence μH[m+1](N̂) = 0, and μHE[m+1](N̂) = c_{m+1}·0 = 0 by (C2). With step 1, the statement holds for all m. ∎

Appendix (Lean, verified). The declaration below proves exactly this frozen statement. It was compiled against the frozen project:
- environment: commit d8d46c9, Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630;
- placement: inside GMT/Ch06/Submission.lean, in `namespace GMT.Ch06` after the contract's `noncomputable section … end`, where accepted `theorem Submission.…` declarations go (the check used a scratch file that imports GMT.Ch06.Submission and replays the contract's namespace and `open` commands);
- `#print axioms` reports [propext, Classical.choice, Quot.sound].
Extra imports to add at the top of GMT/Ch06/Submission.lean: none beyond the frozen contract's imports. The proof uses no auxiliary top-level declarations.

theorem Submission.iwl_cr_hp_cylinder_null : ∀ (P m : ℕ) (N : Set (Eucl P)), (μHE[m] : Measure (Eucl P)) N = 0 → (μHE[m + 1] : Measure (Eucl (P + 1))) {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} = 0 := by
  intro P m N hN
  have hE : ∀ (k : ℕ) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
      [MeasurableSpace X] [BorelSpace X] (S : Set X), (μHE[k] : Measure X) S =
        (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin k))) μH[k] : ℝ≥0∞) *
          μH[k] S := by
    intro k X _ _ _ _ S
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- `m = 0`: a `μH[0]`-null set is empty
    have hNe : N = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
      have h1 : μH[0] ({x} : Set (Eucl P)) ≤ μH[0] N := measure_mono (singleton_subset_iff.mpr hx)
      rw [Measure.hausdorffMeasure_zero_singleton] at h1
      rw [Measure.euclideanHausdorffMeasure_zero] at hN
      rw [hN] at h1
      exact absurd h1 (by simp)
    subst hNe
    simp
  · have hcm : (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin m)))
        μH[m] : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero m
    have hNm : μH[(m : ℝ)] N = 0 := by
      rw [hE m N] at hN
      exact (mul_eq_zero.mp hN).resolve_left hcm
    rw [hE (m + 1)]
    suffices h : μH[((m + 1 : ℕ) : ℝ)] {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} = 0 by rw [h, mul_zero]
    have hsub : {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} ⊆ ⋃ a : ℤ, {y : Eucl (P + 1) |
          (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N ∧
          (a : ℝ) ≤ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∧
          EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ≤ a + 1} := by
      intro y hy
      exact mem_iUnion.2 ⟨⌊EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0⌋, hy, Int.floor_le _,
        (Int.lt_floor_add_one _).le⟩
    have hstrip : ∀ a : ℤ, μH[((m + 1 : ℕ) : ℝ)] {y : Eucl (P + 1) |
        (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N ∧
        (a : ℝ) ≤ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∧
        EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ≤ a + 1} = 0 := by
      intro a
      set π : Eucl (P + 1) → Eucl P := fun y =>
        (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))
        with hπdef
      set y0 : Eucl (P + 1) → ℝ := fun y => EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 with hy0def
      have hdist : ∀ y y' : Eucl (P + 1),
          dist y y' ^ 2 = (y0 y - y0 y') ^ 2 + dist (π y) (π y') ^ 2 := by
        intro y y'
        rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity),
          Real.sq_sqrt (by positivity), Fin.sum_univ_succ]
        simp [hπdef, hy0def, Fin.tail, Real.dist_eq, sq_abs]
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      apply le_antisymm _ zero_le
      rw [Measure.hausdorffMeasure_apply]
      refine iSup₂_le fun r hr => ?_
      refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
      rw [zero_add]
      -- the radius
      obtain ⟨δ, hδ0, hδ1, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ENNReal.ofReal δ ≤ r := by
        rcases eq_or_ne r ⊤ with rfl | hrt
        · exact ⟨1 / 2, by norm_num, le_rfl, le_top⟩
        · have hr' : 0 < r.toReal := ENNReal.toReal_pos hr.ne' hrt
          refine ⟨min (1 / 2) (r.toReal / 2), by positivity, min_le_left _ _, ?_⟩
          calc ENNReal.ofReal (min (1 / 2) (r.toReal / 2)) ≤ ENNReal.ofReal r.toReal :=
                ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (by linarith))
            _ = r := ENNReal.ofReal_toReal hrt
      -- the smallness parameter
      have hη0 : (0 : ℝ) < η := hη
      set ε : ℝ := min ((δ / 2) ^ m / 2) (η / 2 ^ (m + 3)) with hεdef
      have hε0 : 0 < ε := by positivity
      have hεδ : ε < (δ / 2) ^ m := by
        have : 0 < (δ / 2) ^ m := by positivity
        exact (min_le_left _ _).trans_lt (by linarith)
      have hεη : 2 ^ (m + 3) * ε ≤ η := by
        have h := min_le_right ((δ / 2) ^ m / 2) (η / 2 ^ (m + 3))
        rw [← hεdef] at h
        have h2 : (0 : ℝ) < 2 ^ (m + 3) := by positivity
        calc 2 ^ (m + 3) * ε ≤ 2 ^ (m + 3) * (η / 2 ^ (m + 3)) := by gcongr
          _ = η := by field_simp
      -- a cover of `N`
      have hNa := hNm
      rw [Measure.hausdorffMeasure_apply] at hNa
      have hδ2 : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.mpr (by positivity)
      have hF := (iSup₂_eq_bot.mp hNa) (ENNReal.ofReal (δ / 2)) hδ2
      have hlt : (⨅ (t : ℕ → Set (Eucl P)) (_ : N ⊆ ⋃ n, t n)
          (_ : ∀ n, ediam (t n) ≤ ENNReal.ofReal (δ / 2)),
            ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (m : ℝ)) < ENNReal.ofReal ε := by
        rw [hF]; exact ENNReal.ofReal_pos.mpr hε0
      obtain ⟨C, hC⟩ := iInf_lt_iff.mp hlt
      obtain ⟨hCcov, hC⟩ := iInf_lt_iff.mp hC
      obtain ⟨hCdiam, hCsum⟩ := iInf_lt_iff.mp hC
      have hCsum' : ∑' i, ediam (C i) ^ m < ENNReal.ofReal ε := by
        refine lt_of_le_of_lt (le_of_eq ?_) hCsum
        refine tsum_congr fun i => ?_
        rcases (C i).eq_empty_or_nonempty with he | hne
        · have : ¬ (C i).Nonempty := by rw [he]; exact not_nonempty_empty
          rw [iSup_neg this, he, ediam_empty, zero_pow (by omega)]
          rfl
        · rw [iSup_pos hne, ENNReal.rpow_natCast]
      -- real diameters
      set D : ℕ → ℝ := fun i => (ediam (C i)).toReal with hDdef
      have hCfin : ∀ i, ediam (C i) ≠ ⊤ := fun i =>
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hCdiam i)
      have hCeq : ∀ i, ediam (C i) = ENNReal.ofReal (D i) := fun i =>
        (ENNReal.ofReal_toReal (hCfin i)).symm
      have hD0 : ∀ i, 0 ≤ D i := fun i => ENNReal.toReal_nonneg
      have hDδ : ∀ i, D i ≤ δ / 2 := fun i =>
        ENNReal.toReal_le_of_le_ofReal (by positivity) (hCdiam i)
      have hCdist : ∀ i, ∀ x ∈ C i, ∀ x' ∈ C i, dist x x' ≤ D i := by
        intro i x hx x' hx'
        have h := edist_le_ediam_of_mem hx hx'
        rw [hCeq i, edist_dist] at h
        exact (ENNReal.ofReal_le_ofReal_iff (hD0 i)).mp h
      -- inflated diameters
      set lam : ℕ → ℝ := fun i => ε / 2 / 2 ^ i / (δ / 2) ^ m with hlamdef
      have hδm : 0 < (δ / 2) ^ m := by positivity
      have hlam0 : ∀ i, 0 < lam i := fun i => by positivity
      have hlam1 : ∀ i, lam i ≤ 1 := by
        intro i
        rw [hlamdef, div_le_one hδm]
        have h1 : ε / 2 / 2 ^ i ≤ ε := by
          rw [div_div]
          exact div_le_self hε0.le (by
            have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
            linarith)
        linarith
      set ρ : ℕ → ℝ := fun i => δ / 2 * lam i with hρdef
      have hρ0 : ∀ i, 0 < ρ i := fun i => mul_pos (by positivity) (hlam0 i)
      have hρδ : ∀ i, ρ i ≤ δ / 2 := fun i => by
        have := hlam1 i
        have h2 : 0 < δ / 2 := by positivity
        calc ρ i = δ / 2 * lam i := rfl
          _ ≤ δ / 2 * 1 := by gcongr
          _ = δ / 2 := mul_one _
      have hρm : ∀ i, ρ i ^ m ≤ ε / 2 / 2 ^ i := by
        intro i
        have hl := pow_le_of_le_one (hlam0 i).le (hlam1 i) (by omega : m ≠ 0)
        calc ρ i ^ m = (δ / 2) ^ m * lam i ^ m := by rw [hρdef, mul_pow]
          _ ≤ (δ / 2) ^ m * lam i := by gcongr
          _ = ε / 2 / 2 ^ i := by rw [hlamdef]; field_simp
      set d : ℕ → ℝ := fun i => max (D i) (ρ i) with hddef
      have hd0 : ∀ i, 0 < d i := fun i => lt_max_of_lt_right (hρ0 i)
      have hdδ : ∀ i, d i ≤ δ / 2 := fun i => max_le (hDδ i) (hρδ i)
      have hd1 : ∀ i, d i ≤ 1 := fun i => (hdδ i).trans (by linarith)
      have hDd : ∀ i, D i ≤ d i := fun i => le_max_left _ _
      have hdm : ∀ i, d i ^ m ≤ D i ^ m + ε / 2 / 2 ^ i := by
        intro i
        rcases le_total (D i) (ρ i) with h | h
        · rw [hddef]; simp only [max_eq_right h]
          have := hρm i
          have : 0 ≤ D i ^ m := pow_nonneg (hD0 i) m
          linarith
        · rw [hddef]; simp only [max_eq_left h]
          have : 0 ≤ ε / 2 / 2 ^ i := by positivity
          linarith
      -- number of intervals
      set k : ℕ → ℕ := fun i => ⌊1 / d i⌋₊ + 1 with hkdef
      have hk : ∀ i, (k i : ℝ) ≤ 2 / d i := by
        intro i
        have h1 : (⌊1 / d i⌋₊ : ℝ) ≤ 1 / d i := Nat.floor_le (by have := hd0 i; positivity)
        have h2 : (1 : ℝ) ≤ 1 / d i := by rw [le_div_iff₀ (hd0 i)]; linarith [hd1 i]
        simp only [hkdef, Nat.cast_add, Nat.cast_one]
        calc (⌊1 / d i⌋₊ : ℝ) + 1 ≤ 1 / d i + 1 / d i := by linarith
          _ = 2 / d i := by ring
      -- the boxes
      set Q : ℕ → ℕ → Set (Eucl (P + 1)) := fun i j =>
        {y | π y ∈ C i ∧ (a : ℝ) + j * d i ≤ y0 y ∧ y0 y ≤ a + (j + 1) * d i} with hQdef
      have hQdiam : ∀ i j, ediam (Q i j) ≤ ENNReal.ofReal (2 * d i) := by
        intro i j
        refine ediam_le_of_forall_dist_le fun y hy y' hy' => ?_
        have h1 : |y0 y - y0 y'| ≤ d i := by
          rw [abs_le]; constructor <;> nlinarith [hy.2.1, hy.2.2, hy'.2.1, hy'.2.2]
        have h2 : dist (π y) (π y') ≤ d i := (hCdist i _ hy.1 _ hy'.1).trans (hDd i)
        have h3 : dist y y' ^ 2 ≤ (2 * d i) ^ 2 := by
          rw [hdist]
          have : (y0 y - y0 y') ^ 2 ≤ d i ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
          have : dist (π y) (π y') ^ 2 ≤ d i ^ 2 := pow_le_pow_left₀ dist_nonneg h2 2
          nlinarith
        have h4 : 0 ≤ 2 * d i := by have := hd0 i; positivity
        exact (pow_le_pow_iff_left₀ dist_nonneg h4 two_ne_zero).mp h3
      -- the indexed cover
      set t : ℕ → Set (Eucl (P + 1)) := fun n =>
        if n.unpair.2 < k n.unpair.1 then Q n.unpair.1 n.unpair.2 else ∅ with htdef
      have htpair : ∀ i j, t (Nat.pair i j) = if j < k i then Q i j else ∅ := by
        intro i j; simp only [htdef, Nat.unpair_pair]
      have htcov : {y : Eucl (P + 1) | π y ∈ N ∧ (a : ℝ) ≤ y0 y ∧ y0 y ≤ a + 1} ⊆ ⋃ n, t n := by
        intro y hy
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hCcov hy.1)
        set u : ℝ := (y0 y - a) / d i with hudef
        have hu0 : 0 ≤ u := div_nonneg (by linarith [hy.2.1]) (hd0 i).le
        have hu1 : u ≤ 1 / d i := div_le_div_of_nonneg_right (by linarith [hy.2.2]) (hd0 i).le
        set j := ⌊u⌋₊ with hjdef
        have hjk : j < k i := by
          have : ⌊u⌋₊ ≤ ⌊1 / d i⌋₊ := Nat.floor_le_floor hu1
          simp only [hkdef]; omega
        refine mem_iUnion.mpr ⟨Nat.pair i j, ?_⟩
        rw [htpair, ite_eq_left hjk]
        refine ⟨hi, ?_, ?_⟩
        · have h1 : (j : ℝ) ≤ u := Nat.floor_le hu0
          have h2 : (j : ℝ) * d i ≤ y0 y - a := by
            rw [hudef, le_div_iff₀ (hd0 i)] at h1; exact h1
          linarith
        · have h1 : u < j + 1 := Nat.lt_floor_add_one u
          have h2 : y0 y - a < (j + 1) * d i := by
            rw [hudef, div_lt_iff₀ (hd0 i)] at h1; exact h1
          linarith
      have htdiam : ∀ n, ediam (t n) ≤ r := by
        intro n
        simp only [htdef]
        split_ifs
        · exact (hQdiam _ _).trans ((ENNReal.ofReal_le_ofReal (by linarith [hdδ n.unpair.1])).trans hδr)
        · rw [ediam_empty]; exact zero_le
      refine iInf_le_of_le t (iInf_le_of_le htcov (iInf_le_of_le htdiam ?_))
      -- the sum estimate
      have hterm : ∀ n, (⨆ _ : (t n).Nonempty, ediam (t n) ^ ((m + 1 : ℕ) : ℝ)) ≤
          ediam (t n) ^ (m + 1) := fun n => by
        rw [ENNReal.rpow_natCast]; exact iSup_le fun _ => le_rfl
      have hinner : ∀ i, ∑' j, ediam (t (Nat.pair i j)) ^ (m + 1) ≤
          ENNReal.ofReal (2 ^ (m + 2)) * (ediam (C i) ^ m + ENNReal.ofReal (ε / 2 / 2 ^ i)) := by
        intro i
        have hsupp : ∀ j ∉ Finset.range (k i), ediam (t (Nat.pair i j)) ^ (m + 1) = 0 := by
          intro j hj
          rw [Finset.mem_range, not_lt] at hj
          rw [htpair, ite_eq_right (by omega), ediam_empty, zero_pow (by omega)]
        rw [tsum_eq_sum hsupp]
        calc ∑ j ∈ Finset.range (k i), ediam (t (Nat.pair i j)) ^ (m + 1)
            ≤ ∑ j ∈ Finset.range (k i), ENNReal.ofReal (2 * d i) ^ (m + 1) := by
              refine Finset.sum_le_sum fun j hj => ?_
              rw [Finset.mem_range] at hj
              rw [htpair, ite_eq_left hj]
              exact pow_le_pow_left₀ zero_le (hQdiam i j) _
          _ = ENNReal.ofReal ((k i : ℝ) * (2 * d i) ^ (m + 1)) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
                ENNReal.ofReal_pow (by have := hd0 i; positivity)]
          _ ≤ ENNReal.ofReal (2 ^ (m + 2) * (D i ^ m + ε / 2 / 2 ^ i)) := by
              refine ENNReal.ofReal_le_ofReal ?_
              have hdi := hd0 i
              calc (k i : ℝ) * (2 * d i) ^ (m + 1) ≤ 2 / d i * (2 * d i) ^ (m + 1) := by
                    gcongr; exact hk i
                _ = 2 ^ (m + 2) * d i ^ m := by
                    field_simp; ring
                _ ≤ 2 ^ (m + 2) * (D i ^ m + ε / 2 / 2 ^ i) := by gcongr; exact hdm i
          _ = ENNReal.ofReal (2 ^ (m + 2)) * (ediam (C i) ^ m + ENNReal.ofReal (ε / 2 / 2 ^ i)) := by
              rw [ENNReal.ofReal_mul (by positivity), hCeq i,
                ← ENNReal.ofReal_pow (hD0 i), ← ENNReal.ofReal_add (pow_nonneg (hD0 i) _)
                  (by positivity)]
      have hgeom : ∑' i : ℕ, ENNReal.ofReal (ε / 2 / 2 ^ i) = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (summable_geometric_two' ε),
          tsum_geometric_two']
      calc ∑' n, (⨆ _ : (t n).Nonempty, ediam (t n) ^ ((m + 1 : ℕ) : ℝ))
          ≤ ∑' n, ediam (t n) ^ (m + 1) := ENNReal.tsum_le_tsum hterm
        _ = ∑' p : ℕ × ℕ, ediam (t (Nat.pair p.1 p.2)) ^ (m + 1) :=
            (Nat.pairEquiv.tsum_eq (fun n => ediam (t n) ^ (m + 1))).symm
        _ = ∑' i, ∑' j, ediam (t (Nat.pair i j)) ^ (m + 1) :=
            ENNReal.tsum_prod (f := fun i j => ediam (t (Nat.pair i j)) ^ (m + 1))
        _ ≤ ∑' i, ENNReal.ofReal (2 ^ (m + 2)) * (ediam (C i) ^ m + ENNReal.ofReal (ε / 2 / 2 ^ i)) :=
            ENNReal.tsum_le_tsum hinner
        _ = ENNReal.ofReal (2 ^ (m + 2)) * (∑' i, ediam (C i) ^ m +
              ∑' i : ℕ, ENNReal.ofReal (ε / 2 / 2 ^ i)) := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
        _ ≤ ENNReal.ofReal (2 ^ (m + 2)) * (ENNReal.ofReal ε + ENNReal.ofReal ε) := by
            rw [hgeom]; gcongr
        _ = ENNReal.ofReal (2 ^ (m + 3) * ε) := by
            rw [← ENNReal.ofReal_add hε0.le hε0.le, ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
        _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hεη
        _ = (η : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
    exact measure_mono_null hsub (measure_iUnion_null hstrip)

## Key steps

1. μHE[k] = c_k·μH[k] with c_k ∈ ℝ≥0 nonzero, so μHE- and μH-null sets agree; for m = 0, μH[0]{x} = 1 forces N = ∅.
2. For m ≥ 1, N̂ ⊆ ⋃_{a∈ℤ} S_a with S_a = {π ∈ N, a ≤ y_0 ≤ a+1}. Via hausdorffMeasure_apply, it suffices for each r > 0 and η > 0 to cover S_a by sets of ediam ≤ r with Σ ediam^{m+1} ≤ η.
3. Choose δ ≤ 1/2 with δ ≤ r and ε = min((δ/2)^m/2, η/2^{m+3}). From μH[m](N) = 0 extract C_i covering N with ediam ≤ δ/2 and Σ ediam(C_i)^m < ε.
4. Inflate D_i = diam C_i to d_i = max(D_i, ρ_i) with ρ_i^m ≤ ε/2/2^i. Then d_i ≤ δ/2 and d_i^m ≤ D_i^m + ε/2/2^i.
5. Cut [a, a+1] into k_i = ⌊1/d_i⌋ + 1 ≤ 2/d_i intervals of length d_i. The boxes Q_{i,j} = {π ∈ C_i, y_0 ∈ [a + j d_i, a + (j+1) d_i]} cover S_a and have ediam ≤ 2d_i ≤ δ ≤ r.
6. Index the boxes by Nat.pair. Σ ediam^{m+1} ≤ Σ_i 2^{m+2} d_i^m ≤ 2^{m+2}·2ε ≤ η, so μH[m+1](S_a) = 0, hence μHE[m+1](N̂) = 0.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json  (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3: read /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/{parent-child-handoff.json, parent-supplied-natural-proof.json, parent-supplied-natural-proof.md, parent-supplied-plan.md}`
- `python3: dag.json node statuses and lean_names (lpf_raf_*, lpf_countably_rectifiable_c1_cover, rectifiability_weighted_tangent_ae, iwl_cr_*); grep -r 'iwl_cr_hp_' over the run directory (no match)`
- `grep -n 'theorem hausdorffMeasure_apply|hausdorffMeasure_le_liminf_tsum|hausdorffMeasure_zero_singleton' Mathlib/MeasureTheory/Measure/Hausdorff.lean; grep 'euclideanHausdorffMeasure_def|euclideanHausdorffMeasure_zero|addHaarScalarFactor_volume_hausdorffMeasure_ne_zero' Mathlib/Geometry/Euclidean/Volume/Measure.lean (snapshot)`
- `sed -n 250,275p Mathlib/MeasureTheory/Function/Jacobian.lean (exists_partition_approximatesLinearOn_of_hasFDerivWithinAt); grep measurePreserving_piFinSuccAbove Mathlib/MeasureTheory/Constructions/Pi.lean; grep 'PiLp.volume_preserving_ofLp|PiLp.volume_preserving_toLp' Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean; grep det_succ_row_zero Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean; grep exists_measurable_subset_ae_eq Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `sed -n 290,320p Mathlib/Analysis/InnerProductSpace/NormDet.lean (LinearMap.normDet_sq_eq_det_gram, any Fintype index)`
- `grep -rn 'setLIntegral_comp_preimage|theorem prod_restrict|theorem lintegral_prod |Measurable.lintegral_prod_right'|MeasurePreserving.prod|LipschitzWith.prodMk' Mathlib/ (snapshot)`
- `grep -rn 'ediam_le|edist_le_ediam_of_mem|ediam_empty|ediam_le_of_forall_dist_le' Mathlib/Topology/EMetricSpace/Diam.lean Mathlib/Topology/MetricSpace/Bounded.lean (snapshot)`
- `simongmt: cat Chapter02/AreaLipschitz.lean; sed Chapter02/Area.lean, Chapter02/AreaParametrization.lean, Chapter02/AreaApproximation.lean; grep -rn 'theorem areaJacobianAt'; sed -n 28,80p Chapter03/Rectifiable.lean (CountablyRectifiable, CountablyRectifiable.mono)`
- `git show 2f36576:GMT/Ch06/Submission.lean (accepted rectifiability_weighted_tangent_ae, hparam/hpart piece construction); git show a46aa05:GMT/Ch06/Submission.lean and accepted candidate diffs (declaration conventions)`
- `verifier: gmt-compare.py contract_scope/child_modules and lean_contract.validate_lean_statement; python3 -I /tmp/hp_decomp/scripts/gen.py children_v1.json -> NodeChallenge files; lake env lean on each (all elaborate)`
- `lake env lean /tmp/hp_decomp/T0.lean (areaJacobianAt, weighted_area_formula_lipschitz_injOn and LinearMap.normDet_sq_eq_det_gram unknown under frozen imports; MeasurableSet.image_of_continuousOn_injOn, measurePreserving_piFinSuccAbove available)`
- `lake env lean /tmp/hp_decomp/scratch/{Assembly,JacBridge,LiftGram,PieceProduct,Pieces,Cyl}.lean and /tmp/hp_decomp/final/{All,Check_iwl_cr_hp_*}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/speculative-prompt-v3.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaParametrization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/hp_decomp/T0.lean`
- `/tmp/hp_decomp/scratch/Assembly.lean`
- `/tmp/hp_decomp/scratch/JacBridge.lean`
- `/tmp/hp_decomp/scratch/LiftGram.lean`
- `/tmp/hp_decomp/scratch/PieceProduct.lean`
- `/tmp/hp_decomp/scratch/Pieces.lean`
- `/tmp/hp_decomp/scratch/Cyl.lean`
- `/tmp/hp_decomp/final/All.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_cylinder_null.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_injective_pieces.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_lift_gram_det.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_piece_product.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c; the frozen contract is Contract.lean, and Submission.lean is identical to it at the dispatch base.

Library inputs found (all with standard axioms):
- Mathlib supplies:
  - Hausdorff measure: hausdorffMeasure_apply (ediam form), hausdorffMeasure_zero_singleton, euclideanHausdorffMeasure_def/_zero, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero;
  - pieces: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (root namespace), MeasurableSet.image_of_continuousOn_injOn;
  - linear algebra: LinearMap.normDet_sq_eq_det_gram (any Fintype index, so EuclideanSpace.basisFun works), Matrix.det_succ_row_zero;
  - integration: measurePreserving_piFinSuccAbove, PiLp.volume_preserving_ofLp/toLp, MeasurePreserving.setLIntegral_comp_preimage, Measure.prod_restrict, lintegral_prod, Measurable.lintegral_prod_right', NullMeasurableSet.exists_measurable_subset_ae_eq;
  - diameters: Metric.ediam_le_of_forall_dist_le, edist_le_ediam_of_mem.
- SimonGMT 2b36630 supplies weighted_area_formula_lipschitz_injOn, area_image_compl_regularSet_eq_zero, measurableSet_areaRegularSet, measurable_areaJacobianAt, areaJacobianAt_eq_normDet/_nonneg, CountablyRectifiable (F_j : EuclideanSpace ℝ (Fin n) → E) and CountablyRectifiable.mono.
- Neither library has a Hausdorff product formula for rectifiable sets; only hausdorffMeasure_pi_real/prod_real exist.
- No DAG node supplies the needed lemmas with compatible types:
  - the lpf_raf_* area lemmas are chart/fibre-sum forms;
  - lpf_countably_rectifiable_c1_cover is only speculative-ready.
  So the split relies on library theorems only.

Scope check: areaJacobianAt, the SimonGMT area formula and LinearMap.normDet are NOT visible after `import GMT.Ch06.Submission` with the frozen imports. Hence lift_gram_det is stated with Gram determinants (Matrix.of … inner ℝ … EuclideanSpace.single). All four child statements elaborate in verifier-generated challenge modules.

Lean results:
- Scratch proofs of all four children with exactly the proposed types, and of the parent's exact frozen type from them, compile with only propext, Classical.choice and Quot.sound, and with zero warnings.
- Per-child compiles succeed with the minimal imports listed in each appendix.
- The accepted hparam/hpart code (commit 2f36576) was reused for injective_pieces.
- No name collisions with dag.json.
