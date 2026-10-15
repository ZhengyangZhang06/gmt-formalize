# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1.density_comparison-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 3 (Simon Ch. 1, Theorem 3.3 with Lemma 3.4(*) and Corollary 3.5; book/chapter-01.txt lines 602–696). The parent's claim is the special case μ = μHE[n]⌞(M ∩ A₂); the argument below is the parent's argument, written for an arbitrary measure μ. Notation: Hⁿ = μHE[n] and ω = ω_n = unitBallVolume n. All quantities lie in [0, ∞], and ediam is the extended diameter. For b = (y, ρ) ∈ ℝ^P × ℝ write B(b) := B̄_ρ(y).
1. Reductions. If μ(ℝ^P) = ∞ the inequality is trivial. If A = ∅ then Hⁿ(A) = 0 and it is again trivial. So assume μ(ℝ^P) < ∞ and fix x₀ ∈ A; then t < (limsup at x₀) ≤ ∞ forces t < ∞. Moreover 0 < ω < ∞, because ω is the volume of the nonempty, open, bounded unit ball of Euclid n (measure_ball_pos, measure_ball_lt_top). Hence 0 < tω < ∞.
2. Fineness. Let x ∈ A and η > 0. Because t < limsup_{r→0+} μ(B̄_r(x))/(ω·ofReal(rⁿ)), the quotient exceeds t frequently as r → 0+ (Filter.frequently_lt_of_lt_limsup; boundedness is automatic in the complete lattice [0, ∞]). Since r ∈ (0, η) eventually (Ioo_mem_nhdsGT), there is ρ ∈ (0, η) with t < μ(B̄_ρ(x))/(ω·ofReal(ρⁿ)). As 0 < ω·ofReal(ρⁿ) < ∞, this is equivalent to t·ω·ofReal(ρ)ⁿ < μ(B̄_ρ(x)) (ENNReal.lt_div_iff_mul_lt, ENNReal.ofReal_pow).
3. Covers at scale δ with slack ε. Fix δ > 0 and ε ∈ (0, ∞], and put D := 2ⁿ·(μ(ℝ^P)/(tω)). We build a countable family (C_b)_{b∈u} such that A ⊆ ⋃_b C_b, ediam C_b ≤ ofReal(5δ) for every b, and Σ_b ediam(C_b)ⁿ ≤ D + ε.
(a) Vitali selection (Simon 3.4(*)). Let T := {(y, ρ) : y ∈ A, 0 < ρ < δ/2, tω·ofReal(ρ)ⁿ < μ(B̄_ρ(y))}. Apply Vitali.exists_disjoint_subfamily_covering_enlargement to the family b ↦ B(b) indexed by T, with size function (y, ρ) ↦ ρ, factor τ = 2 and bound R = δ/2. On T the sizes lie in [0, R] and every B(b) is nonempty. This gives u ⊆ T such that the balls B(b), b ∈ u, are pairwise disjoint, and every a = (y, ρ) ∈ T admits some b = (y_b, ρ_b) ∈ u with B(a) ∩ B(b) ≠ ∅ and ρ ≤ 2ρ_b.
(b) Countability. Each B(b), b ∈ u, contains the nonempty open ball B_{ρ_b}(y_b), since ρ_b > 0. A pairwise disjoint family of sets with nonempty interior in the separable space ℝ^P is countable (Set.PairwiseDisjoint.countable_of_nonempty_interior). So u is countable.
(c) Packing. Put s_b := ofReal(ρ_b)ⁿ for b ∈ u. The B(b) are disjoint closed, hence measurable, sets, so tω·Σ_{b∈u} s_b = Σ_{b∈u} tω·s_b ≤ Σ_{b∈u} μ(B(b)) = μ(⋃_{b∈u} B(b)) ≤ μ(ℝ^P) (measure_biUnion). Hence S := Σ_{b∈u} s_b ≤ μ(ℝ^P)/(tω) < ∞.
(d) Finite part. As S < ∞, the tail sums Σ_{b∈u∖F} s_b tend to 0 along the finite subsets F of u ordered by inclusion (ENNReal.tendsto_tsum_compl_atTop_zero). Since ε/10ⁿ > 0, choose a finite F ⊆ u with Σ_{b∈u∖F} s_b < ε/10ⁿ.
(e) The cover. For b ∈ u let C_b := B̄_{ρ_b}(y_b) if b ∈ F, and C_b := B̄_{5ρ_b}(y_b) if b ∉ F.
(f) A ⊆ ⋃_{b∈u} C_b (Simon 3.5). Let x ∈ A. If x ∈ B(b) for some b ∈ F, then x ∈ C_b. Otherwise x lies outside the closed set K := ⋃_{b∈F} B(b), a finite union of closed balls, so there is η > 0 with B_η(x) ∩ K = ∅. By step 2 choose ρ with 0 < ρ < min(η/2, δ/2) and tω·ofReal(ρ)ⁿ < μ(B̄_ρ(x)); then a := (x, ρ) ∈ T. By (a) there are b = (y_b, ρ_b) ∈ u and a point z ∈ B̄_ρ(x) ∩ B(b) with ρ ≤ 2ρ_b. Since d(z, x) ≤ ρ < η, z ∈ B_η(x), so z ∉ K; as z ∈ B(b), this forces b ∉ F. Finally d(x, y_b) ≤ d(x, z) + d(z, y_b) ≤ ρ + ρ_b ≤ 3ρ_b ≤ 5ρ_b, so x ∈ B̄_{5ρ_b}(y_b) = C_b.
(g) Diameters. A closed ball of radius r has extended diameter ≤ ofReal(2r), by ediam_le_of_forall_dist_le and the triangle inequality. Hence ediam C_b ≤ ofReal(10ρ_b) ≤ ofReal(5δ), because ρ_b < δ/2. Moreover ediam(C_b)ⁿ ≤ (2·ofReal ρ_b)ⁿ = 2ⁿ·s_b when b ∈ F, and ediam(C_b)ⁿ ≤ (10·ofReal ρ_b)ⁿ = 10ⁿ·s_b when b ∉ F. (Mathlib's Hausdorff sums use the real exponent (n : ℝ); x^(n:ℝ) = xⁿ by ENNReal.rpow_natCast.)
(h) Cost. By (g), ediam(C_b)ⁿ ≤ 2ⁿ·s_b + 1_{b∉F}·10ⁿ·s_b for every b ∈ u. Sum this over u, using ENNReal.tsum_add and ENNReal.tsum_mul_left, and tsum_subtype to turn the indicator sum into a sum over {b ∈ u : b ∉ F}. This gives Σ_{b∈u} ediam(C_b)ⁿ ≤ 2ⁿ·S + 10ⁿ·Σ_{b∈u∖F} s_b ≤ 2ⁿ·μ(ℝ^P)/(tω) + 10ⁿ·(ε/10ⁿ) = D + ε (ENNReal.mul_div_cancel, using 0 < 10ⁿ < ∞).
4. Hausdorff measure. Let ε > 0. For each k ∈ ℕ apply step 3 with δ_k := 1/(k+1) and this ε, obtaining countable families (C^k_b)_{b∈u_k}. Then r_k := ofReal(5/(k+1)) → 0, ediam C^k_b ≤ r_k for all b, every family covers A, and Σ_b ediam(C^k_b)ⁿ ≤ D + ε for every k. By Measure.hausdorffMeasure_le_liminf_tsum (index set ℕ with the filter atTop, countable index types u_k), μH[n](A) ≤ liminf_k Σ_b ediam(C^k_b)ⁿ ≤ D + ε (liminf_le_of_frequently_le'). Since ε > 0 is arbitrary, μH[n](A) ≤ D = 2ⁿ·μ(ℝ^P)/(tω) (ENNReal.le_of_forall_pos_le_add).
5. Normalisation. (IB) holds setwise for every subset of ℝ^P, measurable or not (Measure.le_iff'; (c•ν)(A) = c·ν(A) by Measure.smul_apply). Hence Hⁿ(A) ≤ (ω/2ⁿ)·μH[n](A) ≤ (ω/2ⁿ)·2ⁿ·(μ(ℝ^P)/(tω)) = ω·(μ(ℝ^P)/(tω)) (ENNReal.div_mul_cancel, using 0 < 2ⁿ < ∞). Multiplying by t gives t·Hⁿ(A) ≤ tω·(μ(ℝ^P)/(tω)) = μ(ℝ^P) (ENNReal.mul_div_cancel, using 0 < tω < ∞). ∎

Validated Lean tactic script. It was kernel-checked during this decomposition inside a copy of GMT/Ch07/Submission.lean, at the insertion point used for child declarations, with default heartbeats; the only axioms are propext, Classical.choice and Quot.sound. It is the body after `theorem Submission.cbr_ci_gp_density_comparison : <frozen type> := by`:
```lean
  intro P n μ A t hIB ht hA
  -- Step 1: trivial cases
  rcases eq_or_ne (μ univ) ∞ with hμ | hμ
  · rw [hμ]; exact le_top
  rcases A.eq_empty_or_nonempty with hAe | ⟨x₀, hx₀⟩
  · simp [hAe]
  have htop : t ≠ ∞ := ne_top_of_lt (hA x₀ hx₀)
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  set ω := unitBallVolume n with hωdef
  have htω0 : t * ω ≠ 0 := mul_ne_zero ht.ne' hω0
  have htωtop : t * ω ≠ ∞ := ENNReal.mul_ne_top htop hωtop
  -- Step 2: fineness
  have hfine : ∀ x ∈ A, ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ρ < η ∧
      t * ω * ENNReal.ofReal ρ ^ n < μ (closedBall x ρ) := by
    intro x hx η hη
    have hfreq : ∃ᶠ r in 𝓝[>] (0:ℝ), t < μ (closedBall x r) / (ω * ENNReal.ofReal (r ^ n)) :=
      frequently_lt_of_lt_limsup (by isBoundedDefault) (hA x hx)
    obtain ⟨ρ, hρ, hρη⟩ := (hfreq.and_eventually (Ioo_mem_nhdsGT hη)).exists
    refine ⟨ρ, hρη.1, hρη.2, ?_⟩
    have hw0 : ω * ENNReal.ofReal (ρ ^ n) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.ofReal_pos.2 (pow_pos hρη.1 n)).ne'
    have hwtop : ω * ENNReal.ofReal (ρ ^ n) ≠ ∞ := ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hw0) (Or.inl hwtop)] at hρ
    rw [← ENNReal.ofReal_pow hρη.1.le, mul_assoc]
    exact hρ
  -- Steps 3–8: for every scale δ and slack ε a cheap countable cover of A
  set D : ℝ≥0∞ := 2 ^ n * (μ univ / (t * ω)) with hD
  have hcover : ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ u : Set (Euclid P × ℝ), u.Countable ∧ ∃ c : u → Set (Euclid P),
        (∀ b, ediam (c b) ≤ ENNReal.ofReal (5 * δ)) ∧ A ⊆ ⋃ b, c b ∧
        ∑' b, ediam (c b) ^ (n : ℝ) ≤ D + ε := by
    intro δ hδ ε hε
    set T : Set (Euclid P × ℝ) := {p | p.1 ∈ A ∧ 0 < p.2 ∧ p.2 < δ / 2 ∧
      t * ω * ENNReal.ofReal p.2 ^ n < μ (closedBall p.1 p.2)} with hT
    -- Step 3: Vitali selection with the intersection-and-radius property
    obtain ⟨u, huT, hdisj, hmeet⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun p : Euclid P × ℝ => closedBall p.1 p.2) T (fun p => p.2) 2 one_lt_two
      (fun p hp => hp.2.1.le) (δ / 2) (fun p hp => hp.2.2.1.le)
      (fun p hp => nonempty_closedBall.2 hp.2.1.le)
    -- Step 5: countability
    have hucount : u.Countable := by
      apply hdisj.countable_of_nonempty_interior
      intro p hp
      refine ⟨p.1, interior_mono ball_subset_closedBall ?_⟩
      rw [isOpen_ball.interior_eq]
      exact mem_ball_self (huT hp).2.1
    have : Countable u := hucount.to_subtype
    refine ⟨u, hucount, ?_⟩
    -- Step 6: packing
    set s : u → ℝ≥0∞ := fun b => ENNReal.ofReal (b : Euclid P × ℝ).2 ^ n with hs
    have hpack : t * ω * ∑' b, s b ≤ μ univ := by
      rw [← ENNReal.tsum_mul_left]
      calc ∑' b : u, t * ω * s b
          ≤ ∑' b : u, μ (closedBall (b : Euclid P × ℝ).1 (b : Euclid P × ℝ).2) :=
            ENNReal.tsum_le_tsum fun b => (huT b.2).2.2.2.le
        _ = μ (⋃ b ∈ u, closedBall b.1 b.2) :=
            (measure_biUnion hucount hdisj fun b _ => measurableSet_closedBall).symm
        _ ≤ μ univ := measure_mono (subset_univ _)
    have hS : ∑' b, s b ≤ μ univ / (t * ω) := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl htω0) (Or.inl htωtop), mul_comm]; exact hpack
    have hSfin : ∑' b, s b ≠ ∞ := ne_top_of_le_ne_top (ENNReal.div_ne_top hμ htω0) hS
    -- Step 8 (tail): a finite subfamily whose complement has small total cost
    have htail := ENNReal.tendsto_tsum_compl_atTop_zero hSfin
    have h10top : (10 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
    have h10ne : (10 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    obtain ⟨F, hF⟩ := (htail.eventually (gt_mem_nhds (ENNReal.div_pos hε h10top))).exists
    classical
    refine ⟨fun b => if b ∈ F then closedBall (b : Euclid P × ℝ).1 (b : Euclid P × ℝ).2
      else closedBall (b : Euclid P × ℝ).1 (5 * (b : Euclid P × ℝ).2), ?_, ?_, ?_⟩
    · -- diameters
      intro b
      have hb := huT b.2
      have hρ0 : 0 < (b : Euclid P × ℝ).2 := hb.2.1
      have hρδ : (b : Euclid P × ℝ).2 < δ / 2 := hb.2.2.1
      dsimp only
      split_ifs
      · refine ediam_le_of_forall_dist_le fun y hy z hz => ?_
        rw [mem_closedBall] at hy hz
        linarith [dist_triangle_right y z (b : Euclid P × ℝ).1]
      · refine ediam_le_of_forall_dist_le fun y hy z hz => ?_
        rw [mem_closedBall] at hy hz
        linarith [dist_triangle_right y z (b : Euclid P × ℝ).1]
    · -- Step 7 (Simon 3.5): the tail enlargements cover what the finite part misses
      intro x hx
      by_cases hxK : x ∈ ⋃ b ∈ F, closedBall (b : Euclid P × ℝ).1 (b : Euclid P × ℝ).2
      · obtain ⟨b, hbF, hxb⟩ := mem_iUnion₂.1 hxK
        exact mem_iUnion.2 ⟨b, by simp only [hbF, ite_true]; exact hxb⟩
      · have hKc : IsClosed (⋃ b ∈ F, closedBall (b : Euclid P × ℝ).1 (b : Euclid P × ℝ).2) :=
          isClosed_biUnion_finset fun b _ => isClosed_closedBall
        obtain ⟨η, hη, hηball⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl x hxK
        obtain ⟨ρ, hρ0, hρη, hρμ⟩ := hfine x hx (min (η / 2) (δ / 2)) (by positivity)
        have haT : (x, ρ) ∈ T := ⟨hx, hρ0, lt_of_lt_of_le hρη (min_le_right _ _), hρμ⟩
        obtain ⟨b, hbu, ⟨z, hz1, hz2⟩, hle⟩ := hmeet (x, ρ) haT
        have hzx : dist z x ≤ ρ := hz1
        have hzb : dist z b.1 ≤ b.2 := hz2
        have hle' : ρ ≤ 2 * b.2 := hle
        have hbF : (⟨b, hbu⟩ : u) ∉ F := by
          intro hbF
          have hzK : z ∈ ⋃ b ∈ F, closedBall (b : Euclid P × ℝ).1 (b : Euclid P × ℝ).2 :=
            mem_biUnion hbF hz2
          have hzball : z ∈ ball x η := by
            rw [mem_ball]
            have : ρ < η / 2 := lt_of_lt_of_le hρη (min_le_left _ _)
            linarith
          exact hηball hzball hzK
        refine mem_iUnion.2 ⟨⟨b, hbu⟩, ?_⟩
        simp only [hbF, ite_false]
        rw [mem_closedBall]
        have hb0 : 0 < b.2 := (huT hbu).2.1
        calc dist x b.1 ≤ dist x z + dist z b.1 := dist_triangle _ _ _
          _ ≤ ρ + b.2 := by rw [dist_comm] at hzx; linarith
          _ ≤ 5 * b.2 := by linarith
    · -- Step 8: the cost of the cover
      have hterm : ∀ b : u, ediam (if b ∈ F then closedBall (b : Euclid P × ℝ).1 (b : Euclid P × ℝ).2
          else closedBall (b : Euclid P × ℝ).1 (5 * (b : Euclid P × ℝ).2)) ^ (n : ℝ)
          ≤ 2 ^ n * s b + {b : u | b ∉ F}.indicator (fun b => 10 ^ n * s b) b := by
        intro b
        have hb0 : 0 < (b : Euclid P × ℝ).2 := (huT b.2).2.1
        rw [ENNReal.rpow_natCast]
        split_ifs with hbF
        · have hd : ediam (closedBall (b : Euclid P × ℝ).1 (b : Euclid P × ℝ).2)
              ≤ 2 * ENNReal.ofReal (b : Euclid P × ℝ).2 := by
            calc _ ≤ ENNReal.ofReal (2 * (b : Euclid P × ℝ).2) :=
                  ediam_le_of_forall_dist_le fun y hy z hz => by
                    rw [mem_closedBall] at hy hz
                    linarith [dist_triangle_right y z (b : Euclid P × ℝ).1]
              _ = 2 * ENNReal.ofReal (b : Euclid P × ℝ).2 := by
                  rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
          calc _ ≤ (2 * ENNReal.ofReal (b : Euclid P × ℝ).2) ^ n := by gcongr
            _ = 2 ^ n * s b := by rw [mul_pow]
            _ ≤ _ := le_self_add
        · have hd : ediam (closedBall (b : Euclid P × ℝ).1 (5 * (b : Euclid P × ℝ).2))
              ≤ 10 * ENNReal.ofReal (b : Euclid P × ℝ).2 := by
            calc _ ≤ ENNReal.ofReal (10 * (b : Euclid P × ℝ).2) :=
                  ediam_le_of_forall_dist_le fun y hy z hz => by
                    rw [mem_closedBall] at hy hz
                    linarith [dist_triangle_right y z (b : Euclid P × ℝ).1]
              _ = 10 * ENNReal.ofReal (b : Euclid P × ℝ).2 := by
                  rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
          have hind : {b : u | b ∉ F}.indicator (fun b => 10 ^ n * s b) b = 10 ^ n * s b :=
            indicator_of_mem (show b ∈ {b : u | b ∉ F} from hbF) _
          calc _ ≤ (10 * ENNReal.ofReal (b : Euclid P × ℝ).2) ^ n := by gcongr
            _ = 10 ^ n * s b := by rw [mul_pow]
            _ ≤ _ := by rw [hind]; exact le_add_self
      calc ∑' b, _ ≤ ∑' b : u, (2 ^ n * s b + {b : u | b ∉ F}.indicator (fun b => 10 ^ n * s b) b) :=
            ENNReal.tsum_le_tsum hterm
        _ = 2 ^ n * ∑' b, s b + 10 ^ n * ∑' b : {b : u // b ∉ F}, s b := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ← tsum_subtype {b : u | b ∉ F}
              (fun b => 10 ^ n * s b), ENNReal.tsum_mul_left]
            rfl
        _ ≤ D + ε := by
            refine add_le_add (by rw [hD]; exact mul_le_mul_right hS _) ?_
            calc 10 ^ n * ∑' b : {b : u // b ∉ F}, s b ≤ 10 ^ n * (ε / 10 ^ n) :=
                  mul_le_mul_right hF.le _
              _ = ε := ENNReal.mul_div_cancel h10ne h10top
  -- Step 9: the Hausdorff measure bound
  have hH : μH[(n : ℝ)] A ≤ D := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε' : (ε : ℝ≥0∞) ≠ 0 := by simpa using hε.ne'
    have hk : ∀ k : ℕ, ∃ u : Set (Euclid P × ℝ), u.Countable ∧ ∃ c : u → Set (Euclid P),
        (∀ b, ediam (c b) ≤ ENNReal.ofReal (5 * (1 / ((k : ℝ) + 1)))) ∧ A ⊆ ⋃ b, c b ∧
        ∑' b, ediam (c b) ^ (n : ℝ) ≤ D + ε := fun k => hcover _ (by positivity) _ hε'
    choose u hu c hc1 hc2 hc3 using hk
    have : ∀ k, Countable (u k) := fun k => (hu k).to_subtype
    have hlim := Measure.hausdorffMeasure_le_liminf_tsum (X := Euclid P) (ι := fun k => u k)
      (n : ℝ) A (l := atTop) (fun k : ℕ => ENNReal.ofReal (5 * (1 / ((k : ℝ) + 1))))
      (by
        rw [show (0 : ℝ≥0∞) = ENNReal.ofReal (5 * 0) by simp]
        exact ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 5))
      c (Eventually.of_forall hc1) (Eventually.of_forall hc2)
    exact hlim.trans (liminf_le_of_frequently_le' (Frequently.of_forall hc3))
  -- Step 10: the isodiametric normalisation
  have hle : μHE[n] A ≤ ω / 2 ^ n * μH[(n : ℝ)] A := by
    have := Measure.le_iff'.1 hIB A
    rwa [Measure.smul_apply, smul_eq_mul] at this
  have h2 : (2 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2top : (2 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  calc t * μHE[n] A ≤ t * (ω / 2 ^ n * D) := by gcongr; exact hle.trans (by gcongr)
    _ = μ univ := by
      rw [hD, ← mul_assoc (ω / 2 ^ n), ENNReal.div_mul_cancel h2 h2top, ← mul_assoc,
        ENNReal.mul_div_cancel htω0 htωtop]
```

## Key steps

1. Reduce to μ(ℝ^P) < ∞ and A ≠ ∅, so 0 < t < ∞ and 0 < ω_n < ∞.
2. Fineness: every x ∈ A has arbitrarily small ρ with t·ω_n·ρⁿ < μ(B̄_ρ(x)).
3. Vitali selection (factor 2) gives a countable disjoint subfamily u with the meet-and-radius property; packing gives Σ_u ρ_bⁿ ≤ μ(ℝ^P)/(tω_n) < ∞.
4. Simon 3.5 tail cover: choose finite F ⊆ u with small tail; then A ⊆ ⋃_F B_b ∪ ⋃_{u∖F} 5B_b, at scale 5δ, with cost ≤ 2ⁿμ(ℝ^P)/(tω_n) + ε.
5. Measure.hausdorffMeasure_le_liminf_tsum with δ_k = 1/(k+1) gives μH[n](A) ≤ 2ⁿμ(ℝ^P)/(tω_n).
6. (IB), applied setwise, gives t·μHE[n](A) ≤ t(ω_n/2ⁿ)μH[n](A) ≤ μ(ℝ^P).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean (identical); grep -n 'def unitBallVolume' and 'abbrev MultiVector' in the snapshot Contract.lean (lines 143, 48)`
- `grep -n 'theorem exists_disjoint_subfamily_covering_enlargement' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean (line 59)`
- `grep -n 'theorem hausdorffMeasure_le_liminf_tsum' and 'theorem hausdorffMeasure_apply' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean (lines 555, 546)`
- `grep -n 'theorem ae_tendsto_lintegral_enorm_sub_div' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean (line 818)`
- `grep -n 'def vitaliFamily' and 'theorem tendsto_filterAt' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean (lines 1021, 1060)`
- `grep -rn 'theorem tendsto_tsum_compl_atTop_zero' <snapshot>/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ (ENNReal.lean line 235)`
- `grep -n 'countable_of_nonempty_interior' <snapshot>/mathlib/Mathlib/Topology/Bases.lean (line 493)`
- `grep -n 'exists_isOpen_lt_of_lt' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean (line 359)`
- `grep -rn 'theorem le_iff' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/ (CompleteLattice.lean line 46: Measure.le_iff' is setwise for all sets)`
- `grep -n 'frequently_lt_of_lt_limsup' and 'eventually_lt_of_limsup_lt' <snapshot>/mathlib/Mathlib/Order/LiminfLimsup.lean (lines 646, 605)`
- `grep -n 'euclideanHausdorffMeasure' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (def at line 68: μHE[d] = volume.addHaarScalarFactor μH[d] • μH[d])`
- `lean with LEAN_PATH from lake env on /tmp/gp-decomp/Check1.lean, Inst.lean, Inst2.lean, Api1.lean, Api2.lean (import GMT.Ch07.Submission): all cited lemmas reachable; HasBesicovitchCovering (Euclid P) and OuterRegular of finite measures found; Integrable τ μ for τ : Euclid P → MultiVector P n fails (ContinuousENorm not synthesized; the TopologicalSpace instance is ContinuousLinearMap.topologicalSpace, equal by rfl to the norm topology)`
- `lean on /tmp/gp-decomp/Final.lean and /tmp/gp-decomp/SubmissionInplace.lean: four child theorems proved from their exact frozen types, plus the parent assembly with the IB type as hypothesis; #print axioms gives propext, Classical.choice, Quot.sound`
- `python3 -I scan of dag.json: 1322 lean_names, none with prefix cbr_ci_gp_; the selected type and the cbr_ci_euclideanHausdorff_le_isodiametric type are equal to the strings used; inspected limsup/upper-density/covector nodes (regcomp_atl_upper_density_zero, idtp_dema_upper_density_zero, doraggt_ae_rescaled_lebesgue_point, regcomp_covector_*, cbr_lower_density_of_slice_property): no identical type to reuse`
- `git show 031b51256 (accepted Submission.regcomp_atl_upper_density_zero: Vitali + Measure.hausdorffMeasure_le_liminf_tsum pattern with crude constant 6^n)`
- `sed -n 1,100p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean (outerMeasure_le_tsum_of_fiveTimesCovering, simon_theorem_3_3: sharp-constant finite-tail argument, outside the contract import closure); Chapter06/Mass.lean covectorEuclideanNorm; Chapter06/Forms.lean Covector`
- `sed -n 560,735p and 1190,1240p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt (Simon 3.1-3.8, 3.26)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on the four child types (all pass); leaf_verification.check_source_delta forbidden-token regex on the four proof bodies (no hits)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_existing_lean_name_problem, _solve_children, _render_parent_supplied_plan: children receive only their own sibling prerequisites)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/CompleteLattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-479700eeeb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/tmp/gp-decomp/Final.lean`
- `/tmp/gp-decomp/SubmissionInplace.lean`

Contract and reuse: the snapshot contract (project b4d606db, Mathlib 25730c7c) is byte-identical to the workspace Submission.lean. Every Mathlib lemma used by the child proofs exists in the snapshot and is reachable from import GMT.Ch07.Submission. The SimonGMT formalization of Simon 3.3 is not importable from the contract, so density_comparison re-proves it and takes IB as an explicit hypothesis. No existing DAG declaration has an identical type, and the cbr_ci_gp_ names are fresh.

Instance finding: Integrable cannot be stated for MultiVector-valued maps with default instances, so the L1 data is passed as StronglyMeasurable plus a finite ∫⁻‖·‖ₑ.

Validation: all four child types elaborate in contract scope and pass the verifier's lexical check. Each child was proved sorry-free from its exact frozen type, compiled inside a copy of Submission.lean. The frozen parent type follows from upper_density, weighted_field and lebesgue_error together with the IB sibling. Only propext, Classical.choice and Quot.sound are used.
