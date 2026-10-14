# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.cutoff_estimates-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.cutoff_estimates-a1.radial_cutoff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof step 2: the C¹ cut-off that replaces Simon's Lipschitz cut-offs in Ch. 3, 4.3 (3)–(4), chapter-03.txt lines 621–636. The superlevel sets {ζ ≥ t} are described as in parent step 4. Three details below are filled in to justify the parent's assertions: the one-sided derivatives of the profile at 0 and 1, the Lipschitz bound for Dζ, and Fermat's theorem for the vanishing of Dζ.

Notation. |·| is the Euclidean norm on ℝ^P, B_r := B_r(y) is the open ball, B̄_r := B̄_r(y) is the closed ball, and Dζ(z) := fderiv ℝ ζ z has operator norm ‖Dζ(z)‖.

1. Profile. Let p(s) := 1 − 3s² + 2s³ = (1 − s)²(1 + 2s), c(s) := max(0, min(s, 1)), h(s) := p(c(s)) and q(s) := p′(c(s)) = −6c(s) + 6c(s)². Then c(s) = 0 for s ≤ 0, c(s) = s for 0 ≤ s ≤ 1, c(s) = 1 for s ≥ 1, and 0 ≤ c ≤ 1. Since p(0) = 1 and p(1) = 0, h = 1 on (−∞, 0], h = p on [0, 1] and h = 0 on [1, ∞). Also p′(s) = −6s + 6s², so p′(0) = p′(1) = 0.

2. h′ = q everywhere.
(a) If s < 0, h ≡ 1 on the neighbourhood (−∞, 0) of s, so h′(s) = 0 = q(s).
(b) If 0 < s < 1, h = p on the neighbourhood (0, 1), so h′(s) = p′(s) = q(s).
(c) If s > 1, h ≡ 0 on (1, ∞), so h′(s) = 0 = q(s).
(d) At s = 0: h ≡ 1 on (−∞, 0], so h has derivative 0 within (−∞, 0] at 0. Also h = p on [0, 1), a neighbourhood of 0 within [0, ∞), so h has derivative p′(0) = 0 within [0, ∞) at 0. The two one-sided derivatives coincide and (−∞, 0] ∪ [0, ∞) = ℝ, so h′(0) = 0 = q(0).
(e) At s = 1, symmetrically: h = p on (0, 1] gives derivative p′(1) = 0 within (−∞, 1], and h ≡ 0 on [1, ∞) gives derivative 0 within [1, ∞). So h′(1) = 0 = q(1).

3. Properties of h. q = p′ ∘ c is continuous, so h is differentiable with a continuous derivative, i.e. h ∈ C¹(ℝ). Since 0 ≤ c ≤ 1 and 0 ≤ c(1 − c) ≤ 1/4, q = −6c(1 − c) satisfies −3/2 ≤ q ≤ 0. Hence h is nonincreasing (h′ ≤ 0) and, by the mean value theorem, (3/2)-Lipschitz. Further 0 ≤ h ≤ 1, because h = (1 − c)²(1 + 2c) ≥ 0 and 1 − h = c²(3 − 2c) ≥ 0. Finally h(s) = 1 for s ≤ 0 and h(s) = 0 for s ≥ 1.

4. Definition of ζ and its support. Put a(z) := (|z − y| − ρ)/δ and ζ := h ∘ a. By step 3, 0 ≤ ζ ≤ 1. If z ∈ B̄_ρ then a(z) ≤ 0, so ζ(z) = 1. If |z − y| ≥ ρ + δ then a(z) ≥ 1, so ζ(z) = 0. Hence support ζ ⊆ B_{ρ+δ} ⊆ B̄_{ρ+δ}. Since B̄_{ρ+δ} is closed, tsupport ζ = closure(support ζ) ⊆ B̄_{ρ+δ}. Since B̄_{ρ+δ} is compact and ζ vanishes outside it, ζ has compact support.

5. ζ is C¹. It suffices to show that ζ is C¹ at every z. If |z − y| < ρ, the open ball B_ρ is a neighbourhood of z on which ζ ≡ 1 (step 4), so ζ agrees with a constant near z and is C¹ at z. Otherwise |z − y| ≥ ρ > 0, so z − y ≠ 0. The Euclidean norm is C^∞ away from 0, so z′ ↦ |z′ − y| and a are C¹ at z, and ζ = h ∘ a is C¹ at z by the chain rule (h ∈ C¹ by step 3).

6. Gradient bound. For all z, w: |a(z) − a(w)| = ||z − y| − |w − y||/δ ≤ |z − w|/δ, so a is (1/δ)-Lipschitz. With step 3, ζ = h ∘ a is (3/2)·(1/δ) = 3/(2δ)-Lipschitz. The derivative of a Lipschitz function has operator norm at most the Lipschitz constant: |Dζ(z)w| = lim_{s→0} |ζ(z + sw) − ζ(z)|/|s| ≤ (3/(2δ))|w|. So ‖Dζ(z)‖ ≤ 3/(2δ) for every z.

7. Dζ vanishes off the open annulus. Let z ∉ B_{ρ+δ} ∖ B̄_ρ, i.e. |z − y| ≥ ρ + δ or |z − y| ≤ ρ. In the first case ζ(z) = 0 and ζ ≥ 0 everywhere. In the second case ζ(z) = 1 and ζ ≤ 1 everywhere (steps 3–4). So z is a local minimum or maximum of the differentiable function ζ, and Dζ(z) = 0 by Fermat's theorem. (Equivalently: where |z − y| ∉ {ρ, ρ + δ}, ζ is locally constant; where |z − y| ∈ {ρ, ρ + δ}, the chain rule gives Dζ(z) = δ^{−1}h′(a(z))·D|· − y|(z) with h′(0) = h′(1) = 0.)

8. Superlevel sets. Fix t ∈ (0, 1]. The set M := {s ∈ [0, 1] : h(s) ≥ t} is compact, being a closed subset of [0, 1] since h is continuous. It contains 0 because h(0) = 1 ≥ t. Let s_t := sup M; then s_t ∈ M and s_t ≥ 0. Moreover s_t < 1, since s_t = 1 would give t ≤ h(1) = 0.
Claim: for every real u, t ≤ h(u) ⇔ u ≤ s_t.
- If u ≤ s_t then h(u) ≥ h(s_t) ≥ t, because h is nonincreasing.
- Conversely, let t ≤ h(u) and suppose u > s_t. If u ≤ 1 then u ∈ [0, 1] (as u > s_t ≥ 0), so u ∈ M and u ≤ sup M = s_t, a contradiction. If u > 1 then h(u) = 0 < t, also a contradiction.
Now put r := ρ + δ s_t, so ρ ≤ r < ρ + δ. For every z, since δ > 0: t ≤ ζ(z) ⇔ a(z) ≤ s_t ⇔ |z − y| ≤ ρ + δ s_t = r ⇔ z ∈ B̄_r. Hence {z : t ≤ ζ(z)} = B̄_r.

9. Conclusion. The function ζ has all the required properties:
- it is C¹ (step 5);
- it has compact support and tsupport ζ ⊆ B̄_{ρ+δ} (step 4);
- 0 ≤ ζ ≤ 1 and ζ = 1 on B̄_ρ (step 4);
- ‖Dζ‖ ≤ 3/(2δ) (step 6);
- Dζ = 0 off B_{ρ+δ} ∖ B̄_ρ (step 7);
- its superlevel sets are the closed balls of step 8. ∎

Appendix (non-normative). A kernel-checked Lean proof of exactly this frozen statement was found during decomposition (workspace file GMT/Scratch/codim1_rdo_dg_cutoff_estimates_decomposition/Full.lean, git-ignored; it uses only the contract imports, compiles without warnings after `import GMT.Ch07.Submission` inside `namespace GMT.Ch07` with the contract opens, and `#print axioms` gives [propext, Classical.choice, Quot.sound]):

```lean
theorem Submission.codim1_rdo_dg_ce_radial_cutoff : ∀ (P : ℕ) (y : Euclid P) (ρ δ : ℝ), 0 < ρ → 0 < δ → ∃ ζ : Euclid P → ℝ, ContDiff ℝ 1 ζ ∧ HasCompactSupport ζ ∧ (∀ z, 0 ≤ ζ z ∧ ζ z ≤ 1) ∧ (∀ z ∈ closedBall y ρ, ζ z = 1) ∧ tsupport ζ ⊆ closedBall y (ρ + δ) ∧ (∀ z, ‖fderiv ℝ ζ z‖ ≤ 3 / (2 * δ)) ∧ (∀ z, z ∉ ball y (ρ + δ) \ closedBall y ρ → fderiv ℝ ζ z = 0) ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∃ r : ℝ, ρ ≤ r ∧ r < ρ + δ ∧ {z | t ≤ ζ z} = closedBall y r := by
  intro P y ρ δ hρ hδ
  have profile : ∃ h : ℝ → ℝ, ContDiff ℝ 1 h ∧ Antitone h ∧ (∀ s, 0 ≤ h s ∧ h s ≤ 1) ∧ (∀ s, s ≤ 0 → h s = 1) ∧ (∀ s, 1 ≤ s → h s = 0) ∧ LipschitzWith (3 / 2 : NNReal) h := by
    set p : ℝ → ℝ := fun s => 1 - 3 * s ^ 2 + 2 * s ^ 3 with hp_def
    set cl : ℝ → ℝ := fun s => max 0 (min s 1) with hcl_def
    set h : ℝ → ℝ := fun s => p (cl s) with hh_def
    set q : ℝ → ℝ := fun s => -6 * cl s + 6 * cl s ^ 2 with hq_def
    have hp : ∀ s, HasDerivAt p (-6 * s + 6 * s ^ 2) s := by
      intro s
      have h1 := ((hasDerivAt_pow 2 s).const_mul 3).const_sub 1
      have h2 := (hasDerivAt_pow 3 s).const_mul 2
      convert h1.add h2 using 1
      push_cast
      ring
    have hcl0 : ∀ s, s ≤ 0 → cl s = 0 := fun s hs => by
      simp only [hcl_def]; exact max_eq_left (min_le_of_left_le hs)
    have hcl1 : ∀ s, 1 ≤ s → cl s = 1 := fun s hs => by
      simp only [hcl_def]; rw [min_eq_right hs]; exact max_eq_right zero_le_one
    have hclmid : ∀ s, 0 ≤ s → s ≤ 1 → cl s = s := fun s h0 h1 => by
      simp only [hcl_def]; rw [min_eq_left h1]; exact max_eq_right h0
    have hcl01 : ∀ s, 0 ≤ cl s ∧ cl s ≤ 1 := fun s =>
      ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
    have hderiv : ∀ s, HasDerivAt h (q s) s := by
      intro s
      rcases lt_trichotomy s 0 with hs | hs | hs
      · have heq : h =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
          filter_upwards [Iio_mem_nhds hs] with u hu
          simp only [hh_def, hcl0 u (le_of_lt hu), hp_def]; norm_num
        have hq0 : q s = 0 := by simp only [hq_def, hcl0 s hs.le]; norm_num
        rw [hq0]; exact (hasDerivAt_const s (1 : ℝ)).congr_of_eventuallyEq heq
      · subst hs
        have hq0 : q 0 = 0 := by simp only [hq_def, hcl0 0 le_rfl]; norm_num
        rw [hq0]
        have hL : HasDerivWithinAt h 0 (Iic 0) 0 := by
          refine (hasDerivWithinAt_const (0 : ℝ) (Iic 0) (1 : ℝ)).congr (fun u hu => ?_) ?_
          · simp only [hh_def, hcl0 u hu, hp_def]; norm_num
          · simp only [hh_def, hcl0 0 le_rfl, hp_def]; norm_num
        have hR : HasDerivWithinAt h 0 (Ici 0) 0 := by
          have := (hp 0).hasDerivWithinAt (s := Ici 0)
          simp only [mul_zero, zero_pow two_ne_zero, add_zero] at this
          refine this.congr_of_eventuallyEq ?_ ?_
          · filter_upwards [inter_mem_nhdsWithin (Ici (0:ℝ)) (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))]
              with u hu
            simp only [hh_def, hclmid u hu.1 (le_of_lt hu.2)]
          · simp only [hh_def, hclmid 0 le_rfl zero_le_one]
        have := hL.union hR
        rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
      · rcases lt_trichotomy s 1 with hs1 | hs1 | hs1
        · have heq : h =ᶠ[𝓝 s] p := by
            filter_upwards [Ioo_mem_nhds hs hs1] with u hu
            simp only [hh_def, hclmid u hu.1.le hu.2.le]
          have hqs : q s = -6 * s + 6 * s ^ 2 := by simp only [hq_def, hclmid s hs.le hs1.le]
          rw [hqs]; exact (hp s).congr_of_eventuallyEq heq
        · subst hs1
          have hq0 : q 1 = 0 := by simp only [hq_def, hcl1 1 le_rfl]; norm_num
          rw [hq0]
          have hR : HasDerivWithinAt h 0 (Ici 1) 1 := by
            refine (hasDerivWithinAt_const (1 : ℝ) (Ici 1) (0 : ℝ)).congr (fun u hu => ?_) ?_
            · simp only [hh_def, hcl1 u hu, hp_def]; norm_num
            · simp only [hh_def, hcl1 1 le_rfl, hp_def]; norm_num
          have hL : HasDerivWithinAt h 0 (Iic 1) 1 := by
            have := (hp 1).hasDerivWithinAt (s := Iic 1)
            norm_num at this
            refine this.congr_of_eventuallyEq ?_ ?_
            · filter_upwards [inter_mem_nhdsWithin (Iic (1:ℝ)) (Ioi_mem_nhds (show (0:ℝ) < 1 by norm_num))]
                with u hu
              simp only [hh_def, hclmid u (le_of_lt hu.2) hu.1]
            · simp only [hh_def, hclmid 1 zero_le_one le_rfl]
          have := hL.union hR
          rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
        · have heq : h =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
            filter_upwards [Ioi_mem_nhds hs1] with u hu
            simp only [hh_def, hcl1 u (le_of_lt hu), hp_def]; norm_num
          have hq0 : q s = 0 := by simp only [hq_def, hcl1 s hs1.le]; norm_num
          rw [hq0]; exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq heq
    have hdiff : Differentiable ℝ h := fun s => (hderiv s).differentiableAt
    have hderiv_eq : deriv h = q := funext fun s => (hderiv s).deriv
    have hclcont : Continuous cl := by
      simp only [hcl_def]; fun_prop
    have hqcont : Continuous q := by
      simp only [hq_def]; fun_prop
    have hC1 : ContDiff ℝ 1 h := contDiff_one_iff_deriv.2 ⟨hdiff, hderiv_eq ▸ hqcont⟩
    have hq_nonpos : ∀ s, q s ≤ 0 := by
      intro s; obtain ⟨h0, h1⟩ := hcl01 s; simp only [hq_def]; nlinarith
    have hq_abs : ∀ s, |q s| ≤ 3 / 2 := by
      intro s; obtain ⟨h0, h1⟩ := hcl01 s
      rw [abs_of_nonpos (hq_nonpos s)]; simp only [hq_def]; nlinarith [sq_nonneg (cl s - 1 / 2)]
    refine ⟨h, hC1, antitone_of_deriv_nonpos hdiff (fun s => hderiv_eq ▸ hq_nonpos s), ?_, ?_, ?_, ?_⟩
    · intro s; obtain ⟨h0, h1⟩ := hcl01 s
      simp only [hh_def, hp_def]
      have e1 : 1 - 3 * cl s ^ 2 + 2 * cl s ^ 3 = (1 - cl s) ^ 2 * (1 + 2 * cl s) := by ring
      constructor
      · rw [e1]; exact mul_nonneg (sq_nonneg _) (by linarith)
      · nlinarith [mul_nonneg (sq_nonneg (cl s)) (by linarith : (0:ℝ) ≤ 3 - 2 * cl s)]
    · intro s hs; simp only [hh_def, hcl0 s hs, hp_def]; norm_num
    · intro s hs; simp only [hh_def, hcl1 s hs, hp_def]; norm_num
    · refine lipschitzWith_of_nnnorm_deriv_le hdiff fun s => ?_
      rw [hderiv_eq, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
      simpa using hq_abs s
  obtain ⟨h, hC1, hanti, h01, h0, h1, hlip⟩ := profile
  set a : Euclid P → ℝ := fun z => (‖z - y‖ - ρ) / δ with ha_def
  set ζ : Euclid P → ℝ := fun z => h (a z) with hζ_def
  have hζ1 : ∀ z ∈ closedBall y ρ, ζ z = 1 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    exact h0 _ (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
  have hζ0 : ∀ z, ρ + δ ≤ ‖z - y‖ → ζ z = 0 := by
    intro z hz
    refine h1 _ ?_
    rw [ha_def, le_div_iff₀ hδ]; linarith
  have hsupp : support ζ ⊆ ball y (ρ + δ) := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    by_contra hcon
    exact hz (hζ0 z (not_lt.1 hcon))
  have htsupp : tsupport ζ ⊆ closedBall y (ρ + δ) :=
    closure_minimal (hsupp.trans ball_subset_closedBall) isClosed_closedBall
  have hcomp : HasCompactSupport ζ :=
    HasCompactSupport.intro (isCompact_closedBall y (ρ + δ)) fun z hz =>
      image_eq_zero_of_notMem_tsupport (fun h' => hz (htsupp h'))
  -- C¹
  have hC1ζ : ContDiff ℝ 1 ζ := by
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hz : ‖z - y‖ < ρ
    · have heq : ζ =ᶠ[𝓝 z] fun _ => (1 : ℝ) := by
        have hmem : ball y ρ ∈ 𝓝 z := isOpen_ball.mem_nhds (by rw [mem_ball, dist_eq_norm]; exact hz)
        filter_upwards [hmem] with u hu
        exact hζ1 u (ball_subset_closedBall hu)
      exact contDiffAt_const.congr_of_eventuallyEq heq
    · have hzy : z - y ≠ 0 := by
        intro h0'; rw [h0', norm_zero] at hz; exact hz hρ
      have hn : ContDiffAt ℝ 1 (fun u : Euclid P => ‖u - y‖) z :=
        (contDiffAt_id.sub contDiffAt_const).norm ℝ hzy
      have ha' : ContDiffAt ℝ 1 a z := (hn.sub contDiffAt_const).div_const δ
      exact hC1.contDiffAt.comp z ha'
  -- Lipschitz bound on the derivative
  have hlipζ : LipschitzWith (Real.toNNReal (3 / (2 * δ))) ζ := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    have h1' := hlip.dist_le_mul (a z) (a w)
    have h2' : dist (a z) (a w) ≤ dist z w / δ := by
      rw [Real.dist_eq, ha_def]
      simp only
      rw [← sub_div, abs_div, abs_of_pos hδ, dist_eq_norm]
      gcongr
      calc |‖z - y‖ - ρ - (‖w - y‖ - ρ)| = |‖z - y‖ - ‖w - y‖| := by ring_nf
        _ ≤ ‖(z - y) - (w - y)‖ := abs_norm_sub_norm_le _ _
        _ = ‖z - w‖ := by abel_nf
    rw [Real.coe_toNNReal _ (by positivity)]
    calc dist (ζ z) (ζ w) ≤ (3 / 2 : NNReal) * dist (a z) (a w) := h1'
      _ ≤ (3 / 2 : ℝ) * (dist z w / δ) := by
          push_cast; gcongr
      _ = 3 / (2 * δ) * dist z w := by field_simp
  have hgrad : ∀ z, ‖fderiv ℝ ζ z‖ ≤ 3 / (2 * δ) := by
    intro z
    have := norm_fderiv_le_of_lipschitz ℝ hlipζ (x₀ := z)
    rwa [Real.coe_toNNReal _ (by positivity)] at this
  -- vanishing of the derivative off the open annulus
  have hζle : ∀ z, ζ z ≤ 1 := fun z => (h01 _).2
  have hζge : ∀ z, 0 ≤ ζ z := fun z => (h01 _).1
  have hzero : ∀ z, z ∉ ball y (ρ + δ) \ closedBall y ρ → fderiv ℝ ζ z = 0 := by
    intro z hz
    rw [Set.mem_sdiff, not_and_or, not_not] at hz
    rcases hz with hz | hz
    · rw [mem_ball, dist_eq_norm, not_lt] at hz
      have hmin : IsLocalMin ζ z := Eventually.of_forall fun u => by rw [hζ0 z hz]; exact hζge u
      exact hmin.fderiv_eq_zero
    · have hmax : IsLocalMax ζ z := Eventually.of_forall fun u => by rw [hζ1 z hz]; exact hζle u
      exact hmax.fderiv_eq_zero
  -- superlevel sets
  have hlevel : ∀ t : ℝ, 0 < t → t ≤ 1 → ∃ r : ℝ, ρ ≤ r ∧ r < ρ + δ ∧ {z | t ≤ ζ z} = closedBall y r := by
    intro t ht0 ht1
    set M : Set ℝ := Icc 0 1 ∩ h ⁻¹' Ici t with hM
    have hMc : IsCompact M :=
      isCompact_Icc.inter_right (isClosed_Ici.preimage hC1.continuous)
    have hM0 : (0 : ℝ) ∈ M := ⟨⟨le_rfl, zero_le_one⟩, by simp [h0 0 le_rfl, ht1]⟩
    set st := sSup M with hst
    have hstM : st ∈ M := hMc.sSup_mem ⟨0, hM0⟩
    have hst0 : 0 ≤ st := hstM.1.1
    have hst1 : st < 1 := by
      rcases hstM.1.2.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; have := hstM.2; rw [heq, mem_preimage, mem_Ici, h1 1 le_rfl] at this; linarith
    have hiff : ∀ u : ℝ, t ≤ h u ↔ u ≤ st := by
      intro u
      constructor
      · intro hu
        by_contra hcon
        push Not at hcon
        rcases le_or_gt u 1 with hu1 | hu1
        · have huM : u ∈ M := ⟨⟨hst0.trans hcon.le, hu1⟩, hu⟩
          exact absurd (le_csSup hMc.bddAbove huM) (not_le.2 hcon)
        · rw [h1 u hu1.le] at hu; linarith
      · intro hu
        exact le_trans hstM.2 (hanti hu)
    refine ⟨ρ + δ * st, by nlinarith, by nlinarith, ?_⟩
    ext z
    simp only [Set.mem_ofPred_eq, mem_closedBall, dist_eq_norm, hζ_def]
    rw [hiff, ha_def, div_le_iff₀ hδ]
    constructor <;> intro hh <;> linarith
  exact ⟨ζ, hC1ζ, hcomp, fun z => h01 _, hζ1, htsupp, hgrad, hzero, hlevel⟩
```

## Key steps

1. Profile h = p ∘ clamp_[0,1] with p(s) = 1 − 3s² + 2s³: one-sided derivatives agree at 0 and 1 (p′(0) = p′(1) = 0), so h′ = p′ ∘ clamp is continuous and h ∈ C¹.
2. h is nonincreasing, 0 ≤ h ≤ 1, h = 1 on (−∞,0], h = 0 on [1,∞), and h is (3/2)-Lipschitz since |h′| = 6c(1−c) ≤ 3/2.
3. ζ(z) = h((|z−y|−ρ)/δ) equals 1 on B̄_ρ and 0 off B_{ρ+δ}, so tsupport ζ ⊆ B̄_{ρ+δ} (compact).
4. ζ is C¹: it is locally constant on B_ρ and a C¹ composite (the norm is smooth away from 0) wherever z ≠ y.
5. ζ is 3/(2δ)-Lipschitz, so ‖Dζ‖ ≤ 3/(2δ); Dζ = 0 off the open annulus by Fermat at the extrema ζ = 0 and ζ = 1.
6. {ζ ≥ t} = B̄_{ρ+δ s_t} with s_t = max{s ∈ [0,1] : h(s) ≥ t} < 1, using that h is nonincreasing and h = 0 on [1,∞).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `python3 scans of dag.json: de_giorgi-a1 children (status, lean_name, depth); accepted nodes whose title/statement matches cut-off|bump|smoothstep|layer|Fubini|integration by parts|divergence; statements of dorag_th_radial_cutoff, doragm_sab_cutoff_profile, dorag_ha_mv_radial_potential, dsmc_em_cutoff_tendsto_ball, doragm_sab_cutoff_mass_sandwich, doragm_sab_annulus_increment_sandwich, dorag_ha_lsc_ibp_c1_ball, regcomp_smooth_cutoff_product; collision check of the five codim1_rdo_dg_ce_* names (974 nodes: all free)`
- `grep -rn codim1_rdo_dg_ce /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt (no match)`
- `rg -n 'theorem integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable|theorem integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable|lemma trace_smulRight|theorem trace_eq_matrix_trace |theorem addHaar_ball |theorem volume_ball|theorem contDiffAt_norm|theorem norm_fderiv_le_of_lipschitz|theorem fderiv_smul_const|theorem HasCompactSupport.smul_right|theorem integral_integral_swap|theorem lintegral_eq_lintegral_meas_le|theorem inner_neg_neg|theorem finrank_euclideanSpace_fin|theorem addHaar_sphere|trace_eq_sum_inner' <snapshot>/mathlib/Mathlib`
- `rg -n for contDiff_one_iff_deriv, lipschitzWith_of_nnnorm_deriv_le, IsLocalMax.fderiv_eq_zero, IsLocalMin.fderiv_eq_zero, support_fderiv_subset, Continuous.integrable_of_hasCompactSupport, integral_inner, antitone_of_deriv_nonpos, mem_nhdsGT_iff_exists_Ioo_subset, def basisFun, Integrable.integral_prod_right, setIntegral_eq_integral_of_forall_compl_eq_zero, integral_add_compl, HasDerivWithinAt.union, norm_integral_le_of_norm_le, integral_indicator_const, integrableOn_of_bounded, IsCompact.sSup_mem, HasCompactSupport.intro, LipschitzWith.of_dist_le_mul, mul_le_mul_right' in <snapshot>/mathlib/Mathlib`
- `sed -n 560,700p book/chapter-03.txt; grep -n of the numbered steps (1)-(6), '4.3 Theorem' and 'Proof: By 1.6' in book/chapter-03.txt`
- `git show 46877ce9:GMT/Ch07/Submission.lean; git show 296e19be:GMT/Ch07/Submission.lean (accepted IBP proofs keep the contract imports; LipschitzWith.integral_lineDeriv_mul_eq usage)`
- `lake env lean -DautoImplicit=false /tmp/ce-split-check/Types.lean (five child types elaborate; sorry warnings only)`
- `lake env lean -DautoImplicit=false /tmp/ce-split-check/Assembly.lean (frozen parent type proved from child stubs; type byte-identical to handoff lean_statement; #print axioms = propext, sorryAx, Classical.choice, Quot.sound)`
- `lake env lean -DautoImplicit=false GMT/Scratch/codim1_rdo_dg_cutoff_estimates_decomposition/Full.lean and /tmp/ce-split-check/FromPayload.lean (all five children proved and the parent proved from them; no warnings; #print axioms = [propext, Classical.choice, Quot.sound] for all six)`
- `sed -n 1380,1440p and grep -n _existing_lean_name_problem /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py; cat swarm-project.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-3ce4c763f6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-3ce4c763f6/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-3ce4c763f6/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/codim1_rdo_dg_cutoff_estimates_decomposition/Full.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/codim1_rdo_dg_cutoff_estimates_decomposition/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/codim1_rdo_dg_cutoff_estimates_decomposition/child_statements.json`
- `/tmp/ce-split-check/Types.lean`
- `/tmp/ce-split-check/Assembly.lean`
- `/tmp/ce-split-check/FromPayload.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`

Pins. The snapshot manifest records project b4d606db and Mathlib 25730c7c. The workspace HEAD is b4d606db, and Contract.lean and Submission.lean are byte-identical. Library. No local declaration has the exact types needed for the annulus cut-off, the signed layer cake, ∫ div φ = 0 or the quantitative normal-average bound. The closest accepted nodes differ: dorag_th_radial_cutoff, doragm_sab_cutoff_profile, dorag_ha_mv_radial_potential, dorag_ha_lsc_ibp_c1_ball. So all five children are new, with fresh codim1_rdo_dg_ce_* names that are free among 974 DAG nodes and in SimonGMT. Snapshot Mathlib supplies every tool used: LinearMap.trace_smulRight, LinearMap.trace_eq_sum_inner, fderiv_smul_const, contDiffAt_norm, norm_fderiv_le_of_lipschitz, lipschitzWith_of_nnnorm_deriv_le, IsLocalMax/IsLocalMin.fderiv_eq_zero, integral_integral_swap, Integrable.integral_prod_right, Measure.addHaar_ball, finrank_euclideanSpace_fin, Measure.integrableOn_of_bounded, and LipschitzWith.integral_lineDeriv_mul_eq (Rademacher, imported). integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (LineDeriv/IntegrationByParts.lean) and integral_inner (L2Space.lean) exist in the snapshot but are not imported by the contract; accepted submissions 46877ce9 and 296e19be keep the contract imports. Book. Simon Ch. 3, 4.3 steps (1) and (3)–(6) at chapter-03.txt lines 604–652 match the parent's cited source. Lean. The five child types elaborate. The parent's frozen type is proved from the children, with a byte-identical type. Complete proofs of all five children and of the parent build with axioms [propext, Classical.choice, Quot.sound]; they are saved in GMT/Scratch/codim1_rdo_dg_cutoff_estimates_decomposition and repeated as appendices. Runtime. The node is at depth 5 < max_depth 6, so the children (depth 6) are leaves, and the name-collision rule is satisfied.
