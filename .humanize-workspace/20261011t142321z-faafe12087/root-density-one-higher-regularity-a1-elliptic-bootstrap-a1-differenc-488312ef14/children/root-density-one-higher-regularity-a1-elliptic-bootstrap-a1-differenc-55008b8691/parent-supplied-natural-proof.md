# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.difference_quotient_limit-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.difference_quotient_limit-a1.c1holder_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4-7 of the parent proof of dohr_eb_difference_quotient_limit:
- the uniform Cauchy property of the derivatives, from the interpolation inequality;
- completeness of L(R^n, R^l);
- inheritance of the bounds by the limit;
- the theorem on uniform limits of derivatives.
It is stated for an abstract family F_i along a filter l ≠ ⊥ that converges uniformly on compact subsets of B. The parent applies it with i = d, l = 𝓝[≠] 0, F_d = g_d and G = D_e f.

Sibling lemma used: Submission.dohr_eb_dql_interpolation_fderiv_bound (key interpolation). Suppose 0 < t ≤ r, alpha > 0, L ≥ 0, h is differentiable at every point of B̄_{2r}(x), ‖Dh(y) - Dh(y')‖ ≤ L‖y - y'‖^alpha for y, y' ∈ B̄_{2r}(x), and ‖h(y)‖ ≤ S for y ∈ B̄_{2r}(x). Then ‖Dh(y)‖ ≤ 2S/t + L t^alpha for every y ∈ B̄_r(x).

Notation:
- B := ball(x0, rho), which is open and convex; B̄_s(z) := closedBall z s; DF_i := fderiv ℝ (F i).
- E := the set of i such that F_i is differentiable at every x ∈ B, ‖DF_i(x)‖ ≤ M for x ∈ B, and ‖DF_i(x) - DF_i(y)‖ ≤ M‖x - y‖^alpha for x, y ∈ B. E ∈ l, as the intersection of the three eventual hypotheses.
- V : R^n -> L(R^n, R^l) is defined by V(y) := limUnder l (fun i => DF_i(y)). This is a chosen limit, and it is the limit whenever one exists.

1. (Radii; sign of M.) For x ∈ B put r_x := (rho - dist(x, x0))/4 > 0. If dist(z, x) ≤ 2r_x, then dist(z, x0) ≤ dist(z, x) + dist(x, x0) ≤ (rho - dist(x, x0))/2 + dist(x, x0) < rho; so B̄_{2r_x}(x) ⊆ B. If x ∈ B then M ≥ 0: since l ≠ ⊥, E is non-empty, and for i ∈ E we have M ≥ ‖DF_i(x)‖ ≥ 0.

2. (Uniform Cauchy property.) Fix x ∈ B and r > 0 with B̄_{2r}(x) ⊆ B; by step 1, M ≥ 0. Let η > 0.
   (a) Since t^alpha -> 0 as t -> 0+ (alpha > 0), there is t with 0 < t ≤ r and 2M t^alpha < η/2. The set of such t belongs to 𝓝[>] 0, which is ≠ ⊥.
   (b) K := B̄_{2r}(x) is compact and K ⊆ B, so by hypothesis F_i -> G uniformly on K. Hence the set P of i ∈ E with ‖G(y) - F_i(y)‖ < ηt/8 for all y ∈ K belongs to l, and the pairs (i, j) ∈ P × P form a set of l ×ˢ l.
   (c) Fix such (i, j) and put h := F_i - F_j. Then:
      - h is differentiable at every point of K ⊆ B, with Dh(y) = DF_i(y) - DF_j(y) there (fderiv_sub);
      - for y, y' ∈ K: ‖Dh(y) - Dh(y')‖ = ‖(DF_i(y) - DF_i(y')) - (DF_j(y) - DF_j(y'))‖ ≤ M‖y - y'‖^alpha + M‖y - y'‖^alpha = 2M‖y - y'‖^alpha;
      - for y ∈ K: ‖h(y)‖ = ‖(G(y) - F_j(y)) - (G(y) - F_i(y))‖ ≤ ηt/8 + ηt/8 = ηt/4.
   (d) The interpolation lemma with L := 2M ≥ 0 and S := ηt/4 gives, for every y ∈ B̄_r(x),
      ‖DF_i(y) - DF_j(y)‖ ≤ 2(ηt/4)/t + 2M t^alpha = η/2 + 2M t^alpha < η.
   (e) As η > 0 was arbitrary, the family (DF_i) is uniformly Cauchy on B̄_r(x) along l (UniformCauchySeqOn; unfold it with Metric.mem_uniformity_dist and combine the eventualities with Filter.Eventually.prod_mk).

3. (Uniform limit.) L(R^n, R^l) is complete.
   (a) For y ∈ B̄_r(x), the image of l under i ↦ DF_i(y) is a Cauchy filter (UniformCauchySeqOn.cauchy_map, l ≠ ⊥). Hence it converges (cauchy_map_iff_exists_tendsto), and so DF_i(y) -> V(y) (tendsto_nhds_limUnder).
   (b) A uniformly Cauchy family that converges pointwise converges uniformly to its pointwise limit (UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto). So DF_i -> V uniformly on B̄_r(x) along l.
   (c) Apply this at each y ∈ B with r = r_y from step 1 (note y ∈ B̄_{r_y}(y)): DF_i(y) -> V(y) for every y ∈ B.

4. (Bounds for V and continuity.) Let y, y' ∈ B.
   (a) Eventually in l, ‖DF_i(y)‖ ≤ M and ‖DF_i(y) - DF_i(y')‖ ≤ M‖y - y'‖^alpha. By step 3 and continuity of the norm, DF_i(y) -> V(y) and DF_i(y) - DF_i(y') -> V(y) - V(y').
   (b) Since l ≠ ⊥, closed inequalities pass to the limit (le_of_tendsto): ‖V(y)‖ ≤ M and ‖V(y) - V(y')‖ ≤ M‖y - y'‖^alpha.
   (c) Hence V is continuous on B. For y, z ∈ B, 0 ≤ ‖V(z) - V(y)‖ ≤ M‖z - y‖^alpha, and M‖z - y‖^alpha -> M·0^alpha = 0 as z -> y (alpha > 0). So ‖V(z) - V(y)‖ -> 0 as z -> y within B (squeeze).

5. (Differentiability.) Fix x ∈ B and r := r_x. Apply the uniform-limit theorem for derivatives (hasFDerivAt_of_tendstoUniformlyOnFilter, filter l ≠ ⊥) to F_i, DF_i, G and V at x. Its three hypotheses hold:
   (a) DF_i -> V uniformly on B̄_r(x) (step 3). This set is a neighbourhood of x, so the convergence is uniform on the filter 𝓝 x (tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, TendstoUniformlyOnFilter.mono_right).
   (b) For l ×ˢ 𝓝 x-eventually all (i, y), namely i ∈ E and y ∈ B (B is open and contains x), F_i has Fréchet derivative DF_i(y) at y (DifferentiableAt.hasFDerivAt).
   (c) For every y in the neighbourhood B of x, F_i(y) -> G(y) along l, because F_i -> G uniformly on the compact set {y} ⊆ B (TendstoUniformlyOn.tendsto_at).
   Therefore G has Fréchet derivative V(x) at x; in particular G is differentiable at x and fderiv ℝ G x = V(x). This holds for every x ∈ B.

6. (Conclusion.) G is differentiable at every point of the open set B, and fderiv ℝ G = V on B, which is continuous on B by step 4. Hence G is C^1 on B, via contDiffOn_succ_iff_fderiv_of_isOpen with 1 = 0 + 1:
   - G is differentiable on B;
   - the analyticity clause is vacuous since 0 ≠ ω;
   - ContDiffOn ℝ 0 (fderiv ℝ G) B is equivalent to ContinuousOn (contDiffOn_zero), which follows from the continuity of V by ContinuousOn.congr.
   Finally, for x, y ∈ B, ‖fderiv ℝ G x‖ = ‖V(x)‖ ≤ M and ‖fderiv ℝ G x - fderiv ℝ G y‖ = ‖V(x) - V(y)‖ ≤ M‖x - y‖^alpha by step 4. QED

Appendix (informative; checked Lean realization). The following proof of exactly the frozen type compiled without errors or warnings at the pinned toolchain (Lean 4.35.0-rc3, Mathlib 25730c7c). It was placed inside namespace GMT.Ch05 / namespace Submission with the contract's opens, after the sibling dohr_eb_dql_interpolation_fderiv_bound. #print axioms reports propext, Classical.choice, Quot.sound.

theorem dohr_eb_dql_c1Holder_of_tendstoUniformlyOn : ∀ (n ℓ : ℕ) (ι : Type) (l : Filter ι), l.NeBot → ∀ (F : ι → Rn n → Rn ℓ) (G : Rn n → Rn ℓ) (x₀ : Rn n) (ρ α M : ℝ), 0 < α → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, DifferentiableAt ℝ (F i) x) → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, ‖fderiv ℝ (F i) x‖ ≤ M) → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖fderiv ℝ (F i) x - fderiv ℝ (F i) y‖ ≤ M * ‖x - y‖ ^ α) → (∀ K : Set (Rn n), IsCompact K → K ⊆ ball x₀ ρ → TendstoUniformlyOn F G l K) → ContDiffOn ℝ 1 G (ball x₀ ρ) ∧ (∀ x ∈ ball x₀ ρ, ‖fderiv ℝ G x‖ ≤ M) ∧ ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ M * ‖x - y‖ ^ α := by
  intro n ℓ ι l hl F G x₀ ρ α M hα hD hB hH hU
  have := hl
  have hE := hD.and (hB.and hH)
  set V : Rn n → (Rn n →L[ℝ] Rn ℓ) := fun y => limUnder l (fun i => fderiv ℝ (F i) y) with hVdef
  have hrad : ∀ x ∈ ball x₀ ρ, ∃ r > 0, closedBall x (2 * r) ⊆ ball x₀ ρ := by
    intro x hx
    rw [mem_ball] at hx
    refine ⟨(ρ - dist x x₀) / 4, by linarith, fun z hz => ?_⟩
    rw [mem_closedBall] at hz
    rw [mem_ball]
    calc dist z x₀ ≤ dist z x + dist x x₀ := dist_triangle _ _ _
      _ < ρ := by linarith
  have hM : ∀ x ∈ ball x₀ ρ, 0 ≤ M := by
    intro x hx
    obtain ⟨i, hi⟩ := hB.exists
    exact (norm_nonneg _).trans (hi x hx)
  have hconv : ∀ x ∈ ball x₀ ρ, ∀ r > 0, closedBall x (2 * r) ⊆ ball x₀ ρ →
      TendstoUniformlyOn (fun i => fderiv ℝ (F i)) V l (closedBall x r) := by
    intro x hx r hr hsub
    have hM0 := hM x hx
    have hUC : UniformCauchySeqOn (fun i => fderiv ℝ (F i)) l (closedBall x r) := by
      intro u hu
      obtain ⟨η, hη, hηu⟩ := Metric.mem_uniformity_dist.1 hu
      have ht_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 2 * M * t ^ α < η / 2 := by
        have hc : Tendsto (fun t : ℝ => 2 * M * t ^ α) (𝓝 0) (𝓝 (2 * M * (0 : ℝ) ^ α)) :=
          ((continuousAt_id.rpow_const (Or.inr hα.le)).tendsto).const_mul _
        rw [Real.zero_rpow hα.ne', mul_zero] at hc
        exact nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds (by linarith)))
      have hIoc : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioc 0 r := Ioc_mem_nhdsGT hr
      obtain ⟨t, ht1, ht2⟩ := (ht_ev.and hIoc).exists
      have htpos : 0 < t := ht2.1
      have htr : t ≤ r := ht2.2
      have hK : closedBall x (2 * r) ⊆ ball x₀ ρ := hsub
      have hTU := hU (closedBall x (2 * r)) (isCompact_closedBall x _) hK
      rw [Metric.tendstoUniformlyOn_iff] at hTU
      have hP := hE.and (hTU (η * t / 8) (by positivity))
      filter_upwards [hP.prod_mk hP] with ij hij y hy
      obtain ⟨⟨hDi, hBi, hHi⟩, hGi⟩ := hij.1
      obtain ⟨⟨hDj, hBj, hHj⟩, hGj⟩ := hij.2
      apply hηu
      rw [dist_eq_norm]
      have hyB : y ∈ closedBall x (2 * r) := closedBall_subset_closedBall (by linarith) hy
      set h : Rn n → Rn ℓ := fun z => F ij.1 z - F ij.2 z with hh
      have hdh : ∀ z ∈ closedBall x (2 * r), DifferentiableAt ℝ h z := fun z hz =>
        (hDi z (hK hz)).sub (hDj z (hK hz))
      have hfd : ∀ z ∈ closedBall x (2 * r),
          fderiv ℝ h z = fderiv ℝ (F ij.1) z - fderiv ℝ (F ij.2) z := fun z hz =>
        fderiv_sub (hDi z (hK hz)) (hDj z (hK hz))
      have hbd := dohr_eb_dql_interpolation_fderiv_bound n ℓ h x r t α (2 * M) (η * t / 4)
        htpos htr hα (by linarith) hdh
        (fun z hz z' hz' => by
          rw [hfd z hz, hfd z' hz']
          calc ‖fderiv ℝ (F ij.1) z - fderiv ℝ (F ij.2) z -
                (fderiv ℝ (F ij.1) z' - fderiv ℝ (F ij.2) z')‖
              = ‖(fderiv ℝ (F ij.1) z - fderiv ℝ (F ij.1) z') -
                  (fderiv ℝ (F ij.2) z - fderiv ℝ (F ij.2) z')‖ := by congr 1; abel
            _ ≤ ‖fderiv ℝ (F ij.1) z - fderiv ℝ (F ij.1) z'‖ +
                  ‖fderiv ℝ (F ij.2) z - fderiv ℝ (F ij.2) z'‖ := norm_sub_le _ _
            _ ≤ M * ‖z - z'‖ ^ α + M * ‖z - z'‖ ^ α :=
                add_le_add (hHi z (hK hz) z' (hK hz')) (hHj z (hK hz) z' (hK hz'))
            _ = 2 * M * ‖z - z'‖ ^ α := by ring)
        (fun z hz => by
          have h1 := hGi z hz
          have h2 := hGj z hz
          rw [dist_eq_norm] at h1 h2
          calc ‖h z‖ = ‖(G z - F ij.2 z) - (G z - F ij.1 z)‖ := by
                show ‖F ij.1 z - F ij.2 z‖ = _; congr 1; abel
            _ ≤ ‖G z - F ij.2 z‖ + ‖G z - F ij.1 z‖ := norm_sub_le _ _
            _ ≤ η * t / 4 := by linarith)
        y hy
      rw [hfd y hyB] at hbd
      calc ‖fderiv ℝ (F ij.1) y - fderiv ℝ (F ij.2) y‖ ≤ 2 * (η * t / 4) / t + 2 * M * t ^ α := hbd
        _ = η / 2 + 2 * M * t ^ α := by field_simp; ring
        _ < η := by linarith
    refine hUC.tendstoUniformlyOn_of_tendsto (fun y hy => ?_)
    have hc := hUC.cauchy_map hy
    obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.1 hc
    exact tendsto_nhds_limUnder ⟨L, hL⟩
  have hpt : ∀ y ∈ ball x₀ ρ, Tendsto (fun i => fderiv ℝ (F i) y) l (𝓝 (V y)) := by
    intro y hy
    obtain ⟨r, hr, hsub⟩ := hrad y hy
    exact (hconv y hy r hr hsub).tendsto_at (mem_closedBall_self hr.le)
  have hG : ∀ x ∈ ball x₀ ρ, HasFDerivAt G (V x) x := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := hrad x hx
    have hT := hconv x hx r hr hsub
    refine hasFDerivAt_of_tendstoUniformlyOnFilter (l := l) (f := F) (f' := fun i => fderiv ℝ (F i)) ?_ ?_ ?_
    · exact (tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.1 hT).mono_right
        (le_principal_iff.2 (closedBall_mem_nhds x hr))
    · filter_upwards [hD.prod_mk (isOpen_ball.mem_nhds hx)] with p hp
      exact (hp.1 p.2 hp.2).hasFDerivAt
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact (hU {y} isCompact_singleton (singleton_subset_iff.2 hy)).tendsto_at rfl
  have hfG : ∀ x ∈ ball x₀ ρ, fderiv ℝ G x = V x := fun x hx => (hG x hx).fderiv
  have hVb : ∀ x ∈ ball x₀ ρ, ‖V x‖ ≤ M := fun x hx =>
    le_of_tendsto (hpt x hx).norm (hB.mono fun i hi => hi x hx)
  have hVh : ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖V x - V y‖ ≤ M * ‖x - y‖ ^ α := fun x hx y hy =>
    le_of_tendsto ((hpt x hx).sub (hpt y hy)).norm (hH.mono fun i hi => hi x hx y hy)
  have hVc : ContinuousOn V (ball x₀ ρ) := by
    intro y hy
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun z => M * ‖z - y‖ ^ α) (𝓝 y) (𝓝 (M * ‖y - y‖ ^ α)) :=
      (((continuous_id.sub continuous_const).norm.continuousAt).rpow_const
        (Or.inr hα.le)).tendsto.const_mul M
    rw [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) ?_
      (hlim.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hVh z hz y hy
  refine ⟨?_, fun x hx => by rw [hfG x hx]; exact hVb x hx, fun x hx y hy => by
    rw [hfG x hx, hfG y hy]; exact hVh x hx y hy⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
  refine ⟨fun x hx => (hG x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hVc.congr hfG

## Key steps

1. each x in B has a radius r with closedBall(x, 2r) ⊆ B, and M ≥ 0 because the good set of indices is nonempty
2. the interpolation lemma applied to F_i - F_j (Hoelder constant 2M, sup bound eta t/4 from uniform convergence on closedBall(x, 2r)) makes DF_i uniformly Cauchy on closedBall(x, r)
3. completeness of L(R^n,R^l): DF_i -> V := limUnder uniformly on closedBall(x, r), hence pointwise on B
4. the limit V inherits the bound M and the Hoelder constant M, so V is continuous on B
5. hasFDerivAt_of_tendstoUniformlyOnFilter gives fderiv G = V on B; then ContDiffOn 1 follows from contDiffOn_succ_iff_fderiv_of_isOpen and contDiffOn_zero

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean; cmp GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Contract.lean; git rev-parse HEAD`
- `grep -rn 'theorem hasFDerivAt_of_tendstoUniformlyOnFilter|theorem hasFDerivAt_of_tendstoLocallyUniformlyOn|theorem hasFDerivAt_of_tendstoUniformlyOn ' <snapshot>/mathlib/Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean (sed -n 290,440p)`
- `grep -rnE '(theorem|lemma|instance)[^:]*(exists_cthickening_subset_open|IsCompact.cthickening|closedBall_subset_cthickening|norm_image_sub_le_of_norm_hasFDerivWithin_le\'|norm_image_sub_le_of_norm_fderiv_le|tendstoUniformlyOn_iff|uniformContinuousOn_iff|contDiffOn_succ_iff_fderiv_of_isOpen|continuousOn_fderiv_of_isOpen|contDiffOn_zero|opNorm_le_bound|hasFDerivAt_comp_add_right|UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto|UniformCauchySeqOn.cauchy_map|cauchy_map_iff_exists_tendsto|tendsto_nhds_limUnder|Eventually.prod_mk|uniformCauchySeqOn_iff|IsCompact.uniformContinuousOn_of_continuous|le_of_tendsto)' <snapshot>/mathlib/Mathlib --include=*.lean`
- `grep -rn 'NeBot (𝓝\[≠\]' <snapshot>/mathlib/Mathlib --include=*.lean`
- `rg -l -i 'interpolation inequalit|Landau.Kolmogorov|kolmogorov inequality' <snapshot>/mathlib/Mathlib/Analysis; rg -l -i 'difference quotient' <snapshot>/mathlib/Mathlib`
- `rg -l -i 'interpolation|difference quotient|TendstoUniformlyOn' lake-packages-25730c7c/simongmt --glob '*.lean'; rg -l -i 'difference quotient|interpolation' <snapshot>/project/GMT`
- `python3 scan of dag.json lean_name values for dql/interpolation/diffQuot/c1Holder and of lean_statement values containing TendstoUniformlyOn/TendstoLocallyUniformlyOn/UniformCauchy/𝓝[≠] or fderiv with ^ α; grep -rl dohr_eb_dql nodes dag.json <snapshot>/project <snapshot>/mathlib/Mathlib`
- `python3 -I: contract_scope(Contract.lean, 'GMT.Ch05.main_theorem') from verifier/gmt-compare.py (comparator replay scope)`
- `lake build GMT.Ch05.Submission in scratch copy /tmp/dql-decomp-WcgsEv/proj (Lean 4.35.0-rc3, shared lake-packages-25730c7c)`
- `lake env lean Checks/Assembly.lean (3 child types as axioms in namespace Submission, frozen parent proof, comparator-style exact Submission.X targets, #print axioms)`
- `lake env lean Checks/ChildA.lean; lake env lean Checks/ChildBC.lean; lake env lean Checks/Full.lean (children proved + parent; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/Filter/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/DenselyOrdered.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare`

PIN AND CONTRACT. The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd, which equals the workspace HEAD, and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Contract.lean and Submission.lean are byte-identical to the snapshot contract.

NO EXISTING LEMMA COVERS THE CHILDREN.
- Nothing at the pin gives an interpolation inequality: no interpolation/Landau-Kolmogorov match in Mathlib/Analysis.
- 'difference quotient' matches only Analysis/Calculus/UniformLimitsDeriv.lean. Its private difference_quotients_converge_uniformly belongs to the uniform-limit-of-derivatives theorem, not to difference quotients of a fixed C^1 map along a direction.
- No lemma states that C^{1,alpha} bounds are closed under locally uniform limits.
- The simongmt matches (Chapter01/Lusin.lean Egorov uniformization; Chapter06 current topologies) and the project GMT tree contain nothing relevant.

API THE CHILD PROOFS USE (lines at the pin):
- hasFDerivAt_of_tendstoUniformlyOnFilter [NeBot l] (UniformLimitsDeriv.lean:308; it allows eventually-differentiable families via l ×ˢ 𝓝 x)
- Convex.norm_image_sub_le_of_norm_fderiv_le' (MeanValue.lean:549)
- IsCompact.exists_cthickening_subset_open (Thickening.lean:426), IsCompact.cthickening (:283), closedBall_subset_cthickening (:537)
- IsCompact.uniformContinuousOn_of_continuous (HeineCantor.lean:49)
- contDiffOn_succ_iff_fderiv_of_isOpen (ContDiff/Defs.lean:891), ContDiffOn.continuousOn_fderiv_of_isOpen (:916), contDiffOn_zero (:618)
- hasFDerivAt_comp_add_right (FDeriv/Add.lean:847)
- UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto (UniformConvergence.lean:499), UniformCauchySeqOn.cauchy_map (:564)
- cauchy_map_iff_exists_tendsto (UniformSpace/Cauchy.lean:420), tendsto_nhds_limUnder (Topology/Basic.lean:245)
- Metric.tendstoUniformlyOn_iff (Pseudo/Basic.lean:142), Metric.uniformContinuousOn_iff (Pseudo/Defs.lean:759)
- Filter.Eventually.prod_mk (Order/Filter/Prod.lean:155), ContinuousLinearMap.opNorm_le_bound (Normed/Operator/Basic.lean:196), le_of_tendsto (Order/OrderClosed.lean:133)
- NeBot (𝓝[≠] x) instance (DenselyOrdered.lean:248)
Metric.uniformCauchySeqOn_iff exists only for atTop, so the child proof works from the definition of UniformCauchySeqOn. ContDiffOn.differentiableOn takes 1 ≠ 0.

NAMES. No dql/interpolation/diffQuot/c1Holder lean_name exists in dag.json (431 unique names). 'dohr_eb_dql' occurs nowhere in dag.json, the node directories or the snapshot, so the three proposed names are unreserved.

LEAN CHECKS (scratch build, replayed comparator scope).
- All three child types elaborate, and comparator-style targets close by exact Submission.X.
- With the children as axioms, the frozen parent type is proved; #print axioms lists propext, Classical.choice, Quot.sound, the c1Holder child and the diffQuot child.
- Each child type was also proved in Lean (C using B). The complete chain prints only propext, Classical.choice and Quot.sound, with no errors or warnings.
