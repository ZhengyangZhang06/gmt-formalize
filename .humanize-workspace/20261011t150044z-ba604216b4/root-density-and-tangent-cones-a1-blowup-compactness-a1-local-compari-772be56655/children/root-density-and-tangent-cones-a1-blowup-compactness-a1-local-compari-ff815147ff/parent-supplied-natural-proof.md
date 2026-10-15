# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.density_gradient_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2(a) of the parent proof (its first three bullets): density points admit sequences y_k ∈ Y approaching y from every direction, and dividing |F(y_k) − F(y)| ≤ L|ψ(y_k) − ψ(y)| by |y_k − y| gives the bound. The truncated cone of the parent proof is replaced by a ball inside it, which gives the same scaling argument with ball measures only.
Notation: B := Dψ(y), ℓ := DF(y); |·| Euclidean norm; B_r(z) open ball, B̄_r(z) closed ball; ω := L^d(B_1(0)).

1. (Reduction to unit vectors.) If e = 0 both sides are 0. If e ≠ 0 put u := e/|e|; if |ℓu| ≤ L|Bu| then |ℓe| = |e||ℓu| ≤ L|e||Bu| = L|Be| by linearity. So it suffices to prove |ℓu| ≤ L|Bu| for every u ∈ ℝ^d with |u| = 1. Fix such u; in particular d ≥ 1, so 0 < ω < ∞ and r ↦ r^d is positive for r > 0.
2. (An elementary inequality.) For a, b ∈ ℝ^d ∖ {0}: |a/|a| − b/|b|| ≤ 2|a − b|/|b|. Indeed a/|a| − b/|b| = (a − b)/|b| + a·(|b| − |a|)/(|a||b|), and ||b| − |a|| ≤ |a − b|.
3. (Directions claim.) For every δ ∈ (0, 1) there is z ∈ Y with 0 < |z − y| < δ and |(z − y)/|z − y| − u| < δ.
 Proof by contradiction: let δ ∈ (0, 1) be such that no such z exists. Put ρ := min(δ/8, 1/4) > 0. For 0 < r < δ let W_r := B_{rρ}(y + (r/2)u).
 (a) W_r ⊆ B̄_r(y) and W_r ∩ Y = ∅. Let w ∈ W_r and v := (w − y)/r; then |v − u/2| < ρ, so |v| ≥ 1/2 − ρ ≥ 1/4 > 0 and |v| ≤ 1/2 + ρ ≤ 3/4. Hence 0 < |w − y| = r|v| ≤ 3r/4 < δ and w ∈ B̄_r(y). By step 2 with a := v, b := u/2 (|b| = 1/2, b/|b| = u) and (w − y)/|w − y| = v/|v|: |(w − y)/|w − y| − u| ≤ 4|v − u/2| < 4ρ ≤ δ/2 < δ. So w would be a point z as in the claim unless w ∉ Y; by the contradiction hypothesis w ∉ Y.
 (b) By translation invariance and scaling of Lebesgue measure (Measure.addHaar_ball_of_pos, Measure.addHaar_closedBall, finrank ℝ^d = d): L^d(W_r) = (rρ)^d ω and L^d(B̄_r(y)) = r^d ω, both finite and positive. W_r is open (measurable), W_r ⊆ B̄_r(y), and by (a) Y ∩ B̄_r(y) ⊆ B̄_r(y) ∖ W_r. By monotonicity of the outer measure and measure_diff,
 L^d(Y ∩ B̄_r(y)) ≤ L^d(B̄_r(y)) − L^d(W_r) = (1 − ρ^d)·L^d(B̄_r(y)).
 (c) Thus L^d(Y ∩ B̄_r(y))/L^d(B̄_r(y)) ≤ 1 − ρ^d for every r ∈ (0, δ), which is a set belonging to 𝓝[>] 0. Passing to the limit (le_of_tendsto), the hypothesis gives 1 ≤ 1 − ρ^d, impossible because ρ^d > 0. This proves the claim.
4. (A sequence.) For k ∈ ℕ apply step 3 with δ := (k + 2)⁻¹: there is z_k ∈ Y with s_k := |z_k − y| ∈ (0, (k + 2)⁻¹) and |u_k − u| < (k + 2)⁻¹, where u_k := (z_k − y)/s_k. Hence z_k → y, s_k > 0, s_k → 0, and u_k → u.
5. (Difference quotients.) F is differentiable at y, so F(z) − F(y) − ℓ(z − y) = o(|z − y|) as z → y (HasFDerivAt.isLittleO). Since z_k → y with z_k ≠ y and z_k − y = s_k u_k,
 (F(z_k) − F(y))/s_k = ℓ(u_k) + (F(z_k) − F(y) − ℓ(z_k − y))/s_k → ℓ(u),
 using continuity of ℓ and u_k → u. In the same way (ψ(z_k) − ψ(y))/s_k → Bu.
6. (Lipschitz comparison.) z_k ∈ Y and y ∈ Y, so F(z_k) − F(y) = f(ψ(z_k)) − f(ψ(y)) and |F(z_k) − F(y)| ≤ L|ψ(z_k) − ψ(y)|. Dividing by s_k > 0: |(F(z_k) − F(y))/s_k| ≤ L|(ψ(z_k) − ψ(y))/s_k| for every k. Both sides converge by step 5 and continuity of |·|, and limits preserve non-strict inequalities (le_of_tendsto_of_tendsto'), so |ℓu| ≤ L|Bu|. By step 1 this proves the statement. ∎

Lean realization note. The verified code below proves the directions claim of step 3 for an arbitrary vector e instead of a unit vector, which also removes the reductions of steps 1–2: for ε, T > 0 there are t ∈ (0, T) and z ∈ Y with |z − (y + te)| < εt. It uses the ball B_{(ε/k)r}(y + (r/k)e) ⊆ B̄_r(y), k := |e| + ε (the same ball-in-cone measure argument, ρ = ε/k), and the additive form L^d(Y ∩ B̄_r(y)) + L^d(ball) ≤ L^d(B̄_r(y)) (so ratio + ρ^d ≤ 1, contradicting ratio → 1) instead of truncated subtraction. Steps 4–6 are realised with HasFDerivWithinAt.lim (c_n := t_n⁻¹, d_n := z_n − y) for both F and ψ and le_of_tendsto_of_tendsto'.

Appendix (verified Lean realization of the proof above). The code below compiles with Lean v4.35.0-rc3, Mathlib 25730c7c and simongmt 2b36630 when placed after `import GMT.Ch07.Submission` in the frozen contract scope (inside `namespace GMT.Ch07` with the contract's `open` commands, after the contract's `noncomputable section … end`), i.e. where accepted `theorem Submission.…` declarations live in GMT/Ch07/Submission.lean. It uses no sibling declaration. Auxiliary lemmas are named `Submission.dtc_bc_lc_sl_co_density_gradient_bound_aux_ball_meets`, `Submission.dtc_bc_lc_sl_co_density_gradient_bound_aux_dir` to stay globally unique; they may be renamed or inlined. It was checked twice: (i) with the exact frozen sibling types as hypotheses, giving no errors and no warnings and `#print axioms` = [propext, Classical.choice, Quot.sound]; (ii) end to end, in one file containing all eight new children of dtc_bc_lc_sl_coarea in dependency order, the parent theorem proved from them, and `sorry` placeholders only for the reused accepted declarations and the parent's resolved dependencies (no warning from any child declaration). `Submission.dtc_bc_lc_sl_co_density_gradient_bound` has exactly the frozen type of this child.

```lean
/-- At a density point `y` of `Y`, for every `ρ > 0` and all small `r > 0`, every ball of radius
`ρ r` contained in `closedBall y r` meets `Y`. -/
theorem Submission.dtc_bc_lc_sl_co_density_gradient_bound_aux_ball_meets {d : ℕ} {Y : Set (Euclid d)} {y : Euclid d}
    (hY : Tendsto (fun r => volume (Y ∩ closedBall y r) / volume (closedBall y r))
      (𝓝[>] 0) (𝓝 1))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ p : Euclid d, ball p (ρ * r) ⊆ closedBall y r →
      (Y ∩ ball p (ρ * r)).Nonempty := by
  have hc0 : ENNReal.ofReal (ρ ^ Module.finrank ℝ (Euclid d)) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos hρ _
  have h1 : Tendsto (fun r => volume (Y ∩ closedBall y r) / volume (closedBall y r)
      + ENNReal.ofReal (ρ ^ Module.finrank ℝ (Euclid d))) (𝓝[>] 0)
      (𝓝 (1 + ENNReal.ofReal (ρ ^ Module.finrank ℝ (Euclid d)))) :=
    hY.add tendsto_const_nhds
  have hlt : (1 : ℝ≥0∞) < 1 + ENNReal.ofReal (ρ ^ Module.finrank ℝ (Euclid d)) :=
    ENNReal.lt_add_right ENNReal.one_ne_top hc0
  filter_upwards [(tendsto_order.1 h1).1 1 hlt, self_mem_nhdsWithin] with r hr hr0 p hsub
  have hr0' : 0 < r := hr0
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hdisj : Disjoint (Y ∩ closedBall y r) (ball p (ρ * r)) := by
    rw [Set.disjoint_left]
    intro z hz hzW
    have hmem : z ∈ Y ∩ ball p (ρ * r) := ⟨hz.1, hzW⟩
    rw [hne] at hmem
    exact hmem
  have hmeas : volume (Y ∩ closedBall y r) + volume (ball p (ρ * r)) ≤
      volume (closedBall y r) := by
    rw [← measure_union hdisj measurableSet_ball]
    exact measure_mono (union_subset inter_subset_right hsub)
  have hVW : volume (ball p (ρ * r)) =
      ENNReal.ofReal (ρ ^ Module.finrank ℝ (Euclid d)) * volume (closedBall y r) := by
    rw [Measure.addHaar_ball_of_pos volume p (mul_pos hρ hr0'),
      Measure.addHaar_closedBall volume y hr0'.le, mul_pow,
      ENNReal.ofReal_mul (pow_nonneg hρ.le _), mul_assoc]
  have hV0 : volume (closedBall y r) ≠ 0 := (measure_closedBall_pos volume y hr0').ne'
  have hVT : volume (closedBall y r) ≠ ∞ := measure_closedBall_lt_top.ne
  have hle : volume (Y ∩ closedBall y r) / volume (closedBall y r)
      + ENNReal.ofReal (ρ ^ Module.finrank ℝ (Euclid d)) ≤ 1 := by
    calc volume (Y ∩ closedBall y r) / volume (closedBall y r)
          + ENNReal.ofReal (ρ ^ Module.finrank ℝ (Euclid d))
        = (volume (Y ∩ closedBall y r) + volume (ball p (ρ * r))) / volume (closedBall y r) := by
          rw [ENNReal.add_div, hVW, ENNReal.mul_div_cancel_right hV0 hVT]
      _ ≤ volume (closedBall y r) / volume (closedBall y r) := ENNReal.div_le_div_right hmeas _
      _ = 1 := ENNReal.div_self hV0 hVT
  exact absurd hr (not_lt.2 hle)

/-- Directions claim: at a density point `y` of `Y`, every vector `e` is approximated by
difference quotients of points of `Y`. -/
theorem Submission.dtc_bc_lc_sl_co_density_gradient_bound_aux_dir {d : ℕ} {Y : Set (Euclid d)} {y : Euclid d}
    (hY : Tendsto (fun r => volume (Y ∩ closedBall y r) / volume (closedBall y r))
      (𝓝[>] 0) (𝓝 1))
    (e : Euclid d) {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T) :
    ∃ t ∈ Ioo 0 T, ∃ z ∈ Y, dist z (y + t • e) < ε * t := by
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = ‖e‖ + ε := ⟨_, rfl⟩
  have hkpos : 0 < k := by rw [hk]; positivity
  obtain ⟨r, hr, hrT⟩ := ((Submission.dtc_bc_lc_sl_co_density_gradient_bound_aux_ball_meets hY (div_pos hε hkpos)).and
    (Ioo_mem_nhdsGT (mul_pos hT hkpos))).exists
  have htpos : 0 < r / k := div_pos hrT.1 hkpos
  have hρr : ε / k * r = ε * (r / k) := by ring
  have hsub : ball (y + (r / k) • e) (ε / k * r) ⊆ closedBall y r := by
    intro w hw
    rw [mem_ball, hρr] at hw
    rw [mem_closedBall]
    have h1 : dist (y + (r / k) • e) y = r / k * ‖e‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have h2 : r / k * ‖e‖ + ε * (r / k) = r := by
      calc r / k * ‖e‖ + ε * (r / k) = r / k * (‖e‖ + ε) := by ring
        _ = r / k * k := by rw [hk]
        _ = r := div_mul_cancel₀ r hkpos.ne'
    linarith [dist_triangle w (y + (r / k) • e) y]
  obtain ⟨z, hzY, hzW⟩ := hr (y + (r / k) • e) hsub
  refine ⟨r / k, ⟨htpos, (div_lt_iff₀ hkpos).2 hrT.2⟩, z, hzY, ?_⟩
  rw [mem_ball, hρr] at hzW
  exact hzW

theorem Submission.dtc_bc_lc_sl_co_density_gradient_bound : ∀ (d P : ℕ) (f : Euclid P → ℝ) (L : NNReal) (ψ : Euclid d → Euclid P) (F : Euclid d → ℝ) (Y : Set (Euclid d)) (y : Euclid d), LipschitzWith L f → y ∈ Y → DifferentiableAt ℝ ψ y → DifferentiableAt ℝ F y → (∀ z ∈ Y, f (ψ z) = F z) → Tendsto (fun r => volume (Y ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ e : Euclid d, |fderiv ℝ F y e| ≤ L * ‖fderiv ℝ ψ y e‖ := by
  intro d P f L ψ F Y y hf hyY hψ hF hfψ hY e
  have key : ∀ n : ℕ, ∃ t ∈ Ioo (0:ℝ) (1 / ((n:ℝ) + 1)), ∃ z ∈ Y,
      dist z (y + t • e) < 1 / ((n:ℝ) + 1) * t :=
    fun n => Submission.dtc_bc_lc_sl_co_density_gradient_bound_aux_dir hY e (by positivity) (by positivity)
  choose t ht z hz hzt using key
  have hlim0 : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have ht0 : Tendsto t atTop (𝓝 0) :=
    squeeze_zero (fun n => (ht n).1.le) (fun n => (ht n).2.le) hlim0
  have hcd : Tendsto (fun n => (t n)⁻¹ • (z n - y)) atTop (𝓝 e) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim0
    have htn : 0 < t n := (ht n).1
    have hrw : (t n)⁻¹ • (z n - y) - e = (t n)⁻¹ • (z n - (y + t n • e)) := by
      rw [sub_add_eq_sub_sub, smul_sub (t n)⁻¹ (z n - y), smul_smul, inv_mul_cancel₀ htn.ne',
        one_smul]
    rw [hrw, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htn, ← dist_eq_norm,
      inv_mul_le_iff₀ htn, mul_comm]
    exact (hzt n).le
  have hdlim : Tendsto (fun n => z n - y) atTop (𝓝 0) := by
    have h := ht0.smul hcd
    rw [zero_smul] at h
    refine h.congr (fun n => ?_)
    rw [smul_smul, mul_inv_cancel₀ (ht n).1.ne', one_smul]
  have hF' := (hasFDerivWithinAt_univ.2 hF.hasFDerivAt).lim hdlim
    (Eventually.of_forall fun n => mem_univ _) hcd
  have hψ' := (hasFDerivWithinAt_univ.2 hψ.hasFDerivAt).lim hdlim
    (Eventually.of_forall fun n => mem_univ _) hcd
  simp only [add_sub_cancel] at hF' hψ'
  refine le_of_tendsto_of_tendsto' hF'.abs (hψ'.norm.const_mul (L:ℝ)) (fun n => ?_)
  have htn : 0 < t n := (ht n).1
  rw [smul_eq_mul, abs_mul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htn,
    ← hfψ _ (hz n), ← hfψ _ hyY]
  have hL := hf.dist_le_mul (ψ (z n)) (ψ y)
  rw [Real.dist_eq, dist_eq_norm] at hL
  calc (t n)⁻¹ * |f (ψ (z n)) - f (ψ y)| ≤ (t n)⁻¹ * (L * ‖ψ (z n) - ψ y‖) :=
        mul_le_mul_of_nonneg_left hL (inv_nonneg.2 htn.le)
    _ = L * ((t n)⁻¹ * ‖ψ (z n) - ψ y‖) := by ring
```

## Key steps

1. Reduce to unit vectors u (d ≥ 1).
2. Directions: if no z ∈ Y near y has direction within δ of u, the ball B_{rρ}(y + (r/2)u) ⊆ B̄_r(y) (ρ = min(δ/8, 1/4)) misses Y for all r < δ, so the density ratio is ≤ 1 − ρ^d < 1, contradicting density 1.
3. Choose z_k ∈ Y, z_k → y, z_k ≠ y, (z_k − y)/|z_k − y| → u.
4. Divide |F(z_k) − F(y)| = |f(ψ z_k) − f(ψ y)| ≤ L|ψ(z_k) − ψ(y)| by |z_k − y| and let k → ∞ using differentiability: |DF(y)u| ≤ L|Dψ(y)u|.
5. Verified Lean realization supplied in the appendix (compiles warning-free; standard axioms only).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1, mathlib 25730c7c); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cat .lake/packages manifest (simongmt 2b36630)`
- `python3 -I scans of dag.json (1523 nodes): slicing-a1 subtree and statuses; frozen types of chart_pieces, chart_coarea, eilenberg, im_calculus; nodes matching bi-Lipschitz|immersion|density point|Lebesgue density|blowUpMap|tangential gradient|co-area|Injective (fderiv; the dor_lmb...slicing-a1.slice_family-a1 subtree (lipschitz_chart_pieces, density_directions, piece_coarea, piece_slice_tangent, tangential_gradient)`
- `git show <commit>:GMT/Ch07/Submission.lean and whitespace-normalised type comparison for cmc_imRep_locality_restrict_sub (2af75d6), codim1_rdo_c1cov_local_lower_lipschitz (12e74ed), rsd_tendsto_closedBall_density_of_approxTangent (dbef2c1), dor_lmb_approx_tangent_locality (53d4678): all MATCH; nodes/*/accepted-candidate.json comparator_passed = true`
- `grep -c dtc_bc_lc_sl_co_ dag.json (0); git log --all -S 'dtc_bc_lc_sl_co_' over 6410 refs (no match); survey of 400 accepted candidate commits: added declarations are theorem Submission.*`
- `grep in the snapshot Mathlib: Besicovitch.ae_tendsto_measure_inter_div, MeasurableSet.image_of_continuousOn_injOn, LipschitzOnWith.hausdorffMeasure_image_le, Convex.norm_image_sub_le_of_norm_fderiv_le, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_smul, Measure.addHaar_closedBall, measure_inter_add_sdiff, lintegral_iUnion, lintegral_tsum, ENNReal.Tendsto.sub, ContinuousOn.measurable_piecewise, Measurable.find, ContinuousOn.preimage_isClosed_of_isClosed, InjOn.leftInvOn_invFunOn, ae_restrict_iUnion_iff, ae_restrict_union_iff, ae_restrict_iff', ae_lt_top', NormedRing.inverse_continuousAt, ContinuousLinearMap.adjoint_inner_left, toDual_symm_apply, IsCompact.exists_bound_of_continuousOn, LinearMap.isUnit_iff_ker_eq_bot`
- `grep in SimonGMT: Chapter03/Rectifiable.lean (CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt, .unique, countablyRectifiable_iUnion, countablyRectifiable_of_measure_zero, CountablyRectifiable.mono); Chapter02/Lipschitz.lean (euclideanHausdorffMeasure_image_le_of_lipschitzOn); Chapter04/TangentDensity.lean; no nonlinear co-area, tangential gradient or slicing declarations`
- `sed book/chapter-03.txt lines 300-460 (Remark 1.8, 2.1-2.10) and book/chapter-06.txt lines 1140-1200 (Lemma 4.1)`
- `Lean checks through a persistent LSP worker: #check availability file under import GMT.Ch07.Submission; /tmp/coarea_split/v2/ch/Challenge_<key>.lean (11 modules from gmt-compare.py child_modules, contract mode); /tmp/coarea_split/asm/Assembly3.lean; /tmp/coarea_split/agents/{A,B,C,D,E} hypothesis-form proofs; /tmp/coarea_split/e2e2/E2E_from_json.lean and E2E_solution.lean (end to end, comparator form)`
- `sed /runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/runtime.py (_decompose depth gate, _dependency_problem, _existing_lean_name_problem) and prompts.py (DECOMPOSITION_AUDIT, RLCR_LEAN_TASK, LEAN_AUDIT, SPECULATIVE_PARENT_TASK)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-772be56655/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-ec0e4b9204/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/prompts.py`
- `/tmp/coarea_split/v2/ch`
- `/tmp/coarea_split/asm/Assembly3.lean`
- `/tmp/coarea_split/e2e2/E2E_from_json.lean`
- `/tmp/coarea_split/e2e2/E2E_solution.lean`

Neither the pinned SimonGMT library nor Mathlib has a nonlinear co-area formula, a tangential gradient of Lipschitz functions on rectifiable sets, or slicing. They do supply every tool cited in the child proofs: the Lebesgue density theorem, Lusin–Souslin, the Lipschitz image bound, the mean value inequality, Haar scaling, adjoints, continuity of Ring.inverse, and the countable-rectifiability lemmas. Three comparator-accepted DAG declarations are reused with identical types: cmc_imRep_locality_restrict_sub, codim1_rdo_c1cov_local_lower_lipschitz and rsd_tendsto_closedBall_density_of_approxTangent. dor_lmbsf_density_directions (accepted) overlaps one step of density_gradient_bound but is not needed. The eight new names are unreserved. All 11 types elaborate in the exact comparator challenge modules. Every new child is proved in Lean exactly as typed, both in hypothesis form and end to end. The exact frozen parent type is proved from the children and its resolved dependencies, using only propext, Classical.choice and Quot.sound.
