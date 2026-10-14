# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1.lipschitz_minor_ibp-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 6(i), Lipschitz case: 'For Lipschitz functions mollify g and all u_i simultaneously: ... h∗ϕ_δ → h uniformly, D(h∗ϕ_δ) = (Dh)∗ϕ_δ → Dh a.e. and |D(h∗ϕ_δ)| ≤ Lip(h); dominated convergence on the compact set spt β gives the identity in the limit', written for the coordinate coefficients (Jacobian minors in directions V_0, …, V_r) as in the sibling smooth_minor_ibp. Uses the siblings lipschitz_smooth_approx (the mollified functions), smooth_minor_ibp (the identity for smooth functions) and minor_bound (measurability and bounds). (The frozen type is identical to that of the not yet accepted node dor_lmb_fcd_jwc_lipschitz_minor_ibp of another branch, so a fresh name is used.)

Notation: λ = Lebesgue measure on ℝᵏ = Euclid k; D = fderiv ℝ (the zero map where the function is not differentiable); ∂_Wψ(x) := Dψ(x)W; A(x) := (Dg_c(x)V_b)_{c,b ∈ Fin(r+1)}, M_b(x) := det(Dg_{c+1}(x)V_{s_b(b')})_{c,b' ∈ Fin r} with s_b = Fin.succAbove b; B := (r+1)!·(L·Σ_b ‖V_b‖)^{r+1} and B_b := r!·(L·Σ_{b'} ‖V_{s_b(b')}‖)^r.

1. (Approximation.) For each c ∈ Fin(r+1) the sibling lipschitz_smooth_approx gives functions g^n_c (n ∈ ℕ), each C^∞ and L-Lipschitz, with g^n_c → g_c uniformly on ℝᵏ and Dg^n_c(x) → Dg_c(x) for all x outside a λ-null set N_c. N := ∪_c N_c is null (finite union; ae_all_iff). Let A^n, M^n_b be defined like A, M_b from the g^n_c.

2. (Smooth identity.) For every n the g^n_c are C^∞, hence C², and ψ is C¹ with compact support, so the sibling smooth_minor_ibp gives ∫ ψ·det A^n = −Σ_b (−1)^b ∫ ∂_{V_b}ψ·g^n_0·M^n_b.

3. (Pointwise convergence.) For x ∉ N and all c, b: Dg^n_c(x)V_b → Dg_c(x)V_b (evaluation at V_b is a continuous linear map on the space of linear maps). Matrices converge entrywise and the determinant is continuous (Continuous.matrix_det), so det A^n(x) → det A(x) and M^n_b(x) → M_b(x). Moreover g^n_0(x) → g_0(x) for every x (uniform convergence).

4. (Bounds and measurability.) All g^n_c are L-Lipschitz, so by the sibling minor_bound, det A^n and M^n_b are measurable with |det A^n(x)| ≤ B and |M^n_b(x)| ≤ B_b for all n and x. ψ and ∂_{V_b}ψ are continuous with compact support (Dψ is continuous since ψ is C¹, and it vanishes outside the support of ψ), hence integrable; g^n_0 and g_0 are continuous.

5. (Left side.) |ψ·det A^n| ≤ B·|ψ|, an integrable function independent of n, and ψ·det A^n → ψ·det A outside N by step 3. By dominated convergence (tendsto_integral_of_dominated_convergence), ∫ ψ·det A^n → ∫ ψ·det A.

6. (Right side.) By uniform convergence there is n_0 with |g^n_0(x) − g_0(x)| ≤ 1 for all x and all n ≥ n_0, hence |g^n_0(x)| ≤ |g_0(x)| + 1. For n ≥ n_0, |∂_{V_b}ψ·g^n_0·M^n_b| ≤ B_b·|∂_{V_b}ψ|·(|g_0| + 1), which is continuous with compact support, hence integrable. The integrands converge outside N by step 3. Dominated convergence with a bound valid for all large n (tendsto_integral_filter_of_dominated_convergence) gives ∫ ∂_{V_b}ψ·g^n_0·M^n_b → ∫ ∂_{V_b}ψ·g_0·M_b for each b, so the right side of step 2 converges to −Σ_b (−1)^b ∫ ∂_{V_b}ψ·g_0·M_b (finite sums and constant multiples of convergent sequences converge).

7. (Conclusion.) The two sides of step 2 agree for every n; by uniqueness of limits in ℝ (tendsto_nhds_unique) the limits of steps 5 and 6 agree, which is the claimed identity ∫ ψ·det A = −Σ_b (−1)^b ∫ ∂_{V_b}ψ·g_0·M_b.

Lean realization (compiled during this decomposition with the pinned toolchain against GMT.Ch07.Submission at b4d606db, Mathlib 25730c7c, in the Submission layout: inside namespace GMT.Ch07 after the contract's open commands, together with the proofs of the sibling declarations it uses; no extra import, no sorry; #print axioms: propext, Classical.choice, Quot.sound):
```lean
/-- **Integration by parts for Jacobian minors of Lipschitz maps** (the step "`(∗)` holds for
Lipschitz `v`" in the weak continuity of Jacobian minors): for `L`-Lipschitz `g₀, …, g_r` on `ℝᵏ`,
vectors `V₀, …, V_r` and `ψ ∈ C¹_c(ℝᵏ)`,
`∫ ψ det A = −Σ_b (−1)^b ∫ ∂_{V_b}ψ · g₀ · M_b`, where `A = (Dg_c V_b)_{c,b}` and `M_b` is the minor
`det (Dg_{c+1} V_{s_b(b')})_{c,b'}`, `s_b = b.succAbove`.  Mollify every `g_c`: `C^∞`, `L`-Lipschitz
`g^n_c → g_c` uniformly with `Dg^n_c → Dg_c` a.e.  The identity holds for every `n` (smooth case);
the determinants converge a.e. and are bounded by `(r+1)! (L Σ_b ‖V_b‖)^(r+1)`, resp.
`r! (L Σ_b' ‖V_{s_b(b')}‖)^r`, so both sides converge by dominated convergence (on the right with
`|g^n_0| ≤ |g_0| + 1` for large `n`), and the limits agree. -/
theorem Submission.dimred_mbl_dt_lp_jc_lipschitz_minor_ibp : ∀ (k r : ℕ) (L : NNReal) (g : Fin (r + 1) → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (ψ : Euclid k → ℝ), (∀ c, LipschitzWith L (g c)) → ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) = -∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * ∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))) := by
  intro k r L g V ψ hg hψ hψs
  -- step 1: smooth `L`-Lipschitz approximants `fs c n` of every component `g c`
  choose fs hfs_smooth hfs_lip hfs_unif hfs_ae using
    fun c => Submission.dimred_mbl_dt_lp_jc_lipschitz_smooth_approx k L (g c) (hg c)
  -- step 2: the identity for the smooth maps `fs · n`
  have hid := fun n => Submission.dimred_mbl_dt_lp_jc_smooth_minor_ibp k r (fun c => fs c n) V ψ
    (fun c => (hfs_smooth c n).of_le (by simp)) hψ hψs
  -- step 3: off a null set all derivatives converge, hence so do the entries and determinants
  have hae : ∀ᵐ x ∂(volume : Measure (Euclid k)), ∀ c,
      Tendsto (fun n => fderiv ℝ (fs c n) x) atTop (𝓝 (fderiv ℝ (g c) x)) := ae_all_iff.2 hfs_ae
  have hdet_lim : ∀ {m : ℕ} (σ : Fin m → Fin (r + 1)) (W : Fin m → Euclid k) (x : Euclid k),
      (∀ c, Tendsto (fun n => fderiv ℝ (fs c n) x) atTop (𝓝 (fderiv ℝ (g c) x))) →
      Tendsto (fun n => Matrix.det (Matrix.of fun (c b : Fin m) => fderiv ℝ (fs (σ c) n) x (W b)))
        atTop (𝓝 (Matrix.det (Matrix.of fun (c b : Fin m) => fderiv ℝ (g (σ c)) x (W b)))) := by
    intro m σ W x hx
    have hM : Tendsto (fun n => (Matrix.of fun (c b : Fin m) => fderiv ℝ (fs (σ c) n) x (W b)))
        atTop (𝓝 (Matrix.of fun (c b : Fin m) => fderiv ℝ (g (σ c)) x (W b))) := by
      refine tendsto_pi_nhds.2 fun c => tendsto_pi_nhds.2 fun b => ?_
      exact ((ContinuousLinearMap.apply ℝ ℝ (W b)).continuous.tendsto _).comp (hx (σ c))
    exact ((continuous_id.matrix_det).tendsto _).comp hM
  -- step 4: the bound `B` of the full determinants and the integrability of `ψ`
  set B : ℝ := ((r + 1).factorial : ℝ) * ((L : ℝ) * ∑ b, ‖V b‖) ^ (r + 1)
  have hψc : Continuous ψ := hψ.continuous
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  -- step 5: the left side converges, dominated by `B |ψ|`
  have hL : Tendsto
      (fun n => ∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (fs c n) x (V b)))
      atTop (𝓝 (∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => B * ‖ψ x‖) (fun n => ?_)
      (hψi.norm.const_mul B) (fun n => Eventually.of_forall fun x => ?_) ?_
    · exact hψc.aestronglyMeasurable.mul
        (Submission.dor_lmb_fcd_jwc_minor_measurable_bound k (r + 1) L (fun c => fs c n) V
          (fun c => hfs_lip c n)).1.aestronglyMeasurable
    · have h := (Submission.dor_lmb_fcd_jwc_minor_measurable_bound k (r + 1) L (fun c => fs c n) V
        (fun c => hfs_lip c n)).2 x
      rw [norm_mul, Real.norm_eq_abs (Matrix.det _), mul_comm]
      exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
    · filter_upwards [hae] with x hx
      exact tendsto_const_nhds.mul (hdet_lim id V x hx)
  -- step 6: each term of the right side converges, dominated by `Br |∂_{V_b}ψ| (|g 0| + 1)`
  have hR : ∀ b : Fin (r + 1), Tendsto (fun n => ∫ x, fderiv ℝ ψ x (V b) * fs 0 n x *
      Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (fs c.succ n) x (V (b.succAbove b'))))
      atTop (𝓝 (∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det
        (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))))) := by
    intro b
    set Br : ℝ := (r.factorial : ℝ) * ((L : ℝ) * ∑ b', ‖V (b.succAbove b')‖) ^ r
    have hdψc : Continuous (fun x => fderiv ℝ ψ x (V b)) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdψs : HasCompactSupport (fun x => fderiv ℝ ψ x (V b)) := hψs.fderiv_apply (𝕜 := ℝ) (V b)
    have hwi : Integrable (fun x => Br * (‖fderiv ℝ ψ x (V b)‖ * (‖g 0 x‖ + 1))) := by
      refine Integrable.const_mul ?_ _
      exact Continuous.integrable_of_hasCompactSupport
        (hdψc.norm.mul ((hg 0).continuous.norm.add continuous_const)) hdψs.norm.mul_right
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => Br * (‖fderiv ℝ ψ x (V b)‖ * (‖g 0 x‖ + 1)))
      (Eventually.of_forall fun n => ?_) ?_ hwi ?_
    · exact (hdψc.mul (hfs_smooth 0 n).continuous).aestronglyMeasurable.mul
        (Submission.dor_lmb_fcd_jwc_minor_measurable_bound k r L (fun c => fs c.succ n)
          (fun b' => V (b.succAbove b')) (fun c => hfs_lip c.succ n)).1.aestronglyMeasurable
    · -- `|fs 0 n| ≤ |g 0| + 1` once `fs 0 n` is uniformly `1`-close to `g 0`
      obtain ⟨N, hN⟩ :=
        (Metric.tendstoUniformly_iff.1 (hfs_unif 0) 1 one_pos).exists_forall_of_atTop
      refine eventually_atTop.2 ⟨N, fun n hn => Eventually.of_forall fun x => ?_⟩
      have h1 : ‖fs 0 n x‖ ≤ ‖g 0 x‖ + 1 := by
        have := hN n hn x
        rw [dist_comm, dist_eq_norm] at this
        have := norm_le_insert' (fs 0 n x) (g 0 x)
        linarith
      have h2 := (Submission.dor_lmb_fcd_jwc_minor_measurable_bound k r L (fun c => fs c.succ n)
        (fun b' => V (b.succAbove b')) (fun c => hfs_lip c.succ n)).2 x
      rw [norm_mul, norm_mul, Real.norm_eq_abs (Matrix.det _)]
      calc ‖fderiv ℝ ψ x (V b)‖ * ‖fs 0 n x‖ * |Matrix.det _|
          ≤ ‖fderiv ℝ ψ x (V b)‖ * (‖g 0 x‖ + 1) * Br := by gcongr
        _ = Br * (‖fderiv ℝ ψ x (V b)‖ * (‖g 0 x‖ + 1)) := by ring
    · filter_upwards [hae] with x hx
      refine (tendsto_const_nhds.mul ((hfs_unif 0).tendsto_at x)).mul ?_
      exact hdet_lim Fin.succ (fun b' => V (b.succAbove b')) x hx
  have hRall : Tendsto (fun n => -∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) *
      ∫ x, fderiv ℝ ψ x (V b) * fs 0 n x * Matrix.det
        (Matrix.of fun (c b' : Fin r) => fderiv ℝ (fs c.succ n) x (V (b.succAbove b'))))
      atTop (𝓝 (-∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * ∫ x, fderiv ℝ ψ x (V b) * g 0 x *
        Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))))) :=
    Tendsto.neg (tendsto_finsetSum _ fun b _ => (hR b).const_mul _)
  -- step 7: both sides of step 2 agree for every `n`, so their limits agree
  exact tendsto_nhds_unique hL (hRall.congr fun n => (hid n).symm)
```

## Key steps

1. Approximate every g_c by C^∞, L-Lipschitz g^n_c → g_c uniformly with Dg^n_c → Dg_c off a null set (sibling lipschitz_smooth_approx).
2. The identity holds for every n (sibling smooth_minor_ibp).
3. Determinants converge a.e. (continuity of det) and are bounded by (r+1)!(LΣ‖V_b‖)^{r+1}, resp. r!(LΣ‖V_{s_b b'}‖)^r (sibling minor_bound).
4. Dominated convergence on both sides (with |g^n_0| ≤ |g_0| + 1 for large n) and uniqueness of limits.

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git -C SNAPSHOT/mathlib rev-parse HEAD (25730c7c); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean workspace GMT/Ch07/Submission.lean (identical); git log -1 of the workspace (b4d606db)`
- `rg -n -i 'piola|mollif|weak.?contin|null.?lagrang|minor' SNAPSHOT/project -g '*.lean' (no relevant match: only LpSeminorm imports and a Hölder-seminorm comment in Ch04/Ch05); rg -n -i jacobian SNAPSHOT/project/GMT/Ch02/Contract.lean SNAPSHOT/project/GMT/Ch03/Contract.lean SNAPSHOT/project/GMT/Ch07/Contract.lean (only the areaJacobian/coareaJacobian definitions of Ch02/Ch03 and the area/coarea formulas; nothing in Ch07)`
- `rg -l 'dimred_mbl_dt_lp_jc|dor_lmb_fcd_jwc|cmcs_ls_mollify|cmr_cc_det' SNAPSHOT/project (no match; these declarations exist only in DAG candidate commits)`
- `rg -n '^(theorem|lemma) [A-Za-z_.]*NAME' SNAPSHOT/mathlib/Mathlib for NAME in integral_lineDeriv_mul_eq, norm_fderiv_le_of_lipschitz, measurable_fderiv_apply_const, contDiff_convolution_left, hasFDerivAt_convolution_left, convolutionExists_left, ae_tendsto_average_norm_sub, tendsto_integral_smul_of_tendsto_average_norm_sub, dist_convolution_le, extDeriv_pullback, extDeriv_apply, det_succ_row_zero, tendsto_integral_filter_of_dominated_convergence, ae_differentiableAt, induction_dense, exists_contDiff_support_eq_eq_one_iff, lipschitzWith_of_hasCompactSupport, exists_isCompact_sdiff_lt, exists_isOpen_sdiff_lt, bdd_mul, addHaar_real_closedBall' (all found); ae_convolution_tendsto_right_of_locallyIntegrable and det_le (found in the snapshot, see next query)`
- `lake env lean /tmp/jc-decomp2/probe/Probe.lean importing only GMT.Ch07.Submission: #check ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable and Matrix.det_le (Unknown constant: outside the frozen import closure); #check IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub, tendsto_integral_smul_of_tendsto_average_norm_sub, LipschitzWith.integral_lineDeriv_mul_eq, MemLp.induction_dense, HasCompactSupport.hasFDerivAt_convolution_left, extDeriv_pullback (available)`
- `python3 scans of RUN/dag.json: nodes whose id/title/statement mention Jacobian weak continuity; status, candidate_commit, updated_at and lean_statement of the eleven child names under the runtime rule _accepted_checkpoint (six reused names accepted with byte-identical types; twin mollify_fderiv accepted at 01:41:31Z, the four other twins comparing/speculative-ready); collision scan for dimred_mbl_dt_lp_jc_* (unused); RUN/issue-workers.json (mode broker-owned-issue-polling; worker for issue 7020 started 2026-10-14T00:19:09Z)`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose depth guard and name checks, _existing_lean_name_problem, _accepted_checkpoint, _solve_children reuse by lean_name), store.py (refresh, update: accepted is permanent), parallel.py (enabled, RefreshLock), scripts/swarm-run-issue.py, and workspace .humanize/swarm-configs/c8e45649089f4d62adf9de1e95c664c3.json (github_shared_issue_runtime true, max_depth 6, max_children 12, max_nodes 5000, decomposition_attempts 5)`
- `git show <commit>:GMT/Ch07/Submission.lean for accepted candidates fee01ff86c, 2c87728a, 7ba02a03, c6153c4c, 52b9c39c, 13966862 (reused proofs byte-identical to the compiled chain) and ebbe3de7 (accepted twin of mollify_fderiv; proof body identical to the embedded realization)`
- `lake env lean /tmp/jc-decomp2/lean/FinalCheck.lean (eleven child proofs, assembly_from_children, Submission.dimred_mbl_dt_lp_jacobian_weak_continuity with its frozen type, exact-type checks; exit 0, no sorry, axioms propext/Classical.choice/Quot.sound); lake env lean /tmp/jc-decomp2/challenges/AllChallenges.lean (prefix from verifier contract_scope; exit 0, only sorry warnings); both validate_lean_statement implementations on all eleven types; dependency cross-check of Submission.* references against depends_on`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-b372f37aac/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-b372f37aac/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/c8e45649089f4d62adf9de1e95c664c3.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/parallel.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/scripts/swarm-run-issue.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/jc-decomp2/lean/FinalCheck.lean`
- `/tmp/jc-decomp2/challenges/AllChallenges.lean`
- `/tmp/jc-decomp2/probe/Probe.lean`

Pins match: project b4d606db and Mathlib 25730c7c, and the workspace Submission is byte-identical to the frozen Ch07 contract. The snapshot project contains no weak-continuity, Piola, mollification or minor-expansion lemma. Its only Jacobians are the Ch02/Ch03 area/coarea Jacobian definitions, so the needed obligations come from the DAG. Six comparator-accepted DAG declarations with exactly the needed types are reused verbatim: cmr_cc_det_covector_exists, dor_lmb_fcd_jwc_covector_det_expansion, dor_lmb_fcd_jwc_weak_star_l1_upgrade, dor_lmb_fcd_jwc_piola_identity, cmcs_ls_mollify_lipschitz and dor_lmb_fcd_jwc_minor_measurable_bound. All six were accepted before this attempt's shared-DAG refresh (01:30:20Z), so the earlier 'reserved by active DAG node' rejection no longer applies. The five remaining links get fresh, unused dimred_mbl_dt_lp_jc_* names, because their twins were unaccepted at that refresh. Every Mathlib lemma cited by the child proofs exists in the snapshot and is available after import GMT.Ch07.Submission. ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable and Matrix.det_le exist in the snapshot but are outside the import closure, so the child proofs use in-closure substitutes. All eleven child proofs plus the parent, stated with its exact frozen type, compile together with no sorry and only the standard axioms. Every type elaborates in the comparator's challenge scope.
