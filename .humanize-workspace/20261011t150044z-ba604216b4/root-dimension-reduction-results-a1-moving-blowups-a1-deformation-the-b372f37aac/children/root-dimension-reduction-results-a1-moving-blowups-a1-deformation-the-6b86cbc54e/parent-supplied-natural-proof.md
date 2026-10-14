# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1.smooth_minor_ibp-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 6(i), smooth case: 'For C^∞ functions this is ∫ d(gβ ∧ du_2 ∧ ⋯ ∧ du_r) = 0 (Stokes for a compactly supported exact n-form, i.e. ∫∂_b(·) = 0 for compactly supported C¹ coefficients), together with d(gβ ∧ du_2 ∧ ⋯) = dg ∧ β ∧ du_2 ∧ ⋯ + g dβ ∧ du_2 ∧ ⋯ (d(du_i) = 0)'. As announced in the parent ('all statements below are statements about these coordinate integrals'), it is written here for the coordinate coefficients: Jacobian minors with rows g_0, …, g_r and arbitrary directions V_0, …, V_r, the row g_0 being integrated by parts (g_0 plays g, the rows g_1, …, g_r play u_2, …, u_r, and ψ is the coefficient of the test form); only C² regularity of the rows and C¹ regularity of ψ are needed. Uses the sibling piola_identity (d(du) = 0 in coordinates). (The frozen type is identical to that of the not yet accepted node dor_lmb_fcd_jwc_smooth_minor_ibp of another branch, so a fresh name is used.)

Notation: λ = Lebesgue measure on ℝᵏ = Euclid k; D = fderiv ℝ; ∂_W F(x) := DF(x)W; A(x) := (Dg_c(x)V_b)_{c,b ∈ Fin(r+1)}; for b ∈ Fin(r+1), s_b := Fin.succAbove b and M_b(x) := det(Dg_{c+1}(x)V_{s_b(b')})_{c,b' ∈ Fin r}, the minor of A(x) with row 0 and column b deleted.

1. (Laplace expansion along row 0; Matrix.det_succ_row_zero.) For every x, det A(x) = Σ_{b=0}^{r} (−1)^b·A(x)_{0,b}·det(A(x) without row 0 and column b) = Σ_b (−1)^b·∂_{V_b}g_0(x)·M_b(x), because deleting row 0 and column b of A(x) leaves the matrix (∂_{V_{s_b(b')}} g_{c+1}(x))_{c,b'}.

2. (Regularity.) Each entry y ↦ ∂_W g_c(y) = Dg_c(y)W is C¹ because g_c is C² (ContDiff.fderiv_right, then evaluation at the constant W). A determinant of a matrix of C¹ entries is C¹, since by the Leibniz formula it is a finite sum of constants times finite products of entries (ContDiff.sum, contDiff_prod). Hence every M_b is C¹, and F_b := ψ·g_0·M_b is C¹; F_b has compact support because its support lies in that of ψ.

3. (Product rule.) For every b and x, ∂_{V_b}F_b(x) = ∂_{V_b}ψ(x)·g_0(x)·M_b(x) + ψ(x)·∂_{V_b}g_0(x)·M_b(x) + ψ(x)·g_0(x)·∂_{V_b}M_b(x) (HasFDerivAt.mul twice).

4. (Piola.) The sibling piola_identity applied to the C² functions c ↦ g_{c+1} (c ∈ Fin r) and the directions V_0, …, V_r gives Σ_b (−1)^b·∂_{V_b}M_b(x) = 0 for every x.

5. (Pointwise identity.) Multiply step 3 by (−1)^b and sum over b. The middle terms give ψ·Σ_b (−1)^b ∂_{V_b}g_0·M_b = ψ·det A by step 1, and the last terms give ψ·g_0·Σ_b (−1)^b ∂_{V_b}M_b = 0 by step 4. Hence for every x: ψ(x)·det A(x) = Σ_b (−1)^b ∂_{V_b}F_b(x) − Σ_b (−1)^b ∂_{V_b}ψ(x)·g_0(x)·M_b(x).

6. (Exact derivatives integrate to zero.) Let F be C¹ with compact support and W ∈ ℝᵏ. F is Lipschitz (ContDiff.lipschitzWith_of_hasCompactSupport). Integration by parts for Lipschitz functions (LipschitzWith.integral_lineDeriv_mul_eq) applied to the constant function 1 (Lipschitz, with zero line derivative), the compactly supported Lipschitz F and the direction −W gives ∫ (∂_W F)·1 dλ = ∫ (line derivative of 1)·F dλ = 0; as F is differentiable, its line derivative in direction W is DF(·)W (DifferentiableAt.lineDeriv_eq_fderiv). Thus ∫ ∂_W F dλ = 0.

7. (Integration.) Every function in step 5 is continuous with compact support, hence integrable: ∂_{V_b}F_b is continuous (F_b is C¹) and vanishes outside the support of F_b (HasCompactSupport.fderiv_apply); ∂_{V_b}ψ is continuous (ψ is C¹) and vanishes outside the support of ψ, and g_0, M_b are continuous. Integrating step 5, using linearity (integral_sub, integral_finsetSum, integral_const_mul) and step 6 for each F_b: ∫ ψ·det A dλ = 0 − Σ_b (−1)^b ∫ ∂_{V_b}ψ·g_0·M_b dλ, which is the claim.

Lean realization (compiled during this decomposition with the pinned toolchain against GMT.Ch07.Submission at b4d606db, Mathlib 25730c7c, in the Submission layout: inside namespace GMT.Ch07 after the contract's open commands, together with the proofs of the sibling declarations it uses; no extra import, no sorry; #print axioms: propext, Classical.choice, Quot.sound):
```lean
/-- **Integration by parts for Jacobian minors** (formula (∗) of the weak continuity of Jacobian
minors, for `C²` maps): for `C²` functions `g₀, …, g_r` on `ℝᵏ`, directions `V₀, …, V_r` and a
compactly supported `C¹` function `ψ`, with `A = (Dg_c V_b)_{c,b}` and `M_b` the minor of `A`
without row `0` and column `b`, `∫ ψ det A = −Σ_b (−1)^b ∫ (Dψ V_b) g₀ M_b`.  Laplace expansion
along row `0`, the product rule for `F_b = ψ g₀ M_b` and the Piola identity
`Σ_b (−1)^b ∂_{V_b} M_b = 0` give `ψ det A = Σ_b (−1)^b ∂_{V_b} F_b − Σ_b (−1)^b (∂_{V_b} ψ) g₀ M_b`
pointwise, and `∫ ∂_W F = 0` for every compactly supported `C¹` function `F` (integration by
parts of the Lipschitz functions `1` and `F`). -/
theorem Submission.dimred_mbl_dt_lp_jc_smooth_minor_ibp : ∀ (k r : ℕ) (g : Fin (r + 1) → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (ψ : Euclid k → ℝ), (∀ c, ContDiff ℝ 2 (g c)) → ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) = -∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * ∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))) := by
  intro k r g V ψ hg hψ hψs
  -- Step 2: the entries `Dg_c(·)W` are `C¹` (`g_c` is `C²`), hence so is every determinant of
  -- such entries (Leibniz formula), in particular every minor `M_b`
  have hdetC1 : ∀ {m : ℕ} (A : Euclid k → Fin m → Fin m → ℝ),
      (∀ i j, ContDiff ℝ 1 (fun x => A x i j)) →
      ContDiff ℝ 1 (fun x => Matrix.det (Matrix.of (A x))) := by
    intro m A hA
    have hLeib : (fun x => Matrix.det (Matrix.of (A x))) =
        fun x => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A x (σ i) i := by
      funext x
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Units.smul_def, zsmul_eq_mul]
      simp [Matrix.of_apply]
    rw [hLeib]
    exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hA _ _)
  have hentry : ∀ c (W : Euclid k), ContDiff ℝ 1 (fun x => fderiv ℝ (g c) x W) := fun c W =>
    ((hg c).fderiv_right (by norm_num)).clm_apply contDiff_const
  set M : Fin (r + 1) → Euclid k → ℝ := fun b x => Matrix.det (Matrix.of fun (c b' : Fin r) =>
    fderiv ℝ (g c.succ) x (V (b.succAbove b')))
  have hMC1 : ∀ b, ContDiff ℝ 1 (M b) := fun b =>
    hdetC1 (fun x c b' => fderiv ℝ (g c.succ) x (V (b.succAbove b'))) fun c b' => hentry _ _
  -- `F_b = ψ g₀ M_b` is `C¹` with compact support
  have hFC1 : ∀ b, ContDiff ℝ 1 (fun y => ψ y * g 0 y * M b y) := fun b =>
    (hψ.mul ((hg 0).of_le (by norm_num))).mul (hMC1 b)
  have hFs : ∀ b, HasCompactSupport (fun y => ψ y * g 0 y * M b y) := fun b =>
    hψs.mul_right.mul_right
  -- Step 3: product rule for `∂_{V_b} F_b`
  have hdiff : ∀ b x, fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b) =
      fderiv ℝ ψ x (V b) * g 0 x * M b x + ψ x * fderiv ℝ (g 0) x (V b) * M b x +
        ψ x * g 0 x * fderiv ℝ (M b) x (V b) := by
    intro b x
    have hψd : DifferentiableAt ℝ ψ x := hψ.differentiable (by norm_num) x
    have hgd : DifferentiableAt ℝ (g 0) x := (hg 0).differentiable (by norm_num) x
    have hMd : DifferentiableAt ℝ (M b) x := (hMC1 b).differentiable (by norm_num) x
    have h : HasFDerivAt (fun y => ψ y * g 0 y * M b y) _ x :=
      (hψd.hasFDerivAt.mul hgd.hasFDerivAt).mul hMd.hasFDerivAt
    rw [h.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, Pi.mul_apply]
    ring
  -- Steps 1, 4, 5: Laplace expansion along row `0` and the Piola identity give, pointwise,
  -- `ψ det A = Σ_b (−1)^b ∂_{V_b} F_b − Σ_b (−1)^b (∂_{V_b} ψ) g₀ M_b`
  have hpt : ∀ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) =
      ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b) -
        ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * (fderiv ℝ ψ x (V b) * g 0 x * M b x) := by
    intro x
    have hp : ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (M b) x (V b) = 0 :=
      Submission.dor_lmb_fcd_jwc_piola_identity k r (fun c => g c.succ) V x fun c => hg c.succ
    simp_rw [hdiff]
    have halg : ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * (fderiv ℝ ψ x (V b) * g 0 x * M b x +
          ψ x * fderiv ℝ (g 0) x (V b) * M b x + ψ x * g 0 x * fderiv ℝ (M b) x (V b)) -
        ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * (fderiv ℝ ψ x (V b) * g 0 x * M b x) =
        ψ x * ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (g 0) x (V b) * M b x +
          ψ x * g 0 x * ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (M b) x (V b) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [halg, hp, mul_zero, add_zero, Matrix.det_succ_row_zero]
    rfl
  -- Step 6: `∫ ∂_W F = 0` for `C¹` compactly supported `F` (integration by parts of the
  -- Lipschitz functions `1` and `F`)
  have hIBP0 : ∀ F : Euclid k → ℝ, ContDiff ℝ 1 F → HasCompactSupport F → ∀ W,
      ∫ x, fderiv ℝ F x W = 0 := by
    intro F hF hFs W
    obtain ⟨C, hFL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hFs hF (by norm_num)
    have h := LipschitzWith.integral_lineDeriv_mul_eq (μ := (volume : Measure (Euclid k)))
      (LipschitzWith.const (1 : ℝ)) hFL hFs (-W)
    have h0 : ∀ x : Euclid k, lineDeriv ℝ (fun _ : Euclid k => (1 : ℝ)) x (-W) = 0 := by
      intro x
      rw [(differentiableAt_const (1 : ℝ)).lineDeriv_eq_fderiv]
      simp
    have h1 : ∀ x, lineDeriv ℝ F x W = fderiv ℝ F x W := fun x =>
      (hF.differentiable (by norm_num) x).lineDeriv_eq_fderiv
    simp only [h0, zero_mul, integral_zero, neg_neg, mul_one, h1] at h
    exact h.symm
  -- Step 7: every term is continuous with compact support, hence integrable; integrate
  have hi1 : ∀ b : Fin (r + 1), Integrable (fun x => (-1 : ℝ) ^ (b : ℕ) *
      fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b)) := fun b =>
    ((((hFC1 b).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).integrable_of_hasCompactSupport ((hFs b).fderiv_apply ℝ (V b))).const_mul _
  have hi2 : ∀ b : Fin (r + 1), Integrable (fun x => (-1 : ℝ) ^ (b : ℕ) *
      (fderiv ℝ ψ x (V b) * g 0 x * M b x)) := fun b =>
    (((((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
      (hg 0).continuous).mul (hMC1 b).continuous).integrable_of_hasCompactSupport
      ((hψs.fderiv_apply ℝ (V b)).mul_right.mul_right)).const_mul _
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_sub (integrable_finsetSum _ fun b _ => hi1 b)
      (integrable_finsetSum _ fun b _ => hi2 b),
    integral_finsetSum _ fun b _ => hi1 b, integral_finsetSum _ fun b _ => hi2 b]
  have hz : ∑ b : Fin (r + 1), ∫ x, (-1 : ℝ) ^ (b : ℕ) *
      fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b) = 0 :=
    Finset.sum_eq_zero fun b _ => by rw [integral_const_mul, hIBP0 _ (hFC1 b) (hFs b) _, mul_zero]
  rw [hz, zero_sub]
  simp only [integral_const_mul]
  rfl
```

## Key steps

1. Laplace expansion along row 0: det A = Σ_b (−1)^b ∂_{V_b}g_0·M_b.
2. Product rule for F_b = ψ·g_0·M_b (C¹ with compact support) and the Piola identity Σ_b (−1)^b ∂_{V_b}M_b = 0 give ψ det A = Σ_b (−1)^b ∂_{V_b}F_b − Σ_b (−1)^b ∂_{V_b}ψ·g_0·M_b pointwise.
3. ∫ ∂_W F = 0 for C¹ compactly supported F (integration by parts against the constant 1).
4. Integrate the pointwise identity (all terms continuous with compact support).

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
