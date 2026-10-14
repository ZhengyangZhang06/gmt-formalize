# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1.smooth_minor_ibp-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent Step 4: 'Expansion of μ along its first row a := a_1: μ(Dv) = Σ_{b=1}^r (−1)^{b+1} ∂_{l_b}v^a · μ_b(Dv) ... For smooth v the Piola identity ... holds ..., so μ(Dv) = Σ_b (−1)^{b+1}∂_{l_b}(v^a μ_b(Dv)) ..., and integrating by parts (∗) ∫ψ μ(Dv) = −Σ_b (−1)^{b+1}∫ ∂_{l_b}ψ · v^a · μ_b(Dv) for ψ ∈ C_c^∞.' Rows and columns are indexed from 0 here, so (−1)^{b+1} (b = 1, …, r) becomes (−1)^b (b = 0, …, r); the rows are g_0, …, g_r (g_0 plays v^a), the columns are arbitrary directions V_b, and ψ only needs to be C¹. Uses the sibling piola_identity.

Notation: λ = Lebesgue measure; D = fderiv ℝ; ∂_W F(x) := DF(x)W; A and M_b as in the statement.

1. (Laplace expansion along row 0; Matrix.det_succ_row_zero.) det A(x) = Σ_{b=0}^{r} (−1)^b·A(x)_{0,b}·det(A(x) without row 0 and column b) = Σ_b (−1)^b·∂_{V_b}g_0(x)·M_b(x), since deleting row 0 and column b of A(x) leaves the matrix (∂_{V_{s_b(b')}} g_{c+1}(x))_{c,b'}.
2. (Regularity.) Each entry y ↦ ∂_W g_c(y) = Dg_c(y)W is C¹ because g_c is C² (ContDiff.fderiv_right). The determinant is a polynomial in the entries (Leibniz formula: a finite sum of ± products of entries), so every M_b is C¹. Consequently F_b := ψ·g_0·M_b is C¹ and has compact support (its support lies in that of ψ).
3. (Product rule.) ∂_{V_b}F_b = ∂_{V_b}ψ·g_0·M_b + ψ·∂_{V_b}g_0·M_b + ψ·g_0·∂_{V_b}M_b.
4. (Piola.) The sibling piola_identity applied to the C² functions g_1, …, g_r (i.e. c ↦ g_{c+1}, c ∈ Fin r) and the directions V_0, …, V_r gives Σ_b (−1)^b·∂_{V_b}M_b(x) = 0 for every x.
5. (Pointwise identity.) Multiply step 3 by (−1)^b and sum over b. The middle terms give ψ·Σ_b (−1)^b ∂_{V_b}g_0·M_b = ψ·det A by step 1, and the last terms give ψ·g_0·Σ_b (−1)^b ∂_{V_b}M_b = 0 by step 4. Hence, for every x, ψ(x)·det A(x) = Σ_b (−1)^b ∂_{V_b}F_b(x) − Σ_b (−1)^b ∂_{V_b}ψ(x)·g_0(x)·M_b(x).
6. (Exact derivatives integrate to zero.) Let F be C¹ with compact support and W ∈ ℝᵏ. F is Lipschitz (ContDiff.lipschitzWith_of_hasCompactSupport). Mathlib's integration by parts for Lipschitz functions (LipschitzWith.integral_lineDeriv_mul_eq) applied to the constant function 1 (Lipschitz, with zero line derivative), the compactly supported Lipschitz F and the direction −W gives 0 = ∫ (line derivative of F in direction W)·1 dλ; as F is differentiable, that line derivative is DF(·)W (DifferentiableAt.lineDeriv_eq_fderiv). Thus ∫ ∂_W F dλ = 0.
7. (Integration.) Every function in step 5 is continuous with compact support (Dψ is continuous since ψ is C¹ and vanishes outside the support of ψ; ∂_{V_b}F_b is continuous since F_b is C¹ and vanishes outside the support of F_b), hence integrable. Integrating step 5 and using linearity and step 6 for each F_b: ∫ψ·det A dλ = 0 − Σ_b (−1)^b ∫ ∂_{V_b}ψ·g_0·M_b dλ, which is the claim.

Lean realization (compiled during decomposition with the pinned toolchain in the Submission layout, inside namespace GMT.Ch07; uses Submission.dor_lmb_fcd_jwc_piola_identity; #print axioms: propext, Classical.choice, Quot.sound; no extra import):
```lean
theorem Submission.dor_lmb_fcd_jwc_smooth_minor_ibp : (∀ (k r : ℕ) (g : Fin (r + 1) → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (ψ : Euclid k → ℝ), (∀ c, ContDiff ℝ 2 (g c)) → ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) = -∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * ∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b')))) := by
  intro k r g V ψ hg hψ hψs
  -- the determinant of a C¹ matrix-valued map is C¹ (Leibniz formula)
  have hdetC1 : ∀ {m : ℕ} (A : Euclid k → Fin m → Fin m → ℝ), (∀ i j, ContDiff ℝ 1 (fun x => A x i j)) →
      ContDiff ℝ 1 (fun x => Matrix.det (Matrix.of (A x))) := by
    intro m A hA
    have : (fun x => Matrix.det (Matrix.of (A x))) =
        fun x => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A x (σ i) i := by
      funext x
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Units.smul_def, zsmul_eq_mul]
      simp [Matrix.of_apply]
    rw [this]
    exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hA _ _)
  have hentry : ∀ c (v : Euclid k), ContDiff ℝ 1 (fun x => fderiv ℝ (g c) x v) := fun c v =>
    ((hg c).fderiv_right (by norm_num)).clm_apply contDiff_const
  set M : Fin (r + 1) → Euclid k → ℝ := fun b x => Matrix.det (Matrix.of fun (c b' : Fin r) =>
    fderiv ℝ (g c.succ) x (V (b.succAbove b'))) with hM
  have hMC1 : ∀ b, ContDiff ℝ 1 (M b) := fun b =>
    hdetC1 (fun x c b' => fderiv ℝ (g c.succ) x (V (b.succAbove b'))) (fun c b' => hentry _ _)
  -- ∫ ∂_v F = 0 for C¹ compactly supported F
  have hIBP0 : ∀ F : Euclid k → ℝ, ContDiff ℝ 1 F → HasCompactSupport F → ∀ v,
      ∫ x, fderiv ℝ F x v = 0 := by
    intro F hF hFs v
    obtain ⟨C, hFL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hFs hF (by norm_num)
    have h := LipschitzWith.integral_lineDeriv_mul_eq (μ := (volume : Measure (Euclid k)))
      (LipschitzWith.const (1 : ℝ)) hFL hFs (-v)
    have h0 : ∀ x : Euclid k, lineDeriv ℝ (fun _ : Euclid k => (1 : ℝ)) x (-v) = 0 := by
      intro x
      rw [(differentiableAt_const (1 : ℝ)).lineDeriv_eq_fderiv]
      simp
    have h1 : ∀ x, lineDeriv ℝ F x v = fderiv ℝ F x v := fun x =>
      (hF.differentiable (by norm_num) x).lineDeriv_eq_fderiv
    simp only [h0, zero_mul, integral_zero, neg_neg, mul_one, h1] at h
    exact h.symm
  -- product rule
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
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Pi.mul_apply]
    ring
  -- pointwise identity: ψ det = Σ (-1)^b ∂_b(ψ g₀ M_b) − Σ (-1)^b ∂_bψ g₀ M_b
  have hpt : ∀ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) =
      ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b) -
        ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * (fderiv ℝ ψ x (V b) * g 0 x * M b x) := by
    intro x
    have hp := Submission.dor_lmb_fcd_jwc_piola_identity k r (fun c => g c.succ) V x
      (fun c => hg c.succ)
    simp_rw [hdiff]
    have halg : ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * (fderiv ℝ ψ x (V b) * g 0 x * M b x +
          ψ x * fderiv ℝ (g 0) x (V b) * M b x + ψ x * g 0 x * fderiv ℝ (M b) x (V b)) -
        ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * (fderiv ℝ ψ x (V b) * g 0 x * M b x) =
        ψ x * ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (g 0) x (V b) * M b x +
          ψ x * g 0 x * ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (M b) x (V b) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [halg]
    have hp' : ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (M b) x (V b) = 0 := hp
    rw [hp', mul_zero, add_zero, Matrix.det_succ_row_zero]
    congr 1
  -- integrability
  have hψc : Continuous ψ := hψ.continuous
  have hdψc : ∀ b, Continuous (fun x => fderiv ℝ ψ x (V b)) := fun b =>
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψs : ∀ b, HasCompactSupport (fun x => fderiv ℝ ψ x (V b)) := fun b =>
    (hψs.fderiv (𝕜 := ℝ)).comp_left (g := fun T : Euclid k →L[ℝ] ℝ => T (V b)) (by simp)
  have hFC1 : ∀ b, ContDiff ℝ 1 (fun y => ψ y * g 0 y * M b y) := fun b =>
    (hψ.mul ((hg 0).of_le (by norm_num))).mul (hMC1 b)
  have hFs : ∀ b, HasCompactSupport (fun y => ψ y * g 0 y * M b y) := fun b =>
    (hψs.mul_right).mul_right
  have hi1 : ∀ b : Fin (r + 1), Integrable (fun x => (-1 : ℝ) ^ (b : ℕ) *
      fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b)) := by
    intro b
    refine Integrable.const_mul ?_ _
    exact (((hFC1 b).continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (((hFs b).fderiv (𝕜 := ℝ)).comp_left (g := fun T : Euclid k →L[ℝ] ℝ => T (V b)) (by simp))
  have hi2 : ∀ b : Fin (r + 1), Integrable (fun x => (-1 : ℝ) ^ (b : ℕ) * (fderiv ℝ ψ x (V b) * g 0 x * M b x)) := by
    intro b
    refine Integrable.const_mul ?_ _
    exact (((hdψc b).mul ((hg 0).continuous)).mul (hMC1 b).continuous).integrable_of_hasCompactSupport
      ((hdψs b).mul_right.mul_right)
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  rw [integral_sub (integrable_finsetSum _ fun b _ => hi1 b) (integrable_finsetSum _ fun b _ => hi2 b),
    integral_finsetSum _ fun b _ => hi1 b, integral_finsetSum _ fun b _ => hi2 b]
  have hz : ∑ b : Fin (r + 1), ∫ x, (-1 : ℝ) ^ (b : ℕ) *
      fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b) = 0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [integral_const_mul, hIBP0 _ (hFC1 b) (hFs b), mul_zero]
  rw [hz, zero_sub]
  simp only [integral_const_mul]
  rfl
```

## Key steps

1. Laplace expansion along row 0: det A = Σ_b (−1)^b ∂_{V_b}g_0·M_b.
2. The minors M_b are C¹, so F_b := ψ g_0 M_b is C¹ with compact support; product rule for ∂_{V_b}F_b.
3. Piola (sibling piola_identity): Σ_b (−1)^b ∂_{V_b}M_b = 0, giving ψ det A = Σ_b (−1)^b ∂_{V_b}F_b − Σ_b (−1)^b ∂_{V_b}ψ g_0 M_b pointwise.
4. ∫ ∂_W F = 0 for C¹ compactly supported F (Lipschitz integration by parts against the constant 1); integrate.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `python3 -I parse of nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-f189b35d70/parent-child-handoff.json and cat parent-supplied-plan.md (frozen type, empty sibling prerequisites)`
- `sed -n 1,140p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean; sed -n 60,160p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean (Covector = E [Wedge^Fin n]->L ℝ, DifferentialForm = E -> Covector, TestFormOn U n = testFormOnSubmodule: IsTestForm (ContDiff ∞ and HasCompactSupport) and tsupport ⊆ U)`
- `python3 -I scans of dag.json (1744 nodes): regex mollif|convolution|ContDiffBump|Piola|null Lagrang|Jacobian minor|weak continuity|lineDeriv|Rademacher|Matrix.det|minor|dense|weak-*; printed statuses and frozen types of cmcs_lipschitz_smoothing, cmcs_ls_mollify_lipschitz, cmr_cc_det_covector_exists, dgcr_stc_exists_normalized_mollifier, dor_ims_sua_mollify_unit_field, dor_lmbsf_pwl_fderiv_weak_integrable, cbr_ci_cp_pr_factorial_mul_eq_sum_det, cbr_ci_cp_tr_smooth_approx_of_continuous, codim1_rdo_dg_bvc_smooth_indicator_approx, regcomp_exists_continuous_unit_form_approx; siblings under deformation-a1; grep dor_lmb_fcd_jwc in dag.json and rg dor_lmb_fcd_jwc in the snapshot project (no match: names fresh)`
- `git show 00c458d8b5f0043b634cbdd0b8d43d20d1d7deb6:GMT/Ch07/Submission.lean and git show fee01ff86c9de6b32f7cfc6b3f5088750ef5af7e:GMT/Ch07/Submission.lean (accepted proofs of cmcs_ls_mollify_lipschitz and cmr_cc_det_covector_exists); python3 -I import scan of accepted candidate commits (accepted nodes add Mathlib imports such as ContinuousMapDense, BumpFunction.SmoothApprox)`
- `lake env lean /tmp/jwc-decomp-k7q2/Avail*.lean: #check in the import closure of GMT.Ch07.Submission (present: LipschitzWith.ae_differentiableAt, LipschitzWith.integral_lineDeriv_mul_eq, measurable_fderiv, HasCompactSupport.contDiff_convolution_left, HasCompactSupport.hasFDerivAt_convolution_left, dist_convolution_le, extDeriv_pullback, extDeriv_apply, extDeriv_extDeriv_apply, Matrix.det_succ_row_zero, MultilinearMap.map_sum, Integrable.induction, IsUnifLocDoublingMeasure.ae_tendsto_average; absent without extra imports: ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, ContDiffBump.normed, Integrable.exists_hasCompactSupport_integral_sub_le, Matrix.det_le, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable)`
- `rg -n in snapshot mathlib: theorem ae_convolution_tendsto_right_of_locallyIntegrable (Analysis/Calculus/BumpFunction/Convolution.lean:103), theorem exist_eLpNorm_sub_le (Analysis/Normed/Lp/SmoothApprox.lean:87), theorem det_le (LinearAlgebra/Matrix/AbsoluteValue.lean:43), theorem extDeriv_pullback (Analysis/Calculus/DifferentialForm/Basic.lean:259), DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap (Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:137), alternatizeUncurryFinCLM_apply (Analysis/Normed/Module/Alternating/Uncurry/Fin.lean:129), precompL_apply (Analysis/Normed/Operator/Bilinear.lean:379), Continuous.exists_contDiff_approx (Geometry/Manifold/SmoothApprox.lean:132), Integrable.exists_hasCompactSupport_integral_sub_le (MeasureTheory/Function/ContinuousMapDense.lean:226)`
- `sed -n 1,28p, 300,372p, 580,660p verifier/gmt-compare.py (child challenge = import GMT.Ch07.Submission + contract scope replay; new Lean files allowed only under GMT/Ch07); verifier/lean_contract.py validate_lean_statement; runtime.py _existing_lean_name_problem (accepted declarations reusable only with identical frozen type) and _decompose (depth >= max_depth stops splitting)`
- `lake env lean /tmp/jwc-decomp-k7q2/lean/Chal_*.lean (12 exact comparator challenges), AllProps.lean, ParentAssembly.lean, E3Assembly.lean, C3Assembly.lean, C4bAssembly.lean, C4aAssembly.lean, B2Assembly.lean, H0Proof.lean, E2Proof.lean, C1Proof.lean, B1Proof.lean, AllProofs.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-f189b35d70/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-f189b35d70/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-e358a4c0e4/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-coo-498906c61d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-lipschitz-smoot-0c46a16452/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/tmp/jwc-decomp-k7q2/lean/AllProofs.lean`
- `/tmp/jwc-decomp-k7q2/lean/ParentAssembly.lean`

Snapshot: project b4d606db, mathlib 25730c7c; the snapshot Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Neither the snapshot project nor SimonGMT contains weak continuity of Jacobian minors, a Piola identity, or a Lipschitz mollification lemma with a.e. derivative convergence (SimonGMT Chapter06 gives the Covector/DifferentialForm/TestFormOn objects and d^2 = 0 / pull-back naturality on open domains). Pinned Mathlib supplies every tool used by the child proofs: Rademacher (LipschitzWith.ae_differentiableAt), Lipschitz integration by parts (LipschitzWith.integral_lineDeriv_mul_eq), convolution differentiation and smoothness, extDeriv_pullback/extDeriv_apply, Laplace expansion, and, with an extra import, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, MemLp.exist_eLpNorm_sub_le and Matrix.det_le. Reuse: cmr_cc_det_covector_exists and cmcs_ls_mollify_lipschitz are comparator-accepted with byte-identical frozen types and are reused as siblings; the other nine dor_lmb_fcd_jwc_* names are fresh. Lean: the 12 types compile as exact comparator challenges; the parent and all internal dependencies were proved from their listed siblings, the leaves were proved, and a combined file with all 12 declarations compiles with axioms [propext, Classical.choice, Quot.sound].
