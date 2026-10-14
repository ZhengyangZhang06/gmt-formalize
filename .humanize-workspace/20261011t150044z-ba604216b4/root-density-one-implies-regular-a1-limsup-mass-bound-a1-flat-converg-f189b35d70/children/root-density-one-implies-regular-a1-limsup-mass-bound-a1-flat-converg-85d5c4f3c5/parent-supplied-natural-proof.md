# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1.minor_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent Notation paragraph ('u ↦ DH(u) is measurable (Mathlib measurable_fderiv), so all integrands below are measurable, and they are bounded') and Steps 2–4 ('|det D(H_j^I)| ≤ L^k a.e.', 'Since |μ(Dv_j)| ≤ r!L^r uniformly'), stated for arbitrary directions V_b and everywhere (fderiv is 0 at non-differentiability points).

Notation: ∂_W g(x) := Dg(x)W with Dg(x) := fderiv ℝ g x; D(x) := det(∂_{V_b} g_c(x))_{c,b ∈ Fin r}; s := L·Σ_b ‖V_b‖.

1. (Measurable entries.) For each c, x ↦ Dg_c(x) is Borel measurable from ℝᵏ into the space of continuous linear maps ℝᵏ → ℝ (measurable_fderiv; ℝ is complete). Composing with the continuous evaluation T ↦ T V_b, each entry x ↦ ∂_{V_b} g_c(x) is measurable (measurable_fderiv_apply_const).
2. (Measurability of D.) By the Leibniz formula (Matrix.det_apply) D(x) = Σ_{σ ∈ Perm(Fin r)} sign(σ)·Π_b ∂_{V_b} g_{σ(b)}(x): a finite sum of constants times finite products of the measurable functions of step 1. Hence D is measurable (Finset.measurable_sum, Finset.measurable_prod, Measurable.mul).
3. (Entry bound.) If g is L-Lipschitz then ‖Dg(x)‖ ≤ L for every x (norm_fderiv_le_of_lipschitz; at non-differentiability points Dg(x) = 0). Hence |∂_{V_b} g_c(x)| ≤ ‖Dg_c(x)‖·‖V_b‖ ≤ L‖V_b‖ ≤ L·Σ_{b'} ‖V_{b'}‖ = s, using ‖V_b‖ ≤ Σ_{b'} ‖V_{b'}‖ (all terms nonnegative).
4. (Determinant bound.) If every entry of an r×r real matrix has absolute value at most s, then by the Leibniz formula and the triangle inequality |det| ≤ Σ_σ Π_b s = r!·s^r (Matrix.det_le with the absolute value; card Perm(Fin r) = r!). With step 3, |D(x)| ≤ r!·(L·Σ_b ‖V_b‖)^r for every x. (For r = 0 this reads |1| ≤ 1.)

Lean realization (compiled during decomposition with the pinned toolchain in the Submission layout, inside namespace GMT.Ch07; #print axioms: propext, Classical.choice, Quot.sound; extra import: Mathlib.LinearAlgebra.Matrix.AbsoluteValue, for Matrix.det_le):
```lean
theorem Submission.dor_lmb_fcd_jwc_minor_measurable_bound : (∀ (k r : ℕ) (L : NNReal) (g : Fin r → Euclid k → ℝ) (V : Fin r → Euclid k), (∀ c, LipschitzWith L (g c)) → Measurable (fun x => Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b))) ∧ ∀ x, |Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b))| ≤ (r.factorial : ℝ) * ((L : ℝ) * ∑ b, ‖V b‖) ^ r) := by
  intro k r L g V hg
  constructor
  · -- Leibniz formula: a finite sum of products of measurable entries
    have hent : ∀ c b, Measurable (fun x => fderiv ℝ (g c) x (V b)) := fun c b =>
      measurable_fderiv_apply_const ℝ (g c) (V b)
    have : (fun x => Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b))) =
        fun x => ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ i, fderiv ℝ (g (σ i)) x (V i) := by
      funext x
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Units.smul_def, zsmul_eq_mul]
      simp [Matrix.of_apply]
    rw [this]
    exact Finset.measurable_sum _ fun σ _ =>
      measurable_const.mul (Finset.measurable_prod _ fun i _ => hent _ _)
  · intro x
    have hent : ∀ c b, |Matrix.of (fun c b => fderiv ℝ (g c) x (V b)) c b| ≤ (L : ℝ) * ∑ b, ‖V b‖ := by
      intro c b
      rw [Matrix.of_apply, ← Real.norm_eq_abs]
      calc ‖fderiv ℝ (g c) x (V b)‖ ≤ ‖fderiv ℝ (g c) x‖ * ‖V b‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ L * ‖V b‖ := mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hg c)) (norm_nonneg _)
        _ ≤ L * ∑ b, ‖V b‖ := by
            gcongr
            exact Finset.single_le_sum (f := fun b => ‖V b‖) (fun b _ => norm_nonneg _) (Finset.mem_univ b)
    have := Matrix.det_le (abv := AbsoluteValue.abs) hent
    simpa [Fintype.card_fin, nsmul_eq_mul] using this
```

## Key steps

1. Each entry x ↦ Dg_c(x)V_b is measurable (measurable_fderiv).
2. Leibniz formula: the determinant is a finite signed sum of products of entries, hence measurable.
3. Lipschitz bound ‖Dg_c(x)‖ ≤ L gives |entries| ≤ L·Σ_b‖V_b‖ everywhere.
4. Matrix.det_le: |det| ≤ r!·(L·Σ_b‖V_b‖)^r.

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
