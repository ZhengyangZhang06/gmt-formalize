# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1.covector_det_expansion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent Step 2 ('Write ω = Σ_I ω_I dy^{I_1} ∧ ⋯ ∧ dy^{I_k} ... Then H^#ω(u)(e) = Σ_I ω_I(H(u))·det D(H^I)(u) (multilinearity and alternation of dy^I ∘ DH(u))'), stated pointwise for one covector f (the parent uses f = ω(H(u)) and u_b = DH(u)e_b) and summed over all index maps I instead of increasing ones; each increasing I then occurs k! times, which produces the factor k!.

Notation. ℝ^{N'} = Euclid N'; e'_i := EuclideanSpace.single i 1 (i ∈ Fin N'); z(i) (Lean z i) is the i-th coordinate of z ∈ ℝ^{N'}. For I : Fin k → Fin N' put e'_I := (e'_{I(0)}, …, e'_{I(k−1)}) and let M_I be the k×k matrix with (M_I)_{c,b} = u_b(I(c)).

1. (Basis expansion.) Every z ∈ ℝ^{N'} satisfies z = Σ_{i ∈ Fin N'} z(i)·e'_i (the standard basis EuclideanSpace.basisFun has the coordinates as its repr; Basis.sum_repr). In particular u_b = Σ_i u_b(i)·e'_i for every b.
2. (Multilinear expansion.) f is multilinear, so (MultilinearMap.map_sum) f(u) = f(Σ_i u_0(i)e'_i, …, Σ_i u_{k−1}(i)e'_i) = Σ_{J : Fin k → Fin N'} f(u_0(J 0)·e'_{J 0}, …, u_{k−1}(J(k−1))·e'_{J(k−1)}), and pulling out the scalars (MultilinearMap.map_smul_univ) each summand equals (Π_b u_b(J b))·f(e'_J). Hence f(u) = Σ_J (Π_b u_b(J b))·f(e'_J).
3. (Reindexing by a permutation.) Fix σ ∈ Perm(Fin k). The map I ↦ I ∘ σ is a bijection of the finite set of maps Fin k → Fin N' (inverse J ↦ J ∘ σ⁻¹; Lean Equiv.arrowCongr σ⁻¹ (Equiv.refl _)). Substituting J = I ∘ σ in step 2: f(u) = Σ_I (Π_b u_b(I(σ b)))·f(e'_{I(σ 0)}, …, e'_{I(σ(k−1))}).
4. (Alternation.) The family (e'_{I(σ b)})_b is the family e'_I composed with σ, and an alternating map satisfies f(v ∘ σ) = sign(σ)·f(v) (AlternatingMap.map_perm). Hence, for every σ, f(u) = Σ_I sign(σ)·(Π_b u_b(I(σ b)))·f(e'_I).
5. (Averaging.) Perm(Fin k) has k! elements (Fintype.card_perm). Summing step 4 over all σ and exchanging the two finite sums: k!·f(u) = Σ_σ f(u) = Σ_I f(e'_I)·Σ_σ sign(σ)·Π_b u_b(I(σ b)).
6. (Leibniz formula.) By Matrix.det_apply, det M_I = Σ_σ sign(σ)·Π_b (M_I)_{σ(b), b} = Σ_σ sign(σ)·Π_b u_b(I(σ b)). Substituting into step 5 gives k!·f(u) = Σ_I f(e'_I)·det M_I, the claim.
7. (Degenerate cases.) Steps 1–6 use neither k ≥ 1 nor N' ≥ 1. For k = 0 there is exactly one I (the empty map), 0! = 1, the empty determinant is 1 and f(e'_I) = f(u) (both arguments are the empty family). For N' = 0 < k the right side is an empty sum and step 2 gives f(u) = 0.

Lean realization (compiled during decomposition with the pinned toolchain in the Submission layout, inside namespace GMT.Ch07 after the contract's open commands; #print axioms: propext, Classical.choice, Quot.sound; no extra import):
```lean
theorem Submission.dor_lmb_fcd_jwc_covector_det_expansion : (∀ (N' k : ℕ) (f : Covector (Euclid N') k) (u : Fin k → Euclid N'), (k.factorial : ℝ) * f u = ∑ I : Fin k → Fin N', f (fun c => EuclideanSpace.single (I c) (1 : ℝ)) * Matrix.det (Matrix.of fun c b => u b (I c))) := by
  intro N' k f u
  set e : Fin N' → Euclid N' := fun i => EuclideanSpace.single i (1 : ℝ) with he
  -- step 1: multilinear expansion in the standard basis
  have h1 : f u = ∑ J : Fin k → Fin N', (∏ b, u b (J b)) * f (fun b => e (J b)) := by
    have hu : u = fun b => ∑ i, u b i • e i := by
      funext b
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N') ℝ).sum_repr (u b)]
      simp [he]
    conv_lhs => rw [hu]
    rw [show f (fun b => ∑ i, u b i • e i) = f.toMultilinearMap (fun b => ∑ i, u b i • e i) from rfl,
      MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [MultilinearMap.map_smul_univ]
    simp [smul_eq_mul]
  -- step 2: reindex by a permutation σ, using alternation
  have h2 : ∀ σ : Equiv.Perm (Fin k), f u = ∑ I : Fin k → Fin N',
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ b, u b (I (σ b))) * f (fun c => e (I c)) := by
    intro σ
    rw [h1]
    rw [← Equiv.sum_comp ((σ.symm).arrowCongr (Equiv.refl (Fin N')))]
    refine Finset.sum_congr rfl fun I _ => ?_
    have hperm : f (fun b => e (I (σ b))) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * f (fun c => e (I c)) := by
      have := f.toAlternatingMap.map_perm (fun c => e (I c)) σ
      simp only [Function.comp_def] at this
      rw [show f (fun b => e (I (σ b))) = f.toAlternatingMap (fun b => e (I (σ b))) from rfl, this,
        Units.smul_def, zsmul_eq_mul]
      rfl
    simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Equiv.symm_symm, Function.comp_apply]
    rw [hperm]
    ring
  -- step 3: average over σ and recognize the Leibniz formula
  have h3 : (k.factorial : ℝ) * f u = ∑ σ : Equiv.Perm (Fin k), f u := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [h3]
  calc ∑ σ : Equiv.Perm (Fin k), f u
      = ∑ σ : Equiv.Perm (Fin k), ∑ I : Fin k → Fin N',
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ b, u b (I (σ b))) * f (fun c => e (I c)) :=
        Finset.sum_congr rfl fun σ _ => h2 σ
    _ = ∑ I : Fin k → Fin N', ∑ σ : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ b, u b (I (σ b))) * f (fun c => e (I c)) :=
        Finset.sum_comm
    _ = _ := ?_
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Matrix.det_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  simp only [Matrix.of_apply, he]
  ring
```

## Key steps

1. Expand each u_b in the standard basis and use multilinearity: f(u) = Σ_J (Π_b u_b(J b))·f(e'_J).
2. For each permutation σ reindex J = I ∘ σ and use alternation f(v ∘ σ) = sign(σ) f(v).
3. Average over the k! permutations and exchange the finite sums.
4. Recognize Σ_σ sign(σ) Π_b u_b(I(σ b)) as det(u_b(I_c))_{c,b} by the Leibniz formula.

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
