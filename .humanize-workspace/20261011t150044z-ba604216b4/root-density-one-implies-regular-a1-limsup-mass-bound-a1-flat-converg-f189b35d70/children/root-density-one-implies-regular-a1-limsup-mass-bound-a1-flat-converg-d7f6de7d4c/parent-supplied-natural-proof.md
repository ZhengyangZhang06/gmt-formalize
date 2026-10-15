# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1.piola_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent Step 4: 'For smooth v the Piola identity Σ_b (−1)^{b+1} ∂_{l_b}(μ_b(Dv)) = 0 holds (it is the l_1⋯l_r-coefficient of d(dv^{a_2} ∧ ⋯ ∧ dv^{a_r}) = 0, i.e. symmetry of second derivatives)'. Here the rows g_0, …, g_{r−1} are the parent's v^{a_2}, …, v^{a_r}, the columns are arbitrary directions V_0, …, V_r (indexed from 0, so the sign is (−1)^b), and dg_0 ∧ ⋯ ∧ dg_{r−1} is realized as the pull-back G^*θ of the constant determinant form θ = dy^0 ∧ ⋯ ∧ dy^{r−1} by G = (g_0, …, g_{r−1}); then d(G^*θ) = G^*(dθ) = 0, the naturality of d being where the symmetry of the second derivatives of G enters. Uses the sibling det_covector_exists (Submission.cmr_cc_det_covector_exists).

Notation: D = fderiv ℝ; ℝ^r = Euclid r; s_b = Fin.succAbove b; Fin.removeNth b V = V ∘ s_b is the tuple V with V_b deleted.

1. (The map G.) Let G : ℝᵏ → ℝ^r, G(y) := (g_0(y), …, g_{r−1}(y)) (Lean: (EuclideanSpace.equiv (Fin r) ℝ).symm applied to fun c => g c y). G is C², a continuous linear equivalence composed with a map whose components are C² (contDiff_pi). Its derivative is computed componentwise (hasFDerivAt_pi): for all y, w ∈ ℝᵏ and c ∈ Fin r, the c-th coordinate of DG(y)w equals Dg_c(y)w.
2. (Determinant form.) By the sibling det_covector_exists with P = n = r and I = id there is an r-covector θ on ℝ^r with θ(w_0, …, w_{r−1}) = det(w_b(c))_{c,b ∈ Fin r} for all w. Let Θ : ℝ^r → Covector(ℝ^r, r) be the constant form Θ(z) := θ.
3. (Pull-back.) Put β(y) := θ ∘ DG(y), i.e. β(y)(w_0, …, w_{r−1}) = θ(DG(y)w_0, …, DG(y)w_{r−1}) (Lean: (Θ (G y)).compContinuousLinearMap (fderiv ℝ G y)). By steps 1 and 2, β(y)(w) = det(Dg_c(y)w_b)_{c,b}; in particular β(y)(V ∘ s_b) = M_b(y) for every y and b.
4. (dΘ = 0.) Θ is constant, so its derivative vanishes and its exterior derivative dΘ(z), the alternatization of DΘ(z), is 0 (the alternatization is linear: alternatizeUncurryFinCLM).
5. (Naturality of d.) Θ is differentiable and G is C², so Mathlib's extDeriv_pullback gives dβ(x) = dΘ(G(x)) ∘ DG(x), which is 0 by step 4. (The proof of extDeriv_pullback uses the symmetry of the second derivative of G.)
6. (Coordinate formula for d.) β is differentiable at x, since θ is constant and DG is C¹ (DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap). Mathlib's extDeriv_apply gives dβ(x)(V_0, …, V_r) = Σ_{b=0}^{r} (−1)^b·D[y ↦ β(y)(V ∘ s_b)](x)V_b, and by step 3 the functions y ↦ β(y)(V ∘ s_b) are exactly M_b, so dβ(x)(V) = Σ_b (−1)^b·DM_b(x)V_b.
7. (Conclusion.) By step 5 the left side of step 6 is 0, hence Σ_{b=0}^{r} (−1)^b·DM_b(x)V_b = 0. (For r = 0 each M_b is the constant 1 and the identity is trivial; the argument covers this case too.)

Lean realization (compiled during decomposition with the pinned toolchain in the Submission layout, inside namespace GMT.Ch07; uses Submission.cmr_cc_det_covector_exists; #print axioms: propext, Classical.choice, Quot.sound; no extra import):
```lean
theorem Submission.dor_lmb_fcd_jwc_piola_identity : (∀ (k r : ℕ) (g : Fin r → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (x : Euclid k), (∀ c, ContDiff ℝ 2 (g c)) → ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (fun y => Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c) y (V (b.succAbove b')))) x (V b) = 0) := by
  intro k r g V x hg
  -- the map G = (g_0, …, g_{r-1}) : ℝᵏ → ℝʳ
  set e : (Fin r → ℝ) ≃L[ℝ] Euclid r := (EuclideanSpace.equiv (Fin r) ℝ).symm with he
  set G : Euclid k → Euclid r := fun y => e (fun c => g c y) with hG
  have hGc : ContDiff ℝ 2 G := e.contDiff.comp (contDiff_pi.2 hg)
  have hGd : ∀ y w (c : Fin r), fderiv ℝ G y w c = fderiv ℝ (g c) y w := by
    intro y w c
    have hpi : HasFDerivAt (fun y => fun c => g c y)
        (ContinuousLinearMap.pi fun c => fderiv ℝ (g c) y) y :=
      hasFDerivAt_pi.2 fun c => ((hg c).differentiable (by norm_num) y).hasFDerivAt
    have h := (e.hasFDerivAt.comp y hpi)
    rw [show G = e ∘ (fun y => fun c => g c y) from rfl, h.fderiv]
    simp [he]
  obtain ⟨θ, hθ⟩ := Submission.cmr_cc_det_covector_exists r r id
  set Θ : Euclid r → Covector (Euclid r) r := fun _ => θ with hΘ
  have hdΘ : extDeriv Θ (G x) = 0 := by
    simp [extDeriv, hΘ, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
  have hpull := extDeriv_pullback (ω := Θ) (f := G) (x := x) (r := 2) (differentiableAt_const θ)
    hGc.contDiffAt (by simp)
  rw [hdΘ] at hpull
  have hβd : DifferentiableAt ℝ (fun y => (Θ (G y)).compContinuousLinearMap (fderiv ℝ G y)) x :=
    (differentiableAt_const θ).continuousAlternatingMapCompContinuousLinearMap
      ((hGc.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
  have happ := extDeriv_apply hβd V
  rw [hpull] at happ
  have hβ : ∀ i : Fin (r + 1), (fun y => (Θ (G y)).compContinuousLinearMap (fderiv ℝ G y)
      (i.removeNth V)) = fun y => Matrix.det (Matrix.of fun (c b' : Fin r) =>
        fderiv ℝ (g c) y (V (i.succAbove b'))) := by
    intro i
    funext y
    simp only [hΘ, ContinuousAlternatingMap.compContinuousLinearMap_apply, hθ]
    congr 1
    ext c b'
    simp [Matrix.of_apply, Fin.removeNth, hGd]
  simp only [hβ] at happ
  rw [eq_comm] at happ
  simpa [zsmul_eq_mul] using happ
```

## Key steps

1. G := (g_0, …, g_{r−1}) is C² and (DG(y)w)_c = Dg_c(y)w.
2. With the constant determinant form θ (sibling det_covector_exists), β = G^*θ satisfies β(y)(V without V_b) = M_b(y).
3. dθ = 0 for the constant form, so naturality extDeriv_pullback gives dβ(x) = 0.
4. extDeriv_apply expands dβ(x)(V_0, …, V_r) = Σ_b (−1)^b DM_b(x)V_b, which therefore vanishes.

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
