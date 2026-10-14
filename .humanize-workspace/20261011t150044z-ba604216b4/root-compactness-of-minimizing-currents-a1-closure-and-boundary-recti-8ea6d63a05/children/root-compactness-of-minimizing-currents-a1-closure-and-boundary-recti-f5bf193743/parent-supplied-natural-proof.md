# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.cone-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.cone-a1.cycle_const-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5 and 7 of the parent proof (cut-off, and 'constant forms are boundaries near spt X'). Here the cut-off is taken at inner radius r, and the parent's test form ζα is replaced by any test form φ that equals α on B_r(x₀). The (VO)-localization of parent step 6 is the sibling localize, and the identity dψ = α is the sibling affine_primitive.

Notation. B_r(x₀) is the open ball and B̄_r(x₀) the closed ball. For an n-form g, dg = extDeriv g. For η ∈ TestFormOn univ n, exteriorDerivativeTestOn univ n η ∈ TestFormOn univ (n+1) is the test form whose underlying form is extDeriv η.

1. (Cut-off.) Let ζ : ℝ^P → ℝ be Mathlib's smooth bump function (ContDiffBump) centred at x₀ with inner radius rIn := r and outer radius rOut := r + 1; this is allowed because 0 < r < r + 1. Then ζ is C^∞ (ContDiffBump.contDiff) and has compact support (ContDiffBump.hasCompactSupport; ℝ^P is finite-dimensional). Moreover ζ(z) = 1 for every z ∈ B̄_r(x₀) (ContDiffBump.one_of_mem_closedBall), hence for every z ∈ B_r(x₀) (ball_subset_closedBall).

2. (The primitive.) Let ψ(y) := ((n : ℝ) + 1)⁻¹ · α.curryLeft(y − x₀), an n-form. ψ is C^∞: it is the continuous linear map α.curryLeft composed with the smooth map y ↦ y − x₀, multiplied by a constant (ContinuousLinearMap.contDiff, ContDiff.comp, contDiff_id.sub contDiff_const, ContDiff.const_smul). By the sibling affine_primitive, extDeriv ψ y = α for every y ∈ ℝ^P.

3. (A compactly supported primitive.) Let g(y) := ζ(y) · ψ(y). g is C^∞ (ContDiff.smul applied to steps 1 and 2), and it has compact support because ζ does (HasCompactSupport.smul_right). So g is a test form with tsupport g ⊆ ℝ^P = univ, and hence η := g ∈ TestFormOn univ n.

4. (∂X = 0 kills dη.) Let dη := exteriorDerivativeTestOn univ n η; its underlying form is extDeriv g. By the definition of the boundary (GeometricCurrentOn.boundary_apply), X(dη) = (∂X)(η). Since ∂X = 0, X(dη) = 0(η) = 0.

5. (φ = dη on the ball.) Let y ∈ B_r(x₀). The open ball B_r(x₀) is a neighbourhood of y (isOpen_ball.mem_nhds). For z in it ζ(z) = 1 (step 1), so g(z) = ψ(z); thus g =ᶠ[𝓝 y] ψ. The exterior derivative at y depends only on the germ at y (Filter.EventuallyEq.extDeriv_eq), so extDeriv g y = extDeriv ψ y = α by step 2. By hypothesis φ(y) = α. Hence φ(y) = (dη)(y) for every y ∈ B_r(x₀).

6. (Localization.) B_r(x₀) is open, spt X ⊆ B_r(x₀) by hypothesis, and by step 5 the forms φ, dη ∈ TestFormOn univ (n+1) agree on B_r(x₀). The sibling localize, applied with (VO), P, k := n + 1, U := univ, G := B_r(x₀), X, φ₁ := φ and φ₂ := dη, gives X(φ) = X(dη). By step 4, X(dη) = 0. Hence X(φ) = 0. ∎

Lean note (this exact proof compiled against the pinned snapshot in a scratch file, using only the two siblings; axioms propext, Classical.choice, Quot.sound only):
  intro VO P n X x₀ r α φ hr hbd hspt hφ
  let ζ : ContDiffBump x₀ := ⟨r, r + 1, hr, by linarith⟩
  let ψ : DifferentialForm (Euclid P) n := fun y => ((n : ℝ) + 1)⁻¹ • α.curryLeft (y - x₀)
  have hψ : IsSmoothForm ψ :=
    (α.curryLeft.contDiff.comp (contDiff_id.sub contDiff_const)).const_smul _
  let g : DifferentialForm (Euclid P) n := fun y => ζ y • ψ y
  have hg : IsSmoothForm g := ζ.contDiff.smul hψ
  have hgc : HasCompactSupport g := ζ.hasCompactSupport.smul_right
  let η : TestFormOn (univ : Set (Euclid P)) n := ⟨g, ⟨hg, hgc⟩, subset_univ _⟩
  have h0 : X (exteriorDerivativeTestOn univ n η) = 0 := by
    have h := congrArg (fun T : GeometricCurrentOn (univ : Set (Euclid P)) n => T η) hbd
    simpa using h
  have heq : EqOn (φ : DifferentialForm (Euclid P) (n + 1))
      ((exteriorDerivativeTestOn univ n η : TestFormOn (univ : Set (Euclid P)) (n + 1)) :
        DifferentialForm (Euclid P) (n + 1)) (ball x₀ r) := by
    intro y hy
    rw [hφ y hy]
    change α = extDeriv g y
    have hev : g =ᶠ[𝓝 y] ψ := by
      filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      simp [g, ζ.one_of_mem_closedBall (ball_subset_closedBall hz)]
    rw [hev.extDeriv_eq, Submission.cbrld_cone_extDeriv_affine_contraction P n α x₀ y]
  rw [Submission.cbrld_cone_eval_eq_of_eqOn_open VO P (n + 1) univ (ball x₀ r) X φ _ isOpen_ball hspt heq, h0]

## Key steps

1. Bump ζ (ContDiffBump at x₀, rIn = r, rOut = r + 1): smooth, compactly supported, ζ = 1 on B_r(x₀).
2. ψ(y) = (n+1)⁻¹ α.curryLeft(y − x₀) is smooth with dψ = α (affine_primitive); η := ζψ is a test n-form.
3. ∂X = 0 gives X(dη) = ∂X(η) = 0.
4. On the open ball ζψ = ψ, so dη = dψ = α = φ there (EventuallyEq.extDeriv_eq).
5. localize with G = B_r(x₀) ⊇ spt X gives X(φ) = X(dη) = 0.

## Reference use

### local-project

Queries:
- `python3 -I json parse of the selected node's parent-child-handoff.json (subproblem, audit, resolved_dependencies) and cat parent-supplied-plan.md`
- `cat manifest.json of local-references/123e8435b4a2469b (project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sed/cat of SimonGMT Chapter06 Forms.lean, Currents.lean, Mass.lean, FormSupNorm.lean, CurrentLocalEquality.lean: IsSmoothForm, IsTestForm, testFormOnSubmodule, TestFormOn, GeometricCurrentOn, exteriorDerivativeTestOn, GeometricCurrentOn.boundary_apply, zero_apply, covectorEuclideanNorm(_neg,_nonneg), massAdmissibleOn, massOn, le_massOn, mass, VanishesOn, zeroRegion, support`
- `python3 -I scans of dag.json lean_statement: covectorEuclideanNorm / le_massOn / massOn-bound patterns (found accepted cmr_abs_apply_le_massOn, rsd_mw_tfa_norm_props, regcomp_covectorEuclideanNorm_seminorm_retract); regex curryLeft | extDeriv | EqOn.*support | covectorEuclideanNorm(..-..) ≤ ..dist | boundary = 0.*ball (no statement equal to the four new children; closest accepted dtc_cone_euler_cartan); status of dtc_vanish_off_support (accepted); collision check of cbrld_cone_testForm_coeff_lipschitz, cbrld_cone_extDeriv_affine_contraction, cbrld_cone_eval_eq_of_eqOn_open, cbrld_cone_cycle_eval_eq_zero_of_const_on_ball against 940 DAG lean names (none); count of existing cross-branch child reuses (232)`
- `git show 7a706164baaf42fc7f55751247396a8836928310:GMT/Ch07/Submission.lean and f492ba4a003c8f1324077e050d48667ae23c7100:GMT/Ch07/Submission.lean (accepted proofs of the reused declarations); python3 -I read of their parent-child-handoff.json (accepted natural proofs)`
- `grep -n _existing_lean_name_problem, _accepted_checkpoint, existing_by_name, _install_parent_supplied_child_handoff, _dependency_problem in runtime.py; grep -n 'def ensure' -A 40 store.py`
- `grep in the Mathlib snapshot: def curryLeft, curryLeft_apply_apply, alternatizeUncurryFin_curryLeft, alternatizeUncurryFin_smul, def extDeriv, Filter.EventuallyEq.extDeriv_eq, structure ContDiffBump, one_of_mem_closedBall, zero_of_le_dist, nonneg, le_one, ContDiffBump.hasCompactSupport, ContDiffBump.contDiff, norm_image_sub_le_of_norm_fderiv_le, lipschitzWith_of_nnnorm_fderiv_le, HasCompactSupport.fderiv, HasCompactSupport.smul_right, ContDiff.continuous_fderiv, Continuous.bounded_above_of_compact_support, ContinuousAlternatingMap.le_opNorm`
- `rg -n 'curryLeft|extDeriv|LipschitzWith|ContDiffBump|cone' <snapshot>/project --glob '*.lean'; rg -c covectorEuclideanNorm <snapshot>/project --glob '*.lean'`
- `sed -n 520,552p and 2376,2400p book/chapter-06.txt (Simon Ch. 6, 2.25-2.32 homotopy formula and cone; 8.2 use of 2.27/2.30)`
- `lake env lean /tmp/cbrld-cone-decomp-k7/{Types,Assembly,Fix,EndToEnd}.lean and /tmp/cbrld-cone-decomp-k7/challenges/*_Challenge.lean (generated by verifier/gmt-compare.py child_modules, contract mode); python3 -I validate.py calling verifier/lean_contract.py validate_lean_statement`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-8ea6d63a05/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-8ea6d63a05/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-norm-props-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cbrld-cone-decomp-k7/Types.lean`
- `/tmp/cbrld-cone-decomp-k7/Assembly.lean`
- `/tmp/cbrld-cone-decomp-k7/Fix.lean`
- `/tmp/cbrld-cone-decomp-k7/EndToEnd.lean`
- `/tmp/cbrld-cone-decomp-k7/challenges/T_coeff_lipschitz_Challenge.lean`
- `/tmp/cbrld-cone-decomp-k7/challenges/T_affine_primitive_Challenge.lean`
- `/tmp/cbrld-cone-decomp-k7/challenges/T_localize_Challenge.lean`
- `/tmp/cbrld-cone-decomp-k7/challenges/T_cycle_const_Challenge.lean`
- `/tmp/cbrld-cone-decomp-k7/challenges/T_mass_eval_Challenge.lean`
- `/tmp/cbrld-cone-decomp-k7/challenges/T_norm_props_Challenge.lean`

The snapshot project has no cone inequality, no coefficient-norm Lipschitz bound for test forms, no explicit primitive of a constant form and no support-localization lemma. rg over project/GMT found only unrelated Ch02 LipschitzWith statements and Ch07 tangent-cone definitions, and no use of curryLeft, extDeriv or ContDiffBump. SimonGMT Chapter06 supplies only the current/test-form/mass/support/boundary definitions, together with le_massOn, boundary_apply and covectorEuclideanNorm_neg/_nonneg. Two accepted DAG declarations match parent steps 1-3 with byte-identical frozen types and are reused: cmr_abs_apply_le_massOn (candidate 7a706164) and rsd_mw_tfa_norm_props (candidate f492ba4a). The runtime reuses accepted checkpoints by identical Lean name and type, and returns existing nodes unchanged. No DAG node states any of the four new children. The closest is the accepted dtc_cone_euler_cartan, which would need extra translation and constant-form steps. Mathlib supplies every tool the child proofs cite: alternatizeUncurryFin_curryLeft and alternatizeUncurryFin_smul, extDeriv and EventuallyEq.extDeriv_eq, ContDiffBump, the mean value inequality, HasCompactSupport.fderiv and smul_right, and Continuous.bounded_above_of_compact_support. The last one needs an explicit (f := ...) argument, otherwise elaboration hits a whnf timeout. All six child types elaborate in the comparator's own generated challenge files and pass the lexical validator. A scratch Lean development proves the exact selected frozen type from the six children, and each new child from its declared siblings, using only the axioms propext, Classical.choice and Quot.sound. None of the four new names collides with the 940 DAG names.
