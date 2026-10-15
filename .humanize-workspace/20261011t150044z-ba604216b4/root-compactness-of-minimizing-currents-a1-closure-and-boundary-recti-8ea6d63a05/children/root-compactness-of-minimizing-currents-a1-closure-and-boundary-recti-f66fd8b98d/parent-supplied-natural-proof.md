# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.cone-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.cone-a1.coeff_lipschitz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2 and 4 of the parent proof (the Lipschitz constant c of the fixed test form, measured in the Euclidean coefficient norm), stated for an arbitrary degree k and an arbitrary domain U. The comparison of the coefficient norm with the operator norm (parent step 2) is supplied by part (iii) of the sibling norm_props.

Notation. For a k-covector β (an element of Covector (Euclid P) k, i.e. a continuous alternating k-linear form on ℝ^P), |β| := covectorEuclideanNorm β and ‖β‖ is its operator norm. On ℝ^P, ‖·‖ is the Euclidean norm and dist(x, y) = ‖x − y‖ (dist_eq_norm). Write w := (ω : DifferentialForm (Euclid P) k) : ℝ^P → Covector (Euclid P) k for the underlying form of ω.

1. (Coefficient norm versus operator norm.) By the sibling norm_props, part (iii), applied to (P, k), there is a real C ≥ 0 such that |β| ≤ C·‖β‖ for every k-covector β.

2. (Smoothness.) Membership ω ∈ TestFormOn U k means IsTestForm w ∧ tsupport w ⊆ U, where IsTestForm w = IsSmoothForm w ∧ HasCompactSupport w and IsSmoothForm w = ContDiff ℝ ∞ w. Since the smoothness order ∞ is nonzero, w is differentiable at every point of ℝ^P (ContDiff.differentiable). Its Fréchet derivative Dw := fderiv ℝ w : ℝ^P → (ℝ^P →L[ℝ] Covector (Euclid P) k) is continuous (ContDiff.continuous_fderiv).

3. (The derivative is bounded.) Dw has compact support because w does (HasCompactSupport.fderiv: the support of Dw lies in tsupport w). A continuous map with compact support into a normed space is bounded (Continuous.bounded_above_of_compact_support), so there is L ∈ ℝ with ‖Dw(z)‖ ≤ L for every z ∈ ℝ^P. Put L₀ := max(L, 0). Then L₀ ≥ 0 and ‖Dw(z)‖ ≤ L₀ for every z.

4. (Mean value inequality.) ℝ^P is convex, w is differentiable at every point, and ‖Dw(z)‖ ≤ L₀ for every z. The mean value inequality (Convex.norm_image_sub_le_of_norm_fderiv_le with s = ℝ^P) therefore gives ‖w(x) − w(y)‖ ≤ L₀·‖x − y‖ for all x, y ∈ ℝ^P.

5. (Conclusion.) Put c := C·L₀, which is ≥ 0 as a product of nonnegative reals. For all x, y ∈ ℝ^P, step 1 (applied to β := w(x) − w(y)), step 4 and C ≥ 0 give
   |w(x) − w(y)| ≤ C·‖w(x) − w(y)‖ ≤ C·(L₀·‖x − y‖) = c·‖x − y‖ = c·dist(x, y).
This is the claim. ∎

Lean note (this exact proof compiled against the pinned snapshot in a scratch file; axioms propext, Classical.choice, Quot.sound only). Supplying f explicitly in Continuous.bounded_above_of_compact_support is necessary: without (f := …) elaboration hits a whnf heartbeat timeout.
  intro P k U ω
  obtain ⟨C, hC0, hC⟩ := (Submission.rsd_mw_tfa_norm_props P k).2.2.1
  have hsm : IsSmoothForm (ω : DifferentialForm (Euclid P) k) := ω.property.1.1
  have hcs : HasCompactSupport (ω : DifferentialForm (Euclid P) k) := ω.property.1.2
  have hcont : Continuous (fderiv ℝ (ω : DifferentialForm (Euclid P) k)) :=
    hsm.continuous_fderiv (by simp)
  have hcs' : HasCompactSupport (fderiv ℝ (ω : DifferentialForm (Euclid P) k)) := hcs.fderiv ℝ
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ z, ‖fderiv ℝ (ω : DifferentialForm (Euclid P) k) z‖ ≤ L :=
    Continuous.bounded_above_of_compact_support
      (f := fderiv ℝ (ω : DifferentialForm (Euclid P) k)) hcont hcs'
  have hdiff : Differentiable ℝ (ω : DifferentialForm (Euclid P) k) :=
    hsm.differentiable (by simp)
  have hmv : ∀ x y : Euclid P, ‖(ω : DifferentialForm (Euclid P) k) x -
      (ω : DifferentialForm (Euclid P) k) y‖ ≤ max L 0 * ‖x - y‖ := fun x y =>
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z)
      (fun z _ => (hL z).trans (le_max_left _ _)) (mem_univ y) (mem_univ x)
  refine ⟨C * max L 0, mul_nonneg hC0 (le_max_right _ _), fun x y => ?_⟩
  have h1 := hC ((ω : DifferentialForm (Euclid P) k) x - (ω : DifferentialForm (Euclid P) k) y)
  have h2 := mul_le_mul_of_nonneg_left (hmv x y) hC0
  rw [dist_eq_norm]
  calc covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x -
        (ω : DifferentialForm (Euclid P) k) y)
      ≤ C * ‖(ω : DifferentialForm (Euclid P) k) x - (ω : DifferentialForm (Euclid P) k) y‖ := h1
    _ ≤ C * (max L 0 * ‖x - y‖) := h2
    _ = C * max L 0 * ‖x - y‖ := by ring

## Key steps

1. norm_props (iii): |β| ≤ C‖β‖ for every k-covector β, with C ≥ 0.
2. ω is C^∞ with compact support, so Dω is continuous with compact support; hence ‖Dω(z)‖ ≤ L₀ for all z, with L₀ ≥ 0.
3. Mean value inequality on the convex set ℝ^P: ‖ω(x) − ω(y)‖ ≤ L₀‖x − y‖.
4. c := C·L₀ ≥ 0 gives |ω(x) − ω(y)| ≤ c·dist(x, y).

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
