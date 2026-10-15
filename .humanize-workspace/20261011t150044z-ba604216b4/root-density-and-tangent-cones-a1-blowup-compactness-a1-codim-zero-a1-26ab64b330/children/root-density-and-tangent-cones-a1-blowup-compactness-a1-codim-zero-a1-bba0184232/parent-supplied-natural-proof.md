# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.minimizing-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.minimizing-a1.const_eq_zero-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof of dtc_bc_cz_isMinimizingIn (the proof that c' = 0). Here it is stated for an arbitrary current X ∈ 𝒟_n(ℝⁿ) with compact support and an arbitrary real constant c.

Siblings used:
- bump_form (Bf = dtc_bc_cz_isMinimizingIn_bump_form): for every p ∈ ℝⁿ and r > 0 there is ω ∈ TestFormOn univ n with tsupport ω ⊆ closedBall(p, r) and 0 < ∫ ω(y)(e) dy.
- vanish_off_support (V = the accepted declaration dtc_vanish_off_support): S(ω) = 0 whenever tsupport ω is disjoint from S.support.

Write e := EuclideanSpace.basisFun (Fin n) ℝ.

1. spt X = X.support is compact, hence bounded (IsCompact.isBounded). So there is r₀ ∈ ℝ with spt X ⊆ closedBall(0, r₀) (Bornology.IsBounded.subset_closedBall).
2. Since n ≥ 1, the index i₀ := ⟨0, hn⟩ ∈ Fin n exists.
   - Let e₁ := EuclideanSpace.single i₀ (1 : ℝ). Then ‖e₁‖ = ‖(1 : ℝ)‖ = 1 (EuclideanSpace.norm_single, now PiLp.norm_single).
   - Put p := (|r₀| + 2)·e₁. As |r₀| + 2 > 0, ‖p‖ = (|r₀| + 2)·‖e₁‖ = |r₀| + 2 (norm_smul, Real.norm_eq_abs, abs_of_pos).
3. Apply Bf with this p and r := 1 > 0. This gives ω ∈ TestFormOn univ n with tsupport ω ⊆ closedBall(p, 1) and I := ∫ ω(y)(e) dy > 0.
4. tsupport ω and spt X are disjoint.
   - Suppose y ∈ tsupport ω ∩ spt X. By step 3, ‖y − p‖ ≤ 1; by step 1, ‖y‖ ≤ r₀.
   - The triangle inequality applied to p = y − (y − p), together with r₀ ≤ |r₀|, gives ‖p‖ ≤ ‖y‖ + ‖y − p‖ ≤ r₀ + 1 ≤ |r₀| + 1 < |r₀| + 2 = ‖p‖.
   - This is a contradiction.
5. Apply V with P := n, U := univ, S := X and this ω, using step 4. This gives X(ω) = 0.
6. By the hypothesis on X, X(ω) = c·I. Hence c·I = 0. Since I > 0, we have I ≠ 0, and therefore c = 0 (mul_eq_zero). ∎

Implementation note (not part of the proof): name every auxiliary Lean declaration introduced for this child with the prefix dtc_bc_cz_isMinimizingIn_const_eq_zero_. Sibling candidates are merged into one Submission.lean, and only byte-identical duplicate declarations are dropped.

## Key steps

1. Compactness of spt X gives spt X ⊆ closedBall(0, r₀). Since n ≥ 1, the point p = (|r₀| + 2)e₁ exists and has ‖p‖ = |r₀| + 2.
2. bump_form gives a test form ω with tsupport ω ⊆ closedBall(p, 1) and ∫ω(y)(e) dy > 0. The triangle inequality makes tsupport ω disjoint from spt X.
3. vanish_off_support gives X(ω) = 0. The hypothesis gives X(ω) = c·∫ω(y)(e) dy, and the integral is positive, so c = 0.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch07/{Contract,Submission}.lean against workspace GMT/Ch07/{Contract,Submission}.lean (identical); git show 72492511a:GMT/Ch07/Submission.lean (dispatch base = frozen contract only)`
- `python3 -I over dag.json: this node (depth 4, decomposing, depends_on top_constancy/im_sub/vanish_off_support), sibling types (dtc_bc_cz_top_constancy, dtc_isIntegerMultiplicity_sub, dtc_vanish_off_support), regex scans of all lean_statements for '∃ ω : TestFormOn', 'basisFun' + Covector, 'IsTestForm.*∫', '0 < ∫', and lean_name collision check for the proposed names`
- `rg -n 'theorem integral_pos|theorem tsupport_eq|protected theorem contDiff|theorem nonneg|protected theorem hasCompactSupport' mathlib/Mathlib/Analysis/Calculus/BumpFunction/{Basic,Normed}.lean`
- `rg -n 'continuous_of_finiteDimensional|toContinuousAlternatingMap|mkContinuousAlternating' mathlib/Mathlib (LinearMap version only)`
- `rg -n 'theorem det_self|theorem det_apply' mathlib/Mathlib/LinearAlgebra/Determinant.lean; rg -n 'basisFun_repr|basisFun_apply|basisFun_toBasis' mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean; rg -n 'continuous_matrix|Continuous.matrix_det' mathlib/Mathlib/Topology/Instances/Matrix.lean; rg -n 'tsupport_smul_subset_left|HasCompactSupport.smul_right' mathlib/Mathlib; rg -n 'norm_single' mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `grep -n 'def IsSmoothForm|def IsTestForm|abbrev TestFormOn|structure GeometricCurrentOn|boundary_apply|theorem ext' simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents}.lean`
- `git show fee01ff8:GMT/Ch07/Submission.lean (accepted cmr_cc_det_covector_exists: detRowAlternating.compLinearMap + mkContinuous with Leibniz bound); import scan of 1038 accepted candidates (10 add Mathlib.Analysis.Calculus.BumpFunction.* imports; 77fcc7d adds Poincare.SimonGMT.Chapter01.DensityComparison)`
- `rg dtc_bc_cz_isMinimizingIn_ in dag.json, snapshot project, workspace GMT, simongmt/Poincare (no match, exit 1); rg -l in nodes/ (only the implementation-note prefix in this node's handoff and the parent's decompositions)`
- `grep _existing_lean_name_problem|_solve_children|_install_parent_supplied_child_handoff|_overlay_accepted_children in runtime.py; store.py ensure (accepted reuse returns the existing node, handoff install skipped)`
- `python3 -I /tmp/mzn-split/scripts/gen.py (verifier gmt-compare.py child_modules contract mode + lean_contract.validate_lean_statement) on the selected type and the 3 child types`
- `lake env lean /tmp/mzn-split/check/{Challenge_parent,Challenge_bump_form,Challenge_vanish_off_support,Challenge_const_eq_zero,Assembly,BumpProof,DetRoute}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1-26ab64b330/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/store.py`
- `/tmp/mzn-split/check/Assembly.lean`
- `/tmp/mzn-split/check/BumpProof.lean`
- `/tmp/mzn-split/check/DetRoute.lean`
- `/tmp/mzn-split/check/Challenge_parent.lean`
- `/tmp/mzn-split/check/Challenge_bump_form.lean`
- `/tmp/mzn-split/check/Challenge_const_eq_zero.lean`
- `/tmp/mzn-split/check/Challenge_vanish_off_support.lean`

Snapshot and base:
- The snapshot (project b4d606d, Mathlib 25730c7c) has a Contract.lean and Submission.lean byte-identical to the workspace files used for compilation.
- This node's dispatch base 7249251 holds only the frozen contract, so children see only the commits of their sibling dependencies.

Library support:
- Every lemma the child proofs cite exists at the pin:
  - ContDiffBump.nonneg/tsupport_eq/hasCompactSupport/contDiff (BumpFunction/Basic.lean:142–203)
  - ContDiffBump.integral_pos (BumpFunction/Normed.lean:63)
  - Module.Basis.det_apply/det_self (Determinant.lean:607/610)
  - EuclideanSpace.basisFun_apply/basisFun_repr (PiL2.lean:806/810)
  - continuous_matrix and Continuous.matrix_det (Instances/Matrix.lean:97/212)
  - tsupport_smul_subset_left and HasCompactSupport.smul_right (Algebra/Support.lean:168/466)
  - PiLp.norm_single (PiLp.lean:1044)
- ContDiffBump.integral_pos is outside the frozen import closure, but accepted candidates already add such imports: 10 add BumpFunction imports and 77fcc7d adds a SimonGMT import.
- MultilinearMap.continuous_of_finiteDimensional is absent at the pin. So e* is made continuous through the coordinate determinant (or a Leibniz bound, as in accepted cmr_cc_det_covector_exists).

Reuse:
- No accepted DAG declaration gives a positive-integral top-degree test form or the compact-support rigidity.
- dtc_vanish_off_support is accepted with a byte-identical type, so it is reused.

Lean checks:
- The selected type and all child types elaborate in comparator contract scope.
- Assembly.lean derives the exact selected type from G, Cst and const_eq_zero, and derives const_eq_zero from bump_form and V.
- BumpProof.lean proves bump_form outright, and DetRoute.lean checks the basis-determinant route to e*.
- All checks use only the axioms [propext, Classical.choice, Quot.sound].

Names: the new names occur nowhere in dag.json (1625 nodes), the snapshot, workspace GMT or SimonGMT.
