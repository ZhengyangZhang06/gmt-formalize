# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.minimizing-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.minimizing-a1.bump_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof of dtc_bc_cz_isMinimizingIn, which builds the test form ω = a·e* and shows ∫ω(y)(e) dy = ∫a > 0. Here it is stated for an arbitrary centre p ∈ ℝⁿ and radius r > 0. No sibling is used.

Notation:
- e := EuclideanSpace.basisFun (Fin n) ℝ. So e(j) = EuclideanSpace.single j 1 is the j-th standard unit vector (EuclideanSpace.basisFun_apply), and e.repr x k = x k (EuclideanSpace.basisFun_repr).
- dy is Lebesgue measure (volume) on ℝⁿ = Euclid n.
- No assumption on n is needed. For n = 0 every step holds verbatim: ℝ⁰ is a point and D below is the empty determinant, equal to 1.

1. The n-covector e*.
   - Let D := e.toBasis.det, an alternating n-linear map (ℝⁿ)ⁿ → ℝ.
   - For v : Fin n → ℝⁿ, D(v) = det(e.toBasis.toMatrix v) (Module.Basis.det_apply). Since e.toBasis.toMatrix v k j = e.repr (v j) k = v j k, this gives D(v) = det(Matrix.of fun k j => v j k).
   - Each entry v ↦ v j k is continuous: it is evaluation at j followed by the k-th coordinate (continuous_apply, PiLp.continuous_apply). So the matrix-valued map v ↦ Matrix.of (fun k j => v j k) is continuous (continuous_matrix), and so is its determinant (Continuous.matrix_det).
   - Hence D together with this continuity is a continuous alternating map e* : Covector (Euclid n) n = ℝⁿ [⋀^Fin n]→L[ℝ] ℝ with e*(v) = D(v) for all v. In Lean this is the structure { D with cont := … }.
   - Equivalently, the Leibniz formula and |v_j(k)| ≤ ‖v_j‖ give |D(v)| ≤ n!·∏_j ‖v_j‖, and AlternatingMap.mkContinuous then produces the same e*.
   - Finally e*(e) = D(e) = 1 by Module.Basis.det_self (the coercions of e and e.toBasis to functions agree).
2. The bump.
   - Since 0 < r/2 < r, there is a smooth bump function a : ContDiffBump p with inner radius r/2 and outer radius r. The instance HasContDiffBump holds because ℝⁿ is a finite-dimensional inner product space.
   - a is C^∞ (ContDiffBump.contDiff).
   - a(y) ≥ 0 for every y (ContDiffBump.nonneg).
   - HasCompactSupport a (ContDiffBump.hasCompactSupport).
   - tsupport a = closedBall(p, r) (ContDiffBump.tsupport_eq).
   - 0 < ∫ a(y) dy (ContDiffBump.integral_pos). Indeed, a is continuous, nonnegative and integrable, and it is positive on the nonempty open ball B(p, r), which has positive measure. Lebesgue measure on ℝⁿ is locally finite and positive on nonempty open sets.
3. The form.
   - Define ω(y) := a(y) • e* for y ∈ ℝⁿ.
   - ω is C^∞, being a smooth function times a constant covector (ContDiff.smul with contDiff_const). So IsSmoothForm ω.
   - ω(y) = 0 whenever a(y) = 0. Hence HasCompactSupport ω (HasCompactSupport.smul_right), and tsupport ω ⊆ tsupport a = closedBall(p, r) (tsupport_smul_subset_left).
   - Thus IsTestForm ω, and tsupport ω ⊆ univ trivially. So ω ∈ TestFormOn univ n with tsupport ω ⊆ closedBall(p, r).
4. The integral.
   - For every y, ω(y)(e) = (a(y) • e*)(e) = a(y)·e*(e) = a(y)·1 = a(y), by ContinuousAlternatingMap.smul_apply and step 1.
   - Hence ∫ ω(y)(e) dy = ∫ a(y) dy > 0 by step 2.
   - So this ω witnesses the statement. ∎

Implementation notes (not part of the proof):
- ContDiffBump.integral_pos lives in Mathlib.Analysis.Calculus.BumpFunction.Normed, which is outside the frozen import closure. Add `import Mathlib.Analysis.Calculus.BumpFunction.Normed` to Submission.lean.
- Name every auxiliary Lean declaration introduced for this child with the prefix dtc_bc_cz_isMinimizingIn_bump_form_. Sibling candidates are merged into one Submission.lean, and only byte-identical duplicate declarations are dropped.

## Key steps

1. e* := the basis determinant D = (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det. It is continuous because D(v) = det(v_j(k)) is a polynomial in the coordinates, and e*(e) = 1 by Module.Basis.det_self.
2. a := ContDiffBump p with radii r/2 < r. It is smooth, nonnegative and compactly supported, with tsupport a = closedBall(p, r) and ∫a > 0.
3. ω := a·e* is a test form on ℝⁿ with tsupport ω ⊆ closedBall(p, r), and ∫ω(y)(e) dy = ∫a(y) dy > 0.

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
