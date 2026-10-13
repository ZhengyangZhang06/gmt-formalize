# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.c1_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1–2 of the parent proof (slicing_im_st_level_set_charts): "Since g is C¹ at 0 it is C¹ on a neighbourhood of 0 (ContDiffAt.eventually); choose r₀ > 0 such that g is C¹ on B(0, 3r₀). Let χ : ℝ^m → [0, 1] be a C^∞ bump function with χ = 1 on B(0, r₀) and support in B(0, 2r₀) (ContDiffBump). Put g̃ := χ·g. Then g̃ is C¹ on ℝ^m: it is C¹ on B(0, 3r₀) as a product of C¹ functions, and it vanishes identically on the open set {|v| > 2r₀}; these two open sets cover ℝ^m. Moreover g̃ = g on B(0, r₀)." Here it is stated for an arbitrary centre x (the parent uses x = 0) and the new function is called g' in Lean.

Conventions. ℝ^k = Eucl k = EuclideanSpace ℝ (Fin k) with inner product ⟨·,·⟩ (inner ℝ) and Euclidean norm |·|; B(x, r) = ball x r is the open ball; Df(x) := fderiv ℝ f x for a map f.

1. (g is C¹ near x.) g is C¹ at x and 1 ≠ ∞, so g is C¹ at every point of some neighbourhood of x (ContDiffAt.eventually). Choose ε > 0 such that g is C¹ at every y ∈ B(x, ε) (Metric.mem_nhds_iff), and put ρ := ε/3 > 0; thus ε = 3ρ.

2. (Bump function.) ℝ^m is a finite-dimensional inner product space, so smooth bump functions exist on it (hasContDiffBump_of_innerProductSpace). Let χ be the bump function centred at x with inner radius ρ and outer radius 2ρ (ContDiffBump x with rIn := ρ, rOut := 2ρ; valid since 0 < ρ < 2ρ). Then χ : ℝ^m → ℝ is C^∞, in particular C¹ at every point (ContDiffBump.contDiffAt); χ(y) = 1 for every y with |y − x| ≤ ρ (ContDiffBump.one_of_mem_closedBall); and χ(y) = 0 for every y with |y − x| ≥ 2ρ (ContDiffBump.zero_of_le_dist).

3. (Definition.) Put g̃(y) := χ(y)·g(y) for y ∈ ℝ^m, and take this ρ.

4. (g̃ is C¹ on ℝ^m.) By contDiff_iff_contDiffAt it suffices to show that g̃ is C¹ at every y ∈ ℝ^m.
   - Case |y − x| < ε. Then y ∈ B(x, ε), so g is C¹ at y by step 1, and χ is C¹ at y by step 2; hence the product g̃ = χ·g is C¹ at y (ContDiffAt.mul).
   - Case |y − x| ≥ ε. Then |y − x| ≥ 3ρ > 2ρ. The set O := {z : |z − x| > 2ρ} is open, as the strict superlevel set of the continuous function z ↦ dist(z, x) (isOpen_lt), and y ∈ O. For z ∈ O, |z − x| ≥ 2ρ, so χ(z) = 0 and g̃(z) = 0. Thus g̃ agrees with the constant function 0 on the neighbourhood O of y, and a constant function is C¹; hence g̃ is C¹ at y (contDiffAt_const.congr_of_eventuallyEq).
   The two cases are exhaustive, so g̃ is C¹ on ℝ^m.

5. (Agreement on B(x, ρ).) If v ∈ B(x, ρ) then |v − x| < ρ, so χ(v) = 1 by step 2 and g̃(v) = 1·g(v) = g(v).

6. (Conclusion.) ρ > 0 and g̃ satisfy ContDiff ℝ 1 g̃ (step 4) and g̃(v) = g(v) for all v ∈ B(x, ρ) (step 5). ∎

Lean remark. The following proof was verified (Lean v4.35.0-rc3, Mathlib 25730c7c) as the declaration `theorem Submission.slicing_im_st_lsc_c1_extension : (<frozen statement>) := by` placed, like other accepted declarations, after the `end` of the `noncomputable section` and before `main_theorem` inside `namespace GMT.Ch06` of GMT/Ch06/Submission.lean. It needs no import beyond the frozen ones (ContDiffBump and the inner-product-space bump instance are already available). Axioms: propext, Classical.choice, Quot.sound. The comparator-style check `exact Submission.slicing_im_st_lsc_c1_extension` against the frozen type in the contract scope also passed.
  intro m g x hg
  -- `g` is `C¹` at every point of some ball `B(x, ε)` (`ContDiffAt.eventually`); `ρ := ε / 3`.
  have hev := hg.eventually (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hev
  set ρ := ε / 3 with hρdef
  have hρ : 0 < ρ := by positivity
  -- Bump `χ` with `χ = 1` on `closedBall x ρ` and `χ = 0` off `ball x (2ρ)`; `g' := χ * g`.
  let χ : ContDiffBump x := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  refine ⟨ρ, hρ, fun y => χ y * g y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : dist y x < ε
    · exact χ.contDiffAt.mul (hball hy)
    · have hopen : IsOpen {z : Eucl m | 2 * ρ < dist z x} :=
        isOpen_lt continuous_const (continuous_id.dist continuous_const)
      have hy2 : 2 * ρ < dist y x := by
        have := not_lt.1 hy
        linarith
      have hzero : (fun y => χ y * g y) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [hopen.mem_nhds hy2] with z hz
        have : χ z = 0 := χ.zero_of_le_dist (le_of_lt hz)
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  · intro v hv
    have : χ v = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hv)
    simp [this]

## Key steps

1. ContDiffAt.eventually: g is C¹ at every point of B(x, ε); put ρ := ε/3.
2. Smooth bump χ centred at x with χ = 1 on closedBall(x, ρ) and χ = 0 where |y − x| ≥ 2ρ.
3. g̃ := χ·g is C¹ at points of B(x, 3ρ) (product rule) and vanishes near points with |y − x| > 2ρ; these cases cover ℝ^m.
4. g̃ = g on B(x, ρ) because χ = 1 there.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch06/Contract.lean with the workspace Contract.lean (identical) and Contract.lean with Submission.lean (identical)`
- `read nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.json} (frozen type, Steps 0-9 of the supplied proof)`
- `python3 over dag.json: id/lean_name/status/lean_statement of all 476 nodes; grep -iE 'antilip|implicit|level|chart|graph|bump|c1_|immersion|orthonormal|isometry|kernel' over the name list; lean_statement scan for 'implicit', 'level set', 'LinearMap.ker'`
- `grep -c 'slicing_im_st_lsc_' (and each full new name) in dag.json DAG.md issue-workers.json dag.mmd; grep -rl 'slicing_im_st_lsc' nodes/ local-references/197bdd4b88278494/project lake-packages-25730c7c/simongmt/Poincare (no match)`
- `read decomposition-v1.json of root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1 (fiw_ims_frame_sign reuse convention) and of root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655 (earlier reuse of lpf_wtc_cat_fderiv_lower_bound, resolved to the accepted node in dag.json)`
- `read parent-supplied-natural-proof.{md,json} of root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9 (accepted proof and key steps of lpf_wtc_cat_fderiv_lower_bound); git show 8cfbc487a3d10545b0ea005ad58122242bbcc072 -- GMT/Ch06/Submission.lean (placement of accepted Submission.* declarations)`
- `rg in the Mathlib snapshot: ContDiffAt.implicitFunction, implicitFunction_apply_self, eventually_apply_eq_iff_implicitFunction, contDiffAt_implicitFunction, ContDiffAt.eventually, ContDiffBump (one_of_mem_closedBall, zero_of_le_dist, contDiffAt), hasContDiffBump_of_innerProductSpace, ContDiffOn.exists_lipschitzOnWith, TopologicalSpace.isOpen_iUnion_countable, Set.Countable.exists_eq_range, ContinuousLinearMap.IsInvertible, InnerProductSpace.toDual_symm_apply, stdOrthonormalBasis, OrthonormalBasis.reindex, ContinuousLinearMap.codRestrict, LinearMap.range_eq_top_of_ne_zero, LinearMap.finrank_range_of_inj, LinearMap.finrank_range_add_finrank_ker, Submodule.eq_of_le_of_finrank_eq, norm_add_sq_real, ball_prod_same, fderiv_comp, LinearMap.range_comp, Filter.EventuallyEq.fderiv_eq, ContDiff.continuous_fderiv, le_of_sq_le_sq, sq_le_sq₀`
- `lake env lean Check.lean: #check of the above after `import GMT.Ch06.Submission` (all available except ContDiffAt.implicitFunction* and LinearMap.range_eq_top_of_ne_zero; the former needs `import Mathlib.Analysis.Calculus.ImplicitContDiff`, whose olean is in lake-packages-25730c7c)`
- `gmt-compare.py contract_scope/child_modules (child scope: namespace GMT.Ch06 + contract opens, noncomputable section/end) and frozen_inputs/candidate_inputs (only GMT/Ch06/Submission.lean is not byte-frozen; imports unrestricted); import lines of 398 branch heads (earlier accepted candidates added Poincare.* imports)`
- `python3 -I validate.py: lean_contract.validate_lean_statement on the parent and the 5 child statements (all returned unchanged)`
- `lake env lean Stmts.lean (all child types elaborate in the comparator child scope); Assembly.lean (frozen parent type from the local_graph and tangent_range types as hypotheses: axioms propext, Classical.choice, Quot.sound); KernelFrame.lean, C1Extension.lean, LocalGraph.lean (from kernel_frame and c1_extension), TangentRange.lean (from fderiv_lower_bound): each standard axioms only`
- `lean -R sim -o sim/out/GMT/Ch06/Submission.olean sim/GMT/Ch06/Submission.lean (frozen Submission + import Mathlib.Analysis.Calculus.ImplicitContDiff + the 6 Submission.* declarations); LEAN_PATH=sim/out:$LEAN_PATH lean sim/Solutions.lean (comparator-style `exact Submission.X` for all 6 frozen types, #print axioms: propext, Classical.choice, Quot.sound)`
- `independent reviewer subagent: rebuilt the simulation from the JSON Lean remarks, compared reuse fields byte-for-byte, hashed the 56 frozen GMT.Ch06 declarations with/without the extra import (identical), ran gmt-compare.py with a simulated DAG for local_graph and the parent ('Your solution is okay!'); verdict ACCEPT`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/DAG.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.mmd`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-interio-e2ad70d40d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ImplicitContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Invertible.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Dual/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/Ring/Abs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/.lake/build/lib/lean/Mathlib/Analysis/Calculus/ImplicitContDiff.olean`
- `/tmp/lsc-split-7731/Stmts.lean`
- `/tmp/lsc-split-7731/Assembly.lean`
- `/tmp/lsc-split-7731/KernelFrame.lean`
- `/tmp/lsc-split-7731/C1Extension.lean`
- `/tmp/lsc-split-7731/LocalGraph.lean`
- `/tmp/lsc-split-7731/TangentRange.lean`
- `/tmp/lsc-split-7731/sim/GMT/Ch06/Submission.lean`
- `/tmp/lsc-split-7731/sim/Solutions.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract, and the workspace Submission is byte-identical to it. No SimonGMT or project declaration and no DAG node provides local graph charts of regular level sets, an adapted kernel frame, a C¹ germ extension or the tangent-range identity. The names slicing_im_st_lsc_* occur nowhere in dag.json, DAG.md, issue-workers.json, dag.mmd, nodes/ or the snapshot. The only reusable accepted declaration is lpf_wtc_cat_fderiv_lower_bound (accepted, commit 8cfbc487), reused with its byte-identical type and accepted proof, as already done in the measurable_chart_differential decomposition. Mathlib supplies everything else: the C¹ implicit function theorem (ContDiffAt.implicitFunction with implicitFunction_apply_self, eventually_apply_eq_iff_implicitFunction, contDiffAt_implicitFunction), ContDiffBump on inner product spaces, ContDiffAt.eventually, ContDiffOn.exists_lipschitzOnWith, isOpen_iUnion_countable, Riesz duality, stdOrthonormalBasis and the finrank API. ImplicitContDiff is not imported by the frozen Submission. The comparator lets Submission.lean add imports, so only local_graph needs the extra import line. All 5 child types validate and elaborate in the comparator scope. Every new child is fully proved in Lean from its sibling dependencies, and the frozen parent type is proved from local_graph and tangent_range. Everything was kernel-checked in a simulated Submission module with comparator-style checks and standard axioms only, and independently re-verified, including by full gmt-compare.py runs.
