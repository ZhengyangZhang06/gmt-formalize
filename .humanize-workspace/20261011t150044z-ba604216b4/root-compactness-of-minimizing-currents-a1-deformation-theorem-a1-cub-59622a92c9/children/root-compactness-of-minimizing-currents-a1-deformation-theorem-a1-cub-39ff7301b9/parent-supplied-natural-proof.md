# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.bv_trace-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.bv_trace-a1.cube_cont_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 0 of the parent proof (bv_trace: 'div G is continuous; it is therefore bounded on the compact set [0, 1]ⁿ ⊇ Q₁') and step 1 ('Each v_k is continuous, hence bounded on the bounded set Q_δ; so v_k ... integrable'). Both uses are isolated here for an arbitrary continuous f.

Notation. Euclid k = EuclideanSpace ℝ (Fin k) with Lebesgue measure volume; y_i is the i-th coordinate (y i = WithLp.ofLp y i in Lean). Q₁ := {y : 0 < y_i < 1 for all i} and K := {y : 0 ≤ y_i ≤ 1 for all i} (the closed unit cube).

1. K is compact. The coordinate map ofLp : Euclid k → (Fin k → ℝ), y ↦ (y_i)_i, is a homeomorphism (Mathlib PiLp.homeomorph 2 (fun _ => ℝ)). A point y lies in K iff 0 ≤ y_i ≤ 1 for every i, i.e. iff ofLp y lies in the order interval Icc 0 1 = ∏_i [0, 1] of Fin k → ℝ (the order there is coordinatewise). So K is the preimage of Icc 0 1 under this homeomorphism. Icc 0 1 is compact in Fin k → ℝ (isCompact_Icc; it is a finite product of compact intervals), and the preimage of a compact set under a homeomorphism is compact (Homeomorph.isCompact_preimage). Hence K is compact.

2. Q₁ ⊆ K, since 0 < y_i < 1 implies 0 ≤ y_i ≤ 1 for each i.

3. Boundedness. f is continuous, hence continuous on the compact set K, so it is bounded there: there is M ∈ ℝ with |f(y)| = ‖f(y)‖ ≤ M for all y ∈ K (IsCompact.exists_bound_of_continuousOn). By step 2 the same bound holds for all y ∈ Q₁. This proves (a).

4. Integrability. Lebesgue measure on Euclid k is finite on compact sets (it is an additive Haar measure, so IsFiniteMeasureOnCompacts holds), and Euclid k is Hausdorff. Hence f, continuous on the compact set K, is integrable on K (ContinuousOn.integrableOn_compact). Integrability on a set passes to subsets (IntegrableOn.mono_set), so by step 2 f is integrable on Q₁. This proves (b). ∎

## Key steps

1. The closed cube K = {0 ≤ y_i ≤ 1} is the preimage of the compact box Icc 0 1 ⊆ (Fin k → ℝ) under the homeomorphism PiLp.homeomorph, hence compact.
2. Q₁ ⊆ K.
3. A continuous f is bounded on the compact K (IsCompact.exists_bound_of_continuousOn), hence on Q₁.
4. A continuous f is integrable on the compact K for the Haar measure volume (ContinuousOn.integrableOn_compact), hence on Q₁ ⊆ K.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n 'cmcdt_cbm_bvt' project mathlib/Mathlib -g '*.lean' (no match); python3 scan of dag.json lean_name/theorems fields for cmcdt_cbm_bvt_cube_cont_bound, cmcdt_cbm_bvt_l1_limit, cmcdt_cbm_bvt_cube_exhaust (no collision); python3 scan of dag.json lean_statements containing '0 < y i ∧ y i < 1' or '1 - δ' (only cube_bv_median siblings and face_replacement nodes; no accepted exhaustion/boundedness lemma to reuse)`
- `rg -n -i 'exhaust|unit cube|cube_cont|l1_limit|tendsto_setIntegral|exists_bound_of_continuousOn' project -g '*.lean' (no match); rg -n -i 'exhaust|tendsto_setIntegral|exists_bound_of_continuousOn|integrableOn_compact' lake-packages-25730c7c/simongmt/Poincare -g '*.lean' (only internal uses in Chapter04 ball arguments; nothing about cubes)`
- `rg -n 'theorem (tendsto_setIntegral_of_monotone|tendsto_integral_filter_of_dominated_convergence|setIntegral_indicator|setIntegral_mono_set|integral_mono_ae|abs_integral_le_integral_abs|integral_const_mul)\b' mathlib/Mathlib`
- `rg -n 'theorem (IsCompact\.exists_bound_of_continuousOn|ContinuousOn\.integrableOn_compact)\b|(theorem|lemma) (Integrable\.mul_bdd|ge_of_tendsto'|le_of_tendsto)\b' mathlib/Mathlib; sed -n 1060,1080p Mathlib/MeasureTheory/Function/L1Space/Integrable.lean (Integrable.bdd_mul / mul_bdd signatures)`
- `rg -n 'theorem ContDiff.continuous_fderiv\b|def coeLM\b|theorem LinearMap.continuous_of_finiteDimensional' mathlib/Mathlib; sed -n 530,550p Mathlib/Analysis/Normed/Lp/PiLp.lean (continuous_ofLp, PiLp.continuous_apply, PiLp.homeomorph)`
- `lake env lean /tmp/bvtrace-decomp/Types.lean (child types elaborate); lake env lean /tmp/bvtrace-decomp/Children.lean (three children fully proved; axioms propext, Classical.choice, Quot.sound); lake env lean /tmp/bvtrace-decomp/Assembly.lean and /tmp/bvtrace-decomp/final/Final.lean (generated from frozen DAG strings: exact parent type proved from exact child types plus exact sibling types cmcdt_cbm_smooth_approx / cmcdt_cbm_smooth_trace; sorry only in sibling stubs)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/WeightedEstimates.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-59622a92c9/parent-child-handoff.json`
- `/tmp/bvtrace-decomp/Types.lean`
- `/tmp/bvtrace-decomp/Children.lean`
- `/tmp/bvtrace-decomp/Assembly.lean`
- `/tmp/bvtrace-decomp/final/Final.lean`
- `/tmp/bvtrace-decomp/final/subproblems.json`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same contract as the workspace Submission.lean.

Nothing in it can be reused directly:
- No project, simongmt or DAG declaration states that continuous functions are bounded and integrable on the unit cube.
- None states the L¹ limit passage or the exhaustion of Q₁ by the shrunken cubes Q_δ.
- No name with the prefix cmcdt_cbm_bvt exists anywhere.

Mathlib, already inside the import closure of GMT.Ch07.Submission so that no new imports are needed, supplies every tool the child proofs and the parent assembly cite:
- PiLp.homeomorph, PiLp.continuous_apply, isCompact_Icc, Homeomorph.isCompact_preimage;
- IsCompact.exists_bound_of_continuousOn, ContinuousOn.integrableOn_compact, IntegrableOn.mono_set;
- ae_restrict_iff', Integrable.mul_bdd, integral_sub, integral_add, integral_mono(_ae), abs_integral_le_integral_abs, integral_const_mul;
- ge_of_tendsto', le_of_tendsto;
- setIntegral_indicator, tendsto_integral_filter_of_dominated_convergence, Filter.eventually_all, eventually_lt_nhds, isOpen_iInter_of_finite, setIntegral_mono_set;
- ContDiff.continuous_fderiv, LinearMap.continuous_of_finiteDimensional, ContinuousLinearMap.coeLM, Ioo_mem_nhdsGT.

All three children were fully proved in Lean using only the standard axioms. The parent's frozen type was proved from the exact child types and the exact frozen sibling types (smooth_approx and smooth_trace).
