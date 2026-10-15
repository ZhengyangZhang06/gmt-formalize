# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.bv_trace-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.bv_trace-a1.l1_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (bv_trace: 'Limit k → ∞ ... Passing to the limit in the inequality of step 1'), stated for an arbitrary measure space, set S, multiplier h and constants A, B. In the parent it is applied with S = Q_δ, h = div G, A = (2n + 1)V and B = 4n.

Notation. All integrals are over S with respect to μ, i.e. Bochner integrals for the restricted measure μ⌞S. Put ε_k := ∫_S |v_k − w|.

1. A.e. bound and integrability of the products. S is measurable and |h(x)| ≤ M for every x ∈ S, so ‖h(x)‖ = |h(x)| ≤ M for μ⌞S-almost every x (ae_restrict_iff'). Since h is a.e.-strongly measurable for μ⌞S and essentially bounded by M there, and w and every v_k are integrable on S, the products w·h and v_k·h are integrable on S (Integrable.mul_bdd: integrable times essentially bounded a.e.-strongly measurable is integrable).

2. Difference estimate. Fix k. By linearity (step 1), ∫_S w h − ∫_S v_k h = ∫_S (w h − v_k h). Hence
|∫_S w h − ∫_S v_k h| ≤ ∫_S |w h − v_k h|.
For μ⌞S-a.e. x, |w(x)h(x) − v_k(x)h(x)| = |w(x) − v_k(x)|·|h(x)| ≤ M·|v_k(x) − w(x)|, using |h(x)| ≤ M (step 1), |w − v_k| = |v_k − w| and |v_k − w| ≥ 0. Both |w h − v_k h| and M|v_k − w| are integrable on S (step 1 and integrability of v_k − w), so monotonicity of the integral (integral_mono_ae) and linearity give
|∫_S w h − ∫_S v_k h| ≤ ∫_S M|v_k − w| = M ε_k.

3. Comparison of ∫|v_k| with ∫|w|. For every x, |v_k(x)| = |w(x) + (v_k(x) − w(x))| ≤ |w(x)| + |v_k(x) − w(x)|. The functions |v_k|, |w| and |v_k − w| are integrable on S, so ∫_S |v_k| ≤ ∫_S (|w| + |v_k − w|) = ∫_S |w| + ε_k.

4. Estimate for fixed k. By the triangle inequality, the hypothesis on v_k, step 3 multiplied by B ≥ 0, and step 2:
|∫_S w h| ≤ |∫_S v_k h| + |∫_S w h − ∫_S v_k h|
 ≤ A + B∫_S |v_k| + M ε_k
 ≤ A + B∫_S |w| + B ε_k + M ε_k
 = A + B∫_S |w| + (B + M) ε_k.

5. Limit. Since ε_k → 0, the sequence A + B∫_S |w| + (B + M) ε_k converges to A + B∫_S |w| + (B + M)·0 = A + B∫_S |w|. By step 4 the constant |∫_S w h| is ≤ every term of this sequence, so it is ≤ its limit (ge_of_tendsto'): |∫_S w h| ≤ A + B∫_S |w|. ∎

## Key steps

1. |h| ≤ M on the measurable set S gives an a.e. bound for μ⌞S, so w·h and v_k·h are integrable on S.
2. |∫_S w h − ∫_S v_k h| ≤ ∫_S |w − v_k||h| ≤ M ε_k with ε_k = ∫_S |v_k − w|.
3. ∫_S |v_k| ≤ ∫_S |w| + ε_k.
4. Hence |∫_S w h| ≤ A + B∫_S |w| + (B + M) ε_k for every k (B ≥ 0).
5. Let k → ∞ (ε_k → 0) and use ge_of_tendsto'.

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
