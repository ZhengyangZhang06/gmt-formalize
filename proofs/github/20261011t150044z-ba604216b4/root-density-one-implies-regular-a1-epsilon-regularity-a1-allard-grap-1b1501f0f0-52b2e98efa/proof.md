# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.interior_estimates-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.interior_estimates-a1.mean_value_sq_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step (2a) of the selected parent proof, the Cauchy–Schwarz bound for a function equal to its own ball mean (Simon Ch. 5, 3.2 with q = 0).

1. Let B := ball(y, ρ) and V := (Lⁿ(B)).toReal. B is bounded, so Lⁿ(B) < ∞ (measure_ball_lt_top). Constants are integrable on B, and ∫_B c = V·c for every c ∈ ℝ (setIntegral_const, with volume.real B = (volume B).toReal by measureReal_def).

2. closedBall(y, ρ) is compact, and f and f² are continuous on it. So both are integrable on closedBall(y, ρ) (ContinuousOn.integrableOn_compact), hence on its subset B (IntegrableOn.mono_set).

3. The integrand (f(z) − f(y))² is nonnegative, so 0 ≤ ∫_B (f(z) − f(y))² dz (setIntegral_nonneg).

4. Pointwise, (f(z) − f(y))² = (f(z)² − 2f(y)f(z)) + f(y)². All pieces are integrable on B (steps 1–2), so by linearity of the integral (integral_add, integral_sub, integral_const_mul, setIntegral_const):
∫_B (f − f(y))² = ∫_B f² − 2f(y)·∫_B f + f(y)²·V.

5. Substitute the hypothesis ∫_B f = V·f(y):
∫_B (f − f(y))² = ∫_B f² − 2f(y)²V + f(y)²V = ∫_B f² − f(y)²·V.

6. Steps 3 and 5 give f(y)²·V ≤ ∫_B f². This is the parent's Cauchy–Schwarz inequality (∫_B f)² ≤ V·∫_B f² with ∫_B f = V f(y) inserted, proved here by expanding a square. ∎

## Key steps

1. f and f² are integrable on the ball, since f is continuous on the compact closed ball; and ∫_B c = V·c for constants.
2. 0 ≤ ∫_B (f − f(y))².
3. Expanding and using ∫_B f = V·f(y) gives ∫_B (f − f(y))² = ∫_B f² − f(y)²V.
4. Hence f(y)²V ≤ ∫_B f².

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean && cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (IDENTICAL)`
- `grep -rn "theorem HasFDerivAt.le_of_lip'" <snapshot>/mathlib/Mathlib/Analysis`
- `grep -rn 'theorem integral_inter_add_diff\|theorem integral_inter_add_sdiff' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `grep -rn 'theorem addHaar_ball ' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `grep -rn 'theorem ContDiffAt.isSymmSndFDerivAt' <snapshot>/mathlib/Mathlib/Analysis`
- `grep -rn 'theorem abs_pow_sub_pow_le' <snapshot>/mathlib/Mathlib`
- `grep -rn 'theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary\b|theorem norm_image_sub_le_of_norm_deriv_le_segment' <snapshot>/mathlib/Mathlib/Analysis`
- `grep -rn 'theorem norm_setIntegral_le_of_norm_le_const\b|theorem setIntegral_mono_set' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `grep -rn 'iteratedFDeriv_two_apply|theorem fderiv_clm_apply|theorem ContDiffOn.fderiv_of_isOpen|theorem fderiv_fun_sum|theorem opNorm_le_bound ' <snapshot>/mathlib/Mathlib`
- `grep -n -E '^(theorem|lemma)' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/*.lean Analysis/InnerProductSpace/Laplacian.lean`
- `grep -rln -i 'mean.value|meanValue|ball_average|average_ball' Analysis/InnerProductSpace Analysis/Complex/Harmonic  (only Complex/Harmonic/MeanValue.lean)`
- `grep -rn -i -E 'theorem .*harmonic.*(fderiv|deriv)|theorem .*(fderiv|deriv).*harmonic' <snapshot>/mathlib/Mathlib  (no match)`
- `grep -rn -E 'theorem taylor_mean_remainder' <snapshot>/mathlib/Mathlib  (one-variable only)`
- `grep -rn -i -E 'harmonic|taylor|mean.value' <snapshot>/project/GMT; grep -rn -i -E 'theorem .*(harmonic|meanValue|mean_value|taylor)' .lake/packages/simongmt/Poincare`
- `python3 -I: lean_name scan of dag.json (344 nodes) and nodes/*/*.json (589 names); git grep 'dorag_ha_ie_' over 1016 refs -- GMT  (no hit)`
- `grep -n '_existing_lean_name_problem|_overlay_accepted_children|max_depth' /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py; validate_lean_statement from lean_contract.py on the six child types`
- `toolchains/lean-4.35.0-rc3-linux/bin/lake env lean /tmp/ie-decomp/Glue.lean, /tmp/ie-decomp/children/{A,BC,D1,D2,E}/*.lean, /tmp/ie-decomp/All.lean (#print axioms of all six children and of Submission.dorag_ha_interior_estimates)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Ring/Abs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/HarmonicContOnCl.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Harmonic/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Taylor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-f15d71c3ef/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-support-null-a1-local-carrier-null-a1/decomposition-v1.json`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/ie-decomp/Glue.lean`
- `/tmp/ie-decomp/All.lean`
- `/tmp/ie-decomp/All.log`
- `/tmp/ie-decomp/children/D1/D1_analysis.lean`
- `/tmp/ie-decomp/children/D2/D2_stub_counterexample.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c, and GMT/Ch07/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Nothing reusable exists for this node:
- the pinned Mathlib has no ℝⁿ mean value property, no interior derivative estimate for harmonic functions, and no lemma that derivatives of harmonic functions are harmonic;
- InnerProductSpace/Harmonic contains only closure properties, and the only mean value result is circle averages on ℂ;
- Taylor.lean is one-variable only;
- the project Ch05 HarmonicApproximationLemma is an unproved Prop, and SimonGMT Chapter05/Basic.lean only re-exports HarmonicOn basics.
No comparator-accepted declaration can be reused. mean_value-a1 is still decomposing, so the children take the mean value identity as a hypothesis.

The pinned Mathlib does supply every tool the child proofs cite: HasFDerivAt.le_of_lip' (FDeriv/Basic.lean:897), integral_inter_add_sdiff (Bochner/Set.lean:114), norm_setIntegral_le_of_norm_le_const (:613), setIntegral_mono_set (:737), Measure.addHaar_ball (EqHaar.lean:456), ContDiffAt.isSymmSndFDerivAt (Symmetric.lean:533), abs_pow_sub_pow_le (Abs.lean:189), image_norm_le_of_norm_deriv_right_le_deriv_boundary (MeanValue.lean:298), norm_image_sub_le_of_norm_deriv_le_segment' (:325), iteratedFDeriv_two_apply (FTaylorSeries.lean:948), fderiv_clm_apply (CompCLM.lean:143), ContDiffOn.fderiv_of_isOpen (ContDiff/Defs.lean:907), fderiv_fun_sum (FDeriv/Add.lean:452) and opNorm_le_bound (Operator/Basic.lean:196).

Lean checks (/tmp/ie-decomp/All.lean, exit code 0):
- complete proofs of all six children use only propext, Classical.choice and Quot.sound;
- the exact frozen parent type compiles from these children plus a sorry-stub of dorag_ha_mean_value with its exact frozen type, which is the only source of sorryAx;
- the unparenthesized shifted-ball type is provably false, so the parenthesized form is used;
- all six names are unreserved.
