# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1`
- Child DAG node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1.one_point_ball_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof (the one-point case of Simon 8.5.10, printed (8)). Here the cylinder is replaced by the closed ball that contains it; the parent applies measure monotonicity to the cylinder itself. The hypotheses p(y) = x and ‖y − p(y)‖ < ε are replaced by their consequence ‖y − x‖ < ε. Notation: B_r(w) := closedBall w r. Inequalities between measures are in [0,∞], real coefficients enter through ENNReal.ofReal, and r^n means ofReal(r)^n.

1. Elementary bounds. From 0 < δ ≤ 1/2: δ² ≤ 1/4 and δ⁴ = δ²·δ² ≤ δ². Hence ε ≤ δ⁴ ≤ δ² ≤ 1/4. So 0 < σ ≤ δ² ≤ 1/4 < 3/4 ≤ 1 − ε < 1. In particular σ ∈ (0,1), 1 − ε ∈ (0,1) and σ ≤ 1 − ε.

2. Monotonicity. Put f(r) := ofReal(e^{εr})·μ(B_r(y))/ofReal(r)^n. Hypothesis (M_y), applied to σ ≤ 1 − ε in (0,1), gives f(σ) ≤ f(1 − ε).

3. Lower end. Since εσ ≥ 0, e^{εσ} ≥ 1 and ofReal(e^{εσ}) ≥ 1. So μ(B_σ(y)) = 1·μ(B_σ(y)) ≤ ofReal(e^{εσ})·μ(B_σ(y)). Dividing by ofReal(σ)^n (division by a fixed element of [0,∞] is monotone, ENNReal.div_le_div_right) gives μ(B_σ(y))/σ^n ≤ f(σ).

4. Upper end.
 (a) Ball inclusion. If ‖z − y‖ ≤ 1 − ε, then ‖z − x‖ ≤ ‖z − y‖ + ‖y − x‖ < (1 − ε) + ε = 1. So B_{1−ε}(y) ⊆ B_1(x), and μ(B_{1−ε}(y)) ≤ μ(B_1(x)).
 (b) ε(1 − ε) = ε − ε² ≤ ε, so e^{ε(1−ε)} ≤ e^ε and ofReal(e^{ε(1−ε)}) ≤ ofReal(e^ε).
 Since multiplication and division by a fixed denominator are monotone in [0,∞], f(1 − ε) ≤ ofReal(e^ε)·μ(B_1(x))/ofReal(1 − ε)^n.

5. Rewriting. Since 1 − ε > 0, ofReal(1 − ε)^n = ofReal((1 − ε)^n) (ENNReal.ofReal_pow). Since (1 − ε)^n > 0, ofReal(e^ε)/ofReal((1 − ε)^n) = ofReal(e^ε/(1 − ε)^n) (ENNReal.ofReal_div_of_pos). With a·b/c = (a/c)·b in [0,∞] (ENNReal.mul_div_right_comm):
 ofReal(e^ε)·μ(B_1(x))/ofReal(1 − ε)^n = ofReal(e^ε/(1 − ε)^n)·μ(B_1(x)).

6. The real inequality e^ε/(1 − ε)^n ≤ 1 + 2^{n+2}δ².
 (F2) Since 0 ≤ ε < 1, e^ε ≤ 1/(1 − ε) (Real.exp_bound_div_one_sub_of_interval). Also 1/(1 − ε) ≤ 1 + 2ε, because (1 + 2ε)(1 − ε) = 1 + ε − 2ε² ≥ 1 when 0 ≤ ε ≤ 1/2. Hence e^ε ≤ 1 + 2ε.
 (F1) For 0 ≤ u ≤ 1 and k ∈ ℕ, (1 + u)^k ≤ 1 + (2^k − 1)u. Induct on k. For k = 0 both sides equal 1. If it holds for k, then (1 + u)^{k+1} = (1 + u)^k(1 + u) ≤ (1 + (2^k − 1)u)(1 + u) = 1 + 2^k·u + (2^k − 1)u² ≤ 1 + 2^k·u + (2^k − 1)u = 1 + (2^{k+1} − 1)u. This uses 1 + u ≥ 0, u² ≤ u and 2^k − 1 ≥ 0.
 Now 1/(1 − ε)^n = (1/(1 − ε))^n ≤ (1 + 2ε)^n ≤ 1 + (2^n − 1)·2ε. The first step uses 0 ≤ 1/(1 − ε) ≤ 1 + 2ε and monotonicity of t ↦ t^n on [0,∞). The second is (F1) with u = 2ε ∈ [0, 1/2].
 Both factors below are nonnegative, so
 e^ε/(1 − ε)^n = e^ε·(1/(1 − ε)^n) ≤ (1 + 2ε)(1 + (2^n − 1)·2ε) = 1 + 2^n·2ε + (2^n − 1)·4ε²
  ≤ 1 + 2^n·2ε + 2^n·4ε² ≤ 1 + 2^n·2ε + 2^n·2ε = 1 + 2^{n+2}ε ≤ 1 + 2^{n+2}δ².
 The steps use 2^n − 1 ≤ 2^n, then 4ε² ≤ 2ε (as ε ≤ 1/2), and finally ε ≤ δ².

7. Conclusion. Chain steps 3, 2, 4, 5 and 6; ofReal is monotone and multiplication by μ(B_1(x)) is monotone in [0,∞]:
 μ(B_σ(y))/σ^n ≤ f(σ) ≤ f(1 − ε) ≤ ofReal(e^ε)·μ(B_1(x))/ofReal(1 − ε)^n = ofReal(e^ε/(1 − ε)^n)·μ(B_1(x)) ≤ ofReal(1 + 2^{n+2}δ²)·μ(B_1(x)). ∎

## Key steps

1. ε ≤ δ⁴ ≤ δ² ≤ 1/4, so σ ≤ 1/4 < 1 − ε and σ, 1 − ε ∈ (0,1)
2. (M_y) gives f(σ) ≤ f(1 − ε); e^{εσ} ≥ 1 gives μ(B_σ(y))/σ^n ≤ f(σ)
3. B_{1−ε}(y) ⊆ B_1(x) and e^{ε(1−ε)} ≤ e^ε give f(1 − ε) ≤ ofReal(e^ε)μ(B_1(x))/ofReal(1 − ε)^n = ofReal(e^ε/(1 − ε)^n)·μ(B_1(x))
4. e^ε ≤ 1/(1 − ε) ≤ 1 + 2ε and (1 + u)^k ≤ 1 + (2^k − 1)u on [0,1] give e^ε/(1 − ε)^n ≤ (1 + 2ε)(1 + (2^n − 1)2ε) ≤ 1 + 2^{n+2}ε ≤ 1 + 2^{n+2}δ²

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum of snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean and GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'theorem (one_add_pow_le|pow_le_one_add|one_add_mul_le_pow|add_pow_le_pow_mul_pow_of_sq_le_sq|one_add_pow_le_pow_one_add|pow_le_pow_of_le_one|sub_one_le_pow)' mathlib/Mathlib ; rg -n '\(1 \+ [a-z]\) \^ [a-z] ≤ 1 \+' mathlib/Mathlib`
- `rg -n 'theorem exp_bound_div_one_sub_of_interval|theorem add_one_le_exp|theorem exp_le_one_add|theorem one_sub_le_exp_neg|theorem exp_bound' mathlib/Mathlib`
- `rg -n 'offDiag.*Nonempty|Nonempty.*offDiag|offDiag_nonempty' mathlib/Mathlib ; rg -n 'theorem one_lt_card' mathlib/Mathlib/Data/Finset/Card.lean ; rg -n 'theorem mem_offDiag' mathlib/Mathlib/Data/Finset/Prod.lean`
- `rg/grep for prod_fiberwise_of_maps_to, measure_biUnion_finset, ENNReal sum_div / mul_div_mul_left / div_le_div_left / mul_div_right_comm / ofReal_div_of_pos, LinearMap.continuous_of_finiteDimensional, one_le_pow₀ / pow_le_pow_left₀ / pow_le_pow_right₀ in mathlib/Mathlib`
- `#check from import GMT.Ch08.Submission (/tmp/ccb-decomp-v1/Probe.lean, Probe2.lean): Grassmannian.project, Finset.sum_fiberwise_of_maps_to, measure_biUnion_finset, Finset.exists_min_image, one_add_mul_le_pow, ENNReal.sum_div, ENNReal.mul_div_mul_left, ENNReal.div_le_div_left, ENNReal.mul_div_right_comm, ENNReal.ofReal_div_of_pos, Real.exp_bound_div_one_sub_of_interval, LinearMap.continuous_of_finiteDimensional, Finset.one_lt_card_iff_nontrivial (Finset.offDiag_nonempty: unknown constant); example proofs of linearity (simp [Grassmannian.project, map_sub]) and continuity (projectionLinearMap.continuous_of_finiteDimensional) of Grassmannian.project`
- `grep -n 'theorem|def|abbrev' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean (Euclidean, Grassmannian, projectionLinearMap, project, project_project; no norm-contraction lemma for v − project v)`
- `python3 -I /tmp/ccb-decomp-v1/scripts/gen.py (verifier lean_contract.validate_lean_statement + gmt-compare.py layout/child_modules in contract mode on the four lean_statements)`
- `lake env lean /tmp/ccb-decomp-v1/compform/C{1,2,3,4}_Challenge.lean, /tmp/ccb-decomp-v1/assembly/Assembly.lean, Full.lean, FullAxiomComp.lean (with #print axioms)`
- `grep -c of intcpt_allard_ccb_* names in dag.json, grep -rl in the run directory, git grep over all 314 refs (0 hits)`
- `read nodes/root-integral-compactness-a1-allard-lemma-a1-weighted-radial-monotonicity-a1/decomposition-v1.json and decomposition-audit-v1.json (precedent: an uncle dependency is passed to a child as an explicit hypothesis)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Set/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Finset/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Finset/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/BigOperators.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-cylinder-cluster-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-weighted-radial-monotonicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-weighted-radial-monotonicity-a1/decomposition-audit-v1.json`
- `/tmp/ccb-decomp-v1/compform/C1_Challenge.lean`
- `/tmp/ccb-decomp-v1/assembly/Assembly.lean`
- `/tmp/ccb-decomp-v1/assembly/Full.lean`
- `/tmp/ccb-decomp-v1/assembly/FullAxiomComp.lean`

Snapshot provenance:
- The snapshot is project 63436ae6 with Mathlib 25730c7c. Its Contract is byte-identical to the workspace Contract and Submission.

Projection facts:
- Grassmannian.project P is defined as the linear map Grassmannian.projectionLinearMap P (SimonGMT Chapter08/Varifold.lean:82,105). So q = id − p is linear, and p is continuous by LinearMap.continuous_of_finiteDimensional.
- No contraction lemma ‖v − p v‖ ≤ ‖v‖ exists, and none is needed: the fibre identity q(y − y') = y − y' for p(y) = p(y') = x suffices.

Lemmas absent from Mathlib, and what replaces them:
- There is no lemma (1+u)^n ≤ 1 + (2^n − 1)u. The only nearby result is the rpow Bernoulli bound at Analysis/Convex/SpecificFunctions/Basic.lean:166. (F1) is therefore proved inline by induction in the two children that use it.
- Finset.offDiag_nonempty does not exist; only Set.offDiag_nonempty exists (Data/Set/Prod.lean:559). Finset.one_lt_card (Data/Finset/Card.lean:747), Finset.mem_offDiag (Data/Finset/Prod.lean:266) and Finset.exists_min_image give the minimal distance instead.

Lemmas used:
- e^ε ≤ 1/(1 − ε) is Real.exp_bound_div_one_sub_of_interval (Analysis/Complex/Exponential.lean:617).
- Grouping: Finset.sum_fiberwise_of_maps_to (the additive form of prod_fiberwise_of_maps_to, Algebra/BigOperators/Group/Finset/Basic.lean:264) and measure_biUnion_finset (MeasureTheory/Measure/Basic.lean:150).
- Division in [0,∞]: ENNReal.sum_div (Basic/ENNReal/BigOperators.lean:143), and ENNReal.mul_div_mul_left, div_le_div_left, mul_div_right_comm and ofReal_div_of_pos (Basic/ENNReal/Inv.lean:264, 471, 194, 960).
- Powers: one_le_pow₀, pow_le_pow_right₀ and pow_le_pow_left₀ (Algebra/Order/GroupWithZero/Basic.lean:483, 500, 513).
- All of these were #checked from import GMT.Ch08.Submission.

Lean checks:
- All four child statements pass validate_lean_statement and elaborate in comparator form.
- The parent's frozen type is proved from sorried children with a sorry-free assembly.
- All four children are fully proved with axioms propext, Classical.choice, Quot.sound; the comparator-form exact targets are accepted.

Names:
- The four lean_names are unused in dag.json, in the run directory and in the git refs.
