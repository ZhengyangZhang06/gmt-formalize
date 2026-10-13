# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1`
- Child DAG node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1.affine_combine-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 10 (combination) of the parent proof, with b := (2^n − 1)a, c := c_m, k := (m+1)K and c' := c_{m+1}. M stands for μ(B_1(x)), which may be ∞. Real coefficients enter through ENNReal.ofReal.

1. Real facts. δ² ≥ 0 and δ² ≤ 1, so δ⁴ = δ²·δ² ≤ δ². With bc ≥ 0 this gives bc·δ⁴ ≤ bc·δ². Also 1 + bδ² ≥ 0, cδ² ≥ 0 and kδ² ≥ 0.

2. First coefficient. (1 + bδ²)(1 + cδ²) = 1 + (b + c)δ² + bc·δ⁴ ≤ 1 + (b + c + bc)δ² ≤ 1 + c'δ². The first inequality is step 1. The second multiplies b + c + bc ≤ c' by δ² ≥ 0.

3. Second coefficient. (1 + bδ²)·cδ² + kδ² = cδ² + bc·δ⁴ + kδ² ≤ cδ² + bc·δ² + kδ² = ((1 + b)c + k)δ² ≤ c'δ². This uses step 1 and (1 + b)c + k ≤ c' multiplied by δ² ≥ 0.

4. Substitution in [0,∞]. Multiplication by ofReal(1 + bδ²) and addition are monotone, so the two hypotheses give
 X ≤ ofReal(1 + bδ²)·(ofReal(1 + cδ²)·M + ofReal(cδ²)) + ofReal(kδ²).
 Distribute: ofReal(1 + bδ²)·(ofReal(1 + cδ²)·M + ofReal(cδ²)) = ofReal(1 + bδ²)·ofReal(1 + cδ²)·M + ofReal(1 + bδ²)·ofReal(cδ²). Then use ofReal(p)·ofReal(q) = ofReal(pq) for p = 1 + bδ² ≥ 0 (ENNReal.ofReal_mul), and ofReal(p) + ofReal(q) = ofReal(p + q) for p, q ≥ 0 (ENNReal.ofReal_add). The right-hand side becomes
 ofReal((1 + bδ²)(1 + cδ²))·M + ofReal((1 + bδ²)·cδ² + kδ²).
 These identities hold in [0,∞] also when M = ∞.

5. Conclusion. By steps 2 and 3, monotonicity of ofReal, monotonicity of multiplication by M, and monotonicity of addition:
 X ≤ ofReal(1 + c'δ²)·M + ofReal(c'δ²). ∎

## Key steps

1. δ⁴ ≤ δ² and bc ≥ 0, so bcδ⁴ ≤ bcδ²
2. (1 + bδ²)(1 + cδ²) ≤ 1 + (b + c + bc)δ² ≤ 1 + c'δ²
3. (1 + bδ²)cδ² + kδ² ≤ ((1 + b)c + k)δ² ≤ c'δ²
4. substitute the bound on Y, distribute with ENNReal.ofReal_mul/ofReal_add (valid for M = ∞), then use monotonicity

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
