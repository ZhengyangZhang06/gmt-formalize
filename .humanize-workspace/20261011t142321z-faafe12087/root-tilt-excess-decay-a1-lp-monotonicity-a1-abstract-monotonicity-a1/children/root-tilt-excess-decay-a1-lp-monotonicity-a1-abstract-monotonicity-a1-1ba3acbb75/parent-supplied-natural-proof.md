# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.lp_monotonicity-a1.abstract_monotonicity-a1`
- Child DAG node: `root.tilt_excess_decay-a1.lp_monotonicity-a1.abstract_monotonicity-a1.exp_perturbation_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 11 (a)-(d) of the parent proof, with c renamed q and the parent's u = -integral_0^r a_0 (a_0 being the parent's limit coefficient) replaced by an arbitrary real u.

1. Put b := (Lambda/4) q. Then b >= 0 (Lambda > 0, q >= 0), b <= (Lambda/4) * 1 = Lambda/4 (q <= 1, Lambda/4 >= 0), and |u| <= b, i.e. -b <= u <= b.
2. (a) -Lambda <= -b <= u <= b <= Lambda/4 <= Lambda (b <= Lambda/4 and Lambda > 0), so by monotonicity of exp, e^(-Lambda) <= e^u <= e^Lambda.
3. Key estimate: |e^u - 1| <= e^b b.
 - Case u >= 0. Then e^u >= 1 + u >= 1 (Real.add_one_le_exp), so |e^u - 1| = e^u - 1. Also e^(-u) >= 1 - u (Real.add_one_le_exp at -u) and e^u e^(-u) = 1; multiplying e^(-u) >= 1 - u by e^u > 0 gives 1 >= (1 - u) e^u, i.e. e^u - 1 <= u e^u. Since 0 <= u <= b and 0 < e^u <= e^b, u e^u <= b e^b.
 - Case u <= 0. Then e^u <= 1, so |e^u - 1| = 1 - e^u, and e^u >= 1 + u gives 1 - e^u <= -u <= b. Since b >= 0 and e^b >= 1, b <= b e^b.
4. (b) Since b <= Lambda/4, e^b <= e^(Lambda/4), so by item 3 and b >= 0, |e^u - 1| <= e^(Lambda/4) b = (e^(Lambda/4)/4) (Lambda q). Moreover e^(Lambda/4) <= e^(Lambda/2) (Lambda/4 <= Lambda/2) and e^(Lambda/4) > 0, so e^(Lambda/4)/4 <= e^(Lambda/4)/2 <= e^(Lambda/2)/2. Multiplying by Lambda q >= 0 gives |e^u - 1| <= (e^(Lambda/2)/2) Lambda q.
5. (c) Assume Lambda <= 1. Then 0 < Lambda/4 <= 1/4, so |Lambda/4| <= 1 and Real.abs_exp_sub_one_le gives |e^(Lambda/4) - 1| <= 2 (Lambda/4) <= 1/2; hence e^(Lambda/4) <= 3/2 <= 4. By item 3 and e^b <= e^(Lambda/4): |e^u - 1| <= e^(Lambda/4) b <= 4 b = Lambda q.

## Key steps

1. b := (Lambda/4) q lies in [0, Lambda/4] and |u| <= b, which gives e^(-Lambda) <= e^u <= e^Lambda.
2. |e^u - 1| <= e^b b, from e^x >= 1 + x in the cases u >= 0 and u <= 0.
3. e^b b <= (e^(Lambda/4)/4) Lambda q <= (e^(Lambda/2)/2) Lambda q.
4. If Lambda <= 1, Real.abs_exp_sub_one_le gives e^(Lambda/4) <= 3/2 <= 4, so |e^u - 1| <= 4 b = Lambda q.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean (snapshot = .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7)`
- `rg -n 'ted_lpm_am_|ted_lpm_abstract_monotonicity' <snapshot>/project (no match)`
- `rg -n 'theorem abs_exp_sub_one_le|theorem add_one_le_exp |theorem tendsto_integral_filter_of_dominated_convergence|theorem norm_integral_le_of_norm_le |theorem intervalIntegrable_rpow' |theorem integral_rpow |theorem tendsto_integral_of_dominated_convergence |theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem le_of_tendsto_of_tendsto'|theorem ContinuousOn.aestronglyMeasurable|theorem tendsto_one_div_add_atTop_nhds_zero_nat|theorem rpow_le_rpow_of_exponent_le |theorem div_rpow |theorem ofReal_rpow_of_nonneg' <snapshot>/mathlib/Mathlib`
- `rg -n 'protected theorem contDiff|protected theorem monotone|theorem zero_of_nonpos|theorem one_of_one_le|theorem nonneg|theorem le_one|monotone' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `python3 -I scan of dag.json (411 nodes): lean_name/status/lean_statement; whitespace-normalized equality of the five child types against every node; name-collision check; grep -rl 'ted_lpm_am_' dag.json nodes; git log --all --oneline -S 'ted_lpm_am_' (no match)`
- `read nodes/*/decomposition-v*.json and decomposition-audit-v*.json (aal monotonicity_core, dohr local_monotonicity, curvature_holder sibling) and GMT/Scratch/aal_mrc/README.md + aal_mrc_split_all.lean.txt (template proofs), swarm-project.json (max_nodes), problem.md:477`
- `lake env lean -o /tmp/ted-lpm-am-decomp/build/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean; lean on ted_lpm_am_split_all.lean.txt, the axiom-sibling variant, the #count_heartbeats variant, and Facts.lean (#check of all cited lemmas)`
- `verifier/gmt-compare.py child_modules (contract mode) + verifier/lean_contract.validate_lean_statement on the five child types and the parent type; NodeChallenge against the contract build; NodeSolution against a lean --root build containing the split`
- `runtime /runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/leaf_verification.py check_source_delta (identical in gmt-claude-d253855dab51) on each child and the assembly, with negative controls`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-lp-monotonicity-a1-abstract-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-lp-monotonicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-lp-monotonicity-a1-curvature-holder-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-local-monotonicity-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/aal_mrc/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/aal_mrc/aal_mrc_split_all.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/ted_lpm_am/ted_lpm_am_split_all.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/ted_lpm_am/README.md`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. Its project Contract.lean and Submission.lean are byte-identical (cmp) to the workspace copies.

No-match results: the snapshot project has no ted_lpm_am_* or ted_lpm_abstract_monotonicity declaration, and the prefix ted_lpm_am_ occurs nowhere in dag.json, nodes/ or git history. No node among the 411 in dag.json has any of the five child types. The accepted aal_monotonicity_of_radial_identity needs an identity with a weight w for all C^1 cutoffs, which (A5) cannot supply, so nothing is reused.

Pinned Mathlib supplies every cited fact (mathlib/Mathlib/...):
- Real.smoothTransition contDiff/monotone/one_of_one_le/zero_of_nonpos/nonneg/le_one: Analysis/SpecialFunctions/SmoothTransition.lean:205, 222, 161, 168, 190, 187
- Real.abs_exp_sub_one_le and Real.add_one_le_exp: Analysis/Complex/Exponential.lean:533, 632
- tendsto_integral_of_dominated_convergence: MeasureTheory/Integral/DominatedConvergence.lean:57; intervalIntegral.tendsto_integral_filter_of_dominated_convergence: same file, line 170
- intervalIntegral.norm_integral_le_of_norm_le: MeasureTheory/Integral/IntervalIntegral/Basic.lean:756
- intervalIntegrable_rpow': Analysis/SpecialFunctions/Integrability/Basic.lean:47; integral_rpow: Analysis/SpecialFunctions/Integrals/Basic.lean:146
- setIntegral_eq_integral_of_forall_compl_eq_zero: MeasureTheory/Integral/Bochner/Set.lean:486
- ContinuousOn.aestronglyMeasurable: MeasureTheory/Integral/IntegrableOn.lean:791
- le_of_tendsto_of_tendsto': Topology/Order/OrderClosed.lean:480
- tendsto_one_div_add_atTop_nhds_zero_nat: Analysis/SpecificLimits/Basic.lean:70
- Real.div_rpow and Real.rpow_le_rpow_of_exponent_le: Analysis/SpecialFunctions/Pow/Real.lean:487, 616; ENNReal.ofReal_rpow_of_nonneg: Analysis/SpecialFunctions/Pow/NNReal.lean:971
All elaborate in the contract's import closure (#check).

Lean evidence, stored in GMT/Scratch/ted_lpm_am with SHA256SUMS:
- The five children compile with complete proofs, each depending only on propext, Classical.choice and Quot.sound.
- From them, the frozen ted_lpm_abstract_monotonicity compiles, depending only on those three and the two siblings.
- Heartbeats: 3.6k-11k per child and 65k for the assembly, against a 200k limit.
- The comparator's NodeChallenge and NodeSolution modules pass for all five children and for the parent.
- The runtime leaf gate accepts each child and the assembly as single theorems.
