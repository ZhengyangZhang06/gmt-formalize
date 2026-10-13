# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.lp_monotonicity-a1.abstract_monotonicity-a1`
- Child DAG node: `root.tilt_excess_decay-a1.lp_monotonicity-a1.abstract_monotonicity-a1.cutoff_integral_tendsto-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 8 of the parent proof (restriction to B_S(y) and dominated convergence), written for a general integrand g; the parent applies it with g = 1 and g(x) = (x - y).H(x).

1. t <= S: since T >= 1 and t > 0, t = 1 * t <= T t <= S. Hence the closed ball B_t(y) is contained in B_S(y).
2. Let nu := mu restricted to B_S(y). Since g is mu-integrable on B_S(y), g is nu-integrable; in particular g is nu-a.e. strongly measurable and |g| is nu-integrable.
3. Vanishing off B_S(y). If x is not in B_S(y), then |x - y| > S >= T t, so |x - y|/t >= T (as t > 0), hence phi_k(|x - y|/t) = 0 and phi_k(|x - y|/t) g(x) = 0 for every k. Therefore, for every k, integral_E phi_k(|x - y|/t) g dmu = integral over B_S(y) of phi_k(|x - y|/t) g dmu = integral phi_k(|x - y|/t) g dnu (setIntegral_eq_integral_of_forall_compl_eq_zero).
4. The limit value. Closed balls are measurable, so integral 1_{B_t(y)} g dnu = integral over B_t(y) of g d(nu) (integral_indicator) = integral over B_t(y) ∩ B_S(y) of g dmu (Measure.restrict_restrict), and B_t(y) ∩ B_S(y) = B_t(y) by item 1. So the claimed limit equals integral 1_{B_t(y)} g dnu.
5. Dominated convergence for nu (tendsto_integral_of_dominated_convergence) with bound |g|:
 (a) each integrand x -> phi_k(|x - y|/t) g(x) is nu-a.e. strongly measurable, because phi_k composed with the continuous map x -> |x - y|/t is continuous and g is nu-a.e. strongly measurable;
 (b) |phi_k(|x - y|/t) g(x)| <= |g(x)| for every x and k, because 0 <= phi_k <= 1; and |g| is nu-integrable (item 2);
 (c) pointwise limit, for every x: if x is in B_t(y), then |x - y| <= t, so |x - y|/t <= 1, phi_k(|x - y|/t) = 1 for every k, and the sequence is constantly g(x) = 1_{B_t(y)}(x) g(x); if x is not in B_t(y), then |x - y| > t, so |x - y|/t > 1, hence phi_k(|x - y|/t) = 0 for all large k and the sequence is eventually 0 = 1_{B_t(y)}(x) g(x).
 Hence integral phi_k(|x - y|/t) g dnu -> integral 1_{B_t(y)} g dnu.
6. By items 3, 4 and 5, integral_E phi_k(|x - y|/t) g dmu -> integral over B_t(y) of g dmu.

## Key steps

1. t <= T t <= S, so B_t(y) is contained in B_S(y).
2. The integrand vanishes off B_S(y), so each mu-integral equals the integral for nu = mu restricted to B_S(y).
3. The target equals the nu-integral of 1_{B_t(y)} g.
4. Dominated convergence with bound |g|: the integrand is constantly g on B_t(y) and eventually 0 off B_t(y).

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
