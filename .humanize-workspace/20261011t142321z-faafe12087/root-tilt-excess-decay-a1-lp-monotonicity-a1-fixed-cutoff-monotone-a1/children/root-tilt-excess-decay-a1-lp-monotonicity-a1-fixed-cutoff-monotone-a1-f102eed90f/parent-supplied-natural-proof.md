# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.lp_monotonicity-a1.fixed_cutoff_monotone-a1`
- Child DAG node: `root.tilt_excess_decay-a1.lp_monotonicity-a1.fixed_cutoff_monotone-a1.cutoff_pairing_continuity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof (continuity of L), with the localisation of step 2 (Simon, Ch. 4, 4.3-4.4). Notation: r(x) := |x - y|, B_S(y) the closed ball, nu := mu restricted to B_S(y), and h(x) := (x - y).H(x).

1. Bound on phi. phi is continuous on the compact interval [0, T], so there is K with |phi(u)| <= K for u in [0, T] (IsCompact.exists_bound_of_continuousOn). Taking u = 0 gives K >= 0. For u > T, phi(u) = 0. Hence |phi(u)| <= K for all u >= 0.

2. Localisation. Since T > 0, T s < S iff s < S/T. So (0, S/T) is an open neighbourhood of t; it contains t because T t < S. Let s be in (0, S/T) and x outside B_S(y). Then r(x) > S > T s, so r(x)/s > T and phi(r(x)/s) = 0. Hence the integrand phi(r(x)/s) h(x) vanishes off B_S(y), and
 L(s) = integral over B_S(y) of phi(r(x)/s) h(x) dmu = integral phi(r(x)/s) h(x) dnu(x) =: L_nu(s)
 (setIntegral_eq_integral_of_forall_compl_eq_zero). So L = L_nu on a neighbourhood of t, and it suffices to show that L_nu is continuous at t (ContinuousAt.congr).

3. Dominated continuity. Apply continuousAt_of_dominated to F(s, x) := phi(r(x)/s) h(x), with respect to nu at t and with the bound G(x) := K S |H(x)|.
 - Measurability. H is nu-integrable (this is the hypothesis that H is mu-integrable on B_S(y)), hence nu-a.e. strongly measurable. So x -> (x - y, H(x)) is nu-a.e. strongly measurable into E x E. The inner product is continuous on E x E, so h is nu-a.e. strongly measurable (Continuous.comp_aestronglyMeasurable with continuous_inner). For every s, x -> phi(r(x)/s) is continuous. Hence each F(s, .) is nu-a.e. strongly measurable.
 - Domination. Take s in the neighbourhood (0, infinity) of t and x in B_S(y), which covers nu-a.e. x (ae_restrict_mem). Then r(x)/s >= 0, so |phi(r(x)/s)| <= K by step 1. Also |h(x)| <= |x - y| |H(x)| <= S |H(x)|, by Cauchy-Schwarz (norm_inner_le_norm) and |x - y| <= S. Hence |F(s, x)| <= K S |H(x)| = G(x).
 - Integrability of the bound. |H| is nu-integrable, hence so is G = K S |H|.
 - Pointwise continuity. For every x, s -> phi(r(x)/s) h(x) is continuous at t: since t != 0, s -> r(x)/s is continuous at t, phi is continuous, and h(x) is a constant.
 Therefore L_nu is continuous at t.

4. By step 2, L agrees with L_nu on a neighbourhood of t, so L is continuous at t.

## Key steps

1. |phi(u)| <= K for all u >= 0 (continuity on the compact [0, T] and phi = 0 beyond T).
2. On the neighbourhood (0, S/T) of t the integrand vanishes off B_S(y), so L equals its integral against nu = mu restricted to B_S(y).
3. continuousAt_of_dominated for nu with bound K S |H|: measurability via continuous_inner, domination via Cauchy-Schwarz and |x - y| <= S, pointwise continuity at t != 0.
4. ContinuousAt.congr transfers continuity from the nu-integral to L.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean <workspace>/GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Submission.lean <workspace>/GMT/Ch05/Submission.lean (both identical)`
- `rg -n 'ted_lpm_fcm_|aal_cfs_integrating_factor_deriv' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project (no match)`
- `rg -n "^theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le|^theorem continuousAt_of_dominated|^theorem IntegrableOn.integrable_of_forall_notMem_eq_zero|^lemma IntegrableOn.of_bound|^theorem setIntegral_eq_integral_of_forall_compl_eq_zero|^theorem ContDiff.continuous_deriv |^theorem Filter.EventuallyEq.deriv_eq|^theorem HasDerivAt.congr_of_eventuallyEq|^theorem monotoneOn_of_deriv_nonneg|^theorem integral_hasDerivAt_right|^theorem intervalIntegrable_rpow'|^theorem integral_div|^theorem integral_const_mul|^theorem integral_add |^protected theorem inner|^theorem continuous_inner|^theorem interior_Ioo" Analysis MeasureTheory Topology Order (cwd <snapshot>/mathlib/Mathlib)`
- `grep -rn 'exists_bound_of_continuousOn' <snapshot>/mathlib/Mathlib; grep -rn 'Integrable.of_bound|norm_inner_le_norm|AEStronglyMeasurable.inner|isFiniteMeasure_restrict' <snapshot>/mathlib/Mathlib`
- `python3 -I scan of dag.json: lean_name/status/lean_statement/candidate_commit/updated_at of monotonicity, cutoff and radial nodes (aal_cfs_*, allard52_am_*, ted_lpm_*, ted_lp_monotonicity)`
- `git show 99d4f685ff569eb9d68fc1e0d28ba77e7a3f22c4:GMT/Ch05/Submission.lean (accepted aal_cfs_integrating_factor_deriv); git show 2627b345844aca5f755b25ea3df419f11a6bb507:GMT/Ch05/Submission.lean (accepted aal_cfs_cutoff_pairing_continuousAt)`
- `grep -rl 'ted_lpm_fcm_' dag.json nodes DAG.md issue-workers.json; git grep -q 'ted_lpm_fcm_' <ref> -- GMT over all 774 unique local ref heads; git log --all -S'ted_lpm_fcm_' (no match anywhere)`
- `sed -n on /runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, child activation existing_by_name, _install_parent_supplied_child_handoff, decomposition validation) and store.py (refresh, update)`
- `python3 -I contract_scope(Contract.lean, 'GMT.Ch05.main_theorem') from verifier/gmt-compare.py; validate_lean_statement (verifier/lean_contract.py and _recursive_lean/lean_contract.py) on the three child types`
- `lake env lean Check/Types_{reuse,mass,pair,parent}.lean, Check/Assembly.lean, Check/Children.lean, Check/Full.lean, Check/Closure.lean (#print axioms / #check) in /tmp/fcm-decomp-1791832966/proj`
- `lake build GMT.Ch05.Submission (scratch copy with the four declarations inserted), then lake env lean Check/Sol_{reuse,mass,pair,parent}.lean (NodeSolution form: exact Submission.X)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Continuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-lp-monotonicity-a1-fixed-cutoff-monotone-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-lp-monotonicity-a1-fixed-cutoff-monotone-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-lp-monotonicity-a1-fixed-cutoff-monotone-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-lp-monotonicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-lp-monotonicity-a1/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-lp-monotonicity-a1-cutoff-squeeze-a1-int-85dadbafe4/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/fcm-decomp-1791832966/proj/Check/Types_reuse.lean`
- `/tmp/fcm-decomp-1791832966/proj/Check/Types_mass.lean`
- `/tmp/fcm-decomp-1791832966/proj/Check/Types_pair.lean`
- `/tmp/fcm-decomp-1791832966/proj/Check/Types_parent.lean`
- `/tmp/fcm-decomp-1791832966/proj/Check/Assembly.lean`
- `/tmp/fcm-decomp-1791832966/proj/Check/Children.lean`
- `/tmp/fcm-decomp-1791832966/proj/Check/Full.lean`
- `/tmp/fcm-decomp-1791832966/proj/Check/Sol_reuse.lean`
- `/tmp/fcm-decomp-1791832966/proj/Check/Sol_mass.lean`
- `/tmp/fcm-decomp-1791832966/proj/Check/Sol_pair.lean`
- `/tmp/fcm-decomp-1791832966/proj/Check/Sol_parent.lean`
- `/tmp/fcm-decomp-1791832966/proj/Check/Closure.lean`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. Its project Contract.lean and Submission.lean are byte-identical (cmp) to the workspace files.

No-match results: the snapshot project contains no ted_lpm_fcm_* or aal_cfs_integrating_factor_deriv. The prefix 'ted_lpm_fcm_' occurs nowhere in dag.json, nodes/, DAG.md, issue-workers.json, the 774 unique local ref heads or the git history, so both new names are globally unused.

Reused declaration: aal_cfs_integrating_factor_deriv.
- Accepted node root.affine_approximation-a1.lp_monotonicity-a1.cutoff_squeeze-a1.integrating_factor-a1, status accepted since 2026-10-12T15:21:51Z, candidate 99d4f685.
- The accepted source declares exactly the dag.json type string used here.
- Its proof recompiles with axioms {propext, Classical.choice, Quot.sound}.
- runtime.py _existing_lean_name_problem admits accepted cross-branch reuse with an identical type, and child activation maps it to the existing node. This node entered 'decomposing' at 19:17:55Z, after the acceptance.

Accepted cutoff lemmas not usable: aal_cfs_hasDerivAt_cutoff_integral and aal_cfs_cutoff_pairing_continuousAt need phi = 1 on (-inf, 1] and a cutoff at 1 + eps, which this node lacks. The allard52_am_cc_* nodes are unaccepted, so their names are reserved.

Mathlib lemmas used (snapshot paths under mathlib/Mathlib):
- hasDerivAt_integral_of_dominated_loc_of_deriv_le (Analysis/Calculus/ParametricIntegral.lean:286, set-neighbourhood form)
- continuousAt_of_dominated (MeasureTheory/Integral/Bochner/Basic.lean:458)
- IntegrableOn.integrable_of_forall_notMem_eq_zero (MeasureTheory/Integral/IntegrableOn.lean:453)
- IntegrableOn.of_bound (IntegrableOn.lean:174)
- setIntegral_eq_integral_of_forall_compl_eq_zero (MeasureTheory/Integral/Bochner/Set.lean:486)
- ContDiff.continuous_deriv (Analysis/Calculus/ContDiff/Deriv.lean:108)
- Filter.EventuallyEq.deriv_eq and HasDerivAt.congr_of_eventuallyEq (Analysis/Calculus/Deriv/Basic.lean:638, 606)
- monotoneOn_of_deriv_nonneg (Analysis/Calculus/Deriv/MeanValue.lean:411)
- intervalIntegral.integral_hasDerivAt_right (MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:725)
- intervalIntegrable_rpow' (Analysis/SpecialFunctions/Integrability/Basic.lean:47)
- continuous_inner (Analysis/InnerProductSpace/Continuous.lean:65)
- norm_inner_le_norm (Analysis/InnerProductSpace/Basic.lean:455)
- interior_Ioo (Topology/Order/OrderClosed.lean:603)

Import-closure gaps: MeasureTheory.AEStronglyMeasurable.inner (MeasureTheory/Function/StronglyMeasurable/Inner.lean:50) and Real.exp_one_lt_d9 are unknown constants after import GMT.Ch05.Submission. continuous_inner.comp_aestronglyMeasurable with prodMk is used instead. ContDiff.differentiable takes (n != 0) at this revision.

Lean checks (all under default maxHeartbeats):
- All child types elaborate in the comparator's NodeChallenge contract scope.
- Both new children are fully proved, and the parent assembly proves the frozen parent type from the three children.
- Full sorry-free chain, and NodeSolution checks (exact Submission.X) for all three children and the parent: axioms {propext, Classical.choice, Quot.sound}.
