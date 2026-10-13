# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.lp_monotonicity-a1.fixed_cutoff_monotone-a1`
- Child DAG node: `root.tilt_excess_decay-a1.lp_monotonicity-a1.fixed_cutoff_monotone-a1.cutoff_mass_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 2 and 3 of the parent proof (Simon, Ch. 4, 4.3: differentiation of the cutoff mass I(t) = integral phi(r/t) dmu), stated for one radius t. Notation: r(x) := |x - y|, phi' := deriv phi, B_S(y) the closed ball, nu := mu restricted to B_S(y).

1. Properties of phi.
 (a) phi is C^1, so phi and phi' are continuous (ContDiff.continuous_deriv). phi is differentiable with derivative phi'(u) at every u (ContDiff.differentiable).
 (b) phi'(u) = 0 for u > T. The open set (T, infinity) is a neighbourhood of u on which phi = 0, so phi coincides near u with the zero function and phi'(u) = 0 (Filter.EventuallyEq.deriv_eq).
 (c) Bounds. The continuous functions phi and u -> u phi'(u) are bounded on the compact interval [0, T] (IsCompact.exists_bound_of_continuousOn): |phi(u)| <= K and |u phi'(u)| <= C for u in [0, T]. Taking u = 0 gives K >= 0 and C >= 0. For u > T, phi(u) = 0 by hypothesis and u phi'(u) = 0 by (b). Hence |phi(u)| <= K and |u phi'(u)| <= C for every u >= 0.

2. Vanishing off the ball. Let s > 0 with T s < S, and let x be outside B_S(y). Then r(x) > S > T s, so r(x)/s > T. Hence phi(r(x)/s) = 0 by hypothesis and phi'(r(x)/s) = 0 by 1(b).

3. Integrability, (a) and (b). The maps f(x) := phi(r(x)/t) and g(x) := (r(x)/t) phi'(r(x)/t) are continuous on E (compositions and products of continuous maps), hence a.e. strongly measurable for every measure. Since r(x)/t >= 0, step 1(c) gives |f| <= K and |g| <= C everywhere. As mu(B_S(y)) < infinity, f and g are integrable on B_S(y) (IntegrableOn.of_bound). By step 2 with s = t (note T t < S), f and g vanish outside B_S(y). So they are mu-integrable (IntegrableOn.integrable_of_forall_notMem_eq_zero). This proves (a) and (b).

4. Pointwise derivative. Fix x, write r := r(x), and let s > 0. The map u -> r/u has derivative (0 * s - r * 1)/s^2 = -r/s^2 at s (quotient rule). By the chain rule and 1(a), u -> phi(r/u) has derivative phi'(r/s)(-r/s^2) = -((r/s) phi'(r/s))/s at s.

5. Differentiation under the integral sign for nu. nu is a finite measure, because nu(E) = mu(B_S(y)) < infinity (isFiniteMeasure_restrict). Put F(s, x) := phi(r(x)/s) and F'(s, x) := -((r(x)/s) phi'(r(x)/s))/s, and let N := (t/2, infinity), a neighbourhood of t. We check the hypotheses of hasDerivAt_integral_of_dominated_loc_of_deriv_le for nu at t, with the set N and the constant bound 2C/t:
 - for every s, x -> F(s, x) is continuous, hence nu-a.e. strongly measurable;
 - F(t, .) = f is nu-integrable, since it is mu-integrable (step 3);
 - F'(t, .) = -g/t is continuous, hence nu-a.e. strongly measurable;
 - for every x and every s in N we have s > t/2 > 0, so |F'(s, x)| = |(r/s) phi'(r/s)|/s <= C/s <= 2C/t, by 1(c) (r/s >= 0) and C >= 0;
 - the constant 2C/t is nu-integrable because nu is finite;
 - for every x and every s in N, s > 0, so u -> F(u, x) has derivative F'(s, x) at s by step 4.
 Hence s -> integral F(s, x) dnu(x) has derivative integral F'(t, x) dnu(x) at t.

6. Back to mu. Since T > 0, the condition T s < S is equivalent to s < S/T, so (0, S/T) is an open neighbourhood of t. For s in (0, S/T), step 2 shows that F(s, .) vanishes off B_S(y). Hence integral F(s, x) dmu = integral over B_S(y) of F(s, x) dmu = integral F(s, x) dnu (setIntegral_eq_integral_of_forall_compl_eq_zero). So s -> integral F(s, x) dmu agrees with s -> integral F(s, x) dnu on a neighbourhood of t, and has the same derivative at t (HasDerivAt.congr_of_eventuallyEq). By linearity (integral of a negative, division by the constant t), integral F'(t, x) dnu = -(integral g dnu)/t. Also integral g dnu = integral g dmu, because g vanishes off B_S(y) (step 2 with s = t). Therefore s -> integral phi(r(x)/s) dmu(x) has derivative -(integral (r/t) phi'(r/t) dmu)/t at t, which is (c).

## Key steps

1. phi and phi' are continuous, phi' = 0 on (T, infinity), and |phi(u)| <= K, |u phi'(u)| <= C for all u >= 0 (compactness of [0, T]).
2. For s > 0 with T s < S, phi(r/s) and phi'(r/s) vanish outside B_S(y).
3. x -> phi(r/t) and x -> (r/t) phi'(r/t) are continuous, bounded on B_S(y) (finite measure) and zero outside, hence mu-integrable.
4. d/ds phi(r/s) = -((r/s) phi'(r/s))/s, bounded by 2C/t for s > t/2.
5. Differentiation under the integral sign for the finite measure nu = mu restricted to B_S(y) (hasDerivAt_integral_of_dominated_loc_of_deriv_le).
6. On the neighbourhood (0, S/T) of t the mu- and nu-integrals agree; transfer the derivative (HasDerivAt.congr_of_eventuallyEq) and rewrite its value as -(int (r/t) phi'(r/t) dmu)/t.

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
