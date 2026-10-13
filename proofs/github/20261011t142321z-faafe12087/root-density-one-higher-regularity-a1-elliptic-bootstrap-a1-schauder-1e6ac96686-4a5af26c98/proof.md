# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.weak_eq_limit-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.weak_eq_limit-a1.uniform_limit_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4 and 5d of the parent proof (bounding an integral over the ball Bbar_r(0) that contains all supports), stated for a general compact set K. Let mu denote Lebesgue measure on R^n; all integrals are Bochner integrals for mu.
1. Finite measure. K is compact and mu is finite on compact sets, so mu(K) < infinity (IsCompact.measure_lt_top). Let M := mu(K) as a real number (M = mu.real K). Then M >= 0.
2. Choice of k0. Fix eps > 0 and put delta := eps / (M + 1) > 0. Uniform convergence on K in its metric form (Metric.tendstoUniformlyOn_iff) gives, for all sufficiently large k, |g(z) - f_k(z)| < delta for every z in K. Combine this with the two eventual hypotheses. This gives k0 such that every k >= k0 satisfies: (i) f_k is integrable; (ii) f_k(z) = 0 for all z not in K; (iii) |f_k(z) - g(z)| < delta for all z in K.
3. Fix k >= k0. Since f_k and g are integrable, the integral of f_k minus the integral of g equals the integral of f_k - g (integral_sub).
4. By (ii) and the hypothesis on g, f_k - g vanishes at every z not in K. So its integral over R^n equals its integral over K (setIntegral_eq_integral_of_forall_compl_eq_zero).
5. By (iii), |f_k(z) - g(z)| <= delta for every z in K, and mu(K) < infinity. Hence the absolute value of the integral of f_k - g over K is at most delta * M (norm_setIntegral_le_of_norm_le_const).
6. delta * M = eps * M / (M + 1) < eps, because M >= 0 and eps > 0 give eps * M < eps * (M + 1).
7. Steps 3 to 6 give |integral of f_k - integral of g| < eps for every k >= k0. Since eps > 0 was arbitrary, the integrals of f_k tend to the integral of g (Metric.tendsto_nhds). QED.

## Key steps

1. mu(K) < infinity since K is compact; put M := mu(K) >= 0
2. given eps > 0, choose k0 beyond which f_k is integrable, vanishes off K, and |f_k - g| < eps/(M+1) on K
3. integral of f_k minus integral of g = integral of (f_k - g) over R^n = integral of (f_k - g) over K
4. |integral over K of (f_k - g)| <= eps M/(M+1) < eps, so the integrals converge

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; sha256sum GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean`
- `rg -n 'theorem (setIntegral_eq_integral_of_forall_compl_eq_zero|norm_setIntegral_le_of_norm_le_const|norm_integral_le_of_norm_le_const|Continuous.integrable_of_hasCompactSupport|measure_closedBall_lt_top|tendsto_integral_filter_of_dominated_convergence|tendsto_integral_of_dominated_convergence)' <snapshot>/mathlib/Mathlib`
- `rg -n 'TendstoUniformlyOn.*integral|integral.*TendstoUniformly|tendsto_integral_of_tendstoUniformly|TendstoUniformly.*setIntegral' <snapshot>/mathlib/Mathlib (no match)`
- `rg -n -i uniform <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/*.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/*.lean; rg -ln TendstoUniformly <snapshot>/mathlib/Mathlib/MeasureTheory`
- `sed -n 100,215p <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean; sed -n 480,500p and 580,620p <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `rg -n 'theorem (ContinuousOn.integrable_of_hasCompactSupport|ContinuousOn.integrableOn_compact|HasCompactSupport.integrable|ContinuousOn.continuous_of_tsupport|continuous_of_continuousOn_of_tsupport)' <snapshot>/mathlib/Mathlib; rg -n 'theorem ContinuousOn.continuous_of|lemma ContinuousOn.continuous_of' <snapshot>/mathlib/Mathlib; sed -n 185,215p <snapshot>/mathlib/Mathlib/Topology/Algebra/Support.lean; sed -n 580,600p <snapshot>/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `rg -n 'theorem (Continuous.bounded_above_of_compact_support|HasCompactSupport.fderiv|ContDiff.continuous_fderiv|IsCompact.exists_bound_of_continuousOn|support_fderiv_subset|tsupport_fderiv_subset)' <snapshot>/mathlib/Mathlib; rg -n 'theorem (ContinuousOn.clm_apply|Continuous.clm_apply|le_opNorm₂|opNorm_le_bound₂)' <snapshot>/mathlib/Mathlib; rg -n 'theorem (Metric.tendstoUniformlyOn_iff|tendstoUniformlyOn_iff)' <snapshot>/mathlib/Mathlib`
- `rg -n -i 'tendstoUniformlyOn|weak_eq|weak equation|setIntegral_eq_integral' <snapshot>/project/GMT (no match)`
- `rg -n 'TendstoUniformlyOn|setIntegral_eq_integral_of_forall_compl_eq_zero|integrable_of_hasCompactSupport' lake-packages-25730c7c/simongmt/Poincare`
- `python3 scan of dag.json: sibling statuses (all 'decomposing'), depth distribution and depth-5 decomposition decisions, statements mentioning Integrable/TendstoUniformlyOn (closest: dohr_eb_lhr_dqwe_integrable_of_continuousAt, other branch, decomposing)`
- `rg -l -F <each new lean_name> over the run directory, GMT and simongmt/Poincare; git grep dohr_eb_sch_bu_wel over all workspace refs (no match)`
- `python3 -I: gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch05.main_theorem') and child_modules(..., 'contract'); lean_contract.validate_lean_statement on the three child statements and the parent`
- `LEAN_PATH=$(lake env printenv LEAN_PATH) lean -o <scratch>/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean; lean check/Probe.lean check/Probe2.lean (#check of all cited lemmas; Norm on the bilinear-form type fails at default maxSynthPendingDepth, works with 3)`
- `lean check/Types.lean, check/Children.lean, check/Assembly.lean; lean -o olean2/GMT/Ch05/Submission.olean sub/GMT/Ch05/Submission.lean; lean node/<key>_NodeChallenge.lean and node/<key>_NodeSolution.lean for the 3 children and the parent; lean node/Axioms.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-335f55150d/parent-child-handoff.json`

Snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Submission.lean is byte-identical to the snapshot Contract.lean (sha256 c966f51e...). Pinned Mathlib supplies every tool the children need: setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486), norm_setIntegral_le_of_norm_le_const (:613), Continuous.integrable_of_hasCompactSupport (LocallyIntegrable.lean:622), HasCompactSupport.intro, ContinuousOn.continuous_of_tsupport_subset (additive form of Support.lean:196), IsCompact.measure_lt_top, Metric.tendstoUniformlyOn_iff (MetricSpace/Pseudo/Basic.lean:142), ContinuousLinearMap.le_opNorm₂ (Bilinear.lean:71), ContinuousOn.clm_apply (BoundedLinearMaps.lean:476), support_fderiv_subset and HasCompactSupport.fderiv (FDeriv/Const.lean:379, 389), ContDiff.continuous_fderiv (ContDiff/Defs.lean:1271) and Real.rpow_le_rpow. Mathlib proves uniform-limit-of-integrals only for interval and circle integrals (DominatedConvergence.lean:182, CircleIntegral.lean:448). For localization it has only ContinuousOn.integrableOn_compact (LocallyIntegrable.lean:592). So children 1 and 2 are not restatements of single Mathlib lemmas. The project snapshot has no match for uniform limits of integrals or weak equations, and SimonGMT only uses the same basic Mathlib lemmas. dag.json: the selected node has no children. The closest generic node, dohr_eb_lhr_dqwe_integrable_of_continuousAt, is in another branch, is still decomposing and has a different type, so it is not reused. The three new names occur nowhere. Instance finding: Norm on the bilinear-form type fails at the default maxSynthPendingDepth and works with 3; only child 3's proof needs it. Lean checks: all child types elaborate in the comparator scope; all three children are proved; the frozen parent type is proved from the verbatim child types as hypotheses; comparator-style challenge/solution files for all four nodes compile; #print axioms gives propext, Classical.choice, Quot.sound.
