# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_limit-a1`
- Child DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_limit-a1.interval_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 and the first two bullets of step 7 of the parent proof.

Notation: beta := n/p, kappa := (p - n)/(4p), b(tau) := 2 kappa Lambda R^(-1) (tau/R)^(-beta) (the majorant in the eventual hypothesis, written 2 * ((p - n) / (4 * p)) * Λ / R * (τ / R) ^ (-((n : ℝ) / p)) in Lean), and C := 2 kappa Lambda R^(-1) R^beta. Fix k_0 such that the eventual hypothesis holds for every k >= k_0. Since 0 <= n < p, we have p > 0 and 0 <= beta < 1. As t > 0, the interval integral integral_0^t involves only the values on (0, t].

1. Rewriting b. For tau >= 0 and R > 0, the quotient rule for real powers of nonnegative bases gives (tau/R)^(-beta) = tau^(-beta)/R^(-beta) = tau^(-beta) R^beta. This also holds at tau = 0 under the convention 0^x = 0 for x != 0 and 0^0 = 1 used by Real.rpow. Hence b(tau) = C tau^(-beta) for every tau >= 0.

2. Integrability of b. Since -beta > -1, tau -> tau^(-beta) is integrable on [0, t], and so is C tau^(-beta). By step 1, b equals this function on [0, t], so b is interval integrable on [0, t].

3. Value of integral_0^t b. By step 1 and the power rule (valid because -beta > -1),
 integral_0^t b = C integral_0^t tau^(-beta) dtau = C (t^(1-beta) - 0^(1-beta))/(1 - beta) = C t^(1-beta)/(1 - beta),
 because 1 - beta > 0 gives 0^(1-beta) = 0.
 Since 1 - beta = (p - n)/p, we get 2 kappa/(1 - beta) = (2(p - n)/(4p))(p/(p - n)) = 1/2. Also R^beta/R = 1/R^(1-beta).
 Therefore integral_0^t b = (Lambda/2) t^(1-beta)/R^(1-beta) = (Lambda/2)(t/R)^(1-beta) = (Lambda/2)(t/R)^(1 - n/p), using (t/R)^(1-beta) = t^(1-beta)/R^(1-beta) for t, R >= 0.

4. Dominated convergence. For k >= k_0:
 (a) a_k is continuous at every point of (0, t]. So it is continuous on (0, t], hence a.e.-strongly measurable for Lebesgue measure restricted to (0, t].
 (b) |a_k(tau)| <= b(tau) for every tau in (0, t].
 By step 2, b is integrable on (0, t], and a_k(tau) -> g(tau) for every tau in (0, t]. The dominated convergence theorem for interval integrals, along the filter atTop in k and with (a) and (b) holding eventually, gives integral_0^t a_k -> integral_0^t g. This is the first conclusion.

5. Bound. Fix k >= k_0. By (a) and (b), a_k is integrable on (0, t] and |a_k| <= b there. Hence |integral_0^t a_k| <= integral_0^t |a_k| <= integral_0^t b.
 By step 4 and continuity of the absolute value, |integral_0^t a_k| -> |integral_0^t g|. A limit of quantities that are eventually <= integral_0^t b is itself <= integral_0^t b. With step 3, |integral_0^t g| <= integral_0^t b = (Lambda/2)(t/R)^(1 - n/p).

## Key steps

1. b(tau) = C tau^(-n/p) on [0, infinity) with C = 2 kappa Lambda R^(-1) R^(n/p), and -n/p > -1, so b is integrable on (0, t].
2. integral_0^t b = C t^(1-n/p)/(1 - n/p) = (Lambda/2)(t/R)^(1 - n/p), since 2 kappa/(1 - n/p) = 1/2.
3. Eventually each a_k is continuous, hence measurable, and dominated by b on (0, t]; with pointwise convergence, dominated convergence for interval integrals gives integral_0^t a_k -> integral_0^t g.
4. |integral_0^t a_k| <= integral_0^t b eventually; pass to the limit.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean`
- `grep -rl 'allard52_amcl_cutoff_sequence|allard52_amcl_radial_cutoff_tendsto|allard52_amcl_interval_limit|allard52_amcl_annular_lintegral_le|allard52_amcl_' over dag.json, <snapshot>/project, <snapshot>/mathlib/Mathlib (*.lean), .humanize; git log --all -S allard52_amcl`
- `grep -rn -c 'smoothTransition|dominated_convergence|setLIntegral_iUnion|intervalIntegrable_rpow|integral_rpow' <snapshot>/project --include=*.lean`
- `grep -n over <snapshot>/mathlib/Mathlib for: setLIntegral_iUnion_of_directed, lintegral_mono_set, tendsto_integral_of_dominated_convergence, tendsto_integral_filter_of_dominated_convergence, norm_integral_le_of_norm_le, intervalIntegrable_congr, integral_rpow, intervalIntegrable_rpow', abs_exp_sub_one_le, smoothTransition lemmas, setIntegral_eq_integral_of_forall_compl_eq_zero, setIntegral_const, integral_indicator, integrableOn_const, measureReal_def, AEStronglyMeasurable.inner, continuous_inner, div_rpow, rpow_neg, rpow_sub, zero_rpow, integral_congr, integral_const_mul, exists_nat_one_div_lt, Monotone.directed_le, eventually_lt_nhds, tendsto_natCast_atTop_atTop`
- `python3 over dag.json: status and lean_statement of fixed_cutoff-a1 and of related nodes (aal_monotonicity_of_radial_identity, ted_lpm_abstract_monotonicity, aal_cutoff_integrating_factor_squeeze, aal_cfs_*, dohr_local_monotonicity, aal_l1th_exists_cutoff)`
- `git show 2ebde7c2c32008cca12f4d09bbc18df1db6c01fe:GMT/Ch05/Submission.lean (speculative monotonicity_core draft: hCutoffSeq, hCutoffIntLim); git show 4c0fc30d6a1cd4ba43b449f2e51583e4e473c461 --stat (accepted dohr_local_monotonicity)`
- `toolchains/lean-4.35.0-rc3-linux/bin/lean GMT/Ch05/Submission.lean -o /tmp/cl-decomp/build/lib/GMT/Ch05/Submission.olean; then lean Types.lean, Assembly.lean, AssemblyAx.lean, Children.lean, Combined.lean (LEAN_PATH = build lib + lake-packages-25730c7c/*/.lake/build/lib/lean)`
- `python3 -I: lean_contract.validate_lean_statement on the 4 child types; gmt-compare.child_modules(contract mode) to generate NodeChallenge/NodeSolution; compile challenges against the frozen olean and solutions against a Submission build with the child proofs`
- `sed -n 440,560p book/chapter-04.txt (Simon Ch. 4, 4.1-4.9)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Continuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/Archimedean/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/Directed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/Filter/AtTopBot/Archimedean.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-c-e2dbd3c563/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-c-e2dbd3c563/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/tmp/cl-decomp/check/Types.lean`
- `/tmp/cl-decomp/check/Assembly.lean`
- `/tmp/cl-decomp/check/AssemblyAx.lean`
- `/tmp/cl-decomp/check/Children.lean`
- `/tmp/cl-decomp/check/Combined.lean`
- `/tmp/cl-decomp/cmp/allard52_amcl_interval_limit__NodeSolution.lean`

Snapshot and naming:
- Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f31 and Mathlib 25730c7c759d. The workspace Submission.lean and Contract.lean are byte-identical to the snapshot copies.
- The snapshot project has no cutoff, dominated-convergence or annular-limit lemmas (every grep count is 0). Nothing called allard52_amcl_* exists in the snapshot, dag.json, .humanize or git history, so all four new names are free.
- No accepted node has an identical type that could be reused. aal_l1th_exists_cutoff is a ball cutoff in Rn m, and the speculative monotonicity_core draft keeps its limit facts as local haves.

Mathlib tools (snapshot paths and lines):
- Lebesgue/Basic.lean: setLIntegral_iUnion_of_directed :668 (no measurability hypotheses); lintegral_mono_set :98.
- DominatedConvergence.lean: tendsto_integral_of_dominated_convergence :57; the interval filter version :170.
- IntervalIntegral/Basic.lean: norm_integral_le_of_norm_le :756; intervalIntegrable_congr :113 (alias IntervalIntegrable.congr :117); integral_congr :1077; integral_const_mul :817.
- integral_rpow: Integrals/Basic.lean:146. intervalIntegral.intervalIntegrable_rpow': Integrability/Basic.lean:47.
- smoothTransition lemmas: SmoothTransition.lean:161-222. Real.abs_exp_sub_one_le: Complex/Exponential.lean:533.
- Bochner/Set.lean: setIntegral_eq_integral_of_forall_compl_eq_zero :486; setIntegral_const :524; integral_indicator :185.
- integrableOn_const: IntegrableOn.lean:119. measureReal_def: MeasureSpaceDef.lean:105. continuous_inner: InnerProductSpace/Continuous.lean:65.
- Pow/Real.lean: zero_rpow :128; rpow_neg :259; rpow_sub :262; div_rpow :487.
- Order lemmas: exists_nat_one_div_lt (Archimedean/Basic.lean:211); Monotone.directed_le (Directed.lean:205); eventually_lt_nhds (OrderClosed.lean:229, via to_dual); tendsto_natCast_atTop_atTop (AtTopBot/Archimedean.lean:44).
- AEStronglyMeasurable.inner (StronglyMeasurable/Inner.lean:50) is not in the import closure of GMT.Ch05.Submission, so continuous_inner.comp_aestronglyMeasurable is used instead.

Lean checks (Lean 4.35.0-rc3, after import GMT.Ch05.Submission in the contract scope):
- The 4 child types elaborate and pass validate_lean_statement. The comparator challenge files elaborate.
- Children.lean fully proves all 4 children using only propext, Classical.choice and Quot.sound. The solution files (exact Submission.X) compile.
- Assembly.lean proves the exact frozen parent type from the 4 children and the exact frozen fixed_cutoff type. AssemblyAx and Combined show that the only extra dependency is allard52_am_fixed_cutoff.

Source: Simon Ch. 4, 4.1-4.8 (book/chapter-04.txt) obtains 4.7-4.8 by 'integrating from sigma to rho and letting eps -> 0'. The four children are exactly the technical parts of that limit.
