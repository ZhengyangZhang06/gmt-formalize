# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_limit-a1`
- Child DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_limit-a1.cutoff_sequence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 2 of the parent proof (cubic cutoff profile; eps_k := 1/(k+2)). Everything needed is defined below.

1. Transition profile. Let S : R -> R be S(v) := 0 for v <= 0, S(v) := 3v^2 - 2v^3 for 0 <= v <= 1, and S(v) := 1 for v >= 1. The formulas agree at v = 0 (value 0) and at v = 1 (value 1), so S is well defined and continuous.

2. Properties of S.
 (a) S is C^1. On (0, 1), S'(v) = 6v - 6v^2 = 6v(1 - v). At v = 0: for h < 0, S(h) - S(0) = 0; for 0 < h <= 1, |S(h) - S(0)|/h = |3h - 2h^2| <= 3h + 2h^2. So S'(0) = 0. At v = 1: for h > 0, S(1 + h) - S(1) = 0; for -1 <= h < 0, put u := -h, so S(1 - u) = 1 - 3u^2 + 2u^3 and |S(1 + h) - S(1)|/|h| = |3u^2 - 2u^3|/u <= 3u + 2u^2. So S'(1) = 0. Hence S is differentiable everywhere, with S'(v) = 6v(1 - v) for 0 <= v <= 1 and S'(v) = 0 otherwise. This derivative is continuous because it vanishes at 0 and at 1. So S is C^1.
 (b) S' >= 0 everywhere, so S is nondecreasing. Since S(0) = 0 and S(1) = 1, we get 0 <= S(v) <= 1 for all v: directly for v <= 0 and v >= 1, and by monotonicity for 0 <= v <= 1.
 (c) S(v) = 0 for v <= 0 and S(v) = 1 for v >= 1.
 Only (a)-(c) are used below. In Lean one may take S := Real.smoothTransition instead. It is C^infinity, hence C^1 (smoothTransition.contDiff), monotone (.monotone), has values in [0, 1] (.nonneg, .le_one), vanishes on (-infinity, 0] (.zero_of_nonpos) and equals 1 on [1, infinity) (.one_of_one_le).

3. Widths. Put eps_k := 1/(k + 2). Since k + 2 >= 2 > 0, we have 0 < eps_k <= 1/2 <= 1, which is (a). Since k + 2 -> infinity, eps_k -> 0, which is (b).

4. Cutoffs. Put phi_k(u) := 1 - S((u - 1)(k + 2)). Note that (u - 1)(k + 2) = (u - 1)/eps_k.

5. (c). The map u -> (u - 1)(k + 2) is affine, hence C^infinity. Composed with the C^1 function S it is C^1, and so is a constant minus it.

6. (d). Let u <= v. Since k + 2 > 0, (u - 1)(k + 2) <= (v - 1)(k + 2). As S is nondecreasing, S((u - 1)(k + 2)) <= S((v - 1)(k + 2)), that is, phi_k(v) <= phi_k(u).

7. (e). From 0 <= S <= 1 we get 0 <= 1 - S((u - 1)(k + 2)) <= 1.

8. (f). If u <= 1, then (u - 1)(k + 2) <= 0, so S((u - 1)(k + 2)) = 0 and phi_k(u) = 1.

9. (g). If u >= 1 + eps_k, then u - 1 >= 1/(k + 2), so (u - 1)(k + 2) >= 1. Hence S((u - 1)(k + 2)) = 1 and phi_k(u) = 0.

10. Therefore phi := (phi_k)_k and eps := (eps_k)_k witness the existential statement.

## Key steps

1. Take a C^1 nondecreasing profile S with 0 <= S <= 1, S = 0 on (-infinity, 0] and S = 1 on [1, infinity): S(v) = 3v^2 - 2v^3 on [0, 1], or Real.smoothTransition.
2. eps_k := 1/(k + 2) gives 0 < eps_k <= 1 and eps_k -> 0.
3. phi_k(u) := 1 - S((u - 1)(k + 2)) is C^1, nonincreasing and [0, 1]-valued.
4. u <= 1 makes the argument <= 0, so phi_k(u) = 1; u >= 1 + eps_k makes it >= 1, so phi_k(u) = 0.

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
