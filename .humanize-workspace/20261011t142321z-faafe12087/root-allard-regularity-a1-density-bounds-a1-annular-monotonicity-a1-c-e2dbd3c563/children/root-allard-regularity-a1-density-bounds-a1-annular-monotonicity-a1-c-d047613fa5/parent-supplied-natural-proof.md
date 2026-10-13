# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_limit-a1`
- Child DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_limit-a1.radial_tendsto-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (dominated convergence at a fixed radius), stated for a general integrand f. The parent applies it with f = 1 and with f(x) = (x - y).H(x).

Notation: r_x := |x - y| = dist(x, y); B_rho := closedBall y rho = {x : r_x <= rho}; nu := mu restricted to B_R; h_k(x) := phi_k(r_x/t) f(x). Integrals of non-integrable functions are 0 by the Bochner convention. Only large k matter below.

1. Eventually (1 + eps_k) t < R. Since 0 < t < R, delta := R/t - 1 > 0. As eps_k -> 0, there is k_0 with eps_k < delta for all k >= k_0. That is, 1 + eps_k < R/t, so (1 + eps_k) t < R.

2. For k >= k_0, h_k vanishes off B_R. If x is not in B_R, then r_x > R > (1 + eps_k) t. So r_x/t >= 1 + eps_k and phi_k(r_x/t) = 0. Since h_k = 0 outside B_R, the integral of h_k over the whole space equals its integral over B_R: integral h_k dmu = integral h_k dnu for k >= k_0. This identity needs no integrability of h_k: a function vanishing off B_R is mu-integrable iff it is nu-integrable, with equal integrals, and otherwise both integrals are 0 (Mathlib: setIntegral_eq_integral_of_forall_compl_eq_zero, which has no integrability hypothesis).

3. The limit as a nu-integral. B_t is a closed, hence measurable, subset of B_R because t < R. So integral 1_{B_t} f dnu = integral over B_t ∩ B_R of f dmu = integral over B_t of f dmu.

4. Hypotheses of dominated convergence for nu, with dominating function |f|.
 (a) |f| is nu-integrable, because f is mu-integrable on B_R.
 (b) Each h_k is nu-a.e.-strongly measurable. The function x -> phi_k(r_x/t) is continuous (phi_k is continuous and x -> |x - y|/t is continuous), and f is nu-a.e.-strongly measurable because it is nu-integrable. The product is therefore nu-a.e.-strongly measurable.
 (c) For all x and k, |h_k(x)| = phi_k(r_x/t) |f(x)| <= |f(x)|, since 0 <= phi_k <= 1.
 (d) h_k(x) -> 1_{B_t}(x) f(x) for every x.
  - If r_x <= t, then r_x/t <= 1, so phi_k(r_x/t) = 1 and h_k(x) = f(x) = 1_{B_t}(x) f(x) for every k.
  - If r_x > t, then u := r_x/t > 1. As eps_k -> 0, there is k_1 with eps_k < u - 1 for all k >= k_1. Then u >= 1 + eps_k, so phi_k(u) = 0 and h_k(x) = 0 = 1_{B_t}(x) f(x) for k >= k_1.

5. Dominated convergence gives integral h_k dnu -> integral 1_{B_t} f dnu.

6. Conclusion. By step 2, integral h_k dmu = integral h_k dnu for all k >= k_0. So integral h_k dmu -> integral 1_{B_t} f dnu, which equals the integral over B_t of f dmu by step 3.

## Key steps

1. Eventually (1 + eps_k) t < R, so the integrand vanishes off B_R(y) and its mu-integral equals its integral against nu = mu restricted to B_R(y).
2. The target integral over B_t(y) equals the nu-integral of 1_{B_t(y)} f, because B_t(y) ⊆ B_R(y).
3. |phi_k(|x - y|/t) f(x)| <= |f(x)|, which is nu-integrable, and the integrands are nu-a.e.-strongly measurable.
4. Pointwise limit 1_{B_t(y)} f: phi_k = 1 when |x - y| <= t, and phi_k is eventually 0 when |x - y| > t.
5. Dominated convergence.

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
