# Parent-supplied natural-language proof

- Parent DAG node: `root.weighted_monotonicity-a1.cutoff_limit-a1`
- Child DAG node: `root.weighted_monotonicity-a1.cutoff_limit-a1.kernel_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. λ is Lebesgue measure on ℝ and ∫_{(σ,ρ]} is the integral against λ⌞(σ,ρ] (Ioc σ ρ); φ_m' := deriv φ_m; K_m(s, τ) := −(s/τ²)·φ_m'(s/τ)/τⁿ, so k_m(s) = ∫_{(σ,ρ]} K_m(s, τ)dτ; D_m(s) := φ_m(s/ρ) − φ_m(s/σ); κ(s) := 1_{(σ,ρ]}(s)·(sⁿ)^{-1}. The two-sided bound is a HYPOTHESIS of this lemma (in the parent it is supplied by weighted_mono_kernel_bounds, a dependency of the parent node that is not available here and needs C¹, which is not assumed); use the hypothesis directly. (Context: Step 6 of the parent proof.) Note ρ ≥ σ > 0.
0. (Range of φ_m.) For every t: φ_m(t) ≤ φ_m(min(t, 1)) = 1, because min(t, 1) ≤ t, φ_m is nonincreasing and min(t, 1) ≤ 1; and φ_m(t) ≥ φ_m(max(t, 1 + ε_m)) = 0, because max(t, 1 + ε_m) ≥ t and max(t, 1 + ε_m) ≥ 1 + ε_m. So 0 ≤ φ_m ≤ 1.
1. (Properties of D_m.) Let s > 0. (a) Since 0 < σ ≤ ρ, s/ρ ≤ s/σ, so φ_m(s/ρ) ≥ φ_m(s/σ) and D_m(s) ≥ 0; by 0, D_m(s) ≤ 1 − 0 = 1. (b) If s ≤ σ, then s/σ ≤ 1 and s/ρ ≤ 1 (as s ≤ σ ≤ ρ), so D_m(s) = 1 − 1 = 0. (c) If s > (1 + ε_m)ρ, then (dividing by ρ > 0) s/ρ ≥ 1 + ε_m and, by (a), s/σ ≥ s/ρ ≥ 1 + ε_m, so D_m(s) = 0 − 0 = 0.
2. (Squeeze to zero.) If s > 0 and D_m(s) = 0, the assumed bounds read 0 = 0/sⁿ ≤ k_m(s) ≤ (1 + ε_m)ⁿ·0 = 0, so k_m(s) = 0.
3. (k_m(0) = 0.) For s = 0 the integrand is −(0/τ²)·φ_m'(0/τ)/τⁿ = 0 for every τ, so k_m(0) = ∫_{(σ,ρ]} 0 dτ = 0.
4. (Claim (1): measurability.) For any function φ_m: ℝ → ℝ, deriv φ_m is Borel measurable (measurable_deriv). The map (s, τ) ↦ K_m(s, τ) on ℝ × ℝ is obtained from the coordinate projections, the quotient s/τ, deriv φ_m, powers, products, negation and quotients, all of which are Borel measurable on ℝ (division on ℝ is measurable, with x/0 = 0); hence K_m is Borel measurable, so strongly measurable, on ℝ × ℝ. The measure λ⌞(σ,ρ] is s-finite (indeed finite), so s ↦ ∫K_m(s, τ) d(λ⌞(σ,ρ])(τ) = k_m(s) is strongly measurable (StronglyMeasurable.integral_prod_right), hence measurable.
5. (Claim (2): uniform bound.) Let s ≥ 0. If s = 0, |k_m(0)| = 0 ≤ 2ⁿ/σⁿ by 3. If 0 < s ≤ σ, k_m(s) = 0 by 1(b) and 2, so |k_m(s)| = 0 ≤ 2ⁿ/σⁿ. If s > σ: by 1(a) and the lower bound, k_m(s) ≥ D_m(s)/sⁿ ≥ 0, so |k_m(s)| = k_m(s) ≤ (1 + ε_m)ⁿ·(D_m(s)/sⁿ). Now 0 ≤ 1 + ε_m ≤ 2 (as 0 < ε_m ≤ 1), so (1 + ε_m)ⁿ ≤ 2ⁿ; and D_m(s)/sⁿ ≤ 1/sⁿ ≤ 1/σⁿ because 0 ≤ D_m(s) ≤ 1 and sⁿ ≥ σⁿ > 0. Multiplying these inequalities between nonnegative quantities gives k_m(s) ≤ 2ⁿ·(1/σⁿ) = 2ⁿ/σⁿ.
6. (Claim (3): support.) If s > (1 + ε_m)ρ, then s > 0 (since (1 + ε_m)ρ > 0) and D_m(s) = 0 by 1(c), so k_m(s) = 0 by 2.
7. (Claim (4): pointwise limit.) Fix s ≥ 0. (a) s = 0: k_m(0) = 0 for every m by 3, and 0 ∉ (σ, ρ] because σ > 0, so κ(0) = 0; the constant sequence 0 converges to κ(0). (b) 0 < s ≤ σ: k_m(s) = 0 for every m by 1(b) and 2, and s ∉ (σ, ρ], so κ(s) = 0. (c) σ < s ≤ ρ: here κ(s) = (sⁿ)^{-1}. Since s/σ > 1 and ε_m → 0, there is m₀ with ε_m < s/σ − 1 for m ≥ m₀; for such m, φ_m(s/σ) = 0 while φ_m(s/ρ) = 1 (as s/ρ ≤ 1), so D_m(s) = 1 and the assumed bounds give (sⁿ)^{-1} ≤ k_m(s) ≤ (1 + ε_m)ⁿ·(1/sⁿ). As m → ∞, 1 + ε_m → 1, so (1 + ε_m)ⁿ → 1ⁿ = 1 (continuity of t ↦ tⁿ) and the upper bound tends to 1/sⁿ = (sⁿ)^{-1}; the lower bound is constant. By the squeeze theorem with eventual inequalities (tendsto_of_tendsto_of_tendsto_of_le_of_le'), k_m(s) → (sⁿ)^{-1} = κ(s). (d) s > ρ: κ(s) = 0. Since s/ρ > 1 and s/σ > 1 (because s > ρ ≥ σ), there is m₀ with ε_m < s/ρ − 1 and ε_m < s/σ − 1 for m ≥ m₀; for such m, φ_m(s/ρ) = φ_m(s/σ) = 0, so D_m(s) = 0 and k_m(s) = 0 by 2. Hence k_m(s) is eventually 0 and tends to 0 = κ(s). In all cases k_m(s) → κ(s) = (Ioc σ ρ).indicator (s ↦ (sⁿ)^{-1}) (s).

## Key steps

1. 0 ≤ φ_m ≤ 1 from antitonicity and the boundary values; 0 ≤ D_m(s) ≤ 1 for s > 0
2. D_m(s) = 0 for 0 < s ≤ σ and for s > (1+ε_m)ρ, and then the assumed kernel squeeze forces k_m(s) = 0; k_m(0) = 0
3. k_m is measurable: the integrand is Borel on ℝ² (measurable_deriv) and StronglyMeasurable.integral_prod_right
4. |k_m(s)| ≤ (1+ε_m)ⁿ s^{-n} ≤ 2ⁿσ^{-n} for s > σ, and k_m(s) = 0 otherwise
5. Pointwise limit by cases s = 0, 0 < s ≤ σ, σ < s ≤ ρ (squeeze with (1+ε_m)ⁿ → 1), s > ρ, using ε_m → 0

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `grep -n '^theorem\|^protected theorem' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `rg -n 'theorem tendsto_integral_filter_of_dominated_convergence|theorem continuousOn_of_dominated|theorem _root_.aestronglyMeasurable_of_tendsto_ae|theorem StronglyMeasurable.integral_prod_right|theorem measurable_deriv|lemma IntegrableOn.of_bound|theorem integrableOn_const |theorem integral_indicator |theorem integrable_indicator_iff|theorem tendsto_of_tendsto_of_tendsto_of_le_of_le'|theorem norm_integral_le_of_norm_le |theorem measure_closedBall_lt_top|theorem div₀|theorem ContinuousOn.aestronglyMeasurable|theorem tendsto_nhds_unique ' <snapshot>/mathlib/Mathlib`
- `rg -n 'aestronglyMeasurable_indicator_iff|const_div_atTop' <snapshot>/mathlib/Mathlib`
- `grep -rn 'monotonicityCutoff' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04`
- `rg/grep/git grep 'weighted_mono_cutoff_seq_exists|weighted_mono_cutoff_integral_tendsto|weighted_mono_kernel_limit|weighted_mono_kernel_term_tendsto|weighted_mono_curvature_term_tendsto' over <snapshot>, dag.json, nodes/, GMT/Ch04/Submission.lean and all local branches`
- `python3 -I: verifier/lean_contract.validate_lean_statement and verifier/gmt-compare.py child_modules (contract mode) for each child`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/cutoff-limit-decomp/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/cutoff-limit-decomp/olean lean /tmp/cutoff-limit-decomp/work/{Assembly,C1,C2,C3,C4,C5,Full}.lean (#print axioms)`
- `LEAN_PATH=... lean /tmp/cutoff-limit-decomp/gen/<key>_NodeChallenge.lean for all five children`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Algebra/Order/Field.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1-cutoff-limit-a1/parent-child-handoff.json`
- `/tmp/cutoff-limit-decomp/work/Assembly.lean`
- `/tmp/cutoff-limit-decomp/work/Full.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (sha256 6e58e5dd…0f4770b; project ff75f52a, mathlib 25730c7c).

Every tool the children use exists in the snapshot Mathlib:
- Real.smoothTransition.{contDiff, monotone, zero_of_nonpos, one_of_one_le, nonneg, le_one}: SmoothTransition.lean:161–222.
- tendsto_integral_filter_of_dominated_convergence: DominatedConvergence.lean:67.
- continuousOn_of_dominated and norm_integral_le_of_norm_le: Bochner/Basic.lean:467, 985.
- integral_indicator: Bochner/Set.lean:185.
- integrableOn_const, IntegrableOn.of_bound, integrable_indicator_iff, ContinuousOn.aestronglyMeasurable: IntegrableOn.lean:119, 174, 340, 791.
- AEStronglyMeasurable.div₀, aestronglyMeasurable_indicator_iff, aestronglyMeasurable_of_tendsto_ae: AEStronglyMeasurable.lean:332, 545, 696.
- MeasureTheory.StronglyMeasurable.integral_prod_right: Integral/Prod.lean:67.
- measurable_deriv: FDeriv/Measurable.lean:398.
- measure_closedBall_lt_top: Typeclasses/Finite.lean:364.
- tendsto_of_tendsto_of_tendsto_of_le_of_le': Topology/Order/Basic.lean:220.
- tendsto_nhds_unique: Separation/Hausdorff.lean:180.
- Filter.Tendsto.const_div_atTop: Topology/Algebra/Order/Field.lean:222.

SimonGMT's monotonicityCutoff (Chapter04/FirstVariation.lean:825–885) is the same construction as cutoff_seq. GMT.Ch04.Submission does not import that module, so the child uses Real.smoothTransition directly.

No-match result: none of the five proposed lean_names occurs in the snapshot, dag.json, nodes/, GMT/, or any local branch.

All five child types elaborate in the comparator contract scope, and each has a sorry-free Lean proof using only standard axioms. The selected frozen theorem compiles from the five children plus the frozen weighted_mono_kernel_bounds type.
