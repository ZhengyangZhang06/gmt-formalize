# Parent-supplied natural-language proof

- Parent DAG node: `root.weighted_monotonicity-a1.cutoff_limit-a1`
- Child DAG node: `root.weighted_monotonicity-a1.cutoff_limit-a1.kernel_term-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. E := Ambient n ℓ = EuclideanSpace ℝ (Fin (n+ℓ)) = ℝ^{n+ℓ} with its Borel σ-algebra; B_s(ξ) := closedBall ξ s is the CLOSED ball, so x ∈ B_s(ξ) ⟺ |x − ξ| ≤ s (dist x ξ = |x − ξ|); r = r(x) := |x − ξ| ≥ 0; λ is Lebesgue measure on ℝ and ∫_{(a,b]} means the integral over Ioc a b; 1_S is the indicator function of S. Put B := B_R(ξ), Ann := B_ρ(ξ) ∖ B_σ(ξ), κ(s) := 1_{(σ,ρ]}(s)·(sⁿ)^{-1} and F_m(x) := u(x)·q(x)·k_m(r(x)). (Context: Steps 7 and 11 of the parent proof, with the kernel properties of its Step 6 taken as hypotheses.)
0. (Preliminaries.) E is finite-dimensional, so closed balls are compact and μ(B) < ∞ (measure_closedBall_lt_top, μ finite on compacts). For x ∈ E: x ∈ Ann ⟺ (r(x) ≤ ρ and not r(x) ≤ σ) ⟺ σ < r(x) ≤ ρ ⟺ r(x) ∈ (σ, ρ]. Since ρ ≤ R, Ann ⊆ B_ρ(ξ) ⊆ B. Ann is measurable (difference of two closed sets).
1. (First conclusion: integrability on the annulus.) Let x ∈ Ann. Then x ∈ B, so |u(x)| ≤ A (in particular A ≥ 0) and |q(x)| ≤ 1; and r(x) > σ > 0, so r(x)ⁿ ≥ σⁿ > 0. Hence |u(x)·(q(x)/r(x)ⁿ)| = |u(x)|·(|q(x)|/r(x)ⁿ) ≤ A·(1/r(x)ⁿ) ≤ A·(1/σⁿ) = A/σⁿ. The function x ↦ u(x)·(q(x)/r(x)ⁿ) is a.e. strongly measurable for μ⌞Ann: u and q are a.e. strongly measurable for μ⌞B and μ⌞Ann ≤ μ⌞B (Ann ⊆ B), so they are a.e. strongly measurable for μ⌞Ann; x ↦ r(x)ⁿ is continuous; and products and quotients of a.e. strongly measurable real functions are a.e. strongly measurable (AEStronglyMeasurable.mul, AEStronglyMeasurable.div₀). Since μ(Ann) ≤ μ(B) < ∞ and the bound A/σⁿ holds μ⌞Ann-a.e. (indeed at every point of Ann), the function is μ-integrable on Ann (IntegrableOn.of_bound).
2. (Vanishing off B.) If x ∉ B then r(x) > R, so k_m(r(x)) = 0 and F_m(x) = 0 for every m.
3. (Measurability.) By 2, F_m = 1_B·F_m. On B, F_m is the product of u and q, which are a.e. strongly measurable for μ⌞B, and of k_m∘r, which is Borel measurable (k_m measurable, r continuous); so F_m is a.e. strongly measurable for μ⌞B, and since B is closed (measurable), 1_B·F_m = F_m is a.e. strongly measurable for μ (aestronglyMeasurable_indicator_iff).
4. (Domination.) Let g := 1_B·(A·C), i.e. the constant A·C on B and 0 off B; g is μ-integrable because μ(B) < ∞. For x ∈ B: |u(x)|·|q(x)| ≤ |u(x)|·1 ≤ A, |k_m(r(x))| ≤ C (as r(x) ≥ 0), and A ≥ |u(x)| ≥ 0, so |F_m(x)| = (|u(x)|·|q(x)|)·|k_m(r(x))| ≤ A·C = g(x). For x ∉ B, |F_m(x)| = 0 = g(x) by 2.
5. (Pointwise limit.) Fix x. Since r(x) ≥ 0, k_m(r(x)) → κ(r(x)), so F_m(x) → u(x)·q(x)·κ(r(x)). If x ∈ Ann then r(x) ∈ (σ, ρ] and u(x)·q(x)·κ(r(x)) = u(x)·q(x)·(r(x)ⁿ)^{-1} = u(x)·(q(x)/r(x)ⁿ); if x ∉ Ann then r(x) ∉ (σ, ρ] and u(x)·q(x)·κ(r(x)) = 0. Hence F_m → 1_{Ann}·(x ↦ u(x)·(q(x)/r(x)ⁿ)) pointwise on E.
6. (Second conclusion.) By 3, 4 and 5, dominated convergence (tendsto_integral_filter_of_dominated_convergence with bound g) gives ∫F_m dμ → ∫1_{Ann}·u·(q/rⁿ) dμ, and ∫1_{Ann}·u·(q/rⁿ) dμ = ∫_{Ann} u·(q/rⁿ) dμ because Ann is measurable (integral_indicator).

## Key steps

1. μ(B_R(ξ)) < ∞, annulus ⊆ B_R(ξ), and x ∈ annulus ⟺ |x−ξ| ∈ (σ,ρ]
2. On the annulus |u·(q/rⁿ)| ≤ A/σⁿ, so the limit integrand is μ-integrable there
3. u·q·k_m(r) vanishes off B_R(ξ), is μ-a.e. strongly measurable, and is dominated by A·C·1_{B_R(ξ)}
4. Pointwise limit u·q·κ(r) = 1_annulus·u·(q/rⁿ)
5. Dominated convergence plus integral_indicator

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
