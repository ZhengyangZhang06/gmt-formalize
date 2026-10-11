# Parent-supplied natural-language proof

- Parent DAG node: `root.classical_tangent-a1`
- Child DAG node: `root.classical_tangent-a1.off_plane_mass_decay-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. μ := V.weight; B_ρ(ξ) := closedBall ξ ρ; μ.real(A) := (μ A).toReal; d(y) := infDist(y − x, P); A_ρ := B_ρ(x) ∖ {y : d(y) < ερ}; Hⁿ := μHE[n]. Source: the blow-up step (step 3) of the supplied proof of Simon 6.3, which the printed text summarises as 'evidently leads immediately'. Only the convergence part of IsApproxTangentAt is used.

1. Measurability and finiteness. The map z ↦ infDist(z, P) is 1-Lipschitz, hence continuous, so d is continuous. Therefore {d < ερ} is open and A_ρ is a Borel set. A_ρ ⊆ B_ρ(x), which is compact, so μ(A_ρ) ≤ μ(B_ρ(x)) < ∞ because μ is finite on compact sets.

2. The test function. Let g₁(z) := min(1, max(0, 2 − ‖z‖)), g₂(z) := min(1, max(0, 2·infDist(z, P)/ε − 1)) and f(z) := g₁(z)·g₂(z).
- f is continuous: z ↦ ‖z‖ and z ↦ infDist(z, P) are continuous, and min, max, +, −, · and division by the constant ε ≠ 0 preserve continuity.
- 0 ≤ f ≤ 1, since g₁ and g₂ take values in [0, 1].
- f has compact support: if ‖z‖ > 2 then max(0, 2 − ‖z‖) = 0, so g₁(z) = 0 and f(z) = 0. Thus f vanishes outside the compact set B_2(0), and f is an element of C_c(E, ℝ).
- f vanishes on P: if z ∈ P then infDist(z, P) = 0, so g₂(z) = min(1, max(0, −1)) = 0 and f(z) = 0. Therefore ∫_P f dHⁿ = 0, since the integrand vanishes at every point of the domain of integration.

3. The blow-up limit. By IsApproxTangentAt x P there is c ∈ ℝ with (tⁿ)⁻¹·∫ f(t⁻¹(y − x)) dμ(y) → c·∫_P f dHⁿ = c·0 = 0 as t ↓ 0. Neither dim P = n nor c > 0 is needed.

4. Pointwise comparison. Fix ρ > 0 and y ∈ A_ρ, and put z := ρ⁻¹(y − x).
- Since |y − x| ≤ ρ, ‖z‖ ≤ 1. So 2 − ‖z‖ ≥ 1 and g₁(z) = 1.
- Let w ∈ P. Then ρw ∈ P, hence d(y) = infDist(y − x, P) ≤ ‖(y − x) − ρw‖ = ‖ρ(z − w)‖ = ρ‖z − w‖. As y ∉ {d < ερ}, d(y) ≥ ερ, so ‖z − w‖ ≥ ε.
- P is nonempty (0 ∈ P), so infDist(z, P) = inf_{w ∈ P} ‖z − w‖ ≥ ε. Hence 2·infDist(z, P)/ε − 1 ≥ 1, g₂(z) = 1 and f(z) = 1.
Consequently 1_{A_ρ}(y) ≤ f(ρ⁻¹(y − x)) for every y ∈ E; off A_ρ the left side is 0 ≤ f.

5. Integration. Fix ρ > 0 and put h_ρ(y) := f(ρ⁻¹(y − x)).
- h_ρ is continuous. If |y − x| > 2ρ then ‖ρ⁻¹(y − x)‖ > 2 and h_ρ(y) = 0. So h_ρ vanishes outside the compact ball B_{2ρ}(x), has compact support, and is μ-integrable because μ is finite on compact sets (Continuous.integrable_of_hasCompactSupport).
- The indicator 1_{A_ρ} is nonnegative and μ-integrable, since A_ρ is measurable and μ(A_ρ) < ∞.
By step 4 and monotonicity of the integral, μ.real(A_ρ) = ∫ 1_{A_ρ} dμ ≤ ∫ h_ρ dμ. Multiplying by (ρⁿ)⁻¹ > 0 gives 0 ≤ (ρⁿ)⁻¹·μ.real(A_ρ) ≤ (ρⁿ)⁻¹·∫ f(ρ⁻¹(y − x)) dμ(y).

6. Squeeze. The inequalities of step 5 hold for every ρ > 0, hence eventually as ρ ↓ 0. The lower bound is the constant 0, and the upper bound tends to 0 by step 3. Therefore (ρⁿ)⁻¹·μ.real(B_ρ(x) ∖ {y : infDist(y − x, P) < ερ}) → 0 as ρ ↓ 0. ∎

## Key steps

1. A_ρ = B_ρ(x) ∖ {dist(y − x, P) < ερ} is Borel with finite μ-measure
2. f(z) = min(1, max(0, 2 − ‖z‖))·min(1, max(0, 2·dist(z, P)/ε − 1)) is in C_c(E), takes values in [0,1] and vanishes on P, so the IsApproxTangentAt limit for f is c·0 = 0
3. For y ∈ A_ρ, f(ρ⁻¹(y − x)) = 1, since ρw ∈ P for w ∈ P gives dist(ρ⁻¹(y − x), P) ≥ ε; hence 1_{A_ρ} ≤ f(ρ⁻¹(· − x))
4. Integrate (both sides are μ-integrable because μ is finite on compacts) and squeeze (ρⁿ)⁻¹μ.real(A_ρ) between 0 and the vanishing blow-up integral

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `sha256sum <snapshot>/project/GMT/Ch04/Contract.lean GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean`
- `python3 (json): print lean_name/lean_statement/depends_on of every node in <run>/dag.json; compare the sibling types (mean_curvature_monotonicity, canonical_representatives) and the parent type in the handoff with /tmp/ct-a1-audit/ChildTypes.lean`
- `rg -n 'sSup_nonneg|sSup_le' <snapshot>/mathlib/Mathlib/Algebra/Order/Archimedean/Real/Basic.lean`
- `rg -n 'theorem measureReal_mono\b|theorem MemLp.integrable_norm_rpow|theorem setIntegral_mono_set\b' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem infDist_le_infDist_add_dist|theorem infDist_zero_of_mem\b|theorem lipschitz_infDist_pt|theorem continuous_infDist_pt|lemma le_infDist|theorem infDist_le_dist_of_mem' <snapshot>/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `rg -n 'theorem Continuous.integrable_of_hasCompactSupport|theorem integral_indicator_one\b|theorem setIntegral_eq_zero_of_forall_eq_zero\b|theorem measure_closedBall_lt_top\b|theorem tendsto_nhdsWithin_nhds\b|theorem continuousAt_rpow_const\b|theorem tendsto_of_tendsto_of_tendsto_of_le_of_le' <snapshot>/mathlib/Mathlib`
- `rg -n 'infDist_smul₀' <snapshot>/mathlib/Mathlib/Analysis/Normed; rg -n 'theorem intro' <snapshot>/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `rg -n -t lean -i 'classical.?tangent|IsApproxTangentAt|lower.?density|infDist_smul|tangent_plane' lake-packages-25730c7c/simongmt/Poincare`
- `grep -n 'theorem\|def ' simongmt/Poincare/SimonGMT/Chapter04/{ClassicalTangent,LpLowerDensity}.lean`
- `grep -n -i 'simongmt\|unfaithful\|Poincare' GMT/Ch04/README.md`
- `grep -n '6.3' book/chapter-04.txt; sed -n 895,930p book/chapter-04.txt`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/ct-a1-audit/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/ct-a1-audit/olean lean /tmp/ct-a1-audit/ChildTypes.lean`
- `LEAN_PATH=... lean /tmp/ct-a1-audit/A/Proof.lean; ... B/Proof.lean; ... C/Proof.lean (each ends with #print axioms)`
- `LEAN_PATH=... lean /tmp/ct-a1-audit/Combined.lean`
- `rg -l -e 'classical_tangent_uniform_lower_density|classical_tangent_off_plane_mass_decay|classical_tangent_support_flatness' over <run> (excluding local-references), GMT/, simongmt/Poincare, <snapshot>/mathlib/Mathlib`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Algebra/Order/Archimedean/Real/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-classical-tangent-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-classical-tangent-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-classical-tangent-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root/speculative-prompt-v2.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/ClassicalTangent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/LpLowerDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/tmp/ct-a1-audit/ChildTypes.lean`
- `/tmp/ct-a1-audit/A/Proof.lean`
- `/tmp/ct-a1-audit/B/Proof.lean`
- `/tmp/ct-a1-audit/C/Proof.lean`
- `/tmp/ct-a1-audit/Combined.lean`

The snapshot Contract.lean (sha256 6e58e5dd…0f4770b) is byte-identical to the workspace Contract.lean and Submission.lean. The snapshot is project ff75f52 and Mathlib 25730c7c; SimonGMT is at 2b3663083f3fe399b6296fb8eaee52169170e197.

All Mathlib lemmas the child proofs cite exist in the snapshot: Real.sSup_le, Real.sSup_nonneg, measureReal_mono, MemLp.integrable_norm_rpow, setIntegral_mono_set, setIntegral_eq_zero_of_forall_eq_zero, integral_indicator_one, Continuous.integrable_of_hasCompactSupport, measure_closedBall_lt_top, Metric.infDist_le_infDist_add_dist, infDist_zero_of_mem, le_infDist, infDist_le_dist_of_mem, continuous_infDist_pt, Metric.tendsto_nhdsWithin_nhds, Real.continuousAt_rpow_const, tendsto_of_tendsto_of_tendsto_of_le_of_le', HasCompactSupport.intro and infDist_smul₀.

SimonGMT Chapter04/ClassicalTangent.lean proves 6.3 (HasGeneralizedMeanCurvatureIn.classical_tangent, via exists_uniform_lower_ball_mass_lp and eventually_support_flatness_half) with the same three-part structure. It is only for the strengthened Chapter04.RectifiableVarifold, which README.md says the contract does not use, so it is not reusable without building that structure; the children are proved from Mathlib alone.

After compiling Submission to /tmp/ct-a1-audit/olean:
- all three child types elaborate in namespace GMT.Ch04 with the contract's opens and `open RectifiableVarifold`;
- the parent assembly from the three children and the two dag.json sibling interfaces typechecks against exactly the frozen parent type;
- complete scratch proofs of the three children compile, with `#print axioms` = [propext, Classical.choice, Quot.sound];
- in Combined.lean, the parent's only sorryAx comes from the two sorry'd siblings.

No collision was found for the three proposed names (no match in the run directory, GMT sources, SimonGMT or the snapshot Mathlib).
