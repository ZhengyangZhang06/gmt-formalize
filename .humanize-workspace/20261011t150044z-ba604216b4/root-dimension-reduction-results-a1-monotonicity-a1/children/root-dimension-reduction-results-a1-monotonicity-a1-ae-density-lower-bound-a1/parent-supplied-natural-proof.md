# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.monotonicity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.monotonicity-a1.ae_density_lower_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the first half of step 7 of the selected node's supplied proof ("Θ ≥ 1 μ-a.e."), i.e. Simon Ch. 4, 3.13 and the sentence after it (chapter-04.txt lines 350–364), with Simon Ch. 3, Remark 1.5(3) (chapter-03.txt lines 95–101). Only a lower bound is needed. So instead of Θⁿ(μ, x) = θ(x) (Ch. 3, Theorem 1.9 with Ch. 4, Remark 1.8(2)), we use θ ≥ 1 and the unit density of the unweighted measure Hⁿ⌞M, which is given by the siblings closed_ball_unit_density and open_ball_density.
Notation: M := R.carrier, θ := R.mult, ν := Hⁿ⌞M = μHE[n].restrict M, μ := R.measure = ν.withDensity θ, ω_n := unitBallVolume n, B_t(z) := ball z t.
1. (Reduction to ν.) μ ≪ ν (withDensity_absolutelyContinuous). So every property that holds for ν-a.e. x holds for μ-a.e. x (AbsolutelyContinuous.ae_le). It suffices to prove the claim for ν-a.e. x.
2. (Good points.) M is Borel, so ν-a.e. x lies in M (ae_restrict_mem). By the field R.orients, for ν-a.e. x there is a subspace Q with HasApproximateTangentSpaceAt n M x Q. Both properties hold simultaneously for ν-a.e. x.
3. (Weight versus area.) For every Borel A, ν(A) ≤ μ(A). Indeed μ(A) = ∫⁻_A θ dν (withDensity_apply). θ is ℕ-valued and positive on M (R.mult_pos), and ν-a.e. point lies in M, so θ ≥ 1 ν-a.e. Hence μ(A) ≥ ∫⁻_A 1 dν = ν(A).
4. (Local finiteness.) Fix x as in step 2, with x ∈ M and a subspace Q. Fix θ₀ ∈ ℝ with μ(B_ρ(x))/(ω_n·ofReal(ρ^n)) → ofReal(θ₀) as ρ ↓ 0; we must show θ₀ ≥ 1. Since x ∈ M ⊆ U (R.carrier_subset) and U is open, there is s > 0 with closedBall x s ⊆ U. closedBall x s is compact, and θ ≥ 1 on M, so Hⁿ(M ∩ closedBall x s) = ∫⁻_{M ∩ closedBall x s} 1 dHⁿ ≤ ∫⁻_{M ∩ closedBall x s} θ dHⁿ < ∞. The last bound is the field R.locallyIntegrable_mult for K = closedBall x s.
5. (Unit density of ν.)
 - By the sibling closed_ball_unit_density, applied to M, x, Q and s (using step 4 and HasApproximateTangentSpaceAt n M x Q), Hⁿ(M ∩ closedBall x ρ)/(ω_n·ofReal(ρ^n)) → 1 as ρ ↓ 0.
 - Closed balls are Borel, so ν(closedBall x ρ) = Hⁿ(closedBall x ρ ∩ M) = Hⁿ(M ∩ closedBall x ρ) for every ρ (Measure.restrict_apply). Hence ν(closedBall x ρ)/(ω_n·ofReal(ρ^n)) → 1.
 - By the sibling open_ball_density, applied to ν, x and the limit 1, ν(B_ρ(x))/(ω_n·ofReal(ρ^n)) → 1 as ρ ↓ 0.
6. (Comparison and conclusion.) By step 3 with A = B_ρ(x), ν(B_ρ(x)) ≤ μ(B_ρ(x)) for every ρ. Division by the same element of [0, ∞] is monotone (ENNReal.div_le_div_right), so ν(B_ρ(x))/(ω_n·ofReal(ρ^n)) ≤ μ(B_ρ(x))/(ω_n·ofReal(ρ^n)) for every ρ. The left side tends to 1 by step 5, and the right side tends to ofReal(θ₀) by assumption. The filter ρ ↓ 0 is nontrivial, so 1 ≤ ofReal(θ₀) (le_of_tendsto_of_tendsto'). Hence θ₀ ≥ 1 (ENNReal.one_le_ofReal). This holds for every such θ₀ and every x in the ν-full set of step 2, so by step 1 the claim holds for μ-a.e. x.

## Key steps

1. μ_R ≪ ν = Hⁿ⌞M, and ν-a.e. x lies in M and has an approximate tangent plane Q.
2. θ ≥ 1 on M gives ν ≤ μ_R on Borel sets and Hⁿ(M ∩ closedBall x s) < ∞ for small s (locallyIntegrable_mult).
3. closed_ball_unit_density and open_ball_density give ν(B_ρ(x))/(ω_nρ^n) → 1.
4. Comparing ν ≤ μ_R along ρ ↓ 0 gives 1 ≤ ofReal θ₀, i.e. θ₀ ≥ 1.

## Reference use

### local-project

Queries:
- `cat nodes/root-dimension-reduction-results-a1-monotonicity-a1/{parent-child-handoff.json,decomposition-v1.json,decomposition-audit-v1.json,decomposition-review-receipt-v1.json,decomposition-scope-v1.json}`
- `python3 over dag.json: monotonicity-a1 and im_mass_measure-a1 nodes (status, depends_on, lean_statement); search of all lean_statements for HasMassDensity|UpperSemicontinuousOn|MonotoneOn|unitBallVolume|Real.exp; duplicate-lean_name check; children of im_sub-a1 and support_null-a1 (reuse precedent)`
- `cat nodes/{…mean-curvature-monotonicity-a1-ex-17c79c81ce,…-ta-ec3b44cb45,…-fi-76e995b6e5,root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1,…-closed-to-open-b-2625a8c412}/{parent-supplied-natural-proof.md,parent-child-handoff.json,isolated-comparator-result.json,accepted-candidate.json}`
- `git show 81933e8:GMT/Ch07/Submission.lean | grep -n dsmc_exp_ball_mass_monotone`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/{mathlib,simongmt} rev-parse HEAD`
- `rg -n over local-references/123e8435b4a2469b/mathlib/Mathlib for MonotoneOn.tendsto_nhdsWithin_Ioo_right, ENNReal.Tendsto.{mul,const_mul,div_const}, ENNReal.{mul_lt_mul_right,mul_lt_mul_iff_right,div_mul_cancel,ofReal_inv_of_pos,div_le_div_right}, withDensity_apply, ae_restrict_mem, AbsolutelyContinuous.ae_le, nhdsGT_basis, integral_withDensity_eq_integral_smul, image_eq_zero_of_notMem_tsupport`
- `rg -n "HasLocallyBoundedMeanCurvature|def IMRep.measure|locallyIntegrable_mult|def HasMassDensity|def unitBallVolume" local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `grep -n 'def massOn|theorem massOn_mono|def support|zeroRegion|support_subset_domain' simongmt/Poincare/SimonGMT/Chapter06/{Mass,CurrentLocalEquality}.lean`
- `sed -n 315,432p book/chapter-04.txt (Simon Ch. 4, 3.8–3.17)`
- `grep -c / grep -rl of the four new dimred_mono_* names in dag.json, run nodes, GMT, .humanize/math-wiki, simongmt/Poincare and .swarm-worktrees/*/Submission.lean (no match)`
- `lake env lean /tmp/mono-v2-check/Assembly.lean; lake env lean /tmp/mono-v2-check/Children.lean; lake env lean /tmp/mono-v2-check/Density.lean (#print axioms)`
- `python3 byte comparison of the compiled theorem types with the dag.json / handoff lean_statement strings`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-monotonicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-monotonicity-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ex-17c79c81ce/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ex-17c79c81ce/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ta-ec3b44cb45/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ta-ec3b44cb45/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-fi-76e995b6e5/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-closed-to-open-b-2625a8c412/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-closed-to-open-b-2625a8c412/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/tmp/mono-v2-check/Assembly.lean`
- `/tmp/mono-v2-check/Children.lean`
- `/tmp/mono-v2-check/Density.lean`

Pins and contract.
- The snapshot pins project b4d606d, Mathlib 25730c7c and SimonGMT 2b36630, matching the workspace HEAD and the installed packages.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Reusable accepted declarations (status accepted in dag.json, isolated comparator passed, frozen types byte-identical to the strings used here):
- dsmc_exp_ball_mass_monotone (candidate 81933e8): Simon 3.17 for one ball;
- dsmc_approxTangentPlane_starProjection_aemeasurable (7eb1db9);
- rsd_tendsto_closedBall_density_of_approxTangent (dbef2c1);
- rsd_tendsto_ball_density_of_closedBall (c3ca64f).
Rejected candidates:
- dtc_density_usc has the content of part (iii) but is not accepted, so it is neither reused nor collided with.
- dor_imrep_massOn_eq_measure_and_support is an accepted analogue of im_mass_measure (a)/(b). The assembly keeps the declared sibling dependency dimred_im_mass_measure, as in the supplied proof.

Library facts.
- SimonGMT: massOn is an sSup and is monotone (massOn_mono); support = U \ zeroRegion ⊆ U (support_subset_domain).
- Contract: HasLocallyBoundedMeanCurvature gives only a μ-a.e. bound on compacts, which motivates the truncation child.
- Every Mathlib lemma used in the proofs exists at the pinned revision.

Lean checks.
- All 8 child types elaborate after import GMT.Ch07.Submission.
- The exact parent type is proved from them plus the two prerequisites; sorryAx comes only from the stubs.
- The four new children have complete proofs using only standard axioms, modulo the reused rsd declarations for the a.e. bound.

Names and dependencies.
- The new names are globally unique.
- The dependencies are acyclic.
