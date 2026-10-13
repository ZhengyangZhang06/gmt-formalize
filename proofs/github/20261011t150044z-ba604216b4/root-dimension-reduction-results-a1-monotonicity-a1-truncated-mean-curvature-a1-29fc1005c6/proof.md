# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.monotonicity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.monotonicity-a1.truncated_mean_curvature-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the selected node's supplied proof, "Λ := max(Λ_K, 0)" with |H| ≤ Λ_K μ-a.e. on K (Simon Ch. 4, 3.14–3.15, chapter-04.txt lines 370–386: the bound |H| ≤ Λ is only needed where the test fields live). The radial fields used for a ball closedBall y R ⊆ K are supported in K, so H may be changed off K and on μ-null sets. This lemma makes H bounded everywhere, which is the form (Simon 3.15, |H| ≤ Λ) in which the selected node uses the mean curvature vector. Notation: μ := R.measure, ⟨·,·⟩ := inner ℝ on ℝ^P.
1. (Data.) By R.HasLocallyBoundedMeanCurvature there is H₀ : ℝ^P → ℝ^P with the following three properties:
 - H₀ is μ-a.e. strongly measurable;
 - for every compact K' ⊆ U there is Λ_{K'} ∈ ℝ with ‖H₀(x)‖ ≤ Λ_{K'} for μ-a.e. x ∈ K';
 - R.firstVariation X = −∫⟨X, H₀⟩ dμ for every C¹ field X with compact support and tsupport X ⊆ U.
 Fix a compact K ⊆ U and Λ_K as above, and put Λ := max(Λ_K, 0). Then Λ ≥ 0, and ‖H₀(x)‖ ≤ Λ for μ-a.e. x ∈ K.
2. (A strongly measurable version.) Since H₀ is μ-a.e. strongly measurable, there is a strongly measurable H₁ : ℝ^P → ℝ^P with H₁ = H₀ μ-a.e. (AEStronglyMeasurable.mk, stronglyMeasurable_mk, ae_eq_mk).
 - The set S := {x : ‖H₁(x)‖ ≤ Λ} is measurable, because x ↦ ‖H₁(x)‖ is measurable (measurableSet_le).
 - Define H := 1_S·H₁, i.e. H(x) := H₁(x) for x ∈ S and H(x) := 0 for x ∉ S (Set.indicator).
 - H is strongly measurable, as the indicator of a measurable set times a strongly measurable function (StronglyMeasurable.indicator). In particular H is μ-a.e. strongly measurable.
3. (Global bound.) Let x ∈ ℝ^P. If x ∈ S, then ‖H(x)‖ = ‖H₁(x)‖ ≤ Λ. If x ∉ S, then ‖H(x)‖ = ‖0‖ = 0 ≤ Λ. So ‖H(x)‖ ≤ Λ for every x.
4. (H = H₀ a.e. on K.) Let G be the set of x with H₁(x) = H₀(x) and (x ∈ K ⇒ ‖H₀(x)‖ ≤ Λ). By steps 1 and 2, the complement of G is μ-null. If x ∈ G ∩ K, then ‖H₁(x)‖ = ‖H₀(x)‖ ≤ Λ. Hence x ∈ S and H(x) = H₁(x) = H₀(x).
5. (First variation.) Let X be a C¹ field with compact support and tsupport X ⊆ K.
 - Since K ⊆ U, tsupport X ⊆ U, so step 1 gives R.firstVariation X = −∫⟨X, H₀⟩ dμ.
 - Let x ∈ G. If x ∈ K, then ⟨X(x), H₀(x)⟩ = ⟨X(x), H(x)⟩ by step 4. If x ∉ K, then x ∉ tsupport X, so X(x) = 0 (image_eq_zero_of_notMem_tsupport) and both inner products are 0.
 - Hence ⟨X, H₀⟩ = ⟨X, H⟩ μ-a.e., and the two Bochner integrals are equal (integral_congr_ae, which needs no integrability).
 - Therefore R.firstVariation X = −∫⟨X, H⟩ dμ.
6. Steps 2, 3 and 5 give Λ ≥ 0 and H with all the required properties.

## Key steps

1. Take H₀ and Λ_K from HasLocallyBoundedMeanCurvature and set Λ := max(Λ_K, 0).
2. Replace H₀ by a strongly measurable version H₁ and set H := 1_{‖H₁‖ ≤ Λ}·H₁, which is strongly measurable with ‖H‖ ≤ Λ everywhere.
3. H = H₀ μ-a.e. on K, and every X with tsupport X ⊆ K vanishes off K, so ⟨X, H⟩ = ⟨X, H₀⟩ μ-a.e. and the first-variation identity transfers to H.

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
