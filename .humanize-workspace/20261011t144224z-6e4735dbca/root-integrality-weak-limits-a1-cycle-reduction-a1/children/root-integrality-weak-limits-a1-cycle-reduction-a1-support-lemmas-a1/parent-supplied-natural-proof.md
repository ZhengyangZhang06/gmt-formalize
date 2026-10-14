# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.support_lemmas-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the support facts used in Part II, Step 7 (spt ∂T_j ⊆ spt T_j, (F4) for weak limits) and Step 9 (spt T′_j ⊆ spt T_j ∪ spt C_j) of the parent proof, made explicit.

Recall spt Z = U ∖ zeroRegion(Z), where zeroRegion(Z) is the union of all W with W open, closure W compact, closure W ⊆ U and Z(η) = 0 for every η ∈ D^n(U) with tsupport η ⊆ W (“Z vanishes on W”). (F2′): by the reused lemma isoperimetric_apply_eq_zero_of_disjoint_support, Z(ω) = 0 whenever tsupport ω ∩ spt Z = ∅. (Balls): for x ∈ ℝ^P and r > 0, W := B_r(x) is open, closure W = B̄_r(x) (`closure_ball`) is compact (`isCompact_closedBall`); so W is admissible for zeroRegion as soon as B̄_r(x) ⊆ U and Z vanishes on W.

1. (Part (1).) Let x ∈ spt ∂Z, so x ∈ U, and suppose x ∉ spt Z. Then x ∈ zeroRegion(Z): x ∈ W for some W open with closure W compact, closure W ⊆ U, and Z vanishing on W. For φ ∈ D^m(U) with tsupport φ ⊆ W we have tsupport dφ ⊆ tsupport φ ⊆ W (SimonGMT `tsupport_exteriorDerivative_subset`), so ∂Z(φ) = Z(dφ) = 0. Thus ∂Z vanishes on W, W is admissible for zeroRegion(∂Z), and x ∈ zeroRegion(∂Z), contradicting x ∈ spt ∂Z. Hence spt ∂Z ⊆ spt Z. (No openness of U is needed.)
2. (Part (2).) Let x ∈ spt Z ⊆ U and suppose x ∉ K. The set U ∖ K is open (U open, K closed) and contains x, so there is r > 0 with B̄_r(x) ⊆ U ∖ K (take half of a radius of a ball inside U ∖ K). Let W := B_r(x). For ω ∈ D^n(U) with tsupport ω ⊆ W: tsupport ω ∩ K = ∅, hence tsupport ω ∩ spt Z_j = ∅ for every j, so Z_j(ω) = 0 by (F2′); since Z_j(ω) → Z(ω) and limits in ℝ are unique, Z(ω) = 0. So Z vanishes on W, W is admissible, x ∈ zeroRegion(Z), contradicting x ∈ spt Z. Hence spt Z ⊆ K.
3. (Part (3).) Let x ∈ spt Z ⊆ U and suppose x ∉ spt Z_1 ∪ spt Z_2. As x ∈ U, x ∈ zeroRegion(Z_1) ∩ zeroRegion(Z_2) ∩ U, an open set (zero regions are unions of open sets, U is open), so there is r > 0 with B̄_r(x) contained in it. Let W := B_r(x). For ω ∈ D^n(U) with tsupport ω ⊆ W: tsupport ω ⊆ zeroRegion(Z_i), which is disjoint from spt Z_i = U ∖ zeroRegion(Z_i), so Z_i(ω) = 0 by (F2′) (i = 1, 2), and Z(ω) = a·0 + b·0 = 0. So Z vanishes on W, W is admissible (B̄_r(x) ⊆ U), x ∈ zeroRegion(Z), contradicting x ∈ spt Z. Hence spt Z ⊆ spt Z_1 ∪ spt Z_2. ∎

## Key steps

1. If Z vanishes on an admissible W then so does ∂Z, because tsupport dφ ⊆ tsupport φ; hence spt ∂Z ⊆ spt Z.
2. For x ∉ K a small ball W around x misses K, so every Z_j kills test forms supported in W (reused vanishing lemma) and so does the weak limit Z.
3. For x outside spt Z_1 ∪ spt Z_2 a small ball lies in both zero regions; both Z_i, hence Z = aZ_1 + bZ_2, vanish on it.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; sha256sum GMT/Ch06/Contract.lean`
- `python3: read nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/{parent-child-handoff,decomposition-v1,decomposition-audit-v1,decomposition-review-receipt-v1}.json`
- `python3: dag.json statuses and frozen lean_statements of iwl_im_closure, iwl_smooth_pushforward, iwl_cycle_reduction, isoperimetric_apply_eq_zero_of_disjoint_support, cmb_abs_apply_le_of_massOn_le, isoperimetric_abs_covector_apply_le, lpf_countably_rectifiable_c1_cover, lpf_rectifiable_area_formula; scan of dag.json and nodes/*/decomposition-v*.json for iwl_cr_* names`
- `rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|theorem MeasurableSet.image_of_continuousOn_injOn|theorem LinearMap.injective_iff_antilipschitz|theorem normDet_sq_eq_det_gram|theorem measurePreserving_piFinSuccAbove|theorem PiLp.volume_preserving_ofLp|theorem PiLp.volume_preserving_toLp|theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero|theorem hausdorffMeasure_zero_singleton|theorem hausdorffMeasure_apply|theorem exists_measurable_subset_ae_eq|theorem lintegral_prod |theorem Measurable.lintegral_prod_right'|theorem lintegral_iUnion |theorem lintegral_tsum' mathlib/Mathlib (snapshot)`
- `rg -n 'hausdorffMeasure.*prod|area_formula|areaJacobian' mathlib/Mathlib (snapshot)`
- `grep -rln for hasFDerivAt_integral_of_dominated_of_fderiv_le, norm_iteratedFDeriv_le_of_bilinear, norm_iteratedFDeriv_smul_le, alternatizeUncurryFin_curryLeft, extDeriv_extDeriv, tendsto_integral_filter_of_dominated_convergence, integral_integral_swap, euclideanHausdorffMeasure_homothety_image, det_succ_row_zero in snapshot Mathlib`
- `grep -n '^theorem|^def' simongmt Chapter02/{AreaLipschitz,WeightedArea,Area,AreaApproximation,AreaNoninjective}.lean, Chapter03/{Rectifiable,DisjointCover,SubmanifoldCover}.lean, Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean; rg 'pointSlice_isTestForm|iteratedFDeriv_fixedSupportParameterSlice' simongmt`
- `git show 2f3657605e574458d48b2cd837f262ae2f392816:GMT/Ch06/Submission.lean (accepted rectifiability_weighted_tangent_ae, piece construction hpart)`
- `python3 -I /tmp/cr2/scripts/gen.py (verifier gmt-compare.py child_modules + lean_contract.validate_lean_statement); lake env lean /tmp/cr2/gen/*__NodeChallenge.lean`
- `lake env lean /tmp/cr2/Scratch/Assembly.lean, SolutionCheck.lean, LibCheck.lean, JacCheck.lean, SplitCheck.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-weighted-tangent-ae-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-weighted-tangent-ae-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-density-comparison-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-vanish-off-support-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/cr2/scripts/gen.py`
- `/tmp/cr2/Scratch/Assembly.lean`
- `/tmp/cr2/Scratch/SolutionCheck.lean`
- `/tmp/cr2/Scratch/LibCheck.lean`
- `/tmp/cr2/Scratch/JacCheck.lean`
- `/tmp/cr2/Scratch/SplitCheck.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. Its Ch06 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0dd…853d).

Findings in dag.json:
- The chart-cover and rectifiable-area-formula nodes (lpf_countably_rectifiable_c1_cover, lpf_rectifiable_area_formula) are still speculative-ready, so they cannot be reused.
- No other DAG node supplies a product formula.
- iwl_im_closure and iwl_smooth_pushforward are the parent's frozen sibling dependencies, with the types used in the assembly.
- The reused isoperimetric_apply_eq_zero_of_disjoint_support, cmb_abs_apply_le_of_massOn_le and isoperimetric_abs_covector_apply_le are accepted, with identical types.

Libraries:
- rg in the snapshot Mathlib finds no area formula and no Hausdorff product formula for rectifiable sets; only hausdorffMeasure_pi_real and hausdorffMeasure_prod_real exist.
- The pinned SimonGMT package (lake-packages-25730c7c/simongmt, rev 2b36630) supplies the injective Lipschitz area formula weighted_area_formula_lipschitz_injOn (Chapter02/AreaLipschitz.lean:101). It takes an arbitrary weight, with μHE[finrank E] on the target, volume on the source and J = areaJacobianAt = normDet. It is derived from WeightedArea.lean:76/120. SimonGMT also supplies area_image_compl_regularSet_eq_zero, measurableSet_areaRegularSet and measurable_areaJacobianAt.
- Mathlib supplies exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Jacobian.lean:255), MeasurableSet.image_of_continuousOn_injOn (Polish/Basic.lean:821), LinearMap.injective_iff_antilipschitz, LinearMap.normDet_sq_eq_det_gram (NormDet.lean:303), measurePreserving_piFinSuccAbove, PiLp.volume_preserving_ofLp/toLp, lintegral_prod, lintegral_iUnion and lintegral_tsum.
- All of these print only propext, Classical.choice and Quot.sound.
- The accepted rectifiability_weighted_tangent_ae (commit 2f36576) already formalizes the same bi-Lipschitz piece construction (`hpart`).
- These inputs give a complete chart-free proof of the product formula.

Lean checks:
- 12 challenge modules and 12 solution resolutions.
- The parent assembly.
- The lift Jacobian identity and the measure-preserving split (standard axioms only).

These checks certify statements, assembly and library inputs, not the remaining analytic proofs. Those were reviewed in natural language; the v1 audit accepted 11 of them, and an independent reviewer accepted the repaired one in this session.

Public citation: Federer, GMT (1969) 3.2.23, cited for this product formula in arXiv:2505.11279.
