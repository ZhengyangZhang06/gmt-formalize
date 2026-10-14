# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.partition_tannery-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5 and 7 of the parent proof (countable additivity over the chart pieces, and dominated convergence for series), stated for an abstract measure space. In the parent: X = ℝ^P, μ = μHE[k], S = M, E_i = the disjointed chart pieces, f_j = F_j, f₀ = F, and G = max(Λ, Λ′)^k·sup‖ω‖·1_{g⁻¹(K)}·θ.

Write S′ := ⋃_i E_i.
1. (Same restricted measure.) Since S = S′ μ-a.e., μ⌞S = μ⌞S′ (Measure.restrict_congr_set), and ∫_S φ dμ = ∫_{S′} φ dμ for every φ (setIntegral_congr_set). In particular G is μ-integrable on S′.
2. (Integrability.) For every j in the eventual range of the bound, f_j is a.e.-strongly measurable for μ⌞S = μ⌞S′ and |f_j| ≤ G a.e. So f_j is μ-integrable on S′ (Integrable.mono'). Likewise f₀ is μ-integrable on S′.
3. (Countable additivity.) The E_i are null-measurable and pairwise disjoint, hence pairwise a.e.-disjoint. For φ integrable on S′, ∫_{S′} φ dμ = Σ_i ∫_{E_i} φ dμ (integral_iUnion_ae). Write a_i(j) := ∫_{E_i} f_j dμ and a_i := ∫_{E_i} f₀ dμ. With steps 1–2:
 - ∫_S f_j dμ = Σ_i a_i(j) for all large j;
 - ∫_S f₀ dμ = Σ_i a_i.
4. (Summable domination.) Let b_i := ∫_{E_i} G dμ. Since G is integrable on S′, Σ_i b_i converges, to ∫_{S′} G dμ (hasSum_integral_iUnion_ae). For each i, μ⌞E_i ≤ μ⌞S′ = μ⌞S (E_i ⊆ S′). So for all large j, |f_j| ≤ G μ⌞E_i-a.e., and |a_i(j)| ≤ b_i (norm_integral_le_of_norm_le, with G integrable on E_i).
5. (Tannery.) We have: a_i(j) → a_i for every i (hypothesis); |a_i(j)| ≤ b_i for every i and all large j; and Σ_i b_i < ∞. By dominated convergence for series (Tannery's theorem; Mathlib tendsto_tsum_of_dominated_convergence), Σ_i a_i(j) → Σ_i a_i. By step 3 and eventual equality (Tendsto.congr'), ∫_S f_j dμ → ∫_S f₀ dμ. ∎

Lean remark. The script below was verified with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b36630 as `theorem Submission.deformation_ipl_cc_tendsto_setIntegral_of_partition : (<frozen type>) := by` inside `namespace GMT.Ch06` of GMT/Ch06/Submission.lean. It uses no sibling declaration, and #print axioms gives only propext, Classical.choice and Quot.sound. It needs the additional import `import Mathlib.Analysis.Normed.Group.Tannery` (tendsto_tsum_of_dominated_convergence is not in the frozen import closure). Alternatively, prove the series limit directly by an ε-argument: cut the tail of Σ b_i.
Additional import(s):
import Mathlib.Analysis.Normed.Group.Tannery
Tactic script:
  intro X _ μ S E f f₀ G hEm hEd hSE hG hfm hf₀m hfb hf₀b hlim
  have hres : μ.restrict S = μ.restrict (⋃ i, E i) := Measure.restrict_congr_set hSE
  have hGS' : IntegrableOn G (⋃ i, E i) μ := by rw [IntegrableOn, ← hres]; exact hG
  have hint : ∀ᶠ j in atTop, IntegrableOn (f j) (⋃ i, E i) μ := by
    filter_upwards [hfb] with j hj
    rw [IntegrableOn, ← hres]
    exact Integrable.mono' hG (hfm j) (by simpa [Real.norm_eq_abs] using hj)
  have hint₀ : IntegrableOn f₀ (⋃ i, E i) μ := by
    rw [IntegrableOn, ← hres]
    exact Integrable.mono' hG hf₀m (by simpa [Real.norm_eq_abs] using hf₀b)
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ) E) := fun i j hij => (hEd hij).aedisjoint
  have hsumj : ∀ᶠ j in atTop, ∫ x in S, f j x ∂μ = ∑' i, ∫ x in E i, f j x ∂μ := by
    filter_upwards [hint] with j hj
    rw [setIntegral_congr_set hSE, integral_iUnion_ae hEm hdisj hj]
  have hsum₀ : ∫ x in S, f₀ x ∂μ = ∑' i, ∫ x in E i, f₀ x ∂μ := by
    rw [setIntegral_congr_set hSE, integral_iUnion_ae hEm hdisj hint₀]
  have hEsub : ∀ i, μ.restrict (E i) ≤ μ.restrict S := fun i => by
    rw [hres]; exact Measure.restrict_mono (subset_iUnion E i) le_rfl
  have hbsum : Summable (fun i => ∫ x in E i, G x ∂μ) :=
    (hasSum_integral_iUnion_ae hEm hdisj hGS').summable
  have hbound : ∀ᶠ j in atTop, ∀ i, ‖∫ x in E i, f j x ∂μ‖ ≤ ∫ x in E i, G x ∂μ := by
    filter_upwards [hfb] with j hj i
    refine norm_integral_le_of_norm_le (hGS'.mono_set (subset_iUnion E i)) ?_
    have hj' : ∀ᵐ x ∂(μ.restrict S), ‖f j x‖ ≤ G x := by simpa [Real.norm_eq_abs] using hj
    exact ae_mono (hEsub i) hj'
  have htan := tendsto_tsum_of_dominated_convergence hbsum hlim hbound
  rw [hsum₀]
  exact htan.congr' (hsumj.mono fun j hj => hj.symm)

## Key steps

1. μ⌞S = μ⌞⋃E_i, and eventually f_j, as well as f₀, are integrable on ⋃E_i (dominated by G).
2. Countable additivity (integral_iUnion_ae): eventually ∫_S f_j = Σ_i ∫_{E_i} f_j, and ∫_S f₀ = Σ_i ∫_{E_i} f₀.
3. |∫_{E_i} f_j| ≤ b_i := ∫_{E_i} G with Σ_i b_i = ∫_{⋃E_i} G < ∞; Tannery's theorem (tendsto_tsum_of_dominated_convergence) passes to the limit.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp of workspace GMT/Ch06/Submission.lean, GMT/Ch06/Contract.lean and the snapshot project/GMT/Ch06/Contract.lean (byte-identical)`
- `python3 -I over dag.json: status, candidate_commit and lean_statement of the node's dependencies lpf_simple_nvector_algebra, lpf_countably_rectifiable_c1_cover, lpf_chart_chain_rule, lpf_raf_chart_change_of_variables (accepted), deformation_ipl_minor_weak_continuity and deformation_ipl_tangential_pushforward_aestronglyMeasurable (decomposing)`
- `python3 -I over dag.json: regex search jacob|change_of_var|antilip|gram|det|tannery|dominat|chart|area|orient|simple|pushforward over lean names, then lean_statement of lpf_wtc_cat_fderiv_lower_bound, lpf_wtc_cat_gram_jacobian_continuous, lpf_wtc_caf_signed_of_lintegral, lpf_pi_jacobian_local_bound, lpf_pi_measurability, lpf_pic_density_dominated, lpf_raf_chart_preimage_null, lpf_ccr_ae_pullback, lpf_weighted_tangent_on_c1_chart, lpf_wtc_chart_image_measurable_locally_finite, iwl_sp_sn_signed_simpleNVector_bound_ne_zero, fiw_ims_frame_sign, slicing_im_ll_twl_chart_integral_eq (decomposing, not reusable)`
- `python3 -I over nodes/*/parent-child-handoff.json: map the six reused node ids to their directories and check title/statement/lean_statement/lean_name byte-identity with dag.json (all True)`
- `python3 -I over dag.json: lean-name collision check for deformation_ipl_cc_gram_det_lower_bound, deformation_ipl_cc_signed_change_of_variables, deformation_ipl_cc_chart_orientation_sign, deformation_ipl_cc_chart_integral_representation, deformation_ipl_cc_pushforward_integrand_bound, deformation_ipl_cc_tendsto_setIntegral_of_partition (none); rg -l deformation_ipl_cc over GMT, snapshot project, snapshot Mathlib and SimonGMT (no match); git grep over all local branches (no match)`
- `rg -n 'abbrev (Covector|NVector)|def (simpleNVector|nVectorPushforward|covectorPullback|wedgeCovectors)|theorem wedgeCovectors_apply_det|theorem nVectorPushforward_simple' simongmt/Poincare/SimonGMT/Chapter06; rg -n 'HasWeightedApproximateTangentSpaceAt' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n over snapshot Mathlib: IsOpen.isSigmaCompact (no match), NullMeasurableSet.disjointed, disjointed_subset|iUnion_disjointed|disjoint_disjointed, integral_iUnion_ae, hasSum_integral_iUnion_ae, tendsto_tsum_of_dominated_convergence, setIntegral_congr_set, setIntegral_indicator, aestronglyMeasurable_indicator_iff₀, aestronglyMeasurable_iUnion_iff, Matrix.IsHermitian det_eq_prod_eigenvalues|eigenvalues_eq|mulVec_eigenvectorBasis, prod_le_prod₀, adjoint_inner_right, continuous_compContinuousLinearMapCLM, integral_eq_lintegral_pos_part_sub_lintegral_neg_part, Orthonormal.inner_right_fintype, mem_span_range_iff_exists_fun, HasDerivAt.le_of_lipschitz, norm_fderiv_le_of_lipschitz, IsCompact.cthickening, mem_cthickening_of_dist_le, image_eq_zero_of_notMem_tsupport, HasCompactSupport.exists_bound_of_continuous, opNorm_smul_le, NormedSpace.toNormSMulClass`
- `git show 9fc44225b304fca8af9dead3256575ef03818d1e:GMT/Ch06/Submission.lean (accepted declaration format) and the import lines of all accepted candidate Submissions (extra imports already accepted)`
- `python3 -I verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py child_modules (mode contract) for the twelve types`
- `lake env lean /tmp/ccv-decomp/ExactScope.lean (twelve types, exit 0); /tmp/ccv-decomp/Assembly.lean (parent from child and dependency types); /tmp/ccv-decomp/Dproof.lean, Cproof.lean, Bproof.lean, Aproof.lean (+Mathlib.Analysis.Matrix.Spectrum), Eproof.lean, Fproof.lean (+Mathlib.Analysis.Normed.Group.Tannery); /tmp/ccv-decomp/Final_*.lean (final Submission.* forms against stubs); /tmp/ccv-decomp/Inst.lean (NormSMulClass ℝ (NVector …) not synthesized)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-audit-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-simple-nvector-algebra-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1-ae-pullback-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ch-1ba1e0b708/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-1f4173ea67/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Matrix/Spectrum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/ccv-decomp/ExactScope.lean`
- `/tmp/ccv-decomp/Assembly.lean`
- `/tmp/ccv-decomp/Dproof.lean`
- `/tmp/ccv-decomp/Cproof.lean`
- `/tmp/ccv-decomp/Final_parent.lean`

Pinned revisions are confirmed, and the frozen contract is byte-identical to the snapshot (Submission = Contract).
Reuse:
- Six accepted declarations are reused by name: lpf_simple_nvector_algebra, lpf_weighted_tangent_on_c1_chart, lpf_ccr_ae_pullback, lpf_raf_chart_change_of_variables, lpf_wtc_cat_fderiv_lower_bound and lpf_wtc_chart_image_measurable_locally_finite.
- Each has status accepted with a candidate commit, and its title, statement and Lean type are copied byte-for-byte from dag.json (identical to its handoff).
- The node's other dependencies (c1_cover, chart_chain_rule, minor_weak_continuity, pushforward_measurable) are used only by the parent assembly.
- No accepted DAG node or library lemma states the signed chart change of variables, the measurable chart orientation sign, the chart integral representation or the partition Tannery lemma. slicing_im_ll_twl_chart_integral_eq is still decomposing, so it cannot be reused.
New names: the six deformation_ipl_cc_ names collide with nothing in dag.json, the project, SimonGMT or the pinned Mathlib.
Library support (all present in the snapshot):
- Matrix.IsHermitian spectral theorem (det_eq_prod_eigenvalues, eigenvalues_eq) and tendsto_tsum_of_dominated_convergence; both modules need an extra import.
- NullMeasurableSet.disjointed, integral_iUnion_ae, hasSum_integral_iUnion_ae, integral_eq_lintegral_pos_part_sub_lintegral_neg_part, ContinuousLinearMap.adjoint_inner_right and ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.
- SimonGMT: wedgeCovectors_apply_det, nVectorPushforward_simple and HasWeightedApproximateTangentSpaceAt.unique.
- IsOpen.isSigmaCompact does not exist; the open-set exhaustion is written out explicitly.
- NormSMulClass ℝ (NVector …) is not synthesized; opNorm_smul_le is used instead.
Lean checks:
- All twelve types validate and elaborate in the exact comparator scope.
- The parent assembly compiles from the frozen child and dependency types.
- Every new child compiles from exactly its declared sibling types.
- All of these give only propext, Classical.choice and Quot.sound.
