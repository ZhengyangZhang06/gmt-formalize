# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.flux_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.flux_density-a1.cone_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5(i) (Scaling) of the parent-supplied proof of idtp_cse_flux_density_eq.
1. Fix r > 0 and let S(x) := rx. S is a homeomorphism of ℝ^P with inverse x ↦ r^{−1}x (Homeomorph.smulOfNeZero r), hence a measurable equivalence e (Homeomorph.toMeasurableEquiv) with e x = rx.
2. (Image measure.) Claim: map S μ = ofReal((r^{−1})^n)·μ. By Measure.ext it suffices to compare both sides on Borel sets A. By Measure.map_apply (S measurable, A Borel), (map S μ)(A) = μ(S^{−1}(A)), and S^{−1}(A) = {x : rx ∈ A} = (y ↦ r^{−1}y)''A: if rx ∈ A then x = r^{−1}(rx), and conversely r(r^{−1}y) = y ∈ A (smul_smul, inv_mul_cancel₀, mul_inv_cancel₀). By the sibling cone_measure (the accepted theorem Submission.cone_current_imrep_measure_smul_image, applied with λ := r^{−1} > 0 and the Borel set A), μ((y ↦ r^{−1}y)''A) = ofReal((r^{−1})^n)·μ(A). Hence (map S μ)(A) = (ofReal((r^{−1})^n)·μ)(A) for every Borel A, proving the claim.
3. (Change of variables.) For every φ : ℝ^P → ℝ, integral_map_equiv for the measurable equivalence e (valid for arbitrary φ) gives ∫ φ d(map S μ) = ∫ φ(S x) dμ(x) = ∫ φ(rx) dμ(x). By step 2 and integral_smul_measure (also valid for arbitrary φ), ∫ φ(rx) dμ(x) = ∫ φ d(ofReal((r^{−1})^n)·μ) = toReal(ofReal((r^{−1})^n))·∫ φ dμ = (r^{−1})^n ∫ φ dμ (ENNReal.toReal_ofReal, as (r^{−1})^n ≥ 0).
4. Since (r^{−1})^n = (r^n)^{−1} (inv_pow), ∫ φ(rx) dμ(x) = (r^n)^{−1} ∫ φ dμ. ∎
(Formalization note, not part of the argument: after rewriting with integral_map_equiv, identify e x with r • x by simp only [Homeomorph.toMeasurableEquiv_coe, Homeomorph.smulOfNeZero_apply]; closing that goal by rfl elaborates extremely slowly.)

## Key steps

1. {x : rx ∈ A} = r^{−1}A, so the reused cone-weight homogeneity with λ = r^{−1} gives map(x ↦ rx)μ = ofReal(r^{−n})·μ on Borel sets, hence as measures.
2. Change of variables for the measurable equivalence x ↦ rx (integral_map_equiv) and integral_smul_measure give ∫φ(rx)dμ = (r^n)^{−1}∫φ dμ for every φ.

## Reference use

### local-project

Queries:
- `rg -n 'lemma support_mem_ae|theorem integral_map_equiv|theorem integral_smul_measure|theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|theorem integral_eq_lintegral_of_nonneg_ae|lemma Continuous.bounded_above_of_compact_support|protected theorem HasCompactSupport.deriv|theorem ContDiff.continuous_deriv|protected lemma mono_ac|theorem _root_.Continuous.comp_aestronglyMeasurable₂|theorem norm_starProjection_apply_le|theorem ae_lt_top'|theorem setLIntegral_prod|theorem prod_restrict|theorem withDensity_absolutelyContinuous' local-references/123e8435b4a2469b/mathlib`
- `rg -n 'HereditarilyLindelofSpace X where' -B2 local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Lindelof.lean`
- `rg -n 'idtp_cse_fd_|cone_current_imrep_measure_smul_image|imrep_represents_support_eq_inter_measure_support|imrep_approxTangent_starProjection_aesm' local-references/123e8435b4a2469b/project (no match: the snapshot project is the pristine contract)`
- `rg -n 'def IsConeCurrent|def approxTangentPlane|def IMRep.measure|locallyIntegrable_mult' local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `grep -rn 'starProjection_eq_self_iff|inner_starProjection_left_eq_right|norm_sub_sq_real|real_inner_smul_left|measure_eq_zero_iff_ae_notMem|integral_Ioc_eq_integral_Ioo|Continuous.integrableOn_Icc|integral_id|max_zero_sub_eq_self|Integrable.of_bound|isFiniteMeasure_restrict|aestronglyMeasurable_comp₂|AEMeasurable.ennreal_toReal' over the pinned Mathlib (lake-packages-25730c7c/mathlib)`
- `python3 scan of dag.json: lean_statement/status/candidate_commit/proof_base_commit of the six sibling dependencies of the selected node and of imrep_represents_support_eq_inter_measure_support, cone_current_imrep_measure_smul_image, imrep_approxTangent_starProjection_aesm, imrep_measure_eq_of_represents_same_current; census of reused-child edges (parent.children entries whose parent differs) = 506`
- `grep -c idtp_cse_fd_ dag.json; grep -rl idtp_cse_fd_ nodes/ local-references/ and all .swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean (no match)`
- `git -C .github-mirror/gmt-formalize.git show 1d65cf6d4d:GMT/Ch07/Submission.lean (proof base of the selected node: 457 lines, no Submission.* theorem)`
- `read /runtime/flows/gmt-claude-44ad5d9baeee/_recursive_lean/runtime.py: _existing_lean_name_problem, child activation id mapping, _install_parent_supplied_child_handoff, _overlay_accepted_children, _solve/_resume_accepted_candidate (reuse of accepted names; overlay of children and depends_on histories)`
- `lean /tmp/fdx-check/Stmts.lean (all 14 declarations elaborate in the contract scope); lean /tmp/fdx-check/final/ParentAx.lean (parent type from axiomatized children + six sibling dependencies; axioms: propext, Classical.choice, Quot.sound + those dependencies, no sorryAx); lean A.lean, B3.lean, C.lean, D.lean, E.lean (each new child fully proved with only its declared dependency axiomatized)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Lindelof.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-27685c46df/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-18ac87081c/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-support-eq-measure-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-tangent-projection-measurable-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-44ad5d9baeee/_recursive_lean/runtime.py`
- `/tmp/fdx-check/Stmts.lean`
- `/tmp/fdx-check/final/ParentAx.lean`
- `/tmp/fdx-check/final/A.lean`
- `/tmp/fdx-check/final/B3.lean`
- `/tmp/fdx-check/final/C.lean`
- `/tmp/fdx-check/final/D.lean`
- `/tmp/fdx-check/final/E.lean`

The snapshot pins project b4d606db and mathlib 25730c7c. Its project is the pristine contract with no accepted Submission.* lemmas, and the selected node's proof base (dispatch commit 1d65cf6d) is likewise pristine. So the three accepted theorems from other branches that the supplied proof cites are reused as children: their frozen types are byte-identical to the DAG, their status is accepted, and they have candidate commits. Every Mathlib name used in the child proofs exists at the pin, including support_mem_ae (via SecondCountableTopology.toHereditarilyLindelof), integral_map_equiv, integral_smul_measure, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, integral_eq_lintegral_of_nonneg_ae, AEStronglyMeasurable.mono_ac, ContinuousLinearMap.aestronglyMeasurable_comp₂, norm_starProjection_apply_le, HasCompactSupport.deriv, ContDiff.continuous_deriv, Continuous.bounded_above_of_compact_support and lintegral_prod/prod_restrict. No idtp_cse_fd_* name exists anywhere. All 8 child types elaborate. Each new child was proved in Lean with only its declared dependency axiomatized. The parent's frozen type follows from the children and its six sibling dependencies, kernel-checked with otherwise only standard axioms.
