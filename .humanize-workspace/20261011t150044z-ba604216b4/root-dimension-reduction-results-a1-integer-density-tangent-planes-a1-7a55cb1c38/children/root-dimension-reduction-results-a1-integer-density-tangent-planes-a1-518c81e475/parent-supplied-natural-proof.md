# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.flux_density-a1.fibre_signed-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.flux_density-a1.fibre_signed-a1.ratio_aesm-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2(b) (measurability of G) of the parent-supplied proof of idtp_cse_fd_fibre_signed_identity, stated for general n and U and for the unrestricted weight μ (the parent then restricts to its sector Z).
1. (Tangent projection field.) By the accepted sibling theorem tangent_aesm, i.e. Submission.imrep_approxTangent_starProjection_aesm applied to P, n, U and R, the operator-valued map x ↦ p_{T_x} = (approxTangentPlane n M x).starProjection, with values in ℝ^P →L[ℝ] ℝ^P, is a.e. strongly measurable for H^n⌞M = μHE[n].restrict R.carrier.
2. (Transfer to μ.) By definition (IMRep.measure), μ = (H^n⌞M).withDensity θ, so μ ≪ H^n⌞M (withDensity_absolutelyContinuous). A.e. strong measurability passes to an absolutely continuous measure (AEStronglyMeasurable.mono_ac), so x ↦ p_{T_x} is μ-a.e. strongly measurable.
3. (Evaluation at Ax.) The map x ↦ Ax = ⟨x,a⟩e − ⟨x,e⟩a is continuous (continuity of the inner product, of scalar multiplication and of subtraction), hence μ-a.e. strongly measurable. The evaluation (L, v) ↦ L v is the continuous bilinear map given by the identity continuous linear map of the operator space ℝ^P →L[ℝ] ℝ^P. Applying ContinuousLinearMap.aestronglyMeasurable_comp₂ to it, to the map of step 2 and to x ↦ Ax shows that x ↦ p_{T_x}(Ax) is μ-a.e. strongly measurable.
4. (Numerator.) Norm and squaring are continuous, so N(x) := |p_{T_x}(Ax)|² is μ-a.e. strongly measurable, and in particular μ-a.e. measurable as a real-valued function.
5. (Denominator.) D(x) := |πx|² is continuous (π is a continuous linear map; norm and squaring are continuous), hence measurable.
6. (Quotient.) Real division is a measurable operation on ℝ (ℝ has measurable division in both arguments, including the convention t/0 = 0), so G = N/D is μ-a.e. measurable (AEMeasurable.div). As ℝ is second countable and metrizable, a μ-a.e. measurable real-valued function is μ-a.e. strongly measurable (AEMeasurable.aestronglyMeasurable). Hence G is μ-a.e. strongly measurable. ∎

## Key steps

1. tangent_aesm: x ↦ p_{T_x} is H^n⌞M-a.e. strongly measurable; μ = (H^n⌞M).withDensity θ ≪ H^n⌞M transfers this to μ (mono_ac).
2. Evaluation at the continuous field Ax (aestronglyMeasurable_comp₂ with the identity of the operator space), then norm and square.
3. Divide by the continuous |πx|² (AEMeasurable.div) and convert back to a.e. strong measurability.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); lake-manifest.json of the compilation workspace (mathlib 25730c7c) and git rev-parse HEAD of lake-packages-25730c7c/mathlib; cmp workspace GMT/Ch07/Submission.lean with snapshot project/GMT/Ch07/Submission.lean (identical)`
- `rg -n 'def approxTangentPlane|def IMRep.measure|locallyIntegrable_mult|structure IMRep' project/GMT/Ch07/Contract.lean`
- `rg -n 'idtp_cse_fd_fs_|imrep_approxTangent_starProjection_aesm|pushforward_signed_transfer|frame_ratio' project/ (no match: the snapshot project is the pristine contract)`
- `rg -n -F / grep -n over mathlib/Mathlib (whole tree or targeted subdirectories) for: 'theorem ae_lt_top'', 'theorem integral_eq_lintegral_of_nonneg_ae', 'theorem hasFiniteIntegral_iff_ofReal', 'theorem Integrable.bdd_mul', 'lemma Integrable.of_bound', 'theorem norm_starProjection_apply_le', 'theorem inner_starProjection_left_eq_right', 'theorem starProjection_eq_self_iff', 'theorem ofReal_toReal_le', 'aestronglyMeasurable_comp₂', 'theorem lintegral_indicator ', 'theorem withDensity_absolutelyContinuous', 'protected lemma mono_ac', 'theorem norm_sub_sq_real|theorem norm_add_sq_real', 'max_zero_sub_eq_self', 'theorem AEMeasurable.ennreal_toReal', 'theorem integrable_toReal_of_lintegral_ne_top', 'theorem ae_restrict_mem', 'theorem restrict_restrict ', 'theorem withDensity_apply ', 'class HasOrthogonalProjection'`
- `python3 scan of dag.json: lean_statement/status/candidate_commit of root.minimizing_implies_stationary-a1.tangent_projection_measurable-a1 and of the selected node; DAG lemmas matching IsFiniteMeasure/R.measure K ≠ ∞ and names containing transfer/frame; all nodes whose lean_statement contains 'inner ℝ x a • e - inner ℝ x e • a', '∀ b : ℝ × ℝ → ℝ≥0∞' or AEStronglyMeasurable+approxTangentPlane (finds the accepted idtp_cse_fc_planar_fibre_geometry, idtp_cse_bml_tilt_pointwise_bound, dorag_approxTangent_starProjection_aesm, idtp_cse_fibre_area_identities, idtp_cse_rotation_conservation, idtp_cse_fc_jacobian_upper)`
- `grep -rl 'idtp_cse_fd_fs_|frame_ratio_le_one|frame_ratio_aesm|pushforward_signed_transfer' nodes/ dag.json decomposition-reopenings/ (no match)`
- `git show d9c9559b:GMT/Ch07/Submission.lean (selected node proof base: pristine, only main_theorem); git show 36b2d372:GMT/Ch07/Submission.lean and git show ee1e2fe5:GMT/Ch07/Submission.lean (accepted tangent_aesm and planar_geometry candidates: pristine contract plus one theorem each)`
- `lean (4.35.0-rc3, LEAN_PATH of the workspace) on /tmp/fs-split-check/work/Stmts.lean, B.lean, C.lean, ParentAx2.lean and /tmp/fs-split-check/real2/Full2.lean (pristine contract + accepted 36b2d372 and ee1e2fe5 theorem blocks + the two new children + parent assembly, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Group/MinMax.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-7a55cb1c38/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-27685c46df/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-tangent-projection-measurable-a1/parent-child-handoff.json`
- `/tmp/fs-split-check/work/Stmts.lean`
- `/tmp/fs-split-check/work/B.lean`
- `/tmp/fs-split-check/work/C.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-65b004cf60/parent-child-handoff.json`
- `/tmp/fs-split-check/work/ParentAx2.lean`
- `/tmp/fs-split-check/real2/Full2.lean`

The snapshot pins project b4d606db and mathlib 25730c7c, the same revisions used for compilation, and its Submission.lean is byte-identical to the pristine contract; the selected node's proof base d9c9559b is also pristine. The contract confirms IMRep.measure = (μHE[n].restrict carrier).withDensity mult, the locallyIntegrable_mult field and approxTangentPlane as used. No idtp_cse_fd_fs_* name or proposal exists in the snapshot, dag.json or any node directory. Every Mathlib lemma cited in the child proofs exists at the pin; HasOrthogonalProjection is a Prop class, so projection instances are proof-irrelevant. The DAG scan found the accepted idtp_cse_fc_planar_fibre_geometry, whose part (a) |p_T(Ax)| ≤ |πx| yields the frame bound G ≤ 1 under exactly the parent's hypotheses. It is therefore reused (byte-identical type, candidate ee1e2fe5) instead of introducing a duplicate. idtp_cse_bml_tilt_pointwise_bound needs an unavailable radial-tangency hypothesis, and no accepted lemma states the abstract transfer or the measurability of G. The other reuse is the accepted tangent_aesm (byte-identical type, candidate 36b2d372). All four child types elaborate in the contract scope. signed_transfer was proved with standard axioms, and ratio_aesm with only tangent_aesm axiomatized. The parent's exact frozen type compiles from the children. A file merging both accepted sources into the pristine contract proves everything with only propext, Classical.choice and Quot.sound.
