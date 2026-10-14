# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.slice_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent V4(ii). Uses (SL) = sibling slicing and (REP), (T1), (T2), (MM), (IML) of sibling foundations; CL_P(d) only in the open balls W_k := B_{k+1}(0) ⊆ ℝ^P.
1. For bounded open W, Λ_W := sup_i(M_W(X_i) + M_W(∂X_i)) < ∞ and, by lower semicontinuity, M_W(X), M_W(∂X) ≤ Λ_W.
2. Fix admissible (μ, ξ), (μ', ξ') of X, ∂X and L-Lipschitz f. (REP) gives mass representations (μ_i, ξ_i), (μ'_i, ξ'_i) of X_i, ∂X_i; by (T1), along a subsequence, limsup_i μ_i(K) ≤ ν(K) and limsup_i μ'_i(K) ≤ ν'(K) for compact K.
3. (SL) gives A_{i,t}, B_{i,t} and Z_{i,t} := ∂A_{i,t} − B_{i,t} with M_W(Z_{i,t}) ≤ L·liminf_h h⁻¹μ_i(W ∩ {t−h<f<t}); if d ≥ 1, (SL) applied to ∂X_i (with (0, 0) for ∂∂X_i = 0) gives M_W(∂B_{i,t}) ≤ L·liminf_h h⁻¹μ'_i(W ∩ {t−h<f<t}). ISP of X_i gives null sets N_i off which Z_{i,t} is IM.
4. (MM) with μ_i + μ'_i, G := W_k, (a, b) := (−m, m) gives, for a.e. t, liminf_i(M_{W_k}(Z_{i,t}) + M_{W_k}(∂B_{i,t})) < ∞ for all k; ν{f = t} = ν'{f = t} = 0 off a countable set (countable_meas_level_set_pos). Let N be the union of all these exceptional sets and of the N_i; fix t ∉ N and A, B as in ISP.
5. (T2) for X_i ⇀ X and ∂X_i ⇀ ∂X gives A_{i,t}(ω) → A(ω) and B_{i,t}(η) → B(η), so Z_{i,t} ⇀ Z := ∂A − B.
6. Fix k and a subsequence with bounded M_{W_k}(Z_{i,t}) + M_{W_k}(∂Z_{i,t}) (∂Z_{i,t} = −∂B_{i,t}). The restrictions Z_{i,t}|_{W_k} are IM ((IML)(2)) and converge weakly to Z|_{W_k}, so CL_P(d) in W_k shows Z|_{W_k} IM; lower semicontinuity gives M_W(Z) < ∞ for bounded W.
7. Each B_1(x) lies in some W_k, so Z|_{B_1(x)} is IM by (IML)(2), and Z is IM by (IML)(1). Hence X has ISP. ∎

## Key steps

1. Representations, limit measures and slices of X_i.
2. Good levels by (MM); slices converge by (T2).
3. CL_P(d) on balls and gluing.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD (b4d606db)`
- `cmp GMT/Ch07/Contract.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `grep -rn 'theorem exists_disjoint_subfamily_covering_enlargement_closedBall|theorem exists_disjoint_subfamily_covering_enlargement |theorem hausdorffMeasure_le_liminf_tsum|theorem exists_disjoint_closedBall_covering_ae |theorem ae_tendsto_average_norm_sub|theorem tendsto_filterAt|theorem exists_isOpen_lt_of_lt|theorem measure_toMeasurable_inter_of_sFinite|euclideanHausdorffMeasure_eq_volume|theorem hausdorffMeasure_image_le|lemma isMulLeftInvariant_eq_smul |theorem tendsto_of_subseq_tendsto' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `sed -n 40,75p and 150,185p mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean; sed -n 545,575p mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean; sed -n 1,140p and 185,200p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE[d] := addHaarScalarFactor(volume, μH[d]) • μH[d])`
- `grep -rn 'theorem simon_theorem_3_3|theorem simon_theorem_3_26_i|theorem simon_theorem_2_10|simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure' lake-packages-25730c7c/simongmt/Poincare/SimonGMT; sed -n 1,280p Chapter03/Rectifiable.lean (HasApproximateTangentSpaceAt, CountablyRectifiable, blowUpMap); grep -n 'def massAdmissibleOn|def GeometricCurrentOn.massOn|massOn_le_liminf' Chapter06/Mass.lean`
- `lake env lean (run.py) Reach.lean / Reach2.lean / Reach3.lean / Reach4.lean after import GMT.Ch07.Submission: #check of Vitali.exists_disjoint_subfamily_covering_enlargement, Measure.hausdorffMeasure_le_liminf_tsum, Besicovitch.exists_disjoint_closedBall_covering_ae, Besicovitch.tendsto_filterAt, VitaliFamily.ae_tendsto_average_norm_sub, Set.exists_isOpen_lt_of_lt, Measure.measure_toMeasurable_inter_of_sFinite, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, LipschitzWith.hausdorffMeasure_image_le, Isometry.euclideanHausdorffMeasure_image, Measure.isAddLeftInvariant_eq_smul, tendsto_of_subseq_tendsto, integral_withDensity_eq_integral_toReal_smul, Measure.haveLebesgueDecomposition_add, Measure.singularPart_eq_zero_of_ac, CountablyRectifiable.mono, WeaklyConvergesOn.massOn_le_liminf (all found); Poincare.SimonGMT.Chapter01.simon_theorem_3_26_i and simon_theorem_2_10 (unknown identifier)`
- `python3 -I over dag.json: statuses/candidate commits of cmc_slice_mass_bounds, cbr_setIntegral_eq_of_integral_eq, cbr_isoperimetric_filling, dimred_mbl_fnd_exists_massRepresentation_core, dimred_mbl_fnd_null_of_representation, cbr_vague_*, cbr_sublevel_restriction_tendsto, cbr_slice_mass_majorant, cbr_isIntegerMultiplicity_of_local_reps, cbr_imRep_measure_basic, cbr_orient_ae_eq_of_setIntegral_eq, cmcdt_*, cbrcs_localize_at_point, cmc_deformation_theorem, dimred_mbl_deformation_theorem, cmc_closure_and_boundary_rectifiability, cbr_ci_*; prefix scan dtc_bc_tc_cl`
- `python3 -I string comparison: frozen types of slicing/restrict_unique/rectifiable/(MR) versus the hypothesis prefixes of cbr_ci_dilation_slice_property, cbr_ci_plane_multiplicity_nat, cbr_ci_isIntegerMultiplicity_of_ae_tangent and the type of cbr_rectifiable_of_approx_tangent (all equal)`
- `lake env lean (run.py) /tmp/dtc_closure_v2/lean/Types.lean (12 frozen types, exit 0) and Assembly.lean (#print axioms: propext, Classical.choice, Quot.sound); verifier/lean_contract.py validate_lean_statement on all 12 types`
- `sed of the parallel-branch proofs: nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-{33509b6e86,951a399d2e,479700eeeb,87895248bb,3684511996,af13c47156,d8eab44069,57440db406}/parent-supplied-natural-proof.md (cycle_im, weight_ge_one, good_points, upper_density, isodiametric, density_rep, blowup_limit, pointwise)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/EuclideanNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-e6c3d0d31e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-e6c3d0d31e/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-e6c3d0d31e/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-compactness-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-951a399d2e/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-33509b6e86/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-479700eeeb/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3684511996/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dtc_closure_v2/lean/Types.lean`
- `/tmp/dtc_closure_v2/lean/Assembly.lean`
- `/tmp/dtc_closure_v2/lean/Reach.lean`

The snapshot (local-project, project b4d606db, Mathlib 25730c7c) has a Ch07 Contract.lean byte-identical to the workspace Contract.lean and Submission.lean. It contains no proved closure, deformation, density-comparison or rectifiability theorem. Every Mathlib lemma named in the repaired cycle_im proof exists in the snapshot and resolves after import GMT.Ch07.Submission: Vitali.exists_disjoint_subfamily_covering_enlargement (the 'meets a larger chosen ball' form needed for the finite tail), hausdorffMeasure_le_liminf_tsum, Besicovitch Lebesgue differentiation, outer regularity, Measure.measure_toMeasurable_inter_of_sFinite, LipschitzWith.hausdorffMeasure_image_le, Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Haar uniqueness and tendsto_of_subseq_tendsto. SimonGMT's simon_theorem_3_3, simon_theorem_3_26_i and simon_theorem_2_10 exist in the pinned library but are not importable from the contract. The sharp density comparison and the isodiametric normalization are therefore proved inline; the latter is also the accepted declaration cbr_ci_euclideanHausdorff_le_isodiametric. Mathlib defines μHE[n] = c_n•μH[n], so the isodiametric bound c_n ≤ ω_n/2ⁿ is exactly what the upper-density bound Θ* ≤ 1 needs. All twelve frozen types still elaborate, and the parent assembly compiles with only propext, Classical.choice and Quot.sound. The reused declarations are accepted with identical types. The cited accepted cbr_ci_* declarations have hypotheses identical to the sibling frozen types. No dtc_bc_tc_cl_* name is reserved.
