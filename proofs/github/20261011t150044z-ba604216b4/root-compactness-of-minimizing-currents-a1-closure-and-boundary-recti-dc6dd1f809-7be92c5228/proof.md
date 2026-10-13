# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.plane_map-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 0, 8 and 12 of the parent proof ('p|_{V₀+w} is an isometry onto ℝⁿ and Hⁿ = Lⁿ on ℝⁿ, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.map_euclideanHausdorffMeasure').
1. (A parametrisation of Π.) Define ι : ℝⁿ → ℝ^P, ι(z) := w + Σ_i (z_i − ⟨v_i, w⟩)·v_i. It is continuous (affine), hence measurable.
2. (pL∘ι = id.) (pL ι(z))_k = ⟨v_k, w⟩ + Σ_i (z_i − ⟨v_i, w⟩)⟨v_k, v_i⟩ = ⟨v_k, w⟩ + z_k − ⟨v_k, w⟩ = z_k by orthonormality; so pL(ι z) = z (ext on Euclid n).
3. (ι is an isometry.) ι(z) − ι(z') = Σ_i (z_i − z'_i)v_i and, v being orthonormal, ‖Σ_i c_i v_i‖² = Σ_i c_i² (Orthonormal.inner_sum / norm_sq of an orthonormal combination), which is ‖z − z'‖² in Euclid n (EuclideanSpace.norm_eq). So dist(ι z, ι z') = dist(z, z') (Isometry.of_dist_eq).
4. (range ι = Π.) If y = ι(z) then y − w = Σ_i c_i v_i ∈ span(v). Conversely, if y − w ∈ span(v), write y − w = Σ_i c_i v_i (Submodule.mem_span_range_iff_exists_fun); taking inner products with v_k gives c_k = ⟨v_k, y − w⟩. With z := pL y (z_i = ⟨v_i, y⟩) we get ι(z) = w + Σ_i (⟨v_i, y⟩ − ⟨v_i, w⟩)v_i = w + Σ_i ⟨v_i, y − w⟩v_i = w + (y − w) = y.
5. (Hausdorff measure.) By Isometry.map_euclideanHausdorffMeasure, Measure.map ι μHE[n] = μHE[n].restrict (range ι) = μHE[n].restrict Π (μHE[n] on Euclid n on the left, on Euclid P on the right), and μHE[n] = volume on Euclid n (EuclideanSpace.euclideanHausdorffMeasure_eq_volume n).
6. (Conclusion.) Measure.map pL (μHE[n].restrict Π) = Measure.map pL (Measure.map ι volume) = Measure.map (pL∘ι) volume (Measure.map_map; pL, ι measurable) = Measure.map id volume = volume. ∎

## Key steps

1. Parametrise Π by the affine map ι(z) = w + Σ_i (z_i − ⟨v_i, w⟩)v_i.
2. ι is an isometry with range Π and pL∘ι = id.
3. Isometry.map_euclideanHausdorffMeasure and μHE[n] = volume on ℝⁿ give map ι volume = Hⁿ⌞Π.
4. Hence map pL (Hⁿ⌞Π) = map (pL∘ι) volume = volume.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `python3 -I scans of /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json: lean_name prefix cbr_ci_pw (no match among 1331 names; all 11 new names fresh); cbr_ci_* names of the sibling branch; accepted covector lemmas (regcomp_covector_sq_sum_orthonormalBasis accepted, candidate_commit 16144a475b, frozen type byte-identical to the proposed sq_sum child; regcomp_covector_eval_orthonormal_le, dgoj_exists_det_covector, dgcr_bwd_coordinate_covector, dgoj_exists_continuous_covector_eval also accepted); extraction of the frozen REP, SL, T2, MM components from the selected node's lean_statement`
- `sed /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean, Currents.lean, Mass.lean, FormSupNorm.lean (Covector, DifferentialForm, IsTestForm, TestFormOn, TestFormOnConverges, GeometricCurrentOn, boundary, exteriorDerivativeTestOn, WeaklyConvergesOn, covectorEuclideanNorm, massAdmissibleOn, massOn, le_massOn, extDeriv-based exteriorDerivative)`
- `rg -n in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib: 'theorem exists_contDiff_support_eq_eq_one_iff' (Geometry/Manifold/PartitionOfUnity.lean:789), 'theorem exists_contDiff_tsupport_subset' (Analysis/Calculus/BumpFunction/FiniteDimension.lean:45), 'theorem measure_toMeasurable_inter_of_sFinite' (MeasureTheory/Measure/Typeclasses/SFinite.lean:477), 'theorem hausdorffMeasure_image_le' (MeasureTheory/Measure/Hausdorff.lean:745), 'euclideanHausdorffMeasure_def' and 'Isometry.map_euclideanHausdorffMeasure' (Geometry/Euclidean/Volume/Measure.lean), 'def apply' (Topology/Algebra/Module/Alternating/Topology.lean:294), 'continuous_of_finiteDimensional' (only the LinearMap version; no multilinear version)`
- `lake env lean /tmp/w1-decomp/T0.lean, T1.lean, T2.lean (#check reachability after import GMT.Ch07.Submission: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.map_euclideanHausdorffMeasure, LipschitzWith.hausdorffMeasure_image_le, extDeriv_pullback, extDeriv_apply, exists_contDiff_support_eq_eq_one_iff, MeasureTheory.ext_of_generate_finite, Measure.haveLebesgueDecomposition_add, Measure.singularPart_eq_zero_of_ac, integral_withDensity_eq_integral_toReal_smul, Measure.measure_toMeasurable_inter_of_sFinite, AlternatingMap.eq_smul_basis_det, Matrix.det_succ_column_zero, Filter.EventuallyEq.fderiv_eq, Filter.extraction_forall_of_frequently, Filter.frequently_lt_of_liminf_lt, integral_sub_left_eq_self, HasCompactSupport.contDiff_convolution_right, Orthonormal.exists_orthonormalBasis_extension_of_card_eq, ContDiffBump(.contDiff/.support_eq/.tsupport_eq), VitaliFamily.ae_tendsto_average_norm_sub, IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub, Measure.integral_comp_inv_smul, ContDiff.lipschitzWith_of_hasCompactSupport, Continuous.matrix_det, Module.Basis.det: reachable; ContDiffBump.normed, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, MultilinearMap.continuous_of_finiteDimensional: not reachable, avoided)`
- `lake env lean /tmp/w1-decomp/T3.lean, T4.lean, T5.lean, T6.lean (pL from EuclideanSpace.equiv and innerSL with pL x i = inner ℝ (v i) x by simp; ξ_v := ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ v; dy from (EuclideanSpace.basisFun _ ℝ).toBasis.det made continuous by Continuous.matrix_det; boundaryMassOn Y W = Y.boundary.massOn W by rfl at degree d+1; (S − T) ω = S ω − T ω by rfl; S − 0 = S; massOn univ = massOn U; covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α; IsUnifLocDoublingMeasure (volume : Measure (Euclid n)) synthesizes)`
- `lake env lean /tmp/w1-decomp/Final.lean (the 12 exact child types elaborate, only sorry warnings) and /tmp/w1-decomp/Asm.lean (parent assembly skeleton applying every child to the parent's data and concluding 1 ≤ α i₀; elaborates with routine glue left as sorry); python3 -I validate_lean_statement from verifier/lean_contract.py on all 12 types (pass)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py check_source_delta (one appended theorem, no helper declarations, no set_option), runtime.py _decompose, _existing_lean_name_problem, _solve_children and _install_parent_supplied_child_handoff (an accepted declaration with identical frozen type may be reused; accepted children return early), parent_verification.py, prompts.py DECOMPOSE/DECOMPOSITION_AUDIT`
- `git -C /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07 show 16144a475b (accepted proof of Submission.regcomp_covector_sq_sum_orthonormalBasis); sed of its parent-supplied-natural-proof.md`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-951a399d2e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-951a399d2e/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-951a399d2e/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-covec-c35871b74d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/parent_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/w1-decomp/Final.lean`
- `/tmp/w1-decomp/Asm.lean`
- `/tmp/w1-decomp/T4.lean`
- `/tmp/w1-decomp/T5.lean`
- `/tmp/w1-decomp/T6.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c). No declaration with the prefix cbr_ci_pw exists in the DAG, so the 11 new names are fresh; regcomp_covector_sq_sum_orthonormalBasis is comparator-accepted with exactly the reused frozen type. Every library lemma cited in the child proofs is reachable from import GMT.Ch07.Submission (checked with #check); the unreachable normed-bump/convolution-a.e. and finite-dimensional multilinear continuity lemmas are avoided (normalised bumps are built from ContDiffBump, Lebesgue points from IsUnifLocDoublingMeasure/VitaliFamily.ae_tendsto_average_norm_sub, dy from Module.Basis.det with Continuous.matrix_det). All 12 child types elaborate in the contract scope and pass the verifier's lexical check, and a Lean skeleton of the parent assembly type-checks against them, so the children interlock with the frozen parent type as described in the rationale.
