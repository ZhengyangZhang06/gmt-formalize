# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.line_param-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: shared tool for steps 3–6 of the parent proof (H¹ of rays and segments, and "ω_1 = unitBallVolume 1 = 2" used for "μ(B_ρ(y)) = 2mρ = m·ω_1ρ"); Simon 7.3.3, proof of (2), formula (10) (chapter-07.txt lines 563–568). Notation: H¹ := μHE[1], Mathlib's normalized 1-dimensional Hausdorff measure on ℝ^P; γ(t) := p + t·v.
1. (Isometry.) For s, t ∈ ℝ, dist(γ(s), γ(t)) = ‖(s − t)·v‖ = |s − t|·‖v‖ = |s − t|, because ‖v‖ = 1. So γ is an isometry ℝ → ℝ^P (Isometry.of_dist_eq).
2. (Measurable embedding.) An isometry from the complete space ℝ is a closed embedding (Isometry.isClosedEmbedding), and a closed embedding between Borel spaces is a measurable embedding (IsClosedEmbedding.measurableEmbedding). This is the first conjunct of (ii). In particular range γ is closed, hence measurable, and γ is injective.
3. (H¹ = ℒ¹ on ℝ.) ℝ is a real inner product space with finrank ℝ ℝ = 1, so InnerProductSpace.euclideanHausdorffMeasure_eq_volume gives μHE[1] = volume on ℝ.
4. (Push-forward.) For the isometry γ, Isometry.map_euclideanHausdorffMeasure gives Measure.map γ (μHE[1] on ℝ) = H¹⌞range γ; by step 3, Measure.map γ volume = H¹⌞range γ.
5. (Restriction to γ(I).) Let I ⊆ ℝ be any set. Since γ(I) ⊆ range γ and range γ is measurable, H¹⌞γ(I) = (H¹⌞range γ)⌞γ(I) (Measure.restrict_restrict_of_subset). By step 4 this is (Measure.map γ volume)⌞γ(I), and for the measurable embedding γ, (Measure.map γ volume)⌞γ(I) = Measure.map γ (volume⌞γ⁻¹(γ(I))) (MeasurableEmbedding.restrict_map). By injectivity γ⁻¹(γ(I)) = I. Hence H¹⌞γ(I) = Measure.map γ (volume⌞I), the second conjunct of (ii).
6. (Measure of γ(I).) Isometry.euclideanHausdorffMeasure_image gives μHE[1](γ(I)) = μHE[1](I) for every set I ⊆ ℝ; with step 3, H¹(γ(I)) = volume(I), the third conjunct of (ii).
7. (ω₁ = 2.) On Euclid 1, volume = μHE[1] (EuclideanSpace.euclideanHausdorffMeasure_eq_volume with d = 1). Let ε₀ := EuclideanSpace.single 0 1 ∈ Euclid 1. Then ‖ε₀‖ = 1, and every x ∈ Euclid 1 equals (x 0)·ε₀ (Fin 1 has one element), so ‖x‖ = |x 0|. Hence ball(0, 1) = {t·ε₀ : −1 < t < 1} = γ₀((−1, 1)) for γ₀(t) := 0 + t·ε₀. By step 6 applied with P = 1, p = 0, v = ε₀ and I = (−1, 1): unitBallVolume 1 = volume(ball(0, 1)) = μHE[1](γ₀((−1, 1))) = volume((−1, 1)) = 2. This is (i). ∎

## Key steps

1. t ↦ p + t v is an isometry because ‖v‖ = 1, hence a closed and a measurable embedding.
2. μHE[1] = volume on ℝ since finrank ℝ ℝ = 1.
3. Isometry.map_euclideanHausdorffMeasure and MeasurableEmbedding.restrict_map with injectivity give H¹⌞γ(I) = γ_#(ℒ¹⌞I) for every I.
4. Isometry.euclideanHausdorffMeasure_image gives H¹(γ(I)) = ℒ¹(I).
5. The unit ball of ℝ¹ is γ₀((−1, 1)), so ω₁ = 2.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `python3 -I scans of dag.json: status/children/depends_on/speculative_commit of root.dimension_reduction_results-a1.one_dim_cones-a1 and of the siblings under root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1; the 1008 accepted lean_name/lean_statement pairs filtered for unitBallVolume 1, Measure.map (fun t, deriv φ, LocallyIntegrableOn, ∫ t in, Finset (Euclid, IsConeCurrent C →; byte-equality of the reused, monotonicity and parent types; node ids under the selected node`
- `python3 -I reads of nodes/root-dimension-reduction-results-a1-one-dim-cones-a1/decomposition-v1.json, decomposition-audit-v1.json, decomposition-v2.json, speculative-process-v2.log, speculative-prompt-v2.md`
- `git show 75f499358:GMT/Ch07/Submission.lean (speculative draft of the identical theorem); python3 extraction of its Submission.odc_* signatures and helper call graph`
- `grep -n "_machine_leaf|_leaf_author_task|check_source_delta|check_parent_git_delta|_solve_children|_existing_lean_name_problem|_overlay_accepted_children|_wait_for_accepted_dependencies|_submit_speculative_parent" in /runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py, leaf_verification.py, parent_verification.py, inherited.py, store.py`
- `rg -n "Isometry.euclideanHausdorffMeasure_image|Isometry.map_euclideanHausdorffMeasure|euclideanHausdorffMeasure_eq_volume|ae_eq_zero_of_integral_contDiff_smul_eq_zero|measure_null_of_locally_null|integral_Ioi_of_hasDerivAt_of_tendsto|extDeriv_constOfIsEmpty|contDiff_infty_iff_deriv|restrict_map" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n "countablyRectifiable_sUnion|countablyRectifiable_range|blowUpMap|HasApproximateTangentSpaceAt|euclideanHausdorffMeasure_image_le_of_lipschitzOn|zeroRegion|exteriorDerivative_apply|TestFormOnConverges|massAdmissibleOn|le_massOn" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT; rg -n -i constancy /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06 (no match)`
- `grep -c idtp_fons_odc dag.json; grep -rl idtp_fons_odc nodes GMT .lake/packages/simongmt/Poincare; grep -rl --include=*.lean idtp_fons_odc ../.swarm-worktrees (all no match)`
- `grep -n "1-dimensional minimizing cone|Constancy Theorem" book/chapter-07.txt book/chapter-06.txt`
- `lake env lean /tmp/odc_fons_check/TypesJson.lean; lake env lean /tmp/odc_fons_check/Assembly.lean; lake env lean /tmp/odc_fons_check/DraftChecks.lean; lake env lean /tmp/odc_fons_check/DraftChecksAx.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-cc23a75e0c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-one-dim-cones-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-one-dim-cones-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-one-dim-cones-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-one-dim-cones-a1/speculative-process-v2.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1/isolated-comparator-result.json`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/parent_verification.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/odc_fons_check/TypesJson.lean`
- `/tmp/odc_fons_check/Assembly.lean`
- `/tmp/odc_fons_check/DraftChecks.lean`
- `/tmp/odc_fons_check/DraftChecksAx.lean`

Pins match: the snapshot manifest records project b4d606db and Mathlib 25730c7c (workspace HEAD and .lake/packages/mathlib); SimonGMT is 2b366308; the snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. The identically typed node root.dimension_reduction_results-a1.one_dim_cones-a1 (dimred_one_dim_minimizing_cone) is speculative-ready, not accepted, so it cannot be reused; its decomposition-v1 (ten children, all accepted by decomposition-audit-v1) was dropped only for the then node bound 200, and its speculative draft 75f499358 (81 Submission.odc_* helpers) proves this exact type modulo the two prerequisites. runtime.py/leaf_verification.py show that a childless node here is a machine leaf restricted to one theorem without helpers or set_option, so the split is needed; problem.md:471 requires a node per named helper. Reused: dimred_im_mass_measure (accepted, 01ae2c59, isolated comparator passed) and cone_current_imrep_measure_smul_image (accepted, e183b985, isolated comparator passed), byte-identical types. Library: the snapshot Mathlib supplies Isometry.euclideanHausdorffMeasure_image (Geometry/Euclidean/Volume/Measure.lean:131), Isometry.map_euclideanHausdorffMeasure (:141), EuclideanSpace/InnerProductSpace.euclideanHausdorffMeasure_eq_volume (:187, :191), IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (Analysis/Distribution/AEEqOfIntegralContDiff.lean:205), measure_null_of_locally_null (MeasureTheory/OuterMeasure/Basic.lean:150), integral_Ioi_of_hasDerivAt_of_tendsto (MeasureTheory/Integral/IntegralEqImproper.lean:786), extDeriv_constOfIsEmpty (Analysis/Calculus/DifferentialForm/Basic.lean:143), contDiff_infty_iff_deriv (Analysis/Calculus/ContDiff/Deriv.lean:103), Measure.restrict_map (MeasureTheory/Measure/Restrict.lean:332); SimonGMT supplies blowUpMap and HasApproximateTangentSpaceAt (Chapter03/Rectifiable.lean:96, :102), countablyRectifiable_range (:64) and countablyRectifiable_sUnion (:416), euclideanHausdorffMeasure_image_le_of_lipschitzOn (Chapter02/Lipschitz.lean:216), zeroRegion (Chapter06/CurrentLocalEquality.lean:108), exteriorDerivative_apply (Chapter06/Forms.lean:119), TestFormOnConverges and exteriorDerivativeTestOn (Chapter06/Currents.lean:132, :193). No current constancy theorem exists in SimonGMT Chapter06 (only Chapter08 varifold files), and no library or accepted declaration states any of the ten new child statements, so they enter as fresh obligations. Lean: all 12 child types elaborate; the parent type follows from them and the frozen monotonicity type with standard axioms only; the draft derives all ten new child types (sorryAx only via the stub of the accepted dimred_im_mass_measure for antipodal and line_conclusion). No idtp_fons_odc_ name is reserved anywhere.
