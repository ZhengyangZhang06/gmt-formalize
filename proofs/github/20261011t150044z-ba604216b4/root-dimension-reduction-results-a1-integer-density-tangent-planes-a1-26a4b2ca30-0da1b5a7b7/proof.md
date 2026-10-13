# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1.null_image-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1(c) of the parent proof together with its library fact (L1) (Lipschitz images, Simon Ch. 2, 1.8(i); Mathlib/SimonGMT). Notation: E := ℝ^P; H^n := μHE[n] on E and on ℝ^n; L^n := volume on ℝ^n.
1. (Localization.) By the sibling lipschitz_localization (Submission.idtp_caf_lipschitz_localization) applied to Z and F there are open V_l ⊆ Z, Borel pairwise disjoint Z_l ⊆ V_l with ⋃_l Z_l = Z, and maps G_l : E → ℝ^n, G_l being K_l-Lipschitz for some K_l ∈ ℝ≥0, with F = G_l on V_l (l ∈ ℕ).
2. (Splitting S.) Since S ⊆ Z = ⋃_l Z_l, S = ⋃_l (S ∩ Z_l), hence F(S) = ⋃_l F(S ∩ Z_l). As S ∩ Z_l ⊆ Z_l ⊆ V_l and F = G_l on V_l, F(S ∩ Z_l) = G_l(S ∩ Z_l).
3. (Lipschitz images, (L1).) G_l is K_l-Lipschitz on S ∩ Z_l, so H^n(G_l(S ∩ Z_l)) ≤ K_l^n·H^n(S ∩ Z_l) (SimonGMT Chapter02 euclideanHausdorffMeasure_image_le_of_lipschitzOn, valid between any two metric spaces with their Borel σ-algebras; equivalently Mathlib LipschitzOnWith.hausdorffMeasure_image_le for μH[n] and μHE[n] = c_n·μH[n]). Since H^n(S ∩ Z_l) ≤ H^n(S) = 0, we get H^n(G_l(S ∩ Z_l)) = 0, the measure being μHE[n] on ℝ^n.
4. (Conclusion.) On ℝ^n = Euclid n, μHE[n] = L^n (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume), so L^n(F(S ∩ Z_l)) = 0 for every l, and by countable subadditivity (measure_iUnion_null) L^n(F(S)) = 0. ∎

## Key steps

1. Take the localization (V_l, Z_l, G_l) of F from the sibling lipschitz_localization.
2. F(S) = ⋃_l G_l(S ∩ Z_l) since S ⊆ ⋃ Z_l and F = G_l on Z_l ⊆ V_l.
3. Each G_l(S ∩ Z_l) is μHE[n]-null by the Lipschitz image bound H^n(G(X)) ≤ K^n H^n(X).
4. μHE[n] = volume on Euclid n and a countable union of null sets is null.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project; project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); sed -n 1,457p GMT/Ch07/Contract.lean; python3 -I read of the node's parent-child-handoff.json and parent decomposition-v3.json`
- `lake env lean /tmp/caf_probe/Probe.lean (import GMT.Ch07.Submission, contract scope): LinearMap.normDet, Poincare.SimonGMT.Chapter02.areaJacobianAt, Poincare.SimonGMT.Chapter02.weightedAreaFiberSum, LinearMap.euclideanHausdorffMeasure_image unknown; LipschitzOnWith.extend_finite_dimension, ContDiffOn.exists_lipschitzOnWith, Besicovitch.ae_tendsto_measure_inter_div, LipschitzWith.ae_differentiableAt, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Poincare.SimonGMT.Chapter03.blowUpMap, stdOrthonormalBasis, MeasurableSet.image_of_continuousOn_injOn, LipschitzOnWith.hausdorffMeasure_image_le available`
- `grep -n 'theorem weighted_area_formula_lipschitz_fiberSum|theorem aemeasurable_weightedAreaFiberSum_lipschitz|theorem weighted_area_formula_lipschitz_injOn|def areaRegularSet|theorem area_image_compl_regularSet_eq_zero|theorem measurable_areaJacobianAt|theorem weightedAreaFiberSum_iUnion|def weightedAreaFiberSum|def areaJacobianAt|theorem HasApproximateTangentSpaceAt.unique|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn|theorem simon_theorem_3_6|def dimensionalUpperDensity|theorem measure_toOuterMeasure_isBorelRegular|simonAreaNormalization' -r /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT`
- `grep -rn 'theorem normDet_comp|theorem normDet_sq_eq_det_gram|theorem euclideanHausdorffMeasure_image|theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|theorem lintegral_sum_measure|theorem restrict_iUnion|theorem lintegral_tsum|protected theorem tsum_sigma.|def unionEqSigmaOfDisjoint|theorem restrict_congr_set|theorem restrict_apply.|theorem ae_restrict_iff.|theorem ae_restrict_of_ae_restrict_of_subset|theorem ContDiffOn.contDiffAt|theorem ContDiffAt.differentiableAt|def gram|theorem isOpen_iUnion_countable|theorem countable_cover_nhdsWithin' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `python3 -I scans of /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json (720 nodes): accepted nodes (status accepted, candidate_commit set) whose lean_statement mentions HasApproximateTangentSpaceAt, approxTangentPlane, LipschitzWith/LipschitzOnWith, ContDiffOn, volume-null images or fibre tsums; statuses of dpf_rectifiable_bilipschitz_pieces, doraggt_ae_approxTangent_transfer, ptd_piece_image_measurable_ae_pullback, dpf_itt_approxTangentPlane_eq (accepted), dpf_approxTangent_ae_bilipschitz_piece (speculative-ready), ptd_piece_image_approxTangent_ae (waiting-children), pit_* (decomposing), dimred_rpd_bilipschitz_image_measure, doraggt_ae_rescaled_lebesgue_point, dorwbl_diff_quotient_tendstoUniformlyOn (accepted)`
- `cat nodes/*/parent-supplied-natural-proof.md of the four reused nodes and of doraggt_local_density_zero, doraggt_approxTangent_iff_of_density_zero; git show a2ba78f:GMT/Ch07/Submission.lean (imports, accepted declaration)`
- `grep -c idtp_caf_ dag.json DAG.md dag.mmd issue-workers.json; grep -rl idtp_caf_ nodes/; git for-each-ref (3388 refs) | xargs git grep -l idtp_caf_ -- GMT (all no match)`
- `sed -n on /runtime/flows/gmt-claude-ebe9113f52d5/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, child id mapping by lean name, _install_parent_supplied_child_handoff early return for accepted nodes, accepted-child overlay of depends_on) and store.py ensure; verifier/gmt-compare.py child_modules and contract_scope`
- `python3 -I /tmp/caf_scripts/assemble.py (verifier/lean_contract.py validate_lean_statement on all 10 child statements)`
- `lake env lean /tmp/caf_dec/Stmts.lean (10 stubs elaborate); lake env lean /tmp/caf_dec/Assembly.lean (#print axioms caf_parent_check, caf_Dprime_check: propext, sorryAx, Classical.choice, Quot.sound)`
- `independent reviewer subagent: /tmp/caf_review/Check.lean and CheckAx.lean (child stubs as named axioms; per-theorem axiom dependencies)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3c1713cbf6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-4344c8c0d8/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-6e2110e6b7/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-cda4d660ba/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-c5809c1d90/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-e483a373f0/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-tan-cd2837f661/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Lattice/Disjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-ebe9113f52d5/_recursive_lean/runtime.py`
- `/tmp/caf_dec/Assembly.lean`
- `/tmp/caf_dec/subproblems.json`

Pins match. The snapshot manifest has project b4d606d (the workspace HEAD) and mathlib 25730c7c. Contract.lean and Submission.lean are byte-identical.

Library support.
- SimonGMT provides the Euclidean-domain Lipschitz area formulas: weighted_area_formula_lipschitz_fiberSum, aemeasurable_weightedAreaFiberSum_lipschitz, and weighted_area_formula_lipschitz_injOn with arbitrary weights.
- SimonGMT also provides areaRegularSet with its null-image lemma, measurable_areaJacobianAt, euclideanHausdorffMeasure_image_le_of_lipschitzOn, HasApproximateTangentSpaceAt.unique, simon_theorem_3_6 and measure_toOuterMeasure_isBorelRegular.
- Mathlib provides normDet_comp, normDet_sq_eq_det_gram, euclideanHausdorffMeasure_image_eq_normDet_mul_volume, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, Besicovitch density, Lebesgue differentiation, Lipschitz extension, ContDiffOn.exists_lipschitzOnWith, restrict_iUnion and lintegral_sum_measure (no measurability needed).

Statement scope. normDet, areaJacobianAt and weightedAreaFiberSum are not in the contract's import closure. The child statements therefore use the parent's Gram-determinant and subtype-tsum forms; child proofs may add imports, as accepted candidates already do.

Reuse.
- Four exactly matching declarations are comparator-accepted and are reused with byte-identical types: dpf_rectifiable_bilipschitz_pieces, doraggt_ae_approxTangent_transfer, ptd_piece_image_measurable_ae_pullback and dpf_itt_approxTangentPlane_eq.
- The runtime maps these to the existing nodes and overlays their candidate commits for dependents.
- The related unaccepted nodes ptd_piece_image_approxTangent_ae, dpf_approxTangent_ae_bilipschitz_piece and pit_* cannot be shared, so fresh idtp_caf_* names are used. These names are unused everywhere.

Lean checks.
- All 10 child types elaborate in the contract scope.
- The assembly proves the exact frozen parent type from the 10 child stubs. Its axioms are propext, Classical.choice and Quot.sound, plus sorryAx from the stubs only.
- The step-3 glue child follows from its four siblings.
