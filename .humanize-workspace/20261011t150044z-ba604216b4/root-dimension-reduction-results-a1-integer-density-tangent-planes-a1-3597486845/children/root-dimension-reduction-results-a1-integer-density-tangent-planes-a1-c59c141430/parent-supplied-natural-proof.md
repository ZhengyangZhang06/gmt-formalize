# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.minimizing_stationary-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 9, first sentence (Simon 7.1.2 with U = N = ℝ^P).
1. (Case n ≤ P.) Write P = n + k₀. Apply the root result minimizing_implies_stationary (`Submission.minimizing_implies_stationary : MinimizingImpliesStationary`) with n, k := k₀, ℓ := k₀ (ℓ ≤ k), U := univ and N := univ. Its hypotheses hold: univ is open; univ is an embedded C² (n + k₀)-dimensional submanifold of ℝ^{n+k₀} (IsEmbeddedSubmanifold 2 (n + k₀) univ: at every point take V := univ ⊆ Euclid (n + k₀), W := univ and ψ := id, which is smooth, injective, satisfies ψ(V) = W ∩ univ, is proper and has injective derivative); (closure univ ∖ univ) ∩ univ = ∅; spt C ⊆ univ; IsMinimizingIn C (univ ∩ univ), which is the hypothesis after rewriting univ ∩ univ = univ; BoundaryVanishes C; and R represents C. Hence R.IsStationaryAlong univ. Now let X be C¹ with compact support. Then tsupport X ⊆ univ, and X(x) ∈ tangentSpace univ x for every x: the curve c(t) := x + t·X(x) is C¹, maps (−1, 1) into univ, and has c(0) = x and c'(0) = X(x). By the definition of IsStationaryAlong, R.firstVariation X = 0.
2. (Case P < n.) For every j ∈ ℕ, Mathlib's `Measure.euclideanHausdorffMeasure_zero_or_top` (P < n) gives μHE[n](B_j(0)) = 0 or μHE[P](B_j(0)) = ∞; the latter is impossible since μHE[P] = volume on Euclid P (`EuclideanSpace.euclideanHausdorffMeasure_eq_volume P`) and balls have finite volume. As ℝ^P = ⋃_j B_j(0), μHE[n] = 0 on Euclid P. Hence μHE[n]⌞R.carrier = 0 and R.firstVariation X = ∫_{R.carrier} R.mult·tangentialDivergence n R.carrier X dμHE[n] = 0. ∎

## Key steps

1. If n ≤ P, write P = n + k₀ and apply minimizing_implies_stationary with U = N = ℝ^P (identity chart) to get R.IsStationaryAlong univ.
2. Every vector is tangent to ℝ^P (straight-line curves), so every C¹ compactly supported X is admissible and R.firstVariation X = 0.
3. If P < n, μHE[n] vanishes on ℝ^P (Hausdorff dimension), so the first-variation integral is 0.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `python3 -I scans of dag.json (lean_name, lean_statement, status): lemmas mentioning regularSet; IsConeCurrent together with support; IsStationaryAlong or firstVariation together with IsMinimizingIn; HasApproximateTangentSpaceAt together with IsEmbeddedSubmanifold or ContDiff; names matching support_null|density_zero|vanish|null_off; restrictDomain together with boundary; subspace ball measure; statuses of the 29 cited lemma names`
- `grep -n 'def restrictDomain|def VanishesOn|def zeroRegion|def support|def IsTestForm|def testFormOnSubmodule|def GeometricCurrentOn.boundary|def WeaklyConvergesOn|abbrev Covector' simongmt Chapter06/{CurrentLocalEquality,Currents,Forms}.lean`
- `grep -n 'def HasApproximateTangentSpaceAt|HasApproximateTangentSpaceAt.unique|def CountablyRectifiable' simongmt Chapter03/Rectifiable.lean`
- `grep -n 'theorem integral_area_formula_of_injective_derivative|def areaJacobianAt|areaJacobianAt_eq_sqrt_det_gram|theorem ae_eq_const_of_weak_coordinate_derivatives_zero' simongmt Chapter02/{WeightedArea,Area,AreaParametrization}.lean Chapter08/DistributionalConstancy.lean`
- `grep -rn 'euclideanHausdorffMeasure' mathlib Geometry/Euclidean/Volume/Measure.lean (zero_or_top, eq_volume, Isometry.euclideanHausdorffMeasure_image); grep -n 'addHaar_ball_of_pos|addHaar_ball ' mathlib MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `grep -c idtp_ccd dag.json; grep -rl idtp_ccd run nodes/*.json|*.md and .swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean (no match); grep -n 'Whi82' book/chapter-07.txt, book/simon-gmt.txt; sed -n 490,515p book/chapter-07.txt`
- `lake env lean /tmp/ccdp_check/Children.lean (7 child types elaborate); lake env lean /tmp/ccdp_check/Assembly.lean (#print axioms assembly_check: propext, Classical.choice, Quot.sound); lake env lean /tmp/ccdp_check/FromJson.lean (frozen child types as Submission.* stubs plus accepted-lemma stubs prove the parent type, exit 0)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3597486845/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3597486845/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3597486845/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/ccdp_check/Children.lean`
- `/tmp/ccdp_check/Assembly.lean`
- `/tmp/ccdp_check/FromJson.lean`

Pins match the manifest. The snapshot project commit equals workspace HEAD, b4d606d. Mathlib is 25730c7c and SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Accepted DAG lemmas used by the children, all with status `accepted`: rsd_constant_multiplicity_reduction, rsd_ae_hasMassDensity_mult, rsd_mem_support_iff_measure_ball_pos, rsd_massOn_eq_measure, rsd_cmr_support_eq_inter, imrep_carrier_sdiff_support_null, regcomp_atl_local_density_zero, approxTangent_le_submanifold_tangentSpace, dtc_approxTangent_of_null_diff, chart_tangentSpace_eq_range_fderiv, dsmc_chart_inverse_continuity, dimred_rpd_submanifold_density_one, imsupp_unit_orientation_ne_zero_norm_le_one, cone_current_imrep_measure_smul_image, dtc_restrictDomain_isIntegerMultiplicity, dtc_massOn_eq_of_agreeOn, dimred_cs_mi_hasMassDensity_unique, dimred_regular_point_density.

Non-accepted results used, all ancestor or parent prerequisites as in the supplied proof:
- density_one_implies_regular (speculative-ready)
- minimizing_implies_stationary (speculative-ready)
- idtp_planar_cycle_eq_const_mul (planar_constancy, this node's prerequisite)

No accepted lemma already states any child. In particular:
- No accepted lemma states cone-support dilation invariance or the regular-point support identity.
- No accepted lemma gives existence of approximate tangent planes for C¹ submanifolds. This is why sheet_first_variation uses the density argument plus approxTangent_le_submanifold_tangentSpace.
- The decomposing node codim1_density_one_regular_local_rep covers only density 1 and is not accepted.

SimonGMT supplies the area formula integral_area_formula_of_injective_derivative (areaJacobianAt = normDet; areaJacobianAt_eq_sqrt_det_gram is in AreaParametrization.lean) and ae_eq_const_of_weak_coordinate_derivatives_zero, which takes C¹ test functions. These modules are outside the base import closure, so only proofs, never the frozen statements, use them; other worktrees already add these imports. The SimonGMT definitions of support, zeroRegion and test forms (ContDiff ∞ with compact support) match the arguments in the proofs.

Mathlib supplies euclideanHausdorffMeasure_zero_or_top, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.euclideanHausdorffMeasure_image and addHaar_ball_of_pos.

The proposed names idtp_ccd_* are unreserved: there is no match in dag.json, the run nodes, or any worktree Submission.

Lean check: all 7 child types elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07. The hypothesis-only assembly proves the frozen parent type with axioms propext, Classical.choice and Quot.sound.
