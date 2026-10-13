# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.cone_support_smul-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, preliminary (K) ("spt C is invariant under x ↦ sx, s > 0").
1. Let R ∈ IMRep univ n represent C (IsIntegerMultiplicity C) and μ := R.measure. By the accepted lemma `Submission.rsd_mem_support_iff_measure_ball_pos` (U := ℝ^P open, R represents C), z ∈ spt C ↔ (z ∈ ℝ^P and μ(B_r(z)) > 0 for every r > 0).
2. By the accepted lemma `Submission.cone_current_imrep_measure_smul_image` (C a cone represented by R, λ := t > 0), μ((z ↦ t z)(A)) = ENNReal.ofReal(tⁿ)·μ(A) for every Borel set A.
3. Let x ∈ spt C and r > 0. The homothety z ↦ t z maps B_{r/t}(x) onto B_r(t x) (Mathlib smul_ball: t • B_s(x) = B_{|t| s}(t • x) for t ≠ 0). Hence μ(B_r(t x)) = ENNReal.ofReal(tⁿ)·μ(B_{r/t}(x)), which is > 0 because tⁿ > 0 and μ(B_{r/t}(x)) > 0 (step 1, x ∈ spt C, r/t > 0).
4. By step 1, t x ∈ spt C. ∎

## Key steps

1. spt C = {z : μ_R(B_r(z)) > 0 ∀ r > 0} for a representation R (rsd_mem_support_iff_measure_ball_pos).
2. μ_R(tA) = tⁿμ_R(A) for a cone (cone_current_imrep_measure_smul_image).
3. B_r(tx) = t·B_{r/t}(x), so μ_R(B_r(tx)) = tⁿμ_R(B_{r/t}(x)) > 0 and tx ∈ spt C.

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
