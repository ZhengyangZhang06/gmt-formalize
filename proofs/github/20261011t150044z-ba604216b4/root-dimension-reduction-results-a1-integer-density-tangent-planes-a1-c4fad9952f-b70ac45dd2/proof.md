# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.arc_planarity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 11 (Cauchy–Schwarz with |Aγ| = |πγ| and Bessel's inequality force |πγ| = 1; then the polar form). Notation: ⟨·,·⟩ real inner product; γ′(α) := deriv γ α.
1. Fix α ∈ (−s, s); put x := ⟨γ(α), u⟩ > 0, y := ⟨γ(α), e⟩ and q := x² + y² > 0. By sibling idtp_ccd_scsp_angle_curve, x⟨γ′(α), e⟩ − y⟨γ′(α), u⟩ = q.
2. Let w := x·e − y·u. Then ⟨w, γ′(α)⟩ = x⟨e, γ′(α)⟩ − y⟨u, γ′(α)⟩ = q, and ‖w‖² = x²‖e‖² − 2xy⟨e,u⟩ + y²‖u‖² = q (orthonormality; norm_sub_sq_real).
3. (Cauchy–Schwarz.) Using the hypothesis ‖γ′(α)‖ = q: q = ⟨w, γ′(α)⟩ ≤ ‖w‖·‖γ′(α)‖ = ‖w‖·q (real_inner_le_norm), so ‖w‖ ≥ 1 because q > 0, and hence q = ‖w‖² ≥ 1.
4. (Bessel.) ‖γ(α) − (x·u + y·e)‖² = ‖γ(α)‖² − 2⟨γ(α), x·u + y·e⟩ + ‖x·u + y·e‖² = 1 − 2(x² + y²) + (x² + y²) = 1 − q, using ‖γ(α)‖ = 1 and orthonormality (norm_sub_sq_real, norm_add_sq_real). The left-hand side is ≥ 0, so q ≤ 1. Hence q = 1, the left-hand side is 0, and γ(α) = x·u + y·e.
5. (Polar form.) Since x > 0 and x² + y² = 1, 1 + (y/x)² = (1/x)² and √(1 + (y/x)²) = 1/x. By hypothesis α = arctan(y/x), so cos α = 1/√(1 + (y/x)²) = x (Real.cos_arctan) and sin α = (y/x)/√(1 + (y/x)²) = y (Real.sin_arctan). Therefore γ(α) = cos α·u + sin α·e. ∎

## Key steps

1. With x = ⟨γ,u⟩ > 0, y = ⟨γ,e⟩, q = x² + y² and w = x·e − y·u, sibling angle_curve gives ⟨w, γ′⟩ = q, and orthonormality gives ‖w‖² = q.
2. Cauchy–Schwarz with ‖γ′‖ = q gives ‖w‖ ≥ 1, so q ≥ 1; Bessel gives ‖γ − (x·u + y·e)‖² = 1 − q ≥ 0, so q = 1 and γ = x·u + y·e.
3. x = cos(arctan(y/x)) = cos α and y = sin α by Real.cos_arctan and Real.sin_arctan.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `grep -n 'IsEmbeddedSubmanifold\|def tangentSpace\|tangentSpace' GMT/Ch07/Contract.lean; sed -n 200,300p GMT/Ch07/Contract.lean`
- `python3 -I scans of dag.json lean_statement for: arctan | deriv φ | Ioo with deriv and ∃ c | μHE[2] | areaJacobian | LinearMap.trace | starProjection | tangentSpace | cutoff (= 1 with IsCompact K and HasCompactSupport); lean_name lookups chart_tangentSpace_eq_range_fderiv, dsmc_chart_inverse_continuity, dsmc_chart_tangentSpace_eq_range, dsmc_chart_range_subset_tangentSpace, fvmb_trace_starProjection_comp_eq_sum_inner, dgcr_bwd_normal_cutoff, dgce_left_inverse_tangentSpace_eq_range, doragm_sab_cutoff_profile`
- `grep -c idtp_ccd_scsp dag.json; grep -rl idtp_ccd_scsp runs/.../nodes; grep -l idtp_ccd_scsp ../.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean (all no match, also for each of the 10 proposed names)`
- `grep -rn 'toOpenPartialHomeomorph|exists_contDiff_support_eq_eq_one_iff|exists_contDiff_tsupport_subset|IsCompact.exists_cthickening_subset_open|ContinuousLinearEquiv.isOpen|OpenPartialHomeomorph.hasFDerivAt_symm|restrOpen|symm_image_target_eq_source|volume_preserving_finTwoArrow|EuclideanSpace.volume_preserving_|euclideanHausdorffMeasure_eq_volume|LinearMap.finrank_range_of_inj|IsPreconnected.subset_of_closure_inter_subset|Filter.EventuallyEq.fderiv_eq|ContDiffOn.continuousOn_fderiv_of_isOpen|setIntegral_eq_integral_of_forall_compl_eq_zero|integral_hasDerivAt_right|contDiff_one_iff_deriv|hasDerivAt_arctan|contDiffAt_norm|LinearIndependent.pair_iff' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -n 'theorem integral_area_formula_of_injective_derivative|def areaJacobianAt|areaJacobianAt_eq_normDet|areaJacobianAt_eq_sqrt_det_gram|normDet_sq_eq_det_gram|theorem ae_eq_const_of_weak_coordinate_derivatives_zero|def WeakDerivativesZero' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/{WeightedArea,Area,AreaParametrization,AreaCurve}.lean .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `lake env lean /tmp/scsp_check/Probe.lean; Children.lean; Assembly.lean (#print axioms); Conservation.lean; Planarity.lean; Imports.lean; Names.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3876084c61/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3876084c61/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Connected/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/ArctanDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaParametrization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/tmp/scsp_check/Children.lean`
- `/tmp/scsp_check/Assembly.lean`
- `/tmp/scsp_check/Conservation.lean`
- `/tmp/scsp_check/Planarity.lean`
- `/tmp/scsp_check/Imports.lean`
- `/tmp/scsp_check/Names.lean`

Pins match. The snapshot project_commit b4d606d equals workspace HEAD, mathlib 25730c7c equals .lake/packages/mathlib HEAD, and SimonGMT is at the lakefile pin 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

The child proofs use three accepted DAG lemmas (status accepted): chart_tangentSpace_eq_range_fderiv, dsmc_chart_inverse_continuity and fvmb_trace_starProjection_comp_eq_sum_inner.

No accepted DAG lemma states any child: no DAG statement mentions arctan, and there is no 1-D weak-derivative constancy lemma, cone area formula, or submanifold local-inverse lemma. The idtp_ccd_scsp_* names have no match in dag.json, in the run nodes, or in any worktree Submission.lean.

Pinned Mathlib supplies the lemmas the proofs cite, including:
- inverse function theorem: ContDiffAt.toOpenPartialHomeomorph; OpenPartialHomeomorph.restrOpen, contDiffAt_symm and hasFDerivAt_symm
- cutoffs: ContinuousLinearEquiv.isOpen, exists_contDiff_support_eq_eq_one_iff (reachable from the frozen imports), IsCompact.exists_cthickening_subset_open
- volume transport: EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, volume_preserving_finTwoArrow, InnerProductSpace.euclideanHausdorffMeasure_eq_volume
- integrals: integral_prod_mul, setIntegral_indicator, support_fderiv_subset
- trigonometry: Real.cos_arctan, Real.sin_arctan

These names do not exist and are not cited: HasFDerivAt.norm, EuclideanSpace.measurableEquiv, unprimed setIntegral_congr, and ContDiffBump.normed (unavailable without an extra import).

SimonGMT supplies integral_area_formula_of_injective_derivative (WeightedArea.lean), areaJacobianAt_eq_normDet with LinearMap.normDet_sq_eq_det_gram (or areaJacobianAt_eq_sqrt_det_gram), and ae_eq_const_of_weak_coordinate_derivatives_zero. Using them requires proof-only imports, which load together with GMT.Ch07.Submission.

Lean checks:
- All 10 child types elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07.
- The parent's exact frozen type is proved from the 10 Submission.* stubs, with axioms propext, Classical.choice and Quot.sound, plus sorryAx only from the stubs.
- cone_conservation is proved from the test_field, cone_area and angle_curve stubs.
- arc_planarity is proved from the angle_curve stub.
