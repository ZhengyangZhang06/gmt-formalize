# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_conservation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 9 (test stationarity with X, apply the area formula with J_G = t|γ′|, and separate variables with a positive radial weight). Conventions: J := (r₀ − s, r₀ + s), I := (−s, s), R := J ×ˢ I ⊆ ℝ × ℝ with volume (= volume.prod volume); S := image of R under q ↦ q.1·γ(q.2); κ(α) := (⟨γ(α),u⟩² + ⟨γ(α),e⟩²)/‖γ′(α)‖; g′ := deriv g.
1. Fix φ : ℝ → ℝ, C¹, with compact support and tsupport φ ⊆ I.
2. (Radial weight.) Let λ be the ContDiffBump function centred at r₀ with inner radius s/4 and outer radius s/2. Then λ is C^∞ (ContDiffBump.contDiff), 0 ≤ λ ≤ 1 (ContDiffBump.nonneg), λ = 1 on [r₀ − s/4, r₀ + s/4] (ContDiffBump.one_of_mem_closedBall), tsupport λ = closedBall(r₀, s/2) ⊆ J (ContDiffBump.tsupport_eq), and λ has compact support (ContDiffBump.hasCompactSupport).
3. (Test field.) Sibling idtp_ccd_scsp_test_field applied to (P, u, e, r₀, s, N, γ, T, λ, φ) (its hypotheses are among ours together with step 2) gives X : ℝ^P → ℝ^P, C¹ with compact support and tsupport X ⊆ N, such that h(x) := tr(P_{T(x)} ∘ DX(x)) satisfies h(tγ(α)) = λ(t)·φ′(α)·(⟨γ(α),u⟩² + ⟨γ(α),e⟩²)/‖γ′(α)‖² for t ∈ J, α ∈ I. By the stationarity hypothesis, ∫_S h dμHE[2] = 0.
4. (Curve facts.) By sibling idtp_ccd_scsp_angle_curve, ⟨γ(α), γ′(α)⟩ = 0 and γ′(α) ≠ 0 for α ∈ I. γ is injective on I: if γ(α) = γ(α′) with α, α′ ∈ I, then α = arctan(⟨γ(α),e⟩/⟨γ(α),u⟩) = arctan(⟨γ(α′),e⟩/⟨γ(α′),u⟩) = α′.
5. (Area formula.) Sibling idtp_ccd_scsp_cone_area applied to (P, r₀, s, γ, h) (hypotheses: 0 < s < r₀, γ C¹ on I, γ injective on I, and ‖γ‖ = 1, ⟨γ, γ′⟩ = 0, γ′ ≠ 0 on I) gives ∫_S h dμHE[2] = ∫_R t‖γ′(α)‖·h(tγ(α)) d(t, α). Hence the latter integral is 0.
6. (Separation of variables.) For (t, α) ∈ R, step 3 and γ′(α) ≠ 0 give t‖γ′(α)‖·h(tγ(α)) = (t·λ(t))·(φ′(α)·κ(α)). By setIntegral_congr_fun on the measurable set R, ∫_R (t·λ(t))·(φ′(α)κ(α)) d(t, α) = 0. Since volume on ℝ × ℝ is volume.prod volume (Measure.volume_eq_prod) and its restriction to J ×ˢ I is (volume.restrict J).prod (volume.restrict I) (Measure.prod_restrict), integral_prod_mul (which needs no integrability hypothesis) gives 0 = (∫_J t·λ(t) dt)·(∫_I φ′(α)κ(α) dα).
7. (Positivity of the radial factor.) t ↦ t·λ(t) is continuous, nonnegative on J (t > r₀ − s > 0 and λ ≥ 0), integrable on J (continuous on the compact interval [r₀ − s, r₀ + s]), and its support contains (r₀ − s/4, r₀ + s/4), where it equals t > 0; this interval has positive length. Hence ∫_J t·λ(t) dt > 0 (setIntegral_pos_iff_support_of_nonneg_ae).
8. (Conclusion.) By steps 6–7, ∫_I φ′(α)κ(α) dα = 0. φ′ vanishes outside tsupport φ ⊆ I (support_deriv_subset), so φ′κ vanishes outside I and ∫_ℝ φ′κ = ∫_I φ′κ (setIntegral_eq_integral_of_forall_compl_eq_zero). Therefore ∫_ℝ φ′(α)κ(α) dα = 0. ∎

## Key steps

1. Fix φ and a radial bump λ (ContDiffBump at r₀ with radii s/4, s/2) whose tsupport lies in (r₀ − s, r₀ + s).
2. Sibling test_field gives an admissible X with tr(P_T∘DX) = λ(t)φ′(α)q/‖γ′‖² on the cone; stationarity makes its integral over S vanish.
3. Sibling cone_area (γ is injective by the angle relation; angle_curve facts) turns ∫_S into ∫_R t‖γ′‖·(integrand) = ∫_R (tλ(t))(φ′κ).
4. integral_prod_mul factors this as (∫ tλ)(∫ φ′κ); the first factor is positive, so ∫_I φ′κ = 0 and hence ∫_ℝ φ′κ = 0.

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
