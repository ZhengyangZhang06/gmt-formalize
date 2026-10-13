# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.test_field-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 7–8 (the test field X = ψ₀(f)λ(|x|)ζ·Ax and the computation of its tangential divergence), stated for the cone over γ; φ plays the role of ψ₀. Conventions: J := (r₀ − s, r₀ + s), I := (−s, s); ⟨·,·⟩ real inner product; Ax := ⟨x,u⟩e − ⟨x,e⟩u (a continuous linear map); f(x) := arctan(⟨x,e⟩/⟨x,u⟩); q(x) := ⟨x,u⟩² + ⟨x,e⟩²; Ω := {x : ⟨x,u⟩ > 0} (open, N ⊆ Ω, 0 ∉ Ω); g′ := deriv g, Dg := fderiv ℝ g.
1. (Calculus facts.) ⟨Ax, y⟩ = ⟨x,u⟩⟨e,y⟩ − ⟨x,e⟩⟨u,y⟩; in particular ⟨Ax, x⟩ = 0 for all x. f is C^∞ on Ω (x ↦ ⟨x,e⟩/⟨x,u⟩ is a quotient of continuous linear functions with nonvanishing denominator on Ω, and arctan is smooth, Real.contDiff_arctan), and for x ∈ Ω, by Real.hasDerivAt_arctan and the quotient rule, Df(x)h = (⟨h,e⟩⟨x,u⟩ − ⟨x,e⟩⟨h,u⟩)/q(x) = ⟨Ax, h⟩/q(x), where q(x) ≥ ⟨x,u⟩² > 0. The norm is C^∞ on Euclid P ∖ {0} ⊇ Ω (contDiffAt_norm) with derivative h ↦ ⟨x, h⟩/‖x‖ at x ≠ 0 (e.g. from (hasFDerivAt_id x).norm_sq, HasFDerivAt.sqrt and Real.sqrt_sq). For t ∈ J and α ∈ I: t > r₀ − s > 0, ‖tγ(α)‖ = t, ⟨tγ(α), u⟩ > 0, f(tγ(α)) = arctan(t⟨γ(α),e⟩/(t⟨γ(α),u⟩)) = α, and q(tγ(α)) = t²q(γ(α)).
2. (Curve facts.) By sibling idtp_ccd_scsp_angle_curve (P, u, e, s, γ), for α ∈ I: ⟨γ(α), γ′(α)⟩ = 0, γ′(α) ≠ 0, and ⟨γ(α),u⟩⟨γ′(α),e⟩ − ⟨γ(α),e⟩⟨γ′(α),u⟩ = q(γ(α)); the left-hand side equals ⟨Aγ(α), γ′(α)⟩. Put τ(α) := ‖γ′(α)‖⁻¹γ′(α). Then (γ(α), τ(α)) is orthonormal, span{γ(α), τ(α)} = span{γ(α), γ′(α)}, and ⟨Aγ(α), τ(α)⟩ = q(γ(α))/‖γ′(α)‖.
3. (Compact set and cutoff.) K₀ := {tγ(α) : t ∈ tsupport λ, α ∈ tsupport φ} is the image of the compact set tsupport λ ×ˢ tsupport φ ⊆ J ×ˢ I under (t, α) ↦ tγ(α), which is continuous on J ×ˢ I (IsCompact.image_of_continuousOn); so K₀ is compact, and K₀ ⊆ N by hypothesis. By IsCompact.exists_cthickening_subset_open choose ε > 0 with cthickening (3ε) K₀ ⊆ N. Apply exists_contDiff_support_eq_eq_one_iff (available from the frozen imports) to the open set thickening (2ε) K₀ and the closed set cthickening ε K₀ ⊆ thickening (2ε) K₀: there is ζ : Euclid P → ℝ, C^∞, with values in [0, 1], support ζ = thickening (2ε) K₀, and ζ(x) = 1 exactly for x ∈ cthickening ε K₀. Then ζ ≡ 1 on the open neighbourhood V := thickening ε K₀ of K₀, so Dζ = 0 on V; tsupport ζ ⊆ cthickening (2ε) K₀ ⊆ N, a closed bounded (hence compact) set, so ζ has compact support. (If K₀ = ∅ one may take ζ := 0.)
4. (The field.) Let g(x) := φ(f(x))·λ(‖x‖)·ζ(x) and X(x) := g(x)·Ax. On the open set N ⊆ Ω every factor is C¹ (φ, λ are C¹; f, ‖·‖, ζ are C^∞ there), so g is C¹ on N; g vanishes on the open set (tsupport ζ)ᶜ; as tsupport ζ ⊆ N these two open sets cover Euclid P, so g is C¹ at every point, i.e. ContDiff ℝ 1 g. Hence X is C¹ (product of g with the continuous linear map A). support X ⊆ support ζ, so tsupport X ⊆ tsupport ζ ⊆ N, and X has compact support (HasCompactSupport.mono). For every x, DX(x)h = (Dg(x)h)·Ax + g(x)·Ah.
5. (Trace in an orthonormal frame.) Fix t ∈ J, α ∈ I and write x := tγ(α), γ₀ := γ(α), τ₀ := τ(α), T₀ := T(x) = span{γ₀, γ′(α)} = span(range ![γ₀, τ₀]). By the accepted lemma Submission.fvmb_trace_starProjection_comp_eq_sum_inner (n := 2, the orthonormal family ![γ₀, τ₀], Q := T₀, B := DX(x)), tr(P_{T₀} ∘ DX(x)) = ⟨γ₀, DX(x)γ₀⟩ + ⟨τ₀, DX(x)τ₀⟩. Now ⟨γ₀, DX(x)γ₀⟩ = (Dg(x)γ₀)⟨γ₀, Ax⟩ + g(x)⟨γ₀, Aγ₀⟩ = 0, because ⟨γ₀, Ax⟩ = t⟨Aγ₀, γ₀⟩ = 0 and ⟨γ₀, Aγ₀⟩ = 0; and ⟨τ₀, DX(x)τ₀⟩ = (Dg(x)τ₀)⟨τ₀, Ax⟩ + g(x)⟨τ₀, Aτ₀⟩ = (Dg(x)τ₀)⟨τ₀, Ax⟩, where ⟨τ₀, Ax⟩ = t⟨Aγ₀, τ₀⟩ = t·q(γ₀)/‖γ′(α)‖. Hence tr(P_{T₀} ∘ DX(x)) = (Dg(x)τ₀)·t·q(γ₀)/‖γ′(α)‖.
6. (Value of Dg(x)τ₀.) (i) If t ∉ tsupport λ, then λ = 0 on a neighbourhood of t; since ‖·‖ is continuous with ‖x‖ = t, g = 0 on a neighbourhood of x, so DX(x) = 0 and the trace is 0; also λ(t) = 0, so the claimed value is 0. (ii) If α ∉ tsupport φ, then φ = 0 on a neighbourhood of α, hence φ′(α) = 0; since f is continuous at x ∈ Ω with f(x) = α, g = 0 on a neighbourhood of x, so the trace is 0, equal to the claimed value. (iii) Otherwise t ∈ tsupport λ and α ∈ tsupport φ, so x ∈ K₀ ⊆ V and ζ ≡ 1 near x; therefore g(y) = φ(f(y))·λ(‖y‖) near x and Dg(x)h = φ′(α)λ(t)·Df(x)h + φ(α)λ′(t)·⟨x, h⟩/‖x‖ = λ(t)φ′(α)⟨Ax, h⟩/q(x) + φ(α)λ′(t)⟨γ₀, h⟩. For h = τ₀: ⟨γ₀, τ₀⟩ = 0, ⟨Ax, τ₀⟩ = t·q(γ₀)/‖γ′(α)‖ and q(x) = t²q(γ₀), so Dg(x)τ₀ = λ(t)φ′(α)/(t‖γ′(α)‖), and the trace equals λ(t)φ′(α)/(t‖γ′(α)‖)·t·q(γ₀)/‖γ′(α)‖ = λ(t)φ′(α)q(γ₀)/‖γ′(α)‖².
7. (Conclusion.) In every case tr(P_{T(tγ(α))} ∘ DX(tγ(α))) = λ(t)·φ′(α)·(⟨γ(α),u⟩² + ⟨γ(α),e⟩²)/‖γ′(α)‖² for all t ∈ J, α ∈ I; and X is C¹ with compact support and tsupport X ⊆ N. ∎

## Key steps

1. K₀ = {tγ(α) : t ∈ tsupport λ, α ∈ tsupport φ} is a compact subset of N; a smooth cutoff ζ ≡ 1 near K₀ has compact support inside N.
2. X := φ(f)·λ(‖x‖)·ζ·Ax with Ax = ⟨x,u⟩e − ⟨x,e⟩u is C¹, compactly supported, tsupport X ⊆ N, and DX = g·A + (Ax)⊗∇g.
3. The accepted fvmb_trace_starProjection_comp_eq_sum_inner in the orthonormal frame (γ, γ′/‖γ′‖) gives tr = (Dg(x)τ)⟨τ, Ax⟩, since A is skew.
4. With sibling angle_curve (⟨Aγ, γ′⟩ = q(γ), γ ⊥ γ′) and Df(x) = ⟨Ax, ·⟩/q(x), the trace is λ(t)φ′(α)q(γ(α))/‖γ′(α)‖²; outside tsupport λ × tsupport φ both sides vanish.

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
