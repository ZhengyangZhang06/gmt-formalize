# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_chart-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 1–6 (chart, p ∈ Q, coordinates u, e, f, F, inverse function theorem, relative openness, radial structure), with p := r₀u. Conventions: B_r(x) := ball x r; ⟨·,·⟩ real inner product; p := r₀u; Q := span(tangentSpace M p); J := (r₀ − s, r₀ + s), I := (−s, s); g′ := deriv g, Dg := fderiv ℝ g; for t, α ∈ ℝ, ⟨⟨t, α⟩⟩ denotes the point of Euclid 2 with coordinates (t, α) (Lean: !₂[t, α]). Note ⟨p, u⟩ = r₀‖u‖² = r₀ and ‖p‖ = r₀.
1. (The plane Q.) Sibling idtp_ccd_scsp_tangent_plane_mem applied to (P, M, p, ρ) (its hypotheses: M is an embedded C¹ 2-submanifold, p = r₀u ∈ M, ρ > 0, and the radial hypothesis) gives finrank Q = 2 and p ∈ Q; hence u = r₀⁻¹p ∈ Q.
2. (Choice of e.) span{u} ≤ Q and finrank span{u} = 1 < 2 = finrank Q (finrank_span_singleton), so span{u} < Q and there is w ∈ Q with w ∉ span{u} (SetLike.exists_of_lt). Then e′ := w − ⟨w,u⟩u ∈ Q, e′ ≠ 0 (otherwise w = ⟨w,u⟩u ∈ span{u}) and ⟨u, e′⟩ = ⟨u,w⟩ − ⟨w,u⟩‖u‖² = 0. Put e := ‖e′‖⁻¹e′; then e ∈ Q, ‖e‖ = 1, ⟨u, e⟩ = 0. (u, e) is orthonormal, hence linearly independent (Orthonormal.linearIndependent), so span{u, e} has finrank 2; since span{u, e} ≤ Q and finrank Q = 2, Q = span{u, e} (Submodule.eq_of_le_of_finrank_eq). Consequently every v ∈ Q satisfies v = ⟨v,u⟩u + ⟨v,e⟩e (write v = a·u + b·e by Submodule.mem_span_pair and take inner products with u and e).
3. (Coordinates.) Let ρ₁ := min(ρ, r₀/2) > 0 and U := B_{ρ₁}(p), an open set with p ∈ U ⊆ B_ρ(p). For x ∈ U, ⟨x,u⟩ = ⟨p,u⟩ + ⟨x − p, u⟩ ≥ r₀ − ‖x − p‖ > r₀/2 > 0; in particular x ≠ 0. Define f(x) := arctan(⟨x,e⟩/⟨x,u⟩) and F : Euclid P → Euclid 2, F(x) := ⟨⟨‖x‖, f(x)⟩⟩. On U both coordinate functions are C^∞: the norm is smooth away from 0 (contDiffAt_norm), x ↦ ⟨x,e⟩ and x ↦ ⟨x,u⟩ are continuous linear, the quotient is smooth where ⟨x,u⟩ ≠ 0, and arctan is smooth (Real.contDiff_arctan); hence F is C¹ on U (coordinatewise criterion contDiffOn_piLp). Homogeneity: if ⟨x,u⟩ > 0 and c > 0 then f(c·x) = arctan(c⟨x,e⟩/(c⟨x,u⟩)) = f(x) and ‖c·x‖ = c‖x‖. Values at p: ⟨p,e⟩ = r₀⟨u,e⟩ = 0, so f(p) = arctan 0 = 0 and F(p) = ⟨⟨r₀, 0⟩⟩. Derivative at p, coordinatewise (hasStrictFDerivAt_piLp / hasFDerivWithinAt_piLp): the norm has derivative h ↦ ⟨p, h⟩/‖p‖ = ⟨u, h⟩ at p ≠ 0 (e.g. from (hasFDerivAt_id p).norm_sq and HasFDerivAt.sqrt, using Real.sqrt_sq), and Df(p)h = (1/(1 + 0²))·(⟨h,e⟩⟨p,u⟩ − ⟨p,e⟩⟨h,u⟩)/⟨p,u⟩² = ⟨e, h⟩/r₀. So DF(p)h = ⟨⟨⟨u, h⟩, ⟨e, h⟩/r₀⟩⟩.
4. (Transversality.) If v ∈ Q and DF(p)v = 0, then ⟨u,v⟩ = 0 and ⟨e,v⟩ = 0, so v = ⟨v,u⟩u + ⟨v,e⟩e = 0 by step 2. Hence DF(p) is injective on Q.
5. (Local inverse.) Sibling idtp_ccd_scsp_local_inverse applied to (P, M, p, U, F) gives an open O ⊆ Euclid 2, an open N₀ ⊆ Euclid P and G : Euclid 2 → Euclid P with F(p) ∈ O, p ∈ N₀ ⊆ U, G C¹ on O, G(O) = M ∩ N₀, F(G w) = w for w ∈ O, and tangentSpace M (G w) = Set.range DG(w) for w ∈ O. If x ∈ M ∩ N₀, then x = G w for some w ∈ O, so F x = w and G(F x) = x.
6. (Square and the set N.) As O is open and F(p) = ⟨⟨r₀, 0⟩⟩ ∈ O, choose ε > 0 with B_ε(F p) ⊆ O and fix s with 0 < s < min(ε/2, r₀/2). Let R_s := {w ∈ Euclid 2 : |w₀ − r₀| < s and |w₁| < s} = {⟨⟨t, α⟩⟩ : t ∈ J, α ∈ I} (w₀, w₁ the coordinates of w), an open set. For w ∈ R_s, ‖w − F p‖² = (w₀ − r₀)² + w₁² < 2s² < ε², so R_s ⊆ B_ε(F p) ⊆ O; also 0 < s < r₀. Define N := N₀ ∩ (U ∩ F⁻¹(R_s)); since F is continuous on the open set U, U ∩ F⁻¹(R_s) is open (ContinuousOn.isOpen_inter_preimage), so N is open. N ⊆ N₀ ⊆ U ⊆ B_ρ(p), and ⟨x, u⟩ > 0 for every x ∈ N (step 3). p ∈ N because p ∈ N₀, p ∈ U and F(p) ∈ R_s. Claim: M ∩ N = G(R_s). If x ∈ M ∩ N, then x ∈ M ∩ N₀, so x = G(F x) with F x ∈ R_s. Conversely, if w ∈ R_s ⊆ O, then G w ∈ G(O) = M ∩ N₀, so G w ∈ M and G w ∈ N₀ ⊆ U, and F(G w) = w ∈ R_s; hence G w ∈ M ∩ N.
7. (The curve.) Define γ(α) := r₀⁻¹·G(⟨⟨r₀, α⟩⟩). The map α ↦ ⟨⟨r₀, α⟩⟩ is affine and maps I into R_s ⊆ O, so γ is C¹ on I (ContDiffOn.comp, then multiplication by a constant). For α ∈ I put x_α := G(⟨⟨r₀, α⟩⟩) ∈ G(R_s) = M ∩ N; then F(x_α) = ⟨⟨r₀, α⟩⟩, i.e. ‖x_α‖ = r₀ and f(x_α) = α. Hence ‖γ(α)‖ = 1; x_α ∈ N gives ⟨x_α, u⟩ > 0, so ⟨γ(α), u⟩ = r₀⁻¹⟨x_α, u⟩ > 0; and by homogeneity f(γ(α)) = f(x_α) = α, i.e. arctan(⟨γ(α),e⟩/⟨γ(α),u⟩) = α. Also γ(0) = r₀⁻¹·G(F p) = r₀⁻¹·p = u, using p ∈ M ∩ N₀ and step 5.
8. (Radial structure.) Claim: G(⟨⟨t, α⟩⟩) = t·γ(α) for all t ∈ J and α ∈ I. Fix α ∈ I and let A := {t ∈ J : G(⟨⟨t, α⟩⟩) = t·γ(α)}. (i) r₀ ∈ A, since r₀·γ(α) = G(⟨⟨r₀, α⟩⟩). (ii) closure(A) ∩ J ⊆ A: the maps t ↦ G(⟨⟨t, α⟩⟩) and t ↦ t·γ(α) are continuous on the open interval J (G is continuous on O and t ↦ ⟨⟨t, α⟩⟩ maps J into R_s), so their equalizer is relatively closed in J. (iii) A is open: let t ∈ A and x := t·γ(α) = G(⟨⟨t, α⟩⟩) ∈ M ∩ N. As N is open, choose η > 0 with B_η(x) ⊆ N and η ≤ t − (r₀ − s). Let |t′ − t| < η; then t′ > r₀ − s > 0 and ‖t′·γ(α) − x‖ = |t′ − t|·‖γ(α)‖ < η, so y := t′·γ(α) ∈ N ⊆ B_ρ(p). Moreover y = (t′/t)·x with x ∈ M ∩ B_ρ(p) (as N ⊆ B_ρ(p)) and t′/t > 0, so y ∈ M by the radial hypothesis. Thus y ∈ M ∩ N = G(R_s), say y = G(w) with w ∈ R_s, and then w = F(G w) = F(y) = ⟨⟨‖t′·γ(α)‖, f(t′·γ(α))⟩⟩ = ⟨⟨t′, f(γ(α))⟩⟩ = ⟨⟨t′, α⟩⟩, using t′ > 0, ‖γ(α)‖ = 1, ⟨γ(α), u⟩ > 0 and homogeneity. Hence ⟨⟨t′, α⟩⟩ = w ∈ R_s, i.e. t′ ∈ J, and G(⟨⟨t′, α⟩⟩) = y = t′·γ(α), i.e. t′ ∈ A. So (t − η, t + η) ⊆ A. (iv) J is preconnected, A is open, A ∩ J ≠ ∅ and closure(A) ∩ J ⊆ A, so J ⊆ A (IsPreconnected.subset_of_closure_inter_subset). Consequently M ∩ N = G(R_s) = {t·γ(α) : t ∈ J, α ∈ I}, i.e. M ∩ N is the image of J ×ˢ I under q ↦ q.1·γ(q.2).
9. (Tangent planes.) Let t ∈ J, α ∈ I, w := ⟨⟨t, α⟩⟩ ∈ R_s and x := t·γ(α) = G w. G agrees with G̃(w′) := w′₀·γ(w′₁) on the open neighbourhood R_s of w (step 8), so DG(w) = DG̃(w) (Filter.EventuallyEq.fderiv_eq). Since γ is differentiable at α (I is open), G̃ is differentiable at w with DG̃(w)h = h₀·γ(α) + t·h₁·γ′(α) (product rule). As t ≠ 0, Set.range DG̃(w) = {c₁γ(α) + c₂γ′(α) : c₁, c₂ ∈ ℝ}, the carrier of span{γ(α), γ′(α)} (Submodule.mem_span_pair). By step 5, tangentSpace M x = Set.range DG(w) is the carrier of span{γ(α), γ′(α)}; therefore span(tangentSpace M (t·γ(α))) = span{γ(α), γ′(α)} (Submodule.span_eq).
10. (γ′(0) = e.) Sibling idtp_ccd_scsp_angle_curve applied to (P, u, e, s, γ) (hypotheses from step 7) at α = 0, where γ(0) = u, gives ⟨u, γ′(0)⟩ = 0 and ⟨u,u⟩⟨γ′(0),e⟩ − ⟨u,e⟩⟨γ′(0),u⟩ = ⟨u,u⟩² + ⟨u,e⟩²; since ⟨u,u⟩ = 1 and ⟨u,e⟩ = 0, this says ⟨γ′(0), e⟩ = 1. By step 9 with t = r₀, α = 0 (r₀·γ(0) = p), Q = span(tangentSpace M p) = span{u, γ′(0)} ∋ γ′(0), and by step 2, γ′(0) = ⟨γ′(0),u⟩u + ⟨γ′(0),e⟩e = 0·u + 1·e = e.
11. (Collect.) The data e, s, N, γ satisfy: ‖e‖ = 1 and ⟨u, e⟩ = 0 (step 2); 0 < s < r₀ (step 6); N open, r₀u = p ∈ N, N ⊆ B_ρ(r₀u) and ⟨x, u⟩ > 0 on N (step 6); γ C¹ on I with γ(0) = u (step 7) and γ′(0) = e (step 10); ‖γ(α)‖ = 1, ⟨γ(α),u⟩ > 0 and arctan(⟨γ(α),e⟩/⟨γ(α),u⟩) = α on I (step 7); M ∩ N = image of J ×ˢ I under q ↦ q.1·γ(q.2) (step 8); and span(tangentSpace M (t·γ(α))) = span{γ(α), γ′(α)} for t ∈ J, α ∈ I (step 9). ∎

## Key steps

1. Sibling tangent_plane_mem: Q = span(tangentSpace M p), p = r₀u, has finrank 2 and contains u; choose a unit e ∈ Q with ⟨u,e⟩ = 0, so Q = span{u, e}.
2. F(x) = (‖x‖, arctan(⟨x,e⟩/⟨x,u⟩)) is C¹ on U = B_{min(ρ, r₀/2)}(p) ⊆ {⟨x,u⟩ > 0}, and DF(p)v = (⟨u,v⟩, ⟨e,v⟩/r₀) is injective on Q.
3. Sibling local_inverse gives O, N₀, G with G(O) = M ∩ N₀ and F∘G = id on O; shrinking to a square R_s ⊆ O and N := N₀ ∩ U ∩ F⁻¹(R_s) gives M ∩ N = G(R_s).
4. γ(α) := r₀⁻¹G(r₀, α) satisfies ‖γ‖ = 1, ⟨γ,u⟩ > 0, f(γ(α)) = α, γ(0) = u; radial invariance, F∘G = id and connectedness of (r₀ − s, r₀ + s) give G(t, α) = tγ(α).
5. range DG(t, α) = span{γ(α), γ′(α)} gives the tangent planes; sibling angle_curve and γ′(0) ∈ Q = span{u, e} give γ′(0) = e.

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
