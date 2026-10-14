# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1.zero_mean_curvature-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 7 of the supplied proof of the parent ((7a) continuity of div_M ν on M; (7b) stationarity tested with X = φν gives ∫_M φ·div_M ν dH^m = 0; (7c) continuity and positivity of H^m on small balls force div_M ν ≡ 0), with (7c) packaged in the sibling fundamental_lemma (Submission.codim1_hcp_un_fundamental_lemma). Departure in (7a): continuity of x ↦ P_x on M is obtained from the hypersurface identity P_x = P_{A₀} − ν(x)⊗ν(x) (step 2 below, the sibling hyperplane_projection) instead of the chart formula P_x = DG_y(a)(DG_y(a)*DG_y(a))^{-1}DG_y(a)*; it needs only the continuity of ν. Sibling lemmas: tangent_subspace (Submission.codim1_hcp_un_tangent_subspace), hyperplane_projection (Submission.codim1_hcp_un_hyperplane_projection), fundamental_lemma, density_one (Submission.dimred_rpd_submanifold_density_one), locally_closed (Submission.dimred_rpd_embedded_locally_closed).
Notation: H^m := μHE[m]; for x ∈ M, T_x := tangentSpace M x and P_x := the orthogonal projection onto span T_x; P_{A₀} := the orthogonal projection onto A₀; h(x) := trace(P_x∘Dν(x)) for x ∈ ℝ^P (P_x defined by the same formula for every x); O is an open set with M ⊆ O on which ν is C^∞.

1. (Tangent spaces.) For x ∈ M, tangent_subspace (IsEmbeddedSubmanifold 1 m M and M ⊆ A₀) gives a subspace Q_x with underlying set T_x, dim Q_x = m and Q_x ⊆ A₀. Hence span T_x = Q_x and P_x is the orthogonal projection onto Q_x.

2. (Projection formula.) Let x ∈ M. Then P_x w = P_{A₀}w − (ν(x)·w)ν(x) for every w ∈ ℝ^P: apply hyperplane_projection with Q := Q_x (dim m, Q_x ⊆ A₀, step 1), dim A₀ = m + 1 and n := ν(x), which lies in A₀, has |ν(x)| = 1 and is orthogonal to every v ∈ Q_x = T_x (hypotheses).

3. (Continuity of h on M.) For z ∈ ℝ^P put F(z) := trace(P_{A₀}∘Dν(z)) − ν(z)·Dν(z)ν(z). For x ∈ M, step 2 gives P_x∘Dν(x) = P_{A₀}∘Dν(x) − R_x, where R_x w := (ν(x)·Dν(x)w)ν(x) is a rank-one map whose trace is ν(x)·Dν(x)ν(x); hence h(x) = F(x). F is continuous on O: ν is C^∞ on the open set O, so ν and z ↦ Dν(z) are continuous on O, and composition with P_{A₀}, the trace and the inner product are continuous (finite dimension). As M ⊆ O and h = F on M, h is continuous on M.

4. (Test fields.) Put U' := O ∩ U, an open set containing M. Let φ : ℝ^P → ℝ be C^∞ with compact support and tsupport φ ⊆ U', and define X(z) := φ(z)ν(z).
 (a) X is C^∞ on ℝ^P, in particular C¹: near every point of the open set O, X is a product of C^∞ functions; a point z ∉ O lies outside the closed set tsupport φ ⊆ O, so φ, and hence X, vanishes on a neighbourhood of z.
 (b) X vanishes wherever φ does, so tsupport X ⊆ tsupport φ, which is compact and contained in U' ⊆ U. Thus X has compact support and tsupport X ⊆ U.
 (c) For x ∈ M ⊆ O the product rule gives DX(x)w = φ(x)Dν(x)w + (Dφ(x)w)ν(x). The trace is linear and the rank-one map w ↦ ℓ(w)u has trace ℓ(u), so trace(P_x∘DX(x)) = φ(x)h(x) + Dφ(x)(P_xν(x)) = φ(x)h(x), because ν(x) ⊥ T_x gives ν(x) ⊥ span T_x and P_xν(x) = 0.
 (d) By stationarity applied to X (admissible by (a) and (b)), ∫_M trace(P_x∘DX(x)) dH^m(x) = 0. By (c) the integrand equals φ(x)h(x) at every x ∈ M (and M is measurable, step 5), so ∫_M φ·h dH^m = 0.

5. (Measurability, finiteness, positivity.) By locally_closed, M is measurable. For every compact K ⊆ U' we have K ⊆ U, so H^m(M ∩ K) < ∞ by hypothesis. For x ∈ M and s > 0, H^m(M ∩ B_s(x)) > 0: by density_one (IsEmbeddedSubmanifold 1 m M, x ∈ M), H^m(M ∩ B_t(x))/(ω_m t^m) → 1 as t ↓ 0, where ω_m = unitBallVolume m; if H^m(M ∩ B_s(x)) were 0, then H^m(M ∩ B_t(x)) = 0 for every t ∈ (0, s] by monotonicity, so the quotient would be 0 for all these t, contradicting the limit 1.

6. (Conclusion.) Apply fundamental_lemma with the measure H^m, the open set U', the set M ⊆ U' and the function h: M is measurable, h is continuous on M (step 3), H^m(M ∩ K) < ∞ for every compact K ⊆ U' and H^m(M ∩ B_s(x)) > 0 for x ∈ M, s > 0 (step 5), and ∫_M φ·h dH^m = 0 for every C^∞ φ with compact support and tsupport φ ⊆ U' (step 4). Hence h(x) = trace(P_x∘Dν(x)) = 0 for every x ∈ M. ∎

## Key steps

1. tangent_subspace: span T_x = Q_x is an m-dimensional subspace of A₀ orthogonal to ν(x).
2. hyperplane_projection: P_x = P_{A₀} − ν(x)⊗ν(x), so h(x) = trace(P_x∘Dν(x)) agrees on M with a function continuous on O.
3. For C^∞ φ with compact support in O ∩ U, X = φν is an admissible C¹ field and trace(P_x∘DX(x)) = φ(x)h(x) on M (P_xν(x) = 0); stationarity gives ∫_M φh dH^m = 0.
4. locally_closed (measurability), local finiteness and density_one (positive measure of M ∩ B_s(x)) feed fundamental_lemma, so h ≡ 0 on M.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 195,300p GMT/Ch07/Contract.lean (IsEmbeddedSubmanifold, tangentSpace, IsOrientation, IsUnitOrientationOf, MultiVector, tangentialDivergence)`
- `grep -rn 'abbrev Covector' .lake/packages/simongmt/Poincare; sed -n 1,80p simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `python3 scans of dag.json: selected node (depth 5, max 6) and all children of hypercone_plane with statuses and frozen types; accepted nodes matching tangent-dimension, gluing, fundamental-lemma, [⋀^Fin, Orthonormal, unit-normal and retraction shapes (closest: fvmb_trace_starProjection_comp_eq_sum_inner, dgoj_covector_eq_det_mul_of_mem_span, codim1_lur_normal_covector_orientation; none states a needed child)`
- `python3 read of hypercone_plane decomposition-v1.json (smooth_charts statement and proof; reused chart_tangent_space, density_one, locally_closed records)`
- `grep -n 'theorem|lemma' mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean (exists_contMDiffMap_forall_mem_convex_of_local, SmoothPartitionOfUnity.exists_isSubordinate, contDiffAt_finsum)`
- `grep -rn 'contMDiffAt_subtype_iff|contMDiffOn_iff_contDiffOn|contMDiffAt_iff_contDiffAt' mathlib/Mathlib/Geometry/Manifold; sed -n 1000,1020p Geometry/Manifold/IsManifold/Basic.lean; grep SigmaCompactSpace / IsOpen.locallyCompactSpace in Topology/Compactness`
- `sed -n 20,120p mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean; grep -rn 'OpenPartialHomeomorph.contDiffAt_symm' mathlib/Mathlib/Analysis/Calculus`
- `grep -rn 'compContinuousAlternatingMap|mkContinuous|ContinuousMultilinearMap.contDiff' in Topology/Algebra/Module/Alternating, Analysis/Normed/Module/Alternating, Analysis/Calculus/ContDiff/CPolynomial.lean`
- `grep -n 'starProjection_apply_eq_zero_iff' mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `runtime.py (flow gmt-claude-252c8df06c56): _solve_children, _existing_lean_name_problem, _accepted_checkpoint, _install_parent_supplied_child_handoff; store.py ensure`
- `grep -c codim1_hcp_un_ dag.json (0); grep -rln codim1_hcp_un_ GMT/ .lake/packages/simongmt/Poincare (none); git for-each-ref (2639 distinct objects) | xargs git grep -l codim1_hcp_un_ -- 'GMT/*.lean' (none)`
- `lean -DautoImplicit=false /tmp/un-split/check/{Types,Assembly,Inst,ProjCheck,HypUse}.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-342a5e032a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/IsManifold/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/CPolynomial.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/store.py`
- `/tmp/un-split/check/Types.lean`
- `/tmp/un-split/check/Assembly.lean`
- `/tmp/un-split/check/Inst.lean`
- `/tmp/un-split/check/ProjCheck.lean`
- `/tmp/un-split/check/HypUse.lean`

Pins.
- The snapshot manifest records project b4d606db and Mathlib 25730c7c. These equal workspace HEAD and .lake/packages/mathlib (simongmt is at 2b366308).
- The snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Library.
- Covector (Euclid P) n = Euclid P [⋀^Fin n]→L[ℝ] ℝ (SimonGMT Chapter06/Forms.lean).
- The snapshot Mathlib supplies what each child needs:
  - smooth_glue: exists_contMDiffMap_forall_mem_convex_of_local and SmoothPartitionOfUnity.exists_isSubordinate (Geometry/Manifold/PartitionOfUnity.lean), the IsManifold instance for Opens, contMDiffAt_subtype_iff, contMDiffAt_iff_contDiffAt, and IsOpen.locallyCompactSpace.
  - chart_retraction: HasStrictFDerivAt.toOpenPartialHomeomorph, ContDiffAt.to_localInverse and OpenPartialHomeomorph.contDiffAt_symm.
  - cross_product, orientation_normal and normal_local_smooth: ContinuousMultilinearMap.contDiff and ContinuousLinearMap.compContinuousAlternatingMap.
  - hyperplane_projection and zero_mean_curvature: Submodule.finrank_add_inf_finrank_orthogonal, Submodule.eq_starProjection_of_mem_of_inner_eq_zero, starProjection_apply_eq_zero_iff, LinearMap.trace_smulRight and ContDiffOn.continuousOn_fderiv_of_isOpen.
  - tangent_subspace: hasDerivAt_iff_tendsto_slope_zero.
  - chart_retraction (left inverse): LinearMap.exists_leftInverse_of_injective.
- No library lemma and no accepted DAG node states any of the 9 new children in the needed form.

DAG.
- The selected node is at depth 5 (max 6), so its children are leaves.
- chart_tangentSpace_eq_range_fderiv, dimred_rpd_submanifold_density_one and dimred_rpd_embedded_locally_closed are accepted (candidate commits d626082a69a0, e8842d90b78f, 6da66b1edf6f). They are reused with byte-identical types; the runtime returns existing nodes unchanged and skips their handoffs.
- codim1_hcp_smooth_charts is decomposing under hypercone_plane, so it is used only in this node's glue.
- The 9 new codim1_hcp_un_ names are unused everywhere.

Lean.
- All 12 child types elaborate.
- The selected frozen type is kernel-checked from them plus smooth_charts, all as axioms.
- Instances were checked by rfl.
- hyperplane_projection is already fully proved.
