# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1.smooth_glue-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 6 of the supplied proof of the parent: "O := ⋃_{y∈M} O_y is open and contains M. As an open subset of ℝ^P it is a σ-compact smooth manifold, so there is a smooth partition of unity (λ_i)_{i∈I} on O subordinate to the open cover {O_y} (Mathlib SmoothPartitionOfUnity.exists_isSubordinate): λ_i ∈ C^∞(O; [0, 1]), tsupport λ_i ⊆ O_{y(i)} (closure in O), the family is locally finite, and Σ_iλ_i = 1 on O. Define ν(z) := Σ_iλ_i(z)ν_{y(i)}(z) for z ∈ O, each term being C^∞ on O …, the sum being locally finite; and ν(z) := 0 for z ∉ O. Then ν is C^∞ on O, and for x ∈ M, ν(x) = Σ_iλ_i(x)ν₀(x) = ν₀(x)." Here the local extensions g_y are arbitrary (in the parent g_y = ν_y and f = ν₀) and the codomain is any real normed space F.

1. (The open set.) For each y ∈ M choose O_y and g_y as in the hypothesis and put O := ⋃_{y∈M} O_y. O is open, and M ⊆ O because y ∈ O_y.

2. (O as a manifold.) Regard O as an open submanifold of ℝ^P: its charts are the restrictions of the identity chart of ℝ^P (model space ℝ^P with the trivial model with corners), so O is a C^∞ manifold. O is Hausdorff and second countable (a subspace of ℝ^P) and locally compact (an open subset of the locally compact space ℝ^P; in Lean via the open embedding of the subtype, IsOpenEmbedding.locallyCompactSpace); hence O is σ-compact (a locally compact second-countable space is σ-compact). Therefore smooth partitions of unity on O subordinate to any open cover of O exist (Mathlib SmoothPartitionOfUnity.exists_isSubordinate, applied to the closed subset O of the manifold O).

3. (Partition of unity.) The sets O_y (y ∈ M) form an open cover of O. Let (λ_i)_{i∈I} be a smooth partition of unity on O subordinate to it: each λ_i : O → [0, 1] is C^∞, the family of supports is locally finite, Σ_i λ_i = 1 on O, and for each i there is y(i) ∈ M with tsupport λ_i ⊆ O_{y(i)} (closure taken in O).

4. (The glued map.) For p ∈ O put G(p) := Σ_i λ_i(p)·g_{y(i)}(p), a finite sum near every point by local finiteness. Each term λ_i·g_{y(i)} is C^∞ on O: near a point of the open set O_{y(i)} it is a product of C^∞ functions, and a point of O ∖ O_{y(i)} lies outside the set tsupport λ_i, which is closed in O, so the term vanishes on a neighbourhood of it. A locally finite sum of C^∞ functions is C^∞, so G is C^∞ on O.

5. (G = f on M.) Let x ∈ M. If λ_i(x) ≠ 0 then x ∈ tsupport λ_i ⊆ O_{y(i)}, so x ∈ M ∩ O_{y(i)} and g_{y(i)}(x) = f(x). Hence G(x) = Σ_i λ_i(x)·f(x) = f(x).
 (Equivalently, steps 3–5 are Mathlib's local-to-global theorem for convex constraints, exists_contMDiffMap_forall_mem_convex_of_local, on the manifold O with t(p) := {f(p)} for p ∈ M and t(p) := F for p ∉ M — all convex: for p ∈ O pick y with p ∈ O_y; then O_y ∩ O is a neighbourhood of p in O on which g_y is C^∞, and g_y(q) ∈ t(q) for every q in it.)

6. (Back to ℝ^P.) Define ν(z) := G(z) for z ∈ O and ν(z) := 0 for z ∉ O. Since O is open in ℝ^P and the charts of O are restrictions of the identity of ℝ^P, smoothness of G at a point p of the manifold O is the same as smoothness of ν at p in ℝ^P (Mathlib contMDiffAt_subtype_iff together with contMDiffAt_iff_contDiffAt; ν restricted to O is G). So ν is C^∞ at every point of the open set O, i.e. ν is C^∞ on O, and ν(x) = G(x) = f(x) for every x ∈ M ⊆ O. ∎

## Key steps

1. O := ⋃_y O_y is an open, Hausdorff, σ-compact submanifold of ℝ^P containing M.
2. A smooth partition of unity (λ_i) on O subordinate to {O_y} gives G := Σ_i λ_i g_{y(i)}, C^∞ on O.
3. At x ∈ M every nonzero term has g_{y(i)}(x) = f(x), so G(x) = f(x); extending G by 0 off O gives ν, C^∞ on O.

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
