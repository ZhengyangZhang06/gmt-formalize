# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1.tangent_projection-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof items (0.1) (T_x ⊆ A₀, A₀ = T_x ⊕ ℝν(x)) and (0.5) (continuity of x ↦ P_x on M). Departure: continuity is obtained from the hypersurface identity P_x = Π − ν(x)⊗ν(x) instead of the chart formula P_{ψ(v)} = Dψ(Dψ*Dψ)^{-1}Dψ*. Dependency: chart_tangent_space (Lean name Submission.chart_tangentSpace_eq_range_fderiv).

Notation. For x ∈ M: T_x := tangentSpace M x, S_x := span_ℝ T_x, P_x := orthogonal projection onto S_x, Π := orthogonal projection onto A₀.

1. (T_x ⊆ A₀.) Let x ∈ M and v ∈ T_x, witnessed by γ : ℝ → ℝ^P that is C¹ on (−1,1), maps (−1,1) into M, has γ(0) = x and derivative v at 0. For 0 < |s| < 1 the slope s⁻¹(γ(0 + s) − γ(0)) lies in A₀, because γ(s) and γ(0) lie in M ⊆ A₀ and A₀ is a linear subspace. By HasDerivAt.tendsto_slope_zero these slopes tend to v along the punctured neighbourhood filter of 0, and A₀ is closed (a finite-dimensional subspace, Submodule.closed_of_finiteDimensional). Hence v ∈ A₀ (IsClosed.mem_of_tendsto).

2. (A chart and the dimension of S_x.) By IsEmbeddedSubmanifold 1 m M at x there are open V ⊆ ℝ^m, W ⊆ ℝ^P and ψ : ℝ^m → ℝ^P with x ∈ W, ψ C¹ on V, injective on V, ψ(V) = W ∩ M, V ∩ ψ⁻¹(K) compact for every compact K ⊆ W, and Dψ(z) injective for z ∈ V. Since x ∈ W ∩ M = ψ(V), x = ψ(v₀) for some v₀ ∈ V. By chart_tangent_space (with r = 1), T_x = range Dψ(v₀). This range is a linear subspace, so S_x = range Dψ(v₀) (Submodule.span_eq), and since Dψ(v₀) : ℝ^m → ℝ^P is injective, dim S_x = m (LinearMap.finrank_range_of_inj, finrank_euclideanSpace_fin).

3. (S_x = (ℝν(x))^⊥ ∩ A₀.) Write n := ν(x) and H := (ℝn)^⊥ ⊓ A₀. Since n ∈ A₀ and n ≠ 0 (|n| = 1), the line ℝn has dimension 1 and is contained in A₀, so Submodule.finrank_add_inf_finrank_orthogonal gives 1 + dim H = dim A₀ = m + 1, i.e. dim H = m. Every v ∈ T_x satisfies n·v = 0 (hypothesis) and v ∈ A₀ (step 1), so T_x ⊆ H and therefore S_x ≤ H (Submodule.span_le). Both have dimension m, so S_x = H (Submodule.eq_of_le_of_finrank_eq).

4. (The projection formula.) Fix u ∈ ℝ^P and put p := Πu − (n·u)n. Then p ∈ A₀ (Πu ∈ A₀ and n ∈ A₀), and
 n·p = n·Πu − (n·u)(n·n) = Πn·u − n·u = 0,
because Π is self-adjoint (Submodule.inner_starProjection_left_eq_right), Πn = n (n ∈ A₀) and n·n = |n|² = 1. So p ∈ H = S_x. For every w ∈ H = S_x,
 (u − p)·w = (u − Πu)·w + (n·u)(n·w) = 0,
since w ∈ A₀ and u − Πu ∈ A₀^⊥ (Submodule.sub_starProjection_mem_orthogonal), and n·w = 0 because w ∈ (ℝn)^⊥. A vector p ∈ S_x with u − p ⊥ S_x is the orthogonal projection of u onto S_x (Submodule.eq_starProjection_of_mem_of_inner_eq_zero). Hence P_x u = Πu − (ν(x)·u)ν(x) for every x ∈ M and u ∈ ℝ^P, which is the first conjunct.

5. (Continuity.) Assume ν is continuous on M and fix u ∈ ℝ^P. The map x ↦ Πu − (ν(x)·u)ν(x) is continuous on M: it is a constant minus the product of the continuous scalar function x ↦ ν(x)·u (ContinuousOn.inner) and the continuous map ν. By step 4 it coincides on M with x ↦ P_x u, which is therefore continuous on M (ContinuousOn.congr). This is the second conjunct. ∎

## Key steps

1. Tangent vectors are limits of slopes of curves in M ⊆ A₀, so T_xM ⊆ A₀ (A₀ closed); T_xM ⊥ ν(x) by hypothesis.
2. chart_tangent_space: span T_xM = range Dψ(v₀) with Dψ(v₀) injective, so dim span T_xM = m = dim((ℝν(x))^⊥ ∩ A₀) and the two subspaces coincide.
3. p := Πu − (ν(x)·u)ν(x) lies in span T_xM and u − p ⊥ span T_xM, so P_x u = p; continuity of x ↦ P_x u on M follows from that of ν.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 1,457p GMT/Ch07/Submission.lean (Euclid, IsEmbeddedSubmanifold, tangentSpace, μHE, main_theorem placeholder)`
- `python3 scans of dag.json: selected node, its depends_on (area_formula, lipschitz_approx, smooth_charts, chart_tangent_space, locally_closed) with statuses and frozen lean_statements; hypercone_plane decomposition-v1.json (reused chart_tangent_space entry)`
- `rg -c codim1_hcp_stab_ local-references/123e8435b4a2469b/project lake-packages-25730c7c/simongmt GMT runs/.../dag.json (no match)`
- `rg -n -i 'second.?variation|stability|jacobian' lake-packages-25730c7c/simongmt/Poincare -t lean`
- `rg -n 'theorem coeff_det_one_add_X_smul_eq_sum_minors|exists_contDiff_support_eq_eq_one_iff|det_eq_prod_eigenvalues|ContDiffAt.isSymmSndFDerivAt|trace_eq_sum_inner|exists_compact_between|tendsto_integral_filter_of_dominated_convergence|setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|IntegrableOn.of_forall_sdiff_eq_zero|norm_image_sub_le_of_norm_fderiv_le|det_nonneg' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lean #check after import GMT.Ch07.Submission (/tmp/stab-decomp-q7/Avail*.lean): Matrix.PosSemidef.det_nonneg, Matrix.posSemidef_conjTranspose_mul_self, Matrix.det_le, Poincare.SimonGMT.Chapter08.quadraticMatrixDeterminant, LinearMap.normDet (absent); LinearMap.IsSymmetric.det_eq_prod_eigenvalues, Matrix.coeff_det_one_add_X_smul_eq_sum_minors, LinearMap.trace_eq_sum_inner, exists_contDiff_support_eq_eq_one_iff, ContDiffAt.isSymmSndFDerivAt, Submodule.finrank_add_inf_finrank_orthogonal (present)`
- `git show --stat d626082a69a0 (accepted chart_tangentSpace_eq_range_fderiv: proof appended to GMT/Ch07/Submission.lean, imports unchanged)`
- `sed -n 1385,1440p; 1700,1960p; 6640,6728p /runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/runtime.py (_decompose depth gate, _solve_children name reuse, _existing_lean_name_problem)`
- `lean -DautoImplicit=false /tmp/stab-decomp-q7/{Assembly,Parse,AProof,BProof,CProof,D1Proof,D2Proof,EProof,FProof,IProof,GProof,H1Proof,H2Proof,Full}.lean with LEAN_PATH = workspace .lake/build/lib/lean plus every package's .lake/build/lib/lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-74ac1ba807/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/JacobianBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/SimonsInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Matrix/PosDef.lean`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/runtime.py`
- `/tmp/stab-decomp-q7/Full.lean`

Pins match: the manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib; the snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…). Reuse: chart_tangentSpace_eq_range_fderiv is accepted (candidate d626082a69a0) and is reused with its byte-identical frozen type; area_formula (codim1_hcp_submanifold_area_formula) and lipschitz_approx (codim1_hcp_lipschitz_smooth_approx) are active nodes under another parent, so they are not children: they enter smooth_case and lipschitz_extension as hypotheses and are discharged in this node's glue, where they are resolved dependencies; locally_closed likewise supplies MeasurableSet M in the glue. The 11 codim1_hcp_stab_ names occur nowhere in dag.json, GMT/, SimonGMT or the snapshot (rg: no match). Library: SimonGMT has related but unusable material (Chapter08/JacobianBounds.lean: quadraticMatrixDeterminant = det(1 + t•X + t²•Y) with first-order Lipschitz bounds; Chapter02/AreaApproximation.lean; AppendixB algebra), none in Submission's import closure and none giving a second-order expansion, so det_second_order and jacobian_bound are new. The pinned Mathlib (inside the import closure) supplies Matrix.coeff_det_one_add_X_smul_eq_sum_minors (Charpoly/Coeff.lean:398), LinearMap.IsSymmetric.det_eq_prod_eigenvalues (Spectrum.lean:389), ContDiffAt.isSymmSndFDerivAt (FDeriv/Symmetric.lean:533), LinearMap.trace_eq_sum_inner (InnerProductSpace/Trace.lean:25), exists_contDiff_support_eq_eq_one_iff (PartitionOfUnity.lean:789), exists_compact_between (LocallyCompact.lean:172), tendsto_integral_filter_of_dominated_convergence (DominatedConvergence.lean:67), setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (Bochner/Set.lean:466), IntegrableOn.of_forall_sdiff_eq_zero (IntegrableOn.lean:435), Convex.norm_image_sub_le_of_norm_fderiv_le (MeanValue.lean:499); Matrix.PosSemidef.det_nonneg (Analysis/Matrix/PosDef.lean:51) exists but is outside the closure, so det ≥ 0 is proved via the spectral theorem. Lean: all 11 new child types elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07 with the contract opens; Full.lean (1626 lines, 0 errors, no sorry) proves every child and the selected frozen type; #print axioms lists only propext, Classical.choice, Quot.sound for the children (plus chart_tangentSpace_eq_range_fderiv for tangent_projection, shape_operator, smooth_case), and for the selected theorem additionally only its resolved dependencies chart_tangentSpace_eq_range_fderiv, dimred_rpd_embedded_locally_closed, codim1_hcp_submanifold_area_formula and codim1_hcp_lipschitz_smooth_approx (as axioms with their frozen types). The runtime caps depth at 6, so these depth-6 children are leaves.
