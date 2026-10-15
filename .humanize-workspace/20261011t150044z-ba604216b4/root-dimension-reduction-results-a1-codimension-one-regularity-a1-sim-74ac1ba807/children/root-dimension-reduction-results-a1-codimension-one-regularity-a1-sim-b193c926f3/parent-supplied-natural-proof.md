# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1.variation_field-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof steps (1a)–(1b) and the remark in (1c) that ζ̃ and Dζ̃ vanish on T_xM at points of M outside tsupport Z. Departure: the projection Π onto A₀ used in (1a) plays no role later and is omitted. No dependencies.

1. (Cut-off.) C is compact and C ⊆ M ⊆ O ∩ U, an open set. Since ℝ^P is locally compact, there is a compact L with C ⊆ interior(L) and L ⊆ O ∩ U (exists_compact_between). The smooth Urysohn lemma exists_contDiff_support_eq_eq_one_iff (with smoothness ⊤), applied to the open set interior(L) and the closed set C ⊆ interior(L), gives β : ℝ^P → ℝ, C^∞, with support β = interior(L) and β(x) = 1 for x ∈ C. Then tsupport β = closure(interior L) ⊆ L because L is closed; so tsupport β is compact and tsupport β ⊆ O ∩ U.

2. (Definition and smoothness of Z.) Put Z(y) := (β(y)ζ(y))ν(y). Let y ∈ ℝ^P. If y ∈ O, then βζ is C^∞ at y and ν is C^∞ at y (ν is C^∞ on the open set O ∋ y), so Z is C^∞ at y. If y ∉ O, then y ∉ tsupport β (as tsupport β ⊆ O); the complement of tsupport β is an open neighbourhood of y on which β = 0 (image_eq_zero_of_notMem_tsupport), so Z = 0 near y and Z is C^∞ at y. Thus Z is C^∞ at every point, i.e. ContDiff ℝ ⊤ Z (contDiff_iff_contDiffAt).

3. (Support.) tsupport Z ⊆ tsupport(βζ) ⊆ tsupport β (tsupport_smul_subset_left, tsupport_mul_subset_left), so tsupport Z ⊆ U. Z vanishes outside the compact closed set tsupport β, hence Z has compact support (HasCompactSupport.intro').

4. ((a) Z = ζν on M.) Let x ∈ M. If x ∈ C then β(x) = 1 and Z(x) = ζ(x)ν(x). If x ∉ C then ζ(x) = 0 by hypothesis, so Z(x) = 0 = ζ(x)ν(x).

5. ((b) The tangential derivative.) Let x ∈ M and v ∈ tangentSpace M x, witnessed by γ: C¹ on (−1,1), γ((−1,1)) ⊆ M, γ(0) = x, γ'(0) = v. Z and ζ are differentiable everywhere, and ν is differentiable at x (x ∈ O, O open). By the chain rule s ↦ Z(γ(s)) has derivative DZ(x)v at 0; by the chain and product rules (HasDerivAt.smul) s ↦ ζ(γ(s))ν(γ(s)) has derivative ζ(x)Dν(x)v + (Dζ(x)v)ν(x) at 0. By step 4 these two functions coincide on (−1,1), a neighbourhood of 0, so their derivatives coincide: DZ(x)v = (Dζ(x)v)ν(x) + ζ(x)Dν(x)v. Both sides are linear in v (DZ(x), Dζ(x), Dν(x) are linear maps), so by induction over the span (zero, sums, scalar multiples; Submodule.span_induction) the identity holds for every τ ∈ span(tangentSpace M x).

6. ((c) Vanishing off tsupport Z.) Let x ∈ M with x ∉ tsupport Z. The complement N of tsupport Z is an open neighbourhood of x on which Z = 0. For y ∈ N ∩ M, ζ(y)ν(y) = Z(y) = 0 by (a) and ν(y) ≠ 0 since |ν(y)| = 1, hence ζ(y) = 0; in particular ζ(x) = 0. Now let v ∈ tangentSpace M x with curve γ as in step 5. γ is continuous at 0 with γ(0) = x, so γ(s) ∈ N for all small |s|, and γ(s) ∈ M for |s| < 1; hence ζ∘γ vanishes on a neighbourhood of 0 and its derivative at 0 is 0. By the chain rule this derivative equals Dζ(x)v, so Dζ(x)v = 0. By linearity Dζ(x)τ = 0 for every τ ∈ span(tangentSpace M x). ∎

## Key steps

1. A C^∞ cut-off β with β ≡ 1 on C and compact tsupport β ⊆ O ∩ U (exists_compact_between, exists_contDiff_support_eq_eq_one_iff).
2. Z := βζν is C^∞ (near points of O a product of smooth maps, elsewhere locally 0), compactly supported in U, and equals ζν on M.
3. Differentiating along C¹ curves in M gives DZ(x)τ = (Dζ(x)τ)ν(x) + ζ(x)Dν(x)τ, and off tsupport Z gives ζ(x) = 0 and Dζ(x)τ = 0; extend to span T_xM by linearity.

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
