# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1.shape_operator-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof items (0.2) (D_τν ∈ T_xM) and (0.3) (symmetry, Simon 4.26). Departure: the chart used for (0.3) is the C² chart supplied directly by IsEmbeddedSubmanifold 2 m M, so smooth_charts is not needed. Dependencies: chart_tangent_space (Submission.chart_tangentSpace_eq_range_fderiv), tangent_projection (Submission.codim1_hcp_stab_tangent_projection).

Notation. T_y := tangentSpace M y, S_y := span T_y, P_y := orthogonal projection onto S_y, Π := orthogonal projection onto A₀, Dν(y) := fderiv ℝ ν y.

0. (Preliminaries.) IsEmbeddedSubmanifold 2 m M implies IsEmbeddedSubmanifold 1 m M: every chart that is C² on V is C¹ on V (ContDiffOn.of_le) and the other chart conditions do not change. For y ∈ O, ν is differentiable at y with derivative Dν(y), since O is open and ν is C¹ on O. Fix x ∈ M (so x ∈ O) and write n := ν(x).

1. (A C² chart at x.) IsEmbeddedSubmanifold 2 m M at x gives open V ⊆ ℝ^m, W ⊆ ℝ^P with x ∈ W and ψ : ℝ^m → ℝ^P, C² on V, injective on V, with ψ(V) = W ∩ M, V ∩ ψ⁻¹(K) compact for compact K ⊆ W, and Dψ(z) injective for z ∈ V. As x ∈ W ∩ M = ψ(V), x = ψ(v₀) with v₀ ∈ V. By chart_tangent_space (with r = 2), T_{ψ(v)} = range Dψ(v) for every v ∈ V. In particular T_x = range Dψ(v₀) is a linear subspace and S_x = range Dψ(v₀) = T_x.

2. (Dν(x) maps S_x into S_x.) Let τ ∈ S_x = T_x, witnessed by a curve γ that is C¹ on (−1,1), maps (−1,1) into M, has γ(0) = x and γ'(0) = τ. By the chain rule, s ↦ ν(γ(s)) has derivative Dν(x)τ at 0.
 (a) Let Π^⊥ be the orthogonal projection onto A₀^⊥, a continuous linear map. For s ∈ (−1,1), ν(γ(s)) ∈ A₀ = (A₀^⊥)^⊥, so Π^⊥(ν(γ(s))) = 0 (Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal). Thus Π^⊥∘ν∘γ vanishes on a neighbourhood of 0; its derivative at 0, which by the chain rule is Π^⊥(Dν(x)τ), is therefore 0 (uniqueness of derivatives). Hence Dν(x)τ ∈ (A₀^⊥)^⊥ = A₀.
 (b) For s ∈ (−1,1), ν(γ(s))·ν(γ(s)) = |ν(γ(s))|² = 1. Differentiating at 0 (HasDerivAt.inner) gives n·Dν(x)τ + Dν(x)τ·n = 0, i.e. n·Dν(x)τ = 0.
 (c) By tangent_projection (first conjunct; its hypotheses hold with IsEmbeddedSubmanifold 1 m M), P_x(Dν(x)τ) = Π(Dν(x)τ) − (n·Dν(x)τ)n = Dν(x)τ, using (a) (Πw = w for w ∈ A₀) and (b). As P_x takes values in S_x, Dν(x)τ ∈ S_x.

3. (A function vanishing on V.) Fix a ∈ ℝ^m and define f_a(v) := ν(ψ(v))·(Dψ(v)a). For v ∈ V we have ψ(v) ∈ ψ(V) ⊆ M and Dψ(v)a ∈ range Dψ(v) = T_{ψ(v)} (step 1), so f_a(v) = 0 by the normality hypothesis at ψ(v). Since V is an open neighbourhood of v₀, f_a vanishes near v₀ and its derivative at v₀ is 0.

4. (Its derivative.) ψ is differentiable at v₀ and ν at ψ(v₀) = x, so v ↦ ν(ψ(v)) has derivative Dν(x)∘Dψ(v₀) at v₀ (chain rule). Since ψ is C² on the open set V, v ↦ Dψ(v) is C¹ on V (ContDiffOn.fderiv_of_isOpen), so it has derivative D²ψ(v₀) := fderiv ℝ (fderiv ℝ ψ) v₀ at v₀, and v ↦ Dψ(v)a has derivative b ↦ D²ψ(v₀)(b)(a) (HasFDerivAt.clm_apply). By the product rule for the inner product (HasFDerivAt.inner, fderivInnerCLM_apply) and step 3, for all b ∈ ℝ^m:
 (★) n·(D²ψ(v₀)(b)(a)) + (Dν(x)Dψ(v₀)b)·(Dψ(v₀)a) = 0.

5. (Schwarz.) ψ is C² on a neighbourhood of v₀, so its second derivative at v₀ is symmetric: D²ψ(v₀)(a)(b) = D²ψ(v₀)(b)(a) for all a, b (ContDiffAt.isSymmSndFDerivAt; over ℝ, minSmoothness ℝ 2 = 2).

6. (Symmetry.) Let τ, η ∈ S_x = range Dψ(v₀), say τ = Dψ(v₀)a and η = Dψ(v₀)b. Applying (★) to the pairs (a, b) and (b, a) and using step 5,
 (Dν(x)Dψ(v₀)b)·(Dψ(v₀)a) = −n·D²ψ(v₀)(b)(a) = −n·D²ψ(v₀)(a)(b) = (Dν(x)Dψ(v₀)a)·(Dψ(v₀)b).
 Hence η·Dν(x)τ = (Dν(x)τ)·η = (Dν(x)η)·τ = τ·Dν(x)η. Together with step 2 this proves the claim for every x ∈ M. ∎

## Key steps

1. Along a C¹ curve γ in M through x, ν∘γ stays in A₀ and on the unit sphere, so Dν(x)τ ∈ A₀ ∩ ν(x)^⊥; tangent_projection then gives P_x(Dν(x)τ) = Dν(x)τ ∈ span T_xM.
2. In a C² chart ψ with x = ψ(v₀), chart_tangent_space gives f_a(v) := ν(ψ(v))·Dψ(v)a ≡ 0 on V; differentiating at v₀: (Dν(x)Dψ(v₀)b)·Dψ(v₀)a = −ν(x)·D²ψ(v₀)(b)(a).
3. Symmetry of D²ψ(v₀) (Schwarz) makes (a,b) ↦ (Dν(x)Dψ(v₀)a)·Dψ(v₀)b symmetric, i.e. η·Dν(x)τ = τ·Dν(x)η on span T_xM = range Dψ(v₀).

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
