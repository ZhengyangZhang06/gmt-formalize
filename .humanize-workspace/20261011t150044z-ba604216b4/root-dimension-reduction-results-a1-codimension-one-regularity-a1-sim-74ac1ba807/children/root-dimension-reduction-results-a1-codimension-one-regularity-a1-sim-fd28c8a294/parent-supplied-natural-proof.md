# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1.energy_convergence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. The right-hand side of parent proof step 2 ('Dζ_k → d^Mζ in L²(H^m⌞M) for the seminorms |·|_{T_x} … Minkowski's inequality gives ∫_M|Dζ_k|²_{T_x} → ∫_M|∇^Mζ|²'), stated for a general measure. No dependencies.

Notation. a_k := Σ_jF_{k,j}², b := Σ_jG_j², d_k := Σ_j(F_{k,j} − G_j)². These are ≥ 0 and a.e.-strongly measurable (finite sums of products of a.e.-strongly measurable functions). Let δ_k := ∫⁻ ofReal(d_k) dμ, so δ_k → 0.

1. (Scalar inequalities.) For real x, y and ε > 0: x² ≤ (1 + ε)y² + (1 + 1/ε)(x − y)², since x² = y² + 2y(x − y) + (x − y)² and 2y(x − y) ≤ εy² + (x − y)²/ε (expand (εy − (x − y))² ≥ 0 and divide by ε). Summing over j: pointwise a_k ≤ (1 + ε)b + (1 + 1/ε)d_k and b ≤ (1 + ε)a_k + (1 + 1/ε)d_k. Also G_j² ≤ 2F_{k,j}² + 2(F_{k,j} − G_j)², so b ≤ 2a_k + 2d_k.

2. (Integrability.) Since δ_k → 0, δ_k < ∞ for all large k, and for such k the function d_k is integrable (a.e.-measurable with finite lintegral; hasFiniteIntegral_iff_ofReal). Fix one such k₀. Then 0 ≤ b ≤ 2a_{k₀} + 2d_{k₀}, an integrable function, and b is a.e.-strongly measurable, so b is integrable (Integrable.mono'). This is the first conclusion.

3. (∫d_k → 0.) For each k, ∫d_k dμ = (δ_k).toReal (integral_eq_lintegral_of_nonneg_ae), and toReal is continuous at 0, so ∫d_k dμ → 0.

4. (Convergence of the energies.) Let η > 0 and B := ∫b dμ ≥ 0. Put ε := min(1, η/(8(B + 1))), so 2εB ≤ η/4, and choose K such that for k ≥ K: δ_k < ∞ and 2(1 + 1/ε)∫d_k < η/4 (step 3). For k ≥ K, integrating the inequalities of step 1 (all functions involved are integrable) gives
 ∫a_k ≤ (1 + ε)B + (1 + 1/ε)∫d_k and B ≤ (1 + ε)∫a_k + (1 + 1/ε)∫d_k.
 From the first, ∫a_k − B ≤ εB + (1 + 1/ε)∫d_k < η. Inserting the first into the second and using ε ≤ 1 (so ε(1 + 1/ε) = ε + 1 ≤ 2 ≤ 1 + 1/ε),
 B − ∫a_k ≤ ε∫a_k + (1 + 1/ε)∫d_k ≤ ε(1 + ε)B + (ε(1 + 1/ε) + (1 + 1/ε))∫d_k ≤ 2εB + 2(1 + 1/ε)∫d_k < η.
 Hence |∫a_k − ∫b| < η for all k ≥ K, i.e. ∫Σ_jF_{k,j}² dμ → ∫Σ_jG_j² dμ. ∎

## Key steps

1. Pointwise: (x)² ≤ (1+ε)y² + (1+1/ε)(x−y)², summed over j, compares the energies a_k, b with the error d_k in both directions.
2. Finite ∫⁻ d_k for large k and b ≤ 2a_k + 2d_k give integrability of b; ∫d_k → 0.
3. Choosing ε small and then k large gives |∫a_k − ∫b| < η.

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
