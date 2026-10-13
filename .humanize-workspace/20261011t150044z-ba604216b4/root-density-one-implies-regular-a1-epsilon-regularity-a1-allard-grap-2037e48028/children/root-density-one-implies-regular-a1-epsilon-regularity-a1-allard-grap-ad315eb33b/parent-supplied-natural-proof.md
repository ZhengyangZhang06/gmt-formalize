# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1.adapted_frame-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Provenance (orientation only, not a dependency): parent proof Step 0 (0.1–0.3), stated as a standalone lemma.
1. ι and ι' are injective, being linear isometries. Let V₁ := range ι and V₂ := range ι' (ranges of the underlying linear maps). By injectivity dim V₁ = n and dim V₂ = k (LinearMap.finrank_range_of_inj; finrank_euclideanSpace_fin).
2. V₁ = T. Every ιv lies in T, so V₁ ⊆ T, and dim V₁ = n = dim T. A subspace of a finite-dimensional space contained in another of the same dimension equals it (Submodule.eq_of_le_of_finrank_eq), so V₁ = T.
3. Proof of (c). Let w ∈ ℝᵏ. By Step 2 every element of T has the form ιv, and ⟨ιv, ι'w⟩ = 0 by hypothesis. Hence ι'w is orthogonal to T, i.e. ι'w ∈ T^⊥ (Submodule.mem_orthogonal).
4. V₂ = T^⊥. By (c), V₂ ⊆ T^⊥. Since dim T + dim T^⊥ = dim ℝ^{n+k} = n + k (Submodule.finrank_add_finrank_orthogonal) and dim T = n, dim T^⊥ = k = dim V₂. Hence V₂ = T^⊥ as in Step 2.
5. Decomposition. Let y ∈ ℝ^{n+k}. Then p_T y ∈ T = V₁ and y − p_T y ∈ T^⊥ = V₂ (Submodule.starProjection_apply_mem, Submodule.sub_starProjection_mem_orthogonal). So p_T y = ιu and y − p_T y = ι'w for some u ∈ ℝⁿ, w ∈ ℝᵏ, and y = p_T y + (y − p_T y) = ιu + ι'w.
6. For all u ∈ ℝⁿ and w ∈ ℝᵏ, linearity of P and the hypotheses give P(ιu + ι'w) = P(ιu) + P(ι'w) = u + 0 = u.
7. Proof of (a). Let u ∈ ℝⁿ and y ∈ ℝ^{n+k}. Write y = ιu₀ + ι'w as in Step 5. Then ⟨ιu, y⟩ = ⟨ιu, ιu₀⟩ + ⟨ιu, ι'w⟩ = ⟨u, u₀⟩ + 0, because ι preserves inner products (LinearIsometry.inner_map_map) and by the orthogonality hypothesis. By Step 6, Py = u₀, so ⟨u, Py⟩ = ⟨u, u₀⟩ = ⟨ιu, y⟩.
8. Proof of (b). Write y = ιu + ι'w. Since ιu ∈ T, p_T(ιu) = ιu (Submodule.starProjection_eq_self_iff). Since ι'w ∈ T^⊥ by (c), p_T(ι'w) = 0 (Submodule.starProjection_apply_eq_zero_iff). By linearity p_T y = ιu, and ι(Py) = ιu by Step 6.
9. Proof of (d). Put z := p_T y. Since z ∈ T and y − z ∈ T^⊥, ⟨z, y − z⟩ = 0 (Submodule.starProjection_inner_eq_zero and symmetry). Expanding |y|² = |z + (y − z)|² = |z|² + 2⟨z, y − z⟩ + |y − z|² (norm_add_sq_real) gives |y|² = |z|² + |y − z|². By (b), z = ι(Py), and ι is an isometry, so |z| = |Py|. Hence |y|² = |Py|² + |y − p_T y|².
10. Proof of (e). By (d), |Py|² ≤ |y|². Both norms are nonnegative, so |Py| ≤ |y| (pow_le_pow_iff_left₀ with exponent 2). ∎

## Key steps

1. Dimension count: range ι ⊆ T with equal dimension n, so range ι = T; hence ι'w ⊥ T, i.e. ι'w ∈ T^⊥ (c).
2. range ι' ⊆ T^⊥ with dim T^⊥ = (n + k) − n = k = dim range ι', so range ι' = T^⊥.
3. Every y decomposes as y = p_T y + (y − p_T y) = ιu + ι'w, and then Py = u.
4. (a) ⟨ιu, y⟩ = ⟨u, Py⟩ and (b) p_T y = ιPy follow from the decomposition.
5. (d) Pythagoras for y = p_T y + (y − p_T y) with |p_T y| = |ιPy| = |Py|; (e) follows from (d).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `rg -n -i 'firstVariation|tangentialDivergence|ContDiffBump|smulRight|starProjection|withDensity' <snapshot>/project/GMT --glob '*.lean'`
- `rg -n -i 'vertical|cutoff|graph plane|adapted frame' <snapshot>/project/GMT --glob '*.lean'  (no match)`
- `rg -n --fixed-strings over <snapshot>/mathlib/Mathlib for: integral_withDensity_eq_integral_toReal_smul; trace_smulRight; fderiv_smul_const; measure_compl_support; support_mem_ae; support_fderiv_subset; fderiv_of_notMem_tsupport; norm_fderiv_le_of_lipschitz; toDual_symm_apply; EuclideanSpace.inner_single_right; enorm_integral_le_lintegral_enorm; integral_inter_add_sdiff; lintegral_indicator_const; lintegral_const_mul'; lintegral_mono_set; setIntegral_eq_integral_of_forall_compl_eq_zero; setIntegral_congr_ae; norm_integral_le_of_norm_le; Measure.integrableOn_of_bounded; AEStronglyMeasurable.apply_continuousLinearMap; finrank_add_finrank_orthogonal; eq_of_le_of_finrank_eq; LinearMap.finrank_range_of_inj; starProjection_apply_mem; sub_starProjection_mem_orthogonal; starProjection_eq_self_iff; starProjection_apply_eq_zero_iff; starProjection_inner_eq_zero; norm_starProjection_apply_le; sum_inner_mul_inner; basisFun_apply; PiLp.norm_apply_le; one_of_mem_closedBall; tsupport_eq; tsupport_mul_subset_right; HasCompactSupport.mul_left; norm_image_sub_le_of_norm_fderiv_le`
- `grep -rl 'dorag_tes_gv_' over workspaces/gmt-ch0*/.humanize/github-theorem-prover/runs/*/dag.json, workspaces/gmt-ch0*/GMT, this run's nodes/ and git log -S  (no match)`
- `python3 -I scan of dag.json lean_statements for 'firstVariation (fun', 'smulRight', 'ContDiffBump' and firstVariation+fderiv  (no identical statement; dorag_lip_orthonormal_coordinates is a different existence statement, status rlcr-lean)`
- `python3 -I verifier/lean_contract.validate_lean_statement on the six child types  (all accepted unchanged)`
- `lean (lean-4.35.0-rc3, LEAN_PATH of the built workspace and lake-packages-25730c7c) on GMT/Scratch/dorag_tes_graph_first_variation_estimate/Full.lean with #print axioms parent, and on the six Challenge_<key>.lean comparator-format modules`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-2037e48028/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dorag_tes_graph_first_variation_estimate/Full.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dorag_tes_graph_first_variation_estimate/Challenge_frame.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dorag_tes_graph_first_variation_estimate/Challenge_graph_pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dorag_tes_graph_first_variation_estimate/Challenge_vertical_divergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dorag_tes_graph_first_variation_estimate/Challenge_cutoff_extension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dorag_tes_graph_first_variation_estimate/Challenge_vertical_bound.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dorag_tes_graph_first_variation_estimate/Challenge_split_estimate.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dorag_tes_graph_first_variation_estimate/README.md`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, so every child type was elaborated in the correct comparator scope.

Nothing in the snapshot proves the selected theorem or any child. GMT/Ch02 defines a different tangentialDivergence for C² submanifolds, and GMT/Ch05 has only unproved Prop contracts for a different varifold type; neither is reusable. No DAG node has an identical frozen type: the closest, dorag_lip_orthonormal_coordinates, is an existence statement and is not accepted. All six dorag_tes_gv_* names are unused.

Every Mathlib lemma the child proofs need exists at the pinned revision, at the cited paths. Examples: integral_withDensity_eq_integral_toReal_smul, LinearMap.trace_smulRight, fderiv_smul_const, Measure.support_mem_ae, fderiv_of_notMem_tsupport, ContDiffBump.one_of_mem_closedBall and tsupport_eq, OrthonormalBasis.sum_inner_mul_inner, integral_inter_add_sdiff, lintegral_const_mul', Measure.integrableOn_of_bounded, and Convex.norm_image_sub_le_of_norm_fderiv_le.

Lean results:
- Full.lean proves all six child types, each from at most its declared siblings, and then the exact frozen parent type. #print axioms parent = [propext, Classical.choice, Quot.sound, proj_algebra]: the sibling dorag_tes_projection_algebra type is the only assumption, with no sorryAx.
- All six comparator-format challenge modules elaborate.
