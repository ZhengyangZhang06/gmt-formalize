# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1.split_integral_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Provenance (orientation only, not a dependency): parent proof Steps 5.4 and 6 (splitting B_r(ξ) into Φ(D) and its complement, and the conversion to [0, ∞]), stated for abstract integrands.
1. If g is not μ-integrable on A, then ∫_A g dμ = 0 by the Bochner convention (integral_undef), and the left side is ofReal 0 = 0 ≤ the right side. Assume from now on that g is μ-integrable on A.
2. Splitting. u is integrable on A and on B ∖ A, since both are subsets of B. Since A is measurable and B ∩ A = A, ∫_B u = ∫_A u + ∫_{B∖A} u (integral_inter_add_sdiff). Since u and g are integrable on A, ∫_A (u − g) = ∫_A u − ∫_A g (integral_sub). Hence ∫_A g = ∫_B u − ∫_{B∖A} u − ∫_A (u − g).
3. Triangle inequality. |∫_A g| ≤ |∫_B u| + |∫_{B∖A} u| + |∫_A (u − g)|. ENNReal.ofReal is monotone and subadditive (ENNReal.ofReal_add_le), so ofReal|∫_A g| ≤ ofReal|∫_B u| + ofReal|∫_{B∖A} u| + ofReal|∫_A (u − g)|.
4. Off A. ofReal|∫_{B∖A} u| ≤ ∫⁻_{B∖A} ofReal|u| dμ (enorm_integral_le_lintegral_enorm, with ‖y‖ₑ = ofReal|y| for real y). For μ-a.e. x ∈ B ∖ A (B ∖ A is measurable, ae_restrict_iff'): if x ∈ F then u(x) = 0, so ofReal|u(x)| = 0; if x ∉ F then ofReal|u(x)| ≤ ofReal G. Thus ofReal|u| ≤ ofReal(G)·1_{X∖F} μ-a.e. on B ∖ A. Since F is measurable, ∫⁻_{B∖A} ofReal(G)·1_{X∖F} dμ = ofReal(G)·μ((X ∖ F) ∩ (B ∖ A)) (lintegral_indicator_const, Measure.restrict_apply). This is ≤ ofReal(G)·μ(B ∖ F) because (X ∖ F) ∩ (B ∖ A) ⊆ B ∖ F.
5. On A. Similarly ofReal|∫_A (u − g)| ≤ ∫⁻_A ofReal|u − g| dμ. For μ-a.e. x ∈ A, ofReal|u(x) − g(x)| ≤ ofReal(G·t(x)) = ofReal(G)·ofReal(t(x)), using G ≥ 0. Since ofReal G ≠ ∞, ∫⁻_A ofReal(G)·ofReal(t) dμ = ofReal(G)·∫⁻_A ofReal(t) dμ (lintegral_const_mul', which needs no measurability). Finally ∫⁻_A ofReal(t) ≤ ∫⁻_B ofReal(t) because A ⊆ B (lintegral_mono_set). Hence ofReal|∫_A (u − g)| ≤ ofReal(G)·∫⁻_B ofReal(t) dμ.
6. Conclusion. Combine Steps 3–5 with the hypothesis ofReal|∫_B u| ≤ C: ofReal|∫_A g| ≤ C + ofReal(G)·μ(B ∖ F) + ofReal(G)·∫⁻_B ofReal(t) dμ. Rearranging in the commutative semiring [0, ∞] gives ofReal(G)·(∫⁻_B ofReal(t) dμ + μ(B ∖ F)) + C. ∎

## Key steps

1. If g is not integrable on A the left side is 0. Otherwise ∫_A g = ∫_B u − ∫_{B∖A} u − ∫_A (u − g).
2. Triangle inequality and subadditivity of ENNReal.ofReal.
3. ofReal|∫_{B∖A} u| ≤ ∫⁻_{B∖A} ofReal(G)·1_{X∖F} ≤ ofReal(G)·μ(B ∖ F), since |u| ≤ G on B and u = 0 on (B ∖ A) ∩ F.
4. ofReal|∫_A (u − g)| ≤ ofReal(G)·∫⁻_A ofReal(t) ≤ ofReal(G)·∫⁻_B ofReal(t).
5. Add the three bounds, using the hypothesis ofReal|∫_B u| ≤ C.

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
