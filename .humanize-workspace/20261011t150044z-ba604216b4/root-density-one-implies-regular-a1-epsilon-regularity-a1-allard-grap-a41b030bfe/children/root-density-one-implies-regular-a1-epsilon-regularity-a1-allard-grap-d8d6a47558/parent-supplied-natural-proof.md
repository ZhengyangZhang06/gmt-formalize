# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_height-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_height-a1.weight_ball-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 6.2 (second half) and Step 6.3 of the parent proof of dorag_tes_graph_affine_height. Step 6.2's second half is the weight bound Σ_i|Df(v)e_i|² ≤ n for 1-Lipschitz f, followed by lintegral_const_mul; Step 6.3 says the sphere is Lⁿ-null, so closed and open parameter balls give equal lower integrals. Together they formalize the area-formula comparison in Simon, Ch. 5, proof of Theorem 4.5, book/chapter-05.txt: the graph integral at lines 963–965 is compared with the parameter integral (19) at line 949, using Lip f ≤ 1 from (3) at line 795. Here they are stated for an arbitrary integrand G.
1. (Derivative bound.) The hypothesis says dist(f v, f w) ≤ 1·dist(v, w), so f is 1-Lipschitz (LipschitzWith.of_dist_le_mul). Hence ‖Df(v)‖ ≤ 1 for every v ∈ ℝⁿ (norm_fderiv_le_of_lipschitz). This holds also where f is not differentiable, since there Df(v) = 0.
2. (Sum bound.) For each i ∈ Fin n, |e_i| = 1, so |Df(v)e_i| ≤ ‖Df(v)‖·|e_i| = ‖Df(v)‖ ≤ 1 (ContinuousLinearMap.le_opNorm). Since 0 ≤ |Df(v)e_i| ≤ 1, we get |Df(v)e_i|² ≤ 1. Summing over the n indices gives Σ_{i∈Fin n}|Df(v)e_i|² ≤ n.
3. (Weight bound.) Since 2ⁿ ≥ 0, step 2 gives 1 + 2ⁿΣ_i|Df(v)e_i|² ≤ 1 + n·2ⁿ. ENNReal.ofReal is monotone, so ofReal(1 + 2ⁿΣ_i|Df(v)e_i|²) ≤ ofReal(1 + n·2ⁿ) for every v.
4. (Pull out the constant.) Multiplying step 3 by G(v) ≥ 0 and using pointwise monotonicity of the lower integral (lintegral_mono, no measurability needed): LHS ≤ ∫⁻_{B̄ⁿ_t(0)} ofReal(1 + n·2ⁿ)·G(v) dv. Since ofReal(1 + n·2ⁿ) ≠ ∞, lintegral_const_mul' turns this into ofReal(1 + n·2ⁿ)·∫⁻_{B̄ⁿ_t(0)} G(v) dv.
5. (Closed vs open ball.) Since n ≥ 1, Fin n is nonempty, so ℝⁿ is nontrivial. Lebesgue measure on ℝⁿ is an additive Haar measure, so every sphere sphere 0 t is null, for every t ∈ ℝ (Measure.addHaar_sphere).
 Also closedBall 0 t ∖ ball 0 t = sphere 0 t, and ball 0 t ∖ closedBall 0 t = ∅ because ball ⊆ closedBall. Hence closedBall 0 t = ball 0 t almost everywhere (ae_eq_set), and the lower integrals of G over the two sets coincide (setLIntegral_congr).
6. Combining steps 4 and 5: LHS ≤ ofReal(1 + n·2ⁿ)·∫⁻_{B̆ⁿ_t(0)} G(v) dv. ∎

## Key steps

1. f is 1-Lipschitz, so ‖Df(v)‖ ≤ 1 everywhere (norm_fderiv_le_of_lipschitz; Df = 0 off differentiability).
2. |Df(v)e_i| ≤ 1 for each i, so Σ_i|Df(v)e_i|² ≤ n and the weight is ≤ ofReal(1 + n·2ⁿ).
3. lintegral_mono, then lintegral_const_mul' (the constant is finite), pulls the constant out of the closed-ball integral.
4. For n ≥ 1 the sphere is Lebesgue-null (addHaar_sphere), so closedBall 0 t =ᵐ ball 0 t and the integrals agree (setLIntegral_congr).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); grep -n 'def IMRep.measure' -A2 <snapshot>/project/GMT/Ch07/Contract.lean`
- `rg -n 'notation.*μHE|μHE\[' <snapshot>/mathlib/Mathlib --glob '*.lean'`
- `rg -n 'support_mem_ae|measure_compl_support|compl_support' <snapshot>/mathlib/Mathlib/MeasureTheory --glob '*.lean'`
- `rg -n 'ball_ae_eq_closedBall|closedBall_ae_eq|ae_eq_closedBall|addHaar_sphere' <snapshot>/mathlib/Mathlib --glob '*.lean'`
- `rg -n 'norm_fderiv_le_of_lipschitz' <snapshot>/mathlib/Mathlib --glob '*.lean'`
- `rg -n 'starProjection_minimal|starProjection_apply_mem|sub_starProjection_mem_orthogonal|finrank_add_finrank_orthogonal|eq_of_le_of_finrank_eq|finrank_range_of_inj|finrank_euclideanSpace_fin|norm_add_sq_real' <snapshot>/mathlib/Mathlib`
- `rg -n 'lintegral_union_le|lintegral_mono_set|setLIntegral_const|lintegral_const_mul'|setLIntegral_congr|lintegral_mono_ae|restrict_restrict'|restrict_restrict_of_subset|restrict_mono|restrict_union_le|pow_le_pow_left₀|mul_le_mul_right' <snapshot>/mathlib/Mathlib`
- `python3 -I lean_name scan over workspaces/*/.humanize/github-theorem-prover/runs/*/dag.json (1924 names) plus rg 'dorag_tes_[A-Za-z0-9_]+' over this run's nodes/ and dag.json: no dorag_tes_gah_* reserved`
- `lean (v4.35.0-rc3, LEAN_PATH from /tmp/tes-v2/env.sh) on /tmp/gh-split/lean/Children.lean, Assembly.lean, Frame.lean, Small.lean, EndToEnd.lean, EndToEnd3.lean with #print axioms`
- `grep -n on book/chapter-05.txt for Theorem 4.5 and its proof (lines 747, 776, 789–797, 935–974)`
- `rg 'dorag_aa_height_bounds_of_net' over this run's nodes (no-split precedent for the support-conull argument)`

Files inspected:
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `GMT/Ch07/Submission.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/AddCircle.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-a41b030bfe/parent-child-handoff.json`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-609ef45196/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/gh-split/lean/Children.lean`
- `/tmp/gh-split/lean/Assembly.lean`
- `/tmp/gh-split/lean/Frame.lean`
- `/tmp/gh-split/lean/Small.lean`
- `/tmp/gh-split/lean/EndToEnd.lean`
- `/tmp/gh-split/lean/EndToEnd3.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace Submission.lean; there IMRep.measure = (μHE[n].restrict carrier).withDensity mult.

Nothing in the snapshot proves the selected node or any child, and no dorag_tes_gah_* name is reserved, so no declaration is reused.

The needed Mathlib infrastructure exists:
- Measure.support_mem_ae (hereditarily Lindelöf spaces);
- Measure.addHaar_sphere. There is no general ball/closedBall a.e. lemma; only AddCircle.closedBall_ae_eq_ball exists, so weight_ball uses ae_eq_set together with closedBall_diff_ball;
- norm_fderiv_le_of_lipschitz;
- Submodule.starProjection_minimal, starProjection_apply_mem, sub_starProjection_mem_orthogonal and finrank_add_finrank_orthogonal;
- Submodule.eq_of_le_of_finrank_eq and LinearMap.finrank_range_of_inj;
- restrict_withDensity, ae_withDensity_iff and withDensity_congr_ae;
- lintegral_union_le, lintegral_mono_set, lintegral_const_mul', setLIntegral_congr and setLIntegral_const;
- mul_le_mul_right, which is the ordered-monoid name in this Mathlib.

Lean results:
- The three child types elaborate in comparator scope.
- The exact frozen parent type is proved from them plus the frozen graph_area type (GHSplit.parent3).
- All three child types are themselves proved.
- Axioms throughout are propext, Classical.choice and Quot.sound; there is no sorryAx.

The book passage is Simon, Ch. 5, proof of Theorem 4.5, lines 960–970, with hypotheses (2)–(4) at lines 789–797. The no-split precedent in nodes/…609ef45196 justified folding the support-conull step back into the parent.
