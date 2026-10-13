# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1.local_comparison-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1.local_comparison-a1.graph_fderiv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 1–2 of the supplied proof of local_comparison, specialised to one point w₀ at which g is differentiable.

Notation. |·| is the Euclidean norm, B₀ := Dg(w₀) = fderiv ℝ g w₀, and ι, ι' are regarded as the continuous linear maps ι.toContinuousLinearMap, ι'.toContinuousLinearMap.

1. (Derivative.) A continuous linear map is its own Fréchet derivative at every point. So ι has derivative ι at w₀, and ι' has derivative ι' at g(w₀). Since g is differentiable at w₀, it has derivative B₀ there. By the chain rule (HasFDerivAt.comp), w ↦ ι'(g(w)) has derivative ι'∘B₀ at w₀. By the sum rule (HasFDerivAt.add), G = ι + ι'∘g has derivative ι + ι'∘B₀ at w₀. By uniqueness of the Fréchet derivative (HasFDerivAt.fderiv), fderiv ℝ G w₀ = ι + ι'∘B₀. This is the first assertion.

2. (Pythagoras.) Let h ∈ ℝ^m. By step 1, DG(w₀)h = ιh + ι'(B₀h). Expanding the squared norm of a sum in a real inner product space (norm_add_sq_real),
 |ιh + ι'(B₀h)|² = |ιh|² + 2⟨ιh, ι'(B₀h)⟩ + |ι'(B₀h)|².
 The middle term vanishes by the orthogonality hypothesis with v = h and w = B₀h. Since ι and ι' are isometries (LinearIsometry.norm_map), |ιh| = |h| and |ι'(B₀h)| = |B₀h|. Hence |DG(w₀)h|² = |h|² + |B₀h|².

3. (Conclusion.) Since |B₀h|² ≥ 0, step 2 gives |h|² ≤ |DG(w₀)h|². Both |h| and |DG(w₀)h| are nonnegative, and for nonnegative reals a, b, a² ≤ b² implies a ≤ b (pow_le_pow_iff_left₀ with exponent 2 ≠ 0). Therefore |h| ≤ |DG(w₀)h| for every h ∈ ℝ^m, which is the second assertion. The argument does not use any property of m or k, so it covers m = 0 and k = 0. ∎

## Key steps

1. Sum and chain rules for HasFDerivAt, with uniqueness of the derivative, give fderiv ℝ G w₀ = ι + ι'∘Dg(w₀).
2. norm_add_sq_real, orthogonality ⟨ιh, ι'(Dg(w₀)h)⟩ = 0 and the isometry property give |DG(w₀)h|² = |h|² + |Dg(w₀)h|².
3. Hence |h|² ≤ |DG(w₀)h|², and comparing nonnegative square roots gives |h| ≤ |DG(w₀)h|.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-11bcb375f2/parent-child-handoff.json and parent-supplied-plan.md`
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; cat lakefile.toml lean-toolchain`
- `python3 -I scan of dag.json: nodes with id prefix root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1 (status, lean_name, depends_on, lean_statement)`
- `python3 -I scan of dag.json: collisions for lean_names codim1_zsl_ga_lc_graph_fderiv, codim1_zsl_ga_lc_eps_choice, codim1_zsl_ga_lc_local_bilipschitz, codim1_zsl_ga_lc_jacobian_continuousOn, codim1_zsl_ga_lc_sandwich; lean_statements containing 'adjoint'+'ContinuousOn', '(1 + ε) ^', 'toContinuousLinearMap'+'fderiv', '(1 - ε) * ‖', 'ENNReal.ofReal t *'`
- `grep -n 'def check_source_delta' -A60 /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `git diff ecc53ec24a4257fbec663adb97bf513c2ccbefcb 24e3df5256a9a5aeb511fbc40fcae5062df412b2 -- GMT/Ch07/Submission.lean (leaf insertion position)`
- `rg -n "theorem ContinuousAt.eventually_lt|theorem ofReal_mul' |theorem setLIntegral_mono' |theorem setLIntegral_const |theorem norm_image_sub_le_of_norm_fderiv_le|theorem fderiv_fun_sub|theorem norm_add_sq_real" local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'continuous_det|continuousOn_fderiv_of_isOpen|pow_le_pow_iff_left₀|Ioo_mem_nhdsGT|theorem continuousAt_iff|theorem isOpen_iff|def adjoint|protected theorem fderiv|protected theorem HasFDerivAt.fderiv' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n "mul_le_mul_right'" local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order`
- `lake env lean /tmp/lc-dec-a1/LC.lean with '#count_heartbeats in' and 'set_option maxHeartbeats 100000/50000/25000 in' variants; LC_count_noarith.lean (final arithmetic replaced by sorry)`
- `lake env lean /tmp/lc-dec-a1/Split.lean ('#count_heartbeats in' for each child and the parent assembly)`
- `lake env lean /tmp/lc-dec-a1/SubmissionCheck.lean (#print axioms on a copy of GMT/Ch07/Submission.lean with the full chain inserted)`
- `sed -n 740,780p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-11bcb375f2/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-11bcb375f2/parent-supplied-plan.md`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Linear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/lc-dec-a1/LC.lean`
- `/tmp/lc-dec-a1/Split.lean`
- `/tmp/lc-dec-a1/SubmissionCheck.lean`

Pins. The snapshot manifest records project b4d606db and Mathlib 25730c7c, the same revisions as the workspace lakefile.

No reusable node. No DAG node has the type of any proposed child, and the five codim1_zsl_ga_lc_* names are unused. The related accepted nodes have different types:
- dgoj_graph_fderiv_left_inverse and dgcr_graph_orientation_jacobian: graphs z + ιv + ι'u(v) on ball 0 s;
- dimred_rpd_near_isometric_chart: submanifold charts;
- dimred_rpd_bilipschitz_image_measure: bi-Lipschitz relative to the identity.
So nothing can be reused by identical type.

Lemmas. Every lemma the children cite exists at the pin and inside the import closure of GMT.Ch07.Submission:
- ContinuousAt.eventually_lt (OrderClosed.lean:691)
- ENNReal.ofReal_mul' (Basic/ENNReal/Real.lean:301)
- setLIntegral_const / setLIntegral_mono' (Lebesgue/Basic.lean:121/254)
- norm_add_sq_real (InnerProductSpace/Basic.lean:411)
- Convex.norm_image_sub_le_of_norm_fderiv_le (MeanValue.lean:499)
- fderiv_fun_sub (FDeriv/Add.lean:680)
- HasFDerivAt.fderiv (FDeriv/Basic.lean:415)
- ContinuousLinearMap.fderiv (FDeriv/Linear.lean:79)
- ContDiffOn.continuousOn_fderiv_of_isOpen (ContDiff/Defs.lean:916)
- ContinuousLinearMap.continuous_det (Normed/Module/FiniteDimension.lean:175)
- ContinuousLinearMap.adjoint (Adjoint.lean:112)
- pow_le_pow_iff_left₀ (GroupWithZero/Basic.lean:681)
- Metric.isOpen_iff / Metric.continuousAt_iff (Pseudo/Defs.lean:833/871)

Renames at this pin. mul_le_mul_right' is absent, so use the pattern `gcongr ENNReal.ofReal ?_ * X`. ContinuousLinearMap.add_apply is deprecated in favour of add_apply.

Leaf rule. One theorem per leaf, with no helpers and no set_option. Leaf theorems go after the noncomputable section's `end`, inside namespace GMT.Ch07, as in commit 24e3df52.

Heartbeats. The monolithic proof uses 197,210 of 200,000; about 37k of that is its final arithmetic. In the split the children use 11,665, 4,450, 25,897, 15,793 and 1,736, and the parent assembly 28,232.

Axiom check. The full chain compiles in a copy of Submission.lean with axioms propext, Classical.choice and Quot.sound only.

Book. chapter-02.txt lines 743–776 give 3.1 and derive 3.2–3.3 'by an approximation argument based on the linear case 3.1'.
