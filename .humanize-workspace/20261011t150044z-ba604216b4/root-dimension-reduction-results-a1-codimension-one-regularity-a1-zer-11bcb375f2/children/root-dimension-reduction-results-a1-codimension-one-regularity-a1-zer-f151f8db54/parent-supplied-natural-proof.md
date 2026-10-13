# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1.local_comparison-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1.local_comparison-a1.jacobian_continuous_on-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 5 of the supplied proof of local_comparison ("The map T ↦ √det(T*∘T) is continuous: the adjoint is an isometric linear equivalence, composition is continuous, and ContinuousLinearMap.continuous_det and Real.continuous_sqrt apply. So J is continuous at w₀"), stated for a general map F that is C¹ on D.

1. (DF is continuous on D.) F is C¹ on the open set D and 1 ≤ 1. So w ↦ DF(w) = fderiv ℝ F w is continuous on D as a map into the normed space of continuous linear maps ℝ^m → ℝ^P (ContDiffOn.continuousOn_fderiv_of_isOpen).

2. (Φ(T) := √det(T*∘T) is continuous on all continuous linear maps T : ℝ^m → ℝ^P.)
 (a) T ↦ T* is continuous: the adjoint ContinuousLinearMap.adjoint is a (conjugate-)linear isometric equivalence, hence continuous.
 (b) T ↦ T*∘T is continuous: composition of continuous linear maps is jointly continuous, and both factors depend continuously on T (Continuous.clm_comp with (a) and continuous_id).
 (c) det : (ℝ^m →L ℝ^m) → ℝ is continuous, as ℝ^m is finite dimensional (ContinuousLinearMap.continuous_det).
 (d) √ : ℝ → ℝ is continuous (Real.continuous_sqrt).
 Hence Φ = √ ∘ det ∘ (T ↦ T*∘T) is continuous.

3. (Composition.) The function w ↦ √det(DF(w)*∘DF(w)) equals Φ ∘ DF. A continuous map composed after a map continuous on D is continuous on D (Continuous.comp_continuousOn). So by steps 1 and 2 the function is continuous on D. This holds for all m, P ≥ 0. ∎

## Key steps

1. F is C¹ on the open set D, so DF is continuous on D.
2. T ↦ √det(T*∘T) is continuous: the adjoint is an isometric equivalence, composition is jointly continuous, det is continuous in finite dimensions, and √ is continuous.
3. Composing gives continuity of w ↦ √det(DF(w)*∘DF(w)) on D.

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
