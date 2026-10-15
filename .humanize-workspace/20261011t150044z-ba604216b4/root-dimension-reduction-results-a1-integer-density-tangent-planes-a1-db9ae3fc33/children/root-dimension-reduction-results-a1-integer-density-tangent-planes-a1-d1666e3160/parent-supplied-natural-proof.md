# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.test_function-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.test_function-a1.indicator_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5, 6 and 7 of the parent proof (compact support, local form and C¹ regularity of g), stated for an arbitrary open set U, compact K ⊆ U and function h.
Notation: g := U.indicator h, so g(y) = h(y) for y ∈ U (Set.indicator_of_mem) and g(y) = 0 for y ∉ U (Set.indicator_of_notMem).
1. (Support.) support g ⊆ K. Let g(y) ≠ 0. If y ∉ U then g(y) = 0, a contradiction; so y ∈ U and h(y) = g(y) ≠ 0, hence y ∈ K by hypothesis.
2. (Topological support.) K is compact in the Hausdorff space ℝ^P, hence closed (IsCompact.isClosed). So tsupport g = closure(support g) ⊆ K by step 1 (closure_minimal).
3. (Compact support.) Every y ∉ K has g(y) = 0 by step 1. Since K is compact, g has compact support (HasCompactSupport.intro).
4. (Points of U.) Let x ∈ U. Since U is open, U ∈ 𝓝 x (IsOpen.mem_nhds), and g = h on U, so g =ᶠ[𝓝 x] h. Hence g is C¹ at x because h is (ContDiffAt.congr_of_eventuallyEq), and Dg(x) = Dh(x) (Filter.EventuallyEq.fderiv_eq). This is the third conclusion.
5. (Points off U.) Let x ∉ U. Since K ⊆ U, x ∉ K, so x ∉ tsupport g by step 2. Hence g = 0 on a neighbourhood of x (notMem_tsupport_iff_eventuallyEq). The constant function 0 is C¹ (contDiffAt_const), so g is C¹ at x (ContDiffAt.congr_of_eventuallyEq), and Dg(x) = D0(x) = 0 (Filter.EventuallyEq.fderiv_eq, fderiv_const_apply). This is the fourth conclusion.
6. (Global C¹.) By steps 4 and 5, g is C¹ at every point of ℝ^P, hence ContDiff ℝ 1 g (contDiff_iff_contDiffAt). With step 3, all four conclusions hold. ∎

## Key steps

1. g(y) ≠ 0 forces y ∈ U and h(y) ≠ 0, so support g ⊆ K; K is compact, hence closed, so tsupport g ⊆ K.
2. g vanishes off the compact set K, so HasCompactSupport g.
3. For x ∈ U, U is a neighbourhood of x on which g = h; so g is C¹ at x and Dg(x) = Dh(x).
4. For x ∉ U, x ∉ K ⊇ tsupport g, so g = 0 near x; so g is C¹ at x and Dg(x) = 0.
5. C¹ at every point gives ContDiff ℝ 1 g.

## Reference use

### local-project

Queries:
- `python3 scan of dag.json: nodes with id prefix root...rotation_conservation-a1 (status, depth, lean_name, depends_on, lean_statement); depth/status counts (depth-6 nodes exist, so depth 5 may split)`
- `python3 regex scan of dag.json lean_statements for 'fderiv ℝ \(fun [a-z] : Euclid P => ‖[a-z]‖\)', 'fderiv ℝ norm', 'HasCompactSupport', 'Real.arctan' (no reusable norm-derivative or extension-by-zero lemma)`
- `grep -c idtp_cse_rc_tf_support_bound|idtp_cse_rc_tf_indicator_extension|idtp_cse_rc_tf_product_fderiv|idtp_cse_rc_tf_ dag.json issue-workers.json; rg -l idtp_cse_rc_tf nodes/ GMT/ local-references/123e8435b4a2469b/project; rg -l --glob '*.lean' idtp_cse_rc_tf .swarm-worktrees/*/gmt-ch07/GMT/Ch07 (all no match)`
- `grep -rn 'theorem hasStrictFDerivAt_norm\b|theorem fderiv_norm\b|theorem HasFDerivAt.norm\b|theorem DifferentiableAt.norm\b|theorem hasFDerivAt_norm_rpow|theorem fderiv_norm_sq' Mathlib (no plain norm-derivative lemma; hasStrictFDerivAt_norm_sq, DifferentiableAt.norm, contDiffAt_norm exist)`
- `rg -n 'theorem (starProjection_orthogonal_val|norm_sq_eq_add_norm_sq_starProjection|hasStrictFDerivAt_norm_sq|HasFDerivAt.pow|HasFDerivAt.mul|HasDerivAt.comp_hasFDerivAt|Filter.EventuallyEq.fderiv_eq|ContDiffAt.congr_of_eventuallyEq|contDiff_iff_contDiffAt|fderiv_const_apply|support_deriv_subset|arctan_one|arctan_neg|IsCompact.inter_left|contDiffAt_norm|contDiffAt_const|ContDiffAt.differentiableAt|ContDiff.differentiable) ' in the snapshot mathlib`
- `rg -n 'theorem (two_le_pi|arctan_strictMono)|notMem_mulTSupport_iff_eventuallyEq' in the snapshot mathlib Trigonometric and Topology/Algebra/Support.lean`
- `cmp of 14 cited Mathlib files between local-references/123e8435b4a2469b/mathlib and .lake/packages/mathlib (all identical); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean GMT/Ch07/Submission.lean (identical)`
- `lake env lean /tmp/tf_decomp/Stmts.lean (parent, cone_cutoff, angle_fderiv and the 3 child types elaborate)`
- `lake env lean /tmp/tf_decomp/Full.lean (childA/B/C proved; parent_from_children proves the exact parent type from the 3 children + cone_cutoff/angle_fderiv types; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/tf_decomp/Named.lean (exact Submission.idtp_cse_rc_tf_* names and frozen types: standard axioms; Submission.idtp_cse_rc_test_function proved from them, sorry only via the two scratch sibling stand-ins; 0 errors)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-db9ae3fc33/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-db9ae3fc33/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormPow.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean`
- `/tmp/tf_decomp/Stmts.lean`
- `/tmp/tf_decomp/Full.lean`
- `/tmp/tf_decomp/Named.lean`
- `/tmp/tf_decomp/gen/children.json`
- `/tmp/tf_decomp/gen/proposal_children.json`

The frozen GMT.Ch07 contract (snapshot project Submission.lean, identical to the workspace copy) is the compiler authority at mathlib 25730c7c. All 14 cited snapshot Mathlib files are byte-identical to .lake/packages/mathlib. The DAG has no reusable lemma for the norm derivative in orthogonal directions or for extension by zero, so these become the generic children product_fderiv and indicator_extension. Mathlib at this pin has no plain norm-derivative lemma, so child 3 derives DN(x)v = 0 from hasStrictFDerivAt_norm_sq, HasFDerivAt.pow and HasFDerivAt.unique. Every lemma cited in the child proofs exists at this pin: Submodule.{norm_sq_eq_add_norm_sq_starProjection, starProjection_orthogonal_val}, Real.{two_le_pi, arctan_strictMono, arctan_one, arctan_neg}, contDiffAt_norm, HasDerivAt.comp_hasFDerivAt, HasFDerivAt.{fun_mul, pow, unique, fderiv}, Filter.EventuallyEq.fderiv_eq, ContDiffAt.congr_of_eventuallyEq, contDiffAt_const, fderiv_const_apply, contDiff_iff_contDiffAt, HasCompactSupport.intro, notMem_tsupport_iff_eventuallyEq, support_deriv_subset, IsCompact.inter_left. The proposed names idtp_cse_rc_tf_{support_bound, indicator_extension, product_fderiv} appear nowhere in dag.json, issue-workers.json, node artifacts, the project or the 4216 swarm worktrees. All three child types elaborate and were kernel-checked under their exact names with propext, Classical.choice and Quot.sound only. The exact frozen parent type follows from them plus the frozen types of idtp_cse_rc_cone_cutoff and idtp_cse_rc_angle_fderiv, with standard axioms only. An independent reviewer reproduced these checks and returned ACCEPT.
