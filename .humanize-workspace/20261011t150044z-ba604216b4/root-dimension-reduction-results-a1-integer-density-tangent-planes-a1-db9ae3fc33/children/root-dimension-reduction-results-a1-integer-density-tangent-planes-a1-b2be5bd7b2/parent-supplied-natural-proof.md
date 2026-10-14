# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.test_function-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.test_function-a1.support_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3 and 4 of the parent proof (the arctan bound and the support bound), stated for one point y; the identity |πy|² = ⟨y,a⟩² + ⟨y,e⟩² is a hypothesis of this statement.
Notation: α := ⟨y,a⟩ > 0, β := ⟨y,e⟩, t := β/α, q := y − πy.
1. (π/4 exceeds s.) Since π ≥ 2 (Real.two_le_pi), π/4 ≥ 1/2 > 1/4 ≥ s. The hypothesis |arctan t| < s therefore gives −π/4 < −s < arctan t < s < π/4.
2. (|t| < 1.) arctan is strictly increasing, hence monotone (Real.arctan_strictMono), arctan 1 = π/4 (Real.arctan_one), and arctan(−1) = −arctan 1 = −π/4 (Real.arctan_neg). If t ≥ 1 then arctan t ≥ arctan 1 = π/4, contradicting step 1; so t < 1. If t ≤ −1 then arctan t ≤ arctan(−1) = −π/4, contradicting step 1; so t > −1.
3. (β² < α².) Since α > 0, the inequalities −1 < β/α < 1 are equivalent to −α < β < α (div_lt_one, lt_div_iff₀). Hence α − β > 0 and α + β > 0, so α² − β² = (α − β)(α + β) > 0, i.e. β² < α².
4. (Pythagoras.) |y|² = |πy|² + |q|². Indeed Submodule.norm_sq_eq_add_norm_sq_starProjection gives |y|² = |πy|² + |Qᗮ.starProjection y|², and Qᗮ.starProjection y = y − πy = q (Submodule.starProjection_orthogonal_val).
5. (Bounds on |y|.) ||y| − 1| < s means 1 − s < |y| < 1 + s. With s ≤ 1/4 this gives |y| > 3/4, hence |y|² > 9/16, and |y| < 5/4. The latter is the second conclusion.
6. (Lower bound for |πy|².) From 0 ≤ |q| < s|y|, squaring gives |q|² < (s|y|)² = s²|y|² (pow_lt_pow_left₀). From 0 < s ≤ 1/4, s² ≤ 1/16, so 1 − s² ≥ 15/16. By step 4, |πy|² = |y|² − |q|² > (1 − s²)|y|² ≥ (15/16)|y|² > (15/16)(9/16) = 135/256, using |y|² ≥ 0 and step 5.
7. (First conclusion.) By hypothesis and step 3, |πy|² = α² + β² < 2α². With step 6, 2α² > 135/256, so α² > 135/512 > 128/512 = 1/4 = (1/2)². Since α > 0 and 1/2 > 0, this gives α > 1/2 (pow_lt_pow_iff_left₀). With step 5, 1/2 < ⟨y,a⟩ and |y| < 5/4. ∎

## Key steps

1. s ≤ 1/4 < π/4, and arctan is strictly increasing with arctan(±1) = ±π/4, so |arctan(β/α)| < s forces −1 < β/α < 1.
2. Multiplying by α = ⟨y,a⟩ > 0 gives |β| < α, hence ⟨y,e⟩² < ⟨y,a⟩².
3. Pythagoras: |y|² = |πy|² + |y − πy|², via norm_sq_eq_add_norm_sq_starProjection and starProjection_orthogonal_val.
4. ||y| − 1| < s ≤ 1/4 gives 3/4 < |y| < 5/4; |y − πy| < s|y| with s² ≤ 1/16 gives |πy|² > (15/16)|y|² > 135/256.
5. |πy|² = ⟨y,a⟩² + ⟨y,e⟩² < 2⟨y,a⟩², so ⟨y,a⟩² > 135/512 > 1/4, and ⟨y,a⟩ > 0 gives ⟨y,a⟩ > 1/2.

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
