# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.box_inclusions-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.box_inclusions-a1.abs_arctan_sub_self-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Extracted from step 1(e) of the parent proof (the mean-value-theorem estimate |arctan z − z| ≤ ξ²|z| ≤ |z|³), stated for every real z.
1. If z = 0 then arctan 0 − 0 = 0 = |0|³, so the inequality holds. Assume z ≠ 0 from now on.
2. Define g : ℝ → ℝ by g(t) := arctan t − t. Since arctan is differentiable on ℝ with arctan′(t) = 1/(1 + t²), g is differentiable (in particular continuous) on ℝ with g′(t) = 1/(1 + t²) − 1, and g(0) = arctan 0 − 0 = 0.
3. For every ξ ∈ ℝ, 1/(1 + ξ²) − 1 = −ξ²/(1 + ξ²). Since 1 + ξ² ≥ 1, this gives |g′(ξ)| = ξ²/(1 + ξ²) ≤ ξ².
4. Let α := min(0, z) and β := max(0, z), so α < β. By the mean value theorem for g on [α, β] there is ξ ∈ (α, β) with g(β) − g(α) = g′(ξ)(β − α). If z > 0 this reads g(z) − g(0) = g′(ξ)·z; if z < 0 it reads g(0) − g(z) = g′(ξ)·(0 − z). In both cases, since g(0) = 0, arctan z − z = g(z) = g′(ξ)·z = (1/(1 + ξ²) − 1)·z = −ξ²z/(1 + ξ²).
5. Since ξ ∈ (α, β), ξ lies strictly between 0 and z, so |ξ| ≤ |z| and hence ξ² ≤ z².
6. Therefore |arctan z − z| = |g′(ξ)|·|z| ≤ ξ²|z| ≤ z²|z| = |z|³. ∎

## Key steps

1. If z = 0 both sides vanish.
2. g(t) := arctan t − t has g(0) = 0 and g′(t) = 1/(1 + t²) − 1 = −t²/(1 + t²), so |g′(t)| ≤ t².
3. The mean value theorem on [min(0, z), max(0, z)] gives arctan z − z = g′(ξ)·z for some ξ strictly between 0 and z.
4. |ξ| ≤ |z| gives |arctan z − z| ≤ ξ²|z| ≤ z²|z| = |z|³.

## Reference use

### local-project

Queries:
- `rg -n 'theorem .*arctan|lemma .*arctan' local-references/123e8435b4a2469b/mathlib/Mathlib | grep -iE 'le|lt|abs|sub|bound|self'`
- `rg -n 'arctan_le_self|arctan_lt_self|abs_arctan|le_arctan|arctan_le|self_le_arctan|arctan_sub|hasDerivAt_arctan|deriv_arctan|abs_sub_arctan|arctan.*x \^ 3|sub_arctan|lipschitz.*arctan|arctan.*Lipschitz' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'sub_starProjection|starProjection_eq_self_iff|norm_sq_eq_add_norm_sq_projection' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n -A3 'theorem norm_sq_eq_add_norm_sq_starProjection|theorem starProjection_orthogonal_val|norm_starProjection_apply_le|theorem norm_starProjection_le' local-references/123e8435b4a2469b/mathlib/Mathlib; rg -n -A6 'theorem norm_image_sub_le_of_norm_hasDerivWithin_le|theorem norm_image_sub_le_of_norm_deriv_le_segment' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n '^theorem exists_hasDerivAt_eq_slope|^theorem abs_real_inner_le_norm|^theorem real_inner_le_norm|^theorem norm_add_sq_real|^theorem real_inner_smul_left|^theorem real_inner_smul_right|^theorem real_inner_self_eq_norm_sq|^theorem real_inner_comm|^theorem pow_le_pow_left₀|^theorem starProjection_eq_self_iff|^theorem norm_starProjection_apply_le' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `python3 -I scan of dag.json: selected node (depth 5, status decomposing), depth histogram (200 nodes at depth 6), siblings under box_mass_limits-a1, lean_name substring search for idtp_cse_bml_rbi/arctan/norm_expansion/projection_residual (none)`
- `for n in idtp_cse_bml_rbi_abs_arctan_sub_self_le idtp_cse_bml_rbi_arctan_quotient_estimate idtp_cse_bml_rbi_norm_expansion idtp_cse_bml_rbi_projection_residual_le idtp_cse_bml_rbi: grep -c $n dag.json; grep -rl $n nodes/; rg -l $n local-references/123e8435b4a2469b/project; grep -rl --include=*.lean $n GMT (all 0)`
- `ls -d .swarm-worktrees/*/gmt-ch07/GMT | xargs -P 32 -I{} grep -rl --include=*.lean -e idtp_cse_bml_rbi -e abs_arctan_sub_self_le -e arctan_quotient_estimate {} (1463 worktrees, no match)`
- `grep -n -i 'arctan|tan^{-1}|Z(s|sector|square' book/chapter-07.txt; sed -n 405,560p book/chapter-07.txt`
- `lake env lean /tmp/rbi-decomp-x9f3/check/Stmts.lean (5 types elaborate, pp.explicit instance check); Children.lean (4 child proofs compile); Parent.lean (frozen parent from 3 children as axioms; #print axioms); Full.lean (#print axioms: propext, Classical.choice, Quot.sound only)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-240bfba243/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-240bfba243/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/ArctanDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/rbi-decomp-x9f3/check/Stmts.lean`
- `/tmp/rbi-decomp-x9f3/check/Children.lean`
- `/tmp/rbi-decomp-x9f3/check/Parent.lean`
- `/tmp/rbi-decomp-x9f3/check/Full.lean`
- `/tmp/rbi-decomp-x9f3/review/drafts.md`

The manifest pins project b4d606db and Mathlib 25730c7c; the workspace Submission.lean (identical to Contract.lean) is the compiler authority, and its dilation is -(lam⁻¹ • x) + dilationCLM P lam y.

The pinned Mathlib has only first-order arctan bounds: Real.arctan_lt_self, arctan_le_self, self_le_arctan and abs_arctan_le_abs in Analysis/SpecialFunctions/Trigonometric/Bounds.lean. It has no cubic or Taylor bound for arctan z − z, so abs_arctan_sub_self is a genuine missing obligation. Its proof uses Real.hasDerivAt_arctan (ArctanDeriv.lean) and exists_hasDerivAt_eq_slope (Calculus/Deriv/MeanValue.lean).

The norm and projection children use lemmas that all exist at the pin: norm_add_sq_real, abs_real_inner_le_norm, real_inner_le_norm, real_inner_smul_left/right, real_inner_self_eq_norm_sq, Submodule.starProjection_eq_self_iff, Submodule.starProjection_orthogonal_val and Submodule.norm_starProjection_apply_le.

No project, snapshot or DAG declaration covers any child. The 4 proposed names and the prefix idtp_cse_bml_rbi have no match in dag.json, nodes/, the snapshot project, workspace GMT, or 1463 ch07 swarm worktrees, so the names are unreserved.

The book (chapter-07.txt 405–560, proof of 7.3.3) prints no counterpart of this estimate, so the child proofs are extracted from the parent-supplied proof.

Kernel checks: all 5 types elaborate. Trial proofs of all 4 children compile. The frozen parent compiles from the three direct children as axioms. The full development depends only on propext, Classical.choice and Quot.sound.
