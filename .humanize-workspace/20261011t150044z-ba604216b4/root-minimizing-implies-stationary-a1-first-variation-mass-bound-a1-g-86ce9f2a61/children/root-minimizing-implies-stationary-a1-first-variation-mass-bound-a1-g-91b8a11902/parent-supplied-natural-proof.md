# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1.gram_jacobian_first_order-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1.gram_jacobian_first_order-a1.scalar_sqrt_exp_first_order-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 6–10 of the parent proof of fvmb_orthonormal_gram_sqrt_det_le_first_order: constants, square root of the exponential bound, size of σ, exponential expansion, error terms. Here the Gram determinant is replaced by an arbitrary real number g, and Σ_a τ_a·Bτ_a by an arbitrary real number D with |D| ≤ nA. Background: Simon Ch. 2, §5 (book/chapter-02.txt lines 1162–1256), the expansion J_t = 1 + t div_M X + O(t²) behind the first variation formula 5.3. Here only a one-sided first-order bound is needed.

√ is Real.sqrt, which is monotone on all of ℝ (Mathlib Real.sqrt_le_sqrt). Other useful Mathlib facts: Real.exp_add, Real.exp_pos, Real.sqrt_mul_self, Real.abs_exp_sub_one_sub_id_le, pow_le_pow_left₀, sq_abs.

1. Constants. Put c₀ := (n + 1)(A + 2 + (A + 1)²) and K := n(A + 1)²/2 + c₀².
- Since n ≥ 0 and A ≥ 0, n + 1 ≥ 1 > 0 and A + 2 + (A + 1)² ≥ 2 > 0, so c₀ > 0.
- Since n(A + 1)²/2 ≥ 0, K ≥ c₀² > 0.
- Put η := min(1, ε/(2n + 1)) and δ := min(1, min(1/c₀, ε/(2K))).
- Since 2n + 1 ≥ 1, ε/(2n + 1) > 0. Also 1/c₀ > 0 and ε/(2K) > 0. Hence 0 < η ≤ 1 and δ > 0.
2. Bound on nη. Since η ≤ ε/(2n + 1) and n ≥ 0, nη ≤ nε/(2n + 1). Also nε/(2n + 1) ≤ ε/2: multiplying by 2(2n + 1) > 0 turns this into 2nε ≤ (2n + 1)ε, i.e. 0 ≤ ε. Hence nη ≤ ε/2.
3. Fix real t, D, g with |t| < δ, |D| ≤ nA and g ≤ exp(2tD + 2nη|t| + n(A + 1)²t²). Since δ ≤ 1, δ ≤ 1/c₀ and δ ≤ ε/(2K), |t| < δ gives |t| ≤ 1, |t| ≤ 1/c₀ and |t| ≤ ε/(2K). Also t² = |t|·|t| ≤ |t|, because 0 ≤ |t| ≤ 1.
4. Square root. Put σ := tD + nη|t| + n(A + 1)²t²/2. Then 2tD + 2nη|t| + n(A + 1)²t² = σ + σ, so g ≤ exp(σ + σ) = exp(σ)·exp(σ). By monotonicity of √, and since √(x·x) = x for x = exp(σ) > 0, we get √g ≤ √(exp(σ)·exp(σ)) = exp(σ).
5. Size of σ. By the triangle inequality, |σ| ≤ |tD| + |nη|t|| + |n(A + 1)²t²/2|. Bound the three terms:
- |tD| = |t||D| ≤ |t|·nA.
- nη|t| ≥ 0, and nη|t| ≤ n·1·|t| = n|t| because 0 < η ≤ 1.
- n(A + 1)²t²/2 ≥ 0, and n(A + 1)²t²/2 ≤ n(A + 1)²t² ≤ n(A + 1)²|t| by t² ≤ |t|.
Hence |σ| ≤ |t|nA + n|t| + n(A + 1)²|t| = n(A + 1 + (A + 1)²)|t|. Since 0 ≤ n ≤ n + 1 and 0 ≤ A + 1 + (A + 1)² ≤ A + 2 + (A + 1)², we have n(A + 1 + (A + 1)²) ≤ c₀. Multiplying by |t| ≥ 0 gives |σ| ≤ c₀|t|.
6. Consequences. |σ| ≤ c₀|t| ≤ c₀·(1/c₀) = 1. Squaring 0 ≤ |σ| ≤ c₀|t| gives σ² = |σ|² ≤ c₀²|t|² = c₀²t².
7. Exponential expansion. For |σ| ≤ 1 one has |e^σ − 1 − σ| ≤ σ² (Mathlib Real.abs_exp_sub_one_sub_id_le). Hence e^σ ≤ 1 + σ + σ² ≤ 1 + tD + nη|t| + n(A + 1)²t²/2 + c₀²t² = 1 + tD + nη|t| + Kt².
8. Error terms.
- By step 2 and |t| ≥ 0, nη|t| ≤ (ε/2)|t|.
- Since 0 ≤ |t| ≤ ε/(2K) and K > 0, Kt² = (K|t|)·|t| ≤ (K·ε/(2K))·|t| = (ε/2)|t|.
9. Conclusion. By steps 4, 7 and 8, √g ≤ e^σ ≤ 1 + tD + (ε/2)|t| + (ε/2)|t| = 1 + tD + ε|t|. No step uses n > 0, so n = 0 is included (there |D| ≤ 0 forces D = 0). ∎

## Key steps

1. Choose c₀ = (n+1)(A+2+(A+1)²), K = n(A+1)²/2 + c₀², η = min(1, ε/(2n+1)), δ = min(1, min(1/c₀, ε/(2K))); then 0 < η ≤ 1, δ > 0 and nη ≤ ε/2.
2. With σ = tD + nη|t| + n(A+1)²t²/2 the hypothesis reads g ≤ exp(σ+σ) = exp(σ)·exp(σ), so √g ≤ exp σ.
3. |σ| ≤ n(A+1+(A+1)²)|t| ≤ c₀|t| ≤ 1, and σ² ≤ c₀²t².
4. exp σ ≤ 1 + σ + σ² ≤ 1 + tD + nη|t| + Kt² ≤ 1 + tD + (ε/2)|t| + (ε/2)|t| = 1 + tD + ε|t|.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `python3 -I: read nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1-g-86ce9f2a61/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `python3 -I: dag.json scan (509 nodes): selected node entry (depth 3, status decomposing, children []); siblings under first_variation_mass_bound-a1 incl. GE fvmb_gram_det_le_exp_sum_norm_sq_sub frozen type; lean_name collision check for fvmb_perturbed_frame_sum_norm_sq_sub_le and fvmb_sqrt_le_first_order_of_le_exp (0 hits); lean_names containing frame|sqrt|exp_first|first_order`
- `git log --all --oneline -S"fvmb_perturbed_frame_sum_norm_sq_sub_le" -- GMT/Ch07/Submission.lean; git log --all --oneline -S"fvmb_sqrt_le_first_order_of_le_exp" -- GMT/Ch07/Submission.lean (2557 refs, no hits)`
- `git show 2fd8f6f:GMT/Ch07/Submission.lean | sed -n 440,470p (accepted child theorems are declared as GMT.Ch07.Submission.X before main_theorem)`
- `rg -n 'Orthonormal ℝ' project; rg -l 'abs_exp_sub_one_sub_id_le|Real.sqrt \(Matrix.det|sum_norm_sq|norm_add_sq_real' project simongmt; rg -n '^(theorem|lemma|def) ' simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `grep -rn in mathlib/Mathlib: abs_exp_sub_one_sub_id_le, exp_le_exp, exp_add, exp_pos, sqrt_le_sqrt, sqrt_sq, sqrt_mul_self, abs_sum_le_sum_abs, real_inner_le_norm, abs_real_inner_le_norm, norm_add_sq_real, inner_add_right, real_inner_smul_right, le_opNorm, norm_smul_le, pow_le_pow_left₀; awk namespace scan of Analysis/Complex/Exponential.lean and Analysis/Real/Sqrt.lean`
- `sed -n 520,660p verifier/gmt-compare.py; grep -n 'CHILD_TARGET\s*=\|CHILD_MODULES\s*=\|AXIOMS\s*=' verifier/gmt-compare.py (contract_scope/child_modules replay, target HumanizeNodeComparator.target, permitted axioms)`
- `sed -n 1162,1175p and 1236,1256p book/chapter-02.txt (Simon Ch. 2 §5, 5.1–5.3)`
- `lake env lean /tmp/gjfo/Scope.lean (frozen parent and GE types elaborate in the replayed scope)`
- `lake env lean /tmp/gjfo/Children.lean (both child types elaborate)`
- `lake env lean /tmp/gjfo/Full.lean (both children proved; frozen parent type assembled from children + GE stub; #print axioms)`
- `lake env lean /tmp/gjfo/Replay.lean (comparator replay: exact Submission.X closes both child types and the parent type; rfl parse checks)`
- `independent reviewer agent: /tmp/gjfo_review/Insitu.lean (children inside Submission.lean noncomputable section + generated NodeSolution text), replay.out, scripts/numcheck.py, scripts/validate.py, scripts/parent_check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1-g-86ce9f2a61/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1-g-86ce9f2a61/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1-g-86ce9f2a61/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/gjfo/Scope.lean`
- `/tmp/gjfo/Children.lean`
- `/tmp/gjfo/Full.lean`
- `/tmp/gjfo/Replay.lean`
- `/tmp/gjfo/proposal.md`
- `/tmp/gjfo_review/Insitu.lean`
- `/tmp/gjfo_review/replay.out`

Neither child statement exists in the pinned snapshot (project b4d606d, Mathlib 25730c7c) or in the DAG; both are new. Their lean_names collide with nothing among the 509 DAG nodes or in the GMT/Ch07/Submission.lean history of 2557 refs. The snapshot Contract.lean is byte-identical to the workspace contract, and the workspace Submission.lean equals it.

Nothing in SimonGMT can be reused. Chapter04/FirstVariation.lean defines firstVariation through tangentialDivergence but has no Jacobian or Gram first-order lemma. The rg hits in Chapter04/CompactConvexHull.lean and Chapter05/Basic.lean are unrelated uses.

Every Mathlib fact cited in the child proofs exists in the snapshot:
- Analysis/Complex/Exponential.lean: Real.abs_exp_sub_one_sub_id_le (:537), Real.exp_le_exp (:316), Real.exp_add (:211), Real.exp_pos (:283).
- Analysis/Real/Sqrt.lean: Real.sqrt_le_sqrt (:208), Real.sqrt_mul_self (:152), Real.sqrt_sq (:180).
- Analysis/InnerProductSpace/Basic.lean: norm_add_sq_real (:411), abs_real_inner_le_norm (:471), real_inner_le_norm (:475), real_inner_smul_right (:120), inner_add_right (:77).
- Analysis/Normed/Operator/Basic.lean: ContinuousLinearMap.le_opNorm (:234).
- Algebra/Order/BigOperators/Group/Finset.lean: Finset.abs_sum_le_sum_abs (:371).
- Algebra/Order/GroupWithZero/Basic.lean: pow_le_pow_left₀ (:513).

Simon Ch. 2 §5 (book/chapter-02.txt lines 1162–1256) gives the C² Taylor expansion J_t = 1 + t div_M X + O(t²) behind 5.3. The children carry the supplied proof's one-sided, first-order version.

The comparator replay of verifier/gmt-compare.py (contract_scope/child_modules, target _root_.HumanizeNodeComparator.target, exact Submission.X) is reproduced in /tmp/gjfo/Replay.lean. Both child types elaborate and are proved with only propext, Classical.choice and Quot.sound. The frozen parent type is proved from the two children plus the sibling GE fvmb_gram_det_le_exp_sum_norm_sq_sub, stubbed with its frozen DAG type; GE is the only extra axiom. The independent reviewer reproduced all of this and accepted.
