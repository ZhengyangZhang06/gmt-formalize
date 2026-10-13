# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.lipschitz_smoothing-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.lipschitz_smoothing-a1.mollify_lipschitz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof (gradient bound: g'(x) − g'(x') = ∫ ψ(y)·(g(x − y) − g(x' − y)) dλ(y), |g(x − y) − g(x' − y)| ≤ K‖x − x'‖, ψ ≥ 0 and ∫ψ dλ = 1 give |g'(x) − g'(x')| ≤ K‖x − x'‖), stated for an arbitrary continuous, compactly supported, nonnegative kernel ψ of integral 1. This is the standard (folklore) fact that mollification does not increase Lipschitz constants (e.g. Lemma 17 of arXiv:2412.04899, for smoothing kernels as in its Definition 8: nonnegative, compactly supported, integral 1); the argument below is self-contained and uses only the stated hypotheses. Notation: λ = volume, Lebesgue measure on Euclid P; ∫ means ∫ … ∂λ; G(x) := ∫ ψ(y)·g(x − y) dλ(y) for x ∈ Euclid P.
1. (Integrability.) g is continuous, being Lipschitz (LipschitzWith.continuous). Fix x ∈ Euclid P. The map y ↦ x − y is continuous, so h_x(y) := ψ(y)·g(x − y) is continuous as a product of continuous functions. If h_x(y) ≠ 0 then ψ(y) ≠ 0, so support h_x ⊆ support ψ and h_x has compact support (HasCompactSupport.mul_right). Since λ is finite on compact sets, h_x is integrable (Continuous.integrable_of_hasCompactSupport). By the same lemma ψ itself is integrable, hence so is y ↦ ψ(y)·C for every constant C ∈ ℝ (Integrable.mul_const).
2. (Difference as one integral.) Fix x, x' ∈ Euclid P. Both h_x and h_{x'} are integrable by step 1, so by linearity of the integral (integral_sub) G(x) − G(x') = ∫ (ψ(y)·g(x − y) − ψ(y)·g(x' − y)) dλ(y).
3. (Pointwise bound.) For every y ∈ Euclid P: |ψ(y)·g(x − y) − ψ(y)·g(x' − y)| = |ψ(y)|·|g(x − y) − g(x' − y)| = ψ(y)·dist(g(x − y), g(x' − y)) (because ψ(y) ≥ 0) ≤ ψ(y)·(K·dist(x − y, x' − y)) (g is K-Lipschitz and ψ(y) ≥ 0) = ψ(y)·(K·dist(x, x')) (dist(x − y, x' − y) = dist(x, x'), dist_sub_right).
4. (Integration of the bound.) The majorant y ↦ ψ(y)·(K·dist(x, x')) is integrable by step 1, so by step 3 and norm_integral_le_of_norm_le, |G(x) − G(x')| = |∫ (ψ(y)·g(x − y) − ψ(y)·g(x' − y)) dλ(y)| ≤ ∫ ψ(y)·(K·dist(x, x')) dλ(y) = (∫ ψ dλ)·(K·dist(x, x')) = K·dist(x, x'), using integral_mul_const and ∫ ψ dλ = 1.
5. (Conclusion.) Hence dist(G(x), G(x')) = |G(x) − G(x')| ≤ K·dist(x, x') for all x, x' ∈ Euclid P, i.e. G = (fun x => ∫ y, ψ y * g (x - y)) is K-Lipschitz (LipschitzWith.of_dist_le_mul). ∎

## Key steps

1. For each x, y ↦ ψ(y)·g(x − y) is continuous with support inside support ψ, hence integrable; ψ and its constant multiples are integrable.
2. G(x) − G(x') = ∫ (ψ(y)·g(x − y) − ψ(y)·g(x' − y)) dλ(y) by integral_sub.
3. Pointwise |ψ(y)·g(x − y) − ψ(y)·g(x' − y)| ≤ ψ(y)·K·dist(x, x') since ψ ≥ 0, g is K-Lipschitz and dist(x − y, x' − y) = dist(x, x').
4. Integrating: |G(x) − G(x')| ≤ K·dist(x, x')·∫ψ dλ = K·dist(x, x'), so G is K-Lipschitz (LipschitzWith.of_dist_le_mul).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD = b4d606db1da5da8fa2c0292ad4924d97de8b3c4b`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `grep -n 'theorem\|lemma' local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean (normed_def, nonneg_normed, contDiff_normed, integral_normed, support_normed_eq, hasCompactSupport_normed)`
- `sed -n 1,150p local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean (normed_convolution_eq_right; dist_normed_convolution_le is a wrapper of dist_convolution_le)`
- `grep -n "theorem HasCompactSupport.contDiff_convolution_left\|theorem dist_convolution_le\|theorem convolution_eq_right'\|theorem convolution_def\|theorem convolution_eq_swap\|def ConvolutionExistsAt\|Lipschitz" local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean; sed -n 760,830p Analysis/Convolution.lean`
- `grep -rn 'theorem norm_fderiv_le_of_lipschitz' local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/*.lean (FDeriv/Basic.lean:947)`
- `lean GMT/Scratch/cmcs_lipschitz_smoothing_decomposition/Probe.lean after import GMT.Ch07.Submission. Unknown constant: #check ContDiffBump.normed, contDiff_normed, integral_normed, nonneg_normed, hasCompactSupport_normed, support_normed_eq, integrable_normed, continuous_normed, dist_normed_convolution_le, normed_convolution_eq_right. Found: ContDiffBump, hasContDiffBump_of_innerProductSpace, ContDiffBump.{support_eq,contDiff,nonneg,hasCompactSupport,continuous}, convolution_eq_right', dist_convolution_le, HasCompactSupport.contDiff_convolution_left, norm_fderiv_le_of_lipschitz, integral_pos_iff_support_of_nonneg, Continuous.integrable_of_hasCompactSupport, LipschitzWith.of_dist_le_mul, integral_sub, norm_integral_le_of_norm_le, and the instances HasContDiffBump, IsAddHaarMeasure, IsNegInvariant, IsAddLeftInvariant, BorelSpace, SecondCountableTopology, SFinite, IsOpenPosMeasure on Euclid P`
- `python3 -I scan of dag.json lean_name/lean_statement for ContDiffBump|mollif|convolution|normed|bump|smoothing and for LipschitzWith in lean_statement`
- `git show 376e5f48:GMT/Ch07/Submission.lean | sed -n 455,475p; git show 376e5f48 --stat`
- `grep -n 'def _existing_lean_name_problem' -A 40 and grep -n 'def _accepted_checkpoint' -A 5 /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py; grep -n -i import prompts.py (imports frozen)`
- `grep -rl cmcs_ls_mollify_lipschitz dag.json nodes/; for r in $(git for-each-ref --format='%(refname)'): git grep -q cmcs_ls_ $r -- '*.lean' (no match in 2987 refs)`
- `lean GMT/Scratch/cmcs_lipschitz_smoothing_decomposition/Assembly.lean (#print axioms: propext, Classical.choice, Quot.sound)`
- `python3 -I gen.py (verifier lean_contract.validate_lean_statement + gmt-compare.contract_scope replay of GMT.Ch07.main_theorem scope) -> Challenge.lean (3 types elaborate) and Solution.lean (exact Submission.X, standard axioms)`
- `lean Parse.lean with set_option pp.parens true (((∫ x, ψ x) = 1); LipschitzWith K fun x => ∫ y, ψ y * g (x - y); volume from measureSpaceOfInnerProductSpace)`
- `sed -n 1380,1410p book/chapter-06.txt`
- `independent reviewer: review/StubParent.lean, review/ImportClosure.lean, review/Fidelity.lean, review/InsertedSubmission.lean, review/SearchEnv.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-lipschitz-smoothing-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-786dd02ecc/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_lipschitz_smoothing_decomposition/Probe.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_lipschitz_smoothing_decomposition/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_lipschitz_smoothing_decomposition/Challenge.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_lipschitz_smoothing_decomposition/Solution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_lipschitz_smoothing_decomposition/Parse.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_lipschitz_smoothing_decomposition/children.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`

Snapshot facts:
- The manifest pins project b4d606db and Mathlib 25730c7c, and HEAD is b4d606db.
- The snapshot Ch07 contract is byte-identical to the workspace Submission.lean.
- The snapshot project has no smoothing or mollifier result to reuse.

What Mathlib has, and what is in scope:
- Snapshot Mathlib has the normalized-bump API that the supplied proof cites: BumpFunction/Normed.lean (normed, contDiff_normed, nonneg_normed, integral_normed, support_normed_eq, hasCompactSupport_normed) and BumpFunction/Convolution.lean (dist_normed_convolution_le, normed_convolution_eq_right).
- None of these modules is in the import closure of GMT.Ch07.Submission: every such name is an unknown constant after the frozen import, and imports are frozen.
- These are in scope: ContDiffBump with support_eq, contDiff, nonneg and hasCompactSupport; hasContDiffBump_of_innerProductSpace; HasCompactSupport.contDiff_convolution_left; convolution_def; convolution_eq_right'; the unnormalized dist_convolution_le (normed version is a one-line wrapper of it); norm_fderiv_le_of_lipschitz (FDeriv/Basic.lean:947); and the Haar-measure instances on Euclid P.

DAG findings:
- The DAG contains the accepted Submission.dgcr_stc_exists_normalized_mollifier (candidate 376e5f48). Its type is byte-identical to the one proposed here, and the runtime reuse rule permits sharing it.
- No Lipschitz-convolution lemma exists in Mathlib's import closure or in the DAG, so cmcs_ls_mollify_lipschitz is new. The name is unique across the DAG, the nodes/ tree and all git refs.

Lean checks:
- Both child types elaborate in the verifier's replayed contract scope.
- The new child is fully proved, and the frozen parent is proved from the two children, using only propext, Classical.choice and Quot.sound (Assembly.lean).
- An independent reviewer reproduced these results and returned ACCEPT.
