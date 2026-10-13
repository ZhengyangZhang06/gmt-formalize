# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_area-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_area-a1.prod_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 7, the induction Π_{i≤m}(1 + λ_i) ≤ 1 + 2^{m−1}S_m, stated here with the constant 2^m. The larger constant makes the inequality valid for every m ≥ 0, including m = 0, where both sides equal 1. It is exactly the constant the parent needs: its Step 8 weakens 2^{n−1} to 2ⁿ anyway.

Notation: for m ∈ ℕ and λ : Fin m → ℝ put P(λ) := Π_i (1 + λ_i) and S(λ) := Σ_i λ_i. The empty product is 1 and the empty sum is 0.

1. We prove by induction on m the claim Q(m): for every λ : Fin m → ℝ with 0 ≤ λ_i ≤ 1 for all i, 1 ≤ P(λ) and P(λ) ≤ 1 + 2^m S(λ).
2. Base case m = 0. Here P(λ) = 1 and S(λ) = 0, so 1 ≤ 1 and 1 ≤ 1 + 2^0 · 0 = 1.
3. Induction step: setup. Assume Q(m) and let λ : Fin (m+1) → ℝ with 0 ≤ λ_i ≤ 1 for all i. Split off the last index (Fin.prod_univ_castSucc, Fin.sum_univ_castSucc): P(λ) = P'·(1 + μ) and S(λ) = S' + μ, where
   - λ' := (i ↦ λ_{castSucc i}) : Fin m → ℝ;
   - P' := P(λ') and S' := S(λ');
   - μ := λ_{last m}.
   The entries of λ' lie in [0, 1], so Q(m) gives 1 ≤ P' and P' ≤ 1 + 2^m S'. Moreover 0 ≤ μ ≤ 1, S' ≥ 0 (a sum of nonnegative terms), and 2^m ≥ 1.
4. Lower bound. P' ≥ 1 and 1 + μ ≥ 1, so P'(1 + μ) − 1 = (P' − 1)(1 + μ) + μ ≥ 0. Hence P(λ) ≥ 1.
5. Upper bound.
   - Since 1 + μ ≥ 0 and P' ≤ 1 + 2^m S': P'(1 + μ) ≤ (1 + 2^m S')(1 + μ) = 1 + 2^m S' + μ + μ·2^m S'.
   - Since 2^m S' ≥ 0 and μ ≤ 1: μ·2^m S' ≤ 2^m S'. Hence P(λ) ≤ 1 + 2·2^m S' + μ = 1 + 2^{m+1} S' + μ.
   - Since μ ≥ 0 and 2^{m+1} ≥ 1: μ ≤ 2^{m+1} μ. Hence P(λ) ≤ 1 + 2^{m+1}(S' + μ) = 1 + 2^{m+1} S(λ).
6. Steps 4 and 5 prove Q(m+1). By induction Q(m) holds for every m, which is the claim. ∎

## Key steps

1. Induction on m; for m = 0 the empty product is 1 and the empty sum is 0, so 1 ≤ 1 ≤ 1.
2. Split off the last index: P = P'(1+μ), S = S' + μ with μ ∈ [0,1], S' ≥ 0, and 1 ≤ P' ≤ 1 + 2^m S' by the induction hypothesis.
3. Lower bound: P'(1+μ) ≥ 1 because both factors are ≥ 1.
4. Upper bound: P'(1+μ) ≤ (1+2^m S')(1+μ) ≤ 1 + 2^{m+1}S' + μ ≤ 1 + 2^{m+1}(S'+μ), using μ ≤ 1, 2^m S' ≥ 0, μ ≥ 0 and 2^{m+1} ≥ 1.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `rg -n -i 'gram|normDet|areaJacobian|eigenvalue|det_id_add|prod_one_add' <snapshot>/project/GMT --glob '*.lean'`
- `rg -n 'det_eq_prod_eigenvalues|trace_eq_sum_eigenvalues|theorem.*eigenvalues_nonneg|eigenvalues_le|IsPositive.*eigenvalues' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem ext_inner_left|theorem ext_inner_right|theorem adjoint_inner_left|theorem adjoint_inner_right|theorem apply_eigenvectorBasis|theorem inner_map_map|theorem basisFun_apply|theorem toMatrix_apply |theorem det_toMatrix |theorem coe_toBasis ' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/ <snapshot>/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `grep -n 'theorem\|lemma\|def ' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `grep -n 'theorem\|lemma\|def ' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean; cat lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `lean (lean-4.35.0-rc3, workspace LEAN_PATH) on /tmp/ga-split/Avail.lean and /tmp/ga-split/Avail2.lean: #check of normDet, areaJacobianAt, weighted_area_formula_lipschitz_injOn, IsSymmetric.eigenvectorBasis, trace_eq_sum_inner, det_toMatrix after `import GMT.Ch07.Submission``
- `python3 -I lean_name scan over dag.json and nodes/*/decomposition-v*.json (639 names); grep -rl dorag_tes_ga_ over dag.json, nodes/, cluster-state; git grep -l dorag_tes_ga_ over all 1127 git refs  (no match)`
- `python3 -I /tmp/ga-split/scripts/gen.py (verifier/gmt-compare.py contract_scope + child_modules, verifier/lean_contract.py validate_lean_statement) -> /tmp/ga-split/chal/Challenge_{prod_bound,gram_identity,det_bound}.lean, compiled with lean`
- `lean on /tmp/ga-split/kids/Kids.lean, /tmp/ga-split/asm/Assembly.lean, /tmp/ga-split/full/P1.lean, /tmp/ga-split/sol/Sol.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Positive.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-27e8b1c734/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-af4665598c/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ga-split/chal/Challenge_prod_bound.lean`
- `/tmp/ga-split/chal/Challenge_gram_identity.lean`
- `/tmp/ga-split/chal/Challenge_det_bound.lean`
- `/tmp/ga-split/kids/Kids.lean`
- `/tmp/ga-split/asm/Assembly.lean`
- `/tmp/ga-split/full/P1.lean`
- `/tmp/ga-split/sol/Sol.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, so every check ran in the frozen compiler context.

No snapshot project declaration proves the selected theorem or any child. The project search only found GMT/Ch02's own areaJacobian contract, which Ch07 does not import, and a NormDet import in Ch03.

Mathlib supplies, all in scope after `import GMT.Ch07.Submission`:
- LinearMap.IsSymmetric.eigenvectorBasis and apply_eigenvectorBasis (Spectrum.lean:324);
- LinearMap.trace_eq_sum_inner (Trace.lean);
- LinearMap.det_toMatrix (Determinant.lean:206) and Matrix.det_diagonal;
- EuclideanSpace.basisFun_apply (PiL2.lean:806);
- ContinuousLinearMap.adjoint_inner_right (Adjoint.lean:125);
- LinearIsometry.inner_map_map and ext_inner_left (Basic.lean:324).

Not in scope after that import: LinearMap.normDet (NormDet.lean), and SimonGMT areaJacobianAt and weighted_area_formula_lipschitz_injOn (Chapter02/Area.lean, AreaLipschitz.lean:101). The children are therefore stated with `.det` of continuous linear maps; only the parent uses the area formula, through the new import.

Lean results:
- All three child types elaborate in the comparator scope.
- Complete child proofs compile with standard axioms only.
- The exact frozen parent type is proved from the children plus SimonGMT with [propext, Classical.choice, Quot.sound].

No reserved name collides with the three proposed names. The related doraggt_graph_map_gram_identity is not accepted and has a different type, so it is not reused.
