# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.interior_bound-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.interior_bound-a1.contraction_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4–8 of the supplied proof of the selected parent dph_sh_covectorEuclideanNorm_interior_le (the bound for the contraction γ_w := γ(w, ·) inside fact (F8) of dph_smooth_homotopy), extracted with all details filled in. The contraction is represented by an arbitrary k-covector δ with δ(u) = γ(Fin.cons w u), so the statement does not fix a construction such as ContinuousAlternatingMap.curryLeft. Sibling used: tuple_sum_factorial (iwl_sp_pn_sum_sq_tuples_eq_factorial_mul).

Notation: for an n-covector α on ℝ^p, |α| := covectorEuclideanNorm α = √(Σ_{I : Fin n → Fin p strictly increasing} α(e∘I)²), where e_b := EuclideanSpace.basisFun (Fin p) ℝ b is the standard basis of ℝ^p and e∘I := (i ↦ e_{I(i)}). For w ∈ ℝ^p, w_b is its b-th coordinate. Fix p, k, γ, w and δ as in the statement, so δ(u) = γ(Fin.cons w u) for every u : Fin k → ℝ^p.

1. (Expansion in the first slot.) w = Σ_b w_b·e_b (OrthonormalBasis.sum_repr for EuclideanSpace.basisFun, whose coordinates are the w_b by EuclideanSpace.basisFun_repr). For fixed u : Fin k → ℝ^p, the map x ↦ γ(Fin.cons x u) is linear in x. Indeed it is x ↦ (γ.curryLeft x)(u): ContinuousAlternatingMap.curryLeft γ is a continuous linear map, and (γ.curryLeft x)(u) = γ(Matrix.vecCons x u) = γ(Fin.cons x u) (ContinuousAlternatingMap.curryLeft_apply_apply; Matrix.vecCons is Fin.cons). Equivalently, γ is linear in its first argument (ContinuousAlternatingMap.cons_add, cons_smul). With the hypothesis on δ this gives, for every u,
   δ(u) = γ(Fin.cons w u) = Σ_b w_b·γ(Fin.cons e_b u).
2. (Basis tuples.) For b ∈ Fin p and J : Fin k → Fin p, Fin.cons e_b (e∘J) = e∘(Fin.cons b J) as maps Fin (k+1) → ℝ^p. At the entry 0 both sides equal e_b (Fin.cons_zero). At an entry i.succ both sides equal e_{J(i)} (Fin.cons_succ). Every entry has one of these two forms (Fin.cases). Step 1 with u := e∘J therefore gives δ(e∘J) = Σ_b w_b·γ(e∘(Fin.cons b J)).
3. (Cauchy–Schwarz.) Fix J : Fin k → Fin p. By step 2 and the Cauchy–Schwarz inequality for finite sums (Finset.sum_mul_sq_le_sq_mul_sq):
   δ(e∘J)² = (Σ_b w_b·γ(e∘(Fin.cons b J)))² ≤ (Σ_b w_b²)·Σ_b γ(e∘(Fin.cons b J))² = ‖w‖²·Σ_b γ(e∘(Fin.cons b J))²,
   using ‖w‖² = Σ_b w_b² (EuclideanSpace.real_norm_sq_eq).
4. (Reindexing.) The map (b, J) ↦ Fin.cons b J is a bijection Fin p × (Fin k → Fin p) → (Fin (k+1) → Fin p) (Fin.consEquiv (fun _ => Fin p)). Exchange the two finite sums (Finset.sum_comm), combine them into one sum over pairs (Fintype.sum_prod_type') and reindex along this bijection (Fintype.sum_equiv, or Equiv.sum_comp). This gives
   Σ_{J : Fin k → Fin p} Σ_b γ(e∘(Fin.cons b J))² = Σ_{I : Fin (k+1) → Fin p} γ(e∘I)².
5. (Summation and the all-tuples identity.) tuple_sum_factorial with m := p gives, for δ in degree j := k and for γ in degree j := k+1:
   Σ_{J : Fin k → Fin p} δ(e∘J)² = k!·|δ|² and Σ_{I : Fin (k+1) → Fin p} γ(e∘I)² = (k+1)!·|γ|².
   Sum step 3 over all J (Finset.sum_le_sum), pull the constant ‖w‖² out of the sum (Finset.mul_sum) and use step 4:
   k!·|δ|² = Σ_J δ(e∘J)² ≤ ‖w‖²·Σ_J Σ_b γ(e∘(Fin.cons b J))² = ‖w‖²·Σ_I γ(e∘I)² = ‖w‖²·(k+1)!·|γ|².
6. (Cancelling k!.) Since (k+1)! = (k+1)·k! (Nat.factorial_succ), step 5 reads k!·|δ|² ≤ k!·((k+1)·‖w‖²·|γ|²). As k! > 0 (Nat.factorial_pos), this gives |δ|² ≤ (k+1)·‖w‖²·|γ|² (le_of_mul_le_mul_left).
7. (Square roots.) Since k+1 ≥ 0, (√(k+1))² = k+1 (Real.sq_sqrt), so (k+1)·‖w‖²·|γ|² = (√(k+1)·‖w‖·|γ|)². Both |δ| and √(k+1)·‖w‖·|γ| are ≥ 0 (covectorEuclideanNorm_nonneg, Real.sqrt_nonneg, norm_nonneg). Hence |δ|² ≤ (√(k+1)·‖w‖·|γ|)² gives |δ| ≤ √(k+1)·‖w‖·|γ| (pow_le_pow_iff_left₀ with exponent 2 ≠ 0).
No restriction on p or k is used. For k = 0 there is exactly one tuple J (the empty one), 0! = 1, and step 2 only concerns the entry 0. For p = 0 we have w = 0, and all sums over Fin p are empty, so δ(e∘J) = 0 for every J and both sides of the bound are 0. ∎

## Key steps

1. Linearity of γ in its first slot (w = Σ_b w_b e_b, curryLeft) and Fin.cons e_b (e∘J) = e∘(Fin.cons b J) give δ(e∘J) = Σ_b w_b·γ(e∘(Fin.cons b J)).
2. Cauchy–Schwarz: δ(e∘J)² ≤ ‖w‖²·Σ_b γ(e∘(Fin.cons b J))².
3. Summing over J and reindexing by Fin.consEquiv: Σ_J δ(e∘J)² ≤ ‖w‖²·Σ_{I : Fin (k+1) → Fin p} γ(e∘I)².
4. tuple_sum_factorial turns this into k!|δ|² ≤ ‖w‖²(k+1)!|γ|². Cancel k! > 0 using (k+1)! = (k+1)·k!, then take nonnegative square roots: |δ| ≤ √(k+1)‖w‖|γ|.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n 'covectorEuclideanNorm|curryLeft|interior product|interiorProduct' project -g '*.lean' (snapshot project: no match)`
- `rg -n 'Remark 2.6|coefficient norm' project/GMT/Ch06 (only the massOn docstrings of Contract.lean/Submission.lean and README.md)`
- `rg -n 'theorem curryLeft_apply_apply|lemma norm_curryLeft|def curryLeft' mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean (lines 38, 53, 57)`
- `rg -n '^def consEquiv|lemma sum_mul_sq_le_sq_mul_sq|theorem EuclideanSpace.real_norm_sq_eq|protected theorem sum_repr|lemma pow_le_pow_iff_left₀|theorem factorial_succ' mathlib/Mathlib (Data/Fin/Tuple/Basic.lean:184, Algebra/Order/BigOperators/Ring/Finset.lean:171, Analysis/InnerProductSpace/PiL2.lean:153 and :494, Algebra/Order/GroupWithZero/Basic.lean:681, Data/Nat/Factorial/Basic.lean:56)`
- `rg -n 'interior product|interiorProduct|contraction' mathlib/Mathlib/Analysis/Normed/Module/Alternating mathlib/Mathlib/Topology/Algebra/Module/Alternating mathlib/Mathlib/LinearAlgebra/Alternating (no match)`
- `rg -n 'theorem sum_apply|theorem cons_smul|theorem cons_add' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean (lines 235, 382, 396)`
- `cmp of the 7 snapshot Mathlib files above against .lake/packages/mathlib (all identical)`
- `grep -rn covectorEuclideanNorm .lake/packages/simongmt/Poincare (Chapter06/Mass.lean: definition, covectorEuclideanNorm_zero, _nonneg, _neg; FormSupNorm.lean usage only; no smul, pull-back or contraction lemma)`
- `python3 -I over dag.json (669 nodes): lean_statements containing covectorEuclideanNorm or curryLeft -> accepted fiw_tb_ext_covectorNorm_smul, iwl_sp_covectorEuclideanNorm_pullback_le, iwl_sp_pn_sum_sq_tuples_eq_factorial_mul; no other contraction bound besides the selected node`
- `python3 -I: for the 3 reused nodes compare parent-child-handoff.json subproblem title/statement/lean_statement/lean_name with dag.json (all equal), read isolated-comparator-result.json (passed, same candidate commit), git grep 'theorem Submission.<name>' <candidate_commit> -- '*.lean' (each found in GMT/Ch06/Submission.lean); git diff --shortstat d8d46c95 47d3d707 -- GMT/Ch06/Submission.lean (+14 lines, 1 theorem)`
- `name collision: dag.json lean_names (no dph_sh_ib*); grep -rn 'dph_sh_ib|covectorEuclideanNorm_contract' GMT .lake/packages/simongmt/Poincare .lake/packages/mathlib/Mathlib; git grep -q -e 'dph_sh_ib_' -e 'covectorEuclideanNorm_contract_le' over 1733 distinct tips of 4067 local refs (-- '*.lean'); grep over 3661 .swarm-worktrees/*/gmt-ch06/GMT/Ch06/Submission.lean: no match`
- `sed /runtime/flows/gmt-claude-eb5f84b9e61e/_recursive_lean/runtime.py: _decompose (no split only when node.depth >= max_depth), _existing_lean_name_problem (reuse only for accepted checkpoints with identical lean_statement), _solve_children (accepted nodes reused by lean_name), _publish_decomposition_workspace (reused accepted children not re-provisioned), _merge_candidate_history`
- `python3 -I verifier/lean_contract.py validate_lean_statement on the 4 child statements and the selected statement (all valid)`
- `lake env lean /tmp/ib_split_check/Stmts.lean (selected + 4 child statements after the replayed comparator scope; only sorry warnings)`
- `lake env lean /tmp/ib_split_check/Iface2.lean (selected type from the frozen types of norm_smul, pullback_norm, contraction_bound) and /tmp/ib_split_check/Child2.lean (contraction_bound from the frozen type of tuple_sum_factorial): no errors; axioms propext, Classical.choice, Quot.sound`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Nat/Factorial/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-715d48ac9c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-homotopy-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1-norm-smul-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1-norm-smul-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a-71535d6e53/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a-71535d6e53/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-eb5f84b9e61e/_recursive_lean/runtime.py`
- `/tmp/ib_split_check/Stmts.lean`
- `/tmp/ib_split_check/Iface2.lean`
- `/tmp/ib_split_check/Child2.lean`

Nothing in the pinned project, SimonGMT or Mathlib bounds the Euclidean coefficient norm of a contraction. Mathlib's norm_curryLeft is only the operator-norm identity, and there is no interior-product lemma. So the contraction bound is a genuine new obligation. Mathlib supplies its inputs: curryLeft/curryLeft_apply_apply, Fin.consEquiv, Finset.sum_mul_sq_le_sq_mul_sq, EuclideanSpace.real_norm_sq_eq, OrthonormalBasis.sum_repr, Nat.factorial_succ and pow_le_pow_iff_left₀; the snapshot files are identical to the build. Three accepted declarations with byte-identical types and passed comparators cover homogeneity, the pull-back bound and the all-tuples identity. All statements elaborate in the comparator scope. Lean proves the selected type from the children and the new child from tuple_sum_factorial, both with standard axioms only. The new name is globally unused.
