# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.projection_reduction-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.projection_reduction-a1.column_expansion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof. There, det(⟨u_a, e'_{i_b}⟩) is expanded along column k (Matrix.det_succ_column), with α := (−1)^k·e'^{I∖i_k} built as in step 2 from the d-tuple obtained by deleting the k-th vector. Here the same argument is stated for an arbitrary (d+1)-tuple g.
1. (The minor covector.) Let g' : Fin d → ℝ^P, g'_{b'} := g_{k.succAbove b'}, be g with its k-th entry deleted; k.succAbove : Fin d → Fin (d+1) is the increasing map whose image is Fin (d+1) ∖ {k}. By the sibling lemma det_covector with n := d and the tuple g', there is a d-covector γ' with γ'(v) = det(⟨g'_{b'}, v_{a'}⟩)_{a',b' ∈ Fin d} for all v ∈ (ℝ^P)^d. Put α := (−1)^k · γ'; a scalar multiple of a d-covector is a d-covector.
2. (Laplace expansion.) Fix u ∈ (ℝ^P)^{d+1} and let M be the (d+1)×(d+1) real matrix M_{a,b} := ⟨g_b, u_a⟩, so γ(u) = det M by hypothesis. Laplace expansion along column k (Matrix.det_succ_column) gives
   det M = Σ_{i ∈ Fin(d+1)} (−1)^{i+k} · M_{i,k} · det(M^{(i,k)}),
   where M^{(i,k)} := M.submatrix i.succAbove k.succAbove is M with row i and column k removed.
3. (Identify the terms.)
   - M_{i,k} = ⟨g_k, u_i⟩.
   - The (a', b') entry of M^{(i,k)} is M_{i.succAbove a', k.succAbove b'} = ⟨g_{k.succAbove b'}, u_{i.succAbove a'}⟩ = ⟨g'_{b'}, (removeNth i u)_{a'}⟩, because (removeNth i u)_{a'} = u_{i.succAbove a'} by definition of Fin.removeNth.
   - Therefore M^{(i,k)} is the matrix (⟨g'_{b'}, (removeNth i u)_{a'}⟩)_{a',b'}, and det(M^{(i,k)}) = γ'(removeNth i u) by step 1.
4. (Signs.) Since (−1)^{i+k} = (−1)^i (−1)^k and real multiplication is commutative,
   (−1)^{i+k} ⟨g_k, u_i⟩ γ'(removeNth i u) = (−1)^i (⟨g_k, u_i⟩ · ((−1)^k γ'(removeNth i u))) = (−1)^i (⟨g_k, u_i⟩ · α(removeNth i u)).
   Summing over i gives γ(u) = Σ_{i=0}^{d} (−1)^i ⟨g_k, u_i⟩ α(removeNth i u) for every u, as claimed.
   Check for d = 0: k = 0, γ' is the constant 0-covector 1 and α = 1, so the formula reads γ(u) = ⟨g_0, u_0⟩, which is the 1×1 determinant. ∎
Formalization note: the following script compiled in scratch for exactly this frozen type, after import GMT.Ch07.Submission in the contract scope, with the sibling available as Submission.cbr_ci_cp_pr_inner_det_covector, default options and axioms [propext, Classical.choice, Quot.sound]:
  intro P d g k γ hγ
  obtain ⟨γ', hγ'⟩ := Submission.cbr_ci_cp_pr_inner_det_covector P d (fun b => g (k.succAbove b))
  refine ⟨((-1 : ℝ) ^ (k : ℕ)) • γ', fun u => ?_⟩
  rw [hγ u, Matrix.det_succ_column _ k]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousAlternatingMap.smul_apply, hγ' (i.removeNth u), smul_eq_mul]
  have hsub : (Matrix.of fun a b => inner ℝ (g b) (u a)).submatrix i.succAbove k.succAbove =
      Matrix.of fun a b => inner ℝ (g (k.succAbove b)) (i.removeNth u a) := by
    ext a b
    simp [Fin.removeNth]
  rw [hsub, Matrix.of_apply, pow_add]
  ring

## Key steps

1. By det_covector, the d×d minor determinant v ↦ det(⟨g_{k.succAbove b'}, v_{a'}⟩) is a d-covector γ'; set α := (−1)^k γ'.
2. Expand det(⟨g_b,u_a⟩) along column k by Laplace expansion (Matrix.det_succ_column).
3. The (i,k) minor is the matrix of removeNth i u against g with g_k deleted, so it equals γ'(removeNth i u); regroup (−1)^{i+k} = (−1)^i(−1)^k.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); grep of scope commands in Submission.lean (open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; noncomputable section … end)`
- `python3 -I regex scan of dag.json lean_statement for '∃ \w+ : OrthonormalBasis', 'OrthonormalBasis \(Fin P\)', '∃ \w+ : Covector \(Euclid P\) n, ∀ u', 'removeNth', 'detRowAlternating', 'factorial', 'Matrix\.of fun a b', '∈ V ∨', '∈ Vᗮ' (18 hits)`
- `python3 -I scan of dag.json lean_name for cbr_ci_cp_pr_adapted_orthonormalBasis, cbr_ci_cp_pr_inner_det_covector, cbr_ci_cp_pr_det_covector_laplace, cbr_ci_cp_pr_factorial_mul_eq_sum_det (absent; re-run with 1552 and then 1559 nodes); rg -n cbr_ci_cp_pr <snapshot>/project and GMT/ (no match); git log --all -S cbr_ci_cp_pr (no match)`
- `grep -rn in <snapshot>/mathlib/Mathlib for continuous_of_finiteDimensional, 'theorem det_succ_column ', "theorem det_apply' ", 'theorem map_perm', "theorem sum_repr'", subordinateOrthonormalBasis, subordinateOrthonormalBasis_subordinate, orthogonalFamily_self, isInternal_iff, 'theorem map_sum', 'theorem map_smul_univ', 'theorem Fintype.card_perm' (all found)`
- `sed of verifier/lean_contract.py (validate_lean_statement), verifier/gmt-compare.py (contract_scope, child_modules), /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py (check_source_delta: one appended theorem, forbidden def/set_option/…), runtime.py (_decompose: depth ≥ max_depth stops splitting; _existing_lean_name_problem; _reference_use_problem), decomposition_scope.py`
- `lake env lean /tmp/cpr-split/Stmts.lean with set_option pp.explicit: the determinant elaborates as @Matrix.det (Fin n) (instDecidableEqFin n) (Fin.fintype n) Real Real.commRing (Matrix.of …)`
- `lake env lean /tmp/cpr-split/Assembly.lean: theorem cpr_assembly (hypotheses: the 4 child types verbatim; conclusion: the frozen parent type) compiles; #print axioms: propext, Classical.choice, Quot.sound`
- `lake env lean /tmp/cpr-split/A.lean, B0.lean, C.lean, B.lean: each child proved as a single theorem without helper declarations or set_option (default heartbeats); python3 -I /tmp/cpr-scripts/gen.py kids.json → Challenges.lean (comparator-style theorem _root_.X : (stmt) := by sorry in the replayed contract scope; all 4 elaborate) and Integrated.lean (4 children as Submission.X + frozen parent proved only from them; #print axioms of all 5: propext, Classical.choice, Quot.sound); forbidden-token regex of check_source_delta on all 5 proof bodies: no hits`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on the 4 child strings (pass); key/lean_name regexes (pass); the parent string is byte-identical to the handoff's frozen lean_statement`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fintype/Perm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3ff19dec2b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3ff19dec2b/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/decomposition_scope.py`
- `/tmp/cpr-split/Assembly.lean`
- `/tmp/cpr-split/Integrated.lean`
- `/tmp/cpr-split/Challenges.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c).

No accepted DAG theorem has a needed type:
- cmcs_wn_adapted_orthonormalBasis adapts a basis to a linear functional, not to a subspace.
- regcomp_covector_sq_sum_orthonormalBasis only fixes the n!-over-all-maps convention adopted here.
- cbr_ci_pw_pu_inner_det_covector is similar but uses inner (u a) (w b). It is an unaccepted node under another parent, so its name cannot be shared.
The four cbr_ci_cp_pr_* names are fresh in the DAG, the snapshot, GMT/ and git history.

Every Mathlib tool used exists in the snapshot and is reachable from import GMT.Ch07.Submission: Matrix.detRowAlternating, Matrix.det_succ_column, Matrix.det_apply', AlternatingMap.map_perm, ContinuousAlternatingMap.map_sum/map_smul_univ, OrthonormalBasis.sum_repr', DirectSum.IsInternal.subordinateOrthonormalBasis(_subordinate), Submodule.orthogonalFamily_self, OrthogonalFamily.isInternal_iff, Fintype.card_perm.

All four child types elaborate in the replayed contract scope, with the matrix determinant instance verified, and pass validate_lean_statement. Each child has a compiled single-theorem proof that would pass the leaf-delta rules. The hypothesis-only assembly proves the exact frozen parent type with only propext, Classical.choice and Quot.sound.
