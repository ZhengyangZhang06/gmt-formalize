# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.projection_reduction-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.projection_reduction-a1.det_expansion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof. There, β = Σ_I β(e'_I)·e'^I is proved by expanding each argument u_a = Σ_m⟨u_a, e'_m⟩e'_m and using that β is alternating. Here the sum is taken over all index maps I : Fin n → Fin P instead of strictly increasing ones. The two forms agree:
- a non-injective I contributes 0, since its determinant has two equal columns;
- each strictly increasing J occurs exactly n! times as J∘π, π a permutation, and β(e_{J∘π})·det(⟨e_{J(π b)}, u_a⟩) = sign(π)²·β(e_J)·det(⟨e_{J(b)}, u_a⟩) = β(e_J)·det(⟨e_{J(b)}, u_a⟩).
This explains the factor n!. The proof below proves the stated identity directly. Write e_I := (e_{I(0)}, …, e_{I(n−1)}).
1. (Multilinear expansion.) For every v ∈ (ℝ^P)^n, β(v) = Σ_{I : Fin n → Fin P} (Π_{a ∈ Fin n} ⟨e_{I(a)}, v_a⟩) · β(e_I).
   - Since e is orthonormal, v_a = Σ_{m ∈ Fin P} ⟨e_m, v_a⟩ e_m for each a (OrthonormalBasis.sum_repr').
   - Expanding β multilinearly in all n arguments (ContinuousAlternatingMap.map_sum) gives β(v) = Σ_{I : Fin n → Fin P} β(⟨e_{I(0)}, v_0⟩ e_{I(0)}, …, ⟨e_{I(n−1)}, v_{n−1}⟩ e_{I(n−1)}).
   - Pulling the scalars out of every argument (ContinuousAlternatingMap.map_smul_univ) turns each term into (Π_a ⟨e_{I(a)}, v_a⟩)·β(e_I).
2. (Alternation.) For each permutation σ of Fin n, β(u∘σ) = sign(σ)·β(u), because β is alternating (AlternatingMap.map_perm applied to β.toAlternatingMap). Since sign(σ) = ±1, sign(σ)·β(u∘σ) = sign(σ)²·β(u) = β(u). Fin n has n! permutations (Fintype.card_perm, Fintype.card_fin), so summing over them gives n!·β(u) = Σ_σ sign(σ)·β(u∘σ).
3. (Substitute and exchange sums.) Apply step 1 with v := u∘σ, only to the term β(u∘σ) and not again to β(e_I). This gives
   n!·β(u) = Σ_σ Σ_I sign(σ)·(Π_a ⟨e_{I(a)}, u_{σ(a)}⟩)·β(e_I).
   Exchanging the two finite sums (Finset.sum_comm) and factoring out β(e_I):
   n!·β(u) = Σ_I β(e_I)·Σ_σ sign(σ)·Π_a ⟨e_{I(a)}, u_{σ(a)}⟩.
4. (Leibniz formula.) For fixed I let M^I be the n×n matrix with M^I_{a,b} := ⟨e_{I(b)}, u_a⟩. The Leibniz formula det M = Σ_σ sign(σ)·Π_b M_{σ(b), b} (Matrix.det_apply') gives det M^I = Σ_σ sign(σ)·Π_b ⟨e_{I(b)}, u_{σ(b)}⟩. This is the inner sum of step 3 with the product variable renamed from a to b. Therefore n!·β(u) = Σ_{I : Fin n → Fin P} β(e_I)·det(⟨e_{I(b)}, u_a⟩)_{a,b}.
   The argument is valid for every n, including n = 0 (0! = 1, a single empty map I, empty determinant 1) and P = 0. ∎
Formalization note: the following script compiled in scratch for exactly this frozen type, after import GMT.Ch07.Submission in the contract scope, with default options and axioms [propext, Classical.choice, Quot.sound]. Rewrite with hexp only at u ∘ σ: simp_rw [hexp] loops, because hexp's right side contains β again.
  intro P n e β u
  classical
  have hexp : ∀ v : Fin n → Euclid P, β v =
      ∑ I : Fin n → Fin P, (∏ a, inner ℝ (e (I a)) (v a)) * β (fun a => e (I a)) := by
    intro v
    have hv : v = fun a => ∑ m, inner ℝ (e m) (v a) • e m := by
      funext a
      exact (e.sum_repr' (v a)).symm
    conv_lhs => rw [hv]
    rw [β.map_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [β.map_smul_univ (fun a => inner ℝ (e (I a)) (v a)) (fun a => e (I a)), smul_eq_mul]
  have halt : (n.factorial : ℝ) * β u =
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) * β (u ∘ σ) := by
    have : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) * β (u ∘ σ) = β u := by
      intro σ
      rw [show β (u ∘ σ) = Equiv.Perm.sign σ • β u from β.toAlternatingMap.map_perm u σ]
      rw [Units.smul_def, zsmul_eq_mul, ← mul_assoc]
      have hs : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
        rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
      rw [hs, one_mul]
    rw [Finset.sum_congr rfl fun σ _ => this σ, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [halt]
  have h2 : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) * β (u ∘ σ) =
      ∑ I : Fin n → Fin P, (Equiv.Perm.sign σ : ℝ) *
        ((∏ a, inner ℝ (e (I a)) ((u ∘ σ) a)) * β (fun a => e (I a))) := by
    intro σ
    rw [hexp (u ∘ σ), Finset.mul_sum]
  rw [Finset.sum_congr rfl fun σ _ => h2 σ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Matrix.det_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.of_apply, Function.comp_apply]
  ring

## Key steps

1. Multilinear expansion in the orthonormal basis: β(v) = Σ_I (Π_a⟨e_{I(a)},v_a⟩)·β(e_I).
2. Alternation: n!·β(u) = Σ_σ sign(σ)·β(u∘σ).
3. Substitute the expansion for v = u∘σ, swap the finite sums, and recognize Σ_σ sign(σ) Π_b⟨e_{I(b)},u_{σ(b)}⟩ = det(⟨e_{I(b)},u_a⟩) by the Leibniz formula.

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
