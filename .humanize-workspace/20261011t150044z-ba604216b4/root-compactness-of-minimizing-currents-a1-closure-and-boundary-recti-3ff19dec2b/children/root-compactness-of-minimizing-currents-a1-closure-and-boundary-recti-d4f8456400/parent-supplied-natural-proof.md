# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.projection_reduction-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.projection_reduction-a1.det_covector-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof. There, e'^I(u) := det(⟨u_a, e'_{i_b}⟩) is shown to be an n-covector: row a depends linearly on u_a, the determinant is multilinear and alternating in the rows, and continuity holds in finite dimension. Here the same argument is stated for an arbitrary n-tuple g instead of (e'_{i_0}, …, e'_{i_d}).
1. (Rows.) Let L : ℝ^P → ℝ^n be the linear map L(x) := (⟨g_b, x⟩)_{b ∈ Fin n}; each coordinate x ↦ ⟨g_b, x⟩ is linear. For u ∈ (ℝ^P)^n, the matrix (⟨g_b, u_a⟩)_{a,b} is the matrix whose row a is L(u_a).
2. (Row determinant.) Regard the determinant as a function of the n rows: D(r_0, …, r_{n−1}) := det(matrix with rows r_a). D is multilinear (linear in each row) and alternating (zero when two rows coincide). In Mathlib this is Matrix.detRowAlternating.
3. (Multilinear and alternating.) Define γ_0(u) := D(L(u_0), …, L(u_{n−1})) = det(⟨g_b, u_a⟩)_{a,b}.
   - γ_0 is linear in each argument u_a, because L is linear and D is linear in each row.
   - If u_a = u_{a'} for some a ≠ a', then L(u_a) = L(u_{a'}), so two rows coincide and γ_0(u) = 0.
   Hence γ_0 is an alternating n-linear map. In Mathlib it is AlternatingMap.compLinearMap of detRowAlternating with LinearMap.pi (fun b => innerₛₗ ℝ (g b)), and its value at u is definitionally det(Matrix.of fun a b => ⟨g_b, u_a⟩).
4. (Continuity.) Each entry u ↦ ⟨g_b, u_a⟩ is continuous: a coordinate projection followed by the continuous inner product. The determinant is a polynomial in the n² entries. Therefore u ↦ det(⟨g_b, u_a⟩) is continuous on (ℝ^P)^n (fun_prop, or Continuous.matrix_det).
5. (Package.) A multilinear alternating map that is continuous is a continuous alternating map. Combine:
   - the continuous multilinear map ⟨γ_0 as a multilinear map, continuity from step 4⟩, and
   - the alternating property from step 3.
   The resulting γ : Covector (Euclid P) n satisfies γ(u) = γ_0(u) = det(⟨g_b, u_a⟩)_{a,b} for all u. The argument is uniform in n: for n = 0 the empty determinant is 1 and γ is the constant 0-covector 1. ∎
Formalization note: the following script compiled in scratch for exactly this frozen type, after import GMT.Ch07.Submission in the contract scope, with default options and axioms [propext, Classical.choice, Quot.sound]:
  intro P n g
  let f : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ :=
    Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun b => innerₛₗ ℝ (g b))
  have hf : ∀ u, f u = Matrix.det (Matrix.of fun a b => inner ℝ (g b) (u a)) := by
    intro u
    rfl
  have hc : Continuous fun u : Fin n → Euclid P => Matrix.det (Matrix.of fun a b => inner ℝ (g b) (u a)) := by
    fun_prop
  refine ⟨⟨⟨f.toMultilinearMap, ?_⟩, f.map_eq_zero_of_eq'⟩, ?_⟩
  · exact hc.congr fun u => (hf u).symm
  · intro u
    exact hf u

## Key steps

1. Row a of the matrix (⟨g_b,u_a⟩)_{a,b} is L(u_a), where L(x) = (⟨g_b,x⟩)_b is linear.
2. The row determinant is multilinear and alternating, so u ↦ det(⟨g_b,u_a⟩) is an alternating n-linear map.
3. It is continuous (a polynomial in continuous entries), hence a continuous alternating map, i.e. an n-covector.

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
