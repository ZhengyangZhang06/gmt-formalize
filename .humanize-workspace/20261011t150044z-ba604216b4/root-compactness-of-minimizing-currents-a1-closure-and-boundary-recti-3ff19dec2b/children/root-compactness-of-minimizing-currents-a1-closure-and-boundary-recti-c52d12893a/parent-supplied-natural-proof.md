# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.projection_reduction-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.projection_reduction-a1.adapted_basis-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof (an adapted orthonormal basis, obtained by concatenating orthonormal bases of V and V^⊥ using ℝ^P = V ⊕ V^⊥ orthogonally). The parent's later steps only use the dichotomy 'e_i ∈ V or e_i ∈ V^⊥', so the ordering 'the first r = dim V vectors lie in V' is not recorded.
1. (V and V^⊥ are orthogonal.) If v ∈ V and w ∈ V^⊥ then ⟨v, w⟩ = 0, by definition of V^⊥. In particular V ∩ V^⊥ = {0}, because a vector in both is orthogonal to itself.
2. (V + V^⊥ = ℝ^P.) Let x be orthogonal to the subspace V + V^⊥.
   - Since V ⊆ V + V^⊥, x is orthogonal to V, i.e. x ∈ V^⊥.
   - Since V^⊥ ⊆ V + V^⊥, x is orthogonal to V^⊥, i.e. x ∈ (V^⊥)^⊥.
   - Hence ⟨x, x⟩ = 0 (x ∈ V^⊥ and x is orthogonal to every vector of V^⊥), so x = 0.
   Thus (V + V^⊥)^⊥ = {0}. Since ℝ^P is finite-dimensional, V + V^⊥ = ((V + V^⊥)^⊥)^⊥ = ℝ^P. With step 1, ℝ^P is the internal orthogonal direct sum of V and V^⊥.
3. (Concatenate.) Choose an orthonormal basis f_1, …, f_r of V and an orthonormal basis h_1, …, h_s of V^⊥; finite-dimensional inner product spaces have orthonormal bases.
   - The concatenated family (f_1, …, f_r, h_1, …, h_s) is orthonormal: within each block by choice, and ⟨f_j, h_l⟩ = 0 by step 1.
   - It spans V + V^⊥ = ℝ^P by step 2.
   - An orthonormal family is linearly independent, so it is an orthonormal basis of ℝ^P. In particular r + s = P.
4. (Re-index.) The index set {1, …, r} ⊔ {1, …, s} has P elements. Transport the basis along a bijection with Fin P and call the result e = (e_i)_{i ∈ Fin P}. Its vectors are the f_j ∈ V and the h_l ∈ V^⊥, so each e_i lies in V or in V^⊥. ∎
Formalization note (Mathlib): this is DirectSum.IsInternal.subordinateOrthonormalBasis for the Bool-indexed family b ↦ cond b V Vᗮ.
- The family is orthogonal by Submodule.orthogonalFamily_self.
- It is internal by OrthogonalFamily.isInternal_iff: internal ⟺ (⨆ b, cond b V Vᗮ)ᗮ = ⊥, which is step 2 via Submodule.orthogonal_le, le_iSup and Submodule.orthogonal_disjoint.
- The dimension is finrank_euclideanSpace_fin.
- DirectSum.IsInternal.subordinateOrthonormalBasis_subordinate places each basis vector in cond b V Vᗮ, where b = subordinateOrthonormalBasisIndex. Generalize this index and case on b.
The following script compiled in scratch for exactly this frozen type, after import GMT.Ch07.Submission in the contract scope, with default options and axioms [propext, Classical.choice, Quot.sound]:
  intro P V
  have hW' : OrthogonalFamily ℝ (fun b : Bool => ↥(cond b V Vᗮ)) fun b => (cond b V Vᗮ).subtypeₗᵢ :=
    V.orthogonalFamily_self
  have hW : DirectSum.IsInternal fun b : Bool => cond b V Vᗮ := by
    rw [hW'.isInternal_iff]
    rw [Submodule.eq_bot_iff]
    intro x hx
    have h1 : x ∈ Vᗮ := Submodule.orthogonal_le (le_iSup (fun b : Bool => cond b V Vᗮ) true) hx
    have h2 : x ∈ Vᗮᗮ := Submodule.orthogonal_le (le_iSup (fun b : Bool => cond b V Vᗮ) false) hx
    exact Submodule.mem_bot ℝ |>.mp (by
      have := Submodule.orthogonal_disjoint Vᗮ
      exact (Submodule.disjoint_def.mp this) x h1 h2 ▸ Submodule.zero_mem _)
  refine ⟨hW.subordinateOrthonormalBasis (finrank_euclideanSpace_fin) hW', fun i => ?_⟩
  have hmem := hW.subordinateOrthonormalBasis_subordinate (finrank_euclideanSpace_fin) i hW'
  revert hmem
  generalize hW.subordinateOrthonormalBasisIndex (finrank_euclideanSpace_fin) i hW' = b
  cases b
  · intro hmem
    exact Or.inr hmem
  · intro hmem
    exact Or.inl hmem

## Key steps

1. V and V^⊥ are orthogonal, and V + V^⊥ = ℝ^P because a vector orthogonal to both is orthogonal to itself.
2. Concatenating orthonormal bases of V and V^⊥ gives an orthonormal family that spans ℝ^P, hence an orthonormal basis with P elements.
3. Re-index it by Fin P; each basis vector lies in V or in V^⊥.

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
