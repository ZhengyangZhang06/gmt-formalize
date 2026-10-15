# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.normalization-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.normalization-a1.rank_deficient_vanish-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the selected proof ("For every n-covector β and every u, the n vectors p u_0, …, p u_d lie in V, whose dimension is r < n, so they are linearly dependent, and the alternating map β vanishes on them (AlternatingMap.map_linearDependent). Thus β∘p = 0"), stated for an arbitrary degree n.
Notation: ℝ^P = Euclid P; an n-covector is β : Covector (Euclid P) n = Euclid P [⋀^Fin n]→L[ℝ] ℝ; p := V.starProjection = V.subtypeL ∘L V.orthogonalProjectionOnto, so p x = ↑(V.orthogonalProjectionOnto x) ∈ V (Submodule.starProjection_apply); β∘p := β.compContinuousLinearMap p, with (β∘p)(u) = β(p∘u) = β(p u_0, …, p u_{n−1}) (ContinuousAlternatingMap.compContinuousLinearMap_apply).
1. (Reduction to values.) Two continuous alternating maps are equal when they agree at every argument family (ext). Fix u : Fin n → ℝ^P; since the zero map takes the value 0 everywhere (ContinuousAlternatingMap.coe_zero), it suffices to prove β(p u_0, …, p u_{n−1}) = 0.
2. (The projected family is linearly dependent.) Suppose the family w := (p u_i)_{i ∈ Fin n} in ℝ^P were linearly independent. Put w'_i := V.orthogonalProjectionOnto u_i ∈ V; then w = V.subtype ∘ w' by the definition of p. If the image of a family under a linear map is linearly independent then so is the family (LinearIndependent.of_comp, applied to the linear map V.subtype); hence w' is a linearly independent family of n vectors in the finite-dimensional space V, and therefore n = card(Fin n) ≤ dim V (LinearIndependent.fintype_card_le_finrank, Fintype.card_fin). This contradicts the hypothesis dim V < n. Hence w is not linearly independent.
3. (Alternating forms vanish on dependent families.) β.toAlternatingMap is an alternating ℝ-multilinear map (ℝ^P)^n → ℝ over the field ℝ (a domain, and ℝ is torsion-free over itself); such a map vanishes on every family that is not linearly independent (AlternatingMap.map_linearDependent). By step 2, β(p∘u) = β.toAlternatingMap(w) = 0.
4. (Conclusion.) As u was arbitrary, β∘p = 0 by step 1. (If n = 0 the hypothesis dim V < 0 is impossible, so the claim is vacuous; the argument above needs no case split.) ∎
Formalization note: machine leaf — exactly one theorem Submission.cbr_ci_cp_comp_starProjection_eq_zero_of_finrank_lt appended to the frozen GMT/Ch07/Submission.lean inside namespace GMT.Ch07 (after the contract section's closing end, before main_theorem), with no import, option or helper declaration. The following proof was compiled in this decomposition session against the frozen import closure of GMT.Ch07.Submission (Lean 4.35.0-rc3, Mathlib 25730c7c; #print axioms = propext, Classical.choice, Quot.sound; no warnings), both standalone and in situ next to the other children, and it passes the runtime leaf check check_source_delta; it may be used verbatim:
theorem Submission.cbr_ci_cp_comp_starProjection_eq_zero_of_finrank_lt : ∀ (P n : ℕ) (V : Submodule ℝ (Euclid P)), Module.finrank ℝ V < n → ∀ β : Covector (Euclid P) n, β.compContinuousLinearMap V.starProjection = 0 := by
  intro P n V hlt β
  ext u
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  apply β.toAlternatingMap.map_linearDependent
  intro hli
  have hli' : LinearIndependent ℝ (fun i => V.orthogonalProjectionOnto (u i)) := by
    apply LinearIndependent.of_comp V.subtype
    exact hli
  have hcard := hli'.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega

## Key steps

1. Reduce β∘p_V = 0 to β(p_V u_0, …, p_V u_{n−1}) = 0 for every family u (ext, compContinuousLinearMap_apply).
2. p_V∘u = V.subtype ∘ (orthogonalProjectionOnto ∘ u) is not linearly independent: otherwise LinearIndependent.of_comp gives n linearly independent vectors in V, so n ≤ dim V < n.
3. An alternating form vanishes on a linearly dependent family (AlternatingMap.map_linearDependent), so β(p_V∘u) = 0.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `python3 -I scans of /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json lean_statement / lean_name values: 'Orthonormal' with 'span' or 'finrank'; 'compContinuousLinearMap' with 'starProjection' or '= 0'; 'Function.update'; regex 'finrank ℝ \w+ = \w+ → ∃ \w+ : Fin'; '-α τ'; lean_name regex 'frame|flip|neg_first|update_neg|orthonormal_basis|onb' (found accepted dgoj_covector_eq_det_mul_of_mem_span, regcomp_covector_eval_orthonormal_le, regcomp_exists_covector_eval_orthonormal_eq_one with byte-identical types; no accepted subspace-frame, rank-deficient-vanishing or frame-flip theorem)`
- `rg -c 'cbr_ci_cp_comp_starProjection_eq_zero_of_finrank_lt|cbr_ci_cp_exists_orthonormal_frame_of_finrank_eq|cbr_ci_cp_exists_orthonormal_frame_eval_neg' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project GMT (no match, exit 1); DAG lean_name scan (no node uses the three new names)`
- `rg -n in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib: 'theorem map_linearDependent', 'theorem fintype_card_le_finrank', 'theorem LinearIndependent.of_comp', 'def starProjection', 'lemma starProjection_apply', 'lemma starProjection_apply_mem', 'Orthonormal.comp_linearIsometry', 'theorem orthonormal_iff_ite', 'Orthonormal.inner_right_fintype', 'irreducible_def stdOrthonormalBasis', 'coe_toBasis', 'theorem map_update_smul', 'theorem real_inner_smul_left', 'theorem real_inner_smul_right', 'theorem span_image', 'theorem map_top', 'theorem range_subtype', 'protected theorem span_eq', 'theorem range_comp', 'theorem AlternatingMap.eq_smul_basis_det' (all found)`
- `git show b7846b639953f647296619e6e73dec8a8a22ba73 / baaca6e45ef59dcdc4a449dbbfe914c226ee5d7b / 73310ec921452a01670f397b34d1cf3cd7135598 :GMT/Ch07/Submission.lean (accepted candidate proofs of the three reused theorems and their regcomp_covector_sq_sum_* helpers; insertion point after the contract section end, before main_theorem)`
- `lake env lean /tmp/nz-decomp/Stmts.lean (the six child types and the frozen parent type elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07 with the contract opens)`
- `lake env lean /tmp/nz-decomp/Assembly.lean (theorem nz_assembly_exact: hypotheses = the six child types verbatim, conclusion = exact frozen parent type; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/nz-decomp/Children.lean and /tmp/nz-decomp/InSitu.lean (frozen Submission.lean + accepted reused theorems + three new child proofs + Submission.cbr_ci_cp_eval_eq_orthonormal_frame proved from them; compiles; #print axioms: propext, Classical.choice, Quot.sound)`
- `python3 -I /tmp/nz-scripts/check.py (check_source_delta extracted from leaf_verification.py passes for the three child proofs and the parent assembly; verifier/lean_contract.py validate_lean_statement passes for all six strings; key and lean_name regexes; reused types byte-identical to dag.json)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose: depth 5 < max_depth 6; _existing_lean_name_problem; _solve_children reuse by lean_name; _overlay_accepted_children merges children and depends_on; _install_parent_supplied_child_handoff skips accepted checkpoints) and decomposition_scope.py`
- `sed of simongmt Poincare/SimonGMT/Chapter06/Forms.lean (Covector), Mass.lean (covectorEuclideanNorm) and GMT/Ch07/Submission.lean (Euclid, MultiVector, IsUnitOrientationOf, insertion context)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/LinearIndependent/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Span/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Basis/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-a44cc12920/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6c861e5511/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-596f7d2f1c/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/decomposition_scope.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/nz-decomp/Assembly.lean`
- `/tmp/nz-decomp/InSitu.lean`

The snapshot contract is byte-identical to the workspace Submission.lean (project b4d606db, Mathlib 25730c7c). Three comparator-accepted DAG theorems are reused with byte-identical types: dgoj_covector_eq_det_mul_of_mem_span (step 3 in determinant form), regcomp_covector_eval_orthonormal_le (O1) and regcomp_exists_covector_eval_orthonormal_eq_one (O2). No accepted theorem gives rank-deficient vanishing, an orthonormal frame of a subspace of given dimension, or the frame sign flip, so these become three new leaves with fresh cbr_ci_cp_ names. Every cited Mathlib lemma exists in the snapshot and is reachable from import GMT.Ch07.Submission. All six child types elaborate and validate. The three new child proofs compile and pass check_source_delta. The exact frozen parent type is proved from the six child types, both hypothesis-only and in situ, using only propext, Classical.choice and Quot.sound.
