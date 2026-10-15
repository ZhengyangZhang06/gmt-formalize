# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.normalization-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.normalization-a1.frame_flip-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the selected proof ("If s = −1, let v' := (−v_0, v_1, …, v_d) (Function.update v 0 (−v_0)): v' is orthonormal, span{v'} = span{v} = V, and β(v') = −β(v) by linearity of β in its first argument (MultilinearMap.map_update_smul / map_neg on β.toAlternatingMap)").
Notation: ℝ^P = Euclid P; ⟨x, y⟩ = inner ℝ x y; Function.update f i x is f with its i-th entry replaced by x; a (d+1)-covector is β : Covector (Euclid P) (d + 1) = Euclid P [⋀^Fin (d + 1)]→L[ℝ] ℝ; 0 is the first index of Fin (d + 1), which exists because d + 1 ≥ 1.
1. (Signs.) Let c : Fin (d+1) → ℝ, c := Function.update (fun _ => 1) 0 (−1), i.e. c_0 = −1 and c_i = 1 for i ≠ 0; then c_i·c_i = 1 for every i. Let w := Function.update v 0 (−v_0) = (−v_0, v_1, …, v_d). Then w_i = c_i • v_i for every i: for i = 0 both sides equal −v_0, and for i ≠ 0 both sides equal v_i.
2. (w is orthonormal.) For all i, j: ⟨w_i, w_j⟩ = ⟨c_i • v_i, c_j • v_j⟩ = c_i·(c_j·⟨v_i, v_j⟩) (real_inner_smul_left, real_inner_smul_right), and ⟨v_i, v_j⟩ = [i = j] because v is orthonormal (orthonormal_iff_ite). If i = j this equals c_i·(c_i·1) = 1 by step 1; if i ≠ j it equals c_i·(c_j·0) = 0. Thus ⟨w_i, w_j⟩ = [i = j] for all i, j, i.e. w is orthonormal (orthonormal_iff_ite).
3. (Equal spans.) Each w_i = c_i • v_i is a scalar multiple of an element of range v, hence lies in span(range v); so span(range w) ≤ span(range v) (Submodule.span_le, Submodule.smul_mem, Submodule.subset_span). Conversely, by step 1, v_i = (c_i·c_i) • v_i = c_i • (c_i • v_i) = c_i • w_i (one_smul, smul_smul) lies in span(range w); so span(range v) ≤ span(range w). By antisymmetry span{w_0, …, w_d} = span{v_0, …, v_d}.
4. (Covector values change sign.) Let β be a (d+1)-covector. Linearity of β in its 0-th argument gives β(update v 0 ((−1) • v_0)) = (−1) • β(update v 0 v_0) (ContinuousAlternatingMap.map_update_smul), and update v 0 v_0 = v (Function.update_eq_self). Since (−1) • x = −x (neg_one_smul), the left side is β(w) and the right side is −β(v); hence β(w) = −β(v).
5. (Conclusion.) w is orthonormal, span{w_0, …, w_d} = span{v_0, …, v_d}, and β(w) = −β(v) for every (d+1)-covector β. ∎
Formalization note: machine leaf — exactly one theorem Submission.cbr_ci_cp_exists_orthonormal_frame_eval_neg appended to the frozen GMT/Ch07/Submission.lean inside namespace GMT.Ch07 (after the contract section's closing end, before main_theorem), with no import, option or helper declaration. The following proof was compiled in this decomposition session against the frozen import closure of GMT.Ch07.Submission (Lean 4.35.0-rc3, Mathlib 25730c7c; #print axioms = propext, Classical.choice, Quot.sound; no warnings), both standalone and in situ next to the other children, and it passes the runtime leaf check check_source_delta; it may be used verbatim:
theorem Submission.cbr_ci_cp_exists_orthonormal_frame_eval_neg : ∀ (P d : ℕ) (v : Fin (d + 1) → Euclid P), Orthonormal ℝ v → ∃ w : Fin (d + 1) → Euclid P, Orthonormal ℝ w ∧ Submodule.span ℝ (Set.range w) = Submodule.span ℝ (Set.range v) ∧ ∀ β : Covector (Euclid P) (d + 1), β w = -β v := by
  intro P d v hv
  let c : Fin (d + 1) → ℝ := Function.update (fun _ => (1 : ℝ)) 0 (-1)
  have hc : ∀ i, c i * c i = 1 := by
    intro i
    by_cases h : i = 0
    · subst h; simp [c]
    · simp [c, h]
  have hw : (fun i => c i • v i) = Function.update v 0 (-v 0) := by
    funext i
    by_cases h : i = 0
    · subst h; simp [c]
    · simp [c, h]
  refine ⟨Function.update v 0 (-v 0), ?_, ?_, ?_⟩
  · rw [← hw]
    rw [orthonormal_iff_ite] at hv ⊢
    intro i j
    rw [real_inner_smul_left, real_inner_smul_right, hv i j]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, mul_one]
      exact hc i
    · simp only [hij, ↓reduceIte, mul_zero]
  · rw [← hw]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h : v i = c i • (c i • v i) := by
        rw [smul_smul, hc i, one_smul]
      rw [h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro β
    have h := β.map_update_smul v 0 (-1 : ℝ) (v 0)
    rw [neg_one_smul, Function.update_eq_self] at h
    rw [h, neg_one_smul]

## Key steps

1. Take c := update 1 0 (−1) (so c_i·c_i = 1) and w := update v 0 (−v_0), so that w_i = c_i • v_i.
2. ⟨w_i, w_j⟩ = c_i c_j ⟨v_i, v_j⟩ = [i = j], so w is orthonormal.
3. w_i = c_i • v_i and v_i = c_i • w_i give span(range w) = span(range v).
4. Linearity of β in slot 0 (map_update_smul with scalar −1, update_eq_self) gives β(w) = −β(v).

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
