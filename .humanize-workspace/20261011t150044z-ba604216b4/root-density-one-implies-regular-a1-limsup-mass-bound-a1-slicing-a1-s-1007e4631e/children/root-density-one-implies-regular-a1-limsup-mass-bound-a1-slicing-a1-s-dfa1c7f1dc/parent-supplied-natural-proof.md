# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.wedge_orientation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.wedge_orientation-a1.wedge_eval-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 3 of the parent proof (wedge expansion); Simon Ch. 6, 4.3 (book/chapter-06.txt lines 1209–1219: ⟨v⌞w, a⟩ = ⟨v, w ∧ a⟩, the interior product used to orient the slice).
Notation: ℝ^P = Euclid P = EuclideanSpace ℝ (Fin P); ⟨x, y⟩ = inner ℝ x y; |x| = ‖x‖; an n-covector is an element of Covector (Euclid P) n = Euclid P [⋀^Fin n]→L[ℝ] ℝ; an n-vector is an element of MultiVector P n = Covector (Euclid P) n →L[ℝ] ℝ; ν^⊥ = (ℝ ∙ ν)ᗮ; Fin.cons ν σ is the family (ν, σ_0, …, σ_{n−1}) indexed by Fin (n + 1).
1. Expansion formula. For F : ℝ^P →L[ℝ] Covector (Euclid P) n and v : Fin (n + 1) → ℝ^P, (alternatizeUncurryFin F)(v) = Σ_{i : Fin (n+1)} (−1)^i • F(v_i)(removeNth i v) (ContinuousAlternatingMap.alternatizeUncurryFin_apply), where removeNth i v is v with the i-th entry deleted. Here F = (innerSL ℝ ν).smulRight α, so F(w) = ⟨ν, w⟩ • α (ContinuousLinearMap.smulRight_apply, innerSL_apply_apply) and F(w)(u) = ⟨ν, w⟩·α(u).
2. Take v := Fin.cons ν σ, so v_0 = ν and v_{j+1} = σ_j (Fin.cons_zero, Fin.cons_succ). Split the sum over Fin (n + 1) into the term i = 0 and the terms i = j + 1, j ∈ Fin n (Fin.sum_univ_succ).
3. The term i = 0 equals (−1)^0·⟨ν, ν⟩·α(removeNth 0 v). Here removeNth 0 v = Fin.tail (Fin.cons ν σ) = σ (Fin.removeNth_zero, Fin.tail_cons) and ⟨ν, ν⟩ = |ν|² = 1. So this term is α(σ).
4. For i = j + 1 the term equals (−1)^{j+1}·⟨ν, σ_j⟩·α(removeNth (j+1) v) = 0, because ⟨ν, σ_j⟩ = 0 by hypothesis.
5. Summing, (ν♭∧α)(Fin.cons ν σ) = α(σ) + 0 = α(σ). For n = 0 the sum consists of the i = 0 term only and the same computation applies. ∎
Formalization note (supplementary; the numbered proof above is complete): unless split further this is a machine leaf: exactly one theorem `Submission.dor_lmbsf_io_wedge_eval_cons` appended to the frozen GMT/Ch07/Submission.lean inside `namespace GMT.Ch07` after the `end` of the noncomputable section (just before `main_theorem`), with no new import, option or helper declaration. Every lemma cited is in the import closure of GMT.Ch07.Submission (pinned Mathlib 25730c7c). The following Lean proof was compiled by this decomposition session, inserted at exactly that position in a copy of GMT/Ch07/Submission.lean (Lean 4.35.0-rc3; `#print axioms` = propext, Classical.choice, Quot.sound; no errors or warnings), and may be used verbatim:
theorem Submission.dor_lmbsf_io_wedge_eval_cons : ∀ (P n : ℕ) (ν : Euclid P) (σ : Fin n → Euclid P) (α : Covector (Euclid P) n), ‖ν‖ = 1 → (∀ i, inner ℝ ν (σ i) = 0) → ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ ν).smulRight α) (Fin.cons ν σ : Fin (n + 1) → Euclid P) = α σ := by
  intro P n ν σ α hν hνσ
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ]
  simp [Fin.removeNth_zero, Fin.tail_cons, innerSL_apply_apply, hνσ, hν]

## Key steps

1. ContinuousAlternatingMap.alternatizeUncurryFin_apply: (ν♭∧α)(v) = Σ_i (−1)^i ⟨ν, v_i⟩ α(removeNth i v).
2. With v = Fin.cons ν σ, split off i = 0 by Fin.sum_univ_succ.
3. The i = 0 term is ⟨ν, ν⟩ α(Fin.tail (Fin.cons ν σ)) = |ν|² α(σ) = α(σ).
4. Every term i = j + 1 contains ⟨ν, σ_j⟩ = 0.
5. Hence (ν♭∧α)(ν, σ) = α(σ).

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -n 'def IsUnitOrientationOf|abbrev MultiVector|abbrev Euclid|Covector|alternatizeUncurryFin|innerSL' <snapshot>/project/GMT/Ch07/Contract.lean`
- `rg -n 'dor_lmbsf_io_|interior_product_orientation' <snapshot>/project/ (no match)`
- `rg -n 'theorem alternatizeUncurryFin_apply|eq_smul_basis_det|theorem finrank_add_inf_finrank_orthogonal|theorem orthonormal_iff_ite|theorem Orthonormal.comp_linearIsometry|theorem Orthonormal.inner_right_fintype|theorem mem_orthogonal_singleton_iff_inner_right|theorem finrank_span_eq_card|theorem Submodule.mem_span_range_iff_exists_fun|theorem det_transpose|theorem det_mul|theorem finrank_span_singleton|removeNth_zero|theorem tail_cons|theorem innerSL_apply_apply|det_to_matrix_orthonormalBasis_real|stdOrthonormalBasis|theorem span_singleton_le_iff_mem|theorem span_image|theorem map_top|theorem range_subtype|subtypeₗᵢ' <snapshot>/mathlib/Mathlib`
- `grep -rn 'abbrev Covector' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/`
- `python3 -I DAG scans of dag.json: lean_statements mentioning IsUnitOrientationOf / alternatizeUncurryFin / Orthonormal+det / Fin.cons / removeNth / innerSL+smulRight; lean_name collision check for the four child names; reuse candidate dgoj_covector_eq_det_mul_of_mem_span (status accepted, candidate_commit 73310ec9); orientation-lemma scan (rsdic_unitOrientation_eq_or_eq_neg, dgcr_unitOrientation_eq_or_neg)`
- `git log --all -S dor_lmbsf_io_ --oneline -- GMT/Ch07/Submission.lean (no match); git show 73310ec921452a01670f397b34d1cf3cd7135598:GMT/Ch07/Submission.lean (accepted dgoj proof)`
- `grep -n '4.3\|1.1' book/chapter-06.txt (Simon 6.1.1 at lines 28-30, 6.4.3 at lines 1209-1219)`
- `python3 -I verifier lean_contract.validate_lean_statement and gmt-compare.child_modules (contract mode) on the 4 child statements`
- `lake env lean /tmp/wedge-orient-decomp/All.lean; lake env lean /tmp/wedge-orient-decomp/insert/GMT/Ch07/SubmissionInserted.lean; lake env lean /tmp/wedge-orient-decomp/challenges/*_Challenge.lean (#print axioms = propext, Classical.choice, Quot.sound)`
- `rg -n '_existing_lean_name_problem|An accepted theorem may be reused by Lean name|_overlay_accepted_children' /runtime/flows/gmt-claude-82aee5f72857/_recursive_lean/runtime.py (reuse of accepted nodes by identical frozen type)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Span/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Span/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-1007e4631e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-596f7d2f1c/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/wedge-orient-decomp/All.lean`
- `/tmp/wedge-orient-decomp/insert/GMT/Ch07/SubmissionInserted.lean`

Snapshot: project b4d606d, mathlib 25730c7c. Snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. IsUnitOrientationOf is defined at Contract.lean:52 and Covector at simongmt Chapter06/Forms.lean:31.

No snapshot or DAG declaration states the adapted frame, the frame-sign lemma or the wedge evaluation; rg for dor_lmbsf_io_ / interior_product_orientation finds nothing.

One exact match exists: the accepted Submission.dgoj_covector_eq_det_mul_of_mem_span (candidate 73310ec9) has exactly the covector_det type. It is reused by its byte-identical frozen type, which the runtime permits for accepted checkpoints.

All cited library facts are in the pinned snapshot:
- ContinuousAlternatingMap.alternatizeUncurryFin_apply (Uncurry/Fin.lean:137);
- AlternatingMap.eq_smul_basis_det (Determinant.lean:650);
- Submodule.finrank_add_inf_finrank_orthogonal (Projection/FiniteDimensional.lean:89);
- orthonormal_iff_ite (Orthonormal.lean:82), Orthonormal.inner_right_fintype (:129), Orthonormal.comp_linearIsometry (:315);
- Submodule.mem_orthogonal_singleton_iff_inner_right (Orthogonal.lean:86);
- finrank_span_eq_card (Dimension/Constructions.lean:463);
- Submodule.mem_span_range_iff_exists_fun (Finsupp/LinearCombination.lean:379);
- Matrix.det_mul (:141) and Matrix.det_transpose (:206);
- finrank_span_singleton (FiniteDimensional/Basic.lean:535);
- Fin.tail_cons (:117) and Fin.removeNth_zero (:893);
- innerSL_apply_apply (InnerProductSpace/LinearMap.lean:172);
- OrthonormalBasis.det_to_matrix_orthonormalBasis_real (PiL2.lean:992) and stdOrthonormalBasis (PiL2.lean:1073);
- Submodule.span_singleton_le_iff_mem (Span/Defs.lean:545), Submodule.span_image (Span/Basic.lean:254), Submodule.map_top (:305) and Submodule.range_subtype (:309).

Lean checks:
- All four child types pass validate_lean_statement and elaborate in the exact comparator scope.
- Complete proofs of all children and the assembly of the exact frozen parent type from them compile inside a copy of Submission.lean with only propext, Classical.choice and Quot.sound.
