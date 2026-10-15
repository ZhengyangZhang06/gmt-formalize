# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.normal_orientation-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.normal_orientation-a1.det_normal_decomp-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the determinant argument of step 5 of the parent proof ('the determinant is linear in its first column and vanishes when two columns are equal, so det[φ, σ] = ⟨φ, ν⟩·det[ν, σ]'), stated for an arbitrary first column w and for any family σ spanning ν^⊥ (orthonormality of σ is not used).

Notation. ⟨·,·⟩ is the standard (real, symmetric) inner product of ℝ^{n+1}, and D(x) := det[x, σ] for x ∈ ℝ^{n+1}. In Lean, det(Matrix.of fun r c => v c r) = det_std(v), the determinant with respect to the standard basis EuclideanSpace.basisFun (Module.Basis.det_apply), and D(x) = det_std(Fin.cons x σ) = (det_std.curryLeft x)(σ) (AlternatingMap.curryLeft_apply_apply).

1. (D is linear.) Column 0 of [x, σ] is the only column depending on x, and the determinant is linear in each column; hence D(x + y) = D(x) + D(y) and D(t·x) = t·D(x) for x, y ∈ ℝ^{n+1}, t ∈ ℝ. (Explicitly, Laplace expansion along column 0 gives D(x) = Σ_i (−1)^i x_i det N_i with minors N_i not depending on x; in Lean, x ↦ det_std.curryLeft x is a linear map, so map_add and map_smul apply.)
2. (D vanishes on span σ.) Let q ∈ span{σ_0, …, σ_{n−1}}. The family (q, σ_0, …, σ_{n−1}) = Fin.cons q σ is not linearly independent, since Fin.cons q σ is linearly independent only if q ∉ span(range σ) (linearIndependent_finCons). The determinant of a matrix whose columns are linearly dependent is 0 (AlternatingMap.map_linearDependent applied to det_std). Hence D(q) = 0. (Alternatively: write q = Σ_k c_k σ_k; by step 1, D(q) = Σ_k c_k D(σ_k), and each D(σ_k) = 0 because [σ_k, σ] has equal columns 0 and k+1.)
3. (Normal decomposition.) Put q := w − ⟨w, ν⟩ν. Using ⟨ν, ν⟩ = |ν|² = 1 and the symmetry of the real inner product, ⟨ν, q⟩ = ⟨ν, w⟩ − ⟨w, ν⟩⟨ν, ν⟩ = ⟨w, ν⟩ − ⟨w, ν⟩ = 0. Hence q ∈ (span{ν})^⊥ (Submodule.mem_orthogonal_singleton_iff_inner_right), and by the hypothesis span{σ_0, …, σ_{n−1}} = (span{ν})^⊥ we get q ∈ span{σ_0, …, σ_{n−1}}.
4. (Conclusion.) Since w = ⟨w, ν⟩ν + q, steps 1–3 give D(w) = ⟨w, ν⟩·D(ν) + D(q) = ⟨w, ν⟩·D(ν), that is, det[w, σ] = ⟨w, ν⟩·det[ν, σ]. ∎

## Key steps

1. x ↦ det[x, σ] is linear, since only column 0 depends on x.
2. det[q, σ] = 0 for every q ∈ span σ, because the columns (q, σ_0, …, σ_{n−1}) are linearly dependent.
3. q := w − ⟨w, ν⟩ν lies in ν^⊥ = span σ, so det[w, σ] = ⟨w, ν⟩·det[ν, σ] + det[q, σ] = ⟨w, ν⟩·det[ν, σ].

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib rev-parse HEAD; git -C /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt rev-parse HEAD; sha256sum GMT/Ch07/Submission.lean <snapshot>/project/GMT/Ch07/Contract.lean`
- `grep -rn 'Covector' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `python3 scans of dag.json: selected-node record (depth 5, status decomposing); lean_statements containing 'succAbove', 'Matrix.det' or 'Covector'+'Orthonormal'; lean_name/lean_statement lookup of codim1_lur_no_oriented_normal_frame, codim1_lur_no_covector_eq_det_cons, codim1_lur_no_det_cons_normal_decomp (no hits in 936 nodes)`
- `git for-each-ref --format='%(objectname)' | sort -u | xargs -n 100 sh -c 'git grep -l -E "codim1_lur_no_(oriented_normal_frame|covector_eq_det_cons|det_cons_normal_decomp)" "$@" -- "GMT/*.lean"' _   (1662 tips, no match; sanity pattern dor_ims_massOn_le_measure does match)`
- `rg -n 'theorem det_to_matrix_orthonormalBasis|theorem finrank_orthogonal_span_singleton|theorem Orthonormal.comp_linearIsometry|span_eq_top_of_card_eq_finrank|theorem linearIndependent_finCons|theorem cons_update|theorem map_update_smul|theorem orthonormal_iff_ite|def mk \(hon|theorem sign_cycleRange|theorem cycleRange_symm_zero|theorem cycleRange_symm_succ|theorem ext_alternating|theorem det_succ_column_zero|theorem map_perm|theorem map_linearDependent|theorem curryLeft_apply_apply|theorem finrank_euclideanSpace_fin' <snapshot>/mathlib/Mathlib`
- `rg -n 'det_apply' <snapshot>/mathlib/Mathlib/LinearAlgebra/Determinant.lean; rg -n 'ext_alternating' <snapshot>/mathlib/Mathlib; rg -n 'lemma exists_succAbove_eq|theorem map_update_sum|map_vecCons_add|map_vecCons_smul' <snapshot>/mathlib/Mathlib; rg -n 'theorem det_updateCol_smul|theorem det_updateColumn_smul' <snapshot>/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean; rg -n 'det_to_matrix_orthonormalBasis_real|theorem coe_mk|theorem basisFun_apply' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `lean -DautoImplicit=false /tmp/no-split/{Types,Assembly,ChildA,ChildB,ChildC,All,Inst,Names}.lean with LEAN_PATH taken from .lake/build/lib/lean/GMT/Ch07/Submission.trace; #print axioms on the parent and the three children`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-44555cebd5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-44555cebd5/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-44555cebd5/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/LinearIndependent/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/GroupTheory/Perm/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/GroupTheory/Perm/Sign.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/SuccPred.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/tmp/no-split/Types.lean`
- `/tmp/no-split/Assembly.lean`
- `/tmp/no-split/ChildA.lean`
- `/tmp/no-split/ChildB.lean`
- `/tmp/no-split/ChildC.lean`
- `/tmp/no-split/All.lean`
- `/tmp/no-split/Inst.lean`
- `/tmp/no-split/Names.lean`

Pins match.
- Snapshot manifest: project b4d606db and Mathlib 25730c7c, equal to workspace HEAD, .lake/packages/mathlib and the compiled lake-packages-25730c7c/mathlib.
- SimonGMT is at 2b366308.
- Submission.lean is byte-identical to the snapshot Contract.lean (sha256 e4148e7f…).

Library.
- Covector E n is E [⋀^Fin n]→L[ℝ] ℝ (SimonGMT Chapter06/Forms.lean:31).
- Everything needed exists in the snapshot Mathlib:
  - Matrix.det_succ_column_zero (Matrix/Determinant/Basic.lean:734) and Matrix.det_updateCol_smul (:404).
  - Module.Basis.det_apply and det_self (Determinant.lean:607, 610).
  - Module.Basis.ext_alternating, AlternatingMap.map_perm, map_linearDependent and map_vecCons_add/smul (Alternating/Basic.lean:907, 672, 784, 804/809); curryLeft_apply_apply (Alternating/Curry.lean:43).
  - OrthonormalBasis.det_to_matrix_orthonormalBasis_real and OrthonormalBasis.mk (PiL2.lean:992, 712).
  - Submodule.finrank_orthogonal_span_singleton (Projection/FiniteDimensional.lean:125); orthonormal_iff_ite and Orthonormal.comp_linearIsometry (Orthonormal.lean:82, 315).
  - Fin.sign_cycleRange and cycleRange_symm_zero/succ (Perm/Fin.lean:225, 258, 262); Fin.exists_succAbove_eq (Data/Fin/SuccPred.lean:661); Fin.cons_update (Fin/Tuple/Basic.lean:143); linearIndependent_finCons (LinearIndependent/Lemmas.lean:677).
- No Mathlib or SimonGMT lemma states the n-covector = det[φ_β, ·] identity or the oriented normal frame directly.

DAG.
- No node has any of the three child types. The closest accepted nodes (dgoj_covector_eq_det_mul_of_mem_span, cmr_cc_det_covector_exists, cmr_cc_det_covector_basis_kronecker) have different types, so nothing is reused.
- The three new names appear in none of the 936 dag.json nodes and in no GMT/*.lean file at any of the 1662 ref tips.

Lean.
- Types.lean elaborates the three child types.
- Assembly.lean proves the byte-identical frozen parent type from the three children taken as axioms. `#print axioms` gives only those three plus propext, Classical.choice and Quot.sound.
- All.lean contains complete proofs of all three children and the parent; every one depends only on propext, Classical.choice and Quot.sound.
- Inst.lean confirms the matrix layout and instances: the constructed object is a genuine Matrix (Fin (n+1)) (Fin (n+1)) ℝ, its det agrees with Module.Basis.det, the Laplace layout holds by rfl, `.ofLp` gives coordinates, and `inner ℝ` is the dot product.
- Names.lean confirms that all 41 lemma names cited in the child proofs exist.
