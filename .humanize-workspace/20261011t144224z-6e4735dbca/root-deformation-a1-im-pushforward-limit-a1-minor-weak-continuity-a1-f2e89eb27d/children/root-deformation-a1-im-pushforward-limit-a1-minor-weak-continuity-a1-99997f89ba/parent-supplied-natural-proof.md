# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1.cofactor_leibniz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 2 of the parent proof (cofactor formula): the Laplace expansion along the first row combined with the Leibniz formula, applied to the auxiliary matrix whose first row is a unit vector (standard linear algebra; Mathlib Matrix.det_succ_row_zero, Matrix.det_apply', Matrix.det_transpose).

Notation. S := Equiv.Perm (Fin (r+1)); for σ ∈ S, sgn σ := ((Equiv.Perm.sign σ : ℤ) : ℝ) ∈ {1, −1}; ε_q(σ) := sgn σ if σ(0) = q and ε_q(σ) := 0 otherwise (this is the factor `if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0` of the Lean statement). 𝟙_q := Pi.single q 1 : Fin (r+1) → ℝ, so (𝟙_q)_j = 1 if j = q and (𝟙_q)_j = 0 if j ≠ q. For t ∈ Fin r, t.succ ∈ Fin (r+1) is t+1, and 0 ∈ Fin (r+1) is the first index.

1. (Auxiliary matrix.) Let A be the (r+1)×(r+1) real matrix whose row 0 is 𝟙_q and whose row t.succ is N_t (t ∈ Fin r), i.e. A_{0,j} = (𝟙_q)_j and A_{t.succ,j} = N_{t,j} for j ∈ Fin (r+1). In Lean, A := Matrix.of (Matrix.vecCons (Pi.single q 1) N); its rows are evaluated by Matrix.cons_val_zero and Matrix.cons_val_succ. We compute det A in two ways.

2. (Laplace expansion along row 0.) By Matrix.det_succ_row_zero,
 det A = Σ_{j ∈ Fin (r+1)} (−1)^j · A_{0,j} · det(A.submatrix Fin.succ j.succAbove).
 For j ≠ q the factor A_{0,j} = (𝟙_q)_j vanishes, so every term with j ≠ q is 0 and the sum equals its term j = q (Finset.sum_eq_single q; q ∈ Finset.univ). Since A_{0,q} = 1, that term is (−1)^q · det(A.submatrix Fin.succ q.succAbove). The r×r matrix A.submatrix Fin.succ q.succAbove has (t, s) entry A_{t.succ, q.succAbove(s)} = N_{t, q.succAbove(s)}, so it is equal (entrywise) to Matrix.of (fun t s => N t (q.succAbove s)). Hence
 det A = (−1)^q · det(N_{t, q.succAbove(s)})_{t,s ∈ Fin r}.   (a)
 For r = 0 this is still correct: the submatrix is the empty matrix, whose determinant is 1.

3. (Leibniz formula.) det A = det Aᵀ (Matrix.det_transpose), and by the Leibniz formula det M = Σ_{σ∈S} sgn σ · Π_{i ∈ Fin (r+1)} M_{σ(i), i} (Matrix.det_apply') applied to M = Aᵀ, whose (σ(i), i) entry is A_{i, σ(i)},
 det A = Σ_{σ∈S} sgn σ · Π_{i ∈ Fin (r+1)} A_{i, σ(i)}.   (b)

4. (Splitting off row 0.) Fix σ ∈ S. Splitting the product over Fin (r+1) into the factor i = 0 and the factors i = t.succ, t ∈ Fin r (Fin.prod_univ_succ),
 Π_i A_{i,σ(i)} = A_{0,σ(0)} · Π_{t ∈ Fin r} A_{t.succ, σ(t.succ)} = (𝟙_q)_{σ(0)} · Π_{t ∈ Fin r} N_{t, σ(t.succ)}.
 If σ(0) = q, then (𝟙_q)_{σ(0)} = 1, so sgn σ · Π_i A_{i,σ(i)} = sgn σ · Π_t N_{t,σ(t.succ)} = ε_q(σ) · Π_t N_{t,σ(t.succ)}. If σ(0) ≠ q, then (𝟙_q)_{σ(0)} = 0 (Pi.single_apply), and both sgn σ · Π_i A_{i,σ(i)} and ε_q(σ) · Π_t N_{t,σ(t.succ)} are 0. In both cases
 sgn σ · Π_i A_{i,σ(i)} = ε_q(σ) · Π_{t ∈ Fin r} N_{t, σ(t.succ)}.   (c)

5. (Conclusion.) Summing (c) over σ ∈ S (Finset.sum_congr) and combining with (a) and (b):
 (−1)^q · det(N_{t, q.succAbove(s)})_{t,s} = det A = Σ_{σ∈S} ε_q(σ) · Π_{t ∈ Fin r} N_{t, σ(t.succ)},
 which is exactly the asserted identity. ∎

Formalization notes (no new mathematics). The following script was checked with lake env lean after import GMT.Ch06.Submission in the exact comparator scope (namespace GMT.Ch06 with the frozen open commands, after the noncomputable section); it compiles without warnings and #print axioms reports only propext, Classical.choice and Quot.sound. It may be used verbatim:
theorem Submission.deformation_ipl_mwc_pi_cofactor_leibniz : ∀ (r : ℕ) (N : Fin r → Fin (r + 1) → ℝ) (q : Fin (r + 1)), (-1 : ℝ) ^ (q : ℕ) * Matrix.det (Matrix.of fun t s : Fin r => N t (q.succAbove s)) = ∑ σ : Equiv.Perm (Fin (r + 1)), (if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0) * ∏ t : Fin r, N t (σ t.succ) := by
  intro r N q
  let A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ := Matrix.of (Matrix.vecCons (Pi.single q 1) N)
  have h1 : A.det = (-1 : ℝ) ^ (q : ℕ) * Matrix.det (Matrix.of fun t s : Fin r => N t (q.succAbove s)) := by
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single q]
    · have hsub : A.submatrix Fin.succ q.succAbove = Matrix.of fun t s : Fin r => N t (q.succAbove s) := by
        ext t s
        simp [A]
      rw [hsub]
      simp [A]
    · intro j _ hj
      simp [A, hj]
    · intro h
      exact absurd (Finset.mem_univ q) h
  have h2 : A.det = ∑ σ : Equiv.Perm (Fin (r + 1)), (if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0) * ∏ t : Fin r, N t (σ t.succ) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Fin.prod_univ_succ]
    simp only [A, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, Pi.single_apply]
    split_ifs <;> ring
  rw [← h1, h2]

## Key steps

1. Auxiliary (r+1)×(r+1) matrix A = Matrix.of (Matrix.vecCons (Pi.single q 1) N): row 0 is the unit vector 𝟙_q, row t.succ is N_t.
2. Laplace along row 0 (Matrix.det_succ_row_zero, Finset.sum_eq_single q): det A = (−1)^q·det(N_{t,q.succAbove s}), since A.submatrix Fin.succ q.succAbove = Matrix.of (fun t s => N t (q.succAbove s)).
3. Leibniz via the transpose (Matrix.det_transpose, Matrix.det_apply'): det A = Σ_σ sgn σ·Π_i A_{i,σ(i)}.
4. Split row 0 (Fin.prod_univ_succ, Pi.single_apply): sgn σ·Π_i A_{i,σ(i)} = (if σ 0 = q then sgn σ else 0)·Π_t N_{t,σ(t.succ)}; compare the two expressions of det A.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project, project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD (= project_commit)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (both identical)`
- `python3 -I over dag.json: nodes under root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1 (piola_identity at depth 4 with no deps; minor_ibp_smooth depends on it); regex piola|hessian|schwarz|symm|cofactor|leibniz|laplace|det_|perm|sign|swap|finsetProd|fderiv_sum|prod_rule|product rule|second deriv|isSymmSnd over titles, lean names and statements; duplicate lean_name scan (none)`
- `grep deformation_ipl_mwc_pi_ over dag.json, nodes/, GMT/, the snapshot project and simongmt/Poincare; git log --all -S deformation_ipl_mwc_pi_ (no match)`
- `rg -n 'isSymmSndFDerivAt|IsSymmSndFDerivAt|det_succ_row_zero|Piola|piola|cofactor' over simongmt/Poincare and the snapshot project`
- `rg -n in the snapshot Mathlib: 'theorem det_succ_row_zero|theorem det_apply'|theorem det_transpose' (LinearAlgebra/Matrix/Determinant/Basic.lean); 'theorem ContDiffAt.isSymmSndFDerivAt|def IsSymmSndFDerivAt' (Analysis/Calculus/FDeriv/Symmetric.lean); 'theorem HasFDerivAt.finsetProd|theorem fderiv_finsetProd|theorem HasFDerivAt.const_mul' (FDeriv/Mul.lean); 'theorem fderiv_clm_apply' (FDeriv/CompCLM.lean); 'theorem HasFDerivAt.sum|theorem fderiv_sum' (FDeriv/Add.lean); 'theorem sign_mul|theorem sign_swap' (GroupTheory/Perm/Sign.lean); 'theorem prod_univ_succ' (Algebra/BigOperators/Fin.lean)`
- `lake env lean /tmp/piola_decomp/build/Avail.lean and Names.lean (#check of every cited name under import GMT.Ch06.Submission); Closure.lean (#check of the SimonGMT Chapter08 Piola lemma under the frozen import)`
- `git show 3ceb8b21a8d3961c1d9a4aad2075a7d209773632:GMT/Ch06/Submission.lean | grep (how accepted children are declared)`
- `python3 -I /tmp/piola_decomp/scripts/gen.py (verifier lean_contract.validate_lean_statement plus gmt-compare child_modules in contract mode) and lake env lean on the four /tmp/piola_decomp/build/*_challenge.lean`
- `lake env lean on /tmp/piola_decomp/build/Assembly.lean, RefImpl2.lean, RefImpl2Compare.lean and Iso_{cofactor_leibniz,hessian_symm,fderiv_sum_prod,swap_cancel}.lean, with #print axioms`
- `python3 -I /tmp/piola_decomp/scripts/build_payload.py (re-validates key and name patterns and lean statements, and embeds the verified scripts)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-f2e89eb27d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-f2e89eb27d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-f2e89eb27d/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-f2e89eb27d/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/ConstancyPiola.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DeformationFamily.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/GroupTheory/Perm/Sign.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/BigOperators/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/piola_decomp/build/Avail.lean`
- `/tmp/piola_decomp/build/Names.lean`
- `/tmp/piola_decomp/build/Closure.lean`
- `/tmp/piola_decomp/build/cofactor_leibniz_challenge.lean`
- `/tmp/piola_decomp/build/hessian_symm_challenge.lean`
- `/tmp/piola_decomp/build/fderiv_sum_prod_challenge.lean`
- `/tmp/piola_decomp/build/swap_cancel_challenge.lean`
- `/tmp/piola_decomp/build/Assembly.lean`
- `/tmp/piola_decomp/build/RefImpl2.lean`
- `/tmp/piola_decomp/build/RefImpl2Compare.lean`
- `/tmp/piola_decomp/build/Iso_cofactor_leibniz.lean`
- `/tmp/piola_decomp/build/Iso_hessian_symm.lean`
- `/tmp/piola_decomp/build/Iso_fderiv_sum_prod.lean`
- `/tmp/piola_decomp/build/Iso_swap_cancel.lean`
- `/tmp/piola_decomp/scripts/gen.py`
- `/tmp/piola_decomp/scripts/build_payload.py`

The pinned revisions are confirmed: HEAD = project_commit d8d46c95, and Contract, Submission and the snapshot Contract are byte-identical.

Nothing existing can be reused. No DAG node, no SimonGMT lemma in the frozen import closure and no Mathlib lemma states the Piola identity, the restricted Leibniz cofactor formula or the swap cancellation. SimonGMT Chapter08 ConstancyPiola (chartTangentialDivergence_coordinate_test) is a different identity, for varifold charts, and is an unknown identifier under import GMT.Ch06.Submission. Chapter06 FormsDuality only uses det_succ_row_zero for wedgeCovectors_apply_det.

Every Mathlib name the children need exists in the snapshot and elaborates under the frozen import: Matrix.det_succ_row_zero, Matrix.det_apply', Matrix.det_transpose, Fin.prod_univ_succ, Pi.single_apply, ContDiffAt.isSymmSndFDerivAt, ContDiff.fderiv_right, ContDiff.differentiable, fderiv_clm_apply, HasFDerivAt.finsetProd, HasFDerivAt.const_mul, HasFDerivAt.sum, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap, Equiv.swap_apply_of_ne_of_ne, Equiv.mulRight, Equiv.sum_comp and Fintype.sum_ite_eq. Use sum_apply and smul_apply: ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, coe_sum' and coe_smul' are deprecated.

Accepted children are declared as theorem Submission.X inside namespace GMT.Ch06. The four new names deformation_ipl_mwc_pi_{cofactor_leibniz,hessian_symm,fderiv_sum_prod,swap_cancel} collide with nothing.

Lean checks:
- All four statements validate and elaborate in the generated comparator challenge modules (exit 0).
- The parent compiles from the four sorry'd children.
- A sorry-free, warning-free reference implementation of the four children and the parent compiles.
- Each child's script compiles in isolation.
- The comparator-style exact Submission.X check passes for all five frozen types.
- #print axioms reports only propext, Classical.choice and Quot.sound.
