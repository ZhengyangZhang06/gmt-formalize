# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1`
- Child DAG node: `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1.wedge_cons_sign-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 2 of the parent proof (sign lemma), with the details filled in.

Notation. For α : Fin (m+1) → (ℝ^P)^* write wedge(α) := wedgeCovectors (m+1) α.
- Two (m+1)-covectors are equal iff they agree at every v : Fin (m+1) → ℝ^P (ext).
- By SimonGMT wedgeCovectors_apply_det, wedge(α)(v) = det A(α, v), where A(α, v) is the (m+1)×(m+1) real matrix with entries A(α, v)_{a,b} = α_a(v_b) (row a, column b).
Fix l and j, and write l∘j.succAbove for k ↦ l(j.succAbove k).

Part (a).
1. Let σ := (Fin.cycleRange j).symm, a permutation of Fin (m+1). By Mathlib Fin.cycleRange_symm_zero, σ(0) = j. By Fin.cycleRange_symm_succ, σ(k.succ) = j.succAbove(k) for every k ∈ Fin m.
2. Hence Fin.cons (l j) (l∘j.succAbove) = l∘σ. Check this by cases on a ∈ Fin (m+1) (Fin.cases):
 - for a = 0, both sides equal l(j), by Fin.cons_zero and Step 1;
 - for a = k.succ, both sides equal l(j.succAbove k), by Fin.cons_succ and Step 1.
3. Fix v : Fin (m+1) → ℝ^P and let M := A(l, v). By Step 2, A(Fin.cons (l j) (l∘j.succAbove), v)_{a,b} = l_{σ(a)}(v_b) = M_{σ(a),b}. So this matrix is M.submatrix σ id, i.e. M with its rows permuted by σ. By Mathlib Matrix.det_permute, det(M.submatrix σ id) = sign(σ)·det M.
4. By Equiv.Perm.sign_symm, sign(σ) = sign(Fin.cycleRange j). By Fin.sign_cycleRange this equals (−1)^j in ℤˣ, and its image in ℝ is (−1 : ℝ)^j.
5. Combining Steps 3 and 4:
 wedge(Fin.cons (l j) (l∘j.succAbove))(v) = (−1)^j·det A(l, v) = (−1)^j·wedge(l)(v) = ((−1)^j • wedge(l))(v).
 Since v is arbitrary, wedge(Fin.cons (l j) (l∘j.succAbove)) = (−1)^j • wedge(l).

Part (b).
6. Let i ∈ Fin (m+1) with i ≠ j. By Mathlib Fin.exists_succAbove_eq applied to i ≠ j, there is k ∈ Fin m with j.succAbove(k) = i.
7. Fix v and let N := A(Fin.cons (l i) (l∘j.succAbove), v).
 - Row 0 of N is b ↦ l_i(v_b), by Fin.cons_zero.
 - Row k.succ of N is b ↦ l_{j.succAbove k}(v_b), by Fin.cons_succ; by Step 6 this is b ↦ l_i(v_b).
 So rows 0 and k.succ of N coincide, and k.succ ≠ 0 (Fin.succ_ne_zero).
8. A square matrix with equal rows at two distinct indices has determinant 0 (Matrix.det_zero_of_row_eq). Hence wedge(Fin.cons (l i) (l∘j.succAbove))(v) = det N = 0. Since v is arbitrary, wedge(Fin.cons (l i) (l∘j.succAbove)) = 0.

9. Parts (a) and (b) together are the stated conjunction. ∎

## Key steps

1. wedgeCovectors_apply_det reduces both claims to determinants of the value matrices (α_a(v_b)); use ext over v.
2. σ := (cycleRange j).symm has σ 0 = j and σ k.succ = j.succAbove k, so Fin.cons l_j (l∘j.succAbove) = l∘σ and its matrix is M.submatrix σ id.
3. Matrix.det_permute, Equiv.Perm.sign_symm and Fin.sign_cycleRange give the factor (−1)^j.
4. For i ≠ j, Fin.exists_succAbove_eq gives k with j.succAbove k = i. Rows 0 and k.succ coincide, so Matrix.det_zero_of_row_eq gives 0.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c95; mathlib_commit 25730c7c)`
- `rg -n 'abbrev Eucl|^theorem main_theorem|^namespace|^open' project/GMT/Ch06/Contract.lean (snapshot)`
- `rg -n '^noncomputable def extDeriv |theorem sign_cycleRange|theorem cycleRange_symm_zero|theorem cycleRange_symm_succ|theorem det_permute \(|theorem det_zero_of_row_eq|lemma exists_succAbove_eq \{|theorem sign_symm \(|lemma alternatizeUncurryFinCLM_apply|theorem alternatizeUncurryFin_add \(|theorem alternatizeUncurryFin_smul \{|theorem HasFDerivAt.sum \(|theorem HasFDerivAt.smul_const \(|theorem HasFDerivAt.const_mul \(|theorem HasFDerivAt.mul \(|theorem basisFun_apply|theorem basisFun_repr|abbrev EuclideanSpace.proj ' on the snapshot's mathlib/Mathlib files listed`
- `rg -ln 'def wedgeCovectors' in the snapshot (no match: SimonGMT is not in the snapshot; used the pinned lake package instead)`
- `grep -n 'wedgeCovectors' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `grep -n 'Covector|DifferentialForm|exteriorDerivative' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `python3 scan of dag.json lean_statements for wedgeCovectors/extDeriv/alternatizeUncurryFin/Fin.cons/succAbove/cycleRange (no accepted node with a reusable identical type)`
- `python3 reserved-name scan of dag.json and nodes/*/decomposition-v*.json (467 names; no collision with rpn_pfd_*)`
- `python3 verifier/lean_contract.py validate_lean_statement on the 4 child statements (all valid)`
- `python3 verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') to replay the child comparator header`
- `lake env lean /tmp/pfd_decomp/T1.lean (glue proves the frozen parent type from the four child types; exit 0)`
- `lake env lean /tmp/pfd_decomp/T2.lean, T3.lean (child proofs; fixed coe_zero and explicit smul_const argument)`
- `lake env lean /tmp/pfd_decomp/EndToEnd.lean (4 children + glue + comparator challenge/solution forms; #print axioms = [propext, Classical.choice, Quot.sound]; exit 0)`
- `python3 read of nodes/root-rectifiability-a1-projection-null-a1*/decomposition-v*.json and decomposition-audit-v3.json (sibling split precedents)`

Files inspected:
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/GroupTheory/Perm/Fin.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/GroupTheory/Perm/Sign.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/SuccPred.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-potential-form-derivative-a1/parent-child-handoff.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1/decomposition-audit-v3.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1/decomposition-v1.json`
- `/tmp/pfd_decomp/T1.lean`
- `/tmp/pfd_decomp/EndToEnd.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. Mathlib defines extDeriv ω x := alternatizeUncurryFin (fderiv ω x) (DifferentialForm/Basic.lean:72).

Lemmas the children use, all present in the snapshot:
- signs: Fin.sign_cycleRange, cycleRange_symm_zero, cycleRange_symm_succ (Perm/Fin.lean:225,258,262); Equiv.Perm.sign_symm (Perm/Sign.lean:385);
- determinants: Matrix.det_permute, det_zero_of_row_eq (Determinant/Basic.lean:216,373);
- Fin.exists_succAbove_eq (Data/Fin/SuccPred.lean:661);
- linearity of Alt: alternatizeUncurryFinCLM_apply, alternatizeUncurryFin_add, alternatizeUncurryFin_smul (Alternating/Uncurry/Fin.lean:129,149,160);
- calculus: HasFDerivAt.sum, smul_const, mul, const_mul (FDeriv/Add.lean:418; FDeriv/Mul.lean:126,205,352);
- coordinates: EuclideanSpace.proj, basisFun_apply, basisFun_repr (PiL2.lean:285,806,810).

SimonGMT is absent from the snapshot (no match). In the pinned simongmt package, FormsDuality.lean:115 defines wedgeCovectors (n+1) α = alternatizeUncurryFin ((α 0).smulRight (wedgeCovectors n (Fin.tail α))), and :127 proves wedgeCovectors_apply_det.

No accepted DAG node has an identical reusable type, so all four children are new. Each child type elaborates in the replayed comparator scope. All four children and the parent glue are proved end to end with only propext, Classical.choice and Quot.sound.
