# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1`
- Child DAG node: `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1.divergence_term-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 4 and 5 of the parent proof (coordinates of Dψ_j(Lx)∘L and the divergence term), with ℓ in place of Dψ_j(Lx).

Notation.
- λ_i := (EuclideanSpace.proj i).comp L for i ∈ Fin (m+1), so λ_i(v) = (Lv)_i.
- e_i := EuclideanSpace.single i 1.
- β := λ∘j.succAbove, i.e. β(k) = λ_{j.succAbove k} = (EuclideanSpace.proj (j.succAbove k)).comp L.
- wedge(α) := wedgeCovectors (m+1) α.

1. Coordinate expansion of ℓ∘L. Let v ∈ ℝ^P and b := EuclideanSpace.basisFun (Fin (m+1)) ℝ, the standard orthonormal basis. Then
 Lv = Σ_i (b.repr (Lv))_i • b_i = Σ_i (Lv)_i • e_i,
 by OrthonormalBasis.sum_repr, EuclideanSpace.basisFun_repr and EuclideanSpace.basisFun_apply. Since ℓ is linear (map_sum, map_smul),
 ℓ(Lv) = Σ_i (Lv)_i·ℓ(e_i) = Σ_i ℓ(e_i)·λ_i(v).
 Evaluation of a finite sum of scalar multiples of functionals is the corresponding sum of values, and v is arbitrary. So by extensionality ℓ.comp L = Σ_i ℓ(e_i) • λ_i in (ℝ^P)^*.

2. Linearity in the first slot. Apply the sibling theorem wedge_cons_linear (Submission.rpn_pfd_wedge_cons_isLinearMap) to P, m and β. The map Λ(γ) := wedge(Fin.cons γ β) is ℝ-linear; write Λ also for the associated linear map (IsLinearMap.mk'). A linear map commutes with finite linear combinations (map_sum, map_smul), so by Step 1
 wedge(Fin.cons (ℓ.comp L) β) = Λ(Σ_i ℓ(e_i)•λ_i) = Σ_i ℓ(e_i)•Λ(λ_i) = Σ_i ℓ(e_i)•wedge(Fin.cons λ_i β).

3. The sign lemma. Apply the sibling theorem wedge_cons_sign (Submission.rpn_pfd_wedge_cons_succAbove_sign) to P, m, l := λ and j. Here Fin.cons (l i) (k ↦ l(j.succAbove k)) is literally Fin.cons λ_i β. It gives:
 (a) wedge(Fin.cons λ_j β) = (−1)^j • wedge(λ);
 (b) wedge(Fin.cons λ_i β) = 0 for every i ≠ j.

4. Collapse of the sum. By Step 3(b), every term of the sum in Step 2 with i ≠ j is ℓ(e_i)•0 = 0 (smul_zero). Since j ∈ Finset.univ, Finset.sum_eq_single j leaves only the j-th term. By Step 3(a), smul_smul and commutativity of multiplication in ℝ, it equals
 ℓ(e_j)•((−1)^j•wedge(λ)) = (ℓ(e_j)·(−1)^j)•wedge(λ) = ((−1)^j·ℓ(e_j))•wedge(λ).

5. Combining Steps 2 and 4,
 wedgeCovectors (m+1) (Fin.cons (ℓ.comp L) (k ↦ (EuclideanSpace.proj (j.succAbove k)).comp L)) = ((−1)^j·ℓ(EuclideanSpace.single j 1)) • wedgeCovectors (m+1) (i ↦ (EuclideanSpace.proj i).comp L),
 which is the claim. ∎

## Key steps

1. ℓ.comp L = Σ_i ℓ(e_i)•λ_i, by expanding Lv in EuclideanSpace.basisFun and using linearity of ℓ.
2. Sibling wedge_cons_linear: γ ↦ wedge(Fin.cons γ (λ∘j.succAbove)) is linear, so wedge(Fin.cons (ℓ∘L) β) = Σ_i ℓ(e_i)•wedge(Fin.cons λ_i β).
3. Sibling wedge_cons_sign: the i = j term is (−1)^j•wedge(λ), and every term with i ≠ j vanishes.
4. Finset.sum_eq_single j and smul_smul give ((−1)^j·ℓ(e_j))•wedge(λ).

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
