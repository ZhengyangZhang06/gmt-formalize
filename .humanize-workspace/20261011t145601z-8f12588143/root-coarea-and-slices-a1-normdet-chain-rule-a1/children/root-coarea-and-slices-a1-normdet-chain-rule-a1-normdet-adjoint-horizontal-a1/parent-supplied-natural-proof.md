# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_and_slices-a1.normdet_chain_rule-a1`
- Child DAG node: `root.coarea_and_slices-a1.normdet_chain_rule-a1.normdet_adjoint_horizontal-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent-supplied proof of coarea_normDet_chain_rule, step 1(iii). This is the fact about normDet of adjoints that steps 3–4 use for P = L and P = Γ, here stated for arbitrary finite-dimensional real inner product spaces.
Notation: normDet = LinearMap.normDet. P* = LinearMap.adjoint P, characterized by ⟨P*y, x⟩ = ⟨y, Px⟩. S^⊥ is the orthogonal complement of S. H := (ker P)^⊥ ⊆ X, and ι_H : H → X is the inclusion.

1. (Kernel and range of the adjoint.) For any linear P : X → Y and y ∈ Y: y ∈ ker P* ⟺ ⟨P*y, x⟩ = 0 for all x ∈ X ⟺ ⟨y, Px⟩ = 0 for all x ⟺ y ∈ (range P)^⊥. So ker P* = (range P)^⊥ (Mathlib LinearMap.orthogonal_range). Dually, range P* = (ker P)^⊥ = H (LinearMap.orthogonal_ker). Both use finite-dimensionality.

2. (Second conjunct.) Assume P is not surjective, so range P ≠ Y. In a finite-dimensional inner product space, S^⊥ = 0 holds iff S is the whole space (Submodule.orthogonal_eq_bot_iff). Hence (range P)^⊥ ≠ 0, and by step 1, ker P* ≠ 0. A linear map with nonzero kernel has normDet 0 (LinearMap.normDet_eq_zero_iff_ker_ne_bot). Therefore normDet(P*) = 0.

3. (First conjunct: the horizontal map is an isomorphism.) Assume P is surjective and put h := P ∘ ι_H : H → Y.
- h is injective: if u ∈ H and Pu = 0, then u ∈ ker P ∩ (ker P)^⊥ = {0}.
- h is surjective: given y ∈ Y, pick x with Px = y. Since ker P is finite-dimensional it has an orthogonal projection, so x = k + u with k ∈ ker P and u ∈ H. Then h(u) = Px − Pk = y.
So h is a linear isomorphism and dim H = dim Y.

4. (Corestriction of P*.) By step 1, P*y ∈ H for every y ∈ Y. So P* = ι_H ∘ P', where P' : Y → H is the codomain restriction of P* (LinearMap.codRestrict). Corestriction does not change normDet (LinearMap.normDet_codRestrict), so normDet(P*) = normDet(P').

5. (P' is the adjoint of h.) For y ∈ Y and u ∈ H: ⟨P'y, u⟩_H = ⟨P*y, u⟩_X = ⟨y, Pu⟩_Y = ⟨y, h u⟩_Y. By uniqueness of the adjoint (LinearMap.eq_adjoint_iff), P' = h*.

6. (Adjoints between equal-dimensional spaces.) Let d := dim H = dim Y (step 3). Choose orthonormal bases (e_i) of H and (f_i) of Y indexed by the same set Fin d, for example stdOrthonormalBasis with one of them reindexed by the dimension equality. When both orthonormal bases share a finite index set, normDet is |det| of the matrix (LinearMap.normDet_eq_norm_det_toMatrix). Let M be the matrix of h in the bases (e_i), (f_i). The matrix of h* in the bases (f_i), (e_i) has entries ⟨e_i, h* f_j⟩ = ⟨h e_i, f_j⟩ = M_{ji}, so it is Mᵀ (LinearMap.toMatrix_adjoint). Since det Mᵀ = det M (Matrix.det_conjTranspose over ℝ), normDet(h*) = normDet(h).

7. (Conclusion of the first conjunct.) normDet(P*) = normDet(P') = normDet(h*) = normDet(h) = normDet(P ∘ ι_H). In Lean, P ∘ ι_H is P ∘ₗ (LinearMap.ker P)ᗮ.subtype. ∎

Lean note: steps 1–7 are exactly the kernel-checked SimonGMT lemmas in Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean:
- coareaLinearJacobian P := P.adjoint.normDet.
- coareaHorizontalLinear P := P.domRestrict P.kerᗮ, which is definitionally P ∘ₗ P.kerᗮ.subtype.
- coareaHorizontalLinear_normDet, coareaLinearJacobian_eq_zero_iff and normDet_adjoint_of_finrank_eq.
After adding import Poincare.SimonGMT.Chapter02.CoareaLinearAlgebra to Submission.lean, the theorem is proved by ⟨fun hP => (Poincare.SimonGMT.Chapter02.coareaHorizontalLinear_normDet hP).symm, fun hP => (Poincare.SimonGMT.Chapter02.coareaLinearJacobian_eq_zero_iff P).mpr hP⟩. This was checked in a scratch file; axioms propext, Classical.choice, Quot.sound.

## Key steps

1. ker P* = (range P)^⊥ and range P* = (ker P)^⊥.
2. If P is not surjective then ker P* ≠ 0, so normDet(P*) = 0.
3. If P is surjective then h = P ∘ ι_{(ker P)^⊥} : (ker P)^⊥ → Y is a linear isomorphism, so dim (ker P)^⊥ = dim Y.
4. P* corestricted to (ker P)^⊥ equals h*, and corestriction preserves normDet.
5. Between equal-dimensional spaces normDet(h*) = normDet(h), because their matrices in orthonormal bases are transposes.

## Reference use

### local-project

Queries:
- `cat mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean (normDet, normDet_eq_norm_det_toMatrix_rangeRestrict, normDet_eq_zero_iff_ker_ne_bot, normDet_eq_norm_det_toMatrix, normDet_comp, normDet_comp_of_finrank_eq, normDet_codRestrict, normDet_of_subsingleton, normDet_sq)`
- `rg -l "normDet" mathlib/Mathlib project`
- `rg -l "normDet" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare`
- `grep -n "^theorem\|^def" Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean (coareaLinearJacobian, coareaLinearJacobian_eq_zero_iff, normDet_adjoint_of_finrank_eq, coareaHorizontalLinear, coareaHorizontalLinear_normDet)`
- `grep -rn "theorem det_prodMap\|theorem det_restrict\|det_quotient\|theorem det_fromBlocks" mathlib/Mathlib/LinearAlgebra/Determinant.lean mathlib/Mathlib/LinearAlgebra/Matrix/ mathlib/Mathlib/LinearAlgebra/Prod.lean`
- `grep -rln "fromBlocks" mathlib/Mathlib/LinearAlgebra mathlib/Mathlib/Analysis/InnerProductSpace`
- `grep -rn "def orthogonalDecomposition\|OrthonormalBasis.prod\|theorem Orthonormal.sum" mathlib/Mathlib/Analysis/InnerProductSpace/`
- `grep -n "theorem sub_.*mem_orthogonal\|theorem inner_orthogonalProjectionOnto\|theorem orthogonalProjectionOnto_eq_zero_iff" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `grep -n "theorem repr_apply_apply\|theorem coe_toBasis_repr_apply\|theorem coe_toBasis\|theorem map_apply\|theorem reindex_apply" mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `cmp local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean`
- `python3 -I: gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch03.main_theorem') and lean_contract.validate_lean_statement on the three child types`
- `lake env lean GMT/Scratch/NDCRSplit3.lean (parent assembly with the exact frozen type against sorry'd child stubs)`
- `lake env lean GMT/Scratch/NDCRSplit3Proofs.lean, GMT/Scratch/NDCRSplit3Block.lean, GMT/Scratch/NDCRSplit3Full.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/ProdL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/NDCRSplit3.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/NDCRSplit3Full.lean`

Mathlib 25730c7c supplies the normDet API this proof needs:
- normDet: normDet_eq_norm_det_toMatrix(_rangeRestrict), normDet_codRestrict, normDet_comp(_of_finrank_eq), normDet_eq_zero_iff_ker_ne_bot.
- Adjoints: LinearMap.orthogonal_ker and LinearMap.orthogonal_range.
- Bases: OrthonormalBasis.prod and Submodule.orthogonalDecomposition (ProdL2.lean).
- Block determinant: Matrix.det_fromBlocks_zero₂₁.
- Projections: Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, sub_starProjection_mem_orthogonal, orthogonal_orthogonal.

No match: Mathlib has no normDet lemma for adjoints, for block-triangular maps, or for compositions through orthogonal projections; rg 'normDet' hits only NormDet.lean. LinearMap.det_eq_det_mul_det exists only for endomorphisms with an invariant subspace and is not needed.

SimonGMT Chapter02/CoareaLinearAlgebra.lean contains coareaHorizontalLinear_normDet, coareaLinearJacobian_eq_zero_iff and normDet_adjoint_of_finrank_eq, which together are child 1. The Contract does not import this file transitively (checked with #check: unknown identifier), but Submission.lean may import it. The snapshot Contract is byte-identical to the workspace Contract.

Scratch checks:
- The three child types elaborate in the comparator's replayed scope.
- The exact frozen parent type is assembled from them.
- All three children are proved; the parent's axioms are [propext, Classical.choice, Quot.sound].
- A monolithic proof hit whnf heartbeat timeouts on the doubly nested submodule W ≤ ↥T. The generic children avoid it.
