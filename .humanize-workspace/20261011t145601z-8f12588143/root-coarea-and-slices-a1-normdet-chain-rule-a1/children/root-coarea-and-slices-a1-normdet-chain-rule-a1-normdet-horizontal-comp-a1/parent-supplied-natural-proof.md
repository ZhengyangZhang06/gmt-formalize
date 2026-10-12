# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_and_slices-a1.normdet_chain_rule-a1`
- Child DAG node: `root.coarea_and_slices-a1.normdet_chain_rule-a1.normdet_horizontal_comp-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent-supplied proof of coarea_normDet_chain_rule, step 6 (Γ|_{K^⊥} = L|_W ∘ A₁₁, so |det(Γ|_{K^⊥})| = |det(L|_W)|·|det A₁₁|), together with the dimension count of step 4 (dim K^⊥ = dim W). Here A : ℝⁿ → T is replaced by an arbitrary bijective B : V → X, and L : T → ℝᵐ by an arbitrary L : X → Y.
Notation: K = ker Γ, W = (ker L)^⊥, and g := p_W ∘ B ∘ ι_{K^⊥} : K^⊥ → W.

1. (W^⊥ = ker L.) ker L is finite-dimensional, so it has an orthogonal projection and (ker L)^⊥⊥ = ker L (Submodule.orthogonal_orthogonal). Hence W^⊥ = ker L.

2. (Factorization of Γ on K^⊥.) Let u ∈ K^⊥ and x := Bu. Then x − p_W x ∈ W^⊥ (Submodule.sub_starProjection_mem_orthogonal; the coercion of p_W x to X is W.starProjection x). By step 1, L(x − p_W x) = 0, i.e. L(x) = L(p_W x). Therefore Γu = L(Bu) = L(p_W(Bu)) = (L ∘ ι_W)(g u). As linear maps K^⊥ → Y, this says Γ ∘ ι_{K^⊥} = (L ∘ ι_W) ∘ g.

3. (ker L = B(K).) If v ∈ K, then L(Bv) = Γv = 0, so Bv ∈ ker L. Conversely, for t ∈ ker L write t = Bv, using that B is surjective. Then Γv = L(Bv) = L(t) = 0, so v ∈ K and t = Bv ∈ B(K).

4. (dim K^⊥ = dim W.) B is injective, so it maps K isomorphically onto B(K) = ker L (Submodule.equivMapOfInjective); hence dim ker L = dim K. B is bijective, so dim X = dim V (LinearEquiv.ofBijective). By Submodule.finrank_add_finrank_orthogonal, dim K + dim K^⊥ = dim V and dim ker L + dim W = dim X. Hence dim K^⊥ = dim V − dim K = dim X − dim ker L = dim W.

5. (Multiplicativity of normDet.) If g : U → U' and h : U' → Z are linear, with U and U' finite-dimensional and dim U = dim U', then normDet(h ∘ g) = normDet(h)·normDet(g) (LinearMap.normDet_comp_of_finrank_eq). Apply it with U = K^⊥, U' = W, h = L ∘ ι_W and the dimension equality of step 4.

6. (Conclusion.) By steps 2 and 5, normDet(Γ ∘ ι_{K^⊥}) = normDet((L ∘ ι_W) ∘ g) = normDet(L ∘ ι_W)·normDet(p_W ∘ B ∘ ι_{K^⊥}). ∎

Surjectivity of L is not needed. This argument was checked in Lean in a scratch file; axioms propext, Classical.choice, Quot.sound.

## Key steps

1. W^⊥ = (ker L)^⊥⊥ = ker L, so L(Bu) = L(p_W(Bu)) and Γ∘ι_{K^⊥} = (L∘ι_W)∘(p_W∘B∘ι_{K^⊥}).
2. ker L = B(K); B is bijective, so dim K = dim ker L, dim V = dim X, and therefore dim K^⊥ = dim W.
3. LinearMap.normDet_comp_of_finrank_eq gives normDet(Γ∘ι_{K^⊥}) = normDet(L∘ι_W)·normDet(p_W∘B∘ι_{K^⊥}).

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
