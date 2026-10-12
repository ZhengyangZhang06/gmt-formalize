# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.flat_jacobian-a1`
- Child DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.flat_jacobian-a1.block_normdet-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent's supplied proof, steps 1 and 6 (parent (ii)). The only change is that the second component of T is a linear map S given by hypothesis, and only surjectivity of Γ is assumed. The argument below uses nothing else.

Notation: V := ℝ^{m+k}, K := ker Γ ⊆ V, K^⊥ := its orthogonal complement, ι_K : K → V the inclusion, Γ_⊥ := Γ.domRestrict K^⊥ : K^⊥ → ℝᵐ, S_⊥ := S.domRestrict K^⊥ : K^⊥ → ℝᵏ, S_K := S∘ι_K : K → ℝᵏ. Both P = WithLp 2 (ℝᵐ × ℝᵏ) and WithLp 2 (K^⊥ × K) carry the L² inner product ⟨x, x'⟩ = ⟨x.fst, x'.fst⟩ + ⟨x.snd, x'.snd⟩ (WithLp.prod_inner_apply).

Facts used:
(F1) LinearMap.normDet_comp_of_finrank_eq: if f : U → U' and g : U' → W are linear and finrank U = finrank U', then normDet(g∘f) = normDet(g)·normDet(f).
(F2) LinearIsometry.normDet_eq_one: a linear isometry has normDet 1.
(F3) LinearMap.normDet_eq_norm_det_toMatrix: if β and γ are orthonormal bases of U and U' indexed by the same finite type, then normDet(f) = ‖det(toMatrix β γ f)‖. Over ℝ this is |det(toMatrix β γ f)|.
(F4) Matrix.det_fromBlocks_zero₁₂: det(fromBlocks A 0 C D) = det A · det D for square blocks A, D.

1. (Dimensions.) Since Γ is surjective, range Γ = ℝᵐ. Rank–nullity (LinearMap.finrank_range_add_finrank_ker, packaged as SimonGMT coarea_kernel_finrank) gives finrank K = finrank V − finrank ℝᵐ = (m + k) − m = k (finrank_euclideanSpace_fin). By Submodule.finrank_add_finrank_orthogonal, finrank K + finrank K^⊥ = m + k, so finrank K^⊥ = m.

2. (Orthogonal coordinates.) Define c : WithLp 2 (K^⊥ × K) → V by c(toLp(a, b)) := a + b. It is a linear isometric equivalence:
- it is linear;
- it is bijective, because V = K^⊥ ⊕ K, so every v ∈ V decomposes uniquely as v = a + b with a ∈ K^⊥ and b ∈ K;
- it preserves norms, because ⟨a, b⟩ = 0 gives ‖a + b‖² = ‖a‖² + ‖b‖² = ‖toLp(a, b)‖².
In Lean, c := (SimonGMT coareaCoordinates Γ).symm, and coareaCoordinates_symm_apply gives c p = p.fst + p.snd. Since c is a linear equivalence, finrank WithLp 2 (K^⊥ × K) = finrank V. So (F1) and (F2) give normDet(T∘c) = normDet(T)·normDet(c) = normDet(T)·1 = normDet(T).

3. (Formula for T∘c.) Let a ∈ K^⊥ and b ∈ K. Then Γ b = 0. By the hypotheses on the components of T, (T∘c)(toLp(a, b)) = T(a + b) has first component Γ(a + b) = Γ a = Γ_⊥ a and second component S(a + b) = S_⊥ a + S_K b. In particular:
- (T∘c)(toLp(a, 0)) has components Γ_⊥ a and S_⊥ a;
- (T∘c)(toLp(0, b)) has components 0 and S_K b.

4. (Bases.) By step 1, choose an orthonormal basis β₁ of K^⊥ indexed by Fin m and an orthonormal basis β₂ of K indexed by Fin k (stdOrthonormalBasis reindexed by finCongr). Let γ₁ := EuclideanSpace.basisFun (Fin m) ℝ and γ₂ := EuclideanSpace.basisFun (Fin k) ℝ be the standard orthonormal bases of ℝᵐ and ℝᵏ. Let β := β₁.prod β₂ and γ := γ₁.prod γ₂ (OrthonormalBasis.prod, Mathlib Analysis/InnerProductSpace/ProdL2.lean). These are orthonormal bases of WithLp 2 (K^⊥ × K) and of P, both indexed by Fin m ⊕ Fin k. By OrthonormalBasis.prod_apply:
- β(inl j) = toLp(β₁ j, 0) and β(inr j) = toLp(0, β₂ j);
- γ(inl i) = toLp(γ₁ i, 0) and γ(inr i) = toLp(0, γ₂ i).

5. (Block form.) We have toMatrix β γ f i j = γ.repr(f(β j)) i (LinearMap.toMatrix_apply), and γ.repr x i = ⟨γ i, x⟩ for an orthonormal basis (OrthonormalBasis.repr_apply_apply). By the L² inner product, ⟨toLp(y, 0), x⟩ = ⟨y, x.fst⟩ and ⟨toLp(0, z), x⟩ = ⟨z, x.snd⟩. With step 3, the entries of M := toMatrix β γ (T∘c) are:
(a) M(inl i, inl j) = ⟨γ₁ i, Γ_⊥(β₁ j)⟩ = (toMatrix β₁ γ₁ Γ_⊥) i j;
(b) M(inl i, inr j) = ⟨γ₁ i, Γ(β₂ j)⟩ = ⟨γ₁ i, 0⟩ = 0, because β₂ j ∈ K = ker Γ;
(c) M(inr i, inl j) = ⟨γ₂ i, S(β₁ j)⟩ = (toMatrix β₁ γ₂ S_⊥) i j;
(d) M(inr i, inr j) = ⟨γ₂ i, S(β₂ j)⟩ = (toMatrix β₂ γ₂ S_K) i j.
Therefore M = Matrix.fromBlocks M₁₁ 0 M₂₁ M₂₂, where M₁₁ := toMatrix β₁ γ₁ Γ_⊥ (m × m), M₂₁ := toMatrix β₁ γ₂ S_⊥ and M₂₂ := toMatrix β₂ γ₂ S_K (k × k).

6. (Determinant.) By (F4), det M = det M₁₁ · det M₂₂.

7. (Conclusion.) Combine step 2, (F3) for (β, γ) indexed by Fin m ⊕ Fin k, and step 6. Then use |xy| = |x|·|y| and (F3) again for (β₁, γ₁) indexed by Fin m and (β₂, γ₂) indexed by Fin k:
normDet(T) = normDet(T∘c) = |det M| = |det M₁₁|·|det M₂₂| = normDet(Γ_⊥)·normDet(S_K) = normDet(Γ.domRestrict K^⊥)·normDet(S∘ι_K). ∎

## Key steps

1. Γ is surjective, so finrank(ker Γ) = k (rank–nullity / coarea_kernel_finrank) and finrank (ker Γ)^⊥ = m (Submodule.finrank_add_finrank_orthogonal).
2. c(toLp(a,b)) = a + b is a linear isometric equivalence WithLp 2 (K^⊥ × K) ≃ₗᵢ V, the inverse of SimonGMT coareaCoordinates Γ. So normDet(T∘c) = normDet(T) by normDet_comp_of_finrank_eq and LinearIsometry.normDet_eq_one.
3. Since Γ b = 0 for b ∈ K, the components of (T∘c)(toLp(a,b)) are Γ_⊥ a and S a + S b.
4. In the product orthonormal bases β₁.prod β₂ and γ₁.prod γ₂, toMatrix(T∘c) = fromBlocks M₁₁ 0 M₂₁ M₂₂, with M₁₁ = toMatrix(Γ.domRestrict K^⊥) and M₂₂ = toMatrix(S∘ι_K). The upper-right block vanishes because Γ = 0 on K.
5. Matrix.det_fromBlocks_zero₁₂ gives det = det M₁₁·det M₂₂. Applying normDet_eq_norm_det_toMatrix three times gives normDet(T) = normDet(Γ.domRestrict K^⊥)·normDet(S∘ι_K).

## Reference use

### local-project

Queries:
- `cat local-references/d498d77b74ea2063/manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean <workspace>/GMT/Ch03/Contract.lean (identical)`
- `rg -n "theorem normDet_comp_of_finrank_eq|theorem normDet_eq_norm_det_toMatrix|theorem _root_.LinearIsometry.normDet_eq_one|theorem normDet_id|theorem normDet_codRestrict" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean (lines 348, 182, 213, 220, 365)`
- `rg -n "fromBlocks|prodMap|block" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean (no match)`
- `rg -n "theorem det_fromBlocks_zero₁₂" mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean (line 728)`
- `rg -n "theorem det_prodMap|theorem det_prod" mathlib/Mathlib/LinearAlgebra/Determinant.lean (line 375, det_prodMap; block-diagonal only, not used)`
- `rg -n "fromBlocks" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean (lines 67-71: same toMatrix/fromBlocks/det technique for reflections)`
- `rg -n "def prod |theorem prod_apply|theorem prod_inner_apply|def orthogonalDecomposition" mathlib/Mathlib/Analysis/InnerProductSpace/ProdL2.lean (lines 57, 71, 46, 88)`
- `rg -n "def sndₗ|def fstₗ" mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean (lines 131, 124)`
- `rg -n "protected theorem repr_apply_apply|protected theorem coe_toBasis_repr_apply|protected theorem coe_toBasis |theorem basisFun_repr" mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean (lines 440, 490, 482, 810)`
- `rg -n "theorem finrank_add_finrank_orthogonal" mathlib/Mathlib/Analysis/InnerProductSpace/ (Projection/FiniteDimensional.lean:110)`
- `rg -n "theorem LinearMap.toMatrix_apply" mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean (line 619)`
- `rg -n "normDet.*fromBlocks|normDet_prod|normDet_prodMap|normDet_block" mathlib/Mathlib (full-tree search timed out on this filesystem; targeted NormDet.lean search above has no match)`
- `rg -n "pcoarea_flat|normDet_block|normDet_section" project/GMT (no match)`
- `cat lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean (coareaCoordinates, coareaCoordinates_symm_apply, coareaHorizontalLinear = domRestrict kerᗮ, normDet_adjoint_of_finrank_eq, coareaHorizontalLinear_normDet, coarea_kernel_finrank)`
- `python3 -I dag.json scan of lean_name/theorems over all 166 nodes for pcoarea_flat_normDet_block / pcoarea_flat_normDet_section (no collision)`
- `python3 -I /tmp/flatjac_split_scripts/gen_scope.py (gmt-compare.py contract_scope for GMT.Ch03.main_theorem + lean_contract.validate_lean_statement) then lake env lean GMT/Scratch/FlatJacSplitScope.lean`
- `lake env lean GMT/Scratch/FlatJacSplitAssembly.lean (parent frozen type from sorry-stub children; #print axioms)`
- `lake env lean GMT/Scratch/FlatJacSplitSection.lean and GMT/Scratch/FlatJacSplitBlock.lean (full child proofs)`
- `lake env lean GMT/Scratch/FlatJacSplitFull.lean (both children + parent proved, comparator-style targets `exact Submission.X`, #print axioms)`
- `lake env lean GMT/Scratch/FlatJacSplitInst.lean (rfl checks of L² inner product on WithLp 2 (Rn m × Rn k) and restricted inner products on ker Γ, (ker Γ)ᗮ; #synth gives WithLp.instProdInnerProductSpace)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/ProdL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-parametric-coarea-a1-flat-jacobian-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FlatJacSplitScope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FlatJacSplitAssembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FlatJacSplitSection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FlatJacSplitBlock.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FlatJacSplitFull.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FlatJacSplitInst.lean`

Snapshot pins: project d09bc8a, Mathlib 25730c7c, plus the pinned simongmt package. The snapshot Contract.lean is identical to the workspace one.

No-match results: Mathlib NormDet.lean has no block-triangular, product or fromBlocks normDet lemma, and the project has no pcoarea_flat_* or normDet_block/section declaration. So both children are new obligations.

Every cited fact exists in the snapshot and type-checks in the stated form:
- Mathlib: normDet_comp_of_finrank_eq, normDet_eq_norm_det_toMatrix, LinearIsometry.normDet_eq_one, normDet_id, Matrix.det_fromBlocks_zero₁₂, OrthonormalBasis.prod and prod_apply, WithLp.prod_inner_apply, WithLp.sndₗ, OrthonormalBasis.repr_apply_apply and coe_toBasis_repr_apply, LinearMap.toMatrix_apply, Submodule.finrank_add_finrank_orthogonal.
- SimonGMT: coareaCoordinates and coareaCoordinates_symm_apply, coarea_kernel_finrank, coareaHorizontalLinear_normDet.
Projection/FiniteDimensional.lean lines 67-71 already use the same toMatrix + fromBlocks + det technique.

Validation:
(1) Both frozen child types pass validate_lean_statement and elaborate in the comparator's replayed Contract scope after `import GMT.Ch03.Submission`. Instances were checked by rfl and #synth (WithLp.instProdInnerProductSpace; restricted inner products on submodules).
(2) With sorry-stub children, the parent assembly proves the exact frozen parent type.
(3) Full Lean proofs of both children and the parent compile. Comparator-style targets `exact Submission.X` typecheck, and the axioms are only propext, Classical.choice and Quot.sound.
(4) The proposed names do not collide with the 166 DAG nodes. The other branch's coarea_normDet_block_triangular has a different type and is not accepted, so it is not reused.
