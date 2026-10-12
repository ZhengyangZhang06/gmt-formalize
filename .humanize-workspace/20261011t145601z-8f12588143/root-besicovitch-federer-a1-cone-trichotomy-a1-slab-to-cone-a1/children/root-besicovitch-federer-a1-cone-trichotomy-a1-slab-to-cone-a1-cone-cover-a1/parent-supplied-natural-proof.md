# Parent-supplied natural-language proof

- Parent DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.slab_to_cone-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.slab_to_cone-a1.cone_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 3(b) of the parent proof, stated pointwise for y = x − a, with p_j y written out explicitly as Py + (y·u_j)u_j. (That this is the projection onto W ⊔ span{u_j} is the separate sibling lemma; it is not needed here.) Notation: x·y is the inner product and |·| the norm of E.

1. Dimension count. dim W + dim W^⊥ = dim E = n + ℓ (Submodule.finrank_add_finrank_orthogonal and finrank_euclideanSpace_fin). Since dim W = n, dim W^⊥ = ℓ.

2. Orthonormal basis of W^⊥.
 - Let v_j be u_j regarded as an element of the subspace W^⊥ (possible since u_j ∈ W^⊥).
 - Inner products and norms in W^⊥ are those of E, so (v_j)_{j ∈ Fin ℓ} is orthonormal in W^⊥ and hence linearly independent.
 - The family has card(Fin ℓ) = ℓ = dim W^⊥ members, and Fin ℓ is nonempty because ℓ ≥ 1. So it spans W^⊥ (LinearIndependent.span_eq_top_of_card_eq_finrank).
 - Therefore it is an orthonormal basis b of W^⊥ (OrthonormalBasis.mk), with b_k = u_k as vectors of E.

3. Py ⊥ u_k. For every k, Py ∈ W (Submodule.starProjection_apply_mem) and u_k ∈ W^⊥, so Py·u_k = 0 (Submodule.inner_right_of_mem_orthogonal).

4. Parseval for y − Py.
 - z := y − Py lies in W^⊥ (Submodule.sub_starProjection_mem_orthogonal).
 - Parseval's identity for the orthonormal basis b of W^⊥ (OrthonormalBasis.sum_sq_inner_right) gives |z|² = Σ_k (b_k·z)² = Σ_k (u_k·z)².
 - By symmetry and step 3, u_k·z = z·u_k = y·u_k − Py·u_k = y·u_k.
 - Hence |y − Py|² = Σ_k (y·u_k)².

5. Pythagoras. Let Q := W^⊥.starProjection. Then |y|² = |Py|² + |Qy|² (Submodule.norm_sq_eq_add_norm_sq_starProjection), and Qy = y − Py (Submodule.starProjection_orthogonal_val). With step 4,
 |y|² = |Py|² + Σ_k (y·u_k)².

6. Choice of j. Since Fin ℓ is finite and nonempty, choose j ∈ Fin ℓ with (y·u_k)² ≤ (y·u_j)² for every k (Finset.exists_max_image on Finset.univ). Then
 Σ_k (y·u_k)² ≤ Σ_k (y·u_j)² = ℓ·(y·u_j)².

7. Norm of Py + (y·u_j)u_j. Expanding the square (norm_add_sq_real, real_inner_smul_right, norm_smul),
 |Py + (y·u_j)u_j|² = |Py|² + 2(y·u_j)(Py·u_j) + (y·u_j)²|u_j|² = |Py|² + (y·u_j)²,
 by step 3 and |u_j| = 1.

8. s > 0. Otherwise s ≤ 0 gives s|y| ≤ 0 ≤ |Py|, contradicting |Py| < s|y|.

9. Comparison of squares.
 - Since 0 ≤ |Py| < s|y|, squaring gives |Py|² < (s|y|)² = s²|y|² (pow_lt_pow_left₀).
 - By step 5, s²|y|² = s²(|Py|² + Σ_k (y·u_k)²).
 - Since ℓ ≥ 1, |Py|² ≤ ℓ|Py|². Together with step 6 and s² ≥ 0, s²(|Py|² + Σ_k (y·u_k)²) ≤ s²(ℓ|Py|² + ℓ(y·u_j)²).
 - By step 7 and (√ℓ)² = ℓ (Real.sq_sqrt, ℓ ≥ 0), s²(ℓ|Py|² + ℓ(y·u_j)²) = (√ℓ)²·s²·|Py + (y·u_j)u_j|² = (√ℓ·s·|Py + (y·u_j)u_j|)².
 - Altogether |Py|² < (√ℓ·s·|Py + (y·u_j)u_j|)².

10. Square roots. R := √ℓ·s·|Py + (y·u_j)u_j| is ≥ 0, since √ℓ ≥ 0, s > 0 (step 8) and norms are ≥ 0; also |Py| ≥ 0. For nonnegative reals a and b, a² < b² implies a < b (lt_of_pow_lt_pow_left₀). Hence |Py| < √ℓ·s·|Py + (y·u_j)u_j| for the index j of step 6. ∎

## Key steps

1. dim W^⊥ = (n+ℓ) − n = ℓ, so the orthonormal family (u_k), viewed in W^⊥, is an orthonormal basis of W^⊥.
2. Py·u_k = 0, and Parseval with Pythagoras gives |y|² = |Py|² + Σ_k (y·u_k)².
3. Choose j maximizing (y·u_k)²; then Σ_k (y·u_k)² ≤ ℓ(y·u_j)² and |Py + (y·u_j)u_j|² = |Py|² + (y·u_j)².
4. s > 0, and |Py|² < s²|y|² ≤ s²(ℓ|Py|² + ℓ(y·u_j)²) = (√ℓ·s·|Py + (y·u_j)u_j|)².
5. Both sides are nonnegative, so taking square roots gives |Py| < √ℓ·s·|Py + (y·u_j)u_j|.

## Reference use

### local-project

Queries:
- `cat manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `grep -n "^abbrev Rn\|^namespace GMT.Ch03\|^open " project/GMT/Ch03/Contract.lean; cmp project/GMT/Ch03/Contract.lean <workspace>/GMT/Ch03/Contract.lean; cmp GMT/Ch03/Contract.lean GMT/Ch03/Submission.lean`
- `rg -n "theorem (eq_starProjection_of_mem_of_inner_eq_zero|starProjection_singleton|norm_starProjection_apply_le|starProjection_eq_self_iff|starProjection_orthogonal_val|starProjection_add_starProjection_orthogonal|inf_orthogonal|starProjection_apply_eq_zero_iff|starProjection_eq_zero_iff|starProjection_inner_eq_zero|inner_starProjection_left_eq_right|starProjection_mem|sub_starProjection_mem_orthogonal|starProjection_orthogonal|norm_sq_eq_add_norm_sq_starProjection|starProjection_minimal|starProjection_eq_linear_proj|starProjection_tendsto_closure_iSup|starProjection_bot|starProjection_top|starProjection_sup)" mathlib/Mathlib/Analysis/InnerProductSpace/`
- `rg -n "theorem (sum_sq_norm_inner|sum_inner_mul_inner|sum_repr|sum_sq_inner|norm_sq_eq_sum|sum_repr'|repr_apply_apply|starProjection_eq_sum|orthogonalProjection_eq_sum|sum_inner_sq)" mathlib/Mathlib/Analysis/InnerProductSpace/`
- `rg -n "def basisOfOrthonormalOfCardEqFinrank|theorem coe_basisOfOrthonormalOfCardEqFinrank|OrthonormalBasis.mk|def OrthonormalBasis.mk|protected def mk" mathlib/Mathlib/Analysis/InnerProductSpace/`
- `grep -n "μHE\[" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -rn "theorem measure_iUnion_fintype_le\|theorem measure_biUnion_finset_le\|lemma measure_iUnion_fintype_le\|lemma measure_biUnion_finset_le" mathlib/Mathlib/MeasureTheory/`
- `grep -n "theorem mem_orthogonal_singleton_iff_inner_right\|theorem mem_orthogonal_singleton_iff_inner_left\|theorem inner_right_of_mem_orthogonal\|theorem inner_left_of_mem_orthogonal\|theorem coe_inner\b\|theorem finrank_add_finrank_orthogonal" mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean mathlib/Mathlib/Analysis/InnerProductSpace/Subspace.lean`
- `grep -rn "theorem span_eq_top_of_card_eq_finrank\|lemma span_eq_top_of_card_eq_finrank\|theorem LinearIndependent.span_eq_top_of_card_eq_finrank" mathlib/Mathlib/LinearAlgebra/`
- `grep -rn "theorem norm_le_card_mul_iSup_norm_inner\|lemma norm_le_card_mul_iSup_norm_inner\|lemma sum_sq_norm_inner_right\|theorem sum_sq_norm_inner_right" mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `grep -c for bf_starProjection_sup_span_unit / bf_cone_subset_iUnion_slabCones / bf_coneTrichotomy_of_slabCover in dag.json; grep -rl over .humanize/; git grep -l over GMT/Ch03 of every local branch and remote (no match)`
- `lake env lean GMT/Scratch/SlabToConeSplitDecision.lean (child types elaborate; parent assembly with the frozen type compiles from them)`
- `lake env lean GMT/Scratch/SlabToConeChildProofs.lean (all three children proved; no errors or warnings)`
- `lake env lean GMT/Scratch/SlabToConeEndToEnd.lean (#print axioms: propext, Classical.choice, Quot.sound for all four declarations)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-slab-to-cone-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/SlabToConeSplitDecision.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/SlabToConeChildProofs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/SlabToConeEndToEnd.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean. It fixes Rn N = EuclideanSpace ℝ (Fin N) (line 56) in namespace GMT.Ch03, with the opens that all child types use. The pinned Mathlib supplies every ingredient the child proofs cite.
- Projection/Basic.lean: Submodule.eq_starProjection_of_mem_orthogonal, sub_starProjection_mem_orthogonal, starProjection_orthogonal_val, norm_sq_eq_add_norm_sq_starProjection, norm_starProjection_apply_le.
- Orthogonal.lean: Submodule.inf_orthogonal ((K₁ ⊔ K₂)ᗮ = K₁ᗮ ⊓ K₂ᗮ), mem_orthogonal_singleton_iff_inner_right, inner_left_of_mem_orthogonal, inner_right_of_mem_orthogonal.
- Projection/FiniteDimensional.lean: Submodule.finrank_add_finrank_orthogonal.
- LinearAlgebra/FiniteDimensional/Lemmas.lean: LinearIndependent.span_eq_top_of_card_eq_finrank.
- PiL2.lean: OrthonormalBasis.mk and OrthonormalBasis.sum_sq_inner_right (Parseval).
- OuterMeasure/Basic.lean: measure_iUnion_fintype_le.
- Geometry/Euclidean/Volume/Measure.lean: μHE[d] is notation for euclideanHausdorffMeasure d : Measure X, so it instantiates the abstract measure μ of the transfer lemma.
No existing declaration states the projection formula for W ⊔ span{u}, the slab-cone covering, or the abstract trichotomy transfer. The three proposed names are fresh in dag.json, in .humanize, and in every branch's GMT/Ch03. In the scratch files, the child types elaborate, the parent assembly with the frozen type compiles from them, all three children have compiled proofs, and only the standard axioms are used.
