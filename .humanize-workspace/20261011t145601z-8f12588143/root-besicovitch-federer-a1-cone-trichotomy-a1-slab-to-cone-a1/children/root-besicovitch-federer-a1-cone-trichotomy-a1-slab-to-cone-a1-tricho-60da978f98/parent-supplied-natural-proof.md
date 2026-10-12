# Parent-supplied natural-language proof

- Parent DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.slab_to_cone-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.slab_to_cone-a1.trichotomy_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 (Cases 1–3) of the parent proof. The concrete cone families are replaced by abstract families satisfying the two inclusions of the parent's step 3 (where κ = √ℓ and ι = Fin ℓ).

Notation: m_X(r, s) := μ(A ∩ (X(s) ∩ B(a, r))) and m_j(r, s) := μ(A ∩ (Z_j(s) ∩ B(a, r))). On arbitrary sets μ is monotone (measure_mono) and finitely subadditive (measure_iUnion_fintype_le).

1. Case 1: Ax′_j holds for some j. Then Ax holds by (iii), so the third disjunct holds.

2. Case 2: Case 1 fails and Ψ∞_j holds for some j. We prove Φ∞.
 - Let K ∈ ℝ and ε > 0. By Ψ∞_j there are s with 0 < s < ε and r with 0 < r < δ such that ofReal(K(rs)ⁿ) ≤ m_j(r, s).
 - Since s > 0, (i) gives Z_j(s) ⊆ X(s), hence A ∩ (Z_j(s) ∩ B(a, r)) ⊆ A ∩ (X(s) ∩ B(a, r)) (Set.inter_subset_inter_right, Set.inter_subset_inter_left).
 - By monotonicity m_j(r, s) ≤ m_X(r, s), so ofReal(K(rs)ⁿ) ≤ m_X(r, s) with the same s, r. This is Φ∞.

3. Case 3: Cases 1 and 2 both fail. Then for every j neither Ax′_j nor Ψ∞_j holds, so (iv) gives Ψ0_j for every j. We prove Φ0. Let c > 0, put M := card ι ≥ 1 (ι is nonempty) and c′ := c/(M·κⁿ). Then c′ > 0, since c > 0, M > 0 and κ > 0.

4. Choice of ε.
 - For each j, Ψ0_j applied to c′ gives ε_j > 0 with m_j(r, s) ≤ ofReal(c′(rs)ⁿ) for all 0 < s < ε_j and 0 < r < δ.
 - Let ε₀ := min_{j∈ι} ε_j (Finset.inf' over Finset.univ, which is nonempty). Then ε₀ > 0 as the minimum of finitely many positive numbers (Finset.lt_inf'_iff).
 - Put ε := ε₀/κ > 0.

5. Fix s, r with 0 < s < ε and 0 < r < δ, and put s′ := κs. Then s′ > 0, and s′ < κε = ε₀ ≤ ε_j for every j (Finset.inf'_le).

6. Covering. By (ii) (s > 0), A ∩ (X(s) ∩ B(a, r)) ⊆ ⋃_j A ∩ (Z_j(s′) ∩ B(a, r)). Indeed, if x ∈ A, x ∈ X(s) and x ∈ B(a, r), then x ∈ Z_j(κs) for some j, so x lies in the j-th member of the union.

7. Estimate. By monotonicity, finite subadditivity, step 5 and the choice of ε_j,
 m_X(r, s) ≤ Σ_j m_j(r, s′) ≤ Σ_j ofReal(c′(rs′)ⁿ) = M·ofReal(c′(rκs)ⁿ)
 (Finset.sum_const, nsmul_eq_mul). Since c′(rκs)ⁿ ≥ 0,
 M·ofReal(c′(rκs)ⁿ) = ofReal(M)·ofReal(c′(rκs)ⁿ) = ofReal(M·c′·(rκs)ⁿ)
 (ENNReal.ofReal_natCast, ENNReal.ofReal_mul). Finally, since M ≠ 0 and κⁿ ≠ 0,
 M·c′·(rκs)ⁿ = M·(c/(M·κⁿ))·κⁿ·(rs)ⁿ = c(rs)ⁿ.
 Hence m_X(r, s) ≤ ofReal(c(rs)ⁿ).

8. Since s ∈ (0, ε) and r ∈ (0, δ) were arbitrary, ε witnesses Φ0 for this c. As c > 0 was arbitrary, Φ0 holds.

9. The three cases are exhaustive, so Φ0 ∨ Φ∞ ∨ Ax. ∎

## Key steps

1. If some Ax′_j holds, then Ax holds by (iii).
2. If some Ψ∞_j holds, then Φ∞ follows with the same s and r, from Z_j(s) ⊆ X(s) (s > 0) and monotonicity of μ.
3. Otherwise every Ψ0_j holds. For c > 0, apply each Ψ0_j to c′ := c/(card ι·κⁿ) to get ε_j, and set ε := (min_j ε_j)/κ > 0.
4. For 0 < s < ε and 0 < r < δ: A ∩ X(s) ∩ B(a,r) ⊆ ⋃_j A ∩ Z_j(κs) ∩ B(a,r) with κs < ε_j. Finite subadditivity gives the bound card ι·ofReal(c′(rκs)ⁿ) = ofReal(c(rs)ⁿ), which is Φ0.

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
