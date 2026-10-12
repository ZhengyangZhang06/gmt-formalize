# Parent-supplied natural-language proof

- Parent DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.slab_to_cone-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.slab_to_cone-a1.slab_projection-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (the formula p_j y = Py + (y·u_j)u_j), extracted for a single unit vector u ∈ W^⊥ and an arbitrary ambient dimension N. Every subspace of the finite-dimensional space E is complete, so W and H have orthogonal projections. Fix y ∈ E and put z := Py + (y·u)u.

1. Characterization of the orthogonal projection. Let K ⊆ E be a subspace with an orthogonal projection and y, z ∈ E. If z ∈ K and y − z ∈ K^⊥, then K.starProjection y = z (Mathlib Submodule.eq_starProjection_of_mem_orthogonal). We apply this with K := H, so it remains to show z ∈ H (step 2) and y − z ∈ H^⊥ (steps 3–5).

2. z ∈ H.
 - Py ∈ W (Submodule.starProjection_apply_mem).
 - (y·u)u ∈ span{u}, since u ∈ span{u} (Submodule.mem_span_singleton_self) and a subspace is closed under scalar multiplication (Submodule.smul_mem).
 - Hence z = Py + (y·u)u ∈ W ⊔ span{u} = H (Submodule.add_mem_sup).

3. Orthogonal complement of a join. (W ⊔ span{u})^⊥ = W^⊥ ⊓ span{u}^⊥ (Submodule.inf_orthogonal). So y − z ∈ H^⊥ follows from y − z ∈ W^⊥ (step 4) and y − z ∈ span{u}^⊥ (step 5).

4. y − z ∈ W^⊥. We have y − z = (y − Py) − (y·u)u.
 - y − Py ∈ W^⊥ (Submodule.sub_starProjection_mem_orthogonal).
 - (y·u)u ∈ W^⊥, because u ∈ W^⊥ and W^⊥ is a subspace.
 - The difference of two elements of the subspace W^⊥ lies in W^⊥ (Submodule.sub_mem).

5. y − z ∈ span{u}^⊥. A vector v lies in span{u}^⊥ iff u·v = 0 (Submodule.mem_orthogonal_singleton_iff_inner_right). By bilinearity (inner_sub_right, inner_add_right, real_inner_smul_right),
 u·(y − z) = u·y − u·Py − (y·u)(u·u).
 - u·Py = 0, since Py ∈ W and u ∈ W^⊥ (Submodule.inner_left_of_mem_orthogonal).
 - u·u = |u|² = 1 (real_inner_self_eq_norm_sq and |u| = 1).
 Hence u·(y − z) = u·y − y·u = 0, by symmetry of the real inner product (real_inner_comm).

6. Conclusion. By steps 2–5, z ∈ H and y − z ∈ H^⊥, so step 1 gives p(y) = H.starProjection y = z = Py + (y·u)u. ∎

## Key steps

1. Characterize H.starProjection y as the unique z ∈ H with y − z ∈ H^⊥ (Submodule.eq_starProjection_of_mem_orthogonal), with z := Py + (y·u)u.
2. z ∈ W ⊔ span{u}, since Py ∈ W and (y·u)u ∈ span{u}.
3. (W ⊔ span{u})^⊥ = W^⊥ ⊓ span{u}^⊥ (Submodule.inf_orthogonal).
4. y − z = (y − Py) − (y·u)u ∈ W^⊥, because y − Py ∈ W^⊥ and u ∈ W^⊥.
5. u·(y − z) = u·y − u·Py − (y·u)|u|² = u·y − y·u = 0, so y − z ∈ span{u}^⊥; hence p(y) = Py + (y·u)u.

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
