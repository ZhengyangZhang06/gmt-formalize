# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.wedge_norm-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.wedge_norm-a1.adapted_basis-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1–3 of the parent proof of cmcs_wedge_norm_le (fact (E1): rotate β to a multiple of a basis covector), including the case b = 0 from step 2. The base index 0 of the parent proof is replaced by an arbitrary index i₀.
1. (Riesz representative.) Let b := (InnerProductSpace.toDual ℝ (Euclid P)).symm β ∈ ℝ^P. By InnerProductSpace.toDual_symm_apply, β(x) = ⟨b, x⟩ for every x ∈ ℝ^P. Since toDual is a linear isometry equivalence, so is its inverse, hence ‖b‖ = ‖β‖ (LinearIsometryEquiv.norm_map).
2. (Standard basis.) Let e := EuclideanSpace.basisFun (Fin P) ℝ, an orthonormal basis of ℝ^P indexed by Fin P. By orthonormality (orthonormal_iff_ite), ⟨e_a, e_c⟩ = 1 if a = c and ⟨e_a, e_c⟩ = 0 if a ≠ c; in particular ‖e_{i₀}‖ = 1.
3. (Case b = 0.) Then ‖β‖ = ‖b‖ = 0, and β(x) = ⟨0, x⟩ = 0 for every x (inner_zero_left). Take f := e. For every i we have β(e_i) = 0. The required value (‖β‖ if i = i₀, 0 otherwise) is 0 in both cases because ‖β‖ = 0. This proves the claim when b = 0.
4. (Case b ≠ 0: a unit vector.) Now ‖b‖ > 0 (norm_pos_iff). Put u := ‖b‖⁻¹·b. Then ‖u‖ = ‖b‖⁻¹·‖b‖ = 1 (norm_smul, norm_inv, norm_norm), and b = ‖b‖·u (smul_smul and ‖b‖·‖b‖⁻¹ = 1).
5. (Reflection.) Let R := (ℝ ∙ (e_{i₀} − u))ᗮ.reflection, the reflection of ℝ^P in the orthogonal complement of the line spanned by e_{i₀} − u. It is a linear isometry equivalence ℝ^P ≃ₗᵢ[ℝ] ℝ^P. Since ‖e_{i₀}‖ = 1 = ‖u‖, Submodule.reflection_sub gives R(e_{i₀}) = u.
6. (The basis.) Let f := e.map R (OrthonormalBasis.map). It is an orthonormal basis of ℝ^P indexed by Fin P, and f_i = R(e_i) for every i (OrthonormalBasis.map_apply).
7. (Values.) Fix i ∈ Fin P. By steps 1, 4 and 5, and since R preserves inner products (LinearIsometryEquiv.inner_map_map):
β(f_i) = ⟨b, R(e_i)⟩ = ⟨‖b‖·u, R(e_i)⟩ = ‖b‖·⟨u, R(e_i)⟩ = ‖b‖·⟨R(e_{i₀}), R(e_i)⟩ = ‖b‖·⟨e_{i₀}, e_i⟩ (using real_inner_smul_left).
If i = i₀, then ⟨e_{i₀}, e_i⟩ = 1 by step 2, so β(f_i) = ‖b‖ = ‖β‖. If i ≠ i₀, then ⟨e_{i₀}, e_i⟩ = 0 by step 2, so β(f_i) = 0. Hence β(f_i) = (if i = i₀ then ‖β‖ else 0) for every i, which proves the claim when b ≠ 0. ∎

## Key steps

1. Riesz: b := (toDual ℝ (Euclid P)).symm β satisfies β(x) = ⟨b, x⟩ and ‖b‖ = ‖β‖.
2. If b = 0, then ‖β‖ = 0 and β = 0, so the standard basis e works.
3. If b ≠ 0, set u := ‖b‖⁻¹·b (so ‖u‖ = 1 and b = ‖b‖·u) and R := reflection in (ℝ ∙ (e_{i₀} − u))ᗮ, so R(e_{i₀}) = u by Submodule.reflection_sub.
4. f := e.map R is an orthonormal basis with f_i = R(e_i), and β(f_i) = ‖b‖⟨R e_{i₀}, R e_i⟩ = ‖b‖⟨e_{i₀}, e_i⟩ = (if i = i₀ then ‖β‖ else 0).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cat local-references/123e8435b4a2469b/manifest.json`
- `rg -n 'theorem reflection_sub|theorem toDual_symm_apply|protected theorem map_apply|theorem orthonormal_iff_ite|theorem alternatizeUncurryFin_apply|theorem map_eq_zero_of_not_injective|lemma removeNth_insertNth|theorem insertNth_apply_same|def insertNthEquiv' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `rg -n 'theorem LinearIsometryEquiv.inner_map_map|theorem Fintype.prod_prod_type|lemma _root_.Equiv.prod_comp' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean' (the additive forms Fintype.sum_prod_type and Equiv.sum_comp come from to_additive)`
- `rg -n -i 'alternatizeUncurryFin.*norm|norm_alternatizeUncurryFin|wedge.*norm_le|norm_wedge' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `rg -n 'sum.*removeNth|removeNth.*sum' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `rg -n 'exists_orthonormalBasis.*inner|reflection.*OrthonormalBasis|OrthonormalBasis.*reflection' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `rg -n 'alternatizeUncurryFin|covectorEuclideanNorm|removeNth|insertNth|smulRight' local-references/123e8435b4a2469b/project -g '*.lean'`
- `grep -n 'def covectorEuclideanNorm|abbrev Covector' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `python3 -I scan of dag.json (645 nodes): lean_name and theorems fields compared against cmcs_wn_adapted_orthonormalBasis, cmcs_wn_tuple_sq_le and cmcs_wn_removeNth_fiber_sum; status of the covector_sq_sum nodes`
- `git for-each-ref (2981 refs, 1268 unique commits) | xargs -n 100 sh -c 'git grep -l -E cmcs_wn_ $@ -- *.lean'; the same command finds regcomp_covector_sq_sum_orthonormalBasis in 25 commits`
- `grep -rl cmcs_wn_ over runs/20261011T150044Z-ba604216b4/nodes, dag.json and decomposition-reopenings; grep -l cmcs_wn_ over the 687 files .swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean`
- `git show 16144a47:GMT/Ch07/Submission.lean (accepted proofs of regcomp_covector_sq_sum_basis_invariant, regcomp_covector_sq_sum_basisFun and regcomp_covector_sq_sum_orthonormalBasis)`
- `lean GMT/Scratch/cmcs_wedge_norm_decomposition/{ChildA,ChildB,ChildC,Assembly,Full,InstCheck}.lean with #print axioms and pp.explicit/pp.coercions instance checks`
- `sed -n 20,62p and sed -n 170,185p book/chapter-06.txt (Simon 6.1.1-1.3 wedge product, 1.15 Euclidean norm)`
- `WebSearch (standard): Federer 1.8.1 |xi wedge eta| <= |xi||eta| if xi or eta is simple, Euclidean norm on the exterior algebra (two queries)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Reflection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fintype/BigOperators.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_wedge_norm_decomposition/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_wedge_norm_decomposition/Full.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_wedge_norm_decomposition/ChildA.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_wedge_norm_decomposition/ChildB.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_wedge_norm_decomposition/ChildC.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_wedge_norm_decomposition/InstCheck.lean`

Snapshot facts:
- The manifest pins project b4d606db and Mathlib 25730c7c.
- The snapshot Ch07 contract is byte-identical to the workspace Submission.lean.
- The snapshot project contains no alternatizeUncurryFin, covectorEuclideanNorm, removeNth, insertNth or smulRight lemma.

What the snapshot Mathlib lacks:
- It has no coefficient-norm wedge inequality, no adapted-orthonormal-basis lemma for a functional, and no removeNth fiber-sum identity.
- The only wedge norm bound is norm_alternatizeUncurryFin_le (Analysis/Normed/Module/Alternating/Uncurry/Fin.lean:133). It bounds the operator (comass) norm by (n+1)·‖f‖, a different norm with a different constant, so it cannot replace any child.
- The removeNth sum hits are unrelated (LinearAlgebra/Alternating/Uncurry/Fin.lean:114, Matrix/Determinant/Bird).

Cited tools, all located in the snapshot:
- Submodule.reflection_sub (Projection/Reflection.lean:153)
- InnerProductSpace.toDual_symm_apply (Dual.lean:178)
- OrthonormalBasis.map_apply (PiL2.lean:586)
- LinearIsometryEquiv.inner_map_map (InnerProductSpace/LinearMap.lean:117)
- orthonormal_iff_ite (Orthonormal.lean:82)
- ContinuousAlternatingMap.alternatizeUncurryFin_apply (Normed/Module/Alternating/Uncurry/Fin.lean:137)
- ContinuousAlternatingMap.map_eq_zero_of_not_injective (Topology/Algebra/Module/Alternating/Basic.lean:137)
- Fin.insertNth_apply_same, Fin.removeNth_insertNth, Fin.insertNthEquiv (Data/Fin/Tuple/Basic.lean:855, 890, 1065)
- Fintype.sum_prod_type (to_additive of Fintype.prod_prod_type, Data/Fintype/BigOperators.lean:271-273)
- Equiv.sum_comp (to_additive of Equiv.prod_comp, BigOperators/Group/Finset/Defs.lean:749)
SimonGMT defines covectorEuclideanNorm (Chapter06/Mass.lean:30) and Covector (Forms.lean:31).

Reuse and names:
- The only reusable DAG result is the accepted regcomp_covector_sq_sum_orthonormalBasis (commit 16144a47, identical type). It is already this node's dependency.
- The new names cmcs_wn_adapted_orthonormalBasis, cmcs_wn_tuple_sq_le and cmcs_wn_removeNth_fiber_sum collide with none of the 645 DAG nodes and none of the 2981 git refs. The ref search method was validated on a known name.
- They also do not appear in the run's node files or in the 687 worktree Submission.lean files.

Lean checks:
- The three child types elaborate with the intended instances.
- Each child is proved in scratch using standard axioms only.
- Assembly.lean proves the frozen parent from the child stubs.
- Full.lean proves the parent end-to-end with axioms [propext, Classical.choice, Quot.sound].

Public sources: Federer, Geometric Measure Theory (1969), §1.8 (Euclidean norms on the exterior algebra; |ξ∧η| ≤ |ξ||η| when one factor is simple). The exact numbering was not confirmed by the searches; the searches returned only background (arXiv:2503.12402, arXiv:2411.13966 for comass analogues with other constants). The proof here is self-contained and Lean-checked, so it does not rely on these sources.
