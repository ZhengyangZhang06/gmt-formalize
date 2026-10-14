# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.wedge_norm-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.wedge_norm-a1.tuple_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof of cmcs_wedge_norm_le (values of β ∧ γ on basis tuples). The adapted orthonormal basis f, the index 0 and the constant ‖b‖ are replaced by an arbitrary injective family v, an index i₀ and a constant c such that β(v_a) = c if a = i₀ and β(v_a) = 0 otherwise.
Fix j : Fin (k+1) → Fin P. Write ω := alternatizeUncurryFin (β.smulRight γ) and w := v ∘ j (that is, w_m = v_{j(m)}). Write S := c²·Σ_{i ∈ Fin (k+1)} s_i for the right-hand side, where s_i := γ(v ∘ removeNth i j)² if j(i) = i₀ and s_i := 0 otherwise.
1. (S ≥ 0.) Each s_i is a square or 0, so Σ_i s_i ≥ 0 (Finset.sum_nonneg). Also c² ≥ 0, hence S ≥ 0.
2. (Case j not injective.) Then w = v ∘ j is not injective: if it were, j would be injective (Function.Injective.of_comp). Since ω is a continuous alternating map, ω(w) = 0 (ContinuousAlternatingMap.map_eq_zero_of_not_injective). Hence ω(w)² = 0 ≤ S by step 1.
3. (Expansion of ω(w).) By ContinuousAlternatingMap.alternatizeUncurryFin_apply, ω(w) = Σ_{i ∈ Fin (k+1)} (−1)^i • ((β.smulRight γ)(w_i))(Fin.removeNth i w). The integer (−1)^i acts by zsmul, i.e. as multiplication by the real number (−1)^i (zsmul_eq_mul). By ContinuousLinearMap.smulRight_apply, (β.smulRight γ)(x) = β(x)•γ, so the i-th term equals (−1)^i·β(w_i)·γ(Fin.removeNth i w).
Now w_i = v_{j(i)}, so by hypothesis β(w_i) = c if j(i) = i₀ and β(w_i) = 0 otherwise. Also Fin.removeNth i w = v ∘ (Fin.removeNth i j), because both tuples send m ∈ Fin k to v_{j(succAbove i m)} (Fin.removeNth_apply; the two sides agree definitionally). Therefore ω(w) = Σ_i (−1)^i·t_i·γ(v ∘ removeNth i j), where t_i := c if j(i) = i₀ and t_i := 0 otherwise.
4. (Case j injective and j(i) ≠ i₀ for every i.) Then t_i = 0 for every i, so ω(w) = 0 by step 3, and ω(w)² = 0 ≤ S by step 1.
5. (Case j injective and j(i₁) = i₀ for some i₁.) For every i ≠ i₁, injectivity of j gives j(i) ≠ j(i₁) = i₀, so t_i = 0 and s_i = 0. Hence only the index i₁ contributes to either sum (Finset.sum_eq_single): ω(w) = (−1)^{i₁}·c·γ(v ∘ removeNth i₁ j) and S = c²·γ(v ∘ removeNth i₁ j)². Since ((−1)^{i₁})² = ((−1)²)^{i₁} = 1, we get ω(w)² = ((−1)^{i₁})²·c²·γ(v ∘ removeNth i₁ j)² = c²·γ(v ∘ removeNth i₁ j)² = S, so ω(w)² ≤ S.
6. Steps 2, 4 and 5 exhaust all cases, so ω(v ∘ j)² ≤ S for every j : Fin (k+1) → Fin P. ∎

## Key steps

1. The right-hand side S is nonnegative (c² times a sum of squares and zeros).
2. If j is not injective, then v ∘ j is not injective and the alternating map β ∧ γ vanishes on it.
3. alternatizeUncurryFin_apply and smulRight_apply give (β ∧ γ)(v ∘ j) = Σ_i (−1)^i·[j(i) = i₀]c·γ(v ∘ removeNth i j).
4. If j is injective, at most one i₁ has j(i₁) = i₀. If there is none, the value is 0. Otherwise only i₁ contributes to both sides, and ((−1)^{i₁})² = 1 gives equality.

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
