# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1`
- Child DAG node: `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1.parseval_sq_sum-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 2 (basis independence of N). It is stated here for two arbitrary orthonormal bases u and v. The parent uses v = e, the standard basis; the argument is the same.

Notation. [P] := {0,…,P−1}; ⟨·,·⟩ and |·| are the Euclidean inner product and norm of ℝ^P. u = (u_0,…,u_{P−1}) and v = (v_0,…,v_{P−1}) are orthonormal bases of ℝ^P. φ is a k-covector, a continuous alternating k-linear map (ℝ^P)^k → ℝ; only multilinearity is used. For a family w and I : {0,…,k−1} → [P] put φ(w_I) := φ(w_{I(0)},…,w_{I(k−1)}) and N_w(φ) := Σ_{all I} φ(w_I)². Claim: N_u(φ) = N_v(φ).

1. (Parseval in one slot.) For every linear functional ℓ : ℝ^P → ℝ, Σ_{i∈[P]} ℓ(u_i)² = Σ_{i∈[P]} ℓ(v_i)². Proof: by the Riesz representation on ℝ^P, ℓ = ⟨a, ·⟩ for some a ∈ ℝ^P. For any orthonormal basis w of ℝ^P, a = Σ_i ⟨a, w_i⟩ w_i, so |a|² = Σ_i ⟨a, w_i⟩² (Parseval). Hence Σ_i ℓ(u_i)² = Σ_i ⟨a, u_i⟩² = |a|² = Σ_i ⟨a, v_i⟩² = Σ_i ℓ(v_i)². Both sums equal the squared operator norm ‖ℓ‖² = |a|²; every linear functional on ℝ^P is continuous.

2. (Hybrid sums.) For r = 0, 1, …, k and I : {0,…,k−1} → [P], let w^{r,I} be the k-tuple with entries w^{r,I}_j := v_{I(j)} for j < r and w^{r,I}_j := u_{I(j)} for j ≥ r. Put M_r := Σ_{all I} φ(w^{r,I})². Since w^{0,I} = u_I and w^{k,I} = v_I, M_0 = N_u(φ) and M_k = N_v(φ).

3. (One slot at a time: M_r = M_{r+1} for r < k.) Fix r < k. The maps I : {0,…,k−1} → [P] correspond bijectively to pairs (i, I'), where i := I(r) ∈ [P] and I' is the restriction of I to {0,…,k−1}∖{r}. For fixed I', set x_j := v_{I'(j)} for j < r and x_j := u_{I'(j)} for j > r. Define ℓ_{I'}(z) := φ(x_0,…,x_{r−1}, z, x_{r+1},…,x_{k−1}); this is a linear functional on ℝ^P because φ is linear in its r-th argument. If I corresponds to (i, I'), then w^{r,I} and w^{r+1,I} both have entry x_j in every position j ≠ r: for j < r both use v_{I(j)}, and for j > r both use u_{I(j)}. Their r-th entries are u_i and v_i respectively. Hence φ(w^{r,I}) = ℓ_{I'}(u_i) and φ(w^{r+1,I}) = ℓ_{I'}(v_i). Summing first over i ∈ [P] and then over I', and applying step 1 to each ℓ_{I'}:
 M_r = Σ_{I'} Σ_{i∈[P]} ℓ_{I'}(u_i)² = Σ_{I'} Σ_{i∈[P]} ℓ_{I'}(v_i)² = M_{r+1}.

4. (Conclusion.) By step 3, N_u(φ) = M_0 = M_1 = ⋯ = M_k = N_v(φ). For k = 0 the chain is trivial: both sides equal φ()², the value on the empty tuple. For P = 0 and k ≥ 1 both sums are empty. ∎

Remark (the same slot-by-slot replacement, organized for Lean). Run it as an induction on k, for all k-covectors at once. In degree k+1, write φ(z_0, z_1,…,z_k) = ψ_{z_0}(z_1,…,z_k), where ψ_z := φ(z, ·,…,·) is a k-covector (ContinuousAlternatingMap.curryLeft, curryLeft_apply_apply). Split I into (I(0), J) with J := (I(1),…,I(k)) (Fin.consEquiv, Fintype.sum_prod_type). Replace u by v in the last k slots by applying the induction hypothesis to each ψ_{u_i}. Exchange the two sums (Finset.sum_comm). Finally, replace u_i by v_i in slot 0 by step 1 applied to ℓ_J(z) := ψ_z(v_J), the continuous linear functional (ContinuousAlternatingMap.apply ℝ ℝ^P ℝ v_J) ∘ curryLeft φ. Step 1 is Mathlib's OrthonormalBasis.norm_dual: ‖ℓ‖² = Σ_i ℓ(w_i)² for every orthonormal basis w.

## Key steps

1. One-slot Parseval: for every linear functional ℓ = ⟨a,·⟩, Σ_i ℓ(u_i)² = |a|² = Σ_i ℓ(v_i)² (OrthonormalBasis.norm_dual).
2. Hybrid sums M_r use v in slots j < r and u in slots j ≥ r, so M_0 = N_u(φ) and M_k = N_v(φ).
3. M_r = M_{r+1}: fixing every index except I(r) makes slot r a linear functional ℓ_{I'}, and Σ_i ℓ_{I'}(u_i)² = Σ_i ℓ_{I'}(v_i)².
4. The chain M_0 = ⋯ = M_k gives N_u(φ) = N_v(φ).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical); cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (identical)`
- `snapshot project/lake-manifest.json revs vs git rev-parse HEAD of lake-packages-25730c7c/{simongmt,mathlib}: simongmt 2b3663083f3fe399b6296fb8eaee52169170e197, mathlib 25730c7c759d108ef87ab70af2342a196760f79d (match)`
- `rg -n 'covectorEuclideanNorm' local-references/197bdd4b88278494/project (no match)`
- `rg -n 'slicing_mb_wn_|sq_sum_eq_factorial_mul|sq_sum_onb_invariant|norm_sq_eq_onb_sum|adapted_onb|adapted_sum_le' local-references/197bdd4b88278494/project (no match)`
- `grep -n 'covectorEuclideanNorm|abbrev Covector|def Covector|StrictMono' simongmt/Poincare/SimonGMT/Chapter06/*.lean; rg -n 'OrthonormalBasis' Poincare/SimonGMT/Chapter06 (no match); rg -n 'factorial|orderEmbOfFin|Tuple.sort|StrictMono I' Poincare/SimonGMT`
- `grep -n 'theorem|lemma|def |abbrev ' simongmt Chapter06/{WedgeForms,FormSupNorm,FormsDuality,GeometricPointProduct}.lean`
- `rg -n 'lemma OrthonormalBasis.norm_dual' Mathlib/Analysis/InnerProductSpace/Dual.lean; rg -n 'theorem Orthonormal.exists_orthonormalBasis_extension_of_card_eq' Mathlib/Analysis/InnerProductSpace/PiL2.lean; rg -n 'theorem alternatizeUncurryFin_apply' Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean; rg -n 'theorem curryLeft_apply_apply' Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `rg -n 'theorem monotone_sort|theorem sort_eq_refl_iff_monotone|theorem comp_perm_comp_sort_eq_comp_sort' Mathlib/Data/Fin/Tuple/Sort.lean; rg -n 'theorem map_perm ' Mathlib/LinearAlgebra/Alternating/Basic.lean; rg -n 'theorem map_eq_zero_of_not_injective' Mathlib/Topology/Algebra/Module/Alternating/Basic.lean; rg -n '^theorem toDual_symm_apply' Mathlib/Analysis/InnerProductSpace/Dual.lean; rg -n 'def apply \(m' Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `rg -ln 'factorial' Mathlib/LinearAlgebra/Alternating Mathlib/LinearAlgebra/ExteriorPower Mathlib/Analysis/Normed/Module/Alternating; module docstrings of Mathlib/LinearAlgebra/ExteriorPower/{BilinForm,Pairing,HodgeStar}.lean`
- `python3 scan of dag.json (217 nodes, 217 distinct lean_names): five proposed names absent; statements mentioning covectorEuclideanNorm/Orthonormal/alternatizeUncurryFin/smulRight/StrictMono listed (no identical type)`
- `contract_scope/child_modules in verifier/gmt-compare.py (replayed child scope: opens, namespace GMT.Ch06, noncomputable section/end)`
- `lake env printenv LEAN_PATH; lean -o /tmp/wedge_split_trCfMb/out/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean`
- `lean /tmp/wedge_split_trCfMb/check/Stmts.lean (5 child types + parent elaborate, no errors)`
- `lean /tmp/wedge_split_trCfMb/check/Instances.lean (pp.explicit: StrictMono decidability instance instDecidableStrictMonoOfForallForallForallLt, same as in covectorEuclideanNorm; #check of cited lemmas)`
- `lean /tmp/wedge_split_trCfMb/check/Assembly.lean (#print axioms full_assembly: [propext, Classical.choice, Quot.sound]; ‖α‖ = ContinuousLinearMap.opNorm α by rfl)`
- `lean /tmp/wedge_split_trCfMb/check/{ProveC1,ProveC2,ProveC4_ax,ProveC5_ax,EndToEnd}.lean (#print axioms of all five children and the parent: [propext, Classical.choice, Quot.sound])`
- `grep -n -i 'orthonormal' book/chapter-06.txt; sed -n 85,110p book/chapter-06.txt (Simon 1.5–1.6)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/ExteriorPower/BilinForm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/ExteriorPower/Pairing.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/ExteriorPower/HodgeStar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/WedgeForms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-wedge-norm-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/wedge_split_trCfMb/check/Stmts.lean`
- `/tmp/wedge_split_trCfMb/check/Instances.lean`
- `/tmp/wedge_split_trCfMb/check/Assembly.lean`
- `/tmp/wedge_split_trCfMb/check/ProveC1.lean`
- `/tmp/wedge_split_trCfMb/check/ProveC2.lean`
- `/tmp/wedge_split_trCfMb/check/ProveC4.lean`
- `/tmp/wedge_split_trCfMb/check/ProveC5.lean`
- `/tmp/wedge_split_trCfMb/check/EndToEnd.lean`

Findings:
- The pinned snapshot (project d8d46c95, Mathlib 25730c7c, SimonGMT 2b366308 per lake-manifest and package HEADs) contains the frozen Ch06 contract, byte-identical to the workspace Submission.
- SimonGMT defines covectorEuclideanNorm as √(Σ_{I : Fin n → Fin P} if StrictMono I then α(basisFun ∘ I)² else 0) (Mass.lean:30), with Covector E n = E [⋀^Fin n]→L[ℝ] ℝ (Forms.lean:31).
- SimonGMT has no orthonormal-basis invariance, counting identity or wedge-norm bound for this norm. Its only wedge estimate (norm_covectorWedge_le) is for the operator norm, and it contains no OrthonormalBasis usage in Chapter06.
- Mathlib provides the needed tools: OrthonormalBasis.norm_dual (‖L‖² = Σ L(b_i)², the one-slot Parseval step), Orthonormal.exists_orthonormalBasis_extension_of_card_eq, InnerProductSpace.toDual_symm_apply, alternatizeUncurryFin_apply, curryLeft_apply_apply, ContinuousAlternatingMap.apply, map_eq_zero_of_not_injective, AlternatingMap.map_perm and the Tuple.sort API.
- Mathlib's exterior-power bilinear forms act on ⋀[R]^n M, not on continuous alternating maps, and provide no coefficient-norm invariance. So all five children are new obligations.
- In the replayed comparator child scope, all five child types and the parent type elaborate. The StrictMono decidability instance matches the one in covectorEuclideanNorm's definition.
- The parent follows from the children with axioms [propext, Classical.choice, Quot.sound]. Scratch proofs of all five children compile with the same axioms.
- No proposed name occurs in the snapshot project or among the 217 DAG nodes.
- Simon 1.5–1.6 (local book) states that the covector inner product is induced from ℝ^P, which supports the basis independence in Step 3.
