# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.orientation_pushforward-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.orientation_pushforward-a1.gram_basis_invariance-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (basis independence of the Gram determinant). The parent's alternative via LinearMap.normDet is not usable here because Mathlib's NormDet and GramMatrix files are not in the import closure of GMT.Ch07.Submission. Instead the proof goes through the basis-free determinant of L'^* L'.

Notation: ⟨·,·⟩ is the Euclidean inner product of ℝ^P. Q carries the restricted inner product, so it is a finite-dimensional inner product space. ι_Q : Q → ℝ^P is the inclusion. For a finite index type ι and a family b : ι → Q, G(Lb) := (⟨L b_i, L b_j⟩)_{i,j∈ι}.

1. The endomorphism T. Let L' := L ∘ ι_Q : Q → ℝ^P, a linear map between finite-dimensional inner product spaces. Let L'^* : ℝ^P → Q be its adjoint, so ⟨x, L'^* y⟩ = ⟨L' x, y⟩ for all x ∈ Q and y ∈ ℝ^P (LinearMap.adjoint, LinearMap.adjoint_inner_right). Put T := L'^* ∘ L' : Q → Q, a linear endomorphism of Q.

2. Claim: for every finite index type ι (with decidable equality) and every orthonormal basis b = (b_i)_{i∈ι} of Q, det G(Lb) = det T.
   - The (i, j) entry of the matrix of T in the basis b (LinearMap.toMatrix b b T) is the i-th coordinate of T b_j (LinearMap.toMatrix_apply).
   - For an orthonormal basis, the i-th coordinate of x ∈ Q is ⟨b_i, x⟩ (OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply).
   - So the entry equals ⟨b_i, L'^*(L' b_j)⟩ = ⟨L' b_i, L' b_j⟩ = ⟨L b_i, L b_j⟩. Thus the matrix of T in b is exactly G(Lb).
   - The determinant of the matrix of an endomorphism in any basis is the determinant of the endomorphism (LinearMap.det_toMatrix), so det G(Lb) = det T.
   - If ι is empty, both sides are 1.

3. τ is an orthonormal basis of Q.
   - Each τ_a lies in span{τ_1, …, τ_n} = Q. Let τ'_a ∈ Q denote τ_a regarded as an element of Q, so ι_Q(τ'_a) = τ_a.
   - Norms and inner products in Q are computed in ℝ^P, so |τ'_a| = 1 and ⟨τ'_a, τ'_c⟩ = 0 for a ≠ c. Hence τ' is orthonormal in Q.
   - τ' spans Q. The map ι_Q sends span(τ') onto span(ι_Q ∘ τ') = span τ = Q = ι_Q(Q) (Submodule.map_span, Set.range_comp, Submodule.map_top, Submodule.range_subtype). Because ι_Q is injective, the induced map on submodules of Q is injective (Submodule.map_injective_of_injective). Therefore span(τ') = Q, the top submodule of Q.
   - Hence τ' is an orthonormal basis of Q indexed by Fin n (OrthonormalBasis.mk applied to the orthonormality and the spanning property).

4. Conclusion.
   - Step 2 with b = e := stdOrthonormalBasis ℝ Q (index type Fin (finrank ℝ Q)) gives det(⟨L e_i, L e_j⟩)_{i,j} = det T.
   - Step 2 with b = τ' (index type Fin n) gives det G(Lτ') = det T. Since ι_Q(τ'_a) = τ_a, G(Lτ') = (⟨L τ_a, L τ_b⟩)_{a,b}.
   - Therefore det(⟨L e_i, L e_j⟩)_{i,j ∈ Fin(finrank Q)} = det T = det(⟨L τ_a, L τ_b⟩)_{a,b ∈ Fin n}.
   - The argument uses neither injectivity of L nor the equality finrank Q = n (which does hold, but is not needed). ∎

Formalization notes (all names are available after import GMT.Ch07.Submission, so no new import is needed). With L' := (L : Euclid P →ₗ[ℝ] Euclid P) ∘ₗ Q.subtype and T := LinearMap.adjoint L' ∘ₗ L', state a local have:
  key : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ Q), Matrix.det (Matrix.of fun i j : ι => inner ℝ (L (b i : Euclid P)) (L (b j : Euclid P))) = LinearMap.det T
Prove it by rw [← LinearMap.det_toMatrix b.toBasis T], congr 1, ext i j, rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply], then simp only [T, LinearMap.comp_apply, LinearMap.adjoint_inner_right, Matrix.of_apply] and rfl. Apply key to stdOrthonormalBasis ℝ Q and to OrthonormalBasis.mk hτ' hspan'; that basis coerces back to τ by simp.

## Key steps

1. Let T := L'^* L' on Q, where L' is L restricted to Q and L'^* is its adjoint.
2. For any orthonormal basis b of Q, the matrix of T in b is the Gram matrix (⟨L b_i, L b_j⟩), so its determinant is det T.
3. τ regarded in Q is orthonormal and spans Q (inclusion injective, span τ = Q), so it is an orthonormal basis of Q.
4. Apply the previous step to stdOrthonormalBasis ℝ Q and to τ: both Gram determinants equal det T.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c)`
- `diff -q <snapshot>/project/GMT/Ch07/Submission.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n 'theorem gramSchmidtOrthonormalBasis_det|theorem normDet_sq_eq_det_gram|theorem gram_eq_conjTranspose_mul|theorem AlternatingMap.eq_smul_basis_det|theorem det_toMatrix|theorem adjoint_inner_right|theorem is_basis_iff_det|theorem finrank_span_eq_card|theorem sum_inner_mul_inner|lemma prod_le_prod₀' <snapshot>/mathlib/Mathlib`
- `rg -n -i 'hadamard.*inequality|det_le_prod_norm|abs_det_le_prod' <snapshot>/mathlib/Mathlib (no match: Mathlib has no Hadamard determinant inequality)`
- `rg -n 'gramSchmidt|stdOrthonormalBasis|IsUnitOrientationOf|normDet' <snapshot>/project/GMT --glob '*.lean' (only contract definitions; no prior proof of this statement)`
- `rg -n 'def compContinuousLinearMapCLM' and 'gramSchmidtOrthonormalBasis(_inv_triangular)' in the snapshot Mathlib`
- `grep -n theorem/def in Mathlib/Analysis/InnerProductSpace/{NormDet,GramMatrix,GramSchmidtOrtho}.lean`
- `python3 -I dag.json scans: lean_name/lean_statement for dgoj_*, covectorEuclideanNorm_gram_bounds, stdOrthonormalBasis, LinearIndependent+Orthonormal, gramSchmidt; collision checks for dpf_det_gram_stdOrthonormalBasis_eq and dpf_exists_orthonormal_frame_det_gram (no hits)`
- `grep -l <new names> nodes/*/*.json (no hits); git grep over 1083 branch tips -- GMT (no hits)`
- `git show 73310ec:GMT/Ch07/Submission.lean (accepted proof of Submission.dgoj_covector_eq_det_mul_of_mem_span)`
- `read controller /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_existing_lean_name_problem, child materialization by lean_name, _install_parent_supplied_child_handoff, _overlay_accepted_children) and leaf_verification.py (single-theorem leaf delta, no import)`
- `lake env lean /tmp/dpf-orient-split/Avail.lean and Avail2.lean (gramSchmidtOrthonormalBasis(_det), LinearMap.adjoint, LinearMap.det_toMatrix available; LinearMap.normDet_sq_eq_det_gram, Matrix.gram_eq_conjTranspose_mul, Matrix.det_gram_ne_zero_iff_linearIndependent NOT available after import GMT.Ch07.Submission)`
- `lake env lean /tmp/dpf-orient-split/{Types,Assembly,Child1,Child2,Full}.lean and /tmp/dpf-orient-split/final/Final.lean (#print axioms: propext, Classical.choice, Quot.sound)`
- `sed -n 780,835p book/sources/chapter-06-source.txt (Simon 6.3.4-3.7)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-orientati-f9454fcfd5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/parent_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-06-source.txt`
- `/tmp/dpf-orient-split/final/Final.lean`
- `/tmp/dpf-orient-split/Child1.lean`
- `/tmp/dpf-orient-split/Child2.lean`
- `/tmp/dpf-orient-split/Assembly.lean`

The pinned local snapshot (project b4d606d, mathlib 25730c7c) does not prove this statement or either new child. Snapshot Ch07 Submission is identical to the workspace one and contains only contract definitions. One required step already exists as the comparator-accepted Submission.dgoj_covector_eq_det_mul_of_mem_span (candidate commit 73310ec). Its frozen type is byte-identical, so it is reused rather than re-proved.

Library facts in the Submission's import closure:
- gramSchmidtOrthonormalBasis and gramSchmidtOrthonormalBasis_det (GramSchmidtOrtho.lean:318, 374);
- LinearMap.adjoint and adjoint_inner_right (Adjoint.lean:592);
- LinearMap.det_toMatrix and Module.Basis.is_basis_iff_det (Determinant.lean:206, 625);
- AlternatingMap.eq_smul_basis_det (Determinant.lean:650);
- OrthonormalBasis.sum_inner_mul_inner (PiL2.lean:506);
- finrank_span_eq_card (Constructions.lean:463);
- Finset.prod_le_prod₀ (BigOperators/GroupWithZero/Finset.lean:38).

Not available after import GMT.Ch07.Submission, so the child proofs avoid them:
- LinearMap.normDet_sq_eq_det_gram (NormDet.lean:303);
- Matrix.gram_eq_conjTranspose_mul (GramMatrix.lean:130).

Mathlib has no Hadamard determinant inequality (rg: no match), so the bound J ≤ ‖L‖^n uses the Gram–Schmidt upper-triangular determinant. Leaf candidates may insert only one theorem without imports. Both new children were proved in exactly that form in scratch Lean, and the parent assembly compiles from the three child types. Final.lean (both children, the accepted text of (c) and the assembly) depends only on propext, Classical.choice and Quot.sound.
