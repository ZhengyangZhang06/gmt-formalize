# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.orient_projection-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.orient_projection-a1.projected_gram_det-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3–4 of the parent proof, with the details filled in.
- Parent step 3: 0 ≤ G ≤ I. For every c ∈ ℝ^m, cᵀGc = ‖q(Σ_i c_iτ_i)‖² ∈ [0, Σ_i c_i²], because q is a contraction and τ is orthonormal.
- Parent step 4: by the spectral theorem the eigenvalues of G lie in [0, 1], and det G = Π_k λ_k ≤ 1.
This is the Gram-determinant form of "orthogonal projection does not increase area" (Simon Ch. 7 §3, footnote 2, chapter-07.txt lines 358–362). Here √det G is the m-dimensional Jacobian of q on span τ (Simon 6.3.4–3.5, chapter-06.txt lines 789–806).
Notation.
- ⟨·,·⟩ and ‖·‖ are the Euclidean inner product and norm, both on ℝ^P = Euclid P and on ℝ^m = EuclideanSpace ℝ (Fin m).
- q := V.starProjection : ℝ^P → ℝ^P, a continuous linear map. It exists for every subspace V, since ℝ^P is finite-dimensional and so V is complete.
- e_1, …, e_m is the standard orthonormal basis of ℝ^m (EuclideanSpace.basisFun).
- G is the m×m real matrix G_ij := ⟨qτ_i, qτ_j⟩, i.e. Matrix.of fun i j => inner ℝ (q (τ i)) (q (τ j)).
1. (Two linear maps on ℝ^m.) Let U, T : ℝ^m → ℝ^P be the linear maps defined on the basis e by U e_i := τ_i and T e_i := qτ_i (Basis.constr; Basis.constr_basis gives the values on each e_i). So U c = Σ_i c_iτ_i and T c = Σ_i c_i qτ_i. T and q∘U agree on every e_i, both giving qτ_i, so T = q∘U (Basis.ext). That is, Tc = q(Uc) = q(Σ_i c_iτ_i) for all c.
2. (U is an isometry.) U sends the orthonormal basis e to the orthonormal family τ, so ‖Uc‖ = ‖c‖ for all c ∈ ℝ^m (LinearMap.isometryOfOrthonormal). Explicitly, ‖Σ_i c_iτ_i‖² = Σ_i Σ_j c_i c_j ⟨τ_i, τ_j⟩ = Σ_i c_i² = ‖c‖², since ⟨τ_i, τ_j⟩ is 1 for i = j and 0 otherwise.
3. (T is a contraction.) Orthogonal projection does not increase norms: ‖qw‖ ≤ ‖w‖ for every w ∈ ℝ^P (Submodule.norm_starProjection_apply_le). Indeed ‖w‖² = ‖qw‖² + ‖w − qw‖², since w − qw ⊥ qw. By steps 1–2, ‖Tc‖ = ‖q(Uc)‖ ≤ ‖Uc‖ = ‖c‖ for every c ∈ ℝ^m.
4. (G is the matrix of the symmetric operator S := T*T.) Let T* : ℝ^P → ℝ^m be the adjoint of T (LinearMap.adjoint), and S := T*∘T : ℝ^m → ℝ^m.
- ⟨x, Sy⟩ = ⟨Tx, Ty⟩ for all x, y ∈ ℝ^m (LinearMap.adjoint_inner_right), so S is symmetric (LinearMap.isSymmetric_adjoint_comp_self).
- The (i, j) entry of the matrix of S in the orthonormal basis e is ⟨e_i, S e_j⟩ = ⟨T e_i, T e_j⟩ = ⟨qτ_i, qτ_j⟩ = G_ij (LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply).
- Hence det S = det G (LinearMap.det_toMatrix).
- In the parent's matrix language, for c ∈ ℝ^m: cᵀGc = ⟨c, Sc⟩ = ‖Tc‖² = ‖q(Σ_i c_iτ_i)‖² and cᵀc = ‖c‖². So step 3 is exactly the parent's 0 ≤ cᵀGc ≤ cᵀc.
5. (Spectral theorem.) ℝ^m has dimension m (finrank_euclideanSpace_fin). The spectral theorem for the symmetric operator S (LinearMap.IsSymmetric.eigenvectorBasis, .eigenvalues, .apply_eigenvectorBasis) gives an orthonormal basis u_1, …, u_m of ℝ^m and reals λ_1, …, λ_m with S u_k = λ_k u_k for every k. Moreover det S = Π_k λ_k (LinearMap.IsSymmetric.det_eq_prod_eigenvalues; over ℝ the coercion of λ_k is the identity).
6. (Each eigenvalue lies in [0, 1].) Fix k. Since ‖u_k‖ = 1, λ_k = λ_k‖u_k‖² = ⟨u_k, λ_k u_k⟩ = ⟨u_k, S u_k⟩ = ⟨T u_k, T u_k⟩ = ‖T u_k‖² (inner_smul_right, real_inner_self_eq_norm_sq, step 4). Hence λ_k ≥ 0. By step 3, 0 ≤ ‖T u_k‖ ≤ ‖u_k‖ = 1, so λ_k = ‖T u_k‖² ≤ 1 (pow_le_one₀).
7. (Conclusion.) By steps 4–6, det G = det S = Π_k λ_k is a finite product of reals in [0, 1], so det G ≤ 1 (Finset.prod_le_one₀). It is also ≥ 0, which is not needed.
8. (Edge cases.) For m = 0, ℝ^0 is the zero space, G is the empty matrix with det G = 1, and Π_k λ_k is the empty product 1, so the argument above applies unchanged. If m > P there is no orthonormal family of length m in ℝ^P, so the hypothesis never holds; the argument never uses m ≤ P. ∎
Formalization notes. The proof below was checked: it compiles after import GMT.Ch07.Submission in the contract scope (namespace GMT.Ch07, open Poincare.SimonGMT.Chapter06) and verbatim inside an end-to-end candidate file, with #print axioms = [propext, Classical.choice, Quot.sound].
- The parent's step 4 cites the matrix spectral API (Matrix.IsHermitian.eigenvalues_eq, Matrix.IsHermitian.det_eq_prod_eigenvalues, in Mathlib/Analysis/Matrix/Spectrum.lean). It is NOT in the import closure of the contract header: `Matrix.IsHermitian` is an unknown constant there.
- No extra import is needed. Steps 4–6 use the operator spectral theorem of Mathlib/Analysis/InnerProductSpace/Spectrum.lean, which is in scope. The accepted DAG declaration fvmb_gram_det_le_exp_sum_norm_sq_sub is proved with the same API.
- Use Finset.prod_le_one₀ (nonnegative factors), not the ordered-monoid Finset.prod_le_one.
- Verified tactic proof of the frozen type:
  intro P m V τ hτ
  classical
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  let v : Fin m → Euclid P := fun i => V.starProjection (τ i)
  -- `U eᵢ = τᵢ` (an isometry since `τ` is orthonormal), `T eᵢ = q τᵢ`, so `T = q ∘ U`
  let U : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] Euclid P := b.toBasis.constr ℝ τ
  let T : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] Euclid P := b.toBasis.constr ℝ v
  let S := LinearMap.adjoint T ∘ₗ T
  have hS : S.IsSymmetric := LinearMap.isSymmetric_adjoint_comp_self T
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := finrank_euclideanSpace_fin
  have hUe : ∀ a, U (b a) = τ a := by
    intro a
    have := b.toBasis.constr_basis ℝ τ a
    rw [OrthonormalBasis.coe_toBasis] at this
    exact this
  have hTe : ∀ a, T (b a) = v a := by
    intro a
    have := b.toBasis.constr_basis ℝ v a
    rw [OrthonormalBasis.coe_toBasis] at this
    exact this
  have hTU : ∀ c, T c = V.starProjection (U c) := by
    have hlin : T = (V.starProjection : Euclid P →L[ℝ] Euclid P).toLinearMap ∘ₗ U := by
      apply b.toBasis.ext
      intro a
      rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, hTe, hUe]
      rfl
    intro c
    rw [hlin]
    rfl
  have hUiso : ∀ c, ‖U c‖ = ‖c‖ := by
    intro c
    have hb : Orthonormal ℝ (b.toBasis : Fin m → EuclideanSpace ℝ (Fin m)) := by
      rw [OrthonormalBasis.coe_toBasis]; exact b.orthonormal
    have hf : Orthonormal ℝ (U ∘ b.toBasis) := by
      have hcomp : (U ∘ b.toBasis) = τ := by
        funext a
        simp only [Function.comp_apply, OrthonormalBasis.coe_toBasis, hUe]
      rw [hcomp]; exact hτ
    exact (U.isometryOfOrthonormal hb hf).norm_map c
  -- the orthogonal projection is a contraction, so `‖T c‖ ≤ ‖c‖`
  have hcontr : ∀ c, ‖T c‖ ≤ ‖c‖ := by
    intro c
    rw [hTU, ← hUiso c]
    exact V.norm_starProjection_apply_le (U c)
  have hSinner : ∀ x y, inner ℝ x (S y) = inner ℝ (T x) (T y) := by
    intro x y
    simp [S, LinearMap.adjoint_inner_right]
  -- the matrix of `S` in the standard basis is the Gram matrix `G`
  have hmat :
      LinearMap.toMatrix b.toBasis b.toBasis S = Matrix.of fun i j => inner ℝ (v i) (v j) := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, hSinner, hTe, hTe]
    rfl
  have hdet : LinearMap.det S = Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) := by
    rw [← LinearMap.det_toMatrix b.toBasis, hmat]
  -- spectral theorem: `λₖ = ⟪uₖ, S uₖ⟫ = ‖T uₖ‖² ∈ [0, 1]`
  have hbounds : ∀ k, 0 ≤ hS.eigenvalues hn k ∧ hS.eigenvalues hn k ≤ 1 := by
    intro k
    have h1 := hS.apply_eigenvectorBasis hn k
    have hu : ‖hS.eigenvectorBasis hn k‖ = 1 := (hS.eigenvectorBasis hn).orthonormal.1 k
    have h2 : inner ℝ (hS.eigenvectorBasis hn k) (S (hS.eigenvectorBasis hn k)) =
        hS.eigenvalues hn k := by
      rw [h1, inner_smul_right, real_inner_self_eq_norm_sq, hu]
      simp
    rw [← h2, hSinner, real_inner_self_eq_norm_sq]
    have h3 := hcontr (hS.eigenvectorBasis hn k)
    rw [hu] at h3
    have h4 := norm_nonneg (T (hS.eigenvectorBasis hn k))
    exact ⟨by positivity, pow_le_one₀ h4 h3⟩
  change Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) ≤ 1
  rw [← hdet, hS.det_eq_prod_eigenvalues hn]
  simp only [RCLike.ofReal_real_eq_id, id]
  exact Finset.prod_le_one₀ (fun k _ => (hbounds k).1) (fun k _ => (hbounds k).2)

## Key steps

1. Write T = q∘U on ℝ^m with U e_i = τ_i and T e_i = qτ_i. U is an isometry because τ is orthonormal, and q is a contraction, so ‖Tc‖ ≤ ‖c‖, i.e. 0 ≤ cᵀGc ≤ cᵀc.
2. G is the matrix of the symmetric operator S = T*T in the standard orthonormal basis, so det G = det S.
3. Spectral theorem for S: orthonormal eigenvectors u_k with λ_k = ⟨u_k, S u_k⟩ = ‖T u_k‖² ∈ [0, 1].
4. det G = Π_k λ_k ≤ 1.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project_commit b4d606db1da5…, mathlib_commit 25730c7c759d…)`
- `cat nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projec-af41a13265/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `python3 over dag.json: ids matching gram|orient_projection|subspace_projection-a1; lean_statements containing starProjection with IsUnitOrientationOf or compContinuousLinearMap; accepted lean_statements containing Matrix.det and inner (found covectorEuclideanNorm_gram_bounds, dtc_bc_lc_pf_unitOrientation_comp, dtc_bc_lc_pf_gram_det_le_prod_norm_sq, fvmb_gram_det_le_exp_sum_norm_sq_sub; statuses, candidate commits)`
- `python3 -I: byte-compare the dag.json lean_statement of covectorEuclideanNorm_gram_bounds with the `theorem Submission.covectorEuclideanNorm_gram_bounds` line of git show 2fd8f6ff9db8d5c94835632a4abd3e7d37106715:GMT/Ch07/Submission.lean (identical)`
- `cat nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projection-a1/{decomposition-v1.json,decomposition-v2.json,decomposition-scope-v2.json}; nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-9f4d277b67/{decomposition-v1.json,decomposition-scope-v1.json,parent-implementation-base.json}`
- `git show 2f77cee10b1d24bcd515ffe5a9f58f12e115348e:GMT/Ch07/Submission.lean | grep ^theorem (selected node's proof base: only main_theorem); git show 874d02d6dcf5…; import headers of accepted candidates 734e454c, 5c994751, a0bc3cde`
- `git show 734e454cc3d143c74375012e4aaee10059ec6d03:GMT/Ch07/Submission.lean, lines 445–510 (fvmb_gram_det_le_exp_sum_norm_sq_sub proved with the LinearMap.IsSymmetric spectral API under the contract header)`
- `rg -n 'theorem eigenvalues_eq|theorem det_eq_prod_eigenvalues|def eigenvectorBasis|def eigenvalues' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Matrix/Spectrum.lean; rg -n 'norm_starProjection_apply_le|starProjection_norm_le' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n -i hadamard /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib (only Hadamard products, no Hadamard inequality); rg -n 'theorem det_le|det_le_one|det_nonneg|eigenvalues_nonneg|det_le_prod' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib; grep theorem|lemma in Analysis/Matrix/Order.lean and Analysis/Matrix/PosDef.lean (no det ≤ 1 for 0 ≤ A ≤ I)`
- `rg -n 'def isometryOfOrthonormal|theorem apply_eigenvectorBasis|theorem det_eq_prod_eigenvalues|theorem isSymmetric_adjoint_comp_self|theorem constr_basis|theorem det_toMatrix|theorem finrank_euclideanSpace_fin|prod_le_one|pow_le_one₀|theorem ext \{|theorem coe_toBasis' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `sed -n 350,366p book/chapter-07.txt; sed -n 785,808p book/chapter-06.txt`
- `grep -n import verifier/gmt-compare.py; sed validate_lean_statement in verifier/lean_contract.py; python3 -I /tmp/op-decomp-af41/scripts/validate.py (both child types accepted unchanged)`
- `lake env lean /tmp/op-decomp-af41/Types.lean (parent and both child types; #check of the Gram Matrix.of)`
- `lake env lean /tmp/op-decomp-af41/Check.lean (first child draft via Matrix.IsHermitian fails: invalid field IsHermitian; assembly_check passes)`
- `lake env lean /tmp/op-decomp-af41/Check2.lean (Unknown constant Matrix.IsHermitian and Matrix.IsHermitian.det_eq_prod_eigenvalues; child_check, assembly_check, parent_from_children; #print axioms)`
- `lake env lean /tmp/op-decomp-af41/E2E.lean (accepted 2fd8f6f candidate + new child + Submission.dimred_cs_sp_orient_projection_le under the proposed names; #print axioms)`
- `grep -l dimred_cs_sp_op_ over nodes/, GMT/, dag.json and the 670 .swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean (no hits)`
- `WebSearch 'Gram determinant volume parallelotope orthogonal projection does not increase volume' → https://encyclopediaofmath.org/wiki/Gram_determinant (Gram determinant = squared volume of the parallelotope; Hadamard-type inequality)`
- `independent adversarial review subagent on /tmp/op-decomp-af41/draft_subproblems.json and the compile logs (verdict ACCEPT; five minor notes incorporated)`
- `python3 -I over the current dag.json (2391 nodes): count of nodes with children ∩ depends_on ≠ ∅ (90); re-check of lean_name collisions for dimred_cs_sp_op (none); covectorEuclideanNorm_gram_bounds status (accepted)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projec-af41a13265/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projec-af41a13265/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projec-af41a13265/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projection-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projection-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projection-a1/decomposition-scope-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-covector-gram-bounds-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-covector-gram-bounds-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-9f4d277b67/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-9f4d277b67/parent-implementation-base.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Matrix/Spectrum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Matrix/PosDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Matrix/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/op-decomp-af41/Types.lean`
- `/tmp/op-decomp-af41/Check.lean`
- `/tmp/op-decomp-af41/Check2.lean`
- `/tmp/op-decomp-af41/E2E.lean`
- `/tmp/op-decomp-af41/draft_subproblems.json`

Pins. The manifest gives project b4d606d (= workspace HEAD) and Mathlib 25730c7c, and the snapshot Contract.lean is the frozen contract.
Mathlib snapshot.
- The matrix spectral theorem cited by the supplied step 4 exists (Analysis/Matrix/Spectrum.lean: IsHermitian.eigenvalues_eq l.147, det_eq_prod_eigenvalues l.192). It is outside the contract's import closure: after import GMT.Ch07.Submission, Matrix.IsHermitian is an unknown constant.
- The operator spectral theorem is in scope: Analysis/InnerProductSpace/Spectrum.lean (apply_eigenvectorBasis l.324, det_eq_prod_eigenvalues l.389).
- Also in scope: LinearMap.isSymmetric_adjoint_comp_self (Adjoint.lean l.760), LinearMap.isometryOfOrthonormal (Orthonormal.lean l.330), Submodule.norm_starProjection_apply_le (Projection/Basic.lean l.411), Finset.prod_le_one₀ and pow_le_one₀.
- No Hadamard inequality and no det ≤ 1 for 0 ≤ A ≤ I: rg hadamard finds only Hadamard products, and PosSemidef gives only det ≥ 0.
DAG.
- covectorEuclideanNorm_gram_bounds is accepted (2fd8f6f) with a byte-identical type and is reused.
- dtc_bc_lc_pf_unitOrientation_comp and the Hadamard lemma dtc_bc_lc_pf_gram_det_le_prod_norm_sq are accepted, but they would replace supplied steps 3–4 rather than discharge them, so they are not used.
- fvmb_gram_det_le_exp_sum_norm_sq_sub (734e454) shows the operator spectral API compiles under the contract header.
- The selected node's proof base 2f77cee contains no Submission theorems.
Book. chapter-07.txt 358–362 (projection does not increase area) and chapter-06.txt 789–806 (3.4–3.5) match the cited sources.
Lean checks. Both child types elaborate and pass validate_lean_statement. The new child has a compiled proof. The frozen parent type compiles from the two children, including end to end with the real accepted gram_bounds proof, using only propext, Classical.choice and Quot.sound.
Names. The new name collides with nothing in the DAG, the node artifacts, GMT/ or the swarm worktrees.
