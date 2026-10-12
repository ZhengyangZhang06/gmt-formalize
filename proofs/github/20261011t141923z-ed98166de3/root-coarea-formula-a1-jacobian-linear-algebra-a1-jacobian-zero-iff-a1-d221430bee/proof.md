# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_formula-a1.jacobian_linear_algebra-a1`
- Child DAG node: `root.coarea_formula-a1.jacobian_linear_algebra-a1.jacobian_zero_iff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1–3 of the parent proof (Part (1)), routed through the sibling bridge lemma. This is the route of the parent's parenthetical "apply SimonGMT coareaLinearJacobian_eq_sqrt_det and coareaLinearJacobian_eq_zero_iff to the linear map L".

Notation. Fix N, m, n, M, f, x, A with hT : tangentSpace M x = range A.
- T := tangentSpace M x and D := fderiv ℝ f x.
- L := ((fderiv ℝ f x).comp T.subtypeL).toLinearMap : T → ℝᵐ, so L t = D t for t ∈ T.
- L* := LinearMap.adjoint L : ℝᵐ → T.

1. By the sibling lemma jacobian_normdet_bridge (Submission.coareaJacobian_eq_normDet_adjoint N m M f x), coareaJacobian M f x = normDet(L*).

2. normDet(L*) = 0 iff ker(L*) ≠ 0 (Mathlib LinearMap.normDet_eq_zero_iff_ker_ne_bot: normDet vanishes exactly on non-injective maps). In the parent's terms, normDet(L*)² = det(LL*), and LL* is positive semidefinite with ker(LL*) = ker(L*): if LL*v = 0 then |L*v|² = ⟨LL*v, v⟩ = 0.

3. ker(L*) = (range L)^⊥ (Mathlib LinearMap.orthogonal_range: (range L)ᗮ = ker(L*)). Indeed v ∈ ker L* iff ⟨L*v, t⟩ = ⟨v, L t⟩ = 0 for all t ∈ T. In the finite-dimensional space ℝᵐ, (range L)^⊥ = 0 iff range L = ℝᵐ (Submodule.orthogonal_eq_bot_iff), iff L is surjective (LinearMap.range_eq_top). By steps 1–3, coareaJacobian M f x = 0 ⟺ ¬ Surjective L.

4. Claim: Surjective L ⟺ Surjective (D ∘L A).
   (⇒) Let y ∈ ℝᵐ. Choose t ∈ T with L t = D t = y. Since T = range A (hT), t = A z for some z ∈ ℝⁿ. Then (D ∘L A) z = D(A z) = D t = y.
   (⇐) Let y ∈ ℝᵐ and choose z ∈ ℝⁿ with D(A z) = y. Then A z ∈ range A = T, and the element t := A z of T satisfies L t = D(A z) = y.

5. Negate both sides of step 4 and combine with step 3: coareaJacobian M f x = 0 ⟺ ¬ Surjective L ⟺ ¬ Surjective ((fderiv ℝ f x).comp A). ∎

The case m = 0 needs no separate treatment. Then L* is a map out of the zero space, so normDet(L*) = 1 ≠ 0. Also every map into ℝ⁰ is surjective. Both sides of the equivalence are therefore false, and steps 2–5 cover this case verbatim.

Formalization note (optional guidance, not part of the mathematical argument). The following script was checked with the pinned toolchain in a copy of Submission.lean (namespace GMT.Ch02; only standard axioms; no extra import):

theorem Submission.coareaJacobian_eq_zero_iff_not_surjective : (∀ (N m n : ℕ) (M : Set (Rn N)) (f : Rn N → Rn m) (x : Rn N) (A : Rn n →L[ℝ] Rn N), tangentSpace M x = LinearMap.range A.toLinearMap → (coareaJacobian M f x = 0 ↔ ¬ Function.Surjective ((fderiv ℝ f x).comp A))) := by
  intro N m n M f x A hT
  rw [Submission.coareaJacobian_eq_normDet_adjoint, LinearMap.normDet_eq_zero_iff_ker_ne_bot,
    ← LinearMap.orthogonal_range, ne_eq, Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top]
  apply not_congr
  constructor
  · intro hs y
    obtain ⟨t, ht⟩ := hs y
    have : (t : Rn N) ∈ LinearMap.range A.toLinearMap := hT ▸ t.2
    obtain ⟨z, hz⟩ := this
    refine ⟨z, ?_⟩
    rw [← ht]
    have hz' : A z = (t : Rn N) := hz
    simp [hz']
  · intro hs y
    obtain ⟨z, hz⟩ := hs y
    have hmem : A z ∈ tangentSpace M x := hT ▸ LinearMap.mem_range_self A.toLinearMap z
    refine ⟨⟨A z, hmem⟩, ?_⟩
    simpa using hz

## Key steps

1. By the bridge lemma, coareaJacobian M f x = normDet(L*) with L = df_x|_T.
2. normDet(L*) = 0 ⟺ ker L* ≠ 0 ⟺ (range L)^⊥ ≠ 0 ⟺ range L ≠ ℝᵐ ⟺ L is not surjective.
3. T = range A gives range L = D(range A) = range(D∘A), so L is surjective iff (fderiv ℝ f x).comp A is surjective.

## Reference use

### local-project

Queries:
- `cat local-references/ff09f3909baeeae7/manifest.json`
- `sed -n 80,200p project/GMT/Ch02/Contract.lean`
- `grep -n "theorem\|lemma\|def \|^variable\|^section\|^namespace\|^end" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `sed -n 1,440p mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `grep -rn "OrthonormalBasis.prod\|def prod .*OrthonormalBasis\|theorem.*withLpProdComm\|def withLpProdComm\|orthogonalDecomposition" mathlib/Mathlib --include=*.lean`
- `sed -n 1,140p mathlib/Mathlib/Analysis/InnerProductSpace/ProdL2.lean`
- `grep -rn "theorem det_fromBlocks_zero\|theorem det_prodMap\|theorem toMatrix_prodMap\|det_restrict\|det_quotient\|theorem det_conj\b\|theorem det_comp\b" mathlib/Mathlib --include=*.lean`
- `sed -n 770,840p mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `grep -n "theorem adjoint_toLinearMap\|adjoint_toContinuousLinearMap\|theorem orthogonal_range\|theorem orthogonal_ker\|def adjoint" mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `sed -n 1,60p mathlib/Mathlib/Topology/Algebra/Module/Determinant.lean`
- `grep -rn "def orthogonalProjectionOnto\|orthogonalProjectionOnto_eq_zero_iff\|orthogonalProjectionOnto_mem_subspace_eq_self\|orthogonalProjectionOnto_apply_of_mem_orthogonal\|starProjection_add_starProjection_orthogonal" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/*.lean`
- `grep -rn "withLpProdComm" mathlib/Mathlib --include=*.lean`
- `cat lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean`
- `grep -rhoE '"lean_name": *"[^"]+"' nodes/ dag.json | sort -u`
- `grep -n "co-area\|6\.2" book/chapter-02.txt; sed -n 1405,1560p book/chapter-02.txt`
- `python3 -I gen_challenge.py (gmt-compare.py child_modules/contract_scope + lean_contract.validate_lean_statement) on the five child statements; lake env lean NodeChallenge_00..04.lean`
- `lean FullProof.lean / DepCheck.lean / FinalAssembly.lean with #print axioms; lean NodeSolution_00..05.lean against a scratch Submission.lean containing the proofs; lean Inst.lean (#synth InnerProductSpace ℝ (WithLp 2 (Rn 2 × Rn 3)))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/ProdL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Algebra/Module/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-jacobian-linear-algebra-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-c1-sard-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`

The manifest pins project 1b1689a8 and Mathlib 25730c7c, which match the workspace lake manifest.

project/GMT/Ch02/Contract.lean fixes the two definitions in play:
- tangentSpace (l.86);
- coareaJacobian (l.123): let L := (fderiv ℝ f x).comp (tangentSpace M x).subtypeL; Real.sqrt ((L ∘L adjoint L).det).
ContinuousLinearMap.det is an abbrev for LinearMap.det of the underlying map (Topology/Algebra/Module/Determinant.lean). ContinuousLinearMap.adjoint_toLinearMap holds by rfl (Adjoint.lean l.578).

Mathlib supplies everything else.
- NormDet.lean: normDet_nonneg, normDet_eq_zero_iff_ker_ne_bot (l.111), normDet_eq_norm_det_toMatrix (l.182), LinearIsometry.normDet_eq_one (l.213), normDet_id, normDet_sq (l.294), normDet_comp_of_finrank_eq (l.348), normDet_codRestrict (l.365).
- ProdL2.lean: OrthonormalBasis.prod with prod_apply, Submodule.orthogonalDecomposition and WithLp.prod_inner_apply.
- Matrix/Determinant/Basic.lean: Matrix.det_fromBlocks_zero₁₂ (l.728).
- LinearAlgebra/Determinant.lean: LinearMap.det_eq_det_mul_det, the quotient form of the block formula. It is not needed.
- Adjoint.lean: LinearMap.orthogonal_range and orthogonal_ker (l.632–642), adjoint_adjoint, eq_adjoint_iff.
- Projection/Basic.lean: orthogonalProjectionOnto, orthogonalProjectionOnto_apply_of_mem_orthogonal (l.484), orthogonalProjectionOnto_mem_subspace_eq_self (l.277).
- ProdLp.lean: LinearIsometryEquiv.withLpProdComm_apply (l.1208).

The pinned SimonGMT file CoareaLinearAlgebra.lean already proves coareaLinearJacobian_eq_sqrt_det, coareaLinearJacobian_eq_zero_iff, coareaCoordinates, coareaHorizontalLinear_coordinates, coareaHorizontalLinear_normDet and coarea_kernel_finrank. Its olean is built in the package tree. Only child (d) uses it, and the import is axiom-clean.

No snapshot file contains the block-triangular normDet lemma or the abstract Lemma L: grep for normDet together with fromBlocks/WithLp found only the generic pieces listed above. Hence children (c) and (d) are new.

All five statements validate and elaborate in the contract scope. Full proofs of the five children and of the parent compile with only propext, Classical.choice and Quot.sound, and so do the NodeSolution modules. The dependency-only checks and the stand-in assembly of the parent pass.

No dag.json or nodes/* file reserves any of the five names. The c1_sard branch's c1_sard_coarea_jacobian_eq_zero_iff has a different type and is not reused.

The book's §6, 6.2 (chapter-02.txt l.1410–1475) is the source of the argument.
