# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_formula-a1.jacobian_linear_algebra-a1`
- Child DAG node: `root.coarea_formula-a1.jacobian_linear_algebra-a1.chart_normdet_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 4–9 of the parent proof (Lemma L), with T = tangentSpace M x abstracted to an arbitrary finite-dimensional inner product space T. The isomorphism Ã becomes the bijection Φ and Θ₂ becomes Ψ. The block computation of parent Step 6 is the sibling lemma block_triangular_normdet.

Setup. P := WithLp 2 (ℝᵐ × ℝᵏ), with inner product ⟨p, p'⟩ = ⟨p₁, p'₁⟩ + ⟨p₂, p'₂⟩, where p₁ = WithLp.fst p and p₂ = WithLp.snd p. Hypotheses: (Hbij) Φ is bijective; (HL) L(Φ p) = p₁ for all p; (HΨ) Ψ b = Φ(toLp(0, b)) for all b.

1. L is surjective: for a ∈ ℝᵐ, L(Φ(toLp(a, 0))) = (toLp(a, 0))₁ = a by (HL).

2. Dimensions.
   - P ≅ ℝᵐ × ℝᵏ linearly (WithLp.linearEquiv), and dim ℝⁿ = n (finrank_euclideanSpace_fin), so dim P = m + k.
   - Φ is a linear isomorphism (LinearEquiv.ofBijective), so dim T = m + k.
   - Let Q := ker L ⊆ T and let Q^⊥ be its orthogonal complement in T. By rank–nullity and step 1 (range L = ℝᵐ), dim Q = (m + k) − m = k. This is SimonGMT Chapter02.coarea_kernel_finrank, or LinearMap.finrank_range_add_finrank_ker.
   - Since dim Q + dim Q^⊥ = dim T (Submodule.finrank_add_finrank_orthogonal), dim Q^⊥ = m.

3. Orthogonal coordinates. Let π₁ : T → Q^⊥ and π₂ : T → Q be the orthogonal projections (Submodule.orthogonalProjectionOnto). Then t = π₁ t + π₂ t, and C : T → WithLp 2 (Q^⊥ × Q), C t := toLp(π₁ t, π₂ t), is a linear isometric equivalence (by Pythagoras). In Lean one may take C := SimonGMT Chapter02.coareaCoordinates L, i.e. (ker L).orthogonalDecomposition followed by LinearIsometryEquiv.withLpProdComm. Its value is toLp(π₁ t, π₂ t), by simp with Submodule.orthogonalDecomposition_apply and LinearIsometryEquiv.withLpProdComm_apply.

4. Let G := C ∘ Φ : P → WithLp 2 (Q^⊥ × Q). Since dim P = dim T, normDet(G) = normDet(C) · normDet(Φ) (LinearMap.normDet_comp_of_finrank_eq). normDet(C) = 1 because C is a linear isometry (LinearIsometry.normDet_eq_one). Hence normDet G = normDet Φ.

5. Ψ maps into Q: L(Ψ b) = L(Φ(toLp(0, b))) = (toLp(0, b))₁ = 0. Consequently, for every b ∈ ℝᵏ:
   - (G(toLp(0, b)))₁ = π₁(Φ(toLp(0, b))) = π₁(Ψ b) = 0, because Ψ b ∈ Q ⊆ (Q^⊥)^⊥ (Submodule.le_orthogonal_orthogonal, Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal);
   - (G(toLp(0, b)))₂ = π₂(Ψ b) = Ψ b (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self).

6. Define linear maps α : ℝᵐ → Q^⊥, α a := (G(toLp(a, 0)))₁ = π₁(Φ(toLp(a, 0))), and Θ : ℝᵏ → Q, Θ b := (G(toLp(0, b)))₂. They are linear as compositions of G with the linear embeddings a ↦ toLp(a, 0), b ↦ toLp(0, b) and the coordinate maps WithLp.fstL, WithLp.sndL. By step 5, Θ b = Ψ b for all b, i.e. Θ = Ψ.codRestrict Q. Following a map by the isometric inclusion of a subspace does not change normDet (LinearMap.normDet_codRestrict), so normDet Θ = normDet Ψ.

7. Apply the sibling lemma block_triangular_normdet (Submission.coarea_normDet_block_triangular) with E₁ := ℝᵐ, E₂ := ℝᵏ, F₁ := Q^⊥, F₂ := Q, the map G, G₁₁ := α and G₂₂ := Θ. Its hypotheses hold:
   - dim ℝᵐ = m = dim Q^⊥ and dim ℝᵏ = k = dim Q (step 2);
   - (G(toLp(0, b)))₁ = 0 (step 5);
   - α and Θ satisfy their defining equations by construction (step 6).
   Hence normDet G = normDet α · normDet Θ. With steps 4 and 6: normDet Φ = normDet α · normDet Ψ.

8. Let λ := L|_{Q^⊥} : Q^⊥ → ℝᵐ (SimonGMT Chapter02.coareaHorizontalLinear L = L.domRestrict (ker L)ᗮ). For t ∈ T, π₂ t ∈ Q = ker L, so λ(π₁ t) = L(π₁ t) = L(t − π₂ t) = L t (SimonGMT Chapter02.coareaHorizontalLinear_coordinates). Taking t := Φ(toLp(a, 0)) gives λ(α a) = L(Φ(toLp(a, 0))) = a by (HL), so λ ∘ α = id on ℝᵐ. Since dim ℝᵐ = m = dim Q^⊥, normDet(λ ∘ α) = normDet λ · normDet α (LinearMap.normDet_comp_of_finrank_eq), and normDet(id) = 1 (LinearMap.normDet_id). Therefore normDet λ · normDet α = 1.

9. normDet λ = normDet(L*). This is SimonGMT Chapter02.coareaHorizontalLinear_normDet for surjective L (step 1): its statement is (coareaHorizontalLinear L).normDet = coareaLinearJacobian L, and coareaLinearJacobian L := L.adjoint.normDet by definition. A self-contained proof:
   (i) range L* = (ker L)^⊥ = Q^⊥ (LinearMap.orthogonal_ker). So κ := L*.codRestrict Q^⊥ : ℝᵐ → Q^⊥ is defined, and normDet κ = normDet L* (normDet_codRestrict).
   (ii) For y ∈ ℝᵐ and q ∈ Q^⊥: ⟨κ y, q⟩ = ⟨L* y, q⟩ = ⟨y, L q⟩ = ⟨y, λ q⟩. Hence κ = λ* (LinearMap.eq_adjoint_iff).
   (iii) λ maps between two spaces of dimension m. In orthonormal bases with a common index type, the matrix of λ* is the transpose of the matrix Λ of λ (LinearMap.toMatrix_adjoint). So normDet λ* = |det Λᵀ| = |det Λ| = normDet λ (normDet_eq_norm_det_toMatrix; this is SimonGMT normDet_adjoint_of_finrank_eq).
   Thus normDet L* = normDet κ = normDet λ* = normDet λ.

10. Conclusion: normDet(L*) · normDet(Φ) = normDet λ · (normDet α · normDet Ψ) = (normDet λ · normDet α) · normDet Ψ = 1 · normDet Ψ = normDet Ψ. ∎

Degenerate cases.
- m = 0: Q^⊥ = 0, and α, λ are maps between zero spaces with normDet 1.
- k = 0: Q = 0, and Θ, Ψ are maps out of the zero space with normDet 1.
All steps hold verbatim; the block lemma has no positivity requirement on the dimensions.

Formalization note (optional guidance, not part of the mathematical argument). The following script was checked with the pinned toolchain in a copy of Submission.lean (namespace GMT.Ch02; only standard axioms). It uses the pinned SimonGMT library, so add `import Poincare.SimonGMT.Chapter02.CoareaLinearAlgebra` to the import block of Submission.lean. This is permitted: the comparator byte-checks only the frozen files, and those SimonGMT lemmas use only propext, Classical.choice and Quot.sound. `open Poincare.SimonGMT` is already in the contract's scope, so `Chapter02.` resolves:

theorem Submission.coarea_normDet_adjoint_mul_normDet_chart : (∀ (m k : ℕ) (T : Type) [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T] (L : T →ₗ[ℝ] Rn m) (Φ : WithLp 2 (Rn m × Rn k) →ₗ[ℝ] T) (Ψ : Rn k →ₗ[ℝ] T), Function.Bijective Φ → (∀ p, L (Φ p) = WithLp.fst p) → (∀ b, Ψ b = Φ (WithLp.toLp 2 (0, b))) → (LinearMap.adjoint L).normDet * Φ.normDet = Ψ.normDet) := by
  intro m k T _ _ _ L Φ Ψ hΦ hL hΨ
  have hsurj : Function.Surjective L := fun a => ⟨Φ (WithLp.toLp 2 (a, 0)), by rw [hL]; rfl⟩
  have hP : Module.finrank ℝ (WithLp 2 (Rn m × Rn k)) = m + k := by
    rw [(WithLp.linearEquiv 2 ℝ (Rn m × Rn k)).finrank_eq, Module.finrank_prod]
    simp
  have hT : Module.finrank ℝ T = m + k := by
    rw [← (LinearEquiv.ofBijective Φ hΦ).finrank_eq, hP]
  have hQ : Module.finrank ℝ (LinearMap.ker L) = k := by
    rw [Chapter02.coarea_kernel_finrank hsurj, hT, finrank_euclideanSpace_fin]
    omega
  have hQperp : Module.finrank ℝ (LinearMap.ker L)ᗮ = m := by
    have := (LinearMap.ker L).finrank_add_finrank_orthogonal
    omega
  let C := Chapter02.coareaCoordinates L
  let G : WithLp 2 (Rn m × Rn k) →ₗ[ℝ] WithLp 2 ((LinearMap.ker L)ᗮ × LinearMap.ker L) :=
    C.toLinearEquiv.toLinearMap ∘ₗ Φ
  let inl : Rn m →ₗ[ℝ] WithLp 2 (Rn m × Rn k) :=
    (WithLp.linearEquiv 2 ℝ (Rn m × Rn k)).symm.toLinearMap ∘ₗ LinearMap.inl ℝ (Rn m) (Rn k)
  let inr : Rn k →ₗ[ℝ] WithLp 2 (Rn m × Rn k) :=
    (WithLp.linearEquiv 2 ℝ (Rn m × Rn k)).symm.toLinearMap ∘ₗ LinearMap.inr ℝ (Rn m) (Rn k)
  let G₁₁ : Rn m →ₗ[ℝ] (LinearMap.ker L)ᗮ := (WithLp.fstL 2 ℝ _ _).toLinearMap ∘ₗ G ∘ₗ inl
  let G₂₂ : Rn k →ₗ[ℝ] LinearMap.ker L := (WithLp.sndL 2 ℝ _ _).toLinearMap ∘ₗ G ∘ₗ inr
  have hC : ∀ t, C t = WithLp.toLp 2 ((LinearMap.ker L)ᗮ.orthogonalProjectionOnto t,
      (LinearMap.ker L).orthogonalProjectionOnto t) := by
    intro t
    simp [C, Chapter02.coareaCoordinates, LinearIsometryEquiv.withLpProdComm_apply]
  have hΨmem : ∀ b, Ψ b ∈ LinearMap.ker L := by
    intro b; rw [LinearMap.mem_ker, hΨ, hL]; rfl
  have h0 : ∀ b, WithLp.fst (G (WithLp.toLp 2 (0, b))) = 0 := by
    intro b
    simp only [G, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    rw [← hΨ, hC]
    simp [Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
      ((LinearMap.ker L).le_orthogonal_orthogonal (hΨmem b))]
  have hG := Submission.coarea_normDet_block_triangular (Rn m) (Rn k) _ _ G G₁₁ G₂₂ (by simp [hQperp]) (by simp [hQ]) h0
    (fun a => rfl) (fun b => rfl)
  have hGΦ : G.normDet = Φ.normDet := by
    rw [LinearMap.normDet_comp_of_finrank_eq _ _ (by rw [hP, hT])]
    have : (C.toLinearEquiv.toLinearMap).normDet = 1 := C.toLinearIsometry.normDet_eq_one
    rw [this, one_mul]
  have hG₂₂ : G₂₂ = Ψ.codRestrict (LinearMap.ker L) hΨmem := by
    refine LinearMap.ext fun b => ?_
    apply Subtype.ext
    simp only [G₂₂, G, inr, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearMap.codRestrict_apply]
    have : (WithLp.linearEquiv 2 ℝ (Rn m × Rn k)).symm (LinearMap.inr ℝ (Rn m) (Rn k) b) = WithLp.toLp 2 (0, b) := rfl
    rw [this, ← hΨ, hC]
    simp [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨Ψ b, hΨmem b⟩]
  let lam := Chapter02.coareaHorizontalLinear L
  have hlam : lam ∘ₗ G₁₁ = LinearMap.id := by
    refine LinearMap.ext fun a => ?_
    have h := Chapter02.coareaHorizontalLinear_coordinates L (Φ (WithLp.toLp 2 (a, 0)))
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [hL] at h
    exact h
  have h1 : lam.normDet * G₁₁.normDet = 1 := by
    rw [← LinearMap.normDet_comp_of_finrank_eq _ _ (by simp [hQperp]), hlam, LinearMap.normDet_id]
  have hlamJ : lam.normDet = (LinearMap.adjoint L).normDet :=
    Chapter02.coareaHorizontalLinear_normDet hsurj
  rw [← hGΦ, hG, hG₂₂, LinearMap.normDet_codRestrict, ← hlamJ, ← mul_assoc, h1, one_mul]

## Key steps

1. L is surjective; dim P = dim T = m + k, dim ker L = k and dim (ker L)^⊥ = m.
2. C := (π_{Q^⊥}, π_Q) : T → WithLp 2 (Q^⊥ × Q) is a linear isometric equivalence, so normDet(C∘Φ) = normDet Φ.
3. Ψ maps into Q = ker L, so C∘Φ is block lower triangular. The block lemma gives normDet Φ = normDet α · normDet Θ with α = π_{Q^⊥}∘Φ∘(·,0) and Θ = Ψ.codRestrict Q, and normDet Θ = normDet Ψ.
4. λ := L|_{Q^⊥} satisfies λ∘α = id, so normDet λ · normDet α = 1.
5. normDet λ = normDet L* (coareaHorizontalLinear_normDet), hence normDet L* · normDet Φ = normDet Ψ.

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
