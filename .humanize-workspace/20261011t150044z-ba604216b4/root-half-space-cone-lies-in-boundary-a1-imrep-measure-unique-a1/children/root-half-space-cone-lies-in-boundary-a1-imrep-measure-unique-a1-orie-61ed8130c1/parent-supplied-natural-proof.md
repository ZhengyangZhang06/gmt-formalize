# Parent-supplied natural-language proof

- Parent DAG node: `root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1.orientation_common_covector-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1(b) and 1(d) of the parent proof of representation independence of θH^n⌞M (Simon Ch. 6, 3.2(3)): the frame-determinant covector δ_τ(w) = det(⟨τ_i, w_j⟩)_{i,j} satisfies δ_τ(τ) = 1 and, for any orthonormal τ' with the same span, δ_τ(τ') = det O ∈ {−1, +1} with O = (⟨τ_i, τ'_j⟩); hence a unit orientation built on τ or on τ' takes the value ±1 at δ_τ.

1. Unpack the hypotheses: there are orthonormal families τ, τ' : Fin n → ℝ^P with span(τ) = Q = span(τ') and signs ε_1, ε_2 ∈ {1, −1} such that ξ_1(α) = ε_1·α(τ) and ξ_2(α) = ε_2·α(τ') for every n-covector α.
2. (The frame-determinant covector.) For w = (w_1,…,w_n) ∈ (ℝ^P)^n put δ(w) := det(⟨τ_i, w_j⟩)_{i,j=1}^n. It is n-linear (the determinant is linear in each column, and the j-th column (⟨τ_i, w_j⟩)_i depends linearly on w_j alone) and alternating (if w_j = w_k for some j ≠ k the matrix has two equal columns, so δ(w) = 0). It is continuous: by the Leibniz formula and Cauchy–Schwarz with ‖τ_i‖ = 1, |δ(w)| ≤ Σ_σ ∏_j |⟨τ_{σ(j)}, w_j⟩| ≤ n!·∏_j ‖w_j‖, and a multilinear map satisfying such a bound is continuous. Hence δ is an n-covector on ℝ^P. (For n = 0, δ is the constant 1, the determinant of the empty matrix.)
3. δ(τ) = det(⟨τ_i, τ_j⟩) = det(I_n) = 1, by orthonormality of τ.
4. Put O_{ij} := ⟨τ_i, τ'_j⟩, so δ(τ') = det O. Each τ'_j lies in Q = span(τ); writing τ'_j = Σ_i c_i τ_i and pairing with τ_k gives c_k = ⟨τ_k, τ'_j⟩ = O_{kj}, i.e. τ'_j = Σ_i O_{ij} τ_i. Therefore ⟨τ'_j, τ'_k⟩ = Σ_i O_{ij} O_{ik} = (OᵀO)_{jk}. Since τ' is orthonormal, OᵀO = I_n, so (det O)² = det(Oᵀ)·det(O) = det(OᵀO) = 1 and det O ∈ {1, −1}.
5. Take α := δ. Then |ξ_1(δ)| = |ε_1|·|δ(τ)| = 1 by step 3 and |ξ_2(δ)| = |ε_2|·|det O| = 1 by step 4. ∎

Lean route used by the reference implementation (same covector, different bookkeeping): build orthonormal bases b, b' of the subspace Q from τ, τ' (OrthonormalBasis.mk; orthonormality transported by Q.subtypeₗᵢ.orthonormal_comp_iff, spanning by Submodule.mem_span_range_iff_exists_fun); δ := b.toBasis.det composed with the orthogonal projection π_Q = Q.orthogonalProjectionOnto (the b-coordinates of π_Q w_j are ⟨τ_i, w_j⟩, so this is the δ of step 2). Mathlib at this pin has no continuity theorem for multilinear maps on finite-dimensional spaces, so δ is made continuous with AlternatingMap.mkContinuous and the bound |δ(w)| = |volumeForm(π_Q w)| ≤ ∏‖π_Q w_i‖ ≤ ∏‖w_i‖ (Orientation.volumeForm_robust', Orientation.abs_volumeForm_apply_le, Submodule.norm_orthogonalProjectionOnto_apply_le, with Fact (finrank ℝ Q = n) and the orientation of b). Steps 3–4 become |δ(τ)| = |det_b b| = 1 and |δ(τ')| = |det_b b'| = 1 (Orientation.abs_volumeForm_apply_of_orthonormal; equivalently OrthonormalBasis.det_to_matrix_orthonormalBasis_real). SimonGMT's wedgeCovectors_apply_det (Chapter06/FormsDuality.lean) is not imported by GMT.Ch07.Submission.

Lean reference implementation (kernel-checked during this decomposition against GMT.Ch07.Submission, Lean v4.35.0-rc3, Mathlib 25730c7c; place inside `namespace GMT.Ch07` / `namespace Submission` with the contract's opens; #print axioms gives propext, Classical.choice, Quot.sound):
open scoped ContDiff Pointwise in
theorem unit_orientations_common_unit_covector : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ₁ ξ₂ : MultiVector P n), IsUnitOrientationOf ξ₁ Q → IsUnitOrientationOf ξ₂ Q → ∃ α : Covector (Euclid P) n, |ξ₁ α| = 1 ∧ |ξ₂ α| = 1 := by
  rintro P n Q ξ₁ ξ₂ ⟨τ, hτ, hspan, hξ₁⟩ ⟨τ', hτ', hspan', hξ₂⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let w : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hw : Orthonormal ℝ w := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := w)]
      exact hσ
    have hwspan : ⊤ ≤ Submodule.span ℝ (range w) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [w] using hc)⟩
    exact ⟨OrthonormalBasis.mk hw hwspan, fun i => by simp [w]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  have : Fact (Module.finrank ℝ Q = n) := ⟨by simpa using Module.finrank_eq_card_basis b.toBasis⟩
  let o : Orientation ℝ Q (Fin n) := b.toBasis.orientation
  let π : Euclid P →L[ℝ] Q := Q.orthogonalProjectionOnto
  -- the frame determinant `δ(w) = det_b (π_Q w)`
  let A : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := b.toBasis.det.compLinearMap π.toLinearMap
  have hA : ∀ w, ‖A w‖ ≤ 1 * ∏ i, ‖w i‖ := by
    intro w
    have h1 : |A w| = |o.volumeForm (fun i => π (w i))| :=
      (o.volumeForm_robust' b (fun i => π (w i))).symm
    rw [Real.norm_eq_abs, h1, one_mul]
    refine (o.abs_volumeForm_apply_le _).trans ?_
    gcongr with i
    exact Q.norm_orthogonalProjectionOnto_apply_le (w i)
  let δ : Covector (Euclid P) n := A.mkContinuous 1 hA
  have hπ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (i : Fin n), π (c i : Euclid P) = c i := fun c i =>
    Q.orthogonalProjectionOnto_mem_subspace_eq_self (c i)
  have hδ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
      (∀ i, (c i : Euclid P) = σ i) → |δ σ| = 1 := by
    intro c σ hc
    have h2 : δ σ = b.toBasis.det (fun i => π (σ i)) := rfl
    have h3 : (fun i => π (σ i)) = c := by
      funext i; rw [← hc i, hπ]
    rw [h2, h3, ← o.volumeForm_robust' b]
    exact o.abs_volumeForm_apply_of_orthonormal c
  refine ⟨δ, ?_, ?_⟩
  · rcases hξ₁ with h | h
    · rw [h]; exact hδ b τ hb
    · rw [h, abs_neg]; exact hδ b τ hb
  · rcases hξ₂ with h | h
    · rw [h]; exact hδ b' τ' hb'
    · rw [h, abs_neg]; exact hδ b' τ' hb'

## Key steps

1. Unpack: ξ_1(α) = ε_1α(τ), ξ_2(α) = ε_2α(τ') with τ, τ' orthonormal frames of Q and ε_k = ±1.
2. The frame determinant δ(w) = det(⟨τ_i, w_j⟩) is a continuous alternating n-form with δ(τ) = 1.
3. O = (⟨τ_i, τ'_j⟩) satisfies OᵀO = I because τ'_j = Σ_i O_{ij}τ_i, so δ(τ') = det O = ±1.
4. Hence |ξ_1(δ)| = |ξ_2(δ)| = 1; take α = δ.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cat local-references/123e8435b4a2469b/manifest.json`
- `sed -n 1,280p simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (blowUpMap, HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique)`
- `grep -n Covector simongmt/Poincare/SimonGMT/Chapter06/Forms.lean; sed -n 100,200p simongmt/Poincare/SimonGMT/Chapter06/Currents.lean (testFormOnSubmodule, TestFormOn, GeometricCurrentOn)`
- `grep -rn wedgeCovectors_apply_det simongmt/Poincare/SimonGMT (Chapter06/FormsDuality.lean; Unknown identifier after import GMT.Ch07.Submission)`
- `grep -n theorem mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean; sed -n 118,240p (IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero)`
- `sed -n 60,185p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_smul₀, Isometry.euclideanHausdorffMeasure_image)`
- `grep -rn det_to_matrix_orthonormalBasis_real mathlib/Mathlib; grep -rn eq_smul_basis_det mathlib/Mathlib; sed -n 150,300p mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean (volumeForm_robust', abs_volumeForm_apply_le, abs_volumeForm_apply_of_orthonormal)`
- `grep -rn continuous_of_finiteDimensional mathlib/Mathlib (no multilinear version); grep -n mkContinuous mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `grep -n integral_apply mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean; grep -n locallyIntegrableOn_iff mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean; grep -n subset_image_sdiff mathlib/Mathlib/Data/Set/Image.lean`
- `python3 census of lean_name fields in dag.json; grep -rhoE lean_name nodes dag.json problem.json | sort -u; grep -rl for each proposed name in nodes, dag.json, problem.json, local-references project, simongmt/Poincare (no match)`
- `lake env lean /tmp/imrep-unique-decomp/{Stmts,Assembly,Small,Frame,Inst,Inst2,Inst3,Inst4,Inst5,Fin,Vec4,All,StmtsExact,Final}.lean (#synth probes, conditional parent assembly, child trial proofs, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Image.lean`
- `/tmp/imrep-unique-decomp/Final.lean`
- `/tmp/imrep-unique-decomp/Assembly.lean`
- `/tmp/imrep-unique-decomp/StmtsExact.lean`
- `/tmp/imrep-unique-review/Cond.lean`

The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean.

Library support:
- SimonGMT Chapter03/Rectifiable.lean defines blowUpMap and HasApproximateTangentSpaceAt (Simon 3.1.4) and proves HasApproximateTangentSpaceAt.unique, which the parent uses.
- Mathlib (snapshot) supplies IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (Banach-valued, no local finiteness), ContinuousLinearMap.integral_apply, Measure.euclideanHausdorffMeasure_smul₀, Isometry.euclideanHausdorffMeasure_image, Set.subset_image_sdiff and setIntegral_congr_set.
- It also supplies the volume-form lemmas Orientation.volumeForm_robust', Orientation.abs_volumeForm_apply_le (Hadamard) and Orientation.abs_volumeForm_apply_of_orthonormal, plus OrthonormalBasis.det_to_matrix_orthonormalBasis_real.

Gaps:
- There is no continuity theorem for multilinear maps on finite-dimensional spaces, so the frame determinant is made continuous with AlternatingMap.mkContinuous.
- SimonGMT wedgeCovectors_apply_det is not reachable from Submission's imports.
- Instance search fails for ContinuousENorm, NormSMulClass ℝ and PseudoMetrizableSpace on MultiVector P n; the vector-density child's proof records the workaround that was tested.

Checks:
- All four child types and the parent type elaborate in namespace GMT.Ch07 with the contract's opens.
- The parent compiles from the four children with sorry'd proofs.
- Full trial proofs of all four children and of the parent assembly print axioms propext, Classical.choice, Quot.sound only.
- None of the four proposed names occurs in the DAG, the nodes, the project snapshot or SimonGMT.
