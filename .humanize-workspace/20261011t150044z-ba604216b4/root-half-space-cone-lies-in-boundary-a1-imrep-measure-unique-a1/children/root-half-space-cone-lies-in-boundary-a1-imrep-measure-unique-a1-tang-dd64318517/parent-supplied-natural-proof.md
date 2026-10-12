# Parent-supplied natural-language proof

- Parent DAG node: `root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1.tangent_null_invariance-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof of representation independence of θH^n⌞M (Simon Ch. 6, 3.2(3)): blow-ups of H^n-a.e. equal sets coincide up to H^n-null sets, so the limits in Simon Ch. 3, 1.4 (approximate tangent space) agree.

Notation: H^n = μHE[n]; for r ∈ ℝ, b_r := blowUpMap x r, b_r(y) = r^{-1}(y − x) (Simon's η_{x,r}).
1. (Definition.) HasApproximateTangentSpaceAt n M x Q means: finrank Q = n and, for every f ∈ C_c(ℝ^P), φ_M^f(r) := ∫_{b_r(M)} f dH^n converges to ∫_Q f dH^n as r → 0 with r > 0 (along the filter 𝓝[>] 0).
2. (Null sets stay null under b_r, r ≠ 0.) Let S ⊆ ℝ^P with H^n(S) = 0. Then b_r(S) = r^{-1}·(S − x), where S − x is the image of S under the isometry y ↦ y − x. Isometries preserve H^n (Mathlib Isometry.euclideanHausdorffMeasure_image), so H^n(S − x) = 0; and H^n(c·S') = |c|^n·H^n(S') for c ≠ 0 (Mathlib Measure.euclideanHausdorffMeasure_smul₀). Hence H^n(b_r(S)) = 0.
3. (The blow-ups agree up to null sets.) For any map b, b(A) ∖ b(B) ⊆ b(A ∖ B): if y = b(a) with a ∈ A and y ∉ b(B), then a ∉ B (Mathlib Set.subset_image_sdiff). Likewise b(B) ∖ b(A) ⊆ b(B ∖ A). By the hypotheses H^n(A ∖ B) = 0 = H^n(B ∖ A) and step 2, for every r ≠ 0 both differences b_r(A) ∖ b_r(B) and b_r(B) ∖ b_r(A) are H^n-null, i.e. b_r(A) and b_r(B) coincide up to an H^n-null set (Mathlib ae_eq_set). Consequently H^n⌞b_r(A) = H^n⌞b_r(B), and φ_A^f(r) = φ_B^f(r) for every f ∈ C_c(ℝ^P) and every r ≠ 0 (Mathlib setIntegral_congr_set). No integrability is needed: the two set integrals are integrals against the same restricted measure.
4. (The limits agree.) Fix f ∈ C_c(ℝ^P). The set (0, ∞) belongs to 𝓝[>] 0 (self_mem_nhdsWithin) and φ_A^f = φ_B^f on it by step 3, so φ_A^f converges to L along 𝓝[>] 0 if and only if φ_B^f does (Filter.Tendsto.congr').
5. The dimension clause finrank Q = n is literally the same on both sides. Combining it with step 4 for every f ∈ C_c(ℝ^P) gives HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q, for every x and every Q. ∎

Lean reference implementation (kernel-checked during this decomposition against GMT.Ch07.Submission, Lean v4.35.0-rc3, Mathlib 25730c7c; place inside `namespace GMT.Ch07` / `namespace Submission` with the contract's opens; #print axioms gives propext, Classical.choice, Quot.sound):
open scoped ContDiff Pointwise in
theorem hasApproximateTangentSpaceAt_iff_of_null_sdiff : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), μHE[n] (A \ B) = 0 → μHE[n] (B \ A) = 0 → (HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q) := by
  intro P n A B x Q hAB hBA
  have himg_null : ∀ r : ℝ, r ≠ 0 → ∀ S : Set (Euclid P), μHE[n] S = 0 →
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) = 0 := by
    intro r hr S hS
    have himg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S =
        r⁻¹ • ((fun y => y - x) '' S) := by
      rw [← Set.image_smul, Set.image_image]
      rfl
    have hiso : Isometry (fun y : Euclid P => y - x) := (IsometryEquiv.subRight x).isometry
    rw [himg, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr),
      hiso.euclideanHausdorffMeasure_image, hS, smul_zero]
  have hint : ∀ r : ℝ, r ≠ 0 → ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n] =
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] := by
    intro r hr f
    apply setIntegral_congr_set
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hAB)
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hBA)
  constructor
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hint r (ne_of_gt hr) f
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hint r (ne_of_gt hr) f).symm

## Key steps

1. For r ≠ 0, η_{x,r} is a translation followed by a dilation, so it maps H^n-null sets to H^n-null sets.
2. η(A) ∖ η(B) ⊆ η(A ∖ B) and η(B) ∖ η(A) ⊆ η(B ∖ A), so the blow-ups of A and B agree up to H^n-null sets and their integrals coincide for every r > 0.
3. Functions that agree on (0, ∞) have the same limits along 𝓝[>] 0, and the dimension clause is shared, so the two predicates are equivalent.

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
