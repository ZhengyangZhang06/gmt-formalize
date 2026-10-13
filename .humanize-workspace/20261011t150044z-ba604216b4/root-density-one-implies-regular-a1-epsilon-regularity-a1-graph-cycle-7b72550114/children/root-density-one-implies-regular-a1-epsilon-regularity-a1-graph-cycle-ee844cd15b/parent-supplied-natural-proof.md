# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1.det_covector-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (δ := the standard determinant n-form made into a continuous alternating map, via the volume form of the standard orientation, o.volumeForm.mkContinuous 1 with Orientation.abs_volumeForm_apply_le; δ(e₁, …, eₙ) = 1).
Notation: ℝᵐ means Euclid m = EuclideanSpace ℝ (Fin m); ⟨x, y⟩ is inner ℝ x y; e_j := EuclideanSpace.single j (1 : ℝ) is the j-th standard basis vector of ℝⁿ; an n-covector of ℝᴾ is an element of Covector (Euclid P) n = Euclid P [⋀^Fin n]→L[ℝ] ℝ (a continuous alternating n-linear map ℝᴾ × ⋯ × ℝᴾ → ℝ); MultiVector P n = Covector (Euclid P) n →L[ℝ] ℝ (continuous linear functionals on n-covectors); for a continuous linear map F, F* = F.adjoint and det of an endomorphism is ContinuousLinearMap.det (= LinearMap.det of the underlying linear map).
1. Setup. finrank ℝⁿ = n (finrank_euclideanSpace_fin), recorded as the instance Fact (finrank ℝ (Euclid n) = n) required by Orientation.volumeForm. Let B := EuclideanSpace.basisFun (Fin n) ℝ, the standard orthonormal basis of ℝⁿ (Bᵢ = eᵢ, EuclideanSpace.basisFun_apply), and o := B.toBasis.orientation.
2. Continuity. The volume form ω := o.volumeForm is an alternating n-linear form on ℝⁿ satisfying Hadamard's inequality |ω(v)| ≤ ∏ᵢ ‖vᵢ‖ (Orientation.abs_volumeForm_apply_le). Hence δ := ω.mkContinuous 1 (AlternatingMap.mkContinuous with constant 1; the bound reads ‖ω(v)‖ = |ω(v)| ≤ 1·∏ᵢ ‖vᵢ‖ by Real.norm_eq_abs) is a continuous alternating map, i.e. δ ∈ Covector (Euclid n) n, and δ = ω as functions (AlternatingMap.coe_mkContinuous). (Automatic continuity of multilinear maps on finite-dimensional spaces is not in the frozen import closure, which is why the explicit bound is used.)
3. Normalization. B is an orthonormal basis whose orientation is o, so ω = det_B, the determinant with respect to the basis B (Orientation.volumeForm_robust B rfl). Since (e₁, …, eₙ) = (B₁, …, Bₙ), δ(e₁, …, eₙ) = det_B(B) = 1 (Module.Basis.det_self). ∎
Formalization note: unless split further this is a machine leaf: exactly one theorem `Submission.dgoj_exists_det_covector` appended to the frozen GMT/Ch07/Submission.lean inside `namespace GMT.Ch07` (before `main_theorem`), no new import, option or helper declaration. Every lemma cited is in the import closure of GMT.Ch07.Submission (pinned Mathlib 25730c7c). The following Lean proof was compiled by the parent decomposition session against that frozen import closure (lean 4.35.0-rc3; `#print axioms` = propext, Classical.choice, Quot.sound; no warnings) and passes the runtime leaf-delta check `check_source_delta`; it may be used verbatim:
theorem Submission.dgoj_exists_det_covector : ∀ n : ℕ, ∃ δ : Covector (Euclid n) n, δ (fun i => EuclideanSpace.single i (1 : ℝ)) = 1 := by
  intro n
  have : Fact (Module.finrank ℝ (Euclid n) = n) := ⟨finrank_euclideanSpace_fin⟩
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let o : Orientation ℝ (Euclid n) (Fin n) := b.toBasis.orientation
  refine ⟨o.volumeForm.mkContinuous 1 fun m => ?_, ?_⟩
  · rw [one_mul, Real.norm_eq_abs]
    exact o.abs_volumeForm_apply_le m
  · rw [AlternatingMap.coe_mkContinuous, o.volumeForm_robust b rfl]
    have h : (fun i => EuclideanSpace.single i (1 : ℝ)) = ⇑b.toBasis := by
      funext i; simp [b]
    rw [h, Module.Basis.det_self]

## Key steps

1. Standard orthonormal basis B = EuclideanSpace.basisFun of ℝⁿ, orientation o, Fact (finrank = n).
2. δ := o.volumeForm.mkContinuous 1, continuous by Hadamard's bound |ω(v)| ≤ ∏‖vᵢ‖.
3. volumeForm_robust: ω = det_B, so δ(e) = det_B(B) = 1.

## Reference use

### local-project

Queries:
- `rg -n 'theorem AlternatingMap.eq_smul_basis_det' mathlib/Mathlib`
- `rg -n 'theorem volumeForm_robust\b|theorem abs_volumeForm_apply_le' mathlib/Mathlib`
- `rg -n 'theorem norm_image_sub_le' mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `rg -n 'theorem le_opNorm|theorem opNorm_le_bound' mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `rg -n 'finrank_range_of_inj' mathlib/Mathlib`
- `rg -n 'theorem det_eq_zero_iff_ker_ne_bot' mathlib/Mathlib`
- `rg -n 'theorem span_apply' mathlib/Mathlib/LinearAlgebra/Basis/Basic.lean`
- `rg -n 'theorem Orthonormal.inner_right_fintype' mathlib/Mathlib`
- `rg -n 'theorem Orthonormal.comp_linearIsometry' mathlib/Mathlib`
- `rg -n 'mem_span_range_iff_exists_fun' mathlib/Mathlib`
- `rg -n 'theorem toMatrix_self|theorem toMatrix_apply' mathlib/Mathlib/LinearAlgebra/Matrix/Basis.lean`
- `rg -n 'theorem det_toMatrix \(b' mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `rg -n 'theorem EuclideanSpace.inner_single_left' mathlib/Mathlib`
- `rg -n 'theorem adjoint_inner_right' mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `rg -n 'theorem ContDiffOn.continuousOn_fderiv_of_isOpen' mathlib/Mathlib`
- `rg -n 'theorem ContinuousLinearMap.continuous_det' mathlib/Mathlib`
- `rg -n 'def apply \(m : ι → E\)' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `rg -n 'theorem posDef_gram_of_linearIndependent|theorem gram_eq_conjTranspose_mul' mathlib/Mathlib`
- `rg -n 'continuous_of_finiteDimensional' mathlib/Mathlib`
- `rg -n 'IsUnitOrientationOf|volumeForm|eq_smul_basis_det|ContinuousAlternatingMap.apply' project/GMT`
- `rg -n 'adjoint ∘L|\.det\)|Real.sqrt' project/GMT --glob '*.lean'`
- `rg -n 'mkContinuous|compContinuousLinearMap' project/GMT --glob '*.lean'`
- `lean #check probes after import GMT.Ch07.Submission: Matrix.gram, Matrix.posDef_gram_of_linearIndependent, Matrix.PosDef.det_pos, MultilinearMap.continuous_of_finiteDimensional, AlternatingMap.toContinuousAlternatingMap, ContinuousAlternatingMap.apply, ContinuousAlternatingMap.norm_image_sub_le, LinearMap.isUnit_iff_isUnit_det, Orientation.volumeForm_robust`
- `grep 'dgoj_' over dag.json, nodes/*/{decomposition-v*,parent-child-handoff}.json and git refs`
- `lean Stmts/Assembly/Full2/Check/Challenge.lean and in-situ OrientationJacobianFull.lean with #print axioms; python leaf_verification.check_source_delta on each child`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Basis/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Basis.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-7b72550114/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/graph_orientation_jacobian_decomposition/OrientationJacobianFull.lean`

The snapshot is project b4d606d with mathlib 25730c7c.

The project has no reusable frame, Gram or evaluation lemma for this node:
- It contains only the Ch07 definitions of MultiVector and IsUnitOrientationOf.
- The Ch02 Jacobian definitions (√det(L*∘L)) belong to another chapter's contract and are not imported.

Pinned Mathlib inside the frozen import closure supplies:
- linear algebra: AlternatingMap.eq_smul_basis_det, Module.Basis.span/span_apply, Module.Basis.det_apply/det_self, LinearMap.det_toMatrix, LinearMap.det_eq_zero_iff_ker_ne_bot, LinearMap.finrank_range_of_inj;
- inner products and orientation: Orthonormal.inner_right_fintype/comp_linearIsometry, stdOrthonormalBasis, Orientation.volumeForm_robust and abs_volumeForm_apply_le, ContinuousLinearMap.adjoint_inner_left/right;
- analysis: ContinuousAlternatingMap.le_opNorm and norm_image_sub_le, ContinuousLinearMap.continuous_det, ContDiffOn.continuousOn_fderiv_of_isOpen.

Unknown after `import GMT.Ch07.Submission`, so outside the closure:
- Matrix.gram and posDef_gram_of_linearIndependent (GramMatrix.lean);
- Matrix.PosDef.det_pos;
- MultilinearMap.continuous_of_finiteDimensional;
- AlternatingMap.toContinuousAlternatingMap.
The children therefore prove the Gram identity by hand, get positivity from the kernel of F*F, and build δ with the Hadamard bound.

Checks:
- All seven child types elaborate in the comparator contract scope.
- Each child was proved as a single theorem that passes check_source_delta.
- The frozen parent type assembles from the children in situ.
- Axioms are only propext, Classical.choice and Quot.sound.
- The prefix dgoj_ is unused, so there are no name collisions.
