# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1.graph_fderiv_left_inverse-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 2 of the parent proof (ι*ι = id, ι*ι' = 0, hence Pr(Φ(v)) = v; F(v) = ι + ι'∘Du(v), ι*∘F(v) = id; v ↦ F(v) continuous on D by ContDiffOn.continuousOn_fderiv_of_isOpen).
Notation: ℝᵐ means Euclid m = EuclideanSpace ℝ (Fin m); ⟨x, y⟩ is inner ℝ x y; e_j := EuclideanSpace.single j (1 : ℝ) is the j-th standard basis vector of ℝⁿ; an n-covector of ℝᴾ is an element of Covector (Euclid P) n = Euclid P [⋀^Fin n]→L[ℝ] ℝ (a continuous alternating n-linear map ℝᴾ × ⋯ × ℝᴾ → ℝ); MultiVector P n = Covector (Euclid P) n →L[ℝ] ℝ (continuous linear functionals on n-covectors); for a continuous linear map F, F* = F.adjoint and det of an endomorphism is ContinuousLinearMap.det (= LinearMap.det of the underlying linear map).
1. Part (i). Fix v ∈ ℝⁿ, w ∈ ℝ^k. For every v' ∈ ℝⁿ: ⟨ι*(ιv + ι'w), v'⟩ = ⟨ιv + ι'w, ιv'⟩ (ContinuousLinearMap.adjoint_inner_left) = ⟨ιv, ιv'⟩ + ⟨ι'w, ιv'⟩ (inner_add_left). Here ⟨ι'w, ιv'⟩ = ⟨ιv', ι'w⟩ = 0 (real_inner_comm and the orthogonality hypothesis) and ⟨ιv, ιv'⟩ = ⟨v, v'⟩ because ι is a linear isometry (LinearIsometry.inner_map_map). So ⟨ι*(ιv + ι'w), v'⟩ = ⟨v, v'⟩ for all v', whence ι*(ιv + ι'w) = v (ext_inner_right).
2. Part (ii). Φ is C¹ on D: the constant z is C¹ (contDiffOn_const), the continuous linear map ι is C¹ (ContinuousLinearMap.contDiff), ι'∘u is C¹ on D as the composition of the C¹ map ι' with u, C¹ on D (ContDiff.comp_contDiffOn), and sums of C¹-on-D maps are C¹ on D (ContDiffOn.add). D is open (isOpen_ball) and 1 ≤ 1, so the derivative of Φ is continuous on D (ContDiffOn.continuousOn_fderiv_of_isOpen).
3. Part (iii). Let v ∈ D and w ∈ ℝⁿ. Since u is C¹ on D it is differentiable on D (ContDiffOn.differentiableOn with 1 ≠ 0), and since D is open it is differentiable at v (DifferentiableOn.differentiableAt, isOpen_ball.mem_nhds). By the rules for adding a constant and for continuous linear maps (ContinuousLinearMap.hasFDerivAt, HasFDerivAt.const_add), the chain rule (HasFDerivAt.comp) and the sum rule (HasFDerivAt.add), Φ has derivative ι + ι'∘Du(v) at v, so DΦ(v) = ι + ι'∘Du(v) (HasFDerivAt.fderiv). Hence DΦ(v)w = ιw + ι'(Du(v)w), and by part (i) ι*(DΦ(v)w) = w. ∎
Formalization note: unless split further this is a machine leaf: exactly one theorem `Submission.dgoj_graph_fderiv_left_inverse` appended to the frozen GMT/Ch07/Submission.lean inside `namespace GMT.Ch07` (before `main_theorem`), no new import, option or helper declaration. Every lemma cited is in the import closure of GMT.Ch07.Submission (pinned Mathlib 25730c7c). The following Lean proof was compiled by the parent decomposition session against that frozen import closure (lean 4.35.0-rc3; `#print axioms` = propext, Classical.choice, Quot.sound; no warnings) and passes the runtime leaf-delta check `check_source_delta`; it may be used verbatim:
theorem Submission.dgoj_graph_fderiv_left_inverse : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → ContDiffOn ℝ 1 u (ball 0 s) → (∀ (v : Euclid n) (w : Euclid k), ι.toContinuousLinearMap.adjoint (ι v + ι' w) = v) ∧ ContinuousOn (fderiv ℝ (fun v => z + ι v + ι' (u v))) (ball (0 : Euclid n) s) ∧ ∀ v ∈ ball (0 : Euclid n) s, ∀ w : Euclid n, ι.toContinuousLinearMap.adjoint (fderiv ℝ (fun v => z + ι v + ι' (u v)) v w) = w := by
  intro n k ι ι' u z s horth hu
  have hadj : ∀ (v : Euclid n) (w : Euclid k), ι.toContinuousLinearMap.adjoint (ι v + ι' w) = v := by
    intro v w
    apply ext_inner_right ℝ
    intro v'
    rw [ContinuousLinearMap.adjoint_inner_left, inner_add_left]
    have h1 : inner ℝ (ι' w) (ι.toContinuousLinearMap v') = 0 := by
      rw [real_inner_comm]; exact horth v' w
    rw [h1, add_zero]
    exact ι.inner_map_map v v'
  refine ⟨hadj, ?_, ?_⟩
  · have hΦ : ContDiffOn ℝ 1 (fun v => z + ι v + ι' (u v)) (ball 0 s) :=
      (contDiffOn_const.add ι.toContinuousLinearMap.contDiff.contDiffOn).add
        (ι'.toContinuousLinearMap.contDiff.comp_contDiffOn hu)
    exact hΦ.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  · intro v hv w
    have hdu : DifferentiableAt ℝ u v :=
      (hu.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hv)
    have hder : HasFDerivAt (fun v => z + ι v + ι' (u v))
        (ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp (fderiv ℝ u v)) v := by
      have h1 : HasFDerivAt (fun v => z + ι v) ι.toContinuousLinearMap v :=
        ι.toContinuousLinearMap.hasFDerivAt.const_add z
      have h2 : HasFDerivAt (fun v => ι' (u v)) (ι'.toContinuousLinearMap.comp (fderiv ℝ u v)) v :=
        ι'.toContinuousLinearMap.hasFDerivAt.comp v hdu.hasFDerivAt
      exact h1.add h2
    rw [hder.fderiv]
    exact hadj w _

## Key steps

1. (i) ⟨ι*(ιv + ι'w), v'⟩ = ⟨ιv, ιv'⟩ + ⟨ι'w, ιv'⟩ = ⟨v, v'⟩ for all v', so ι*(ιv + ι'w) = v.
2. (ii) Φ = z + ι + ι'∘u is C¹ on the open ball, so fderiv Φ is continuous there.
3. (iii) For v in the ball, u is differentiable at v and DΦ(v) = ι + ι'∘Du(v); apply (i) to get ι*(DΦ(v)w) = w.

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
