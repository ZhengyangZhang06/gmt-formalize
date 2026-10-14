# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1.continuous_covector_eval-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (definition of ev(c) ∈ MultiVector (n+k) n by ev(c)(α) := α(c) and its continuity via ContinuousAlternatingMap.norm_image_sub_le and ContinuousLinearMap.opNorm_le_bound), stated for arbitrary P and n.
Notation: ℝᵐ means Euclid m = EuclideanSpace ℝ (Fin m); ⟨x, y⟩ is inner ℝ x y; e_j := EuclideanSpace.single j (1 : ℝ) is the j-th standard basis vector of ℝⁿ; an n-covector of ℝᴾ is an element of Covector (Euclid P) n = Euclid P [⋀^Fin n]→L[ℝ] ℝ (a continuous alternating n-linear map ℝᴾ × ⋯ × ℝᴾ → ℝ); MultiVector P n = Covector (Euclid P) n →L[ℝ] ℝ (continuous linear functionals on n-covectors); for a continuous linear map F, F* = F.adjoint and det of an endomorphism is ContinuousLinearMap.det (= LinearMap.det of the underlying linear map). On Fin n → ℝᴾ the norm is the sup norm ‖c‖ = maxᵢ ‖cᵢ‖.
1. Definition. Fix c. The map α ↦ α(c) is linear in α (addition and scalar multiplication of covectors are pointwise, so both linearity identities hold by definition), and |α(c)| ≤ ‖α‖·∏ᵢ ‖cᵢ‖ (ContinuousAlternatingMap.le_opNorm). Hence it is a bounded linear functional; let ev(c) ∈ MultiVector P n be LinearMap.mkContinuous of it with bound constant ∏ᵢ ‖cᵢ‖. By construction ev(c)(α) = α(c) (definitional).
2. Estimate. For c, c' and every α, ContinuousAlternatingMap.norm_image_sub_le gives |α(c) − α(c')| ≤ ‖α‖·card(Fin n)·max(‖c‖, ‖c'‖)^{card(Fin n) − 1}·‖c − c'‖ with card(Fin n) = n (Fintype.card_fin). Since (ev(c) − ev(c'))(α) = α(c) − α(c'), the operator-norm bound (ContinuousLinearMap.opNorm_le_bound, the constant n·max(‖c‖, ‖c'‖)^{n−1}·‖c − c'‖ being ≥ 0) gives ‖ev(c) − ev(c')‖ ≤ n·max(‖c‖, ‖c'‖)^{n−1}·‖c − c'‖.
3. Continuity at an arbitrary c₀. The real function g(c) := n·max(‖c‖, ‖c₀‖)^{n−1}·‖c − c₀‖ is continuous in c and g(c₀) = 0, so g(c) → 0 as c → c₀. By step 2 (with c' = c₀), 0 ≤ ‖ev(c) − ev(c₀)‖ ≤ g(c); by squeezing (squeeze_zero) ‖ev(c) − ev(c₀)‖ → 0, i.e. ev(c) → ev(c₀) (tendsto_iff_norm_sub_tendsto_zero). Since c₀ was arbitrary, ev is continuous (continuous_iff_continuousAt). ∎
Lean caveat (verified): MultiVector P n carries the operator-norm instances, so give the generic lemmas their arguments explicitly — `norm_nonneg (ev c - ev c₀)` and `tendsto_iff_norm_sub_tendsto_zero (E := MultiVector P n) (f := ev) (b := ev c₀)` — otherwise unification between ContinuousLinearMap.hasOpNorm and SeminormedAddGroup.toNorm stalls on metavariables.
Formalization note: unless split further this is a machine leaf: exactly one theorem `Submission.dgoj_exists_continuous_covector_eval` appended to the frozen GMT/Ch07/Submission.lean inside `namespace GMT.Ch07` (before `main_theorem`), no new import, option or helper declaration. Every lemma cited is in the import closure of GMT.Ch07.Submission (pinned Mathlib 25730c7c). The following Lean proof was compiled by the parent decomposition session against that frozen import closure (lean 4.35.0-rc3; `#print axioms` = propext, Classical.choice, Quot.sound; no warnings) and passes the runtime leaf-delta check `check_source_delta`; it may be used verbatim:
theorem Submission.dgoj_exists_continuous_covector_eval : ∀ (P n : ℕ), ∃ ev : (Fin n → Euclid P) → MultiVector P n, Continuous ev ∧ ∀ (c : Fin n → Euclid P) (α : Covector (Euclid P) n), ev c α = α c := by
  intro P n
  let ev : (Fin n → Euclid P) → MultiVector P n := fun c =>
    LinearMap.mkContinuous
      { toFun := fun α => α c
        map_add' := fun α β => rfl
        map_smul' := fun r α => rfl }
      (∏ i, ‖c i‖) fun α => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        calc ‖α c‖ ≤ ‖α‖ * ∏ i, ‖c i‖ := α.le_opNorm c
          _ = (∏ i, ‖c i‖) * ‖α‖ := mul_comm _ _
  have hev : ∀ (c : Fin n → Euclid P) (α : Covector (Euclid P) n), ev c α = α c := fun c α => rfl
  refine ⟨ev, ?_, hev⟩
  have key : ∀ c c' : Fin n → Euclid P,
      ‖ev c - ev c'‖ ≤ (n : ℝ) * max ‖c‖ ‖c'‖ ^ (n - 1) * ‖c - c'‖ := by
    intro c c'
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun α => ?_
    rw [sub_apply, hev, hev]
    have h := α.norm_image_sub_le c c'
    rw [Fintype.card_fin] at h
    calc ‖α c - α c'‖ ≤ ‖α‖ * n * max ‖c‖ ‖c'‖ ^ (n - 1) * ‖c - c'‖ := h
      _ = (n : ℝ) * max ‖c‖ ‖c'‖ ^ (n - 1) * ‖c - c'‖ * ‖α‖ := by ring
  rw [continuous_iff_continuousAt]
  intro c₀
  have hcont : Continuous fun c : Fin n → Euclid P => (n : ℝ) * max ‖c‖ ‖c₀‖ ^ (n - 1) * ‖c - c₀‖ := by
    fun_prop
  have h0 := hcont.tendsto c₀
  simp only [sub_self, norm_zero, mul_zero] at h0
  have h1 : Tendsto (fun c => ‖ev c - ev c₀‖) (𝓝 c₀) (𝓝 0) :=
    squeeze_zero (fun c => norm_nonneg (ev c - ev c₀)) (fun c => key c c₀) h0
  exact (tendsto_iff_norm_sub_tendsto_zero (E := MultiVector P n) (f := ev) (b := ev c₀)).2 h1

## Key steps

1. ev(c) := the bounded linear functional α ↦ α(c) (bound ∏‖cᵢ‖ from ContinuousAlternatingMap.le_opNorm); ev(c)(α) = α(c).
2. norm_image_sub_le + opNorm_le_bound: ‖ev(c) − ev(c')‖ ≤ n·max(‖c‖,‖c'‖)^{n−1}·‖c − c'‖.
3. The right side with c' = c₀ is continuous in c and vanishes at c₀; squeeze gives ev(c) → ev(c₀), so ev is continuous.

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
