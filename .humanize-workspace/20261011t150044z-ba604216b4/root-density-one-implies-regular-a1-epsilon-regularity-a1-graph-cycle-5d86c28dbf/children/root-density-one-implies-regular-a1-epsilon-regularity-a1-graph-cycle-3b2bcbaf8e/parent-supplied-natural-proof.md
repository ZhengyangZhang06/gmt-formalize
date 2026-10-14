# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.graph_pullback_extderiv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 0, 4 and the computation in 6(i) of the parent proof (ι*ι = id, ι*ι' = 0, Pr(Φ(v)) = v, ι*(DΦ(v)eᵢ) = eᵢ, and d(P^#ψ) = P^#(dψ)), extracted for an arbitrary smooth form ψ and a point v where u is differentiable.
Notation: ℝ^p means Euclid p = EuclideanSpace ℝ (Fin p); e_l := EuclideanSpace.single l (1 : ℝ) is the l-th standard basis vector; for an (m+1)-tuple w, removeNth i w := Fin.removeNth i w is the m-tuple with entry i deleted, so (removeNth i w)(l) = w(i.succAbove l) (Fin.removeNth_apply); Covector E m = E [⋀^Fin m]→L[ℝ] ℝ (continuous alternating m-linear forms); DifferentialForm E m = E → Covector E m; exteriorDerivative = Mathlib's extDeriv (Poincare.SimonGMT.Chapter06.exteriorDerivative is an abbrev), with the alternating-sum formula dω(x)(w₀,…,w_m) = Σᵢ (−1)^i • D[y ↦ ω(y)(removeNth i w)](x)(wᵢ) for ω differentiable at x (exteriorDerivative_apply); IsSmoothForm ψ := ContDiff ℝ ∞ ψ where ∞ = ((⊤ : ℕ∞) : WithTop ℕ∞) (in the frozen contract scope `∞` denotes ENNReal's ∞ because of `open scoped ENNReal`, so write the order as (⊤ : ℕ∞)).
1. Adjoint identities. For v' ∈ ℝ^{m+1}: L(ιv') = v', because for every y ∈ ℝ^{m+1}, ⟨L(ιv'), y⟩ = ⟨ιv', ιy⟩ (ContinuousLinearMap.adjoint_inner_left) = ⟨v', y⟩ (LinearIsometry.inner_map_map), and vectors with equal inner products against every y are equal (ext_inner_right). For w ∈ ℝ^k: L(ι'w) = 0, because ⟨L(ι'w), y⟩ = ⟨ι'w, ιy⟩ = ⟨ιy, ι'w⟩ (real_inner_comm) = 0 = ⟨0, y⟩ (orthogonality hypothesis, inner_zero_left).
2. Derivative of the graph map. Φ = (constant z) + ι + ι'∘u. Since u is differentiable at v, the chain rule gives HasFDerivAt (ι' ∘ u) (ι' ∘L Du(v)) v (ContinuousLinearMap.hasFDerivAt for ι'.toContinuousLinearMap composed with hu.hasFDerivAt); ι has derivative ι (ContinuousLinearMap.hasFDerivAt), and the constant z has derivative 0 (hasFDerivAt_const). Adding (HasFDerivAt.add) and simplifying 0 + ι = ι gives DΦ(v) = ι + ι' ∘L Du(v) (HasFDerivAt.fderiv). Hence DΦ(v)eᵢ = ιeᵢ + ι'(Du(v)eᵢ) and, by step 1, L(DΦ(v)eᵢ) = eᵢ + 0 = eᵢ for every i.
3. Base point. −Lz + L(Φ(v)) = −Lz + Lz + L(ιv) + L(ι'u(v)) = v + 0 = v, by linearity of L (map_add) and step 1.
4. Since ψ is smooth, d(P^#ψ) = P^#(dψ) (Poincare.SimonGMT.Chapter06.exteriorDerivative_affinePullbackForm with L and b := −Lz). By the definition of affinePullbackForm and ContinuousAlternatingMap.compContinuousLinearMap_apply, the left-hand side equals dψ(−Lz + L(Φ(v)))(i ↦ L(DΦ(v)eᵢ)). By step 3 the base point is v and by step 2 the vectors are eᵢ, so it equals dψ(v)(e₀, …, e_m). (In Lean: `rw [exteriorDerivative_affinePullbackForm _ _ hψ]; simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]; congr 1`, then close the base-point goal by `simp [map_add, hLι, hLι']` and the vector goal by `funext i; simp [hD, hLι, hLι']`.) ∎
Formalization note: this child is a machine leaf (one theorem `Submission.dgcr_bwd_graph_pullback_extDeriv` appended inside `namespace GMT.Ch07` of GMT/Ch07/Submission.lean; no helper declarations, no set_option). The following tactic proof was compiled on the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b36630) in exactly that file context under default maxHeartbeats, passes the workflow's leaf source-delta check, and depends only on propext, Classical.choice, Quot.sound; it may be used verbatim:
theorem Submission.dgcr_bwd_graph_pullback_extDeriv : ∀ (m k : ℕ) (ι : Euclid (m + 1) →ₗᵢ[ℝ] Euclid (m + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + 1 + k)) (u : Euclid (m + 1) → Euclid k) (z : Euclid (m + 1 + k)) (ψ : DifferentialForm (Euclid (m + 1)) m) (v : Euclid (m + 1)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → IsSmoothForm ψ → DifferentiableAt ℝ u v → exteriorDerivative (affinePullbackForm (ContinuousLinearMap.adjoint ι.toContinuousLinearMap) (-(ContinuousLinearMap.adjoint ι.toContinuousLinearMap z)) ψ) (z + ι v + ι' (u v)) (fun i => fderiv ℝ (fun v => z + ι v + ι' (u v)) v (EuclideanSpace.single i (1 : ℝ))) = exteriorDerivative ψ v (fun i => EuclideanSpace.single i (1 : ℝ)) := by
  intro m k ι ι' u z ψ v hperp hψ hu
  have hLι : ∀ v', ContinuousLinearMap.adjoint ι.toContinuousLinearMap (ι v') = v' := by
    intro v'
    apply ext_inner_right ℝ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact ι.inner_map_map v' y
  have hLι' : ∀ w, ContinuousLinearMap.adjoint ι.toContinuousLinearMap (ι' w) = 0 := by
    intro w
    apply ext_inner_right ℝ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm]
    exact hperp y w
  have hD : fderiv ℝ (fun v => z + ι v + ι' (u v)) v =
      ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp (fderiv ℝ u v) := by
    have hι : HasFDerivAt (fun v => ι v) ι.toContinuousLinearMap v :=
      ι.toContinuousLinearMap.hasFDerivAt
    have hι' : HasFDerivAt (fun v => ι' (u v)) (ι'.toContinuousLinearMap.comp (fderiv ℝ u v)) v :=
      ι'.toContinuousLinearMap.hasFDerivAt.comp v hu.hasFDerivAt
    have h1 := ((hasFDerivAt_const z v).add hι).add hι'
    rw [zero_add] at h1
    exact h1.fderiv
  rw [exteriorDerivative_affinePullbackForm _ _ hψ]
  simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  · simp [map_add, hLι, hLι']
  · funext i
    simp [hD, hLι, hLι']

## Key steps

1. Adjoint identities L(ιv') = v' and L(ι'w) = 0 from adjoint_inner_left, inner_map_map and orthogonality.
2. DΦ(v) = ι + ι' ∘L Du(v) by the chain rule, hence L(DΦ(v)eᵢ) = eᵢ.
3. Base point −Lz + LΦ(v) = v.
4. d(P^#ψ) = P^#(dψ) (exteriorDerivative_affinePullbackForm); evaluating at Φ(v) on DΦ(v)e gives dψ(v)(e).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (byte-identical); manifest.json project_commit b4d606d, mathlib_commit 25730c7c; simongmt package at 2b36630`
- `rg -n 'extDeriv_eq|theorem extDeriv_apply|theorem extDeriv_pullback' mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `rg -n 'theorem curryLeft_apply_apply|def curryLeft' mathlib/Mathlib/Analysis/Normed/Module/Alternating/*.lean`
- `rg -n 'cons_removeNth_eq_comp_cycleRange_symm|sign_cycleRange' mathlib/Mathlib`
- `rg -n 'theorem det_self|theorem det_apply' mathlib/Mathlib/LinearAlgebra/Determinant.lean; rg -n 'Continuous.matrix_det|continuous_matrix' mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `rg -n 'map_perm|map_eq_zero_of_eq' mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean; rg -n 'adjoint_inner_left' mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `rg -n 'theorem exists_lt_subset_ball' mathlib/Mathlib; rg -n 'one_of_mem_closedBall|tsupport_eq|hasCompactSupport|contDiff' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `rg -n 'continuous_of_finiteDimensional' mathlib/Mathlib (only LinearMap.continuous_of_finiteDimensional; no MultilinearMap variant)`
- `rg -n 'fderiv_mul_const|DifferentiableAt.smul_const|tsupport_smul_subset_left|image_eq_zero_of_notMem_tsupport|setIntegral_congr_fun' mathlib/Mathlib`
- `rg -n 'exteriorDerivative_apply|exteriorDerivative_affinePullbackForm|affinePullbackForm_isSmoothForm|def affinePullbackForm|tsupport_exteriorDerivative_subset|GeometricCurrentOn.boundary_apply|def exteriorDerivativeTestOn|def IsSmoothForm|abbrev TestFormOn' simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents,AffineCurrentPushforward}.lean`
- `lake env lean /tmp/bwd-split-work/Names.lean and Names2.lean: #check of all cited names after import GMT.Ch07.Submission`
- `python3 lean_contract.validate_lean_statement on the 6 child types; gmt-compare.contract_scope replay; lake env lean /tmp/bwd-split-work/Elab.lean (types elaborate in the comparator scope)`
- `lake env lean /tmp/bwd-split-work/Full.lean: six child proofs as GMT.Ch07.Submission.* theorems, the exact parent type proved from them plus dgcr_orthogonal_coordinates as a hypothesis, comparator-style `exact Submission.X` checks, #print axioms`
- `lake env lean /tmp/bwd-split-work/SimSubmission.lean: frozen Submission.lean with all six children inserted before `end GMT.Ch07`; leaf_verification.check_source_delta simulated for each insertion`
- `grep 'dgcr_bwd_' over dag.json, nodes/*, and all 1159 git refs (git grep): no match`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/GroupTheory/Perm/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-5d86c28dbf/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/bwd-split-work/Elab.lean`
- `/tmp/bwd-split-work/Full.lean`
- `/tmp/bwd-split-work/SimSubmission.lean`

The snapshot is project b4d606d with Mathlib 25730c7c, and its Contract.lean is byte-identical to the workspace Submission.lean. Every cited lemma is in the import closure of GMT.Ch07.Submission.
Mathlib lemmas used: Filter.EventuallyEq.extDeriv_eq, extDeriv_apply, ContinuousAlternatingMap.curryLeft_apply_apply, Fin.cons_removeNth_eq_comp_cycleRange_symm, Fin.sign_cycleRange, Module.Basis.det_apply/det_self, Continuous.matrix_det, continuous_matrix, AlternatingMap.map_perm/map_eq_zero_of_eq, ContinuousLinearMap.adjoint_inner_left, exists_lt_subset_ball, the ContDiffBump API, fderiv_mul_const and setIntegral_congr_fun.
simongmt lemmas used: exteriorDerivative_apply, affinePullbackForm with affinePullbackForm_isSmoothForm and exteriorDerivative_affinePullbackForm, tsupport_exteriorDerivative_subset, exteriorDerivativeTestOn and GeometricCurrentOn.boundary_apply.
MultilinearMap.continuous_of_finiteDimensional has no match, so the determinant covector proves its continuity explicitly.
Lean checks:
- All 6 child types pass validate_lean_statement and elaborate in the comparator contract scope.
- Each child compiles as a single theorem under default heartbeats and passes the leaf source-delta check.
- The exact parent type follows from children coordinate_form, graph_pullback_extderiv and graph_cutoff_lift plus dgcr_orthogonal_coordinates, with axioms only propext, Classical.choice and Quot.sound.
- No dgcr_bwd_ name collision exists in the DAG, node records or git refs.
