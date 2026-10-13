# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.coordinate_covector-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (the constant covector βⱼ(w₁,…,w_m) := δ(eⱼ, w₁, …, w_m)), extracted as a stand-alone lemma.
Notation: ℝ^p means Euclid p = EuclideanSpace ℝ (Fin p); e_l := EuclideanSpace.single l (1 : ℝ) is the l-th standard basis vector; for an (m+1)-tuple w, removeNth i w := Fin.removeNth i w is the m-tuple with entry i deleted, so (removeNth i w)(l) = w(i.succAbove l) (Fin.removeNth_apply); Covector E m = E [⋀^Fin m]→L[ℝ] ℝ (continuous alternating m-linear forms); DifferentialForm E m = E → Covector E m; exteriorDerivative = Mathlib's extDeriv (Poincare.SimonGMT.Chapter06.exteriorDerivative is an abbrev), with the alternating-sum formula dω(x)(w₀,…,w_m) = Σᵢ (−1)^i • D[y ↦ ω(y)(removeNth i w)](x)(wᵢ) for ω differentiable at x (exteriorDerivative_apply); IsSmoothForm ψ := ContDiff ℝ ∞ ψ where ∞ = ((⊤ : ℕ∞) : WithTop ℕ∞) (in the frozen contract scope `∞` denotes ENNReal's ∞ because of `open scoped ENNReal`, so write the order as (⊤ : ℕ∞)).
1. Let b := (EuclideanSpace.basisFun (Fin (m+1)) ℝ).toBasis, the standard basis of ℝ^{m+1}; b l = e_l for every l (OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply; `funext l; simp [b]`). Let δ₀ := b.det, the determinant alternating (m+1)-linear map with respect to b (Module.Basis.det). By Module.Basis.det_apply, δ₀ c = det (b.toMatrix c), and b.toMatrix c is the matrix whose (r, l)-entry is b.repr (c l) r = (c l) r. Hence δ₀ c = det (Matrix.of fun r l => c l r) for every c : Fin (m+1) → ℝ^{m+1} (in Lean, after `rw [Module.Basis.det_apply]` the goal is closed by `congr 1`).
2. Continuity of δ₀. The map c ↦ Matrix.of (fun r l => c l r) is continuous, because each entry c ↦ (c l) r is the composition of the evaluation c ↦ c l (continuous_apply l) with the continuous coordinate projection EuclideanSpace.proj r, and a matrix-valued map with continuous entries is continuous (continuous_matrix). Composing with the determinant (Continuous.matrix_det) shows that c ↦ δ₀ c is continuous by step 1. (The automatic-continuity lemma MultilinearMap.continuous_of_finiteDimensional is not available in the import closure, so this explicit argument is used.)
3. Consequently δ₀ underlies a continuous alternating map δ ∈ Covector (Euclid (m+1)) (m+1) with δ c = δ₀ c for every c (in Lean: `let δ : Covector (Euclid (m + 1)) (m + 1) := { b.det with cont := hcont }`; then `δ c = b.det c` holds by rfl).
4. Define β := δ.curryLeft (b j) ∈ Covector (Euclid (m+1)) m (ContinuousAlternatingMap.curryLeft). By ContinuousAlternatingMap.curryLeft_apply_apply, β w = δ (Matrix.vecCons (b j) w) = δ₀ (Matrix.vecCons (b j) w) for every w : Fin m → ℝ^{m+1}. Since (l ↦ e_l) = b (step 1), the claim for a fixed i reads δ₀ c_i = (if i = j then (−1)^j else 0), where c_i := Matrix.vecCons (b j) (removeNth i b) (Matrix.vecCons = Fin.cons). Split on whether i = j.
5. Case i = j. By Fin.cons_removeNth_eq_comp_cycleRange_symm (with x := b and p := i), c_i = Fin.cons (b i) (removeNth i b) = b ∘ σ with σ := (Fin.cycleRange i).symm. By AlternatingMap.map_perm, δ₀ (b ∘ σ) = sign σ • δ₀ b. Here δ₀ b = b.det b = 1 (Module.Basis.det_self) and sign σ = sign (cycleRange i) (Equiv.Perm.sign_symm) = (−1)^i in ℤˣ (Fin.sign_cycleRange). Hence δ₀ c_i = ((−1)^i : ℤˣ) • (1 : ℝ) = (−1 : ℝ)^i (`simp [Units.smul_def]`), which is (−1)^j because i = j.
6. Case i ≠ j. As j ≠ i, Fin.exists_succAbove_eq gives l ∈ Fin m with i.succAbove l = j. Then c_i 0 = b j and c_i (l.succ) = (removeNth i b) l = b (i.succAbove l) = b j (Fin.removeNth_apply), while 0 ≠ l.succ (Fin.succ_ne_zero). An alternating map vanishes on a family with equal entries at two distinct indices (AlternatingMap.map_eq_zero_of_eq, applied with indices 0 and l.succ; the entry equality is closed by `simp [Fin.removeNth_apply, hl]`), so δ₀ c_i = 0.
7. Steps 5 and 6 give β (removeNth i (l ↦ e_l)) = if i = j then (−1)^j else 0 for every i ∈ Fin (m+1) (`split_ifs`), so β has the required property. (For m = 0 the same argument applies verbatim: β is the 0-covector with value δ₀(e₀) = 1 = (−1)^0.) ∎
Formalization note: this child is a machine leaf (one theorem `Submission.dgcr_bwd_coordinate_covector` appended inside `namespace GMT.Ch07` of GMT/Ch07/Submission.lean; no helper declarations, no set_option). The following tactic proof was compiled on the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b36630) in exactly that file context under default maxHeartbeats, passes the workflow's leaf source-delta check, and depends only on propext, Classical.choice, Quot.sound; it may be used verbatim:
theorem Submission.dgcr_bwd_coordinate_covector : ∀ (m : ℕ) (j : Fin (m + 1)), ∃ β : Covector (Euclid (m + 1)) m, ∀ i : Fin (m + 1), β (i.removeNth (fun l : Fin (m + 1) => EuclideanSpace.single l (1 : ℝ))) = if i = j then (-1 : ℝ) ^ (j : ℕ) else 0 := by
  intro m j
  classical
  let b : Module.Basis (Fin (m + 1)) ℝ (Euclid (m + 1)) :=
    (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis
  have hb : (b : Fin (m + 1) → Euclid (m + 1)) = fun l => EuclideanSpace.single l (1 : ℝ) := by
    funext l; simp [b]
  have hdet : ∀ c : Fin (m + 1) → Euclid (m + 1), b.det c = (Matrix.of fun r l => c l r).det := by
    intro c
    rw [Module.Basis.det_apply]
    congr 1
  have hcont : Continuous (fun c : Fin (m + 1) → Euclid (m + 1) => b.det c) := by
    simp only [hdet]
    apply Continuous.matrix_det
    refine continuous_matrix fun r l => ?_
    exact (EuclideanSpace.proj r).continuous.comp (continuous_apply l)
  let δ : Covector (Euclid (m + 1)) (m + 1) := { b.det with cont := hcont }
  have hδ : ∀ c, δ c = b.det c := fun c => rfl
  refine ⟨δ.curryLeft (b j), fun i => ?_⟩
  rw [ContinuousAlternatingMap.curryLeft_apply_apply, hδ, ← hb]
  split_ifs with hij
  · subst hij
    have hc : (Matrix.vecCons (b i) (i.removeNth ⇑b) : Fin (m + 1) → Euclid (m + 1)) =
        ⇑b ∘ ⇑(Equiv.symm i.cycleRange) :=
      Fin.cons_removeNth_eq_comp_cycleRange_symm (⇑b) i
    rw [hc, AlternatingMap.map_perm, Module.Basis.det_self, Equiv.Perm.sign_symm, Fin.sign_cycleRange]
    simp [Units.smul_def]
  · obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq (x := j) (y := i) (Ne.symm hij)
    apply AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := l.succ)
    · simp [Fin.removeNth_apply, hl]
    · exact (Fin.succ_ne_zero l).symm

## Key steps

1. Standard basis b of ℝ^{m+1} with b l = e_l; δ₀ := b.det satisfies δ₀ c = det (Matrix.of fun r l => c l r).
2. δ₀ is continuous (continuous_matrix + Continuous.matrix_det), so it upgrades to δ ∈ Covector (Euclid (m+1)) (m+1) via { b.det with cont := _ }.
3. β := δ.curryLeft (b j), so β w = δ (vecCons (b j) w).
4. i = j: vecCons (b j) (removeNth j b) = b ∘ (cycleRange j)⁻¹; map_perm, sign (cycleRange j) = (−1)^j and det_self give (−1)^j.
5. i ≠ j: e_j occurs at positions 0 and l.succ (i.succAbove l = j), so the alternating form vanishes.

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
