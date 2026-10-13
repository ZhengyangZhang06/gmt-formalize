# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.directional-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.directional-a1.wedge_riesz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 2 of the parent proof (the wedge w^♭∧α := exteriorDerivative (y ↦ ⟨w, y⟩•α) 0 and the Riesz vector v_α of w ↦ ζ₀(w^♭∧α)), with the uniqueness of w^♭∧α and its linearity in w written out. Uses the sibling extderiv_smul (accepted dgcr_bwd_extDeriv_smul_const): for a : ℝ^P → ℝ differentiable at x and a constant m-covector β, exteriorDerivative (y ↦ a(y)•β) x u = Σ_{i=0}^{m} (−1)^i·(Da(x)(u_i)·β(removeNth i u)) for all u : Fin (m+1) → ℝ^P.
Notation: ℝ^P = Euclid P = EuclideanSpace ℝ (Fin P) with real inner product ⟨·,·⟩; a d-covector is an element of Covector (Euclid P) d (a continuous alternating d-linear form); ζ₀ ∈ MultiVector P (d+1) is a continuous linear functional on (d+1)-covectors; removeNth i u := Fin.removeNth i u; for w ∈ ℝ^P and u : Fin (d+1) → ℝ^P put F_w(u) := Σ_{i=0}^{d} (−1)^i·(⟨w, u_i⟩·α(removeNth i u)).
1. (The covector W(w) = w^♭∧α.) Fix w ∈ ℝ^P. The function a_w(y) := ⟨w, y⟩ is the continuous linear map innerSL ℝ w, so it is differentiable at 0 and its derivative there is innerSL ℝ w itself (ContinuousLinearMap.differentiableAt, ContinuousLinearMap.fderiv), i.e. Da_w(0)(h) = ⟨w, h⟩ (innerSL_apply_apply). Define the (d+1)-covector W(w) := exteriorDerivative (y ↦ ⟨w, y⟩•α) 0. By extderiv_smul with m = d, a = a_w, β = α, x = 0, for every u: W(w)(u) = Σ_i (−1)^i·(Da_w(0)(u_i)·α(removeNth i u)) = F_w(u).
2. (Uniqueness.) Let γ be a (d+1)-covector with γ(u) = F_w(u) for all u. Then γ(u) = W(w)(u) for every u by step 1, so γ = W(w), because continuous alternating maps with the same values are equal (ContinuousAlternatingMap.ext).
3. (W is linear in w.) Let w, w' ∈ ℝ^P and c ∈ ℝ. For every u, by step 1 and ⟨w + w', u_i⟩ = ⟨w, u_i⟩ + ⟨w', u_i⟩ (inner_add_left), W(w + w')(u) = Σ_i (−1)^i·((⟨w, u_i⟩ + ⟨w', u_i⟩)·α(removeNth i u)) = F_w(u) + F_{w'}(u) = (W(w) + W(w'))(u) (distribute each term and split the sum, Finset.sum_add_distrib); hence W(w + w') = W(w) + W(w') (ext). Likewise, by ⟨c•w, u_i⟩ = c·⟨w, u_i⟩ (real_inner_smul_left) and pulling the constant c out of the sum (Finset.mul_sum), W(c•w)(u) = c·F_w(u) = (c•W(w))(u); hence W(c•w) = c•W(w).
4. (The functional ℓ.) Define ℓ(w) := ζ₀(W(w)). Since ζ₀ is linear, step 3 gives ℓ(w + w') = ζ₀(W(w) + W(w')) = ℓ(w) + ℓ(w') and ℓ(c•w) = ζ₀(c•W(w)) = c·ℓ(w). So ℓ is a linear functional on the finite-dimensional space ℝ^P, hence a continuous linear functional (LinearMap.toContinuousLinearMap).
5. (Riesz representative.) Let v := (InnerProductSpace.toDual ℝ ℝ^P).symm ℓ, the Riesz representative of the continuous linear functional ℓ. Then ⟨v, w⟩ = ℓ(w) for every w ∈ ℝ^P (InnerProductSpace.toDual_symm_apply).
6. (Conclusion.) The vector v depends only on ζ₀ and α. Let w ∈ ℝ^P and let γ be a (d+1)-covector with γ(u) = Σ_i (−1)^i·(⟨w, u_i⟩·α(removeNth i u)) = F_w(u) for all u. By step 2, γ = W(w); hence ζ₀(γ) = ζ₀(W(w)) = ℓ(w) = ⟨v, w⟩ by step 5. This is the claim. ∎
Formalization note: this child is a machine leaf (one theorem `Submission.cbr_ci_cp_dir_wedge_riesz_vector` inserted inside `namespace GMT.Ch07` of GMT/Ch07/Submission.lean before main_theorem; no helper declarations, no set_option). The following tactic proof was compiled on the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b36630) in exactly that file context (on top of the accepted Submission.dgcr_bwd_extDeriv_smul_const, candidate 9dcae6bd) under default maxHeartbeats, passes the workflow's leaf source-delta check, and depends only on propext, Classical.choice, Quot.sound; it may be used verbatim:
theorem Submission.cbr_ci_cp_dir_wedge_riesz_vector : ∀ (P d : ℕ) (ζ₀ : MultiVector P (d + 1)) (α : Covector (Euclid P) d), ∃ v : Euclid P, ∀ (w : Euclid P) (γ : Covector (Euclid P) (d + 1)), (∀ u : Fin (d + 1) → Euclid P, γ u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ w (u i) * α (i.removeNth u))) → ζ₀ γ = inner ℝ v w := by
  intro P d ζ₀ α
  set W : Euclid P → Covector (Euclid P) (d + 1) :=
    fun w => exteriorDerivative (fun y => inner ℝ w y • α) 0 with hW
  have hWf : ∀ (w : Euclid P) (u : Fin (d + 1) → Euclid P), W w u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ w (u i) * α (i.removeNth u)) := by
    intro w u
    have hd : DifferentiableAt ℝ (fun y => inner ℝ w y) (0 : Euclid P) :=
      (innerSL ℝ w).differentiableAt
    rw [hW, Submission.dgcr_bwd_extDeriv_smul_const P d (fun y => inner ℝ w y) α 0 u hd]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hf : fderiv ℝ (fun y => inner ℝ w y) (0 : Euclid P) = innerSL ℝ w :=
      (innerSL ℝ w).fderiv
    rw [hf, innerSL_apply_apply]
  have huniq : ∀ (w : Euclid P) (γ : Covector (Euclid P) (d + 1)), (∀ u : Fin (d + 1) → Euclid P, γ u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ w (u i) * α (i.removeNth u))) → γ = W w := by
    intro w γ hγ
    ext u
    rw [hγ u, hWf w u]
  have hadd : ∀ w w' : Euclid P, W (w + w') = W w + W w' := by
    intro w w'
    ext u
    rw [ContinuousAlternatingMap.add_apply, hWf, hWf, hWf, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [inner_add_left]
    ring
  have hsmul : ∀ (c : ℝ) (w : Euclid P), W (c • w) = c • W w := by
    intro c w
    ext u
    rw [ContinuousAlternatingMap.smul_apply, hWf, hWf, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [real_inner_smul_left]
    ring
  let ℓ : Euclid P →ₗ[ℝ] ℝ :=
    { toFun := fun w => ζ₀ (W w)
      map_add' := by
        intro w w'
        simp only [hadd, map_add]
      map_smul' := by
        intro c w
        simp only [hsmul, map_smul, smul_eq_mul, RingHom.id_apply] }
  refine ⟨(InnerProductSpace.toDual ℝ (Euclid P)).symm (LinearMap.toContinuousLinearMap ℓ), ?_⟩
  intro w γ hγ
  rw [InnerProductSpace.toDual_symm_apply, huniq w γ hγ]
  rfl

## Key steps

1. W(w) := exteriorDerivative (y ↦ ⟨w, y⟩•α) 0 satisfies W(w)(u) = Σ_i (−1)^i⟨w, u_i⟩α(removeNth i u) (extderiv_smul with Da_w(0) = innerSL ℝ w), and every γ with this formula equals W(w) (ext).
2. W is additive and homogeneous in w (inner_add_left, real_inner_smul_left, ext), so ℓ(w) := ζ₀(W(w)) is a linear, hence continuous, functional on ℝ^P.
3. v := (InnerProductSpace.toDual ℝ ℝ^P).symm ℓ satisfies ⟨v, w⟩ = ℓ(w), so ζ₀(γ) = ζ₀(W(w)) = ℓ(w) = ⟨v, w⟩.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp same GMT/Ch07/Submission.lean (identical)`
- `rg -n "cbr_ci_cp_dir" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project (no match); python3 -I scan of dag.json (1549 nodes): names cbr_ci_cp_dir_wedge_riesz_vector, cbr_ci_cp_dir_integral_fderiv_span, cbr_ci_cp_dir_cycle_fderiv_integral_zero unused; lean_statement substrings 'removeNth u))) → ζ₀ γ = inner', '∂ν = 0) → ∀ v ∈ Submodule.span', 'inner ℝ v w', 'Submodule.span ℝ S' (no match)`
- `python3 -I scan of dag.json for lean_name dgcr_bwd_extDeriv_smul_const (status accepted, candidate_commit 9dcae6bdd56dfe358491f8344e7a8610f929bf88, lean_statement byte-identical); git show 9dcae6bdd56dfe358491f8344e7a8610f929bf88 -- GMT/Ch07/Submission.lean (one theorem inserted before main_theorem)`
- `grep -rln "alternatizeUncurryFin" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib; sed -n 80,170p Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean (alternatizeUncurryFinCLM exists; the children instead follow the supplied proof via extderiv_smul)`
- `rg -n "theorem toDual_symm_apply|theorem inner_right_of_mem_orthogonal|theorem Continuous.integrable_of_hasCompactSupport|theorem HasCompactSupport.fderiv_apply|theorem span_induction|class IsFiniteMeasureOnCompacts|theorem integral_const_mul |theorem integral_congr_ae|theorem real_inner_smul_left|theorem inner_add_left|theorem innerSL_apply_apply|theorem real_inner_comm|def toContinuousLinearMap|theorem Continuous.clm_apply|theorem HasCompactSupport.smul_right|theorem fderiv_mul_const" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib (all found)`
- `sed -n 20,145p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean; sed -n 100,130p .../Chapter06/Currents.lean (Covector, DifferentialForm, exteriorDerivative = extDeriv, exteriorDerivative_apply, testFormOnSubmodule / TestFormOn)`
- `lake env lean /tmp/wedge-decomp/Elab.lean (the three new child types elaborate after import GMT.Ch07.Submission in the contract namespace/opens)`
- `lake env lean /tmp/wedge-decomp/lean/Final.lean (Submission.* children with exact types, the parent from them, and hypothesis-only wedge_assembly_exact: three new child types verbatim ⊢ frozen parent type; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/wedge-decomp/lean/FullSubmission2.lean (Submission.lean at 9dcae6bd + the three child proofs extracted verbatim from the natural_proof notes + parent assembly before main_theorem: only main_theorem's frozen sorry warning; axioms propext, Classical.choice, Quot.sound)`
- `python3 -I /tmp/wedge-decomp/build/check.py (verifier/lean_contract.py validate_lean_statement on all five strings; key/lean_name regexes; replica of leaf_verification.check_source_delta for each child inserted before main_theorem: pass)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose: max_depth 6, so children of this depth-5 node are leaves; _existing_lean_name_problem/_accepted_checkpoint: an accepted node is reusable under an identical type; _reference_use_problem) and leaf_verification.py (check_source_delta forbidden tokens)`
- `independent reviewer agent: re-compiled Final.lean, FullSubmission2.lean and per-child files /tmp/wedge-review/IsoSpan.lean (bare frozen base), IsoRiesz.lean and IsoPair.lean (base 9dcae6bd): all pass; string-identity and digest checks pass`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Span/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-eb599607aa/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-eb599607aa/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6c861e5511/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-18aa777bf2/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-18aa777bf2/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/parent_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/wedge-decomp/lean/Final.lean`
- `/tmp/wedge-decomp/lean/FullSubmission2.lean`

The snapshot contract (project b4d606db, Mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean. No snapshot declaration or DAG node already states the Riesz-vector, span-vanishing or cycle-pairing lemma, and the three new names cbr_ci_cp_dir_* are fresh; the only reuse is the accepted dgcr_bwd_extDeriv_smul_const with its byte-identical type. Every Mathlib lemma cited in the child proofs exists in the snapshot and is reachable from import GMT.Ch07.Submission: InnerProductSpace.toDual_symm_apply, Submodule.inner_right_of_mem_orthogonal, Continuous.integrable_of_hasCompactSupport, HasCompactSupport.fderiv_apply, Submodule.span_induction, IsFiniteMeasureOnCompacts, integral_const_mul, integral_congr_ae, real_inner_smul_left, inner_add_left, innerSL_apply_apply, real_inner_comm, LinearMap.toContinuousLinearMap, Continuous.clm_apply, HasCompactSupport.smul_right and fderiv_mul_const. The compiled checks listed in the queries confirm that the three child types imply the frozen parent type, and that each child has a compiling leaf proof using only propext, Classical.choice and Quot.sound.
