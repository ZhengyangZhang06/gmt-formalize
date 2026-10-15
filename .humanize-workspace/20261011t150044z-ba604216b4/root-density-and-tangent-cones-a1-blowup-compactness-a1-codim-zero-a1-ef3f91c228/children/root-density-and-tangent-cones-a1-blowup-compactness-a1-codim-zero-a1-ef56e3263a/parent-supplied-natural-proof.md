# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.top_constancy-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.top_constancy-a1.weak_derivs-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3–5 of the selected node's supplied proof, plus the comparison of the integral over B with the integral over ℝⁿ from its step 6.
- Steps 3–5: β_i := a·γ_i is a test form supported in B, and 0 = ∂X(β_i) = X(dβ_i) = ±∫ g ∂_i a.
- Step 6 part: the integral over B equals the integral over ℝⁿ because the integrand vanishes outside tsupport a ⊆ B.
Sibling used: coordinate_form = Submission.dgcr_bwd_coordinate_form (CF). It packages the supplied steps 2 and 4 with the sign (−1)^j absorbed. Here G is an arbitrary real function. The selected node applies this lemma with G(y) = (g(y) : ℝ), the integer density of top_density, and then feeds the conclusion verbatim into dgcr_smooth_tests_to_C1_tests.

Notation.
- ℝ^{m+1} = Euclid (m+1).
- e_l := EuclideanSpace.single l (1 : ℝ). Since EuclideanSpace.basisFun (Fin (m+1)) ℝ l = e_l for every l (EuclideanSpace.basisFun_apply), the tuples ⇑(EuclideanSpace.basisFun (Fin (m+1)) ℝ) and (l ↦ e_l) are equal (funext).
- An element of TestFormOn V k is a k-form ω with IsTestForm ω ∧ tsupport ω ⊆ V (Poincare.SimonGMT.Chapter06.testFormOnSubmodule). Here IsTestForm ω = IsSmoothForm ω ∧ HasCompactSupport ω.

1. Fix a C^∞ function a with compact support and tsupport a ⊆ B, and fix j ∈ Fin (m+1). Apply CF to m, a, j and ContDiff ℝ (⊤ : ℕ∞) a. This gives an m-form ψ on ℝ^{m+1} with IsSmoothForm ψ, tsupport ψ ⊆ tsupport a, and dψ(x)(l ↦ e_l) = Da(x)(e_j) for every x (d = exteriorDerivative).
2. ψ is a test form in V supported in B.
- tsupport ψ is closed (isClosed_tsupport) and contained in the compact set tsupport a (HasCompactSupport a). So it is compact (IsCompact.of_isClosed_subset), i.e. HasCompactSupport ψ.
- Moreover tsupport ψ ⊆ tsupport a ⊆ B ⊆ V.
- Thus ψ ∈ TestFormOn V m. Call this element β. Its underlying form is ψ, so tsupport β = tsupport ψ ⊆ B.
3. Boundary and representation.
- By hypothesis (i), X.boundary β = 0.
- By GeometricCurrentOn.boundary_apply, X.boundary β = X(exteriorDerivativeTestOn V m β). By the definition of exteriorDerivativeTestOn, the underlying form of this test form is exteriorDerivative ψ = dψ.
- Apply hypothesis (ii) to this (m+1)-test form: 0 = X(exteriorDerivativeTestOn V m β) = ∫ G(y)·dψ(y)(⇑basisFun) dy.
4. For every y, ⇑(EuclideanSpace.basisFun (Fin (m+1)) ℝ) = (l ↦ e_l) by basisFun_apply. So by step 1, G(y)·dψ(y)(⇑basisFun) = G(y)·Da(y)(e_j). The two integrands are equal as functions, so ∫ G(y)·Da(y)(e_j) dy = 0. No integrability is needed to rewrite an integral along an equality of integrands.
5. Let v ∉ B. Then v ∉ tsupport a, because tsupport a ⊆ B. So Da(v) = 0 (fderiv_of_notMem_tsupport) and G(v)·Da(v)(e_j) = 0. A function vanishing outside B has the same integral over B as over ℝ^{m+1} (setIntegral_eq_integral_of_forall_compl_eq_zero, which needs neither measurability of B nor integrability). Hence ∫_B G(v)·Da(v)(e_j) dv = ∫ G(v)·Da(v)(e_j) dv = 0 by step 4. Since a and j were arbitrary, the claim holds. ∎

Formalization note (not part of the proof).
- This child is a machine leaf: one theorem Submission.dtc_bc_cz_tc_weak_derivs appended inside namespace GMT.Ch07 of GMT/Ch07/Submission.lean. It needs no helper declaration, no import and no set_option; the frozen import closure suffices.
- The proof below was compiled on the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b36630) on top of the accepted CF candidate bb4ef845.
- It depends only on propext, Classical.choice and Quot.sound, and it passes the runtime's leaf source-delta check. It may be used verbatim:
theorem Submission.dtc_bc_cz_tc_weak_derivs : ∀ (m : ℕ) (V B : Set (Euclid (m + 1))) (X : GeometricCurrentOn V (m + 1)) (G : Euclid (m + 1) → ℝ), B ⊆ V → (∀ β : TestFormOn V m, tsupport (β : DifferentialForm (Euclid (m + 1)) m) ⊆ B → X.boundary β = 0) → (∀ ω : TestFormOn V (m + 1), X ω = ∫ y, G y * (ω : DifferentialForm (Euclid (m + 1)) (m + 1)) y ⇑(EuclideanSpace.basisFun (Fin (m + 1)) ℝ)) → ∀ a : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a → tsupport a ⊆ B → ∀ j : Fin (m + 1), ∫ v in B, G v * fderiv ℝ a v (EuclideanSpace.single j (1 : ℝ)) = 0 := by
  intro m V B X G hBV hbdry hrep a ha hacpt haB j
  obtain ⟨ψ, hψs, hψsupp, hψd⟩ := Submission.dgcr_bwd_coordinate_form m a j ha
  have hψc : HasCompactSupport ψ :=
    IsCompact.of_isClosed_subset hacpt (isClosed_tsupport ψ) hψsupp
  let β : TestFormOn V m := ⟨ψ, ⟨⟨hψs, hψc⟩, hψsupp.trans (haB.trans hBV)⟩⟩
  have h0 : X.boundary β = 0 := hbdry β (hψsupp.trans haB)
  rw [GeometricCurrentOn.boundary_apply, hrep] at h0
  have hbasis : ⇑(EuclideanSpace.basisFun (Fin (m + 1)) ℝ) =
      fun i => EuclideanSpace.single i (1 : ℝ) := by
    funext i
    simp
  have h1 : ∫ y, G y * fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ)) = 0 := by
    rw [← h0]
    congr 1
    funext y
    change G y * fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ)) =
      G y * exteriorDerivative ψ y ⇑(EuclideanSpace.basisFun (Fin (m + 1)) ℝ)
    rw [hbasis, hψd y]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact h1
  · intro v hv
    have hva : v ∉ tsupport a := fun h => hv (haB h)
    simp [fderiv_of_notMem_tsupport ℝ hva]

## Key steps

1. CF gives a smooth m-form ψ with tsupport ψ ⊆ tsupport a and dψ(x)(e) = ∂_j a(x) for all x.
2. tsupport ψ is a closed subset of the compact set tsupport a ⊆ B ⊆ V, so ψ is a TestFormOn V m supported in B.
3. 0 = X.boundary ψ = X(dψ) = ∫ G·dψ(e) = ∫ G·∂_j a, by boundary_apply, the density representation and basisFun_apply.
4. The integrand vanishes off tsupport a ⊆ B (fderiv_of_notMem_tsupport), so ∫_B G·∂_j a = ∫ G·∂_j a = 0.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp workspace GMT/Ch07/Submission.lean against git show HEAD and dispatch base 72492511 (identical)`
- `python3 -I over dag.json: selected node record (depth 4, status decomposing, children [], depends_on top_density-a1 and smooth_to_c1_tests-a1); keyword scan of accepted titles/lean_statements for removeNth|curryLeft|exteriorDerivative|extDeriv|ae_eq_const|IsPreconnected|onstancy; exact-name/type match of dgcr_bwd_coordinate_form, dgcr_smooth_tests_to_C1_tests, dtc_bc_cz_top_density, dtc_bc_cz_top_constancy`
- `git show {72492511,bb4ef845,c1d60848,dcc3f4b7,9dcae6bd}:GMT/Ch07/Submission.lean | grep theorem/import; import scan of 1037 accepted candidate commits for Chapter08.DistributionalConstancy`
- `grep/sed /runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/runtime.py (_solve_children, _existing_lean_name_problem, _install_parent_supplied_child_handoff, _overlay_accepted_children, _accepted_checkpoint, _machine_leaf, _leaf_author_task, _machine_git_check), store.py ensure, leaf_verification.py check_source_delta/check_git_delta, parent_verification.py check_parent_git_delta`
- `sed simongmt Chapter06/Forms.lean (IsSmoothForm, IsTestForm, exteriorDerivative_apply), Chapter06/Currents.lean (testFormOnSubmodule, TestFormOn, exteriorDerivativeTestOn, GeometricCurrentOn.boundary_apply), Chapter08/DistributionalConstancy.lean (ae_eq_const_of_weak_coordinate_derivatives_zero)`
- `rg -n 'theorem map_insertNth|theorem curryLeft_apply_apply|insertNth_self_removeNth|exists_succAbove_eq|removeNth_apply|map_eq_zero_of_eq|cons_removeNth_eq_comp_cycleRange_symm|sign_cycleRange|setIntegral_eq_integral_of_forall_compl_eq_zero|exists_mem_of_measure_ne_zero_of_ae|theorem integral_const_mul|fderiv_of_notMem_tsupport|fderiv_mul_const|IsOpen.measure_pos|ae_restrict_iff|basisFun_apply|tsupport_smul_subset_left|IsCompact.of_isClosed_subset' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -l 'dtc_bc_cz_tc_' over simongmt/Poincare, the local-references snapshot, workspace GMT, dag.json, issue-workers.json, DAG.md, nodes/, decomposition-reopenings/, operator-dependency-edits/ (no match, exit 1); git show <each codim-zero ref>:GMT/Ch07/Submission.lean | grep 'dtc_bc_cz_tc_|dtc_bc_cz_top_constancy' (no match)`
- `python3 -I gen_challenges.py (gmt-compare.py child_modules contract mode + lean_contract.validate_lean_statement); lake env lean on Challenge_{coordinate_form,weak_derivs,parent,top_density,smooth_to_c1_tests,int_const}.lean, Closure.lean, Assembly.lean, sim/leaf_cand.lean, sim/leaf_cmp.lean, sim/parent_sim.lean with #print axioms; check_source_delta(leaf_base, leaf_cand, dtc_bc_cz_tc_weak_derivs)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1-ef3f91c228/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1-ef3f91c228/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1-ef3f91c228/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-d443cc9f96/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1/decomposition-v2.json`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/parent_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/SuccPred.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/tmp/tc-decomp/check/Challenge_weak_derivs.lean`
- `/tmp/tc-decomp/check/Challenge_coordinate_form.lean`
- `/tmp/tc-decomp/check/Challenge_parent.lean`
- `/tmp/tc-decomp/check/Closure.lean`
- `/tmp/tc-decomp/check/Assembly.lean`
- `/tmp/tc-decomp/sim/leaf_cand.lean`
- `/tmp/tc-decomp/sim/leaf_cmp.lean`
- `/tmp/tc-decomp/sim/parent_sim.lean`

Snapshot and base:
- The snapshot pins project b4d606d and Mathlib 25730c7c.
- The workspace Submission.lean equals the frozen dispatch base 72492511 (contract only).

Reuse:
- The accepted Submission.dgcr_bwd_coordinate_form (candidate bb4ef845, with its accepted prerequisites dgcr_bwd_coordinate_covector and dgcr_bwd_extDeriv_smul_const) is exactly supplied steps 2–4.
- Its frozen type is byte-identical to the child lean_statement.
- It is not in this node's base or depends_on, so it must be listed as a child to be usable.

Library and leaf protocol:
- The pinned constancy theorem lives in Chapter08/DistributionalConstancy.lean and is outside the frozen import closure (Closure.lean: unknown identifier).
- Machine leaves may only append one theorem: check_source_delta forbids import, helper declarations and set_option.
- The library theorem therefore has to be applied in this node's non-leaf assembly. The two accepted non-leaf parents that import DistributionalConstancy did exactly this.
- Every Mathlib/SimonGMT lemma cited in the child proofs exists at the pin.

Lean checks:
- All child, parent and dependency types elaborate in the comparator's contract scope.
- A Lean assembly proves the exact parent type from top_density, S2C and the children, with standard axioms.
- The weak_derivs leaf compiles on top of bb4ef845 in the frozen closure, passes check_source_delta, and has standard axioms.
- A composed parent simulation compiles; its only sorryAx is the stub for the not-yet-proved top_density.

Names: no occurrence of dtc_bc_cz_tc_ anywhere.
