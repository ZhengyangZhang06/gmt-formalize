# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1.contraction_test_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 4 of the parent proof ("Both are smooth (compositions of smooth maps with continuous bilinear maps …) and have tsupport ⊆ tsupport β_{s₀}"), used there for ψ = ι_Xβ and χ = ι_X dβ (Simon Ch. 6, 2.25–2.26 and Lemma 2.33).
- Conventions: (f.curryLeft x)(v_1, …, v_m) = f(x, v_1, …, v_m) (Mathlib ContinuousAlternatingMap.curryLeft).
- IsTestForm φ means φ is C^∞ (all orders, ContDiff ℝ ∞) and has compact support.

1. Bilinear structure. f ↦ f.curryLeft is a linear isometry Λ^{m+1}(ℝ^P) → L(ℝ^P, Λ^m(ℝ^P)) (Mathlib ContinuousAlternatingMap.curryLeftLI); write A for it as a continuous linear map. Then (ι_Xβ)(z) = A(β(z))(z) for every z.
2. Smoothness. z ↦ A(β(z)) is C^∞ (a continuous linear map composed with the C^∞ map β), and z ↦ z is C^∞. The application of a C^∞ family of continuous linear maps to a C^∞ vector is C^∞ (Mathlib ContDiff.clm_apply). Hence ι_Xβ is C^∞.
3. Support. If β(z) = 0, then (ι_Xβ)(z) = 0.curryLeft z = 0. Hence supp(ι_Xβ) ⊆ supp β ⊆ tsupport β, which is compact since β has compact support; therefore ι_Xβ has compact support (Mathlib HasCompactSupport.mono).
4. By steps 2 and 3, ι_Xβ is a test m-form. ∎

Implementation note (not part of the numbered proof).
- The Lean proof below of exactly this frozen type was kernel-checked during this decomposition: Lean v4.35.0-rc3, Mathlib 25730c7c, after `import GMT.Ch07.Submission`, placed inside `namespace GMT.Ch07` with the contract's opens, like the accepted Submission theorems.
- #print axioms gives propext, Classical.choice, Quot.sound.
theorem Submission.dtc_cwv_euler_contraction_isTestForm : ∀ (P m : ℕ) (β : DifferentialForm (Euclid P) (m + 1)), IsTestForm β → IsTestForm (fun z => ContinuousAlternatingMap.curryLeft (β z) z) := by
  intro P m β hβ
  obtain ⟨hs, hc⟩ := hβ
  refine ⟨?_, ?_⟩
  · -- Steps 1–2: `z ↦ (curryLeftLI (β z)) z` is a smooth family of CLMs applied to `z`.
    change ContDiff ℝ (⊤ : ℕ∞) (fun z => (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ)
      (E := Euclid P) (F := ℝ) (n := m)).toContinuousLinearMap (β z) z)
    exact (((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid P) (F := ℝ)
      (n := m)).toContinuousLinearMap.contDiff).comp hs).clm_apply contDiff_id
  · -- Step 3: `β z = 0 → β(z).curryLeft z = 0`, so the support stays inside `supp β`.
    refine hc.mono ?_
    intro z hz
    simp only [mem_support] at hz ⊢
    intro h0
    apply hz
    rw [h0]
    rfl

## Key steps

1. ι_Xβ(z) = A(β(z))(z) with A = curryLeftLI, a continuous linear map.
2. C^∞: a C^∞ family of continuous linear maps applied to the C^∞ vector z (ContDiff.clm_apply).
3. β(z) = 0 ⇒ ι_Xβ(z) = 0, so supp ι_Xβ ⊆ tsupport β is compact (HasCompactSupport.mono).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp … GMT/Ch07/Submission.lean (identical); cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); git -C lake-packages-25730c7c/simongmt rev-parse HEAD (2b366308)`
- `cat simongmt/Poincare/SimonGMT/Chapter06/Forms.lean and Chapter06/AffineCurrentPushforward.lean; sed -n 1,260p Chapter06/Currents.lean; grep -n boundary Chapter06/Currents.lean; sed -n 1,80p Chapter06/CurrentLocalEquality.lean (IsTestForm, TestFormOn, exteriorDerivative_isTestForm, exteriorDerivativeTestOn, GeometricCurrentOn.boundary_apply, affinePullbackForm, affinePullbackTestOn, affinePushforward_apply, restrictDomain_apply, testFormOnInclusion)`
- `rg -n 'theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le' Mathlib/Analysis/Calculus/ParametricIntegral.lean; rg -n 'is_const_of_deriv' Mathlib/Analysis/Calculus/MeanValue.lean; rg -n 'HasCompactSupport.comp_smul' Mathlib/Topology/Algebra/ConstMulAction.lean; rg -n 'ae_withDensity_iff' Mathlib/MeasureTheory/Measure/WithDensity.lean; rg -n 'bounded_above_of_compact_support' Mathlib/Analysis/Normed/Group/Bounded.lean; rg -n 'aestronglyMeasurable_comp₂|apply_continuousLinearMap' Mathlib/MeasureTheory; rg -n 'integrable_indicator_iff|Integrable.mono' Mathlib/MeasureTheory`
- `python3 census of lean_name/lean_statement in dag.json and nodes/*/decomposition-v*.json (patterns IsConeCurrent, R.action with HasDerivAt, curryLeft (β z) z, ‖R.orient x‖, IsUnitOrientationOf with ≤); rg -l -F for each of the five new names in dag.json, nodes, GMT, the project snapshot and simongmt/Poincare (0 hits)`
- `git show 52115c22:GMT/Ch07/Submission.lean (Submission.cone_current_apply_dilation_pullback); git show 77ba6718 (Submission.dtc_cone_euler_cartan); git show f1339f96 (Submission.regcomp_rim_action_integrable); git log/show d90c7c52 (implementation base merging a reused cross-branch child)`
- `sed -n 430,480p and 540,580p book/chapter-06.txt (2.25–2.27, Lemma 2.33); sed -n 340,365p book/chapter-07.txt (7.3.1 proof, 'apply Lemma 2.33 to deduce that C is a cone')`
- `grep -n '_existing_lean_name_problem|_solve_children|_install_parent_supplied_child_handoff|_accepted_checkpoint' /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py; store.py ensure; .humanize/swarm-configs/be41fd7aece94f7eb83ed6e064a802a0.json (max_nodes 1000); dag.json node count 417`
- `python3 -I /tmp/conelemma-scripts/gen.py (gmt-compare.child_modules mode=contract, lean_contract.validate_lean_statement) then lake env lean gen/Ch_*.lean; lake env lean Assembly.lean, Trial1.lean, Trial2.lean, Trial3.lean, final/Final.lean, final/FinalSol.lean, final/FromJson.lean, each with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-euler-cartan-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-euler-cartan-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-euler-cartan-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-orie-c3a822a8f5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-orie-c3a822a8f5/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-orie-c3a822a8f5/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-one-dim-cones-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-tangent-projection-measurable-a1/parent-implementation-base.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-im-sub-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-mass-eq-measure-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/be41fd7aece94f7eb83ed6e064a802a0.json`
- `/tmp/conelemma-decomp/children.json`
- `/tmp/conelemma-decomp/Assembly.lean`
- `/tmp/conelemma-decomp/Trial1.lean`
- `/tmp/conelemma-decomp/Trial2.lean`
- `/tmp/conelemma-decomp/Trial3.lean`
- `/tmp/conelemma-decomp/final/Final.lean`
- `/tmp/conelemma-decomp/final/FinalSol.lean`
- `/tmp/conelemma-decomp/final/FromJson.lean`
- `/tmp/conelemma-scripts/gen.py`
- `/tmp/conelemma-scripts/build.py`

The snapshot contract (project b4d606d, Mathlib 25730c7c, simongmt 2b36630) is byte-identical to the workspace Contract.lean and Submission.lean. All seven child types therefore elaborate after `import GMT.Ch07.Submission` in the comparator's contract scope (namespace GMT.Ch07 with the contract's opens).

SimonGMT supplies what the children need about forms and currents:
- IsTestForm, TestFormOn, exteriorDerivative_isTestForm and exteriorDerivativeTestOn;
- GeometricCurrentOn.boundary_apply (C.boundary ψ = C(dψ));
- affinePullbackForm, affinePullbackTestOn, affinePushforward_apply and restrictDomain_apply, which make η_{0,λ#}C(ω) = C(ω(λ⁻¹·)∘λ⁻¹) definitional.

The Mathlib snapshot supplies hasDerivAt_integral_of_dominated_loc_of_deriv_le, IsOpen.is_const_of_deriv_eq_zero, HasCompactSupport.comp_smul/fderiv/mono, ae_withDensity_iff, ContinuousAlternatingMap.curryLeftLI/map_smul_univ and ContDiff.clm_apply/fderiv_right. Mathlib has no Lie-derivative or Cartan API; the Euler-field Cartan identity is the accepted Submission.dtc_cone_euler_cartan.

Reuse:
- Submission.unit_orientation_norm_le_one (commit 0325970d) and Submission.dtc_cone_euler_cartan (commit 77ba6718) passed their isolated comparators and have byte-identical frozen types.
- runtime.py maps accepted names with identical types to the existing nodes and skips their handoffs, and implementation bases merge reused commits (d90c7c52).
- The five new dtc_cwv_* names occur nowhere in the run, the project or SimonGMT.
- dag.json has 417 nodes against max_nodes 1000.

Lean checks:
- Kernel-checked proofs of all five new children, the accepted proofs of the two reused declarations and the 8-line parent assembly compile together with axioms propext, Classical.choice and Quot.sound only.
- The comparator solution side `exact Submission.X` elaborates against every frozen type.
- The code embedded in the natural proofs was re-extracted from the final JSON and recompiled.

Pitfalls found:
- `open scoped ContDiff` makes ω a token;
- Continuous.bounded_above_of_compact_support on the CLM-valued fderiv times out.
