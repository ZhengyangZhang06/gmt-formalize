# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1.lie_annihilation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 0(c), 0(d), 4 and 5 of the parent proof.
- Simon Ch. 6, Lemma 2.33 (chapter-06.txt lines 557–567): its proof shows that the homotopy term vanishes because x ∧ C⃗ = 0 and ∂C = 0. Here this is made explicit through Cartan's formula L_X = dι_X + ι_X d for the Euler field X(x) = x.
- Simon 7.3.1 (chapter-07.txt line 359) applies the lemma to tangent cones.
Notation:
- M = R.carrier, θ = R.mult, ξ = R.orient, ν := Hⁿ⌞M = μHE[n].restrict M, and R.measure = ν.withDensity θ.
- R.Represents C means C(φ) = R.action(φ) = ∫ θ(y)ξ(y)(φ(y)) dν(y) for all φ ∈ TestFormOn univ n.
- ι_Xφ(z) := φ(z).curryLeft z; d = exteriorDerivative; Dβ(y) = fderiv ℝ β y.

1. Since n ≥ 1, write n = m + 1. Then (n : ℝ) = m + 1, the wedge hypothesis concerns (m+2)-covectors, and BoundaryVanishes C means C.boundary = 0 (definition of BoundaryVanishes in degree m + 1).
2. ψ := ι_Xβ is a test m-form. β is a test (m+1)-form, so by the sibling contraction_test_form, z ↦ β(z).curryLeft z is C^∞ with compact support. Regard it as ψ ∈ TestFormOn univ m (tsupport ⊆ univ).
3. χ := ι_X dβ is a test (m+1)-form. dβ is a test (m+2)-form, since exterior differentiation preserves test forms (SimonGMT exteriorDerivative_isTestForm). So by contraction_test_form applied with m + 1 in place of m, χ(z) = (dβ(z)).curryLeft z defines χ ∈ TestFormOn univ (m+1).
4. Cartan. β is C^∞, hence differentiable at every y, so the sibling euler_cartan gives dψ(y) + χ(y) = (m+1)·β(y) + Dβ(y)[y] = γ(y) for every y (hypothesis on γ, with (n : ℝ) = m + 1). Hence γ = dψ + χ in TestFormOn univ (m+1), where dψ = exteriorDerivativeTestOn univ m ψ.
5. Linearity (parent 0(d)). C is linear on test forms, so C(γ) = C(dψ) + C(χ).
6. Boundary term (parent 0(d), step 5). By GeometricCurrentOn.boundary_apply, C(dψ) = C(exteriorDerivativeTestOn univ m ψ) = (C.boundary)(ψ) = 0, since C.boundary = 0.
7. Wedge term (parent 0(c), step 5). C(χ) = R.action(χ) = ∫ θ(y)·ξ(y)((dβ(y)).curryLeft y) dν(y).
- The function y ↦ (θ(y) : ℝ≥0∞) is measurable. By Mathlib ae_withDensity_iff, the hypothesis "for R.measure-a.e. x, ξ(x)(α.curryLeft x) = 0 for all α" is equivalent to: for ν-a.e. y, θ(y) ≠ 0 implies ξ(y)(α.curryLeft y) = 0 for all α.
- ν-a.e. y lies in M (ν is Hⁿ restricted to the measurable set M), and θ(y) > 0 for y ∈ M (R.mult_pos).
- Taking α := dβ(y), the integrand θ(y)·ξ(y)((dβ(y)).curryLeft y) vanishes for ν-a.e. y, so the integral is 0 (no integrability needed).
Thus C(χ) = 0.
8. Conclusion. C(γ) = C(dψ) + C(χ) = 0 + 0 = 0. ∎

Implementation note (not part of the numbered proof).
- The Lean proof below of exactly this frozen type was kernel-checked during this decomposition: Lean v4.35.0-rc3, Mathlib 25730c7c, after `import GMT.Ch07.Submission`, placed inside `namespace GMT.Ch07` with the contract's opens, like the accepted Submission theorems. #print axioms gives propext, Classical.choice, Quot.sound.
- Do not put `open scoped ContDiff` in front of this declaration: that scope makes `ω` a reserved token and breaks the binder `ω`.
- Write the smoothness order as `(⊤ : ℕ∞)` instead of `∞`: with `open scoped ENNReal`, `∞` is the ENNReal top.
- The siblings are `Submission.dtc_cwv_euler_contraction_isTestForm` (contraction_test_form) and `Submission.dtc_cone_euler_cartan` (euler_cartan).
theorem Submission.dtc_cwv_euler_lie_annihilated : ∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), 0 < n → R.Represents C → BoundaryVanishes C → (∀ᵐ x ∂R.measure, ∀ β : Covector (Euclid P) (n + 1), R.orient x (ContinuousAlternatingMap.curryLeft β x) = 0) → ∀ β γ : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (γ : DifferentialForm (Euclid P) n) y = (n : ℝ) • (β : DifferentialForm (Euclid P) n) y + fderiv ℝ (β : DifferentialForm (Euclid P) n) y y) → C γ = 0 := by
  intro P n C R hn hR hb hw β γ hγ
  -- Step 1: write `n = m + 1`.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- Step 2: `ψ = ι_X β` is a test `m`-form.
  have hψ : IsTestForm (fun z => ContinuousAlternatingMap.curryLeft
      ((β : DifferentialForm (Euclid P) (m + 1)) z) z) :=
    Submission.dtc_cwv_euler_contraction_isTestForm P m _ β.property.1
  let ψ : TestFormOn (univ : Set (Euclid P)) m := ⟨_, hψ, subset_univ _⟩
  -- Step 3: `χ = ι_X dβ` is a test `(m+1)`-form.
  have hdβ : IsTestForm (exteriorDerivative (β : DifferentialForm (Euclid P) (m + 1))) :=
    exteriorDerivative_isTestForm β.property.1
  have hχ := Submission.dtc_cwv_euler_contraction_isTestForm P (m + 1) _ hdβ
  let χ : TestFormOn (univ : Set (Euclid P)) (m + 1) := ⟨_, hχ, subset_univ _⟩
  -- Step 4: Cartan's formula gives `γ = dψ + χ`.
  have hsplit : γ = exteriorDerivativeTestOn univ m ψ + χ := by
    apply Subtype.ext
    funext y
    have hdiff : DifferentiableAt ℝ (β : DifferentialForm (Euclid P) (m + 1)) y :=
      (β.property.1.1.differentiable (by simp)).differentiableAt
    have hc := Submission.dtc_cone_euler_cartan P m β y hdiff
    rw [hγ y]
    push_cast
    exact hc.symm
  -- Step 6: `C(dψ) = ∂C(ψ) = 0`.
  have hbd : C.boundary = 0 := hb
  have h1 : C (exteriorDerivativeTestOn univ m ψ) = 0 := by
    have := congrArg (fun T : GeometricCurrentOn (univ : Set (Euclid P)) m => T ψ) hbd
    simpa [GeometricCurrentOn.boundary_apply] using this
  -- Step 7: `C(χ) = ∫_M θ ξ((dβ(y)).curryLeft y) dHⁿ = 0` by the wedge hypothesis.
  have h2 : C χ = 0 := by
    rw [hR χ]
    unfold IMRep.action
    apply integral_eq_zero_of_ae
    have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := by
      exact measurable_from_nat.comp R.measurable_mult
    have h' := (ae_withDensity_iff hθ).1 hw
    have hmem : ∀ᵐ x ∂(μHE[m + 1].restrict R.carrier), x ∈ R.carrier :=
      ae_restrict_mem R.measurableSet_carrier
    filter_upwards [h', hmem] with x hx hxM
    have hpos : (R.mult x : ℝ≥0∞) ≠ 0 := by
      have := R.mult_pos x hxM
      exact_mod_cast this.ne'
    have := hx hpos (exteriorDerivative (β : DifferentialForm (Euclid P) (m + 1)) x)
    simp only [Pi.zero_apply]
    change (R.mult x : ℝ) * R.orient x (ContinuousAlternatingMap.curryLeft
      (exteriorDerivative (β : DifferentialForm (Euclid P) (m + 1)) x) x) = 0
    rw [this, mul_zero]
  -- Steps 5 and 8: linearity, `C(γ) = C(dψ) + C(χ) = 0`.
  rw [hsplit]
  change C.toCurrent (exteriorDerivativeTestOn univ m ψ + χ) = 0
  rw [map_add]
  exact (congrArg₂ (· + ·) h1 h2).trans (add_zero 0)

## Key steps

1. n = m + 1; ψ := ι_Xβ ∈ 𝒟^m and χ := ι_X dβ ∈ 𝒟^{m+1} by contraction_test_form (dβ is a test form).
2. euler_cartan: dψ + χ = (m+1)β + Dβ[·] = γ, so C(γ) = C(dψ) + C(χ).
3. C(dψ) = (∂C)(ψ) = 0 since ∂C = 0.
4. C(χ) = ∫_M θ ξ((dβ(y)).curryLeft y) dHⁿ = 0: the wedge hypothesis transfers from θHⁿ⌞M to Hⁿ⌞M (ae_withDensity_iff, θ ≥ 1 on M).

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
