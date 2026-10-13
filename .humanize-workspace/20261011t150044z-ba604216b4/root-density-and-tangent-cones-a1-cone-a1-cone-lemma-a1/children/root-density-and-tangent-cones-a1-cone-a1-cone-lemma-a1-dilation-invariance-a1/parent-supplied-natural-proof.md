# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1.dilation_invariance-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 1, 2 (the identity ∂_sβ_s = (c'/c(s))·Lβ_s), 4 (Lβ_s is a test form) and 6 (constancy) of the parent proof (Simon Ch. 6, Lemma 2.33 via the homotopy formula 2.25–2.27).
- Specialization: the identity parametrization c(s) = s on J = (0, ∞), which the parent's Remark allows. Thus β_s(y) := sⁿω(sy) = h_s^#ω for h_s(y) = sy, so β_1 = ω, β_{λ⁻¹}(y) = λ⁻ⁿω(λ⁻¹y) (the parent's β_1) and c'/c(s) = 1/s.
- Notation: Dφ(y) = fderiv ℝ φ y; Lβ(y) := nβ(y) + Dβ(y)[y].

1. The function G. For s ∈ ℝ let β_s(y) := sⁿ·ω(sy) and G(s) := R.action(β_s).
- G(1) = R.action(ω), since 1ⁿ = 1 and 1·y = y.
- G(λ⁻¹) = R.action(ω'), since β_{λ⁻¹}(y) = (λ⁻¹)ⁿ·ω(λ⁻¹y) = ω'(y) for every y by hypothesis.
2. Constant factors. For c ∈ ℝ and any form φ, R.action(y ↦ c·φ(y)) = c·R.action(φ). Indeed θ(y)·ξ(y)(c·φ(y)) = c·(θ(y)·ξ(y)(φ(y))) by linearity of ξ(y), and ∫ c·f = c·∫ f (no integrability needed).
3. β_t is a test form for t ≠ 0.
- It is C^∞: ω is C^∞, y ↦ ty is linear, and the constant factor is tⁿ.
- Its support lies in the support of y ↦ ω(ty), because β_t(y) ≠ 0 forces ω(ty) ≠ 0. That support is compact since y ↦ ty is a homeomorphism of ℝ^P for t ≠ 0 (Mathlib HasCompactSupport.comp_smul).
Hence β_t ∈ TestFormOn univ n (tsupport ⊆ univ trivially).
4. Chain rule. Dβ_t(y) = tⁿ·(Dω(ty)∘(t·id)), so Dβ_t(y)[y] = tⁿ·Dω(ty)[ty] = tⁿ⁺¹·Dω(ty)[y].
5. γ_t := Lβ_t is a test form for t ≠ 0, and R.action(γ_t) = 0. Let γ_t(y) := n·β_t(y) + Dβ_t(y)[y].
- γ_t is C^∞: β_t is C^∞, hence so is Dβ_t, and applying a C^∞ family of continuous linear maps to the C^∞ vector y is C^∞ (Mathlib ContDiff.fderiv_right, ContDiff.clm_apply).
- Its support lies in supp β_t ∪ supp Dβ_t, and Dβ_t has compact support because β_t does (Mathlib HasCompactSupport.fderiv). So γ_t ∈ TestFormOn univ n.
- The pair (β_t, γ_t) satisfies γ_t(y) = n·β_t(y) + Dβ_t(y)[y] for all y by definition, so the hypothesis gives R.action(γ_t) = 0.
6. The derivative integrand is t⁻¹γ_t. Fix t > 0. By step 4,
γ_t(y) = n·tⁿ·ω(ty) + tⁿ⁺¹·Dω(ty)[y] = t·(n·t^{n−1}·ω(ty) + tⁿ·Dω(ty)[y]).
(For n ≥ 1, t·t^{n−1} = tⁿ; for n = 0 both first terms are 0.) Hence y ↦ n·t^{n−1}·ω(ty) + tⁿ·Dω(ty)[y] is the form y ↦ t⁻¹·γ_t(y), and by step 2 its action is t⁻¹·R.action(γ_t) = 0.
7. G' = 0 on (0, ∞). By the sibling scaled_derivative, for every t > 0, G has derivative R.action(y ↦ n·t^{n−1}·ω(ty) + tⁿ·Dω(ty)[y]) at t, which is 0 by step 6. This is the parent's F'(s₀) = (c'/c(s₀))·R.action(Lβ_{s₀}) = 0 with c(s) = s. So G is differentiable on the open interval (0, ∞) with derivative 0 there.
8. Constancy (parent step 6). (0, ∞) is open and connected (convex), so by the mean value theorem G is constant on it (Mathlib IsOpen.is_const_of_deriv_eq_zero). Since λ⁻¹ > 0 and 1 > 0, step 1 gives R.action(ω') = G(λ⁻¹) = G(1) = R.action(ω). ∎

Implementation note (not part of the numbered proof).
- The Lean proof below of exactly this frozen type was kernel-checked during this decomposition: Lean v4.35.0-rc3, Mathlib 25730c7c, after `import GMT.Ch07.Submission`, placed inside `namespace GMT.Ch07` with the contract's opens, like the accepted Submission theorems. #print axioms gives propext, Classical.choice, Quot.sound.
- Do not put `open scoped ContDiff` in front of this declaration: that scope makes `ω` a reserved token and breaks the binder `ω`.
- Write the smoothness order as `(⊤ : ℕ∞)` instead of `∞`: with `open scoped ENNReal`, `∞` is the ENNReal top.
- The sibling `scaled_derivative` is `Submission.dtc_cwv_scaled_action_hasDerivAt`.
theorem Submission.dtc_cwv_action_dilation_invariant : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n), (∀ β γ : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (γ : DifferentialForm (Euclid P) n) y = (n : ℝ) • (β : DifferentialForm (Euclid P) n) y + fderiv ℝ (β : DifferentialForm (Euclid P) n) y y) → R.action (γ : DifferentialForm (Euclid P) n) = 0) → ∀ lam : ℝ, 0 < lam → ∀ ω ω' : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (ω' : DifferentialForm (Euclid P) n) y = (lam⁻¹ ^ n) • (ω : DifferentialForm (Euclid P) n) (lam⁻¹ • y)) → R.action (ω' : DifferentialForm (Euclid P) n) = R.action (ω : DifferentialForm (Euclid P) n) := by
  intro P n R hL lam hlam ω ω' hω'
  have hws : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
  have hwc : HasCompactSupport (ω : DifferentialForm (Euclid P) n) := ω.property.1.2
  -- Step 2: the action is homogeneous under constant rescaling of the form.
  have hsmul : ∀ (c : ℝ) (φ : DifferentialForm (Euclid P) n),
      R.action (fun y => c • φ y) = c * R.action φ := by
    intro c φ
    unfold IMRep.action
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [map_smul, smul_eq_mul]
    ring
  -- Step 3: β_t(y) = tⁿ ω(t y) is a test form for t ≠ 0.
  have hβs : ∀ t : ℝ, ContDiff ℝ (⊤ : ℕ∞)
      (fun y => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • y)) := fun t =>
    (hws.comp (contDiff_const_smul t)).const_smul (t ^ n)
  have hβc : ∀ t : ℝ, t ≠ 0 → HasCompactSupport
      (fun y => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • y)) := by
    intro t ht
    refine (hwc.comp_smul ht).mono ?_
    intro y hy
    simp only [mem_support] at hy ⊢
    intro h0
    apply hy
    rw [h0, smul_zero]
  -- Step 4: chain rule, Dβ_t(y)[y] = tⁿ⁺¹ Dω(t y)[y].
  have hfd : ∀ (t : ℝ) (y : Euclid P),
      fderiv ℝ (fun z => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • z)) y y =
        (t ^ n * t) • fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • y) y := by
    intro t y
    have h1 : HasFDerivAt (fun z : Euclid P => t • z) (t • ContinuousLinearMap.id ℝ (Euclid P)) y :=
      (hasFDerivAt_id y).const_smul t
    have h2 : HasFDerivAt (fun z : Euclid P => (ω : DifferentialForm (Euclid P) n) (t • z))
        ((fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • y)).comp
          (t • ContinuousLinearMap.id ℝ (Euclid P))) y :=
      ((hws.differentiable (by simp)).differentiableAt (x := t • y)).hasFDerivAt.comp y h1
    have h3 : HasFDerivAt (fun z : Euclid P => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • z))
        ((t ^ n) • (fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • y)).comp
          (t • ContinuousLinearMap.id ℝ (Euclid P))) y :=
      h2.const_smul (t ^ n)
    rw [h3.fderiv]
    simp [smul_smul]
  -- Step 5: γ_t(y) = n β_t(y) + Dβ_t(y)[y] is a test form for t ≠ 0.
  have hγs : ∀ t : ℝ, ContDiff ℝ (⊤ : ℕ∞)
      (fun y => (n : ℝ) • ((t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • y)) +
        fderiv ℝ (fun z => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • z)) y y) := by
    intro t
    have hd : ContDiff ℝ (⊤ : ℕ∞)
        (fderiv ℝ (fun z => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • z))) :=
      (hβs t).fderiv_right (by simp)
    exact ((hβs t).const_smul (n : ℝ)).add (hd.clm_apply contDiff_id)
  have hγc : ∀ t : ℝ, t ≠ 0 → HasCompactSupport
      (fun y => (n : ℝ) • ((t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • y)) +
        fderiv ℝ (fun z => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • z)) y y) := by
    intro t ht
    have h1 : HasCompactSupport
        (fun y => (n : ℝ) • ((t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • y))) := by
      refine (hβc t ht).mono ?_
      intro y hy
      simp only [mem_support] at hy ⊢
      intro h0
      apply hy
      rw [h0, smul_zero]
    have h2 : HasCompactSupport
        (fun y => fderiv ℝ (fun z => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • z)) y y) := by
      refine ((hβc t ht).fderiv ℝ).mono ?_
      intro y hy
      simp only [mem_support] at hy ⊢
      intro h0
      apply hy
      rw [h0]
      rfl
    exact h1.add h2
  -- Steps 1, 5–7: G(s) = R.action β_s has derivative 0 on (0, ∞).
  let G : ℝ → ℝ := fun s => R.action (fun y => (s ^ n) • (ω : DifferentialForm (Euclid P) n) (s • y))
  have hG : ∀ t : ℝ, 0 < t → HasDerivAt G 0 t := by
    intro t ht
    have hD := Submission.dtc_cwv_scaled_action_hasDerivAt P n R ω t ht
    let β : TestFormOn (univ : Set (Euclid P)) n :=
      ⟨fun y => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • y), ⟨hβs t, hβc t ht.ne'⟩,
        subset_univ _⟩
    let γ : TestFormOn (univ : Set (Euclid P)) n :=
      ⟨fun y => (n : ℝ) • ((t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • y)) +
        fderiv ℝ (fun z => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • z)) y y,
        ⟨hγs t, hγc t ht.ne'⟩, subset_univ _⟩
    have hγ0 : R.action (γ : DifferentialForm (Euclid P) n) = 0 := hL β γ (fun y => rfl)
    have heq : (fun y => ((n : ℝ) * t ^ (n - 1)) • (ω : DifferentialForm (Euclid P) n) (t • y) +
        (t ^ n) • fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • y) y) =
        fun y => t⁻¹ • (γ : DifferentialForm (Euclid P) n) y := by
      funext y
      change _ = t⁻¹ • ((n : ℝ) • ((t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • y)) +
        fderiv ℝ (fun z => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • z)) y y)
      rw [hfd t y, smul_add, smul_smul, smul_smul, smul_smul]
      congr 2
      · rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; simp
        · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          field_simp
          simp [pow_succ]
      · field_simp
    have h0 : R.action (fun y => ((n : ℝ) * t ^ (n - 1)) • (ω : DifferentialForm (Euclid P) n) (t • y) +
        (t ^ n) • fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • y) y) = 0 := by
      rw [heq, hsmul, hγ0, mul_zero]
    rw [h0] at hD
    exact hD
  -- Step 8: constancy on the connected open set (0, ∞); endpoint values (step 1).
  have hconst : G lam⁻¹ = G 1 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
      (fun t ht => (hG t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hG t ht).deriv) (inv_pos.2 hlam) (show (0 : ℝ) < 1 from one_pos)
  have hG1 : G 1 = R.action (ω : DifferentialForm (Euclid P) n) := by
    simp [G]
  have hGl : G lam⁻¹ = R.action (ω' : DifferentialForm (Euclid P) n) := by
    simp only [G]
    congr 1
    funext y
    rw [hω' y]
  rw [← hGl, hconst, hG1]

## Key steps

1. G(s) := R.action(β_s), β_s(y) = sⁿω(sy); G(1) = R.action ω and G(λ⁻¹) = R.action ω'.
2. For t > 0, β_t and γ_t := nβ_t + Dβ_t[·] are test forms, so R.action γ_t = 0 by hypothesis.
3. Chain rule Dβ_t(y)[y] = tⁿ⁺¹Dω(ty)[y] gives n t^{n−1}ω(ty) + tⁿDω(ty)[y] = t⁻¹γ_t(y).
4. scaled_derivative: G'(t) = R.action(t⁻¹γ_t) = t⁻¹R.action γ_t = 0 on (0, ∞).
5. Mean value theorem on the connected open set (0, ∞): G(λ⁻¹) = G(1).

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
