# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1.weak_star_l1_upgrade-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent Step 3: 'For the second, given ε > 0 choose ψ ∈ C_c^∞(ℝᵏ) with ‖φ_I − ψ‖_{L¹} < ε; the error is at most 2L^kε uniformly in j', together with the supplied (M_r) remark that it suffices to test against smooth compactly supported ψ when the minors are uniformly bounded. Here this density reduction is stated for an arbitrary uniformly bounded sequence. Uses Mathlib's density of C_c^∞ in L¹ (MeasureTheory.MemLp.exist_eLpNorm_sub_le, Mathlib/Analysis/Normed/Lp/SmoothApprox.lean).

1. (Sign of C; basic estimate.) C ≥ |F(0)| ≥ 0. If θ is integrable and G is a.e.-strongly measurable with |G| ≤ C everywhere, then θG is integrable (Integrable.mul_bdd) and |∫ θG| ≤ ∫ |θ|·|G| ≤ C·∫|θ|.
2. (Approximation.) Fix ε > 0 and let η := ε/(4C + 1) > 0; then C·η < ε/4 (because 4C < 4C + 1). Since φ ∈ L¹ and smooth compactly supported functions are dense in L¹ (MemLp.exist_eLpNorm_sub_le with p = 1), there is a C^∞ function ψ with compact support and ∫ |φ − ψ| ≤ η (the eLpNorm with p = 1 is ∫⁻ ‖φ − ψ‖ₑ and its real value is ∫ |φ − ψ|). ψ is continuous with compact support, hence integrable.
3. (Convergence on ψ.) By hypothesis there is N with |∫ ψF_j − ∫ ψF| < ε/2 for every j ≥ N.
4. (Three-term estimate.) For j ≥ N, all products below being integrable by step 1, linearity gives ∫ φF_j − ∫ φF = ∫ (φ − ψ)F_j − ∫ (φ − ψ)F + (∫ ψF_j − ∫ ψF). By step 1 each of the first two terms has absolute value at most C·∫|φ − ψ| ≤ C·η < ε/4. Hence |∫ φF_j − ∫ φF| < ε/4 + ε/4 + ε/2 = ε.
5. (Conclusion.) ε > 0 was arbitrary, so ∫ φF_j → ∫ φF.

Lean realization (compiled during decomposition with the pinned toolchain in the Submission layout, inside namespace GMT.Ch07; #print axioms: propext, Classical.choice, Quot.sound; extra import: Mathlib.Analysis.Normed.Lp.SmoothApprox):
```lean
theorem Submission.dor_lmb_fcd_jwc_weak_star_l1_upgrade : (∀ (k : ℕ) (C : ℝ) (Fs : ℕ → Euclid k → ℝ) (F : Euclid k → ℝ), (∀ j, AEStronglyMeasurable (Fs j) (volume : Measure (Euclid k))) → AEStronglyMeasurable F (volume : Measure (Euclid k)) → (∀ j x, |Fs j x| ≤ C) → (∀ x, |F x| ≤ C) → (∀ ψ : Euclid k → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → Tendsto (fun j => ∫ x, ψ x * Fs j x) atTop (𝓝 (∫ x, ψ x * F x))) → ∀ φ : Euclid k → ℝ, Integrable φ → Tendsto (fun j => ∫ x, φ x * Fs j x) atTop (𝓝 (∫ x, φ x * F x))) := by
  intro k C Fs F hFs hF hFsb hFb hconv φ hφ
  have hC : 0 ≤ C := (abs_nonneg _).trans (hFb 0)
  -- |∫ θ G| ≤ C ∫ |θ| for |G| ≤ C
  have hint : ∀ θ : Euclid k → ℝ, Integrable θ → ∀ G : Euclid k → ℝ,
      AEStronglyMeasurable G (volume : Measure (Euclid k)) → (∀ x, |G x| ≤ C) →
      Integrable (fun x => θ x * G x) ∧ |∫ x, θ x * G x| ≤ C * ∫ x, ‖θ x‖ := by
    intro θ hθ G hG hGb
    refine ⟨hθ.mul_bdd hG (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hGb x), ?_⟩
    calc |∫ x, θ x * G x| = ‖∫ x, θ x * G x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x, C * ‖θ x‖ := by
          refine norm_integral_le_of_norm_le (hθ.norm.const_mul C) (Eventually.of_forall fun x => ?_)
          rw [norm_mul, Real.norm_eq_abs (G x), mul_comm]
          exact mul_le_mul_of_nonneg_right (hGb x) (norm_nonneg _)
      _ = C * ∫ x, ‖θ x‖ := integral_const_mul _ _
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (4 * C + 1) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨ψ, hψs, hψc, hψε⟩ :=
    (memLp_one_iff_integrable.2 hφ).exist_eLpNorm_sub_le (p := 1) (by simp) le_rfl hηpos
  have hψi : Integrable ψ := hψc.continuous.integrable_of_hasCompactSupport hψs
  have hdiff : ∫ x, ‖(φ - ψ) x‖ ≤ η := by
    have h1 := integral_norm_eq_lintegral_enorm (μ := (volume : Measure (Euclid k)))
      (hφ.sub hψi).aestronglyMeasurable
    rw [h1, ← eLpNorm_one_eq_lintegral_enorm]
    · exact ENNReal.toReal_le_of_le_ofReal hηpos.le hψε
    · exact (hφ.sub hψi).aestronglyMeasurable
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hconv ψ hψc hψs) (ε / 2) (by positivity)
  refine ⟨N, fun j hj => ?_⟩
  have h1 := hint (φ - ψ) (hφ.sub hψi) (Fs j) (hFs j) (hFsb j)
  have h2 := hint (φ - ψ) (hφ.sub hψi) F hF hFb
  have h3 := hint ψ hψi (Fs j) (hFs j) (hFsb j)
  have h4 := hint ψ hψi F hF hFb
  have e1 : ∫ x, φ x * Fs j x = (∫ x, (φ - ψ) x * Fs j x) + ∫ x, ψ x * Fs j x := by
    rw [← integral_add h1.1 h3.1]
    congr 1; funext x; simp only [Pi.sub_apply]; ring
  have e2 : ∫ x, φ x * F x = (∫ x, (φ - ψ) x * F x) + ∫ x, ψ x * F x := by
    rw [← integral_add h2.1 h4.1]
    congr 1; funext x; simp only [Pi.sub_apply]; ring
  have hNj := hN j hj
  rw [Real.dist_eq] at hNj ⊢
  rw [e1, e2]
  have hCη : C * η < ε / 4 := by
    rw [hη, mul_div_assoc']
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hA := h1.2.trans (mul_le_mul_of_nonneg_left hdiff hC)
  have hB := h2.2.trans (mul_le_mul_of_nonneg_left hdiff hC)
  have key : ∀ a1 b1 a2 b2 : ℝ, |(a1 + b1) - (a2 + b2)| ≤ |a1| + |a2| + |b1 - b2| := by
    intro a1 b1 a2 b2
    calc |(a1 + b1) - (a2 + b2)| = |(a1 - a2) + (b1 - b2)| := by ring_nf
      _ ≤ |a1 - a2| + |b1 - b2| := abs_add_le _ _
      _ ≤ |a1| + |a2| + |b1 - b2| := by
          have := abs_sub a1 a2
          linarith
  have := key (∫ x, (φ - ψ) x * Fs j x) (∫ x, ψ x * Fs j x) (∫ x, (φ - ψ) x * F x) (∫ x, ψ x * F x)
  linarith
```

## Key steps

1. |∫θG| ≤ C∫|θ| for integrable θ and |G| ≤ C.
2. Approximate φ in L¹ by a C^∞ compactly supported ψ with ∫|φ − ψ| ≤ ε/(4C + 1).
3. Convergence on ψ by hypothesis.
4. Three-term estimate: |∫φF_j − ∫φF| ≤ 2C∫|φ − ψ| + |∫ψF_j − ∫ψF| < ε for large j.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `python3 -I parse of nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-f189b35d70/parent-child-handoff.json and cat parent-supplied-plan.md (frozen type, empty sibling prerequisites)`
- `sed -n 1,140p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean; sed -n 60,160p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean (Covector = E [Wedge^Fin n]->L ℝ, DifferentialForm = E -> Covector, TestFormOn U n = testFormOnSubmodule: IsTestForm (ContDiff ∞ and HasCompactSupport) and tsupport ⊆ U)`
- `python3 -I scans of dag.json (1744 nodes): regex mollif|convolution|ContDiffBump|Piola|null Lagrang|Jacobian minor|weak continuity|lineDeriv|Rademacher|Matrix.det|minor|dense|weak-*; printed statuses and frozen types of cmcs_lipschitz_smoothing, cmcs_ls_mollify_lipschitz, cmr_cc_det_covector_exists, dgcr_stc_exists_normalized_mollifier, dor_ims_sua_mollify_unit_field, dor_lmbsf_pwl_fderiv_weak_integrable, cbr_ci_cp_pr_factorial_mul_eq_sum_det, cbr_ci_cp_tr_smooth_approx_of_continuous, codim1_rdo_dg_bvc_smooth_indicator_approx, regcomp_exists_continuous_unit_form_approx; siblings under deformation-a1; grep dor_lmb_fcd_jwc in dag.json and rg dor_lmb_fcd_jwc in the snapshot project (no match: names fresh)`
- `git show 00c458d8b5f0043b634cbdd0b8d43d20d1d7deb6:GMT/Ch07/Submission.lean and git show fee01ff86c9de6b32f7cfc6b3f5088750ef5af7e:GMT/Ch07/Submission.lean (accepted proofs of cmcs_ls_mollify_lipschitz and cmr_cc_det_covector_exists); python3 -I import scan of accepted candidate commits (accepted nodes add Mathlib imports such as ContinuousMapDense, BumpFunction.SmoothApprox)`
- `lake env lean /tmp/jwc-decomp-k7q2/Avail*.lean: #check in the import closure of GMT.Ch07.Submission (present: LipschitzWith.ae_differentiableAt, LipschitzWith.integral_lineDeriv_mul_eq, measurable_fderiv, HasCompactSupport.contDiff_convolution_left, HasCompactSupport.hasFDerivAt_convolution_left, dist_convolution_le, extDeriv_pullback, extDeriv_apply, extDeriv_extDeriv_apply, Matrix.det_succ_row_zero, MultilinearMap.map_sum, Integrable.induction, IsUnifLocDoublingMeasure.ae_tendsto_average; absent without extra imports: ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, ContDiffBump.normed, Integrable.exists_hasCompactSupport_integral_sub_le, Matrix.det_le, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable)`
- `rg -n in snapshot mathlib: theorem ae_convolution_tendsto_right_of_locallyIntegrable (Analysis/Calculus/BumpFunction/Convolution.lean:103), theorem exist_eLpNorm_sub_le (Analysis/Normed/Lp/SmoothApprox.lean:87), theorem det_le (LinearAlgebra/Matrix/AbsoluteValue.lean:43), theorem extDeriv_pullback (Analysis/Calculus/DifferentialForm/Basic.lean:259), DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap (Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:137), alternatizeUncurryFinCLM_apply (Analysis/Normed/Module/Alternating/Uncurry/Fin.lean:129), precompL_apply (Analysis/Normed/Operator/Bilinear.lean:379), Continuous.exists_contDiff_approx (Geometry/Manifold/SmoothApprox.lean:132), Integrable.exists_hasCompactSupport_integral_sub_le (MeasureTheory/Function/ContinuousMapDense.lean:226)`
- `sed -n 1,28p, 300,372p, 580,660p verifier/gmt-compare.py (child challenge = import GMT.Ch07.Submission + contract scope replay; new Lean files allowed only under GMT/Ch07); verifier/lean_contract.py validate_lean_statement; runtime.py _existing_lean_name_problem (accepted declarations reusable only with identical frozen type) and _decompose (depth >= max_depth stops splitting)`
- `lake env lean /tmp/jwc-decomp-k7q2/lean/Chal_*.lean (12 exact comparator challenges), AllProps.lean, ParentAssembly.lean, E3Assembly.lean, C3Assembly.lean, C4bAssembly.lean, C4aAssembly.lean, B2Assembly.lean, H0Proof.lean, E2Proof.lean, C1Proof.lean, B1Proof.lean, AllProofs.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-f189b35d70/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-f189b35d70/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-e358a4c0e4/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-coo-498906c61d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-lipschitz-smoot-0c46a16452/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/tmp/jwc-decomp-k7q2/lean/AllProofs.lean`
- `/tmp/jwc-decomp-k7q2/lean/ParentAssembly.lean`

Snapshot: project b4d606db, mathlib 25730c7c; the snapshot Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Neither the snapshot project nor SimonGMT contains weak continuity of Jacobian minors, a Piola identity, or a Lipschitz mollification lemma with a.e. derivative convergence (SimonGMT Chapter06 gives the Covector/DifferentialForm/TestFormOn objects and d^2 = 0 / pull-back naturality on open domains). Pinned Mathlib supplies every tool used by the child proofs: Rademacher (LipschitzWith.ae_differentiableAt), Lipschitz integration by parts (LipschitzWith.integral_lineDeriv_mul_eq), convolution differentiation and smoothness, extDeriv_pullback/extDeriv_apply, Laplace expansion, and, with an extra import, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, MemLp.exist_eLpNorm_sub_le and Matrix.det_le. Reuse: cmr_cc_det_covector_exists and cmcs_ls_mollify_lipschitz are comparator-accepted with byte-identical frozen types and are reused as siblings; the other nine dor_lmb_fcd_jwc_* names are fresh. Lean: the 12 types compile as exact comparator challenges; the parent and all internal dependencies were proved from their listed siblings, the leaves were proved, and a combined file with all 12 declarations compiles with axioms [propext, Classical.choice, Quot.sound].
