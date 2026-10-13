# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.caccioppoli-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.caccioppoli-a1.energy_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4 and 5 of the parent proof (expansion and absorption) and the first part of step 6 (passage from integrals to lower integrals). Here they are carried out for an arbitrary admissible cutoff eta and an arbitrary open set U. The parent proof uses U = B_{2 rho}(y) and its particular eta. The proof uses the sibling lemma test_function (Lean: Submission.dohr_eb_sch_cacc_test_function).
Notation. L := L(R^n, R^l) with the operator norm. A[P][Q] is the value of the continuous bilinear form A, so Q -> A[P][Q] is a continuous linear form on L. DV(x) := fderiv R V x and D eta(x) := fderiv R eta x. For v in R^l and a linear form p on R^n, v (x) p in L is h -> p(h) v; in Lean this is p.smulRight v, and its operator norm is ||p|| ||v|| (ContinuousLinearMap.norm_smulRight_apply). All integrals are over R^n with Lebesgue measure.
1. The test function. Let zeta := eta^2 (V - c). By test_function, applied to U, V, eta and c (U is open, V is C^1 on U, eta is C^1 with compact support, tsupport(eta) is contained in U), zeta is C^1 on R^n, has compact support, and tsupport(zeta) is contained in U. Moreover D zeta(x) = eta(x)^2 DV(x) + 2 eta(x) (V(x) - c) (x) D eta(x) for every x. By the hypothesis on V, the integral of h is 0, where h(x) := A[DV(x)][D zeta(x)].
2. The integrands. Put g1(x) := eta(x)^2 ||DV(x)||^2 and g3(x) := ||V(x) - c||^2 ||D eta(x)||^2.
(a) Continuity on U. DV is continuous on U, because V is C^1 on the open set U (ContDiffOn.continuousOn_fderiv_of_isOpen). V is continuous on U. D eta and D zeta are continuous on R^n, because eta and zeta are C^1. A is continuous. So h, g1 and g3 are continuous on U.
(b) Supports. If x is not in tsupport(zeta), then zeta vanishes near x, so D zeta(x) = 0 and h(x) = A[DV(x)][0] = 0. If x is not in tsupport(eta), then eta(x) = 0 and D eta(x) = 0, so g1(x) = g3(x) = 0. Taking closures, tsupport(h) is contained in tsupport(zeta), which is contained in U. Likewise tsupport(g1) and tsupport(g3) are contained in tsupport(eta), which is contained in U.
(c) Global continuity and integrability. Let f be continuous on the open set U with tsupport(f) contained in U. Then f is continuous on R^n: at points of U by (a), and at points outside tsupport(f) because f vanishes near them (ContinuousOn.continuous_of_tsupport_subset). So h, g1 and g3 are continuous on R^n. Their tsupports are closed subsets of the compact sets tsupport(zeta) and tsupport(eta), so they have compact support. A continuous function with compact support is Lebesgue integrable (Continuous.integrable_of_hasCompactSupport). Hence h, g1 and g3 are integrable.
3. Expansion. Fix x, and put P := DV(x) and W := (V(x) - c) (x) D eta(x). By the derivative formula of step 1 and the linearity of Q -> A[P][Q],
h(x) = eta(x)^2 A[P][P] + 2 eta(x) A[P][W].
In the notation of the parent proof this is f1 + 2 f2.
4. Pointwise lower bound. Put a := eta(x) ||P|| and b := ||V(x) - c|| ||D eta(x)||. Then a >= 0 because eta >= 0, b >= 0, g1(x) = a^2 and g3(x) = b^2.
(a) Legendre condition: eta(x)^2 A[P][P] >= eta(x)^2 lam ||P||^2 = lam a^2.
(b) Bound: ||W|| = ||D eta(x)|| ||V(x) - c|| = b, so A[P][W] >= -|A[P][W]| >= -Lam ||P|| b. Multiplying by 2 eta(x) >= 0 gives 2 eta(x) A[P][W] >= -2 Lam a b.
(c) Young's inequality: (lam/2) a^2 + (2 Lam^2/lam) b^2 - 2 Lam a b = (lam a - 2 Lam b)^2 / (2 lam) >= 0. This holds for every real Lam, because lam > 0.
Adding (a) and (b) and then using (c):
h(x) >= lam a^2 - 2 Lam a b >= lam a^2 - (lam/2) a^2 - (2 Lam^2/lam) b^2 = (lam/2) g1(x) - (2 Lam^2/lam) g3(x).
5. Absorption. All functions in step 4 are integrable, by step 2. Integrating the pointwise bound and using that the integral of h is 0 (step 1):
(lam/2) (integral of g1) - (2 Lam^2/lam) (integral of g3) <= integral of h = 0.
Since lam > 0, multiplying by 2/lam gives
integral of g1 <= (4 Lam^2/lam^2) (integral of g3).
This is the parent's chain lam (integral of g1) <= integral of f1 = -2 (integral of f2) <= 2 Lam (integral of g2) <= (lam/2) (integral of g1) + (2 Lam^2/lam) (integral of g3). Here the pointwise inequalities are combined before integrating, so only h, g1 and g3 need to be integrable. The absorbed quantity, the integral of g1, is finite.
6. Lower integrals. g1 and g3 are integrable and nonnegative. Hence the lower integral of ofReal(g1) equals ofReal(integral of g1), and the lower integral of ofReal(g3) equals ofReal(integral of g3) (ofReal_integral_eq_lintegral_ofReal). ofReal is monotone, and ofReal(r s) = ofReal(r) ofReal(s) when r >= 0. Using step 5:
lower integral of ofReal(eta^2 ||DV||^2) = ofReal(integral of g1) <= ofReal((4 Lam^2/lam^2) (integral of g3)) = ofReal(4 Lam^2/lam^2) * ofReal(integral of g3) = ofReal(4 Lam^2/lam^2) * (lower integral of ofReal(||V - c||^2 ||D eta||^2)).
This is the claim. QED
Appendix (reference Lean proof, checked; not part of the mathematical argument). At Lean v4.35.0-rc3 / Mathlib 25730c7c the declaration below compiles when placed inside `namespace Submission` of GMT/Ch05/Submission.lean (that is, inside `namespace GMT.Ch05`, after `open RectifiableVarifold`, before `main_theorem`), and the comparator's generated NodeSolution (`exact Submission.dohr_eb_sch_cacc_energy_estimate`) closes the frozen target; `#print axioms` reports only propext, Classical.choice, Quot.sound. In this scope the bare identifier `support` resolves to `RectifiableVarifold.support`, so the proof writes `Function.support`. It invokes the sibling `Submission.dohr_eb_sch_cacc_test_function` with exactly its frozen type.
```lean
theorem dohr_eb_sch_cacc_energy_estimate :
    ∀ (n ℓ : ℕ) (lam Lam : ℝ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (U : Set (Rn n)) (V : Rn n → Rn ℓ) (η : Rn n → ℝ) (c : Rn ℓ), 0 < lam → (∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ A P P) → (∀ P Q : Rn n →L[ℝ] Rn ℓ, |A P Q| ≤ Lam * ‖P‖ * ‖Q‖) → IsOpen U → ContDiffOn ℝ 1 V U → ContDiff ℝ 1 η → HasCompactSupport η → tsupport η ⊆ U → (∀ x, 0 ≤ η x) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0) → ∫⁻ x, ENNReal.ofReal (η x ^ 2 * ‖fderiv ℝ V x‖ ^ 2) ≤ ENNReal.ofReal (4 * Lam ^ 2 / lam ^ 2) * ∫⁻ x, ENNReal.ofReal (‖V x - c‖ ^ 2 * ‖fderiv ℝ η x‖ ^ 2) := by
  intro n ℓ lam Lam A U V η c hlam hcoer hbdd hU hV hη hηc hηU hη0 hweak
  obtain ⟨hζ1, hζc, hζU, hζd⟩ :=
    Submission.dohr_eb_sch_cacc_test_function n ℓ U V η c hU hV hη hηc hηU
  have h0 := hweak _ hζ1 hζc hζU
  -- continuity of the ingredients
  have hDVc : ContinuousOn (fderiv ℝ V) U := hV.continuousOn_fderiv_of_isOpen hU le_rfl
  have hVc : ContinuousOn V U := hV.continuousOn
  have hDη : Continuous (fderiv ℝ η) := hη.continuous_fderiv one_ne_zero
  have hDζ : Continuous (fderiv ℝ (fun x => η x ^ 2 • (V x - c))) := hζ1.continuous_fderiv one_ne_zero
  -- the three integrands
  set h : Rn n → ℝ := fun x => A (fderiv ℝ V x) (fderiv ℝ (fun x => η x ^ 2 • (V x - c)) x) with hh
  set g1 : Rn n → ℝ := fun x => η x ^ 2 * ‖fderiv ℝ V x‖ ^ 2 with hg1
  set g3 : Rn n → ℝ := fun x => ‖V x - c‖ ^ 2 * ‖fderiv ℝ η x‖ ^ 2 with hg3
  have hsupp_h : Function.support h ⊆ tsupport (fun x => η x ^ 2 • (V x - c)) := by
    intro x hx
    by_contra hxs
    apply hx
    simp only [hh, fderiv_of_notMem_tsupport ℝ hxs, map_zero]
  have hsupp_g1 : Function.support g1 ⊆ tsupport η := by
    intro x hx
    by_contra hxs
    apply hx
    simp only [hg1, image_eq_zero_of_notMem_tsupport hxs]
    ring
  have hsupp_g3 : Function.support g3 ⊆ tsupport η := by
    intro x hx
    by_contra hxs
    apply hx
    simp only [hg3, fderiv_of_notMem_tsupport ℝ hxs, norm_zero]
    ring
  have hcont_h : Continuous h := by
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((closure_minimal hsupp_h (isClosed_tsupport _)).trans hζU)
    exact (A.continuous.comp_continuousOn hDVc).clm_apply hDζ.continuousOn
  have hcont_g1 : Continuous g1 := by
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((closure_minimal hsupp_g1 (isClosed_tsupport _)).trans hηU)
    exact (hη.continuous.pow 2).continuousOn.mul (hDVc.norm.pow 2)
  have hcont_g3 : Continuous g3 := by
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((closure_minimal hsupp_g3 (isClosed_tsupport _)).trans hηU)
    exact ((hVc.sub continuousOn_const).norm.pow 2).mul (hDη.norm.pow 2).continuousOn
  have hint_h : Integrable h := hcont_h.integrable_of_hasCompactSupport (hζc.mono' hsupp_h)
  have hint_g1 : Integrable g1 := hcont_g1.integrable_of_hasCompactSupport (hηc.mono' hsupp_g1)
  have hint_g3 : Integrable g3 := hcont_g3.integrable_of_hasCompactSupport (hηc.mono' hsupp_g3)
  -- pointwise lower bound (Legendre + bound + Young)
  have hpt : ∀ x, lam / 2 * g1 x - 2 * Lam ^ 2 / lam * g3 x ≤ h x := by
    intro x
    have hid : h x = η x ^ 2 * A (fderiv ℝ V x) (fderiv ℝ V x) +
        2 * η x * A (fderiv ℝ V x) ((fderiv ℝ η x).smulRight (V x - c)) := by
      simp only [hh, hζd x, map_add, map_smul, smul_eq_mul]
    rw [hid]
    have hc := hcoer (fderiv ℝ V x)
    have hb := hbdd (fderiv ℝ V x) ((fderiv ℝ η x).smulRight (V x - c))
    rw [ContinuousLinearMap.norm_smulRight_apply] at hb
    have hb' := (abs_le.mp hb).1
    set a := η x * ‖fderiv ℝ V x‖ with ha
    set b := ‖V x - c‖ * ‖fderiv ℝ η x‖ with hb_def
    have e1 : lam * a ^ 2 ≤ η x ^ 2 * A (fderiv ℝ V x) (fderiv ℝ V x) := by
      rw [ha, mul_pow]
      nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg (η x))]
    have e2 : -(2 * Lam * (a * b)) ≤
        2 * η x * A (fderiv ℝ V x) ((fderiv ℝ η x).smulRight (V x - c)) := by
      have h2η : 0 ≤ 2 * η x := by linarith [hη0 x]
      have := mul_le_mul_of_nonneg_left hb' h2η
      rw [ha, hb_def]
      linarith [this]
    have e3 : 2 * Lam * (a * b) ≤ lam / 2 * a ^ 2 + 2 * Lam ^ 2 / lam * b ^ 2 := by
      have key : lam / 2 * a ^ 2 + 2 * Lam ^ 2 / lam * b ^ 2 - 2 * Lam * (a * b) =
          (lam * a - 2 * Lam * b) ^ 2 / (2 * lam) := by
        field_simp
        ring
      have : 0 ≤ (lam * a - 2 * Lam * b) ^ 2 / (2 * lam) := by positivity
      linarith
    have hg1x : g1 x = a ^ 2 := by rw [hg1, ha, mul_pow]
    have hg3x : g3 x = b ^ 2 := by rw [hg3, hb_def, mul_pow]
    rw [hg1x, hg3x]
    linarith
  -- integrate and absorb
  have hint_lhs : Integrable (fun x => lam / 2 * g1 x - 2 * Lam ^ 2 / lam * g3 x) :=
    (hint_g1.const_mul _).sub (hint_g3.const_mul _)
  have hmono := integral_mono hint_lhs hint_h hpt
  rw [h0, integral_sub (hint_g1.const_mul _) (hint_g3.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  have key : ∫ x, g1 x ≤ 4 * Lam ^ 2 / lam ^ 2 * ∫ x, g3 x := by
    have h2 : lam / 2 * ∫ x, g1 x ≤ 2 * Lam ^ 2 / lam * ∫ x, g3 x := by linarith
    have hlam2 : 0 < lam / 2 := by positivity
    calc ∫ x, g1 x = (lam / 2)⁻¹ * (lam / 2 * ∫ x, g1 x) := by field_simp
      _ ≤ (lam / 2)⁻¹ * (2 * Lam ^ 2 / lam * ∫ x, g3 x) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hlam2.le)
      _ = 4 * Lam ^ 2 / lam ^ 2 * ∫ x, g3 x := by field_simp; ring
  have hg1n : 0 ≤ᵐ[volume] g1 := ae_of_all _ (fun x => by positivity)
  have hg3n : 0 ≤ᵐ[volume] g3 := ae_of_all _ (fun x => by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hint_g1 hg1n,
    ← ofReal_integral_eq_lintegral_ofReal hint_g3 hg3n, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal key
```

## Key steps

1. zeta := eta^2 (V - c) is admissible by test_function, so the integral of A[DV][D zeta] is 0, with the formula D zeta = eta^2 DV + 2 eta (V - c) (x) D eta
2. h = A[DV][D zeta], g1 = eta^2 ||DV||^2 and g3 = ||V - c||^2 ||D eta||^2 are continuous on U with tsupport in U, hence continuous, compactly supported and integrable
3. pointwise h = eta^2 A[DV][DV] + 2 eta A[DV][(V - c) (x) D eta] >= (lam/2) g1 - (2 Lam^2/lam) g3, by the Legendre condition, the bound and Young's inequality
4. integrate using the integral of h = 0 and absorb: integral of g1 <= (4 Lam^2/lam^2) integral of g3
5. pass to lower integrals: ofReal(integral of g) = lower integral of ofReal(g) for integrable g >= 0, and ofReal is multiplicative

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp workspace GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Contract.lean (byte-identical)`
- `grep -rli 'caccioppoli' <snapshot>/mathlib/Mathlib (0 files); grep -rli 'caccioppoli\|energy estimate\|cutoff\|cut-off' <snapshot>/mathlib/Mathlib/Analysis <snapshot>/mathlib/Mathlib/MeasureTheory <snapshot>/project (only project/GMT/Ch05/README.md)`
- `grep -n 'theorem\|lemma' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `grep -rn 'continuous_of_tsupport\|contDiff_of_tsupport\|of_tsupport_subset\|fderiv_of_notMem_tsupport\|support_fderiv_subset\|continuous_of_mulTSupport' <snapshot>/mathlib/Mathlib`
- `grep (pinned Mathlib) for contDiff_of_contDiffOn_union_of_isOpen, HasFDerivAt.norm_sq, HasFDerivAt.mul_const, HasDerivAt.comp_hasFDerivAt, innerSL_apply_norm, norm_smulRight_apply, ContDiffOn.continuousOn_fderiv_of_isOpen, Continuous.integrable_of_hasCompactSupport, ofReal_integral_eq_lintegral_ofReal, lintegral_const_mul', setLIntegral_le_lintegral`
- `python3 scan of run dag.json (lean_name, theorems, raw text) for the proposed names and for cutoff/bump/Caccioppoli nodes`
- `python3 gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch05.main_theorem') and child_modules(...) to generate NodeChallenge/NodeSolution files`
- `lake build GMT.Ch05.Submission; lake env lean Checks/{Elab,Assembly,Cutoff,TestFun,Energy,InstVerify,Sol_cutoff,Sol_test_function,Sol_energy_estimate,Sol_parent}.lean in scratch /tmp/cacc-decomp-zgZPXQ/proj (Lean v4.35.0-rc3, shared lake-packages-25730c7c)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`

The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Submission.lean is byte-identical to the snapshot Contract.lean.

The pinned Mathlib has no Caccioppoli or energy-estimate result: 'caccioppoli' has 0 matches in Mathlib/, and the only cutoff/Caccioppoli hit in Analysis, MeasureTheory or the project is the chapter README. The proof is assembled from these pinned tools:
- Cutoff profile: Real.smoothTransition (SmoothTransition.lean: one_of_one_le :161, zero_of_nonpos :168, contDiff :205).
- Cutoff gradient bound: HasFDerivAt.norm_sq (InnerProductSpace/Calculus.lean:211), HasFDerivAt.mul_const (FDeriv/Mul.lean:299), HasDerivAt.comp_hasFDerivAt (Deriv/Comp.lean:171) and innerSL_apply_norm (InnerProductSpace/LinearMap.lean:225).
- Test function: contDiff_of_contDiffOn_union_of_isOpen (ContDiff/Basic.lean:612), and fderiv_of_notMem_tsupport and support_fderiv_subset (FDeriv/Const.lean:375-381).
- Energy estimate: ContinuousOn.continuous_of_tsupport_subset (to_additive of Topology/Algebra/Support.lean:196), ContDiffOn.continuousOn_fderiv_of_isOpen (ContDiff/Defs.lean:916), Continuous.integrable_of_hasCompactSupport (Function/LocallyIntegrable.lean:622), ContinuousLinearMap.norm_smulRight_apply (Normed/Operator/Bilinear.lean:449) and ofReal_integral_eq_lintegral_ofReal (Integral/Bochner/Basic.lean:739).
- Parent assembly: lintegral_const_mul' (Lebesgue/Add.lean:420) and setLIntegral_le_lintegral (Lebesgue/Basic.lean:258).

dag.json contains accepted cutoffs exists_smooth_cutoff_half_ball_grad_le and aal_l1th_exists_cutoff. Each equals 1 on closedBall xi (rho/2), vanishes for dist >= rho, and has gradient at most 3/rho. They are not reused: with the fixed 1/2 ratio and vanishing only on a closed set, they cannot equal 1 on the open B_rho(y) while keeping tsupport inside the open B_{2rho}(y). A new cutoff child is therefore needed. None of the three proposed names occurs in dag.json.

In the replayed scope, bare `support` is RectifiableVarifold.support, so the proofs write Function.support.

Scratch-build Lean checks:
- All child types and the frozen parent type elaborate.
- The parent follows from the cutoff and energy_estimate types.
- energy_estimate follows from the test_function type.
- cutoff and test_function are proved outright.
- All four verifier-generated NodeSolution targets close by exact Submission.X, using only propext, Classical.choice and Quot.sound.
