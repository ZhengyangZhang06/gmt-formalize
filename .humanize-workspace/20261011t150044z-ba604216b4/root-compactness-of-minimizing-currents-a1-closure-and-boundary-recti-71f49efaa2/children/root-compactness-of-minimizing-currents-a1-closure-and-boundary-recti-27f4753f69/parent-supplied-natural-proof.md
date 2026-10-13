# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1.smooth_test_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 (Claim A, parts (a)–(e)) of the parent proof; the Fubini/translation computation of 1(a), 1(c) is the sibling pairing_identity and the FTC-plus-variation estimate of 1(b)–(d) is the sibling translate_test.
1. (φ has compact support; g vanishes off B_{2R}(0).) tsupport φ is closed and contained in B_s(0) ⊆ closedBall(0, s), which is compact, so tsupport φ is compact: φ has compact support. φ is continuous (it is C^∞) and therefore integrable. Since s > 0 and 2s < R we have s < R, so R + s ≤ 2R and tsupport g ⊆ B_{R+s}(0) ⊆ B_{2R}(0); thus g(x) = 0 for every x ∉ B_{2R}(0) (such x is not in tsupport g). (R > 0 also follows from s > 0 and 2s < R and is not used separately; smoothness of φ is used only through continuity.)
2. (Fubini identity.) Apply pairing_identity with S := B_{2R}(0) (an open, hence measurable, set), φ (continuous, compactly supported, ∫φ = 1), u (integrable on S) and g (continuous, compactly supported, zero off S):
   ∫ (u(x) − w(x))·g(x) dx = ∫ φ(z)·I(z) dz,  where I(z) := ∫_{B_{2R}(0)} u(y)(g(y) − g(y + z)) dy.
3. (Pointwise bound: |φ(z)I(z)| ≤ φ(z)·sV for every z.) If φ(z) = 0 both sides are 0. Otherwise z ∈ support φ ⊆ tsupport φ ⊆ B_s(0), so ‖z‖ < s. From 2s < R we get ‖z‖ < s < R − s, hence R + s < 2R − ‖z‖ and tsupport g ⊆ B_{R+s}(0) ⊆ B_{2R−‖z‖}(0). Apply translate_test with ρ := 2R, V, M := 1, u, g and v := z; its hypotheses hold: u is integrable on B_{2R}(0); the variation hypothesis of the present theorem is literally the one required there with ρ = 2R; g is smooth with compact support; tsupport g ⊆ B_{2R−‖z‖}(0); |g| ≤ 1. It gives |∫_{B_{2R}(0)} u(y)(g(y + z) − g(y)) dy| ≤ V‖z‖·1. Since u(y)(g(y) − g(y + z)) = −u(y)(g(y + z) − g(y)), I(z) is the negative of that integral, so |I(z)| ≤ V‖z‖ ≤ Vs = sV (V ≥ 0 and ‖z‖ ≤ s). As φ(z) ≥ 0, |φ(z)I(z)| = φ(z)|I(z)| ≤ φ(z)·sV.
4. (Integration.) z ↦ φ(z)·sV is integrable (φ integrable), so by step 3 and the norm bound for integrals (norm_integral_le_of_norm_le), |∫ φ(z)I(z) dz| ≤ ∫ φ(z)·sV dz = (∫φ)·sV = sV. By step 2 this is |∫ (u(x) − w(x))g(x) dx| ≤ sV. ∎

Verified Lean realization (supplementary; compiled with `lake env lean` inside a copy of GMT/Ch07/Submission.lean at project b4d606db / Mathlib 25730c7c, inserted before `main_theorem`; no new warnings; axioms propext, Classical.choice, Quot.sound). It may be appended verbatim as the single leaf theorem:
```lean
theorem Submission.cbr_ci_pw_bv_smooth_test_bound : ∀ (n : ℕ) (R s V : ℝ) (φ u g : Euclid n → ℝ), 0 < R → 0 < s → 2 * s < R → 0 ≤ V → ContDiff ℝ (⊤ : ℕ∞) φ → (∀ y, 0 ≤ φ y) → tsupport φ ⊆ ball 0 s → ∫ y, φ y = 1 → IntegrableOn u (ball 0 (2 * R)) → (∀ (f : Euclid n → ℝ) (z : Euclid n) (M : ℝ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ ball 0 (2 * R) → (∀ y, |f y| ≤ M) → |∫ y in ball 0 (2 * R), u y * fderiv ℝ f y z| ≤ V * ‖z‖ * M) → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ ball 0 (R + s) → (∀ x, |g x| ≤ 1) → |∫ x, (u x - ∫ y in ball 0 (2 * R), u y * φ (x - y)) * g x| ≤ s * V := by
  intro n R s V φ u g hR hs h2s hV hφ hφ0 hφs hφ1 hu hvar hg hgc hgs hgb
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall (0 : Euclid n) s).of_isClosed_subset (isClosed_tsupport φ)
      (hφs.trans ball_subset_closedBall)
  have hgS : ∀ x, x ∉ ball (0 : Euclid n) (2 * R) → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (ball_subset_ball (by linarith) (hgs hx'))
  rw [Submission.cbr_ci_pw_bv_pairing_identity n (ball 0 (2 * R)) φ u g measurableSet_ball
    hφ.continuous hφc hφ1 hu hg.continuous hgc hgS]
  have hbound : ∀ z, ‖φ z * ∫ y in ball (0 : Euclid n) (2 * R), u y * (g y - g (y + z))‖ ≤ φ z * (s * V) := by
    intro z
    by_cases hz : φ z = 0
    · simp [hz]
    have hzs : ‖z‖ < s := mem_ball_zero_iff.1 (hφs (subset_tsupport φ hz))
    have hT := Submission.cbr_ci_pw_bv_translate_test n (2 * R) V 1 u g z hu hvar hg hgc
      (hgs.trans (ball_subset_ball (by linarith))) hgb
    have hneg : ∫ y in ball (0 : Euclid n) (2 * R), u y * (g y - g (y + z)) =
        -∫ y in ball (0 : Euclid n) (2 * R), u y * (g (y + z) - g y) := by
      rw [← integral_neg]; congr 1; funext y; ring
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hφ0 z), hneg, abs_neg]
    refine mul_le_mul_of_nonneg_left (hT.trans ?_) (hφ0 z)
    nlinarith [norm_nonneg z]
  have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
  calc |∫ z, φ z * ∫ y in ball (0 : Euclid n) (2 * R), u y * (g y - g (y + z))|
      = ‖∫ z, φ z * ∫ y in ball (0 : Euclid n) (2 * R), u y * (g y - g (y + z))‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, φ z * (s * V) := norm_integral_le_of_norm_le (hφi.mul_const _) (Eventually.of_forall hbound)
    _ = s * V := by rw [integral_mul_const, hφ1, one_mul]
```

## Key steps

1. φ has compact support (tsupport φ ⊆ closedBall(0, s)); g = 0 off B_{2R}(0) because R + s ≤ 2R.
2. pairing_identity with S = B_{2R}(0): ∫(u − w)g = ∫ φ(z)I(z) dz, I(z) = ∫_{B_{2R}} u(y)(g(y) − g(y + z)) dy.
3. If φ(z) ≠ 0 then ‖z‖ < s < R − s, so tsupport g ⊆ B_{2R−‖z‖}(0) and translate_test (ρ = 2R, M = 1, v = z) gives |I(z)| ≤ V‖z‖ ≤ sV.
4. |∫ φ I| ≤ ∫ φ·sV = sV.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical; workspace HEAD b4d606db)`
- `rg -n 'cbr_ci_pw_bv|mollif|convolution|ae_tendsto_average|l1_duality' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT (no match)`
- `grep -rn in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/ for: 'theorem tendsto_integral_smul_of_tendsto_average_norm_sub' (MeasureTheory/Integral/Average.lean:835), 'theorem ae_tendsto_average_norm_sub' (MeasureTheory/Covering/DensityTheorem.lean:150; Covering/Differentiation.lean:837), 'HasCompactSupport.contDiff_convolution_right' (Analysis/Calculus/ContDiff/Convolution.lean:420), 'intervalIntegral_integral_swap' (MeasureTheory/Integral/Prod.lean:483), 'theorem integral_integral_swap' (Integral/Prod.lean:478), 'theorem Integrable.mul_prod' (Integral/Prod.lean:297), 'AEStronglyMeasurable.comp_snd' (Integral/Prod.lean:135), 'lemma Integrable.comp_snd' (Integral/Prod.lean:285), 'theorem continuous_of_dominated' (Integral/Bochner/Basic.lean:476), 'theorem integral_comp_inv_smul_of_nonneg' (Measure/Haar/NormedSpace.lean:129), "theorem addHaar_real_closedBall'" (Measure/Lebesgue/EqHaar.lean:479; IsUnifLocDoublingMeasure instance for Haar measures at EqHaar.lean:551), 'theorem fderiv_comp_add_right' (Analysis/Calculus/FDeriv/Add.lean:855), 'theorem norm_integral_le_of_norm_le_const' (IntervalIntegral/Basic.lean:769), 'theorem tendsto_integral_of_dominated_convergence' (Integral/DominatedConvergence.lean:57), 'theorem integral_eq_sub_of_hasDerivAt' (IntervalIntegral/FundThmCalculus.lean:1148), 'theorem integral_pos_iff_support_of_nonneg' (Bochner/Basic.lean:790), 'theorem support_eq' (Analysis/Calculus/BumpFunction/Basic.lean:151), 'theorem integrableOn_iff_integrable_of_support_subset' (Integral/IntegrableOn.lean:462), 'Measure.integrableOn_of_bounded' (Integral/IntegrableOn.lean:716), 'theorem setIntegral_indicator' (Integral/Bochner/Set.lean:194), 'theorem norm_integral_le_of_norm_le' (Bochner/Basic.lean:985)`
- `python3 -I scans of /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json: no lean_name with prefix cbr_ci_pw_bv_ except the selected cbr_ci_pw_bv_mollifier_estimate (rechecked immediately before returning); keyword scan (mollif|dualit|Lebesgue point|convolution|translation) of accepted nodes; frozen types of codim1_rdo_dg_bvc_l1_le_of_tests, codim1_rdo_dg_bvc_translate_test_le, codim1_rdo_dg_bvc_translation_l1_le, codim1_rdo_dg_bvc_mollify_l1_le, dorag_ha_weyl_ae_tendsto, dorag_ha_weyl_radial_mollifier, dgcr_stc_exists_normalized_mollifier compared with the needed obligations (none identical)`
- `git show f471edcde (dorag_ha_weyl_ae_tendsto), 376e5f482 (dgcr_stc_exists_normalized_mollifier), bfd6db12d (codim1_rdo_dg_bvc_mollify_l1_le), 499364f8f (codim1_rdo_dg_bvc_l1_le_of_tests), e2ca2a5c7 (codim1_rdo_dg_bvc_translate_test_le) as proof templates`
- `lake env lean /tmp/bvdec/T0.lean and T1.lean (#check after import GMT.Ch07.Submission: all cited lemmas reachable; Real.sign and measurable_sign NOT reachable, so the sign function is an if-then-else; IsUnifLocDoublingMeasure (volume : Measure (Euclid n)) synthesizes for every n)`
- `lake env lean /tmp/bvdec/Stmts.lean (six child types elaborate; parent assembly compiles against them), /tmp/bvdec/AsmAD.lean (smooth_test_bound from pairing_identity + translate_test; l1_duality from smooth_ae_approx), /tmp/bvdec/C.lean, T.lean, A1.lean, M.lean (complete leaf proofs), /tmp/bvdec/SubmissionCopy.lean (all six children plus the parent inserted before main_theorem in a copy of GMT/Ch07/Submission.lean: only the inherited main_theorem sorry warning; #print axioms Submission.cbr_ci_pw_bv_mollifier_estimate = [propext, Classical.choice, Quot.sound])`
- `python3 -I validate_lean_statement (verifier/lean_contract.py) on the six child types (all pass, normalized text unchanged); regex check that each frozen type is byte-identical to the compiled declaration`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose: max_depth, _existing_lean_name_problem, _solve_children, _reference_use_problem), leaf_verification.py check_source_delta (one appended theorem, no helper declarations or set_option), prompts.py DECOMPOSITION_AUDIT`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Doubling.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-71f49efaa2/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-71f49efaa2/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-951a399d2e/decomposition-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/bvdec/Stmts.lean`
- `/tmp/bvdec/AsmAD.lean`
- `/tmp/bvdec/SubmissionCopy.lean`

The pinned snapshot (local-project; project b4d606db, Mathlib 25730c7c) has Contract.lean byte-identical to the workspace Contract.lean and Submission.lean, and the project contains no mollification, convolution, duality or Lebesgue-point declaration (rg: no match), so the children rely only on pinned Mathlib. Every Mathlib lemma named in the child proofs was located in the snapshot (paths and lines above) and is reachable from import GMT.Ch07.Submission; Real.sign is not imported and is avoided. No DAG node uses a cbr_ci_pw_bv_* name other than the selected one, so the six names are fresh. Related accepted DAG theorems have different frozen types (codim1_rdo_dg_bvc_l1_le_of_tests needs a bounded measurable integrand and C¹ tests, but u − w is unbounded and only smooth tests are controlled; dorag_ha_weyl_ae_tendsto needs 0 < n), so nothing is reused and the children have no cross-branch dependencies; their accepted proofs were used only as templates. All six child types elaborate in the contract scope and pass validate_lean_statement. Complete Lean proofs of all six, plus the parent proof from mollify_continuous, smooth_test_bound and l1_duality, compile inside a copy of GMT/Ch07/Submission.lean with no new warnings. The parent depends only on propext, Classical.choice and Quot.sound.
