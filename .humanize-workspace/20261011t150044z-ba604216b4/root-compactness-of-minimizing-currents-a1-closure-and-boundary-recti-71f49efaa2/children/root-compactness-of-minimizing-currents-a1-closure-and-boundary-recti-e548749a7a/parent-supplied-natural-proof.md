# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1.pairing_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1(a) and 1(c) of the parent proof (Fubini and translation invariance turn ∫ w g into ∫ ū(y)∫ φ(z)g(y + z) dz dy; then ∫φ = 1 and a second Fubini), stated for a general measurable set S and continuous compactly supported φ, g.
Notation: ū := 1_S·u (Set.indicator S u); w(x) := ∫_S u(y)φ(x − y) dy; unlabeled integrals are over ℝⁿ with Lebesgue measure.
1. (Preliminaries.) ū is integrable on ℝⁿ (integrable_indicator_iff; S measurable, u integrable on S). φ and g are continuous with compact support, hence integrable (Continuous.integrable_of_hasCompactSupport) and bounded: fix K_φ, K_g with |φ| ≤ K_φ and |g| ≤ K_g everywhere (Continuous.bounded_above_of_compact_support).
2. (Replacing S-integrals by integrals of ū.) Since 1_S(y)·u(y)·c(y) = ū(y)·c(y) for every function c and S is measurable (integral_indicator): w(x) = ∫ ū(y)φ(x − y) dy for every x, and ∫_S u(y)(g(y) − g(y + z)) dy = ∫ ū(y)(g(y) − g(y + z)) dy for every z. Moreover (u(x) − w(x))·g(x) = ū(x)g(x) − w(x)g(x) for every x: if x ∈ S then u(x) = ū(x); if x ∉ S then g(x) = 0 by hypothesis and both sides vanish.
3. (First Fubini.) Let F(x, y) := ū(y)·φ(x − y)·g(x) on ℝⁿ × ℝⁿ. F is a.e.-strongly measurable for the product measure ((x, y) ↦ ū(y) by AEStronglyMeasurable.comp_snd; (x, y) ↦ φ(x − y) and (x, y) ↦ g(x) are continuous), and |F(x, y)| ≤ K_φ·|g(x)|·|ū(y)|, which is integrable on the product (Integrable.mul_prod applied to |g| and |ū|). Hence F is integrable on ℝⁿ × ℝⁿ (Integrable.mono'). Consequently:
   (a) w(x)g(x) = ∫ F(x, y) dy for every x (integral_mul_const), and x ↦ w(x)g(x) is integrable (Integrable.integral_prod_left);
   (b) for every y, ∫ φ(x − y)g(x) dx = ∫ φ(z)g(z + y) dz, by translation invariance of Lebesgue measure applied to z ↦ φ(z)g(z + y) (integral_sub_right_eq_self, noting g(x − y + y) = g(x)); hence ∫ F(x, y) dx = ū(y)·∫ φ(z)g(z + y) dz (integral_const_mul), and y ↦ ū(y)·∫ φ(z)g(z + y) dz is integrable (Integrable.integral_prod_right together with this identity);
   (c) by Fubini (integral_integral_swap), ∫ w(x)g(x) dx = ∫∫ F(x, y) dy dx = ∫∫ F(x, y) dx dy = ∫ ū(y)(∫ φ(z)g(z + y) dz) dy.
4. (Inner identity.) For every y, z ↦ φ(z)g(y) and z ↦ φ(z)g(z + y) are integrable (φ integrable; g bounded and continuous), so ∫ φ(z)(g(y) − g(y + z)) dz = g(y)·∫φ − ∫ φ(z)g(z + y) dz = g(y) − ∫ φ(z)g(z + y) dz, using ∫φ = 1 and y + z = z + y.
5. (Second Fubini.) Let H(z, y) := φ(z)·(ū(y)·(g(y) − g(y + z))). H is a.e.-strongly measurable on the product (as in step 3), and |H(z, y)| ≤ 2K_g·|φ(z)|·|ū(y)| since |g(y) − g(y + z)| ≤ 2K_g; the right side is integrable on the product (Integrable.mul_prod), so H is integrable. By step 2, Fubini (integral_integral_swap), integral_const_mul and step 4:
   ∫ φ(z)(∫_S u(y)(g(y) − g(y + z)) dy) dz = ∫∫ H(z, y) dy dz = ∫∫ H(z, y) dz dy = ∫ ū(y)(∫ φ(z)(g(y) − g(y + z)) dz) dy = ∫ ū(y)(g(y) − ∫ φ(z)g(z + y) dz) dy.
6. (Assembly.) x ↦ ū(x)g(x) is integrable (ū integrable, g measurable and bounded: Integrable.mul_bdd). By step 2, 3(a) and 3(c), the left side equals ∫ ūg − ∫ wg = ∫ ūg − ∫ ū(y)(∫ φ(z)g(z + y) dz) dy. By step 5 and the integrability in 3(b) (integral_sub), the right side equals ∫ ū(y)g(y) dy − ∫ ū(y)(∫ φ(z)g(z + y) dz) dy. The two expressions coincide. ∎

Verified Lean realization (supplementary; compiled with `lake env lean` inside a copy of GMT/Ch07/Submission.lean at project b4d606db / Mathlib 25730c7c, inserted before `main_theorem`; no new warnings; axioms propext, Classical.choice, Quot.sound). It may be appended verbatim as the single leaf theorem:
```lean
theorem Submission.cbr_ci_pw_bv_pairing_identity : ∀ (n : ℕ) (S : Set (Euclid n)) (φ u g : Euclid n → ℝ), MeasurableSet S → Continuous φ → HasCompactSupport φ → ∫ y, φ y = 1 → IntegrableOn u S → Continuous g → HasCompactSupport g → (∀ x, x ∉ S → g x = 0) → ∫ x, (u x - ∫ y in S, u y * φ (x - y)) * g x = ∫ z, φ z * ∫ y in S, u y * (g y - g (y + z)) := by
  intro n S φ u g hS hφ hφc hφ1 hu hg hgc hgS
  set ub : Euclid n → ℝ := S.indicator u with hub
  have hubi : Integrable ub := (integrable_indicator_iff hS).2 hu
  obtain ⟨Kφ, hKφ⟩ := hφ.bounded_above_of_compact_support hφc
  obtain ⟨Kg, hKg⟩ := hg.bounded_above_of_compact_support hgc
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hw : ∀ x, ∫ y in S, u y * φ (x - y) = ∫ y, ub y * φ (x - y) := by
    intro x
    rw [← integral_indicator hS]
    congr 1; funext y
    simp only [hub, Set.indicator]; split_ifs <;> simp
  have hI : ∀ z, ∫ y in S, u y * (g y - g (y + z)) = ∫ y, ub y * (g y - g (y + z)) := by
    intro z
    rw [← integral_indicator hS]
    congr 1; funext y
    simp only [hub, Set.indicator]; split_ifs <;> simp
  have hL : ∀ x, (u x - ∫ y in S, u y * φ (x - y)) * g x
      = ub x * g x - (∫ y, ub y * φ (x - y)) * g x := by
    intro x
    rw [hw x, sub_mul]
    congr 1
    by_cases hx : x ∈ S
    · simp [hub, Set.indicator_of_mem hx]
    · simp [hgS x hx]
  simp_rw [hL, hI]
  -- integrability facts
  have hubg : Integrable (fun x => ub x * g x) :=
    hubi.mul_bdd hg.aestronglyMeasurable (Eventually.of_forall hKg)
  -- Fubini 1
  have hFi : Integrable (uncurry fun x y => ub y * φ (x - y) * g x) (volume.prod volume) := by
    have hdom : Integrable (fun p : Euclid n × Euclid n => Kφ * (‖g p.1‖ * ‖ub p.2‖))
        (volume.prod volume) := (hgi.norm.mul_prod hubi.norm).const_mul Kφ
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hubi.aestronglyMeasurable.comp_snd).mul
        ((hφ.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable)).mul
        ((hg.comp continuous_fst).aestronglyMeasurable)
    · simp only [uncurry, norm_mul]
      have h1 := hKφ (p.1 - p.2)
      have h2 := norm_nonneg (ub p.2)
      have h3 := norm_nonneg (g p.1)
      calc ‖ub p.2‖ * ‖φ (p.1 - p.2)‖ * ‖g p.1‖ = ‖φ (p.1 - p.2)‖ * (‖g p.1‖ * ‖ub p.2‖) := by ring
        _ ≤ Kφ * (‖g p.1‖ * ‖ub p.2‖) := mul_le_mul_of_nonneg_right h1 (mul_nonneg h3 h2)
  have hwg : ∀ x, (∫ y, ub y * φ (x - y)) * g x = ∫ y, ub y * φ (x - y) * g x := fun x =>
    (integral_mul_const _ _).symm
  have hwgi : Integrable (fun x => (∫ y, ub y * φ (x - y)) * g x) := by
    simp_rw [hwg]; exact hFi.integral_prod_left
  have key1 : ∫ x, (∫ y, ub y * φ (x - y)) * g x = ∫ y, ub y * ∫ z, φ z * g (z + y) := by
    simp_rw [hwg]
    rw [integral_integral_swap hFi]
    congr 1; funext y
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    congr 1
    have := integral_sub_right_eq_self (μ := (volume : Measure (Euclid n))) (fun z => φ z * g (z + y)) y
    simpa [sub_add_cancel] using this
  -- Fubini 2
  have hHi : Integrable (uncurry fun z y => φ z * (ub y * (g y - g (y + z)))) (volume.prod volume) := by
    have hdom : Integrable (fun p : Euclid n × Euclid n => (2 * Kg) * (‖φ p.1‖ * ‖ub p.2‖))
        (volume.prod volume) := (hφi.norm.mul_prod hubi.norm).const_mul (2 * Kg)
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (hφ.comp continuous_fst).aestronglyMeasurable.mul
        ((hubi.aestronglyMeasurable.comp_snd).mul
          ((hg.comp continuous_snd).sub (hg.comp (continuous_snd.add continuous_fst))).aestronglyMeasurable)
    · simp only [uncurry, norm_mul]
      have h1 : ‖g p.2 - g (p.2 + p.1)‖ ≤ 2 * Kg := by
        calc ‖g p.2 - g (p.2 + p.1)‖ ≤ ‖g p.2‖ + ‖g (p.2 + p.1)‖ := norm_sub_le _ _
          _ ≤ Kg + Kg := add_le_add (hKg _) (hKg _)
          _ = 2 * Kg := by ring
      have h2 := norm_nonneg (ub p.2)
      have h3 := norm_nonneg (φ p.1)
      calc ‖φ p.1‖ * (‖ub p.2‖ * ‖g p.2 - g (p.2 + p.1)‖)
          = ‖g p.2 - g (p.2 + p.1)‖ * (‖φ p.1‖ * ‖ub p.2‖) := by ring
        _ ≤ (2 * Kg) * (‖φ p.1‖ * ‖ub p.2‖) := mul_le_mul_of_nonneg_right h1 (mul_nonneg h3 h2)
  have hinner : ∀ y, ∫ z, φ z * (g y - g (y + z)) = g y - ∫ z, φ z * g (z + y) := by
    intro y
    have hc : Integrable (fun z => φ z * g y) := hφi.mul_const _
    have hs : Integrable (fun z => φ z * g (z + y)) :=
      hφi.mul_bdd (hg.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (Eventually.of_forall fun z => hKg _)
    simp_rw [mul_sub]
    rw [integral_sub hc (by simpa [add_comm] using hs), integral_mul_const, hφ1, one_mul]
    simp_rw [add_comm y]
  have key2 : ∫ z, φ z * ∫ y, ub y * (g y - g (y + z)) = ∫ y, ub y * (g y - ∫ z, φ z * g (z + y)) := by
    simp_rw [← integral_const_mul]
    rw [integral_integral_swap hHi]
    congr 1; funext y
    have : ∀ z, φ z * (ub y * (g y - g (y + z))) = ub y * (φ z * (g y - g (y + z))) := fun z => by ring
    simp_rw [this]
    rw [integral_const_mul, hinner y]
  have hconv : Integrable (fun y => ub y * ∫ z, φ z * g (z + y)) := by
    refine (hFi.integral_prod_right).congr (Eventually.of_forall fun y => ?_)
    simp only [uncurry]
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    congr 1
    have := integral_sub_right_eq_self (μ := (volume : Measure (Euclid n))) (fun z => φ z * g (z + y)) y
    simpa [sub_add_cancel] using this
  rw [integral_sub hubg hwgi, key1, key2]
  simp_rw [mul_sub]
  rw [integral_sub hubg hconv]
```

## Key steps

1. Replace u by ū = 1_S u: w(x) = ∫ ū(y)φ(x − y) dy, the S-integrals become ℝⁿ-integrals, and (u − w)g = ūg − wg because g = 0 off S.
2. First Fubini for F(x, y) = ū(y)φ(x − y)g(x) (dominated by K_φ|g(x)||ū(y)|) plus translation invariance: ∫ wg = ∫ ū(y)∫φ(z)g(z + y) dz dy, with the needed integrabilities.
3. ∫φ = 1 gives ∫ φ(z)(g(y) − g(y + z)) dz = g(y) − ∫ φ(z)g(z + y) dz.
4. Second Fubini for H(z, y) = φ(z)ū(y)(g(y) − g(y + z)) (dominated by 2K_g|φ(z)||ū(y)|) turns the right side into ∫ ū(y)(g(y) − ∫φ(z)g(z + y) dz) dy = ∫ ūg − ∫ wg.

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
