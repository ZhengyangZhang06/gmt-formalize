# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.boundary_layer_estimate-a1.smooth_annulus_estimate-a1`
- Child DAG node: `root.harmonic_approximation-a1.boundary_layer_estimate-a1.smooth_annulus_estimate-a1.annulus_kernel_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and role. This is step 5 ("Function term and kernel bound") of the supplied proof of ble_smooth_annulus_estimate. The supplied proof uses it with F = |φ|^2 and τ = 1 - sqrt(1 - r)/2 > 1/2. Here it is stated, with the same proof, for every measurable F and every τ ≥ 1/2. The parent applies it with F(y) = ‖φ y‖ₑ^2, which is measurable because φ is continuous.

Sibling used: dilation_formula (Submission.ble_sac_lintegral_comp_smul). For t > 0, every G : R^n → [0, ∞] and every set E ⊆ R^n:
∫_E G(t x) dx = ENNReal.ofReal((t^n)⁻¹) ∫_{{y : t⁻¹ y ∈ E}} G(y) dy.

Notation. R^n is Rn n = EuclideanSpace ℝ (Fin n), with Lebesgue measure. λ is Lebesgue measure on ℝ. B_ρ := ball(0, ρ) is the open ball, and A := B_s \ B_{rs} = {x : r s ≤ |x| < s}. All integrals are lintegrals with values in [0, ∞]. "∫_{[τ,1]} … dt" is the lintegral over Icc τ 1 with respect to λ. The constant 2^{n+1}(1 - r) enters via ENNReal.ofReal.

Hypotheses: n ∈ ℕ; F : R^n → [0, ∞] measurable; r, s, τ ∈ ℝ with 1/2 ≤ r < 1, s > 0 and τ ≥ 1/2.
Claim: ∫_{[τ,1]} ∫_A F(t x) dx dt ≤ 2^{n+1} (1 - r) ∫_{B_s} F(y) dy.

Proof.

1. The kernel. Let S := {(y, t) ∈ R^n × ℝ : r s t ≤ |y| and |y| < s t}.
   - S is measurable. The maps (y, t) ↦ r s t, |y| and s t are continuous, hence measurable. The first condition is a non-strict inequality between measurable functions and the second a strict one (measurableSet_le, measurableSet_lt). S is their intersection.
   - Put K(y, t) := ENNReal.ofReal((t^n)⁻¹) · 1_S(y, t). It is measurable on R^n × ℝ: t ↦ (t^n)⁻¹ is measurable, ENNReal.ofReal is measurable, and the indicator of a measurable set is measurable.

2. Change of variables for fixed t. Let t ∈ [τ, 1]; then t ≥ 1/2 > 0. By dilation_formula with G = F and E = A,
∫_A F(t x) dx = ENNReal.ofReal((t^n)⁻¹) ∫_{A_t} F(y) dy, where A_t := {y : t⁻¹ y ∈ A}.
Since t > 0, |t⁻¹ y| = |y|/t, so
y ∈ A_t ⟺ r s ≤ |y|/t < s ⟺ r s t ≤ |y| < s t ⟺ (y, t) ∈ S.
In particular A_t is the section {y : (y, t) ∈ S} of S, which is measurable (measurable_prodMk_right). Write the set integral as the integral of an indicator (lintegral_indicator) and move the finite constant ENNReal.ofReal((t^n)⁻¹) inside (lintegral_const_mul'). Pointwise, ENNReal.ofReal((t^n)⁻¹) · 1_{A_t}(y) F(y) = F(y) K(y, t). Hence
∫_A F(t x) dx = ∫_{R^n} F(y) K(y, t) dy for every t ∈ [τ, 1].   (A)

3. Tonelli. Integrate (A) over t ∈ [τ, 1] (setLIntegral_congr_fun, [τ, 1] measurable). The function (t, y) ↦ F(y) K(y, t) is measurable on ℝ × R^n, since F and K are. The measures λ restricted to [τ, 1] and Lebesgue measure on R^n are s-finite. So the order of integration may be swapped (lintegral_lintegral_swap). The factor F(y) does not depend on t and comes out of the t-integral (lintegral_const_mul, as K(y, ·) is measurable):
∫_{[τ,1]} ∫_A F(t x) dx dt = ∫_{R^n} ∫_{[τ,1]} F(y) K(y, t) dt dy = ∫_{R^n} F(y) k(y) dy, where k(y) := ∫_{[τ,1]} K(y, t) dt.

4. Kernel bound: k(y) ≤ 2^{n+1} (1 - r) · 1_{B_s}(y) for every y ∈ R^n.
(a) Case |y| ≥ s. For t ∈ [τ, 1] we have s t ≤ s ≤ |y|, since s > 0 and t ≤ 1. So |y| < s t fails, (y, t) ∉ S, and K(y, t) = 0. Hence k(y) = 0, which is the bound.
(b) Case |y| < s. Let t ∈ [τ, 1].
   - If (y, t) ∈ S: |y| < s t gives t > |y|/s, and r s t ≤ |y| gives t ≤ |y|/(r s), since r, s > 0. So t ∈ (|y|/s, |y|/(r s)]. Moreover t ≥ τ ≥ 1/2, so t⁻¹ ≤ 2 and (t^n)⁻¹ = (t⁻¹)^n ≤ 2^n.
   - If (y, t) ∉ S, then K(y, t) = 0.
In both cases K(y, t) ≤ 2^n · 1_{(|y|/s, |y|/(r s)]}(t). Integrating over [τ, 1], then enlarging the domain of the nonnegative integrand to ℝ (setLIntegral_le_lintegral), and using lintegral_indicator_const with Real.volume_Ioc:
k(y) ≤ ∫_{[τ,1]} 2^n 1_{(|y|/s, |y|/(r s)]}(t) dt ≤ ∫_ℝ 2^n 1_{(|y|/s, |y|/(r s)]}(t) dt = 2^n · ENNReal.ofReal(|y|/(r s) - |y|/s).
Finally |y|/(r s) - |y|/s = |y| (1 - r)/(r s) ≤ 2 (1 - r). Indeed |y| (1 - r) ≤ s (1 - r), because |y| < s and 1 - r ≥ 0. And s (1 - r) ≤ 2 (1 - r) r s, because s (1 - r)(2 r - 1) ≥ 0. Hence k(y) ≤ 2^n · 2 (1 - r) = 2^{n+1} (1 - r). (For y = 0 the interval (0, 0] is empty and k(0) = 0.)

5. Conclusion. Combine step 3, the kernel bound of step 4 (monotonicity of the lintegral), lintegral_indicator (B_s is open, hence measurable) and lintegral_mul_const (F is measurable):
∫_{[τ,1]} ∫_A F(t x) dx dt = ∫ F(y) k(y) dy ≤ ∫ F(y) · 2^{n+1}(1 - r) · 1_{B_s}(y) dy = ∫_{B_s} F(y) · 2^{n+1}(1 - r) dy = 2^{n+1}(1 - r) ∫_{B_s} F(y) dy. QED.

Formalization note. The following proof of this exact frozen statement compiles against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c) after `import GMT.Ch05.Submission`, inside `namespace GMT.Ch05` / `namespace Submission` with the contract's `open`s. It needs the sibling Submission.ble_sac_lintegral_comp_smul declared before it, and no extra imports. `#print axioms` lists only propext, Classical.choice and Quot.sound. A copy is in GMT/Scratch/ble_sac/ble_sac_annulus_dilation_avg_le.lean.txt. In this Mathlib `Set.mem_diff`/`Set.mem_setOf_eq` are deprecated in favor of `Set.mem_sdiff`/`Set.mem_ofPred_eq`, and `mem_sdiff` must be written in full as `Set.mem_sdiff` because `open Filter` makes it ambiguous.

```lean
theorem ble_sac_annulus_dilation_avg_le : ∀ (n : ℕ) (F : Rn n → ℝ≥0∞), Measurable F → ∀ r s τ : ℝ, 1 / 2 ≤ r → r < 1 → 0 < s → 1 / 2 ≤ τ → ∫⁻ t in Icc τ 1, ∫⁻ x in ball (0 : Rn n) s \ ball 0 (r * s), F (t • x) ≤ ENNReal.ofReal (2 ^ (n + 1) * (1 - r)) * ∫⁻ y in ball (0 : Rn n) s, F y := by
  intro n F hF r s τ hr1 hr2 hs hτ
  have hr0 : 0 < r := by linarith
  set S : Set (Rn n × ℝ) := {p | r * s * p.2 ≤ ‖p.1‖ ∧ ‖p.1‖ < s * p.2} with hS_def
  have hSm : MeasurableSet S := by
    have h1 : Measurable fun p : Rn n × ℝ => r * s * p.2 := measurable_const.mul measurable_snd
    have h2 : Measurable fun p : Rn n × ℝ => ‖p.1‖ := measurable_fst.norm
    have h3 : Measurable fun p : Rn n × ℝ => s * p.2 := measurable_const.mul measurable_snd
    exact (measurableSet_le h1 h2).inter (measurableSet_lt h2 h3)
  set K : Rn n × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal ((p.2 ^ n)⁻¹) * S.indicator 1 p with hK_def
  have hKm : Measurable K :=
    (ENNReal.measurable_ofReal.comp ((measurable_snd.pow_const n).inv)).mul
      (measurable_one.indicator hSm)
  -- Natural-proof step 2: change of variables for each fixed t, giving (A).
  have step1 : ∀ t ∈ Icc τ 1, ∫⁻ x in ball (0 : Rn n) s \ ball 0 (r * s), F (t • x) =
      ∫⁻ y, F y * K (y, t) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [ble_sac_lintegral_comp_smul n F _ t ht0]
    have hpre : (fun y => t⁻¹ • y) ⁻¹' (ball (0 : Rn n) s \ ball 0 (r * s)) =
        {y | (y, t) ∈ S} := by
      ext y
      simp only [mem_preimage, Set.mem_sdiff, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos ht0, not_lt, Set.mem_ofPred_eq, hS_def]
      constructor
      · rintro ⟨h1, h2⟩
        constructor
        · rw [le_inv_mul_iff₀ ht0] at h2; linarith
        · rw [inv_mul_lt_iff₀ ht0] at h1; linarith
      · rintro ⟨h1, h2⟩
        constructor
        · rw [inv_mul_lt_iff₀ ht0]; linarith
        · rw [le_inv_mul_iff₀ ht0]; linarith
    have hSt : MeasurableSet {y : Rn n | (y, t) ∈ S} := measurable_prodMk_right hSm
    rw [hpre, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator hSt]
    congr 1
    funext y
    by_cases hy : (y, t) ∈ S
    · rw [indicator_of_mem (show y ∈ {y : Rn n | (y, t) ∈ S} from hy)]
      simp only [hK_def, indicator_of_mem hy, Pi.one_apply, mul_one]
      ring
    · rw [indicator_of_notMem (show y ∉ {y : Rn n | (y, t) ∈ S} from hy)]
      simp only [hK_def, indicator_of_notMem hy, mul_zero]
  -- Natural-proof step 4: the kernel bound.
  have kernel : ∀ y : Rn n, ∫⁻ t in Icc τ 1, K (y, t) ≤
      (ball (0 : Rn n) s).indicator (fun _ => ENNReal.ofReal (2 ^ (n + 1) * (1 - r))) y := by
    intro y
    by_cases hy : y ∈ ball (0 : Rn n) s
    · rw [indicator_of_mem hy]
      rw [mem_ball_zero_iff] at hy
      have hbound : ∀ t ∈ Icc τ 1, K (y, t) ≤
          (Ioc (‖y‖ / s) (‖y‖ / (r * s))).indicator (fun _ => ENNReal.ofReal (2 ^ n)) t := by
        intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        by_cases hS : (y, t) ∈ S
        · have hmem : t ∈ Ioc (‖y‖ / s) (‖y‖ / (r * s)) := by
            constructor
            · rw [div_lt_iff₀ hs]; linarith [hS.2]
            · rw [le_div_iff₀ (by positivity)]; linarith [hS.1]
          rw [indicator_of_mem hmem]
          simp only [hK_def, indicator_of_mem hS, Pi.one_apply, mul_one]
          apply ENNReal.ofReal_le_ofReal
          rw [← inv_pow]
          apply pow_le_pow_left₀ (by positivity)
          rw [inv_le_comm₀ ht0 (by norm_num)]
          linarith [ht.1]
        · simp [hK_def, indicator_of_notMem hS]
      have hlen : ‖y‖ / (r * s) - ‖y‖ / s ≤ 2 * (1 - r) := by
        rw [show ‖y‖ / (r * s) - ‖y‖ / s = ‖y‖ * (1 - r) / (r * s) by field_simp]
        rw [div_le_iff₀ (by positivity)]
        have h1 : ‖y‖ * (1 - r) ≤ s * (1 - r) := mul_le_mul_of_nonneg_right hy.le (by linarith)
        have h2 : s * (1 - r) ≤ 2 * (1 - r) * (r * s) := by
          nlinarith [mul_nonneg (mul_nonneg hs.le (by linarith : (0:ℝ) ≤ 1 - r))
            (by linarith : (0:ℝ) ≤ 2 * r - 1)]
        linarith
      calc ∫⁻ t in Icc τ 1, K (y, t)
            ≤ ∫⁻ t in Icc τ 1, (Ioc (‖y‖ / s) (‖y‖ / (r * s))).indicator
                (fun _ => ENNReal.ofReal (2 ^ n)) t := setLIntegral_mono' measurableSet_Icc hbound
        _ ≤ ∫⁻ t, (Ioc (‖y‖ / s) (‖y‖ / (r * s))).indicator (fun _ => ENNReal.ofReal (2 ^ n)) t :=
            setLIntegral_le_lintegral _ _
        _ = ENNReal.ofReal (2 ^ n) * ENNReal.ofReal (‖y‖ / (r * s) - ‖y‖ / s) := by
            rw [lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc]
        _ ≤ ENNReal.ofReal (2 ^ n) * ENNReal.ofReal (2 * (1 - r)) := by
            gcongr
        _ = ENNReal.ofReal (2 ^ (n + 1) * (1 - r)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
    · rw [indicator_of_notMem hy]
      have hz : ∀ t ∈ Icc τ 1, K (y, t) = 0 := by
        intro t ht
        have hS : (y, t) ∉ S := by
          rintro ⟨_, h2⟩
          rw [mem_ball_zero_iff, not_lt] at hy
          nlinarith [ht.2]
        simp only [hK_def, indicator_of_notMem hS, mul_zero]
      rw [setLIntegral_congr_fun measurableSet_Icc hz, lintegral_zero]
  -- Natural-proof steps 3 and 5: Tonelli, then integrate the kernel bound.
  have hmeas : AEMeasurable (Function.uncurry fun (t : ℝ) (y : Rn n) => F y * K (y, t))
      ((volume.restrict (Icc τ 1)).prod volume) :=
    ((hF.comp measurable_snd).mul (hKm.comp (measurable_snd.prodMk measurable_fst))).aemeasurable
  calc ∫⁻ t in Icc τ 1, ∫⁻ x in ball (0 : Rn n) s \ ball 0 (r * s), F (t • x)
        = ∫⁻ t in Icc τ 1, ∫⁻ y, F y * K (y, t) := setLIntegral_congr_fun measurableSet_Icc step1
    _ = ∫⁻ y, ∫⁻ t in Icc τ 1, F y * K (y, t) := lintegral_lintegral_swap hmeas
    _ = ∫⁻ y, F y * ∫⁻ t in Icc τ 1, K (y, t) := by
        congr 1
        funext y
        exact lintegral_const_mul _ (hKm.comp measurable_prodMk_left)
    _ ≤ ∫⁻ y, F y * (ball (0 : Rn n) s).indicator
          (fun _ => ENNReal.ofReal (2 ^ (n + 1) * (1 - r))) y :=
        lintegral_mono (fun y => by gcongr; exact kernel y)
    _ = ∫⁻ y in ball (0 : Rn n) s, F y * ENNReal.ofReal (2 ^ (n + 1) * (1 - r)) := by
        rw [← lintegral_indicator measurableSet_ball]
        congr 1
        funext y
        by_cases hy : y ∈ ball (0 : Rn n) s
        · simp [indicator_of_mem hy]
        · simp [indicator_of_notMem hy]
    _ = _ := by rw [lintegral_mul_const _ hF, mul_comm]
```

## Key steps

1. Borel kernel set S = {(y,t) : rst ≤ |y| < st} and measurable weight K(y,t) = t^{-n} 1_S(y,t)
2. for t ∈ [τ,1], the dilation formula and t⁻¹y ∈ A ⟺ (y,t) ∈ S give ∫_A F(tx) dx = ∫ F(y) K(y,t) dy
3. Tonelli: ∫_{[τ,1]} ∫_A F(tx) dx dt = ∫ F(y) k(y) dy with k(y) = ∫_{[τ,1]} K(y,t) dt
4. kernel bound k(y) ≤ 2^{n+1}(1 - r) 1_{B_s}(y): k = 0 for |y| ≥ s; for |y| < s the t-support lies in (|y|/s, |y|/(rs)], of length ≤ 2(1 - r), and t^{-n} ≤ 2^n
5. integrate the kernel bound against F to get 2^{n+1}(1 - r) ∫_{B_s} F

## Reference use

### local-project

Queries:
- `cmp /tmp/sac-decomp/proj/GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Submission.lean (SAME_AS_SNAPSHOT); sha256sum Contract.lean Submission.lean (both c966f51efddb5a68ce15ef2a2a322fd9df0ca69da4626c7acef05b05d1691e12)`
- `rg -n "theorem (setLIntegral_mono|setLIntegral_mono'|lintegral_const_mul'|lintegral_const_mul|setLIntegral_const|lintegral_mono_set|lintegral_add_left|lintegral_add_right|setLIntegral_congr_fun)\b" <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/`
- `rg -n "theorem (lintegral_lintegral_swap|Measurable.lintegral_prod_right'|Measurable.lintegral_prod_right|lintegral_prod_swap)\b" <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `rg -n "theorem map_addHaar_smul|theorem addHaar_smul\b|theorem addHaar_preimage_smul" .../Measure/Lebesgue/EqHaar.lean; rg -n "theorem volume_Icc|theorem volume_Ioc" .../Measure/Lebesgue/Basic.lean`
- `rg -n "theorem (lintegral_comp_smul|setLIntegral_comp_smul|lintegral_comp_smul_deriv|lintegral_comp_mul_left)" <snapshot>/mathlib/Mathlib/MeasureTheory/  (no match)`
- `grep -rn "mul_le_mul_iff_right|ofReal_ofNat|ofReal_eq_zero" <snapshot>/mathlib/Mathlib/Basic/ENNReal/*.lean  (Data/ENNReal/*.lean are 5-line deprecated stubs re-exporting Mathlib.Basic.ENNReal.*)`
- `grep -n for enorm_integral_le_lintegral_enorm, integral_eq_sub_of_hasDerivAt, inner_gradient_left, toDual_symm_apply, lintegral_mul_le_Lp_mul_Lq, HolderConjugate two_two, add_sq_le, two_mul_le_add_sq, enorm_le_iff_norm_le, ofReal_norm, norm_inner_le_norm, ENNReal.rpow_two/rpow_natCast/rpow_mul, ENNReal.continuous_pow, ContDiff.continuous_fderiv, Continuous.enorm, integral_of_le, norm_integral_le_integral_norm, integral_mono_interval`
- `grep -n for lintegral_indicator, lintegral_indicator_const, setLIntegral_le_lintegral, lintegral_smul_measure, lintegral_mul_const, restrict_map, lintegral_map, finrank_euclideanSpace_fin, measurable_prodMk_right, restrict_smul`
- `python scan of dag.json lean_name fields and lean_statements plus all nodes/*/* files for 'ble_sac_' (none); grep -rl ble_sac GMT/ and <snapshot>/project (none); git grep -l -e ble_sac_ across all 614 refs, *.lean (none)`
- `lake env lean Check/{Types,All,Three,Ray,Kern,Full,SubShaped,Statements,FromPaste,SplitAllFinal,SubShapedFinal}.lean in scratch project /tmp/sac-decomp/proj (frozen Submission compiled to an olean); #print axioms on all four declarations`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/Real/ConjExponents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/Ring/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-boundary-layer-estimate-a1-smooth-annu-922079b7be/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-boundary-layer-estimate-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/ble_sac/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/ble_sac/ble_sac_split_all.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/ble_sac/check_submission_shaped.lean.txt`
- `/tmp/sac-decomp/proj/Check/Full.lean`
- `/tmp/sac-decomp/proj/Check/SubShaped.lean`

Pinned snapshot: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The frozen Submission.lean is byte-identical in the snapshot, the workspace and the scratch project, with SHA-256 c966f51e….

No match in the snapshot (gaps the children fill):
- There is no lintegral dilation lemma: lintegral_comp_smul and setLIntegral_comp_smul do not exist under MeasureTheory. Child dilation_formula provides it from Measure.map_addHaar_smul (Lebesgue/EqHaar.lean:336), finrank_euclideanSpace_fin (PiL2.lean:205), MeasurableEmbedding.restrict_map and lintegral_map, Measure.restrict_smul (Restrict.lean:193) and lintegral_smul_measure (Lebesgue/Basic.lean:418).
- There is no ray, Cauchy–Schwarz or annulus-kernel lemma either.

Usable lemmas, all verified to exist and used in the compiled proofs:
- Set integrals: setLIntegral_mono and setLIntegral_mono' (Lebesgue/Basic.lean:246,254), setLIntegral_const (:121), lintegral_mono_set (:98), setLIntegral_congr_fun (:298), setLIntegral_le_lintegral (:258), lintegral_indicator (:510), lintegral_indicator_const (:541).
- Linearity: lintegral_add_left and lintegral_add_right (Lebesgue/Add.lean:316,339), lintegral_const_mul and lintegral_const_mul' (:381,420), lintegral_mul_const (:433).
- Tonelli: Measurable.lintegral_prod_right' and lintegral_lintegral_swap (Measure/Prod.lean:123,1071).
- Lebesgue measure on ℝ: Real.volume_Icc and volume_Ioc (Lebesgue/Basic.lean:86,110).
- Integral bounds: ENNReal.lintegral_mul_le_Lp_mul_Lq (MeanInequalities.lean:202), Real.HolderConjugate.two_two (Basic/Real/ConjExponents.lean:137), enorm_integral_le_lintegral_enorm (Bochner/Basic.lean:333).
- Calculus: intervalIntegral.integral_eq_sub_of_hasDerivAt (FundThmCalculus.lean:1148), intervalIntegral.integral_of_le (IntervalIntegral/Basic.lean:677), inner_gradient_left (Gradient/Basic.lean:292), ContDiff.continuous_fderiv (ContDiff/Defs.lean:1271; takes n ≠ 0).
- Norms and inner products: enorm_le_iff_norm_le (Normed/Group/Basic.lean:399), norm_inner_le_norm (InnerProductSpace/Basic.lean:455), add_sq_le (Algebra/Order/Ring/Basic.lean:113).
- ENNReal: ENNReal.mul_le_mul_iff_right (Basic/ENNReal/Operations.lean:75), ENNReal.ofReal_ofNat (Basic/ENNReal/Basic.lean:512), ENNReal.ofReal_eq_zero (Basic/ENNReal/Real.lean:181), ENNReal.continuous_pow (Topology/Instances/ENNReal/Lemmas.lean:406), ENNReal.rpow_two, rpow_natCast and rpow_mul (Pow/NNReal.lean:701,686,669).

API drift found: Data/ENNReal/* are deprecated stubs pointing to Mathlib.Basic.ENNReal.*; Set.mem_diff, Set.mem_setOf_eq and Set.diff_subset are deprecated in favor of Set.mem_sdiff, Set.mem_ofPred_eq and Set.sdiff_subset; zero_le takes implicit arguments.

Lean results (scratch project, frozen Submission olean):
- The three child types and the parent's frozen type elaborate in namespace GMT.Ch05.Submission.
- All four declarations are fully proved. #print axioms gives [propext, Classical.choice, Quot.sound] for each.
- A Submission-shaped copy with `example : <frozen type> := Submission.X` checks compiles. Its only sorry is the contract's main_theorem.
- The evidence is saved in the git-ignored GMT/Scratch/ble_sac/ with SHA256SUMS.

The proposed names are not reserved anywhere. An independent reviewer agent re-ran all checks and accepted.
