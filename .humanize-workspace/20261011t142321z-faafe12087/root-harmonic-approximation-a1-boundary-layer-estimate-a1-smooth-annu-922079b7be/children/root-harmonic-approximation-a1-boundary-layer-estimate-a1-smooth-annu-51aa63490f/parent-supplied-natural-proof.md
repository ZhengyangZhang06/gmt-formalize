# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.boundary_layer_estimate-a1.smooth_annulus_estimate-a1`
- Child DAG node: `root.harmonic_approximation-a1.boundary_layer_estimate-a1.smooth_annulus_estimate-a1.ray_inequality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and role. This is step 2 ("Pointwise ray inequality") of the supplied proof of ble_smooth_annulus_estimate, namely its inequality (2.2). The supplied proof uses it with τ = 1 - sqrt(1 - r)/2 ∈ (1/2, 1) and x in the annulus. Here it is stated, with the same proof, for every τ ≤ 1 and every x with |x| ≤ 1. The parent applies it at each x ∈ B_s \ B_{rs} (where |x| < s ≤ 1) in its step 3.

Notation. R^n is Rn n = EuclideanSpace ℝ (Fin n). λ is Lebesgue measure on ℝ, and λ([τ, 1]) = ENNReal.ofReal (1 - τ) (Real.volume_Icc). |v| is the norm and |v|^2 means ‖v‖ₑ ^ 2. ∇φ := gradient φ and Dφ := fderiv ℝ φ. Every "∫_{[τ,1]} … dt" is a lintegral over Icc τ 1 with respect to λ. Put
G := ∫_{[τ,1]} |∇φ(σx)|^2 dσ and m := ∫_{[τ,1]} |∇φ(σx)| dσ, both in [0, ∞].

Hypotheses: n ∈ ℕ; φ : R^n → ℝ with ContDiff ℝ 1 φ; x ∈ R^n with |x| ≤ 1; τ ∈ ℝ with τ ≤ 1.
Claim: (1 - τ) |φ(x)|^2 ≤ 2 ∫_{[τ,1]} |φ(t x)|^2 dt + 2 (1 - τ)^2 G. Here (1 - τ) and (1 - τ)^2 enter via ENNReal.ofReal.

Proof.

1. Regularity. Since φ is C^1, it is differentiable (ContDiff.differentiable with 1 ≠ 0), and Dφ is continuous (ContDiff.continuous_fderiv with 1 ≠ 0). Also ∇φ = (InnerProductSpace.toDual ℝ (Rn n)).symm ∘ Dφ, and the inverse of toDual is a linear isometry, so ∇φ is continuous. Finally ⟨∇φ(y), v⟩ = Dφ(y) v for all y and v (inner_gradient_left).

2. Derivative along the ray. Let u(σ) := φ(σ x) for σ ∈ ℝ. The map σ ↦ σ x has derivative x. By the chain rule (HasFDerivAt.comp_hasDerivAt) and step 1, u has derivative u'(σ) = Dφ(σ x) x = ⟨∇φ(σ x), x⟩ at every σ. The function σ ↦ ⟨∇φ(σ x), x⟩ is continuous by step 1, hence interval integrable on every bounded interval.

3. Cauchy–Schwarz on [τ, 1]: m^2 ≤ (1 - τ) G. Use Hölder's inequality for [0, ∞]-valued functions (ENNReal.lintegral_mul_le_Lp_mul_Lq) for the measure λ restricted to [τ, 1]. Take the conjugate exponents p = q = 2 (Real.HolderConjugate.two_two), f ≡ 1 and g(σ) := |∇φ(σ x)|. Both are a.e.-measurable, since g is continuous. This gives
m = ∫_{[τ,1]} 1 · g ≤ (∫_{[τ,1]} 1^2)^{1/2} (∫_{[τ,1]} g^2)^{1/2} = (1 - τ)^{1/2} G^{1/2},
because ∫_{[τ,1]} 1 = λ([τ, 1]) = ENNReal.ofReal (1 - τ) and g^{(2:ℝ)} = g^2 (ENNReal.rpow_two). Squaring is monotone on [0, ∞]. Moreover (A^{1/2} B^{1/2})^2 = A B for A, B ∈ [0, ∞] (mul_pow, ENNReal.rpow_natCast, ENNReal.rpow_mul). Hence m^2 ≤ (1 - τ) G.

4. An elementary inequality: (p + q)^2 ≤ 2 p^2 + 2 q^2 for all p, q ∈ [0, ∞]. If p = ∞ or q = ∞, the right side is ∞. Otherwise p, q ∈ [0, ∞), and (p + q)^2 ≤ 2 (p^2 + q^2) because 2 p q ≤ p^2 + q^2 (add_sq_le in ℝ≥0, then cast).

5. The pointwise inequality (2.1). Fix t ∈ [τ, 1]. The fundamental theorem of calculus on [t, 1] (intervalIntegral.integral_eq_sub_of_hasDerivAt, using step 2) gives
φ(x) - φ(t x) = ∫_t^1 ⟨∇φ(σ x), x⟩ dσ = ∫_{(t,1]} ⟨∇φ(σ x), x⟩ dσ,
where the second form uses t ≤ 1 (intervalIntegral.integral_of_le). We bound this in three steps:
   - The extended norm of a Bochner integral is at most the lintegral of the extended norm (enorm_integral_le_lintegral_enorm).
   - By Cauchy–Schwarz in R^n and |x| ≤ 1, |⟨∇φ(σ x), x⟩| ≤ |∇φ(σ x)| |x| ≤ |∇φ(σ x)| (norm_inner_le_norm, enorm_le_iff_norm_le).
   - Since τ ≤ t, we have (t, 1] ⊆ [τ, 1], and the integrand is nonnegative (lintegral_mono_set).
Together these give
|φ(x) - φ(t x)| ≤ ∫_{(t,1]} |∇φ(σ x)| dσ ≤ m.
The triangle inequality gives |φ(x)| ≤ |φ(t x)| + |φ(x) - φ(t x)|. Combining this with step 4, the display above and step 3:
|φ(x)|^2 ≤ (|φ(t x)| + |φ(x) - φ(t x)|)^2 ≤ 2 |φ(t x)|^2 + 2 |φ(x) - φ(t x)|^2 ≤ 2 |φ(t x)|^2 + 2 m^2 ≤ 2 |φ(t x)|^2 + 2 (1 - τ) G.   (2.1)

6. Integration in t. The left side of (2.1) does not depend on t, so ∫_{[τ,1]} |φ(x)|^2 dt = (1 - τ) |φ(x)|^2 (setLIntegral_const). Integrate (2.1) over t ∈ [τ, 1]; [τ, 1] is measurable, so setLIntegral_mono' applies. The constant term 2 (1 - τ) G splits off (lintegral_add_right; a constant is measurable), and the factor 2 comes out (lintegral_const_mul', 2 ≠ ∞). This gives
(1 - τ) |φ(x)|^2 ≤ 2 ∫_{[τ,1]} |φ(t x)|^2 dt + 2 (1 - τ) G · λ([τ, 1]) = 2 ∫_{[τ,1]} |φ(t x)|^2 dt + 2 (1 - τ)^2 G.
The last step uses ENNReal.ofReal (1 - τ) · ENNReal.ofReal (1 - τ) = ENNReal.ofReal ((1 - τ)^2) (ENNReal.ofReal_pow, valid since 1 - τ ≥ 0). This is the claim. QED.

Formalization note. The following proof of this exact frozen statement compiles against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c) after `import GMT.Ch05.Submission`, inside `namespace GMT.Ch05` / `namespace Submission` with the contract's `open`s. No extra imports, helpers or siblings are needed. `#print axioms` lists only propext, Classical.choice and Quot.sound. A copy is in GMT/Scratch/ble_sac/ble_sac_ray_sq_bound.lean.txt. Note the parentheses around the first lintegral in the statement: without them, `2 * ∫⁻ t in s, f t + c` would parse as `2 * ∫⁻ t in s, (f t + c)`.

```lean
theorem ble_sac_ray_sq_bound : ∀ (n : ℕ) (φ : Rn n → ℝ), ContDiff ℝ 1 φ → ∀ (x : Rn n), ‖x‖ ≤ 1 → ∀ τ : ℝ, τ ≤ 1 → ENNReal.ofReal (1 - τ) * ‖φ x‖ₑ ^ 2 ≤ 2 * (∫⁻ t in Icc τ 1, ‖φ (t • x)‖ₑ ^ 2) + 2 * ENNReal.ofReal ((1 - τ) ^ 2) * ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ ^ 2 := by
  intro n φ hφ x hx τ hτ
  have hgc : Continuous (gradient φ) :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hderiv : ∀ σ : ℝ, HasDerivAt (fun σ : ℝ => φ (σ • x)) (inner ℝ (gradient φ (σ • x)) x) σ := by
    intro σ
    have h1 : HasFDerivAt φ (fderiv ℝ φ (σ • x)) (σ • x) := (hdiff (σ • x)).hasFDerivAt
    have h2 : HasDerivAt (fun σ : ℝ => σ • x) x σ := by
      simpa using (hasDerivAt_id σ).smul_const x
    have h3 := h1.comp_hasDerivAt σ h2
    rw [inner_gradient_left]
    exact h3
  have hray : Continuous (fun σ : ℝ => σ • x) := continuous_id.smul continuous_const
  have hcont_inner : Continuous (fun σ : ℝ => inner ℝ (gradient φ (σ • x)) x) :=
    (hgc.comp hray).inner continuous_const
  set G : ℝ≥0∞ := ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ ^ 2 with hG_def
  set m : ℝ≥0∞ := ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ with hm_def
  -- Cauchy–Schwarz on [τ, 1].
  have hcs : m ^ 2 ≤ ENNReal.ofReal (1 - τ) * G := by
    have hmeas : AEMeasurable (fun σ : ℝ => ‖gradient φ (σ • x)‖ₑ) (volume.restrict (Icc τ 1)) :=
      (hgc.comp hray).enorm.aemeasurable
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Icc τ 1))
      Real.HolderConjugate.two_two (aemeasurable_const (b := (1 : ℝ≥0∞))) hmeas
    simp only [Pi.mul_apply, one_mul, setLIntegral_const, Real.volume_Icc,
      ENNReal.rpow_two, one_pow] at h
    calc m ^ 2 ≤ ((ENNReal.ofReal (1 - τ)) ^ (1 / 2 : ℝ) * G ^ (1 / 2 : ℝ)) ^ 2 := by
          gcongr
      _ = ENNReal.ofReal (1 - τ) * G := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num
  have hsq : ∀ p q : ℝ≥0∞, (p + q) ^ 2 ≤ 2 * p ^ 2 + 2 * q ^ 2 := by
    intro p q
    rcases eq_or_ne p ⊤ with hp | hp
    · simp [hp]
    rcases eq_or_ne q ⊤ with hq | hq
    · simp [hq]
    lift p to ℝ≥0 using hp
    lift q to ℝ≥0 using hq
    have h := add_sq_le (a := p) (b := q)
    rw [mul_add] at h
    exact_mod_cast h
  -- Pointwise inequality (2.1) for t ∈ [τ, 1].
  have hpt : ∀ t ∈ Icc τ 1, ‖φ x‖ₑ ^ 2 ≤ 2 * ‖φ (t • x)‖ₑ ^ 2 + 2 * (ENNReal.ofReal (1 - τ) * G) := by
    intro t ht
    have hftc : ∫ σ in t..1, inner ℝ (gradient φ (σ • x)) x = φ x - φ (t • x) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hderiv σ)
        (hcont_inner.intervalIntegrable t 1)]
      simp
    have hb : ‖φ x - φ (t • x)‖ₑ ≤ m := by
      rw [← hftc, intervalIntegral.integral_of_le ht.2]
      calc ‖∫ σ in Ioc t 1, inner ℝ (gradient φ (σ • x)) x‖ₑ
            ≤ ∫⁻ σ in Ioc t 1, ‖inner ℝ (gradient φ (σ • x)) x‖ₑ :=
              enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ σ in Ioc t 1, ‖gradient φ (σ • x)‖ₑ := by
            apply lintegral_mono
            intro σ
            rw [enorm_le_iff_norm_le]
            calc ‖inner ℝ (gradient φ (σ • x)) x‖ ≤ ‖gradient φ (σ • x)‖ * ‖x‖ :=
                  norm_inner_le_norm _ _
              _ ≤ ‖gradient φ (σ • x)‖ * 1 := by gcongr
              _ = _ := mul_one _
        _ ≤ m := lintegral_mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc ht.1 le_rfl))
    have htri : ‖φ x‖ₑ ≤ ‖φ (t • x)‖ₑ + ‖φ x - φ (t • x)‖ₑ := by
      calc ‖φ x‖ₑ = ‖φ (t • x) + (φ x - φ (t • x))‖ₑ := by ring_nf
        _ ≤ _ := enorm_add_le _ _
    calc ‖φ x‖ₑ ^ 2 ≤ (‖φ (t • x)‖ₑ + ‖φ x - φ (t • x)‖ₑ) ^ 2 := by gcongr
      _ ≤ 2 * ‖φ (t • x)‖ₑ ^ 2 + 2 * ‖φ x - φ (t • x)‖ₑ ^ 2 := hsq _ _
      _ ≤ 2 * ‖φ (t • x)‖ₑ ^ 2 + 2 * m ^ 2 := by gcongr
      _ ≤ _ := by gcongr
  -- Integrate (2.1) over t ∈ [τ, 1].
  calc ENNReal.ofReal (1 - τ) * ‖φ x‖ₑ ^ 2 = ∫⁻ t in Icc τ 1, ‖φ x‖ₑ ^ 2 := by
        rw [setLIntegral_const, Real.volume_Icc, mul_comm]
    _ ≤ ∫⁻ t in Icc τ 1, (2 * ‖φ (t • x)‖ₑ ^ 2 + 2 * (ENNReal.ofReal (1 - τ) * G)) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = 2 * (∫⁻ t in Icc τ 1, ‖φ (t • x)‖ₑ ^ 2) +
          2 * (ENNReal.ofReal (1 - τ) * G) * ENNReal.ofReal (1 - τ) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by simp),
          setLIntegral_const, Real.volume_Icc]
    _ = _ := by
        rw [ENNReal.ofReal_pow (by linarith)]
        ring
```

## Key steps

1. ∇φ is continuous with ⟨∇φ(y), v⟩ = Dφ(y)v; the chain rule gives d/dσ φ(σx) = ⟨∇φ(σx), x⟩
2. Cauchy–Schwarz (Hölder with p = q = 2 and f ≡ 1): (∫_{[τ,1]} |∇φ(σx)|)^2 ≤ (1 - τ) ∫_{[τ,1]} |∇φ(σx)|^2
3. FTC on [t,1] together with |⟨∇φ(σx), x⟩| ≤ |∇φ(σx)| and (t,1] ⊆ [τ,1] gives |φ(x) - φ(tx)| ≤ ∫_{[τ,1]} |∇φ(σx)| for t ∈ [τ,1]
4. (p + q)^2 ≤ 2p^2 + 2q^2 in [0, ∞] gives (2.1): |φ(x)|^2 ≤ 2|φ(tx)|^2 + 2(1 - τ) ∫_{[τ,1]} |∇φ(σx)|^2
5. integrate (2.1) over t ∈ [τ,1], a set of Lebesgue measure 1 - τ

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
