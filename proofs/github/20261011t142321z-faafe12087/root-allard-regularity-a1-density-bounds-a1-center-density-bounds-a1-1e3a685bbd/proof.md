# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.density_bounds-a1`
- Child DAG node: `root.allard_regularity-a1.density_bounds-a1.center_density_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 6-8 of the parent proof (derivation of (P.i), (P.ii), (P.iii) from (M) at the centre y, including the limits r -> R_y and t -> 0), with the data of (M) at y taken as hypotheses. In the parent, mu = V.weight, R = (1 - 3 delta) rho, Lambda = delta/kappa, M = (1 + delta) omega_n rho^n, omega = omega_n and g(x) = |x - y - p_x(x - y)|^2/|x - y|^(n+2).

Notation: B_r := closedBall y r, m(r) := mu(B_r).toReal, Phi(r) := F(r) (r^n)^(-1) m(r) + F(r) - 1.

1. Preliminaries. For r in (0, R), (H1) gives mu(B_r) <= ofReal M < infinity, hence mu(B_r) = ofReal(m(r)) and 0 <= m(r) <= M (as M >= 0). By (H2), F(r) >= e^(-Lambda) > 0, F(r) <= e^Lambda, F(r) - 1 <= Lambda and 1 - F(r) <= Lambda.

2. Upper bound for Phi. For r in (0, R), Phi(r) <= e^Lambda r^(-n) M + Lambda, because 0 <= F(r) <= e^Lambda, 0 <= r^(-n) m(r) <= r^(-n) M and F(r) - 1 <= Lambda. Fix s in (0, R). For every r in [s, R), (H3) gives Phi(s) <= Phi(r) <= e^Lambda r^(-n) M + Lambda. The map r -> e^Lambda r^(-n) M + Lambda is continuous at R > 0, so letting r -> R from the left:
 (dagger) Phi(s) <= e^Lambda (M/R^n) + Lambda.

3. (i). By (dagger) and 1 - F(s) <= Lambda, F(s) s^(-n) m(s) = Phi(s) + 1 - F(s) <= e^Lambda (M/R^n) + 2 Lambda. The right side is >= 0 and F(s) >= e^(-Lambda) > 0, hence s^(-n) m(s) <= (e^Lambda (M/R^n) + 2 Lambda)/F(s) <= e^Lambda (e^Lambda (M/R^n) + 2 Lambda) = e^(2 Lambda)(M/R^n) + 2 e^Lambda Lambda. Multiplying by s^n > 0 gives m(s) <= (e^(2 Lambda)(M/R^n) + 2 e^Lambda Lambda) s^n, so mu(B_s) = ofReal(m(s)) <= ofReal((e^(2 Lambda)(M/R^n) + 2 e^Lambda Lambda) s^n) by monotonicity of ofReal.

4. (ii). Assume (H4). Then omega <= Phi(s) = F(s) s^(-n) m(s) + F(s) - 1 <= F(s) s^(-n) m(s) + Lambda, so omega - Lambda <= F(s) s^(-n) m(s) <= e^Lambda s^(-n) m(s) (as s^(-n) m(s) >= 0 and F(s) <= e^Lambda). Multiplying by e^(-Lambda) > 0 and by s^n > 0: e^(-Lambda)(omega - Lambda) s^n <= m(s). Hence ofReal(e^(-Lambda)(omega - Lambda) s^n) <= ofReal(m(s)) = mu(B_s).

5. (iii). Assume (H4). For t in (0, s), (H3) applied to the pair (t, s) (0 < t <= s < R), (H4) at t, (dagger) and e^Lambda > 0 give
 integral^-_{B_s minus B_t} ofReal(g) dmu <= ofReal(e^Lambda (Phi(s) - Phi(t))) <= ofReal(e^Lambda (e^Lambda (M/R^n) + Lambda - omega)) =: Q,
 because Phi(s) - Phi(t) <= Phi(s) - omega <= e^Lambda (M/R^n) + Lambda - omega and ofReal is monotone. The sets A_k := B_s minus B_(s/(k+2)) (k = 0, 1, 2, ...) increase with k, and their union is B_s minus {y}: if x in B_s and x != y then |x - y| > s/(k+2) for k large, while y lies in no A_k. For an increasing (hence directed) countable family of sets, the lower integral over the union equals the supremum of the lower integrals over the members, for an arbitrary [0, infinity]-valued integrand (Mathlib: setLIntegral_iUnion_of_directed); as s/(k+2) is in (0, s), each of these is <= Q, so integral^-_{B_s minus {y}} ofReal(g) dmu <= Q. Finally B_s is contained in (B_s minus {y}) union {y}, so by monotonicity and subadditivity of the lower integral in the domain (lintegral_union_le), and since integral^-_{{y}} ofReal(g) dmu = ofReal(g(y)) mu({y}) = 0 * mu({y}) = 0 (g(y) = 0, and 0 * infinity = 0 in [0, infinity]), we get integral^-_{B_s} ofReal(g) dmu <= Q.

6. Steps 3-5 prove (i), and under (H4) also (ii) and (iii), for every s in (0, R).

Appendix (non-normative implementation aid; the numbered argument above is the proof). The following Lean 4 declaration was compiled in the namespace/opens of the frozen contract (import GMT.Ch05.Submission; open MeasureTheory Metric Set Filter Topology; open scoped ENNReal NNReal; namespace GMT.Ch05; open RectifiableVarifold; namespace Submission) with Lean v4.35.0-rc3 and Mathlib 25730c7c. It adds no other declaration. #print axioms: propext, Classical.choice, Quot.sound. It follows steps 1-5 (ge_of_tendsto along nhdsWithin R (Iio R) for (dagger), setLIntegral_iUnion_of_directed and lintegral_union_le for (iii)).

```lean
theorem allard52_center_density_bounds : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (g : Amb n ℓ → ℝ) (F : ℝ → ℝ) (y : Amb n ℓ) (ω R Λ M : ℝ), 0 < R → 0 < Λ → 0 ≤ M → g y = 0 → (∀ r ∈ Ioo 0 R, μ (closedBall y r) ≤ ENNReal.ofReal M) → (∀ r ∈ Ioo 0 R, Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Λ) → (∀ s r : ℝ, 0 < s → s ≤ r → r < R → F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1 ≤ F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1 ∧ ∫⁻ x in closedBall y r \ closedBall y s, ENNReal.ofReal (g x) ∂μ ≤ ENNReal.ofReal (Real.exp Λ * ((F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) - (F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1)))) → ∀ s : ℝ, 0 < s → s < R → μ (closedBall y s) ≤ ENNReal.ofReal ((Real.exp (2 * Λ) * (M / R ^ n) + 2 * Real.exp Λ * Λ) * s ^ n) ∧ ((∀ t ∈ Ioo 0 R, ω ≤ F t * (t ^ n)⁻¹ * (μ (closedBall y t)).toReal + F t - 1) → ENNReal.ofReal (Real.exp (-Λ) * (ω - Λ) * s ^ n) ≤ μ (closedBall y s) ∧ ∫⁻ x in closedBall y s, ENNReal.ofReal (g x) ∂μ ≤ ENNReal.ofReal (Real.exp Λ * (Real.exp Λ * (M / R ^ n) + Λ - ω))) := by
  intro n ℓ μ g F y ω R Λ M hR hΛ hM hgy hμ hF hΦ s hs hsR
  have hexp_pos : 0 < Real.exp Λ := Real.exp_pos Λ
  have hexpn_pos : 0 < Real.exp (-Λ) := Real.exp_pos (-Λ)
  have hfin : ∀ r ∈ Ioo 0 R, μ (closedBall y r) ≠ ∞ := fun r hr =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hμ r hr)
  have hmM : ∀ r ∈ Ioo 0 R, (μ (closedBall y r)).toReal ≤ M := fun r hr =>
    ENNReal.toReal_le_of_le_ofReal hM (hμ r hr)
  have hm0 : ∀ r, 0 ≤ (μ (closedBall y r)).toReal := fun r => ENNReal.toReal_nonneg
  -- Step 2: upper bound for Φ r
  have hΦup : ∀ r ∈ Ioo 0 R, F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1
      ≤ Real.exp Λ * (r ^ n)⁻¹ * M + Λ := by
    intro r hr
    obtain ⟨hF1, hF2, hF3⟩ := hF r hr
    have hFpos : 0 < F r := lt_of_lt_of_le hexpn_pos hF1
    have hrn : 0 < (r ^ n)⁻¹ := inv_pos.mpr (pow_pos hr.1 n)
    have hmr := hmM r hr
    have hm0r := hm0 r
    have h1 : F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal ≤ Real.exp Λ * (r ^ n)⁻¹ * M := by
      calc F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal
          ≤ Real.exp Λ * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal := by
            apply mul_le_mul_of_nonneg_right _ hm0r
            exact mul_le_mul_of_nonneg_right hF2 hrn.le
        _ ≤ Real.exp Λ * (r ^ n)⁻¹ * M := by
            apply mul_le_mul_of_nonneg_left hmr
            exact (mul_pos hexp_pos hrn).le
    have h2 : F r - 1 ≤ Λ := le_trans (le_abs_self _) hF3
    linarith
  -- Step 2 (†): letting r → R⁻
  have hdagger : ∀ s ∈ Ioo 0 R, F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1
      ≤ Real.exp Λ * (M / R ^ n) + Λ := by
    intro s hs
    have hRn : R ^ n ≠ 0 := pow_ne_zero _ hR.ne'
    have hlim0 : Tendsto (fun r : ℝ => Real.exp Λ * (r ^ n)⁻¹ * M + Λ) (𝓝 R)
        (𝓝 (Real.exp Λ * (R ^ n)⁻¹ * M + Λ)) :=
      ((tendsto_const_nhds.mul (((continuous_pow n).tendsto R).inv₀ hRn)).mul
        tendsto_const_nhds).add tendsto_const_nhds
    have hlim : Tendsto (fun r : ℝ => Real.exp Λ * (r ^ n)⁻¹ * M + Λ) (𝓝[<] R)
        (𝓝 (Real.exp Λ * (M / R ^ n) + Λ)) := by
      rw [show Real.exp Λ * (M / R ^ n) + Λ = Real.exp Λ * (R ^ n)⁻¹ * M + Λ by
        rw [div_eq_mul_inv]; ring]
      exact tendsto_nhdsWithin_of_tendsto_nhds hlim0
    apply ge_of_tendsto hlim
    have hmem : Ioo s R ∈ 𝓝[<] R := Ioo_mem_nhdsLT hs.2
    filter_upwards [hmem] with r hr
    have hr' : r ∈ Ioo 0 R := ⟨lt_trans hs.1 hr.1, hr.2⟩
    exact le_trans (hΦ s r hs.1 hr.1.le hr.2).1 (hΦup r hr')
  have hsI : s ∈ Ioo 0 R := ⟨hs, hsR⟩
  obtain ⟨hF1, hF2, hF3⟩ := hF s hsI
  have hFpos : 0 < F s := lt_of_lt_of_le hexpn_pos hF1
  have hsn : 0 < s ^ n := pow_pos hs n
  have hx0 : 0 ≤ (s ^ n)⁻¹ * (μ (closedBall y s)).toReal :=
    mul_nonneg (inv_pos.mpr hsn).le (hm0 s)
  have hcancel : ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal) * s ^ n
      = (μ (closedBall y s)).toReal := by
    field_simp
  have hd := hdagger s hsI
  refine ⟨?_, ?_⟩
  · -- (i)
    have h1 : 1 - F s ≤ Λ := by
      have := neg_abs_le (F s - 1)
      linarith
    have hA : F s * ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal)
        ≤ Real.exp Λ * (M / R ^ n) + 2 * Λ := by
      have : F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal
          = F s * ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal) := by ring
      linarith
    have hB : (s ^ n)⁻¹ * (μ (closedBall y s)).toReal
        ≤ Real.exp Λ * (Real.exp Λ * (M / R ^ n) + 2 * Λ) := by
      have hC : Real.exp (-Λ) * ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal)
          ≤ Real.exp Λ * (M / R ^ n) + 2 * Λ :=
        le_trans (mul_le_mul_of_nonneg_right hF1 hx0) hA
      have hexpinv : Real.exp Λ * Real.exp (-Λ) = 1 := by
        rw [← Real.exp_add]; simp
      calc (s ^ n)⁻¹ * (μ (closedBall y s)).toReal
          = Real.exp Λ * (Real.exp (-Λ) * ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal)) := by
            rw [← mul_assoc, hexpinv, one_mul]
        _ ≤ Real.exp Λ * (Real.exp Λ * (M / R ^ n) + 2 * Λ) :=
            mul_le_mul_of_nonneg_left hC hexp_pos.le
    have h2Λ : Real.exp (2 * Λ) = Real.exp Λ * Real.exp Λ := by
      rw [two_mul, Real.exp_add]
    have hmain : (μ (closedBall y s)).toReal
        ≤ (Real.exp (2 * Λ) * (M / R ^ n) + 2 * Real.exp Λ * Λ) * s ^ n := by
      calc (μ (closedBall y s)).toReal
          = ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal) * s ^ n := hcancel.symm
        _ ≤ (Real.exp Λ * (Real.exp Λ * (M / R ^ n) + 2 * Λ)) * s ^ n :=
            mul_le_mul_of_nonneg_right hB hsn.le
        _ = (Real.exp (2 * Λ) * (M / R ^ n) + 2 * Real.exp Λ * Λ) * s ^ n := by
            rw [h2Λ]; ring
    exact (ENNReal.ofReal_toReal (hfin s hsI)).symm.trans_le (ENNReal.ofReal_le_ofReal hmain)
  · intro hω
    have hωs := hω s hsI
    refine ⟨?_, ?_⟩
    · -- (ii)
      have h2 : F s - 1 ≤ Λ := le_trans (le_abs_self _) hF3
      have hA : ω - Λ ≤ F s * ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal) := by
        have : F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal
            = F s * ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal) := by ring
        linarith
      have hC : ω - Λ ≤ Real.exp Λ * ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal) :=
        le_trans hA (mul_le_mul_of_nonneg_right hF2 hx0)
      have hexpinv : Real.exp (-Λ) * Real.exp Λ = 1 := by
        rw [← Real.exp_add]; simp
      have hB : Real.exp (-Λ) * (ω - Λ) ≤ (s ^ n)⁻¹ * (μ (closedBall y s)).toReal := by
        calc Real.exp (-Λ) * (ω - Λ)
            ≤ Real.exp (-Λ) * (Real.exp Λ * ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal)) :=
              mul_le_mul_of_nonneg_left hC hexpn_pos.le
          _ = (s ^ n)⁻¹ * (μ (closedBall y s)).toReal := by
              rw [← mul_assoc, hexpinv, one_mul]
      have hmain : Real.exp (-Λ) * (ω - Λ) * s ^ n ≤ (μ (closedBall y s)).toReal := by
        calc Real.exp (-Λ) * (ω - Λ) * s ^ n
            ≤ ((s ^ n)⁻¹ * (μ (closedBall y s)).toReal) * s ^ n :=
              mul_le_mul_of_nonneg_right hB hsn.le
          _ = (μ (closedBall y s)).toReal := hcancel
      exact (ENNReal.ofReal_le_ofReal hmain).trans_eq (ENNReal.ofReal_toReal (hfin s hsI))
    · -- (iii)
      have hpiece : ∀ t : ℝ, 0 < t → t < s →
          ∫⁻ x in closedBall y s \ closedBall y t, ENNReal.ofReal (g x) ∂μ
            ≤ ENNReal.ofReal (Real.exp Λ * (Real.exp Λ * (M / R ^ n) + Λ - ω)) := by
        intro t ht hts
        have htI : t ∈ Ioo 0 R := ⟨ht, lt_trans hts hsR⟩
        refine le_trans (hΦ t s ht hts.le hsR).2 (ENNReal.ofReal_le_ofReal ?_)
        have hωt := hω t htI
        apply mul_le_mul_of_nonneg_left _ hexp_pos.le
        linarith
      have hmono : Monotone (fun k : ℕ => closedBall y s \ closedBall y (s / ((k : ℝ) + 2))) := by
        intro i j hij
        apply sdiff_subset_sdiff_right
        apply closedBall_subset_closedBall
        have hij' : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
        apply div_le_div_of_nonneg_left hs.le (by positivity)
        linarith
      have hdir : Directed (· ⊆ ·)
          (fun k : ℕ => closedBall y s \ closedBall y (s / ((k : ℝ) + 2))) :=
        hmono.directed_le
      have hUnion : (⋃ k : ℕ, closedBall y s \ closedBall y (s / ((k : ℝ) + 2)))
          = closedBall y s \ {y} := by
        ext x
        simp only [mem_iUnion, Set.mem_sdiff, mem_closedBall, mem_singleton_iff, not_le]
        constructor
        · rintro ⟨k, hx1, hx2⟩
          refine ⟨hx1, fun h => ?_⟩
          have : 0 < s / ((k : ℝ) + 2) := by positivity
          rw [h, dist_self] at hx2
          linarith
        · rintro ⟨hx1, hx2⟩
          have hpos : 0 < dist x y := dist_pos.mpr hx2
          obtain ⟨k, hk⟩ := exists_nat_gt (s / dist x y)
          refine ⟨k, hx1, ?_⟩
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hpos] at hk
          nlinarith
      have hmain : ∫⁻ x in closedBall y s \ {y}, ENNReal.ofReal (g x) ∂μ
          ≤ ENNReal.ofReal (Real.exp Λ * (Real.exp Λ * (M / R ^ n) + Λ - ω)) := by
        rw [← hUnion, setLIntegral_iUnion_of_directed (fun x => ENNReal.ofReal (g x)) hdir]
        apply iSup_le
        intro k
        apply hpiece
        · positivity
        · apply div_lt_self hs
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith
      have hsingle : ∫⁻ x in ({y} : Set (Amb n ℓ)), ENNReal.ofReal (g x) ∂μ = 0 := by
        simp [hgy]
      calc ∫⁻ x in closedBall y s, ENNReal.ofReal (g x) ∂μ
          ≤ ∫⁻ x in (closedBall y s \ {y}) ∪ {y}, ENNReal.ofReal (g x) ∂μ := by
            apply lintegral_mono_set
            intro x hx
            by_cases h : x = y
            · exact Or.inr h
            · exact Or.inl ⟨hx, h⟩
        _ ≤ ∫⁻ x in closedBall y s \ {y}, ENNReal.ofReal (g x) ∂μ
            + ∫⁻ x in ({y} : Set (Amb n ℓ)), ENNReal.ofReal (g x) ∂μ :=
            lintegral_union_le _ _ _
        _ ≤ ENNReal.ofReal (Real.exp Λ * (Real.exp Λ * (M / R ^ n) + Λ - ω)) := by
            rw [hsingle, add_zero]; exact hmain
```

## Key steps

1. For r < R: mu(B_r) = ofReal(m(r)) with 0 <= m(r) <= M, and e^-Lambda <= F(r) <= e^Lambda, |F(r) - 1| <= Lambda
2. Phi(s) <= Phi(r) <= e^Lambda r^-n M + Lambda for s <= r < R; letting r -> R gives Phi(s) <= e^Lambda M/R^n + Lambda
3. (i): divide F(s) s^-n m(s) <= e^Lambda M/R^n + 2 Lambda by F(s) >= e^-Lambda
4. (ii): omega - Lambda <= F(s) s^-n m(s) <= e^Lambda s^-n m(s)
5. (iii): annular bounds over B_s minus B_t are uniformly <= Q; the increasing union over t = s/(k+2) is B_s minus {y}, and the centre contributes 0 since g(y) = 0

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean`
- `rg -c -t lean 'allard52_density_constants|allard52_annular_monotonicity|allard52_support_density_ge_one|allard52_center_density_bounds|aal_allard_subball_bounds' <snapshot>/project <snapshot>/mathlib/Mathlib`
- `for pat in Allard Varifold monotonicity_formula tangentProj; do rg -l -t lean $pat <snapshot>/mathlib/Mathlib | wc -l; done`
- `rg -n (theorem setLIntegral_iUnion_of_directed | theorem lintegral_union_le | theorem lintegral_liminf_le' | theorem tendsto_measure_biInter_gt | lemma mem_support_iff_forall | theorem LocallyIntegrableOn.integrableOn_compact_subset | theorem lintegral_lintegral_swap | theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le | theorem norm_image_sub_le_of_norm_deriv_le | theorem integral_hasDerivAt_right) MeasureTheory Analysis/Calculus/ParametricIntegral.lean Analysis/Calculus/MeanValue.lean, run in <snapshot>/mathlib/Mathlib`
- `rg -n (monoton|κ|kappa|2.4|density) <snapshot>/project/GMT/Ch05/README.md; sed -n 25,45p <snapshot>/project/GMT/Ch05/README.md`
- `grep -n (def lpMeanCurvatureKappa|structure LpAnnularCorrection|theorem HasGeneralizedMeanCurvatureIn.exists_lpAnnularCorrection) -A3 .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `python3 over dag.json: lean_name, lean_statement, status, parent and candidate_commit for the five proposed names, allard52_tangent_ae, allard52_density_bounds and every accepted node`
- `git show 595bf34cad5e797b1ca2c89a3d419f3daecdab75:GMT/Ch05/Submission.lean; git show 9f4dca65df4fbd188bea65e81c59d598279e6643:GMT/Ch05/Submission.lean | grep -n 'theorem allard52_tangent_ae'; git show 4c0fc30d6a1cd4ba43b449f2e51583e4e473c461:GMT/Ch05/Submission.lean | grep -n 'theorem dohr_local_monotonicity'`
- `toolchains/lean-4.35.0-rc3-linux/bin/lean GMT/Ch05/Submission.lean -o /tmp/db3-build/lib/GMT/Ch05/Submission.olean (LEAN_PATH = /tmp/db3-build/lib plus lake-packages-25730c7c/*/.lake/build/lib/lean)`
- `LEAN_PATH=<same> lean /tmp/db3-check/Types.lean; lean /tmp/db3-check/Assembly.lean; lean /tmp/db3-check/Appx_density_constants.lean; lean /tmp/db3-check/Appx_center_density_bounds.lean; lean /tmp/db3-check/Appx_support_density_ge_one.lean; lean /tmp/db3-check/Subball.lean`
- `python3 field-by-field comparison of the proposed subproblems with nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-v2.json`
- `grep max_nodes .humanize/swarm-configs/675fa2adfe3d43c39028ca3e3199bdce.json; read _existing_lean_name_problem, _accepted_checkpoint, _install_parent_supplied_child_handoff and the node-bound check of /runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py, and ensure in store.py`
- `sed -n 270,315p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt (Simon Ch. 5, 2.3, 2.4 and inequality (1) in the proof of 2.5)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/swarm-configs/675fa2adfe3d43c39028ca3e3199bdce.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/db3-check/Types.lean`
- `/tmp/db3-check/Assembly.lean`
- `/tmp/db3-check/Appx_density_constants.lean`
- `/tmp/db3-check/Appx_center_density_bounds.lean`
- `/tmp/db3-check/Appx_support_density_ge_one.lean`
- `/tmp/db3-check/Subball.lean`

Pins: project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The workspace Contract.lean and Submission.lean are byte-identical to the snapshot copies.

Names.
- The five proposed names have no match in the snapshot project or Mathlib (rg exit status 1).
- In dag.json (200 nodes) the four new names occur nowhere.
- aal_allard_subball_bounds is the accepted node root.affine_approximation-a1.pinched_density_bounds-a1.allard_subball_bounds-a1 (candidate 595bf34c). Its frozen lean_statement is byte-identical to the proposed one, so runtime reuse is permitted.
- allard52_tangent_ae is accepted (candidate 9f4dca65, theorem at line 816) with the type used by the assembly.

Mathlib.
- The topics Allard, Varifold, monotonicity_formula and tangentProj have 0 hits, so the annular monotonicity is new.
- Lemmas used by the child proofs exist: setLIntegral_iUnion_of_directed (Lebesgue/Basic.lean:668), lintegral_union_le (Basic.lean:632), lintegral_liminf_le' (Lebesgue/Add.lean:216), tendsto_measure_biInter_gt (Measure/Continuity.lean:266), mem_support_iff_forall (Measure/Support.lean:75), LocallyIntegrableOn.integrableOn_compact_subset (LocallyIntegrable.lean:122), lintegral_lintegral_swap (Measure/Prod.lean:1071), integral_hasDerivAt_right (FundThmCalculus.lean:725), hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286) and norm_image_sub_le_of_norm_deriv_le (MeanValue.lean:727).

SimonGMT.
- lpMeanCurvatureKappa n p = (p - n) / (4 * p) (LpMeanCurvature.lean:76) confirms the corrected kappa.
- LpAnnularCorrection and exists_lpAnnularCorrection (LpAnnular.lean:335, 358) are proved for the library varifold with stored tangent data. The chapter README (lines 33-38) says this needs a bridge, so annular_monotonicity re-derives the result for the contract varifold.
- The accepted dohr_local_monotonicity (4c0fc30d, line 465) has the same hypotheses but no conical term and no decay rate.

Lean checks (Lean v4.35.0-rc3).
- Types.lean: every proposed type, the tangent sibling type and the frozen parent type elaborate with only sorry warnings.
- Assembly.lean proves the exact frozen parent type from the five children and allard52_tangent_ae. #print axioms lists exactly propext, Classical.choice, Quot.sound and those six declarations.
- Appendices: density_constants and center_density_bounds use standard axioms only; support_density_ge_one uses standard axioms plus aal_allard_subball_bounds and allard52_annular_monotonicity.
- The accepted subball body recompiles with standard axioms only.
- No matrix or inline-instance constructions occur; V.weight is passed directly as the abstract measure of center_density_bounds and elaborates.

Runtime. The current config has max_nodes = 1000 against 200 existing nodes, so the 4 new nodes fit. Reused accepted nodes skip handoff installation, and ensure returns existing nodes unchanged.

Source. Simon's 2.4 and the proof of 2.5 (1) confirm the pinched density and conical-integral bounds that are formalized here with explicit constants.
