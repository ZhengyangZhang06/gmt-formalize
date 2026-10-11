# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_regularity-a1.density_ge_one-a1`
- Child DAG node: `root.density_one_regularity-a1.density_ge_one-a1.density_usc-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 4, 4.9 (density exists everywhere in U and is upper semicontinuous), with the argument of 3.11. This is steps 6 and 7 of the parent proof, written with the explicit monotone quantity of the sibling child lp_monotonicity. Notation: mu := V.weight; B_t(y) := closed ball; omega_n := unitBallVolume n = pi^(n/2)/Gamma(n/2 + 1) > 0 (Gamma > 0 on (0, infinity)); kappa := (p-n)/(4p) > 0; a := 1 - n/p in (0,1).

1. Set-up. Fix xi in U. Since U is open, choose R > 0 with B_{2R}(xi) contained in U. Every compact K contained in U has mu(K) = int over M cap K of theta dH^n < infinity (structure field integrableOn_mult). In particular mu(B_t(y)) <= mu(B_{2R}(xi)) < infinity whenever B_t(y) is contained in B_{2R}(xi). Let A* := int over B_{2R}(xi) of |H|^p dmu; it is finite by the local L^p hypothesis. Put s* := (R^(p-n) A*)^(1/p) < infinity and Lambda := s*/kappa >= 0, so kappa Lambda = s*. For y in B_R(xi), the triangle inequality gives B_R(y) contained in B_{2R}(xi), hence in U. Then
(R^(p-n) int over B_R(y) of |H|^p dmu)^(1/p) <= (R^(p-n) A*)^(1/p) = kappa Lambda,
by monotonicity of the integral in the domain and of u -> u^(1/p). So the sibling child lp_monotonicity applies at every y in B_R(xi), with radius R and this Lambda: with f(sigma) := exp((Lambda/2)(sigma/R)^a), the function G_y(sigma) := f(sigma)(sigma^(-n) mu(B_sigma(y)) + 1) is nondecreasing on (0, R]. Put m_y(sigma) := sigma^(-n) mu(B_sigma(y)) for 0 < sigma <= R, a finite nonnegative real number.

2. The factor. f is continuous on R, since a > 0 makes sigma -> (sigma/R)^a continuous. Also f(0) = exp(0) = 1, so f(sigma) -> 1 as sigma -> 0+, and f > 0.

3. Densities as real limits. Let y be in B_R(xi) and t real with V.HasDensity y t, i.e. mu(B_sigma(y))/(omega_n sigma^n) -> t^+ := max(t, 0) in [0, infinity] as sigma -> 0+. Indeed ENNReal.ofReal t = ENNReal.ofReal t^+. For 0 < sigma <= R this quotient is the finite number m_y(sigma)/omega_n, since mu(B_sigma(y)) < infinity and omega_n sigma^n > 0. Applying ENNReal.toReal, which is continuous at the finite limit ENNReal.ofReal t and maps it to t^+, gives m_y(sigma)/omega_n -> t^+, i.e. m_y(sigma) -> omega_n t^+ as sigma -> 0+.

4. Existence of the density at xi (parent step 6). G_xi is nondecreasing on (0, R] and G_xi >= 0. So the limit L := lim_{sigma -> 0+} G_xi(sigma) = inf over (0,R) of G_xi exists in R. By step 2, m_xi(sigma) = G_xi(sigma)/f(sigma) - 1 -> L - 1 =: g0, and g0 >= 0 since m_xi >= 0. Put d := g0/omega_n >= 0. For 0 < sigma <= R the density quotient of V at xi equals ENNReal.ofReal(m_xi(sigma)/omega_n), and m_xi(sigma)/omega_n -> d. Since ENNReal.ofReal is continuous, V.HasDensity xi d.

5. A lower bound at nearby points. Let y be in B_R(xi), t real with V.HasDensity y t, and tau in (0, R]. For 0 < sigma <= tau, monotonicity gives G_y(sigma) <= G_y(tau). As sigma -> 0+, G_y(sigma) = f(sigma)(m_y(sigma) + 1) -> 1 * (omega_n t^+ + 1) by steps 2 and 3. Hence omega_n t^+ + 1 <= G_y(tau).

6. Choice of scales (parent step 7). Fix eps > 0 and put T := omega_n (d + eps) + 1. As tau -> 0+, f(tau)(m_xi(tau) + 1) -> 1 * (g0 + 1) = omega_n d + 1 < T. So there is tau in (0, R/2) with f(tau)(m_xi(tau) + 1) < T. Next, the closed balls B_{tau+delta}(xi), delta > 0, decrease to their intersection B_tau(xi), and mu(B_{tau + R/2}(xi)) <= mu(B_{2R}(xi)) < infinity. By continuity of measure from above, mu(B_{tau+delta}(xi)) -> mu(B_tau(xi)) as delta -> 0+, hence f(tau)(tau^(-n) mu(B_{tau+delta}(xi)) + 1) -> f(tau)(m_xi(tau) + 1) < T. So there is delta in (0, R/2) with f(tau)(tau^(-n) mu(B_{tau+delta}(xi)) + 1) < T.

7. Conclusion. Let N be the open ball of radius delta about xi; it is a neighbourhood of xi. Let y be in N and t real with V.HasDensity y t. Then y is in B_R(xi) because delta < R. Also B_tau(y) is contained in B_{tau+delta}(xi) by the triangle inequality, and tau <= R. By step 5, monotonicity of mu and f(tau) > 0:
omega_n t^+ + 1 <= G_y(tau) = f(tau)(tau^(-n) mu(B_tau(y)) + 1) <= f(tau)(tau^(-n) mu(B_{tau+delta}(xi)) + 1) < T = omega_n (d + eps) + 1.
Since omega_n > 0, t <= t^+ < d + eps. This holds for every y in N and every such t, which is the asserted upper semicontinuity. Together with step 4 this proves the claim. QED.

Formalization notes (not part of the argument): the appendix below gives a complete Lean proof of this child from the frozen type of lp_monotonicity, compiled during the decomposition. Ingredients:
- MonotoneOn.tendsto_nhdsWithin_Ioo_right (the limit in step 4).
- ENNReal.tendsto_toReal and ENNReal.toReal_ofReal' (step 3).
- ENNReal.ofReal_div_of_pos and ENNReal.ofReal_toReal (step 4).
- tendsto_measure_cthickening_of_isClosed with cthickening_closedBall (step 6).
- Real.Gamma_pos_of_pos (omega_n > 0).
- Ioc_mem_nhdsGT and Ioo_mem_nhdsGT.

APPENDIX (formal reference, not part of the mathematical proof). Complete Lean proof of this exact frozen statement from the frozen type of the sibling `lp_corrected_mass_ratio_monotoneOn` (child lp_monotonicity). It was compiled during the decomposition review (Lean v4.35.0-rc3, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d, simongmt 2b3663083f3fe399b6296fb8eaee52169170e197) after lines 1-460 of GMT/Ch05/Contract.lean, inside `namespace Submission`. No extra imports are needed. Together with the appendices of the two siblings, `#print axioms Submission.exists_density_upperSemicontinuous_of_locallyLp` reports [propext, Classical.choice, Quot.sound].
```lean
theorem exists_density_upperSemicontinuous_of_locallyLp : ∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), 1 ≤ n → IsOpen U → (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → V.LocallyLp H p → AEStronglyMeasurable V.tangentProj V.weight → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ ξ ∈ U, ∃ d : ℝ, 0 ≤ d ∧ V.HasDensity ξ d ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 ξ, ∀ t : ℝ, V.HasDensity y t → t ≤ d + ε := by
  intro n ℓ U V H p hn hU hp hH hLp hG2 hG1 ξ hξ
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    apply div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    apply Real.Gamma_pos_of_pos
    positivity
  set ω := unitBallVolume n with hω_def
  -- local finiteness of the weight on compact subsets of `U`
  have hfin : ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ U → V.weight K < ∞ := by
    intro K hK hKU
    have hint := V.integrableOn_mult K hK hKU
    rw [RectifiableVarifold.weight, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, Set.inter_comm]
    exact hint.lintegral_lt_top
  obtain ⟨R, hR, hball⟩ : ∃ R > 0, closedBall ξ (2 * R) ⊆ U := by
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU ξ hξ
    refine ⟨r / 4, by positivity, ?_⟩
    exact (closedBall_subset_ball (by linarith)).trans hsub
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  set κ : ℝ := (p - n) / (4 * p) with hκ_def
  have hκ : 0 < κ := div_pos (sub_pos.mpr hp) (by positivity)
  set A := ∫⁻ x in closedBall ξ (2 * R), ‖H x‖ₑ ^ p ∂V.weight with hA_def
  have hA : A < ∞ := hLp _ (isCompact_closedBall _ _) hball
  set s : ℝ≥0∞ := (ENNReal.ofReal (R ^ (p - n)) * A) ^ (1 / p) with hs_def
  have hs : s ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA.ne
  set Λ : ℝ := s.toReal / κ with hΛ_def
  have hΛ : 0 ≤ Λ := div_nonneg ENNReal.toReal_nonneg hκ.le
  have hκΛ : ENNReal.ofReal (κ * Λ) = s := by
    rw [hΛ_def, mul_div_cancel₀ _ hκ.ne', ENNReal.ofReal_toReal hs]
  have hsub2 : ∀ y ∈ closedBall ξ R, closedBall y R ⊆ closedBall ξ (2 * R) := by
    intro y hy
    apply closedBall_subset_closedBall'
    have : dist y ξ ≤ R := hy
    linarith
  have hscale : ∀ y ∈ closedBall ξ R, V.scaledLpNorm H p y R ≤ ENNReal.ofReal (κ * Λ) := by
    intro y hy
    rw [hκΛ, RectifiableVarifold.scaledLpNorm]
    apply ENNReal.rpow_le_rpow _ (by positivity)
    exact mul_le_mul_right (lintegral_mono_set (hsub2 y hy)) _
  set f : ℝ → ℝ := fun σ => Real.exp (Λ / 2 * (σ / R) ^ (1 - (n : ℝ) / p)) with hf_def
  set G : Amb n ℓ → ℝ → ℝ := fun y σ =>
    f σ * ((V.weight (closedBall y σ)).toReal / σ ^ n + 1) with hG_def
  have hmono : ∀ y ∈ closedBall ξ R, MonotoneOn (G y) (Ioc 0 R) := by
    intro y hy
    exact lp_corrected_mass_ratio_monotoneOn V H p hn hp hH hG2 hG1 y R Λ hR hΛ
      ((hsub2 y hy).trans hball) (hscale y hy)
  have he : 0 < 1 - (n : ℝ) / p := sub_pos.mpr ((div_lt_one hp0).mpr hp)
  have hf1 : Tendsto f (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous f := by
      apply Real.continuous_exp.comp
      exact continuous_const.mul
        ((continuous_id.div_const R).rpow_const (fun _ => Or.inr he.le))
    have ht := (hc.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa [hf_def, zero_div, Real.zero_rpow he.ne'] using ht
  have hfpos : ∀ σ, 0 < f σ := fun σ => Real.exp_pos _
  have hfinball : ∀ y ∈ closedBall ξ R, ∀ σ, σ ≤ R → V.weight (closedBall y σ) ≠ ∞ := by
    intro y hy σ hσ
    exact ((measure_mono (closedBall_subset_closedBall hσ)).trans_lt
      (hfin _ (isCompact_closedBall _ _) ((hsub2 y hy).trans hball))).ne
  set m : Amb n ℓ → ℝ → ℝ := fun y σ => (V.weight (closedBall y σ)).toReal / σ ^ n with hm_def
  -- conversion of `HasDensity` into a limit of real mass ratios
  have hconv : ∀ y ∈ closedBall ξ R, ∀ t : ℝ, V.HasDensity y t →
      Tendsto (m y) (𝓝[>] 0) (𝓝 (ω * max t 0)) := by
    intro y hy t ht
    have h1 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp ht
    rw [ENNReal.toReal_ofReal'] at h1
    have h2 := h1.const_mul ω
    apply h2.congr'
    filter_upwards [Ioc_mem_nhdsGT hR] with σ hσ
    have hσn : 0 < σ ^ n := pow_pos hσ.1 n
    simp only [Function.comp_apply, hm_def]
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (by positivity), ← hω_def]
    field_simp
  have hξR : ξ ∈ closedBall ξ R := mem_closedBall_self hR.le
  -- existence of the density at `ξ`
  have hne : (Ioo (0 : ℝ) R).Nonempty := ⟨R / 2, by positivity, by linarith⟩
  have hGnonneg : ∀ σ ∈ Ioo 0 R, 0 ≤ G ξ σ := fun σ hσ =>
    mul_nonneg (hfpos σ).le (add_nonneg (div_nonneg ENNReal.toReal_nonneg
      (pow_pos hσ.1 n).le) zero_le_one)
  have hGlim := MonotoneOn.tendsto_nhdsWithin_Ioo_right hne
    ((hmono ξ hξR).mono Ioo_subset_Ioc_self)
    ⟨0, by rintro _ ⟨σ, hσ, rfl⟩; exact hGnonneg σ hσ⟩
  set L := sInf (G ξ '' Ioo 0 R) with hL_def
  have hm_lim : Tendsto (m ξ) (𝓝[>] 0) (𝓝 (L - 1)) := by
    have h := (hGlim.div hf1 one_ne_zero).sub_const 1
    rw [div_one] at h
    apply h.congr'
    filter_upwards with σ
    simp only [Pi.div_apply, hG_def, hm_def]
    rw [mul_div_cancel_left₀ _ (hfpos σ).ne']
    ring
  have hL1 : 0 ≤ L - 1 := by
    apply ge_of_tendsto hm_lim
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact div_nonneg ENNReal.toReal_nonneg (pow_pos hσ n).le
  set d := (L - 1) / ω with hd_def
  have hωd : ω * d = L - 1 := by rw [hd_def]; field_simp
  refine ⟨d, div_nonneg hL1 hω.le, ?_, ?_⟩
  · -- `HasDensity ξ d`
    unfold RectifiableVarifold.HasDensity
    have h := (ENNReal.continuous_ofReal.tendsto _).comp (hm_lim.div_const ω)
    apply h.congr'
    filter_upwards [Ioc_mem_nhdsGT hR] with σ hσ
    have hσn : 0 < σ ^ n := pow_pos hσ.1 n
    simp only [Function.comp_apply, hm_def]
    rw [div_div, mul_comm (σ ^ n) ω, ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_toReal (hfinball ξ hξR σ hσ.2)]
  · intro ε hε
    set T := ω * (d + ε) + 1 with hT_def
    have hlim0 : Tendsto (fun τ => f τ * (m ξ τ + 1)) (𝓝[>] 0) (𝓝 (1 * (L - 1 + 1))) :=
      hf1.mul (hm_lim.add_const 1)
    have hlt0 : 1 * (L - 1 + 1) < T := by
      rw [← hωd, hT_def]
      nlinarith [mul_pos hω hε]
    obtain ⟨τ, hτlt, hτ⟩ :=
      ((hlim0.eventually (gt_mem_nhds hlt0)).and (Ioo_mem_nhdsGT (half_pos hR))).exists
    -- continuity from above of `δ ↦ μ(B_{τ+δ}(ξ))`
    have hcont : Tendsto (fun δ => V.weight (closedBall ξ (τ + δ))) (𝓝[>] 0)
        (𝓝 (V.weight (closedBall ξ τ))) := by
      have h := tendsto_measure_cthickening_of_isClosed (μ := V.weight)
        (s := closedBall ξ τ) ⟨R / 2, half_pos hR, by
          rw [cthickening_closedBall (half_pos hR).le hτ.1.le]
          exact hfinball ξ hξR _ (by linarith [hτ.2])⟩ isClosed_closedBall
      apply (h.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)).congr'
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      rw [cthickening_closedBall (le_of_lt hδ) hτ.1.le, add_comm δ τ]
    have hcontR : Tendsto (fun δ => f τ * ((V.weight (closedBall ξ (τ + δ))).toReal / τ ^ n + 1))
        (𝓝[>] 0) (𝓝 (f τ * (m ξ τ + 1))) := by
      have h := (ENNReal.tendsto_toReal (hfinball ξ hξR τ (by linarith [hτ.2]))).comp hcont
      exact ((h.div_const (τ ^ n)).add_const 1).const_mul (f τ)
    obtain ⟨δ, hδlt, hδ⟩ :=
      ((hcontR.eventually (gt_mem_nhds hτlt)).and (Ioo_mem_nhdsGT (half_pos hR))).exists
    filter_upwards [ball_mem_nhds ξ hδ.1] with y hy t ht
    have hyξ : dist y ξ < δ := hy
    have hyR : y ∈ closedBall ξ R := by
      show dist y ξ ≤ R
      linarith [hδ.2]
    have hlimy := hconv y hyR t ht
    have hGy : Tendsto (G y) (𝓝[>] 0) (𝓝 (1 * (ω * max t 0 + 1))) :=
      hf1.mul (hlimy.add_const 1)
    have hle : 1 * (ω * max t 0 + 1) ≤ G y τ := by
      apply le_of_tendsto hGy
      filter_upwards [Ioc_mem_nhdsGT hτ.1] with σ hσ
      exact hmono y hyR ⟨hσ.1, hσ.2.trans (by linarith [hτ.2])⟩
        ⟨hτ.1, by linarith [hτ.2]⟩ hσ.2
    have hball_sub : closedBall y τ ⊆ closedBall ξ (τ + δ) := by
      apply closedBall_subset_closedBall'
      linarith
    have hGyτ : G y τ ≤ f τ * ((V.weight (closedBall ξ (τ + δ))).toReal / τ ^ n + 1) := by
      apply mul_le_mul_of_nonneg_left _ (hfpos τ).le
      have hτn : 0 < τ ^ n := pow_pos hτ.1 n
      have := ENNReal.toReal_mono (hfinball ξ hξR (τ + δ) (by linarith [hτ.2, hδ.2]))
        (measure_mono hball_sub)
      gcongr
    have h3 : ω * max t 0 < ω * (d + ε) := by linarith
    have h4 := lt_of_mul_lt_mul_left h3 hω.le
    linarith [le_max_left t 0]
```

## Key steps

1. Choose R with B_{2R}(xi) in U and Lambda = kappa^-1 (R^(p-n) int_{B_2R(xi)}|H|^p)^(1/p); lp_monotonicity applies at every y in B_R(xi) with radius R
2. HasDensity y t gives sigma^-n mu(B_sigma(y)) -> omega_n max(t,0)
3. At xi the monotone G_xi has a limit as sigma -> 0+, and the factor tends to 1, so sigma^-n mu(B_sigma(xi)) converges; this gives HasDensity xi d with d >= 0
4. Monotonicity at nearby y gives omega_n max(t,0) + 1 <= G_y(tau) <= f(tau)(tau^-n mu(B_{tau+delta}(xi)) + 1)
5. Choose tau small, then delta small by continuity from above of closed-ball measures; then t <= d + eps on the delta-ball about xi

## Reference use

### local-project

Queries:
- `python3 json.load(nodes/root-density-one-regularity-a1-density-ge-one-a1/parent-child-handoff.json): subproblem, audit, resolved_dependencies`
- `python3 scan of dag.json: lean_name / lean_statement / status of every node (reserved names; tangent_ae, aal_lp_monotonicity, aal_tangent_structure, dohr_local_monotonicity)`
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean`
- `rg -n 'def HasDensity|def LocallyLp|def scaledLpNorm|def HasGeneralizedMeanCurvature|def divM|def tangentProj|def support|def weight|integrableOn_mult' <snapshot>/project/GMT/Ch05/Contract.lean`
- `rg -n 'theorem |lemma ' <snapshot>/project/GMT/Ch05/`
- `rg -n '^theorem (hasDerivAt_integral_of_dominated_loc_of_deriv_le|integral_mul_le_Lp_mul_Lq_of_nonneg|monotoneOn_of_deriv_nonneg|tendsto_integral_filter_of_dominated_convergence|tendsto_measure_cthickening_of_isClosed|cthickening_closedBall|measure_eq_zero_iff_ae_notMem|withDensity_absolutelyContinuous|Integrable.lintegral_lt_top|Gamma_pos_of_pos|contDiffAt_norm)\b' <snapshot>/mathlib/Mathlib`
- `rg -n '^(theorem|lemma) (MonotoneOn.tendsto_nhdsWithin_Ioo_right|mem_support_iff_forall|LocallyIntegrableOn.integrableOn_compact_subset)\b' <snapshot>/mathlib/Mathlib`
- `rg -n smoothTransition <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `grep -rn 'HasFDerivAt.norm|hasFDerivAt_norm|fderiv_norm|hasStrictFDerivAt_norm' Mathlib --include=*.lean`
- `grep -n '^theorem|^def' .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/{LpDensity,LpMeanCurvature,FirstVariation,MeanCurvature,Density,LowerDensityTangents,TangentDensity}.lean`
- `cat Chapter04/{LpLowerDensity,MultiplicityBridge,LpDensity}.lean; sed -n 1,260p Chapter04/Basic.lean; sed -n 1,563p Chapter04/LpMeanCurvature.lean; sed -n 1,320p, 390,430p, 600,960p Chapter04/FirstVariation.lean`
- `sed -n 25,130p and 225,365p .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `sed -n 215,575p book/chapter-04.txt`
- `grep -rl 'radial_cutoff_first_variation_eq|lp_corrected_mass_ratio_monotoneOn|exists_density_upperSemicontinuous_of_locallyLp' .humanize GMT .lake/packages/simongmt/Poincare .lake/packages/mathlib/Mathlib`
- `sed -n 1,120p, 330,384p, 500,580p verifier/gmt-compare.py (child_modules / contract_scope)`
- `lake env lean /tmp/dge1-check/Check5.lean, Check3.lean, Check4.lean, verify/A1.lean, verify/M.lean, verify/FullChain.lean, verify/FromJSON.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpLowerDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/MultiplicityBridge.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Density.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-density-ge-one-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dge1-check/Check5.lean`
- `/tmp/dge1-check/Check3.lean`
- `/tmp/dge1-check/Check4.lean`
- `/tmp/dge1-check/verify/A1.lean`
- `/tmp/dge1-check/verify/M.lean`
- `/tmp/dge1-check/verify/FromJSON.lean`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d; its GMT/Ch05/Contract.lean is byte-identical to the workspace copy (cmp). The project contains no density or monotonicity theorem for the contract RectifiableVarifold (rg finds only definitions and the sorry'd main_theorem), so all three children are new obligations.

SimonGMT Chapter04 proves the full L^p theory: LpMeanCurvature.lean lp_normalizedBallMass_monotoneOn_Ioc with lpMonotonicityFactor = exp((Lambda/2)(rho/R)^(1-n/p)); LpDensity.lean; LpLowerDensity.lean one_le_stationaryDensityReal_of_mem_support_lp. It does so only for Chapter04.RectifiableVarifold (Basic.lean), which needs a MeasurableSet carrier, an unweighted approximate-tangent field (Chapter03 HasApproximateTangentSpaceAt) and a globally locally finite weight. The contract varifold and the sibling tangent_ae give only weighted tangents (HasWeightedApproximateTangentSpaceAt, Chapter03/Rectifiable.lean:330), so these theorems do not transfer. The generic SimonGMT lemmas do apply and are used: monotonicityCutoff (FirstVariation.lean:825ff), deriv_eq_zero_of_cutoff, hasDerivAt_lpMonotonicityFactor, and trace_radialEndomorphism as a template.

All Mathlib lemmas used are present in the snapshot:
- hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286)
- integral_mul_le_Lp_mul_Lq_of_nonneg (Bochner/Basic.lean:1230)
- monotoneOn_of_deriv_nonneg (Deriv/MeanValue.lean:411)
- tendsto_integral_filter_of_dominated_convergence (DominatedConvergence.lean:67)
- tendsto_measure_cthickening_of_isClosed (BorelSpace/Metric.lean:143)
- cthickening_closedBall (Ball/Pointwise.lean:318)
- measure_eq_zero_iff_ae_notMem (OuterMeasure/AE.lean:145)
- withDensity_absolutelyContinuous (WithDensity.lean:146)
- Integrable.lintegral_lt_top (IntegrableOn.lean:479)
- Real.Gamma_pos_of_pos (Gamma/Basic.lean:443)
- contDiffAt_norm (InnerProductSpace/Calculus.lean:154)
- MonotoneOn.tendsto_nhdsWithin_Ioo_right (Topology/Order/Monotone.lean:457)
- Measure.mem_support_iff_forall (Measure/Support.lean:75)
- LocallyIntegrableOn.integrableOn_compact_subset (LocallyIntegrable.lean:122)
- the Real.smoothTransition API
There is no derivative-of-norm lemma (no match for HasFDerivAt.norm or hasFDerivAt_norm), so the Lean proof of child 1 uses the squared-radius reparametrization.

The three proposed lean_names occur nowhere in .humanize, GMT, SimonGMT or Mathlib and are not among the DAG's reserved lean_names.

Lean checks:
- All three types elaborate verbatim in the child-comparator scope.
- Complete sorry-free proofs of all three children compile with axioms propext, Classical.choice, Quot.sound.
- The selected theorem compiles from the children and the sibling tangent_ae, with sorryAx only from that sibling placeholder.
