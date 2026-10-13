# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.density_bounds-a1`
- Child DAG node: `root.allard_regularity-a1.density_bounds-a1.support_density_ge_one-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof (Simon, Introduction to GMT, Ch. 4, 4.9 and 4.10(1): upper semicontinuity of the density and Theta >= 1 on spt V), with the monotonicity facts (M) supplied by the sibling annular_monotonicity and the curvature scaling of step 2 supplied by the sibling subball_bounds.

Notation. mu := V.weight; B_r(z) closed balls, B°_r(z) open balls; kappa := (p - n)/(4p) > 0; alpha' := 1 - n/p in (0, 1); omega_n := unitBallVolume n = pi^(n/2)/Gamma(n/2 + 1) > 0; W := B°_rho(0); Lambda := delta/kappa, so 0 < Lambda <= 1 (from 0 < delta <= kappa) and kappa Lambda = delta. From V.AllardHypotheses H p delta rho we use rho > 0, V.HasGeneralizedMeanCurvature H, V.mult >= 1 mu-a.e., and mu(B_rho(0)) <= ofReal((1 + delta) omega_n rho^n) < infinity.

1. Uniqueness of densities. If V.HasDensity x t and V.HasDensity x t', then ofReal t = ofReal t', because both are limits of the same function along the filter of right neighbourhoods of 0 in R, which is not trivial, in the Hausdorff space [0, infinity]. Hence t = t' whenever t, t' >= 0; and if t' > 0 then t = t' (ofReal t = t' > 0 forces t > 0).

2. Monotonicity at the points of W. Let x in W and 0 < R' <= rho - |x|. Then R' <= rho and B_(R')(x) is contained in B_rho(0) (|z| <= |x| + R' <= rho). By subball_bounds (with z := x, r := R'), B_(R')(x) is contained in U and V.scaledLpNorm H p x R' <= ofReal delta = ofReal(kappa Lambda). (T1) implies its local form (for mu-a.e. x', if x' in B°_(R')(x) then V.tangentProj x' is the projection onto an n-dimensional subspace), and (T0) implies a.e.-strong measurability of x' -> V.tangentProj x' for mu restricted to B°_(R')(x). Hence annular_monotonicity applies with centre x, radius R' and this Lambda: there are F : R -> R and t_(x,R') >= 0 such that, for every r in (0, R'), F(r) >= e^(-Lambda) > 0 and |F(r) - 1| <= Lambda (r/R')^(alpha'), V.HasDensity x t_(x,R'), and omega_n t_(x,R') <= F(r) r^(-n) mu(B_r(x)).toReal + F(r) - 1 for every r in (0, R'). Define Theta(x) := t_(x, rho - |x|) >= 0, so V.HasDensity x Theta(x); by step 1, t_(x,R') = Theta(x) for every admissible R'. With c := Lambda (r/R')^(alpha') we have F(r) <= 1 + c, F(r) - 1 <= c and mu(B_r(x)).toReal >= 0, hence
 (2.1) omega_n Theta(x) <= (1 + Lambda (r/R')^(alpha')) r^(-n) mu(B_r(x)).toReal + Lambda (r/R')^(alpha') for all x in W, 0 < R' <= rho - |x| and 0 < r < R'.

3. Upper semicontinuity of Theta on W. Let x in W and eta > 0. Put R_0 := (rho - |x|)/3 > 0 and c(r) := Lambda (r/R_0)^(alpha') for r > 0; c(r) -> 0 as r -> 0+ because alpha' > 0.
 (a) For 0 < r <= 3 R_0 = rho - |x|, mu(B_r(x)) <= mu(B_rho(0)) < infinity, so mu(B_r(x))/ofReal(omega_n r^n) = ofReal(mu(B_r(x)).toReal/(omega_n r^n)). Since V.HasDensity x Theta(x) and toReal is continuous at the finite value ofReal Theta(x), r^(-n) mu(B_r(x)).toReal -> omega_n Theta(x) as r -> 0+. Choose r in (0, R_0) with (1 + c(r)) r^(-n) mu(B_r(x)).toReal + c(r) < omega_n Theta(x) + omega_n eta/2.
 (b) The closed balls B_(r')(x), r' in (r, 3R_0], have finite measure and decrease to their intersection B_r(x) as r' decreases to r, so mu(B_(r')(x)) -> mu(B_r(x)) (continuity from above). Choose r' in (r, 2 R_0) with (1 + c(r)) r^(-n) mu(B_(r')(x)).toReal + c(r) < omega_n Theta(x) + omega_n eta.
 (c) Put d := min{R_0, r' - r} > 0 and let x' in B°_d(x). Then |x'| < |x| + R_0 < rho, so x' in W, and rho - |x'| > rho - |x| - R_0 = 2 R_0 >= R_0; moreover B_r(x') is contained in B_(r')(x), because |z - x| <= |z - x'| + |x' - x| < r + d <= r'. By (2.1) at x' with R' := R_0 and this r < R_0, and monotonicity of mu (all masses finite),
 omega_n Theta(x') <= (1 + c(r)) r^(-n) mu(B_r(x')).toReal + c(r) <= (1 + c(r)) r^(-n) mu(B_(r')(x)).toReal + c(r) < omega_n Theta(x) + omega_n eta.
 Hence B°_d(x) is contained in W and Theta(x') < Theta(x) + eta for every x' in B°_d(x).

4. Theta >= 1 almost everywhere on W. By (T3) and V.mult >= 1 mu-a.e. (from 2.3), for mu-a.e. x we have V.HasDensity x (V.mult x) and V.mult x >= 1. For such x in W, step 1 (with t' := V.mult x > 0) gives Theta(x) = V.mult x >= 1. Thus for mu-a.e. x: if x in W then Theta(x) >= 1.

5. Conclusion. Let y in spt V cap W and t real with V.HasDensity y t. Suppose Theta(y) < 1. Step 3 with eta := (1 - Theta(y))/2 > 0 gives d > 0 with B°_d(y) contained in W and Theta(x') < 1 for all x' in B°_d(y). By step 4, mu-a.e. x satisfies x not in B°_d(y), i.e. mu(B°_d(y)) = 0. But y in V.support is contained in spt mu, so every open neighbourhood of y, in particular B°_d(y), has positive mu-measure: a contradiction. Therefore Theta(y) >= 1 > 0, and step 1 (V.HasDensity y t and V.HasDensity y Theta(y)) gives t = Theta(y) >= 1.

Appendix (non-normative implementation aid; the numbered argument above is the proof). The following Lean 4 declaration was compiled in the namespace/opens of the frozen contract (import GMT.Ch05.Submission; open MeasureTheory Metric Set Filter Topology; open scoped ENNReal NNReal; namespace GMT.Ch05; open RectifiableVarifold; namespace Submission) with Lean v4.35.0-rc3 and Mathlib 25730c7c. It adds no other declaration. It uses only the sibling declarations Submission.aal_allard_subball_bounds and Submission.allard52_annular_monotonicity (with exactly their frozen types); with those two as the only assumptions, #print axioms lists propext, Classical.choice, Quot.sound and these two siblings. It follows steps 1-5 (uniqueness of densities, monotonicity bound (2.1) at every point of W, upper semicontinuity, Theta >= 1 a.e., and the support argument via Measure.support).

```lean
theorem allard52_support_density_ge_one : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ (p - n) / (4 * p) → V.AllardHypotheses H p δ ρ → AEStronglyMeasurable V.tangentProj V.weight → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → (∀ᵐ x ∂V.weight, V.HasDensity x (V.mult x)) → ∀ y ∈ V.support ∩ ball (0 : Amb n ℓ) ρ, ∀ t : ℝ, V.HasDensity y t → 1 ≤ t := by
  intro n ℓ hn p hp U hU V H δ ρ hδ hδκ hA hmeas htan hdens y hy t ht
  /- Step 1: uniqueness of densities, and `ω_n > 0`. -/
  have hunique : ∀ (x : Amb n ℓ) (a b : ℝ), V.HasDensity x a → V.HasDensity x b →
      ENNReal.ofReal a = ENNReal.ofReal b :=
    fun _ _ _ ha hb => tendsto_nhds_unique ha hb
  have hdeq : ∀ (x : Amb n ℓ) (a b : ℝ), V.HasDensity x a → V.HasDensity x b → 0 ≤ a → 0 ≤ b →
      a = b :=
    fun x a b ha hb ha0 hb0 => (ENNReal.ofReal_eq_ofReal_iff ha0 hb0).1 (hunique x a b ha hb)
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    positivity
  /- Constants: `κ = (p - n)/(4p)`, `Λ = δ/κ ∈ (0, 1]`, `α = 1 - n/p ∈ (0, 1)`. -/
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have hκ : 0 < (p - n) / (4 * p) := div_pos (by linarith) (by linarith)
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = δ / ((p - n) / (4 * p)) := ⟨_, rfl⟩
  have hΛ0 : 0 < Λ := by
    rw [hΛdef]
    exact div_pos hδ hκ
  have hΛ1 : Λ ≤ 1 := by
    rw [hΛdef]
    exact (div_le_one hκ).2 hδκ
  have hκΛ : (p - n) / (4 * p) * Λ = δ := by
    rw [hΛdef]
    exact mul_div_cancel₀ δ hκ.ne'
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = 1 - (n : ℝ) / p := ⟨_, rfl⟩
  have hα : 0 < α := by
    rw [hαdef, sub_pos, div_lt_one hp0]
    exact hp
  have hfin : V.weight (closedBall 0 ρ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA.2.2.2.2.2.1
  /- Step 2: the monotonicity inequality (2.1) at points of `B̆_ρ(0)`, for every admissible
  radius `R ≤ ρ - ‖x‖`, from the two black boxes. -/
  have hmono : ∀ (x : Amb n ℓ) (R : ℝ), 0 < R → R ≤ ρ - ‖x‖ →
      ∃ θ : ℝ, 0 ≤ θ ∧ V.HasDensity x θ ∧ ∀ r ∈ Ioo 0 R, unitBallVolume n * θ ≤
        (1 + Λ * (r / R) ^ α) * ((r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal) +
          Λ * (r / R) ^ α := by
    intro x R hR hRx
    have hRρ : R ≤ ρ := by linarith [norm_nonneg x]
    have hsub : closedBall x R ⊆ closedBall 0 ρ := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      rw [mem_closedBall_zero_iff]
      calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ ρ := by linarith
    obtain ⟨hU', -, hLp, -⟩ := aal_allard_subball_bounds n ℓ p hp U V H δ ρ hA x R hR hRρ hsub
    obtain ⟨F, hF, -, θ, hθ0, hθd, hθ⟩ :=
      allard52_annular_monotonicity n ℓ hn p hp U hU V H hA.2.1 x R Λ hR hU'
        (htan.mono fun z hz _ => hz) hmeas.restrict hΛ0 hΛ1 (by rw [hκΛ]; exact hLp)
    rw [← hαdef] at hF
    refine ⟨θ, hθ0, hθd, fun r hr => ?_⟩
    obtain ⟨-, -, hFr⟩ := hF r hr
    have hm : 0 ≤ (r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal := by
      have := hr.1
      positivity
    have hFle : F r ≤ 1 + Λ * (r / R) ^ α := by
      linarith [le_abs_self (F r - 1)]
    calc unitBallVolume n * θ
        ≤ F r * (r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal + F r - 1 := hθ r hr
      _ = F r * ((r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal) + (F r - 1) := by ring
      _ ≤ (1 + Λ * (r / R) ^ α) * ((r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal) +
            Λ * (r / R) ^ α :=
          add_le_add (mul_le_mul_of_nonneg_right hFle hm) (by linarith [le_abs_self (F r - 1)])
  -- existence of a (nonnegative) density at every point of `B̆_ρ(0)`
  have hex : ∀ x : Amb n ℓ, x ∈ ball (0 : Amb n ℓ) ρ → ∃ θ : ℝ, 0 ≤ θ ∧ V.HasDensity x θ := by
    intro x hx
    have hxρ : ‖x‖ < ρ := mem_ball_zero_iff.1 hx
    obtain ⟨θ, hθ0, hθ, -⟩ := hmono x (ρ - ‖x‖) (by linarith) le_rfl
    exact ⟨θ, hθ0, hθ⟩
  -- (2.1) holds for *every* nonnegative density value, by uniqueness
  have hineq : ∀ (x : Amb n ℓ) (R : ℝ), 0 < R → R ≤ ρ - ‖x‖ → ∀ θ : ℝ, 0 ≤ θ →
      V.HasDensity x θ → ∀ r ∈ Ioo 0 R, unitBallVolume n * θ ≤
        (1 + Λ * (r / R) ^ α) * ((r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal) +
          Λ * (r / R) ^ α := by
    intro x R hR hRx θ hθ0 hθ r hr
    obtain ⟨θ₁, hθ₁0, hθ₁, hθ₁ineq⟩ := hmono x R hR hRx
    rw [hdeq x θ θ₁ hθ hθ₁ hθ0 hθ₁0]
    exact hθ₁ineq r hr
  /- Step 3: upper semicontinuity of the density on `B̆_ρ(0)`. -/
  have husc : ∀ x : Amb n ℓ, x ∈ ball (0 : Amb n ℓ) ρ → ∀ θ : ℝ, 0 ≤ θ → V.HasDensity x θ →
      ∀ η : ℝ, 0 < η → ∃ d > 0, ∀ x' ∈ ball x d, x' ∈ ball (0 : Amb n ℓ) ρ ∧
        ∀ θ' : ℝ, 0 ≤ θ' → V.HasDensity x' θ' → θ' < θ + η := by
    intro x hx θ hθ0 hθ η hη
    have hxρ : ‖x‖ < ρ := mem_ball_zero_iff.1 hx
    set R₀ := (ρ - ‖x‖) / 3 with hR₀def
    have hR₀ : 0 < R₀ := by rw [hR₀def]; linarith
    -- finiteness of the masses of the balls `B_s(x)`, `s ≤ 2 R₀`
    have hfin' : ∀ s, s ≤ 2 * R₀ → V.weight (closedBall x s) ≠ ⊤ := by
      intro s hs
      refine ne_top_of_le_ne_top hfin (measure_mono ?_)
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      rw [mem_closedBall_zero_iff]
      calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ ρ := by rw [hR₀def] at hs; linarith
    -- (a) the error term `c(r) = Λ (r/R₀)^α` tends to `0`
    have hc : Tendsto (fun r : ℝ => Λ * (r / R₀) ^ α) (𝓝[>] 0) (𝓝 0) := by
      have h2 : ContinuousAt (fun r : ℝ => Λ * (r / R₀) ^ α) 0 := by
        apply ContinuousAt.mul continuousAt_const
        exact ContinuousAt.rpow_const (continuousAt_id.div_const R₀) (Or.inr hα.le)
      have h3 := h2.tendsto
      simp only [zero_div, Real.zero_rpow hα.ne', mul_zero] at h3
      exact h3.mono_left nhdsWithin_le_nhds
    -- the normalized masses `r⁻ⁿ μ(B_r(x))` converge to `ω θ`
    have hlimm : Tendsto (fun r : ℝ => (r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal)
        (𝓝[>] 0) (𝓝 (unitBallVolume n * θ)) := by
      have hθ' : Tendsto (fun r : ℝ => V.weight (closedBall x r) /
          ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ)) := hθ
      have h1 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hθ'
      rw [ENNReal.toReal_ofReal hθ0] at h1
      have h2 := h1.const_mul (unitBallVolume n)
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : 0 < r := hr
      have hrn : 0 < r ^ n := pow_pos hr' n
      simp only [Function.comp_apply, ENNReal.toReal_div]
      rw [ENNReal.toReal_ofReal (mul_pos hω hrn).le]
      field_simp
    have hE : Tendsto (fun r : ℝ => (1 + Λ * (r / R₀) ^ α) *
        ((r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal) + Λ * (r / R₀) ^ α) (𝓝[>] 0)
        (𝓝 (unitBallVolume n * θ)) := by
      have h := (((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1)).add
        hc).mul hlimm).add hc
      simp only [add_zero, one_mul] at h
      exact h
    have hlt : unitBallVolume n * θ < unitBallVolume n * θ + unitBallVolume n * η / 2 := by
      have := mul_pos hω hη
      linarith
    obtain ⟨r, hrE, hr⟩ :=
      ((hE.eventually (gt_mem_nhds hlt)).and
        (Ioo_mem_nhdsGT hR₀ : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 R₀)).exists
    -- (b) continuity from above of `s ↦ μ(B_s(x))` at `r`
    have hcont : Tendsto (fun s => V.weight (closedBall x s)) (𝓝[>] r)
        (𝓝 (V.weight (closedBall x r))) := by
      have h := tendsto_measure_biInter_gt (μ := V.weight) (s := closedBall x) (a := r)
        (fun _ _ => measurableSet_closedBall.nullMeasurableSet)
        (fun _ _ _ hij => closedBall_subset_closedBall hij)
        ⟨2 * R₀, by linarith [hr.2], hfin' _ le_rfl⟩
      rw [biInter_gt_closedBall] at h
      exact h
    have hcont' : Tendsto (fun s => (V.weight (closedBall x s)).toReal) (𝓝[>] r)
        (𝓝 (V.weight (closedBall x r)).toReal) :=
      (ENNReal.tendsto_toReal (hfin' r (by linarith [hr.2]))).comp hcont
    have hE2 : Tendsto (fun s => (1 + Λ * (r / R₀) ^ α) *
        ((r ^ n)⁻¹ * (V.weight (closedBall x s)).toReal) + Λ * (r / R₀) ^ α) (𝓝[>] r)
        (𝓝 ((1 + Λ * (r / R₀) ^ α) * ((r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal) +
          Λ * (r / R₀) ^ α)) :=
      ((hcont'.const_mul _).const_mul _).add_const _
    have hlt2 : (1 + Λ * (r / R₀) ^ α) * ((r ^ n)⁻¹ * (V.weight (closedBall x r)).toReal) +
        Λ * (r / R₀) ^ α < unitBallVolume n * θ + unitBallVolume n * η := by
      have := mul_pos hω hη
      linarith
    obtain ⟨r', hr'E, hr'⟩ :=
      ((hE2.eventually (gt_mem_nhds hlt2)).and
        (Ioo_mem_nhdsGT (show r < 2 * R₀ by linarith [hr.2]) :
          ∀ᶠ s in 𝓝[>] r, s ∈ Ioo r (2 * R₀))).exists
    -- (c) on `B̆_d(x)`, `d = min R₀ (r' - r)`, the density is `< θ + η`
    refine ⟨min R₀ (r' - r), lt_min hR₀ (by linarith [hr'.1]), fun x' hx' => ?_⟩
    have hd1 : dist x' x < R₀ := lt_of_lt_of_le hx' (min_le_left _ _)
    have hd2 : dist x' x < r' - r := lt_of_lt_of_le hx' (min_le_right _ _)
    have hnx' : ‖x'‖ < ‖x‖ + R₀ := by
      rw [dist_eq_norm] at hd1
      calc ‖x'‖ = ‖(x' - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖x' - x‖ + ‖x‖ := norm_add_le _ _
        _ < ‖x‖ + R₀ := by linarith
    refine ⟨mem_ball_zero_iff.2 (by rw [hR₀def] at hnx'; linarith), fun θ' hθ'0 hθ' => ?_⟩
    have key := hineq x' R₀ hR₀ (by rw [hR₀def] at hnx' ⊢; linarith) θ' hθ'0 hθ' r hr
    have hball : closedBall x' r ⊆ closedBall x r' := by
      intro z hz
      rw [mem_closedBall] at hz ⊢
      calc dist z x ≤ dist z x' + dist x' x := dist_triangle _ _ _
        _ ≤ r' := by linarith
    have hmono' : (V.weight (closedBall x' r)).toReal ≤ (V.weight (closedBall x r')).toReal :=
      ENNReal.toReal_mono (hfin' r' hr'.2.le) (measure_mono hball)
    have hr0 : 0 < r := hr.1
    have hc0 : 0 ≤ Λ * (r / R₀) ^ α := by
      have := hΛ0.le
      positivity
    have h3 : (1 + Λ * (r / R₀) ^ α) * ((r ^ n)⁻¹ * (V.weight (closedBall x' r)).toReal) ≤
        (1 + Λ * (r / R₀) ^ α) * ((r ^ n)⁻¹ * (V.weight (closedBall x r')).toReal) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_left hmono' (by positivity)
    have h4 : unitBallVolume n * θ' < unitBallVolume n * (θ + η) := by
      rw [mul_add]
      linarith
    exact lt_of_mul_lt_mul_left h4 hω.le
  /- Step 4: `μ`-a.e. every density value is `≥ 1`. -/
  have hae : ∀ᵐ x ∂V.weight, ∀ θ' : ℝ, V.HasDensity x θ' → 1 ≤ θ' := by
    filter_upwards [hdens, hA.2.2.1] with x hx1 hx2 θ' hθ'
    have h1 : 1 ≤ ENNReal.ofReal θ' := by
      rw [hunique x θ' (V.mult x) hθ' hx1]
      exact ENNReal.one_le_ofReal.2 hx2
    exact ENNReal.one_le_ofReal.1 h1
  /- Step 5: conclusion. -/
  have hysupp : y ∈ V.weight.support := (show y ∈ U ∩ V.weight.support from hy.1).2
  obtain ⟨θ, hθ0, hθ⟩ := hex y hy.2
  have hθ1 : 1 ≤ θ := by
    by_contra hlt
    have hlt : θ < 1 := not_le.1 hlt
    obtain ⟨d, hd, hball⟩ := husc y hy.2 θ hθ0 hθ ((1 - θ) / 2) (by linarith)
    have hzero : V.weight (ball y d) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hae] with x hx hxb
      obtain ⟨hxW, hlt'⟩ := hball x hxb
      obtain ⟨θ', hθ'0, hθ'⟩ := hex x hxW
      have h1 := hx θ' hθ'
      have h2 := hlt' θ' hθ'0 hθ'
      linarith
    have hpos := (Measure.mem_support_iff_forall y).1 hysupp (ball y d) (ball_mem_nhds y hd)
    rw [hzero] at hpos
    exact lt_irrefl _ hpos
  have h1 : 1 ≤ ENNReal.ofReal t := by
    rw [hunique y t θ ht hθ]
    exact ENNReal.one_le_ofReal.2 hθ1
  exact ENNReal.one_le_ofReal.1 h1
```

## Key steps

1. Densities are unique: two values t, t' >= 0 (or t' > 0) of V.HasDensity at the same point coincide
2. subball_bounds and the local forms of (T0), (T1) let annular_monotonicity act at every x in B°_rho(0) with any radius R' <= rho - |x| and Lambda = delta/kappa; this gives Theta(x) and the bound (2.1)
3. Upper semicontinuity of Theta on B°_rho(0) from (2.1) with a common radius R_0, the density limit at x and continuity of mu on shrinking closed balls
4. Theta = theta >= 1 mu-a.e. by (T3), theta >= 1 a.e. and uniqueness
5. An open set where Theta < 1 is mu-null, hence misses spt mu; so Theta(y) >= 1 and every density value t at y equals Theta(y)

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
