# Parent-supplied natural-language proof

- Parent DAG node: `root.poincare_inequality-a1`
- Child DAG node: `root.poincare_inequality-a1.ball_average_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 2 ('Gronwall form of 5.4'), with the Gronwall computation supplied by the sibling integral_gronwall and the sibling theorem weighted_monotonicity_identity supplied as the hypothesis (WMI). Corrections as documented in the parent: the coefficient in 5.2 is Λ (not Λρ), which produces the factor e^{Λ(r−s)}.

0. Notation. μ = V.weight, B_τ = B_τ(y) (closed ball), r > 0 (as 0 < s ≤ r). For τ ∈ ℝ put
f(τ) := τ^{−n} ∫_{B_τ} g dμ,  R(τ) := τ^{−(n+1)} ∫_{B_τ} |x − y| |∇^M g(x)| dμ(x),
Q(τ) := τ^{−(n+1)} ∫_{B_τ} ⟨x − y, ∇^M g(x) + g(x)H(x)⟩ dμ(x),  K_g := ∫_{B_r} |∇^M g(x)| |x − y|^{1−n} dμ(x).
The claim is f(s) ≤ e^{Λ(r−s)} (f(r) + n^{−1}K_g).

1. Preliminary facts. μ(B_τ) < ∞ for every τ by (FV1). Since B_r ⊆ U and g ∈ C¹(U), g is continuous on the compact set B_r, hence bounded there, and g ≥ 0 on B_r. The gradient ∇g is continuous on the open set U, so |∇g| ≤ C₁ on B_r for some C₁; as an orthogonal projection has norm ≤ 1, |∇^M g(x)| = |p_{T_xV}(∇g(x))| ≤ |∇g(x)| ≤ C₁ on B_r. The map x ↦ ∇^M g(x) is μ-a.e. strongly measurable: x ↦ ∇g(x) (the Riesz representative of Dg(x)) is Borel measurable for every function g, x ↦ p_{T_xV} is μ-a.e. strongly measurable by (FV3), and evaluation (L, v) ↦ L v is continuous bilinear. H is μ-integrable on B_r, because V has mean curvature H in U (H is locally integrable on U) and B_r is a compact subset of U. Consequently, for every τ ≤ r the functions g, x ↦ |x − y||∇^M g(x)| (bounded by rC₁) and x ↦ ⟨x − y, ∇^M g(x) + g(x)H(x)⟩ (the first part bounded by rC₁, the second dominated by (sup_{B_r} g)·r|H|) are μ-integrable on B_τ.

2. Integrability in τ. On [s, r] the functions τ ↦ ∫_{B_τ} g dμ and τ ↦ ∫_{B_τ} |x − y||∇^M g| dμ are nondecreasing (nonnegative integrands on B_r, nested balls), hence a.e.-measurable for Lebesgue measure on [s, r]; so f and R are a.e.-measurable on [s, r], and they are bounded there by s^{−n}∫_{B_r} g dμ and s^{−(n+1)}∫_{B_r}|x − y||∇^M g| dμ. Hence f and R are integrable on [s, r]. Moreover R(τ) ≥ 0 for τ > 0. Put P := ∫_{(s,r]} R(τ) dτ ≥ 0.

3. Claim: f(σ) ≤ f(r) + P + Λ ∫_{(σ,r]} f(τ) dτ for every σ ∈ [s, r].
(a) Apply (WMI) with (n, ℓ, V, U, H, h := g, ξ := y, σ, ρ := r). Its hypotheses hold: n ≥ 1, (FV1)–(FV3), U open, H a mean curvature of V in U, g ∈ C¹(U), tsupport g ∩ B_r ⊆ B_r ⊆ U, 0 < σ ≤ r. It yields that Q is integrable on (σ, r] and f(r) − f(σ) = W + ∫_{(σ,r]} Q(τ) dτ, where W := ∫_{B_r∖B_σ} g(x) q_y(x)/|x − y|ⁿ dμ(x).
(b) W ≥ 0: on B_r∖B_σ ⊆ U we have g ≥ 0, q_y = |p^⊥(x − y)|²/|x − y|² ≥ 0 and |x − y|ⁿ ≥ 0.
(c) Let τ ∈ (σ, r]. For μ-a.e. x ∈ B_τ we have x ∈ U, hence |H(x)| ≤ Λ, and by Cauchy–Schwarz, g(x) ≥ 0 and |x − y| ≤ τ:
⟨x − y, ∇^M g + gH⟩ = ⟨x − y, ∇^M g⟩ + g⟨x − y, H⟩ ≥ −|x − y||∇^M g| − g|x − y||H| ≥ −|x − y||∇^M g| − τΛg.
Integrating over B_τ (all functions integrable by step 1): ∫_{B_τ}⟨x − y, ∇^M g + gH⟩ dμ ≥ −∫_{B_τ}|x − y||∇^M g| dμ − τΛ∫_{B_τ} g dμ, and dividing by τ^{n+1} > 0: Q(τ) ≥ −R(τ) − Λ f(τ).
(d) Integrating (c) over (σ, r] (Q, R and f are integrable there): ∫_{(σ,r]} Q ≥ −∫_{(σ,r]} R − Λ∫_{(σ,r]} f. Since R ≥ 0 and (σ, r] ⊆ (s, r], ∫_{(σ,r]} R ≤ P.
(e) Therefore f(σ) = f(r) − W − ∫_{(σ,r]} Q ≤ f(r) + P + Λ∫_{(σ,r]} f.

4. Apply the sibling integral_gronwall with a := s, b := r, Λ, C := f(r) + P and the function f (integrable on [s, r] by step 2; hypothesis = step 3). At s ∈ [s, r] it gives f(s) ≤ (f(r) + P) e^{Λ(r−s)}.

5. Claim: P ≤ n^{−1} K_g. Work with lower integrals and ofReal = ENNReal.ofReal.
(a) For τ ∈ (s, r]: R(τ) = τ^{−n−1}·∫_{B_τ}|x − y||∇^M g| dμ with τ^{−n−1} = 1/τ^{n+1} > 0 and an integrable nonnegative integrand, so ofReal(R(τ)) = ofReal(τ^{−n−1}) ∫_{B_τ} ofReal(|x − y||∇^M g(x)|) dμ(x) = ∫_{B_r} ofReal(τ^{−n−1}) 1_{|x−y|≤τ} ofReal(|x − y||∇^M g(x)|) dμ(x) (B_τ ⊆ B_r).
(b) ofReal(P) = ∫_{(s,r]} ofReal(R(τ)) dτ (R is integrable and nonnegative on (s, r]) = ∫_{(s,r]} ∫_{B_r} (…) dμ dτ = ∫_{B_r} ∫_{(s,r]} (…) dτ dμ by Tonelli; the integrand is a.e.-measurable for (Lebesgue on (s, r]) ⊗ (μ⌞B_r) as a product of a measurable function of τ, the indicator of the closed set {(τ, x) : |x − y| ≤ τ}, and an a.e.-measurable function of x.
(c) Fix x ∈ B_r and put d := |x − y|. If d = 0 the integrand vanishes identically. If d > 0, the inner integral is at most ofReal(d|∇^M g(x)|) ∫_{[d,∞)} ofReal(τ^{−n−1}) dτ = ofReal(d|∇^M g(x)|)·ofReal(∫_d^∞ τ^{−n−1} dτ) = ofReal(d|∇^M g(x)|·d^{−n}/n) = ofReal(n^{−1}|∇^M g(x)| d^{1−n}) (the exponent −n−1 < −1, and [d, ∞) and (d, ∞) differ by a null set).
(d) Hence ofReal(P) ≤ ∫_{B_r} ofReal(n^{−1}|∇^M g(x)||x − y|^{1−n}) dμ(x) = ofReal(n^{−1}K_g), the integrand being μ-integrable on B_r by hypothesis; since n^{−1}K_g ≥ 0, P ≤ n^{−1}K_g.

6. As e^{Λ(r−s)} > 0, steps 4 and 5 give f(s) ≤ (f(r) + P)e^{Λ(r−s)} ≤ e^{Λ(r−s)}(f(r) + n^{−1}K_g), which is the assertion. ∎

Remark (used by the parent for the growth bound): for g ≡ 1 one has ∇^M g = 0, so K_g = 0 and the estimate reads μ(B_s(y))/sⁿ ≤ e^{Λ(r−s)} μ(B_r(y))/rⁿ.

Formalization notes (Mathlib/Lean names used in a machine-checked transcription of the numbered argument): IsCompact.exists_bound_of_continuousOn, ContDiffOn.continuousOn_fderiv_of_isOpen, Submodule.norm_starProjection_apply_le, measurable_fderiv, ContinuousLinearMap.aestronglyMeasurable_comp₂, LocallyIntegrableOn.integrableOn_compact_subset, AEStronglyMeasurable.inner, Integrable.bdd_mul, aemeasurable_restrict_of_monotoneOn, Integrable.of_bound, integral_mono_ae, setIntegral_mono_on, setIntegral_mono_set, ofReal_integral_eq_lintegral_ofReal, lintegral_lintegral_swap, AEMeasurable.comp_snd, AEMeasurable.indicator, Ioi_ae_eq_Ici, integrableOn_Ioi_rpow_of_lt, integral_Ioi_rpow_of_lt.

Appendix (machine-checked reference transcription; the numbered argument above is the proof). The following tactic block is the proof (the text after `:= by`) of the declaration `theorem bounded_curvature_ball_average_estimate` with exactly the frozen lean_statement above as its type, inside `namespace Submission` (scope `open MeasureTheory Metric Set Filter Topology`, `open scoped ENNReal ContDiff CompactlySupported`, `namespace GMT.Ch04`, `noncomputable section`, `open RectifiableVarifold`, after `import GMT.Ch04.Submission`), compiles with Lean v4.35.0-rc3 / Mathlib 25730c7c and depends only on propext, Classical.choice and Quot.sound. Extra imports: `Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner`, `Mathlib.Analysis.SpecialFunctions.ImproperIntegrals`. The script calls the sibling child as `Submission.backward_integral_gronwall_Ioc`.
```lean
  intro hWMI n ℓ V U H Λ g y r s hn hFV1 hFV2 hFV3 hU hH hΛ hHΛ hg hg0 hball hs hsr hint
  haveI := hFV1
  set μ := V.weight with hμ
  have hr : 0 < r := hs.trans_le hsr
  have hgcont : ContinuousOn g U := hg.continuousOn
  -- bounds on the closed ball of radius r
  obtain ⟨Cg0, hCg0⟩ : ∃ C, ∀ x ∈ closedBall y r, ‖g x‖ ≤ C :=
    (isCompact_closedBall y r).exists_bound_of_continuousOn (hgcont.mono hball)
  have hgradcont : ContinuousOn (gradient g) U :=
    (InnerProductSpace.toDual ℝ (Ambient n ℓ)).symm.continuous.comp_continuousOn
      (hg.continuousOn_fderiv_of_isOpen hU le_rfl)
  obtain ⟨Cg1, hCg1⟩ : ∃ C, ∀ x ∈ closedBall y r, ‖gradient g x‖ ≤ C :=
    (isCompact_closedBall y r).exists_bound_of_continuousOn (hgradcont.mono hball)
  have hTGbound : ∀ x ∈ closedBall y r, ‖V.tangentialGradient g x‖ ≤ Cg1 := fun x hx =>
    (Submodule.norm_starProjection_apply_le _ _).trans (hCg1 x hx)
  have hTGmeas : AEStronglyMeasurable (V.tangentialGradient g) μ := by
    have hgm : Measurable (gradient g) :=
      (InnerProductSpace.toDual ℝ (Ambient n ℓ)).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
    exact (ContinuousLinearMap.id ℝ (Ambient n ℓ →L[ℝ] Ambient n ℓ)).aestronglyMeasurable_comp₂
      hFV3 hgm.aestronglyMeasurable
  have hfinB : ∀ τ : ℝ, IsFiniteMeasure (μ.restrict (closedBall y τ)) := fun τ => ⟨by
    rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall y τ).measure_lt_top⟩
  have hsubB : ∀ τ ≤ r, closedBall y τ ⊆ closedBall y r := fun τ hτ => closedBall_subset_closedBall hτ
  -- integrability on balls
  have hgint : ∀ τ ≤ r, IntegrableOn g (closedBall y τ) μ := fun τ hτ =>
    (hgcont.mono ((hsubB τ hτ).trans hball)).integrableOn_compact (isCompact_closedBall y τ)
  have hFint : ∀ τ ≤ r, IntegrableOn (fun x => ‖x - y‖ * ‖V.tangentialGradient g x‖) (closedBall y τ) μ := by
    intro τ hτ
    haveI := hfinB τ
    refine Integrable.of_bound (C := r * Cg1)
      (((continuous_id.sub continuous_const).norm.aestronglyMeasurable).mul hTGmeas.norm).restrict ?_
    refine (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : ‖x - y‖ ≤ r := by rw [← dist_eq_norm]; exact (mem_closedBall.1 hx).trans hτ
    exact mul_le_mul h1 (hTGbound x (hsubB τ hτ hx)) (norm_nonneg _) hr.le
  have hHint : IntegrableOn H (closedBall y r) μ :=
    hH.1.integrableOn_compact_subset hball (isCompact_closedBall y r)
  -- integrability of the inner integrand on balls
  have hsubm : AEStronglyMeasurable (fun x : Ambient n ℓ => x - y) μ :=
    (continuous_sub_right y).aestronglyMeasurable
  have hQint : ∀ τ ≤ r, IntegrableOn
      (fun x => inner ℝ (x - y) (V.tangentialGradient g x + g x • H x)) (closedBall y τ) μ := by
    intro τ hτ
    haveI := hfinB τ
    have h1 : IntegrableOn (fun x => inner ℝ (x - y) (V.tangentialGradient g x)) (closedBall y τ) μ := by
      refine Integrable.of_bound (C := r * Cg1) ?_ ?_
      · exact (hsubm.inner hTGmeas).restrict
      · refine (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_)
        refine (norm_inner_le_norm _ _).trans ?_
        have h1 : ‖x - y‖ ≤ r := by rw [← dist_eq_norm]; exact (mem_closedBall.1 hx).trans hτ
        exact mul_le_mul h1 (hTGbound x (hsubB τ hτ hx)) (norm_nonneg _) hr.le
    have hHτ : IntegrableOn (fun x => inner ℝ (x - y) (H x)) (closedBall y τ) μ := by
      have hH' := hHint.mono_set (hsubB τ hτ)
      refine (hH'.norm.const_mul r).mono' (hsubm.restrict.inner hH'.aestronglyMeasurable) ?_
      refine (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_)
      refine (norm_inner_le_norm _ _).trans ?_
      have h1 : ‖x - y‖ ≤ r := by rw [← dist_eq_norm]; exact (mem_closedBall.1 hx).trans hτ
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h2 : IntegrableOn (fun x => g x * inner ℝ (x - y) (H x)) (closedBall y τ) μ := by
      refine Integrable.bdd_mul (c := Cg0) hHτ ?_ ?_
      · exact (hgcont.mono ((hsubB τ hτ).trans hball)).aestronglyMeasurable measurableSet_closedBall
      · exact (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx =>
          hCg0 x (hsubB τ hτ hx))
    refine (h1.add h2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, inner_add_right, inner_smul_right]
  -- the radial functions
  set f : ℝ → ℝ := fun τ => (∫ x in closedBall y τ, g x ∂μ) / τ ^ n with hf
  set R : ℝ → ℝ := fun τ =>
    (∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) / τ ^ (n + 1) with hR
  have hg0B : ∀ x ∈ closedBall y r, 0 ≤ g x := fun x hx => hg0 x (hball hx)
  -- monotonicity in τ of the ball integrals of nonnegative functions
  have hmonog : MonotoneOn (fun τ => ∫ x in closedBall y τ, g x ∂μ) (Icc s r) := by
    intro a ha b hb hab
    exact setIntegral_mono_set (hgint b hb.2)
      ((ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx =>
        hg0B x (hsubB b hb.2 hx)))
      (Eventually.of_forall (closedBall_subset_closedBall hab))
  have hmonoF : MonotoneOn (fun τ => ∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ)
      (Icc s r) := by
    intro a ha b hb hab
    exact setIntegral_mono_set (hFint b hb.2)
      (Eventually.of_forall fun x => by positivity)
      (Eventually.of_forall (closedBall_subset_closedBall hab))
  have hIg_nonneg : ∀ τ, 0 ≤ ∫ x in closedBall y τ, g x ∂μ ∨ r < τ := by
    intro τ
    by_cases hτ : τ ≤ r
    · exact Or.inl (setIntegral_nonneg measurableSet_closedBall fun x hx => hg0B x (hsubB τ hτ hx))
    · exact Or.inr (not_le.1 hτ)
  haveI : IsFiniteMeasure (volume.restrict (Icc s r)) := ⟨by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hfint : IntegrableOn f (Icc s r) := by
    refine Integrable.of_bound (C := (∫ x in closedBall y r, g x ∂μ) / s ^ n) ?_ ?_
    · exact ((aemeasurable_restrict_of_monotoneOn measurableSet_Icc hmonog).div
        (continuous_pow n).aemeasurable).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun τ hτ => ?_)
      have hτ0 : 0 < τ := hs.trans_le hτ.1
      have hI0 : 0 ≤ ∫ x in closedBall y τ, g x ∂μ :=
        setIntegral_nonneg measurableSet_closedBall fun x hx => hg0B x (hsubB τ hτ.2 hx)
      rw [Real.norm_of_nonneg (div_nonneg hI0 (pow_pos hτ0 n).le)]
      calc (∫ x in closedBall y τ, g x ∂μ) / τ ^ n ≤ (∫ x in closedBall y r, g x ∂μ) / τ ^ n :=
            div_le_div_of_nonneg_right (hmonog hτ ⟨hsr, le_rfl⟩ hτ.2) (pow_pos hτ0 n).le
        _ ≤ (∫ x in closedBall y r, g x ∂μ) / s ^ n :=
            div_le_div_of_nonneg_left (setIntegral_nonneg measurableSet_closedBall hg0B)
              (pow_pos hs n) (pow_le_pow_left₀ hs.le hτ.1 n)
  have hRint : IntegrableOn R (Icc s r) := by
    refine Integrable.of_bound
      (C := (∫ x in closedBall y r, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) / s ^ (n + 1)) ?_ ?_
    · exact ((aemeasurable_restrict_of_monotoneOn measurableSet_Icc hmonoF).div
        (continuous_pow (n + 1)).aemeasurable).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun τ hτ => ?_)
      have hτ0 : 0 < τ := hs.trans_le hτ.1
      have hI0 : 0 ≤ ∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ :=
        setIntegral_nonneg measurableSet_closedBall fun x _ => by positivity
      rw [Real.norm_of_nonneg (div_nonneg hI0 (pow_pos hτ0 _).le)]
      calc (∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) / τ ^ (n + 1)
          ≤ (∫ x in closedBall y r, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) / τ ^ (n + 1) :=
            div_le_div_of_nonneg_right (hmonoF hτ ⟨hsr, le_rfl⟩ hτ.2) (pow_pos hτ0 _).le
        _ ≤ (∫ x in closedBall y r, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) / s ^ (n + 1) :=
            div_le_div_of_nonneg_left
              (setIntegral_nonneg measurableSet_closedBall fun x _ => by positivity)
              (pow_pos hs _) (pow_le_pow_left₀ hs.le hτ.1 _)
  have hR0 : ∀ τ, 0 < τ → 0 ≤ R τ := fun τ hτ =>
    div_nonneg (integral_nonneg fun x => by positivity) (pow_pos hτ _).le
  set P := ∫ τ in Ioc s r, R τ with hP
  have hP0 : 0 ≤ P := setIntegral_nonneg measurableSet_Ioc fun τ hτ => hR0 τ (hs.trans hτ.1)
  have hstepA : ∀ σ ∈ Icc s r, f σ ≤ (f r + P) + Λ * ∫ τ in Ioc σ r, f τ := by
    intro σ hσ
    have hσ0 : 0 < σ := hs.trans_le hσ.1
    obtain ⟨hQi, -, hid⟩ := hWMI n ℓ V U H g y σ r hn hFV1 hFV2 hFV3 hU hH hg
      (fun x hx => hball hx.2) hσ0 hσ.2
    have hW0 : 0 ≤ ∫ x in closedBall y r \ closedBall y σ,
        g x * (V.normalRadialSq y x / ‖x - y‖ ^ n) ∂μ := by
      refine setIntegral_nonneg (measurableSet_closedBall.diff measurableSet_closedBall) fun x hx => ?_
      have : 0 ≤ V.normalRadialSq y x := by unfold RectifiableVarifold.normalRadialSq; positivity
      exact mul_nonneg (hg0B x hx.1) (div_nonneg this (by positivity))
    have hQlow : ∀ τ ∈ Ioc σ r, -R τ - Λ * f τ ≤
        (∫ x in closedBall y τ, inner ℝ (x - y) (V.tangentialGradient g x + g x • H x) ∂μ) /
          τ ^ (n + 1) := by
      intro τ hτ
      have hτ0 : 0 < τ := hσ0.trans hτ.1
      have hτr : τ ≤ r := hτ.2
      have hint1 : ∫ x in closedBall y τ, (-(‖x - y‖ * ‖V.tangentialGradient g x‖) - τ * Λ * g x) ∂μ ≤
          ∫ x in closedBall y τ, inner ℝ (x - y) (V.tangentialGradient g x + g x • H x) ∂μ := by
        refine integral_mono_ae ((hFint τ hτr).neg.sub ((hgint τ hτr).const_mul (τ * Λ)))
          (hQint τ hτr) ?_
        filter_upwards [ae_restrict_mem measurableSet_closedBall, ae_restrict_of_ae hHΛ] with x hx hHx
        have hxU : x ∈ U := hball (hsubB τ hτr hx)
        have hgx : 0 ≤ g x := hg0 x hxU
        have hxy : ‖x - y‖ ≤ τ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hx
        have hH1 : ‖H x‖ ≤ Λ := hHx hxU
        have i1 : -(‖x - y‖ * ‖V.tangentialGradient g x‖) ≤ inner ℝ (x - y) (V.tangentialGradient g x) :=
          neg_le_of_abs_le (abs_real_inner_le_norm _ _)
        have i2 : -(‖x - y‖ * ‖H x‖) ≤ inner ℝ (x - y) (H x) := neg_le_of_abs_le (abs_real_inner_le_norm _ _)
        have i3 : ‖x - y‖ * ‖H x‖ ≤ τ * Λ := mul_le_mul hxy hH1 (norm_nonneg _) hτ0.le
        simp only [inner_add_right, inner_smul_right]
        nlinarith [mul_le_mul_of_nonneg_left i3 hgx, mul_le_mul_of_nonneg_left i2 hgx]
      have heq : ∫ x in closedBall y τ, (-(‖x - y‖ * ‖V.tangentialGradient g x‖) - τ * Λ * g x) ∂μ =
          -(∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) -
            τ * Λ * ∫ x in closedBall y τ, g x ∂μ := by
        rw [integral_sub (f := fun x => -(‖x - y‖ * ‖V.tangentialGradient g x‖))
          (g := fun x => τ * Λ * g x) (hFint τ hτr).neg ((hgint τ hτr).const_mul (τ * Λ)),
          integral_neg, integral_const_mul]
      rw [heq] at hint1
      have hpos : (0 : ℝ) < τ ^ (n + 1) := pow_pos hτ0 _
      have hfτ : f τ = (∫ x in closedBall y τ, g x ∂μ) / τ ^ n := rfl
      have hRτ : R τ = (∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) / τ ^ (n + 1) := rfl
      rw [hfτ, hRτ, le_div_iff₀ hpos]
      have hexp : τ ^ (n + 1) = τ ^ n * τ := pow_succ τ n
      have hτn : (0 : ℝ) < τ ^ n := pow_pos hτ0 n
      calc (-((∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) / τ ^ (n + 1)) -
            Λ * ((∫ x in closedBall y τ, g x ∂μ) / τ ^ n)) * τ ^ (n + 1)
          = -(∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) -
            τ * Λ * ∫ x in closedBall y τ, g x ∂μ := by
            rw [hexp]; field_simp
        _ ≤ _ := hint1
    have hT : -(∫ τ in Ioc σ r, R τ) - Λ * ∫ τ in Ioc σ r, f τ ≤
        ∫ τ in Ioc σ r, (∫ x in closedBall y τ, inner ℝ (x - y) (V.tangentialGradient g x + g x • H x) ∂μ) /
          τ ^ (n + 1) := by
      have hsubI : Ioc σ r ⊆ Icc s r := fun τ hτ => ⟨hσ.1.trans hτ.1.le, hτ.2⟩
      have hRi := hRint.mono_set hsubI
      have hfi := hfint.mono_set hsubI
      rw [← integral_neg, ← integral_const_mul, ← integral_sub (f := fun τ => -R τ)
        (g := fun τ => Λ * f τ) hRi.neg (hfi.const_mul Λ)]
      exact setIntegral_mono_on (hRi.neg.sub (hfi.const_mul Λ)) hQi measurableSet_Ioc hQlow
    have hRle : ∫ τ in Ioc σ r, R τ ≤ P := by
      refine setIntegral_mono_set (hRint.mono_set Ioc_subset_Icc_self) ?_ ?_
      · exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ => hR0 τ (hs.trans hτ.1))
      · exact Eventually.of_forall (Ioc_subset_Ioc_left hσ.1)
    have hfr : f r = (∫ x in closedBall y r, g x ∂μ) / r ^ n := rfl
    have hfσ : f σ = (∫ x in closedBall y σ, g x ∂μ) / σ ^ n := rfl
    rw [hfσ, hfr]
    rw [hfr] at *
    linarith
  have hB := Submission.backward_integral_gronwall_Ioc s r Λ (f r + P) f hsr hΛ hfint hstepA s
    ⟨le_rfl, hsr⟩
  set Kg := ∫ x in closedBall y r, ‖V.tangentialGradient g x‖ * ‖x - y‖ ^ (1 - (n : ℝ)) ∂μ with hKg
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hKg0 : 0 ≤ Kg := setIntegral_nonneg measurableSet_closedBall fun x _ => by positivity
  have hstepC : P ≤ (n : ℝ)⁻¹ * Kg := by
    set Fe : Ambient n ℓ → ℝ≥0∞ := fun x => ENNReal.ofReal (‖x - y‖ * ‖V.tangentialGradient g x‖)
      with hFe
    have hFeae : AEMeasurable Fe μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable ((hsubm.norm.mul hTGmeas.norm).aemeasurable)
    have h1 : ENNReal.ofReal P = ∫⁻ τ in Ioc s r, ENNReal.ofReal (R τ) :=
      ofReal_integral_eq_lintegral_ofReal (hRint.mono_set Ioc_subset_Icc_self)
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ => hR0 τ (hs.trans hτ.1)))
    have h2 : ∀ τ ∈ Ioc s r, ENNReal.ofReal (R τ) = ∫⁻ x in closedBall y r,
        ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x ∂μ := by
      intro τ hτ
      have hτ0 : 0 < τ := hs.trans hτ.1
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_closedBall,
        Measure.restrict_restrict measurableSet_closedBall, Set.inter_eq_left.2 (hsubB τ hτ.2),
        ← ofReal_integral_eq_lintegral_ofReal (hFint τ hτ.2) (Eventually.of_forall fun x => by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : τ ^ (-(n : ℝ) - 1) = (τ ^ (n + 1))⁻¹ := by
        rw [show -(n : ℝ) - 1 = -((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hτ0.le,
          Real.rpow_natCast]
      rw [this, hR]
      simp only
      rw [div_eq_inv_mul]
    have hmeasP : MeasurableSet {p : ℝ × Ambient n ℓ | dist p.2 y ≤ p.1} :=
      measurableSet_le (by fun_prop) measurable_fst
    have h3 : ∫⁻ τ in Ioc s r, ∫⁻ x in closedBall y r,
        ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x ∂μ =
        ∫⁻ x in closedBall y r, (∫⁻ τ in Ioc s r,
          ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x) ∂μ := by
      refine lintegral_lintegral_swap ?_
      have heq : Function.uncurry (fun (τ : ℝ) (x : Ambient n ℓ) =>
          ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x) =
          fun p : ℝ × Ambient n ℓ => ENNReal.ofReal (p.1 ^ (-(n : ℝ) - 1)) *
            {p : ℝ × Ambient n ℓ | dist p.2 y ≤ p.1}.indicator (fun p => Fe p.2) p := by
        ext ⟨τ, x⟩
        simp only [Function.uncurry_apply_pair, Set.indicator, mem_closedBall, Set.mem_ofPred_eq]
      rw [heq]
      refine (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).aemeasurable.mul ?_
      exact (hFeae.restrict.comp_snd).indicator hmeasP
    have h4 : ∀ x ∈ closedBall y r, (∫⁻ τ in Ioc s r,
        ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x) ≤
        ENNReal.ofReal ((n : ℝ)⁻¹ * (‖V.tangentialGradient g x‖ * ‖x - y‖ ^ (1 - (n : ℝ)))) := by
      intro x hx
      by_cases hd : ‖x - y‖ = 0
      · have hFe0 : Fe x = 0 := by simp only [hFe, hd, zero_mul, ENNReal.ofReal_zero]
        have : ∀ τ, ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x = 0 := by
          intro τ
          by_cases hm : x ∈ closedBall y τ
          · rw [Set.indicator_of_mem hm, hFe0, mul_zero]
          · rw [Set.indicator_of_notMem hm, mul_zero]
        simp only [this, lintegral_zero]
        exact bot_le
      · have hdpos : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
        have hpt : ∀ τ, ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x =
            (Ici ‖x - y‖).indicator (fun τ => ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * Fe x) τ := by
          intro τ
          by_cases hm : x ∈ closedBall y τ
          · have : ‖x - y‖ ∈ Ici τ ∨ True := Or.inr trivial
            rw [Set.indicator_of_mem hm, Set.indicator_of_mem (by
              rw [mem_closedBall, dist_eq_norm] at hm; exact hm)]
          · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (by
              rw [mem_closedBall, dist_eq_norm] at hm; simpa using hm), mul_zero]
        have hexp : -(n : ℝ) - 1 < -1 := by linarith
        calc ∫⁻ τ in Ioc s r, ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x
            ≤ ∫⁻ τ, ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x :=
              setLIntegral_le_lintegral _ _
          _ = ∫⁻ τ in Ici ‖x - y‖, ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * Fe x := by
              simp_rw [hpt]
              rw [lintegral_indicator measurableSet_Ici]
          _ = ∫⁻ τ in Ioi ‖x - y‖, ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * Fe x :=
              setLIntegral_congr Ioi_ae_eq_Ici.symm
          _ = ENNReal.ofReal (∫ τ in Ioi ‖x - y‖, τ ^ (-(n : ℝ) - 1)) * Fe x := by
              rw [lintegral_mul_const' _ _ (by simp only [hFe]; exact ENNReal.ofReal_ne_top),
                ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hexp hdpos)]
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
              exact Real.rpow_nonneg (hdpos.trans hτ).le _
          _ = ENNReal.ofReal ((n : ℝ)⁻¹ * (‖V.tangentialGradient g x‖ * ‖x - y‖ ^ (1 - (n : ℝ)))) := by
              rw [integral_Ioi_rpow_of_lt hexp hdpos, hFe]
              simp only
              rw [← ENNReal.ofReal_mul (by
                have : -(n : ℝ) - 1 + 1 = -(n : ℝ) := by ring
                rw [this, neg_div_neg_eq]
                positivity)]
              congr 1
              have h1 : -(n : ℝ) - 1 + 1 = -(n : ℝ) := by ring
              rw [h1]
              have h2 : ‖x - y‖ ^ (1 - (n : ℝ)) = ‖x - y‖ * ‖x - y‖ ^ (-(n : ℝ)) := by
                rw [show (1 : ℝ) - n = 1 + (-(n : ℝ)) by ring, Real.rpow_add hdpos, Real.rpow_one]
              rw [h2]
              field_simp
    have h5 : ∫⁻ x in closedBall y r,
        ENNReal.ofReal ((n : ℝ)⁻¹ * (‖V.tangentialGradient g x‖ * ‖x - y‖ ^ (1 - (n : ℝ)))) ∂μ =
        ENNReal.ofReal ((n : ℝ)⁻¹ * Kg) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
        (Eventually.of_forall fun x => by positivity), integral_const_mul]
    have hfinal : ENNReal.ofReal P ≤ ENNReal.ofReal ((n : ℝ)⁻¹ * Kg) := by
      rw [h1, setLIntegral_congr_fun measurableSet_Ioc h2, h3, ← h5]
      exact setLIntegral_mono' measurableSet_closedBall h4
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfinal
  have hexpos : 0 < Real.exp (Λ * (r - s)) := Real.exp_pos _
  have hfs : f s = (∫ x in closedBall y s, g x ∂μ) / s ^ n := rfl
  have hfr : f r = (∫ x in closedBall y r, g x ∂μ) / r ^ n := rfl
  rw [← hfs, ← hfr]
  calc f s ≤ (f r + P) * Real.exp (Λ * (r - s)) := hB
    _ ≤ (f r + (n : ℝ)⁻¹ * Kg) * Real.exp (Λ * (r - s)) := by gcongr
    _ = Real.exp (Λ * (r - s)) * (f r + (n : ℝ)⁻¹ * Kg) := mul_comm _ _
```

## Key steps

1. WMI at radii σ ≤ r: f(r) − f(σ) = W + ∫_{(σ,r]} Q with W ≥ 0
2. |H| ≤ Λ, Cauchy–Schwarz and |x−y| ≤ τ: Q(τ) ≥ −R(τ) − Λf(τ)
3. f(σ) ≤ f(r) + P + Λ∫_{(σ,r]} f for σ ∈ [s, r], with P = ∫_{(s,r]} R and f, R integrable on [s, r]
4. sibling integral_gronwall: f(s) ≤ (f(r) + P)e^{Λ(r−s)}
5. Tonelli: P ≤ n⁻¹∫_{B_r}|∇^M g||x−y|^{1−n} since ∫_d^∞ τ^{−n−1}dτ = d^{−n}/n

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `python3: read lean_name/lean_statement of every node in <run>/dag.json and every */decomposition*.json (uncle frozen types; name-collision check)`
- `rg -n 'theorem|lemma' <snapshot>/mathlib/Mathlib/Analysis/ODE/Gronwall.lean; grep -ril gronwall <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem lintegral_eq_lintegral_meas_lt|theorem lintegral_comp_eq_lintegral_meas_lt_mul|theorem lintegral_lintegral_swap|theorem lintegral_prod_swap' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem measurable_fderiv |theorem measurable_deriv |theorem measurableSet_of_differentiableAt ' <snapshot>/mathlib/Mathlib`
- `rg -n '^theorem|^lemma' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean; rg -n 'gradient_fun_const|gradient_eq' <snapshot>/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `rg -n 'Integrable.bdd_mul|support_mem_ae|norm_starProjection_apply_le|aestronglyMeasurable_comp₂|apply_continuousLinearMap|Monotone.deriv_nonneg|integral_comp_sub_left|integral_deriv_eq_sub|integral_Ioi_rpow_of_lt|integrableOn_Ioi_rpow_of_lt|rpow_inv_lt_iff_of_neg|lt_rpow_inv_iff_of_neg|continuousOn_primitive_interval_left|integral_hasDerivAt_left|monotoneOn_of_deriv_nonneg|aemeasurable_restrict_of_monotoneOn|integrableOn_of_bounded|setIntegral_mono_set|AEMeasurable.comp_snd' <snapshot>/mathlib/Mathlib`
- `grep -rniE 'gronwall|layercake|poincare|monotonicity' lake-packages-25730c7c/simongmt/Poincare; grep -n '^theorem' simongmt/Poincare/SimonGMT/Chapter04/{Poincare,PoincareKernel,PoincareTruncation,LayerCake}.lean`
- `python3: verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch04.main_theorem') and lean_contract.validate_lean_statement on all child statements`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/ch04-poincare-split/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=...:/tmp/ch04-poincare-split/olean lean /tmp/ch04-poincare-split/src/ChildTypes.lean`
- `lean /tmp/ch04-poincare-split/asm/A7.lean (parent assembly from sorried children and byte-identical uncle stubs)`
- `lean /tmp/ch04-poincare-split/kids/K1..K7.lean and /tmp/ch04-poincare-split/full/Full.lean with #print axioms`
- `HUMANIZE_RUN_DIR=/tmp/ch04-poincare-split/fakerun python3 verifier/gmt-compare.py --lean-target GMT/Ch04/Submission.lean --verifier-dir verifier --packages lake-packages-25730c7c --frozen-commit ff75f52a4c9deb3b3abbd91eb31d7b02e29a4cef --dry-run root.poincare_inequality-a1.tangentialGradient_comp_of_differentiableAt-a1`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-poincare-inequality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/ODE/Gronwall.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/ODE/DiscreteGronwall.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/PoincareKernel.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/PoincareTruncation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/LayerCake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ch04-poincare-split/src/ChildTypes.lean`
- `/tmp/ch04-poincare-split/asm/A7.lean`
- `/tmp/ch04-poincare-split/full/Full.lean`

The snapshot contract (sha256 6e58e5dd…0f4770b) is byte-identical to the workspace Contract.lean and Submission.lean. The Mathlib (25730c7c) and SimonGMT (2b366308) revisions match the project manifest. The pinned Mathlib has no integral-form Gronwall inequality (only Analysis/ODE/Gronwall.lean, which is differential, and DiscreteGronwall.lean), so integral_gronwall is a genuine new obligation. Mathlib supplies the other ingredients: the layer-cake formula (lintegral_eq_lintegral_meas_lt), Tonelli (lintegral_lintegral_swap), measurable_fderiv for arbitrary functions, Real.smoothTransition, improper rpow integrals (integral_Ioi_rpow_of_lt) and FTC/monotonicity lemmas. SimonGMT has an earlier Poincaré development (Chapter04/Poincare.lean, PoincareKernel.lean, PoincareTruncation.lean), but it is stated for the strengthened Chapter04.RectifiableVarifold, which the Ch04 README says needs a transport construction, so it is not reused. Its generic kernel and truncation lemmas have different hypotheses, and the children were proved without them. All seven child types elaborate in the exact comparator scope and pass the comparator's statement validator, and a comparator dry run generates the expected challenge and solution modules. All children have machine-checked Lean proofs using only propext, Classical.choice and Quot.sound. The selected frozen type compiles from the seven children plus the byte-identical uncle types, with no other sorry.
