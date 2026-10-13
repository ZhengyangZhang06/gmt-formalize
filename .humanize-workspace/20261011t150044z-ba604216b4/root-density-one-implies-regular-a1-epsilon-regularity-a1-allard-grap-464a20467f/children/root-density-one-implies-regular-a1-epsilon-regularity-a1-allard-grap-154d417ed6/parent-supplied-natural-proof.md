# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.cone_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 5, 'For y₁, y₂ ∈ G: |Q(y₂ − y₁)| ≤ C₈βL|y₂ − y₁|'. The first case is Simon Ch. 5, proof of 2.6, (3)–(4). The second case (t > σ₀/2) is the parent's correction: Simon treats only the first.
In the parent's application:
- μ = R.measure and τ = approxTangentPlane n R.carrier;
- ε = δ^α;
- (H1) is the sibling affine approximation at (y, t);
- (H2) is the lower density bound (b);
- (H3) is the parent hypothesis (ii).
Notation: P := T₀.starProjection, Qu := u − Pu, p_x := (τ x).starProjection, |A|² := Σ_i ‖A e_i‖² (so the integrands are ofReal|p_x − p_S|² and ofReal|p_x − P|²), ℝ≥0∞-valued lower integrals.
0. Constants. Let ω := (unitBallVolume n).toReal. unitBallVolume n is the Lebesgue measure of the open unit ball of ℝⁿ, which is positive (measure_ball_pos) and finite (measure_ball_lt_top). Hence ω > 0 and unitBallVolume n = ofReal ω. Define C₈ := max(C₃ + √((8C₃ + 2^{n+3})/ω), 4C₆) > 0. C₈ is fixed once n, k, C₃, C₆ are given, before μ, τ, T₀, ξ, σ₀, ε, β, L, as the statement's quantifier order requires. The formula happens not to involve k, but the statement claims only dependence on n, k, C₃ and C₆.
1. Hilbert–Schmidt facts.
   (a) ‖Au‖ ≤ |A|·‖u‖ for every linear map A of ℝ^{n+k} and every u. Write u = Σ_i u_i e_i; then Au = Σ_i u_i A e_i, so ‖Au‖ ≤ Σ_i |u_i|‖A e_i‖ ≤ (Σ_i u_i²)^{1/2}(Σ_i ‖A e_i‖²)^{1/2} = ‖u‖·|A| by Cauchy–Schwarz.
   (b) For subspaces S, T₀ and every x: |p_S − P|² ≤ 2|p_x − p_S|² + 2|p_x − P|². Indeed (p_S − P)e_i = (p_x − P)e_i − (p_x − p_S)e_i and ‖a − b‖² ≤ 2‖a‖² + 2‖b‖².
2. Measurability. For a fixed subspace S, the map A ↦ ofReal(Σ_i ‖A e_i − p_S e_i‖²) is continuous on E →L[ℝ] E. Composing it with the a.e. strongly measurable x ↦ p_x (Continuous.comp_aestronglyMeasurable, then aemeasurable) shows that x ↦ ofReal|p_x − p_S|² is μ-a.e. measurable, also for every restriction μ⌞B. The same holds with S = T₀.
3. Reduction. Fix y₁, y₂ as in the statement and put u := y₂ − y₁, t := ‖u‖. If t = 0, then u = 0 and both sides are 0. Assume t > 0.
4. Case 0 < t ≤ σ₀/2.
   (i) (H1) at (y₁, t) gives S with ‖(x − y₁) − p_S(x − y₁)‖ ≤ C₃εt for x ∈ spt μ ∩ B_t(y₁), and ∫_{B_{t/2}(y₁)} ofReal|p_x − p_S|² dμ ≤ ofReal(C₃ε²(t/2)ⁿ). Since y₂ ∈ spt μ and dist(y₂, y₁) = t, ‖u − p_S u‖ ≤ C₃εt.
   (ii) The good-set hypothesis at this t gives ∫_{B_{t/2}(y₁)} ofReal|p_x − P|² dμ ≤ ofReal(β²L²tⁿ).
   (iii) Let h := |p_S − P|² ≥ 0, a constant, and B := B_{t/2}(y₁).
      - Pointwise, ofReal(h) ≤ 2·ofReal|p_x − p_S|² + 2·ofReal|p_x − P|² (fact 1(b), ofReal_add, ofReal_mul).
      - Integrate over B. On the left use setLIntegral_const. On the right use additivity of the lower integral when one summand is a.e.-measurable (lintegral_add_left', by step 2) and pull out the constant 2.
      - Result: ofReal(h)·μ(B) ≤ 2·ofReal(C₃ε²(t/2)ⁿ) + 2·ofReal(β²L²tⁿ).
   (iv) Bound h.
      - (H2) at (y₁, t/2), valid since t/2 ≤ σ₀/4, gives ofReal(ω)·ofReal((t/2)ⁿ) ≤ 2μ(B).
      - Hence ofReal(h·ω·(t/2)ⁿ) ≤ 2·ofReal(h)·μ(B) ≤ ofReal(4C₃ε²(t/2)ⁿ + 4β²L²tⁿ).
      - Both sides are finite, so h·ω·(t/2)ⁿ ≤ 4C₃ε²(t/2)ⁿ + 4β²L²tⁿ (ENNReal.ofReal_le_ofReal_iff).
      - Divide by ω(t/2)ⁿ > 0 and use tⁿ = 2ⁿ(t/2)ⁿ and ε² ≤ β²L² (from 0 ≤ ε ≤ βL): h ≤ (4C₃ε² + 2^{n+2}β²L²)/ω ≤ (8C₃ + 2^{n+3})β²L²/ω.
      - Therefore √h ≤ √((8C₃ + 2^{n+3})/ω)·βL.
   (v) Qu = (u − p_S u) + (p_S − P)u. By (i) and fact 1(a), ‖Qu‖ ≤ C₃εt + √h·t ≤ (C₃ + √((8C₃ + 2^{n+3})/ω))·βL·t ≤ C₈βL‖y₂ − y₁‖, using ε ≤ βL.
5. Case t > σ₀/2.
   - Since 3σ₀/4 ≤ σ₀, y₁ and y₂ lie in spt μ ∩ B_{σ₀}(ξ), so (H3) gives ‖Q(yᵢ − ξ)‖ ≤ C₆εσ₀.
   - Q is linear and Qu = Q(y₂ − ξ) − Q(y₁ − ξ), so ‖Qu‖ ≤ 2C₆εσ₀.
   - Since σ₀ < 2t, ε ≤ βL and C₆ > 0: 2C₆εσ₀ ≤ 4C₆εt ≤ 4C₆βLt ≤ C₈βL‖y₂ − y₁‖. ∎
Formal check. The following declarations compile after import GMT.Ch07.Submission in the comparator scope, with no warnings, using the witness C₈ of step 0. They consist of seven helper theorems with the private prefix Submission.dorag_lip_cone_estimate_aux_ (Hilbert–Schmidt bound, the squared triangle inequality, the pointwise bound of fact 1(b) in ℝ≥0∞, a.e.-measurability, set integration, and two real-arithmetic steps), followed by Submission.dorag_lip_good_set_cone_estimate with the exact frozen type. #print axioms gives propext, Classical.choice, Quot.sound.
/-- Hilbert–Schmidt bound `‖A u‖ ≤ |A| ‖u‖` with `|A|² = ∑ᵢ ‖A eᵢ‖²`. -/
theorem Submission.dorag_lip_cone_estimate_aux_hs_bound {N : ℕ}
    (A : Euclid N →L[ℝ] Euclid N) (u : Euclid N) :
    ‖A u‖ ≤ Real.sqrt (∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖u‖ := by
  have hu : u = ∑ i : Fin N, u i • EuclideanSpace.single i (1 : ℝ) := by
    have := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr u
    simpa using this.symm
  have hAu : A u = ∑ i : Fin N, u i • A (EuclideanSpace.single i (1 : ℝ)) := by
    conv_lhs => rw [hu]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul A _ _
  have h1 : ‖A u‖ ≤ ∑ i : Fin N, |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
    rw [hAu]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_smul, Real.norm_eq_abs]
  have h2 : (∑ i : Fin N, |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 ≤
      (∑ i : Fin N, |u i| ^ 2) * ∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ∑ i : Fin N, |u i| ^ 2 = ‖u‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => sq_abs _
  rw [h3] at h2
  have h4 : ∑ i : Fin N, |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ ≤
      Real.sqrt (‖u‖ ^ 2 * ∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) :=
    (le_abs_self _).trans (Real.abs_le_sqrt h2)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h4
  calc ‖A u‖ ≤ _ := h1
    _ ≤ _ := h4
    _ = _ := mul_comm _ _

/-- `‖b - c‖² ≤ 2‖a - b‖² + 2‖a - c‖²`. -/
theorem Submission.dorag_lip_cone_estimate_aux_sq_tri {E : Type*} [SeminormedAddCommGroup E]
    (a b c : E) : ‖b - c‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖a - c‖ ^ 2 := by
  have h : ‖b - c‖ ≤ ‖a - b‖ + ‖a - c‖ := by
    calc ‖b - c‖ = ‖(a - c) - (a - b)‖ := by congr 1; abel
      _ ≤ ‖a - c‖ + ‖a - b‖ := norm_sub_le _ _
      _ = ‖a - b‖ + ‖a - c‖ := add_comm _ _
  have h0 : 0 ≤ ‖b - c‖ := norm_nonneg _
  have hab := norm_nonneg (a - b)
  have hac := norm_nonneg (a - c)
  have hsq : ‖b - c‖ * ‖b - c‖ ≤ (‖a - b‖ + ‖a - c‖) * (‖a - b‖ + ‖a - c‖) :=
    mul_le_mul h h h0 (by positivity)
  nlinarith [sq_nonneg (‖a - b‖ - ‖a - c‖)]

/-- Pointwise Hilbert–Schmidt triangle bound, in `ℝ≥0∞`. -/
theorem Submission.dorag_lip_cone_estimate_aux_pt {N : ℕ} (A B C : Euclid N →L[ℝ] Euclid N) :
    ENNReal.ofReal (∑ i : Fin N, ‖B (EuclideanSpace.single i (1 : ℝ)) -
        C (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤
      2 * ENNReal.ofReal (∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ)) -
        B (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) +
      2 * ENNReal.ofReal (∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ)) -
        C (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
  have hle : ∑ i : Fin N, ‖B (EuclideanSpace.single i (1 : ℝ)) -
        C (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤
      2 * ∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ)) -
        B (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 +
      2 * ∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ)) -
        C (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => Submission.dorag_lip_cone_estimate_aux_sq_tri _ _ _
  refine (ENNReal.ofReal_le_ofReal hle).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- a.e.-measurability of the tilt integrand. -/
theorem Submission.dorag_lip_cone_estimate_aux_aemeas {N : ℕ} {μ : Measure (Euclid N)}
    {τ : Euclid N → Submodule ℝ (Euclid N)} (S : Submodule ℝ (Euclid N))
    (hτ : AEStronglyMeasurable (fun x => (τ x).starProjection) μ) :
    AEMeasurable (fun x => ENNReal.ofReal (∑ i : Fin N,
      ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
        S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) μ := by
  have hc : Continuous (fun A : Euclid N →L[ℝ] Euclid N => ENNReal.ofReal (∑ i : Fin N,
      ‖A (EuclideanSpace.single i (1 : ℝ)) -
        S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) := by
    refine ENNReal.continuous_ofReal.comp ?_
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_id.clm_apply continuous_const).sub continuous_const).norm.pow 2
  exact (hc.comp_aestronglyMeasurable hτ).aemeasurable

/-- Integrating a pointwise bound over a set. -/
theorem Submission.dorag_lip_cone_estimate_aux_lint {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {f g : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : AEMeasurable f (μ.restrict s)) (hfg : ∀ x, c ≤ 2 * f x + 2 * g x) :
    c * μ s ≤ 2 * ∫⁻ x in s, f x ∂μ + 2 * ∫⁻ x in s, g x ∂μ := by
  rw [← setLIntegral_const]
  calc ∫⁻ _ in s, c ∂μ ≤ ∫⁻ x in s, (2 * f x + 2 * g x) ∂μ := lintegral_mono hfg
    _ = ∫⁻ x in s, 2 * f x ∂μ + ∫⁻ x in s, 2 * g x ∂μ :=
        lintegral_add_left' (hf.const_mul 2) _
    _ = 2 * ∫⁻ x in s, f x ∂μ + 2 * ∫⁻ x in s, g x ∂μ := by
        rw [lintegral_const_mul' 2 f ENNReal.ofNat_ne_top,
          lintegral_const_mul' 2 g ENNReal.ofNat_ne_top]

/-- From the `ℝ≥0∞` inequalities to a real inequality. -/
theorem Submission.dorag_lip_cone_estimate_aux_real {h w X Y s : ℝ} {m : ℝ≥0∞}
    (hh : 0 ≤ h) (hw : 0 ≤ w) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h1 : ENNReal.ofReal h * m ≤ 2 * ENNReal.ofReal X + 2 * ENNReal.ofReal Y)
    (h2 : ENNReal.ofReal w * ENNReal.ofReal s ≤ 2 * m) :
    h * w * s ≤ 4 * X + 4 * Y := by
  have h3 : ENNReal.ofReal (h * w * s) ≤ ENNReal.ofReal (4 * X + 4 * Y) := by
    calc ENNReal.ofReal (h * w * s)
        = ENNReal.ofReal h * (ENNReal.ofReal w * ENNReal.ofReal s) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hh hw), ENNReal.ofReal_mul hh, mul_assoc]
      _ ≤ ENNReal.ofReal h * (2 * m) := by gcongr
      _ = 2 * (ENNReal.ofReal h * m) := by ring
      _ ≤ 2 * (2 * ENNReal.ofReal X + 2 * ENNReal.ofReal Y) := by gcongr
      _ = ENNReal.ofReal (4 * X + 4 * Y) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat]
          ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

/-- Dividing out the radius factor. -/
theorem Submission.dorag_lip_cone_estimate_aux_div {h w C₃ ε β L s : ℝ} (n : ℕ)
    (hw : 0 < w) (hs : 0 < s) (hC₃ : 0 ≤ C₃) (hε : 0 ≤ ε) (hεβL : ε ≤ β * L)
    (H : h * w * s ≤ 4 * (C₃ * ε ^ 2 * s) + 4 * (β ^ 2 * L ^ 2 * (2 ^ n * s))) :
    h ≤ (8 * C₃ + 2 ^ (n + 3)) / w * (β * L) ^ 2 := by
  have h1 : h * w ≤ 4 * C₃ * ε ^ 2 + 4 * 2 ^ n * (β * L) ^ 2 := by
    have : h * w * s ≤ (4 * C₃ * ε ^ 2 + 4 * 2 ^ n * (β * L) ^ 2) * s := by
      calc h * w * s ≤ _ := H
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hs
  have hε2 : ε ^ 2 ≤ (β * L) ^ 2 := pow_le_pow_left₀ hε hεβL 2
  have h2n : (2:ℝ) ^ (n + 3) = 8 * 2 ^ n := by ring
  have hp : (0:ℝ) ≤ 2 ^ n := by positivity
  have hb : 0 ≤ (β * L) ^ 2 := sq_nonneg _
  have h2 : h * w ≤ (8 * C₃ + 2 ^ (n + 3)) * (β * L) ^ 2 := by
    rw [h2n]
    nlinarith [mul_le_mul_of_nonneg_left hε2 hC₃, mul_nonneg hC₃ hb, mul_nonneg hp hb]
  rw [div_mul_eq_mul_div, le_div_iff₀ hw]
  exact h2

theorem Submission.dorag_lip_good_set_cone_estimate : ∀ (n k : ℕ) (C₃ C₆ : ℝ), 1 ≤ C₃ → 1 ≤ C₆ → ∃ C₈ : ℝ, 0 < C₈ ∧ ∀ (μ : Measure (Euclid (n + k))) (τ : Euclid (n + k) → Submodule ℝ (Euclid (n + k))) (T₀ : Submodule ℝ (Euclid (n + k))) (ξ : Euclid (n + k)) (σ₀ ε β L : ℝ), AEStronglyMeasurable (fun x => (τ x).starProjection) μ → 0 < σ₀ → 0 ≤ ε → 0 < β → 0 < L → ε ≤ β * L → (∀ y ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∃ S : Submodule ℝ (Euclid (n + k)), (∀ x ∈ μ.support ∩ closedBall y t, ‖(x - y) - S.starProjection (x - y)‖ ≤ C₃ * ε * t) ∧ ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal (C₃ * ε ^ 2 * (t / 2) ^ n)) → (∀ y ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 4 → unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ 2 * μ (closedBall y t)) → (∀ x ∈ μ.support ∩ closedBall ξ σ₀, ‖(x - ξ) - T₀.starProjection (x - ξ)‖ ≤ C₆ * ε * σ₀) → ∀ y₁ ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ y₂ ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), (∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∫⁻ x in closedBall y₁ (t / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal (β ^ 2 * L ^ 2 * t ^ n)) → ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖ ≤ C₈ * β * L * ‖y₂ - y₁‖ := by
  intro n k C₃ C₆ hC₃ hC₆
  have hC₃0 : 0 < C₃ := by linarith
  have hvol_pos : 0 < unitBallVolume n := by
    unfold unitBallVolume; exact measure_ball_pos _ _ one_pos
  have hvol_lt : unitBallVolume n < ⊤ := by
    unfold unitBallVolume; exact measure_ball_lt_top
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (unitBallVolume n).toReal := ⟨_, rfl⟩
  have hw_pos : 0 < w := by rw [hw]; exact ENNReal.toReal_pos hvol_pos.ne' hvol_lt.ne
  have hw_eq : unitBallVolume n = ENNReal.ofReal w := by
    rw [hw, ENNReal.ofReal_toReal hvol_lt.ne]
  obtain ⟨K, hK_def⟩ : ∃ K : ℝ, K = (8 * C₃ + 2 ^ (n + 3)) / w := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hK_def]; positivity
  obtain ⟨C₈, hC₈⟩ : ∃ C : ℝ, C = max (C₃ + Real.sqrt K) (4 * C₆) := ⟨_, rfl⟩
  have hC₈a : C₃ + Real.sqrt K ≤ C₈ := by rw [hC₈]; exact le_max_left _ _
  have hC₈b : 4 * C₆ ≤ C₈ := by rw [hC₈]; exact le_max_right _ _
  refine ⟨C₈, by linarith, ?_⟩
  intro μ τ T₀ ξ σ₀ ε β L hmeas hσ₀ hε hβ hL hεβL H1 H2 H3 y₁ hy₁ y₂ hy₂ Hgood
  have hβL : 0 < β * L := mul_pos hβ hL
  rcases (norm_nonneg (y₂ - y₁)).eq_or_lt with ht0 | htpos
  · have hu0 : y₂ - y₁ = 0 := norm_eq_zero.1 ht0.symm
    rw [hu0]; simp
  obtain ⟨t, ht⟩ : ∃ t : ℝ, ‖y₂ - y₁‖ = t := ⟨_, rfl⟩
  rw [ht] at htpos ⊢
  rcases le_or_gt t (σ₀ / 2) with hts | hts
  · -- Case `0 < t ≤ σ₀ / 2`.
    obtain ⟨S, hS1, hS2⟩ := H1 y₁ hy₁ t htpos hts
    have hgood := Hgood t htpos hts
    have hy₂ball : y₂ ∈ μ.support ∩ closedBall y₁ t :=
      ⟨hy₂.1, mem_closedBall.2 (le_of_eq (by rw [dist_eq_norm, ht]))⟩
    have hQS : ‖(y₂ - y₁) - S.starProjection (y₂ - y₁)‖ ≤ C₃ * ε * t := hS1 y₂ hy₂ball
    obtain ⟨h, hh_def⟩ : ∃ h : ℝ, h = ∑ i : Fin (n + k),
        ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := ⟨_, rfl⟩
    have hh0 : 0 ≤ h := by rw [hh_def]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hint := Submission.dorag_lip_cone_estimate_aux_lint (s := closedBall y₁ (t / 2))
      (Submission.dorag_lip_cone_estimate_aux_aemeas S hmeas).restrict
      (fun x => Submission.dorag_lip_cone_estimate_aux_pt ((τ x).starProjection)
        S.starProjection T₀.starProjection)
    rw [← hh_def] at hint
    have hint2 : ENNReal.ofReal h * μ (closedBall y₁ (t / 2)) ≤
        2 * ENNReal.ofReal (C₃ * ε ^ 2 * (t / 2) ^ n) +
          2 * ENNReal.ofReal (β ^ 2 * L ^ 2 * t ^ n) := by
      refine hint.trans ?_
      gcongr
    have hdens := H2 y₁ hy₁ (t / 2) (by positivity) (by linarith)
    rw [hw_eq] at hdens
    have hreal := Submission.dorag_lip_cone_estimate_aux_real hh0 hw_pos.le
      (by positivity) (by positivity) hint2 hdens
    have htn : t ^ n = 2 ^ n * (t / 2) ^ n := by
      rw [← mul_pow]; congr 1; ring
    rw [htn] at hreal
    have hhK : h ≤ K * (β * L) ^ 2 := by
      rw [hK_def]
      exact Submission.dorag_lip_cone_estimate_aux_div n hw_pos (by positivity) hC₃0.le hε
        hεβL hreal
    have hsqrt : Real.sqrt h ≤ Real.sqrt K * (β * L) := by
      calc Real.sqrt h ≤ Real.sqrt (K * (β * L) ^ 2) := Real.sqrt_le_sqrt hhK
        _ = Real.sqrt K * (β * L) := by rw [Real.sqrt_mul hK, Real.sqrt_sq hβL.le]
    have hHS := Submission.dorag_lip_cone_estimate_aux_hs_bound
      (S.starProjection - T₀.starProjection) (y₂ - y₁)
    simp only [_root_.sub_apply] at hHS
    rw [← hh_def, ht] at hHS
    calc ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖
        = ‖((y₂ - y₁) - S.starProjection (y₂ - y₁)) +
            (S.starProjection (y₂ - y₁) - T₀.starProjection (y₂ - y₁))‖ := by
          congr 1; abel
      _ ≤ ‖(y₂ - y₁) - S.starProjection (y₂ - y₁)‖ +
            ‖S.starProjection (y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖ := norm_add_le _ _
      _ ≤ C₃ * ε * t + Real.sqrt h * t := add_le_add hQS hHS
      _ ≤ C₃ * (β * L) * t + Real.sqrt K * (β * L) * t := by
          have e1 : C₃ * ε * t ≤ C₃ * (β * L) * t :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεβL hC₃0.le) htpos.le
          have e2 : Real.sqrt h * t ≤ Real.sqrt K * (β * L) * t :=
            mul_le_mul_of_nonneg_right hsqrt htpos.le
          linarith
      _ = (C₃ + Real.sqrt K) * (β * L * t) := by ring
      _ ≤ C₈ * (β * L * t) := mul_le_mul_of_nonneg_right hC₈a (by positivity)
      _ = C₈ * β * L * t := by ring
  · -- Case `t > σ₀ / 2`.
    have hsub : ∀ y ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), y ∈ μ.support ∩ closedBall ξ σ₀ :=
      fun y hy => ⟨hy.1, closedBall_subset_closedBall (by linarith) hy.2⟩
    have h1 := H3 y₁ (hsub y₁ hy₁)
    have h2 := H3 y₂ (hsub y₂ hy₂)
    have hQ : (y₂ - y₁) - T₀.starProjection (y₂ - y₁) =
        ((y₂ - ξ) - T₀.starProjection (y₂ - ξ)) - ((y₁ - ξ) - T₀.starProjection (y₁ - ξ)) := by
      have e : y₂ - y₁ = (y₂ - ξ) - (y₁ - ξ) := by abel
      rw [e, map_sub T₀.starProjection (y₂ - ξ) (y₁ - ξ)]; abel
    have hC₆0 : 0 ≤ C₆ := by linarith
    have hCε : 0 ≤ C₆ * ε := mul_nonneg hC₆0 hε
    calc ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖
        = ‖((y₂ - ξ) - T₀.starProjection (y₂ - ξ)) -
            ((y₁ - ξ) - T₀.starProjection (y₁ - ξ))‖ := by rw [hQ]
      _ ≤ ‖(y₂ - ξ) - T₀.starProjection (y₂ - ξ)‖ + ‖(y₁ - ξ) - T₀.starProjection (y₁ - ξ)‖ :=
          norm_sub_le _ _
      _ ≤ C₆ * ε * σ₀ + C₆ * ε * σ₀ := add_le_add h2 h1
      _ = 2 * (C₆ * ε) * σ₀ := by ring
      _ ≤ 2 * (C₆ * ε) * (2 * t) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 * C₆ * ε * t := by ring
      _ ≤ 4 * C₆ * (β * L) * t := by
          have : 0 ≤ 4 * C₆ := by linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεβL this) htpos.le
      _ = 4 * C₆ * (β * L * t) := by ring
      _ ≤ C₈ * (β * L * t) := mul_le_mul_of_nonneg_right hC₈b (by positivity)
      _ = C₈ * β * L * t := by ring

## Key steps

1. constants ω = (unitBallVolume n).toReal > 0 and C₈ := max(C₃ + √((8C₃ + 2^{n+3})/ω), 4C₆)
2. Hilbert–Schmidt facts: ‖Au‖ ≤ |A|‖u‖ and |p_S − P|² ≤ 2|p_x − p_S|² + 2|p_x − P|²
3. a.e. measurability of the tilt integrands from the measurability hypothesis
4. case t ≤ σ₀/2: plane S from (H1) at (y₁, t), good-set bound at t, integrate over B_{t/2}(y₁) and use (H2) to get |p_S − P|² ≤ (8C₃ + 2^{n+3})β²L²/ω
5. ‖Q(y₂ − y₁)‖ ≤ C₃εt + |p_S − P|t ≤ C₈βLt
6. case t > σ₀/2 via (H3): ‖Q(y₂ − y₁)‖ ≤ 2C₆εσ₀ ≤ 4C₆βLt ≤ C₈βLt

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d; the workspace lake-manifest.json pins the same mathlib rev and simongmt 2b3663083f3fe399b6296fb8eaee52169170e197)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `rg -n -i 'lipschitz.?approx|LipschitzApproximationLemma|LipschitzGraphCorollary|dorag_lip_' local-references/123e8435b4a2469b/project/GMT`
- `rg -c 'dorag_lip_' local-references/123e8435b4a2469b  (no match)`
- `rg -n "theorem exists_disjoint_subfamily_covering_enlargement_closedBall|theorem LipschitzOnWith.extend_real|lemma measure_compl_support|countable_of_nonempty_interior|lemma exp_le_two_add_div_two_sub|theorem withDensity_apply |theorem lintegral_add_left'|theorem lintegral_const_mul'|theorem setLIntegral_mono'|IsClosed.exists_infDist_eq_dist|lemma isClosed_support|theorem measure_toMeasurable|euclideanHausdorffMeasure_eq_volume|theorem addHaar_closedBall |norm_starProjection_apply_le|starProjection_orthogonal_val" local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lean CheckNames.lean: #check of the 37 Mathlib/SimonGMT declarations cited by the children (all resolve, including Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn)`
- `python3: frozen lean_statement of the four sibling prerequisites (dorag_approxTangent_starProjection_aesm, dorag_monotonicity_density, dorag_standing_density_bounds, dorag_affine_approximation) and of dorag_lipschitz_approximation from dag.json, compared with the assembly's hypotheses and conclusion (all equal)`
- `python3 -I lean_contract.validate_lean_statement on the 8 lean_statements; scan of all 8 workspace dag.json files and GMT/ for dorag_lip_* and the dorag_lip_cone_estimate_aux_/dorag_lip_off_support_aux_ prefixes (no collision)`
- `lean ChallengeAll.lean (8 child types and the frozen parent type elaborate); lean FromFinal.lean (8 child proofs + LipApxAssembly + LipApxFromChildren regenerated from the submitted JSON, exit 0); lean perchild/Child_<key>.lean (each child with only its declared dependency); gmt-compare.py contract_scope emulation cmp/Sol_<key>.lean and cmp/Chal_<key>.lean (all exit 0)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-464a20467f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-464a20467f/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-464a20467f/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/lipapx-v2-work/FromFinal.lean`
- `/tmp/lipapx-v2-work/ChallengeAll.lean`
- `/tmp/lipapx-v2-work/CheckNames.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. The workspace builds against the same Mathlib revision. The snapshot's Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, which form the compiler context of every child.

Nothing in the snapshot proves the selected theorem or any child:
- GMT/Ch05 Contract/Submission (lines 272–309) define LipschitzApproximationLemma and LipschitzGraphCorollary only as Props for a different varifold type. They are used solely in the sorry-backed main_theorem (line 461).
- No dorag_lip_* name occurs in the snapshot.
So no comparator-approved declaration can be reused.

The tools the children cite exist at the pinned revision:
- Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (MeasureTheory/Covering/Vitali.lean:158);
- Set.PairwiseDisjoint.countable_of_nonempty_interior (Topology/Bases.lean:493);
- LipschitzOnWith.extend_real (Topology/MetricSpace/Lipschitz.lean:308);
- IsClosed.exists_infDist_eq_dist (Topology/MetricSpace/HausdorffDistance.lean:615);
- Measure.isClosed_support and Measure.measure_compl_support (MeasureTheory/Measure/Support.lean:115, 202);
- withDensity_apply (WithDensity.lean:44);
- measure_toMeasurable (MeasureSpaceDef.lean:348);
- lintegral_add_left' and lintegral_const_mul' (Integral/Lebesgue/Add.lean:326, 420);
- setLIntegral_mono' (Integral/Lebesgue/Basic.lean:254);
- Real.exp_le_two_add_div_two_sub (Analysis/Complex/Exponential.lean:676);
- Submodule.starProjection_orthogonal_val and norm_starProjection_apply_le (InnerProductSpace/Projection/Basic.lean:203, 411);
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187);
- Measure.addHaar_closedBall (Lebesgue/EqHaar.lean:500);
- SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn, which lies in the contract's import closure.

Lean checks:
- All 8 child types and the frozen parent type elaborate in comparator scope.
- All 8 children are fully proved, warning-free.
- The exact frozen parent type is derived from the 4 frozen sibling types plus the 8 children, using only propext, Classical.choice and Quot.sound.
- No name collides with any DAG reservation.
