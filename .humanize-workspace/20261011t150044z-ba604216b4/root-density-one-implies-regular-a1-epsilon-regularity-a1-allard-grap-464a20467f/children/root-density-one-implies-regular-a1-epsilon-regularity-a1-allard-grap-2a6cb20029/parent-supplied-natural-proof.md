# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.off_support-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 8, estimate (10'). It corrects Simon Ch. 5, proof of 2.6, (9)–(10): Simon's B_σ(η) becomes B_{3s}(η), and since H is bounded (here only κσ₀ ≤ 1 is used) no additive error Cδσⁿ occurs.
In the parent's application:
- F is the Lipschitz graph, with cone constant λ = 2√kC₈βL;
- (Da) and (Db) are the density bounds (a) and (b);
- (M2) is the second monotonicity inequality of the sibling dorag_monotonicity_density.
Notation: E := ℝ^{n+k}; P := T₀.starProjection, Qu := u − Pu; p_x := (τ x).starProjection, p_x^⊥u := u − p_x u; |A|² := Σ_i ‖A e_i‖²; ω := (unitBallVolume n).toReal. The open unit ball of ℝⁿ has positive finite measure, so ω ∈ (0, ∞) and unitBallVolume n = ofReal ω. Write λ for lam.
0. Constants. λ₀ := 1/√(288·15ⁿ) > 0 and C₉ := 144·3ⁿ/ω > 0. They are fixed once n and k are given, before μ, τ, T₀, F, ξ, σ₀, κ, λ, as the statement's quantifier order requires. The formulas happen not to involve k, but the statement claims only dependence on n and k. For 0 ≤ λ ≤ λ₀ we have λ² ≤ 1/(288·15ⁿ), i.e. 72·15ⁿλ² ≤ 1/4.
Let μ, τ, T₀, F, ξ, σ₀, κ, λ satisfy the hypotheses and let η ∈ (F ∖ spt μ) ∩ B_{σ₀/4}(ξ).
1. Nearest point.
   - spt μ is closed (Measure.isClosed_support), nonempty (it contains ξ), and η ∉ spt μ.
   - Let d := infDist(η, spt μ). Then d > 0 (IsClosed.notMem_iff_infDist_pos) and d ≤ dist(η, ξ) (infDist_le_dist_of_mem).
   - d = dist(η, y) for some y ∈ spt μ (IsClosed.exists_infDist_eq_dist; E is proper).
   - Put s := d/2. Then s > 0, 2s ≤ dist(η, ξ) ≤ σ₀/4 (so s ≤ σ₀/8) and dist(y, η) = 2s.
   - Also dist(y, ξ) ≤ dist(y, η) + dist(η, ξ) ≤ 2·dist(η, ξ) ≤ σ₀/2.
   These are the s and y of the conclusion; it remains to prove the inequality.
2. μ(B_s(η)) = 0. If x ∈ B_s(η), then dist(η, x) ≤ s < d, so x ∉ spt μ. Thus B_s(η) ⊆ E ∖ spt μ, and μ(E ∖ spt μ) = 0 (Measure.measure_compl_support; E is second countable).
3. Mass bounds. Since dist(y, η) = 2s, B_s(y) ⊆ B_{3s}(η) ⊆ B_{5s}(y). Put a := μ(B_{3s}(η)).
   - (Db) at (y, s), valid as y ∈ spt μ ∩ B_{σ₀/2}(ξ) and s ≤ σ₀/8: ω sⁿ ≤ 2μ(B_s(y)) ≤ 2a.
   - (Da) at (y, 5s), valid as y ∈ B_{σ₀/2}(ξ) and 5s ≤ 5σ₀/8: a ≤ μ(B_{5s}(y)) ≤ 2ω(5s)ⁿ = 2·5ⁿωsⁿ < ∞.
4. Monotonicity. Apply (M2) at η (η ∈ B_{σ₀/4}(ξ)) with radii s < 3s ≤ 3σ₀/8.
   - By step 2 the term ofReal(e^{−κs}/sⁿ)·μ(B_s(η)) vanishes, so ofReal(e^{−3κs}/(3s)ⁿ)·a ≤ J := ∫_{B_{3s}(η)∖B_s(η)} ofReal(‖p_x^⊥(x − η)‖²/‖x − η‖^{n+2}) dμ.
   - On the annulus ‖x − η‖ > s > 0, so the integrand is ≤ ofReal(1/s^{n+2})·ofReal(‖p_x^⊥(x − η)‖²) (setLIntegral_mono' on the measurable annulus).
   - Pull out the finite constant (lintegral_const_mul') and enlarge the domain (lintegral_mono_set): J ≤ ofReal(1/s^{n+2})·I₂, where I₂ := ∫_{B_{3s}(η)} ofReal(‖p_x^⊥(x − η)‖²) dμ.
5. Exponential factor.
   - 0 ≤ 3κs ≤ 3κσ₀/8 ≤ 3/8. Hence e^{3κs} ≤ (2 + 3κs)/(2 − 3κs) ≤ 2 (Real.exp_le_two_add_div_two_sub, and 3κs ≤ 2/3).
   - Multiply step 4 by ofReal(e^{3κs}(3s)ⁿ), using ofReal(e^{3κs}(3s)ⁿ)·ofReal(e^{−3κs}/(3s)ⁿ) = 1: a ≤ ofReal(e^{3κs}·3ⁿ/s²)·I₂ ≤ ofReal(2·3ⁿ/s²)·I₂.
6. Pointwise bound on B_{3s}(η).
   - Since p_x^⊥(x − η) = Q(x − η) + (P − p_x)(x − η), ‖p_x^⊥(x − η)‖² ≤ 2‖Q(x − η)‖² + 2‖(P − p_x)(x − η)‖².
   - The Hilbert–Schmidt bound ‖Au‖ ≤ |A|‖u‖ (expand u = Σ u_i e_i and apply Cauchy–Schwarz), with A = P − p_x (note ‖(P − p_x)e_i‖ = ‖p_x e_i − P e_i‖) and ‖x − η‖ ≤ 3s, gives ‖(P − p_x)(x − η)‖² ≤ 9s²|p_x − P|².
   - If x ∈ F, then (F) with x, η ∈ F gives ‖Q(x − η)‖ ≤ λ‖x − η‖ ≤ 3λs.
   - If x ∉ F, then ‖Q(x − η)‖ ≤ ‖x − η‖ ≤ 3s, since Q is the orthogonal projection onto T₀^⊥ (Submodule.starProjection_orthogonal_val, Submodule.norm_starProjection_apply_le).
   - Let M := toMeasurable μ (B_{3s}(η) ∖ F). It is measurable, contains B_{3s}(η) ∖ F, and has μ(M) = μ(B_{3s}(η) ∖ F); no measurability of F is assumed.
   - Hence for every x ∈ B_{3s}(η): ‖p_x^⊥(x − η)‖² ≤ 18λ²s² + 18s²·1_M(x) + 18s²|p_x − P|².
7. Integration. Integrate step 6 over B_{3s}(η).
   - The first two summands are measurable, so the lower integral is additive (lintegral_add_left). Constants and indicators are handled by setLIntegral_const and lintegral_indicator, the last summand by lintegral_const_mul'.
   - Result: I₂ ≤ ofReal(18λ²s²)·a + ofReal(18s²)·μ(M ∩ B_{3s}(η)) + ofReal(18s²)·X₂ ≤ ofReal(18λ²s²)·a + ofReal(18s²)·X₁ + ofReal(18s²)·X₂, where X₁ := μ(B_{3s}(η) ∖ F) and X₂ := ∫_{B_{3s}(η)} ofReal|p_x − P|² dμ.
8. Absorption.
   - Steps 5 and 7 give a ≤ ofReal(36·3ⁿλ²)·a + ofReal(36·3ⁿ)·(X₁ + X₂).
   - By step 3 and step 0: ofReal(36·3ⁿλ²)·a ≤ ofReal(36·3ⁿλ²·2·5ⁿωsⁿ) = ofReal(72·15ⁿλ²·ωsⁿ) ≤ ofReal(ωsⁿ/4).
   - With ofReal(ωsⁿ) ≤ 2a (step 3): ofReal(ωsⁿ/2) ≤ a ≤ ofReal(ωsⁿ/4) + ofReal(36·3ⁿ)·(X₁ + X₂).
   - Since ofReal(ωsⁿ/4) < ∞ and ofReal(ωsⁿ/2) = ofReal(ωsⁿ/4) + ofReal(ωsⁿ/4), it can be cancelled: ofReal(ωsⁿ/4) ≤ ofReal(36·3ⁿ)·(X₁ + X₂).
   - Multiplying by ofReal(4/ω): ofReal(sⁿ) ≤ ofReal(144·3ⁿ/ω)·(X₁ + X₂) = ofReal(C₉)·(μ(B_{3s}(η) ∖ F) + ∫_{B_{3s}(η)} ofReal|p_x − P|² dμ). This is the asserted inequality. ∎
Formal check. The following declarations compile after import GMT.Ch07.Submission in the comparator scope, with no warnings, using the witnesses λ₀ = 1/√(288·15ⁿ) and C₉ = 144·3ⁿ/ω of step 0. They consist of six helper theorems with the private prefix Submission.dorag_lip_off_support_aux_ (Hilbert–Schmidt bound, the real pointwise split, the ℝ≥0∞ pointwise bound in the cases x ∈ F and x ∉ F, steps 4–5, the λ-condition, and the step-8 absorption), followed by Submission.dorag_lip_off_support_estimate with the exact frozen type. No measurability of τ or F is used. #print axioms gives propext, Classical.choice, Quot.sound.
/-- Hilbert–Schmidt bound: `‖A u‖² ≤ (∑ᵢ ‖A eᵢ‖²) ‖u‖²`. -/
theorem Submission.dorag_lip_off_support_aux_hs {N : ℕ} (A : Euclid N →L[ℝ] Euclid N)
    (u : Euclid N) :
    ‖A u‖ ^ 2 ≤ (∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖u‖ ^ 2 := by
  have hu : ∑ i : Fin N, u i • EuclideanSpace.single i (1 : ℝ) = u := by
    have h := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr u
    simpa using h
  have hAu : A u = ∑ i : Fin N, u i • A (EuclideanSpace.single i (1 : ℝ)) := by
    conv_lhs => rw [← hu]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul A _ _
  have h1 : ‖A u‖ ≤ ∑ i : Fin N, |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
    rw [hAu]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_smul, Real.norm_eq_abs]
  have h2 : (∑ i : Fin N, |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 ≤
      (∑ i : Fin N, |u i| ^ 2) * ∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ∑ i : Fin N, |u i| ^ 2 = ‖u‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => sq_abs _
  calc ‖A u‖ ^ 2 ≤ (∑ i : Fin N, |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i : Fin N, |u i| ^ 2) * ∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := h2
    _ = (∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖u‖ ^ 2 := by
        rw [h3, mul_comm]

/-- Pointwise splitting `u - S u = (u - T u) + (T u - S u)` with the Hilbert–Schmidt bound. -/
theorem Submission.dorag_lip_off_support_aux_pt {N : ℕ} (T S : Submodule ℝ (Euclid N))
    (u : Euclid N) (r q : ℝ) (hr : ‖u‖ ≤ r) (hq : ‖u - T.starProjection u‖ ≤ q) :
    ‖u - S.starProjection u‖ ^ 2 ≤ 2 * q ^ 2 + 2 * r ^ 2 *
      ∑ i : Fin N, ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
        T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
  have hHS0 : 0 ≤ ∑ i : Fin N, ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
      T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hA := Submission.dorag_lip_off_support_aux_hs (T.starProjection - S.starProjection) u
  have e : ∑ i : Fin N, ‖(T.starProjection - S.starProjection)
      (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 =
      ∑ i : Fin N, ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
        T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_apply, norm_sub_rev]
  rw [e, sub_apply] at hA
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hur : ‖u‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hu0 hr 2
  have hq2 : ‖u - T.starProjection u‖ ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hq 2
  have htri : ‖u - S.starProjection u‖ ≤
      ‖u - T.starProjection u‖ + ‖T.starProjection u - S.starProjection u‖ := by
    have e2 : u - S.starProjection u =
        (u - T.starProjection u) + (T.starProjection u - S.starProjection u) := by abel
    rw [e2]
    exact norm_add_le _ _
  have hB : ‖T.starProjection u - S.starProjection u‖ ^ 2 ≤
      (∑ i : Fin N, ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
        T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * r ^ 2 :=
    hA.trans (mul_le_mul_of_nonneg_left hur hHS0)
  have ha0 : 0 ≤ ‖u - T.starProjection u‖ := norm_nonneg _
  have hb0 : 0 ≤ ‖T.starProjection u - S.starProjection u‖ := norm_nonneg _
  have hc0 : 0 ≤ ‖u - S.starProjection u‖ := norm_nonneg _
  have hsq : ‖u - S.starProjection u‖ ^ 2 ≤
      (‖u - T.starProjection u‖ + ‖T.starProjection u - S.starProjection u‖) ^ 2 :=
    pow_le_pow_left₀ hc0 htri 2
  nlinarith [sq_nonneg (‖u - T.starProjection u‖ - ‖T.starProjection u - S.starProjection u‖)]

/-- The pointwise bound in `ℝ≥0∞`, in the two cases `x ∈ F` / `x ∉ F`. -/
theorem Submission.dorag_lip_off_support_aux_ptE {N : ℕ} (T S : Submodule ℝ (Euclid N))
    (u : Euclid N) (s lam : ℝ) (c : ℝ≥0∞) (hu : ‖u‖ ≤ 3 * s)
    (h : ‖u - T.starProjection u‖ ≤ lam * (3 * s) ∨ c = ENNReal.ofReal (18 * s ^ 2)) :
    ENNReal.ofReal (‖u - S.starProjection u‖ ^ 2) ≤
      ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) + c + ENNReal.ofReal (18 * s ^ 2) *
        ENNReal.ofReal (∑ i : Fin N, ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
  have hHS0 : 0 ≤ ∑ i : Fin N, ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
      T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases h with hq | hc
  · have h1 := Submission.dorag_lip_off_support_aux_pt T S u (3 * s) (lam * (3 * s)) hu hq
    calc ENNReal.ofReal (‖u - S.starProjection u‖ ^ 2)
        ≤ ENNReal.ofReal (18 * lam ^ 2 * s ^ 2 + 18 * s ^ 2 *
          ∑ i : Fin N, ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
            T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          refine h1.trans (le_of_eq ?_)
          ring
      _ = ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) + ENNReal.ofReal (18 * s ^ 2) *
          ENNReal.ofReal (∑ i : Fin N, ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
            T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (p := 18 * s ^ 2) (by positivity)]
      _ ≤ _ := add_le_add le_self_add le_rfl
  · have hq : ‖u - T.starProjection u‖ ≤ 3 * s := by
      calc ‖u - T.starProjection u‖ = ‖Tᗮ.starProjection u‖ := by
            rw [Submodule.starProjection_orthogonal_val]
        _ ≤ ‖u‖ := Submodule.norm_starProjection_apply_le _ _
        _ ≤ 3 * s := hu
    have h1 := Submission.dorag_lip_off_support_aux_pt T S u (3 * s) (3 * s) hu hq
    rw [hc]
    calc ENNReal.ofReal (‖u - S.starProjection u‖ ^ 2)
        ≤ ENNReal.ofReal (18 * s ^ 2 + 18 * s ^ 2 *
          ∑ i : Fin N, ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
            T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          refine h1.trans (le_of_eq ?_)
          ring
      _ = ENNReal.ofReal (18 * s ^ 2) + ENNReal.ofReal (18 * s ^ 2) *
          ENNReal.ofReal (∑ i : Fin N, ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
            T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (p := 18 * s ^ 2) (by positivity)]
      _ ≤ _ := add_le_add le_add_self le_rfl

/-- Monotonicity at `η` with radii `s < 3 s`, combined with `e^{3κs} ≤ 2`. -/
theorem Submission.dorag_lip_off_support_aux_exp (n : ℕ) (κ s : ℝ) (a J I₂ : ℝ≥0∞)
    (hκ : 0 ≤ κ) (hs : 0 < s) (hκs : κ * (3 * s) ≤ 3 / 8)
    (hM : ENNReal.ofReal (Real.exp (-(κ * (3 * s))) / (3 * s) ^ n) * a ≤ J)
    (hJ : J ≤ ENNReal.ofReal (1 / s ^ (n + 2)) * I₂) :
    a ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * I₂ := by
  have hexp : Real.exp (κ * (3 * s)) ≤ 2 := by
    have h0 : 0 ≤ κ * (3 * s) := by positivity
    calc Real.exp (κ * (3 * s)) ≤ (2 + κ * (3 * s)) / (2 - κ * (3 * s)) :=
          Real.exp_le_two_add_div_two_sub h0 (by linarith)
      _ ≤ 2 := by
          rw [div_le_iff₀ (by linarith)]
          linarith
  have hc : 0 ≤ Real.exp (κ * (3 * s)) * (3 * s) ^ n := by positivity
  have hcinv : ENNReal.ofReal (Real.exp (κ * (3 * s)) * (3 * s) ^ n) *
      ENNReal.ofReal (Real.exp (-(κ * (3 * s))) / (3 * s) ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_one]
    congr 1
    have h1 : Real.exp (κ * (3 * s)) * Real.exp (-(κ * (3 * s))) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h2 : (3 * s) ^ n / (3 * s) ^ n = 1 := div_self (by positivity)
    calc Real.exp (κ * (3 * s)) * (3 * s) ^ n * (Real.exp (-(κ * (3 * s))) / (3 * s) ^ n)
        = (Real.exp (κ * (3 * s)) * Real.exp (-(κ * (3 * s)))) *
          ((3 * s) ^ n / (3 * s) ^ n) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  have hcs : Real.exp (κ * (3 * s)) * (3 * s) ^ n * (1 / s ^ (n + 2)) ≤ 2 * 3 ^ n / s ^ 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), mul_pow, pow_add]
    have hpos : 0 ≤ 3 ^ n * s ^ n * s ^ 2 := by positivity
    nlinarith
  calc a = ENNReal.ofReal (Real.exp (κ * (3 * s)) * (3 * s) ^ n) *
        (ENNReal.ofReal (Real.exp (-(κ * (3 * s))) / (3 * s) ^ n) * a) := by
        rw [← mul_assoc, hcinv, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (κ * (3 * s)) * (3 * s) ^ n) *
        (ENNReal.ofReal (1 / s ^ (n + 2)) * I₂) := mul_le_mul_right (hM.trans hJ) _
    _ = ENNReal.ofReal (Real.exp (κ * (3 * s)) * (3 * s) ^ n * (1 / s ^ (n + 2))) * I₂ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hc]
    _ ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * I₂ :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hcs) _

/-- The bound `72·15ⁿ·λ² ≤ 1/4` for `0 ≤ λ ≤ λ₀`. -/
theorem Submission.dorag_lip_off_support_aux_lam (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hlam₀ : lam ≤ 1 / Real.sqrt (288 * 15 ^ n)) : 72 * 15 ^ n * lam ^ 2 ≤ 1 / 4 := by
  have hpos : (0 : ℝ) < 288 * 15 ^ n := by positivity
  have hsq : lam ^ 2 ≤ 1 / (288 * 15 ^ n) := by
    have h1 : lam ^ 2 ≤ (1 / Real.sqrt (288 * 15 ^ n)) ^ 2 := pow_le_pow_left₀ hlam hlam₀ 2
    rwa [div_pow, Real.sq_sqrt hpos.le, one_pow] at h1
  calc 72 * 15 ^ n * lam ^ 2 ≤ 72 * 15 ^ n * (1 / (288 * 15 ^ n)) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 1 / 4 := by
        rw [mul_one_div, div_eq_iff hpos.ne']
        ring

/-- The final absorption argument (pure `ℝ≥0∞` arithmetic). -/
theorem Submission.dorag_lip_off_support_aux_final (n : ℕ) (ω s lam : ℝ) (a I₂ X₁ X₂ : ℝ≥0∞)
    (hω : 0 < ω) (hs : 0 < s) (hlam2 : 72 * 15 ^ n * lam ^ 2 ≤ 1 / 4)
    (ha_lower : ENNReal.ofReal (ω * s ^ n / 2) ≤ a)
    (ha_upper : a ≤ ENNReal.ofReal (2 * 5 ^ n * ω * s ^ n))
    (haI : a ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * I₂)
    (hI : I₂ ≤ ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * a + ENNReal.ofReal (18 * s ^ 2) * X₁ +
      ENNReal.ofReal (18 * s ^ 2) * X₂) :
    ENNReal.ofReal (s ^ n) ≤ ENNReal.ofReal (144 * 3 ^ n / ω) * (X₁ + X₂) := by
  have e1 : ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) =
      ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
    ring
  have e2 : ENNReal.ofReal (36 * 3 ^ n) =
      ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * ENNReal.ofReal (18 * s ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
    ring
  have hmain : a ≤ ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a +
      ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := by
    calc a ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * I₂ := haI
      _ ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * (ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * a +
          ENNReal.ofReal (18 * s ^ 2) * X₁ + ENNReal.ofReal (18 * s ^ 2) * X₂) :=
          mul_le_mul_right hI _
      _ = ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a +
          ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := by
          rw [e1, e2]
          ring
  have hlamterm : ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a ≤ ENNReal.ofReal (ω * s ^ n / 4) := by
    calc ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a
        ≤ ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * ENNReal.ofReal (2 * 5 ^ n * ω * s ^ n) :=
          mul_le_mul_right ha_upper _
      _ = ENNReal.ofReal (72 * 15 ^ n * lam ^ 2 * (ω * s ^ n)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show (15 : ℝ) ^ n = 3 ^ n * 5 ^ n by rw [← mul_pow]; norm_num]
          ring
      _ ≤ ENNReal.ofReal (1 / 4 * (ω * s ^ n)) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_right hlam2 (by positivity)
      _ = ENNReal.ofReal (ω * s ^ n / 4) := by
          congr 1
          ring
  have hfin : ENNReal.ofReal (ω * s ^ n / 4) ≤ ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := by
    have h1 : ENNReal.ofReal (ω * s ^ n / 4) + ENNReal.ofReal (ω * s ^ n / 4) ≤
        ENNReal.ofReal (ω * s ^ n / 4) + ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := by
      calc ENNReal.ofReal (ω * s ^ n / 4) + ENNReal.ofReal (ω * s ^ n / 4)
          = ENNReal.ofReal (ω * s ^ n / 2) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
        _ ≤ a := ha_lower
        _ ≤ ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a +
            ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := hmain
        _ ≤ ENNReal.ofReal (ω * s ^ n / 4) + ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) :=
            add_le_add hlamterm le_rfl
    exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp h1
  calc ENNReal.ofReal (s ^ n) = ENNReal.ofReal (4 / ω) * ENNReal.ofReal (ω * s ^ n / 4) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [div_mul_div_comm, eq_div_iff (by positivity)]
        ring
    _ ≤ ENNReal.ofReal (4 / ω) * (ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂)) :=
        mul_le_mul_right hfin _
    _ = ENNReal.ofReal (144 * 3 ^ n / ω) * (X₁ + X₂) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

theorem Submission.dorag_lip_off_support_estimate : ∀ (n k : ℕ), ∃ lam₀ C₉ : ℝ, 0 < lam₀ ∧ 0 < C₉ ∧ ∀ (μ : Measure (Euclid (n + k))) (τ : Euclid (n + k) → Submodule ℝ (Euclid (n + k))) (T₀ : Submodule ℝ (Euclid (n + k))) (F : Set (Euclid (n + k))) (ξ : Euclid (n + k)) (σ₀ κ lam : ℝ), 0 < σ₀ → 0 ≤ κ → κ * σ₀ ≤ 1 → 0 ≤ lam → lam ≤ lam₀ → ξ ∈ μ.support → (∀ x ∈ F, ∀ x' ∈ F, ‖(x - x') - T₀.starProjection (x - x')‖ ≤ lam * ‖x - x'‖) → (∀ y ∈ closedBall ξ (σ₀ / 2), ∀ t : ℝ, 0 < t → t ≤ 5 * σ₀ / 8 → μ (closedBall y t) ≤ 2 * unitBallVolume n * ENNReal.ofReal (t ^ n)) → (∀ y ∈ μ.support ∩ closedBall ξ (σ₀ / 2), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 8 → unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ 2 * μ (closedBall y t)) → (∀ (y : Euclid (n + k)) (s t : ℝ), y ∈ closedBall ξ (σ₀ / 4) → 0 < s → s < t → t ≤ 3 * σ₀ / 8 → ENNReal.ofReal (Real.exp (-(κ * t)) / t ^ n) * μ (closedBall y t) ≤ ENNReal.ofReal (Real.exp (-(κ * s)) / s ^ n) * μ (closedBall y s) + ∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (τ x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂μ) → ∀ η ∈ (F \ μ.support) ∩ closedBall ξ (σ₀ / 4), ∃ s : ℝ, ∃ y ∈ μ.support, 0 < s ∧ 2 * s ≤ dist η ξ ∧ dist y η = 2 * s ∧ ENNReal.ofReal (s ^ n) ≤ ENNReal.ofReal C₉ * (μ (closedBall η (3 * s) \ F) + ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ) := by
  intro n k
  have hV_pos : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact measure_ball_pos _ _ one_pos
  have hV_lt : unitBallVolume n < ∞ := by
    unfold unitBallVolume
    exact measure_ball_lt_top
  obtain ⟨ω, hω_def⟩ : ∃ ω : ℝ, ω = (unitBallVolume n).toReal := ⟨_, rfl⟩
  have hω_pos : 0 < ω := by
    rw [hω_def]
    exact ENNReal.toReal_pos hV_pos.ne' hV_lt.ne
  have hV_eq : unitBallVolume n = ENNReal.ofReal ω := by
    rw [hω_def, ENNReal.ofReal_toReal hV_lt.ne]
  refine ⟨1 / Real.sqrt (288 * 15 ^ n), 144 * 3 ^ n / ω, by positivity, by positivity, ?_⟩
  intro μ τ T₀ F ξ σ₀ κ lam hσ₀ hκ hκσ hlam hlam₀ hξ hF hDa hDb hM2 η hη
  obtain ⟨⟨hηF, hηS⟩, hηξ'⟩ := hη
  have hηξ : dist η ξ ≤ σ₀ / 4 := mem_closedBall.mp hηξ'
  -- Step 1: nearest point of the support
  have hSc : IsClosed μ.support := Measure.isClosed_support
  have hSne : μ.support.Nonempty := ⟨ξ, hξ⟩
  have hd_pos : 0 < Metric.infDist η μ.support := (hSc.notMem_iff_infDist_pos hSne).mp hηS
  have hd_le : Metric.infDist η μ.support ≤ dist η ξ := Metric.infDist_le_dist_of_mem hξ
  obtain ⟨y, hyS, hyd⟩ := hSc.exists_infDist_eq_dist hSne η
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = Metric.infDist η μ.support / 2 := ⟨_, rfl⟩
  have hs : 0 < s := by
    rw [hs_def]
    positivity
  have h2s : 2 * s ≤ dist η ξ := by
    rw [hs_def]
    linarith
  have hyη : dist y η = 2 * s := by
    rw [dist_comm, ← hyd, hs_def]
    ring
  have hs8 : s ≤ σ₀ / 8 := by linarith
  have hyξ : dist y ξ ≤ σ₀ / 2 := by linarith [dist_triangle y η ξ]
  refine ⟨s, y, hyS, hs, h2s, hyη, ?_⟩
  -- Step 2: the small ball around η misses the support
  have hμs0 : μ (closedBall η s) = 0 := by
    have hsub : closedBall η s ⊆ μ.supportᶜ := by
      intro x hx
      rw [mem_compl_iff]
      intro hxS
      have h1 := Metric.infDist_le_dist_of_mem (x := η) hxS
      have h2 : dist x η ≤ s := mem_closedBall.mp hx
      rw [dist_comm] at h1
      linarith
    exact measure_mono_null hsub (Measure.measure_compl_support (μ := μ))
  -- Step 3: mass bounds
  have hsub1 : closedBall y s ⊆ closedBall η (3 * s) := by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    linarith [dist_triangle x y η]
  have hsub2 : closedBall η (3 * s) ⊆ closedBall y (5 * s) := by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    have h := dist_triangle x η y
    rw [dist_comm η y] at h
    linarith
  have hDb' := hDb y ⟨hyS, mem_closedBall.mpr hyξ⟩ s hs hs8
  have hDa' := hDa y (mem_closedBall.mpr hyξ) (5 * s) (by positivity) (by linarith)
  have ha_lower : ENNReal.ofReal (ω * s ^ n / 2) ≤ μ (closedBall η (3 * s)) := by
    have h1 : ENNReal.ofReal (ω * s ^ n) ≤ 2 * μ (closedBall η (3 * s)) := by
      calc ENNReal.ofReal (ω * s ^ n) = unitBallVolume n * ENNReal.ofReal (s ^ n) := by
            rw [hV_eq, ENNReal.ofReal_mul hω_pos.le]
        _ ≤ 2 * μ (closedBall y s) := hDb'
        _ ≤ 2 * μ (closedBall η (3 * s)) := mul_le_mul_right (measure_mono hsub1) _
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
    exact ENNReal.div_le_of_le_mul' h1
  have ha_upper : μ (closedBall η (3 * s)) ≤ ENNReal.ofReal (2 * 5 ^ n * ω * s ^ n) := by
    calc μ (closedBall η (3 * s)) ≤ μ (closedBall y (5 * s)) := measure_mono hsub2
      _ ≤ 2 * unitBallVolume n * ENNReal.ofReal ((5 * s) ^ n) := hDa'
      _ = ENNReal.ofReal (2 * 5 ^ n * ω * s ^ n) := by
        rw [hV_eq, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  -- Step 4: monotonicity at η with radii s < 3 s
  have hM2' := hM2 η s (3 * s) hηξ' hs (by linarith) (by linarith)
  rw [hμs0, mul_zero, zero_add] at hM2'
  have hJ : ∫⁻ x in closedBall η (3 * s) \ closedBall η s,
      ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 / ‖x - η‖ ^ (n + 2)) ∂μ ≤
      ENNReal.ofReal (1 / s ^ (n + 2)) * ∫⁻ x in closedBall η (3 * s),
        ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ := by
    calc ∫⁻ x in closedBall η (3 * s) \ closedBall η s,
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 / ‖x - η‖ ^ (n + 2)) ∂μ
        ≤ ∫⁻ x in closedBall η (3 * s) \ closedBall η s, ENNReal.ofReal (1 / s ^ (n + 2)) *
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ := by
          refine setLIntegral_mono' (measurableSet_closedBall.diff measurableSet_closedBall) ?_
          intro x hx
          have hx2 : s < ‖x - η‖ := by
            rw [← dist_eq_norm]
            have h := hx.2
            rw [mem_closedBall, not_le] at h
            exact h
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          calc ‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 / ‖x - η‖ ^ (n + 2)
              ≤ ‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 / s ^ (n + 2) := by
                gcongr
            _ = 1 / s ^ (n + 2) * ‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 := by ring
      _ = ENNReal.ofReal (1 / s ^ (n + 2)) * ∫⁻ x in closedBall η (3 * s) \ closedBall η s,
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (1 / s ^ (n + 2)) * ∫⁻ x in closedBall η (3 * s),
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ :=
          mul_le_mul_right (lintegral_mono_set sdiff_subset) _
  -- Step 5: the exponential factor
  have hκs : κ * (3 * s) ≤ 3 / 8 := by nlinarith [mul_le_mul_of_nonneg_left hs8 hκ]
  have ha_I2 := Submission.dorag_lip_off_support_aux_exp n κ s _ _ _ hκ hs hκs hM2' hJ
  -- Step 6: pointwise bound on the ball `B_{3s}(η)`
  obtain ⟨M, hM_def⟩ : ∃ M : Set (Euclid (n + k)),
      M = toMeasurable μ (closedBall η (3 * s) \ F) := ⟨_, rfl⟩
  have hMmeas : MeasurableSet M := by
    rw [hM_def]
    exact measurableSet_toMeasurable _ _
  have hMsub : closedBall η (3 * s) \ F ⊆ M := by
    rw [hM_def]
    exact subset_toMeasurable _ _
  have hMmu : μ M = μ (closedBall η (3 * s) \ F) := by
    rw [hM_def]
    exact measure_toMeasurable _
  have hpt : ∀ x ∈ closedBall η (3 * s),
      ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ≤
        ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) +
          M.indicator (fun _ => ENNReal.ofReal (18 * s ^ 2)) x +
          ENNReal.ofReal (18 * s ^ 2) * ENNReal.ofReal (∑ i : Fin (n + k),
            ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
              T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
    intro x hx
    have hxr : ‖x - η‖ ≤ 3 * s := by
      rw [← dist_eq_norm]
      exact mem_closedBall.mp hx
    apply Submission.dorag_lip_off_support_aux_ptE T₀ (τ x) (x - η) s lam _ hxr
    by_cases hxF : x ∈ F
    · left
      exact (hF x hxF η hηF).trans (mul_le_mul_of_nonneg_left hxr hlam)
    · right
      exact Set.indicator_of_mem (hMsub ⟨hx, hxF⟩) _
  -- Step 7: integration
  have hI2 : ∫⁻ x in closedBall η (3 * s),
        ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ ≤
      ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * μ (closedBall η (3 * s)) +
        ENNReal.ofReal (18 * s ^ 2) * μ (closedBall η (3 * s) \ F) +
        ENNReal.ofReal (18 * s ^ 2) * ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal
          (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
              T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ := by
    calc ∫⁻ x in closedBall η (3 * s),
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ
        ≤ ∫⁻ x in closedBall η (3 * s), (ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) +
            M.indicator (fun _ => ENNReal.ofReal (18 * s ^ 2)) x +
            ENNReal.ofReal (18 * s ^ 2) * ENNReal.ofReal (∑ i : Fin (n + k),
              ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) ∂μ :=
          setLIntegral_mono' measurableSet_closedBall hpt
      _ = ∫⁻ x in closedBall η (3 * s), (ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) +
            M.indicator (fun _ => ENNReal.ofReal (18 * s ^ 2)) x) ∂μ +
          ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal (18 * s ^ 2) *
            ENNReal.ofReal (∑ i : Fin (n + k),
              ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ :=
          lintegral_add_left ((measurable_const.indicator hMmeas).const_add _) _
      _ = ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * μ (closedBall η (3 * s)) +
            ENNReal.ofReal (18 * s ^ 2) * μ (M ∩ closedBall η (3 * s)) +
          ENNReal.ofReal (18 * s ^ 2) * ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal
            (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_indicator_const hMmeas, Measure.restrict_apply hMmeas,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * μ (closedBall η (3 * s)) +
            ENNReal.ofReal (18 * s ^ 2) * μ (closedBall η (3 * s) \ F) +
          ENNReal.ofReal (18 * s ^ 2) * ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal
            (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ := by
          have hμM : μ (M ∩ closedBall η (3 * s)) ≤ μ (closedBall η (3 * s) \ F) :=
            (measure_mono inter_subset_left).trans hMmu.le
          exact add_le_add (add_le_add le_rfl (mul_le_mul_right hμM _)) le_rfl
  -- Step 8: absorption of the λ-term
  exact Submission.dorag_lip_off_support_aux_final n ω s lam _ _ _ _ hω_pos hs
    (Submission.dorag_lip_off_support_aux_lam n lam hlam hlam₀) ha_lower ha_upper ha_I2 hI2

## Key steps

1. constants λ₀ = (288·15ⁿ)^{-1/2} and C₉ = 144·3ⁿ/ω
2. nearest support point y with s = infDist(η, spt μ)/2, 2s ≤ |η − ξ|, |y − η| = 2s
3. μ(B_s(η)) = 0 because B_s(η) misses spt μ
4. ½ωsⁿ ≤ μ(B_{3s}(η)) ≤ 2·5ⁿωsⁿ via B_s(y) ⊆ B_{3s}(η) ⊆ B_{5s}(y)
5. (M2) at η with s < 3s and e^{3κs} ≤ 2: μ(B_{3s}(η)) ≤ 2·3ⁿs^{−2}∫_{B_{3s}(η)}|p_x^⊥(x − η)|²
6. pointwise split p_x^⊥(x − η) = Q(x − η) + (P − p_x)(x − η) with the cone condition on F and the Hilbert–Schmidt bound
7. integrate: μ(B_{3s}(η)) ≤ 36·3ⁿ[λ²μ(B_{3s}(η)) + μ(B_{3s}(η) ∖ F) + ∫|p_x − P|²]
8. absorb the λ-term using λ ≤ λ₀ and conclude sⁿ ≤ C₉[μ(B_{3s}(η) ∖ F) + ∫_{B_{3s}(η)}|p_x − P|²]

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
