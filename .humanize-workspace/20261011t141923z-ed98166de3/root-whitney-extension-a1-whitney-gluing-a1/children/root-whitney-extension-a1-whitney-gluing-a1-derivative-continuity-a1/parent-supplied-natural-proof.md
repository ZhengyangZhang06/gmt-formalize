# Parent-supplied natural-language proof

- Parent DAG node: `root.whitney_extension-a1.whitney_gluing-a1`
- Child DAG node: `root.whitney_extension-a1.whitney_gluing-a1.derivative_continuity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: (E1), (E2), step 2 and step 4 of the supplied proof of whitney_jet_gluing_c1. Two inputs that the supplied proof derives are hypotheses here: the identity Dg = L_ν on A (its step 3), and the derivative representation at points off A (its (1b)-(1f) together with (P3), (P6), (P7)).

Notation. d(x) := Metric.infDist x A. For v ∈ ℝⁿ, L_v := innerSL ℝ v, so L_v(w) = ⟨v, w⟩ (innerSL_apply_apply), L_v − L_w = L_{v−w} by linearity of innerSL, and ‖L_v‖ = ‖v‖ (innerSL_apply_norm). Dψ(x) := fderiv ℝ ψ x, normed by the operator norm. For x ∉ A and i ∈ ι, P_i(x) := h(p_i) + ⟨ν(p_i), x − p_i⟩.

Proof. Fix a ∈ A. By Metric.continuousAt_iff it suffices to show: for every η > 0 there is ρ > 0 with ‖Dg(x) − Dg(a)‖ < η whenever ‖x − a‖ < ρ. Fix η > 0. By hypothesis Dg(a) = L_{ν(a)}.

1. Constants. Put B := 1 + (3C + 1)M. Since C, M ≥ 0, B ≥ 1. Put ε := η/(2B) > 0. Then εB = η/2 < η, and ε ≤ εB < η.

2. Let K := A ∩ B̄(a, 1). K is compact (a closed ball in the proper space ℝⁿ, intersected with the closed set A), and K ⊆ A. Apply (W) to K and ε: there is δ₁ > 0 with |h(y) − h(b) − ⟨ν(b), y − b⟩| ≤ ε‖y − b‖ for all b ∈ K and y ∈ A with 0 < ‖y − b‖ < δ₁. The inequality also holds when y = b, where both sides are 0. Call this (2a).

3. By continuity of ν on A at a, choose τ > 0 with ‖ν(y) − ν(a)‖ < ε for all y ∈ A with ‖y − a‖ < τ. Call this (3a).

4. Put r := min{1, δ₁, τ} > 0 and ρ := r/(C + 2) > 0. Since C ≥ 0: (C + 1)ρ < r, 2ρ ≤ r, and ρ < r.

5. Let ‖x − a‖ < ρ.
Case x ∈ A. By hypothesis Dg(x) = L_{ν(x)}, so Dg(x) − Dg(a) = L_{ν(x)−ν(a)}. Its norm is ‖ν(x) − ν(a)‖, which is < ε < η by (3a), because ‖x − a‖ < ρ < r ≤ τ.
Case x ∉ A. Take S from (R').
(a) A is closed and nonempty (a ∈ A) and x ∉ A, so d(x) > 0 (IsClosed.notMem_iff_infDist_pos). Also d(x) ≤ ‖x − a‖ (infDist_le_dist_of_mem) < ρ < r ≤ 1. Write d := d(x). As d ≤ 1, (R') gives Σ_{i∈S} ‖Dφ_i(x)‖ ≤ M/d.
(b) Nearest point. A is closed and nonempty and ℝⁿ is proper, so there is a* ∈ A with ‖x − a*‖ = d (IsClosed.exists_infDist_eq_dist). Then ‖a* − a‖ ≤ ‖x − a*‖ + ‖x − a‖ ≤ 2‖x − a‖ < 2ρ ≤ r. Hence a* ∈ K (as ‖a* − a‖ ≤ 1), and ‖ν(a*) − ν(a)‖ < ε by (3a).
(c) Let i ∈ S. By (R') and C ≥ 0, ‖x − p_i‖ ≤ C·d ≤ C‖x − a‖. Then ‖p_i − a‖ ≤ ‖x − a‖ + ‖x − p_i‖ ≤ (C + 1)‖x − a‖ < (C + 1)ρ < r. Since p_i ∈ A, (3a) gives ‖ν(p_i) − ν(a)‖ < ε. Hence ‖ν(p_i) − ν(a*)‖ ≤ ‖ν(p_i) − ν(a)‖ + ‖ν(a*) − ν(a)‖ ≤ 2ε.
(d) Let i ∈ S. Then ‖p_i − a*‖ ≤ ‖x − a*‖ + ‖x − p_i‖ ≤ d + C·d = (C + 1)d ≤ (C + 1)‖x − a‖ < (C + 1)ρ < r ≤ δ₁. By (2a) with b := a* ∈ K and y := p_i ∈ A: |h(p_i) − h(a*) − ⟨ν(a*), p_i − a*⟩| ≤ ε‖p_i − a*‖ ≤ ε(C + 1)d.
(e) Put c := h(a*) + ⟨ν(a*), x − a*⟩. (E1): since x − a* = (x − p_i) + (p_i − a*), we have P_i(x) − c = [h(p_i) − h(a*) − ⟨ν(a*), p_i − a*⟩] + ⟨ν(p_i) − ν(a*), x − p_i⟩. By (d), Cauchy–Schwarz, (c) and ‖x − p_i‖ ≤ C·d: |P_i(x) − c| ≤ ε(C + 1)d + 2ε·C·d = ε(3C + 1)d for every i ∈ S.
(f) Representation. By (R'), Dg(x) = Σ_{i∈S}(φ_i(x)•L_{ν(p_i)} + P_i(x)•Dφ_i(x)), Σ_{i∈S} φ_i(x) = 1 and Σ_{i∈S} Dφ_i(x) = 0. Hence L_{ν(a)} = Σ_{i∈S} φ_i(x)•L_{ν(a)} and 0 = c•Σ_{i∈S} Dφ_i(x) = Σ_{i∈S} c•Dφ_i(x). Subtracting both from Dg(x):
Dg(x) − L_{ν(a)} = Σ_{i∈S} φ_i(x)•(L_{ν(p_i)} − L_{ν(a)}) + Σ_{i∈S} (P_i(x) − c)•Dφ_i(x).
(g) Estimates. First term: use φ_i(x) ≥ 0, ‖L_{ν(p_i)} − L_{ν(a)}‖ = ‖ν(p_i) − ν(a)‖ ≤ ε from (c), and Σ_{i∈S} φ_i(x) = 1:
‖Σ_{i∈S} φ_i(x)•(L_{ν(p_i)} − L_{ν(a)})‖ ≤ Σ_{i∈S} φ_i(x)‖ν(p_i) − ν(a)‖ ≤ ε.
Second term: use (e), (a) and d > 0:
‖Σ_{i∈S} (P_i(x) − c)•Dφ_i(x)‖ ≤ Σ_{i∈S} |P_i(x) − c|·‖Dφ_i(x)‖ ≤ ε(3C + 1)d·Σ_{i∈S}‖Dφ_i(x)‖ ≤ ε(3C + 1)d·(M/d) = ε(3C + 1)M.
Therefore ‖Dg(x) − Dg(a)‖ = ‖Dg(x) − L_{ν(a)}‖ ≤ ε + ε(3C + 1)M = εB < η.

6. So ‖Dg(x) − Dg(a)‖ < η whenever ‖x − a‖ < ρ, and fderiv ℝ g is continuous at a. As a ∈ A was arbitrary, the theorem follows. ∎

Formalization remark (non-normative; the numbered proof above is complete without it). During the decomposition session the frozen type was proved verbatim by the following declaration. It was kernel-checked against a scratch build of GMT.Ch02.Submission at the frozen commit, with Lean v4.35.0-rc3 and Mathlib 25730c7c, and uses only the axioms propext, Classical.choice and Quot.sound. It follows steps 1-6 above. Placed inside `namespace GMT.Ch02` of GMT/Ch02/Submission.lean, before `main_theorem`, it elaborates unchanged:

theorem Submission.whitney_gluing_continuousAt_fderiv : (∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (ν : Rn n → Rn n) (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (C M : ℝ) (g : Rn n → ℝ), IsClosed A → ContinuousOn ν A → (∀ K ⊆ A, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ A, 0 < ‖y - x‖ → ‖y - x‖ < δ → |h y - h x - inner ℝ (ν x) (y - x)| ≤ ε * ‖y - x‖) → 0 ≤ C → 0 ≤ M → (∀ i, p i ∈ A) → (∀ x ∈ A, fderiv ℝ g x = innerSL ℝ (ν x)) → (∀ x ∉ A, ∃ S : Finset ι, (∀ i ∈ S, 0 ≤ φ i x ∧ ‖x - p i‖ ≤ C * Metric.infDist x A) ∧ ∑ i ∈ S, φ i x = 1 ∧ ∑ i ∈ S, fderiv ℝ (φ i) x = 0 ∧ (Metric.infDist x A ≤ 1 → ∑ i ∈ S, ‖fderiv ℝ (φ i) x‖ ≤ M / Metric.infDist x A) ∧ fderiv ℝ g x = ∑ i ∈ S, (φ i x • innerSL ℝ (ν (p i)) + (h (p i) + inner ℝ (ν (p i)) (x - p i)) • fderiv ℝ (φ i) x)) → ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a) := by
  intro n A h ν ι φ p C M g hA hν hW hC hM hp hFD hrep a ha
  rw [Metric.continuousAt_iff]
  intro η hη
  have hB : 0 < 1 + (3 * C + 1) * M := by nlinarith
  set ε := η / (2 * (1 + (3 * C + 1) * M)) with hε_def
  have hε : 0 < ε := div_pos hη (by linarith)
  have hεB : ε * (1 + (3 * C + 1) * M) < η := by
    rw [hε_def, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  have hεη : ε < η := by
    have h0 : 0 ≤ (3 * C + 1) * M := mul_nonneg (by linarith) hM
    have : ε ≤ ε * (1 + (3 * C + 1) * M) := by nlinarith [mul_nonneg hε.le h0]
    linarith
  set K : Set (Rn n) := A ∩ closedBall a 1 with hK_def
  have hK : IsCompact K := (isCompact_closedBall a 1).inter_left hA
  obtain ⟨δ₁, hδ₁, hWK⟩ := hW K inter_subset_left hK ε hε
  obtain ⟨τ, hτ, hντ⟩ := Metric.continuousWithinAt_iff.mp (hν a ha) ε hε
  set r := min 1 (min δ₁ τ) with hr_def
  have hr : 0 < r := lt_min one_pos (lt_min hδ₁ hτ)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrδ : r ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hrτ : r ≤ τ := (min_le_right _ _).trans (min_le_right _ _)
  have hC2 : 0 < C + 2 := by linarith
  set ρ := r / (C + 2) with hρ_def
  have hρ : 0 < ρ := div_pos hr hC2
  have hρr : (C + 1) * ρ < r := by
    rw [hρ_def, mul_div_assoc', div_lt_iff₀ hC2]
    nlinarith
  have hρr2 : 2 * ρ ≤ r := by
    rw [hρ_def, mul_div_assoc', div_le_iff₀ hC2]
    nlinarith
  have hρr' : ρ < r := by
    have : ρ ≤ (C + 1) * ρ := by nlinarith
    linarith
  -- (W) with base point in K, including the trivial case y = base
  have hWK' : ∀ b ∈ K, ∀ y ∈ A, ‖y - b‖ < δ₁ → |h y - h b - inner ℝ (ν b) (y - b)| ≤ ε * ‖y - b‖ := by
    intro b hb y hy hyb
    rcases eq_or_ne y b with rfl | hne
    · simp
    · exact hWK b hb y hy (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) hyb
  have hνa : ∀ b ∈ A, ‖b - a‖ < r → ‖ν b - ν a‖ < ε := by
    intro b hb hba
    have := hντ hb (by rw [dist_eq_norm]; linarith)
    rwa [dist_eq_norm] at this
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  have hxa : ‖x - a‖ < ρ := by rwa [dist_eq_norm] at hx
  rw [dist_eq_norm, hFD a ha]
  by_cases hxA : x ∈ A
  · rw [hFD x hxA, ← map_sub, innerSL_apply_norm]
    exact (hνa x hxA (by linarith)).trans hεη
  · obtain ⟨S, hS, hS1, hD0, hDbound, hfd⟩ := hrep x hxA
    have hne : A.Nonempty := ⟨a, ha⟩
    have hdpos : 0 < infDist x A := (hA.notMem_iff_infDist_pos hne).mp hxA
    have hdx : infDist x A ≤ ‖x - a‖ := by rw [← dist_eq_norm]; exact infDist_le_dist_of_mem ha
    have hd1 : infDist x A ≤ 1 := by linarith
    obtain ⟨a', ha', hda'⟩ := hA.exists_infDist_eq_dist hne x
    have hxa' : ‖x - a'‖ = infDist x A := by rw [hda', dist_eq_norm]
    have ha'a : ‖a' - a‖ < r := by
      have : ‖a' - a‖ ≤ ‖x - a'‖ + ‖x - a‖ := by
        calc ‖a' - a‖ = ‖(x - a) - (x - a')‖ := by congr 1; abel
          _ ≤ ‖x - a‖ + ‖x - a'‖ := norm_sub_le _ _
          _ = ‖x - a'‖ + ‖x - a‖ := add_comm _ _
      linarith
    have ha'K : a' ∈ K := ⟨ha', by rw [mem_closedBall, dist_eq_norm]; linarith⟩
    have hνa' : ‖ν a' - ν a‖ < ε := hνa a' ha' ha'a
    set d := infDist x A with hd_def
    set c := h a' + inner ℝ (ν a') (x - a') with hc_def
    -- estimates for the anchors
    have hνi : ∀ i ∈ S, ‖ν (p i) - ν a‖ ≤ ε := by
      intro i hi
      have hxp : ‖x - p i‖ ≤ C * ‖x - a‖ := (hS i hi).2.trans (mul_le_mul_of_nonneg_left hdx hC)
      have hpa : ‖p i - a‖ ≤ (C + 1) * ‖x - a‖ := by
        calc ‖p i - a‖ = ‖(x - a) - (x - p i)‖ := by congr 1; abel
          _ ≤ ‖x - a‖ + ‖x - p i‖ := norm_sub_le _ _
          _ ≤ ‖x - a‖ + C * ‖x - a‖ := by linarith
          _ = (C + 1) * ‖x - a‖ := by ring
      have : (C + 1) * ‖x - a‖ ≤ (C + 1) * ρ := mul_le_mul_of_nonneg_left hxa.le (by linarith)
      exact (hνa (p i) (hp i) (by linarith)).le
    have hPi : ∀ i ∈ S, |(h (p i) + inner ℝ (ν (p i)) (x - p i)) - c| ≤ ε * (3 * C + 1) * d := by
      intro i hi
      have hxp : ‖x - p i‖ ≤ C * d := (hS i hi).2
      have hpa' : ‖p i - a'‖ ≤ (C + 1) * d := by
        calc ‖p i - a'‖ = ‖(x - a') - (x - p i)‖ := by congr 1; abel
          _ ≤ ‖x - a'‖ + ‖x - p i‖ := norm_sub_le _ _
          _ ≤ d + C * d := by rw [hxa']; linarith
          _ = (C + 1) * d := by ring
      have hpa'δ : ‖p i - a'‖ < δ₁ := by
        have : (C + 1) * d ≤ (C + 1) * ρ := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        linarith
      have hWi := hWK' a' ha'K (p i) (hp i) hpa'δ
      have hνpa' : ‖ν (p i) - ν a'‖ ≤ 2 * ε := by
        calc ‖ν (p i) - ν a'‖ = ‖(ν (p i) - ν a) - (ν a' - ν a)‖ := by congr 1; abel
          _ ≤ ‖ν (p i) - ν a‖ + ‖ν a' - ν a‖ := norm_sub_le _ _
          _ ≤ ε + ε := add_le_add (hνi i hi) hνa'.le
          _ = 2 * ε := by ring
      have hE1 : (h (p i) + inner ℝ (ν (p i)) (x - p i)) - c =
          (h (p i) - h a' - inner ℝ (ν a') (p i - a')) + inner ℝ (ν (p i) - ν a') (x - p i) := by
        have hsplit : x - a' = (x - p i) + (p i - a') := by abel
        rw [hc_def, inner_sub_left, hsplit, inner_add_right]
        ring
      rw [hE1]
      calc |(h (p i) - h a' - inner ℝ (ν a') (p i - a')) + inner ℝ (ν (p i) - ν a') (x - p i)|
          ≤ |h (p i) - h a' - inner ℝ (ν a') (p i - a')| + |inner ℝ (ν (p i) - ν a') (x - p i)| :=
            abs_add_le _ _
        _ ≤ ε * ‖p i - a'‖ + ‖ν (p i) - ν a'‖ * ‖x - p i‖ :=
            add_le_add hWi (abs_real_inner_le_norm _ _)
        _ ≤ ε * ((C + 1) * d) + (2 * ε) * (C * d) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hpa' hε.le
            · exact mul_le_mul hνpa' hxp (norm_nonneg _) (by linarith)
        _ = ε * (3 * C + 1) * d := by ring
    -- algebraic representation (1g)
    have hrepr : fderiv ℝ g x - innerSL ℝ (ν a) =
        ∑ i ∈ S, φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a)) +
          ∑ i ∈ S, ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x := by
      rw [hfd]
      simp_rw [smul_sub, sub_smul]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_smul, ← Finset.smul_sum, hS1, hD0, one_smul, smul_zero, sub_zero]
      abel
    rw [hrepr]
    have hfirst : ‖∑ i ∈ S, φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a))‖ ≤ ε := by
      calc ‖∑ i ∈ S, φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a))‖
          ≤ ∑ i ∈ S, ‖φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a))‖ := norm_sum_le _ _
        _ = ∑ i ∈ S, φ i x * ‖ν (p i) - ν a‖ := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [norm_smul, Real.norm_of_nonneg (hS i hi).1, ← map_sub, innerSL_apply_norm]
        _ ≤ ∑ i ∈ S, φ i x * ε := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_left (hνi i hi) (hS i hi).1
        _ = ε := by rw [← Finset.sum_mul, hS1, one_mul]
    have hsecond : ‖∑ i ∈ S, ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x‖ ≤
        ε * (3 * C + 1) * M := by
      calc ‖∑ i ∈ S, ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x‖
          ≤ ∑ i ∈ S, ‖((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x‖ :=
            norm_sum_le _ _
        _ = ∑ i ∈ S, |(h (p i) + inner ℝ (ν (p i)) (x - p i)) - c| * ‖fderiv ℝ (φ i) x‖ := by
            apply Finset.sum_congr rfl
            intro i _
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ∑ i ∈ S, (ε * (3 * C + 1) * d) * ‖fderiv ℝ (φ i) x‖ := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_right (hPi i hi) (norm_nonneg _)
        _ = (ε * (3 * C + 1) * d) * ∑ i ∈ S, ‖fderiv ℝ (φ i) x‖ := by rw [Finset.mul_sum]
        _ ≤ (ε * (3 * C + 1) * d) * (M / d) := by
            apply mul_le_mul_of_nonneg_left (hDbound hd1)
            have : 0 ≤ 3 * C + 1 := by linarith
            positivity
        _ = ε * (3 * C + 1) * M := by field_simp
    calc ‖∑ i ∈ S, φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a)) +
          ∑ i ∈ S, ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x‖
        ≤ ‖∑ i ∈ S, φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a))‖ +
          ‖∑ i ∈ S, ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x‖ := norm_add_le _ _
      _ ≤ ε + ε * (3 * C + 1) * M := add_le_add hfirst hsecond
      _ = ε * (1 + (3 * C + 1) * M) := by ring
      _ < η := hεB

## Key steps

1. Fix a ∈ A and η > 0 and put ε := η/(2(1+(3C+1)M)). (W) on K = A ∩ B̄(a,1) gives δ₁, continuity of ν at a gives τ; set r := min{1,δ₁,τ} and ρ := r/(C+2).
2. If x ∈ A: ‖Dg(x) − Dg(a)‖ = ‖L_{ν(x)−ν(a)}‖ = |ν(x) − ν(a)| < ε < η.
3. If x ∉ A: 0 < d(x) ≤ |x−a| < 1, and a nearest point a* ∈ A lies in K with |ν(a*)−ν(a)| < ε. For i ∈ S, |ν(p_i)−ν(a)| < ε, and (E1) with (W) at a* gives |P_i(x) − P*(x)| ≤ ε(3C+1)d(x).
4. Dg(x) − L_{ν(a)} = Σ_S φ_i(x)(L_{ν(p_i)} − L_{ν(a)}) + Σ_S (P_i(x) − P*(x))Dφ_i(x), so ‖Dg(x) − Dg(a)‖ ≤ ε + ε(3C+1)d(x)·M/d(x) < η.

## Reference use

### local-project

Queries:
- `cmp local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean workspaces/gmt-ch02/GMT/Ch02/Contract.lean`
- `rg -n "Whitney|whitney" local-references/ff09f3909baeeae7/project/GMT`
- `rg -n "whitney_gluing_local_structure|whitney_gluing_hasFDerivAt|whitney_gluing_continuousAt_fderiv" <run dir> local-references/ff09f3909baeeae7/project local-references/ff09f3909baeeae7/mathlib/Mathlib lake-packages-25730c7c/simongmt/Poincare (exit 1: no match); dag.json lean_name scan for the same names (absent)`
- `rg -n "theorem IsLocalMin.fderiv_eq_zero|theorem innerSL_apply_apply|theorem innerSL_apply_norm|theorem contDiff_one_iff_fderiv|theorem ContDiffAt.continuousAt_fderiv|theorem ContDiffAt.congr_of_eventuallyEq|theorem HasFDerivAt.mul |theorem ContDiffAt.sum|theorem abs_real_inner_le_norm|theorem infDist_le_dist_of_mem|theorem IsCompact.inter_left|theorem abs_sum_le_sum_abs" mathlib/Mathlib`
- `rg -n "finsum_eq_sum_of_support_subset|theorem sum_filter_of_ne|theorem sum_filter_ne_zero|exists_infDist_eq_dist|notMem_iff_infDist_pos|HasFDerivAt.of_isLittleO|EventuallyEq.fderiv_eq" mathlib/Mathlib`
- `rg -n "theorem finsum_eq_sum_of_support_subset|theorem prod_filter_of_ne|theorem prod_filter_ne_one|theorem HasFDerivAt.sum|theorem IsLittleO.of_bound|theorem continuousWithinAt_iff|theorem continuousAt_iff|theorem HasFDerivAt.unique|theorem HasFDerivAt.congr_of_eventuallyEq|theorem hasFDerivAt_const|theorem mem_of_mem_nhds" mathlib/Mathlib`
- `full reads of lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean and WhitneyExtension.lean; ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02 | grep -i whitney; grep import Poincare/SimonGMT.lean | grep -i whitney (exit 1)`
- `lean -R . -o /tmp/gluing-decomp/build/GMT/Ch02/Submission.olean GMT/Ch02/Submission.lean (scratch copy of the frozen Submission; LEAN_PATH = scratch build + shared package oleans, read-only)`
- `python3 -I gen.py (gmt-compare.py layout/child_modules + lean_contract.validate_lean_statement), then lean NodeChallenge_00.lean NodeChallenge_01.lean NodeChallenge_02.lean`
- `lean asm/AssemblyCheck.lean; lean c1/Child1Check.lean; lean c2/Child2Check.lean; lean c3/Child3Check.lean (each with #print axioms)`
- `lean full/GMT/Ch02/Submission.lean (copy with Submission.whitney_gluing_* and Submission.whitney_jet_gluing_c1 inserted before main_theorem), then lean full/NodeSolution_0..3.lean (exact Submission.X)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Algebra/BigOperators/Finprod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Neighborhoods.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1-whitney-gluing-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1-whitney-gluing-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1/decomposition-v1.json`
- `/tmp/gluing-decomp/gen-v1/NodeChallenge_00.lean`
- `/tmp/gluing-decomp/gen-v1/NodeChallenge_01.lean`
- `/tmp/gluing-decomp/gen-v1/NodeChallenge_02.lean`
- `/tmp/gluing-decomp/asm/AssemblyCheck.lean`
- `/tmp/gluing-decomp/c1/Child1Check.lean`
- `/tmp/gluing-decomp/c2/Child2Check.lean`
- `/tmp/gluing-decomp/c3/Child3Check.lean`
- `/tmp/gluing-decomp/full/GMT/Ch02/Submission.lean`

Snapshot and names:
- The snapshot's project/GMT/Ch02/Contract.lean is byte-identical to the workspace contract (cmp).
- In project/GMT, 'Whitney' occurs only in the WhitneyExtension definition (Contract/Submission lines 204-208) and README rows 3-4.
- None of the three proposed names occurs anywhere: run directory, dag.json lean_name fields, snapshot project, snapshot Mathlib, or simongmt (rg exit 1). The names are unreserved.

Mathlib reuse. Snapshot Mathlib has no abstract Whitney-gluing lemma, but supplies every tool the child proofs cite:
- IsLocalMin.fderiv_eq_zero (LocalExtr/Basic.lean:181);
- finsum_eq_sum_of_support_subset (to_additive of Finprod.lean:350);
- Finset.sum_filter_of_ne / sum_filter_ne_zero (to_additive of Group/Finset/Basic.lean:319/328);
- innerSL_apply_apply and innerSL_apply_norm (InnerProductSpace/LinearMap.lean:172/225);
- abs_real_inner_le_norm (InnerProductSpace/Basic.lean:471);
- ContDiffAt.congr_of_eventuallyEq and contDiff_one_iff_fderiv (ContDiff/Defs.lean:966/1261);
- ContDiffAt.continuousAt_fderiv (ContDiff/Comp.lean:816);
- ContDiffAt.sum (ContDiff/Operations.lean:369);
- HasFDerivAt.mul (FDeriv/Mul.lean:205);
- HasFDerivAt.sum, with fun_sum generated by to_fun (FDeriv/Add.lean:418);
- HasFDerivAt.unique (FDeriv/Basic.lean:174);
- HasFDerivAt.congr_of_eventuallyEq and Filter.EventuallyEq.fderiv_eq (FDeriv/Congr.lean:176/260);
- hasFDerivAt_const (FDeriv/Const.lean:115);
- HasFDerivAt.of_isLittleO (FDeriv/Defs.lean:230);
- IsLittleO.of_bound (Asymptotics/Defs.lean:185);
- infDist_le_dist_of_mem, IsClosed.notMem_iff_infDist_pos and IsClosed.exists_infDist_eq_dist (HausdorffDistance.lean:500/584/615);
- Metric.continuousAt_iff and continuousWithinAt_iff (Pseudo/Defs.lean:871/875);
- IsCompact.inter_left (Compactness/Compact.lean:96);
- abs_sum_le_sum_abs (Order/BigOperators/Group/Finset.lean:371);
- mem_of_mem_nhds (Neighborhoods.lean:85).

SimonGMT. The pinned WhitneyExtension.lean proves the analogous facts for its own WhitneyBallCover:
- whitneyExtension_contDiffAt_compl and whitneyExtension_fderiv_eq_near_sum correspond to child 1;
- HasWhitneyC1Compatibility.hasFDerivAt_whitneyExtension corresponds to child 2;
- continuousAt_fderiv_whitneyExtension, with norm_fderiv_whitneyExtension_sub_le, corresponds to child 3.
WhitneyExtension has no .olean (only WhitneyCover/Jet/Partition do), and Poincare/SimonGMT.lean imports no Whitney file. So it served only as a template, and the children were proved from Mathlib alone.

Lean checks. All ran in /tmp scratch with the pinned toolchain; the shared package tree and workspace stayed untouched.
- The three types elaborate in the verifier-generated NodeChallenge modules.
- AssemblyCheck derives the selected exact type from them.
- Child1-3Check prove each exact type.
- The Submission copy compiles Submission.whitney_gluing_* and Submission.whitney_jet_gluing_c1, and NodeSolution_0..3 pass.
- #print axioms reports only propext, Classical.choice and Quot.sound everywhere.
