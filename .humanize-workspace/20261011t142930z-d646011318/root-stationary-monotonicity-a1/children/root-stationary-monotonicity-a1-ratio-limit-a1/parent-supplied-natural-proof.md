# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_monotonicity-a1`
- Child DAG node: `root.stationary_monotonicity-a1.ratio_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. E = Ambient n ℓ = ℝ^{n+ℓ} with its Borel σ-algebra; B_r(ξ) = closedBall ξ r (a closed Borel set; B_r(ξ) = ∅ for r < 0); μ = V.weight; for a Borel set S, μ_ℝ(S) := V.weight.real S = (μ S).toReal ∈ [0, ∞) (it is 0 when μ S = ∞); ω_n = omega n = (Lebesgue measure of the unit ball of ℝⁿ).toReal; real division follows Lean's convention x/0 = 0, 0⁻¹ = 0. Put q(x) := V.normalRadialSq ξ x = ‖p_{(T_xV)^⊥}(x − ξ)‖²/‖x − ξ‖², w(x) := q(x)/‖x − ξ‖ⁿ, a(r) := μ_ℝ(B_r(ξ))/rⁿ, Q(r) := μ_ℝ(B_r(ξ))/(ω_n rⁿ), and Θ := V.density ξ = limUnder (𝓝[>] 0) Q. Hypothesis (H): for all reals 0 < σ ≤ ρ < R, w is μ-integrable on B_ρ(ξ) ∖ B_σ(ξ) and a(ρ) − a(σ) = ∫_{B_ρ(ξ)∖B_σ(ξ)} w dμ. Nothing else is used: no finiteness of μ, and no positivity of n or of ω_n.

Source: Steps 3–4 of the parent proof (Simon Ch. 4, 3.8–3.10) and the inequality of its Step 5 (ω_nΘ(ξ) = inf a ≤ a(ρ)). The parent's monotone-limit and monotone-convergence arguments are written out in full below.

1. Elementary facts. (a) w(x) ≥ 0 for every x, because q(x) is a quotient of two squares and ‖x − ξ‖ⁿ ≥ 0. (b) w(ξ) = 0: since ‖ξ − ξ‖² = 0, q(ξ) = ‖·‖²/0 = 0, hence w(ξ) = 0. (c) a(r) ≥ 0 for r > 0, since μ_ℝ ≥ 0 and rⁿ > 0. (d) Q(r) = ω_n⁻¹ · a(r) for every real r: x/(ω rⁿ) = x·(ω rⁿ)⁻¹ = x·ω⁻¹·(rⁿ)⁻¹ = ω⁻¹·(x/rⁿ), using (uv)⁻¹ = u⁻¹v⁻¹, which holds for all reals under the convention 0⁻¹ = 0. (e) ω_n⁻¹ ≥ 0, because ω_n is the real value of a measure and so ω_n ≥ 0. (ω_n > 0 is true but not needed.)

2. (3.8, monotonicity; conclusion 1.) Let σ, ρ ∈ (0, R) with σ ≤ ρ. Then 0 < σ ≤ ρ < R, so by (H), a(ρ) − a(σ) = ∫_{B_ρ(ξ)∖B_σ(ξ)} w dμ. The set B_ρ(ξ)∖B_σ(ξ) is measurable and w ≥ 0 on it (1a), so the integral is ≥ 0 (setIntegral_nonneg). Hence a(σ) ≤ a(ρ): the function r ↦ μ_ℝ(B_r(ξ))/rⁿ is monotone (nondecreasing) on (0, R).

3. (3.9, existence of the limit and of the density; conclusion 3.) Assume R > 0. The set a((0, R)) is nonempty (R/2 ∈ (0, R)) and bounded below by 0 (1c); let L := inf a((0, R)) ∈ [0, ∞). Then L ≤ a(s) for every s ∈ (0, R), and a(s) → L as s ↓ 0. Indeed, given ε > 0, choose s₀ ∈ (0, R) with a(s₀) < L + ε; for 0 < s < s₀ we have s ∈ (0, R), and by Step 2, L ≤ a(s) ≤ a(s₀) < L + ε. (Mathlib: MonotoneOn.tendsto_nhdsWithin_Ioo_right.) By (1d), Q(s) = ω_n⁻¹a(s) → ω_n⁻¹L as s ↓ 0. The filter 𝓝[>] 0 on ℝ is nontrivial and ℝ is Hausdorff, so the limUnder that defines V.density ξ equals this limit (Tendsto.limUnder_eq): Θ = ω_n⁻¹L. Hence Q(s) → Θ as s ↓ 0, which is V.HasDensityAt ξ (V.density ξ).

4. (Ratio bound; conclusion 4.) Let 0 < ρ < R. Then R > 0, so Step 3 applies and L ≤ a(ρ). Multiplying by ω_n⁻¹ ≥ 0 (1e) and using (1d): V.density ξ = ω_n⁻¹L ≤ ω_n⁻¹a(ρ) = Q(ρ) = μ_ℝ(B_ρ(ξ))/(ω_nρⁿ).

5. (3.10, by monotone convergence; conclusion 2.) Fix 0 < ρ < R. Then R > 0, so Steps 3–4 apply. For k ∈ ℕ put s_k := ρ/(k + 1) and A_k := B_ρ(ξ) ∖ B_{s_k}(ξ).
(a) Properties. 0 < s_k ≤ ρ < R. The sequence (s_k) is nonincreasing and s_k → 0, so s_k → 0 within (0, ∞), i.e. along 𝓝[>] 0. Consequently (A_k) is nondecreasing and every A_k is Borel. Moreover ⋃_k A_k = B_ρ(ξ) ∖ {ξ}: if x ∈ A_k then ‖x − ξ‖ > s_k > 0, so x ≠ ξ; conversely, if x ∈ B_ρ(ξ) and x ≠ ξ, then ‖x − ξ‖ > 0, so s_k < ‖x − ξ‖ for some k (as s_k → 0), and x ∈ A_k.
(b) By (H) with σ = s_k: w is μ-integrable on A_k and ∫_{A_k} w dμ = a(ρ) − a(s_k).
(c) Finite lower integral. Since w ≥ 0 is integrable on A_k, ∫⁻_{A_k} ofReal(w) dμ = ofReal(∫_{A_k} w dμ) = ofReal(a(ρ) − a(s_k)) (ofReal_integral_eq_lintegral_ofReal). This is ≤ ofReal(a(ρ) − L), because L ≤ a(s_k) (s_k ∈ (0, R)). The family (A_k) is increasing, hence directed, so by monotone convergence the lower integral over the union is the supremum (setLIntegral_iUnion_of_directed): ∫⁻_{B_ρ(ξ)∖{ξ}} ofReal(w) dμ = sup_k ∫⁻_{A_k} ofReal(w) dμ ≤ ofReal(a(ρ) − L) < ∞.
(d) Integrability on B_ρ(ξ) ∖ {ξ}. By (b), w is μ-a.e. strongly measurable on each A_k, hence on the countable union ⋃_k A_k = B_ρ(ξ)∖{ξ} (aestronglyMeasurable_iUnion_iff). Together with (c) and w ≥ 0 (hasFiniteIntegral_iff_ofReal), w is μ-integrable on B_ρ(ξ) ∖ {ξ}.
(e) The point ξ. Since w(ξ) = 0 (1b), w is μ-integrable on {ξ} whatever μ{ξ} is (integrableOn_singleton_iff), and ∫_{{ξ}} w dμ = 0 because w vanishes on {ξ}.
(f) Integrability on B_ρ(ξ). Since ‖ξ − ξ‖ = 0 ≤ ρ, we have ξ ∈ B_ρ(ξ), so B_ρ(ξ) = (B_ρ(ξ)∖{ξ}) ∪ {ξ}, a disjoint union of Borel sets. By (d) and (e), w is μ-integrable on B_ρ(ξ). This is the IntegrableOn part of conclusion 2.
(g) Value of the integral. By (d), w is integrable on ⋃_k A_k, and (A_k) is increasing and measurable, so ∫_{A_k} w dμ → ∫_{B_ρ(ξ)∖{ξ}} w dμ (dominated convergence; tendsto_setIntegral_of_monotone). On the other hand, ∫_{A_k} w dμ = a(ρ) − a(s_k) → a(ρ) − L, because s_k → 0 along 𝓝[>] 0 and a(s) → L as s ↓ 0 (Step 3). By uniqueness of limits, ∫_{B_ρ(ξ)∖{ξ}} w dμ = a(ρ) − L. With (e), (f) and additivity of the integral over the disjoint union (setIntegral_union): ∫_{B_ρ(ξ)} w dμ = (a(ρ) − L) + 0 = a(ρ) − L.
(h) Conclusion. By (1d) and Step 3, Q(ρ) − Θ = ω_n⁻¹a(ρ) − ω_n⁻¹L = ω_n⁻¹(a(ρ) − L) = ω_n⁻¹ ∫_{B_ρ(ξ)} w dμ. That is, V.weight.real (closedBall ξ ρ)/(omega n · ρⁿ) − V.density ξ = (omega n)⁻¹ · ∫_{closedBall ξ ρ} V.normalRadialSq ξ x/‖x − ξ‖ⁿ dμ.

6. Steps 2, 5, 3 and 4 give, in that order, the four conjuncts of the statement:
- MonotoneOn on Ioo 0 R;
- for 0 < ρ < R, IntegrableOn on closedBall ξ ρ together with identity 3.10;
- 0 < R → V.HasDensityAt ξ (V.density ξ);
- for 0 < ρ < R, V.density ξ ≤ V.weight.real (closedBall ξ ρ)/(omega n · ρⁿ). ∎

Appendix (reference only; the numbered proof above is complete). The decomposition author compiled the following Lean proof of exactly this statement. It used `import GMT.Ch04.Submission` with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c) and has no errors or warnings. `#print axioms` reports only [propext, Classical.choice, Quot.sound].

import GMT.Ch04.Submission

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal ContDiff CompactlySupported

namespace GMT.Ch04

noncomputable section

open RectifiableVarifold

namespace Submission

theorem stationary_ratio_limit_of_annulus_identity : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (ξ : Ambient n ℓ) (R : ℝ), (∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ < R → IntegrableOn (fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ V.weight.real (closedBall ξ ρ) / ρ ^ n - V.weight.real (closedBall ξ σ) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) → MonotoneOn (fun ρ ↦ V.weight.real (closedBall ξ ρ) / ρ ^ n) (Ioo 0 R) ∧ (∀ ρ : ℝ, 0 < ρ → ρ < R → IntegrableOn (fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) (closedBall ξ ρ) V.weight ∧ V.weight.real (closedBall ξ ρ) / (omega n * ρ ^ n) - V.density ξ = (omega n)⁻¹ * ∫ x in closedBall ξ ρ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) ∧ (0 < R → V.HasDensityAt ξ (V.density ξ)) ∧ ∀ ρ : ℝ, 0 < ρ → ρ < R → V.density ξ ≤ V.weight.real (closedBall ξ ρ) / (omega n * ρ ^ n) := by
  intro n ℓ V ξ R hid
  set μ := V.weight with hμ
  set w : Ambient n ℓ → ℝ := fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n with hw
  set a : ℝ → ℝ := fun ρ ↦ μ.real (closedBall ξ ρ) / ρ ^ n with ha
  have hw0 : ∀ x, 0 ≤ w x := fun x ↦
    div_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (pow_nonneg (norm_nonneg _) _)
  have hwξ : w ξ = 0 := by simp [hw, normalRadialSq]
  have ha0 : ∀ ρ, 0 < ρ → 0 ≤ a ρ := fun ρ hρ ↦
    div_nonneg measureReal_nonneg (pow_nonneg hρ.le _)
  -- Step 1 (3.8): monotonicity.
  have hmono : MonotoneOn a (Ioo 0 R) := by
    intro σ hσ ρ hρ hσρ
    have h := (hid σ ρ hσ.1 hσρ hρ.2).2
    have hnn : 0 ≤ ∫ x in closedBall ξ ρ \ closedBall ξ σ, w x ∂μ :=
      setIntegral_nonneg (measurableSet_closedBall.diff measurableSet_closedBall)
        fun x _ ↦ hw0 x
    change a ρ - a σ = _ at h
    linarith
  -- The density quotient is `ωₙ⁻¹ a`.
  have hQ : ∀ ρ, μ.real (closedBall ξ ρ) / (omega n * ρ ^ n) = (omega n)⁻¹ * a ρ := by
    intro ρ
    simp only [ha, div_eq_mul_inv, mul_inv]
    ring
  have hωinv : 0 ≤ (omega n)⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
  -- Step 2 (3.9): the limit `L` and the density.
  have hlim : 0 < R → Tendsto a (𝓝[>] 0) (𝓝 (sInf (a '' Ioo 0 R))) ∧
      V.density ξ = (omega n)⁻¹ * sInf (a '' Ioo 0 R) ∧
      Tendsto (fun ρ ↦ μ.real (closedBall ξ ρ) / (omega n * ρ ^ n)) (𝓝[>] 0)
        (𝓝 ((omega n)⁻¹ * sInf (a '' Ioo 0 R))) := by
    intro hR
    have hbdd : BddBelow (a '' Ioo 0 R) := ⟨0, by
      rintro _ ⟨ρ, hρ, rfl⟩
      exact ha0 ρ hρ.1⟩
    have hT : Tendsto a (𝓝[>] 0) (𝓝 (sInf (a '' Ioo 0 R))) :=
      MonotoneOn.tendsto_nhdsWithin_Ioo_right ⟨R / 2, by positivity, by linarith⟩ hmono hbdd
    have hT' : Tendsto (fun ρ ↦ μ.real (closedBall ξ ρ) / (omega n * ρ ^ n)) (𝓝[>] 0)
        (𝓝 ((omega n)⁻¹ * sInf (a '' Ioo 0 R))) := by
      simp_rw [hQ]
      exact hT.const_mul _
    exact ⟨hT, hT'.limUnder_eq, hT'⟩
  refine ⟨hmono, ?_, ?_, ?_⟩
  · -- Step 3 (3.10): monotone convergence.
    intro ρ hρ hρR
    have hR : 0 < R := hρ.trans hρR
    obtain ⟨hT, hdens, -⟩ := hlim hR
    set L := sInf (a '' Ioo 0 R) with hL
    have hbdd : BddBelow (a '' Ioo 0 R) := ⟨0, by
      rintro _ ⟨ρ, hρ, rfl⟩
      exact ha0 ρ hρ.1⟩
    have hLle : ∀ s ∈ Ioo 0 R, L ≤ a s := fun s hs ↦ csInf_le hbdd (mem_image_of_mem _ hs)
    set s : ℕ → ℝ := fun k ↦ ρ / (k + 1) with hs
    have hs0 : ∀ k, 0 < s k := fun k ↦ by positivity
    have hsρ : ∀ k, s k ≤ ρ := fun k ↦ div_le_self hρ.le (by norm_cast; omega)
    have hsanti : Antitone s := fun i j hij ↦ by
      simp only [hs]
      gcongr
    set A : ℕ → Set (Ambient n ℓ) := fun k ↦ closedBall ξ ρ \ closedBall ξ (s k) with hA
    have hAmono : Monotone A := fun i j hij ↦
      sdiff_subset_sdiff_right (closedBall_subset_closedBall (hsanti hij))
    have hAmeas : ∀ k, MeasurableSet (A k) := fun k ↦
      measurableSet_closedBall.diff measurableSet_closedBall
    have hAint : ∀ k, IntegrableOn w (A k) μ := fun k ↦ (hid (s k) ρ (hs0 k) (hsρ k) hρR).1
    have hAeq : ∀ k, ∫ x in A k, w x ∂μ = a ρ - a (s k) := fun k ↦
      (hid (s k) ρ (hs0 k) (hsρ k) hρR).2.symm
    have hUnion : (⋃ k, A k) = closedBall ξ ρ \ {ξ} := by
      ext x
      simp only [hA, mem_iUnion, Set.mem_sdiff, mem_closedBall, mem_singleton_iff, not_le]
      constructor
      · rintro ⟨k, hxρ, hxk⟩
        refine ⟨hxρ, fun hx ↦ ?_⟩
        rw [hx, dist_self] at hxk
        exact lt_irrefl _ ((hs0 k).trans hxk)
      · rintro ⟨hxρ, hxξ⟩
        have hd : 0 < dist x ξ := dist_pos.2 hxξ
        have hts : Tendsto s atTop (𝓝 0) := by
          have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ρ
          rw [mul_zero] at this
          refine this.congr fun k ↦ ?_
          simp only [hs]
          ring
        obtain ⟨k, hk⟩ := (hts.eventually (gt_mem_nhds hd)).exists
        exact ⟨k, hxρ, hk⟩
    -- the lintegrals over `A k` are bounded by `a ρ - L`
    have hlin : ∀ k, ∫⁻ x in A k, ENNReal.ofReal (w x) ∂μ = ENNReal.ofReal (a ρ - a (s k)) := by
      intro k
      rw [← hAeq k, ofReal_integral_eq_lintegral_ofReal (hAint k)
        (Eventually.of_forall fun x ↦ hw0 x)]
    have hlinU : ∫⁻ x in ⋃ k, A k, ENNReal.ofReal (w x) ∂μ ≤ ENNReal.ofReal (a ρ - L) := by
      rw [setLIntegral_iUnion_of_directed _ hAmono.directed_le]
      refine iSup_le fun k ↦ ?_
      rw [hlin k]
      exact ENNReal.ofReal_le_ofReal (by linarith [hLle (s k) ⟨hs0 k, (hsρ k).trans_lt hρR⟩])
    have hintU : IntegrableOn w (⋃ k, A k) μ := by
      refine ⟨aestronglyMeasurable_iUnion_iff.2 fun k ↦ (hAint k).1, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x ↦ hw0 x)]
      exact hlinU.trans_lt ENNReal.ofReal_lt_top
    have hintξ : IntegrableOn w {ξ} μ := (integrableOn_singleton_iff (hfx := enorm_ne_top)).2 (Or.inl (by rw [hwξ, enorm_zero]))
    have hball : closedBall ξ ρ = (⋃ k, A k) ∪ {ξ} := by
      rw [hUnion, sdiff_union_self, union_eq_left.2 (singleton_subset_iff.2
        (mem_closedBall_self hρ.le))]
    have hint : IntegrableOn w (closedBall ξ ρ) μ := by
      rw [hball]
      exact hintU.union hintξ
    -- the value of the integral
    have hlimU : Tendsto (fun k ↦ ∫ x in A k, w x ∂μ) atTop (𝓝 (∫ x in ⋃ k, A k, w x ∂μ)) :=
      tendsto_setIntegral_of_monotone hAmeas hAmono hintU
    have hsT : Tendsto s atTop (𝓝[>] 0) := by
      have hts : Tendsto s atTop (𝓝 0) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ρ
        rw [mul_zero] at this
        refine this.congr fun k ↦ ?_
        simp only [hs]
        ring
      exact tendsto_nhdsWithin_iff.2 ⟨hts, Eventually.of_forall hs0⟩
    have hlim2 : Tendsto (fun k ↦ ∫ x in A k, w x ∂μ) atTop (𝓝 (a ρ - L)) := by
      simp_rw [hAeq]
      exact tendsto_const_nhds.sub (hT.comp hsT)
    have hvalU : ∫ x in ⋃ k, A k, w x ∂μ = a ρ - L := tendsto_nhds_unique hlimU hlim2
    have hvalξ : ∫ x in ({ξ} : Set (Ambient n ℓ)), w x ∂μ = 0 := by
      rw [setIntegral_congr_fun (measurableSet_singleton ξ) (g := fun _ ↦ (0 : ℝ))
        (fun x hx ↦ by rw [mem_singleton_iff.1 hx]; exact hwξ)]
      simp
    have hdisj : Disjoint (⋃ k, A k) {ξ} := by
      rw [hUnion]
      exact disjoint_sdiff_left
    have hval : ∫ x in closedBall ξ ρ, w x ∂μ = a ρ - L := by
      rw [hball, setIntegral_union hdisj (measurableSet_singleton ξ) hintU hintξ, hvalU, hvalξ,
        add_zero]
    refine ⟨hint, ?_⟩
    change μ.real (closedBall ξ ρ) / (omega n * ρ ^ n) - V.density ξ =
      (omega n)⁻¹ * ∫ x in closedBall ξ ρ, w x ∂μ
    rw [hQ, hdens, hval]
    ring
  · intro hR
    obtain ⟨-, hdens, hT'⟩ := hlim hR
    unfold HasDensityAt
    rw [hdens]
    exact hT'
  · intro ρ hρ hρR
    have hR : 0 < R := hρ.trans hρR
    obtain ⟨-, hdens, -⟩ := hlim hR
    have hbdd : BddBelow (a '' Ioo 0 R) := ⟨0, by
      rintro _ ⟨ρ, hρ, rfl⟩
      exact ha0 ρ hρ.1⟩
    rw [hQ, hdens]
    exact mul_le_mul_of_nonneg_left (csInf_le hbdd (mem_image_of_mem _ ⟨hρ, hρR⟩)) hωinv

end Submission

end

end GMT.Ch04

## Key steps

1. Elementary facts: w ≥ 0, w(ξ) = 0 (division by 0 is 0), a ≥ 0 on (0, ∞), μ(B_r)/(ω_n rⁿ) = ω_n⁻¹a(r), ω_n⁻¹ ≥ 0
2. Annulus identity and ∫ w ≥ 0 give that a is monotone on (0, R) (3.8)
3. Monotone and bounded below by 0: a(s) → L = inf_{(0,R)} a as s ↓ 0; the quotient tends to ω_n⁻¹L, so V.density ξ = ω_n⁻¹L (limUnder on the nontrivial filter 𝓝[>]0) and HasDensityAt (3.9)
4. L ≤ a(ρ) gives V.density ξ ≤ μ(B_ρ)/(ω_nρⁿ)
5. Monotone convergence on A_k = B_ρ ∖ B_{ρ/(k+1)} ↑ B_ρ ∖ {ξ}: lintegral ≤ a(ρ) − L < ∞, integrability on B_ρ using w(ξ) = 0, ∫_{B_ρ} w = a(ρ) − L, hence 3.10

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `rg -n 'theorem (MonotoneOn|Monotone)\.tendsto_nhdsWithin_I(oi|io|oo)' <snapshot>/mathlib/Mathlib`
- `rg -n 'tendsto_nhdsWithin_Ioo_left|tendsto_nhdsWithin_Ioo_right|MonotoneOn.tendsto_nhdsGT|tendsto_nhdsGT' <snapshot>/mathlib/Mathlib/Topology/Order/*.lean`
- `rg -n 'theorem tendsto_measure_cthickening|theorem tendsto_measure_closedBall|tendsto_measure_biInter_gt|theorem tendsto_measure_iInter|tendsto_measure_cthickening_of_isCompact' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem (tendsto_setIntegral_of_monotone|tendsto_setLIntegral_of_monotone|lintegral_iUnion_mono|setLIntegral_iUnion_of_directed|lintegral_iUnion_of_directed|integrableOn_iUnion_of_summable|tendsto_lintegral_of_monotone)' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem gradient_const|theorem gradient_fun_const' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem locallyIntegrableOn_zero|locallyIntegrableOn_const' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem setIntegral_const|theorem integrableOn_singleton_iff|theorem aestronglyMeasurable_iUnion_iff|theorem ofReal_integral_eq_lintegral_ofReal|theorem Tendsto.limUnder_eq|theorem lintegral_singleton' <snapshot>/mathlib/Mathlib`
- `rg -n 'limUnder_eq' <snapshot>/mathlib/Mathlib/Topology/Separation/*.lean`
- `rg -n 'UpperSemicontinuous|monotonicity|HasDensity' lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `grep -rl 'stationary_ratio_limit_of_annulus_identity|stationary_density_usc_of_ratio_bound' .humanize GMT lake-packages-25730c7c/simongmt/Poincare lake-packages-25730c7c/mathlib/Mathlib`
- `sed -n 290,365p book/sources/chapter-04-source.txt`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/sm-a1-audit/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/sm-a1-audit/olean lean /tmp/sm-a1-audit/{Assembly,ChildA,ChildB,Combined,Bare}.lean (with #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Order/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Density.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-stationary-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root/speculative-prompt-v2.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-04-source.txt`
- `/tmp/sm-a1-audit/Assembly.lean`
- `/tmp/sm-a1-audit/ChildA.lean`
- `/tmp/sm-a1-audit/ChildB.lean`
- `/tmp/sm-a1-audit/Combined.lean`
- `/tmp/sm-a1-audit/Bare.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (sha256 6e58e5dd…0f4770b); the Mathlib revision is 25730c7c.

Every ingredient of the two children exists in the pinned Mathlib:
- MonotoneOn.tendsto_nhdsWithin_Ioo_right (Topology/Order/Monotone.lean:457): the monotone limit at 0+.
- tendsto_measure_biInter_gt (MeasureTheory/Measure/Continuity.lean:266): continuity from above on the closed balls B_{ρ+δ}(ξ).
- setLIntegral_iUnion_of_directed (Integral/Lebesgue/Basic.lean:668) and tendsto_setIntegral_of_monotone (Integral/Bochner/Set.lean:290): monotone convergence on B_ρ∖B_{ρ/(k+1)}.
- integrableOn_singleton_iff (Integral/IntegrableOn.lean:211; it has an autoParam hfx) and ofReal_integral_eq_lintegral_ofReal (Bochner/Basic.lean:739).
- Filter.Tendsto.limUnder_eq (Topology/Separation/Hausdorff.lean:296).

The parent's Steps 1–2 use gradient_fun_const (Gradient/Basic.lean:368), locallyIntegrableOn_zero (LocallyIntegrable.lean:379) and setIntegral_const (Bochner/Set.lean:524).

SimonGMT's Chapter04 upper-semicontinuity and density lemmas (Density.lean:470 IsStationaryIn.upperSemicontinuousOn_stationaryDensityReal) are stated for its own structure RectifiableVarifold (Chapter04/Basic.lean:53, with a lower-density ℝ≥0∞ density), not for the contract's quotient type and limUnder density. They are not usable here, and the children need nothing from SimonGMT.

The two new names (stationary_ratio_limit_of_annulus_identity, stationary_density_usc_of_ratio_bound) occur nowhere in .humanize, GMT, SimonGMT or Mathlib.

With GMT.Ch04.Submission compiled to an olean:
- Both child types elaborate in the bare contract scope.
- Complete Lean proofs of both children compile with no errors or warnings, depending only on propext, Classical.choice and Quot.sound.
- The parent assembly typechecks against the sibling's exact frozen type plus the two children. Its only sorryAx comes from the stubbed sibling.

Simon Ch. 4, 3.6–3.11 (local source lines 290–349) matches the parent's Steps 3–6.
