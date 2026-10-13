# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_weak_star-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the Claim of step 3 of the parent proof together with its proof (3.0)–(3.3): induction on the order r, for all a, b, η simultaneously; step (3.0) is the sibling test_density and the identity (P) of (3.2) is the sibling minor_ibp_lipschitz. This is the classical weak continuity of Jacobian minors in W^{1,∞} (J. M. Ball, Arch. Rational Mech. Anal. 63 (1977) 337–403; I. Fonseca, G. Leoni, J. Malý, Arch. Rational Mech. Anal. 178 (2005) 411–448).

Notation. λ = Lebesgue measure; e_i := EuclideanSpace.single i 1; u^c := EuclideanSpace.proj c ∘ u. For a : Fin (r+1) → Fin Q, b : Fin (r+1) → Fin k and q ∈ Fin (r+1) put a′ := (t ↦ a(t.succ)) : Fin r → Fin Q and b^{(q)} := (s ↦ b(q.succAbove s)) : Fin r → Fin k. Then the cofactor of the sibling minor_ibp_lipschitz is C_q(u) = (−1)^q·M_{a′,b^{(q)}}(u).

0. (Bounds and measurability.) Let u be C-Lipschitz on Ω and w ∈ Ω. Since Ω is a neighbourhood of w, ‖fderiv ℝ u w‖ ≤ C (Mathlib norm_fderiv_le_of_lipschitzOn). Hence every entry satisfies |EuclideanSpace.proj c (fderiv ℝ u w (e_i))| ≤ ‖fderiv ℝ u w (e_i)‖ ≤ ‖fderiv ℝ u w‖·‖e_i‖ ≤ C (PiLp.norm_apply_le, ‖e_i‖ = 1), and by the Leibniz formula and the triangle inequality |M_{a,b}(u)(w)| ≤ r!·C^r for w ∈ Ω (an n×n matrix with entries bounded by c has |det| ≤ n!·c^n; prove it from Matrix.det_apply, since Matrix.det_le is not imported). The function w ↦ M_{a,b}(u)(w) is Borel measurable: each entry is EuclideanSpace.proj c applied to the measurable function w ↦ fderiv ℝ u w (e_i) (measurable_fderiv_apply_const), and the determinant is continuous in the entries (Continuous.matrix_det on the function space, measurable_pi_iff). Also u is continuous on Ω (LipschitzOnWith.continuousOn).

We prove by induction on r the statement P(r): for all a : Fin r → Fin Q, b : Fin r → Fin k and all η integrable on Ω, ∫_Ω η·M_{a,b}(v_j) → ∫_Ω η·M_{a,b}(v₀).

1. (r = 0.) A 0×0 determinant equals 1 (Matrix.det_isEmpty), so every term of the sequence equals ∫_Ω η: the sequence is constant.

2. (Step r → r+1: reduction to C¹ test functions.) Assume P(r) and fix a : Fin (r+1) → Fin Q and b : Fin (r+1) → Fin k. Apply the sibling test_density with f_j := M_{a,b}(v_j), f₀ := M_{a,b}(v₀) and B := (r+1)!·C^{r+1}: by Step 0 these functions are a.e.-strongly measurable for λ restricted to Ω and bounded by B on Ω. So it suffices to prove, for every φ : ℝ^k → ℝ of class C¹ with compact support and tsupport φ ⊆ Ω,
 ∫_Ω φ·M_{a,b}(v_j) → ∫_Ω φ·M_{a,b}(v₀).  (★)

3. (Integration by parts.) Fix such φ, let K := tsupport φ (compact, K ⊆ Ω) and dφ_q(w) := fderiv ℝ φ w (e_{b(q)}). dφ_q is continuous (φ ∈ C¹) and vanishes outside K (support_fderiv_subset), hence it has compact support and is integrable. By the sibling minor_ibp_lipschitz, for u ∈ {v_j, v₀},
 ∫_Ω φ·M_{a,b}(u) = −Σ_{q∈Fin(r+1)} ∫_Ω u^{a(0)}·((−1)^q·M_{a′,b^{(q)}}(u))·dφ_q.
 Hence (★) follows (tendsto_finsetSum, Tendsto.neg) once we show, for each fixed q,
 I_j := ∫_Ω v_j^{a(0)}·((−1)^q M_{a′,b^{(q)}}(v_j))·dφ_q → I_0 := ∫_Ω v₀^{a(0)}·((−1)^q M_{a′,b^{(q)}}(v₀))·dφ_q.  (★★)

4. (Integrability.) Each u ∈ {v_j, v₀} is continuous on Ω ⊇ K, so |u^{a(0)}| ≤ P_u on the compact set K for some constant P_u ≥ 0 (IsCompact.exists_bound_of_continuousOn). Every function F used below is a.e.-strongly measurable for λ restricted to Ω and satisfies |F(w)| ≤ c·|dφ_q(w)| for all w ∈ Ω with a constant c (on K use the bounds P_u and Step 0; off K, F(w) = 0 because F contains the factor dφ_q(w) = 0). Hence F is integrable on Ω (Integrable.mono′ with the integrable majorant c|dφ_q|). This applies to (v_j^{a(0)} − v₀^{a(0)})·((−1)^q M_{a′,b^{(q)}}(v_j))·dφ_q (c = (P_{v_j} + P_{v₀})·r!C^r) and to η_q·M_{a′,b^{(q)}}(u) (c = P_{v₀}·r!C^r), where η_q := v₀^{a(0)}·dφ_q. In particular η_q itself is integrable on Ω (c = P_{v₀}).

5. (Splitting.) By linearity (Step 4),
 I_j = ∫_Ω (v_j^{a(0)} − v₀^{a(0)})·((−1)^q M_{a′,b^{(q)}}(v_j))·dφ_q + (−1)^q·∫_Ω η_q·M_{a′,b^{(q)}}(v_j), and I_0 = 0 + (−1)^q·∫_Ω η_q·M_{a′,b^{(q)}}(v₀).

6. (First term → 0.) Let ε > 0, B′ := r!·C^r, I_φ := ∫ |dφ_q| dλ and δ := ε/(2(B′I_φ + 1)) > 0. By uniform convergence on Ω (Metric.tendstoUniformlyOn_iff) there is N with ‖v_j(w) − v₀(w)‖ < δ for all j ≥ N and w ∈ Ω; then |v_j^{a(0)}(w) − v₀^{a(0)}(w)| ≤ ‖v_j(w) − v₀(w)‖ < δ (PiLp.norm_apply_le). Using |M_{a′,b^{(q)}}(v_j)| ≤ B′ on Ω (Step 0), the first integrand is bounded on Ω by δB′|dφ_q|, so for j ≥ N the first integral has absolute value ≤ δB′I_φ < ε (norm_integral_le_of_norm_le, setIntegral_le_integral). Hence it tends to 0.

7. (Second term: induction hypothesis.) P(r), applied to a′, b^{(q)} and the function η_q, which is integrable on Ω by Step 4, gives ∫_Ω η_q·M_{a′,b^{(q)}}(v_j) → ∫_Ω η_q·M_{a′,b^{(q)}}(v₀); multiplication by the constant (−1)^q preserves the limit.

8. (Conclusion of the step.) By Steps 5–7, I_j → 0 + (−1)^q·∫_Ω η_q·M_{a′,b^{(q)}}(v₀) = I_0, which is (★★). Hence (★) holds for every admissible φ, and Step 2 gives P(r+1). By induction P(r) holds for every r, which is the statement. ∎

Reference implementation (compiled). The following single theorem, whose hypotheses hA and hD are the frozen types of the siblings test_density and minor_ibp_lipschitz (instantiate hA := Submission.deformation_ipl_mwc_test_density and hD := Submission.deformation_ipl_mwc_minor_ibp_lipschitz, or replace them by these names), was compiled with `lake env lean` against the frozen `import GMT.Ch06.Submission` in the exact comparator scope (namespace GMT.Ch06 and the Contract's opens). It needs no new import, is fully proved, and #print axioms gives propext, Classical.choice, Quot.sound. It follows Steps 0–8 above; the prose proof governs.

theorem _root_.TestMWC4.weak_star_ref (hA : ∀ (k : ℕ) (Ω : Set (Eucl k)) (B : ℝ) (f : ℕ → Eucl k → ℝ) (f₀ : Eucl k → ℝ), IsOpen Ω → (∀ j, AEStronglyMeasurable (f j) ((volume : Measure (Eucl k)).restrict Ω)) → AEStronglyMeasurable f₀ ((volume : Measure (Eucl k)).restrict Ω) → (∀ j, ∀ w ∈ Ω, |f j w| ≤ B) → (∀ w ∈ Ω, |f₀ w| ≤ B) → (∀ φ : Eucl k → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω → Tendsto (fun j => ∫ w in Ω, φ w * f j w ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, φ w * f₀ w ∂(volume : Measure (Eucl k))))) → ∀ η : Eucl k → ℝ, IntegrableOn η Ω (volume : Measure (Eucl k)) → Tendsto (fun j => ∫ w in Ω, η w * f j w ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, η w * f₀ w ∂(volume : Measure (Eucl k))))) (hD : ∀ (k Q r : ℕ) (Ω : Set (Eucl k)) (C : ℝ≥0) (a : Fin (r + 1) → Fin Q) (b : Fin (r + 1) → Fin k) (v : Eucl k → Eucl Q) (φ : Eucl k → ℝ), IsOpen Ω → LipschitzOnWith C v Ω → ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω → ∫ w in Ω, φ w * Matrix.det (Matrix.of fun t s : Fin (r + 1) => EuclideanSpace.proj (a t) (fderiv ℝ v w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k)) = -∑ q : Fin (r + 1), ∫ w in Ω, EuclideanSpace.proj (a 0) (v w) * ((-1 : ℝ) ^ (q : ℕ) * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t.succ) (fderiv ℝ v w (EuclideanSpace.single (b (q.succAbove s)) 1)))) * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) ∂(volume : Measure (Eucl k))) : (∀ (k Q : ℕ) (Ω : Set (Eucl k)) (C : ℝ≥0) (v : ℕ → Eucl k → Eucl Q) (v₀ : Eucl k → Eucl Q), IsOpen Ω → (∀ j, LipschitzOnWith C (v j) Ω) → LipschitzOnWith C v₀ Ω → TendstoUniformlyOn v v₀ atTop Ω → ∀ (r : ℕ) (a : Fin r → Fin Q) (b : Fin r → Fin k) (η : Eucl k → ℝ), IntegrableOn η Ω (volume : Measure (Eucl k)) → Tendsto (fun j => ∫ w in Ω, η w * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t) (fderiv ℝ (v j) w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, η w * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t) (fderiv ℝ v₀ w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k))))) := by
  intro k Q Ω C v v₀ hΩ hv hv₀ hconv r
  -- |det A| ≤ n! c^n for entries bounded by c (Matrix.det_le is not imported)
  have abs_det_le : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ),
      (∀ i j, |A i j| ≤ c) → |A.det| ≤ (Nat.factorial n : ℝ) * c ^ n := by
    intro n A c hA
    rw [Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin n), |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), c ^ n := by
          gcongr with σ
          have h1 : |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = |∏ i, A (σ i) i| := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
          rw [h1, Finset.abs_prod]
          calc ∏ i, |A (σ i) i| ≤ ∏ _i : Fin n, c := by
                gcongr with i
                exact hA _ _
            _ = c ^ n := by simp
      _ = (Nat.factorial n : ℝ) * c ^ n := by simp [Fintype.card_perm]
  -- bound and measurability of the minors of a map Lipschitz on Ω
  have minor_facts : ∀ {n : ℕ} (a : Fin n → Fin Q) (b : Fin n → Fin k) (u : Eucl k → Eucl Q),
      LipschitzOnWith C u Ω →
      (∀ w ∈ Ω, |Matrix.det (Matrix.of fun t s : Fin n => EuclideanSpace.proj (a t)
          (fderiv ℝ u w (EuclideanSpace.single (b s) 1)))| ≤ (Nat.factorial n : ℝ) * (C : ℝ) ^ n) ∧
      Measurable (fun w => Matrix.det (Matrix.of fun t s : Fin n => EuclideanSpace.proj (a t)
          (fderiv ℝ u w (EuclideanSpace.single (b s) 1)))) := by
    intro n a b u hu
    constructor
    · intro w hw
      apply abs_det_le
      intro t s
      have h1 : ‖fderiv ℝ u w‖ ≤ C := norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hw) hu
      calc |EuclideanSpace.proj (a t) (fderiv ℝ u w (EuclideanSpace.single (b s) 1))|
          = ‖(fderiv ℝ u w (EuclideanSpace.single (b s) 1)) (a t)‖ := by simp [Real.norm_eq_abs]
        _ ≤ ‖fderiv ℝ u w (EuclideanSpace.single (b s) 1)‖ := PiLp.norm_apply_le _ _
        _ ≤ ‖fderiv ℝ u w‖ * ‖EuclideanSpace.single (b s) (1 : ℝ)‖ := (fderiv ℝ u w).le_opNorm _
        _ ≤ C := by simpa using h1
    · have hdetc : Continuous fun A : Fin n → Fin n → ℝ => (Matrix.of A).det :=
        Continuous.matrix_det continuous_id
      have : ∀ t s : Fin n, Measurable fun w =>
          EuclideanSpace.proj (a t) (fderiv ℝ u w (EuclideanSpace.single (b s) 1)) := fun t s =>
        (EuclideanSpace.proj (a t)).continuous.measurable.comp (measurable_fderiv_apply_const ℝ u _)
      exact hdetc.measurable.comp (measurable_pi_iff.2 fun t => measurable_pi_iff.2 fun s => this t s)
  induction r with
  | zero =>
    intro a b η hη
    simp only [Matrix.det_isEmpty, mul_one]
    exact tendsto_const_nhds
  | succ r ih =>
    intro a b η hη
    let M : (Eucl k → Eucl Q) → Eucl k → ℝ := fun u w => Matrix.det (Matrix.of fun t s : Fin (r + 1) =>
      EuclideanSpace.proj (a t) (fderiv ℝ u w (EuclideanSpace.single (b s) 1)))
    refine hA k Ω ((Nat.factorial (r + 1) : ℝ) * (C : ℝ) ^ (r + 1)) (fun j => M (v j)) (M v₀) hΩ
      (fun j => (minor_facts a b (v j) (hv j)).2.aestronglyMeasurable)
      (minor_facts a b v₀ hv₀).2.aestronglyMeasurable
      (fun j => (minor_facts a b (v j) (hv j)).1)
      (minor_facts a b v₀ hv₀).1 ?_ η hη
    intro φ hφ hφc hφΩ
    let M' : Fin (r + 1) → (Eucl k → Eucl Q) → Eucl k → ℝ := fun q u w =>
      Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t.succ)
        (fderiv ℝ u w (EuclideanSpace.single (b (q.succAbove s)) 1)))
    let dφ : Fin (r + 1) → Eucl k → ℝ := fun q w => fderiv ℝ φ w (EuclideanSpace.single (b q) 1)
    let p : (Eucl k → Eucl Q) → Eucl k → ℝ := fun u w => EuclideanSpace.proj (a 0) (u w)
    have hDu : ∀ u, LipschitzOnWith C u Ω → ∫ w in Ω, φ w * M u w ∂(volume : Measure (Eucl k)) =
        -∑ q : Fin (r + 1), ∫ w in Ω, p u w * ((-1 : ℝ) ^ (q : ℕ) * M' q u w) * dφ q w
          ∂(volume : Measure (Eucl k)) :=
      fun u hu => hD k Q r Ω C a b u φ hΩ hu hφ hφc hφΩ
    have hfun : (fun j => ∫ w in Ω, φ w * M (v j) w ∂(volume : Measure (Eucl k))) = fun j =>
        -∑ q : Fin (r + 1), ∫ w in Ω, p (v j) w * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w
          ∂(volume : Measure (Eucl k)) := funext fun j => hDu _ (hv j)
    rw [hfun, hDu v₀ hv₀]
    refine (tendsto_finsetSum _ fun q _ => ?_).neg
    -- facts about the test function and the maps on K = tsupport φ
    set K := tsupport φ with hK
    have hKc : IsCompact K := hφc
    have hdφc : Continuous (dφ q) :=
      (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hdφ0 : ∀ w, w ∉ K → dφ q w = 0 := by
      intro w hw
      have : fderiv ℝ φ w = 0 := by
        by_contra h
        exact hw (support_fderiv_subset ℝ (Function.mem_support.2 h))
      simp [dφ, this]
    have hdφsupp : HasCompactSupport (dφ q) :=
      HasCompactSupport.of_support_subset_isCompact hKc fun w hw => by
        by_contra h; exact hw (hdφ0 w h)
    have hdφint : Integrable (dφ q) (volume : Measure (Eucl k)) :=
      hdφc.integrable_of_hasCompactSupport hdφsupp
    have hpbd : ∀ u, LipschitzOnWith C u Ω → ∃ P : ℝ, 0 ≤ P ∧ ∀ w ∈ K, |p u w| ≤ P := by
      intro u hu
      obtain ⟨P, hP⟩ := hKc.exists_bound_of_continuousOn
        (((EuclideanSpace.proj (a 0)).continuous.comp_continuousOn hu.continuousOn).mono hφΩ)
      refine ⟨max P 0, le_max_right _ _, fun w hw => le_trans ?_ (le_max_left _ _)⟩
      have := hP w hw
      simp only [Function.comp_apply, Real.norm_eq_abs] at this
      exact this
    have hpm : ∀ u, LipschitzOnWith C u Ω →
        AEStronglyMeasurable (p u) ((volume : Measure (Eucl k)).restrict Ω) := fun u hu =>
      ((EuclideanSpace.proj (a 0)).continuous.comp_continuousOn hu.continuousOn).aestronglyMeasurable
        hΩ.measurableSet
    have hM'b : ∀ u, LipschitzOnWith C u Ω → ∀ w ∈ Ω, |M' q u w| ≤ (Nat.factorial r : ℝ) * (C : ℝ) ^ r :=
      fun u hu => (minor_facts (fun t => a t.succ) (fun s => b (q.succAbove s)) u hu).1
    have hM'm : ∀ u, LipschitzOnWith C u Ω → Measurable (M' q u) :=
      fun u hu => (minor_facts (fun t => a t.succ) (fun s => b (q.succAbove s)) u hu).2
    set B' : ℝ := (Nat.factorial r : ℝ) * (C : ℝ) ^ r with hB'
    have hB'0 : 0 ≤ B' := by positivity
    -- generic integrability: anything a.e.-measurable on Ω and bounded by c * |dφ q| on Ω
    have hint : ∀ (F : Eucl k → ℝ) (c : ℝ), AEStronglyMeasurable F ((volume : Measure (Eucl k)).restrict Ω) →
        (∀ w ∈ Ω, |F w| ≤ c * |dφ q w|) → IntegrableOn F Ω (volume : Measure (Eucl k)) := by
      intro F c hFm hFb
      refine Integrable.mono' ((hdφint.abs.const_mul c).integrableOn) hFm ?_
      exact (ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun w hw => by
        simpa [Real.norm_eq_abs] using hFb w hw)
    -- η_q and the induction hypothesis
    let ηq : Eucl k → ℝ := fun w => p v₀ w * dφ q w
    obtain ⟨P0, hP00, hP0⟩ := hpbd v₀ hv₀
    have hηq : IntegrableOn ηq Ω (volume : Measure (Eucl k)) := by
      refine hint ηq P0 ((hpm v₀ hv₀).mul hdφc.aestronglyMeasurable.restrict) fun w hw => ?_
      by_cases hwK : w ∈ K
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hP0 w hwK) (abs_nonneg _)
      · simp [ηq, hdφ0 w hwK]
    have hih := ih (fun t => a t.succ) (fun s => b (q.succAbove s)) ηq hηq
    -- integrability of the pieces
    have hI1 : ∀ j, IntegrableOn (fun w => (p (v j) w - p v₀ w) * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w)
        Ω (volume : Measure (Eucl k)) := by
      intro j
      obtain ⟨Pj, hPj0, hPj⟩ := hpbd (v j) (hv j)
      refine hint _ ((Pj + P0) * B') ((((hpm _ (hv j)).sub (hpm _ hv₀)).mul
        ((hM'm _ (hv j)).aestronglyMeasurable.const_mul _)).mul hdφc.aestronglyMeasurable.restrict) ?_
      intro w hw
      by_cases hwK : w ∈ K
      · rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        gcongr
        · exact (abs_sub _ _).trans (add_le_add (hPj w hwK) (hP0 w hwK))
        · exact hM'b _ (hv j) w hw
      · simp [hdφ0 w hwK]
    have hI2 : ∀ u, LipschitzOnWith C u Ω → IntegrableOn (fun w => ηq w * M' q u w) Ω (volume : Measure (Eucl k)) := by
      intro u hu
      refine hint _ (P0 * B') ((hpm v₀ hv₀).mul hdφc.aestronglyMeasurable.restrict
        |>.mul (hM'm _ hu).aestronglyMeasurable) ?_
      intro w hw
      by_cases hwK : w ∈ K
      · simp only [ηq, abs_mul]
        calc |p v₀ w| * |dφ q w| * |M' q u w| ≤ P0 * |dφ q w| * B' := by
              gcongr
              · exact hP0 w hwK
              · exact hM'b _ hu w hw
          _ = P0 * B' * |dφ q w| := by ring
      · simp [ηq, hdφ0 w hwK]
    -- algebraic splitting
    have hsplit : ∀ j, ∫ w in Ω, p (v j) w * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w ∂(volume : Measure (Eucl k)) =
        (∫ w in Ω, (p (v j) w - p v₀ w) * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w ∂(volume : Measure (Eucl k))) +
          (-1 : ℝ) ^ (q : ℕ) * ∫ w in Ω, ηq w * M' q (v j) w ∂(volume : Measure (Eucl k)) := by
      intro j
      rw [← integral_const_mul, ← integral_add (hI1 j) ((hI2 _ (hv j)).const_mul _)]
      congr 1; funext w; simp only [ηq]; ring
    have hlim : ∫ w in Ω, p v₀ w * ((-1 : ℝ) ^ (q : ℕ) * M' q v₀ w) * dφ q w ∂(volume : Measure (Eucl k)) =
        0 + (-1 : ℝ) ^ (q : ℕ) * ∫ w in Ω, ηq w * M' q v₀ w ∂(volume : Measure (Eucl k)) := by
      rw [zero_add, ← integral_const_mul]
      congr 1; funext w; simp only [ηq]; ring
    -- first piece tends to zero by uniform convergence
    have h1 : Tendsto (fun j => ∫ w in Ω, (p (v j) w - p v₀ w) * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w
        ∂(volume : Measure (Eucl k))) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      set I := ∫ w, |dφ q w| ∂(volume : Measure (Eucl k)) with hI
      have hI0 : 0 ≤ I := integral_nonneg fun w => abs_nonneg _
      set δ := ε / (2 * (B' * I + 1)) with hδ
      have hδ0 : 0 < δ := by positivity
      obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hconv δ hδ0)
      refine ⟨N, fun j hj => ?_⟩
      rw [dist_zero_right]
      have hbound : ∀ᵐ w ∂((volume : Measure (Eucl k)).restrict Ω),
          ‖(p (v j) w - p v₀ w) * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w‖ ≤ δ * B' * |dφ q w| := by
        refine (ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun w hw => ?_)
        have e1 : |p (v j) w - p v₀ w| ≤ δ := by
          have h' := (hN j hj w hw).le
          rw [dist_comm, dist_eq_norm] at h'
          calc |p (v j) w - p v₀ w| = |EuclideanSpace.proj (a 0) (v j w - v₀ w)| := by simp [p]
            _ = ‖(v j w - v₀ w) (a 0)‖ := by simp [Real.norm_eq_abs]
            _ ≤ ‖v j w - v₀ w‖ := PiLp.norm_apply_le _ _
            _ ≤ δ := h'
        have e2 := hM'b _ (hv j) w hw
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        gcongr
      calc ‖∫ w in Ω, (p (v j) w - p v₀ w) * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w ∂(volume : Measure (Eucl k))‖
          ≤ ∫ w in Ω, δ * B' * |dφ q w| ∂(volume : Measure (Eucl k)) :=
            norm_integral_le_of_norm_le ((hdφint.abs.const_mul _).integrableOn) hbound
        _ ≤ ∫ w, δ * B' * |dφ q w| ∂(volume : Measure (Eucl k)) :=
            setIntegral_le_integral (hdφint.abs.const_mul _) (ae_of_all _ fun w => by positivity)
        _ = δ * (B' * I) := by rw [integral_const_mul, hI]; ring
        _ < ε := by
            rw [hδ]
            have : 0 < B' * I + 1 := by positivity
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith
    rw [hlim]
    exact (h1.add (hih.const_mul _)).congr fun j => (hsplit j).symm

## Key steps

1. Rademacher-type bound ‖Du‖ ≤ C on Ω gives |M_{a,b}(u)| ≤ r!C^r on Ω; minors are Borel measurable.
2. Induction on r; r = 0 is trivial (empty determinant 1).
3. Step r → r+1: by test_density (bound (r+1)!C^{r+1}) it suffices to test against φ ∈ C¹_c(Ω).
4. minor_ibp_lipschitz rewrites ∫_Ω φM_{a,b}(u) = −Σ_q ∫_Ω u^{a(0)}(−1)^q M_{a′,b^{(q)}}(u)∂_{b(q)}φ for u = v_j, v₀.
5. Split each term: uniform convergence handles (v_j^{a(0)} − v₀^{a(0)}); the induction hypothesis for the (r×r) minors tested against η_q = v₀^{a(0)}∂_{b(q)}φ ∈ L¹(Ω) handles the rest.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886 = git HEAD; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (both byte-identical)`
- `python3 -I over dag.json: this node (depth 3, status decomposing, attempt 1, depends_on root.compactness_mass_bounds-a1.covector_expansion-a1) and the parent's decomposition-v3.json (format of reused children)`
- `python3 -I regex over dag.json titles/statements/lean statements: mollif|Piola|dense in|density of|C_c|integration by parts|weak-*|weak star|cofactor|convolution|minors|smooth approximation|ContDiffBump`
- `python3 -I over dag.json: status, candidate_commit, title/statement/lean_statement equality with the handoff for constancy_mdc_smooth_approx_identity_ae_tendsto, slicing_mb_sa_mollify_lipschitz_hasFDerivAt, slicing_mb_sa_mollify_lipschitz_close, cmb_covector_eq_sum_coord_smul_wedge (all accepted, equal); lean_name collisions for deformation_ipl_mwc_* (none)`
- `grep -rn deformation_ipl_mwc over GMT/, the snapshot project, simongmt/Poincare and the snapshot Mathlib (no match)`
- `rg -n 'abbrev Covector|SimonMultiIndex|def wedgeCovectors|theorem wedgeCovectors_apply_det|def euclideanCovectorCoordinate' simongmt/Poincare/SimonGMT`
- `rg -n 'theorem norm_fderiv_le_of_lipschitzOn|LipschitzOnWith.extend_real|extend_finite_dimension|lipschitzExtensionConstant' snapshot Mathlib`
- `rg -n '^theorem' Mathlib/Analysis/Calculus/Rademacher.lean and Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean; sed ContinuousMapDense.lean 135-240, LineDeriv/IntegrationByParts.lean 215-245, ContDiff/Convolution.lean 50-100 and 415-435, Matrix/AbsoluteValue.lean det_le, ContDiff/RCLike.lean lipschitzWith_of_hasCompactSupport, FDeriv/Mul.lean finsetProd`
- `git log --all -G'^import' -- GMT/Ch06/Submission.lean; git show cdfc95dc (leaf gate rejects added imports); git show 2219dd32 (accepted ae-mollifier proof uses IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub)`
- `lake env lean /tmp/mwc_decomp/build/Avail.lean, build_v2/Avail2.lean, build_v2/Avail3.lean, build_v2/Small2.lean (#check availability under import GMT.Ch06.Submission)`
- `python3 -I /tmp/mwc_decomp/gen.py (verifier lean_contract.validate_lean_statement + gmt-compare child_modules, contract mode) and lake env lean on the eleven /tmp/mwc_decomp/build_final/*_challenge.lean (all exit 0, sorry warnings only)`
- `lake env lean /tmp/mwc_decomp/build/Assembly.lean, build_v2/F_from_E.lean, build_v2/E_from_AD.lean, build_v2/RefImpl.lean (#print axioms: propext, Classical.choice, Quot.sound)`
- `grep 'Your solution is okay' in comparator-v1.log and isolated-comparator-result.json (passed: true) of the four reused nodes`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/speculative-prompt-v4.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-covector-expansion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1-smooth-appro-6a720fda87/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1-smooth-appro-6a720fda87/comparator-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollify-fderiv-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollify-close-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/mwc_decomp/build_final`
- `/tmp/mwc_decomp/build/Assembly.lean`
- `/tmp/mwc_decomp/build_v2/F_from_E.lean`
- `/tmp/mwc_decomp/build_v2/E_from_AD.lean`
- `/tmp/mwc_decomp/build_v2/RefImpl.lean`
- `/tmp/mwc_decomp/build/Avail.lean`
- `/tmp/mwc_decomp/build_v2/Avail2.lean`
- `/tmp/mwc_decomp/build_v2/Avail3.lean`

Pinned revisions are confirmed (HEAD = project_commit), and Contract = Submission = the snapshot Contract byte-for-byte.
No existing proof: neither Mathlib, SimonGMT nor any accepted DAG node proves weak continuity of Jacobian minors, the Piola identity or L¹-density by smooth functions. (The r = 1 analogue slicing_im_ll_gradient_weak_star and the density node slicing_im_ll_gws_smooth_dense are not accepted.) Hence seven new children; their names deformation_ipl_mwc_* collide with nothing.
Reused, with byte-identical types and comparator-passed: cmb_covector_eq_sum_coord_smul_wedge, constancy_mdc_smooth_approx_identity_ae_tendsto, slicing_mb_sa_mollify_lipschitz_hasFDerivAt, slicing_mb_sa_mollify_lipschitz_close.
Import closure: the leaf gate forbids new imports (commit cdfc95dc).
- Available in the frozen closure: SimonGMT wedgeCovectors_apply_det; Mathlib norm_fderiv_le_of_lipschitzOn, LipschitzOnWith.extend_real, extend_finite_dimension, LipschitzOnWith.ae_differentiableWithinAt_of_mem, LipschitzWith.integral_lineDeriv_mul_eq, HasCompactSupport.contDiff_convolution_left/right, ContDiffAt.isSymmSndFDerivAt, HasFDerivAt.finsetProd, Matrix.det_succ_row_zero, Matrix.det_apply, measurable_fderiv(_apply_const), tendsto_integral_filter_of_dominated_convergence, IsCompact.exists_cthickening_subset_open, ContDiff.lipschitzWith_of_hasCompactSupport.
- Not available: ContDiffBump.normed and BumpFunction/Convolution, ContinuousMapDense, LineDeriv/IntegrationByParts, Matrix.det_le. The children replace them by the reused siblings or by short arguments.
Lean checks:
- All eleven statements validate and elaborate in the exact comparator scope.
- Three links compile with only propext, Classical.choice and Quot.sound: parent ⇐ coeff_minor_continuity + covector expansion; coeff_minor_continuity ⇐ minor_weak_star; minor_weak_star ⇐ test_density + minor_ibp_lipschitz.
