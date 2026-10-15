# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_height-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_height-a1.energy_inequality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Sibling map (dependency key — frozen Lean declaration — label): projection_trace — Submission.dorag_th_trace_proj_comp_compl — (B); hs_operator_bound — Submission.dorag_th_norm_apply_sq_le_hs — (C); test_field_divergence — Submission.dorag_th_trace_comp_fderiv_test_field — (D).
Source: parent proof steps 2–4 together with its preliminaries (P1)–(P4), for an arbitrary cut-off ζ (Simon, proof of Ch. 5, Lemma 2.1, displays (1)–(3) and "Hence ∫ζ²|…|² ≤ 4∫(|x′|²|∇ζ|² + |x′||H|ζ²)", book/chapter-05.txt, lines 222–259; the constants 16 and 4 come from the parent's Young inequality 2ab ≤ ¼a² + 4b²).
Notation: M := R.carrier, θ := R.mult, μ := R.measure = (Hⁿ⌞M).withDensity θ, T_x := approxTangentPlane n M x with orthogonal projection p_x, p_S the orthogonal projection onto S, q := I − p_S, w(x) := q(x − ξ) = (x − ξ) − p_S(x − ξ), b(x) := |w(x)|, a(x) := Σ_i |p_x e_i − p_S e_i|², K := tsupport ζ.

1. κ ≥ 0, since 0 ≤ |H(0)| ≤ κ.
2. μ(K) < ∞. K is compact (ζ has compact support), closed hence Borel, and K ⊆ W ⊆ U. By the definitions of withDensity and of the restricted measure, μ(K) = ∫_{M∩K} θ dHⁿ, which is finite by the field R.locallyIntegrable_mult applied to the compact set K ⊆ U.
3. Integrability criterion. If f : ℝ^P → ℝ is μ-a.e. strongly measurable, |f| ≤ C on ℝ^P and f = 0 outside K, then |f| ≤ C·1_K, and C·1_K is μ-integrable by step 2; hence f is μ-integrable.
4. Elementary bounds. (i) ζ is continuous with compact support, so |ζ| ≤ Z for some Z ≥ 0, and ζ = 0 outside K. (ii) Dζ = fderiv ℝ ζ is continuous (ζ is C¹) and vanishes outside K (a function vanishing on a neighbourhood of a point has zero derivative there, and every point outside tsupport ζ has such a neighbourhood), so ‖Dζ‖ ≤ D′ for some D′ ≥ 0. (iii) w is continuous (affine), so b ≤ B on the compact set K for some B ≥ 0. (iv) 0 ≤ a ≤ 4P everywhere: orthogonal projections have operator norm ≤ 1 and |e_i| = 1, so |p_x e_i − p_S e_i| ≤ |p_x e_i| + |p_S e_i| ≤ 2.
5. Measurability. As x ↦ p_x is μ-a.e. strongly measurable (hypothesis), so is x ↦ p_x e_i (evaluation at a fixed vector is a continuous linear function of the operator), hence a (continuous operations and a finite sum), and so is x ↦ p_x w(x) (the evaluation (A, v) ↦ Av is jointly continuous and w is continuous). ζ, Dζ and w are continuous, and H is μ-a.e. strongly measurable, so x ↦ ⟨X(x), H(x)⟩ is μ-a.e. strongly measurable for every continuous X (the inner product is continuous).
6. The functions. Let F₁ := ζ²a, F₂ := 2ζ·Dζ[p_x w], X := ζ²w, F₃ := ⟨X, H⟩, G₁ := ‖Dζ‖²b², G₂ := κζ²b. By steps 4–5 each is μ-a.e. strongly measurable and bounded on ℝ^P (|F₁| ≤ 4PZ², |F₂| ≤ 2ZD′B, |F₃| ≤ Z²Bκ, G₁ ≤ D′²B², G₂ ≤ κZ²B, using |p_x w(x)| ≤ |w(x)| ≤ B on K), and each vanishes outside K because it contains the factor ζ or Dζ. By step 3 all six are μ-integrable.
7. The test field. X is C¹ (ζ² is C¹ and w is affine), and {X ≠ 0} ⊆ {ζ ≠ 0}, so tsupport X ⊆ K ⊆ W and X has compact support. By the first-variation hypothesis, R.firstVariation X = −∫F₃ dμ.
8. First variation as a μ-integral. By definition R.firstVariation X = ∫_M θ·div_M X dHⁿ with div_M X(x) = tangentialDivergence n M X x = trace(p_x∘DX(x)). Since μ = (Hⁿ⌞M).withDensity θ with θ measurable and ℕ-valued (hence ℝ≥0-valued), ∫ g dμ = ∫_M θ·g dHⁿ for every real function g, with no integrability assumption (Mathlib: integral_withDensity_eq_integral_smul). Hence R.firstVariation X = ∫ div_M X dμ.
9. Almost every approximate tangent plane is n-dimensional. By the field R.orients, for Hⁿ⌞M-a.e. x there is Q with HasApproximateTangentSpaceAt n M x Q. At such x, the definition of approxTangentPlane selects some Q′ with HasApproximateTangentSpaceAt n M x Q′, and the first conjunct of that predicate is dim Q′ = n. Since μ ≪ Hⁿ⌞M (a measure with density is absolutely continuous), dim T_x = n for μ-a.e. x.
10. Pointwise divergence. For every x, ζ is differentiable at x, so (D) with T = T_x gives div_M X(x) = ζ(x)²·trace(p_x∘(I − p_S)) + F₂(x). For μ-a.e. x, dim T_x = n = dim S by step 9, so (B) gives trace(p_x∘(I − p_S)) = ½a(x). Hence div_M X = ½F₁ + F₂ μ-a.e.
11. The identity. By steps 6, 8, 10 and 7 and linearity of the integral on integrable functions: ½∫F₁ dμ + ∫F₂ dμ = ∫(½F₁ + F₂) dμ = ∫div_M X dμ = R.firstVariation X = −∫F₃ dμ.
12. Cross term. Fix x and put L := Dζ(x). Since w(x) = v − p_S v with v := x − ξ lies in S^⊥, p_S w(x) = 0, hence p_x w(x) = (p_x − p_S)w(x). By (C) with A := p_x − p_S (note (p_x − p_S)e_i = p_x e_i − p_S e_i): |(p_x − p_S)w(x)|² ≤ a(x)·b(x)², so |L[p_x w(x)]| ≤ ‖L‖·√a(x)·b(x). Therefore −F₂(x) ≤ 2|ζ(x)|·|L[p_x w(x)]| ≤ 2(|ζ(x)|√a(x))(‖L‖b(x)) ≤ ¼ζ(x)²a(x) + 4‖L‖²b(x)² = ¼F₁(x) + 4G₁(x), by 2αβ ≤ ¼α² + 4β² ⇔ (α/2 − 2β)² ≥ 0.
13. Curvature term. −F₃(x) ≤ |⟨X(x), H(x)⟩| ≤ |X(x)|·|H(x)| = ζ(x)²b(x)|H(x)| ≤ κζ(x)²b(x) = G₂(x).
14. Absorption. Integrating steps 12 and 13 (monotonicity of the integral for integrable functions): −∫F₂ ≤ ¼∫F₁ + 4∫G₁ and −∫F₃ ≤ ∫G₂. With step 11, ½∫F₁ = −∫F₂ − ∫F₃ ≤ ¼∫F₁ + 4∫G₁ + ∫G₂. As ∫F₁ is a finite real number, ¼∫F₁ ≤ 4∫G₁ + ∫G₂, i.e. ∫F₁ ≤ 16∫G₁ + 4∫G₂.
15. Lower integrals. F₁, G₁, G₂ are nonnegative (κ ≥ 0 by step 1) and integrable, so ∫⁻ ofReal(F₁) dμ = ofReal(∫F₁ dμ), and likewise for G₁ and G₂ (Mathlib: ofReal_integral_eq_lintegral_ofReal). Since ∫G₁, ∫G₂ ≥ 0 and ofReal is monotone, additive and multiplicative on nonnegative reals: ∫⁻ ofReal(F₁) = ofReal(∫F₁) ≤ ofReal(16∫G₁ + 4∫G₂) = ofReal(16)·ofReal(∫G₁) + ofReal(4)·ofReal(∫G₂) = ofReal(16)·∫⁻ ofReal(G₁) + ofReal(4)·∫⁻ ofReal(G₂). As F₁ = ζ²|p_x − p_S|², G₁ = ‖Dζ‖²|w|² and G₂ = κζ²|w|, this is the assertion. ∎

Appendix — machine-checked Lean realization (verified during decomposition: Lean v4.35.0-rc3, Mathlib 25730c7c, inside `namespace GMT.Ch07` of the frozen Submission scope; `#print axioms` gives [propext, Classical.choice, Quot.sound]; the numbered argument above is the proof, this block only records one verified formalization of it):
```lean
theorem Submission.dorag_th_tilt_energy_inequality : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ) (S : Submodule ℝ (Euclid P)) (ξ : Euclid P) (ζ : Euclid P → ℝ), W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → Module.finrank ℝ S = n → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ W → ∫⁻ x, ENNReal.ofReal (ζ x ^ 2 * ∑ i : Fin P, ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal 16 * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ ζ x‖ ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂R.measure + ENNReal.ofReal 4 * ∫⁻ x, ENNReal.ofReal (κ * ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖) ∂R.measure := by
  intro P n U W R H κ S ξ ζ hWU hpM hH hHκ hMC hS hζC hζcpt hζW
  -- (3) δV(X) = ∫ div_M X dμ for every X (μ = (Hⁿ⌞M).withDensity θ)
  have hFV : ∀ X : Euclid P → Euclid P,
      R.firstVariation X = ∫ x, tangentialDivergence n R.carrier X x ∂R.measure := by
    intro X
    have hm : Measurable (fun x => ((R.mult x : NNReal))) :=
      (measurable_from_nat (f := fun m : ℕ => (m : NNReal))).comp R.measurable_mult
    have h := integral_withDensity_eq_integral_smul hm (fun x => tangentialDivergence n R.carrier X x)
      (μ := μHE[n].restrict R.carrier)
    simp only [ENNReal.coe_natCast] at h
    rw [IMRep.measure, h, IMRep.firstVariation]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [NNReal.smul_def])
  -- (4) dim TₓM = n for μ-a.e. x
  have hfin : ∀ᵐ x ∂R.measure, Module.finrank ℝ (approxTangentPlane n R.carrier x) = n := by
    have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
    filter_upwards [hac.ae_le R.orients] with x hx
    obtain ⟨Q, hQ, -⟩ := hx
    have hex : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    rw [approxTangentPlane, dite_eq_left_of_eq_true (eq_true hex)]
    exact hex.choose_spec.1
  -- (5) cross-term bound: |L(p_T(v - p_S v))| ≤ ‖L‖ √|p_T - p_S|² ‖v - p_S v‖
  have hcross : ∀ (T : Submodule ℝ (Euclid P)) (L : Euclid P →L[ℝ] ℝ) (v : Euclid P),
      |L (T.starProjection (v - S.starProjection v))| ≤
        ‖L‖ * (Real.sqrt (∑ i : Fin P, ‖T.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖v - S.starProjection v‖) := by
    intro T L v
    set w := v - S.starProjection v
    have hw : S.starProjection w = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff S).mpr (Submodule.sub_starProjection_mem_orthogonal v)
    have heq : T.starProjection w = (T.starProjection - S.starProjection) w := by
      simp [hw]
    have hsq := Submission.dorag_th_norm_apply_sq_le_hs P (T.starProjection - S.starProjection) w
    simp only [sub_apply] at hsq
    have hn : ‖(T.starProjection - S.starProjection) w‖ ≤
        Real.sqrt (∑ i : Fin P, ‖T.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖w‖ := by
      rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg w), ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by simpa [sub_apply] using hsq)
    rw [heq]
    calc |L ((T.starProjection - S.starProjection) w)| ≤ ‖L‖ * ‖(T.starProjection - S.starProjection) w‖ := by
          rw [← Real.norm_eq_abs]; exact L.le_opNorm _
      _ ≤ _ := by gcongr
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  have hKm : MeasurableSet (tsupport ζ) := (isClosed_tsupport ζ).measurableSet
  -- (1) the compact set K = tsupport ζ ⊆ U has finite μ-measure
  have hμK : R.measure (tsupport ζ) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm, Set.inter_comm]
    exact R.locallyIntegrable_mult _ hζcpt (hζW.trans hWU)
  -- integrability of bounded a.e.-strongly measurable functions vanishing off K
  have hint : ∀ f : Euclid P → ℝ, AEStronglyMeasurable f R.measure → (∃ M, ∀ x, |f x| ≤ M) →
      (∀ x, x ∉ tsupport ζ → f x = 0) → Integrable f R.measure := by
    rintro f hf ⟨M, hM⟩ h0
    have hg : Integrable ((tsupport ζ).indicator (fun _ => M)) R.measure :=
      (integrableOn_const hμK).integrable_indicator hKm
    refine hg.mono' hf (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport ζ
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]; exact hM x
    · rw [Set.indicator_of_notMem hx, h0 x hx, norm_zero]
  have hζ_cont : Continuous ζ := hζC.continuous
  have hDζ_cont : Continuous (fderiv ℝ ζ) := hζC.continuous_fderiv one_ne_zero
  have hζ0 : ∀ x, x ∉ tsupport ζ → ζ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hDζ0 : ∀ x, x ∉ tsupport ζ → fderiv ℝ ζ x = 0 := fun x hx => fderiv_of_notMem_tsupport ℝ hx
  have hw_cont : Continuous (fun y : Euclid P => (y - ξ) - S.starProjection (y - ξ)) := by fun_prop
  obtain ⟨Z, hZ⟩ := hζ_cont.bounded_above_of_compact_support hζcpt
  obtain ⟨D', hD'⟩ := hDζ_cont.bounded_above_of_compact_support (hζcpt.fderiv (𝕜 := ℝ))
  obtain ⟨Wb1, hWb1⟩ := IsCompact.exists_bound_of_continuousOn hζcpt hw_cont.continuousOn
  set Wb := max Wb1 0 with hWb_def
  have hWb : ∀ x ∈ tsupport ζ, ‖(x - ξ) - S.starProjection (x - ξ)‖ ≤ Wb :=
    fun x hx => (hWb1 x hx).trans (le_max_left _ _)
  have hWb0 : 0 ≤ Wb := le_max_right _ _
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ ξ)
  have hD'0 : 0 ≤ D' := (norm_nonneg _).trans (hD' ξ)
  -- the tilt density a(x) = |p_x - p_S|²
  set a : Euclid P → ℝ := fun x => ∑ i : Fin P, ‖(approxTangentPlane n R.carrier x).starProjection
      (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
    with ha_def
  have ha0 : ∀ x, 0 ≤ a x := fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have ha_le : ∀ x, a x ≤ 4 * P := by
    intro x
    have : ∀ i : Fin P, ‖(approxTangentPlane n R.carrier x).starProjection
        (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤ 4 := by
      intro i
      have h1 := (approxTangentPlane n R.carrier x).norm_starProjection_apply_le
        (EuclideanSpace.single i (1 : ℝ))
      have h2 := S.norm_starProjection_apply_le (EuclideanSpace.single i (1 : ℝ))
      have h3 := norm_sub_le ((approxTangentPlane n R.carrier x).starProjection
        (EuclideanSpace.single i (1 : ℝ))) (S.starProjection (EuclideanSpace.single i (1 : ℝ)))
      simp only [EuclideanSpace.norm_single, norm_one] at h1 h2
      nlinarith [norm_nonneg ((approxTangentPlane n R.carrier x).starProjection
        (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ)))]
    calc a x ≤ ∑ _i : Fin P, (4 : ℝ) := Finset.sum_le_sum fun i _ => this i
      _ = 4 * P := by simp [mul_comm]
  have ha_meas : AEStronglyMeasurable a R.measure := by
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
    exact (((hpM.apply_continuousLinearMap _).sub aestronglyMeasurable_const).norm).pow 2
  have hpw_meas : AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection
      ((x - ξ) - S.starProjection (x - ξ))) R.measure :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (A : Euclid P →L[ℝ] Euclid P) (v : Euclid P) => A v)
      (by fun_prop) hpM hw_cont.aestronglyMeasurable
  -- the five functions
  set F1 : Euclid P → ℝ := fun x => ζ x ^ 2 * a x with hF1
  set F2 : Euclid P → ℝ := fun x => 2 * ζ x * fderiv ℝ ζ x ((approxTangentPlane n R.carrier x).starProjection
      ((x - ξ) - S.starProjection (x - ξ))) with hF2
  set X : Euclid P → Euclid P := fun y => ζ y ^ 2 • ((y - ξ) - S.starProjection (y - ξ)) with hX
  set F3 : Euclid P → ℝ := fun x => inner ℝ (X x) (H x) with hF3
  set G1 : Euclid P → ℝ := fun x => ‖fderiv ℝ ζ x‖ ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2 with hG1
  set G2 : Euclid P → ℝ := fun x => κ * ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ with hG2
  have hX_cont : Continuous X := by fun_prop
  -- integrability
  have hF1i : Integrable F1 R.measure := by
    refine hint F1 ((hζ_cont.aestronglyMeasurable.pow 2).mul ha_meas) ⟨Z ^ 2 * (4 * P), fun x => ?_⟩
      (fun x hx => by simp [F1, hζ0 x hx])
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (ha0 x))]
    have : ζ x ^ 2 ≤ Z ^ 2 := by
      have := hZ x; rw [Real.norm_eq_abs] at this
      nlinarith [abs_nonneg (ζ x), sq_abs (ζ x)]
    exact mul_le_mul this (ha_le x) (ha0 x) (sq_nonneg _)
  have hF2i : Integrable F2 R.measure := by
    refine hint F2 ?_ ⟨2 * Z * (D' * Wb), fun x => ?_⟩ (fun x hx => by simp [F2, hζ0 x hx])
    · exact (aestronglyMeasurable_const.mul hζ_cont.aestronglyMeasurable).mul
        (Continuous.comp_aestronglyMeasurable₂ (g := fun (L : Euclid P →L[ℝ] ℝ) (v : Euclid P) => L v)
          (by fun_prop) hDζ_cont.aestronglyMeasurable hpw_meas)
    · by_cases hx : x ∈ tsupport ζ
      · have h1 : |ζ x| ≤ Z := by simpa [Real.norm_eq_abs] using hZ x
        have h2 : |fderiv ℝ ζ x ((approxTangentPlane n R.carrier x).starProjection
            ((x - ξ) - S.starProjection (x - ξ)))| ≤ D' * Wb := by
          rw [← Real.norm_eq_abs]
          calc _ ≤ ‖fderiv ℝ ζ x‖ * ‖(approxTangentPlane n R.carrier x).starProjection
                ((x - ξ) - S.starProjection (x - ξ))‖ := (fderiv ℝ ζ x).le_opNorm _
            _ ≤ D' * Wb := by
              apply mul_le_mul (hD' x) _ (norm_nonneg _) hD'0
              exact ((approxTangentPlane n R.carrier x).norm_starProjection_apply_le _).trans (hWb x hx)
        simp only [F2, abs_mul, abs_two]
        have := mul_le_mul h1 h2 (abs_nonneg _) hZ0
        nlinarith [abs_nonneg (ζ x)]
      · simp only [F2, hζ0 x hx, mul_zero, zero_mul, abs_zero]
        positivity
  have hζsq : ∀ x, ζ x ^ 2 ≤ Z ^ 2 := by
    intro x
    have := hZ x; rw [Real.norm_eq_abs] at this
    nlinarith [abs_nonneg (ζ x), sq_abs (ζ x)]
  have hF3i : Integrable F3 R.measure := by
    refine hint F3 (Continuous.comp_aestronglyMeasurable₂ (g := fun (u v : Euclid P) => (inner ℝ u v : ℝ))
      continuous_inner hX_cont.aestronglyMeasurable hH) ⟨Z ^ 2 * Wb * κ, fun x => ?_⟩
      (fun x hx => by simp [F3, X, hζ0 x hx])
    by_cases hx : x ∈ tsupport ζ
    · calc |F3 x| ≤ ‖X x‖ * ‖H x‖ := abs_real_inner_le_norm _ _
        _ ≤ (Z ^ 2 * Wb) * κ := by
          apply mul_le_mul _ (hHκ x) (norm_nonneg _) (by positivity)
          simp only [X, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (ζ x))]
          exact mul_le_mul (hζsq x) (hWb x hx) (norm_nonneg _) (sq_nonneg _)
    · simp only [F3, X, hζ0 x hx]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul, inner_zero_left,
        abs_zero]
      positivity
  have hG1i : Integrable G1 R.measure := by
    refine hint G1 ((hDζ_cont.norm.pow 2).mul (hw_cont.norm.pow 2)).aestronglyMeasurable
      ⟨D' ^ 2 * Wb ^ 2, fun x => ?_⟩ (fun x hx => by simp [G1, hDζ0 x hx])
    by_cases hx : x ∈ tsupport ζ
    · rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hD' x) 2)
        (pow_le_pow_left₀ (norm_nonneg _) (hWb x hx) 2) (sq_nonneg _) (sq_nonneg _)
    · simp only [G1, hDζ0 x hx, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, abs_zero]
      positivity
  have hG2i : Integrable G2 R.measure := by
    refine hint G2 ((continuous_const.mul (hζ_cont.pow 2)).mul hw_cont.norm).aestronglyMeasurable
      ⟨κ * Z ^ 2 * Wb, fun x => ?_⟩ (fun x hx => by simp [G2, hζ0 x hx])
    by_cases hx : x ∈ tsupport ζ
    · rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hζsq x) hκ) (hWb x hx) (norm_nonneg _)
        (by positivity)
    · simp only [G2, hζ0 x hx]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul, abs_zero]
      positivity
  -- (2) the test field X = ζ² (x - ξ - p_S (x - ξ))
  have hXC : ContDiff ℝ 1 X :=
    (hζC.pow 2).smul ((contDiff_id.sub contDiff_const).sub
      (S.starProjection.contDiff.comp (contDiff_id.sub contDiff_const)))
  have hXsupp : tsupport X ⊆ tsupport ζ := by
    apply closure_mono
    intro y hy
    by_contra h
    apply hy
    simp only [Function.mem_support, not_not] at h
    simp [X, h]
  have hXcpt : HasCompactSupport X := hζcpt.mono' ((subset_tsupport X).trans hXsupp)
  have hMCX := hMC X hXC hXcpt (hXsupp.trans hζW)
  -- (3) first variation as an integral of the divergence, (4)-(5) a.e. divergence formula
  rw [hFV] at hMCX
  have hdiv : (fun x => tangentialDivergence n R.carrier X x) =ᵐ[R.measure]
      (fun x => 1 / 2 * F1 x + F2 x) := by
    filter_upwards [hfin] with x hx
    have hd := Submission.dorag_th_trace_comp_fderiv_test_field P (approxTangentPlane n R.carrier x) S ζ ξ x ((hζC.differentiable one_ne_zero) x)
    rw [tangentialDivergence, hd, Submission.dorag_th_trace_proj_comp_compl P _ S (by rw [hx, hS])]
    simp only [F1, F2, a]
    ring
  have hid : 1 / 2 * ∫ x, F1 x ∂R.measure + ∫ x, F2 x ∂R.measure = -∫ x, F3 x ∂R.measure := by
    rw [← integral_const_mul, ← integral_add (hF1i.const_mul _) hF2i, ← integral_congr_ae hdiv]
    exact hMCX
  -- (6) pointwise bounds
  have hb1 : ∀ x, -F2 x ≤ 1 / 4 * F1 x + 4 * G1 x := by
    intro x
    have ht := hcross (approxTangentPlane n R.carrier x) (fderiv ℝ ζ x) (x - ξ)
    set t := fderiv ℝ ζ x ((approxTangentPlane n R.carrier x).starProjection
      ((x - ξ) - S.starProjection (x - ξ)))
    set c := ‖fderiv ℝ ζ x‖
    set s := Real.sqrt (a x)
    set β := ‖(x - ξ) - S.starProjection (x - ξ)‖
    have hs : s ^ 2 = a x := Real.sq_sqrt (ha0 x)
    have hc0 : 0 ≤ c := norm_nonneg _
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hβ0 : 0 ≤ β := norm_nonneg _
    have h1 : -(2 * ζ x * t) ≤ 2 * |ζ x| * |t| := by
      have := neg_le_abs (2 * ζ x * t)
      rwa [abs_mul, abs_mul, abs_two] at this
    have h2 : 2 * |ζ x| * |t| ≤ 2 * |ζ x| * (c * (s * β)) := by gcongr
    have h3 : 2 * |ζ x| * (c * (s * β)) ≤ 1 / 4 * (ζ x ^ 2 * s ^ 2) + 4 * (c ^ 2 * β ^ 2) := by
      nlinarith [sq_nonneg (|ζ x| * s - 4 * c * β), sq_abs (ζ x), abs_nonneg (ζ x)]
    simp only [F1, F2, G1]
    rw [← hs]
    linarith
  have hb2 : ∀ x, -F3 x ≤ G2 x := by
    intro x
    calc -F3 x ≤ |F3 x| := neg_le_abs _
      _ ≤ ‖X x‖ * ‖H x‖ := abs_real_inner_le_norm _ _
      _ = ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ * ‖H x‖ := by
          simp only [X, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (ζ x))]
      _ ≤ ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ * κ := by
          gcongr
          exact hHκ x
      _ = G2 x := by simp only [G2]; ring
  -- (7) integrate and absorb
  have i1 : ∫ x, -F2 x ∂R.measure ≤ ∫ x, (1 / 4 * F1 x + 4 * G1 x) ∂R.measure :=
    integral_mono hF2i.neg ((hF1i.const_mul _).add (hG1i.const_mul _)) hb1
  have i2 : ∫ x, -F3 x ∂R.measure ≤ ∫ x, G2 x ∂R.measure := integral_mono hF3i.neg hG2i hb2
  rw [integral_neg] at i1 i2
  rw [integral_add (hF1i.const_mul _) (hG1i.const_mul _), integral_const_mul, integral_const_mul] at i1
  have hfin : ∫ x, F1 x ∂R.measure ≤ 16 * ∫ x, G1 x ∂R.measure + 4 * ∫ x, G2 x ∂R.measure := by
    linarith
  -- (8) convert to lower Lebesgue integrals
  have hF1n : ∀ x, 0 ≤ F1 x := fun x => mul_nonneg (sq_nonneg _) (ha0 x)
  have hG1n : ∀ x, 0 ≤ G1 x := fun x => by positivity
  have hG2n : ∀ x, 0 ≤ G2 x := fun x => by positivity
  have l1 := ofReal_integral_eq_lintegral_ofReal hF1i (Filter.Eventually.of_forall hF1n)
  have l2 := ofReal_integral_eq_lintegral_ofReal hG1i (Filter.Eventually.of_forall hG1n)
  have l3 := ofReal_integral_eq_lintegral_ofReal hG2i (Filter.Eventually.of_forall hG2n)
  have hI1 : 0 ≤ ∫ x, G1 x ∂R.measure := integral_nonneg hG1n
  have hI2 : 0 ≤ ∫ x, G2 x ∂R.measure := integral_nonneg hG2n
  calc ∫⁻ x, ENNReal.ofReal (F1 x) ∂R.measure = ENNReal.ofReal (∫ x, F1 x ∂R.measure) := l1.symm
    _ ≤ ENNReal.ofReal (16 * ∫ x, G1 x ∂R.measure + 4 * ∫ x, G2 x ∂R.measure) :=
        ENNReal.ofReal_le_ofReal hfin
    _ = ENNReal.ofReal 16 * ENNReal.ofReal (∫ x, G1 x ∂R.measure) +
          ENNReal.ofReal 4 * ENNReal.ofReal (∫ x, G2 x ∂R.measure) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
    _ = _ := by rw [l2, l3]
```

## Key steps

1. μ(tsupport ζ) < ∞ by locallyIntegrable_mult; bounded a.e.-measurable functions vanishing off tsupport ζ are μ-integrable.
2. Test field X = ζ²((x − ξ) − p_S(x − ξ)) is C¹ with tsupport X ⊆ tsupport ζ ⊆ W, so δV(X) = −∫⟨X, H⟩dμ; and δV(X) = ∫div_M X dμ (withDensity).
3. dim T_xM = n μ-a.e.; by (D) and (B), div_M X = ½ζ²|p_x − p_S|² + 2ζDζ[p_x w] μ-a.e.
4. By (C) and p_S w = 0, −2ζDζ[p_x w] ≤ ¼ζ²|p_x − p_S|² + 4‖Dζ‖²|w|²; and −⟨X, H⟩ ≤ κζ²|w|.
5. Absorb: ∫ζ²|p_x − p_S|² ≤ 16∫‖Dζ‖²|w|² + 4∫κζ²|w|, then pass to lower integrals of ofReal.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `rg -n -i 'tilt|cutoff|cut-off|hilbert.?schmidt|trace' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07  (only the frozen tangentialDivergence definition, Contract.lean:264-267, and README.md:59; no tilt/cut-off/Hilbert–Schmidt lemma)`
- `rg -n -i 'TiltExcessHeight' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean  (Prop definition at :240, used only in main_theorem := by sorry at :461)`
- `rg -n 'theorem (integral_withDensity_eq_integral_smul|setLIntegral_congr_fun|setLIntegral_le_lintegral|setLIntegral_const|lintegral_add_right|lintegral_const_mul|withDensity_absolutelyContinuous|ofReal_integral_eq_lintegral_ofReal)' and 'lemma setLIntegral_eq_of_support_subset' in the snapshot Mathlib`
- `rg -n 'theorem fderiv_of_notMem_tsupport|support_fderiv_subset' Analysis/Calculus/FDeriv/Const.lean; rg -n 'IsProj.trace' LinearAlgebra/Trace.lean; rg -n trace Analysis/InnerProductSpace/Trace.lean  (in the snapshot Mathlib)`
- `rg -n 'starProjection_(apply_eq_zero_iff|eq_self_iff)|sub_starProjection_mem_orthogonal|isIdempotentElem_starProjection|starProjection_isSymmetric|norm_starProjection_apply_le' Analysis/InnerProductSpace/Projection/Basic.lean  (in the snapshot Mathlib)`
- `grep -rn 'bounded_above_of_compact_support|integrableOn_const|comp_aestronglyMeasurable₂|apply_continuousLinearMap|AEStronglyMeasurable.inner' MeasureTheory Topology Analysis  (in the snapshot Mathlib; AEStronglyMeasurable.inner lives in MeasureTheory/Function/StronglyMeasurable/Inner.lean, which is outside the Submission's import closure)`
- `grep -n HasApproximateTangentSpaceAt /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean  (simongmt rev 2b3663083f3fe399b6296fb8eaee52169170e197, pinned by /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json)`
- `rg -n -i 'cutoff|trace|tilt' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare  (Chapter04/FirstVariation.lean trace_starProjection :122 and trace_radialEndomorphism :135; Chapter05/Basic.lean has no tilt-height lemma)`
- `#check @Poincare.SimonGMT.Chapter04.trace_starProjection after import GMT.Ch07.Submission  (unknown identifier: not in the Submission's import closure); #check of LinearMap.trace_eq_sum_inner, LinearMap.trace_smulRight, Real.smoothTransition, contDiffAt_norm, Finset.sum_mul_sq_le_sq_mul_sq (all available)`
- `python3: lean_name collision scan of the 5 dorag_th_* names over every workspace's dag.json, nodes/*/*.json and .humanize/math-wiki/*.md, plus grep of GMT/*/Submission.lean  (no hits)`
- `python3 -I lean_contract.validate_lean_statement on the 5 child lean_statements; lean (lean-4.35.0-rc3, LEAN_PATH of the built workspace) on 5 comparator-format modules Challenge_<key>.lean`
- `lean Final.lean / Final2.lean (5 children proved as theorem Submission.<name> with the frozen types; #print axioms; parent from children plus sibling stub; exact Submission.<name> comparator checks); lean Assembly.lean, EProof.lean, BCD.lean, AProof.lean, Full.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-b5982cc9c1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/tiltheight-decomp-4Xk0Bt/Final.lean`
- `/tmp/tiltheight-decomp-4Xk0Bt/Final2.lean`
- `/tmp/tiltheight-decomp-4Xk0Bt/Assembly.lean`
- `/tmp/tiltheight-decomp-4Xk0Bt/EProof.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace contract and to GMT/Ch07/Submission.lean, which is the compiler context of every child type.

Nothing in the snapshot proves the tilt–height estimate or any child, so no comparator-accepted declaration can be reused:
- GMT/Ch07 contains only the frozen definitions (tangentialDivergence, firstVariation, approxTangentPlane).
- GMT/Ch05 states TiltExcessHeightEstimate only behind main_theorem := by sorry, for a different varifold type.
- SimonGMT Chapter05/Basic.lean has no tilt-height lemma.
- SimonGMT Chapter04/FirstVariation.lean:122 (trace_starProjection) is outside the Submission's import closure, so child B re-derives trace p_T = dim T.

Pinned facts the proofs rely on:
- SimonGMT Chapter03/Rectifiable.lean:102: HasApproximateTangentSpaceAt includes finrank = n, which gives dim T_xM = n μ-a.e. in E.
- Snapshot Mathlib: integral_withDensity_eq_integral_smul (ContinuousLinearMap.lean:251), setLIntegral_eq_of_support_subset (Lebesgue/Basic.lean:545), fderiv_of_notMem_tsupport (FDeriv/Const.lean:375), LinearMap.trace_eq_sum_inner (InnerProductSpace/Trace.lean:25), starProjection_apply_eq_zero_iff (Projection/Basic.lean:689) and Continuous.comp_aestronglyMeasurable₂ (AEStronglyMeasurable.lean:263) all exist.

Lean checks:
- All 5 child types elaborate in comparator scope and pass the lexical validator.
- Each child is proved as Submission.<name> with axioms propext, Classical.choice and Quot.sound only.
- The exact frozen parent type follows from A, E and the sibling dorag_approxTangent_starProjection_aesm, with axioms propext, Classical.choice and Quot.sound only.
- None of the 5 dorag_th_* names collides with any reservation.
