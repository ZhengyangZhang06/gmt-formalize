# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_regularity-a1.density_ge_one-a1`
- Child DAG node: `root.density_one_regularity-a1.density_ge_one-a1.radial_first_variation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 4, 3.1-3.3 (first variation of the radial field (r)(x - xi)), with general mean curvature as in 3.14, 3.16 and 4.1; this is step 2, parts (2a)-(2c), of the parent proof, with the parent's cutoff phi. Notation: mu := V.weight = theta H^n restricted to M; P_x := V.tangentProj x; r(x) := |x - xi|; s(x) := r(x)/sigma; phi' := deriv phi, which is continuous because phi is C^1; |w_perp(x)|^2 := |(x - xi) - P_x(x - xi)|^2 / |x - xi|^2 for x != xi and |w_perp(xi)|^2 := 0 (this is also the Lean value of 0/0). Hypotheses used: (GMC) H is locally mu-integrable on U and int div_M X dmu = - int <X, H> dmu for every C^1 compactly supported X with tsupport X contained in U, where div_M X(x) = trace(DX(x) o P_x); (G1) for mu-a.e. x, P_x is the orthogonal projection onto an n-dimensional linear subspace; (G2) x -> P_x is mu-a.e. strongly measurable.

1. Facts about phi and b. (i) b > 1: otherwise t0 := max(b, 0) lies in [0,1] and t0 >= b, so 1 = phi(t0) = 0, which is absurd. (ii) phi is constant on the open sets (0,1) and (b, infinity), so phi' = 0 there. (iii) phi and phi' are continuous; put C0 := max over [0,b] of |phi| and C1 := max over [0,b] of |phi'|, both finite.

2. Finiteness. K := closed ball B_{b sigma}(xi) is compact and K is contained in U. By definition of the weight, mu(K) = int over M cap K of theta dH^n, which is finite because theta is H^n-integrable on M cap K (structure field integrableOn_mult with the compact K contained in U). By (GMC), H is locally mu-integrable on U, hence mu-integrable on the compact set K contained in U.

3. The test field X(x) := phi(s(x)) (x - xi).
(a) X is C^1. On the open ball of radius sigma about xi we have 0 <= s(x) < 1, so phi(s(x)) = 1 and X(x) = x - xi there. On the open set {x != xi} the map x -> |x - xi| is C^infinity (the Euclidean norm is smooth away from 0), so x -> phi(|x - xi|/sigma) is C^1 and X is C^1 as a product. The two open sets cover R^(n+l), and being C^1 is a local property.
(b) Support. If X(x) != 0 then phi(s(x)) != 0, so s(x) < b, i.e. x lies in the open ball of radius b sigma. Hence tsupport X is contained in K, which is contained in U, and X has compact support (a closed subset of the compact K).
(c) By (GMC), int div_M X dmu = - int <X, H> dmu = - int phi(s(x)) <x - xi, H(x)> dmu, because <c v, w> = c <v, w>.

4. Derivative of X. For x != xi let w := (x - xi)/r. The derivative of y -> |y - xi| at x is v -> <w, v> (e.g. from |y - xi| = (|y - xi|^2)^(1/2) and D|y - xi|^2 = 2 <y - xi, .>). By the chain and product rules, DX(x)v = phi(s) v + sigma^(-1) phi'(s) <w, v> (x - xi) = phi(s) v + (phi'(s)/(sigma r)) <x - xi, v> (x - xi). At x = xi: X(y) = y - xi on a neighbourhood of xi, so DX(xi) = Id.

5. Trace lemma. Let Q be the orthogonal projection onto an n-dimensional subspace T. For alpha, beta real and a in R^(n+l), L := alpha Id + beta <a, .> a satisfies trace(L o Q) = alpha trace(Q) + beta trace(v -> <a, Qv> a) = alpha n + beta <Qa, a> = alpha n + beta |Qa|^2. Indeed trace Q = dim T = n; v -> <a, Qv> a = <Qa, v> a (Q self-adjoint) is a rank-one map with trace <Qa, a>; and <a, Qa> = <Qa, Qa> since Q is self-adjoint and idempotent. Moreover |a|^2 = |Qa|^2 + |a - Qa|^2 because Qa is orthogonal to a - Qa.

6. Pointwise divergence. Let x be a point at which P_x is the orthogonal projection onto an n-dimensional subspace; by (G1) this holds for mu-a.e. x.
If x != xi, steps 4 and 5 with alpha = phi(s), beta = phi'(s)/(sigma r), a = x - xi give div_M X(x) = n phi(s) + (phi'(s)/(sigma r)) |P_x(x - xi)|^2 = n phi(s) + (phi'(s)/(sigma r)) (r^2 - |(x - xi) - P_x(x - xi)|^2) = [n phi(s) + s phi'(s)] - s phi'(s) |w_perp(x)|^2.
If x = xi, DX(xi) = Id gives div_M X(xi) = trace(P_xi) = n = n phi(0) (phi(0) = 1 since 0 is in [0,1]), and the right-hand side [n phi(0) + 0 * phi'(0)] - 0 * phi'(0) * 0 also equals n.
Put g(x) := n phi(s(x)) + s(x) phi'(s(x)) and h(x) := s(x) phi'(s(x)) |w_perp(x)|^2. Then div_M X = g - h mu-almost everywhere.

7. Integrability. g is continuous; it vanishes outside K, since x not in K means s(x) > b, so phi(s) = 0 and phi'(s) = 0 by 1(ii); and |g| <= n C0 + b C1 on K. As mu(K) < infinity, g is mu-integrable. For h: x -> P_x(x - xi) is mu-a.e. strongly measurable by (G2), because evaluation (L, v) -> L v is continuous, so h is a.e. strongly measurable. Also h vanishes outside K (factor phi'(s)), and 0 <= |w_perp|^2 <= 1: for every x, P_x is either an orthogonal projection or 0 by the definition of tangentProj, and in both cases |v - P_x v| <= |v|; alternatively use (G1) for a.e. x. So |h| <= b C1 on K, and h is mu-integrable. (Integrability of phi(s(x)) <x - xi, H(x)> is not needed: the right-hand side of the identity is the same Bochner integral as in step 3(c). It does hold anyway, since the function is a.e. strongly measurable, vanishes outside K and is bounded by C0 b sigma |H| on K, with H in L^1(mu restricted to K) by step 2.)

8. Conclusion. By step 6, int div_M X dmu = int (g - h) dmu, and by step 7 this equals int g dmu - int h dmu. Combining with step 3(c) gives int g dmu - int h dmu = - int phi(s(x)) <x - xi, H(x)> dmu, which is the asserted identity with g and h written out. QED.

Formalization notes (not part of the argument):
- SimonGMT (Poincare/SimonGMT/Chapter04/FirstVariation.lean) has generic lemmas for any finite-dimensional real inner product space: trace_radialEndomorphism (trace(((a • id) + b • f.smulRight v) ∘ P.starProjection) = a * finrank P + b * f (P.starProjection v)), trace_starProjection, inner_starProjection_eq_norm_sq and deriv_eq_zero_of_cutoff. These cover steps 1(ii) and 5.
- Mathlib contDiffAt_norm (needs x - xi != 0), with contDiff_iff_contDiffAt and Filter.EventuallyEq.contDiffAt_iff, gives step 3(a).
- MeasureTheory.integral_congr_ae and integral_sub give step 8.
- The verified Lean proof in the appendix below uses a squared-radius reparametrization. Write phi(r/sigma) = eta(r^2) with eta(t) := phi(sqrt(t)/sigma). Then eta = 1 on (-infinity, sigma^2], eta is C^1 because sqrt is smooth on (0, infinity), and X(x) = eta(|x - xi|^2)(x - xi) is C^1 with DX(x) = eta Id + 2 eta' <x - xi, .>(x - xi) at every x (no case split at xi). Finally 2 r^2 eta'(r^2) = s phi'(s) for r > 0, and both sides vanish at r = 0. SimonGMT's squared-radius lemmas contDiff_squaredRadialVectorField and hasFDerivAt_squaredRadialVectorField follow the same route.

APPENDIX (formal reference, not part of the mathematical proof). Complete Lean proof of this exact frozen statement. It was compiled during the decomposition review (Lean v4.35.0-rc3, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d, simongmt 2b3663083f3fe399b6296fb8eaee52169170e197) after lines 1-460 of GMT/Ch05/Contract.lean, inside `namespace Submission`. No extra imports are needed. `#print axioms Submission.radial_cutoff_first_variation_eq` reports [propext, Classical.choice, Quot.sound].
```lean
theorem radial_cutoff_first_variation_eq : ∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → AEStronglyMeasurable V.tangentProj V.weight → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ (ξ : Amb n ℓ) (σ b : ℝ) (φ : ℝ → ℝ), 0 < σ → ContDiff ℝ 1 φ → (∀ t ∈ Icc (0 : ℝ) 1, φ t = 1) → (∀ t, b ≤ t → φ t = 0) → closedBall ξ (b * σ) ⊆ U → ∫ x, ((n : ℝ) * φ (‖x - ξ‖ / σ) + ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ)) ∂V.weight - ∫ x, ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ) * (‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2) ∂V.weight = -∫ x, φ (‖x - ξ‖ / σ) * inner ℝ (x - ξ) (H x) ∂V.weight := by
  intro n ℓ U V H hH hG2 hG1 ξ σ b φ hσ hφ hφ1 hφ0 hball
  -- Step 1: `b > 1`
  have hb : 1 < b := by
    by_contra hb
    have hb' : b ≤ 1 := le_of_not_gt hb
    have h1 := hφ1 (max b 0) ⟨le_max_right _ _, max_le hb' zero_le_one⟩
    have h0 := hφ0 (max b 0) (le_max_left _ _)
    rw [h1] at h0
    exact one_ne_zero h0
  have hbσ : 0 < b * σ := mul_pos (by linarith) hσ
  -- Step 2: finiteness of the weight on `K = B_{bσ}(ξ)`
  have hKfin : V.weight (closedBall ξ (b * σ)) < ∞ := by
    have hint := V.integrableOn_mult _ (isCompact_closedBall ξ (b * σ)) hball
    rw [RectifiableVarifold.weight, withDensity_apply _ isClosed_closedBall.measurableSet,
      Measure.restrict_restrict isClosed_closedBall.measurableSet, Set.inter_comm]
    exact hint.lintegral_lt_top
  -- the squared-radius profile `η(t) = φ(√t / σ)`
  set η : ℝ → ℝ := fun t => φ (Real.sqrt t / σ) with hη_def
  have hη_one : ∀ t, t < σ ^ 2 → η t = 1 := by
    intro t ht
    apply hφ1
    constructor
    · exact div_nonneg (Real.sqrt_nonneg _) hσ.le
    · rw [div_le_one₀ hσ]
      calc Real.sqrt t ≤ Real.sqrt (σ ^ 2) := Real.sqrt_le_sqrt ht.le
        _ = σ := Real.sqrt_sq hσ.le
  have hη_zero : ∀ t, (b * σ) ^ 2 ≤ t → η t = 0 := by
    intro t ht
    apply hφ0
    rw [le_div_iff₀ hσ]
    calc b * σ = Real.sqrt ((b * σ) ^ 2) := (Real.sqrt_sq hbσ.le).symm
      _ ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
  have hη_C1 : ContDiff ℝ 1 η := by
    rw [contDiff_iff_contDiffAt]
    intro t
    rcases lt_or_ge t (σ ^ 2) with ht | ht
    · have hev : η =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [Iio_mem_nhds ht] with s hs
        exact hη_one s hs
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have ht0 : t ≠ 0 := (lt_of_lt_of_le (pow_pos hσ 2) ht).ne'
      exact hφ.contDiffAt.comp t ((Real.contDiffAt_sqrt ht0).div_const σ)
  have hη_diff : Differentiable ℝ η := hη_C1.differentiable (by simp)
  have hη_sq : ∀ x : Amb n ℓ, η (‖x - ξ‖ ^ 2) = φ (‖x - ξ‖ / σ) := by
    intro x
    simp only [hη_def, Real.sqrt_sq (norm_nonneg _)]
  have hη_deriv : ∀ x : Amb n ℓ,
      2 * deriv η (‖x - ξ‖ ^ 2) * ‖x - ξ‖ ^ 2 = ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ) := by
    intro x
    rcases (norm_nonneg (x - ξ)).eq_or_lt with hr | hr
    · rw [← hr]; simp
    · have hr2 : ‖x - ξ‖ ^ 2 ≠ 0 := pow_ne_zero 2 hr.ne'
      have hd : HasDerivAt η (deriv φ (Real.sqrt (‖x - ξ‖ ^ 2) / σ) *
          (1 / (2 * Real.sqrt (‖x - ξ‖ ^ 2)) / σ)) (‖x - ξ‖ ^ 2) :=
        (hφ.differentiable (by simp) _).hasDerivAt.comp _ ((Real.hasDerivAt_sqrt hr2).div_const σ)
      rw [hd.deriv, Real.sqrt_sq (norm_nonneg _)]
      field_simp
  -- Step 3: the test field `X(x) = φ(|x - ξ|/σ) (x - ξ)`
  set X : Amb n ℓ → Amb n ℓ := fun x => η (‖x - ξ‖ ^ 2) • (x - ξ) with hX_def
  have hX_C1 : ContDiff ℝ 1 X := by
    have hsub : ContDiff ℝ 1 (fun x : Amb n ℓ ↦ x - ξ) := contDiff_id.sub contDiff_const
    exact (hη_C1.comp (hsub.norm_sq ℝ)).smul hsub
  have hX_ball : tsupport X ⊆ closedBall ξ (b * σ) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hxb
    have hnorm : b * σ < ‖x - ξ‖ := by
      simpa only [mem_closedBall, dist_eq_norm, not_le] using hxb
    have hzero : η (‖x - ξ‖ ^ 2) = 0 :=
      hη_zero _ (by nlinarith [norm_nonneg (x - ξ)])
    exact hx (by simp [hX_def, hzero])
  have hX_cpt : HasCompactSupport X :=
    (isCompact_closedBall ξ (b * σ)).of_isClosed_subset (isClosed_tsupport _) hX_ball
  have hX_supp : tsupport X ⊆ U := hX_ball.trans hball
  have hFV := hH.2 X hX_C1 hX_cpt hX_supp
  have hrhs : ∀ x, inner ℝ (X x) (H x) = φ (‖x - ξ‖ / σ) * inner ℝ (x - ξ) (H x) := by
    intro x
    rw [← hη_sq x]
    exact real_inner_smul_left (x - ξ) (H x) (η (‖x - ξ‖ ^ 2))
  -- Step 4: derivative of `X`
  have hfd : ∀ x, fderiv ℝ X x = η (‖x - ξ‖ ^ 2) • ContinuousLinearMap.id ℝ (Amb n ℓ) +
      (2 * deriv η (‖x - ξ‖ ^ 2)) • (innerSL ℝ (x - ξ)).smulRight (x - ξ) := by
    intro x
    have hsub : HasFDerivAt (fun y : Amb n ℓ ↦ y - ξ) (ContinuousLinearMap.id ℝ (Amb n ℓ)) x :=
      hasFDerivAt_sub_const ξ
    have hsq := hsub.norm_sq
    have hηComp := (hη_diff (‖x - ξ‖ ^ 2)).hasDerivAt.comp_hasFDerivAt x hsq
    have hX' : HasFDerivAt X (η (‖x - ξ‖ ^ 2) • ContinuousLinearMap.id ℝ (Amb n ℓ) +
        (2 * deriv η (‖x - ξ‖ ^ 2)) • (innerSL ℝ (x - ξ)).smulRight (x - ξ)) x := by
      refine (hηComp.smul hsub).congr_fderiv ?_
      ext1 w
      simp [mul_smul]
      module
    exact hX'.fderiv
  -- trace of `(a • id + b • f.smulRight v) ∘ P` for an orthogonal projection `P`
  have htrace : ∀ (P : Submodule ℝ (Amb n ℓ)) (a c : ℝ) (f : Amb n ℓ →L[ℝ] ℝ) (v : Amb n ℓ),
      LinearMap.trace ℝ (Amb n ℓ)
        (((a • ContinuousLinearMap.id ℝ (Amb n ℓ)) + c • f.smulRight v).toLinearMap ∘ₗ
          P.starProjection.toLinearMap) =
        a * (Module.finrank ℝ P : ℝ) + c * f (P.starProjection v) := by
    intro P a c f v
    have htr : LinearMap.trace ℝ (Amb n ℓ) P.starProjection.toLinearMap =
        (Module.finrank ℝ P : ℝ) := by
      rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp,
        LinearMap.trace_comp_comm']
      have hcomp : P.orthogonalProjectionOnto.toLinearMap.comp P.subtypeL.toLinearMap =
          LinearMap.id := by
        ext x
        simp
      rw [hcomp, LinearMap.trace_id]
    change LinearMap.trace ℝ (Amb n ℓ)
        (((a • LinearMap.id) + c • f.toLinearMap.smulRight v).comp
          P.starProjection.toLinearMap) = _
    have hcomp :
        (((a • LinearMap.id) + c • f.toLinearMap.smulRight v).comp
            P.starProjection.toLinearMap) =
          a • P.starProjection.toLinearMap +
            c • (f.toLinearMap.comp P.starProjection.toLinearMap).smulRight v := by
      ext w
      simp
    rw [hcomp, map_add, map_smul, map_smul, LinearMap.trace_smulRight, htr]
    simp
  have hinner : ∀ (P : Submodule ℝ (Amb n ℓ)) (v : Amb n ℓ),
      inner ℝ v (P.starProjection v) = ‖P.starProjection v‖ ^ 2 := by
    intro P v
    rw [← P.inner_starProjection_left_eq_right v v]
    simpa using P.re_inner_starProjection_eq_normSq v
  -- Pythagoras
  have hpyth : ∀ (Q : Submodule ℝ (Amb n ℓ)) (w : Amb n ℓ),
      ‖w‖ ^ 2 = ‖Q.starProjection w‖ ^ 2 + ‖w - Q.starProjection w‖ ^ 2 := by
    intro Q w
    rw [← Submodule.starProjection_orthogonal_val]
    exact Submodule.norm_sq_eq_add_norm_sq_starProjection w Q
  -- Steps 5-6: pointwise divergence
  have hdiv : ∀ᵐ x ∂V.weight, V.divM X x =
      ((n : ℝ) * φ (‖x - ξ‖ / σ) + ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ)) -
        ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ) *
          (‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2) := by
    filter_upwards [hG1] with x hx
    obtain ⟨Q, hQn, hQ⟩ := hx
    rw [RectifiableVarifold.divM, hfd x, hQ, htrace,
      hQn, innerSL_apply_apply, hinner,
      hη_sq x, ← hη_deriv x]
    have hp := hpyth Q (x - ξ)
    have hkey : ‖x - ξ‖ ^ 2 * (‖(x - ξ) - Q.starProjection (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2) =
        ‖(x - ξ) - Q.starProjection (x - ξ)‖ ^ 2 := by
      rcases eq_or_ne (x - ξ) 0 with h0 | h0
      · simp [h0]
      · exact mul_div_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr h0))
    linear_combination (-2 * deriv η (‖x - ξ‖ ^ 2)) * hp + (2 * deriv η (‖x - ξ‖ ^ 2)) * hkey
  -- Step 7: integrability
  have hout : ∀ x, x ∉ closedBall ξ (b * σ) → b < ‖x - ξ‖ / σ := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    rw [lt_div_iff₀ hσ]
    exact hx
  have hφ_out : ∀ x, x ∉ closedBall ξ (b * σ) → φ (‖x - ξ‖ / σ) = 0 := fun x hx =>
    hφ0 _ (hout x hx).le
  have hφ'_out : ∀ x, x ∉ closedBall ξ (b * σ) → deriv φ (‖x - ξ‖ / σ) = 0 := by
    intro x hx
    have hzero : φ =ᶠ[𝓝 (‖x - ξ‖ / σ)] fun _ ↦ 0 := by
      filter_upwards [lt_mem_nhds (hout x hx)] with s hs
      exact hφ0 s hs.le
    exact hzero.deriv_eq.trans (deriv_const _ 0)
  have hint : ∀ f : Amb n ℓ → ℝ, AEStronglyMeasurable f V.weight →
      (∃ C, ∀ᵐ x ∂V.weight, ‖f x‖ ≤ C) → (∀ x, x ∉ closedBall ξ (b * σ) → f x = 0) →
      Integrable f V.weight := by
    intro f hf hC hzero
    obtain ⟨C, hC⟩ := hC
    have hon : IntegrableOn f (closedBall ξ (b * σ)) V.weight :=
      Measure.integrableOn_of_bounded hKfin.ne hf (ae_restrict_of_ae hC)
    refine (integrableOn_iff_integrable_of_support_subset ?_).mp hon
    intro x hx
    by_contra hxK
    exact hx (hzero x hxK)
  have hbound : ∀ f : Amb n ℓ → ℝ, Continuous f → (∀ x, x ∉ closedBall ξ (b * σ) → f x = 0) →
      ∃ C, ∀ x, ‖f x‖ ≤ C := by
    intro f hf hzero
    obtain ⟨C, hC⟩ := (isCompact_closedBall ξ (b * σ)).exists_bound_of_continuousOn hf.continuousOn
    refine ⟨max C 0, fun x => ?_⟩
    by_cases hx : x ∈ closedBall ξ (b * σ)
    · exact (hC x hx).trans (le_max_left _ _)
    · rw [hzero x hx, norm_zero]
      exact le_max_right _ _
  have hs_cont : Continuous (fun x : Amb n ℓ => ‖x - ξ‖ / σ) :=
    (continuous_id.sub continuous_const).norm.div_const σ
  have hφc : Continuous φ := hφ.continuous
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv_one
  have hg_int : Integrable (fun x : Amb n ℓ =>
      (n : ℝ) * φ (‖x - ξ‖ / σ) + ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ)) V.weight := by
    have hc : Continuous (fun x : Amb n ℓ =>
        (n : ℝ) * φ (‖x - ξ‖ / σ) + ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ)) :=
      (continuous_const.mul (hφc.comp hs_cont)).add (hs_cont.mul (hφ'c.comp hs_cont))
    have hz : ∀ x, x ∉ closedBall ξ (b * σ) →
        (n : ℝ) * φ (‖x - ξ‖ / σ) + ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ) = 0 := by
      intro x hx
      rw [hφ_out x hx, hφ'_out x hx]
      ring
    obtain ⟨C, hC⟩ := hbound _ hc hz
    exact hint _ hc.aestronglyMeasurable ⟨C, Eventually.of_forall hC⟩ hz
  have hP_meas : AEStronglyMeasurable (fun x => V.tangentProj x (x - ξ)) V.weight :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hG2.prodMk (continuous_id.sub continuous_const).aestronglyMeasurable)
  have hq_meas : AEStronglyMeasurable
      (fun x => ‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2) V.weight := by
    have h1 : AEMeasurable (fun x => (x - ξ) - V.tangentProj x (x - ξ)) V.weight :=
      (measurable_id.sub_const ξ).aemeasurable.sub hP_meas.aemeasurable
    exact ((h1.norm.pow_const 2).div
      ((measurable_id.sub_const ξ).norm.pow_const 2).aemeasurable).aestronglyMeasurable
  have hq_bound : ∀ᵐ x ∂V.weight,
      ‖‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2‖ ≤ 1 := by
    filter_upwards [hG1] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    rw [hQ, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply div_le_one_of_le₀ _ (by positivity)
    have hp := hpyth Q (x - ξ)
    nlinarith [sq_nonneg ‖Q.starProjection (x - ξ)‖]
  have hh_int : Integrable (fun x : Amb n ℓ => ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ) *
      (‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2)) V.weight := by
    have hc : Continuous (fun x : Amb n ℓ => ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ)) :=
      hs_cont.mul (hφ'c.comp hs_cont)
    have hz : ∀ x, x ∉ closedBall ξ (b * σ) → ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ) = 0 := by
      intro x hx
      rw [hφ'_out x hx, mul_zero]
    obtain ⟨C, hC⟩ := hbound _ hc hz
    have hi : Integrable (fun x : Amb n ℓ => ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ)) V.weight :=
      hint _ hc.aestronglyMeasurable ⟨C, Eventually.of_forall hC⟩ hz
    exact hi.mul_bdd hq_meas hq_bound
  -- Step 8: conclusion
  rw [← integral_sub hg_int hh_int]
  calc ∫ x, ((n : ℝ) * φ (‖x - ξ‖ / σ) + ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ)) -
        ‖x - ξ‖ / σ * deriv φ (‖x - ξ‖ / σ) *
          (‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2) ∂V.weight
      = ∫ x, V.divM X x ∂V.weight := (integral_congr_ae hdiv).symm
    _ = -∫ x, inner ℝ (X x) (H x) ∂V.weight := hFV
    _ = -∫ x, φ (‖x - ξ‖ / σ) * inner ℝ (x - ξ) (H x) ∂V.weight := by
      rw [integral_congr_ae (Eventually.of_forall hrhs)]
```

## Key steps

1. b > 1, phi' = 0 on (0,1) and (b, infinity); K = B_{b sigma}(xi) is compact in U with mu(K) < infinity and H in L^1(mu restricted to K)
2. X(x) = phi(|x - xi|/sigma)(x - xi) is C^1 (equal to x - xi near xi, smooth away from xi) with tsupport in K, so the generalized mean curvature identity applies
3. DX(x) = phi(s) Id + (phi'(s)/(sigma r)) (x - xi)<x - xi, .> for x != xi and DX(xi) = Id
4. trace((alpha Id + beta a<a,.>) o Q) = alpha n + beta |Qa|^2 and |a|^2 = |Qa|^2 + |a - Qa|^2 for a rank-n orthogonal projection Q
5. div_M X = [n phi + s phi'] - s phi' |w_perp|^2 mu-a.e. (also at x = xi)
6. all integrands are bounded or dominated by |H| on K and vanish off K, hence integrable; split the integral and conclude

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
