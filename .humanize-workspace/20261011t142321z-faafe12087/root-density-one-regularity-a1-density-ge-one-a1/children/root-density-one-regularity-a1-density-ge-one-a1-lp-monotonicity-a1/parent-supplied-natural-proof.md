# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_regularity-a1.density_ge_one-a1`
- Child DAG node: `root.density_one_regularity-a1.density_ge_one-a1.lp_monotonicity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 4, 3.3-3.6 and 4.1-4.8, with the corrected constant kappa = (p-n)/(4p) of 4.2. This is steps 0 and 2d-5 of the parent proof. One change: following the remark after step 5, the integrating factor is built from the majorant c of |F_0| instead of F_0 itself. Notation: mu := V.weight; P_x := V.tangentProj x; r(x) := |x - xi|; B_t := closed ball B_t(xi); kappa := (p-n)/(4p) > 0; a := 1 - n/p in (0,1); p > n >= 1, so p > 1. For sigma > 0 put f(sigma) := exp((Lambda/2)(sigma/R)^a) and c(sigma) := 2 kappa Lambda R^(-1) (sigma/R)^(-n/p) >= 0. Then f > 0, f is differentiable on (0, infinity), and f'(sigma) = f(sigma) (Lambda/2) a R^(-1) (sigma/R)^(a-1) = f(sigma) c(sigma), since 2 kappa = (p-n)/(2p) = a/2 and a - 1 = -n/p. The claim is that G(sigma) := f(sigma) (sigma^(-n) mu(B_sigma) + 1) is nondecreasing on (0, R].

0. Finiteness.
(a) For every compact K contained in U, mu(K) = int over M cap K of theta dH^n < infinity (structure field integrableOn_mult). In particular mu(B_t) <= mu(B_R) < infinity for t <= R.
(b) H is mu-integrable on B_R, because H is locally mu-integrable on U (first part of the generalized mean curvature hypothesis) and B_R is a compact subset of U.
(c) Let A := int over B_R of |H|^p dmu, in [0, infinity]. The hypothesis says (R^(p-n) A)^(1/p) <= kappa Lambda < infinity, and R^(p-n) > 0, so A < infinity and A^(1/p) <= kappa Lambda R^(-(p-n)/p).

1. Cutoffs. For e in (0,1] fix a C^1 nonincreasing function phi_e : R -> [0,1] with phi_e = 1 on (-infinity, 1] and phi_e = 0 on [1+e, infinity). For example phi_e(t) := psi((1 + e - t)/e), where psi is the standard C^infinity nondecreasing transition function (psi = 0 on (-infinity, 0], psi = 1 on [1, infinity), 0 <= psi <= 1). Then phi_e' <= 0, phi_e' vanishes outside [1, 1+e], and M_e := sup |phi_e'| < infinity. Put q(x) := |(x - xi) - P_x(x - xi)|^2 / |x - xi|^2, with q(xi) := 0. Then 0 <= q <= 1, because P_x is an orthogonal projection or 0 by definition. For 0 < sigma < R/(1+e) define
I_e(sigma) := int phi_e(r/sigma) dmu,
N_e(sigma) := - int (r/sigma) phi_e'(r/sigma) q dmu,
K_e(sigma) := int phi_e(r/sigma) <x - xi, H(x)> dmu.
Each integrand vanishes unless r <= (1+e) sigma, so it vanishes outside B_{(1+e)sigma}, which is contained in B_R. The integrands of I_e and K_e are integrable by step 0. N_e(sigma) >= 0, because its integrand -(r/sigma) phi_e'(r/sigma) q is pointwise >= 0. Also 0 <= I_e(sigma) <= mu(B_R). Put m_e(sigma) := sigma^(-n) I_e(sigma). In the parent's notation N_e = sigma J_e' with J_e(sigma) = int phi_e(r/sigma) q dmu, but J_e itself is not needed.

2. Differentiation of I_e (Simon 3.4). Fix e, sigma0 in (0, R/(1+e)) and alpha, beta with 0 < alpha < sigma0 < beta < R/(1+e). For sigma in [alpha, beta] and every x, the map sigma -> phi_e(r/sigma) is C^1 with derivative -(r/sigma^2) phi_e'(r/sigma). This derivative is continuous in (sigma, x), nonzero only if 1 <= r/sigma <= 1+e, and then bounded by (1+e) M_e / sigma <= 2 M_e / alpha. It vanishes outside B_{(1+e)beta}, which is contained in B_R. So it is dominated, uniformly for sigma in [alpha, beta], by the integrable function (2 M_e / alpha) 1_{B_R}. By differentiation under the integral sign (dominated derivative), I_e is differentiable at sigma0, and for every sigma in (0, R/(1+e)):
sigma I_e'(sigma) = - int (r/sigma) phi_e'(r/sigma) dmu.

3. First variation, (4.1). For sigma in (0, R/(1+e)) apply the sibling child radial_first_variation. Its hypotheses hold: phi := phi_e, b := 1+e, phi_e = 1 on [0,1] and = 0 on [b, infinity), phi_e is C^1, B_{b sigma} is contained in B_R and hence in U, and (G1), (G2) and the generalized mean curvature hypothesis are assumed. It gives
int [n phi_e(r/sigma) + (r/sigma) phi_e'(r/sigma)] dmu - int (r/sigma) phi_e'(r/sigma) q dmu = - K_e(sigma).
Split the first integral (both summands are bounded, vanish outside B_R and are therefore integrable) and use step 2 and the definition of N_e. The left side becomes n I_e - sigma I_e' + N_e. Hence
(3.1) sigma I_e'(sigma) = n I_e(sigma) + N_e(sigma) + K_e(sigma),
and therefore m_e'(sigma) = sigma^(-n) I_e' - n sigma^(-n-1) I_e = sigma^(-n-1)(sigma I_e' - n I_e) = sigma^(-n-1) (N_e(sigma) + K_e(sigma)).

4. Hoelder estimate, (4.2)-(4.3). Let sigma be in (0, R/(1+e)). Where phi_e(r/sigma) != 0 we have r < (1+e) sigma <= 2 sigma. Also 0 <= phi_e <= 1 implies phi_e <= phi_e^(1 - 1/p). Hoelder's inequality with exponents p and p/(p-1) then gives, all integrals over B_R,
|K_e(sigma)| <= int phi_e(r/sigma) r |H| dmu <= 2 sigma int phi_e(r/sigma)^(1-1/p) |H| dmu <= 2 sigma A^(1/p) (int phi_e(r/sigma) dmu)^(1-1/p) = 2 sigma A^(1/p) I_e(sigma)^(1-1/p).
Hence |sigma^(-n-1) K_e(sigma)| <= 2 sigma^(-n) A^(1/p) I_e^(1-1/p) = 2 sigma^(-n/p) A^(1/p) m_e(sigma)^(1-1/p) <= 2 sigma^(-n/p) A^(1/p) (1 + m_e(sigma)). Here we used u^(1-1/p) <= 1 + u for u >= 0: if u <= 1 the left side is <= 1, and if u > 1 it is <= u. By step 0(c), 2 sigma^(-n/p) A^(1/p) <= 2 kappa Lambda sigma^(-n/p) R^(-(p-n)/p) = 2 kappa Lambda R^(-1) (sigma/R)^(-n/p) = c(sigma). Therefore
(4.3') |sigma^(-n-1) K_e(sigma)| <= c(sigma) (1 + m_e(sigma)).

5. Integrating factor, (4.4). On (0, R/(1+e)) put G_e(sigma) := f(sigma) (m_e(sigma) + 1). By steps 2-3 and f' = f c, G_e is differentiable with
G_e' = f c (m_e + 1) + f sigma^(-n-1) (N_e + K_e) >= f [c (1 + m_e) - |sigma^(-n-1) K_e|] >= 0,
by N_e >= 0, (4.3') and f > 0. A function that is differentiable with nonnegative derivative on an open interval is nondecreasing there (mean value theorem), so G_e is nondecreasing on (0, R/(1+e)).
Remark (relation to the parent's step 4): the parent takes the exact factor exp(int_0^sigma F_0), with F_0 := -sigma^(-n-1) K_e/(1 + m_e). Its argument only uses |F_0| <= c. Replacing F_0 by its majorant c gives the factor exp(int_0^sigma c(t) dt) = exp((Lambda/2)(sigma/R)^(1-n/p)) = f(sigma). This satisfies the same bounds (4.5), with E := f - 1, and does not depend on e or H, so the limit e -> 0 below only involves I_e.

6. Letting e -> 0 (closed balls, (4.7)-(4.8)). Let 0 < sigma < tau < R. For every e in (0,1] with (1+e) tau < R (all small e > 0), step 5 gives G_e(sigma) <= G_e(tau). Fix t in {sigma, tau}. As e -> 0+, phi_e(r/t) -> 1_{r <= t} pointwise. If r <= t then r/t <= 1 and phi_e(r/t) = 1. If r > t then 1 + e <= r/t for e <= r/t - 1, so phi_e(r/t) = 0. The functions are dominated by 1_{B_R}, which is integrable. By dominated convergence I_e(t) -> mu(B_t), so G_e(t) -> G(t) = f(t)(t^(-n) mu(B_t) + 1). Passing to the limit gives G(sigma) <= G(tau).

7. Endpoint tau = R. Let 0 < sigma < R. For t in (sigma, R), step 6 and B_t contained in B_R give G(sigma) <= G(t) <= f(t)(t^(-n) mu(B_R) + 1). The right side is continuous in t and tends to f(R)(R^(-n) mu(B_R) + 1) = G(R) as t -> R-. Hence G(sigma) <= G(R). Together with step 6 and the trivial case sigma = tau, G is nondecreasing on (0, R]. QED.

Formalization notes (not part of the argument):
- psi = Real.smoothTransition, with lemmas contDiff, monotone, zero_of_nonpos, one_of_one_le, nonneg, le_one.
- Step 2: hasDerivAt_integral_of_dominated_loc_of_deriv_le.
- Step 4: integral_mul_le_Lp_mul_Lq_of_nonneg or ENNReal.lintegral_mul_le_Lp_mul_Lq.
- Step 5: monotoneOn_of_deriv_nonneg.
- Step 6: tendsto_integral_filter_of_dominated_convergence.
- Integrability of functions bounded on B_R and vanishing outside it: Measure.integrableOn_of_bounded with integrableOn_iff_integrable_of_support_subset.
- SimonGMT (Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean, FirstVariation.lean) runs exactly this argument for its own Chapter04.RectifiableVarifold, using squared-radius cutoffs phi(r^2/rho^2) and a globally locally finite weight. See integral_mul_cutoff_le, abs_cutoffMeanCurvatureError_le_holder, abs_cutoffLpMeanCurvatureError_le, lpMonotonicityFactor (= f), hasDerivAt_lpMonotonicityFactor, lp_normalizedCutoffMass_monotoneOn, lp_normalizedBallMass_monotoneOn, lp_normalizedBallMass_monotoneOn_Ioc, hasDerivAt_integral_scaledRadialCutoff_mul, tendsto_cutoffMass, monotonicityCutoff. These can be adapted as templates; lp_normalizedBallMass_monotoneOn_Ioc is the analogue of this child's conclusion. Here the weight is only finite on compact subsets of U, so every support and every domination set must stay inside B_R.

APPENDIX (formal reference, not part of the mathematical proof). Complete Lean proof of this exact frozen statement, using the sibling `radial_cutoff_first_variation_eq` (child radial_first_variation). It was compiled during the decomposition review (Lean v4.35.0-rc3, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d, simongmt 2b3663083f3fe399b6296fb8eaee52169170e197) after lines 1-460 of GMT/Ch05/Contract.lean, with ONE extra line `import Poincare.SimonGMT.Chapter04.LpMeanCurvature` among the imports. The code sits inside `namespace Submission`, directly after the sibling's proof. The helper lemmas are prefixed `lpm_`. `#print axioms Submission.lp_corrected_mass_ratio_monotoneOn` reports [propext, Classical.choice, Quot.sound]. The generic SimonGMT cutoff `Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff e t = 1 - Real.smoothTransition ((t - 1)/e)` plays the role of phi_e. All integrals are taken over the finite measure mu restricted to B_R(xi).
```lean
/-- Hölder's inequality against a cutoff with values in `[0,1]` (adapted from SimonGMT). -/
theorem lpm_integral_mul_cutoff_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    {p : ℝ} (hp : 1 < p) {f ψ : α → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ)
    (hfnonneg : ∀ x, 0 ≤ f x) (hψmeas : AEStronglyMeasurable ψ μ)
    (hψ : ∀ x, ψ x ∈ Icc 0 1) :
    (∫ x, f x * ψ x ∂μ) ≤
      (∫ x, f x ^ p ∂μ) ^ (1 / p) * (∫ x, ψ x ∂μ) ^ (1 - 1 / p) := by
  let q := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hψLp : MemLp ψ (ENNReal.ofReal q) μ :=
    MemLp.of_bound hψmeas 1 (Eventually.of_forall fun x ↦ by
      rw [Real.norm_of_nonneg (hψ x).1]
      exact (hψ x).2)
  have hψint : Integrable ψ μ := hψLp.integrable (by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hpq.symm.lt.le)
  have hψpowint : Integrable (fun x ↦ ψ x ^ q) μ := by
    have h := hψLp.integrable_norm_rpow'
    simpa only [ENNReal.toReal_ofReal hpq.symm.nonneg,
      Real.norm_of_nonneg (hψ _).1] using h
  have hpowle : (∫ x, ψ x ^ q ∂μ) ≤ ∫ x, ψ x ∂μ :=
    integral_mono hψpowint hψint
      (fun x ↦ Real.rpow_le_self_of_le_one (hψ x).1 (hψ x).2 hpq.symm.lt.le)
  have hexp : 1 / q = 1 - 1 / p := by
    simpa only [one_div] using hpq.one_sub_inv.symm
  calc
    _ ≤ (∫ x, f x ^ p ∂μ) ^ (1 / p) * (∫ x, ψ x ^ q ∂μ) ^ (1 / q) :=
      integral_mul_le_Lp_mul_Lq_of_nonneg hpq
        (Eventually.of_forall hfnonneg) (Eventually.of_forall fun x ↦ (hψ x).1) hf hψLp
    _ ≤ (∫ x, f x ^ p ∂μ) ^ (1 / p) * (∫ x, ψ x ∂μ) ^ (1 / q) := by
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (integral_nonneg fun x ↦
          Real.rpow_nonneg (hψ x).1 _) hpowle hpq.symm.one_div_nonneg)
      exact Real.rpow_nonneg (integral_nonneg fun x ↦
        Real.rpow_nonneg (hfnonneg x) _) _
    _ = _ := by rw [hexp]

theorem lpm_rpow_normalization {n : ℕ} {a ρ p : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ) :
    a ^ (1 - 1 / p) / ρ ^ n =
      ρ ^ (-(n : ℝ) / p) * (a / ρ ^ n) ^ (1 - 1 / p) := by
  rw [Real.div_rpow ha (pow_pos hρ n).le, ← Real.rpow_natCast ρ n,
    ← Real.rpow_mul hρ.le]
  calc
    _ = a ^ (1 - 1 / p) * ρ ^ (-(n : ℝ)) := by rw [Real.rpow_neg hρ.le]; rfl
    _ = a ^ (1 - 1 / p) *
        (ρ ^ (-(n : ℝ) / p) * ρ ^ (-((n : ℝ) * (1 - 1 / p)))) := by
      rw [← Real.rpow_add hρ]
      congr 2
      ring
    _ = _ := by rw [Real.rpow_neg hρ.le]; ring

theorem lpm_rpow_le_one_add {a p : ℝ} (ha : 0 ≤ a) (hp : 1 < p) :
    a ^ (1 - 1 / p) ≤ 1 + a := by
  have he0 : 0 ≤ 1 - 1 / p := sub_nonneg.mpr ((div_le_one (by linarith)).mpr hp.le)
  have he1 : 1 - 1 / p ≤ 1 := by
    have : 0 ≤ 1 / p := by positivity
    linarith
  by_cases ha1 : a ≤ 1
  · exact (Real.rpow_le_one ha ha1 he0).trans (by linarith)
  · exact (Real.rpow_le_self_of_one_le (le_of_not_ge ha1) he1).trans (by linarith)

theorem lpm_lpScale_coefficient {n : ℕ} {R ρ p : ℝ} (hR : 0 < R) (hρ : 0 < ρ) :
    ρ ^ (-(n : ℝ) / p) / R ^ (1 - n / p) =
      R⁻¹ * (ρ / R) ^ (-(n : ℝ) / p) := by
  rw [Real.div_rpow hρ.le hR.le, Real.rpow_sub hR, Real.rpow_one,
    div_div_eq_mul_div]
  simp only [neg_div]
  rw [Real.rpow_neg hR.le]
  field_simp

/-- The error estimate: `2 t A^{1/p} I^{1-1/p} ≤ t^{n+1} c(t) (1 + I/t^n)`. -/
theorem lpm_error_le {n : ℕ} {p R Λ A I t : ℝ} (hp : 1 < p) (hR : 0 < R) (ht : 0 < t)
    (hA : 0 ≤ A) (hI : 0 ≤ I)
    (hscale : R ^ (1 - (n : ℝ) / p) * A ^ (1 / p) ≤ (p - n) / (4 * p) * Λ) :
    2 * t * (A ^ (1 / p) * I ^ (1 - 1 / p)) ≤
      t ^ (n + 1) * (2 * ((p - n) / (4 * p)) * Λ * R⁻¹ * (t / R) ^ (-(n : ℝ) / p)) *
        (1 + I / t ^ n) := by
  have hm : 0 ≤ I / t ^ n := div_nonneg hI (pow_pos ht n).le
  have hnorm := lpm_rpow_normalization (n := n) (p := p) hI ht
  have hle := lpm_rpow_le_one_add hm hp
  have hRpos : 0 < R ^ (1 - (n : ℝ) / p) := Real.rpow_pos_of_pos hR _
  have hAle : A ^ (1 / p) ≤ (p - n) / (4 * p) * Λ / R ^ (1 - (n : ℝ) / p) := by
    rw [le_div_iff₀ hRpos]
    linarith [hscale]
  have hcoef := lpm_lpScale_coefficient (n := n) (p := p) hR ht
  have ha : 0 ≤ A ^ (1 / p) := Real.rpow_nonneg hA _
  have hs : 0 < t ^ (-(n : ℝ) / p) := Real.rpow_pos_of_pos ht _
  have hu : 0 ≤ (I / t ^ n) ^ (1 - 1 / p) := Real.rpow_nonneg hm _
  have hI' : I ^ (1 - 1 / p) = t ^ n * (t ^ (-(n : ℝ) / p) * (I / t ^ n) ^ (1 - 1 / p)) := by
    rw [← hnorm]
    field_simp
  have htn : 0 < t ^ (n + 1) := pow_pos ht _
  calc 2 * t * (A ^ (1 / p) * I ^ (1 - 1 / p))
      = 2 * t ^ (n + 1) * t ^ (-(n : ℝ) / p) * A ^ (1 / p) * (I / t ^ n) ^ (1 - 1 / p) := by
        rw [hI']; ring
    _ ≤ 2 * t ^ (n + 1) * t ^ (-(n : ℝ) / p) * A ^ (1 / p) * (1 + I / t ^ n) := by
        apply mul_le_mul_of_nonneg_left hle
        positivity
    _ ≤ 2 * t ^ (n + 1) * t ^ (-(n : ℝ) / p) *
          ((p - n) / (4 * p) * Λ / R ^ (1 - (n : ℝ) / p)) * (1 + I / t ^ n) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        apply mul_le_mul_of_nonneg_left hAle
        positivity
    _ = t ^ (n + 1) * (2 * ((p - n) / (4 * p)) * Λ *
          (t ^ (-(n : ℝ) / p) / R ^ (1 - (n : ℝ) / p))) * (1 + I / t ^ n) := by
        ring
    _ = _ := by rw [hcoef]; ring

/-- A bound for `s φ_ε'(s)`. -/
theorem lpm_cutoff_deriv_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ s : ℝ, |s * deriv (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε) s| ≤ C := by
  have hcont : Continuous (fun s : ℝ => s * deriv (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε) s) :=
    continuous_id.mul (Poincare.SimonGMT.Chapter04.RectifiableVarifold.contDiff_monotonicityCutoff ε).continuous_deriv_one
  have hsupp : HasCompactSupport (fun s : ℝ => s * deriv (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε) s) := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (1 : ℝ) (1 + ε)))
    intro s hs
    simp only [mem_Icc, not_and_or, not_le] at hs
    rcases hs with hs | hs
    · rw [Poincare.SimonGMT.Chapter04.RectifiableVarifold.deriv_monotonicityCutoff_eq_zero_below_one hε hs, mul_zero]
    · rw [Poincare.SimonGMT.Chapter04.RectifiableVarifold.deriv_eq_zero_of_cutoff (fun u hu => Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff_zero hε hu) hs, mul_zero]
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hcont
  exact ⟨C, fun s => by simpa [Real.norm_eq_abs] using hC s⟩

/-- Differentiation under the integral sign for `t ↦ ∫ φ(r/t) dν` (finite `ν`). -/
theorem lpm_hasDerivAt_integral_cutoff {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsFiniteMeasure ν] {r : α → ℝ} (hr : Measurable r) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {B C : ℝ} (hφB : ∀ s, |φ s| ≤ B) (hφC : ∀ s, |s * deriv φ s| ≤ C) {t₀ : ℝ}
    (ht₀ : 0 < t₀) :
    HasDerivAt (fun t => ∫ x, φ (r x / t) ∂ν)
      (-(∫ x, r x / t₀ * deriv φ (r x / t₀) ∂ν) / t₀) t₀ := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hφC 0)
  have hφm : Measurable φ := hφ.continuous.measurable
  have hφ'm : Measurable (deriv φ) := hφ.continuous_deriv_one.measurable
  have hderiv : ∀ x, ∀ t ∈ Ioo (t₀ / 2) (2 * t₀),
      HasDerivAt (fun t => φ (r x / t)) (-(r x / t * deriv φ (r x / t)) / t) t := by
    intro x t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have h1 : HasDerivAt (fun t => r x / t) (-(r x) / t ^ 2) t := by
      have := (hasDerivAt_inv ht0).const_mul (r x)
      convert this using 1
      · ext s; simp [div_eq_mul_inv]
      · field_simp
    have h2 := ((hφ.differentiable (by simp) (r x / t)).hasDerivAt).comp t h1
    convert h2 using 1
    · rfl
    · ring
  have hbound : ∀ x, ∀ t ∈ Ioo (t₀ / 2) (2 * t₀),
      ‖-(r x / t * deriv φ (r x / t)) / t‖ ≤ 2 * C / t₀ := by
    intro x t ht
    have htpos : 0 < t := by linarith [ht.1]
    rw [norm_div, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos htpos]
    calc |r x / t * deriv φ (r x / t)| / t ≤ C / t :=
          div_le_div_of_nonneg_right (hφC _) htpos.le
      _ ≤ C / (t₀ / 2) := div_le_div_of_nonneg_left hC0 (by linarith) ht.1.le
      _ = 2 * C / t₀ := by field_simp
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun t x => φ (r x / t)) (F' := fun t x => -(r x / t * deriv φ (r x / t)) / t)
    (x₀ := t₀) (s := Ioo (t₀ / 2) (2 * t₀)) (bound := fun _ => 2 * C / t₀)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun t => (hφm.comp (hr.div_const t)).aestronglyMeasurable)
    (Integrable.of_bound (hφm.comp (hr.div_const t₀)).aestronglyMeasurable B
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hφB _))
    ((((hr.div_const t₀).mul (hφ'm.comp (hr.div_const t₀))).neg.div_const
      t₀).aestronglyMeasurable)
    (Eventually.of_forall fun x t ht => hbound x t ht)
    (integrable_const _)
    (Eventually.of_forall fun x t ht => hderiv x t ht)
  have hval : ∫ x, -(r x / t₀ * deriv φ (r x / t₀)) / t₀ ∂ν =
      -(∫ x, r x / t₀ * deriv φ (r x / t₀) ∂ν) / t₀ := by
    rw [integral_div, integral_neg]
  rw [← hval]
  exact key.2

/-- Dominated convergence of the cutoff masses to the closed-ball mass. -/
theorem lpm_tendsto_cutoff_integral {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (ν : Measure E) [IsFiniteMeasure ν] (ξ : E) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun ε => ∫ x, Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / t) ∂ν) (𝓝[>] 0)
      (𝓝 (ν.real (closedBall ξ t))) := by
  have hlim : ∀ x, Tendsto (fun ε => Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / t)) (𝓝[>] 0)
      (𝓝 ((closedBall ξ t).indicator (fun _ => (1 : ℝ)) x)) := by
    intro x
    have h := Poincare.SimonGMT.Chapter04.RectifiableVarifold.tendsto_monotonicityCutoff (‖x - ξ‖ / t)
    have hmem : ‖x - ξ‖ / t ∈ Iic 1 ↔ x ∈ closedBall ξ t := by
      rw [mem_Iic, div_le_one ht, mem_closedBall, dist_eq_norm]
    convert h using 2
    by_cases hx : x ∈ closedBall ξ t
    · rw [indicator_of_mem hx, indicator_of_mem (hmem.mpr hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hmem.mp h))]
  have h := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε x => Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / t))
    (f := (closedBall ξ t).indicator (fun _ => (1 : ℝ))) (fun _ => (1 : ℝ))
    (Eventually.of_forall fun ε => ((Poincare.SimonGMT.Chapter04.RectifiableVarifold.contDiff_monotonicityCutoff ε).continuous.comp
      ((continuous_id.sub continuous_const).norm.div_const t)).aestronglyMeasurable)
    (Eventually.of_forall fun ε => Eventually.of_forall fun x => by
      have := Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff_mem_Icc ε (‖x - ξ‖ / t)
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]
      exact this.2)
    (integrable_const _)
    (Eventually.of_forall hlim)
  rwa [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul,
    mul_one] at h

/-- The "integrating factor" argument: a differential inequality gives monotonicity. -/
theorem lpm_ode_monotone {n : ℕ} {p R Λ : ℝ} (hp : 0 < p) (hR : 0 < R)
    {I D : ℝ → ℝ} {σ τ : ℝ} (hσ : 0 < σ) (hστ : σ ≤ τ)
    (hI : ∀ t ∈ Icc σ τ, HasDerivAt I (D t) t)
    (hineq : ∀ t ∈ Icc σ τ,
      -(t ^ (n + 1) * (2 * ((p - n) / (4 * p)) * Λ * R⁻¹ * (t / R) ^ (-(n : ℝ) / p)) *
        (1 + I t / t ^ n)) ≤ t * D t - n * I t) :
    Real.exp (Λ / 2 * (σ / R) ^ (1 - (n : ℝ) / p)) * (I σ / σ ^ n + 1) ≤
      Real.exp (Λ / 2 * (τ / R) ^ (1 - (n : ℝ) / p)) * (I τ / τ ^ n + 1) := by
  set c : ℝ → ℝ := fun t => 2 * ((p - n) / (4 * p)) * Λ * R⁻¹ * (t / R) ^ (-(n : ℝ) / p)
    with hc
  set f : ℝ → ℝ := Poincare.SimonGMT.Chapter04.RectifiableVarifold.lpMonotonicityFactor n p R Λ with hf
  have hfval : ∀ t, f t = Real.exp (Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p)) := fun t => rfl
  have hderiv : ∀ t ∈ Icc σ τ, HasDerivAt (fun t => f t * (I t / t ^ n + 1))
      (f t * c t * (I t / t ^ n + 1) +
        f t * ((D t * t ^ n - I t * (n * t ^ n / t)) / (t ^ n) ^ 2)) t := by
    intro t ht
    have ht0 : 0 < t := hσ.trans_le ht.1
    have hfd := Poincare.SimonGMT.Chapter04.RectifiableVarifold.hasDerivAt_lpMonotonicityFactor (n := n) hp hR ht0 Λ
    have hpow : HasDerivAt (fun t : ℝ ↦ t ^ n) (n * t ^ n / t) t := by
      convert (hasDerivAt_id t).pow n using 1
      · rfl
      · cases n with
        | zero => simp
        | succ m => simp [pow_succ, ht0.ne', mul_div_assoc]
    have hm := ((hI t ht).div hpow (pow_ne_zero n ht0.ne')).add_const 1
    convert hfd.mul hm using 1
    simp only [hc, hf, Poincare.SimonGMT.Chapter04.RectifiableVarifold.lpMeanCurvatureKappa, Pi.div_apply]
  have hnonneg : ∀ t ∈ Icc σ τ, 0 ≤ f t * c t * (I t / t ^ n + 1) +
        f t * ((D t * t ^ n - I t * (n * t ^ n / t)) / (t ^ n) ^ 2) := by
    intro t ht
    have ht0 : 0 < t := hσ.trans_le ht.1
    have htn : 0 < t ^ n := pow_pos ht0 n
    have htn1 : 0 < t ^ (n + 1) := pow_pos ht0 (n + 1)
    have hX := hineq t ht
    have heq : (D t * t ^ n - I t * (n * t ^ n / t)) / (t ^ n) ^ 2 =
        (t * D t - n * I t) / t ^ (n + 1) := by
      field_simp
      ring
    have h1 : -(c t * (1 + I t / t ^ n)) ≤ (t * D t - n * I t) / t ^ (n + 1) := by
      rw [le_div_iff₀ htn1]
      have : -(c t * (1 + I t / t ^ n)) * t ^ (n + 1) =
          -(t ^ (n + 1) * c t * (1 + I t / t ^ n)) := by ring
      rw [this]
      exact hX
    rw [heq]
    have hfpos : 0 < f t := Real.exp_pos _
    have : f t * c t * (I t / t ^ n + 1) + f t * ((t * D t - n * I t) / t ^ (n + 1)) =
        f t * (c t * (1 + I t / t ^ n) + (t * D t - n * I t) / t ^ (n + 1)) := by ring
    rw [this]
    exact mul_nonneg hfpos.le (by linarith)
  have hmono : MonotoneOn (fun t => f t * (I t / t ^ n + 1)) (Icc σ τ) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc σ τ)
      (fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt)
    · intro t ht
      rw [interior_Icc] at ht
      exact (hderiv t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t (Ioo_subset_Icc_self ht)).deriv]
      exact hnonneg t (Ioo_subset_Icc_self ht)
  exact hmono ⟨le_rfl, hστ⟩ ⟨hστ, le_rfl⟩ hστ

/-- Hölder bound for the mean-curvature term `K(t) = ∫ φ(|x-ξ|/t) ⟨x-ξ, H⟩ dν`. -/
theorem lpm_abs_integral_cutoff_inner_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (ν : Measure E) [IsFiniteMeasure ν]
    (ξ : E) (H : E → E) {p : ℝ} (hp : 1 < p)
    (hHint : Integrable H ν) (hLp : MemLp (fun x => ‖H x‖) (ENNReal.ofReal p) ν)
    {φ : ℝ → ℝ} (hφc : Continuous φ) (hφrange : ∀ s, φ s ∈ Icc 0 1) {b t : ℝ} (hb : 0 ≤ b)
    (ht : 0 < t) (hφzero : ∀ s, b ≤ s → φ s = 0) :
    |∫ x, φ (‖x - ξ‖ / t) * inner ℝ (x - ξ) (H x) ∂ν| ≤
      b * t * ((∫ x, ‖H x‖ ^ p ∂ν) ^ (1 / p) * (∫ x, φ (‖x - ξ‖ / t) ∂ν) ^ (1 - 1 / p)) := by
  have hψc : Continuous (fun x : E => φ (‖x - ξ‖ / t)) :=
    hφc.comp ((continuous_id.sub continuous_const).norm.div_const t)
  have hψm : AEStronglyMeasurable (fun x : E => φ (‖x - ξ‖ / t)) ν := hψc.aestronglyMeasurable
  have hprod : Integrable (fun x => ‖H x‖ * φ (‖x - ξ‖ / t)) ν :=
    hHint.norm.mul_bdd hψm (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (hφrange _).1]; exact (hφrange _).2)
  have hbound : ∀ x, ‖φ (‖x - ξ‖ / t) * inner ℝ (x - ξ) (H x)‖ ≤
      b * t * (‖H x‖ * φ (‖x - ξ‖ / t)) := by
    intro x
    by_cases hx : ‖x - ξ‖ ≤ b * t
    · rw [norm_mul, Real.norm_of_nonneg (hφrange _).1]
      calc φ (‖x - ξ‖ / t) * ‖inner ℝ (x - ξ) (H x)‖
          ≤ φ (‖x - ξ‖ / t) * (b * t * ‖H x‖) :=
            mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
              (mul_le_mul_of_nonneg_right hx (norm_nonneg _))) (hφrange _).1
        _ = b * t * (‖H x‖ * φ (‖x - ξ‖ / t)) := by ring
    · have h0 : φ (‖x - ξ‖ / t) = 0 := hφzero _ (by rw [le_div_iff₀ ht]; linarith)
      simp [h0]
  have hholder := lpm_integral_mul_cutoff_le ν hp hLp (fun x => norm_nonneg (H x)) hψm
    (fun x => hφrange _)
  calc |∫ x, φ (‖x - ξ‖ / t) * inner ℝ (x - ξ) (H x) ∂ν|
      = ‖∫ x, φ (‖x - ξ‖ / t) * inner ℝ (x - ξ) (H x) ∂ν‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, b * t * (‖H x‖ * φ (‖x - ξ‖ / t)) ∂ν :=
        norm_integral_le_of_norm_le (hprod.const_mul _) (Eventually.of_forall hbound)
    _ = b * t * ∫ x, ‖H x‖ * φ (‖x - ξ‖ / t) ∂ν := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hholder (mul_nonneg hb ht.le)

/-- The hypothesis on the scaled `Lᵖ` norm gives `‖H‖ ∈ Lᵖ` and the real bound
`R^{1-n/p} (∫ ‖H‖^p)^{1/p} ≤ κ Λ`. -/
theorem lpm_scaled_bound {α : Type*} [MeasurableSpace α] {E : Type*} [NormedAddCommGroup E]
    (ν : Measure α) {H : α → E} (hHm : AEStronglyMeasurable H ν) {n : ℕ} {p R Λ : ℝ}
    (hp : (n : ℝ) < p) (hR : 0 < R) (hΛ : 0 ≤ Λ)
    (hscale : (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x, ‖H x‖ₑ ^ p ∂ν) ^ (1 / p) ≤
      ENNReal.ofReal ((p - n) / (4 * p) * Λ)) :
    MemLp (fun x => ‖H x‖) (ENNReal.ofReal p) ν ∧
      R ^ (1 - (n : ℝ) / p) * (∫ x, ‖H x‖ ^ p ∂ν) ^ (1 / p) ≤ (p - n) / (4 * p) * Λ := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have hRpos : 0 < R ^ (p - n) := Real.rpow_pos_of_pos hR _
  have hκ : 0 ≤ (p - n) / (4 * p) * Λ :=
    mul_nonneg (div_nonneg (by linarith) (by linarith)) hΛ
  set L := ∫⁻ x, ‖H x‖ₑ ^ p ∂ν with hL
  have hLtop : L < ∞ := by
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hRpos).ne',
      ENNReal.top_rpow_of_pos (by positivity)] at hscale
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hscale)
  have hmeas : AEStronglyMeasurable (fun x => ‖H x‖) ν := hHm.norm
  have hMemLp : MemLp (fun x => ‖H x‖) (ENNReal.ofReal p) ν := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (ENNReal.ofReal_pos.mpr hp0).ne'
      ENNReal.ofReal_ne_top hmeas]
    simpa [ENNReal.toReal_ofReal hp0.le, enorm_norm] using hLtop
  refine ⟨hMemLp, ?_⟩
  have hAeq : ∫ x, ‖H x‖ ^ p ∂ν = L.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)
      (hmeas.aemeasurable.pow_const p).aestronglyMeasurable, hL]
    congr 1
    apply lintegral_congr
    intro x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
  have hA0 : 0 ≤ ∫ x, ‖H x‖ ^ p ∂ν :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hLeq : L = ENNReal.ofReal (∫ x, ‖H x‖ ^ p ∂ν) := by
    rw [hAeq, ENNReal.ofReal_toReal hLtop.ne]
  rw [hLeq, ← ENNReal.ofReal_mul hRpos.le,
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hRpos.le hA0) (by positivity),
    ENNReal.ofReal_le_ofReal_iff hκ] at hscale
  calc R ^ (1 - (n : ℝ) / p) * (∫ x, ‖H x‖ ^ p ∂ν) ^ (1 / p)
      = (R ^ (p - n) * ∫ x, ‖H x‖ ^ p ∂ν) ^ (1 / p) := by
        rw [Real.mul_rpow hRpos.le hA0, ← Real.rpow_mul hR.le,
          show (p - n) * (1 / p) = 1 - (n : ℝ) / p by field_simp]
    _ ≤ _ := hscale

/-- First variation with the cutoff `φ_ε`, transferred to `ν = μ ⌞ B_R(ξ)`, in the form
`K(t) ≤ -∫ s φ_ε'(s) dν - n I(t)` (the normal term is dropped since it is `≤ 0`). -/
theorem lpm_cutoff_first_variation_ge {n ℓ : ℕ} {U : Set (Amb n ℓ)}
    (V : RectifiableVarifold n ℓ U)
    (H : Amb n ℓ → Amb n ℓ) (hH : V.HasGeneralizedMeanCurvature H)
    (hG2 : AEStronglyMeasurable V.tangentProj V.weight)
    (hG1 : ∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧
      V.tangentProj x = P.starProjection)
    (ξ : Amb n ℓ) {R : ℝ} (hball : closedBall ξ R ⊆ U)
    [IsFiniteMeasure (V.weight.restrict (closedBall ξ R))]
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) (htR : (1 + ε) * t < R) :
    ∫ x, Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / t) * inner ℝ (x - ξ) (H x)
        ∂(V.weight.restrict (closedBall ξ R)) ≤
      -(∫ x, ‖x - ξ‖ / t * deriv (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε) (‖x - ξ‖ / t)
          ∂(V.weight.restrict (closedBall ξ R))) -
        n * ∫ x, Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / t) ∂(V.weight.restrict (closedBall ξ R)) := by
  have hφC1 : ContDiff ℝ 1 (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε) := Poincare.SimonGMT.Chapter04.RectifiableVarifold.contDiff_monotonicityCutoff ε
  have hfv := radial_cutoff_first_variation_eq V H hH hG2 hG1 ξ t (1 + ε)
    (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε) ht hφC1
    (fun s hs => Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff_one hε hs.2) (fun s hs => Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff_zero hε hs)
    ((closedBall_subset_closedBall htR.le).trans hball)
  have hout : ∀ x, x ∉ closedBall ξ R → 1 + ε < ‖x - ξ‖ / t := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    rw [lt_div_iff₀ ht]
    linarith
  have hφout : ∀ x, x ∉ closedBall ξ R → Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / t) = 0 :=
    fun x hx => Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff_zero hε (hout x hx).le
  have hφ'out : ∀ x, x ∉ closedBall ξ R → deriv (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε) (‖x - ξ‖ / t) = 0 :=
    fun x hx => Poincare.SimonGMT.Chapter04.RectifiableVarifold.deriv_eq_zero_of_cutoff (fun u hu => Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff_zero hε hu) (hout x hx)
  have e1 : ∫ x, ((n : ℝ) * Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / t) +
        ‖x - ξ‖ / t * deriv (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε) (‖x - ξ‖ / t)) ∂V.weight =
      ∫ x, ((n : ℝ) * Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / t) +
        ‖x - ξ‖ / t * deriv (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε) (‖x - ξ‖ / t))
          ∂(V.weight.restrict (closedBall ξ R)) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hφout x hx, hφ'out x hx]; ring).symm
  have e2 : ∫ x, ‖x - ξ‖ / t * deriv (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε) (‖x - ξ‖ / t) *
        (‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2) ∂V.weight =
      ∫ x, ‖x - ξ‖ / t * deriv (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε) (‖x - ξ‖ / t) *
        (‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2)
          ∂(V.weight.restrict (closedBall ξ R)) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hφ'out x hx]; ring).symm
  have e3 : ∫ x, Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / t) * inner ℝ (x - ξ) (H x) ∂V.weight =
      ∫ x, Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / t) * inner ℝ (x - ξ) (H x)
        ∂(V.weight.restrict (closedBall ξ R)) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hφout x hx]; ring).symm
  rw [e1, e2, e3] at hfv
  obtain ⟨C, hC⟩ := lpm_cutoff_deriv_bound hε
  have hs_cont : Continuous (fun x : Amb n ℓ => ‖x - ξ‖ / t) :=
    (continuous_id.sub continuous_const).norm.div_const t
  have hint1 : Integrable (fun x => (n : ℝ) * Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / t))
      (V.weight.restrict (closedBall ξ R)) :=
    Integrable.of_bound
      ((continuous_const.mul (hφC1.continuous.comp hs_cont)).aestronglyMeasurable) n
      (Eventually.of_forall fun x => by
        have := Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff_mem_Icc ε (‖x - ξ‖ / t)
        rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast, abs_of_nonneg this.1]
        exact mul_le_of_le_one_right (Nat.cast_nonneg n) this.2)
  have hint2 : Integrable (fun x => ‖x - ξ‖ / t * deriv (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε) (‖x - ξ‖ / t))
      (V.weight.restrict (closedBall ξ R)) :=
    Integrable.of_bound
      ((hs_cont.mul (hφC1.continuous_deriv_one.comp hs_cont)).aestronglyMeasurable) C
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC _)
  rw [integral_add hint1 hint2, integral_const_mul] at hfv
  have hN : ∫ x, ‖x - ξ‖ / t * deriv (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε) (‖x - ξ‖ / t) *
      (‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2)
        ∂(V.weight.restrict (closedBall ξ R)) ≤ 0 := by
    refine integral_nonpos (fun x => ?_)
    have h1 : 0 ≤ ‖x - ξ‖ / t := div_nonneg (norm_nonneg _) ht.le
    have h2 : deriv (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε) (‖x - ξ‖ / t) ≤ 0 :=
      (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff_antitone hε).deriv_nonpos
    have h3 : 0 ≤ ‖(x - ξ) - V.tangentProj x (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2 := by positivity
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h1 h2) h3
  linarith

theorem lp_corrected_mass_ratio_monotoneOn : ∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), 1 ≤ n → (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → AEStronglyMeasurable V.tangentProj V.weight → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ (ξ : Amb n ℓ) (R Λ : ℝ), 0 < R → 0 ≤ Λ → closedBall ξ R ⊆ U → V.scaledLpNorm H p ξ R ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → MonotoneOn (fun σ : ℝ => Real.exp (Λ / 2 * (σ / R) ^ (1 - (n : ℝ) / p)) * ((V.weight (closedBall ξ σ)).toReal / σ ^ n + 1)) (Ioc 0 R) := by
  intro n ℓ U V H p hn hnp hH hG2 hG1 ξ R Λ hR hΛ hball hscale
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hnp
  have hp1 : 1 < p := lt_of_le_of_lt (by exact_mod_cast hn) hnp
  -- Step 0: finiteness of `μ(B_R(ξ))`, integrability of `H`, and the real `Lᵖ` bound
  have hμR : V.weight (closedBall ξ R) < ∞ := by
    have hint := V.integrableOn_mult _ (isCompact_closedBall ξ R) hball
    rw [RectifiableVarifold.weight, withDensity_apply _ isClosed_closedBall.measurableSet,
      Measure.restrict_restrict isClosed_closedBall.measurableSet, Set.inter_comm]
    exact hint.lintegral_lt_top
  have hfin : IsFiniteMeasure (V.weight.restrict (closedBall ξ R)) :=
    isFiniteMeasure_restrict.mpr hμR.ne
  have hHint : Integrable H (V.weight.restrict (closedBall ξ R)) :=
    hH.1.integrableOn_compact_subset hball (isCompact_closedBall ξ R)
  obtain ⟨hLp, hA⟩ := lpm_scaled_bound (V.weight.restrict (closedBall ξ R))
    hHint.aestronglyMeasurable hnp hR hΛ hscale
  -- Steps 1-5: monotonicity of the smoothed ratio `G_ε`
  have hGε : ∀ ε, 0 < ε → ε ≤ 1 → ∀ σ τ, 0 < σ → σ ≤ τ → (1 + ε) * τ < R →
      Real.exp (Λ / 2 * (σ / R) ^ (1 - (n : ℝ) / p)) *
          ((∫ x, Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / σ) ∂(V.weight.restrict (closedBall ξ R))) /
            σ ^ n + 1) ≤
        Real.exp (Λ / 2 * (τ / R) ^ (1 - (n : ℝ) / p)) *
          ((∫ x, Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / τ) ∂(V.weight.restrict (closedBall ξ R))) /
            τ ^ n + 1) := by
    intro ε hε hε1 σ τ hσ hστ hτR
    obtain ⟨C, hC⟩ := lpm_cutoff_deriv_bound hε
    refine lpm_ode_monotone (n := n) (p := p) (R := R) (Λ := Λ)
      (I := fun t => ∫ x, Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / t) ∂(V.weight.restrict (closedBall ξ R)))
      (D := fun t => -(∫ x, ‖x - ξ‖ / t * deriv (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε) (‖x - ξ‖ / t)
          ∂(V.weight.restrict (closedBall ξ R))) / t)
      hp0 hR hσ hστ ?_ ?_
    · intro t ht
      exact lpm_hasDerivAt_integral_cutoff _ (r := fun x => ‖x - ξ‖)
        (measurable_id.sub_const ξ).norm
        (Poincare.SimonGMT.Chapter04.RectifiableVarifold.contDiff_monotonicityCutoff ε) (B := 1) (fun s => by
          have := Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff_mem_Icc ε s
          rw [abs_of_nonneg this.1]; exact this.2) hC (hσ.trans_le ht.1)
    · intro t ht
      have ht0 : 0 < t := hσ.trans_le ht.1
      have htR : (1 + ε) * t < R :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht.2 (by linarith)) hτR
      have hfv := lpm_cutoff_first_variation_ge V H hH hG2 hG1 ξ hball hε ht0 htR
      have hK := lpm_abs_integral_cutoff_inner_le (V.weight.restrict (closedBall ξ R)) ξ H hp1
        hHint hLp (Poincare.SimonGMT.Chapter04.RectifiableVarifold.contDiff_monotonicityCutoff ε).continuous (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff_mem_Icc ε)
        (b := 1 + ε) (by linarith) ht0 (fun s hs => Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff_zero hε hs)
      set ν := V.weight.restrict (closedBall ξ R) with hν
      set Iε := ∫ x, Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / t) ∂ν with hIε
      set S := ∫ x, ‖x - ξ‖ / t * deriv (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε) (‖x - ξ‖ / t) ∂ν with hS
      set K := ∫ x, Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / t) * inner ℝ (x - ξ) (H x) ∂ν with hKdef
      set A := ∫ x, ‖H x‖ ^ p ∂ν with hAdef
      have hInn : 0 ≤ Iε := integral_nonneg fun x => (Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff_mem_Icc ε _).1
      have hA0 : 0 ≤ A := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
      have harith := lpm_error_le (n := n) hp1 hR ht0 hA0 hInn hA
      have hprodnn : 0 ≤ A ^ (1 / p) * Iε ^ (1 - 1 / p) :=
        mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hInn _)
      have h2 : (1 + ε) * t * (A ^ (1 / p) * Iε ^ (1 - 1 / p)) ≤
          2 * t * (A ^ (1 / p) * Iε ^ (1 - 1 / p)) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hprodnn
      have htD : t * (-S / t) = -S := by field_simp
      have habs := neg_abs_le K
      have key : -(t ^ (n + 1) * (2 * ((p - n) / (4 * p)) * Λ * R⁻¹ * (t / R) ^ (-(n : ℝ) / p)) *
          (1 + Iε / t ^ n)) ≤ t * (-S / t) - n * Iε := by
        rw [htD]; linarith
      exact key
  -- Step 6: letting `ε → 0`, the cutoff masses converge to closed-ball masses
  have hlimit : ∀ t, 0 < t → t ≤ R →
      Tendsto (fun ε => ∫ x, Poincare.SimonGMT.Chapter04.RectifiableVarifold.monotonicityCutoff ε (‖x - ξ‖ / t)
          ∂(V.weight.restrict (closedBall ξ R)))
        (𝓝[>] 0) (𝓝 (V.weight (closedBall ξ t)).toReal) := by
    intro t ht htR
    have h := lpm_tendsto_cutoff_integral (V.weight.restrict (closedBall ξ R)) ξ ht
    have heq : (V.weight.restrict (closedBall ξ R)).real (closedBall ξ t) =
        (V.weight (closedBall ξ t)).toReal := by
      rw [measureReal_def, Measure.restrict_apply measurableSet_closedBall,
        inter_eq_left.mpr (closedBall_subset_closedBall htR)]
    rwa [heq] at h
  have hIoo : ∀ σ τ, 0 < σ → σ ≤ τ → τ < R →
      Real.exp (Λ / 2 * (σ / R) ^ (1 - (n : ℝ) / p)) *
          ((V.weight (closedBall ξ σ)).toReal / σ ^ n + 1) ≤
        Real.exp (Λ / 2 * (τ / R) ^ (1 - (n : ℝ) / p)) *
          ((V.weight (closedBall ξ τ)).toReal / τ ^ n + 1) := by
    intro σ τ hσ hστ hτR
    have hτ : 0 < τ := hσ.trans_le hστ
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (1 + ε) * τ < R := by
      have hc : Tendsto (fun ε : ℝ => (1 + ε) * τ) (𝓝[>] 0) (𝓝 ((1 + 0) * τ)) :=
        ((tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds)).mul_const τ)
      rw [add_zero, one_mul] at hc
      exact hc.eventually (gt_mem_nhds hτR)
    apply le_of_tendsto_of_tendsto
      ((((hlimit σ hσ (by linarith)).div_const (σ ^ n)).add_const 1).const_mul
        (Real.exp (Λ / 2 * (σ / R) ^ (1 - (n : ℝ) / p))))
      ((((hlimit τ hτ hτR.le).div_const (τ ^ n)).add_const 1).const_mul
        (Real.exp (Λ / 2 * (τ / R) ^ (1 - (n : ℝ) / p))))
    filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hεR hε
    exact hGε ε hε.1 hε.2.le σ τ hσ hστ hεR
  -- Step 7: the endpoint `τ = R`
  intro σ hσ τ hτ hστ
  rcases lt_or_eq_of_le hτ.2 with hτR | hτR
  · exact hIoo σ τ hσ.1 hστ hτR
  rcases lt_or_eq_of_le hστ with hστ' | hστ'
  · have hσR : σ < R := hτR ▸ hστ'
    have hcont : ContinuousAt (fun t : ℝ => Real.exp (Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p)) *
        ((V.weight (closedBall ξ R)).toReal / t ^ n + 1)) R := by
      have hf := (Poincare.SimonGMT.Chapter04.RectifiableVarifold.hasDerivAt_lpMonotonicityFactor (n := n) hp0 hR hR Λ).continuousAt
      exact hf.mul ((continuousAt_const.div (continuousAt_id.pow n)
        (pow_ne_zero n hR.ne')).add continuousAt_const)
    have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio R))
    rw [hτR]
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsLT hσR] with t ht
    have ht0 : 0 < t := hσ.1.trans ht.1
    calc _ ≤ Real.exp (Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p)) *
          ((V.weight (closedBall ξ t)).toReal / t ^ n + 1) :=
          hIoo σ t hσ.1 ht.1.le ht.2
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        have hmono : (V.weight (closedBall ξ t)).toReal ≤ (V.weight (closedBall ξ R)).toReal :=
          ENNReal.toReal_mono hμR.ne (measure_mono (closedBall_subset_closedBall ht.2.le))
        have := div_le_div_of_nonneg_right hmono (pow_pos ht0 n).le
        linarith
  · rw [hστ']
```

## Key steps

1. Finiteness: mu(B_R(xi)) < infinity, H in L^1(mu restricted to B_R(xi)), A = int_{B_R}|H|^p < infinity with A^(1/p) <= kappa Lambda R^(-(p-n)/p)
2. For C^1 nonincreasing cutoffs phi_e (1 on (-infinity,1], 0 on [1+e,infinity)) differentiate I_e(sigma) = int phi_e(r/sigma) dmu under the integral: sigma I_e' = -int (r/sigma) phi_e'(r/sigma) dmu
3. radial_first_variation with b = 1+e gives sigma I_e' = n I_e + N_e + K_e with N_e = -int (r/sigma) phi_e' |w_perp|^2 >= 0, hence (sigma^-n I_e)' = sigma^(-n-1)(N_e + K_e) (4.1)
4. Hoelder: |sigma^(-n-1) K_e| <= c(sigma)(1 + sigma^-n I_e) with c(sigma) = 2 kappa Lambda R^-1 (sigma/R)^(-n/p) = f'/f for f = exp((Lambda/2)(sigma/R)^(1-n/p)) (4.3)
5. G_e = f (sigma^-n I_e + 1) has G_e' >= 0, so it is nondecreasing on (0, R/(1+e)) (explicit integrating factor, 4.4)
6. Let e -> 0 by dominated convergence (I_e(t) -> mu(B_t), closed balls) to get monotonicity on (0,R); extend to the endpoint R by continuity of f and B_t contained in B_R

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
