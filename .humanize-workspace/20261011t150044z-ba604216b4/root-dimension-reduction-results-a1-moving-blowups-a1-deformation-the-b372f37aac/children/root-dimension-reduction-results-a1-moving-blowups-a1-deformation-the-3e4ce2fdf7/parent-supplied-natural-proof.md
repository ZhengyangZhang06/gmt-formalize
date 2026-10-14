# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1.lipschitz_smooth_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 6(i): 'For Lipschitz functions mollify g and all u_i simultaneously: for each Lipschitz h, h∗ϕ_δ → h uniformly, D(h∗ϕ_δ) = (Dh)∗ϕ_δ → Dh a.e. and |D(h∗ϕ_δ)| ≤ Lip(h)'. The parent cites Mathlib ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable for the a.e. convergence; that lemma lies outside the Submission's import closure, so the same Lebesgue-differentiation step is done below with IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub and tendsto_integral_smul_of_tendsto_average_norm_sub, which are available. Uses the siblings mollify_fderiv and mollify_lipschitz. (The frozen type is identical to that of the not yet accepted node dor_lmb_fcd_jwc_lipschitz_smooth_approx of another branch, so a fresh name is used.)

Notation: λ = Lebesgue measure on ℝᵏ = Euclid k; D = fderiv ℝ; e_i := EuclideanSpace.single i 1 (i ∈ Fin k); d := finrank ℝ (Euclid k); c := λ(closedBall(0, 1)) ∈ (0, ∞) as a real number.

1. (Bumps.) For n ∈ ℕ let φ_n be the smooth bump function at 0 (ContDiffBump (0 : Euclid k)) with inner radius r_n := 1/(n+2) and outer radius R_n := 2/(n+2) = 2r_n. Then φ_n is C^∞, 0 ≤ φ_n ≤ 1, φ_n = 1 on closedBall(0, r_n), support φ_n = ball(0, R_n), and φ_n has compact support.

2. (Normalization.) For every x and every ρ ≥ 0, λ(closedBall(x, ρ)) = ρ^d·c (Measure.addHaar_real_closedBall'), and c > 0. Since φ_n ≥ 0 is integrable and equals 1 on closedBall(0, r_n), I_n := ∫ φ_n ≥ λ(closedBall(0, r_n)) = r_n^d·c > 0. Put ρ_n := φ_n / I_n. Then ρ_n is C^∞ (in particular C¹), continuous, has compact support, ρ_n ≥ 0, ∫ ρ_n = 1, support ρ_n ⊆ ball(0, R_n), and ρ_n ≤ 1/I_n ≤ 1/(r_n^d·c) everywhere (φ_n ≤ 1).

3. (Definition and smoothness.) Put f_n(x) := ∫ ρ_n(t)·f(x − t) dt = (ρ_n ⋆ f)(x) (convolution with the multiplication pairing). ρ_n is C^∞ with compact support and f is continuous, hence locally integrable, so f_n is C^∞ (HasCompactSupport.contDiff_convolution_left).

4. (Lipschitz constant.) ρ_n is continuous, compactly supported, nonnegative with ∫ ρ_n = 1 and f is L-Lipschitz, so by the sibling mollify_lipschitz, f_n = (x ↦ ∫ ρ_n(y)·f(x − y) dy) is L-Lipschitz.

5. (Uniform convergence.) Fix n and x. For y ∈ ball(x, R_n), |f(y) − f(x)| ≤ L·|y − x| ≤ L·R_n. Since ρ_n ≥ 0, ∫ρ_n = 1 and support ρ_n ⊆ ball(0, R_n), dist_convolution_le gives |f_n(x) − f(x)| ≤ L·R_n. As L·R_n → 0 and the bound does not depend on x, f_n → f uniformly on ℝᵏ: for ε > 0, eventually L·R_n < ε, and then dist(f(x), f_n(x)) < ε for all x.

6. (Derivatives of f_n.) By the sibling mollify_fderiv (ρ_n is C¹ with compact support), for all n, x, v: Df_n(x)v = ∫ ρ_n(t)·Df(x − t)v dt.

7. (A.e. convergence in each basis direction.) Fix i and put g_i(s) := Df(s)e_i. g_i is measurable (measurable_fderiv_apply_const) and |g_i(s)| ≤ ‖Df(s)‖·‖e_i‖ ≤ L‖e_i‖ (norm_fderiv_le_of_lipschitz), so g_i is locally integrable (dominated by a constant). Lebesgue measure is uniformly locally doubling, so by the Lebesgue differentiation theorem (IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub) there is a λ-null set outside of which, for every sequence of radii R_n → 0+ and centres in closedBall(x, R_n) (here the centre x itself), the averages ⨍_{closedBall(x, R_n)} |g_i − g_i(x)| dλ tend to 0. Fix such x and apply tendsto_integral_smul_of_tendsto_average_norm_sub with the constant 2^d to the kernels K_n(y) := ρ_n(x − y). Its hypotheses hold: g_i is integrable on every closed ball; ∫ K_n = ∫ ρ_n = 1 (translation and reflection invariance, integral_sub_left_eq_self); support K_n ⊆ closedBall(x, R_n) (if K_n(y) ≠ 0 then x − y ∈ ball(0, R_n)); and 0 ≤ K_n(y) ≤ 1/(r_n^d·c) = 2^d/((2r_n)^d·c) = 2^d/λ(closedBall(x, R_n)). Hence ∫ K_n(y)·g_i(y) dy → g_i(x). By the change of variables t = x − y and step 6, ∫ K_n(y)·g_i(y) dy = ∫ ρ_n(t)·g_i(x − t) dt = Df_n(x)e_i. So Df_n(x)e_i → Df(x)e_i for λ-a.e. x.

8. (All directions and the operator norm.) The k exceptional null sets of step 7 have a null union (ae_all_iff), so for λ-a.e. x, Df_n(x)e_i → Df(x)e_i for every i ∈ Fin k. For a continuous linear T : ℝᵏ → ℝ and w ∈ ℝᵏ, w = Σ_i w(i)e_i and |w(i)| ≤ ‖w‖ (PiLp.norm_apply_le), so |Tw| ≤ Σ_i |w(i)|·|Te_i| ≤ (Σ_i |Te_i|)·‖w‖, i.e. ‖T‖ ≤ Σ_i |Te_i| (ContinuousLinearMap.opNorm_le_bound). With T = Df_n(x) − Df(x) at such a point x, 0 ≤ ‖Df_n(x) − Df(x)‖ ≤ Σ_i |Df_n(x)e_i − Df(x)e_i| → 0, so Df_n(x) → Df(x) (squeeze).

Steps 3, 4, 5 and 8 are the four required properties of the sequence (f_n).

Lean realization (compiled during this decomposition with the pinned toolchain against GMT.Ch07.Submission at b4d606db, Mathlib 25730c7c, in the Submission layout: inside namespace GMT.Ch07 after the contract's open commands, together with the proofs of the sibling declarations it uses; no extra import, no sorry; #print axioms: propext, Classical.choice, Quot.sound):
```lean
/-- **Smooth approximation of a Lipschitz function** (step 4 of the weak continuity of Jacobians):
an `L`-Lipschitz `f : ℝᵏ → ℝ` is the uniform limit of `C^∞`, `L`-Lipschitz functions `f_n` with
`Df_n(x) → Df(x)` in operator norm for a.e. `x`.  Take `f_n = ρ_n ⋆ f`, where `ρ_n = φ_n / ∫ φ_n`
normalizes a bump `φ_n` equal to `1` on `B(0, 1/(n+2))` and supported in `B(0, 2/(n+2))`.  Then
`f_n` is smooth, `L`-Lipschitz (`cmcs_ls_mollify_lipschitz`) and `|f_n - f| ≤ 2L/(n+2)`.  By
`dimred_mbl_dt_lp_jc_mollify_fderiv_eq`, `Df_n(x) eᵢ = (ρ_n ⋆ Df(·) eᵢ)(x)`; as `∫ φ_n ≥ |B(0, 1/(n+2))|`
gives `0 ≤ ρ_n ≤ 2ᵈ / |B(0, 2/(n+2))|`, this tends to `Df(x) eᵢ` at every Lebesgue point of the
bounded function `Df(·) eᵢ`, and `‖T‖ ≤ ∑ᵢ |T eᵢ|` gives convergence in operator norm. -/
theorem Submission.dimred_mbl_dt_lp_jc_lipschitz_smooth_approx : ∀ (k : ℕ) (L : NNReal) (f : Euclid k → ℝ), LipschitzWith L f → ∃ fs : ℕ → Euclid k → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (fs n)) ∧ (∀ n, LipschitzWith L (fs n)) ∧ TendstoUniformly fs f atTop ∧ ∀ᵐ x ∂(volume : Measure (Euclid k)), Tendsto (fun n => fderiv ℝ (fs n) x) atTop (𝓝 (fderiv ℝ f x)) := by
  intro k L f hf
  -- step 1: bumps `φ n` with `rIn = 1/(n+2)`, `rOut = 2/(n+2)`, normalized to `ρ n = φ n / ∫ φ n`
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  let φ : ℕ → ContDiffBump (0 : Euclid k) := fun n =>
    ⟨1 / ((n : ℝ) + 2), 2 / ((n : ℝ) + 2), by have := hpos n; positivity,
      div_lt_div_of_pos_right (by norm_num) (hpos n)⟩
  have hrOut : ∀ n, (φ n).rOut = 2 * (φ n).rIn := fun n => by
    show 2 / ((n : ℝ) + 2) = 2 * (1 / ((n : ℝ) + 2))
    rw [mul_one_div]
  -- `|B(x, r)| = r ^ d * c` with `c = |B(0, 1)| > 0`
  set d := Module.finrank ℝ (Euclid k)
  set c := (volume : Measure (Euclid k)).real (closedBall 0 1)
  have hcpos : 0 < c := ENNReal.toReal_pos (measure_closedBall_pos _ _ one_pos).ne'
    measure_closedBall_lt_top.ne
  have hvol : ∀ (x : Euclid k) (r : ℝ), 0 ≤ r →
      (volume : Measure (Euclid k)).real (closedBall x r) = r ^ d * c :=
    fun x r hr => Measure.addHaar_real_closedBall' _ x hr
  -- `φ n = 1` on `B(0, rIn)` and `φ n ≥ 0`, so `∫ φ n ≥ |B(0, rIn)| = rIn ^ d * c > 0`
  have hφint : ∀ n, Integrable (φ n) (volume : Measure (Euclid k)) := fun n =>
    (φ n).continuous.integrable_of_hasCompactSupport (φ n).hasCompactSupport
  have hIge : ∀ n, (φ n).rIn ^ d * c ≤ ∫ x, φ n x := by
    intro n
    rw [← hvol 0 _ (φ n).rIn_pos.le]
    calc (volume : Measure (Euclid k)).real (closedBall 0 (φ n).rIn)
        = ∫ x in closedBall (0 : Euclid k) (φ n).rIn, φ n x := by
          rw [setIntegral_congr_fun measurableSet_closedBall
            (fun x hx => (φ n).one_of_mem_closedBall hx), setIntegral_const, smul_eq_mul, mul_one]
      _ ≤ ∫ x, φ n x :=
          setIntegral_le_integral (hφint n) (Eventually.of_forall fun x => (φ n).nonneg)
  have hIpos : ∀ n, 0 < ∫ x, φ n x := fun n =>
    (mul_pos (pow_pos (φ n).rIn_pos d) hcpos).trans_le (hIge n)
  set ρ : ℕ → Euclid k → ℝ := fun n x => φ n x / ∫ y, φ n y with hρ
  have hρc : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ρ n) := fun n => (φ n).contDiff.div_const _
  have hρc1 : ∀ n, ContDiff ℝ 1 (ρ n) := fun n => (φ n).contDiff.div_const _
  have hρcont : ∀ n, Continuous (ρ n) := fun n => (φ n).continuous.div_const _
  have hρs : ∀ n, HasCompactSupport (ρ n) := fun n =>
    (φ n).hasCompactSupport.comp_left (g := fun t : ℝ => t / ∫ y, φ n y) (zero_div _)
  have hρ0 : ∀ n x, 0 ≤ ρ n x := fun n x => div_nonneg (φ n).nonneg (hIpos n).le
  have hρint : ∀ n, ∫ x, ρ n x = 1 := fun n => by
    show ∫ x, φ n x / ∫ y, φ n y = 1
    rw [integral_div, div_self (hIpos n).ne']
  have hρsupp : ∀ n, support (ρ n) ⊆ ball 0 (φ n).rOut := fun n x hx => by
    rw [← (φ n).support_eq, mem_support]
    intro h0
    exact (mem_support.1 hx) (by simp [hρ, h0])
  have hρle : ∀ n x, ρ n x ≤ 1 / ((φ n).rIn ^ d * c) := fun n x =>
    calc ρ n x = φ n x / ∫ y, φ n y := rfl
      _ ≤ 1 / ∫ y, φ n y := div_le_div_of_nonneg_right (φ n).le_one (hIpos n).le
      _ ≤ 1 / ((φ n).rIn ^ d * c) :=
          one_div_le_one_div_of_le (mul_pos (pow_pos (φ n).rIn_pos d) hcpos) (hIge n)
  -- `f_n = ρ n ⋆ f`
  set fs : ℕ → Euclid k → ℝ := fun n x => ∫ t, ρ n t * f (x - t) with hfs
  have hconv : ∀ n, fs n = convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    intro n; funext x; simp [hfs, convolution_def]
  have hrOut0 : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    have := tendsto_const_nhds (x := (2 : ℝ)) |>.div_atTop
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    simpa [φ] using this
  refine ⟨fs, fun n => ?_, fun n => ?_, ?_, ?_⟩
  · -- step 2: `ρ n ⋆ f` is smooth
    rw [hconv]
    exact (hρs n).contDiff_convolution_left _ (hρc n) hf.continuous.locallyIntegrable
  · -- step 3: `ρ n ⋆ f` is `L`-Lipschitz
    exact Submission.cmcs_ls_mollify_lipschitz k (ρ n) f L (hρcont n) (hρs n) (hρ0 n) (hρint n) hf
  · -- step 4: `|f_n x - f x| ≤ L * rOut` for all `x`, and `rOut → 0`
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(hrOut0.const_mul (L : ℝ)).eventually (gt_mem_nhds (by simpa using hε))]
      with n hn x
    have hdist := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := f x) (g := f)
      (by positivity : (0 : ℝ) ≤ L * (φ n).rOut) (hρsupp n) (hρ0 n) (hρint n)
      hf.continuous.aestronglyMeasurable (fun y hy => by
        calc dist (f y) (f x) ≤ L * dist y x := hf.dist_le_mul y x
          _ ≤ L * (φ n).rOut := by gcongr; exact (mem_ball.1 hy).le)
    rw [← hconv] at hdist
    rw [dist_comm]
    exact lt_of_le_of_lt hdist hn
  · -- step 5: `Df_n(x) v = ∫ ρ n t * Df(x - t) v dt`
    have hB1 : ∀ n x v, fderiv ℝ (fs n) x v = ∫ t, ρ n t * fderiv ℝ f (x - t) v := fun n x v =>
      Submission.dimred_mbl_dt_lp_jc_mollify_fderiv_eq k L f (ρ n) hf (hρc1 n) (hρs n) x v
    have hδ : Tendsto (fun n => (φ n).rOut) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hrOut0, Eventually.of_forall fun n => (φ n).rOut_pos⟩
    -- steps 6-7: for each basis vector `e_i`, `Df_n(x) e_i → Df(x) e_i` for a.e. `x`
    have hDi : ∀ i : Fin k, ∀ᵐ x ∂(volume : Measure (Euclid k)),
        Tendsto (fun n => fderiv ℝ (fs n) x (EuclideanSpace.single i (1 : ℝ))) atTop
          (𝓝 (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)))) := by
      intro i
      set g : Euclid k → ℝ := fun s => fderiv ℝ f s (EuclideanSpace.single i (1 : ℝ)) with hg
      have hloc : LocallyIntegrable g (volume : Measure (Euclid k)) := by
        refine (locallyIntegrable_const ((L : ℝ) * ‖EuclideanSpace.single i (1 : ℝ)‖)).mono
          ((measurable_fderiv_apply_const ℝ f _).aestronglyMeasurable)
          (Eventually.of_forall fun s => ?_)
        rw [Real.norm_eq_abs (_ * _), abs_of_nonneg (by positivity)]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _))
      -- Lebesgue differentiation: `⨍_{B(x, r)} |g - g x| → 0` as `r → 0`, for a.e. `x`
      filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hloc 1]
        with x hx
      have havg := hx (fun _ => x) (fun n => (φ n).rOut) hδ
        (Eventually.of_forall fun n => mem_closedBall_self (by simpa using (φ n).rOut_pos.le))
      -- `0 ≤ ρ n (x - ·) ≤ 2 ^ d / |B(x, rOut)|`, supported in `B(x, rOut)`, with integral `1`
      have key := tendsto_integral_smul_of_tendsto_average_norm_sub ((2 : ℝ) ^ d) havg
        (g := fun n y => ρ n (x - y))
        (Eventually.of_forall fun n => hloc.integrableOn_isCompact (isCompact_closedBall _ _))
        (tendsto_const_nhds.congr fun n => by
          rw [integral_sub_left_eq_self (ρ n) volume x, hρint n])
        (Eventually.of_forall fun n y hy => by
          have hy' : x - y ∈ ball (0 : Euclid k) (φ n).rOut := hρsupp n hy
          rw [mem_ball, dist_zero_right] at hy'
          rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
          exact hy'.le)
        (Eventually.of_forall fun n y => by
          rw [abs_of_nonneg (hρ0 n _), hvol x _ (φ n).rOut_pos.le, hrOut n]
          calc ρ n (x - y) ≤ 1 / ((φ n).rIn ^ d * c) := hρle n _
            _ = 2 ^ d / ((2 * (φ n).rIn) ^ d * c) := by
              rw [mul_pow]
              field_simp)
      refine key.congr fun n => ?_
      rw [hB1, ← integral_sub_left_eq_self (fun y => ρ n (x - y) • g y) volume x]
      simp only [sub_sub_cancel, smul_eq_mul, hg]
    filter_upwards [ae_all_iff.2 hDi] with x hx
    -- step 8: `‖T‖ ≤ ∑ᵢ |T eᵢ|`, so convergence on the basis gives convergence in norm
    have hbound : ∀ T : Euclid k →L[ℝ] ℝ, ‖T‖ ≤ ∑ i, ‖T (EuclideanSpace.single i (1 : ℝ))‖ := by
      intro T
      refine ContinuousLinearMap.opNorm_le_bound T (Finset.sum_nonneg fun i _ => norm_nonneg _)
        fun w => ?_
      have hw : w = ∑ i, w i • EuclideanSpace.single i (1 : ℝ) := by
        conv_lhs => rw [← (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr w]
        simp
      calc ‖T w‖ = ‖∑ i, w i • T (EuclideanSpace.single i (1 : ℝ))‖ := by
            conv_lhs => rw [hw]
            simp [map_sum, map_smul]
        _ ≤ ∑ i, ‖w i • T (EuclideanSpace.single i (1 : ℝ))‖ := norm_sum_le _ _
        _ = ∑ i, ‖w i‖ * ‖T (EuclideanSpace.single i (1 : ℝ))‖ := by simp
        _ ≤ ∑ i, ‖w‖ * ‖T (EuclideanSpace.single i (1 : ℝ))‖ := by
            gcongr with i
            exact PiLp.norm_apply_le w i
        _ = (∑ i, ‖T (EuclideanSpace.single i (1 : ℝ))‖) * ‖w‖ := by
            rw [Finset.sum_mul]; simp [mul_comm]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => hbound _) ?_
    have : Tendsto (fun n => ∑ i : Fin k, ‖(fderiv ℝ (fs n) x - fderiv ℝ f x)
        (EuclideanSpace.single i (1 : ℝ))‖) atTop (𝓝 (∑ i : Fin k, (0 : ℝ))) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      have := tendsto_iff_norm_sub_tendsto_zero.1 (hx i)
      simpa using this
    simpa using this
```

## Key steps

1. Normalized bumps ρ_n = φ_n/∫φ_n supported in B(0, 2/(n+2)) with 0 ≤ ρ_n ≤ 2^d/λ(B(x, 2/(n+2))) and ∫ρ_n = 1; f_n := ρ_n ⋆ f.
2. f_n is C^∞ (contDiff_convolution_left), L-Lipschitz (sibling mollify_lipschitz) and |f_n − f| ≤ 2L/(n+2) (dist_convolution_le).
3. Df_n(x)e_i = ∫ρ_n(t)Df(x − t)e_i dt (sibling mollify_fderiv) → Df(x)e_i a.e. by Lebesgue differentiation for the doubling Lebesgue measure.
4. ‖T‖ ≤ Σ_i |Te_i| upgrades convergence on the basis to operator-norm convergence a.e.

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git -C SNAPSHOT/mathlib rev-parse HEAD (25730c7c); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean workspace GMT/Ch07/Submission.lean (identical); git log -1 of the workspace (b4d606db)`
- `rg -n -i 'piola|mollif|weak.?contin|null.?lagrang|minor' SNAPSHOT/project -g '*.lean' (no relevant match: only LpSeminorm imports and a Hölder-seminorm comment in Ch04/Ch05); rg -n -i jacobian SNAPSHOT/project/GMT/Ch02/Contract.lean SNAPSHOT/project/GMT/Ch03/Contract.lean SNAPSHOT/project/GMT/Ch07/Contract.lean (only the areaJacobian/coareaJacobian definitions of Ch02/Ch03 and the area/coarea formulas; nothing in Ch07)`
- `rg -l 'dimred_mbl_dt_lp_jc|dor_lmb_fcd_jwc|cmcs_ls_mollify|cmr_cc_det' SNAPSHOT/project (no match; these declarations exist only in DAG candidate commits)`
- `rg -n '^(theorem|lemma) [A-Za-z_.]*NAME' SNAPSHOT/mathlib/Mathlib for NAME in integral_lineDeriv_mul_eq, norm_fderiv_le_of_lipschitz, measurable_fderiv_apply_const, contDiff_convolution_left, hasFDerivAt_convolution_left, convolutionExists_left, ae_tendsto_average_norm_sub, tendsto_integral_smul_of_tendsto_average_norm_sub, dist_convolution_le, extDeriv_pullback, extDeriv_apply, det_succ_row_zero, tendsto_integral_filter_of_dominated_convergence, ae_differentiableAt, induction_dense, exists_contDiff_support_eq_eq_one_iff, lipschitzWith_of_hasCompactSupport, exists_isCompact_sdiff_lt, exists_isOpen_sdiff_lt, bdd_mul, addHaar_real_closedBall' (all found); ae_convolution_tendsto_right_of_locallyIntegrable and det_le (found in the snapshot, see next query)`
- `lake env lean /tmp/jc-decomp2/probe/Probe.lean importing only GMT.Ch07.Submission: #check ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable and Matrix.det_le (Unknown constant: outside the frozen import closure); #check IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub, tendsto_integral_smul_of_tendsto_average_norm_sub, LipschitzWith.integral_lineDeriv_mul_eq, MemLp.induction_dense, HasCompactSupport.hasFDerivAt_convolution_left, extDeriv_pullback (available)`
- `python3 scans of RUN/dag.json: nodes whose id/title/statement mention Jacobian weak continuity; status, candidate_commit, updated_at and lean_statement of the eleven child names under the runtime rule _accepted_checkpoint (six reused names accepted with byte-identical types; twin mollify_fderiv accepted at 01:41:31Z, the four other twins comparing/speculative-ready); collision scan for dimred_mbl_dt_lp_jc_* (unused); RUN/issue-workers.json (mode broker-owned-issue-polling; worker for issue 7020 started 2026-10-14T00:19:09Z)`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose depth guard and name checks, _existing_lean_name_problem, _accepted_checkpoint, _solve_children reuse by lean_name), store.py (refresh, update: accepted is permanent), parallel.py (enabled, RefreshLock), scripts/swarm-run-issue.py, and workspace .humanize/swarm-configs/c8e45649089f4d62adf9de1e95c664c3.json (github_shared_issue_runtime true, max_depth 6, max_children 12, max_nodes 5000, decomposition_attempts 5)`
- `git show <commit>:GMT/Ch07/Submission.lean for accepted candidates fee01ff86c, 2c87728a, 7ba02a03, c6153c4c, 52b9c39c, 13966862 (reused proofs byte-identical to the compiled chain) and ebbe3de7 (accepted twin of mollify_fderiv; proof body identical to the embedded realization)`
- `lake env lean /tmp/jc-decomp2/lean/FinalCheck.lean (eleven child proofs, assembly_from_children, Submission.dimred_mbl_dt_lp_jacobian_weak_continuity with its frozen type, exact-type checks; exit 0, no sorry, axioms propext/Classical.choice/Quot.sound); lake env lean /tmp/jc-decomp2/challenges/AllChallenges.lean (prefix from verifier contract_scope; exit 0, only sorry warnings); both validate_lean_statement implementations on all eleven types; dependency cross-check of Submission.* references against depends_on`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-b372f37aac/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-b372f37aac/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/c8e45649089f4d62adf9de1e95c664c3.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/parallel.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/scripts/swarm-run-issue.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/jc-decomp2/lean/FinalCheck.lean`
- `/tmp/jc-decomp2/challenges/AllChallenges.lean`
- `/tmp/jc-decomp2/probe/Probe.lean`

Pins match: project b4d606db and Mathlib 25730c7c, and the workspace Submission is byte-identical to the frozen Ch07 contract. The snapshot project contains no weak-continuity, Piola, mollification or minor-expansion lemma. Its only Jacobians are the Ch02/Ch03 area/coarea Jacobian definitions, so the needed obligations come from the DAG. Six comparator-accepted DAG declarations with exactly the needed types are reused verbatim: cmr_cc_det_covector_exists, dor_lmb_fcd_jwc_covector_det_expansion, dor_lmb_fcd_jwc_weak_star_l1_upgrade, dor_lmb_fcd_jwc_piola_identity, cmcs_ls_mollify_lipschitz and dor_lmb_fcd_jwc_minor_measurable_bound. All six were accepted before this attempt's shared-DAG refresh (01:30:20Z), so the earlier 'reserved by active DAG node' rejection no longer applies. The five remaining links get fresh, unused dimred_mbl_dt_lp_jc_* names, because their twins were unaccepted at that refresh. Every Mathlib lemma cited by the child proofs exists in the snapshot and is available after import GMT.Ch07.Submission. ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable and Matrix.det_le exist in the snapshot but are outside the import closure, so the child proofs use in-closure substitutes. All eleven child proofs plus the parent, stated with its exact frozen type, compile together with no sorry and only the standard axioms. Every type elaborates in the comparator's challenge scope.
