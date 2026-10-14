# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.mean_value-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.mean_value-a1.deriv_under_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof, differentiation under the integral sign via hasDerivAt_integral_of_dominated_loc_of_deriv_le. The neighbourhood of s, the constants and all hypotheses are made explicit here.

Fix s with |s|r < R. Write F(σ, y) := h(x − σy)·g(|y|²) and F'(σ, y) := −(Dh(x − σy)(y)·g(|y|²)).

1. (A neighbourhood of s.) Let δ := (R − |s|r)/(2r) > 0 and R₁ := (|s| + δ)r = |s|r + (R − |s|r)/2 < R. Let J := (s − δ, s + δ), the ball of radius δ about s. For σ ∈ J, |σ| ≤ |s| + |σ − s| < |s| + δ, hence |σ|r < R₁ < R.

2. (Geometry.) |(x − σy) − x| = |σ||y|. Hence:
(a) if |σ|r < R and |y| ≤ r, then x − σy ∈ closedBall(x, R) ⊆ U;
(b) if σ ∈ J and |y| ≤ r, then |σ||y| ≤ (|s| + δ)r = R₁, i.e. x − σy ∈ closedBall(x, R₁).

3. (g beyond r.) If |y| ≥ r then |y|² ≥ r² (as r > 0), so g(|y|²) = 0. Hence F(σ, y) = 0 and F'(σ, y) = 0 for every σ.

4. (Constants.) U is open and h is C¹ on U. So h is continuous and differentiable at every point of U, and Dh is continuous on U (ContDiffOn.continuousOn_fderiv_of_isOpen).
- closedBall(x, R₁) ⊆ closedBall(x, R) ⊆ U is compact, so ‖Dh‖ has a bound A₁ on closedBall(x, R₁) (IsCompact.exists_bound_of_continuousOn).
- Let γ be a bound for |g| on the compact interval [0, r²]. Then |g(|y|²)| ≤ γ for all y: if |y| ≤ r then |y|² ∈ [0, r²]; otherwise g(|y|²) = 0 ≤ |g(0)| ≤ γ.

5. (Continuity in y.) Let σ satisfy |σ|r < R. Then y ↦ F(σ, y) is continuous on ℝⁿ:
- at y₀ with |y₀| ≤ r: x − σy₀ ∈ U by step 2(a), so h is continuous at x − σy₀. Since y ↦ x − σy is continuous, y ↦ h(x − σy) is continuous at y₀, and so is its product with the continuous map y ↦ g(|y|²);
- at y₀ with |y₀| > r: F(σ, ·) vanishes on the open set {|y| > r} ∋ y₀ by step 3.
The same argument, using continuity of Dh at x − s y₀ and of (L, y) ↦ L y, shows that y ↦ F'(s, y) is continuous. In particular F(σ, ·) for σ ∈ J and F'(s, ·) are a.e.-strongly measurable. Moreover F(s, ·) vanishes outside the compact set closedBall(0, r), so it is integrable (Continuous.integrable_of_hasCompactSupport).

6. (Pointwise derivative.) Let y ∈ ℝⁿ and σ ∈ J.
- If |y| < r: x − σy ∈ U by step 2(a) with step 1, so h is differentiable there. The map σ ↦ x − σy has derivative −y. By the chain rule, σ ↦ h(x − σy) has derivative Dh(x − σy)(−y) = −Dh(x − σy)(y). Multiplying by the constant g(|y|²) gives derivative F'(σ, y).
- If |y| ≥ r: σ ↦ F(σ, y) is identically 0 by step 3, with derivative 0 = F'(σ, y).

7. (Domination.) For σ ∈ J and every y, |F'(σ, y)| ≤ bound(y) := A₁·r·γ·1_{closedBall(0,r)}(y).
- If |y| ≤ r: |Dh(x − σy)(y)| ≤ ‖Dh(x − σy)‖·|y| ≤ A₁r, by step 2(b) and the choice of A₁; and |g(|y|²)| ≤ γ.
- If |y| > r: F'(σ, y) = 0.
The bound is integrable, being a constant times the indicator of closedBall(0, r), which has finite Lebesgue measure.

8. (Conclusion.) Apply hasDerivAt_integral_of_dominated_loc_of_deriv_le with the neighbourhood J of s; steps 5–7 supply its hypotheses. It gives that σ ↦ ∫ F(σ, y) dy = M(σ) has derivative ∫ F'(s, y) dy at s, and ∫ F'(s, y) dy = −∫ Dh(x − s y)(y)·g(|y|²) dy (integral_neg). ∎

Formalization appendix. Compiled at decomposition time inside namespace GMT.Ch07 under the frozen header, with no extra import (Lean 4.35.0-rc3, Mathlib 25730c7c). #print axioms reports propext, Classical.choice, Quot.sound. If a transcription detail fails, the numbered proof above is authoritative.

theorem Submission.dorag_ha_mv_deriv_under_integral : ∀ (n : ℕ) (U : Set (Euclid n)) (h : Euclid n → ℝ) (x : Euclid n) (r R : ℝ) (g : ℝ → ℝ), IsOpen U → ContDiffOn ℝ 1 h U → closedBall x R ⊆ U → 0 < r → Continuous g → (∀ t : ℝ, r ^ 2 ≤ t → g t = 0) → ∀ s : ℝ, |s| * r < R → HasDerivAt (fun σ : ℝ => ∫ y : Euclid n, h (x - σ • y) * g (‖y‖ ^ 2)) (-∫ y : Euclid n, fderiv ℝ h (x - s • y) y * g (‖y‖ ^ 2)) s := by
  intro n U h x r R g hU hh hRU hr hg hgr s hs
  set δ : ℝ := (R - |s| * r) / (2 * r) with hδ
  have hδpos : 0 < δ := div_pos (by linarith) (by positivity)
  set R₁ : ℝ := (|s| + δ) * r with hR₁
  have hR₁R : R₁ < R := by
    have : R₁ = |s| * r + (R - |s| * r) / 2 := by
      simp only [hR₁, hδ]; field_simp
    rw [this]; linarith
  have hgz : ∀ y : Euclid n, r ≤ ‖y‖ → g (‖y‖ ^ 2) = 0 := fun y hy =>
    hgr _ (pow_le_pow_left₀ hr.le hy 2)
  have hnorm : ∀ (σ : ℝ) (y : Euclid n), ‖x - σ • y - x‖ = |σ| * ‖y‖ := by
    intro σ y; rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
  have hmemU : ∀ σ : ℝ, |σ| * r < R → ∀ y : Euclid n, ‖y‖ ≤ r → x - σ • y ∈ U := by
    intro σ hσ y hy
    apply hRU
    rw [mem_closedBall, dist_eq_norm, hnorm]
    nlinarith [abs_nonneg σ]
  have hball : ∀ σ ∈ ball s δ, |σ| < |s| + δ := by
    intro σ hσ
    rw [mem_ball, Real.dist_eq] at hσ
    have := abs_sub_abs_le_abs_sub σ s
    linarith
  have hball' : ∀ σ ∈ ball s δ, |σ| * r < R := by
    intro σ hσ
    have := hball σ hσ
    have : |σ| * r < (|s| + δ) * r := mul_lt_mul_of_pos_right this hr
    linarith
  have hmemK : ∀ σ ∈ ball s δ, ∀ y : Euclid n, ‖y‖ ≤ r → x - σ • y ∈ closedBall x R₁ := by
    intro σ hσ y hy
    rw [mem_closedBall, dist_eq_norm, hnorm]
    have := hball σ hσ
    calc |σ| * ‖y‖ ≤ (|s| + δ) * r := by
          apply mul_le_mul this.le hy (norm_nonneg _) (by positivity)
      _ = R₁ := rfl
  have hhc : ∀ z ∈ U, ContinuousAt h z := fun z hz =>
    hh.continuousOn.continuousAt (hU.mem_nhds hz)
  have hdc : ContinuousOn (fderiv ℝ h) U := hh.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ h z := fun z hz =>
    (hh.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  obtain ⟨A₁, hA₁⟩ := (isCompact_closedBall x R₁).exists_bound_of_continuousOn
    (hdc.mono ((closedBall_subset_closedBall hR₁R.le).trans hRU))
  obtain ⟨γ, hγ⟩ := (isCompact_Icc (a := (0:ℝ)) (b := r ^ 2)).exists_bound_of_continuousOn
    hg.continuousOn
  have hgγ : ∀ y : Euclid n, ‖g (‖y‖ ^ 2)‖ ≤ γ := by
    intro y
    by_cases hy : ‖y‖ ≤ r
    · exact hγ _ ⟨by positivity, pow_le_pow_left₀ (norm_nonneg _) hy 2⟩
    · rw [hgz y (le_of_not_ge hy), norm_zero]
      exact (norm_nonneg _).trans (hγ 0 ⟨le_rfl, by positivity⟩)
  have hFcont : ∀ σ : ℝ, |σ| * r < R →
      Continuous (fun y : Euclid n => h (x - σ • y) * g (‖y‖ ^ 2)) := by
    intro σ hσ
    rw [continuous_iff_continuousAt]
    intro y₀
    by_cases hy₀ : ‖y₀‖ ≤ r
    · have h1 : ContinuousAt (fun y : Euclid n => h (x - σ • y)) y₀ :=
        ContinuousAt.comp (f := fun y : Euclid n => x - σ • y) (hhc _ (hmemU σ hσ y₀ hy₀)) (by fun_prop)
      exact h1.mul (by fun_prop)
    · push Not at hy₀
      have : (fun y : Euclid n => h (x - σ • y) * g (‖y‖ ^ 2)) =ᶠ[𝓝 y₀] fun _ => 0 := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy₀] with y hy
        rw [hgz y (le_of_lt hy), mul_zero]
      exact continuousAt_const.congr this.symm
  have hF'cont : Continuous (fun y : Euclid n => -(fderiv ℝ h (x - s • y) y * g (‖y‖ ^ 2))) := by
    rw [continuous_iff_continuousAt]
    intro y₀
    by_cases hy₀ : ‖y₀‖ ≤ r
    · have h1 : ContinuousAt (fun y : Euclid n => fderiv ℝ h (x - s • y)) y₀ :=
        ContinuousAt.comp (f := fun y : Euclid n => x - s • y)
          (hdc.continuousAt (hU.mem_nhds (hmemU s hs y₀ hy₀))) (by fun_prop)
      exact ((h1.clm_apply continuousAt_id).mul (by fun_prop)).neg
    · push Not at hy₀
      have : (fun y : Euclid n => -(fderiv ℝ h (x - s • y) y * g (‖y‖ ^ 2))) =ᶠ[𝓝 y₀]
          fun _ => 0 := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy₀] with y hy
        rw [hgz y (le_of_lt hy), mul_zero, neg_zero]
      exact continuousAt_const.congr this.symm
  have hsupp : ∀ σ : ℝ, HasCompactSupport (fun y : Euclid n => h (x - σ • y) * g (‖y‖ ^ 2)) := by
    intro σ
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) r) fun y hy => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    rw [hgz y hy.le, mul_zero]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun σ (y : Euclid n) => h (x - σ • y) * g (‖y‖ ^ 2))
    (F' := fun σ (y : Euclid n) => -(fderiv ℝ h (x - σ • y) y * g (‖y‖ ^ 2)))
    (x₀ := s) (bound := (closedBall (0 : Euclid n) r).indicator fun _ => A₁ * r * γ)
    (ball_mem_nhds s hδpos)
    (eventually_of_mem (ball_mem_nhds s hδpos) fun σ hσ =>
      (hFcont σ (hball' σ hσ)).aestronglyMeasurable)
    ((hFcont s hs).integrable_of_hasCompactSupport (hsupp s))
    hF'cont.aestronglyMeasurable
    (Eventually.of_forall fun y σ hσ => by
      by_cases hy : ‖y‖ ≤ r
      · rw [indicator_of_mem (by rwa [mem_closedBall, dist_zero_right])]
        rw [norm_neg, norm_mul]
        have h1 : ‖fderiv ℝ h (x - σ • y) y‖ ≤ A₁ * r :=
          ((fderiv ℝ h (x - σ • y)).le_opNorm y).trans
            (mul_le_mul (hA₁ _ (hmemK σ hσ y hy)) hy (norm_nonneg _)
              ((norm_nonneg _).trans (hA₁ _ (hmemK σ hσ y hy))))
        exact mul_le_mul h1 (hgγ y) (norm_nonneg _) (by nlinarith [norm_nonneg (fderiv ℝ h (x - σ • y) y)])
      · rw [hgz y (le_of_not_ge hy), mul_zero, neg_zero, norm_zero]
        rw [indicator_of_notMem (by rwa [mem_closedBall, dist_zero_right])])
    ((integrableOn_const (measure_closedBall_lt_top (x := (0 : Euclid n)) (r := r)).ne).integrable_indicator
      measurableSet_closedBall)
    (Eventually.of_forall fun y σ hσ => by
      by_cases hy : ‖y‖ < r
      · have hd := (hdiff _ (hmemU σ (hball' σ hσ) y hy.le)).hasFDerivAt
        have hγ' : HasDerivAt (fun σ : ℝ => x - σ • y) (-y) σ := by
          simpa using (hasDerivAt_id σ).smul_const y |>.const_sub x
        have := (hd.comp_hasDerivAt σ hγ').mul_const (g (‖y‖ ^ 2))
        simpa [map_neg, neg_mul] using this
      · push Not at hy
        have h0 : (fun σ : ℝ => h (x - σ • y) * g (‖y‖ ^ 2)) = fun _ => 0 := by
          funext σ; rw [hgz y hy, mul_zero]
        rw [h0, hgz y hy, mul_zero, neg_zero]
        exact hasDerivAt_const σ 0)
  simpa [integral_neg] using key.2

## Key steps

1. Choose δ = (R − |s|r)/(2r) and R₁ = (|s| + δ)r < R; for σ ∈ (s − δ, s + δ) and |y| ≤ r, x − σy ∈ closedBall(x, R₁) ⊆ U.
2. F(σ, y) = h(x − σy)g(|y|²) and its σ-derivative vanish for |y| ≥ r; for |σ|r < R they are continuous in y (h and Dh are continuous at points of U), hence measurable, and F(s, ·) is integrable.
3. Chain rule: ∂_σ F(σ, y) = −Dh(x − σy)(y)·g(|y|²) for all y and all σ near s.
4. Uniform bound A₁·r·γ·1_{closedBall(0,r)}, with A₁ = sup ‖Dh‖ on closedBall(x, R₁) and γ = sup |g| on [0, r²]; apply hasDerivAt_integral_of_dominated_loc_of_deriv_le, then integral_neg.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean && cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (IDENTICAL)`
- `grep -rn 'theorem integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable|theorem integral_lineDeriv_mul_eq|theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le|theorem integral_hasDerivAt_right|theorem HasFDerivAt.norm_sq|theorem hasStrictFDerivAt_norm_sq|theorem tsupport_eq|theorem iteratedFDeriv_two_apply|theorem exists_hasDerivAt_eq_slope|theorem constant_of_derivWithin_zero|theorem tendsto_integral_of_dominated_convergence|theorem cthickening_closedBall|theorem comp_right_fderiv|theorem fderiv_comp_sub' <snapshot>/mathlib/Mathlib`
- `grep -rn 'iteratedFDeriv_comp_add_left|iteratedFDeriv_comp_right|iteratedFDeriv_comp_sub|exists_cthickening_subset_open|lipschitzWith_of_hasCompactSupport|measurePreserving_sub_left|iteratedFDeriv_const_smul|ContinuousLinearEquiv.iteratedFDerivWithin_comp_right|inner_single_right|support_fderiv_subset|fderiv_comp_add_left|addHaar_ball_center' <snapshot>/mathlib/Mathlib`
- `sed -n 1,60p and 215,250p Analysis/Calculus/LineDeriv/IntegrationByParts.lean; sed -n 280,310p Analysis/Calculus/ParametricIntegral.lean; sed -n 940,985p Analysis/Calculus/ContDiff/FTaylorSeries.lean; sed -n 430,500p Analysis/Calculus/ContDiff/Basic.lean; sed -n 190,215p Analysis/InnerProductSpace/Calculus.lean`
- `grep -n '^theorem|^lemma|^def' Analysis/InnerProductSpace/Laplacian.lean; ls Analysis/InnerProductSpace/Harmonic/; grep -rn -E 'theorem .*(mean|Mean)' Analysis/InnerProductSpace/Harmonic/*.lean; grep -n '^theorem' Analysis/Complex/Harmonic/MeanValue.lean`
- `grep -rn -i -E 'mean_value|meanValue|mean value|laplacian|harmonic|integral_mul_fderiv|lineDeriv_mul' <snapshot>/project/GMT; grep -rln -i -E 'mean_value|meanValue|laplacian|harmonic' .lake/packages/simongmt; grep -n -E '^(theorem|lemma|def) ' SimonGMT/Chapter08/DistributionalConstancy.lean Chapter05/HarmonicEnergy.lean Chapter05/Basic.lean Chapter04/FirstVariation.lean`
- `sed -n 336,386p and 540,640p verifier/gmt-compare.py (child scope replay; only Contract.lean and build inputs are frozen, new Lean files allowed under GMT/Ch07/); git show <ref>:GMT/Ch07/Submission.lean | grep '^import' over all 957 refs (accepted branches add Mathlib/SimonGMT imports)`
- `python3 -I scan of dag.json (325 nodes) and nodes/*/*.json lean_name fields (566 distinct names) for the 6 proposed dorag_ha_mv_* names: no collision`
- `lean (toolchains/lean-4.35.0-rc3-linux, LEAN_PATH = workspace .lake builds) /tmp/mv-decomp/Scope.lean, Children.lean, Assembly.lean, Flux.lean, AffineTest.lean, RadialGreenTest.lean, DerivTest.lean, BallTest.lean, Avail.lean, AllChildren.lean, AllChildrenClean.lean (#print axioms)`
- `ls lake-packages-25730c7c/mathlib/.lake/build/lib/lean/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.olean (present)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Harmonic/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Equiv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter05/HarmonicEnergy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-9f82487345/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/.lake/build/lib/lean/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.olean`
- `/tmp/mv-decomp/Children.lean`
- `/tmp/mv-decomp/Assembly.lean`
- `/tmp/mv-decomp/Flux.lean`
- `/tmp/mv-decomp/AffineTest.lean`
- `/tmp/mv-decomp/RadialGreenTest.lean`
- `/tmp/mv-decomp/DerivTest.lean`
- `/tmp/mv-decomp/BallTest.lean`
- `/tmp/mv-decomp/Avail.lean`
- `/tmp/mv-decomp/AllChildrenClean.lean`

Snapshot and scope:
- The snapshot pins project b4d606d and Mathlib 25730c7c.
- GMT/Ch07/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, so child types are checked in exactly the comparator scope.

Nothing reusable exists for this node:
- The project snapshot has none of the needed lemmas; Ch05 HarmonicApproximationLemma is only a Prop.
- SimonGMT has no mean value, Green or radial-potential lemma; Chapter05/Basic.lean only re-exports HarmonicOn vocabulary.
- Mathlib's only harmonic mean value theorem is HarmonicOnNhd.circleAverage_eq on ℂ (Complex/Harmonic/MeanValue.lean).
- Laplacian.lean has no composition-on-the-right lemma.
So the general-n argument must be built from the following pinned Mathlib lemmas.

Pinned Mathlib lemmas used by the children:
- integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (LineDeriv/IntegrationByParts.lean:226). It requires each factor to be differentiable only on the other's tsupport, which removes the parent's cutoff. The frozen header does not import it, so green_identity adds the import; the olean is present in the comparator package tree.
- hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286).
- Continuous.integral_hasStrictDerivAt, contDiff_one_iff_deriv, hasStrictFDerivAt_norm_sq / contDiff_norm_sq (InnerProductSpace/Calculus.lean:197,140).
- iteratedFDeriv_two_apply and iteratedFDeriv_comp_add_left (FTaylorSeries.lean:948,958).
- ContinuousLinearEquiv.iteratedFDerivWithin_comp_right (ContDiff/Basic.lean:436) and ContinuousLinearEquiv.comp_right_fderiv (FDeriv/Equiv.lean:227).
- fderiv_comp_add_left (FDeriv/Add.lean:867) and support_fderiv_subset (FDeriv/Const.lean:379).
- exists_hasDerivAt_eq_slope (Deriv/MeanValue.lean:123).
- IsCompact.exists_cthickening_subset_open (Thickening.lean:426) and cthickening_closedBall (Ball/Pointwise.lean:318).
- tendsto_integral_of_dominated_convergence (DominatedConvergence.lean:57), Measure.measurePreserving_sub_left, MeasurePreserving.setIntegral_preimage_emb and Measure.addHaar_ball_center (EqHaar.lean:418).
All except the IBP lemma are reachable from the frozen imports, as Avail.lean confirmed.

Comparator and names:
- gmt-compare.py freezes only Contract.lean and the build inputs, and allows new Lean files under GMT/Ch07/.
- The six dorag_ha_mv_* names are unreserved: no collision among the 566 lean_names in dag.json and the node files.

Lean checks:
- All six child types elaborate in comparator scope.
- Complete proofs of all six children compile, and so does the parent assembly of the exact frozen dorag_ha_mean_value type (AllChildrenClean.lean).
- Axioms are only propext, Classical.choice and Quot.sound.
