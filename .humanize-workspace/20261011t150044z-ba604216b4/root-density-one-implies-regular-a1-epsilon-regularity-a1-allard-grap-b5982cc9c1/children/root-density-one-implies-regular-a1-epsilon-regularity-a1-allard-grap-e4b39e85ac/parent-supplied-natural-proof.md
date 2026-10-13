# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_height-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_height-a1.radial_cutoff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 1 (the cut-off), i.e. the choice "ζ ≡ 1 in B_{ρ/2}(0), ζ ≡ 0 outside B_ρ(0) and |∇ζ| ≤ 3/ρ" at the end of Simon's proof of Ch. 5, Lemma 2.1 (book/chapter-05.txt, lines 260–262). Notation: ‖·‖ is the Euclidean norm, B̆ an open ball, B̄ a closed ball.

1. Admissible profiles. Call χ : ℝ → ℝ admissible if (χ1) χ is C¹ (or smoother); (χ2) 0 ≤ χ ≤ 1; (χ3) χ(σ) = 1 for σ ≤ 1/2; (χ4) χ(σ) = 0 for σ ≥ 1; (χ5) |χ(σ) − χ(τ)| ≤ 3|σ − τ| for all σ, τ ∈ ℝ.
2. An admissible profile exists (the cubic of the parent proof). Let χ₀(u) := 1 − 3u² + 2u³. Then χ₀(0) = 1, χ₀(1) = 0 and χ₀'(u) = −6u(1 − u), so χ₀'(0) = χ₀'(1) = 0, χ₀ is nonincreasing on [0, 1] (hence 0 ≤ χ₀ ≤ 1 there) and |χ₀'(u)| = 6u(1 − u) ≤ 3/2 on [0, 1]. Put χ(σ) := 1 for σ ≤ 1/2, χ(σ) := χ₀(2σ − 1) for 1/2 ≤ σ ≤ 1, χ(σ) := 0 for σ ≥ 1 (the definitions agree at σ = 1/2 and σ = 1). On each of the open intervals (−∞, 1/2), (1/2, 1), (1, ∞) χ is a polynomial with derivative 0, 2χ₀'(2σ − 1), 0 respectively. At σ = 1/2 the left difference quotients vanish and (χ(1/2 + h) − 1)/h = −12h + 16h² → 0 as h ↓ 0; at σ = 1 the right difference quotients vanish and (χ(1 − h) − 0)/(−h) = −12h + 16h² → 0 as h ↓ 0. Hence χ is differentiable on ℝ with χ'(σ) = 2χ₀'(2σ − 1) = −12(2σ − 1)(2 − 2σ) for σ ∈ [1/2, 1] and χ'(σ) = 0 otherwise; χ' is continuous (it vanishes at both junctions), so χ is C¹, and |χ'| ≤ 2 · 3/2 = 3. Thus (χ1)–(χ4) hold, and (χ5) follows from |χ'| ≤ 3 by the mean value theorem.
   Remark (an alternative admissible profile, C^∞; it is the one used in the Lean appendix). Let S = Real.smoothTransition (C^∞, 0 ≤ S ≤ 1, S = 0 on (−∞, 0], S = 1 on [1, ∞)) and g(t) := S(12(t − 1/2))·S(12(1 − t)). Then g is C^∞, 0 ≤ g ≤ 1, g = 0 for t ≤ 1/2 and for t ≥ 1, and g = 1 on [7/12, 11/12], so c := ∫_{1/2}^{1} g ≥ 1/3 > 0. Put χ(σ) := 1 − c⁻¹∫_{1/2}^{σ} g. By the fundamental theorem of calculus χ is C^∞ with χ' = −c⁻¹g, so |χ'| ≤ c⁻¹ ≤ 3 and χ is 3-Lipschitz; χ = 1 on (−∞, 1/2], χ = 0 on [1, ∞) (as ∫_{1/2}^{σ} g = c for σ ≥ 1), and 0 ≤ χ ≤ 1 because 0 ≤ ∫_{1/2}^{σ} g ≤ c.
3. Definition. Fix an admissible χ and put ζ(x) := χ(‖x − ξ‖/r).
4. Values and plateau. 0 ≤ ζ ≤ 1 by (χ2). If x ∈ B̄_{r/2}(ξ) then ‖x − ξ‖/r ≤ 1/2, so ζ(x) = 1 by (χ3).
5. Support. If ‖x − ξ‖ ≥ r then ‖x − ξ‖/r ≥ 1 and ζ(x) = 0 by (χ4). Hence {ζ ≠ 0} ⊆ B̆_r(ξ), and tsupport ζ = closure{ζ ≠ 0} ⊆ closure B̆_r(ξ) ⊆ B̄_r(ξ), the closed ball being closed.
6. ζ is C¹. The open sets O₁ := B̆_{r/2}(ξ) and O₂ := ℝ^P \ {ξ} cover ℝ^P (ξ ∈ O₁ because r > 0). On O₁, ζ ≡ 1 by step 4, so ζ is C¹ near every point of O₁. On O₂ the map y ↦ ‖y − ξ‖/r is C^∞ (the Euclidean norm is smooth on ℝ^P \ {0}), so ζ = χ ∘ (‖· − ξ‖/r) is C¹ near every point of O₂ by the chain rule. Being C¹ is a local property, so ζ is C¹ on ℝ^P (C^∞ if χ is C^∞).
7. Gradient bound. For y, z ∈ ℝ^P, (χ5) and the reverse triangle inequality give |ζ(y) − ζ(z)| ≤ (3/r)·|‖y − ξ‖ − ‖z − ξ‖| ≤ (3/r)·‖y − z‖, so ζ is (3/r)-Lipschitz. For every x and h, |Dζ(x)h| = lim_{t↓0} |ζ(x + th) − ζ(x)|/t ≤ (3/r)‖h‖, i.e. ‖Dζ(x)‖ ≤ 3/r (Mathlib: norm_fderiv_le_of_lipschitz).
8. Steps 4–7 give all assertions. (For P = 0 the space is {ξ} ⊆ O₁ and everything is immediate.) ∎

Appendix — machine-checked Lean realization (verified during decomposition: Lean v4.35.0-rc3, Mathlib 25730c7c, inside `namespace GMT.Ch07` of the frozen Submission scope; `#print axioms` gives [propext, Classical.choice, Quot.sound]; the numbered argument above is the proof, this block only records one verified formalization of it):
```lean
open scoped NNReal in
theorem Submission.dorag_th_radial_cutoff : ∀ (P : ℕ) (ξ : Euclid P) (r : ℝ), 0 < r → ∃ ζ : Euclid P → ℝ, ContDiff ℝ 1 ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ (∀ x ∈ closedBall ξ (r / 2), ζ x = 1) ∧ tsupport ζ ⊆ closedBall ξ r ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ 3 / r := by
  intro P ξ r hr
  obtain ⟨φ, hφ_smooth, hφ_bounds, hφ_one, hφ_zero, hφ_lip⟩ : ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧
      (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧ (∀ t, t ≤ 1 / 2 → φ t = 1) ∧ (∀ t, 1 ≤ t → φ t = 0) ∧
      LipschitzWith 3 φ := by
    set g : ℝ → ℝ := fun t =>
      Real.smoothTransition (12 * (t - 1 / 2)) * Real.smoothTransition (12 * (1 - t)) with hg_def
    have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
      have h₁ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 12 * (t - 1 / 2) := by fun_prop
      have h₂ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 12 * (1 - t) := by fun_prop
      exact (Real.smoothTransition.contDiff.comp h₁).mul (Real.smoothTransition.contDiff.comp h₂)
    have hg_cont : Continuous g := hg_smooth.continuous
    have hg_int : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
      hg_cont.intervalIntegrable a b
    have hg_nonneg : ∀ t, 0 ≤ g t := fun t =>
      mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
    have hg_le_one : ∀ t, g t ≤ 1 := fun t =>
      (mul_le_of_le_one_left (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)).trans
        (Real.smoothTransition.le_one _)
    have hg_left : ∀ t, t ≤ 1 / 2 → g t = 0 := fun t ht => by
      simp only [hg_def]
      rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
    have hg_right : ∀ t, 1 ≤ t → g t = 0 := fun t ht => by
      simp only [hg_def]
      rw [Real.smoothTransition.zero_of_nonpos (by linarith : 12 * (1 - t) ≤ 0), mul_zero]
    have hg_mid : ∀ t, 7 / 12 ≤ t → t ≤ 11 / 12 → g t = 1 := fun t h₁ h₂ => by
      simp only [hg_def]
      rw [Real.smoothTransition.one_of_one_le (by linarith),
        Real.smoothTransition.one_of_one_le (by linarith), mul_one]
    set c : ℝ := ∫ s in (1 / 2 : ℝ)..1, g s with hc_def
    have hc_ge : 1 / 3 ≤ c := by
      have h : ∫ s in (7 / 12 : ℝ)..(11 / 12), g s = 1 / 3 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
        · simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
          norm_num
        · intro s hs
          rw [uIcc_of_le (by norm_num)] at hs
          exact hg_mid s hs.1 hs.2
      rw [← h]
      exact intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) (by norm_num)
        (ae_of_all _ hg_nonneg) (hg_int _ _)
    have hc_pos : 0 < c := by linarith
    have hcinv_le : c⁻¹ ≤ 3 := by
      rw [inv_le_comm₀ hc_pos (by norm_num)]
      linarith
    set F : ℝ → ℝ := fun t => ∫ s in (1 / 2 : ℝ)..t, g s with hF_def
    have hF_deriv : ∀ t, HasDerivAt F (g t) t := fun t =>
      (hg_cont.integral_hasStrictDerivAt (1 / 2) t).hasDerivAt
    have hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F :=
      contDiff_infty_iff_deriv.2 ⟨fun t => (hF_deriv t).differentiableAt,
        (funext fun t => (hF_deriv t).deriv : deriv F = g) ▸ hg_smooth⟩
    have hF_left : ∀ t, t ≤ 1 / 2 → F t = 0 := fun t ht => by
      simp only [hF_def]
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · intro s hs
        rw [uIcc_of_ge ht] at hs
        exact hg_left s hs.2
    have hF_right : ∀ t, 1 ≤ t → F t = c := fun t ht => by
      simp only [hF_def, hc_def]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hg_int (1 / 2) 1) (hg_int 1 t)]
      have h : ∫ s in (1 : ℝ)..t, g s = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
        · simp
        · intro s hs
          rw [uIcc_of_le ht] at hs
          exact hg_right s hs.1
      rw [h, add_zero]
    have hF_bounds : ∀ t, 0 ≤ F t ∧ F t ≤ c := fun t => by
      rcases le_total t (1 / 2) with ht | ht
      · rw [hF_left t ht]
        exact ⟨le_rfl, hc_pos.le⟩
      rcases le_total 1 t with ht' | ht'
      · rw [hF_right t ht']
        exact ⟨hc_pos.le, le_rfl⟩
      exact ⟨intervalIntegral.integral_nonneg ht fun u _ => hg_nonneg u,
        intervalIntegral.integral_mono_interval le_rfl ht ht' (ae_of_all _ hg_nonneg) (hg_int _ _)⟩
    have hφ_deriv : ∀ t, HasDerivAt (fun t => 1 - c⁻¹ * F t) (-(c⁻¹ * g t)) t := fun t => by
      simpa using ((hF_deriv t).const_mul c⁻¹).const_sub 1
    refine ⟨fun t => 1 - c⁻¹ * F t, contDiff_const.sub (contDiff_const.mul hF_smooth), ?_, ?_, ?_, ?_⟩
    · intro t
      obtain ⟨h₀, h₁⟩ := hF_bounds t
      have hci : 0 ≤ c⁻¹ := inv_nonneg.2 hc_pos.le
      have h : c⁻¹ * F t ≤ 1 := by
        calc c⁻¹ * F t ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left h₁ hci
          _ = 1 := inv_mul_cancel₀ hc_pos.ne'
      exact ⟨by linarith, by linarith [mul_nonneg hci h₀]⟩
    · intro t ht
      simp only [hF_left t ht, mul_zero, sub_zero]
    · intro t ht
      simp only [hF_right t ht, inv_mul_cancel₀ hc_pos.ne', sub_self]
    · refine lipschitzWith_of_nnnorm_deriv_le (fun t => (hφ_deriv t).differentiableAt) fun t => ?_
      rw [(hφ_deriv t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (mul_nonneg (inv_nonneg.2 hc_pos.le) (hg_nonneg t))]
      calc c⁻¹ * g t ≤ c⁻¹ * 1 := mul_le_mul_of_nonneg_left (hg_le_one t) (inv_nonneg.2 hc_pos.le)
        _ ≤ 3 := by rw [mul_one]; exact hcinv_le
        _ = ((3 : ℝ≥0) : ℝ) := by norm_num
  have hC : ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclid P => φ (‖x - ξ‖ / r)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases eq_or_ne x ξ with rfl | hx
    · refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds x (half_pos hr)] with y hy
      rw [Metric.mem_ball, dist_eq_norm] at hy
      exact hφ_one _ ((div_le_iff₀ hr).2 (by linarith))
    · have h : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Euclid P => ‖y - ξ‖ / r) x :=
        ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hx)).div_const r
      exact hφ_smooth.contDiffAt.comp x h
  have hlip : LipschitzWith (3 / r.toNNReal) fun y : Euclid P => φ (‖y - ξ‖ / r) := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [NNReal.coe_div, Real.coe_toNNReal r hr.le]
    calc dist (φ (‖y - ξ‖ / r)) (φ (‖z - ξ‖ / r))
        ≤ (3 : ℝ≥0) * dist (‖y - ξ‖ / r) (‖z - ξ‖ / r) := hφ_lip.dist_le_mul _ _
      _ = 3 / r * |‖y - ξ‖ - ‖z - ξ‖| := by
          rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hr]; push_cast; try ring
      _ ≤ 3 / r * ‖(y - ξ) - (z - ξ)‖ := by gcongr; exact abs_norm_sub_norm_le _ _
      _ = (3 : ℝ≥0) / r * dist y z := by rw [sub_sub_sub_cancel_right, dist_eq_norm]; push_cast; try ring
  refine ⟨fun x => φ (‖x - ξ‖ / r), hC.of_le (by norm_cast), fun x => hφ_bounds _,
    fun x hx => hφ_one _ ?_, ?_, fun x => ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm] at hx
    rw [div_le_iff₀ hr]
    linarith
  · refine (closure_mono ?_).trans (closure_ball_subset_closedBall)
    intro x hx
    by_contra hxb
    apply hx
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at hxb
    exact hφ_zero _ ((le_div_iff₀ hr).2 (by linarith))
  · have h := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := x)
    rwa [NNReal.coe_div, Real.coe_toNNReal r hr.le] at h
```

## Key steps

1. Admissible profile χ: C¹, 0 ≤ χ ≤ 1, χ = 1 on (−∞, 1/2], χ = 0 on [1, ∞), 3-Lipschitz (cubic 1 − 3u² + 2u³ at u = 2σ − 1, or a smoothTransition primitive).
2. ζ(x) := χ(‖x − ξ‖/r): values in [0, 1], ζ = 1 on B̄_{r/2}(ξ), ζ = 0 when ‖x − ξ‖ ≥ r, hence tsupport ζ ⊆ B̄_r(ξ).
3. ζ is C¹: constant near ξ, and χ composed with the smooth map ‖· − ξ‖/r away from ξ.
4. ζ is (3/r)-Lipschitz by the reverse triangle inequality, hence ‖Dζ(x)‖ ≤ 3/r.

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
