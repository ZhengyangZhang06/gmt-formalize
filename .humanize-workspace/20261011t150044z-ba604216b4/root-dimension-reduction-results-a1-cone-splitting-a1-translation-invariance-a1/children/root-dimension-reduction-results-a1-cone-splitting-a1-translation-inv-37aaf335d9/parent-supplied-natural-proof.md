# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1.translate_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 3 of the parent proof (Derivative along the translation: 'for s in a bounded interval the integrand and its s-derivative θξ(y)(Dω(sv + y)[v]) vanish outside a fixed compact set and are bounded by Cθ (‖ξ(y)‖ ≤ 1 for Hⁿ-a.e. y ∈ M by … unit_orientation_norm_le_one), which is integrable there; so G is differentiable with G'(s) = S(Dβ_s(·)[v])'), written for the representing triple; Dβ_t(y)[v] = Dω(tv + y)[v]. It is the translation counterpart of the accepted Submission.dtc_cwv_scaled_action_hasDerivAt. Notation: ν := Hⁿ⌞M = μHE[n].restrict M, so R.action φ = ∫ θ(y)·ξ(y)(φ(y)) dν(y) for every form φ; norms on covectors and multivectors are operator norms.

1. (Orientation bound.) By R.orients, for ν-a.e. y there is a subspace Q with IsUnitOrientationOf (ξ(y)) Q; by the sibling orientation_norm, ‖ξ(y)‖ ≤ 1. Hence for ν-a.e. y and every n-covector α, |ξ(y)(α)| ≤ ‖ξ(y)‖·‖α‖ ≤ ‖α‖.
2. (Data from ω.) ω is C^∞ with compact support, so ω and Dω are continuous, and ω(z) = 0, Dω(z) = 0 whenever z ∉ tsupport ω (tsupport Dω ⊆ tsupport ω, Mathlib tsupport_fderiv_subset). Choose r ∈ ℝ with tsupport ω ⊆ B̄_r(0) (a compact set is bounded) and K₀ with ‖ω(z)‖ ≤ K₀ for every z (continuous with compact support); then K₀ ≥ ‖ω(0)‖ ≥ 0.
3. (Integrands.) For s ∈ ℝ and y ∈ ℝ^P put Ψ(s, y) := Dω(sv + y)[v], F(s, y) := θ(y)·ξ(y)(ω(sv + y)) and F'(s, y) := θ(y)·ξ(y)(Ψ(s, y)). Then G(s) = ∫ F(s, ·) dν, and the claimed derivative is ∫ F'(t, ·) dν = R.action(y ↦ Ψ(t, y)).
4. (Pointwise derivative.) Fix y. The map s ↦ sv + y has derivative v; ω is differentiable, so by the chain rule s ↦ ω(sv + y) has derivative Dω(sv + y)[v] = Ψ(s, y). Composing with the continuous linear functional ξ(y) and multiplying by the constant θ(y), s ↦ F(s, y) has derivative F'(s, y) at every s, for every y.
5. (Measurability.) θ is measurable (R.measurable_mult composed with ℕ → ℝ) and ξ is AEStronglyMeasurable for ν (R.aestronglyMeasurable_orient). The map (s, y) ↦ Ψ(s, y) is jointly continuous (Dω is continuous, (s, y) ↦ sv + y is continuous, and evaluation at the constant v is continuous), and y ↦ ω(sv + y) is continuous for each s. The evaluation (ζ, α) ↦ ζ(α) is continuous on MultiVector P n × Covector (Euclid P) n, so y ↦ ξ(y)(φ(y)) is AEStronglyMeasurable for ν for every continuous φ; multiplying by θ, F(s, ·) (each s) and F'(t, ·) are AEStronglyMeasurable for ν.
6. (Localization.) Let I := (t − 1, t + 1), an open neighbourhood of t, ρ := r + (|t| + 1)‖v‖ and B := B̄_ρ(0) (compact and measurable). For s ∈ [t − 1, t + 1], |s| ≤ |t| + 1. If |s| ≤ |t| + 1 and sv + y ∈ tsupport ω, then ‖sv + y‖ ≤ r and ‖y‖ ≤ ‖sv + y‖ + ‖sv‖ ≤ r + |s|·‖v‖ ≤ ρ, i.e. y ∈ B. If sv + y ∉ tsupport ω, then ω(sv + y) = 0 and Dω(sv + y) = 0 by step 2, so F(s, y) = F'(s, y) = 0.
7. (Uniform bound.) Ψ is continuous on the compact set [t − 1, t + 1] × B, so there is K with ‖Ψ(s, y)‖ ≤ K for (s, y) ∈ [t − 1, t + 1] × B. Let g(y) := K·θ(y)·1_B(y). For ν-a.e. y (those of step 1) and every s ∈ I: if sv + y ∈ tsupport ω, then y ∈ B by step 6 and |F'(s, y)| ≤ θ(y)·‖ξ(y)‖·‖Ψ(s, y)‖ ≤ θ(y)·1·K = g(y); otherwise F'(s, y) = 0 ≤ g(y), since g(y) = 0 if y ∉ B, and if y ∈ B then K ≥ ‖Ψ(t, y)‖ ≥ 0.
8. (Integrability.) B is compact and B ⊆ univ, so R.locallyIntegrable_mult gives ∫_{M∩B} θ dHⁿ < ∞; as θ is measurable, θ·1_B is ν-integrable, hence so is g. Moreover |F(t, y)| ≤ K₀·θ(y)·1_B(y) for ν-a.e. y: if tv + y ∈ tsupport ω then y ∈ B (step 6 with s = t) and |F(t, y)| ≤ θ(y)·1·K₀; otherwise F(t, y) = 0 ≤ K₀θ(y)1_B(y). So F(t, ·) is ν-integrable.
9. (Conclusion.) The dominated differentiation theorem (Mathlib hasDerivAt_integral_of_dominated_loc_of_deriv_le, with the neighbourhood I of t) applies: F(s, ·) is AEStronglyMeasurable for s near t (step 5); F(t, ·) is integrable (step 8); F'(t, ·) is AEStronglyMeasurable (step 5); |F'(s, y)| ≤ g(y) for ν-a.e. y and all s ∈ I, with g integrable (steps 7–8); and s ↦ F(s, y) has derivative F'(s, y) on I for every y (step 4). Hence G(s) = ∫ F(s, ·) dν has derivative ∫ F'(t, ·) dν = R.action(y ↦ Dω(tv + y)[v]) at t. ∎

Implementation note (not part of the numbered proof).
- The Lean proof below of exactly this frozen type was kernel-checked during this decomposition: Lean v4.35.0-rc3, Mathlib 25730c7c, after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)`), like the accepted Submission theorems. #print axioms gives propext, Classical.choice, Quot.sound. It was also checked in isolation with only the listed sibling dependencies present (as stubs), and through the comparator's own NodeSolution wrapper (`exact Submission.X`).
- Do not put `open scoped ContDiff` in front of the declaration (it makes `ω` a reserved token); write the smoothness order as `(⊤ : ℕ∞)`, not `∞` (with `open scoped ENNReal`, `∞` is the ENNReal top).
- Bound the jointly continuous covector-valued Ψ on the compact set as in step 7 (`IsCompact.exists_bound_of_continuousOn`); applying `Continuous.bounded_above_of_compact_support` to the CLM-valued `fderiv ℝ ω` hits a deterministic whnf timeout (recorded by the accepted dilation analogue). `Continuous.bounded_above_of_compact_support` is used only for the covector-valued ω (step 2).
- The sibling orientation_norm is `Submission.unit_orientation_norm_le_one`.
```lean
/-- Differentiation under the integral sign for the translations `y ↦ sv + y`: for every `t`,
`s ↦ τ(M, θ, ξ)(ω(sv + ·))` has derivative `τ(M, θ, ξ)(Dω(tv + ·)[v])` at `t`.  For
`s ∈ (t − 1, t + 1)` the integrands vanish off `B = B̄_ρ(0)`, `ρ = r + (|t| + 1)‖v‖` where
`spt ω ⊆ B̄_r(0)`, and are dominated by `K θ 1_B`, `K` bounding the continuous map
`(s, y) ↦ Dω(sv + y)[v]` on `[t − 1, t + 1] × B` (as `‖ξ‖ ≤ 1` a.e.); `θ 1_B` is integrable since
`θ` is locally `Hⁿ`-integrable. -/
theorem Submission.dimred_cs_ti_translate_action_hasDerivAt : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (ω : TestFormOn (univ : Set (Euclid P)) n) (v : Euclid P) (t : ℝ), HasDerivAt (fun s : ℝ => R.action (fun y => (ω : DifferentialForm (Euclid P) n) (s • v + y))) (R.action (fun y => fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) v)) t := by
  intro P n R ω v t
  have hws : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
  have hwc : HasCompactSupport (ω : DifferentialForm (Euclid P) n) := ω.property.1.2
  set w : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n) with hw_def
  -- Step 1: `‖ξ(x)‖ ≤ 1` for `Hⁿ⌞M`-a.e. `x`
  have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ‖R.orient x‖ ≤ 1 := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact Submission.unit_orientation_norm_le_one P n Q _ hQ
  -- Step 2: a support radius `r` and a bound `K0` for `ω`; `ω` and `Dω` vanish off `spt ω`
  have hwcont : Continuous w := hws.continuous
  have hDw : Continuous (fderiv ℝ w) := hws.continuous_fderiv (by simp)
  obtain ⟨K0, hK0⟩ := hwcont.bounded_above_of_compact_support hwc
  obtain ⟨r, hr⟩ : ∃ r, tsupport w ⊆ closedBall (0 : Euclid P) r :=
    hwc.isCompact.isBounded.subset_closedBall 0
  have hvan : ∀ z, z ∉ tsupport w → w z = 0 ∧ fderiv ℝ w z = 0 := fun z hz =>
    ⟨image_eq_zero_of_notMem_tsupport hz,
      image_eq_zero_of_notMem_tsupport (fun h => hz (tsupport_fderiv_subset ℝ h))⟩
  -- Step 3: measurability of the integrands
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have happly : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hmeas : ∀ φ : Euclid P → Covector (Euclid P) n, Continuous φ →
      AEStronglyMeasurable (fun y => (R.mult y : ℝ) * R.orient y (φ y))
        (μHE[n].restrict R.carrier) :=
    fun φ hφ => hθm.aestronglyMeasurable.mul
      (happly.comp_aestronglyMeasurable
        (R.aestronglyMeasurable_orient.prodMk hφ.aestronglyMeasurable))
  have hcF : ∀ s : ℝ, Continuous (fun y => w (s • v + y)) := fun s =>
    hwcont.comp (continuous_const.add continuous_id)
  have hΦ : Continuous (fun p : ℝ × Euclid P => fderiv ℝ w (p.1 • v + p.2) v) := by
    have hsy : Continuous (fun p : ℝ × Euclid P => p.1 • v + p.2) :=
      (continuous_fst.smul continuous_const).add continuous_snd
    exact (hDw.comp hsy).clm_apply continuous_const
  have hcF' : ∀ s : ℝ, Continuous (fun y => fderiv ℝ w (s • v + y) v) := fun s =>
    hΦ.comp (continuous_const.prodMk continuous_id)
  -- Step 4: localization in `B = B̄_ρ(0)`, `ρ = r + (|t| + 1)‖v‖`; the bound `K` of `Dω(sv+y)[v]`
  set ρ : ℝ := r + (|t| + 1) * ‖v‖ with hρ
  set B : Set (Euclid P) := closedBall (0 : Euclid P) ρ with hB
  have hBm : MeasurableSet B := measurableSet_closedBall
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := t - 1) (b := t + 1)).prod
    (isCompact_closedBall (0 : Euclid P) ρ) |>.exists_bound_of_continuousOn hΦ.continuousOn
  have hθB : IntegrableOn (fun x => (R.mult x : ℝ)) B (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, Measure.restrict_restrict hBm, inter_comm]
    simpa only [Real.enorm_natCast] using
      (R.locallyIntegrable_mult B (isCompact_closedBall 0 ρ) (subset_univ _)).lt_top
  -- if `|s| ≤ |t| + 1` and `s v + y ∈ spt ω` then `y ∈ B`
  have hmemB : ∀ s : ℝ, |s| ≤ |t| + 1 → ∀ y : Euclid P, s • v + y ∈ tsupport w → y ∈ B := by
    intro s hs y hy
    have h1 : ‖s • v + y‖ ≤ r := by simpa using hr hy
    have h2 := norm_sub_le (s • v + y) (s • v)
    rw [add_sub_cancel_left] at h2
    have h3 : ‖s • v‖ ≤ (|t| + 1) * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hs (norm_nonneg v)
    simp only [hB, mem_closedBall, dist_zero_right, hρ]
    linarith
  have habs : ∀ s ∈ Icc (t - 1) (t + 1), |s| ≤ |t| + 1 := by
    intro s hs
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2, neg_abs_le t, le_abs_self t]
  -- Step 5: hypotheses of the dominated differentiation theorem
  have hs : Ioo (t - 1) (t + 1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable
      (fun y => (R.mult y : ℝ) * R.orient y (w (s • v + y))) (μHE[n].restrict R.carrier) :=
    Eventually.of_forall fun s => hmeas _ (hcF s)
  have hF'_meas : AEStronglyMeasurable (fun y => (R.mult y : ℝ) * R.orient y
      (fderiv ℝ w (t • v + y) v)) (μHE[n].restrict R.carrier) := hmeas _ (hcF' t)
  have hF_int : Integrable (fun y => (R.mult y : ℝ) * R.orient y (w (t • v + y)))
      (μHE[n].restrict R.carrier) := by
    refine ((hθB.integrable_indicator hBm).const_mul K0).mono' (hmeas _ (hcF t)) ?_
    filter_upwards [hξ] with y hy
    by_cases hty : t • v + y ∈ tsupport w
    · have hyB := hmemB t (by linarith [abs_nonneg t]) y hty
      rw [indicator_of_mem hyB, norm_mul, Real.norm_natCast]
      calc (R.mult y : ℝ) * ‖R.orient y (w (t • v + y))‖
          ≤ (R.mult y : ℝ) * (‖R.orient y‖ * ‖w (t • v + y)‖) := by
            gcongr; exact (R.orient y).le_opNorm _
        _ ≤ (R.mult y : ℝ) * (1 * K0) := by
            gcongr
            exact hK0 _
        _ = K0 * (R.mult y : ℝ) := by ring
    · rw [(hvan _ hty).1, map_zero, mul_zero, norm_zero]
      have hK0n : 0 ≤ K0 := le_trans (norm_nonneg _) (hK0 0)
      by_cases hyB : y ∈ B
      · rw [indicator_of_mem hyB]; positivity
      · rw [indicator_of_notMem hyB, mul_zero]
  have h_bound : ∀ᵐ y ∂(μHE[n].restrict R.carrier), ∀ s ∈ Ioo (t - 1) (t + 1),
      ‖(R.mult y : ℝ) * R.orient y (fderiv ℝ w (s • v + y) v)‖ ≤
        K * B.indicator (fun x => (R.mult x : ℝ)) y := by
    filter_upwards [hξ] with y hy s hs
    by_cases hsy : s • v + y ∈ tsupport w
    · have hyB := hmemB s (habs s (Ioo_subset_Icc_self hs)) y hsy
      rw [indicator_of_mem hyB, norm_mul, Real.norm_natCast]
      have hnorm := hK (s, y) ⟨Ioo_subset_Icc_self hs, hyB⟩
      calc (R.mult y : ℝ) * ‖R.orient y (fderiv ℝ w (s • v + y) v)‖
          ≤ (R.mult y : ℝ) * (‖R.orient y‖ * ‖fderiv ℝ w (s • v + y) v‖) := by
            gcongr; exact (R.orient y).le_opNorm _
        _ ≤ (R.mult y : ℝ) * (1 * K) := by gcongr
        _ = K * (R.mult y : ℝ) := by ring
    · rw [(hvan _ hsy).2, zero_apply, map_zero, mul_zero, norm_zero]
      by_cases hyB : y ∈ B
      · rw [indicator_of_mem hyB]
        have hKn : 0 ≤ K := le_trans (norm_nonneg _)
          (hK (t, y) ⟨⟨by linarith, by linarith⟩, hyB⟩)
        positivity
      · rw [indicator_of_notMem hyB, mul_zero]
  have h_diff : ∀ᵐ y ∂(μHE[n].restrict R.carrier), ∀ s ∈ Ioo (t - 1) (t + 1),
      HasDerivAt (fun s => (R.mult y : ℝ) * R.orient y (w (s • v + y)))
        ((R.mult y : ℝ) * R.orient y (fderiv ℝ w (s • v + y) v)) s := by
    refine Eventually.of_forall fun y s _ => ?_
    have h1 : HasDerivAt (fun s : ℝ => s • v + y) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).add_const y
    have h2 : HasDerivAt (fun s : ℝ => w (s • v + y)) (fderiv ℝ w (s • v + y) v) s :=
      ((hws.differentiable (by simp)).differentiableAt (x := s • v + y)).hasFDerivAt.comp_hasDerivAt
        s h1
    exact ((R.orient y).hasFDerivAt.comp_hasDerivAt s h2).const_mul (R.mult y : ℝ)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound
    ((hθB.integrable_indicator hBm).const_mul K) h_diff
  exact key.2
```

## Key steps

1. ‖ξ‖ ≤ 1 Hⁿ⌞M-a.e. (orientation_norm); ω, Dω continuous, vanishing off tsupport ω ⊆ B̄_r(0); ‖ω‖ ≤ K₀.
2. For each y, s ↦ θ(y)ξ(y)(ω(sv + y)) has derivative θ(y)ξ(y)(Dω(sv + y)[v]) (chain rule); the integrands are AEStronglyMeasurable.
3. For s ∈ (t − 1, t + 1) the integrands vanish unless y ∈ B = B̄_{r+(|t|+1)‖v‖}(0), and |F'| ≤ Kθ1_B with θ1_B integrable (locallyIntegrable_mult); F(t, ·) is integrable.
4. hasDerivAt_integral_of_dominated_loc_of_deriv_le gives G'(t) = R.action(y ↦ Dω(tv + y)[v]).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c); git status (clean at b4d606d); stat GMT/Ch07/Submission.lean .lake/build/lib/lean/GMT/Ch07/Submission.olean`
- `python3 inspection of dag.json: selected node (depth 3, depends_on orientation_norm_bound-a1, no children), siblings under cone_splitting-a1, accepted dtc_cwv_* / dtc_cone_* / unit_orientation_norm_le_one / dtc_blowUp_testForm_corr types; scan of all lean_statements for curryLeft|blowUp|translat|fderiv|extDeriv|exteriorDerivative|HasDerivAt`
- `git show {d120e82,9203aee,77ba671,ec0cc8f,dd88db7,81f1c23,da8da23,0325970}:GMT/Ch07/Submission.lean (accepted cone criterion, wedge vanishing, Euler-Cartan, contraction, Lie annihilation, scaled derivative, dilation invariance, orientation norm proofs)`
- `python3 nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/decomposition-v1.json and nodes/root-dimension-reduction-results-a1-cone-splitting-a1/decomposition-v1.json (reuse convention, embedded-proof precedent)`
- `grep -rn 'alternatizeUncurryFin|extDeriv' and grep -rln 'Cartan|interiorProduct|lieDerivForm' in the snapshot mathlib (only Lie-algebra Cartan files; no Cartan formula or interior product for differential forms)`
- `grep -n defs in simongmt Chapter06/Forms.lean, AffineCurrentPushforward.lean, CurrentLocalEquality.lean (restrictDomain_apply); grep -rn 'curryLeft|interior|translat' simongmt (no contraction/translation lemmas)`
- `sed -n 330,400p book/chapter-07.txt (7.3.1 proof, Lemma 7.3.5 left to reader); sed -n 420,500p and 550,600p book/chapter-06.txt (homotopy formula 2.25-2.27, Lemma 2.33)`
- `#check fderiv_comp_add_left, is_const_of_deriv_eq_zero, exteriorDerivative_isTestForm, GeometricCurrentOn.boundary_apply, ContinuousAlternatingMap.curryLeftLI, ContinuousAlternatingMap.alternatizeUncurryFin`
- `verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py contract_scope/child_modules applied to the 8 types (NodeChallenge/NodeSolution emulation)`
- `lake env lean /tmp/ti-decomp/{Stubs,Full2,Emu}.lean and /tmp/ti-decomp/final/{Final,Isolate,FromJson}.lean (all children, isolation with dependency stubs, comparator wrapper, re-extraction from JSON; #print axioms)`
- `grep -rl dimred_cs_ti_ across workspaces/ (incl. .swarm-worktrees), lake-packages simongmt, and dag.json (no matches)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-translation-invariance-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-translation-invariance-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-orie-c3a822a8f5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ti-decomp/final/FromJson.lean`
- `/tmp/ti-decomp/final/Isolate.lean`
- `/tmp/ti-decomp/Emu.lean`

The pins match: the snapshot is at project b4d606d (= the workspace HEAD, clean) and mathlib 25730c7c. The built Submission.olean is newer than the frozen source.

What the library lacks.
- Mathlib has the exterior derivative (extDeriv = alternatizeUncurryFin ∘ fderiv, with extDeriv_apply and alternatizeUncurryFin_apply). It has no interior product and no Cartan formula for differential forms; the Cartan grep matches only Lie-algebra files.
- SimonGMT Chapter06 provides exteriorDerivative, IsTestForm, exteriorDerivative_isTestForm, boundary_apply, restrictDomain_apply, affinePushforward_apply and affinePullbackForm. It has no contraction, translation or Lie-derivative lemmas.
So the constant-field Cartan identity, the contraction lemma and the translation lemmas are new obligations.

Precedent and reuse.
- The accepted cone-lemma children (commits d120e82, 9203aee, 77ba671, ec0cc8f, dd88db7, 81f1c23, da8da23) prove the Euler-field (dilation) versions. Their types are tied to the point x or to sⁿω(s·), so none applies to a fixed vector v; they served as templates.
- The accepted dtc_blowUp_testForm_corr is not needed, because blowup_translate_eval unfolds blowUp directly.
- The only reuse is unit_orientation_norm_le_one (accepted, candidate 0325970, byte-identical type), which is already this node's resolved dependency.

Mathlib facts used, all present in the snapshot: fderiv_comp_add_left, is_const_of_deriv_eq_zero, HasCompactSupport.comp_homeomorph, HasCompactSupport.fderiv, hasDerivAt_integral_of_dominated_loc_of_deriv_le, Submodule.starProjection_eq_self_iff, ae_withDensity_iff and withDensity_absolutelyContinuous.

Lean check. All seven new children have kernel-checked proofs with standard axioms only, and the 9-line assembly of the frozen parent type compiles from them.
