# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_approximate_tangent-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_approximate_tangent-a1.rescaled_integral_tendsto-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3(c), 4, 5 and 6 of the parent proof, with J an arbitrary continuous weight (the parent uses J = JΦ). The parent's substitution v = w + rs on ℝⁿ used BLOWUP together with μHE[n] = Lⁿ. Here it is done directly with the scaling and translation formulas for Lebesgue (Haar) measure, so no sibling result is needed. The parent's step 1 limit is re-derived inside step 5 from differentiability.

Conventions: ℝ^P = Eucl P = EuclideanSpace ℝ (Fin P) with Euclidean norm ‖·‖; Lⁿ = volume on Eucl n, an additive Haar measure with finrank ℝ (Eucl n) = n (finrank_euclideanSpace_fin); L := fderiv ℝ Φ w; B̄_ρ(x) = closedBall x ρ.

1. (Constants.)
 (a) tsupport φ is compact, hence bounded. So there is R > 0 with tsupport φ ⊆ B̄_R(0). Lean: hφc.isCompact.isBounded.subset_closedBall_lt 0 0.
 (b) φ is continuous with compact support, so there is A with ‖φ(x)‖ ≤ A for all x (Continuous.bounded_above_of_compact_support). Then A ≥ ‖φ(0)‖ ≥ 0.
 (c) B̄_{R/c}(w) is compact (isCompact_closedBall) and J is continuous. So there is B with ‖J(z)‖ ≤ B for all z ∈ B̄_{R/c}(w) (IsCompact.exists_bound_of_continuousOn). Then B ≥ ‖J(w)‖ ≥ 0, because w ∈ B̄_{R/c}(w) as R/c > 0.
 For r ∈ ℝ define k_r(v) := J(v)·φ(r⁻¹•(Φ(v) − Φ(w))) for v ∈ ℝⁿ, and F_r(s) := 1_Ω(w + r•s)·k_r(w + r•s) = Ω.indicator k_r (w + r•s) for s ∈ ℝⁿ.

2. (Change of variables v = w + r•s.) Let r > 0. Then ∫ F_r(s) ds = (rⁿ)⁻¹ ∫_Ω k_r(v) dv.
 - ∫_Ω k_r = ∫ Ω.indicator k_r, since Ω is open, hence measurable (integral_indicator).
 - Apply the Haar scaling formula Measure.integral_comp_smul_of_nonneg (R := r ≥ 0) to x ↦ Ω.indicator k_r (w + x). It gives ∫ Ω.indicator k_r (w + r•s) ds = (r^{finrank})⁻¹ • ∫ Ω.indicator k_r (w + x) dx, with finrank ℝ (Eucl n) = n.
 - By translation invariance (integral_add_left_eq_self), ∫ Ω.indicator k_r (w + x) dx = ∫ Ω.indicator k_r (x) dx.
 - Combining these gives the claim. All three identities hold for the Bochner integral without any integrability hypothesis.

3. (Measurability.) Fix r. k_r is continuous, as a product and composition of the continuous maps J, φ, Φ, subtraction of the constant Φ(w), and scalar multiplication by r⁻¹. Hence Ω.indicator k_r is measurable (Measurable.indicator, Ω measurable). The map s ↦ w + r•s is continuous, hence measurable. So F_r is measurable, hence AEStronglyMeasurable for Lⁿ.

4. (Domination for 0 < r ≤ 1.) Let bound(s) := 1_{B̄_{R/c}(0)}(s)·(B·A). Claim: ‖F_r(s)‖ ≤ bound(s) for all r ∈ (0, 1] and all s ∈ ℝⁿ.
 - If F_r(s) = 0 this holds because bound ≥ 0 (B, A ≥ 0).
 - Otherwise: (i) w + r•s ∈ Ω, since otherwise the indicator is 0. So F_r(s) = J(w + r•s)·φ(r⁻¹•(Φ(w + r•s) − Φ(w))).
   (ii) φ(r⁻¹•(Φ(w + r•s) − Φ(w))) ≠ 0, since otherwise F_r(s) = 0. So this point lies in support φ ⊆ tsupport φ ⊆ B̄_R(0), i.e. r⁻¹‖Φ(w + r•s) − Φ(w)‖ ≤ R, i.e. ‖Φ(w + r•s) − Φ(w)‖ ≤ rR.
   (iii) The antilipschitz hypothesis with v = w + r•s ∈ Ω and v′ = w ∈ Ω gives c·r‖s‖ = c‖r•s‖ ≤ ‖Φ(w + r•s) − Φ(w)‖ ≤ rR. Dividing by r > 0 and c > 0 gives ‖s‖ ≤ R/c. So s ∈ B̄_{R/c}(0) and bound(s) = B·A.
   (iv) dist(w + r•s, w) = ‖r•s‖ = r‖s‖ ≤ ‖s‖ ≤ R/c, because 0 < r ≤ 1. Hence ‖J(w + r•s)‖ ≤ B, and ‖φ(·)‖ ≤ A.
   Therefore ‖F_r(s)‖ = ‖J(w + r•s)‖·‖φ(·)‖ ≤ B·A = bound(s).
 - bound is Lⁿ-integrable: B̄_{R/c}(0) has finite volume (measure_closedBall_lt_top), so the constant B·A is integrable on it (integrableOn_const), and its indicator is integrable (IntegrableOn.integrable_indicator, measurableSet_closedBall).
 - The set (0, 1] = Ioc 0 1 belongs to 𝓝[>] 0 (Ioc_mem_nhdsGT zero_lt_one), so the bound holds 𝓝[>]0-eventually.

5. (Pointwise limit.) Fix s ∈ ℝⁿ. We show F_t(s) → J(w)·φ(L s) as t → 0⁺.
 (i) The curve t ↦ w + t•s has derivative s at 0 and value w at 0, and Φ has derivative L at w. By the chain rule (HasFDerivAt.comp_hasDerivAt_of_eq), γ(t) := Φ(w + t•s) has derivative L s at 0. By HasDerivAt.tendsto_slope_zero_right, t⁻¹•(Φ(w + t•s) − Φ(w)) → L s along 𝓝[>] 0; simp removes 0 + t and 0•s.
 (ii) t ↦ w + t•s is continuous with value w at 0, so w + t•s → w along 𝓝[>] 0 (≤ 𝓝 0). Since Ω ∈ 𝓝 w (Ω open, w ∈ Ω), eventually w + t•s ∈ Ω.
 (iii) By continuity of J, J(w + t•s) → J(w). By continuity of φ and (i), φ(t⁻¹•(Φ(w + t•s) − Φ(w))) → φ(L s). Hence the product converges to J(w)·φ(L s) (Tendsto.mul).
 (iv) By (ii), for eventually all t, F_t(s) equals this product (indicator_of_mem). So F_t(s) → J(w)·φ(L s) (Tendsto.congr').

6. (Dominated convergence.) 𝓝[>] (0 : ℝ) is countably generated. tendsto_integral_filter_of_dominated_convergence applies with:
 - the bound function bound;
 - the eventual measurability from step 3;
 - the eventual domination and integrability of bound from step 4;
 - the pointwise limit from step 5, which holds for every s and hence a.e.
 It gives ∫ F_r(s) ds → ∫ J(w)·φ(L s) ds as r → 0⁺.

7. (Conclusion.) By step 2, for 𝓝[>]0-eventually all r (namely all r > 0, by self_mem_nhdsWithin), ∫ F_r = (rⁿ)⁻¹ ∫_Ω J(v)·φ(r⁻¹•(Φ(v) − Φ(w))) dv. By Tendsto.congr', the stated function converges to ∫ J(w)·φ(L s) ds = ∫ s, J w * φ (fderiv ℝ Φ w s). ∎

Lean remark. The following proof was verified in the exact comparator scope as `theorem Submission.lpf_wtc_cat_rescaled_integral_tendsto : (<frozen statement>) := by` inside `namespace GMT.Ch06`. Axioms: propext, Classical.choice, Quot.sound.
  intro Q n Φ Ω J φ w hΩ hw hΦc hdiff hanti hJ hφ hφc
  obtain ⟨c, hc, hcΩ⟩ := hanti
  obtain ⟨R, hR0, hR⟩ : ∃ R, 0 < R ∧ tsupport φ ⊆ closedBall (0 : Eucl Q) R :=
    hφc.isCompact.isBounded.subset_closedBall_lt 0 0
  obtain ⟨A, hA⟩ : ∃ A, ∀ x, ‖φ x‖ ≤ A := hφ.bounded_above_of_compact_support hφc
  obtain ⟨B, hB⟩ : ∃ B, ∀ z ∈ closedBall w (R / c), ‖J z‖ ≤ B :=
    (isCompact_closedBall w (R / c)).exists_bound_of_continuousOn hJ.continuousOn
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB w (mem_closedBall_self (div_pos hR0 hc).le))
  set F : ℝ → Eucl n → ℝ := fun r s =>
    Ω.indicator (fun v => J v * φ (r⁻¹ • (Φ v - Φ w))) (w + r • s) with hF
  have hcov : ∀ r : ℝ, 0 < r →
      ∫ s, F r s = (r ^ n)⁻¹ * ∫ v in Ω, J v * φ (r⁻¹ • (Φ v - Φ w)) := by
    intro r hr
    rw [← integral_indicator hΩ.measurableSet]
    have h1 := Measure.integral_comp_smul_of_nonneg (volume : Measure (Eucl n))
      (fun x => Ω.indicator (fun v => J v * φ (r⁻¹ • (Φ v - Φ w))) (w + x)) r (hR := hr.le)
    rw [integral_add_left_eq_self, finrank_euclideanSpace_fin, smul_eq_mul] at h1
    exact h1
  have hmeas : ∀ r : ℝ, AEStronglyMeasurable (F r) volume := by
    intro r
    have hk : Continuous (fun v => J v * φ (r⁻¹ • (Φ v - Φ w))) := by
      have h1 : Continuous (fun v => r⁻¹ • (Φ v - Φ w)) :=
        (hΦc.sub continuous_const).const_smul r⁻¹
      exact hJ.mul (hφ.comp h1)
    have hlin : Measurable (fun s : Eucl n => w + r • s) :=
      (continuous_const.add (continuous_id.const_smul r)).measurable
    exact ((hk.measurable.indicator hΩ.measurableSet).comp hlin).aestronglyMeasurable
  set bound : Eucl n → ℝ := (closedBall (0 : Eucl n) (R / c)).indicator (fun _ => B * A) with hbound
  have hdom : ∀ r : ℝ, r ∈ Ioc (0 : ℝ) 1 → ∀ s, ‖F r s‖ ≤ bound s := by
    rintro r ⟨hr0, hr1⟩ s
    by_cases hz : F r s = 0
    · rw [hz, norm_zero]
      exact indicator_nonneg (fun _ _ => mul_nonneg hB0 hA0) s
    · have hmemΩ : w + r • s ∈ Ω := by
        by_contra hnot
        exact hz (by simp only [hF, indicator_of_notMem hnot])
      have hFeq : F r s = J (w + r • s) * φ (r⁻¹ • (Φ (w + r • s) - Φ w)) := by
        simp only [hF, indicator_of_mem hmemΩ]
      have hφne : φ (r⁻¹ • (Φ (w + r • s) - Φ w)) ≠ 0 := by
        intro h0; apply hz; rw [hFeq, h0, mul_zero]
      have hinR : ‖r⁻¹ • (Φ (w + r • s) - Φ w)‖ ≤ R := by
        have := hR (subset_tsupport φ hφne)
        simpa [mem_closedBall, dist_zero_right] using this
      have hΦR : ‖Φ (w + r • s) - Φ w‖ ≤ r * R := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr0.le), inv_mul_le_iff₀ hr0] at hinR
        exact hinR
      have hant := hcΩ (w + r • s) hmemΩ w hw
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr0.le] at hant
      have hs : ‖s‖ ≤ R / c := by
        rw [le_div_iff₀ hc]
        have : r * (c * ‖s‖) ≤ r * R := by nlinarith
        nlinarith
      have hsball : s ∈ closedBall (0 : Eucl n) (R / c) := by
        simpa [mem_closedBall, dist_zero_right] using hs
      have hwball : w + r • s ∈ closedBall w (R / c) := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg hr0.le]
        calc r * ‖s‖ ≤ 1 * ‖s‖ := by gcongr
          _ = ‖s‖ := one_mul _
          _ ≤ R / c := hs
      rw [hbound, indicator_of_mem hsball, hFeq, norm_mul]
      exact mul_le_mul (hB _ hwball) (hA _) (norm_nonneg _) hB0
  have hint : Integrable bound volume := by
    rw [hbound]
    exact (integrableOn_const (measure_closedBall_lt_top (x := (0 : Eucl n)) (r := R / c)).ne).integrable_indicator measurableSet_closedBall
  have hlim : ∀ s, Tendsto (fun r => F r s) (𝓝[>] 0) (𝓝 (J w * φ (fderiv ℝ Φ w s))) := by
    intro s
    have hline : HasDerivAt (fun t : ℝ => w + t • s) s 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const s).const_add w
    have hγ : HasDerivAt (fun t : ℝ => Φ (w + t • s)) (fderiv ℝ Φ w s) 0 := by
      have h0 : w + (0 : ℝ) • s = w := by simp
      exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline h0.symm
    have hslope : Tendsto (fun t : ℝ => t⁻¹ • (Φ (w + t • s) - Φ w)) (𝓝[>] 0)
        (𝓝 (fderiv ℝ Φ w s)) := by
      simpa using hγ.tendsto_slope_zero_right
    have hcont : Continuous (fun t : ℝ => w + t • s) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hto : Tendsto (fun t : ℝ => w + t • s) (𝓝[>] 0) (𝓝 w) := by
      have := hcont.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), w + t • s ∈ Ω := hto (hΩ.mem_nhds hw)
    have hJlim : Tendsto (fun t : ℝ => J (w + t • s)) (𝓝[>] 0) (𝓝 (J w)) :=
      (hJ.tendsto w).comp hto
    have hφlim : Tendsto (fun t : ℝ => φ (t⁻¹ • (Φ (w + t • s) - Φ w))) (𝓝[>] 0)
        (𝓝 (φ (fderiv ℝ Φ w s))) := (hφ.tendsto _).comp hslope
    refine (hJlim.mul hφlim).congr' ?_
    filter_upwards [hmem] with t ht
    simp only [hF, indicator_of_mem ht]
  have hdct := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (Eucl n)))
    (l := 𝓝[>] (0 : ℝ)) (F := F) (f := fun s => J w * φ (fderiv ℝ Φ w s)) bound
    (Eventually.of_forall hmeas)
    (by filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with r hr
        exact Eventually.of_forall (hdom r hr))
    hint (Eventually.of_forall hlim)
  refine hdct.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hcov r hr

## Key steps

1. Constants: R > 0 with tsupport φ ⊆ B̄_R(0), A = sup|φ|, B = sup of |J| on B̄_{R/c}(w).
2. Change of variables v = w + r•s by Haar scaling and translation: (rⁿ)⁻¹∫_Ω k_r = ∫ F_r with F_r(s) = 1_Ω(w + r•s)·J(w + r•s)·φ(r⁻¹(Φ(w + r•s) − Φ(w))).
3. Each F_r is measurable (indicator of an open set composed with an affine map, times a continuous function).
4. Domination for 0 < r ≤ 1: φ ≠ 0 forces ‖Φ(w + r•s) − Φ(w)‖ ≤ rR, so the antilipschitz bound gives ‖s‖ ≤ R/c, and |F_r| ≤ B·A·1_{B̄_{R/c}(0)}, which is integrable.
5. Pointwise limit: eventually w + r•s ∈ Ω, slope limit r⁻¹(Φ(w + r•s) − Φ(w)) → DΦ(w)s, continuity of J and φ give F_r(s) → J(w)φ(DΦ(w)s).
6. Dominated convergence along the countably generated filter 𝓝[>]0, then Tendsto.congr' with the change-of-variables identity.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); diff of snapshot project/GMT/Ch06/Contract.lean against workspace GMT/Ch06/Contract.lean (identical)`
- `python3 scan of dag.json: lean_name/lean_statement/status/depends_on of root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.* ; scan of all nodes for dependencies on non-siblings (none); grep -c 'lpf_wtc_cat_|fderiv_lower_bound|rescaled_integral_tendsto|gram_jacobian_continuous' dag.json DAG.md dag.mmd issue-workers.json problem.json (0 hits)`
- `inspection of parent-child-handoff.json of children of split nodes that have uncle dependencies (nodes/root-boundary-rectifiability-a1-lattice-approximation-a1-*): children carry only sibling deps; the split parent uses its own resolved deps in its assembly`
- `sed -n 1,160p simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (blowUpMap, HasApproximateTangentSpaceAt)`
- `contract_scope and child_modules from verifier/gmt-compare.py (CHILD_TARGET = HumanizeNodeComparator.target) to generate the exact child-scope prefix and NodeChallenge/NodeSolution files; lean_contract.validate_lean_statement on the 3 child statements`
- `lean -R . -o out/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean in /tmp/cat_decomp_scratch_e41b with LEAN_PATH = lake-packages-25730c7c/*/.lake/build/lib/lean; lean Scratch/Stmts.lean, Scratch/Assembly.lean, Scratch/ProveAC.lean, Scratch/ProveB.lean; simulated sim/GMT/Ch06/Submission.lean with the 3 children and the parent; lean sim/Scratch/*_NodeSolution.lean and sim/Scratch/AllNodes.lean (#print axioms)`
- `rg -n 'integral_comp_smul_of_nonneg|integral_add_left_eq_self|tendsto_slope_zero_right|tendsto_integral_filter_of_dominated_convergence' Mathlib/MeasureTheory Mathlib/Analysis/Calculus; rg -n for Continuous.matrix_det, ContDiff.continuous_fderiv, HasFDerivAt.comp_hasDerivAt_of_eq, LinearMap.finrank_range_of_inj, coe_range, comp_homeomorph, integral_mul_left_eq_self in the snapshot mathlib`
- `rg -n 'theorem .*(antilip|Antilip)' simongmt/Poincare/SimonGMT; rg -ln 'Matrix.of fun i j => inner|Gram' simongmt/Poincare/SimonGMT`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-8ee6679021/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-8ee6679021/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-lattice-approximation-a1-flat-to-weak-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaBranches.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/tmp/cat_decomp_scratch_e41b/Scratch/Assembly.lean`
- `/tmp/cat_decomp_scratch_e41b/Scratch/ProveAC.lean`
- `/tmp/cat_decomp_scratch_e41b/Scratch/ProveB.lean`
- `/tmp/cat_decomp_scratch_e41b/sim/GMT/Ch06/Submission.lean`

The snapshot pins project d8d46c95 and Mathlib 25730c7c. Its Contract.lean is byte-identical to the workspace contract.

The child scope is `import GMT.Ch06.Submission`, then `open MeasureTheory Filter Set Metric` and `open scoped ENNReal NNReal Topology`, then `namespace GMT.Ch06` with its opens, then `noncomputable section` … `end`. It was derived with gmt-compare.py contract_scope.

Definitions checked in simongmt Chapter03/Rectifiable.lean:
- `blowUpMap x r y := r⁻¹ • (y - x)`. So the sibling outputs match the child-B integrand by rfl.
- `HasApproximateTangentSpaceAt n M x P := finrank ℝ P = n ∧ ∀ f : C_c(E, ℝ), Tendsto (fun r ↦ ∫ y in blowUpMap x r '' M, f y ∂μHE[n]) (𝓝[>] 0) (𝓝 (∫ y in (P : Set E), f y ∂μHE[n]))`.

DAG checks:
- No existing node depends on a non-sibling. So the children cannot cite the sibling nodes BLOWUP/AREA, and they are designed not to need them.
- No lpf_wtc_cat_* name is reserved, and no existing declaration has these statements.

Library search: no SimonGMT lemma states the derivative lower bound, the rescaled dominated-convergence limit, or continuity of the Gram Jacobian. The only antilipschitz lemma is ApproximatesLinearOn.injOn_of_antilipschitz in Chapter02/AreaBranches.lean; the Chapter05 Gram files concern graph area expansions.

Mathlib lemmas used, as located in the snapshot:
- Measure.integral_comp_smul_of_nonneg (Haar/NormedSpace.lean:115);
- integral_add_left_eq_self (additive form of Group/Integral.lean:91);
- HasDerivAt.tendsto_slope_zero_right (Deriv/Slope.lean:89);
- tendsto_integral_filter_of_dominated_convergence (Integral/DominatedConvergence.lean:67);
- HasFDerivAt.comp_hasDerivAt_of_eq (Deriv/Comp.lean:380);
- ContDiff.continuous_fderiv (ContDiff/Defs.lean:1271);
- Continuous.matrix_det (Topology/Instances/Matrix.lean:212);
- LinearMap.finrank_range_of_inj (Dimension/Finrank.lean:127);
- LinearMap.coe_range (Submodule/Range.lean:60);
- HasCompactSupport.comp_homeomorph (additive form of Topology/Algebra/Support.lean:562).

All 3 child statements pass validate_lean_statement and elaborate in the exact scope. The needed instances are found: IsAddHaarMeasure for volume on Eucl n, and IsCountablyGenerated for 𝓝[>] 0.

All 3 children were fully proved in Lean with only standard axioms. The frozen parent was kernel-checked from them plus sorry-stubs of the two sibling declarations.
