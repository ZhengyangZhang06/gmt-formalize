# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.im_series-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.im_series-a1.density_series-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the supplied proof of dor_lmb_fc_im_series (Simon Ch. 6, Lemma 3.13, chapter-06.txt lines 901–935: the densities θ_qξ_q of the integer multiplicity currents converge in L¹), stated for an arbitrary sequence of IMReps. Departure (detail only): the supplied proof measures n-vectors with the dual norm |ζ|* = sup{ζ(α) : |α| ≤ 1}; here the operator norm ‖ζ‖ of Λ_n(ℝ^P) (the norm of MultiVector P n) is used, and the only fact needed about it is ‖ξ‖ ≤ 1 for every unit orientation ξ of a subspace, which is the reused accepted sibling orientation_norm (unit_orientation_norm_le_one). Conventions: ℝ^P = Euclid P and Hⁿ = μHE[n]. Λ_n(ℝ^P) = MultiVector P n is the space of continuous linear functionals on n-covectors (Covector (Euclid P) n), with its operator norm ‖·‖ and the induced topology. An IMRep R = (M, θ, ξ) in U is the contract structure IMRep U n (M = R.carrier Borel, M ⊆ U, countably n-rectifiable; θ = R.mult : ℝ^P → ℕ measurable, θ ≥ 1 on M, locally Hⁿ-integrable on M in U; ξ = R.orient : ℝ^P → Λ_n(ℝ^P), Hⁿ⌞M-a.e. strongly measurable and Hⁿ⌞M-a.e. a unit orientation (IsUnitOrientationOf) of an approximate tangent space of M). Its density is D_R(x) := 1_M(x)θ(x)ξ(x) ∈ Λ_n(ℝ^P) (Lean: R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x), its weight is μ_R := θ·Hⁿ⌞M (R.measure), and its action on an n-form ω is R.action(ω) = ∫_M θ(x)·ξ(x)(ω(x)) dHⁿ(x). 𝒟ⁿ(U) = TestFormOn U n (smooth n-forms on ℝ^P with compact support contained in U).
Notation: μ := Hⁿ; R_r = (M_r, θ_r, ξ_r); D_r := D_{R_r}; g_r(x) := 1_{M_r}(x)θ_r(x) ∈ [0, ∞).
1. Weight of one term. g_r is Borel (θ_r is measurable and M_r is Borel). Since M_r is Borel, μ_{R_r}(M_r) = ∫_{M_r} θ_r d(μ⌞M_r) = ∫_{M_r} θ_r dμ = ∫ g_r dμ (Mathlib withDensity_apply, Measure.restrict_restrict, lintegral_indicator). Since M_r ⊆ U, monotonicity of the measure μ_{R_r} gives ∫ g_r dμ = μ_{R_r}(M_r) ≤ μ_{R_r}(U). (No measurability of U is used.)
2. A.e. finiteness. By monotone convergence for series (lintegral_tsum), ∫ Σ_r g_r dμ = Σ_r ∫ g_r dμ ≤ Σ_r μ_{R_r}(U) < ∞. Hence Σ_r g_r(x) < ∞ for μ-a.e. x (ae_lt_top), i.e. the nonnegative real series Σ_r g_r(x) is summable for μ-a.e. x.
3. Pointwise bound. Fix r. By the field orients of R_r, for μ-a.e. x ∈ M_r (equivalently: for μ-a.e. x, x ∈ M_r implies ...) the vector ξ_r(x) is a unit orientation of some subspace Q, hence ‖ξ_r(x)‖ ≤ 1 by orientation_norm. Therefore for μ-a.e. x we have ‖D_r(x)‖ ≤ g_r(x): if x ∈ M_r, ‖θ_r(x)ξ_r(x)‖ ≤ |θ_r(x)|·‖ξ_r(x)‖ ≤ θ_r(x) = g_r(x); if x ∉ M_r, D_r(x) = 0 and g_r(x) = 0. Intersecting countably many full-measure sets, for μ-a.e. x: ‖D_r(x)‖ ≤ g_r(x) for all r.
4. The limit η and claim (a). Λ_n(ℝ^P) is complete (continuous linear maps into ℝ). For μ-a.e. x (those satisfying steps 2 and 3), Σ_r ‖D_r(x)‖ ≤ Σ_r g_r(x) < ∞, so the series Σ_r D_r(x) is summable by comparison (Summable.of_norm_bounded). Define η(x) := Σ'_r D_r(x) (the tsum in Λ_n(ℝ^P); it is 0 where the series is not summable, which happens only on a μ-null set). Then for μ-a.e. x the series Σ_r D_r(x) has sum η(x) (Summable.hasSum). This is (a).
5. Termwise integration. Fix ω ∈ 𝒟ⁿ(U) and write w := ω as an ambient form; w is continuous with compact support, so B := sup_x ‖w(x)‖ < ∞ and B ≥ 0. Put F_r(x) := D_r(x)(w(x)) ∈ ℝ.
 (i) F_r is μ-a.e. strongly measurable: x ↦ θ_r(x)ξ_r(x) is a.e. strongly measurable for μ⌞M_r (θ_r measurable, ξ_r a.e. strongly measurable for μ⌞M_r), so its indicator D_r on the Borel set M_r is a.e. strongly measurable for μ (aestronglyMeasurable_indicator_iff); w is continuous; F_r is the image of x ↦ (D_r(x), w(x)) under the continuous evaluation map (ζ, α) ↦ ζ(α).
 (ii) For μ-a.e. x: |F_r(x)| ≤ ‖D_r(x)‖·‖w(x)‖ ≤ B·g_r(x) (step 3).
 (iii) For μ-a.e. x the series Σ_r B·g_r(x) is summable (step 2), and x ↦ Σ_r B·g_r(x) is μ-integrable: μ-a.e. it equals B·G(x), where G(x) := (Σ_r ENNReal.ofReal g_r(x)).toReal is measurable and ∫ G dμ ≤ ∫ Σ_r g_r dμ < ∞ (integrable_toReal_of_lintegral_ne_top; ENNReal.ofReal_tsum_of_nonneg on the summable set).
 (iv) For μ-a.e. x the series Σ_r F_r(x) has sum η(x)(w(x)): apply the continuous linear map ζ ↦ ζ(w(x)) to the sum in step 4 (HasSum.mapL).
 By dominated convergence for series (hasSum_integral_of_dominated_convergence) with (i)–(iv), the real series Σ_r ∫ F_r dμ has sum ∫ η(x)(w(x)) dμ(x).
6. Identification of the terms. For every x, F_r(x) = 1_{M_r}(x)·θ_r(x)·ξ_r(x)(w(x)) (if x ∈ M_r, (θ_r(x)ξ_r(x))(w(x)) = θ_r(x)·ξ_r(x)(w(x)); otherwise both sides are 0). Hence ∫ F_r dμ = ∫_{M_r} θ_r(x)·ξ_r(x)(w(x)) dμ = R_r.action(w) (integral_indicator, M_r Borel). With step 5 this is (b). ∎

Lean reference implementation (kernel-checked during this decomposition in namespace GMT.Ch07 after import GMT.Ch07.Submission, together with stand-ins carrying the exact frozen types of the reused accepted declarations; #print axioms of the conditional version gives [propext, Classical.choice, Quot.sound]):
theorem Submission.dor_lmb_fc_ims_density_series : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : ℕ → IMRep U n), ∑' r, (R r).measure U ≠ ∞ → ∃ η : Euclid P → MultiVector P n, (∀ᵐ x ∂μHE[n], HasSum (fun r => (R r).carrier.indicator (fun y => ((R r).mult y : ℝ) • (R r).orient y) x) (η x)) ∧ ∀ ω : TestFormOn U n, HasSum (fun r => (R r).action (ω : DifferentialForm (Euclid P) n)) (∫ x, η x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) := by
  have hnorm := Submission.unit_orientation_norm_le_one
  intro P n U R hfin
  set D : ℕ → Euclid P → MultiVector P n := fun r x =>
    (R r).carrier.indicator (fun y => ((R r).mult y : ℝ) • (R r).orient y) x with hD
  set g : ℕ → Euclid P → ℝ := fun r x =>
    (R r).carrier.indicator (fun y => ((R r).mult y : ℝ)) x with hg
  have hg_nonneg : ∀ r x, 0 ≤ g r x := fun r x =>
    Set.indicator_nonneg (fun y _ => Nat.cast_nonneg _) x
  have hmult_meas : ∀ r, Measurable (fun y => ((R r).mult y : ℝ)) := fun r =>
    measurable_from_nat.comp (R r).measurable_mult
  have hg_meas : ∀ r, Measurable (g r) := fun r =>
    (hmult_meas r).indicator (R r).measurableSet_carrier
  -- ∫⁻ g_r dHⁿ = μ_{R_r}(M_r) ≤ μ_{R_r}(U)
  have hg_lint : ∀ r, ∫⁻ x, ENNReal.ofReal (g r x) ∂μHE[n] ≤ (R r).measure U := by
    intro r
    have hM := (R r).measurableSet_carrier
    have h1 : (fun x => ENNReal.ofReal (g r x)) =
        (R r).carrier.indicator (fun y => ((R r).mult y : ℝ≥0∞)) := by
      funext x
      by_cases hx : x ∈ (R r).carrier <;> simp [g, hx]
    calc ∫⁻ x, ENNReal.ofReal (g r x) ∂μHE[n]
        = ∫⁻ x in (R r).carrier, ((R r).mult x : ℝ≥0∞) ∂μHE[n] := by
          rw [h1, lintegral_indicator hM]
      _ = (R r).measure (R r).carrier := by
          rw [IMRep.measure, withDensity_apply _ hM, Measure.restrict_restrict hM, inter_self]
      _ ≤ (R r).measure U := measure_mono (R r).carrier_subset
  have hsum_lint : ∫⁻ x, ∑' r, ENNReal.ofReal (g r x) ∂μHE[n] ≠ ∞ := by
    rw [lintegral_tsum (fun r => (hg_meas r).ennreal_ofReal.aemeasurable)]
    exact ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum hg_lint)
  have hfinite : ∀ᵐ x ∂μHE[n], ∑' r, ENNReal.ofReal (g r x) < ∞ :=
    ae_lt_top (Measurable.ennreal_tsum fun r => (hg_meas r).ennreal_ofReal) hsum_lint
  have hg_summ : ∀ᵐ x ∂μHE[n], Summable (fun r => g r x) := by
    filter_upwards [hfinite] with x hx
    have := ENNReal.summable_toReal hx.ne
    simpa [ENNReal.toReal_ofReal (hg_nonneg _ x)] using this
  -- ‖D_r(x)‖ ≤ g_r(x) a.e., from ‖ξ‖ ≤ 1 for unit orientations
  have hD_bound : ∀ r, ∀ᵐ x ∂μHE[n], ‖D r x‖ ≤ g r x := by
    intro r
    have h := (R r).orients
    rw [ae_restrict_iff' (R r).measurableSet_carrier] at h
    filter_upwards [h] with x hx
    by_cases hxM : x ∈ (R r).carrier
    · obtain ⟨Q, -, hQ⟩ := hx hxM
      have h1 := hnorm P n Q _ hQ
      simp only [D, g, Set.indicator_of_mem hxM]
      calc ‖((R r).mult x : ℝ) • (R r).orient x‖
          ≤ ‖((R r).mult x : ℝ)‖ * ‖(R r).orient x‖ := ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ ‖((R r).mult x : ℝ)‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = ((R r).mult x : ℝ) := by rw [mul_one, Real.norm_natCast]
    · simp only [D, g, Set.indicator_of_notMem hxM]
      exact ContinuousLinearMap.opNorm_zero.le
  have hD_bound' : ∀ᵐ x ∂μHE[n], ∀ r, ‖D r x‖ ≤ g r x := ae_all_iff.2 hD_bound
  have hD_summ : ∀ᵐ x ∂μHE[n], Summable (fun r => D r x) := by
    filter_upwards [hD_bound', hg_summ] with x h1 h2
    exact Summable.of_norm_bounded (E := MultiVector P n) h2 h1
  refine ⟨fun x => ∑' r, D r x, ?_, ?_⟩
  · filter_upwards [hD_summ] with x hx
    exact hx.hasSum
  · intro ω
    set w : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n) with hw
    have hw_cont : Continuous w := ContDiff.continuous ω.property.1.1
    obtain ⟨B, hB⟩ : ∃ B, ∀ x, ‖w x‖ ≤ B :=
      hw_cont.bounded_above_of_compact_support ω.property.1.2
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    have hDr_meas : ∀ r, AEStronglyMeasurable (D r) μHE[n] := by
      intro r
      refine (aestronglyMeasurable_indicator_iff (R r).measurableSet_carrier).2 ?_
      exact (hmult_meas r).aestronglyMeasurable.smul (R r).aestronglyMeasurable_orient
    have hF_meas : ∀ r, AEStronglyMeasurable (fun x => D r x (w x)) μHE[n] := fun r =>
      isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        ((hDr_meas r).prodMk hw_cont.aestronglyMeasurable)
    have h_bound : ∀ r, ∀ᵐ x ∂μHE[n], ‖D r x (w x)‖ ≤ B * g r x := by
      intro r
      filter_upwards [hD_bound r] with x hx
      calc ‖D r x (w x)‖ ≤ ‖D r x‖ * ‖w x‖ := (D r x).le_opNorm _
        _ ≤ g r x * B := mul_le_mul hx (hB x) (norm_nonneg _) (hg_nonneg r x)
        _ = B * g r x := mul_comm _ _
    have h_summ : ∀ᵐ x ∂μHE[n], Summable (fun r => B * g r x) :=
      hg_summ.mono fun x hx => hx.mul_left B
    have h_int : Integrable (fun x => ∑' r, B * g r x) μHE[n] := by
      have hG : Integrable (fun x => (∑' r, ENNReal.ofReal (g r x)).toReal) μHE[n] :=
        integrable_toReal_of_lintegral_ne_top
          (Measurable.ennreal_tsum fun r => (hg_meas r).ennreal_ofReal).aemeasurable hsum_lint
      refine (hG.const_mul B).congr ?_
      filter_upwards [hg_summ] with x hx
      rw [tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun r => hg_nonneg r x) hx,
        ENNReal.toReal_ofReal (tsum_nonneg fun r => hg_nonneg r x)]
    have hlim : ∀ᵐ x ∂μHE[n], HasSum (fun r => D r x (w x)) ((∑' r, D r x) (w x)) := by
      filter_upwards [hD_summ] with x hx
      exact hx.hasSum.mapL (ContinuousLinearMap.apply ℝ ℝ (w x))
    have hHS := hasSum_integral_of_dominated_convergence (fun r x => B * g r x) hF_meas
      h_bound h_summ h_int hlim
    convert hHS using 1
    funext r
    have hM := (R r).measurableSet_carrier
    have h1 : (fun x => D r x (w x)) =
        (R r).carrier.indicator (fun x => ((R r).mult x : ℝ) * (R r).orient x (w x)) := by
      funext x
      by_cases hx : x ∈ (R r).carrier <;> simp [D, hx]
    rw [h1, integral_indicator hM]
    rfl

Implementation notes (Lean v4.35.0-rc3, Mathlib 25730c7c, after import GMT.Ch07.Submission): for MultiVector P n, generic normed-group lemmas may fail to find instances; use ContinuousLinearMap.opNorm_smul_le / ContinuousLinearMap.opNorm_zero instead of norm_smul / norm_zero, Summable.of_norm_bounded (E := MultiVector P n), and the explicit instance @PseudoEMetricSpace.pseudoMetrizableSpace _ (inferInstance : PseudoEMetricSpace (MultiVector P n)) before aestronglyMeasurable_of_tendsto_ae; Nat.measurable_floor is not imported, use Nat.floor_mono.measurable.

## Key steps

1. ∫ 1_{M_r}θ_r dHⁿ = μ_{R_r}(M_r) ≤ μ_{R_r}(U), so Σ_r 1_{M_r}θ_r has integral ≤ Σ_r μ_{R_r}(U) < ∞ and is finite Hⁿ-a.e.
2. ‖ξ_r‖ ≤ 1 Hⁿ-a.e. on M_r (orientation_norm) gives ‖D_{R_r}‖ ≤ 1_{M_r}θ_r, so Σ_r D_{R_r}(x) converges absolutely Hⁿ-a.e.; η := Σ'_r D_{R_r} gives (a).
3. For ω ∈ 𝒟ⁿ(U) and B = sup‖ω‖, dominated convergence for series with bounds B·1_{M_r}θ_r gives HasSum (∫ D_{R_r}(ω) dHⁿ) (∫ η(ω) dHⁿ).
4. ∫ D_{R_r}(x)(ω(x)) dHⁿ = ∫_{M_r} θ_r ξ_r(ω) dHⁿ = R_r.action(ω) by integral_indicator, giving (b).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `sed -n 880,945p book/chapter-06.txt (Simon Ch. 6, Lemma 3.13 and its printed proof)`
- `sed -n 1,116p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; sed -n 100,200p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean (massAdmissibleOn, massOn, mass, le_massOn, GeometricCurrentOn, TestFormOn)`
- `rg -n 'theorem countablyRectifiable_of_measure_zero|theorem CountablyRectifiable.mono|theorem countablyRectifiable_iUnion|theorem HasApproximateTangentSpaceAt.unique' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `python3 -I scans of dag.json (re-read at 2026-10-13T13:51Z): accepted declarations mentioning IMRep / IsIntegerMultiplicity / IsUnitOrientationOf; status and byte-identical frozen type of the 7 reused declarations (all still accepted); cmc_fc_series_current, cmcdt_im_series and cmcdt_ims_imrep_tsum are speculative-ready, not accepted, hence not reusable; no collision for dor_lmb_fc_ims_*`
- `grep -rl dor_lmb_fc_ims_ nodes decomposition-reopenings (no match)`
- `git show 0af9ed59:GMT/Ch07/Submission.lean (theorem Submission.rsdic_exists_imrep_int_combination); git show d76960cc:GMT/Ch07/Submission.lean (PseudoMetrizableSpace (MultiVector P n) instance workaround)`
- `rg -n in local-references/123e8435b4a2469b/mathlib: hasSum_integral_of_dominated_convergence, integral_tsum, lintegral_tsum, lintegral_liminf_le, ae_lt_top, aestronglyMeasurable_of_tendsto_ae, measure_eq_zero_iff_ae_notMem, Set.Finite.isClosed, liminf_le_of_frequently_le', UniformSpace.pseudoMetrizableSpace, Summable.of_norm_bounded, HasSum.mapL`
- `cat nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-im-series-a1/decomposition-audit-v1.json (parallel im_series split via a common orientation, accepted)`
- `python3 -I gmt-compare.py contract_scope replay and lean_contract.validate_lean_statement on all 10 lean_statement strings`
- `lake env lean /tmp/ims-decomp/lean/{Types,Assembly,ChildA,ChildB,ChildC,ChildC_noHB,Final}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-ac22a8c7fb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-im-series-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ims-decomp/lean/Assembly.lean`
- `/tmp/ims-decomp/lean/ChildA.lean`
- `/tmp/ims-decomp/lean/ChildB.lean`
- `/tmp/ims-decomp/lean/ChildC.lean`
- `/tmp/ims-decomp/lean/Final.lean`

Snapshot: project b4d606db and mathlib 25730c7c. The snapshot Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.
Neither SimonGMT nor the snapshot contains Simon's Lemma 3.13 or any completeness result for IM currents. Seven comparator-accepted DAG declarations supply the needed IMRep calculus and are reused with byte-identical frozen types: dor_imrep_massOn_eq_measure_and_support (C1), cmc_imRep_locality_restrict_sub (IMC), dor_ims_unitOrientation_dual (UOD), unit_orientation_norm_le_one, rsdic_exists_imrep_int_combination, dor_lmb_ic_measure_le_of_weighted_orient_eq and rsdic_unitOrientation_eq_or_eq_neg. cmc_fc_series_current has the type of supplied step 1 but is only speculative-ready, so it is not reused; the assembly gets Y from (IMC)(b) instead. The speculative-ready cmcdt_ims_imrep_tsum overlaps the three new children taken together and is likewise not reusable. SimonGMT supplies countablyRectifiable_of_measure_zero / iUnion / mono and HasApproximateTangentSpaceAt.unique. The snapshot Mathlib supplies dominated convergence for series, Fatou, a.e. limits of a.e. strongly measurable maps, and Summable.of_norm_bounded.
Lean: all ten child types elaborate in the replayed comparator scope. The three new children and the exact parent type are kernel-checked conditionally on the reused frozen types with axioms [propext, Classical.choice, Quot.sound], and they compile as drop-in Submission declarations.
