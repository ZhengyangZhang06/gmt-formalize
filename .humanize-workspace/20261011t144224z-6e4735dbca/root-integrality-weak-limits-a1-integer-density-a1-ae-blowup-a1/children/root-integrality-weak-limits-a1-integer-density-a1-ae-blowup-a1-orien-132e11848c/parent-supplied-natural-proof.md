# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1`
- Child DAG node: `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.orientation_error_vanishes-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 6 (the normalized Lebesgue point, condition (G2)) and 8 (the error term) of the parent proof. The outputs of the parent's steps 3 and 5 enter here as the hypotheses (i) and (ii).

Notation:
- Hⁿ := μHE[n] on ℝ^P, and ν := Hⁿ⌞M;
- a(s) := ∫⁻_{M∩B̄_s(x)} ofReal(θ(y))‖ξ(y) − ξ(x)‖ₑ dHⁿ(y);
- b(s) := ∫⁻_{M∩B̄_s(x)} ofReal(θ) dHⁿ;
- ε(s) := a(s)/ofReal(sⁿ) ∈ [0, ∞].

1. An inequality in [0, ∞]. Let a', b', d ∈ [0, ∞] and c ∈ ℝ≥0 with 0 < d < ∞, b' ≤ c·d and a'/b' < 1. Then a'/d ≤ c·(a'/b').
Proof: by ENNReal.div_le_iff (d ≠ 0, d ≠ ∞) it suffices to show a' ≤ c·(a'/b')·d.
- If b' = 0, then a' = 0: otherwise a'/b' = ∞ (ENNReal.div_zero), contradicting a'/b' < 1. The inequality is then trivial.
- If b' ≠ 0, then b' ≤ c·d < ∞, so a' = (a'/b')·b' ≤ (a'/b')·c·d (ENNReal.div_mul_cancel).

2. ε(s) → 0 as s → 0⁺. The set {t : t < 1} is a neighbourhood of 0 in [0, ∞]. So by (i) and (ii), for all s in a set belonging to 𝓝[>] 0 we have s > 0, b(s) ≤ C·ofReal(sⁿ) and a(s)/b(s) < 1. For such s, d := ofReal(sⁿ) satisfies 0 < d < ∞, and step 1 gives 0 ≤ ε(s) ≤ C·(a(s)/b(s)). Since C < ∞, (ii) gives C·(a(s)/b(s)) → C·0 = 0 (ENNReal.Tendsto.const_mul). By the squeeze theorem, ε(s) → 0.

3. Radius and bound. tsupport ω is compact, hence bounded, so it lies in some closed ball B̄_{R₀}(0). Put R := max(R₀, 1) > 0; then tsupport ω ⊆ B̄_R(0). Since ω is continuous with compact support, there is B with ‖ω(z)‖ ≤ B for all z (HasCompactSupport.exists_bound_of_continuous). Also B ≥ ‖ω(0)‖ ≥ 0.

4. Pointwise bound. Fix r > 0, put c_r := (rⁿ)⁻¹ ≥ 0, and let F_r(y) := θ(y)·(ξ(y) − ξ(x))(c_r•ω(r⁻¹•(y − x))).
 (a) If y ∉ B̄_{Rr}(x), then ‖r⁻¹•(y − x)‖ = r⁻¹‖y − x‖ > R. So r⁻¹•(y − x) ∉ tsupport ω, hence ω(r⁻¹•(y − x)) = 0 and F_r(y) = 0.
 (b) If y ∈ M, then θ(y) ≥ 0. Using |w(α)| ≤ ‖w‖‖α‖ for n-vectors w and ‖c•α‖ = |c|‖α‖, we get |F_r(y)| ≤ θ(y)‖ξ(y) − ξ(x)‖·c_r·B. In [0, ∞]:
  ‖F_r(y)‖ₑ ≤ ofReal(c_r·B)·ofReal(θ(y))‖ξ(y) − ξ(x)‖ₑ.
 Since M is null-measurable, ν-a.e. y lies in M. So by (a) and (b), for ν-a.e. y:
  ‖F_r(y)‖ₑ ≤ 1_{B̄_{Rr}(x)}(y)·ofReal(c_r·B)·ofReal(θ(y))‖ξ(y) − ξ(x)‖ₑ.

5. Integral bound. Let E(r) := ∫_M F_r dHⁿ. Then
  ‖E(r)‖ₑ ≤ ∫⁻_M ‖F_r‖ₑ dHⁿ   [enorm_integral_le_lintegral_enorm; valid whether or not F_r is integrable, since the Bochner integral is otherwise 0]
  ≤ ∫⁻_M 1_{B̄_{Rr}(x)}·ofReal(c_r·B)·ofReal(θ)‖ξ − ξ(x)‖ₑ dHⁿ   [step 4, lintegral_mono_ae]
  = ofReal(c_r·B)·∫⁻_{M∩B̄_{Rr}(x)} ofReal(θ)‖ξ − ξ(x)‖ₑ dHⁿ   [lintegral_indicator on the measurable ball, Measure.restrict_restrict, lintegral_const_mul' with a finite constant]
  = ofReal(c_r·B)·a(Rr).
Since 0 < ofReal((Rr)ⁿ) < ∞, a(Rr) = ε(Rr)·ofReal((Rr)ⁿ). Also ofReal(c_r·B)·ofReal((Rr)ⁿ) = ofReal((rⁿ)⁻¹·B·Rⁿrⁿ) = ofReal(B·Rⁿ). Hence ‖E(r)‖ₑ ≤ ofReal(B·Rⁿ)·ε(Rr) for every r > 0.

6. Limit. Since R > 0, the map r ↦ Rr sends (0, ∞) into (0, ∞) and tends to 0, so it tends to 0 within (0, ∞) as r → 0⁺. By step 2, ε(Rr) → 0, and hence ofReal(B·Rⁿ)·ε(Rr) → 0, the constant being finite. By step 5 and the squeeze theorem, ‖E(r)‖ₑ → 0 as r → 0⁺, i.e. E(r) → 0 in ℝ (tendsto_zero_iff_enorm_tendsto_zero). ∎

Formalization note: for n-vectors, the bridge between ofReal ‖·‖ and ‖·‖ₑ must be written ofReal_norm_eq_enorm (E := NVector (Eucl P) n). Without the explicit E, the instance paths of the norm on NVector (ContinuousLinearMap.hasOpNorm versus the normed-group norm) do not unify. Avoid `set` over large integral expressions, which causes heartbeat timeouts.

Appendix (formalization aid; not part of the mathematical argument). The following script was kernel-checked in scratch against the frozen environment (Lean v4.35.0-rc3, Mathlib 25730c7c, `import GMT.Ch06.Submission`, inside `namespace GMT.Ch06` with the contract's `open`s) and depends only on propext, Classical.choice and Quot.sound:

theorem Submission.ind_ab_orientation_error_vanishes :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (x : Eucl P) (ω : Eucl P → Covector (Eucl P) n), NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ y ∈ M, 0 ≤ θ y) → Continuous ω → HasCompactSupport ω → (∃ C : ℝ≥0, ∀ᶠ s in 𝓝[>] (0 : ℝ), ∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)) ≤ C * ENNReal.ofReal (s ^ n)) → Tendsto (fun s : ℝ => (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) / (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)))) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => ∫ y in M, θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x))) ∂(μHE[n] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0) := by
  intro P n M θ ξ x ω hM hθ hω hωc hgrowth hratio
  obtain ⟨C, hC⟩ := hgrowth
  -- an elementary ENNReal estimate
  have key : ∀ (a b d : ℝ≥0∞) (c : ℝ≥0), d ≠ 0 → d ≠ ⊤ → b ≤ c * d → a / b < 1 →
      a / d ≤ c * (a / b) := by
    intro a b d c hd0 hdtop hbd hab
    rw [ENNReal.div_le_iff hd0 hdtop]
    by_cases hb0 : b = 0
    · have ha0 : a = 0 := by
        by_contra hne
        rw [hb0, ENNReal.div_zero hne] at hab
        exact absurd hab (not_lt.2 le_top)
      rw [ha0]; exact zero_le
    · have hbtop : b ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hdtop) hbd
      calc a = (a / b) * b := (ENNReal.div_mul_cancel hb0 hbtop).symm
        _ ≤ (a / b) * ((c : ℝ≥0∞) * d) := by gcongr
        _ = (c : ℝ≥0∞) * (a / b) * d := by ring
  -- Step 1: the normalized error tends to 0
  have hε : Tendsto (fun s : ℝ => (∫⁻ y in M ∩ closedBall x s,
      ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) / ENNReal.ofReal (s ^ n))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), (∫⁻ y in M ∩ closedBall x s,
        ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) /
          ENNReal.ofReal (s ^ n) ≤
        (C : ℝ≥0∞) * ((∫⁻ y in M ∩ closedBall x s,
          ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) /
            (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)))) := by
      filter_upwards [hC, hratio.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 from zero_lt_one)),
        self_mem_nhdsWithin] with s hbs hrs hs
      have hs' : (0 : ℝ) < s := hs
      exact key _ _ _ C (ENNReal.ofReal_pos.2 (pow_pos hs' n)).ne' ENNReal.ofReal_ne_top hbs hrs
    have h2 := ENNReal.Tendsto.const_mul hratio (Or.inr (ENNReal.coe_ne_top (r := C)))
    rw [mul_zero] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
      (Eventually.of_forall fun _ => zero_le) h1
  -- Step 2: radius and bound of ω
  obtain ⟨R₀, hR₀⟩ := (hωc.isCompact.isBounded).subset_closedBall (0 : Eucl P)
  obtain ⟨R, hRpos, hRsub⟩ : ∃ R : ℝ, 0 < R ∧ tsupport ω ⊆ closedBall (0 : Eucl P) R :=
    ⟨max R₀ 1, lt_max_of_lt_right one_pos,
      hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
  obtain ⟨B, hB⟩ := hωc.exists_bound_of_continuous hω
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  -- Step 3/4: integral bound
  have hbound : ∀ r : ℝ, 0 < r →
      ‖∫ y in M, θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x))) ∂(μHE[n] : Measure (Eucl P))‖ₑ ≤
        ENNReal.ofReal ((r ^ n)⁻¹ * B) *
          ∫⁻ y in M ∩ closedBall x (R * r), ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ
            ∂(μHE[n] : Measure (Eucl P)) := by
    intro r hr
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have hpt : ∀ᵐ y ∂((μHE[n] : Measure (Eucl P)).restrict M),
        ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ₑ ≤
          (closedBall x (R * r)).indicator
            (fun y => ENNReal.ofReal ((r ^ n)⁻¹ * B) * (ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ)) y := by
      filter_upwards [ae_restrict_mem₀ hM] with y hy
      by_cases hyB : y ∈ closedBall x (R * r)
      · rw [indicator_of_mem hyB]
        have hcn : 0 ≤ (r ^ n)⁻¹ := inv_nonneg.2 (pow_nonneg hr.le n)
        have hreal : ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ ≤
            ((r ^ n)⁻¹ * B) * (θ y * ‖ξ y - ξ x‖) := by
          rw [norm_mul, Real.norm_of_nonneg (hθ y hy)]
          have hθy := hθ y hy
          calc θ y * ‖(ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖
              ≤ θ y * (‖ξ y - ξ x‖ * ‖(r ^ n)⁻¹ • ω (r⁻¹ • (y - x))‖) := by
                gcongr
                exact (ξ y - ξ x).le_opNorm _
            _ ≤ θ y * (‖ξ y - ξ x‖ * ((r ^ n)⁻¹ * B)) := by
                gcongr
                rw [norm_smul, Real.norm_of_nonneg hcn]
                gcongr
                exact hB _
            _ = ((r ^ n)⁻¹ * B) * (θ y * ‖ξ y - ξ x‖) := by ring
        calc ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ₑ
            = ENNReal.ofReal ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ :=
              (ofReal_norm_eq_enorm _).symm
          _ ≤ ENNReal.ofReal (((r ^ n)⁻¹ * B) * (θ y * ‖ξ y - ξ x‖)) := ENNReal.ofReal_le_ofReal hreal
          _ = ENNReal.ofReal ((r ^ n)⁻¹ * B) * (ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ) := by
              have he : ENNReal.ofReal ‖ξ y - ξ x‖ = ‖ξ y - ξ x‖ₑ :=
                ofReal_norm_eq_enorm (E := NVector (Eucl P) n) _
              rw [ENNReal.ofReal_mul (mul_nonneg hcn hB0), ENNReal.ofReal_mul (hθ y hy), he]
      · rw [indicator_of_notMem hyB]
        have hω0 : ω (r⁻¹ • (y - x)) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hmem
          apply hyB
          have h1 := hRsub hmem
          rw [mem_closedBall, dist_zero_right, norm_smul,
            Real.norm_of_nonneg (inv_nonneg.2 hr.le), inv_mul_le_iff₀ hr] at h1
          rw [mem_closedBall, dist_eq_norm]
          linarith
        simp [hω0]
    calc ∫⁻ y in M, ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ₑ
          ∂(μHE[n] : Measure (Eucl P))
        ≤ ∫⁻ y in M, (closedBall x (R * r)).indicator
            (fun y => ENNReal.ofReal ((r ^ n)⁻¹ * B) * (ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ)) y
            ∂(μHE[n] : Measure (Eucl P)) := lintegral_mono_ae hpt
      _ = ∫⁻ y in M ∩ closedBall x (R * r),
            ENNReal.ofReal ((r ^ n)⁻¹ * B) * (ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ)
            ∂(μHE[n] : Measure (Eucl P)) := by
          rw [lintegral_indicator measurableSet_closedBall,
            Measure.restrict_restrict measurableSet_closedBall, inter_comm]
      _ = ENNReal.ofReal ((r ^ n)⁻¹ * B) * ∫⁻ y in M ∩ closedBall x (R * r),
            ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hbound2 : ∀ r : ℝ, 0 < r →
      ‖∫ y in M, θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x))) ∂(μHE[n] : Measure (Eucl P))‖ₑ ≤
        ENNReal.ofReal (B * R ^ n) * ((∫⁻ y in M ∩ closedBall x (R * r),
          ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) /
            ENNReal.ofReal ((R * r) ^ n)) := by
    intro r hr
    refine (hbound r hr).trans (le_of_eq ?_)
    have hRr : 0 < R * r := mul_pos hRpos hr
    have hd0 : ENNReal.ofReal ((R * r) ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hRr n)).ne'
    have hdt : ENNReal.ofReal ((R * r) ^ n) ≠ ⊤ := ENNReal.ofReal_ne_top
    conv_lhs => rw [← ENNReal.div_mul_cancel hd0 hdt (b := ∫⁻ y in M ∩ closedBall x (R * r),
      ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P)))]
    rw [mul_comm _ (ENNReal.ofReal ((R * r) ^ n)), ← mul_assoc,
      ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 (pow_nonneg hr.le n)) hB0)]
    congr 2
    rw [mul_pow]
    field_simp
  have hcomp : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h1 : Tendsto (fun r : ℝ => R * r) (𝓝 0) (𝓝 (R * 0)) := tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hRpos hr
  have hlim := ENNReal.Tendsto.const_mul (hε.comp hcomp)
    (Or.inr (ENNReal.ofReal_ne_top (r := B * R ^ n)))
  rw [mul_zero] at hlim
  rw [tendsto_zero_iff_enorm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hbound2 r hr

## Key steps

1. ENNReal inequality: if 0 < d < ∞, b ≤ c·d and a/b < 1, then a/d ≤ c·(a/b) (b = 0 forces a = 0).
2. Hence ε(s) := a(s)/ofReal(sⁿ) ≤ C·(a(s)/b(s)) eventually, so ε(s) → 0.
3. Choose R > 0 with tsupport ω ⊆ B̄_R(0) and a bound B ≥ 0 for ‖ω‖.
4. For r > 0, the integrand vanishes off B̄_{Rr}(x) and is bounded on M by (rⁿ)⁻¹B·θ‖ξ − ξ(x)‖.
5. ‖E(r)‖ₑ ≤ ∫⁻_M ‖F_r‖ₑ ≤ ofReal((rⁿ)⁻¹B)·a(Rr) = ofReal(BRⁿ)·ε(Rr).
6. As r → 0⁺, Rr → 0⁺, so ε(Rr) → 0 and E(r) → 0.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff project/GMT/Ch06/Contract.lean project/GMT/Ch06/Submission.lean (identical); diff snapshot Contract.lean vs workspace GMT/Ch06/Contract.lean (identical)`
- `rg -n 'ind_ab_' project/ and simongmt/Poincare (no match); python3 scan of dag.json lean_name and theorems lists for ind_ab_* (362 nodes, no match); git grep -l 'ind_ab_' over all local branch heads (no match)`
- `python3 scan of dag.json for the accepted lpf_wtc_blowup_setIntegral_image, fiw_ims_tt_unit_bound, ltg_tau_integrable, lpf_wtc_density_bound_of_tangent, lpf_wtc_wtt_remainder_vanishes and lpf_wtc_wtt_blowup_integral_split, and for the sibling ind_* statements`
- `sed -n '/def blowUpMap/,/^$/p;/def HasWeightedApproximateTangentSpaceAt/,/^$/p' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'abbrev NVector|def simpleNVector|abbrev Covector|abbrev DifferentialForm' simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean Chapter06/Forms.lean`
- `rg -n 'HasWeightedApproximateTangentSpaceAt|theorem .*blowUp|ae_tendsto_lintegral_enorm_sub_div|vitaliFamily|Besicovitch|withDensity' simongmt/Poincare -g '*.lean'`
- `rg -n 'protected def vitaliFamily|theorem tendsto_filterAt' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean; rg -n 'theorem ae_tendsto_lintegral_enorm_sub_div' mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `rg -n 'lemma withDensity_absolutelyContinuous|setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀|theorem withDensity_apply' mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `rg -n 'aestronglyMeasurable_iUnion_iff|Continuous.comp_aestronglyMeasurable₂|IntegrableOn.of_ae_sdiff_eq_zero|Measure.integrableOn_of_bounded|Integrable.lintegral_lt_top|enorm_integral_le_lintegral_enorm|ofReal_integral_eq_lintegral_ofReal|sigmaFinite_of_locallyFinite|isBoundedBilinearMap_apply|HasCompactMulSupport.exists_bound_of_continuous|div_le_iff|div_mul_cancel|div_zero|instHasBesicovitchCovering' in the snapshot mathlib/Mathlib files listed`
- `git show <lpf blow-up branch>:GMT/Ch06/Submission.lean (accepted proof of Submission.lpf_wtc_blowup_setIntegral_image)`
- `sed -n 2400,2440p book/chapter-06.txt (printed Proof of 8.2, display (7))`
- `verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') and lean_contract.validate_lean_statement on the 4 child statements`
- `lake env lean /tmp/ab-decomp-scratch/{Stmts,Pairing,Enorm,C1,C24,C3,Assembly,Full}.lean (#synth, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-ae-blowup-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ab-decomp-scratch/Stmts.lean`
- `/tmp/ab-decomp-scratch/Assembly.lean`
- `/tmp/ab-decomp-scratch/Full.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) has the frozen Ch06 Contract, byte-identical to its Submission and to the workspace Contract.

Available API and reuse:
- The contract's own scope opens only CountablyRectifiable and HasWeightedApproximateTangentSpaceAt from Chapter03. The statements therefore spell blow-ups as r⁻¹ • (y - x), not blowUpMap.
- SimonGMT Chapter03/Rectifiable.lean supplies blowUpMap and the definition of HasWeightedApproximateTangentSpaceAt (finrank plus a C_c blow-up limit).
- Chapter06 supplies NVector = Covector →L ℝ and simpleNVector (built with mkContinuous, bound ∏‖v_i‖).
- SimonGMT has no weighted Lebesgue-point or rescaled-tangent lemma for general (M, θ). Chapter04/WeightedBlowUp.lean (tendsto_rescaled_weight_of_weighted_approximateTangent) is a varifold-specific analogue of child 1. It is not imported by the contract and does not apply to arbitrary M and θ.
- The snapshot Mathlib supplies everything children 3 and 4 need: Besicovitch.vitaliFamily, Besicovitch.tendsto_filterAt, VitaliFamily.ae_tendsto_lintegral_enorm_sub_div, withDensity_apply, withDensity_absolutelyContinuous(') and setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀; aestronglyMeasurable_iUnion_iff, IntegrableOn.of_ae_sdiff_eq_zero, Measure.integrableOn_of_bounded, Integrable.lintegral_lt_top, enorm_integral_le_lintegral_enorm, ofReal_integral_eq_lintegral_ofReal and sigmaFinite_of_locallyFinite; instHasBesicovitchCovering, isBoundedBilinearMap_apply, the ENNReal division lemmas and HasCompactSupport.exists_bound_of_continuous.
- Accepted DAG declarations reused with identical frozen types: Submission.lpf_wtc_blowup_setIntegral_image (child 1; its proof was inspected on its branch). Optionally Submission.fiw_ims_tt_unit_bound (unit bound, child 3 and the parent).
- No ind_ab_* names exist in the DAG, the snapshot, SimonGMT or the local branches.

Scratch kernel checks:
- All 4 child statements pass validate_lean_statement and elaborate in the contract_scope replay.
- The parent assembly and complete proofs of all 4 children check with only propext, Classical.choice and Quot.sound. So do the comparator-style `exact Submission.X` replays of all 4 children and of the parent ind_ae_blowup_limit.
