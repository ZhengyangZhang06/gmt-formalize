# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1.weak_conv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 10 (weak convergence) of the parent proof of cmc_fc_localize, stated abstractly. In the parent: g = dist(·, closure W); s is the good level from cmc_fc_good_slice; μ_j = R_{φ(j)}.measure and ξ_j = R_{φ(j)}.orient; T_j = T_{φ(j)}; T'_j = A_{φ(j)}(s), the slice current T_{φ(j)}⌞{g < s}; μ = R_T.measure, ξ = R_T.orient and T' = T⌞{g < s}. The no-concentration hypothesis (H6) is conclusion (ii) of good_slice transported along g.
Notation: G := {g < s}; |α| := covectorEuclideanNorm α; ⟨β, ζ⟩ := ζ(β).
Hypotheses:
(H0) g is continuous.
(H1) μ_j(G) < ∞ for all j, and μ(G) < ∞.
(H2) ξ_j is μ_j-a.e. strongly measurable, and ξ is μ-a.e. strongly measurable.
(H3) For μ_j-a.e. x, |⟨α, ξ_j(x)⟩| ≤ |α| for all α; likewise for μ-a.e. x and ξ.
(H4) For every ω ∈ 𝒟^d(U) (Bochner integrals): T_j(ω) = ∫⟨ω, ξ_j⟩ dμ_j, T(ω) = ∫⟨ω, ξ⟩ dμ, T'_j(ω) = ∫_G⟨ω, ξ_j⟩ dμ_j, T'(ω) = ∫_G⟨ω, ξ⟩ dμ.
(H5) T_j ⇀ T.
(H6) For every ε ∈ (0, ∞] there is δ > 0 such that μ_j({s - δ ≤ g ≤ s}) ≤ ε for all sufficiently large j.
Claim: T'_j(ω) → T'(ω) for every ω ∈ 𝒟^d(U).
1. (A bound for ω.) Fix ω ∈ 𝒟^d(U); ω also denotes the underlying smooth compactly supported form. The coefficient norm is |α| = sqrt(Σ_{I strictly increasing} α(e_{I(1)}, …, e_{I(d)})²). It is continuous in α: each evaluation α ↦ α(v) at a fixed tuple v is continuous (continuous_eval_const), and squares, finite sums and sqrt are continuous. So x ↦ |ω(x)| is continuous. It has compact support because ω does and |0| = 0 (HasCompactSupport.comp_left). Hence it is bounded (HasCompactSupport.exists_bound_of_continuous). Fix c ∈ ℝ with |ω(x)| ≤ c for all x; then c ≥ |ω(0)| ≥ 0.
2. (Cutoff estimate.) Claim: let ν be a measure on ℝ^P with ν(G) < ∞, and ζ a ν-a.e. strongly measurable d-vector field with |⟨α, ζ(x)⟩| ≤ |α| for all α, for ν-a.e. x. Let r ∈ ℝ, and let χ : ℝ^P → [0, 1] be continuous with χ = 1 on {g ≤ r} and χ = 0 on {g ≥ s}. Then |∫_G⟨ω, ζ⟩ dν - ∫⟨χω, ζ⟩ dν| ≤ c·ν({r < g < s}). Here ν({r < g < s}) ≤ ν(G) < ∞, and its real value is used.
 Proof of the claim.
 (a) F(x) := ⟨ω(x), ζ(x)⟩ is ν-a.e. strongly measurable: (L, v) ↦ L(v) is jointly continuous (Continuous.clm_apply); x ↦ (ζ(x), ω(x)) is ν-a.e. strongly measurable (AEStronglyMeasurable.prodMk, ω continuous); and continuous maps preserve a.e. strong measurability (Continuous.comp_aestronglyMeasurable).
 (b) For ν-a.e. x, |F(x)| ≤ |ω(x)| ≤ c (hypothesis with α := ω(x), and step 1). Also |χ(x)F(x)| ≤ c, since 0 ≤ χ ≤ 1.
 (c) Since ν(G) < ∞, F and χF are integrable on G (Measure.integrableOn_of_bounded).
 (d) ⟨χ(x)ω(x), ζ(x)⟩ = χ(x)F(x) by linearity of ζ(x) (map_smul). χF vanishes outside G, where g ≥ s and so χ = 0. Hence ∫χF dν = ∫_G χF dν (setIntegral_eq_integral_of_forall_compl_eq_zero).
 (e) By (c) and linearity, ∫_G F dν - ∫_G χF dν = ∫_G (1 - χ)F dν (integral_sub).
 (f) (1 - χ)F vanishes on G ∖ {r < g < s} = G ∩ {g ≤ r}, where χ = 1. Since {r < g < s} ⊆ G and G is Borel, ∫_G (1 - χ)F dν = ∫_{r<g<s} (1 - χ)F dν (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero).
 (g) |(1 - χ)F| ≤ c ν-a.e., because 0 ≤ 1 - χ ≤ 1 and by (b). Since ν({r < g < s}) ≤ ν(G) < ∞, |∫_{r<g<s} (1 - χ)F dν| ≤ c·ν({r < g < s}) (norm_setIntegral_le_of_norm_le_const_ae).
 Combining (d)-(g) proves the claim.
3. Fix ε > 0 and put η := ε/(3(c + 1)) > 0.
4. (Small layer for the limit measure.) For i ∈ ℕ let S_i := {s - 1/(i+1) < g < s}.
 - Each S_i is Borel, since g is continuous.
 - The sequence is decreasing: 1/(k+1) ≤ 1/(i+1) for i ≤ k.
 - μ(S_0) ≤ μ(G) < ∞.
 - ⋂_i S_i = ∅: if g(x) < s, choose i with 1/(i+1) < s - g(x) (exists_nat_one_div_lt), so x ∉ S_i; if g(x) ≥ s, then x ∉ S_0.
 By continuity from above (tendsto_measure_iInter_atTop), μ(S_i) → μ(∅) = 0. So some i has μ(S_i) ≤ ENNReal.ofReal η. Put δ₁ := 1/(i+1) > 0; then μ({s - δ₁ < g < s}) ≤ η.
5. (Small layer along the sequence.) Apply (H6) with ε := ENNReal.ofReal η > 0. This gives δ₂ > 0 and N₂ with μ_j({s - δ₂ ≤ g ≤ s}) ≤ η for all j ≥ N₂.
6. (Cutoff.) Let δ' := min(δ₁, δ₂) > 0. The set {g ≤ s - δ'} is closed and contained in the open set {g < s - δ'/2}, which is its own interior. By the smooth Urysohn lemma there is a C^∞ function χ : ℝ^P → [0, 1] with χ = 1 on {g ≤ s - δ'} and χ = 0 outside {g < s - δ'/2}; in particular χ = 0 on {g ≥ s}. (Mathlib: exists_contMDiffMap_one_nhds_of_subset_interior with the model modelWithCornersSelf ℝ ℝ^P and n = ∞, followed by contMDiff_iff_contDiff.)
7. (The test form χω.) The form χω : x ↦ χ(x)ω(x) is C^∞ (ContDiff.smul). Its support is contained in that of ω, since ω(x) = 0 implies χ(x)ω(x) = 0. So it has compact support (HasCompactSupport.mono'), and tsupport(χω) ⊆ tsupport(ω) ⊆ U (closure_mono). Hence χω ∈ 𝒟^d(U).
8. By (H5) applied to χω there is N₁ with |T_j(χω) - T(χω)| < η for all j ≥ N₁.
9. (Estimate.) Let j ≥ max(N₁, N₂).
 - By (H4), T'_j(ω) = ∫_G⟨ω, ξ_j⟩ dμ_j and T_j(χω) = ∫⟨χω, ξ_j⟩ dμ_j. Step 2 with ν := μ_j, ζ := ξ_j, r := s - δ' applies, by (H1)-(H3) and step 6. Using δ' ≤ δ₂ and step 5, |T'_j(ω) - T_j(χω)| ≤ c·μ_j({s - δ' < g < s}) ≤ c·μ_j({s - δ₂ ≤ g ≤ s}) ≤ cη.
 - Likewise, step 2 with ν := μ and ζ := ξ, together with δ' ≤ δ₁ and step 4, gives |T'(ω) - T(χω)| ≤ c·μ({s - δ' < g < s}) ≤ c·μ({s - δ₁ < g < s}) ≤ cη.
 The passage from the ENNReal bounds to real bounds uses ENNReal.toReal_le_of_le_ofReal.
10. By the triangle inequality, for all j ≥ max(N₁, N₂), |T'_j(ω) - T'(ω)| ≤ |T'_j(ω) - T_j(χω)| + |T_j(χω) - T(χω)| + |T(χω) - T'(ω)| < cη + η + cη = (2c + 1)η < 3(c + 1)η = ε.
11. Since ε > 0 was arbitrary, T'_j(ω) → T'(ω). Since ω was arbitrary, T'_j ⇀ T' (WeaklyConvergesOn). ∎
Formalization notes, from the compiled proof below:
- Do not open scoped ContDiff: it makes ω a token, which breaks binder names. Write the smoothness order as ((⊤ : ℕ∞) : WithTop ℕ∞).
- Use modelWithCornersSelf ℝ (Euclid P) instead of the 𝓘 notation.
- Build χω from pointwise support inclusions (HasCompactSupport.mono', closure_mono). The generic HasCompactSupport.smul_left and tsupport_smul_subset_right took several minutes to elaborate for covector-valued forms.
Appendix (verified Lean). This tactic proof of exactly the frozen statement compiled after import GMT.Ch07.Submission inside namespace GMT.Ch07 with the contract's opens. #print axioms: propext, Classical.choice, Quot.sound.
  intro P d U g s μs μ ξs ξ Ts Ts' T T' hg hμsG hμG hξsm hξm hξsb hξb hTs hT hTs' hT' hconv hconc
  intro ω
  obtain ⟨w, hwdef⟩ : ∃ w : DifferentialForm (Euclid P) d, w = (ω : DifferentialForm (Euclid P) d) :=
    ⟨_, rfl⟩
  have hwc : Continuous w := by rw [hwdef]; exact ω.property.1.1.continuous
  -- Step 1: a bound `c` for the coefficient norm of `ω`.
  have hnc : Continuous fun α : Covector (Euclid P) d => covectorEuclideanNorm α := by
    unfold covectorEuclideanNorm
    apply Continuous.sqrt
    apply continuous_finsetSum
    intro I _
    split_ifs
    · exact (continuous_eval_const _).pow 2
    · exact continuous_const
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ x, covectorEuclideanNorm (w x) ≤ c := by
    have hwcs : HasCompactSupport w := by
      rw [hwdef]
      exact ω.property.1.2
    have hcs : HasCompactSupport (covectorEuclideanNorm ∘ w) :=
      hwcs.comp_left (covectorEuclideanNorm_zero P d)
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous (hnc.comp hwc)
    exact ⟨C, fun x => le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC x)⟩
  have hc0 : 0 ≤ c := le_trans (covectorEuclideanNorm_nonneg _) (hc 0)
  have hGm : MeasurableSet {x | g x < s} := measurableSet_lt hg.measurable measurable_const
  -- Step 2: the cutoff estimate, for an arbitrary measure.
  have key : ∀ (ν : Measure (Euclid P)) (ζ : Euclid P → MultiVector P d) (χ : Euclid P → ℝ) (r : ℝ),
      ν {x | g x < s} < ∞ → AEStronglyMeasurable ζ ν →
      (∀ᵐ x ∂ν, ∀ α : Covector (Euclid P) d, |ζ x α| ≤ covectorEuclideanNorm α) →
      Continuous χ → (∀ x, χ x ∈ Icc (0 : ℝ) 1) → (∀ x, g x ≤ r → χ x = 1) →
      (∀ x, s ≤ g x → χ x = 0) →
      |∫ x in {x | g x < s}, ζ x (w x) ∂ν - ∫ x, ζ x (χ x • w x) ∂ν| ≤
        c * ν.real {x | r < g x ∧ g x < s} := by
    intro ν ζ χ r hνG hζm hζb hχc hχ01 hχ1 hχ0
    have hF : AEStronglyMeasurable (fun x => ζ x (w x)) ν :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hζm.prodMk hwc.aestronglyMeasurable)
    have hFb : ∀ᵐ x ∂ν, |ζ x (w x)| ≤ c := hζb.mono fun x hx => (hx _).trans (hc x)
    have hint1 : IntegrableOn (fun x => ζ x (w x)) {x | g x < s} ν :=
      Measure.integrableOn_of_bounded hνG.ne hF
        (ae_restrict_of_ae (hFb.mono fun x hx => by rwa [Real.norm_eq_abs]))
    have hχF : ∀ x, |ζ x (w x)| ≤ c → |χ x * ζ x (w x)| ≤ c := by
      intro x hx
      rw [abs_mul]
      have h01 := hχ01 x
      calc |χ x| * |ζ x (w x)| ≤ 1 * c :=
            mul_le_mul (by rw [abs_of_nonneg h01.1]; exact h01.2) hx (abs_nonneg _) zero_le_one
        _ = c := one_mul c
    have hint2 : IntegrableOn (fun x => χ x * ζ x (w x)) {x | g x < s} ν :=
      Measure.integrableOn_of_bounded hνG.ne (hχc.aestronglyMeasurable.mul hF)
        (ae_restrict_of_ae (hFb.mono fun x hx => by rw [Real.norm_eq_abs]; exact hχF x hx))
    have hsmul : ∀ x, ζ x (χ x • w x) = χ x * ζ x (w x) := fun x => by
      rw [map_smul, smul_eq_mul]
    have h2 : ∫ x, ζ x (χ x • w x) ∂ν = ∫ x in {x | g x < s}, χ x * ζ x (w x) ∂ν := by
      simp_rw [hsmul]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have : s ≤ g x := not_lt.1 hx
        rw [hχ0 x this, zero_mul]).symm
    rw [h2, ← integral_sub hint1 hint2]
    have h3 : ∫ x in {x | g x < s}, (ζ x (w x) - χ x * ζ x (w x)) ∂ν =
        ∫ x in {x | r < g x ∧ g x < s}, (ζ x (w x) - χ x * ζ x (w x)) ∂ν := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hGm (fun x hx => hx.2)
      intro x hx
      have : g x ≤ r := by
        by_contra h
        exact hx.2 ⟨lt_of_not_ge h, hx.1⟩
      rw [hχ1 x this]
      ring
    rw [h3, ← Real.norm_eq_abs]
    apply norm_setIntegral_le_of_norm_le_const_ae
      (lt_of_le_of_lt (measure_mono fun x hx => hx.2) hνG)
    apply ae_restrict_of_ae
    filter_upwards [hFb] with x hx
    rw [Real.norm_eq_abs, show ζ x (w x) - χ x * ζ x (w x) = (1 - χ x) * ζ x (w x) by ring,
      abs_mul]
    have h01 := hχ01 x
    calc |1 - χ x| * |ζ x (w x)| ≤ 1 * c :=
          mul_le_mul (by rw [abs_of_nonneg (by linarith [h01.2])]; linarith [h01.1]) hx
            (abs_nonneg _) zero_le_one
      _ = c := one_mul c
  -- Step 3: the ε-argument.
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (3 * (c + 1)) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  obtain ⟨δ₁, hδ₁, hμδ₁⟩ :
      ∃ δ₁ : ℝ, 0 < δ₁ ∧ μ {x | s - δ₁ < g x ∧ g x < s} ≤ ENNReal.ofReal η := by
    let S : ℕ → Set (Euclid P) := fun i => {x | s - 1 / ((i : ℝ) + 1) < g x ∧ g x < s}
    have hSm : ∀ i, NullMeasurableSet (S i) μ := fun i =>
      ((measurableSet_lt measurable_const hg.measurable).inter hGm).nullMeasurableSet
    have hSanti : Antitone S := by
      intro i k hik x hx
      refine ⟨lt_of_le_of_lt ?_ hx.1, hx.2⟩
      have : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hik 1)
      linarith
    have hSfin : ∃ i, μ (S i) ≠ ∞ :=
      ⟨0, (lt_of_le_of_lt (measure_mono fun x hx => hx.2) hμG).ne⟩
    have hinter : (⋂ i, S i) = ∅ := by
      ext x
      simp only [S, mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall]
      by_cases hxs : g x < s
      · obtain ⟨i, hi⟩ := exists_nat_one_div_lt (sub_pos.2 hxs)
        exact ⟨i, fun h => by linarith [h.1]⟩
      · exact ⟨0, fun h => hxs h.2⟩
    have ht := tendsto_measure_iInter_atTop hSm hSanti hSfin
    rw [hinter, measure_empty] at ht
    have hev := (ENNReal.tendsto_nhds_zero.1 ht) (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)
    obtain ⟨i, hi⟩ := hev.exists
    exact ⟨1 / ((i : ℝ) + 1), by positivity, hi⟩
  obtain ⟨δ₂, hδ₂, hev₂⟩ := hconc (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)
  have hδ' : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  obtain ⟨χ, hχs, hχ01, hχ1, hχ0'⟩ : ∃ χ : Euclid P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ (∀ x, g x ≤ s - min δ₁ δ₂ → χ x = 1) ∧
      (∀ x, s - min δ₁ δ₂ / 2 ≤ g x → χ x = 0) := by
    obtain ⟨f, hf1, hf0, hf01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
      (modelWithCornersSelf ℝ (Euclid P)) (n := ⊤) (s := {x | g x ≤ s - min δ₁ δ₂})
      (t := {x | g x < s - min δ₁ δ₂ / 2}) (isClosed_le hg continuous_const)
      (by
        rw [(isOpen_lt hg continuous_const).interior_eq]
        intro x (hx : g x ≤ s - min δ₁ δ₂)
        show g x < s - min δ₁ δ₂ / 2
        linarith)
    refine ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, hf01, fun x hx => hf1.self_of_nhdsSet x hx,
      fun x hx => hf0 x (by simp only [mem_setOf_eq, not_lt]; exact hx)⟩
  have hχ0 : ∀ x, s ≤ g x → χ x = 0 := fun x hx => hχ0' x (by linarith)
  have hws : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := by rw [hwdef]; exact ω.property.1.1
  have hwcs : HasCompactSupport w := by rw [hwdef]; exact ω.property.1.2
  have hwU : tsupport w ⊆ U := by rw [hwdef]; exact ω.property.2
  have hsupp : support (fun x => χ x • w x) ⊆ support w := by
    intro x hx h0
    apply hx
    simp only [h0, smul_zero]
  have h1 : IsSmoothForm (fun x => χ x • w x) := hχs.smul hws
  have h2 : HasCompactSupport (fun x => χ x • w x) :=
    hwcs.mono' (hsupp.trans (subset_tsupport w))
  have h3 : tsupport (fun x => χ x • w x) ⊆ U := (closure_mono hsupp).trans hwU
  have hmem : (fun x => χ x • w x) ∈ TestFormOn U d := ⟨⟨h1, h2⟩, h3⟩
  let χω : TestFormOn U d := ⟨fun x => χ x • w x, hmem⟩
  have hconvχ := hconv χω
  rw [Metric.tendsto_atTop] at hconvχ
  obtain ⟨N₁, hN₁⟩ := hconvχ η hη
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hev₂
  refine ⟨max N₁ N₂, fun j hj => ?_⟩
  have hj₁ : N₁ ≤ j := le_trans (le_max_left _ _) hj
  have hj₂ : N₂ ≤ j := le_trans (le_max_right _ _) hj
  have e1 := key (μs j) (ξs j) χ (s - min δ₁ δ₂) (hμsG j) (hξsm j) (hξsb j) hχs.continuous hχ01
    hχ1 hχ0
  have e2 := key μ ξ χ (s - min δ₁ δ₂) hμG hξm hξb hχs.continuous hχ01 hχ1 hχ0
  have hm1 : (μs j).real {x | s - min δ₁ δ₂ < g x ∧ g x < s} ≤ η := by
    have : μs j {x | s - min δ₁ δ₂ < g x ∧ g x < s} ≤ ENNReal.ofReal η :=
      le_trans (measure_mono (show {x | s - min δ₁ δ₂ < g x ∧ g x < s} ⊆
          {x | s - δ₂ ≤ g x ∧ g x ≤ s} from
          fun x hx => ⟨by linarith [hx.1, min_le_right δ₁ δ₂], hx.2.le⟩)) (hN₂ j hj₂)
    exact ENNReal.toReal_le_of_le_ofReal hη.le this
  have hm2 : μ.real {x | s - min δ₁ δ₂ < g x ∧ g x < s} ≤ η := by
    have : μ {x | s - min δ₁ δ₂ < g x ∧ g x < s} ≤ ENNReal.ofReal η :=
      le_trans (measure_mono (show {x | s - min δ₁ δ₂ < g x ∧ g x < s} ⊆
          {x | s - δ₁ < g x ∧ g x < s} from
          fun x hx => ⟨by linarith [hx.1, min_le_left δ₁ δ₂], hx.2⟩)) hμδ₁
    exact ENNReal.toReal_le_of_le_ofReal hη.le this
  have h3 : dist (Ts j χω) (T χω) < η := hN₁ j hj₁
  have hTsχ : Ts j χω = ∫ x, ξs j x (χ x • w x) ∂(μs j) := hTs j χω
  have hTχ : T χω = ∫ x, ξ x (χ x • w x) ∂μ := hT χω
  rw [Real.dist_eq, hTsχ, hTχ] at h3
  rw [Real.dist_eq, hTs' j ω, hT' ω, ← hwdef]
  have hc1 := mul_le_mul_of_nonneg_left hm1 hc0
  have hc2 := mul_le_mul_of_nonneg_left hm2 hc0
  have habs := abs_sub_le (∫ x in {x | g x < s}, ξs j x (w x) ∂(μs j))
    (∫ x, ξs j x (χ x • w x) ∂(μs j)) (∫ x in {x | g x < s}, ξ x (w x) ∂μ)
  have habs2 := abs_sub_le (∫ x, ξs j x (χ x • w x) ∂(μs j)) (∫ x, ξ x (χ x • w x) ∂μ)
    (∫ x in {x | g x < s}, ξ x (w x) ∂μ)
  rw [abs_sub_comm (∫ x, ξ x (χ x • w x) ∂μ)] at habs2
  have hfin : (2 * c + 1) * η < ε := by
    rw [hηdef]
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

## Key steps

1. Bound |ω(x)| ≤ c, using that the coefficient norm of ω is continuous and compactly supported.
2. Cutoff estimate: |∫_G⟨ω,ζ⟩dν - ∫⟨χω,ζ⟩dν| ≤ c·ν({r < g < s}) for continuous χ ∈ [0,1] with χ = 1 on {g ≤ r} and χ = 0 on {g ≥ s}.
3. Continuity from above gives δ₁ with μ({s-δ₁<g<s}) ≤ η; (H6) gives δ₂ with μ_j({s-δ₂≤g≤s}) ≤ η for large j.
4. A smooth Urysohn cutoff χ (= 1 on {g ≤ s-δ'}, = 0 on {g ≥ s-δ'/2}) gives χω ∈ 𝒟^d(U), and T_j(χω) → T(χω).
5. Triangle inequality: |T'_j(ω) - T'(ω)| ≤ (2c+1)η < ε for large j, so T'_j ⇀ T'.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -n 'cmc_fcl|cmc_fc_localize|weakConverges_sublevel' local-references/123e8435b4a2469b/project --glob '*.lean' (no match)`
- `rg -n 'theorem integral_withDensity_eq_integral_smul |theorem exists_contMDiffMap_one_nhds_of_subset_interior|theorem _root_.IsCompact.exists_cthickening_subset_open|theorem tendsto_measure_iInter_atTop|theorem norm_setIntegral_le_of_norm_le_const_ae|theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|theorem enorm_integral_le_lintegral_enorm|theorem restrict_withDensity|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem lipschitz_infDist_pt|theorem _root_.IsCompact.cthickening' local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean'`
- `grep -rn 'GeometricCurrentOn.support|def GeometricCurrentOn.zeroRegion|GeometricCurrentOn.VanishesOn|restrictDomain' lake-packages-25730c7c/simongmt/Poincare/SimonGMT; cat Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean`
- `python3 over dag.json: statuses and frozen types of the flat_convergence siblings (cmc_fc_good_slice); accepted declarations mentioning IMRep/massOn/support (dor_ims_action_eq_integral, dor_ims_massOn_le_measure, rsd_cmr_support_subset_of_vanish, rsd_mw_wlm_eval_eq_integral_restrict); lcmp_massOn_le_add_of_eval_eq (decomposing under another parent); collision check of the cmc_fcl_* names (none)`
- `sed /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (_existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children, decomposition workspace publication) and store.py ensure`
- `sed -n 2028,2110p book/chapter-06.txt (Simon 7.2; localization sentence at lines 2090-2096)`
- `lake env lean /tmp/lczdec/T1.lean, /tmp/lczdec/check/T2.lean (#check probes of the GMT.Ch07.Submission import closure; smooth Urysohn cutoff via exists_contMDiffMap_one_nhds_of_subset_interior), /tmp/lczdec/check/T6.lean-T8.lean (elaboration-time probes)`
- `lake env lean /tmp/lczdec/Assembly.lean (child stubs, cmc_fc_good_slice stub and the assembly of the exact cmc_fc_localize type: no errors)`
- `lake env lean /tmp/lczdec/Full.lean (six child proofs plus the assembly; #print axioms of the children: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-localize-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-localize-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `/tmp/lczdec/Assembly.lean`
- `/tmp/lczdec/Full.lean`

The snapshot is project b4d606db with Mathlib 25730c7c. Its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. The snapshot contains no cmc_fcl_* or cmc_fc_localize declaration (rg: no match). SimonGMT Chapter06 supplies massOn, mass, support, zeroRegion, massOn_mono and le_massOn, but none of the seven child facts. The pinned Mathlib supplies every tool the compiled child proofs use, all inside the import closure of GMT.Ch07.Submission: integral_withDensity_eq_integral_smul, restrict_withDensity, Measure.restrict_restrict, withDensity_absolutelyContinuous, IsCompact.exists_cthickening_subset_open, IsCompact.cthickening, lipschitz_infDist_pt, enorm_integral_le_lintegral_enorm, setIntegral_eq_integral_of_forall_compl_eq_zero, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, norm_setIntegral_le_of_norm_le_const_ae, Measure.integrableOn_of_bounded, tendsto_measure_iInter_atTop, exists_contMDiffMap_one_nhds_of_subset_interior and contMDiff_iff_contDiff. Among accepted DAG declarations, rsd_cmr_support_subset_of_vanish is reused with its identical frozen type. lcmp_massOn_le_add_of_eval_eq is still active under another parent, so it is not shared and cmc_fcl_massOn_le_add is introduced instead. No cmc_fcl_* name collides with any of the 668 DAG names. All seven child types elaborate. The exact frozen type of cmc_fc_localize compiles from the seven children and cmc_fc_good_slice. The six new children compile using only the axioms propext, Classical.choice and Quot.sound.
