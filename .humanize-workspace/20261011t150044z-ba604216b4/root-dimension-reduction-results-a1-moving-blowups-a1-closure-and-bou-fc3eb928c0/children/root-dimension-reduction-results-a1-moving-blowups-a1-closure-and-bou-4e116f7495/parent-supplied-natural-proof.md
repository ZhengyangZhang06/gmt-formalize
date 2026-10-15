# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.null_off_image-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 10 of the parent proof (σ₁ := u⁺Lⁿ + p_*(h⁻μ_k⌞F), σ₂ := u⁻Lⁿ + p_*(h⁺μ_k⌞F), uniqueness of measures from C_c^∞ tests, the measurable hull E_k = toMeasurable(Lⁿ, S_k)); there q = p, σ = μ_k⌞(F ∩ p⁻¹B_{2R}), h = ξ_k(β_v), A = N_k ∩ F.
0. (Measurable versions.) Choose a measurable ũ with u = ũ volume-a.e. on U (IntegrableOn gives AEStronglyMeasurable for volume⌞U; AEStronglyMeasurable.mk) and a measurable h̃ with h = h̃ σ-a.e. The hypothesis holds with (ũ, h̃) in place of (u, h) (integrals of a.e.-equal functions agree), ũ is integrable on U and h̃ is σ-integrable; and B ∩ {u ≠ 0} ⊆ (B ∩ {ũ ≠ 0}) ∪ (U ∩ {u ≠ ũ}) with the last set volume-null, so the conclusion for ũ implies it for u (measure_union_le). Hence we may and do assume that u and h are measurable.
1. (Finite measures.) Let u^± := max(±u, 0), h^± := max(±h, 0) (measurable, nonnegative). Put λ_± := (volume⌞U).withDensity(ofReal∘u^±) and m_± := Measure.map q (σ.withDensity(ofReal∘h^±)) (q is continuous, hence measurable). They are finite: λ_±(ℝⁿ) = ∫⁻_U ofReal(u^±) ≤ ∫⁻_U ofReal|u| < ∞ and m_±(ℝⁿ) = ∫⁻ofReal(h^±)dσ < ∞. Set σ₁ := (λ₊ + m₋)⌞U and σ₂ := (λ₋ + m₊)⌞U, finite Borel measures on ℝⁿ.
2. (Equal integrals of test functions.) Let b be smooth, compactly supported, tsupport b ⊆ U; b is bounded, continuous and vanishes off U. Then ∫b dσ₁ = ∫_U b u⁺ + ∫b(q x)h⁻(x)dσ(x): restricting to U does not change the integral of b (b = 0 off U; setIntegral_eq_integral_of_forall_compl_eq_zero), integral_add_measure splits the sum, integral_withDensity_eq_integral_toReal_smul (measurable densities, finite a.e.) gives ∫b dλ₊ = ∫_U u⁺b, and integral_map with the same lemma gives ∫b dm₋ = ∫b(q x)h⁻(x)dσ(x); likewise ∫b dσ₂ = ∫_U b u⁻ + ∫b(q x)h⁺(x)dσ(x). All these integrals are finite (b bounded). Their difference is ∫_U b u − ∫b(q x)h(x)dσ(x) = 0 by hypothesis (u = u⁺ − u⁻, h = h⁺ − h⁻). So ∫b dσ₁ = ∫b dσ₂.
3. (Open sets.) Let O ⊆ ℝⁿ be open and V := O ∩ U (open). For j ∈ ℕ let K_j := {y : infEdist(y, ℝⁿ ∖ V) ≥ 1/(j+1)} ∩ closedBall(0, j): it is closed (infEdist is continuous) and bounded, hence compact, and K_j ⊆ V (points of ℝⁿ ∖ V have infEdist 0; if V = ℝⁿ the infEdist to ∅ is ∞ and K_j = closedBall(0, j)); every y ∈ V lies in K_j for all large j (V open, so infEdist(y, ℝⁿ ∖ V) > 0). Smooth cutoff: choose r_j > 0 with cthickening(2r_j, K_j) ⊆ V (IsCompact.exists_cthickening_subset_open); cthickening(2r_j, K_j) is compact (IsCompact.cthickening). Apply exists_contDiff_support_eq_eq_one_iff (smooth Urysohn in the finite-dimensional space ℝⁿ) to the open set thickening(2r_j, K_j) and the closed set cthickening(r_j, K_j) ⊆ thickening(2r_j, K_j): it gives a smooth b_j : ℝⁿ → [0, 1] with support b_j = thickening(2r_j, K_j) and b_j = 1 on cthickening(r_j, K_j) ⊇ K_j; so tsupport b_j ⊆ cthickening(2r_j, K_j) ⊆ V ⊆ U is compact. Then b_j(y) → 1_V(y) for every y, |b_j| ≤ 1, and σ_i is finite, so by dominated convergence (tendsto_integral_of_dominated_convergence with the constant bound 1) ∫b_j dσ_i → σ_i(V) = σ_i(O) (σ_i is carried by U). By step 2, σ₁(O) = σ₂(O) for every open O.
4. (Uniqueness.) The open sets form a π-system (isPiSystem_isOpen) generating the Borel σ-algebra of ℝⁿ (borel = generateFrom {open}; BorelSpace.measurable_eq), ℝⁿ is open and σ₁, σ₂ are finite; so σ₁ = σ₂ (MeasureTheory.ext_of_generate_finite). In particular (λ₊ + m₋)(B') = (λ₋ + m₊)(B') for every measurable B' ⊆ U.
5. (Measurable hull.) Let E := toMeasurable volume (q(A)), a measurable superset of q(A) with volume(E ∩ B) = volume(q(A) ∩ B) for every measurable B (Measure.measure_toMeasurable_inter_of_sFinite; volume is σ-finite). Let B' ⊆ U ∖ E be measurable. If x ∈ A and q(x) ∈ B', then q(x) ∈ q(A) ⊆ E, impossible; so q⁻¹(B') ⊆ ℝ^P ∖ A, σ(q⁻¹(B')) = 0, and m_±(B') = ∫⁻_{q⁻¹(B')}ofReal(h^±)dσ = 0 (Measure.map_apply, withDensity_apply, setLIntegral_measure_zero). By step 4, λ₊(B') = λ₋(B'), i.e. ∫⁻_{B'}ofReal(u⁺) = ∫⁻_{B'}ofReal(u⁻).
6. (Vanishing off E.) Apply step 5 to B'₊ := (U ∖ E) ∩ {u > 0} (measurable): u⁻ = 0 on B'₊, so ∫⁻_{B'₊}ofReal(u⁺) = 0, hence u⁺ = 0 a.e. on B'₊ (setLIntegral_eq_zero_iff / lintegral_eq_zero_iff); but u⁺ = u > 0 on B'₊, so volume(B'₊) = 0. Symmetrically volume((U ∖ E) ∩ {u < 0}) = 0. Hence volume((U ∖ E) ∩ {u ≠ 0}) = 0.
7. (Conclusion.) For measurable B ⊆ U: B ∩ {u ≠ 0} ⊆ (E ∩ B) ∪ ((U ∖ E) ∩ {u ≠ 0}), so volume(B ∩ {u ≠ 0}) ≤ volume(E ∩ B) + 0 = volume(q(A) ∩ B) = volume(B ∩ q(A)) (measure_union_le and the hull identity of step 5). ∎

Verified Lean realization (supplementary). The single theorem below was compiled with `lake env lean` (Lean v4.35.0-rc3; project b4d606db, Mathlib 25730c7c, SimonGMT 2b366308) in a file that imports GMT.Ch07.Submission and reopens the frozen contract's namespace GMT.Ch07 with its `open`s, with no sibling dependency: no errors and no warnings; `#count_heartbeats` reports 19932 heartbeats, below the default maxHeartbeats 200000 (no set_option); `#print axioms` lists propext, Classical.choice and Quot.sound only; inserted before main_theorem in GMT/Ch07/Submission.lean it passes the runtime's leaf source-delta check (one appended theorem under its exact name; no helper declaration, import, set_option or placeholder). Its local lemmas aux_* are proved inline and correspond to the numbered steps above: aux_smooth_cutoff_seq is the cutoff sequence b_j ↑ 1_V of step 3; aux_restrict_eq_of_smooth_test is steps 3–4 (two finite measures with equal integrals of all smooth tests supported in the open set U have equal restrictions to U); aux_setIntegral_eq_preimage combines steps 0–2 and 4 into the identity ∫_B u = ∫_{q⁻¹(B)} h dσ for every measurable B ⊆ U (by applying the previous fact to the finite measures (λ₊ + m₋)⌞U and (λ₋ + m₊)⌞U of step 1); the final lines are steps 5–7 (E := toMeasurable volume (q(A)); for measurable s ⊆ U ∖ E, q⁻¹(s) ⊆ ℝ^P ∖ A is σ-null, so ∫_s u = 0; hence u = 0 a.e. on U ∖ E; and the measure estimate with Measure.measure_toMeasurable_inter_of_sFinite). It may be appended verbatim as the single leaf theorem:
```lean
theorem Submission.dmcbr_ci_pw_density_null_off_image : ∀ (P n : ℕ) (U : Set (Euclid n)) (u : Euclid n → ℝ) (σ : Measure (Euclid P)) (q : Euclid P → Euclid n) (h : Euclid P → ℝ) (A : Set (Euclid P)), IsOpen U → Continuous q → IntegrableOn u U → σ univ < ∞ → Integrable h σ → σ Aᶜ = 0 → (∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → ∫ y in U, b y * u y = ∫ x, b (q x) * h x ∂σ) → ∀ B : Set (Euclid n), MeasurableSet B → B ⊆ U → volume (B ∩ {y | u y ≠ 0}) ≤ volume (B ∩ q '' A) := by
  have aux_smooth_cutoff_seq : ∀ (n : ℕ) (V : Set (Euclid n)), IsOpen V → ∃ b : ℕ → Euclid n → ℝ, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (b j)) ∧ (∀ j, HasCompactSupport (b j)) ∧ (∀ j, tsupport (b j) ⊆ V) ∧ (∀ j y, 0 ≤ b j y ∧ b j y ≤ 1) ∧ ∀ y, Tendsto (fun j => b j y) atTop (𝓝 (V.indicator (fun _ => (1 : ℝ)) y)) := by
    intro n V hV
    -- Step 1: the compact exhaustion `Kⱼ = {y : infEDist y Vᶜ ≥ 1/(j+1)} ∩ B̄(0, j)` of `V`.
    set K : ℕ → Set (Euclid n) := fun j =>
      {y | ((j : ℝ≥0∞) + 1)⁻¹ ≤ infEDist y Vᶜ} ∩ closedBall 0 j
    have hKc : ∀ j, IsCompact (K j) := fun j =>
      (isCompact_closedBall 0 (j : ℝ)).inter_left (isClosed_le continuous_const continuous_infEDist)
    have hKV : ∀ j, K j ⊆ V := by
      intro j y hy
      by_contra hyV
      have h1 : ((j : ℝ≥0∞) + 1)⁻¹ ≤ infEDist y Vᶜ := hy.1
      rw [infEDist_zero_of_mem hyV] at h1
      exact (ENNReal.inv_pos.mpr (by simp)).ne' (le_antisymm h1 bot_le)
    have hKev : ∀ y ∈ V, ∀ᶠ j in atTop, y ∈ K j := by
      intro y hy
      have hpos : 0 < infEDist y Vᶜ := by
        rw [infEDist_pos_iff_notMem_closure, hV.isClosed_compl.closure_eq]
        exact fun h => h hy
      have h1 : ∀ᶠ j : ℕ in atTop, ((j : ℝ≥0∞) + 1)⁻¹ ≤ infEDist y Vᶜ := by
        have ht : Tendsto (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) :=
          (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)).congr fun j => by simp
        filter_upwards [ht.eventually (gt_mem_nhds hpos)] with j hj using hj.le
      have h2 : ∀ᶠ j : ℕ in atTop, y ∈ closedBall (0 : Euclid n) j := by
        obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
        filter_upwards [eventually_ge_atTop N] with j hj
        rw [mem_closedBall, dist_zero_right]
        exact hN.trans (by exact_mod_cast hj)
      filter_upwards [h1, h2] with j hj1 hj2 using ⟨hj1, hj2⟩
    -- Step 2: radii `rⱼ > 0` with `cthickening (2 rⱼ) Kⱼ ⊆ V`.
    have hr : ∀ j, ∃ r : ℝ, 0 < r ∧ cthickening (2 * r) (K j) ⊆ V := by
      intro j
      obtain ⟨δ, hδ, hsub⟩ := (hKc j).exists_cthickening_subset_open hV (hKV j)
      exact ⟨δ / 2, by positivity, by rwa [mul_div_cancel₀ _ two_ne_zero]⟩
    choose r hr0 hrV using hr
    -- Step 3: smooth Urysohn functions, `1` exactly on `cthickening rⱼ Kⱼ`, with support
    -- `thickening (2 rⱼ) Kⱼ`.
    have hb : ∀ j, ∃ f : Euclid n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ range f ⊆ Icc 0 1 ∧
        support f = thickening (2 * r j) (K j) ∧ ∀ x, x ∈ cthickening (r j) (K j) ↔ f x = 1 :=
      fun j => exists_contDiff_support_eq_eq_one_iff isOpen_thickening isClosed_cthickening
        (cthickening_subset_thickening' (by linarith [hr0 j]) (by linarith [hr0 j]) _)
    choose b hbsmooth hbrange hbsupp hbone using hb
    have htsupp : ∀ j, tsupport (b j) ⊆ cthickening (2 * r j) (K j) := by
      intro j
      rw [tsupport, hbsupp]
      exact closure_thickening_subset_cthickening _ _
    refine ⟨b, hbsmooth,
      fun j => (hKc j).cthickening.of_isClosed_subset (isClosed_tsupport _) (htsupp j),
      fun j => (htsupp j).trans (hrV j), fun j y => hbrange j ⟨y, rfl⟩, fun y => ?_⟩
    -- Step 4: `bⱼ y = 1` for large `j` if `y ∈ V`, and `bⱼ y = 0` for all `j` if `y ∉ V`.
    by_cases hy : y ∈ V
    · rw [indicator_of_mem hy]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hKev y hy] with j hj
      exact ((hbone j y).mp (self_subset_cthickening _ hj)).symm
    · rw [indicator_of_notMem hy]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun j => ?_)
      by_contra hne
      exact hy ((htsupp j).trans (hrV j) (subset_tsupport _ (Ne.symm hne)))
  have aux_restrict_eq_of_smooth_test : ∀ (n : ℕ) (U : Set (Euclid n)) (μ ν : Measure (Euclid n)), IsOpen U → IsFiniteMeasure μ → IsFiniteMeasure ν → (∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → ∫ y, b y ∂μ = ∫ y, b y ∂ν) → μ.restrict U = ν.restrict U := by
    intro n U μ ν hU hμ hν htest
    -- Step 1: `μ` and `ν` agree on `O ∩ U` for every open `O`, by testing with smooth cutoffs
    -- `bⱼ → 𝟙_{O ∩ U}` and dominated convergence (bound `1`, integrable as the measures are finite).
    have hopen : ∀ O : Set (Euclid n), IsOpen O → μ (O ∩ U) = ν (O ∩ U) := by
      intro O hO
      obtain ⟨b, hbs, hbc, hbt, hb01, hblim⟩ :=
        aux_smooth_cutoff_seq n (O ∩ U) (hO.inter hU)
      have hlim : ∀ ρ : Measure (Euclid n), IsFiniteMeasure ρ →
          Tendsto (fun j => ∫ y, b j y ∂ρ) atTop (𝓝 (ρ.real (O ∩ U))) := by
        intro ρ hρ
        rw [← integral_indicator_one (hO.inter hU).measurableSet]
        refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
          (fun j => (hbs j).continuous.aestronglyMeasurable) (integrable_const 1)
          (fun j => Eventually.of_forall fun y => ?_) (Eventually.of_forall hblim)
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [(hb01 j y).1, (hb01 j y).2]
      have heq : ∀ j, ∫ y, b j y ∂μ = ∫ y, b j y ∂ν := fun j =>
        htest (b j) (hbs j) (hbc j) ((hbt j).trans inter_subset_right)
      have h₁ := hlim μ hμ
      have h₂ := hlim ν hν
      simp_rw [heq] at h₁
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
        (tendsto_nhds_unique h₁ h₂)
    -- Step 2: `μ⌞U` and `ν⌞U` agree on the π-system of open sets, which generates the Borel
    -- σ-algebra, and on `univ`; finite measures agreeing there are equal.
    refine ext_of_generate_finite {s | IsOpen s} BorelSpace.measurable_eq isPiSystem_isOpen ?_ ?_
    · intro s (hs : IsOpen s)
      rw [Measure.restrict_apply hs.measurableSet, Measure.restrict_apply hs.measurableSet]
      exact hopen s hs
    · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
      simpa using hopen univ isOpen_univ
  have aux_setIntegral_eq_preimage : ∀ (P n : ℕ) (U : Set (Euclid n)) (u : Euclid n → ℝ) (σ : Measure (Euclid P)) (q : Euclid P → Euclid n) (h : Euclid P → ℝ), IsOpen U → Measurable q → IntegrableOn u U → Integrable h σ → (∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → ∫ y in U, b y * u y = ∫ x, b (q x) * h x ∂σ) → ∀ B : Set (Euclid n), MeasurableSet B → B ⊆ U → ∫ y in B, u y = ∫ x in q ⁻¹' B, h x ∂σ := by
    intro P n U u σ q h hU hq hu hh htest B hB hBU
    -- Step 1: the finite measures `λ± = u± Lⁿ⌞U` and `m± = q_♯(h± σ)`.
    set lp : Measure (Euclid n) := (volume.restrict U).withDensity fun y => ENNReal.ofReal (u y)
      with hlp
    set lm : Measure (Euclid n) := (volume.restrict U).withDensity fun y => ENNReal.ofReal (-u y)
      with hlm
    set mp : Measure (Euclid n) := (σ.withDensity fun x => ENNReal.ofReal (h x)).map q with hmp
    set mm : Measure (Euclid n) := (σ.withDensity fun x => ENNReal.ofReal (-h x)).map q with hmm
    have hlpf : IsFiniteMeasure lp := isFiniteMeasure_withDensity_ofReal hu.2
    have hlmf : IsFiniteMeasure lm := isFiniteMeasure_withDensity_ofReal hu.neg.2
    have hmpf : IsFiniteMeasure mp := by
      have : IsFiniteMeasure (σ.withDensity fun x => ENNReal.ofReal (h x)) :=
        isFiniteMeasure_withDensity_ofReal hh.2
      exact Measure.isFiniteMeasure_map _ _
    have hmmf : IsFiniteMeasure mm := by
      have : IsFiniteMeasure (σ.withDensity fun x => ENNReal.ofReal (-h x)) :=
        isFiniteMeasure_withDensity_ofReal hh.neg.2
      exact Measure.isFiniteMeasure_map _ _
    -- Step 2: integrals of a function `b` against `λ±` and `m±`.
    have hlam : ∀ (f : Euclid n → ℝ) (b : Euclid n → ℝ), IntegrableOn f U →
        ∫ y, b y ∂((volume.restrict U).withDensity fun y => ENNReal.ofReal (f y)) =
          ∫ y in U, max (f y) 0 * b y := by
      intro f b hf
      rw [integral_withDensity_eq_integral_toReal_smul₀ hf.aemeasurable.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal', smul_eq_mul]
    have hpush : ∀ (g : Euclid P → ℝ) (b : Euclid n → ℝ), Integrable g σ → Continuous b →
        ∫ y, b y ∂((σ.withDensity fun x => ENNReal.ofReal (g x)).map q) =
          ∫ x, max (g x) 0 * b (q x) ∂σ := by
      intro g b hg hb
      rw [integral_map hq.aemeasurable hb.aestronglyMeasurable,
        integral_withDensity_eq_integral_toReal_smul₀ hg.aemeasurable.ennreal_ofReal
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal', smul_eq_mul]
    -- Step 3: `λ₊ + m₋` and `λ₋ + m₊` have the same integral against every test function, since
    -- `u = u⁺ - u⁻`, `h = h⁺ - h⁻` and `∫_U b u = ∫ (b ∘ q) h dσ`.
    have hkey : ∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U →
        ∫ y, b y ∂(lp + mm) = ∫ y, b y ∂(lm + mp) := by
      intro b hb hbc hbU
      have hbcont : Continuous b := hb.continuous
      obtain ⟨C, hC⟩ := hbcont.bounded_above_of_compact_support hbc
      have hbm : AEStronglyMeasurable b (volume.restrict U) := hbcont.aestronglyMeasurable
      have hbqm : AEStronglyMeasurable (fun x => b (q x)) σ :=
        (hbcont.measurable.comp hq).aestronglyMeasurable
      rw [integral_add_measure (hbcont.integrable_of_hasCompactSupport hbc)
          (hbcont.integrable_of_hasCompactSupport hbc),
        integral_add_measure (hbcont.integrable_of_hasCompactSupport hbc)
          (hbcont.integrable_of_hasCompactSupport hbc),
        hlam u b hu, hlam (fun y => -u y) b hu.neg, hpush h b hh hbcont,
        hpush (fun x => -h x) b hh.neg hbcont]
      have I1 : (∫ y in U, max (u y) 0 * b y) - ∫ y in U, max (-u y) 0 * b y =
          ∫ y in U, b y * u y := by
        have hsub := integral_sub (hu.pos_part.mul_bdd hbm (Eventually.of_forall hC))
          (hu.neg_part.mul_bdd hbm (Eventually.of_forall hC))
        refine hsub.symm.trans (integral_congr_ae (Eventually.of_forall fun y => ?_))
        simp only
        rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self, mul_comm]
      have I2 : ∫ x, max (h x) 0 * b (q x) ∂σ - ∫ x, max (-h x) 0 * b (q x) ∂σ =
          ∫ x, b (q x) * h x ∂σ := by
        have hsub := integral_sub (hh.pos_part.mul_bdd hbqm (Eventually.of_forall fun x => hC (q x)))
          (hh.neg_part.mul_bdd hbqm (Eventually.of_forall fun x => hC (q x)))
        refine hsub.symm.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
        simp only
        rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self, mul_comm]
      have := htest b hb hbc hbU
      linarith
    -- Step 4: uniqueness, so the two measures agree on the measurable subset `B` of `U`.
    have hres := aux_restrict_eq_of_smooth_test n U (lp + mm) (lm + mp) hU
      inferInstance inferInstance hkey
    have hBeq : (lp + mm) B = (lm + mp) B := by
      have := congrArg (fun μ : Measure (Euclid n) => μ B) hres
      simpa only [Measure.restrict_apply hB, inter_eq_left.mpr hBU] using this
    -- Step 5: `λ±(B) = ∫⁻_B (±u)⁺` and `m±(B) = ∫⁻_{q⁻¹ B} (±h)⁺ dσ`.
    have hlB : ∀ f : Euclid n → ℝ, ((volume.restrict U).withDensity fun y => ENNReal.ofReal (f y)) B =
        ∫⁻ y in B, ENNReal.ofReal (f y) := by
      intro f
      rw [withDensity_apply _ hB, Measure.restrict_restrict hB, inter_eq_left.mpr hBU]
    have hmB : ∀ g : Euclid P → ℝ, ((σ.withDensity fun x => ENNReal.ofReal (g x)).map q) B =
        ∫⁻ x in q ⁻¹' B, ENNReal.ofReal (g x) ∂σ := by
      intro g
      rw [Measure.map_apply hq hB, withDensity_apply _ (hq hB)]
    -- Step 6: all four values are finite, so the identity of Step 4 passes to real numbers, and
    -- both set integrals are differences of positive and negative parts.
    rw [Measure.add_apply, Measure.add_apply] at hBeq
    have hreal : (lp B).toReal + (mm B).toReal = (lm B).toReal + (mp B).toReal := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
        ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hBeq]
    have hL : ∫ y in B, u y = (lp B).toReal - (lm B).toReal := by
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hu.mono_set hBU), hlp, hlm, hlB, hlB]
    have hR : ∫ x in q ⁻¹' B, h x ∂σ = (mp B).toReal - (mm B).toReal := by
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hh.integrableOn, hmp, hmm, hmB, hmB]
    rw [hL, hR]
    linarith
  intro P n U u σ q h A hU hq hu _hσ hh hA htest B hB hBU
  -- the measurable hull `E` of `q '' A`
  set E : Set (Euclid n) := toMeasurable volume (q '' A) with hE
  have hUE : MeasurableSet (U \ E) := hU.measurableSet.diff (measurableSet_toMeasurable _ _)
  -- `∫_s u = 0` for measurable `s ⊆ U \ E`, because `q ⁻¹' s ⊆ Aᶜ` is `σ`-null
  have hzero : ∀ s : Set (Euclid n), MeasurableSet s → s ⊆ U \ E → ∫ y in s, u y = 0 := by
    intro s hs hsUE
    rw [aux_setIntegral_eq_preimage P n U u σ q h hU hq.measurable hu hh
      htest s hs (hsUE.trans sdiff_subset)]
    refine setIntegral_measure_zero _ (measure_mono_null ?_ hA)
    intro x hx hxA
    exact (hsUE hx).2 (subset_toMeasurable _ _ ⟨x, hxA, rfl⟩)
  -- hence `u = 0` a.e. on `U \ E`
  have hae : u =ᵐ[volume.restrict (U \ E)] 0 :=
    (hu.mono_set sdiff_subset).ae_eq_zero_of_forall_setIntegral_eq_zero fun s hs _ => by
      rw [Measure.restrict_restrict hs]
      exact hzero _ (hs.inter hUE) inter_subset_right
  have hnull : volume ({y | u y ≠ 0} ∩ (U \ E)) = 0 := by
    rw [← Measure.restrict_apply' hUE]
    exact hae
  -- `B ∩ {u ≠ 0} ⊆ (B ∩ E) ∪ ({u ≠ 0} ∩ (U \ E))` and `Lⁿ(B ∩ E) = Lⁿ(B ∩ q '' A)`
  calc volume (B ∩ {y | u y ≠ 0})
      ≤ volume (B ∩ E ∪ {y | u y ≠ 0} ∩ (U \ E)) := by
        refine measure_mono fun y hy => ?_
        by_cases hyE : y ∈ E
        · exact Or.inl ⟨hy.1, hyE⟩
        · exact Or.inr ⟨hy.2, hBU hy.1, hyE⟩
    _ ≤ volume (B ∩ E) + volume ({y | u y ≠ 0} ∩ (U \ E)) := measure_union_le _ _
    _ = volume (B ∩ q '' A) := by
        rw [hnull, add_zero, inter_comm, hE,
          Measure.measure_toMeasurable_inter_of_sFinite hB, inter_comm]
```

## Key steps

1. σ₁ := (u⁺Lⁿ⌞U + q_*(h⁻σ))⌞U and σ₂ := (u⁻Lⁿ⌞U + q_*(h⁺σ))⌞U are finite measures with equal integrals of all b ∈ C_c^∞(U).
2. Smooth cutoffs b_j ↑ 1_{O∩U} and dominated convergence give σ₁ = σ₂ on open sets, hence on all Borel sets (π-system uniqueness).
3. For Borel B' ⊆ U ∖ toMeasurable(q(A)), q⁻¹(B') is σ-null, so ∫_{B'}u⁺ = ∫_{B'}u⁻ and u = 0 a.e. on U ∖ E.
4. Lⁿ(B ∩ {u ≠ 0}) ≤ Lⁿ(E ∩ B) = Lⁿ(q(A) ∩ B) by the hull property.

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json -> mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d; git rev-parse HEAD in the workspace, .lake/packages/mathlib and .lake/packages/simongmt -> b4d606db1, 25730c7c, 2b366308; cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean -> identical`
- `python3 -I scans of RUN/dag.json (2229 nodes): selected node (depth 5, decomposing, attempt 2 started 2026-10-14T02:29:54Z); subtree of root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1 (cbr_ci_plane_weight_ge_one: identical frozen type, speculative-ready) with statuses, candidate commits and updated_at; lean_name lookup of all 11 proposed names: the 8 reused names each occur once, accepted with candidate commits (latest 02:28:02Z) and identical lean_statement; the 3 dmcbr_ci_pw_* names have no node; byte comparisons dimred_mbl_slice_mass_bounds = cmc_slice_mass_bounds, dmcbr_measure_convergence_tools = cbr_measure_convergence_tools, first conjunct of dimred_mbl_current_foundations = cmc_exists_massRepresentation, and (REP), (SL), (CT) occur verbatim in the selected type`
- `grep -n / sed -n over /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose, _existing_lean_name_problem, _accepted_checkpoint, _solve_children existing_by_name), store.py (refresh, update: accepted status is permanent), leaf_verification.py (check_source_delta), lean_contract.py (validate_lean_statement); swarm-project.json -> max_depth 6, max_children 12`
- `read RUN/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-fc3eb928c0/{parent-child-handoff.json, parent-supplied-plan.md, decomposition-v1.json}: attempt 1 (12 children) was rejected only by the name check on cbr_ci_pw_bv_smooth_test_bound; its child statements, types and proofs were reused here, except smooth_test_bound (dropped) and bv_estimate (now the accepted cbr_ci_pw_bv_mollifier_estimate, with Claim A proved inline)`
- `git show <candidate>:GMT/Ch07/Submission.lean for e55e2ff3e6, f6358e3d52, e42d9153e5, b0c7e18f51, 7bb3791613, 4020906019, 04807323c8, 144655f39d -> each contains 'theorem Submission.<name> : <frozen type> :=' with the reused name occurring exactly once`
- `grep -rn over SNAPSHOT/mathlib/Mathlib for the library names cited in the bv_estimate proof: ae_tendsto_average_norm_sub (Covering/DensityTheorem.lean:150, Covering/Differentiation.lean:837), tendsto_integral_smul_of_tendsto_average_norm_sub, integral_comp_inv_smul_of_nonneg, addHaar_real_closedBall', contDiff_convolution_right, integrableOn_iff_integrable_of_support_subset, integrableOn_of_bounded, continuous_of_dominated, intervalIntegral_integral_swap, norm_integral_le_of_norm_le_const, fderiv_comp_add_right, tsupport_comp_eq_preimage, integral_sub_right_eq_self, Integrable.mul_prod, integral_integral_swap, Integrable.mul_bdd, setIntegral_indicator, integral_pos_iff_support_of_nonneg, measure_ball_pos, Integrable.integral_prod_left, Integrable.integral_prod_right, Continuous.integrable_of_hasCompactSupport, Continuous.bounded_above_of_compact_support, HasCompactSupport.fderiv, integral_eq_sub_of_hasDerivAt -> all present`
- `rg -l dmcbr_ci_pw_projected_current|dmcbr_ci_pw_density_null_off_image|dmcbr_ci_pw_density_l1_tendsto_const over SNAPSHOT/project, GMT and .lake/packages/simongmt -> no match (exit 1)`
- `lake env lean /tmp/dmcbr_ci_a2/lean/Types.lean (the 11 child types as Submission.* theorems) -> only sorry warnings, exit 0`
- `lake env lean /tmp/dmcbr_ci_a2/lean/Assembly.lean (exact frozen parent type from the 11 child types as axioms, no sorry) -> #print axioms: propext, Classical.choice, Quot.sound, cbr_ci_pw_good_level_slices, cbr_ci_pw_isolate_plane, cbr_ci_pw_orthonormal_covector_bounds, cbr_ci_pw_plane_map_volume, cbr_ci_pw_top_current_density, dmcbr_ci_pw_density_l1_tendsto_const, dmcbr_ci_pw_density_null_off_image, dmcbr_ci_pw_projected_current`
- `lake env lean /tmp/dmcbr_ci_a2/lean/check_{projection,null_off_image,l1_constant}.lean (#count_heartbeats in + realization + #print axioms, siblings declared by exact frozen types) -> 102743 / 19932 / 59551 heartbeats, axioms = standard three + declared siblings only`
- `lake env lean /tmp/dmcbr_ci_a2/lean/EndToEnd.lean (3 fresh realizations as theorems + assembly) -> #print axioms: propext, Classical.choice, Quot.sound + the 8 reused accepted declarations, exit 0`
- `python3 -I: AST-extracted leaf_verification.check_source_delta on GMT/Ch07/Submission.lean with each fresh realization inserted before main_theorem's docstring -> OK (3/3); lean_contract.validate_lean_statement on all 11 child types -> valid and unchanged`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-fc3eb928c0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-fc3eb928c0/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-fc3eb928c0/decomposition-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/tmp/dmcbr_ci_a2/lean/Types.lean`
- `/tmp/dmcbr_ci_a2/lean/Assembly.lean`
- `/tmp/dmcbr_ci_a2/lean/check_projection.lean`
- `/tmp/dmcbr_ci_a2/lean/check_null_off_image.lean`
- `/tmp/dmcbr_ci_a2/lean/check_l1_constant.lean`
- `/tmp/dmcbr_ci_a2/lean/EndToEnd.lean`

The snapshot is compatible: pins match, and the snapshot contract is byte-identical to Submission.lean. No dmcbr_ci_pw_* declaration exists in the snapshot, the workspace or SimonGMT. The 8 reused children (covector_bounds, plane_map, isolate_plane, good_level, top_density, interior_form, mollified_uniform, bv_estimate = cbr_ci_pw_bv_mollifier_estimate) are accepted checkpoints. They were accepted before this attempt's DAG refresh, and each candidate commit declares exactly the frozen type. The 3 fresh children take globally unused dmcbr_ci_pw_* names because their other-branch counterparts are unaccepted. All 11 child types elaborate. The sorry-free conditional assembly and the end-to-end file prove the exact parent type using only propext, Classical.choice, Quot.sound and child or reused accepted declarations. The fresh single-theorem realizations compile within the default heartbeats and pass the leaf delta check.
