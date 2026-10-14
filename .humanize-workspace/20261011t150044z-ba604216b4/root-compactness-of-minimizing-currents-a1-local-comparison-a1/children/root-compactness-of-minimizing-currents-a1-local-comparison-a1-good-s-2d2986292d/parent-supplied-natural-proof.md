# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.local_comparison-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.local_comparison-a1.good_slice_level-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 5 (choice of α and φ; Simon 7.2.4 (3)–(5), chapter-07.txt lines 192–205: “By the slicing theory (and in particular by 4.5 of Ch. 6) we can choose 0 < α < 1 and a subsequence ... We can also of course choose α to be such that (5) ...”). The parent applies this lemma with ν_j := μ_{R_j}, κ_j := μ_{T_j}, f := −ψ and (a, b) := (−1, 0), so that A = {0 < ψ < 1}, {t − h < f < t} = {α < ψ < α + h} and {f = t} = {ψ = α} for α := −t ∈ (0, 1); the slicing sibling bounds M_{W₀}(P_{j,α}) by L·D_j(t).
Detail (departure in the choice of the majorant). The parent majorizes the difference quotients by −L H_j′ with H_j(s) = μ_{R_j}(W₀ ∩ {s < ψ < 1}) and bounds ∫ −H_j′ by Mathlib MonotoneOn.intervalIntegral_deriv_mem_uIcc; that lemma is not in the import closure of the frozen contract. We use instead the sequential lower difference quotient G_j below, whose integral bound follows from Tonelli's theorem; the remainder of the argument (Fatou's lemma, countably many atoms, choice of the level and of the subsequence) is the parent's.

All quantities lie in [0, ∞] (0·∞ = 0); λ is Lebesgue measure on ℝ and “a.e.” refers to λ.

1. Measurability. Since f is Borel, A, the level sets {f = s} and the sets {t − h < f < t} are Borel.
2. Pushforward. Let ρ_j be the image of ν_j⌞A under f: ρ_j(B) = ν_j(f⁻¹(B) ∩ A) for Borel B ⊆ ℝ. Then ρ_j(ℝ) = ν_j(A) < ∞, so ρ_j is a finite Borel measure on ℝ.
3. Tonelli. For c ∈ ℝ let S_c := {(s, y) ∈ ℝ² : s − c < y < s}, a Borel set. Its sections are {y : (s, y) ∈ S_c} = (s − c, s) and {s : (s, y) ∈ S_c} = (y, y + c). Hence s ↦ ρ_j((s − c, s)) is Borel (measurability of sections of a product set, Mathlib measurable_measure_prodMk_left), and computing (λ × ρ_j)(S_c) in both orders (Measure.prod_apply, Measure.prod_apply_symm) gives ∫ ρ_j((s − c, s)) dλ(s) = ∫ λ((y, y + c)) dρ_j(y) = ofReal(c)·ρ_j(ℝ) = ofReal(c)·ν_j(A).
4. Majorants. For k ∈ ℕ let h_k := 1/(k + 1) and F_{j,k}(s) := (k + 1)·ρ_j((s − h_k, s)). By step 3, F_{j,k} is Borel and ∫ F_{j,k} dλ = (k + 1)·ofReal(h_k)·ν_j(A) = ν_j(A). Let G_j(s) := liminf_{k→∞} F_{j,k}(s), a Borel function. Fatou's lemma gives ∫ G_j dλ ≤ liminf_k ∫ F_{j,k} dλ = ν_j(A) < ∞; hence G_j < ∞ a.e., and, intersecting countably many full-measure sets, a.e. s satisfies G_j(s) < ∞ for every j.
5. Fatou in j. H(s) := liminf_{j→∞} G_j(s) is Borel and ∫ H dλ ≤ liminf_j ∫ G_j dλ ≤ liminf_j ν_j(A) = 0, because ν_j(A) → 0. Hence H = 0 a.e.
6. Atoms. For each j the measure κ_j⌞A is finite. The level sets {f = s}, s ∈ ℝ, are pairwise disjoint, so (κ_j⌞A)({f = s}) > 0 for at most countably many s (Mathlib Measure.countable_meas_level_set_pos). Countable sets are λ-null, so for a.e. s: (κ_j⌞A)({f = s}) = 0 for every j.
7. The level. λ((a, b)) = b − a > 0. By steps 4–6, a.e. s ∈ (a, b) satisfies H(s) = 0, G_j(s) < ∞ for every j, and (κ_j⌞A)({f = s}) = 0 for every j. A full-measure subset of a set of positive measure is nonempty, so there is t ∈ (a, b) with these three properties.
8. (i). Since t ∈ (a, b), {f = t} ⊆ A, so κ_j({f = t}) = κ_j({f = t} ∩ A) = (κ_j⌞A)({f = t}) = 0.
9. D_j(t) ≤ G_j(t). Put u_j(h) := ofReal(h⁻¹)·ν_j({t − h < f < t}). The sequence h_k tends to 0 through positive values, i.e. along atTop it tends to 0 within (0, ∞); a liminf along the finer filter (the image of atTop under k ↦ h_k) is at least the liminf along 𝓝[>] 0, so D_j(t) ≤ liminf_k u_j(h_k). For all k with h_k < t − a (all large k, since h_k → 0 < t − a): a < t − h_k and t < b give {t − h_k < f < t} ⊆ A, so ν_j({t − h_k < f < t}) = ν_j(f⁻¹((t − h_k, t)) ∩ A) = ρ_j((t − h_k, t)); and ofReal(h_k⁻¹) = k + 1. Hence u_j(h_k) = F_{j,k}(t) for all large k, and liminf_k u_j(h_k) = G_j(t). Therefore D_j(t) ≤ G_j(t).
10. (ii). D_j(t) ≤ G_j(t) < ∞ by steps 7 and 9.
11. (iii). liminf_j G_j(t) = H(t) = 0, so for every n ∈ ℕ there are infinitely many j with G_j(t) < 1/(n + 1). Choose φ(0) < φ(1) < ⋯ inductively with G_{φ(n)}(t) < 1/(n + 1) (Mathlib extraction_forall_of_frequently). Then 0 ≤ D_{φ(n)}(t) ≤ G_{φ(n)}(t) < 1/(n + 1) → 0. ∎

Appendix (verified Lean realization of the numbered proof above; not part of the proof). The declaration below was compiled in this decomposition session with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b366308, placed after `import GMT.Ch07.Submission` in the child comparator scope (inside `namespace GMT.Ch07` with the frozen contract's `open` commands, after its `noncomputable section ... end`). `exact Submission.lcmp_exists_good_slice_level` closes the frozen type, and `#print axioms` reports only propext, Classical.choice and Quot.sound. In the code, `ρ j` is the pushforward measure ρ_j of step 2 and `D j` is the majorant G_j of steps 4–11.

```lean
theorem Submission.lcmp_exists_good_slice_level : ∀ (P : ℕ) (ν κ : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (a b : ℝ), Measurable f → a < b → (∀ j, ν j {x | a < f x ∧ f x < b} < ∞) → Tendsto (fun j => ν j {x | a < f x ∧ f x < b}) atTop (𝓝 0) → (∀ j, κ j {x | a < f x ∧ f x < b} < ∞) → ∃ t ∈ Ioo a b, ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ j, κ j {x | f x = t} = 0) ∧ (∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν j {x | t - h < f x ∧ f x < t}) (𝓝[>] 0) < ∞) ∧ Tendsto (fun j => liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (φ j) {x | t - h < f x ∧ f x < t}) (𝓝[>] 0)) atTop (𝓝 0) := by
  intro P ν κ f a b hf hab hνfin hνlim hκfin
  obtain ⟨A, hA⟩ : ∃ A : Set (Euclid P), A = {x | a < f x ∧ f x < b} := ⟨_, rfl⟩
  rw [← hA] at hνfin hνlim hκfin
  have hAm : MeasurableSet A := by
    rw [hA]
    exact (measurableSet_lt measurable_const hf).inter (measurableSet_lt hf measurable_const)
  -- Step 1: push the restricted measures forward to the line
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → Measure ℝ, ρ = fun j => ((ν j).restrict A).map f := ⟨_, rfl⟩
  have hρapp : ∀ j (s : Set ℝ), MeasurableSet s → ρ j s = ν j (f ⁻¹' s ∩ A) := by
    intro j s hs
    rw [hρ, Measure.map_apply hf hs, Measure.restrict_apply (hf hs)]
  have hρuniv : ∀ j, ρ j univ = ν j A := by
    intro j
    rw [hρapp j univ MeasurableSet.univ, preimage_univ, univ_inter]
  have hρfin : ∀ j, IsFiniteMeasure (ρ j) := fun j => ⟨by rw [hρuniv]; exact hνfin j⟩
  -- Step 2: Tonelli for the strips
  have hSm : ∀ c : ℝ, MeasurableSet {p : ℝ × ℝ | p.1 - c < p.2 ∧ p.2 < p.1} := fun c =>
    (measurableSet_lt (measurable_fst.sub_const c) measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have hsec : ∀ c t : ℝ, Prod.mk t ⁻¹' {p : ℝ × ℝ | p.1 - c < p.2 ∧ p.2 < p.1} = Ioo (t - c) t := by
    intro c t
    ext y
    simp [mem_Ioo]
  have hsec' : ∀ c y : ℝ,
      (fun t => (t, y)) ⁻¹' {p : ℝ × ℝ | p.1 - c < p.2 ∧ p.2 < p.1} = Ioo y (y + c) := by
    intro c y
    ext t
    simp only [mem_preimage, mem_ofPred_eq, mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hmeasF : ∀ j (c : ℝ), Measurable fun t : ℝ => ρ j (Ioo (t - c) t) := by
    intro j c
    have := hρfin j
    have := measurable_measure_prodMk_left (ν := ρ j) (hSm c)
    simpa only [hsec] using this
  have hTon : ∀ j (c : ℝ), ∫⁻ t, ρ j (Ioo (t - c) t) = ENNReal.ofReal c * ν j A := by
    intro j c
    have := hρfin j
    have h1 := Measure.prod_apply (μ := (volume : Measure ℝ)) (ν := ρ j) (hSm c)
    have h2 := Measure.prod_apply_symm (μ := (volume : Measure ℝ)) (ν := ρ j) (hSm c)
    simp only [hsec, hsec', Real.volume_Ioo, add_sub_cancel_left] at h1 h2
    rw [← h1, h2, lintegral_const, hρuniv]
  -- Step 3: the sequential majorants D_j and their integrals
  have hFm : ∀ j (k : ℕ),
      Measurable fun t : ℝ => ((k : ℝ≥0∞) + 1) * ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t) :=
    fun j k => (hmeasF j _).const_mul _
  have hcancel : ∀ k : ℕ, ((k : ℝ≥0∞) + 1) * ENNReal.ofReal (1 / ((k : ℝ) + 1)) = 1 := by
    intro k
    have hk : ENNReal.ofReal ((k : ℝ) + 1) = (k : ℝ≥0∞) + 1 := by
      rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
        ENNReal.ofReal_one]
    rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), hk,
      ENNReal.mul_inv_cancel (by simp) (by simp)]
  have hFint : ∀ j (k : ℕ),
      ∫⁻ t, ((k : ℝ≥0∞) + 1) * ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t) = ν j A := by
    intro j k
    rw [lintegral_const_mul _ (hmeasF j _), hTon j, ← mul_assoc, hcancel, one_mul]
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ → ℝ≥0∞, D = fun j t =>
      liminf (fun k : ℕ => ((k : ℝ≥0∞) + 1) * ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t)) atTop :=
    ⟨_, rfl⟩
  have hDm : ∀ j, Measurable (D j) := fun j => by
    rw [hD]
    exact Measurable.liminf (hFm j)
  have hDint : ∀ j, ∫⁻ t, D j t ≤ ν j A := by
    intro j
    rw [hD]
    calc ∫⁻ t, liminf (fun k : ℕ => ((k : ℝ≥0∞) + 1) * ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t)) atTop
        ≤ liminf (fun k : ℕ => ∫⁻ t, ((k : ℝ≥0∞) + 1) * ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t))
          atTop := lintegral_liminf_le (hFm j)
      _ = ν j A := by simp only [hFint, liminf_const]
  -- Step 4: Fatou in j
  have hHm : Measurable fun t => liminf (fun j => D j t) atTop := Measurable.liminf hDm
  have hHint : ∫⁻ t, liminf (fun j => D j t) atTop = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ t, liminf (fun j => D j t) atTop ≤ liminf (fun j => ∫⁻ t, D j t) atTop :=
          lintegral_liminf_le hDm
      _ ≤ liminf (fun j => ν j A) atTop := liminf_le_liminf (Eventually.of_forall hDint)
      _ = 0 := hνlim.liminf_eq
  have hH0 : ∀ᵐ t, liminf (fun j => D j t) atTop = 0 :=
    ((lintegral_eq_zero_iff hHm).1 hHint).mono fun t ht => ht
  have hDfin : ∀ᵐ t, ∀ j, D j t < ∞ :=
    ae_all_iff.2 fun j => ae_lt_top (hDm j) ((hDint j).trans_lt (hνfin j)).ne
  -- Step 5: atoms of κ_j on the level sets
  have hatomsAE : ∀ᵐ s : ℝ, ∀ j, (κ j).restrict A {x | f x = s} = 0 := by
    rw [ae_all_iff]
    intro j
    have : IsFiniteMeasure ((κ j).restrict A) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hκfin j⟩
    have hc := Measure.countable_meas_level_set_pos (μ := (κ j).restrict A) hf
    filter_upwards [hc.ae_notMem (volume : Measure ℝ)] with s hs
    simp only [not_lt, nonpos_iff_eq_zero] at hs
    exact hs
  -- Step 6: the good level
  have hIoo : volume (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    simpa using hab
  have : (ae (volume.restrict (Ioo a b))).NeBot :=
    ae_neBot.2 (by rw [Ne, Measure.restrict_eq_zero]; exact hIoo)
  have hgood : ∀ᵐ s ∂(volume.restrict (Ioo a b)), s ∈ Ioo a b ∧
      liminf (fun j => D j s) atTop = 0 ∧ (∀ j, D j s < ∞) ∧
      ∀ j, (κ j).restrict A {x | f x = s} = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hH0,
      ae_restrict_of_ae hDfin, ae_restrict_of_ae hatomsAE] with s h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨t, ht, hHt, hDt, hκt⟩ := hgood.exists
  -- Step 7: the one-sided difference quotients are dominated by D_j(t)
  have hlink : ∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν j {x | t - h < f x ∧ f x < t})
      (𝓝[>] 0) ≤ D j t := by
    intro j
    have hseq : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun k => ?_⟩
      show (0 : ℝ) < 1 / ((k : ℝ) + 1)
      positivity
    have hle := liminf_le_liminf_of_le
      (u := fun h : ℝ => ENNReal.ofReal h⁻¹ * ν j {x | t - h < f x ∧ f x < t}) hseq
    refine hle.trans (le_of_eq ?_)
    rw [hD]
    show liminf ((fun h : ℝ => ENNReal.ofReal h⁻¹ * ν j {x | t - h < f x ∧ f x < t}) ∘
      fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop = _
    apply liminf_congr
    have hsmall : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < t - a :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds (sub_pos.2 ht.1))
    filter_upwards [hsmall] with k hk
    simp only [Function.comp_apply]
    have h1 : ENNReal.ofReal (1 / ((k : ℝ) + 1))⁻¹ = (k : ℝ≥0∞) + 1 := by
      rw [one_div, inv_inv, ENNReal.ofReal_add (by positivity) zero_le_one,
        ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    have h2 : ν j {x | t - 1 / ((k : ℝ) + 1) < f x ∧ f x < t} =
        ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t) := by
      rw [hρapp j _ measurableSet_Ioo]
      congr 1
      ext x
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioo, hA]
      constructor
      · rintro ⟨h3, h4⟩
        refine ⟨⟨h3, h4⟩, ?_, ?_⟩ <;> linarith [ht.2]
      · rintro ⟨⟨h3, h4⟩, -⟩
        exact ⟨h3, h4⟩
    rw [h1, h2]
  -- Step 8: the subsequence
  have hfreq : ∀ n : ℕ, ∃ᶠ j in atTop, D j t < ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    refine frequently_lt_of_liminf_lt (by isBoundedDefault) ?_
    rw [hHt]
    exact ENNReal.inv_pos.2 (by simp)
  obtain ⟨φ, hφ, hφlt⟩ := extraction_forall_of_frequently hfreq
  refine ⟨t, ht, φ, hφ, fun j => ?_, fun j => (hlink j).trans_lt (hDt j), ?_⟩
  · have hsubA : {x | f x = t} ⊆ A := by
      intro x hx
      rw [hA]
      simp only [mem_ofPred_eq] at hx ⊢
      rw [hx]
      exact ht
    have h := hκt j
    rwa [Measure.restrict_apply (measurableSet_eq_fun hf measurable_const),
      inter_eq_left.2 hsubA] at h
  · have hinv : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv (fun _ => zero_le)
      (fun n => (hlink (φ n)).trans (hφlt n).le)
```

## Key steps

1. Push ν_j⌞A forward by f to a finite measure ρ_j on ℝ; Tonelli on S_c = {s − c < y < s} gives ∫ ρ_j((s − c, s)) ds = c·ν_j(A).
2. G_j(s) := liminf_k (k + 1)·ρ_j((s − 1/(k + 1), s)) is Borel with ∫ G_j ≤ ν_j(A) (Fatou), so G_j < ∞ a.e.
3. Fatou in j: liminf_j G_j = 0 a.e.; for each j only countably many levels are atoms of κ_j⌞A.
4. Pick a good t ∈ (a, b): κ_j({f = t}) = 0, and D_j(t) ≤ G_j(t) < ∞ via h_k = 1/(k + 1) and {t − h_k < f < t} ⊆ A.
5. Extract φ with G_{φ(n)}(t) < 1/(n + 1), so D_{φ(n)}(t) → 0.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical); cat local-references/123e8435b4a2469b/manifest.json`
- `rg -n 'lcmp_|good_slice|lipschitz_cutoff' local-references/123e8435b4a2469b/project (no match)`
- `rg -n 'theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc|theorem countable_meas_level_set_pos|theorem IsOpen.exists_contDiff_support_eq|theorem prod_apply_symm|theorem measurable_measure_prodMk_left|theorem lintegral_liminf_le|theorem extraction_forall_of_frequently|theorem integral_withDensity_eq_integral_smul|theorem tendsto_measure_iInter_atTop|theorem closure_eq_iInter_thickening' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'; rg -n 'theorem (one_of_one_le|zero_of_nonpos|le_one|nonneg)|protected theorem contDiff' .../Analysis/SpecialFunctions/SmoothTransition.lean`
- `lake env lean /tmp/lcmp/Names.lean, Names2.lean, Names3.lean, N4.lean (#check of every cited Mathlib/SimonGMT declaration after import GMT.Ch07.Submission; MonotoneOn.intervalIntegral_deriv_mem_uIcc and MonotoneOn.intervalIntegrable_deriv are not in the import closure)`
- `sed SimonGMT Chapter06/{Mass,Currents,CurrentLocalEquality,Forms}.lean (massOn, massAdmissibleOn, covectorEuclideanNorm_neg, le_massOn, massOn_mono, boundary_apply, boundary_boundary, zeroRegion/support, TestFormOn); rg -n -i 'slice by|lipschitz slic|flat norm|deformation theorem' Chapter06 (no match)`
- `python3 -I scans of dag.json: lean_statement/status/children/depends_on of all 514 nodes; sibling frozen types of the selected node; accepted nodes mentioning support/massOn/IMRep/withDensity (155); smooth cut-off and mass-triangle candidates; collision check of the 8 proposed names`
- `grep -c of the six lcmp_ names in dag.json, issue-workers.json, DAG.md, GMT/, .lake/packages/simongmt; git grep -l lcmp_ over all 1117 distinct ref commits -- GMT (no match)`
- `git show 02c6122c94d0280a6288d299659b2dab7b59e109:GMT/Ch07/Submission.lean and 702e7082a5a7012f7a8f6efd9d272697e426f50b:GMT/Ch07/Submission.lean (accepted proofs of the two reused declarations)`
- `sed -n 3160,3230p and 6557,6600p runtime.py (_overlay_accepted_children: prerequisites = children + depends_on; _existing_lean_name_problem: reuse only for accepted identical types); sed -n 480,620p verifier/gmt-compare.py (contract_scope, child_modules)`
- `lake env lean /tmp/lcmp/Types1.lean; /tmp/lcmp/AsmFinal.lean; /tmp/lcmp/Validate.lean; /tmp/lcmp/FinalCheck.lean (#print axioms)`
- `sed -n 150,262p book/chapter-07.txt (Simon 7.2.4 proof, (1)–(12))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/lcmp/Types1.lean`
- `/tmp/lcmp/AsmFinal.lean`
- `/tmp/lcmp/Validate.lean`
- `/tmp/lcmp/FinalCheck.lean`
- `/tmp/lcmp/out/subproblems.json`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (manifest: project b4d606db, mathlib 25730c7c), and the snapshot project contains no lcmp_ declaration. Neither the snapshot Mathlib nor the pinned SimonGMT states any of the six new child facts: Lipschitz cut-off, good slicing level, mass localization, mass triangle inequality, IMRep restriction calculus, compact outer bound. SimonGMT Chapter06 has only massOn/le_massOn/massOn_mono and covectorEuclideanNorm_neg. Every Mathlib declaration cited in the child proofs is located in the snapshot and checked importable after import GMT.Ch07.Submission. The exception is MonotoneOn.intervalIntegral_deriv_mem_uIcc (DerivIntegrable.lean): it is cited by the parent's step 5 but is not imported, so child good_slice_level uses a Tonelli-based majorant instead. Two accepted DAG declarations with byte-identical frozen types are reused: rsd_cmr_support_subset_of_vanish and rsd_imrep_compact_measure_ne_top. In Lean: all eight child types elaborate in the comparator scope, and all eight child proofs compile with only propext, Classical.choice and Quot.sound. A conditional assembly from the six exact sibling types plus the eight child types proves the exact frozen parent type, with the same axioms. Simon's text (chapter-07.txt lines 176–258) confirms the parent's corrections S̃_j = S_j⌞W_α − P_j and γ ↑ α.
