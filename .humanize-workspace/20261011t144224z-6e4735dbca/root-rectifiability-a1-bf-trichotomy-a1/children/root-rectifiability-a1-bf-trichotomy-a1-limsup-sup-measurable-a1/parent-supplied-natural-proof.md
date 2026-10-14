# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.bf_trichotomy-a1`
- Child DAG node: `root.rectifiability-a1.bf_trichotomy-a1.limsup_sup_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2(a)-(c) of the parent-supplied proof of rectifiability_bf_trichotomy (P. Mattila, Geometry of Sets and Measures in Euclidean Spaces, Lemma 18.9; R. Hovila, E. Järvenpää, M. Järvenpää, F. Ledrappier, Geom. Dedicata 161 (2012), arXiv:1104.3453, Lemma 2.4). There, the supremum over r may be taken over rational r by left continuity in r, and the limsup over s along rational s by the scaling estimate F(s) ≤ (s′/s)ᵏF(s′). The statement here is for an abstract measurable family G, so that it serves both the cone ratio Φ(a,v) (sibling cone_ratio_measurable) and the slice densities ϑ_j (sibling slice_density_null). The sets G(r,s) are only assumed measurable, so the section measures are shown measurable by Tonelli's theorem instead of the Fatou/semicontinuity argument of 2(a).

Notation. c(x) := ENNReal.ofReal x for x ∈ ℝ. For z ∈ Z and r, s ∈ ℝ put g(z,r,s) := μ({y : (z,y) ∈ G(r,s)}), R(z,r,s) := g(z,r,s)/c((rs)ᵏ) and F(z,s) := sup_{r∈(0,δ)} R(z,r,s), so that Φ(z) = limsup_{s→0⁺} F(z,s). ℚ is viewed inside ℝ.

1. Measurable sections. Fix r, s. The set {y : (z,y) ∈ G(r,s)} is the preimage Prod.mk z ⁻¹' G(r,s). G(r,s) is measurable in Z × Y and μ is s-finite, so z ↦ μ(Prod.mk z ⁻¹' G(r,s)) is measurable (Tonelli; Mathlib measurable_measure_prodMk_left). Hence z ↦ R(z,r,s) = g(z,r,s)·c((rs)ᵏ)⁻¹ is measurable.

2. Monotonicity in r. If 0 < r₁ ≤ r₂, then G(r₁,s) ⊆ G(r₂,s). For r₁ = r₂ this is trivial. For r₁ < r₂ we have r₁ ∈ (0,r₂), so G(r₁,s) ⊆ ⋃_{r′∈(0,r₂)} G(r′,s) = G(r₂,s) by (ii). Hence g(z,r₁,s) ≤ g(z,r₂,s).

3. Rational radii. Let z ∈ Z, s > 0 and r ∈ (0,δ). Then R(z,r,s) ≤ sup_{q∈ℚ∩(0,δ)} R(z,q,s). Consequently F(z,s) = sup_{q∈ℚ∩(0,δ)} R(z,q,s) for every s > 0; the inequality ≥ holds because ℚ∩(0,δ) ⊆ (0,δ).
 Proof. Let Q_r := ℚ∩(0,r), a countable set.
 - By (ii), G(r,s) = ⋃_{r′∈(0,r)} G(r′,s).
 - Each r′ ∈ (0,r) lies below some q ∈ Q_r (density of ℚ: pick q ∈ (r′,r)), and then G(r′,s) ⊆ G(q,s) by step 2. Also G(q,s) ⊆ G(r,s) for q ∈ Q_r, by step 2.
 - Hence G(r,s) = ⋃_{q∈Q_r} G(q,s). Taking sections at z, {y : (z,y) ∈ G(r,s)} = ⋃_{q∈Q_r} {y : (z,y) ∈ G(q,s)}.
 - This countable family is directed by inclusion: by step 2, the sets for q and q′ are contained in the set for max(q,q′) ∈ Q_r. Continuity from below for directed countable families (Mathlib Directed.measure_iUnion or measure_biUnion_eq_iSup; the sets need not be measurable) gives g(z,r,s) = sup_{q∈Q_r} g(z,q,s).
 - For q ∈ Q_r we have 0 < qs < rs, so c((qs)ᵏ) ≤ c((rs)ᵏ). Therefore g(z,q,s)/c((rs)ᵏ) ≤ g(z,q,s)/c((qs)ᵏ) = R(z,q,s) (ENNReal.div_le_div_left).
 - Using (sup_q x_q)/b = sup_q (x_q/b) (ENNReal.iSup_div), we get R(z,r,s) = sup_{q∈Q_r} g(z,q,s)/c((rs)ᵏ) ≤ sup_{q∈Q_r} R(z,q,s) ≤ sup_{q∈ℚ∩(0,δ)} R(z,q,s), since Q_r ⊆ ℚ∩(0,δ) (as r < δ).

4. Scaling in s. Let 0 < s ≤ s′. Then F(z,s) ≤ c((s′/s)ᵏ)·F(z,s′) for every z.
 Proof. Fix r ∈ (0,δ).
 - By (i), G(r,s) ⊆ G(r,s′), so g(z,r,s) ≤ g(z,r,s′).
 - As r, s, s′ > 0, (rs′)ᵏ = (s′/s)ᵏ·(rs)ᵏ with both factors positive. So c((rs′)ᵏ) = c((s′/s)ᵏ)·c((rs)ᵏ) (ENNReal.ofReal_mul), and all three numbers lie in (0,∞).
 - Hence R(z,r,s) = g(z,r,s)/c((rs)ᵏ) ≤ g(z,r,s′)/c((rs)ᵏ) = c((s′/s)ᵏ)·g(z,r,s′)/c((rs′)ᵏ) = c((s′/s)ᵏ)·R(z,r,s′) ≤ c((s′/s)ᵏ)·F(z,s′).
 - Taking the supremum over r ∈ (0,δ) gives the claim.

5. Rational s. For every z and every ε > 0, sup_{s∈(0,ε)} F(z,s) = sup_{q∈ℚ∩(0,ε)} F(z,q).
 Proof. The inequality ≥ is clear. Put T := sup_{q∈ℚ∩(0,ε)} F(z,q) and fix s ∈ (0,ε); we show F(z,s) ≤ T.
 - If T = ∞ there is nothing to prove, so let T < ∞.
 - For n ∈ ℕ choose a rational q_n with s < q_n < min(ε, s(1 + 1/(n+1))); the interval is nonempty and ℚ is dense.
 - By step 4 and q_n/s ≤ 1 + 1/(n+1), F(z,s) ≤ c((q_n/s)ᵏ)·F(z,q_n) ≤ c((1 + 1/(n+1))ᵏ)·T.
 - As n → ∞, (1 + 1/(n+1))ᵏ → 1, so c((1 + 1/(n+1))ᵏ)·T → c(1)·T = T. This uses continuity of ENNReal.ofReal and of multiplication by the finite constant T. Hence F(z,s) ≤ T. In Lean: F(z,s) ≤ c((1+1/(n+1))ᵏ)·T for all n, T ≠ ⊤ and c((1+1/(n+1))ᵏ) → 1, so le_of_tendsto' with ENNReal.Tendsto.mul_const gives F(z,s) ≤ T.

6. Countable formula. Apply the sibling limsup_eq_iinf (Submission.rectifiability_mickle_rado_limsup_eq_iInf) to f := F(z,·): Φ(z) = inf_{n∈ℕ} sup_{s∈(0,1/(n+1))} F(z,s). Step 5 with ε = 1/(n+1), then step 3 (all q there are > 0), give for every z ∈ Z
 Φ(z) = inf_{n∈ℕ} sup_{q∈ℚ∩(0,1/(n+1))} sup_{q′∈ℚ∩(0,δ)} R(z,q′,q).

7. Conclusion. By step 1, each z ↦ R(z,q′,q) is measurable. Suprema over the countable sets ℚ∩(0,1/(n+1)) and ℚ∩(0,δ), and the infimum over n ∈ ℕ, of measurable [0,∞]-valued functions are measurable (Mathlib Measurable.biSup with Set.Countable, Measurable.iSup, Measurable.iInf; [0,∞] is a second-countable complete linear order with its Borel σ-algebra). Hence the right side of step 6 is a measurable function of z. It agrees with Φ at every z, so Φ is measurable (funext / Measurable.congr). ∎

Lean reference proof (appendix; written by the independent Lean reviewer of this decomposition and re-compiled by the author). It is compile-checked as a single declaration against the exact frozen statement inside `namespace GMT.Ch06` of a scratch copy of the frozen project (commit d8d46c9587747dee0751a1f780fcafdba16a3886, Lean v4.35.0-rc3, pinned Mathlib 25730c7c), with its declared sibling dependency Submission.rectifiability_mickle_rado_limsup_eq_iInf present as a theorem of its exact frozen type; with that sibling proved, #print axioms = [propext, Classical.choice, Quot.sound]. It introduces no auxiliary declarations.
```lean
theorem Submission.rectifiability_bf_limsup_sup_measurable : (∀ (Z Y : Type) [MeasurableSpace Z] [MeasurableSpace Y] (k : ℕ) (μ : Measure Y) (δ : ℝ) (G : ℝ → ℝ → Set (Z × Y)), SFinite μ → (∀ r s, MeasurableSet (G r s)) → (∀ r s s', s ≤ s' → G r s ⊆ G r s') → (∀ r s, 0 < r → G r s = ⋃ r' ∈ Ioo (0 : ℝ) r, G r' s) → Measurable (fun z : Z => limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {y | (z, y) ∈ G r s} / ENNReal.ofReal ((r * s) ^ k)) (𝓝[>] 0))) := by
  intro Z Y _ _ k μ δ G hμ hG hmono hcont
  -- g z r s := μ (section), F z s := sup over r
  let g : Z → ℝ → ℝ → ℝ≥0∞ := fun z r s => μ {y | (z, y) ∈ G r s}
  let F : Z → ℝ → ℝ≥0∞ := fun z s => ⨆ r ∈ Ioo (0 : ℝ) δ, g z r s / ENNReal.ofReal ((r * s) ^ k)
  show Measurable fun z => limsup (F z) (𝓝[>] 0)
  have hgm : ∀ r s, Measurable fun z => g z r s := fun r s => measurable_measure_prodMk_left (hG r s)
  -- monotone in r
  have hGr : ∀ s r₁ r₂, 0 < r₁ → r₁ ≤ r₂ → G r₁ s ⊆ G r₂ s := by
    intro s r₁ r₂ h1 h12
    rcases h12.lt_or_eq with h | rfl
    · rw [hcont r₂ s (h1.trans h)]
      exact subset_biUnion_of_mem (u := fun r' => G r' s) ⟨h1, h⟩
    · exact le_rfl
  -- rational radii
  have hFq : ∀ z s, 0 < s → F z s = ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) δ),
      g z q s / ENNReal.ofReal (((q : ℝ) * s) ^ k) := by
    intro z s hs
    apply le_antisymm
    · refine iSup₂_le fun r hr => ?_
      have hU : {y | (z, y) ∈ G r s} =
          ⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < r}, {y | (z, y) ∈ G (q.1 : ℝ) s} := by
        ext y
        simp only [mem_iUnion, mem_ofPred_eq]
        constructor
        · intro hy
          rw [hcont r s hr.1] at hy
          simp only [mem_iUnion] at hy
          obtain ⟨r', hr', hy'⟩ := hy
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hr'.2
          exact ⟨⟨q, hr'.1.trans hq1, hq2⟩, hGr s r' q hr'.1 hq1.le hy'⟩
        · rintro ⟨q, hy⟩
          exact hGr s q r q.2.1 q.2.2.le hy
      have hdir : Directed (· ⊆ ·)
          (fun q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < r} => {y | (z, y) ∈ G (q.1 : ℝ) s}) := by
        intro q₁ q₂
        refine ⟨⟨max q₁.1 q₂.1, ?_, ?_⟩, ?_, ?_⟩
        · exact lt_of_lt_of_le q₁.2.1 (by exact_mod_cast le_max_left q₁.1 q₂.1)
        · rw [Rat.cast_max]; exact max_lt q₁.2.2 q₂.2.2
        · intro y hy
          exact hGr s q₁.1 _ q₁.2.1 (by exact_mod_cast le_max_left q₁.1 q₂.1) hy
        · intro y hy
          exact hGr s q₂.1 _ q₂.2.1 (by exact_mod_cast le_max_right q₁.1 q₂.1) hy
      have hgr : g z r s = ⨆ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < r}, g z (q.1 : ℝ) s := by
        show μ {y | (z, y) ∈ G r s} = _
        rw [hU]
        exact hdir.measure_iUnion
      rw [hgr, ENNReal.iSup_div]
      refine iSup_le fun q => ?_
      refine le_trans ?_ (le_iSup₂ (f := fun (q : ℚ) (_ : (q : ℝ) ∈ Ioo (0 : ℝ) δ) =>
        g z q s / ENNReal.ofReal (((q : ℝ) * s) ^ k)) q.1 ⟨q.2.1, q.2.2.trans hr.2⟩)
      apply ENNReal.div_le_div_left
      apply ENNReal.ofReal_le_ofReal
      apply pow_le_pow_left₀ (mul_pos q.2.1 hs).le
      exact mul_le_mul_of_nonneg_right q.2.2.le hs.le
    · refine iSup_le fun q => iSup_le fun hq => ?_
      exact le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) => g z r s / ENNReal.ofReal ((r * s) ^ k))
        (q : ℝ) hq
  have hFm : ∀ s, 0 < s → Measurable fun z => F z s := by
    intro s hs
    have : (fun z => F z s) = fun z => ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) δ),
        g z q s / ENNReal.ofReal (((q : ℝ) * s) ^ k) := funext fun z => hFq z s hs
    rw [this]
    exact Measurable.iSup fun q => Measurable.iSup fun _ => (hgm q s).div_const _
  -- scaling in s
  have hscale : ∀ z s s', 0 < s → s ≤ s' → F z s ≤ ENNReal.ofReal ((s' / s) ^ k) * F z s' := by
    intro z s s' hs hss'
    refine iSup₂_le fun r hr => ?_
    have hs' : 0 < s' := hs.trans_le hss'
    have h1 : g z r s ≤ g z r s' := measure_mono (fun y hy => hmono r s s' hss' hy)
    have hA : ENNReal.ofReal ((r * s') ^ k) =
        ENNReal.ofReal ((s' / s) ^ k) * ENNReal.ofReal ((r * s) ^ k) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
      congr 2
      field_simp
    have hc0 : ENNReal.ofReal ((s' / s) ^ k) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    calc g z r s / ENNReal.ofReal ((r * s) ^ k)
        ≤ g z r s' / ENNReal.ofReal ((r * s) ^ k) := ENNReal.div_le_div_right h1 _
      _ = ENNReal.ofReal ((s' / s) ^ k) * (g z r s' / ENNReal.ofReal ((r * s') ^ k)) := by
          rw [hA, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal ((s' / s) ^ k) * F z s' := by
          gcongr
          exact le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
            g z r s' / ENNReal.ofReal ((r * s') ^ k)) r hr
  -- rational s
  have hsupq : ∀ z (ε : ℝ), 0 < ε → ⨆ s ∈ Ioo (0 : ℝ) ε, F z s =
      ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε), F z q := by
    intro z ε hε
    apply le_antisymm
    · refine iSup₂_le fun s hs => ?_
      have hn : ∀ n : ℕ, F z s ≤ ENNReal.ofReal ((1 + 1 / ((n : ℝ) + 1)) ^ k) *
          ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε), F z q := by
        intro n
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        have hlt : s < min ε (s * (1 + 1 / ((n : ℝ) + 1))) := by
          refine lt_min hs.2 ?_
          have := mul_pos hs.1 hpos
          nlinarith
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
        have hqε : (q : ℝ) < ε := hq2.trans_le (min_le_left _ _)
        have hq0 : 0 < (q : ℝ) := hs.1.trans hq1
        calc F z s ≤ ENNReal.ofReal (((q : ℝ) / s) ^ k) * F z q := hscale z s q hs.1 hq1.le
          _ ≤ ENNReal.ofReal ((1 + 1 / ((n : ℝ) + 1)) ^ k) *
              ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε), F z q := by
            gcongr ?_ * ?_
            · apply ENNReal.ofReal_le_ofReal
              apply pow_le_pow_left₀ (div_pos hq0 hs.1).le
              rw [div_le_iff₀ hs.1]
              have := hq2.trans_le (min_le_right _ _)
              linarith
            · exact le_iSup₂ (f := fun (q : ℚ) (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε) => F z q) q ⟨hq0, hqε⟩
      have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 + 1 / ((n : ℝ) + 1)) ^ k)) atTop (𝓝 1) := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.tendsto_ofReal
        have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1).pow k
        simpa using this
      have htend := ENNReal.Tendsto.mul_const h1
        (Or.inl one_ne_zero) (b := ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε), F z q)
      rw [one_mul] at htend
      exact ge_of_tendsto' htend hn
    · refine iSup_le fun q => iSup_le fun hq => ?_
      exact le_iSup₂ (f := fun s (_ : s ∈ Ioo (0 : ℝ) ε) => F z s) (q : ℝ) hq
  have hform : ∀ z, limsup (F z) (𝓝[>] 0) = ⨅ n : ℕ, ⨆ q : ℚ,
      ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1))), F z q := by
    intro z
    rw [Submission.rectifiability_mickle_rado_limsup_eq_iInf (F z)]
    congr 1
    funext n
    exact hsupq z _ (by positivity)
  rw [funext hform]
  exact Measurable.iInf fun n => Measurable.iSup fun q => Measurable.iSup fun hq => hFm q hq.1
```

## Key steps

1. Tonelli (measurable_measure_prodMk_left): z ↦ μ({y : (z,y) ∈ G(r,s)}) is measurable for each (r,s).
2. (ii) makes G monotone in r. Directed continuity from below over rational r′ < r then shows that the sup over r ∈ (0,δ) equals the sup over rational r.
3. (i) gives F(s) ≤ (s′/s)ᵏF(s′) for s ≤ s′; with rationals s′ ↓ s, the sup over s ∈ (0,ε) equals the sup over rational s.
4. limsup_eq_iinf rewrites Φ as inf_n sup_{s<1/(n+1)} F(s), a countable inf-sup of measurable functions, hence measurable.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `git archive d8d46c9 into /tmp/bft-decomp-1791847446; cmp GMT/Ch06/Submission.lean (workspace) and project/GMT/Ch06/Contract.lean (snapshot) against the scratch copy (identical); lake build GMT.Ch06.Submission (success, 3152 jobs)`
- `rg -n 'theorem ae_ae_comm|theorem measurable_measure_prodMk_left |theorem _root_.Monotone.measure_iUnion|theorem _root_.Directed.measure_iUnion|theorem measure_biUnion_eq_iSup|theorem prod_apply_symm|theorem prod_apply |lemma IsSigmaCompact.image|theorem limsup_add_le|theorem limsup_const_mul_of_ne_top|theorem inner_single_left' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n 'measure_preimage_add_right|measure_univ_of_isAddLeftInvariant|measure_univ_of_isMulLeftInvariant' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n -i 'mickle|besicovitch.federer|purely.unrectifiable' local-references/197bdd4b88278494/mathlib/Mathlib local-references/197bdd4b88278494/project (no match); rg -n 'IsSigmaCompact.measurableSet' local-references/197bdd4b88278494/mathlib/Mathlib (no match)`
- `rg -n 'def dimensionalDensityQuotient|def realUnitBallVolume' lake-packages-25730c7c/simongmt/Poincare; sed -n 1,70p Chapter01/Densities.lean`
- `python3 verifier/gmt-compare.py contract_scope + child_modules (contract mode) for all 8 child statements; lake env lean Scratch/Chal_*.lean (0 errors)`
- `lake env lean Scratch/Names.lean and Scratch/Inst.lean (#check of the cited lemma names; instance checks for IsAddHaarMeasure, IsAddRightInvariant, SFinite of volume on Fin (m+1) → Eucl N, volume univ = ⊤ on Eucl (m+1), BorelSpace of the product types)`
- `lake env lean Scratch/Assembly.lean (parent from child stubs; #print axioms), Scratch/Iface1.lean (cone_ratio_measurable proved from the limsup_sup_measurable stub; ϑ_j instance), Scratch/Iface2.lean (OuterMeasure.mk + rectifiability_mickle_rado interface; later found vacuous because of a binder capture in the test example, and superseded by the complete slice_density_null proof)`
- `python3 lean_name collision scan of dag.json and nodes/*/decomposition-v*.json (658 names); byte comparison of reused lean_statement/title/statement against dag.json and the accepted handoffs`
- `lake env lean Verify/AllProofsFull.lean (independent reviewer's complete proofs of all six new children + accepted mickle_rado subtree + parent assembly; 0 errors; #print axioms [propext, Classical.choice, Quot.sound] for every declaration) and Verify/Standalone/<key>.lean for each new child with only its declared siblings stubbed (0 errors)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-bf-trichotomy-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1-limsup-eq-iinf-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mass-measure-rectifiable-a1/decomposition-v1.json`
- `/tmp/bft-decomp-1791847446/Scratch/Assembly.lean`
- `/tmp/bft-decomp-1791847446/Scratch/Iface1.lean`
- `/tmp/bft-decomp-1791847446/Verify/AllProofsFull.lean`
- `/tmp/bft-decomp-1791847446/Verify/Standalone/slice_density_null.lean`
- `/tmp/bft-decomp-1791847446/Verify/Standalone/limsup_sup_measurable.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract, byte-identical to the workspace Submission.lean and to the scratch copy. Neither the snapshot Mathlib nor the project contains a Besicovitch–Federer, Mickle–Radó or purely-unrectifiable result (rg: no match), and Mathlib has no IsSigmaCompact.measurableSet. So all six new child obligations are genuine; the two accepted declarations rectifiability_mickle_rado and rectifiability_mickle_rado_limsup_eq_iInf are reused with byte-identical types. Every library input cited by the child proofs exists in the pinned environment: measurable_measure_prodMk_left, Measure.prod_apply and prod_apply_symm, Measure.ae_ae_comm (Prod.lean), Monotone.measure_iUnion, Directed.measure_iUnion and measure_biUnion_eq_iSup (Continuity.lean), measure_preimage_add_right and measure_univ_of_isAddLeftInvariant (additive forms of Group/Measure.lean), ENNReal.limsup_const_mul_of_ne_top (Order/Filter/ENNReal.lean), IsSigmaCompact.image, EuclideanSpace.inner_single_left (PiL2.lean:318), and dimensionalDensityQuotient and realUnitBallVolume (SimonGMT Chapter01/Densities.lean:39, Hausdorff.lean:34). ENNReal.limsup_add_le (ENNReal.lean:231) requires CountableInterFilter, which 𝓝[>]0 is not, so fibre_cone_comparison proves limsup subadditivity directly. In the scratch build, all eight child types elaborate in the comparator's exact child scope. The parent compiles from the five stubbed children it uses. Complete single-declaration Lean proofs of all six new children compile against their exact frozen types, using only their declared siblings, and with the accepted mickle_rado subtree the whole tree including Submission.rectifiability_bf_trichotomy compiles with axioms [propext, Classical.choice, Quot.sound].
