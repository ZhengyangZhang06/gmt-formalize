# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.mickle_rado-a1`
- Child DAG node: `root.rectifiability-a1.mickle_rado-a1.density_zero-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent-supplied proof (Mattila, Thm 18.5, Mickle–Radó). The parent takes a Lebesgue density point c₀ of the compact set K, fixes ε = 1/(2q²12ᵏ) and t₀, and derives ψ(B(c₀,t)) ≤ tᵏ/(2q) from the Vitali chain. Here the same estimate is run with ε ↓ 0, which shows that the upper density vanishes at every such density point. Sibling used: vitali_bound (Lean `Submission.rectifiability_mickle_rado_vitali_bound`).

Notation. k := m + 1. ℝᵏ = EuclideanSpace ℝ (Fin k). B(x,ρ) is the open ball and B̄(x,ρ) the closed ball. Lᵏ = `volume`. ω := Lᵏ(B(0,1)). For t > 0, tᵏ means ENNReal.ofReal(tᵏ) ∈ (0,∞). Arithmetic is in [0,∞]. Hypotheses: ψ is an outer measure; K is closed with ψ(K) = 0; C ∈ [0,∞) (C ≠ ∞); r > 0; (B) ψ(B(z,τ)) ≤ C·τᵏ for all z ∈ K and 0 < τ < r. Claim: for (Lᵏ⌞K)-a.e. c, limsup_{t↓0} f_c(t) = 0, where f_c(t) := ψ(B(c,t))/tᵏ.

1. Choice of good points. ℝᵏ is a finite-dimensional normed space, so it is a second-countable metric space with the Besicovitch covering property, and Lᵏ is locally finite. Lebesgue's density theorem in the form of Mathlib `Besicovitch.ae_tendsto_measure_inter_div` (applied to Lᵏ and K) gives, for (Lᵏ⌞K)-a.e. c, R_c(ρ) := Lᵏ(K ∩ B̄(c,ρ))/Lᵏ(B̄(c,ρ)) → 1 as ρ → 0⁺. Since K is closed, hence Borel, (Lᵏ⌞K)-a.e. c lies in K (Mathlib `ae_restrict_mem`). Fix c ∈ K with R_c(ρ) → 1 as ρ → 0⁺. Because 𝓝[>]0 is a nontrivial filter, it suffices to prove f_c(t) → 0 as t → 0⁺; then limsup_{t↓0} f_c(t) = 0 (Mathlib `Filter.Tendsto.limsup_eq`).
2. Measure of the closed-ball complement. Lᵏ(B(0,1)) ∈ (0,∞), so ω ∈ (0,∞). Fix ρ > 0. Put V := Lᵏ(B̄(c,ρ)) = ρᵏ·ω (Mathlib `Measure.addHaar_closedBall`, finrank = k); then V ∈ (0,∞). Put A := Lᵏ(K ∩ B̄(c,ρ)) ≤ V. Since K is measurable, Lᵏ(B̄(c,ρ)∖K) + A = V (Mathlib `measure_sdiff_add_inter`). Hence Lᵏ(B̄(c,ρ)∖K) = V − A, as A ≤ V < ∞. Also V·(A/V) = A, because 0 < V < ∞, and multiplication by the finite V distributes over truncated subtraction. Therefore Lᵏ(B̄(c,ρ)∖K) = V·(1 − A/V) = ρᵏ·ω·(1 − R_c(ρ)).
3. Pointwise bound. Let 0 < t < r/6. Then 0 < t and 6t ≤ r, and c ∈ K. So vitali_bound (with c₀ := c) gives ψ(B(c,t))·ω ≤ C·6ᵏ·Lᵏ(B(c,2t)∖K). Since B(c,2t)∖K ⊆ B̄(c,2t)∖K, step 2 with ρ = 2t gives
 ψ(B(c,t))·ω ≤ C·6ᵏ·(2t)ᵏ·ω·(1 − R_c(2t)) = [C·12ᵏ·(1 − R_c(2t))·tᵏ]·ω,
 using (2t)ᵏ = 2ᵏ·tᵏ and 6ᵏ·2ᵏ = 12ᵏ. Cancel the factor ω ∈ (0,∞) (Mathlib `ENNReal.mul_le_mul_iff_left`) to get ψ(B(c,t)) ≤ C·12ᵏ·(1 − R_c(2t))·tᵏ. As tᵏ ∈ (0,∞), this means f_c(t) ≤ h(t) := C·12ᵏ·(1 − R_c(2t)) (Mathlib `ENNReal.div_le_iff_le_mul`).
4. Limit of the bound. As t → 0⁺, also 2t → 0⁺: the map t ↦ 2t sends 𝓝[>]0 into 𝓝[>]0. So R_c(2t) → 1. Truncated subtraction on [0,∞] is continuous at (1,1) (Mathlib `ENNReal.Tendsto.sub`), so 1 − R_c(2t) → 0. Since C·12ᵏ < ∞ (as C ≠ ∞), h(t) → C·12ᵏ·0 = 0 (Mathlib `ENNReal.Tendsto.const_mul`).
5. Squeeze. We have 0 ≤ f_c(t) ≤ h(t) for all t in (0, r/6), which belongs to 𝓝[>]0, and h(t) → 0. By the squeeze theorem f_c(t) → 0 as t → 0⁺ (Mathlib `tendsto_of_tendsto_of_tendsto_of_le_of_le'`). By step 1, limsup_{t↓0} ψ(B(c,t))/tᵏ = 0. This holds for (Lᵏ⌞K)-a.e. c. ∎

Lean reference proof (appendix; compile-checked as a single declaration inside `namespace GMT.Ch06` of a scratch copy of the frozen project, commit d8d46c9587747dee0751a1f780fcafdba16a3886, Lean v4.35.0-rc3, pinned Mathlib 25730c7c; `#print axioms` = [propext, Classical.choice, Quot.sound]; it introduces no auxiliary declarations):
```lean
theorem Submission.rectifiability_mickle_rado_density_zero : ∀ (m : ℕ) (ψ : OuterMeasure (Eucl (m + 1))) (K : Set (Eucl (m + 1))) (C : ℝ≥0∞) (r : ℝ), IsClosed K → ψ K = 0 → C ≠ ⊤ → 0 < r → (∀ z ∈ K, ∀ τ ∈ Ioo (0 : ℝ) r, ψ (ball z τ) ≤ C * ENNReal.ofReal (τ ^ (m + 1))) → ∀ᵐ c ∂((volume : Measure (Eucl (m + 1))).restrict K), limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) = 0 := by
  intro m ψ K C r hK hψK hC hr hbound
  set μ : Measure (Eucl (m + 1)) := volume with hμ
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ K, ae_restrict_mem hK.measurableSet]
    with c hc hcK
  apply Tendsto.limsup_eq
  set ω := μ (ball 0 1) with hω
  have hω0 : ω ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hωtop : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hfin : Module.finrank ℝ (Eucl (m + 1)) = m + 1 := finrank_euclideanSpace_fin
  -- the density ratio at radius 2t
  have hR2 : Tendsto (fun t : ℝ => μ (K ∩ closedBall c (2 * t)) / μ (closedBall c (2 * t)))
      (𝓝[>] 0) (𝓝 1) := by
    refine hc.comp ?_
    have h2 : Tendsto (fun t : ℝ => 2 * t) (𝓝[>] 0) (𝓝[>] (2 * 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_const.mul continuous_id).tendsto' _ _ rfl |>.mono_left nhdsWithin_le_nhds)
        (by filter_upwards [self_mem_nhdsWithin] with t ht; exact mem_Ioi.2 (by simpa using ht))
    simpa using h2
  have hlim : Tendsto (fun t : ℝ => C * 12 ^ (m + 1) *
      (1 - μ (K ∩ closedBall c (2 * t)) / μ (closedBall c (2 * t)))) (𝓝[>] 0) (𝓝 0) := by
    have h1 := ENNReal.Tendsto.sub tendsto_const_nhds hR2 (Or.inl ENNReal.one_ne_top)
    have h12 : C * 12 ^ (m + 1) ≠ ⊤ := ENNReal.mul_ne_top hC (ENNReal.pow_ne_top (by norm_num))
    have h2 := ENNReal.Tendsto.const_mul (a := C * 12 ^ (m + 1)) h1 (Or.inr h12)
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r / 6 by positivity)] with t ht
  have ht0 : 0 < t := ht.1
  have h0 := Submission.rectifiability_mickle_rado_vitali_bound m ψ K C r hK hψK hbound c hcK t ht0
    (by linarith [ht.2])
  -- measure of the complement in the closed ball
  set V := μ (closedBall c (2 * t)) with hV
  set A := μ (K ∩ closedBall c (2 * t)) with hA
  have hVball : V = ENNReal.ofReal ((2 * t) ^ (m + 1)) * ω := by
    rw [hV, Measure.addHaar_closedBall μ c (by positivity), hfin]
  have hV0 : V ≠ 0 := by
    rw [hVball]; exact mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne' hω0
  have hVtop : V ≠ ⊤ := measure_closedBall_lt_top.ne
  have hAle : A ≤ V := measure_mono inter_subset_right
  have hdiff : μ (ball c (2 * t) \ K) ≤ V * (1 - A / V) := by
    have hsplit : μ (closedBall c (2 * t) \ K) + A = V := by
      rw [hA, inter_comm]; exact measure_sdiff_add_inter _ hK.measurableSet
    have h1 : μ (ball c (2 * t) \ K) ≤ μ (closedBall c (2 * t) \ K) :=
      measure_mono (sdiff_subset_sdiff_left ball_subset_closedBall)
    have h2 : μ (closedBall c (2 * t) \ K) = V - A :=
      ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top hVtop hAle) hsplit
    have h3 : V * (1 - A / V) = V - A := by
      rw [ENNReal.mul_sub (fun _ _ => hVtop), mul_one, ENNReal.mul_div_cancel hV0 hVtop]
    rw [h3, ← h2]; exact h1
  -- conclude
  have hpowt : ENNReal.ofReal (t ^ (m + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos ht0 _)).ne'
  rw [ENNReal.div_le_iff_le_mul (Or.inl hpowt) (Or.inl ENNReal.ofReal_ne_top)]
  have h2t : ENNReal.ofReal ((2 * t) ^ (m + 1)) = 2 ^ (m + 1) * ENNReal.ofReal (t ^ (m + 1)) := by
    rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp
  have key : ψ (ball c t) * ω ≤ (C * 12 ^ (m + 1) * (1 - A / V) * ENNReal.ofReal (t ^ (m + 1))) * ω := by
    calc ψ (ball c t) * ω ≤ C * 6 ^ (m + 1) * μ (ball c (2 * t) \ K) := h0
      _ ≤ C * 6 ^ (m + 1) * (V * (1 - A / V)) := by gcongr
      _ = (C * 12 ^ (m + 1) * (1 - A / V) * ENNReal.ofReal (t ^ (m + 1))) * ω := by
        rw [hVball, h2t]
        have : (12 : ℝ≥0∞) ^ (m + 1) = 6 ^ (m + 1) * 2 ^ (m + 1) := by
          rw [← mul_pow]; norm_num
        rw [this]; ring
  exact (ENNReal.mul_le_mul_iff_left hω0 hωtop).1 key
```

## Key steps

1. By the Besicovitch–Lebesgue density theorem, (Lᵏ⌞K)-a.e. c lies in K and satisfies R_c(ρ) := Lᵏ(K∩B̄(c,ρ))/Lᵏ(B̄(c,ρ)) → 1 as ρ → 0⁺.
2. Lᵏ(B̄(c,ρ)∖K) = ρᵏω(1 − R_c(ρ)), since K is measurable and Lᵏ(B̄(c,ρ)) = ρᵏω ∈ (0,∞).
3. For 0 < t < r/6, vitali_bound and B ⊆ B̄ give ψ(B(c,t))/tᵏ ≤ C·12ᵏ·(1 − R_c(2t)).
4. 1 − R_c(2t) → 0 and C < ∞, so the bound tends to 0. Squeeze: ψ(B(c,t))/tᵏ → 0, hence the limsup is 0.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; cmp GMT/Ch06/Contract.lean /tmp/mickle-rado-decomp-VkNUMK/GMT/Ch06/Contract.lean (all identical)`
- `rg -n 'theorem exists_disjoint_subfamily_covering_enlargement|theorem ae_tendsto_measure_inter_div|theorem exists_mem_of_measure_ne_zero_of_ae|theorem countable_of_isOpen|theorem measure_biUnion_le|theorem addHaar_ball|theorem addHaar_closedBall|theorem exists_infDist_eq_dist|exists_isCompact_lt_add|exists_lt_isCompact|theorem LowerSemicontinuous.measurable|lowerSemicontinuous_iSup|theorem HasBasis.limsup_eq_iInf_iSup|theorem nhdsGT_basis' local-references/197bdd4b88278494/mathlib/Mathlib`
- `sed -n 50,80p and 150,215p mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean; sed -n 1080,1115p mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean; sed -n 420,432p mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n -i 'mickle|radó|rado\b' local-references/197bdd4b88278494/mathlib/Mathlib; rg -n -i 'mickle' local-references/197bdd4b88278494/project; rg -n -i 'mickle|radó' lake-packages-25730c7c/simongmt/Poincare (no Mickle–Radó result; only author-name false positives 'Herradón')`
- `rg -n 'LowerSemicontinuous|lowerSemicontinuous' lake-packages-25730c7c/simongmt/Poincare/SimonGMT; sed -n 1,420p SimonGMT/Chapter01/Densities.lean`
- `grep -n '^theorem\|^lemma\|^def\|^noncomputable def' SimonGMT/Chapter01/{InfiniteDensitySet,HausdorffDensityBounds,RadonDensity,DensityComparison,DensityCovering,LowerDensityComparison,GeneralDensity,SymmetricVitali}.lean; sed -n 15,75p and 290,420p DensityComparison.lean; sed -n 1,80p DensityCovering.lean; sed -n 15,100p HausdorffDensityBounds.lean`
- `cmp -s snapshot mathlib/Mathlib/{MeasureTheory/Covering/Vitali,MeasureTheory/Covering/Besicovitch,MeasureTheory/Measure/Restrict,MeasureTheory/Measure/Regular,MeasureTheory/Measure/Lebesgue/EqHaar,Order/LiminfLimsup,Topology/Semicontinuity/Basic}.lean against lake-packages-25730c7c/mathlib (all identical; git rev-parse HEAD = 25730c7c759d108ef87ab70af2342a196760f79d)`
- `lake env lean Scratch/Names.lean (#synth volume.InnerRegular, IsLocallyFiniteMeasure, ProperSpace, SeparableSpace, IsAddHaarMeasure on Eucl 3; #check of every cited Mathlib lemma)`
- `lake env lean Scratch/Parent.lean; Scratch/Assembly.lean (parent from four sorry'd children); Scratch/Easy.lean; Scratch/Vitali.lean; Scratch/Full.lean with #print axioms of all five declarations`
- `lake env lean GMT/Ch06/Submission.lean -o .lake/build/lib/lean/GMT/Ch06/Submission.olean -i ...ilean (scratch Submission with the five declarations inserted before main_theorem)`
- `python3 -I /tmp/mickle-rado-gen/gen.py: verifier/lean_contract.validate_lean_statement + gmt-compare.child_modules(mode=contract) for the 5 statements; lake env lean on the 10 generated NodeChallenge/NodeSolution modules (all rc=0)`
- `python3 lean_name collision scan of dag.json (257 nodes) and nodes/*/decomposition-v*.json (422 proposed names)`
- `python3 survey of nodes/*/decomposition-audit-v*.json (rejection reasons); sed -n 340,378p problem.md (helper-declaration rule at line 378)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/LeftRightNhds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityCovering.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/InfiniteDensitySet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/LowerDensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/GeneralDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/SymmetricVitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-density-comparison-a1/decomposition-v1.json`
- `/tmp/mickle-rado-decomp-VkNUMK/Scratch/Parent.lean`
- `/tmp/mickle-rado-decomp-VkNUMK/Scratch/Names.lean`
- `/tmp/mickle-rado-decomp-VkNUMK/Scratch/Assembly.lean`
- `/tmp/mickle-rado-decomp-VkNUMK/Scratch/Easy.lean`
- `/tmp/mickle-rado-decomp-VkNUMK/Scratch/Vitali.lean`
- `/tmp/mickle-rado-decomp-VkNUMK/Scratch/Full.lean`
- `/tmp/mickle-rado-decomp-VkNUMK/GMT/Ch06/Submission.lean`
- `/tmp/mickle-rado-decomp-VkNUMK/Scratch/Cmp`
- `/tmp/mickle-rado-gen/gen.py`
- `/tmp/mickle-rado-gen/children.json`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract. It is byte-identical to the workspace Contract.lean and Submission.lean and to the scratch copy.

No existing Mickle–Radó result: neither the snapshot Mathlib, the project, nor the pinned SimonGMT contains one (rg -i 'mickle|radó' finds only author-name false positives).

SimonGMT's density results do not apply to the bare outer measure ψ, which has only inner continuity on balls:
- Chapter01/Densities.lean: lowerSemicontinuous_measure_ball needs a Measure; lowerSemicontinuous_outerMeasure_inter_ball and measurable_dimensionalUpperDensity need borel ≤ caratheodory and finite closed balls; nhdsGT_zero_basis_rat is also there.
- DensityComparison.lean: simon_theorem_3_3 and simon_theorem_3_6 need IsBorelRegularOuterMeasure.
So the four child obligations are genuine.

The snapshot Mathlib supplies every ingredient the children and the assembly use:
- limsup_eq_iinf: nhdsGT_basis (LeftRightNhds.lean:80), Filter.HasBasis.limsup_eq_iInf_iSup (LiminfLimsup.lean:308), exists_nat_one_div_lt.
- sup_lsc: lt_biSup_iff, ENNReal.continuous_div_const, Continuous.comp_lowerSemicontinuous, lowerSemicontinuous_biSup.
- vitali_bound: Vitali.exists_disjoint_subfamily_covering_enlargement_ball (Vitali.lean:195), Set.PairwiseDisjoint.countable_of_isOpen, IsClosed.exists_infDist_eq_dist, IsClosed.notMem_iff_infDist_pos, Metric.disjoint_ball_infDist, measure_biUnion_le (OuterMeasure/Basic.lean:74), measure_biUnion, Measure.addHaar_ball (EqHaar.lean:456), finrank_euclideanSpace_fin.
- density_zero: Besicovitch.ae_tendsto_measure_inter_div (Besicovitch.lean:1105), Measure.addHaar_closedBall (EqHaar.lean:500), measure_sdiff_add_inter, ENNReal.Tendsto.sub and ENNReal.Tendsto.const_mul, tendsto_of_tendsto_of_tendsto_of_le_of_le'.
- parent assembly: LowerSemicontinuous.measurable (BorelSpace/Order.lean:686), Measurable.iInf, MeasurableSet.exists_lt_isCompact (Regular.lean:732, with the InnerRegular instance on volume), Measure.exists_mem_of_measure_ne_zero_of_ae (Restrict.lean:426), ENNReal.exists_nat_gt, ENNReal.exists_inv_nat_lt.
The snapshot files are byte-identical to the pinned package Mathlib used for compilation.

Compile checks in a scratch copy of the frozen project:
- All four children and the parent assembly compile; #print axioms gives [propext, Classical.choice, Quot.sound] for all five declarations.
- All 10 comparator-generated NodeChallenge/NodeSolution modules compile in the exact child scope.
- All five statements pass validate_lean_statement.

No proposed lean_name collides with the 257 DAG names or the 422 names proposed in decompositions.
