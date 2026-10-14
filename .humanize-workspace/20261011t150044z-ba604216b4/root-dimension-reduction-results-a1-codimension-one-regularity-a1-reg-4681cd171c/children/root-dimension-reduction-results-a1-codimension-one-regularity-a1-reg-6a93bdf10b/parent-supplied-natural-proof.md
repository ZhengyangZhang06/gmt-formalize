# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1.halving_step-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof, claim (★) of step 0, proved by step 1 (Localization), step 2(c) and the last line of step 6. This is the printed halving “μ(ℝ^{n+ℓ} \ ∪_{j=1}^J Q_j(graph f_j)) ≤ ½ μ(ℝ^{n+ℓ})” of Simon Ch. 3, proof of 1.6 “⇐” (chapter-03.txt lines 256–261), obtained there from (4) and (8). Departure (order of steps only): the parent's step 1 transfers the flat-tangent hypothesis to λ := μ⌞U and then applies flat_tangent_density to λ. Here flat_tangent_density has already been applied to μ in the assembly of the parent theorem; its conclusions (5) and (6), with α = ¼, are the hypothesis of this lemma, and the same localization argument transfers them from μ to λ. Dependencies: uniform_compact, compact_cover.

1. Finiteness and the trivial case. U ⊆ Ū, and Ū is compact with Ū ⊆ D, so μ(U) ≤ μ(Ū) < ∞. If μ(U) = 0, take Γ := ∅, which is closed and countably m-rectifiable (H^m(∅) = 0): μ(U \ ∅) = 0 ≤ μ(U)/2. Assume μ(U) > 0 from now on.

2. Localization. Let λ := μ⌞U, i.e. λ(A) = μ(A ∩ U); λ is a finite Borel measure, since λ(E) = μ(U) < ∞. Claim: for λ-a.e. y, (5) λ(B̄_r(y))/(ω_m r^m) → 1 and (6) λ(C(y) ∩ B̄_r(y))/r^m → 0 as r ↓ 0. Indeed λ(E \ U) = 0, and the μ-null exceptional set of the hypothesis is λ-null, so it suffices to treat y ∈ U at which the limits hold for μ. As U is open there is r_y > 0 with B_{r_y}(y) ⊆ U. For 0 < r < r_y we have B̄_r(y) ⊆ U, hence λ(B̄_r(y)) = μ(B̄_r(y)) and λ(C(y) ∩ B̄_r(y)) = μ(C(y) ∩ B̄_r(y)). So the functions of r for λ and for μ agree on (0, r_y), a neighbourhood of 0 within (0, ∞), and the limits for μ give the limits for λ.

3. Constants. Let ε := 1/(2(1 + 16^m)), so that ε > 0 and (1 + 16^m)ε = ½ < 1, and let η := μ(U)/2 ∈ (0, ∞).

4. Uniformization. By uniform_compact applied to λ, ν (Borel), ε and η, there are a compact K ⊆ E and δ > 0 with λ(E \ K) ≤ η such that for x ∈ K and ρ ∈ (0, δ): (1 − ε)⁺ ω_m ρ^m ≤ λ(B̄_ρ(x)) and λ(C(x) ∩ B̄_ρ(x)) ≤ ε ω_m ρ^m.

5. Covering. By compact_cover applied to λ, ν (|ν| ≡ 1), K, δ and ε (ε ≥ 0, (1 + 16^m)ε < 1) with the bounds of step 4, there is a closed countably m-rectifiable Γ ⊆ E with K ⊆ Γ.

6. Estimate. Since U \ Γ ⊆ U, μ(U \ Γ) = μ((U \ Γ) ∩ U) = λ(U \ Γ); and U \ Γ ⊆ E \ K because K ⊆ Γ. Hence μ(U \ Γ) = λ(U \ Γ) ≤ λ(E \ K) ≤ η = μ(U)/2. ∎

Lean note (non-normative aid). The following tactic proof of `Submission.codim1_rdo_dg_rc_halving_step` (the frozen type above, followed by `:= by`) compiles against the frozen contract: `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open`s, Lean v4.35.0-rc3, Mathlib 25730c7c; `#print axioms` gives only propext, Classical.choice, Quot.sound. Sibling lemmas used: `Submission.codim1_rdo_dg_rc_uniform_compact`, `Submission.codim1_rdo_dg_rc_compact_cover`.
```lean
  intro m D μ ν hfin hν hν1 hae U hU hUc hUD
  have hUfin : μ U ≠ ∞ := ne_top_of_le_ne_top (hfin _ hUc hUD) (measure_mono subset_closure)
  by_cases h0 : μ U = 0
  · refine ⟨∅, isClosed_empty,
      Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero (by simp), ?_⟩
    simp [h0]
  set lam := μ.restrict U with hlam
  have : IsFiniteMeasure lam := isFiniteMeasure_restrict.2 hUfin
  set ε : ℝ := 1 / (2 * (1 + 16 ^ m)) with hε
  have hεpos : 0 < ε := by positivity
  have hε1 : (1 + 16 ^ m) * ε < 1 := by
    rw [hε]
    have : (0 : ℝ) < 1 + 16 ^ m := by positivity
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith
  have haeL : ∀ᵐ y ∂lam, Tendsto (fun r : ℝ => lam (closedBall y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) ∧ Tendsto (fun r : ℝ => lam ({z | (1 / 4 : ℝ) * ‖z - y‖ ≤ |inner ℝ (z - y) (ν y)|} ∩ closedBall y r) / ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [ae_restrict_mem hU.measurableSet, ae_restrict_of_ae hae] with y hyU hy
    obtain ⟨h1, h2⟩ := hy
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU y hyU
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < r := by
      filter_upwards [Ioo_mem_nhdsGT hr] with s hs using hs.2
    constructor
    · refine h1.congr' ?_
      filter_upwards [hev] with s hs
      rw [hlam, Measure.restrict_apply' hU.measurableSet,
        inter_eq_left.2 ((closedBall_subset_ball hs).trans hrU)]
    · refine h2.congr' ?_
      filter_upwards [hev] with s hs
      rw [hlam, Measure.restrict_apply' hU.measurableSet,
        inter_eq_left.2 (inter_subset_right.trans ((closedBall_subset_ball hs).trans hrU))]
  obtain ⟨K, δ, hK, hδ, hKc, hlow, hup⟩ := Submission.codim1_rdo_dg_rc_uniform_compact m lam ν ε
    (μ U / 2) inferInstance hν hεpos (ENNReal.half_pos h0) haeL
  obtain ⟨Γ, hΓc, hΓr, hKΓ⟩ :=
    Submission.codim1_rdo_dg_rc_compact_cover m lam ν K δ ε hν1 hK hδ hεpos.le hε1 hlow hup
  refine ⟨Γ, hΓc, hΓr, ?_⟩
  calc μ (U \ Γ) = lam (U \ Γ) := by
        rw [hlam, Measure.restrict_apply' hU.measurableSet, inter_eq_left.2 sdiff_subset]
    _ ≤ lam Kᶜ := measure_mono (fun x hx hxK => hx.2 (hKΓ hxK))
    _ ≤ μ U / 2 := hKc
```

## Key steps

1. μ(U) ≤ μ(Ū) < ∞; if μ(U) = 0 take Γ = ∅.
2. λ := μ⌞U is finite and inherits the a.e. density and cone limits, because λ = μ on closed balls inside the open set U.
3. uniform_compact with ε = 1/(2(1+16^m)) and η = μ(U)/2 gives compact K and δ > 0 with λ(E \ K) ≤ μ(U)/2 and uniform bounds.
4. compact_cover gives a closed countably m-rectifiable Γ ⊇ K, and μ(U \ Γ) = λ(U \ Γ) ≤ λ(E \ K) ≤ μ(U)/2.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 scans of dag.json: selected node (depth 5, no children), sibling flat_tangent_density frozen type, collision check of the 7 codim1_rdo_dg_rc_* names, statements mentioning CountablyRectifiable or 16 ^ (cbrr_*, dpf*, codim1_rdo_*)`
- `rg -n 'theorem measurable_measure_prodMk_left|theorem LipschitzOnWith.extend_real|isClosed_range|finite_cover_balls|exists_isCompact_diff_lt|orthogonal_span_singleton|fromOrthogonalSpanSingleton|isOpen_biUnion_countable|isOpen_iUnion_countable|tendsto_measure_iUnion_atTop|Measurable.inner|instance.*InnerRegularCompactLTTop' <snapshot>/mathlib/Mathlib`
- `grep -n '^theorem|^def' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `sed -n 100,280p book/chapter-03.txt (printed proof of Simon Ch. 3, 1.6 ⇐)`
- `lake env lean -DautoImplicit=false /tmp/rc-split-check/Names.lean and Names2.lean (#check of the lemmas above inside the import closure of GMT.Ch07.Submission)`
- `lake env lean -DautoImplicit=false /tmp/rc-split-check/Types.lean, Assembly.lean, Full.lean and /tmp/rc-final/Verify.lean (7 child types, child proofs rebuilt from the returned JSON, parent assembly with a sorry stub of the uncle; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/SpecialFunctions/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-4681cd171c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/rc-split-check/Full.lean`
- `/tmp/rc-final/Verify.lean`

Pins: the snapshot manifest pins project b4d606db and Mathlib 25730c7c, and the snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f9503aa28…).

No local declaration states any of the seven children. SimonGMT Chapter03/Rectifiable.lean supplies only the definition CountablyRectifiable and the lemmas countablyRectifiable_range, _iUnion, _sUnion, _of_measure_zero and CountablyRectifiable.mono, which the children use. The related general-codimension DAG branch (cbr_rectifiable_of_approx_tangent → cbrr_cone_claim, cbrr_rectifiable_of_uniform_density) is unaccepted and has different types, so nothing is reused.

Snapshot Mathlib supplies:
- measurable_measure_prodMk_left (Prod.lean:97);
- LipschitzOnWith.extend_real (Lipschitz.lean:308);
- AntilipschitzWith.isClosed_range (Antilipschitz.lean:175);
- OrthonormalBasis.fromOrthogonalSpanSingleton (PiL2.lean:1157);
- MeasurableSet.exists_isCompact_sdiff_lt (Regular.lean:843), with an InnerRegularCompactLTTop instance for every measure on Euclid (RegularityCompacts.lean:186);
- tendsto_measure_iUnion_atTop (Continuity.lean:198);
- IsCompact.finite_cover_balls (Pseudo/Basic.lean:260);
- TopologicalSpace.isOpen_biUnion_countable.
Measurable.inner (SpecialFunctions/Inner.lean) is outside the import closure, so Continuous.measurable2 is used instead.

Lean: all 7 child types elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07 with the contract opens. Every child is proved with axioms propext, Classical.choice, Quot.sound only. The selected frozen type is proved from halving_step, of_halving and a sorry stub of the uncle Submission.codim1_rdo_dg_flat_tangent_density_cone; the only extra axiom is sorryAx, from that stub.

Names: the 7 codim1_rdo_dg_rc_* identifiers occur nowhere in dag.json (945 nodes), GMT/, SimonGMT or Mathlib.
