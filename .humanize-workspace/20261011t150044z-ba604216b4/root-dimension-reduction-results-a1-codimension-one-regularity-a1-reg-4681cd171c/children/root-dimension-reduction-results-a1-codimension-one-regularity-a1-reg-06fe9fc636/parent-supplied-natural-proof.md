# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1.halving_reduction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof, step 0 (Reduction). It makes explicit the printed iteration in Simon Ch. 3, proof of 1.6 “⇐” (chapter-03.txt lines 262–268: “Since we can now repeat the argument, starting with μ⌞(ℝ^{n+ℓ} \ ∪_j Q_j(graph f_j)) in place of μ, we thus deduce that there are countably many Lipschitz graphs … with μ(ℝ^{n+ℓ} \ ∪_j Q_j(graph f_j)) = 0”). The printed proof works with one finite measure; as in the parent's step 0, the iteration is run on each member of a countable cover of D by balls with compact closure in D. Countable m-rectifiability is SimonGMT's `CountablyRectifiable m` (Simon Ch. 3, 1.1); it holds for H^m-null sets (`countablyRectifiable_of_measure_zero`) and is preserved by countable unions (`countablyRectifiable_iUnion`, `countablyRectifiable_sUnion`).

1. Countable cover of D. For x ∈ D choose r_x > 0 with B_{r_x}(x) ⊆ D (D is open) and put W_x := B_{r_x/2}(x). Then W_x is open, x ∈ W_x, closure(W_x) ⊆ B̄_{r_x/2}(x) ⊆ B_{r_x}(x) ⊆ D, and closure(W_x) is compact, being a closed subset of the compact ball B̄_{r_x/2}(x). Since E is second countable, the family {W_x : x ∈ D} of open sets has a countable subfamily with the same union (Lindelöf; Mathlib `TopologicalSpace.isOpen_biUnion_countable`): there is a countable T ⊆ D with ⋃_{x∈T} W_x = ⋃_{x∈D} W_x = D.

2. Halving iteration on one set. Let W ⊆ E be open with closure(W) compact and closure(W) ⊆ D. Then μ(W) ≤ μ(closure W) < ∞. Claim: for every i ∈ ℕ there is a closed countably m-rectifiable Γ ⊆ E with μ(W \ Γ) ≤ 2^{-i} μ(W). Induction on i. For i = 0 take Γ := ∅: it is closed, countably m-rectifiable (H^m(∅) = 0), and μ(W \ ∅) = μ(W). Suppose Γ_i is as claimed for i and put U := W \ Γ_i. U is open (W open, Γ_i closed); closure(U) ⊆ closure(W) ⊆ D; and closure(U) is compact as a closed subset of the compact set closure(W). By (★) there is a closed countably m-rectifiable Γ′ with μ(U \ Γ′) ≤ μ(U)/2. Put Γ_{i+1} := Γ_i ∪ Γ′, which is closed and countably m-rectifiable (union of two such sets). Since W \ Γ_{i+1} = (W \ Γ_i) \ Γ′ = U \ Γ′, we get μ(W \ Γ_{i+1}) ≤ μ(U)/2 = μ(W \ Γ_i)/2 ≤ 2^{-(i+1)} μ(W).

3. Exhausting W. Choose Γ_i as in step 2 for every i ∈ ℕ and set R_W := ⋃_{i∈ℕ} Γ_i. R_W is Borel (a countable union of closed sets) and countably m-rectifiable (`countablyRectifiable_iUnion`). For every i, W \ R_W ⊆ W \ Γ_i, so μ(W \ R_W) ≤ 2^{-i} μ(W). As μ(W) < ∞, 2^{-i} μ(W) → 0 when i → ∞; hence μ(W \ R_W) = 0.

4. Gluing. For x ∈ T apply step 3 to W := W_x (open, with compact closure contained in D by step 1) and obtain R_x := R_{W_x} with μ(W_x \ R_x) = 0. Let R := ⋃_{x∈T} R_x. Since T is countable, R is Borel and countably m-rectifiable (countable union; `countablyRectifiable_sUnion` applied to the countable family {R_x : x ∈ T}). If y ∉ R, then either y ∉ D, or y ∈ D = ⋃_{x∈T} W_x and so y ∈ W_x \ R_x for some x ∈ T. Thus E \ R ⊆ (E \ D) ∪ ⋃_{x∈T} (W_x \ R_x), and by countable subadditivity μ(E \ R) ≤ μ(E \ D) + Σ_{x∈T} μ(W_x \ R_x) = 0 + 0 = 0. ∎

Lean note (non-normative aid). The following tactic proof of `Submission.codim1_rdo_dg_rc_of_halving` (the frozen type above, followed by `:= by`) compiles against the frozen contract: `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open`s, Lean v4.35.0-rc3, Mathlib 25730c7c; `#print axioms` gives only propext, Classical.choice, Quot.sound.
```lean
  intro m D μ hDo hDc hfin hhalf
  -- Steps 2–3: on an open set `W` with compact closure in `D`, iterate the halving hypothesis.
  have key : ∀ W : Set (Euclid (m + 1)), IsOpen W → IsCompact (closure W) → closure W ⊆ D →
      ∃ R' : Set (Euclid (m + 1)), MeasurableSet R' ∧ CountablyRectifiable m R' ∧
        μ (W \ R') = 0 := by
    intro W hWo hWc hWD
    have hWfin : μ W ≠ ∞ := ne_top_of_le_ne_top (hfin _ hWc hWD) (measure_mono subset_closure)
    have step : ∀ i : ℕ, ∃ Γ : Set (Euclid (m + 1)), IsClosed Γ ∧ CountablyRectifiable m Γ ∧
        μ (W \ Γ) ≤ μ W * (2⁻¹ : ℝ≥0∞) ^ i := by
      intro i
      induction i with
      | zero =>
        refine ⟨∅, isClosed_empty,
          Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty, ?_⟩
        simp
      | succ i ih =>
        obtain ⟨Γ, hΓc, hΓr, hΓμ⟩ := ih
        have hUo : IsOpen (W \ Γ) := hWo.sdiff hΓc
        have hUcl : closure (W \ Γ) ⊆ closure W := closure_mono sdiff_subset
        obtain ⟨Γ', hΓ'c, hΓ'r, hΓ'μ⟩ :=
          hhalf (W \ Γ) hUo (hWc.of_isClosed_subset isClosed_closure hUcl) (hUcl.trans hWD)
        refine ⟨Γ ∪ Γ', hΓc.union hΓ'c, ?_, ?_⟩
        · rw [← sUnion_pair]
          refine Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion
            (Set.toFinite _).countable ?_
          rintro S (rfl | rfl)
          · exact hΓr
          · exact hΓ'r
        · rw [← sdiff_sdiff]
          calc μ ((W \ Γ) \ Γ') ≤ μ (W \ Γ) / 2 := hΓ'μ
            _ = μ (W \ Γ) * 2⁻¹ := div_eq_mul_inv _ _
            _ ≤ μ W * (2⁻¹ : ℝ≥0∞) ^ i * 2⁻¹ := by gcongr
            _ = μ W * (2⁻¹ : ℝ≥0∞) ^ (i + 1) := by rw [pow_succ, mul_assoc]
    choose Γ hΓc hΓr hΓμ using step
    refine ⟨⋃ i, Γ i, MeasurableSet.iUnion (fun i => (hΓc i).measurableSet),
      Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion Γ hΓr, ?_⟩
    have hlim : Tendsto (fun i : ℕ => μ W * (2⁻¹ : ℝ≥0∞) ^ i) atTop (𝓝 0) := by
      have h1 : Tendsto (fun i : ℕ => (2⁻¹ : ℝ≥0∞) ^ i) atTop (𝓝 0) :=
        ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.one_half_lt_one
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inr hWfin)
    refine nonpos_iff_eq_zero.1 ?_
    refine ge_of_tendsto' hlim (fun i => ?_)
    exact (measure_mono (sdiff_subset_sdiff_right (subset_iUnion Γ i))).trans (hΓμ i)
  -- Step 1: a countable cover of `D` by balls with compact closure inside `D`.
  have hr : ∀ x : Euclid (m + 1), ∃ r : ℝ, 0 < r ∧ (x ∈ D → ball x r ⊆ D) := by
    intro x
    by_cases hx : x ∈ D
    · obtain ⟨r, hr0, hrD⟩ := Metric.isOpen_iff.1 hDo x hx
      exact ⟨r, hr0, fun _ => hrD⟩
    · exact ⟨1, one_pos, fun h => absurd h hx⟩
  choose r hr0 hrD using hr
  let W : Euclid (m + 1) → Set (Euclid (m + 1)) := fun x => ball x (r x / 2)
  have hWcl : ∀ x ∈ D, closure (W x) ⊆ D := fun x hx =>
    closure_ball_subset_closedBall.trans
      ((closedBall_subset_ball (half_lt_self (hr0 x))).trans (hrD x hx))
  have hWcpt : ∀ x, IsCompact (closure (W x)) := fun x =>
    (isCompact_closedBall x (r x / 2)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  have hR : ∀ x : Euclid (m + 1), ∃ R' : Set (Euclid (m + 1)), MeasurableSet R' ∧
      CountablyRectifiable m R' ∧ (x ∈ D → μ (W x \ R') = 0) := by
    intro x
    by_cases hx : x ∈ D
    · obtain ⟨R', h1, h2, h3⟩ := key (W x) isOpen_ball (hWcpt x) (hWcl x hx)
      exact ⟨R', h1, h2, fun _ => h3⟩
    · exact ⟨∅, MeasurableSet.empty,
        Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty,
        fun h => absurd h hx⟩
  choose Rx hRxm hRxr hRxμ using hR
  obtain ⟨T, hTD, hTc, hTU⟩ :=
    TopologicalSpace.isOpen_biUnion_countable D W (fun x _ => isOpen_ball)
  have hDcov : D ⊆ ⋃ x ∈ T, W x := by
    rw [hTU]
    intro y hy
    exact mem_biUnion hy (mem_ball_self (half_pos (hr0 y)))
  -- Step 4: glue.
  refine ⟨⋃ x ∈ T, Rx x, MeasurableSet.biUnion hTc (fun x _ => hRxm x), ?_, ?_⟩
  · rw [← sUnion_image]
    exact Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion (hTc.image Rx)
      (by rintro S ⟨x, -, rfl⟩; exact hRxr x)
  · have hsub : (⋃ x ∈ T, Rx x)ᶜ ⊆ Dᶜ ∪ ⋃ x ∈ T, (W x \ Rx x) := by
      intro y hy
      by_cases hyD : y ∈ D
      · right
        obtain ⟨x, hxT, hyW⟩ := mem_iUnion₂.1 (hDcov hyD)
        exact mem_iUnion₂.2 ⟨x, hxT, hyW, fun hyR => hy (mem_iUnion₂.2 ⟨x, hxT, hyR⟩)⟩
      · exact Or.inl hyD
    refine measure_mono_null hsub (measure_union_null hDc ?_)
    exact (measure_biUnion_null_iff hTc).2 (fun x hx => hRxμ x (hTD hx))
```

## Key steps

1. Cover D by countably many open balls W_x (x ∈ T) whose closures are compact subsets of D (Lindelöf).
2. For such W, induction applying (★) to W \ Γ_i gives closed countably m-rectifiable Γ_i with μ(W \ Γ_i) ≤ 2^{-i} μ(W).
3. R_W := ⋃_i Γ_i is Borel and countably m-rectifiable with μ(W \ R_W) = 0, because μ(W) < ∞.
4. R := ⋃_{x∈T} R_{W_x} is Borel and countably m-rectifiable, and μ(E \ R) ≤ μ(E \ D) + Σ_x μ(W_x \ R_{W_x}) = 0.

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
