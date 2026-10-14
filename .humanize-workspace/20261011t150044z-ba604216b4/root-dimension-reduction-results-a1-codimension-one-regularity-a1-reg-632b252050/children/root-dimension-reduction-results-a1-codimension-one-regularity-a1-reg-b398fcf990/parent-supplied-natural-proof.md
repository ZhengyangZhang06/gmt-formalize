# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1.tangential_vanish-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 5(a) ('|∫_{F_r} Dζ(w)| ≤ ‖ζ‖_∞|w|C₁R^m(2ε(rR))^{1/2} → 0'); printed (8) together with (2) of Simon Ch. 3, 4.3.
1. Choice of R and M. tsupport ζ is compact, hence bounded: choose R > 0 with tsupport ζ ⊆ B_R(0). ζ is continuous with compact support, so M := sup_x |ζ(x)| < ∞.
2. Normal concentration. μ(B̄_{ρ₁/2}(y)) ≤ C₁(ρ₁/2)^m < ∞, so the sibling theorem normal_defect_small applies to μ, ν, y, v (ν Borel, |ν| = 1, |v| = 1, A(ρ) → v) with ρ₀ := ρ₁/2. Fix η > 0 and put δ := η/(1 + M|w|C₁R^m) > 0. By its part (ii) there is ρ' > 0 such that ∫_{B̄_ρ(y)} |⟨ν(z), w⟩| dμ(z) ≤ δ|w|·μ(B̄_ρ(y))_ℝ for all 0 < ρ < ρ'.
3. Rescaled identity. Let 0 < r < r₀ := min{ρ₁, ρ'}/R and put ρ := rR, so 0 < ρ < min{ρ₁, ρ'} and B̄_ρ(y) ⊆ B̄_{ρ₁}(y) ⊆ D. The sibling theorem directional_gauss_green (with these m, D, F, μ, ν, y, r, R, ζ, w; F Borel, (GG), r > 0) gives ∫_{F_{y,r}} Dζ(z)(w) dL(z) = −(r^m)^{-1} ∫ k dμ, with k(z) := ζ(r^{-1}(z − y))·⟨w, ν(z)⟩.
4. Estimate of ∫ k dμ. If k(z) ≠ 0 then r^{-1}(z − y) ∈ support ζ ⊆ B_R(0), so z ∈ B̄_ρ(y); and |k(z)| ≤ M·|⟨ν(z), w⟩|. Hence |k| ≤ M|⟨ν, w⟩|·1_{B̄_ρ(y)}, and the right side is μ-integrable (bounded, Borel, μ(B̄_ρ(y)) ≤ C₁ρ^m < ∞); k is Borel (ζ continuous, ν Borel). Therefore |∫ k dμ| ≤ ∫ |k| dμ ≤ M ∫_{B̄_ρ(y)} |⟨ν, w⟩| dμ ≤ Mδ|w|·μ(B̄_ρ(y))_ℝ ≤ Mδ|w|C₁ρ^m = Mδ|w|C₁R^m·r^m, using step 2 (ρ < ρ') and μ(B̄_ρ(y)) ≤ C₁ρ^m (0 < ρ < ρ₁).
5. Conclusion. For 0 < r < r₀, |∫_{F_{y,r}} Dζ(z)(w) dL(z)| = (r^m)^{-1}|∫ k dμ| ≤ δ·M|w|C₁R^m = η·M|w|C₁R^m/(1 + M|w|C₁R^m) < η. Since η > 0 was arbitrary, ∫_{F_{y,r}} Dζ(z)(w) dL(z) → 0 as r ↓ 0. ∎
Formalization pointers (verified): hζc.isCompact.isBounded.subset_ball 0, then R := max R₀ 1; hζ.continuous.bounded_above_of_compact_support hζc; finiteness at ρ₁/2 from the density bound (half_pos, half_lt_self, ENNReal.ofReal_ne_top). The map r ↦ rR sends 𝓝[>]0 to 𝓝[>]0 (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within), and Tendsto.eventually transports the eventual bound of normal_defect_small. Also used: Metric.tendsto_nhds, dist_zero_right, setIntegral_eq_integral_of_forall_compl_eq_zero, and norm_integral_le_of_norm_le with the integrable bound M·|⟨ν, w⟩| on μ⌞B̄_ρ(y) (Integrable.of_bound, Integrable.const_mul). The final estimate uses integral_const_mul, norm_mul, norm_neg, norm_inv, field_simp and div_lt_iff₀.

Appendix (an optional aid; the numbered argument above is the proof). The Lean 4 script below proves exactly the frozen statement. It compiled against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, project b4d606db) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open Filter Function Set MeasureTheory Metric` and `open scoped ENNReal Topology`. Compiled together with the other eight child proofs, `#print axioms` reported only propext, Classical.choice and Quot.sound. The exact compiled source of all nine children, plus the parent assembly, is saved at .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-632b252050/bh-split-v2-lean-prototype.lean.txt. It uses the sibling declarations Submission.codim1_rdo_dg_bh_directional_gauss_green and Submission.codim1_rdo_dg_bh_normal_defect_small at their frozen types.
```lean
theorem Submission.codim1_rdo_dg_bh_tangential_vanish : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)) (ρ₁ C₁ : ℝ), MeasurableSet F → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → ‖v‖ = 1 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → 0 < ρ₁ → 0 ≤ C₁ → closedBall y ρ₁ ⊆ D → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C₁ * ρ ^ m)) → ∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∀ w : Euclid (m + 1), inner ℝ w v = 0 → Tendsto (fun r : ℝ => ∫ z in (fun z => y + r • z) ⁻¹' F, fderiv ℝ ζ z w) (𝓝[>] 0) (𝓝 0) := by
  intro m D F μ ν y v ρ₁ C₁ hF hν hν1 hGG hv hA hρ₁ hC₁ hball hmass ζ hζ hζc w hw
  obtain ⟨R₀, hR₀⟩ := hζc.isCompact.isBounded.subset_ball (0 : Euclid (m + 1))
  set R := max R₀ 1 with hR_def
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR : tsupport ζ ⊆ ball (0 : Euclid (m + 1)) R :=
    hR₀.trans (ball_subset_ball (le_max_left _ _))
  obtain ⟨M, hM⟩ : ∃ M, ∀ z, ‖ζ z‖ ≤ M := hζ.continuous.bounded_above_of_compact_support hζc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hM' : ∀ z, |ζ z| ≤ M := fun z => by simpa [Real.norm_eq_abs] using hM z
  have hfin : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ μ (closedBall y ρ₀) ≠ ∞ :=
    ⟨ρ₁ / 2, half_pos hρ₁, ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hmass _ (half_pos hρ₁) (half_lt_self hρ₁))⟩
  have htend : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun r : ℝ => r * R) (𝓝 0) (𝓝 (0 * R)) := tendsto_id.mul_const R
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hRpos
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r * R < ρ₁ :=
    (htend.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hρ₁)
  set K := M * ‖w‖ * C₁ * R ^ m with hK
  have hK0 : 0 ≤ K := by positivity
  rw [Metric.tendsto_nhds]
  intro η hη
  set δ := η / (1 + K) with hδ_def
  have hδ : 0 < δ := div_pos hη (by linarith)
  have hnd := htend.eventually
    (Submission.codim1_rdo_dg_bh_normal_defect_small m μ ν y v hν hν1 hv hfin hA δ hδ)
  filter_upwards [hnd, hsmall, self_mem_nhdsWithin] with r h1 h2 h3
  have hr : 0 < r := h3
  have hrR : 0 < r * R := mul_pos hr hRpos
  have hsub : closedBall y (r * R) ⊆ D := (closedBall_subset_closedBall h2.le).trans hball
  have hBfin : μ (closedBall y (r * R)) ≤ ENNReal.ofReal (C₁ * (r * R) ^ m) := hmass _ hrR h2
  have hBlt : μ (closedBall y (r * R)) < ∞ := hBfin.trans_lt ENNReal.ofReal_lt_top
  have : IsFiniteMeasure (μ.restrict (closedBall y (r * R))) :=
    isFiniteMeasure_restrict.mpr hBlt.ne
  have hμB : (μ (closedBall y (r * R))).toReal ≤ C₁ * (r * R) ^ m :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hBfin
  have hζz : ∀ z, z ∉ closedBall y (r * R) → ζ (r⁻¹ • (z - y)) = 0 := by
    intro z hz
    by_contra hne
    apply hz
    have hmem : r⁻¹ • (z - y) ∈ ball (0 : Euclid (m + 1)) R := hR (subset_tsupport _ hne)
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at hmem
    rw [mem_closedBall, dist_eq_norm]
    have := (inv_mul_lt_iff₀ hr).mp hmem
    linarith
  have hζmeas : Measurable (fun z : Euclid (m + 1) => ζ (r⁻¹ • (z - y))) :=
    (hζ.continuous.comp ((continuous_id.sub continuous_const).const_smul r⁻¹)).measurable
  have hrm : 0 < r ^ m := pow_pos hr m
  rw [dist_zero_right, Submission.codim1_rdo_dg_bh_directional_gauss_green m D F μ ν y r R hF hGG hr
    hsub ζ hζ hζc hR w]
  have hzero : ∀ z, z ∉ closedBall y (r * R) → ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) = 0 := by
    intro z hz
    rw [hζz z hz, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hνw : Measurable (fun z => |inner ℝ (ν z) w|) :=
    (continuous_abs.comp (continuous_id.inner continuous_const)).measurable.comp hν
  have hint2 : Integrable (fun z => M * |inner ℝ (ν z) w|) (μ.restrict (closedBall y (r * R))) := by
    refine (Integrable.of_bound hνw.aestronglyMeasurable ‖w‖ (Eventually.of_forall fun z => ?_)).const_mul M
    rw [Real.norm_eq_abs, abs_abs]
    calc |inner ℝ (ν z) w| ≤ ‖ν z‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ = ‖w‖ := by rw [hν1, one_mul]
  have hb1 : ‖∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) ∂μ‖ ≤
      ∫ z in closedBall y (r * R), M * |inner ℝ (ν z) w| ∂μ := by
    apply norm_integral_le_of_norm_le hint2
    refine Eventually.of_forall fun z => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, real_inner_comm]
    exact mul_le_mul_of_nonneg_right (hM' _) (abs_nonneg _)
  have hb2 : ∫ z in closedBall y (r * R), M * |inner ℝ (ν z) w| ∂μ ≤
      M * (δ * ‖w‖ * (C₁ * (r * R) ^ m)) := by
    rw [integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ hM0
    calc ∫ z in closedBall y (r * R), |inner ℝ (ν z) w| ∂μ
        ≤ δ * ‖w‖ * (μ (closedBall y (r * R))).toReal := h1.2 w hw
      _ ≤ δ * ‖w‖ * (C₁ * (r * R) ^ m) := by gcongr
  have hnorm : ‖-(r ^ m)⁻¹ * ∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) ∂μ‖ =
      (r ^ m)⁻¹ * ‖∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) ∂μ‖ := by
    rw [norm_mul, norm_neg, norm_inv, Real.norm_eq_abs (r ^ m), abs_of_pos hrm]
  rw [hnorm]
  calc (r ^ m)⁻¹ * ‖∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) ∂μ‖
      ≤ (r ^ m)⁻¹ * (M * (δ * ‖w‖ * (C₁ * (r * R) ^ m))) := by
        gcongr
        exact hb1.trans hb2
    _ = δ * K := by rw [hK, mul_pow]; field_simp
    _ < η := by
        rw [hδ_def, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith
```

## Key steps

1. Choose R > 0 with tsupport ζ ⊆ B_R(0) and M := sup|ζ|.
2. normal_defect_small (ii) (finite mass from the density bound at ρ₁/2) gives ∫_{B̄_ρ}|⟨ν, w⟩| ≤ δ|w|μ(B̄_ρ) for small ρ.
3. directional_gauss_green at scale r with ρ = rR: ∫_{F_{y,r}} Dζ(w) = −r^{-m}∫ζ((z−y)/r)⟨w, ν⟩dμ.
4. Bound by r^{-m}·Mδ|w|C₁(rR)^m = δM|w|C₁R^m.
5. δ arbitrary ⇒ the integrals tend to 0.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD`
- `sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 over dag.json: selected node record (status, message, attempts, children); frozen lean_statement of cutoff_estimates-a1, volume_density_lower-a1, bv_compactness-a1 and halfspace_rigidity-a1; name-collision and identical-type scan of the nine codim1_rdo_dg_bh_* children (1010 nodes, re-run at 1119 nodes)`
- `grep -l '"child_id": "...blowup_halfspace-a1.' nodes/*/parent-child-handoff.json; grep -rl codim1_rdo_dg_bh_ nodes/ .humanize/publication-intents .humanize/issue-claims (no match outside decomposition-v1.json)`
- `sed -n runtime.py: _solve loop (960-1060), _decompose (1388-1560), _parent_supplied_child_checkpoint (1741-1799), _solve_children (1801-1990), _existing_lean_name_problem (6532-6575); cat swarm-project.json; cat run.json`
- `rg -n 'blowUp|blowup|symmDiff|GaussGreen|gaussGreen|reducedBoundary|rescal|L1loc|halfspace' <snapshot>/project/GMT/Ch07; rg -n 'DeGiorgi|reducedBoundary|symmDiff|blow' <snapshot>/project/GMT/Ch03/Contract.lean; rg -ln 'blowUp|blowUpMap|reducedBoundary|GaussGreen|gaussGreen|symmDiff' simongmt/Poincare; rg -n '^theorem|^lemma|^def|^structure' simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `rg -n in <snapshot>/mathlib: tendsto_of_subseq_tendsto | integral_comp_smul | addHaar_preimage_smul | trace_smulRight | fderiv_smul_const | symmDiff_triangle | norm_setIntegral_le_of_norm_le_const | setIntegral_eq_integral_of_forall_compl_eq_zero | norm_integral_le_of_norm_le | integral_mul_left_eq_self | mulTSupport_comp_subset_preimage | HasCompactMulSupport.comp_homeomorph | HasCompactSupport.fderiv_apply | ContDiff.continuous_fderiv | ENNReal.tendsto_nhds | Integrable.of_bound | integral_inner | integral_indicator_const | isFiniteMeasure_restrict | measure_preimage_mul | toReal_le_of_le_ofReal | integrableOn_const`
- `sed -n 560,760p book/chapter-03.txt (Simon Ch. 3, 4.3 printed proof)`
- `git show <last 200 commits>:GMT/Ch07/Submission.lean | grep ^import (import practice of candidate submissions); sed -n 1,28p verifier/gmt-compare.py`
- `lake env lean -DautoImplicit=false /tmp/bh-split-v2/{Types,Assembly,Checks,Rescaled,NormalDefect,L1loc,FirstVariation,Full,SavedCopy}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/SymmDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/run.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-632b252050/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-632b252050/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-632b252050/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-632b252050/bh-split-v2-lean-prototype.lean.txt`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/bh-split-v2/Types.lean`
- `/tmp/bh-split-v2/Assembly.lean`
- `/tmp/bh-split-v2/Checks.lean`
- `/tmp/bh-split-v2/Rescaled.lean`
- `/tmp/bh-split-v2/NormalDefect.lean`
- `/tmp/bh-split-v2/L1loc.lean`
- `/tmp/bh-split-v2/FirstVariation.lean`
- `/tmp/bh-split-v2/Full.lean`

Pins: the snapshot manifest (project b4d606db, Mathlib 25730c7c) equals workspace HEAD and .lake/packages/mathlib. Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Reuse: nothing in the snapshot is reusable. The project's only blow-up is the current-level GMT.Ch07.blowUp (Contract.lean:184). The snapshot's GMT/Ch03 has a DeGiorgiTheorem Prop (Contract.lean:325), but its main_theorem is `by sorry` (:339). SimonGMT Chapter03/FinitePerimeter.lean supplies only the reducedBoundary data. No local declaration states the rescaled Gauss–Green identity, the normal-defect estimate, the blow-up perimeter bound, the L¹_loc transfer or the offset lemma, so all become children.

API: snapshot Mathlib supplies everything the child proofs use: CountablyGenerated.lean:125, Haar/NormedSpace.lean:92, Lebesgue/EqHaar.lean:352, LinearAlgebra/Trace.lean:272, FDeriv/Mul.lean:153, FDeriv/Const.lean:393, ContDiff/Defs.lean:1271, Order/SymmDiff.lean:210, Bochner/Set.lean:486/528/613, Bochner/Basic.lean:985, Group/Integral.lean:91, Group/Measure.lean:236, Topology/Algebra/Support.lean:99/562, ENNReal/Lemmas.lean:233, IntegrableOn.lean:119/171, Typeclasses/Finite.lean:40, Basic/ENNReal/Real.lean:283. One exception: integral_inner (Function/L2Space.lean:89) is outside the frozen header's import closure, so normal_defect's pointer uses innerSL ℝ v with integral_comp_comm. Recent candidate commits do add Mathlib imports, so importing it is also an option.

Lean checks (from the workspace root):
- All 13 types elaborate.
- The parent's frozen type is proved from the 9 children and the 4 sibling contracts.
- All 9 children are proved with only propext, Classical.choice, Quot.sound.
- The saved prototype recompiles identically.

DAG and runtime: v1 (identical contract) was accepted at 11:14Z, but its children were never activated before the 11:42Z restart. The node has no children, and there are no leftover handoffs or publication intents. The nine names are unused across the 1119 nodes, and no identical type exists. Config: max_depth 6, max_children 12.
