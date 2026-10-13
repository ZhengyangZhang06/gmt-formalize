# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1.continuous_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Extracted from step 5 of the supplied parent proof (Simon Ch. 3, 4.3 (†)): 'For 0 < r < ρ₁/(R+1): |r^{-m} ∫ (f − f_θ)((z − y)/r) dμ| ≤ θ r^{-m} μ(B̄_{r(R+1)}(y)) ≤ θ C₁ (R+1)^m, and |∫_{P_v} (f − f_θ) dH^m| ≤ θ H^m(P_v ∩ B_{R+1}(0)) … limsup ≤ θ (C₁ + ω_m)(R+1)^m; let θ ↓ 0.' Here the limit measure is an arbitrary τ that is finite on balls. Dependency: smooth_approx. Notation: B̄_ρ(x) closed balls.

1. Choose R ≥ 0 with tsupport f ⊆ B̄_R(0); put S := R + 1 > 0, T := τ(B̄_S(0))_ℝ (finite by hypothesis) and K := C S^n + T + 1 > 0.
2. μ-estimate. Let φ be continuous with |φ| ≤ c and φ = 0 outside B̄_S(0), and let 0 < r with rS < ρ₁. If φ(r^{-1}(z − y)) ≠ 0 then |z − y| ≤ rS, so z ↦ φ(r^{-1}(z − y)) vanishes outside B := B̄_{rS}(y); μ(B) ≤ C (rS)^n < ∞. Hence this function is μ-integrable (continuous, bounded, supported in a set of finite measure) and |r^{-n} ∫ φ(r^{-1}(z − y)) dμ| ≤ r^{-n} c μ(B)_ℝ ≤ r^{-n} c C (rS)^n = c C S^n.
3. τ-estimate. For φ as in step 2, φ is τ-integrable (continuous, bounded, vanishing outside B̄_S(0), which has finite τ-measure) and |∫ φ dτ| ≤ c T.
4. Approximation. Let ε > 0 and θ := ε/(4K) > 0. By smooth_approx (with R and θ) there is g of class C¹ with compact support, tsupport g ⊆ B̄_{R+1}(0) = B̄_S(0) and |f − g| ≤ θ everywhere. Then f and g are continuous, bounded and vanish outside B̄_S(0), and f − g is continuous, bounded by θ and vanishes outside B̄_S(0).
5. By hypothesis applied to g, there is r₀ > 0 such that |r^{-n} ∫ g(r^{-1}(z − y)) dμ − ∫ g dτ| < ε/2 for 0 < r < r₀; shrinking r₀ we may also assume r₀ ≤ ρ₁/S.
6. For 0 < r < r₀: by step 2 for f and for g, both rescaled integrals are finite integrals of integrable functions, so r^{-n} ∫ f(r^{-1}(z − y)) dμ − r^{-n} ∫ g(r^{-1}(z − y)) dμ = r^{-n} ∫ (f − g)(r^{-1}(z − y)) dμ, whose absolute value is at most θ C S^n (step 2 with φ = f − g, c = θ). By step 3, ∫ f dτ − ∫ g dτ = ∫ (f − g) dτ has absolute value at most θ T.
7. By the triangle inequality, for 0 < r < r₀: |r^{-n} ∫ f(r^{-1}(z − y)) dμ − ∫ f dτ| ≤ θ C S^n + |r^{-n} ∫ g(r^{-1}(z − y)) dμ − ∫ g dτ| + θ T < θ K + ε/2 = ε/4 + ε/2 < ε. As ε > 0 was arbitrary, r^{-n} ∫ f(r^{-1}(z − y)) dμ → ∫ f dτ as r ↓ 0. ∎

Appendix (formal check; the numbered proof above is the argument). The Lean proof below of exactly this frozen statement was compiled in the pinned project (Lean v4.35.0-rc3, Mathlib 25730c7c) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`), as part of one file containing all ten children; it refers only to the sibling theorem(s) `Submission.codim1_rdo_dg_tma_smooth_approx` with their frozen types, and `#print axioms` reports propext, Classical.choice, Quot.sound.

theorem Submission.codim1_rdo_dg_tma_continuous_extension : ∀ (P n : ℕ) (μ τ : Measure (Euclid P)) (y : Euclid P) (ρ₁ C : ℝ), 0 < ρ₁ → 0 ≤ C → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ R : ℝ, τ (closedBall (0 : Euclid P) R) ≠ ∞) → (∀ g : Euclid P → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z, g z ∂τ))) → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z, f z ∂τ)) := by
  intro P n μ τ y ρ₁ C hρ₁ hC hdens hτ hsmooth f hf hfc
  obtain ⟨R₀, hR₀⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  set R := max R₀ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : tsupport f ⊆ closedBall 0 R :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  set S := R + 1 with hSdef
  have hS : 0 < S := by positivity
  -- uniform local estimate for the rescaled μ-integrals
  have key : ∀ (φ : Euclid P → ℝ) (c r : ℝ), Continuous φ → (∀ w, |φ w| ≤ c) →
      (∀ w, φ w ≠ 0 → w ∈ closedBall (0 : Euclid P) S) → 0 < r → r * S < ρ₁ →
      Integrable (fun z => φ (r⁻¹ • (z - y))) μ ∧
        |(r ^ n)⁻¹ * ∫ z, φ (r⁻¹ • (z - y)) ∂μ| ≤ c * (C * S ^ n) := by
    intro φ c r hφ hφc hφs hr hrS
    set B := closedBall y (r * S) with hBdef
    have hBfin : μ B ≠ ∞ :=
      ((hdens (r * S) (by positivity) hrS).trans_lt ENNReal.ofReal_lt_top).ne
    have hsupp : ∀ z, z ∉ B → φ (r⁻¹ • (z - y)) = 0 := by
      intro z hz
      by_contra hne
      have h1 := hφs _ hne
      apply hz
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        at h1
      rw [hBdef, mem_closedBall, dist_eq_norm]
      calc ‖z - y‖ = r * (r⁻¹ * ‖z - y‖) := by field_simp
        _ ≤ r * S := mul_le_mul_of_nonneg_left h1 hr.le
    have hcont : Continuous (fun z => φ (r⁻¹ • (z - y))) := by fun_prop
    have hint : Integrable (fun z => φ (r⁻¹ • (z - y))) μ := by
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hsupp
      exact Measure.integrableOn_of_bounded hBfin hcont.aestronglyMeasurable (M := c)
        (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hφc _)
    refine ⟨hint, ?_⟩
    have hc0 : 0 ≤ c := (abs_nonneg _).trans (hφc 0)
    have hle : |∫ z, φ (r⁻¹ • (z - y)) ∂μ| ≤ c * (μ B).toReal := by
      have h2 : ‖∫ z, φ (r⁻¹ • (z - y)) ∂μ‖ ≤ ∫ z, B.indicator (fun _ => c) z ∂μ := by
        refine norm_integral_le_of_norm_le
          ((integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hBfin))
          (Eventually.of_forall fun z => ?_)
        by_cases hz : z ∈ B
        · rw [indicator_of_mem hz]
          simpa [Real.norm_eq_abs] using hφc _
        · rw [indicator_of_notMem hz, hsupp z hz, norm_zero]
      rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, Measure.real] at h2
      simpa [Real.norm_eq_abs, mul_comm] using h2
    have hμ : (μ B).toReal ≤ C * (r * S) ^ n :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hdens _ (by positivity) hrS)
    rw [abs_mul, abs_of_pos (inv_pos.2 (pow_pos hr n))]
    calc (r ^ n)⁻¹ * |∫ z, φ (r⁻¹ • (z - y)) ∂μ|
        ≤ (r ^ n)⁻¹ * (c * (C * (r * S) ^ n)) := by
          gcongr
          exact hle.trans (mul_le_mul_of_nonneg_left hμ hc0)
      _ = c * (C * S ^ n) := by
          rw [mul_pow]
          field_simp
  -- estimate for τ-integrals
  set T := (τ (closedBall (0 : Euclid P) S)).toReal with hTdef
  have keyτ : ∀ (φ : Euclid P → ℝ) (c : ℝ), Continuous φ → (∀ w, |φ w| ≤ c) →
      (∀ w, φ w ≠ 0 → w ∈ closedBall (0 : Euclid P) S) →
      Integrable φ τ ∧ |∫ z, φ z ∂τ| ≤ c * T := by
    intro φ c hφ hφc hφs
    have hBfin := hτ S
    have hsupp : ∀ z, z ∉ closedBall (0 : Euclid P) S → φ z = 0 := by
      intro z hz
      by_contra hne
      exact hz (hφs z hne)
    have hint : Integrable φ τ := by
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hsupp
      exact Measure.integrableOn_of_bounded hBfin hφ.aestronglyMeasurable (M := c)
        (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hφc _)
    refine ⟨hint, ?_⟩
    have h2 : ‖∫ z, φ z ∂τ‖ ≤ ∫ z, (closedBall (0 : Euclid P) S).indicator (fun _ => c) z ∂τ := by
      refine norm_integral_le_of_norm_le
        ((integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hBfin))
        (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ closedBall (0 : Euclid P) S
      · rw [indicator_of_mem hz]
        simpa [Real.norm_eq_abs] using hφc _
      · rw [indicator_of_notMem hz, hsupp z hz, norm_zero]
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, Measure.real] at h2
    simpa [Real.norm_eq_abs, mul_comm, hTdef] using h2
  -- support of f
  have hfs : ∀ w, f w ≠ 0 → w ∈ closedBall (0 : Euclid P) S := by
    intro w hw
    have := hR (subset_tsupport f hw)
    exact closedBall_subset_closedBall (by linarith) this
  obtain ⟨Mf, hMf⟩ := hf.bounded_above_of_compact_support hfc
  have hMf' : ∀ w, |f w| ≤ Mf := fun w => by simpa [Real.norm_eq_abs] using hMf w
  set K := C * S ^ n + T + 1 with hKdef
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  have hK : 0 < K := by positivity
  rw [Metric.tendsto_nhds]
  intro ε hε
  set θ := ε / (4 * K) with hθdef
  have hθ : 0 < θ := by positivity
  obtain ⟨g, hg, hgc, hgs, hfg⟩ :=
    Submission.codim1_rdo_dg_tma_smooth_approx P f R θ hf hR hθ
  have hgs' : ∀ w, g w ≠ 0 → w ∈ closedBall (0 : Euclid P) S := fun w hw =>
    hgs (subset_tsupport g hw)
  obtain ⟨Mg, hMg⟩ := hg.continuous.bounded_above_of_compact_support hgc
  have hMg' : ∀ w, |g w| ≤ Mg := fun w => by simpa [Real.norm_eq_abs] using hMg w
  have hlim := Metric.tendsto_nhds.1 (hsmooth g hg hgc) (ε / 2) (by positivity)
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ρ₁ / S :=
    nhdsWithin_le_nhds (gt_mem_nhds (div_pos hρ₁ hS))
  filter_upwards [hlim, self_mem_nhdsWithin, hsmall] with r hr1 hr hrS
  have hrS' : r * S < ρ₁ := by
    have := (lt_div_iff₀ hS).mp hrS
    linarith
  have hdiff_s : ∀ w, (f - g) w ≠ 0 → w ∈ closedBall (0 : Euclid P) S := by
    intro w hw
    by_cases hfw : f w = 0
    · have : g w ≠ 0 := by
        intro hgw
        apply hw
        simp [hfw, hgw]
      exact hgs' w this
    · exact hfs w hfw
  have hd : ∀ w, |(f - g) w| ≤ θ := fun w => by simpa using hfg w
  obtain ⟨hint_f, -⟩ := key f Mf r hf hMf' hfs hr hrS'
  obtain ⟨hint_g, -⟩ := key g Mg r hg.continuous hMg' hgs' hr hrS'
  obtain ⟨-, hest⟩ := key (f - g) θ r (hf.sub hg.continuous) hd hdiff_s hr hrS'
  obtain ⟨hτf, -⟩ := keyτ f Mf hf hMf' hfs
  obtain ⟨hτg, -⟩ := keyτ g Mg hg.continuous hMg' hgs'
  obtain ⟨-, hestτ⟩ := keyτ (f - g) θ (hf.sub hg.continuous) hd hdiff_s
  have e1 : (r ^ n)⁻¹ * ∫ z, (f - g) (r⁻¹ • (z - y)) ∂μ =
      (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ - (r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ := by
    rw [← mul_sub, ← integral_sub hint_f hint_g]
    rfl
  have e2 : ∫ z, (f - g) z ∂τ = ∫ z, f z ∂τ - ∫ z, g z ∂τ := by
    rw [← integral_sub hτf hτg]
    rfl
  rw [e1] at hest
  rw [e2] at hestτ
  rw [Real.dist_eq] at hr1 ⊢
  have hθK : θ * (C * S ^ n) + θ * T ≤ ε / 2 := by
    have h1 : θ * (C * S ^ n) + θ * T ≤ θ * K := by
      rw [hKdef]
      nlinarith
    have h2 : θ * K = ε / 4 := by
      rw [hθdef]
      field_simp
    linarith
  calc |(r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ - ∫ z, f z ∂τ|
      = |((r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ - (r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ)
          + ((r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ - ∫ z, g z ∂τ)
          - (∫ z, f z ∂τ - ∫ z, g z ∂τ)| := by ring_nf
    _ ≤ |(r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ - (r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ|
          + |(r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ - ∫ z, g z ∂τ|
          + |∫ z, f z ∂τ - ∫ z, g z ∂τ| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ < θ * (C * S ^ n) + ε / 2 + θ * T := by
        have := hr1
        linarith
    _ ≤ ε := by linarith

## Key steps

1. Uniform bounds: |r^{-n}∫φ(r^{-1}(z − y))dμ| ≤ sup|φ| C S^n and |∫φ dτ| ≤ sup|φ| τ(B̄_S(0)) for φ supported in B̄_S(0), rS < ρ₁.
2. smooth_approx: g ∈ C¹_c with tsupport g ⊆ B̄_{R+1}(0) and |f − g| ≤ θ.
3. Convergence for g plus the two θ-bounds for f − g.
4. ε/3-type estimate and θ ↓ 0 give convergence for f.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; git -C /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07 rev-parse HEAD; git -C /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib rev-parse HEAD`
- `python3 scans of dag.json: frozen lean_statement of the selected node and of siblings normal_average_ae-a1, cutoff_estimates-a1, blowup_halfspace-a1; accepted nodes grepped for μHE[, ᗮ, LinearMap.trace, symmDiff, Ioi and smooth-approximation statements; collision check of the 10 names codim1_rdo_dg_tma_* (0 hits among 993 nodes)`
- `grep -rn codim1_rdo_dg_tma GMT/ and lake-packages-25730c7c/simongmt (no match)`
- `sed -n 1,420p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE API)`
- `rg in snapshot mathlib: trace_eq_sum_inner, integral_Ioi_of_hasDerivAt_of_tendsto, HasCompactSupport.integral_Ioi_deriv_eq, hasDerivAt_integral_of_dominated_loc_of_deriv_le, measurePreserving_repr_symm, LinearIsometryEquiv.measurePreserving, setIntegral_comp_smul_of_pos, integral_comp_smul, integral_mul_right_eq_self, volume_preserving_piFinSuccAbove, snocEquiv, OrthonormalBasis.sum_repr_symm, integral_prod, support_fderiv_subset, contDiff_convolution_left, support_convolution_subset, exists_contDiff_tsupport_subset, finrank_orthogonal_span_singleton, basisOfOrthonormalOfCardEqFinrank, integral_inner, dist_normed_convolution_le, Submodule.measurePreserving_measurableEquivProd`
- `#check probes after import GMT.Ch07.Submission (/tmp/tma-split-check/Probe*.lean): ContDiffBump.normed, ContDiffBump.dist_normed_convolution_le, integral_inner and EuclideanSpace.volume_preserving_measurableEquiv are unknown constants in the contract's import closure; (volume : Measure (Euclid m × ℝ)) = (volume : Measure (Euclid m)).prod volume holds by rfl`
- `sed -n 540,760p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt (printed proof of Simon Ch. 3, 4.3)`
- `lake env lean -DautoImplicit=false /tmp/tma-split-check/Full.lean (exit 0; #print axioms for the 10 children and the selected node)`
- `sed -n runtime.py _decompose, _dependency_problem, _existing_lean_name_problem, _solve_children; cat swarm-project.json (max_depth 6, max_children 12)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-8598f2d8c1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-8598f2d8c1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/tma-split-check/Full.lean`
- `/tmp/tma-split-check/Assembly.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`

Pins: snapshot manifest project b4d606db… and Mathlib 25730c7c… equal the workspace HEAD and .lake/packages/mathlib. Library: snapshot Mathlib supplies everything the children need: Isometry.map_euclideanHausdorffMeasure (Geometry/Euclidean/Volume/Measure.lean:141), EuclideanSpace.euclideanHausdorffMeasure_eq_volume (:187), LinearMap.trace_eq_sum_inner (InnerProductSpace/Trace.lean:25), HasCompactSupport.integral_Ioi_deriv_eq (IntegralEqImproper.lean:820), hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286), OrthonormalBasis.measurePreserving_repr_symm (Haar/InnerProductSpace.lean:114), setIntegral_comp_smul_of_pos (Haar/NormedSpace.lean:148), volume_preserving_piFinSuccAbove (Constructions/Pi.lean:818), integral_prod (Integral/Prod.lean:440), support_fderiv_subset (FDeriv/Const.lean:379), HasCompactSupport.contDiff_convolution_left (ContDiff/Convolution.lean:427), support_convolution_subset (Convolution.lean:670), exists_contDiff_tsupport_subset (BumpFunction/FiniteDimension.lean:45), finrank_orthogonal_span_singleton (Projection/FiniteDimensional.lean:125). ContDiffBump.dist_normed_convolution_le (BumpFunction/Convolution.lean:71) and integral_inner (Function/L2Space.lean:89) exist in the snapshot but are not in the contract's import closure, so the child proofs avoid them. No Mathlib, SimonGMT or accepted-DAG declaration states the half-space Gauss–Green formula, the rescaled Gauss–Green identity, the normal-defect estimate or the C¹-to-C⁰ extension; accepted candidates dimred_rpd_bilipschitz_image_measure, pit_setIntegral_range_linear and dgcr_stc_exists_normalized_mollifier were inspected and not needed, so no reuse. The 10 names codim1_rdo_dg_tma_* have no match among 993 DAG nodes, GMT/ or SimonGMT. Lean: /tmp/tma-split-check/Full.lean elaborates all 10 child types in the frozen contract scope, proves each with axioms propext, Classical.choice, Quot.sound, and proves the selected frozen type (byte-identical to dag.json) from them plus the three sibling stubs with exact frozen types (sorryAx only from the stubs). Runtime: depth 5 < max_depth 6, so the children are depth-6 leaves; 10 ≤ max_children 12.
