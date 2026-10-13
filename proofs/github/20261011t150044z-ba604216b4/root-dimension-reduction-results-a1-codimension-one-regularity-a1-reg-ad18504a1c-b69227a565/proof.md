# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1.vector_convergence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 3 of the supplied parent proof, formula (3a) (Simon Ch. 3, 4.3 (†): 'by 4.1, (1) and (2)'). Dependencies: rescaled_gauss_green, halfspace_gauss_green. Notation: H := {w : ⟨w, v⟩ > 0}, F_r := {w : y + r w ∈ F}, T := div g = trace Dg, P_v := (span{v})^⊥, H^m := μHE[m].

1. Radius and bounds. tsupport g is compact, so there is R > 0 with tsupport g ⊆ B_R(0). T is continuous (g is C¹ and the trace is linear on a finite-dimensional space), and T(w) = 0 whenever w ∉ B_R(0): then w ∉ tsupport g, so Dg(w) = 0 because the support of Dg lies in tsupport g. Hence T has compact support, is integrable, and |T| ≤ M for some M ≥ 0.
2. Rescaled identity for small r. Let 0 < r < ρ₁/R. For w ∈ tsupport g, |(y + r w) − y| = r|w| < rR < ρ₁, so y + r w ∈ B̄_{ρ₁}(y) ⊆ D. Thus rescaled_gauss_green applies and gives r^{-m} ∫ ⟨g(r^{-1}(z − y)), ν(z)⟩ dμ(z) = −∫_{F_r} T for every r ∈ (0, ρ₁/R), in particular eventually as r ↓ 0.
3. Comparison estimate. For r > 0, F_r is Borel (preimage of F under a continuous map) and H is open. Then |∫_{F_r} T − ∫_H T| = |∫ (1_{F_r} − 1_H) T| ≤ ∫ M · 1_{(F_r Δ H) ∩ B_R(0)} = M · L^{m+1}((F_r Δ H) ∩ B_R(0)). Indeed, pointwise (1_{F_r} − 1_H)(w) T(w) = 0 if w ∉ B_R(0) (since T(w) = 0) or if w ∉ F_r Δ H (since the two indicators agree), and otherwise its absolute value is |T(w)| ≤ M. The volume on the right is finite (at most L^{m+1}(B_R(0))).
4. By the hypothesis with this R, L^{m+1}((F_r Δ H) ∩ B_R(0)) → 0 as r ↓ 0 (in [0, ∞], hence also as real numbers), so by step 3 and the squeeze principle ∫_{F_r} T → ∫_H T.
5. By halfspace_gauss_green (|v| = 1, g C¹ with compact support), ∫_H T = −∫_{P_v} ⟨g, v⟩ dH^m. Hence −∫_{F_r} T → ∫_{P_v} ⟨g, v⟩ dH^m as r ↓ 0.
6. By step 2, r ↦ r^{-m} ∫ ⟨g(r^{-1}(z − y)), ν(z)⟩ dμ(z) agrees with r ↦ −∫_{F_r} T on (0, ρ₁/R), so it has the same limit: r^{-m} ∫ ⟨g(r^{-1}(z − y)), ν(z)⟩ dμ(z) → ∫_{(span{v})^⊥} ⟨g, v⟩ dH^m. ∎

Appendix (formal check; the numbered proof above is the argument). The Lean proof below of exactly this frozen statement was compiled in the pinned project (Lean v4.35.0-rc3, Mathlib 25730c7c) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`), as part of one file containing all ten children; it refers only to the sibling theorem(s) `Submission.codim1_rdo_dg_tma_rescaled_gauss_green`, `Submission.codim1_rdo_dg_tma_halfspace_gauss_green` with their frozen types, and `#print axioms` reports propext, Classical.choice, Quot.sound.

theorem Submission.codim1_rdo_dg_tma_vector_convergence : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)) (ρ₁ : ℝ), MeasurableSet F → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → 0 < ρ₁ → closedBall y ρ₁ ⊆ D → ‖v‖ = 1 → (∀ R : ℝ, Tendsto (fun r : ℝ => volume (symmDiff ((fun w => y + r • w) ⁻¹' F) {w | 0 < inner ℝ w v} ∩ ball (0 : Euclid (m + 1)) R)) (𝓝[>] 0) (𝓝 0)) → ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 g → HasCompactSupport g → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ) (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))), inner ℝ (g z) v ∂μHE[m])) := by
  intro m D F μ ν y v ρ₁ hF hGG hρ₁ hball hv hblow g hg hgc
  obtain ⟨R, hRpos, hR⟩ : ∃ R : ℝ, 0 < R ∧ tsupport g ⊆ ball (0 : Euclid (m + 1)) R := by
    obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_ball (0 : Euclid (m + 1))
    exact ⟨max R 1, by positivity, hR.trans (ball_subset_ball (le_max_left _ _))⟩
  set T : Euclid (m + 1) → ℝ := fun w =>
    LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1))
    with hTdef
  have hTcont : Continuous T := by
    have h1 : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
    have h2 : Continuous (fun A : Euclid (m + 1) →L[ℝ] Euclid (m + 1) =>
        LinearMap.trace ℝ (Euclid (m + 1)) (A : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1))) :=
      ((LinearMap.trace ℝ (Euclid (m + 1))).comp
        (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional
    exact h2.comp h1
  have hTzero : ∀ w, w ∉ ball (0 : Euclid (m + 1)) R → T w = 0 := by
    intro w hw
    have hw' : w ∉ tsupport g := fun h => hw (hR h)
    have : fderiv ℝ g w = 0 := by
      by_contra hne
      exact hw' (support_fderiv_subset ℝ hne)
    simp [hTdef, this]
  have hTcs : HasCompactSupport T := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) R) ?_
    intro w hw
    exact hTzero w (fun h => hw (ball_subset_closedBall h))
  obtain ⟨M, hM⟩ : ∃ M, ∀ w, ‖T w‖ ≤ M := hTcont.bounded_above_of_compact_support hTcs
  have hTint : Integrable T := hTcont.integrable_of_hasCompactSupport hTcs
  set H : Set (Euclid (m + 1)) := {w | 0 < inner ℝ w v} with hHdef
  have hHmeas : MeasurableSet H :=
    (isOpen_lt continuous_const (continuous_id.inner continuous_const)).measurableSet
  -- eventual identity from the rescaled Gauss–Green formula
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), (r ^ m)⁻¹ * ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ =
      -∫ w in (fun w => y + r • w) ⁻¹' F, T w := by
    have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ρ₁ / R :=
      nhdsWithin_le_nhds (gt_mem_nhds (div_pos hρ₁ hRpos))
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrR
    refine Submission.codim1_rdo_dg_tma_rescaled_gauss_green m D F μ ν y r g hF hGG hr hg hgc ?_
    intro w hw
    apply hball
    have hwR : ‖w‖ < R := by simpa using hR hw
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    have : r * ‖w‖ ≤ r * R := mul_le_mul_of_nonneg_left hwR.le hr.le
    have h2 : r * R < ρ₁ := by
      have := (lt_div_iff₀ hRpos).mp hrR
      linarith
    linarith
  -- convergence of the set integrals over the blown-up sets
  have hlim : Tendsto (fun r : ℝ => ∫ w in (fun w => y + r • w) ⁻¹' F, T w) (𝓝[>] 0)
      (𝓝 (∫ w in H, T w)) := by
    have hbound : ∀ r : ℝ, 0 < r → ‖(∫ w in (fun w => y + r • w) ⁻¹' F, T w) - ∫ w in H, T w‖ ≤
        M * (volume (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
          ball (0 : Euclid (m + 1)) R)).toReal := by
      intro r hr
      have hFr : MeasurableSet ((fun w => y + r • w) ⁻¹' F) :=
        hF.preimage (by fun_prop)
      rw [← integral_indicator hFr, ← integral_indicator hHmeas, ← integral_sub
        (hTint.indicator hFr) (hTint.indicator hHmeas)]
      have hS : MeasurableSet (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
          ball (0 : Euclid (m + 1)) R) :=
        ((hFr.symmDiff hHmeas)).inter measurableSet_ball
      have hfin : volume (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
          ball (0 : Euclid (m + 1)) R) ≠ ∞ :=
        (measure_mono inter_subset_right).trans_lt measure_ball_lt_top |>.ne
      calc ‖∫ w, ((fun w => y + r • w) ⁻¹' F).indicator T w - H.indicator T w‖
          ≤ ∫ w, (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
              ball (0 : Euclid (m + 1)) R).indicator (fun _ => M) w := by
            have hInt : Integrable ((symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
                ball (0 : Euclid (m + 1)) R).indicator (fun _ => M)) :=
              (integrable_indicator_iff hS).2 (integrableOn_const hfin)
            refine norm_integral_le_of_norm_le hInt (Eventually.of_forall fun w => ?_)
            have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
            have hMabs : ∀ w, |T w| ≤ M := fun w => by simpa [Real.norm_eq_abs] using hM w
            by_cases hwB : w ∈ ball (0 : Euclid (m + 1)) R
            · by_cases h1 : w ∈ (fun w => y + r • w) ⁻¹' F <;> by_cases h2 : w ∈ H <;>
                simp [indicator_apply, h1, h2, hwB, Set.mem_symmDiff, hMabs, hM0, norm_neg]
            · have hT0 := hTzero w hwB
              by_cases h1 : w ∈ (fun w => y + r • w) ⁻¹' F <;> by_cases h2 : w ∈ H <;>
                simp [indicator_apply, h1, h2, hwB, hT0, Set.mem_symmDiff, hM0]
        _ = M * (volume (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
              ball (0 : Euclid (m + 1)) R)).toReal := by
            rw [integral_indicator_const _ hS, smul_eq_mul, mul_comm, Measure.real]
    have h0 : Tendsto (fun r : ℝ => M * (volume (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
          ball (0 : Euclid (m + 1)) R)).toReal) (𝓝[>] 0) (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hblow R)
      simpa using this.const_mul M
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hbound r hr
  have hGGH := Submission.codim1_rdo_dg_tma_halfspace_gauss_green m v g hv hg hgc
  have hneg := hlim.neg
  rw [show (∫ w in H, T w) = -∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))),
      inner ℝ (g z) v ∂μHE[m] from hGGH, neg_neg] at hneg
  exact hneg.congr' (hev.mono fun r hr => hr.symm)

## Key steps

1. Choose R with tsupport g ⊆ B_R(0); T = div g is continuous, bounded and vanishes off B_R(0).
2. For 0 < r < ρ₁/R, rescaled_gauss_green: r^{-m} ∫ ⟨g(r^{-1}(z − y)), ν⟩ dμ = −∫_{F_r} div g.
3. |∫_{F_r} T − ∫_H T| ≤ sup|T| · L^{m+1}((F_r Δ H) ∩ B_R(0)) → 0 by the blow-up hypothesis.
4. halfspace_gauss_green: −∫_H div g = ∫_{v^⊥} ⟨g, v⟩ dH^m.

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
