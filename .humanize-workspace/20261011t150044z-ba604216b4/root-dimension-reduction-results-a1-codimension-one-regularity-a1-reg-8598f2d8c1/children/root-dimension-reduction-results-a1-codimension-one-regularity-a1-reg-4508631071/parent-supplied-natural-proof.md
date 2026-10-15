# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1.tangential_halfspace-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Extracted from step 2 of the supplied parent proof (Simon Ch. 3, 4.3 (†)): for the boundary-parallel basis directions b_i ⊥ v, 'For i ≤ m, ∫_{H_v} D⟨g, b_i⟩(b_i) dL = 0', which the parent obtains by integrating the derivative along the lines in the b_i-direction (fundamental theorem of calculus, compact support). The same vanishing is proved here in its integrated form: H is invariant under translation along u, so the u-translates of h have the same integral over H, and the derivative of this constant integral in the translation parameter is ∫_H Dh(w)(u) dw. This is the line-by-line FTC argument summed over all lines, and it needs no further Fubini decomposition. Notation: ℝ^P := Euclid P, L^P := volume, H := {w : ⟨w, v⟩ > 0}.

1. H is open (preimage of (0, ∞) under the continuous map w ↦ ⟨w, v⟩), hence Borel. For t ∈ ℝ and w ∈ ℝ^P, ⟨w + t u, v⟩ = ⟨w, v⟩ + t⟨u, v⟩ = ⟨w, v⟩, so w + t u ∈ H if and only if w ∈ H.
2. Constancy. Put Φ(t) := ∫_H h(w + t u) dw. By step 1, 1_H(w) h(w + t u) = (1_H h)(w + t u) for all w, so by translation invariance of Lebesgue measure Φ(t) = ∫ (1_H h)(w + t u) dw = ∫ (1_H h)(w) dw = Φ(0) for every t. Hence Φ is constant, and Φ has derivative 0 at t = 0.
3. Bounds. Choose R with tsupport h ⊆ B̄_R(0) (h has compact support) and M with |Dh(w)| ≤ M for all w (Dh is continuous and vanishes outside the compact set tsupport h). For |t| < 1 and any w, the map t ↦ h(w + t u) has derivative Dh(w + t u)(u) (chain rule). If Dh(w + t u) ≠ 0 then w + t u ∈ tsupport h (the support of Dh lies in tsupport h), so |w| ≤ |w + t u| + |t||u| ≤ R + |u|. Hence |Dh(w + t u)(u)| ≤ b(w) := M|u| 1_{B̄_{R+|u|}(0)}(w), and b is integrable (a constant on a ball of finite measure). The maps w ↦ h(w + t u) and w ↦ Dh(w + t u)(u) are continuous, hence measurable, and h is integrable on H (continuous with compact support).
4. Differentiation under the integral sign. By the dominated differentiation theorem (Mathlib `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, applied to the measure L^P restricted to H, with F(t, w) = h(w + t u), F′(t, w) = Dh(w + t u)(u), the neighbourhood (−1, 1) of 0 and the bound b of step 3), Φ is differentiable at 0 with Φ′(0) = ∫_H Dh(w)(u) dw.
5. By uniqueness of derivatives and step 2, ∫_H Dh(w)(u) dw = Φ′(0) = 0. ∎

Appendix (formal check; the numbered proof above is the argument). The Lean proof below of exactly this frozen statement was compiled in the pinned project (Lean v4.35.0-rc3, Mathlib 25730c7c) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`), as part of one file containing all ten children; it uses no other child, and `#print axioms` reports propext, Classical.choice, Quot.sound.

theorem Submission.codim1_rdo_dg_tma_tangential_halfspace : ∀ (P : ℕ) (v u : Euclid P) (h : Euclid P → ℝ), inner ℝ u v = 0 → ContDiff ℝ 1 h → HasCompactSupport h → ∫ w in {w : Euclid P | 0 < inner ℝ w v}, fderiv ℝ h w u = 0 := by
  intro P v u h huv hh hhc
  set H : Set (Euclid P) := {w | 0 < inner ℝ w v} with hHdef
  have hHmeas : MeasurableSet H :=
    (isOpen_lt continuous_const (continuous_id.inner continuous_const)).measurableSet
  have hHinv : ∀ (t : ℝ) (w : Euclid P), w + t • u ∈ H ↔ w ∈ H := by
    intro t w
    simp [hHdef, inner_add_left, real_inner_smul_left, huv]
  -- the translated integrals do not depend on t
  have hconst : ∀ t : ℝ, ∫ w in H, h (w + t • u) = ∫ w in H, h w := by
    intro t
    rw [← integral_indicator hHmeas, ← integral_indicator hHmeas]
    have hfun : (fun w => H.indicator (fun w => h (w + t • u)) w) =
        fun w => H.indicator h (w + t • u) := by
      funext w
      by_cases hw : w ∈ H
      · rw [indicator_of_mem hw, indicator_of_mem ((hHinv t w).2 hw)]
      · rw [indicator_of_notMem hw, indicator_of_notMem (fun h' => hw ((hHinv t w).1 h'))]
    rw [hfun, integral_add_right_eq_self (fun w => H.indicator h w) (t • u)]
  -- differentiation under the integral sign at t = 0
  obtain ⟨R, hR⟩ := hhc.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  have hdc : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ := hdc.bounded_above_of_compact_support (hhc.fderiv ℝ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set bound : Euclid P → ℝ :=
    (closedBall (0 : Euclid P) (R + ‖u‖)).indicator (fun _ => M * ‖u‖) with hbound
  have hhd : Differentiable ℝ h := hh.differentiable one_ne_zero
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict H) (F := fun (t : ℝ) w => h (w + t • u))
    (F' := fun (t : ℝ) w => fderiv ℝ h (w + t • u) u) (x₀ := (0 : ℝ)) (bound := bound)
    (ball_mem_nhds (0 : ℝ) one_pos)
    (Eventually.of_forall fun t => (hh.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (by
      simp only [zero_smul, add_zero]
      exact (hh.continuous.integrable_of_hasCompactSupport hhc).integrableOn)
    ((hdc.clm_apply continuous_const).comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun w t ht => by
      by_cases hwt : w + t • u ∈ tsupport h
      · have h1 : ‖w + t • u‖ ≤ R := by simpa using hR hwt
        have ht1 : |t| < 1 := by simpa using ht
        have h2 : ‖w‖ ≤ R + ‖u‖ := by
          calc ‖w‖ = ‖(w + t • u) - t • u‖ := by simp
            _ ≤ ‖w + t • u‖ + ‖t • u‖ := norm_sub_le _ _
            _ ≤ R + ‖u‖ := by
                rw [norm_smul, Real.norm_eq_abs]
                nlinarith [abs_nonneg t, norm_nonneg u]
        rw [hbound, indicator_of_mem (by simpa using h2)]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
      · have : fderiv ℝ h (w + t • u) = 0 := by
          by_contra hne
          exact hwt (support_fderiv_subset ℝ hne)
        rw [this, ContinuousLinearMap.zero_apply, norm_zero]
        exact indicator_nonneg (fun _ _ => mul_nonneg hM0 (norm_nonneg _)) _)
    ((integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (measure_closedBall_lt_top).ne)).integrableOn
    (Eventually.of_forall fun w t _ => by
      have h1 : HasDerivAt (fun t : ℝ => w + t • u) u t := by
        simpa using ((hasDerivAt_id t).smul_const u).const_add w
      exact ((hhd (w + t • u)).hasFDerivAt.comp_hasDerivAt t h1))
  have h0 : HasDerivAt (fun t : ℝ => ∫ w in H, h (w + t • u)) 0 0 := by
    have hfun : (fun t : ℝ => ∫ w in H, h (w + t • u)) = fun _ => ∫ w in H, h w :=
      funext hconst
    rw [hfun]
    exact hasDerivAt_const _ _
  have := key.2.unique h0
  simpa using this

## Key steps

1. ⟨u, v⟩ = 0 makes H = {⟨w, v⟩ > 0} invariant under w ↦ w + t u.
2. Translation invariance of Lebesgue measure: t ↦ ∫_H h(w + t u) dw is constant.
3. Domination |Dh(w + t u)(u)| ≤ M|u| 1_{B̄_{R+|u|}(0)}(w) for |t| < 1.
4. Differentiating under the integral at t = 0 gives ∫_H Dh(w)(u) dw, which therefore equals 0.

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
