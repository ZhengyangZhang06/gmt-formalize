# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.piece_weak_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Supplied proof of dtc_bc_lc_sl_lipschitz_leibniz, steps 4(c)–(e), on one chart piece. This is Simon's (1) in the proof of Ch. 6, Lemma 4.5(2) (chapter-06.txt lines 1253–1262, printed p. 156): "since N_j is C¹ this follows fairly easily by approximating v by smooth functions and using the fact that h^{(σ)} converges to h uniformly". One departure from the supplied text: the cut-off is placed on the chart (u_k := h_k∘ψ̃ with ψ̃ := χψ) instead of on the composite (χ·(h_k∘ψ)). Near closure(Y) the two agree, and this choice makes the uniform Lipschitz bound immediate.

Dependencies:
 - Submission.dtc_bc_lc_sl_ll_chart_pullback (key chart_pullback);
 - Submission.dtc_bc_lc_sl_ll_grad_weak_limit (key grad_weak_limit).
Import: add `import Poincare.SimonGMT.Chapter02.AreaDomain`, which provides Poincare.SimonGMT.Chapter02.ae_eq_of_hasFDerivWithinAt.

Notation. N := n + 1, H^N := μHE[N], L^N := volume on ℝ^N, A := ψ(Y), D := fderiv ℝ.

1. Pull-back. Apply chart_pullback to ψ, V, Y and obtain (i) and (ii). By (ii) applied to w (integrable on A and tangent a.e. by hypothesis), there is a Lebesgue integrable W : ℝ^N → ℝ^N with W = 0 off Y and
 ∫_A ℓ(x)(w(x)) dH^N = ∫ ℓ(ψ(y))(Dψ(y)W(y)) dy for every ℓ : ℝ^P → (ℝ^P)*.

2. Cut-off on the chart.
 - closure(Y) is compact, hence bounded: choose R with closure(Y) ⊆ B_R(0), and put R₁ := max(R, 1) > 0.
 - Let χ be the ContDiffBump centred at 0 with rIn = R₁ and rOut = 2R₁. Then χ is C^∞, has compact support, and χ = 1 on closedBall(0, R₁).
 - Put ψ̃ := χ·ψ. On the open set O := B_{R₁}(0) ⊇ Y we have ψ̃ = ψ.
 - ψ̃ is C¹ with compact support, so it is L_ψ-Lipschitz for some L_ψ (ContDiff.lipschitzWith_of_hasCompactSupport).

3. Uniformly Lipschitz, uniformly convergent family.
 - Each h_k is K-Lipschitz, because it is differentiable with ‖Dh_k‖ ≤ K (lipschitzWith_of_nnnorm_fderiv_le).
 - Put u_k := h_k∘ψ̃ and u := h∘ψ̃. All are (K·L_ψ)-Lipschitz (LipschitzWith.comp).
 - u_k → u uniformly on ℝ^N (TendstoUniformly.comp).

4. Weak-* limit. By grad_weak_limit (with N, u_k, u, Λ := K·L_ψ and W):
 ∫ Du_k(y)(W(y)) dy → ∫ Du(y)(W(y)) dy.

5. Identification of Du_k and the left side.
 - For y ∈ Y ⊆ O, u_k = h_k∘ψ on a neighbourhood of y (O is open and ψ̃ = ψ on O). So Du_k(y) = D(h_k∘ψ)(y) (Filter.EventuallyEq.fderiv_eq), and by the chain rule (fderiv_comp; h_k and ψ are differentiable) this equals Dh_k(ψ(y))∘Dψ(y).
 - For y ∉ Y, W(y) = 0.
 Hence for every y: Du_k(y)(W(y)) = Dh_k(ψ(y))(Dψ(y)W(y)). By step 1 with ℓ := Dh_k,
 ∫_A Dh_k(x)(w(x)) dH^N = ∫ Du_k(y)(W(y)) dy.

6. Identification of Du.
 - u = h∘ψ on O and h∘ψ = F on Y, so u = F on Y.
 - u is Lipschitz, so by Rademacher (LipschitzWith.ae_differentiableAt) it is differentiable at L^N-a.e. y.
 - Let Y' := Y ∩ {y : u is differentiable at y}. It is Borel (measurableSet_of_differentiableAt).
 - For y ∈ Y': u has derivative Du(y) within Y' at y. Also F has derivative DF(y) at y, and u = F on Y' with u(y) = F(y). So u has derivative DF(y) within Y' at y (HasFDerivWithinAt.congr).
 - By Poincare.SimonGMT.Chapter02.ae_eq_of_hasFDerivWithinAt (applied with f := u), Du = DF L^N-a.e. on Y'.
 Hence for L^N-a.e. y: if y ∈ Y then Du(y) = DF(y).

7. Chart-gradient identity on Y. Apply chart_pullback (i) to the property p(x) := (∀ y' ∈ Y, ψ(y') = x → ∀ e, ⟨G(x), Dψ(y')e⟩ = DF(y')e), which holds H^N-a.e. on A by hypothesis, and take y' := y. For L^N-a.e. y ∈ Y: ⟨G(ψ(y)), Dψ(y)e⟩ = DF(y)e for all e.

8. The right side. By step 1 with ℓ(x) := ⟨G(x), ·⟩ (innerSL ℝ (G x)),
 ∫_A ⟨G, w⟩ dH^N = ∫ ⟨G(ψ(y)), Dψ(y)W(y)⟩ dy.
 For a.e. y the integrand equals Du(y)(W(y)):
 - if y ∈ Y, by step 7 with e := W(y) and by step 6;
 - if y ∉ Y, both sides vanish because W(y) = 0.
 Hence ∫_A ⟨G, w⟩ dH^N = ∫ Du(y)(W(y)) dy (integral_congr_ae).

9. Conclusion. By steps 4, 5 and 8, ∫_A Dh_k(x)(w(x)) dH^N → ∫_A ⟨G(x), w(x)⟩ dH^N. ∎

Appendix: Lean proof checked during the decomposition. It is a complete proof of exactly this frozen type HC2 from the frozen types HC1 (chart_pullback) and HA (grad_weak_limit), with the extra import Poincare.SimonGMT.Chapter02.AreaDomain; axioms are propext, Classical.choice and Quot.sound. In Submission.lean, replace hC1 and hA by the corresponding Submission.<name> declarations.
```lean
set_option maxHeartbeats 4000000 in
theorem assembly_C2 (hC1 : HC1) (hA : HA) : HC2 := by
  intro P n ψ V Y F h K G hs w hV hψ hinj hDinj hFc hY hYc hYV hh hhF hs_C1 hs_deriv hunif hG hw
    hwtan
  obtain ⟨hC1i, hC1ii⟩ := hC1 P n ψ V Y hV hψ hinj hDinj hY hYc hYV
  -- Step 1 (child chart_pullback (ii))
  obtain ⟨W, hWint, hW0, hWid⟩ := hC1ii w hw hwtan
  -- Step 4: cut-off on the chart
  obtain ⟨R, hR⟩ : ∃ R : ℝ, closure Y ⊆ ball (0 : Euclid (n + 1)) R :=
    hYc.isBounded.subset_ball 0
  have hRpos : 0 < max R 1 := lt_max_of_lt_right one_pos
  let χ : ContDiffBump (0 : Euclid (n + 1)) := ⟨max R 1, 2 * max R 1, hRpos, by linarith⟩
  let ψt : Euclid (n + 1) → Euclid P := fun y => χ y • ψ y
  have hYO : ∀ y ∈ Y, y ∈ ball (0 : Euclid (n + 1)) (max R 1) := fun y hy =>
    ball_subset_ball (le_max_left R 1) (hR (subset_closure hy))
  have hO : ∀ y ∈ ball (0 : Euclid (n + 1)) (max R 1), ψt y = ψ y := by
    intro y hy
    have h1 : χ y = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hy)
    simp only [ψt, h1, one_smul]
  obtain ⟨Lψ, hLψ⟩ : ∃ C, LipschitzWith C ψt :=
    ContDiff.lipschitzWith_of_hasCompactSupport (χ.hasCompactSupport.smul_right)
      ((χ.contDiff (n := 1)).smul hψ) one_ne_zero
  -- Step 5: uniform Lipschitz bounds
  have hsLip : ∀ k, LipschitzWith K (hs k) := fun k =>
    lipschitzWith_of_nnnorm_fderiv_le ((hs_C1 k).differentiable one_ne_zero) (fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hs_deriv k x)
  have hu_lip : LipschitzWith (K * Lψ) (h ∘ ψt) := hh.comp hLψ
  -- Step 7 (child grad_weak_limit)
  have hlim := hA (n + 1) (fun k => hs k ∘ ψt) (h ∘ ψt) (K * Lψ) W
    (fun k => (hsLip k).comp hLψ) hu_lip (hunif.comp ψt) hWint
  -- Step 8: identification of `Du_k`
  have hleft : ∀ k, ∫ x in ψ '' Y, fderiv ℝ (hs k) x (w x) ∂μHE[n + 1] =
      ∫ y, fderiv ℝ (hs k ∘ ψt) y (W y) := by
    intro k
    rw [hWid (fun x => fderiv ℝ (hs k) x)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hyY : y ∈ Y
    · have hev : (hs k ∘ ψt) =ᶠ[𝓝 y] (hs k ∘ ψ) := by
        filter_upwards [isOpen_ball.mem_nhds (hYO y hyY)] with z hz
        simp only [Function.comp_apply, hO z hz]
      show fderiv ℝ (hs k) (ψ y) (fderiv ℝ ψ y (W y)) = fderiv ℝ (hs k ∘ ψt) y (W y)
      rw [hev.fderiv_eq, fderiv_comp y ((hs_C1 k).differentiable one_ne_zero _)
        (hψ.differentiable one_ne_zero y)]
      rfl
    · simp [hW0 y hyY]
  -- Step 9: identification of `Du` (Rademacher and SimonGMT ae_eq_of_hasFDerivWithinAt)
  have hdiff_ae : ∀ᵐ y ∂(volume : Measure (Euclid (n + 1))), DifferentiableAt ℝ (h ∘ ψt) y :=
    hu_lip.ae_differentiableAt
  have hY'meas : MeasurableSet (Y ∩ {y | DifferentiableAt ℝ (h ∘ ψt) y}) :=
    hY.inter (measurableSet_of_differentiableAt ℝ _)
  have huF : ∀ y ∈ Y, (h ∘ ψt) y = F y := by
    intro y hy
    simp only [Function.comp_apply, hO y (hYO y hy), hhF y hy]
  have hDuDF : (fun y => fderiv ℝ (h ∘ ψt) y) =ᵐ[volume.restrict
      (Y ∩ {y | DifferentiableAt ℝ (h ∘ ψt) y})] (fun y => fderiv ℝ F y) := by
    refine Poincare.SimonGMT.Chapter02.ae_eq_of_hasFDerivWithinAt (f := h ∘ ψt) hY'meas
      (fun y hy => ?_) (fun y hy => ?_)
    · exact hy.2.hasFDerivAt.hasFDerivWithinAt
    · exact ((hFc.differentiable one_ne_zero y).hasFDerivAt.hasFDerivWithinAt).congr
        (fun z hz => huF z hz.1) (huF y hy.1)
  have hDuDF' : ∀ᵐ y ∂(volume : Measure (Euclid (n + 1))), y ∈ Y →
      fderiv ℝ (h ∘ ψt) y = fderiv ℝ F y := by
    have h1 := (ae_restrict_iff' hY'meas).1 hDuDF
    filter_upwards [h1, hdiff_ae] with y hy1 hy2 hyY
    exact hy1 ⟨hyY, hy2⟩
  -- Step 3 (child chart_pullback (i)): the chart-gradient identity a.e. on `Y`
  have hGy : ∀ᵐ y ∂(volume : Measure (Euclid (n + 1))), y ∈ Y →
      ∀ e, inner ℝ (G (ψ y)) (fderiv ℝ ψ y e) = fderiv ℝ F y e := by
    have h1 := hC1i (fun x => ∀ y ∈ Y, ψ y = x → ∀ e : Euclid (n + 1),
      inner ℝ (G x) (fderiv ℝ ψ y e) = fderiv ℝ F y e) hG
    have h2 := (ae_restrict_iff' hY).1 h1
    filter_upwards [h2] with y hy hyY
    exact hy hyY y hyY rfl
  have hright : ∫ x in ψ '' Y, inner ℝ (G x) (w x) ∂μHE[n + 1] =
      ∫ y, fderiv ℝ (h ∘ ψt) y (W y) := by
    have h1 := hWid (fun x => innerSL ℝ (G x))
    simp only [innerSL_apply_apply] at h1
    rw [h1]
    refine integral_congr_ae ?_
    filter_upwards [hGy, hDuDF'] with y hy1 hy2
    by_cases hyY : y ∈ Y
    · rw [hy2 hyY, ← hy1 hyY (W y)]
    · simp [hW0 y hyY]
  rw [hright]
  exact hlim.congr (fun k => (hleft k).symm)
```

## Key steps

1. chart_pullback (ii) gives an integrable W, zero off Y, with ∫_{ψ(Y)} ℓ(w) dH^N = ∫ ℓ(ψ)(Dψ W) for every ℓ.
2. Cut-off on the chart: ψ̃ = χψ is Lipschitz and equals ψ near closure(Y). Then u_k = h_k∘ψ̃ and u = h∘ψ̃ are uniformly Lipschitz and u_k → u uniformly.
3. grad_weak_limit gives ∫ Du_k(W) → ∫ Du(W).
4. Du_k = Dh_k(ψ)∘Dψ on Y (chain rule), so ∫ Du_k(W) = ∫_{ψ(Y)} Dh_k(w) dH^N.
5. Du = DF a.e. on Y (Rademacher and SimonGMT ae_eq_of_hasFDerivWithinAt). The chart-gradient identity holds a.e. on Y (chart_pullback (i)). So ∫ Du(W) = ∫_{ψ(Y)} ⟨G, w⟩ dH^N.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1, mathlib 25730c7c); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `python3 -I scans of dag.json: the slicing-a1 children (chart_pieces, coarea, slice_family, ...) and their lean_statements; the dependencies im_calculus, defect_identity, lipschitz_smoothing, chart_pieces; regex 'lipschitz_leibniz|leibniz|tangential gradient|weak convergence|chart gradient' and 'TendstoUniformly|integral_lineDeriv|weak-limit|weakly' (hits dor_lmbsf_lipschitz_cutoff_leibniz, dor_lmbsf_piece_weak_limit, dor_lmbsf_tangential_gradient: all decomposing, different statements)`
- `git show <accepted commit>:GMT/Ch07/Submission.lean and whitespace-normalised comparison of theorem Submission.<name> with the DAG type: cmc_imRep_locality_restrict_sub (2af75d6), cmcs_cd_defect_identity (e32f0ad), cmcs_lipschitz_smoothing (00c458d) -> IDENTICAL`
- `grep -c dtc_bc_lc_sl_ll_ dag.json (0); git log --all -S dtc_bc_lc_sl_ll_ (no match); grep -rl dtc_bc_lc_sl_ll_ runs/.../nodes (none)`
- `scan of the 958 accepted candidate commits for imports added to Submission.lean (26 do, e.g. Poincare.SimonGMT.Chapter02.WeightedArea, Chapter02.AreaLipschitz, Mathlib.MeasureTheory.Function.ContinuousMapDense, Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox); verifier/gmt-compare.py candidate_inputs/child_modules/contract_scope (Submission.lean and new GMT/Ch07 files may change)`
- `grep in the snapshot mathlib for integral_lineDeriv_mul_eq, ae_differentiableAt_of_real, Besicovitch.ae_tendsto_measure_inter_div, Integrable.exists_hasCompactSupport_integral_sub_le, UniformContinuous.exists_contDiff_dist_le, tendsto_tsum_of_dominated_convergence, integral_iUnion, hasSum_integral_iUnion, setIntegral_congr_set, MeasurableSet.image_of_continuousOn_injOn, euclideanHausdorffMeasure_smul₀, Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, alternatizeUncurryFinCLM, alternatizeUncurryFin_apply, smulRightL, ContDiff.lipschitzWith_of_hasCompactSupport, ContDiffBump.one_of_mem_closedBall`
- `grep in SimonGMT for HasApproximateTangentSpaceAt (definition, .unique, support_euclideanHausdorffMeasure_restrict_submodule, regular_euclideanHausdorffMeasure_restrict_submodule), weighted_area_formula_volume_of_injective_derivative, integral_area_formula_of_injective_derivative, injective_area_formula_areaJacobianAt, integrableOn_image_iff_integrableOn_areaJacobian_smul, areaJacobianAt_eq_zero_iff_not_injective, ae_eq_of_hasFDerivWithinAt, ae_fderivWithin_eq_of_lipschitz_extension, continuous_normDet, measurable_areaJacobianAt`
- `lake env lean on /tmp/llz_dec/AllTypes.lean (11 types in the contract-mode challenge header), Avail.lean, Avail2.lean and Avail3.lean (#check of every cited lemma with the base and the extra imports), and AssemblyAll.lean with #print axioms`
- `sed book/chapter-06.txt lines 1180–1300 (4.2–4.5 and the proof of 4.5(2), including (1)–(3)); book/chapter-03.txt lines 325–362 (Definition 2.1 and the remark that ∇^M f does not depend on the decomposition)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-1a374f83a8/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/llz_dec/AllTypes.lean`
- `/tmp/llz_dec/AssemblyAll.lean`

The pinned libraries supply the tools but none of the needed lemmas. SimonGMT has Simon's approximate tangent spaces with uniqueness and plane-support lemmas (Ch. 3), the injective weighted, Bochner and measure area formulas with Jacobian positivity, and a.e. uniqueness of within-derivatives (Ch. 2, AreaDomain). Mathlib has Rademacher, integration by parts for Lipschitz functions, L¹-density of C_c functions, smooth uniform approximation, Tannery's theorem, Lusin–Souslin and the μHE scaling and translation laws. No pinned or DAG declaration proves any of: uniqueness of approximate differentials along a set, weak-* convergence of gradients, the anti-Lipschitz bound for immersions, the chart pull-back, or the Leibniz rule with a Lipschitz multiplier. The dor_lmbsf_* analogues are decomposing and state different results. Hence there are nine new children, with the prefix dtc_bc_lc_sl_ll_ (absent from dag.json and git history), plus two accepted declarations reused with identical types: cmc_imRep_locality_restrict_sub (2af75d6) and cmcs_cd_defect_identity (e32f0ad). Four children need imports outside the base closure: ContinuousMapDense, SmoothApprox, Chapter02.WeightedArea/AreaCritical, Chapter02.AreaDomain and Tannery. Accepted candidates already add such imports. All 11 types elaborate in the contract-mode challenge header. Lean assemblies prove the parent type from weak_limit, smooth_leibniz, orient_interior, chart_pieces and lipschitz_smoothing, and prove weak_limit, piece_gradient, piece_weak_limit and smooth_leibniz from their declared dependencies, all with axioms propext, Classical.choice and Quot.sound only.
