# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.weak_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Supplied proof of dtc_bc_lc_sl_lipschitz_leibniz, step 4 ("Weak convergence (Simon's (1))"), in particular 4(a) ("Reduction to pieces"). This is Simon's (1) in the proof of Ch. 6, Lemma 4.5(2) (chapter-06.txt lines 1253–1262, printed p. 156), with v ∈ L¹ tangent and with ∇^M h replaced by the approximate tangential gradient H: "we have merely to check that (1) holds with N_j in place of M_j". The chart data (ψ_j, V_j, Y_j, F_j) are exactly the conclusion of the parent's dependency dtc_bc_lc_sl_chart_pieces for (M, h); the parent obtains them and passes them in.

Dependencies:
 - Submission.dtc_bc_lc_sl_ll_piece_gradient (key piece_gradient);
 - Submission.dtc_bc_lc_sl_ll_piece_weak_limit (key piece_weak_limit).
Import: add `import Mathlib.Analysis.Normed.Group.Tannery` for tendsto_tsum_of_dominated_convergence (Tannery's theorem). Alternatively, prove that limit interchange directly by the same ε/3 argument.

Notation. N := n + 1, H^N := μHE[N], A_j := ψ_j(Y_j), D := fderiv ℝ.

1. Pieces.
 - Each A_j is Borel (MeasurableSet.image_of_continuousOn_injOn; ψ_j is continuous and injective on Y_j ⊆ closure(Y_j) ⊆ V_j).
 - A_j ⊆ M, the A_j are pairwise disjoint, and H^N(M ∖ ∪_j A_j) = 0.
 Hence M = ∪_j A_j up to an H^N-null set (ae_eq_set).

2. Tangency of w in chart form. Fix j. For H^N-a.e. x ∈ A_j, w(x) ∈ approxTangentPlane N M x (the hypothesis restricted to A_j ⊆ M). Let y ∈ Y_j with ψ_j(y) = x. M has approximate tangent space range Dψ_j(y) at x (chart data). By the definition of approxTangentPlane (a chosen tangent space when one exists) and uniqueness (HasApproximateTangentSpaceAt.unique), approxTangentPlane N M x = range Dψ_j(y). Hence for H^N-a.e. x ∈ A_j and every y ∈ Y_j with ψ_j(y) = x: w(x) ∈ range Dψ_j(y).

3. Gradient on the pieces. Fix j. Apply dtc_bc_lc_sl_ll_piece_gradient to M, ψ_j, V_j, Y_j, F_j, h and H. Its hypotheses are: the Borel and local finiteness hypotheses on M, the j-th chart data, and the hypothesis on H. It gives, for H^N-a.e. x ∈ A_j and every y ∈ Y_j with ψ_j(y) = x: ⟨H(x), Dψ_j(y)e⟩ = DF_j(y)e for all e.

4. Convergence on the pieces. Fix j. Apply dtc_bc_lc_sl_ll_piece_weak_limit to ψ_j, V_j, Y_j, F_j, h, K, G := H, the h_k, and w. Its hypotheses are: the j-th chart data; h K-Lipschitz; h∘ψ_j = F_j on Y_j; the hypotheses on h_k; step 3; w integrable on A_j ⊆ M; and step 2. It gives
 a_{k,j} := ∫_{A_j} Dh_k(x)(w(x)) dH^N → a_j := ∫_{A_j} ⟨H(x), w(x)⟩ dH^N as k → ∞.

5. Integrability and domination.
 - x ↦ Dh_k(x)(w(x)) is a.e.-strongly measurable on M (Dh_k is continuous because h_k is C¹; w is a.e.-strongly measurable; evaluation is continuous), and |Dh_k(x)(w(x))| ≤ K|w(x)|.
 - x ↦ ⟨H(x), w(x)⟩ is a.e.-strongly measurable (H Borel, inner product continuous), and |⟨H, w⟩| ≤ K|w|.
 So both are integrable on M. Moreover |a_{k,j}| ≤ b_j := K∫_{A_j} |w| dH^N for all k, j (norm_integral_le_integral_norm, integral_mono_of_nonneg). (b_j) is summable: Σ_j ∫_{A_j} |w| dH^N = ∫_{∪A_j} |w| dH^N ≤ ∫_M |w| dH^N < ∞ (hasSum_integral_iUnion).

6. Decomposition. For f integrable on M,
 ∫_M f dH^N = ∫_{∪_j A_j} f dH^N = Σ_j ∫_{A_j} f dH^N,
 by setIntegral_congr_set with step 1, then integral_iUnion (disjoint Borel pieces). Apply this to f = Dh_k(w) and f = ⟨H, w⟩:
 ∫_M Dh_k(w) dH^N = Σ_j a_{k,j} and ∫_M ⟨H, w⟩ dH^N = Σ_j a_j.

7. Dominated convergence for series. Tannery's theorem (tendsto_tsum_of_dominated_convergence), with steps 4 and 5, gives Σ_j a_{k,j} → Σ_j a_j. By step 6 this is the claim. ∎

Appendix: Lean proof checked during the decomposition. It is a complete proof of exactly this frozen type HE from the frozen types HD (piece_gradient) and HC2 (piece_weak_limit), with the extra import Mathlib.Analysis.Normed.Group.Tannery; axioms are propext, Classical.choice and Quot.sound. In Submission.lean, replace hD and hC2 by the corresponding Submission.<name> declarations.
```lean
set_option maxHeartbeats 4000000 in
theorem assembly_E (hD : HD) (hC2 : HC2) : HE := by
  intro P n M h K H ψ V Y F hs w hM hloc hh hHm hHK hHgrad hpc hdisj hnull hs_C1 hs_deriv hunif
    hw hwtan
  -- Step 1: the pieces are Borel subsets of `M`
  have hAmeas : ∀ j, MeasurableSet (ψ j '' Y j) := by
    intro j
    obtain ⟨-, hψ, hinj, -, -, hY, -, hYV, -⟩ := hpc j
    exact hY.image_of_continuousOn_injOn hψ.continuous.continuousOn
      (hinj.mono (subset_closure.trans hYV))
  have hAM : ∀ j, ψ j '' Y j ⊆ M := fun j => (hpc j).2.2.2.2.2.2.2.2.1
  -- Step 2: tangency of `w` in chart form
  have hwchart : ∀ j, ∀ᵐ x ∂(μHE[n + 1].restrict (ψ j '' Y j)), ∀ y ∈ Y j, ψ j y = x →
      w x ∈ LinearMap.range (fderiv ℝ (ψ j) y : Euclid (n + 1) →ₗ[ℝ] Euclid P) := by
    intro j
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (hAM j) hwtan] with x hx y hy hyx
    have htan := (hpc j).2.2.2.2.2.2.2.2.2.2 y hy
    rw [hyx] at htan
    have hex : ∃ Q', HasApproximateTangentSpaceAt (n + 1) M x Q' := ⟨_, htan⟩
    have hQeq : approxTangentPlane (n + 1) M x =
        LinearMap.range (fderiv ℝ (ψ j) y : Euclid (n + 1) →ₗ[ℝ] Euclid P) := by
      unfold approxTangentPlane
      rw [dif_pos hex]
      exact hex.choose_spec.unique htan
    rw [← hQeq]
    exact hx
  -- Step 3 (child piece_gradient)
  have hgrad : ∀ j, ∀ᵐ x ∂(μHE[n + 1].restrict (ψ j '' Y j)), ∀ y ∈ Y j, ψ j y = x →
      ∀ e : Euclid (n + 1), inner ℝ (H x) (fderiv ℝ (ψ j) y e) = fderiv ℝ (F j) y e := by
    intro j
    obtain ⟨hV, hψ, hinj, hDinj, hF, hY, hYc, hYV, hYM, hhF, htan⟩ := hpc j
    filter_upwards [hD P n M (ψ j) (V j) (Y j) (F j) h H hM hloc hV hψ hinj hDinj hF hY hYc hYV
      hYM hhF htan hHgrad] with x hx y hy hyx e
    exact (hx y hy hyx).2 e
  -- Step 4 (child piece_weak_limit)
  have hconv : ∀ j, Tendsto (fun k => ∫ x in ψ j '' Y j, fderiv ℝ (hs k) x (w x) ∂μHE[n + 1])
      atTop (𝓝 (∫ x in ψ j '' Y j, inner ℝ (H x) (w x) ∂μHE[n + 1])) := by
    intro j
    obtain ⟨hV, hψ, hinj, hDinj, hF, hY, hYc, hYV, hYM, hhF, -⟩ := hpc j
    exact hC2 P n (ψ j) (V j) (Y j) (F j) h K H hs w hV hψ hinj hDinj hF hY hYc hYV hh hhF hs_C1
      hs_deriv hunif (hgrad j) (hw.mono_set hYM) (hwchart j)
  -- Step 5: integrability and domination
  have hwn : IntegrableOn (fun x => ‖w x‖) M μHE[n + 1] := hw.norm
  have hwm : AEStronglyMeasurable w (μHE[n + 1].restrict M) := hw.aestronglyMeasurable
  have hfk_meas : ∀ k, AEStronglyMeasurable (fun x => fderiv ℝ (hs k) x (w x))
      (μHE[n + 1].restrict M) := fun k =>
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (((hs_C1 k).continuous_fderiv one_ne_zero).aestronglyMeasurable.prodMk hwm)
  have hpt : ∀ k x, ‖fderiv ℝ (hs k) x (w x)‖ ≤ (K : ℝ) * ‖w x‖ := by
    intro k x
    calc ‖fderiv ℝ (hs k) x (w x)‖ ≤ ‖fderiv ℝ (hs k) x‖ * ‖w x‖ :=
          (fderiv ℝ (hs k) x).le_opNorm _
      _ ≤ K * ‖w x‖ := by gcongr; exact hs_deriv k x
  have hfk_int : ∀ k, IntegrableOn (fun x => fderiv ℝ (hs k) x (w x)) M μHE[n + 1] := fun k =>
    Integrable.mono' (hwn.const_mul K) (hfk_meas k) (Eventually.of_forall (hpt k))
  have hf_int : IntegrableOn (fun x => inner ℝ (H x) (w x)) M μHE[n + 1] := by
    refine Integrable.mono' (hwn.const_mul K) ?_ (Eventually.of_forall fun x => ?_)
    · exact continuous_inner.comp_aestronglyMeasurable (hHm.aestronglyMeasurable.prodMk hwm)
    · calc ‖inner ℝ (H x) (w x)‖ ≤ ‖H x‖ * ‖w x‖ := norm_inner_le_norm _ _
        _ ≤ K * ‖w x‖ := by gcongr; exact hHK x
  -- Step 6: decomposition over the pieces
  have hMU : M =ᵐ[μHE[n + 1]] ⋃ j, ψ j '' Y j := by
    refine ae_eq_set.2 ⟨hnull, ?_⟩
    rw [diff_eq_empty.2 (iUnion_subset hAM)]
    exact measure_empty
  have hdecomp : ∀ f : Euclid P → ℝ, IntegrableOn f M μHE[n + 1] →
      ∫ x in M, f x ∂μHE[n + 1] = ∑' j, ∫ x in ψ j '' Y j, f x ∂μHE[n + 1] := by
    intro f hf
    rw [setIntegral_congr_set hMU,
      integral_iUnion hAmeas hdisj (hf.mono_set (iUnion_subset hAM))]
  have hlhs : (fun k => ∫ x in M, fderiv ℝ (hs k) x (w x) ∂μHE[n + 1]) =
      fun k => ∑' j, ∫ x in ψ j '' Y j, fderiv ℝ (hs k) x (w x) ∂μHE[n + 1] :=
    funext fun k => hdecomp _ (hfk_int k)
  rw [hlhs, hdecomp _ hf_int]
  -- Step 7: dominated convergence for series
  have hsum : Summable fun j => (K : ℝ) * ∫ x in ψ j '' Y j, ‖w x‖ ∂μHE[n + 1] :=
    ((hasSum_integral_iUnion hAmeas hdisj (hwn.mono_set (iUnion_subset hAM))).summable).mul_left _
  refine tendsto_tsum_of_dominated_convergence hsum hconv (Eventually.of_forall fun k j => ?_)
  calc ‖∫ x in ψ j '' Y j, fderiv ℝ (hs k) x (w x) ∂μHE[n + 1]‖
      ≤ ∫ x in ψ j '' Y j, ‖fderiv ℝ (hs k) x (w x)‖ ∂μHE[n + 1] :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in ψ j '' Y j, (K : ℝ) * ‖w x‖ ∂μHE[n + 1] := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
          ((hwn.mono_set (hAM j)).const_mul _) (Eventually.of_forall fun x => hpt k x)
    _ = (K : ℝ) * ∫ x in ψ j '' Y j, ‖w x‖ ∂μHE[n + 1] := integral_const_mul _ _
```

## Key steps

1. The pieces A_j = ψ_j(Y_j) are disjoint Borel subsets of M covering it up to an H^N-null set.
2. On A_j, approxTangentPlane N M (ψ_j y) = Dψ_j(y)(ℝ^N), so w is tangent in chart form.
3. piece_gradient: ⟨H, Dψ_j e⟩ = DF_j e a.e. on A_j.
4. piece_weak_limit: ∫_{A_j} Dh_k(w) → ∫_{A_j} ⟨H, w⟩ for every j.
5. Decompose ∫_M = Σ_j ∫_{A_j} (integral_iUnion); |∫_{A_j} Dh_k(w)| ≤ K∫_{A_j}|w| is summable; conclude by Tannery's theorem.

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
