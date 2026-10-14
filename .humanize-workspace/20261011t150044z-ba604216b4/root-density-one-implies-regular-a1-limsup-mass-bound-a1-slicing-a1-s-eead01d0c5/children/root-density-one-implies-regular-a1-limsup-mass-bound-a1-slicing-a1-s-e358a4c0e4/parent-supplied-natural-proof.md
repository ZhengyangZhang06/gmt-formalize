# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1.weak_integrable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 3, “Density”, “Uniform bounds” and “Conclusion”. The u_k here are globally Lipschitz, so the cut-off of the test fields used there is not needed. Uses the sibling weak_smooth (Lean Submission.dor_lmbsf_pwl_fderiv_weak_smooth).

1. u is K-Lipschitz: |u(x) − u(z)| = lim_k |u_k(x) − u_k(z)| ≤ K|x − z|.
2. Uniform bound. Let v be K-Lipschitz (v = u_k or v = u) and let Θ : ℝ^d → ℝ^d be integrable.
 - ‖Dv(y)‖ ≤ K for every y (norm_fderiv_le_of_lipschitz; Dv(y) = 0 at non-differentiability points).
 - y ↦ Dv(y) is Borel (measurable_fderiv). So y ↦ Dv(y)[Θ(y)] is a.e.-strongly measurable, being continuous evaluation of the pair (Dv(y), Θ(y)).
 - |Dv(y)[Θ(y)]| ≤ K|Θ(y)|. Hence y ↦ Dv(y)[Θ(y)] is integrable and |∫ Dv[Θ]| ≤ K ∫|Θ|.
 - By linearity of Dv(y) and of the integral, ∫ Dv[Φ] = ∫ Dv[Φ − Ψ] + ∫ Dv[Ψ] for every integrable Ψ.
3. Fix ε > 0 and put η := ε/(4K + 1) > 0, so that Kη ≤ ε/4. Smooth compactly supported functions are dense in L¹ (MeasureTheory.MemLp.exist_eLpNorm_sub_le with p = 1). So there is a C^∞, in particular C¹, field Ψ : ℝ^d → ℝ^d with compact support and ∫|Φ − Ψ| ≤ η. In Lean, use eLpNorm f 1 = ∫⁻‖f‖ₑ and ∫‖f‖ = (∫⁻‖f‖ₑ).toReal. Ψ is continuous with compact support, hence integrable.
4. By weak_smooth applied to (u_k), u and Ψ, ∫ Du_k[Ψ] → ∫ Du[Ψ]. Choose N with |∫ Du_k[Ψ] − ∫ Du[Ψ]| < ε/2 for all k ≥ N.
5. For k ≥ N, steps 2–4 give
 |∫ Du_k[Φ] − ∫ Du[Φ]| ≤ |∫ Du_k[Φ − Ψ]| + |∫ Du[Φ − Ψ]| + |∫ Du_k[Ψ] − ∫ Du[Ψ]| < Kη + Kη + ε/2 ≤ ε.
6. Since ε > 0 was arbitrary, ∫ Du_k[Φ] → ∫ Du[Φ]. ∎

Lean realization: compiled during decomposition with the pinned toolchain in the Submission layout, as the body of `theorem Submission.dor_lmbsf_pwl_fderiv_weak_integrable : (frozen lean_statement) := by` inside `namespace GMT.Ch07`. #print axioms reports only propext, Classical.choice and Quot.sound. Extra imports: Mathlib.Analysis.Normed.Lp.SmoothApprox. Write the sum of two integrals as `(∫ y, f y) + ∫ y, g y`: without the parentheses, `∫ y, f y + ∫ y, g y` parses as a single integral.
```lean
  intro d K us u Φ hus hU hΦ
  have hu : LipschitzWith K u := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    exact le_of_tendsto ((hU.tendsto_at x).dist (hU.tendsto_at y))
      (Eventually.of_forall fun k => (hus k).dist_le_mul x y)
  have hbound : ∀ (v : Euclid d → ℝ), LipschitzWith K v → ∀ Θ : Euclid d → Euclid d,
      Integrable Θ → Integrable (fun y => fderiv ℝ v y (Θ y)) ∧
        ‖∫ y, fderiv ℝ v y (Θ y)‖ ≤ K * ∫ y, ‖Θ y‖ := by
    intro v hv Θ hΘ
    have hmeas : AEStronglyMeasurable (fun y => fderiv ℝ v y (Θ y)) volume := by
      have h1 : AEStronglyMeasurable (fun y => fderiv ℝ v y) volume :=
        (measurable_fderiv ℝ v).aestronglyMeasurable
      exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Euclid d) (F := ℝ)).continuous.comp_aestronglyMeasurable
        (h1.prodMk hΘ.aestronglyMeasurable)
    have hle : ∀ y, ‖fderiv ℝ v y (Θ y)‖ ≤ K * ‖Θ y‖ := fun y =>
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hv) (norm_nonneg _))
    refine ⟨Integrable.mono' (hΘ.norm.const_mul K) hmeas (Eventually.of_forall hle), ?_⟩
    calc ‖∫ y, fderiv ℝ v y (Θ y)‖ ≤ ∫ y, (K : ℝ) * ‖Θ y‖ :=
          norm_integral_le_of_norm_le (hΘ.norm.const_mul K) (Eventually.of_forall hle)
      _ = K * ∫ y, ‖Θ y‖ := integral_const_mul _ _
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hK0 : (0 : ℝ) ≤ K := K.2
  set η : ℝ := ε / (4 * K + 1) with hη
  have hηpos : 0 < η := div_pos hε (by positivity)
  obtain ⟨Ψ, hΨc, hΨs, hΨε⟩ :=
    (memLp_one_iff_integrable.2 hΦ).exist_eLpNorm_sub_le (p := 1) (by simp) le_rfl hηpos
  have hΨi : Integrable Ψ := hΨs.continuous.integrable_of_hasCompactSupport hΨc
  have hdiff : ∫ y, ‖(Φ - Ψ) y‖ ≤ η := by
    have h1 := integral_norm_eq_lintegral_enorm (μ := (volume : Measure (Euclid d)))
      (hΦ.sub hΨi).aestronglyMeasurable
    rw [h1, ← eLpNorm_one_eq_lintegral_enorm]
    all_goals first
      | exact ENNReal.toReal_le_of_le_ofReal hηpos.le hΨε
      | exact (hΦ.sub hΨi).aestronglyMeasurable
  have hconv := Submission.dor_lmbsf_pwl_fderiv_weak_smooth d K us u Ψ hus hU (hΨs.of_le (by exact_mod_cast le_top)) hΨc
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv (ε / 2) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  have hK1 := hbound (us k) (hus k) (Φ - Ψ) (hΦ.sub hΨi)
  have hK2 := hbound u hu (Φ - Ψ) (hΦ.sub hΨi)
  have e1 : ∫ y, fderiv ℝ (us k) y (Φ y) =
      (∫ y, fderiv ℝ (us k) y ((Φ - Ψ) y)) + ∫ y, fderiv ℝ (us k) y (Ψ y) := by
    calc ∫ y, fderiv ℝ (us k) y (Φ y)
        = ∫ y, (fderiv ℝ (us k) y ((Φ - Ψ) y) + fderiv ℝ (us k) y (Ψ y)) := by
          congr 1
          funext y
          simp
      _ = _ := integral_add hK1.1 (hbound (us k) (hus k) Ψ hΨi).1
  have e2 : ∫ y, fderiv ℝ u y (Φ y) =
      (∫ y, fderiv ℝ u y ((Φ - Ψ) y)) + ∫ y, fderiv ℝ u y (Ψ y) := by
    calc ∫ y, fderiv ℝ u y (Φ y)
        = ∫ y, (fderiv ℝ u y ((Φ - Ψ) y) + fderiv ℝ u y (Ψ y)) := by
          congr 1
          funext y
          simp
      _ = _ := integral_add hK2.1 (hbound u hu Ψ hΨi).1
  rw [dist_eq_norm, e1, e2]
  have h3 := hN k hk
  rw [dist_eq_norm] at h3
  have hKη : (K : ℝ) * η ≤ ε / 4 := by
    rw [hη, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set A1k := ∫ y, fderiv ℝ (us k) y ((Φ - Ψ) y)
  set A2k := ∫ y, fderiv ℝ (us k) y (Ψ y)
  set B1 := ∫ y, fderiv ℝ u y ((Φ - Ψ) y)
  set B2 := ∫ y, fderiv ℝ u y (Ψ y)
  have hA1k : ‖A1k‖ ≤ K * η := hK1.2.trans (mul_le_mul_of_nonneg_left hdiff hK0)
  have hB1 : ‖B1‖ ≤ K * η := hK2.2.trans (mul_le_mul_of_nonneg_left hdiff hK0)
  calc ‖A1k + A2k - (B1 + B2)‖ = ‖A1k - B1 + (A2k - B2)‖ := by ring_nf
    _ ≤ ‖A1k‖ + ‖B1‖ + ‖A2k - B2‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ < ε := by linarith [hA1k, hB1, h3, hKη]
```

## Key steps

1. u is K-Lipschitz; ‖Dv‖ ≤ K gives integrability of Dv[Θ] and |∫ Dv[Θ]| ≤ K‖Θ‖_{L¹}.
2. Approximate Φ in L¹ by a smooth compactly supported Ψ (MemLp.exist_eLpNorm_sub_le).
3. Apply weak_smooth to Ψ.
4. ε/3 estimate: |∫Du_k[Φ] − ∫Du[Φ]| ≤ 2K‖Φ − Ψ‖₁ + |∫Du_k[Ψ] − ∫Du[Ψ]|.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; cmp snapshot project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean (identical); cmp snapshot mathlib Analysis/Calculus/Rademacher.lean, Analysis/Normed/Lp/SmoothApprox.lean, MeasureTheory/Covering/Besicovitch.lean, Geometry/Manifold/PartitionOfUnity.lean, Analysis/Calculus/FDeriv/Basic.lean, Geometry/Euclidean/Volume/Measure.lean against lake-packages-25730c7c/mathlib (all identical)`
- `python3 -I scan of dag.json: frozen types of dor_lmbsf_piece_weak_limit and dor_lmbsf_density_directions (exact string match); regex 'lineDeriv|Rademacher|weak|McShane|extend_real|density point|Besicovitch|ae_tendsto_measure_inter_div|integral_lineDeriv_mul_eq|dense_hasCompactSupport|areaJacobian|area formula|uniformly Lipschitz|TendstoUniformly' over node statements; lean_name collision check for the seven dor_lmbsf_pwl_* names (1523 nodes, none)`
- `grep -n 'integral_area_formula_of_injective_derivative|weighted_area_formula_of_injective_derivative|map_withDensity_areaJacobian_eq|integrableOn_image_iff_integrableOn_areaJacobian_smul|areaJacobianAt_eq_zero_iff_not_injective|measurable_areaJacobianAt|def areaJacobianAt|areaJacobianAt_nonneg' simongmt/Poincare/SimonGMT/Chapter02`
- `rg/grep -n 'integral_lineDeriv_mul_eq|ae_differentiableAt|HasFDerivWithinAt.lim|ae_tendsto_measure_inter_div|exist_eLpNorm_sub_le|dense_hasCompactSupport_contDiff|exists_contDiff_zero_iff_one_iff_of_isClosed|lipschitzWith_of_nnnorm_fderiv_le|ContDiff.lipschitzWith_of_hasCompactSupport|norm_fderiv_le_of_lipschitz|measurable_fderiv|NormedRing.inverse_continuousAt|ContinuousLinearMap.isUnit_iff_bijective|euclideanHausdorffMeasure_eq_volume|exists_cthickening_subset_open|cthickening_subset_thickening|tendsto_integral_filter_of_dominated_convergence|Integrable.smul_bdd|Integrable.bdd_mul|setIntegral_indicator|setIntegral_eq_integral_of_forall_compl_eq_zero|setIntegral_congr_ae|ae_withDensity_iff|ae_of_ae_map' in the snapshot/package mathlib`
- `python3 -I verifier gmt-compare.contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') and lean_contract.validate_lean_statement on the seven child types`
- `git show proof-workspace/gmt-ch07/20261011t150044z-ba604216b4/theorems/solutions/root-density-and-tangent-cones-a1-blowup-scaling-a1-testform-correspondence-a1-7af5165c95:GMT/Ch07/Submission.lean (child layout: theorem Submission.X inside namespace GMT.Ch07)`
- `toolchains/lean-4.35.0-rc3-linux/bin/lake env lean on /tmp/pwl-decomp/{Types,Assembly,Probe2,ProtoA1,ProtoA,ProtoB,ProtoE,ProtoC,ProtoF,ProtoD,All,Layout,LayoutCmp}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-eead01d0c5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-eead01d0c5/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-e999363692/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Normed/Operator/Banach.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/pwl-decomp/Types.lean`
- `/tmp/pwl-decomp/Assembly.lean`
- `/tmp/pwl-decomp/All.lean`
- `/tmp/pwl-decomp/Layout.lean`
- `/tmp/pwl-decomp/LayoutCmp.lean`

Snapshot: project b4d606d, mathlib 25730c7c. The snapshot Contract.lean and the cited mathlib files are byte-identical to the workspace and package trees.

No existing or accepted DAG declaration has any of the seven child types. The closest node, dor_lmb_fcd_jacobian_weak_continuity, is unaccepted and states a different, Jacobian-minor result. So all seven children get fresh dor_lmbsf_pwl_* names, none used among the 1523 nodes.

Library facts that suffice, all confirmed by compilation:
- SimonGMT Chapter02: integral_area_formula_of_injective_derivative, integrableOn_image_iff_integrableOn_areaJacobian_smul, map_withDensity_areaJacobian_eq, areaJacobianAt_eq_zero_iff_not_injective, measurable_areaJacobianAt.
- Mathlib: LipschitzWith.integral_lineDeriv_mul_eq, LipschitzWith.ae_differentiableAt, MemLp.exist_eLpNorm_sub_le, Besicovitch.ae_tendsto_measure_inter_div, HasFDerivWithinAt.lim (in this version it takes dlim : d → 0), exists_contDiff_zero_iff_one_iff_of_isClosed, lipschitzWith_of_nnnorm_fderiv_le, NormedRing.inverse_continuousAt, ContinuousLinearMap.isUnit_iff_bijective, EuclideanSpace.euclideanHausdorffMeasure_eq_volume.

Lean checks:
- All seven child types validate and elaborate in the comparator scope.
- The parent assembly compiles with only standard axioms.
- All seven children are fully proven in the Submission layout with only standard axioms, and `exact Submission.X` closes each comparator challenge.
