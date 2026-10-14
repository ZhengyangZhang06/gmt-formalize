# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1.chart_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 2 (“Area measure”, “The chart field”, “Chain rule”, “Area formula for Bochner integrals”, “Ŵ ∈ L¹”) and the backward use of the area formula in Step 5; Simon Ch. 2, 3.2 and (3.5). Uses the sibling left_inverse (Lean Submission.dor_lmbsf_pwl_immersion_left_inverse). Notation: A(y) := Dψ(y), and J(y) := areaJacobianAt ψ y is the metric Jacobian (J ≥ 0, Borel by measurable_areaJacobianAt).

1. Hypotheses of the area formula.
 - Y ⊆ C ⊆ V is Borel, and ψ is injective on Y.
 - ψ is differentiable at every y ∈ Y, since V is open and ψ is C¹ on V; A(y) is injective for y ∈ Y.
 - J(y) > 0 for y ∈ Y, since J(y) = 0 iff A(y) is not injective (areaJacobianAt_eq_zero_iff_not_injective).
 - On ℝ^d, μHE[d] is Lebesgue measure (EuclideanSpace.euclideanHausdorffMeasure_eq_volume), and finrank ℝ^d = d.
2. Bochner area formula (integral_area_formula_of_injective_derivative). For every g : ℝ^P → ℝ, with no measurability or integrability assumption, ∫_{ψ(Y)} g dH^d = ∫_Y J(y)·g(ψ(y)) dy.
3. Integrability transfer (integrableOn_image_iff_integrableOn_areaJacobian_smul). Since w is integrable on ψ(Y), y ↦ J(y)·w(ψ(y)) is integrable on Y.
4. Pull-back of tangency.
 - The measure form of the area formula (map_withDensity_areaJacobian_eq) states H^d⌞ψ(Y) = ψ_#((L^d⌞Y) with density J).
 - ψ is a.e.-measurable for the latter measure: it is continuous on Y, and the density measure is absolutely continuous w.r.t. L^d⌞Y. So the hypothesis on W transfers (ae_of_ae_map): for a.e. y with respect to (L^d⌞Y) with density J, the tangency predicate holds at x = ψ(y).
 - By ae_withDensity_iff, for (L^d⌞Y)-a.e. y, J(y) ≠ 0 implies the predicate at ψ(y). Since J > 0 on Y, the predicate holds at ψ(y) for L^d-a.e. y ∈ Y.
 - Taking the witness y itself gives W(ψ(y)) ∈ A(y)(ℝ^d) for L^d-a.e. y ∈ Y.
5. Chart field.
 - Let R be given by left_inverse: R is continuous on V and R(y)∘A(y) = id for y ∈ V.
 - C ⊆ V is compact and R is continuous on C, so there is M with ‖R(y)‖ ≤ M for y ∈ C (M ≥ 0 whenever C ≠ ∅).
 - Put E(y) := R(y)[W(ψ(y))]. Then |E(y)| ≤ M·c' for y ∈ Y.
 - E is a.e.-strongly measurable for L^d⌞Y: R is continuous on the Borel set V ⊇ Y, y ↦ W(ψ(y)) is a.e.-measurable on Y (W Borel, ψ continuous on V), and evaluation (T, v) ↦ T v is continuous.
6. For every y as in step 4, write W(ψ(y)) = A(y)z. Then E(y) = R(y)A(y)z = z, hence A(y)E(y) = W(ψ(y)).
7. Define Φ(y) := (J(y)·w(ψ(y)))·E(y) for y ∈ Y and Φ(y) := 0 for y ∉ Y. By steps 3 and 5, Φ is an integrable scalar times a bounded a.e.-strongly measurable field on Y. So Φ is integrable on Y, and therefore on ℝ^d. Φ = 0 off Y by definition.
8. Let β, α satisfy β(ψ(y))∘A(y) = α(y) for y ∈ Y.
 - By step 2 with g(x) := w(x)·β(x)[W(x)], ∫_{ψ(Y)} w·β[W] dH^d = ∫_Y J(y)·w(ψ(y))·β(ψ(y))[W(ψ(y))] dy.
 - For L^d-a.e. y ∈ Y, steps 4 and 6 give β(ψ(y))[W(ψ(y))] = β(ψ(y))[A(y)E(y)] = α(y)[E(y)].
 - By linearity of α(y), J(y)·w(ψ(y))·β(ψ(y))[W(ψ(y))] = α(y)[(J(y)·w(ψ(y)))·E(y)] = α(y)[Φ(y)].
 - The two integrands agree a.e. on Y, so the right-hand side equals ∫_Y α(y)[Φ(y)] dy.
9. For y ∉ Y, α(y)[Φ(y)] = α(y)[0] = 0, so ∫_Y α[Φ] dy = ∫_{ℝ^d} α[Φ] dy (setIntegral_eq_integral_of_forall_compl_eq_zero). Steps 8 and 9 prove the identity. ∎

Lean realization: compiled during decomposition with the pinned toolchain in the Submission layout, as the body of `theorem Submission.dor_lmbsf_pwl_chart_pairing_transfer : (frozen lean_statement) := by` inside `namespace GMT.Ch07`. #print axioms reports only propext, Classical.choice and Quot.sound. Extra imports: Poincare.SimonGMT.Chapter02.WeightedArea, Poincare.SimonGMT.Chapter02.AreaCritical. When rewriting with setIntegral_eq_integral_of_forall_compl_eq_zero, give `f` explicitly so that the full-space integral is the one rewritten.
```lean
  intro P d V C Y ψ w W c' hV hψ hψinj hDψ hC hCV hY hYC hw hWm hWb hWt
  obtain ⟨R, hRc, hRinv⟩ := Submission.dor_lmbsf_pwl_immersion_left_inverse P d V ψ hV hψ hDψ
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (hRc.mono hCV)
  have hYV : Y ⊆ V := hYC.trans hCV
  have hdiff : ∀ y ∈ Y, DifferentiableAt ℝ ψ y := fun y hy =>
    (hψ.differentiableOn one_ne_zero y (hYV hy)).differentiableAt (hV.mem_nhds (hYV hy))
  have hreg : ∀ y ∈ Y, Injective (fderiv ℝ ψ y) := fun y hy => hDψ y (hYV hy)
  have hinjY : InjOn ψ Y := hψinj.mono hYV
  set J : Euclid d → ℝ := Poincare.SimonGMT.Chapter02.areaJacobianAt ψ with hJdef
  -- Bochner area formula
  have harea : ∀ g : Euclid P → ℝ, ∫ x in ψ '' Y, g x ∂μHE[d] = ∫ y in Y, J y * g (ψ y) := by
    intro g
    have := Poincare.SimonGMT.Chapter02.integral_area_formula_of_injective_derivative
      hY hdiff hreg hinjY g
    simp only [finrank_euclideanSpace_fin, smul_eq_mul] at this
    rw [this, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- integrability of J * (w ∘ ψ) on Y
  have hJw : IntegrableOn (fun y => J y * w (ψ y)) Y := by
    have := Poincare.SimonGMT.Chapter02.integrableOn_image_iff_integrableOn_areaJacobian_smul
      hY hdiff hreg hinjY w
    simp only [finrank_euclideanSpace_fin, smul_eq_mul] at this
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact this.1 hw
  -- pull back the tangency condition
  have htan : ∀ᵐ y ∂(volume.restrict Y),
      W (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid d →ₗ[ℝ] Euclid P) := by
    have hmap := Poincare.SimonGMT.Chapter02.map_withDensity_areaJacobian_eq hY hdiff hreg hinjY
    simp only [finrank_euclideanSpace_fin] at hmap
    have hp := hWt
    rw [← hmap] at hp
    have hcont : ContinuousOn ψ Y := fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
    have hae : AEMeasurable ψ ((μHE[d].restrict Y).withDensity
        (fun x => ENNReal.ofReal (Poincare.SimonGMT.Chapter02.areaJacobianAt ψ x))) :=
      (hcont.aemeasurable hY).mono_ac (withDensity_absolutelyContinuous _ _)
    have h1 := ae_of_ae_map hae hp
    rw [ae_withDensity_iff
      (Poincare.SimonGMT.Chapter02.measurable_areaJacobianAt ψ).ennreal_ofReal] at h1
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h1
    filter_upwards [h1, ae_restrict_mem hY] with y hy hyY
    have hJ : Poincare.SimonGMT.Chapter02.areaJacobianAt ψ y ≠ 0 := by
      rw [Ne, Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_zero_iff_not_injective, not_not]
      exact hreg y hyY
    have hJpos : 0 < Poincare.SimonGMT.Chapter02.areaJacobianAt ψ y :=
      lt_of_le_of_ne (Poincare.SimonGMT.Chapter02.areaJacobianAt_nonneg ψ y) (Ne.symm hJ)
    exact hy (by simpa using hJpos) y hyY rfl
  -- the chart field
  set E : Euclid d → Euclid d := fun y => R y (W (ψ y)) with hEdef
  have hEm : AEStronglyMeasurable E (volume.restrict Y) := by
    have hR : AEStronglyMeasurable R (volume.restrict Y) :=
      (hRc.mono hYV).aestronglyMeasurable hY
    have hWψ : AEStronglyMeasurable (fun y => W (ψ y)) (volume.restrict Y) :=
      (hWm.comp_aemeasurable ((hψ.continuousOn.mono hYV).aemeasurable hY)).aestronglyMeasurable
    exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Euclid P) (F := Euclid d)).continuous.comp_aestronglyMeasurable
      (hR.prodMk hWψ)
  have hEb : ∀ᵐ y ∂(volume.restrict Y), ‖E y‖ ≤ M * c' := by
    filter_upwards [ae_restrict_mem hY] with y hy
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y (hYC hy))
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hM y (hYC hy)) (hWb _) (norm_nonneg _) hM0)
  set Φ : Euclid d → Euclid d := Y.indicator (fun y => (J y * w (ψ y)) • E y) with hΦdef
  have hΦi : Integrable Φ := by
    rw [hΦdef, integrable_indicator_iff hY]
    exact hJw.smul_bdd (M * c') hEm hEb
  refine ⟨Φ, hΦi, fun y hy => by simp [hΦdef, indicator_of_notMem hy], ?_⟩
  intro β α hβα
  rw [harea]
  have hcompl : ∀ y, y ∉ Y → α y (Φ y) = 0 := fun y hy => by
    simp [hΦdef, indicator_of_notMem hy]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
    (f := fun y => α y (Φ y)) hcompl]
  refine setIntegral_congr_ae hY ?_
  filter_upwards [ae_restrict_iff' hY |>.1 htan] with y hyt hyY
  obtain ⟨z, hz⟩ := hyt hyY
  have hz' : fderiv ℝ ψ y z = W (ψ y) := hz
  have hEz : E y = z := by
    have := congrArg (fun T : Euclid d →L[ℝ] Euclid d => T z) (hRinv y (hYV hyY))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
    rw [hEdef]
    simp only
    rw [← hz', this]
  have hE : fderiv ℝ ψ y (E y) = W (ψ y) := by rw [hEz, hz']
  rw [hΦdef, indicator_of_mem hyY, map_smul, ← hβα y hyY, ContinuousLinearMap.comp_apply, hE,
    smul_eq_mul]
  ring
```

## Key steps

1. Area-formula hypotheses hold on Y; J > 0 on Y; μHE[d] is Lebesgue measure on ℝ^d.
2. The Bochner area formula turns ∫_{ψ(Y)} w·β[W] into ∫_Y J·(w∘ψ)·β(ψ)[W∘ψ].
3. The measure form of the area formula and J > 0 pull the tangency of W back to a.e. y ∈ Y.
4. E := R(W∘ψ) with the left inverse R from left_inverse satisfies A·E = W∘ψ a.e. on Y and |E| ≤ M·c'.
5. Φ := 1_Y·J·(w∘ψ)·E is integrable; β(ψ)∘A = α turns the integrand into α[Φ] a.e. on Y, and Φ = 0 off Y.

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
