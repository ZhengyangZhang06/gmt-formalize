# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1.cutoff_deriv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 4(b)–(c): the chain rule away from the kinks and the agreement lemma on the kink levels. On Z the function u is compared directly with γ∘F, so the parent's intermediate identity D(f∘ψ) = DF is not needed. Uses the sibling eqon_deriv (Lean Submission.dor_lmbsf_pwl_fderiv_eq_ae_of_eqOn), to which (DD) is passed.

1. Rademacher: u is differentiable at L^d-a.e. y (LipschitzWith.ae_differentiableAt).
2. Local form of γ (b − a > 0).
 - If s < a, then (b − s)/(b − a) > 1 and γ(s) = 1.
 - If a < s < b, then 0 < (b − s)/(b − a) < 1 and γ(s) = (b − s)/(b − a).
 - If s > b, then (b − s)/(b − a) < 0 and γ(s) = 0.
 - Moreover γ(a) = 1 and γ(b) = 0.
3. Decomposition. Z = Z₀ ∪ Z_a ∪ Z_b, where Z₀ := Z ∩ {F ≠ a} ∩ {F ≠ b}, Z_a := Z ∩ F⁻¹(a) and Z_b := Z ∩ F⁻¹(b). F is continuous, so all three sets are Borel.
4. Kink levels. On Z_a, u = γ(a) = 1. Apply eqon_deriv to Z_a, v₁ = u and the constant v₂ ≡ 1, which is differentiable everywhere with derivative 0. For a.e. y ∈ Z_a at which u is differentiable, this gives Du(y) = 0. Since F(y) = a ∉ (a, b), γ'(F(y)) = 0, so Du(y) = 0 = γ'(F(y))DF(y). The same argument with v₂ ≡ 0 = γ(b) handles Z_b.
5. Away from the kinks. Let g := γ∘F and let F(y) ∉ {a, b}.
 - By continuity of F, for z near y the value F(z) lies in the same one of the open sets (−∞, a), (a, b), (b, ∞) as F(y).
 - By step 2, near y either g ≡ 1, or g(z) = (b − F(z))/(b − a), or g ≡ 0.
 - So g is differentiable at y with Dg(y) = 0, −(b − a)⁻¹DF(y) and 0 respectively, i.e. Dg(y) = γ'(F(y))DF(y). (A function eventually equal near y to a differentiable function has the same derivative at y.)
 - u = g on Z₀ ⊆ Z, so eqon_deriv applied to Z₀, v₁ = u, v₂ = g gives Du(y) = Dg(y) = γ'(F(y))DF(y) for a.e. y ∈ Z₀ at which u is differentiable.
6. Intersect the full-measure sets of steps 1, 4 (for a and for b) and 5. For y ∈ Z in the intersection, exactly one of F(y) = a, F(y) = b, F(y) ∉ {a, b} holds, and in each case Du(y) = γ'(F(y))DF(y). ∎

Lean realization: compiled during decomposition with the pinned toolchain in the Submission layout, as the body of `theorem Submission.dor_lmbsf_pwl_fderiv_cutoff_comp_ae : (frozen lean_statement) := by` inside `namespace GMT.Ch07`. #print axioms reports only propext, Classical.choice and Quot.sound. Extra imports: Mathlib.Analysis.Calculus.Rademacher.
```lean
  intro hDD d Z F u K a b hZ hF hu hab hEq
  have hFc : Continuous F := hF.continuous
  have hba : 0 < b - a := sub_pos.2 hab
  set g : Euclid d → ℝ := fun y => min 1 (max 0 ((b - F y) / (b - a))) with hgdef
  have hZ0 : MeasurableSet (Z ∩ {y | F y ≠ a ∧ F y ≠ b}) := by
    refine hZ.inter ?_
    have h1 : MeasurableSet {y | F y ≠ a} :=
      (measurableSet_singleton a).compl.preimage hFc.measurable
    have h2 : MeasurableSet {y | F y ≠ b} :=
      (measurableSet_singleton b).compl.preimage hFc.measurable
    exact h1.inter h2
  have hZa : MeasurableSet (Z ∩ F ⁻¹' {a}) :=
    hZ.inter ((measurableSet_singleton a).preimage hFc.measurable)
  have hZb : MeasurableSet (Z ∩ F ⁻¹' {b}) :=
    hZ.inter ((measurableSet_singleton b).preimage hFc.measurable)
  have hdiff : ∀ᵐ y ∂(volume : Measure (Euclid d)), DifferentiableAt ℝ u y :=
    hu.ae_differentiableAt
  have h0 := Submission.dor_lmbsf_pwl_fderiv_eq_ae_of_eqOn hDD d (Z ∩ {y | F y ≠ a ∧ F y ≠ b}) u g hZ0 (fun y hy => hEq y hy.1)
  have ha := Submission.dor_lmbsf_pwl_fderiv_eq_ae_of_eqOn hDD d (Z ∩ F ⁻¹' {a}) u (fun _ => 1) hZa (by
    intro y hy
    have hFy : F y = a := hy.2
    simp only [hEq y hy.1, hFy, sub_self, zero_div, div_self hba.ne']
    simp)
  have hb := Submission.dor_lmbsf_pwl_fderiv_eq_ae_of_eqOn hDD d (Z ∩ F ⁻¹' {b}) u (fun _ => 0) hZb (by
    intro y hy
    have hFy : F y = b := hy.2
    simp only [hEq y hy.1, hFy, sub_self, zero_div]
    simp)
  filter_upwards [hdiff, h0, ha, hb] with y hyd hy0 hya hyb hyZ
  by_cases hFa : F y = a
  · have h := hya ⟨hyZ, hFa⟩ hyd (differentiableAt_const _)
    rw [h, fderiv_const_apply]
    simp [hFa]
  by_cases hFb : F y = b
  · have h := hyb ⟨hyZ, hFb⟩ hyd (differentiableAt_const _)
    rw [h, fderiv_const_apply]
    simp [hFb]
  have hgd : HasFDerivAt g ((if a < F y ∧ F y < b then -(b - a)⁻¹ else 0) • fderiv ℝ F y) y := by
    have hFd : HasFDerivAt F (fderiv ℝ F y) y := (hF y).hasFDerivAt
    rcases lt_or_gt_of_ne hFa with h | h
    · -- F y < a : g = 1 near y
      have hev : g =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
        filter_upwards [hFc.continuousAt.eventually (gt_mem_nhds h)] with z hz
        have : 1 < (b - F z) / (b - a) := by
          rw [one_lt_div hba]; linarith
        simp only [hgdef]
        rw [max_eq_right (by linarith), min_eq_left this.le]
      have hn : ¬ (a < F y ∧ F y < b) := fun h' => absurd h'.1 (not_lt.2 h.le)
      simp only [hn, ite_false, zero_smul]
      exact (hasFDerivAt_const (1 : ℝ) y).congr_of_eventuallyEq hev
    · rcases lt_or_gt_of_ne hFb with h' | h'
      · -- a < F y < b : g = (b - F)/(b - a) near y
        have hev : g =ᶠ[𝓝 y] fun z => (b - F z) / (b - a) := by
          filter_upwards [hFc.continuousAt.eventually (lt_mem_nhds h),
            hFc.continuousAt.eventually (gt_mem_nhds h')] with z hz1 hz2
          have hpos : 0 < (b - F z) / (b - a) := div_pos (by linarith) hba
          have hlt : (b - F z) / (b - a) < 1 := by
            rw [div_lt_one hba]; linarith
          simp only [hgdef]
          rw [max_eq_right hpos.le, min_eq_right hlt.le]
        have hy' : a < F y ∧ F y < b := ⟨h, h'⟩
        simp only [hy', and_self, ite_true]
        have hlin : HasFDerivAt (fun z => (b - F z) / (b - a))
            (-(b - a)⁻¹ • fderiv ℝ F y) y := by
          have := ((hasFDerivAt_const b y).sub hFd).const_mul (b - a)⁻¹
          convert this using 1
          · funext z
            simp only [Pi.sub_apply]
            rw [div_eq_inv_mul]
          · rw [zero_sub, smul_neg, neg_smul]
        exact hlin.congr_of_eventuallyEq hev
      · -- F y > b : g = 0 near y
        have hev : g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
          filter_upwards [hFc.continuousAt.eventually (lt_mem_nhds h')] with z hz
          have : (b - F z) / (b - a) < 0 := div_neg_of_neg_of_pos (by linarith) hba
          simp only [hgdef]
          rw [max_eq_left this.le]
          simp
        have hn : ¬ (a < F y ∧ F y < b) := fun h'' => absurd h''.2 (not_lt.2 h'.le)
        simp only [hn, ite_false, zero_smul]
        exact (hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq hev
  have h := hy0 ⟨hyZ, hFa, hFb⟩ hyd hgd.differentiableAt
  rw [h, hgd.fderiv]
```

## Key steps

1. Rademacher: u is differentiable a.e.
2. Split Z into the Borel pieces F = a, F = b and F ∉ {a, b}.
3. On the kink levels u is constant; eqon_deriv with a constant gives Du = 0 = γ'(F)DF.
4. Off the kinks γ∘F is locally 1, (b − F)/(b − a) or 0, hence differentiable with derivative γ'(F)DF; eqon_deriv with v₂ = γ∘F concludes.

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
