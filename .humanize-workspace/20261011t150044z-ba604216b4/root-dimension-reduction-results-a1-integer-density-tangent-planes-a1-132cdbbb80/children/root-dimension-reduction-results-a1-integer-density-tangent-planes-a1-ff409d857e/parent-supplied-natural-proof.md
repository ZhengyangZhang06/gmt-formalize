# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1.normalized_bump-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Context: Mathlib's normalized bump API (ContDiffBump.normed, ContDiffBump.integral_normed) is not in the import closure of GMT/Ch07/Submission.lean, so the bump is built by hand. This exact construction was kernel-checked during the decomposition review.
1. Let σ := Real.smoothTransition. Then σ is C^∞ (Real.smoothTransition.contDiff), 0 ≤ σ ≤ 1 (Real.smoothTransition.nonneg, Real.smoothTransition.le_one), σ(x) = 0 for x ≤ 0 (zero_of_nonpos) and σ(x) = 1 for x ≥ 1 (one_of_one_le).
2. Put m := (c + d)/2, ρ := (d − c)/2 > 0, p := m − ρ/2 and q := m + ρ/2, so that c < p < q < d. Define θ(α) := σ((4/ρ)(α − p)) · σ((4/ρ)(q − α)). Each factor is σ composed with an affine map, so θ is C^∞, in particular C¹. Also θ ≥ 0.
3. If α < p then (4/ρ)(α − p) ≤ 0, so the first factor is 0. If α > q then (4/ρ)(q − α) ≤ 0, so the second factor is 0. Hence support θ ⊆ [p, q]. Since [p, q] is closed, tsupport θ ⊆ [p, q] ⊆ (c, d). In particular tsupport θ is a closed subset of the compact interval [c, d], so θ has compact support.
4. At α = m both arguments equal (4/ρ)(ρ/2) = 2 ≥ 1, so θ(m) = 1 ≠ 0.
5. θ is continuous, compactly supported, nonnegative and not identically zero. Hence I_θ := ∫_ℝ θ > 0 (Mathlib Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero).
6. Let χ := I_θ⁻¹ · θ. Then χ is C¹, being a constant times a C¹ function. Also tsupport χ ⊆ tsupport θ ⊆ (c, d) (tsupport_mul_subset_right). Finally ∫ χ = I_θ⁻¹ · I_θ = 1 (integral_const_mul). ∎

## Key steps

1. Build θ(α) = σ((4/ρ)(α − p))·σ((4/ρ)(q − α)) from σ = Real.smoothTransition, with c < p < q < d.
2. θ is C^∞ and ≥ 0, and vanishes off [p, q], so tsupport θ ⊆ (c, d); also θ((c+d)/2) = 1.
3. ∫θ > 0, since θ is continuous, compactly supported, nonnegative and nonzero.
4. Normalize: χ := (∫θ)⁻¹·θ is C¹, keeps the support, and has ∫χ = 1.

## Reference use

### local-project

Queries:
- `lake env lean probe after `import GMT.Ch07.Submission`: #check @Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero, @ContinuousMap.instSeparableSpace, @ContDiffBump.integral_normed, @exists_polynomial_near_continuousMap, @ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints, @MeasureTheory.Lp.secondCountableTopology, (inferInstance : Denumerable ℚ) -> all unknown / not synthesizable`
- `lake env lean probe after `import GMT.Ch07.Submission`: #check @IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero, @integral_prod, @setIntegral_prod_mul, @Measure.ae_prod_iff_ae_ae, @Measure.ae_ae_of_ae_prod, @Measure.quasiMeasurePreserving_fst, @Measure.integral_comp_mul_left, @Integrable.comp_mul_left', @Real.volume_preimage_mul_left, @IsUnifLocDoublingMeasure.ae_tendsto_average plus `example : IsUnifLocDoublingMeasure (volume : Measure ℝ) := inferInstance`, @Measure.ext_of_Ioc_finite, @intervalIntegral.continuous_primitive, @intervalIntegral.integral_hasDerivAt_right, @Real.smoothTransition.contDiff/zero_of_nonpos/one_of_one_le/nonneg/le_one, @Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero, @exists_surjective_nat, @tendsto_integral_of_dominated_convergence, @AEStronglyMeasurable.mk, @StronglyMeasurable.integral_prod_right', @IsCompact.sInf_mem, @tsupport_sub, @Integrable.bdd_mul, @HasCompactSupport.exists_bound_of_continuous -> all available`
- `rg -n 'idtp_cse|du Bois|Bois-Reymond|ae_eq_const_of_weak|SimonGMT.Chapter08' local-references/123e8435b4a2469b/project (no hit in GMT/Ch07; only the unrelated Ch08 contract imports Chapter08)`
- `rg -n 'theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero|theorem integral_comp_mul_left |theorem ae_tendsto_average|theorem ext_of_Ioc_finite|theorem continuous_primitive|theorem integral_hasDerivAt_right|theorem setIntegral_prod_mul|theorem ae_prod_iff_ae_ae|theorem quasiMeasurePreserving_fst|theorem volume_preimage_mul_left|theorem Integrable.comp_mul_left|theorem Integrable.bdd_mul ' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `diff -q local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean GMT/Ch07/Submission.lean (identical)`
- `python3 scan of dag.json lean_name values for the nine proposed idtp_cse_ah_* names (no match); grep -rl idtp_cse_ah nodes decomposition-reopenings operator-dependency-edits dag.json issue-workers.json (no match)`
- `python3 scan of dag.json statements for related analytic nodes (deriv ψ, ae_eq_const, homogeneous, distributional, fundamental lemma): codim1_rdo_dg_hr_ae_translate_invariant, dgcr_smooth_tests_to_C1_tests, idtp_pc_constancy_reduction, dorag_ha_weyl_lemma, imsupp_measure_eq_zero_of_vanishesOn (none has a Lean type reusable here)`
- `git show c1d608481329bbb6de1c0f4e4052367b8d92d742:GMT/Ch07/Submission.lean and git show 1d65cf6d4d473fe727cd0ad43b45f3adfea87280:GMT/Ch07/Submission.lean (accepted node proofs are appended under the unchanged frozen import header)`
- `lake env lean /tmp/ah-decomp/final/Stmts.lean (all nine Submission.idtp_cse_ah_* types elaborate in namespace GMT.Ch07 with the frozen opens; only sorry warnings)`
- `lake env lean /tmp/ah-decomp/final/Checks.lean (check_parent_assembly, check_slice_ae_const_assembly, check_normalized_bump, check_product_integral_reduce; #print axioms: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-132cdbbb80/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-132cdbbb80/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/tmp/ah-decomp/final/stmts.json`
- `/tmp/ah-decomp/final/Stmts.lean`
- `/tmp/ah-decomp/final/Checks.lean`

The snapshot Submission.lean is byte-identical to the workspace compiler authority (mathlib 25730c7c, SimonGMT 2b36630), and accepted node proofs are appended to it without import changes. Two results cited by the supplied proof are not in that import closure: SimonGMT Chapter08 ae_eq_const_of_weak_coordinate_derivatives_zero and Mathlib ContinuousMap.instSeparableSpace (likewise ContDiffBump.integral_normed). The children therefore use routes that are available: the fundamental lemma, Fubini/Tonelli, dominated convergence, IsUnifLocDoublingMeasure.ae_tendsto_average (the instance exists for volume on ℝ), interval-integral FTC, Real.smoothTransition, change of variables and exists_surjective_nat. No DAG node, run record or snapshot file uses the idtp_cse_ah_ prefix, and no existing DAG declaration has a reusable identical type. All nine child types elaborate. The parent's frozen type is kernel-checked from six of the children, and slice_ae_const is kernel-checked from its four siblings. normalized_bump and product_integral_reduce are fully proved. All of these use only propext, Classical.choice and Quot.sound.
