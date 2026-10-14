# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1.slice_boundary_mass-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 12(b) of the parent-supplied proof of cmcsd_shell_decomposition (the second slicing, applied there to ∂T, μ_∂, ξ_∂, f = d, L = 1, t = r_j and W = ℝ^P); Simon, Introduction to GMT, Ch. 6, proof of the deformation theorem 5.1, displays (8)–(10) (book/chapter-06.txt lines 1405–1928).
1. (m = 0.) For a current of degree 0, boundaryMassOn B W = 0 by definition, and 0 ≤ anything in [0, ∞].
2. (m = k + 1: the data for (SL).) Now boundaryMassOn B W = M_W(∂B) by definition. Apply (SL) with k, U, the current T′ := ∂T ∈ 𝒟_{k+1}(U), the measures μ and μ′ := 0 (the zero measure), ξ and ξ′ := 0 (the zero map ℝ^P → Λ_k), f and L. Its hypotheses hold: U is open; μ is finite on compact subsets of U and so is 0; ξ is μ-a.e. strongly measurable and the zero map is a.e. strongly measurable for the zero measure (aestronglyMeasurable_zero_measure); the bound for ξ holds μ-a.e., and every property holds a.e. for the zero measure (ae_zero); T′(η) = ∂T(η) = ∫ ξ(x)(η(x)) dμ(x) for every η ∈ 𝒟^{k+1}(U) by hypothesis; ∂T′ = ∂∂T = 0 (GeometricCurrentOn.boundary_boundary), so ∂T′(ζ) = 0 = ∫ 0 d0 (integral_zero_measure) for every ζ ∈ 𝒟^k(U); and f is L-Lipschitz.
3. (SL) gives A′ : ℝ → 𝒟_{k+1}(U) and B′ : ℝ → 𝒟_k(U) with (SL1) A′_t(η) = ∫_{f<t} ξ(x)(η(x)) dμ(x), (SL2) B′_t(ζ) = ∫_{f<t} 0(x)(ζ(x)) d0(x) = 0, and (SL4) M_W(∂A′_t − B′_t) ≤ L·liminf_{h→0+} ofReal(h⁻¹)·μ(W ∩ {t − h < f < t}) for the open set W.
4. By (SL1) and the hypothesis on B, A′_t(η) = B(η) for every η, so A′_t = B (GeometricCurrentOn.ext). By (SL2), B′_t(ζ) = 0 for every ζ, so B′_t = 0. Hence ∂A′_t − B′_t = ∂B − 0 = ∂B (ext: (∂B − 0)(ζ) = ∂B(ζ) − 0 = ∂B(ζ)).
5. Therefore boundaryMassOn B W = M_W(∂B) = M_W(∂A′_t − B′_t) ≤ L·liminf_{h→0+} ofReal(h⁻¹)·μ(W ∩ {t − h < f < t}). ∎

## Key steps

1. m = 0: boundaryMassOn B W = 0.
2. m = k + 1: apply (SL) to ∂T with (μ, ξ) and the zero measure and zero orientation for ∂∂T = 0.
3. (SL1), (SL2) give A′_t = B and B′_t = 0, so ∂A′_t − B′_t = ∂B.
4. (SL4) bounds M_W(∂B) = boundaryMassOn B W by L·liminf h⁻¹ μ(W ∩ {t − h < f < t}).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD = 25730c7c759d108ef87ab70af2342a196760f79d (matches manifest)`
- `rg -n 'cmcsd_sh_|shell_series|dyadic_good_radii' project mathlib/Mathlib (no match); python3 -I scan of runs/20261011T150044Z-ba604216b4/dag.json lean_name values: none starts with cmcsd_sh except the selected cmcsd_shell_decomposition`
- `rg -n 'def boundaryMassOn|instance : Sub \(GeometricCurrentOn|def IMRep.measure|def IsIntegerMultiplicity' project/GMT/Ch07/Contract.lean`
- `rg -n '^theorem (setIntegral_sdiff|integral_add_compl|Summable.hasSum_iff_tendsto_nat|ENNReal.summable_toReal|Summable.of_norm_bounded|strictAnti_nat_of_succ_lt|Integrable.of_bound|integral_eq_zero_of_ae|Continuous.bounded_above_of_compact_support|measure_eq_zero_iff_ae_notMem|image_eq_zero_of_notMem_tsupport|ENNReal.Tendsto.mul_const|ENNReal.Tendsto.const_mul|squeeze_zero_norm|integral_zero_measure|isBoundedBilinearMap_apply|ae_restrict_of_ae|ae_restrict_mem|tendsto_add_atTop_iff_nat|measure_iUnion)\b' mathlib/Mathlib`
- `rg -n 'theorem _root_.Continuous.comp_aestronglyMeasurable₂|theorem continuous_eval_const|theorem aestronglyMeasurable_zero_measure|theorem setIntegral_univ' mathlib/Mathlib; rg -n 'clm_apply' mathlib/Mathlib/MeasureTheory (AEStronglyMeasurable.clm_apply does not exist; Continuous.comp_aestronglyMeasurable₂ with isBoundedBilinearMap_apply used instead)`
- `grep -n 'def GeometricCurrentOn.support|def GeometricCurrentOn.zeroRegion|theorem GeometricCurrentOn.isOpen_zeroRegion|theorem GeometricCurrentOn.boundary_boundary|def GeometricCurrentOn.mass|def GeometricCurrentOn.massOn|theorem GeometricCurrentOn.massOn_mono' over lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,CurrentLocalEquality,Mass}.lean`
- `python3 -I extraction from dag.json of the frozen types of dtc_vanish_off_support, cmc_massOn_eq_imRep_measure, cmc_exists_massRepresentation, cmc_imRep_locality_restrict_sub, cmc_slice_mass_bounds (each verified to occur verbatim as an antecedent of the selected type), cmcsd_support_calculus, cmcsd_massOn_le_measure_inter, cmcsd_good_radius (status decomposing) and the accepted lcmp_imRep_measure_restrict, cmc_fc_cs_massOn_sub_le, cmr_abs_apply_le_massOn`
- `lean Types.lean (13 stubs elaborate); lean AssemblyAx.lean (selected type from child and dependency axioms); lean ReusedCheck.lean (accepted commits ae810e9b, ea5c1199, 7a706164 recompile with standard axioms, types identical to dag.json); lean EndToEnd.lean (all seven children proved with standard axioms; selected type additionally uses only cmcsd_good_radius, cmcsd_massOn_le_measure_inter, cmcsd_support_calculus)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Monotone/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_shell_decomposition_split/Types.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_shell_decomposition_split/AssemblyAx.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_shell_decomposition_split/EndToEnd.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_shell_decomposition_split/ReusedCheck.lean`

The snapshot matches the manifest: project b4d606d with an unchanged Contract.lean, identical to Submission.lean, and Mathlib 25730c7c. It contains no declaration with the cmcsd_sh_ prefix, and the DAG has none either, so the seven new names are globally unique. The contract fixes the definitions the children rely on: boundaryMassOn (0 in degree 0), the definitional Sub instance, IMRep.measure and IsIntegerMultiplicity. SimonGMT supplies support = U \ zeroRegion, isOpen_zeroRegion, boundary_boundary, mass = massOn U and massOn_mono. Mathlib supplies every tool the child proofs cite (setIntegral_sdiff, integral_add_compl, Summable.hasSum_iff_tendsto_nat, ENNReal.summable_toReal, Continuous.comp_aestronglyMeasurable₂, isBoundedBilinearMap_apply, measure_eq_zero_iff_ae_notMem, among others). AEStronglyMeasurable.clm_apply does not exist, so the proofs avoid it. The three reused accepted declarations have frozen types identical to the DAG and recompile with standard axioms. The five antecedents of the selected type are exactly the frozen types of VO, MR, REP, IMC and SL. The scratch files check, in Lean, that the seven new children are provable and that they imply the selected frozen type.
