# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1.null_off_support-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step (1d) of the parent-supplied proof of cmcsd_shell_decomposition (used there for T and, in step 2, for ∂T); Simon, Introduction to GMT, Ch. 6, proof of the deformation theorem 5.1, displays (8)–(10) (book/chapter-06.txt lines 1405–1928).
1. (The complement of the support is the open zero region.) By definition, spt X = ℝ^P \ Z with Z := X.zeroRegion, the union of all open W with compact closure (contained in ℝ^P) on which X vanishes. Hence (spt X)ᶜ = Z (the complement of univ \ Z is Z), and Z is open, being a union of open sets (GeometricCurrentOn.isOpen_zeroRegion).
2. By the hypothesis applied to the open set W := Z, μ((spt X)ᶜ) = μ(Z) = M_Z(X), and by definition M_Z(X) is the supremum of ENNReal.ofReal X(ω) over the ω ∈ 𝒟^k(ℝ^P) admissible for M_Z (tsupport ω ⊆ Z and |ω(x)| ≤ 1 for all x).
3. Let ω be admissible for M_Z. Then tsupport ω ⊆ Z = (spt X)ᶜ, so tsupport ω is disjoint from spt X (Set.disjoint_of_subset_left with disjoint_compl_left). By (VO), applied with U := ℝ^P and S := X, X(ω) = 0, hence ENNReal.ofReal X(ω) = ENNReal.ofReal 0 = 0.
4. Every element of the set whose supremum is M_Z(X) is therefore 0, so M_Z(X) ≤ 0 (sSup_le), i.e. M_Z(X) = 0. By step 2, μ((spt X)ᶜ) = 0. ∎

## Key steps

1. (spt X)ᶜ = X.zeroRegion, which is open (isOpen_zeroRegion).
2. μ((spt X)ᶜ) = M_Z(X), the supremum of ofReal X(ω) over ω admissible for Z = X.zeroRegion.
3. Every such ω has tsupport disjoint from spt X, so X(ω) = 0 by (VO).
4. The supremum is ≤ 0 (sSup_le), so μ((spt X)ᶜ) = 0.

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
