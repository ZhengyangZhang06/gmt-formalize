# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1.im_mass_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 8 of the parent-supplied proof of cmcsd_shell_decomposition (the mass measure μ_T := R.measure and the integrality of the shells W_j); Simon, Introduction to GMT, Ch. 6, proof of the deformation theorem 5.1, displays (8)–(10) (book/chapter-06.txt lines 1405–1928). Siblings used: null_off_support (cmcsd_sh_measure_compl_support_eq_zero) and IR = imrep_restriction (lcmp_imRep_measure_restrict: for every IMRep R in U, (a) R.measure ≪ Hⁿ⌞R.carrier, (b) R.orient is R.measure-a.e. strongly measurable, (c) for every Borel E and every IMRep R′ in U with R′.carrier = R.carrier ∩ E, R′.mult = R.mult and R′.orient = R.orient: R′.measure = R.measure⌞E and R′.action ω = ∫_E R.orient(x)(ω(x)) dR.measure(x) for every form ω).
1. Since T is integer multiplicity, choose an IMRep R in ℝ^P (U = univ) representing T: T(ω) = R.action ω for every ω ∈ 𝒟ⁿ(ℝ^P). Put μ := R.measure and ξ := R.orient.
2. ((5) and (1).) ℝ^P is open, so (MR) with U := ℝ^P gives M_W(T) = μ(W) for every open W, which is (5). For W := ℝ^P this gives μ(ℝ^P) = M_{ℝ^P}(T) = M(T) < ∞ (T.mass is by definition T.massOn univ), so μ is a finite measure (IsFiniteMeasure.mk), which is (1).
3. ((2) and (3).) By IR (b), ξ = R.orient is μ-a.e. strongly measurable, which is (2). By (IMC)(d), for Hⁿ⌞R.carrier-a.e. x we have |ξ(x)(α)| ≤ |α| for every n-covector α. By IR (a), μ ≪ Hⁿ⌞R.carrier, so every property holding Hⁿ⌞R.carrier-a.e. holds μ-a.e. (Measure.AbsolutelyContinuous.ae_le); this is (3).
4. ((4).) Apply IR (c) with the Borel set E := ℝ^P and R′ := R; its hypotheses R.carrier = R.carrier ∩ ℝ^P (Set.inter_univ), R.mult = R.mult and R.orient = R.orient hold. It gives R.action ω = ∫_{ℝ^P} ξ(x)(ω(x)) dμ(x) = ∫ ξ(x)(ω(x)) dμ(x) (setIntegral_univ) for every form ω. Since R represents T, T(ω) = R.action ω = ∫ ξ(x)(ω(x)) dμ(x) for every ω ∈ 𝒟ⁿ(ℝ^P), which is (4).
5. ((6).) By step 2, M_W(T) = μ(W) for every open W, so the sibling null_off_support, applied with (VO), X := T and μ, gives μ(ℝ^P \ spt T) = 0, which is (6).
6. ((7).) Let E be Borel and X ∈ 𝒟_n(ℝ^P) with X(ω) = ∫_E ξ(x)(ω(x)) dμ(x) for all ω ∈ 𝒟ⁿ(ℝ^P). By (IMC)(b) with U := ℝ^P (open), R and E there are A ∈ 𝒟_n(ℝ^P) and an IMRep R′ with R′.carrier = R.carrier ∩ E, R′.mult = R.mult and R′.orient = R.orient (that R′ represents A is not needed). By IR (c) applied to E and R′, R′.action ω = ∫_E R.orient(x)(ω(x)) dR.measure(x) = ∫_E ξ(x)(ω(x)) dμ(x) = X(ω) for every ω ∈ 𝒟ⁿ(ℝ^P). Hence R′ represents X, and X is integer multiplicity.
7. Steps 2–6 show that μ and ξ have properties (1)–(7). ∎

## Key steps

1. Choose an IMRep R of T; μ := R.measure, ξ := R.orient.
2. (MR) gives M_W(T) = μ(W) for open W, hence μ(ℝ^P) = M(T) < ∞ and μ is finite.
3. IR (a), (b) and (IMC)(d) give a.e. strong measurability of ξ and the μ-a.e. bound |ξ(x)(α)| ≤ |α|.
4. IR (c) with E = ℝ^P, R′ = R gives T(ω) = ∫ ξ(ω) dμ.
5. null_off_support with (VO) gives μ(ℝ^P \ spt T) = 0.
6. (IMC)(b) gives an IMRep R′ with carrier R.carrier ∩ E; IR (c) shows R′.action = ∫_E ξ(ω) dμ = X(ω), so X is IM.

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
