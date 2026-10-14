# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1.dyadic_radii-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent-supplied proof of cmcsd_shell_decomposition, with the density estimates of its steps 11(b) and 13(iii); Simon, Introduction to GMT, Ch. 6, proof of the deformation theorem 5.1, displays (8)–(10) (book/chapter-06.txt lines 1405–1928) (display (10): ρ ∈ (σ/2, σ) with M⟨T, d, ρ⟩ ≤ (c/σ)·M(T_σ − T_{σ/2})).
1. Put ρ_j := (1/2)^{j+2}. Then ρ_j > 0, ρ_j ≤ (1/2)^2 = 1/4 (pow_le_pow_of_le_one, since j + 2 ≥ 2) and ρ_j/2 = (1/2)^{j+3} (pow_succ).
2. (Choice of r_j; (i) and (vi).) Fix j and put B_j := C·ofReal(ρ_j^{m+2})·M. By the hypothesis with r := ρ_j, μ({d < ρ_j}) ≤ B_j. GR, applied with μ, μ′ (finite), f := d (measurable), ρ := ρ_j > 0 and B := B_j, gives r_j with ρ_j/2 < r_j < ρ_j, liminf_{h→0+} ofReal(h⁻¹)·μ({r_j − h < d < r_j}) ≤ ofReal(4/ρ_j)·B_j and liminf_{h→0+} ofReal(h⁻¹)·μ′({r_j − h < d < r_j}) < ∞. Choose such an r_j for every j (axiom of choice). By step 1 this gives (i), and (vi) holds.
3. ((ii).) For every j, r_{j+1} < (1/2)^{j+3} < r_j by (i) (applied to j + 1 and to j). Hence r is strictly decreasing (strictAnti_nat_of_succ_lt).
4. ((iii).) Since r_j < ρ_j, {d < r_j} ⊆ {d < ρ_j}, so μ({d < r_j}) ≤ μ({d < ρ_j}) ≤ C·ofReal(ρ_j^{m+2})·M by the hypothesis with r := ρ_j, and ρ_j^{m+2} = ((1/2)^{j+2})^{m+2} = (1/2)^{(j+2)(m+2)} (pow_mul). The same argument with μ′ and M′ gives the second inequality.
5. ((iv).) Since (j + 2)(m + 2) ≥ j → ∞ and (1/2)^n → 0 (tendsto_pow_atTop_nhds_zero_of_lt_one), (1/2)^{(j+2)(m+2)} → 0, hence ofReal((1/2)^{(j+2)(m+2)}) → ofReal 0 = 0 (ENNReal.tendsto_ofReal). As C ≠ ∞ and M ≠ ∞, C·ofReal((1/2)^{(j+2)(m+2)})·M → C·0·M = 0 (ENNReal.Tendsto.const_mul, ENNReal.Tendsto.mul_const). By (iii), 0 ≤ μ({d < r_j}) ≤ C·ofReal((1/2)^{(j+2)(m+2)})·M, so μ({d < r_j}) → 0 (tendsto_of_tendsto_of_tendsto_of_le_of_le). The same argument with μ′ and M′ ≠ ∞ gives μ′({d < r_j}) → 0.
6. ((v).) For ρ > 0 we have (4/ρ)·ρ^{m+2} = 4ρ^{m+1}, hence ofReal(4/ρ)·ofReal(ρ^{m+2}) = ofReal(4ρ^{m+1}) = 4·ofReal(ρ^{m+1}) (ENNReal.ofReal_mul with 4/ρ ≥ 0 and with 4 ≥ 0; ENNReal.ofReal_ofNat). Using commutativity and associativity of multiplication in [0, ∞], ofReal(4/ρ_j)·B_j = C·(ofReal(4/ρ_j)·ofReal(ρ_j^{m+2}))·M = 4·C·ofReal(ρ_j^{m+1})·M, and ρ_j^{m+1} = (1/2)^{(j+2)(m+1)} (pow_mul). With the liminf bound of step 2 this gives (v). ∎

## Key steps

1. ρ_j = (1/2)^{j+2} ∈ (0, 1/4] and ρ_j/2 = (1/2)^{j+3}.
2. GR with B_j = C·ofReal(ρ_j^{m+2})·M (density hypothesis at ρ_j) gives r_j ∈ (ρ_j/2, ρ_j) with both liminf bounds; choose for all j.
3. r_{j+1} < (1/2)^{j+3} < r_j, so r is strictly decreasing.
4. μ({d < r_j}) ≤ μ({d < ρ_j}) ≤ C·ofReal((1/2)^{(j+2)(m+2)})·M (pow_mul), and the same for μ′; this bound tends to 0.
5. ofReal(4/ρ)·ofReal(ρ^{m+2}) = 4·ofReal(ρ^{m+1}) turns the GR bound into 4·C·ofReal((1/2)^{(j+2)(m+1)})·M.

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
