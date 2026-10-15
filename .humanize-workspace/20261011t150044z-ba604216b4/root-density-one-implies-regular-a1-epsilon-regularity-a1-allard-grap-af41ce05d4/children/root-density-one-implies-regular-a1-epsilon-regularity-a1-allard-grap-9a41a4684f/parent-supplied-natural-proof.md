# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.l2_subseq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 5 (extraction in the complete space L²).

1. Let 𝓛 := Lp ℝ 2 μ, a complete metric space (instance Lp.instCompleteSpace). Let F_j := (MemLp.toLp) f_j ∈ 𝓛.

2. (Norm identity.) For h with MemLp h 2 μ: ‖toLp h‖² = ∫ h² dμ. Indeed:
- ‖toLp h‖ = (eLpNorm h 2 μ).toReal (Lp.norm_toLp);
- eLpNorm h 2 μ = ofReal((∫|h|²)^{1/2}) (MemLp.eLpNorm_eq_integral_rpow_norm);
- so ‖toLp h‖ = (∫ h²)^{1/2} with ∫ h² ≥ 0 (ENNReal.toReal_ofReal, Real.rpow_inv_natCast_pow, Real.rpow_natCast, sq_abs).
Since F_j − F_k = toLp(f_j − f_k) (MemLp.toLp_sub), we get dist(F_j, F_k)² = ∫ (f_j − f_k)² dμ.

3. (Total boundedness.) Let ε > 0 and apply the hypothesis with η := ε²/2. This gives a finite S such that every j has some k ∈ S with dist(F_j, F_k)² ≤ ε²/2 < ε², hence dist(F_j, F_k) < ε (lt_of_pow_lt_pow_left₀). So range F ⊆ ⋃_{k∈S} ball(F_k, ε), a finite union, and range F is totally bounded (Metric.totallyBounded_iff).

4. (Compactness.) closure(range F) is totally bounded (TotallyBounded.closure) and closed in the complete space 𝓛, hence compact (TotallyBounded.isCompact_of_isClosed).

5. (Extraction.) IsCompact.tendsto_subseq, applied to F_j ∈ closure(range F), gives G ∈ 𝓛 and a strictly increasing φ with F_{φ(j)} → G.

6. Let W := ⇑G, a representative of G; then MemLp W 2 μ (Lp.memLp G). The function f_{φ(j)} − W is in L² and its class is F_{φ(j)} − G (MemLp.toLp_sub, Lp.toLp_coeFn). By step 2, ∫ (f_{φ(j)} − W)² dμ = ‖F_{φ(j)} − G‖². Since ‖F_{φ(j)} − G‖ → 0 (tendsto_iff_norm_sub_tendsto_zero), its square tends to 0 (Tendsto.pow). ∎

Validation note (not part of the argument): a kernel-checked Lean proof of this exact frozen statement was compiled during decomposition review as Submission.dorag_ha_rb_l2_subseq in /tmp/rellich-validate/Full/Full.lean (axioms propext, Classical.choice, Quot.sound). That scratch file may not persist.

## Key steps

1. In Lp ℝ 2 μ, ‖toLp h‖² = ∫ h², so dist(F_j, F_k)² = ∫ (f_j − f_k)².
2. The finite-net hypothesis with η = ε²/2 makes {F_j} totally bounded.
3. The closure is compact in the complete space Lp, so IsCompact.tendsto_subseq yields F_{φ(j)} → G.
4. W := ⇑G is in L² and ∫ (f_{φ(j)} − W)² = ‖F_{φ(j)} − G‖² → 0.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `grep -n 'absolutelyContinuousOnInterval\|integral_deriv_eq_sub' <snapshot>/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
- `lake env lean /tmp/rellich-decomp/Names.lean (#check after import GMT.Ch07.Submission of LipschitzWith.ae_differentiableAt, measurableSet_of_differentiableAt, Measure.ae_ae_comm, Measure.addHaar_preimage_smul, Measure.integral_comp_smul_of_nonneg, Measure.setIntegral_comp_smul_of_pos, TotallyBounded.isCompact_of_isClosed, IsCompact.tendsto_subseq, Lp.instCompleteSpace, measurable_fderiv, norm_fderiv_le_of_lipschitz, integral_sub_left_eq_self, finite_approx_of_totallyBounded, MemLp.toLp, intervalIntegral.integral_congr_ae, LipschitzOnWith.absolutelyContinuousOnInterval, AbsolutelyContinuousOnInterval.integral_deriv_eq_sub, BoundedContinuousFunction.arzela_ascoli, L2.inner_def, ContDiffBump.integral_normed)`
- `grep -n 'theorem arzela_ascoli' lake-packages-25730c7c/mathlib/Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean; grep -rn 'theorem integral_comp_smul_of_nonneg\|theorem MemLp.eLpNorm_eq_integral_rpow_norm\|theorem map_addHaar_smul\|theorem finite_approx_of_totallyBounded' (same Mathlib commit)`
- `grep -rli -E 'rellich|kondrachov|arzela|mollif|absolutelyContinuousOnInterval' lake-packages-25730c7c/simongmt/Poincare <snapshot>/project/GMT`
- `python3 -I scan of dag.json lean_name/theorems (323 names) and nodes/*/*.json (2900 files) for dorag_ha_rb_* and for accepted LipschitzWith/fderiv/MemLp/Finset-net statements`
- `python3 -I scan of accepted candidate commits for extra imports in GMT/Ch07/Submission.lean`
- `lake env lean /tmp/rellich-decomp/Children.lean (12 child statements + parent assembly), /tmp/rellich-decomp/Elab2.lean, /tmp/rellich-decomp/LineFTC.lean, /tmp/rellich-decomp/SegRay.lean, /tmp/rellich-validate/{A,B,C,D,E}/*.lean, /tmp/rellich-validate/Full/Full.lean (#print axioms of all 13 declarations)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-af41ce05d4/parent-child-handoff.json`
- `/tmp/rellich-decomp/Children.lean`
- `/tmp/rellich-decomp/Elab2.lean`
- `/tmp/rellich-decomp/LineFTC.lean`
- `/tmp/rellich-decomp/SegRay.lean`
- `/tmp/rellich-validate/AllStatements.lean`
- `/tmp/rellich-validate/Full/Full.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. The children are declared as theorem Submission.X inside namespace GMT.Ch07 of Submission.lean, which is byte-identical to the contract.

What the pinned code lacks:
- No Rellich/Kondrachov theorem, no Lipschitz-on-lines FTC lemma and no finite-net Arzelà–Ascoli exist in the pinned project or SimonGMT. The SimonGMT matches are only a ContDiffBump mollifier for Ch08 distributional constancy (Chapter08/DistributionalConstancy.lean) and BV L¹ compactness notes (Chapter02/BV.lean); neither has the needed types.
- No accepted DAG declaration has a reusable identical type, and the 12 dorag_ha_rb_* names are unreserved.

Mathlib under import GMT.Ch07.Submission:
- Available: Rademacher (LipschitzWith.ae_differentiableAt), measurableSet_of_differentiableAt, Measure.ae_ae_comm, Haar scaling (addHaar_preimage_smul, map_addHaar_smul, integral_comp_smul), Lp completeness, IsCompact.tendsto_subseq, TotallyBounded.isCompact_of_isClosed, finite_approx_of_totallyBounded.
- Not imported: AbsolutelyContinuousOnInterval.integral_deriv_eq_sub and LipschitzOnWith.absolutelyContinuousOnInterval. They exist in the snapshot (AbsolutelyContinuousFun.lean:225, AbsolutelyContinuous.lean:309), so line_ftc adds import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun; an accepted child already added an import.
- BoundedContinuousFunction.arzela_ascoli and L2.inner_def are not imported either and are not needed: the sup_net and l2_subseq proofs use only imported lemmas.

Lean checks:
- All 12 child types elaborate in comparator scope.
- Each child was proved in Lean, and together with the exact frozen parent type they compile in /tmp/rellich-validate/Full/Full.lean with axioms [propext, Classical.choice, Quot.sound] only.
