# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.segment_ftc-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 1 (FTC along translations; Tonelli for the null set of non-differentiability points).

1. Let D := {y ∈ ℝⁿ : u is differentiable at y}. D is measurable (measurableSet_of_differentiableAt ℝ u). By Rademacher's theorem (LipschitzWith.ae_differentiableAt), a.e. y ∈ ℝⁿ lies in D.

2. Fix τ ∈ ℝ. The translation p ↦ p + τz preserves Lebesgue measure (measurePreserving_add_right volume (τ • z)), so pulling back the a.e. statement of step 1 gives: for a.e. p, p + τz ∈ D (MeasurePreserving.quasiMeasurePreserving.ae). Hence ∀ τ, ∀ᵐ p, p + τz ∈ D; in particular ∀ᵐ τ, ∀ᵐ p, p + τz ∈ D (Filter.Eventually.of_forall).

3. The set {(p, τ) ∈ ℝⁿ × ℝ : p + τz ∈ D} is measurable: it is the preimage of D under the continuous map (p, τ) ↦ p + τ•z. Lebesgue measures on ℝⁿ and on ℝ are σ-finite, so Fubini's theorem for null sets (MeasureTheory.Measure.ae_ae_comm) turns step 2 into: for a.e. p ∈ ℝⁿ, for a.e. τ ∈ ℝ, p + τz ∈ D.

4. Fix such p. The hypothesis of Submission.dorag_ha_rb_line_ftc holds for (p, v, a, b) = (p, z, 0, 1): for a.e. τ, whether or not τ ∈ uIcc 0 1, u is differentiable at p + τ•z. It yields u(p + 1•z) − u(p + 0•z) = ∫_0^1 Du(p + τz)z dτ. Since 1•z = z and p + 0•z = p (simp), this is the claim. ∎

Validation note (not part of the argument): a kernel-checked Lean proof of this exact frozen statement from dorag_ha_rb_line_ftc was compiled during decomposition review as Submission.dorag_ha_rb_segment_ftc in /tmp/rellich-validate/Full/Full.lean (axioms propext, Classical.choice, Quot.sound). That scratch file may not persist.

## Key steps

1. The differentiability set D is measurable and conull (Rademacher).
2. For each τ, translation invariance gives a.e. p with p + τz ∈ D.
3. Measure.ae_ae_comm on the measurable set {(p, τ) : p + τz ∈ D} gives: for a.e. p, for a.e. τ, p + τz ∈ D.
4. Apply dorag_ha_rb_line_ftc with v = z, a = 0, b = 1 and simplify.

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
