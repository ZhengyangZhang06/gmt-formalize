# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.boundary_layer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 3 (boundary layer), parts (i)–(iii) and (v). Part (iv) is Submission.dorag_ha_rb_dilation_average.

1. (Bounds.)
- ‖Du‖ ≤ L everywhere (norm_fderiv_le_of_lipschitz).
- For ‖y‖ ≤ 1, |u(y)| ≤ |u(0)| + L =: M₀ (Lipschitz).
- Bounded a.e.-strongly-measurable functions are integrable on measurable subsets of B, which have finite measure. In particular u² and ‖Du‖² (measurable via measurable_fderiv) are integrable on B and on A_s.

2. (Rays.) By Submission.dorag_ha_rb_ray_ftc, for a.e. x and every t ∈ ℝ: u(x) − u(tx) = ∫_t^1 Du(σx)x dσ.

3. (Pointwise estimate.) Fix such an x with ‖x‖ ≤ 1. Put
- g(σ) := ‖Du(σx)‖, which is measurable with 0 ≤ g ≤ L;
- γ := ∫_{1/2}^1 g ≥ 0;
- J(x) := ∫_{1/2}^1 ‖Du(σx)‖² dσ;
- I₁(x) := ∫_{1/2}^1 u(tx)² dt.
(a) For t ∈ [1/2, 1]: |u(x) − u(tx)| = |∫_t^1 Du(σx)x dσ| ≤ ∫_t^1 ‖Du(σx)‖‖x‖ dσ ≤ ∫_t^1 g ≤ γ. This uses intervalIntegral.norm_integral_le_integral_norm, ContinuousLinearMap.le_opNorm, ‖x‖ ≤ 1, g ≥ 0 and intervalIntegral.integral_mono_interval.
(b) Hence u(x)² ≤ 2u(tx)² + 2γ² for every t ∈ [1/2, 1], since (a + b)² ≤ 2a² + 2b².
(c) Cauchy–Schwarz on [1/2, 1], an interval of length 1/2: 0 ≤ ∫_{1/2}^1 (g − 2γ)² = J(x) − 4γ² + 2γ², so 2γ² ≤ J(x). Any weaker bound 2γ² ≤ cJ(x) with c ≤ 4 also suffices below; for example, integrating 2γg ≤ g² + γ² gives (3/2)γ² ≤ J(x).
(d) The map t ↦ u(tx)² is continuous. Integrating (b) over t ∈ [1/2, 1] gives (1/2)u(x)² ≤ 2I₁(x) + (1/2)·2γ². So u(x)² ≤ 4I₁(x) + 2γ² ≤ 4I₁(x) + J(x).

4. (Integrability on A_s.) Write the interval integrals as integrals over Ioc (1/2) 1 (intervalIntegral.integral_of_le).
- I₁ and J are a.e.-strongly measurable on A_s: apply StronglyMeasurable.integral_prod_right to the jointly measurable functions (x, t) ↦ u(tx)² and (x, t) ↦ ‖Du(tx)‖².
- They are bounded on A_s by M₀²/2 and L²/2 (intervalIntegral.norm_integral_le_of_norm_le_const), since ‖tx‖ ≤ 1 for x ∈ A_s and t ∈ [1/2, 1].
Hence I₁ and J are integrable on A_s.

5. (Integration.) By steps 2 and 3, u(x)² ≤ 4I₁(x) + J(x) for a.e. x ∈ A_s (ae_restrict_iff'). integral_mono_of_nonneg and linearity give
∫_{A_s} u² ≤ 4∫_{A_s} I₁ + ∫_{A_s} J.

6. (Dilation.)
- With F = u² (measurable, ≥ 0, integrable on B), Submission.dorag_ha_rb_dilation_average gives ∫_{A_s} I₁ ≤ 2^{n+1}s∫_B u².
- With F = ‖Du‖² (measurable, ≥ 0, integrable on B), it gives ∫_{A_s} J ≤ 2^{n+1}s∫_B ‖Du‖².

7. Hence ∫_{A_s} u² ≤ 4·2^{n+1}s∫_B u² + 2^{n+1}s∫_B ‖Du‖² ≤ 2^{n+3}s(∫_B u² + ∫_B ‖Du‖²). This uses 2^{n+3} = 4·2^{n+1}, s > 0 and ∫_B ‖Du‖² ≥ 0. ∎

Validation note (not part of the argument): a kernel-checked Lean proof of this exact frozen statement from dorag_ha_rb_ray_ftc and dorag_ha_rb_dilation_average was compiled during decomposition review as Submission.dorag_ha_rb_boundary_layer in /tmp/rellich-validate/Full/Full.lean (axioms propext, Classical.choice, Quot.sound). That scratch file may not persist.

## Key steps

1. By dorag_ha_rb_ray_ftc, for a.e. x and all t: u(x) − u(tx) = ∫_t^1 Du(σx)x dσ.
2. For x ∈ A_s and t ∈ [1/2, 1]: u(x)² ≤ 2u(tx)² + 2γ² with γ = ∫_{1/2}^1 ‖Du(σx)‖ dσ, and 2γ² ≤ ∫_{1/2}^1 ‖Du(σx)‖² by Cauchy–Schwarz.
3. Averaging over t ∈ [1/2, 1] gives u(x)² ≤ 4∫_{1/2}^1 u(tx)² dt + ∫_{1/2}^1 ‖Du(σx)‖² dσ.
4. Integrate over A_s (both averages are bounded and measurable, hence integrable) and apply dorag_ha_rb_dilation_average to u² and ‖Du‖²; 4·2^{n+1} = 2^{n+3}.

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
