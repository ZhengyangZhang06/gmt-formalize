# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.total_bounded-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 4 (total boundedness), written with squared L² quantities. The pointwise inequalities (a − b)² ≤ 2a² + 2b² and (a + b + c)² ≤ 3(a² + b² + c²) replace the L² triangle inequality, and the uniform L¹ bound uses |a| ≤ (1 + a²)/2 instead of Cauchy–Schwarz.

1. (Constants.) M ≥ ∫_B u_0² ≥ 0. Let ω := Lⁿ(B), finite, as a real number ≥ 0. Given η > 0 choose:
- s := min(1/2, η/(3·2^{n+6}(M + 1))). Then 0 < s ≤ 1/2 and 2^{n+6}sM ≤ η/3.
- ε := min(s/2, η/(18(M + 1))). Then 0 < ε ≤ s/2 (so ε ≤ s and ε ≤ 1), ε² ≤ ε, and 6ε²M ≤ η/3.
- δ := min(1, η/(9(ω + 1))). Then 0 < δ ≤ 1, δ² ≤ δ, and 3δ²ω ≤ η/3.

2. (Kernel.) Submission.dorag_ha_rb_kernel gives ρ and C with: ρ continuous, ρ ≥ 0, ρ = 0 on {‖z‖ ≥ 1}, ∫ρ = 1, |ρ| ≤ C, and |ρ(z) − ρ(z')| ≤ C‖z − z'‖. Also C ≥ |ρ(0)| ≥ 0. Put v_j(x) := ∫ u_j(x − εz)ρ(z) dz and K := closedBall(0, 1 − s), which is compact.

3. (Uniform L¹ bound.) Each u_j is continuous, so every continuous expression in the u_j is integrable on B: it is continuous on the compact closedBall(0, 1) (ContinuousOn.integrableOn_compact, mono_set). Since |a| ≤ 1/2 + a²/2:
∫_B |u_j| ≤ ω/2 + (1/2)∫_B u_j² ≤ (ω + M)/2 =: I.

4. (Uniform bounds on K.) Submission.dorag_ha_rb_mollify_bounds (u_j continuous, ε ≤ s/2) together with step 3 gives, for x, x' ∈ K:
|v_j(x)| ≤ (ε^n)⁻¹CI and |v_j(x) − v_j(x')| ≤ (ε^{n+1})⁻¹CI‖x − x'‖.
Let D := (ε^n)⁻¹CI + (ε^{n+1})⁻¹CI; both summands are ≥ 0. Then for every j, |v_j| ≤ D on K and |v_j(x) − v_j(x')| ≤ D‖x − x'‖ on K. In particular v_j is Lipschitz, hence continuous, on K (LipschitzOnWith.of_dist_le', LipschitzOnWith.continuousOn). So (u_j − v_j)² is continuous on K and integrable on B̆_{1−s}(0) ⊆ K.

5. (Finite sup-net.) Submission.dorag_ha_rb_sup_net, applied to K, g := (j, x) ↦ v_j(x), constant D and tolerance δ, gives a finite S ⊆ ℕ such that every j has some k ∈ S with |v_j(x) − v_k(x)| ≤ δ for all x ∈ K. Fix j and such a k; we show ∫_B (u_j − u_k)² ≤ η.

6. (Split.) Let A_s := B ∖ B̆_{1−s}(0). Since B̆_{1−s}(0) ⊆ B (ball_subset_ball, 1 − s ≤ 1) and the integrand is integrable on B:
∫_B (u_j − u_k)² = ∫_{B̆_{1−s}} (u_j − u_k)² + ∫_{A_s} (u_j − u_k)² (integral_inter_add_sdiff with Set.inter_eq_right).

7. (Boundary layer.) Pointwise (u_j − u_k)² ≤ 2u_j² + 2u_k². By Submission.dorag_ha_rb_boundary_layer (with the Lipschitz constant of u_j and the above s):
∫_{A_s} u_j² ≤ 2^{n+3}s(∫_B u_j² + ∫_B ‖Du_j‖²) ≤ 2^{n+3}s(M + M),
and likewise for k. Hence ∫_{A_s} (u_j − u_k)² ≤ 4·2^{n+3}s·2M = 2^{n+6}sM ≤ η/3.

8. (Interior.) For x ∈ B̆_{1−s}(0) ⊆ K, write u_j − u_k = (u_j − v_j) + (v_j − v_k) + (v_k − u_k). Using |v_j − v_k| ≤ δ:
(u_j − u_k)² ≤ 3(u_j − v_j)² + 3δ² + 3(u_k − v_k)².
Integrate with setIntegral_mono_on; all terms are integrable on B̆_{1−s}, and setIntegral_const handles the constant. Then:
- Submission.dorag_ha_rb_mollify_l2 applies, since ρ satisfies its hypotheses and 0 < ε ≤ s. It gives ∫_{B̆_{1−s}} (u_j − v_j)² ≤ ε²∫_B ‖Du_j‖² ≤ ε²M, and likewise for k.
- Lⁿ(B̆_{1−s}) ≤ ω (measureReal_mono).
So ∫_{B̆_{1−s}} (u_j − u_k)² ≤ 6ε²M + 3δ²ω ≤ 2η/3.

9. Adding steps 7 and 8 into step 6 gives ∫_B (u_j − u_k)² ≤ η. ∎

Validation note (not part of the argument): a kernel-checked Lean proof of this exact frozen statement from the five sibling statements was compiled during decomposition review as Submission.dorag_ha_rb_total_bounded in /tmp/rellich-validate/Full/Full.lean (axioms propext, Classical.choice, Quot.sound). That scratch file may not persist.

## Key steps

1. Choose s, ε ≤ s/2 and δ so that 2^{n+6}sM, 6ε²M and 3δ²Lⁿ(B) are each ≤ η/3.
2. Mollify with the kernel from dorag_ha_rb_kernel; via dorag_ha_rb_mollify_bounds and ∫_B|u_j| ≤ (Lⁿ(B) + M)/2, the v_j are uniformly bounded and uniformly Lipschitz on closedBall(0, 1 − s).
3. dorag_ha_rb_sup_net gives finitely many indices whose v_k form a δ-net in sup norm on closedBall(0, 1 − s).
4. Split B into B̆_{1−s} and A_s: dorag_ha_rb_boundary_layer bounds the annulus by 2^{n+6}sM; dorag_ha_rb_mollify_l2 and the sup-net bound the interior by 6ε²M + 3δ²Lⁿ(B).

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
