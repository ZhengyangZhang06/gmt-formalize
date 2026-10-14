# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.du_bois_reymond-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.du_bois_reymond-a1.dbr_integrable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 (Integrability) of the parent proof of the du Bois-Reymond lemma, stated here for an arbitrary continuous χ. Lebesgue measure on ℝ is `volume`.
1. Let K := tsupport χ, the closure of the support of χ. Because χ has compact support, K is compact, and K ⊆ (a, b) by hypothesis. No assumption a < b is needed: if K = ∅ the argument below applies verbatim.
2. κ is continuous on (a, b), hence on its subset K (ContinuousOn.mono with K ⊆ (a, b)). χ is continuous on ℝ, hence on K. So the product x ↦ χ(x)κ(x) is continuous on K (ContinuousOn.mul).
3. Lebesgue measure is finite on compact sets and ℝ is Hausdorff. So a function continuous on the compact set K is integrable on K (ContinuousOn.integrableOn_compact), i.e. IntegrableOn (fun x => χ x * κ x) K.
4. If x ∉ K = tsupport χ, then χ(x) = 0 (image_eq_zero_of_notMem_tsupport), so χ(x)κ(x) = 0·κ(x) = 0.
5. A function that is integrable on K and vanishes at every point outside K is integrable on ℝ (IntegrableOn.integrable_of_forall_notMem_eq_zero, using steps 3 and 4). Hence x ↦ χ(x)κ(x) is integrable on ℝ. ∎

## Key steps

1. K := tsupport χ is compact and K ⊆ (a, b).
2. χ·κ is continuous on K, hence integrable on the compact set K.
3. χ·κ vanishes outside K, hence is integrable on ℝ.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean`
- `grep -n '^open\|^namespace\|^end\|^section\|^noncomputable\|^variable\|^universe\|^set_option\|^notation' GMT/Ch07/Contract.lean`
- `python3 -I scan of dag.json: selected node id/depth/status; lean_name matching bois|reymond|fundamental_lemma|antideriv|weak_deriv|distrib; all lean_name with prefix idtp_ccd_scsp`
- `grep -c / grep -rl idtp_ccd_scsp_dbr{,_integrable,_normalized_bump,_antiderivative,_fundamental_lemma} in dag.json and runs/20261011T150044Z-ba604216b4/nodes; grep -l idtp_ccd_scsp_dbr ../.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean`
- `rg -n 'theorem (IsOpen\.ae_eq_zero_of_integral_contDiff_smul_eq_zero|contDiff_one_iff_deriv|integral_pos_iff_support_of_nonneg|Continuous\.integrable_of_hasCompactSupport|ContinuousOn\.integrableOn_compact|IntegrableOn\.integrable_of_forall_notMem_eq_zero|integral_eq_integral_of_support_subset|integral_zero_ae|IsCompact\.sInf_mem|IsCompact\.sSup_mem|tsupport_mul_subset_right|eqOn_open_of_ae_eq|volume_ball|ContinuousOn\.locallyIntegrableOn)\b' Mathlib`
- `rg -n 'theorem _root_.Continuous.integral_hasStrictDerivAt|theorem _root_.Continuous.deriv_integral' Mathlib; rg -n 'mulTSupport_div|theorem intro' Mathlib/Topology/Algebra/Support.lean; rg -n 'structure ContDiffBump|one_of_mem_closedBall|support_eq|tsupport_eq|hasCompactSupport|contDiff' Mathlib/Analysis/Calculus/BumpFunction/Basic.lean; rg -n hasContDiffBump_of_innerProductSpace Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean; rg -n 'def normed' Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `rg -n 'du Bois|DuBois|fundamental lemma of (the )?calculus of variations' Mathlib (no match); grep -n 'theorem ae_eq_const_of_weak_coordinate_derivatives_zero' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `lake env lean /tmp/dbr_probe/Probe1.lean; Probe2.lean; Assembly.lean; Children.lean; Full.lean (with #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-9858a75c38/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-9858a75c38/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/tmp/dbr_probe/Probe1.lean`
- `/tmp/dbr_probe/Probe2.lean`
- `/tmp/dbr_probe/Assembly.lean`
- `/tmp/dbr_probe/Children.lean`
- `/tmp/dbr_probe/Full.lean`

Pins match. The snapshot project_commit b4d606d equals workspace HEAD and mathlib 25730c7c equals .lake/packages/mathlib HEAD. The snapshot Contract.lean is byte-identical to the workspace Contract.lean. The comparator scope at main_theorem is namespace GMT.Ch07 with open Filter Function Set MeasureTheory Metric, open scoped ENNReal Topology, open Poincare.SimonGMT.Chapter06 and the Chapter03 selective open.

Neither the Mathlib snapshot nor the DAG contains a du Bois-Reymond lemma or a pointwise fundamental lemma of the calculus of variations: the rg searches for 'du Bois', 'DuBois' and 'fundamental lemma of calculus of variations' found nothing. The closest results:
- IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean:205), an a.e. version reachable from the frozen imports. Combined with Measure.eqOn_open_of_ae_eq (OpenPos.lean:115) it gives an alternative proof of the dbr_fundamental_lemma child.
- SimonGMT ae_eq_const_of_weak_coordinate_derivatives_zero (Chapter08/DistributionalConstancy.lean:294), which needs a proof-only import and Euclidean transport and is not used.

The only related DAG node, idtp_cse_ah_antiderivative_test, has status decomposing (not accepted) and a different type, so it cannot be reused. Fresh names idtp_ccd_scsp_dbr_* were chosen; they have no match in dag.json, in the run nodes, or in 1408 worktree Submission.lean files.

Pinned Mathlib supplies every lemma the child proofs cite:
- bump functions: ContDiffBump with one_of_mem_closedBall, nonneg, support_eq, tsupport_eq, hasCompactSupport, contDiff and continuous (BumpFunction/Basic.lean), with the instance hasContDiffBump_of_innerProductSpace (InnerProduct.lean). ContDiffBump.normed (Normed.lean) is not imported and not used.
- calculus: Continuous.integral_hasStrictDerivAt and Continuous.deriv_integral (FundThmCalculus.lean:656/664); contDiff_one_iff_deriv (ContDiff/Deriv.lean:98).
- integrals: integral_pos_iff_support_of_nonneg (Bochner/Basic.lean:790), integral_sub, integral_const_mul, integral_mul_const; intervalIntegral.integral_eq_integral_of_support_subset and integral_zero_ae (IntervalIntegral/Basic.lean:1230/1268); Real.volume_ball (Lebesgue/Basic.lean:132).
- integrability: Continuous.integrable_of_hasCompactSupport, ContinuousOn.integrableOn_compact and ContinuousOn.locallyIntegrableOn (LocallyIntegrable.lean); IntegrableOn.integrable_of_forall_notMem_eq_zero (IntegrableOn.lean:453).
- topology and supports: IsCompact.sInf_mem and sSup_mem (Topology/Order/Compact.lean); tsupport_sub (via mulTSupport_div), tsupport_mul_subset_right and HasCompactSupport.intro (Topology/Algebra/Support.lean).

Lean checks after import GMT.Ch07.Submission in the contract scope:
- All four child types elaborate.
- Assembly.lean proves the exact frozen parent type from the four stubs, with axioms propext, Classical.choice and Quot.sound, plus sorryAx only from the stubs.
- Children.lean proves each child, including an alternative Mathlib proof of the fundamental lemma, with axioms propext, Classical.choice and Quot.sound.
- Full.lean contains no sorry and proves the parent through the children with standard axioms only.
