# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.du_bois_reymond-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.du_bois_reymond-a1.dbr_fundamental_lemma-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 (Fundamental lemma) of the parent proof of the du Bois-Reymond lemma, with κ − c replaced by an arbitrary g. This is the basic version of the fundamental lemma of the calculus of variations; Wikipedia, 'Fundamental lemma of the calculus of variations', proves it with a bump on a subinterval where the function keeps one sign. Lebesgue measure on ℝ is `volume`. The proof uses the sibling lemma dbr_integrable.
1. Fix x₀ ∈ (a, b). We first prove the Claim: if h : ℝ → ℝ is continuous on (a, b) and ∫ χ(y)h(y) dy = 0 for every C^∞ χ with compact support and tsupport χ ⊆ (a, b), then h(x₀) > 0 is impossible.
2. Proof of the Claim. Suppose d := h(x₀) > 0.
   - (a, b) is open and contains x₀, so continuity of h on (a, b) gives continuity of h at x₀ (ContinuousOn.continuousAt with isOpen_Ioo.mem_nhds).
   - Both (a, b) and {y : h(y) > d/2} are neighbourhoods of x₀; the latter because d/2 < h(x₀) and h is continuous at x₀.
   - So there is ρ > 0 such that every y with |y − x₀| < ρ satisfies y ∈ (a, b) and h(y) > d/2 (Metric.eventually_nhds_iff_ball).
   - Put r := ρ/2. Then every y with |y − x₀| ≤ r satisfies y ∈ (a, b) and h(y) > d/2.
3. Let χ be the ContDiffBump centred at x₀ with inner radius r/2 and outer radius r (valid since 0 < r/2 < r; ℝ has HasContDiffBump ℝ). Then:
   - χ is C^∞, continuous, and has compact support;
   - 0 ≤ χ ≤ 1, and χ(y) = 1 for |y − x₀| ≤ r/2 (one_of_mem_closedBall);
   - support χ = (x₀ − r, x₀ + r) and tsupport χ = [x₀ − r, x₀ + r];
   - tsupport χ ⊆ (a, b) by step 2.
   The hypothesis on h therefore gives ∫ χ(y)h(y) dy = 0.
4. χh ≥ 0 everywhere. If |y − x₀| ≤ r, then χ(y) ≥ 0 and h(y) > d/2 > 0, so χ(y)h(y) ≥ 0. Otherwise y ∉ (x₀ − r, x₀ + r) = support χ, so χ(y) = 0 and χ(y)h(y) = 0.
5. χh is integrable on ℝ by the sibling lemma dbr_integrable, applied with κ := h (continuous on (a, b)) and the continuous, compactly supported χ with tsupport χ ⊆ (a, b).
6. For |y − x₀| < r/2 we have χ(y) = 1 and h(y) > d/2 > 0, so χ(y)h(y) > d/2 > 0. Hence the support of χh contains the open interval (x₀ − r/2, x₀ + r/2), whose Lebesgue measure is r > 0 (Real.volume_ball and measure_mono). By integral_pos_iff_support_of_nonneg (χh ≥ 0 by step 4, integrable by step 5, support of positive measure), ∫χh > 0; quantitatively ∫χh ≥ (d/2)·r. This contradicts step 3 and proves the Claim.
7. Apply the Claim with h := g: g(x₀) > 0 is impossible.
   Apply it with h := −g. −g is continuous on (a, b), and for every admissible χ, ∫χ(−g) = −∫χg = 0 (mul_neg, integral_neg). So −g(x₀) > 0 is impossible, i.e. g(x₀) < 0 is impossible.
   By trichotomy g(x₀) = 0. Since x₀ ∈ (a, b) was arbitrary, g = 0 on (a, b). If b ≤ a the statement is vacuous. ∎
Remark (alternative Lean route, also complete). This proof can replace steps 1–7.
   - g is continuous on the measurable set (a, b), hence locally integrable on the open set (a, b) (ContinuousOn.locallyIntegrableOn with measurableSet_Ioo).
   - Mathlib's IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean, reachable from the frozen imports) applies with μ := volume and U := (a, b). Its hypothesis ∫ χ • g = 0 is exactly the given one, since χ • g = χ·g (smul_eq_mul).
   - It yields ∀ᵐ x, x ∈ (a, b) → g x = 0, i.e. g = 0 almost everywhere for volume restricted to (a, b) (ae_restrict_iff' with measurableSet_Ioo).
   - g and the constant 0 are continuous on the open set (a, b), and Lebesgue measure is positive on nonempty open sets. So Measure.eqOn_open_of_ae_eq gives g x = 0 for every x ∈ (a, b).

## Key steps

1. It suffices to show that h(x₀) > 0 is impossible for any h satisfying the hypotheses; apply this to g and −g.
2. By continuity at x₀, find r > 0 with [x₀ − r, x₀ + r] ⊆ (a, b) and h > h(x₀)/2 there.
3. Take the ContDiffBump χ at x₀ with radii r/2 and r. Then χh ≥ 0, χh is integrable (dbr_integrable), and χh > h(x₀)/2 on (x₀ − r/2, x₀ + r/2).
4. Hence ∫χh > 0, contradicting the hypothesis ∫χh = 0; so g(x₀) = 0.

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
