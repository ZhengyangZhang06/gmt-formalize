# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.du_bois_reymond-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.du_bois_reymond-a1.dbr_normalized_bump-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 (Normalized bump) of the parent proof of the du Bois-Reymond lemma. Lebesgue measure on ℝ is `volume`.
1. Put m := (a + b)/2 and ρ := (b − a)/4. Since a < b, 0 < (b − a)/8 < ρ. Let β be the ContDiffBump centred at m with inner radius rIn = (b − a)/8 and outer radius rOut = ρ. These are valid radii (0 < rIn < rOut), and ℝ has the instance HasContDiffBump ℝ because it is a real inner product space (hasContDiffBump_of_innerProductSpace).
2. The standard ContDiffBump properties give:
   - β is C^∞ (ContDiffBump.contDiff with n = ⊤) and continuous;
   - 0 ≤ β(x) for every x (nonneg);
   - support β = ball(m, ρ) = (m − ρ, m + ρ) (support_eq);
   - tsupport β = closedBall(m, ρ) = [m − ρ, m + ρ] (tsupport_eq);
   - β has compact support (hasCompactSupport).
3. [m − ρ, m + ρ] ⊆ (a, b). Indeed, if |x − m| ≤ ρ, then x ≥ m − ρ = a + (b − a)/4 > a and x ≤ m + ρ = b − (b − a)/4 < b.
4. β is continuous with compact support, hence integrable (Continuous.integrable_of_hasCompactSupport). Since β ≥ 0 and β is integrable, integral_pos_iff_support_of_nonneg gives: ∫β > 0 iff volume(support β) > 0. Moreover volume(support β) = volume(ball(m, ρ)) = ENNReal.ofReal(2ρ) > 0 (Real.volume_ball and 2ρ > 0). Hence I_β := ∫β > 0, in particular I_β ≠ 0.
5. Define η(x) := I_β⁻¹ · β(x). Then:
   - η is C^∞, as the product of the constant I_β⁻¹ and the C^∞ function β (contDiff_const.mul);
   - η has compact support, because support η ⊆ support β (HasCompactSupport.mul_left);
   - tsupport η ⊆ tsupport β = [m − ρ, m + ρ] ⊆ (a, b), by tsupport_mul_subset_right and step 3;
   - ∫η = I_β⁻¹ · ∫β = I_β⁻¹ · I_β = 1, by integral_const_mul and step 4. ∎

## Key steps

1. Take the ContDiffBump β centred at (a+b)/2 with radii (b−a)/8 and (b−a)/4.
2. tsupport β = [m − (b−a)/4, m + (b−a)/4] ⊆ (a, b).
3. ∫β > 0 because β ≥ 0 is integrable and its support is an interval of positive length.
4. η := (∫β)⁻¹·β is C^∞, compactly supported in (a, b), with ∫η = 1.

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
