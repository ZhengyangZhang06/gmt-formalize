# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.du_bois_reymond-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.du_bois_reymond-a1.dbr_antiderivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 (Antiderivatives) of the parent proof of the du Bois-Reymond lemma, applied to an arbitrary g in place of χ₀ = χ − (∫χ)η. Lebesgue measure on ℝ is `volume`, and ∫_{u}^{v} denotes the oriented interval integral.
1. Let K := tsupport g. K is compact (g has compact support) and K ⊆ (a, b).
   If K = ∅, every x lies outside tsupport g, so g(x) = 0 for all x (image_eq_zero_of_notMem_tsupport), i.e. g = 0. Then Φ := 0 works: it is C¹ (constant), has compact support, tsupport 0 = ∅ ⊆ (a, b), and deriv 0 = 0 = g. This case also covers b ≤ a, since then (a, b) = ∅. Assume from now on K ≠ ∅.
2. Choose a′ and b′.
   - A nonempty compact subset of ℝ contains its infimum and supremum (IsCompact.sInf_mem, IsCompact.sSup_mem). So k₁ := inf K ∈ K and k₂ := sup K ∈ K, hence a < k₁ and k₂ < b.
   - Put a′ := (a + k₁)/2 and b′ := (k₂ + b)/2. Then a < a′ < k₁ ≤ k₂ < b′ < b.
   - K is bounded, so every y ∈ K satisfies k₁ ≤ y ≤ k₂ (csInf_le, le_csSup); hence K ⊆ (a′, b′).
   - Consequently support g ⊆ K ⊆ (a′, b′), i.e. g(y) = 0 whenever y ≤ a′ or y ≥ b′.
3. Define Φ(x) := ∫_{a′}^{x} g(y) dy. Since g is continuous, the fundamental theorem of calculus gives HasStrictDerivAt Φ (g x) x for every x (Continuous.integral_hasStrictDerivAt with lower limit a′). So Φ is differentiable at every x, and deriv Φ x = g x (Continuous.deriv_integral). Thus Φ is differentiable on ℝ and deriv Φ = g, which is continuous; by contDiff_one_iff_deriv, Φ is C¹.
4. Φ vanishes outside [a′, b′].
   (i) If x < a′: the oriented integral ∫_{a′}^{x} g involves only points of the half-open interval uIoc a′ x = (x, a′]. Each such y satisfies y ≤ a′, so g(y) = 0 by step 2. Hence Φ(x) = 0 (intervalIntegral.integral_zero_ae).
   (ii) If x > b′: support g ⊆ (a′, b′) ⊆ (a′, x]. So ∫_{a′}^{x} g = ∫_ℝ g (intervalIntegral.integral_eq_integral_of_support_subset), which is 0 by hypothesis. Hence Φ(x) = 0.
5. By step 4, support Φ ⊆ [a′, b′].
   - [a′, b′] is compact, so Φ has compact support (HasCompactSupport.intro).
   - [a′, b′] is closed, so tsupport Φ = closure(support Φ) ⊆ [a′, b′] (closure_minimal).
   - [a′, b′] ⊆ (a, b) because a < a′ and b′ < b.
   Together with step 3 (Φ is C¹ and deriv Φ = g), Φ has all the required properties. ∎

## Key steps

1. If tsupport g = ∅ then g = 0 and Φ = 0 works.
2. Otherwise choose a < a′ < inf K ≤ sup K < b′ < b, so g = 0 outside (a′, b′).
3. Φ(x) := ∫_{a′}^{x} g is C¹ with deriv Φ = g by the fundamental theorem of calculus.
4. Φ = 0 for x < a′ (g = 0 there) and for x > b′ (∫_ℝ g = 0), so Φ has compact support and tsupport Φ ⊆ [a′, b′] ⊆ (a, b).

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
