# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.local_filling-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.local_filling-a1.small_scale-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 0 and 2 of the parent proof (Simon Ch. 6, 8.2 (2), with the lower density in place of Θ^{*n}), stated for an arbitrary real η₀ and an arbitrary measure μ.

Notation: ω_n := unitBallVolume n = volume(ball (0 : Euclid n) 1) ∈ [0, ∞] and w := ω_n.toReal. For real r, g(r) := μ(ball x₁ r)/(ω_n · ENNReal.ofReal(r^n)) ∈ [0, ∞], using ENNReal division.

1. (ω_n > 0.) By definition (unfold unitBallVolume), ω_n = volume(ball (0 : Euclid n) 1). The volume measure on the finite-dimensional inner product space Euclid n is an additive Haar measure, so it is positive on nonempty open sets (IsOpenPosMeasure). The ball of radius 1 > 0 about 0 is open and contains 0, so ω_n > 0 (measure_ball_pos _ _ one_pos). This also holds for n = 0, where the ball is the whole one-point space.

2. (ω_n < ∞.) Euclid n is a proper metric space and volume is finite on compact sets, so every ball has finite measure (measure_ball_lt_top). Hence ω_n < ∞.

3. (Part (a).) By Steps 1 and 2, ω_n ≠ 0 and ω_n ≠ ∞. So w = ω_n.toReal > 0 (ENNReal.toReal_pos) and ENNReal.ofReal w = ω_n (ENNReal.ofReal_toReal). This proves (a).

4. (Part (b): the ratio is frequently small.) Fix P, μ, x₁, η₀ and δ with δ > 0 and liminf_{𝓝[>] 0} g < ENNReal.ofReal η₀. [0, ∞] is a complete linear order, so the coboundedness side condition holds automatically (isBoundedDefault). Then frequently_lt_of_liminf_lt shows that g(r) < ENNReal.ofReal η₀ holds frequently along 𝓝[>] 0.

5. (Choosing s.) Since δ > 0, Ioo 0 δ ∈ 𝓝[>] 0 (Ioo_mem_nhdsGT), so 0 < r < δ holds eventually along 𝓝[>] 0. A frequently-true property and an eventually-true property hold together for at least one r (Frequently.and_eventually, then Frequently.exists). Call that r s. Then 0 < s < δ and g(s) < ENNReal.ofReal η₀.

6. (Clearing the denominator.) Let D := ω_n · ENNReal.ofReal(s^n).
- D ≠ 0: s > 0 gives s^n > 0 (pow_pos), so ENNReal.ofReal(s^n) > 0 (ENNReal.ofReal_pos), and ω_n > 0 by Step 1 (mul_ne_zero).
- D ≠ ∞: ω_n < ∞ by Step 2 and ENNReal.ofReal(s^n) ≠ ∞ (ENNReal.mul_ne_top).
ENNReal.div_lt_iff (Or.inl (D ≠ 0)) (Or.inl (D ≠ ∞)) turns g(s) < ENNReal.ofReal η₀ into μ(ball x₁ s) < ENNReal.ofReal η₀ · D.

7. (η₀ ≥ 0.) Suppose η₀ < 0. Then ENNReal.ofReal η₀ = 0 (ENNReal.ofReal_of_nonpos), and Step 6 gives μ(ball x₁ s) < 0 · D = 0. No element of [0, ∞] is < 0, so this is impossible. Hence η₀ ≥ 0.

8. (Rewriting the bound.) We have η₀ ≥ 0, w ≥ 0 and s^n ≥ 0. Apply ENNReal.ofReal_mul twice, then ENNReal.ofReal w = ω_n (Step 3), then associativity:
ENNReal.ofReal(η₀ · w · s^n) = ENNReal.ofReal η₀ · ENNReal.ofReal w · ENNReal.ofReal(s^n) = ENNReal.ofReal η₀ · (ω_n · ENNReal.ofReal(s^n)) = ENNReal.ofReal η₀ · D.
By Step 6, μ(ball x₁ s) < ENNReal.ofReal(η₀ · w · s^n), and 0 < s < δ by Step 5. This proves (b). ∎

## Key steps

1. ω_n = volume(ball(0,1)) is positive (a nonempty open set under an additive Haar measure) and finite (a ball in a proper space), so w = ω_n.toReal > 0 and ENNReal.ofReal w = ω_n.
2. liminf_{𝓝[>]0} g < ofReal η₀ gives g(r) < ofReal η₀ frequently (frequently_lt_of_liminf_lt). Since Ioo 0 δ ∈ 𝓝[>] 0, pick s ∈ (0, δ) with g(s) < ofReal η₀.
3. The denominator ω_n·ofReal(s^n) is nonzero and finite, so ENNReal.div_lt_iff gives μ(B_s(x₁)) < ofReal η₀·(ω_n·ofReal(s^n)). Moreover η₀ ≥ 0, since otherwise the right side would be 0.
4. ofReal η₀·(ω_n·ofReal(s^n)) = ofReal(η₀·w·s^n) by ENNReal.ofReal_mul and ofReal w = ω_n.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cat of the node's parent-child-handoff.json, parent-supplied-plan.md and parent-supplied-natural-proof.md`
- `python3 -I scan of dag.json: this node (depth 4, status decomposing, depends_on slice-a1/radius-a1/mass_gap-a1); frozen lean_statements of the siblings cbrld_sphere_slice_isIntegerMultiplicity, cbrld_exists_good_slice_radius and cbrld_im_degree_zero_eq_zero_of_mass_lt_one; regex search of all lean_statements for '(0 : GeometricCurrentOn', 'unitBallVolume', 'frequently', 'thickening', 'support = ∅' and 'IsCompact X.support'. Only non-identical statements matched (dtc_dim_zero_eq_zero, rsd_cmr_support_subset_of_vanish, dtc_extend_by_zero, cmc_deformation_theorem, dorag_dbs_density_constants), so none can be reused verbatim`
- `sed of GMT/Ch07/Contract.lean and Submission.lean (identical; unitBallVolume := volume (ball (0 : Euclid n) 1), Euclid, IsIntegerMultiplicity, Sub instance); grep 'def unitBallVolume' in local-references/.../project/GMT (Ch07/Submission.lean:143 matches the workspace)`
- `sed of SimonGMT Chapter06/Currents.lean (GeometricCurrentOn, Zero instance, zero_apply, boundary, boundary_apply, boundary_boundary), Mass.lean (covectorEuclideanNorm, massAdmissibleOn, massOn, mass, le_massOn) and CurrentLocalEquality.lean (VanishesOn, zeroRegion, support, isOpen_zeroRegion)`
- `grep -rn in the Mathlib snapshot for: Ioo_mem_nhdsGT, frequently_lt_of_liminf_lt (to_dual of frequently_lt_of_lt_limsup), Frequently.and_eventually, Frequently.exists, ENNReal.div_lt_iff, toReal_pos, ofReal_le_ofReal, ofReal_pos, ofReal_mul, ofReal_toReal, toReal_le_of_le_ofReal, measure_ball_pos, measure_ball_lt_top, isCompact_sphere, mem_thickening_iff, Real.rpow_add', Real.rpow_mul, Real.mul_rpow, Real.pow_rpow_inv_natCast, Real.rpow_inv_natCast_pow, Real.rpow_le_rpow, Real.rpow_le_one`
- `verifier/lean_contract.py validate_lean_statement on both child statements (pass); verifier/gmt-compare.py contract_scope/child_modules (scope replay: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section)`
- `runtime.py _decompose / _dependency_problem / _existing_lean_name_problem; grep -c cbrldlf in dag.json and issue-workers.json (0 each); grep -rln for the two proposed names over GMT/, simongmt and local-references/.../project (no match)`
- `lake env lean /tmp/cbrldlf-decomp-k7q2/Types.lean (both child types elaborate); /tmp/cbrldlf-decomp-k7q2/Children.lean (scratch proofs of both children; #print axioms: propext, Classical.choice, Quot.sound); /tmp/cbrldlf-decomp-k7q2/Assembly.lean (exact frozen parent type from the two child types plus the frozen slice/radius/mass_gap types; #print axioms: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-5b8e55fd95/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-5b8e55fd95/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-5b8e55fd95/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LeftRightNhds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/tmp/cbrldlf-decomp-k7q2/Types.lean`
- `/tmp/cbrldlf-decomp-k7q2/Children.lean`
- `/tmp/cbrldlf-decomp-k7q2/Assembly.lean`

Nothing in the snapshot (the project, SimonGMT, Mathlib or the accepted DAG nodes) gives, verbatim, either the extraction of a scale from the lower density or the constant/rpow estimate for the isoperimetric filling, so both are new obligations. Mathlib supplies every generic tool cited in the child proofs; each name was found in the pinned snapshot. SimonGMT Chapter06 supplies the zero current, boundary_boundary, mass/massOn and support/zeroRegion that the parent's own assembly uses. Neither child depends on the parent's siblings or on the other child. Both child types elaborate in the replayed contract scope and pass the verifier's lexical check. Scratch Lean proofs of both children compile, and a scratch assembly derives the exact frozen parent type from the two child types and the frozen types of slice, radius and mass_gap. All of these use only the axioms propext, Classical.choice and Quot.sound. The names cbrldlf_exists_small_scale_of_lower_density and cbrldlf_exists_filling_constant collide with no DAG node or existing declaration.
