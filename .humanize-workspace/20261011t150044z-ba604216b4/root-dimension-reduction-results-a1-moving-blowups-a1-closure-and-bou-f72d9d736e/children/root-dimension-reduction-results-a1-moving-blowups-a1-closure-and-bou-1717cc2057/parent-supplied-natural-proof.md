# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.lower_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.local_filling-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 3–6 of the supplied proof (Simon Ch. 6, 8.2 (2)–(4) with the corrections of the closure node's proof: the lower density replaces Θ^{*n}, and the support of the filling is controlled through the isoperimetric/deformation bound), with the same constants. Siblings used: slice = cbrld_sphere_slice_isIntegerMultiplicity (Step 4), radius = dmcbrld_exists_good_slice_radius (Steps 3, 5) and mass_gap = cbrld_im_degree_zero_eq_zero_of_mass_lt_one (Step 6, n = 1).

Notation: n := d + 1, ω_n := unitBallVolume n = L^n(B_1(0)) and w := ω_n read as a real number; for ρ ∈ ℝ, F(ρ) := μ(B_ρ(x₁)) read as a real number; M(·) = mass on ℝ^P read as a real number when finite.

0. (ω_n.) 0 < ω_n < ∞: the unit ball of ℝ^n is bounded, so it has finite Lebesgue measure, and it is a nonempty open set, so its measure is positive. Hence w > 0 and ω_n = w (as an element of [0, ∞]).

1. (Constants; they depend only on P and d.) If d = 0 (n = 1) put η₀ := 1/(4w). If d = m + 1 (n = m + 2 ≥ 2), let c ≥ 1 be the constant given by (ISO) for (P, m), put K₀ := c·(2c)^{1/(m+1)}·(2n)^{n/(m+1)} > 0 and η₀ := min{(2K₀)^{−(m+1)}/w, 1/(4cnw)} > 0; then (i) K₀·(η₀w)^{1/(m+1)} ≤ 1/2 (because η₀w ≤ (2K₀)^{−(m+1)}) and (ii) 4cnη₀w ≤ 1. In both cases put a := (η₀w)^{1/n} > 0, so that a^n = η₀w (for n = 1, a = η₀w = 1/4). η₀ and a are fixed here, before C, μ, ξ, x₁ and δ are chosen.

2. (A small scale.) Fix C, μ, ξ satisfying the hypotheses, x₁ with liminf_{r↓0} μ(B_r(x₁))/(ω_n r^n) < η₀, and δ > 0. By the definition of liminf, μ(B_r(x₁))/(ω_n r^n) < η₀ holds for r in a set that is frequent along r ↓ 0 (frequently_lt_of_liminf_lt), while 0 < r < δ holds eventually; choose s ∈ (0, δ) with μ(B_s(x₁))/(ω_n s^n) < η₀. Since ω_n s^n ∈ (0, ∞), μ(B_s(x₁)) < η₀·ω_n·s^n = η₀w s^n = (as)^n (ENNReal.div_lt_iff).

3. (Good radius and slice.) The sibling slice (with (SL), ∂C = 0, the representation (μ, ξ) and ISP) applied at x₁ gives a Lebesgue-null set N ⊆ ℝ. The sibling radius (with n ≥ 1, a > 0, s > 0, μ(B_s(x₁)) < (as)^n and N) gives ρ ∈ (0, s), ρ ∉ N, with μ(∂B_ρ(x₁)) = 0 and ℓ := liminf_{h↓0} h⁻¹μ({ρ − h < |x − x₁| < ρ}) ≤ b, where b := 2na·F(ρ)^{(n−1)/n} ≥ 0. Applying slice at ρ (ρ > 0, ρ ∉ N) gives A ∈ 𝒟_n(ℝ^P) with A(ω) = ∫_{B_ρ(x₁)} ξ(ω)dμ for all test forms ω, such that Z := ∂A ∈ 𝒟_d(ℝ^P) is integer multiplicity, spt Z ⊆ ∂B_ρ(x₁), and M(Z) ≤ ℓ ≤ b. In particular M(Z) < ∞ and M := M(Z) ≤ b. Moreover F(ρ) ≤ F(s) < (as)^n.

4. (Case n = 1, d = 0.) Here b = 2a·F(ρ)^0 = 2a = 1/2 < 1, so Z is an integer multiplicity 0-current with M(Z) < 1, and the sibling mass_gap (with (MR)) gives Z = 0. Take S := 0 ∈ 𝒟_1(ℝ^P). Then ∂S = 0 = Z = ∂A; M(S) = 0 ≤ ½·μ(B_ρ(x₁)) (every value of S is 0); and spt S = ∅ ⊆ B̄_{(1+3√P)δ}(x₁), since the zero current vanishes on every ball B_1(y), an open set with compact closure, so every y lies in its zero region.

5. (Case n = m + 2 ≥ 2.) Z ∈ 𝒟_{m+1}(ℝ^P) satisfies ∂Z = ∂∂A = 0 (GeometricCurrentOn.boundary_boundary), is integer multiplicity, has M(Z) < ∞, and spt Z is compact: it is closed (the complement of the open zero region) and contained in the compact sphere ∂B_ρ(x₁). By (ISO) for (P, m) there is an integer multiplicity Y ∈ 𝒟_{m+2}(ℝ^P) = 𝒟_n(ℝ^P) with ∂Y = Z, M(Y) ≤ c(2cM)^{1/(m+1)}M and spt Y ⊆ thickening(3√P(2cM)^{1/(m+1)}, spt Z). Take S := Y, so ∂S = Z = ∂A.
(a) Mass. Since 0 ≤ M ≤ b and n/(m+1) > 0: c(2cM)^{1/(m+1)}M = c(2c)^{1/(m+1)}M^{1/(m+1)}M^1 = c(2c)^{1/(m+1)}M^{1/(m+1)+1} = c(2c)^{1/(m+1)}M^{n/(m+1)} (Real.mul_rpow for the nonnegative factors 2c and M, and Real.rpow_add', which needs only M ≥ 0 and 1/(m+1) + 1 ≠ 0, so it also covers M = 0) ≤ c(2c)^{1/(m+1)}b^{n/(m+1)} (Real.rpow_le_rpow), and b^{n/(m+1)} = (2n)^{n/(m+1)}·a^{n/(m+1)}·(F(ρ)^{(m+1)/n})^{n/(m+1)} = (2n)^{n/(m+1)}(η₀w)^{1/(m+1)}F(ρ) (a^{n/(m+1)} = ((η₀w)^{1/n})^{n/(m+1)} = (η₀w)^{1/(m+1)}). Hence c(2cM)^{1/(m+1)}M ≤ K₀(η₀w)^{1/(m+1)}F(ρ) ≤ F(ρ)/2 by (i), and M(S) ≤ ENNReal.ofReal(F(ρ)/2) = ½·μ(B_ρ(x₁)).
(b) Support. Since F(ρ) < (as)^n and u ↦ u^{(m+1)/n} is monotone on [0, ∞), b = 2na·F(ρ)^{(m+1)/n} ≤ 2na(as)^{m+1} = 2n·a^n·s^{m+1} = 2nη₀w·s^{m+1}. Hence 2cM ≤ 4cnη₀w·s^{m+1} ≤ s^{m+1} by (ii), so (2cM)^{1/(m+1)} ≤ s. If y ∈ spt S, there is z ∈ spt Z ⊆ ∂B_ρ(x₁) with |y − z| < 3√P(2cM)^{1/(m+1)} ≤ 3√P·s (Metric.mem_thickening_iff), so |y − x₁| < ρ + 3√P·s ≤ (1 + 3√P)δ because ρ < s < δ. Thus spt S ⊆ B̄_{(1+3√P)δ}(x₁).

6. (Conclusion.) In both cases 0 < ρ < s < δ, μ(∂B_ρ(x₁)) = 0, A(ω) = ∫_{B_ρ(x₁)} ξ(ω)dμ for all ω, ∂S = ∂A, M(S) ≤ ½·μ(B_ρ(x₁)) and spt S ⊆ B̄_{(1+3√P)δ}(x₁). ∎

## Key steps

1. Constants depending only on (P, d): η₀ = 1/(4ω_1) if n = 1; for n = m+2, η₀ with K₀(η₀ω_n)^{1/(m+1)} ≤ 1/2 and 4cnη₀ω_n ≤ 1 (c from (ISO)); a := (η₀ω_n)^{1/n}.
2. From the liminf hypothesis pick s ∈ (0, δ) with μ(B_s(x₁)) < (as)^n.
3. slice gives the null set N; radius gives ρ ∈ (0, s) ∖ N with μ(∂B_ρ(x₁)) = 0 and slice liminf ≤ 2naF(ρ)^{(n−1)/n}; slice at ρ gives A = C⌞B_ρ(x₁) with Z = ∂A integer multiplicity, spt Z ⊆ ∂B_ρ(x₁), M(Z) ≤ 2naF(ρ)^{(n−1)/n}.
4. n = 1: M(Z) ≤ 1/2, so Z = 0 by mass_gap and S := 0.
5. n ≥ 2: (ISO) gives S with ∂S = Z, M(S) ≤ K₀(η₀ω_n)^{1/(m+1)}F(ρ) ≤ F(ρ)/2 and spt S within 3√P·s of ∂B_ρ(x₁), hence in B̄_{(1+3√P)δ}(x₁).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD; cmp snapshot project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean`
- `rg -c 'dmcbrld|cbrld_' over the snapshot (no match, exit 1); grep -rl dmcbrld_ over GMT/, .lake/packages/simongmt and RUN/nodes (no match)`
- `rg -n 'theorem exists_disjoint_closedBall_covering_ae|theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc|theorem MonotoneOn.intervalIntegrable_deriv|theorem Monotone.ae_differentiableAt|theorem measurable_deriv|theorem countable_meas_pos_of_disjoint_iUnion|theorem hausdorffMeasure_zero_singleton|theorem ae_iff|theorem measure_iUnion_null' over snapshot mathlib/Mathlib (all found: Besicovitch.lean:833, DerivIntegrable.lean:86/100, Monotone.lean:209, FDeriv/Measurable.lean:398, SFinite.lean:305, Hausdorff.lean:628, OuterMeasure/AE.lean:134)`
- `python3 -I scans of RUN/dag.json: twin node root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1 has a byte-identical frozen type; statuses, candidate commits and frozen types of its 7 children and grandchildren; cbr_isoperimetric_filling and dmcbr_isoperimetric_filling types identical; (VO), (SL), (DT) types occur verbatim in the selected type; fresh-name collision check over 1598 nodes`
- `sed of RUN/nodes/…b16b774435/decomposition-v1.json and decomposition-audit-v1.json (twin split and its passing audit); difflib comparison of the two supplied natural proofs`
- `git show b82dc736 (twin parent assembly draft), 909d2bdf (local_filling draft), 6bf34ee2 (null_set draft); git log of the twin radius worktree (215074ec7 proves cbrld_exists_good_slice_radius)`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py: _existing_lean_name_problem, _accepted_checkpoint, _solve_children, _reference_use_problem`
- `sed of .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean (massAdmissibleOn, massOn, mass, le_massOn, WeaklyConvergesOn.massOn_le_liminf) and Currents.lean (zeroRegion, support)`
- `lake env lean /tmp/dmcbrld_work/lean/Types.lean, Assembly.lean (#print axioms: propext, Classical.choice, Quot.sound), WiringLF.lean, WiringNS.lean, Names.lean; verifier/lean_contract.py validate_lean_statement on the 7 child types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-f72d9d736e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b16b774435/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b16b774435/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b16b774435/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/tmp/dmcbrld_work/lean/Types.lean`
- `/tmp/dmcbrld_work/lean/Assembly.lean`
- `/tmp/dmcbrld_work/lean/WiringLF.lean`
- `/tmp/dmcbrld_work/lean/WiringNS.lean`

The pins match: HEAD b4d606d equals the snapshot project commit, Mathlib is 25730c7c, and Submission.lean is byte-identical to the frozen contract and its snapshot copy. The snapshot has no dmcbrld_ or cbrld_ declaration and no lower-density, covering or slicing theorem, so the split is needed. Every cited Mathlib lemma exists in the snapshot. MonotoneOn.intervalIntegral_deriv_mem_uIcc and intervalIntegrable_deriv live in a module that GMT.Ch07.Submission does not import; the radius proof says so and gives the lintegral alternative. The twin lower_density node has the same frozen type and a passing audit. Its four accepted children are reused by exact name with identical types; its three unaccepted children get fresh dmcbrld_ names, which collide with nothing. All 7 types elaborate. The assembly proves the exact parent type using only propext, Classical.choice and Quot.sound. The wiring drafts of local_filling and null_set typecheck against their declared siblings.
