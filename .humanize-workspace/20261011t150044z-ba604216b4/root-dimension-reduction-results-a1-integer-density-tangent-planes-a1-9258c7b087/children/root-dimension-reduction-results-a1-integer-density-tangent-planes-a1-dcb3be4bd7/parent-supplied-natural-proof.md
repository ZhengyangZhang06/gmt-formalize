# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.uniform_density_bound-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.uniform_density_bound-a1.local_uniform_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon 7.3.3, proof of (1), display (2) (book/chapter-07.txt lines 420–428): for each point x with Θ^n(μ_T, x) < m − β there is a ball B_{2σ}(x) on which μ_T(B_ρ(y))/(ω_nρ^n) ≤ m − β/2 for all ρ < σ and y ∈ B_σ(x). This lemma is exactly that pointwise statement, i.e. steps 3–6 of the parent proof for one point y; it uses the sibling lemmas idod_monotone_quantity_eventually_lt (C1, steps 1–4) and idod_nearby_center_ball_mass_bound (C2, step 6(b)–(e)).

Notation: M(z, ρ) := T.massOn (ball z ρ); ω := unitBallVolume n; ofReal := ENNReal.ofReal; f_z(ρ) := ofReal(e^{Λρ}/ρ^n)·M(z, ρ), the function in the monotonicity hypothesis. Hypotheses: Λ ≥ 0, σ₀ > 0, θ < θ₁, θ₁ < θ₂, HasMassDensity T y θ, closedBall y (2σ₀) ⊆ K'', and (Mono): for all z and R with closedBall z R ⊆ K'', f_z is monotone on (0, R).

1. Choice of the radius r (= ρ_y of the parent proof). By C1 (Submission.idod_monotone_quantity_eventually_lt) applied to P, n, U, T, y, Λ, θ, θ₁ with the hypotheses HasMassDensity T y θ and θ < θ₁, the property f_y(ρ) < ω·ofReal(θ₁) holds eventually along the filter 𝓝[>] 0 on ℝ. Since σ₀ > 0, the interval (0, σ₀) belongs to 𝓝[>] 0 (Ioo_mem_nhdsGT). The conjunction of the two properties holds eventually along 𝓝[>] 0, and 𝓝[>] 0 on ℝ is a nontrivial filter, so some r satisfies both: f_y(r) < ω·ofReal(θ₁) and 0 < r < σ₀.

2. Choice of the shift τ (= τ_y of the parent proof). Let h(t) := θ₁·(r/(r − t))^n for t ∈ ℝ. The map t ↦ r − t is continuous with value r ≠ 0 at t = 0, so t ↦ r/(r − t) is continuous at 0 (quotient of continuous functions with nonzero denominator at 0); powers and multiplication by the constant θ₁ preserve continuity at 0. Thus h is continuous at 0, and h(0) = θ₁·(r/r)^n = θ₁·1 = θ₁ < θ₂. Hence {t : h(t) < θ₂} is a neighbourhood of 0, so it belongs to 𝓝[>] 0 (since 𝓝[>] 0 ≤ 𝓝 0). Also (0, r) ∈ 𝓝[>] 0 because r > 0. By nontriviality of 𝓝[>] 0 there is τ with 0 < τ < r and θ₁·(r/(r − τ))^n < θ₂.

3. Put δ := min(τ, r − τ). Then δ > 0, because τ > 0 and r − τ > 0.

4. Fix y' ∈ ball y δ and ρ with 0 < ρ < δ. Then dist(y', y) < δ ≤ τ, and ρ < δ ≤ r − τ.

5. Monotonicity at the centre y'. We have r + dist(y', y) < r + τ < 2r < 2σ₀ (using τ < r < σ₀), so closedBall y' r ⊆ closedBall y (2σ₀) (Metric.closedBall_subset_closedBall'), and hence closedBall y' r ⊆ K'' by hypothesis. By (Mono) with z := y' and R := r, f_{y'} is monotone on (0, r).

6. Conclusion via C2. Apply C2 (Submission.idod_nearby_center_ball_mass_bound) to P, n, U, T, y, y', Λ, r, τ, θ₁, θ₂. Its hypotheses hold: 0 ≤ Λ; 0 < τ and τ < r (step 2); dist(y', y) < τ (step 4); θ₁·(r/(r − τ))^n ≤ θ₂ (step 2, strict inequality weakened); f_{y'} monotone on (0, r) (step 5); f_y(r) ≤ ω·ofReal(θ₁) (step 1, strict inequality weakened). Since 0 < ρ < r − τ (step 4), C2 yields T.massOn (ball y' ρ) ≤ ENNReal.ofReal θ₂ * unitBallVolume n * ENNReal.ofReal (ρ ^ n). As y' ∈ ball y δ and ρ ∈ (0, δ) were arbitrary, δ has the required property. ∎

## Key steps

1. C1 together with (0, σ₀) ∈ 𝓝[>] 0 gives r ∈ (0, σ₀) with ofReal(e^{Λr}/r^n)·M_{B_r(y)}(T) < ω_n·ofReal θ₁.
2. Continuity of t ↦ θ₁(r/(r − t))^n at t = 0 (value θ₁ < θ₂) gives τ ∈ (0, r) with θ₁(r/(r − τ))^n < θ₂.
3. δ := min(τ, r − τ) > 0; for y' ∈ B_δ(y): closedBall y' r ⊆ closedBall y (2σ₀) ⊆ K'', so the monotonicity hypothesis holds at y' on (0, r).
4. C2 with (y, y', Λ, r, τ, θ₁, θ₂) gives M_{B_ρ(y')}(T) ≤ ofReal θ₂·ω_n·ofReal(ρ^n) for 0 < ρ < δ ≤ r − τ.

## Reference use

### local-project

Queries:
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with local-references/123e8435b4a2469b/manifest.json)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `grep -n 'unitBallVolume\|HasMassDensity' GMT/Ch07/Contract.lean (lines 143, 147-149)`
- `python3 scan of dag.json: nodes whose lean_statement contains 'Real.exp' and 'massOn'; lean_name lookup for idod_monotone_quantity_eventually_lt, idod_nearby_center_ball_mass_bound, idod_local_uniform_ball_mass_bound (re-run at updated_at 2026-10-13T12:48:19Z, 1207 nodes)`
- `grep -rho 'idod_[A-Za-z0-9_]*' nodes/ decomposition-reopenings/; grep -rn for the three new names in GMT/ and .lake/packages/simongmt (no match)`
- `git show c6671eb41:GMT/Ch07/Submission.lean (accepted proof of Submission.dimred_mono_density_usc_of_monotone, lines 462-598)`
- `rg -n 'theorem measure_ball_pos|theorem measure_ball_lt_top|theorem ball_subset_ball.|theorem closedBall_subset_closedBall.|theorem IsCompact.elim_nhds_subcover|theorem div_le_self|theorem one_le_exp' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'protected theorem Tendsto\.mul\b|protected theorem Tendsto\.mul_const|theorem ofReal_div_of_pos|protected theorem mul_inv\b|protected theorem mul_inv_cancel|theorem ofReal_lt_ofReal_iff\b|theorem tendsto_ofReal\b|theorem ofReal_mul\b|theorem ofReal_le_ofReal\b|theorem ofReal_one\b' mathlib/Mathlib/Basic/ENNReal mathlib/Mathlib/Topology/Instances/ENNReal`
- `sed -n 55,90p mathlib/Mathlib/Basic/ENNReal/Operations.lean; sed -n 278,284p mathlib/Mathlib/Topology/Order/OrderClosed.lean; sed -n 560,563p and 755,759p mathlib/Mathlib/Data/Finset/Lattice/Fold.lean; grep eq_empty_or_nonempty Data/Finset/Empty.lean; grep mem_iUnion₂ Data/Set/Lattice/Indexed.lean`
- `sed -n 78,90p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean (GeometricCurrentOn.massOn_mono)`
- `grep -n 'Proof of 3.3(1)\|monotonicity of 4.7' book/chapter-07.txt book/sources/chapter-07-source.txt (lines 420, 424)`
- `lake env lean /tmp/udb_check/Stmts.lean, C1.lean, C2.lean, All.lean, FromJson.lean, Assembly.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-9258c7b087/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Field/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Finset/Lattice/Fold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Finset/Empty.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Lattice/Indexed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/udb_check/json/subproblems.json`
- `/tmp/udb_check/FromJson.lean`
- `/tmp/udb_check/Assembly.lean`

Pins match. The manifest records project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d, equal to the workspace HEAD and .lake/packages/mathlib HEAD; SimonGMT is at 2b3663083f3fe399b6296fb8eaee52169170e197. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (unitBallVolume at line 143, HasMassDensity at 147-149).

Library support used by the children, all present in the snapshot:
- measure_ball_pos (MeasureTheory/Measure/OpenPos.lean:212) and measure_ball_lt_top (Typeclasses/Finite.lean:373).
- ENNReal: mul_inv_cancel (Basic/ENNReal/Inv.lean:103), mul_inv (Inv.lean:245), ofReal_div_of_pos (Inv.lean:960), ofReal_le_ofReal (Basic/ENNReal/Real.lean:137), ofReal_lt_ofReal_iff (Real.lean:167), ofReal_mul (Real.lean:297, first factor nonnegative), ofReal_one (Basic/ENNReal/Basic.lean:299), mul_lt_mul_iff_right (Basic/ENNReal/Operations.lean:83).
- ENNReal topology: tendsto_ofReal, Tendsto.mul, Tendsto.mul_const (Topology/Instances/ENNReal/Lemmas.lean:72, 337, 359).
- Metric balls: ball_subset_ball' and closedBall_subset_closedBall' (Topology/MetricSpace/Pseudo/Defs.lean:537, 547).
- Compactness and filters: IsCompact.elim_nhds_subcover (Topology/Compactness/Compact.lean:236); Ioo_mem_nhdsGT, the to_dual of Ioo_mem_nhdsLT (Topology/Order/OrderClosed.lean:281-282).
- Real analysis: div_le_self (Algebra/Order/Field/Basic.lean:84), Real.one_le_exp (Analysis/Complex/Exponential.lean:280).
- Finsets and sets: Finset.inf'_le and lt_inf'_iff via to_dual (Data/Finset/Lattice/Fold.lean:562, 757), Finset.eq_empty_or_nonempty (Data/Finset/Empty.lean:152), mem_iUnion₂ (Data/Set/Lattice/Indexed.lean:33).
- SimonGMT: GeometricCurrentOn.massOn_mono (Chapter06/Mass.lean:81).

DAG and reuse:
- The only accepted node with a related monotone-quantity argument is dimred_mono_density_usc_of_monotone (commit c6671eb41). It has a different type, so it cannot be reused, but it confirms the ENNReal idioms work at this pin.
- No existing node or declaration has the type of C1, C2 or C3.
- The names idod_monotone_quantity_eventually_lt, idod_nearby_center_ball_mass_bound and idod_local_uniform_ball_mass_bound do not occur in dag.json (1207 nodes at 2026-10-13T12:48:19Z), GMT/, SimonGMT or git history. The selected node is still 'decomposing' with no children.
- Book lines 420-428 of chapter-07.txt contain the proof of 3.3(1) and display (2), as cited.

Lean checks:
- All child statements elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07 with the contract opens.
- FromJson.lean proves all three children and the frozen parent type from them, with axioms [propext, Classical.choice, Quot.sound] only and no sorryAx.
- Assembly.lean, with C1 and C2 as axioms, shows that C3 and the parent use only those two.
- An independent reviewer reproduced these results, including a parent proof from C3 alone, and accepted.
