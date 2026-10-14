# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.uniform_density_bound-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.uniform_density_bound-a1.nearby_center_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon 7.3.3, proof of (1), display (2) (book/chapter-07.txt lines 420–428), where the bound at a centre x is transferred to all y ∈ B_σ(x) 'by the monotonicity of 4.7 of Ch. 4'. This lemma is step 6(b)–(e) of the parent proof together with identity 2(i), with the radius r = ρ_y and shift τ = τ_y as free parameters. Neither positivity nor finiteness of ω_n nor any sign condition on θ₁, θ₂ is used.

Notation: M(z, ρ) := T.massOn (ball z ρ) ∈ [0, ∞]; ω := unitBallVolume n; ofReal := ENNReal.ofReal; f_z(ρ) := ofReal(e^{Λρ}/ρ^n)·M(z, ρ). Products are taken in [0, ∞] and are monotone in each factor. Hypotheses: (H1) Λ ≥ 0; (H2) 0 < τ; (H3) τ < r; (H4) dist(y', y) < τ; (H5) θ₁·(r/(r − τ))^n ≤ θ₂; (H6) f_{y'} is monotone on (0, r); (H7) f_y(r) ≤ ω·ofReal(θ₁). Fix ρ with 0 < ρ < r − τ, and put s := r − τ.

1. Elementary facts. r > 0 (from H2 and H3), 0 < s (H3) and s < r (H2). Hence ρ ∈ (0, r) (0 < ρ < s < r), s ∈ (0, r), and ρ ≤ s.

2. Monotonicity at the centre y'. By (H6) and step 1, f_{y'}(ρ) ≤ f_{y'}(s).

3. Enlarging the exponential factor and the ball: f_{y'}(s) = ofReal(e^{Λs}/s^n)·M(y', s) ≤ ofReal(e^{Λr}/s^n)·M(y, r).
   - First factor: Λr − Λs = Λτ ≥ 0 by (H1) and (H2), so Λs ≤ Λr and e^{Λs} ≤ e^{Λr} (exp is monotone). Since s^n ≥ 0, dividing by s^n preserves the inequality (div_le_div_of_nonneg_right), and ofReal is monotone (ENNReal.ofReal_le_ofReal): ofReal(e^{Λs}/s^n) ≤ ofReal(e^{Λr}/s^n).
   - Second factor: s + dist(y', y) ≤ s + τ = r by (H4), so ball y' s ⊆ ball y r (Metric.ball_subset_ball'), and T.massOn is monotone in its set argument (SimonGMT GeometricCurrentOn.massOn_mono): M(y', s) ≤ M(y, r).
   - Multiply the two inequalities (monotonicity of multiplication in [0, ∞]).

4. Rescaling to radius r at the centre y. Put q := (r/s)^n; q ≥ 0 because r > 0 and s > 0. The real identity e^{Λr}/s^n = q·(e^{Λr}/r^n) holds because (r/s)^n = r^n/s^n (div_pow) and r^n ≠ 0, s^n ≠ 0 (field_simp). By ENNReal.ofReal_mul (its first factor q is ≥ 0), ofReal(e^{Λr}/s^n) = ofReal(q)·ofReal(e^{Λr}/r^n). Therefore
   ofReal(e^{Λr}/s^n)·M(y, r) = ofReal(q)·f_y(r)   (associativity)
   ≤ ofReal(q)·(ω·ofReal(θ₁))   (H7)
   = ofReal(θ₁·q)·ω   (θ₁·q = q·θ₁ and ENNReal.ofReal_mul with q ≥ 0 give ofReal(θ₁·q) = ofReal(q)·ofReal(θ₁); then commutativity)
   ≤ ofReal(θ₂)·ω   (H5 says θ₁·q ≤ θ₂; ofReal is monotone).

5. Back to the mass at y'. Since ρ > 0, ρ^n > 0 and e^{Λρ} > 0, so the real identity (ρ^n/e^{Λρ})·(e^{Λρ}/ρ^n) = 1 holds. By ENNReal.ofReal_mul (ρ^n/e^{Λρ} ≥ 0) and ofReal(1) = 1,
   M(y', ρ) = ofReal(ρ^n/e^{Λρ})·ofReal(e^{Λρ}/ρ^n)·M(y', ρ) = ofReal(ρ^n/e^{Λρ})·f_{y'}(ρ).
   Moreover Λρ ≥ 0 (H1, ρ > 0), so e^{Λρ} ≥ 1 (Real.one_le_exp), hence ρ^n/e^{Λρ} ≤ ρ^n (div_le_self, ρ^n ≥ 0) and ofReal(ρ^n/e^{Λρ}) ≤ ofReal(ρ^n).

6. Conclusion. By steps 2, 3 and 4, f_{y'}(ρ) ≤ f_{y'}(s) ≤ ofReal(e^{Λr}/s^n)·M(y, r) ≤ ofReal(θ₂)·ω. With step 5,
   M(y', ρ) = ofReal(ρ^n/e^{Λρ})·f_{y'}(ρ) ≤ ofReal(ρ^n)·(ofReal(θ₂)·ω) = ofReal(θ₂)·ω·ofReal(ρ^n),
   i.e. T.massOn (ball y' ρ) ≤ ENNReal.ofReal θ₂ * unitBallVolume n * ENNReal.ofReal (ρ ^ n). ∎

## Key steps

1. With s = r − τ ∈ (0, r) and 0 < ρ ≤ s: monotonicity at y' gives f_{y'}(ρ) ≤ f_{y'}(s).
2. Λ ≥ 0 gives e^{Λs} ≤ e^{Λr}; B_s(y') ⊆ B_r(y) since s + |y' − y| < r, and massOn_mono: f_{y'}(s) ≤ ofReal(e^{Λr}/s^n)·M_{B_r(y)}(T).
3. e^{Λr}/s^n = (r/s)^n·e^{Λr}/r^n, ENNReal.ofReal_mul and the bound at y give ≤ ofReal(θ₁(r/s)^n)·ω_n ≤ ofReal(θ₂)·ω_n.
4. M_{B_ρ(y')}(T) = ofReal(ρ^n/e^{Λρ})·f_{y'}(ρ) and e^{Λρ} ≥ 1 give M_{B_ρ(y')}(T) ≤ ofReal(θ₂)·ω_n·ofReal(ρ^n).

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
