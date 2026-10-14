# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.uniform_density_bound-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.uniform_density_bound-a1.eventual_threshold-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon 7.3.3, proof of (1), display (2) (book/chapter-07.txt lines 420–428): the bound μ_T(B_ρ(y))/(ω_nρ^n) ≤ m − β/2 near a point x with Θ^n(μ_T, x) < m − β is obtained 'by the monotonicity of 4.7 of Ch. 4'. This lemma is steps 1, 2(ii), 3 and 4 of the parent proof (the choice of a radius at which the monotone quantity is already below ω_nθ₁), with the restriction ρ < σ₀ left to the caller; it uses only its own hypotheses (no Λ ≥ 0 is needed).

Notation: M(ρ) := T.massOn (ball y ρ) ∈ [0, ∞]; ω := unitBallVolume n; ofReal := ENNReal.ofReal; f(ρ) := ofReal(e^{Λρ}/ρ^n)·M(ρ) (the quantity in the conclusion); g(ρ) := M(ρ)/(ω·ofReal(ρ^n)) (the ratio in HasMassDensity). All products, inverses and quotients are taken in [0, ∞].

1. ω ∈ (0, ∞). By definition ω = volume (ball (0 : Euclid n) 1). It is positive because Lebesgue measure on Euclid n is an open-positive measure and the ball of radius 1 > 0 is open and nonempty (Mathlib measure_ball_pos), and it is finite because Euclid n is a proper metric space on which volume is finite on bounded sets (measure_ball_lt_top). Both facts also hold for n = 0. So ω ≠ 0 and ω ≠ ∞.

2. Unfolding the hypothesis. HasMassDensity T y θ means: 0 ≤ θ, and g(ρ) → ofReal(θ) as ρ → 0 along the filter 𝓝[>] 0 (ρ ↓ 0 with ρ > 0). Together with θ < θ₁ this gives θ₁ > θ ≥ 0, so θ₁ > 0.

3. An identity for ρ > 0: f(ρ) = (ofReal(e^{Λρ})·ω)·g(ρ). Fix a real ρ > 0; then ρ^n > 0. By ENNReal.ofReal_div_of_pos, ofReal(e^{Λρ}/ρ^n) = ofReal(e^{Λρ})·b with b := ofReal(ρ^n)^{−1}. By ENNReal.mul_inv (admissible because ω ≠ 0 and ω ≠ ∞), (ω·ofReal(ρ^n))^{−1} = ω^{−1}·b, so g(ρ) = M(ρ)·(ω^{−1}·b). By ENNReal.mul_inv_cancel (ω ≠ 0, ω ≠ ∞), ω·ω^{−1} = 1. Writing a := ofReal(e^{Λρ}) we get, using commutativity and associativity of multiplication in [0, ∞],
   f(ρ) = a·b·M(ρ) = a·b·M(ρ)·(ω·ω^{−1}) = (a·ω)·(M(ρ)·(ω^{−1}·b)) = (ofReal(e^{Λρ})·ω)·g(ρ).

4. Limit of the prefactor. The real function ρ ↦ e^{Λρ} is continuous with value e^0 = 1 at ρ = 0, so e^{Λρ} → 1 along 𝓝 0 and hence along the smaller filter 𝓝[>] 0. Since ofReal is continuous (ENNReal.tendsto_ofReal), ofReal(e^{Λρ}) → ofReal(1) = 1 along 𝓝[>] 0. Multiplying by the constant ω ≠ ∞ (ENNReal.Tendsto.mul_const), ofReal(e^{Λρ})·ω → 1·ω = ω along 𝓝[>] 0.

5. Limit of the product. Apply ENNReal.Tendsto.mul to the limits ofReal(e^{Λρ})·ω → ω (step 4) and g(ρ) → ofReal(θ) (step 2). Its side conditions hold: 'ω ≠ 0 or ofReal(θ) ≠ ∞' holds because ω ≠ 0, and 'ofReal(θ) ≠ 0 or ω ≠ ∞' holds because ω ≠ ∞. Hence (ofReal(e^{Λρ})·ω)·g(ρ) → ω·ofReal(θ) along 𝓝[>] 0.

6. Strict comparison of the limits. Since θ₁ > 0 and θ < θ₁, ofReal(θ) < ofReal(θ₁) (ENNReal.ofReal_lt_ofReal_iff). Multiplication by ω, which is ≠ 0 and ≠ ∞, is strictly monotone on [0, ∞] (ENNReal.mul_lt_mul_iff_right), so ω·ofReal(θ) < ω·ofReal(θ₁).

7. Conclusion. The set {x ∈ [0, ∞] : x < ω·ofReal(θ₁)} is a neighbourhood of the limit ω·ofReal(θ) (order topology; gt_mem_nhds with step 6). By step 5, eventually along 𝓝[>] 0 we have (ofReal(e^{Λρ})·ω)·g(ρ) < ω·ofReal(θ₁). Also eventually along 𝓝[>] 0 we have ρ > 0 (self_mem_nhdsWithin). For every ρ satisfying both, step 3 gives f(ρ) = (ofReal(e^{Λρ})·ω)·g(ρ) < ω·ofReal(θ₁). Since the intersection of two eventually-true properties is eventually true, ∀ᶠ ρ in 𝓝[>] 0, ofReal(e^{Λρ}/ρ^n)·T.massOn (ball y ρ) < unitBallVolume n·ofReal(θ₁). ∎

## Key steps

1. 0 < ω_n < ∞ (measure_ball_pos, measure_ball_lt_top); HasMassDensity T y θ gives θ ≥ 0, hence θ₁ > 0, and g(ρ) = M_{B_ρ(y)}(T)/(ω_n·ofReal(ρ^n)) → ofReal θ along 𝓝[>] 0.
2. For ρ > 0: ofReal(e^{Λρ}/ρ^n)·M_{B_ρ(y)}(T) = (ofReal(e^{Λρ})·ω_n)·g(ρ) (ENNReal.ofReal_div_of_pos, ENNReal.mul_inv, ENNReal.mul_inv_cancel).
3. ofReal(e^{Λρ})·ω_n → ω_n, so by ENNReal.Tendsto.mul the product tends to ω_n·ofReal θ along 𝓝[>] 0.
4. ω_n·ofReal θ < ω_n·ofReal θ₁ (ENNReal.ofReal_lt_ofReal_iff, ENNReal.mul_lt_mul_iff_right), so the quantity is eventually < ω_n·ofReal θ₁.

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
