# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.uniform_density_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon 7.3.3, proof of (1), display (2) (chapter-07.txt lines 420–428): from 'the monotonicity of 4.7 of Ch. 4' the book obtains, for x ∈ U_{m,β}, a ball B_{2σ}(x) ⊆ U_{m,β} with μ_T(B_ρ(y))/(ω_nρ^n) ≤ m − β/2 for all ρ < σ and y ∈ B_σ(x). This is step 2 of the parent proof with every detail supplied; it uses only the stated hypotheses (no minimality, no prerequisite DAG result).

Notation:
- M(y, ρ) := T.massOn (ball y ρ) ∈ [0, ∞]; ω := unitBallVolume n; ofReal = ENNReal.ofReal; all products and quotients below are in [0, ∞] unless stated otherwise.
- f_y(ρ) := ofReal(e^{Λρ}/ρ^n)·M(y, ρ), the function in the monotonicity hypothesis.
- g_y(ρ) := M(y, ρ)/(ω·ofReal(ρ^n)), the ratio in HasMassDensity.

1. ω ∈ (0, ∞). ω is the Lebesgue measure of the open unit ball of Euclid n. It is positive because volume is an open-positive measure and the ball is open and nonempty (Mathlib measure_ball_pos), and finite because Euclid n is a proper space and volume is finite on bounded sets (measure_ball_lt_top). Both facts hold also for n = 0.

2. Two identities, valid for every y ∈ ℝ^P and every real ρ > 0.
   (i) M(y, ρ) = ofReal(ρ^n/e^{Λρ})·f_y(ρ). Indeed ofReal(ρ^n/e^{Λρ})·ofReal(e^{Λρ}/ρ^n) = ofReal((ρ^n/e^{Λρ})·(e^{Λρ}/ρ^n)) = ofReal(1) = 1 (ENNReal.ofReal_mul; both real factors are ≥ 0, and ρ^n > 0, e^{Λρ} > 0).
   (ii) f_y(ρ) = (ofReal(e^{Λρ})·ω)·g_y(ρ). Indeed ofReal(e^{Λρ}/ρ^n) = ofReal(e^{Λρ})·ofReal(ρ^n)^{−1} (ENNReal.ofReal_div_of_pos, ρ^n > 0); (ω·ofReal(ρ^n))^{−1} = ω^{−1}·ofReal(ρ^n)^{−1} (ENNReal.mul_inv, using ω ≠ 0 and ω ≠ ∞); and ω·ω^{−1} = 1 (ENNReal.mul_inv_cancel). Rearranging the commutative product gives the identity.

3. Fix y ∈ K. By hypothesis choose θ_y < θ₁ with HasMassDensity T y θ_y, i.e. θ_y ≥ 0 and g_y(ρ) → ofReal(θ_y) as ρ → 0 along the filter 𝓝[>] 0 (ρ ↓ 0, ρ > 0). In particular θ₁ > θ_y ≥ 0.

4. Choice of ρ_y.
   - ρ ↦ ofReal(e^{Λρ}) is continuous on ℝ with value ofReal(e^0) = 1 at ρ = 0, so ofReal(e^{Λρ}) → 1 along 𝓝[>] 0, and ofReal(e^{Λρ})·ω → 1·ω = ω (ENNReal.Tendsto.mul_const, using ω ≠ ∞).
   - By ENNReal.Tendsto.mul (admissible because the first limit ω is ≠ 0 and ≠ ∞), (ofReal(e^{Λρ})·ω)·g_y(ρ) → ω·ofReal(θ_y).
   - Since θ_y < θ₁ and θ₁ > 0, ofReal(θ_y) < ofReal(θ₁) (ENNReal.ofReal_lt_ofReal_iff), hence ω·ofReal(θ_y) < ω·ofReal(θ₁) because ω ∈ (0, ∞) (ENNReal.mul_lt_mul_iff_right).
   - Therefore the set of ρ with (ofReal(e^{Λρ})·ω)·g_y(ρ) < ω·ofReal(θ₁) belongs to 𝓝[>] 0 (order topology: tendsto_order), and so does the interval (0, σ₀) (σ₀ > 0). The filter 𝓝[>] 0 on ℝ is nontrivial, so there is ρ_y in both sets: 0 < ρ_y < σ₀ and, by identity 2(ii), f_y(ρ_y) < ω·ofReal(θ₁).

5. Choice of τ_y. The real function τ ↦ θ₁·(ρ_y/(ρ_y − τ))^n is continuous at τ = 0 (its denominator ρ_y − 0 = ρ_y is nonzero) and its value there is θ₁·1 = θ₁ < θ₂. Hence θ₁·(ρ_y/(ρ_y − τ))^n < θ₂ for all τ in a neighbourhood of 0; intersecting with (0, ρ_y) ∈ 𝓝[>] 0 gives τ_y with 0 < τ_y < ρ_y and θ₁·(ρ_y/(ρ_y − τ_y))^n < θ₂.

6. Local bound: for every y' with |y' − y| < τ_y and every ρ with 0 < ρ < ρ_y − τ_y, M(y', ρ) ≤ ofReal(θ₂)·ω·ofReal(ρ^n).
   (a) closedBall y' ρ_y ⊆ K''. If |w − y'| ≤ ρ_y then |w − y| ≤ ρ_y + |y' − y| < ρ_y + τ_y < 2σ₀ (both ρ_y and τ_y are < σ₀), so w ∈ closedBall y (2σ₀) ⊆ K'' (hypothesis, y ∈ K). By the monotonicity hypothesis with the centre y' and R := ρ_y, f_{y'} is monotone on (0, ρ_y).
   (b) Both ρ and ρ_y − τ_y lie in (0, ρ_y), and ρ ≤ ρ_y − τ_y, so f_{y'}(ρ) ≤ f_{y'}(ρ_y − τ_y).
   (c) f_{y'}(ρ_y − τ_y) ≤ ofReal(e^{Λρ_y}/(ρ_y − τ_y)^n)·M(y, ρ_y). First factor: Λ(ρ_y − τ_y) ≤ Λρ_y because Λ ≥ 0 and τ_y > 0, so e^{Λ(ρ_y−τ_y)} ≤ e^{Λρ_y}; divide by (ρ_y − τ_y)^n > 0 and use that ofReal is monotone. Second factor: B_{ρ_y−τ_y}(y') ⊆ B_{ρ_y}(y) because (ρ_y − τ_y) + |y' − y| < ρ_y (Metric.ball_subset_ball'), and T.massOn is monotone in its set argument (SimonGMT GeometricCurrentOn.massOn_mono).
   (d) The real identity e^{Λρ_y}/(ρ_y − τ_y)^n = (ρ_y/(ρ_y − τ_y))^n·(e^{Λρ_y}/ρ_y^n) (div_pow, cancel ρ_y^n ≠ 0) and ENNReal.ofReal_mul (the factor (ρ_y/(ρ_y − τ_y))^n is ≥ 0 since ρ_y > 0 and ρ_y − τ_y > 0) give
       ofReal(e^{Λρ_y}/(ρ_y − τ_y)^n)·M(y, ρ_y) = ofReal((ρ_y/(ρ_y − τ_y))^n)·f_y(ρ_y)
       ≤ ofReal((ρ_y/(ρ_y − τ_y))^n)·(ω·ofReal(θ₁))   (step 4)
       = ofReal(θ₁·(ρ_y/(ρ_y − τ_y))^n)·ω   (ENNReal.ofReal_mul with θ₁ ≥ 0, commutativity)
       ≤ ofReal(θ₂)·ω   (step 5 and monotonicity of ofReal).
   (e) By (b), (c), (d): f_{y'}(ρ) ≤ ofReal(θ₂)·ω. Moreover e^{Λρ} ≥ 1 (Λρ ≥ 0), so ρ^n/e^{Λρ} ≤ ρ^n (div_le_self). By identity 2(i):
       M(y', ρ) = ofReal(ρ^n/e^{Λρ})·f_{y'}(ρ) ≤ ofReal(ρ^n)·(ofReal(θ₂)·ω) = ofReal(θ₂)·ω·ofReal(ρ^n).

7. Compactness. For (ρ, y') ∈ ℝ × ℝ^P let Φ(ρ, y') be the statement [0 < ρ ⇒ M(y', ρ) ≤ ofReal(θ₂)·ω·ofReal(ρ^n)].
   - By step 6, for each y ∈ K, Φ holds on the neighbourhood B_{ρ_y−τ_y}(0) × B_{τ_y}(y) of (0, y) in ℝ × ℝ^P (if 0 < ρ and |ρ| < ρ_y − τ_y then ρ < ρ_y − τ_y).
   - Since K is compact, Mathlib's IsCompact.eventually_forall_of_forall_eventually (at x₀ := 0 ∈ ℝ) gives a neighbourhood of 0 in ℝ on which ρ ↦ [∀ y ∈ K, Φ(ρ, y)] holds; by Metric.eventually_nhds_iff there is ε > 0 such that Φ(ρ, y) for all |ρ| < ε and y ∈ K. (Equivalently: cover K by finitely many balls B_{τ_{y_j}}(y_j) and take ε := min_j (ρ_{y_j} − τ_{y_j}); if K = ∅ any ε > 0 works.)
   - Put ρ₀ := ε > 0. If y ∈ K and 0 < ρ < ρ₀, then |ρ| = ρ < ε, so Φ(ρ, y) gives T.massOn (ball y ρ) ≤ ofReal(θ₂)·unitBallVolume n·ofReal(ρ^n). ∎

## Key steps

1. ω_n = unitBallVolume n ∈ (0, ∞). For ρ > 0: M(y, ρ) = ofReal(ρ^n/e^{Λρ})·f_y(ρ) and f_y(ρ) = (ofReal(e^{Λρ})·ω_n)·g_y(ρ), where f_y is the monotone quantity and g_y the density ratio.
2. For y ∈ K with density θ_y < θ₁: the limit g_y → ofReal(θ_y) and e^{Λρ} → 1 give ρ_y ∈ (0, σ₀) with f_y(ρ_y) < ω_n·ofReal(θ₁).
3. Continuity at τ = 0 gives τ_y ∈ (0, ρ_y) with θ₁(ρ_y/(ρ_y − τ_y))^n < θ₂.
4. For |y' − y| < τ_y and 0 < ρ < ρ_y − τ_y: monotonicity at y' (closedBall y' ρ_y ⊆ closedBall y (2σ₀) ⊆ K''), B_{ρ_y−τ_y}(y') ⊆ B_{ρ_y}(y), Λ ≥ 0 and e^{Λρ} ≥ 1 give M(y', ρ) ≤ ofReal(θ₂)·ω_n·ofReal(ρ^n).
5. Compactness of K (IsCompact.eventually_forall_of_forall_eventually, or a finite subcover by the balls B_{τ_y}(y)) yields a common ρ₀ > 0.

## Reference use

### local-project

Queries:
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with local-references/123e8435b4a2469b/manifest.json)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `git show fb9bfaa2bb3b6a2fb2c8d2c902f098a63fc92f2d:GMT/Ch07/Submission.lean (layout of the accepted theorem Submission.idtp_convergesWeakly_massOn_le)`
- `python3 scan of dag.json: lean_statement/status of dimred_im_mass_measure, dimred_minimizing_monotonicity, dimred_threshold_reduction, dimred_invariant_cone_splitting, dimred_one_dim_minimizing_cone, dtc_blowUp_massOn_image, idtp_convergesWeakly_massOn_le, idtp_imrep_measure_density_ae, idtp_two_dim_cone_integer_density, dimred_cs_mi_hasMassDensity_unique; dependency lists of the parent and grandparent nodes`
- `grep -c 'idod_' dag.json DAG.md dag.mmd issue-workers.json problem.json (all 0); grep -rl 'idod_' nodes/ decomposition-reopenings/ (only this node's decomposition-v1/audit/receipt); grep -rl 'idod_' local-references/123e8435b4a2469b/project .lake/packages/simongmt (no match); git log --all -S 'idod_' (no match)`
- `grep -rn 'theorem measure_null_of_locally_null|theorem IsCompact.eventually_forall_of_forall_eventually|theorem upperSemicontinuousOn_iff_preimage_Iio|protected lemma mul_lt_mul_iff_right|lemma withDensity_zero_left|theorem measure_ball_pos|theorem measure_ball_lt_top|theorem ofReal_div_of_pos|protected theorem Tendsto.mul|theorem le_of_tendsto|theorem mul_le_mul_right' local-references/123e8435b4a2469b/mathlib/Mathlib; grep -n 'theorem GeometricCurrentOn.massOn_mono' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `sed -n 360,520p book/chapter-07.txt (Simon 7.3.3, Remark 3.4, Lemma 3.5, proof of 3.3(1), displays (1)-(15))`
- `lake env lean /tmp/idod2/check/Probe.lean (#check of the library lemmas)`
- `lake env lean /tmp/idod2/check/Assembly.lean (#print axioms check_parent)`
- `lake env lean /tmp/idod2/check/Leaves1.lean (#print axioms check_C1, check_C2); lake env lean /tmp/idod2/check/Leaves2.lean (#print axioms check_C3, check_C4, check_C5)`
- `lake env lean /tmp/idod2/check/FromJson.lean (statements and proofs regenerated from the final JSON strings)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-80d24321a5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-80d24321a5/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-80d24321a5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/idod2/check/DepStubs.txt`
- `/tmp/idod2/check/ChildStubs.txt`
- `/tmp/idod2/check/Assembly.lean`
- `/tmp/idod2/check/Leaves1.lean`
- `/tmp/idod2/check/Leaves2.lean`
- `/tmp/idod2/check/FromJson.lean`

Pins match: the snapshot manifest records project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d, equal to the workspace HEAD and .lake/packages/mathlib HEAD; SimonGMT is pinned at 2b3663083f3fe399b6296fb8eaee52169170e197. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and accepted children are declared as `theorem Submission.X` inside `namespace GMT.Ch07` (checked on the accepted commit fb9bfaa2).

Library support found in the snapshot: measure_null_of_locally_null (MeasureTheory/OuterMeasure/Basic.lean:150), measure_iUnion_null, IsCompact.eventually_forall_of_forall_eventually (Topology/Compactness/Compact.lean:459), upperSemicontinuousOn_iff_preimage_Iio (Topology/Semicontinuity/Basic.lean:914), measure_ball_pos (Measure/OpenPos.lean:212), measure_ball_lt_top (Measure/Typeclasses/Finite.lean:373), withDensity_zero_left (Measure/WithDensity.lean:83), ENNReal.ofReal_div_of_pos (Basic/ENNReal/Inv.lean:960), ENNReal.mul_lt_mul_iff_right (Basic/ENNReal/Operations.lean:83), ENNReal.Tendsto.mul / Tendsto.mul_const (Topology/Instances/ENNReal/Lemmas.lean:337, 359), le_of_tendsto (Topology/Order/OrderClosed.lean:133), and SimonGMT GeometricCurrentOn.massOn_mono (Chapter06/Mass.lean:81). In this Mathlib pin the monoid lemmas are named mul_le_mul_right/mul_le_mul_left (Algebra/Order/Monoid/Unbundled/Basic.lean:58, 66) and ENNReal lives under Mathlib/Basic/ENNReal.

DAG: the cited results have these frozen types and states: dimred_im_mass_measure, dtc_blowUp_massOn_image, idtp_convergesWeakly_massOn_le and dimred_cs_mi_hasMassDensity_unique are accepted; dimred_minimizing_monotonicity, dimred_threshold_reduction, dimred_invariant_cone_splitting, dimred_one_dim_minimizing_cone, idtp_imrep_measure_density_ae and idtp_two_dim_cone_integer_density are frozen siblings of this node or of its parent. No match for idod_ in dag.json, DAG.md, dag.mmd, issue-workers.json, problem.json, the pinned project, SimonGMT or git history. The only hits are this node's own unmaterialized attempt-1 files (decomposition-v1.json, audit, receipt); the DAG lists no children for this node. The five names are therefore unreserved and are reused with identical types.

Lean checks: stubs were generated verbatim from the dag.json types. Assembly.lean proves the frozen parent type from the children with axioms [propext, Classical.choice, Quot.sound, dimred_minimizing_monotonicity, idod_local_threshold_null]. Leaves1/Leaves2 prove each child's exact type from the stubs:
- C1: standard axioms only;
- C2: dtc_blowUp_massOn_image and idtp_convergesWeakly_massOn_le;
- C3: dimred_im_mass_measure and idtp_imrep_measure_density_ae;
- C4: dimred_invariant_cone_splitting, dimred_one_dim_minimizing_cone and idtp_two_dim_cone_integer_density;
- C5: dimred_minimizing_monotonicity, dimred_threshold_reduction and C1–C4.
No sorryAx appears. An independent reviewer agent re-ran a copy (/tmp/idod2_review/FromJson.lean) with identical axiom sets and accepted the split. Inline indicators, ENNReal products, casts and scalar multiplications have their intended instances, and no matrix construction occurs.
