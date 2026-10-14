# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1.piece_image_tangent-a1.rescaled_integral_limit-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1.piece_image_tangent-a1.rescaled_integral_limit-a1.compl_average-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the first bullet of step 6 of the parent proof, which verifies the hypothesis of pit_integral_closedBall_rescale_tendsto for h = 1_{ℝ^n∖B}. Here it is stated on its own.
Notation:
- λ := Lebesgue measure on ℝ^n, and λ_ℝ(E) := λ(E) as a real number (toReal);
- for s > 0, C_s := B̄_s(b) and q(s) := λ(B ∩ C_s)/λ(C_s) ∈ [0, ∞].
1. Fix s > 0.
- C_s contains the nonempty open ball B_s(b), and Lebesgue measure is positive on nonempty open sets, so λ(C_s) > 0 (measure_closedBall_pos).
- C_s is compact, so λ(C_s) < ∞ (measure_closedBall_lt_top).
- Hence λ_ℝ(C_s) > 0.
2. ℝ^n∖B is Borel, so ∫_{C_s} 1_{ℝ^n∖B} dλ = ∫_{C_s ∩ (ℝ^n∖B)} 1 dλ = λ_ℝ(C_s ∖ B) (setIntegral_indicator, setIntegral_const).
3. B is Borel and λ(C_s) < ∞, so λ_ℝ(C_s ∩ B) + λ_ℝ(C_s ∖ B) = λ_ℝ(C_s) (measureReal_inter_add_sdiff). Hence ∫_{C_s} 1_{ℝ^n∖B} dλ = λ_ℝ(C_s) − λ_ℝ(B ∩ C_s).
4. By the definition of the set average (setAverage_eq) and λ_ℝ(C_s) ≠ 0 from step 1:
⨍_{C_s} 1_{ℝ^n∖B} dλ = λ_ℝ(C_s)^{-1}·(λ_ℝ(C_s) − λ_ℝ(B ∩ C_s)) = 1 − λ_ℝ(B ∩ C_s)/λ_ℝ(C_s).
5. In [0, ∞], (x/y).toReal = x.toReal/y.toReal (ENNReal.toReal_div), so q(s).toReal = λ_ℝ(B ∩ C_s)/λ_ℝ(C_s). Therefore, for every s > 0, ⨍_{B̄_s(b)} 1_{ℝ^n∖B} dλ = 1 − q(s).toReal.
6. By hypothesis q(s) → 1 as s → 0⁺. Since 1 ≠ ∞, toReal is continuous at 1 (ENNReal.tendsto_toReal). So q(s).toReal → 1, and 1 − q(s).toReal → 1 − 1 = 0.
7. The identity of step 5 holds for all s ∈ (0, ∞), and this set belongs to the filter 𝓝[>] 0 (self_mem_nhdsWithin). Functions that agree eventually have the same limit (Tendsto.congr'). So ⨍_{B̄_s(b)} 1_{ℝ^n∖B} dλ → 0 as s → 0⁺.
No case split on n is needed. For n = 0, ℝ^0 is a single point of measure 1, and the same computation applies.

## Key steps

1. For s > 0, 0 < λ(B̄_s(b)) < ∞.
2. ∫_{B̄_s(b)} 1_{Bᶜ} = λ_ℝ(B̄_s(b)) − λ_ℝ(B ∩ B̄_s(b)) by additivity, since B is Borel.
3. So for s > 0 the average equals 1 − (λ(B ∩ B̄_s(b))/λ(B̄_s(b))).toReal.
4. toReal is continuous at 1, so the averages tend to 1 − 1 = 0; transfer along the eventual identity on (0, ∞).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp project/GMT/Ch07/Contract.lean and project/GMT/Ch07/Submission.lean against the workspace copies (identical)`
- `rg -n 'pit_ril|pit_rescaled_integral_tendsto|pit_integral_closedBall_rescale_tendsto' project --glob '*.lean' (no match)`
- `rg -n -e 'theorem tendsto_nhdsWithin_nhds ' -e 'theorem uniformContinuous_iff ' -e 'theorem hasFDerivAt_iff_isLittleO_nhds_zero' -e 'theorem norm_setIntegral_le_of_norm_le_const ' -e 'theorem measure_closedBall_lt_top' -e 'theorem measure_closedBall_pos' -e 'theorem setIntegral_indicator ' -e 'theorem measureReal_inter_add_sdiff' -e 'theorem setAverage_eq ' -e 'theorem toReal_div ' -e 'theorem tendsto_toReal ' -e 'theorem setIntegral_eq_integral_of_forall_compl_eq_zero' -e 'theorem norm_integral_le_of_norm_le ' -e 'theorem integral_const_mul ' -e 'theorem eventually_nhds_iff ' mathlib/Mathlib --glob '*.lean'`
- `rg -n -e 'uniformContinuous_of_continuous' -e 'exists_pos_le_norm' -e 'bounded_above_of_compact_support' -e 'lemma squeeze_zero' -e 'tendsto_iff_norm_div_tendsto_zero' -e 'integrableOn_of_bounded' mathlib/Mathlib --glob '*.lean'`
- `python3 -I: verifier/gmt-compare.py contract_scope(GMT/Ch07/Contract.lean, 'GMT.Ch07.main_theorem'); verifier/lean_contract.py validate_lean_statement on the three child types`
- `python3 -I: lean_name scan of all eight chapter dag.json files (2,795 nodes) for pit_ril_* (no match); grep -rl pit_ril over the ch07 run node files, the SimonGMT package and GMT/ (no match)`
- `git cat-file --batch over the 778 distinct GMT/Ch07/Submission.lean blobs of 1,477 ref commits: pit_ril 0, Submission.pit_ 0, Submission.pit_rescaled_integral_tendsto 0; control Submission.ptd_piece_image_measurable_ae_pullback 2`
- `lake env lean /tmp/ril-decomp-q3/Parent.lean (parent and sibling frozen types elaborate; #check of the cited API)`
- `lake env lean /tmp/ril-decomp-q3/Assembly.lean (#print axioms ril_assembly_conditional)`
- `lake env lean /tmp/ril-decomp-q3/A/ChildA.lean, /tmp/ril-decomp-q3/B/ChildB.lean, /tmp/ril-decomp-q3/C/ChildC.lean (#print axioms of each child)`
- `lake env lean /tmp/ril-decomp-q3/final/EndToEnd.lean and /tmp/ril-decomp-q3/final/CompStyle.lean; reviewer check /tmp/ril-decomp-q3/review/PureAssembly.lean`
- `sed -n 105,175p book/chapter-03.txt (Simon Ch. 3 Theorem 1.6, proof of '⇒')`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-666e5eebda/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-666e5eebda/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-666e5eebda/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/ril-decomp-q3/Parent.lean`
- `/tmp/ril-decomp-q3/Assembly.lean`
- `/tmp/ril-decomp-q3/A/ChildA.lean`
- `/tmp/ril-decomp-q3/B/ChildB.lean`
- `/tmp/ril-decomp-q3/C/ChildC.lean`
- `/tmp/ril-decomp-q3/final/EndToEnd.lean`
- `/tmp/ril-decomp-q3/final/CompStyle.lean`
- `/tmp/ril-decomp-q3/review/PureAssembly.lean`

The snapshot contains no proof of the selected statement, of the sibling pit_integral_closedBall_rescale_tendsto, or of any proposed child. The project supplies only the frozen contract and Euclid (rg: no match).

Every lemma cited in the child proofs exists in the pinned Mathlib 25730c7c with the signature used:
- Metric.uniformContinuous_iff, Metric.eventually_nhds_iff and Metric.tendsto_nhdsWithin_nhds (Topology/MetricSpace/Pseudo/Defs.lean:755/779/861);
- hasFDerivAt_iff_isLittleO_nhds_zero (Analysis/Calculus/FDeriv/Basic.lean:815);
- setIntegral_indicator, setIntegral_eq_integral_of_forall_compl_eq_zero and norm_setIntegral_le_of_norm_le_const, which needs only μ s < ∞ and no measurability (Integral/Bochner/Set.lean:194/486/613);
- integral_const_mul and norm_integral_le_of_norm_le (Integral/Bochner/Basic.lean:290/985);
- Measure.integrableOn_of_bounded (Integral/IntegrableOn.lean:716) and setAverage_eq (Integral/Average.lean:402);
- measureReal_inter_add_sdiff (Measure/Real.lean:237), measure_closedBall_pos (Measure/OpenPos.lean:216) and measure_closedBall_lt_top (Measure/Typeclasses/Finite.lean:364);
- ENNReal.toReal_div (Basic/ENNReal/Inv.lean:977) and ENNReal.tendsto_toReal (Topology/Instances/ENNReal/Lemmas.lean:102);
- the to_additive forms HasCompactSupport.uniformContinuous_of_continuous (UniformSpace/HeineCantor.lean:91), HasCompactSupport.exists_pos_le_norm and Continuous.bounded_above_of_compact_support (Analysis/Normed/Group/Bounded.lean:163/153), and tendsto_iff_norm_sub_tendsto_zero (Analysis/Normed/Group/Continuity.lean:305);
- squeeze_zero' (Topology/MetricSpace/Pseudo/Lemmas.lean:32).

The Lean checks pass:
- The three child types pass validate_lean_statement and elaborate in the comparator's replayed scope (open Filter Function Set MeasureTheory Metric; namespace GMT.Ch07; ...).
- Each child is proved in scratch Lean using only propext, Classical.choice and Quot.sound.
- The parent's exact DAG type is proved from the three child declarations with the sibling's frozen type as a hypothesis, using the same axioms.
- Comparator-style `exact Submission.X` checks pass.

The names are fresh: none appears in any chapter DAG, the ch07 node files, or any ref's Submission.lean.
