# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.radon_convergence_criterion-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.radon_convergence_criterion-a1.superlevel_convergence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof of `cmc_tendsto_integral_of_limsup_liminf` (the "standard approximation argument" that ends Simon's proof of 7.2.4, chapter-07.txt lines 284–289, which starts from (13) limsup_j μ_{T_j}(K) ≤ μ_T(K) for compact K ⊆ U and (14) μ_T(W) ≤ liminf_j μ_{T_j}(W) for open W ⊆ U). Here it is stated for one continuous compactly supported g. No sign condition on g is needed.
1. Notation. Let C := tsupport g = closure{x : g(x) ≠ 0}. Since g has compact support, C is compact, and C ⊆ U by hypothesis. So μ(C) < ∞ by (a).
2. The exceptional set is countable. Let μ_C := μ⌞C, i.e. μ_C(A) = μ(A ∩ C). Then μ_C(ℝ^P) = μ(C) < ∞, so μ_C is a finite measure. For s ∈ ℝ let L_s := {x : g(x) = s}. These are Borel sets, because g is continuous and hence Borel measurable, and they are pairwise disjoint for distinct s. Let D := {s ∈ ℝ : μ_C(L_s) > 0}. For n ≥ 1, let D_n := {s : μ_C(L_s) > 1/n}. If s_1, …, s_m are distinct elements of D_n, then m/n < Σ_i μ_C(L_{s_i}) = μ_C(⋃_i L_{s_i}) ≤ μ_C(ℝ^P) = μ(C) < ∞. So D_n has at most n·μ(C) elements, and D = ⋃_{n≥1} D_n is countable. (In Mathlib this is `MeasureTheory.Measure.countable_meas_level_set_pos` applied to `hg.measurable` and the finite, hence s-finite, measure `μ.restrict (tsupport g)`. Register `IsFiniteMeasure (μ.restrict (tsupport g))` from `Measure.restrict_apply_univ` and μ(C) < ∞.)
3. Choice of t. A countable subset of ℝ is Lebesgue-null (`Set.Countable.measure_zero`). So Lebesgue-a.e. t ∈ ℝ satisfies t ∉ D (`measure_eq_zero_iff_ae_notMem`), and the same then holds a.e. for Lebesgue measure restricted to (0, ∞) (`ae_restrict_of_ae`). Also, a.e. point for that restricted measure lies in (0, ∞) (`ae_restrict_mem measurableSet_Ioi`). Fix t with t > 0 and t ∉ D. It suffices to show μ_j(G) → μ(G) in [0, ∞], where G := {x : g(x) > t}. This gives the claim for every t outside a null set.
4. Topology of the superlevel sets. Let K := {x : g(x) ≥ t}. If x ∈ K, then g(x) ≥ t > 0, so g(x) ≠ 0 and x ∈ support g ⊆ C. Hence G ⊆ K ⊆ C ⊆ U. Because g is continuous, G = g⁻¹((t, ∞)) is open and K = g⁻¹([t, ∞)) is closed (`isOpen_lt continuous_const hg`, `isClosed_le continuous_const hg`). As a closed subset of the compact set C, K is compact (`IsCompact.of_isClosed_subset`).
5. μ(K) = μ(G). We have K ∖ G = {x : g(x) = t} = L_t, and L_t ⊆ K ⊆ C. So μ(K ∖ G) = μ(L_t) = μ(L_t ∩ C) = μ_C(L_t) (`Measure.restrict_eq_self`), and μ_C(L_t) = 0 because t ∉ D. Since K = G ∪ (K ∖ G) (`union_sdiff_cancel`), subadditivity (`measure_union_le`) gives μ(K) ≤ μ(G) + μ(K ∖ G) = μ(G). Monotonicity gives μ(G) ≤ μ(K). Hence μ(K) = μ(G). (Alternatively, Mathlib's `MeasureTheory.meas_le_ae_eq_meas_lt` gives μ{g ≥ t} = μ{g > t} for a.e. t by a different route.)
6. Squeeze. By (c) for the open set G ⊆ U, μ(G) ≤ liminf_j μ_j(G). Since μ_j(G) ≤ μ_j(K) for every j, we get limsup_j μ_j(G) ≤ limsup_j μ_j(K) (`limsup_le_limsup`). By (b) for the compact set K ⊆ U, limsup_j μ_j(K) ≤ μ(K) = μ(G). Hence limsup_j μ_j(G) ≤ μ(G) ≤ liminf_j μ_j(G). In [0, ∞], a complete linear order with the order topology in which every sequence is bounded, this forces μ_j(G) → μ(G) (`tendsto_of_le_liminf_of_limsup_le hinf hsup`; with `exact`/`refine` the boundedness auto-parameters close by themselves).
7. By steps 3–6, μ_j({g > t}) → μ({g > t}) for a.e. t with respect to Lebesgue measure restricted to (0, ∞). ∎
Implementation note: once μ(K ∖ G) = 0 is known, Mathlib's Portmanteau lemma `MeasureTheory.tendsto_measure_of_le_liminf_measure_of_limsup_measure_le` would also give step 6 (and the conclusion μ(K) = μ(G) of step 5), but `Mathlib.MeasureTheory.Measure.Portmanteau` is not in the import closure of `GMT.Ch07.Submission`. The direct squeeze above uses only imported lemmas.

## Key steps

1. C := tsupport g is compact and ⊆ U, so μ(C) < ∞ by (a); μ⌞C is a finite measure.
2. The level sets {g = s} are disjoint Borel sets, so only countably many have positive μ⌞C-measure. Hence for Lebesgue-a.e. t > 0, μ({g = t}) = 0.
3. For such t > 0: G = {g > t} is open, K = {g ≥ t} is compact, G ⊆ K ⊆ C ⊆ U, and μ(K) = μ(G) because K ∖ G = {g = t}.
4. limsup_j μ_j(G) ≤ limsup_j μ_j(K) ≤ μ(K) = μ(G) ≤ liminf_j μ_j(G) by (b) and (c), so μ_j(G) → μ(G) in [0, ∞].

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cmp GMT/Ch07/Contract.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `rg -n 'theorem Integrable.integral_eq_integral_meas_lt|countable_meas_level_set_pos|theorem tendsto_integral_filter_of_dominated_convergence|theorem tendsto_of_le_liminf_of_limsup_le|theorem tendsto_toReal' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n '^theorem|^lemma' mathlib/Mathlib/MeasureTheory/Measure/Portmanteau.lean; sed -n 205,245p and 490,545p Portmanteau.lean (tendsto_measure_of_le_liminf_measure_of_limsup_measure_le, lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure)`
- `sed -n 40,100p and 495,560p mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean (countable_meas_le_ne_meas_lt, meas_le_ae_eq_meas_lt, Integrable.integral_eq_integral_meas_lt)`
- `rg -n 'max_zero_sub_eq_self|HasCompactSupport.mono|eventually_lt_of_limsup_lt|Continuous.integrable_of_hasCompactSupport|integrableOn_iff_integrable_of_support_subset|bounded_above_of_compact_support|Countable.measure_zero|restrict_eq_self|measure_eq_zero_iff_ae_notMem|ae_restrict_mem|integrableOn_const|integrable_indicator_iff|measureReal_nonneg' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'cmc_rcc|superlevel|layer_cake|tendsto_integral_of' local-references/123e8435b4a2469b/project -g '*.lean' (no match)`
- `python3 scan of dag.json: lean_name/lean_statement/theorems of all 515 nodes for limsup|liminf|layer|superlevel|meas_lt|integrable_of|tendsto_integral|portmanteau|dominated|level_set|cmc_ and for the proposed names (no collision, no reusable accepted node)`
- `rg -n -i 'portmanteau|layer.?cake|integral_eq_integral_meas_lt|tendsto_integral_of' lake-packages-25730c7c/simongmt -g '*.lean' (only Chapter04 layer-cake identities, not imported by Submission)`
- `sed -n 255,295p book/chapter-07.txt`
- `lake env lean /tmp/rcc-decomp/lean/Types.lean; lake env lean /tmp/rcc-decomp/lean/Assembly.lean; lake env lean /tmp/rcc-decomp/lean/Children2.lean; lake env lean /tmp/rcc-decomp/lean/Full.lean (all compile; #print axioms = propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Portmanteau.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Group/MinMax.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-radon-convergence-criterion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-radon-convergence-criterion-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/LayerCake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/tmp/rcc-decomp/lean/Types.lean`
- `/tmp/rcc-decomp/lean/Assembly.lean`
- `/tmp/rcc-decomp/lean/Children2.lean`
- `/tmp/rcc-decomp/lean/Full.lean`

Contract and versions: the snapshot contract (project b4d606db, Mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean.

No existing result to reuse: neither the snapshot project nor SimonGMT (Chapter04 layer-cake identities are not imported) has a convergence criterion for limsup on compacts and liminf on opens, and no accepted DAG node has either child type. The proposed names do not occur anywhere in the DAG or snapshot.

Mathlib supplies every ingredient in the import closure of GMT.Ch07.Submission: Integrable.integral_eq_integral_meas_lt, Measure.countable_meas_level_set_pos (also meas_le_ae_eq_meas_lt), tendsto_integral_filter_of_dominated_convergence, tendsto_of_le_liminf_of_limsup_le, ENNReal.tendsto_toReal, Continuous.integrable_of_hasCompactSupport, integrableOn_iff_integrable_of_support_subset, eventually_lt_of_limsup_lt and Continuous.bounded_above_of_compact_support. Portmanteau.lean is not imported, so its tendsto_measure_of_le_liminf_measure_of_limsup_measure_le is unavailable; the direct squeeze is used instead.

Lean checks: both child types elaborate. The two children imply the exact frozen parent type, and both children have scratch proofs. All of this compiles with only propext, Classical.choice and Quot.sound.
