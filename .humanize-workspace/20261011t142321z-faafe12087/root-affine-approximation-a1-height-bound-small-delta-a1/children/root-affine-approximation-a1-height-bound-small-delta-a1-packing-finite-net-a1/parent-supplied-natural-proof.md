# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1.height_bound_small_delta-a1`
- Child DAG node: `root.affine_approximation-a1.height_bound_small_delta-a1.packing_finite_net-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 5, printed proof of Lemma 2.5 (p. 109):
- "Recall the general principle that if K is compact and tau > 0 then any maximal pairwise disjoint collection B_{tau/2}(y_j) with y_j in K will automatically have the property that K is contained in the union of the B_tau(y_j)";
- together with the counting estimate (3): "C^{-1} N delta^{alpha n} <= sum_j mu(B_{delta^alpha/2}(y_j)) = mu(union_j B_{delta^alpha/2}(y_j)) <= mu(B_2(0)) <= 2C".
This is Step 4 of the parent proof (an admissible set of maximal cardinality), stated abstractly:
- centre set S (parent: spt V cap B_sigma(xi));
- radius r = tau/2 (parent: A sigma/2);
- container E (parent: B_{2 sigma}(xi));
- lower mass bound a (parent: (1/2) omega_n (A sigma/2)^n);
- upper bound b (parent: 2 omega_n (2 sigma)^n).
Compactness of K is not needed, because finiteness comes from the mass bounds. No erratum affects this step.

Hypotheses and notation.
- X is a metric space whose sigma-algebra contains the open sets, and mu is a measure on X with values in [0, infinity].
- B_t(y) := {x in X : dist(x, y) <= t} is the closed ball.
- S, E are subsets of X; r > 0, a > 0, b >= 0; mu(E) <= b in [0, infinity].
- For every y in S: B_r(y) is contained in E and mu(B_r(y)) >= a.

1. Measurability of balls. Each closed ball B_r(z) is a closed set. Its complement is open, hence measurable, so B_r(z) is measurable.

2. Admissible sets. Call a finite set G of points of X admissible if G is contained in S and the closed balls B_r(z), z in G, are pairwise disjoint, i.e. B_r(z) cap B_r(z') is empty whenever z, z' in G and z != z'. The empty set is admissible (vacuously).

3. Packing bound: every admissible G satisfies (#G) a <= b.
 (a) The sets B_r(z), z in G, are measurable (Step 1) and pairwise disjoint, so by finite additivity mu(union_{z in G} B_r(z)) = sum_{z in G} mu(B_r(z)).
 (b) Each z in G lies in S, so mu(B_r(z)) >= a, and the sum is >= sum_{z in G} a = (#G) a.
 (c) Each B_r(z) is contained in E (z in S), so the union is contained in E, and by monotonicity mu(union_{z in G} B_r(z)) <= mu(E) <= b.
 (d) Hence (#G) a <= b in [0, infinity]. Both (#G) a and b are nonnegative real numbers, so the inequality also holds in R.
 (e) As a > 0, #G <= b/a, and therefore #G <= floor(b/a).

4. A maximal admissible set. Let Cset := {#G : G admissible}, a set of natural numbers. By Steps 2 and 3, 0 is in Cset and every element of Cset is <= floor(b/a). A nonempty set of natural numbers that is bounded above contains its supremum N := sup Cset. Fix an admissible F with #F = N; then #G <= N for every admissible G.

5. First two conclusions. F is contained in S because F is admissible, and (#F) a <= b by Step 3.

6. Net property. Let y in S and suppose, for contradiction, that dist(y, z) > 2r for every z in F.
 (a) y is not in F: otherwise taking z = y would give 0 = dist(y, y) > 2r > 0.
 (b) For every z in F, B_r(y) cap B_r(z) is empty: if w belonged to both balls, then dist(y, z) <= dist(y, w) + dist(w, z) <= r + r = 2r, contradicting dist(y, z) > 2r.
 (c) G' := F union {y} is admissible: G' is contained in S because F is contained in S and y in S. Balls centred at two distinct points of F are disjoint because F is admissible, and the ball centred at y is disjoint from the ball centred at any z in F by (b).
 (d) By (a), #G' = #F + 1 = N + 1 > N, contradicting the maximality in Step 4.
 Hence some z in F satisfies dist(y, z) <= 2r.

7. Conclusion. By Steps 5 and 6, F is a finite subset of S with (#F) a <= b, and every y in S has dist(y, z) <= 2r for some z in F. QED

(Mathlib names for the steps: measurableSet_closedBall, measure_biUnion_finset, measure_mono, ENNReal.ofReal_mul, ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff, Nat.le_floor, le_div_iff₀, Nat.sSup_mem, le_csSup, Set.PairwiseDisjoint.insert, Metric.closedBall_disjoint_closedBall, Finset.card_insert_of_notMem.)

## Key steps

1. Admissible sets: finite G contained in S whose closed r-balls are pairwise disjoint; the empty set is admissible.
2. Packing count: (#G) a <= sum mu(B_r(z)) = mu(union B_r(z)) <= mu(E) <= b by finite additivity and B_r(z) contained in E; hence #G <= floor(b/a).
3. Choose an admissible F of maximal cardinality N (a nonempty, bounded-above set of naturals contains its supremum).
4. If y in S had dist(y,z) > 2r for all z in F, then y is not in F and B_r(y) is disjoint from every B_r(z), so F union {y} would be admissible of size N+1, a contradiction; hence every y in S is within 2r of F.

## Reference use

### local-project

Queries:
- `timeout 300 rg -n 'aal_packing_finite_net|aal_normal_sq_lintegral_le_conical|aal_good_tangent_point|aal_height_of_net_plane' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib  (no match, rc=1)`
- `python3 -I: list lean_name of every node in .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json (collision check)`
- `rg -n "theorem measure_biUnion_finset\b|theorem closedBall_disjoint_closedBall|theorem infDist_le_dist_of_mem|theorem lintegral_finset_sum'|theorem setLIntegral_const\b|theorem lintegral_mono_set\b|theorem lintegral_const_mul'\b|theorem setLIntegral_mono'|lemma starProjection_apply_mem|theorem sSup_mem|theorem mul_meas_ge_le_lintegral₀|theorem ae_restrict_mem\b|theorem dist_starProjection_eq_infDist|theorem infDist_le_infDist_add_dist" <snapshot>/mathlib/Mathlib`
- `rg -n "lintegral_finset_sum|theorem lintegral_const_mul'|clm_apply|apply_continuousLinearMap" <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/*.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/*.lean`
- `rg -n "clm_apply" <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -n "theorem lintegral_finsetSum'|aestronglyMeasurable_comp₂|theorem PairwiseDisjoint.insert\b|theorem le_csSup\b|theorem card_insert_of_notMem\b|theorem sSup_mem" <snapshot>/mathlib/Mathlib`
- `rg -n "exists_fiveTimesCovering|PairwiseDisjoint" .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityCovering.lean`
- `grep -n '2.5\|2.4\|2.3' book/sources/chapter-05-source.txt; sed -n 255,380p book/sources/chapter-05-source.txt (printed Lemma 2.5 and proof (1)-(6))`
- `python3 -I: lean_contract.validate_lean_statement on the 4 child lean_statements; gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch05.main_theorem') for the comparator replay`
- `lake env lean /tmp/claude-1000/hb-split/Check1.lean (child types elaborate), Check2.lean (sorry-free parent assembly from sorried children + uncles), Check3.lean (Lean proofs of the 4 children), Check4.lean (combined + #print axioms), Check5.lean (comparator-style challenge per child), Check6.lean (pp.explicit instance inspection)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/Lattice/Nat.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/Set/Pairwise/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/Finset/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-height-bound-small-delta-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityCovering.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-05-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/claude-1000/hb-split/Check4.lean`
- `/tmp/claude-1000/hb-split/Check5.lean`

Snapshot a7f8fcd21d5c8fc7: manifest.json pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.

No-match results:
- The four proposed names (aal_packing_finite_net, aal_normal_sq_lintegral_le_conical, aal_good_tangent_point, aal_height_of_net_plane) occur nowhere in <snapshot>/project or <snapshot>/mathlib (rg rc=1).
- dag.json reserves none of them. Existing aal_* names: density_ge_one, height_bound_small_delta, l1_tilt_height, lp_monotonicity, mass_upper_bound, pinched_density_bounds, tangent_structure, tilt_height_curvature_bound.
- No Mathlib or SimonGMT lemma packages the maximal-disjoint-ball net with a measure count. SimonGMT Chapter01/DensityCovering.lean:26 exists_fiveTimesCovering is the Vitali 5r lemma, which is not what is needed here.
- There is no AEStronglyMeasurable.clm_apply in the snapshot; only ContinuousOn.clm_apply appears, in CurveIntegral.

Located items (under <snapshot>/mathlib/Mathlib):
- ContinuousLinearMap.aestronglyMeasurable_comp₂: MeasureTheory/Function/StronglyMeasurable/Lemmas.lean:79
- lintegral_finsetSum': MeasureTheory/Integral/Lebesgue/Add.lean:343 (old name lintegral_finset_sum' is a deprecated alias at :354)
- lintegral_const_mul': Add.lean:420
- lintegral_mono_set: MeasureTheory/Integral/Lebesgue/Basic.lean:98
- setLIntegral_const: Basic.lean:121
- setLIntegral_mono': Basic.lean:254
- mul_meas_ge_le_lintegral₀: MeasureTheory/Integral/Lebesgue/Markov.lean:52
- ae_restrict_mem: MeasureTheory/Measure/Restrict.lean:640
- measure_biUnion_finset: MeasureTheory/Measure/Basic.lean:150
- Metric.closedBall_disjoint_closedBall: Topology/MetricSpace/Pseudo/Defs.lean:495
- Set.PairwiseDisjoint.insert: Data/Set/Pairwise/Basic.lean:297
- Nat.sSup_mem: Order/Lattice/Nat.lean:145
- le_csSup: Order/ConditionallyCompleteLattice/Basic.lean:197
- Finset.card_insert_of_notMem: Data/Finset/Card.lean:103
- Metric.infDist_le_dist_of_mem: Topology/MetricSpace/HausdorffDistance.lean:500
- Submodule.starProjection_apply_mem: Analysis/InnerProductSpace/Projection/Basic.lean:156
- Submodule.dist_starProjection_eq_infDist: Analysis/InnerProductSpace/Projection/Basic.lean:234

Book source: chapter-05-source.txt lines 294-370 (Lemma 2.5 and the printed proof (1)-(6)), used for the child Source lines.

Lean results (scratch, contract scope):
- The 4 child types elaborate, pass validate_lean_statement, and close comparator-style challenges.
- The 4 children are proved using only propext, Classical.choice and Quot.sound.
- The selected frozen type is proved from the children plus the frozen uncle types (aal_tangent_structure, aal_pinched_density_bounds); sorryAx comes only from those two sorried uncle stubs.
- The uncle and selected types match dag.json byte-for-byte.
