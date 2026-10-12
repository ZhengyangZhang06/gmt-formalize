# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1.height_bound_small_delta-a1`
- Child DAG node: `root.affine_approximation-a1.height_bound_small_delta-a1.height_from_net_plane-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 5, printed proof of Lemma 2.5 (pp. 109-110), (5)-(6) and the conclusion: "|p_{(T_{x_0} M)^perp}(y_j - x_0)| <= C delta^{1/2 - alpha n}; since |x_0| < delta^alpha, |p_{(T_{x_0} M)^perp}(y_j)| <= C(delta^{1/2 - alpha n} + delta^alpha) ... all the points y_1, ..., y_N are in the C delta^{1/(2n+2)} neighborhood of the subspace T_0 = T_{x_0} M, and hence by (2) we have dist(y, T_0) <= C delta^{1/(2n+2)} for all y in spt mu cap B_1(0)".
This is Steps 6-7 of the parent proof: the net points y_j (parent: F, an A sigma-net of spt V cap B_sigma(xi)), the selected point x_0, the plane T, a = A sigma = delta^alpha sigma and b = C_6 delta^alpha sigma, with the two triangle inequalities combined into one. No erratum affects this step.

Hypotheses and notation.
- n, l are natural numbers; T is a linear subspace of R^(n+l); p_T := T.starProjection is the orthogonal projection onto T, so p_T(v) is in T for every v.
- xi, x_0 in R^(n+l); S is a subset of R^(n+l); F is a finite subset of R^(n+l); a, b are real numbers.
- (i) |x_0 - xi| <= a.
- (ii) |(x_0 - y) - p_T(x_0 - y)| <= b for every y in F.
- (iii) For every x in S there is y in F with dist(x, y) = |x - y| <= a.
- For v in R^(n+l), dist(v, T) := inf{|v - t| : t in T} (Metric.infDist).

1. Fix x in S. By (iii) choose y in F with |x - y| <= a.

2. Put u := x_0 - y and t := -p_T(u). Since p_T(u) is in T and T is a linear subspace (closed under negation), t is in T.

3. Algebraic identity: (x - xi) - t = (x - xi) + p_T(u) = (x - y) + (x_0 - xi) - (u - p_T(u)). This holds because (x - y) + (x_0 - xi) - (x_0 - y) = x - xi.

4. Since t is in T, dist(x - xi, T) <= |(x - xi) - t|, because an infimum is at most each of its values.

5. By Step 3 and the triangle inequality,
 |(x - xi) - t| <= |x - y| + |x_0 - xi| + |u - p_T(u)| <= a + a + b,
 using Step 1, (i), and (ii) for this y in F.

6. Hence dist(x - xi, T) <= b + 2a. As x in S was arbitrary, the inequality holds for every x in S. QED

Remark: u - p_T(u) = p_{T^perp}(x_0 - y), so Step 5 is the book's estimate |p_{T^perp}(x - xi)| <= |p_{T^perp}(x_0 - y)| + |x_0 - xi| + |x - y|.

(Mathlib: Submodule.starProjection_apply_mem, Submodule.neg_mem, Metric.infDist_le_dist_of_mem, dist_eq_norm, norm_sub_le, norm_add_le.)

## Key steps

1. For x in S pick y in F with |x - y| <= a.
2. t := -p_T(x_0 - y) lies in T.
3. (x - xi) - t = (x - y) + (x_0 - xi) - ((x_0 - y) - p_T(x_0 - y)).
4. dist(x - xi, T) <= |(x - xi) - t| <= a + a + b = b + 2a by the triangle inequality and the hypotheses.

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
