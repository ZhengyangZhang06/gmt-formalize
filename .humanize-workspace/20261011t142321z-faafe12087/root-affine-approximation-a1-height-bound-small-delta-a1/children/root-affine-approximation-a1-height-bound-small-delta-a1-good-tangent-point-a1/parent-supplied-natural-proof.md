# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1.height_bound_small_delta-a1`
- Child DAG node: `root.affine_approximation-a1.height_bound_small_delta-a1.good_tangent_point-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 5, printed proof of Lemma 2.5 (p. 109), (4)-(5): "Thus for any given k >= 1 we have sum_{j=1}^N |p_{(T_x M)^perp}(x - y_j)|^2 <= C k delta^{1 - alpha n} except possibly for a set of x in B_1(0) cap spt mu of mu-measure <= 1/k. Since mu(B_{delta^alpha}(0)) >= C^{-1} delta^{alpha n} by 2.4, we can select k = C delta^{-alpha n}, thus ensuring that (4) holds for some x_0 in spt mu cap B_{delta^alpha}(0)".
This follows the explicit form of Step 5 of the parent proof: f := sum_j |p_x^perp(x - y_j)|^2, Chebyshev's inequality, positivity of the measure of the good set, and the choice of a point where p_x is the projection onto an n-dimensional T (aal_tangent_structure (a),(b)).
Here mu, P, the radii (parent: R = sigma, s = A sigma), the per-point bound K (parent: (2 sigma)^(n+2) C_P omega_n delta) and lambda (parent: (4 C_5/omega_n) delta^(1 - 2 alpha n) sigma^2) are arbitrary, and the parent's numerical estimate is packaged into hypothesis (H2). No erratum affects this step.

Hypotheses and notation.
- n, l are natural numbers; mu is a measure on R^(n+l); P : R^(n+l) -> L(R^(n+l), R^(n+l)) is mu-a.e. strongly measurable.
- (A) For mu-a.e. x there is a linear subspace T of dimension n with P(x) = p_T, where p_T := T.starProjection is the orthogonal projection onto T.
- xi in R^(n+l); s, R, K, lambda are real with lambda > 0 and s <= R; F is a finite subset of R^(n+l).
- (H1) For every y in F: int_{B_R(xi)} ofReal(|(x - y) - P(x)(x - y)|^2) dmu(x) <= ofReal(K).
- (H2) ofReal((#F) K) < ofReal(lambda) mu(B_s(xi)).
- Balls are closed; integrals are Lebesgue integrals in [0, infinity]; ofReal(t) = max(t, 0).

1. Notation. For y in F put h_y(x) := ofReal(|(x - y) - P(x)(x - y)|^2) and f(x) := sum_{y in F} h_y(x) in [0, infinity]. Let B := B_R(xi) and B' := B_s(xi). Both are closed, hence measurable, and B' is contained in B because s <= R.

2. Measurability of h_y.
 (a) The evaluation map (L, v) -> L(v), from L(R^(n+l), R^(n+l)) x R^(n+l) to R^(n+l), is continuous bilinear.
 (b) P is mu-a.e. strongly measurable and x -> x - y is continuous, so x -> P(x)(x - y) is mu-a.e. strongly measurable (Mathlib ContinuousLinearMap.aestronglyMeasurable_comp₂ applied to the identity map of L(R^(n+l), R^(n+l))).
 (c) Then x -> (x - y) - P(x)(x - y), its norm, the square and ofReal are mu-a.e. measurable. So h_y is mu-a.e. measurable, and also a.e. measurable for mu restricted to B.

3. Integral of f over B. By additivity of the Lebesgue integral for finitely many a.e.-measurable [0, infinity]-valued functions (Mathlib lintegral_finsetSum') and (H1):
 int_B f dmu = sum_{y in F} int_B h_y dmu <= sum_{y in F} ofReal(K) = (#F) ofReal(K) = ofReal((#F) K).
 The last equality holds because #F >= 0 gives ofReal((#F) K) = ofReal(#F) ofReal(K), and ofReal(#F) = #F.

4. Assumption for contradiction. Suppose the conclusion fails: for every x in B' and every n-dimensional subspace T with P(x) = p_T, there is y in F with |(x - y) - p_T(x - y)|^2 >= lambda.

5. Then f >= ofReal(lambda) a.e. on B', i.e. for a.e. x with respect to mu restricted to B'.
 (a) By (A) there is a mu-null set Z such that for every x outside Z some n-dimensional T_x satisfies P(x) = p_{T_x}. Z is also null for mu restricted to B', and almost every point for mu restricted to B' lies in B'.
 (b) For x in B' minus Z, Step 4 applied to (x, T_x) gives y in F with |(x - y) - P(x)(x - y)|^2 = |(x - y) - p_{T_x}(x - y)|^2 >= lambda.
 (c) So ofReal(lambda) <= h_y(x) <= f(x), because all summands of f are >= 0.

6. Chebyshev's inequality in the form needed:
 ofReal(lambda) mu(B') = int_{B'} ofReal(lambda) dmu <= int_{B'} f dmu <= int_B f dmu <= ofReal((#F) K).
 The four relations use, in order: the integral of a constant over B', a.e. monotonicity of the integral (Step 5), monotonicity in the domain (B' contained in B), and Step 3. This contradicts (H2).
 Equivalently: {x in B' : f(x) >= lambda} has mu-measure at most lambda^{-1} int_B f dmu < mu(B'). So Y = {x in B' : f(x) < lambda} has positive measure and, by (A), contains a point x_0 at which P(x_0) is the projection onto an n-dimensional subspace.

7. Conclusion. There exist x_0 in B_s(xi) and an n-dimensional subspace T with P(x_0) = p_T and |(x_0 - y) - p_T(x_0 - y)|^2 < lambda for every y in F. QED

(Mathlib: ContinuousLinearMap.aestronglyMeasurable_comp₂, AEStronglyMeasurable.norm, AEMeasurable.pow_const, ENNReal.measurable_ofReal, lintegral_finsetSum', ENNReal.ofReal_mul, ENNReal.ofReal_natCast, ae_restrict_of_ae, ae_restrict_mem, Finset.single_le_sum, setLIntegral_const, lintegral_mono_ae, lintegral_mono_set, Metric.closedBall_subset_closedBall.)

## Key steps

1. f := sum_{y in F} ofReal|(x - y) - P(x)(x - y)|^2 is mu-a.e. measurable because P is a.e. strongly measurable and evaluation is continuous bilinear.
2. int_{B_R(xi)} f = sum_y int_{B_R(xi)} h_y <= (#F) K by finite additivity and (H1).
3. If no good point existed, then by the a.e. n-plane hypothesis f >= lambda a.e. on B_s(xi).
4. Then lambda mu(B_s(xi)) <= int_{B_s(xi)} f <= int_{B_R(xi)} f <= (#F) K contradicts (H2); hence x_0 in B_s(xi) and T with P(x_0) = p_T and all |p_T^perp(x_0 - y)|^2 < lambda exist.

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
