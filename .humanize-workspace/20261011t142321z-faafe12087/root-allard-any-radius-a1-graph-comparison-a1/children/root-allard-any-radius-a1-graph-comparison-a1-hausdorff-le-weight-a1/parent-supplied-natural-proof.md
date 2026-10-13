# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.graph_comparison-a1`
- Child DAG node: `root.allard_any_radius-a1.graph_comparison-a1.hausdorff_le_weight-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3 and 4 of the parent proof (Gamma \ M is H^n-null by the Upper Density Theorem; H^n <= mu on Gamma because theta >= 1). Uses the sibling upper_density (Submission.aetp_upper_density_zero_ae). Notation: H := muHE[n] on R^(n+l), M := V.carrier (H-null-measurable), theta := V.mult (> 0 on M, and a.e.-measurable for H restricted to M), mu := V.weight = (H restricted to M).withDensity(ofReal o theta). B_r(x) is the closed ball and B°_r(x) the open ball.
1. A measurable core of M. M is H-null-measurable, so there is a Borel M_1 contained in M with M_1 = M H-a.e. (NullMeasurableSet.exists_measurable_subset_ae_eq). Then (H restricted to M)(complement of M_1) = (H restricted to M_1)(complement of M_1) = 0, because restrictions to a.e.-equal sets agree (Measure.restrict_congr_set, Measure.restrict_apply). mu is absolutely continuous with respect to H restricted to M (withDensity_absolutelyContinuous), so mu(complement of M_1) = 0.
2. Upper density. A := O cap M_1 is Borel with mu(A) <= mu(O) < infinity. By upper_density applied to nu := mu and A: for H-a.e. x, if x is not in A, then mu(A cap B_r(x))/ofReal(r^n) -> 0 as r -> 0+.
3. H(Gamma \ M) = 0. Let x be in Gamma \ M; then x is not in A, since A is contained in M_1, which is contained in M. Let c, s_0 be as in the hypothesis for y = x, and e > 0 with B°_e(x) contained in O (O is open and contains x).
   For 0 < r < min(s_0, e/2), B_r(x) is contained in O. So B_r(x) \ A is contained in the complement of M_1, and mu(B_r(x) \ A) = 0 by step 1. Therefore
   ofReal(c r^n) <= mu(B_r(x)) <= mu(A cap B_r(x)) + mu(B_r(x) \ A) = mu(A cap B_r(x)),
   i.e. mu(A cap B_r(x))/ofReal(r^n) >= ofReal(c) > 0 (ENNReal.le_div_iff_mul_le, ofReal(c) ofReal(r^n) = ofReal(c r^n)).
   This holds for all r in the interval (0, min(s_0, e/2)), which belongs to the filter 𝓝[>] 0. If the quotient tended to 0, it would eventually be < ofReal(c) (Filter.Tendsto.eventually_lt_const). Since 𝓝[>] 0 is a proper filter, both eventual properties would hold at some r, a contradiction.
   Hence x lies in the exceptional H-null set of step 2. So Gamma \ M is contained in that set, and H(Gamma \ M) = 0 (measure_mono_null).
4. theta >= 1 H-a.e. on M. The hypothesis says 1 <= theta mu-a.e. The density ofReal o theta is a.e.-measurable for H restricted to M (V.aemeasurable_mult.ennreal_ofReal), so by ae_withDensity_iff', for (H restricted to M)-a.e. x: ofReal(theta x) != 0 implies 1 <= theta x. Also, for (H restricted to M)-a.e. x, x lies in M (ae_restrict_mem₀, M null-measurable), where theta x > 0 (V.mult_pos), so ofReal(theta x) != 0. Hence 1 <= ofReal(theta x) for (H restricted to M)-a.e. x.
5. Conclusion. As measures:
   H restricted to Gamma <= H restricted to M = (H restricted to M).withDensity 1 <= (H restricted to M).withDensity(ofReal o theta) = mu.
   The first inequality is Measure.restrict_mono_ae: Gamma is contained in M up to the H-null set Gamma \ M (step 3, ae_le_set). Then withDensity_one, and withDensity_mono with step 4. Equivalently, for every Borel B:
   H(B cap Gamma) <= H(B cap M) + H(Gamma \ M) = H(B cap M) <= integral over B of ofReal(theta) d(H restricted to M) = mu(B) (withDensity_apply).
   For an arbitrary set B: H(B cap Gamma) <= (H restricted to Gamma)(B) <= mu(B) (Measure.le_restrict_apply, Measure.le_iff'). In particular H(Gamma \ M) <= mu(complement of M) = 0. QED

## Key steps

1. Borel core M_1 of the carrier with mu(complement of M_1) = 0
2. Apply upper_density to mu and A = O cap M_1
3. Positive lower density at points of Gamma \ M contradicts zero density, so H^n(Gamma \ M) = 0
4. theta >= 1 H^n-a.e. on M via ae_withDensity_iff' and mult_pos
5. H^n restricted to Gamma <= H^n restricted to M = withDensity 1 <= withDensity(ofReal theta) = mu

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `python3 -I: print lean_statement of every subproblem in nodes/root-allard-any-radius-a1/decomposition-v2.json and nodes/root-allard-regularity-a1-graph-comparison-a1/decomposition-v{1,2}.json`
- `python3 -I scan of every lean_name in dag.json and nodes/*/*.json (409 reserved names); grep -rl anyrad_gc dag.json nodes GMT <snapshot>/project; git grep -l anyrad_gc <all refs> -- GMT/Ch05/Submission.lean (no match)`
- `python3 -I: dag.json nodes with status accepted/proved whose lean_statement mentions graphOver|tangentProj|hsNormSq|filterAt|withDensity|V.weight|μHE`
- `git show a8902dc6b193b40a3329c4ecc57e245a8e3c2b7c:GMT/Ch05/Submission.lean | grep -n '^theorem\|sorry\|import'; git show 066406829f5683c27ac3a01e8406376a154ff75a:GMT/Ch05/Submission.lean | grep import`
- `rg -n 'μHE\[' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -n 'hausdorffMeasure_image_le\|theorem hausdorffMeasure_smul₀\|theorem hausdorffMeasure_le_liminf_tsum\|mkMetric_le_liminf_tsum' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -n '^theorem\|^protected def' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean; grep -n 'theorem ae_tendsto_lintegral_enorm_sub_div\|theorem ae_tendsto_average_norm_sub' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean; grep -n 'protected def vitaliFamily\|theorem tendsto_filterAt' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `grep -rn 'theorem LipschitzOnWith.extend_pi\|theorem LipschitzOnWith.extend_real\|extend_lp_infty' Mathlib/Topology/MetricSpace; grep -n 'lipschitzOnWith_of_nnnorm_fderiv_le\|norm_image_sub_le_of_norm_fderiv_le' Mathlib/Analysis/Calculus/MeanValue.lean; grep -rn starProjection_norm_le Mathlib/Analysis/InnerProductSpace/Projection`
- `grep -n 'theorem\|lemma\|instance\|^def' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `python3 -I /tmp/gc-split-k7/scripts/closure.py <the 15 frozen header imports> (transitive import closure: 3203 modules)`
- `sed -n on runtime.py (_solve_children, _existing_lean_name_problem, _accepted_checkpoint), leaf_verification.py (check_source_delta), parent_verification.py; cat swarm-project.json (max_nodes 1000); len(dag.json nodes) = 200`
- `lake build GMT.Ch05.Submission in the scratch copy /tmp/gc-split-k7/proj (packages symlinked to the workspace .lake/packages)`
- `lake env lean Checks/Types.lean; lake env lean Checks/Assembly.lean; lake env lean Val/GraphTransfer.lean Val/HausdorffLeWeight.lean Val/GraphTangent.lean Val/Lebesgue.lean; python3 -I scripts/stmtcheck.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-comparison-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-comparison-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-tangent-plane-facts-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-tangent-plane-facts-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-tangent-plane-facts-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-ae-tangent-planes-a1-upper-density-zero-a1/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/parent_verification.py`
- `/tmp/gc-split-k7/closure.txt`
- `/tmp/gc-split-k7/proj/Checks/Types.lean`
- `/tmp/gc-split-k7/proj/Checks/Assembly.lean`
- `/tmp/gc-split-k7/proj/Val/GraphTransfer.lean`
- `/tmp/gc-split-k7/proj/Val/HausdorffLeWeight.lean`
- `/tmp/gc-split-k7/proj/Val/GraphTangent.lean`
- `/tmp/gc-split-k7/proj/Val/Lebesgue.lean`

Snapshot and reuse
- manifest.json pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d; the workspace GMT/Ch05/Submission.lean is the frozen contract file.
- Two accepted declarations from other branches cover parts of this proof and are reused with byte-identical frozen types (accepted, candidate commit present, comparator passed):
  - aetp_upper_density_zero_ae: the Upper Density Theorem (candidate 066406829f…).
  - ted_tangent_plane_facts: tangent-plane existence, measurability, density, and locality along Lipschitz graphs (candidate a8902dc6…; a sorry-free proof of about 1500 lines).
- Other accepted lemmas were found but are not needed: upperDensity_ne_zero_outside_hausdorff_null, rsod_blowUp_setIntegral_eq, lip_approx_graph_coordinates, allard52_tangent_ae, lgc_tangent_plane_ae.
- No-match: anyrad_gc_* occurs nowhere (dag.json, node files, snapshot project, all git refs). The 409 reserved names include none of the new names.

Library
All of the following are in the transitive import closure of the frozen header (3203 modules, computed from source and confirmed by #check), so leaves need no new import:
- LipschitzWith.hausdorffMeasure_image_le and Measure.hausdorffMeasure_le_liminf_tsum (Measure/Hausdorff.lean);
- Measure.euclideanHausdorffMeasure_def and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean);
- Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall;
- VitaliFamily.ae_tendsto_lintegral_enorm_sub_div(_of_integrable), with Besicovitch.vitaliFamily and Besicovitch.tendsto_filterAt;
- MeasurableSet.image_of_continuousOn_injOn (Lusin–Souslin);
- Convex.lipschitzOnWith_of_nnnorm_fderiv_le, LipschitzOnWith.extend_pi and extend_finite_dimension;
- Submodule.starProjection_norm_le and Integrable.of_bound;
- SimonGMT HasWeightedApproximateTangentSpaceAt and its .unique.

Controller rules
- runtime.py reuses an accepted cross-branch node only when the lean_statement is identical.
- leaf_verification.check_source_delta makes each leaf one appended theorem with no imports.
- max_nodes is 1000 and the DAG has 200 nodes.

Lean checks
- All 7 child types elaborate.
- Assembly.lean proves the exact selected type sorry-free (propext, Classical.choice, Quot.sound).
- The 5 new children are proved in scratch as single theorems.
