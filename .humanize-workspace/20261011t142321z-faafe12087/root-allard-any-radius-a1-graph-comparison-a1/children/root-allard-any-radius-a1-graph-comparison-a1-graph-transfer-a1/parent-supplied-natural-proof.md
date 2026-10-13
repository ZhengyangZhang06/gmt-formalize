# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.graph_comparison-a1`
- Child DAG node: `root.allard_any_radius-a1.graph_comparison-a1.graph_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 5 of the parent proof (Borel images by Lusin–Souslin; L^n(A') <= H^n(F(A')) <= mu(F(A')) gives (E1) through the push-forward F_#(L^n restricted to A), and transfers null sets to parameters). Here mu is replaced by any measure nu dominating H^n on the graph piece. Uses the sibling graph_volume (Submission.anyrad_gc_volume_le_graph_hausdorff). Notation: H := muHE[n] on R^(n+l). For every A, q(graph u over A) = F(A) (Set.image_image).
1. F is continuous on Omega and injective. graphPoint is continuous in (x, y): it is toLp o Fin.append applied to (ofLp x, ofLp y) (PiLp.continuous_toLp, PiLp.continuous_ofLp, Fin.continuous_append). The map x -> (x, u x) is continuous on Omega, and q is continuous, so F is continuous on Omega. If F x = F x', then graphPoint(x, u x) = graphPoint(x', u x') (q is injective); comparing the coordinates Fin.castAdd l i gives x = x'.
2. (a) Let A be Borel with A contained in Omega. F is continuous and injective on A, and R^n is a Polish space, so F(A) is Borel by the Lusin–Souslin theorem (MeasurableSet.image_of_continuousOn_injOn).
3. Key inequality. For every set S in R^(n+l):
   H(S cap Gamma) <= (H restricted to Gamma)(S) <= nu(S)
   by Measure.le_restrict_apply and the hypothesis applied to arbitrary sets (Measure.le_iff'). Combined with graph_volume (L^n(B) <= H(F(B)) for every B in R^n): if B is contained in Omega and F(B) is contained in S, then
   L^n(B) <= H(F(B)) <= H(S cap Gamma) <= nu(S).
4. (b) Let A be Borel with A contained in Omega, and g Borel. F is a.e.-measurable for L^n restricted to A (ContinuousOn.aemeasurable). Let m := F_#(L^n restricted to A) (Measure.map).
   For Borel B, m(B) = L^n(F^-1(B) cap A) (Measure.map_apply_of_aemeasurable, Measure.restrict_apply'). F(F^-1(B) cap A) is contained in (B cap F(A)) cap Gamma, so by step 3, m(B) <= nu(B cap F(A)) = (nu restricted to F(A))(B) (Measure.restrict_apply). Hence m <= nu restricted to F(A) (Measure.le_iff).
   Therefore: integral over A of g(F x) dx = integral of g dm (lintegral_map') <= integral of g d(nu restricted to F(A)) (lintegral_mono') = integral over q(graph u over A) of g dnu.
5. (c) Let P hold nu-a.e., i.e. nu({y : not P y}) = 0. Since Omega is Borel, (L^n restricted to Omega)({x : not P(F x)}) = L^n({x : not P(F x)} cap Omega) (Measure.restrict_apply'). The F-image of this set is contained in {y : not P y} cap Gamma, so by step 3 its L^n-measure is <= nu({y : not P y}) = 0. Hence P(F x) holds for L^n-a.e. x in Omega (ae_iff). QED

## Key steps

1. F = q o graphPoint(., u(.)) is continuous on Omega and injective
2. Lusin–Souslin gives Borel images F(A)
3. graph_volume plus H^n restricted to Gamma <= nu give L^n(B) <= nu(S) whenever F(B) is contained in S
4. The push-forward of L^n restricted to A is <= nu restricted to F(A); lintegral_map' gives (b)
5. nu-null sets pull back to L^n-null parameter sets in Omega: (c)

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
