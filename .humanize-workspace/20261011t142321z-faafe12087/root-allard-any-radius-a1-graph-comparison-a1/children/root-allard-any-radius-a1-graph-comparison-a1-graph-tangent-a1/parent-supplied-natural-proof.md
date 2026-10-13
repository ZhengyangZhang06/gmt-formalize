# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.graph_comparison-a1`
- Child DAG node: `root.allard_any_radius-a1.graph_comparison-a1.graph_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof ("locality of approximate tangents, Simon Ch. 3, Remark 1.8(1), identifies p on the graph with q(graph Du) a.e.") and step 5 (null sets transfer to parameters). The locality statement is taken from the sibling tangent_facts (Submission.ted_tangent_plane_facts, conjunct (4)). That conjunct proves, for Lipschitz graphs, exactly the blow-up identification of step 6: Lebesgue points of theta on the graph, zero density of M \ Gamma and Gamma \ M, and convergence of the blown-up graphs to the tangent plane. Its exceptional set is mu-null, which the transfer hypothesis handles. Notation: T(x) := image under q of span{graphPoint(v, Du(x) v) : v in R^n}, i.e. Submodule.map q (span (range (v -> graphPoint v (Du(x) v)))).
1. Regularity of u. u is C^1 on the open set Omega. So u is differentiable at every x in Omega (ContDiffOn.differentiableOn_one, and Omega is a neighbourhood of x), and x -> Du(x) is continuous on Omega (ContDiffOn.continuousOn_fderiv_of_isOpen).
2. Local Lipschitz extension. Fix x_0 in Omega and e > 0 with B°_e(x_0) contained in Omega. Put r := e/2 and K := B_r(x_0) (closed ball); K is contained in Omega and is compact and convex.
   ||Du|| is continuous on K, hence bounded there by some C (IsCompact.exists_bound_of_continuousOn). By the mean value inequality on the convex set K, u is L-Lipschitz on K with L := max(C, 0) (Convex.lipschitzOnWith_of_nnnorm_fderiv_le).
   Extend u restricted to K to a map f : R^n -> R^l that is Lipschitz on all of R^n and equals u on K. One way is LipschitzOnWith.extend_finite_dimension. Another is a coordinatewise McShane extension (LipschitzOnWith.extend_pi for x -> ofLp(u x), then toLp, which is Lipschitz as a linear map between finite-dimensional spaces).
   Put R := |x_0| + r. Then B°_r(x_0) is contained in B°_R(0) (triangle inequality), and f is Lipschitz on B_R(0).
3. Apply tangent_facts (4) to q, f, R and the Lipschitz constant of f. It gives a mu-a.e. property Q(y):
   "for all x' in B°_R(0), if y = q(graphPoint(x', f x')) and f is differentiable at x', then V.tangentProj y is the orthogonal projection onto span{q(graphPoint(v, Df(x') v)) : v in R^n}".
   By the transfer hypothesis, Q(F x) holds for L^n-a.e. x in Omega.
4. Let x in B°_r(x_0) satisfy Q(F x).
   (a) x lies in B°_R(0), and f(x) = u(x) since x is in K; so F x = q(graphPoint(x, f x)).
   (b) f = u on the open ball B°_r(x_0), a neighbourhood of x. Hence f is differentiable at x, because u is (step 1; DifferentiableAt.congr_of_eventuallyEq), and Df(x) = Du(x) (Filter.EventuallyEq.fderiv_eq).
   (c) So Q(F x) gives V.tangentProj(F x) = orthogonal projection onto span{q(graphPoint(v, Du(x) v))}.
   (d) span{q(w) : w in W} = map q (span W) with W := range(v -> graphPoint(v, Du(x) v)) (Submodule.map_span, Set.range_comp). This is T(x), so V.tangentProj(F x) = T(x).starProjection. In Lean, prove the submodule equality first and conclude by congr, since starProjection carries an instance argument.
   Hence the set of x in Omega cap B°_r(x_0) where the conclusion fails is L^n-null.
5. Local to global. Every x_0 in Omega has a neighbourhood B°_r(x_0) on which the failure set is L^n-null (step 4). R^n is second countable, so countably many of these balls cover Omega, and the failure set in Omega is L^n-null. One can use measure_null_of_locally_null, or a countable cover by balls with centres in a countable dense set and rational radii together with ae_all_iff. Together with ae_restrict_mem (Omega is open, hence Borel), this is the claim: for L^n-a.e. x in Omega, V.tangentProj(F x) = T(x).starProjection. QED

## Key steps

1. u is differentiable on Omega with continuous Du
2. On a closed ball K in Omega u is Lipschitz (mean value inequality); extend to a globally Lipschitz f equal to u on K
3. tangent_facts (4) for (q, f, R) gives the graph tangent identity mu-a.e.; transfer it to parameters
4. On the open ball f = u near x, so Df(x) = Du(x) and span{q(graphPoint(v, Du v))} = q(span{graphPoint(v, Du v)})
5. Countably many balls (Lindelöf / measure_null_of_locally_null) give the L^n-a.e. statement on Omega

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
