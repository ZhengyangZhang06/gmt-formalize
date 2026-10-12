# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.graph_comparison-a1`
- Child DAG node: `root.allard_any_radius-a1.graph_comparison-a1.graph_volume-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof (the 1-Lipschitz left inverse pi of the graph map) together with step 5 (L^n(A') = H^n(pi(F(A'))) <= H^n(F(A')), using that pi is 1-Lipschitz and H^n = L^n on R^n). Notation: S := q(graph u over A) = {q(graphPoint(x, u x)) : x in A}.
1. Projection. Let pi : R^(n+l) -> R^n, pi(z) := (z_1, ..., z_n), the first n coordinates. In Lean this is WithLp.toLp 2 (fun i : Fin n => z (Fin.castAdd l i)).
   (a) pi(graphPoint(x, y)) = x, since graphPoint(x, y) = toLp (Fin.append x y) and Fin.append x y (Fin.castAdd l i) = x i (Fin.append_left).
   (b) For all z, z': |pi z - pi z'|^2 = sum over i < n of (z_i - z'_i)^2 <= sum over j < n + l of (z_j - z'_j)^2 = |z - z'|^2. To see this, split the sum over Fin (n + l) with Fin.sum_univ_add; the remaining part is a sum of squares, hence >= 0. So pi is 1-Lipschitz.
2. Left inverse. phi := pi o q^-1 is 1-Lipschitz, because q^-1 is an isometry. Also phi(q(graphPoint(x, u x))) = pi(graphPoint(x, u x)) = x, hence phi(S) = A.
3. Lipschitz image bound. On every metric space, muHE[n] = c_n muH[n] with the same scalar c_n = addHaarScalarFactor(volume on EuclideanSpace R (Fin n), muH[n]), which depends only on n (Measure.euclideanHausdorffMeasure_def). By LipschitzWith.hausdorffMeasure_image_le with K = 1 and d = n >= 0: muH[n](phi(S)) <= 1^n muH[n](S) = muH[n](S). Multiplying by c_n gives muHE[n](phi(S)) <= muHE[n](S).
4. Normalisation on R^n. muHE[n] = volume on EuclideanSpace R (Fin n) (EuclideanSpace.euclideanHausdorffMeasure_eq_volume). Therefore L^n(A) = muHE[n](A) = muHE[n](phi(S)) <= muHE[n](S) = H^n(q(graph u over A)). QED

## Key steps

1. The first-n-coordinates map pi is 1-Lipschitz and pi(graphPoint(x, y)) = x
2. phi = pi o q^-1 is 1-Lipschitz and maps q(graph u over A) onto A
3. Lipschitz image bound for muH[n], transported to muHE[n] = c_n muH[n] with the same c_n on both spaces
4. muHE[n] equals Lebesgue measure on R^n

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
