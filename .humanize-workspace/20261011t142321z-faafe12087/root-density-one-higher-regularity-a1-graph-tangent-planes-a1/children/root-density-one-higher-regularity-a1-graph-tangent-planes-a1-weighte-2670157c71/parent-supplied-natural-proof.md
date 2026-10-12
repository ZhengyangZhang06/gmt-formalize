# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.weighted_tangent_ae-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. H := muHE[n] on E := Amb n l, nu := H restricted to S cap O, f := M.indicator theta. Sibling results used: (LP) = dohr_tp_ae_lebesgue_point_of_growth and (PT) = dohr_tp_weighted_tangent_of_lebesgue_point.

1. Growth of nu. For z in E and r > 0: nu(closedBall z r) = H(closedBall z r cap (S cap O)) = H(S cap O cap closedBall z r) <= ENNReal.ofReal (C r^n) (Measure.restrict_apply; closed balls are measurable).

2. f is nu-integrable. f is H-a.e.-measurable (aemeasurable_indicator_iff₀, M null-measurable, theta a.e.-measurable for H restricted to M), hence a.e.-strongly measurable for nu. M is nu-null-measurable (nu is absolutely continuous with respect to H), so the lintegral of |f|_e dnu equals the lintegral over M of |theta|_e dnu (lintegral_indicator₀), which equals the lintegral over M cap (S cap O) of |theta|_e dH (Measure.restrict_restrict₀) and is at most the lintegral over M cap O of |theta|_e dH < infinity, because theta is integrable on M cap O.

3. Lebesgue points. By (LP) applied to nu, f and C (using steps 1-2): for nu-a.e. y, ENNReal.ofReal (r^{-n}) * (lintegral over closedBall y r of |f w - f y|_e dnu) -> 0 as r -> 0+. Let Leb be the set of such y. Then nu(E minus Leb) = 0, and H((E minus Leb) cap (S cap O)) <= nu(E minus Leb) = 0 (Measure.le_restrict_apply).

4. Good points. Let y be in M cap O cap S cap Leb and let P satisfy HasApproximateTangentSpaceAt n S y P. Since O is open, choose eps > 0 with ball y eps contained in O (Metric.isOpen_iff). Then: (a) H((M cap ball y eps) minus S) <= H((M cap O) minus S) = 0; (b) H(S cap ball y eps) <= H(S cap O cap closedBall y eps) <= ENNReal.ofReal (C eps^n) < infinity; (c) f(y) = theta(y) because y is in M; (d) for 0 < r < eps, closedBall y r is contained in ball y eps, hence in O, so closedBall y r cap (S cap O) = S cap closedBall y r and the lintegral over closedBall y r of |f w - f y|_e dnu equals the lintegral over S cap closedBall y r of |M.indicator theta w - theta y|_e dH (Measure.restrict_restrict). By (d), the function in the definition of Leb and the function in the Lebesgue hypothesis of (PT) agree for r in (0, eps), a set in nhdsWithin 0 (Ioi 0), so the latter also tends to 0 as r -> 0+ (Tendsto.congr'). With (a), (b), the null-measurability of M and the a.e.-measurability of theta, (PT) applied to M, S, theta, y, P and eps gives HasWeightedApproximateTangentSpaceAt n M theta y P.

5. Exceptional set. Let y be in M and suppose the asserted implication fails at y: y is in O and some P satisfies HasApproximateTangentSpaceAt n S y P but not the weighted property. By step 4, either y is not in S, so y lies in (M cap O) minus S, or y is in S but not in Leb, so y lies in (E minus Leb) cap (S cap O). Both sets are H-null (hypothesis and step 3), so the failure set meets M in an H-null set (measure_union_null). Since M is H-null-measurable, (H restricted to M)(failure set) = H(failure set cap M) = 0 (Measure.restrict_apply₀'), which is the asserted almost-everywhere statement (ae_iff).

## Key steps

1. nu := H^n restricted to S cap O has n-dimensional growth and f := 1_M theta is nu-integrable
2. sibling dohr_tp_ae_lebesgue_point_of_growth: nu-a.e. point is a Lebesgue point of f; the exceptional set meets S cap O in an H^n-null set
3. at y in M cap O cap S that is a Lebesgue point, the Lebesgue integrals for nu and for H^n on S agree for small r
4. sibling dohr_tp_weighted_tangent_of_lebesgue_point turns each approximate tangent plane of S at y into a weighted one of (M, theta)
5. the failure set inside M lies in ((M cap O) minus S) union (non-Lebesgue points of S cap O), which is H^n-null

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; git rev-parse HEAD (project ea56075..., .lake/packages/mathlib 25730c7c..., .lake/packages/simongmt 2b366308...)`
- `diff GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean; diff GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Submission.lean`
- `rg -n 'dohr_tp_|dohr_graph_tangent_planes' <snapshot>; grep -c dohr_tp_ dag.json; grep -rl dohr_tp_ <run>/nodes GMT .lake/packages/simongmt`
- `rg -n 'theorem ae_tendsto_lintegral_enorm_sub_div' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `rg -n 'theorem tendsto_filterAt' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n 'theorem hausdorffMeasure_image_le' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'theorem inverse_continuousAt' <snapshot>/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `rg -n 'theorem eq_starProjection_of_mem_of_inner_eq_zero|theorem starProjection_map_apply' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n 'theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul|theorem integral_image_eq_integral_abs_det_fderiv_smul' <snapshot>/mathlib/Mathlib`
- `grep -n 'instance.*HasBesicovitchCovering' Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean; grep -n 'def comp ' Mathlib/Topology/ContinuousMap/CompactlySupported.lean`
- `sed -n 1,200p .lake/packages/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -n 'def HasApproximateTangentSpaceAt|def HasWeightedApproximateTangentSpaceAt|def blowUpMap|theorem HasWeightedApproximateTangentSpaceAt.unique' -A 22 .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `lean -o build/GMT/Ch05/Submission.olean (fresh scratch compile of the frozen GMT/Ch05/Submission.lean)`
- `lean Probe.lean (#check of the cited Mathlib/SimonGMT lemmas under import GMT.Ch05.Submission)`
- `lean Probe2.lean (#check Poincare.SimonGMT.Chapter02.injective_area_formula_lipschitzOn, LinearMap.normDet, ContinuousLinearMap.adjoint, LinearMap.adjoint; HasSummableGeomSeries (Rn n ->L[R] Rn n); (a * b) v = a (b v))`
- `python3 -I gen_children.py (lean_contract.validate_lean_statement + gmt-compare.child_modules contract mode) then lean on the 7 NodeChallenge and 7 NodeSolution modules`
- `lean Assembly.lean; #print axioms Submission.dohr_graph_tangent_planes`
- `lean Child6.lean; #print axioms Submission.dohr_tp_ae_weighted_tangent_of_growth`
- `python3 scan of dag.json: accepted checkpoints, and lean_statements mentioning HasApproximateTangentSpaceAt / HasWeightedApproximateTangentSpaceAt / starProjection`
- `grep -rn max_nodes /runtime/flows/gmt-claude-6e6a457c9391; sed -n 1793,1990p _recursive_lean/runtime.py; sed -n 6490,6560p _recursive_lean/runtime.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1/decomposition-audit-v3.json`
- `/runtime/flows/gmt-claude-6e6a457c9391/__init__.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/models.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/gtp5-tZl9KO/src/Probe.lean`
- `/tmp/gtp5-tZl9KO/src/Probe2.lean`
- `/tmp/gtp5-tZl9KO/src/Assembly.lean`
- `/tmp/gtp5-tZl9KO/src/Child6.lean`
- `/tmp/gtp5-tZl9KO/gen/NodeChallenge_graph_approx_tangent.lean`

Snapshot manifest pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace HEAD and .lake/packages/mathlib match them, and simongmt is at its pinned 2b3663083f3f. The workspace Contract.lean and Submission.lean are byte-identical to the snapshot copies.

rg finds no 'dohr_tp_' or 'dohr_graph_tangent_planes' anywhere in the snapshot. dag.json has 0 'dohr_tp_' matches, and the only node-directory matches are this node's unactivated v2 records, so the 7 proposed names are free.

The pinned Mathlib supplies:
- VitaliFamily.ae_tendsto_lintegral_enorm_sub_div (Differentiation.lean:818)
- Besicovitch.tendsto_filterAt (Besicovitch.lean:1060)
- instHasBesicovitchCovering (BesicovitchVectorSpace.lean:499)
- LipschitzOnWith.hausdorffMeasure_image_le (Hausdorff.lean:733)
- euclideanHausdorffMeasure_def, IsometryEquiv.measurePreserving_euclideanHausdorffMeasure, Isometry.euclideanHausdorffMeasure_image, Measure.euclideanHausdorffMeasure_smul₀ and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean)
- NormedRing.inverse_continuousAt (Units.lean:183)
- Submodule.eq_starProjection_of_mem_of_inner_eq_zero and Submodule.starProjection_map_apply (Projection/Basic.lean:180, 358)
- CompactlySupportedContinuousMap.comp
Mathlib's Jacobian change of variables (Jacobian.lean:1183/1213) only treats maps E -> E of equal dimension, so it is not an area formula for graphs.

SimonGMT Chapter03/Rectifiable.lean supplies blowUpMap, HasApproximateTangentSpaceAt (l.102), HasWeightedApproximateTangentSpaceAt (l.330) and its .unique (l.345).

Lean checks, run against a fresh scratch build of the frozen Submission:
- Every cited lemma resolves under the frozen imports.
- injective_area_formula_lipschitzOn, LinearMap.normDet, ContinuousLinearMap.adjoint and LinearMap.adjoint are unknown there. This is why child (1) uses a bi-Lipschitz comparison and child (7) uses a hand-built adjoint.
- All 7 statements pass validate_lean_statement and elaborate in the verifier-generated NodeChallenge modules. All 7 NodeSolution modules elaborate.
- The exact frozen parent type is proved from children (1), (2), (3), (6), (7) with axioms {propext, Classical.choice, Quot.sound} plus those children.
- Child (6) is proved from (4) and (5) with the same clean report.

None of the 17 accepted DAG checkpoints is an ingredient of this proof. Related tangent lemmas in other branches are unaccepted and have different types.

The controller's node bound is a hard 200 (Field le=200 in __init__.py), and dag.json holds 199 nodes. Activating these 7 children therefore needs the operator to resolve the cap at the orchestration level, as the v3 audit stated.
