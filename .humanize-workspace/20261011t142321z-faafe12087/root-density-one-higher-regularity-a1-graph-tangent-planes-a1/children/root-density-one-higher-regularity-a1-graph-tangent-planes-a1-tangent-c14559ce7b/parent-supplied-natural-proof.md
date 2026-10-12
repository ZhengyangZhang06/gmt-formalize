# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.tangent_projection_continuous-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. E := Amb n l, Bo := ball (0 : Rn n) R, G(z) := graphPoint z (u z), A(x) := fderiv R G x : Rn n ->L[R] E, and e_i := EuclideanSpace.single i 1 (i in Fin n) the standard basis of Rn n. Only facts available under the frozen imports of GMT.Ch05.Submission are used; in particular the adjoint is built by hand (ContinuousLinearMap.adjoint is not available there).

1. Derivative of the graph map. Phi(a, b) := graphPoint a b is a continuous linear map Rn n x Rn l -> E (its coordinates are those of a followed by those of b), and |graphPoint a b|^2 = |a|^2 + |b|^2 (split the coordinate sum over Fin (n+l) into Fin n and Fin l). Since u is C^1 on the open set Bo, u is differentiable at every x in Bo and x -> fderiv R u x is continuous on Bo (ContDiffOn.continuousOn_fderiv_of_isOpen). Hence G = Phi o (id, u) is differentiable at every x in Bo with A(x) v = graphPoint v (Du(x) v), x -> A(x) is continuous on Bo (it is the composition of x -> Du(x) with the continuous affine map psi -> Phi o (id, psi)), and |A(x) v| >= |v| for x in Bo and all v.

2. Hand-built adjoint. For A in Rn n ->L[R] E define A# : E ->L[R] Rn n by A# w := sum over i of <A e_i, w> e_i, a finite sum of the continuous linear maps (innerSL R (A e_i)).smulRight e_i. Expanding v = sum over i of v_i e_i gives <A# w, v> = sum over i of <A e_i, w> v_i = <A v, w> for all v, w. Each A -> A e_i is continuous linear, so A -> A# is continuous, and x -> A(x)# is continuous on Bo.

3. Invertibility. For x in Bo let N(x) := A(x)# composed with A(x), in Rn n ->L[R] Rn n. By step 2, <N(x) v, v> = |A(x) v|^2 >= |v|^2, so N(x) is injective, hence bijective because Rn n is finite-dimensional, hence IsUnit N(x) in the ring Rn n ->L[R] Rn n (ContinuousLinearMap.isUnit_iff_bijective). x -> N(x) is continuous on Bo (composition of continuous linear maps is jointly continuous), and Ring.inverse is continuous at every unit of the complete normed ring Rn n ->L[R] Rn n (NormedRing.inverse_continuousAt). Hence x -> Ring.inverse N(x) is continuous on Bo.

4. Projection formula. For x in Bo put Pi(x) := A(x) o Ring.inverse N(x) o A(x)#. For w in E, Pi(x) w lies in range A(x), and for every v, by step 2 and N(x) o Ring.inverse N(x) = id (Ring.mul_inverse_cancel for the unit N(x)): <w - Pi(x) w, A(x) v> = <A(x)# w - N(x) (Ring.inverse N(x)) (A(x)# w), v> = 0. By Submodule.eq_starProjection_of_mem_of_inner_eq_zero, (LinearMap.range A(x)).starProjection w = Pi(x) w. So on Bo the map x -> (LinearMap.range A(x)).starProjection coincides with x -> Pi(x), which is continuous on Bo by steps 1-3 and continuity of composition.

5. Rotation. For every subspace K, (Submodule.map Q.toLinearEquiv.toLinearMap K).starProjection = Q o K.starProjection o Q.symm (Submodule.starProjection_map_apply, applied pointwise, then ext). The map T -> Q o T o Q.symm is continuous on E ->L[R] E. Composing it with step 4 shows that x -> (Submodule.map Q.toLinearEquiv.toLinearMap (LinearMap.range A(x))).starProjection is continuous on Bo, which is the claim.

## Key steps

1. A(x) = DG(x) v = (v, Du(x) v) depends continuously on x in the ball and satisfies |A(x) v| >= |v|
2. hand-built adjoint A# with <A# w, v> = <A v, w>, continuous in A
3. N(x) = A(x)# A(x) is a unit, and Ring.inverse is continuous at units
4. the projection onto range A(x) is A (A# A)^{-1} A#, continuous in x
5. conjugation by Q gives the projection onto Q(range A(x))

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
