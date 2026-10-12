# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.weighted_tangent_pointwise-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. E := Amb n l, H := muHE[n]. For r > 0, eta_r := blowUpMap y r, i.e. eta_r(w) = r^{-1} (w - y); it is a bijection of E with inverse z -> y + r z. f_M := M.indicator theta. For t > 0, L(t) := lintegral over S cap closedBall y t of |f_M w - theta y|_e dH(w).

1. Scaling identity. For r > 0, every set X in E and every g : E -> R: integral over eta_r '' X of g dH = r^{-n} * integral over X of g(eta_r w) dH(w). Proof: eta_r is a homeomorphism (hence a measurable embedding) and H(eta_r '' A) = r^{-n} H(A) for every set A in E, since eta_r is the translation w -> w - y (an isometry: Isometry.euclideanHausdorffMeasure_image) followed by multiplication by r^{-1} (Measure.euclideanHausdorffMeasure_smul₀, with |r^{-1}|^n = r^{-n}). Hence for measurable B: (Measure.map eta_r (H restricted to X))(B) = H(eta_r^{-1}(B) cap X) = r^n H(eta_r '' (eta_r^{-1}(B) cap X)) = r^n H(B cap eta_r '' X), i.e. H restricted to eta_r '' X equals r^{-n} times Measure.map eta_r (H restricted to X); now apply integral_smul_measure and MeasurableEmbedding.integral_map (no integrability or measurability of g is needed).

2. Rewriting both blow-ups. Fix phi in C_c(E, R); choose rho > 0 with phi(w) = 0 whenever |w| > rho, and put K := sup |phi| (finite). Let phi_r(w) := phi(eta_r(w)); phi_r is continuous, |phi_r| <= K, and phi_r(w) = 0 unless w lies in B_r := closedBall y (r rho). By step 1 with g(z) = phi(z) theta(y + r z), and since y + r eta_r(w) = w:
 I(r) := integral over eta_r '' M of phi(z) theta(y + r z) dH(z) = r^{-n} * integral over M of phi_r theta dH;
 J(r) := integral over eta_r '' S of phi dH = r^{-n} * integral over S of phi_r dH.

3. Localization. Let r > 0 with r rho < eps, so that B_r is contained in ball y eps. Since phi_r vanishes off the closed (measurable) ball B_r, the integral over S of phi_r dH equals the integral over S cap B_r of phi_r dH, and the integral over M of phi_r theta dH equals the integral over M cap B_r of phi_r theta dH (setIntegral_eq_integral_of_forall_compl_eq_zero for the restricted measure, then Measure.restrict_restrict). Since (M cap B_r) minus S is contained in (M cap ball y eps) minus S, which is H-null, the sets M cap B_r and S cap B_r cap M are H-a.e. equal, so the latter integral equals the integral over S cap B_r cap M of phi_r theta dH, which equals the integral over S cap B_r of phi_r f_M dH (M is null-measurable; integral of an indicator over a null-measurable set). These identities hold for Bochner integrals without any integrability assumption.

4. Integrability for small r. By the Lebesgue hypothesis choose r1 > 0 such that ENNReal.ofReal (t^{-n}) L(t) <= 1 for 0 < t < r1; since ENNReal.ofReal (t^{-n}) > 0, L(t) < infinity for these t. Also H(S cap closedBall y t) <= H(S cap ball y eps) < infinity for t < eps. Now let r > 0 with r rho < min(eps, r1). f_M is H-a.e.-measurable (aemeasurable_indicator_iff₀, using that M is null-measurable and theta is a.e.-measurable for H restricted to M), hence a.e.-strongly measurable for H restricted to S cap B_r, and the lintegral over S cap B_r of |f_M|_e is at most L(r rho) + |theta y|_e H(S cap B_r) < infinity. So f_M and the constant theta(y) are integrable on S cap B_r, and therefore so are phi_r f_M and phi_r theta(y) (phi_r is bounded and continuous).

5. Comparison. For such r, by steps 2-4 and linearity of the integral, I(r) - theta(y) J(r) = r^{-n} * integral over S cap B_r of phi_r (f_M - theta(y)) dH, hence |I(r) - theta(y) J(r)| <= r^{-n} K * integral over S cap B_r of |f_M - theta(y)| dH = K rho^n * (ENNReal.ofReal ((r rho)^{-n}) L(r rho)).toReal (the Bochner integral of the nonnegative integrable function |f_M - theta(y)| is the toReal of its lintegral, ofReal_integral_norm_eq_lintegral_enorm).

6. Limit. As r -> 0+, r rho -> 0 within (0, infinity), so ENNReal.ofReal ((r rho)^{-n}) L(r rho) -> 0 by the Lebesgue hypothesis; its toReal tends to 0 (ENNReal.tendsto_toReal at the finite limit 0), hence I(r) - theta(y) J(r) -> 0 by step 5. By the hypothesis HasApproximateTangentSpaceAt n S y P, J(r) -> integral over P of phi dH. Therefore I(r) = (I(r) - theta(y) J(r)) + theta(y) J(r) -> theta(y) * integral over P of phi dH.

7. Since phi in C_c(E, R) was arbitrary and finrank P = n (first component of the hypothesis on S), HasWeightedApproximateTangentSpaceAt n M theta y P holds.

## Key steps

1. scaling identity: integral over blowUpMap y r '' X of g dH^n = r^{-n} integral over X of g o blowUpMap y r
2. both blow-up integrals become r^{-n} integrals of phi_r over M (weighted by theta) and over S
3. localize to S cap B_{r rho}(y) and use H^n((M cap Bo_eps(y)) minus S) = 0 to replace M by S with weight 1_M theta
4. the Lebesgue hypothesis gives integrability for small r and makes I(r) - theta(y) J(r) tend to 0
5. J(r) tends to the plane integral by the unweighted tangent hypothesis, so I(r) tends to theta(y) times it

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
