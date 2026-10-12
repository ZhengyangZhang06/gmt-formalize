# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.translate_varifold-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.translate_varifold-a1.gmc_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: second half of Step 5 and Step 6 of the parent-supplied proof. Notation: mu := V.weight, H'(y) := H(y + xi). The map tau is a homeomorphism (Homeomorph.subRight xi), in particular a topological embedding, and a measurable embedding (MeasurableEquiv.subRight xi); it is injective. By hypothesis V'.weight = mu.map tau, and V has generalized mean curvature H in U, i.e. (A) H is locally mu-integrable on U and (B) integral of V.divM X dmu = - integral of <X, H> dmu for every C^1 map X with compact support and tsupport X contained in U.

1. Local integrability of H' on tau(U) for V'.weight. Let y be in tau(U), say y = tau(x) with x in U. By (A) there is N in the filter nhdsWithin(x, U) with H integrable on N for mu.
(a) tau(N) belongs to nhdsWithin(y, tau(U)): since tau is an embedding, map tau (nhdsWithin(x, U)) = nhdsWithin(tau x, tau(U)) (Topology.IsEmbedding.map_nhdsWithin_eq), and tau(N) belongs to map tau (nhdsWithin(x, U)) because N is contained in tau^{-1}(tau(N)) (image_mem_map).
(b) H' is integrable on tau(N) for V'.weight: the restriction (mu.map tau) restricted to tau(N) equals (mu restricted to tau^{-1}(tau(N))).map tau (MeasurableEmbedding.restrict_map), and tau^{-1}(tau(N)) = N by injectivity. By MeasurableEmbedding.integrable_map_iff, H' is integrable for (mu restricted to N).map tau if and only if H' o tau is integrable for mu restricted to N; and H' o tau = H because H'(x - xi) = H(x - xi + xi) = H(x). So this is the choice of N.
Thus H' is integrable at the filter nhdsWithin(y, tau(U)) for every y in tau(U), i.e. LocallyIntegrableOn H' (tau(U)) V'.weight.

2. First variation. Let X : R^(n+l) -> R^(n+l) be C^1 with compact support and tsupport X contained in tau(U). Put Y(x) := X(x - xi), i.e. Y = X o tau.
(a) Y is C^1, as the composition of X with the affine map x -> x - xi.
(b) Y has compact support, because tau is a homeomorphism (HasCompactSupport.comp_homeomorph).
(c) tsupport Y is contained in U: tsupport(X o tau) = tau^{-1}(tsupport X) for the homeomorphism tau (tsupport_comp_eq_preimage). If tau(x) is in tsupport X, which is contained in tau(U), then tau(x) = tau(u) for some u in U, and injectivity of tau gives x = u in U.
(d) Pointwise divergence identity: for every x, V'.divM X (x - xi) = V.divM Y x. Indeed V'.divM X (x - xi) = trace(DX(x - xi) o V'.tangentProj(x - xi)); by hypothesis V'.tangentProj(x - xi) = V.tangentProj(x - xi + xi) = V.tangentProj x; and DY(x) = DX(x - xi) (fderiv_comp_sub, which needs no differentiability hypothesis). Hence V'.divM X (x - xi) = trace(DY(x) o V.tangentProj x) = V.divM Y x.
(e) Change of variables: for a measurable embedding tau and every integrand g (no measurability needed), integral of g d(mu.map tau) = integral of g(tau x) dmu(x) (MeasurableEmbedding.integral_map). Therefore
integral of V'.divM X dV'.weight = integral of V'.divM X (x - xi) dmu(x) = integral of V.divM Y dmu (by (d)) = - integral of <Y(x), H(x)> dmu(x) (by (B), applicable to Y by (a), (b), (c)) = - integral of <X(x - xi), H'(x - xi)> dmu(x) (since H'(x - xi) = H(x)) = - integral of <X(y), H'(y)> dV'.weight(y) (change of variables again).

3. Steps 1 and 2 are exactly the two conjuncts of V'.HasGeneralizedMeanCurvature (fun y => H (y + xi)) in tau(U).

## Key steps

1. tau(N) lies in nhdsWithin(tau x, tau U) whenever N lies in nhdsWithin(x, U), since tau is an embedding
2. integrability of H(. + xi) on tau(N) for mu.map tau reduces to integrability of H on N via MeasurableEmbedding.integrable_map_iff
3. for X in C^1_c with tsupport in tau(U), Y = X(. - xi) is C^1_c with tsupport in U
4. V'.divM X (x - xi) = V.divM Y x from the tangentProj hypothesis and fderiv_comp_sub
5. change variables in both integrals with MeasurableEmbedding.integral_map and apply V's first-variation identity to Y

## Reference use

### local-project

Queries:
- `rg -n 'dohr_tv_|dohr_translate' <snapshot>`
- `rg -n -i 'translat' <snapshot>/project/GMT`
- `rg -n 'support_map|map_support' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/`
- `rg -n 'theorem .*withDensity.*map|lemma .*withDensity.*map|theorem .*map.*withDensity|lemma .*map.*withDensity' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -n 'measurePreserving_euclideanHausdorffMeasure|euclideanHausdorffMeasure_image' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'def divRight|def mulRight' <snapshot>/mathlib/Mathlib/Topology/MetricSpace/IsometricSMul.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Group/MeasurableEquiv.lean`
- `rg -n 'lemma mem_support_iff_forall' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n 'theorem lintegral_map_equiv|theorem image_eq_preimage_symm|theorem restrict_map' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean <snapshot>/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'MeasurableEmbedding.integral_map|MeasurableEmbedding.integrable_map_iff' <snapshot>/mathlib/Mathlib`
- `rg -n 'integrableOn_comp_preimage|theorem restrict_preimage_emb|NullMeasurableSet.preimage|theorem comp_quasiMeasurePreserving' <snapshot>/mathlib/Mathlib/MeasureTheory <snapshot>/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `rg -n 'theorem fderiv_comp_sub ' <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `rg -n 'lemma Topology.IsEmbedding.map_nhdsWithin_eq' <snapshot>/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `rg -n 'HasCompactMulSupport.comp_homeomorph|mulTSupport_comp_eq_preimage' <snapshot>/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `grep -n 'def CountablyRectifiable|def blowUpMap|def HasWeightedApproximateTangentSpaceAt' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n -i 'translat|blowUpMap_|subRight|addRight' .lake/packages/simongmt/Poincare/SimonGMT`
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean`
- `lake env lean -o /tmp/dohr-tv-check/build/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/dohr-tv-check/build lean /tmp/dohr-tv-check/src/Children.lean'`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/dohr-tv-check/build lean /tmp/dohr-tv-check/src/Full.lean'`
- `python3 -I name-collision check of the 5 proposed lean_names against all 79 lean_name fields of .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/IsometricSMul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/MeasurableEquiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-translate-varifold-a1/parent-child-handoff.json`
- `/tmp/dohr-tv-check/src/Children.lean`
- `/tmp/dohr-tv-check/src/Full.lean`

The pinned snapshot (manifest.json) records project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. Its Contract.lean and Submission.lean are byte-identical to the workspace copies (cmp).

Nothing to reuse for this node:
- Neither the snapshot nor simongmt has a translation lemma for the contract's RectifiableVarifold. 'translat' matches only a remark in the Ch08 README, and 'dohr_tv_' matches nothing anywhere.
- Mathlib has no lemma for the support of a pushforward ('support_map' / 'map_support' match nothing in Measure/Support.lean).
- Mathlib has no general map-of-withDensity lemma for measurable equivalences; only Jacobian and rnDeriv variants exist.
So children 2 and 3 are real obligations.

Library facts the child proofs use (snapshot line numbers):
- IsometryEquiv.measurePreserving_euclideanHausdorffMeasure and Isometry.euclideanHausdorffMeasure_image: Geometry/Euclidean/Volume/Measure.lean:127, 131.
- Translations subRight/addRight, the to_additive forms of divRight/mulRight: Topology/MetricSpace/IsometricSMul.lean:157, 167 and MeasureTheory/Group/MeasurableEquiv.lean:117, 193.
- Measure.mem_support_iff_forall: Support.lean:75.
- lintegral_map_equiv: Integral/Lebesgue/Map.lean:94.
- MeasurableEquiv.image_eq_preimage_symm: MeasurableSpace/Embedding.lean:315.
- MeasurableEquiv.restrict_map: Measure/Restrict.lean:890.
- MeasurableEmbedding.integral_map: Bochner/Basic.lean:1093.
- MeasurableEmbedding.integrable_map_iff: L1Space/Integrable.lean:374.
- MeasurePreserving.integrableOn_comp_preimage: IntegrableOn.lean:319.
- MeasurePreserving.restrict_preimage_emb: Dynamics/Ergodic/MeasurePreserving.lean:81.
- NullMeasurableSet.preimage: QuasiMeasurePreserving.lean:134.
- fderiv_comp_sub: FDeriv/Add.lean:892.
- Topology.IsEmbedding.map_nhdsWithin_eq: ContinuousOn.lean:841.
- HasCompactSupport.comp_homeomorph and tsupport_comp_eq_preimage: to_additive forms at Topology/Algebra/Support.lean:562 and 106.
- simongmt Chapter03/Rectifiable.lean: CountablyRectifiable (l.34), blowUpMap (l.96), HasWeightedApproximateTangentSpaceAt (l.330). Its blow-up form makes the tangent-plane transport a direct rewrite.

Lean checks used the pinned toolchain with Submission compiled to a scratch olean:
- All five child statements elaborate.
- The parent assembly from the five sorry'd children compiles with no sorry of its own.
- Complete scratch proofs of all five children compile, and #print axioms gives only [propext, Classical.choice, Quot.sound] for each child and for Submission.dohr_translate_varifold.
- The independent reviewer reproduced these results.

The five dohr_tv_ names collide with none of the 79 DAG lean_names.
