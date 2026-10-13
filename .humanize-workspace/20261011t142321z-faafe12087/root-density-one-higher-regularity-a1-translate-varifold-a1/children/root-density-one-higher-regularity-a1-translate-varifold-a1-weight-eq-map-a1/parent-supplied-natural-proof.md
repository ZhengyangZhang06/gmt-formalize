# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.translate_varifold-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.translate_varifold-a1.weight_eq_map-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 3 of the parent-supplied proof; the needed translation invariance of H^n and change of variables (the parent's fact (I1)) are restated in steps 1, 2 and 5. Notation: H^n := muHE[n], M := V.carrier, theta := V.mult, e := MeasurableEquiv.subRight xi (its underlying function is tau and its inverse is y -> y + xi), mu_V := V.weight = (H^n restricted to M).withDensity(x -> ofReal(theta(x))), mu_V' := V'.weight = (H^n restricted to V'.carrier).withDensity(y -> ofReal(V'.mult(y))). For a measure nu and a set A, nu|A denotes the restriction.

1. tau is H^n-measure preserving: tau is the isometric bijection IsometryEquiv.subRight xi, and muHE[n] is preserved by isometric bijections (IsometryEquiv.measurePreserving_euclideanHausdorffMeasure). Hence Measure.map tau H^n = H^n.

2. (H^n|M).map tau = H^n|tau(M). For a measurable equivalence e, every measure nu and every set s, (nu.map e)|s = (nu|e^{-1}(s)).map e (MeasurableEquiv.restrict_map). Apply this with nu = H^n and s = e.symm^{-1}(M), which equals tau(M) (MeasurableEquiv.image_eq_preimage_symm). Since e^{-1}(e.symm^{-1}(M)) = M, we get (H^n.map tau)|tau(M) = (H^n|M).map tau, and H^n.map tau = H^n by step 1.

3. By Measure.ext it suffices to show that mu_V' and mu_V.map tau agree on every measurable set S. Fix a measurable S; tau^{-1}(S) is measurable because tau is measurable.

4. Right-hand side: (mu_V.map tau)(S) = mu_V(tau^{-1}(S)) (Measure.map_apply, tau measurable, S measurable) = integral over tau^{-1}(S) of ofReal(theta(x)) d(H^n|M)(x) (withDensity_apply, tau^{-1}(S) measurable).

5. Left-hand side: mu_V'(S) = integral over S of ofReal(V'.mult(y)) d(H^n|V'.carrier)(y) (withDensity_apply, S measurable). Since V'.carrier = tau(M), the measure of integration is (H^n|tau(M))|S, which by step 2 and MeasurableEquiv.restrict_map equals ((H^n|M).map tau)|S = ((H^n|M)|tau^{-1}(S)).map tau. The change-of-variables formula for a measurable equivalence, integral of f d(nu.map e) = integral of f(e x) dnu(x), holds for every f >= 0 without any measurability assumption (lintegral_map_equiv). Therefore mu_V'(S) = integral of ofReal(V'.mult(x - xi)) d((H^n|M)|tau^{-1}(S))(x). Finally V'.mult(x - xi) = theta(x - xi + xi) = theta(x), so mu_V'(S) = integral over tau^{-1}(S) of ofReal(theta(x)) d(H^n|M)(x).

6. Steps 4 and 5 give mu_V'(S) = (mu_V.map tau)(S) for every measurable S, hence V'.weight = V.weight.map (fun x => x - xi).

## Key steps

1. tau is H^n-measure preserving because it is an isometric bijection
2. (H^n restricted to M) pushed forward by tau equals H^n restricted to tau(M), via MeasurableEquiv.restrict_map
3. reduce to measurable S by Measure.ext and evaluate both sides with withDensity_apply
4. change variables with lintegral_map_equiv (no measurability needed) and use V'.mult(x - xi) = theta(x)

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
