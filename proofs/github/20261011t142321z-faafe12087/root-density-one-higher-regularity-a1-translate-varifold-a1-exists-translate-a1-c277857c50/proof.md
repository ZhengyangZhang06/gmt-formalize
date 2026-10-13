# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.translate_varifold-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.translate_varifold-a1.exists_translate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1 and 2 of the parent-supplied proof (definition of V' and verification of its structure fields); the needed translation invariance of H^n (the parent's fact (I1)) is restated in step 0. Notation: M := V.carrier, theta := V.mult, H^n := muHE[n], tau(x) := x - xi, sigma(x) := x + xi (the inverse of tau).

0. Preliminary facts. (i) tau and sigma are isometric bijections of R^(n+l) (IsometryEquiv.subRight xi, IsometryEquiv.addRight xi) and measurable equivalences (MeasurableEquiv.subRight xi, MeasurableEquiv.addRight xi); in particular sigma is continuous and a measurable embedding. (ii) muHE[n] is preserved by isometric bijections, so sigma is measure preserving from H^n to H^n (IsometryEquiv.measurePreserving_euclideanHausdorffMeasure), hence quasi-measure-preserving, and H^n(tau(S)) = H^n(S) for every set S (Isometry.euclideanHausdorffMeasure_image, valid without measurability). (iii) For every set S, tau(S) = sigma^{-1}(S): if y = x - xi with x in S then y + xi = x is in S; conversely, if y + xi is in S then y = tau(y + xi) is in tau(S).

1. Definition. Let V' have carrier M' := tau(M) and multiplicity theta'(y) := theta(y + xi). Once the six structure fields are verified in steps 2-7, V' is a rectifiable n-varifold in tau(U), and the two required equalities V'.carrier = tau(M) and V'.mult y = theta(y + xi) (for all y) hold by definition.

2. carrier_subset: M is contained in U, hence tau(M) is contained in tau(U) (monotonicity of images).

3. nullMeasurableSet_carrier: by (iii), tau(M) = sigma^{-1}(M). The set M is H^n-null-measurable and sigma is quasi-measure-preserving from H^n to H^n by (ii), so sigma^{-1}(M) is H^n-null-measurable (NullMeasurableSet.preimage).

4. countablyRectifiable: by definition of countable n-rectifiability of M there are a set M0 with H^n(M0) = 0 and maps F_j : R^n -> R^(n+l) (j in N), each Lipschitz with some constant K_j, such that M is contained in M0 union (union over j of range F_j). Take M0' := tau(M0) and F'_j(z) := F_j(z) - xi. (a) H^n(tau(M0)) = H^n(M0) = 0 by (ii). (b) F'_j is K_j-Lipschitz, because dist(F_j(z) - xi, F_j(w) - xi) = dist(F_j(z), F_j(w)) <= K_j dist(z, w). (c) If y is in tau(M), then y = x - xi with x in M; either x is in M0, and then y is in tau(M0), or x = F_j(z) for some j and z, and then y = F'_j(z) is in range F'_j. Hence tau(M) is contained in M0' union (union over j of range F'_j), so tau(M) is countably n-rectifiable.

5. mult_pos: if y is in tau(M), then y = x - xi with x in M, and theta'(y) = theta(x - xi + xi) = theta(x) > 0 by positivity of theta on M.

6. aemeasurable_mult: theta' = theta o sigma and, by (iii), H^n restricted to tau(M) equals H^n restricted to sigma^{-1}(M). Since sigma is measure preserving for H^n and a measurable embedding, it is measure preserving from H^n restricted to sigma^{-1}(M) to H^n restricted to M (MeasurePreserving.restrict_preimage_emb), in particular quasi-measure-preserving. As theta is a.e.-measurable for H^n restricted to M, the composition theta o sigma is a.e.-measurable for H^n restricted to sigma^{-1}(M) (AEMeasurable.comp_quasiMeasurePreserving).

7. integrableOn_mult: let K be compact with K contained in tau(U). Then sigma(K) is compact (continuous image of a compact set), and sigma(K) is contained in U: if y is in K, then y = x - xi for some x in U and sigma(y) = x is in U. By the corresponding field of V, theta is H^n-integrable on M cap sigma(K). Moreover tau(M) cap K = sigma^{-1}(M) cap sigma^{-1}(sigma(K)) = sigma^{-1}(M cap sigma(K)), using (iii) and sigma^{-1}(sigma(K)) = K (sigma is injective). Because sigma is measure preserving and a measurable embedding, for every set S the function theta o sigma is H^n-integrable on sigma^{-1}(S) if and only if theta is H^n-integrable on S (MeasurePreserving.integrableOn_comp_preimage). Taking S = M cap sigma(K) shows that theta' = theta o sigma is H^n-integrable on tau(M) cap K.

8. Steps 2-7 verify every field of the structure, so V' is a rectifiable n-varifold in tau(U) with V'.carrier = tau(M) and V'.mult y = theta(y + xi) for every y, which is the assertion.

## Key steps

1. define V' with carrier tau(M) and multiplicity y -> theta(y + xi); both required equalities hold by definition
2. tau(S) = sigma^{-1}(S) for sigma(x) = x + xi, and tau, sigma are H^n-measure-preserving isometric measurable equivalences
3. null-measurability and a.e.-measurability of the new fields by pulling back along the measure-preserving embedding sigma
4. countable rectifiability: translate the null set and compose each Lipschitz parametrization with tau (same constant)
5. positivity, and integrability on tau(M) cap K via the compact set sigma(K) contained in U and MeasurePreserving.integrableOn_comp_preimage

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
