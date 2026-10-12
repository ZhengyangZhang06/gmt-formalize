# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.translate_varifold-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.translate_varifold-a1.tangent_proj_eq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: first half of Step 5 of the parent-supplied proof. Notation: M := V.carrier, theta := V.mult, H^n := muHE[n], eta_{a,r}(z) := blowUpMap a r z = r^{-1} • (z - a) (scalar multiplication •), and HasW(N, w, a, P) := Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n N w a P, which by definition means: finrank P = n, and for every f in C_c(R^(n+l), R) the function r -> integral over eta_{a,r}(N) of f(z) * w(a + r • z) dH^n(z) tends to w(a) * (integral over P of f dH^n) as r -> 0+. Fix y in R^(n+l).

1. The blow-up sets agree: for every r, eta_{y,r}(V'.carrier) = eta_{y+xi,r}(M). Indeed V'.carrier = tau(M), so eta_{y,r}(tau(M)) is the image of M under eta_{y,r} o tau (Set.image_image), and for every x, eta_{y,r}(tau(x)) = r^{-1} • ((x - xi) - y) = r^{-1} • (x - (y + xi)) = eta_{y+xi,r}(x), by the abelian-group identity (x - xi) - y = x - (y + xi).

2. The weights agree: for every r and z, V'.mult(y + r • z) = theta(y + r • z + xi) = theta((y + xi) + r • z) (add_right_comm), and V'.mult(y) = theta(y + xi).

3. Hence for every linear subspace P: HasW(V'.carrier, V'.mult, y, P) holds if and only if HasW(M, theta, y + xi, P) holds. After unfolding the definition, rewriting the integration domains by step 1 and every value of the multiplicity (inside the integrals and in the limit value) by step 2 turns the left-hand proposition literally into the right-hand one; the dimension condition finrank P = n is the same on both sides.

4. Put A(P) := HasW(V'.carrier, V'.mult, y, P) and B(P) := HasW(M, theta, y + xi, P). By step 3 and function and propositional extensionality, A = B as predicates on subspaces. By definition, with the classical decidability instance, V'.tangentProj y = (if h : exists P, A P then (Classical.choose h).starProjection else 0) and V.tangentProj (y + xi) = (if h : exists P, B P then (Classical.choose h).starProjection else 0). The expression (if h : exists P, C P then (Classical.choose h).starProjection else 0) depends only on the predicate C, so substituting A = B shows the two expressions are equal. Hence V'.tangentProj y = V.tangentProj (y + xi); since y was arbitrary, this holds for every y.

## Key steps

1. blowUpMap y r '' tau(M) = blowUpMap (y + xi) r '' M because (x - xi) - y = x - (y + xi)
2. V'.mult(y + r • z) = theta((y + xi) + r • z) and V'.mult y = theta(y + xi)
3. the weighted approximate tangent predicates of V' at y and of V at y + xi coincide for every subspace P
4. equal predicates give equal dependent if-then-else with Classical.choose, so the tangent projections agree

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
