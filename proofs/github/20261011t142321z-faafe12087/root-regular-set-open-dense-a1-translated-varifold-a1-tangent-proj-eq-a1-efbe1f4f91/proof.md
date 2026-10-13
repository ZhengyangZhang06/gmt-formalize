# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.translated_varifold-a1`
- Child DAG node: `root.regular_set_open_dense-a1.translated_varifold-a1.tangent_proj_eq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: M := V.carrier, θ := V.mult, τ(y) := y + x₀, and blowUpMap x r z := r⁻¹ • (z − x) (Poincare.SimonGMT.Chapter03.blowUpMap).
Hypotheses: (hc) W.carrier = τ⁻¹M; (hm) W.mult y = θ(y + x₀) for all y.
Fix y.

Definitions recalled:
- HasWeightedApproximateTangentSpaceAt n S φ x P means: finrank P = n, and for every f ∈ C_c(ℝ^{n+ℓ}, ℝ), r ↦ ∫_{blowUpMap x r '' S} f(w) φ(x + r•w) dHⁿ(w) tends to φ(x) ∫_P f dHⁿ as r → 0⁺.
- tangentProj at x is, with classical decidability, `if h : ∃ P, HasWeightedApproximateTangentSpaceAt n carrier mult x P then (Classical.choose h).starProjection else 0`.

1. The blow-up sets agree: for every r, blowUpMap y r '' W.carrier = blowUpMap (y + x₀) r '' M.
- By (hc), W.carrier = τ⁻¹M.
- If z ∈ τ⁻¹M, put m := z + x₀ ∈ M. Then r⁻¹•(z − y) = r⁻¹•(m − (y + x₀)), since z − y = (z + x₀) − (y + x₀).
- Conversely, if m ∈ M, put z := m − x₀. Then z + x₀ = m ∈ M, so z ∈ τ⁻¹M, and r⁻¹•(m − (y + x₀)) = r⁻¹•(z − y).
- In Lean: rw [hc]; ext w; rintro the image witnesses; prove the vector identities by `congr 1; abel`.

2. The multiplicities agree.
- By (hm), W.mult = (z ↦ θ(z + x₀)) (funext).
- Hence W.mult(y + r•w) = θ(y + r•w + x₀) = θ((y + x₀) + r•w) (add_right_comm), and W.mult(y) = θ(y + x₀).

3. Let Pred_W := HasWeightedApproximateTangentSpaceAt n W.carrier W.mult y and Pred_V := HasWeightedApproximateTangentSpaceAt n M θ (y + x₀), both predicates on subspaces P.
- Unfold both and rewrite with steps 1-2. The finrank clauses are identical, and so are the integration domains, the integrands and the limits.
- So Pred_W P and Pred_V P are the same proposition for every P, and hpred : Pred_W = Pred_V (funext P; simp only [HasWeightedApproximateTangentSpaceAt, step 1, step 2]; simp only [add_right_comm y _ x₀]).

4. Choice congruence. For predicates p, q on subspaces with p = q and proofs hp : ∃ P, p P and hq : ∃ P, q P, Classical.choose hp = Classical.choose hq. Proof: substitute q := p; both sides are then the same term.

5. Unfold tangentProj and split cases on E := ∃ P, Pred_V P.
(a) Suppose E holds.
- Then ∃ P, Pred_W P also holds (rewrite with hpred).
- Both conditionals take their first branch (dite_eq_left), so the goal becomes (Classical.choose h_W).starProjection = (Classical.choose h_V).starProjection.
- `congr 1` reduces this to equality of the chosen subspaces. The HasOrthogonalProjection instance argument is a proposition, so proof irrelevance handles it.
- Step 4 with hpred closes the goal.
(b) Suppose E fails.
- By hpred, no P satisfies Pred_W either.
- Both conditionals take their second branch (dite_eq_right), and both sides equal 0.
Lean caution: `rw [hpred]` directly inside the dependent if-then-else fails ('motive is not type correct'). Classical.choose and the auxiliary instance proof in tangentProj both depend on the condition. The case split above avoids this.

6. Hence W.tangentProj y = V.tangentProj (y + x₀) for every y.

## Key steps

1. Blow-up sets agree: blowUpMap y r '' τ⁻¹M = blowUpMap (y + x₀) r '' M via m = z + x₀
2. Multiplicities agree: W.mult(y + r•w) = θ((y + x₀) + r•w) and W.mult y = θ(y + x₀)
3. Hence the weighted approximate-tangent predicates of W at y and of V at y + x₀ are equal as functions of P
4. Case split on existence; use dite_eq_left/dite_eq_right, Classical.choose congruence and congr 1 for the starProjection

## Reference use

### local-project

Queries:
- `rg -n '^theorem (IsometryEquiv.measurePreserving_euclideanHausdorffMeasure)' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem (setLIntegral_comp_preimage_emb|lintegral_map_equiv)\b' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `rg -n 'theorem (integrableOn_map_equiv|MeasurePreserving.integrableOn_comp_preimage)\b' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `rg -n 'theorem _root_.MeasureTheory.NullMeasurableSet.preimage' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean`
- `rg -n 'theorem measure_preimage_emb' <snapshot>/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `rg -n 'theorem (restrict_map|map_apply)\b' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n '^theorem integral_map_equiv' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `rg -n '^theorem fderiv_comp_sub\b' <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `rg -n 'HasCompactMulSupport.comp_homeomorph|lemma mulTSupport_comp_subset_preimage' <snapshot>/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `rg -n 'def (divRight|mulRight)\b' <snapshot>/mathlib/Mathlib/MeasureTheory/Group/MeasurableEquiv.lean <snapshot>/mathlib/Mathlib/Topology/MetricSpace/IsometricSMul.lean`
- `rg -n '^lemma mem_support_iff_forall' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n 'support_map' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean (no match)`
- `rg -n 'theorem ContinuousWithinAt.tendsto_nhdsWithin \{' <snapshot>/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `rg -n 'class HasOrthogonalProjection' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n -i 'translat|addRight|subRight|vadd' <snapshot>/project/GMT/Ch05 (no match)`
- `rg -n 'noncomputable def tangentProj|open Classical in|def divM|def support|def weight|def LocallyLp|def HasGeneralizedMeanCurvature' <snapshot>/project/GMT/Ch05/Submission.lean`
- `diff -q <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean (identical)`
- `rg -n 'noncomputable def blowUpMap|^def HasWeightedApproximateTangentSpaceAt|^def CountablyRectifiable' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n -i 'translat|addRight|subRight' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03 .lake/packages/simongmt/Poincare/SimonGMT/Chapter04 (no match)`
- `rg -ln 'rsod_tv_' .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087 <snapshot>/project (no match; name-collision check)`
- `python3: DAG dag.json lean_name listing (other translation nodes dohr_translate_varifold, exists_translated_varifold_allardHypotheses use image-form domains, not identical types)`
- `python3: gmt-compare.py contract_scope(Contract.lean, GMT.Ch05.main_theorem) and lean_contract.validate_lean_statement on all child types`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/rsod-tv-check/build lean /tmp/rsod-tv-check/src/All2.lean (6 full child proofs, parent assembly, comparator-shaped targets, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/MeasurableEquiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/IsometricSMul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/rsod-tv-check/src/All2.lean`

The snapshot is pinned at project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The snapshot's project/GMT/Ch05/Submission.lean is byte-identical to the worktree's.

No-match results:
- The project has no translation lemmas for RectifiableVarifold (rg for translat/addRight/subRight/vadd in project/GMT/Ch05).
- simongmt Chapter03 and Chapter04 have none either.
- Mathlib's Measure/Support.lean has no support_map lemma, so the support child proves the identity directly with mem_support_iff_forall (Support.lean:75) and MeasurableEquiv.map_apply.
- No rsod_tv_ name exists in the run, so there are no collisions.
- The other translation nodes (dohr_translate_varifold, exists_translated_varifold_allardHypotheses) have different, image-form types and are not reusable verbatim.

Usable Mathlib items (in the snapshot):
- IsometryEquiv.measurePreserving_euclideanHausdorffMeasure (Geometry/Euclidean/Volume/Measure.lean:127), with IsometryEquiv.addRight/subRight (IsometricSMul.lean:157,167).
- MeasurableEquiv.addRight/subRight (MeasurableEquiv.lean:117,193), measurable_sub_const and measurable_add_const.
- MeasurePreserving.measure_preimage_emb (MeasurePreserving.lean:151) and NullMeasurableSet.preimage (QuasiMeasurePreserving.lean:134).
- MeasureTheory.MeasurePreserving.setLIntegral_comp_preimage_emb and lintegral_map_equiv (Lebesgue/Map.lean:130,94).
- integrableOn_map_equiv and MeasurePreserving.integrableOn_comp_preimage (IntegrableOn.lean:315,319).
- MeasurableEmbedding.restrict_map and MeasurableEquiv.restrict_map (Restrict.lean:890), and Measure.restrict_restrict.
- withDensity_apply and integral_map_equiv (Bochner/Basic.lean:1105).
- fderiv_comp_sub (FDeriv/Add.lean:892).
- HasCompactSupport.comp_homeomorph and tsupport_comp_subset_preimage (Topology/Algebra/Support.lean:562,99).
- ContinuousWithinAt.tendsto_nhdsWithin (ContinuousOn.lean:59).
- LipschitzWith.sub.
- Core dite_eq_left and dite_eq_right.
- HasOrthogonalProjection is a Prop class (Projection/Basic.lean:48), so `congr 1` closes the instance argument.

simongmt (pinned under .lake/packages, outside the snapshot): Chapter03/Rectifiable.lean gives CountablyRectifiable (line 34), blowUpMap (96) and HasWeightedApproximateTangentSpaceAt (330), and the tangent child relies on these definitions.

Lean check (/tmp/rsod-tv-check/src/All2.lean, compiled against a scratch build of GMT.Ch05.Submission with Lean v4.35.0-rc3):
- All six children are fully proved.
- The frozen parent type is assembled from them.
- Comparator-shaped targets compile for all six children and the parent.
- The only axioms are propext, Classical.choice and Quot.sound.
- All types pass validate_lean_statement.

Pitfall found: rewriting the predicate equality inside the dependent if-then-else of tangentProj fails with 'motive is not type correct'. The fix is a case split with dite_eq_left/dite_eq_right, a Classical.choose congruence and `congr 1`.
