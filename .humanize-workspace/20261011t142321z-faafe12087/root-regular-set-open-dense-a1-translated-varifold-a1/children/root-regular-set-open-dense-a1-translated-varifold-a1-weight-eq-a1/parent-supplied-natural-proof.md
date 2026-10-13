# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.translated_varifold-a1`
- Child DAG node: `root.regular_set_open_dense-a1.translated_varifold-a1.weight_eq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation:
- M := V.carrier, θ := V.mult, Hⁿ := μHE[n];
- μ_V := V.weight = (Hⁿ⌞M).withDensity(ofReal ∘ θ) and μ_W := W.weight = (Hⁿ⌞W.carrier).withDensity(ofReal ∘ W.mult);
- τ(y) := y + x₀ and σ(y) := y − x₀.

Hypotheses: (hc) W.carrier = τ⁻¹M; (hm) W.mult y = θ(y + x₀) for all y. The sets U and U' play no role.

1. τ is Hⁿ-measure-preserving: IsometryEquiv.measurePreserving_euclideanHausdorffMeasure (IsometryEquiv.addRight x₀) n. It is also a measurable embedding: (MeasurableEquiv.addRight x₀).measurableEmbedding. σ is measurable (measurable_sub_const x₀).

2. Two measures that agree on measurable sets are equal (Measure.ext). So it suffices to prove μ_W(A) = (map σ μ_V)(A) for every measurable A. Fix such an A; then σ⁻¹A is also measurable.

3. (map σ μ_V)(A) = μ_V(σ⁻¹A), by Measure.map_apply with σ measurable and A measurable.

4. By withDensity_apply (A and σ⁻¹A are measurable) and Measure.restrict_restrict:
- μ_W(A) = ∫⁻_{A ∩ W.carrier} ofReal(W.mult y) dHⁿ(y);
- μ_V(σ⁻¹A) = ∫⁻_{σ⁻¹A ∩ M} ofReal(θ x) dHⁿ(x).

5. Two identities:
- By (hc) and (y + x₀) − x₀ = y, τ⁻¹(σ⁻¹A ∩ M) = {y : (y + x₀) − x₀ ∈ A and y + x₀ ∈ M} = A ∩ τ⁻¹M = A ∩ W.carrier (ext; simp [hc]).
- By (hm), the functions y ↦ ofReal(W.mult y) and y ↦ ofReal(θ(y + x₀)) are equal (funext).

6. Change of variables for the measure-preserving measurable embedding τ (MeasurePreserving.setLIntegral_comp_preimage_emb hτ hτe): for every g : ℝ^{n+ℓ} → [0, ∞] and every set s, ∫⁻_{τ⁻¹s} g(τ y) dHⁿ(y) = ∫⁻_s g dHⁿ. Take s := σ⁻¹A ∩ M and g := ofReal ∘ θ. Then by steps 4 and 5:
 μ_W(A) = ∫⁻_{τ⁻¹s} ofReal(θ(τ y)) dHⁿ(y) = ∫⁻_s ofReal(θ) dHⁿ = μ_V(σ⁻¹A) = (map σ μ_V)(A).

7. Hence W.weight = V.weight.map (fun y => y − x₀).

## Key steps

1. τ = (· + x₀) preserves Hⁿ and is a measurable embedding; σ = (· − x₀) is measurable
2. Reduce to measurable sets A by Measure.ext, and use (map σ μ_V)(A) = μ_V(σ⁻¹A)
3. Unfold both withDensity weights into set lintegrals over A ∩ W.carrier and σ⁻¹A ∩ M
4. τ⁻¹(σ⁻¹A ∩ M) = A ∩ W.carrier, and W.mult = θ ∘ τ
5. Apply MeasurePreserving.setLIntegral_comp_preimage_emb to conclude μ_W(A) = (map σ μ_V)(A)

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
