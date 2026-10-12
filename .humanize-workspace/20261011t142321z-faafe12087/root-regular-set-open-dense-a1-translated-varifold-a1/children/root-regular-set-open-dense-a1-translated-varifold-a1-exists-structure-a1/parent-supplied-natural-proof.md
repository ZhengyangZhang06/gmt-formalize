# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.translated_varifold-a1`
- Child DAG node: `root.regular_set_open_dense-a1.translated_varifold-a1.exists_structure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: M := V.carrier, θ := V.mult, Hⁿ := μHE[n] on ℝ^{n+ℓ} = Amb n ℓ, and τ(y) := y + x₀.

1. Properties of τ.
- τ is the isometric bijection IsometryEquiv.addRight x₀, whose coercion is definitionally y ↦ y + x₀. By IsometryEquiv.measurePreserving_euclideanHausdorffMeasure it is measure preserving: hτ : MeasurePreserving τ Hⁿ Hⁿ.
- τ is a measurable embedding, being the measurable equivalence MeasurableEquiv.addRight x₀: hτe := (MeasurableEquiv.addRight x₀).measurableEmbedding.
- τ is continuous (continuous_add_const x₀) and injective.
- Consequences: (i) Hⁿ(τ⁻¹A) = Hⁿ(A) for every set A (MeasurePreserving.measure_preimage_emb hτ hτe); (ii) map τ Hⁿ = Hⁿ (hτ.map_eq).

2. Definition of W.
- Let W be the structure with carrier := τ⁻¹M = {y : y + x₀ ∈ M} and mult := y ↦ θ(y + x₀).
- Then W.carrier = τ⁻¹M, and W.mult y = θ(y + x₀) for all y, both by definition (rfl).
- Steps 3-8 verify the remaining fields for the domain τ⁻¹U.

3. carrier_subset. M ⊆ U (V.carrier_subset), so τ⁻¹M ⊆ τ⁻¹U (preimage_mono).

4. nullMeasurableSet_carrier.
- M is Hⁿ-null-measurable (V.nullMeasurableSet_carrier).
- A measure-preserving map is quasi-measure-preserving.
- The preimage of a null-measurable set under a quasi-measure-preserving map is null-measurable (NullMeasurableSet.preimage with hτ.quasiMeasurePreserving).
- So τ⁻¹M is Hⁿ-null-measurable.

5. countablyRectifiable.
- V.countablyRectifiable provides M₀ with Hⁿ(M₀) = 0 and F : ℕ → ℝⁿ → ℝ^{n+ℓ} such that each F_j is K_j-Lipschitz for some K_j ∈ ℝ≥0 and M ⊆ M₀ ∪ ⋃_j range F_j.
- Put M₀' := τ⁻¹M₀ and F'_j(z) := F_j(z) − x₀.
- (a) Hⁿ(M₀') = Hⁿ(M₀) = 0 by 1(i).
- (b) F'_j is (K_j + 0)-Lipschitz, as the difference of the K_j-Lipschitz map F_j and the 0-Lipschitz constant map x₀ (LipschitzWith.sub with LipschitzWith.const x₀).
- (c) Let y ∈ τ⁻¹M, so y + x₀ ∈ M. If y + x₀ ∈ M₀, then y ∈ M₀'. Otherwise y + x₀ = F_j(z) for some j and z, so y = F_j(z) − x₀ = F'_j(z) ∈ range F'_j.
- Hence τ⁻¹M ⊆ M₀' ∪ ⋃_j range F'_j, which witnesses CountablyRectifiable n (τ⁻¹M).

6. mult_pos. If y ∈ τ⁻¹M, then y + x₀ ∈ M, so W.mult y = θ(y + x₀) > 0 by V.mult_pos.

7. aemeasurable_mult.
- Let ν := Hⁿ⌞τ⁻¹M.
- τ is a measurable embedding, so (map τ Hⁿ)⌞M = map τ (Hⁿ⌞τ⁻¹M) (MeasurableEmbedding.restrict_map).
- Together with map τ Hⁿ = Hⁿ, this gives map τ ν = Hⁿ⌞M.
- By V.aemeasurable_mult, θ is AEMeasurable for Hⁿ⌞M = map τ ν.
- Composing with the measurable map τ (AEMeasurable.comp_measurable with measurable_add_const x₀) shows that y ↦ θ(y + x₀) is AEMeasurable for ν.

8. integrableOn_mult.
- Let K be compact with K ⊆ τ⁻¹U.
- τ(K) = {k + x₀ : k ∈ K} is compact (IsCompact.image of the continuous τ).
- τ(K) ⊆ U, because k ∈ K implies k + x₀ ∈ U.
- By V.integrableOn_mult, θ is Hⁿ-integrable on M ∩ τ(K).
- Since τ is injective, τ⁻¹(M ∩ τ(K)) = τ⁻¹M ∩ τ⁻¹(τ(K)) = τ⁻¹M ∩ K (preimage_inter and Function.Injective.preimage_image).
- By MeasurePreserving.integrableOn_comp_preimage (with hτ and hτe), IntegrableOn (θ ∘ τ) (τ⁻¹s) Hⁿ ↔ IntegrableOn θ s Hⁿ for s := M ∩ τ(K).
- Hence W.mult = θ ∘ τ is Hⁿ-integrable on τ⁻¹M ∩ K = W.carrier ∩ K.
- In Lean: expose the composition with `show IntegrableOn (V.mult ∘ fun y => y + x₀) ((fun y => y + x₀) ⁻¹' V.carrier ∩ K) μHE[n]`, rewrite with the preimage identity, then apply the iff.

9. Steps 2-8 construct W : RectifiableVarifold n ℓ (τ⁻¹U) with W.carrier = τ⁻¹M and W.mult y = θ(y + x₀) for all y, which is the claim.

## Key steps

1. τ(y) = y + x₀ is an Hⁿ-measure-preserving, injective, continuous measurable embedding (isometry invariance of μHE[n])
2. Define W with carrier τ⁻¹M and multiplicity θ∘τ; the carrier and multiplicity equations hold by rfl
3. carrier ⊆ τ⁻¹U by preimage_mono; null-measurability by NullMeasurableSet.preimage
4. Countable rectifiability from τ⁻¹M₀ and the Lipschitz maps F_j − x₀
5. Positivity; a.e.-measurability from map τ (Hⁿ⌞τ⁻¹M) = Hⁿ⌞M
6. Local integrability on compact K from τ(K) compact ⊆ U, τ⁻¹(M ∩ τK) = τ⁻¹M ∩ K and integrableOn_comp_preimage

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
