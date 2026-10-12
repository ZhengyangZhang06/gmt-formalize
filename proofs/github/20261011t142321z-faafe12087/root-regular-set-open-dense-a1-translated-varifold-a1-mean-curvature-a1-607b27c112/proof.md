# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.translated_varifold-a1`
- Child DAG node: `root.regular_set_open_dense-a1.translated_varifold-a1.mean_curvature-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: μ := V.weight, τ(y) := y + x₀, and σ := MeasurableEquiv.subRight x₀, whose coercion is definitionally y ↦ y − x₀.
Hypotheses:
- (hw) W.weight = map σ μ;
- (hT) W.tangentProj y = V.tangentProj (y + x₀) for all y.
Let H satisfy V.HasGeneralizedMeanCurvature H, which means:
- (A) LocallyIntegrableOn H U μ;
- (B) ∫ V.divM Y dμ = −∫ ⟨Y, H⟩ dμ for every Y that is C¹, has compact support and has tsupport Y ⊆ U.
Put H'(y) := H(y + x₀). We prove both clauses of W.HasGeneralizedMeanCurvature H', whose domain is τ⁻¹U.

1. Change-of-variables facts for σ:
- (i) ∫ F d(map σ μ) = ∫ F(x − x₀) dμ(x) for every F (integral_map_equiv). This holds for all F because σ is a measurable equivalence.
- (ii) IntegrableOn f S (map σ μ) ↔ IntegrableOn (f ∘ σ) (σ⁻¹S) μ for every f and set S (integrableOn_map_equiv).

2. Local integrability.
- Let y ∈ τ⁻¹U, so y + x₀ ∈ U.
- LocallyIntegrableOn H U μ means ∀ x ∈ U, ∃ G ∈ 𝓝[U] x, IntegrableOn H G μ. By (A) at y + x₀, pick G ∈ 𝓝[U](y + x₀) with IntegrableOn H G μ.
- Take G' := τ⁻¹G.
- (a) G' ∈ 𝓝[τ⁻¹U] y: τ is continuous and maps τ⁻¹U into U (mapsTo_preimage). So it tends from 𝓝[τ⁻¹U] y to 𝓝[U] τ(y) (ContinuousWithinAt.tendsto_nhdsWithin), and G belongs to the latter filter.
- (b) Rewrite W.weight by (hw). By 1(ii), integrability of H' on G' for map σ μ is equivalent to integrability of H' ∘ σ on σ⁻¹G' for μ. But σ⁻¹G' = {z : (z − x₀) + x₀ ∈ G} = G and (H' ∘ σ)(z) = H((z − x₀) + x₀) = H(z), so this is exactly IntegrableOn H G μ.
- Hence LocallyIntegrableOn H' (τ⁻¹U) W.weight.

3. The translated test field.
Let X be C¹ with compact support and tsupport X ⊆ τ⁻¹U, and define X̃(x) := X(x − x₀).
- (a) X̃ is C¹: ContDiff.comp of X with contDiff_id.sub contDiff_const.
- (b) X̃ has compact support: X̃ = X ∘ e for the homeomorphism e := (IsometryEquiv.subRight x₀).toHomeomorph, so HasCompactSupport.comp_homeomorph applies.
- (c) tsupport X̃ ⊆ U: by tsupport_comp_subset_preimage (z ↦ z − x₀ is continuous), x ∈ tsupport X̃ implies x − x₀ ∈ tsupport X ⊆ τ⁻¹U, i.e. (x − x₀) + x₀ = x ∈ U.
- (d) Applying (B) to Y := X̃ gives ∫ V.divM X̃ dμ = −∫ ⟨X̃(x), H(x)⟩ dμ(x).

4. Divergence identity. For every x:
- W.divM X (x − x₀) = trace(DX(x − x₀) ∘ W.tangentProj(x − x₀)) = trace(DX(x − x₀) ∘ V.tangentProj x), by (hT) and (x − x₀) + x₀ = x;
- DX̃(x) = DX(x − x₀) (fderiv_comp_sub);
- hence W.divM X (x − x₀) = V.divM X̃ x.
- In Lean: simp only [RectifiableVarifold.divM, hT, sub_add_cancel]; rw [fderiv_comp_sub].

5. The first-variation identity.
- By (hw) and 1(i): ∫ W.divM X dW.weight = ∫ W.divM X (x − x₀) dμ(x) = ∫ V.divM X̃ dμ, using step 4.
- Likewise ∫ ⟨X, H'⟩ dW.weight = ∫ ⟨X(x − x₀), H((x − x₀) + x₀)⟩ dμ(x) = ∫ ⟨X̃(x), H(x)⟩ dμ(x).
- By step 3(d), ∫ W.divM X dW.weight = −∫ ⟨X, H'⟩ dW.weight.

6. Steps 2 and 5 are the two clauses of W.HasGeneralizedMeanCurvature (fun y => H (y + x₀)).

## Key steps

1. Change of variables along the measurable equivalence σ = (· − x₀): integral_map_equiv and integrableOn_map_equiv
2. Local integrability: transport the neighbourhoods G ∈ 𝓝[U](y + x₀) to τ⁻¹G ∈ 𝓝[τ⁻¹U] y, with H' ∘ σ = H and σ⁻¹(τ⁻¹G) = G
3. The translated test field X̃ = X(· − x₀) is C¹, compactly supported, with tsupport X̃ ⊆ U
4. W.divM X (x − x₀) = V.divM X̃ x from the tangentProj identity and fderiv_comp_sub
5. Change variables in both sides of the first variation and apply V's identity to X̃

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
