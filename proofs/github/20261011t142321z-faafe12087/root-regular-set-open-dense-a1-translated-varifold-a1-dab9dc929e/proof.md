# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1`
- Child DAG node: `root.regular_set_open_dense-a1.translated_varifold-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the translation invariance used in step 6 of the parent proof (5.2 is applied to V~ translated by -x₀). Let n, ℓ ∈ ℕ, U ⊆ ℝ^{n+ℓ} (arbitrary), V : RectifiableVarifold n ℓ U with M := V.carrier, θ := V.mult, Hⁿ := μHE[n], μ := V.weight, and x₀ ∈ ℝ^{n+ℓ}. Let τ(y) := y + x₀ and σ(y) := y - x₀ = τ⁻¹(y). Both are isometric bijections and measurable equivalences (MeasurableEquiv.addRight / subRight); by IsometryEquiv.measurePreserving_euclideanHausdorffMeasure they preserve Hⁿ: Hⁿ(τ⁻¹A) = Hⁿ(A) = Hⁿ(σ⁻¹A) for every A, map τ Hⁿ = Hⁿ = map σ Hⁿ.
1. Construction. Define W : RectifiableVarifold n ℓ (τ⁻¹(U)) with carrier τ⁻¹(M) = {y : y + x₀ ∈ M} and mult y ↦ θ(y + x₀). Fields: (a) τ⁻¹(M) ⊆ τ⁻¹(U) since M ⊆ U. (b) τ⁻¹(M) is Hⁿ-null-measurable: preimage of the null-measurable set M under the measure-preserving map τ (NullMeasurableSet.preimage). (c) Countable rectifiability: CountablyRectifiable n M gives M₀ with Hⁿ(M₀) = 0 and Lipschitz F_j : ℝⁿ → ℝ^{n+ℓ} with M ⊆ M₀ ∪ ⋃_j range F_j. Then τ⁻¹(M) ⊆ τ⁻¹(M₀) ∪ ⋃_j range(F_j(·) - x₀): if y + x₀ ∈ M₀ then y ∈ τ⁻¹M₀, and if y + x₀ = F_j(z) then y = F_j(z) - x₀. Here Hⁿ(τ⁻¹M₀) = Hⁿ(M₀) = 0 and z ↦ F_j(z) - x₀ is Lipschitz with the same constant. (d) For y ∈ τ⁻¹(M), θ(y + x₀) > 0. (e) map τ (Hⁿ⌞τ⁻¹(M)) = (map τ Hⁿ)⌞M = Hⁿ⌞M (MeasurableEquiv.restrict_map), so θ ∘ τ is AEMeasurable for Hⁿ⌞τ⁻¹(M) (compose the AEMeasurable θ with the measurable τ). (f) If K ⊆ τ⁻¹(U) is compact, then τ(K) = K + x₀ is compact, τ(K) ⊆ U, and τ⁻¹(M) ∩ K = τ⁻¹(M ∩ τ(K)); θ is integrable on M ∩ τ(K), so θ ∘ τ is integrable on τ⁻¹(M ∩ τ(K)) by measure preservation (MeasurePreserving.integrableOn_comp_preimage). By construction W.carrier = τ⁻¹(M) and W.mult y = θ(y + x₀).
2. Weight. For measurable A, by the change of variables along τ (MeasurableEquiv.restrict_map, lintegral_map_equiv): W.weight(A) = ∫⁻_{A ∩ τ⁻¹M} ofReal(θ(τ y)) dHⁿ(y) = ∫⁻_{τ(A) ∩ M} ofReal(θ) dHⁿ = μ(τ(A)) = μ(σ⁻¹(A)) = (map σ μ)(A). Hence W.weight = V.weight.map (fun y => y - x₀). Since σ is a measurable equivalence, (map σ μ)(G) = μ(σ⁻¹G) holds for every set G (MeasurableEquiv.map_apply).
3. Support. For y ∈ ℝ^{n+ℓ}: y ∈ spt(map σ μ) ⟺ ∀ G ∈ 𝓝 y, μ(σ⁻¹G) > 0 ⟺ ∀ G' ∈ 𝓝(y + x₀), μ(G') > 0 ⟺ y + x₀ ∈ spt μ, because σ is a homeomorphism with σ(y + x₀) = y, so G ↦ σ⁻¹(G) is a bijection from the neighbourhoods of y onto those of y + x₀ (Measure.mem_support_iff_forall). Thus spt(W.weight) = τ⁻¹(spt μ) and W.support = τ⁻¹(U) ∩ τ⁻¹(spt μ) = τ⁻¹(U ∩ spt μ) = τ⁻¹(V.support).
4. Tangent planes. For every y and every subspace P the propositions HasWeightedApproximateTangentSpaceAt n (τ⁻¹M) (θ∘τ) y P and HasWeightedApproximateTangentSpaceAt n M θ (y + x₀) P are equal: blowUpMap y r '' τ⁻¹(M) = {r⁻¹(z - y) : z + x₀ ∈ M} = {r⁻¹(m - (y + x₀)) : m ∈ M} = blowUpMap (y + x₀) r '' M (substitute m = z + x₀); (θ∘τ)(y + r•w) = θ((y + x₀) + r•w) (add_right_comm); and (θ∘τ)(y) = θ(y + x₀). Hence the dependent if-then-else defining tangentProj gives W.tangentProj y = V.tangentProj (y + x₀) for every y.
5. Generalized mean curvature. Assume V.HasGeneralizedMeanCurvature H and put H'(y) := H(y + x₀). (a) LocallyIntegrableOn H' (τ⁻¹U) W.weight: for y ∈ τ⁻¹U, y + x₀ ∈ U and by hypothesis some G ∈ 𝓝[U](y + x₀) has H integrable on G for μ. Then G' := τ⁻¹(G) ∈ 𝓝[τ⁻¹U] y (τ is a homeomorphism carrying τ⁻¹U onto U), and integrability of H' on G' for map σ μ is equivalent, via the measurable equivalence σ (MeasurableEmbedding.integrableOn_map_iff), to integrability of H' ∘ σ = H on σ⁻¹(G') = G for μ. (b) Let X be C¹ with compact support and tsupport X ⊆ τ⁻¹(U). Put X̃(x) := X(x - x₀); X̃ is C¹ with compact support, tsupport X̃ = τ(tsupport X) ⊆ U, and fderiv X̃ x = fderiv X (x - x₀). Using ∫ F d(map σ μ) = ∫ F(x - x₀) dμ(x) for every F (MeasurableEquiv.integral_map) and step 4 (W.tangentProj(x - x₀) = V.tangentProj x): ∫ W.divM X dW.weight = ∫ trace(DX(x - x₀) ∘ W.tangentProj(x - x₀)) dμ(x) = ∫ trace(DX̃(x) ∘ V.tangentProj x) dμ(x) = ∫ V.divM X̃ dμ = -∫ ⟨X̃(x), H(x)⟩ dμ(x) = -∫ ⟨X(x - x₀), H'(x - x₀)⟩ dμ(x) = -∫ ⟨X, H'⟩ dW.weight. Hence W.HasGeneralizedMeanCurvature H'.
6. LocallyLp. Assume V.LocallyLp H p and let K ⊆ τ⁻¹(U) be compact. Then σ⁻¹(K) = τ(K) is compact and contained in U, and ∫⁻_K ‖H'‖ₑ^p d(map σ μ) = ∫⁻_{σ⁻¹K} ‖H'(σ x)‖ₑ^p dμ(x) = ∫⁻_{τ(K)} ‖H‖ₑ^p dμ < ∞ (set lintegral for a pushforward by a measurable equivalence). So W.LocallyLp H' p.
7. Steps 1-6 prove all conjuncts.

## Key steps

1. Translation τ(y) = y + x₀ is a measurable equivalence preserving Hⁿ
2. Build W on τ⁻¹U with carrier τ⁻¹M and multiplicity θ∘τ; check the structure fields
3. W.weight = map (· - x₀) μ by change of variables
4. Supports correspond under the homeomorphism: W.support = τ⁻¹(spt V)
5. Blow-ups of τ⁻¹M at y equal blow-ups of M at y + x₀, so tangent planes translate
6. First variation, local integrability and LocallyLp transfer by change of variables

## Reference use

### local-project

Queries:
- `rg -l 'rsod_|regularSet|IsC1Submanifold' <snapshot>/project`
- `rg -n '^lemma (isClosed_support|mem_support_iff_forall|notMem_support_iff_exists|support_mem_ae|measure_compl_support|interior_inter_support|support_restrict_subset)' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n '^theorem (IsometryEquiv.measurePreserving_euclideanHausdorffMeasure|MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀|Isometry.euclideanHausdorffMeasure_image)' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -l -e '[Vv]arifold' -e 'ApproximateTangent' -e 'approximate tangent' -e 'Whitney' -e 'rectifiable' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem ae_tendsto_rnDeriv ' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n 'subRight' <snapshot>/mathlib/Mathlib/MeasureTheory/Group/MeasurableEquiv.lean; rg -n 'theorem ae_map_iff \{p' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean; rg -n '^theorem ae_smul_measure ' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Module.lean; rg -n 'protected theorem Tendsto.const_mul' <snapshot>/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `sed -n 1,558p .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, blowUpMap, HasWeightedApproximateTangentSpaceAt, .unique)`
- `rg -n -i 'whitney|c1_approx|C1Approx|approximation theorem|upper density|theorem_1_5' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n '^theorem' .lake/packages/simongmt/Poincare/SimonGMT/{Chapter01/DensityComparison.lean,Chapter01/HausdorffDensityBounds.lean,Chapter01/Lusin.lean,Chapter02/AreaCritical.lean,Chapter02/WhitneyExtension.lean,Chapter04/TangentDensity.lean}`
- `grep -rl rsod_ .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087 (name-collision check)`
- `lake env lean /tmp/rsod-check/RsodCheck/All.lean (12 child statements, comparator targets, parent assembly, glue and leaf proofs)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/MeasurableEquiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Manifold/WhitneyEmbedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/rsod-check/RsodCheck/All.lean`

The snapshot is pinned at project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json).

No prior proofs exist. regularSet and IsC1Submanifold occur only in project/GMT/Ch05/{Contract,Submission}.lean and README.md. No rsod_ name occurs anywhere in the run, so there are no name collisions.

No-match results:
- Mathlib has no varifold, rectifiable-set, approximate-tangent or Whitney C¹-extension material. The only hits are Geometry/Manifold/WhitneyEmbedding.lean and PartitionOfUnity.lean (the Whitney embedding theorem for manifolds) and a comment in CategoryTheory/Monoidal/Rigid/Braided.lean.
- The pinned simongmt package lies outside the snapshot, under .lake/packages. It proves uniqueness of weighted approximate tangent planes (Chapter03/Rectifiable.lean, whose definition matches Def 1.7 literally).
- simongmt proves only the easy direction of Ch. 3 Lemma 1.2; SubmanifoldCover.lean says the 'only if' direction 'remains a separate theorem'.
- simongmt has no C¹ approximation theorem, and its Chapter04 varifold stores tangent planes as data.
- So a.e. existence of tangent planes (Ch. 3, 1.9) and the C¹ cover are genuinely new obligations: children rectifiable_c1_cover and ae_approx_tangent_exists.

Usable Mathlib items:
- Measure.support API: isClosed_support, mem_support_iff_forall, notMem_support_iff_exists, support_mem_ae (hereditarily Lindelöf), interior_inter_support, support_restrict_subset.
- μHE[n] invariance: IsometryEquiv.measurePreserving_euclideanHausdorffMeasure and euclideanHausdorffMeasure_smul₀.
- Measurable equivalences: MeasurableEquiv.subRight with MeasurableEmbedding.ae_map_iff and MeasurableEquiv.map_apply.
- Measure.ae_smul_measure, ENNReal.Tendsto.const_mul and Besicovitch.ae_tendsto_rnDeriv.

Usable simongmt items:
- Chapter03: CountablyRectifiable.mono and HasWeightedApproximateTangentSpaceAt.unique.
- Chapter01: simon_theorem_3_6 (upper density), simon_theorem_3_26_i and Lusin (simon_theorem_1_17).
- Chapter02: exists_contDiff_one_extension_of_whitney with HasWhitneyC1Compatibility, rademacher_ae_differentiableAt, and area_image_criticalSet_eq_zero.
- Chapter04: planeMeasure_unit_closedBall, tangentDensityCutoff and one_le_density_of_approximateTangent, for Remark 1.8(2).

Lean check (/tmp/rsod-check/RsodCheck/All.lean, built against GMT.Ch05.Submission with Lean v4.35.0-rc3):
- All 12 child types elaborate in the comparator's contract scope.
- With the children and the sibling as sorry declarations, the following compile with 0 errors: the parent assembly of RegularSetOpenDense, the glue proofs of regular_set_rel_open, density_one_regular_point and regular_points_dense, and full proofs of c1_submanifold_open_inter and least_integer_density_point.
- There are 13 sorry warnings: the 12 children plus the simulated sibling.
