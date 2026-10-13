# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1`
- Child DAG node: `root.regular_set_open_dense-a1.density_one_regular_point-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof (support form of Theorem 7.1, obtained from Theorem 5.2 as in the first paragraph of the printed proof of 7.1). Hypothesis: the sibling statement AllardRegularityTheorem (Simon 5.2), taken as an explicit premise; the parent supplies it as Submission.allard_regularity_theorem. Let n ≥ 1, U ⊆ ℝ^{n+ℓ} open, V : RectifiableVarifold n ℓ U with generalized mean curvature H, V.LocallyLp H p with p > n, V.mult ≥ 1 V.weight-a.e., x₀ ∈ U and V.HasDensity x₀ 1. We show x₀ ∈ V.regularSet. Write μ := V.weight, spt V := V.support.
Dependencies: children translated_varifold, allard_hypotheses_small_scale, c1_submanifold_graph_ball.
1. AllardRegularityTheorem applied to n, ℓ (1 ≤ n) and p (n < p) gives δ₀, γ, C with 0 < δ₀ < 1, 0 < γ < 1 such that for every open U', every W : RectifiableVarifold n ℓ U', every H', every δ ∈ (0, δ₀] and every ρ: W.AllardHypotheses H' p δ ρ ⟹ AllardConclusion W p δ ρ γ C.
2. Translate: child translated_varifold with V and x₀ gives W : RectifiableVarifold n ℓ U' with U' := {y : y + x₀ ∈ U}, W.mult y = V.mult(y + x₀), W.weight = map (fun y => y - x₀) μ, W.support = {y : y + x₀ ∈ spt V}, W.HasGeneralizedMeanCurvature H' and W.LocallyLp H' p, where H'(y) := H(y + x₀).
3. U' is open (preimage of the open U under the continuous y ↦ y + x₀) and 0 ∈ U' (0 + x₀ = x₀ ∈ U).
4. W.HasDensity 0 1. Let e be the measurable equivalence y ↦ y - x₀ (MeasurableEquiv.subRight x₀). For every r, W.weight(B_r(0)) = (map e μ)(B_r(0)) = μ(e⁻¹(B_r(0))) = μ(B_r(x₀)) (MeasurableEquiv.map_apply; ‖y - x₀‖ ≤ r ⟺ y ∈ B_r(x₀)). So the density-ratio functions of W at 0 and of V at x₀ coincide, and V.HasDensity x₀ 1 gives W.HasDensity 0 1.
5. W.mult ≥ 1 W.weight-a.e.: by MeasurableEmbedding.ae_map_iff for e, this is equivalent to: for μ-a.e. x, 1 ≤ W.mult(x - x₀) = V.mult((x - x₀) + x₀) = V.mult x, which is the hypothesis.
6. Child allard_hypotheses_small_scale applied to W (on the open set U', with H', p, the facts of steps 2-5) and δ := δ₀ > 0 gives ρ with W.AllardHypotheses H' p δ₀ ρ; in particular ρ > 0 and 0 ∈ W.support.
7. Step 1 with U', W, H', δ := δ₀ (0 < δ₀ ≤ δ₀) and ρ gives AllardConclusion W p δ₀ ρ γ C: a linear isometry q and u : ℝⁿ → ℝ^ℓ, C¹ on the closed ball Bⁿ_{γρ}(0), with W.support ∩ B_{γρ}(0) = q(graphOver u (Bⁿ_{γρ}(0))) ∩ B_{γρ}(0). By step 2 the left side is {y : y + x₀ ∈ spt V} ∩ B_{γρ}(0).
8. With s := γρ > 0 (γ > 0, ρ > 0), child c1_submanifold_graph_ball (with q, u, x₀, s and S := spt V) gives IsC1Submanifold n (B̆_s(x₀) ∩ spt V).
9. From 0 ∈ W.support = {y : y + x₀ ∈ spt V} (step 6) we get x₀ ∈ spt V. With step 8 (radius s > 0) this is exactly x₀ ∈ V.regularSet.

## Key steps

1. Obtain δ₀, γ, C from AllardRegularityTheorem
2. Translate V by -x₀; the translate W has density 1 at 0 and multiplicity ≥ 1 a.e.
3. Small-scale Allard hypotheses for W at some ρ > 0
4. Allard: spt W ∩ B_{γρ}(0) = q(graph u) ∩ B_{γρ}(0)
5. Graph lemma: B̆_{γρ}(x₀) ∩ spt V is a C¹ submanifold; x₀ ∈ spt V, so x₀ ∈ reg V

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
