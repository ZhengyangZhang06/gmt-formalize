# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1`
- Child DAG node: `root.regular_set_open_dense-a1.c1_submanifold_open_inter-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: fact (Sub) of the parent proof (restrict the charts). Let m, N ∈ ℕ, S, B ⊆ ℝ^N, S an m-dimensional C¹ submanifold in the sense of IsC1Submanifold m S, and B open. We show IsC1Submanifold m (B ∩ S).
1. Let y ∈ B ∩ S. Since y ∈ S, the definition of IsC1Submanifold gives V ⊆ ℝ^m open, W ⊆ ℝ^N open with y ∈ W, and φ : ℝ^m → ℝ^N with: φ is C¹ on V (ContDiffOn ℝ 1 φ V), φ is injective on V, φ(V) = W ∩ S, for every compact K ⊆ W the set V ∩ φ⁻¹(K) is compact, and Dφ(x) = fderiv ℝ φ x is injective for every x ∈ V.
2. Put V' := V ∩ φ⁻¹(B) and W' := W ∩ B. Since φ is C¹ on V it is continuous on V; V and B are open, so V' is open (ContinuousOn.isOpen_inter_preimage). W' is open as an intersection of open sets, and y ∈ W' because y ∈ W and y ∈ B.
3. Since V' ⊆ V, φ is C¹ on V' (ContDiffOn.mono), injective on V' (InjOn.mono), and Dφ(x) is injective for all x ∈ V' (each such x lies in V).
4. Image: φ(V ∩ φ⁻¹(B)) = φ(V) ∩ B (Set.image_inter_preimage) = (W ∩ S) ∩ B = (W ∩ B) ∩ (B ∩ S) = W' ∩ (B ∩ S).
5. Properness: let K be compact with K ⊆ W' = W ∩ B. Then K ⊆ W and K ⊆ B. If x ∈ V and φ(x) ∈ K then φ(x) ∈ B, so V' ∩ φ⁻¹(K) = V ∩ φ⁻¹(B) ∩ φ⁻¹(K) = V ∩ φ⁻¹(K), which is compact by the properness in step 1 (applied to K ⊆ W).
6. Steps 2-5 show that (V', W', φ) satisfies all requirements of IsC1Submanifold m at the point y of B ∩ S. Since y ∈ B ∩ S was arbitrary, IsC1Submanifold m (B ∩ S).

## Key steps

1. Take the chart (V, W, φ) of S at y ∈ B ∩ S
2. Restrict: V' := V ∩ φ⁻¹(B) (open by continuity), W' := W ∩ B ∋ y
3. C¹, injectivity and injective derivative restrict to V'
4. φ(V') = φ(V) ∩ B = W' ∩ (B ∩ S)
5. For compact K ⊆ W', V' ∩ φ⁻¹(K) = V ∩ φ⁻¹(K) is compact

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
