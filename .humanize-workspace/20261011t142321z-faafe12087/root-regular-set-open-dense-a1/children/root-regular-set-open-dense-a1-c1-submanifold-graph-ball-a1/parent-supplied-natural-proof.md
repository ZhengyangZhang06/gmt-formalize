# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1`
- Child DAG node: `root.regular_set_open_dense-a1.c1_submanifold_graph_ball-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: fact (Gr) of the parent proof, in the form used in its step 6 (chart x ↦ x₀ + q(x, u(x)) on W' := {x ∈ B̆ⁿ_s(0) : |(x, u(x))| < s}, target open set B̆_s(x₀)). Let n, ℓ ∈ ℕ, q a linear isometry (equivalence) of ℝ^{n+ℓ}, u : ℝⁿ → ℝ^ℓ, x₀ ∈ ℝ^{n+ℓ}, s > 0 and S ⊆ ℝ^{n+ℓ}, with (A) u is C¹ on the closed ball Bⁿ_s(0) (ContDiffOn ℝ 1 u (closedBall 0 s)) and (H) {y : y + x₀ ∈ S} ∩ B_s(0) = q(graphOver u (Bⁿ_s(0))) ∩ B_s(0). We prove IsC1Submanifold n (B̆_s(x₀) ∩ S).
1. Graph points. Let G(x, y) := graphPoint x y = toLp 2 (Fin.append (ofLp x) (ofLp y)) ∈ ℝ^{n+ℓ}. G is linear in the pair (x, y), hence a continuous linear map ℝⁿ × ℝ^ℓ → ℝ^{n+ℓ}. Its Euclidean norm satisfies ‖G(x,y)‖² = Σ_{i<n+ℓ} (Fin.append x y)_i² = ‖x‖² + ‖y‖² (split the sum over Fin (n+ℓ) with Fin.sum_univ_add). Consequences: (i) ‖x‖ ≤ ‖G(x,y)‖; (ii) if G(x,y) = G(x',y') then x = x' (compare the first n coordinates, Fin.append_left). Also graphOver u D = {G(x, u(x)) : x ∈ D}.
2. Unfolding (H): for z ∈ ℝ^{n+ℓ} with ‖z‖ ≤ s we have z + x₀ ∈ S ⟺ z ∈ q(graphOver u (Bⁿ_s(0))), i.e. ⟺ ∃ x with ‖x‖ ≤ s and z = q(G(x, u(x))).
3. Chart. Let g(x) := G(x, u(x)), φ(x) := q(g(x)) + x₀, W := B̆_s(x₀) (open) and Ω := {x ∈ B̆ⁿ_s(0) : ‖g(x)‖ < s}. Since u is continuous on Bⁿ_s(0) ⊇ B̆ⁿ_s(0), the function x ↦ ‖g(x)‖ is continuous on the open ball B̆ⁿ_s(0), so Ω = B̆ⁿ_s(0) ∩ {x : ‖g(x)‖ < s} is open (ContinuousOn.isOpen_inter_preimage).
4. Smoothness. Every x ∈ Ω lies in the open ball B̆ⁿ_s(0), which is a neighbourhood of x contained in Bⁿ_s(0); hence by (A) u is C¹ at x (ContDiffOn.contDiffAt) and differentiable at x. Since G and q are continuous linear maps, φ = q ∘ G ∘ (id, u) + x₀ is C¹ on Ω, and for x ∈ Ω, Dφ(x)v = q(G(v, Du(x)v)) for v ∈ ℝⁿ.
5. Injectivity on Ω: φ(x) = φ(x') gives q(g(x)) = q(g(x')), hence g(x) = g(x') (q injective), hence x = x' by 1(ii).
6. Injective derivative: if Dφ(x)v = 0 then G(v, Du(x)v) = 0 (q injective), so ‖v‖ ≤ ‖G(v, Du(x)v)‖ = 0 by 1(i); thus v = 0, and the linear map Dφ(x) = fderiv ℝ φ x is injective.
7. Image: φ(Ω) = W ∩ (B̆_s(x₀) ∩ S). (⊆) Let x ∈ Ω and z := q(g(x)). Then ‖z‖ = ‖g(x)‖ < s (q is an isometry), so φ(x) = z + x₀ ∈ B̆_s(x₀) = W; and x ∈ B̆ⁿ_s(0) ⊆ Bⁿ_s(0), so z ∈ q(graphOver u (Bⁿ_s(0))) with ‖z‖ ≤ s, whence by step 2 φ(x) = z + x₀ ∈ S. (⊇) Let y ∈ B̆_s(x₀) ∩ S and z := y - x₀. Then ‖z‖ < s and z + x₀ = y ∈ S, so by step 2 z = q(g(x)) for some x with ‖x‖ ≤ s. Then ‖g(x)‖ = ‖z‖ < s and, by 1(i), ‖x‖ ≤ ‖g(x)‖ < s; so x ∈ Ω and φ(x) = z + x₀ = y.
8. Properness: let K ⊆ W be compact. Claim Ω ∩ φ⁻¹(K) = Bⁿ_s(0) ∩ φ⁻¹(K). (⊆) is clear since Ω ⊆ Bⁿ_s(0). (⊇) If ‖x‖ ≤ s and φ(x) ∈ K ⊆ B̆_s(x₀), then ‖g(x)‖ = ‖φ(x) - x₀‖ < s and ‖x‖ ≤ ‖g(x)‖ < s, so x ∈ Ω. Now φ is continuous on the compact ball Bⁿ_s(0) (u is continuous there) and K is closed, so Bⁿ_s(0) ∩ φ⁻¹(K) is a closed subset of the compact set Bⁿ_s(0) (ContinuousOn.preimage_isClosed_of_isClosed), hence compact.
9. For every y ∈ B̆_s(x₀) ∩ S we have y ∈ W, and the triple (Ω, W, φ) satisfies: Ω, W open; φ C¹ and injective on Ω; φ(Ω) = W ∩ (B̆_s(x₀) ∩ S); properness (step 8); injective derivative (step 6). Hence IsC1Submanifold n (B̆_s(x₀) ∩ S). (If B̆_s(x₀) ∩ S is empty the claim is vacuous.)

## Key steps

1. ‖(x,y)‖² = ‖x‖² + ‖y‖², so ‖x‖ ≤ ‖(x,y)‖ and graph points determine x
2. Unfold the hypothesis: for ‖z‖ ≤ s, z + x₀ ∈ S ⟺ z ∈ q(graph u)
3. Chart φ(x) = q(x,u(x)) + x₀ on the open set Ω = {x ∈ B̆ⁿ_s : ‖(x,u(x))‖ < s}
4. φ is C¹, injective, with injective derivative on Ω
5. φ(Ω) = B̆_s(x₀) ∩ S using the norm inequality
6. Ω ∩ φ⁻¹(K) = Bⁿ_s ∩ φ⁻¹(K) is a closed subset of a compact ball

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
