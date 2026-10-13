# Parent-supplied natural-language proof

- Parent DAG node: `root.section3_consequences-a1`
- Child DAG node: `root.section3_consequences-a1.chart_projection_positive-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Ch. 3, proof of Lemma 3.3 (chapter-03.txt lines 492-496, printed p. 79, via Ch. 2, Remark 4.4); parent proof Part 2, steps 4-5 (density point and local bi-Lipschitz estimate).

Notation. ℝ^d = Rn d. Hⁿ = μHE[n] and Lⁿ = volume on ℝⁿ, both outer measures. p_J := coordinateProjection J. Dψ(u) := fderiv ℝ ψ u.

Statement. Let n, ℓ ∈ ℕ, V ⊆ ℝⁿ open, ψ C¹ on V with Dψ(u) injective for every u ∈ V, and T ⊆ V with Lⁿ(T) > 0. Then there is J ⊆ Fin(n+ℓ) with #J = n and Hⁿ(p_J(ψ(T))) > 0.

Proof.

1. Facts.
(a) μHE[n] = c_n·μH[n] with a fixed constant c_n ∈ ℝ≥0 (euclideanHausdorffMeasure_def).
(b) Hⁿ = Lⁿ on ℝⁿ (EuclideanSpace.euclideanHausdorffMeasure_eq_volume).
(c) If g : X → Y between metric spaces satisfies dist(x, y) ≤ K·dist(g(x), g(y)) for all x, y, then μH[n](s) ≤ K^n μH[n](g(s)) for every s ⊆ X (AntilipschitzWith.le_hausdorffMeasure_image).
(d) Hausdorff measure is intrinsic: for t ⊆ s ⊆ Z, μH[n](t) is the same whether computed in the metric subspace s or in Z (Isometry.hausdorffMeasure_image for the inclusion of s).

2. Density point (Simon line 492). There is u₀ ∈ T such that Lⁿ(T ∩ U) > 0 for every neighbourhood U of u₀. Otherwise every u ∈ T has a neighbourhood U_u with Lⁿ(T ∩ U_u) = 0. Since ℝⁿ is second countable, countably many U_u cover T, and countable subadditivity gives Lⁿ(T) = 0, a contradiction (Mathlib exists_mem_forall_mem_nhdsWithin_pos_measure).

3. Choice of J (sibling coordinate_projection_injective). Since u₀ ∈ T ⊆ V, D := Dψ(u₀) : ℝⁿ → ℝ^{n+ℓ} is injective, so L := D(ℝⁿ) has dim L = n (LinearMap.finrank_range_of_inj and dim ℝⁿ = n). The sibling, applied with N := n + ℓ and this L, gives J ⊆ Fin(n+ℓ) with #J = n such that p_J is injective on L.
Then A := p_J ∘ D : ℝⁿ → ℝ^{n+ℓ} is injective: if A v = A w, then p_J(Dv) = p_J(Dw) with Dv, Dw ∈ L, so Dv = Dw and v = w.

4. Lower bound for A. A is an injective linear map on the finite-dimensional space ℝⁿ, so there is K > 0 with |v| ≤ K|Av| for all v ∈ ℝⁿ. For n ≥ 1 take K := 1/min_{|v|=1}|Av|, which is positive by compactness of the unit sphere and injectivity; for n = 0 any K > 0 works (Mathlib LinearMap.exists_antilipschitzWith with ker A = 0).

5. Strict differentiability. This replaces the inverse function theorem in Simon's "C¹ diffeomorphism" step.
Put Φ := p_J ∘ ψ : ℝⁿ → ℝ^{n+ℓ}. Since V is open, ψ is C¹ near u₀, hence strictly differentiable at u₀ with derivative D (ContDiffAt.hasStrictFDerivAt). Since p_J is continuous linear, Φ is strictly differentiable at u₀ with derivative A (chain rule).
Therefore there is a neighbourhood s of u₀ with |Φ(x) − Φ(y) − A(x − y)| ≤ (2K)⁻¹|x − y| for all x, y ∈ s (HasStrictFDerivAt.approximates_deriv_on_nhds with constant (2K)⁻¹ > 0).

6. Φ is anti-Lipschitz on s. For x, y ∈ s, by steps 4 and 5:
|x − y| ≤ K|A(x − y)| ≤ K(|Φ(x) − Φ(y)| + |Φ(x) − Φ(y) − A(x − y)|) ≤ K|Φ(x) − Φ(y)| + |x − y|/2.
Hence |x − y| ≤ 2K|Φ(x) − Φ(y)|.

7. Measure estimate. Let T' := T ∩ s. Since s is a neighbourhood of u₀, step 2 gives Lⁿ(T') > 0.
Apply fact (c) to the restriction g := Φ|_s : s → ℝ^{n+ℓ}, where s carries the induced metric and, by step 6, g satisfies the hypothesis with constant 2K. Apply it to T' ⊆ s, and use fact (d) to evaluate μH[n](T') in ℝⁿ. This gives μH[n](T') ≤ (2K)^n μH[n](Φ(T')). Multiplying by c_n: Hⁿ(T') ≤ (2K)^n Hⁿ(Φ(T')).
Since Hⁿ(T') = Lⁿ(T') > 0 by fact (b), and (2K)^n < ∞, we get Hⁿ(Φ(T')) > 0.
Equivalently, as in the parent proof: Φ|_s is injective with a 2K-Lipschitz inverse on Φ(s). The parent's further composition with the isometry ι_J⁻¹ : span{e_j : j ∈ J} → ℝⁿ changes no Hausdorff measure, so it is omitted.

8. Conclusion. Φ(T') = p_J(ψ(T')) ⊆ p_J(ψ(T)), so Hⁿ(p_J(ψ(T))) ≥ Hⁿ(Φ(T')) > 0, and #J = n. ∎

Remark. For n = 0 every step remains valid: T = {0}, L = 0, J = ∅, p_∅ = 0, and H⁰ is counting measure. Measurability of T is never used.

## Key steps

1. There is a density-type point u₀ ∈ T: every neighbourhood of u₀ meets T in positive Lebesgue outer measure.
2. The sibling coordinate_projection_injective, applied to L = range Dψ(u₀), gives J with #J = n such that A = p_J ∘ Dψ(u₀) is injective.
3. Injectivity gives |v| ≤ K|Av|. Strict differentiability of Φ = p_J ∘ ψ at u₀ gives |Φx − Φy − A(x−y)| ≤ |x−y|/(2K) on a neighbourhood s.
4. Hence |x − y| ≤ 2K|Φx − Φy| on s.
5. The anti-Lipschitz bound gives Hⁿ(T ∩ s) ≤ (2K)ⁿ Hⁿ(Φ(T ∩ s)). Since Hⁿ(T ∩ s) = Lⁿ(T ∩ s) > 0 and Φ(T ∩ s) ⊆ p_J(ψ(T)), the projection has positive measure.

## Reference use

### local-project

Queries:
- `rg -n "^def (coordinateProjection|IsC1Submanifold|RectifiableDecomposition|CoordinateProjectionCriterion|BesicovitchFedererProjectionTheorem|RectifiabilityTheoremForSets|SubmanifoldCoverCharacterization|ForAlmostAllProjections)|^noncomputable def coordinateProjection" project/GMT/Ch03/Contract.lean`
- `cmp local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean`
- `rg -n "theorem (exists_mem_forall_mem_nhdsWithin_pos_measure|measure_null_of_locally_null)" mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `rg -n "theorem comap_apply" mathlib/Mathlib/MeasureTheory/OuterMeasure/Operations.lean`
- `rg -n "theorem (le_hausdorffMeasure_image|hausdorffMeasure_image_le|hausdorffMeasure_image) " mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n "theorem (MeasureTheory.Measure.euclideanHausdorffMeasure_def|EuclideanSpace.euclideanHausdorffMeasure_eq_volume|MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero)" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "theorem LinearMap.exists_antilipschitzWith" mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `rg -n "theorem approximates_deriv_on_nhds" mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `rg -n "theorem ContDiffAt.hasStrictFDerivAt |theorem HasStrictFDerivAt.exists_lipschitzOnWith " mathlib/Mathlib/Analysis/Calculus`
- `rg -n "theorem eq_starProjection_of_mem_of_inner_eq_zero" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n "theorem (span_eq_top_of_ne_zero|exists_fun_fin_finrank_span_eq)" mathlib/Mathlib/LinearAlgebra`
- `rg -n "theorem LinearMap.finrank_range_of_inj" mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `rg -n "theorem isOpen_iUnion_countable" mathlib/Mathlib/Topology/Bases.lean`
- `grep -n of_le_mul_dist mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean`
- `rg -n -i "coordinateProjection|PurelyUnrectifiable|besicovitch.?federer|CountablyRectifiable" mathlib/Mathlib (no match)`
- `rg -n "theorem (simon_lemma_3_2|countablyRectifiable_of_measure_zero|exists_bijective_selectedCoordinateMap|countablyRectifiable_of_submanifold_cover|PurelyUnrectifiable.mono)" lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03`
- `rg -n "exists_ae_subset_biUnion_countable" lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n -i "besicovitch.?federer|structure theorem|null.?projection" lake-packages-25730c7c/simongmt/Poincare/SimonGMT (no match)`
- `ls lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter03/ | grep CoordinateProjection (no match: module not built)`
- `lake env lean /tmp/s3c-decomp/final/Challenge{0..5}.lean and /tmp/s3c-decomp/final/EndToEnd.lean (elaboration of exact frozen statements and full child/parent proofs)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/OuterMeasure/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Dual/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/CoordinateProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`

The snapshot (project d09bc8a, Mathlib 25730c7c) has a Contract.lean byte-identical to the workspace. It fixes coordinateProjection as the starProjection onto span{e_j : j ∈ J}, IsC1Submanifold, ForAlmostAllProjections, and the three conjunct Props.

Available and used:
- SimonGMT simon_lemma_3_2, imported by the contract via Chapter03/Rectifiable.lean: closes Lemma 3.2 directly. Its proof uses Measure.exists_ae_subset_biUnion_countable.
- SimonGMT countablyRectifiable_of_measure_zero.
- Mathlib exists_mem_forall_mem_nhdsWithin_pos_measure and measure_null_of_locally_null, plus OuterMeasure.comap_apply.
- Mathlib LipschitzOnWith.hausdorffMeasure_image_le, AntilipschitzWith.le_hausdorffMeasure_image and Isometry.hausdorffMeasure_image.
- Mathlib euclideanHausdorffMeasure_def (μHE[n] = c_n·μH[n], c_n ∈ ℝ≥0) and EuclideanSpace.euclideanHausdorffMeasure_eq_volume.
- Mathlib LinearMap.exists_antilipschitzWith, HasStrictFDerivAt.approximates_deriv_on_nhds, ContDiffAt.hasStrictFDerivAt and HasStrictFDerivAt.exists_lipschitzOnWith.
- Mathlib Submodule.eq_starProjection_of_mem_of_inner_eq_zero, Submodule.span_eq_top_of_ne_zero, Submodule.exists_fun_fin_finrank_span_eq, LinearMap.finrank_range_of_inj and TopologicalSpace.isOpen_iUnion_countable.

No match:
- Mathlib has no coordinateProjection, CountablyRectifiable, PurelyUnrectifiable or Besicovitch–Federer theorem.
- SimonGMT has no Besicovitch–Federer theorem, so it is consumed as a hypothesis.
- SimonGMT's exists_bijective_selectedCoordinateMap (Chapter03/CoordinateProjection.lean) is not built in the pinned package (no CoordinateProjection.olean) and not imported, so the child reproduces it. A full reproduction compiles with only import GMT.Ch03.Submission.

With these, all six child statements were fully proved in Lean using only the standard axioms.
