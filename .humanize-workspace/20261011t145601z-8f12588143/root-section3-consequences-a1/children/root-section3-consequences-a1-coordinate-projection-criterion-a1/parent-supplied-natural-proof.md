# Parent-supplied natural-language proof

- Parent DAG node: `root.section3_consequences-a1`
- Child DAG node: `root.section3_consequences-a1.coordinate_projection_criterion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Ch. 3, Lemma 3.3 and its proof (chapter-03.txt lines 476-496, printed pp. 78-79); parent proof Part 2, steps 2 and 4.
Erratum: Def. 3.1 (line 446) "if P contains" should read "if S contains". This is how the definition is encoded: PurelyUnrectifiable n S := ∀ R ⊆ S, CountablyRectifiable n R → Hⁿ(R) = 0.

Notation. ℝ^d = Rn d. Hⁿ = μHE[n] and Lⁿ = volume, both outer measures. p_J := coordinateProjection J.

Statement. Assume SubmanifoldCoverCharacterization (Lemma 1.2). Then for all n, ℓ and S ⊆ ℝ^{n+ℓ} with Hⁿ(p_J(S)) = 0 for every J with #J = n, S is purely n-unrectifiable.

Proof. Assume Lemma 1.2. Fix n, ℓ and S with the projection hypothesis
(H): Hⁿ(p_J(S)) = 0 whenever J ⊆ Fin(n+ℓ) and #J = n.
Let R ⊆ S be countably n-rectifiable; we show Hⁿ(R) = 0. Suppose instead that Hⁿ(R) ≠ 0.

1. Lemma 1.2, direction "⇒" (Simon line 490). Apply the assumed characterization to M := R. This gives N₀ ⊆ ℝ^{n+ℓ} with Hⁿ(N₀) = 0 and sets N_j (j ∈ ℕ), each with IsC1Submanifold n N_j, such that R ⊆ N₀ ∪ ⋃_j N_j.

2. Choice of a submanifold (Simon line 491). R ⊆ N₀ ∪ ⋃_j (R ∩ N_j), so by countable subadditivity Hⁿ(R) ≤ Hⁿ(N₀) + Σ_j Hⁿ(R ∩ N_j) = Σ_j Hⁿ(R ∩ N_j). Since Hⁿ(R) ≠ 0, some j has Hⁿ(R ∩ N_j) ≠ 0. Fix it and write N := N_j.

3. Charts. By IsC1Submanifold n N, each y ∈ N has:
- an open set V_y ⊆ ℝⁿ;
- an open set W_y ⊆ ℝ^{n+ℓ} with y ∈ W_y;
- a map ψ_y : ℝⁿ → ℝ^{n+ℓ}, C¹ on V_y, with Dψ_y(u) injective for all u ∈ V_y and ψ_y(V_y) = W_y ∩ N.
Injectivity and properness of ψ_y are not needed.
The open sets W_y (y ∈ N) cover N. Since ℝ^{n+ℓ} is second countable, there is a countable I ⊆ N with ⋃_{y∈I} W_y = ⋃_{y∈N} W_y ⊇ N (Lindelöf; Mathlib TopologicalSpace.isOpen_iUnion_countable).

4. Choice of a chart. R ∩ N ⊆ ⋃_{y∈I} (R ∩ N ∩ W_y), so countable subadditivity gives y ∈ I with Hⁿ(R ∩ N ∩ W_y) ≠ 0. Write V := V_y and ψ := ψ_y.

5. Let T := V ∩ ψ⁻¹(R) ⊆ V. Then ψ(T) = ψ(V) ∩ R = W_y ∩ N ∩ R, so Hⁿ(ψ(T)) ≠ 0.

6. Apply the sibling c1_image_null with N := n + ℓ, V, T and ψ (V is open, ψ is C¹ on V, T ⊆ V). If Lⁿ(T) = 0, it would give Hⁿ(ψ(T)) = 0. Hence Lⁿ(T) > 0.

7. Apply the sibling chart_projection_positive to n, ℓ, V, T and ψ (Dψ(u) is injective for u ∈ V). It gives J ⊆ Fin(n+ℓ) with #J = n and Hⁿ(p_J(ψ(T))) > 0. This is Simon lines 492-496: near a density point the coordinate projection is bi-Lipschitz on the chart image, so the projection of S ∩ N has positive measure.

8. Since ψ(T) ⊆ R ⊆ S, we have p_J(ψ(T)) ⊆ p_J(S). So Hⁿ(p_J(S)) ≥ Hⁿ(p_J(ψ(T))) > 0, contradicting (H) for this J. Therefore Hⁿ(R) = 0. As R ⊆ S was an arbitrary countably n-rectifiable set, S is purely n-unrectifiable. ∎

Remarks.
- Only the forward direction of Lemma 1.2 is used.
- No measurability of S or R is needed; all estimates use outer measure.
- The argument is uniform in n. For n = 0 one can also argue directly, as in the parent proof: J = ∅ gives p_∅(S) = {0}, of H⁰-measure 1 unless S = ∅.

## Key steps

1. Suppose R ⊆ S is countably rectifiable with Hⁿ(R) ≠ 0. Lemma 1.2 (⇒) covers R by a null set N₀ and C¹ submanifolds N_j.
2. Countable subadditivity gives j with Hⁿ(R ∩ N_j) ≠ 0. Lindelöf on the chart domains W_y then gives a chart (V, W, ψ) with Hⁿ(R ∩ N_j ∩ W) ≠ 0.
3. T := V ∩ ψ⁻¹(R) satisfies ψ(T) = R ∩ N_j ∩ W, so Lⁿ(T) > 0 by the sibling c1_image_null.
4. The sibling chart_projection_positive gives J with #J = n and Hⁿ(p_J(ψ(T))) > 0. But p_J(ψ(T)) ⊆ p_J(S), which is Hⁿ-null — a contradiction.

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
