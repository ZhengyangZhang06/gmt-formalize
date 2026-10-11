# Parent-supplied natural-language proof

- Parent DAG node: `root.section3_consequences-a1`
- Child DAG node: `root.section3_consequences-a1.rectifiable_decomposition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Ch. 3, Lemma 3.2 and its proof (chapter-03.txt lines 449-469, printed p. 78); parent proof Part 1, step 1.

Notation. ℝ^d = Rn d = EuclideanSpace ℝ (Fin d). Hⁿ = μHE[n], applied to arbitrary sets as an outer measure. CountablyRectifiable and PurelyUnrectifiable are the SimonGMT predicates opened by the contract.

Statement to prove (RectifiableDecomposition). For all n, ℓ and A ⊆ ℝ^{n+ℓ}, assume there are A_j (j ∈ ℕ) with A = ⋃_j A_j and Hⁿ(A_j) < ∞ for all j. Then:
(i) ∃ R P, A = R ∪ P ∧ Disjoint R P ∧ CountablyRectifiable n R ∧ PurelyUnrectifiable n P;
(ii) if NullMeasurableSet A μHE[n], then ∃ R P, A = R ∪ P ∧ Disjoint R P ∧ MeasurableSet R ∧ CountablyRectifiable n R ∧ PurelyUnrectifiable n P.

Proof.

1. Fix n, ℓ, A and (A_j) as in the hypothesis. From A = ⋃_j A_j we get the cover A ⊆ ⋃_j A_j, and Hⁿ(A_j) < ∞ for every j.

2. Apply the kernel-checked theorem Poincare.SimonGMT.Chapter03.simon_lemma_3_2 (Chapter03/Rectifiable.lean; this module is imported by the contract) with:
- E := ℝ^{n+ℓ}, the given n and the set A;
- the cover S := (A_j)_{j∈ℕ};
- hcover : A ⊆ ⋃_j A_j and hfinite : ∀ j, μHE[n] (A_j) < ∞.
Its first component is literally conclusion (i).
Its second component states: if NullMeasurableSet A μHE[n], then ∃ R P, A = R ∪ P ∧ Disjoint R P ∧ MeasurableSet R ∧ NullMeasurableSet P μHE[n] ∧ CountablyRectifiable n R ∧ PurelyUnrectifiable n P. Discarding the conjunct NullMeasurableSet P gives conclusion (ii).
The library lemma and the contract use the same objects CountablyRectifiable, PurelyUnrectifiable and μHE[n], so no translation is needed. This proves RectifiableDecomposition.

3. For completeness, here is the mathematics of the library proof. It is Simon lines 455-469, with Simon's α_j-supremum selection of closed sets R_ij replaced by an equivalent σ-finite exhaustion.
(a) σ-finiteness. Let B_j ⊇ A_j be Borel with Hⁿ(B_j) = Hⁿ(A_j) < ∞ (measurable hulls). Then A ⊆ ⋃_j B_j, so μ := Hⁿ⌞A is σ-finite.
(b) Exhaustion. Let C be the class of Borel, countably n-rectifiable subsets of ℝ^{n+ℓ}. C is closed under countable unions: interleave the countable families of Lipschitz maps via a pairing ℕ×ℕ → ℕ, and take the union of the Hⁿ-null exceptional sets. Since μ is σ-finite, there is a countable D ⊆ C such that μ(S ∖ ⋃D) = 0 for every S ∈ C (Mathlib Measure.exists_ae_subset_biUnion_countable). Put M := ⋃D; M is Borel and countably n-rectifiable.
(c) A ∖ M is purely n-unrectifiable. Let S ⊆ A ∖ M be countably n-rectifiable, say S ⊆ M₀ ∪ ⋃_k F_k(ℝⁿ) with Hⁿ(M₀) = 0 and F_k Lipschitz. Let B be the union of a Borel Hⁿ-null hull of M₀ with the sets F_k(ℝⁿ); these are σ-compact, hence Borel. Then B ∈ C and S ⊆ B. So μ(B ∖ M) = Hⁿ((B ∖ M) ∩ A) = 0, and S ⊆ (B ∖ M) ∩ A gives Hⁿ(S) = 0.
(d) For (i), take R := A ∩ M (countably rectifiable, being a subset of M) and P := A ∖ M.
(e) For (ii), suppose A is Hⁿ-measurable; then so is A ∩ M. Choose a Borel R ⊆ A ∩ M with Hⁿ((A ∩ M) ∖ R) = 0, and put P := A ∖ R. Then A = R ∪ P disjointly, R is Borel and countably rectifiable, and P ⊆ (A ∖ M) ∪ ((A ∩ M) ∖ R). Any countably rectifiable R' ⊆ P splits as R' ∩ (A ∖ M), which is Hⁿ-null by (c), and R' ∩ ((A ∩ M) ∖ R), which is Hⁿ-null. Hence P is purely n-unrectifiable. ∎

## Key steps

1. A = ⋃_j A_j gives the cover A ⊆ ⋃_j A_j with Hⁿ(A_j) < ∞.
2. SimonGMT simon_lemma_3_2 with S := (A_j) gives conclusion (i) directly. Its measurable part gives (ii) after dropping NullMeasurableSet P.
3. The library argument: σ-finite exhaustion by Borel countably rectifiable sets gives M; A ∖ M is purely unrectifiable; take R := A ∩ M, or a Borel inner approximation of it when A is Hⁿ-measurable.

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
