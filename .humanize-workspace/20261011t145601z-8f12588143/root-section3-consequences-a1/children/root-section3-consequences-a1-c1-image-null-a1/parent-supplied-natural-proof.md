# Parent-supplied natural-language proof

- Parent DAG node: `root.section3_consequences-a1`
- Child DAG node: `root.section3_consequences-a1.c1_image_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof Part 2, step 4 ("Lⁿ(T′) > 0 since Hⁿ(ψ(T′)) ≤ Lip(ψ|D)ⁿ Lⁿ(T′)"). This makes explicit the measure step that is implicit in Simon's proof of Lemma 3.3 (chapter-03.txt lines 490-492).

Notation. ℝ^d = Rn d. Hⁿ = μHE[n]. Lⁿ = volume on ℝⁿ. All measures are applied to arbitrary sets as outer measures.

Statement. Let n, N ∈ ℕ, V ⊆ ℝⁿ open, ψ : ℝⁿ → ℝᴺ C¹ on V (ContDiffOn ℝ 1 ψ V), and T ⊆ V with Lⁿ(T) = 0. Then Hⁿ(ψ(T)) = 0.

Proof.

1. Facts about Hⁿ.
(a) μHE[n] = c_n · μH[n], where c_n := addHaarScalarFactor(volume on ℝⁿ, μH[n]) is a fixed element of ℝ≥0 (in particular finite) that does not depend on the ambient space (Mathlib MeasureTheory.Measure.euclideanHausdorffMeasure_def).
(b) If f is K-Lipschitz on a subset s of a metric space, then μH[n](f(s)) ≤ K^n μH[n](s) (LipschitzOnWith.hausdorffMeasure_image_le). Multiplying by c_n gives Hⁿ(f(s)) ≤ K^n Hⁿ(s).
(c) On ℝⁿ itself, Hⁿ = Lⁿ (EuclideanSpace.euclideanHausdorffMeasure_eq_volume).

2. Local Lipschitz property. Let u ∈ T. Since u ∈ V and V is open, ψ is C¹ on a neighbourhood of u, so ψ is strictly differentiable at u (ContDiffAt.hasStrictFDerivAt). Hence ψ is Lipschitz on some neighbourhood t_u of u (HasStrictFDerivAt.exists_lipschitzOnWith; classically, apply the mean value inequality on a ball around u on which ‖Dψ‖ ≤ ‖Dψ(u)‖ + 1). That is, there is K_u ≥ 0 with |ψ(a) − ψ(b)| ≤ K_u |a − b| for all a, b ∈ t_u.

3. Local nullity. By 1(b) applied to the set T ∩ t_u ⊆ t_u, and 1(c):
Hⁿ(ψ(T ∩ t_u)) ≤ K_u^n Hⁿ(T ∩ t_u) = K_u^n Lⁿ(T ∩ t_u) ≤ K_u^n Lⁿ(T) = 0.

4. Countable cover. ℝⁿ is second countable, so (Lindelöf) a countable subfamily of the relative neighbourhoods T ∩ t_u (u ∈ T) covers T, say T ∩ t_{u_k} for k ∈ ℕ. Then ψ(T) = ⋃_k ψ(T ∩ t_{u_k}). By countable subadditivity of the outer measure Hⁿ, Hⁿ(ψ(T)) ≤ Σ_k Hⁿ(ψ(T ∩ t_{u_k})) = 0.
In Lean: apply measure_null_of_locally_null to the outer measure B ↦ μHE[n](ψ(B)) on ℝⁿ (OuterMeasure.comap ψ μHE[n], with comap_apply), using T ∩ t_u ∈ 𝓝[T] u. ∎

Remark. The case n = 0 is included: the argument applies verbatim, although Lⁿ(T) = 0 then already forces T = ∅. Measurability of T is never used.

## Key steps

1. Hⁿ = c_n·μH[n] with c_n a fixed finite constant; Hⁿ = Lⁿ on ℝⁿ; a K-Lipschitz map increases Hⁿ by at most a factor Kⁿ.
2. Each u ∈ T has a neighbourhood t_u on which ψ is Lipschitz, since C¹ near u implies strictly differentiable at u.
3. Hⁿ(ψ(T ∩ t_u)) ≤ K_uⁿ Lⁿ(T ∩ t_u) = 0.
4. By second countability, countably many t_u cover T; countable subadditivity gives Hⁿ(ψ(T)) = 0.

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
