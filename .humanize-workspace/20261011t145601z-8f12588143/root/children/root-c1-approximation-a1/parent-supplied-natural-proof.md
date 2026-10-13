# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.c1_approximation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Introduction to GMT, Ch. 2, Theorem 1.5 (C¹ Approximation Theorem), statement in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt lines 165-168 (printed p. 42), printed proof lines 246-268 (printed p. 44). It is the result cited in Ch. 3, proof of Lemma 1.2 (chapter-03.txt lines 39-42) and in Ch. 3, (2.4), (2.8), 2.10(2) (chapter-03.txt lines 378-380, 426-428, 440-442). Simon states it for scalar f; the vector-valued statement below follows componentwise (Step 2). Notation: ℝᵏ = EuclideanSpace ℝ (Fin k), Lⁿ = volume, Dh(x) = fderiv ℝ h x (Mathlib convention: Dh(x) = 0 where h is not differentiable).

Statement. For n, p ∈ ℕ, a K-Lipschitz map f : ℝⁿ → ℝᵖ and ε ∈ (0, ∞], there is a C¹ map g : ℝⁿ → ℝᵖ with Lⁿ({x : f(x) ≠ g(x) or Df(x) ≠ Dg(x)}) < ε.

Proof.

1. Trivial cases. If ε = ∞ the measure bound only needs finiteness, and the set constructed below has finite measure, so we may assume ε < ∞ (or simply run the construction with ε replaced by 1). If n = 0, then ℝ⁰ = {0}; every map on ℝ⁰ is C¹ (indeed ContDiff), so g := f works and the exceptional set is empty. If p = 0 then ℝᵖ = {0}, f = g = 0 works. Assume n ≥ 1, p ≥ 1, 0 < ε < ∞.

2. Reduction to scalar functions. Write f = Σ_{i=1}^p fⁱ eᵢ with fⁱ := ⟨f, eᵢ⟩ (K-Lipschitz, ℝ-valued). Suppose for each i we have gⁱ ∈ C¹(ℝⁿ, ℝ) with Lⁿ({fⁱ ≠ gⁱ} ∪ {Dfⁱ ≠ Dgⁱ}) < ε/(p+1). Put g := Σ gⁱ eᵢ (C¹). By Rademacher's theorem (Ch. 2, Theorem 1.4, chapter-02.txt lines 62-130; SimonGMT Poincare.SimonGMT.Chapter02.rademacher_ae_differentiableAt) the set Z where f is not differentiable is Lⁿ-null. At x ∉ Z every fⁱ is differentiable with Dfⁱ(x) = ⟨Df(x)(·), eᵢ⟩, so f(x) ≠ g(x) or Df(x) ≠ Dg(x) forces fⁱ(x) ≠ gⁱ(x) or Dfⁱ(x) ≠ Dgⁱ(x) for some i. Hence the exceptional set for f is contained in Z ∪ ⋃ᵢ({fⁱ ≠ gⁱ} ∪ {Dfⁱ ≠ Dgⁱ}), of measure < p·ε/(p+1) < ε. So it suffices to treat f : ℝⁿ → ℝ Lipschitz (Steps 3-8).

3. Differentiability set (Simon line 246). By Rademacher's theorem f is differentiable on a Borel set B with Lⁿ(ℝⁿ ∖ B) = 0 (the set of differentiability points of a continuous function is Borel, and x ↦ Df(x) is Borel measurable; Mathlib measurableSet_of_differentiableAt, measurable_fderiv).

4. Lusin (Simon lines 247-249; Ch. 1, Theorem 1.17, chapter-01.txt lines 346-380, SimonGMT IsBorelRegularOuterMeasure.simon_theorem_1_17, “which applies to sets of infinite measure for Lⁿ”). For j ≥ 1 let Aⱼ := {x ∈ B : j − 1 ≤ |x| < j} (Borel, finite measure). Lusin's theorem for real-valued functions (SimonGMT Chapter01.exists_isClosed_continuousOn_of_measurable with ν := Lⁿ, its regularity hypothesis supplied by MeasurableSet.exists_isClosed_sdiff_lt), applied on the finite-measure Borel set Aⱼ to each of the n Borel components x ↦ Df(x)e_l with error ε2^{-j-2}/n, gives closed sets whose intersection Cⱼ ⊆ Aⱼ is closed, satisfies Lⁿ(Aⱼ ∖ Cⱼ) < ε 2^{-j-2}, and Df|Cⱼ is continuous. C := ⋃ⱼ Cⱼ is closed (every bounded set meets only finitely many Cⱼ) and Df|C is continuous (pasting along the locally finite family of closed sets Cⱼ); C ⊆ B and Lⁿ(ℝⁿ ∖ C) ≤ Lⁿ(ℝⁿ ∖ B) + Σⱼ ε2^{-j-2} < ε/2.

5. Remainder functions (Simon lines 250-257). For x, y ∈ C with y ≠ x put R(x, y) := (f(y) − f(x) − Df(x)(y − x))/|y − x|, and for k ≥ 1, ηₖ(x) := sup{|R(x, y)| : y ∈ C, 0 < |y − x| < 1/k} (sup ∅ := 0) for x ∈ C, ηₖ(x) := 0 for x ∉ C. Since |R(x, y)| ≤ K + ‖Df(x)‖ ≤ 2K (f is K-Lipschitz), ηₖ is real-valued. Since f is differentiable at every x ∈ C ⊆ B, ηₖ(x) ↓ 0 as k → ∞ for every x ∈ C. Each ηₖ is Borel on C: R is continuous on {(x, y) ∈ C × C : x ≠ y} (f continuous, Df|C continuous), so for fixed x the supremum may be taken over y in a fixed countable dense subset D of C (any y ∈ C with 0 < |y − x| < 1/k is a limit of points of D in the same open shell), and ηₖ(x) = sup_{y∈D} 1_{0<|y−x|<1/k}·|R(x, y)| is a countable supremum of Borel functions of x.

6. Egoroff (Simon lines 257-260). For j ≥ 1 apply Egoroff's theorem (Mathlib MeasureTheory.tendstoUniformlyOn_of_ae_tendsto) to the finite measure Lⁿ⌞(C ∩ B_j(0)) and the Borel functions ηₖ → 0: there is a measurable Gⱼ ⊆ C ∩ B_j(0) with Lⁿ((C ∩ B_j(0)) ∖ Gⱼ) < ε 2^{-j-3} on which ηₖ → 0 uniformly. Put A₀ := ⋃ⱼ (Gⱼ ∖ B_{j−1}(0)). Then Lⁿ(C ∖ A₀) < ε/8 and ηₖ → 0 uniformly on A₀ ∩ B_j(0) for each j (A₀ ∩ B_j(0) ⊆ G₁ ∪ … ∪ Gⱼ).

7. Closed set (Simon lines 260-262). For each j choose (inner regularity; MeasurableSet.exists_isClosed_sdiff_lt) a closed Fⱼ ⊆ Gⱼ ∖ B_{j−1}(0) with Lⁿ((Gⱼ ∖ B_{j−1}(0)) ∖ Fⱼ) < ε2^{-j-3}, and put A := ⋃ⱼ Fⱼ. A is closed because Fⱼ ⊆ {j − 1 ≤ |x| < j}, so the family is locally finite; A ⊆ A₀ and Lⁿ(A₀ ∖ A) < ε/8. Then Lⁿ(ℝⁿ ∖ A) ≤ Lⁿ(ℝⁿ ∖ C) + Lⁿ(C ∖ A₀) + Lⁿ(A₀ ∖ A) < ε/2 + ε/8 + ε/8 < ε.

8. Whitney extension (Simon line 262; Ch. 2, Theorem 1.6, chapter-02.txt lines 173-185; SimonGMT Poincare.SimonGMT.Chapter02.exists_contDiff_one_extension_of_whitney with the structure HasWhitneyC1Compatibility). Take h := f, D := Df on the closed set A. Then h|A and D|A are continuous (Steps 4, A ⊆ C), and for every compact K ⊆ A, sup_{x∈K} ηₖ(x) → 0 (K is bounded, so K ⊆ A₀ ∩ B_j(0) for some j), i.e. for every ε' > 0 there is δ > 0 with |f(y) − f(x) − Df(x)(y − x)| ≤ ε'|y − x| for all x ∈ K, y ∈ A, |x − y| < δ: this is exactly the hypothesis 1.6(‡) (the remainder field of HasWhitneyC1Compatibility). Whitney's theorem gives g ∈ C¹(ℝⁿ) with g = f on A and Dg(a) = Df(a) for every a ∈ A (HasFDerivAt g (Df a) a). Hence {f ≠ g} ∪ {Df ≠ Dg} ⊆ ℝⁿ ∖ A, which has measure < ε by Step 7. ∎

Remark (no departure from the book except the explicit vector-valued reduction in Step 2 and the bookkeeping of Lusin/Egoroff on the σ-finite measure Lⁿ, which Simon indicates in lines 247-260).

## Key steps

1. Dispose of n = 0, p = 0 and ε = ∞; reduce to scalar f componentwise using Rademacher's theorem.
2. Rademacher: f is differentiable on a Borel set of full measure, with Borel derivative.
3. Lusin on annuli: a closed C of co-measure < ε/2 on which Df is continuous.
4. Remainders ηₖ(x) = sup_{y∈C, 0<|y−x|<1/k}|R(x,y)| are Borel and decrease to 0 on C.
5. Egoroff on bounded pieces and inner regularity: a closed A of co-measure < ε on which ηₖ → 0 uniformly on compacts (Whitney's hypothesis 1.6(‡)).
6. Whitney extension (SimonGMT exists_contDiff_one_extension_of_whitney): C¹ g with g = f and Dg = Df on A.

## Reference use

### local-project

Queries:
- `rg -n "^def |^noncomputable def |^abbrev " project/GMT/Ch03/Contract.lean (frozen definitions: IsC1Submanifold, IsPositiveLocallyIntegrableWeight, approxTangentPlane, HasTangentialDifferentialAt, areaJacobian, coareaJacobian, HasApproxTangentPlaneWithMultiplicity, coordinateProjection, frameProjection, ForAlmostAllProjections, HasLocallyFinitePerimeter, IsGaussGreenPair, normalAverage, reducedBoundary, reducedNormal)`
- `rg -n "theorem normDet_comp|def normDet|normDet_sq" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `rg -n "ae_tendsto_average_norm_sub|ae_tendsto_rnDeriv|def vitaliFamily" mathlib/Mathlib/MeasureTheory/Covering`
- `rg -n "tendstoUniformlyOn_of_ae_tendsto" mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `rg -n "exists_disjoint_covering_ae" mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `rg -n "haarMeasure_unique|isHaarMeasure_haarMeasure" mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `rg -n "eLpNorm_le_eLpNorm_fderiv_of_eq" mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `rg -n "euclideanHausdorffMeasure_eq_volume" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "LipschitzWith.ae_differentiableAt" mathlib/Mathlib`
- `rg -n -i "lusin" mathlib/Mathlib`
- `rg -l -i "grassmannian|coarea|kirszbraun|CountablyRectifiable|whitney" mathlib/Mathlib`
- `grep -n for simon_lemma_3_2, measurable_rectifiable_purelyUnrectifiable_decomposition, countablyRectifiable_of_submanifold_cover, IsSimonSubmanifold, simon_remark_1_3_nullMeasurable, HasWeightedApproximateTangentSpaceAt.unique, rademacher_ae_differentiableAt, exists_contDiff_one_extension_of_whitney, HasWhitneyC1Compatibility, area_formula_lipschitzOn_multiplicity, weighted_area_formula_lipschitzOn_fiberSum, areaJacobian_comp_eq_parametrization_mul_tangential, simon_theorem_3_3, simon_theorem_3_6, simon_theorem_4_14, exists_isClosed_continuousOn_of_measurable, IsLocallyBV in the pinned simongmt package Poincare/SimonGMT`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/RingTheory/Grassmannian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/CoordinateProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`

Snapshot (project d09bc8a, Mathlib 25730c7c) plus the pinned simongmt dependency. Available and cited by the children: SimonGMT simon_lemma_3_2 and measurable_rectifiable_purelyUnrectifiable_decomposition (Lemma 3.2), countablyRectifiable_of_submanifold_cover (1.2 '⇐'; IsSimonSubmanifold (E := ℝⁿ) 1 unfolds to the contract's IsC1Submanifold), countablyRectifiable_iUnion/_range/_of_measure_zero, countablyRectifiable_image_contDiffOn_open, HasWeightedApproximateTangentSpaceAt.unique, Lipschitz area formulas on Euclidean domains (area_formula_lipschitzOn_multiplicity, weighted_area_formula_lipschitzOn_fiberSum, injective_area_formula_lipschitzOn, aemeasurable_weightedAreaFiberSum_lipschitzOn), areaJacobian_comp_eq_parametrization_mul_tangential, rademacher_ae_differentiableAt, Whitney C¹ extension (exists_contDiff_one_extension_of_whitney / HasWhitneyC1Compatibility), density theorems simon_theorem_3_3, simon_theorem_3_6, simon_remark_3_7_of_openSigmaFinite, vector Riesz representation simon_theorem_4_14, real-valued Lusin exists_isClosed_continuousOn_of_measurable, IsLocallyBV and euclideanDivergence; Mathlib LinearMap.normDet_comp, Besicovitch.vitaliFamily with VitaliFamily.ae_tendsto_average_norm_sub and Besicovitch.ae_tendsto_rnDeriv, MeasureTheory.tendstoUniformlyOn_of_ae_tendsto (Egorov), Vitali.exists_disjoint_covering_ae, Haar measure on locally compact groups, eLpNorm_le_eLpNorm_fderiv_of_eq (Gagliardo-Nirenberg-Sobolev), EuclideanSpace.euclideanHausdorffMeasure_eq_volume, ENNReal.tsum_set_one. No match (hence supplied as shared children or proved inside children): no C¹ approximation theorem and no coarea formula beyond the linear case in SimonGMT; Mathlib has no coarea formula, no countable rectifiability, no Kirszbraun theorem, no Whitney C¹ extension (only manifold embeddings), no Lusin continuity theorem (only Lusin separation/Lusin-Souslin), no measure on Grassmannians (RingTheory/Grassmannian.lean is algebraic), no BV compactness; neither library has the Besicovitch-Federer theorem or De Giorgi's theorem. SimonGMT's Chapter03 tangentialDifferential/tangentialJacobian (Differential.lean) are not used, as the README marks them unfaithful.
