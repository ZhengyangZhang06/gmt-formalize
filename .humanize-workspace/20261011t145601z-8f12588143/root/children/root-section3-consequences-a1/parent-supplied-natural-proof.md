# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.section3_consequences-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Ch. 3, Lemma 3.2 (chapter-03.txt lines 449-469, printed p. 78), Lemma 3.3 (lines 476-496, printed pp. 78-79) and Theorem 3.8 (lines 540-548, printed p. 80). Errata: Definition 3.1 (line 446) “if P contains” should read “if S contains” (as encoded by PurelyUnrectifiable); line 540 “by combining 3.2 and 3.7” should read “by combining 3.2 and 3.6” — Remark 3.7 is the converse direction (via Lemma 3.3), whereas the proof of 3.8 uses the null-projection theorem 3.6, supplied by the sibling besicovitch_federer.

Notation. N := n + ℓ, ℝ^d = EuclideanSpace ℝ (Fin d), Hⁿ = μHE[n], Lⁿ = volume = Hⁿ on ℝⁿ; coordinateProjection J is the orthogonal projection of ℝ^N onto span{e_j : j ∈ J}.

Statement. RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ RectifiabilityTheoremForSets.

Part 1: Lemma 3.2 (RectifiableDecomposition).
1. Let A = ⋃ⱼ Aⱼ with Hⁿ(Aⱼ) < ∞. SimonGMT Poincare.SimonGMT.Chapter03.simon_lemma_3_2 (Chapter03/Rectifiable.lean), applied with the cover S := (Aⱼ)ⱼ (A ⊆ ⋃ⱼ Aⱼ, Hⁿ(Aⱼ) < ∞), gives exactly the first conclusion (A = R ∪ P, Disjoint R P, R countably n-rectifiable, P purely n-unrectifiable) and, if A is Hⁿ-null-measurable, a decomposition with additionally MeasurableSet R (and NullMeasurableSet P, which we drop). That Lean proof implements Simon's argument (lines 455-469): reduce to the measurable case via Borel hulls of the Aⱼ; maximize Hⁿ over Borel countably rectifiable subsets (σ-finiteness of Hⁿ⌞A) to get a Borel countably rectifiable R capturing, up to Hⁿ-null sets, every rectifiable subset of A; then A ∖ R is purely unrectifiable.

Part 2: Lemma 3.3 (CoordinateProjectionCriterion), Simon lines 482-496.
2. Case n = 0. For J = ∅, coordinateProjection ∅ is the zero map, so coordinateProjection ∅ '' S = {0} if S ≠ ∅, of H⁰-measure 1. The hypothesis therefore forces S = ∅, which is purely 0-unrectifiable. Assume n ≥ 1.
3. Linear algebra (Simon lines 482-489). If L ⊆ ℝ^N is an n-dimensional subspace, there is J ⊆ {1, …, N} with #J = n such that coordinateProjection J restricted to L is a linear isomorphism onto span{e_j : j ∈ J}. Proof: the coordinate functionals x ↦ x_j restricted to L span the dual space L* (a nonzero x ∈ L has some nonzero coordinate), which has dimension n, so n of them, indexed by some J, form a basis of L*; then x ↦ (x_j)_{j∈J} is injective on L, i.e. coordinateProjection J (x ↦ Σ_{j∈J} x_j e_j) is injective on L, and both spaces have dimension n. (This is SimonGMT Chapter03/CoordinateProjection.lean, exists_bijective_selectedCoordinateMap, which returns an injective j : Fin n → Fin N with selectedCoordinateMap L j bijective; take J := Finset.univ.image j, of cardinality n since j is injective. That file is not imported by the contract, but its short proof can be reproduced.)
4. Suppose S is not purely n-unrectifiable: there is R ⊆ S countably n-rectifiable with Hⁿ(R) > 0. By the sibling submanifold_cover (Lemma 1.2, “⇒”), R ⊆ N₀ ∪ ⋃ⱼ Nⱼ with Hⁿ(N₀) = 0 and IsC1Submanifold n Nⱼ; by countable subadditivity Hⁿ(R ∩ N) > 0 for N := Nⱼ, some j (Simon lines 490-491). N is a countable union of chart images ψ(V) (V ⊆ ℝⁿ open, ψ C¹ with injective derivative; Lindelöf), and V is a countable union of closed balls D on which ψ is bi-Lipschitz (choose D = B̄_r(u) with ‖Dψ − Dψ(u)‖ ≤ c/2 on D, c := min_{|v|=1}|Dψ(u)v|, and use the mean value inequality). So some chart and ball have Hⁿ(R ∩ ψ(D)) > 0. Let T' := D ∩ ψ⁻¹(R); then Lⁿ(T') > 0 (outer measure), since Hⁿ(R ∩ ψ(D)) = Hⁿ(ψ(T')) ≤ Lip(ψ|D)ⁿ Lⁿ(T'). There is u₀ ∈ T' with Lⁿ(T' ∩ B(u₀, ρ)) > 0 for every ρ > 0 (otherwise T' is covered by countably many Lⁿ-null balls; Simon line 492: “there must be some x ∈ S ∩ N with Hⁿ(S ∩ N ∩ B_ρ(x)) > 0 for all ρ > 0”).
5. Local diffeomorphism (Simon lines 493-496, via Ch. 2, Remark 4.4). Let L := range Dψ(u₀) (n-dimensional), J as in Step 3, and ι_J : ℝⁿ → span{e_j : j ∈ J} a linear isometry. Φ := ι_J⁻¹ ∘ coordinateProjection J ∘ ψ is C¹ near u₀ with DΦ(u₀) = ι_J⁻¹ ∘ coordinateProjection J ∘ Dψ(u₀), a linear isomorphism of ℝⁿ. By the mean value inequality (as in Step 4; the inverse function theorem is not needed) there are ρ > 0 and c > 0 with B(u₀, ρ) ⊆ V and |Φ(u) − Φ(u')| ≥ c|u − u'| for u, u' ∈ B(u₀, ρ). Hence Lⁿ(T' ∩ B(u₀, ρ)) ≤ c^{-n} Hⁿ(Φ(T' ∩ B(u₀, ρ))) (Φ⁻¹ is c⁻¹-Lipschitz on the image), and since ι_J is an isometry and ψ(T') ⊆ R ⊆ S:
 Hⁿ(coordinateProjection J '' S) ≥ Hⁿ(coordinateProjection J (ψ(T' ∩ B(u₀, ρ)))) = Hⁿ(Φ(T' ∩ B(u₀, ρ))) ≥ cⁿ Lⁿ(T' ∩ B(u₀, ρ)) > 0,
 contradicting the hypothesis (#J = n). Hence S is purely n-unrectifiable.

Part 3: Theorem 3.8 (RectifiabilityTheoremForSets), Simon lines 540-548 (with the erratum above).
6. Let A = ⋃ⱼ Aⱼ, Hⁿ(Aⱼ) < ∞, and assume every B ⊆ A with Hⁿ(B) > 0 satisfies ¬ForAlmostAllProjections (n+ℓ) n (fun p ↦ Hⁿ(p '' B) = 0). By Part 1, A = R ∪ P with R countably n-rectifiable and P purely n-unrectifiable. P ⊆ A and P = ⋃ⱼ (P ∩ Aⱼ) with Hⁿ(P ∩ Aⱼ) ≤ Hⁿ(Aⱼ) < ∞, so the sibling besicovitch_federer (Theorem 3.6) gives ForAlmostAllProjections (n+ℓ) n (fun p ↦ Hⁿ(p '' P) = 0). If Hⁿ(P) > 0, the hypothesis applied to B := P contradicts this; hence Hⁿ(P) = 0. Then P is countably n-rectifiable (SimonGMT countablyRectifiable_of_measure_zero) and A = R ∪ P is countably n-rectifiable (countablyRectifiable_iUnion with the two-member family, or directly: if R ⊆ R₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ) then A ⊆ (R₀ ∪ P) ∪ ⋃ⱼ Fⱼ(ℝⁿ) with Hⁿ(R₀ ∪ P) = 0). ∎

## Key steps

1. 3.2: SimonGMT simon_lemma_3_2 with the cover (Aⱼ).
2. 3.3, n = 0: the hypothesis forces S = ∅.
3. 3.3 linear algebra: every n-plane is mapped isomorphically by some coordinate projection.
4. 3.3: a rectifiable subset of positive measure meets some C¹ chart (Lemma 1.2 sibling) in a set with a parameter density point u₀; near u₀ the coordinate projection composed with the chart is bi-Lipschitz, so the projection of S has positive measure.
5. 3.8: decompose A = R ∪ P by 3.2; Besicovitch-Federer (sibling) gives null projections of P a.e., so Hⁿ(P) = 0 by hypothesis and A is countably rectifiable.

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
