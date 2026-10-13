# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.eilenberg_inequality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Ch. 2, Theorem 1.8(ii) (k = 0 case) and Theorem 1.9 with Remark 1.10 (upper Lebesgue integral), chapter-02.txt lines 270-333 (1.8) and 335-400 (1.9, its proof lines 366-400), printed pp. 44-46. Simon proves exactly the upper-integral inequality below (lines 366-397); his additional measurability assertion is not needed here and is not claimed. Constants: we do not use the isodiametric inequality (Simon's sharp constant ω_mω_k/ω_{m+k}); any constant C(m, k) suffices.

Notation. ℝ^d = EuclideanSpace ℝ (Fin d); for s ≥ 0, Hˢ = μHE[s] on ℝ^N. Mathlib's μHE[s] equals c_s·μH[s], where μH[s] = sup_{δ>0} μH[s]_δ is the Hausdorff measure built from covers by sets of diameter ≤ δ with cost diam^s (cost 1 for every nonempty set when s = 0; H⁰ is counting measure). Write H^s_δ(S) := inf{Σᵢ c_s (diam Cᵢ)^s : S ⊆ ⋃ᵢ Cᵢ, diam Cᵢ ≤ δ}, so H^s_δ ↑ Hˢ as δ ↓ 0 and covers may be taken by closed sets (diam C̄ = diam C). λₘ = volume (Lebesgue measure) on ℝᵐ; ωₘ := λₘ(B_1(0)) (ω₀ = 1). The Lipschitz constant is L and Lᵐ below always means its m-th power.

Statement. For N, m, k ∈ ℕ there is C ≥ 0 such that for all A ⊆ ℝ^N, L ≥ 0 and L-Lipschitz f : ℝ^N → ℝᵐ there is a Borel g : ℝᵐ → [0, ∞] with Hᵏ(A ∩ f⁻¹{y}) ≤ g(y) for all y and ∫ g dλₘ ≤ C·Lᵐ·H^{m+k}(A).

Proof. Put C := ωₘ·c_k / c_{m+k} (positive; for m = 0 this is 1).

1. Elementary volume bound. For S ⊆ ℝᵐ nonempty, S ⊆ B̄_{diam S}(s₀) for any s₀ ∈ S, hence λₘ(S̄) ≤ ωₘ (diam S)ᵐ (for m = 0, λ₀ is the unit point mass and the bound reads 1 ≤ 1). If f is L-Lipschitz and C ⊆ ℝ^N then diam f(C) ≤ L diam C, so λₘ(closure f(C)) ≤ ωₘ Lᵐ (diam C)ᵐ.

2. Case L = 0. Then f ≡ y₀ is constant and A ∩ f⁻¹{y} is A for y = y₀ and ∅ otherwise. Take g := Hᵏ(A)·1_{{y₀}} (Borel). If m ≥ 1 then ∫ g dλₘ = Hᵏ(A)·λₘ({y₀}) = 0 (with ∞·0 = 0). If m = 0 then ∫ g = Hᵏ(A) = C·L⁰·H^{0+k}(A) (C = 1, L⁰ = 1). Assume L > 0.

3. Case H^{m+k}(A) = ∞. Take g :≡ ∞; then ∫ g ≤ ∞ = C·Lᵐ·H^{m+k}(A) since C > 0, L > 0. Assume H^{m+k}(A) < ∞.

4. Covers (Simon (1), lines 366-369). For each i ≥ 1 choose closed sets C_{i1}, C_{i2}, … with A ⊆ ⋃ⱼ C_{ij}, diam C_{ij} ≤ 1/i, and Σⱼ c_{m+k}(diam C_{ij})^{m+k} ≤ H^{m+k}_{1/i}(A) + 1/i (discard empty sets). Define the Borel simple-type functions (Simon lines 369-372)
 gᵢ(y) := Σⱼ c_k (diam C_{ij})^k · 1_{K_{ij}}(y), K_{ij} := closure of f(C_{ij}) (closed, hence Borel).
 (For k = 0 the coefficient is c₀·1.)

5. Pointwise bound (Simon (2), lines 373-377). Fix y. A ∩ f⁻¹{y} ⊆ ⋃_{j : y ∈ f(C_{ij})} C_{ij}, a cover by sets of diameter ≤ 1/i, so H^k_{1/i}(A ∩ f⁻¹{y}) ≤ Σ_{j : y ∈ f(C_{ij})} c_k (diam C_{ij})^k ≤ gᵢ(y).

6. Integral bound (Simon lines 377-385). By monotone convergence and Step 1,
 ∫ gᵢ dλₘ = Σⱼ c_k (diam C_{ij})^k λₘ(K_{ij}) ≤ Σⱼ c_k ωₘ Lᵐ (diam C_{ij})^{m+k} = C Lᵐ Σⱼ c_{m+k}(diam C_{ij})^{m+k} ≤ C Lᵐ (H^{m+k}_{1/i}(A) + 1/i).

7. Limit (Simon lines 385-393; Remark 1.10). Let g := liminf_{i→∞} gᵢ (Borel). For every y, Hᵏ(A ∩ f⁻¹{y}) = lim_i H^k_{1/i}(A ∩ f⁻¹{y}) ≤ liminf_i gᵢ(y) = g(y) by Step 5. By Fatou's lemma and Step 6, ∫ g dλₘ ≤ liminf_i ∫ gᵢ ≤ liminf_i C Lᵐ (H^{m+k}_{1/i}(A) + 1/i) ≤ C Lᵐ H^{m+k}(A), because H^{m+k}_{1/i}(A) ≤ H^{m+k}(A). ∎

Remarks. (i) No measurability of A is used (Simon's proof of the inequality uses only covers; his measurability hypothesis serves the separate measurability assertion, which is not part of this statement). (ii) Consequences used by siblings: if H^{m+k}(A) = 0 then Hᵏ(A ∩ f⁻¹{y}) = 0 for λₘ-a.e. y (g = 0 a.e.); if H^{m+k}(A) < ∞ then Hᵏ(A ∩ f⁻¹{y}) < ∞ for λₘ-a.e. y (g < ∞ a.e.).

## Key steps

1. Choose C := ωₘc_k/c_{m+k}; treat L = 0 (f constant) and H^{m+k}(A) = ∞ directly.
2. For each i cover A by closed sets C_{ij} of diameter ≤ 1/i nearly realizing H^{m+k}_{1/i}(A).
3. Define Borel gᵢ := Σⱼ c_k(diam C_{ij})^k 1_{closure f(C_{ij})}; then H^k_{1/i}(A ∩ f⁻¹{y}) ≤ gᵢ(y).
4. Bound ∫gᵢ using Lᵐ(closure f(C)) ≤ ωₘ(L diam C)ᵐ.
5. g := liminf gᵢ; Fatou gives ∫g ≤ C L^m H^{m+k}(A), and Hᵏ = lim H^k_{1/i} gives the pointwise bound.

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
