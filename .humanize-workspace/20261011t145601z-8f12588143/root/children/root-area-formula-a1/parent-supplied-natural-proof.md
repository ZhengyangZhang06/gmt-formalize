# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.area_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Ch. 3, (2.1)-(2.6), chapter-03.txt lines 327-409 (printed pp. 75-77): Definitions 2.1-2.3, the area formula 2.4 with its proof (lines 370-396) and 2.5 (lines 397-401). Erratum (README, contract docstring): the outer integrals are over the target ℝ^{n+ℓ₁} (printed ℝ^{n+ℓ} in 2.4/2.5 and ℝⁿ in the display on line 388). Departure: Simon's written proof (lines 377-396) replaces f on M_j by C¹ functions g_j (C¹ approximation) and applies the smooth area formula 3.4 of Ch. 2 on N_j; we follow instead the route Simon states just before it (lines 370-371: “In view of 4.11 and the area formula for Lipschitz maps from domains in ℝⁿ, as discussed in §3, we have the general area formula”), i.e. the Lipschitz area formula on parameter domains plus the Jacobian chain rule (4.11) of Ch. 2; this avoids extending C¹ functions off the submanifolds. The identification T_xM = T_xN_j a.e. (Remark 1.5(2), line 348) and the tangential differential (Ch. 2 (4.8)-(4.10)) are supplied by the sibling chart_tangent_differential.

Notation. N = n + ℓ, P := n + ℓ₁ (target dimension), ℝ^d = EuclideanSpace ℝ (Fin d), Hⁿ = μHE[n] on ℝ^N and on ℝ^P, Lⁿ = volume on ℝⁿ. For x ∈ M: T_xM := approxTangentPlane n M θ x, d^Mf_x := tangentialDifferential T_xM f x, J^M_f(x) := areaJacobian T_xM f x = normDet(d^Mf_x). #S := S.encard ∈ [0, ∞] (H⁰ = counting measure). For a C¹ map ψ, Jψ(u) := normDet(Dψ(u)).

Statement. AreaFormula: for M Hⁿ-measurable and countably n-rectifiable, θ a positive locally integrable weight on M, U ⊇ M open, f locally Lipschitz on U: (a) for Hⁿ-a.e. x ∈ M there are P and L : P →L ℝ^P with HasWeightedApproximateTangentSpaceAt n M θ x P and HasTangentialDifferentialAt P f x L; (b) ∫_A J^M_f dHⁿ = ∫_{ℝ^P} #(A ∩ f⁻¹{y}) dHⁿ(y) for every Hⁿ-measurable A ⊆ M; (c) ∫_M h·J^M_f dHⁿ = ∫_{ℝ^P} Σ_{x∈M∩f⁻¹{y}} h(x) dHⁿ(y) for every Hⁿ⌞M-measurable h : ℝ^N → [0, ∞].

Proof.

1. Good chart balls. By the sibling submanifold_cover (Lemma 1.2), M ⊆ N₀ ∪ ⋃_j N_j with Hⁿ(N₀) = 0 and IsC1Submanifold n N_j, and (Lindelöf, as the chart targets W are open and ℝ^N is second countable) each N_j is a countable union of chart images ψ(V), with V ⊆ ℝⁿ open, ψ C¹ and injective on V, Dψ(u) injective for u ∈ V. For such a chart and u ∈ V with ψ(u) ∈ U, choose a closed ball D = B̄_r(u) ⊆ V such that (i) ψ is bi-Lipschitz on D (if n = 0 then D = {u} = ℝ⁰ and (i) is vacuous; otherwise): with c := min_{|v|=1}|Dψ(u)v| > 0 and r so small that ‖Dψ(z) − Dψ(u)‖ ≤ c/2 on D, the mean value inequality gives (c/2)|z − z'| ≤ |ψ(z) − ψ(z')| ≤ (‖Dψ(u)‖ + c/2)|z − z'|; (ii) ψ(D) ⊆ B_s(ψ(u)) ⊆ U where f is Lipschitz on B_s(ψ(u)) (f is locally Lipschitz on the open U). The open set V ∩ ψ⁻¹(U) is covered by the interiors of such balls, hence by countably many of them (Lindelöf). Collecting over all charts we obtain countably many pairs (ψ_α, D_α), α ∈ ℕ (pad with D_α = ∅ if needed), with: ψ_α C¹ on an open set containing the compact ball D_α, injective and bi-Lipschitz on D_α, Dψ_α(z) injective on D_α, h_α := f∘ψ_α Lipschitz on D_α, and M ⊆ N₀ ∪ ⋃_α ψ_α(int D_α) (every x ∈ M ∖ N₀ is ψ(u) for a chart with ψ(u) = x ∈ M ⊆ U).

2. Pointwise identification (Simon (2.1)-(2.3), lines 337-370; Ch. 2 (4.11)). Apply the sibling chart_tangent_differential to (M, U, θ, f) and the chart underlying α (V open, ψ C¹ on V, Dψ injective on V). It gives an Lⁿ-null Z_α such that every u ∈ D_α ∖ Z_α with x := ψ_α(u) ∈ M satisfies: (A) HasWeightedApproximateTangentSpaceAt n M θ x T_u, T_u := range Dψ_α(u); (B) h_α is differentiable at u; (C) HasLineDerivAt ℝ f (Dh_α(u)w) x (Dψ_α(u)w) for all w. Consequences at such u:
 (a') T_xM = T_u: the predicate ∃P, HasWeightedApproximateTangentSpaceAt n M θ x P holds, so approxTangentPlane chooses some P' with this property, and P' = T_u by uniqueness (SimonGMT HasWeightedApproximateTangentSpaceAt.unique, applicable as θ(x) > 0 for x ∈ M).
 (b') Let L_x : T_u → ℝ^P be the linear map L_x(Dψ_α(u)w) := Dh_α(u)w (well defined: Dψ_α(u) : ℝⁿ → T_u is a linear isomorphism; continuous as T_u is finite dimensional). By (C), HasTangentialDifferentialAt T_u f x L_x. Line derivatives are unique, so every L' with HasTangentialDifferentialAt T_u f x L' equals L_x; hence d^Mf_x = tangentialDifferential T_u f x = L_x.
 (c') Jacobian chain rule (Simon Ch. 2 (4.11)): Dh_α(u) = L_x ∘ Dψ_α(u), so by Mathlib LinearMap.normDet_comp (equivalently SimonGMT Chapter02.areaJacobian_comp_eq_parametrization_mul_tangential, with any linear extension of L_x to ℝ^N), normDet(Dh_α(u)) = normDet(L_x)·normDet(Dψ_α(u)), i.e. Jh_α(u) = J^M_f(ψ_α(u))·Jψ_α(u).
 Conclusion (a): the set N₀ ∪ ⋃_α ψ_α(Z_α ∩ D_α) is Hⁿ-null (ψ_α is Lipschitz on D_α, and Lⁿ = Hⁿ on ℝⁿ by EuclideanSpace.euclideanHausdorffMeasure_eq_volume); every x ∈ M outside it is ψ_α(u) with u ∈ int D_α ∖ Z_α, and P := T_u, L := L_x satisfy (a).

3. Decomposition of A. Let A ⊆ M be Hⁿ-measurable. Put A_α := (A ∩ ψ_α(D_α)) ∖ ⋃_{β<α} ψ_β(D_β) and A_∞ := A ∖ ⋃_α ψ_α(D_α) ⊆ N₀. The A_α are pairwise disjoint and Hⁿ-measurable (the ψ_β(D_β) are compact), A = A_∞ ⊔ ⨆_α A_α, Hⁿ(A_∞) = 0. Let B_α := D_α ∩ ψ_α⁻¹(A_α); ψ_α : B_α → A_α is a bijection, and B_α is Lⁿ-measurable (A_α is a Borel set plus an Hⁿ-null set; ψ_α|D_α is a bi-Lipschitz homeomorphism onto a compact set, so preimages of Borel sets are Borel and of Hⁿ-null sets are Lⁿ-null).

4. Measurability of J^M_f. By (c'), for u ∈ B_α ∖ Z_α: J^M_f(ψ_α(u)) = Jh_α(u)/Jψ_α(u), and the right side is an Lⁿ-measurable function on B_α (u ↦ Dh_α(u) is measurable where defined, Mathlib measurable_fderiv; Jψ_α is continuous and positive on D_α). Transporting by the bi-Lipschitz ψ_α, J^M_f agrees Hⁿ-a.e. on A_α with a Borel function; hence J^M_f is Hⁿ⌞A-measurable (A_∞ is null).

5. One piece (Simon lines 385-390). The area formula for the Lipschitz map h_α on the Lⁿ-measurable set B_α (Simon Ch. 2 (3.4); SimonGMT Chapter02.area_formula_lipschitzOn_multiplicity, whose Jacobian is normDet of the derivative within B_α, equal to Jh_α(u) at Lⁿ-a.e. u ∈ B_α) gives ∫_{ℝ^P} #(B_α ∩ h_α⁻¹{y}) dHⁿ(y) = ∫_{B_α} Jh_α dLⁿ. Since ψ_α : B_α → A_α is bijective and h_α = f∘ψ_α, #(B_α ∩ h_α⁻¹{y}) = #(A_α ∩ f⁻¹{y}) (SimonGMT's multiplicity is a tsum of 1 over the fibre, equal to encard by ENNReal.tsum_set_one). The injective weighted area formula for ψ_α on B_α (Simon Ch. 2 (4.13); SimonGMT Chapter02.weighted_area_formula_lipschitzOn_fiberSum, each fibre of the injective ψ_α having at most one point) gives ∫_{A_α} w dHⁿ = ∫_{B_α} w(ψ_α(u)) Jψ_α(u) du for Hⁿ⌞A_α-measurable w ≥ 0. With w = J^M_f (Step 4) and (c'):
 ∫_{A_α} J^M_f dHⁿ = ∫_{B_α} J^M_f(ψ_α u) Jψ_α(u) du = ∫_{B_α} Jh_α du = ∫_{ℝ^P} #(A_α ∩ f⁻¹{y}) dHⁿ(y).

6. Summation, (2.4) (Simon lines 393-396). Countable additivity of the integral over the disjoint measurable A_α (A_∞ null) and monotone convergence (Mathlib lintegral_tsum; each y ↦ #(A_α ∩ f⁻¹{y}) = #(B_α ∩ h_α⁻¹{y}) is Hⁿ-a.e. measurable by SimonGMT aemeasurable_weightedAreaFiberSum_lipschitzOn, i.e. Simon Ch. 2, 1.8(ii)) give
 ∫_A J^M_f dHⁿ = Σ_α ∫ #(A_α ∩ f⁻¹{y}) dHⁿ(y) = ∫ Σ_α #(A_α ∩ f⁻¹{y}) dHⁿ(y) = ∫ #((A ∖ A_∞) ∩ f⁻¹{y}) dHⁿ(y),
 using additivity of encard over the disjoint union. Finally #(A ∩ f⁻¹{y}) = #((A ∖ A_∞) ∩ f⁻¹{y}) unless y ∈ f(A_∞), and Hⁿ(f(A_∞)) = 0 because A_∞ ⊆ U is Hⁿ-null and f is locally Lipschitz on U (Simon line 395, “the (easily checked) fact”: cover U by countably many balls on which f is Lipschitz). So the two integrands agree Hⁿ-a.e., proving (b).

7. Formula (2.5) (Simon lines 397-401). Let h : ℝ^N → [0, ∞] be Hⁿ⌞M-measurable. Take A := M in Step 3 (M_α, B_α). For each α, w_α(u) := h(ψ_α(u)) is Lⁿ⌞B_α-measurable (ψ_α bi-Lipschitz). The weighted fibre-sum area formula for h_α on B_α (Simon Ch. 2 (3.5); SimonGMT weighted_area_formula_lipschitzOn_fiberSum) and Steps 2, 5 give
 ∫_{ℝ^P} Σ_{u∈B_α∩h_α⁻¹{y}} h(ψ_α u) dHⁿ(y) = ∫_{B_α} Jh_α(u) h(ψ_α u) du = ∫_{B_α} h(ψ_α u) J^M_f(ψ_α u) Jψ_α(u) du = ∫_{M_α} h·J^M_f dHⁿ,
 and Σ_{u∈B_α∩h_α⁻¹{y}} h(ψ_α u) = Σ_{x∈M_α∩f⁻¹{y}} h(x); each of these fibre sums is an Hⁿ-a.e. measurable function of y (SimonGMT aemeasurable_weightedAreaFiberSum_lipschitzOn), as needed for monotone convergence. Summing over α (monotone convergence; [0,∞]-valued sums over the disjoint pieces M_α ∩ f⁻¹{y} add up to the sum over (M ∖ M_∞) ∩ f⁻¹{y}), and discarding M_∞ as in Step 6 (both sides: M_∞ is Hⁿ-null and Hⁿ(f(M_∞)) = 0), we get ∫_M h·J^M_f dHⁿ = ∫_{ℝ^P} Σ_{x∈M∩f⁻¹{y}} h(x) dHⁿ(y), which is (c). ∎

## Key steps

1. Lemma 1.2 (sibling) + Lindelöf: countably many good chart balls (ψ_α, D_α), ψ_α bi-Lipschitz, f∘ψ_α Lipschitz, covering M up to an Hⁿ-null set.
2. Sibling chart lemma: at a.e. parameter, T_xM = range Dψ_α(u) (uniqueness), d^Mf_x∘Dψ_α(u) = D(f∘ψ_α)(u) (uniqueness of line derivatives); this gives (a).
3. Jacobian chain rule (Simon (4.11), Mathlib normDet_comp): J(f∘ψ_α) = J^M_f∘ψ_α · Jψ_α; measurability of J^M_f.
4. Disjoint decomposition of A into pieces A_α = ψ_α(B_α) plus an Hⁿ-null set.
5. On each piece: SimonGMT Lipschitz area formula for f∘ψ_α and injective weighted area formula for ψ_α.
6. Sum over α (monotone convergence, additivity of encard); the null piece has Hⁿ-null image; weighted version gives (c).

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
