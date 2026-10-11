# Chapter 3 — Countably n-Rectifiable Sets (Simon, printed pp. 69–84)

Frozen contract: `GMT/Ch03/Contract.lean` (namespace `GMT.Ch03`), final theorem
`GMT.Ch03.main_theorem`, a conjunction of the 12 Props below. `GMT/Ch03/Submission.lean` is a
byte copy for the prover.

Conventions: `Rn N = EuclideanSpace ℝ (Fin N)`; `Hⁿ = μHE[n]` (Mathlib's Euclidean Hausdorff
measure, equal to Simon's `ω_n (diam/2)^n` normalization; on arbitrary sets it is the outer
measure); `Lᵐ = volume`; "`Hⁿ`-measurable" = `NullMeasurableSet · μHE[n]`; "`Hⁿ`-a.e. `x ∈ M`" =
`∀ᵐ x ∂μHE[n], x ∈ M → …`; `B_ρ(x)` = open ball; `η_{x,λ}(y) = λ⁻¹(y − x)` = SimonGMT `blowUpMap`.

## Statement map

| # | Book item (page) | Lean name | Existing SimonGMT support |
|---|---|---|---|
| 1 | Lemma 1.2 (p. 69) | `SubmanifoldCoverCharacterization` | "⇐" proved: `Chapter03.countablyRectifiable_of_submanifold_cover` (Chapter03/SubmanifoldCover.lean); "⇒" new |
| 2 | Theorem 1.6 (p. 71) | `ApproximateTangentCharacterization` | new |
| 3 | Theorem 1.9 (p. 75) | `WeightedApproximateTangentCharacterization` | new |
| 4 | Area formula 2.4–2.5 (pp. 76–77) | `AreaFormula` | new |
| 5 | Co-area formula 2.8–2.9 (p. 77) | `CoareaFormula` | new |
| 6 | Remark 2.10(2) (p. 77) | `SlicesAreRectifiable` | new |
| 7 | Lemma 3.2 (p. 78) | `RectifiableDecomposition` | proved: `Chapter03.simon_lemma_3_2` (Chapter03/Rectifiable.lean) |
| 8 | Lemma 3.3 (p. 78) | `CoordinateProjectionCriterion` | new |
| 9 | Theorem 3.6 (p. 80) | `BesicovitchFedererProjectionTheorem` | new |
| 10 | Theorem 3.8 (p. 80) | `RectifiabilityTheoremForSets` | new |
| 11 | (4.1) (p. 80) | `GaussGreenRepresentation` | new |
| 12 | Theorem 4.3 (p. 81) | `DeGiorgiTheorem` | new |

### 1. `SubmanifoldCoverCharacterization` — Lemma 1.2
For all `n ℓ` and `M ⊆ ℝ^{n+ℓ}`: `CountablyRectifiable n M ↔ ∃ N₀ N, Hⁿ(N₀) = 0 ∧
(∀ j, IsC1Submanifold n (N j)) ∧ M ⊆ N₀ ∪ ⋃ⱼ N j`. No hypotheses. Existing: the "⇐" direction is
`Poincare.SimonGMT.Chapter03.countablyRectifiable_of_submanifold_cover` for
`Chapter02.IsSimonSubmanifold (E := Rn n) 1`, which unfolds to the same predicate as
`IsC1Submanifold n` (same seven conditions, reordered, plus the trivially true `1 ≤ 1`). Also
useful: `countablyRectifiable_of_isSimonSubmanifold`, `measurableSet_of_isSimonSubmanifold`.
"⇒" needs the C¹ approximation theorem (Ch. 2, 1.5), which is missing in SimonGMT.

### 2. `ApproximateTangentCharacterization` — Theorem 1.6
Hypotheses: `M` is `Hⁿ`-measurable and `Hⁿ(M ∩ K) < ∞` for all compact `K`. Conclusion:
`CountablyRectifiable n M ↔` for `Hⁿ`-a.e. `x ∈ M` there is `P` with
`HasApproximateTangentSpaceAt n M x P` (Def. 1.4). Supporting SimonGMT facts:
`HasApproximateTangentSpaceAt.unique`, `hasApproximateTangentSpaceAt_submodule`
(Chapter03/Rectifiable.lean); upper density theorem `Chapter01.simon_theorem_3_6`
(Chapter01/DensityComparison.lean); Remark 1.3 `Chapter03.simon_remark_1_3_nullMeasurable`
(Chapter03/DisjointCover.lean); Lusin `IsBorelRegularOuterMeasure.simon_theorem_1_17`.

### 3. `WeightedApproximateTangentCharacterization` — Theorem 1.9
Hypotheses: `M` `Hⁿ`-measurable, `IsPositiveLocallyIntegrableWeight n M θ` (θ > 0 on `M`,
`Hⁿ⌞M`-measurable, `∫_{M∩K} θ dHⁿ < ∞` for compact `K`). Conclusion: `CountablyRectifiable n M ↔`
for `Hⁿ`-a.e. `x ∈ M` there is `P` with `HasWeightedApproximateTangentSpaceAt n M θ x P`
(Def. 1.7). Supporting: `HasWeightedApproximateTangentSpaceAt.unique` (Rectifiable.lean).

### 4. `AreaFormula` — (2.4), (2.5)
Hypotheses: `M ⊆ ℝ^{n+ℓ}` `Hⁿ`-measurable and countably `n`-rectifiable; `θ` a positive locally
`Hⁿ`-integrable weight on `M` (only used to name `T_x M`, see below); `U ⊇ M` open;
`f : ℝ^{n+ℓ} → ℝ^{n+ℓ₁}` locally Lipschitz on `U`. Conclusions: (a) for `Hⁿ`-a.e. `x ∈ M`, the
approximate tangent space `T_x M` (Def. 1.7) and `d^M f_x : T_x M → ℝ^{n+ℓ₁}` exist;
(b) (2.4) `∫_A J^M_f dHⁿ = ∫ H⁰(A ∩ f⁻¹(y)) dHⁿ(y)` for every `Hⁿ`-measurable `A ⊆ M`
(`H⁰` = `Set.encard`); (c) (2.5) `∫_M h J^M_f dHⁿ = ∫ ∑_{x ∈ M ∩ f⁻¹(y)} h(x) dHⁿ(y)` for every
`Hⁿ⌞M`-measurable `h : ℝ^{n+ℓ} → [0, ∞]`. `J^M_f(x) = areaJacobian (approxTangentPlane n M θ x) f x`.
Erratum: the outer integral is over the target `ℝ^{n+ℓ₁}` (printed `ℝ^{n+ℓ}`). Existing related
results (Lipschitz maps on Euclidean domains, Ch. 2 3.4/3.5):
`Chapter02.area_formula_lipschitzOn_multiplicity`,
`Chapter02.weighted_area_formula_lipschitzOn_fiberSum_simon_hausdorffWeight` (Chapter02/AreaDomain.lean),
`Chapter02.rademacher_ae_differentiableAt` (Chapter02/Lipschitz.lean). SimonGMT's
`Chapter03.tangentialDifferential/tangentialJacobian` (Chapter03/Differential.lean) are **not**
reused: they restrict the *ambient* Fréchet derivative, which generally does not exist on `M` for
Lipschitz `f` (it is then `0`), so they differ from Simon's `d^M f_x`.

### 5. `CoareaFormula` — (2.8), (2.9)
Hypotheses: `n = m + k` with `0 < k` (Simon's `m < n`); `M ⊆ ℝ^{n+ℓ}` `Hⁿ`-measurable and
countably `n`-rectifiable; `θ` as in 4; `U ⊇ M` open; `f : ℝ^{n+ℓ} → ℝᵐ` locally Lipschitz on `U`.
Conclusions: (a) a.e. existence as in 4; (b) (2.8) `∫_A J^{M*}_f dHⁿ = ∫_{ℝᵐ} Hᵏ(A ∩ f⁻¹(y)) dLᵐ(y)`;
(c) (2.9) `∫_A g J^{M*}_f dHⁿ = ∫_{ℝᵐ} ∫_{A ∩ f⁻¹(y)} g dHᵏ dLᵐ(y)` for `g ≥ 0` `Hⁿ⌞A`-measurable
(all `Hⁿ`-measurable `A ⊆ M`). `J^{M*}_f(x) = coareaJacobian (approxTangentPlane n M θ x) f x`.
Erratum: (2.9) is printed with `∫_A` on the left and `f⁻¹(y) ∩ M` on the right; stated with `A`
on both sides (taking `A = M` gives the printed reading for `g` defined on `M`). Existing related:
linear co-area `Chapter02.coarea_linear`, `Chapter02.coarea_linear_lintegral`
(Chapter02/CoareaLinear.lean).

### 6. `SlicesAreRectifiable` — Remark 2.10(2)
Same setting as 5 (without θ): for `Lᵐ`-a.e. `y ∈ ℝᵐ`, `M ∩ f⁻¹(y)` is countably
`k`-rectifiable. New.

### 7. `RectifiableDecomposition` — Lemma 3.2
Hypothesis: `A = ⋃ⱼ Aⱼ` with `Hⁿ(Aⱼ) < ∞` (no measurability). Conclusions: `A = R ∪ P`,
`Disjoint R P`, `R` countably `n`-rectifiable, `P` purely `n`-unrectifiable; and if `A` is
`Hⁿ`-measurable, the same with `R` Borel (`MeasurableSet R`). Existing:
`Poincare.SimonGMT.Chapter03.simon_lemma_3_2` (Rectifiable.lean), stated with a cover
`A ⊆ ⋃ⱼ Sⱼ`, `μHE[n] (Sⱼ) < ∞`, which the hypothesis here supplies (`Sⱼ = Aⱼ`).

### 8. `CoordinateProjectionCriterion` — Lemma 3.3
For `S ⊆ ℝ^{n+ℓ}`: if `Hⁿ(coordinateProjection J '' S) = 0` for every `J ⊆ {1,…,n+ℓ}` with
`#J = n` (`J` ↔ `j₁ < ⋯ < jₙ`), then `PurelyUnrectifiable n S`. New (SimonGMT's
Chapter03/CoordinateProjection.lean, containing the linear-algebra step, is not built/imported).

### 9. `BesicovitchFedererProjectionTheorem` — Theorem 3.6
Hypotheses: `Q` purely `n`-unrectifiable, `Q = ⋃ⱼ Qⱼ` with `Hⁿ(Qⱼ) < ∞`. Conclusion:
`ForAlmostAllProjections (n+ℓ) n (fun p ↦ Hⁿ(p(Q)) = 0)`. New.

### 10. `RectifiabilityTheoremForSets` — Theorem 3.8
Hypotheses: `A = ⋃ⱼ Aⱼ`, `Hⁿ(Aⱼ) < ∞`, and every `B ⊆ A` with `Hⁿ(B) > 0` satisfies
`¬ ForAlmostAllProjections (n+ℓ) n (fun p ↦ Hⁿ(p(B)) = 0)` ("`Hⁿ(p(B)) > 0` on a set of `p` of
positive (outer) `σ`-measure"). Conclusion: `CountablyRectifiable n A`. New.

### 11. `GaussGreenRepresentation` — (4.1)
For `U ⊆ ℝ^{n+1}` open, `E` `L^{n+1}`-measurable: `HasLocallyFinitePerimeter U E ↔
∃ μ ν, IsGaussGreenPair U E μ ν`, and any two Gauss–Green pairs satisfy `μ = μ'`, `ν = ν'`
`μ`-a.e. (this is what "`μ_E (= |Dχ_E|)`" and "the" normal mean). New (SimonGMT
`Chapter03.FinitePerimeterRepresentation` supplies the pair as data and is not used).

### 12. `DeGiorgiTheorem` — Theorem 4.3
Hypotheses: `U ⊆ ℝ^{n+1}` open, `E` `L^{n+1}`-measurable, `HasLocallyFinitePerimeter U E`.
Conclusions: a Gauss–Green pair exists, and for every Gauss–Green pair `(μ, ν)` (unique by 11):
`∂*E := reducedBoundary U μ ν` is countably `n`-rectifiable; `μ = Hⁿ ⌞ ∂*E`; at **every**
`x ∈ ∂*E`, (‡) `HasApproxTangentPlaneWithMultiplicity n μ x (span{ν_E(x)})ᗮ 1`; (‡‡) for every
compact `K`, `L^{n+1}(K ∩ (η_{x,λ}(E) ∆ {y · ν_E(x) > 0})) → 0` as `λ ↓ 0` (`L¹_loc` convergence of
characteristic functions). `ν_E = reducedNormal μ ν`. New. (Proof erratum, not affecting the
statement: in the proof, (9) and the final display should read `{x^{n+1} > λ}`, `{x^{n+1} > 0}`.)

## Definitions

Reused from SimonGMT (bodies read and checked; marked clean in the survey):
`Chapter03.CountablyRectifiable` (Def. 1.1: `M ⊆ M₀ ∪ ⋃ range Fⱼ`, `Hⁿ(M₀) = 0`, `Fⱼ : ℝⁿ → ℝ^{n+ℓ}`
Lipschitz), `Chapter03.HasApproximateTangentSpaceAt` (Def. 1.4, literal test-function convergence
with `η_{x,r}`), `Chapter03.HasWeightedApproximateTangentSpaceAt` (Def. 1.7, literal),
`Chapter03.PurelyUnrectifiable` (Def. 3.1), `Chapter03.blowUpMap` (`η_{x,λ}`),
`Chapter02.IsLocallyBV` (Ch. 2 (2.1)), `Chapter02.euclideanDivergence` (trace of `fderiv`).

New definitions (all in `GMT.Ch03`):
* `Rn N` — `EuclideanSpace ℝ (Fin N)` (abbrev).
* `IsC1Submanifold n S` — Simon Ch. 2 (4.1): local one-to-one `C¹` parametrizations `ψ : V → W`
  from open `V ⊆ ℝⁿ` with `ψ(V) = W ∩ S`, relatively proper, `Dψ` injective. Literal transcription
  of the book's definition of an embedded `C¹` submanifold (same content as SimonGMT's
  `Chapter02.IsSimonSubmanifold … 1`, written out because that one is not on the survey's clean list).
* `IsPositiveLocallyIntegrableWeight n M θ` — the hypotheses on θ in 1.7/1.9, literally
  (positivity on `M`, `Hⁿ⌞M`-measurability, integrability on `M ∩ K` for compact `K`).
* `approxTangentPlane n M θ x` — the `P` of Def. 1.7 (chosen; unique when `θ x ≠ 0` by
  `HasWeightedApproximateTangentSpaceAt.unique`), `⊥` if none. Faithfulness: Simon's §2 uses
  `T_x M` for general (not locally `Hⁿ`-finite) `M`, which only makes sense through Def. 1.7;
  for every `Hⁿ`-measurable countably rectifiable `M` such a θ exists (`M` is `Hⁿ`-σ-finite), and
  `T_x M` agrees a.e. with `T_x N_j` on `M_j` (the plane Simon uses in 2.1), so the Jacobians agree
  `Hⁿ`-a.e. with Simon's and the formulas do not depend on θ. With `θ ≡ 1` it is Def. 1.4.
* `HasTangentialDifferentialAt T f x L` / `tangentialDifferential T f x` — Simon (2.2):
  `d^M f_x(τ) = D_τ f(x)` for `τ ∈ T_x M`, where by Ch. 2 (4.10) (`f` locally Lipschitz on the open
  `U ⊇ M`) the directional derivative along curves in `M` equals `d/dt f(x + tτ)|_{t=0}`; encoded
  with Mathlib's `HasLineDerivAt` (two-sided), required for all `τ ∈ T` with `L` linear. `L` is
  unique when it exists, so the choice is canonical.
* `areaJacobian`, `coareaJacobian` — (2.3) `√det(d* ∘ d)` and (2.7) `√det(d ∘ d*)` via Mathlib's
  `LinearMap.normDet` (`normDet L ^ 2 = det(L* ∘ L)`, `LinearMap.normDet_sq`), applied to `d` and to
  its adjoint.
* `HasApproxTangentPlaneWithMultiplicity n μ x P θ` — approximate tangent space with multiplicity
  of a Radon measure (4.3 (‡); Ch. 4 p. 86): `λ⁻ⁿ ∫ f ∘ η_{x,λ} dμ → θ ∫_P f dHⁿ` for all
  `f ∈ C_c`. For `μ = Hⁿ⌞M`, `θ = 1` it is Def. 1.4.
* `coordinateProjection J` — orthogonal projection onto `span{e_j : j ∈ J}` (3.3).
* `frameProjection v`, `ForAlmostAllProjections N n P` — "`P(p)` for `σ`-a.e. `p ∈ O(N, n)`" (3.6,
  3.8), encoded as "for Lebesgue-a.e. frame `v ∈ (ℝᴺ)ⁿ` with `v` linearly independent, `P` holds
  for the orthogonal projection onto `span v`". Faithfulness: the Haar (`O(N)`-invariant)
  probability `σ` on the Grassmannian is the law of `span v` for a standard Gaussian frame `v`
  (`O(N)`-invariance of the Gaussian + uniqueness of the invariant probability on a compact
  homogeneous space), and the Gaussian and Lebesgue measures on `(ℝᴺ)ⁿ` have the same (outer) null
  sets, so this predicate has exactly the `σ`-null exceptional sets. Mathlib has no Grassmannian or
  Haar measure on `O(N)` in usable form.
* `HasLocallyFinitePerimeter U E` — `IsLocallyBV U χ_E` (`χ_E ∈ BV_loc(U)`), as in §4 (p. 80);
  defined from BV, not from Gauss–Green data.
* `IsGaussGreenPair U E μ ν` — (4.1): `μ` Borel measure vanishing off `U`, finite on compacta of
  `U` (= Radon on `U`), `ν` `μ`-measurable with `|ν| = 1` `μ`-a.e., and
  `∫_{E∩U} div g = -∫ g · ν dμ` for all `g ∈ C¹_c(U; ℝ^{n+1})`. This is a *property* characterizing
  the polar decomposition `Dχ_E = ν |Dχ_E|` of the vector Radon measure `Dχ_E`; existence and
  uniqueness are theorems (`GaussGreenRepresentation`), and 4.3 quantifies over all such pairs.
* `normalAverage`, `reducedBoundary`, `reducedNormal` — (4.2) and `ν_E(x)` of 4.3: averages
  `μ(B_ρ(x))⁻¹ ∫_{B_ρ(x)} ν dμ` (open balls; `0` when the denominator is `0`), `∂*E` = points of `U`
  where they converge to a unit vector, `ν_E(x)` = that limit (`limUnder`). They depend on `(μ, ν)`
  only through the vector measure `νμ = Dχ_E`.

## Errata (summary)
* (2.4)/(2.5): outer integrals over the target `ℝ^{n+ℓ₁}` (printed `ℝ^{n+ℓ}`).
* (2.9): domains `A` (left) and `M` (right) reconciled to `A` on both sides.
* Def. 3.1: "if `P` contains" should read "if `S` contains"; Def. 1.4: "`H(M ∩ K)`" is `Hⁿ(M ∩ K)`.
* Proof of 4.3 (not the statement): `{x^{n+1} < λ}` / `{x^{n+1} < 0}` should be `>`, consistent with
  the minus sign in (4.1) and with (‡‡).

## Modeling choices and points of uncertainty
* §2 Jacobians use `T_x M` from Def. 1.7 with an auxiliary weight θ (see above). An alternative
  would be Simon's decomposition-based definition 2.1; the θ-form is intrinsic and equivalent a.e.
* "`σ`-a.e. projection" is encoded with Lebesgue-a.e. frames (see above).
* 4.3 is stated for *every* Gauss–Green pair; uniqueness (in 11) shows this is "the" `μ_E`, `ν_E`.
* "`Hⁿ`-measurable" is `NullMeasurableSet` for `μHE[n]`; all such sets in the statements are
  `Hⁿ`-σ-finite (or locally finite), where this coincides with Carathéodory measurability.
* (2.8)/(2.9)/2.10(2) keep the book's restriction `m < n` (`0 < k`).
* Remark 2.10(2) is included as a stand-alone result (used for slicing later in the book).
