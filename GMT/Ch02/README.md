# Chapter 2 contract — Simon, *Introduction to GMT*, "Some Further Preliminaries from Analysis" (printed pp. 39–68)

Files: `Contract.lean` (frozen statement), `Submission.lean` (byte copy for the prover).
Final theorem: `GMT.Ch02.main_theorem`, the conjunction of the 16 Props below.

Conventions (Simon's Notation page): `B_ρ(ξ)` = **closed** ball (`Metric.closedBall`);
`W ⊂⊂ U` = `closure W` compact and `⊆ U` (`Chapter02.IsRelativelyCompactIn`); `ℝⁿ = EuclideanSpace ℝ (Fin n)`
(`GMT.Ch02.Rn n`), `Lⁿ = volume`. Real-dimensional Hausdorff measure `𝓗[s]` (local notation) =
`Poincare.SimonGMT.Chapter01.simonHausdorffMeasureReal s = (ω_s/2^s) • μH[s]` with `ω_s = π^{s/2}/Γ(s/2+1)`
(Ch. 1, 2.1–2.2; `ω[s]` = `Chapter01.realUnitBallVolume s`). For natural `n` the contract uses Mathlib's `μHE[n]`,
which equals `𝓗[n]` (SimonGMT `Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure`) and equals
`Lⁿ` on `ℝⁿ` (`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`). Carathéodory "`μ`-measurable" is rendered
`NullMeasurableSet` / `AEMeasurable`; these coincide for sets of finite measure and for functions supported in a
set of σ-finite measure, which covers every use below.

## Statement map

| # | Book item (printed page) | Lean name | What it says | Existing SimonGMT material |
|---|---|---|---|---|
| 1 | Thm 1.2 (p. 40) | `LipschitzExtension` | `X` metric, `∅ ≠ A ⊆ X`, `f : A → ℝ` Lipschitz ⇒ ∃ Lipschitz `F : X → ℝ`, `Lip F = Lip f`, `F|A = f`. | `Chapter02.lipschitz_extension_real_optimal` (Chapter02/Lipschitz.lean) proves exactly this with `optimalLipschitzConstant` (= `sInf {K | LipschitzWith K f}`, same as `lipConst`) and `IsLipschitz`. |
| 2 | Thm 1.4 (p. 40) | `Rademacher` | Lipschitz `f : ℝⁿ → ℝ` is (Fréchet) differentiable `Lⁿ`-a.e. | Mathlib `LipschitzWith.ae_differentiableAt`; `Chapter02.rademacher_ae_differentiableAt` (Lipschitz.lean). |
| 3 | Thm 1.5 (p. 42) | `C1Approximation` | Lipschitz `f : ℝⁿ → ℝ`, `ε > 0` ⇒ ∃ `g ∈ C¹(ℝⁿ)` with `Lⁿ({f ≠ g} ∪ {∇f ≠ ∇g}) < ε`. `{∇f ≠ ∇g}` is rendered as `{x | ¬ HasFDerivAt f (Dg(x)) x}` (differs from the literal set by a null set, by 1.4). | new (Whitney route in Chapter02/Whitney*.lean is unbuilt and incomplete). |
| 4 | Thm 1.6 (pp. 42–43) | `WhitneyExtension` | `A ⊆ ℝⁿ` closed, `h : A → ℝ`, `ν : A → ℝⁿ` continuous, `R(x,y) → 0` as `y → x` in `A` uniformly for `x` in each compact `K ⊆ A` ⇒ ∃ `g ∈ C¹(ℝⁿ)`, `g = h`, `∇g = ν` on `A`. Uniform limit written as `∀ ε>0 ∃ δ>0 ∀ x∈K ∀ y∈A, 0<|y−x|<δ → |h y − h x − ν(x)·(y−x)| ≤ ε|y−x|`. | new (Chapter02/WhitneyJet/Cover/Partition/Extension.lean exist but are not built/imported). |
| 5 | Thm 1.8 (p. 44) | `LipschitzImageHausdorff` | `X` σ-compact metric, `Y` metric, real `m ≥ 0`, `A` `Hᵐ`-measurable, `Hᵐ(A) < ∞`, `f` `K`-Lipschitz on `A`: (i) `f(A)` `Hᵐ`-measurable, `Hᵐ(f(A)) ≤ Kᵐ Hᵐ(A)`; (ii) `N(f,·)` `Hᵐ`-measurable, `∫ N(f,y) dHᵐ ≤ Kᵐ Hᵐ(A)`. | (i) inequality: Mathlib `LipschitzOnWith.hausdorffMeasure_image_le`; (i) measurability for natural `m` only: `Chapter02.nullMeasurableSet_image_of_lipschitzOn_sigmaCompact_of_nullMeasurable` (LipschitzMeasurability.lean). (ii) new. |
| 6 | Thm 1.9 (p. 45) | `EilenbergInequality` | `X` σ-compact metric, `m ≥ 1`, real `k > 0`, `A` `H^{m+k}`-measurable of finite measure, `f : A → ℝᵐ` `K`-Lipschitz ⇒ `y ↦ Hᵏ(A ∩ f⁻¹y)` `Lᵐ`-measurable and `∫ Hᵏ(A ∩ f⁻¹y) dLᵐ ≤ (ω_m ω_k/ω_{m+k}) Kᵐ H^{m+k}(A)`. | new; Remark 1.10 upper-integral tools in Chapter02/UpperIntegral.lean (`exists_measurableMajorant_lintegral_eq_upperLebesgueIntegral`, …). |
| 7 | Thm 2.6 (p. 50) | `BVCompactness` | `u_k ∈ BV_loc(U)` with `sup_k (‖u_k‖_{L¹(W)} + |Du_k|(W)) < ∞` for all open `W ⊂⊂ U` ⇒ subsequence `u_{ψ k} → u` in `L¹_loc(U)`, `u ∈ BV_loc(U)`, `|Du|(W) ≤ liminf |Du_{ψ k}|(W)` for open `W ⊂⊂ U`. | partial: `Chapter02.isLocallyBV_of_locallyL1_of_uniform_bound`, `Chapter02.bvVariationOn_le_liminf_of_locallyL1` (BV.lean) give the limit-closure and l.s.c. steps; subsequence extraction is new. |
| 8 | Lemma 2.7 (p. 51) | `BVPoincare` | `∀ n θ δ ∃ C(θ,δ,n)`: `U` bounded open convex, `B_{δR}(ξ) ⊆ U ⊆ B_R(ξ)` (closed balls), `u ∈ BV(U)`, `min{Lⁿ{u ≥ β}, Lⁿ{u ≤ β}} ≥ θ Lⁿ(U)` ⇒ `∫_U |u−β| ≤ C R |Du|(U)`. | new. |
| 9 | Lemma 2.8 (p. 51) | `BVExtensionEstimate` | `∀ n δ ∃ C(δ,n)`: `U, R, ξ` as in 2.7, `u ∈ BV(ℝⁿ)`, `u = 0` a.e. off `Ū` ⇒ `|Du|(ℝⁿ∖Ū) = 0` and `|Du|(ℝⁿ) ≤ C(|Du|(U) + R⁻¹∫_U|u|)`. | new. |
| 10 | 3.4 and 3.5 (p. 54) | `AreaFormula` | `A ⊆ ℝⁿ` `Lⁿ`-measurable, `f` Lipschitz on `A` into `ℝᵐ`, `m ≥ n`, `Jf = √det(df*df)` with `df` = derivative within `A`: (3.4) `∫ #(A ∩ f⁻¹y) dHⁿ(y) = ∫_A Jf dLⁿ`; (3.5) for `Lⁿ`-measurable `h ≥ 0` on `A`, `y ↦ ∑_{x∈A∩f⁻¹y} h(x)` is `Hⁿ`-measurable and `∫ ∑ h dHⁿ = ∫_A h Jf dLⁿ`. **Erratum**: 3.4 prints `dHᵐ(y)`; correct is `dHⁿ(y)`. | essentially proved: `Chapter02.area_formula_lipschitzOn_multiplicity` and `weighted_area_formula_lipschitzOn_fiberSum`, `aemeasurable_weightedAreaFiberSum_lipschitzOn` (AreaDomain.lean); `area_formula_lipschitzOn_multiplicity_simon_volume` (AreaLiteral.lean). Bridges needed: `areaJacobianWithin` uses `normDet` (= `√det(L*L)`, `areaJacobianAt_eq_sqrt_det_adjoint_comp`, Area.lean); `areaMultiplicity`/`weightedAreaFiberSum` vs `fiberCount`/`∑'` over `A ∩ f⁻¹{y}`; `μHE[finrank ℝ (Rn n)]` vs `μHE[n]`. |
| 11 | 5.3 (p. 63) | `FirstVariation` | `M` `n`-dim `C¹` submanifold of `ℝ^{n+ℓ}`, `U` open, `U∩M ≠ ∅`, `Hⁿ(K'∩M) < ∞` for compact `K' ⊆ U`, `φ` admissible of class `C²` (5.1) ⇒ `HasDerivAt (t ↦ Hⁿ(φ_t(M∩K))) (∫_M div_M X dHⁿ) 0`. | new; supporting algebra in SubmanifoldCalculus.lean (`submanifoldDivergenceAt`, `submanifoldDivergenceAt_eq_sum_inner`), area on charts `IsSimonLocalRepresentation.weighted_area_formula` (WeightedArea.lean). |
| 12 | 5.4 (p. 63) | `SecondVariation` | same setting, `φ` of class **C³**: `t ↦ Hⁿ(M_t)` differentiable near 0 and its derivative has derivative `∫_M (div_M Z + (div_M X)² + ∑|(D_{τᵢ}X)^⊥|² − ∑(τᵢ·D_{τⱼ}X)(τⱼ·D_{τᵢ}X)) dHⁿ` at 0. **Correction**: book assumes `C²`; then `Z` is only `C⁰` and `div_M Z` is undefined. | new. |
| 13 | Lemma 5.5(2) (p. 63) | `StationaryIffMeanCurvatureZero` | `M` `C²`, `U` open, `Ū ∩ M` compact ⇒ (`M` stationary in `U` ⇔ `H ≡ 0` on `M ∩ U`). Part (1) (manifold with boundary) omitted. | new; pointwise identity `div_M X^⊥ = −X·H` is `Chapter02.submanifoldDivergenceAt_normalFrameComponent_eq_neg_inner_meanCurvature`; 4.30 is partial (`integral_submanifoldDivergence_eq_curvature_sub_boundary`, divergence theorem assumed). |
| 14 | Lemma 5.11 (p. 65) | `SecondVariationStationary` | `M` `C²`, stationary in `U`, `(M̄∖M) ∩ U = ∅`, `φ` admissible `C³` with normal initial velocity `X` ⇒ second variation `= ∫_M (∑|(D_{τᵢ}X)^⊥|² − ∑(X·B(τᵢ,τⱼ))²) dHⁿ`. Same `C³` correction. | new; `secondFundamentalForm_eq_normalProjection_curve` (SecondFundamentalFormCalculus.lean) relates to 4.25. |
| 15 | 6.3 and 6.6 (pp. 66–67) | `CoareaFormula` | `M` `(m+k)`-dim `C¹` submanifold of `ℝᴺ`, `k ≥ 1`, `f` `C¹` on open `U ⊇ M`, `g ≥ 0` `Hⁿ`-measurable on `M` ⇒ `y ↦ ∫_{M∩f⁻¹y} g dHᵏ` is `Lᵐ`-measurable and `∫_M g J*_f dHⁿ = ∫_{ℝᵐ} ∫_{M∩f⁻¹y} g dHᵏ dLᵐ(y)`; 6.3 is `g = 1_A`. | partial: linear cases `Chapter02.coarea_linear`, `coarea_linear_lintegral` (CoareaLinear.lean), `coarea_projection(_lintegral)` (CoareaProjection.lean); nonlinear new. |
| 16 | Thm 6.4 (p. 67) | `C1Sard` | same setting, `C = {x ∈ M : J*_f(x) = 0}`: `C = {x ∈ M : rank df_x < m}`; `Hᵏ(f⁻¹y ∩ C) = 0` for `Lᵐ`-a.e. `y`; for every `y`, `f⁻¹y ∩ C` is relatively closed in `M` and `f⁻¹y ∖ C` is a `k`-dim `C¹` submanifold (vacuously if empty). | new. |

Not included (routine or out of scope): 1.3, 1.7, 1.10–1.12, 2.1–2.5, 2.9, 3.1–3.3 and 3.6 (special cases/examples of
3.4–3.5), §4 items 4.1–4.30 (definitions and pointwise identities used by §5; 4.21/4.30 need a manifold-with-boundary
notion), 5.5(1), 5.6–5.10 (stationarity relative to an ambient `N`), 5.12, 6.1–6.2 (special cases of 6.3), 6.5, 6.7.

## New definitions and why they are faithful

- `Rn n` — `EuclideanSpace ℝ (Fin n)`, Simon's `ℝⁿ` with its Euclidean norm and Lebesgue measure.
- `lipConst f` — `sInf {K : ℝ≥0 | LipschitzWith K f}`, Simon's `Lip f` (1.1: the least constant). Used only together
  with a Lipschitz hypothesis/conclusion, so the junk value `sInf ∅ = 0` never matters.
- `fiberCount A f y` — `encard (A ∩ f⁻¹{y})` in `ℝ≥0∞` = `H⁰(A ∩ f⁻¹y)` = Simon's `N(f,y)` (counting measure, `∞` allowed).
- `areaJacobian L` — `√det(L* ∘ L)`, literally 3.1/3.3. Applied to `fderivWithin ℝ f A x` (the derivative of `f|A`,
  unique and equal to the derivative of any Lipschitz extension at `Lⁿ`-a.e. point of `A`).
- `IsBVOn U u` — `U` open, `u ∈ L¹(U)`, `|Du|(U) = bvVariationOn u U < ∞`: the standard `BV(U)` (Simon 2.4 gives
  `|Du|(W)` for open `W` as this supremum over Lipschitz fields, equivalently `C¹_c` fields).
- `tangentSpace M y` — span of `{γ'(0) : γ ∈ C¹((−1,1)), γ((−1,1)) ⊆ M, γ(0) = y}`, Simon's definition before 4.3
  (for a submanifold the set is already a subspace, 4.3).
- `tangentProjection`, `normalPart` — orthogonal projection onto `T_yM` (`Submodule.starProjection`) and `v − P_y v`.
- `tangentFrame M y` — an orthonormal basis `τ₁..τₙ` of `T_yM` (Mathlib `stdOrthonormalBasis`). All expressions built
  from it are basis-independent traces, so the choice is harmless (and the integrands are measurable).
- `tangentialDivergence M X y` — `∑ᵢ τᵢ · DX(y)τᵢ` = `div_M X` (4.18–4.20), `X` an ambient `C¹` field.
- `secondFundamentalForm M y τ η` — `(D_τ P)(η)`: derivative within `M` (Mathlib `fderivWithin`) of the field
  `z ↦ P_z` in direction `τ`, applied to `η`. For `C²` `M` and `τ, η ∈ T_yM` this equals Simon's 4.24
  `B_y(τ,η) = −∑_α (η·D_τν^α)ν^α` (expand `P = I − ∑ν^α⊗ν^α`), hence `B_y(τ,τ) = γ''(0)^⊥` (4.25). The within-derivative
  is unique on `T_yM ⊆` tangent cone of `M` at `y`, so no choice enters on tangent arguments.
- `meanCurvature M y` — `∑ᵢ B_y(τᵢ,τᵢ)` (4.27); Simon's sign convention (`∫ div_M X = −∫ X·H` for compactly supported `X`).
- `coareaJacobian M f x` — `√det(df_x ∘ df_x*)` with `df_x = Df(x) ∘ ι_{T_xM} : T_xM → ℝᵐ` (p. 66).
- `IsAdmissibleDeformation r U K φ` — 5.1: `U` open, `K ⊆ U` compact, `(t,x) ↦ φ_t(x)` is `C^r` on `(−1,1) × U`,
  `φ_0 = id` on `U`, `φ_t = id` off `K`, and each `φ_t` (`|t| < 1`) is a diffeomorphism of `U` (bijection `U → U`
  with invertible derivative on `U`, equivalent by the inverse function theorem). Values off `U` are normalized to the
  identity (Simon's `φ_t` is only defined on `U`; since `K ⊂ U` this is a harmless normalization).
- `initialVelocity`, `initialAcceleration` — `X = ∂_tφ|_{t=0}`, `Z = ∂²_tφ|_{t=0}` (before 5.2).
- `deformedArea n M K φ t` — `Hⁿ(φ_t(M ∩ K))` as a real number (finite for the relevant `t`).
- `IsStationaryIn n M U` — p. 63: `Hⁿ(M ∩ K) < ∞` for all compact `K ⊆ U` and `HasDerivAt (t ↦ Hⁿ(M_t)) 0 0` for
  every admissible `C²` family (5.1). Defined from variations, not from `∫ div_M X = 0` (that equivalence is a theorem).
- `secondVariationIntegrand`, `stableSecondVariationIntegrand` — the integrands of 5.4 and 5.11, written with the
  orthonormal frame exactly as printed.

Reused SimonGMT definitions (sources read): `Chapter02.IsLocallyBV` (2.1: `U` open, `u ∈ L¹_loc(U)`, and for every
open `W ⊂⊂ U` a constant `c ≥ 0` with `∫_W u div g ≤ c sup|g|` for all `C¹_c` fields with `spt g ⊆ W`),
`Chapter02.bvVariationOn` (2.4: sup of `∫_W u div g` over compactly supported Lipschitz `g`, `spt g ⊆ W`, `sup|g| ≤ 1`;
`div` uses `fderiv`, which agrees a.e. with the true divergence by Rademacher), `Chapter02.TendstoLocallyInL1On`
(`∫_K |v_i − u| → 0` for every compact `K ⊆ U`), `Chapter02.IsRelativelyCompactIn`, `Chapter02.IsSimonSubmanifold`
(4.1: around each point an open `V ⊆ ℝⁿ`, open `W`, a `C^r` injective map `ψ` with `ψ(V) = W ∩ M`, proper relative to
`V, W`, `Dψ` injective; `r ≥ 1`), `Chapter01.simonHausdorffMeasureReal`, `Chapter01.realUnitBallVolume`.

## Errata / corrections

- 3.4: target measure `Hᵐ` → `Hⁿ` (as in 3.5 and the SimonGMT ledger).
- 5.4 and 5.11: deformations of class `C³` instead of `C²` (needed for `Z ∈ C¹` and the `O(t³)` expansion 5.2).
- 1.5: `{∇f ≠ ∇g}` read as "not (f differentiable with `∇f = ∇g`)" — equal to the literal set up to an `Lⁿ`-null set.
- 2.6: `W ⊂⊂ U` taken open (the l.s.c. conclusion fails for non-open `W`; 2.4 characterizes `|Du|(W)` only for open `W`).

## Judgment calls (flag for review)

- 1.8 is stated for real `m ≥ 0` (Simon's `Hᵐ` is defined for all real `m ≥ 0`); SimonGMT has image measurability
  only for natural `m`.
- 1.8/1.9 use a Lipschitz constant `K` in place of `Lip f`; equivalent because the least constant is attained.
- 2.7 `u ∈ BV(U)` includes `u ∈ L¹(U)`; 2.8's `spt u ⊂ Ū` is "`u = 0` a.e. off `Ū`", and the printed equality
  `∫_{ℝⁿ}|Du| = ∫_Ū|Du|` is encoded as `|Du|(ℝⁿ∖Ū) = 0` (`bvVariationOn u (closure U)ᶜ = 0`).
- 3.4/3.5: `Jf` uses the derivative of `f` within `A` (`fderivWithin`); measurability of the fiber-sum integrand is
  asserted as part of 3.5 (Simon's integrals presuppose it).
- 5.x: "diffeomorphism of `U`" encoded as bijection `U → U` with invertible derivative; stationarity is defined via
  variations (as on p. 63), so `∫_M div_M X = 0` is a consequence, not a definition. `B` is defined as `(D_τ P)η`
  rather than via a chosen normal frame (equal to 4.24; frame-free so no choice is needed).
- 5.4/5.11 regularity raised from `C²` to `C³` (see Errata). The second derivative is stated as "differentiable near
  0, and `deriv` has the given derivative at 0".
- 6.4: "closed set" read as relatively closed in `M` (`M` need not be closed in `ℝᴺ`); the printed identity
  `C = {rank df_x < m}` is included as a conjunct.

## Compile

`CAMP/bin/leanc GMT/Ch02/Contract.lean` → only `declaration uses 'sorry'` at `main_theorem`.
`Submission.lean` is a byte copy (`cmp` silent).
