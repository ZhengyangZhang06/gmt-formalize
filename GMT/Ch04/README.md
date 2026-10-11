# Chapter 4 contract: Rectifiable n-varifolds (Simon, printed pp. 85–102)

Files: `Contract.lean` (frozen statement), `Submission.lean` (byte copy for the prover), this README.
Target: `GMT.Ch04.main_theorem`, a conjunction of 16 named Props. The only `sorry` is the proof of
`main_theorem`. The one auxiliary lemma, `pairWeight_eq_of_equiv`, is fully proved; it shows that the
weight measure is well defined on equivalence classes.

## Conventions

- Ambient space: `Ambient n ℓ := EuclideanSpace ℝ (Fin (n + ℓ))`, which is `ℝ^{n+ℓ}`.
- `Hⁿ` is `μHE[n]`, Mathlib's Euclidean Hausdorff measure. It is normalised to agree with Lebesgue
  measure on `n`-planes, so it equals Simon's `Hⁿ`. SimonGMT proves the bridge as
  `simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure`.
- `ωₙ` is `omega n`, the Lebesgue volume of the unit ball of `ℝⁿ`.
- `B_ρ(ξ)` is `closedBall ξ ρ`. In Simon's notation `B_ρ` is the closed ball.
- Every Prop assumes `0 < n`, Simon's standing convention for `n`-varifolds. Without it, 6.1 and 6.2
  would fail for `n = 0`. The Sobolev inequality 5.7 assumes `2 ≤ n` (see errata).
- Hypotheses such as "`|H| ≤ Λ` on `M ∩ U`" are stated `μ_V`-a.e. in `U`. `H` is only defined up to
  `μ_V`-null sets, so this is equivalent to the printed form after changing the representative of
  `H`, and it is formally weaker, which makes the theorem stronger.

## New definitions and why they are faithful

| Lean name | Book | Meaning and fidelity |
|---|---|---|
| `IsRectifiablePair n M θ` | p. 85 | `M` is countably `n`-rectifiable (SimonGMT `Chapter03.CountablyRectifiable`, which is Ch. 3, 1.1 verbatim). `M` is `Hⁿ`-measurable (`NullMeasurableSet M μHE[n]`); see the note below. `θ > 0` on `M`, and `θ` is locally `Hⁿ`-integrable on `M` (`IntegrableOn θ (M ∩ K) Hⁿ` for every compact `K`). These are exactly the book's hypotheses on `(M, θ)`, and no conclusion is stored. |
| `RectifiablePair n ℓ` | p. 85 | A bundled admissible pair `(M, θ)`. |
| `RectifiablePair.Equiv` | p. 85 | The book's relation, verbatim: `Hⁿ((M\M̃) ∪ (M̃\M)) = 0` and `θ̃ = θ` `Hⁿ`-a.e. on `M ∩ M̃`. |
| `RectifiableVarifold n ℓ` | p. 85 | `Quot RectifiablePair.Equiv`, which is literally the equivalence class `v(M, θ)`. `RectifiableVarifold.mk a` is `v(M, θ)`. |
| `pairWeight n M θ` | 1.1 | `(Hⁿ ⌞ M).withDensity θ`, which is `Hⁿ ⌞ θ` with `θ = 0` off `M`. |
| `V.weight` | 1.1 | `μ_V`, obtained by `Quot.lift` of `pairWeight`. Well-definedness is the proved lemma `pairWeight_eq_of_equiv`. |
| `V.support` | 1.4 | `spt V = spt μ_V`, using Mathlib's `Measure.support`. |
| `V.IsApproxTangentAt x P` | 1.3, Ch. 3 1.7 | `P` is an `n`-dimensional subspace, and for some `c ∈ (0,∞)` we have `λ⁻ⁿ∫ f(λ⁻¹(y-x)) dμ_V → c∫_P f dHⁿ` for every `f ∈ C_c`. Changing variables turns the left side into Simon's `∫_{η_{x,λ}(M)} f(y)θ(x+λy) dHⁿ(y)`. The book requires `c = θ(x)`, which depends on the chosen representative. Using `μ_V` with a free multiplicity `c` gives the representative-independent notion that Simon describes in 1.3 and in the remark after 1.2. `ApproxTangentAE` proves that the two notions coincide `Hⁿ`-a.e. on `M` with `c = θ(x)`. No tangent field is stored anywhere. |
| `V.tangentSpace x` | 1.3 | `T_xV`: the approximate tangent space if it exists (chosen; it is unique), and `⊥` otherwise. Its a.e. existence is the theorem `ApproxTangentAE` (Ch. 3, 1.9), not an assumption. |
| `V.tangentialDiv X x` | 2.3 | `div_M X = trace(DX(x) ∘ p_{T_xV})`, which equals `∑_{j,k} e^{jk} D_k X^j` (the same definition as SimonGMT `tangentialDivergence`). |
| `V.tangentialGradient h x` | Ch. 3 §2, Ch. 4 §5 | `∇^M h = p_{T_xV}(∇h)` (the same as SimonGMT `tangentialGradient`). |
| `V.normalRadialSq ξ x` | 3.2–3.3 | `|D^⊥r|² = |p_{(T_xV)^⊥}(x-ξ)|²/|x-ξ|²`. |
| `V.density ξ`, `V.HasDensityAt ξ t` | 3.9 | `Θⁿ(μ_V, ξ)` as the limit value of `μ_V(B_ρ(ξ))/(ωₙρⁿ)` (`limUnder`), and the statement that this limit exists and equals `t`. Every theorem that uses `density` also asserts that the limit exists. |
| `IsTestField U X` | 2.4, 3.14 | `X ∈ C¹_c(U; ℝ^{n+ℓ})`, written as `ContDiff ℝ 1 X`, `HasCompactSupport X` and `tsupport X ⊆ U`. Extending by zero makes this equivalent to the book's condition. |
| `V.IsStationaryIn U` | 2.4 | `∫ div_M X dμ_V = 0` for all `X ∈ C¹_c(U)`. This is the equivalent form stated in 2.4. Its equivalence with the variational definition is the Prop `StationaryIffVariational`. The definition mirrors SimonGMT `IsStationaryIn`, which cannot be reused because it is tied to the strengthened `Chapter04.RectifiableVarifold`. |
| `V.HasMeanCurvatureIn U H` | 3.14 | `H ∈ L¹_loc(U, μ_V)` and `∫ div_M X dμ_V = -∫ X·H dμ_V` for all `X ∈ C¹_c(U)`. The sign is the book's (‡). The `L¹_loc` clause is equivalent to the right side being defined for every `X`, and Simon uses it in 3.18, 5.9 and 6.1. This mirrors SimonGMT `HasGeneralizedMeanCurvatureIn`. |
| `V.IsLocallyLp U H p` | §4–§6 | `H ∈ L^p_loc(μ_V)` in `U`: `MemLp H p (μ_V ⌞ K)` for every compact `K ⊆ U`. |
| `V.MultiplicityGE α U` | 3.13, 4.10, §5, 6.3 | "`θ ≥ α` `μ_V`-a.e. in `U`", stated for some representative `(M, θ)` of `V`. All representatives agree a.e., so the choice does not matter. |
| `V.canonicalCarrier U` | 3.12 | `M_V = {x ∈ U : Θⁿ(μ_V, x) > 0}`. |
| `IsCompactVariation φ ε K` | 2.1 | A smooth family `(t,x) ↦ φ_t(x)` on `(-ε,ε) × ℝ^{n+ℓ}` of diffeomorphisms with `φ₀ = id` and `φ_t = id` off the compact set `K`. Simon's families of diffeomorphisms of an open set `U ⊇ K` fixing `U \ K` are exactly the restrictions of these families, by extension by the identity. |
| `imageMass a f K` | 1.2, 1.5, 1.6 | `M(f_#(V⌞K)) = ∫_{f(M∩K)} θ∘f⁻¹ dHⁿ` for injective `f`, computed from a representative `a = (M, θ)` exactly as in 1.6. |
| `lpKappa n p` | 4.2 | The corrected constant `κ = (p-n)/(4p)`. |
| `omega n`, `Ambient n ℓ` | notation | `ωₙ` and `ℝ^{n+ℓ}`. |

Note on `Hⁿ`-measurability: `NullMeasurableSet` means "Borel up to an `Hⁿ`-null set". For
countably `n`-rectifiable `M`, which lies in an `Hⁿ`-σ-finite Borel set, this coincides with
Carathéodory `Hⁿ`-measurability.

SimonGMT notions reused directly: `Chapter03.CountablyRectifiable`, which is clean and literal
Ch. 3 1.1, and `Chapter03.HasWeightedApproximateTangentSpaceAt`, which is clean and literal
Ch. 3 1.7. The second is used only inside `ApproxTangentAE`, to tie `T_xV` to the book's
definition. The contract does **not** use `Chapter04.RectifiableVarifold` or anything built on it.

## Statement map (Props in the order of `main_theorem`)

| # | Lean Prop | Book item, page | Statement | Key hypotheses | Existing SimonGMT (for the strengthened `Chapter04.RectifiableVarifold`; file under `Poincare/SimonGMT/`) |
|---|---|---|---|---|---|
| 1 | `ApproxTangentAE` | 1.3 with Ch. 3 1.8(2), 1.9; pp. 75, 86 | For every pair `(M, θ)` and `Hⁿ`-a.e. `x ∈ M`: `T_xV` exists and is unique, it is the approximate tangent space of `M` with respect to `θ` in the sense of Ch. 3 1.7, and `Θⁿ(μ_V, x) = θ(x)`. | `0 < n` | New. Ch. 3 1.6 and 1.9 are missing in SimonGMT. Partial tools: `Chapter03.HasWeightedApproximateTangentSpaceAt.unique` (Ch03/Rectifiable.lean) and `integral_weighted_blowUp` / `tendsto_rescaled_weight_of_weighted_approximateTangent` (Ch04/WeightedBlowUp.lean). |
| 2 | `FirstVariationFormula` | 2.2, p. 88 | `d/dt M(φ_t#(V⌞K))\|_{t=0} = ∫ div_M X dμ_V`, where `X = ∂_tφ\|_{t=0}`. | `IsCompactVariation φ ε K` | New. The push-forward and area formula on rectifiable sets are missing. |
| 3 | `StationaryIffVariational` | 2.4, p. 88 | `V` is stationary in open `U`, in the integral form, iff `d/dt M(φ_t#(V⌞K))\|_{t=0} = 0` for every family as in 2.1 with `K ⊆ U`. | `U` open | New. |
| 4 | `StationaryMonotonicity` | 3.6, 3.8, 3.10, pp. 90–91 | For `0<σ≤ρ<R`: `ρ⁻ⁿμ(B_ρ) - σ⁻ⁿμ(B_σ) = ∫_{B_ρ\B_σ} \|D^⊥r\|²/rⁿ dμ`. `ρ⁻ⁿμ(B_ρ)` is increasing on `(0,R)`. The integrand is integrable on `B_ρ`, and `(ωₙρⁿ)⁻¹μ(B_ρ) - Θ = ωₙ⁻¹∫_{B_ρ}…`. | stationary in open `U`, `B_R(ξ) ⊆ U` | `IsStationaryIn.stationaryMonotonicity_real`, `normalizedBallMass_monotoneOn` (Ch04/FirstVariation.lean); `IsStationaryIn.density_add_radialDefectMeasure`, `normalizedBallMass_real_eq_density_add_defect` (Ch04/Density.lean) |
| 5 | `StationaryDensity` | 3.9, 3.11, p. 91 | `Θⁿ(μ_V, ξ)` exists for every `ξ ∈ U` and is u.s.c. on `U`. | stationary in open `U` | `IsStationaryIn.tendsto_densityQuotient`, `upperSemicontinuousOn_stationaryDensityReal` (Ch04/Density.lean) |
| 6 | `CanonicalRepresentative` | 3.12, 3.13, p. 91 | `(M_V, Θ)` is an admissible pair and `v(M_V, Θ) = V⌞U` (equal weights). `{θ_V ≥ α}` is relatively closed in `U`. If `θ ≥ α > 0` a.e., then `M_V = spt V ∩ U` and `θ_V ≥ α` on `M_V`. | stationary in open `U` | Partial: `canonicalDensityCarrier`, `isClosed_canonicalDensity_superlevel` (Ch04/Density.lean), `IsStationaryIn.simon_3_13_support` (Ch04/CanonicalDensitySupport.lean). `V = v(M_V, θ_V)` is missing because it needs `Θ = θ` a.e. |
| 7 | `BoundedCurvatureMonotonicity` | 3.17 and the remark after it, pp. 92–93 | There are `F ∈ [e^{-Λρ}, e^{Λρ}]` and `G ∈ [e^{-ΛR}, e^{ΛR}]` with `F(ρ)ρ⁻ⁿμ(B_ρ) - F(σ)σ⁻ⁿμ(B_σ) = G(σ,ρ)∫_{B_ρ\B_σ} r⁻ⁿ\|D^⊥r\|²` for `0<σ≤ρ<R`. `Θ` exists everywhere in `U` and is u.s.c. | `H` is the generalized mean curvature in open `U`, `\|H\| ≤ Λ` a.e. in `U`, `0 ≤ Λ` | Partial: `HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn`, `tendsto_densityQuotient_real`, `upperSemicontinuousOn_stationaryDensityReal` (Ch04/MeanCurvature.lean). The simultaneous `F,G` identity is open in SimonGMT. |
| 8 | `LogarithmicMonotonicityError` | 3.18, p. 93 | `\|ρ⁻ⁿμ(B_ρ) - σ⁻ⁿμ(B_σ) - ∫_{B_ρ\B_σ} r⁻ⁿ\|D^⊥r\|²\| ≤ δ log(ρ/σ)`. | `τ^{1-n}∫_{B_τ}\|H\| ≤ δ` for `σ≤τ≤ρ`, `B_ρ(ξ) ⊆ U` | `HasGeneralizedMeanCurvatureIn.logarithmic_monotonicity_error` (Ch04/LogarithmicError.lean) |
| 9 | `LpMonotonicity` | 4.2, 4.5, 4.7, 4.8, pp. 93–94 | Bounds 4.5 on `F` and on `E = F - 1`. The identity 4.7 with `G ∈ [e^{-Λ}, e^{Λ}]` for `0<σ≤ρ≤R`. Monotonicity 4.8 on `(0,R]`. | `p > n`, `H ∈ L^p_loc(U)`, `B_R(ξ) ⊆ U`, `(R^{p-n}∫_{B_R}\|H\|^p)^{1/p} ≤ κΛ` with **corrected** `κ = (p-n)/(4p)` | `HasGeneralizedMeanCurvatureIn.exists_lpAnnularCorrection_of_locallyLp` and `LpAnnularCorrection` (Ch04/LpAnnular.lean); `lpMeanCurvatureKappa` (Ch04/LpMeanCurvature.lean). The statement shape is the same. |
| 10 | `LpDensity` | 4.9, p. 95 | `Θ` exists everywhere in `U` and is u.s.c. | `p > n`, `H ∈ L^p_loc(U)` | `HasGeneralizedMeanCurvatureIn.tendsto_densityQuotient_real_lp`, `upperSemicontinuousOn_stationaryDensityReal_lp` (Ch04/LpDensity.lean) |
| 11 | `LpSupportRepresentation` | 4.10(1), p. 95 | `Θ ≥ 1` on `spt V ∩ U`. `(spt V ∩ U, Θ)` is an admissible pair whose weight is `μ_V⌞U`, that is, `V⌞U = v(M_*, θ_*)`. | as in 10, plus `θ ≥ 1` a.e. in `U` | Partial: `HasGeneralizedMeanCurvatureIn.one_le_stationaryDensityReal_of_mem_support` (Ch04/TangentDensity.lean), `exists_ballGrowthBound_lp`, `isClosed_densityReal_superlevel_lp` (Ch04/LpRemarks.lean). The representation is missing. |
| 12 | `PoincareInequality` | 5.6, p. 97 | `∀ α Γ, ∃ β(n,α,Γ) ∈ (0,½), c(n,α,Γ) > 0` with `∫_{B_{βρ}} h ≤ cρ∫_{B_ρ}\|∇^M h\|`. The constants are chosen before `ℓ` and before the varifold data. | `\|H\| ≤ Λ`, `θ ≥ 1`, `h ∈ C¹(U)`, `h ≥ 0`, `B_{2ρ} ⊆ U`, `μ{h>0}∩B_ρ ≤ (1-α)ωₙρⁿ`, `e^{Λρ} ≤ 1+α`, `μ(B_{2ρ}) ≤ Γρⁿ` | `exists_poincare_constants`, `HasGeneralizedMeanCurvatureIn.poincare_inequality` (Ch04/Poincare.lean). SimonGMT fixes the ambient space `E` before its constants, but its constants `poincareRadius n α` and `poincareConstant n α Γ` do not depend on `E`. |
| 13 | `SobolevInequality` | 5.7, 5.9, pp. 98–100 | `∃ c(n)`, independent of `ℓ`, with `(∫h^{n/(n-1)})^{(n-1)/n} ≤ c∫(\|∇^M h\| + h\|H\|)`. | `n ≥ 2`, `H ∈ L¹_loc` only, `θ ≥ 1`, `h ∈ C¹_c(U)`, `h ≥ 0` | `HasGeneralizedMeanCurvatureIn.sobolev_inequality` (Ch04/Sobolev.lean), with constant `sobolevConstant n` (it uses 4× the printed constant). |
| 14 | `SupportInBall` | 6.1, p. 100 | `spt V ⊆ B_R(ξ)`. | `H` is the generalized mean curvature in `ℝ^{n+ℓ}\B_R(ξ)`, `n⁻¹\|H·(x-ξ)\| < 1` a.e. there, `spt V` compact, `R ≥ 0` | `HasGeneralizedMeanCurvatureIn.support_subset_closedBall` (Ch04/CompactSupportMaximum.lean) |
| 15 | `ConvexHullProperty` | 6.2, p. 101 | `spt V ⊆ conv K`. | `spt V` compact, stationary in `ℝ^{n+ℓ}\K`, `K` compact | `IsStationaryIn.support_subset_convexHull` (Ch04/ConvexHullProperty.lean) |
| 16 | `ClassicalTangent` | 6.3, p. 101 | `sup{ρ⁻¹dist(y-x, T_xV) : y ∈ spt V ∩ B_ρ(x)} → 0`. | `θ ≥ 1`, `H ∈ L^p_loc(U)`, `p > n`, `T_xV` exists at `x ∈ U` | `HasGeneralizedMeanCurvatureIn.classical_tangent` (Ch04/ClassicalTangent.lean). SimonGMT assumes the Ch. 3 1.7 tangent with the representative's `θ(x)`; changing `θ` at the single point `x` is a null modification, which bridges the two. |

All SimonGMT Chapter 4 results above are proved only for the strengthened representative
`Chapter04.RectifiableVarifold`, which carries an a.e. approximate-tangent field. To reuse them,
the prover has to build that structure from a `RectifiablePair`. That construction needs
Ch. 3 1.9 (Prop 1) and measurability of the tangent projection, and the prover then has to
transport the definitions: `tangentialDiv` is `tangentialDivergence` a.e., and `density` is
`stationaryDensityReal` wherever the limit exists.

## Errata and corrections built into the statements

- **4.2, κ.** The printed `κ = p/(4(p-n))` does not give the claimed `∫₀^ρ|F₀| ≤ ½Λ(ρ/R)^{1-n/p}`.
  The correct value is `κ = (p-n)/(4p)` (ledger HR-028). `LpMonotonicity` uses the corrected
  value.
- **3.16 and 4.1, sign.** With 3.14(‡) the error term enters with a `+` sign and the integrating
  factor is `exp(-∫E)` (ledger 3.16). The final statements 3.17, 4.5 and 4.7 have symmetric
  bounds, so they are stated as printed.
- **3.17 remark.** "`Θ` exists for all `ξ ∈ N ∩ U`" is a typo for `U`.
- **5.7, dimension.** The exponent `n/(n-1)` requires `n ≥ 2`, so `SobolevInequality` assumes
  `2 ≤ n`. The book's "c does not depend on k" means `ℓ`. The constant is quantified before `ℓ`.
- **6.3, distance.** The printed `dist(y, T_xV)` is corrected to `dist(y - x, T_xV)`, because
  `T_xV` is a linear subspace.
- Not stated, because they are only intermediate steps: the 3.5 prefactors (which are reversed),
  the 4.10(2) annular estimate (false as printed: a Dirac mass on a sphere is a counterexample),
  the 5.2 coefficient (`Λ`, not `Λρ`), and Lemma 5.8 (whose hypotheses are inconsistent as
  printed).

## Deliberately omitted

- 1.6–1.9 for general, non-injective Lipschitz push-forwards, and the identity
  `M(f_#V) = ∫J_M f θ`. These are Ch. 3 area-formula material, used here only through the
  injective `imageMass` in 2.2 and 2.4.
- 2.5–2.7 (stationarity in `U ∩ N` for a `C²` submanifold `N`, and `H̄^N`). Stating them needs a
  second fundamental form of `N`, and later chapters use them only as an example of 3.14.
- 3.7 (the differentiated form of 3.6), 4.6 (a trivial consequence of 4.5), 4.10(2) and 4.11
  (layer-cake), 5.1–5.5 (intermediate inequalities), and 5.8 (a lemma). These are routine or
  intermediate.

## Points of residual uncertainty

- **`T_xV` with a free multiplicity `c`.** This is the representative-independent reading of 1.3.
  At a single point it is weaker than Ch. 3 1.7 with the representative's `θ(x)`, so 6.3 as
  stated is slightly stronger than the book's. It is still true: the proof uses only the
  blow-up convergence, whatever `c` is. `ApproxTangentAE` shows that the two notions agree a.e.
- **Endpoint `ρ = R` in 4.5 and 4.7.** The book prints `ρ ≤ R`, so the contract states the closed
  endpoint and adds the §4 standing hypothesis `H ∈ L^p_loc(U)`, which allows going slightly
  beyond `R`. SimonGMT proves the same closed-endpoint form under the same hypothesis.
- **3.17.** The simultaneous `F,G` identity is stated as printed, existentially, with `ρ < R`. As
  far as I can see it follows from the corrected differential identity by the product rule for
  BV functions, with `F = exp(-∫E)`. It is not yet proved in SimonGMT.
- **Measurability.** The integrals `∫ div_M X dμ_V` and `∫ |∇^M h| dμ_V` are Bochner integrals.
  They have their intended meaning because `x ↦ T_xV` is `μ_V`-a.e. measurable, which follows
  from Ch. 3 1.9 and is part of the prover's work. The definitions do not presuppose it.

## Compile output

`CAMP/bin/leanc GMT/Ch04/Contract.lean` (sha256 `6e58e5dd…0f4770b`):

```
GMT/Ch04/Contract.lean:437:8: warning: declaration uses `sorry`
```

That is the only diagnostic, on `main_theorem`. `Submission.lean` is a byte copy, and `cmp` is
silent.
