# Chapter 8 — Theory of General Varifolds (Simon, printed pp. 205–224)

Frozen contract: `GMT/Ch08/Contract.lean` (namespace `GMT.Ch08`, final theorem
`GMT.Ch08.main_theorem`, a conjunction of 13 named `Prop`s). `GMT/Ch08/Submission.lean` is a byte
copy for the prover.

Conventions. `ℝ^{n+ℓ}` is `Euclidean N = EuclideanSpace ℝ (Fin N)` with `N = n + ℓ` (all `N`, `n`
are universally quantified; `ℓ = N - n` is implicit). `U` is open. An `n`-varifold on `U` is the
SimonGMT structure `Poincare.SimonGMT.Chapter08.Varifold N n U`. Simon's closed ball `B_ρ(x)` is
`Metric.closedBall x ρ`. `H^n` is Mathlib's `μHE[n]` (Hausdorff measure normalized to agree with
Lebesgue measure on `n`-planes, which is Simon's normalization). `ω_n` is the Lebesgue volume of
the unit ball of `ℝ^n`. "`W ⊂⊂ U`" is `IsRelCompactOpenIn W U` (open, compact closure in `U`).

## Statement map

| # | Book item (page) | Lean `Prop` | What it says | Existing SimonGMT coverage |
|---|---|---|---|---|
| 1 | 1.2 First Rectifiability Theorem (p. 206) | `FirstRectifiabilityTheorem` | If `V` has a tangent plane `T_x` with multiplicity `θ(x) ∈ (0,∞)` (Def. 1.1) at `μ_V`-a.e. `x`, then with `M = {x ∈ spt μ_V : T_x, θ(x) exist}` and `θ` the multiplicity function, `M` is `H^n`-measurable, countably `n`-rectifiable, `θ` is locally `H^n`-integrable and `V = v(M,θ)`. | new (Ch. 3 1.9 and Ch. 8 1.3 are missing in SimonGMT) |
| 2 | 2.2–2.4 (pp. 208–209) | `FirstVariationIsMassDerivative` | For a `C²` family `φ_t` (`φ_0 = id`, `φ_t` injective `U → U`, `φ_t = id` off compact `K ⊆ U`) with velocity `X`: `d/dt|₀ M(φ_{t#}V ⌞ Gₙ(K)) = ∫ div_S X dV`; and `div_S X = Σ τ_i·D_{τ_i}X` for any orthonormal basis of `S`. | proved: `Varifold.hasDerivAt_pushforwardMeasure_cylinder_family_of_velocity` (Chapter08/DeformationIntegral.lean), `Varifold.tangentialDivergence_eq_sum_inner` (Chapter08/Varifold.lean) |
| 3 | 2.5–2.10 (pp. 209–210) | `FirstVariationRepresentation` | LBFV ⇒ `‖δV‖` is the Radon measure of 2.5; ∃ Borel `ν`, `|ν| = 1` `‖δV‖`-a.e., `δV(X) = -∫ν·X d‖δV‖`; `D_{μ_V}‖δV‖` exists and is finite `μ_V`-a.e.; `μ_V(Z) = 0`; `δV(X) = -∫H·X dμ_V - ∫_Z ν·X dσ` (with integrability). | proved: `isFirstVariationMeasure_riesz`, `measurable_firstVariationPolarField`, `ae_firstVariationPolarField_norm_one`, `isFirstVariationPolarRepresentation_riesz`, `firstVariationRiesz_symmetricDensity_spec`, `firstVariationRiesz_boundary_spec`, `firstVariationRiesz_integrable_meanCurvature_and_boundary`, `firstVariation_eq_meanCurvature_add_boundary_of_locallyBounded` (Chapter08/FirstVariationRiesz.lean). My `variationDensity`, `generalizedBoundary`, `generalizedBoundaryMeasure`, `generalizedMeanCurvature` unfold to SimonGMT's `symmetricFirstVariationDensity`, `symmetricGeneralizedBoundarySet`, `symmetricGeneralizedBoundaryMeasure`, `symmetricGeneralizedMeanCurvature` applied to `variationMeasure V`. |
| 4 | 3.3 monotonicity, general `Λ ≥ 0` (p. 210) | `MonotonicityFormula` | LBFV, `B_{ρ₀}(x) ⊆ U`, `‖δV‖(B_ρ(x)) ≤ Λ μ_V(B_ρ(x))` for `0<ρ<ρ₀` ⇒ `e^{Λρ}ρ^{-n}μ_V(B_ρ(x))` increasing on `(0,ρ₀)`; `Θ^n(μ_V,x)` exists, is finite, and `Θ ≤ e^{Λσ}ω_n^{-1}σ^{-n}μ_V(B_σ)`, `e^{Λσ}ω_n^{-1}σ^{-n}μ_V(B_σ) + ω_n^{-1}∫_{Gₙ(B_ρ∖B_σ)} r^{-n-2}|p_{S⊥}(y-x)|² dV ≤ e^{Λρ}ω_n^{-1}ρ^{-n}μ_V(B_ρ)` for `0<σ≤ρ<ρ₀`. | partial: only `Λ = 0` (`StationaryOn.stationaryMonotonicity`, `StationaryOn.normalizedBallMass_monotoneOn`, Chapter08/StationaryMonotonicity.lean). General `Λ`: new. |
| 5 | 3.4 identity, `Λ = 0` (p. 211) | `StationaryMonotonicityIdentity` | `V` stationary in `B_{ρ₀}(x) ⊆ U` ⇒ `Θ^n(μ_V,x)` exists and `Θ + ω_n^{-1}∫_{Gₙ(B_ρ(x))} r^{-n-2}|p_{S⊥}(y-x)|² dV = ω_n^{-1}ρ^{-n}μ_V(B_ρ(x))`, `0<ρ<ρ₀`. | partial: annular identity `StationaryOn.stationaryMonotonicity`, limit `StationaryOn.tendsto_normalizedBallMass_atRight` (StationaryMonotonicity.lean); `σ → 0` passage and `ω_n` normalization missing. |
| 6 | 3.6 Lemma (p. 211) | `DensityExistsAE` | LBFV ⇒ `Θ^n(μ_V,x)` exists and is finite `μ_V`-a.e., and agrees `μ_V`-a.e. with a Borel function. | partial: `ae_forall_exists_ballFirstVariationBound` (Chapter08/BallVariationBound.lean) gives the a.e. ball bound 3.1. |
| 7 | 3.7 Theorem (p. 211) | `DensitySemicontinuity` | `V_i → V` (Radon on `Gₙ(U)`), each `V_i` LBFV, `liminf ‖δV_i‖(W) < ∞`, `Θ^n(μ_{V_i},·) ≥ 1` off `B_i` with `μ_{V_i}(B_i ∩ W) → 0` ⇒ `V` LBFV, `‖δV‖(W) ≤ liminf ‖δV_i‖(W)`, `Θ^n(μ_V,·) ≥ 1` `μ_V`-a.e. | partial: `RadonConverges.hasLocallyBoundedFirstVariation`, `RadonConverges.firstVariationRieszMeasure_le_liminf`, `RadonConverges.firstVariationNormOn_le_liminf` (Chapter08/VarifoldConvergence.lean). Density conclusion: new. |
| 8 | 4.1 Constancy Theorem (p. 213), **corrected** | `ConstancyTheorem` | `V` stationary in `U`, `U ∩ spt μ_V ⊆ M`, `M` an `n`-dim `C²` submanifold, **`M ∩ U` connected** ⇒ `V(A) = θ₀ H^n({x ∈ M∩U : (x,T_xM) ∈ A})` for a constant `θ₀ ≥ 0`. | proved in substance: `Varifold.Stationary.exists_const_tangentGraph_connectedCarrier` (Chapter08/ConstancyCorrected.lean; stated with `simonHausdorffMeasureReal` and chart tangents — needs translation to `μHE[n]` via `simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure` and to `classicalTangentSpace`). |
| 9 | 5.1–5.4 varifold tangents (p. 215), **5.2/5.3 corrected** | `VarifoldTangentCones` | LBFV, `Θ^n(μ_V,x) = θ₀ ∈ (0,∞)`, `ρ^{1-n}‖δV‖(B_ρ(x)) → 0` ⇒ every `λ_j → 0` has a subsequence with `η_{x,λ_j#}V → C`; every such `C ∈ VarTan(V,x)` is stationary in `ℝ^{n+ℓ}`, `μ_C(B_ρ(0)) = θ₀ω_nρ^n`, and `μ_C(sA) = s^nμ_C(A)`. | partial: `blowUpMeasure_eq_pushforward`, `tendsto_blowUpWeight_closedBall_of_density`, `Stationary.radial_mem_plane_of_mem_support_of_constant_mass_ratio` (Chapter08/TangentRescaling.lean, TangentRadialRigidity.lean); SimonGMT `blowUpMeasure` is definitionally the contract's `rescaledMeasure` up to unfolding `Chapter03.blowUpMap`. Extraction, stationarity of limits, homogeneity: new. |
| 10 | 5.7 Corollary (p. 216) | `TangentConesAreRectifiableCones` | Under 5.1 and `ρ^{-n}μ_V({y ∈ B_ρ(x) : Θ^n(μ_V,y) ≥ 1 fails}) → 0`, every `C ∈ VarTan(V,x)` is rectifiable and `η_{0,λ#}C = C` for all `λ > 0`. | new |
| 11 | **5.5 Allard Rectifiability Theorem** (p. 215) + Remark 5.6 | `AllardRectifiabilityTheorem` | LBFV and `Θ^n(μ_V,x) > 0` `μ_V`-a.e. ⇒ `V` is rectifiable, and `V` has a tangent plane (Def. 1.1) at `μ_V`-a.e. `x`. | new |
| 12 | **5.8 Compactness Theorem** (p. 218) | `CompactnessTheorem` | Rectifiable LBFV `V_j`, `sup_j(μ_{V_j}(W)+‖δV_j‖(W)) < ∞`, `Θ^n(μ_{V_j},·) ≥ 1` off `A_j` with `μ_{V_j}(A_j ∩ W) → 0` ⇒ subsequence `→` rectifiable LBFV `V` with `Θ^n(μ_V,·) ≥ 1` a.e. and `‖δV‖(W) ≤ liminf_{j'}‖δV_{j'}‖(W)`. | new (l.s.c. part: `RadonConverges.firstVariationRieszMeasure_le_liminf`) |
| 13 | **5.9 Integral Compactness** (Remark, p. 218) | `IntegralCompactnessTheorem` | Integral LBFV `V_j` with the same bounds ⇒ a subsequence converges to an integral LBFV `V` with the l.s.c. bound; and every subsequential Radon limit is integral. | new |

Not included (routine lemmas used only inside proofs): 1.3 (disintegration), 3.5 (weighted
monotonicity; SimonGMT records a sign erratum there), 5.10/5.11 (the integrality lemma).

## Errata / corrections

- **4.1** (printed: `M` connected). False as printed: SimonGMT
  `ConstancyDomainCounterexample.counterexample_constancy_printed_hypotheses` (`U = ℝ∖{0}`, `M = ℝ`,
  `V = v((0,∞))` is stationary in `U` with `spt ⊆ M` but not a constant multiple). Corrected
  hypothesis: `M ∩ U` (pre)connected, which is what the book's proof uses. The conclusion
  `V = θ₀ v(M)` is read in `U`, i.e. `θ₀ v(M ∩ U)`; `θ₀ = 0` is allowed (it is forced e.g. when
  `H^n(M ∩ K) = ∞` for some compact `K ⊆ U`).
- **5.2** printed `μ_C(B_ρ(x))`; corrected to `μ_C(B_ρ(0))` (`C` lives at the origin).
- **5.3** printed `λ^{-n}μ_C(η_{0,λ}(A)) = μ_C(A)` with `η_{0,λ}(y) = λ^{-1}y`; wrong power
  (SimonGMT `TangentScalingCounterexample.printed_inverse_scaling_fails`). Stated as
  `μ_C(sA) = s^n μ_C(A)` for all `s > 0`, all `A`.
- **5.8** "`liminf_{j→∞}`" is taken along the extracted subsequence (along the full sequence the
  inequality can fail).
- **3.3/3.4** subtractions are written additively in `[0,∞]`; this is equivalent because every
  term is finite (`B_ρ(x)` compact in `U`).

## New definitions (all in `GMT.Ch08`) and why they are faithful

- `unitBallVolume n` — `ω_n = vol(B_1^n)` (Mathlib `volume` on `EuclideanSpace ℝ (Fin n)`).
- `densityRatio n μ x ρ = μ(B_ρ(x))/(ω_n ρ^n)`, `HasDensity n μ x θ` — `Θ^n(μ,x)` exists and equals
  `θ` (closed balls, `ρ ↓ 0`), exactly Ch. 1, 3.1.
- `IsRelCompactOpenIn W U` — Simon's `W ⊂⊂ U` (open `W`). Hypotheses quantified over open
  `W ⊂⊂ U` are equivalent to the version over all relatively compact `W`; conclusions about
  `‖δV‖(W) ≤ liminf` are only true for open `W`.
- `variationMeasure V` — `‖δV‖`: SimonGMT's `firstVariationRieszMeasure` under LBFV (else `0`).
  `isFirstVariationMeasure_riesz` proves it is locally finite on `U`, zero off `U`, and equals the
  supremum 2.5 on every open `W ⊂⊂ U`; a Radon measure on `U` is determined by these values, so this
  is the book's `‖δV‖`. `FirstVariationRepresentation` re-asserts this characterization.
- `variationDensity`, `generalizedBoundary`, `generalizedBoundaryMeasure`, `generalizedMeanCurvature`
  — `D_{μ_V}‖δV‖` (as `limsup` of `‖δV‖(B_ρ)/μ_V(B_ρ)`, a true limit a.e.), `Z`, `σ = ‖δV‖⌞Z`,
  `H = (D_{μ_V}‖δV‖)ν` of 2.7–2.9.
- `normalDefect V x A = ∫_{Gₙ(A)} r^{-n-2}|p_{S⊥}(y-x)|² dV`, `p_{S⊥}v = v - p_S v` (3.3/3.4).
- `rescaledMeasure V x λ = λ^{-n} (V.measure.map ((y,S) ↦ (λ^{-1}(y-x), S)))` — `V_{x,λ} = η_{x,λ#}V`
  of 1.1/5.1 (for a homothety `J_Sη = λ^{-n}` and `dη(S) = S`, so this is 2.1; SimonGMT
  `blowUpMeasure_eq_pushforward`).
- `planeVarifoldMeasure T` — `v(T)`: `H^n⌞T` pushed to the graph `y ↦ (y,T)`.
- `HasTangentPlane V x T θ` — Def. 1.1: `x ∈ U`, `θ > 0`, `∫ f dV_{x,λ} → θ ∫ f dv(T)` for every
  `f ∈ C_c(ℝ^N × G(N,n))`.
- `VagueConverges`, `IsVarifoldTangent` — Radon-measure convergence on `Gₙ(ℝ^{n+ℓ})`; Def. 5.4
  (`λ_j > 0`, `λ_j → 0`; any such sequence has a decreasing subsequence with the same limit).
- `IsVarifoldOf V M θ` — `V = v(M,θ)` exactly as on p. 206: `M ⊆ U` `H^n`-measurable
  (`NullMeasurableSet`; for countably rectifiable sets this equals Carathéodory measurability),
  countably `n`-rectifiable (SimonGMT Ch. 3 1.1), `θ > 0` on `M`, `θ` integrable on `M ∩ K` for every
  compact `K ⊆ U`, and `V(A) = ∫_{π(TM∩A)} θ dH^n` where `π(TM ∩ A) = {x ∈ M : ∃ S, M has approximate
  tangent plane S w.r.t. θ at x (Ch. 3, 1.7, SimonGMT `HasWeightedApproximateTangentSpaceAt`) and
  (x,S) ∈ A}`. No tangent field is data; the plane is unique where `θ(x) > 0`
  (`HasWeightedApproximateTangentSpaceAt.unique`). Replaces the unfaithful
  `Chapter04.RectifiableVarifold`.
- `IsRectifiable V`, `IsIntegral V` — `∃ M θ, V = v(M,θ)` (and `θ ∈ ℕ` `H^n`-a.e. on `M`).
- `classicalTangentSpace M y` — Ch. 2 §4 (p. 55): velocities of `C¹` curves `(-1,1) → M` through `y`.

Reused SimonGMT definitions (sources read and checked): `Varifold`, `Grassmannian` (projection
matrices; `Grassmannian.plane`, `Grassmannian.project`), `Varifold.weight`, `Varifold.firstVariation`,
`Varifold.tangentialDivergence` (`trace(P_S DX)`), `Varifold.TestVectorField`,
`Varifold.firstVariationNormOn`, `Varifold.HasLocallyBoundedFirstVariation`,
`Varifold.IsFirstVariationMeasure`, `Varifold.firstVariationRieszMeasure`, `Varifold.Stationary`,
`Varifold.RadonConverges`, `Varifold.pushforwardMeasure` (formula 2.1 with
`J_S f = (det (df|_S)^*(df|_S))^{1/2}`; the plane map is totalized off `J_S f ≠ 0`, where the density
vanishes) — all in Chapter08/Varifold.lean, FirstVariationRiesz.lean, VarifoldConvergence.lean;
`Chapter03.CountablyRectifiable`, `Chapter03.HasWeightedApproximateTangentSpaceAt`
(Chapter03/Rectifiable.lean); `Chapter02.IsSimonSubmanifold` (Chapter02/Submanifold.lean: local
1:1 `C^r` proper maximal-rank parametrizations, exactly Ch. 2 (4.1)).

## Compile check

`bin/leanc GMT/Ch08/Contract.lean` (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b366308):
the only diagnostic is
`GMT/Ch08/Contract.lean:413:8: warning: declaration uses 'sorry'` (the final `main_theorem`).
`Submission.lean` is a byte copy (`cmp` silent).
