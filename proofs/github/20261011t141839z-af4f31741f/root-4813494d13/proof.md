# Final proof of `GMT.Ch08.main_theorem` (root node)

- Run: `20261011T141839Z-af4f31741f`, node `root`, issue
  <https://github.com/ZhengyangZhang06/gmt-formalize/issues/2>.
- Source: Leon Simon, *Introduction to Geometric Measure Theory* (2014), Chapter 8 "Theory of
  General Varifolds", printed pp. 205–224, with the cross-references to Chapters 1–4 that the
  printed proofs use.
- Frozen problem: `GMT/Ch08/Contract.lean` at commit `63436ae63eb6a2fd7525bef73c73cf88e2cd7e93`.
- Lean target: `GMT/Ch08/Submission.lean`. The Lean source of this candidate is the one of commit
  `4c30aa30` ("Repair merged root submission and prove GMT.Ch08.main_theorem"). The commit that adds
  this file changes no `.lean` file.
- Toolchain: Lean `v4.35.0-rc3`, Mathlib `25730c7c759d108ef87ab70af2342a196760f79d`, and the
  `simongmt` package (`Poincare.SimonGMT.*`) at `2b3663083f3fe399b6296fb8eaee52169170e197`. All three
  are pinned by the frozen `lakefile.toml`/`lake-manifest.json`.

## 0. Summary

`GMT.Ch08.main_theorem` is proved in Lean with no `sorry`. Its axioms are exactly `propext`,
`Classical.choice` and `Quot.sound` (`#print axioms`, §8).

The root proof is a single anonymous-constructor term. It assembles the 13 conjuncts from the
conclusions of accepted child theorems (§2). Those children are proved from their own accepted
descendants, the pinned SimonGMT library and Mathlib (§3, Appendix A, Appendix B).

The run's DAG has 241 accepted declarations besides the root. Each one is present exactly once in
`Submission.lean`, under its exact globally qualified name and with its frozen type. Each one's
full text (doc comment, statement and proof) equals the text in its accepted candidate commit. Each
one is used, directly or transitively, by the proof of `main_theorem` (§4, §8).

None of these lemmas is merely historical. §6 lists the differences between the reviewed plans and
the formal proof that was actually carried out.

## 1. Statement, assumptions and conventions

```lean
theorem main_theorem : FirstRectifiabilityTheorem ∧ FirstVariationIsMassDerivative ∧
    FirstVariationRepresentation ∧ MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧
    DensityExistsAE ∧ DensitySemicontinuity ∧ ConstancyTheorem ∧ VarifoldTangentCones ∧
    TangentConesAreRectifiableCones ∧ AllardRectifiabilityTheorem ∧ CompactnessTheorem ∧
    IntegralCompactnessTheorem
```

**Assumptions.** The theorem is a closed proposition and has no hypotheses. Each conjunct is a
frozen `def … : Prop` of the contract. It quantifies over all `N n : ℕ`, all `U`, varifolds,
points, radii and sequences, with exactly the hypotheses written in that definition. No hypothesis
is added, removed or weakened anywhere. The proof introduces no axiom, `sorry`, `admit`, `opaque`,
`native_decide`, `implemented_by` or `extern` (the source was searched; the only textual hits for
"admit" are the English word in three comments).

**Corrections already built into the frozen statement** (`GMT/Ch08/README.md`, "Errata"):

- 4.1 assumes `M ∩ U` preconnected rather than `M` connected; the printed version is false.
- 5.2 is centred at `0`.
- 5.3 is the homogeneity `μ_C(sA) = s^n μ_C(A)`.
- In 5.8 the `liminf` is taken along the extracted subsequence.
- In 3.3 and 3.4 the subtractions are written additively in `[0, ∞]`.

The children also correct two printed proof steps, without touching any statement:

- In Ch. 1, 4.16 the Alaoglu step only yields a subnet. It is replaced by a sequential extraction
  on the second countable space `Gₙ(U)` (§3.3).
- In 1.2 the corrected identity `η_V^(x)(β) = β(T_x)` is used (§3.9).

**Conventions** are those of the contract and its README:

- `Euclidean N = EuclideanSpace ℝ (Fin N)`.
- `B_ρ(x) = Metric.closedBall x ρ`.
- `H^n = μHE[n]`.
- `ω_n = unitBallVolume n`.
- `μ_V = V.weight`, `‖δV‖ = variationMeasure V` and `Θ^n(μ, x)` is `HasDensity n μ x`.
- `V_{x,λ} = rescaledMeasure V x λ`.

**The definitions are the frozen ones.** `Submission.lean` consists of the following, in order:

1. The contract's four imports plus five further SimonGMT imports (`Chapter08.TangentRadialRigidity`,
   `Chapter01.DensityComparison`, `Chapter01.EuclideanHausdorffUpper`, `Chapter02.AreaLiteral`,
   `Chapter08.StationaryMonotonicity`).
2. The contract's 408 lines from the module docstring through `IntegralCompactnessTheorem`,
   byte-for-byte (checked by a line comparison).
3. The 241 child theorems.
4. `main_theorem` with the contract's statement.
5. `end GMT.Ch08`.

## 2. The root argument (the Lean proof of `main_theorem`)

```lean
theorem main_theorem : FirstRectifiabilityTheorem ∧ … ∧ IntegralCompactnessTheorem :=
  ⟨Submission.first_rectifiability_theorem,
    Submission.first_variation_theorems.1,
    Submission.first_variation_theorems.2,
    Submission.monotonicity_and_density_theorems.1,
    Submission.monotonicity_and_density_theorems.2.1,
    Submission.monotonicity_and_density_theorems.2.2,
    Submission.density_semicontinuity_theorem,
    Submission.constancy_theorem,
    Submission.varifold_tangent_theorems.1,
    Submission.allard_rectifiability_and_tangent_cones.2,
    Submission.allard_rectifiability_and_tangent_cones.1,
    Submission.compactness_theorem,
    Submission.integral_compactness_theorem⟩
```

Inside `namespace GMT.Ch08`, `Submission.X` denotes `GMT.Ch08.Submission.X`. The conjunction is
right-nested, so the anonymous constructor fills the 13 conjuncts in order. Each component's type
is, verbatim, the conjunct in that position:

| # | Conjunct | Simon | Lean term | Accepted node (frozen type) |
|---|---|---|---|---|
| 1 | `FirstRectifiabilityTheorem` | 1.2 | `first_rectifiability_theorem` | `root.first_rectifiability-a1` (`FirstRectifiabilityTheorem`) |
| 2 | `FirstVariationIsMassDerivative` | 2.2–2.4 | `first_variation_theorems.1` | `root.first_variation-a1` (`FirstVariationIsMassDerivative ∧ FirstVariationRepresentation`) |
| 3 | `FirstVariationRepresentation` | 2.5–2.10 | `first_variation_theorems.2` | same |
| 4 | `MonotonicityFormula` | 3.3 | `monotonicity_and_density_theorems.1` | `root.monotonicity_density-a1` (`MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE`) |
| 5 | `StationaryMonotonicityIdentity` | 3.4 | `monotonicity_and_density_theorems.2.1` | same |
| 6 | `DensityExistsAE` | 3.6 | `monotonicity_and_density_theorems.2.2` | same |
| 7 | `DensitySemicontinuity` | 3.7 | `density_semicontinuity_theorem` | `root.density_semicontinuity-a1` |
| 8 | `ConstancyTheorem` | 4.1 (corrected) | `constancy_theorem` | `root.constancy-a1` |
| 9 | `VarifoldTangentCones` | 5.1–5.4 (corrected) | `varifold_tangent_theorems.1` | `root.varifold_tangents-a1` (`VarifoldTangentCones ∧ <blow-up density lower bound>`) |
| 10 | `TangentConesAreRectifiableCones` | 5.7 | `allard_rectifiability_and_tangent_cones.2` | `root.allard_tangent_cones-a1` (`AllardRectifiabilityTheorem ∧ TangentConesAreRectifiableCones`) |
| 11 | `AllardRectifiabilityTheorem` | 5.5, 5.6 | `allard_rectifiability_and_tangent_cones.1` | same |
| 12 | `CompactnessTheorem` | 5.8 | `compactness_theorem` | `root.compactness-a1` |
| 13 | `IntegralCompactnessTheorem` | 5.9 | `integral_compactness_theorem` | `root.integral_compactness-a1` |

The child for 5.5 and 5.7 proves `AllardRectifiabilityTheorem ∧ TangentConesAreRectifiableCones`.
The root statement lists 5.7 before 5.5, so conjunct 10 is `.2` and conjunct 11 is `.1`.

The remaining three root children are not named in the tuple but are used by the children:

- `varifold_radon_compactness` (Ch. 1, 4.16 on `Gₙ(U)`).
- `plane_disintegration` (Lemma 1.3).
- `tangent_points_lipschitz_graph_cover` (the Lipschitz-graph cover of tangent points).

So the root theorem holds as soon as the twelve root children hold. §3 explains how each is proved
in Lean.

## 3. Proofs of the twelve root children (the formalized route)

The children are listed in dependency order. For each, "uses" names the sibling root children and
the main accepted descendants that its Lean proof actually invokes. The statement and one-paragraph
proof of every descendant is in Appendix A. The SimonGMT constants that each declaration uses
directly are in Appendix B.

### 3.1 `first_variation_theorems` — Simon 2.2–2.10

**(a) 2.2–2.4.** Let `φ` be a `C²` family on `(−1,1) × U` with the following properties:

- `φ_0 = id`;
- each `φ_t` maps `U` injectively into `U`;
- `φ_t = id` on `U ∖ K` for a compact `K ⊆ U`;
- `X = ∂_t φ|_{t=0}`.

Then `t ↦ M(φ_{t#}V ⌞ Gₙ(K))` has derivative `δV(X) = ∫ div_S X dV` at `0`. This is SimonGMT's
`Varifold.hasDerivAt_pushforwardMeasure_cylinder_family_of_velocity`
(`Chapter08/DeformationIntegral.lean`). By formula 2.1 the mass is `∫_{K×G} J_S φ_t dV`, and
`∂_t J_S φ_t|_{t=0} = div_S X`. The proof differentiates under the integral by dominated
convergence, on a short time interval where the Gram determinant is `≥ 1/2`.

The identity `div_S X = Σ_i τ_i · D_{τ_i}X` for every orthonormal basis `τ` of `S` is SimonGMT's
`Varifold.tangentialDivergence_eq_sum_inner` (`Chapter08/Varifold.lean`). Here `div_S X` is
`trace(p_S ∘ DX)`, and the trace is computed in an orthonormal basis of `ℝ^N` extending `τ`.

**(b) 2.5–2.10.** Assume `V` has locally bounded first variation. In this branch
`variationMeasure V` is by definition SimonGMT's Riesz measure `V.firstVariationRieszMeasure hV`.
Unfolding the contract's `variationDensity`, `generalizedBoundary`, `generalizedBoundaryMeasure` and
`generalizedMeanCurvature` turns them definitionally into SimonGMT's
`symmetricFirstVariationDensity`, `symmetricGeneralizedBoundarySet`,
`symmetricGeneralizedBoundaryMeasure` and `symmetricGeneralizedMeanCurvature` for that measure.
The conclusions then come from SimonGMT (`Chapter08/FirstVariationRiesz.lean`):

- **2.5:** `isFirstVariationMeasure_riesz`. `‖δV‖` is a Radon measure on `U`, equal to the supremum
  of `|δV(X)|` over `|X| ≤ 1`, `spt X ⊆ W` for each open `W ⊂⊂ U`. This is the Riesz
  representation of the bounded functional `δV` on `K(W)`.
- **2.6:** `firstVariationPolarField`, `measurable_firstVariationPolarField`,
  `ae_firstVariationPolarField_norm_one` and `isFirstVariationPolarRepresentation_riesz`. They give
  a Borel `ν` with `|ν| = 1` `‖δV‖`-a.e. and `δV(X) = −∫ ν·X d‖δV‖`, absolutely convergent.
- **2.7:** `firstVariationRiesz_symmetricDensity_spec`. `D_{μ_V}‖δV‖(x)` exists as a limit and is
  finite `μ_V`-a.e. (Besicovitch differentiation).
- **2.9:** `firstVariationRiesz_boundary_spec`, i.e. `μ_V(Z) = 0`.
- **2.8 and 2.10:** `firstVariationRiesz_integrable_meanCurvature_and_boundary` and
  `firstVariation_eq_meanCurvature_add_boundary_of_locallyBounded`. They give the decomposition
  `δV(X) = −∫ H·X dμ_V − ∫_Z ν·X dσ`, with both integrands integrable.

Restricting `σ = ‖δV‖ ⌞ Z` once more to `Z` leaves it unchanged (`Measure.restrict_restrict_of_subset`).

*Uses:* no sibling; SimonGMT and Mathlib only.

### 3.2 `monotonicity_and_density_theorems` — Simon 3.3, 3.4, 3.6

The proof is the triple `⟨monotonicity_formula_8_3_3, stationary_monotonicity_identity_8_3_4,
density_exists_ae_8_3_6⟩`.

**3.3.** Assume `B°_{ρ₀}(x) ⊆ U` and `‖δV‖(B_ρ(x)) ≤ Λ μ_V(B_ρ(x))` for `0 < ρ < ρ₀` (3.1). For
`ε > 0` let `φ = φ_ε` be SimonGMT's smooth non-increasing cutoff
`monotonicityCutoff ε = 1 − smoothTransition((·−1)/ε)`. It equals `1` on `(−∞, 1]` and `0` on
`[1+ε, ∞)`. Put

- `I(t) = ∫ φ(|y−x|²/t²) dμ_V`,
- `J(t) = ∫ φ(|y−x|²/t²) |p_{S⊥}(y−x)|²/|y−x|² dV`,
- `X_t(y) = φ(|y−x|²/t²)(y−x)`.

SimonGMT's `hasDerivAt_normalized_weightedCutoffMass` (`Chapter08/WeightedRadialIdentity.lean`,
weight `h ≡ 1`, so its gradient term vanishes) gives the radial identity

`d/dt (t^{-n} I(t)) = t^{-n} J'(t) − t^{-n-1} δV(X_t)`.

`mono833_radial_first_variation_bound` gives `|δV(X_t)| ≤ (1+ε) Λ t I(t)`. It writes
`δV(X_t) = −∫ ν·X_t d‖δV‖` (2.6) and turns 3.1 into `∫ φ d‖δV‖ ≤ Λ ∫ φ dμ_V`. That last step is the
layer-cake comparison `mono833_radial_layer_cake_le`: every positive superlevel set of the integrand
is a closed ball `B_r(x)` with `r < ρ₀`.

Put `F(t) = t^{-n} I(t)`. Then `t^{-n} J'(t) ≤ F'(t) + (1+ε) Λ F(t)` and `J' ≥ 0`.

For fixed `0 < σ ≤ ρ < ρ₀`, let `q = |p_{S⊥}(y−x)|²/(|y−x|² max(σ, |y−x|)^n)`. This is the bounded
weight of SimonGMT's `truncatedRadialDefect`. Let `G(t) = ∫ φ(|y−x|²/t²) q dV`. Then
`G'(t) ≤ t^{-n} J'(t)` on `[σ, ρ]`. The integrating-factor comparison
`mono833_integrating_factor_comparison`, applied with `L = (1+ε)Λ`, gives:

`e^{(1+ε)Λσ} F(σ) + (G(ρ) − G(σ)) ≤ e^{(1+ε)Λρ} F(ρ)`.

Now let `ε ↓ 0`. Dominated convergence for the cutoffs (SimonGMT `tendsto_cutoffMass`,
`tendsto_integral_radialCutoff`) and continuity of `exp` apply. In the limit `G(ρ) − G(σ)` becomes
the annular defect `∫_{Gₙ(B_ρ∖B_σ)} r^{-n-2}|p_{S⊥}(y−x)|² dV`, since `q = |p_{S⊥}|²/r^{n+2}` for
`r ≥ σ`. Multiplying by `ω_n^{-1}` gives the annular inequality of the conclusion, with every term
finite. Two further consequences follow:

- monotonicity of `e^{Λρ} ρ^{-n} μ_V(B_ρ(x))` on `(0, ρ₀)`;
- via `mono833_exp_weighted_density_limit`, the existence and finiteness of `Θ^n(μ_V, x)` and
  `Θ ≤ e^{Λσ} ω_n^{-1} σ^{-n} μ_V(B_σ(x))`.

**3.4.** Let `V` be stationary in `B°_{ρ₀}(x) ⊆ U`. For `0 < σ ≤ ρ < ρ₀`, SimonGMT's
`StationaryOn.stationaryMonotonicity` (`Chapter08/StationaryMonotonicity.lean`, on a ball `B_R(x)`
with `ρ < R < ρ₀`) gives the additive annular identity. Two lemmas then pass to `σ ↓ 0`:

- `normalDefect_annulus_tendsto_closedBall`: the annular defects increase to the full defect, and
  the integrand vanishes at `y = x`.
- `annular_identity_limit_at_zero`: in `[0, ∞]`, `P(σ) + D(σ, ρ) = P(ρ)` with `D(σ, ρ) → T(ρ)`
  forces `P(σ) → θ` and `θ + T(ρ) = P(ρ)`.

**3.6.** `dea_ae_variationMeasure_ball_bound` shows that hypothesis 3.1 holds at `μ_V`-a.e. `x`,
with some `Λ(x)` and `ρ₀(x)`. This follows from 2.7 (SimonGMT's
`firstVariationRiesz_symmetricDensity_spec`): where `‖δV‖(B_r(x))/μ_V(B_r(x))` has a finite limit,
it is bounded for small `r`. So 3.3 gives a finite density `μ_V`-a.e.
`frt_weq_density_borel_representative` gives a Borel `Θ` with `Θ(x) = liminf_k μ(B_{1/(k+1)}(x))/(ω_n(k+1)^{-n})`, which equals every existing density limit.

*Uses:* no sibling (2.5–2.7 enter through SimonGMT lemmas, not through §3.1).

### 3.3 `varifold_radon_compactness` — Simon Ch. 1, 4.16, corrected, on `Gₙ(U)`

**Statement.** Suppose that for each compact `K ⊆ U` the masses `μ_j(K × G)` are eventually bounded.
Then some subsequence `μ_{φ(j)}` converges, against every `f ∈ C_c` supported in `U × G`, to a
varifold `V` on `U`.

**Proof.** Work on the open set `S = U × G(N, n)`, which is locally compact, Hausdorff and second
countable. Restricted to `S`, the masses are eventually bounded on compact sets of `S`.

1. `radon_compactlySupported_countable_approx` gives a countable family `g_k ∈ C_c(S)`. Every
   `f ∈ C_c(S)` is a uniform limit of `g_k`'s supported in one fixed compact set.
2. `radon_exists_subseq_tendsto_integral` makes `∫ g_k dμ_{φ(j)}` converge for all `k` by a diagonal
   (Tychonoff) extraction. The mass bound then makes every `∫ f dμ_{φ(j)}` Cauchy. This replaces the
   printed Alaoglu step, which only yields a subnet.
3. `radon_exists_measure_of_tendsto_integral` shows that the limit functional is positive and
   linear. Mathlib's Riesz–Markov–Kakutani theorem (`RealRMK.rieszMeasure`,
   `RealRMK.integral_rieszMeasure`) represents it by a locally finite measure `ν` on `S`.
4. `Varifold.ofDomainMeasure` extends `ν` by zero to a varifold on `U`. Test functions supported in
   `S` restrict to `C_c(S)`, which identifies the integrals.

*Uses:* no sibling.

### 3.4 `plane_disintegration` — Simon Lemma 1.3

**Statement.** For `μ_V`-a.e. `x` there is a probability measure `η(x)` on `G(N, n)` such that
`(∫_{Gₙ(B_ρ(x))} β(S) dV)/μ_V(B_ρ(x)) → ∫ β dη(x)` for every continuous `β`. Moreover
`∫_{Gₙ(A)} β(S) dV = ∫_A ∫ β dη(x) dμ_V(x)` for Borel `A` and continuous `β ≥ 0`.

**Proof.**

1. `plane_disint_slice_density` (printed (1)–(2)). For continuous `β ≥ 0`,
   `γ(A) = ∫_{Gₙ(A)} β dV ≤ ‖β‖ μ_V(A)`. SimonGMT's Besicovitch differentiation on `U`
   (`Varifold.ae_tendsto_firstVariationDensity_of_domainMeasure`) and Radon–Nikodym give
   `γ = e μ_V` with `γ(B_ρ(x))/μ_V(B_ρ(x)) → e(x)` a.e.
2. `C(G(N, n), ℝ)` is separable: Stone–Weierstrass, since the matrix-entry functions separate
   points. Take a dense sequence `f_j` and apply step 1 to `β_j = f_j + ‖f_j‖`.
3. `plane_disint_pointwise_measure`, with `plane_disint_riesz_limit`. At a point `x ∈ U ∩ spt μ_V`
   where all these limits exist, the normalized slice measures `m_ρ` are probability measures for
   small `ρ`, and `∫ f dm_ρ` converges on the dense family. Hence `∫ f dm_ρ` converges for every
   `f`. Riesz–Markov–Kakutani on the compact space `G(N, n)` represents the limit by a probability
   measure `η(x)`.
4. `η` is chosen with `Filter.skolem`.
5. `plane_disint_identity_of_limits` (second part). By uniqueness of limits, `e(x) = ∫ β dη(x)`
   a.e.

*Uses:* no sibling.

### 3.5 `tangent_points_lipschitz_graph_cover` — the cone argument of Simon Ch. 3, 1.6 "⇐"

**Statement.** Let `0 < L ≤ 1` and `P ∈ G(N, n)`. There are countably many closed sets `Γ_i` with
`|q(y−z)| ≤ L|p(y−z)|` on each `Γ_i`, where `p = p_P` and `q = I − p`. Together they contain every
`x` at which `V` has a tangent plane `T` (Definition 1.1) with `‖p_T − p_P‖ ≤ L/4`.

**Proof.**

- **`n = 0`.** By `tgc_dim_zero_tangent_points_countable`, such points are atoms of the σ-finite
  `μ_V`, hence countable, and singletons are graphs.
- **`n ≥ 1`.** Each such `x` satisfies two estimates:
  - the lower mass bound `c t^n ≤ μ_V(B_t(x))` for small `t` and every `c < θ ω_n`
    (`tgc_tangent_weight_lower_bound`, from the weight blow-ups `tgc_weight_blowup_tendsto` and
    `H^n(T ∩ B_r) = ω_n r^n`);
  - the cone decay `μ_V{y ∈ B_t(x) : (L/16)|y−x| ≤ |q_T(y−x)|} = o(t^n)`
    (`tgc_tangent_cone_weight_decay`; the rescaled cone meets `T` only at `0`, an `H^n`-null set).

  `tgc_cone_density_graph_cover` (Simon Ch. 3, 1.6, printed (7)–(10)) turns these two estimates into
  the cover. Its three ingredients are:
  - uniformizing the eventual bounds on countably many classes (`tgc_eventual_density_bounds_uniform`,
    replacing Egoroff);
  - the tilted-cone linear algebra `tgc_tilted_cone_inclusion`: a pair violating the `L`-graph
    inequality over `P` puts a ball of comparable mass inside the `T`-cone;
  - localization to closed graph pieces (`tgc_local_graph_closed_cover`).

*Uses:* no sibling.

### 3.6 `density_semicontinuity_theorem` — Simon 3.7

**Statement.** Suppose `V_i → V`, `liminf ‖δV_i‖(W) < ∞`, and `Θ^n(μ_{V_i}, ·) ≥ 1` off `B_i` with
`μ_{V_i}(B_i ∩ W) → 0`. Then `V` has locally bounded first variation,
`‖δV‖(W) ≤ liminf ‖δV_i‖(W)`, and `Θ^n(μ_V, ·) ≥ 1` `μ_V`-a.e.

**Proof.**

1. `variationMeasure_le_liminf_of_radonConverges` (Remark 3.8(1)). On open `W ⊂⊂ U`, `‖δV‖(W)` is
   the supremum 2.5. Radon convergence gives `δV_i(X) → δV(X)`, since `div_S X ∈ C_c`. A supremum
   of limits is at most the `liminf` of the suprema. The SimonGMT lemmas
   `RadonConverges.hasLocallyBoundedFirstVariation` and `RadonConverges.firstVariationNormOn_le_liminf`
   (`Chapter08/VarifoldConvergence.lean`) and `firstVariationRieszMeasure_eq_norm`
   (`Chapter08/FirstVariationRiesz.lean`) give both conclusions.
2. `lower_density_ge_one_ae_of_radonConverges` (printed (1)–(5)) shows
   `liminf_{ρ↓0} μ_V(B_ρ(y))/(ω_nρ^n) ≥ 1` for `μ_V`-a.e. `y`:
   - Fix `W ⊂⊂ U`. A point of `W ∖ B_q` is good for `(q, k)` if `‖δV_q‖ ≤ k μ_q` on its balls of
     radius `< ρ₀`.
   - `besicovitch_ratio_cover_estimate` bounds the bad points by `C k^{-1}‖δV_q‖(W̃) + μ_q(B_q ∩ W)`.
     The points interior to the bad sets for all `k` therefore form a `μ_V`-null set
     (`measure_bad_interior_exceptional_eq_zero`).
   - Every other `x` is a limit of good points `y_i` (`exists_nearby_points_off_bad_sets`). There,
     3.3 with `Λ = k` gives `μ_{q_i}(B_ρ(y_i)) ≥ e^{−kρ} ω_n ρ^n`
     (`weight_closedBall_lower_bound_of_density_ge_one`).
   - The portmanteau inequality (`weight_portmanteau_of_radonConverges`) carries this bound to `μ_V`
     at `x` (`lower_density_ge_one_of_nearby_mass_bounds`).
   - Countably many `W` exhaust `U` (`exists_thickening_isRelCompactOpenIn`,
     `ae_of_forall_relCompactOpen_null_exceptional`).
3. 3.6 for `V` (§3.2) gives that the density exists a.e. Where it exists it equals that `liminf`, so
   it is `≥ 1`.

*Uses:* `monotonicity_and_density_theorems` (3.3 and 3.6).

### 3.7 `constancy_theorem` — Simon 4.1, corrected

**Statement.** Let `V` be stationary in `U` with `U ∩ spt μ_V ⊆ M`, where `M` is an `n`-dimensional
`C²` Simon submanifold and `M ∩ U` is preconnected. Then
`V(A) = θ₀ H^n{x ∈ M ∩ U : ∃ S, S.plane = classicalTangentSpace M x ∧ (x, S) ∈ A}` with `θ₀ ≥ 0`.

**Proof.** If `M = ∅`, then `V` is carried by `U ∩ spt μ_V = ∅`, so `V = 0` and `θ₀ = 0`.
Otherwise `stationary_constancy_tangentGraph_measure` gives `c < ∞` and a Borel `T` with
`V = (c H^n ⌞ (M ∩ U)).map(x ↦ (x, T x))`, and `(T x).plane = classicalTangentSpace M x` when
`c ≠ 0`. Take `θ₀ = c`: a point of `G(N, n)` is determined by its plane, so the two sets coincide.

The Lean proof of `stationary_constancy_tangentGraph_measure` is self-contained. It uses only
SimonGMT's chart API, its Lipschitz image bound and its Jacobian derivative (Appendix B), not
SimonGMT's constancy lemmas. It has five steps:

1. **Support planes are chart tangent planes (printed (1)–(3)).** Let `(x, S) ∈ spt V` with
   `x ∈ U`, and let `φ` be a Simon chart with `φ(a) = x`. Take a `C²` local left inverse `ψ` of
   `φ`, so that `F = id − φ∘ψ` vanishes on `M` near `x`. Cut-offs `f = ζ F_j` vanish on `M ∩ U`, so
   `0 = δV(f∇f) = ∫ |p_S ∇f|² dV`. Hence `p_S` kills `(range Dφ(a))^⊥`. Dimension count then gives
   `S = range Dφ(a)`.
2. **`V` is a graph measure (printed (4)).** Each fibre over `x ∈ U ∩ spt μ_V` is therefore a single
   plane `T(x)`. The map `T` is continuous there (closed graph into the compact `G(N, n)`) and is
   extended to a Borel map. Then `V = μ_V.map(x ↦ (x, T x))`.
3. **Local constancy (replaces printed (5) and the last paragraph).** For `x₀ ∈ M ∩ U` take a chart
   `φ` with `φ(a) = x₀`, its local inverse `ψ`, and the area Jacobian `J = normDet(Dφ)`, which is
   positive near `a`.
   - Pull `μ_V` back to the parameter ball: `ϑ = ψ_#(μ_V ⌞ O)`.
   - Take the tangential test fields `X = Dφ(Y)∘ψ` with `Y(w) = (ζ(w)/J(w)) v`, for `C¹` functions
     `ζ` supported near `a` and directions `v`.
   - A coordinate divergence identity gives `∫ (1/J) ∂_v ζ dϑ = 0`. That identity is the derivative
     of `normDet` along `Dφ + t·D(Dφ·Y)`, through SimonGMT's
     `hasDerivAt_tangentialJacobianReal_id_add_smul`, together with stationarity.
   - A weighted distributional constancy lemma (proved in place by translation invariance and a
     mollifying bump) gives `ϑ = c J dw` on a smaller ball.
   - The area formula on the chart ball (using SimonGMT's
     `euclideanHausdorffMeasure_image_le_of_lipschitzOn`) turns this into
     `μ_V ⌞ O = c H^n ⌞ (M ∩ O)` on an open `O ∋ x₀`. Moreover `H^n(M ∩ O) < ∞` and
     `H^n(M ∩ O' ∩ O) > 0` for every open `O' ∋ x₀`.
4. **Gluing.** On overlaps the two local descriptions of `μ_V(O_x ∩ O_y)` have positive finite
   `H^n`-factors, so the constants agree. The points with a given constant and those without it are
   relatively open, disjoint, and cover `M ∩ U`. Preconnectedness of `M ∩ U` therefore makes the
   constant global. A countable subcover then gives `μ_V = c H^n ⌞ (M ∩ U)`.
5. **Assembly.** If `c ≠ 0`, every `x ∈ M ∩ U` lies in `spt μ_V`, so
   `T(x) = range Dφ(a) = classicalTangentSpace M x` by `simon_chart_classicalTangentSpace_eq_range`
   (Simon Ch. 2, 4.3).

This route needs neither the monotonicity formula nor the absolute continuity `μ_V ≪ H^n ⌞ M` used
in the reviewed outline's step 4.

*Uses:* no sibling.

### 3.8 `varifold_tangent_theorems` — Simon 5.1–5.4 (corrected), and the blow-up density lower bound

**Statement.** Two conjuncts.

- **First.** Assume locally bounded first variation, `x ∈ U`, `Θ^n(μ_V, x) = θ₀ > 0` and
  `ρ^{1−n}‖δV‖(B_ρ(x)) → 0` (5.1). Then:
  - every `λ_j → 0` has a subsequence along which `V_{x,λ_j}` converges;
  - every `C ∈ VarTan(V, x)` is stationary, with `μ_C(B_ρ(0)) = θ₀ ω_n ρ^n` and
    `μ_C(sA) = s^n μ_C(A)`.
- **Second.** If in addition `ρ^{-n} μ_V{y ∈ B_ρ(x) : Θ^n(μ_V, y) ≥ τ fails} → 0`, then
  `Θ^n(μ_C, ·) ≥ τ` `μ_C`-a.e. for every `C ∈ VarTan(V, x)`.

**Proof.**

1. **(5.1) Extraction.** `varifold_tangents_rescaled_ball_mass_tendsto` gives
   `V_{x,t}(B_R(0) × G) = t^{-n} μ_V(B_{tR}(x)) → θ₀ ω_n R^n`. So the masses on compact sets are
   eventually bounded, and §3.3 on `U = ℝ^N` extracts a convergent subsequence.
2. **(5.4) Stationarity.** `varifold_tangents_limit_stationary`. For `X ∈ K(ℝ^N)`,
   `∫ div_S X dV_{x,t_j} → δC(X)`. The rescaled divergence bound
   `varifold_tangents_rescaled_divergence_bound` gives
   `|∫ div_S X dV_{x,t}| ≤ M R^{n−1}(tR)^{1−n}‖δV‖(B_{tR}(x)) → 0`.
3. **(5.2) Ball masses.** `varifold_tangents_limit_ball_mass`, by vague-convergence bounds on
   cylinders and `ρ' ↓ ρ`.
4. **(5.3) Homogeneity.** The ratio `μ_C(B_R(0))/R^n` is constant. SimonGMT's radial rigidity
   `Stationary.ae_normalProject_eq_zero_of_constant_mass_ratio` (the equality case of 3.4,
   `Chapter08/TangentRadialRigidity.lean`) gives `y ∈ S` for `C`-a.e. `(y, S)`. Then
   `varifold_tangents_radial_stationary_homogeneous` tests `δC = 0` against `g(y)y`. This gives
   Euler's identity `∫ (n g + Dg(y)·y) dμ_C = 0`, hence the dilation law
   `∫ g(s^{-1}y) dμ_C = s^n ∫ g dμ_C` for `C¹_c` functions. Mollification extends the law to `C_c`,
   and Riesz uniqueness turns it into `μ_C(sA) = s^n μ_C(A)` for every set `A`.
5. **Density lower bound.** `varifold_tangents_density_lower_bound`, the use of 3.7 in 5.5 and 5.7.
   - On `Ω = B°_R(0)` the varifolds `W_i = τ^{-1} V_{x,t_i} ⌞ (Ω × G)` converge to
     `τ^{-1} C ⌞ (Ω × G)`.
   - `‖δW_i‖(O) = O(ρ^{1−n}‖δV‖(B_ρ(x))) → 0`.
   - `Θ^n(μ_{W_i}, ·) ≥ 1` off the rescaled bad set, whose mass in `O` is
     `O(ρ^{-n} μ_V(bad ∩ B_ρ(x))) → 0`.
   - §3.6 then gives `Θ^n(μ_C, ·) ≥ τ` `μ_C`-a.e. on `Ω`, for every `R`.

*Uses:* `varifold_radon_compactness`, `density_semicontinuity_theorem` (and through it
`monotonicity_and_density_theorems`).

### 3.9 `first_rectifiability_theorem` — Simon 1.2

**Statement.** If `V` has a tangent plane with positive multiplicity at `μ_V`-a.e. `x`, put
`M = {x ∈ spt μ_V : a tangent plane exists at x}`, with `θ(x)` its multiplicity. Then `M` and `θ`
satisfy `IsVarifoldOf V M θ`, and `θ(x)` is a tangent multiplicity at each `x ∈ M`.

**Proof.**

- **Density and uniqueness at tangent points.** At a tangent point, `Θ^n(μ_V, x) = θ(x)` (`frt_tangent_plane_hasDensity`; weight
  blow-ups, `H^n(T ∩ B_r) = ω_n r^n`). The plane and multiplicity are unique
  (`frt_tangent_plane_unique`).
- **Flat graph covers.** For every `L ∈ (0, 1]`, countably many closed `L`-flat graphs, each paired with its
  base plane, cover all tangent points (`frt_tangent_points_flat_graph_cover`). A countable dense
  set of planes is combined with §3.5.
- **Rectifiability.** With `L = 1`, `M` is countably `n`-rectifiable (`frt_countablyRectifiable_of_graph_cover`):
  `p_P` is injective on a `1`-graph with a `√2`-Lipschitz inverse.
- **Measurability.** `M` is `H^n`-null-measurable (`frt_carrier_nullMeasurable`), via uniform lower
  density classes and closures.
- **Weight identity.** `μ_V = θ H^n ⌞ M`, with `θ` locally `H^n`-integrable (`frt_weight_eq_multiplicity_hausdorff`).
  - `H^n`-null sets are `μ_V`-null (`frt_weight_null_of_hausdorff_null`, by finite density and
    covering).
  - `μ_V`-null subsets of `M` are `H^n`-null (`frt_hausdorff_null_of_weight_null`).
  - On graph pieces of small slope, `H^n` has density one
    (`frt_hausdorff_density_one_of_flat_covers`, via Lipschitz image bounds and the Lebesgue density
    theorem).
  - Besicovitch differentiation and Radon–Nikodym then identify the density
    (`frt_weq_piece_restrict_eq_density`, `frt_weq_mul_hausdorff_le_of_upper_density`).
- **Approximate tangent planes.** The tangent planes of `V` are the weighted approximate tangent planes of `(M, θ)`
  (`frt_weighted_approx_tangent`).
- **Graph measure.** Lemma 1.3 (§3.4), with the corrected identity `η_V^(x)(β) = β(T_x)` at tangent points,
  gives `V(A) = μ_V{x : (x, T_x) ∈ A}` (`frt_varifold_eq_tangent_graph_measure`, via a measurable
  plane selection).
- **Assembly.** Together these give `IsVarifoldOf`.

*Uses:* `plane_disintegration`, `tangent_points_lipschitz_graph_cover`.

### 3.10 `allard_rectifiability_and_tangent_cones` — Simon 5.5, 5.6 and 5.7

**Part A (5.5, 5.6): `allard_tc_rectifiability`.** Let `V` have locally bounded first variation and
`Θ^n(μ_V, ·) > 0` a.e. At `μ_V`-a.e. `x` the following hold together:

- `θ₀ = Θ^n(μ_V, x) ∈ (0, ∞)` exists (3.6);
- `D_{μ_V}‖δV‖(x) < ∞` (2.7), which gives 5.1;
- the `β`-averages converge (1.3);
- the density decay of `allard_tc_density_blowup_decay` holds. That lemma follows Remark 5.6(iii)
  and the Lebesgue density theorem (`allard_tc_dbd_lebesgue_density`,
  `allard_tc_dbd_relative_decay`).

At such `x`, the density lower bound of §3.8 with `τ_k ↑ θ₀` gives `Θ^n(μ_C, ·) ≥ θ₀` `μ_C`-a.e.
for every `C ∈ VarTan(V, x)`.

`allard_tc_stationary_cone_flat` shows that such a stationary cone with `μ_C(B_ρ(0)) = θ₀ω_nρ^n` is
`θ₀ v(T)`:

- 3.4 at every centre gives `R(y, ρ) ≤ θ₀` everywhere and `≥ θ₀` on `spt μ_C`;
- so the normal defect vanishes and `spt μ_C ⊆ T`;
- Constancy 4.1 (§3.7) on the plane gives `C = θ v(T)`;
- the unit-ball mass gives `θ = θ₀`.

`allard_tc_unique_tangent_plane` then shows that the tangent cone is unique, so `V` has a tangent
plane at `x` (Definition 1.1). It uses the flat blow-up ball limits `allard_tc_flat_blowup_ball_limits`
and point separation in `G(N, n)`. The First Rectifiability Theorem (§3.9) gives rectifiability.

**Part B (5.7): `allard_tc_tangent_cones_rectifiable`.**

1. The density lower bound with `τ = 1` gives `Θ^n(μ_C, ·) ≥ 1` a.e.
2. `C` is stationary (5.4), so Part A applied to `C` makes it rectifiable, with tangent planes a.e.
3. `allard_tc_tangent_point_representation` represents `C = v(M, θ)` by those tangent planes.
4. `allard_tc_cone_rescaling_invariance` combines the homogeneity 5.3 with the plane dilation lemma
   `allard_tc_tangent_plane_dilation` and full-measure carrier comparisons. This gives
   `η_{0,s#}C = C` for `s > 0`.

*Uses:* `first_variation_theorems` (2.5–2.10), `monotonicity_and_density_theorems` (3.4, 3.6),
`constancy_theorem`, `varifold_tangent_theorems` (both conjuncts), `plane_disintegration`,
`first_rectifiability_theorem`.

### 3.11 `compactness_theorem` — Simon 5.8

1. The uniform bounds `sup_j (μ_{V_j}(W) + ‖δV_j‖(W)) < ∞` on an open `W ⊂⊂ U` around each compact
   `K` let §3.3 extract `V_{φ(j)} → V`.
2. Zero extension of test functions on `Gₙ(U)` turns this into `RadonConverges`.
3. §3.6 along the subsequence (its `liminf` hypothesis follows from the uniform bound) gives three
   things: locally bounded first variation, `‖δV‖(W) ≤ liminf_j ‖δV_{φ(j)}‖(W)`, and
   `Θ^n(μ_V, ·) ≥ 1` a.e.
4. Allard 5.5 (§3.10, Part A) makes `V` rectifiable.

The rectifiability of the `V_j` is not needed.

*Uses:* `varifold_radon_compactness`, `density_semicontinuity_theorem`,
`allard_rectifiability_and_tangent_cones`.

### 3.12 `integral_compactness_theorem` — Simon 5.9

**Remark 5.9 (`intcpt_integral_density_integer`).** An integral varifold has
`Θ^n(μ_V, x) ∈ {1, 2, …}` `μ_V`-a.e. The proof combines the tangent-point density (Ch. 3, Remark
1.8(2)) with Ch. 1, 3.6 for the complement of a Borel hull. So the exceptional sets
`{Θ^n ≥ 1 fails}` are null.

**Existence.** 5.8 (§3.11) with these null exceptional sets gives the convergent subsequence, the
locally bounded first variation and the `liminf` bound.

**Every subsequential limit `V` is integral.** By §3.6, `V` has locally bounded first variation and
`Θ^n ≥ 1` a.e. `intcpt_canonical_tangent_representation` (Allard 5.5 + 1.2) gives
`V = v(M, θ)` with a tangent plane of multiplicity `θ(ξ)` at each `ξ ∈ M`. It also shows that
`μ_V`-null subsets of `M` are `H^n`-null.

`intcpt_variation_liminf_density_bound` (printed (1)–(2), Besicovitch) gives
`liminf_i ‖δV_i‖(B_ρ(ξ)) ≤ cρ^n` for small `ρ` at `μ_V`-a.e. `ξ`. At such `ξ ∈ M`:

1. `intcpt_diagonal_integral_blowup` (printed (3)–(4)) chooses scales `λ_k ↓ 0` and indices `i_k`.
   The blow-ups `W_k = (V_{i_k})_{ξ,λ_k} ⌞ B°_5(0)` are integral, with `‖δW_k‖ → 0`, and
   `W_k → θ(ξ) v(T_ξ)`.
2. `intcpt_flat_limit_integer_multiplicity` (the repaired step B6) shows `θ(ξ) ∈ ℕ`.
   - For `n = 0`, weights are integer point masses (`intcpt_fli_dim_zero_integer`).
   - For `n ≥ 1`, with `k₀ = ⌊θ₀⌋`, the flat claim `intcpt_fli_flat_claim` gives
     `θ₀ I₀ ≤ c₀ δ⁴ + (1 + (4δ⁴/ω_n)²)^{n/2} k₀ I₀` for small `δ`, hence `θ₀ ≤ k₀`.

   The flat claim combines:
   - Allard's integrality lemma 5.10/5.11 (`intcpt_allard_integrality_lemma`). Its bad set has mass
     `≤ c₀ε`, and on good fibres `Σ Θ ≤ (1+δ)ω_n^{-1}μ(B_1(x)) + δ`, proved through the
     cylinder-monotonicity and Besicovitch estimates `intcpt_allard_*`.
   - The tangent tilt bound `‖p_T − p_P‖ ≤ ε/ω_n` at good points (`intcpt_fli_tangent_tilt_bound`).
   - The tangent-graph cover (§3.5), which puts the good points on `4ε/ω_n`-Lipschitz graphs over
     `P`.
   - The Lipschitz-graph fibre bound `∫_G g dH^n ≤ (1+L²)^{n/2} ∫_P Σ_fibre g dH^n`
     (`intcpt_lipschitz_graph_fibre_bound`). It is used in place of the area formula on rectifiable
     carriers.
3. So `{θ ∉ ℕ} ∩ M` is `μ_V`-null, hence `H^n`-null, and `V` is integral.

*Uses:* `monotonicity_and_density_theorems`, `density_semicontinuity_theorem`,
`first_rectifiability_theorem`, `tangent_points_lipschitz_graph_cover`,
`allard_rectifiability_and_tangent_cones`, `compactness_theorem`.

## 4. Dependency structure and absence of circularity

**Actual Lean usage among the twelve root children.** The table lists direct uses: the child's
proof term names the sibling. Transitive uses follow by composing rows.

| Child | Siblings used directly |
|---|---|
| `first_variation_theorems` | — |
| `monotonicity_and_density_theorems` | — |
| `varifold_radon_compactness` | — |
| `plane_disintegration` | — |
| `tangent_points_lipschitz_graph_cover` | — |
| `constancy_theorem` | — |
| `density_semicontinuity_theorem` | `monotonicity_and_density_theorems` |
| `varifold_tangent_theorems` | `varifold_radon_compactness`, `density_semicontinuity_theorem` |
| `first_rectifiability_theorem` | `plane_disintegration`, `tangent_points_lipschitz_graph_cover` |
| `allard_rectifiability_and_tangent_cones` | `first_variation_theorems`, `monotonicity_and_density_theorems`, `constancy_theorem`, `varifold_tangent_theorems`, `plane_disintegration`, `first_rectifiability_theorem` |
| `compactness_theorem` | `varifold_radon_compactness`, `density_semicontinuity_theorem`, `allard_rectifiability_and_tangent_cones` |
| `integral_compactness_theorem` | `monotonicity_and_density_theorems`, `density_semicontinuity_theorem`, `first_rectifiability_theorem`, `tangent_points_lipschitz_graph_cover`, `allard_rectifiability_and_tangent_cones`, `compactness_theorem` |

**No circularity.** Every declaration in `Submission.lean` refers only to declarations earlier in the
file. Lean elaborates top-level declarations in order, and the file has no `mutual` block, `partial`
or `axiom`. So the usage relation is a well-founded DAG.

The longest dependency chain from `main_theorem` has 12 declarations. The 241 accepted declarations
plus `main_theorem` are all reachable from `main_theorem`; none is unused. Appendix A lists every
declaration, grouped by the accepted DAG node that introduced it.

## 5. Library reuse and provenance

**Mathlib** (`25730c7c`, pinned). Standard measure theory and analysis is used throughout. Notable
uses:

- Riesz–Markov–Kakutani: `RealRMK.rieszMeasure` and `RealRMK.integral_rieszMeasure`, in
  `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean` (§3.3, §3.4).
- Besicovitch/Vitali covering and differentiation (`Mathlib/MeasureTheory/Covering/*`):
  `Besicovitch.exist_disjoint_covering_families`, `Besicovitch.ae_tendsto_rnDeriv`,
  `Besicovitch.ae_tendsto_measure_inter_div` and
  `Vitali.exists_disjoint_subfamily_covering_enlargement(_closedBall)`.
- Hausdorff measure `μHE[n]` and its normalization on Euclidean spaces.
- Radon–Nikodym and Lebesgue decomposition.
- Stone–Weierstrass, used through
  `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`.
- `EuclideanSpace.volume_ball`.
- `Real.Gamma`.

**SimonGMT** (`simongmt` package, `2b3663083f3fe399b6296fb8eaee52169170e197`, the
`simongmt-library` branch of `ZhengyangZhang06/gmt-formalize`). This is an earlier, kernel-checked
partial formalization of the same book, whose reuse the task explicitly allows.

- **Definitions.** The contract itself imports SimonGMT and uses the definitions listed in the
  README: `Varifold`, `Grassmannian`, `weight`, `firstVariation`, `tangentialDivergence`,
  `HasLocallyBoundedFirstVariation`, `IsFirstVariationMeasure`, `firstVariationRieszMeasure`,
  `Stationary`, `RadonConverges`, `pushforwardMeasure`, `Chapter03.CountablyRectifiable`,
  `HasWeightedApproximateTangentSpaceAt` and `Chapter02.IsSimonSubmanifold`.
- **Theorems.** The 241 child proofs use SimonGMT theorems directly, each by name, as listed in
  Appendix B.

Appendix B was obtained from the compiled environment, not from a text search. For every constant of
module `GMT.Ch08.Submission` (466 including auxiliary `_proof_`/`match_` constants), the query read
its type and value and listed the constants belonging to `Poincare.*` modules. It found 174 distinct
SimonGMT constants in 23 modules. The query file is not part of the candidate.

The README marks one SimonGMT definition as unfaithful: the structure `Chapter04.RectifiableVarifold`.
It is not used. The proof does use eight constants from the namespace
`Poincare.SimonGMT.Chapter04.RectifiableVarifold`: `monotonicityCutoff`, `scaledRadialCutoff`,
`scaledRadialCutoffDeriv`, and lemmas about them. They are plain real-variable cutoff functions,
`monotonicityCutoff ε t = 1 − smoothTransition((t−1)/ε)` and
`scaledRadialCutoff ξ φ ρ x = φ(‖x−ξ‖²/ρ²)`, and do not mention the structure. They are used only in
§3.3's proof of 3.3.

Every SimonGMT theorem enters only through its statement, with no further assumption. The axioms of
`main_theorem`, which include everything SimonGMT and Mathlib contribute, are exactly `propext`,
`Classical.choice` and `Quot.sound` (§8).

## 6. Historical decomposition versus the lemmas actually used

The following records are history and are not modified by this commit.

**Records of this run** (under `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/`):

- `nodes/root/natural-proof-source.md`: the operator-supplied pointer to the published proof.
- `nodes/root/plan-source.md`, `nodes/root/plan-v1.md`, `nodes/root/rlcr-plan-v2.md`.
- `nodes/root/decomposition-v1.json` and `-v2.json`, with their audits and review receipts.

**Committed copies:**

- `.humanize-workspace/20261011t141839z-af4f31741f/root/decomposition.json`: the accepted v2
  decomposition. It records the repairs of the rejected v1 audit, the errata and the planned parent
  term.
- `.humanize-workspace/20261011t141839z-af4f31741f/*/children/*/parent-supplied-natural-proof.md`:
  each child's reviewed proof.

The formal proof follows the accepted v2 decomposition. The root term in §2 is exactly the planned
parent term. The formal route differs from the plan in two ways.

1. The proof of `stationary_constancy_tangentGraph_measure` replaces the outline's step 4
   (monotonicity, `μ_V ≪ H^n ⌞ M`, Radon–Nikodym) and its last paragraph by the chart pull-back and
   distributional constancy argument of §3.7. The statement is unchanged.
2. Several Lean proofs use fewer dependencies than were declared. In each case the omitted fact
   enters through a pinned SimonGMT lemma or is not needed:

| Node | Declared `depends_on` not used by its Lean proof |
|---|---|
| `constancy_theorem` | `monotonicity_and_density_theorems`: not needed; the chart pull-back and distributional constancy argument of §3.7 replaces the outline's monotonicity/absolute-continuity step |
| `monotonicity_and_density_theorems` | `first_variation_theorems`: 2.6/2.7 enter through SimonGMT `FirstVariationRiesz` lemmas |
| `density_semicontinuity_theorem` | `first_variation_theorems`: same reason |
| `varifold_tangent_theorems` | `first_variation_theorems`: same reason |
| `allard_tc_tangent_point_representation` | `allard_tc_tangent_plane_dilation`: used instead by its sibling `allard_tc_cone_rescaling_invariance` |
| `frt_varifold_eq_tangent_graph_measure` | `frt_tangent_plane_unique`, `frt_tangent_plane_hasDensity`: used instead directly by `first_rectifiability_theorem` |

No accepted declaration is unused. Some nodes are shared between subtrees, for example
`frt_weq_density_borel_representative` (§3.2, §3.9) and `radon_exists_measure_of_tendsto_integral`.
Each is declared once and used from every place that needs it.

## 7. Integration repair made in this candidate

The previous candidate `029cab4a` was produced by merging the accepted checkpoints and the
speculative root draft `ec9516b7`. It was rejected by the comparator (`nodes/root/comparator-v1.log`)
for three merge defects, which commit `4c30aa30` repairs:

1. **Duplicate `frt_hnw_unitBallVolume_eq_gamma`.** It was declared twice. The first copy was
   followed by a line-merged duplicate of the last 40 lines of `varifold_tangents_density_lower_bound`
   (errors "No goals to be solved" and "has already been declared"). The first copy and the
   duplicated tail were removed; the clean second copy remains.
2. **Duplicate `radon_exists_measure_of_tendsto_integral`.** It was declared twice. The second copy
   was followed by a duplicate of the last 43 lines of `plane_disint_pointwise_measure`. The second
   copy and the duplicated tail were removed; the clean first copy remains.
3. **Two `main_theorem` declarations.** The frozen `main_theorem := by sorry` and the speculative
   proof both stood before five of the children they use. Both lines were removed, and
   `main_theorem` is stated once, at the end of the file, with the speculative proof term (§2).

The two import lines duplicated by the merges were also dropped; the same modules are still
imported once. The two tails that were removed are verbatim copies of text that remains in place in
the declarations they came from. So no accepted declaration lost any text. §8 confirms this
mechanically.

## 8. Verification record

- **Comparator.** The exact configured comparator command (`gmt-compare.py … --frozen-commit
  63436ae63eb6… root`) was run on candidate `4c30aa308c61cecff7333e1dbba798535004f9ae`, tree
  `6089fb48…`, with `Submission.lean` sha256 `d8043fa0cc87843a5c8f8fc2282558b59698a3def3f83e6211ea400382e7d984`.
  - Output: `GMT comparator: comparator and Lean kernel accepted GMT.Ch08.main_theorem`, then
    `Your solution is okay!`.
  - Receipt: status `passed`; checks `exit_zero`, `lean_kernel_accepted` and `final_marker` all true;
    no post-check failures; verdict key `cbfdc21c9b4424d5d0cdef99315813e6120d5bd42926e695796babee02a717c2`.
  - Evidence: `cluster-state/verification/results/hoa53/20261013T093244Z-ch08-root-ll3cbvzn/`.
  - The only `sorry` in the log is the challenge's own (`GMT/Ch08/Contract.lean:413`).

  The comparator compares `main_theorem` and every definition it depends on against the frozen
  contract, replays the Lean kernel, and permits only `propext`, `Quot.sound` and
  `Classical.choice`.
- **Independent private build.** `lake env lean -o` was run on `Submission.lean` in a private
  `/tmp` copy that links the shared package tree. It reported no errors and no `sorry`. In the
  resulting environment, `#print axioms GMT.Ch08.main_theorem` prints
  `[propext, Classical.choice, Quot.sound]`.
- **Child interfaces.** The 241 accepted nodes are the DAG's `theorems`/`lean_statement` entries. A
  script checked each of them:
  - its name occurs exactly once;
  - its type equals the frozen `lean_statement` up to whitespace;
  - its full text equals the corresponding declaration in the node's accepted `candidate_commit`.

  All 241 passed. There are no duplicate declaration names and no `sorry`/`admit` tactic.
- **Ordering.** No `Submission.X` reference in code points forward. The single textual forward
  mention is inside a `--` comment.

## 9. reference_use

```json
[
  {
    "source": "local-project",
    "snapshot": ".humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346",
    "manifest": {"mode": "local-project", "project_commit": "63436ae63eb6a2fd7525bef73c73cf88e2cd7e93", "mathlib_commit": "25730c7c759d108ef87ab70af2342a196760f79d"},
    "queries": [
      "cat manifest.json",
      "rg -n 'main_theorem' project/GMT/",
      "rg -n 'first_rectifiability_theorem|varifold_radon_compactness|integral_compactness_theorem|allard_rectifiability_and_tangent_cones|first_variation_theorems|monotonicity_and_density_theorems' project/",
      "cmp project/GMT/Ch08/Contract.lean project/GMT/Ch08/Submission.lean; cmp project/GMT/Ch08/Contract.lean <worktree>/GMT/Ch08/Contract.lean",
      "rg -n 'Submission\\.' project/GMT/Ch08/",
      "rg -n 'theorem integral_rieszMeasure|def rieszMeasure' mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/"
    ],
    "findings": [
      "project/GMT/Ch08/Contract.lean:413 and project/GMT/Ch08/Submission.lean:413: `theorem main_theorem … := by sorry`; the snapshot's Ch08 Submission is a byte copy of the Contract (cmp silent) and the snapshot Contract is byte-identical to the worktree's frozen Contract.",
      "No match for any child theorem name (first_rectifiability_theorem, varifold_radon_compactness, …) anywhere in project/: the snapshot contains no prior proof of this chapter; every Lean proof used here comes from the run's accepted nodes.",
      "project/GMT/Ch08/README.md:4,104: the only `Submission.` occurrences, describing the byte copy.",
      "mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean:65 `noncomputable def rieszMeasure`, :345 `theorem integral_rieszMeasure (f : C_c(X, ℝ)) : ∫ x, f x ∂(rieszMeasure Λ) = Λ f` — the Riesz–Markov–Kakutani step reused by `radon_exists_measure_of_tendsto_integral` and `plane_disint_riesz_limit`; compatible (same Mathlib commit as lake-manifest.json) and axiom-checked through `#print axioms GMT.Ch08.main_theorem`."
    ],
    "use": "Contract identity, absence of prior proofs, and provenance of the reused Mathlib Riesz–Markov–Kakutani declarations; no snapshot declaration was copied."
  }
]
```

No network sources were used for this implementation step; the mathematics is that of Simon's
book as recorded in the accepted child proofs.

## Appendix A. Catalogue of the accepted declarations

Every accepted DAG node of this run, in tree order (parent before children; a node reached again through a second parent is listed only at its first position, and a later "see above" line marks its reuse). For each: the globally qualified name, the DAG node, the statement and proof as recorded in its Lean doc comment (the frozen type is the node's `lean_statement`; all were checked equal to the file), the accepted descendants its proof calls directly, and the declarations that call it. All names are in namespace `GMT.Ch08`; `S.` abbreviates `GMT.Ch08.Submission.`.

### `S.first_variation_theorems`

- Node: `root.first_variation-a1`; accepted candidate `3a1a0900b103`
- Statement and proof: **Simon Ch. 8, 2.2–2.10** (child `first_variation` of `main_theorem`): the mass derivative of a deformation is `δV(X)` (2.2–2.4), and locally bounded first variation gives `‖δV‖`, the polar field, the density `D_{μ_V}‖δV‖`, the generalized boundary and the decomposition 2.10 (2.5–2.10). Both parts are SimonGMT's kernel-checked theorems; `variationMeasure V` unfolds to its Riesz measure, which turns the contract's density, boundary and mean curvature into SimonGMT's symmetric ones.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_rectifiability_and_tangent_cones`, `main_theorem`

### `S.monotonicity_and_density_theorems`

- Node: `root.monotonicity_density-a1`; accepted candidate `d74280205bb9`
- Statement and proof: **Simon Ch. 8, 3.3, 3.4 and 3.6** (child `monotonicity_density` of `main_theorem`): the monotonicity formula under `‖δV‖ ≤ Λ μ_V` (3.3), the stationary monotonicity identity (3.4), and the `μ_V`-a.e. existence and finiteness of `Θ^n(μ_V, ·)` with a Borel representative (3.6). Each conjunct is its own child theorem; 3.6 is derived there from 3.3 and the a.e. bound 3.1.
- Calls: `S.density_exists_ae_8_3_6`, `S.monotonicity_formula_8_3_3`, `S.stationary_monotonicity_identity_8_3_4`
- Called by: `S.density_semicontinuity_theorem`, `S.allard_rectifiability_and_tangent_cones`, `S.integral_compactness_theorem`, `main_theorem`

#### `S.monotonicity_formula_8_3_3`

- Node: `root.monotonicity_density-a1.monotonicity_formula-a1`; accepted candidate `8a2840f9496c`
- Statement and proof: **Simon Ch. 8, 3.3 (monotonicity formula with `‖δV‖ ≤ Λ μ_V`), p. 210.** If `V` has locally bounded first variation, `B°_{ρ₀}(x) ⊆ U`, `Λ ≥ 0` and `‖δV‖(B_ρ(x)) ≤ Λ μ_V(B_ρ(x))` for `0 < ρ < ρ₀`, then `e^{Λρ} ρ^{-n} μ_V(B_ρ(x))` is increasing on `(0, ρ₀)`, `Θ^n(μ_V, x)` exists and is finite, and for `0 < σ ≤ ρ < ρ₀` it is bounded by `e^{Λσ} ω_n^{-1} σ^{-n} μ_V(B_σ(x))`, while `e^{Λσ} ω_n^{-1} σ^{-n} μ_V(B_σ(x))` plus `ω_n^{-1} ∫_{Gₙ(B_ρ(x) ∖ B_σ(x))} r^{-n-2} |p_{S^⊥}(y - x)|² dV` is at most `e^{Λρ} ω_n^{-1} ρ^{-n} μ_V(B_ρ(x))`. For each smooth cutoff `φ_ε` (SimonGMT's `monotonicityCutoff ε`) the radial identity (★) for `I(t)/tⁿ` (SimonGMT's `hasDerivAt_normalized_weightedCutoffMass` with weight `h ≡ 1`) and the bound `|δV(X_t)| ≤ (1 + ε) Λ t I(t)` (`mono833_radial_first_variation_bound`) feed the integrating-factor comparison `mono833_integrating_factor_comparison` on `[σ, ρ]`; letting `ε ↓ 0` by dominated convergence gives the annular inequality, and `mono833_exp_weighted_density_limit` gives the density.
- Calls: `S.mono833_exp_weighted_density_limit`, `S.mono833_integrating_factor_comparison`, `S.mono833_radial_first_variation_bound`
- Called by: `S.density_exists_ae_8_3_6`, `S.monotonicity_and_density_theorems`

##### `S.mono833_radial_layer_cake_le`

- Node: `root.monotonicity_density-a1.monotonicity_formula-a1.radial_layer_cake-a1`; accepted candidate `a5480bd91e20`
- Statement and proof: Layer-cake comparison of radial cutoff integrals (Simon Ch. 8, 3.3, p. 210): if `ν(B_r(x)) ≤ Λ μ(B_r(x))` for `0 < r < ρ₀`, and `φ` is continuous and non-increasing with `φ = 1` on `(-∞, 1]` and `φ = 0` on `[A², ∞)`, where `A, t > 0` and `t A < ρ₀`, then `∫ φ(|y - x|² / t²) dν(y) ≤ Λ ∫ φ(|y - x|² / t²) dμ(y)`. Every superlevel set of the integrand at a positive height is empty or a closed ball `B_r(x)` with `0 < r < ρ₀`; no finiteness of `ν`, `μ` and no sign condition on `Λ` is needed.
- Calls: — (no accepted declaration; library only)
- Called by: `S.mono833_radial_first_variation_bound`

##### `S.mono833_radial_first_variation_bound`

- Node: `root.monotonicity_density-a1.monotonicity_formula-a1.radial_first_variation_bound-a1`; accepted candidate `9e362000bbb5`
- Statement and proof: **Simon Ch. 8, 3.3 (printed p. 210), the first-variation estimate** (child `radial_first_variation_bound` of `monotonicity_formula`): for the radial field `X(y) = φ(|y - x|²/t²)(y - x)`, where `φ` is `C¹`, non-increasing, `φ = 1` on `(-∞, 1]` and `φ = 0` on `[A², ∞)`, with `tA < ρ₀`, hypothesis 3.1 (`‖δV‖(B_r(x)) ≤ Λ μ_V(B_r(x))` for `0 < r < ρ₀`) gives `|δV(X)| ≤ A Λ t ∫ φ(|y - x|²/t²) dμ_V(y)`. Write `δV(X) = -∫ ν·X d‖δV‖` with `|ν| = 1` `‖δV‖`-a.e. (2.6); then `|ν·X| ≤ tA φ(|y - x|²/t²)`, and the layer-cake comparison `mono833_radial_layer_cake_le` turns 3.1 into `∫ φ(|y - x|²/t²) d‖δV‖ ≤ Λ ∫ φ(|y - x|²/t²) dμ_V`.
- Calls: `S.mono833_radial_layer_cake_le`
- Called by: `S.monotonicity_formula_8_3_3`

##### `S.mono833_integrating_factor_comparison`

- Node: `root.monotonicity_density-a1.monotonicity_formula-a1.integrating_factor_comparison-a1`; accepted candidate `01ab77e72e49`
- Statement and proof: Integrating-factor comparison in mean value theorem form (Simon Ch. 8, 3.3, with the integrating factor `e^{Lt}` of Ch. 4, 3.15–3.17): if `0 ≤ L`, `0 ≤ a ≤ b`, `f` and `g` have derivatives `f'` and `g'` at every point of `[a, b]`, and `0 ≤ f' t + L f t` and `g' t ≤ f' t + L f t` on `[a, b]`, then `e^{La} f(a) + (g(b) - g(a)) ≤ e^{Lb} f(b)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.monotonicity_formula_8_3_3`

##### `S.mono833_exp_weighted_density_limit`

- Node: `root.monotonicity_density-a1.monotonicity_formula-a1.exp_weighted_density_limit-a1`; accepted candidate `032d34403443`
- Statement and proof: Density limit from monotonicity of the exponentially weighted ratio (Simon Ch. 8, 3.3, p. 210): if `ρ ↦ e^{Λρ} P(ρ)` is non-decreasing on `(0, ρ₀)` and `P(ρ₀/2) < ∞`, then `P(t)` tends as `t ↓ 0` to `θ = inf_{(0,ρ₀)} e^{Λρ} P(ρ)`, which is finite and bounded by `e^{Λσ} P(σ)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.monotonicity_formula_8_3_3`

#### `S.stationary_monotonicity_identity_8_3_4`

- Node: `root.monotonicity_density-a1.stationary_identity-a1`; accepted candidate `e163fc58e786`
- Statement and proof: **Simon Ch. 8, 3.4 (monotonicity identity, `Λ = 0`), p. 211.** If `V` is stationary in the open ball `B°_{ρ₀}(x) ⊆ U`, then `Θ^n(μ_V, x)` exists and `Θ^n(μ_V, x) + ω_n^{-1} ∫_{Gₙ(B_ρ(x))} r^{-n-2} |p_{S^⊥}(y - x)|² dV = ω_n^{-1} ρ^{-n} μ_V(B_ρ(x))` for `0 < ρ < ρ₀`. The annular identity for `0 < σ ≤ ρ` is SimonGMT's `StationaryOn.stationaryMonotonicity` on a ball `B_R(x)` with `ρ < R < ρ₀`; the two preceding lemmas pass it to the limit `σ ↓ 0`.
- Calls: `S.annular_identity_limit_at_zero`, `S.normalDefect_annulus_tendsto_closedBall`
- Called by: `S.monotonicity_and_density_theorems`

##### `S.normalDefect_annulus_tendsto_closedBall`

- Node: `root.monotonicity_density-a1.stationary_identity-a1.centre_defect_limit-a1`; accepted candidate `e58a09b37338`
- Statement and proof: The normal defect of the annuli `B_ρ(x) ∖ B_σ(x)` tends to that of `B_ρ(x)` as `σ ↓ 0` (Simon Ch. 8, 3.4, p. 211): the defect is continuous from below along the annuli, and its integrand vanishes at the centre `y = x`. No hypothesis on `V` or `ρ` is needed.
- Calls: — (no accepted declaration; library only)
- Called by: `S.stationary_monotonicity_identity_8_3_4`

##### `S.annular_identity_limit_at_zero`

- Node: `root.monotonicity_density-a1.stationary_identity-a1.density_limit-a1`; accepted candidate `7b7f84f3150f`
- Statement and proof: Passage to the limit `σ ↓ 0` in an additive annular identity in `[0, ∞]` (Simon Ch. 8, 3.4): if `P σ + D σ ρ = P ρ` for `0 < σ ≤ ρ < ρ₀` and `D σ ρ → T ρ` as `σ ↓ 0`, then `P` has a limit `θ` at `0⁺` and `θ + T ρ = P ρ` for `0 < ρ < ρ₀`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.stationary_monotonicity_identity_8_3_4`

#### `S.density_exists_ae_8_3_6`

- Node: `root.monotonicity_density-a1.density_exists_ae-a1`; accepted candidate `103e2378dace`
- Statement and proof: **Simon Ch. 8, 3.6 (Lemma).** If `V` has locally bounded first variation in `U`, then `Θ^n(μ_V, x)` exists and is finite for `μ_V`-a.e. `x`, and a Borel `Θ` equals it there: the monotonicity formula 3.3 applies at `μ_V`-a.e. `x`, and the Borel representative of the density takes the value of every existing density limit.
- Calls: `S.dea_ae_variationMeasure_ball_bound`, `S.frt_weq_density_borel_representative`, `S.monotonicity_formula_8_3_3`
- Called by: `S.monotonicity_and_density_theorems`

##### `S.frt_weq_density_borel_representative`

- Node: `root.first_rectifiability-a1.weight_eq_theta_hausdorff-a1.density_borel_representative-a1`; accepted candidate `015a566dda07`
- Statement and proof: A Borel representative of the `n`-density (Step 1 of the proof of Simon Ch. 8, 1.2): for an s-finite `μ` on `ℝ^N`, `g(x) = liminf_k μ(B_{1/(k+1)}(x)) / (ω_n (k+1)^{-n})` is Borel and `g(x) = Θ^n(μ, x)` at every `x` where `Θ^n(μ, x)` exists.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_weight_eq_multiplicity_hausdorff`, `S.density_exists_ae_8_3_6`

##### `S.dea_ae_variationMeasure_ball_bound`

- Node: `root.monotonicity_density-a1.density_exists_ae-a1.ae_ball_variation_bound-a1`; accepted candidate `598c9f332327`
- Statement and proof: Hypothesis 3.1 of the monotonicity formula holds `μ_V`-a.e. (the remark in the proof of Simon Ch. 8, 3.6, p. 211, by the differentiation theorem 2.7): for `μ_V`-a.e. `x` there are `R > 0` with `B_R(x) ⊆ U` and `Λ ≥ 0` with `‖δV‖(B_r(x)) ≤ Λ μ_V(B_r(x))` for all `0 < r < R`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.density_exists_ae_8_3_6`

### `S.density_semicontinuity_theorem`

- Node: `root.density_semicontinuity-a1`; accepted candidate `75c8fd149945`
- Statement and proof: **Simon Ch. 8, 3.7** (child `density_semicontinuity` of `main_theorem`; Step 4 of its proof). Remark 3.8(1) (child `variation_lsc`) gives that `V` has locally bounded first variation and `‖δV‖(W) ≤ liminf_i ‖δV_i‖(W)`. The printed steps (1)–(5) (child `lower_density_ae`, run with the monotonicity formula 3.3) give `liminf_{ρ↓0} μ_V(B_ρ(y)) / (ω_n ρ^n) ≥ 1` for `μ_V`-a.e. `y`, and Lemma 3.6 for `V` gives that `Θ^n(μ_V, y)` exists for `μ_V`-a.e. `y`. Where the density exists it equals that `liminf`, so it is `≥ 1`.
- Calls: `S.lower_density_ge_one_ae_of_radonConverges`, `S.monotonicity_and_density_theorems`, `S.variationMeasure_le_liminf_of_radonConverges`
- Called by: `S.varifold_tangent_theorems`, `S.compactness_theorem`, `S.integral_compactness_theorem`, `main_theorem`

#### `S.variationMeasure_le_liminf_of_radonConverges`

- Node: `root.density_semicontinuity-a1.variation_lsc-a1`; accepted candidate `698820351673`
- Statement and proof: **Simon Ch. 8, Remark 3.8(1), p. 211** (child `variation_lsc` of `density_semicontinuity`): if `V_i → V` as Radon measures on `Gₙ(U)`, every `V_i` has locally bounded first variation and `liminf_i ‖δV_i‖(W) < ∞` for each open `W ⊂⊂ U`, then `V` has locally bounded first variation and `‖δV‖(W) ≤ liminf_i ‖δV_i‖(W)` for each open `W ⊂⊂ U`. On such `W`, `‖δX‖(W)` is the supremum of 2.5 (`firstVariationNormOn`), which is lower semicontinuous because `δV_i(X) → δV(X)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.density_semicontinuity_theorem`

#### `S.weight_portmanteau_of_radonConverges`

- Node: `root.density_semicontinuity-a1.weight_portmanteau-a1`; accepted candidate `4557766ff859`
- Statement and proof: Portmanteau for varifold weights (Simon Ch. 8, proof of 3.7): if `Vᵢ → V` as Radon measures on `Gₙ(U)`, then `μ_V(O) ≤ liminf μ_{Vᵢ}(O)` for every open `O ⊆ U` and `limsup μ_{Vᵢ}(K) ≤ μ_V(K)` for every compact `K ⊆ U`.
- Calls: `S.limsup_measure_compact_le_of_tendsto_integral`, `S.measure_open_le_liminf_of_tendsto_integral`, `S.varifold_weight_integral_tendsto_of_radonConverges`
- Called by: `S.lower_density_ge_one_of_nearby_mass_bounds`, `S.lower_density_ge_one_ae_of_radonConverges`

##### `S.varifold_weight_integral_tendsto_of_radonConverges`

- Node: `root.density_semicontinuity-a1.weight_portmanteau-a1.weight_integral_tendsto-a1`; accepted candidate `7a4194d18972`
- Statement and proof: Radon convergence of varifolds gives vague convergence of their weights on `U` (Simon Ch. 8, proof of 3.7): if `V_i → V` as Radon measures on `Gₙ(U)` and `g ∈ C_c(ℝ^N)` has `spt g ⊆ U`, then `∫ g dμ_{V_i} → ∫ g dμ_V`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.weight_portmanteau_of_radonConverges`

##### `S.exists_urysohn_integral_sandwich`

- Node: `root.density_semicontinuity-a1.weight_portmanteau-a1.urysohn_sandwich-a1`; accepted candidate `4a8e59116e6d`
- Statement and proof: Urysohn sandwich (Simon Ch. 8, proof of 3.7): for compact `K` inside open `O` there is one continuous `g` with compact support in `O` such that `ν(K) ≤ ∫ g dν ≤ ν(O)` for every measure `ν` that is finite on compact subsets of `O`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.measure_open_le_liminf_of_tendsto_integral`, `S.limsup_measure_compact_le_of_tendsto_integral`

##### `S.measure_open_le_liminf_of_tendsto_integral`

- Node: `root.density_semicontinuity-a1.weight_portmanteau-a1.open_set_liminf-a1`; accepted candidate `5daabce7f5e1`
- Statement and proof: Portmanteau (P1) for vague convergence (Simon Ch. 8, proof of 3.7): if `∫ g dμᵢ → ∫ g dμ` for every continuous compactly supported `g` with support in `U`, and all measures are finite on compact subsets of `U`, then `μ(O) ≤ liminf μᵢ(O)` for every open `O ⊆ U`.
- Calls: `S.exists_urysohn_integral_sandwich`
- Called by: `S.weight_portmanteau_of_radonConverges`

##### `S.limsup_measure_compact_le_of_tendsto_integral`

- Node: `root.density_semicontinuity-a1.weight_portmanteau-a1.compact_set_limsup-a1`; accepted candidate `e2139e253e40`
- Statement and proof: Compact-set half of the portmanteau theorem (Simon Ch. 8, proof of 3.7): if `μ_i` and `μ` are finite on compact subsets of the open set `U` and `∫ g dμ_i → ∫ g dμ` for every continuous `g` with compact support in `U`, then `limsup_i μ_i(K) ≤ μ(K)` for every compact `K ⊆ U`.
- Calls: `S.exists_urysohn_integral_sandwich`
- Called by: `S.weight_portmanteau_of_radonConverges`

#### `S.besicovitch_ratio_cover_estimate`

- Node: `root.density_semicontinuity-a1.besicovitch_ratio_cover-a1`; accepted candidate `b70dd9d5e022`
- Statement and proof: **Simon Ch. 8, proof of 3.7, printed step (2)** (child `besicovitch_ratio_cover` of `density_semicontinuity`): if every `x ∈ A` is the centre of a closed ball `B_σ(x)`, `0 < σ < ρ₀`, with `μ(B_σ(x)) ≤ t ν(B_σ(x))`, then `μ(A) ≤ C t ν({dist(·, A) < ρ₀})`, where `C` is the Besicovitch number of `ℝ^N` (Ch. 1, 3.12). The covering lemma splits a subfamily of these balls covering `A` into `C` disjoint, hence countable, subfamilies; sum the ratio bound over each.
- Calls: — (no accepted declaration; library only)
- Called by: `S.lower_density_ge_one_ae_of_radonConverges`

#### `S.weight_closedBall_lower_bound_of_density_ge_one`

- Node: `root.density_semicontinuity-a1.monotonicity_mass_lower_bound-a1`; accepted candidate `94077eb6fde0`
- Statement and proof: **Simon Ch. 8, 3.7, printed step (4)** (child `monotonicity_mass_lower_bound` of the density semicontinuity theorem): at a point where `Θ^n(μ_V, x) ≥ 1` and the ball bound 3.1 holds on `(0, ρ₀)`, the monotonicity formula 3.3 gives `e^{-Λρ} ω_n ρ^n ≤ μ_V(B_ρ(x))` for `0 < ρ < ρ₀`. The density supplied by 3.3 equals `θ` by uniqueness of limits along `𝓝[>] 0`, and `D = ω_n ρ^n ∈ (0, ∞)` cancels in `1 ≤ θ ≤ e^{Λρ} μ_V(B_ρ(x)) / D`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.lower_density_ge_one_ae_of_radonConverges`

#### `S.lower_density_ge_one_of_nearby_mass_bounds`

- Node: `root.density_semicontinuity-a1.limit_mass_lower_bound-a1`; accepted candidate `f1a3dd4009ac`
- Statement and proof: **Simon Ch. 8, proof of 3.7, second half of printed step (4)** (child `limit_mass_lower_bound` of `density_semicontinuity`): let `V_i → V` as Radon measures on `Gₙ(U)`, `q_i → ∞`, `y_i → x`, `B°_{ρ₀}(x) ⊆ U` and `e^{-Λρ} ω_n ρ^n ≤ μ_{V_{q_i}}(B_ρ(y_i))` for all `i` and `0 < ρ < ρ₀`. Then `e^{-Λρ} ω_n ρ^n ≤ μ_V(B_ρ(x))` for `0 < ρ < ρ₀`, hence `liminf_{ρ↓0} μ_V(B_ρ(x))/(ω_n ρ^n) ≥ 1`. For large `i`, `B_{ρ-|y_i-x|}(y_i) ⊆ B_ρ(x)`, so `e^{-Λρ} ω_n ρ^n ≤ limsup_i μ_{V_{q_i}}(B_ρ(x)) ≤ μ_V(B_ρ(x))` by (P2) of `weight_portmanteau_of_radonConverges`; then divide by `ω_n ρ^n`.
- Calls: `S.weight_portmanteau_of_radonConverges`
- Called by: `S.lower_density_ge_one_ae_of_radonConverges`

#### `S.lower_density_ge_one_ae_of_radonConverges`

- Node: `root.density_semicontinuity-a1.lower_density_ae-a1`; accepted candidate `d2f24f236c31`
- Statement and proof: **Simon Ch. 8, 3.7, density part** (child `lower_density_ae` of `density_semicontinuity`; printed proof, pp. 212–213, (1)–(5), with the monotonicity formula 3.3): if `V_i → V` as Radon measures on `Gₙ(U)`, `liminf_i ‖δV_i‖(W) < ∞` and `Θ^n(μ_{V_i}, ·) ≥ 1` off `B_i` with `μ_{V_i}(B_i ∩ W) → 0` for every `W ⊂⊂ U`, then `liminf_{ρ↓0} μ_V(B_ρ(y)) / (ω_n ρ^n) ≥ 1` for `μ_V`-a.e. `y`. Fix `W ⊂⊂ U` and `W̃ = {dist(·, W) < ρ₀} ⊂⊂ U`. A point of `W ∖ B_q` is good for `(q, k)` if `‖δV_q‖ ≤ k μ_q` on its balls of radius `< ρ₀`; Besicovitch bounds the bad set by `C k⁻¹ ‖δV_q‖(W̃) + μ_q(B_q ∩ W)` (printed (2)), so the points interior to `⋂_{ℓ ≥ i}` of the bad sets for every `k ≥ 1` form a `μ_V`-null set (printed (3), (5)). Each other `x ∈ W` is a limit of good points `y_i` of `V_{q_i}`, where 3.3 with `Λ = k` gives `μ_{q_i}(B_ρ(y_i)) ≥ e^{-kρ} ω_n ρ^n`; these bounds pass to `μ_V` at `x` (printed (4)). Countably many `W ⊂⊂ U` exhaust `U`.
- Calls: `S.ae_of_forall_relCompactOpen_null_exceptional`, `S.besicovitch_ratio_cover_estimate`, `S.exists_nearby_points_off_bad_sets`, `S.exists_thickening_isRelCompactOpenIn`, `S.lower_density_ge_one_of_nearby_mass_bounds`, `S.measure_bad_interior_exceptional_eq_zero`, `S.weight_closedBall_lower_bound_of_density_ge_one`, `S.weight_portmanteau_of_radonConverges`
- Called by: `S.density_semicontinuity_theorem`

##### `S.exists_thickening_isRelCompactOpenIn`

- Node: `root.density_semicontinuity-a1.lower_density_ae-a1.thickening_rel_compact-a1`; accepted candidate `e5f3240dec26`
- Statement and proof: **Simon Ch. 8, proof of 3.7, p. 212, choice of `ρ₀` and `W̃`** (child `thickening_rel_compact` of `lower_density_ae`): if `W ⊂⊂ U` then `W̃ = {x : dist(x, W) < ρ₀} ⊂⊂ U` for some `ρ₀ > 0`. The compact set `closure W` has a closed thickening `cthickening ρ₀ (closure W) ⊆ U`; it is compact (`ℝ^N` is proper) and contains `closure W̃ ⊆ cthickening ρ₀ W = cthickening ρ₀ (closure W)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.lower_density_ge_one_ae_of_radonConverges`

##### `S.ae_of_forall_relCompactOpen_null_exceptional`

- Node: `root.density_semicontinuity-a1.lower_density_ae-a1.relcompact_exhaustion_ae-a1`; accepted candidate `68b694e24948`
- Statement and proof: **Simon Ch. 8, proof of 3.7, p. 213, final step** (child `relcompact_exhaustion_ae` of `lower_density_ae`): the book proves the density bound on one `W ⊂⊂ U` off a `μ`-null set ((4), (5)); this passes to `μ`-a.e. point. If `μ(ℝ^N ∖ U) = 0` and `P` holds on each `W ⊂⊂ U` off a `μ`-null set, then `P` holds `μ`-a.e.: each `x ∈ U` has a ball `W_x = B°_{r_x}(x) ⊂⊂ U`, countably many `W_x` cover `U` (`ℝ^N` is second countable), and `{¬P} ⊆ Uᶜ ∪ ⋃_{x ∈ T} E_x` is `μ`-null. No measurability of `P` or of the exceptional sets is used.
- Calls: — (no accepted declaration; library only)
- Called by: `S.lower_density_ge_one_ae_of_radonConverges`

##### `S.measure_bad_interior_exceptional_eq_zero`

- Node: `root.density_semicontinuity-a1.lower_density_ae-a1.bad_interior_null-a1`; accepted candidate `dc13f906cc9a`
- Statement and proof: **Simon Ch. 8, proof of 3.7, pp. 212–213, displays (3) and (5)** (child `bad_interior_null` of `lower_density_ae`): suppose `μ(O) ≤ liminf_q μ_q(O)` for every open `O ⊆ W`, and the sets `Bad q k ⊆ W` satisfy `μ_q(Bad q k) ≤ C k⁻¹ a_q + b_q` for `k ≥ 1`, with `liminf_q a_q < ∞` and `b_q → 0`. Then `⋂_{k ≥ 1} ⋃_i interior (⋂_{ℓ ≥ i} Bad ℓ k)` is `μ`-null. The open set `O_{i,k} = interior (⋂_{ℓ ≥ i} Bad ℓ k)` lies in `Bad q k` for every `q ≥ i`, so `μ(O_{i,k}) ≤ C k⁻¹ liminf_q a_q` (printed (3)). As `O_{i,k}` increases in `i`, the exceptional set has measure `≤ C k⁻¹ liminf_q a_q` for every `k ≥ 1` (printed (5)), and this bound tends to `0`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.lower_density_ge_one_ae_of_radonConverges`

##### `S.exists_nearby_points_off_bad_sets`

- Node: `root.density_semicontinuity-a1.lower_density_ae-a1.nearby_good_points-a1`; accepted candidate `a79903e2e6d0`
- Statement and proof: Choice of `y_i`, `q_i` in the proof of 3.7 (Simon Ch. 8, p. 212, before (4)): if `x ∈ W` with `W` open and `x ∉ interior (⋂_{ℓ ≥ i} Bad ℓ)` for every `i`, then there are `y_i → x` in `W` and `q_i → ∞` with `y_i ∉ Bad (q_i)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.lower_density_ge_one_ae_of_radonConverges`

### `S.constancy_theorem`

- Node: `root.constancy-a1`; accepted candidate `9a9e3f33a30d`
- Statement and proof: **Simon Ch. 8, 4.1 (Constancy Theorem), corrected** (child `constancy` of `main_theorem`). If `M = ∅`, then `V` is carried by `U ∩ spt μ_V = ∅`, so `V = 0` and `θ₀ = 0` works. Otherwise the measure form `V = (c H^n ⌞ (M ∩ U)).map (x ↦ (x, T x))` with `c < ∞` (child `stationary_constancy_tangentGraph_measure`) gives the formula with `θ₀ = c`: if `c = 0` both sides vanish, and if `c ≠ 0` then `T x` is the only point of `G(N,n)` whose plane is `classicalTangentSpace M x`, since a point of `G(N,n)` is determined by its plane.
- Calls: `S.stationary_constancy_tangentGraph_measure`
- Called by: `S.allard_rectifiability_and_tangent_cones`, `main_theorem`

#### `S.simon_chart_classicalTangentSpace_eq_range`

- Node: `root.constancy-a1.classical_tangent-a1`; accepted candidate `e701f44b497c`
- Statement and proof: **Simon Ch. 2, 4.3** (child `classical_tangent` of the constancy theorem): at a point `φ a` of a `C²` local representation, the classical tangent space (velocities of `C¹` curves in `M`) is the range of `L = Dφ(a)`. `⊇`: the curve `t ↦ φ (a + (ε sin (t/ε)) w)` stays in the chart and has velocity `L w`. `⊆`: relative properness makes the chart parameter `β t` of `γ t` tend to `a`, `L` is antilipschitz so `β t - a = O(t)`, and then the component of `γ` normal to `range L` has derivative `0` at `0`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.stationary_constancy_tangentGraph_measure`

#### `S.stationary_constancy_tangentGraph_measure`

- Node: `root.constancy-a1.tangent_graph_measure-a1`; accepted candidate `8a562da58737`
- Statement (frozen type, no doc comment): `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (M : Set (Euclidean N)), V.Stationary → Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M → U ∩ V.weight.support ⊆ M → IsPreconnected (M ∩ U) → M.Nonempty → ∃ (c : ℝ≥0∞) (T : Euclidean N → Grassmannian N n), c ≠ ∞ ∧ Measurable T ∧ V.measure = (c • (μHE[n] : Measure (Euclidean N)).restrict (M ∩ U)).map (fun x ↦ (x, T x)) ∧ (c ≠ 0 → ∀ x ∈ M ∩ U, ((T x).plane : Set (Euclidean N)) = classicalTangentSpace M x)`
- Calls: `S.simon_chart_classicalTangentSpace_eq_range`
- Called by: `S.constancy_theorem`

### `S.varifold_radon_compactness`

- Node: `root.radon_compactness-a1`; accepted candidate `6277cbb0daba`
- Statement and proof: **Simon Ch. 1, 4.16 (Compactness Theorem for Radon measures), corrected**, on `Gₙ(U)`; used in Ch. 8, 5.1 and 5.8. If `μ_j(K × G(N,n))` is eventually bounded for each compact `K ⊆ U`, then a subsequence `μ_{φ(j)}` converges to an `n`-varifold `V` on `U` against every test function supported in `U × G(N,n)`. The printed proof extracts with Alaoglu, which only yields a subnet; on the second countable space `Gₙ(U)` the extraction is sequential, and the limit functional is represented by the Riesz theorem (Ch. 1, 4.12).
- Calls: `S.radon_exists_measure_of_tendsto_integral`, `S.radon_exists_subseq_tendsto_integral`
- Called by: `S.varifold_tangent_theorems`, `S.compactness_theorem`

#### `S.radon_compactlySupported_countable_approx`

- Node: `root.radon_compactness-a1.cc_countable_approx-a1`; accepted candidate `2721e2033725`
- Statement and proof: Test functions for the sequential form of the Alaoglu step in Simon Ch. 1, 4.16 (erratum: the Alaoglu theorem only yields a subnet). If `X` is locally compact, Hausdorff and second countable, there is a sequence `g` in `C_c(X, ℝ)` such that every `f ∈ C_c(X, ℝ)` has a compact `K ⊇ tsupport f` and, for each `η > 0`, some `g k` with `tsupport (g k) ⊆ K` and `|f - g k| ≤ η` everywhere.
- Calls: — (no accepted declaration; library only)
- Called by: `S.radon_exists_subseq_tendsto_integral`

#### `S.radon_exists_subseq_tendsto_integral`

- Node: `root.radon_compactness-a1.subseq_extraction-a1`; accepted candidate `9eade5d8f5de`
- Statement and proof: Subsequence extraction in Simon Ch. 1, 4.16 (erratum: the Alaoglu theorem only yields a subnet, so `X` is taken second countable). If `X` is locally compact, Hausdorff and second countable and the masses `μ j K` of each compact `K` are eventually bounded, then for one strictly increasing `φ` every `∫ f dμ (φ j)` with `f ∈ C_c(X, ℝ)` converges. A Tychonoff (diagonal) extraction in `ℕ → ℝ` makes `∫ g k dμ (φ j)` converge for the countable family `g` of `radon_compactlySupported_countable_approx`; uniform approximation of `f` by `g k` supported in a fixed compact `K ⊇ tsupport f` and the mass bound on `K` then make `∫ f dμ (φ j)` Cauchy.
- Calls: `S.radon_compactlySupported_countable_approx`
- Called by: `S.varifold_radon_compactness`

#### `S.radon_exists_measure_of_tendsto_integral`

- Node: `root.radon_compactness-a1.riesz_limit_measure-a1`; accepted candidate `c0657ab4d3eb`
- Statement and proof: Final step of Simon Ch. 1, 4.16 (Riesz representation, Theorem 4.12): if the masses `μ_j(K)` of each compact `K` are eventually bounded and `∫ f dμ_j` converges for every `f ∈ C_c(X, ℝ)`, then the limits are the integrals `∫ f dν` against a single locally finite measure `ν` on `X`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_radon_compactness`

### `S.varifold_tangent_theorems`

- Node: `root.varifold_tangents-a1`; accepted candidate `7e5f6a9c460e`
- Statement and proof: **Simon Ch. 8, 5.1–5.4 and the use of 3.7 in 5.5/5.7** (child `varifold_tangents` of `main_theorem`), at a point `x` where `ρ^{1-n}‖δV‖(B_ρ(x)) → 0` (5.1). First, if `Θ^n(μ_V, x) = θ₀ > 0`, every `λ_j ↓ 0` has a subsequence along which `V_{x,λ_j}` converges, and every `C ∈ VarTan(V, x)` is stationary with `μ_C(B_ρ(0)) = θ₀ ω_n ρ^n` and `μ_C(s A) = s^n μ_C(A)` (5.2 and 5.3, corrected). Second, if `ρ^{-n} μ_V({y ∈ B_ρ(x) : Θ^n(μ_V, y) ≥ τ fails}) → 0`, then `Θ^n(μ_C, ·) ≥ τ` holds `μ_C`-a.e. for every `C ∈ VarTan(V, x)`. Between 5.2 and 5.3, the constant ratio `μ_C(B_R(0)) / R^n` forces `y ∈ S` for `C`-a.e. `(y, S)`: this is SimonGMT's radial rigidity, the equality case of 3.4.
- Calls: `S.density_semicontinuity_theorem`, `S.varifold_radon_compactness`, `S.varifold_tangents_density_lower_bound`, `S.varifold_tangents_limit_ball_mass`, `S.varifold_tangents_limit_stationary`, `S.varifold_tangents_radial_stationary_homogeneous`, `S.varifold_tangents_rescaled_ball_mass_tendsto`
- Called by: `S.allard_rectifiability_and_tangent_cones`, `main_theorem`

#### `S.varifold_tangents_rescaled_ball_mass_tendsto`

- Node: `root.varifold_tangents-a1.rescaled_ball_mass-a1`; accepted candidate `783517dd1122`
- Statement and proof: **Simon Ch. 8, 5.1–5.2, the ball-mass computation** (child `rescaled_ball_mass` of `varifold_tangents`): if `Θ^n(μ_V, x) = θ`, then `V_{x,t}(B_R(0) × G(N,n)) → θ ω_n R^n` as `t ↓ 0`. For `t > 0` the preimage of `B_R(0) × G(N,n)` under `(z, S) ↦ (t⁻¹(z - x), S)` is `B_{tR}(x) × G(N,n)`, so `V_{x,t}(B_R(0) × G(N,n)) = t^{-n} μ_V(B_{tR}(x))`, which equals `densityRatio n μ_V x (tR) · ω_n R^n` because `0 < ω_n < ∞`; then compose `HasDensity` with `t ↦ tR` (as in SimonGMT's `Varifold.tendsto_blowUpWeight_closedBall_of_density`).
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_tangents_limit_ball_mass`, `S.varifold_tangent_theorems`

#### `S.varifold_tangents_rescaled_divergence_bound`

- Node: `root.varifold_tangents-a1.rescaled_divergence_bound-a1`; accepted candidate `4a352df77a73`
- Statement and proof: **Simon Ch. 8, 5.1–5.2, the first-variation bound for `V_{x,t}`** (child `rescaled_divergence_bound` of `varifold_tangents`): if `X` is `C¹`, `spt X ⊆ B°_R(0)` and `|X| ≤ M`, then `|∫ div_S X dV_{x,t}| ≤ M R^{n-1} (tR)^{1-n} ‖δV‖(B_{tR}(x))`. With `ψ(z) = t⁻¹(z - x)` and `Y(z) = t X(ψ z)`, `∫ div_S X dV_{x,t} = t^{-n} δV(Y)` (`varifold_tangents_rdb_rescaled_integral_eq`). `Y` is `C¹`, `|Y| ≤ tM` and `spt Y ⊆ ψ⁻¹(B°_R(0)) = B°_{tR}(x)`, an open set with compact closure inside `B_{tR}(x) ⊆ U`, so 2.5 gives `|δV(Y)| ≤ tM ‖δV‖(B°_{tR}(x))` (`varifold_tangents_rdb_firstVariation_le_variationMeasure`). The rest is `ℝ≥0∞` arithmetic: `t^{-n} · tM · A = M (R^n / R) (tR · A / (tR)^n)`.
- Calls: `S.varifold_tangents_rdb_firstVariation_le_variationMeasure`, `S.varifold_tangents_rdb_rescaled_integral_eq`
- Called by: `S.varifold_tangents_limit_stationary`, `S.varifold_tangents_density_lower_bound`

##### `S.varifold_tangents_rdb_rescaled_integral_eq`

- Node: `root.varifold_tangents-a1.rescaled_divergence_bound-a1.rescaled_integral_identity-a1`; accepted candidate `3b82c79fbbb6`
- Statement and proof: Simon Ch. 8, 5.1–5.2 (p. 215), the change of variables behind the first variation of the rescaled varifold `V_{x,t} = η_{x,t #} V`: for a `C¹` field `X` and `t > 0`, `∫ div_S X dV_{x,t} = t⁻ⁿ δV(Y)` with `Y(z) = t X(t⁻¹(z - x))`, since `DY(z) = DX(t⁻¹(z - x))`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_tangents_rescaled_divergence_bound`

##### `S.varifold_tangents_rdb_firstVariation_le_variationMeasure`

- Node: `root.varifold_tangents-a1.rescaled_divergence_bound-a1.first_variation_sup_bound-a1`; accepted candidate `6d9eb2633ed5`
- Statement and proof: **Simon Ch. 8, 2.5 (p. 209), the supremum bound** (child `first_variation_sup_bound` of the rescaled divergence bound for varifold tangents). If `V` has locally bounded first variation, `W ⊂⊂ U` is open and `Y` is a `C¹` field with `spt Y ⊆ W` and `|Y| ≤ K`, then `|δV(Y)| ≤ K ‖δV‖(W)`: `Y` is a test field, `‖δV‖(W)` is the supremum in 2.5 (`firstVariationRieszMeasure_eq_norm`), and `K⁻¹ Y` is admissible in that supremum.
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_tangents_rescaled_divergence_bound`

#### `S.varifold_tangents_limit_stationary`

- Node: `root.varifold_tangents-a1.limit_stationary-a1`; accepted candidate `34de3745af71`
- Statement and proof: **Simon Ch. 8, 5.4 (p. 215), varifold tangents are stationary** (child `limit_stationary` of `varifold_tangents`): if `V` has locally bounded first variation, `x ∈ U`, `γ(ρ) = ρ^{1-n} ‖δV‖(B_ρ(x)) → 0` as `ρ ↓ 0` (5.1) and `C ∈ VarTan(V, x)`, then `C` is stationary. For `X ∈ K(ℝ^N;ℝ^N)`, `div_S X` is continuous with compact support, so vague convergence gives `I_j = ∫ div_S X dV_{x,t_j} → δC(X)`. With `spt X ⊆ B°_R(0)`, `|X| ≤ M` and `B_r(x) ⊆ U`, for large `j` the rescaled divergence bound (`varifold_tangents_rescaled_divergence_bound`) gives `|I_j| ≤ M (R^n / R) γ(t_j R) → 0`, hence `δC(X) = 0`.
- Calls: `S.varifold_tangents_rescaled_divergence_bound`
- Called by: `S.varifold_tangent_theorems`

#### `S.varifold_tangents_limit_ball_mass`

- Node: `root.varifold_tangents-a1.limit_ball_mass-a1`; accepted candidate `dbdcf40083d3`
- Statement and proof: **Simon Ch. 8, 5.2 (centre corrected to `0`), ball masses of a varifold tangent** (child `limit_ball_mass` of `varifold_tangents`): if `Θ^n(μ_V, x) = θ₀` and `C ∈ VarTan(V, x)`, then `μ_C(B_ρ(0)) = θ₀ ω_n ρ^n` for every `ρ > 0`. Write `L(r) = θ₀ ω_n r^n` and `K_r = B_r(0) × G(N,n)`. For the radii `t_j > 0`, `t_j → 0` of `C`, `varifold_tangents_rescaled_ball_mass_tendsto` gives `V_{x,t_j}(K_r) → L(r) < ∞` for `r > 0`. As `C(K_ρ') = μ_C(B_ρ'(0)) < ∞`, `varifold_tangents_lbm_vague_cylinder_bounds` (with `a = ρ`, `b = ρ'`) gives `μ_C(B_ρ(0)) ≤ L(ρ')` and `L(ρ) ≤ μ_C(B_ρ'(0))` for every `ρ' > ρ`. Let `ρ' ↓ ρ`: `L` is continuous, and `μ_C(B_ρ'(0)) → μ_C(B_ρ(0))` by continuity from above, since `⋂_{ρ' > ρ} B_ρ'(0) = B_ρ(0)`.
- Calls: `S.varifold_tangents_lbm_vague_cylinder_bounds`, `S.varifold_tangents_rescaled_ball_mass_tendsto`
- Called by: `S.varifold_tangent_theorems`

##### `S.varifold_tangents_lbm_exists_cylinder_cutoff`

- Node: `root.varifold_tangents-a1.limit_ball_mass-a1.cylinder_cutoff-a1`; accepted candidate `5e8b42eeac5e`
- Statement and proof: **Simon Ch. 8, 5.2, the cylinder cut-off** (child `cylinder_cutoff` of `limit_ball_mass`): for `a < b` one `F ∈ C_c(ℝ^N × G(N,n), ℝ)`, chosen before the measure, satisfies `ν(B_a(0) × G(N,n)) ≤ ∫ F dν ≤ ν(B_b(0) × G(N,n))` for every `ν` with `ν(B_b(0) × G(N,n)) < ∞`. Take the ramp `F(y, S) = min 1 (max 0 ((b - |y|) / (b - a)))`: it is continuous, `0 ≤ F ≤ 1`, `F = 1` on `B_a(0) × G(N,n)` and `F = 0` off the compact `B_b(0) × G(N,n)`. Then `|F| ≤ 1_{B_b(0) × G(N,n)}` gives integrability, so `ofReal (∫ F dν) = ∫⁻ ofReal ∘ F dν`, and `1_{B_a(0) × G(N,n)} ≤ ofReal ∘ F ≤ 1_{B_b(0) × G(N,n)}` gives both bounds.
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_tangents_lbm_vague_cylinder_bounds`

##### `S.varifold_tangents_lbm_vague_cylinder_bounds`

- Node: `root.varifold_tangents-a1.limit_ball_mass-a1.vague_cylinder_bounds-a1`; accepted candidate `0b7b368e1df4`
- Statement and proof: **Simon Ch. 8, 5.2, vague-limit cylinder bounds** (child `vague_cylinder_bounds` of `limit_ball_mass`): if `μs j → μ` vaguely, `a < b`, `μ(B_b(0) × G(N,n)) < ∞`, `μs j (B_a(0) × G(N,n)) → La` and `μs j (B_b(0) × G(N,n)) → Lb < ∞`, then `μ(B_a(0) × G(N,n)) ≤ Lb` and `La ≤ μ(B_b(0) × G(N,n))`. Take the cut-off `F` of `varifold_tangents_lbm_exists_cylinder_cutoff` for `a < b`: it puts `ofReal (∫ F dμ)` between `μ(B_a(0) × G(N,n))` and `μ(B_b(0) × G(N,n))`, and, as `Lb < ∞`, eventually puts `ofReal (∫ F dμs j)` between `μs j (B_a(0) × G(N,n))` and `μs j (B_b(0) × G(N,n))`. Vague convergence gives `ofReal (∫ F dμs j) → ofReal (∫ F dμ)`, so passing to the limit gives `ofReal (∫ F dμ) ≤ Lb` and `La ≤ ofReal (∫ F dμ)`.
- Calls: `S.varifold_tangents_lbm_exists_cylinder_cutoff`
- Called by: `S.varifold_tangents_limit_ball_mass`

#### `S.varifold_tangents_radial_stationary_homogeneous`

- Node: `root.varifold_tangents-a1.radial_homogeneity-a1`; accepted candidate `8d3eca4e040c`
- Statement and proof: **Simon Ch. 8, 5.3 (p. 215), corrected**: radial homogeneity of a stationary varifold `C` on `ℝ^N` with `y ∈ S` for `C`-a.e. `(y, S)`, namely `μ_C(s A) = sⁿ μ_C(A)` for every `s > 0` and every set `A ⊆ ℝ^N` (the printed `λ^{-n} μ_C(η_{0,λ}(A)) = μ_C(A)` has the wrong power). Testing `δC = 0` against `g(y) y` gives Euler's identity `∫ (n g + Dg(y)(y)) dμ_C = 0`; this yields the dilation law `∫ g(s⁻¹ y) dμ_C(y) = sⁿ ∫ g dμ_C` for `C¹_c` functions, mollification extends it to `C_c`, and Riesz uniqueness turns it into the stated identity on all sets.
- Calls: `S.varifold_tangents_rh_measure_homogeneous`, `S.varifold_tangents_rh_radial_euler_identity`, `S.varifold_tangents_rh_scaling_continuous`, `S.varifold_tangents_rh_scaling_of_euler_identity`
- Called by: `S.varifold_tangent_theorems`

##### `S.varifold_tangents_rh_radial_euler_identity`

- Node: `root.varifold_tangents-a1.radial_homogeneity-a1.radial_euler_identity-a1`; accepted candidate `166d16177149`
- Statement and proof: Radial Euler identity for a stationary varifold `C` on `ℝ^N` with `y ∈ S` for `C`-a.e. `(y, S)` (Simon Ch. 8, 3.5 at `x = 0` with vanishing normal defect): testing `δC = 0` against the radial field `X(y) = g(y) y` gives `∫ (n g(y) + Dg(y)(y)) dμ_C(y) = 0` for every compactly supported `C¹` function `g`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_tangents_radial_stationary_homogeneous`

##### `S.varifold_tangents_rh_scaling_of_euler_identity`

- Node: `root.varifold_tangents-a1.radial_homogeneity-a1.euler_dilation_c1-a1`; accepted candidate `b7e2b99daeeb`
- Statement and proof: **Simon Ch. 8, 5.3 (p. 215), from Euler's identity to dilation homogeneity** (child `euler_dilation_c1` of the radial homogeneity step for varifold tangents). If `μ` is finite on compact sets and `∫ (n h + Dh(y) y) dμ = 0` for every compactly supported `C¹` function `h`, then `∫ g(s⁻¹ y) dμ(y) = sⁿ ∫ g dμ` for every such `g` and every `s > 0`: `F(t) = ∫ g(t⁻¹ y) dμ(y)` has derivative `-t⁻¹ ∫ Dg(t⁻¹ y)(t⁻¹ y) dμ(y)` (differentiation under the integral sign), Euler's identity on the dilates turns this into `n F(t) / t`, and that ODE forces `F(s) = sⁿ F(1)`.
- Calls: `S.varifold_tangents_rh_edc_euler_dilate`, `S.varifold_tangents_rh_edc_hasDerivAt_dilate_integral`, `S.varifold_tangents_rh_edc_pow_of_hasDerivAt`
- Called by: `S.varifold_tangents_radial_stationary_homogeneous`

###### `S.varifold_tangents_rh_edc_pow_of_hasDerivAt`

- Node: `root.varifold_tangents-a1.radial_homogeneity-a1.euler_dilation_c1-a1.euler_ode_power-a1`; accepted candidate `10b355cf6ff4`
- Statement and proof: Integration of Euler's ODE (used for the radial homogeneity of tangent cones, Simon Ch. 8, 5.3): if `F'(t) = n F(t) / t` for every `t > 0`, then `F(s) = sⁿ F(1)` for every `s > 0`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_tangents_rh_scaling_of_euler_identity`

###### `S.varifold_tangents_rh_edc_euler_dilate`

- Node: `root.varifold_tangents-a1.radial_homogeneity-a1.euler_dilation_c1-a1.euler_identity_dilates-a1`; accepted candidate `7b4bc68f74ab`
- Statement and proof: Euler's identity on the dilates (used for the radial homogeneity of tangent cones, Simon Ch. 8, 5.3): if `∫ (n h + Dh(y) y) dμ = 0` for every compactly supported `C¹` function `h`, then `n ∫ g(t⁻¹ y) dμ + ∫ Dg(t⁻¹ y)(t⁻¹ y) dμ = 0` for every such `g` and every `t > 0`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_tangents_rh_scaling_of_euler_identity`

###### `S.varifold_tangents_rh_edc_hasDerivAt_dilate_integral`

- Node: `root.varifold_tangents-a1.radial_homogeneity-a1.euler_dilation_c1-a1.dilation_integral_deriv-a1`; accepted candidate `de98dbe3d528`
- Statement and proof: Differentiation under the integral sign for dilates (used for the homogeneity 5.3 in Simon Ch. 8): if `μ` is finite on compact sets and `g` is `C¹` with compact support, then for `t > 0` the function `r ↦ ∫ g(r⁻¹y) dμ(y)` has derivative `-(t⁻¹ ∫ Dg(t⁻¹y)(t⁻¹y) dμ(y))` at `t`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_tangents_rh_scaling_of_euler_identity`

##### `S.varifold_tangents_rh_scaling_continuous`

- Node: `root.varifold_tangents-a1.radial_homogeneity-a1.dilation_mollify_cc-a1`; accepted candidate `252ba10bd8a5`
- Statement and proof: Extension of the dilation law from `C¹_c` to `C_c` by mollification (step 3 of the proof of the corrected Simon Ch. 8, 5.3): if `μ` is finite on compact sets, `s > 0` and `∫ h(s⁻¹ y) dμ(y) = sⁿ ∫ h dμ` for every compactly supported `C¹` function `h`, then the same identity holds for every continuous compactly supported `g`. The `C¹` approximants `φ_k → g` (uniformly, all vanishing off one compact `K`) satisfy the identity, and both sides pass to the limit because the integrands converge uniformly and agree with their limits off the fixed compact sets `s • K` and `K`.
- Calls: `S.varifold_tangents_rh_mc_exists_c1_approx`, `S.varifold_tangents_rh_mc_tendsto_integral_of_uniform`
- Called by: `S.varifold_tangents_radial_stationary_homogeneous`

###### `S.varifold_tangents_rh_mc_tendsto_integral_of_uniform`

- Node: `root.varifold_tangents-a1.radial_homogeneity-a1.dilation_mollify_cc-a1.uniform_limit_integral-a1`; accepted candidate `9901c58000f1`
- Statement and proof: Uniform convergence with a common compact support gives convergence of integrals: if `μ` is finite on compacts, `K` is compact, `F k = G` off `K` for every `k` and `F k → G` uniformly, then `∫ F k dμ → ∫ G dμ` (the limit step of the mollification argument for Simon Ch. 8, 5.3).
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_tangents_rh_scaling_continuous`

###### `S.varifold_tangents_rh_mc_exists_c1_approx`

- Node: `root.varifold_tangents-a1.radial_homogeneity-a1.dilation_mollify_cc-a1.mollifier_c1_approx-a1`; accepted candidate `85df1e5ac2e7`
- Statement and proof: Uniform `C¹` approximation by mollification (step 3 of extending the dilation law for varifold tangents, Simon Ch. 8, 5.3, from `C¹_c` to `C_c`): a continuous compactly supported `g` on `ℝ^N` is the uniform limit of the `C¹` functions `φ_k = ψ_k ⋆ g`, where `ψ_k` is a normalized smooth bump supported in `B(0, 1/(k+1))`, and `g` and every `φ_k` vanish off the compact set `K = closedBall 0 1 + tsupport g`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_tangents_rh_scaling_continuous`

##### `S.varifold_tangents_rh_measure_homogeneous`

- Node: `root.varifold_tangents-a1.radial_homogeneity-a1.dilation_riesz_sets-a1`; accepted candidate `635defac48d6`
- Statement and proof: **Simon Ch. 8, 5.3 (p. 215), from integrals to sets** (child `dilation_riesz_sets` of the radial homogeneity step for varifold tangents). If `μ` is finite on compact sets, `s > 0` and `∫ g(s⁻¹ y) dμ(y) = sⁿ ∫ g dμ` for every `g ∈ C_c(ℝ^N)`, then `μ(s A) = sⁿ μ(A)` for every set `A`: the image of `μ` under `T y = s⁻¹ y` and `sⁿ μ` are regular and agree on `C_c`, so they are equal by uniqueness in the Riesz representation theorem, and an image under a measurable equivalence is evaluated exactly on every set, with `T⁻¹(A) = s A`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_tangents_radial_stationary_homogeneous`

#### `S.varifold_tangents_restricted_radon_converges`

- Node: `root.varifold_tangents-a1.restrict_radon_converges-a1`; accepted candidate `e5a53250740b`
- Statement and proof: Restricting vague convergence to an open set (step B2 of the proof of Simon Ch. 8, 5.4): if `μ_i → μ` as Radon measures on `Gₙ(ℝ^{n+ℓ})` and `W_i = c μ_i ⌞ Gₙ(Ω)`, `W = c μ ⌞ Gₙ(Ω)` are varifolds on `Ω`, then `W_i → W` as Radon measures on `Gₙ(Ω)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_tangents_density_lower_bound`

#### `S.varifold_tangents_density_lower_bound`

- Node: `root.varifold_tangents-a1.density_lower_bound-a1`; accepted candidate `b1d1a62c4422`
- Statement and proof: **Simon Ch. 8, the use of 3.7 in the proofs of 5.5 and 5.7** (child `density_lower_bound` of `varifold_tangents`): if 5.1 holds at `x` and `ρ^{-n} μ_V({y ∈ B_ρ(x) : Θ^n(μ_V, y) ≥ τ fails}) → 0`, then `Θ^n(μ_C, ·) ≥ τ` holds `μ_C`-a.e. for every `C ∈ VarTan(V, x)`. On each ball `Ω = B°_R(0)`, the varifolds `W_i = τ⁻¹ V_{x,t_{j₀+i}} ⌞ (Ω × G)` converge to `τ⁻¹ C ⌞ (Ω × G)`. For `O ⊂⊂ Ω` and `ρ = t_{j₀+i} R`, `‖δW_i‖(O) = O(ρ^{1-n}‖δV‖(B_ρ(x))) → 0`. Also `Θ^n(μ_{W_i}, y) ≥ 1` unless `x + t_{j₀+i} y` lies in the bad set, whose `μ_{W_i}`-mass in `O` is `O(ρ^{-n} μ_V(bad ∩ B_ρ(x))) → 0`. So 3.7 gives density `≥ 1` a.e. for the limit `τ⁻¹ μ_C ⌞ Ω`, i.e. `Θ^n(μ_C, ·) ≥ τ` `μ_C`-a.e. on `Ω`.
- Calls: `S.varifold_tangents_dlb_ae_hasDensity_of_restricted`, `S.varifold_tangents_dlb_exists_restricted_varifold`, `S.varifold_tangents_dlb_rescaledMeasure_prod_univ`, `S.varifold_tangents_dlb_restricted_bad_set_weight_le`, `S.varifold_tangents_dlb_restricted_firstVariation_control`, `S.varifold_tangents_dlb_restricted_hasDensity`, `S.varifold_tangents_rescaled_divergence_bound`, `S.varifold_tangents_restricted_radon_converges`
- Called by: `S.varifold_tangent_theorems`

##### `S.varifold_tangents_dlb_hasDensity_of_closedBall_scaling`

- Node: `root.varifold_tangents-a1.density_lower_bound-a1.density_scaling-a1`; accepted candidate `d3544e1fe177`
- Statement and proof: Densities transfer under ball-mass scaling (steps 6 and 9 of the blow-up density lower bound used in Simon Ch. 8, 5.5 and 5.7): if `t > 0`, `c ≠ ∞` and `ν(B_ρ(y)) = c t^{-n} μ(B_{tρ}(z))` for `0 < ρ < δ`, then `Θ^n(μ, z) = θ` implies `Θ^n(ν, y) = c θ`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_tangents_dlb_restricted_hasDensity`, `S.varifold_tangents_dlb_ae_hasDensity_of_restricted`

##### `S.varifold_tangents_dlb_rescaledMeasure_prod_univ`

- Node: `root.varifold_tangents-a1.density_lower_bound-a1.rescaled_mass_formula-a1`; accepted candidate `fcadd8a73118`
- Statement and proof: **Masses of the rescaled varifold on cylinders and closed balls** (child `rescaled_mass_formula` of `varifold_tangents.density_lower_bound`, Simon Ch. 8, 5.5): for every real `t` and Borel `A ⊆ ℝ^N`, `V_{x,t}(A × G(N,n)) = t^{-n} μ_V({z : t⁻¹(z - x) ∈ A})`, because the preimage of `A × G(N,n)` under `(z, S) ↦ (t⁻¹(z - x), S)` is `{z : t⁻¹(z - x) ∈ A} × G(N,n)`; and for `t > 0`, `V_{x,t}(B_ρ(y) × G(N,n)) = t^{-n} μ_V(B_{tρ}(x + ty))`, because `t⁻¹(w - x) - y = t⁻¹(w - (x + ty))` gives `{w : t⁻¹(w - x) ∈ B_ρ(y)} = B_{tρ}(x + ty)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_tangents_dlb_restricted_bad_set_weight_le`, `S.varifold_tangents_dlb_restricted_hasDensity`, `S.varifold_tangents_density_lower_bound`

##### `S.varifold_tangents_dlb_exists_restricted_varifold`

- Node: `root.varifold_tangents-a1.density_lower_bound-a1.restricted_varifold-a1`; accepted candidate `9698262c000a`
- Statement and proof: **Simon Ch. 8, proofs of 5.5 and 5.7, restricted varifolds** (child `restricted_varifold` of the density lower bound for varifold tangents): the construction of `W_j = τ⁻¹ V_{x,λ_j} ⌞ Gₙ(Ω)` and `C_Ω = τ⁻¹ C ⌞ Gₙ(Ω)`, for a general measure `μ`. If `Ω` is open, `c < ∞` and `μ(K × G(N,n)) < ∞` for every compact `K ⊆ Ω`, then `c • μ ⌞ (Ω × G(N,n))` vanishes on `Ωᶜ × G(N,n)` (disjoint from `Ω × G(N,n)`) and is finite on `K × G(N,n)` for compact `K ⊆ Ω`, so it is a varifold on `Ω`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_tangents_density_lower_bound`

##### `S.varifold_tangents_dlb_restricted_firstVariation_control`

- Node: `root.varifold_tangents-a1.density_lower_bound-a1.first_variation_control-a1`; accepted candidate `5725f723329d`
- Statement and proof: **Simon Ch. 8, proof of 5.5, step 5** (child `first_variation_control` of `density_lower_bound`): if `W = c · μ ⌞ Gₙ(Ω)` with `c < ∞` and `|∫ div_S X dμ| ≤ β < ∞` for every `C¹` field `X` with `|X| ≤ 1` and compact support in `Ω`, then `W` has locally bounded first variation and `‖δW‖(O) ≤ c β` for every open `O ⊂⊂ Ω`. On test fields `div_S X` vanishes off `Gₙ(Ω)`, so `δW(X) = c ∫ div_S X dμ`; every term of the supremum (8.2.5) is then at most `c β`, and on `O ⊂⊂ Ω` that supremum is `‖δW‖(O)` (`firstVariationRieszMeasure_eq_norm`).
- Calls: — (no accepted declaration; library only)
- Called by: `S.varifold_tangents_density_lower_bound`

##### `S.varifold_tangents_dlb_restricted_bad_set_weight_le`

- Node: `root.varifold_tangents-a1.density_lower_bound-a1.bad_set_weight-a1`; accepted candidate `dc3341f54037`
- Statement and proof: Bad-set mass in the restricted blow-up (step 7 of the parent `density_lower_bound` proof, Simon Ch. 8, 5.5 and 5.7, for one scale `t`): if `W = c V_{x,t} ⌞ (B°_R(0) × G(N,n))` and `O ⊆ B°_R(0)`, then `μ_W({y : x + t y ∈ E} ∩ O) ≤ c R^n μ_V(B_{tR}(x) ∩ E) / (tR)^n`, the measures being applied to arbitrary sets as outer measures.
- Calls: `S.varifold_tangents_dlb_rescaledMeasure_prod_univ`
- Called by: `S.varifold_tangents_density_lower_bound`

##### `S.varifold_tangents_dlb_restricted_hasDensity`

- Node: `root.varifold_tangents-a1.density_lower_bound-a1.restricted_density-a1`; accepted candidate `d3a87527a4de`
- Statement and proof: **Densities of the restricted blow-up** (child `restricted_density` of `varifold_tangents.density_lower_bound`, Simon Ch. 8, 5.5): if `t > 0`, `c ≠ ∞`, `W = c V_{x,t} ⌞ (B°_R(0) × G(N,n))` and `Θ^n(μ_V, x + ty) = θ` at a point `y ∈ B°_R(0)`, then `Θ^n(μ_W, y) = cθ`. For `0 < ρ < R - |y|` the closed ball `B_ρ(y)` lies in `B°_R(0)`, so the restriction does not cut it and `μ_W(B_ρ(y)) = c t^{-n} μ_V(B_{tρ}(x + ty))` by the rescaled mass formula; the scaling lemma for densities (with centre `z = x + ty`) then gives the density.
- Calls: `S.varifold_tangents_dlb_hasDensity_of_closedBall_scaling`, `S.varifold_tangents_dlb_rescaledMeasure_prod_univ`
- Called by: `S.varifold_tangents_density_lower_bound`

##### `S.varifold_tangents_dlb_ae_hasDensity_of_restricted`

- Node: `root.varifold_tangents-a1.density_lower_bound-a1.density_pullback-a1`; accepted candidate `35333fdd3c68`
- Statement and proof: **Simon Ch. 8, step 9 of the use of 3.7 in 5.5 and 5.7** (child `density_pullback` of `density_lower_bound`): if `μ_W = c μ_V ⌞ Ω` with `0 < c < ∞` (`W.measure = c V ⌞ (Ω × G)`) and `Θ^n(μ_W, ·) ≥ 1` holds `μ_W`-a.e., then `Θ^n(μ_V, ·) ≥ c⁻¹` holds `μ_V`-a.e. on `Ω`. Near a good `y ∈ Ω`, `μ_V(B_ρ(y)) = c⁻¹ μ_W(B_ρ(y))` for small `ρ`, so `density_scaling` with `t = 1` gives `Θ^n(μ_V, y) = c⁻¹ Θ^n(μ_W, y) ≥ c⁻¹`.
- Calls: `S.varifold_tangents_dlb_hasDensity_of_closedBall_scaling`
- Called by: `S.varifold_tangents_density_lower_bound`

### `S.plane_disintegration`

- Node: `root.plane_disintegration-a1`; accepted candidate `b7235ce00be4`
- Statement and proof: **Simon Ch. 8, Lemma 1.3, pp. 207–208** (child `plane_disintegration` of `main_theorem`): the measures `η_V^(x)` on `G(N,n)` that disintegrate `V` along its weight `μ_V`. Child `plane_disint_pointwise_measure` gives, for `μ_V`-a.e. `x`, a probability measure that is the limit of the normalized slices of `V` over `B_ρ(x)`. `η(x)` is such a measure wherever one exists; its value on the remaining `μ_V`-null set is irrelevant (the printed lemma only defines `η_V^(x)` for `μ_V`-a.e. `x`). The second part is child `plane_disint_identity_of_limits` applied to this `η`.
- Calls: `S.plane_disint_identity_of_limits`, `S.plane_disint_pointwise_measure`
- Called by: `S.first_rectifiability_theorem`, `S.allard_rectifiability_and_tangent_cones`

#### `S.plane_disint_slice_density`

- Node: `root.plane_disintegration-a1.slice_density-a1`; accepted candidate `088f75cf0931`
- Statement and proof: **Simon Ch. 8, Lemma 1.3, printed (1)–(2)** (child `slice_density` of `plane_disintegration`): for continuous `β ≥ 0` on `G(N,n)`, the `β`-weighted slices `γ(B) = ∫_{Gₙ(B)} β(S) dV(y,S)` of `V` are differentiated by `μ_V`: the ratio `γ(B_ρ(x)) / μ_V(B_ρ(x))` tends to a Borel `e(x)` for `μ_V`-a.e. `x`, and `γ(A) = ∫_A e dμ_V` for Borel `A`. Since `γ ≤ ‖β‖ μ_V`, `γ` is the zero extension of a locally finite measure on `U`, so SimonGMT's Besicovitch differentiation on `U` (`Varifold.ae_tendsto_firstVariationDensity_of_domainMeasure`) and Radon–Nikodym apply, with `e = (dγ/dμ_V).toReal`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.plane_disint_pointwise_measure`, `S.plane_disint_identity_of_limits`

#### `S.plane_disint_riesz_limit`

- Node: `root.plane_disintegration-a1.riesz_limit-a1`; accepted candidate `21b19ab73ec5`
- Statement and proof: **Simon Ch. 8, proof of Lemma 1.3, printed (3)–(4) and the Riesz step** (child `riesz_limit` of `plane_disintegration`): if `m ρ` is eventually a probability measure on `G(N,n)` and `∫ f dm_ρ` converges along the nontrivial filter `l` for every `f` in a dense `D ⊆ C(G(N,n), ℝ)`, then `∫ f dm_ρ → ∫ f dη` for every `f ∈ C(G(N,n), ℝ)` and some probability measure `η`. The estimate `|∫ f dm - ∫ g dm| ≤ ‖f - g‖` makes `ρ ↦ ∫ f dm_ρ` Cauchy along `l`; the limit `L f` is a positive linear functional with `L 1 = 1`, and Riesz–Markov–Kakutani on the compact space `G(N,n)` represents it by `η`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.plane_disint_pointwise_measure`

#### `S.plane_disint_pointwise_measure`

- Node: `root.plane_disintegration-a1.pointwise_measure-a1`; accepted candidate `fb766d9613ad`
- Statement and proof: **Simon Ch. 8, proof of Lemma 1.3, first part, pp. 207–208** (child `pointwise_measure` of `plane_disintegration`): for `μ_V`-a.e. `x` the normalized slices of `V` over `B_ρ(x)` converge, as `ρ ↓ 0`, to a probability measure `η` on `G(N,n)`. Take a dense sequence `f_j` in the separable space `C(G(N,n), ℝ)` and apply `plane_disint_slice_density` to `β_j = f_j + ‖f_j‖ ≥ 0`. At a point `x ∈ U ∩ spt μ_V` where all these limits exist, the slice measures `m_ρ = μ_V(B_ρ(x))⁻¹ σ_#(V ⌞ (B_ρ(x) × G(N,n)))`, `σ(y, S) = S`, satisfy `∫ f dm_ρ = (∫_{B_ρ(x) × G(N,n)} f(S) dV) / μ_V(B_ρ(x))` and are probability measures for small `ρ`, and `∫ f_j dm_ρ = ∫ β_j dm_ρ - ‖f_j‖` converges for every `j`; `plane_disint_riesz_limit` gives `η`.
- Calls: `S.plane_disint_riesz_limit`, `S.plane_disint_slice_density`
- Called by: `S.plane_disintegration`

#### `S.plane_disint_identity_of_limits`

- Node: `root.plane_disintegration-a1.identity_of_limits-a1`; accepted candidate `c18b8aef1792`
- Statement and proof: **Simon Ch. 8, Lemma 1.3, last part** (child `identity_of_limits` of `plane_disintegration`): if for `μ_V`-a.e. `x` the measure `η(x)` on `G(N,n)` is a probability measure and the slice ratios `(∫_{Gₙ(B_ρ(x))} β(S) dV(y,S)) / μ_V(B_ρ(x))` tend to `∫ β dη(x)` for every continuous `β`, then `∫_{Gₙ(A)} β(S) dV(y,S) = ∫_A ∫ β dη(x) dμ_V(x)` for Borel `A` and continuous `β ≥ 0`. The density `e` of `plane_disint_slice_density` is the limit of the same ratios, so `e(x) = ∫ β dη(x)` for `μ_V`-a.e. `x` by uniqueness of limits ("`e(x,j)` is exactly `η̃_V^(x)(β_j)`").
- Calls: `S.plane_disint_slice_density`
- Called by: `S.plane_disintegration`

### `S.tangent_points_lipschitz_graph_cover`

- Node: `root.tangent_graph_cover-a1`; accepted candidate `1356c1e222f8`
- Statement and proof: **Tangent points with nearly horizontal planes lie on countably many closed `L`-Lipschitz graphs** (node `tangent_graph_cover`; the cone argument of Simon's proof of Ch. 3, 1.6 "⇐", which the proof of Ch. 8, 1.2 invokes through Ch. 3, 1.9). For `0 < L ≤ 1` and `P ∈ G(N,n)` there are closed sets `Γ_i` with `|q(y - z)| ≤ L |p(y - z)|` on each `Γ_i` (`p = p_P`, `q = I - p`) containing every point `x` at which `V` has a tangent plane `T` (Def. 1.1) with `‖p_T - p‖ ≤ L/4`. For `n = 0` such points are atoms of `μ_V`, hence countably many, and singletons are `L`-graphs. For `n ≥ 1` each such point satisfies the lower mass bound `c t^n ≤ μ_V(B_t(x))` for small `t` (any `0 < c < θ ω_n`) and the cone decay `μ_V({y ∈ B_t(x) : (L/16)|y - x| ≤ |q_T(y - x)|}) ≤ ε t^n` for small `t`, which is all the uniform-class/graph construction needs.
- Calls: `S.tgc_cone_density_graph_cover`, `S.tgc_dim_zero_tangent_points_countable`, `S.tgc_tangent_cone_weight_decay`, `S.tgc_tangent_weight_lower_bound`
- Called by: `S.first_rectifiability_theorem`, `S.integral_compactness_theorem`

#### `S.tgc_weight_blowup_tendsto`

- Node: `root.tangent_graph_cover-a1.weight_blowup-a1`; accepted candidate `63f81b1cb898`
- Statement and proof: Weight blow-ups at a tangent point (Simon Ch. 8, Definition 1.1 tested with `f(y,S) = g(y)`): if `V` has tangent plane `T` with multiplicity `θ` at `x`, then for every `g ∈ C_c(ℝ^N)`, `t^{-n} ∫ g(t^{-1}(y - x)) dμ_V(y) → θ ∫_T g dH^n` as `t ↓ 0`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.tgc_tangent_weight_lower_bound`, `S.tgc_tangent_cone_weight_decay`

#### `S.tgc_plane_closedBall_hausdorff`

- Node: `root.tangent_graph_cover-a1.plane_ball_measure-a1`; accepted candidate `45996d70dd49`
- Statement and proof: `H^n(T ∩ B_r(0)) = ω_n r^n` for an `n`-plane `T ∈ G(N,n)` and every `r ≥ 0` (step (1.2) of the tangent graph cover proof): an isometric parametrization of `T` by `ℝ^n` carries `H^n` on `T` to Lebesgue measure on `ℝ^n`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.tgc_tangent_weight_lower_bound`, `S.tgc_tangent_cone_weight_decay`

#### `S.tgc_tangent_weight_lower_bound`

- Node: `root.tangent_graph_cover-a1.lower_mass_bound-a1`; accepted candidate `05c20a437137`
- Statement and proof: **Lower mass bound at a tangent point** (child `lower_mass_bound` of `tangent_graph_cover`, step (1.3) of its proof, in eventual form): if `V` has tangent plane `T` with multiplicity `θ` at `x`, then for every `c < θ ω_n` we have `c t^n ≤ μ_V(B_t(x))` for all small `t > 0`. Choose `κ ∈ (0,1)` with `c < θ ω_n κ^n` and the cut-off `g = min(1, max(0, (1 - |v|)/(1 - κ)))`, so that `1_{B_κ(0)} ≤ g ≤ 1_{B_1(0)}`. Then `θ ∫_T g dH^n ≥ θ H^n(T ∩ B_κ(0)) = θ ω_n κ^n > c` (`plane_ball_measure`), the weight blow-ups `t^{-n} ∫ g((y - x)/t) dμ_V(y)` tend to `θ ∫_T g dH^n` (`weight_blowup`), and each of them is at most `t^{-n} μ_V(B_t(x))`.
- Calls: `S.tgc_plane_closedBall_hausdorff`, `S.tgc_weight_blowup_tendsto`
- Called by: `S.tgc_dim_zero_tangent_points_countable`, `S.tangent_points_lipschitz_graph_cover`

#### `S.tgc_tangent_cone_weight_decay`

- Node: `root.tangent_graph_cover-a1.cone_decay-a1`; accepted candidate `74924bc74356`
- Statement and proof: **Cone decay at a tangent point** (child `cone_decay` of `tangent_graph_cover`, step (1.4) of its proof; the varifold form of the second limit in Simon Ch. 3, Remark 1.5(3), for a tangent plane as in Ch. 8, 1.1): if `V` has tangent plane `T` with multiplicity `θ` at `x` and `n ≥ 1`, then for every `β > 0` the cone section `{y ∈ B_t(x) : β|y - x| ≤ |(y - x) - p_T(y - x)|}` has `μ_V`-mass `o(t^n)` as `t ↓ 0`. The rescaled section `C` meets `T` only at `0`, an `H^n`-null set, so a cut-off `g ≥ 1_C` has `θ ∫_T g dH^n` as small as we like, and the weight blow-ups of `g` bound `t^{-n}` times the `μ_V`-mass of the section.
- Calls: `S.tgc_plane_closedBall_hausdorff`, `S.tgc_weight_blowup_tendsto`
- Called by: `S.tangent_points_lipschitz_graph_cover`

#### `S.tgc_dim_zero_tangent_points_countable`

- Node: `root.tangent_graph_cover-a1.dim_zero_countable-a1`; accepted candidate `f232db531b90`
- Statement and proof: **Dimension `0`: tangent points are atoms of `μ_V`** (child `dim_zero_countable` of `tangent_graph_cover`, step 2 of its proof). If the `0`-varifold `V` has a tangent plane with multiplicity `θ` at `x`, then for `0 < c < θ ω_0` the lower mass bound gives `c ≤ μ_V(B_t(x))` for all small `t > 0`; `μ_V` is finite on a small closed ball about `x ∈ U`, and `B_t(x) ↓ {x}` as `t ↓ 0`, so `μ_V({x}) ≥ c > 0`. The σ-finite measure `μ_V` has only countably many atoms.
- Calls: `S.tgc_tangent_weight_lower_bound`
- Called by: `S.tangent_points_lipschitz_graph_cover`

#### `S.tgc_tilted_cone_inclusion`

- Node: `root.tangent_graph_cover-a1.cone_linear_algebra-a1`; accepted candidate `a598d9a0284c`
- Statement and proof: Linear algebra of tilted cones (step 3, (3.1)–(3.2), of the tangent-graph cover, with `c = L/4` and `γ = L/8`): if `‖p_T u - p_P u‖ ≤ (L/4)‖u‖` for all `u` and `v` violates the `L`-graph inequality over `P`, i.e. `L‖p_P v‖ < ‖v - p_P v‖`, then every `w` with `‖w - v‖ ≤ (L/8)‖v‖` lies in the cone `(L/16)‖w‖ ≤ ‖w - p_T w‖` around `T^⊥`, and `‖w‖ ≤ 2‖v‖`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.tgc_cone_density_graph_cover`

#### `S.tgc_cone_density_graph_cover`

- Node: `root.tangent_graph_cover-a1.cone_graph_cover-a1`; accepted candidate `d259cdfbfb38`
- Statement and proof: Cone/density covering lemma (steps 4–6 of the tangent-graph cover; Simon Ch. 3, Thm 1.6, printed (7)–(10), for an arbitrary measure `μ`): if every `x ∈ A` has a plane `T` tilted from `P` by at most `L/4`, an eventual lower mass bound `c t^n ≤ μ(B_t(x))` with `c > 0`, and eventual cone mass `μ{y ∈ B_t(x) : (L/16)‖y - x‖ ≤ ‖(y - x) - p_T(y - x)‖} ≤ ε t^n` for every `ε > 0`, then `A` is covered by countably many closed `L`-Lipschitz graphs over `P`.
- Calls: `S.tgc_eventual_density_bounds_uniform`, `S.tgc_local_graph_closed_cover`, `S.tgc_tilted_cone_inclusion`
- Called by: `S.tangent_points_lipschitz_graph_cover`

##### `S.tgc_local_graph_closed_cover`

- Node: `root.tangent_graph_cover-a1.cone_graph_cover-a1.local_graph_closed_cover-a1`; accepted candidate `8ab6d6be7d96`
- Statement and proof: Closed graph pieces from a local graph property (the localization `E_j ∩ B_{δ/4}(x_0)` after printed (10) in Simon Ch. 3, Thm 1.6, p. 74, with closures taken): if the `L`-graph inequality over `P` holds for all points of `E` at distance `≤ r`, then `E` is covered by countably many closed sets on each of which it holds for all pairs of points.
- Calls: — (no accepted declaration; library only)
- Called by: `S.tgc_cone_density_graph_cover`

##### `S.tgc_eventual_density_bounds_uniform`

- Node: `root.tangent_graph_cover-a1.cone_graph_cover-a1.density_bounds_uniform-a1`; accepted candidate `9ccedd5d1653`
- Statement and proof: Uniformization of eventual density bounds (Simon Ch. 3, 1.6, replacing Egoroff's theorem in (7)–(9)): if `c t^n ≤ F(t)` eventually for some `c > 0` and `G(t) ≤ ε t^n` eventually for every `ε > 0`, then for some `m, k` both `t^n/(m+1) ≤ F(t)` and `G(t) ≤ β t^n/(m+1)` hold for all `t ∈ (0, 1/(k+1)]`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.tgc_cone_density_graph_cover`

### `S.first_rectifiability_theorem`

- Node: `root.first_rectifiability-a1`; accepted candidate `cc22d38987f6`
- Statement and proof: **Simon Ch. 8, 1.2 (First Rectifiability Theorem), p. 206** (child `first_rectifiability` of `root`; Step 9 of its proof, assembling Steps 0–8). Let `M = {x ∈ spt μ_V : T_x, θ(x) exist}` and let `θ(x)` be the multiplicity of a tangent plane at `x` (and `0` off `M`). Points of `M` have density `θ(x)`, and `μ_V(ℝ^N ∖ M) = 0`. For every `L ∈ (0,1]`, countably many closed `L`-flat graphs cover `M` (sibling `tangent_points_lipschitz_graph_cover`), so `M` is `H^n`-null-measurable and countably `n`-rectifiable, and `μ_V = θ H^n ⌞ M`. Lemma 1.3 (sibling `plane_disintegration`) gives `V(A) = μ_V({x : (x, T_x) ∈ A})`. On `M` the tangent plane `T_x` is the unique approximate tangent plane of `(M, θ)` at `x`, which turns this identity into `V = v(M, θ)`.
- Calls: `S.frt_carrier_nullMeasurable`, `S.frt_countablyRectifiable_of_graph_cover`, `S.frt_tangent_plane_hasDensity`, `S.frt_tangent_plane_unique`, `S.frt_tangent_points_flat_graph_cover`, `S.frt_varifold_eq_tangent_graph_measure`, `S.frt_weight_eq_multiplicity_hausdorff`, `S.frt_weighted_approx_tangent`, `S.plane_disintegration`, `S.tangent_points_lipschitz_graph_cover`
- Called by: `S.allard_rectifiability_and_tangent_cones`, `S.integral_compactness_theorem`, `main_theorem`

#### `S.frt_weight_blowup_tendsto`

- Node: `root.first_rectifiability-a1.weight_blowup-a1`; accepted candidate `b951e87c9540`
- Statement and proof: Weight blow-ups at a tangent point (Simon Ch. 8, Definition 1.1 tested with `f(y,S) = g(y)`): if `V` has tangent plane `T` with multiplicity `θ` at `x`, then for every `g ∈ C_c(ℝ^N)`, `t^{-n} ∫ g(t^{-1}(z - x)) dμ_V(z) → θ ∫_T g dH^n` as `t ↓ 0`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_tangent_plane_hasDensity`, `S.frt_tangent_plane_unique`, `S.frt_weighted_approx_tangent`, `S.allard_tc_tangent_plane_dilation`

#### `S.frt_tangent_plane_hasDensity`

- Node: `root.first_rectifiability-a1.tangent_density-a1`; accepted candidate `fd22334dcfbc`
- Statement and proof: Density at a tangent point (Simon Ch. 8, 1.2, step (0c); Ch. 3, Remark 1.8(2)): if `V` has tangent plane `T` with multiplicity `θ` at `x`, then `Θ^n(μ_V, x) = θ`, i.e. `μ_V(B_t(x)) / (ω_n t^n) → θ` as `t ↓ 0`.
- Calls: `S.frt_td_ball_mass_lower_of_blowup`, `S.frt_td_ball_mass_upper_of_blowup`, `S.frt_td_hasDensity_of_ball_mass_bounds`, `S.frt_weight_blowup_tendsto`
- Called by: `S.frt_tangent_plane_unique`, `S.first_rectifiability_theorem`

##### `S.frt_td_plane_closedBall_hausdorff`

- Node: `root.first_rectifiability-a1.tangent_density-a1.plane_ball-a1`; accepted candidate `c6446adb6504`
- Statement and proof: The `n`-dimensional Hausdorff measure of the closed ball `B_r(0)` of an `n`-plane `T ∈ G(N,n)` is `ω_n r^n` (Simon Ch. 3, Remark 1.8(2); step 3 of the tangent-plane density proof for Simon Ch. 8, 1.2): `H^n` is transported to Lebesgue measure on `ℝ^n` along an isometric parametrization of `T`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_td_ball_mass_lower_of_blowup`, `S.frt_td_ball_mass_upper_of_blowup`

##### `S.frt_td_ball_mass_lower_of_blowup`

- Node: `root.first_rectifiability-a1.tangent_density-a1.lower_bound-a1`; accepted candidate `a7c673c512c2`
- Statement and proof: Lower ball-mass bound from weight blow-ups (Simon Ch. 3, Remark 1.8(2), lower cutoff): if `t^{-n} ∫ g(t^{-1}(z - x)) dμ(z) → θ ∫_T g dH^n` as `t ↓ 0` for every `g ∈ C_c(ℝ^N)`, then for every `c < θ ω_n` we have `c t^n ≤ μ(B_t(x))` for all small `t > 0`.
- Calls: `S.frt_td_plane_closedBall_hausdorff`
- Called by: `S.frt_tangent_plane_hasDensity`

##### `S.frt_td_ball_mass_upper_of_blowup`

- Node: `root.first_rectifiability-a1.tangent_density-a1.upper_bound-a1`; accepted candidate `94a8feb2121a`
- Statement and proof: Upper ball-mass bound from the blow-up limit (Simon Ch. 8, 1.2, Steps 2, 4 and 6; the upper cutoff of Simon Ch. 3, Remark 1.8(2)): if `t⁻ⁿ ∫ g(t⁻¹(z - x)) dμ(z) → θ ∫_T g dHⁿ` for every `g ∈ C_c(ℝ^N)` and `μ(B_{r₀}(x)) < ∞`, then `μ(B_t(x)) ≤ c tⁿ` for all small `t > 0` whenever `θ ωₙ < c`. The test function is a cutoff equal to `1` on `B_1(0)` and to `0` off `B_κ(0)`, with `κ > 1` chosen so that `θ ωₙ κⁿ < c`.
- Calls: `S.frt_td_plane_closedBall_hausdorff`
- Called by: `S.frt_tangent_plane_hasDensity`

##### `S.frt_td_hasDensity_of_ball_mass_bounds`

- Node: `root.first_rectifiability-a1.tangent_density-a1.density_squeeze-a1`; accepted candidate `cf2186673663`
- Statement and proof: Density squeeze (Simon Ch. 3, Remark 1.8(2), last step): if, as `t ↓ 0`, eventually `c t^n ≤ μ(B_t(x))` for every `c < a ω_n` and eventually `μ(B_t(x)) ≤ c t^n` for every `c > a ω_n`, then `Θ^n(μ, x) = a`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_tangent_plane_hasDensity`

#### `S.frt_tangent_plane_unique`

- Node: `root.first_rectifiability-a1.tangent_unique-a1`; accepted candidate `d765c5b1d75a`
- Statement and proof: **Simon Ch. 8, Definition 1.1: the tangent space and its multiplicity are unique** (child `tangent_unique` of `first_rectifiability`: step (0d) of the parent's proof of 1.2; cf. Ch. 3, Remark 1.5(1)). If `V` has tangent space `T` with multiplicity `θ` and `T'` with multiplicity `θ'` at `x`, then `T' = T` and `θ' = θ`. Both multiplicities are the density `Θ^n(μ_V, x)`; the weight blow-ups then give `∫ g dH^n⌞T' = ∫ g dH^n⌞T` for every `g ∈ C_c(ℝ^N)`, so the regular measures `H^n⌞T'` and `H^n⌞T` agree, hence so do their supports `T'` and `T`; a projection matrix is determined by its range.
- Calls: `S.frt_tangent_plane_hasDensity`, `S.frt_weight_blowup_tendsto`
- Called by: `S.first_rectifiability_theorem`

#### `S.frt_tangent_points_flat_graph_cover`

- Node: `root.first_rectifiability-a1.tangent_graph_cover_all-a1`; accepted candidate `02e1a2ba9543`
- Statement and proof: The net-of-planes step of Simon Ch. 3, proof of Theorem 1.6 "⇐" (p. 73), for the tangent points of a varifold (Ch. 8, 1.2): suppose that for every `L ∈ (0,1]` and every plane `P` there are closed `L`-graphs `Γ_0, Γ_1, …` over `P` (`|(y - z) - p_P(y - z)| ≤ L |p_P(y - z)|` for `y, z ∈ Γ_i`) containing every `x` at which `V` has a tangent plane `T` with `|p_T v - p_P v| ≤ (L/4)|v|`. Then for every `L ∈ (0,1]` countably many closed `L`-graphs, each paired with its base plane, cover all points at which `V` has a tangent plane. A countable dense set of planes replaces the book's finite net: `S ↦ p_S` is continuous into operators, so every plane is within operator distance `L/4` of a plane of the dense set.
- Calls: — (no accepted declaration; library only)
- Called by: `S.first_rectifiability_theorem`

#### `S.frt_countablyRectifiable_of_graph_cover`

- Node: `root.first_rectifiability-a1.rectifiable_of_graph_cover-a1`; accepted candidate `c982ee9cae42`
- Statement and proof: Sets covered by countably many `1`-graphs are countably `n`-rectifiable (Simon Ch. 3, proof of Theorem 1.6 "⇐", p. 74): if `C` is countable and every `(P, Γ) ∈ C` satisfies `|(y - z) - p_P(y - z)| ≤ |p_P(y - z)|` for `y, z ∈ Γ`, then `p_P` is injective on `Γ` with a `√2`-Lipschitz inverse, so `Γ` lies in the range of a Lipschitz map `ℝ^n → ℝ^N`, and every `M ⊆ ⋃_{c ∈ C} c.2` is countably `n`-rectifiable.
- Calls: — (no accepted declaration; library only)
- Called by: `S.first_rectifiability_theorem`

#### `S.frt_hausdorff_density_one_of_flat_covers`

- Node: `root.first_rectifiability-a1.density_one_flat_covers-a1`; accepted candidate `d56f81d8a40d`
- Statement and proof: Density one of `H^n` on a set covered by closed Lipschitz graphs of arbitrarily small slope (Simon Ch. 8, proof of 1.2, the density-one property of `H^n` on the rectifiable carrier; cf. Ch. 3, 1.6 and 1.9): if `H^n(A) < ∞`, `A` is `H^n`-measurable and, for every `L ∈ (0,1]`, `A` is covered by countably many closed sets `Γ`, each an `L`-graph over some `P ∈ G(N,n)` (`|(y - z) - p_P(y - z)| ≤ L |p_P(y - z)|` on `Γ`), then `Θ^n(H^n ⌞ A, x) = 1` for `H^n ⌞ A`-a.e. `x`.
- Calls: `S.frt_graph_piece_density_bounds`
- Called by: `S.frt_weight_eq_multiplicity_hausdorff`

##### `S.frt_plane_subset_hasDensity_one`

- Node: `root.first_rectifiability-a1.density_one_flat_covers-a1.plane_density-a1`; accepted candidate `a424ee912009`
- Statement and proof: Lebesgue density one of `H^n` on an arbitrary subset `T` of an `n`-plane (Simon Ch. 8, proof of 1.2, via the Lebesgue density theorem in `ℝ^n`): outside an `H^n`-null set `Z`, every `a ∈ T` has `Θ^n(H^n ⌞ T, a) = 1`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_graph_piece_density_bounds`

##### `S.frt_lipschitz_graph_hausdorff_compare`

- Node: `root.first_rectifiability-a1.density_one_flat_covers-a1.graph_projection_compare-a1`; accepted candidate `01455b1b79c6`
- Statement and proof: Hausdorff-measure comparison between an `L`-graph and its projection (used for the density-one property of `H^n` on the carrier in the proof of Simon Ch. 8, 1.2; cf. Ch. 3, 1.6): if `|(y - z) - p_P(y - z)| ≤ L |p_P(y - z)|` for `y, z ∈ S` and `β = (1 + L²)^{1/2}`, then `p_P` is `1`-Lipschitz, and injective on `S` with a `β`-Lipschitz inverse, so for `x ∈ S` and `r ∈ ℝ` `H^n(p_P(S) ∩ B_{r/β}(p_P x)) ≤ H^n(S ∩ B_r(x)) ≤ β^n H^n(p_P(S) ∩ B_r(p_P x))`, and `H^n(S ∩ p_P⁻¹(Y)) ≤ β^n H^n(Y)` for every `Y ⊆ ℝ^N`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_graph_piece_density_bounds`

##### `S.frt_graph_piece_density_bounds`

- Node: `root.first_rectifiability-a1.density_one_flat_covers-a1.graph_piece_bounds-a1`; accepted candidate `3ee36355e1a1`
- Statement and proof: Two-sided density bounds on a closed Lipschitz-graph piece (Simon Ch. 8, proof of 1.2, the density-one step for `H^n ⌞ A` on one graph piece `Γ`): let `H^n(A) < ∞` with `A` `H^n`-measurable, `L ≥ 0`, `β = (1 + L²)^{1/2}`, and let `Γ` be closed with `|(y - z) - p_P(y - z)| ≤ L |p_P(y - z)|` for `y, z ∈ Γ`. Then for `(H^n ⌞ A) ⌞ Γ`-a.e. `x`, with `λ = H^n ⌞ A`, `β^{-n} ≤ liminf_{r↓0} λ(B_r(x)) / (ω_n r^n)` and `limsup_{r↓0} λ(B_r(x)) / (ω_n r^n) ≤ β^n`.
- Calls: `S.frt_lipschitz_graph_hausdorff_compare`, `S.frt_plane_subset_hasDensity_one`
- Called by: `S.frt_hausdorff_density_one_of_flat_covers`

#### `S.frt_weight_null_of_hausdorff_null`

- Node: `root.first_rectifiability-a1.weight_null_of_hausdorff_null-a1`; accepted candidate `cfe16d73c334`
- Statement and proof: Simon Ch. 8, proof of 1.2, step (3a) (the covering comparison of Ch. 1, 3.2): if `H^n(Z) = 0` and `Θ^n(μ, x)` exists and is finite at every `x ∈ Z`, then `μ(Z) = 0`.
- Calls: `S.frt_ball_bound_of_finite_density`, `S.frt_measure_null_of_hausdorff_null_ball_bound`
- Called by: `S.frt_weight_eq_multiplicity_hausdorff`

##### `S.frt_measure_null_of_hausdorff_null_ball_bound`

- Node: `root.first_rectifiability-a1.weight_null_of_hausdorff_null-a1.null_of_ball_bound-a1`; accepted candidate `d9033b3002dd`
- Statement and proof: Simon Ch. 8, proof of 1.2 (the null case of the upper counterpart of the density comparison Ch. 1, 3.3): if `H^n(A) = 0` and `μ(B_ρ(x)) ≤ c ρ^n` for all `x ∈ A` and `0 < ρ ≤ δ`, with `c < ∞`, then `μ(A) = 0` (outer measure; `A` need not be measurable).
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_weight_null_of_hausdorff_null`

##### `S.frt_ball_bound_of_finite_density`

- Node: `root.first_rectifiability-a1.weight_null_of_hausdorff_null-a1.finite_density_ball_bound-a1`; accepted candidate `4639a3515d00`
- Statement and proof: Finite density gives a small-ball mass bound (Simon Ch. 8, proof of 1.2: the decomposition `Z = ⋃ Z_{k,j}` at a single point). If `Θ^n(μ, x) = θ < ∞`, then there are `K, j ∈ ℕ` with `μ(B_ρ(x)) ≤ K ρ^n` for all `0 < ρ ≤ 1/(j+1)`: eventually `μ(B_ρ(x))/(ω_n ρ^n) < m` for a natural `m > θ`, and `K` is any natural number above `m ω_n`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_weight_null_of_hausdorff_null`

#### `S.frt_hausdorff_null_of_weight_null`

- Node: `root.first_rectifiability-a1.hausdorff_null_of_weight_null-a1`; accepted candidate `1c558e99170e`
- Statement and proof: Step (3b) in the proof of Simon Ch. 8, 1.2 (child `hausdorff_null_of_weight_null` of `first_rectifiability`), via Simon Ch. 1, 3.3: let `U` be open and `μ` finite on compact subsets of `U`. If `Z ⊆ U` is `μ`-null and `limsup_{ρ↓0} μ(B_ρ(x)) / (ω_n ρ^n) > 0` at every `x ∈ Z`, then `H^n(Z) = 0`. For `Z_m = {x ∈ Z : limsup ≥ 1/m}`, Simon 3.3 gives `(1/m) H^n(Z_m) ≤ μ(O)` for every open `O ⊇ Z_m`, and there are such `O` with `μ(O)` arbitrarily small.
- Calls: `S.frt_hnw_exists_open_superset_measure_lt`, `S.frt_hnw_unitBallVolume_eq_gamma`
- Called by: `S.frt_carrier_nullMeasurable`, `S.frt_weight_eq_multiplicity_hausdorff`

##### `S.frt_hnw_unitBallVolume_eq_gamma`

- Node: `root.first_rectifiability-a1.hausdorff_null_of_weight_null-a1.unit_ball_volume-a1`; accepted candidate `9bc587bd7615`
- Statement and proof: `ω_n = π^{n/2} / Γ(n/2 + 1)` for every `n ∈ ℕ` (including `ω_0 = 1`): for `n = 0` the volume of `EuclideanSpace ℝ (Fin 0)` is the Dirac mass at `0`, and for `n ≥ 1` this is `EuclideanSpace.volume_ball` at radius `1` together with `√π ^ n = π ^ (n / 2)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_hausdorff_null_of_weight_null`

##### `S.frt_hnw_exists_open_superset_measure_lt`

- Node: `root.first_rectifiability-a1.hausdorff_null_of_weight_null-a1.small_open_superset-a1`; accepted candidate `5061cb8d004f`
- Statement and proof: Small open neighbourhoods of null sets (used for the First Rectifiability Theorem, Simon Ch. 8, 1.2): if `μ` is finite on compact subsets of the open set `U` and `Z ⊆ U` is `μ`-null, then for every `ζ > 0` there is an open `O` with `Z ⊆ O ⊆ U` and `μ(O) < ζ`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_hausdorff_null_of_weight_null`

#### `S.frt_carrier_nullMeasurable`

- Node: `root.first_rectifiability-a1.carrier_null_measurable-a1`; accepted candidate `3f2c933122da`
- Statement and proof: The carrier is `H^n`-measurable (Simon Ch. 8, 1.2, the printed claim "`M` is `H^n`-measurable", which Ch. 3, 1.9 presupposes): if `M ⊆ U`, `μ_V(ℝ^N ∖ M) = 0` and `Θ^n(μ_V, x) = θ(x) > 0` for every `x ∈ M`, then `M` is `H^n`-null-measurable. `M` is the countable union of the sets `M ∩ closure (F_{m,k} ∩ C_j)`, where `F_{m,k} ⊆ M` carries a uniform lower density bound and the closed sets `C_j ⊆ U` cover `U`; each is a closed set minus an `H^n`-null set.
- Calls: `S.frt_cnm_densityRatio_lower_closure`, `S.frt_cnm_exists_uniform_densityRatio_lower`, `S.frt_hausdorff_null_of_weight_null`
- Called by: `S.frt_weight_eq_multiplicity_hausdorff`, `S.first_rectifiability_theorem`

##### `S.frt_cnm_exists_uniform_densityRatio_lower`

- Node: `root.first_rectifiability-a1.carrier_null_measurable-a1.uniform_lower_density-a1`; accepted candidate `d4df867dc561`
- Statement and proof: Uniform lower density bound (Simon Ch. 8, 1.2, Step 1 "uniform pieces" of the proof that `M` is `H^n`-measurable): if `Θ^n(μ, x) = t > 0` (`t = ∞` allowed), then for some `m, k ∈ ℕ`, `(2(m+1))⁻¹ ≤ μ(B_ρ(x))/(ω_n ρ^n)` for every `0 < ρ ≤ 1/(k+1)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_carrier_nullMeasurable`

##### `S.frt_cnm_densityRatio_lower_closure`

- Node: `root.first_rectifiability-a1.carrier_null_measurable-a1.closure_lower_density-a1`; accepted candidate `05f4ed7898af`
- Statement and proof: Uniform lower density-ratio bounds pass to the closure (Step 4 of the proof that the carrier `M` in Simon Ch. 8, 1.2 is `H^n`-measurable): if `c ≤ μ(B_ρ(x))/(ω_n ρ^n)` for all `x ∈ E` and `0 < ρ ≤ δ`, then the same holds for all `y ∈ closure E`, since `B_s(x) ⊆ B_ρ(y)` whenever `s + |x - y| ≤ ρ`, and `s ↑ ρ`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_carrier_nullMeasurable`

#### `S.frt_weight_eq_multiplicity_hausdorff`

- Node: `root.first_rectifiability-a1.weight_eq_theta_hausdorff-a1`; accepted candidate `babeb3d26bfc`
- Statement and proof: Simon Ch. 8, 1.2, Step 6 (`μ_V = H^n ⌞ θ`): if `μ_V(ℝ^N ∖ M) = 0`, `M ⊆ U`, `μ_V` has density `θ(x) ∈ (0, ∞)` at every `x ∈ M`, and for every `L ∈ (0, 1]` `M` is covered by countably many closed `L`-graphs over `n`-planes, then `θ` is `H^n`-integrable on `M ∩ K` for every compact `K ⊆ U` and `μ_V(B) = ∫_{B ∩ M} θ dH^n` for every `μ_V`-null-measurable `B`.
- Calls: `S.frt_carrier_nullMeasurable`, `S.frt_hausdorff_density_one_of_flat_covers`, `S.frt_hausdorff_null_of_weight_null`, `S.frt_weight_null_of_hausdorff_null`, `S.frt_weq_density_borel_representative`, `S.frt_weq_mul_hausdorff_le_of_upper_density`, `S.frt_weq_open_compact_exhaustion`, `S.frt_weq_piece_restrict_eq_density`
- Called by: `S.first_rectifiability_theorem`

##### `S.frt_weq_open_compact_exhaustion`

- Node: `root.first_rectifiability-a1.weight_eq_theta_hausdorff-a1.open_compact_exhaustion-a1`; accepted candidate `bba9b40575a6`
- Statement and proof: A compact exhaustion of an open `U ⊆ ℝ^N` (preamble of the proof of Simon Ch. 8, 1.2): compact `K_p ⊆ U`, `p ∈ ℕ`, with `K_p ⊆ interior K_{p+1}`, increasing in `p`, and `⋃_p K_p = U`. If `U = ℝ^N` then `K_p = B_{p+1}(0)`; otherwise, with `F = ℝ^N ∖ U`, `K_p = {x : |x| ≤ p + 1, dist(x, F) ≥ 1/(p + 1)}`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_weight_eq_multiplicity_hausdorff`

- *(reused here: `S.frt_weq_density_borel_representative`, node `root.first_rectifiability-a1.weight_eq_theta_hausdorff-a1.density_borel_representative-a1` — see above)*
##### `S.frt_weq_mul_hausdorff_le_of_upper_density`

- Node: `root.first_rectifiability-a1.weight_eq_theta_hausdorff-a1.upper_density_hausdorff_bound-a1`; accepted candidate `6df89ae06153`
- Statement and proof: Upper-density comparison with `H^n` (Simon Ch. 1, 3.3, in the form used for Ch. 8, 1.2): if `W` is open, `A ⊆ W` and `t ≤ limsup_{ρ↓0} μ(B_ρ(x))/(ω_n ρ^n)` for every `x ∈ A`, then `t H^n(A) ≤ μ(W)`. Mathlib's `μHE[n]` is `c • μH[n]` for a Haar scalar `c`; the isodiametric inequality (Simon Ch. 1, 2.10, by Steiner symmetrization) gives `c 2^n ≤ ω_n`, and Vitali's covering lemma with Simon's finite-tail argument bounds `μH[n](A)` by the radii of disjoint good balls.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_weight_eq_multiplicity_hausdorff`

##### `S.frt_weq_nondensity_points_null`

- Node: `root.first_rectifiability-a1.weight_eq_theta_hausdorff-a1.lebesgue_density_subset-a1`; accepted candidate `274b9011f59f`
- Statement and proof: Lebesgue density for an arbitrary subset `A` of an open set `W` with `μ(W) < ∞` (statement (β) of Step 8 in the proof of Simon Ch. 8, 1.2): the set of `x ∈ A` at which `μ(A ∩ B_r(x))/μ(B_r(x))` does not tend to `1` as `r ↓ 0` is `μ`-null. Apply `Besicovitch.ae_tendsto_measure_inter_div` to the finite measure `ν = μ ⌞ W`; a measurable hull `T` of its failure set has `μ(T ∩ A ∩ W) = (ν ⌞ A)(T) = 0`, and at `x ∈ A ∖ T` small balls lie in `W`, so the `μ`- and `ν`-ratios agree near `0⁺`. No measurability of `A` is used.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_weq_piece_restrict_eq_density`

##### `S.frt_weq_piece_restrict_eq_density`

- Node: `root.first_rectifiability-a1.weight_eq_theta_hausdorff-a1.piece_identity-a1`; accepted candidate `d814574b732b`
- Statement and proof: Steps 6–8 of the proof of Simon Ch. 8, 1.2, on one piece `A ⊆ W` (`W` open, `μ(W) < ∞`, `H^n(A) < ∞`): if `μ` has density `θ(x) > 0` at every `x ∈ A`, `μ` and `H^n` have the same null subsets of `A`, and `H^n ⌞ A` has density one `H^n ⌞ A`-a.e., then `μ ⌞ A = (H^n ⌞ A) ⌞ θ`, i.e. `μ(B ∩ A) = ∫_{B ∩ A} θ dH^n` for every Borel `B` (Besicovitch differentiation and Radon–Nikodym).
- Calls: `S.frt_weq_nondensity_points_null`
- Called by: `S.frt_weight_eq_multiplicity_hausdorff`

#### `S.frt_weighted_approx_tangent`

- Node: `root.first_rectifiability-a1.weighted_approx_tangent-a1`; accepted candidate `d578fe83ae6f`
- Statement and proof: Tangent planes of `V` are the approximate tangent planes of its carrier (Simon Ch. 8, proof of 1.2, with Ch. 3, Definition 1.7): if `μ_V(B) = ∫_{B ∩ M} θ dH^n` for Borel `B` and `V` has tangent plane `T` with multiplicity `θ(x)` at `x`, then `T` is the unique `n`-plane that is an approximate tangent space of `M` at `x` with respect to `θ`.
- Calls: `S.frt_wat_integral_eq_setIntegral_mul`, `S.frt_wat_setIntegral_blowUpMap_image`, `S.frt_weight_blowup_tendsto`
- Called by: `S.first_rectifiability_theorem`

##### `S.frt_wat_integral_eq_setIntegral_mul`

- Node: `root.first_rectifiability-a1.weighted_approx_tangent-a1.weight_integral_formula-a1`; accepted candidate `1e268c45646a`
- Statement and proof: Integration against a measure that is `θ H^n ⌞ M` on Borel sets (used in the proof of Simon Ch. 8, 1.2, where `μ_V = θ H^n ⌞ M`): if `μ B = ∫⁻_{B ∩ M} θ dH^n` for every Borel set `B`, `θ > 0` on `M`, `θ` is `H^n`-integrable on `M ∩ K` for a Borel set `K` and `h` vanishes off `K`, then `∫ h dμ = ∫_M h θ dH^n`. `h` is arbitrary: no measurability or integrability is assumed.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_weighted_approx_tangent`

##### `S.frt_wat_setIntegral_blowUpMap_image`

- Node: `root.first_rectifiability-a1.weighted_approx_tangent-a1.blowup_change_of_variables-a1`; accepted candidate `8e389acf8bfb`
- Statement and proof: Dilation change of variables for `H^n` set integrals over blow-up images (the homothety step behind Simon Ch. 8, 1.2 with Ch. 3, 1.7): for `r > 0`, `η = η_{x,r}` (`η y = r⁻¹ • (y - x)`), an arbitrary set `M` and an arbitrary `F : ℝ^N → ℝ`, `∫_{η(M)} F dH^n = r⁻¹ ^ n ∫_M F ∘ η dH^n`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_weighted_approx_tangent`

#### `S.frt_varifold_eq_tangent_graph_measure`

- Node: `root.first_rectifiability-a1.varifold_graph_measure-a1`; accepted candidate `b6b296511a09`
- Statement and proof: **A varifold with tangent planes `μ_V`-a.e. is the graph measure of its tangent planes** (Simon Ch. 8, proof of 1.2, p. 208, printed (1)–(2), with the corrected `η_V^(x)(β) = β(T_x)`). Let `η` satisfy the conclusions of Lemma 1.3, and let `V` have a tangent plane at `μ_V`-a.e. `x`. Then for every Borel `A ⊆ ℝ^N × G(N,n)` the set `S_A = {x : (x, T_x) ∈ A}` is `μ_V`-null-measurable and `V(A) = μ_V(S_A)`. At a tangent point the ball averages tend to `β(T_x)`, so `∫ β dη(x) = β(T_x)` for `μ_V`-a.e. `x`. With a Borel selection `τ` of `x ↦ T_x`, the second part of 1.3 becomes identity (1), hence `V = (μ_V)_#(x ↦ (x, τ x))`.
- Calls: `S.frt_vgm_eq_map_graph_of_lintegral`, `S.frt_vgm_measurable_plane_selection`, `S.frt_vgm_tangent_ball_average`
- Called by: `S.first_rectifiability_theorem`

##### `S.frt_vgm_tangent_ball_average`

- Node: `root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1`; accepted candidate `d929a234933e`
- Statement and proof: Averages over balls at a tangent plane (Simon Ch. 8, proof of 1.2, p. 208, with the erratum `η_V^{(x)}(β) = β(T_x)`): if `V` has tangent plane `T` with multiplicity `θ` at `x` (Def. 1.1), then `μ_V(B_ρ(x))⁻¹ ∫_{Gₙ(B_ρ(x))} β(S) dV(y,S) → β(T)` as `ρ ↓ 0` for every continuous `β` on `G(N,n)`. The multiplicity cancels because the averages are normalised by `μ_V(B_ρ(x))`.
- Calls: `S.frt_vgm_tba_nonneg_ball_limit`
- Called by: `S.frt_varifold_eq_tangent_graph_measure`

###### `S.frt_vgm_tba_plane_closedBall_hausdorff`

- Node: `root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1.plane_ball-a1`; accepted candidate `ec29b8ca3875`
- Statement and proof: The `n`-dimensional Hausdorff measure of the closed ball `B_r(0)` of an `n`-plane `T ∈ G(N,n)` is `ω_n r^n` (step 5, plane balls, of the tangent-ball average proof for Simon Ch. 8, 1.2): `H^n` is transported to Lebesgue measure on `ℝ^n` along an isometric parametrization of `T`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_vgm_tba_plane_cutoff_bounds`

###### `S.frt_vgm_tba_plane_cutoff_bounds`

- Node: `root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1.plane_cutoff_bounds-a1`; accepted candidate `104b957c16c6`
- Statement and proof: The plane integrals of the radial cut-offs `χ⁻ = χ_{1-κ,1}` and `χ⁺ = χ_{1,1+κ}`, where `χ_{a,b}(y) = max(0, min(1, (b - |y|)/(b - a)))`, over an `n`-plane `T ∈ G(N,n)` satisfy `ω_n (1-κ)^n ≤ ∫_T χ⁻ dH^n` and `∫_T χ⁺ dH^n ≤ ω_n (1+κ)^n` for `0 < κ < 1` (step 6 of the tangent-ball average in the proof of Simon Ch. 8, 1.2): `1_{B_{1-κ}(0)} ≤ χ⁻` and `χ⁺ ≤ 1_{B_{1+κ}(0)}`, while `H^n(T ∩ B_r(0)) = ω_n r^n` (`frt_vgm_tba_plane_closedBall_hausdorff`).
- Calls: `S.frt_vgm_tba_plane_closedBall_hausdorff`
- Called by: `S.frt_vgm_tba_nonneg_ball_limit`

###### `S.frt_vgm_tba_product_blowup_tendsto`

- Node: `root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1.product_blowup-a1`; accepted candidate `8d2c403b2201`
- Statement and proof: Simon Ch. 8, Definition 1.1 tested on a product function: if `V` has tangent plane `T` with multiplicity `θ` at `x`, then for `g ∈ C_c(ℝ^N)` and continuous `β` on `G(N,n)`, `t^{-n} ∫ g(t⁻¹(y - x)) β(S) dV(y,S) → θ β(T) ∫_T g dH^n` as `t ↓ 0` (the test function is `f(y,S) = g(y) β(S)`; used for the tangent-ball averages in the proof of 1.2).
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_vgm_tba_nonneg_ball_limit`

###### `S.frt_vgm_tba_ball_cutoff_sandwich`

- Node: `root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1.ball_cutoff_sandwich-a1`; accepted candidate `741b3b5cb45f`
- Statement and proof: The cut-off sandwich for a ball (steps 2 and 7 of the tangent-ball average used for Simon Ch. 8, 1.2): with `χ⁻ = max(0, min(1, (1 - |w|)/κ))`, `χ⁺ = max(0, min(1, (1 + κ - |w|)/κ))` and `w = t⁻¹(y - x)`, `∫ χ⁻ β dV ≤ ∫_{B_t(x) × G} β dV ≤ ∫ χ⁺ β dV` for `β ≥ 0`, since `χ⁻(w) β ≤ 1_{B_t(x) × G} β ≤ χ⁺(w) β` pointwise and all three integrands are bounded, measurable and vanish off `B_{2t}(x) × G`, which has finite `V`-measure.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_vgm_tba_nonneg_ball_limit`

###### `S.frt_vgm_tba_nonneg_ball_limit`

- Node: `root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1.nonneg_ball_limit-a1`; accepted candidate `a053bc3ab3e2`
- Statement and proof: Ball integrals at a tangent plane for `β ≥ 0` (the step "`ν_V^{(x)}(β) = θ(x) β(T_x)`" in the proof of Simon Ch. 8, 1.2, p. 207, for the ratios of 1.3): if `V` has tangent space `T` with multiplicity `θ` at `x` (1.1), then `t^{-n} ∫_{B_t(x) × G(N,n)} β(S) dV(y,S) → θ ω_n β(T)` as `t ↓ 0` for every continuous `β ≥ 0` on `G(N,n)`.
- Calls: `S.frt_vgm_tba_ball_cutoff_sandwich`, `S.frt_vgm_tba_plane_cutoff_bounds`, `S.frt_vgm_tba_product_blowup_tendsto`
- Called by: `S.frt_vgm_tangent_ball_average`

##### `S.frt_vgm_measurable_plane_selection`

- Node: `root.first_rectifiability-a1.varifold_graph_measure-a1.measurable_plane_selection-a1`; accepted candidate `5f86cb46f787`
- Statement and proof: A Borel selection of the plane determined by ball averages (the Borel version `T̃` of `x ↦ T_x` needed in the proof of Simon Ch. 8, 1.2, p. 208): there is a measurable `τ : ℝ^N → G(N,n)` with `τ x = T` whenever the averages of every continuous `β` over `Gₙ(B_ρ(x))` tend to `β T` as `ρ ↓ 0`. The averages of the matrix entries `S ↦ S_{ij}` along `ρ_k = 1/(k+1)` are measurable in `x`, and `τ` selects their entrywise limit.
- Calls: `S.frt_vgm_mps_ball_integral_measurable`, `S.frt_vgm_mps_limit_selection`, `S.frt_vgm_mps_weight_closedBall_measurable`
- Called by: `S.frt_varifold_eq_tangent_graph_measure`

###### `S.frt_vgm_mps_weight_closedBall_measurable`

- Node: `root.first_rectifiability-a1.varifold_graph_measure-a1.measurable_plane_selection-a1.weight_closed_ball_measurable-a1`; accepted candidate `91f07322d212`
- Statement and proof: The closed-ball mass `x ↦ μ(B_r(x))` of an s-finite measure `μ` on `ℝ^N` is Borel measurable for every radius `r` (used with `μ = μ_V` for the Borel choice of `x ↦ T_x` in Simon Ch. 8, proof of 1.2).
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_vgm_measurable_plane_selection`

###### `S.frt_vgm_mps_ball_integral_measurable`

- Node: `root.first_rectifiability-a1.varifold_graph_measure-a1.measurable_plane_selection-a1.ball_integral_measurable-a1`; accepted candidate `29ee15a20ce4`
- Statement and proof: The ball integral `x ↦ ∫_{B_r(x) × G(N,n)} β(S) dν(y,S)` is Borel measurable for every s-finite measure `ν` on `ℝ^N × G(N,n)`, every `r` and every continuous `β` (step 3 of the Borel choice of `x ↦ T_x` in the proof of Simon Ch. 8, 1.2): it equals `x ↦ ∫ 1_{E_r}(x, z) β(z.2) dν(z)` for the closed set `E_r = {(x, z) : |z.1 - x| ≤ r}`, which is measurable in `x` by `StronglyMeasurable.integral_prod_right'`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_vgm_measurable_plane_selection`

###### `S.frt_vgm_mps_limit_selection`

- Node: `root.first_rectifiability-a1.varifold_graph_measure-a1.measurable_plane_selection-a1.grassmannian_limit_selection-a1`; accepted candidate `e0acc5c21117`
- Statement and proof: Measurable selection of entrywise limits in `G(N,n)` (the Borel version of `x ↦ T_x` in Simon Ch. 8, proof of 1.2, p. 208): if every entry `x ↦ a_k(x)_{ij}` is measurable, there is a measurable `τ : X → G(N,n)` with `τ x = T` whenever `a_k(x)_{ij} → T_{ij}` as `k → ∞` for all `i, j`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_vgm_measurable_plane_selection`

##### `S.frt_vgm_eq_map_graph_of_lintegral`

- Node: `root.first_rectifiability-a1.varifold_graph_measure-a1.graph_measure_ext-a1`; accepted candidate `6c7c7c7c07cc`
- Statement and proof: Graph-measure extensionality (Simon Ch. 8, proof of 1.2, p. 208: "from the arbitrariness of `A` and `β`"): if `∫_{Gₙ(A)} β(S) dV(y,S) = ∫_A β(τ(x)) dμ_V(x)` for every Borel `A ⊆ ℝ^N` and every continuous `β ≥ 0` on `G(N,n)`, then `V = (μ_V)_#(x ↦ (x, τ(x)))`.
- Calls: `S.frt_vgm_ext_finite_of_lintegral_continuous`, `S.frt_vgm_ext_prod_of_finite_rectangles`
- Called by: `S.frt_varifold_eq_tangent_graph_measure`

###### `S.frt_vgm_ext_finite_of_lintegral_continuous`

- Node: `root.first_rectifiability-a1.varifold_graph_measure-a1.graph_measure_ext-a1.finite_measure_ext_continuous-a1`; accepted candidate `d579e2e31b9f`
- Statement and proof: A finite Borel measure on a pseudo-metrizable space is determined by the lower integrals of nonnegative continuous functions (the uniqueness step behind "from the arbitrariness of `A` and `β` it then easily follows" in the proof of Simon Ch. 8, 1.2, p. 208): each closed `F` is approximated by `max 0 (1 - (j + 1) d(·, F))`, and closed sets form a π-system generating the Borel σ-algebra.
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_vgm_eq_map_graph_of_lintegral`

###### `S.frt_vgm_ext_prod_of_finite_rectangles`

- Node: `root.first_rectifiability-a1.varifold_graph_measure-a1.graph_measure_ext-a1.prod_measure_ext_rectangles-a1`; accepted candidate `092cf1b60471`
- Statement and proof: Uniqueness of measures on `X × Y` from rectangles with `μ`-finite base (Step 5 of the proof that a varifold is determined by its graph measure): if `μ` is σ-finite, `ρ₁` is finite on the cylinders `A × Y` with `μ(A) < ∞`, and `ρ₁`, `ρ₂` agree on the rectangles `A × B` with `μ(A) < ∞`, then `ρ₁ = ρ₂` (Dynkin's π-λ theorem, `Measure.ext_of_generateFrom_of_iUnion`).
- Calls: — (no accepted declaration; library only)
- Called by: `S.frt_vgm_eq_map_graph_of_lintegral`

### `S.allard_rectifiability_and_tangent_cones`

- Node: `root.allard_tangent_cones-a1`; accepted candidate `746efc2d59f5`
- Statement and proof: **Simon Ch. 8, 5.5 with Remark 5.6, and 5.7, pp. 215–218** (child `allard_tangent_cones` of `main_theorem`): Allard's Rectifiability Theorem, and tangent cones are rectifiable cones. Part A (5.5, 5.6) is child `allard_rectifiability`, applied to 2.5–2.10 (`first_variation_theorems`), 3.4 and 3.6 (`monotonicity_and_density_theorems`), 4.1 (`constancy_theorem`), 5.1–5.4 with the blow-up density lower bound (`varifold_tangent_theorems`), Lemma 1.3 (`plane_disintegration`) and 1.2 (`first_rectifiability_theorem`). Part B (5.7) is child `tangent_cones_rectifiable`; as in the printed proof of 5.7, it applies 5.5, i.e. Part A, to each tangent cone.
- Calls: `S.allard_tc_rectifiability`, `S.allard_tc_tangent_cones_rectifiable`, `S.constancy_theorem`, `S.first_rectifiability_theorem`, `S.first_variation_theorems`, `S.monotonicity_and_density_theorems`, `S.plane_disintegration`, `S.varifold_tangent_theorems`
- Called by: `S.compactness_theorem`, `S.integral_compactness_theorem`, `main_theorem`

#### `S.allard_tc_flat_blowup_ball_limits`

- Node: `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1`; accepted candidate `501c8d724ac1`
- Statement and proof: Ball limits at a flat blow-up (the portmanteau step in the proof of Simon Ch. 8, 5.5: the limit stated right after display (9), p. 218): if `V_{x,t_i} → θ v(T)` as Radon measures along `l`, with `t_i → 0⁺`, then `t_i^{-n} ∫_{B_{t_i}(x) × G(N,n)} β(S) dV(y,S) → θ ω_n β(T)` for every continuous `β` on `G(N,n)`, and `t_i^{-n} μ_V(B_{t_i}(x)) → θ ω_n`.
- Calls: `S.allard_tc_fbl_nonneg_limit`
- Called by: `S.allard_tc_unique_tangent_plane`, `S.allard_tc_tangent_plane_density`

##### `S.allard_tc_fbl_plane_ball_measure`

- Node: `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1.plane_ball_measure-a1`; accepted candidate `3e6e8233280a`
- Statement and proof: The `n`-dimensional Hausdorff measure of the closed and open balls `B_r(0)` of an `n`-plane `T ∈ G(N,n)` is `ω_n r^n` (step 6 of the flat blow-up ball limits used for Simon Ch. 8, 5.5): `H^n` is transported to Lebesgue measure on `ℝ^n` along an isometric parametrization of `T`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_fbl_plane_cutoff_limits`

##### `S.allard_tc_fbl_plane_cutoff_limits`

- Node: `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1.plane_cutoff_limits-a1`; accepted candidate `a3a24dfb04a3`
- Statement and proof: The plane integrals of the unit-ball cut-offs `φ_k⁺ = max(0, 1 - (k+1) max(0, |y| - 1))` and `φ_k⁻ = min(1, (k+1) max(0, 1 - |y|))` over an `n`-plane `T ∈ G(N,n)` both converge to `ω_n` (steps 5–6 of the flat blow-up ball limits used for Simon Ch. 8, 5.5): dominated convergence with the bound `1_{B_2(0)}` and the pointwise limits `1_{B_1(0)}`, `1_{B°_1(0)}`, whose integrals are `ω_n` by `allard_tc_fbl_plane_ball_measure`.
- Calls: `S.allard_tc_fbl_plane_ball_measure`
- Called by: `S.allard_tc_fbl_nonneg_limit`

##### `S.allard_tc_fbl_rescaled_sandwich`

- Node: `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1.rescaled_sandwich-a1`; accepted candidate `7fafe1418e30`
- Statement and proof: Cut-off sandwich for the rescaled ball integral (flat blow-up ball limits for Simon Ch. 8, 5.5): if `r > 0`, `B_{2r}(x) ⊆ U`, `β ≥ 0` is continuous on `G(N,n)` and `a = k + 1`, then `∫ φ⁻ β dV_{x,r} ≤ r⁻ⁿ ∫_{B_r(x) × G(N,n)} β dV ≤ ∫ φ⁺ β dV_{x,r}`, where `φ⁻(y) = min(1, a max(0, 1 - |y|))` and `φ⁺(y) = max(0, 1 - a max(0, |y| - 1))`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_fbl_nonneg_limit`

##### `S.allard_tc_fbl_squeeze`

- Node: `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1.filter_squeeze-a1`; accepted candidate `848f284c6c96`
- Statement and proof: Squeeze along a filter by approximating families (the `ε`-argument closing the flat blow-up ball limits used for Simon Ch. 8, 5.5): if for each `k` eventually `a_k ≤ m ≤ b_k` along `l`, `a_k → A_k` and `b_k → B_k` along `l`, and `A_k → L`, `B_k → L` as `k → ∞`, then `m → L` along `l`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_fbl_nonneg_limit`

##### `S.allard_tc_fbl_nonneg_limit`

- Node: `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1.nonneg_limit-a1`; accepted candidate `ccb55661dda4`
- Statement and proof: Ball-integral limit at a flat blow-up for `β ≥ 0` (flat blow-up ball limits for Simon Ch. 8, 5.5): if `t_i → 0⁺` along `l` and `∫ f dV_{x,t_i} → θ ∫ f dv(T)` for every `f ∈ C_c(ℝ^N × G(N,n))`, then `t_i⁻ⁿ ∫_{B_{t_i}(x) × G(N,n)} β dV → θ ω_n β(T)` for every continuous `β ≥ 0` on `G(N,n)`.
- Calls: `S.allard_tc_fbl_plane_cutoff_limits`, `S.allard_tc_fbl_rescaled_sandwich`, `S.allard_tc_fbl_squeeze`
- Called by: `S.allard_tc_flat_blowup_ball_limits`

#### `S.allard_tc_stationary_cone_flat`

- Node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1`; accepted candidate `86b75144b9b1`
- Statement and proof: **Simon Ch. 8, proof of 5.5, pp. 216–217: a stationary cone with density `≥ θ₀` a.e. is `θ₀ v(T)`.** Let `C` be a stationary `n`-varifold on `ℝ^N` with `μ_C(B_ρ(0)) = θ₀ ω_n ρ^n` for every `ρ > 0` (printed (1)) and `Θ^n(μ_C, y) ≥ θ₀` for `μ_C`-a.e. `y` (printed (7)). By 3.4 at every centre, `R(y, ρ) = μ_C(B_ρ(y))/(ω_n ρ^n) ≤ θ₀` for all `y` (printed (2)) and `R(y, ρ) ≥ θ₀` for `y ∈ spt μ_C`, so `Θ^n(μ_C, y) = θ₀` and the normal defect about `y` vanishes; hence `x - y ∈ S` for `y ∈ spt μ_C` and `(x, S) ∈ spt C` (printed (8)). As `0 ∈ spt μ_C = π(spt C)`, some `(0, T)` lies in `spt C`, so `spt μ_C ⊆ T`; Constancy 4.1 gives `C = θ v(T)`, and the mass of `B_1(0)` gives `θ = θ₀`.
- Calls: `S.allard_tc_scf_constancy_plane`, `S.allard_tc_scf_monotonicity_identity`, `S.allard_tc_scf_plane_ball_mass`, `S.allard_tc_scf_ratio_ge_on_support`, `S.allard_tc_scf_ratio_le`, `S.allard_tc_scf_zero_defect_mem_plane`
- Called by: `S.allard_tc_rectifiability`

##### `S.allard_tc_scf_monotonicity_identity`

- Node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1.monotonicity_identity-a1`; accepted candidate `d1de406f3e87`
- Statement and proof: The monotonicity identity 3.4 at every centre of a stationary varifold `C` on `ℝ^N` (Simon Ch. 8, as used in the proof of 5.5): applying 3.4 with `U = ℝ^N` and `ρ₀ = k + 1` gives `θ_k` with `θ_k + ω_n^{-1} ∫_{Gₙ(B_ρ(y))} r^{-n-2}|p_{S^⊥}(x-y)|² dC = μ_C(B_ρ(y))/(ω_n ρ^n)` for `0 < ρ < k + 1`. Limits along `ρ ↓ 0` are unique, so `θ_k = θ_0` and the identity holds for every `ρ > 0`; the defect integral is monotone in the ball, so the density ratio is non-decreasing.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_stationary_cone_flat`

##### `S.allard_tc_scf_ratio_le`

- Node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1.ratio_upper_bound-a1`; accepted candidate `224cac46d817`
- Statement and proof: Density ratios are bounded by the ball-mass constant about `0` (Simon Ch. 8, the display before 5.5(2)): if `ρ ↦ μ(B_ρ(y))/(ω_n ρ^n)` is non-decreasing on `(0,∞)` for every `y` and `μ(B_ρ(0)) = a ω_n ρ^n` for every `ρ > 0`, then for `ρ' ≥ ρ`, using `B_{ρ'}(y) ⊆ B_{ρ'+|y|}(0)`, `μ(B_ρ(y))/(ω_n ρ^n) ≤ μ(B_{ρ'}(y))/(ω_n ρ'^n) ≤ a (1 + |y|/ρ')^n → a` as `ρ' → ∞`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_stationary_cone_flat`

##### `S.allard_tc_scf_ratio_ge_on_support`

- Node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1.ratio_lower_bound-a1`; accepted candidate `0fcd58060caf`
- Statement and proof: Density ratios at points of `spt μ` are bounded below by an a.e. lower bound of the density (the step "(and hence for every `y ∈ spt μ_C` by 3.4)" after Simon Ch. 8, 5.5(7)): if `μ` is finite on closed balls, `ρ ↦ R(x, ρ) = μ(B_ρ(x))/(ω_n ρ^n)` is non-decreasing on `(0, ∞)` for every `x` and `Θ^n(μ, x) ≥ a` for `μ`-a.e. `x`, then `a ≤ R(y, ρ)` for `y ∈ spt μ` and `ρ > 0`. Each open ball of radius `1/(k+1)` about `y` contains a point `y_k` with `a ≤ Θ^n(μ, y_k) ≤ R(y_k, ρ) ≤ μ(B_{ρ+1/(k+1)}(y))/(ω_n ρ^n)`, and continuity from above for the decreasing closed balls `B_{ρ+1/(k+1)}(y)` lets `k → ∞`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_stationary_cone_flat`

##### `S.allard_tc_scf_zero_defect_mem_plane`

- Node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1.zero_defect_plane-a1`; accepted candidate `bd9c4fe8fb73`
- Statement and proof: Vanishing normal defect about `y` gives `x - y ∈ S` at every `(x, S) ∈ spt V` (Simon Ch. 8, proof of 5.5, p. 217, display (8)): if `∫_{Gₙ(B_ρ(y))} |x - y|^{-n-2} |p_{S^⊥}(x - y)|² dV = 0` for every `ρ > 0`, then `p_{S^⊥}(x - y) = 0` for `V`-a.e. `(x, S)`, hence, by continuity of `p_{S^⊥}(x - y)` in `(x, S)`, at every point of `spt V`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_stationary_cone_flat`

##### `S.allard_tc_scf_subspace_submanifold`

- Node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1.subspace_submanifold-a1`; accepted candidate `50ea862ed9f2`
- Statement and proof: A linear subspace `P` of `ℝ^N` with `dim P = n` is an `n`-dimensional `C²` submanifold in Simon's sense (Ch. 2, §4), so the Constancy Theorem 4.1 applies with `M = P` (step 7(b) of the proof that a stationary cone with density `≥ θ₀` a.e. is `θ₀ v(T)`, used for Simon Ch. 8, 5.5): a linear isometry `J : ℝ^n → ℝ^N` with range `P` is a single global chart `(ℝ^n, ℝ^N, J)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_scf_constancy_plane`

##### `S.allard_tc_scf_subspace_classical_tangent`

- Node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1.subspace_tangent-a1`; accepted candidate `cecde683e3d5`
- Statement and proof: **Simon Ch. 8, proof of 5.5, p. 215, the plane's classical tangent space** (child `subspace_tangent` of `stationary_cone_flat`, step 7): for a linear subspace `P` of `ℝ^N` and `y ∈ P`, the classical tangent space `T_y P` (Ch. 2, §4) is `P` itself. A velocity `γ'(0)` is the limit of the difference quotients `t⁻¹(γ(t) - y) ∈ P` and `P` is closed (finite-dimensional); conversely `ξ ∈ P` is the velocity of the line `s ↦ y + sξ`, which stays in `P`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_scf_constancy_plane`

##### `S.allard_tc_scf_constancy_plane`

- Node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1.constancy_plane-a1`; accepted candidate `17d8646ef394`
- Statement and proof: **Simon Ch. 8, 4.1 for a plane** (child `constancy_plane` of `stationary_cone_flat`; the step "`C = θ₀ v(T)` by Constancy 4.1" in the proof of 5.5): a stationary `n`-varifold `C` on `ℝ^N` with `spt μ_C ⊆ T` is `θ v(T)` for a constant `θ ≥ 0`. `ConstancyTheorem` applies with `U = ℝ^N` and `M = T`: `T` is a `C²` submanifold (`allard_tc_scf_subspace_submanifold`) and `T ∩ ℝ^N = T` is convex, hence connected. Since `T_x T = T` (`allard_tc_scf_subspace_classical_tangent`) and a point of `G(N,n)` is determined by its plane, the constancy set of `A` is `{x ∈ T : (x, T) ∈ A}`, whose `H^n`-measure is `v(T)(A)`.
- Calls: `S.allard_tc_scf_subspace_classical_tangent`, `S.allard_tc_scf_subspace_submanifold`
- Called by: `S.allard_tc_stationary_cone_flat`

##### `S.allard_tc_scf_plane_ball_mass`

- Node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1.plane_ball_mass-a1`; accepted candidate `acb53d1981f8`
- Statement and proof: The plane varifold `v(T)` of an `n`-plane `T ∈ G(N,n)` has mass `ω_n r^n` over the cylinder `B_r(0) × G(N,n)` (step 8 of the proof that a stationary cone with density `≥ θ₀` a.e. is `θ₀ v(T)`, used for Simon Ch. 8, 5.5): `v(T)(B_r(0) × G(N,n)) = H^n(B_r(0) ∩ T)`, and `H^n` is transported to Lebesgue measure on `ℝ^n` along an isometric parametrization of `T`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_stationary_cone_flat`

#### `S.allard_tc_density_blowup_decay`

- Node: `root.allard_tangent_cones-a1.density_blowup_decay-a1`; accepted candidate `d8ca2a737a30`
- Statement and proof: Density blow-up decay (Simon Ch. 8, Remark 5.6(iii) and (3)–(4) in the proof of 5.5): assuming 3.6, if `V` has locally bounded first variation, then for `μ_V`-a.e. `x`, whenever `Θ^n(μ_V, x) = θ₀` and `τ < θ₀`, `ρ^{-n} μ_V({y ∈ B_ρ(x) : not (Θ^n(μ_V, y) exists and is ≥ τ)})` tends to `0` as `ρ ↓ 0`.
- Calls: `S.allard_tc_dbd_lebesgue_density`, `S.allard_tc_dbd_relative_decay`
- Called by: `S.allard_tc_rectifiability`

##### `S.allard_tc_dbd_lebesgue_density`

- Node: `root.allard_tangent_cones-a1.density_blowup_decay-a1.lebesgue_density_open-a1`; accepted candidate `d43946da1bdd`
- Statement and proof: Lebesgue density theorem for a measure `μ` on `ℝ^N` that vanishes off an open set `U` and is finite on compact subsets of `U` (Simon Ch. 8, Remark 5.6(iii), localized as in Simon Ch. 1, 3.23): for measurable `A` and `μ`-a.e. `x`, `μ(A ∩ B_ρ(x)) / μ(B_ρ(x)) → 1_A(x)` as `ρ ↓ 0`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_density_blowup_decay`

##### `S.allard_tc_dbd_relative_decay`

- Node: `root.allard_tangent_cones-a1.density_blowup_decay-a1.relative_density_decay-a1`; accepted candidate `20d343a546a0`
- Statement and proof: Relative density zero at a point of finite density gives `o(ρ^n)` mass (closing steps 8–9 of the density blow-up decay for Simon Ch. 8, 5.6(iii)): if `Θ^n(μ, x) = θ < ∞`, `μ(A ∩ B_ρ(x)) / μ(B_ρ(x)) → 0` as `ρ ↓ 0` and `μ`-a.e. point of `E` lies in `A`, then `μ(B_ρ(x) ∩ E) / ρ^n → 0` as `ρ ↓ 0`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_density_blowup_decay`

#### `S.allard_tc_unique_tangent_plane`

- Node: `root.allard_tangent_cones-a1.unique_tangent_plane-a1`; accepted candidate `d76859859b28`
- Statement and proof: **Simon Ch. 8, proof of 5.5 from (9) to the end** (child `unique_tangent_plane` of `allard_tangent_cones`): suppose every blow-up sequence at `x` has a vaguely convergent subsequence, every `C ∈ VarTan(V, x)` is `θ₀ v(T)` for some plane `T`, and the `β`-averages of `V` over `B_ρ(x)` tend to `∫ β dν` (printed (9)). Then `θ₀ v(T)` is the only varifold tangent and `V_{x,λ} → θ₀ v(T)` as `λ ↓ 0`. With (9), `allard_tc_flat_blowup_ball_limits` gives `β(T) = ∫ β dν` for every such `T`, and the matrix-entry functions separate the points of `G(N,n)`.
- Calls: `S.allard_tc_flat_blowup_ball_limits`
- Called by: `S.allard_tc_rectifiability`

#### `S.allard_tc_rectifiability`

- Node: `root.allard_tangent_cones-a1.allard_rectifiability-a1`; accepted candidate `e04fe202c219`
- Statement and proof: **Simon Ch. 8, 5.5 (Allard's Rectifiability Theorem) with Remark 5.6** (child `allard_rectifiability` of `allard_tangent_cones`). At `μ_V`-a.e. `x`: `θ₀ = Θ^n(μ_V, x)` exists in `(0, ∞)`, `D_{μ_V}‖δV‖(x) < ∞` (which gives 5.1), the `β`-averages of `V` over `B_ρ(x)` converge (Lemma 1.3), and the density decay of `allard_tc_density_blowup_decay` holds. At such `x` the blow-up density lower bound with `τ_k = θ₀ - θ₀/(k+2) ↑ θ₀` gives `Θ^n(μ_C, ·) ≥ θ₀` `μ_C`-a.e. (printed (7)) for each `C ∈ VarTan(V, x)`, so `C = θ₀ v(T)` (`allard_tc_stationary_cone_flat`) and `V` has a tangent plane at `x` (`allard_tc_unique_tangent_plane`). Rectifiability then follows from 1.2.
- Calls: `S.allard_tc_density_blowup_decay`, `S.allard_tc_stationary_cone_flat`, `S.allard_tc_unique_tangent_plane`
- Called by: `S.allard_rectifiability_and_tangent_cones`

#### `S.allard_tc_tangent_plane_density`

- Node: `root.allard_tangent_cones-a1.tangent_plane_density-a1`; accepted candidate `41e017ee87c4`
- Statement and proof: **At a tangent point the density equals the multiplicity** (child `tangent_plane_density` of `allard_tangent_cones`; Simon Ch. 8, 1.1 with Ch. 1, 3.1): if `V` has tangent plane `T` with multiplicity `θ` at `x`, then `Θ^n(μ_V, x) = θ`. Child `flat_blowup_ball_limits` along `t = id` on `𝓝[>] 0` gives `μ_V(B_ρ(x)) / ρ^n → θ ω_n`. For `B_ρ(x) ⊆ U` the ball mass is finite, so with `0 < ω_n < ∞` the density ratio is `ofReal (μ_V(B_ρ(x)) / ρ^n / ω_n)`; continuity of `ofReal` concludes.
- Calls: `S.allard_tc_flat_blowup_ball_limits`
- Called by: `S.allard_tc_tangent_plane_dilation`, `S.allard_tc_tangent_point_representation`

#### `S.allard_tc_tangent_plane_dilation`

- Node: `root.allard_tangent_cones-a1.tangent_plane_dilation-a1`; accepted candidate `9d1b76aa698c`
- Statement and proof: **Tangent planes of a homogeneous varifold are dilation invariant** (the step `Θ^n(μ_C, λy) = Θ^n(μ_C, y)` "by 5.3" in the proof of Simon Ch. 8, 5.7, with 5.3 in its corrected form `μ_C(sA) = s^n μ_C(A)`). If `C` has tangent plane `T` with multiplicity `θ` at `y` and `T'` with multiplicity `θ'` at `s y`, then `T' = T` and `θ' = θ`: the density ratio and the weight blow-ups of `C` at `s y` and scale `s t` are those at `y` and scale `t`. With `s = 1` this is the uniqueness of the tangent plane and multiplicity at a point.
- Calls: `S.allard_tc_tangent_plane_density`, `S.allard_tc_tpd_plane_eq_of_integral_eq`, `S.frt_weight_blowup_tendsto`
- Called by: `S.allard_tc_cone_rescaling_invariance`

- *(reused here: `S.frt_weight_blowup_tendsto`, node `root.first_rectifiability-a1.weight_blowup-a1` — see above)*
##### `S.allard_tc_tpd_plane_eq_of_integral_eq`

- Node: `root.allard_tangent_cones-a1.tangent_plane_dilation-a1.plane_eq_of_integral_eq-a1`; accepted candidate `e56989fe789d`
- Statement and proof: An `n`-plane `T ∈ G(N,n)` is determined by the `H^n`-integrals over it of compactly supported continuous functions (the plane half of the step `Θ^n(μ_C, λy) = Θ^n(μ_C, y)` in the proof of Simon Ch. 8, 5.7): equal integrals force `H^n ⌞ T' = H^n ⌞ T` (uniqueness in the Riesz representation for regular measures), so the supports `T'.plane` and `T.plane` agree, and a point of `G(N,n)` is the matrix of the orthogonal projection onto its plane.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_tangent_plane_dilation`

#### `S.allard_tc_tangent_point_representation`

- Node: `root.allard_tangent_cones-a1.tangent_point_representation-a1`; accepted candidate `9d3622790171`
- Statement and proof: **Canonical representation `C = v(M, θ)` by varifold tangent planes** (step B3 of the proof of Simon Ch. 8, 5.7). Take `M` and `θ` from the First Rectifiability Theorem 1.2. Since `μ_C` is `θ H^n ⌞ M`, at every `x ∈ M` the weighted approximate tangent planes of `(M, θ)` are exactly the varifold tangent planes of `C` with multiplicity `θ(x)`, so they may replace the approximate tangent planes in `IsVarifoldOf`.
- Calls: `S.allard_tc_tangent_plane_density`, `S.allard_tc_tpr_rectifiable_sigmaFinite`, `S.allard_tc_tpr_weight_eq_restrict`, `S.allard_tc_tpr_weighted_approx_tangent_iff`
- Called by: `S.allard_tc_tangent_cones_rectifiable`

##### `S.allard_tc_tpr_rectifiable_sigmaFinite`

- Node: `root.allard_tangent_cones-a1.tangent_point_representation-a1.rectifiable_sigma_finite-a1`; accepted candidate `a0e322cb2412`
- Statement and proof: A countably `n`-rectifiable set `M ⊆ ℝ^N` carries a σ-finite measure `H^n ⌞ M`: up to the `H^n`-null set `M₀`, `M` is covered by the compact Lipschitz images `F_j(B_k(0))`, each of finite `H^n`-measure.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_tangent_point_representation`

##### `S.allard_tc_tpr_hausdorff_null_of_weight_null`

- Node: `root.allard_tangent_cones-a1.tangent_point_representation-a1.hausdorff_null_of_weight_null-a1`; accepted candidate `c8f015ccaf09`
- Statement and proof: `μ`-null sets of positive density are `H^n`-null (Simon Ch. 1, Theorem 3.3, as used in Ch. 8): if `μ` is finite on compact sets, `μ(Z) = 0` and `Θ^n(μ, x) = θ(x) > 0` for every `x ∈ Z`, then `H^n(Z) = 0`. Proof by a Vitali covering of `Z_k = {x ∈ Z : θ(x) > 1/(k+1)}` with closed balls inside an open `O ⊇ Z_k` of small `μ`-measure.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_tpr_weight_eq_restrict`

##### `S.allard_tc_tpr_weight_eq_restrict`

- Node: `root.allard_tangent_cones-a1.tangent_point_representation-a1.weight_eq_restrict-a1`; accepted candidate `ec4de1e8e007`
- Statement and proof: **The weight is `θ H^n ⌞ M` once it is `θ H^n ⌞ E` for some `E ⊆ M`** (child `weight_eq_restrict` of `tangent_point_representation`; gives `μ_C = θ H^n ⌞ M` when writing `C = v(M, θ)` in the proof of Simon Ch. 8, 5.7). Let `B* = toMeasurable (H^n ⌞ M) E`. The hypothesis on `B*ᶜ` is an integral over `E ∩ B*ᶜ = ∅`, so `μ(M ∖ B*) = 0`, and child `hausdorff_null_of_weight_null` gives `H^n(M ∖ B*) = 0` because `θ > 0` is the density of `μ` on `M`. As `H^n ⌞ M` is s-finite, `(H^n ⌞ M)(B* ∩ D) = (H^n ⌞ M)(E ∩ D)` for measurable `D`; hence `H^n ⌞ (E ∩ B) = H^n ⌞ (M ∩ B)` for Borel `B`, and the two set integrals agree.
- Calls: `S.allard_tc_tpr_hausdorff_null_of_weight_null`
- Called by: `S.allard_tc_tangent_point_representation`

##### `S.allard_tc_tpr_integral_eq_weighted`

- Node: `root.allard_tangent_cones-a1.tangent_point_representation-a1.integral_eq_weighted-a1`; accepted candidate `18933c9d71b1`
- Statement and proof: Integration against the weight `μ = H^n ⌞ θ` of `v(M, θ)` (Simon Ch. 8, p. 206): if `μ(B) = ∫_{M ∩ B} θ dH^n` for every Borel `B`, then `∫ g dμ = ∫_M g θ dH^n` for every `g : ℝ^N → ℝ`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_tpr_weighted_approx_tangent_iff`

##### `S.allard_tc_tpr_blowup_setIntegral`

- Node: `root.allard_tangent_cones-a1.tangent_point_representation-a1.blowup_set_integral-a1`; accepted candidate `eb880df6af46`
- Statement and proof: Change of variables under a blow-up (Simon Ch. 8, 5.1/5.5): for `r > 0` and `η_{x,r}(z) = r⁻¹(z - x)`, `∫_{η_{x,r}(M)} φ dH^n = r^{-n} ∫_M φ ∘ η_{x,r} dH^n` for every set `M` and every function `φ`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_tpr_weighted_approx_tangent_iff`

##### `S.allard_tc_tpr_weighted_approx_tangent_iff`

- Node: `root.allard_tangent_cones-a1.tangent_point_representation-a1.weighted_approx_tangent-a1`; accepted candidate `39c7ab7a96d6`
- Statement and proof: Varifold tangent planes versus approximate tangent planes (Simon Ch. 8, Definition 1.1 against Ch. 3, 1.7): if `μ_V = H^n ⌞ θ` on `M` and `V` has tangent plane `T` with multiplicity `θ(x)` at `x`, then `T` is the unique approximate tangent space of `M` at `x` with respect to `θ`.
- Calls: `S.allard_tc_tpr_blowup_setIntegral`, `S.allard_tc_tpr_integral_eq_weighted`
- Called by: `S.allard_tc_tangent_point_representation`

#### `S.allard_tc_cone_rescaling_invariance`

- Node: `root.allard_tangent_cones-a1.cone_rescaling_invariance-a1`; accepted candidate `a236bd3b9834`
- Statement and proof: **Rectifiable tangent cones are invariant under dilations** (child `cone_rescaling_invariance` of `allard_tangent_cones`; Simon Ch. 8, 5.7, last sentence of the proof). If `C = v(M, θ)` has tangent plane `T_x` with multiplicity `θ(x)` at every `x ∈ M`, is represented by these planes and `μ_C(s A) = s^n μ_C(A)`, then `η_{0,s #} C = C` for `s > 0`: on `G = {w ∈ M : s w ∈ M}` the sibling `tangent_plane_dilation` gives `θ(s w) = θ(w)` and the same planes, child `carrier_dilation_null` makes `G` of full `H^n`-measure in both representing sets, and children `rescaled_representation` and `setLIntegral_congr_off_null` compare the two integrals.
- Calls: `S.allard_tc_cri_carrier_dilation_null`, `S.allard_tc_cri_rescaled_representation`, `S.allard_tc_cri_setLIntegral_congr_off_null`, `S.allard_tc_tangent_plane_dilation`
- Called by: `S.allard_tc_tangent_cones_rectifiable`

##### `S.allard_tc_cri_hausdorff_dilation_lintegral`

- Node: `root.allard_tangent_cones-a1.cone_rescaling_invariance-a1.hausdorff_dilation_lintegral-a1`; accepted candidate `246213c2e763`
- Statement and proof: Change of variables for `H^n` under a dilation (used for the rescaling invariance of tangent cones, Simon Ch. 8, 5.3 and 5.7): for `s > 0`, an arbitrary set `D` and an arbitrary `f : ℝ^N → [0,∞]`, `∫_D f dH^n = s^n ∫_{s⁻¹ D} f(s w) dH^n(w)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_cri_rescaled_representation`

##### `S.allard_tc_cri_rescaled_representation`

- Node: `root.allard_tangent_cones-a1.cone_rescaling_invariance-a1.rescaled_representation-a1`; accepted candidate `b62cfd99812b`
- Statement and proof: **Dilation of a varifold given by a fibrewise `H^n`-representation** (child `rescaled_representation` of `cone_rescaling_invariance`; Simon Ch. 8, 5.3 and 5.7). If `C(A) = ∫_{x ∈ M, ∃ T, P x T ∧ (x, T) ∈ A} g dH^n` for Borel `A`, then for `s > 0` `η_{0,s #} C (A) = ∫_{s w ∈ M, ∃ T, P (s w) T ∧ (w, T) ∈ A} g (s w) dH^n(w)`: pull `A` back by `Φ(z, S) = (s⁻¹ (z - 0), S)`, apply the representation, change variables `x = s w` with child `hausdorff_dilation_lintegral`, and cancel `s^{-n} s^n = 1`.
- Calls: `S.allard_tc_cri_hausdorff_dilation_lintegral`
- Called by: `S.allard_tc_cone_rescaling_invariance`

##### `S.allard_tc_cri_carrier_dilation_null`

- Node: `root.allard_tangent_cones-a1.cone_rescaling_invariance-a1.carrier_dilation_null-a1`; accepted candidate `4c1aed2b5f50`
- Statement and proof: The carrier of a dilation-homogeneous measure `θ H^n ⌞ M` is dilation-invariant up to `H^n`-null sets (used for the rescaling invariance of tangent cones, Simon Ch. 8, 5.3 and 5.7): if `M` is `H^n`-measurable, `θ > 0` on `M` is locally `H^n`-integrable, `μ(B) = ∫_{M ∩ B} θ dH^n` for Borel `B` and `μ(s A) = s^n μ(A)` for `s > 0`, then for every `s > 0` the sets `{w ∈ M : s w ∉ M}` and `{w ∉ M : s w ∈ M}` are `H^n`-null.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_cone_rescaling_invariance`

##### `S.allard_tc_cri_setLIntegral_congr_off_null`

- Node: `root.allard_tangent_cones-a1.cone_rescaling_invariance-a1.set_lintegral_congr_off_null-a1`; accepted candidate `0a18f902c494`
- Statement and proof: Set-lintegrals agree when the sets and the integrands agree on a null-measurable set `G` off which both sets are null (used for the rescaling invariance of tangent cones, Simon Ch. 8, 5.3 and 5.7): if `μ (D \ G) = μ (D' \ G) = 0`, `x ∈ D ↔ x ∈ D'` and `f x = g x` for `x ∈ G`, then `∫⁻_D f dμ = ∫⁻_{D'} g dμ`. `D`, `D'`, `f`, `g` are arbitrary and `μ` need not be σ-finite.
- Calls: — (no accepted declaration; library only)
- Called by: `S.allard_tc_cone_rescaling_invariance`

#### `S.allard_tc_tangent_cones_rectifiable`

- Node: `root.allard_tangent_cones-a1.tangent_cones_rectifiable-a1`; accepted candidate `aa920ec64bc2`
- Statement and proof: **Tangent cones are rectifiable cones** (child `tangent_cones_rectifiable` of `allard_tangent_cones`; Simon Ch. 8, Corollary 5.7 and its proof, p. 216): from 5.1–5.4, the blow-up density lower bound, Allard's 5.5/5.6 and the First Rectifiability Theorem 1.2. The lower bound with `τ = 1` gives `Θ^n(μ_C, ·) ≥ 1` `μ_C`-a.e.; `C` is stationary (5.2), so 5.5 makes it rectifiable with tangent planes `μ_C`-a.e.; the siblings `tangent_point_representation` and `cone_rescaling_invariance` with the homogeneity 5.3 then give `η_{0,s #} C = C` for `s > 0`.
- Calls: `S.allard_tc_cone_rescaling_invariance`, `S.allard_tc_tangent_point_representation`
- Called by: `S.allard_rectifiability_and_tangent_cones`

### `S.compactness_theorem`

- Node: `root.compactness-a1`; accepted candidate `4dc8f412869d`
- Statement and proof: **Simon Ch. 8, 5.8 (Compactness Theorem)**, "a direct consequence of" Ch. 1, 4.16, 3.7 and 5.5. Uniform mass bounds on compact sets let the Radon compactness theorem (Ch. 1, 4.16, corrected) extract `V_{φ(j)} → V`; zero extension of test functions on `Gₙ(U)` makes this convergence as Radon measures on `Gₙ(U)`; semicontinuity 3.7 along the subsequence gives locally bounded first variation, `‖δV‖(W) ≤ liminf_{j} ‖δV_{φ(j)}‖(W)` and `Θ^n(μ_V, ·) ≥ 1` `μ_V`-a.e.; and Allard's theorem 5.5 makes `V` rectifiable. The rectifiability of the `V_j` is not needed.
- Calls: `S.allard_rectifiability_and_tangent_cones`, `S.density_semicontinuity_theorem`, `S.varifold_radon_compactness`
- Called by: `S.integral_compactness_theorem`, `main_theorem`

### `S.integral_compactness_theorem`

- Node: `root.integral_compactness-a1`; accepted candidate `2cde3ae11f2d`
- Statement and proof: **Simon Ch. 8, 5.9 (Allard's Integral Compactness Theorem)** (child `integral_compactness` of `main_theorem`): integral varifolds have `Θ^n ≥ 1` almost everywhere, so 5.8 applies with null exceptional sets and gives the convergent subsequence. Every subsequential limit `V` is integral: by 3.7, 5.5 and 1.2, `V = v(M, θ)` with a tangent plane of multiplicity `θ(ξ)` at each `ξ ∈ M`, and at `μ_V`-a.e. `ξ ∈ M` the diagonal blow-ups of the `V_i` at `ξ` are integral with vanishing first variation and converge to `θ(ξ) v(T_ξ)`, which forces `θ(ξ) ∈ ℕ` (5.10, 5.11).
- Calls: `S.allard_rectifiability_and_tangent_cones`, `S.compactness_theorem`, `S.density_semicontinuity_theorem`, `S.first_rectifiability_theorem`, `S.intcpt_canonical_tangent_representation`, `S.intcpt_diagonal_integral_blowup`, `S.intcpt_flat_limit_integer_multiplicity`, `S.intcpt_integral_density_integer`, `S.intcpt_variation_liminf_density_bound`, `S.monotonicity_and_density_theorems`, `S.tangent_points_lipschitz_graph_cover`
- Called by: `main_theorem`

#### `S.intcpt_integral_density_integer`

- Node: `root.integral_compactness-a1.integral_density-a1`; accepted candidate `b7a0640a8e72`
- Statement and proof: **Simon Ch. 8, Remark 5.9** (step B0 of 5.9, for one varifold): an integral varifold has integer density `Θ^n(μ_V, x) ≥ 1` at `μ_V`-a.e. `x`. Write `V = v(M, θ)`, `ν = θ H^n ⌞ M` and `μ_V = ν ⌞ T` for a Borel hull `T` of the tangent-point set `M_*` (`intcpt_id_weight_hull`). At `x ∈ M_*`, `Θ^n(ν, x) = θ(x)` (Ch. 3, Remark 1.8(2): `intcpt_id_tangent_point_density`), and off an `H^n`-null set `Θ^n(ν ⌞ Tᶜ, x) = 0` (Ch. 1, 3.6: `intcpt_id_restrict_density_zero_ae`) and `θ(x) ∈ ℕ`; hence `Θ^n(μ_V, x) = θ(x) ∈ {1, 2, …}` for `H^n`-a.e. `x ∈ M_*`. The set where the conclusion fails is Borel (`intcpt_id_measurable_densities`), so its `μ_V`-measure is the integral of `θ` over an `H^n`-null subset of `M_*`, i.e. `0`.
- Calls: `S.intcpt_id_measurable_densities`, `S.intcpt_id_restrict_density_zero_ae`, `S.intcpt_id_tangent_point_density`, `S.intcpt_id_weight_hull`
- Called by: `S.intcpt_flat_limit_integer_multiplicity`, `S.integral_compactness_theorem`

##### `S.intcpt_id_restrict_sigmaFinite`

- Node: `root.integral_compactness-a1.integral_density-a1.restrict_sigma_finite-a1`; accepted candidate `33a8dd0847be`
- Statement and proof: σ-finiteness of `μ ⌞ M` for a positive, locally integrable multiplicity (Simon Ch. 8, p. 206; used for 5.9 with `μ = H^n`): if `U` is open, `M ⊆ U`, `θ > 0` on `M` and `θ` is `μ`-integrable on `M ∩ K` for every compact `K ⊆ U`, then `μ ⌞ M` is σ-finite. `M` need not be measurable.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_id_weight_hull`

##### `S.intcpt_id_weight_hull`

- Node: `root.integral_compactness-a1.integral_density-a1.weight_hull-a1`; accepted candidate `5fc31e9506d9`
- Statement and proof: The weight of `V = v(M, θ)` (Simon Ch. 8, p. 206: `V(A) = μ(π(TM ∩ A))` with `μ = H^n ⌞ θ`) is `θ H^n ⌞ M` restricted to a Borel hull `T` of the tangent-point set `M_* = {x ∈ M : M has an approximate tangent space at x with respect to θ}` (Ch. 3, 1.7): `μ_V = ((H^n ⌞ M) ⌞ θ) ⌞ T` with `M_* ⊆ T`, and `μ_V(B) = ∫_{M_* ∩ B} θ dH^n` for Borel `B`.
- Calls: `S.intcpt_id_restrict_sigmaFinite`
- Called by: `S.intcpt_integral_density_integer`

##### `S.intcpt_id_tangent_point_density`

- Node: `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1`; accepted candidate `ef0c46bc2e17`
- Statement and proof: Density at a weighted approximate tangent point (Simon Ch. 3, Remark 1.8(2)): if `M` is `H^n`-measurable, `θ ≥ 0` on `M` is `H^n`-integrable on `M ∩ B_{r₀}(x)`, `x ∈ M`, and `M` has weighted approximate tangent space `P` at `x` with respect to `θ` (Ch. 3, 1.7), then `ν = (H^n ⌞ M).withDensity θ` has `Θ^n(ν, x) = θ(x)`, i.e. `ν(B_ρ(x))/(ω_n ρ^n) → θ(x)` as `ρ ↓ 0`.
- Calls: `S.intcpt_id_tpd_ball_mass_lower`, `S.intcpt_id_tpd_ball_mass_upper`, `S.intcpt_id_tpd_hasDensity_of_ball_mass_bounds`
- Called by: `S.intcpt_integral_density_integer`

###### `S.intcpt_id_tpd_setIntegral_blowUpMap_image`

- Node: `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1.blowup_cov-a1`; accepted candidate `7802807dae88`
- Statement and proof: Change of variables for `H^n` set integrals under the blow-up map (step 1 of the tangent-point density argument, Simon Ch. 3, Remark 1.8(2)): for `r > 0`, `η = η_{x,r}` (`η y = r⁻¹ • (y - x)`), an arbitrary set `M` and an arbitrary `F : ℝ^N → ℝ`, `∫_{η(M)} F dH^n = r⁻¹ ^ n ∫_M F ∘ η dH^n`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_id_tpd_ball_sandwich`

###### `S.intcpt_id_tpd_plane_closedBall_hausdorff`

- Node: `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1.plane_ball-a1`; accepted candidate `d97efa972066`
- Statement and proof: The `n`-dimensional Hausdorff measure of the closed ball `B_r(0)` of an `n`-dimensional subspace `P ⊆ ℝ^N` is `ω_n r^n` (Simon Ch. 3, Remark 1.8(2); the plane-ball step of the tangent-point density argument for Simon Ch. 8, 5.9): `P ∩ B_r(0)` is the image of the closed `r`-ball of `P` under the isometric inclusion, `H^n = vol` on `P`, and an orthonormal coordinate map `P ≃ ℝ^n` carries the volume of the open unit ball of `P` to `ω_n`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_id_tpd_plane_cutoff`

###### `S.intcpt_id_tpd_hasDensity_of_ball_mass_bounds`

- Node: `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1.density_squeeze-a1`; accepted candidate `ae67142cf367`
- Statement and proof: Density squeeze (Simon Ch. 3, Remark 1.8(2), final step): if, as `t ↓ 0`, eventually `c t^n ≤ μ(B_t(x))` for each `c < a ω_n` and eventually `μ(B_t(x)) ≤ c t^n` for each `c > a ω_n`, then `Θ^n(μ, x)` exists and equals `a`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_id_tangent_point_density`

###### `S.intcpt_id_tpd_ball_sandwich`

- Node: `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1.ball_sandwich-a1`; accepted candidate `e02be06c645f`
- Statement and proof: Cut-off sandwich for one blow-up integral (tangent point density, Simon Ch. 3, Remark 1.8(2)): let `θ ≥ 0` on `M` be `H^n`-integrable on `M ∩ B_{r₀}(x)`, `ν = (H^n ⌞ M) ⌞ θ`, `η = η_{x,r}` (`η z = r⁻¹ • (z - x)`) with `r > 0`, and `f ∈ C_c(ℝ^N)` with `0 ≤ f ≤ 1`, `f = 1` on `B_a(0)` and `f = 0` off `B_R(0)`, where `rR ≤ r₀`. Then `ν(B_{ra}(x)) ≤ r^n ∫_{η(M)} f(y) θ(x + r y) dH^n(y) ≤ ν(B_{rR}(x))`.
- Calls: `S.intcpt_id_tpd_setIntegral_blowUpMap_image`
- Called by: `S.intcpt_id_tpd_ball_mass_lower`, `S.intcpt_id_tpd_ball_mass_upper`

###### `S.intcpt_id_tpd_plane_cutoff`

- Node: `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1.plane_cutoff-a1`; accepted candidate `df6794cbcbe4`
- Statement and proof: Plane cutoffs (steps 2 and 4 of the tangent-point density argument, Simon Ch. 3, Remark 1.8(2)): for an `n`-dimensional subspace `P` of `ℝ^N` and `0 < a < R`, the radial cutoff `f y = min 1 (max 0 ((R - ‖y‖) / (R - a)))` is in `C_c(ℝ^N, ℝ)`, takes values in `[0, 1]`, equals `1` on `B_a(0)` and `0` off `B_R(0)`, and `ω_n a^n ≤ ∫_P f dH^n ≤ ω_n R^n`.
- Calls: `S.intcpt_id_tpd_plane_closedBall_hausdorff`
- Called by: `S.intcpt_id_tpd_ball_mass_lower`, `S.intcpt_id_tpd_ball_mass_upper`

###### `S.intcpt_id_tpd_ball_mass_lower`

- Node: `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1.ball_mass_lower-a1`; accepted candidate `4995093c8c36`
- Statement and proof: Lower ball-mass bound at a weighted approximate tangent point (the lower half of Simon Ch. 3, Remark 1.8(2)): if `M` has weighted approximate tangent space `P` at `x` with respect to `θ ≥ 0` (Ch. 3, 1.7) and `θ` is `H^n`-integrable on `M ∩ B_{r₀}(x)`, then for every `c < θ(x) ω_n`, `c t^n ≤ ν(B_t(x))` for all small `t > 0`, where `ν = (H^n ⌞ M).withDensity θ`.
- Calls: `S.intcpt_id_tpd_ball_sandwich`, `S.intcpt_id_tpd_plane_cutoff`
- Called by: `S.intcpt_id_tangent_point_density`

###### `S.intcpt_id_tpd_ball_mass_upper`

- Node: `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1.ball_mass_upper-a1`; accepted candidate `dcb730858980`
- Statement and proof: Upper ball-mass bound at a weighted approximate tangent point (tangent point density, Simon Ch. 3, Remark 1.8(2)): let `M` have weighted approximate tangent space `P` at `x ∈ M` with respect to `θ ≥ 0` on `M`, with `θ` `H^n`-integrable on `M ∩ B_{r₀}(x)`, and let `ν = (H^n ⌞ M) ⌞ θ`. Then every `c > θ(x) ω_n` satisfies `ν(B_t(x)) ≤ c t^n` for all sufficiently small `t > 0`.
- Calls: `S.intcpt_id_tpd_ball_sandwich`, `S.intcpt_id_tpd_plane_cutoff`
- Called by: `S.intcpt_id_tangent_point_density`

##### `S.intcpt_id_restrict_density_zero_ae`

- Node: `root.integral_compactness-a1.integral_density-a1.zero_density_off_set-a1`; accepted candidate `6822a90fa726`
- Statement and proof: **Simon Ch. 1, 3.6 (Upper Density Theorem), localized as in Remark 3.7(2)** (child `zero_density_off_set` of `integral_density`, parent step 5): if `μ` is finite on compact subsets of the open set `U` and `A` is Borel, then `Θ^n(μ⌞A, x) = 0` for `H^n`-a.e. `x ∈ U ∖ A`. Simon's proof of 3.6 is carried out inline: the comparison estimate of 3.3 comes from a covering lemma (3.4; here Mathlib's Vitali lemma with enlargement `4`, which only changes the constant), closed sets `C_j ⊆ A` with `μ(A ∖ C_j) → 0` (1.15(2)) make the bad set `H^n`-null, and `U` is covered by countably many balls `B_q(c)` with `B_{2q}(c) ⊆ U`, on which `μ` is finite (3.7(2)).
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_integral_density_integer`

##### `S.intcpt_id_measurable_densities`

- Node: `root.integral_compactness-a1.integral_density-a1.measurable_densities-a1`; accepted candidate `15740b60a5fc`
- Statement and proof: Borel measurability of the upper and lower `n`-densities of an s-finite measure and of each level set `{x | Θ^n(μ, x) = c}` (Simon Ch. 1, 3.2; used in Ch. 8 for `μ = μ_V`, which need not be locally finite near `∂U`).
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_integral_density_integer`

#### `S.intcpt_canonical_tangent_representation`

- Node: `root.integral_compactness-a1.canonical_representation-a1`; accepted candidate `28055239da60`
- Statement and proof: **Canonical representation** (step B2 of the proof of Simon Ch. 8, 5.9; child `canonical_representation` of `integral_compactness`): let `V` have locally bounded first variation and `Θ^n(μ_V, x) > 0` for `μ_V`-a.e. `x`, and let `M = {x ∈ spt μ_V : V has a tangent plane at x}`. Allard's theorem (5.5 with 5.6) gives tangent planes `μ_V`-a.e., so the First Rectifiability Theorem (1.2) gives `θ` with `V = v(M, θ)` and a tangent plane of multiplicity `θ(x)` at each `x ∈ M`. Such a tangent plane forces `Θ^n(μ_V, x) = θ(x)` (`intcpt_canon_tangent_plane_hasDensity`), and as `θ > 0` on `M ⊆ U`, every `μ_V`-null `Z ⊆ M` is `H^n`-null (`intcpt_canon_hausdorff_null_of_weight_null`, via Simon Ch. 1, 3.3).
- Calls: `S.intcpt_canon_hausdorff_null_of_weight_null`, `S.intcpt_canon_tangent_plane_hasDensity`
- Called by: `S.intcpt_flat_limit_integer_multiplicity`, `S.integral_compactness_theorem`

##### `S.intcpt_canon_weight_blowup_tendsto`

- Node: `root.integral_compactness-a1.canonical_representation-a1.weight_blowup-a1`; accepted candidate `5ac08fc73006`
- Statement and proof: Weight blow-ups at a tangent point (Simon Ch. 8, Definition 1.1 tested with `f(z,S) = g(z)`): if `V` has tangent plane `T` with multiplicity `θ` at `x`, then for every `g ∈ C_c(ℝ^N)`, `t^{-n} ∫ g(t^{-1}(z - x)) dμ_V(z) → θ ∫_T g dH^n` as `t ↓ 0`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_canon_tangent_plane_hasDensity`

##### `S.intcpt_canon_plane_closedBall_hausdorff`

- Node: `root.integral_compactness-a1.canonical_representation-a1.plane_ball_measure-a1`; accepted candidate `1e2872f3b7d3`
- Statement and proof: `H^n` of a closed disc in an `n`-plane (step 3 of the canonical-representation proof for Simon Ch. 8, 5.9): for `T ∈ G(N,n)` and `r ≥ 0`, `H^n(T ∩ B_r(0)) = ω_n r^n`, because `T.plane` is an `n`-dimensional inner product space, isometrically included in `ℝ^N`, on which `μHE[n]` is Lebesgue measure.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_canon_tangent_plane_hasDensity`

##### `S.intcpt_canon_tangent_plane_hasDensity`

- Node: `root.integral_compactness-a1.canonical_representation-a1.tangent_density-a1`; accepted candidate `3940e9af8997`
- Statement and proof: Tangent planes force densities (step 3 of the canonical-representation proof for Simon Ch. 8, 5.9): if `V` has tangent plane `T` with multiplicity `θ` at `x` (Definition 1.1), then `Θ^n(μ_V, x) = θ`, i.e. `μ_V(B_ρ(x)) / (ω_n ρ^n) → θ` as `ρ ↓ 0`. Radial cut-offs in `C_c` squeeze `1_{B_ρ(x)}`, the weight blow-up gives their limits, and `H^n` of discs in `T` bounds them.
- Calls: `S.intcpt_canon_plane_closedBall_hausdorff`, `S.intcpt_canon_weight_blowup_tendsto`
- Called by: `S.intcpt_canonical_tangent_representation`

##### `S.intcpt_canon_hausdorff_null_of_weight_null`

- Node: `root.integral_compactness-a1.canonical_representation-a1.null_transfer-a1`; accepted candidate `3c13fe78ee34`
- Statement and proof: Step 4 of the canonical representation in the proof of Simon Ch. 8, 5.9 (child `null_transfer` of `canonical_representation`), via Simon Ch. 1, 3.3: let `U` be open and `μ` finite on compact subsets of `U`. If `Z ⊆ U` is `μ`-null and `limsup_{ρ↓0} μ(B_ρ(x)) / (ω_n ρ^n) > 0` at every `x ∈ Z`, then `H^n(Z) = 0`. Cover `U` by open `W_i ⊆ U` of finite mass (`intcpt_canon_nt_open_cover_finite_measure`) and put `Z_{i,k} = {x ∈ Z ∩ W_i : limsup ≥ 1/(k+1)}`. For `ε > 0` there is an open `O` with `Z_{i,k} ⊆ O ⊆ W_i` and `μ(O) < ε` (`intcpt_canon_nt_exists_open_subset_measure_lt`); on `Z_{i,k}` the upper density of `μ` relative to `O` is that `limsup`, so Simon 3.3 gives `(k+1)⁻¹ H^n(Z_{i,k}) ≤ μ(O) < ε`. Hence each `Z_{i,k}`, and so `Z`, is `H^n`-null.
- Calls: `S.intcpt_canon_nt_exists_open_subset_measure_lt`, `S.intcpt_canon_nt_open_cover_finite_measure`
- Called by: `S.intcpt_canonical_tangent_representation`

###### `S.intcpt_canon_nt_open_cover_finite_measure`

- Node: `root.integral_compactness-a1.canonical_representation-a1.null_transfer-a1.open_cover_finite_measure-a1`; accepted candidate `5b7b06874256`
- Statement and proof: **Countable cover of an open set by open subsets of finite mass** (child `open_cover_finite_measure` of `null_transfer`; step 2 of the supplied proof of `intcpt_canon_hausdorff_null_of_weight_null`): if `μ` is finite on the compact subsets of an open set `U ⊆ ℝ^N`, then `U` is covered by countably many open sets `W i ⊆ U` with `μ (W i) < ∞`. Every `y ∈ U` has a ball `B_y = ball y r_y` with `closedBall y r_y ⊆ U`; that closed ball is compact (`ℝ^N` is proper), so `μ B_y < ∞`. Lindelöf (`ℝ^N` is second countable) extracts a countable subfamily `(B_y)_{y ∈ T}` with the same union, enumerated by a surjection `ℕ → Option T` (`none ↦ ∅`).
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_canon_hausdorff_null_of_weight_null`

###### `S.intcpt_canon_nt_exists_open_subset_measure_lt`

- Node: `root.integral_compactness-a1.canonical_representation-a1.null_transfer-a1.open_subset_measure_lt-a1`; accepted candidate `ac0e4c049907`
- Statement and proof: **Open neighbourhood of small measure inside an open set of finite measure** (child `open_subset_measure_lt` of `null_transfer`; step 4 of the supplied proof of `intcpt_canon_hausdorff_null_of_weight_null`): if `W ⊆ ℝ^N` is open with `μ W < ∞` and `A ⊆ W` is an arbitrary set with `μ A < ε` (outer measure), then some open `O` with `A ⊆ O ⊆ W` has `μ O < ε`. The restriction `μ ⌞ W` is a finite Borel measure on a metric space, hence outer regular (`WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure`); since `(μ ⌞ W) A ≤ μ A < ε`, there is an open `O' ⊇ A` with `(μ ⌞ W) O' < ε`, and `O = O' ∩ W` has `μ O = (μ ⌞ W) O'`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_canon_hausdorff_null_of_weight_null`

#### `S.intcpt_variation_liminf_density_bound`

- Node: `root.integral_compactness-a1.variation_density_bound-a1`; accepted candidate `064c78314ef6`
- Statement and proof: **Simon Ch. 8, proof of 5.9, printed estimates (1)–(2)** (child `variation_density_bound` of `integral_compactness`): if `μ(ℝ^N ∖ U) = 0`, `sup_i ν_i(W) < ∞` for every open `W ⊂⊂ U` and `Θ^n(μ, x)` exists and is finite for `μ`-a.e. `x`, then for `μ`-a.e. `x` there are `c` and `r > 0` with `liminf_i ν_i(B_ρ(x)) ≤ c ρ^n` for `0 < ρ < r`. Cover `U` by countably many `W_p` whose `r_p`-thickenings are `⊂⊂ U` (child `open_thickening_exhaustion`). At `μ`-a.e. `x ∈ W_p`, Besicovitch gives `liminf_i ν_i(B_ρ(x)) ≤ c μ(B_ρ(x))` for `ρ < r_p` (child `liminf_ratio_bound_ae`), and the finite density gives `μ(B_ρ(x)) ≤ C ρ^n` for small `ρ` (child `ball_mass_le_of_density`).
- Calls: `S.intcpt_vdb_ball_mass_le_of_density`, `S.intcpt_vdb_liminf_ratio_bound_ae`, `S.intcpt_vdb_open_thickening_exhaustion`
- Called by: `S.integral_compactness_theorem`

##### `S.intcpt_vdb_liminf_ratio_bound_ae`

- Node: `root.integral_compactness-a1.variation_density_bound-a1.liminf_ratio_bound_ae-a1`; accepted candidate `34d20def09b4`
- Statement and proof: **Simon Ch. 8, proof of 5.9, printed estimate (1)** (child `liminf_ratio_bound_ae` of `variation_density_bound`): if `sup_i ν_i(thickening(r, W)) < ∞`, then for `μ`-a.e. `x ∈ W` some `c ∈ ℕ` satisfies `liminf_i ν_i(B_ρ(x)) ≤ c μ(B_ρ(x))` for every `ρ ∈ (0, r)`. The Besicovitch covering estimate (Ch. 1, 3.12), with its constant `C = C(N)` and `ρ₀ = r`, is exactly the covering hypothesis of the a.e. argument for each `ν_i`.
- Calls: `S.intcpt_vdb_besicovitch_cover_estimate`, `S.intcpt_vdb_liminf_bound_ae_of_cover`
- Called by: `S.intcpt_variation_liminf_density_bound`

###### `S.intcpt_vdb_besicovitch_cover_estimate`

- Node: `root.integral_compactness-a1.variation_density_bound-a1.liminf_ratio_bound_ae-a1.besicovitch_cover_estimate-a1`; accepted candidate `16c6bb837777`
- Statement and proof: **Simon Ch. 8, 5.9, proof of estimate (1), Besicovitch step, p. 219** (child `besicovitch_cover_estimate` of `liminf_ratio_bound_ae`): if every `x ∈ A` is the centre of a closed ball `B_σ(x)`, `0 < σ < ρ₀`, with `μ(B_σ(x)) ≤ t ν(B_σ(x))`, then `μ(A) ≤ C t ν({dist(·, A) < ρ₀})`, where `C` is the Besicovitch number of `ℝ^N` (Ch. 1, 3.12). The covering lemma splits a subfamily of these balls covering `A` into `C` disjoint, hence countable, subfamilies; sum the ratio bound over each.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_vdb_liminf_ratio_bound_ae`

###### `S.intcpt_vdb_liminf_bound_ae_of_cover`

- Node: `root.integral_compactness-a1.variation_density_bound-a1.liminf_ratio_bound_ae-a1.liminf_bound_ae_of_cover-a1`; accepted candidate `57bc90402087`
- Statement and proof: **Simon Ch. 8, proof of 5.9, estimate (1)** (child `liminf_bound_ae_of_cover` of `liminf_ratio_bound_ae`): suppose `μ(A) ≤ C t ν_i({dist(·, A) < r})` whenever every `x ∈ A` is the centre of a closed ball `B_σ(x)`, `0 < σ < r`, with `μ(B_σ(x)) ≤ t ν_i(B_σ(x))` (the Besicovitch estimate), and `S = sup_i ν_i({dist(·, W) < r}) < ∞`. Then for `μ`-a.e. `x ∈ W` there is `c` with `liminf_i ν_i(B_ρ(x)) ≤ c μ(B_ρ(x))` for all `0 < ρ < r`. For each `j`, the exceptional set lies in the increasing union of the sets `A_i` of points with one radius `ρ` such that `(j + 1) μ(B_ρ(x)) < ν_k(B_ρ(x))` for all `k ≥ i`; each `A_i` has measure at most `C S / (j + 1)`, hence so does the exceptional set, which is therefore `μ`-null.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_vdb_liminf_ratio_bound_ae`

##### `S.intcpt_vdb_open_thickening_exhaustion`

- Node: `root.integral_compactness-a1.variation_density_bound-a1.open_thickening_exhaustion-a1`; accepted candidate `5f004b7f24da`
- Statement and proof: **Simon Ch. 8, proof of 5.9, printed (1)–(2), localisation and exhaustion** (child `open_thickening_exhaustion` of `variation_density_bound`): an open `U ⊆ ℝ^N` is covered by countably many sets `W_p` whose `r_p`-thickenings (`r_p > 0`) are relatively compact open subsets of `U`. Take `W = B°_s(x)` and `r = s` with `B°_{3s}(x) ⊆ U`: `thickening s (B°_s(x)) ⊆ B°_{2s}(x)` has compact closure inside `B_{2s}(x) ⊆ U`, and countably many such balls cover `U` (Lindelöf).
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_variation_liminf_density_bound`

##### `S.intcpt_vdb_ball_mass_le_of_density`

- Node: `root.integral_compactness-a1.variation_density_bound-a1.ball_mass_le_of_density-a1`; accepted candidate `dca2d2a0f9d8`
- Statement and proof: **Simon Ch. 8, proof of 5.9, passage from (1) to (2)** (child `ball_mass_le_of_density` of `variation_density_bound`): a finite density `Θ^n(μ, x) = θ < ∞` gives `μ(B_ρ(x)) ≤ C ρ^n`, with `C = (θ + 1) ω_n`, for all small `ρ > 0`. The ratio `μ(B_ρ(x)) / (ω_n ρ^n)` is eventually `< θ + 1`, and `0 < ω_n ρ^n < ∞` clears the denominator.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_variation_liminf_density_bound`

#### `S.intcpt_rescaled_restriction_integral`

- Node: `root.integral_compactness-a1.rescaled_integral-a1`; accepted candidate `3642d9420299`
- Statement and proof: Rescaled restrictions of integral varifolds are integral (Simon Ch. 8, 5.9): if `V = v(M, θ)` is an integral `n`-varifold on `U`, `t > 0`, the similarity `σ(y) = ξ + t y` maps `O` into `U`, and `W` is `η_{ξ,t #} V` restricted to `Gₙ(O)`, then `W = v(O ∩ σ⁻¹(M), θ ∘ σ)` is integral.
- Calls: `S.intcpt_ri_countablyRectifiable_similarity_preimage`, `S.intcpt_ri_restrict_similarity_image`, `S.intcpt_ri_weightedApproxTangent_inter_open_iff`, `S.intcpt_ri_weightedApproxTangent_similarity_iff`
- Called by: `S.intcpt_diagonal_integral_blowup`

##### `S.intcpt_ri_restrict_similarity_image`

- Node: `root.integral_compactness-a1.rescaled_integral-a1.restrict_similarity_image-a1`; accepted candidate `b82dda98146e`
- Statement and proof: `H^n ⌞ σ(A) = t^n σ_# (H^n ⌞ A)` for the similarity `σ(y) = ξ + t y`, `t > 0`, and every set `A` (measurable or not): `σ = (ξ + ·) ∘ (t • ·)` scales `H^n` of every set by `t^n`, and on a Borel set `B` both sides evaluate to `H^n(B ∩ σ(A)) = H^n(σ(σ⁻¹(B) ∩ A))`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_rescaled_restriction_integral`

##### `S.intcpt_ri_countablyRectifiable_similarity_preimage`

- Node: `root.integral_compactness-a1.rescaled_integral-a1.rectifiable_similarity_preimage-a1`; accepted candidate `eef4c8389281`
- Statement and proof: Countable `n`-rectifiability is preserved by the inverse similarity (used for the rescaled integral varifolds in Simon Ch. 8, 5.9): if `M` is countably `n`-rectifiable and `t > 0`, then so is `σ⁻¹(M)` for `σ(y) = ξ + t y`, with exceptional set `σ⁻¹(M₀)` and parametrizations `v ↦ t⁻¹ (F_j(v) - ξ)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_rescaled_restriction_integral`

##### `S.intcpt_ri_weightedApproxTangent_inter_open_iff`

- Node: `root.integral_compactness-a1.rescaled_integral-a1.approx_tangent_local-a1`; accepted candidate `0e81510a03fc`
- Statement and proof: Weighted approximate tangent planes (Simon Ch. 3, 1.7) are local: if `O` is open and `y ∈ O`, then `O ∩ M` has weighted approximate tangent space `P` at `y` with respect to `θ` if and only if `M` has.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_rescaled_restriction_integral`

##### `S.intcpt_ri_weightedApproxTangent_similarity_iff`

- Node: `root.integral_compactness-a1.rescaled_integral-a1.approx_tangent_similarity-a1`; accepted candidate `cde12a445389`
- Statement and proof: Weighted approximate tangent planes (Simon Ch. 3, 1.7) are invariant under the similarity `σ(w) = ξ + t w`, `t > 0`: `σ⁻¹(M)` has weighted approximate tangent space `P` at `y` with respect to `θ ∘ σ` if and only if `M` has weighted approximate tangent space `P` at `σ(y)` with respect to `θ`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_rescaled_restriction_integral`

#### `S.intcpt_diagonal_integral_blowup`

- Node: `root.integral_compactness-a1.diagonal_blowup-a1`; accepted candidate `6b00aec5ff1c`
- Statement and proof: The diagonal blow-up in the proof of **Simon Ch. 8, 5.9** (printed steps (3)–(4); node `diagonal_blowup` of `integral_compactness`), restricted to the fixed ball `B°_5(0)`. Let `V_i → V` with each `V_i` integral of locally bounded first variation, let `V` have tangent plane `P` with multiplicity `θ₀` at `ξ`, and let `liminf_i ‖δV_i‖(B_ρ(ξ)) ≤ c ρ^n` for `0 < ρ < r`. For scales `λ_k ↓ 0` and well-chosen indices `i_k`, the blow-ups `W_k = (V_{i_k})_{ξ,λ_k} ⌞ (B°_5(0) × G)` are integral varifolds on `B°_5(0)` with locally bounded first variation, `‖δW_k‖(B°_5(0)) ≤ 2 max(c,1) 5^n λ_k → 0`, and `W_k → θ₀ v(P)` on `B°_5(0) × G`.
- Calls: `S.intcpt_diag_ball_cc_dense_seq`, `S.intcpt_diag_blowup_variation_bound`, `S.intcpt_diag_dense_family_tendsto`, `S.intcpt_diag_rescaled_integrable`, `S.intcpt_diag_rescaled_radon_tendsto`, `S.intcpt_rescaled_restriction_integral`
- Called by: `S.integral_compactness_theorem`

##### `S.intcpt_diag_rescaled_radon_tendsto`

- Node: `root.integral_compactness-a1.diagonal_blowup-a1.rescaled_radon_tendsto-a1`; accepted candidate `9f2a9c42fd07`
- Statement and proof: Blow-ups preserve Radon convergence (Simon Ch. 8, proof of 5.9: "`V_i → V`, and hence `η_{ξ,λ#}V_i → η_{ξ,λ#}V` for each fixed `λ > 0`"). If `V_i → V` as Radon measures on `Gₙ(U)`, `t > 0` and `F ∈ C_c(ℝ^N × G(N,n))` has `ξ + t y ∈ U` for every `(y, S) ∈ spt F`, then `∫ F dV_{i,ξ,t} → ∫ F dV_{ξ,t}`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_diagonal_integral_blowup`

##### `S.intcpt_diag_rescaled_integrable`

- Node: `root.integral_compactness-a1.diagonal_blowup-a1.rescaled_integrable-a1`; accepted candidate `916dff12c88b`
- Statement and proof: Test functions are integrable for the blow-up `V_{ξ,t} = η_{ξ,t #} V` (Simon Ch. 8, 1.1 and 5.1) when the blow-up of their support stays in `U`: if `t > 0` and `ξ + t y ∈ U` for every `(y, S) ∈ spt F`, then `F ∈ C_c(ℝ^N × G(N,n))` is `rescaledMeasure V ξ t`-integrable.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_diagonal_integral_blowup`

##### `S.intcpt_diag_ball_cc_dense_seq`

- Node: `root.integral_compactness-a1.diagonal_blowup-a1.ball_cc_dense_seq-a1`; accepted candidate `e22ffb6fb00b`
- Statement and proof: A countable sup-dense family of test functions on `B°_R(0) × G(N,n)` (Simon Ch. 8, proof of 5.9, printed (3)–(4), step 1 of the diagonal blow-up): for `R > 0` there are `g_m ∈ C_c(ℝ^N × G(N,n))` with `spt g_m ⊆ B°_R(0) × G(N,n)` such that every `f ∈ C_c(ℝ^N × G(N,n))` with `spt f ⊆ B°_R(0) × G(N,n)` is a uniform limit of the `g_m`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_diagonal_integral_blowup`

##### `S.intcpt_diag_blowup_variation_bound`

- Node: `root.integral_compactness-a1.diagonal_blowup-a1.blowup_variation_bound-a1`; accepted candidate `30f90c0831a0`
- Statement and proof: One blow-up of the diagonal argument in Simon Ch. 8, proof of 5.9 (printed (4): "(by (2)) `‖δW_i‖(B_R(0)) → 0`"). If `V` has locally bounded first variation in `U`, `t, R > 0` and `ξ + t y ∈ U` for every `y ∈ B°_R(0)`, then `W = V_{ξ,t} ⌞ (B°_R(0) × G(N,n))` is an `n`-varifold on `B°_R(0)` with locally bounded first variation, and `‖δW‖(B°_R(0)) ≤ t^{-n} t ‖δV‖(B_{tR}(ξ))`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_diagonal_integral_blowup`

##### `S.intcpt_diag_dense_family_tendsto`

- Node: `root.integral_compactness-a1.diagonal_blowup-a1.dense_family_tendsto-a1`; accepted candidate `f4c8b22df40a`
- Statement and proof: Convergence on a dense family of test functions extends to all of them under a uniform mass bound (Simon Ch. 8, proof of 5.9, printed (3): the diagonal blow-up converges against every test function once it does against a countable dense family). Let `A = O × G(N,n)`, let the `g_m ∈ C_c(ℝ^N × G(N,n))` with `spt g_m ⊆ A` be uniformly dense among the `f ∈ C_c(ℝ^N × G(N,n))` with `spt f ⊆ A`, and let `μ_k(A) ≤ C` and `ν_k(A) ≤ C < ∞` for all large `k`. If `∫ g_m dμ_k - ∫ g_m dν_k → 0` for every `m`, then `∫ f dμ_k - ∫ f dν_k → 0` for every such `f`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_diagonal_integral_blowup`

#### `S.intcpt_allard_integrality_lemma`

- Node: `root.integral_compactness-a1.allard_lemma-a1`; accepted candidate `7c7818c3c288`
- Statement and proof: **Simon Ch. 8, Lemma 5.10 and Remark 5.11, pp. 219–223** (child `allard_lemma` of `integral_compactness`): for `0 < δ ≤ δ̄` and `0 < ε ≤ δ⁴`, if `μ_W(B°_3(0)) ≤ Λ`, `‖δW‖(B°_3(0)) < ε²` and `∫_{B°_3(0) × G} ‖p_S - p_P‖ dW < ε²`, then (a) the points of `B_2(0) ∩ spt μ_W` where printed (1) or (2) fails have `μ_W`-measure at most `c₀ ε` (`intcpt_allard_bad_set_bound`), and (b) on a fibre `p_P(y) = x`, `|x| < 1`, the points satisfying (1) and (2) with `|y - p_P(y)| < ε` and `Θ^n(μ_W, y) ≥ 1` have `Σ_y Θ^n(μ_W, y) ≤ (1 + δ) ω_n^{-1} μ_W(B_1(x)) + δ`. For (b), Remark 5.11: with `m₀ = ⌈(3/2) Λ / ω_n⌉ + 1` and `δ̄ = min{δ'_{m₀}, 1/2}` (`intcpt_allard_fibre_density_sum_bound` with `M = m₀`), `m₀` such points would give `m₀ ≤ Σ Θ ≤ (3/2) Λ / ω_n + 1/2 < m₀`, as `B_1(x) ⊆ B°_3(0)`; so a fibre has at most `m₀` of them and the fibre bound applies. Integrality of `W` is not used.
- Calls: `S.intcpt_allard_bad_set_bound`, `S.intcpt_allard_fibre_density_sum_bound`
- Called by: `S.intcpt_flat_limit_integer_multiplicity`

##### `S.intcpt_allard_good_point_monotonicity`

- Node: `root.integral_compactness-a1.allard_lemma-a1.good_point_monotonicity-a1`; accepted candidate `dcd75faf5410`
- Statement and proof: **Simon Ch. 8, proof of 5.10, printed (3), p. 221** (child `good_point_monotonicity` of `allard_lemma`): if `B°_1(y) ⊆ U`, `μ_W(B°_1(y)) ≤ Λ` and `‖δW‖(B_ρ(y)) ≤ ε μ_W(B_ρ(y))` for `0 < ρ < 1` (printed (1)), the monotonicity formula 3.3 with `ρ₀ = 1` shows that `e^{ερ} ρ^{-n} μ_W(B_ρ(y))` is increasing on `(0, 1)` and that `Θ^n(μ_W, y)` exists, is finite and is at most `e^{εσ} ω_n^{-1} σ^{-n} μ_W(B_σ(y))`. Hence `μ_W(B_σ(y)) ≤ e^ε Λ ρ^{-n} σ^n` for `0 < σ < ρ < 1`, and letting `ρ ↑ 1` gives `μ_W(B_σ(y)) ≤ e^ε Λ σ^n`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_bad_set_bound`, `S.intcpt_allard_fibre_density_sum_bound`

##### `S.intcpt_allard_bad_set_bound`

- Node: `root.integral_compactness-a1.allard_lemma-a1.bad_set_bound-a1`; accepted candidate `c9be4d105082`
- Statement and proof: **Simon Ch. 8, proof of 5.10, printed (4)–(5) and the Besicovitch estimate, p. 221** (child `bad_set_bound` of `allard_lemma`): if `μ_W(B°_3(0)) ≤ Λ`, `‖δW‖(B°_3(0)) < ε²` and `∫_{B°_3(0) × G} ‖p_S - p_P‖ dW < ε²`, then the set of `y ∈ B_2(0) ∩ spt μ_W` at which `‖δW‖(B_ρ(y)) ≤ ε μ_W(B_ρ(y))` (printed (1), with `δ‖W‖` read as `‖δW‖`) or `∫_{B_ρ(y) × G} ‖p_S - p_P‖ dW ≤ ε ρ^n` (printed (2)) fails for some `ρ ∈ (0, 1)` has `μ_W`-measure at most `c₀ ε`, with `c₀` depending only on `N` and `Λ`. At such a `y` some `ρ_y ∈ (0, 1)` has `μ_W(B_{ρ_y}(y)) ≤ ε⁻¹ ‖δW‖(B_{ρ_y}(y))` or, where (1) holds, by printed (3) `μ_W(B_{ρ_y}(y)) ≤ e Λ ρ_y^n ≤ e Λ ε⁻¹ ∫_{B_{ρ_y}(y) × G} ‖p_S - p_P‖ dW`; the Besicovitch covering lemma then bounds `μ_W` of the bad set by `C (ε⁻¹ ε² + e Λ ε⁻¹ ε²) = C (e Λ + 1) ε`.
- Calls: `S.intcpt_allard_bsb_besicovitch_cover`, `S.intcpt_allard_bsb_marginal_measure`, `S.intcpt_allard_good_point_monotonicity`
- Called by: `S.intcpt_allard_integrality_lemma`

###### `S.intcpt_allard_bsb_besicovitch_cover`

- Node: `root.integral_compactness-a1.allard_lemma-a1.bad_set_bound-a1.besicovitch_cover-a1`; accepted candidate `00d7963dc1a3`
- Statement and proof: **Simon Ch. 8, proof of Lemma 5.10, the Besicovitch step (p. 221)** (child `besicovitch_cover` of `bad_set_bound`): if every `x ∈ A` is the centre of a closed ball `B_σ(x) ⊆ O`, `0 < σ ≤ R`, with `μ(B_σ(x)) ≤ t ν(B_σ(x))`, then `μ(A) ≤ C t ν(O)`, where `C` is the Besicovitch number of `ℝ^N` (Ch. 1, 3.12). The covering lemma splits a subfamily of these balls covering `A` into `C` disjoint, hence countable, subfamilies; sum the ratio bound over each.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_bad_set_bound`

###### `S.intcpt_allard_bsb_marginal_measure`

- Node: `root.integral_compactness-a1.allard_lemma-a1.bad_set_bound-a1.marginal_measure-a1`; accepted candidate `0656a76739b1`
- Statement and proof: **Simon Ch. 8, proof of 5.10, p. 221, the Besicovitch step** (child `marginal_measure` of `bad_set_bound`): for any measure `m` on `ℝ^N × G(N,n)` and any `g : ℝ^N × G(N,n) → [0,∞]`, the functional `A ↦ ∫_{A × G(N,n)} g dm` agrees on Borel sets `A ⊆ ℝ^N` with a measure, namely the image of `m ⌞ g` under `(x, S) ↦ x`; so it is monotone and countably additive there.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_bad_set_bound`

##### `S.intcpt_allard_first_variation_le_sup_mul`

- Node: `root.integral_compactness-a1.allard_lemma-a1.first_variation_bound-a1`; accepted candidate `b61202877270`
- Statement and proof: **Simon Ch. 8, 2.5–2.6, as used in the proof of 5.10 (printed (7))** (child `first_variation_bound` of `allard_lemma`): if `W` has locally bounded first variation, `K ⊆ U` is compact and `X` is a `C¹` field with `spt X ⊆ K` and `|X| ≤ B`, then `|δW(X)| ≤ B ‖δW‖(K)`. Write `δW(X) = -∫ ν·X d‖δW‖` with `|ν| = 1` `‖δW‖`-a.e. (2.6); the integrand is bounded by `B` on `K` and vanishes off `K`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_weighted_radial_monotonicity`

##### `S.intcpt_allard_radial_field_divergence`

- Node: `root.integral_compactness-a1.allard_lemma-a1.radial_field_divergence-a1`; accepted candidate `8a11bebfb2e9`
- Statement and proof: The tangential divergence of the radial-type field `Y(w) = a(w) (w - y)` (the pointwise computation behind Simon Ch. 8, 3.2–3.5): if `a` is differentiable at `z`, then `div_S Y(z) = n a(z) + Da(z)[p_S(z - y)]`, via `DY(z) = a(z) id + Da(z) ⊗ (z - y)`, `div_S Y(z) = trace (p_S ∘ DY(z))`, `trace p_S = n` and `trace (ℓ ⊗ u) = ℓ(u)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_weighted_radial_monotonicity`

##### `S.intcpt_allard_weighted_radial_monotonicity`

- Node: `root.integral_compactness-a1.allard_lemma-a1.weighted_radial_monotonicity-a1`; accepted candidate `3c6818bddadb`
- Statement and proof: Integrated weighted monotonicity (Simon Ch. 8, 3.5 integrated from `σ` to `ρ`, as for (6)–(7) in the proof of 5.10): if (1r)–(3r) hold on `B_r(y)` for `0 < r < 1`, then for `0 < σ ≤ ρ` with `ρA < 1` and `Ĩ(t) = ∫ φ(|z - y|²/t²) h(z) dμ_W(z)`, `Ĩ(σ)/σ^n ≤ Ĩ(ρ)/ρ^n + 2^{n+1}(M + K)ερ`. For `t ∈ [σ, ρ]`, `tĨ'(t) - nĨ(t) ≥ G(t) - δW(X_t)`, where `X_t(z) = h(z)φ(|z - y|²/t²)(z - y)` and `G(t) = ∫ φ(|z - y|²/t²) Dh(z)[p_S(z - y)] dW(z,S)`, and `|G(t)| + |δW(X_t)| ≤ A^{n+1}(M + K)εt^{n+1}`; so `t ↦ Ĩ(t)/t^n + 2^{n+1}(M + K)εt` is nondecreasing on `[σ, ρ]`.
- Calls: `S.intcpt_allard_first_variation_le_sup_mul`, `S.intcpt_allard_radial_field_divergence`, `S.intcpt_allard_wrm_cutoff_mass_hasDerivAt`, `S.intcpt_allard_wrm_first_variation_lower_bound`, `S.intcpt_allard_wrm_gradient_term_bound`
- Called by: `S.intcpt_allard_cylinder_monotonicity`

###### `S.intcpt_allard_wrm_cutoff_mass_hasDerivAt`

- Node: `root.integral_compactness-a1.allard_lemma-a1.weighted_radial_monotonicity-a1.cutoff_mass_derivative-a1`; accepted candidate `ef2ced1ce68c`
- Statement and proof: Differentiation of the radial cutoff mass under the integral sign (step 5 of the weighted radial monotonicity argument, Simon Ch. 8, §3): if `φ` is `C¹` with `φ = 0` on `[A², ∞)`, `h` is continuous and `μ(B_R(y)) < ∞`, then for `t₀ > 0` with `t₀ A < R` the map `t ↦ ∫ φ(|z - y|²/t²) h(z) dμ(z)` has derivative `∫ φ'(|z - y|²/t₀²)(-2|z - y|²/t₀³) h(z) dμ(z)` at `t₀`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_weighted_radial_monotonicity`

###### `S.intcpt_allard_wrm_first_variation_lower_bound`

- Node: `root.integral_compactness-a1.allard_lemma-a1.weighted_radial_monotonicity-a1.first_variation_lower_bound-a1`; accepted candidate `21ccf18c67b4`
- Statement and proof: Weighted radial first-variation inequality at a fixed radius (Simon Ch. 8, 3.5, with the sign of `δV(X)` corrected): for `X_t(z) = h(z) φ(|z - y|²/t²) (z - y)`, `n Ĩ(t) - t J(t) + G(t) ≤ δW(X_t)`, because the dropped normal term is nonnegative (`h ≥ 0`, `φ' ≤ 0` and `⟨w, p_S w⟩ ≤ |w|²`). The divergence of `X_t` is supplied by hypothesis (Div).
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_weighted_radial_monotonicity`

###### `S.intcpt_allard_wrm_gradient_term_bound`

- Node: `root.integral_compactness-a1.allard_lemma-a1.weighted_radial_monotonicity-a1.gradient_term_bound-a1`; accepted candidate `b30cec5aa99c`
- Statement and proof: The gradient term `G(t) = ∫ φ(|z - y|²/t²) Dh(z)[p_S(z - y)] dW(z,S)` of the weighted radial monotonicity argument (Simon Ch. 8, 3.3–3.5; tilt-excess estimate) satisfies `|G(t)| ≤ M A^{n+1} ε t^{n+1}`: off `B_{tA}(y) × G(N,n)` the cutoff vanishes, on it the integrand is at most `M (tA) ‖p_S - p_P‖`, and the tilt-excess hypothesis bounds the integral of `‖p_S - p_P‖`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_weighted_radial_monotonicity`

##### `S.intcpt_allard_cylinder_monotonicity`

- Node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1`; accepted candidate `6badac6694b2`
- Statement and proof: Cylinder monotonicity (Simon Ch. 8, (7) in the proof of 5.10, "proved by simply integrating 3.5"): under (1r)–(3r) on `B_r(y)` for `0 < r < 1`, for `0 < τ ≤ 1` and `0 < σ ≤ ρ < 1`, `μ_W(U^τ_σ(y))/σ^n ≤ μ_W(U^{2τ}_ρ(y))/ρ^n + C(1 + K)ερ/τ` with `C = 2^{n+1}(M₀ + 1)`, where `U^τ_r(y) = B_r(y) ∩ {z : |q(z - y)| < τ}` and `q = id - p_P`. The integrated weighted monotonicity is applied to a cylindrical weight `h` (`1` where `|q(z - y)| < τ`, `0` where `|q(z - y)| ≥ 2τ`, `|Dh(z)[p_S(z - y)]| ≤ (M₀/τ)|p_S - p_P||z - y|`) and radial cutoffs `φ_j` with `A_j ↓ 1`; letting `j → ∞` gives the inequality for `∫_{B_t(y)} h dμ_W`, which bounds the cylinder masses.
- Calls: `S.intcpt_allard_cm_cutoff_integral_tendsto`, `S.intcpt_allard_cm_cylinder_mass_bound`, `S.intcpt_allard_cm_cylinder_weight`, `S.intcpt_allard_cm_radial_cutoff`, `S.intcpt_allard_weighted_radial_monotonicity`
- Called by: `S.intcpt_allard_fibre_density_sum_bound`

###### `S.intcpt_allard_cm_cylinder_weight`

- Node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1.cylinder_weight-a1`; accepted candidate `7bbdba787ff7`
- Statement and proof: Cylinder cut-off weight (Simon Ch. 8, proof of Lemma 5.10, displays (6)–(7): the `h` used in 3.5, `h(z) = f(|q(z - y)|)` with `f ≡ 1` on `[0, τ)`, `f ≡ 0` on `(2τ, ∞)`). With `M₀ = 4 sup |st'|` (`st = Real.smoothTransition`), `h(z) = st(4 - ‖q(z - y)‖²/τ²)` is `C¹`, takes values in `[0, 1]`, equals `1` where `‖q(z - y)‖ < τ` and `0` where `‖q(z - y)‖ ≥ 2τ` (`q = id - p_P`), and `|Dh(z)[p_S(z - y)]| ≤ (M₀/τ) ‖p_S - p_P‖ ‖z - y‖`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_cylinder_monotonicity`

###### `S.intcpt_allard_cm_radial_cutoff`

- Node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1.radial_cutoff-a1`; accepted candidate `76dfa07f07aa`
- Statement and proof: **Simon Ch. 8, proof of 5.10, p. 221, the radial cutoffs** (child `radial_cutoff` of `cylinder_monotonicity`, step 1): for `A > 1`, `φ(s) = st((A² - s)/(A² - 1))`, with `st` Mathlib's `Real.smoothTransition`, is a `C¹` non-increasing function with values in `[0,1]` that is `1` on `(-∞, 1]` and `0` on `[A², ∞)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_cylinder_monotonicity`

###### `S.intcpt_allard_cm_cutoff_integral_tendsto`

- Node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1.cutoff_integral_tendsto-a1`; accepted candidate `34701a1b0859`
- Statement and proof: Dominated convergence for shrinking radial cutoffs (step 4 of the cylinder monotonicity used for Simon Ch. 8, 5.9): if `φ_j = 1` on `(-∞, 1]`, `φ_j = 0` on `[A_j², ∞)`, `0 ≤ φ_j ≤ 1`, `A_j → 1` and `μ(B_R(y)) < ∞` with `t A_j ≤ R`, then `∫ φ_j(|z - y|²/t²) h(z) dμ(z) → ∫_{B_t(y)} h dμ` for measurable `0 ≤ h ≤ 1`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_cylinder_monotonicity`

###### `S.intcpt_allard_cm_cylinder_mass_bound`

- Node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1.cylinder_mass_bound-a1`; accepted candidate `e18e1ddd5ef1`
- Statement and proof: Cylinder masses from cut-off ball integrals (Simon Ch. 8, proof of Lemma 5.10, display (7): the last step after integrating 3.5 from `σ` to `ρ`). Let `0 ≤ h ≤ 1` be measurable with `h = 1` where `‖q(z - y)‖ < τ` and `h = 0` where `‖q(z - y)‖ ≥ 2τ` (`q = id - p_P`), `0 < σ ≤ ρ` and `μ(B_ρ(y)) < ∞`. If `σ^{-n} ∫_{B_σ(y)} h dμ ≤ ρ^{-n} ∫_{B_ρ(y)} h dμ + E`, then in `[0, ∞]` `σ^{-n} μ(U^τ_σ(y)) ≤ ρ^{-n} μ(U^{2τ}_ρ(y)) + max(E, 0)`, where `U^τ_r(y) = B_r(y) ∩ {z : ‖q(z - y)‖ < τ}`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_cylinder_monotonicity`

##### `S.intcpt_allard_cluster_selection`

- Node: `root.integral_compactness-a1.allard_lemma-a1.cluster_selection-a1`; accepted candidate `37474d21d289`
- Statement and proof: Cluster selection (Simon Ch. 8, proof of 5.10 (8)): if two distinct points of a finite set `s` with `#s ≥ 2` are at distance `≤ d`, there are centres `Z ⊆ s` with `#Z < #s` and a radius `0 ≤ S ≤ (10 #s)^{#s} d` such that every `y ∈ s` is within `S` of `Z` and distinct centres are at least `2d + 4S` apart. Greedy merging: take an admissible pair (`Z ⊆ s` nonempty, `#Z < #s`, `S`-covering, `S ≤ d (5^{#s - #Z} - 1) / 2`) with `#Z` minimal; two centres closer than `2d + 4S` would give the admissible pair `(Z ∖ {z'}, 2d + 5S)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_cylinder_cluster_bound`

##### `S.intcpt_allard_cylinder_cluster_bound`

- Node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1`; accepted candidate `8e4e5cfa900f`
- Statement and proof: **Simon Ch. 8, proof of 5.10, printed (8), pp. 222–223** (child `cylinder_cluster_bound` of `allard_lemma`): at points `y` of one fibre `p_P(y) = x` with `|y - p_P(y)| < ε`, the monotonicity (M_y) and the cylinder comparison (C_y) give `Σ_{y ∈ s} μ(U^τ_σ(y)) / σ^n ≤ (1 + c δ²) μ(B_1(x)) + c δ²` whenever `#s ≤ m`, `σ ≤ δ²`, `2δ²σ ≤ τ` and `4τ ≤ |y - y'|` for distinct points. The proof is the book's induction on the number of points, with the constants defined by recursion on `m`: `c_0 = 0`, `δ_0 = 1/2` and, for `a = 4(10(m+1))^{m+1}`, `b = (2^n - 1)a`, `c_{m+1} = max{2^{n+2}, b + c_m + b c_m, (1 + b)c_m + (m+1)K}`, `δ_{m+1} = min{δ_m, 1/a}`. At most one point is the monotonicity bound (`intcpt_allard_ccb_one_point_ball_bound`, as `U^τ_σ(y) ⊆ B_σ(y)`). For at least two points, `intcpt_allard_ccb_reduction_step` (the grouping estimate `intcpt_allard_ccb_cylinder_grouping` applied to the clusters of `intcpt_allard_cluster_selection`) passes to `Z ⊆ s` with `#Z ≤ m` and admissible scales `(σ', τ')` at the cost `Σ_s ≤ (1 + bδ²) Σ_Z + (m+1)Kδ²`; the induction hypothesis bounds `Σ_Z`, and `intcpt_allard_ccb_affine_combine` composes the two affine bounds in `[0, ∞]`.
- Calls: `S.intcpt_allard_ccb_affine_combine`, `S.intcpt_allard_ccb_one_point_ball_bound`, `S.intcpt_allard_ccb_reduction_step`, `S.intcpt_allard_cluster_selection`
- Called by: `S.intcpt_allard_fibre_density_sum_bound`

###### `S.intcpt_allard_ccb_cylinder_grouping`

- Node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1.cylinder_grouping-a1`; accepted candidate `f3fab24b30d2`
- Statement and proof: Cylinder grouping (Simon Ch. 8, proof of 5.10 (8), steps (b)–(d)): for a `d`-separated finite set `s` in one fibre of `p = Grassmannian.project P`, the cylinders `U^{d/2}_ρ(y)`, `y ∈ s`, are disjoint and lie in the enlarged cylinders `U^{d/2+S}_{ρ+S}(z)` about representatives `z ∈ Z` within distance `S`; hence the `ρ^{-n}`-normalized sum over `s` is at most `1 + (2^n - 1) u` times the `(ρ + S)^{-n}`-normalized sum over `Z`, when `S ≤ u ρ` and `u ≤ 1`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_ccb_reduction_step`

###### `S.intcpt_allard_ccb_one_point_ball_bound`

- Node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1.one_point_ball_bound-a1`; accepted candidate `2d86d13cadff`
- Statement and proof: One-point bound from monotonicity (Simon Ch. 8, 5.10, proof of (8), one point): if `‖y - x‖ < ε ≤ δ⁴`, `0 < δ ≤ 1/2`, `0 < σ ≤ δ²` and `r ↦ e^{εr} μ(B_r(y)) / r^n` is non-decreasing on `(0,1)`, then `μ(B_σ(y)) / σ^n ≤ (1 + 2^{n+2} δ²) μ(B_1(x))`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_cylinder_cluster_bound`

###### `S.intcpt_allard_ccb_reduction_step`

- Node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1.reduction_step-a1`; accepted candidate `0f2f23ddc76e`
- Statement and proof: Reduction step (Simon Ch. 8, proof of 5.10 (8), inductive step for `#s ≥ 2`): let `s` be a `4τ`-separated set of `2 ≤ #s ≤ m + 1` points in one fibre of `p = Grassmannian.project P`, each within `ε` of that plane and satisfying the comparison (C_y). Cluster selection (CS) at the minimal distance `d` of `s` gives `Z ⊆ s` with `#Z ≤ m` and admissible scales `σ' = ρ + S`, `τ' = d/2 + S` (`ρ = d/(4δ²)`) such that the `σ^{-n}`-normalized cylinder sum over `s` is at most `1 + (2^n - 1) a δ²` times the `σ'^{-n}`-normalized sum over `Z`, plus `(m + 1) K δ²`, where `a = 4 (10 (m + 1))^{m + 1}`.
- Calls: `S.intcpt_allard_ccb_cylinder_grouping`
- Called by: `S.intcpt_allard_cylinder_cluster_bound`

###### `S.intcpt_allard_ccb_affine_combine`

- Node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1.affine_combine-a1`; accepted candidate `286a700acd46`
- Statement and proof: Composing two affine bounds in `[0,∞]` (Simon Ch. 8, proof of 5.10 (8), recombination of the induction constants): if `X ≤ (1 + b δ²) Y + k δ²` and `Y ≤ (1 + c δ²) M + c δ²` with `b, c, k ≥ 0`, `δ² ≤ 1`, `b + c + b c ≤ c'` and `(1 + b) c + k ≤ c'`, then `X ≤ (1 + c' δ²) M + c' δ²` (`M = ∞` allowed).
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_cylinder_cluster_bound`

##### `S.intcpt_allard_fibre_density_sum_bound`

- Node: `root.integral_compactness-a1.allard_lemma-a1.fibre_density_sum_bound-a1`; accepted candidate `f5333307aadd`
- Statement and proof: **Simon Ch. 8, proof of 5.10, printed (6) and (8) (p. 222), and Remark 5.11(∗) (p. 220)** (child `fibre_density_sum_bound` of `allard_lemma`): uniformly over fibres with at most `M` points, if each `y ∈ s` lies over `x`, in `B_2(0)`, within `ε` of `P` and satisfies printed (1) and (2), then `Σ_{y ∈ s} Θ^n(μ_W, y) ≤ (1 + δ) ω_n^{-1} μ_W(B_1(x)) + δ`. Erratum (E2): the book states (6)–(7) for `y ∈ B^n_1(0) ∖ p(A_1 ∪ A_2)`, but they are used, and proved, for points satisfying (1) and (2); the rescaling by `3/2` is replaced by working with `B_1(x)` directly.
- Calls: `S.intcpt_allard_cylinder_cluster_bound`, `S.intcpt_allard_cylinder_monotonicity`, `S.intcpt_allard_fdsb_density_cylinder_bound`, `S.intcpt_allard_fdsb_one_point_bound`, `S.intcpt_allard_fdsb_separated_sum_bound`, `S.intcpt_allard_good_point_monotonicity`
- Called by: `S.intcpt_allard_integrality_lemma`

###### `S.intcpt_allard_fdsb_density_cylinder_bound`

- Node: `root.integral_compactness-a1.allard_lemma-a1.fibre_density_sum_bound-a1.density_cylinder_bound-a1`; accepted candidate `60564de2c22d`
- Statement and proof: Simon Ch. 8, proof of Lemma 5.10, printed (6): if `θ ≤ e^{εσ} μ(B_σ(y))/(ω_n σ^n)` for `σ ∈ (0,1)` (D) and the cylinder ratios satisfy the comparison (C) with error `Kερ/τ`, then for `τ ∈ (0,1/4]` and `σ ∈ (0,1)`, `θ ≤ (e^ε μ(U^{4τ}_σ(y))/σ^n + Kεσ/τ)/ω_n`, where `U^t_r(y) = B_r(y) ∩ {z : |q(z - y)| < t}` and `q(v) = v - p_P(v)`. Since `|q(v)| ≤ |v|`, the ball `B_r(y)` lies in `U^t_r(y)` for `r < t`; for `σ ≤ τ` apply (D) at `σ`, and for `τ < σ` apply (D) at `τ` and then (C) with parameter `2τ` and radii `τ ≤ σ`, using `e^ε ≤ 2`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_fibre_density_sum_bound`

###### `S.intcpt_allard_fdsb_one_point_bound`

- Node: `root.integral_compactness-a1.allard_lemma-a1.fibre_density_sum_bound-a1.one_point_bound-a1`; accepted candidate `0c686aa9847f`
- Statement and proof: Simon Ch. 8, proof of Lemma 5.10 (one-point case of Remark 5.11 (∗)): if `θ ≤ e^{εσ} μ(B_σ(y))/(ω_n σ^n)` for every `σ ∈ (0,1)`, where `0 < δ ≤ 1/2`, `2^{n+2} δ ≤ 1`, `0 < ε ≤ δ⁴` and `|y - x| < ε`, then `θ ≤ (1 + δ) μ(B_1(x))/ω_n`. Take `σ = 1 - ε`, so that `B_σ(y) ⊆ B_1(x)`; then `e^{ε(1-ε)} ≤ e^ε ≤ 1 + 2ε`, `(1 - ε)^{-n} ≤ (1 + 2ε)^n ≤ 1 + (2^n - 1)2ε`, and `e^{ε(1-ε)} (1 - ε)^{-n} ≤ 1 + 2^{n+2}ε ≤ 1 + 2^{n+2}δ² ≤ 1 + δ`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_fibre_density_sum_bound`

###### `S.intcpt_allard_fdsb_separated_sum_bound`

- Node: `root.integral_compactness-a1.allard_lemma-a1.fibre_density_sum_bound-a1.separated_sum_bound-a1`; accepted candidate `653cf6d8cf30`
- Statement and proof: Density sum over a fibre with at least two points (Simon Ch. 8, 5.11(∗) from (8), in the proof of 5.9): with `d` the minimal distance between distinct points of `s`, the per-point bounds at `τ = d/16`, `σ = d/(8δ²)` and the cluster bound at `(σ, d/4)` sum to `Σ_{y∈s} Θ(y) ≤ (1 + δ) μ(B_1(x))/ω_n + δ`, the constants being absorbed by `Aδ ≤ 1`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_allard_fibre_density_sum_bound`

#### `S.intcpt_lipschitz_graph_fibre_bound`

- Node: `root.integral_compactness-a1.graph_fibre_bound-a1`; accepted candidate `6d75a7ddfd23`
- Statement and proof: **Fibre bound over countably many Lipschitz graphs** (Simon Ch. 8, 5.9; child `graph_fibre_bound` of `integral_compactness`, the inequality of step B6 (iii)–(iv) of its proof, used there instead of the mapping formula in (5)–(6) of the book's proof). Let `Γ_i` (`i ∈ ℕ`) be closed `L`-Lipschitz graphs over the `n`-plane `P` (`|q(y - z)| ≤ L |p(y - z)|` on each `Γ_i`, where `p` is the orthogonal projection onto `P` and `q = id - p`), `G ⊆ ⋃_i Γ_i` an `H^n`-measurable set and `g : ℝ^N → [0,∞]` arbitrary. Then `∫⁻_G g dH^n ≤ (1 + L²)^{n/2} ∫⁻_P (Σ_{y ∈ G, p(y) = a} g(y)) dH^n(a)`. The pieces `A_i = G ∩ (Γ_i ∖ ⋃_{j<i} Γ_j)` are pairwise disjoint `H^n`-measurable `L`-graphs with union `G`; the one-piece bound `intcpt_graph_piece_lintegral_le_fibre_sum` is summed over `i` by countable superadditivity of the lower integral, and over each `a` the fibres of the `A_i` are disjoint parts of the fibre of `G`.
- Calls: `S.intcpt_graph_piece_lintegral_le_fibre_sum`
- Called by: `S.intcpt_flat_limit_integer_multiplicity`

##### `S.intcpt_graph_hausdorff_le_projection`

- Node: `root.integral_compactness-a1.graph_fibre_bound-a1.graph_hausdorff_bound-a1`; accepted candidate `947598d179d9`
- Statement and proof: Hausdorff measure of an `L`-Lipschitz graph piece over an `n`-plane (a step in the proof of Simon Ch. 8, 5.9): if `|(y - z) - p_P(y - z)| ≤ L |p_P(y - z)|` for `y, z ∈ A` and `L ≥ 0`, then `p_P` is injective on `A` with a `(1 + L²)^{1/2}`-Lipschitz inverse on `p_P(A)`, so `H^n(A) ≤ (1 + L²)^{n/2} H^n(p_P(A))`. `A` need not be closed or measurable.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_graph_piece_lintegral_le_fibre_sum`

##### `S.intcpt_graph_projection_nullMeasurableSet`

- Node: `root.integral_compactness-a1.graph_fibre_bound-a1.graph_projection_null_measurable-a1`; accepted candidate `6d1584a48ca5`
- Statement and proof: Child `graph_projection_null_measurable` of the graph fibre bound (Simon Ch. 8, proof of 5.9): the projection `p = Grassmannian.project P` of an `H^n`-null-measurable `L`-Lipschitz graph `A` over `P` is `H^n`-null-measurable. The graph inequality makes `p` injective on `A`, and `‖p v‖² = ⟪v, p v⟫` makes `p` `1`-Lipschitz. Writing `A = B ∪ (A ∖ B)` with `B ⊆ A` Borel and `A ∖ B` null, `p '' B` is Borel by Lusin–Souslin and `p '' (A ∖ B)` is null by the Lipschitz image bound for `μH[n]`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_graph_piece_lintegral_le_fibre_sum`

##### `S.intcpt_graph_piece_lintegral_le_fibre_sum`

- Node: `root.integral_compactness-a1.graph_fibre_bound-a1.graph_piece_fibre_bound-a1`; accepted candidate `84cbaa5125b3`
- Statement and proof: **Fibre bound for one Lipschitz graph piece** (Simon Ch. 8, 5.9; child `graph_piece_fibre_bound` of `graph_fibre_bound`, steps (iii)–(iv) of B6 in the proof of the integral compactness theorem). Let `A` be an `H^n`-measurable `L`-Lipschitz graph over the `n`-plane `P` (`|q(y - z)| ≤ L |p(y - z)|` on `A`, where `p` is the orthogonal projection onto `P` and `q = id - p`) and `g : ℝ^N → [0,∞]` arbitrary. Then `∫⁻_A g dH^n ≤ (1 + L²)^{n/2} ∫⁻_P (Σ_{y ∈ A, p(y) = a} g(y)) dH^n(a)`. For a Borel simple `s ≤ g` the level pieces `A_c = s⁻¹{c} ∩ A` are `L`-graphs, so `H^n(A_c) ≤ (1 + L²)^{n/2} H^n(p(A_c))` (`intcpt_graph_hausdorff_le_projection`) with `p(A_c)` `H^n`-measurable (`intcpt_graph_projection_nullMeasurableSet`); as `p` is injective on `A`, `Σ_c c 1_{p(A_c)}` is at most the fibre sum on `P`. The lower integral is the supremum over such `s`, so no measurability of `g` is needed.
- Calls: `S.intcpt_graph_hausdorff_le_projection`, `S.intcpt_graph_projection_nullMeasurableSet`
- Called by: `S.intcpt_lipschitz_graph_fibre_bound`

#### `S.intcpt_flat_limit_integer_multiplicity`

- Node: `root.integral_compactness-a1.flat_limit_integer-a1`; accepted candidate `d06132309b44`
- Statement and proof: **Flat limits of integral varifolds have integer multiplicity** (Simon Ch. 8, 5.9, the printed proof "that `V` is integer multiplicity if the `V_i` are", pp. 218–219, with the repaired step B6; child `flat_limit_integer` of `integral_compactness`). Let `W_k` be integral `n`-varifolds on `B°_5(0)` with locally bounded first variation, `‖δW_k‖(B°_5(0)) → 0` and `W_k → θ₀ v(P)` as Radon measures on `B°_5(0) × G(N,n)`, where `θ₀ > 0`. Then `θ₀ ∈ ℕ`. For `n = 0` the weights are sums of integer point masses (`intcpt_fli_dim_zero_integer`). For `n ≥ 1` let `k₀ = ⌊θ₀⌋`, so `θ₀ < k₀ + 1`; the flat claim (`intcpt_fli_flat_claim`, fed with Allard's lemma 5.10, the integer densities of Remark 5.9, the canonical representation, the Lipschitz-graph fibre bound and the tangent-graph cover) gives `I₀ > 0` with `θ₀ I₀ ≤ c₀ δ⁴ + (1 + (4 δ⁴ / ω_n)²)^{n/2} k₀ I₀` for all small `δ > 0`. Letting `δ ↓ 0` gives `θ₀ ≤ k₀ ≤ θ₀`.
- Calls: `S.intcpt_allard_integrality_lemma`, `S.intcpt_canonical_tangent_representation`, `S.intcpt_fli_dim_zero_integer`, `S.intcpt_fli_flat_claim`, `S.intcpt_integral_density_integer`, `S.intcpt_lipschitz_graph_fibre_bound`
- Called by: `S.integral_compactness_theorem`

##### `S.intcpt_fli_weight_integral_tendsto`

- Node: `root.integral_compactness-a1.flat_limit_integer-a1.weight_tendsto-a1`; accepted candidate `bc2dd17ae121`
- Statement and proof: Weight form of flat convergence (Simon Ch. 8, proof of 5.9, pp. 218–219): if `∫ f dW_k → θ₀ ∫ f dv(P)` for every `f ∈ C_c(ℝ^N × G(N,n))` with `spt f ⊆ B°_5(0) × G(N,n)`, then `∫ g dμ_{W_k} → θ₀ ∫_P g dH^n` for every `g ∈ C_c(ℝ^N)` with `spt g ⊆ B°_5(0)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_fli_weight_compact_eventually_lt`, `S.intcpt_fli_flat_claim`, `S.intcpt_fli_dim_zero_integer`

##### `S.intcpt_fli_plane_ball_measure`

- Node: `root.integral_compactness-a1.flat_limit_integer-a1.plane_ball_measure-a1`; accepted candidate `1afc952ce5c0`
- Statement and proof: `H^n` of the balls of an `n`-plane centred on the plane (step 0(c) of the flat-limit step of Simon Ch. 8, 5.9): for `T ∈ G(N,n)`, `a ∈ T` and `r > 0`, both `T ∩ B_r(a)` and `T ∩ B°_r(a)` have `H^n`-measure `ω_n r^n`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_fli_unit_disc_mass_eventually`, `S.intcpt_fli_tangent_tilt_bound`, `S.intcpt_fli_flat_claim`

##### `S.intcpt_fli_tilt_cutoff_cc`

- Node: `root.integral_compactness-a1.flat_limit_integer-a1.tilt_cutoff-a1`; accepted candidate `d624740029bf`
- Statement and proof: Tilt cutoffs are test functions (the cutoff `χ(z) t_P(S)` of the flat-limit step of Simon Ch. 8, 5.9): for `P ∈ G(N,n)` and continuous compactly supported `χ` on `ℝ^N`, the function `(z,S) ↦ χ(z) ‖p_S - p_P‖` lies in `C_c(ℝ^N × G(N,n))` and has support in `spt χ × G(N,n)`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_fli_tilt_excess_eventually`, `S.intcpt_fli_tangent_tilt_bound`

##### `S.intcpt_fli_integral_canonical_domination`

- Node: `root.integral_compactness-a1.flat_limit_integer-a1.canonical_domination-a1`; accepted candidate `195ebaf3433f`
- Statement and proof: Canonical integer representation of an integral varifold, with mass domination (step 6 of the flat-limit integer multiplicity argument for Simon Ch. 8, 5.9): given a.e. positive integer densities of integral varifolds (hD) and the canonical tangent-plane representation (hC), an integral `W` with locally bounded first variation is `v(M, θ)` for `M = {x ∈ spt μ_W : W has a tangent plane at x}`, `θ` is a positive integer `H^n`-a.e. on `M`, and `∫ u dμ_W ≤ ∫_{M ∩ K} u θ dH^n` for Borel `u ≥ 0` vanishing off a compact `K ⊆ U`.
- Calls: — (no accepted declaration; library only)
- Called by: `S.intcpt_fli_good_mass_estimate`

##### `S.intcpt_fli_weight_compact_eventually_lt`

- Node: `root.integral_compactness-a1.flat_limit_integer-a1.compact_mass_eventually-a1`; accepted candidate `e693f2499cbf`
- Statement and proof: Mass bounds on compact sets under flat convergence (Simon Ch. 8, proof of 5.9, step 0(a), pp. 218–219): if `θ₀ > 0` and `∫ f dW_k → θ₀ ∫ f dv(P)` for every `f ∈ C_c(ℝ^N × G(N,n))` with `spt f ⊆ B°_5(0) × G(N,n)`, then `μ_{W_k}(K) < c` for all large `k` whenever `K ⊆ O ⊆ B°_5(0)` with `K` compact, `O` open and `θ₀ H^n(P ∩ O) < c`.
- Calls: `S.intcpt_fli_weight_integral_tendsto`
- Called by: `S.intcpt_fli_unit_disc_mass_eventually`, `S.intcpt_fli_flat_claim`

##### `S.intcpt_fli_unit_disc_mass_eventually`

- Node: `root.integral_compactness-a1.flat_limit_integer-a1.unit_disc_mass-a1`; accepted candidate `5c275791b69d`
- Statement and proof: Uniform eventual mass bound on the unit disc of `P` (step 4(iv) of the flat-limit argument in the proof of Simon Ch. 8, 5.9, p. 219): if `W_k → θ₀ v(P)` as Radon measures on `Gₙ(B°_5(0))`, then for each `η > 0` and all large `k`, `μ_{W_k}(B_1(a)) ≤ (θ₀ + η) ω_n` for every `a ∈ P` with `|a| ≤ 1`. The compact disc `P ∩ B_1(0)` is covered by finitely many balls `B°_{η'}(a_l)`, and the eventual compact-set mass bound is applied at each centre.
- Calls: `S.intcpt_fli_plane_ball_measure`, `S.intcpt_fli_weight_compact_eventually_lt`
- Called by: `S.intcpt_fli_flat_claim`

##### `S.intcpt_fli_tilt_excess_eventually`

- Node: `root.integral_compactness-a1.flat_limit_integer-a1.tilt_excess_eventually-a1`; accepted candidate `ce0f9af0546d`
- Statement and proof: **The tilt excess of a sequence converging to a plane tends to zero** (step 4(iii) of the proof that a flat limit of integral varifolds has integer multiplicity, used for Simon Ch. 8, 5.9). If `∫ f dW_k → θ₀ ∫ f dv(P)` for every `f ∈ C_c` with `tsupport f ⊆ B°_5(0) × G(N,n)`, then `∫_{B°_3(0) × G(N,n)} ‖p_S - p_P‖ dW_k(z,S) < η` for all large `k`: test the convergence with `f(z,S) = χ(z) ‖p_S - p_P‖`, where the cutoff `χ` is `1` on `B_3(0)` and `0` off `B°_4(0)`; its `v(P)`-integral vanishes because `‖p_P - p_P‖ = 0`.
- Calls: `S.intcpt_fli_tilt_cutoff_cc`
- Called by: `S.intcpt_fli_flat_claim`

##### `S.intcpt_fli_tangent_tilt_bound`

- Node: `root.integral_compactness-a1.flat_limit_integer-a1.tangent_tilt_bound-a1`; accepted candidate `59d6a09d1466`
- Statement and proof: Tangent planes at points of small tilt excess are close to `P` (Simon Ch. 8, proof of 5.9, pp. 218–221: step 7 of the proof that flat limits of integral varifolds have integer multiplicity, at points satisfying the tilt bound (2) of the proof of 5.10, p. 221; child `tangent_tilt_bound` of `flat_limit_integer`). If `W` has tangent plane `T` with multiplicity `θ ≥ 1` at `y` and `∫_{Gₙ(B_ρ(y))} ‖p_S - p_P‖ dW(z,S) ≤ ε ρ^n` for `0 < ρ < 1`, then `‖p_T - p_P‖ ≤ ε / ω_n`: testing the tangent-plane convergence against `χ_κ(z) ‖p_S - p_P‖` (`tilt_cutoff`), with a cutoff `χ_κ = 1` on `B_κ(0)` and `χ_κ = 0` off `B°_1(0)`, gives `θ ω_n κ^n ‖p_T - p_P‖ ≤ ε` (`plane_ball_measure`), and then `κ ↑ 1`.
- Calls: `S.intcpt_fli_plane_ball_measure`, `S.intcpt_fli_tilt_cutoff_cc`
- Called by: `S.intcpt_fli_good_mass_estimate`

##### `S.intcpt_fli_good_mass_estimate`

- Node: `root.integral_compactness-a1.flat_limit_integer-a1.good_mass_estimate-a1`; accepted candidate `fcc03e815f56`
- Statement and proof: **Mass over the good flat points** (Simon Ch. 8, 5.9, integrality of flat limits, pp. 218–219, with Allard's lemma 5.10; child `good_mass_estimate` of `flat_limit_integer`). Let `W` be an integral `n`-varifold on `U ⊇ B°_3(0)` with locally bounded first variation, `μ_W(B°_3(0)) ≤ Λ`, `‖δW‖(B°_3(0)) < ε²`, tilt excess `∫_{B°_3(0) × G(N,n)} ‖p_S - p_P‖ dW < ε²` and `μ_W(B_1(a)) ≤ m ω_n` for `a ∈ P`, `|a| < 1`, where `(1 + δ) m + δ < k₀ + 1`. Then every Borel `g ≤ 1` with `g ≤ φ ∘ p_P` and `g = 0` off `{|p_P y| < 1, |y - p_P y| < ε}` satisfies `∫ g dμ_W ≤ c₀ ε + (1 + (4ε/ω_n)²)^{n/2} k₀ ∫_P φ dH^n`. The bad set of Allard's lemma (a) has `μ_W`-measure `≤ c₀ ε`. Off it `μ_W ≤ θ H^n ⌞ M` (`intcpt_fli_integral_canonical_domination`); the good points of `M` with integer multiplicity lie on `4ε/ω_n`-Lipschitz graphs over `P` (`intcpt_fli_tangent_tilt_bound` and the tangent-graph cover), and by Allard's lemma (b) every fibre of `p_P` meets them in a finite set with `θ`-sum `≤ k₀`, so the Lipschitz graph fibre bound gives the estimate.
- Calls: `S.intcpt_fli_integral_canonical_domination`, `S.intcpt_fli_tangent_tilt_bound`
- Called by: `S.intcpt_fli_flat_claim`

##### `S.intcpt_fli_flat_claim`

- Node: `root.integral_compactness-a1.flat_limit_integer-a1.flat_claim-a1`; accepted candidate `56b167ebe474`
- Statement and proof: **Simon Ch. 8, proof of 5.9: the flat-limit claim** (child `flat_claim` of `flat_limit_integer`). Let integral `n`-varifolds `W_k` on `B°_5(0)` with `‖δW_k‖(B°_5(0)) → 0` converge to `θ₀ v(P)`, `θ₀ > 0`. Then there are `δ̄ > 0`, `c₀ ≥ 0` and `I₀ > 0` with `θ₀ I₀ ≤ c₀ δ⁴ + (1 + (4δ⁴/ω_n)²)^{n/2} k₀ I₀` whenever `0 < δ ≤ δ̄`, `4δ⁴ ≤ ω_n` and `(1 + δ)(θ₀ + δ) + δ < k₀ + 1`. Take `I₀ = ∫_P ψ dH^n` for a radial profile `ψ` on `P`. For large `k`, the good-mass estimate `intcpt_fli_good_mass_estimate` (with `ε = δ⁴`, `m = θ₀ + δ`) bounds `∫ ψ(p_P y) χ(|y - p_P y|) dμ_{W_k}(y)` by the right-hand side, and this integral tends to `θ₀ I₀` by `intcpt_fli_weight_integral_tendsto`.
- Calls: `S.intcpt_fli_good_mass_estimate`, `S.intcpt_fli_plane_ball_measure`, `S.intcpt_fli_tilt_excess_eventually`, `S.intcpt_fli_unit_disc_mass_eventually`, `S.intcpt_fli_weight_compact_eventually_lt`, `S.intcpt_fli_weight_integral_tendsto`
- Called by: `S.intcpt_flat_limit_integer_multiplicity`

##### `S.intcpt_fli_dim_zero_integer`

- Node: `root.integral_compactness-a1.flat_limit_integer-a1.dim_zero-a1`; accepted candidate `655060246db7`
- Statement and proof: **Dimension `0`: flat limits of integral `0`-varifolds have integer multiplicity** (child `dim_zero` of `flat_limit_integer`, step 1 of its proof; Simon Ch. 8, proof of 5.9). For `n = 0` the plane `P` is `{0}` and `H^0` is counting measure, so `∫_P g dH^0 = g(0)`. Each `W_k = v(M, θ)` is carried by a countable set `M` with `θ ∈ ℕ` on `M`, so `μ_{W_k}(B_{1/2}(0)) ∈ ℕ ∪ {∞}`. Cut-offs `g₁ ≤ 1_{B_{1/2}(0)} ≤ g₂` with `g₁(0) = g₂(0) = 1` and `weight_tendsto` give `μ_{W_k}(B_{1/2}(0)) → θ₀`; as `ℕ` is closed in `ℝ`, `θ₀ ∈ ℕ`.
- Calls: `S.intcpt_fli_weight_integral_tendsto`
- Called by: `S.intcpt_flat_limit_integer_multiplicity`


## Appendix B. SimonGMT constants used directly by `GMT.Ch08.Submission`

Package `simongmt` at `2b3663083f3fe399b6296fb8eaee52169170e197` (source files under `Poincare/SimonGMT/`). Obtained from the compiled environment, not from a text search. For each constant of module `GMT.Ch08.Submission`, the query read the type and value (`ConstantInfo.value? (allowOpaque := true)`) and kept the constants whose module is under `Poincare`. This gives 174 distinct constants in 23 modules, listed by module. The users are the top-level `GMT.Ch08.Submission` declarations, or `main_theorem`; auxiliary `._proof_`/`.match_` constants are attributed to their parent. Constants named `X.eq_1` are definitional unfolding lemmas of `X`. The contract itself also uses the definitions `Varifold`, `Grassmannian`, `Euclidean`, etc.

**`Poincare.SimonGMT.Chapter01.Densities`** (`Poincare/SimonGMT/Chapter01/Densities.lean`)

- `Chapter01.dimensionalDensityQuotient` — used by `S.frt_hausdorff_null_of_weight_null`, `S.intcpt_canon_hausdorff_null_of_weight_null`
- `Chapter01.dimensionalDensityQuotient.eq_1` — used by `S.frt_hausdorff_null_of_weight_null`, `S.intcpt_canon_hausdorff_null_of_weight_null`
- `Chapter01.dimensionalUpperDensity` — used by `S.frt_hausdorff_null_of_weight_null`, `S.intcpt_canon_hausdorff_null_of_weight_null`

**`Poincare.SimonGMT.Chapter01.DensityComparison`** (`Poincare/SimonGMT/Chapter01/DensityComparison.lean`)

- `Chapter01.mul_simonHausdorff_le_of_le_dimensionalUpperDensity` — used by `S.frt_hausdorff_null_of_weight_null`, `S.intcpt_canon_hausdorff_null_of_weight_null`

**`Poincare.SimonGMT.Chapter01.EuclideanHausdorffUpper`** (`Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`)

- `Chapter01.volume_euclidean_ball_eq` — used by `S.intcpt_canon_hausdorff_null_of_weight_null`

**`Poincare.SimonGMT.Chapter01.Hausdorff`** (`Poincare/SimonGMT/Chapter01/Hausdorff.lean`)

- `Chapter01.realUnitBallVolume` — used by `S.frt_hausdorff_null_of_weight_null`, `S.intcpt_canon_hausdorff_null_of_weight_null`
- `Chapter01.realUnitBallVolume_eq` — used by `S.frt_hausdorff_null_of_weight_null`
- `Chapter01.realUnitBallVolume_zero` — used by `S.intcpt_canon_hausdorff_null_of_weight_null`
- `Chapter01.simonHausdorffMeasureReal` — used by `S.frt_hausdorff_null_of_weight_null`, `S.intcpt_canon_hausdorff_null_of_weight_null`
- `Chapter01.simonHausdorffMeasureReal_toOuterMeasure` — used by `S.frt_hausdorff_null_of_weight_null`, `S.intcpt_canon_hausdorff_null_of_weight_null`
- `Chapter01.simonHausdorffOuterMeasureReal` — used by `S.frt_hausdorff_null_of_weight_null`, `S.intcpt_canon_hausdorff_null_of_weight_null`

**`Poincare.SimonGMT.Chapter02.AreaLiteral`** (`Poincare/SimonGMT/Chapter02/AreaLiteral.lean`)

- `Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure` — used by `S.frt_hausdorff_null_of_weight_null`, `S.intcpt_canon_hausdorff_null_of_weight_null`

**`Poincare.SimonGMT.Chapter02.Lipschitz`** (`Poincare/SimonGMT/Chapter02/Lipschitz.lean`)

- `Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn` — used by `S.frt_lipschitz_graph_hausdorff_compare`, `S.stationary_constancy_tangentGraph_measure`

**`Poincare.SimonGMT.Chapter02.Submanifold`** (`Poincare/SimonGMT/Chapter02/Submanifold.lean`)

- `Chapter02.IsProperOnInto` — used by `S.allard_tc_scf_subspace_submanifold`, `S.stationary_constancy_tangentGraph_measure`
- `Chapter02.IsSimonLocalRepresentation` — used by `S.allard_tc_scf_subspace_submanifold`, `S.simon_chart_classicalTangentSpace_eq_range`, `S.stationary_constancy_tangentGraph_measure`
- `Chapter02.IsSimonLocalRepresentation.contDiffOn` — used by `S.simon_chart_classicalTangentSpace_eq_range`, `S.stationary_constancy_tangentGraph_measure`
- `Chapter02.IsSimonLocalRepresentation.image_eq` — used by `S.simon_chart_classicalTangentSpace_eq_range`, `S.stationary_constancy_tangentGraph_measure`
- `Chapter02.IsSimonLocalRepresentation.injOn` — used by `S.simon_chart_classicalTangentSpace_eq_range`, `S.stationary_constancy_tangentGraph_measure`
- `Chapter02.IsSimonLocalRepresentation.injective_fderiv` — used by `S.simon_chart_classicalTangentSpace_eq_range`, `S.stationary_constancy_tangentGraph_measure`
- `Chapter02.IsSimonLocalRepresentation.isCompact_source_inter_preimage` — used by `S.simon_chart_classicalTangentSpace_eq_range`
- `Chapter02.IsSimonLocalRepresentation.isOpen_source` — used by `S.simon_chart_classicalTangentSpace_eq_range`, `S.stationary_constancy_tangentGraph_measure`
- `Chapter02.IsSimonLocalRepresentation.isOpen_target` — used by `S.simon_chart_classicalTangentSpace_eq_range`
- `Chapter02.IsSimonSubmanifold` — used by `S.allard_tc_scf_subspace_submanifold`, `S.constancy_theorem`, `S.stationary_constancy_tangentGraph_measure`
- `Chapter02.IsSimonSubmanifold.exists_localRepresentation` — used by `S.stationary_constancy_tangentGraph_measure`

**`Poincare.SimonGMT.Chapter03.Rectifiable`** (`Poincare/SimonGMT/Chapter03/Rectifiable.lean`)

- `Chapter03.CountablyRectifiable` — used by `S.allard_tc_cone_rescaling_invariance`, `S.allard_tc_tangent_point_representation`, `S.allard_tc_tpr_rectifiable_sigmaFinite`, `S.first_rectifiability_theorem`, `S.frt_countablyRectifiable_of_graph_cover`, `S.intcpt_canonical_tangent_representation`, … (14 declarations)
- `Chapter03.CountablyRectifiable.mono` — used by `S.frt_countablyRectifiable_of_graph_cover`, `S.intcpt_rescaled_restriction_integral`
- `Chapter03.HasWeightedApproximateTangentSpaceAt` — used by `S.allard_tc_cone_rescaling_invariance`, `S.allard_tc_tangent_point_representation`, `S.allard_tc_tpr_weighted_approx_tangent_iff`, `S.first_rectifiability_theorem`, `S.frt_weighted_approx_tangent`, `S.intcpt_canonical_tangent_representation`, … (18 declarations)
- `Chapter03.HasWeightedApproximateTangentSpaceAt.unique` — used by `S.allard_tc_tpr_weighted_approx_tangent_iff`, `S.frt_weighted_approx_tangent`
- `Chapter03.blowUpMap` — used by `S.allard_tc_tpr_blowup_setIntegral`, `S.allard_tc_tpr_weighted_approx_tangent_iff`, `S.frt_wat_setIntegral_blowUpMap_image`, `S.frt_weighted_approx_tangent`, `S.intcpt_id_tpd_ball_mass_lower`, `S.intcpt_id_tpd_ball_mass_upper`, … (10 declarations)
- `Chapter03.countablyRectifiable_range` — used by `S.frt_countablyRectifiable_of_graph_cover`
- `Chapter03.countablyRectifiable_sUnion` — used by `S.frt_countablyRectifiable_of_graph_cover`
- `Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule` — used by `S.allard_tc_tpd_plane_eq_of_integral_eq`, `S.frt_tangent_plane_unique`
- `Chapter03.support_euclideanHausdorffMeasure_restrict_submodule` — used by `S.allard_tc_tpd_plane_eq_of_integral_eq`, `S.frt_tangent_plane_unique`

**`Poincare.SimonGMT.Chapter04.FirstVariation`** (`Poincare/SimonGMT/Chapter04/FirstVariation.lean`)

- `Chapter04.RectifiableVarifold.contDiff_monotonicityCutoff` — used by `S.monotonicity_formula_8_3_3`
- `Chapter04.RectifiableVarifold.monotonicityCutoff` — used by `S.monotonicity_formula_8_3_3`
- `Chapter04.RectifiableVarifold.monotonicityCutoff_antitone` — used by `S.monotonicity_formula_8_3_3`
- `Chapter04.RectifiableVarifold.monotonicityCutoff_cutoff` — used by `S.monotonicity_formula_8_3_3`
- `Chapter04.RectifiableVarifold.monotonicityCutoff_one` — used by `S.monotonicity_formula_8_3_3`
- `Chapter04.RectifiableVarifold.scaledRadialCutoff` — used by `S.monotonicity_formula_8_3_3`
- `Chapter04.RectifiableVarifold.scaledRadialCutoffDeriv` — used by `S.monotonicity_formula_8_3_3`
- `Chapter04.RectifiableVarifold.scaledRadialCutoffDeriv_nonneg` — used by `S.monotonicity_formula_8_3_3`

**`Poincare.SimonGMT.Chapter08.DeformationIntegral`** (`Poincare/SimonGMT/Chapter08/DeformationIntegral.lean`)

- `Chapter08.Varifold.hasDerivAt_pushforwardMeasure_cylinder_family_of_velocity` — used by `S.first_variation_theorems`

**`Poincare.SimonGMT.Chapter08.FirstVariation`** (`Poincare/SimonGMT/Chapter08/FirstVariation.lean`)

- `Chapter08.Varifold.hasDerivAt_tangentialJacobianReal_id_add_smul` — used by `S.stationary_constancy_tangentGraph_measure`

**`Poincare.SimonGMT.Chapter08.FirstVariationBounds`** (`Poincare/SimonGMT/Chapter08/FirstVariationBounds.lean`)

- `Chapter08.Varifold.TestVectorField.scale` — used by `S.varifold_tangents_rdb_firstVariation_le_variationMeasure`
- `Chapter08.Varifold.TestVectorField.tsupport_scale_subset` — used by `S.varifold_tangents_rdb_firstVariation_le_variationMeasure`
- `Chapter08.Varifold.firstVariationNormOn_le_of_polarRepresentation` — used by `S.intcpt_diag_blowup_variation_bound`
- `Chapter08.Varifold.le_firstVariationNormOn` — used by `S.intcpt_diag_blowup_variation_bound`, `S.varifold_tangents_rdb_firstVariation_le_variationMeasure`

**`Poincare.SimonGMT.Chapter08.FirstVariationDecomposition`** (`Poincare/SimonGMT/Chapter08/FirstVariationDecomposition.lean`)

- `Chapter08.Varifold.symmetricGeneralizedBoundaryMeasure` — used by `S.first_variation_theorems`
- `Chapter08.Varifold.symmetricGeneralizedBoundaryMeasure.eq_1` — used by `S.first_variation_theorems`
- `Chapter08.Varifold.symmetricGeneralizedBoundarySet` — used by `S.first_variation_theorems`
- `Chapter08.Varifold.symmetricGeneralizedMeanCurvature` — used by `S.first_variation_theorems`
- `Chapter08.Varifold.symmetricGeneralizedMeanCurvature.eq_1` — used by `S.first_variation_theorems`

**`Poincare.SimonGMT.Chapter08.FirstVariationDensity`** (`Poincare/SimonGMT/Chapter08/FirstVariationDensity.lean`)

- `Chapter08.Varifold.ae_tendsto_firstVariationDensity_of_domainMeasure` — used by `S.plane_disint_slice_density`
- `Chapter08.Varifold.symmetricFirstVariationDensity` — used by `S.dea_ae_variationMeasure_ball_bound`, `S.first_variation_theorems`

**`Poincare.SimonGMT.Chapter08.FirstVariationRiesz`** (`Poincare/SimonGMT/Chapter08/FirstVariationRiesz.lean`)

- `Chapter08.Varifold.ae_firstVariationPolarField_norm_one` — used by `S.first_variation_theorems`
- `Chapter08.Varifold.firstVariationPolarField` — used by `S.first_variation_theorems`, `S.intcpt_allard_first_variation_le_sup_mul`, `S.intcpt_diag_blowup_variation_bound`, `S.mono833_radial_first_variation_bound`
- `Chapter08.Varifold.firstVariationRieszMeasure` — used by `S.dea_ae_variationMeasure_ball_bound`, `S.first_variation_theorems`, `S.intcpt_allard_first_variation_le_sup_mul`, `S.intcpt_diag_blowup_variation_bound`, `S.mono833_radial_first_variation_bound`, `S.variationMeasure_le_liminf_of_radonConverges`, … (8 declarations)
- `Chapter08.Varifold.firstVariationRieszMeasure_eq_norm` — used by `S.intcpt_diag_blowup_variation_bound`, `S.variationMeasure_le_liminf_of_radonConverges`, `S.varifold_tangents_dlb_restricted_firstVariation_control`, `S.varifold_tangents_rdb_firstVariation_le_variationMeasure`
- `Chapter08.Varifold.firstVariationRiesz_boundary_spec` — used by `S.first_variation_theorems`
- `Chapter08.Varifold.firstVariationRiesz_integrable_meanCurvature_and_boundary` — used by `S.first_variation_theorems`
- `Chapter08.Varifold.firstVariationRiesz_symmetricDensity_spec` — used by `S.dea_ae_variationMeasure_ball_bound`, `S.first_variation_theorems`
- `Chapter08.Varifold.firstVariation_eq_meanCurvature_add_boundary_of_locallyBounded` — used by `S.first_variation_theorems`
- `Chapter08.Varifold.isFirstVariationMeasure_riesz` — used by `S.first_variation_theorems`
- `Chapter08.Varifold.isFirstVariationPolarRepresentation_riesz` — used by `S.first_variation_theorems`, `S.intcpt_allard_first_variation_le_sup_mul`, `S.intcpt_diag_blowup_variation_bound`, `S.mono833_radial_first_variation_bound`
- `Chapter08.Varifold.measurable_firstVariationPolarField` — used by `S.first_variation_theorems`

**`Poincare.SimonGMT.Chapter08.RadialCutoffDifferentiation`** (`Poincare/SimonGMT/Chapter08/RadialCutoffDifferentiation.lean`)

- `Chapter08.Varifold.hasDerivAt_integral_radialCutoff_of_radius` — used by `S.monotonicity_formula_8_3_3`

**`Poincare.SimonGMT.Chapter08.RadialFirstVariation`** (`Poincare/SimonGMT/Chapter08/RadialFirstVariation.lean`)

- `Chapter08.Grassmannian.measurable_radialNormalSq` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Grassmannian.norm_normalProject_radial_sq` — used by `S.monotonicity_formula_8_3_3`, `S.stationary_monotonicity_identity_8_3_4`
- `Chapter08.Grassmannian.normalProject` — used by `S.monotonicity_formula_8_3_3`, `S.stationary_monotonicity_identity_8_3_4`, `S.varifold_tangent_theorems`
- `Chapter08.Grassmannian.normalProject._proof_1` — used by `S.monotonicity_formula_8_3_3`, `S.stationary_monotonicity_identity_8_3_4`
- `Chapter08.Grassmannian.normalProject_eq_sub` — used by `S.monotonicity_formula_8_3_3`, `S.stationary_monotonicity_identity_8_3_4`, `S.varifold_tangent_theorems`
- `Chapter08.Grassmannian.radialNormalSq` — used by `S.monotonicity_formula_8_3_3`, `S.stationary_monotonicity_identity_8_3_4`
- `Chapter08.Grassmannian.radialNormalSq_le_one` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Grassmannian.radialNormalSq_nonneg` — used by `S.monotonicity_formula_8_3_3`

**`Poincare.SimonGMT.Chapter08.StationaryCutoff`** (`Poincare/SimonGMT/Chapter08/StationaryCutoff.lean`)

- `Chapter08.Varifold.StationaryOn` — used by `S.stationary_monotonicity_identity_8_3_4`
- `Chapter08.Varifold.cutoffMass` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Varifold.cutoffMass.eq_1` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Varifold.measurable_truncatedRadialDefect` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Varifold.norm_truncatedRadialDefect_le` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Varifold.scaledRadialCutoffDeriv_defect_bounds` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Varifold.tendsto_cutoffMass` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Varifold.tendsto_integral_radialCutoff` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Varifold.truncatedRadialDefect` — used by `S.monotonicity_formula_8_3_3`

**`Poincare.SimonGMT.Chapter08.StationaryMonotonicity`** (`Poincare/SimonGMT/Chapter08/StationaryMonotonicity.lean`)

- `Chapter08.Varifold.StationaryOn.stationaryMonotonicity` — used by `S.stationary_monotonicity_identity_8_3_4`
- `Chapter08.Varifold.annularMonotonicityDefect` — used by `S.monotonicity_formula_8_3_3`, `S.stationary_monotonicity_identity_8_3_4`
- `Chapter08.Varifold.integrableOn_radialDefect_annulus` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Varifold.integrableOn_truncatedRadialDefect` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Varifold.normalizedBallMass` — used by `S.monotonicity_formula_8_3_3`, `S.stationary_monotonicity_identity_8_3_4`, `S.varifold_tangent_theorems`
- `Chapter08.Varifold.normalizedBallMass.eq_1` — used by `S.monotonicity_formula_8_3_3`, `S.stationary_monotonicity_identity_8_3_4`, `S.varifold_tangent_theorems`
- `Chapter08.Varifold.normalizedBallMass_ne_top` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Varifold.ofReal_normalizedBallMass_real` — used by `S.monotonicity_formula_8_3_3`

**`Poincare.SimonGMT.Chapter08.TangentRadialRigidity`** (`Poincare/SimonGMT/Chapter08/TangentRadialRigidity.lean`)

- `Chapter08.Varifold.Stationary.ae_normalProject_eq_zero_of_constant_mass_ratio` — used by `S.varifold_tangent_theorems`

**`Poincare.SimonGMT.Chapter08.Varifold`** (`Poincare/SimonGMT/Chapter08/Varifold.lean`)

- `Chapter08.Euclidean` — used by `S.ae_of_forall_relCompactOpen_null_exceptional`, `S.allard_rectifiability_and_tangent_cones`, `S.allard_tc_cone_rescaling_invariance`, `S.allard_tc_cone_rescaling_invariance.match_1_10`, `S.allard_tc_cone_rescaling_invariance.match_1_12`, `S.allard_tc_cone_rescaling_invariance.match_1_14`, … (249 declarations)
- `Chapter08.Grassmannian` — used by `S.allard_tc_cone_rescaling_invariance`, `S.allard_tc_cone_rescaling_invariance.match_1_12`, `S.allard_tc_cone_rescaling_invariance.match_1_14`, `S.allard_tc_cone_rescaling_invariance.match_1_16`, `S.allard_tc_cone_rescaling_invariance.match_1_18`, `S.allard_tc_cone_rescaling_invariance.match_1_4`, … (149 declarations)
- `Chapter08.Grassmannian.coordinateBasis` — used by `S.allard_tc_scf_zero_defect_mem_plane`, `S.allard_tc_tpd_plane_eq_of_integral_eq`, `S.frt_tangent_plane_unique`, `S.frt_tangent_points_flat_graph_cover`, `S.intcpt_allard_radial_field_divergence`, `S.stationary_constancy_tangentGraph_measure`, … (7 declarations)
- `Chapter08.Grassmannian.finrank_plane` — used by `S.allard_tc_fbl_plane_ball_measure`, `S.allard_tc_scf_constancy_plane`, `S.allard_tc_scf_plane_ball_mass`, `S.allard_tc_tpd_plane_eq_of_integral_eq`, `S.allard_tc_tpr_weighted_approx_tangent_iff`, `S.constancy_theorem`, … (17 declarations)
- `Chapter08.Grassmannian.instCompactSpace` — used by `S.allard_tc_fbl_nonneg_limit`, `S.allard_tc_fbl_rescaled_sandwich`, `S.allard_tc_flat_blowup_ball_limits`, `S.allard_tc_stationary_cone_flat`, `S.allard_tc_tpr_weighted_approx_tangent_iff`, `S.frt_varifold_eq_tangent_graph_measure`, … (25 declarations)
- `Chapter08.Grassmannian.instSecondCountableTopology` — used by `S.allard_tc_fbl_nonneg_limit`, `S.allard_tc_fbl_rescaled_sandwich`, `S.allard_tc_flat_blowup_ball_limits`, `S.allard_tc_scf_zero_defect_mem_plane`, `S.allard_tc_stationary_cone_flat`, `S.allard_tc_tpr_weighted_approx_tangent_iff`, … (34 declarations)
- `Chapter08.Grassmannian.isClosed_projectionSet` — used by `S.frt_vgm_mps_limit_selection`
- `Chapter08.Grassmannian.ofSubmodule` — used by `S.allard_tc_scf_constancy_plane`, `S.allard_tc_tpr_weighted_approx_tangent_iff`, `S.constancy_theorem`, `S.frt_weighted_approx_tangent`, `S.stationary_constancy_tangentGraph_measure`
- `Chapter08.Grassmannian.ofSubmodule.congr_simp` — used by `S.frt_weighted_approx_tangent`
- `Chapter08.Grassmannian.ofSubmodule_plane` — used by `S.allard_tc_scf_constancy_plane`, `S.allard_tc_tpr_weighted_approx_tangent_iff`, `S.constancy_theorem`, `S.frt_weighted_approx_tangent`, `S.stationary_constancy_tangentGraph_measure`
- `Chapter08.Grassmannian.plane` — used by `S.allard_tc_cone_rescaling_invariance`, `S.allard_tc_fbl_nonneg_limit`, `S.allard_tc_fbl_plane_ball_measure`, `S.allard_tc_fbl_plane_cutoff_limits`, `S.allard_tc_scf_constancy_plane`, `S.allard_tc_scf_plane_ball_mass`, … (58 declarations)
- `Chapter08.Grassmannian.project` — used by `S.allard_tc_scf_monotonicity_identity`, `S.allard_tc_scf_zero_defect_mem_plane`, `S.first_rectifiability_theorem`, `S.frt_countablyRectifiable_of_graph_cover`, `S.frt_graph_piece_density_bounds`, `S.frt_hausdorff_density_one_of_flat_covers`, … (43 declarations)
- `Chapter08.Grassmannian.project_project` — used by `S.frt_countablyRectifiable_of_graph_cover`, `S.frt_lipschitz_graph_hausdorff_compare`, `S.intcpt_allard_cm_cylinder_weight`, `S.intcpt_allard_fdsb_density_cylinder_bound`, `S.intcpt_allard_wrm_first_variation_lower_bound`, `S.intcpt_graph_hausdorff_le_projection`, … (8 declarations)
- `Chapter08.Grassmannian.projectionLinearMap` — used by `S.allard_tc_scf_zero_defect_mem_plane`, `S.allard_tc_tpd_plane_eq_of_integral_eq`, `S.frt_countablyRectifiable_of_graph_cover`, `S.frt_graph_piece_density_bounds`, `S.frt_lipschitz_graph_hausdorff_compare`, `S.frt_tangent_plane_unique`, … (34 declarations)
- `Chapter08.Grassmannian.projectionLinearMap_apply_of_mem` — used by `S.intcpt_fli_flat_claim`, `S.stationary_constancy_tangentGraph_measure`, `S.tgc_tangent_cone_weight_decay`
- `Chapter08.Grassmannian.projectionLinearMap_comp_self` — used by `S.allard_tc_tpd_plane_eq_of_integral_eq`, `S.frt_tangent_plane_unique`, `S.stationary_constancy_tangentGraph_measure`
- `Chapter08.Grassmannian.projectionLinearMap_isSymmetric` — used by `S.allard_tc_tpd_plane_eq_of_integral_eq`, `S.frt_countablyRectifiable_of_graph_cover`, `S.frt_lipschitz_graph_hausdorff_compare`, `S.frt_tangent_plane_unique`, `S.intcpt_allard_cm_cylinder_weight`, `S.intcpt_allard_fdsb_density_cylinder_bound`, … (11 declarations)
- `Chapter08.Grassmannian.toMatrix_projectionLinearMap` — used by `S.allard_tc_tpd_plane_eq_of_integral_eq`, `S.frt_tangent_plane_unique`, `S.intcpt_allard_radial_field_divergence`, `S.stationary_constancy_tangentGraph_measure`, `S.varifold_tangents_rh_radial_euler_identity`
- `Chapter08.Grassmannian.trace_eq` — used by `S.intcpt_allard_radial_field_divergence`, `S.varifold_tangents_rh_radial_euler_identity`
- `Chapter08.Varifold` — used by `S.allard_rectifiability_and_tangent_cones`, `S.allard_tc_cone_rescaling_invariance`, `S.allard_tc_cone_rescaling_invariance.match_1_12`, `S.allard_tc_cone_rescaling_invariance.match_1_14`, `S.allard_tc_cone_rescaling_invariance.match_1_16`, `S.allard_tc_cone_rescaling_invariance.match_1_18`, … (123 declarations)
- `Chapter08.Varifold.HasLocallyBoundedFirstVariation` — used by `S.allard_rectifiability_and_tangent_cones`, `S.allard_tc_density_blowup_decay`, `S.allard_tc_rectifiability`, `S.allard_tc_tangent_cones_rectifiable`, `S.compactness_theorem`, `S.dea_ae_variationMeasure_ball_bound`, … (36 declarations)
- `Chapter08.Varifold.IsFirstVariationMeasure` — used by `S.allard_tc_rectifiability`, `S.first_variation_theorems`
- `Chapter08.Varifold.IsFirstVariationPolarRepresentation` — used by `S.intcpt_allard_first_variation_le_sup_mul`, `S.mono833_radial_first_variation_bound`
- `Chapter08.Varifold.IsFirstVariationPolarRepresentation._proof_1` — used by `S.first_variation_theorems`, `S.intcpt_allard_first_variation_le_sup_mul`, `S.mono833_radial_first_variation_bound`
- `Chapter08.Varifold.IsFirstVariationPolarRepresentation._proof_2` — used by `S.first_variation_theorems`, `S.intcpt_allard_first_variation_le_sup_mul`, `S.mono833_radial_first_variation_bound`
- `Chapter08.Varifold.Stationary` — used by `S.allard_tc_rectifiability`, `S.allard_tc_scf_constancy_plane`, `S.allard_tc_scf_monotonicity_identity`, `S.allard_tc_stationary_cone_flat`, `S.allard_tc_tangent_cones_rectifiable`, `S.constancy_theorem`, … (11 declarations)
- `Chapter08.Varifold.Stationary.hasLocallyBoundedFirstVariation` — used by `S.allard_tc_tangent_cones_rectifiable`
- `Chapter08.Varifold.TestVectorField` — used by `S.allard_tc_rectifiability`, `S.allard_tc_scf_monotonicity_identity`, `S.first_variation_theorems`, `S.intcpt_allard_first_variation_le_sup_mul`, `S.intcpt_diag_blowup_variation_bound`, `S.mono833_radial_first_variation_bound`, … (11 declarations)
- `Chapter08.Varifold.TestVectorField.UnitSupportedIn` — used by `S.intcpt_diag_blowup_variation_bound`, `S.varifold_tangents_dlb_restricted_firstVariation_control`, `S.varifold_tangents_rdb_firstVariation_le_variationMeasure`
- `Chapter08.Varifold.TestVectorField.compactSupport` — used by `S.intcpt_diag_blowup_variation_bound`, `S.stationary_constancy_tangentGraph_measure`, `S.varifold_tangents_dlb_restricted_firstVariation_control`, `S.varifold_tangents_limit_stationary`
- `Chapter08.Varifold.TestVectorField.contDiff` — used by `S.intcpt_diag_blowup_variation_bound`, `S.stationary_constancy_tangentGraph_measure`, `S.varifold_tangents_dlb_restricted_firstVariation_control`, `S.varifold_tangents_limit_stationary`
- `Chapter08.Varifold.TestVectorField.mk` — used by `S.intcpt_allard_first_variation_le_sup_mul`, `S.intcpt_diag_blowup_variation_bound`, `S.mono833_radial_first_variation_bound`, `S.stationary_constancy_tangentGraph_measure`, `S.varifold_tangents_rdb_firstVariation_le_variationMeasure`, `S.varifold_tangents_rh_radial_euler_identity`
- `Chapter08.Varifold.TestVectorField.support_subset` — used by `S.intcpt_diag_blowup_variation_bound`, `S.stationary_constancy_tangentGraph_measure`, `S.varifold_tangents_dlb_restricted_firstVariation_control`
- `Chapter08.Varifold.TestVectorField.toFun` — used by `S.allard_tc_rectifiability`, `S.allard_tc_scf_monotonicity_identity`, `S.first_variation_theorems`, `S.intcpt_allard_first_variation_le_sup_mul`, `S.intcpt_diag_blowup_variation_bound`, `S.mono833_radial_first_variation_bound`, … (11 declarations)
- `Chapter08.Varifold.ae_mem_domain` — used by `S.constancy_theorem`
- `Chapter08.Varifold.clmToMatrix` — used by `S.intcpt_diag_blowup_variation_bound`, `S.varifold_tangents_rdb_rescaled_integral_eq`
- `Chapter08.Varifold.clmToMatrix._proof_1` — used by `S.varifold_tangents_rdb_rescaled_integral_eq`
- `Chapter08.Varifold.clmToMatrix._proof_2` — used by `S.varifold_tangents_rdb_rescaled_integral_eq`
- `Chapter08.Varifold.clmToMatrix._proof_3` — used by `S.varifold_tangents_rdb_rescaled_integral_eq`
- `Chapter08.Varifold.continuous_tangentialDivergence` — used by `S.intcpt_allard_wrm_first_variation_lower_bound`, `S.intcpt_diag_blowup_variation_bound`, `S.stationary_constancy_tangentGraph_measure`, `S.varifold_tangents_limit_stationary`, `S.varifold_tangents_rdb_rescaled_integral_eq`
- `Chapter08.Varifold.domainMeasure` — used by `S.compactness_theorem`, `S.intcpt_diag_rescaled_radon_tendsto`, `S.varifold_tangents_restricted_radon_converges`, `S.varifold_weight_integral_tendsto_of_radonConverges`
- `Chapter08.Varifold.finite_on_compact` — used by `S.allard_tc_fbl_rescaled_sandwich`, `S.allard_tc_flat_blowup_ball_limits`, `S.frt_vgm_tangent_ball_average`, `S.frt_vgm_tba_ball_cutoff_sandwich`, `S.intcpt_allard_wrm_first_variation_lower_bound`, `S.intcpt_diag_blowup_variation_bound`, … (10 declarations)
- `Chapter08.Varifold.firstVariation` — used by `S.allard_tc_rectifiability`, `S.first_variation_theorems`, `S.intcpt_allard_first_variation_le_sup_mul`, `S.intcpt_allard_weighted_radial_monotonicity`, `S.intcpt_allard_wrm_first_variation_lower_bound`, `S.intcpt_diag_blowup_variation_bound`, … (15 declarations)
- `Chapter08.Varifold.firstVariation.eq_1` — used by `S.varifold_tangents_dlb_restricted_firstVariation_control`
- `Chapter08.Varifold.firstVariationNormOn` — used by `S.intcpt_diag_blowup_variation_bound`, `S.variationMeasure_le_liminf_of_radonConverges`, `S.varifold_tangents_dlb_restricted_firstVariation_control`, `S.varifold_tangents_rdb_firstVariation_le_variationMeasure`
- `Chapter08.Varifold.firstVariation_const_smul` — used by `S.varifold_tangents_rdb_firstVariation_le_variationMeasure`
- `Chapter08.Varifold.firstVariation_zero` — used by `S.varifold_tangents_rdb_firstVariation_le_variationMeasure`
- `Chapter08.Varifold.hasCompactSupport_tangentialDivergence` — used by `S.varifold_tangents_limit_stationary`
- `Chapter08.Varifold.integrable_tangentialDivergence` — used by `S.intcpt_allard_wrm_first_variation_lower_bound`, `S.stationary_constancy_tangentGraph_measure`
- `Chapter08.Varifold.isOpen_domain` — used by `S.allard_tc_density_blowup_decay`, `S.allard_tc_fbl_nonneg_limit`, `S.allard_tc_flat_blowup_ball_limits`, `S.allard_tc_rectifiability`, `S.allard_tc_tangent_plane_density`, `S.compactness_theorem`, … (33 declarations)
- `Chapter08.Varifold.jacobian` — used by `S.intcpt_allard_radial_field_divergence`, `S.stationary_constancy_tangentGraph_measure`, `S.varifold_tangents_rdb_rescaled_integral_eq`, `S.varifold_tangents_rh_radial_euler_identity`
- `Chapter08.Varifold.jacobian_eq_toMatrix` — used by `S.intcpt_allard_radial_field_divergence`, `S.stationary_constancy_tangentGraph_measure`, `S.varifold_tangents_rh_radial_euler_identity`
- `Chapter08.Varifold.map_domainMeasure` — used by `S.compactness_theorem`, `S.intcpt_diag_rescaled_radon_tendsto`, `S.varifold_tangents_restricted_radon_converges`, `S.varifold_weight_integral_tendsto_of_radonConverges`
- `Chapter08.Varifold.measure` — used by `S.allard_tc_cone_rescaling_invariance`, `S.allard_tc_cri_rescaled_representation`, `S.allard_tc_density_blowup_decay`, `S.allard_tc_fbl_nonneg_limit`, `S.allard_tc_fbl_rescaled_sandwich`, `S.allard_tc_flat_blowup_ball_limits`, … (83 declarations)
- `Chapter08.Varifold.measure.instSigmaFinite` — used by `S.frt_vgm_measurable_plane_selection`
- `Chapter08.Varifold.mk` — used by `S.intcpt_diag_blowup_variation_bound`, `S.varifold_tangents_dlb_exists_restricted_varifold`
- `Chapter08.Varifold.ofDomainMeasure` — used by `S.varifold_radon_compactness`
- `Chapter08.Varifold.pushforwardMeasure` — used by `S.first_variation_theorems`
- `Chapter08.Varifold.support_tangentialDivergence_subset` — used by `S.intcpt_diag_blowup_variation_bound`, `S.varifold_tangents_dlb_restricted_firstVariation_control`
- `Chapter08.Varifold.supported` — used by `S.allard_tc_density_blowup_decay`, `S.allard_tc_rectifiability`, `S.dea_ae_variationMeasure_ball_bound`, `S.integral_compactness_theorem`, `S.lower_density_ge_one_ae_of_radonConverges`, `S.plane_disint_pointwise_measure`, … (8 declarations)
- `Chapter08.Varifold.tangentialDerivative` — used by `S.stationary_constancy_tangentGraph_measure`
- `Chapter08.Varifold.tangentialDivergence` — used by `S.first_variation_theorems`, `S.intcpt_allard_radial_field_divergence`, `S.intcpt_allard_wrm_first_variation_lower_bound`, `S.intcpt_diag_blowup_variation_bound`, `S.stationary_constancy_tangentGraph_measure`, `S.varifold_tangents_dlb_restricted_firstVariation_control`, … (10 declarations)
- `Chapter08.Varifold.tangentialDivergence.eq_1` — used by `S.intcpt_allard_radial_field_divergence`, `S.stationary_constancy_tangentGraph_measure`, `S.varifold_tangents_rh_radial_euler_identity`
- `Chapter08.Varifold.tangentialDivergence_eq_sum_inner` — used by `S.first_variation_theorems`
- `Chapter08.Varifold.tangentialJacobianReal` — used by `S.stationary_constancy_tangentGraph_measure`
- `Chapter08.Varifold.tangentialJacobianReal._proof_1` — used by `S.stationary_constancy_tangentGraph_measure`
- `Chapter08.Varifold.weight` — used by `S.allard_rectifiability_and_tangent_cones`, `S.allard_tc_cone_rescaling_invariance`, `S.allard_tc_density_blowup_decay`, `S.allard_tc_flat_blowup_ball_limits`, `S.allard_tc_rectifiability`, `S.allard_tc_scf_constancy_plane`, … (86 declarations)
- `Chapter08.Varifold.weight.eq_1` — used by `S.allard_tc_tpr_weighted_approx_tangent_iff`, `S.frt_weight_blowup_tendsto`, `S.intcpt_canon_weight_blowup_tendsto`, `S.intcpt_fli_weight_integral_tendsto`, `S.stationary_constancy_tangentGraph_measure`, `S.tgc_weight_blowup_tendsto`, … (8 declarations)
- `Chapter08.Varifold.weight.instSigmaFinite` — used by `S.density_exists_ae_8_3_6`, `S.frt_vgm_eq_map_graph_of_lintegral`, `S.frt_vgm_measurable_plane_selection`, `S.frt_weight_eq_multiplicity_hausdorff`, `S.intcpt_integral_density_integer`, `S.plane_disint_slice_density`, … (7 declarations)
- `Chapter08.Varifold.weight_apply` — used by `S.allard_tc_cone_rescaling_invariance`, `S.allard_tc_density_blowup_decay`, `S.allard_tc_flat_blowup_ball_limits`, `S.allard_tc_rectifiability`, `S.allard_tc_stationary_cone_flat`, `S.allard_tc_tangent_point_representation`, … (24 declarations)
- `Chapter08.Varifold.weight_finite_on_compact` — used by `S.allard_tc_density_blowup_decay`, `S.allard_tc_stationary_cone_flat`, `S.allard_tc_tangent_plane_density`, `S.allard_tc_tangent_point_representation`, `S.frt_carrier_nullMeasurable`, `S.frt_tangent_plane_hasDensity`, … (24 declarations)

**`Poincare.SimonGMT.Chapter08.VarifoldConvergence`** (`Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`)

- `Chapter08.Varifold.RadonConverges` — used by `S.compactness_theorem`, `S.density_semicontinuity_theorem`, `S.intcpt_diag_rescaled_radon_tendsto`, `S.intcpt_diagonal_integral_blowup`, `S.integral_compactness_theorem`, `S.lower_density_ge_one_ae_of_radonConverges`, … (12 declarations)
- `Chapter08.Varifold.RadonConverges.firstVariationNormOn_le_liminf` — used by `S.variationMeasure_le_liminf_of_radonConverges`
- `Chapter08.Varifold.RadonConverges.hasLocallyBoundedFirstVariation` — used by `S.variationMeasure_le_liminf_of_radonConverges`

**`Poincare.SimonGMT.Chapter08.WeightedRadialIdentity`** (`Poincare/SimonGMT/Chapter08/WeightedRadialIdentity.lean`)

- `Chapter08.Grassmannian.project.eq_1` — used by `S.intcpt_allard_cm_cylinder_weight`
- `Chapter08.Varifold.hasDerivAt_normalized_weightedCutoffMass` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Varifold.hasDerivAt_weightedCutoffNormalMass` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Varifold.weightedCutoffMass` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Varifold.weightedCutoffMass_eq_weight_integral` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Varifold.weightedCutoffNormalMass` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Varifold.weightedRadialGradientTerm` — used by `S.monotonicity_formula_8_3_3`
- `Chapter08.Varifold.weightedRadialVectorField` — used by `S.monotonicity_formula_8_3_3`