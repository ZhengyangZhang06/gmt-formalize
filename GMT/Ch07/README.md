# Chapter 7 — Area Minimizing Currents (Simon, printed pp. 181–204)

Frozen contract: `GMT/Ch07/Contract.lean` (namespace `GMT.Ch07`, final theorem
`GMT.Ch07.main_theorem`).  `GMT/Ch07/Submission.lean` is a byte copy for the prover.

Book: L. Simon, *Introduction to Geometric Measure Theory* (2014 Tsinghua notes), Chapter 7,
PDF pages 188–211.  Statements were checked against the rendered pages, not memory.

## Conventions

* Ambient space `ℝ^{n+k}` = `Euclid (n + k)` = `EuclideanSpace ℝ (Fin (n + k))`.  When a
  submanifold `N` appears it has dimension `n + ℓ` with `ℓ ≤ k`.  The book prints
  "`N` an `(n+ℓ)`-dimensional submanifold of `ℝ^{n+ℓ}` (`ℓ ≤ k`, so `N = ℝ^{n+ℓ}` …)" (7.1.2, §3,
  4.2); the ambient dimension is evidently `n + k` (`N = U` "when `ℓ = k`", p. 187).
* Currents: the clean SimonGMT `GeometricCurrentOn U n` (Simon 6.2.1, sequential continuity on
  `𝒟ⁿ(U)`; equivalent to Mathlib distributions by `geometricCurrentOnEquivDistribution`).
  Boundary `T.boundary` (6.2.3), mass `T.massOn W` = `M_W(T)` with the Euclidean coefficient norm
  of 6.1.15/6.2.5, `T.mass` (6.2.4), support `T.support` (6.2.11), `WeaklyConvergesOn` (6.2.13),
  restriction of domains `restrictDomain`, proper affine push-forward `affinePushforward` (6.2.23).
* For an `n`-current the book sets `∂T = 0` when `n = 0`.  `SameBoundary`, `BoundaryVanishes`,
  `boundarySupport`, `boundaryMassOn` implement `∂S = ∂T`, `∂T = 0`, `spt ∂T`, `M_W(∂T)` in every
  degree with this convention.
* `Hⁿ` = Mathlib `μHE[n]` (normalized: equals Lebesgue measure on `ℝⁿ`, = Simon's `Hⁿ`).  Null-set
  conclusions `H^s(A) = 0` use Mathlib `μH[s]` with real `s` (same null sets for `s ≥ 0`).  For
  `s < 0` (only in 3.3 with `n ≤ 2` and 4.4 with `n = 1`, small `α`) Simon's `Hˢ` is undefined;
  Mathlib's `μH[s]` is used as is (Simon's dimension-reduction conclusion there is emptiness).
* Densities use masses of open balls, `μ_T(B_ρ(x)) = M_{B_ρ(x)}(T)` (6.2.8); Simon's closed balls
  give the same limit.  `ωₙ = volume (ball 0 1)` in `ℝⁿ`.
* "`λⱼ ↓ 0`" is taken as "`λⱼ > 0`, `λⱼ → 0`" (every such sequence has a decreasing subsequence,
  and the conclusions are about subsequences).

## New definitions (all in `GMT.Ch07`) and why they are faithful

| Lean | Book | Notes |
|---|---|---|
| `MultiVector P n` | `Λₙ(ℝᴾ)` (6.1) | the dual of `n`-covectors `Covector (ℝᴾ) n` (= Mathlib `ContinuousAlternatingMap`); `ξ α = ⟨α, ξ⟩` (6.1.7). |
| `IsUnitOrientationOf ξ Q` | `ξ = τ₁∧⋯∧τₙ`, `τ` orthonormal basis of `Q` | `⟨α, τ₁∧⋯∧τₙ⟩ = α(τ₁,…,τₙ)` (6.1.1, 6.1.7); a `±` sign is allowed (only matters for `n = 0`). |
| `IMRep U n` | triple `(M, θ, ξ)` of Definition 6.3.1 | `M ⊆ U` Borel (Simon: `Hⁿ`-measurable; same current up to null sets), countably `n`-rectifiable (SimonGMT Ch3 `CountablyRectifiable`, clean), `θ : → ℕ` measurable, `θ ≥ 1` on `M`, `∫_{M∩K} θ dHⁿ < ∞` for compact `K ⊆ U`; `ξ` a.e.-strongly measurable and `Hⁿ`-a.e. on `M` orienting the approximate tangent space (SimonGMT Ch3 `HasApproximateTangentSpaceAt`, clean, Ch. 3, 1.4).  This is a witness of the definition, not a stored conclusion about `T`. |
| `IMRep.action`, `IMRep.Represents` | `τ(M,θ,ξ)(ω) = ∫_M ⟨ω,ξ⟩θ dHⁿ`, `T = τ(M,θ,ξ)` | 6.3.1 (‡). |
| `IMRep.measure` | `μ_V = θHⁿ⌞M` (= `μ_T`) | Ch. 4, 1.1; Ch. 6, 3.2(3). |
| `IsIntegerMultiplicity T` | 6.3.1 | `∃ R : IMRep U n, R.Represents T`. |
| `Sub (GeometricCurrentOn U n)` | `S − T` | pointwise difference (continuity proved). |
| `CompactlyContained W U` | `W ⊂⊂ U` | `closure W` compact and `⊆ U`. |
| `IsMinimizingIn T A` | **7.1.1** | `T` integer multiplicity and `M_W(T) ≤ M_W(S)` for all open `W ⊂⊂ U` and integer multiplicity `S` with `∂S = ∂T` and `spt(S − T)` a compact subset of `A ∩ W`.  Competitors are integer multiplicity: Remark 7.2.2(1) ("of course `T` is minimizing", `T` minimizing only among integer multiplicity `R`) and the proofs of 1.4, 2.4 require this. |
| `unitBallVolume n` | `ωₙ` | Lebesgue measure of the unit ball of `ℝⁿ`. |
| `HasMassDensity T x θ` | `Θⁿ(μ_T, x) = θ` | `θ ≥ 0` and `M_{B_ρ(x)}(T)/(ωₙρⁿ) → θ` as `ρ ↓ 0`. |
| `currentEval T ω` | `T(ω)` for `ω ∈ 𝒟ⁿ(U)` | `0` if `ω ∉ 𝒟ⁿ(U)`; only used for sequences whose domains eventually contain `spt ω`. |
| `ConvergesWeakly` | `Tⱼ ⇀ C` in `ℝ^{n+ℓ}` for `Tⱼ ∈ 𝒟ₙ(Uⱼ)` | 6.2.13 on varying (exhausting) domains, as for blow-ups. |
| `MassMeasuresConverge` | `μ_{Tⱼ} → μ_T` (Radon measures) | for **all** integer multiplicity representations of `Tⱼ` and `T`, `∫ f dμ_{Tⱼ} → ∫ f dμ_T` for `f ∈ C_c(V)`; matches Remark 7.2.5(1) (`μ_{V_j} → μ_V`).  `μ_T` does not depend on the representation (Ch. 6, 3.2(3)), so quantifying over all representations is the faithful (strong) reading. |
| `dilationCLM`, `dilation` | `η_{x,λ}(y) = λ⁻¹(y − x)` | written `y ↦ −λ⁻¹x + λ⁻¹y`. |
| `blowUp T x λ hλ` | `η_{x,λ#}T ∈ 𝒟ₙ(η_{x,λ}(U))` | SimonGMT `affinePushforward` (genuine push-forward `T(η^#ω)`, 6.2.23) of `T` (domain restricted along `η⁻¹(η(U)) = U`). |
| `IsConeCurrent C` | `η_{0,λ#}C = C ∀λ > 0` | 3.1(2). |
| `IsTangentConeAt T x C` | tangent cone (3.2(1)) | `η_{x,λⱼ#}T ⇀ C` for some `λⱼ > 0`, `λⱼ → 0`. |
| `HasTangentPlaneAt T x` | "there is a tangent plane for `T` at `x`" (3.2(1)) | some tangent cone has support an `n`-dimensional subspace. |
| `IsEmbeddedSubmanifold r d M` | `d`-dim `Cʳ` submanifold, Ch. 2 §4 (4.1) | local 1:1 proper `Cʳ` parametrizations `ψ : V → W`, `ψ(V) = W ∩ M`, `Dψ` of rank `d`. |
| `tangentSpace M y` | `T_yM` (Ch. 2 §4) | velocities `γ'(0)` of `C¹` curves `γ : (−1,1) → M`, `γ(0) = y`. |
| `IsOrientation d M ξ` | orientation of `M` (6.2.2) | `ξ` continuous on `M`, `ξ(y) = ±τ₁∧⋯∧τ_d` for an orthonormal basis of `T_yM`. |
| `regularSet T`, `singularSet T` | **7.4.1** `reg T`, `sing T = spt T \ reg T` | `y ∈ spt T`, with `y ∈ M` itself (otherwise deleting a singular point such as the Simons-cone vertex from `M` would make it "regular"), with `B_ρ(y) ⊆ U`, `m ∈ ℤ∖{0}`, embedded oriented `C¹` `n`-submanifold `M` (of locally finite `Hⁿ` measure in `B_ρ(y)`, needed for `[[M]]` to be a current, 6.2.2) and `T = m[[M]]` in `B_ρ(y)` (6.2.16). |
| `approxTangentPlane`, `tangentialDivergence` | `TₓM`, `div_M X` (Ch. 4, 2.3) | `div_M X = trace(p_{TₓM} ∘ DX)` = `Σⱼ eⱼ·∇^M Xʲ`; the approximate tangent plane is unique (SimonGMT `HasApproximateTangentSpaceAt.unique`). |
| `IMRep.firstVariation` | `δV(X) = ∫_M div_M X dμ_V` (Ch. 4, 2.2) | `V = v(M, θ)`. |
| `IMRep.IsStationaryAlong R N` | `V` stationary in `U ∩ N` (Ch. 4, 2.6) | computed form stated on p. 88: `δV(X) = 0` for `X ∈ C¹_c(U)` tangent to `N` on `N ∩ U`. |
| `IMRep.HasLocallyBoundedMeanCurvature` | Ch. 4, 3.14 | `δV(X) = −∫ X·H dμ_V` for all `X ∈ C¹_c(U)`, `H` measurable and `μ_V`-essentially bounded on compact subsets of `U`. |
| `InClassO n U N ξN` | class `𝒪` (7.5, p. 197) | oriented embedded `C²` `(n+1)`-submanifold, `(N̄∖N) ∩ U = ∅`, `N ∩ U ≠ ∅`. |
| `IsBoundaryOfRegion T E ξN` | `T = ∂[[E]]` in `U` (7.5.1) | `T(ω) = ∫_E ⟨dω, ξ_N⟩ dH^{n+1}`. |

SimonGMT definitions reused (all on the survey's clean list, sources read): Ch6
`GeometricCurrentOn`, `TestFormOn`, `DifferentialForm`, `Covector`, `IsTestForm`,
`exteriorDerivative`, `GeometricCurrentOn.boundary/massOn/mass/support/restrictDomain/
affinePushforward`, `WeaklyConvergesOn`; Ch3 `CountablyRectifiable`,
`HasApproximateTangentSpaceAt`.  Not used: `Chapter07.MinimizingIn` (abstract),
`Chapter06.IntegerRectifiableCurrentData`, `Chapter04.RectifiableVarifold`.

## Statement map

| # | Lean Prop | Book | Hypotheses → conclusion | Existing SimonGMT |
|---|---|---|---|---|
| 1 | `MinimizingImpliesStationary` | Lemma 7.1.2, pp. 181–182 | `U` open, `N` embedded `C²` `(n+ℓ)`-submanifold of `ℝ^{n+k}`, `(N̄∖N)∩U = ∅`, `spt T ⊆ N`, `T` minimizing in `N ∩ U`, `∂T = 0` → for every representation `(M,θ,ξ)` of `T`, `v(M,θ)` is stationary in `N ∩ U` and has locally bounded generalized mean curvature in `U`. | new.  (Ch8 `Varifold.Stationary` and Ch4 `IsStationaryIn` are on objects not linked to currents.) |
| 2 | `ExistenceOfMinimizingFilling` | Lemma 7.2.1, p. 183 | `S ∈ 𝒟_{n−1}(ℝ^{n+ℓ})` integer multiplicity, `spt S` compact, `∂S = 0` (`n = m+2 ≥ 2`) → `∃ T` integer multiplicity, `spt T` compact, `∂T = S`, `M(T) ≤ M(R)` for all integer multiplicity `R` with compact support and `∂R = S`. | new (needs Federer–Fleming 6.3.11, not in SimonGMT). |
| 3 | `CompactnessOfMinimizingCurrents` | Theorem 7.2.4, p. 184 | `Tⱼ` minimizing in `U`, `supⱼ(M_W(Tⱼ) + M_W(∂Tⱼ)) < ∞` for open `W ⊂⊂ U`, `Tⱼ ⇀ T` → `T` minimizing (incl. integer multiplicity, Remark 2.5(1)) and `μ_{Tⱼ} → μ_T` in `U`. | part: mass l.s.c. `WeaklyConvergesOn.massOn_le_liminf` (Ch06/Mass.lean). |
| 4 | `DensityAndTangentCones` | Theorem 7.3.1, p. 187 | `N` as in #1, `T` minimizing in `U ∩ N`, `spt T ⊆ U ∩ N` → (1) `Θⁿ(μ_T,·)` exists on `U ∖ spt ∂T` and is u.s.c. there; (2) for `x ∈ spt T ∖ spt ∂T`, `λⱼ → 0⁺` there are a subsequence and `C ∈ 𝒟ₙ(ℝ^{n+k})` integer multiplicity minimizing in `ℝ^{n+k}` with `η_{x,λⱼ'#}T ⇀ C`, `μ_{η#T} → μ_C`, `C` a cone, `Θⁿ(μ_C,0) = Θⁿ(μ_T,x)`. | Ch4 monotonicity/density/u.s.c. (`Chapter04/Density.lean` `IsStationaryIn.upperSemicontinuousOn_stationaryDensity`, `Chapter04/MeanCurvature.lean` `HasGeneralizedMeanCurvatureIn.upperSemicontinuousOn_stationaryDensity`, `Chapter04/LpDensity.lean`) — but for the strengthened `RectifiableVarifold`; usable after linking `IMRep` to it. |
| 5 | `IntegerDensityAndTangentPlanes` | Theorem 7.3.3, p. 189 | as #4 plus `∂T = 0` → `∃ E ⊆ F`, `H^{n−3+α}(E) = 0`, `H^{n−2+α}(F) = 0` (`∀α>0`), `Θⁿ(μ_T,x) ∈ ℤ` on `U∖E`, tangent plane at each `x ∈ spt T∖F`. | AppA `DimensionReductionSystem` (Foundations.lean) is the abstract tool. |
| 6 | `RegularSetDense` | Theorem 7.4.2, p. 194 | as #5 → `spt T ⊆ closure (reg T)`. | new (needs Allard 5.2, missing). |
| 7 | `DensityOneImpliesRegular` | Theorem 7.4.3, p. 194 | `Tᵢ, T` minimizing in `U ∩ N`, supports in `N`, `∂Tᵢ = ∂T = 0`, `Tᵢ ⇀ T`, `supᵢ M_W(Tᵢ) < ∞`, `y ∈ N∩U`, `Θⁿ(μ_T,y) = 1`, `yⱼ ∈ spt Tⱼ`, `yⱼ → y` → `y ∈ reg T` and eventually `yⱼ ∈ reg Tⱼ`. | new. |
| 8 | `SingularSetSmallWhereDensityBelowTwo` | Theorem 7.4.4, p. 194 | as #6, `ξ ∈ spt T`, `Θⁿ(μ_T,ξ) < 2` → `∃ρ>0 ∀α>0`, `H^{n−2+α}(sing T ∩ B_ρ(ξ)) = 0`. | AppA `DimensionReductionSystem`. |
| 9 | `HalfSpaceConeLiesInBoundary` | Theorem 7.4.5, p. 195 | `C` minimizing in `ℝ^{n+k}`, `∂C = 0`, cone, `spt C ⊆ closure H`, `H = {v·x > 0}` (`v ≠ 0`) → `spt C ⊆ ∂H`. | new. |
| 10 | `CodimensionOneRegularity` | **Theorem 7.5.8, p. 200** | `N ∈ 𝒪` oriented by `ξN`, `E ⊆ N ∩ U` measurable, `T = ∂[[E]]`, `T` (integer multiplicity and) minimizing in `N ∩ U` → `sing T = ∅` if `n ≤ 6`; `sing T ∩ K` finite for compact `K ⊆ U` if `n = 7`; `H^{n−7+α}(sing T) = 0 ∀α>0` if `n > 7`.  `N = ℝ^{n+1}` is `k = 1`, `N = univ`. | AppB `simons_cone_dimension_seven_threshold`, `exists_final_exponent` (SimonsInequalities.lean), AppA `DimensionReductionSystem`. |
| 11 | `RegularComponentsAreMinimizing` | Corollary 7.5.11, p. 202 | `T` as in #10, `T = τ(M,θ,ξ)`, `y ∈ reg T`, `T₁(ω) = ∫_{M₁} ⟨ω,ξ⟩ dHⁿ` with `M₁` the component of `reg T` through `y` → `∂T₁ = 0`, `T₁` minimizing in `U ∩ N`. | abstract 1.4: `Chapter07.minimizing_summands` (Chapter07/Basic.lean), over abstract groups. |

## Errata corrected / deviations

1. **7.1.2**: hypotheses `spt T ⊆ N` and `(N̄∖N) ∩ U = ∅` added.  They are the setting of
   "stationary in `U ∩ N`" (Ch. 4, 2.5: "`(N̄∖N) ∩ U = ∅`, `M ⊆ N`").  Without `spt T ⊆ N` the
   lemma fails (a non-minimal surface meeting `N` in an `Hⁿ`-null set is vacuously minimizing in
   `N ∩ U`).  The auxiliary statement 1.2(‡) (`M_W(V) ≤ M_W(φ_#V)`) is not stated: as printed
   (`K ⊂ W ∩ N`) it is trivial for `ℓ < k`, and it is only a step toward stationarity.
2. **7.2.1**: the printed conclusion omits `∂T = S` (the proof shows `T ∈ 𝓘_S`); added.
   Stated for `n ≥ 2`, since integer multiplicity currents (Ch. 6, §3) have dimension `≥ 1`; for
   `n = 1` the lemma would moreover need `S(1) = 0`.
3. **7.3.1**: the printed hypothesis "`x ∈ spt T \ spt ∂T`" with conclusion "(1) `Θ` exists
   everywhere in `U`" is garbled; (1) is stated on `U ∖ spt ∂T` (where monotonicity applies),
   (2) for `x ∈ spt T ∖ spt ∂T`.
4. **7.3.3(2)**: printed "`F ⊂ E`" corrected to `E ⊆ F` (the `H^{n−2+α}`-null set must contain the
   `H^{n−3+α}`-null set of non-integer densities: a tangent plane forces integer density).
5. **7.4.3**: stated with `Nᵢ = N` (the book allows `Nᵢ → N` "in the `C²` sense", which is not
   defined at that point); the local mass bound `supᵢ M_W(Tᵢ) < ∞` of 7.2.4, used by the proof
   for `μ_{Tᵢ} → μ_T`, is an explicit hypothesis.
6. **Ambient dimension**: "`(n+ℓ)`-dimensional submanifold of `ℝ^{n+ℓ}` (`ℓ ≤ k`)" read as a
   submanifold of `ℝ^{n+k}`.
7. **7.5.8**: printed "locally finite in `U`" (statement) vs "discrete" (proof) for `n = 7`;
   stated as finiteness on every compact subset of `U` (equivalent, `sing T` being relatively
   closed).

## Results not included

* 1.4 (decomposition lemma) — routine, used only for 5.11; abstract version exists in SimonGMT.
* Unnumbered homology lemma after 2.1, 2.3, 2.5(2), 3.4–3.5, 4.6–4.7, 5.2–5.6, 5.12 — routine or
  proof tools for the headline results.
* 5.7 (one-sided ⇒ regular) — needs a notion of "lies locally on one side of `Σ`" not made
  precise in the book.
* **5.13 (Lemma) is false as printed.**  Counterexample: `ℓ = 2`, `N = (ℝ^{n+1} × {0}) ∪ S` with
  `S` a round `(n+1)`-sphere in `ℝ^{n+2}` inside a ball `U`, away from the hyperplane;
  `E₂ = {x₁ > 0} ∩ ℝ^{n+1} ∩ U`, `E₁ = E₂ ∪ S`.  Then `T₁ = T₂ = ∂[[E₂]]` (a flat disc, minimizing,
  `reg Tᵢ` connected), `E₁ ∩ V = E₂ ∩ V` for a neighbourhood `V` of `∂U` missing `S`, but
  `spt[[E₁]] ⊄ spt[[E₂]]` and `spt T₁ ∩ spt T₂ ⊄ sing T₁ ∩ sing T₂`.  A correct version needs e.g.
  `N ∩ U` connected; it was left out rather than guessed.

## Compile

`bin/leanc GMT/Ch07/Contract.lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) elaborates with a single
warning: `Contract.lean:453:8: warning: declaration uses 'sorry'` (the final `main_theorem`).
No other `sorry`, no `axiom`/`opaque`/`unsafe`/`implemented_by`/`native_decide`; the only proofs in
the file are the continuity of `S − T` and the properness/injectivity of `η_{x,λ}` used to build
`blowUp`.  `Submission.lean` is a byte copy (`cmp` silent).
