# Chapter 6 — Currents (Simon, printed pp. 131–180): statement map

Frozen contract: `GMT/Ch06/Contract.lean` (namespace `GMT.Ch06`), final theorem
`GMT.Ch06.main_theorem`, a conjunction of the 12 Props below. `Submission.lean` is a byte copy.

## Conventions

* Ambient space `Eucl P := EuclideanSpace ℝ (Fin P)` (`ℝ^P`). §2, §3, §4, §7, §8 statements are for
  arbitrary `P` (the book uses `ℝ^P` or `ℝ^{n+ℓ}`; if `P < n` everything is the zero current,
  if `P = n` the book itself covers the case, e.g. 3.14 for 6.3). §5, 6.1, 6.2 use
  `ℝ^{(m+1)+ℓ}`, `ℓ ≥ 1`, because constants are `c(n, ℓ)` and the book's standing assumption
  in §5 is `n, ℓ ≥ 1`.
* **Degree shift.** SimonGMT's `GeometricCurrentOn.boundary` is defined on degree `m + 1`.
  Every statement involving `∂T` of an `n`-current (`n ≥ 1`) writes the book's `n` as `m + 1`
  (6.1, where the book has `n ≥ 2` and `T ∈ 𝒟ₙ₋₁`, writes `n = m + 2`).
* Hausdorff measure `Hⁿ` = Mathlib `μHE[n]` (normalized; equals Lebesgue measure on `ℝⁿ`).
* `W ⊂⊂ U` = `CompactlyContainedOpen W U`: `W` open, `closure W` compact, `closure W ⊆ U`.
* Linear combinations of currents are written pointwise on test forms (SimonGMT provides no
  `Add`/`Sub` instances on `GeometricCurrentOn`), e.g. `∀ ω, T ω - P ω = R.boundary ω + S ω`.

## Reused SimonGMT definitions (all checked against the source)

| Lean | File | Book | Check |
|---|---|---|---|
| `TestFormOn U n` | Chapter06/Currents.lean | `𝒟ⁿ(U)` p. 134 | globally smooth (`C^∞`, not `ω`) forms, compact `tsupport ⊆ U`; equals zero extensions of `𝒟ⁿ(U)` for open `U` |
| `GeometricCurrentOn U n` | Chapter06/Currents.lean | 2.1 | linear + sequentially continuous for the convergence of p. 134 (common compact support `K ⊆ U`, all derivatives uniformly); proved equivalent to Mathlib distributions (`geometricCurrentOnEquivDistribution`) |
| `GeometricCurrentOn.boundary` | Chapter06/Currents.lean | 2.3 | `∂T(ω) = T(dω)` |
| `GeometricCurrentOn.massOn`, `.mass` | Chapter06/Mass.lean | 2.4, 2.5 | sup of `T(ω)` over `ω ∈ 𝒟ⁿ(U)`, `tsupport ω ⊆ W`, Euclidean coefficient norm `|ω(x)| ≤ 1` (Remark 2.6 norm); `mass = massOn U` |
| `GeometricCurrentOn.support` | Chapter06/CurrentLocalEquality.lean | 2.11 | `U \ ⋃{W : T vanishes on W}`; restricting to relatively compact `W` gives the same union |
| `WeaklyConvergesOn` | Chapter06/Currents.lean | 2.13 | pointwise convergence on `𝒟ⁿ(U)` |
| `NVector`, `simpleNVector`, `nVectorPushforward`, `SimonMultiIndex`, `Covector`, `DifferentialForm` | Chapter06/FormsDuality.lean, Forms.lean | 1.1–1.10 | `Λₙ = (Λⁿ)*`; `⟨ω, τ₁∧⋯∧τₙ⟩ = ω(τ₁,…,τₙ)`; `ℓ_#` by duality (1.9) |
| `CountablyRectifiable` | Chapter03/Rectifiable.lean | Ch. 3, 1.1 | `M ⊆ M₀ ∪ ⋃ Fⱼ(ℝⁿ)`, `Hⁿ(M₀) = 0`, `Fⱼ` Lipschitz |
| `HasWeightedApproximateTangentSpaceAt` | Chapter03/Rectifiable.lean | Ch. 3, 1.7 | `lim ∫_{η_{x,λ}M} f(y) θ(x+λy) dHⁿ = θ(x) ∫_P f dHⁿ`, `dim P = n`; by 1.7 this *is* `TₓM` (agrees with 1.4 when `θ ≡ 1`) |
| `dimensionalUpperDensity` | Chapter01/Densities.lean | Ch. 1, 3.1 | `limsup_{ρ↓0} μ(B̄_ρ(x))/(ω_n ρⁿ)` |

Not used (per the brief): `Chapter06.MassRepresentation`, `IntegerRectifiableCurrentData`,
`Current`/`GeometricCurrent` algebraic API, `Chapter04.RectifiableVarifold`.

## New definitions and why they are faithful

* `IsRectifiableTriple U n M θ ξ` (3.1, 8.1): `M ⊆ U`, `NullMeasurableSet M μHE[n]`
  (= `Hⁿ`-measurable, since `M` is `Hⁿ`-σ-finite under the integrability condition),
  `CountablyRectifiable n M`, `θ > 0` on `M`, `θ` integrable on `M ∩ K` for every compact
  `K ⊆ U`, `ξ` `Hⁿ⌞M`-a.e. strongly measurable, and `Hⁿ`-a.e. on `M`, `ξ(x) = ±τ₁∧⋯∧τₙ` with
  `τ` orthonormal spanning the approximate tangent space of `M` w.r.t. `θ` (Ch. 3, 1.7).
  The weighted tangent space is used because in 8.1 `θ` is real and `Hⁿ⌞M` need not be locally
  finite; for integer `θ ≥ 1` it coincides `Hⁿ`-a.e. with `TₓM` of Ch. 3, 1.4. The `±` (printed in
  8.1) matters only for `n = 0`, where no frame can be flipped (0-dimensional slices need signs).
* `tauAction n M θ ξ ω = ∫_M θ ⟨ω, ξ⟩ dHⁿ` — the formula 3.1 (‡).
* `IsIntegerMultiplicity T` (3.1): `∃ M θ ξ`, triple conditions, `θ` natural-valued on `M`,
  `T = τ(M,θ,ξ)` on all test forms. `IsRectifiableCurrent T` (8.1): same with real `θ`.
  These are predicates on genuine currents; no tangent data or mass representation is supplied
  as a field.
* `IsIntegralCurrent T`: `T` and `∂T` integer multiplicity (hypothesis of 8.2).
* `IsMeasureRepresentation T μ v` (2.7): for every test form `ω`, `⟨ω, v⟩` is `μ`-integrable
  and `T(ω) = ∫ ⟨ω, v⟩ dμ`. Testing with `φ dx^α` (`φ = 1` on a compact `K ⊆ U`) shows this is
  equivalent to `v` being locally `μ`-integrable on `U` (phrased via scalar integrability because
  `ContinuousENorm` on `NVector` is not found by instance search at this Mathlib pin). Such
  `(μ, v)` exists iff `T` has locally finite mass (Riesz); the vector measure `v μ` is unique.
* `IsRestriction T A S` (2.9): `A` Borel and `S(ω) = ∫_A ⟨ω, v⟩ dμ` for some representation of
  `T`. Independent of the representation by uniqueness of the vector measure. This replaces
  `MassRepresentation` data: it is a relation, not stored data.
* `IsMassMeasure T μ` (2.8): `μ(Uᶜ) = 0` and `μ(W) = M_W(T)` for every open `W ⊂⊂ U`
  (determines `μ_T` uniquely when masses are locally finite).
* `IsSlice T f t S` (4.6): `S = ∂(T⌞{f<t}) − (∂T)⌞{f<t}` (sets intersected with `U`).
* `IsLipschitzPushforward T f S` (3.6, Ch. 3 2.1–2.2): for some representation `T = τ(M,θ,ξ)`
  and some `L x` agreeing with the directional derivatives `d/dt f(x+tv)|₀` for `v ∈ TₓM`
  (`Hⁿ`-a.e. `x ∈ M`; this is Simon's characterization of `d^M f_x`, Ch. 3 p. 76),
  `S(ω) = ∫_M θ ⟨ω(f(x)), (L x)_# ξ(x)⟩ dHⁿ`. Since `ξ(x) ∈ Λₙ(TₓM)`, only `L x|TₓM = d^M f_x`
  matters, so `S` is unique. For `C¹` `f` it agrees with 2.23 (`L x = Df(x)`).
* `LatticeFaceIndex`, `latticeFace ρ F`, `latticeFaceAction ρ F` (§5 notation): the `n`-faces
  `ρ(z + F_α)` of the cubical decomposition, `z ∈ ℤ^N`, `α` increasing; each face of `𝓛ₙ(ρ)`
  has exactly one index; `[[F]](ω) = ∫_F ⟨ω, e_{α₁}∧⋯∧e_{αₙ}⟩ dHⁿ` (orientation choice is
  absorbed by the real/integer coefficient `β_F`).
* `IsLatticeChain ρ β P`: `P(ω) = ∑'_F β_F [[F]](ω)` (locally finite, so finitely supported
  for each test form).
* `flatDistance W T₁ T₂` (7.1): infimum of `M_W(S) + M_W(R)` over integer multiplicity
  `R ∈ 𝒟ₙ₊₁(U)`, `S ∈ 𝒟ₙ(U)` with `T₁ − T₂ = ∂R + S`.

## Statement map

| # | Book item (printed page) | Lean Prop | Meaning / hypotheses | Errata / notes | Existing SimonGMT support |
|---|---|---|---|---|---|
| 1 | Lemma 2.15 (p. 137) | `CompactnessUnderMassBounds` | `T_q ∈ 𝒟ₙ(U)`, `sup_q M_W(T_q) < ∞ ∀ W ⊂⊂ U` ⇒ subsequence `T_{q'} ⇀ T` in `U`, and convergence on continuous compactly supported forms for every representation (2.7) of the `T_{q'}` and `T` | general `n`, `P` | new; tools: `WeaklyConvergesOn.massOn_le_liminf` (2.14, Mass.lean), `GeometricCurrentOn.fixedSupportCLM` (FixedSupportCurrentTopology.lean), Ch1 `simon_theorem_4_14` (vector Riesz, RadonPolarRepresentation.lean) |
| 2 | Theorem 2.34 Constancy (p. 142) | `ConstancyTheorem` | `U ⊆ ℝⁿ` open connected, `T ∈ 𝒟ₙ(U)`, `∂T = 0` ⇒ `∃ c, T = c[[U]]`, `[[U]](ω) = ∫_U ω(e₁,…,eₙ) dLⁿ` | `n = m+1` | new |
| 3 | Lemma 3.9 (p. 148) | `LipschitzPushforwardIntegerMultiplicity` | `T` integer multiplicity in `U ⊆ ℝ^P`, `f` locally Lipschitz on `U`, `f(U) ⊆ V` open in `ℝ^Q`, `f⁻¹(K) ∩ spt T` compact for compact `K ⊆ V` ⇒ `∃ S ∈ 𝒟ₙ(V)`, `S = f_#T` (3.6) and `S` integer multiplicity | general `n` | new; smooth affine special case `GeometricCurrentOn.affinePushforward` (AffineCurrentPushforward.lean); Ch2 `rademacher_ae_differentiableAt` (Lipschitz.lean) |
| 4 | Theorem 3.11 Federer–Fleming (p. 149) | `FedererFlemingCompactness` | `T_j` integer multiplicity, `sup_j (M_W(T_j)+M_W(∂T_j)) < ∞ ∀ W ⊂⊂ U` ⇒ subsequence `⇀` an integer multiplicity `T` | `n = m+1` | new (proof in book via 8.2 + 6.3) |
| 5 | §4: 4.4–4.10 Slicing (pp. 153–158) | `SlicingTheorem` | `T ∈ 𝒟ₙ(U)` with `M_W(T) + M_W(∂T) < ∞ ∀ W ⊂⊂ U` (general `T`, as in 4.6–4.10), `f` `L`-Lipschitz on `U` ⇒ slices `⟨T,f,t⟩` (4.6) exist ∀ t; `spt ⊆ spt T ∩ {f=t}` (4.8); if `T` is integer multiplicity, slices are integer multiplicity for a.e. `t` (4.4, 4.5(2)); for open `W ⊆ U` and any `L_W` with `‖Df‖ ≤ L_W` Lebesgue-a.e. on `W` (i.e. `L_W ≥ ess sup_W |Df|`, the book's localized constant): `∫*_a^b M_W(⟨T,f,t⟩) dt ≤ L_W·M_W(T⌞{a<f<b})` (4.10, upper integral expressed by a measurable majorant) | book prints `M(T⌞{a<f<b})` on the right of 4.10; the proof (4.9) gives the stronger `M_W`, which is stated | new |
| 6 | 5.3 Deformation Theorem (p. 160), 5.1 = case `ρ = 1` (p. 159) | `DeformationTheorem` | `n, ℓ ≥ 1`, `∃ C(n,ℓ)` ∀ `T ∈ 𝒟ₙ(ℝ^{n+ℓ})`, `M(T)+M(∂T) < ∞`, ∀ `ρ > 0`: `T − P = ∂R + S`, `P = ∑_{F∈𝓛ₙ(ρ)} β_F[[F]]`, `M(P) ≤ C M(T)`, `M(∂P) ≤ C M(∂T)`, `M(R) ≤ CρM(T)`, `M(S) ≤ CρM(∂T)`, supports within distance `< 2√(n+ℓ)ρ` of `spt T` / `spt ∂T`; `T` i.m. ⇒ `β_F ∈ ℤ`, `P, R` i.m.; `T, ∂T` i.m. ⇒ `S` i.m. | printed `n, k ∈ {1,2,…}`, `C(n,k)` → `n, ℓ`; printed `𝓛_j(ρ)` → `𝓛ₙ(ρ)`; "so is s" → `S`; `dist(x, ∅) = ∞` convention via `Metric.thickening` | new |
| 7 | 6.1 Isoperimetric Theorem (p. 168) | `IsoperimetricTheorem` | `n ≥ 2`, `ℓ ≥ 1`, `∃ c(n,ℓ)`: `T ∈ 𝒟ₙ₋₁(ℝ^{n+ℓ})` i.m., `spt T` compact, `∂T = 0` ⇒ `∃ R` i.m., `spt R` compact, `∂R = T`, `M(R)^{(n−1)/n} ≤ c M(T)` | `n = m+2` | new |
| 8 | 6.2 Weak Polyhedral Approximation (p. 169) | `PolyhedralApproximation` | `T` i.m. in `U ⊆ ℝ^{n+ℓ}`, `M_W(T), M_W(∂T) < ∞ ∀ W ⊂⊂ U` ⇒ `ρ_k ↓ 0`, integer `β^{(k)}`, `P_k = ∑_{F∈𝓛ₙ(ρ_k)} β^{(k)}_F[[F]] ⇀ T` in `U` | printed `F_n(ρ_k)`, `β_R^{(k)}` → `𝓛ₙ(ρ_k)`, `β_F^{(k)}`; `n = m+1` | new |
| 9 | 6.3 Boundary Rectifiability (p. 170) | `BoundaryRectifiability` | `T` i.m., `M_W(∂T) < ∞ ∀ W ⊂⊂ U` ⇒ `∂T` i.m. | printed `M(∂T)` → `M_W(∂T)`; `n = m+1`; general `P` (ℓ = 0 is 3.14) | new |
| 10 | Theorem 7.2 (p. 170) | `FlatConvergenceIffWeakConvergence` | `T, T_j` i.m., `sup_j (M_W(T_j)+M_W(∂T_j)) < ∞ ∀ W ⊂⊂ U` ⇒ (`T_j ⇀ T` ⟺ `d_W(T_j,T) → 0 ∀ W ⊂⊂ U`) | `n = m+1` | new |
| 11 | 8.1 Rectifiability Theorem (p. 173) | `RectifiabilityTheorem` | `M_W(T)+M_W(∂T) < ∞ ∀ W ⊂⊂ U`, `Θ*ⁿ(μ_T, x) > 0` `μ_T`-a.e. ⇒ `T = τ(M,θ,ξ)` with real `θ > 0` | upper density as printed; `μ_T` given by `IsMassMeasure`; `n = m+1` | new; tools: Ch1 `simon_theorem_3_3` (DensityComparison.lean), `simon_theorem_3_24_i/ii/iii` (RadonNikodymTheorem.lean), `simon_theorem_4_14`; Ch3 `simon_lemma_3_2` (Rectifiable.lean). Structure theorem (Ch3 3.6/3.8) is missing in SimonGMT |
| 12 | Theorem 8.2 (p. 176) | `IntegralityOfWeakLimits` | `T_j, ∂T_j` i.m., `sup_j (M_W(T_j)+M_W(∂T_j)) < ∞`, `T_j ⇀ T` ⇒ `T` i.m. | `n = m+1` | new |

Always-useful SimonGMT facts: `GeometricCurrentOn.boundary_boundary` (`∂² = 0`),
`WeaklyConvergesOn.boundary`, `GeometricCurrentOn.massOn_mono`, `GeometricCurrentOn.le_massOn`,
`HasWeightedApproximateTangentSpaceAt.unique`, `GeometricCurrentOn.pointProduct` (2.22).

## Points of judgement (flagged for reviewers)

* `θ` for integer multiplicity is real-valued with `θ(x) ∈ ℕ` on `M` (positivity forces `≥ 1`).
* Restriction, mass measure, slice and push-forward are relations (`IsRestriction` …) defined via
  existence of a representation; uniqueness of the represented object is a theorem, not assumed.
  In conclusions they appear existentially (`∃ S, IsSlice …`), in hypotheses universally where
  the object is determined (`∀ R, IsRestriction T A R → …`).
* 2.15 is stated with weak convergence on `𝒟ⁿ(U)` *and* convergence on continuous compactly
  supported forms (the book's literal conclusion), the latter for all representations (2.7).
* 4.10 is stated for general `T` (integrality of slices conditional on `T` integer multiplicity),
  with the localized constant `ess sup_W |Df|` (as `L_W`), with `M_W` on the right (stronger than
  printed `M`), and with Simon's upper
  integral `∫*` encoded as a measurable majorant `g`.
* 5.1 is not a separate Prop: it is 5.3 with `ρ = 1`.
* 3.13, 3.14/3.16, 2.25–2.33, 2.36 are omitted as lemmas serving the headline results.
