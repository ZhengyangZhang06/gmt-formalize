<!-- theorem-id: gmt-ch03/root.de_giorgi-a1.density_estimates-a1 -->

## Theorem `Submission.deGiorgi_density_estimates`

Let n ∈ ℕ, N := n + 1, U ⊆ ℝ^N open, E ⊆ ℝ^N Lebesgue null-measurable and (μ, ν) a Gauss-Green pair for (U, E) (IsGaussGreenPair U E μ ν). Let x ∈ ∂*E := reducedBoundary U μ ν (x ∈ U and normalAverage μ ν x ρ = μ(B_ρ(x)).toReal⁻¹ • ∫_{B_ρ(x)} ν dμ converges as ρ ↓ 0 to a unit vector) and e := ν_E(x) := reducedNormal μ ν x (that limit). Then there are ρ₁ > 0 with B_{ρ₁}(x) ⊆ U and constants C, c ∈ ℝ with c > 0 such that for every ρ ∈ (0, ρ₁): μ(B_ρ(x)) ≤ ofReal(Cρⁿ), ofReal(cρ^{n+1}) ≤ L^N(E ∩ B_ρ(x)) and ofReal(cρ^{n+1}) ≤ L^N(B_ρ(x) ∖ E); and (ρⁿ)⁻¹ ∫_{B_ρ(x)} |ν(y) − e| dμ(y) → 0 as ρ ↓ 0.

Node: `root.de_giorgi-a1.density_estimates-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/32

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/372

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1214, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1218, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1224, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1226, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1231, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1232, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1235, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1242, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1246, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1248, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1251

## Lean problem

Declaration: `Submission.deGiorgi_density_estimates`

```lean
∀ (n : ℕ) (U E : Set (Rn (n + 1))) (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)), IsOpen U → NullMeasurableSet E volume → IsGaussGreenPair U E μ ν → ∀ x ∈ reducedBoundary U μ ν, ∃ ρ₁ : ℝ, 0 < ρ₁ ∧ Metric.ball x ρ₁ ⊆ U ∧ ∃ C c : ℝ, 0 < c ∧ (∀ ρ ∈ Ioo 0 ρ₁, μ (Metric.ball x ρ) ≤ ENNReal.ofReal (C * ρ ^ n) ∧ ENNReal.ofReal (c * ρ ^ (n + 1)) ≤ volume (E ∩ Metric.ball x ρ) ∧ ENNReal.ofReal (c * ρ ^ (n + 1)) ≤ volume (Metric.ball x ρ \ E)) ∧ Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ y in Metric.ball x ρ, ‖ν y - reducedNormal μ ν x‖ ∂μ) (𝓝[>] 0) (𝓝 0)
```

### Frozen project context

`GMT/Ch03/Contract.lean` at `d09bc8a18ce60face651f042976e8465f21f0f68` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.EMetricSpace.Lipschitz
import Poincare.SimonGMT.Chapter02.BV
import Poincare.SimonGMT.Chapter03.Rectifiable

/-!
# Simon, *Introduction to GMT*, Chapter 3 "Countably n-Rectifiable Sets" (pp. 69–84): contract

Frozen statements of the headline results of Chapter 3 of Leon Simon's
*Introduction to Geometric Measure Theory* (2014 Tsinghua notes).

## Conventions (all as in the book)

* `Rn N = EuclideanSpace ℝ (Fin N)`; the ambient space is `ℝ^{n+ℓ}` (`ℝ^{n+1}` in §4).
* `Hⁿ` is Mathlib's Euclidean Hausdorff measure `μHE[n]` (equal to Simon's
  `ω_n (diam/2)^n` normalization, cf. SimonGMT
  `simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure`); applied to an arbitrary set it
  is the Hausdorff outer measure. `Lᵐ` is `volume`.
* "`Hⁿ`-measurable" is `NullMeasurableSet · μHE[n]` (all sets involved are `Hⁿ`-σ-finite, where
  this agrees with Carathéodory measurability). "`Hⁿ`-a.e. `x ∈ M`, `P x`" is
  `∀ᵐ x ∂μHE[n], x ∈ M → P x`, i.e. `Hⁿ({x ∈ M | ¬ P x}) = 0`.
* `B_ρ(x)` is the open ball `Metric.ball x ρ`; `η_{x,λ}(y) = λ⁻¹(y - x)` is SimonGMT `blowUpMap`.

## Definitions reused from `Poincare.SimonGMT.Chapter03` (bodies checked against the book)

* `CountablyRectifiable n M` (Def. 1.1, p. 69): `∃ M₀, μHE[n] M₀ = 0 ∧ ∃ F : ℕ → Rn n → E,
  (∀ j, ∃ K, LipschitzWith K (F j)) ∧ M ⊆ M₀ ∪ ⋃ j, range (F j)`.
* `HasApproximateTangentSpaceAt n M x P` (Def. 1.4, p. 70): `finrank P = n ∧ ∀ f ∈ C_c(E, ℝ),
  ∫_{η_{x,r}(M)} f dHⁿ → ∫_P f dHⁿ` as `r ↓ 0`.
* `HasWeightedApproximateTangentSpaceAt n M θ x P` (Def. 1.7, p. 74): `finrank P = n ∧
  ∀ f ∈ C_c(E, ℝ), ∫_{η_{x,r}(M)} f(y) θ(x + r y) dHⁿ(y) → θ(x) ∫_P f dHⁿ` as `r ↓ 0`.
* `PurelyUnrectifiable n S` (Def. 3.1, p. 78): `∀ R ⊆ S, CountablyRectifiable n R → μHE[n] R = 0`.
* `Chapter02.IsLocallyBV U u` (Ch. 2 (2.1)): `U` open, `u ∈ L¹_loc(U)`, and for every open
  `W ⊂⊂ U` some `c(W)` bounds `∫_W u div g` by `c(W) sup |g|` for all `g ∈ C¹_c(W; ℝᴺ)`.

## Errata / reconciliations (details in the docstrings)

* (2.4)/(2.5): the target of `f` is `ℝ^{n+ℓ₁}` (printed `ℝ^{n+ℓ}`).
* (2.9): printed with `∫_A` on the left and `f⁻¹(y) ∩ M` on the right; stated with `A` on both sides.
* 3.1: "if `P` contains" should read "if `S` contains".
* Proof of 4.3: (9) and the last display should read `{x^{n+1} > λ}`, `{x^{n+1} > 0}` (consistent
  with 4.1 and (‡‡)); the statement of 4.3 is unaffected.
-/

open Filter MeasureTheory Module Set
open scoped CompactlySupported ENNReal NNReal Topology

namespace GMT.Ch03

open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt
  HasWeightedApproximateTangentSpaceAt PurelyUnrectifiable blowUpMap)

/-- The Euclidean space `ℝᴺ`. -/
abbrev Rn (N : ℕ) : Type := EuclideanSpace ℝ (Fin N)

section GeneralDefinitions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Simon Ch. 2, §4 (4.1) (p. 55), used in Ch. 3, Lemma 1.2: `S` is an `n`-dimensional embedded
`C¹` submanifold. Every `y ∈ S` has open sets `V ⊆ ℝⁿ`, `W ∋ y` and a one-to-one `C¹` map
`ψ : V → W` with `ψ(V) = W ∩ S`, `ψ` proper (`K ⊆ W` compact ⇒ `ψ⁻¹(K) ∩ V` compact) and
`Dψ(x)` of rank `n` (injective) at each `x ∈ V`. -/
def IsC1Submanifold (n : ℕ) (S : Set E) : Prop :=
  ∀ y ∈ S, ∃ (V : Set (Rn n)) (W : Set E) (ψ : Rn n → E),
    IsOpen V ∧ IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ 1 ψ V ∧ InjOn ψ V ∧ ψ '' V = W ∩ S ∧
      (∀ K : Set E, IsCompact K → K ⊆ W → IsCompact (V ∩ ψ ⁻¹' K)) ∧
      ∀ x ∈ V, Function.Injective (fderiv ℝ ψ x)

/-- Simon Ch. 3, Def. 1.7 / Thm. 1.9 (pp. 74–75), hypotheses on the multiplicity: `θ` is a
positive `Hⁿ`-measurable function on `M` with `∫_{M ∩ K} θ dHⁿ < ∞` for every compact `K`. -/
def IsPositiveLocallyIntegrableWeight (n : ℕ) (M : Set E) (θ : E → ℝ) : Prop :=
  (∀ x ∈ M, 0 < θ x) ∧ AEMeasurable θ ((μHE[n] : Measure E).restrict M) ∧
    ∀ K : Set E, IsCompact K → IntegrableOn θ (M ∩ K) μHE[n]

open Classical in
/-- The approximate tangent space `T_x M` of Simon Ch. 3, Def. 1.7 (p. 74) with respect to the
multiplicity `θ` (the unique `P` with `HasWeightedApproximateTangentSpaceAt n M θ x P` when
`θ x ≠ 0`; `⊥` if there is none). For `θ ≡ 1` this is Def. 1.4. -/
noncomputable def approxTangentPlane (n : ℕ) (M : Set E) (θ : E → ℝ) (x : E) : Submodule ℝ E :=
  if h : ∃ P : Submodule ℝ E, HasWeightedApproximateTangentSpaceAt n M θ x P then h.choose else ⊥

/-- Simon Ch. 3, (2.1)–(2.2) (pp. 75–76), with Ch. 2, (4.6)–(4.10), (4.15): `L : T → F` is the
induced linear map `d^M f_x` of `f` at `x` along the plane `T = T_x M`, i.e. for every `τ ∈ T`
the directional derivative `D_τ f(x) = d/dt f(x + tτ)|_{t=0}` exists and equals `L τ`.
(By Ch. 2 (4.10), for `f` locally Lipschitz on an open set this is the derivative along curves
in `M`.) -/
def HasTangentialDifferentialAt (T : Submodule ℝ E) (f : E → F) (x : E) (L : T →L[ℝ] F) : Prop :=
  ∀ τ : T, HasLineDerivAt ℝ f (L τ) x (τ : E)

open Classical in
/-- Simon Ch. 3, (2.2) (p. 76): `d^M f_x : T → F` (unique when it exists, `0` otherwise). -/
noncomputable def tangentialDifferential (T : Submodule ℝ E) (f : E → F) (x : E) : T →L[ℝ] F :=
  if h : ∃ L : T →L[ℝ] F, HasTangentialDifferentialAt T f x L then h.choose else 0

/-- Simon Ch. 3, (2.3) (p. 76): the area Jacobian `J^M_f = √det((d^M f_x)* ∘ d^M f_x)`
(Mathlib's `LinearMap.normDet`, whose square is `det(L* ∘ L)`). -/
noncomputable def areaJacobian (T : Submodule ℝ E) (f : E → F) (x : E) : ℝ :=
  (tangentialDifferential T f x).toLinearMap.normDet

/-- Simon Ch. 3, (2.7) (p. 77): the co-area Jacobian `J^{M*}_f = √det(d^M f_x ∘ (d^M f_x)*)`
(`normDet` of the adjoint). -/
noncomputable def coareaJacobian (T : Submodule ℝ E) (f : E → F) (x : E) : ℝ :=
  (LinearMap.adjoint (tangentialDifferential T f x).toLinearMap).normDet

/-- Simon Ch. 3, 4.3 (p. 81) (cf. Ch. 4, p. 86): the Radon measure `μ` has approximate tangent
space `P` with multiplicity `θ` at `x`: `finrank P = n` and for all `f ∈ C_c(E, ℝ)`,
`λ⁻ⁿ ∫ f(η_{x,λ}(y)) dμ(y) → θ ∫_P f dHⁿ` as `λ ↓ 0` (i.e. `λ⁻ⁿ η_{x,λ#} μ → θ Hⁿ ⌞ P`). -/
def HasApproxTangentPlaneWithMultiplicity (n : ℕ) (μ : Measure E) (x : E) (P : Submodule ℝ E)
    (θ : ℝ) : Prop :=
  finrank ℝ P = n ∧
    ∀ f : C_c(E, ℝ), Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ y, f (blowUpMap x r y) ∂μ) (𝓝[>] 0)
      (𝓝 (θ * ∫ y in (P : Set E), f y ∂μHE[n]))

end GeneralDefinitions

/-! ### Orthogonal projections (Simon §3) -/

/-- Simon Ch. 3, 3.3 (p. 78): the orthogonal projection `p_{j₁,…,jₙ}` of `ℝᴺ` onto
`span{e_j : j ∈ J}`. -/
noncomputable def coordinateProjection {N : ℕ} (J : Finset (Fin N)) : Rn N →L[ℝ] Rn N :=
  (Submodule.span ℝ ((fun j ↦ EuclideanSpace.single j (1 : ℝ)) '' (J : Set (Fin N)))).starProjection

/-- The orthogonal projection of `ℝᴺ` onto the span of the frame `v = (v₁, …, vₙ)`. -/
noncomputable def frameProjection {N n : ℕ} (v : Fin n → Rn N) : Rn N →L[ℝ] Rn N :=
  (Submodule.span ℝ (Set.range v)).starProjection

/-- Simon Ch. 3, 3.6/3.8 (p. 80): "`P(p)` holds for `σ`-almost all `p ∈ O(N, n)`", `σ` the Haar
(`O(N)`-invariant) measure on the orthogonal projections of `ℝᴺ` onto `n`-dimensional subspaces.
Encoded through frames: for Lebesgue-a.e. `v ∈ (ℝᴺ)ⁿ` with `v` linearly independent,
`P(p_{span v})`. This has exactly the `σ`-null sets: `σ` is the law of `span v` for a standard
Gaussian `v` (by `O(N)`-invariance of the Gaussian and uniqueness of the invariant probability on
the Grassmannian), and the Gaussian has the same null sets as Lebesgue measure. -/
def ForAlmostAllProjections (N n : ℕ) (P : (Rn N →L[ℝ] Rn N) → Prop) : Prop :=
  ∀ᵐ v : Fin n → Rn N ∂volume, LinearIndependent ℝ v → P (frameProjection v)

/-! ### Sets of locally finite perimeter (Simon §4) -/

/-- Simon Ch. 3, §4 (p. 80): `E` has locally finite perimeter in `U` iff `χ_E ∈ BV_loc(U)`. -/
def HasLocallyFinitePerimeter {N : ℕ} (U E : Set (Rn N)) : Prop :=
  Poincare.SimonGMT.Chapter02.IsLocallyBV U (E.indicator fun _ ↦ (1 : ℝ))

/-- Simon Ch. 3, (4.1) (p. 80): `(μ, ν)` is the polar decomposition `D χ_E = ν μ`,
`μ = |D χ_E|`, of the vector Radon measure `D χ_E` on `U`: `μ` is a Radon measure on `U`
(Borel, vanishing off `U`, finite on compact subsets of `U`), `ν` is `μ`-measurable with `|ν| = 1`
`μ`-a.e., and `∫_{E ∩ U} div g dL^{N} = -∫_U g · ν dμ` for all `g ∈ C¹_c(U; ℝᴺ)`.
Such a pair exists iff `E` has locally finite perimeter, and it is unique
(`GaussGreenRepresentation`). -/
def IsGaussGreenPair {N : ℕ} (U E : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N) : Prop :=
  μ Uᶜ = 0 ∧ (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) ∧ AEStronglyMeasurable ν μ ∧
    (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
    ∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ x in E ∩ U, Poincare.SimonGMT.Chapter02.euclideanDivergence g x =
        -∫ x, inner ℝ (g x) (ν x) ∂μ

/-- The average `μ(B_ρ(x))⁻¹ ∫_{B_ρ(x)} ν dμ` of Simon Ch. 3, (4.2) (p. 81). -/
noncomputable def normalAverage {N : ℕ} (μ : Measure (Rn N)) (ν : Rn N → Rn N) (x : Rn N)
    (ρ : ℝ) : Rn N :=
  (μ (Metric.ball x ρ)).toReal⁻¹ • ∫ y in Metric.ball x ρ, ν y ∂μ

/-- Simon Ch. 3, (4.2) (p. 81): the reduced boundary
`∂*E = {x ∈ U : lim_{ρ↓0} ∫_{B_ρ(x)} ν dμ_E / μ_E(B_ρ(x)) exists and has length 1}`,
for the polar decomposition `(μ_E, ν)` of `D χ_E`. -/
def reducedBoundary {N : ℕ} (U : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N) :
    Set (Rn N) :=
  {x | x ∈ U ∧ ∃ v : Rn N, Tendsto (normalAverage μ ν x) (𝓝[>] 0) (𝓝 v) ∧ ‖v‖ = 1}

/-- Simon Ch. 3, 4.3 (p. 81): `ν_E(x) = lim_{ρ↓0} ∫_{B_ρ(x)} ν dμ_E / μ_E(B_ρ(x))`. -/
noncomputable def reducedNormal {N : ℕ} (μ : Measure (Rn N)) (ν : Rn N → Rn N) (x : Rn N) :
    Rn N :=
  limUnder (𝓝[>] (0 : ℝ)) (normalAverage μ ν x)

/-! ### The headline results -/

/-- **Simon Ch. 3, Lemma 1.2 (p. 69).** A set `M ⊆ ℝ^{n+ℓ}` is countably `n`-rectifiable iff
`M ⊆ N₀ ∪ ⋃_{j ≥ 1} N_j` with `Hⁿ(N₀) = 0` and each `N_j` an `n`-dimensional embedded `C¹`
submanifold of `ℝ^{n+ℓ}`. -/
def SubmanifoldCoverCharacterization : Prop :=
  ∀ (n ℓ : ℕ) (M : Set (Rn (n + ℓ))),
    CountablyRectifiable n M ↔
      ∃ (N₀ : Set (Rn (n + ℓ))) (N : ℕ → Set (Rn (n + ℓ))),
        μHE[n] N₀ = 0 ∧ (∀ j, IsC1Submanifold n (N j)) ∧ M ⊆ N₀ ∪ ⋃ j, N j

/-- **Simon Ch. 3, Theorem 1.6 (p. 71).** Let `M ⊆ ℝ^{n+ℓ}` be `Hⁿ`-measurable with
`Hⁿ(M ∩ K) < ∞` for every compact `K`. Then `M` is countably `n`-rectifiable iff the approximate
tangent space `T_x M` (Def. 1.4) exists for `Hⁿ`-a.e. `x ∈ M`. -/
def ApproximateTangentCharacterization : Prop :=
  ∀ (n ℓ : ℕ) (M : Set (Rn (n + ℓ))),
    NullMeasurableSet M μHE[n] → (∀ K : Set (Rn (n + ℓ)), IsCompact K → μHE[n] (M ∩ K) < ∞) →
      (CountablyRectifiable n M ↔
        ∀ᵐ x ∂(μHE[n] : Measure (Rn (n + ℓ))), x ∈ M →
          ∃ P : Submodule ℝ (Rn (n + ℓ)), HasApproximateTangentSpaceAt n M x P)

/-- **Simon Ch. 3, Theorem 1.9 (p. 75).** Let `M ⊆ ℝ^{n+ℓ}` be `Hⁿ`-measurable and `θ` a
positive `Hⁿ`-measurable function on `M` with `∫_{M ∩ K} θ dHⁿ < ∞` for every compact `K`.
Then `M` is countably `n`-rectifiable iff `M` has an approximate tangent space `T_x M` with
respect to `θ` (Def. 1.7) for `Hⁿ`-a.e. `x ∈ M`. -/
def WeightedApproximateTangentCharacterization : Prop :=
  ∀ (n ℓ : ℕ) (M : Set (Rn (n + ℓ))) (θ : Rn (n + ℓ) → ℝ),
    NullMeasurableSet M μHE[n] → IsPositiveLocallyIntegrableWeight n M θ →
      (CountablyRectifiable n M ↔
        ∀ᵐ x ∂(μHE[n] : Measure (Rn (n + ℓ))), x ∈ M →
          ∃ P : Submodule ℝ (Rn (n + ℓ)), HasWeightedApproximateTangentSpaceAt n M θ x P)

/-- **Simon Ch. 3, area formula (2.4)–(2.5) (pp. 76–77).** Let `M ⊆ ℝ^{n+ℓ}` be `Hⁿ`-measurable
and countably `n`-rectifiable, `U ⊇ M` open and `f : U → ℝ^{n+ℓ₁}` locally Lipschitz. Here
`T_x M` is the approximate tangent space of Def. 1.7 for an arbitrary positive locally
`Hⁿ`-integrable `θ` on `M` (by 1.9 it exists `Hⁿ`-a.e. and a.e. agrees with `T_x N_j` on `M_j`
as in 2.1; for locally `Hⁿ`-finite `M`, `θ ≡ 1` gives Def. 1.4). Then for `Hⁿ`-a.e. `x ∈ M`,
`T_x M` and `d^M f_x : T_x M → ℝ^{n+ℓ₁}` exist, and
(2.4) `∫_A J^M_f dHⁿ = ∫ H⁰(A ∩ f⁻¹(y)) dHⁿ(y)` for every `Hⁿ`-measurable `A ⊆ M`;
(2.5) `∫_M h J^M_f dHⁿ = ∫ (∑_{x ∈ M ∩ f⁻¹(y)} h(x)) dHⁿ(y)` for `Hⁿ`-measurable `h ≥ 0`.
Erratum: the outer integrals are over the target `ℝ^{n+ℓ₁}` (printed `ℝ^{n+ℓ}`). -/
def AreaFormula : Prop :=
  ∀ (n ℓ ℓ₁ : ℕ) (M U : Set (Rn (n + ℓ))) (θ : Rn (n + ℓ) → ℝ) (f : Rn (n + ℓ) → Rn (n + ℓ₁)),
    NullMeasurableSet M μHE[n] → CountablyRectifiable n M → IsPositiveLocallyIntegrableWeight n M θ →
      IsOpen U → M ⊆ U → LocallyLipschitzOn U f →
      (∀ᵐ x ∂(μHE[n] : Measure (Rn (n + ℓ))), x ∈ M →
          ∃ (P : Submodule ℝ (Rn (n + ℓ))) (L : P →L[ℝ] Rn (n + ℓ₁)),
            HasWeightedApproximateTangentSpaceAt n M θ x P ∧ HasTangentialDifferentialAt P f x L) ∧
      (∀ A ⊆ M, NullMeasurableSet A μHE[n] →
          ∫⁻ x in A, ENNReal.ofReal (areaJacobian (approxTangentPlane n M θ x) f x) ∂μHE[n] =
            ∫⁻ y, ((A ∩ f ⁻¹' {y}).encard : ℝ≥0∞) ∂μHE[n]) ∧
      ∀ h : Rn (n + ℓ) → ℝ≥0∞, AEMeasurable h ((μHE[n] : Measure (Rn (n + ℓ))).restrict M) →
        ∫⁻ x in M, h x * ENNReal.ofReal (areaJacobian (approxTangentPlane n M θ x) f x) ∂μHE[n] =
          ∫⁻ y, ∑' x : ↥(M ∩ f ⁻¹' {y}), h x ∂μHE[n]

/-- **Simon Ch. 3, co-area formula (2.8)–(2.9) (p. 77).** Let `n = m + k` with `m < n`,
`M ⊆ ℝ^{n+ℓ}` `Hⁿ`-measurable and countably `n`-rectifiable, `U ⊇ M` open and `f : U → ℝᵐ`
locally Lipschitz; `T_x M` as in `AreaFormula`. Then for `Hⁿ`-a.e. `x ∈ M`, `T_x M` and
`d^M f_x` exist, and for every `Hⁿ`-measurable `A ⊆ M`:
(2.8) `∫_A J^{M*}_f dHⁿ = ∫_{ℝᵐ} Hᵏ(A ∩ f⁻¹(y)) dLᵐ(y)`;
(2.9) `∫_A g J^{M*}_f dHⁿ = ∫_{ℝᵐ} ∫_{A ∩ f⁻¹(y)} g dHᵏ dLᵐ(y)` for `Hⁿ`-measurable `g ≥ 0`.
Erratum: (2.9) is printed with `f⁻¹(y) ∩ M` on the right; the domains must agree. -/
def CoareaFormula : Prop :=
  ∀ (m k ℓ : ℕ), 0 < k →
    ∀ (M U : Set (Rn (m + k + ℓ))) (θ : Rn (m + k + ℓ) → ℝ) (f : Rn (m + k + ℓ) → Rn m),
      NullMeasurableSet M μHE[m + k] → CountablyRectifiable (m + k) M →
        IsPositiveLocallyIntegrableWeight (m + k) M θ → IsOpen U → M ⊆ U → LocallyLipschitzOn U f →
        (∀ᵐ x ∂(μHE[m + k] : Measure (Rn (m + k + ℓ))), x ∈ M →
            ∃ (P : Submodule ℝ (Rn (m + k + ℓ))) (L : P →L[ℝ] Rn m),
              HasWeightedApproximateTangentSpaceAt (m + k) M θ x P ∧
                HasTangentialDifferentialAt P f x L) ∧
        (∀ A ⊆ M, NullMeasurableSet A μHE[m + k] →
            ∫⁻ x in A, ENNReal.ofReal (coareaJacobian (approxTangentPlane (m + k) M θ x) f x)
                ∂μHE[m + k] =
              ∫⁻ y, μHE[k] (A ∩ f ⁻¹' {y}) ∂volume) ∧
        ∀ A ⊆ M, NullMeasurableSet A μHE[m + k] →
          ∀ g : Rn (m + k + ℓ) → ℝ≥0∞,
            AEMeasurable g ((μHE[m + k] : Measure (Rn (m + k + ℓ))).restrict A) →
            ∫⁻ x in A, g x * ENNReal.ofReal (coareaJacobian (approxTangentPlane (m + k) M θ x) f x)
                ∂μHE[m + k] =
              ∫⁻ y, (∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]) ∂volume

/-- **Simon Ch. 3, Remark 2.10(2) (p. 77).** In the setting of the co-area formula (`n = m + k`,
`m < n`, `M` `Hⁿ`-measurable countably `n`-rectifiable, `f` locally Lipschitz on an open
`U ⊇ M`), the slices `M ∩ f⁻¹(y)` are countably `k`-rectifiable for `Lᵐ`-a.e. `y ∈ ℝᵐ`. -/
def SlicesAreRectifiable : Prop :=
  ∀ (m k ℓ : ℕ), 0 < k →
    ∀ (M U : Set (Rn (m + k + ℓ))) (f : Rn (m + k + ℓ) → Rn m),
      NullMeasurableSet M μHE[m + k] → CountablyRectifiable (m + k) M → IsOpen U → M ⊆ U →
        LocallyLipschitzOn U f → ∀ᵐ y ∂(volume : Measure (Rn m)), CountablyRectifiable k (M ∩ f ⁻¹' {y})

/-- **Simon Ch. 3, Lemma 3.2 (p. 78).** If `A = ⋃ⱼ Aⱼ ⊆ ℝ^{n+ℓ}` with `Hⁿ(Aⱼ) < ∞`, then
`A = R ∪ P` (disjoint) with `R` countably `n`-rectifiable and `P` purely `n`-unrectifiable;
if `A` is `Hⁿ`-measurable, `R` can be chosen Borel. -/
def RectifiableDecomposition : Prop :=
  ∀ (n ℓ : ℕ) (A : Set (Rn (n + ℓ))),
    (∃ Aj : ℕ → Set (Rn (n + ℓ)), A = ⋃ j, Aj j ∧ ∀ j, μHE[n] (Aj j) < ∞) →
      (∃ R P : Set (Rn (n + ℓ)), A = R ∪ P ∧ Disjoint R P ∧ CountablyRectifiable n R ∧
          PurelyUnrectifiable n P) ∧
        (NullMeasurableSet A μHE[n] →
          ∃ R P : Set (Rn (n + ℓ)), A = R ∪ P ∧ Disjoint R P ∧ MeasurableSet R ∧
            CountablyRectifiable n R ∧ PurelyUnrectifiable n P)

/-- **Simon Ch. 3, Lemma 3.3 (p. 78).** If `S ⊆ ℝ^{n+ℓ}` and `Hⁿ(p_{j₁,…,jₙ}(S)) = 0` for every
`1 ≤ j₁ < ⋯ < jₙ ≤ n + ℓ` (`p_{j₁,…,jₙ}` the orthogonal projection onto
`span{e_{j₁}, …, e_{jₙ}}`), then `S` is purely `n`-unrectifiable. -/
def CoordinateProjectionCriterion : Prop :=
  ∀ (n ℓ : ℕ) (S : Set (Rn (n + ℓ))),
    (∀ J : Finset (Fin (n + ℓ)), J.card = n → μHE[n] (coordinateProjection J '' S) = 0) →
      PurelyUnrectifiable n S

/-- **Simon Ch. 3, Theorem 3.6 (p. 80), Besicovitch–Federer structure theorem.** If
`Q ⊆ ℝ^{n+ℓ}` is purely `n`-unrectifiable and `Q = ⋃ⱼ Qⱼ` with `Hⁿ(Qⱼ) < ∞`, then
`Hⁿ(p(Q)) = 0` for `σ`-almost all `p ∈ O(n+ℓ, n)` (`σ` the Haar measure on the orthogonal
projections onto `n`-planes; see `ForAlmostAllProjections`). -/
def BesicovitchFedererProjectionTheorem : Prop :=
  ∀ (n ℓ : ℕ) (Q : Set (Rn (n + ℓ))), PurelyUnrectifiable n Q →
    (∃ Qj : ℕ → Set (Rn (n + ℓ)), Q = ⋃ j, Qj j ∧ ∀ j, μHE[n] (Qj j) < ∞) →
      ForAlmostAllProjections (n + ℓ) n (fun p ↦ μHE[n] (p '' Q) = 0)

/-- **Simon Ch. 3, Theorem 3.8 (p. 80), rectifiability theorem for sets.** If `A = ⋃ⱼ Aⱼ ⊆
ℝ^{n+ℓ}` with `Hⁿ(Aⱼ) < ∞`, and every `B ⊆ A` with `Hⁿ(B) > 0` has `Hⁿ(p(B)) > 0` for a set of
`p ∈ O(n+ℓ, n)` of positive `σ`-measure (i.e. not for `σ`-a.e. `p` is `Hⁿ(p(B)) = 0`), then `A`
is countably `n`-rectifiable. -/
def RectifiabilityTheoremForSets : Prop :=
  ∀ (n ℓ : ℕ) (A : Set (Rn (n + ℓ))),
    (∃ Aj : ℕ → Set (Rn (n + ℓ)), A = ⋃ j, Aj j ∧ ∀ j, μHE[n] (Aj j) < ∞) →
      (∀ B ⊆ A, 0 < μHE[n] B → ¬ ForAlmostAllProjections (n + ℓ) n (fun p ↦ μHE[n] (p '' B) = 0)) →
        CountablyRectifiable n A

/-- **Simon Ch. 3, (4.1) (p. 80).** For `U ⊆ ℝ^{n+1}` open and `E` `L^{n+1}`-measurable, `E` has
locally finite perimeter in `U` (`χ_E ∈ BV_loc(U)`) iff there are a Radon measure `μ_E` on `U` and
a `μ_E`-measurable `ν` with `|ν| = 1` `μ_E`-a.e. satisfying the Gauss–Green identity (4.1); such
a pair is unique (`μ_E = |D χ_E|`, and `ν` is unique `μ_E`-a.e.). -/
def GaussGreenRepresentation : Prop :=
  ∀ (n : ℕ) (U E : Set (Rn (n + 1))), IsOpen U → NullMeasurableSet E volume →
    (HasLocallyFinitePerimeter U E ↔ ∃ (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)),
        IsGaussGreenPair U E μ ν) ∧
      ∀ (μ μ' : Measure (Rn (n + 1))) (ν ν' : Rn (n + 1) → Rn (n + 1)),
        IsGaussGreenPair U E μ ν → IsGaussGreenPair U E μ' ν' → μ = μ' ∧ ν =ᵐ[μ] ν'

/-- **Simon Ch. 3, Theorem 4.3 (p. 81), De Giorgi.** Let `U ⊆ ℝ^{n+1}` be open and `E` an
`L^{n+1}`-measurable set of locally finite perimeter in `U`, with Gauss–Green pair
`(μ_E, ν)` (which exists). Then the reduced boundary `∂*E` is countably `n`-rectifiable and
`μ_E = Hⁿ ⌞ ∂*E`. At every `x ∈ ∂*E`: (‡) the approximate tangent space of `μ_E` exists, has
multiplicity `1`, and equals `{y : y · ν_E(x) = 0}`; (‡‡) `E_{x,λ} = η_{x,λ}(E) → {y : y · ν_E(x) > 0}`
in `L¹_loc(ℝ^{n+1})` as `λ ↓ 0` (Lebesgue measure of the symmetric difference within every
compact set tends to `0`). -/
def DeGiorgiTheorem : Prop :=
  ∀ (n : ℕ) (U E : Set (Rn (n + 1))), IsOpen U → NullMeasurableSet E volume →
    HasLocallyFinitePerimeter U E →
      (∃ (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)), IsGaussGreenPair U E μ ν) ∧
      ∀ (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)), IsGaussGreenPair U E μ ν →
        CountablyRectifiable n (reducedBoundary U μ ν) ∧
        μ = (μHE[n] : Measure (Rn (n + 1))).restrict (reducedBoundary U μ ν) ∧
        (∀ x ∈ reducedBoundary U μ ν, HasApproxTangentPlaneWithMultiplicity n μ x
          ((Submodule.span ℝ {reducedNormal μ ν x})ᗮ) 1) ∧
        ∀ x ∈ reducedBoundary U μ ν, ∀ K : Set (Rn (n + 1)), IsCompact K →
          Tendsto (fun r : ℝ ↦ volume (K ∩ symmDiff (blowUpMap x r '' E)
              {y | 0 < inner ℝ y (reducedNormal μ ν x)})) (𝓝[>] 0) (𝓝 0)

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1`
- Child DAG node: `root.de_giorgi-a1.density_estimates-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof Parts 1c, 2 and 3e: Simon, Ch. 3, proof of Theorem 4.3, (1)-(6) (chapter-03.txt lines 607-652) and the Sobolev step leading to (10), (11) (lines 689-733), with erratum E5 (the complement is handled with the pair (μ, −ν) of sibling compl_pair) and erratum E6 (for n = 0 the Sobolev inequality is replaced by its one-dimensional L^∞ form). Here the point x and the unit vector e = ν_E(x) are kept general instead of normalizing to x = 0, e = e_N (parent Part 1b); the argument is unchanged.

Notation. N := n + 1; L^N = volume; B_ρ := B_ρ(x) (open), B̄_ρ := closed ball; ω_N := L^N(B_1(0)); m(ρ) := μ(B_ρ); V(ρ) := L^N(E ∩ B_ρ) and V_c(ρ) := L^N(B_ρ ∖ E) (finite and non-decreasing in ρ); for a Lipschitz ζ, ∇ζ is its a.e. gradient (Rademacher); div g = euclideanDivergence g; φ_σ (σ > 0) is a standard mollifier (C^∞, ≥ 0, even, ∫φ_σ = 1, spt φ_σ ⊆ B̄_σ(0)). IsGaussGreenPair U E μ ν gives (a) μ(Uᶜ) = 0, (b) μ(K) < ∞ for compact K ⊆ U, (c) ν μ-a.e. strongly measurable, (d) |ν| = 1 μ-a.e., (e) (GG) ∫_{E∩U} div g = −∫⟨g, ν⟩ dμ for C¹ g with compact support and tsupport g ⊆ U. By sibling compl_pair, (μ, −ν) is a Gauss-Green pair for (U, U ∖ E).

Step 0 (the unit vector e). Since x ∈ ∂*E, x ∈ U and there is v with |v| = 1 and normalAverage(x, ρ) → v as ρ ↓ 0. The filter 𝓝[>]0 on ℝ is non-trivial and ℝ^N is Hausdorff, so e = reducedNormal μ ν x = limUnder (𝓝[>]0) (normalAverage μ ν x) = v; thus |e| = 1.

Step 1 (radius ρ₀ and positivity; parent 1c). Choose ρ₀ > 0 with B̄_{ρ₀} ⊆ U. For 0 < ρ ≤ ρ₀, m(ρ) ≤ μ(B̄_{ρ₀}) < ∞ by (b). For every ρ > 0, m(ρ) > 0: otherwise m(ρ') = 0 for all ρ' ∈ (0, ρ], hence ∫_{B_{ρ'}} ν dμ = 0 and normalAverage(x, ρ') = 0 for those ρ', so the limit e would be 0, contradicting |e| = 1.

Step 2 (Simon (1) and (2)). For 0 < ρ ≤ ρ₀, ν is μ-integrable on B_ρ (|ν| ≤ 1 a.e., finite measure), normalAverage(x, ρ) = m(ρ)⁻¹ ∫_{B_ρ} ν dμ, and
 a(ρ) := ⟨normalAverage(x, ρ), e⟩ = m(ρ)⁻¹ ∫_{B_ρ} ⟨ν, e⟩ dμ → ⟨e, e⟩ = 1 as ρ ↓ 0; also a(ρ) ≤ 1.
Since |ν| = |e| = 1 μ-a.e., |ν − e|² = 2(1 − ⟨ν, e⟩) μ-a.e., and by the Cauchy-Schwarz inequality
 (2') ∫_{B_ρ} |ν − e| dμ ≤ m(ρ)^{1/2} (∫_{B_ρ} |ν − e|² dμ)^{1/2} = m(ρ) (2(1 − a(ρ)))^{1/2}.

Step 3 (Gauss-Green for Lipschitz fields; Simon (3)). Claim: (GG) holds for every Lipschitz g : ℝ^N → ℝ^N with compact support and tsupport g ⊆ U, for the pair (U, E, μ, ν) and for the pair (U, U ∖ E, μ, −ν). Proof: choose σ₀ > 0 with K' := {y : dist(y, tsupport g) ≤ σ₀} ⊆ U (K' is compact; tsupport g is a compact subset of the open set U), and put g_σ := φ_σ * g. For σ < σ₀, g_σ is C^∞ with tsupport g_σ ⊆ K' ⊆ U, so (GG) holds for g_σ. As σ → 0, g_σ → g uniformly (g is uniformly continuous). If g is L-Lipschitz, g is differentiable a.e. with |Dg| ≤ L, and for each direction w the difference quotients (g(· + tw) − g)/t are bounded by L|w| and converge a.e. to Dg(·)w; convolving with φ_σ and using dominated convergence, D g_σ(·)w = φ_σ * (Dg(·)w). Hence div g_σ = φ_σ * div g, |div g_σ| ≤ NL, and div g_σ → div g a.e. as σ → 0 (Lebesgue differentiation theorem). All these functions vanish off K', L^N(K') < ∞, μ(K') < ∞ and |⟨g_σ, ν⟩| ≤ sup|g| μ-a.e.; dominated convergence on both sides of (GG) for g_σ gives (GG) for g.
 Consequences. Let ζ : ℝ^N → ℝ be Lipschitz with compact support and tsupport ζ ⊆ U and let |w| = 1. Applying the claim to g := ζw (div g = ⟨∇ζ, w⟩ a.e., ⟨g, ν⟩ = ζ⟨w, ν⟩) and using ∇ζ = 0 a.e. outside U:
 (3) ∫ ζ⟨ν, w⟩ dμ = −∫_E ⟨∇ζ, w⟩ dL^N ≤ ∫_E |∇ζ| dL^N;
and applying it to the pair (μ, −ν) for (U, U ∖ E) with the vector −w:
 (3c) ∫ ζ⟨ν, w⟩ dμ = ∫ ζ⟨−ν, −w⟩ dμ = −∫_{U∖E} ⟨∇ζ, −w⟩ dL^N ≤ ∫_{U∖E} |∇ζ| dL^N.

Step 4 (Simon (4), (5)). V and V_c are non-decreasing, hence differentiable at a.e. ρ (Lebesgue; Mathlib Monotone.ae_differentiableAt). Fix ρ ∈ (0, ρ₀) at which V and V_c are differentiable. For k ∈ ℕ with 1/k < ρ let ζ_k(y) := φ_k(|y − x|), where φ_k(t) = 1 for t ≤ ρ − 1/k, φ_k(t) = k(ρ − t) for ρ − 1/k ≤ t ≤ ρ, φ_k(t) = 0 for t ≥ ρ. Then ζ_k is k-Lipschitz, 0 ≤ ζ_k ≤ 1, tsupport ζ_k = B̄_ρ ⊆ U, ζ_k is non-decreasing in k and ζ_k → 1_{B_ρ} pointwise. On the open annulus A_k := {ρ − 1/k < |y − x| < ρ}, ∇ζ_k(y) = −k(y − x)/|y − x| has length k; ∇ζ_k = 0 on the open sets {|y − x| < ρ − 1/k} and {|y − x| > ρ}; the two spheres are L^N-null. Hence
 ∫_E |∇ζ_k| = k L^N(E ∩ A_k) = k(V(ρ) − V(ρ − 1/k)) → V'(ρ), and likewise ∫_{U∖E} |∇ζ_k| = k(V_c(ρ) − V_c(ρ − 1/k)) → V_c'(ρ) (A_k ⊆ B_ρ ⊆ U).
By dominated convergence (|ζ_k⟨ν, e⟩| ≤ 1_{B̄_ρ} μ-a.e., μ(B̄_ρ) < ∞), ∫ ζ_k⟨ν, e⟩ dμ → ∫_{B_ρ} ⟨ν, e⟩ dμ. So (3) and (3c) with w = e give
 (5) ∫_{B_ρ} ⟨ν, e⟩ dμ ≤ min(V'(ρ), V_c'(ρ)) for a.e. ρ ∈ (0, ρ₀).
Moreover, for ρ' < ρ, V(ρ) − V(ρ') ≤ L^N(B_ρ ∖ B_{ρ'}) = ω_N(ρ^N − ρ'^N), so V'(ρ) ≤ Nω_N ρⁿ; likewise V_c'(ρ) ≤ Nω_N ρⁿ.

Step 5 (Simon (6) and the mass bound (6')). By Step 2 choose ρ₁ ∈ (0, ρ₀) with a(ρ) ≥ 1/2, i.e. ∫_{B_ρ} ⟨ν, e⟩ dμ ≥ m(ρ)/2, for all ρ ∈ (0, ρ₁). Then (5) gives, for a.e. ρ ∈ (0, ρ₁),
 (6) m(ρ) ≤ 2V'(ρ), m(ρ) ≤ 2V_c'(ρ), m(ρ) ≤ 2Nω_N ρⁿ.
For an arbitrary ρ ∈ (0, ρ₁) choose ρ_j ↓ ρ in (ρ, ρ₁) outside the exceptional null set; by monotonicity m(ρ) ≤ m(ρ_j) ≤ 2Nω_N ρ_jⁿ → 2Nω_N ρⁿ. Hence, with C := 2Nω_N,
 (6') μ(B_ρ(x)) ≤ Cρⁿ for every ρ ∈ (0, ρ₁).
Also B_{ρ₁} ⊆ B̄_{ρ₀} ⊆ U.

Step 6 (excess decay). For ρ ∈ (0, ρ₁), by (2') and (6'):
 0 ≤ (ρⁿ)⁻¹ ∫_{B_ρ} |ν − e| dμ ≤ (ρⁿ)⁻¹ m(ρ) (2(1 − a(ρ)))^{1/2} ≤ C (2(1 − a(ρ)))^{1/2} → 0 as ρ ↓ 0 (Step 2).

Step 7 (the Sobolev step (S); Simon lines 689-705, errata E5, E6). Constants: for N ≥ 2 let c_N be the Gagliardo-Nirenberg-Sobolev constant, ‖w‖_{L^{N/(N−1)}} ≤ c_N ∫ |∇w| for w ∈ C¹_c(ℝ^N) ([GT01, Thm 7.10]; Mathlib eLpNorm_le_eLpNorm_fderiv_of_eq); for N = 1, sup|w| ≤ ½ ∫ |w'| for w ∈ C¹_c(ℝ) (w(t) = ∫_{−∞}^t w' = −∫_t^∞ w'). Both extend to Lipschitz w with compact support: apply them to φ_τ * w ∈ C^∞_c, note ∫|∇(φ_τ * w)| = ∫|φ_τ * ∇w| ≤ ∫|∇w|, and let τ → 0 (φ_τ * w → w uniformly with supports in a fixed compact set).
Let G ∈ {E, U ∖ E} with Gauss-Green pair (μ, ν_G), where ν_G := ν if G = E and ν_G := −ν if G = U ∖ E (sibling compl_pair). Let ζ ≥ 0 be Lipschitz with compact support and tsupport ζ ⊆ U. Claim:
 (S) if N ≥ 2: ‖ζχ_G‖_{L^{N/(N−1)}} ≤ c_N (∫ ζ dμ + ∫_G |∇ζ|); if N = 1: ess sup ζχ_G ≤ ½ (∫ ζ dμ + ∫_G |∇ζ|).
Proof. Fix σ₀ > 0 with K' := {y : dist(y, tsupport ζ) ≤ 2σ₀} ⊆ U. For σ ∈ (0, σ₀) let u_σ := φ_σ * χ_G (C^∞, 0 ≤ u_σ ≤ 1, ∇u_σ = (∇φ_σ) * χ_G) and w_σ := ζ u_σ (Lipschitz with compact support); then ∫|∇w_σ| ≤ ∫ ζ|∇u_σ| + ∫ u_σ|∇ζ|.
 (a) Let g : ℝ^N → ℝ^N be continuous with compact support and |g| ≤ ζ pointwise, and put g̃(z) := ∫ g(y) φ_σ(y − z) dy. Then g̃ is C^∞, tsupport g̃ ⊆ tsupport ζ + B̄_σ(0) ⊆ K' ⊆ U, |g̃| ≤ ζ̃_σ := ∫ ζ(y) φ_σ(y − ·) dy, and div g̃(z) = −∫ ⟨g(y), ∇φ_σ(y − z)⟩ dy. By Fubini, ∫ ⟨g, ∇u_σ⟩ = ∫_G ∫ ⟨g(y), ∇φ_σ(y − z)⟩ dy dz = −∫_G div g̃ = −∫_{G∩U} div g̃ = ∫ ⟨g̃, ν_G⟩ dμ ≤ ∫ ζ̃_σ dμ, by (GG) for (U, G, μ, ν_G) and |ν_G| = 1 μ-a.e. Taking g_j := ζ ∇u_σ/(|∇u_σ| + 1/j) (continuous, compact support, |g_j| ≤ ζ) and letting j → ∞ (monotone convergence) gives ∫ ζ|∇u_σ| ≤ ∫ ζ̃_σ dμ.
 (b) As σ → 0: ζ̃_σ → ζ uniformly with supports in K' and μ(K') < ∞, so ∫ ζ̃_σ dμ → ∫ ζ dμ; along a sequence σ_j → 0, u_{σ_j} → χ_G a.e. (Lebesgue differentiation theorem) with 0 ≤ u_{σ_j} ≤ 1, so ∫ u_{σ_j}|∇ζ| → ∫_G |∇ζ| and w_{σ_j} → ζχ_G a.e.
 (c) If N ≥ 2, Fatou's lemma and the Lipschitz Sobolev inequality give ‖ζχ_G‖_{N/(N−1)} ≤ liminf_j ‖w_{σ_j}‖_{N/(N−1)} ≤ c_N liminf_j ∫ |∇w_{σ_j}| ≤ c_N (∫ ζ dμ + ∫_G |∇ζ|). If N = 1, ess sup ζχ_G ≤ liminf_j sup|w_{σ_j}| ≤ ½ liminf_j ∫ |w_{σ_j}'| ≤ ½ (∫ ζ dμ + ∫_G |∇ζ|).

Step 8 (lower volume bounds (10), (11); Simon lines 706-733). Let G ∈ {E, U ∖ E} and V_G := V resp. V_c; for 0 < ρ ≤ ρ₀ we have G ∩ B_ρ = E ∩ B_ρ resp. B_ρ ∖ E, since B_ρ ⊆ U.
 (i) V_G(ρ) > 0 for every ρ ∈ (0, ρ₁). Otherwise χ_G = 0 a.e. on B_ρ. Take ρ' ∈ (0, ρ) and the cut-offs ζ_k of Step 4 built with ρ' in place of ρ. Step 3 for the pair (μ, ν_G) with w_G := e (G = E) resp. w_G := −e (G = U ∖ E), for which ⟨ν_G, w_G⟩ = ⟨ν, e⟩, gives ∫ ζ_k⟨ν, e⟩ dμ = −∫_G ⟨∇ζ_k, w_G⟩ = 0, because ∇ζ_k vanishes outside B_{ρ'} ⊆ B_ρ, where χ_G = 0 a.e. Letting k → ∞ (dominated convergence) gives ∫_{B_{ρ'}} ⟨ν, e⟩ dμ = 0, contradicting ∫_{B_{ρ'}} ⟨ν, e⟩ dμ ≥ m(ρ')/2 > 0 (Steps 1 and 5).
 (ii) Let ρ ∈ (0, ρ₁) be such that V and V_c are differentiable at ρ and (6) holds at ρ (this is a.e. ρ). Apply (S) with ζ = ζ_k from Step 4 and let k → ∞: ∫ ζ_k dμ ≤ m(ρ) (ζ_k ≤ 1_{B_ρ}); ∫_G |∇ζ_k| → V_G'(ρ); and, for N ≥ 2, ‖ζ_kχ_G‖_{N/(N−1)} ↑ V_G(ρ)^{(N−1)/N} (monotone convergence, ζ_k ↑ 1_{B_ρ}). Hence V_G(ρ)^{(N−1)/N} ≤ c_N(m(ρ) + V_G'(ρ)) ≤ 3c_N V_G'(ρ) by (6). For N = 1: since V_G(ρ) > 0 and L^1(G ∩ B_{ρ−1/k}) ↑ V_G(ρ), for large k the set G ∩ B_{ρ−1/k}, on which ζ_kχ_G = 1, has positive measure; so ess sup ζ_kχ_G = 1 and 1 ≤ ½(m(ρ) + V_G'(ρ)) ≤ (3/2)V_G'(ρ).
 (iii) Integration (Simon: "Integration (using the fact that L^{n+1}(E ∩ B_ρ(0)) is non-decreasing) then implies (10)"). If N ≥ 2, W := V_G^{1/N} is non-decreasing on [0, ρ₁], and at each ρ as in (ii) we have V_G(ρ) > 0 and V_G'(ρ) > 0, so W is differentiable at ρ with W'(ρ) = V_G'(ρ)/(N V_G(ρ)^{(N−1)/N}) ≥ 1/(3Nc_N). For 0 < ε < ρ < ρ₁, the integral of the a.e. derivative of a non-decreasing function is at most its increment (Mathlib MonotoneOn.intervalIntegral_deriv_mem_uIcc), so W(ρ) ≥ W(ρ) − W(ε) ≥ ∫_ε^ρ W' ≥ (ρ − ε)/(3Nc_N); letting ε ↓ 0, V_G(ρ) ≥ (3Nc_N)^{−N} ρ^N. If N = 1, V_G' ≥ 2/3 a.e. on (0, ρ₁), and in the same way V_G(ρ) ≥ (2/3)ρ.
 Hence, with c := (3Nc_N)^{−N} if N ≥ 2 and c := 2/3 if N = 1 (so c > 0): L^N(E ∩ B_ρ) ≥ cρ^N (10) and L^N(B_ρ ∖ E) ≥ cρ^N (11) for every ρ ∈ (0, ρ₁).

Step 9 (conclusion). ρ₁ > 0 and B_{ρ₁}(x) ⊆ U (Step 5); with C = 2Nω_N and c > 0 as above, (6'), (10) and (11) hold for every ρ ∈ (0, ρ₁) as inequalities of real numbers, hence as the stated inequalities μ(B_ρ(x)) ≤ ENNReal.ofReal(Cρⁿ), ENNReal.ofReal(cρ^{n+1}) ≤ L^N(E ∩ B_ρ(x)) and ENNReal.ofReal(cρ^{n+1}) ≤ L^N(B_ρ(x) ∖ E) (N = n + 1). Step 6 gives (ρⁿ)⁻¹ ∫_{B_ρ(x)} |ν − e| dμ → 0 as ρ ↓ 0. ∎

## Key steps

1. e = reducedNormal μ ν x is the unit limit of normalAverage; μ(B_ρ(x)) ∈ (0, ∞) for 0 < ρ ≤ ρ₀; a(ρ) = ⟨normalAverage(x,ρ), e⟩ → 1 and ∫_{B_ρ}|ν − e|dμ ≤ μ(B_ρ)(2(1 − a(ρ)))^{1/2}.
2. (GG) extends to Lipschitz fields by mollification; with the complement pair (sibling compl_pair) this gives ∫ζ⟨ν, e⟩dμ ≤ min(∫_E|∇ζ|, ∫_{U∖E}|∇ζ|) (Simon (3)).
3. Radial piecewise-linear cut-offs ζ_k ↑ 1_{B_ρ}: ∫_{B_ρ}⟨ν,e⟩dμ ≤ min(V'(ρ), V_c'(ρ)) for a.e. ρ (5); with a(ρ) ≥ 1/2 this gives μ(B_ρ) ≤ 2V', 2V_c', 2Nω_Nρⁿ a.e. (6), and μ(B_ρ) ≤ Cρⁿ for all ρ < ρ₁ (6').
4. Excess decay: (ρⁿ)⁻¹∫_{B_ρ}|ν − e|dμ ≤ C(2(1 − a(ρ)))^{1/2} → 0.
5. Sobolev step (S) for G ∈ {E, U∖E} with the pair (μ, ±ν): mollify χ_G and bound ∫ζ|∇(φ_σ*χ_G)| ≤ ∫(φ_σ*ζ)dμ via (GG); for N = 1 use sup|w| ≤ ½∫|w'|.
6. V_G > 0 on (0, ρ₁); (S) with ζ_k gives V_G^{(N−1)/N} ≤ 3c_N V_G' a.e. (resp. V_G' ≥ 2/3 for N = 1); integrating the a.e. derivative of the monotone V_G^{1/N} yields V_G(ρ) ≥ cρ^N, i.e. (10), (11).

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean`
- `grep -n 'def IsGaussGreenPair|def normalAverage|def reducedBoundary|def reducedNormal|def HasApproxTangentPlaneWithMultiplicity|def DeGiorgiTheorem|def ApproximateTangentCharacterization|def GaussGreenRepresentation' <snapshot>/project/GMT/Ch03/Contract.lean`
- `grep -rn -i 'de.?giorgi|reducedBoundary' <snapshot>/mathlib/Mathlib .lake/packages/simongmt/Poincare`
- `grep -n -i 'compactness|arzela' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/*.lean`
- `grep -n 'def blowUpMap|def HasApproximateTangentSpaceAt|theorem countablyRectifiable_iUnion' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'def euclideanDivergence|support_euclideanDivergence_subset|euclideanDivergence_eq_sum_inner|def IsLocallyBV|isLocallyBV_of_locallyL1_of_uniform_bound' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `grep -rn 'simon_theorem_3_3|def dimensionalUpperDensity|def dimensionalDensityQuotient|simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure|def realUnitBallVolume' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n 'WeakDerivativesZero|constancyMollifier' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `grep 'theorem ae_tendsto_rnDeriv|theorem ae_tendsto_average|theorem tendsto_filterAt|protected def vitaliFamily' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering`
- `grep 'theorem Monotone.ae_differentiableAt|theorem eLpNorm_le_eLpNorm_fderiv_of_eq|theorem LipschitzWith.ae_differentiableAt|theorem tendsto_of_subseq_tendsto|theorem arzela_ascoli|theorem integral_Ioi_of_hasDerivAt_of_tendsto' <snapshot>/mathlib/Mathlib`
- `grep 'MonotoneOn.intervalIntegral_deriv_mem_uIcc|MonotoneOn.intervalIntegral_slope_le' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral`
- `grep 'StronglyMeasurable.integral_prod_right|measurable_measure_prodMk_left|measurableSet_exists_tendsto|StronglyMeasurable.limUnder' <snapshot>/mathlib/Mathlib`
- `grep 'euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_homothety_image|measurePreserving_euclideanHausdorffMeasure|theorem hausdorffMeasure_image|notation "μHE[' <snapshot>/mathlib/Mathlib`
- `grep 'withDensity_rnDeriv_eq|addHaar_image_homothety|theorem addHaar_smul|ae_convolution_tendsto_right_of_locallyIntegrable|finrank_orthogonal_span_singleton|LinearIsometryEquiv.measurePreserving|tendsto_measure_iUnion_atTop|Filter.Tendsto.limUnder_eq|HasCompactSupport.contDiff_convolution_left|OrthonormalBasis.volume_parallelepiped' <snapshot>/mathlib/Mathlib`
- `python3 -I (importlib of verifier/gmt-compare.py) contract_scope(Contract.lean, 'GMT.Ch03.main_theorem') -> NodeChallenge prefix; lake env lean /tmp/dg-decomp/challenges/Challenge_*.lean (10 files), /tmp/dg-decomp/Assembly.lean, /tmp/dg-decomp/Interfaces.lean`
- `python3 -I lean_name collision check against dag.json (73 nodes)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Polish/StronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/dg-decomp/Assembly.lean`
- `/tmp/dg-decomp/Interfaces.lean`

The snapshot contract is byte-identical to the workspace contract (project d09bc8a, Mathlib 25730c7c). Neither Mathlib nor the pinned SimonGMT has a De Giorgi theorem, BV subsequence compactness, a Lipschitz Gauss–Green identity, density estimates for the reduced boundary, half-space rigidity, or measurability of the reduced boundary. SimonGMT FinitePerimeter.lean records only the definitions, and BV.lean states that subsequence extraction 'remains the compactness obligation'. These obligations therefore become children. Library facts located for the child proofs: Besicovitch differentiation (VitaliFamily.ae_tendsto_average, Besicovitch.ae_tendsto_rnDeriv, Besicovitch.tendsto_filterAt); the Gagliardo–Nirenberg–Sobolev inequality (eLpNorm_le_eLpNorm_fderiv_of_eq); Monotone.ae_differentiableAt and MonotoneOn.intervalIntegral_deriv_mem_uIcc; Rademacher; Arzelà–Ascoli; a.e. convergence of mollifiers; product measurability; μHE scaling and isometry invariance; SimonGMT simon_theorem_3_3 with simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure; countablyRectifiable_iUnion; WeakDerivativesZero. All ten child types elaborate in the exact NodeChallenge scope. The parent assembly and the sibling-interface checks compile against stubs, with propext, Classical.choice, Quot.sound and the stubs' sorryAx as the only axioms. No lean_name collides with dag.json.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
