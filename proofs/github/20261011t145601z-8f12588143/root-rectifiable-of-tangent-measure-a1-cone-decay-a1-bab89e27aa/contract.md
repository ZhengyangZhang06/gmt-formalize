<!-- theorem-id: gmt-ch03/root.rectifiable_of_tangent_measure-a1.cone_decay-a1 -->

## Theorem `Submission.tangentMeasure_eventually_cone_small`

Let N, n ∈ ℕ with n ≥ 1, ℝ^N = EuclideanSpace ℝ (Fin N), and let μ be a Borel measure on ℝ^N with μ(K) < ∞ for every compact K ⊆ ℝ^N. Let x ∈ ℝ^N, P a linear subspace of ℝ^N and θ ∈ ℝ such that HasApproxTangentPlaneWithMultiplicity n μ x P θ holds (finrank P = n and (rⁿ)⁻¹ ∫ f(η_{x,r}(y)) dμ(y) → θ ∫_P f dHⁿ as r ↓ 0 for every f ∈ C_c(ℝ^N, ℝ), η_{x,r}(y) = r⁻¹(y − x), Hⁿ = μHE[n]). Let q_P = P.starProjection be the orthogonal projection onto P and C_x := {z : |q_P(z − x)| ≤ |z − x|/2}. Then for every ε > 0, μ(C_x ∩ B_ρ(x)) ≤ ε ρⁿ (as ENNReal.ofReal(ερⁿ)) for all sufficiently small ρ > 0, i.e. eventually in 𝓝[>] 0.

Node: `root.rectifiable_of_tangent_measure-a1.cone_decay-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/23

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.tangentMeasure_eventually_cone_small`

```lean
∀ (N n : ℕ) (μ : Measure (Rn N)) (x : Rn N) (P : Submodule ℝ (Rn N)) (θ : ℝ), (∀ K : Set (Rn N), IsCompact K → μ K < ∞) → 0 < n → HasApproxTangentPlaneWithMultiplicity n μ x P θ → ∀ ε : ℝ, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ ({z | ‖P.starProjection (z - x)‖ ≤ ‖z - x‖ / 2} ∩ Metric.ball x ρ) ≤ ENNReal.ofReal (ε * ρ ^ n)
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

- Parent DAG node: `root.rectifiable_of_tangent_measure-a1`
- Child DAG node: `root.rectifiable_of_tangent_measure-a1.cone_decay-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is Step 3 (6′) of the parent proof, i.e. Simon, Remark 1.5(3) (chapter-03.txt lines 97–105: approximate the indicator of X_{1/2}((T_xM)^⊥, 0) ∩ B_1(0) by test functions), with multiplicity θ. The parent's dominated-convergence step is replaced by the explicit estimate of Steps 1 and 4–5 below.

Notation. |·| is the Euclidean norm, q := q_P, and ν := Hⁿ⌞P = μHE[n].restrict P, so ∫_P f dHⁿ = ∫ f dν. Recall that |q v| ≤ |v| for all v (Mathlib `Submodule.norm_starProjection_apply_le`) and q w = w for w ∈ P (`Submodule.starProjection_eq_self_iff`).

1. ν is small near 0. Because finrank P = n, ν is finite on compact sets (SimonGMT `Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule`). Because n ≥ 1, the n-dimensional Hausdorff measure has no atoms (Mathlib `Measure.nullSingletonClass_hausdorff`), and μHE[n] is a scalar multiple of it, so ν({0}) ≤ μHE[n]({0}) = 0. The closed balls B̄_{1/(k+1)}(0), k ∈ ℕ, decrease, their intersection is {0}, and ν(B̄_1(0)) < ∞; by continuity from above (Mathlib `tendsto_measure_iInter_atTop`) ν(B̄_{1/(k+1)}(0)) → 0. Hence there is k ∈ ℕ with |θ| · ν(B̄_{1/(k+1)}(0)) < ε/2 (ν-values being finite reals). Put r := 1/(3(k+1)) > 0, so that 3r = 1/(k+1).

2. Cone and test function. Let S := {w : |q w| ≤ |w|/2} ∩ B̄_1(0). Then 0 ∈ S, so S ≠ ∅. Define f(w) := max(0, 1 − dist(w, S)/r). Since w ↦ dist(w, S) is 1-Lipschitz, f is continuous; 0 ≤ f ≤ 1; f = 1 on S (there dist(w, S) = 0); and f(w) = 0 whenever dist(w, S) ≥ r.

3. Compact support. If |w| > 1 + r, then dist(w, S) ≥ r: otherwise some s ∈ S has |w − s| < r, and then |w| ≤ |w − s| + |s| < r + 1, a contradiction. So f vanishes outside the compact ball B̄_{1+r}(0), and f ∈ C_c(ℝ^N, ℝ).

4. Localization on P. If w ∈ P and f(w) ≠ 0, then |w| < 3r. Indeed dist(w, S) < r gives s ∈ S with |w − s| < r. Then |w| = |q w| ≤ |q s| + |q(w − s)| ≤ |s|/2 + |w − s|, and |s| ≤ |w| + |w − s|; hence |w| ≤ |w|/2 + (3/2)|w − s| < |w|/2 + 3r/2, i.e. |w| < 3r.

5. Bound for the limit. By step 4 and 0 ≤ f ≤ 1, for every w ∈ P (so for ν-a.e. w) we have f(w) ≤ 1_{B̄_{3r}(0)}(w). Since ν(B̄_{3r}(0)) < ∞, monotonicity of the integral gives 0 ≤ ∫_P f dHⁿ ≤ ν(B̄_{3r}(0)). Therefore L := θ ∫_P f dHⁿ ≤ |θ| ∫_P f dHⁿ ≤ |θ| ν(B̄_{1/(k+1)}(0)) < ε/2 < ε.

6. Blow-up limit. By the hypothesis applied to f, (ρⁿ)⁻¹ J(ρ) → L as ρ ↓ 0, where J(ρ) := ∫ f(η_{x,ρ}(y)) dμ(y). Since L < ε there is ρ₀ > 0 with (ρⁿ)⁻¹ J(ρ) < ε, i.e. J(ρ) < ε ρⁿ, for all ρ ∈ (0, ρ₀).

7. Comparison. Fix ρ ∈ (0, ρ₀) and let T := C_x ∩ B_ρ(x). T is Borel (C_x is closed) and μ(T) ≤ μ(B̄_ρ(x)) < ∞. If y ∈ T and w := η_{x,ρ}(y) = ρ⁻¹(y − x), then |w| = |y − x|/ρ < 1 and |q w| = ρ⁻¹|q(y − x)| ≤ ρ⁻¹|y − x|/2 = |w|/2, so w ∈ S and f(w) = 1. Hence 1_T ≤ f∘η_{x,ρ} pointwise (f ≥ 0). The function f∘η_{x,ρ} is continuous and, by step 3, vanishes outside the compact ball B̄_{ρ(1+r)}(x); as μ is finite on compact sets it is μ-integrable. Therefore μ(T) = ∫ 1_T dμ ≤ J(ρ) < ε ρⁿ, i.e. μ(C_x ∩ B_ρ(x)) ≤ ENNReal.ofReal(ε ρⁿ) for all ρ ∈ (0, ρ₀). ∎

Formalization appendix (verified, supplementary to the proof above). The following Lean proof of exactly this frozen statement compiled without errors or sorry against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b366308), placed after `import GMT.Ch03.Submission` inside `namespace GMT.Ch03` with the contract's opens (`open Filter MeasureTheory Module Set`, `open scoped CompactlySupported ENNReal NNReal Topology`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt HasWeightedApproximateTangentSpaceAt PurelyUnrectifiable blowUpMap)`); `#print axioms` reports only [propext, Classical.choice, Quot.sound]. It follows the numbered steps above.

```lean
theorem Submission.tangentMeasure_eventually_cone_small : (∀ (N n : ℕ) (μ : Measure (Rn N)) (x : Rn N) (P : Submodule ℝ (Rn N)) (θ : ℝ), (∀ K : Set (Rn N), IsCompact K → μ K < ∞) → 0 < n → HasApproxTangentPlaneWithMultiplicity n μ x P θ → ∀ ε : ℝ, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ ({z | ‖P.starProjection (z - x)‖ ≤ ‖z - x‖ / 2} ∩ Metric.ball x ρ) ≤ ENNReal.ofReal (ε * ρ ^ n)) := by
  intro N n μ x P θ hfin hn hP ε hε
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hfin⟩
  obtain ⟨hdim, hlim⟩ := hP
  haveI hreg := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
    (E := Rn N) hdim
  set ν : Measure (Rn N) := (μHE[n] : Measure (Rn N)).restrict (P : Set (Rn N)) with hν
  have hν0 : ν {0} = 0 := by
    rw [hν, Measure.restrict_apply (measurableSet_singleton 0)]
    apply measure_mono_null Set.inter_subset_left
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
    haveI := Measure.nullSingletonClass_hausdorff (X := Rn N) (d := (n : ℝ))
      (by exact_mod_cast hn)
    simp [measure_singleton]
  have hinter : (⋂ k : ℕ, Metric.closedBall (0 : Rn N) (1 / ((k : ℝ) + 1))) = {0} := by
    ext y
    simp only [Set.mem_iInter, Metric.mem_closedBall, Set.mem_singleton_iff]
    constructor
    · intro h
      by_contra hne
      have hpos : 0 < dist y 0 := dist_pos.mpr hne
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
      exact absurd (h k) (not_le.mpr hk)
    · rintro rfl k
      simp only [dist_self]
      positivity
  have htend : Tendsto (fun k : ℕ => ν (Metric.closedBall 0 (1 / ((k : ℝ) + 1)))) atTop
      (𝓝 (ν {0})) := by
    rw [← hinter]
    apply tendsto_measure_iInter_atTop
    · exact fun k => measurableSet_closedBall.nullMeasurableSet
    · intro k l hkl
      apply Metric.closedBall_subset_closedBall
      gcongr
    · exact ⟨0, (isCompact_closedBall _ _).measure_lt_top.ne⟩
  rw [hν0] at htend
  have htend' : Tendsto (fun k : ℕ => |θ| * (ν (Metric.closedBall 0 (1 / ((k : ℝ) + 1)))).toReal)
      atTop (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend).const_mul |θ|
    simpa using this
  obtain ⟨k, hk⟩ := (htend'.eventually (gt_mem_nhds (half_pos hε))).exists
  set r : ℝ := 1 / (3 * ((k : ℝ) + 1)) with hr
  have hr0 : 0 < r := by positivity
  have hr3 : 3 * r = 1 / ((k : ℝ) + 1) := by rw [hr]; field_simp
  set q := P.starProjection with hq
  set S : Set (Rn N) := {w | ‖q w‖ ≤ ‖w‖ / 2} ∩ Metric.closedBall 0 1 with hS
  have hS0 : (0 : Rn N) ∈ S := ⟨by simp, by simp⟩
  have hSne : S.Nonempty := ⟨0, hS0⟩
  let f0 : Rn N → ℝ := fun w => max 0 (1 - Metric.infDist w S / r)
  have f0_cont : Continuous f0 :=
    continuous_const.max (continuous_const.sub ((Metric.continuous_infDist_pt S).div_const r))
  have f0_nonneg : ∀ w, 0 ≤ f0 w := fun w => le_max_left _ _
  have f0_zero : ∀ w, r ≤ Metric.infDist w S → f0 w = 0 := by
    intro w hw
    apply max_eq_left
    have : 1 ≤ Metric.infDist w S / r := by rw [le_div_iff₀ hr0]; linarith
    linarith
  have f0_out : ∀ w, 1 + r < ‖w‖ → f0 w = 0 := by
    intro w hw
    apply f0_zero
    by_contra hlt
    push_neg at hlt
    obtain ⟨s, hs, hws⟩ := (Metric.infDist_lt_iff hSne).mp hlt
    have hs1 : ‖s‖ ≤ 1 := by simpa using hs.2
    rw [dist_eq_norm] at hws
    have : ‖w‖ ≤ ‖w - s‖ + ‖s‖ := by
      calc ‖w‖ = ‖(w - s) + s‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith
  have f0_supp : HasCompactSupport f0 := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Rn N) (1 + r))
    intro w hw
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hw
    exact f0_out w hw
  let f : C_c(Rn N, ℝ) := ⟨⟨f0, f0_cont⟩, f0_supp⟩
  have hf : ∀ w, f w = f0 w := fun w => rfl
  have hloc : ∀ w ∈ (P : Set (Rn N)), f0 w ≠ 0 → ‖w‖ < 3 * r := by
    intro w hwP hw
    have hlt : Metric.infDist w S < r := by
      by_contra h
      push_neg at h
      exact hw (f0_zero w h)
    obtain ⟨s, hs, hws⟩ := (Metric.infDist_lt_iff hSne).mp hlt
    rw [dist_eq_norm] at hws
    have hqw : q w = w := P.starProjection_eq_self_iff.mpr hwP
    have h1 : ‖w‖ ≤ ‖q s‖ + ‖w - s‖ := by
      calc ‖w‖ = ‖q w‖ := by rw [hqw]
        _ = ‖q s + q (w - s)‖ := by rw [← map_add]; congr 2; abel
        _ ≤ ‖q s‖ + ‖q (w - s)‖ := norm_add_le _ _
        _ ≤ ‖q s‖ + ‖w - s‖ := by gcongr; exact P.norm_starProjection_apply_le _
    have h2 : ‖q s‖ ≤ ‖s‖ / 2 := hs.1
    have h3 : ‖s‖ ≤ ‖w‖ + ‖w - s‖ := by
      calc ‖s‖ = ‖w - (w - s)‖ := by congr 1; abel
        _ ≤ ‖w‖ + ‖w - s‖ := norm_sub_le _ _
    linarith
  have hplane : ∫ y in (P : Set (Rn N)), f y ∂μHE[n] ≤
      (ν (Metric.closedBall 0 (3 * r))).toReal := by
    change ∫ y, f y ∂ν ≤ _
    rw [← measureReal_def, ← integral_indicator_one measurableSet_closedBall]
    apply integral_mono_of_nonneg
    · exact Eventually.of_forall fun y => f0_nonneg _
    · exact (integrable_indicator_iff measurableSet_closedBall).mpr
        (integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne)
    · rw [hν]
      filter_upwards [ae_restrict_mem P.closed_of_finiteDimensional.measurableSet] with y hyP
      by_cases hy0 : f0 y = 0
      · rw [hf, hy0]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
      · have hyb : y ∈ Metric.closedBall (0 : Rn N) (3 * r) := by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact (hloc y hyP hy0).le
        rw [Set.indicator_of_mem hyb, hf]
        exact max_le zero_le_one (by
          have := Metric.infDist_nonneg (x := y) (s := S)
          have : 0 ≤ Metric.infDist y S / r := div_nonneg this hr0.le
          simp only [Pi.one_apply]; linarith)
  have hlimlt : θ * ∫ y in (P : Set (Rn N)), f y ∂μHE[n] < ε := by
    have hint_nonneg : 0 ≤ ∫ y in (P : Set (Rn N)), f y ∂μHE[n] :=
      integral_nonneg fun y => f0_nonneg y
    calc θ * ∫ y in (P : Set (Rn N)), f y ∂μHE[n]
        ≤ |θ| * ∫ y in (P : Set (Rn N)), f y ∂μHE[n] :=
          mul_le_mul_of_nonneg_right (le_abs_self θ) hint_nonneg
      _ ≤ |θ| * (ν (Metric.closedBall 0 (3 * r))).toReal :=
          mul_le_mul_of_nonneg_left hplane (abs_nonneg θ)
      _ < ε / 2 := by rw [hr3]; exact hk
      _ < ε := half_lt_self hε
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (ρ ^ n)⁻¹ * ∫ y, f (blowUpMap x ρ y) ∂μ < ε :=
    (hlim f).eventually (gt_mem_nhds hlimlt)
  filter_upwards [hev, self_mem_nhdsWithin] with ρ hρ hρpos
  have hρpos' : (0 : ℝ) < ρ := hρpos
  have hρn : 0 < ρ ^ n := pow_pos hρpos' n
  have hJ : ∫ y, f (blowUpMap x ρ y) ∂μ < ε * ρ ^ n := by
    have := mul_lt_mul_of_pos_left hρ hρn
    rwa [← mul_assoc, mul_inv_cancel₀ hρn.ne', one_mul, mul_comm] at this
  set T := {z | ‖q (z - x)‖ ≤ ‖z - x‖ / 2} ∩ Metric.ball x ρ with hT
  have hTm : MeasurableSet T := by
    refine (isClosed_le ?_ ?_).measurableSet.inter measurableSet_ball
    · exact (q.continuous.comp (continuous_id.sub continuous_const)).norm
    · exact (continuous_id.sub continuous_const).norm.div_const 2
  have hTfin : μ T < ∞ :=
    (measure_mono (Set.inter_subset_right.trans Metric.ball_subset_closedBall)).trans_lt
      (isCompact_closedBall x ρ).measure_lt_top
  have hblow : ∀ y, blowUpMap x ρ y = ρ⁻¹ • (y - x) := fun y => rfl
  have hpt : ∀ y, T.indicator 1 y ≤ f (blowUpMap x ρ y) := by
    intro y
    by_cases hy : y ∈ T
    · rw [Set.indicator_of_mem hy]
      have hw : blowUpMap x ρ y ∈ S := by
        obtain ⟨hy1, hy2⟩ := hy
        rw [Metric.mem_ball, dist_eq_norm] at hy2
        simp only [Set.mem_setOf_eq] at hy1
        refine ⟨?_, ?_⟩
        · show ‖q (blowUpMap x ρ y)‖ ≤ ‖blowUpMap x ρ y‖ / 2
          rw [hblow, map_smul, norm_smul, norm_smul, Real.norm_eq_abs, abs_inv,
            abs_of_pos hρpos']
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hy1 (inv_nonneg.mpr hρpos'.le)
        · rw [Metric.mem_closedBall, dist_zero_right, hblow, norm_smul, Real.norm_eq_abs,
            abs_inv, abs_of_pos hρpos', inv_mul_le_iff₀ hρpos']
          linarith
      rw [hf]
      show (1 : ℝ) ≤ max 0 (1 - Metric.infDist (blowUpMap x ρ y) S / r)
      rw [Metric.infDist_zero_of_mem hw]
      simp
    · rw [Set.indicator_of_notMem hy]
      exact f0_nonneg _
  have hηc : Continuous (blowUpMap x ρ) := by
    change Continuous fun y : Rn N => ρ⁻¹ • (y - x)
    fun_prop
  have hcont : Continuous (fun y => f (blowUpMap x ρ y)) := f.continuous.comp hηc
  have hcs : HasCompactSupport (fun y => f (blowUpMap x ρ y)) := by
    apply HasCompactSupport.intro (isCompact_closedBall x (ρ * (1 + r)))
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hy
    rw [hf]
    apply f0_out
    rw [hblow, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρpos', lt_inv_mul_iff₀ hρpos']
    linarith
  have hfi : Integrable (fun y => f (blowUpMap x ρ y)) μ :=
    hcont.integrable_of_hasCompactSupport hcs
  have hmono : μ.real T ≤ ∫ y, f (blowUpMap x ρ y) ∂μ := by
    rw [← integral_indicator_one hTm]
    exact integral_mono_of_nonneg
      (Eventually.of_forall fun y => Set.indicator_nonneg (fun _ _ => zero_le_one) _) hfi
      (Eventually.of_forall hpt)
  calc μ T = ENNReal.ofReal (μ.real T) := (ENNReal.ofReal_toReal hTfin.ne).symm
    _ ≤ ENNReal.ofReal (ε * ρ ^ n) := ENNReal.ofReal_le_ofReal (by linarith)
```

## Key steps

1. Since n ≥ 1, Hⁿ⌞P has no atom at 0, so Hⁿ(P ∩ B̄_s(0)) → 0 as s ↓ 0; fix r > 0 with |θ| Hⁿ(P ∩ B̄_{3r}(0)) < ε/2.
2. Test function f = max(0, 1 − dist(·, S)/r) ∈ C_c with S = {|q_P w| ≤ |w|/2} ∩ B̄_1(0) and f = 1 on S.
3. On P, f(w) ≠ 0 forces |w| < 3r, hence θ∫_P f dHⁿ ≤ |θ| Hⁿ(P ∩ B̄_{3r}(0)) < ε.
4. The tangent limit gives ∫ f∘η_{x,ρ} dμ < ερⁿ for all small ρ > 0.
5. 1_{C_x ∩ B_ρ(x)} ≤ f∘η_{x,ρ} pointwise, so μ(C_x ∩ B_ρ(x)) ≤ ερⁿ.

## Reference use

### local-project

Queries:
- `cat local-references/d498d77b74ea2063/manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); diff project/GMT/Ch03/Contract.lean against the workspace contract (identical)`
- `grep -n theorem/def simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, countablyRectifiable_iUnion, countablyRectifiable_range, blowUpMap, regular_euclideanHausdorffMeasure_restrict_submodule, support_euclideanHausdorffMeasure_restrict_submodule)`
- `grep -n theorem simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean (locallyFinite_planeMeasure, planeMeasure_unit_closedBall, tangentDensityCutoff, one_le_density_of_approximateTangent)`
- `grep -rn "μHE\[" mathlib/Mathlib; read mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_def, isAddHaarMeasure_euclideanHausdorffMeasure, Isometry.map_euclideanHausdorffMeasure, euclideanHausdorffMeasure_smul₀, InnerProductSpace.euclideanHausdorffMeasure_eq_volume)`
- `grep -rn "LipschitzOnWith.extend_real|LipschitzOnWith.extend_pi|extend_finite_dimension" mathlib/Mathlib`
- `grep -rn "IsSigmaCompact.measurableSet|isSigmaCompact_range" mathlib/Mathlib (no IsSigmaCompact.measurableSet; isSigmaCompact_range in Topology/Compactness/SigmaCompact.lean)`
- `grep -rn "countable_meas_pos" mathlib/Mathlib (Measure.countable_meas_pos_of_disjoint_iUnion in Typeclasses/SFinite.lean); grep sigmaFinite_of_locallyFinite`
- `grep -n "starProjection_norm_le|norm_starProjection_apply_le|starProjection_eq_self_iff|orthogonalProjectionOnto|starProjection_apply" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `grep IsSeparable.exists_countable_dense_subset, IsSeparable.of_separableSpace, exists_countable_dense, Dense.exists_dist_lt, exists_linearIndependent_of_le_finrank, finrank_span_eq_card, stdOrthonormalBasis/reindex, nhdsGT_basis, Antitone.measure_iInter, tendsto_measure_iInter_atTop, nullSingletonClass_hausdorff, mem_support_iff_forall, infDist_lt_iff, continuous_infDist_pt, integral_pos_iff_support_of_nonneg, integral_mono_of_nonneg, integral_indicator_one, integrableOn_const, Continuous.integrable_of_hasCompactSupport, ofReal_le_ofReal_iff'`
- `sed -n 60,280p book/chapter-03.txt (Remark 1.5(3) lines 91-105; proof of 1.6 '⇐' lines 145-274)`
- `python: contract_scope() and validate_lean_statement() from verifier/gmt-compare.py and verifier/lean_contract.py applied to every proposed lean_statement`
- `grep -rl for each proposed lean_name over .humanize, GMT and simongmt/Poincare (no match); dag.json lean_name listing`
- `lake env lean /tmp/rtm_scratch/Challenge.lean, /tmp/rtm_scratch/Assembly.lean, /tmp/rtm_scratch/ChildrenCDEF.lean, /tmp/rtm_scratch/ChildrenAB.lean, /tmp/rtm_scratch/Full.lean (with #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Dimension/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Order/LeftRightNhds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-rectifiable-of-tangent-measure-a1/parent-child-handoff.json`
- `/tmp/rtm_scratch/Challenge.lean`
- `/tmp/rtm_scratch/Assembly.lean`
- `/tmp/rtm_scratch/Full.lean`

Snapshot: project d09bc8a (Contract.lean identical to the workspace copy), Mathlib 25730c7c, pinned simongmt. Found and used: SimonGMT Chapter03 CountablyRectifiable, countablyRectifiable_iUnion, countablyRectifiable_range, blowUpMap, regular_euclideanHausdorffMeasure_restrict_submodule and support_euclideanHausdorffMeasure_restrict_submodule (plane measure Hⁿ⌞P is regular with support P when finrank P = n); Mathlib LipschitzOnWith.extend_finite_dimension (Lipschitz extension into finite-dimensional targets, replacing Simon Ch. 2 Thm 1.2), Measure.countable_meas_pos_of_disjoint_iUnion with sigmaFinite_of_locallyFinite (countable atoms), isSigmaCompact_range (Borel measurability of Lipschitz images), Measure.nullSingletonClass_hausdorff (no atoms for n ≥ 1), Submodule.norm_starProjection_apply_le / starProjection_eq_self_iff, IsSeparable.exists_countable_dense_subset, exists_linearIndependent_of_le_finrank, Antitone.measure_iInter, tendsto_measure_iInter_atTop, infDist_lt_iff, integral_pos_iff_support_of_nonneg, integral_mono_of_nonneg. No match: Mathlib has no IsSigmaCompact.measurableSet (σ-compact sets are handled by unfolding into a countable union of compacts), no countable rectifiability, and no Kirszbraun theorem (not needed: componentwise/finite-dimensional extension suffices); SimonGMT has no approximate-tangent-measure (HasApproxTangentPlaneWithMultiplicity) results. The six child propositions pass the verifier's statement validator and elaborate in the comparator's replayed contract scope; with the children as sorry stubs the parent glue compiles; and complete proofs of all six children plus the parent compile sorry-free using only propext, Classical.choice and Quot.sound. No proposed name is used elsewhere in the active DAG or the libraries.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
