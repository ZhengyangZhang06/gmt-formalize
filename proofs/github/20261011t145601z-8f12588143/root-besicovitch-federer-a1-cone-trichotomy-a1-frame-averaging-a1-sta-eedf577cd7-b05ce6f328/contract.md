<!-- theorem-id: gmt-ch03/root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.stabilizer_orbit_null-a1 -->

## Theorem `Submission.bf_stabilizerOrbit_null`

Let N, n ∈ ℕ, E := ℝᴺ = EuclideanSpace ℝ (Fin N), and let 𝓛 := E →L[ℝ] E carry the Borel σ-algebra of its norm topology; g* is the adjoint. Let Hⁿ := μHE[n], V ⊆ E a linear subspace, S(V) := {x ∈ V : |x| = 1}, and K := {g ∈ 𝓛 : g*g = 1 and gx = x for all x ∈ V^⊥}. Let θ be a Borel probability measure on 𝓛 such that θ-a.e. g lies in K and, for every k ∈ K, the images of θ under g ↦ kg and g ↦ gk equal θ. Assume 0 < Hⁿ(S(V)) < ∞. Then for every ζ ∈ V with |ζ| = 1 and every Borel set Y ⊆ E with Hⁿ(Y ∩ S(V)) = 0, θ({g ∈ 𝓛 : gζ ∈ Y}) = 0.

Node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.stabilizer_orbit_null-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/550

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.bf_stabilizerOrbit_null`

```lean
∀ (N n : ℕ) (V : Submodule ℝ (Rn N)) (θ : Measure (Rn N →L[ℝ] Rn N)), IsProbabilityMeasure θ → (∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1 ∧ ∀ x ∈ Vᗮ, g x = x) → (∀ k : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint k * k = 1 → (∀ x ∈ Vᗮ, k x = x) → Measure.map (fun g ↦ k * g) θ = θ ∧ Measure.map (fun g ↦ g * k) θ = θ) → 0 < μHE[n] {x : Rn N | x ∈ V ∧ ‖x‖ = 1} → μHE[n] {x : Rn N | x ∈ V ∧ ‖x‖ = 1} < ∞ → ∀ ζ ∈ V, ‖ζ‖ = 1 → ∀ Y : Set (Rn N), MeasurableSet Y → μHE[n] (Y ∩ {x : Rn N | x ∈ V ∧ ‖x‖ = 1}) = 0 → θ {g | g ζ ∈ Y} = 0
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

- Parent DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.stabilizer_orbit_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 4 of the parent-supplied proof of bf_frameAveraging_null (its supplied Step 4.4; Mattila, Ch. 3, uniqueness of invariant measures on the sphere), with three substitutions:
- the plane H⁰ = span{e_1, …, e_{n+1}} becomes the subspace V;
- the vector e_{n+1} becomes ζ;
- the stabilizer G′ becomes K = {g : g*g = 1, g = id on V^⊥}. For V = H⁰ this is exactly G′, because V^⊥ = span{e_{n+2}, …, e_N}.
The bounds 0 < Hⁿ(S⁰) < ∞, which the parent derives from bf_sphereCap_measure_bounds, are hypotheses here. Write S := S(V).

Notation (as in the parent proof): E := ℝᴺ = EuclideanSpace ℝ (Fin N); x·y is the inner product and |·| the norm; 𝓛 := E →L[ℝ] E with the Borel σ-algebra of its operator-norm topology; gk is composition and 1 the identity; g* := ContinuousLinearMap.adjoint g; P_W := W.starProjection; gW := W.map g; Hⁿ := μHE[n].

0. Facts about K (the parent's F2 for V). Let k ∈ K.
   (a) kx·ky = x·k*ky = x·y, so |kx| = |x| and k is an isometry of E. In particular k is injective.
       E is finite-dimensional, so k is also surjective (LinearMap.surjective_of_injective).
       For y = kx, k(k*y) = k(k*kx) = kx = y. Hence kk* = 1 and k* is the inverse of k.
       Also k* ∈ K: (k*)*k* = kk* = 1 (ContinuousLinearMap.adjoint_adjoint), and for y ∈ V^⊥, k*y = k*(ky) = y.
   (b) kV ⊆ V. For x ∈ V and y ∈ V^⊥, kx·y = kx·ky = x·y = 0, so kx ∈ (V^⊥)^⊥ = V (Submodule.orthogonal_orthogonal).
   (c) By (a) and (b), kS ⊆ S, and likewise k*S ⊆ S. Since k*k = kk* = 1, for every x ∈ E: kx ∈ S ⟺ x ∈ S, i.e. k⁻¹(S) = S.
1. The two measures.
   - ν₀ is the image of θ under the continuous map g ↦ gζ from 𝓛 to E. It is a Borel probability measure on E.
     By (c), gζ ∈ S for every g ∈ K, so ν₀(E ∖ S) = θ({g : gζ ∉ S}) ≤ θ(𝓛 ∖ K) = 0.
   - Let σ := Hⁿ(S) ∈ (0, ∞) and σ̄ := σ⁻¹·(Hⁿ restricted to S).
     S = V ∩ sphere(0, 1) is closed, hence Borel, so σ̄ is a Borel probability measure on E with σ̄(E ∖ S) = 0.
2. K-invariance. Let k ∈ K.
   (a) k_*ν₀ = ν₀. Indeed k_*ν₀ is the image of θ under g ↦ k(gζ) = (kg)ζ. That is the image under g ↦ gζ of the image of θ under g ↦ kg, which is θ by left invariance.
   (b) k_*σ̄ = σ̄. For Borel B ⊆ E, step 0(c) gives k⁻¹(B) ∩ S = k⁻¹(B) ∩ k⁻¹(S) = k⁻¹(B ∩ S) = k*(B ∩ S).
       The isometry k* preserves Hⁿ (Isometry.euclideanHausdorffMeasure_image), so σ̄(k⁻¹B) = σ⁻¹Hⁿ(k*(B ∩ S)) = σ⁻¹Hⁿ(B ∩ S) = σ̄(B).
3. Transitivity. For x, y ∈ S there is k ∈ K with ky = x.
   - If x = y, take k := 1.
   - Otherwise put d := y − x ≠ 0 and let k be the reflection in d^⊥, kz = z − 2((z·d)/|d|²)d. This is Mathlib's (ℝ ∙ d)ᗮ.reflection, a linear isometry equivalence.
   - As an element of 𝓛, k preserves inner products, so k*k = 1.
   - Since |y| = |x| = 1, ky = x (Submodule.reflection_sub: reflection (ℝ ∙ (v − w))ᗮ v = w when ‖v‖ = ‖w‖; take v = y, w = x).
   - If z ∈ V^⊥, then z·d = 0 because d ∈ V. So z ∈ (ℝd)^⊥ and kz = z. Hence k ∈ K.
4. Uniqueness. Let ν be a Borel probability measure on E with ν(E ∖ S) = 0 and k_*ν = ν for all k ∈ K.
   Let φ : E → ℝ be bounded and continuous, and Ψ(x) := ∫_𝓛 φ(gx) dθ(g). We show ∫ φ dν = Ψ(ζ).
   (a) For k ∈ K, ∫_E φ(kx) dν(x) = ∫ φ d(k_*ν) = ∫ φ dν (integral_map).
   (b) F(g, x) := φ(gx) is bounded and continuous on 𝓛 × E. Both factors are second countable, so F is measurable for the product σ-algebra and integrable for the finite measure θ ⊗ ν.
       By Fubini (integral_integral_swap), ∫_𝓛 ∫_E F dν dθ = ∫_E ∫_𝓛 F dθ dν = ∫_E Ψ dν.
   (c) By (a), the inner integral ∫_E φ(gx) dν(x) equals ∫ φ dν for θ-a.e. g (all g ∈ K).
       So the left side of (b) is (∫ φ dν)·θ(𝓛) = ∫ φ dν.
   (d) Ψ is constant on S. For k ∈ K and y ∈ E, by integral_map and right invariance:
       Ψ(ky) = ∫ φ((gk)y) dθ(g) = ∫ φ(g′y) d((g ↦ gk)_*θ)(g′) = ∫ φ(g′y) dθ(g′) = Ψ(y).
       For x ∈ S, step 3 gives k ∈ K with kζ = x, so Ψ(x) = Ψ(ζ).
   (e) Since ν(E ∖ S) = 0, Ψ = Ψ(ζ) ν-a.e., and ν(E) = 1. So ∫_E Ψ dν = Ψ(ζ) (integral_congr_ae).
       Combining (b), (c) and (e) gives ∫ φ dν = Ψ(ζ).
5. ν₀ = σ̄.
   - Both measures satisfy the hypotheses of step 4, by steps 1 and 2.
   - Hence ∫ φ dν₀ = Ψ(ζ) = ∫ φ dσ̄ for every bounded continuous φ : E → ℝ.
   - Finite Borel measures on the metric space E with equal integrals of all bounded continuous functions are equal. This is MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure in Mathlib.MeasureTheory.Measure.HasOuterApproxClosed, which must be imported; E has HasOuterApproxClosed.
   - So ν₀ = σ̄.
6. Conclusion. Let Y ⊆ E be Borel with Hⁿ(Y ∩ S) = 0. By Measure.map_apply and Measure.restrict_apply,
   θ({g : gζ ∈ Y}) = ν₀(Y) = σ̄(Y) = σ⁻¹Hⁿ(Y ∩ S) = 0. ∎

## Key steps

1. Every k ∈ K is an isometry with k* = k⁻¹ ∈ K and maps V, and hence S(V), onto itself.
2. ν₀ := law of gζ under θ and σ̄ := Hⁿ⌞S(V)/Hⁿ(S(V)) are Borel probability measures concentrated on S(V). Both are K-invariant: ν₀ by left invariance of θ, σ̄ by isometry invariance of Hⁿ.
3. K acts transitively on S(V): the reflection in (y − x)^⊥ lies in K and maps y to x.
4. Uniqueness: if ν is a K-invariant probability on S(V), then ∫φ dν = Ψ(ζ) := ∫φ(gζ) dθ(g) for bounded continuous φ. This uses Fubini on θ ⊗ ν and the fact that right invariance makes Ψ constant on S(V).
5. Hence ν₀ = σ̄ (ext_of_forall_integral_eq_of_IsFiniteMeasure), so θ{g : gζ ∈ Y} = σ̄(Y) = 0 whenever Hⁿ(Y ∩ S(V)) = 0.

## Reference use

### local-project

Queries:
- `cat manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n "def frameProjection|def ForAlmostAllProjections|abbrev Rn" project/GMT/Ch03/Contract.lean`
- `rg -n "instance instMeasurableSpace|instBorelSpace" mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `rg -n "isMulInvariant_eq_smul_of_compactSpace|isHaarMeasure_eq_of_isProbabilityMeasure" mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `rg -n "theorem haarMeasure_self|def haarMeasure " mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `grep -rn CompactSpace mathlib/Mathlib/MeasureTheory/Measure/Haar/*.lean mathlib/Mathlib/MeasureTheory/Group/*.lean | grep -i 'inv|right|unimod' (no right-invariance instance for compact groups)`
- `rg -n "IsTopologicalGroup \(unitary|isClosed_unitary|instance.*unitary" mathlib/Mathlib/Topology/Algebra/Star/Unitary.lean`
- `rg -n "ext_of_forall_integral_eq_of_IsFiniteMeasure" mathlib/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean`
- `grep -rn "LinearIsometry.extend" mathlib/Mathlib (PiL2.lean:1174 def, 1222 extend_apply)`
- `grep -n "theorem reflection_sub" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Reflection.lean (namespace Submodule)`
- `grep -n "eq_starProjection_of_mem_of_inner_eq_zero|starProjection_apply_mem|sub_starProjection_mem_orthogonal" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n "theorem measurePreserving" mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean; rg -n "theorem measurePreserving_pi " mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `#check Measure.ae_ae_comm, measurable_measure_prodMk_left/right, Measure.prod_apply(_symm), isOpen_setOfPred_linearIndependent, ContinuousOn.measurable_piecewise, Isometry.euclideanHausdorffMeasure_image, Submodule.finrank_add_finrank_orthogonal, Submodule.finrank_sup_add_finrank_inf_eq, Submodule.eq_of_le_of_finrank_eq, integral_integral_swap, integral_map (all resolve after import GMT.Ch03.Submission; ext_of_forall_integral_eq_of_IsFiniteMeasure and isClosed_unitary need the extra imports)`
- `inferInstance probes: ContinuousStar (Rn N →L[ℝ] Rn N) fails (must be supplied locally); SecondCountableTopology, MeasurableMul₂, ProperSpace of 𝓛 and HasOuterApproxClosed (Rn N) succeed`
- `grep bf_orthStabilizer_haar_exists|bf_stabilizerOrbit_null|bf_haar_null_of_cosetFibres_null|bf_starProjection_map_orthogonal|bf_haar_planeDirection_null|bf_haar_excPointwise_null|bf_orthogonal_exists_map_eq|bf_haar_null_to_frames in dag.json, the snapshot project and all worktree Submission.lean files (no match); child keys absent from dag.json`
- `grep -n candidate_inputs verifier/gmt-compare.py (only frozen inputs are byte-checked; Submission.lean may add imports)`
- `grep -n "3.6\|Fed69\|Ros84" book/chapter-03.txt (Thm 3.6 at lines 530-536 defers its proof to [Fed69]/[Ros84])`
- `lake env lean GMT/Scratch/FrameAveragingSplit{Decision,Assembly,Glue,Frames,Leaves,EndToEnd,Closed}.lean (all compile; Closed: e2e_parent uses only propext, Classical.choice, Quot.sound and stand-ins with the exact frozen types of the two parent siblings)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/Star/Unitary.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Reflection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-frame-averaging-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitDecision.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitAssembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitGlue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitFrames.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitLeaves.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitHaarStabilizer.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitOrbitNull.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitEndToEnd.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitClosed.lean`

The snapshot fixes Rn, frameProjection and ForAlmostAllProjections (Contract.lean), and the child types use them verbatim. The pinned Mathlib supplies every library ingredient the child proofs cite:
- the Borel structure on E →L[ℝ] E (ContinuousLinearMap.instMeasurableSpace / instBorelSpace);
- the Haar measure, haarMeasure_self, and uniqueness on compact groups (isMulInvariant_eq_smul_of_compactSpace, isHaarMeasure_eq_of_isProbabilityMeasure);
- the unitary topological group (IsTopologicalGroup (unitary R)), which requires a ContinuousStar instance on 𝓛 supplied locally from the continuity of the adjoint;
- ext_of_forall_integral_eq_of_IsFiniteMeasure (requires importing HasOuterApproxClosed);
- Submodule.reflection_sub, LinearIsometry.extend / extend_apply, and the orthogonal-projection characterization eq_starProjection_of_mem_of_inner_eq_zero;
- LinearIsometryEquiv.measurePreserving, measurePreserving_pi, Measure.prod_apply / prod_apply_symm, Measure.ae_ae_comm, measurable_measure_prodMk_left/right, ContinuousOn.measurable_piecewise, isOpen_setOfPred_linearIndependent and Isometry.euclideanHausdorffMeasure_image.
The searches found no right-invariance instance for compact-group Haar measure, no CompactSpace instance for orthogonal groups and no Haar measure on O(N), so those are built in haar_stabilizer. No existing declaration states any of the eight children, and all names and keys are fresh in dag.json, the snapshot and the worktrees. The verifier byte-checks only frozen inputs, so the two extra Mathlib imports needed by the leaves are permitted in Submission.lean. Lean evidence: all child types elaborate in the contract scope. The exact frozen parent type follows from the children plus the two parent siblings. Every child, including the two deep leaves, was proved in scratch, and the closed chain uses only propext, Classical.choice and Quot.sound, besides stand-ins carrying exactly the frozen types of bf_sphereCap_measure_bounds and bf_frameProjection_continuousOn.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
