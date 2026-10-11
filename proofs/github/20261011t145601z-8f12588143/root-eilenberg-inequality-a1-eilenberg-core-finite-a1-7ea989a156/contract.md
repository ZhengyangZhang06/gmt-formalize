<!-- theorem-id: gmt-ch03/root.eilenberg_inequality-a1.eilenberg_core_finite-a1 -->

## Theorem `Submission.eilenberg_hausdorff_upper_integral_of_ne_top`

Let N, m, k ∈ ℕ, let A ⊆ ℝ^N be arbitrary (not necessarily measurable), L ∈ [0, ∞), and f : ℝ^N → ℝᵐ L-Lipschitz (ℝ^d = EuclideanSpace ℝ (Fin d)). Let μH[s] be Mathlib's unnormalized s-dimensional Hausdorff (outer) measure on ℝ^N (gauge diam^s; the exponents are the real numbers k and m + k), λₘ = volume on ℝᵐ, and ωₘ := λₘ(B₁(0)) with B₁(0) the open unit ball of ℝᵐ. If μH[m+k](A) < ∞, there is a Borel measurable g : ℝᵐ → [0, ∞] with μH[k](A ∩ f⁻¹{y}) ≤ g(y) for every y ∈ ℝᵐ and ∫ g dλₘ ≤ ωₘ·L^m·μH[m+k](A).

Node: `root.eilenberg_inequality-a1.eilenberg_core_finite-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/22

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/47, https://github.com/ZhengyangZhang06/gmt-formalize/issues/48

Decomposition children: None

## Lean problem

Declaration: `Submission.eilenberg_hausdorff_upper_integral_of_ne_top`

```lean
∀ (N m k : ℕ) (A : Set (Rn N)) (f : Rn N → Rn m) (L : ℝ≥0), LipschitzWith L f → μH[((m + k : ℕ) : ℝ)] A ≠ ∞ → ∃ g : Rn m → ℝ≥0∞, Measurable g ∧ (∀ y, μH[(k : ℝ)] (A ∩ f ⁻¹' {y}) ≤ g y) ∧ ∫⁻ y, g y ≤ volume (Metric.ball (0 : Rn m) 1) * (L : ℝ≥0∞) ^ m * μH[((m + k : ℕ) : ℝ)] A
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

- Parent DAG node: `root.eilenberg_inequality-a1`
- Child DAG node: `root.eilenberg_inequality-a1.eilenberg_core_finite-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and role. This is Simon, Ch. 2, proof of Theorem 1.9 (chapter-02.txt lines 366–411, printed pp. 45–46), i.e. Steps 4–7 of the parent proof. It is specialised to Mathlib's unnormalized Hausdorff measures (all normalizing constants c_s = 1). Simon's use of the isodiametric inequality (lines 401–406) is replaced by the sibling lemma volume_diameter_bound, so the constant is ωₘ := λₘ(B₁(0)) instead of ωₘω_k/ω_{m+k}. The hypothesis μH[m+k](A) < ∞ is Simon's hypothesis H^{m+k}(A) < ∞. As in the parent (its Remark (i)), measurability of A is not used. Instead of Simon's upper integral and monotone limit (Remark 1.10, lines 407–411), the parent's Step 7 (liminf and Fatou) is used, which directly produces the required Borel majorant g.

Notation. diam = extended diameter in [0, ∞]. For a set T and real s, cost_s(T) := diam(T)^s if T ≠ ∅ and cost_s(∅) := 0; this is the cost used by Mathlib's Hausdorff measure (⨆ _ : T.Nonempty, …). For n ∈ ℕ and x ∈ [0, ∞], the real power x^{(n:ℝ)} equals the ordinary power xⁿ, so x^k·x^m = x^{m+k} for every x ∈ [0, ∞], including 0 and ∞. λₘ = volume on ℝᵐ. ω := ωₘ = λₘ(B₁(0)) < ∞, because B₁(0) is bounded in the finite-dimensional space ℝᵐ. For i ∈ ℕ put ρᵢ := 1/i ∈ (0, ∞] (ρ₀ = ∞); then ρᵢ > 0, ρᵢ ≠ 0 and ρᵢ → 0.

Proof.
1. Covers (Simon (1), lines 366–370; parent Step 4). For each i, apply the sibling lemma hausdorff_near_optimal_cover with X = ℝ^N, d = m + k, s = A and r = ε = ρᵢ, using μH[m+k](A) < ∞. Choosing such a cover for every i (countable choice) gives sets C_{ij} ⊆ ℝ^N (i, j ∈ ℕ) with
 (1a) A ⊆ ⋃ⱼ C_{ij};
 (1b) diam C_{ij} ≤ ρᵢ for all j;
 (1c) Σⱼ cost_{m+k}(C_{ij}) ≤ μH[m+k](A) + ρᵢ.
2. The functions gᵢ and g (Simon lines 371–377; parent Step 4). Let K_{ij} := closure of f(C_{ij}), a closed and hence Borel subset of ℝᵐ. For y ∈ ℝᵐ set
 gᵢ(y) := Σⱼ diam(C_{ij})^k · 1_{K_{ij}}(y) ∈ [0, ∞],  g(y) := liminf_{i→∞} gᵢ(y).
 Each summand y ↦ diam(C_{ij})^k·1_{K_{ij}}(y) is a constant times the indicator of a Borel set, hence Borel. A countable sum of Borel [0, ∞]-valued functions is Borel, so every gᵢ is Borel. The liminf of a sequence of Borel [0, ∞]-valued functions is Borel, so g is Borel. This is the required measurability.
3. Pointwise bound (Simon (2), lines 377–384; parent Steps 5 and 7). Fix y ∈ ℝᵐ and put S := A ∩ f⁻¹{y}. For each i let Jᵢ := {j ∈ ℕ : y ∈ f(C_{ij})}, a countable set; each C_{ij} with j ∈ Jᵢ is nonempty.
 (3a) Cover: S ⊆ ⋃_{j∈Jᵢ} C_{ij}. If x ∈ S then x ∈ A, so x ∈ C_{ij} for some j by (1a); then y = f(x) ∈ f(C_{ij}), i.e. j ∈ Jᵢ.
 (3b) Liminf bound: μH[k](S) ≤ liminf_i Σ_{j∈Jᵢ} diam(C_{ij})^k. By definition μH[k](S) = sup_{ρ>0} I_ρ(S), where I_ρ(S) is the infimum of Σ cost_k over countable covers of S by sets of diameter ≤ ρ. Fix ρ > 0 and choose i₀ with ρᵢ ≤ ρ for all i ≥ i₀ (possible since ρᵢ → 0). For i ≥ i₀, the family (C_{ij})_{j∈Jᵢ} covers S by (3a) and consists of sets of diameter ≤ ρ by (1b). Enumerate it as a sequence, padding with empty sets of cost 0 if Jᵢ is finite; if Jᵢ = ∅ then S = ∅ and the all-empty cover has cost 0. Since cost_k(T) ≤ diam(T)^k for every T, I_ρ(S) ≤ Σ_{j∈Jᵢ} diam(C_{ij})^k for all i ≥ i₀, hence I_ρ(S) ≤ liminf_i Σ_{j∈Jᵢ} diam(C_{ij})^k. Now take the supremum over ρ > 0. (Mathlib packages exactly this as MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum, applied with the countable index types ιᵢ := {j : ℕ // y ∈ f '' C i j}, the sets t i j := C i j, the radii r i := ρᵢ → 0 (ENNReal.tendsto_inv_nat_nhds_zero), the diameter bound (1b) and the cover (3a).)
 (3c) Comparison with gᵢ: for every i, Σ_{j∈Jᵢ} diam(C_{ij})^k ≤ gᵢ(y). Write the left side as Σⱼ 1_{Jᵢ}(j)·diam(C_{ij})^k and compare termwise. If j ∈ Jᵢ then y ∈ f(C_{ij}) ⊆ K_{ij}, so the j-th term of gᵢ(y) is also diam(C_{ij})^k. If j ∉ Jᵢ the left term is 0.
 (3d) By (3b), (3c) and monotonicity of liminf: μH[k](S) ≤ liminf_i Σ_{j∈Jᵢ} diam(C_{ij})^k ≤ liminf_i gᵢ(y) = g(y).
4. Integral of gᵢ (Simon lines 385–406; parent Step 6). Fix i. Integrals and countable sums of nonnegative measurable functions commute (monotone convergence), and ∫ c·1_K dλₘ = c·λₘ(K) for Borel K. Hence
 ∫ gᵢ dλₘ = Σⱼ diam(C_{ij})^k · λₘ(K_{ij}).
 Each term is at most ω·L^m·cost_{m+k}(C_{ij}):
 (4a) If C_{ij} = ∅: f(C_{ij}) = K_{ij} = ∅, the term is diam(∅)^k·0 = 0 (also for k = 0), and the bound reads 0 ≤ 0.
 (4b) If C_{ij} ≠ ∅: by the sibling lemma volume_diameter_bound applied to f(C_{ij}) ⊆ ℝᵐ, λₘ(K_{ij}) ≤ ω·diam(f(C_{ij}))^m. Since f is L-Lipschitz, diam f(C_{ij}) ≤ L·diam C_{ij} in [0, ∞] (Mathlib: LipschitzWith.ediam_image_le). Multiplication and the m-th power are monotone on [0, ∞], so
 diam(C_{ij})^k·λₘ(K_{ij}) ≤ diam(C_{ij})^k·ω·(L·diam C_{ij})^m = ω·L^m·diam(C_{ij})^{m+k} = ω·L^m·cost_{m+k}(C_{ij}).
 The middle equality is commutative-semiring arithmetic in [0, ∞]: (ab)^m = a^m b^m and x^k x^m = x^{m+k}.
 Summing over j, pulling out the constant and using (1c):
 ∫ gᵢ dλₘ ≤ ω·L^m·Σⱼ cost_{m+k}(C_{ij}) ≤ ω·L^m·(μH[m+k](A) + ρᵢ).
5. Fatou and the limit (Simon lines 407–411 and Remark 1.10; parent Step 7). By Fatou's lemma for the Borel functions gᵢ ≥ 0, then step 4 and monotonicity of liminf:
 ∫ g dλₘ = ∫ liminf_i gᵢ dλₘ ≤ liminf_i ∫ gᵢ dλₘ ≤ liminf_i ω·L^m·(μH[m+k](A) + ρᵢ).
 Since ρᵢ → 0, μH[m+k](A) + ρᵢ → μH[m+k](A) in [0, ∞]. The constant ω·L^m is finite (ω < ∞ and L < ∞), so multiplying by it is continuous on [0, ∞]. Hence ω·L^m·(μH[m+k](A) + ρᵢ) → ω·L^m·μH[m+k](A), and the liminf of a convergent sequence is its limit. Therefore ∫ g dλₘ ≤ ωₘ·L^m·μH[m+k](A).
6. Conclusion. g is Borel (step 2), satisfies μH[k](A ∩ f⁻¹{y}) ≤ g(y) for every y (step 3), and satisfies the integral bound (step 5). ∎

Edge cases. The uniform argument covers all of them, with no case split.
- m = 0: ℝ⁰ is a point, and volume_diameter_bound holds for m = 0 with (·)⁰ = 1.
- k = 0: μH[0] counts points. In (3b) the sets C_{ij} with j ∈ Jᵢ are nonempty, and in (4a) the indicator removes the empty C_{ij}, so the convention 0⁰ = 1 never matters.
- L = 0: volume_diameter_bound and the Lipschitz bound hold verbatim, with the [0, ∞] convention 0·∞ = 0.
- i = 0: ρ₀ = ∞; all inequalities above remain valid in [0, ∞], and single indices do not affect a liminf.

Formalization notes.
- Covers: choose C hCcov hCdiam hCsum on the covers from Submission.hausdorffMeasure_exists_cover_tsum_le_add with r = ε = (i : ℝ≥0∞)⁻¹ (ENNReal.inv_pos, ENNReal.inv_ne_zero, ENNReal.natCast_ne_top).
- Functions: G i y := ∑' j, (closure (f '' C i j)).indicator (fun _ => Metric.ediam (C i j) ^ (k : ℝ)) y.
- Measurability: Measurable.ennreal_tsum, measurable_const.indicator isClosed_closure.measurableSet, Measurable.liminf.
- Pointwise bound: Measure.hausdorffMeasure_le_liminf_tsum with the subtype index, liminf_le_liminf, tsum_subtype, ENNReal.tsum_le_tsum, Set.indicator_of_mem, Set.indicator_of_notMem.
- Integral bound: lintegral_tsum, lintegral_indicator_const, iSup_pos, gcongr, the sibling lemma Submission.volume_closure_le_unitBall_mul_ediam_pow, LipschitzWith.ediam_image_le, ENNReal.rpow_natCast, mul_pow, pow_add, ring, ENNReal.tsum_mul_left.
- Limit: lintegral_liminf_le, Tendsto.liminf_eq, ENNReal.Tendsto.const_mul, ENNReal.tendsto_inv_nat_nhds_zero, measure_ball_ne_top.

Appendix (non-normative formalization aid). The Lean proof below compiled with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c) in a scratch file outside the repository. The file begins with import GMT.Ch03.Submission and replays the frozen Contract scope exactly as the comparator does: open Filter MeasureTheory Module Set; open scoped CompactlySupported ENNReal NNReal Topology; namespace GMT.Ch03; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt HasWeightedApproximateTangentSpaceAt PurelyUnrectifiable blowUpMap). A scratch copy of the comparator's child target (theorem _root_.HumanizeNodeComparator.target : (frozen statement) := by exact Submission.X) accepted it, and the whole chain uses only the axioms propext, Classical.choice and Quot.sound. Measurable.ennreal_tsum emits only a deprecation warning.

theorem Submission.eilenberg_hausdorff_upper_integral_of_ne_top : ∀ (N m k : ℕ) (A : Set (Rn N)) (f : Rn N → Rn m) (L : ℝ≥0), LipschitzWith L f → μH[((m + k : ℕ) : ℝ)] A ≠ ∞ → ∃ g : Rn m → ℝ≥0∞, Measurable g ∧ (∀ y, μH[(k : ℝ)] (A ∩ f ⁻¹' {y}) ≤ g y) ∧ ∫⁻ y, g y ≤ volume (Metric.ball (0 : Rn m) 1) * (L : ℝ≥0∞) ^ m * μH[((m + k : ℕ) : ℝ)] A := by
  have hA := @Submission.hausdorffMeasure_exists_cover_tsum_le_add
  have hB := Submission.volume_closure_le_unitBall_mul_ediam_pow
  intro N m k A f L hf hA_fin
  set ω := volume (Metric.ball (0 : Rn m) 1) with hω
  have hω_top : ω ≠ ∞ := measure_ball_ne_top
  have hcov : ∀ i : ℕ, ∃ t : ℕ → Set (Rn N), A ⊆ ⋃ j, t j ∧ (∀ j, Metric.ediam (t j) ≤ (i : ℝ≥0∞)⁻¹) ∧ ∑' j, ⨆ _ : (t j).Nonempty, Metric.ediam (t j) ^ ((m + k : ℕ) : ℝ) ≤ μH[((m + k : ℕ) : ℝ)] A + (i : ℝ≥0∞)⁻¹ := fun i =>
    hA _ A _ _ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top i)) (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top i)) hA_fin
  choose C hCcov hCdiam hCsum using hcov
  set G : ℕ → Rn m → ℝ≥0∞ := fun i y => ∑' j, (closure (f '' C i j)).indicator (fun _ => Metric.ediam (C i j) ^ (k : ℝ)) y with hG
  have hGmeas : ∀ i, Measurable (G i) := fun i =>
    Measurable.ennreal_tsum fun j => measurable_const.indicator isClosed_closure.measurableSet
  refine ⟨fun y => liminf (fun i => G i y) atTop, Measurable.liminf hGmeas, ?_, ?_⟩
  · intro y
    have hcover : ∀ᶠ i in atTop, A ∩ f ⁻¹' {y} ⊆ ⋃ j : {j : ℕ // y ∈ f '' C i j}, C i j.1 :=
      Eventually.of_forall fun i x hx => by
        obtain ⟨j, hj⟩ := mem_iUnion.1 (hCcov i hx.1)
        exact mem_iUnion.2 ⟨⟨j, x, hj, hx.2⟩, hj⟩
    have h1 := Measure.hausdorffMeasure_le_liminf_tsum (ι := fun i : ℕ => {j : ℕ // y ∈ f '' C i j}) (k : ℝ) (A ∩ f ⁻¹' {y}) (l := atTop) (fun i : ℕ => (i : ℝ≥0∞)⁻¹) ENNReal.tendsto_inv_nat_nhds_zero (fun i j => C i j.1) (Eventually.of_forall fun i j => hCdiam i j.1) hcover
    refine h1.trans (liminf_le_liminf (Eventually.of_forall fun i => ?_))
    calc ∑' j : {j : ℕ // y ∈ f '' C i j}, Metric.ediam (C i j.1) ^ (k : ℝ)
        = ∑' j, ({j | y ∈ f '' C i j} : Set ℕ).indicator (fun j => Metric.ediam (C i j) ^ (k : ℝ)) j := tsum_subtype ({j | y ∈ f '' C i j} : Set ℕ) (fun j => Metric.ediam (C i j) ^ (k : ℝ))
      _ ≤ G i y := ENNReal.tsum_le_tsum fun j => by
          by_cases hj : y ∈ f '' C i j
          · rw [Set.indicator_of_mem (show j ∈ {j | y ∈ f '' C i j} from hj), Set.indicator_of_mem (subset_closure hj)]
          · rw [Set.indicator_of_notMem (show j ∉ {j | y ∈ f '' C i j} from hj)]
            exact bot_le
  · have hint : ∀ i : ℕ, ∫⁻ y, G i y ≤ ω * L ^ m * (μH[((m + k : ℕ) : ℝ)] A + (i : ℝ≥0∞)⁻¹) := by
      intro i
      rw [hG]
      dsimp only
      rw [lintegral_tsum (fun j => (measurable_const.indicator isClosed_closure.measurableSet).aemeasurable)]
      calc ∑' j, ∫⁻ y, (closure (f '' C i j)).indicator (fun _ => Metric.ediam (C i j) ^ (k : ℝ)) y
          = ∑' j, Metric.ediam (C i j) ^ (k : ℝ) * volume (closure (f '' C i j)) := by
            congr 1; ext j; exact lintegral_indicator_const isClosed_closure.measurableSet _
        _ ≤ ∑' j, ω * L ^ m * ⨆ _ : (C i j).Nonempty, Metric.ediam (C i j) ^ ((m + k : ℕ) : ℝ) := ENNReal.tsum_le_tsum fun j => by
            rcases (C i j).eq_empty_or_nonempty with h | h
            · simp [h]
            · rw [iSup_pos h]
              calc Metric.ediam (C i j) ^ (k : ℝ) * volume (closure (f '' C i j)) ≤ Metric.ediam (C i j) ^ (k : ℝ) * (ω * Metric.ediam (f '' C i j) ^ m) := by gcongr; exact hB m _
                _ ≤ Metric.ediam (C i j) ^ (k : ℝ) * (ω * (L * Metric.ediam (C i j)) ^ m) := by gcongr; exact hf.ediam_image_le _
                _ = ω * L ^ m * Metric.ediam (C i j) ^ ((m + k : ℕ) : ℝ) := by
                  rw [ENNReal.rpow_natCast, ENNReal.rpow_natCast, mul_pow, pow_add]; ring
        _ = ω * L ^ m * ∑' j, ⨆ _ : (C i j).Nonempty, Metric.ediam (C i j) ^ ((m + k : ℕ) : ℝ) := ENNReal.tsum_mul_left
        _ ≤ ω * L ^ m * (μH[((m + k : ℕ) : ℝ)] A + (i : ℝ≥0∞)⁻¹) := by gcongr; exact hCsum i
    calc ∫⁻ y, liminf (fun i => G i y) atTop ≤ liminf (fun i => ∫⁻ y, G i y) atTop := lintegral_liminf_le hGmeas
      _ ≤ liminf (fun i : ℕ => ω * L ^ m * (μH[((m + k : ℕ) : ℝ)] A + (i : ℝ≥0∞)⁻¹)) atTop := liminf_le_liminf (Eventually.of_forall hint)
      _ = ω * L ^ m * μH[((m + k : ℕ) : ℝ)] A := by
        apply Tendsto.liminf_eq
        have : Tendsto (fun i : ℕ => μH[((m + k : ℕ) : ℝ)] A + (i : ℝ≥0∞)⁻¹) atTop (𝓝 (μH[((m + k : ℕ) : ℝ)] A + 0)) := tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero
        rw [add_zero] at this
        exact ENNReal.Tendsto.const_mul this (Or.inr (ENNReal.mul_ne_top hω_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)))

## Key steps

1. For each i apply hausdorff_near_optimal_cover (d = m+k, r = ε = 1/i) to get covers C_{ij} of A with diam ≤ 1/i and Σⱼ cost_{m+k}(C_{ij}) ≤ μH[m+k](A) + 1/i.
2. Define the Borel functions gᵢ := Σⱼ diam(C_{ij})^k·1_{closure f(C_{ij})} and g := liminf gᵢ, which is Borel.
3. Pointwise: A ∩ f⁻¹{y} is covered by the C_{ij} with y ∈ f(C_{ij}), so μH[k](A ∩ f⁻¹{y}) ≤ liminf_i Σ_{j : y ∈ f(C_{ij})} diam(C_{ij})^k ≤ liminf gᵢ(y) = g(y) (hausdorffMeasure_le_liminf_tsum).
4. Integral: ∫gᵢ = Σⱼ diam(C_{ij})^k·λₘ(closure f(C_{ij})) ≤ ωₘL^m·Σⱼ cost_{m+k}(C_{ij}) ≤ ωₘL^m(μH[m+k](A) + 1/i), by volume_diameter_bound and diam f(C) ≤ L·diam C.
5. Fatou: ∫g ≤ liminf ∫gᵢ ≤ lim ωₘL^m(μH[m+k](A) + 1/i) = ωₘL^m·μH[m+k](A).

## Reference use

### local-project

Queries:
- `rg -n 'μHE|euclideanHausdorffMeasure' mathlib/Mathlib (snapshot)`
- `rg -n '^theorem|^lemma|^def|^noncomputable def' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'def ediam|def EMetric.diam' mathlib/Mathlib/Topology/EMetricSpace mathlib/Mathlib/Topology/MetricSpace`
- `rg -n 'theorem lintegral_liminf_le|theorem Measurable.liminf|theorem tendsto_inv_nat_nhds_zero|theorem lintegral_tsum|theorem lintegral_indicator_const|theorem addHaar_closedBall |theorem measure_closedBall_lt_top|theorem measure_closedBall_pos|theorem lintegral_const_mul |theorem Measurable.ennreal_tsum|theorem finrank_euclideanSpace_fin' mathlib/Mathlib`
- `rg -n 'ediam_closure|diam_closure' mathlib/Mathlib/Topology`
- `rg -n 'theorem ediam_image_le' mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `rg -n -i 'eilenberg|coarea inequality|upper integral' simongmt/Poincare mathlib/Mathlib`
- `rg -ln for the terms 1.9, 1.8, hausdorffMeasure_image_le, μH[ in simongmt/Poincare/SimonGMT/Chapter01, Chapter02, Chapter03`
- `rg -n '^theorem|^lemma' simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean simongmt/Poincare/SimonGMT/Chapter02/LipschitzMeasurability.lean simongmt/Poincare/SimonGMT/Chapter02/UpperIntegral.lean`
- `grep -rl hausdorffMeasure_exists_cover_tsum_le_add / volume_closure_le_unitBall_mul_ediam_pow / eilenberg_hausdorff_upper_integral_of_ne_top over .humanize, simongmt/Poincare and mathlib/Mathlib (name-collision check)`
- `cmp snapshot project/GMT/Ch03/Contract.lean with workspace GMT/Ch03/Contract.lean`
- `lake env lean on scratch files replaying the Contract scope from gmt-compare.py contract_scope (elaboration and proofs of children and parent assembly)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/UpperIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/LipschitzMeasurability.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`

Snapshot is project d09bc8a with Mathlib 25730c7c; the snapshot Contract is byte-identical to the workspace Contract.

Available and used:
- Normalization: μHE[d] = addHaarScalarFactor(volume, μH[d]) • μH[d] (euclideanHausdorffMeasure_def). So μHE[d] S = c_d·μH[d] S by rfl, and c_d ≠ 0 by addHaarScalarFactor_volume_hausdorffMeasure_ne_zero.
- Hausdorff measure: hausdorffMeasure_apply (sup over r > 0 of inf over countable covers, with cost ⨆ _ : Nonempty, ediam^d), which gives child A; hausdorffMeasure_le_liminf_tsum with dependent countable index types, used for child C's pointwise bound.
- Diameter: Metric.ediam lives in namespace Metric, which the Contract does not open, so the statements write Metric.ediam. Also Metric.ediam_closure, Metric.diam_closure and LipschitzWith.ediam_image_le.
- Ball volume: Measure.addHaar_closedBall, whose right side is ofReal(r^finrank)·μ(ball 0 1); this is why Metric.ball appears in the frozen statements. Also finrank_euclideanSpace_fin, measure_ball_ne_top and Metric.measure_ball_pos.
- Integration: lintegral_liminf_le (Fatou), lintegral_tsum, lintegral_indicator_const, lintegral_const_mul, Measurable.liminf, Measurable.ennreal_tsum (a deprecated alias) and ENNReal.tendsto_inv_nat_nhds_zero.

No match: neither Mathlib nor SimonGMT has an Eilenberg/coarea inequality, a near-optimal Hausdorff cover lemma in ∃-form, or a lemma bounding volume by ωₘ·diamᵐ. SimonGMT Chapter02 has only Theorem 1.8(i) (hausdorffMeasure_image_le_of_lipschitzOn, nullMeasurableSet_image_of_lipschitzOn*) and the Remark 1.10 upper integral (UpperIntegral.lean). Neither is needed, because the frozen type asks for a measurable majorant directly.

The three proposed names collide with nothing in the run's .humanize tree, SimonGMT or Mathlib.

Scratch Lean checks: A and B proved; C proved from A and B; the parent proved from C; comparator-style exact Submission.X targets accepted; the parent uses only the axioms propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
