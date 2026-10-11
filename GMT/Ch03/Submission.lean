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

/-- **Quantitative local injectivity of a `C¹` map with injective derivative** (Simon Ch. 3,
proof of Lemma 1.2, `chapter-03.txt` lines 61–64: where the Jacobian of `Gᵢⱼ` is non-zero at
`x`, `Gᵢⱼ(B_σ(x))` is an `n`-dimensional `C¹` submanifold). If `G : ℝⁿ → ℝᵖ` is `C¹` on an open
`U` and `L = DG(x)` is injective at `x ∈ U`, then for some closed ball `B̄_r(x) ⊆ U` and `c > 0`,
`c |z - z'| ≤ |G z - G z'|` and `c |v| ≤ |DG(z) v|` for all `z, z' ∈ B̄_r(x)` and `v`. In finite
dimension `L` is anti-Lipschitz, so `c₀ |v| ≤ |L v|`; `DG` is continuous, so `‖DG - L‖ ≤ c₀ / 2`
on a small ball; the mean value inequality for `G - L` and the triangle inequality then give
both bounds with `c = c₀ / 2`. -/
theorem Submission.c1_injective_fderiv_local_lower_bounds : ∀ (n p : ℕ) (G : Rn n → Rn p)
    (U : Set (Rn n)), IsOpen U → ContDiffOn ℝ 1 G U → ∀ x ∈ U,
    Function.Injective (fderiv ℝ G x) → ∃ r : ℝ, 0 < r ∧ Metric.closedBall x r ⊆ U ∧
      ∃ c : ℝ, 0 < c ∧ (∀ z ∈ Metric.closedBall x r, ∀ z' ∈ Metric.closedBall x r,
        c * ‖z - z'‖ ≤ ‖G z - G z'‖) ∧
        ∀ z ∈ Metric.closedBall x r, ∀ v : Rn n, c * ‖v‖ ≤ ‖fderiv ℝ G z v‖ := by
  intro n p G U hU hG x hx hinj
  -- Step 1: `G` is differentiable at every point of the open set `U`, and `DG` is continuous on
  -- `U`.
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ G z := fun z hz ↦
    (hG.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  have hcont : ContinuousOn (fderiv ℝ G) U := hG.continuousOn_fderiv_of_isOpen hU le_rfl
  -- Step 2: `L = DG(x)` is `K`-anti-Lipschitz, so `c₀ |v| ≤ |L v|` with `c₀ = K⁻¹`.
  obtain ⟨K, hK, hKL⟩ := (fderiv ℝ G x).injective_iff_antilipschitz.mp hinj
  have hKpos : (0 : ℝ) < K := NNReal.coe_pos.mpr hK
  have hc₀ : 0 < (K : ℝ)⁻¹ := inv_pos.mpr hKpos
  have hL : ∀ v, (K : ℝ)⁻¹ * ‖v‖ ≤ ‖fderiv ℝ G x v‖ := fun v ↦
    (inv_mul_le_iff₀ hKpos).mpr ((fderiv ℝ G x).bound_of_antilipschitz hKL v)
  -- Step 3: `r = min δ₁ δ₂ / 2`, where `B_{δ₁}(x) ⊆ U` and `‖DG(z) - L‖ < c₀ / 2` for `z ∈ U`
  -- with `|z - x| < δ₂`; then `B̄_r(x) ⊆ U` and `‖DG - L‖ ≤ c₀ / 2` on `B̄_r(x)`.
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨δ₂, hδ₂, hnear⟩ :=
    Metric.continuousOn_iff.mp hcont x hx ((K : ℝ)⁻¹ / 2) (half_pos hc₀)
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hr : ∀ z ∈ Metric.closedBall x (min δ₁ δ₂ / 2), dist z x < min δ₁ δ₂ := fun z hz ↦
    (Metric.mem_closedBall.mp hz).trans_lt (half_lt_self hδ)
  have hsub : Metric.closedBall x (min δ₁ δ₂ / 2) ⊆ U := fun z hz ↦
    hball (Metric.mem_ball.mpr ((hr z hz).trans_le (min_le_left _ _)))
  have hDG : ∀ z ∈ Metric.closedBall x (min δ₁ δ₂ / 2),
      ‖fderiv ℝ G z - fderiv ℝ G x‖ ≤ (K : ℝ)⁻¹ / 2 := fun z hz ↦ by
    have h := hnear z (hsub hz) ((hr z hz).trans_le (min_le_right _ _))
    rw [dist_eq_norm] at h
    exact h.le
  refine ⟨min δ₁ δ₂ / 2, half_pos hδ, hsub, (K : ℝ)⁻¹ / 2, half_pos hc₀, ?_, ?_⟩
  · -- Step 4: the mean value inequality for `w ↦ G w - L w` on the convex ball `B̄_r(x)`.
    intro z hz z' hz'
    have hmvt := (convex_closedBall x (min δ₁ δ₂ / 2)).norm_image_sub_le_of_norm_fderiv_le'
      (fun w hw ↦ hdiff w (hsub hw)) hDG hz' hz
    have htri : ‖fderiv ℝ G x (z - z')‖ ≤
        ‖G z - G z'‖ + ‖G z - G z' - fderiv ℝ G x (z - z')‖ := by
      calc ‖fderiv ℝ G x (z - z')‖
          = ‖(G z - G z') - (G z - G z' - fderiv ℝ G x (z - z'))‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    linarith [hL (z - z')]
  · -- Step 5: the operator-norm perturbation `|(DG(z) - L) v| ≤ (c₀ / 2) |v|`.
    intro z hz v
    have hop : ‖(fderiv ℝ G z - fderiv ℝ G x) v‖ ≤ (K : ℝ)⁻¹ / 2 * ‖v‖ :=
      ((fderiv ℝ G z - fderiv ℝ G x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hDG z hz) (norm_nonneg v))
    have htri : ‖fderiv ℝ G x v‖ ≤ ‖fderiv ℝ G z v‖ + ‖(fderiv ℝ G z - fderiv ℝ G x) v‖ := by
      calc ‖fderiv ℝ G x v‖ = ‖fderiv ℝ G z v - (fderiv ℝ G z - fderiv ℝ G x) v‖ := by
            rw [sub_apply, sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    linarith [hL v]
/-- **Simon Ch. 3, proof of Lemma 1.2 (p. 70)** (`chapter-03.txt` lines 61–64), with the
submanifold notion of Ch. 2 (4.1): if `G` is `C¹` and injective on `B̄_r(x)` and `DG(z)` is
injective for `z ∈ B_r(x)`, then `G(B_r(x))` is an embedded `C¹` submanifold, with the single
local representation `(V, W, ψ) = (B_r(x), ℝᵖ ∖ G(A), G)`, `A = B̄_r(x) ∖ B_r(x)`. `G(A)` is
compact, so `W` is open; injectivity on `B̄_r(x)` gives `G(B_r(x)) ⊆ W`; and for compact `K ⊆ W`,
`B_r(x) ∩ G⁻¹(K) = B̄_r(x) ∩ G⁻¹(K)` is a closed subset of the compact `B̄_r(x)`. -/
theorem Submission.isC1Submanifold_image_ball_of_injOn_closedBall : ∀ (n p : ℕ)
    (G : Rn n → Rn p) (x : Rn n) (r : ℝ), ContDiffOn ℝ 1 G (Metric.closedBall x r) →
    Set.InjOn G (Metric.closedBall x r) → (∀ z ∈ Metric.ball x r, Function.Injective
    (fderiv ℝ G z)) → IsC1Submanifold n (G '' Metric.ball x r) := by
  intro n p G x r hG hinj hD
  have hGc : ContinuousOn G (Metric.closedBall x r) := hG.continuousOn
  -- `A` is compact, so `G(A)` is closed and `W = G(A)ᶜ` is open.
  have hW : IsOpen (G '' (Metric.closedBall x r \ Metric.ball x r))ᶜ :=
    (((isCompact_closedBall x r).diff Metric.isOpen_ball).image_of_continuousOn
      (hGc.mono sdiff_subset)).isClosed.isOpen_compl
  -- Injectivity on `B̄_r(x)` keeps `G(B_r(x))` off `G(A)`.
  have hsub : G '' Metric.ball x r ⊆ (G '' (Metric.closedBall x r \ Metric.ball x r))ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ ⟨a, ha, hGa⟩
    exact ha.2 ((hinj ha.1 (Metric.ball_subset_closedBall hz) hGa).symm ▸ hz)
  intro y hy
  refine ⟨Metric.ball x r, (G '' (Metric.closedBall x r \ Metric.ball x r))ᶜ, G,
    Metric.isOpen_ball, hW, hsub hy, hG.mono Metric.ball_subset_closedBall,
    hinj.mono Metric.ball_subset_closedBall, (inter_eq_right.2 hsub).symm, fun K hK hKW ↦ ?_, hD⟩
  -- `B_r(x) ∩ G⁻¹(K) = B̄_r(x) ∩ G⁻¹(K)` since `K ⊆ W` misses `G(A)`.
  have heq : Metric.ball x r ∩ G ⁻¹' K = Metric.closedBall x r ∩ G ⁻¹' K := by
    refine Subset.antisymm (inter_subset_inter_left _ Metric.ball_subset_closedBall) ?_
    rintro z ⟨hz, hzK⟩
    refine ⟨?_, hzK⟩
    by_contra hzb
    exact hKW hzK ⟨z, ⟨hz, hzb⟩, rfl⟩
  rw [heq]
  exact (isCompact_closedBall x r).of_isClosed_subset
    (hGc.preimage_isClosed_of_isClosed Metric.isClosed_closedBall hK.isClosed) inter_subset_left

/-- **Simon Ch. 3, proof of Lemma 1.2 (p. 70)** (`chapter-03.txt` lines 61–64): if `G : ℝⁿ → ℝᵖ`
is `C¹` and `DG(x)` is injective, then `G(B_σ(x))` is an `n`-dimensional embedded `C¹` submanifold
for some `σ > 0` (erratum: "of `ℝⁿ`" should read "of `ℝᵖ`"). The lower bounds
`c|z - z'| ≤ |G(z) - G(z')|` and `c|v| ≤ |DG(z)v|` on a closed ball `B̄_σ(x)`
(`c1_injective_fderiv_local_lower_bounds`) make `G` injective on `B̄_σ(x)`, as properness in
Ch. 2, (4.1) requires, and `DG` injective on `B_σ(x)`. Then the single chart
`(B_σ(x), ℝᵖ ∖ G(B̄_σ(x) ∖ B_σ(x)), G)` works (`isC1Submanifold_image_ball_of_injOn_closedBall`). -/
theorem Submission.c1_regular_point_ball_image_isC1Submanifold : ∀ (n p : ℕ) (G : Rn n → Rn p),
    ContDiff ℝ 1 G → ∀ x : Rn n, Function.Injective (fderiv ℝ G x) →
      ∃ σ : ℝ, 0 < σ ∧ IsC1Submanifold n (G '' Metric.ball x σ) := by
  intro n p G hG x hx
  obtain ⟨σ, hσ, -, c, hc, hG_lower, hDG_lower⟩ :=
    Submission.c1_injective_fderiv_local_lower_bounds n p G univ isOpen_univ hG.contDiffOn x
      (mem_univ x) hx
  refine ⟨σ, hσ, Submission.isC1Submanifold_image_ball_of_injOn_closedBall n p G x σ
    hG.contDiffOn (fun z hz z' hz' hzz' ↦ ?_) fun z hz ↦ ?_⟩
  -- `G(z) = G(z')` with `z, z' ∈ B̄_σ(x)` gives `c|z - z'| ≤ 0`.
  · have h := hG_lower z hz z' hz'
    rw [hzz', sub_self, norm_zero] at h
    exact sub_eq_zero.1 (norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right h hc))
  -- `DG(z)v = 0` with `z ∈ B_σ(x) ⊆ B̄_σ(x)` gives `c|v| ≤ 0`.
  · refine (injective_iff_map_eq_zero (fderiv ℝ G z)).2 fun v hv ↦ ?_
    have h := hDG_lower z (Metric.ball_subset_closedBall hz) v
    rw [hv, norm_zero] at h
    exact norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right h hc)

/-- **Simon Ch. 3, proof of Lemma 1.2 (p. 70)** (`chapter-03.txt` lines 61–65), for one `C¹` map
`G : ℝⁿ → ℝᵖ`: `G(ℝⁿ)` lies in an `Hⁿ`-null set together with countably many embedded `C¹`
`n`-submanifolds. The critical image `N₀ = G({x : DG(x) not injective})` is `Hⁿ`-null (Simon's
area-formula step `Hⁿ(G({J_G = 0})) = 0`): Mathlib's
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` cuts the critical points in `B_m(0)`
by disjoint measurable sets into countably many pieces `P`, on each of which `G` is `δ`-close to
a non-injective `A = DG(y)`. For a unit `u ∈ ker A`, the stretch `S_a` by the factor `a` along
`u` has `det S_a = a`, and `G ∘ S_{1/δ}` is `(‖A‖ + 1)`-Lipschitz on `S_δ(P)`, so
`Hⁿ(G(P)) ≤ (‖A‖ + 1)ⁿ δ Lⁿ(P)`; with `δ = ε / (‖A‖ + 1)ⁿ` the total is at most `ε Lⁿ(B_m(0))`.
Every regular point `x` has a ball `B_σ(x)` with `G(B_σ(x))` a submanifold
(`c1_regular_point_ball_image_isC1Submanifold`). Countably many of these balls cover the regular
points (Lindelöf), and padding with `∅`, which is vacuously a submanifold, indexes their images
by `ℕ`. -/
theorem Submission.c1_range_null_union_submanifolds : ∀ (n p : ℕ) (G : Rn n → Rn p),
    ContDiff ℝ 1 G → ∃ (N₀ : Set (Rn p)) (N : ℕ → Set (Rn p)), μHE[n] N₀ = 0 ∧
      (∀ k, IsC1Submanifold n (N k)) ∧ Set.range G ⊆ N₀ ∪ ⋃ k, N k := by
  intro n p G hG
  -- Local estimate: if `G` is `δ`-close on `P` to a non-injective `A` (`0 < δ ≤ 1`), then
  -- `Hⁿ(G(P)) ≤ (‖A‖ + 1)ⁿ δ Lⁿ(P)`.
  have hlocal : ∀ (A : Rn n →L[ℝ] Rn p) (δ : ℝ≥0) (P : Set (Rn n)), ¬ Function.Injective A →
      0 < δ → δ ≤ 1 → ApproximatesLinearOn G A P δ →
      μHE[n] (G '' P) ≤ (((‖A‖₊ + 1) ^ n * δ : ℝ≥0) : ℝ≥0∞) * volume P := by
    intro A δ P hA hδ hδ1 hGA
    -- A unit vector `u` in the kernel of `A`.
    obtain ⟨v, hv, hv0⟩ : ∃ v, A v = 0 ∧ v ≠ 0 := by
      by_contra! h
      exact hA ((injective_iff_map_eq_zero A).2 h)
    have hu : ‖‖v‖⁻¹ • v‖ = 1 := norm_smul_inv_norm hv0
    have hAu : A (‖v‖⁻¹ • v) = 0 := by rw [map_smul, hv, smul_zero]
    generalize ‖v‖⁻¹ • v = u at hu hAu
    have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
    -- The stretch `S a` by the factor `a` along `u`; its matrix is `1 + (a - 1) u uᵀ`, so
    -- `det (S a) = 1 + (a - 1) |u|² = a`.
    have hstretch : ∀ a : ℝ, ∃ S : Rn n →L[ℝ] Rn n,
        (∀ w, S w = w + ((a - 1) * inner ℝ u w) • u) ∧
          LinearMap.det (S : Rn n →ₗ[ℝ] Rn n) = a := by
      intro a
      classical
      refine ⟨ContinuousLinearMap.id ℝ (Rn n) + (a - 1) • (innerSL ℝ u).smulRight u,
        fun w ↦ by simp [mul_smul], ?_⟩
      rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
      have h : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          ((ContinuousLinearMap.id ℝ (Rn n) + (a - 1) • (innerSL ℝ u).smulRight u :
            Rn n →L[ℝ] Rn n) : Rn n →ₗ[ℝ] Rn n) =
          1 + Matrix.replicateCol Unit (fun i ↦ (a - 1) * u i) *
            Matrix.replicateRow Unit (fun j ↦ u j) := by
        ext i j
        simp [LinearMap.toMatrix_apply, Matrix.one_apply, Matrix.mul_apply,
          EuclideanSpace.inner_single_right]
        ring
      have h1 : ∑ i, u i ^ 2 = 1 := by
        have h2 := real_inner_self_eq_norm_sq u
        rw [hu, PiLp.inner_apply] at h2
        simpa using h2
      rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct]
      simp_rw [mul_left_comm _ (a - 1), ← sq, ← Finset.mul_sum, h1]
      ring
    choose S hS hdet using hstretch
    have hSS : ∀ a b w, S a (S b w) = S (a * b) w := by
      intro a b w
      simp only [hS, inner_add_right, inner_smul_right, huu]
      rw [add_assoc, ← add_smul]
      congr 2
      ring
    have hS1 : ∀ w, S 1 w = w := by intro w; simp [hS]
    have hAS : ∀ a w, A (S a w) = A w := by
      intro a w; rw [hS, map_add, map_smul, hAu, smul_zero, add_zero]
    have hSle : ∀ a, 1 ≤ a → ∀ w, ‖S a w‖ ≤ a * ‖w‖ := by
      intro a ha w
      rw [hS]
      calc ‖w + ((a - 1) * inner ℝ u w) • u‖ ≤ ‖w‖ + ‖((a - 1) * inner ℝ u w) • u‖ :=
            norm_add_le _ _
        _ = ‖w‖ + |a - 1| * |inner ℝ u w| := by
            rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_mul]
        _ ≤ ‖w‖ + (a - 1) * ‖w‖ := by
            rw [abs_of_nonneg (by linarith)]
            gcongr
            exact (abs_real_inner_le_norm u w).trans (by rw [hu, one_mul])
        _ = a * ‖w‖ := by ring
    -- `G ∘ S δ⁻¹` maps `S δ (P)` onto `G (P)` and is `(‖A‖ + 1)`-Lipschitz there, since
    -- `A ∘ S δ⁻¹ = A` and `‖S δ⁻¹ w‖ ≤ δ⁻¹ ‖w‖`.
    have hδ0 : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ.ne'
    have hinv : ∀ z, S (δ : ℝ)⁻¹ (S δ z) = z := by
      intro z; rw [hSS, inv_mul_cancel₀ hδ0, hS1]
    have hlip : LipschitzOnWith (‖A‖₊ + 1) (G ∘ S (δ : ℝ)⁻¹) (S δ '' P) := by
      refine LipschitzOnWith.of_dist_le_mul fun w hw w' hw' ↦ ?_
      obtain ⟨z, hz, rfl⟩ := hw
      obtain ⟨z', hz', rfl⟩ := hw'
      simp only [Function.comp_apply, hinv, dist_eq_norm]
      have hzz : z - z' = S (δ : ℝ)⁻¹ (S δ z - S δ z') := by rw [map_sub, hinv, hinv]
      have h1 : ‖A (z - z')‖ ≤ ‖A‖ * ‖S δ z - S δ z'‖ := by
        rw [hzz, hAS]; exact A.le_opNorm _
      have h2 : (δ : ℝ) * ‖z - z'‖ ≤ ‖S δ z - S δ z'‖ := by
        rw [hzz]
        calc (δ : ℝ) * ‖S (δ : ℝ)⁻¹ (S δ z - S δ z')‖
            ≤ δ * ((δ : ℝ)⁻¹ * ‖S δ z - S δ z'‖) := by
              gcongr
              exact hSle _ (one_le_inv₀ (by exact_mod_cast hδ) |>.2 (by exact_mod_cast hδ1)) _
          _ = ‖S δ z - S δ z'‖ := by rw [← mul_assoc, mul_inv_cancel₀ hδ0, one_mul]
      calc ‖G z - G z'‖ ≤ ‖A (z - z')‖ + ‖G z - G z' - A (z - z')‖ := norm_le_insert' _ _
        _ ≤ ‖A‖ * ‖S δ z - S δ z'‖ + δ * ‖z - z'‖ := add_le_add h1 (hGA z hz z' hz')
        _ ≤ ‖A‖ * ‖S δ z - S δ z'‖ + ‖S δ z - S δ z'‖ := by linarith
        _ = ((‖A‖₊ + 1 : ℝ≥0) : ℝ) * ‖S δ z - S δ z'‖ := by push_cast; ring
    have himage : (G ∘ S (δ : ℝ)⁻¹) '' (S δ '' P) = G '' P := by
      rw [image_image]; simp only [Function.comp_apply, hinv]
    -- `Hⁿ = Lⁿ` on `ℝⁿ` and `Lⁿ(S δ (P)) = |det (S δ)| Lⁿ(P) = δ Lⁿ(P)`.
    calc μHE[n] (G '' P) = μHE[n] ((G ∘ S (δ : ℝ)⁻¹) '' (S δ '' P)) := by rw [himage]
      _ ≤ ((‖A‖₊ + 1 : ℝ≥0) : ℝ≥0∞) ^ n * μHE[n] (S δ '' P) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hlip
      _ = ((‖A‖₊ + 1 : ℝ≥0) : ℝ≥0∞) ^ n * (ENNReal.ofReal |(δ : ℝ)| * volume P) := by
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
            Measure.addHaar_image_continuousLinearMap, hdet]
      _ = _ := by
          rw [abs_of_nonneg δ.coe_nonneg, ENNReal.ofReal_coe_nnreal]; push_cast; ring
  -- The critical image is `Hⁿ`-null: its part over `B_m(0)` has measure `≤ ε Lⁿ(B_m(0))` for
  -- every `ε ∈ (0, 1]`.
  have hN₀ : μHE[n] (G '' {x | ¬ Function.Injective (fderiv ℝ G x)}) = 0 := by
    set C : Set (Rn n) := {x | ¬ Function.Injective (fderiv ℝ G x)}
    have hball : ∀ m : ℕ, μHE[n] (G '' (C ∩ Metric.ball 0 m)) = 0 := by
      intro m
      have hbound : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
          μHE[n] (G '' (C ∩ Metric.ball 0 m)) ≤ ε * volume (Metric.ball (0 : Rn n) m) := by
        intro ε hε hε1
        -- Pieces `C ∩ B_m(0) ∩ t k` on which `G` is `ε / (‖A k‖ + 1)ⁿ`-close to `A k = DG(y)`.
        obtain ⟨t, A, t_disj, t_meas, t_cover, ht, hAf⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G (C ∩ Metric.ball 0 m)
            (fderiv ℝ G)
            (fun x _ ↦ (hG.differentiable one_ne_zero x).hasFDerivAt.hasFDerivWithinAt)
            (fun A ↦ ε / (‖A‖₊ + 1) ^ n) fun A ↦ (div_pos hε (by positivity)).ne'
        have hpiece : ∀ k, μHE[n] (G '' (C ∩ Metric.ball 0 m ∩ t k)) ≤
            ε * volume (Metric.ball (0 : Rn n) m ∩ t k) := by
          intro k
          rcases (C ∩ Metric.ball (0 : Rn n) m).eq_empty_or_nonempty with h | h
          · simp [h]
          obtain ⟨y, hy, hAy⟩ := hAf h k
          have hc : (1 : ℝ≥0) ≤ (‖A k‖₊ + 1) ^ n := one_le_pow₀ (le_add_of_nonneg_left zero_le)
          calc μHE[n] (G '' (C ∩ Metric.ball 0 m ∩ t k))
              ≤ (((‖A k‖₊ + 1) ^ n * (ε / (‖A k‖₊ + 1) ^ n) : ℝ≥0) : ℝ≥0∞) *
                  volume (C ∩ Metric.ball 0 m ∩ t k) :=
                hlocal (A k) _ _ (hAy ▸ hy.1) (div_pos hε (zero_lt_one.trans_le hc))
                  (div_le_one_of_le₀ (hε1.trans hc) zero_le) (ht k)
            _ ≤ ε * volume (Metric.ball (0 : Rn n) m ∩ t k) := by
                rw [mul_div_cancel₀ _ (zero_lt_one.trans_le hc).ne']
                gcongr
                exact inter_subset_right
        -- Summing over the disjoint measurable `t k`.
        calc μHE[n] (G '' (C ∩ Metric.ball 0 m))
            ≤ μHE[n] (⋃ k, G '' (C ∩ Metric.ball 0 m ∩ t k)) := by
              refine measure_mono ?_
              rw [← image_iUnion, ← inter_iUnion]
              exact image_mono (subset_inter subset_rfl t_cover)
          _ ≤ ∑' k, μHE[n] (G '' (C ∩ Metric.ball 0 m ∩ t k)) := measure_iUnion_le _
          _ ≤ ∑' k, (ε : ℝ≥0∞) * volume (Metric.ball (0 : Rn n) m ∩ t k) :=
              ENNReal.tsum_le_tsum hpiece
          _ = ε * volume (⋃ k, Metric.ball (0 : Rn n) m ∩ t k) := by
              rw [ENNReal.tsum_mul_left, measure_iUnion
                (fun i j hij ↦ (t_disj hij).mono inter_subset_right inter_subset_right)
                fun k ↦ measurableSet_ball.inter (t_meas k)]
          _ ≤ ε * volume (Metric.ball (0 : Rn n) m) := by
              gcongr
              exact iUnion_subset fun k ↦ inter_subset_left
      -- Let `ε ↓ 0`; `Lⁿ(B_m(0)) < ∞`.
      have hlim : Tendsto (fun ε : ℝ≥0 ↦ (ε : ℝ≥0∞) * volume (Metric.ball (0 : Rn n) m))
          (𝓝[>] 0) (𝓝 0) := by
        have h1 : Tendsto (fun ε : ℝ≥0 ↦ (ε : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) := by
          simpa using (ENNReal.continuous_coe.tendsto (0 : ℝ≥0)).mono_left nhdsWithin_le_nhds
        simpa using ENNReal.Tendsto.mul_const h1
          (Or.inr (measure_ball_lt_top (μ := (volume : Measure (Rn n))) (x := 0) (r := m)).ne)
      refine le_antisymm (ge_of_tendsto hlim ?_) zero_le
      filter_upwards [Ioc_mem_nhdsGT one_pos] with ε hε
      exact hbound ε hε.1 hε.2
    have hU : G '' C = ⋃ m : ℕ, G '' (C ∩ Metric.ball 0 m) := by
      rw [← image_iUnion, ← inter_iUnion, Metric.iUnion_ball_nat, inter_univ]
    rw [hU]
    exact measure_iUnion_null hball
  -- A radius `σ x > 0` at every `x`, with `G(B_{σ x}(x))` a submanifold when `DG(x)` is injective.
  have hradius : ∀ x : Rn n, ∃ σ : ℝ, 0 < σ ∧
      (Function.Injective (fderiv ℝ G x) → IsC1Submanifold n (G '' Metric.ball x σ)) := by
    intro x
    by_cases hx : Function.Injective (fderiv ℝ G x)
    · obtain ⟨σ, hσ, hS⟩ := Submission.c1_regular_point_ball_image_isC1Submanifold n p G hG x hx
      exact ⟨σ, hσ, fun _ ↦ hS⟩
    · exact ⟨1, one_pos, fun h ↦ absurd h hx⟩
  choose σ hσ hS using hradius
  -- Lindelöf: the balls around the points of a countable `T` cover all regular points.
  obtain ⟨T, hTR, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable
    {x | Function.Injective (fderiv ℝ G x)} (fun x ↦ Metric.ball x (σ x))
    fun x _ ↦ Metric.isOpen_ball
  -- Enumerate `{∅} ∪ {G(B_{σ x}(x)) : x ∈ T}` by `ℕ`.
  obtain ⟨N, hN⟩ := ((hTc.image fun x ↦ G '' Metric.ball x (σ x)).insert ∅).exists_eq_range
    (insert_nonempty _ _)
  refine ⟨G '' {x | ¬ Function.Injective (fderiv ℝ G x)}, N, hN₀, fun k ↦ ?_, ?_⟩
  · have hk : N k ∈ insert ∅ ((fun x ↦ G '' Metric.ball x (σ x)) '' T) := by
      rw [hN]
      exact mem_range_self k
    rcases hk with hk | ⟨x, hxT, hx⟩
    · rw [hk]
      exact fun y hy ↦ absurd hy (notMem_empty y)
    · rw [← hx]
      exact hS x (hTR hxT)
  · rintro _ ⟨z, rfl⟩
    by_cases hz : Function.Injective (fderiv ℝ G z)
    · have hzT : z ∈ ⋃ x ∈ {x | Function.Injective (fderiv ℝ G x)}, Metric.ball x (σ x) :=
        mem_biUnion hz (Metric.mem_ball_self (hσ z))
      rw [← hTU] at hzT
      obtain ⟨x, hxT, hzx⟩ := mem_iUnion₂.1 hzT
      have hx : G '' Metric.ball x (σ x) ∈ range N := by
        rw [← hN]
        exact mem_insert_of_mem _ (mem_image_of_mem _ hxT)
      obtain ⟨k, hk⟩ := hx
      exact Or.inr (mem_iUnion.2 ⟨k, by rw [hk]; exact mem_image_of_mem G hzx⟩)
    · exact Or.inl ⟨z, hz, rfl⟩

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
