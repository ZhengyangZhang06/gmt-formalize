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

/-- **Slice integrals over a `C¹` chart** (steps 1–3 of the supplied proof of the chart formula
for the `C¹` parametric co-area formula, Simon Ch. 3, (2.8)–(2.9)). Let `Φ` be an open partial
homeomorphism from `ℝ^{m+k}` to `ℝᵐ × ℝᵏ` (Euclidean product) whose first component is `G` and
whose inverse is `C¹`, let `ψ` be `C¹` and injective on `Φ.source`, and let `B ⊆ Φ.source` be
Borel. If the injective area formula (AF) holds for `φ` in dimension `k`, then for every `y ∈ ℝᵐ`,
`∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ = ∫_{ℝᵏ} F(y, z) dz` with `F = 1_{Φ(B)} · φ ∘ ψ ∘ Φ⁻¹ ·
normDet(D(ψ ∘ Φ⁻¹) ∘ j)`, `j z = (0, z)`: apply (AF) to `χ = ψ ∘ Φ⁻¹ ∘ ι`, `ι z = (y, z)`, on the
Borel set `S = ι⁻¹(Φ(B))`, whose image is `ψ(B ∩ G⁻¹{y})`, and use `Dχ(z) = D(ψ ∘ Φ⁻¹)(ι z) ∘ j`. -/
theorem Submission.pcoarea_chart_slice_lintegral : ∀ (m k N : ℕ) (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m) (Φ : OpenPartialHomeomorph (Rn (m + k)) (WithLp 2 (Rn m × Rn k))), ContDiffOn ℝ 1 ψ Φ.source → InjOn ψ Φ.source → ContDiffOn ℝ 1 Φ.symm Φ.target → (∀ u ∈ Φ.source, (Φ u).fst = G u) → ∀ B ⊆ Φ.source, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, (∀ (V : Set (Rn k)) (χ : Rn k → Rn N), IsOpen V → ContDiffOn ℝ 1 χ V → InjOn χ V → ∀ S ⊆ V, MeasurableSet S → ∫⁻ x in χ '' S, φ x ∂μHE[k] = ∫⁻ z in S, φ (χ z) * ENNReal.ofReal ((fderiv ℝ χ z).toLinearMap.normDet)) → ∀ y : Rn m, ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k] = ∫⁻ z : Rn k, (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet)) (WithLp.toLp 2 (y, z)) := by
  intro m k N ψ G Φ hψ hinj hΦs hfst B hB hBm φ hAF y
  classical
  -- Step 1: the slice map `ι z = (y, z)` has derivative `j z = (0, z)`, is `C¹` and injective.
  set j : Rn k →L[ℝ] WithLp 2 (Rn m × Rn k) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ (Rn m) (Rn k))
  let ι : Rn k → WithLp 2 (Rn m × Rn k) := fun z ↦ WithLp.toLp 2 (y, z)
  have hιd : ∀ z, HasFDerivAt ι j z := by
    intro z
    have h1 : HasFDerivAt (fun z : Rn k ↦ (y, z)) (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)) z :=
      hasFDerivAt_prodMk_right y z
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.hasFDerivAt.comp z h1
  have hιcd : ContDiff ℝ 1 ι :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.contDiff.comp
      (contDiff_const.prodMk contDiff_id)
  have hιc : Continuous ι := hιcd.continuous
  have hιinj : Function.Injective ι := by
    intro z₁ z₂ h
    simpa [ι] using congrArg WithLp.snd h
  -- Step 2: `Φ(B)` is a Borel subset of `Φ.target` (Lusin–Souslin).
/-- **Chart integrand of the parametric co-area formula: Borel measurability and Tonelli.**
Let `Φ` be an open partial homeomorphism from `ℝⁿ`, `n = m + k`, onto an open subset `Ω` of the
Euclidean product `P = WithLp 2 (ℝᵐ × ℝᵏ)`, let `ψ` be continuous on `O = Φ.source`, `B ⊆ O` Borel
and `φ ≥ 0` Borel. With `ρ = ψ ∘ Φ⁻¹` and `j z = toLp (0, z)`, the function
`F = 1_{Φ(B)} · (φ ∘ ρ) · normDet (Dρ ∘ j)` on `P` is Borel: `Φ(B)` is Borel by Lusin–Souslin
(`Φ` is continuous and injective on `O`), `ρ` agrees on `Φ(B)` with the Borel map
`Ω.piecewise ρ 0`, `w ↦ Dρ(w)` is Borel for every `ρ` (`measurable_fderiv`) and
`normDet M = √det (M† M)` is continuous in `M`. Since `toLp` carries `Lᵐ ⊗ Lᵏ` to the volume of
`P`, Tonelli's theorem gives that `y ↦ ∫ F(toLp (y, z)) dLᵏ(z)` is Borel and
`∫_P F = ∫_{ℝᵐ} ∫_{ℝᵏ} F(toLp (y, z)) dLᵏ(z) dLᵐ(y)`. No differentiability is assumed. -/
theorem Submission.pcoarea_chart_integrand_tonelli : ∀ (m k N : ℕ) (ψ : Rn (m + k) → Rn N) (Φ : OpenPartialHomeomorph (Rn (m + k)) (WithLp 2 (Rn m × Rn k))), ContinuousOn ψ Φ.source → ∀ B ⊆ Φ.source, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ → Measurable (fun y : Rn m ↦ ∫⁻ z : Rn k, (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet)) (WithLp.toLp 2 (y, z))) ∧ ∫⁻ w, (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet)) w = ∫⁻ y : Rn m, ∫⁻ z : Rn k, (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet)) (WithLp.toLp 2 (y, z)) := by
  intro m k N ψ Φ hψ B hB hBm φ hφ
  classical
  set j : Rn k →L[ℝ] WithLp 2 (Rn m × Rn k) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ (Rn m) (Rn k))
  -- Step 1: `Φ(B)` is Borel (Lusin–Souslin) and lies in `Ω = Φ.target`.
  have hB' : MeasurableSet (Φ '' B) :=
    hBm.image_of_continuousOn_injOn (Φ.continuousOn.mono hB) (Φ.injOn.mono hB)
  have hB'Ω : Φ '' B ⊆ Φ.target := by
    rintro _ ⟨u, hu, rfl⟩
    exact Φ.map_source (hB hu)
  -- Step 3: `V = ι⁻¹(Φ.target)` is open and `S = ι⁻¹(Φ(B)) ⊆ V` is Borel.
  have hV : IsOpen (ι ⁻¹' Φ.target) := Φ.open_target.preimage hιc
  have hS : MeasurableSet (ι ⁻¹' (Φ '' B)) := hιc.measurable hB'
  have hSV : ι ⁻¹' (Φ '' B) ⊆ ι ⁻¹' Φ.target := fun z hz ↦ hB'Ω hz
  -- Steps 4–5: `χ = ψ ∘ Φ⁻¹ ∘ ι` is `C¹` and injective on `V`.
  let χ : Rn k → Rn N := fun z ↦ ψ (Φ.symm (ι z))
  have hχ : ContDiffOn ℝ 1 χ (ι ⁻¹' Φ.target) := by
    have h1 : ContDiffOn ℝ 1 (fun z ↦ Φ.symm (ι z)) (ι ⁻¹' Φ.target) :=
      hΦs.comp hιcd.contDiffOn (fun z hz ↦ hz)
    exact hψ.comp h1 (fun z hz ↦ Φ.map_target hz)
  have hχi : InjOn χ (ι ⁻¹' Φ.target) := by
    intro z₁ h₁ z₂ h₂ h
    exact hιinj (Φ.symm.injOn h₁ h₂ (hinj (Φ.map_target h₁) (Φ.map_target h₂) h))
  -- Step 6: `ψ(B ∩ G⁻¹{y}) = χ(S)`, since `ι((Φ u).snd) = Φ u` when `G u = y`.
  have himg : ψ '' (B ∩ G ⁻¹' {y}) = χ '' (ι ⁻¹' (Φ '' B)) := by
    ext x
    constructor
    · rintro ⟨u, ⟨huB, huG⟩, rfl⟩
      have hfu : (Φ u).fst = y := (hfst u (hB huB)).trans huG
      have hιu : ι (Φ u).snd = Φ u := by
        show WithLp.toLp 2 (y, (Φ u).snd) = Φ u
        rw [← hfu]
        rfl
      refine ⟨(Φ u).snd, ?_, ?_⟩
      · show ι (Φ u).snd ∈ Φ '' B
        rw [hιu]
        exact ⟨u, huB, rfl⟩
      · show ψ (Φ.symm (ι (Φ u).snd)) = ψ u
        rw [hιu, Φ.left_inv (hB huB)]
    · rintro ⟨z, ⟨u, huB, hu⟩, rfl⟩
      refine ⟨u, ⟨huB, ?_⟩, ?_⟩
      · show G u = y
        rw [← hfst u (hB huB), hu]
        rfl
      · show ψ u = ψ (Φ.symm (ι z))
        rw [← hu, Φ.left_inv (hB huB)]
  -- Step 8: chain rule on `V`, `Dχ(z) = D(ψ ∘ Φ⁻¹)(ι z) ∘ j`.
  have hderiv : ∀ z ∈ ι ⁻¹' Φ.target, fderiv ℝ χ z = (fderiv ℝ (ψ ∘ Φ.symm) (ι z)).comp j := by
    intro z hz
    have hΦsd : DifferentiableAt ℝ Φ.symm (ι z) :=
      (hΦs.differentiableOn one_ne_zero _ hz).differentiableAt (Φ.open_target.mem_nhds hz)
    have hψd : DifferentiableAt ℝ ψ (Φ.symm (ι z)) :=
      (hψ.differentiableOn one_ne_zero _ (Φ.map_target hz)).differentiableAt
        (Φ.open_source.mem_nhds (Φ.map_target hz))
    have hχeq : χ = (ψ ∘ Φ.symm) ∘ ι := rfl
    rw [hχeq, fderiv_comp z (hψd.comp (ι z) hΦsd) (hιd z).differentiableAt, (hιd z).fderiv]
  -- Steps 7, 9, 10: apply (AF) on `(V, χ, S)` and compare the integrands pointwise.
  rw [himg, hAF (ι ⁻¹' Φ.target) χ hV hχ hχi (ι ⁻¹' (Φ '' B)) hSV hS, ← lintegral_indicator hS]
  refine lintegral_congr fun z ↦ ?_
  by_cases hz : z ∈ ι ⁻¹' (Φ '' B)
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show WithLp.toLp 2 (y, z) ∈ Φ '' B from hz),
      hderiv z (hSV hz)]
  · rw [Set.indicator_of_notMem hz,
      Set.indicator_of_notMem (show WithLp.toLp 2 (y, z) ∉ Φ '' B from hz)]
  -- Step 2: `ρ = ψ ∘ Φ⁻¹` is continuous on the open set `Ω`, so `Ω.piecewise ρ 0` is Borel.
  have hρ : ContinuousOn (ψ ∘ Φ.symm) Φ.target :=
    hψ.comp Φ.continuousOn_symm (fun w hw ↦ Φ.map_target hw)
  have hρm : Measurable (Φ.target.piecewise (ψ ∘ Φ.symm) (fun _ ↦ 0)) :=
    hρ.measurable_piecewise continuousOn_const Φ.open_target.measurableSet
  -- Step 3: `normDet M = √det (M† M)` is continuous, so the Jacobian factor is Borel.
  have hnd : Continuous (fun M : Rn k →L[ℝ] Rn N ↦ M.toLinearMap.normDet) := by
    have heq : (fun M : Rn k →L[ℝ] Rn N ↦ M.toLinearMap.normDet) =
        fun M ↦ Real.sqrt ((M.adjoint ∘L M).det) := by
      funext M
      rw [← M.normDet_sq]
      simpa only [RCLike.ofReal_real_eq_id, id_eq] using (Real.sqrt_sq M.normDet_nonneg).symm
    rw [heq]
    exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
  have ha : Measurable
      (fun w ↦ ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp j).toLinearMap.normDet)) :=
    ENNReal.measurable_ofReal.comp
      ((hnd.comp (continuous_id.clm_comp continuous_const)).measurable.comp (measurable_fderiv ℝ _))
  -- Step 4: on `Φ(B)` the integrand agrees with a Borel function, so it is Borel.
  have hFeq : (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) *
        ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp j).toLinearMap.normDet)) =
      (Φ '' B).indicator (fun w ↦ φ (Φ.target.piecewise (ψ ∘ Φ.symm) (fun _ ↦ 0) w) *
        ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp j).toLinearMap.normDet)) := by
    apply Set.indicator_congr
    intro w hw
    simp only [Set.piecewise_eq_of_mem _ _ _ (hB'Ω hw), Function.comp_apply]
  have hFm : Measurable ((Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) *
      ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp j).toLinearMap.normDet))) := by
    rw [hFeq]
    exact ((hφ.comp hρm).mul ha).indicator hB'
  -- Step 5: transport along the measure-preserving `toLp` and apply Tonelli on `ℝᵐ × ℝᵏ`.
  have hmp := WithLp.volume_preserving_toLp (Rn m) (Rn k)
  have hFp := hFm.comp (WithLp.measurable_toLp 2 (Rn m × Rn k))
  refine ⟨hFp.lintegral_prod_right', ?_⟩
  rw [← hmp.lintegral_comp hFm, Measure.volume_eq_prod]
  exact lintegral_prod _ hFp.aemeasurable
/-- **Change of variables from `ℝⁿ` into `P = WithLp 2 (ℝᵐ × ℝᵏ)`** (`n = m + k`; Simon Ch. 3,
(2.8)–(2.9), `chapter-03.txt` lines 412–436, via the `C¹` co-area formula Ch. 2 (6.3),
`chapter-02.txt` lines 1462–1476, whose proof Simon omits; this is the injective
equal-dimensional case of the area formula Ch. 2 (3.1)–(3.5), `chapter-02.txt` lines 743–797):
if `f : ℝⁿ → P` has derivative `f'(u)` within the Borel set `B` at every `u ∈ B` and is injective
on `B`, then `∫_{f(B)} g = ∫_B normDet(f'(u)) · g(f(u)) du` for every `g : P → [0, ∞]`.
As `finrank P = n`, there is a linear isometric equivalence `e : P ≃ ℝⁿ`; `e⁻¹` preserves volume,
Mathlib's change of variables applies to `e ∘ f` on `B`, and
`|det(e ∘ f'(u))| = normDet(e) · normDet(f'(u)) = normDet(f'(u))`. -/
theorem Submission.pcoarea_chart_change_of_variables : ∀ (m k : ℕ) (f : Rn (m + k) → WithLp 2 (Rn m × Rn k)) (f' : Rn (m + k) → Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)) (B : Set (Rn (m + k))), MeasurableSet B → (∀ u ∈ B, HasFDerivWithinAt f (f' u) B u) → InjOn f B → ∀ g : WithLp 2 (Rn m × Rn k) → ℝ≥0∞, ∫⁻ w in f '' B, g w = ∫⁻ u in B, ENNReal.ofReal ((f' u).toLinearMap.normDet) * g (f u) := by
  intro m k f f' B hB hf hinj g
  -- Step 1: `finrank P = m + k`.
  have hfin : finrank ℝ (WithLp 2 (Rn m × Rn k)) = m + k := by
    rw [(WithLp.linearEquiv 2 ℝ (Rn m × Rn k)).finrank_eq, Module.finrank_prod]
    simp
  -- Step 2: a linear isometric equivalence `e : P ≃ ℝⁿ`, and `E = e` as a continuous linear map.
  let e : WithLp 2 (Rn m × Rn k) ≃ₗᵢ[ℝ] Rn (m + k) :=
    ((stdOrthonormalBasis ℝ (WithLp 2 (Rn m × Rn k))).reindex (finCongr hfin)).repr
  let E : WithLp 2 (Rn m × Rn k) →L[ℝ] Rn (m + k) := e.toContinuousLinearEquiv
  -- Step 3: `e⁻¹` is a volume-preserving measurable embedding, so
  -- `∫_{e(f(B))} g ∘ e⁻¹ = ∫_{f(B)} g`.
  have hes : MeasurePreserving e.symm volume volume := e.symm.measurePreserving
  have h1 : ∫⁻ v in e '' (f '' B), g (e.symm v) = ∫⁻ w in f '' B, g w := by
    rw [hes.setLIntegral_comp_emb e.symm.toHomeomorph.measurableEmbedding]
    congr 2
    rw [Set.image_image]
    simp
  -- Step 4: `e ∘ f` has derivative `E ∘ f'(u)` within `B` and is injective on `B`.
  have hder : ∀ u ∈ B, HasFDerivWithinAt (fun u ↦ e (f u)) (E.comp (f' u)) B u := fun u hu ↦
    E.hasFDerivAt.comp_hasFDerivWithinAt u (hf u hu)
  have hinj' : InjOn (fun u ↦ e (f u)) B := fun a ha b hb hab ↦ hinj ha hb (e.injective hab)
  -- Step 5: Mathlib's change of variables for `e ∘ f` and the integrand `g ∘ e⁻¹`.
  have h2 := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hB hder hinj'
    (fun v ↦ g (e.symm v))
  -- Step 7: combine; on `B` it remains to compare the Jacobians, as `e⁻¹ (e (f u)) = f u`.
  rw [← h1, Set.image_image, h2]
  refine setLIntegral_congr_fun hB (fun u hu ↦ ?_)
  simp only [LinearIsometryEquiv.symm_apply_apply]
  congr 2
  -- Step 6: `|det (E ∘ f'(u))| = normDet E · normDet (f'(u)) = normDet (f'(u))`.
  have hE : (E : WithLp 2 (Rn m × Rn k) →ₗ[ℝ] Rn (m + k)).normDet = 1 :=
    LinearIsometry.normDet_eq_one e.toLinearIsometry
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, ← LinearMap.normDet_eq_abs_det,
    LinearMap.normDet_comp_of_finrank_eq _ _ (by rw [hfin, finrank_euclideanSpace_fin]), hE,
    one_mul]
/-- **Pointwise Jacobian identity on a `C¹` chart** (steps 1 and 7 of the supplied proof of the
chart formula for the `C¹` parametric co-area formula, Simon Ch. 3, (2.8)–(2.9)). Let `Φ` be an
open partial homeomorphism from `ℝ^{m+k}` to `ℝᵐ × ℝᵏ` (Euclidean product) such that `Φ` and `Φ⁻¹`
are `C¹`, whose first component is `G`, and let `ψ` be `C¹` on `Φ.source`. If the flat Jacobian
identity (FJ) holds for `(m, k, N)`, then at every `u ∈ Φ.source`, with `j z = (0, z)`,
`normDet(D(ψ ∘ Φ⁻¹)(Φ u) ∘ j) · normDet(DΦ(u)) = normDet(Dψ(u) ∘ ι_{ker DG(u)}) · normDet(DG(u)*)`:
`DΦ(u)` and `DΦ⁻¹(Φ u)` are mutually inverse, `DG(u) = fst ∘ DΦ(u)`, and (FJ) applies to
`A = Dψ(u)`, `Γ = DG(u)`, `T = DΦ(u)` and `E = DΦ⁻¹(Φ u) ∘ j`. -/
theorem Submission.pcoarea_chart_pointwise_jacobian : ∀ (m k N : ℕ) (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m) (Φ : OpenPartialHomeomorph (Rn (m + k)) (WithLp 2 (Rn m × Rn k))), ContDiffOn ℝ 1 ψ Φ.source → ContDiffOn ℝ 1 Φ Φ.source → ContDiffOn ℝ 1 Φ.symm Φ.target → (∀ u ∈ Φ.source, (Φ u).fst = G u) → (∀ (A : Rn (m + k) →ₗ[ℝ] Rn N) (Γ : Rn (m + k) →ₗ[ℝ] Rn m) (T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k)) (E : Rn k →ₗ[ℝ] Rn (m + k)), Function.Bijective T → (∀ v, (T v).fst = Γ v) → (∀ z, T (E z) = WithLp.toLp 2 (0, z)) → (A ∘ₗ E).normDet * T.normDet = (A ∘ₗ (LinearMap.ker Γ).subtype).normDet * (LinearMap.adjoint Γ).normDet) → ∀ u ∈ Φ.source, ((fderiv ℝ (ψ ∘ Φ.symm) (Φ u)).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet * (fderiv ℝ Φ u).toLinearMap.normDet = ((fderiv ℝ ψ u).toLinearMap ∘ₗ (LinearMap.ker (fderiv ℝ G u).toLinearMap).subtype).normDet * (LinearMap.adjoint (fderiv ℝ G u).toLinearMap).normDet := by
  intro m k N ψ G Φ hψ hΦ hΦs hfst hFJ u hu
  set j : Rn k →L[ℝ] WithLp 2 (Rn m × Rn k) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ (Rn m) (Rn k))
  have hw : Φ u ∈ Φ.target := Φ.map_source hu
  have hleft : Φ.symm (Φ u) = u := Φ.left_inv hu
  -- Step 1: `Φ`, `Φ⁻¹` and `ψ` are differentiable at `u`, `Φ u` and `u` (`C¹` on open sets).
  have hΦd : DifferentiableAt ℝ Φ u :=
    (hΦ.differentiableOn one_ne_zero u hu).differentiableAt (Φ.open_source.mem_nhds hu)
  have hΦsd : DifferentiableAt ℝ Φ.symm (Φ u) :=
    (hΦs.differentiableOn one_ne_zero _ hw).differentiableAt (Φ.open_target.mem_nhds hw)
  have hψd : DifferentiableAt ℝ ψ u :=
    (hψ.differentiableOn one_ne_zero u hu).differentiableAt (Φ.open_source.mem_nhds hu)
  set T := fderiv ℝ Φ u
  set Λ := fderiv ℝ Φ.symm (Φ u)
  -- Step 2: `Λ ∘ T = id`, as `Φ⁻¹ ∘ Φ = id` near `u`.
  have hLT : Λ.comp T = ContinuousLinearMap.id ℝ _ := by
    have h1 : HasFDerivAt (Φ.symm ∘ Φ) (Λ.comp T) u := hΦsd.hasFDerivAt.comp u hΦd.hasFDerivAt
    have h2 : HasFDerivAt (Φ.symm ∘ Φ) (ContinuousLinearMap.id ℝ _) u := by
      apply (hasFDerivAt_id u).congr_of_eventuallyEq
      filter_upwards [Φ.open_source.mem_nhds hu] with x hx
      exact Φ.left_inv hx
    exact h1.unique h2
  -- Step 3: `T ∘ Λ = id`, as `Φ ∘ Φ⁻¹ = id` near `Φ u`.
  have hTL : T.comp Λ = ContinuousLinearMap.id ℝ _ := by
    have hΦd' : HasFDerivAt Φ T (Φ.symm (Φ u)) := by rw [hleft]; exact hΦd.hasFDerivAt
    have h1 : HasFDerivAt (Φ ∘ Φ.symm) (T.comp Λ) (Φ u) := hΦd'.comp (Φ u) hΦsd.hasFDerivAt
    have h2 : HasFDerivAt (Φ ∘ Φ.symm) (ContinuousLinearMap.id ℝ _) (Φ u) := by
      apply (hasFDerivAt_id (Φ u)).congr_of_eventuallyEq
      filter_upwards [Φ.open_target.mem_nhds hw] with x hx
      exact Φ.right_inv hx
    exact h1.unique h2
  -- Step 4: `T` is bijective.
  have hbij : Function.Bijective (T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k)) := by
    constructor
    · intro v v' h
      have h' : Λ (T v) = Λ (T v') := congrArg Λ h
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, hLT] at h'
      simpa using h'
    · intro p
      refine ⟨Λ p, ?_⟩
      show T (Λ p) = p
      rw [← ContinuousLinearMap.comp_apply, hTL]
      rfl
  -- Step 5: `G = fst ∘ Φ` near `u`, so `DG(u) = fst ∘ T`.
  have hG : fderiv ℝ G u = (WithLp.fstL 2 ℝ (Rn m) (Rn k)).comp T := by
    have heq : G =ᶠ[𝓝 u] (fun x ↦ (Φ x).fst) := by
      filter_upwards [Φ.open_source.mem_nhds hu] with x hx
      exact (hfst x hx).symm
    rw [heq.fderiv_eq]
    exact ((WithLp.fstL 2 ℝ (Rn m) (Rn k)).hasFDerivAt.comp u hΦd.hasFDerivAt).fderiv
  have hfstT : ∀ v, ((T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k)) v).fst =
      (fderiv ℝ G u : Rn (m + k) →ₗ[ℝ] Rn m) v := by
    intro v
    rw [hG]
    rfl
  -- Step 6: `E = Λ ∘ j` satisfies `T (E z) = (0, z)`.
  let E : Rn k →ₗ[ℝ] Rn (m + k) := ((Λ.comp j : Rn k →L[ℝ] Rn (m + k)) : Rn k →ₗ[ℝ] Rn (m + k))
  have hE : ∀ z, (T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k)) (E z) = WithLp.toLp 2 (0, z) := by
    intro z
    show T (Λ (j z)) = _
    rw [← ContinuousLinearMap.comp_apply, hTL]
    rfl
  -- Step 7: chain rule, `D(ψ ∘ Φ⁻¹)(Φ u) = Dψ(u) ∘ Λ`.
  have hchain : fderiv ℝ (ψ ∘ Φ.symm) (Φ u) = (fderiv ℝ ψ u).comp Λ := by
    have hψd' : DifferentiableAt ℝ ψ (Φ.symm (Φ u)) := by rw [hleft]; exact hψd
    rw [fderiv_comp (Φ u) hψd' hΦsd, hleft]
  -- Step 8: (FJ) with `A = Dψ(u)`, `Γ = DG(u)`, `T` and `E`.
  rw [hchain]
  exact hFJ (fderiv ℝ ψ u) (fderiv ℝ G u) T E hbij hfstT hE

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
