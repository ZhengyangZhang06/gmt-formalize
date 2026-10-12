import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.EMetricSpace.Lipschitz
import Poincare.SimonGMT.Chapter02.BV
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter03.SubmanifoldCover

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

/-- **Null sets have null slices**, Simon Ch. 3, p. 77 (the null parts in the proof of the
co-area formula (2.8)), from Eilenberg's inequality, Simon Ch. 2, Theorem 1.9, taken as the
hypothesis `(E)`. If `f` is locally Lipschitz on `U ⊇ Z` and `H^{m+k}(Z) = 0`, then
`Hᵏ(Z ∩ f⁻¹(y)) = 0` for `Lᵐ`-a.e. `y`. Each `x ∈ Z` has a neighbourhood `V_x` with `f`
Lipschitz on `V_x ∩ U`; countably many `V_x` cover `Z` (Lindelöf). On each piece `f` extends to a
globally Lipschitz `F_x` (`LipschitzOnWith.extend_finite_dimension`), which has the same slices on
`Z ∩ V_x ⊆ U`, and `(E)` gives a Borel majorant `g_x` of `y ↦ Hᵏ(Z ∩ V_x ∩ f⁻¹(y))` with
`∫ g_x ≤ C L_xᵐ H^{m+k}(Z ∩ V_x) = 0`, so `g_x = 0` a.e.; conclude by countable subadditivity. -/
theorem Submission.coarea_null_slices_of_eilenberg : (∀ (N m k : ℕ), ∃ C : ℝ≥0, ∀ (A : Set (Rn N)) (f : Rn N → Rn m) (L : ℝ≥0), LipschitzWith L f → ∃ g : Rn m → ℝ≥0∞, Measurable g ∧ (∀ y, μHE[k] (A ∩ f ⁻¹' {y}) ≤ g y) ∧ ∫⁻ y, g y ≤ ((C * L ^ m : ℝ≥0) : ℝ≥0∞) * μHE[m + k] A) → ∀ (N m k : ℕ) (U Z : Set (Rn N)) (f : Rn N → Rn m), LocallyLipschitzOn U f → Z ⊆ U → μHE[m + k] Z = 0 → ∀ᵐ y ∂(volume : Measure (Rn m)), μHE[k] (Z ∩ f ⁻¹' {y}) = 0 := by
  intro hE N m k U Z f hf hZU hZ
  obtain ⟨C, hC⟩ := hE N m k
  -- Every `x ∈ Z` has a neighbourhood `V x` such that `f` is Lipschitz on `V x ∩ U`.
  have hloc : ∀ x ∈ Z, ∃ V ∈ 𝓝 x, ∃ K : ℝ≥0, LipschitzOnWith K f (V ∩ U) := by
    intro x hx
    obtain ⟨K, t, ht, hft⟩ := hf (hZU hx)
    obtain ⟨V, hV, hVt⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 ht
    exact ⟨V, hV, K, hft.mono hVt⟩
  choose V hV K hK using hloc
  -- Lindelöf: countably many of these neighbourhoods cover `Z`.
  obtain ⟨T, hTc, hZT⟩ := (HereditarilyLindelofSpace.isLindelof Z).elim_nhds_subcover' V hV
  have : Countable T := hTc.to_subtype
  -- On each piece, extend `f` to a globally Lipschitz map and apply `(E)`.
  have hpiece : ∀ i : T, ∃ g : Rn m → ℝ≥0∞,
      (∀ y, μHE[k] (Z ∩ V i.1.1 i.1.2 ∩ f ⁻¹' {y}) ≤ g y) ∧ ∀ᵐ y ∂(volume : Measure (Rn m)), g y = 0 := by
    intro i
    obtain ⟨F, hFL, hfF⟩ := (hK i.1.1 i.1.2).extend_finite_dimension
    obtain ⟨g, hgm, hg, hgi⟩ := hC (Z ∩ V i.1.1 i.1.2) F _ hFL
    refine ⟨g, fun y => ?_, ?_⟩
    · -- `F = f` on `V ∩ U ⊇ Z ∩ V`, so the slices agree.
      have hslice : Z ∩ V i.1.1 i.1.2 ∩ f ⁻¹' {y} = Z ∩ V i.1.1 i.1.2 ∩ F ⁻¹' {y} := by
        ext z
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
        constructor
        · rintro ⟨⟨hz, hzV⟩, hfz⟩
          exact ⟨⟨hz, hzV⟩, (hfF ⟨hzV, hZU hz⟩).symm.trans hfz⟩
        · rintro ⟨⟨hz, hzV⟩, hFz⟩
          exact ⟨⟨hz, hzV⟩, (hfF ⟨hzV, hZU hz⟩).trans hFz⟩
      rw [hslice]
      exact hg y
    · -- `∫ g ≤ C Lᵐ H^{m+k}(Z ∩ V) = 0`, hence `g = 0` a.e.
      have h0 : μHE[m + k] (Z ∩ V i.1.1 i.1.2) = 0 := measure_mono_null inter_subset_left hZ
      rw [h0, mul_zero, nonpos_iff_eq_zero] at hgi
      exact (lintegral_eq_zero_iff hgm).1 hgi
  choose g hg hg0 using hpiece
  -- Countable subadditivity over the pieces.
  filter_upwards [ae_all_iff.2 hg0] with y hy
  refine measure_mono_null (t := ⋃ i : T, Z ∩ V i.1.1 i.1.2 ∩ f ⁻¹' {y}) ?_ ?_
  · rintro z ⟨hz, hfz⟩
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 (hZT hz)
    exact mem_iUnion.2 ⟨⟨i, hi⟩, ⟨hz, hzi⟩, hfz⟩
  · exact measure_iUnion_null fun i => nonpos_iff_eq_zero.1 ((hg i y).trans (hy i).le)

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

/-- **Area formula for a `C¹` map that is injective on an open parameter domain** (Simon Ch. 2,
(3.2) and its weighted form (3.5), cf. (4.13)). Let `V ⊆ ℝᵏ` be open and `χ : ℝᵏ → ℝᴺ` be `C¹`
and injective on `V`; no rank condition on `Dχ` is assumed. Then for every Borel `S ⊆ V` and
Borel `φ ≥ 0`, `∫_{χ(S)} φ dHᵏ = ∫_S φ(χ(z)) J(z) dLᵏ(z)` with `J(z) = normDet (Dχ(z))`.

The Lipschitz area formula of the pinned `simongmt` package (`Chapter02.AreaDomain`) is not in the
import closure of the contract, so the formula is derived here for `C¹` maps from Mathlib's
change of variables in equal dimension and the linear area formula:
* if `Dχ(z)` is injective, let `P` be the orthogonal projection onto its range, read in an
  orthonormal basis. On a small ball `P` is `1`-Lipschitz on `χ(A)` and has a `K`-Lipschitz
  inverse there, and the same holds for `Dχ(w)` in place of `χ`; with the change of variables
  for `P ∘ χ` this gives `∫_A J ≤ Kᵏ Hᵏ(χ(A))` and `Hᵏ(χ(A)) ≤ Kᵏ ∫_A J`;
* if `Dχ(z)` is not injective, compressing a unit kernel direction by `δ` shows
  `Hᵏ(χ(A)) ≤ (‖Dχ(z)‖ + 2)ᵏ δ Lᵏ(A)` on a small ball;
* Lindelöf, Lusin–Souslin (Borel images, `MeasurableSet.image_of_continuousOn_injOn`) and
  `K → 1`, `δ → 0` give `Hᵏ(χ(A)) = ∫_A J` for Borel `A ⊆ V`; the weighted formula follows by
  pushing `J Lᵏ ⌞ S` forward under `χ`. -/
theorem Submission.pcoarea_c1_injOn_area_formula : ∀ (k N : ℕ) (V : Set (Rn k))
    (χ : Rn k → Rn N), IsOpen V → ContDiffOn ℝ 1 χ V → InjOn χ V → ∀ S ⊆ V, MeasurableSet S →
    ∀ φ : Rn N → ℝ≥0∞, Measurable φ → ∫⁻ x in χ '' S, φ x ∂μHE[k] =
      ∫⁻ z in S, φ (χ z) * ENNReal.ofReal ((fderiv ℝ χ z).toLinearMap.normDet) := by
  intro k N V χ hV hχ hinj S hSV hS φ hφ
  /- Step 1: measure-theoretic tools. `Hᵏ = Lᵏ` on `ℝᵏ`; the linear area formula; images under
  a map with a `K`-Lipschitz inverse; continuity of `normDet`. -/
  have hvolE : (μHE[k] : Measure (Rn k)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume k
  have hlinarea : ∀ (L : Rn k →L[ℝ] Rn N) (s : Set (Rn k)),
      μHE[k] (L '' s) = ENNReal.ofReal L.toLinearMap.normDet * volume s := by
    intro L s
    have h := LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume
      (L : Rn k →ₗ[ℝ] Rn N) s
    rwa [finrank_euclideanSpace_fin] at h
  have hlipInv : ∀ (s : Set (Rn k)) (g : Rn k → Rn k) (f : Rn k → Rn N) (K : ℝ≥0),
      (∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ K * ‖g x - g y‖) →
        μHE[k] (f '' s) ≤ (K : ℝ≥0∞) ^ k * volume (g '' s) := by
    intro s g f K hKf
    have hfeq : ∀ x ∈ s, f (Function.invFunOn g s (g x)) = f x := by
      intro x hx
      have hmem := Function.invFunOn_mem (f := g) (b := g x) ⟨x, hx, rfl⟩
      have heq := Function.invFunOn_eq (f := g) (b := g x) ⟨x, hx, rfl⟩
      have h := hKf _ hmem x hx
      rw [heq, sub_self, norm_zero, mul_zero] at h
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
    have himage : f '' s = (f ∘ Function.invFunOn g s) '' (g '' s) := by
      rw [← Set.image_comp]
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, hfeq x hx⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, (hfeq x hx).symm⟩
    have hLip : LipschitzOnWith K (f ∘ Function.invFunOn g s) (g '' s) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [Function.comp_apply, dist_eq_norm, hfeq x hx, hfeq y hy]
      exact hKf x hx y hy
    rw [himage, ← hvolE]
    exact Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k hLip
  have hndcont : Continuous (fun L : Rn k →L[ℝ] Rn N ↦ L.toLinearMap.normDet) := by
    have h1 : Continuous (fun L : Rn k →L[ℝ] Rn N ↦ ContinuousLinearMap.adjoint L ∘L L) :=
      ContinuousLinearMap.adjoint.continuous.clm_comp continuous_id
    have h2 : Continuous (fun L : Rn k →L[ℝ] Rn N ↦
        Real.sqrt (ContinuousLinearMap.adjoint L ∘L L).det) :=
      Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp h1)
    refine h2.congr fun L ↦ ?_
    rw [← ContinuousLinearMap.normDet_sq L]
    exact Real.sqrt_sq (LinearMap.normDet_nonneg _)
  -- Step 2: `χ` is strictly differentiable on `V`, `Dχ` is continuous there, and images of Borel
  -- subsets of `V` are Borel and disjoint for disjoint sets (Lusin–Souslin, injectivity).
  have hdiff : ∀ z ∈ V, HasFDerivAt χ (fderiv ℝ χ z) z := fun z hz =>
    (((hχ.differentiableOn one_ne_zero) z hz).differentiableAt (hV.mem_nhds hz)).hasFDerivAt
  have hstrict : ∀ z ∈ V, HasStrictFDerivAt χ (fderiv ℝ χ z) z := fun z hz =>
    (hχ.contDiffAt (hV.mem_nhds hz)).hasStrictFDerivAt one_ne_zero
  have hfcont : ContinuousOn (fderiv ℝ χ) V := hχ.continuousOn_fderiv_of_isOpen hV le_rfl
  have hχcont : ContinuousOn χ V := hχ.continuousOn
  have hJcont : ContinuousOn (fun z ↦ (fderiv ℝ χ z).toLinearMap.normDet) V :=
    hndcont.comp_continuousOn hfcont
  have himg : ∀ A ⊆ V, MeasurableSet A → MeasurableSet (χ '' A) := fun A hAV hA =>
    hA.image_of_continuousOn_injOn (hχcont.mono hAV) (hinj.mono hAV)
  have hdisjimg : ∀ A B : Set (Rn k), A ⊆ V → B ⊆ V → Disjoint A B →
      Disjoint (χ '' A) (χ '' B) := by
    intro A B hAV hBV hAB
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hba : b = a := hinj (hBV hb) (hAV ha) hab
    exact Set.disjoint_left.mp hAB ha (hba ▸ hb)
  /- Step 3 (regular points): if `Dχ(z)` is injective and `K > 1`, then on a small ball
  `∫_A J ≤ Kᵏ Hᵏ(χ(A))` and `Hᵏ(χ(A)) ≤ Kᵏ ∫_A J`. -/
  have hreg : ∀ z ∈ V, (fderiv ℝ χ z).toLinearMap.normDet ≠ 0 → ∀ K : ℝ≥0, 1 < K →
      ∃ r > 0, Metric.ball z r ⊆ V ∧ ∀ A ⊆ Metric.ball z r, MeasurableSet A →
        μHE[k] (χ '' A) ≤ (K : ℝ≥0∞) ^ k *
            ∫⁻ w in A, ENNReal.ofReal (fderiv ℝ χ w).toLinearMap.normDet ∧
          ∫⁻ w in A, ENNReal.ofReal (fderiv ℝ χ w).toLinearMap.normDet ≤
            (K : ℝ≥0∞) ^ k * μHE[k] (χ '' A) := by
    intro z hz hJz K hK
    set T : Rn k →L[ℝ] Rn N := fderiv ℝ χ z with hTdef
    -- `T` is injective, with a lower bound `‖v‖ ≤ c₀ ‖T v‖`
    have hker : LinearMap.ker T.toLinearMap = ⊥ := by
      by_contra h
      exact hJz (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr h)
    have hTinj : Function.Injective T := LinearMap.ker_eq_bot.mp hker
    obtain ⟨c₀, hc₀, hanti⟩ := T.toLinearMap.exists_antilipschitzWith hker
    have hlow : ∀ v, ‖v‖ ≤ c₀ * ‖T v‖ := by
      intro v
      simpa [dist_eq_norm] using hanti.le_mul_dist v 0
    -- `P`: the orthogonal projection onto `range T`, read in an orthonormal basis of the range
    set R := LinearMap.range T.toLinearMap with hRdef
    have hRrank : finrank ℝ R = k := by
      rw [LinearMap.finrank_range_of_inj hTinj, finrank_euclideanSpace_fin]
    let b : OrthonormalBasis (Fin k) ℝ R := (stdOrthonormalBasis ℝ R).reindex (finCongr hRrank)
    let P : Rn N →L[ℝ] Rn k :=
      (b.repr.toContinuousLinearEquiv : R →L[ℝ] Rn k) ∘L R.orthogonalProjectionOnto
    have hP1 : ∀ y, ‖P y‖ ≤ ‖y‖ := by
      intro y
      have h1 : ‖P y‖ = ‖R.orthogonalProjectionOnto y‖ := by
        simp only [P, ContinuousLinearMap.comp_apply]
        exact b.repr.norm_map _
      rw [h1]
      exact (R.orthogonalProjectionOnto.le_opNorm y).trans
        (mul_le_of_le_one_left (norm_nonneg y) R.orthogonalProjectionOnto_norm_le)
    have hPT : ∀ v, ‖P (T v)‖ = ‖T v‖ := by
      intro v
      have hmem : T v ∈ R := LinearMap.mem_range_self T.toLinearMap v
      have h1 : R.orthogonalProjectionOnto (T v) = ⟨T v, hmem⟩ :=
        R.orthogonalProjectionOnto_mem_subspace_eq_self ⟨T v, hmem⟩
      simp only [P, ContinuousLinearMap.comp_apply, h1]
      exact b.repr.norm_map _
    -- the approximation constant `δ`, with `θ = c₀ δ ≤ min (1/4) ((K - 1)/4)`
    have hK1 : (1 : ℝ) < K := by exact_mod_cast hK
    have hc₀pos : (0 : ℝ) < c₀ := by exact_mod_cast hc₀
    obtain ⟨θ, hθpos, hθ14, hθK⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 4 ∧ θ ≤ ((K : ℝ) - 1) / 4 :=
      ⟨min (1 / 4) (((K : ℝ) - 1) / 4), lt_min (by norm_num) (by linarith), min_le_left _ _,
        min_le_right _ _⟩
    obtain ⟨δ, hδpos, hc₀δ⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ (c₀ : ℝ) * δ = θ :=
      ⟨⟨θ / c₀, (div_pos hθpos hc₀pos).le⟩, div_pos hθpos hc₀pos, mul_div_cancel₀ θ hc₀pos.ne'⟩
    have hδ0 : (0 : ℝ) ≤ δ := δ.2
    -- core estimate for any map `f` approximating `T` with constant `δ` on `s`:
    -- `P ∘ f` is injective on `s`, `P` is `1`-Lipschitz, and `f = h ∘ P ∘ f` with `h` `K`-Lipschitz
    have core : ∀ (f : Rn k → Rn N) (s : Set (Rn k)), ApproximatesLinearOn f T s δ →
        InjOn (P ∘ f) s ∧ volume ((P ∘ f) '' s) ≤ μHE[k] (f '' s) ∧
          μHE[k] (f '' s) ≤ (K : ℝ≥0∞) ^ k * volume ((P ∘ f) '' s) := by
      intro f s hf
      have key : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ K * ‖P (f x) - P (f y)‖ ∧
          3 * ‖x - y‖ ≤ 4 * c₀ * ‖P (f x) - P (f y)‖ := by
        intro x hx y hy
        have he : ‖f x - f y - T (x - y)‖ ≤ δ * ‖x - y‖ := hf x hx y hy
        have hPe : ‖P (f x - f y - T (x - y))‖ ≤ δ * ‖x - y‖ := (hP1 _).trans he
        have ht : ‖T (x - y)‖ ≤ ‖P (f x) - P (f y)‖ + δ * ‖x - y‖ := by
          have h : P (T (x - y)) = (P (f x) - P (f y)) - P (f x - f y - T (x - y)) := by
            rw [map_sub P (f x - f y), map_sub P (f x)]; abel
          rw [← hPT, h]
          exact (norm_sub_le _ _).trans (by linarith)
        have hq : ‖f x - f y‖ ≤ ‖T (x - y)‖ + δ * ‖x - y‖ := by
          have h : f x - f y = T (x - y) + (f x - f y - T (x - y)) := by abel
          calc ‖f x - f y‖ = ‖T (x - y) + (f x - f y - T (x - y))‖ := congrArg _ h
            _ ≤ ‖T (x - y)‖ + ‖f x - f y - T (x - y)‖ := norm_add_le _ _
            _ ≤ ‖T (x - y)‖ + δ * ‖x - y‖ := by linarith
        have ha : ‖x - y‖ ≤ c₀ * ‖T (x - y)‖ := hlow (x - y)
        have hp0 : 0 ≤ ‖P (f x) - P (f y)‖ := norm_nonneg _
        have ha0 : 0 ≤ ‖x - y‖ := norm_nonneg _
        have h1 := mul_le_mul_of_nonneg_left ht hc₀pos.le
        have h1' : (c₀ : ℝ) * (δ * ‖x - y‖) = θ * ‖x - y‖ := by rw [← mul_assoc, hc₀δ]
        have hθa := mul_le_mul_of_nonneg_right hθ14 ha0
        have h2 : 3 * ‖x - y‖ ≤ 4 * c₀ * ‖P (f x) - P (f y)‖ := by
          rw [mul_add, h1'] at h1
          linarith
        refine ⟨?_, h2⟩
        have h3 := mul_le_mul_of_nonneg_left h2 hδ0
        have h3' : (δ : ℝ) * (4 * c₀ * ‖P (f x) - P (f y)‖) = 4 * θ * ‖P (f x) - P (f y)‖ := by
          rw [← hc₀δ]; ring
        have hθp := mul_le_mul_of_nonneg_right hθK hp0
        have hKp : 0 ≤ ((K : ℝ) - 1) * ‖P (f x) - P (f y)‖ := mul_nonneg (by linarith) hp0
        rw [h3'] at h3
        linarith
      refine ⟨?_, ?_, ?_⟩
      · intro x hx y hy hxy
        have h := (key x hx y hy).2
        have hxy' : P (f x) - P (f y) = 0 := sub_eq_zero.mpr hxy
        rw [hxy', norm_zero, mul_zero] at h
        have h0 : ‖x - y‖ = 0 := le_antisymm (by linarith) (norm_nonneg _)
        exact sub_eq_zero.mp (norm_eq_zero.mp h0)
      · rw [Set.image_comp, ← hvolE]
        have hLipP : LipschitzOnWith 1 P (f '' s) := by
          apply LipschitzOnWith.of_dist_le_mul
          intro y₁ _ y₂ _
          rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
          exact hP1 _
        simpa using
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k hLipP
      · exact hlipInv s (P ∘ f) f K (fun x hx y hy => (key x hx y hy).1)
    -- choose the radius: `χ` approximates `T` and `‖Dχ - T‖ < δ` on the ball, which lies in `V`
    obtain ⟨s₀, hs₀, happrox⟩ :=
      (hstrict z hz).approximates_deriv_on_nhds (c := δ) (Or.inr hδpos)
    have hcontz : ContinuousAt (fderiv ℝ χ) z := hfcont.continuousAt (hV.mem_nhds hz)
    have hev : ∀ᶠ w in 𝓝 z, ‖fderiv ℝ χ w - T‖ < δ := by
      have := hcontz.eventually (Metric.ball_mem_nhds T (show (0 : ℝ) < δ from hδpos))
      filter_upwards [this] with w hw
      rwa [dist_eq_norm] at hw
    obtain ⟨r, hr, hball⟩ :=
      Metric.mem_nhds_iff.mp (inter_mem (inter_mem hs₀ (hV.mem_nhds hz)) hev)
    refine ⟨r, hr, fun w hw => (hball hw).1.2, ?_⟩
    intro A hAr hA
    have hAV : A ⊆ V := fun w hw => (hball (hAr hw)).1.2
    obtain ⟨hinjA, hlowA, hupA⟩ :=
      core χ A (happrox.mono_set fun w hw => (hball (hAr hw)).1.1)
    -- change of variables for `P ∘ χ` (Mathlib, equal dimension)
    have hcov : ∫⁻ w in A, ENNReal.ofReal |(P ∘L fderiv ℝ χ w).det| =
        volume ((P ∘ χ) '' A) :=
      lintegral_abs_det_fderiv_eq_addHaar_image volume hA
        (fun w hw => (P.hasFDerivAt.comp w (hdiff w (hAV hw))).hasFDerivWithinAt) hinjA
    -- pointwise comparison of `|det (P ∘ Dχ(w))|` with `J(w)`, from `core` for `Dχ(w)`
    have hlin : ∀ w ∈ Metric.ball z r,
        ENNReal.ofReal |(P ∘L fderiv ℝ χ w).det| ≤
            ENNReal.ofReal (fderiv ℝ χ w).toLinearMap.normDet ∧
          ENNReal.ofReal (fderiv ℝ χ w).toLinearMap.normDet ≤
            (K : ℝ≥0∞) ^ k * ENNReal.ofReal |(P ∘L fderiv ℝ χ w).det| := by
      intro w hw
      set L := fderiv ℝ χ w
      have hLT : ‖L - T‖ < δ := (hball hw).2
      have happL : ApproximatesLinearOn (L : Rn k → Rn N) T univ δ := by
        intro x _ y _
        have h : L x - L y - T (x - y) = (L - T) (x - y) := by
          simp only [sub_apply, map_sub]; abel
        rw [h]
        exact ((L - T).le_opNorm _).trans (mul_le_mul_of_nonneg_right hLT.le (norm_nonneg _))
      obtain ⟨-, hlow', hup'⟩ := core L (Metric.ball 0 1) (happL.mono_set (subset_univ _))
      have h1 : volume ((P ∘ L) '' Metric.ball 0 1) =
          ENNReal.ofReal |(P ∘L L).det| * volume (Metric.ball (0 : Rn k) 1) :=
        Measure.addHaar_image_continuousLinearMap volume (P ∘L L) _
      rw [h1, hlinarea L (Metric.ball 0 1)] at hlow' hup'
      have hB0 : volume (Metric.ball (0 : Rn k) 1) ≠ 0 :=
        (Metric.measure_ball_pos volume (0 : Rn k) one_pos).ne'
      have hBtop : volume (Metric.ball (0 : Rn k) 1) ≠ ⊤ := measure_ball_lt_top.ne
      constructor
      · exact (ENNReal.mul_le_mul_iff_left hB0 hBtop).mp hlow'
      · rw [← mul_assoc] at hup'
        exact (ENNReal.mul_le_mul_iff_left hB0 hBtop).mp hup'
    constructor
    · calc μHE[k] (χ '' A) ≤ (K : ℝ≥0∞) ^ k * volume ((P ∘ χ) '' A) := hupA
        _ = (K : ℝ≥0∞) ^ k * ∫⁻ w in A, ENNReal.ofReal |(P ∘L fderiv ℝ χ w).det| := by
            rw [hcov]
        _ ≤ (K : ℝ≥0∞) ^ k *
              ∫⁻ w in A, ENNReal.ofReal (fderiv ℝ χ w).toLinearMap.normDet :=
            mul_le_mul_right (setLIntegral_mono' hA fun w hw => (hlin w (hAr hw)).1) _
    · calc ∫⁻ w in A, ENNReal.ofReal (fderiv ℝ χ w).toLinearMap.normDet
          ≤ ∫⁻ w in A, (K : ℝ≥0∞) ^ k * ENNReal.ofReal |(P ∘L fderiv ℝ χ w).det| :=
            setLIntegral_mono' hA fun w hw => (hlin w (hAr hw)).2
        _ = (K : ℝ≥0∞) ^ k * ∫⁻ w in A, ENNReal.ofReal |(P ∘L fderiv ℝ χ w).det| :=
            lintegral_const_mul' _ _ (by simp)
        _ = (K : ℝ≥0∞) ^ k * volume ((P ∘ χ) '' A) := by rw [hcov]
        _ ≤ (K : ℝ≥0∞) ^ k * μHE[k] (χ '' A) := mul_le_mul_right hlowA _
  /- Step 4 (critical points): if `Dχ(z)` is not injective and `ε > 0`, then on a small ball
  `Hᵏ(χ(A)) ≤ ε Lᵏ(A)`. -/
  have hcrit : ∀ z ∈ V, (fderiv ℝ χ z).toLinearMap.normDet = 0 → ∀ ε : ℝ≥0, 0 < ε →
      ∃ r > 0, Metric.ball z r ⊆ V ∧ ∀ A ⊆ Metric.ball z r,
        μHE[k] (χ '' A) ≤ ε * volume A := by
    intro z hz hJz ε hε
    set T : Rn k →L[ℝ] Rn N := fderiv ℝ χ z with hTdef
    -- a unit vector `u` in the kernel of `T`
    have hker : LinearMap.ker T.toLinearMap ≠ ⊥ :=
      LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp hJz
    obtain ⟨u₀, hu₀mem, hu₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    set u : Rn k := (‖u₀‖⁻¹ : ℝ) • u₀ with hudef
    have hu1 : ‖u‖ = 1 := norm_smul_inv_norm hu₀ne
    have hTu : T u = 0 := by
      have h0 : T u₀ = 0 := hu₀mem
      rw [hudef, map_smul, h0, smul_zero]
    have huu : inner ℝ u u = (1 : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hu1]; norm_num
    -- constants: `M = ‖T‖ + 2` and `δ ≤ 1` with `Mᵏ δ ≤ ε`
    set M : ℝ≥0 := ‖T‖₊ + 2 with hM
    have hMpos : 0 < M := by positivity
    set δ : ℝ≥0 := min 1 (ε / M ^ k) with hδ
    have hδpos : 0 < δ := lt_min one_pos (div_pos hε (pow_pos hMpos k))
    have hδ1 : (δ : ℝ) ≤ 1 := by exact_mod_cast min_le_left _ _
    have hMδ : M ^ k * δ ≤ ε := by
      calc M ^ k * δ ≤ M ^ k * (ε / M ^ k) := mul_le_mul_right (min_le_right _ _) _
        _ = ε := mul_div_cancel₀ _ (pow_pos hMpos k).ne'
    -- the compression `S x = x + (δ - 1) ⟪u, x⟫ u`
    let S : Rn k →L[ℝ] Rn k :=
      ContinuousLinearMap.id ℝ (Rn k) + ((δ : ℝ) - 1) • (innerSL ℝ u).smulRight u
    have hS : ∀ x, S x = x + (((δ : ℝ) - 1) * inner ℝ u x) • u := by
      intro x
      simp only [S, add_apply, ContinuousLinearMap.id_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
    have hSnorm : ∀ x, ‖x - (inner ℝ u x) • u‖ ≤ ‖S x‖ ∧ (δ : ℝ) * |inner ℝ u x| ≤ ‖S x‖ := by
      intro x
      set a := inner ℝ u x with ha
      have horth : inner ℝ (x - a • u) (((δ : ℝ) * a) • u) = 0 := by
        rw [inner_smul_right, inner_sub_left, inner_smul_left, huu, real_inner_comm, ← ha]
        simp
      have hSx : S x = (x - a • u) + ((δ : ℝ) * a) • u := by
        rw [hS, ← ha, sub_mul, one_mul, sub_smul]
        abel
      have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
      rw [← hSx] at hpy
      have hnu : ‖((δ : ℝ) * a) • u‖ = (δ : ℝ) * |a| := by
        rw [norm_smul, hu1, mul_one, Real.norm_eq_abs, abs_mul, NNReal.abs_eq]
      rw [hnu] at hpy
      have h0 : 0 ≤ (δ : ℝ) * |a| := mul_nonneg δ.2 (abs_nonneg a)
      constructor
      · refine (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).mpr ?_
        rw [hpy]
        exact le_add_of_nonneg_right (mul_self_nonneg _)
      · refine (mul_self_le_mul_self_iff h0 (norm_nonneg _)).mpr ?_
        rw [hpy]
        exact le_add_of_nonneg_left (mul_self_nonneg _)
    -- `det S = δ`, computed in an orthonormal basis containing `u`
    have hdetS : LinearMap.det (S : Rn k →ₗ[ℝ] Rn k) = δ := by
      have hk : k ≠ 0 := by
        rintro rfl
        exact hu₀ne (Subsingleton.elim _ _)
      set i₀ : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
      obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
        (E := Rn k) (ι := Fin k) (by simp) (v := fun _ => u) (s := {i₀}) (by
          rw [orthonormal_iff_ite]
          rintro ⟨i, hi⟩ ⟨j, hj⟩
          simp only [Set.mem_singleton_iff] at hi hj
          subst hi hj
          simp [hu1])
      have hbi₀ : b i₀ = u := hb i₀ rfl
      rw [← LinearMap.det_toMatrix b.toBasis]
      have hmat : LinearMap.toMatrix b.toBasis b.toBasis (S : Rn k →ₗ[ℝ] Rn k) =
          Matrix.diagonal (fun i => if i = i₀ then (δ : ℝ) else 1) := by
        ext i j
        rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis,
          ContinuousLinearMap.coe_coe, hS, inner_add_right, inner_smul_right, ← hbi₀,
          b.inner_eq_ite, b.inner_eq_ite, b.inner_eq_ite, Matrix.diagonal_apply]
        by_cases hij : i = j
        · subst hij
          by_cases hi : i = i₀
          · subst hi; simp
          · simp [hi, Ne.symm hi]
        · by_cases hj : i₀ = j
          · subst hj; simp [hij]
          · simp [hij, hj]
      rw [hmat, Matrix.det_diagonal, Finset.prod_ite_eq' Finset.univ i₀ (fun _ => (δ : ℝ))]
      simp
    -- choose the radius: `χ` approximates `T` with constant `δ` on the ball
    obtain ⟨s₀, hs₀, happrox⟩ :=
      (hstrict z hz).approximates_deriv_on_nhds (c := δ) (Or.inr hδpos)
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hs₀ (hV.mem_nhds hz))
    refine ⟨r, hr, fun w hw => (hball hw).2, ?_⟩
    intro A hAr
    have happA : ApproximatesLinearOn χ T A δ := happrox.mono_set fun w hw => (hball (hAr hw)).1
    -- `‖χ x - χ y‖ ≤ M ‖S x - S y‖` on `A`, since `T` kills the compressed direction
    have hkey : ∀ x ∈ A, ∀ y ∈ A, ‖χ x - χ y‖ ≤ M * ‖S x - S y‖ := by
      intro x hx y hy
      set Δ := x - y with hΔ
      set a := inner ℝ u Δ with ha
      have he : ‖χ x - χ y - T Δ‖ ≤ δ * ‖Δ‖ := happA x hx y hy
      have hTΔ : T Δ = T (Δ - a • u) := by
        rw [T.map_sub Δ (a • u), T.map_smul, hTu, smul_zero, sub_zero]
      have hTb : ‖T (Δ - a • u)‖ ≤ ‖T‖ * ‖Δ - a • u‖ := T.le_opNorm _
      have hΔle : ‖Δ‖ ≤ ‖Δ - a • u‖ + |a| := by
        calc ‖Δ‖ = ‖(Δ - a • u) + a • u‖ := by rw [sub_add_cancel]
          _ ≤ ‖Δ - a • u‖ + ‖a • u‖ := norm_add_le _ _
          _ = ‖Δ - a • u‖ + |a| := by rw [norm_smul, hu1, mul_one, Real.norm_eq_abs]
      obtain ⟨h1, h2⟩ := hSnorm Δ
      rw [← ha, hΔ, map_sub] at h1 h2
      have hq : ‖χ x - χ y‖ ≤ ‖T Δ‖ + δ * ‖Δ‖ := by
        calc ‖χ x - χ y‖ = ‖T Δ + (χ x - χ y - T Δ)‖ := by rw [add_sub_cancel]
          _ ≤ ‖T Δ‖ + ‖χ x - χ y - T Δ‖ := norm_add_le _ _
          _ ≤ ‖T Δ‖ + δ * ‖Δ‖ := by linarith
      have hM' : (M : ℝ) = ‖T‖ + 2 := by simp [M]
      rw [hTΔ] at hq
      rw [hM']
      have hδ0 : (0 : ℝ) ≤ δ := δ.2
      have h3 := mul_le_mul_of_nonneg_left hΔle hδ0
      have h4 := mul_le_mul_of_nonneg_right hδ1 (norm_nonneg (Δ - a • u))
      have h5 := mul_le_mul_of_nonneg_left h1 (norm_nonneg T)
      linarith
    calc μHE[k] (χ '' A) ≤ (M : ℝ≥0∞) ^ k * volume (S '' A) := hlipInv A S χ M hkey
      _ = (M : ℝ≥0∞) ^ k * ((δ : ℝ≥0∞) * volume A) := by
          rw [Measure.addHaar_image_continuousLinearMap, hdetS, NNReal.abs_eq,
            ENNReal.ofReal_coe_nnreal]
      _ = ((M ^ k * δ : ℝ≥0) : ℝ≥0∞) * volume A := by push_cast; ring
      _ ≤ ε * volume A := mul_le_mul_left (by exact_mod_cast hMδ) _
  /- Step 5: localization (Lindelöf). A property of Borel sets that is stable under countable
  disjoint unions and holds for Borel subsets of small balls around each point of `W` holds for
  all Borel subsets of `W`. -/
  have hloc : ∀ (W : Set (Rn k)) (Pr : Set (Rn k) → Prop), Pr ∅ →
      (∀ A : ℕ → Set (Rn k), (∀ i, MeasurableSet (A i)) →
        Pairwise (Function.onFun Disjoint A) → (∀ i, Pr (A i)) → Pr (⋃ i, A i)) →
      (∀ z ∈ W, ∃ r > 0, ∀ A, MeasurableSet A → A ⊆ Metric.ball z r → Pr A) →
      ∀ A, MeasurableSet A → A ⊆ W → Pr A := by
    intro W Pr h0 hU hlocal A hA hAW
    choose! r hr hPr using hlocal
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun z : W => Metric.ball (z : Rn k) (r z)) (fun _ => Metric.isOpen_ball)
    have hcov : A ⊆ ⋃ i ∈ T, Metric.ball (i : Rn k) (r i) := by
      rw [hT]
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hAW hx⟩, Metric.mem_ball_self (hr x (hAW hx))⟩
    rcases T.eq_empty_or_nonempty with hTe | hTne
    · have hAe : A = ∅ := by
        rw [hTe] at hcov
        simpa using hcov
      rw [hAe]
      exact h0
    obtain ⟨e, he⟩ := hTc.exists_eq_range hTne
    set B : ℕ → Set (Rn k) := fun n => A ∩ Metric.ball (e n : Rn k) (r (e n)) with hB
    have hBmeas : ∀ n, MeasurableSet (B n) := fun n => hA.inter measurableSet_ball
    have hAeq : A = ⋃ n, disjointed B n := by
      rw [iUnion_disjointed]
      apply Subset.antisymm
      · intro x hx
        have hx' := hcov hx
        rw [he] at hx'
        simp only [mem_iUnion, mem_range, exists_prop] at hx'
        obtain ⟨i, ⟨n, rfl⟩, hxi⟩ := hx'
        exact mem_iUnion.mpr ⟨n, hx, hxi⟩
      · exact iUnion_subset fun n => inter_subset_left
    rw [hAeq]
    apply hU
    · exact MeasurableSet.disjointed hBmeas
    · exact disjoint_disjointed B
    · intro n
      exact hPr _ (e n).2 _ (MeasurableSet.disjointed hBmeas n)
        ((disjointed_subset B n).trans inter_subset_right)
  -- Step 6: two limit arguments in `[0, ∞]`
  have hlim : ∀ a b : ℝ≥0∞, (∀ K : ℝ≥0, 1 < K → a ≤ (K : ℝ≥0∞) ^ k * b) → a ≤ b := by
    intro a b h
    by_cases hb : b = ⊤
    · rw [hb]; exact le_top
    have h1 : Tendsto (fun K : ℝ≥0 => (K : ℝ≥0∞) ^ k) (𝓝 1) (𝓝 1) := by
      have hc : Continuous (fun K : ℝ≥0 => (K : ℝ≥0∞) ^ k) :=
        (ENNReal.continuous_pow k).comp ENNReal.continuous_coe
      simpa using hc.tendsto 1
    have ht : Tendsto (fun K : ℝ≥0 => (K : ℝ≥0∞) ^ k * b) (𝓝[>] 1) (𝓝 b) := by
      simpa using (ENNReal.Tendsto.mul_const h1 (Or.inr hb)).mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun K hK => h K hK)
  have hzero : ∀ a c : ℝ≥0∞, c ≠ ⊤ → (∀ ε : ℝ≥0, 0 < ε → a ≤ ε * c) → a = 0 := by
    intro a c hc h
    have h1 : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞)) (𝓝 0) (𝓝 0) := by
      simpa using ENNReal.continuous_coe.tendsto 0
    have ht : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * c) (𝓝[>] 0) (𝓝 0) := by
      simpa using (ENNReal.Tendsto.mul_const h1 (Or.inr hc)).mono_left nhdsWithin_le_nhds
    exact le_antisymm (ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => h ε hε))
      zero_le
  -- Step 7: the regular set `G = {J ≠ 0}` (open) and the critical set `Z = V \ G`
  set G : Set (Rn k) := V ∩ (fun z ↦ (fderiv ℝ χ z).toLinearMap.normDet) ⁻¹' {0}ᶜ with hG
  have hGopen : IsOpen G := hJcont.isOpen_inter_preimage hV isOpen_compl_singleton
  set Z : Set (Rn k) := V \ G with hZ
  -- on Borel subsets of `G`: `Hᵏ(χ(A)) = ∫_A J`
  have hregG : ∀ A, MeasurableSet A → A ⊆ G →
      μHE[k] (χ '' A) = ∫⁻ z in A, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet := by
    intro A hA hAG
    have hbounds : ∀ K : ℝ≥0, 1 < K →
        μHE[k] (χ '' A) ≤ (K : ℝ≥0∞) ^ k *
            ∫⁻ z in A, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet ∧
          ∫⁻ z in A, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet ≤
            (K : ℝ≥0∞) ^ k * μHE[k] (χ '' A) := by
      intro K hK
      refine hloc G (fun A => A ⊆ V → (μHE[k] (χ '' A) ≤ (K : ℝ≥0∞) ^ k *
            ∫⁻ z in A, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet ∧
          ∫⁻ z in A, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet ≤
            (K : ℝ≥0∞) ^ k * μHE[k] (χ '' A))) ?_ ?_ ?_ A hA hAG (hAG.trans inter_subset_left)
      · intro _
        simp
      · intro As hAs hdisj hPr hUV
        have hAsV : ∀ i, As i ⊆ V := fun i => (subset_iUnion As i).trans hUV
        have h1 : μHE[k] (χ '' ⋃ i, As i) = ∑' i, μHE[k] (χ '' As i) := by
          rw [image_iUnion]
          exact measure_iUnion (fun i j hij => hdisjimg _ _ (hAsV i) (hAsV j) (hdisj hij))
            (fun i => himg _ (hAsV i) (hAs i))
        have h2 : ∫⁻ z in ⋃ i, As i, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet =
            ∑' i, ∫⁻ z in As i, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet :=
          lintegral_iUnion hAs hdisj _
        rw [h1, h2, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        exact ⟨ENNReal.tsum_le_tsum fun i => ((hPr i) (hAsV i)).1,
          ENNReal.tsum_le_tsum fun i => ((hPr i) (hAsV i)).2⟩
      · intro z hz
        obtain ⟨r, hr, -, hb⟩ := hreg z hz.1 hz.2 K hK
        exact ⟨r, hr, fun A hA hAr _ => hb A hAr hA⟩
    exact le_antisymm (hlim _ _ fun K hK => (hbounds K hK).1)
      (hlim _ _ fun K hK => (hbounds K hK).2)
  -- on Borel subsets of `Z`: `Hᵏ(χ(A)) = 0`
  have hcritZ : ∀ A, MeasurableSet A → A ⊆ Z → μHE[k] (χ '' A) = 0 := by
    intro A hA hAZ
    have hball : ∀ n : ℕ, μHE[k] (χ '' (A ∩ Metric.ball 0 n)) = 0 := by
      intro n
      apply hzero _ (volume (Metric.ball (0 : Rn k) n)) measure_ball_lt_top.ne
      intro ε hε
      have hle := hloc Z (fun A => μHE[k] (χ '' A) ≤ ε * volume A) (by simp) ?_ ?_
        (A ∩ Metric.ball 0 n) (hA.inter measurableSet_ball) (inter_subset_left.trans hAZ)
      · exact hle.trans (mul_le_mul_right (measure_mono inter_subset_right) _)
      · intro As hAs hdisj hPr
        calc μHE[k] (χ '' ⋃ i, As i) = μHE[k] (⋃ i, χ '' As i) := by rw [image_iUnion]
          _ ≤ ∑' i, μHE[k] (χ '' As i) := measure_iUnion_le _
          _ ≤ ∑' i, ε * volume (As i) := ENNReal.tsum_le_tsum hPr
          _ = ε * volume (⋃ i, As i) := by rw [ENNReal.tsum_mul_left, measure_iUnion hdisj hAs]
      · intro z hz
        have hJz : (fderiv ℝ χ z).toLinearMap.normDet = 0 := by
          by_contra h
          exact hz.2 ⟨hz.1, h⟩
        obtain ⟨r, hr, -, hb⟩ := hcrit z hz.1 hJz ε hε
        exact ⟨r, hr, fun A _ hAr => hb A hAr⟩
    have hAU : χ '' A = ⋃ n : ℕ, χ '' (A ∩ Metric.ball 0 n) := by
      rw [← image_iUnion, ← inter_iUnion, Metric.iUnion_ball_nat, inter_univ]
    rw [hAU]
    exact measure_iUnion_null hball
  -- Step 8: the area formula `Hᵏ(χ(A)) = ∫_A J` for Borel `A ⊆ V`
  have hmain : ∀ A ⊆ V, MeasurableSet A →
      μHE[k] (χ '' A) = ∫⁻ z in A, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet := by
    intro A hAV hA
    have hAG : MeasurableSet (A ∩ G) := hA.inter hGopen.measurableSet
    have hAZ : MeasurableSet (A ∩ Z) := hA.inter (hV.measurableSet.diff hGopen.measurableSet)
    have hAsplit : A = (A ∩ G) ∪ (A ∩ Z) := by
      rw [← inter_union_distrib_left, hZ, union_sdiff_cancel inter_subset_left,
        inter_eq_left.mpr hAV]
    have hJZ : ∫⁻ z in A ∩ Z, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet = 0 := by
      rw [setLIntegral_congr_fun hAZ (g := fun _ => 0) (fun z hz => by
        have hJz : (fderiv ℝ χ z).toLinearMap.normDet = 0 := by
          by_contra h
          exact hz.2.2 ⟨hz.2.1, h⟩
        simp [hJz])]
      simp
    have hint : ∫⁻ z in A, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet =
        ∫⁻ z in A ∩ G, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet := by
      conv_lhs => rw [hAsplit]
      rw [lintegral_union hAZ (Disjoint.mono inter_subset_right inter_subset_right
        disjoint_sdiff_right), hJZ, add_zero]
    have hcz := hcritZ (A ∩ Z) hAZ inter_subset_right
    rw [hint, ← hregG (A ∩ G) hAG inter_subset_right]
    apply le_antisymm
    · calc μHE[k] (χ '' A) = μHE[k] (χ '' (A ∩ G) ∪ χ '' (A ∩ Z)) := by
            rw [← image_union, ← hAsplit]
        _ ≤ μHE[k] (χ '' (A ∩ G)) + μHE[k] (χ '' (A ∩ Z)) := measure_union_le _ _
        _ = μHE[k] (χ '' (A ∩ G)) := by rw [hcz, add_zero]
    · exact measure_mono (image_mono inter_subset_left)
  -- Step 9: the weighted formula, pushing `J Lᵏ ⌞ S` forward under (a Borel version of) `χ`
  classical
  set u : Rn k → Rn N := S.piecewise χ 0 with hu
  have humeas : Measurable u := (hχcont.mono hSV).measurable_piecewise continuousOn_const hS
  have hueq : ∀ z ∈ S, u z = χ z := fun z hz => Set.piecewise_eq_of_mem _ _ _ hz
  have hmap : Measure.map u ((volume.restrict S).withDensity
      (fun z ↦ ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet)) =
        (μHE[k] : Measure (Rn N)).restrict (χ '' S) := by
    ext B hB
    rw [Measure.map_apply humeas hB, withDensity_apply _ (humeas hB),
      Measure.restrict_restrict (humeas hB), Measure.restrict_apply hB,
      ← hmain _ (inter_subset_right.trans hSV) ((humeas hB).inter hS)]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨hzB, hzS⟩, rfl⟩
      exact ⟨by rwa [mem_preimage, hueq z hzS] at hzB, z, hzS, rfl⟩
    · rintro ⟨hyB, z, hzS, rfl⟩
      exact ⟨z, ⟨by rwa [mem_preimage, hueq z hzS], hzS⟩, rfl⟩
  have hJae : AEMeasurable (fun z ↦ ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet)
      (volume.restrict S) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hJcont.mono hSV).aemeasurable hS)
  rw [← hmap, lintegral_map hφ humeas, lintegral_withDensity_eq_lintegral_mul₀ hJae
    (g := fun z ↦ φ (u z)) (hφ.comp humeas).aemeasurable]
  refine setLIntegral_congr_fun hS fun z hz => ?_
  simp only [Pi.mul_apply, hueq z hz]
  exact mul_comm _ _

/-- **Block-triangular factorization of `normDet`** (steps 1 and 6 of the flat Jacobian identity
for the co-area formula, Simon Ch. 3, (2.7)–(2.8)). Let `Γ : ℝ^{m+k} → ℝᵐ` be surjective and
`S : ℝ^{m+k} → ℝᵏ` linear, let `T : ℝ^{m+k} → WithLp 2 (ℝᵐ × ℝᵏ)` have components `Γ` and `S`,
and let `K = ker Γ`. Then `normDet T = normDet (Γ|_{K^⊥}) · normDet (S|_K)`. In the coordinates
`c(a, b) = a + b`, a linear isometry `WithLp 2 (K^⊥ × K) ≃ ℝ^{m+k}`, and orthonormal bases of
`K^⊥`, `K`, `ℝᵐ`, `ℝᵏ`, the matrix of `T ∘ c` is block lower-triangular because `Γ` vanishes on
`K`; its diagonal blocks are the matrices of `Γ|_{K^⊥}` and `S|_K`. -/
theorem Submission.pcoarea_flat_normDet_block : ∀ (m k : ℕ) (Γ : Rn (m + k) →ₗ[ℝ] Rn m) (S : Rn (m + k) →ₗ[ℝ] Rn k) (T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k)), Function.Surjective Γ → (∀ v, (T v).fst = Γ v) → (∀ v, (T v).snd = S v) → T.normDet = (Γ.domRestrict (LinearMap.ker Γ)ᗮ).normDet * (S ∘ₗ (LinearMap.ker Γ).subtype).normDet := by
  intro m k Γ S T hΓ hfst hsnd
  -- Step 1: `dim K = k` by rank–nullity (`Γ` is onto), hence `dim K^⊥ = m`.
  have hK : finrank ℝ (LinearMap.ker Γ) = k := by
    have h := LinearMap.finrank_range_add_finrank_ker Γ
    rw [LinearMap.range_eq_top.mpr hΓ, finrank_top, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin] at h
    omega
  have hKp : finrank ℝ (LinearMap.ker Γ)ᗮ = m := by
    have h := Submodule.finrank_add_finrank_orthogonal (LinearMap.ker Γ)
    rw [hK, finrank_euclideanSpace_fin] at h
    omega
  -- Step 2: `c(a, b) = a + b` is a linear isometry `WithLp 2 (K^⊥ × K) ≃ ℝ^{m+k}`, so
  -- `normDet (T ∘ c) = normDet T · normDet c = normDet T`.
  let c : WithLp 2 ((LinearMap.ker Γ)ᗮ × LinearMap.ker Γ) ≃ₗᵢ[ℝ] Rn (m + k) :=
    ((LinearMap.ker Γ).orthogonalDecomposition.trans
      (LinearIsometryEquiv.withLpProdComm 2 ℝ _ _)).symm
  have hc : ∀ p, c p = (p.fst : Rn (m + k)) + (p.snd : Rn (m + k)) := by
    intro p
    change ((p.snd : Rn (m + k)) + (p.fst : Rn (m + k))) = _
    exact add_comm _ _
  have hTc : (T ∘ₗ c.toLinearEquiv.toLinearMap).normDet = T.normDet := by
    rw [LinearMap.normDet_comp_of_finrank_eq _ _ c.toLinearEquiv.finrank_eq,
      show c.toLinearEquiv.toLinearMap.normDet = 1 from c.toLinearIsometry.normDet_eq_one,
      mul_one]
  -- Steps 3–5: in the product orthonormal bases `β₁.prod β₂` of `WithLp 2 (K^⊥ × K)` and
  -- `γ₁.prod γ₂` of `WithLp 2 (ℝᵐ × ℝᵏ)`, the matrix of `T ∘ c` has the blocks
  -- `⟨γ₁ i, Γ (β₁ j)⟩`, `⟨γ₁ i, Γ (β₂ j)⟩ = 0` (as `β₂ j ∈ ker Γ`), `⟨γ₂ i, S (β₁ j)⟩` and
  -- `⟨γ₂ i, S (β₂ j)⟩`.
  let β₁ : OrthonormalBasis (Fin m) ℝ (LinearMap.ker Γ)ᗮ :=
    (stdOrthonormalBasis ℝ (LinearMap.ker Γ)ᗮ).reindex (finCongr hKp)
  let β₂ : OrthonormalBasis (Fin k) ℝ (LinearMap.ker Γ) :=
    (stdOrthonormalBasis ℝ (LinearMap.ker Γ)).reindex (finCongr hK)
  let γ₁ := EuclideanSpace.basisFun (Fin m) ℝ
  let γ₂ := EuclideanSpace.basisFun (Fin k) ℝ
  have hmat : LinearMap.toMatrix (β₁.prod β₂).toBasis (γ₁.prod γ₂).toBasis
      (T ∘ₗ c.toLinearEquiv.toLinearMap) =
      Matrix.fromBlocks
        (LinearMap.toMatrix β₁.toBasis γ₁.toBasis (Γ.domRestrict (LinearMap.ker Γ)ᗮ)) 0
        (LinearMap.toMatrix β₁.toBasis γ₂.toBasis (S.domRestrict (LinearMap.ker Γ)ᗮ))
        (LinearMap.toMatrix β₂.toBasis γ₂.toBasis (S ∘ₗ (LinearMap.ker Γ).subtype)) := by
    have hc' : ∀ x, c.toLinearEquiv x = c x := fun _ => rfl
    ext (i | i) (j | j) <;>
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis, OrthonormalBasis.prod_apply,
        OrthonormalBasis.repr_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
        LinearMap.comp_apply, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
        WithLp.prod_inner_apply, LinearMap.domRestrict_apply, Submodule.subtype_apply] <;>
      simp [hc', hc, hfst, hsnd]
  -- Steps 6–7: `det (fromBlocks M₁₁ 0 M₂₁ M₂₂) = det M₁₁ · det M₂₂`, and `normDet` is `‖det‖` of
  -- the matrix in orthonormal bases indexed by the same type.
  rw [← hTc, LinearMap.normDet_eq_norm_det_toMatrix _ (β₁.prod β₂) (γ₁.prod γ₂), hmat,
    Matrix.det_fromBlocks_zero₁₂, norm_mul,
    ← LinearMap.normDet_eq_norm_det_toMatrix _ β₁ γ₁,
    ← LinearMap.normDet_eq_norm_det_toMatrix _ β₂ γ₂]

/-- **Section identity for the flat co-area Jacobian** (steps (i) and (iv) of the flat-Jacobian
computation behind Simon Ch. 3, (2.7)–(2.8)). Let `K ⊆ ℝⁿ` be a subspace with `dim K = k`,
`ι_K : K → ℝⁿ` its inclusion, and `E : ℝᵏ → ℝⁿ` linear with range in `K` and left inverse
`S : ℝⁿ → ℝᵏ`. Then `normDet(A ∘ E) normDet(S ∘ ι_K) = normDet(A ∘ ι_K)` for every linear
`A : ℝⁿ → ℝᴺ`. Corestricting `E` to `E' : ℝᵏ → K` gives `A ∘ E = (A ∘ ι_K) ∘ E'` and
`(S ∘ ι_K) ∘ E' = id`; as `dim ℝᵏ = dim K`, `normDet` is multiplicative on both composites, so
`normDet(A ∘ E) = normDet(A ∘ ι_K) normDet(E')` and `normDet(S ∘ ι_K) normDet(E') = 1`. -/
theorem Submission.pcoarea_flat_normDet_section : ∀ (n k N : ℕ) (A : Rn n →ₗ[ℝ] Rn N) (K : Submodule ℝ (Rn n)) (S : Rn n →ₗ[ℝ] Rn k) (E : Rn k →ₗ[ℝ] Rn n), Module.finrank ℝ K = k → (∀ z, E z ∈ K) → (∀ z, S (E z) = z) → (A ∘ₗ E).normDet * (S ∘ₗ K.subtype).normDet = (A ∘ₗ K.subtype).normDet := by
  intro n k N A K S E hK hEK hSE
  -- Step 1: corestrict `E` to `E' : ℝᵏ → K`; then `A ∘ E = (A ∘ ι_K) ∘ E'`.
  let E' : Rn k →ₗ[ℝ] K := E.codRestrict K hEK
  have hAE : A ∘ₗ E = (A ∘ₗ K.subtype) ∘ₗ E' := rfl
  -- Step 2: `(S ∘ ι_K) ∘ E' = id`.
  have hSE' : (S ∘ₗ K.subtype) ∘ₗ E' = LinearMap.id := LinearMap.ext hSE
  -- Step 3: `dim ℝᵏ = k = dim K`.
  have hdim : finrank ℝ (Rn k) = finrank ℝ K := by rw [finrank_euclideanSpace_fin, hK]
  -- Steps 4–5: `normDet` is multiplicative on both composites.
  have h4 := LinearMap.normDet_comp_of_finrank_eq E' (A ∘ₗ K.subtype) hdim
  have h5 := LinearMap.normDet_comp_of_finrank_eq E' (S ∘ₗ K.subtype) hdim
  rw [hSE', LinearMap.normDet_id] at h5
  -- Step 6: `normDet(A ∘ E) normDet(S ∘ ι_K) = normDet(A ∘ ι_K) (normDet(S ∘ ι_K) normDet(E'))`.
  rw [hAE, h4, mul_right_comm, mul_assoc, ← h5, mul_one]

/-- **Flat Jacobian identity**: the linear algebra behind the co-area formula 2.7–2.8 of Simon
Ch. 3 (`chapter-03.txt` lines 411–425), which "follows from the `C¹` case". Let `n = m + k`,
`T : ℝⁿ → WithLp 2 (ℝᵐ × ℝᵏ)` be bijective with first component `Γ` and `T (E z) = (0, z)`, and
`K = ker Γ`. Then `normDet (A ∘ E) · normDet T = normDet (A ∘ ι_K) · normDet Γ*`.
`Γ` is onto (as `T` is), so `dim K = k`. With `S` the second component of `T`, `E` maps into `K`
and `S ∘ E = id`, whence `normDet (A ∘ E) · normDet (S ∘ ι_K) = normDet (A ∘ ι_K)`
(`pcoarea_flat_normDet_section`). In the orthogonal splitting `ℝⁿ = K^⊥ ⊕ K`, `T` is block lower
triangular, so `normDet T = normDet (Γ|_{K^⊥}) · normDet (S ∘ ι_K)`
(`pcoarea_flat_normDet_block`). Finally `Γ*`, corestricted to `K^⊥ = range Γ*`, is the adjoint
of the square map `Γ|_{K^⊥}` and so has the same `normDet`. No property of `A` is used. -/
theorem Submission.pcoarea_flat_jacobian_identity : ∀ (m k N : ℕ) (A : Rn (m + k) →ₗ[ℝ] Rn N)
    (Γ : Rn (m + k) →ₗ[ℝ] Rn m) (T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k))
    (E : Rn k →ₗ[ℝ] Rn (m + k)), Function.Bijective T → (∀ v, (T v).fst = Γ v) →
    (∀ z, T (E z) = WithLp.toLp 2 (0, z)) →
    (A ∘ₗ E).normDet * T.normDet =
      (A ∘ₗ (LinearMap.ker Γ).subtype).normDet * (LinearMap.adjoint Γ).normDet := by
  intro m k N A Γ T E hT hfst hE
  -- Step 1: `Γ = fst ∘ T` is surjective because `T` is, so `K = ker Γ` has dimension `k`.
  have hΓ : Function.Surjective Γ := by
    intro y
    obtain ⟨v, hv⟩ := hT.2 (WithLp.toLp 2 (y, 0))
    exact ⟨v, by rw [← hfst, hv, WithLp.toLp_fst]⟩
  have hK : finrank ℝ (LinearMap.ker Γ) = k := by
    have h := LinearMap.finrank_range_add_finrank_ker Γ
    rw [LinearMap.range_eq_top.mpr hΓ, finrank_top, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin] at h
    omega
  -- Step 2: `T v = (Γ v, S v)` with `S = snd ∘ T`; `E` maps into `K` and `S ∘ E = id`.
  obtain ⟨S, hsnd⟩ : ∃ S : Rn (m + k) →ₗ[ℝ] Rn k, ∀ v, (T v).snd = S v :=
    ⟨WithLp.sndₗ 2 ℝ (Rn m) (Rn k) ∘ₗ T, fun v ↦ rfl⟩
  have hEK : ∀ z, E z ∈ LinearMap.ker Γ := by
    intro z
    rw [LinearMap.mem_ker, ← hfst, hE, WithLp.toLp_fst]
  have hSE : ∀ z, S (E z) = z := by
    intro z
    rw [← hsnd, hE, WithLp.toLp_snd]
  -- Steps 3–4: `normDet (A ∘ E) · normDet (S ∘ ι_K) = normDet (A ∘ ι_K)`.
  have hsec := Submission.pcoarea_flat_normDet_section (m + k) k N A (LinearMap.ker Γ) S E hK
    hEK hSE
  -- Step 6: `normDet T = normDet (Γ|_{K^⊥}) · normDet (S ∘ ι_K)`.
  have hblock := Submission.pcoarea_flat_normDet_block m k Γ S T hΓ hfst hsnd
  -- Step 5: `normDet (Γ|_{K^⊥}) = normDet Γ*`.
  have hadj : (Γ.domRestrict (LinearMap.ker Γ)ᗮ).normDet = (LinearMap.adjoint Γ).normDet := by
    have hm : ∀ y, LinearMap.adjoint Γ y ∈ (LinearMap.ker Γ)ᗮ := by
      intro y
      rw [LinearMap.orthogonal_ker]
      exact ⟨y, rfl⟩
    have ha : (LinearMap.adjoint Γ).codRestrict (LinearMap.ker Γ)ᗮ hm =
        LinearMap.adjoint (Γ.domRestrict (LinearMap.ker Γ)ᗮ) := by
      apply (LinearMap.eq_adjoint_iff _ _).mpr
      intro y x
      exact LinearMap.adjoint_inner_left Γ x y
    have hd : finrank ℝ (LinearMap.ker Γ)ᗮ = finrank ℝ (Rn m) := by
      have h := Submodule.finrank_add_finrank_orthogonal (LinearMap.ker Γ)
      rw [hK, finrank_euclideanSpace_fin] at h
      rw [finrank_euclideanSpace_fin]
      omega
    classical
    let b₁ := stdOrthonormalBasis ℝ (LinearMap.ker Γ)ᗮ
    let b₂ := (stdOrthonormalBasis ℝ (Rn m)).reindex (finCongr hd.symm)
    rw [← LinearMap.normDet_codRestrict hm, ha,
      (LinearMap.adjoint _).normDet_eq_norm_det_toMatrix b₂ b₁,
      (Γ.domRestrict _).normDet_eq_norm_det_toMatrix b₁ b₂, LinearMap.toMatrix_adjoint,
      Matrix.det_conjTranspose]
    simp
  -- Step 7: combine.
  rw [hblock, ← hsec, hadj]
  ring

/-- **Critical part of the parametric co-area formula** (parent steps 0(a) and 1). On
`B ⊆ Crit = {u | DG(u) not surjective}` the Jacobian vanishes: `ker DG(u)* = (range DG(u))ᗮ ≠ 0`,
so `normDet DG(u)* = 0` and the left side is `0`. On the right, `ψ` is `C¹` on the open set `D`,
hence locally Lipschitz there; by Lindelöf and Ch. 2, Thm. 1.8(i) (SimonGMT
`euclideanHausdorffMeasure_image_le_of_lipschitzOn`) it maps `Hᵏ`-null subsets of `D` to `Hᵏ`-null
sets. For `Lᵐ`-a.e. `y`, `Hᵏ(B ∩ G⁻¹{y}) ≤ Hᵏ(Crit ∩ G⁻¹{y}) = 0`, so the inner integral over
`ψ(B ∩ G⁻¹{y})` vanishes: the inner function is a.e. `0`, hence a.e.-measurable with integral `0`.
Neither measurability of `φ` nor any regularity of `G` is needed. -/
theorem Submission.pcoarea_critical_part : ∀ (m k N : ℕ) (D : Set (Rn (m + k)))
    (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m), IsOpen D → ContDiffOn ℝ 1 ψ D →
    (∀ᵐ y ∂(volume : Measure (Rn m)),
      μHE[k] ({u | ¬ Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y}) = 0) →
    ∀ B ⊆ D, MeasurableSet B → B ⊆ {u | ¬ Function.Surjective (fderiv ℝ G u)} →
    ∀ φ : Rn N → ℝ≥0∞, Measurable φ →
    AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧
    ∫⁻ u in B, φ (ψ u) * ENNReal.ofReal (((fderiv ℝ ψ u).toLinearMap ∘ₗ
      (LinearMap.ker (fderiv ℝ G u).toLinearMap).subtype).normDet *
      (LinearMap.adjoint (fderiv ℝ G u).toLinearMap).normDet) =
    ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume := by
  intro m k N D ψ G hD hψ hcrit B hBD hB hBcrit φ hφ
  -- Step 1: on `B`, `DG(u)` is not surjective, so `normDet (DG(u)*) = 0` and the left side is `0`.
  have hdet : ∀ u ∈ B, (LinearMap.adjoint (fderiv ℝ G u).toLinearMap).normDet = 0 := by
    intro u hu
    rw [LinearMap.normDet_eq_zero_iff_ker_ne_bot, ← LinearMap.orthogonal_range, Ne,
      Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top]
    exact hBcrit hu
  have hlhs : ∫⁻ u in B, φ (ψ u) * ENNReal.ofReal (((fderiv ℝ ψ u).toLinearMap ∘ₗ
      (LinearMap.ker (fderiv ℝ G u).toLinearMap).subtype).normDet *
      (LinearMap.adjoint (fderiv ℝ G u).toLinearMap).normDet) = 0 := by
    refine (setLIntegral_congr_fun hB fun u hu ↦ ?_).trans lintegral_zero
    simp only [hdet u hu, mul_zero, ENNReal.ofReal_zero]
  -- Step 2: `ψ` is locally Lipschitz on the open set `D`, so it maps `Hᵏ`-null subsets of `D`
  -- to `Hᵏ`-null sets (Lindelöf and countable subadditivity).
  have hnull : ∀ S ⊆ D, μHE[k] S = 0 → μHE[k] (ψ '' S) = 0 := by
    intro S hSD hS
    have hloc : ∀ x ∈ S, ∃ o : Set (Rn (m + k)), IsOpen o ∧ x ∈ o ∧
        ∃ K : ℝ≥0, LipschitzOnWith K ψ o := by
      intro x hx
      obtain ⟨K, t, ht, hK⟩ := (hψ.contDiffAt (hD.mem_nhds (hSD hx))).exists_lipschitzOnWith
      obtain ⟨o, hot, ho, hxo⟩ := mem_nhds_iff.mp ht
      exact ⟨o, ho, hxo, K, hK.mono hot⟩
    choose! o ho hxo K hK using hloc
    obtain ⟨T, hTS, hTc, hTo⟩ := TopologicalSpace.isOpen_biUnion_countable S o ho
    have hcover : ψ '' S ⊆ ⋃ x ∈ T, ψ '' (S ∩ o x) := by
      rintro _ ⟨z, hz, rfl⟩
      have hzT : z ∈ ⋃ x ∈ T, o x := by
        rw [hTo]
        exact mem_biUnion hz (hxo z hz)
      obtain ⟨x, hxT, hzx⟩ := mem_iUnion₂.mp hzT
      exact mem_iUnion₂.mpr ⟨x, hxT, z, ⟨hz, hzx⟩, rfl⟩
    have hpiece : ∀ x ∈ T, μHE[k] (ψ '' (S ∩ o x)) = 0 := by
      intro x hx
      have hL : LipschitzOnWith (K x) ψ (S ∩ o x) := (hK x (hTS hx)).mono inter_subset_right
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k hL
      rw [measure_mono_null inter_subset_left hS, mul_zero] at h
      exact nonpos_iff_eq_zero.mp h
    exact measure_mono_null hcover ((measure_biUnion_null_iff hTc).2 hpiece)
  -- Step 3: for a.e. `y`, `Hᵏ(B ∩ G⁻¹{y}) = 0`, so `Hᵏ(ψ(B ∩ G⁻¹{y})) = 0` and the inner
  -- integral vanishes.
  have hae : (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) =ᵐ[volume]
      fun _ ↦ 0 := by
    filter_upwards [hcrit] with y hy
    exact setLIntegral_measure_zero _ _ (hnull _ (inter_subset_left.trans hBD)
      (measure_mono_null (inter_subset_inter_left _ hBcrit) hy))
  -- Step 4: the inner function is a.e. `0`, so it is a.e.-measurable and both sides are `0`.
  exact ⟨aemeasurable_const.congr hae.symm, by rw [hlhs, lintegral_congr_ae hae, lintegral_zero]⟩

/-- **Implicit-function chart at a regular point** (step 2, L2, of the parametric co-area
formula): if `G : ℝ^{m+k} → ℝᵐ` is `C¹` and `DG(u₀)` is onto, then `Φ = (G, π)`, restricted to a
neighbourhood of `u₀` inside the open set `D`, is a `C¹` chart onto an open subset of
`WithLp 2 (ℝᵐ × ℝᵏ)` with `C¹` inverse and first component `G`. Here `π = ι ∘ p`, where `p` is
the orthogonal projection onto `K₀ = ker DG(u₀)` (of dimension `k` by rank–nullity) and
`ι : K₀ ≃ₗᵢ ℝᵏ`; then `DΦ(u₀) = (DG(u₀), π)` is invertible. The inverse function theorem gives
`Φ` near `u₀`, and restricting it to `D ∩ {u : DΦ(u) invertible}` (open) makes `Φ⁻¹` `C¹` at
every point of the target. -/
theorem Submission.pcoarea_implicit_chart : ∀ (m k : ℕ) (G : Rn (m + k) → Rn m) (D : Set (Rn (m + k))) (u₀ : Rn (m + k)), IsOpen D → u₀ ∈ D → ContDiff ℝ 1 G → Function.Surjective (fderiv ℝ G u₀) → ∃ Φ : OpenPartialHomeomorph (Rn (m + k)) (WithLp 2 (Rn m × Rn k)), u₀ ∈ Φ.source ∧ Φ.source ⊆ D ∧ ContDiffOn ℝ 1 Φ Φ.source ∧ ContDiffOn ℝ 1 Φ.symm Φ.target ∧ ∀ u ∈ Φ.source, (Φ u).fst = G u := by
  intro m k G D u₀ hD hu₀ hG hsurj
  -- Step 1: `K₀ = ker DG(u₀)` has dimension `k` (rank–nullity).
  set K₀ : Submodule ℝ (Rn (m + k)) := (fderiv ℝ G u₀).ker
  have hdim : finrank ℝ K₀ = k := by
    have h := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ G u₀).toLinearMap
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin] at h
    change m + finrank ℝ K₀ = m + k at h
    omega
  -- Step 2: `π = ι ∘ p` with `p` the orthogonal projection onto `K₀` and `ι : K₀ ≃ₗᵢ ℝᵏ`.
  let ι : K₀ ≃ₗᵢ[ℝ] Rn k := ((stdOrthonormalBasis ℝ K₀).reindex (finCongr hdim)).repr
  let π : Rn (m + k) →L[ℝ] Rn k :=
    (ι.toContinuousLinearEquiv : K₀ →L[ℝ] Rn k).comp K₀.orthogonalProjectionOnto
  have hπ : ∀ v : K₀, π v = ι v := fun v ↦ by
    simp [π, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  -- Step 3: `F = σ ∘ (G, π)` is `C¹`, with `DF(u) = σ ∘ (DG(u), π)`.
  let σ := (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm
  let F : Rn (m + k) → WithLp 2 (Rn m × Rn k) := fun u ↦ σ (G u, π u)
  have hF : ContDiff ℝ 1 F := σ.contDiff.comp (hG.prodMk π.contDiff)
  let L : Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k) :=
    (σ : Rn m × Rn k →L[ℝ] WithLp 2 (Rn m × Rn k)).comp ((fderiv ℝ G u₀).prod π)
  have hFL : HasFDerivAt F L u₀ :=
    σ.hasFDerivAt.comp u₀ (((hG.differentiable one_ne_zero) u₀).hasFDerivAt.prodMk π.hasFDerivAt)
  -- Step 4: `DF(u₀)` is bijective.
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h0 : (fderiv ℝ G u₀ v, π v) = 0 := by
      simpa [L] using hv
    have hvK : v ∈ K₀ := LinearMap.mem_ker.mpr (congrArg Prod.fst h0)
    have hιv : ι ⟨v, hvK⟩ = 0 := by
      rw [← hπ]
      exact congrArg Prod.snd h0
    exact congrArg Subtype.val (ι.map_eq_zero_iff.mp hιv)
  have hsurjL : Function.Surjective L := by
    intro z
    obtain ⟨v₁, hv₁⟩ := hsurj z.fst
    let c : K₀ := ι.symm (z.snd - π v₁)
    refine ⟨v₁ + c, ?_⟩
    have h1 : fderiv ℝ G u₀ (c : Rn (m + k)) = 0 := LinearMap.mem_ker.mp c.2
    have h2 : π c = z.snd - π v₁ := by
      rw [hπ]
      exact ι.apply_symm_apply _
    have e1 : fderiv ℝ G u₀ (v₁ + c) = z.fst := by rw [map_add, h1, add_zero, hv₁]
    have e2 : π (v₁ + c) = z.snd := by rw [map_add, h2, add_sub_cancel]
    change σ (fderiv ℝ G u₀ (v₁ + c), π (v₁ + c)) = z
    rw [e1, e2]
    rfl
  let f' : Rn (m + k) ≃L[ℝ] WithLp 2 (Rn m × Rn k) :=
    ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurjL)
  have hf' : (f' : Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)) = L :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  -- Step 5: the inverse function theorem.
  have hstrict : HasStrictFDerivAt F (f' : Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)) u₀ :=
    hF.contDiffAt.hasStrictFDerivAt' (hf' ▸ hFL) one_ne_zero
  -- Step 6: restrict to `U = D ∩ W`, `W = {u : DF(u) is invertible}` (open).
  let W : Set (Rn (m + k)) := fderiv ℝ F ⁻¹' Set.range ContinuousLinearEquiv.toContinuousLinearMap
  have hW : IsOpen W := ContinuousLinearEquiv.isOpen.preimage (hF.continuous_fderiv one_ne_zero)
  have hu₀W : u₀ ∈ W := ⟨f', by rw [hFL.fderiv, ← hf']⟩
  have hU : IsOpen (D ∩ W) := hD.inter hW
  let Φ := (hstrict.toOpenPartialHomeomorph F).restrOpen (D ∩ W) hU
  have hΦ : (Φ : Rn (m + k) → WithLp 2 (Rn m × Rn k)) = F := by
    simp only [Φ, OpenPartialHomeomorph.coe_restrOpen,
      HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  -- Step 7: verification.
  refine ⟨Φ, ⟨hstrict.mem_toOpenPartialHomeomorph_source, hu₀, hu₀W⟩, fun u hu ↦ hu.2.1, ?_, ?_,
    ?_⟩
  · rw [hΦ]
    exact hF.contDiffOn
  · intro w hw
    have hsrc : Φ.symm w ∈ Φ.source := Φ.map_target hw
    obtain ⟨e, he⟩ := hsrc.2.2
    refine (Φ.contDiffAt_symm (f₀' := e) hw ?_ ?_).contDiffWithinAt
    · rw [hΦ]
      change HasFDerivAt F (e.toContinuousLinearMap) (Φ.symm w)
      rw [he]
      exact ((hF.differentiable one_ne_zero) _).hasFDerivAt
    · rw [hΦ]
      exact hF.contDiffAt
  · intro u hu
    rw [hΦ]
    rfl

/-- **Parametric co-area formula on one chart** (Simon Ch. 3, co-area formula 2.8–2.9, regular
part of the `C¹` case; cf. Federer 3.2.12, 3.2.22). Let `Φ` be an open partial homeomorphism from
`ℝⁿ`, `n = m + k`, to `P = WithLp 2 (ℝᵐ × ℝᵏ)`, `C¹` on its source `O` with `C¹` inverse on its
target, whose first component is `G` on `O`, and let `ψ` be `C¹` and injective on `O`. For Borel
`B ⊆ O` and Borel `φ ≥ 0`, `y ↦ ∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ` is a.e. measurable and
`∫_B φ(ψ(u)) J(u) du = ∫_{ℝᵐ} ∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ dy`, where
`J(u) = normDet (Dψ(u) ∘ ι_{ker DG(u)}) · normDet (DG(u)*)`.
With `ρ = ψ ∘ Φ⁻¹`, `j z = (0, z)`, `h = φ ∘ ρ · normDet (Dρ ∘ j)` and `F = 1_{Φ(B)} h` on `P`:
* each slice integral is `∫_{ℝᵏ} F(y, z) dz`, by the injective area formula on the slice
  `z ↦ ρ(y, z)` (`pcoarea_chart_slice_lintegral` with `pcoarea_c1_injOn_area_formula`);
* `y ↦ ∫ F(y, z) dz` is measurable and `∫_P F = ∫_{ℝᵐ} ∫_{ℝᵏ} F(y, z) dz dy` (Tonelli,
  `pcoarea_chart_integrand_tonelli`);
* `Φ(B)` is Borel (Lusin–Souslin), so `∫_P F = ∫_{Φ(B)} h = ∫_B normDet (DΦ(u)) h(Φ(u)) du`
  (`pcoarea_chart_change_of_variables`);
* `normDet (Dρ(Φ(u)) ∘ j) · normDet (DΦ(u)) = J(u)` (`pcoarea_chart_pointwise_jacobian` with the
  flat Jacobian identity `pcoarea_flat_jacobian_identity`). -/
theorem Submission.pcoarea_formula_on_chart : ∀ (m k N : ℕ) (ψ : Rn (m + k) → Rn N)
    (G : Rn (m + k) → Rn m) (Φ : OpenPartialHomeomorph (Rn (m + k)) (WithLp 2 (Rn m × Rn k))),
    ContDiffOn ℝ 1 ψ Φ.source → InjOn ψ Φ.source → ContDiffOn ℝ 1 Φ Φ.source →
    ContDiffOn ℝ 1 Φ.symm Φ.target → (∀ u ∈ Φ.source, (Φ u).fst = G u) →
    ∀ B ⊆ Φ.source, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ →
    AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧
      ∫⁻ u in B, φ (ψ u) * ENNReal.ofReal (((fderiv ℝ ψ u).toLinearMap ∘ₗ
          (LinearMap.ker (fderiv ℝ G u).toLinearMap).subtype).normDet *
          (LinearMap.adjoint (fderiv ℝ G u).toLinearMap).normDet) =
        ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume := by
  intro m k N ψ G Φ hψ hinj hΦ hΦs hfst B hB hBm φ hφ
  -- Steps 1–3: the area formula on every slice gives `∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ = ∫ F(y, z) dz`.
  have hslice := Submission.pcoarea_chart_slice_lintegral m k N ψ G Φ hψ hinj hΦs hfst B hB hBm φ
    (fun V χ hV hχ hχi S hSV hS ↦
      Submission.pcoarea_c1_injOn_area_formula k N V χ hV hχ hχi S hSV hS φ hφ)
  -- Steps 4–5: `F` is Borel, and Tonelli on `ℝᵐ × ℝᵏ` transported to `P`.
  obtain ⟨hmeas, htonelli⟩ :=
    Submission.pcoarea_chart_integrand_tonelli m k N ψ Φ hψ.continuousOn B hB hBm φ hφ
  -- First claim: the slice integral is everywhere equal to a measurable function of `y`.
  refine ⟨hmeas.aemeasurable.congr (Eventually.of_forall fun y ↦ (hslice y).symm), ?_⟩
  -- Step 6: `Φ(B)` is Borel and `Φ` has derivative `DΦ(u)` within `B` at each `u ∈ B`.
  have hΦB : MeasurableSet (Φ '' B) :=
    hBm.image_of_continuousOn_injOn (Φ.continuousOn.mono hB) (Φ.injOn.mono hB)
  have hder : ∀ u ∈ B, HasFDerivWithinAt Φ (fderiv ℝ Φ u) B u := fun u hu ↦
    ((hΦ.differentiableOn one_ne_zero u (hB hu)).differentiableAt
      (Φ.open_source.mem_nhds (hB hu))).hasFDerivAt.hasFDerivWithinAt
  -- Step 7: `normDet (Dρ(Φ(u)) ∘ j) · normDet (DΦ(u)) = J(u)` on the source.
  have hjac := Submission.pcoarea_chart_pointwise_jacobian m k N ψ G Φ hψ hΦ hΦs hfst
    (Submission.pcoarea_flat_jacobian_identity m k N)
  -- Second claim: `∫∫ = ∫_P F = ∫_{Φ(B)} h = ∫_B normDet (DΦ(u)) h(Φ(u)) du = ∫_B φ(ψ(u)) J(u) du`.
  rw [lintegral_congr hslice, ← htonelli, lintegral_indicator hΦB,
    Submission.pcoarea_chart_change_of_variables m k Φ (fderiv ℝ Φ) B hBm hder (Φ.injOn.mono hB)]
  refine setLIntegral_congr_fun hBm (fun u hu ↦ ?_)
  rw [← hjac u (hB hu), ENNReal.ofReal_mul (LinearMap.normDet_nonneg _), Φ.left_inv (hB hu)]
  ring

/-- **Lindelöf gluing of the parametric co-area identity**: the localization step of the proof of
the `C¹` co-area formula (Simon Ch. 2, 6.3 and 6.6, whose proof Simon omits; [Fed69, 3.2.12,
3.2.22]). Let `D ⊆ ℝⁿ` be open, `Z ⊆ ℝⁿ` arbitrary, `ψ : ℝⁿ → ℝᴺ` continuous and injective on `D`,
`G : ℝⁿ → ℝᵐ` continuous and `w ≥ 0` arbitrary. Call a Borel set `B ⊆ D` good if for every Borel
`φ ≥ 0` the function `y ↦ ∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ` is `Lᵐ`-a.e. measurable and
`∫_B φ(ψ(u)) w(u) dLⁿ(u) = ∫_{ℝᵐ} ∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ dLᵐ(y)`. If every Borel `B ⊆ D` with
`B ⊆ Z` is good, and every `p ∈ D \ Z` has an open neighbourhood `O` such that every Borel
`B ⊆ D ∩ O` is good, then every Borel `B ⊆ D` is good. By Lindelöf, countably many of these
neighbourhoods cover `D \ Z`. They cut `B` into disjoint Borel pieces, one inside `Z` and each of
the others inside a single neighbourhood. For every `y` the images `ψ(B_t ∩ G⁻¹{y})` of the
pieces' slices are Borel (Lusin–Souslin) and pairwise disjoint (`ψ` is injective on `D`), so both
sides of the identity are countably additive over the pieces. -/
theorem Submission.pcoarea_gluing : ∀ (n N m k : ℕ) (D Z : Set (Rn n)) (ψ : Rn n → Rn N) (G : Rn n → Rn m) (w : Rn n → ℝ≥0∞), IsOpen D → ContinuousOn ψ D → InjOn ψ D → Continuous G → (∀ B ⊆ D, MeasurableSet B → B ⊆ Z → ∀ φ : Rn N → ℝ≥0∞, Measurable φ → AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧ ∫⁻ u in B, φ (ψ u) * w u = ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume) → (∀ p ∈ D, p ∉ Z → ∃ O : Set (Rn n), IsOpen O ∧ p ∈ O ∧ ∀ B ⊆ D ∩ O, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ → AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧ ∫⁻ u in B, φ (ψ u) * w u = ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume) → ∀ B ⊆ D, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ → AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧ ∫⁻ u in B, φ (ψ u) * w u = ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume := by
  intro n N m k D Z ψ G w _hD hψc hψi hG hCrit hLoc B hBD hBm φ hφ
  classical
  -- Step 1 (Lindelöf): a good open neighbourhood `O p` of each `p ∈ D \ Z`, and a countable
  -- subfamily `(O i)_{i ∈ T}` with the same union.
  have hLoc' : ∀ p : ↥(D \ Z), ∃ O : Set (Rn n), IsOpen O ∧ (p : Rn n) ∈ O ∧
      ∀ B ⊆ D ∩ O, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ →
        AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧
          ∫⁻ u in B, φ (ψ u) * w u =
            ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume :=
    fun p ↦ hLoc p p.2.1 p.2.2
  choose O hOo hpO hOgood using hLoc'
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable O hOo
  have hcovT : D \ Z ⊆ ⋃ i ∈ T, O i := by
    intro x hx
    rw [hTU]
    exact mem_iUnion.2 ⟨⟨x, hx⟩, hpO _⟩
  -- If the subfamily is empty (the case the proof pads with `∅`), then `D ⊆ Z`, so `B` is good
  -- by (Crit).
  by_cases hT : T.Nonempty
  swap
  · have hBZ : B ⊆ Z := by
      intro x hxB
      by_contra hxZ
      obtain ⟨i, hiT, -⟩ := mem_iUnion₂.1 (hcovT ⟨hBD hxB, hxZ⟩)
      exact hT ⟨i, hiT⟩
    exact hCrit B hBD hBm hBZ φ hφ
  -- Otherwise list it as a sequence `U j = O (e j)`, `j ∈ ℕ`, covering `D \ Z`.
  obtain ⟨e, he⟩ := hTc.exists_eq_range hT
  set U : ℕ → Set (Rn n) := fun j ↦ O (e j) with hUdef
  have hUo : ∀ j, IsOpen (U j) := fun j ↦ hOo _
  have hcover : D \ Z ⊆ ⋃ j, U j := by
    intro x hx
    obtain ⟨i, hiT, hxi⟩ := mem_iUnion₂.1 (hcovT hx)
    rw [he] at hiT
    obtain ⟨j, rfl⟩ := hiT
    exact mem_iUnion.2 ⟨j, hxi⟩
  -- Step 2 (disjoint pieces): `P = disjointed C` with `C 0 = B \ ⋃ j, U j` and
  -- `C (j + 1) = B ∩ U j`, so `P 0 = B \ ⋃ j, U j` and `P (j + 1) = (B ∩ U j) \ ⋃_{i < j} U i`.
  let C : ℕ → Set (Rn n) := fun t ↦ Nat.casesOn t (B \ ⋃ j, U j) (fun j ↦ B ∩ U j)
  have hCm : ∀ t, MeasurableSet (C t) := by
    intro t
    cases t with
    | zero => exact hBm.diff (MeasurableSet.iUnion fun j ↦ (hUo j).measurableSet)
    | succ j => exact hBm.inter (hUo j).measurableSet
  have hCB : ∀ t, C t ⊆ B := by
    intro t
    cases t with
    | zero => exact sdiff_subset
    | succ j => exact inter_subset_left
  have hCU : ⋃ t, C t = B := by
    refine Subset.antisymm (iUnion_subset hCB) fun x hxB ↦ ?_
    by_cases hx : x ∈ ⋃ j, U j
    · obtain ⟨j, hxj⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨j + 1, ⟨hxB, hxj⟩⟩
    · exact mem_iUnion.2 ⟨0, ⟨hxB, hx⟩⟩
  set P : ℕ → Set (Rn n) := disjointed C with hPdef
  have hPm : ∀ t, MeasurableSet (P t) := MeasurableSet.disjointed hCm
  have hPd : Pairwise (Function.onFun Disjoint P) := disjoint_disjointed C
  have hPU : ⋃ t, P t = B := by rw [hPdef, iUnion_disjointed, hCU]
  have hPC : ∀ t, P t ⊆ C t := disjointed_subset C
  have hPD : ∀ t, P t ⊆ D := fun t ↦ (hPC t).trans ((hCB t).trans hBD)
  -- Every piece is good: `P 0 ⊆ Z` by (Crit), and `P (j + 1) ⊆ D ∩ U j` by (Loc).
  have hPgood : ∀ t, ∀ φ : Rn N → ℝ≥0∞, Measurable φ →
      AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (P t ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧
        ∫⁻ u in P t, φ (ψ u) * w u =
          ∫⁻ y, (∫⁻ x in ψ '' (P t ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume := by
    intro t
    cases t with
    | zero =>
      refine hCrit (P 0) (hPD 0) (hPm 0) fun x hx ↦ ?_
      have hx' : x ∈ B \ ⋃ j, U j := hPC 0 hx
      by_contra hxZ
      exact hx'.2 (hcover ⟨hBD hx'.1, hxZ⟩)
    | succ j =>
      refine hOgood (e j) (P (j + 1)) (fun x hx ↦ ⟨hPD _ hx, ?_⟩) (hPm _)
      have hx' : x ∈ B ∩ U j := hPC (j + 1) hx
      exact hx'.2
  -- Step 3 (slices): for each `y` the sets `ψ '' (P t ∩ G ⁻¹' {y})` are Borel (Lusin–Souslin)
  -- and pairwise disjoint, with union `ψ '' (B ∩ G ⁻¹' {y})`.
  have hslice : ∀ y : Rn m,
      ψ '' (B ∩ G ⁻¹' {y}) = ⋃ t, ψ '' (P t ∩ G ⁻¹' {y}) := by
    intro y
    rw [← image_iUnion, ← iUnion_inter, hPU]
  have hslice_meas : ∀ (y : Rn m) t, MeasurableSet (ψ '' (P t ∩ G ⁻¹' {y})) := by
    intro y t
    have hsub : P t ∩ G ⁻¹' {y} ⊆ D := inter_subset_left.trans (hPD t)
    exact ((hPm t).inter (isClosed_singleton.preimage hG).measurableSet).image_of_continuousOn_injOn
      (hψc.mono hsub) (hψi.mono hsub)
  have hslice_disj : ∀ y : Rn m,
      Pairwise (Function.onFun Disjoint fun t ↦ ψ '' (P t ∩ G ⁻¹' {y})) := by
    intro y a b hab
    exact Disjoint.image ((hPd hab).mono inter_subset_left inter_subset_left) hψi
      (inter_subset_left.trans (hPD a)) (inter_subset_left.trans (hPD b))
  have hfun : (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) =
      fun y ↦ ∑' t, ∫⁻ x in ψ '' (P t ∩ G ⁻¹' {y}), φ x ∂μHE[k] := by
    funext y
    rw [hslice y, lintegral_iUnion (hslice_meas y) (hslice_disj y)]
  -- Step 4 (measurability): a countable sum of a.e.-measurable functions.
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact AEMeasurable.tsum fun t ↦ (hPgood t φ hφ).1
  -- Step 5 (identity): countable additivity on the left, goodness of the pieces, `lintegral_tsum`.
  · calc ∫⁻ u in B, φ (ψ u) * w u = ∫⁻ u in ⋃ t, P t, φ (ψ u) * w u := by rw [hPU]
      _ = ∑' t, ∫⁻ u in P t, φ (ψ u) * w u := lintegral_iUnion hPm hPd _
      _ = ∑' t, ∫⁻ y, (∫⁻ x in ψ '' (P t ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume := by
        congr 1
        funext t
        exact (hPgood t φ hφ).2
      _ = ∫⁻ y, ∑' t, (∫⁻ x in ψ '' (P t ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume :=
        (lintegral_tsum fun t ↦ (hPgood t φ hφ).1).symm
      _ = ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume := by rw [hfun]

/-- **Regular level slices of a `C¹` map have countably `k`-rectifiable `C¹` images**
(Simon Ch. 2, proof of Theorem 6.4, `chapter-02.txt` lines 1476–1496: off the critical set the
implicit function theorem makes `G⁻¹(y)` a `k`-dimensional `C¹` submanifold). At a point `u₀` of
`D` where `DG(u₀)` is onto, `K₀ = ker DG(u₀)` has dimension `k`; with `π` the orthogonal
projection onto `K₀` followed by `K₀ ≅ ℝᵏ`, the map `Φ = (G, π)` has invertible derivative at
`u₀`, and its local inverse `Θ` parametrizes the slice near `u₀` by the open set
`W = {z | (y, z) ∈ Φ(U₀), Θ(y, z) ∈ D, DΦ(Θ(y, z)) invertible}` through the `C¹` map
`z ↦ ψ(Θ(y, z))`. `C¹` images of open subsets of `ℝᵏ` are countably `k`-rectifiable (Lipschitz
on each compact piece of a compact exhaustion, then extended), and by Lindelöf countably many
such charts cover the regular part. -/
theorem Submission.c1_regular_level_slice_image_countablyRectifiable : ∀ (m k N : ℕ) (D : Set (Rn (m + k))) (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m) (y : Rn m), IsOpen D → ContDiffOn ℝ 1 ψ D → ContDiff ℝ 1 G → CountablyRectifiable k (ψ '' (D ∩ {u | Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y})) := by
  intro m k N D ψ G y hD hψ hG
  -- C¹ images of open subsets of ℝᵏ are countably k-rectifiable
  -- (inline copy of SimonGMT `countablyRectifiable_image_contDiffOn_open`).
  have himage : ∀ (W : Set (Rn k)) (h : Rn k → Rn N), IsOpen W → ContDiffOn ℝ 1 h W →
      CountablyRectifiable k (h '' W) := by
    intro W h hW hh
    let _ : LocallyCompactSpace W := hW.locallyCompactSpace
    obtain ⟨Kc, hKc, hKcover⟩ := SigmaCompactSpace.exists_compact_covering (X := W)
    let C : ℕ → Set (Rn k) := fun j => ((↑) : W → Rn k) '' Kc j
    have hCc : ∀ j, IsCompact (C j) := fun j => (hKc j).image continuous_subtype_val
    have hCW : ∀ j, C j ⊆ W := by
      rintro j _ ⟨x, -, rfl⟩
      exact x.2
    have hLip : ∀ j, ∃ L : ℝ≥0, LipschitzOnWith L h (C j) := by
      intro j
      apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hCc j)
      intro x hx
      obtain ⟨L, t, ht, hht⟩ := (hh.contDiffAt (hW.mem_nhds (hCW j hx))).exists_lipschitzOnWith
      exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hht⟩
    choose L hL using hLip
    choose g hgL hgeq using fun j => (hL j).extend_finite_dimension
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion (fun j => range (g j))
      (fun j => Poincare.SimonGMT.Chapter03.countablyRectifiable_range (hgL j))).mono ?_
    rintro _ ⟨x, hxW, rfl⟩
    have hx : (⟨x, hxW⟩ : W) ∈ ⋃ j, Kc j := by rw [hKcover]; trivial
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    exact mem_iUnion.2 ⟨j, x, (hgeq j ⟨⟨x, hxW⟩, hj, rfl⟩).symm⟩
  -- Local charts at regular points (implicit function theorem via Φ = (G, π)).
  have hloc : ∀ u₀ : ↥(D ∩ {u | Function.Surjective (fderiv ℝ G u)}),
      ∃ O : Set (Rn (m + k)), IsOpen O ∧ (u₀ : Rn (m + k)) ∈ O ∧
        CountablyRectifiable k (ψ '' (O ∩ G ⁻¹' {y})) := by
    rintro ⟨u₀, hu₀D, hu₀S⟩
    set A : Rn (m + k) →L[ℝ] Rn m := fderiv ℝ G u₀ with hA
    have hrange : LinearMap.range (A : Rn (m + k) →ₗ[ℝ] Rn m) = ⊤ := LinearMap.range_eq_top.2 hu₀S
    set K₀ : Submodule ℝ (Rn (m + k)) := LinearMap.ker (A : Rn (m + k) →ₗ[ℝ] Rn m) with hK₀
    have hker : finrank ℝ K₀ = k := by
      have h1 := LinearMap.finrank_range_add_finrank_ker (A : Rn (m + k) →ₗ[ℝ] Rn m)
      rw [hrange, finrank_top] at h1
      simp only [finrank_euclideanSpace, Fintype.card_fin] at h1
      change m + finrank ℝ K₀ = m + k at h1
      omega
    obtain ⟨ι⟩ : Nonempty (K₀ ≃L[ℝ] Rn k) :=
      FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by simp [hker])
    let π : Rn (m + k) →L[ℝ] Rn k := (ι : K₀ →L[ℝ] Rn k).comp K₀.orthogonalProjectionOnto
    let Φ : Rn (m + k) → Rn m × Rn k := fun u => (G u, π u)
    have hΦ : ContDiff ℝ 1 Φ := hG.prodMk π.contDiff
    have hΦd : ∀ u, HasFDerivAt Φ ((fderiv ℝ G u).prod π) u := fun u =>
      ((hG.differentiable one_ne_zero u).hasFDerivAt).prodMk π.hasFDerivAt
    have hinj : Function.Injective (A.prod π) := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      have hAv : A v = 0 := congrArg Prod.fst hv
      have hπv : π v = 0 := congrArg Prod.snd hv
      have hvK : v ∈ K₀ := hAv
      have hP : K₀.orthogonalProjectionOnto v = ⟨v, hvK⟩ :=
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨v, hvK⟩
      have : ι ⟨v, hvK⟩ = 0 := by simpa [π, hP] using hπv
      have h0 : (⟨v, hvK⟩ : K₀) = 0 := by simpa using this
      simpa using congrArg Subtype.val h0
    have hdim : finrank ℝ (Rn (m + k)) = finrank ℝ (Rn m × Rn k) := by
      simp [Module.finrank_prod]
    let e' : Rn (m + k) ≃L[ℝ] Rn m × Rn k :=
      ((A.prod π : Rn (m + k) →ₗ[ℝ] Rn m × Rn k).linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
    have he' : (e' : Rn (m + k) →L[ℝ] Rn m × Rn k) = A.prod π := by ext1 v; rfl
    -- `V`: the open set where `DΦ` is invertible.
    let V : Set (Rn (m + k)) := (fderiv ℝ Φ) ⁻¹'
      range ((↑) : (Rn (m + k) ≃L[ℝ] Rn m × Rn k) → Rn (m + k) →L[ℝ] Rn m × Rn k)
    have hVo : IsOpen V := ContinuousLinearEquiv.isOpen.preimage (hΦ.continuous_fderiv one_ne_zero)
    have hu₀V : u₀ ∈ V := ⟨e', by rw [he', (hΦd u₀).fderiv]⟩
    have hΦa : ContDiffAt ℝ 1 Φ u₀ := hΦ.contDiffAt
    have hΦ'a : HasFDerivAt Φ (e' : Rn (m + k) →L[ℝ] Rn m × Rn k) u₀ := by
      rw [he']; exact hΦd u₀
    have hstrict := ContDiffAt.hasStrictFDerivAt' hΦa hΦ'a one_ne_zero
    let e := HasStrictFDerivAt.toOpenPartialHomeomorph Φ hstrict
    have hecoe : (e : Rn (m + k) → Rn m × Rn k) = Φ := rfl
    refine ⟨e.source ∩ D ∩ V, (e.open_source.inter hD).inter hVo,
      ⟨⟨HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hstrict, hu₀D⟩, hu₀V⟩, ?_⟩
    -- The slice through the chart is the image of the open set `W` under `h`.
    let W : Set (Rn k) := (fun z => (y, z)) ⁻¹' (e.target ∩ e.symm ⁻¹' (D ∩ V))
    have hWo : IsOpen W :=
      (e.isOpen_inter_preimage_symm (hD.inter hVo)).preimage (continuous_const.prodMk continuous_id)
    let h : Rn k → Rn N := fun z => ψ (e.symm (y, z))
    have hh : ContDiffOn ℝ 1 h W := by
      intro z hz
      apply ContDiffAt.contDiffWithinAt
      obtain ⟨hzt, hzD, ⟨L, hL⟩⟩ := hz
      have h1 : ContDiffAt ℝ 1 e.symm (y, z) := by
        refine e.contDiffAt_symm hzt (f₀' := L) ?_ ?_
        · rw [hL, hecoe]
          exact (hΦ.differentiable one_ne_zero _).hasFDerivAt
        · rw [hecoe]; exact hΦ.contDiffAt
      have h2 : ContDiffAt ℝ 1 ψ (e.symm (y, z)) := hψ.contDiffAt (hD.mem_nhds hzD)
      exact h2.comp z (h1.comp z (contDiffAt_const.prodMk contDiffAt_id))
    apply (himage W h hWo hh).mono
    rintro _ ⟨u, ⟨⟨⟨hus, huD⟩, huV⟩, huy⟩, rfl⟩
    have hey : e u = (y, π u) := by
      rw [hecoe]; simp only [Φ]; rw [show G u = y from huy]
    refine ⟨π u, ?_, ?_⟩
    · show (y, π u) ∈ e.target ∩ e.symm ⁻¹' (D ∩ V)
      rw [← hey]
      exact ⟨e.map_source hus, by rw [mem_preimage, e.left_inv hus]; exact ⟨huD, huV⟩⟩
    · show ψ (e.symm (y, π u)) = ψ u
      rw [← hey, e.left_inv hus]
  -- Lindelöf: countably many charts cover the regular part.
  choose O hOo hmem hrect using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable O hOo
  have hsub : ψ '' (D ∩ {u | Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y}) ⊆
      ⋃₀ ((fun i => ψ '' (O i ∩ G ⁻¹' {y})) '' T) := by
    rintro _ ⟨u, ⟨huDS, huy⟩, rfl⟩
    have hu : u ∈ ⋃ i ∈ T, O i := by
      rw [hTU]; exact mem_iUnion.2 ⟨⟨u, huDS⟩, hmem _⟩
    obtain ⟨i, hiT, hui⟩ := mem_iUnion₂.1 hu
    exact ⟨_, ⟨i, hiT, rfl⟩, ⟨u, ⟨hui, huy⟩, rfl⟩⟩
  refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion (hTc.image _) ?_).mono hsub
  rintro _ ⟨i, -, rfl⟩
  exact hrect i

/-- **`C¹` maps on open sets send `Hᵏ`-null sets to `Hᵏ`-null sets**: the critical-part step of
the slice rectifiability in Simon Ch. 3, Remark 2.10(2) (`chapter-03.txt` lines 437–442). Each
`u ∈ D` has an open `t u ∋ u` on which `ψ` is `K u`-Lipschitz (mean value inequality); by
Lindelöf countably many `t u`, `u ∈ T`, cover `Z ⊆ D`. By Ch. 2, Thm. 1.8(i) (`chapter-02.txt`
lines 270–295, valid for non-measurable sets) `Hᵏ(ψ(Z ∩ t u)) ≤ (K u)ᵏ Hᵏ(Z ∩ t u) = 0`, and
countable subadditivity gives `Hᵏ(ψ(Z)) = 0`. No measurability of `Z` and no relation between
`k` and `n` is needed: all estimates are for outer measures. -/
theorem Submission.contDiffOn_image_euclideanHausdorff_null : ∀ (n N k : ℕ) (D Z : Set (Rn n))
    (ψ : Rn n → Rn N), IsOpen D → ContDiffOn ℝ 1 ψ D → Z ⊆ D → μHE[k] Z = 0 →
    μHE[k] (ψ '' Z) = 0 := by
  intro n N k D Z ψ hD hψ hZD hZ
  -- Step 1: each `u ∈ D` has an open `t u ∋ u` on which `ψ` is `K u`-Lipschitz.
  have hloc : ∀ u : D, ∃ K : ℝ≥0, ∃ t : Set (Rn n), IsOpen t ∧ (u : Rn n) ∈ t ∧
      LipschitzOnWith K ψ t := by
    intro u
    obtain ⟨K, t, ht, hKt⟩ := (hψ.contDiffAt (hD.mem_nhds u.2)).exists_lipschitzOnWith
    obtain ⟨t', ht't, ht'o, hut'⟩ := mem_nhds_iff.mp ht
    exact ⟨K, t', ht'o, hut', hKt.mono ht't⟩
  choose K t ht hut hKt using hloc
  -- Step 2 (Lindelöf): countably many `t u`, `u ∈ T`, cover `Z ⊆ D`.
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable t ht
  have hcover : Z ⊆ ⋃ i ∈ T, t i := by
    intro z hz
    rw [hTU]
    exact mem_iUnion.2 ⟨⟨z, hZD hz⟩, hut _⟩
  have himg : ψ '' Z ⊆ ⋃ i ∈ T, ψ '' (Z ∩ t i) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, hiT, hzi⟩ := mem_iUnion₂.1 (hcover hz)
    exact mem_iUnion₂.2 ⟨i, hiT, ⟨z, ⟨hz, hzi⟩, rfl⟩⟩
  -- Steps 3–4: `Hᵏ(ψ(Z ∩ t i)) ≤ (K i)ᵏ Hᵏ(Z ∩ t i) = 0`, then countable subadditivity.
  refine measure_mono_null himg ((measure_biUnion_null_iff hTc).2 fun i _ => ?_)
  refine le_antisymm ?_ bot_le
  calc μHE[k] (ψ '' (Z ∩ t i)) ≤ (K i : ℝ≥0∞) ^ k * μHE[k] (Z ∩ t i) :=
        Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k
          ((hKt i).mono inter_subset_right)
    _ = 0 := by rw [measure_mono_null inter_subset_left hZ, mul_zero]

/-- **Fine covers with small weighted image volume give `Hᵏ`-null slices** (the Fatou covering
criterion behind Simon Ch. 2, p. 66, the consequence of (6.3) stated before 6.4,
`chapter-02.txt` lines 1476–1478). Let `k > 0` and let `S ⊆ ℝⁿ` and `G : ℝⁿ → ℝᵐ` be arbitrary.
If for every `ε > 0` some countable cover `(Tᵢ)` of `S` has `diam Tᵢ ≤ ε` and
`∑ᵢ (diam Tᵢ)ᵏ Lᵐ(G(Tᵢ ∩ S)) ≤ ε`, then `Hᵏ(S ∩ G⁻¹{y}) = 0` for `Lᵐ`-a.e. `y ∈ ℝᵐ`.
With measurable hulls `Aⱼᵢ ⊇ G(Tⱼᵢ ∩ S)` of equal measure, the majorants
`gⱼ = ∑ᵢ (diam Tⱼᵢ)ᵏ 1_{Aⱼᵢ}` have `∫ gⱼ ≤ εⱼ → 0`, so `liminf gⱼ = 0` a.e. by Fatou; for such
`y` the covers `Tⱼᵢ ∩ S ∩ G⁻¹{y}` give `Hᵏ(S ∩ G⁻¹{y}) ≤ liminf gⱼ(y) = 0`. -/
theorem Submission.critSlices_ae_slice_null_of_covers : ∀ (n m k : ℕ) (S : Set (Rn n)) (G : Rn n → Rn m), 0 < k → (∀ ε : ℝ≥0∞, 0 < ε → ∃ (ι : Type) (_ : Countable ι) (T : ι → Set (Rn n)), S ⊆ ⋃ i, T i ∧ (∀ i, Metric.ediam (T i) ≤ ε) ∧ ∑' i, Metric.ediam (T i) ^ k * volume (G '' (T i ∩ S)) ≤ ε) → ∀ᵐ y ∂(volume : Measure (Rn m)), μHE[k] (S ∩ G ⁻¹' {y}) = 0 := by
  intro n m k S G hk hcov
  -- Covers at the scales `εⱼ = (j + 1)⁻¹ → 0`.
  have hεpos : ∀ j : ℕ, (0 : ℝ≥0∞) < ((j : ℝ≥0∞) + 1)⁻¹ := fun j =>
    ENNReal.inv_pos.2 (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top j, ENNReal.one_ne_top⟩)
  have hr : Tendsto (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) :=
    (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)).congr fun j => by
      simp [Nat.cast_add, Nat.cast_one]
  choose ι hι T hTcov hTdiam hTsum using fun j : ℕ => hcov _ (hεpos j)
  -- Measurable hulls `Aⱼᵢ ⊇ G(Tⱼᵢ ∩ S)` of equal measure and the majorants `gⱼ`.
  set A : ∀ j, ι j → Set (Rn m) := fun j i => toMeasurable volume (G '' (T j i ∩ S))
  set g : ℕ → Rn m → ℝ≥0∞ := fun j y => ∑' i, Metric.ediam (T j i) ^ k * (A j i).indicator 1 y
  have hterm : ∀ j i, Measurable fun y => Metric.ediam (T j i) ^ k * (A j i).indicator 1 y :=
    fun j i => measurable_const.mul (measurable_one.indicator (measurableSet_toMeasurable _ _))
  have hgm : ∀ j, Measurable (g j) := fun j => Measurable.tsum fun i => hterm j i
  have hgint : ∀ j, ∫⁻ y, g j y ≤ ((j : ℝ≥0∞) + 1)⁻¹ := by
    intro j
    calc ∫⁻ y, g j y
        = ∑' i, ∫⁻ y, Metric.ediam (T j i) ^ k * (A j i).indicator 1 y :=
          lintegral_tsum fun i => (hterm j i).aemeasurable
      _ = ∑' i, Metric.ediam (T j i) ^ k * volume (G '' (T j i ∩ S)) := by
          congr 1
          ext i
          rw [lintegral_const_mul _ (measurable_one.indicator (measurableSet_toMeasurable _ _)),
            lintegral_indicator_one (measurableSet_toMeasurable _ _), measure_toMeasurable]
      _ ≤ ((j : ℝ≥0∞) + 1)⁻¹ := hTsum j
  -- Fatou: `∫ liminf gⱼ ≤ liminf ∫ gⱼ ≤ liminf εⱼ = 0`, so `liminf gⱼ = 0` a.e.
  have hfatou : ∫⁻ y, liminf (fun j => g j y) atTop = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ y, liminf (fun j => g j y) atTop ≤ liminf (fun j => ∫⁻ y, g j y) atTop :=
          lintegral_liminf_le hgm
      _ ≤ liminf (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) atTop :=
          liminf_le_liminf (Eventually.of_forall hgint)
      _ = 0 := hr.liminf_eq
  have hae : ∀ᵐ y ∂(volume : Measure (Rn m)), liminf (fun j => g j y) atTop = 0 := by
    filter_upwards [(lintegral_eq_zero_iff (Measurable.liminf hgm)).1 hfatou] with y hy
    simpa using hy
  filter_upwards [hae] with y hy
  -- The covers `Tⱼᵢ ∩ (S ∩ G⁻¹{y})` of the slice: an empty piece contributes `0ᵏ = 0`, and a
  -- nonempty one forces `y ∈ G(Tⱼᵢ ∩ S) ⊆ Aⱼᵢ`.
  have hH : μH[(k : ℝ)] (S ∩ G ⁻¹' {y}) ≤ liminf (fun j => g j y) atTop := by
    calc μH[(k : ℝ)] (S ∩ G ⁻¹' {y})
        ≤ liminf (fun j => ∑' i, Metric.ediam (T j i ∩ (S ∩ G ⁻¹' {y})) ^ (k : ℝ)) atTop :=
          Measure.hausdorffMeasure_le_liminf_tsum (k : ℝ) (S ∩ G ⁻¹' {y}) _ hr
            (fun j i => T j i ∩ (S ∩ G ⁻¹' {y}))
            (Eventually.of_forall fun j i =>
              (Metric.ediam_mono inter_subset_left).trans (hTdiam j i))
            (Eventually.of_forall fun j u hu => by
              obtain ⟨i, hi⟩ := mem_iUnion.1 (hTcov j hu.1)
              exact mem_iUnion.2 ⟨i, hi, hu⟩)
      _ ≤ liminf (fun j => g j y) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun j => ENNReal.tsum_le_tsum fun i => ?_)
          by_cases hne : (T j i ∩ (S ∩ G ⁻¹' {y})).Nonempty
          · obtain ⟨u, huT, huS, huy⟩ := hne
            have hyA : y ∈ A j i := subset_toMeasurable _ _ ⟨u, ⟨huT, huS⟩, huy⟩
            rw [indicator_of_mem hyA, Pi.one_apply, mul_one, ENNReal.rpow_natCast]
            exact pow_le_pow_left' (Metric.ediam_mono inter_subset_left) k
          · rw [not_nonempty_iff_eq_empty.1 hne, Metric.ediam_empty,
              ENNReal.zero_rpow_of_pos (by exact_mod_cast hk)]
            exact zero_le
  have hμH : μH[(k : ℝ)] (S ∩ G ⁻¹' {y}) = 0 := le_antisymm (hH.trans hy.le) zero_le
  -- `μHE[k] = c_k • μH[k]`.
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hμH, smul_zero]

/-- **Volume of a slab intersected with a ball**: for a unit vector `ν` of `ℝᵐ`,
`Lᵐ{w : |⟨w - c, ν⟩| ≤ r, |w - c| ≤ R} ≤ 2r (2R)^{m-1}`. This is the slab estimate in a direct
covering proof that critical slices are null (Simon Ch. 2, p. 66: the consequence of 6.3 stated
before 6.4, which Simon derives from the co-area formula 6.3, whose proof he defers to [Har79],
[Fed69]). The set is empty if `r < 0` or `R < 0`, and `‖ν‖ = 1` forces `m ≥ 1`. The reflection
`ρ` of `ℝᵐ` in `(ℝ (ν - e₀))ᗮ` maps `ν` to `e₀`, so `w ↦ ρ(w - c)` maps the set into the box
`[-r, r] × [-R, R]^{m-1}`, since `⟨ρ(w - c), e₀⟩ = ⟨w - c, ν⟩` and `|x_i| ≤ |x| = |w - c|`.
Translation, `ρ` and `ofLp` preserve Lebesgue measure, and the box has volume `2r (2R)^{m-1}`. -/
theorem Submission.critSlices_slab_volume_le : ∀ (m : ℕ) (ν c : Rn m) (r R : ℝ), ‖ν‖ = 1 → volume {w : Rn m | |inner ℝ (w - c) ν| ≤ r ∧ ‖w - c‖ ≤ R} ≤ ENNReal.ofReal (2 * r * (2 * R) ^ (m - 1)) := by
  intro m ν c r R hν
  -- Step 1: for `r < 0` or `R < 0` the set is empty.
  by_cases hr : r < 0
  · have hempty : {w : Rn m | |inner ℝ (w - c) ν| ≤ r ∧ ‖w - c‖ ≤ R} = ∅ := by
      ext w
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h
      exact absurd ((abs_nonneg _).trans h) (not_le.2 hr)
    rw [hempty, measure_empty]
    positivity
  by_cases hR : R < 0
  · have hempty : {w : Rn m | |inner ℝ (w - c) ν| ≤ r ∧ ‖w - c‖ ≤ R} = ∅ := by
      ext w
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro _ h
      exact absurd ((norm_nonneg _).trans h) (not_le.2 hR)
    rw [hempty, measure_empty]
    positivity
  push Not at hr hR
  -- Step 2: `‖ν‖ = 1` rules out `m = 0`.
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
    rcases m with _ | m'
    · exfalso
      have h0 : ν = 0 := Subsingleton.elim _ _
      rw [h0, norm_zero] at hν
      exact zero_ne_one hν
    · exact ⟨m', rfl⟩
  -- Step 3: the reflection `ρ` in `(ℝ (ν - e₀))ᗮ` satisfies `ρ ν = e₀`.
  set e₀ : Rn (m' + 1) := EuclideanSpace.single 0 1 with he₀
  have he₀n : ‖e₀‖ = 1 := by simp [he₀]
  set ρ : Rn (m' + 1) ≃ₗᵢ[ℝ] Rn (m' + 1) := (ℝ ∙ (ν - e₀))ᗮ.reflection with hρ
  have hρν : ρ ν = e₀ := Submodule.reflection_sub (hν.trans he₀n.symm)
  -- Step 4: `w ↦ ofLp (ρ (w - c))` maps the set into the box `Icc a b`.
  set a : Fin (m' + 1) → ℝ := fun i ↦ if i = 0 then -r else -R with ha
  set b : Fin (m' + 1) → ℝ := fun i ↦ if i = 0 then r else R with hb
  have hsub : {w : Rn (m' + 1) | |inner ℝ (w - c) ν| ≤ r ∧ ‖w - c‖ ≤ R} ⊆
      (WithLp.ofLp ∘ ρ ∘ fun w ↦ w - c) ⁻¹' Icc a b := by
    intro w hw
    obtain ⟨h1, h2⟩ := hw
    simp only [mem_preimage, Function.comp_apply, mem_Icc]
    set x := ρ (w - c) with hx
    have hx0 : x.ofLp 0 = inner ℝ (w - c) ν := by
      have h : inner ℝ x e₀ = x.ofLp 0 := by
        rw [he₀, EuclideanSpace.inner_single_right]
        simp
      rw [← h, ← hρν, hx, LinearIsometryEquiv.inner_map_map]
    have hxn : ‖x‖ = ‖w - c‖ := LinearIsometryEquiv.norm_map _ _
    have hcoord : ∀ i, |x.ofLp i| ≤ R := by
      intro i
      have := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at this
      exact this.trans (hxn ▸ h2)
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · by_cases hi : i = 0
      · subst hi
        simp only [ha, ite_true]
        rw [hx0]
        exact (abs_le.1 h1).1
      · simp only [ha, hi, ite_false]
        exact (abs_le.1 (hcoord i)).1
    · by_cases hi : i = 0
      · subst hi
        simp only [hb, ite_true]
        rw [hx0]
        exact (abs_le.1 h1).2
      · simp only [hb, hi, ite_false]
        exact (abs_le.1 (hcoord i)).2
  -- Step 5: translation, `ρ` and `ofLp` preserve Lebesgue measure.
  have hmp : MeasurePreserving (WithLp.ofLp ∘ ρ ∘ fun w : Rn (m' + 1) ↦ w - c) volume volume :=
    (PiLp.volume_preserving_ofLp (Fin (m' + 1))).comp
      (ρ.measurePreserving.comp (measurePreserving_sub_right volume c))
  -- Steps 6–7: the box has volume `2r (2R)^{m'}`; conclude by monotonicity.
  calc volume {w : Rn (m' + 1) | |inner ℝ (w - c) ν| ≤ r ∧ ‖w - c‖ ≤ R}
      ≤ volume ((WithLp.ofLp ∘ ρ ∘ fun w ↦ w - c) ⁻¹' Icc a b) := measure_mono hsub
    _ = volume (Icc a b) := hmp.measure_preimage measurableSet_Icc.nullMeasurableSet
    _ = ∏ i, ENNReal.ofReal (b i - a i) := Real.volume_Icc_pi
    _ = ENNReal.ofReal (2 * r * (2 * R) ^ (m' + 1 - 1)) := by
      rw [Fin.prod_univ_succ]
      simp only [ha, hb, ite_true, Fin.succ_ne_zero, ite_false, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
      rw [ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_pow (by linarith)]
      congr 2 <;> ring

/-- **Images under a nearly degenerate derivative lie in a thin slab.** This is the step "the
image of a critical subcube lies in a thin slab" of the covering proof that critical slices are
null (Simon Ch. 2, p. 66, the consequence of 6.3, `chapter-02.txt` lines 1476–1478; Simon gives
no proof). Here it is stated for a convex `S` of radius `d` about `u₀`. Since `P` is not
surjective, some unit `ν` is orthogonal to `range P`. The mean value inequality for `G - P` gives
`G(u) - G(u₀) = P(u - u₀) + e` with `|e| ≤ εd`. Hence `G(S)` lies in
`{w : |⟨w - G(u₀), ν⟩| ≤ εd, |w - G(u₀)| ≤ (Λ + ε)d}`, whose volume is bounded by
`Submission.critSlices_slab_volume_le`. -/
theorem Submission.critSlices_image_volume_le_of_fderiv_near : ∀ (n m : ℕ) (G : Rn n → Rn m)
    (S : Set (Rn n)) (P : Rn n →L[ℝ] Rn m) (u₀ : Rn n) (d ε Λ : ℝ), Convex ℝ S → u₀ ∈ S →
    (∀ v ∈ S, DifferentiableAt ℝ G v) → (∀ v ∈ S, ‖fderiv ℝ G v - P‖ ≤ ε) →
    (∀ v ∈ S, ‖v - u₀‖ ≤ d) → ¬ Function.Surjective P → ‖P‖ ≤ Λ →
    volume (G '' S) ≤ ENNReal.ofReal (2 * (ε * d) * (2 * ((Λ + ε) * d)) ^ (m - 1)) := by
  intro n m G S P u₀ d ε Λ hS hu₀ hdiff hnear hd hP hΛ
  -- `u₀ ∈ S` gives `ε ≥ ‖DG(u₀) - P‖ ≥ 0`.
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hnear u₀ hu₀)
  -- A unit normal `ν` to the proper subspace `range P`: `(range P)ᗮ ≠ 0` as `range P ≠ ℝᵐ`.
  obtain ⟨ν, hν, hPν⟩ : ∃ ν : Rn m, ‖ν‖ = 1 ∧ ∀ x, inner ℝ (P x) ν = 0 := by
    have hV : LinearMap.range (P : Rn n →ₗ[ℝ] Rn m) ≠ ⊤ := fun h ↦
      hP fun y ↦ LinearMap.mem_range.1 (h ▸ Submodule.mem_top)
    obtain ⟨ν₀, hν₀, hν₀0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (mt Submodule.orthogonal_eq_bot_iff.1 hV)
    refine ⟨‖ν₀‖⁻¹ • ν₀, ?_, fun x ↦ ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hν₀0)]
    · have h0 : inner ℝ (P x) ν₀ = 0 :=
        (Submodule.mem_orthogonal _ _).1 hν₀ (P x) (LinearMap.mem_range_self _ x)
      rw [inner_smul_right, h0, mul_zero]
  -- `G(S)` lies in the slab of half-width `εd` normal to `ν`, cut off by the closed ball of
  -- radius `(Λ + ε)d`, both about `G(u₀)`.
  have hsub : G '' S ⊆
      {w : Rn m | |inner ℝ (w - G u₀) ν| ≤ ε * d ∧ ‖w - G u₀‖ ≤ (Λ + ε) * d} := by
    rintro _ ⟨u, hu, rfl⟩
    -- Mean value inequality for `G - P` on the convex `S`: `|e| ≤ ε|u - u₀| ≤ εd`.
    set e := G u - G u₀ - P (u - u₀) with he_def
    have he : ‖e‖ ≤ ε * d :=
      (hS.norm_image_sub_le_of_norm_fderiv_le' hdiff hnear hu₀ hu).trans
        (mul_le_mul_of_nonneg_left (hd u hu) hε)
    have hw : G u - G u₀ = P (u - u₀) + e := by
      rw [he_def]
      abel
    refine ⟨?_, ?_⟩
    · -- `⟨w, ν⟩ = ⟨e, ν⟩` because `ν ⊥ range P`; then Cauchy–Schwarz.
      rw [hw, inner_add_left, hPν, zero_add]
      calc |inner ℝ e ν| ≤ ‖e‖ * ‖ν‖ := abs_real_inner_le_norm e ν
        _ = ‖e‖ := by rw [hν, mul_one]
        _ ≤ ε * d := he
    · -- `|w| ≤ ‖P‖ |u - u₀| + |e| ≤ Λd + εd`.
      rw [hw]
      calc ‖P (u - u₀) + e‖ ≤ ‖P (u - u₀)‖ + ‖e‖ := norm_add_le _ _
        _ ≤ Λ * d + ε * d := add_le_add ((P.le_opNorm _).trans
            (mul_le_mul hΛ (hd u hu) (norm_nonneg _) ((norm_nonneg _).trans hΛ))) he
        _ = (Λ + ε) * d := by ring
  calc volume (G '' S)
      ≤ volume {w : Rn m | |inner ℝ (w - G u₀) ν| ≤ ε * d ∧ ‖w - G u₀‖ ≤ (Λ + ε) * d} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (2 * (ε * d) * (2 * ((Λ + ε) * d)) ^ (m - 1)) :=
        Submission.critSlices_slab_volume_le m ν (G u₀) (ε * d) ((Λ + ε) * d) hν

/-- **Subdivision of `[-R, R]ⁿ` into `Mⁿ` subcubes**: for `M > 0` and `R ≥ 0`, with side
`s = 2R/M`, the closed cubes `Q_α = {u : -R + s αᵢ ≤ uᵢ ≤ -R + s (αᵢ + 1) for all i}`,
`α : Fin n → Fin M`, are convex, lie in `closedBall 0 (√n R)`, have diameter at most `√n s` and
cover `closedBall 0 R`. This is the cube subdivision in the covering proof that critical slices
are null (Simon Ch. 2, p. 66, the consequence of (6.3) stated before 6.4). The defining
inequalities are preserved by convex combinations. Every coordinate of a point of `Q_α` lies in
`[-R, R]`, and two points of `Q_α` differ by at most `s` in every coordinate, which gives the two
norm bounds. A point `u` of `closedBall 0 R` has `|uᵢ| ≤ R`; it lies in `Q_α` for `α ≡ 0` if
`R = 0`, and for `αᵢ = min ⌊(uᵢ + R)/s⌋₊ (M - 1)` if `R > 0`. -/
theorem Submission.critSlices_cube_cover : ∀ (n M : ℕ) (R : ℝ), 0 < M → 0 ≤ R → ∃ Q : (Fin n → Fin M) → Set (Rn n), (∀ α, Convex ℝ (Q α)) ∧ (∀ α, Q α ⊆ Metric.closedBall 0 (Real.sqrt n * R)) ∧ (∀ α, ∀ u ∈ Q α, ∀ v ∈ Q α, dist u v ≤ Real.sqrt n * (2 * R / M)) ∧ Metric.closedBall (0 : Rn n) R ⊆ ⋃ α, Q α := by
  intro n M R hM hR
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
  -- The side length `s = 2R/M`, so `s ≥ 0` and `s M = 2R`.
  set s : ℝ := 2 * R / M with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hM'.le
  have hsM : s * M = 2 * R := div_mul_cancel₀ _ hM'.ne'
  refine ⟨fun α ↦ {u : Rn n | ∀ i, -R + s * (α i : ℕ) ≤ u i ∧ u i ≤ -R + s * ((α i : ℕ) + 1)},
    ?_, ?_, ?_, ?_⟩
  -- Step 1: the defining inequalities are preserved by convex combinations.
  · intro α u hu v hv a b ha hb hab i
    obtain ⟨hu1, hu2⟩ := hu i
    obtain ⟨hv1, hv2⟩ := hv i
    obtain rfl : b = 1 - a := by linarith
    have hcomb : (a • u + (1 - a) • v) i = a * u i + (1 - a) * v i := rfl
    rw [hcomb]
    constructor
    · linarith [mul_le_mul_of_nonneg_left hu1 ha, mul_le_mul_of_nonneg_left hv1 hb]
    · linarith [mul_le_mul_of_nonneg_left hu2 ha, mul_le_mul_of_nonneg_left hv2 hb]
  -- Step 2: the coordinates of a point of `Q α` lie in `[-R, R]`, so its norm is at most `√n R`.
  · intro α u hu
    have hcoord : ∀ i, ‖u i‖ ≤ R := by
      intro i
      obtain ⟨h1, h2⟩ := hu i
      have hα0 : (0 : ℝ) ≤ (α i : ℕ) := Nat.cast_nonneg _
      have hαM : ((α i : ℕ) : ℝ) + 1 ≤ M := by exact_mod_cast (α i).isLt
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [mul_nonneg hs0 hα0]
      · linarith [mul_le_mul_of_nonneg_left hαM hs0]
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    calc √(∑ i, ‖u i‖ ^ 2) ≤ √(∑ _i : Fin n, R ^ 2) := by
          gcongr with i
          exact hcoord i
      _ = √n * R := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hR]
  -- Step 3: two points of `Q α` differ by at most `s` in every coordinate.
  · intro α u hu v hv
    have hcoord : ∀ i, dist (u i) (v i) ≤ s := by
      intro i
      obtain ⟨hu1, hu2⟩ := hu i
      obtain ⟨hv1, hv2⟩ := hv i
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith
    rw [EuclideanSpace.dist_eq]
    calc √(∑ i, dist (u i) (v i) ^ 2) ≤ √(∑ _i : Fin n, s ^ 2) := by
          gcongr with i
          exact hcoord i
      _ = √n * s := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hs0]
  -- Step 4: every point of `closedBall 0 R` lies in some `Q α`.
  · intro u hu
    rw [mem_closedBall_zero_iff] at hu
    have hcoord : ∀ i, |u i| ≤ R := fun i ↦ by
      have h := PiLp.norm_apply_le u i
      rw [Real.norm_eq_abs] at h
      exact h.trans hu
    rcases hR.eq_or_lt with rfl | hRpos
    · -- `R = 0`: all coordinates vanish and `s = 0`; take `α ≡ 0`.
      refine mem_iUnion.2 ⟨fun _ ↦ ⟨0, hM⟩, fun i ↦ ?_⟩
      have hui : u i = 0 := abs_nonpos_iff.1 (hcoord i)
      have hs00 : s = 0 := by rw [hs]; simp
      simp [hui, hs00]
    · -- `R > 0`: `αᵢ = min ⌊tᵢ⌋₊ (M - 1)` with `tᵢ = (uᵢ + R)/s ∈ [0, M]`.
      have hspos : 0 < s := div_pos (by linarith) hM'
      obtain ⟨t, ht⟩ : ∃ t : Fin n → ℝ, ∀ i, t i = (u i + R) / s := ⟨_, fun _ ↦ rfl⟩
      have ht0 : ∀ i, 0 ≤ t i := fun i ↦ by
        rw [ht i]
        exact div_nonneg (by linarith [(abs_le.1 (hcoord i)).1]) hs0
      have htM : ∀ i, t i ≤ M := fun i ↦ by
        rw [ht i, div_le_iff₀ hspos]
        linarith [(abs_le.1 (hcoord i)).2]
      have hk : ∀ i, ((min ⌊t i⌋₊ (M - 1) : ℕ) : ℝ) ≤ t i ∧
          t i ≤ ((min ⌊t i⌋₊ (M - 1) : ℕ) : ℝ) + 1 := by
        intro i
        refine ⟨(Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le (ht0 i)), ?_⟩
        rcases le_total ⌊t i⌋₊ (M - 1) with hle | hle
        · rw [min_eq_left hle]
          exact (Nat.lt_floor_add_one (t i)).le
        · rw [min_eq_right hle, Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hM.ne'), Nat.cast_one,
            sub_add_cancel]
          exact htM i
      refine mem_iUnion.2 ⟨fun i ↦ ⟨min ⌊t i⌋₊ (M - 1), by omega⟩, fun i ↦ ?_⟩
      obtain ⟨hk1, hk2⟩ := hk i
      have hut : u i = -R + s * t i := by
        rw [ht i, mul_div_cancel₀ _ hspos.ne']
        ring
      show -R + s * ((min ⌊t i⌋₊ (M - 1) : ℕ) : ℝ) ≤ u i ∧
        u i ≤ -R + s * (((min ⌊t i⌋₊ (M - 1) : ℕ) : ℝ) + 1)
      rw [hut]
      exact ⟨by linarith [mul_le_mul_of_nonneg_left hk1 hs0],
        by linarith [mul_le_mul_of_nonneg_left hk2 hs0]⟩

/-- **`C¹` critical slices are `Hᵏ`-null** (Simon Ch. 2, p. 66: the consequence of the co-area
formula 6.3 stated before Theorem 6.4, `chapter-02.txt` lines 1476–1478, whose proof Simon leaves
to [Har79]/[Fed69]). Let `G : ℝ^{m+k} → ℝᵐ` be `C¹`, `k > 0` and `C = {u : DG(u) not surjective}`.
Then `Hᵏ(C ∩ G⁻¹{y}) = 0` for `Lᵐ`-a.e. `y`. If `m = 0` then `C = ∅`. Otherwise, by the fine-cover
criterion, it suffices to treat `C ∩ B̄_R` for `R ∈ ℕ`. Given `ε > 0`, let `Λ` bound `‖DG‖` on
`K = B̄_{√n R}` (`n = m + k`), let `η > 0` be small and `δ > 0` such that
`‖DG(v) - DG(v')‖ ≤ η` for `v, v' ∈ K` with `|v - v'| ≤ δ`, and subdivide `[-R, R]ⁿ` into `Mⁿ`
convex cubes `Q` of diameter `d ≤ min(δ, ε)`. If `Q` meets `C` at `u₀`, then `G(Q)` lies in a slab
normal to `range DG(u₀)`, so `Lᵐ(G(Q)) ≤ 2ηd (2(Λ + η)d)^{m-1}`. As `Md = 2√n R`, the cover has
`Σ_Q (diam Q)ᵏ Lᵐ(G(Q ∩ C)) ≤ (2√n R)ⁿ 2ᵐ (Λ + 1)^{m-1} η ≤ ε`. -/
theorem Submission.c1_critical_slices_null : ∀ (m k : ℕ) (G : Rn (m + k) → Rn m), 0 < k →
    ContDiff ℝ 1 G → ∀ᵐ y ∂(volume : Measure (Rn m)),
      μHE[k] ({u | ¬ Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y}) = 0 := by
  intro m k G hk hG
  -- `m = 0`: every linear map into `ℝ⁰` is surjective, so the critical set is empty.
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hC : {u : Rn (0 + k) | ¬ Function.Surjective (fderiv ℝ G u)} = ∅ := by
      ext u
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_not]
      exact fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
    filter_upwards with y
    simp [hC]
  set C := {u : Rn (m + k) | ¬ Function.Surjective (fderiv ℝ G u)} with hCdef
  have hdiff : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  -- `m ≥ 1`: by the fine-cover criterion, each `C ∩ B̄_R` (`R ∈ ℕ`) has `Hᵏ`-null slices over
  -- `Lᵐ`-a.e. `y`.
  have key : ∀ R : ℕ, ∀ᵐ y ∂(volume : Measure (Rn m)),
      μHE[k] ((C ∩ Metric.closedBall 0 (R : ℝ)) ∩ G ⁻¹' {y}) = 0 := by
    intro R
    refine Submission.critSlices_ae_slice_null_of_covers (m + k) m k
      (C ∩ Metric.closedBall 0 (R : ℝ)) G hk fun ε hε ↦ ?_
    -- Constants: `0 < e` with `e ≤ ε`; a bound `Λ ≥ 0` of `‖DG‖` on the compact `K = B̄_{√n R}`;
    -- the tolerance `η ∈ (0, 1]` with `A₀ η ≤ e`; the modulus `δ > 0` of uniform continuity of
    -- `DG` on `K` for `η`; and `M ∈ ℕ` with cube diameter `d = √n (2R / M) ≤ min(δ, e)`.
    obtain ⟨e, he0, he⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e ≤ ε := by
      obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
      exact ⟨r, ENNReal.ofReal_pos.1 hr, hrε.le⟩
    set K := Metric.closedBall (0 : Rn (m + k)) (Real.sqrt ((m + k : ℕ) : ℝ) * R) with hKdef
    have hK : IsCompact K := isCompact_closedBall _ _
    obtain ⟨Λ₀, hΛ₀⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    set Λ : ℝ := max Λ₀ 0 with hΛdef
    have hΛ : ∀ x ∈ K, ‖fderiv ℝ G x‖ ≤ Λ := fun x hx ↦ (hΛ₀ x hx).trans (le_max_left _ _)
    have hΛ0 : 0 ≤ Λ := le_max_right _ _
    set A₀ : ℝ := (2 * Real.sqrt ((m + k : ℕ) : ℝ) * R) ^ (m + k) * 2 ^ m * (Λ + 1) ^ (m - 1)
      with hA₀def
    have hA₀ : 0 ≤ A₀ := by positivity
    set η : ℝ := min 1 (e / (A₀ + 1)) with hηdef
    have hη0 : 0 < η := lt_min one_pos (div_pos he0 (by linarith))
    have hη1 : η ≤ 1 := min_le_left _ _
    have hηA : A₀ * η ≤ e := by
      have h1 : A₀ * η ≤ A₀ * (e / (A₀ + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hA₀
      have h2 : A₀ * (e / (A₀ + 1)) ≤ e := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff_le.1
      (hK.uniformContinuousOn_of_continuous hcont.continuousOn) η hη0
    set ρ : ℝ := min δ e with hρdef
    have hρ0 : 0 < ρ := lt_min hδ0 he0
    obtain ⟨M, hM⟩ := exists_nat_gt (2 * Real.sqrt ((m + k : ℕ) : ℝ) * R / ρ)
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    have hMpos' : (0 : ℝ) < M := lt_of_le_of_lt (by positivity) hM
    have hMpos : 0 < M := by exact_mod_cast hMpos'
    set d : ℝ := Real.sqrt ((m + k : ℕ) : ℝ) * (2 * R / M) with hddef
    have hd0 : 0 ≤ d := by positivity
    have hdρ : d ≤ ρ := by
      have h := (div_lt_iff₀ hρ0).1 hM
      rw [hddef, mul_div_assoc', div_le_iff₀ hMpos']
      nlinarith
    have hdδ : d ≤ δ := hdρ.trans (min_le_left _ _)
    have hde : d ≤ e := hdρ.trans (min_le_right _ _)
    -- The cover: the `Mⁿ` convex cubes `Q α ⊆ K` of diameter `≤ d ≤ ε` covering `B̄_R`.
    obtain ⟨Q, hQconv, hQK, hQdiam, hQcov⟩ :=
      Submission.critSlices_cube_cover (m + k) M R hMpos hR0
    have hdiamQ : ∀ α, Metric.ediam (Q α) ≤ ENNReal.ofReal d := fun α ↦
      Metric.ediam_le fun u hu v hv ↦ by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (hQdiam α u hu v hv)
    refine ⟨Fin (m + k) → Fin M, inferInstance, Q, inter_subset_right.trans hQcov,
      fun α ↦ (hdiamQ α).trans ((ENNReal.ofReal_le_ofReal hde).trans he), ?_⟩
    rw [tsum_fintype]
    -- A cube `Q α` meeting `C` at `u₀`: `‖DG(v) - DG(u₀)‖ ≤ η` and `|v - u₀| ≤ d` on `Q α`, and
    -- `DG(u₀)` is not surjective, so `Lᵐ(G(Q α)) ≤ 2ηd (2(Λ + η)d)^{m-1}`.
    have hterm : ∀ α, Metric.ediam (Q α) ^ k *
        volume (G '' (Q α ∩ (C ∩ Metric.closedBall 0 (R : ℝ)))) ≤
        ENNReal.ofReal (d ^ k * (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m - 1))) := by
      intro α
      by_cases hne : (Q α ∩ (C ∩ Metric.closedBall 0 (R : ℝ))).Nonempty
      · obtain ⟨u₀, hu₀Q, hu₀C, -⟩ := hne
        have hu₀K : u₀ ∈ K := hQK α hu₀Q
        have hvol := Submission.critSlices_image_volume_le_of_fderiv_near (m + k) m G (Q α)
          (fderiv ℝ G u₀) u₀ d η Λ (hQconv α) hu₀Q (fun v _ ↦ hdiff v)
          (fun v hv ↦ by
            have h := hδ v (hQK α hv) u₀ hu₀K ((hQdiam α v hv u₀ hu₀Q).trans hdδ)
            rwa [dist_eq_norm] at h)
          (fun v hv ↦ by
            rw [← dist_eq_norm]
            exact hQdiam α v hv u₀ hu₀Q)
          hu₀C (hΛ u₀ hu₀K)
        calc Metric.ediam (Q α) ^ k * volume (G '' (Q α ∩ (C ∩ Metric.closedBall 0 (R : ℝ))))
            ≤ ENNReal.ofReal d ^ k * volume (G '' Q α) :=
              mul_le_mul' (pow_le_pow_left' (hdiamQ α) k)
                (measure_mono (image_mono inter_subset_left))
          _ ≤ ENNReal.ofReal d ^ k *
              ENNReal.ofReal (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m - 1)) :=
              mul_le_mul' le_rfl hvol
          _ = ENNReal.ofReal (d ^ k * (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m - 1))) := by
              rw [ENNReal.ofReal_mul (pow_nonneg hd0 k), ENNReal.ofReal_pow hd0]
      · rw [not_nonempty_iff_eq_empty.1 hne, image_empty, measure_empty, mul_zero]
        positivity
    -- Summing over the `Mⁿ` cubes: `Md = 2√n R`, `n = m + k`, `m ≥ 1` and `η ≤ 1` give
    -- `Σ ≤ (2√n R)ⁿ 2ᵐ (Λ + η)^{m-1} η ≤ A₀ η ≤ e ≤ ε`.
    calc ∑ α, Metric.ediam (Q α) ^ k * volume (G '' (Q α ∩ (C ∩ Metric.closedBall 0 (R : ℝ))))
        ≤ ∑ _α : Fin (m + k) → Fin M,
            ENNReal.ofReal (d ^ k * (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m - 1))) :=
          Finset.sum_le_sum fun α _ ↦ hterm α
      _ = ENNReal.ofReal ((M : ℝ) ^ (m + k) *
            (d ^ k * (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m - 1)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (M : ℝ) ^ (m + k)),
            ← Nat.cast_pow, ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal e := by
          apply ENNReal.ofReal_le_ofReal
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
          have hMd : (M : ℝ) * d = 2 * Real.sqrt ((m' + 1 + k : ℕ) : ℝ) * R := by
            rw [hddef]
            field_simp
          have hpow : (Λ + η) ^ (m' + 1 - 1) ≤ (Λ + 1) ^ (m' + 1 - 1) :=
            pow_le_pow_left₀ (by linarith) (by linarith) _
          have hid : (M : ℝ) ^ (m' + 1 + k) *
              (d ^ k * (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m' + 1 - 1))) =
              ((M : ℝ) * d) ^ (m' + 1 + k) * 2 ^ (m' + 1) * (Λ + η) ^ (m' + 1 - 1) * η := by
            simp only [Nat.add_sub_cancel, mul_pow]
            ring
          rw [hid, hMd]
          calc (2 * Real.sqrt ((m' + 1 + k : ℕ) : ℝ) * R) ^ (m' + 1 + k) * 2 ^ (m' + 1) *
                (Λ + η) ^ (m' + 1 - 1) * η
              ≤ (2 * Real.sqrt ((m' + 1 + k : ℕ) : ℝ) * R) ^ (m' + 1 + k) * 2 ^ (m' + 1) *
                (Λ + 1) ^ (m' + 1 - 1) * η := by gcongr
            _ = A₀ * η := by rw [hA₀def]
            _ ≤ e := hηA
      _ ≤ ε := he
  -- `C ∩ G⁻¹{y} ⊆ ⋃_R (C ∩ B̄_R) ∩ G⁻¹{y}`, a countable union of `Hᵏ`-null sets for a.e. `y`.
  filter_upwards [ae_all_iff.2 key] with y hy
  refine measure_mono_null (fun u hu ↦ ?_) (measure_iUnion_null hy)
  obtain ⟨R, hR⟩ := exists_nat_ge ‖u‖
  exact mem_iUnion.2 ⟨R, ⟨hu.1, mem_closedBall_zero_iff.2 hR⟩, hu.2⟩

/-- **`normDet` of an adjoint** (Simon Ch. 2, §6, co-area formula for linear maps,
`chapter-02.txt` lines 1424–1461, and Ch. 3 (2.7), `chapter-03.txt` lines 412–419): for a linear
map `P : X → Y` of finite-dimensional real inner product spaces, if `P` is surjective then
`normDet P* = normDet (P ∘ ι)` with `ι` the inclusion of `(ker P)ᗮ`, and otherwise
`normDet P* = 0`. The horizontal map `h = P ∘ ι` is an isomorphism, `P*` corestricts to `h*`
(as `range P* = (ker P)ᗮ`), and in orthonormal bases with a common index the matrix of `h*` is
the transpose of that of `h`. If `P` is not surjective, `ker P* = (range P)ᗮ ≠ 0`. -/
theorem Submission.coarea_normDet_adjoint_eq_horizontal : ∀ {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y] (P : X →ₗ[ℝ] Y), (Function.Surjective P → (LinearMap.adjoint P).normDet = (P ∘ₗ (LinearMap.ker P)ᗮ.subtype).normDet) ∧ (¬ Function.Surjective P → (LinearMap.adjoint P).normDet = 0) := by
  intro X Y _ _ _ _ _ _ P
  refine ⟨fun hP => ?_, fun hP => ?_⟩
  · set H := (LinearMap.ker P)ᗮ
    set h : H →ₗ[ℝ] Y := P ∘ₗ H.subtype with hh
    -- `h` is injective, as `ker P ⊓ (ker P)ᗮ = ⊥`.
    have hinj : Function.Injective h := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro u hu
      have hz : (u : X) ∈ LinearMap.ker P ⊓ H := ⟨hu, u.property⟩
      rw [Submodule.inf_orthogonal_eq_bot] at hz
      exact (Submodule.mem_bot ℝ).mpr (Subtype.ext ((Submodule.mem_bot ℝ).mp hz))
    -- `h` is surjective: `P x = h (x - π x)` with `π` the orthogonal projection onto `ker P`.
    have hsurj : Function.Surjective h := by
      intro y
      obtain ⟨x, rfl⟩ := hP y
      refine ⟨⟨x - (LinearMap.ker P).starProjection x,
        Submodule.sub_starProjection_mem_orthogonal x⟩, ?_⟩
      simp [hh, (LinearMap.mem_ker).mp ((LinearMap.ker P).starProjection_apply_mem x)]
    have hd : finrank ℝ H = finrank ℝ Y := (LinearEquiv.ofBijective h ⟨hinj, hsurj⟩).finrank_eq
    -- `P*` takes values in `H = (ker P)ᗮ = range P*`, and its corestriction to `H` is `h*`.
    have hm : ∀ y, LinearMap.adjoint P y ∈ H := by
      intro y
      rw [show H = LinearMap.range (LinearMap.adjoint P) from LinearMap.orthogonal_ker P]
      exact ⟨y, rfl⟩
    have ha : (LinearMap.adjoint P).codRestrict H hm = LinearMap.adjoint h := by
      apply (LinearMap.eq_adjoint_iff _ _).mpr
      intro y u
      exact LinearMap.adjoint_inner_left P (u : X) y
    rw [← LinearMap.normDet_codRestrict hm, ha]
    -- In orthonormal bases indexed by the same `Fin d`, the matrix of `h*` is `Mᴴ = Mᵀ`.
    classical
    let bH := stdOrthonormalBasis ℝ H
    let bY := (stdOrthonormalBasis ℝ Y).reindex (finCongr hd.symm)
    rw [(LinearMap.adjoint h).normDet_eq_norm_det_toMatrix bY bH,
      h.normDet_eq_norm_det_toMatrix bH bY, LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose]
    simp
  · -- `ker P* = (range P)ᗮ ≠ ⊥`, since `range P ≠ ⊤`.
    rw [LinearMap.normDet_eq_zero_iff_ker_ne_bot, ← LinearMap.orthogonal_range, ne_eq,
      Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top]
    exact hP

/-- **Block-triangular factorization of `normDet`** (step 5 of the parent proof of
`coarea_normDet_chain_rule`, the block form of `A`). Let `f : V → X` be a linear bijection,
`K ⊆ V` a subspace and `W = f(K)ᗮ`. In orthonormal bases of `V = K ⊕ Kᗮ` and `X = f(K) ⊕ W`
indexed by `Fin r ⊕ Fin s` (`r = dim K = dim f(K)`, `s = dim Kᗮ = dim W`), the matrix of `f` is
`fromBlocks M₁₁ M₁₂ 0 M₂₂`: `M₁₁` is the matrix of `f|_K : K → f(K)`, the lower-left block
vanishes because `W ⊥ f(K)`, and `M₂₂` is the matrix of `p_W ∘ f ∘ ι_{Kᗮ}` because
`⟪w, x⟫ = ⟪w, p_W x⟫` for `w ∈ W`. Hence `normDet f = |det M₁₁| · |det M₂₂|`, and
`|det M₁₁| = normDet (f ∘ ι_K)` since corestricting to `f(K)` does not change `normDet`. -/
theorem Submission.coarea_normDet_block_triangular : ∀ {V X : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] (f : V →ₗ[ℝ] X) (K : Submodule ℝ V) (W : Submodule ℝ X), Function.Bijective f → W = (K.map f)ᗮ → f.normDet = (f ∘ₗ K.subtype).normDet * ((W.orthogonalProjectionOnto : X →ₗ[ℝ] W) ∘ₗ f ∘ₗ Kᗮ.subtype).normDet := by
  intro V X _ _ _ _ _ _ f K W hf hW
  classical
  -- Notation: `F = f(K)`, so `W = Fᗮ`.
  obtain ⟨F, hF⟩ : ∃ F : Submodule ℝ X, F = K.map f := ⟨_, rfl⟩
  rw [← hF] at hW
  -- Step 1: dimensions, `dim F = dim K` and `dim W = dim Kᗮ`.
  have hr : finrank ℝ F = finrank ℝ K := by
    rw [hF]; exact (Submodule.equivMapOfInjective f hf.1 K).finrank_eq.symm
  have hVX : finrank ℝ V = finrank ℝ X := (LinearEquiv.ofBijective f hf).finrank_eq
  have e1 := Submodule.finrank_add_finrank_orthogonal K
  have e2 := Submodule.finrank_add_finrank_orthogonal F
  rw [← hW] at e2
  have hs : finrank ℝ W = finrank ℝ Kᗮ := by omega
  -- Steps 2–3: orthonormal bases of `K`, `Kᗮ`, `F`, `W`; adapted bases `β` of `V`, `γ` of `X`.
  let b₁ := stdOrthonormalBasis ℝ K
  let b₂ := stdOrthonormalBasis ℝ Kᗮ
  let c₁ : OrthonormalBasis (Fin (finrank ℝ K)) ℝ F :=
    (stdOrthonormalBasis ℝ F).reindex (finCongr hr)
  let c₂ : OrthonormalBasis (Fin (finrank ℝ Kᗮ)) ℝ W :=
    (stdOrthonormalBasis ℝ W).reindex (finCongr hs)
  let c₂' : OrthonormalBasis (Fin (finrank ℝ Kᗮ)) ℝ Fᗮ := c₂.map (LinearIsometryEquiv.ofEq _ _ hW)
  let β := (b₁.prod b₂).map K.orthogonalDecomposition.symm
  let γ := (c₁.prod c₂').map F.orthogonalDecomposition.symm
  have hβl : ∀ i, β (Sum.inl i) = (b₁ i : V) := by intro i; simp [β]
  have hβr : ∀ j, β (Sum.inr j) = (b₂ j : V) := by intro j; simp [β]
  have hγl : ∀ i, γ (Sum.inl i) = (c₁ i : X) := by intro i; simp [γ]
  have hγr : ∀ j, γ (Sum.inr j) = (c₂ j : X) := by intro j; simp [γ, c₂']
  -- The diagonal blocks: `f_K : K → F` and `g = p_W ∘ f ∘ ι_{Kᗮ} : Kᗮ → W`.
  have hmemF : ∀ k : K, f k ∈ F := fun k => hF ▸ Submodule.mem_map_of_mem k.2
  let fK : K →ₗ[ℝ] F := (f ∘ₗ K.subtype).codRestrict F (fun k => hmemF k)
  let g : Kᗮ →ₗ[ℝ] W := (W.orthogonalProjectionOnto : X →ₗ[ℝ] W) ∘ₗ f ∘ₗ Kᗮ.subtype
  -- Steps 6–7: `normDet = |det|` in square orthonormal bases; `normDet (f ∘ ι_K) = normDet f_K`.
  have h1 : (f ∘ₗ K.subtype).normDet = fK.normDet := (LinearMap.normDet_codRestrict _).symm
  rw [h1, LinearMap.normDet_eq_norm_det_toMatrix f β γ,
    LinearMap.normDet_eq_norm_det_toMatrix fK b₁ c₁, LinearMap.normDet_eq_norm_det_toMatrix g b₂ c₂,
    ← norm_mul]
  congr 1
  -- Step 4: the matrix of `f` in `β`, `γ` is block upper triangular.
  have hM : LinearMap.toMatrix β.toBasis γ.toBasis f =
      Matrix.fromBlocks (LinearMap.toMatrix b₁.toBasis c₁.toBasis fK)
        (Matrix.of fun i j => inner ℝ (c₁ i : X) (f (b₂ j))) 0
        (LinearMap.toMatrix b₂.toBasis c₂.toBasis g) := by
    ext a b
    rcases a with i | i <;> rcases b with j | j
    · -- (a) the `K → F` block is the matrix of `f_K`.
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, Matrix.fromBlocks_apply₁₁,
        hβl, hγl]
      rfl
    · -- (d) the unconstrained block `M₁₂`.
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, Matrix.fromBlocks_apply₁₂,
        hβr, hγl, Matrix.of_apply]
    · -- (b) `W ⊥ F` kills the `K → W` block.
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, Matrix.fromBlocks_apply₂₁,
        hβl, hγr, Matrix.zero_apply]
      have hmem : (c₂ i : X) ∈ Fᗮ := hW ▸ (c₂ i).2
      exact Submodule.inner_left_of_mem_orthogonal (hmemF (b₁ j)) hmem
    · -- (c) `⟪w, x⟫ = ⟪w, p_W x⟫` for `w ∈ W`: the `Kᗮ → W` block is the matrix of `g`.
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, Matrix.fromBlocks_apply₂₂,
        hβr, hγr]
      simp [g]
  -- Step 5: `det (fromBlocks M₁₁ M₁₂ 0 M₂₂) = det M₁₁ * det M₂₂`.
  rw [hM, Matrix.det_fromBlocks_zero₂₁]

/-- **Horizontal step of the `normDet` chain rule** (step 6 of the supplied proof of the `normDet`
chain rule behind the co-area Jacobian, Simon Ch. 3, (2.7)). Let `B : V → X` be bijective,
`Γ = L ∘ B`, `K = ker Γ` and `W = (ker L)ᗮ`. Since `Wᗮ = ker L`, the restriction of `Γ` to `Kᗮ`
factors as `L|_W ∘ (p_W ∘ B|_{Kᗮ})`, and `B(K) = ker L` gives `dim Kᗮ = dim W`; hence
`normDet (Γ|_{Kᗮ}) = normDet (L|_W) · normDet (p_W ∘ B|_{Kᗮ})`. -/
theorem Submission.coarea_normDet_horizontal_comp : ∀ {V X Y : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y] (B : V →ₗ[ℝ] X) (L : X →ₗ[ℝ] Y) (Γ : V →ₗ[ℝ] Y) (K : Submodule ℝ V) (W : Submodule ℝ X), Function.Bijective B → (∀ v, Γ v = L (B v)) → K = LinearMap.ker Γ → W = (LinearMap.ker L)ᗮ → (Γ ∘ₗ Kᗮ.subtype).normDet = (L ∘ₗ W.subtype).normDet * ((W.orthogonalProjectionOnto : X →ₗ[ℝ] W) ∘ₗ B ∘ₗ Kᗮ.subtype).normDet := by
  intro V X Y _ _ _ _ _ _ _ _ _ B L Γ K W hB hΓ hK hW
  -- `Wᗮ = (ker L)ᗮᗮ = ker L`.
  have hWperp : Wᗮ = LinearMap.ker L := by
    rw [hW, Submodule.orthogonal_orthogonal]
  -- `Γ ∘ ι_{Kᗮ} = (L ∘ ι_W) ∘ (p_W ∘ B ∘ ι_{Kᗮ})`, since `B u - p_W (B u) ∈ Wᗮ = ker L`.
  have hcomp : Γ ∘ₗ Kᗮ.subtype =
      (L ∘ₗ W.subtype) ∘ₗ ((W.orthogonalProjectionOnto : X →ₗ[ℝ] W) ∘ₗ B ∘ₗ Kᗮ.subtype) := by
    refine LinearMap.ext fun u ↦ ?_
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, ContinuousLinearMap.coe_coe]
    have h : B u - (W.orthogonalProjectionOnto (B u) : X) ∈ Wᗮ :=
      Submodule.sub_starProjection_mem_orthogonal (K := W) (B u)
    rw [hWperp, LinearMap.mem_ker, map_sub, sub_eq_zero] at h
    rw [hΓ]
    exact h
  -- `ker L = B(K)`, using that `B` is surjective.
  have hker : LinearMap.ker L = K.map B := by
    ext t
    constructor
    · intro ht
      obtain ⟨v, rfl⟩ := hB.2 t
      refine ⟨v, ?_, rfl⟩
      rw [SetLike.mem_coe, hK, LinearMap.mem_ker, hΓ]
      exact LinearMap.mem_ker.mp ht
    · rintro ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, hK, LinearMap.mem_ker, hΓ] at hv
      exact hv
  -- `dim Kᗮ = dim V - dim K = dim X - dim (ker L) = dim W`.
  have hfin : finrank ℝ Kᗮ = finrank ℝ W := by
    have e1 := Submodule.finrank_add_finrank_orthogonal K
    have e2 := Submodule.finrank_add_finrank_orthogonal (LinearMap.ker L)
    rw [← hW] at e2
    have e3 := (LinearEquiv.ofBijective B hB).finrank_eq
    have e4 := (Submodule.equivMapOfInjective B hB.1 K).finrank_eq
    rw [← hker] at e4
    omega
  -- Multiplicativity of `normDet` for a composition through an equal-dimensional space.
  rw [hcomp]
  exact LinearMap.normDet_comp_of_finrank_eq _ _ hfin

/-- **Chain rule for the co-area factor** (Simon Ch. 3, (2.7)–(2.8), `chapter-03.txt`
lines 412–428, where `J^{M*}_f` is reduced to the `C¹` case along charts): let `A : ℝⁿ → ℝᴺ` be
injective with range `T`, `L : T → ℝᵐ` linear and `Γ = L ∘ A`. Then
`normDet L* · normDet A = normDet (A ∘ ι_{ker Γ}) · normDet Γ*`.
The corestriction `A' : ℝⁿ → T` of `A` is bijective with the same `normDet`, `Γ = L ∘ A'` and
`range L = range Γ`. If `Γ` is not surjective, both adjoints have `normDet` zero
(`Submission.coarea_normDet_adjoint_eq_horizontal`). Otherwise `normDet P* = normDet (P ∘ ι)` for
the inclusion `ι` of `(ker P)ᗮ`, `P = L, Γ`; `ker L = A'(K)` for `K = ker Γ`, and with
`W = (ker L)ᗮ`, `g = p_W ∘ A' ∘ ι_{Kᗮ}`:
`normDet A' = normDet (A' ∘ ι_K) · normDet g` (`Submission.coarea_normDet_block_triangular`) and
`normDet (Γ ∘ ι_{Kᗮ}) = normDet (L ∘ ι_W) · normDet g`
(`Submission.coarea_normDet_horizontal_comp`). -/
theorem Submission.coarea_normDet_chain_rule : ∀ (n N m : ℕ) (T : Submodule ℝ (Rn N))
    (A : Rn n →ₗ[ℝ] Rn N) (L : T →ₗ[ℝ] Rn m) (Γ : Rn n →ₗ[ℝ] Rn m), Function.Injective A →
    LinearMap.range A = T → (∀ (v : Rn n) (hv : A v ∈ T), Γ v = L ⟨A v, hv⟩) →
    (LinearMap.adjoint L).normDet * A.normDet =
      (A ∘ₗ (LinearMap.ker Γ).subtype).normDet * (LinearMap.adjoint Γ).normDet := by
  intro n N m T A L Γ hA hT hΓ
  -- Step 1(i): `A` corestricts to a bijection `A' : ℝⁿ → T` with `Γ = L ∘ A'`; corestricting
  -- does not change `normDet`.
  have hmem : ∀ v, A v ∈ T := fun v ↦ hT ▸ LinearMap.mem_range_self A v
  obtain ⟨A', hA'⟩ : ∃ A' : Rn n →ₗ[ℝ] T, A' = A.codRestrict T hmem := ⟨_, rfl⟩
  have hA'v : ∀ v, (A' v : Rn N) = A v := fun v ↦ by rw [hA']; rfl
  have hbij : Function.Bijective A' := by
    refine ⟨fun v w h ↦ hA (by rw [← hA'v, ← hA'v, h]), ?_⟩
    rintro ⟨t, ht⟩
    obtain ⟨v, rfl⟩ : t ∈ LinearMap.range A := hT ▸ ht
    exact ⟨v, Subtype.ext (hA'v v)⟩
  have hΓA' : ∀ v, Γ v = L (A' v) := fun v ↦ by
    rw [hΓ v (hmem v)]
    exact congrArg L (Subtype.ext (hA'v v).symm)
  have hnA : A.normDet = A'.normDet := by
    rw [hA', LinearMap.normDet_codRestrict]
  obtain ⟨K, hK⟩ : ∃ K : Submodule ℝ (Rn n), K = LinearMap.ker Γ := ⟨_, rfl⟩
  rw [← hK]
  have hnAK : (A ∘ₗ K.subtype).normDet = (A' ∘ₗ K.subtype).normDet := by
    have hKT : ∀ k : K, (A ∘ₗ K.subtype) k ∈ T := fun k ↦ hmem k
    have h : A' ∘ₗ K.subtype = (A ∘ₗ K.subtype).codRestrict T hKT :=
      LinearMap.ext fun k ↦ Subtype.ext (hA'v k)
    rw [h, LinearMap.normDet_codRestrict]
  -- Step 2: `range L = range Γ`, since `A'` is onto `T`; so `L` is onto iff `Γ` is.
  by_cases hsurj : Function.Surjective Γ
  · -- Step 4: `normDet P* = normDet (P ∘ ι_{(ker P)ᗮ})` for `P = L, Γ`, and `ker L = A'(K)`.
    have hLsurj : Function.Surjective L := fun y ↦ by
      obtain ⟨v, hv⟩ := hsurj y
      exact ⟨A' v, (hΓA' v).symm.trans hv⟩
    rw [(Submission.coarea_normDet_adjoint_eq_horizontal L).1 hLsurj,
      (Submission.coarea_normDet_adjoint_eq_horizontal Γ).1 hsurj, ← hK]
    have hker : LinearMap.ker L = K.map A' := by
      rw [hK, show Γ = L ∘ₗ A' from LinearMap.ext hΓA', LinearMap.ker_comp,
        Submodule.map_comap_eq_of_surjective hbij.2]
    obtain ⟨W, hW⟩ : ∃ W : Submodule ℝ T, W = (LinearMap.ker L)ᗮ := ⟨_, rfl⟩
    rw [← hW]
    -- Step 5: `A'` is block triangular along `K ⊕ Kᗮ → A'(K) ⊕ W`.
    have hblock := Submission.coarea_normDet_block_triangular A' K W hbij (by rw [hW, hker])
    -- Step 6: `Γ ∘ ι_{Kᗮ} = (L ∘ ι_W) ∘ (p_W ∘ A' ∘ ι_{Kᗮ})`.
    have hstep := Submission.coarea_normDet_horizontal_comp A' L Γ K W hbij hΓA' hK hW
    -- Step 7.
    rw [hnA, hblock, hnAK, hstep]
    ring
  · -- Step 3: neither `L` nor `Γ` is onto, so both adjoints have `normDet` zero.
    have hLsurj : ¬ Function.Surjective L := fun hL ↦ hsurj fun y ↦ by
      obtain ⟨t, ht⟩ := hL y
      obtain ⟨v, rfl⟩ := hbij.2 t
      exact ⟨v, (hΓA' v).trans ht⟩
    rw [(Submission.coarea_normDet_adjoint_eq_horizontal L).2 hLsurj,
      (Submission.coarea_normDet_adjoint_eq_horizontal Γ).2 hsurj, zero_mul, mul_zero]

/-- **`C¹` co-area formula in parameter form** (Simon Ch. 2, 6.3 and 6.6, pp. 66–67, whose proof
Simon omits; [Fed69, 3.2.12, 3.2.22], Evans–Gariepy §3.4), transported by a `C¹` map `ψ` that is
injective on the open `D ⊆ ℝ^{m+k}`. Let `G : ℝ^{m+k} → ℝᵐ` be `C¹`, `K(u) = ker DG(u)` and
`J(u) = normDet(Dψ(u) ∘ ι_{K(u)}) · normDet(DG(u)*)`. Then for every Borel `B ⊆ D` and Borel
`φ ≥ 0`, `y ↦ ∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ` is `Lᵐ`-a.e. measurable and
`∫_B φ(ψ(u)) J(u) dLⁿ(u) = ∫_{ℝᵐ} ∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ dLᵐ(y)`.
Both claims are glued (Lindelöf, countable additivity) from two kinds of Borel pieces. On the
critical set `Z = {u | DG(u) not surjective}`, `J = 0`, and the slices `Z ∩ G⁻¹{y}` are `Hᵏ`-null
for `Lᵐ`-a.e. `y` (this uses `0 < k`); so both sides vanish. Each `p ∈ D ∖ Z` has an
implicit-function chart `Φ = (G, π)` with source in `D`. On that source the formula follows from
the injective area formula on the slices, the flat Jacobian identity, Tonelli on `ℝᵐ × ℝᵏ` and the
change of variables for `Φ`. -/
theorem Submission.c1_parametric_coarea_formula : ∀ (m k N : ℕ) (D : Set (Rn (m + k)))
    (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m), 0 < m → 0 < k → IsOpen D →
    ContDiffOn ℝ 1 ψ D → InjOn ψ D → ContDiff ℝ 1 G → ∀ B ⊆ D, MeasurableSet B →
    ∀ φ : Rn N → ℝ≥0∞, Measurable φ →
      AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧
        ∫⁻ u in B, φ (ψ u) * ENNReal.ofReal
            (((fderiv ℝ ψ u).toLinearMap ∘ₗ
                (LinearMap.ker (fderiv ℝ G u).toLinearMap).subtype).normDet *
              (LinearMap.adjoint (fderiv ℝ G u).toLinearMap).normDet) =
          ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume := by
  intro m k N D ψ G _hm hk hD hψ hinj hG
  -- Glue over `Z = {DG not surjective}` with the weight `w = ofReal ∘ J`.
  refine Submission.pcoarea_gluing (m + k) N m k D {u | ¬ Function.Surjective (fderiv ℝ G u)} ψ G
    (fun u ↦ ENNReal.ofReal
      (((fderiv ℝ ψ u).toLinearMap ∘ₗ (LinearMap.ker (fderiv ℝ G u).toLinearMap).subtype).normDet *
        (LinearMap.adjoint (fderiv ℝ G u).toLinearMap).normDet))
    hD hψ.continuousOn hinj hG.continuous ?_ ?_
  · -- Critical pieces: `J = 0`, and the slices of `Z` are `Hᵏ`-null for `Lᵐ`-a.e. `y`.
    exact Submission.pcoarea_critical_part m k N D ψ G hD hψ
      (Submission.c1_critical_slices_null m k G hk hG)
  · -- Regular pieces: the source of an implicit-function chart at `p ∈ D ∖ Z`, inside `D`.
    intro p hpD hpZ
    obtain ⟨Φ, hpΦ, hsrc, hΦ, hΦs, hfst⟩ :=
      Submission.pcoarea_implicit_chart m k G D p hD hpD hG (not_not.mp hpZ)
    refine ⟨Φ.source, Φ.open_source, hpΦ, fun B hB hBm φ hφ ↦ ?_⟩
    exact Submission.pcoarea_formula_on_chart m k N ψ G Φ (hψ.mono hsrc) (hinj.mono hsrc) hΦ hΦs
      hfst B (hB.trans inter_subset_right) hBm φ hφ

/-- **Level slices of a `C¹` map have countably `k`-rectifiable `C¹` images for `Lᵐ`-a.e. value**
(Simon Ch. 3, Remark 2.10(2), `chapter-03.txt` lines 439–442, via the `C¹` Sard-type Ch. 2,
Theorem 6.4, `chapter-02.txt` lines 1476–1497). With `C = {u | DG(u) not onto}`,
`ψ(D ∩ G⁻¹{y})` is the union of the regular part `ψ(D ∖ C ∩ G⁻¹{y})`, countably
`k`-rectifiable for every `y` (implicit function charts), and the critical part
`ψ(D ∩ C ∩ G⁻¹{y})`. For `Lᵐ`-a.e. `y`, `Hᵏ(C ∩ G⁻¹{y}) = 0`, and `ψ`, locally Lipschitz on `D`,
keeps it `Hᵏ`-null; an `Hᵏ`-null set is countably `k`-rectifiable. -/
theorem Submission.c1_level_slices_countablyRectifiable : ∀ (m k N : ℕ) (D : Set (Rn (m + k))) (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m), 0 < k → IsOpen D → ContDiffOn ℝ 1 ψ D → ContDiff ℝ 1 G → ∀ᵐ y ∂(volume : Measure (Rn m)), CountablyRectifiable k (ψ '' (D ∩ G ⁻¹' {y})) := by
  intro m k N D ψ G hk hD hψ hG
  -- The critical slices are `Hᵏ`-null for `Lᵐ`-a.e. `y`.
  filter_upwards [Submission.c1_critical_slices_null m k G hk hG] with y hy
  -- Split the slice into its regular part and its critical part.
  have hsplit : ψ '' (D ∩ G ⁻¹' {y}) ⊆
      ⋃₀ {ψ '' (D ∩ {u | Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y}),
        ψ '' (D ∩ ({u | ¬ Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y}))} := by
    rw [sUnion_pair]
    rintro _ ⟨u, ⟨huD, huy⟩, rfl⟩
    by_cases hu : Function.Surjective (fderiv ℝ G u)
    · exact Or.inl ⟨u, ⟨⟨huD, hu⟩, huy⟩, rfl⟩
    · exact Or.inr ⟨u, ⟨huD, hu, huy⟩, rfl⟩
  refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion
    ((countable_singleton _).insert _) ?_).mono hsplit
  rintro S (rfl | rfl)
  -- Regular part: countably `k`-rectifiable for every `y` (implicit function charts).
  · exact Submission.c1_regular_level_slice_image_countablyRectifiable m k N D ψ G y hD hψ hG
  -- Critical part: `ψ`, locally Lipschitz on `D`, keeps it `Hᵏ`-null.
  · exact Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero
      (Submission.contDiffOn_image_euclideanHausdorff_null (m + k) N k D _ ψ hD hψ
        inter_subset_left (measure_mono_null inter_subset_right hy))

/-- **Lipschitz open chart pieces** (Simon Ch. 3, Lemma 1.2 and Remark 1.3, `chapter-03.txt`
lines 25–73, for the embedded `C¹` submanifolds of Ch. 2, (4.1)). Let `U` be open, `M ⊆ U`, `f`
locally Lipschitz on `U`, and `M ⊆ N₀ ∪ ⋃ᵢ Sᵢ` with every `Sᵢ` an `n`-dimensional embedded `C¹`
submanifold. Then `M ⊆ N₀ ∪ ⋃_α ψ_α(D_α)` for countably many open `D_α ⊆ ℝⁿ` and maps `ψ_α`
that are `C¹`, injective and Lipschitz on `D_α` with injective differential, and such that
`f ∘ ψ_α` is Lipschitz on `D_α`. By Lindelöf, countably many charts cover each `Sᵢ`. Around a
parameter `u` of a point of `M`, a closed ball inside the chart domain on which the chart is
Lipschitz (`C¹` on a compact convex set) and which it maps into a ball where `f` is Lipschitz
contains a set `B ∋ u` of a fixed countable basis of `ℝⁿ`; the good pairs `(B, ψ)` are
enumerated by `ℕ`. -/
theorem Submission.submanifold_cover_lipschitz_open_charts : ∀ (n N m : ℕ) (M U N₀ : Set (Rn N)) (S : ℕ → Set (Rn N)) (f : Rn N → Rn m), IsOpen U → M ⊆ U → LocallyLipschitzOn U f → (∀ i, IsC1Submanifold n (S i)) → M ⊆ N₀ ∪ ⋃ i, S i → ∃ (D : ℕ → Set (Rn n)) (ψ : ℕ → Rn n → Rn N), (∀ α, IsOpen (D α)) ∧ (∀ α, ContDiffOn ℝ 1 (ψ α) (D α)) ∧ (∀ α, InjOn (ψ α) (D α)) ∧ (∀ α, ∃ K, LipschitzOnWith K (ψ α) (D α)) ∧ (∀ α, ∀ u ∈ D α, Function.Injective (fderiv ℝ (ψ α) u)) ∧ (∀ α, ∃ K, LipschitzOnWith K (f ∘ ψ α) (D α)) ∧ M ⊆ N₀ ∪ ⋃ α, ψ α '' D α := by
  intro n N m M U N₀ S f hU hMU hf hS hcov
  classical
  -- Step 1: a chart `(V_{i,y}, W_{i,y}, ψ_{i,y})` of `S i` at every `y ∈ S i`.
  choose! V W ψ hVo hWo hyW hψC hψinj hψim hψprop hψD using hS
  clear hψprop
  -- Step 2: by Lindelöf, the charts at countably many `y ∈ T i` cover `S i`.
  choose T hTS hTc hTW using fun i ↦
    TopologicalSpace.isOpen_biUnion_countable (S i) (W i) (fun y hy ↦ hWo i y hy)
  -- Step 3: the good pairs among `(∅, 0)` and `(B, ψ_{i,y})`, `B` in a countable basis of `ℝⁿ`.
  obtain ⟨𝔅, h𝔅c, -, h𝔅⟩ := TopologicalSpace.exists_countable_basis (Rn n)
  obtain ⟨Good, hGood⟩ : ∃ Good : Set (Rn n) × (Rn n → Rn N) → Prop, ∀ p, Good p ↔
      (IsOpen p.1 ∧ ContDiffOn ℝ 1 p.2 p.1 ∧ InjOn p.2 p.1 ∧ (∃ K, LipschitzOnWith K p.2 p.1) ∧
        (∀ u ∈ p.1, Function.Injective (fderiv ℝ p.2 u)) ∧
        ∃ K, LipschitzOnWith K (f ∘ p.2) p.1) := ⟨_, fun _ ↦ Iff.rfl⟩
  have hQc : (insert ((∅ : Set (Rn n)), (0 : Rn n → Rn N))
      (⋃ i, ⋃ y ∈ T i, (fun B ↦ (B, ψ i y)) '' 𝔅)).Countable :=
    (countable_iUnion fun i ↦ (hTc i).biUnion fun y _ ↦ h𝔅c.image _).insert _
  have hPne : {p ∈ insert ((∅ : Set (Rn n)), (0 : Rn n → Rn N))
      (⋃ i, ⋃ y ∈ T i, (fun B ↦ (B, ψ i y)) '' 𝔅) | Good p}.Nonempty :=
    ⟨(∅, 0), mem_insert _ _, (hGood _).mpr ⟨isOpen_empty, contDiffOn_empty, injOn_empty _,
      ⟨0, lipschitzOnWith_empty _ _⟩, fun _ h ↦ h.elim, ⟨0, lipschitzOnWith_empty _ _⟩⟩⟩
  obtain ⟨g, hg⟩ := (hQc.mono (sep_subset _ _)).exists_eq_range hPne
  have hgG : ∀ α, Good (g α) := by
    intro α
    have h : g α ∈ range g := mem_range_self α
    rw [← hg] at h
    exact h.2
  refine ⟨fun α ↦ (g α).1, fun α ↦ (g α).2, fun α ↦ ((hGood _).mp (hgG α)).1,
    fun α ↦ ((hGood _).mp (hgG α)).2.1, fun α ↦ ((hGood _).mp (hgG α)).2.2.1,
    fun α ↦ ((hGood _).mp (hgG α)).2.2.2.1, fun α ↦ ((hGood _).mp (hgG α)).2.2.2.2.1,
    fun α ↦ ((hGood _).mp (hgG α)).2.2.2.2.2, ?_⟩
  -- Step 4: a point `x ∈ M \ N₀` is `ψ_{i,y}(u)` for some `y ∈ T i`, `u ∈ V_{i,y}`.
  intro x hx
  rcases hcov hx with hx0 | hxS
  · exact Or.inl hx0
  right
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hxS
  have hxW : x ∈ ⋃ y ∈ T i, W i y := by
    rw [hTW]
    exact mem_biUnion hxi (hyW i x hxi)
  obtain ⟨y, hyT, hxy⟩ := mem_iUnion₂.mp hxW
  have hy : y ∈ S i := hTS i hyT
  have hxU : x ∈ U := hMU hx
  obtain ⟨u, hu, rfl⟩ : x ∈ ψ i y '' V i y := by
    rw [hψim i y hy]
    exact ⟨hxy, hxi⟩
  -- Step 5: `r = min δ₁ δ₂ / 2` has `closedBall u r ⊆ V` and `ψ(closedBall u r) ⊆ B(x, s)`,
  -- where `f` is `K`-Lipschitz on `B(x, s) ⊆ t`.
  obtain ⟨K, t, ht, hKt⟩ := hf hxU
  rw [hU.nhdsWithin_eq hxU] at ht
  obtain ⟨s, hs, hst⟩ := Metric.mem_nhds_iff.mp ht
  have hcont : ContinuousAt (ψ i y) u :=
    (hψC i y hy).continuousOn.continuousAt ((hVo i y hy).mem_nhds hu)
  obtain ⟨δ₁, hδ₁, hδ₁s⟩ := Metric.continuousAt_iff.mp hcont s hs
  obtain ⟨δ₂, hδ₂, hδ₂V⟩ := Metric.isOpen_iff.mp (hVo i y hy) u hu
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hr0 : 0 < min δ₁ δ₂ / 2 := half_pos hδ
  have hrδ : ∀ v ∈ Metric.closedBall u (min δ₁ δ₂ / 2), dist v u < δ₁ ∧ dist v u < δ₂ :=
    fun v hv ↦ lt_min_iff.mp ((Metric.mem_closedBall.mp hv).trans_lt (half_lt_self hδ))
  have hBV : Metric.closedBall u (min δ₁ δ₂ / 2) ⊆ V i y :=
    fun v hv ↦ hδ₂V (Metric.mem_ball.mpr (hrδ v hv).2)
  -- Step 6: `ψ` is Lipschitz on the compact convex ball.
  obtain ⟨L, hL⟩ := ((hψC i y hy).mono hBV).exists_lipschitzOnWith one_ne_zero
    (convex_closedBall u _) (isCompact_closedBall u _)
  -- Step 7: a basis set `u ∈ B ⊆ B(u, r)` gives a good pair `(B, ψ_{i,y})`.
  obtain ⟨B, hB𝔅, huB, hBball⟩ :=
    h𝔅.exists_subset_of_mem_open (Metric.mem_ball_self hr0) Metric.isOpen_ball
  have hBcl : B ⊆ Metric.closedBall u (min δ₁ δ₂ / 2) :=
    hBball.trans Metric.ball_subset_closedBall
  have hBP : (B, ψ i y) ∈ {p ∈ insert ((∅ : Set (Rn n)), (0 : Rn n → Rn N))
      (⋃ i, ⋃ y ∈ T i, (fun B ↦ (B, ψ i y)) '' 𝔅) | Good p} := by
    refine ⟨mem_insert_of_mem _ (mem_iUnion.mpr ⟨i, mem_iUnion₂.mpr ⟨y, hyT, B, hB𝔅, rfl⟩⟩),
      (hGood _).mpr ⟨h𝔅.isOpen hB𝔅, (hψC i y hy).mono (hBcl.trans hBV),
        (hψinj i y hy).mono (hBcl.trans hBV), ⟨L, hL.mono hBcl⟩,
        fun v hv ↦ hψD i y hy v (hBV (hBcl hv)), ⟨K * L, hKt.comp (hL.mono hBcl) ?_⟩⟩⟩
    intro v hv
    exact hst (Metric.mem_ball.mpr (hδ₁s (hrδ v (hBcl hv)).1))
  -- Step 8: `(B, ψ_{i,y})` is some `(D_α, ψ_α)`, and `x = ψ_α(u) ∈ ψ_α(D_α)`.
  rw [hg] at hBP
  obtain ⟨α, hα⟩ := hBP
  refine mem_iUnion.mpr ⟨α, ?_⟩
  show ψ i y u ∈ (g α).2 '' (g α).1
  rw [hα]
  exact mem_image_of_mem _ huB

/-- **First-order agreement of a Lipschitz map on an open set with `C¹` maps**, Simon Ch. 3,
proof of the area formula (2.4) (`chapter-03.txt` lines 376–381), used again for the co-area
formula (2.8) (lines 426–428). Assume the `C¹` Approximation Theorem (Simon Ch. 2, Thm. 1.5,
`chapter-02.txt` lines 165–169) for Lipschitz maps `ℝⁿ → ℝᵐ`. If `D ⊆ ℝⁿ` is open and `h` is
Lipschitz on `D`, then there are `C¹` maps `G i` and Borel sets `E i ⊆ D` such that `h = G i` on
`E i`, `h` has Fréchet derivative `DG i(u)` at each `u ∈ E i`, and `Lⁿ(D \ ⋃ i, E i) = 0`.
Extend `h|_D` to a globally Lipschitz `h̃` (Ch. 2, Thm. 1.2), apply the hypothesis to `h̃` with
`ε = (i + 1)⁻¹`, and let `E i = D ∩ {h̃ differentiable} ∩ {h̃ = G i} ∩ {Dh̃ = DG i}`. As `D` is
open, `h = h̃` near each `u ∈ D`; and `D \ ⋃ i, E i` lies in the union of the non-differentiability
set of `h̃` (null by Rademacher, Ch. 2, Thm. 1.4) and `⋂ i, {h̃ ≠ G i ∨ Dh̃ ≠ DG i}`, whose
measure is `< (i + 1)⁻¹` for every `i`. -/
theorem Submission.lipschitzOn_open_c1_first_order_agreement : ∀ (n m : ℕ), (∀ (F : Rn n → Rn m) (K : ℝ≥0), LipschitzWith K F → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Rn n → Rn m, ContDiff ℝ 1 g ∧ volume {x | F x ≠ g x ∨ fderiv ℝ F x ≠ fderiv ℝ g x} < ε) → ∀ (D : Set (Rn n)) (h : Rn n → Rn m), IsOpen D → (∃ K, LipschitzOnWith K h D) → ∃ (G : ℕ → Rn n → Rn m) (E : ℕ → Set (Rn n)), (∀ i, ContDiff ℝ 1 (G i)) ∧ (∀ i, MeasurableSet (E i)) ∧ (∀ i, E i ⊆ D) ∧ (∀ i, ∀ u ∈ E i, h u = G i u ∧ HasFDerivAt h (fderiv ℝ (G i) u) u) ∧ volume (D \ ⋃ i, E i) = 0 := by
  intro n m hC1 D h hD ⟨K, hK⟩
  -- Step 1: a globally Lipschitz extension `ht` of `h|_D`.
  obtain ⟨ht, htL, hteq⟩ := hK.extend_finite_dimension
  -- Step 2: `C¹` maps `G i` that agree with `ht` to first order off a set of measure `< (i + 1)⁻¹`.
  have hε : ∀ i : ℕ, (0 : ℝ≥0∞) < ((i + 1 : ℕ) : ℝ≥0∞)⁻¹ := fun i ↦
    ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)
  choose G hGC hGv using fun i : ℕ ↦ hC1 ht _ htL _ (hε i)
  -- Step 3: `E i = D ∩ {ht differentiable} ∩ {ht = G i} ∩ {D ht = D (G i)} ⊆ D`.
  refine ⟨G, fun i ↦ D ∩ {u | DifferentiableAt ℝ ht u} ∩ {u | ht u = G i u} ∩
    {u | fderiv ℝ ht u = fderiv ℝ (G i) u}, hGC, fun i ↦ ?_, fun i u hu ↦ hu.1.1.1, ?_, ?_⟩
  · -- Step 4: `E i` is Borel.
    exact ((hD.measurableSet.inter (measurableSet_of_differentiableAt ℝ ht)).inter
      (isClosed_eq htL.continuous (hGC i).continuous).measurableSet).inter
      (measurableSet_eq_fun (measurable_fderiv ℝ ht) (measurable_fderiv ℝ (G i)))
  · -- Step 5: first-order agreement on `E i`, since `h = ht` on the open neighbourhood `D` of `u`.
    rintro i u ⟨⟨⟨huD, hud⟩, hueq⟩, hufd⟩
    refine ⟨(hteq huD).trans hueq, ?_⟩
    rw [← hufd]
    exact hud.hasFDerivAt.congr_of_eventuallyEq (eventuallyEq_of_mem (hD.mem_nhds huD) hteq)
  · -- Steps 6–7: `D \ ⋃ i, E i ⊆ {¬ DifferentiableAt ℝ ht} ∪ ⋂ i, Bad i` with
    -- `Bad i = {ht ≠ G i ∨ D ht ≠ D (G i)}`; both parts are `Lⁿ`-null.
    have hdiff : volume {u | ¬ DifferentiableAt ℝ ht u} = 0 :=
      ae_iff.1 (htL.ae_differentiableAt (μ := volume))
    have hbad : volume (⋂ i, {x | ht x ≠ G i x ∨ fderiv ℝ ht x ≠ fderiv ℝ (G i) x}) = 0 :=
      nonpos_iff_eq_zero.1 (ge_of_tendsto'
        (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
        fun i ↦ (measure_mono (iInter_subset _ i)).trans (hGv i).le)
    refine measure_mono_null ?_ (measure_union_null hdiff hbad)
    rintro u ⟨huD, huE⟩
    by_cases hud : DifferentiableAt ℝ ht u
    · refine Or.inr (mem_iInter.2 fun i ↦ ?_)
      by_contra hcon
      exact huE (mem_iUnion.2 ⟨i, ⟨⟨huD, hud⟩, not_not.1 fun h₁ ↦ hcon (Or.inl h₁)⟩,
        not_not.1 fun h₂ ↦ hcon (Or.inr h₂)⟩)
    · exact Or.inl hud

/-- **`C¹` chart pieces of a countably rectifiable set with first-order `C¹` agreement of `f`**
(Simon Ch. 3, Lemma 1.2 and Remark 1.3, `chapter-03.txt` lines 25–73, and the procedure of the
area formula, lines 376–381, invoked for the co-area formula at lines 426–428 and for the slices
at lines 440–442). Assume Lemma 1.2 (`SubmanifoldCoverCharacterization`) and the `C¹`
Approximation Theorem (Ch. 2, Thm. 1.5) for Lipschitz maps `ℝⁿ → ℝᵖ`. Let `M ⊆ ℝ^{n+ℓ}` be
countably `n`-rectifiable, `U ⊇ M` open and `f` locally Lipschitz on `U`. Then there are open
`D_j ⊆ ℝⁿ`, maps `ψ_j` that are `C¹`, injective and Lipschitz on `D_j` with injective
differential, `C¹` maps `G_j` and Borel sets `E_j ⊆ D_j` such that `f(ψ_j(u)) = G_j(u)` and
`D(f ∘ ψ_j)(u) = DG_j(u)` for `u ∈ E_j`, and `Hⁿ(M \ ⋃_j ψ_j(E_j)) = 0`. Lemma 1.2 gives
`M ⊆ N₀ ∪ ⋃ᵢ Sᵢ` with `Hⁿ(N₀) = 0`; the chart pieces `(D_α, ψ_α)` of
`submanifold_cover_lipschitz_open_charts` cover `M \ N₀`, and
`lipschitzOn_open_c1_first_order_agreement` for `f ∘ ψ_α` gives `(G_{α,i}, E_{α,i})` with
`Lⁿ(D_α \ ⋃ᵢ E_{α,i}) = 0`, whose image under the Lipschitz `ψ_α` is `Hⁿ`-null. The pairs
`(α, i)` are re-indexed by `Nat.unpair`. -/
theorem Submission.rectifiable_c1_chart_pieces : SubmanifoldCoverCharacterization → (∀ (n p : ℕ) (f : Rn n → Rn p) (K : ℝ≥0), LipschitzWith K f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Rn n → Rn p, ContDiff ℝ 1 g ∧ volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x} < ε) → ∀ (n ℓ m : ℕ) (M U : Set (Rn (n + ℓ))) (f : Rn (n + ℓ) → Rn m), CountablyRectifiable n M → IsOpen U → M ⊆ U → LocallyLipschitzOn U f → ∃ (D : ℕ → Set (Rn n)) (ψ : ℕ → Rn n → Rn (n + ℓ)) (G : ℕ → Rn n → Rn m) (E : ℕ → Set (Rn n)), (∀ j, IsOpen (D j)) ∧ (∀ j, ContDiffOn ℝ 1 (ψ j) (D j)) ∧ (∀ j, InjOn (ψ j) (D j)) ∧ (∀ j, ∃ K, LipschitzOnWith K (ψ j) (D j)) ∧ (∀ j, ∀ u ∈ D j, Function.Injective (fderiv ℝ (ψ j) u)) ∧ (∀ j, ContDiff ℝ 1 (G j)) ∧ (∀ j, MeasurableSet (E j)) ∧ (∀ j, E j ⊆ D j) ∧ (∀ j, ∀ u ∈ E j, f (ψ j u) = G j u ∧ HasFDerivAt (f ∘ ψ j) (fderiv ℝ (G j) u) u) ∧ μHE[n] (M \ ⋃ j, ψ j '' E j) = 0 := by
  intro hSC hC1 n ℓ m M U f hM hU hMU hf
  -- Step 1: Lemma 1.2 gives `M ⊆ N₀ ∪ ⋃ i, S i` with `Hⁿ(N₀) = 0` and `C¹` submanifolds `S i`.
  obtain ⟨N₀, S, hN₀, hS, hcov⟩ := (hSC n ℓ M).1 hM
  -- Steps 2–4: chart pieces `(D α, ψ α)`, `f ∘ ψ α` Lipschitz, `M ⊆ N₀ ∪ ⋃ α, ψ α '' D α`.
  obtain ⟨D, ψ, hDo, hψC, hψinj, hψL, hψD, hfψL, hMcov⟩ :=
    Submission.submanifold_cover_lipschitz_open_charts n (n + ℓ) m M U N₀ S f hU hMU hf hS hcov
  -- Steps 5–7: `C¹` maps `G α i` agreeing with `f ∘ ψ α` to first order on Borel sets
  -- `E α i ⊆ D α`, with `Lⁿ(D α \ ⋃ i, E α i) = 0`.
  choose G E hGC hEm hED hEagr hEnull using fun α ↦
    Submission.lipschitzOn_open_c1_first_order_agreement n m (hC1 n m) (D α) (f ∘ ψ α) (hDo α)
      (hfψL α)
  -- Step 9: re-index the pairs `(α, i)` by `j` through `Nat.unpair`.
  refine ⟨fun j ↦ D j.unpair.1, fun j ↦ ψ j.unpair.1, fun j ↦ G j.unpair.1 j.unpair.2,
    fun j ↦ E j.unpair.1 j.unpair.2, fun j ↦ hDo _, fun j ↦ hψC _, fun j ↦ hψinj _,
    fun j ↦ hψL _, fun j ↦ hψD _, fun j ↦ hGC _ _, fun j ↦ hEm _ _, fun j ↦ hED _ _,
    fun j ↦ hEagr _ _, ?_⟩
  -- Step 8: `ψ α '' (D α \ ⋃ i, E α i)` is `Hⁿ`-null: `ψ α` is Lipschitz and `Hⁿ = Lⁿ` on `ℝⁿ`.
  have hnull : ∀ α, μHE[n] (ψ α '' (D α \ ⋃ i, E α i)) = 0 := by
    intro α
    obtain ⟨K, hK⟩ := hψL α
    refine nonpos_iff_eq_zero.1 ?_
    calc μHE[n] (ψ α '' (D α \ ⋃ i, E α i))
        ≤ (K : ℝ≥0∞) ^ n * μHE[n] (D α \ ⋃ i, E α i) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hK.mono sdiff_subset)
      _ = 0 := by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hEnull α, mul_zero]
  -- Step 9: `M \ ⋃ j, ψ j '' E j ⊆ N₀ ∪ ⋃ α, ψ α '' (D α \ ⋃ i, E α i)`, a null set.
  refine measure_mono_null ?_ (measure_union_null hN₀ (measure_iUnion_null hnull))
  rintro x ⟨hxM, hxE⟩
  rcases hMcov hxM with hx0 | hxD
  · exact Or.inl hx0
  obtain ⟨α, u, huD, rfl⟩ := mem_iUnion.1 hxD
  refine Or.inr (mem_iUnion.2 ⟨α, u, ⟨huD, fun huE ↦ ?_⟩, rfl⟩)
  obtain ⟨i, hi⟩ := mem_iUnion.1 huE
  refine hxE (mem_iUnion.2 ⟨Nat.pair α i, ?_⟩)
  simp only [Nat.unpair_pair]
  exact mem_image_of_mem _ hi

/-- **Simon Ch. 3, 2.1–2.2 and (2.7)** (`chapter-03.txt` lines 335–360 and 412–418), along a
chart: let `A : ℝⁿ → ℝᴺ` be injective with `range A` a weighted approximate tangent plane of `M`
at `x`, `θ x ≠ 0`, and let `f` have line derivative `Γ w` at `x` in every direction `A w`. Then
`T_x M = range A` (uniqueness of weighted tangent planes, SimonGMT
`HasWeightedApproximateTangentSpaceAt.unique`), `L = Γ ∘ A⁻¹` is a tangential differential on
`range A`, it is `d^M f_x` (uniqueness of line derivatives, `HasLineDerivAt.unique`), and
`J^{M*}_f(x) · normDet A = normDet (A ∘ ι_{ker Γ}) · normDet Γ*` by the chain rule
`Submission.coarea_normDet_chain_rule` applied to `T = range A`, `A`, `L` and `Γ`. -/
theorem Submission.chart_coarea_jacobian_identification : ∀ (n N m : ℕ) (M : Set (Rn N))
    (θ : Rn N → ℝ) (f : Rn N → Rn m) (x : Rn N) (A : Rn n →L[ℝ] Rn N) (Γ : Rn n →L[ℝ] Rn m),
    θ x ≠ 0 → Function.Injective A →
    HasWeightedApproximateTangentSpaceAt n M θ x (LinearMap.range A.toLinearMap) →
    (∀ w : Rn n, HasLineDerivAt ℝ f (Γ w) x (A w)) →
    approxTangentPlane n M θ x = LinearMap.range A.toLinearMap ∧
    (∃ L : ↥(LinearMap.range A.toLinearMap) →L[ℝ] Rn m,
      HasTangentialDifferentialAt (LinearMap.range A.toLinearMap) f x L) ∧
    coareaJacobian (approxTangentPlane n M θ x) f x * A.toLinearMap.normDet =
      (A.toLinearMap ∘ₗ (LinearMap.ker Γ.toLinearMap).subtype).normDet *
        (LinearMap.adjoint Γ.toLinearMap).normDet := by
  intro n N m M θ f x A Γ hθ hA hT hΓ
  set T : Submodule ℝ (Rn N) := LinearMap.range A.toLinearMap
  -- (i) `T_x M = T`: the chosen plane and `T` are both weighted tangent planes and `θ x ≠ 0`.
  have hplane : approxTangentPlane n M θ x = T := by
    have h : ∃ P : Submodule ℝ (Rn N), HasWeightedApproximateTangentSpaceAt n M θ x P := ⟨T, hT⟩
    rw [approxTangentPlane, dite_eq_left h]
    exact Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique hθ
      h.choose_spec hT
  -- (ii) `L = Γ ∘ e⁻¹`, `e : ℝⁿ ≃ T` induced by `A`, has line derivative `Γ w` along `e w = A w`.
  let e : Rn n ≃ₗ[ℝ] T := LinearEquiv.ofInjective A.toLinearMap hA
  have he : ∀ w : Rn n, (e w : Rn N) = A w := fun _ ↦ rfl
  obtain ⟨L, hLe⟩ : ∃ L : T →L[ℝ] Rn m, ∀ w : Rn n, L (e w) = Γ w :=
    ⟨LinearMap.toContinuousLinearMap (Γ.toLinearMap ∘ₗ e.symm.toLinearMap), fun w ↦ by simp⟩
  have hL : HasTangentialDifferentialAt T f x L := by
    intro τ
    obtain ⟨w, rfl⟩ := e.surjective τ
    rw [hLe, he]
    exact hΓ w
  -- `d^M f_x = L`: both are line derivatives of `f` at `x` in every direction `τ ∈ T`.
  have hdiff : tangentialDifferential T f x = L := by
    have h : ∃ L' : T →L[ℝ] Rn m, HasTangentialDifferentialAt T f x L' := ⟨L, hL⟩
    rw [tangentialDifferential, dite_eq_left h]
    exact ContinuousLinearMap.ext fun τ ↦ (h.choose_spec τ).unique (hL τ)
  -- (iii) `J^{M*}_f(x) = normDet L*`, and `Γ v = L (A v)` feeds the co-area chain rule.
  refine ⟨hplane, ⟨L, hL⟩, ?_⟩
  rw [hplane, coareaJacobian, hdiff]
  refine Submission.coarea_normDet_chain_rule n N m T A.toLinearMap L.toLinearMap Γ.toLinearMap
    hA rfl fun v hv ↦ ?_
  show Γ v = L ⟨A v, hv⟩
  rw [show (⟨A v, hv⟩ : T) = e v from Subtype.ext (he v).symm, hLe]

/-- **Simon Ch. 3, co-area formula (2.9) on one `C¹` chart piece** (`chapter-03.txt` lines
412–428: (2.8) "follows from the `C¹` case … in a similar manner to the procedure used for the
discussion of the area formula", lines 377–389). Assume the chart lemma (CT), the frozen
statement of `Submission.chart_approx_tangent_and_differential`. Let `n = m + k` with `k > 0`,
`ψ : D → ℝ^{n+ℓ}` a `C¹` chart with injective `Dψ`, injective on the open set `D ⊆ ℝⁿ`, and
`G : ℝⁿ → ℝᵐ` a `C¹` map with `f ∘ ψ = G` and `D(f ∘ ψ) = DG` on the Borel set `E ⊆ D`. Then
for Borel `B ⊆ ψ(E) ∩ M` and Borel `φ ≥ 0`, `y ↦ ∫_{B ∩ f⁻¹(y)} φ dHᵏ` is `Lᵐ`-a.e.
measurable and `∫_B φ J^{M*}_f dHⁿ = ∫_{ℝᵐ} ∫_{B ∩ f⁻¹(y)} φ dHᵏ dLᵐ(y)`.

Proof: for `m = 0`, `ℝ⁰` is a point carrying the unit mass, `J^{M*}_f ≡ 1` (the adjoint has
zero-dimensional domain) and every slice `B ∩ f⁻¹(y)` is `B`. Otherwise pull `B` back to the
Borel set `B' = E ∩ ψ⁻¹(B)`; then `ψ(B') = B` and `B ∩ f⁻¹(y) = ψ(B' ∩ G⁻¹(y))`, so the right
side is the `C¹` parametric co-area formula `Submission.c1_parametric_coarea_formula` on `B'`.
For the left side, the `C¹` area formula `Submission.pcoarea_c1_injOn_area_formula` on the Borel
sets `B' ∩ ψ⁻¹(T)` gives `Hⁿ ⌞ B = (ψ|_{B'})_# (Jψ Lⁿ ⌞ B')`, `Jψ = normDet Dψ`, and `ψ|_{B'}`
is a measurable embedding (Lusin–Souslin), so `∫_B g dHⁿ = ∫_{B'} Jψ(u) g(ψ u) du` for every
`g ≥ 0`, measurable or not; thus the measurability of `J^{M*}_f` is not needed. Finally (CT) and
`Submission.chart_coarea_jacobian_identification` give
`J^{M*}_f(ψ u) Jψ(u) = normDet(Dψ(u) ∘ ι_{ker DG(u)}) normDet(DG(u)*)`, the `C¹` integrand, for
`Lⁿ`-a.e. `u ∈ B'` (`D(f ∘ ψ)(u) = DG(u)` on `E`). -/
theorem Submission.chart_piece_coarea_formula : (∀ (n ℓ p : ℕ) (M U : Set (Rn (n + ℓ)))
    (θ : Rn (n + ℓ) → ℝ) (f : Rn (n + ℓ) → Rn p) (V : Set (Rn n)) (ψ : Rn n → Rn (n + ℓ)),
    NullMeasurableSet M μHE[n] → IsPositiveLocallyIntegrableWeight n M θ → IsOpen U → M ⊆ U →
    LocallyLipschitzOn U f → IsOpen V → ContDiffOn ℝ 1 ψ V →
    (∀ u ∈ V, Function.Injective (fderiv ℝ ψ u)) →
    ∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ V → ψ u ∈ M →
      HasWeightedApproximateTangentSpaceAt n M θ (ψ u)
          (LinearMap.range (fderiv ℝ ψ u).toLinearMap) ∧
        DifferentiableAt ℝ (f ∘ ψ) u ∧
        ∀ w : Rn n, HasLineDerivAt ℝ f (fderiv ℝ (f ∘ ψ) u w) (ψ u) (fderiv ℝ ψ u w)) →
    ∀ (m k ℓ : ℕ) (M U : Set (Rn (m + k + ℓ))) (θ : Rn (m + k + ℓ) → ℝ)
      (f : Rn (m + k + ℓ) → Rn m) (D E : Set (Rn (m + k))) (ψ : Rn (m + k) → Rn (m + k + ℓ))
      (G : Rn (m + k) → Rn m),
      0 < k → NullMeasurableSet M μHE[m + k] → IsPositiveLocallyIntegrableWeight (m + k) M θ →
      IsOpen U → M ⊆ U → LocallyLipschitzOn U f → IsOpen D → ContDiffOn ℝ 1 ψ D → InjOn ψ D →
      (∃ K, LipschitzOnWith K ψ D) → (∀ u ∈ D, Function.Injective (fderiv ℝ ψ u)) →
      ContDiff ℝ 1 G → MeasurableSet E → E ⊆ D →
      (∀ u ∈ E, f (ψ u) = G u ∧ HasFDerivAt (f ∘ ψ) (fderiv ℝ G u) u) →
      ∀ B ⊆ ψ '' E ∩ M, MeasurableSet B → ∀ φ : Rn (m + k + ℓ) → ℝ≥0∞, Measurable φ →
        AEMeasurable (fun y : Rn m ↦ ∫⁻ x in B ∩ f ⁻¹' {y}, φ x ∂μHE[k]) volume ∧
          ∫⁻ x in B, φ x * ENNReal.ofReal (coareaJacobian (approxTangentPlane (m + k) M θ x) f x)
              ∂μHE[m + k] =
            ∫⁻ y, (∫⁻ x in B ∩ f ⁻¹' {y}, φ x ∂μHE[k]) ∂volume := by
  intro hCT m k ℓ M U θ f D E ψ G hk hM hθ hU hMU hf hD hψ hψinj _ hψD hG hE hED hEG
    B hB hBm φ hφ
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- `m = 0`: `ℝ⁰` is a point carrying the unit mass, `J^{M*}_f ≡ 1` and every slice is `B`.
    refine ⟨Subsingleton.measurable.aemeasurable, ?_⟩
    have hslice : ∀ y : Rn 0, B ∩ f ⁻¹' {y} = B := fun y ↦
      inter_eq_left.2 fun x _ ↦ Subsingleton.elim (f x) y
    have hJ : ∀ x, coareaJacobian (approxTangentPlane (0 + k) M θ x) f x = 1 := fun x ↦
      LinearMap.normDet_of_subsingleton _
    have hμ : (μHE[0 + k] : Measure (Rn (0 + k + ℓ))) = μHE[k] :=
      congrArg (fun d ↦ (μHE[d] : Measure (Rn (0 + k + ℓ)))) (Nat.zero_add k)
    simp only [hslice, hJ, hμ, ENNReal.ofReal_one, mul_one, lintegral_const,
      volume_euclideanSpace_eq_dirac, measure_univ]
  -- The Borel parameter set `B' = E ∩ ψ⁻¹(B)`, with `ψ(B') = B`.
  set B' : Set (Rn (m + k)) := E ∩ ψ ⁻¹' B with hB'
  have hB'D : B' ⊆ D := inter_subset_left.trans hED
  have hB'm : MeasurableSet B' := by
    have h := hE.subtype_image (((hψ.continuousOn.mono hED).domRestrict.measurable) hBm)
    rwa [domRestrict_eq, preimage_comp, Subtype.image_preimage_coe] at h
  have himage : ψ '' B' = B := by
    rw [hB', image_inter_preimage]
    exact inter_eq_right.2 fun x hx ↦ (hB hx).1
  -- Slices: `B ∩ f⁻¹(y) = ψ(B' ∩ G⁻¹(y))`, since `f ∘ ψ = G` on `E`.
  have hslice : ∀ y, ψ '' (B' ∩ G ⁻¹' {y}) = B ∩ f ⁻¹' {y} := by
    intro y
    ext x
    constructor
    · rintro ⟨u, ⟨⟨huE, hux⟩, huy⟩, rfl⟩
      refine ⟨hux, ?_⟩
      rw [mem_preimage, (hEG u huE).1]
      exact huy
    · rintro ⟨hxB, hxy⟩
      obtain ⟨u, huE, rfl⟩ := (hB hxB).1
      refine ⟨u, ⟨⟨huE, hxB⟩, ?_⟩, rfl⟩
      rw [mem_preimage, ← (hEG u huE).1]
      exact hxy
  -- Right side: the `C¹` parametric co-area formula on `B'`.
  obtain ⟨hmeas, hc1⟩ := Submission.c1_parametric_coarea_formula m k (m + k + ℓ) D ψ G hm hk hD
    hψ hψinj hG B' hB'D hB'm φ hφ
  simp only [hslice] at hmeas hc1
  refine ⟨hmeas, ?_⟩
  rw [← hc1]
  -- Left side: `Hⁿ ⌞ B` is the image of `Jψ Lⁿ ⌞ B'` under the measurable embedding `ψ|_{B'}`
  -- (Lusin–Souslin), by the `C¹` area formula on the Borel sets `B' ∩ ψ⁻¹(T)`.
  have hndcont : Continuous fun L : Rn (m + k) →L[ℝ] Rn (m + k + ℓ) ↦ L.toLinearMap.normDet := by
    have h1 : Continuous (fun L : Rn (m + k) →L[ℝ] Rn (m + k + ℓ) ↦
        ContinuousLinearMap.adjoint L ∘L L) :=
      ContinuousLinearMap.adjoint.continuous.clm_comp continuous_id
    have h2 : Continuous (fun L : Rn (m + k) →L[ℝ] Rn (m + k + ℓ) ↦
        Real.sqrt (ContinuousLinearMap.adjoint L ∘L L).det) :=
      Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp h1)
    refine h2.congr fun L ↦ ?_
    rw [← ContinuousLinearMap.normDet_sq L]
    exact Real.sqrt_sq (LinearMap.normDet_nonneg _)
  have hwm : Measurable fun u ↦ ENNReal.ofReal (fderiv ℝ ψ u).toLinearMap.normDet :=
    ENNReal.measurable_ofReal.comp (hndcont.measurable.comp (measurable_fderiv ℝ ψ))
  have hemb : MeasurableEmbedding (B'.domRestrict ψ) :=
    ContinuousOn.measurableEmbedding hB'm (hψ.continuousOn.mono hB'D) (hψinj.mono hB'D)
  have hmap : Measure.map (B'.domRestrict ψ) (Measure.comap Subtype.val
      (volume.withDensity fun u ↦ ENNReal.ofReal (fderiv ℝ ψ u).toLinearMap.normDet)) =
      (μHE[m + k] : Measure (Rn (m + k + ℓ))).restrict B := by
    ext T hT
    have hS : Subtype.val '' (B'.domRestrict ψ ⁻¹' T) = B' ∩ ψ ⁻¹' T := by
      rw [domRestrict_eq, preimage_comp, Subtype.image_preimage_coe]
    have hSm : MeasurableSet (B' ∩ ψ ⁻¹' T) := hS ▸ hB'm.subtype_image (hemb.measurable hT)
    have hTB : T ∩ B = ψ '' (B' ∩ ψ ⁻¹' T) := by rw [image_inter_preimage, himage, inter_comm]
    have h := Submission.pcoarea_c1_injOn_area_formula (m + k) (m + k + ℓ) D ψ hD hψ hψinj
      (B' ∩ ψ ⁻¹' T) (inter_subset_left.trans hB'D) hSm 1 measurable_const
    simp only [Pi.one_apply, one_mul, setLIntegral_one] at h
    rw [hemb.map_apply, comap_subtype_coe_apply hB'm, hS, withDensity_apply _ hSm,
      Measure.restrict_apply hT, hTB, h]
  -- Hence `∫_B g dHⁿ = ∫_{B'} Jψ (g ∘ ψ) dLⁿ` for the (possibly non-measurable) integrand `g`.
  have harea : ∫⁻ x in B, φ x * ENNReal.ofReal
        (coareaJacobian (approxTangentPlane (m + k) M θ x) f x) ∂μHE[m + k] =
      ∫⁻ u in B', ENNReal.ofReal (fderiv ℝ ψ u).toLinearMap.normDet * (φ (ψ u) *
        ENNReal.ofReal (coareaJacobian (approxTangentPlane (m + k) M θ (ψ u)) f (ψ u))) := by
    rw [← hmap, hemb.lintegral_map]
    simp only [domRestrict_apply]
    rw [lintegral_subtype_comap hB'm (fun u ↦ φ (ψ u) *
        ENNReal.ofReal (coareaJacobian (approxTangentPlane (m + k) M θ (ψ u)) f (ψ u))),
      setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _ hwm _ hB'm
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    rfl
  rw [harea]
  -- Pointwise for a.e. `u ∈ B'`: `J^{M*}_f(ψ u) Jψ(u)` is the integrand of the `C¹` formula.
  refine setLIntegral_congr_fun_ae hB'm ?_
  filter_upwards [hCT (m + k) ℓ m M U θ f D ψ hM hθ hU hMU hf hD hψ hψD] with u hu huB'
  have huM : ψ u ∈ M := (hB huB'.2).2
  obtain ⟨htan, -, hline⟩ := hu (hB'D huB') huM
  rw [(hEG u huB'.1).2.fderiv] at hline
  have hJ := (Submission.chart_coarea_jacobian_identification (m + k) (m + k + ℓ) m M θ f (ψ u)
    (fderiv ℝ ψ u) (fderiv ℝ G u) (hθ.1 _ huM).ne' (hψD u (hB'D huB')) htan hline).2.2
  have hJ0 : 0 ≤ coareaJacobian (approxTangentPlane (m + k) M θ (ψ u)) f (ψ u) :=
    LinearMap.normDet_nonneg _
  rw [← hJ, ENNReal.ofReal_mul hJ0]
  ring

/-- **Derivative bounds for a `C¹` chart with upper and lower Lipschitz bounds** (Simon Ch. 3, the
`C¹` charts in the proof of Theorem 1.6 "⇒", `chapter-03.txt` lines 113–143, and Remark 1.5(2)).
Let `B ⊆ ℝⁿ` be open and `ψ : ℝⁿ → ℝᴺ` be `C¹` and `K`-Lipschitz on `B`, with
`c |u - u'| ≤ |ψ(u) - ψ(u')|` for all `u, u' ∈ B` (no sign condition on `c`). Then for every
`v ∈ B`: `‖Dψ(v)‖ ≤ K` by `norm_fderiv_le_of_lipschitzOn`, as `B ∈ 𝓝 v`; and `c |w| ≤ |Dψ(v) w|`
for every `w ∈ ℝⁿ`, since for small `t > 0` we have `v + t w ∈ B`, hence
`c |w| ≤ |t⁻¹ (ψ(v + t w) - ψ(v))|`, and these difference quotients tend to `Dψ(v) w` as `t ↓ 0`
(`HasFDerivAt.lim`). -/
theorem Submission.chartTD_chart_fderiv_bounds : ∀ (n N : ℕ) (B : Set (Rn n)) (ψ : Rn n → Rn N) (K : ℝ≥0) (c : ℝ), IsOpen B → ContDiffOn ℝ 1 ψ B → LipschitzOnWith K ψ B → (∀ u ∈ B, ∀ u' ∈ B, c * ‖u - u'‖ ≤ ‖ψ u - ψ u'‖) → ∀ v ∈ B, ‖fderiv ℝ ψ v‖ ≤ K ∧ ∀ w : Rn n, c * ‖w‖ ≤ ‖fderiv ℝ ψ v w‖ := by
  intro n N B ψ K c hB hψ hLip hlow v hv
  have hBv : B ∈ 𝓝 v := hB.mem_nhds hv
  -- Upper bound: `ψ` is `K`-Lipschitz on the neighbourhood `B` of `v`.
  refine ⟨norm_fderiv_le_of_lipschitzOn ℝ hBv hLip, fun w ↦ ?_⟩
  -- `ψ` is `C¹` on the open set `B`, so it has derivative `Dψ(v)` at `v`.
  have hd : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    ((hψ.differentiableOn one_ne_zero).differentiableAt hBv).hasFDerivAt
  -- `|t⁻¹ (ψ(v + t w) - ψ(v))| → |Dψ(v) w|` as `t ↓ 0`, since `|t⁻¹| = t⁻¹ → ∞`.
  have hlim : Tendsto (fun t : ℝ ↦ ‖t⁻¹ • (ψ (v + t⁻¹⁻¹ • w) - ψ v)‖) (𝓝[>] 0)
      (𝓝 ‖fderiv ℝ ψ v w‖) := by
    refine (hd.lim w (c := fun t : ℝ ↦ t⁻¹) ?_).norm
    refine (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [Real.norm_of_nonneg (inv_nonneg.2 ht.le)]
  -- Eventually `v + t w ∈ B`, as `v + t w → v` when `t ↓ 0`.
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), v + t • w ∈ B := by
    have hcont : Tendsto (fun t : ℝ ↦ v + t • w) (𝓝 0) (𝓝 v) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 v (by simp)
    exact hcont.mono_left nhdsWithin_le_nhds hBv
  -- For such `t > 0`: `c |w| = t⁻¹ c |t w| ≤ t⁻¹ |ψ(v + t w) - ψ(v)|`.
  refine ge_of_tendsto hlim ?_
  filter_upwards [hev, self_mem_nhdsWithin] with t ht (htpos : 0 < t)
  have h := hlow (v + t • w) ht v hv
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le] at h
  rw [inv_inv, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 htpos.le)]
  calc c * ‖w‖ = t⁻¹ * (c * (t * ‖w‖)) := by field_simp
    _ ≤ t⁻¹ * ‖ψ (v + t • w) - ψ v‖ := by gcongr

/-- **Operator-norm bound for the area factor** (Simon Ch. 2, linear area formula (3.1),
`chapter-02.txt` lines 742–758, and the Lipschitz image estimate Thm. 1.8(i), lines 268–275):
for every linear map `A : ℝⁿ → ℝᴺ`, `normDet A = √det(A* A) ≤ ‖A‖ⁿ`. On the closed unit ball
`S ⊆ ℝⁿ` the linear area formula gives `Hⁿ(A(S)) = normDet A · Lⁿ(S)`, while `A` is
`‖A‖`-Lipschitz, so `Hⁿ(A(S)) ≤ ‖A‖ⁿ Hⁿ(S) = ‖A‖ⁿ Lⁿ(S)`; cancel `0 < Lⁿ(S) < ∞`. -/
theorem Submission.chartTD_normDet_le_opNorm_pow : ∀ (n N : ℕ) (A : Rn n →L[ℝ] Rn N), A.toLinearMap.normDet ≤ ‖A‖ ^ n := by
  intro n N A
  have hfin : finrank ℝ (Rn n) = n := finrank_euclideanSpace_fin
  set S : Set (Rn n) := Metric.closedBall 0 1
  -- Simon Ch. 2 (3.1): `Hⁿ(A(S)) = normDet A · Lⁿ(S)`.
  have h1 := LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume A.toLinearMap S
  -- `A` is `‖A‖₊`-Lipschitz, so `Hⁿ(A(S)) ≤ ‖A‖₊ⁿ Hⁿ(S) = ‖A‖₊ⁿ Lⁿ(S)`.
  have h2 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
    (finrank ℝ (Rn n)) (A.lipschitzWith.lipschitzOnWith (s := S))
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h2
  have hcoe : (A.toLinearMap : Rn n → Rn N) '' S = A '' S := rfl
  rw [← hcoe, h1] at h2
  -- Cancel `0 < Lⁿ(S) < ∞`.
  have hpos : 0 < volume S := Metric.measure_closedBall_pos _ _ one_pos
  have hfinite : volume S < ∞ := measure_closedBall_lt_top
  have h3 : ENNReal.ofReal A.toLinearMap.normDet ≤ (‖A‖₊ : ℝ≥0∞) ^ finrank ℝ (Rn n) :=
    (ENNReal.mul_le_mul_iff_left hpos.ne' hfinite.ne).mp h2
  rw [hfin] at h3
  -- Back to `ℝ`: `(‖A‖₊ : ℝ≥0∞)ⁿ = ofReal (‖A‖ⁿ)`.
  have h4 : ENNReal.ofReal A.toLinearMap.normDet ≤ ENNReal.ofReal (‖A‖ ^ n) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _)]
    simpa [ofReal_norm, enorm_eq_nnnorm] using h3
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h4

/-- **Injective area formula on an open Lipschitz domain, in integral form** (Simon Ch. 2, (3.2)
and (3.5), `chapter-02.txt` lines 743–797). Let `B ⊆ ℝⁿ` be open, `ψ : ℝⁿ → ℝᴺ` `K`-Lipschitz
and injective on `B`, and `g : ℝᴺ → ℝ` continuous. Then `∫_{ψ(B)} g dHⁿ = ∫_B g(ψ v) Jψ(v) dv`
with `Jψ(v) = normDet (Dψ(v))`, as Bochner integrals (no integrability assumption).

Proof: `Hⁿ⌞ψ(B)` is the push-forward under `ψ` of `ν = Jψ · Lⁿ⌞B`. For Borel `E`, the weighted
area formula (3.5) with weight `1_E ∘ ψ` gives `Hⁿ(E ∩ ψ(B)) = ν(ψ⁻¹(E))`: by injectivity the
fibre sum is `1_{E ∩ ψ(B)}`, and `ψ(B)` is Borel by Lusin–Souslin. Change of variables for the
push-forward and integration against the density `Jψ` then give the integral identity.
The SimonGMT modules proving (3.5) lie outside the frozen imports, so (3.5) is derived here from
the linear case (3.1), Mathlib's `LinearMap.euclideanHausdorffMeasure_image`, by the local steps
of the accepted proof of `Submission.areaFormula_on_chart_piece`: comparison with linear maps on
the pieces of `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, a density-point
bound on derivatives, injective branches, and null images of critical points via the graphs
`x ↦ (G x, ε x)`. Rademacher's theorem gives differentiability a.e. on the open set `B`. -/
theorem Submission.chartTD_injective_area_setIntegral : ∀ (n N : ℕ) (B : Set (Rn n)) (ψ : Rn n → Rn N) (K : ℝ≥0), IsOpen B → LipschitzOnWith K ψ B → InjOn ψ B → ∀ g : Rn N → ℝ, Continuous g → ∫ y in ψ '' B, g y ∂μHE[n] = ∫ v in B, g (ψ v) * (fderiv ℝ ψ v).toLinearMap.normDet := by
  intro n
  classical
  -- The metric Jacobian `L ↦ normDet L = √det (L* L)` is continuous.
  have normDet_cont : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F], Continuous (fun L : Rn n →L[ℝ] F ↦ L.toLinearMap.normDet) := by
    intro F _ _ _
    have heq : (fun L : Rn n →L[ℝ] F ↦ L.toLinearMap.normDet) =
        fun L ↦ Real.sqrt ((ContinuousLinearMap.adjoint L ∘L L).det) := by
      funext L
      rw [← L.normDet_sq]
      simpa only [RCLike.ofReal_real_eq_id, id_eq] using
        (Real.sqrt_sq L.toLinearMap.normDet_nonneg).symm
    rw [heq]
    exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
  -- Hausdorff measures of images under a distance comparison (Simon Ch. 2, Thm. 1.8(i)).
  have image_cmp : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [MeasurableSpace F] [BorelSpace F] (Φ Γ : Rn n → F) (s : Set (Rn n)) (K : ℝ≥0),
      InjOn Γ s → (∀ x ∈ s, ∀ y ∈ s, dist (Φ x) (Φ y) ≤ K * dist (Γ x) (Γ y)) →
      μHE[n] (Φ '' s) ≤ (K : ℝ≥0∞) ^ n * μHE[n] (Γ '' s) := by
    intro F _ _ _ _ Φ Γ s K hΓ hd
    have hL : LipschitzOnWith K (Φ ∘ Function.invFunOn Γ s) (Γ '' s) := by
      refine LipschitzOnWith.of_dist_le_mul fun _ hx _ hy ↦ ?_
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      rw [Function.comp_apply, Function.comp_apply, hΓ.leftInvOn_invFunOn hx,
        hΓ.leftInvOn_invFunOn hy]
      exact hd x hx y hy
    have h1 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hL
    rwa [image_comp, hΓ.invFunOn_image Subset.rfl] at h1
  -- Simon Ch. 2 (3.1): the linear area formula.
  have linear_area : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [MeasurableSpace F] [BorelSpace F] (L : Rn n →ₗ[ℝ] F) (s : Set (Rn n)),
      μHE[n] (L '' s) = ENNReal.ofReal L.normDet * volume s := by
    intro F _ _ _ _ L s
    have h1 := L.euclideanHausdorffMeasure_image s
    rwa [InnerProductSpace.euclideanHausdorffMeasure_eq_volume, finrank_euclideanSpace_fin] at h1
  -- Image estimates for maps uniformly close to an injective linear map `L`.
  have approx_upper : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [MeasurableSpace F] [BorelSpace F] (G : Rn n → F) (L : Rn n →L[ℝ] F) (s : Set (Rn n))
      (δ K : ℝ≥0), ApproximatesLinearOn G L s δ → AntilipschitzWith K L →
      μHE[n] (G '' s) ≤ ((1 + δ * K : ℝ≥0) : ℝ≥0∞) ^ n *
        (ENNReal.ofReal L.toLinearMap.normDet * volume s) := by
    intro F _ _ _ _ G L s δ K hG hK
    rw [← linear_area F L.toLinearMap s]
    refine image_cmp F G L s _ hK.injective.injOn fun x hx y hy ↦ ?_
    have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
      simpa only [dist_eq_norm] using hK.le_mul_dist x y
    have herr : ‖G x - G y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ := by
      calc ‖G x - G y - (L x - L y)‖ ≤ δ * ‖x - y‖ := by
            simpa only [map_sub] using hG x hx y hy
        _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
        _ = (δ : ℝ) * K * ‖L x - L y‖ := by ring
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
    calc ‖G x - G y‖ ≤ ‖G x - G y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
      _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ := add_le_add herr le_rfl
      _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
  have approx_lower : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [MeasurableSpace F] [BorelSpace F] (G : Rn n → F) (L : Rn n →L[ℝ] F) (s : Set (Rn n))
      (δ K : ℝ≥0), ApproximatesLinearOn G L s δ → AntilipschitzWith K L → δ * K < 1 →
      ENNReal.ofReal L.toLinearMap.normDet * volume s ≤
        (((1 - δ * K)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n * μHE[n] (G '' s) := by
    intro F _ _ _ _ G L s δ K hG hK hδ
    have hδR : (δ : ℝ) * K < 1 := hδ
    have hdist : ∀ x ∈ s, ∀ y ∈ s,
        dist (L x) (L y) ≤ ((1 - δ * K)⁻¹ : ℝ≥0) * dist (G x) (G y) := by
      intro x hx y hy
      have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
        simpa only [dist_eq_norm] using hK.le_mul_dist x y
      have herr : ‖G x - G y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ := by
        calc ‖G x - G y - (L x - L y)‖ ≤ δ * ‖x - y‖ := by
              simpa only [map_sub] using hG x hx y hy
          _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
          _ = (δ : ℝ) * K * ‖L x - L y‖ := by ring
      have htri : ‖L x - L y‖ ≤ ‖G x - G y‖ + ‖G x - G y - (L x - L y)‖ := by
        simpa only [norm_sub_rev, add_comm] using norm_le_norm_sub_add (L x - L y) (G x - G y)
      rw [dist_eq_norm, dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδ.le, NNReal.coe_one,
        NNReal.coe_mul, inv_mul_eq_div, le_div_iff₀ (sub_pos.mpr hδR)]
      calc ‖L x - L y‖ * (1 - δ * K) = ‖L x - L y‖ - δ * K * ‖L x - L y‖ := by ring
        _ ≤ ‖G x - G y‖ := by linarith
    have hGinj : InjOn G s := by
      intro x hx y hy hxy
      apply hK.injective
      apply dist_le_zero.mp
      simpa only [hxy, dist_self, mul_zero] using hdist x hx y hy
    rw [← linear_area F L.toLinearMap s]
    exact image_cmp F L G s _ hGinj hdist
  -- For injective `L` and `q > 1`, one radius controls the Jacobians and the image measures.
  have approx_radius : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (L : Rn n →L[ℝ] F),
      Function.Injective L → ∀ q : ℝ≥0, 1 < q → ∃ δ : ℝ≥0, 0 < δ ∧
        (∀ B : Rn n →L[ℝ] F, ‖B - L‖ ≤ δ →
          ENNReal.ofReal B.toLinearMap.normDet ≤ q * ENNReal.ofReal L.toLinearMap.normDet ∧
          ENNReal.ofReal L.toLinearMap.normDet ≤ q * ENNReal.ofReal B.toLinearMap.normDet) ∧
        (∀ (t : Set (Rn n)) (G : Rn n → F), ApproximatesLinearOn G L t δ →
          μHE[n] (G '' t) ≤ q * (ENNReal.ofReal L.toLinearMap.normDet * volume t) ∧
          ENNReal.ofReal L.toLinearMap.normDet * volume t ≤ q * μHE[n] (G '' t)) := by
    intro F _ _ _ _ _ L hL q hq
    obtain ⟨K, -, hK⟩ := L.toLinearMap.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hL)
    have hJ : 0 < L.toLinearMap.normDet := lt_of_le_of_ne (LinearMap.normDet_nonneg _)
      (Ne.symm ((L.toLinearMap.normDet_ne_zero_tfae.out 1 5).mpr hL))
    have hqR : (1 : ℝ) < q := hq
    have hmul : L.toLinearMap.normDet < (q : ℝ) * L.toLinearMap.normDet := by
      have := mul_lt_mul_of_pos_right hqR hJ
      rwa [one_mul] at this
    have hnear : ∀ᶠ B : Rn n →L[ℝ] F in 𝓝 L,
        B.toLinearMap.normDet < (q : ℝ) * L.toLinearMap.normDet ∧
          L.toLinearMap.normDet < (q : ℝ) * B.toLinearMap.normDet :=
      ((normDet_cont F).continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul (normDet_cont F).continuousAt) hmul)
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
    have h1 : ∀ᶠ δ : ℝ≥0 in 𝓝 0, δ * K < 1 :=
      (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
    have h2 : ∀ᶠ δ : ℝ≥0 in 𝓝 0, (1 + δ * K) ^ n < q :=
      ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
        continuousAt_const (by simpa using hq)
    have h3 : ∀ᶠ δ : ℝ≥0 in 𝓝 0, ((1 - δ * K)⁻¹) ^ n < q :=
      (((continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).inv₀
        (by simp)).pow _).eventually_lt continuousAt_const (by simpa using hq)
    have h4 : ∀ᶠ δ : ℝ≥0 in 𝓝 0, (δ : ℝ) < ε :=
      NNReal.continuous_coe.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
    obtain ⟨δ, ⟨⟨⟨hδ1, hδ2⟩, hδ3⟩, hδ4⟩, hδ0⟩ :=
      ((((h1.and h2).and h3).and h4).filter_mono nhdsWithin_le_nhds |>.and
        (self_mem_nhdsWithin : Ioi (0 : ℝ≥0) ∈ 𝓝[>] (0 : ℝ≥0))).exists
    refine ⟨δ, hδ0, fun B hB ↦ ?_, fun t G hG ↦ ⟨?_, ?_⟩⟩
    · obtain ⟨hup, hlow⟩ := hnear (show dist B L < ε by rw [dist_eq_norm]; exact hB.trans_lt hδ4)
      constructor
      · simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg q), ENNReal.ofReal_coe_nnreal] using
          ENNReal.ofReal_le_ofReal hup.le
      · simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg q), ENNReal.ofReal_coe_nnreal] using
          ENNReal.ofReal_le_ofReal hlow.le
    · refine (approx_upper F G L t δ K hG hK).trans (mul_le_mul_left ?_ _)
      exact_mod_cast hδ2.le
    · refine (approx_lower F G L t δ K hG hK hδ1).trans (mul_le_mul_left ?_ _)
      exact_mod_cast hδ3.le
  -- At density points, derivatives inherit the bound of a linear approximation.
  have deriv_density : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      (G : Rn n → F) (A : Rn n →L[ℝ] F) (s : Set (Rn n)) (δ : ℝ≥0) (G' : Rn n → Rn n →L[ℝ] F),
      ApproximatesLinearOn G A s δ → MeasurableSet s →
      (∀ x ∈ s, HasFDerivWithinAt G (G' x) s x) →
      ∀ᵐ x ∂(volume.restrict s), ‖G' x - A‖₊ ≤ δ := by
    intro F _ _ G A s δ G' hf hs hf'
    open scoped Pointwise in
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (Rn n)) s,
      ae_restrict_mem hs]
    intro x hx xs
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
    suffices H : ∀ ε, 0 < ε → ‖(G' x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖G' x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖G' x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖G' x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • Metric.closedBall z ε)).Nonempty :=
      Measure.eventually_nonempty_inter_smul_of_density_one volume s x hx _
        measurableSet_closedBall (Metric.measure_closedBall_pos volume z εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ :
        ∃ ρ > 0, Metric.ball x ρ ∩ s ⊆ {y : Rn n | ‖G y - G x - (G' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      Metric.mem_nhdsWithin_iff.1 ((hf' x xs).isLittleO.bound εpos)
    have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • Metric.closedBall z ε ⊆ Metric.ball x ρ := by
      apply nhdsWithin_le_nhds
      exact eventually_singleton_add_smul_subset Metric.isBounded_closedBall
        (Metric.ball_mem_nhds x ρpos)
    obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
        ∃ r : ℝ, (s ∩ ({x} + r • Metric.closedBall z ε)).Nonempty ∧
          {x} + r • Metric.closedBall z ε ⊆ Metric.ball x ρ ∧ 0 < r :=
      (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, az, ya⟩ : ∃ a, a ∈ Metric.closedBall z ε ∧ y = x + r • a := by
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
      rcases hy with ⟨a, az, ha⟩
      exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
      calc
        ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
    have I : r * ‖(G' x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
      calc
        r * ‖(G' x - A) a‖ = ‖(G' x - A) (r • a)‖ := by
          simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖G y - G x - A (y - x) - (G y - G x - (G' x) (y - x))‖ := by
          simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
            Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖G y - G x - A (y - x)‖ + ‖G y - G x - (G' x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := (add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩))
        _ = r * (δ + ε) * ‖a‖ := by
          simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
          ring
        _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
    calc
      ‖(G' x - A) z‖ = ‖(G' x - A) a + (G' x - A) (z - a)‖ := by
        congr 1
        simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
        abel
      _ ≤ ‖(G' x - A) a‖ + ‖(G' x - A) (z - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖G' x - A‖ * ‖z - a‖ := by
        apply add_le_add
        · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
        · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖G' x - A‖ * ε := by
        rw [mem_closedBall_iff_norm'] at az
        gcongr
  -- Simon Ch. 2 (3.2) up to the factor `q²`, on the pieces of a linear-approximation partition.
  have area_cmp : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (s : Set (Rn n)) (G : Rn n → F),
      MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ G x) →
      (∀ x ∈ s, Function.Injective (fderiv ℝ G x)) → InjOn G s → ∀ q : ℝ≥0, 1 < q →
      μHE[n] (G '' s) ≤ (q : ℝ≥0∞) ^ 2 *
          ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet ∧
        ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet ≤
          (q : ℝ≥0∞) ^ 2 * μHE[n] (G '' s) := by
    intro F _ _ _ _ _ s G hs hd hreg hinj q hq
    rcases eq_empty_or_nonempty s with rfl | hsne
    · simp
    classical
    let δ : (Rn n →L[ℝ] F) → ℝ≥0 := fun L ↦
      if hL : Function.Injective L then (approx_radius F L hL q hq).choose else 1
    have hδpos : ∀ L, δ L ≠ 0 := by
      intro L
      by_cases hL : Function.Injective L
      · rw [show δ L = (approx_radius F L hL q hq).choose from dite_eq_left hL]
        exact (approx_radius F L hL q hq).choose_spec.1.ne'
      · rw [show δ L = 1 from dite_eq_right hL]
        exact one_ne_zero
    obtain ⟨t, L, hdisj, ht, hcover, happrox, hactual⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G s (fderiv ℝ G)
        (fun x hx ↦ (hd x hx).hasFDerivAt.hasFDerivWithinAt) δ hδpos
    have hLreg : ∀ i, Function.Injective (L i) := by
      intro i
      obtain ⟨x, hx, hLx⟩ := hactual hsne i
      rw [hLx]
      exact hreg x hx
    have hseq : s = ⋃ i, s ∩ t i := by
      rw [← inter_iUnion]
      exact (inter_eq_left.mpr hcover).symm
    have hcont : ContinuousOn G s := fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt
    have hsumimage : μHE[n] (G '' s) = ∑' i, μHE[n] (G '' (s ∩ t i)) := by
      conv_lhs => rw [hseq, image_iUnion]
      exact measure_iUnion (fun i j hij ↦ Disjoint.image (Disjoint.mono inter_subset_right
        inter_subset_right (hdisj hij)) hinj inter_subset_left inter_subset_left)
        (fun i ↦ (hs.inter (ht i)).image_of_continuousOn_injOn (hcont.mono inter_subset_left)
          (hinj.mono inter_subset_left))
    have hsumint : ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet =
        ∑' i, ∫⁻ x in s ∩ t i, ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet := by
      conv_lhs => rw [hseq]
      exact lintegral_iUnion (fun i ↦ hs.inter (ht i))
        (pairwise_disjoint_mono hdisj fun _ ↦ inter_subset_right) _
    have hpiece : ∀ i, μHE[n] (G '' (s ∩ t i)) ≤ (q : ℝ≥0∞) ^ 2 *
          ∫⁻ x in s ∩ t i, ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet ∧
        ∫⁻ x in s ∩ t i, ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet ≤
          (q : ℝ≥0∞) ^ 2 * μHE[n] (G '' (s ∩ t i)) := by
      intro i
      have hδi : δ (L i) = (approx_radius F (L i) (hLreg i) q hq).choose := dite_eq_left (hLreg i)
      obtain ⟨-, hJ, harea⟩ := (approx_radius F (L i) (hLreg i) q hq).choose_spec
      have happ := happrox i
      rw [hδi] at happ
      obtain ⟨hup, hlow⟩ := harea (s ∩ t i) G happ
      have hder := deriv_density F G (L i) (s ∩ t i) _ (fderiv ℝ G) happ (hs.inter (ht i))
        (fun x hx ↦ (hd x hx.1).hasFDerivAt.hasFDerivWithinAt)
      have hJup : ∫⁻ x in s ∩ t i, ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet ≤
          q * (ENNReal.ofReal (L i).toLinearMap.normDet * volume (s ∩ t i)) := by
        calc _ ≤ ∫⁻ _ in s ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (L i).toLinearMap.normDet := by
              apply lintegral_mono_ae
              filter_upwards [hder] with x hx
              exact (hJ (fderiv ℝ G x) hx).1
          _ = _ := by rw [setLIntegral_const, mul_assoc]
      have hJlow : ENNReal.ofReal (L i).toLinearMap.normDet * volume (s ∩ t i) ≤
          q * ∫⁻ x in s ∩ t i, ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet := by
        calc _ = ∫⁻ _ in s ∩ t i, ENNReal.ofReal (L i).toLinearMap.normDet :=
              (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ x in s ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet := by
              apply lintegral_mono_ae
              filter_upwards [hder] with x hx
              exact (hJ (fderiv ℝ G x) hx).2
          _ = _ := lintegral_const_mul' _ _ ENNReal.coe_ne_top
      constructor
      · calc _ ≤ q * (ENNReal.ofReal (L i).toLinearMap.normDet * volume (s ∩ t i)) := hup
          _ ≤ q * (q * ∫⁻ x in s ∩ t i, ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet) :=
              mul_le_mul_right hJlow _
          _ = _ := by rw [pow_two, mul_assoc]
      · calc _ ≤ q * (ENNReal.ofReal (L i).toLinearMap.normDet * volume (s ∩ t i)) := hJup
          _ ≤ q * (q * μHE[n] (G '' (s ∩ t i))) := mul_le_mul_right hlow _
          _ = _ := by rw [pow_two, mul_assoc]
    rw [hsumimage, hsumint]
    constructor
    · calc _ ≤ ∑' i, (q : ℝ≥0∞) ^ 2 *
            ∫⁻ x in s ∩ t i, ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet :=
            ENNReal.tsum_le_tsum fun i ↦ (hpiece i).1
        _ = _ := ENNReal.tsum_mul_left
    · calc _ ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[n] (G '' (s ∩ t i)) :=
            ENNReal.tsum_le_tsum fun i ↦ (hpiece i).2
        _ = _ := ENNReal.tsum_mul_left
  -- Simon Ch. 2 (3.2) for injective maps with injective derivatives (`q → 1`).
  have area_inj : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (s : Set (Rn n)) (G : Rn n → F),
      MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ G x) →
      (∀ x ∈ s, Function.Injective (fderiv ℝ G x)) → InjOn G s →
      μHE[n] (G '' s) = ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet := by
    intro F _ _ _ _ _ s G hs hd hreg hinj
    have hlim : ∀ a : ℝ≥0∞, Tendsto (fun q : ℝ≥0 ↦ (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      intro a
      have hcoe : Tendsto (fun q : ℝ≥0 ↦ (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlim _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (area_cmp F s G hs hd hreg hinj q hq).1
    · apply ge_of_tendsto (hlim _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (area_cmp F s G hs hd hreg hinj q hq).2
  -- Its weighted form: `Jac · volume⌞s` is carried by `G` to `Hⁿ⌞G(s)`.
  have area_inj_weighted : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (s : Set (Rn n)) (G : Rn n → F),
      MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ G x) →
      (∀ x ∈ s, Function.Injective (fderiv ℝ G x)) → InjOn G s → ∀ φ : F → ℝ≥0∞, Measurable φ →
      ∫⁻ y in G '' s, φ y ∂μHE[n] =
        ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet * φ (G x) := by
    intro F _ _ _ _ _ s G hs hd hreg hinj φ hφ
    classical
    have hcont : ContinuousOn G s := fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt
    have hJm : Measurable (fun x ↦ ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet) :=
      ENNReal.measurable_ofReal.comp ((normDet_cont F).measurable.comp (measurable_fderiv ℝ G))
    have hGm : AEMeasurable G ((volume.restrict s).withDensity
        (fun x ↦ ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet)) :=
      (hcont.aemeasurable hs).mono_ac (withDensity_absolutelyContinuous _ _)
    have hpw : Measurable (s.piecewise G (fun _ ↦ (0 : F))) :=
      hcont.measurable_piecewise continuousOn_const hs
    have hmap : Measure.map G ((volume.restrict s).withDensity
        (fun x ↦ ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet)) =
        (μHE[n] : Measure F).restrict (G '' s) := by
      ext T hT
      have hmeas : MeasurableSet (G ⁻¹' T ∩ s) := by
        have h1 : G ⁻¹' T ∩ s = s.piecewise G (fun _ ↦ (0 : F)) ⁻¹' T ∩ s := by
          ext x
          constructor
          · rintro ⟨hxT, hxs⟩
            exact ⟨by rw [mem_preimage, piecewise_eq_of_mem _ _ _ hxs]; exact hxT, hxs⟩
          · rintro ⟨hxT, hxs⟩
            exact ⟨by rw [mem_preimage, piecewise_eq_of_mem _ _ _ hxs] at hxT; exact hxT, hxs⟩
        rw [h1]
        exact (hpw hT).inter hs
      rw [Measure.map_apply_of_aemeasurable hGm hT, Measure.restrict_apply hT, withDensity_apply' _ _,
        Measure.restrict_restrict' hs, ← area_inj F _ G hmeas (fun x hx ↦ hd x hx.2)
          (fun x hx ↦ hreg x hx.2) (hinj.mono inter_subset_right)]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨hxT, hxs⟩, rfl⟩
        exact ⟨hxT, x, hxs, rfl⟩
      · rintro ⟨hyT, x, hxs, rfl⟩
        exact ⟨x, ⟨hyT, hxs⟩, rfl⟩
    rw [← hmap, lintegral_map' hφ.aemeasurable hGm]
    exact lintegral_withDensity_eq_lintegral_mul₀ (μ := volume.restrict s) hJm.aemeasurable
      (g := fun a ↦ φ (G a)) (hφ.comp_aemeasurable (hcont.aemeasurable hs))
  -- The regular set splits into countably many disjoint Borel injective branches.
  have inj_branches : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F] (s : Set (Rn n)) (G : Rn n → F), MeasurableSet s →
      (∀ x ∈ s, DifferentiableAt ℝ G x) → (∀ x ∈ s, Function.Injective (fderiv ℝ G x)) →
      ∃ t : ℕ → Set (Rn n), (∀ i, MeasurableSet (t i)) ∧ Pairwise (Function.onFun Disjoint t) ∧
        (⋃ i, t i) = s ∧ ∀ i, InjOn G (t i) := by
    intro F _ _ _ s G hs hd hreg
    rcases eq_empty_or_nonempty s with rfl | hsne
    · exact ⟨fun _ ↦ ∅, fun _ ↦ MeasurableSet.empty, fun _ _ _ ↦ disjoint_bot_left,
        iUnion_empty, fun _ ↦ injOn_empty _⟩
    have hchoice : ∀ L : Rn n →L[ℝ] F, ∃ δ : ℝ≥0, 0 < δ ∧ (Function.Injective L →
        ∀ (u : Set (Rn n)) (g : Rn n → F), ApproximatesLinearOn g L u δ → InjOn g u) := by
      intro L
      by_cases hL : Function.Injective L
      · obtain ⟨K, -, hK⟩ := L.toLinearMap.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hL)
        have hK' : AntilipschitzWith K L := hK
        refine ⟨(K + 1)⁻¹, inv_pos.mpr (add_pos_of_nonneg_of_pos K.2 one_pos), fun _ u g hg ↦ ?_⟩
        intro x hx y hy hxy
        have he : ‖L x - L y‖ ≤ ((K + 1)⁻¹ : ℝ≥0) * ‖x - y‖ := by
          simpa only [map_sub, hxy, sub_self, zero_sub, norm_neg] using hg x hx y hy
        have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
          simpa only [dist_eq_norm] using hK'.le_mul_dist x y
        have hK1 : (K : ℝ) * ((K + 1)⁻¹ : ℝ≥0) < 1 := by
          rw [NNReal.coe_inv, NNReal.coe_add, NNReal.coe_one, ← div_eq_mul_inv,
            div_lt_one (by positivity)]
          exact lt_add_one _
        by_contra hne
        have hp : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
        have h1 : ‖x - y‖ ≤ (K : ℝ) * ((K + 1)⁻¹ : ℝ≥0) * ‖x - y‖ := by
          calc ‖x - y‖ ≤ K * ‖L x - L y‖ := hb
            _ ≤ K * (((K + 1)⁻¹ : ℝ≥0) * ‖x - y‖) := mul_le_mul_of_nonneg_left he K.2
            _ = _ := by ring
        have h2 : (K : ℝ) * ((K + 1)⁻¹ : ℝ≥0) * ‖x - y‖ < ‖x - y‖ := by
          simpa only [one_mul] using mul_lt_mul_of_pos_right hK1 hp
        exact (lt_irrefl _ (h1.trans_lt h2))
      · exact ⟨1, zero_lt_one, fun h ↦ (hL h).elim⟩
    choose δ hpos hδ using hchoice
    obtain ⟨t, L, hdisj, ht, hcover, happrox, hactual⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G s (fderiv ℝ G)
        (fun x hx ↦ (hd x hx).hasFDerivAt.hasFDerivWithinAt) δ (fun L ↦ (hpos L).ne')
    refine ⟨fun i ↦ s ∩ t i, fun i ↦ hs.inter (ht i),
      pairwise_disjoint_mono hdisj (fun _ ↦ inter_subset_right), ?_, fun i ↦ ?_⟩
    · rw [← inter_iUnion]
      exact inter_eq_left.mpr hcover
    · obtain ⟨x, hx, heq⟩ := hactual hsne i
      exact hδ (L i) (heq ▸ hreg x hx) _ G (happrox i)
  -- Simon Ch. 2 (3.4)–(3.5) on the regular set, summing over the branches.
  have area_mult_regular : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (s : Set (Rn n)) (G : Rn n → F)
      (w : Rn n → ℝ≥0∞), MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ G x) →
      (∀ x ∈ s, Function.Injective (fderiv ℝ G x)) → Measurable w →
      Measurable (fun y ↦ ∑' x : ↥(s ∩ G ⁻¹' {y}), w x) ∧
      ∫⁻ y, (∑' x : ↥(s ∩ G ⁻¹' {y}), w x) ∂μHE[n] =
        ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet * w x := by
    intro F _ _ _ _ _ s G w hs hd hreg hw
    classical
    obtain ⟨t, ht, hdisj, hcover, hinj⟩ := inj_branches F s G hs hd hreg
    have hts : ∀ i, t i ⊆ s := fun i ↦ hcover ▸ subset_iUnion t i
    have hemb : ∀ i, MeasurableEmbedding ((t i).domRestrict G) := fun i ↦
      ContinuousOn.measurableEmbedding (f := G) (ht i)
        (fun x hx ↦ (hd x (hts i hx)).continuousAt.continuousWithinAt) (hinj i)
    -- the fibre sum over one branch
    have hbr : ∀ i y, (∑' x : ↥(t i ∩ G ⁻¹' {y}), w x) =
        Function.extend ((t i).domRestrict G) (fun x : t i ↦ w x) (fun _ ↦ 0) y := by
      intro i y
      by_cases hy : ∃ a : t i, (t i).domRestrict G a = y
      · obtain ⟨a, rfl⟩ := hy
        rw [(hemb i).injective.extend_apply]
        exact tsum_eq_single (⟨a.1, a.2, rfl⟩ : ↥(t i ∩ G ⁻¹' {(t i).domRestrict G a}))
          fun b hb ↦ absurd (Subtype.ext (hinj i b.2.1 a.2 (show G b.1 = G a.1 from b.2.2))) hb
      · rw [Function.extend_apply' _ _ _ hy]
        exact ENNReal.tsum_eq_zero.mpr fun b ↦ absurd ⟨⟨b.1, b.2.1⟩, b.2.2⟩ hy
    have hbrm : ∀ i, Measurable (fun y ↦ ∑' x : ↥(t i ∩ G ⁻¹' {y}), w x) := by
      intro i
      simp only [hbr]
      exact (hemb i).measurable_extend (hw.comp measurable_subtype_coe) measurable_const
    have hbri : ∀ i, ∫⁻ y, (∑' x : ↥(t i ∩ G ⁻¹' {y}), w x) ∂μHE[n] =
        ∫⁻ x in t i, ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet * w x := by
      intro i
      have hsupp : (Function.support fun y ↦ ∑' x : ↥(t i ∩ G ⁻¹' {y}), w x) ⊆ G '' t i := by
        intro y hy
        by_contra hy'
        apply hy
        exact ENNReal.tsum_eq_zero.mpr fun b ↦ absurd ⟨b.1, b.2.1, b.2.2⟩ hy'
      rw [← setLIntegral_eq_of_support_subset hsupp,
        area_inj_weighted F (t i) G (ht i) (fun x hx ↦ hd x (hts i hx)) (fun x hx ↦ hreg x (hts i hx)) (hinj i)
          _ (hbrm i)]
      refine setLIntegral_congr_fun (ht i) fun x hx ↦ ?_
      congr 1
      exact tsum_eq_single (⟨x, hx, rfl⟩ : ↥(t i ∩ G ⁻¹' {G x}))
        fun b hb ↦ absurd (Subtype.ext (hinj i b.2.1 hx (show G b.1 = G x from b.2.2))) hb
    have hsum : ∀ y, (∑' x : ↥(s ∩ G ⁻¹' {y}), w x) = ∑' i, ∑' x : ↥(t i ∩ G ⁻¹' {y}), w x := by
      intro y
      have he : s ∩ G ⁻¹' {y} = ⋃ i, t i ∩ G ⁻¹' {y} := by
        rw [← iUnion_inter, hcover]
      rw [he]
      exact ENNReal.tsum_biUnion fun i _ j _ hij ↦
        (hdisj hij).mono inter_subset_left inter_subset_left
    simp only [hsum]
    refine ⟨Measurable.tsum hbrm, ?_⟩
    rw [lintegral_tsum fun i ↦ (hbrm i).aemeasurable, ← hcover, lintegral_iUnion ht hdisj]
    exact tsum_congr hbri
  -- Critical points have `Hⁿ`-null image: compare with the graphs `x ↦ (G x, ε x)`, `ε → 0`.
  have crit_null : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (Z : Set (Rn n)) (G : Rn n → F),
      MeasurableSet Z → (∀ x ∈ Z, DifferentiableAt ℝ G x) →
      (∀ x ∈ Z, ¬ Function.Injective (fderiv ℝ G x)) → μHE[n] (G '' Z) = 0 := by
    intro F _ _ _ _ _ Z G hZ hd hcrit
    let e := (WithLp.prodContinuousLinearEquiv 2 ℝ F (Rn n)).symm.toContinuousLinearMap
    obtain ⟨T, hTdef, hTc, hT0⟩ : ∃ T : (Rn n →L[ℝ] F) → ℝ → (Rn n →L[ℝ] WithLp 2 (F × Rn n)),
        (∀ L ε, T L ε = e ∘L (L.prod (ε • ContinuousLinearMap.id ℝ (Rn n)))) ∧
        Continuous (fun p : (Rn n →L[ℝ] F) × ℝ ↦ (T p.1 p.2).toLinearMap.normDet) ∧
        (∀ L : Rn n →L[ℝ] F, ¬ Function.Injective L → (T L 0).toLinearMap.normDet = 0) := by
      refine ⟨fun L ε ↦ e ∘L (L.prod (ε • ContinuousLinearMap.id ℝ (Rn n))), fun _ _ ↦ rfl,
        (normDet_cont (WithLp 2 (F × Rn n))).comp (Continuous.clm_comp continuous_const
          ((ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp
            (continuous_fst.prodMk (continuous_snd.smul continuous_const)))), fun L hL ↦ ?_⟩
      by_contra hne
      apply hL
      intro u v huv
      have hinjT := ((e ∘L (L.prod ((0 : ℝ) • ContinuousLinearMap.id ℝ (Rn n)))).toLinearMap.normDet_ne_zero_tfae.out 1 5).mp hne
      apply hinjT
      show e (L.prod ((0 : ℝ) • ContinuousLinearMap.id ℝ (Rn n)) u) =
        e (L.prod ((0 : ℝ) • ContinuousLinearMap.id ℝ (Rn n)) v)
      simp only [ContinuousLinearMap.prod_apply, huv, FunLike.coe_smul, Pi.smul_apply, zero_smul]
    have hpiece : ∀ Y ⊆ Z, MeasurableSet Y → volume Y ≠ ⊤ → ∀ B : ℝ,
        (∀ x ∈ Y, ‖fderiv ℝ G x‖ ≤ B) → μHE[n] (G '' Y) = 0 := by
      intro Y hYZ hY hYfin B hB
      obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : Rn n →L[ℝ] F) B).prod
        (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))).exists_bound_of_continuousOn
          hTc.continuousOn
      have hbound : ∀ ε : ℝ, ε ≠ 0 → μHE[n] (G '' Y) ≤ ((2 : ℝ≥0) : ℝ≥0∞) ^ 2 *
          ∫⁻ x in Y, ENNReal.ofReal (T (fderiv ℝ G x) ε).toLinearMap.normDet := by
        intro ε hε
        have hGε : ∀ x ∈ Y, HasFDerivAt (fun x ↦ e (G x, ε • x)) (T (fderiv ℝ G x) ε) x := by
          intro x hx
          rw [hTdef]
          exact e.hasFDerivAt.comp x
            ((hd x (hYZ hx)).hasFDerivAt.prodMk ((hasFDerivAt_id x).const_smul ε))
        have hinjε : Function.Injective (fun x : Rn n ↦ e (G x, ε • x)) := by
          intro u v huv
          have h1 := congrArg (fun z ↦ ((WithLp.prodContinuousLinearEquiv 2 ℝ F (Rn n)) z).2) huv
          simp only [e, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at h1
          exact smul_right_injective (Rn n) hε h1
        have hTinj : ∀ x, Function.Injective (T (fderiv ℝ G x) ε) := by
          intro x u v huv
          rw [hTdef] at huv
          have h1 := congrArg (fun z ↦ ((WithLp.prodContinuousLinearEquiv 2 ℝ F (Rn n)) z).2) huv
          simp only [e, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
            ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.prod_apply,
            FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply] at h1
          exact smul_right_injective (Rn n) hε h1
        have hproj : μHE[n] (G '' Y) ≤ μHE[n] ((fun x ↦ e (G x, ε • x)) '' Y) := by
          have hp : LipschitzWith 1
              (fun z : WithLp 2 (F × Rn n) ↦ (WithLp.prodContinuousLinearEquiv 2 ℝ F (Rn n) z).1) :=
            LipschitzWith.of_dist_le_mul fun a b ↦ by simpa using WithLp.dist_fst_le a b
          have h1 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hp.lipschitzOnWith (s := (fun x ↦ e (G x, ε • x)) '' Y))
          rw [image_image, ENNReal.coe_one, one_pow, one_mul] at h1
          simpa only [e, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
            using h1
        have hc := (area_cmp (WithLp 2 (F × Rn n)) Y (fun x ↦ e (G x, ε • x)) hY
          (fun x hx ↦ (hGε x hx).differentiableAt)
          (fun x hx ↦ by rw [(hGε x hx).fderiv]; exact hTinj x)
          hinjε.injOn 2 (by norm_num)).1
        refine hproj.trans (hc.trans_eq ?_)
        congr 1
        exact setLIntegral_congr_fun hY fun x hx ↦ by rw [(hGε x hx).fderiv]
      have hmeas : ∀ ε : ℝ, Measurable
          (fun x ↦ ENNReal.ofReal (T (fderiv ℝ G x) ε).toLinearMap.normDet) := fun ε ↦
        ENNReal.measurable_ofReal.comp ((hTc.comp (continuous_id.prodMk continuous_const)).measurable.comp
          (measurable_fderiv ℝ G))
      have hlim : Tendsto (fun ε : ℝ ↦
          ∫⁻ x in Y, ENNReal.ofReal (T (fderiv ℝ G x) ε).toLinearMap.normDet) (𝓝 0) (𝓝 0) := by
        have h1 := tendsto_lintegral_filter_of_dominated_convergence (μ := volume.restrict Y)
          (l := 𝓝 (0 : ℝ))
          (F := fun ε x ↦ ENNReal.ofReal (T (fderiv ℝ G x) ε).toLinearMap.normDet) (f := fun _ ↦ 0)
          (fun _ ↦ ENNReal.ofReal C) (Eventually.of_forall hmeas) ?_ ?_ ?_
        · simpa only [lintegral_zero] using h1
        · filter_upwards [Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
            with ε hε
          filter_upwards [ae_restrict_mem hY] with x hx
          exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC ⟨fderiv ℝ G x, ε⟩
            ⟨mem_closedBall_zero_iff.mpr (hB x hx), hε⟩))
        · rw [lintegral_const, Measure.restrict_apply_univ]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYfin
        · filter_upwards [ae_restrict_mem hY] with x hx
          have h2 : Continuous (fun ε : ℝ ↦
              ENNReal.ofReal (T (fderiv ℝ G x) ε).toLinearMap.normDet) :=
            ENNReal.continuous_ofReal.comp
              (hTc.comp ((continuous_const (y := fderiv ℝ G x)).prodMk continuous_id))
          exact h2.tendsto' 0 0 (by
            show ENNReal.ofReal (T (fderiv ℝ G x) 0).toLinearMap.normDet = 0
            rw [hT0 _ (hcrit x (hYZ hx)), ENNReal.ofReal_zero])
      apply le_antisymm _ bot_le
      have hlim' := ENNReal.Tendsto.const_mul (a := ((2 : ℝ≥0) : ℝ≥0∞) ^ 2)
        (hlim.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))) (Or.inr (by simp))
      rw [mul_zero] at hlim'
      exact ge_of_tendsto hlim' (eventually_nhdsWithin_of_forall fun ε hε ↦ hbound ε hε)
    let t : ℕ → Set (Rn n) := fun k ↦ Z ∩ Metric.closedBall 0 k ∩ {x | ‖fderiv ℝ G x‖ ≤ k}
    have ht : ∀ k, MeasurableSet (t k) := fun k ↦ (hZ.inter measurableSet_closedBall).inter
      (measurableSet_le (measurable_fderiv ℝ G).norm measurable_const)
    have hcover : Z ⊆ ⋃ k, t k := by
      intro x hx
      obtain ⟨k, hk⟩ := exists_nat_gt (max ‖x‖ ‖fderiv ℝ G x‖)
      exact mem_iUnion.mpr ⟨k, ⟨hx, mem_closedBall_zero_iff.mpr ((le_max_left _ _).trans hk.le)⟩,
        (le_max_right _ _).trans hk.le⟩
    apply measure_mono_null (image_mono hcover)
    rw [image_iUnion]
    exact measure_iUnion_null fun k ↦ hpiece (t k) (fun x hx ↦ hx.1.1) (ht k)
      (ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono fun x hx ↦ hx.1.2)) k
      (fun x hx ↦ hx.2)
  -- Simon Ch. 2 (3.5) for maps Lipschitz on a null-measurable set and differentiable a.e.
  have area_mult : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (A : Set (Rn n)) (G : Rn n → F)
      (K : ℝ≥0) (w : Rn n → ℝ≥0∞), NullMeasurableSet A volume → LipschitzOnWith K G A →
      (∀ᵐ x ∂volume, x ∈ A → DifferentiableAt ℝ G x) → AEMeasurable w (volume.restrict A) →
      AEMeasurable (fun y ↦ ∑' x : ↥(A ∩ G ⁻¹' {y}), w x) μHE[n] ∧
      ∫⁻ y, (∑' x : ↥(A ∩ G ⁻¹' {y}), w x) ∂μHE[n] =
        ∫⁻ x in A, ENNReal.ofReal (fderiv ℝ G x).toLinearMap.normDet * w x := by
    intro F _ _ _ _ _ A G K w hA hL hdA hw
    obtain ⟨A₁, hA₁A, hA₁m, hA₁ae⟩ := hA.exists_measurable_subset_ae_eq
    have hJm : Measurable (fun x ↦ (fderiv ℝ G x).toLinearMap.normDet) :=
      (normDet_cont F).measurable.comp (measurable_fderiv ℝ G)
    obtain ⟨R, hRm, hR⟩ : ∃ R : Set (Rn n), MeasurableSet R ∧ ∀ x, x ∈ R ↔
        (x ∈ A₁ ∧ DifferentiableAt ℝ G x) ∧ (fderiv ℝ G x).toLinearMap.normDet ≠ 0 :=
      ⟨_, (hA₁m.inter (measurableSet_of_differentiableAt ℝ G)).inter
        (hJm (measurableSet_singleton 0)).compl, fun _ ↦ Iff.rfl⟩
    obtain ⟨Z, hZm, hZ⟩ : ∃ Z : Set (Rn n), MeasurableSet Z ∧ ∀ x, x ∈ Z ↔
        (x ∈ A₁ ∧ DifferentiableAt ℝ G x) ∧ (fderiv ℝ G x).toLinearMap.normDet = 0 :=
      ⟨_, (hA₁m.inter (measurableSet_of_differentiableAt ℝ G)).inter
        (hJm (measurableSet_singleton 0)), fun _ ↦ Iff.rfl⟩
    have hgood : ∀ᵐ x ∂volume, x ∈ A → (x ∈ A₁ ∧ DifferentiableAt ℝ G x) ∧ w x = hw.mk w x := by
      filter_upwards [hA₁ae.mem_iff, hdA, (ae_restrict_iff'₀ hA).mp hw.ae_eq_mk]
        with x h1 h2 h3 hx
      exact ⟨⟨h1.mpr hx, h2 hx⟩, h3 hx⟩
    obtain ⟨N, hNA, hN0, hNdef⟩ : ∃ N : Set (Rn n), N ⊆ A ∧ volume N = 0 ∧ ∀ x ∈ A, x ∉ N →
        (x ∈ A₁ ∧ DifferentiableAt ℝ G x) ∧ w x = hw.mk w x :=
      ⟨{x | ¬ (x ∈ A → (x ∈ A₁ ∧ DifferentiableAt ℝ G x) ∧ w x = hw.mk w x)},
        fun x hx ↦ (not_imp.mp hx).1, ae_iff.mp hgood, fun x hxA hxN ↦ (not_not.mp hxN) hxA⟩
    have hGN : μHE[n] (G '' N) = 0 := by
      have h1 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hL.mono hNA)
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hN0, mul_zero] at h1
      exact le_antisymm h1 bot_le
    have hGZ := crit_null F Z G hZm (fun x hx ↦ ((hZ x).mp hx).1.2) fun x hx hi ↦
      (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp ((hZ x).mp hx).2) (LinearMap.ker_eq_bot.mpr hi)
    obtain ⟨hmeasR, hintR⟩ := area_mult_regular F R G (hw.mk w) hRm (fun x hx ↦ ((hR x).mp hx).1.2)
      (fun x hx ↦ LinearMap.ker_eq_bot.mp (not_not.mp fun hk ↦
        ((hR x).mp hx).2 (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hk)))
      hw.measurable_mk
    have hfib : (fun y ↦ ∑' x : ↥(A ∩ G ⁻¹' {y}), w x) =ᵐ[μHE[n]]
        fun y ↦ ∑' x : ↥(R ∩ G ⁻¹' {y}), hw.mk w x := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_union_null hGN hGZ)] with y hy
      have hset : A ∩ G ⁻¹' {y} = R ∩ G ⁻¹' {y} := by
        ext x
        constructor
        · rintro ⟨hxA, hxy⟩
          have hxN := hNdef x hxA fun hxN' ↦ hy (Or.inl ⟨x, hxN', hxy⟩)
          exact ⟨(hR x).mpr ⟨hxN.1, fun h0 ↦ hy (Or.inr ⟨x, (hZ x).mpr ⟨hxN.1, h0⟩, hxy⟩)⟩, hxy⟩
        · rintro ⟨hxR, hxy⟩
          exact ⟨hA₁A ((hR x).mp hxR).1.1, hxy⟩
      rw [hset]
      exact tsum_congr fun x ↦ (hNdef x.1 (hA₁A ((hR x.1).mp x.2.1).1.1)
        fun hxN' ↦ hy (Or.inl ⟨x.1, hxN', x.2.2⟩)).2
    refine ⟨hmeasR.aemeasurable.congr hfib.symm, ?_⟩
    rw [lintegral_congr_ae hfib, hintR, ← inter_eq_left.mpr (fun x hx ↦ hA₁A ((hR x).mp hx).1.1),
      ← setLIntegral_indicator hRm]
    refine lintegral_congr_ae ?_
    filter_upwards [(ae_restrict_iff'₀ hA).mpr hgood] with x hx
    by_cases hxR : x ∈ R
    · rw [indicator_of_mem hxR, hx.2]
    · rw [indicator_of_notMem hxR, not_not.mp fun h0 ↦ hxR ((hR x).mpr ⟨hx.1, h0⟩),
        ENNReal.ofReal_zero, zero_mul]
  -- Simon Ch. 2 (3.2) in integral form for the injective map `ψ` on the open set `B`.
  intro N B ψ K hB hLip hinj g hg
  set J : Rn n → ℝ := fun v ↦ (fderiv ℝ ψ v).toLinearMap.normDet with hJdef
  have hJmeas : Measurable J := (normDet_cont (Rn N)).measurable.comp (measurable_fderiv ℝ ψ)
  set j : Rn n → ℝ≥0 := fun v ↦ (J v).toNNReal with hjdef
  have hjmeas : Measurable j := hJmeas.real_toNNReal
  set ν : Measure (Rn n) := (volume.restrict B).withDensity (fun v ↦ (j v : ℝ≥0∞)) with hνdef
  have hψcont : ContinuousOn ψ B := hLip.continuousOn
  have hBmeas : MeasurableSet B := hB.measurableSet
  have hψae : AEMeasurable ψ (volume.restrict B) := hψcont.aemeasurable hBmeas
  have hψν : AEMeasurable ψ ν := hψae.mono_ac (withDensity_absolutelyContinuous _ _)
  -- Lusin–Souslin: the injective continuous image `ψ(B)` of the Borel set `B` is Borel.
  have hΓ : MeasurableSet (ψ '' B) := hBmeas.image_of_continuousOn_injOn hψcont hinj
  -- Rademacher: `ψ` is differentiable at almost every point of the open set `B`.
  have hdiff : ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ B → DifferentiableAt ℝ ψ x := by
    filter_upwards [hLip.ae_differentiableWithinAt_of_mem (μ := volume)] with x hx hxB
    exact (hx hxB).differentiableAt (hB.mem_nhds hxB)
  -- `Hⁿ⌞ψ(B) = ψ_# ν`, tested on Borel sets `E`.
  have hmeas : (μHE[n] : Measure (Rn N)).restrict (ψ '' B) = Measure.map ψ ν := by
    ext E hE
    rw [Measure.restrict_apply hE, Measure.map_apply_of_aemeasurable hψν hE, hνdef,
      withDensity_apply' _ _]
    have hw : AEMeasurable (fun v ↦ E.indicator (1 : Rn N → ℝ≥0∞) (ψ v)) (volume.restrict B) :=
      (measurable_one.indicator hE).comp_aemeasurable hψae
    -- Simon (3.5) with the weight `1_E ∘ ψ`.
    have harea : ∫⁻ y, (∑' x : ↥(B ∩ ψ ⁻¹' {y}), E.indicator (1 : Rn N → ℝ≥0∞) (ψ x)) ∂μHE[n] =
        ∫⁻ x in B, ENNReal.ofReal (fderiv ℝ ψ x).toLinearMap.normDet *
          E.indicator (1 : Rn N → ℝ≥0∞) (ψ x) :=
      (area_mult (Rn N) B ψ K _ hBmeas.nullMeasurableSet hLip hdiff hw).2
    -- By injectivity, the fibre sum is the indicator of `E ∩ ψ(B)`.
    have hfib : ∀ y, (∑' x : ↥(B ∩ ψ ⁻¹' {y}), E.indicator (1 : Rn N → ℝ≥0∞) (ψ x)) =
        (E ∩ ψ '' B).indicator 1 y := by
      intro y
      by_cases hy : y ∈ ψ '' B
      · obtain ⟨v, hv, rfl⟩ := hy
        rw [tsum_eq_single (⟨v, hv, rfl⟩ : ↥(B ∩ ψ ⁻¹' {ψ v})) fun b hb ↦
          absurd (Subtype.ext (hinj b.2.1 hv (show ψ b.1 = ψ v from b.2.2))) hb]
        show E.indicator (1 : Rn N → ℝ≥0∞) (ψ v) = _
        by_cases hvE : ψ v ∈ E
        · rw [indicator_of_mem hvE,
            indicator_of_mem (show ψ v ∈ E ∩ ψ '' B from ⟨hvE, v, hv, rfl⟩)]
        · rw [indicator_of_notMem hvE,
            indicator_of_notMem (show ψ v ∉ E ∩ ψ '' B from fun h ↦ hvE h.1)]
      · rw [indicator_of_notMem (show y ∉ E ∩ ψ '' B from fun h ↦ hy h.2)]
        exact ENNReal.tsum_eq_zero.mpr fun b ↦ absurd ⟨b.1, b.2.1, b.2.2⟩ hy
    rw [lintegral_congr hfib, lintegral_indicator_one (hE.inter hΓ)] at harea
    rw [harea, ← lintegral_indicator₀ (hψae.nullMeasurable hE)]
    refine setLIntegral_congr_fun hBmeas fun x _ ↦ ?_
    by_cases hxE : ψ x ∈ E
    · rw [indicator_of_mem hxE, indicator_of_mem (show x ∈ ψ ⁻¹' E from hxE)]
      simp [hjdef, hJdef, ENNReal.ofReal]
    · rw [indicator_of_notMem hxE, indicator_of_notMem (show x ∉ ψ ⁻¹' E from hxE)]
      simp
  -- Change of variables for `ψ_# ν`, then integration against the density `Jψ`.
  rw [hmeas, integral_map hψν hg.aestronglyMeasurable, hνdef,
    integral_withDensity_eq_integral_smul hjmeas]
  congr 1
  funext v
  rw [NNReal.smul_def, smul_eq_mul, hjdef]
  simp only
  rw [Real.coe_toNNReal _ (LinearMap.normDet_nonneg _), mul_comm]

/-- **Blow-up limit of a pulled-back chart integral** (Simon Ch. 3, proof of Theorem 1.6 "⇒" and
Remark 1.5(2), `chapter-03.txt` lines 87–90 and 113–143, for a single bi-Lipschitz `C¹` chart):
let `B ⊆ ℝⁿ` be open, `ψ` `C¹` and `K`-Lipschitz on `B` with `c|u - u'| ≤ |ψ(u) - ψ(u')|`
(`c > 0`) on `B`, and `Jψ(v) = normDet(Dψ(v))`. Then for `u ∈ B` and `f ∈ C_c(ℝᴺ)`,
`r⁻ⁿ ∫_B f(η_{ψ(u),r}(ψ(v))) Jψ(v) dv → Jψ(u) ∫_{ℝⁿ} f(Dψ(u) y) dy` as `r ↓ 0`. The substitution
`v = u + r y` turns the left side into `∫ G_r` with
`G_r(y) = 1_B(u + r y) f(r⁻¹(ψ(u + r y) - ψ(u))) Jψ(u + r y)`. If `f(z) ≠ 0` forces `|z| ≤ R`, the
lower bound gives `G_r = 0` off `B̄_{R/c}(0)`, and `|G_r| ≤ (sup |f|) Kⁿ` by
`Submission.chartTD_chart_fderiv_bounds` and `Submission.chartTD_normDet_le_opNorm_pow`. Since
`G_r(y) → f(Dψ(u) y) Jψ(u)` pointwise (`Dψ` and `normDet` are continuous), dominated convergence
applies. -/
theorem Submission.chartTD_chart_blowup_integral_tendsto : ∀ (n N : ℕ) (B : Set (Rn n))
    (ψ : Rn n → Rn N) (K : ℝ≥0) (c : ℝ), IsOpen B → ContDiffOn ℝ 1 ψ B →
    LipschitzOnWith K ψ B → 0 < c → (∀ u ∈ B, ∀ u' ∈ B, c * ‖u - u'‖ ≤ ‖ψ u - ψ u'‖) →
    ∀ u ∈ B, ∀ f : C_c(Rn N, ℝ),
      Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ v in B, f (blowUpMap (ψ u) r (ψ v)) *
          (fderiv ℝ ψ v).toLinearMap.normDet) (𝓝[>] 0)
        (𝓝 ((fderiv ℝ ψ u).toLinearMap.normDet * ∫ y, f (fderiv ℝ ψ u y))) := by
  intro n N B ψ K c hB hψ hLip hc hlow u hu f
  set J : Rn n → ℝ := fun v => (fderiv ℝ ψ v).toLinearMap.normDet with hJdef
  set L := fderiv ℝ ψ u with hLdef
  have hBmeas : MeasurableSet B := hB.measurableSet
  -- Step 1: `normDet = √det(A* ∘ A)` is continuous, so `J = normDet ∘ Dψ` is Borel and continuous
  -- at `u`; `0 ≤ J ≤ Kⁿ` on `B`; `ψ` is continuous on `B` and has derivative `L` at `u`.
  have hND : Continuous (fun A : Rn n →L[ℝ] Rn N ↦ A.toLinearMap.normDet) := by
    have key : ∀ A : Rn n →L[ℝ] Rn N, A.toLinearMap.normDet =
        Real.sqrt ((ContinuousLinearMap.adjoint A ∘L A).det) := by
      intro A
      rw [← A.normDet_sq]
      simp [Real.sqrt_sq (LinearMap.normDet_nonneg _)]
    simp_rw [key]
    exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id))
  have hJmeas : Measurable J := hND.measurable.comp (measurable_fderiv ℝ ψ)
  have hJnn : ∀ v, 0 ≤ J v := fun v => LinearMap.normDet_nonneg _
  have hJle : ∀ v ∈ B, J v ≤ (K : ℝ) ^ n := fun v hv =>
    (Submission.chartTD_normDet_le_opNorm_pow n N _).trans
      (pow_le_pow_left₀ (norm_nonneg _)
        (Submission.chartTD_chart_fderiv_bounds n N B ψ K c hB hψ hLip hlow v hv).1 n)
  have hJcont : ContinuousAt J u := by
    have h1 : ContinuousAt (fderiv ℝ ψ) u :=
      (hψ.continuousOn_fderiv_of_isOpen hB le_rfl).continuousAt (hB.mem_nhds hu)
    exact hND.continuousAt.comp h1
  have hψcont : ContinuousOn ψ B := hLip.continuousOn
  have hd : HasFDerivAt ψ L u :=
    ((hψ.differentiableOn one_ne_zero).differentiableAt (hB.mem_nhds hu)).hasFDerivAt
  -- Step 2: `|f| ≤ M` everywhere, and `f z ≠ 0` forces `‖z‖ ≤ R`.
  obtain ⟨M, hM⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  obtain ⟨R, hR⟩ : ∃ R, ∀ z, f z ≠ 0 → ‖z‖ ≤ R := by
    obtain ⟨R, hR⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
    exact ⟨R, fun z hz => by simpa using hR (subset_tsupport _ hz)⟩
  -- Step 3: the substitution `v = u + r y`: `r⁻ⁿ ∫_B h_r = ∫ G_r` for every `r > 0`.
  let h : ℝ → Rn n → ℝ := fun r v => f (blowUpMap (ψ u) r (ψ v)) * J v
  let G : ℝ → Rn n → ℝ := fun r y => B.indicator (h r) (u + r • y)
  have hsub : ∀ r : ℝ, 0 < r →
      (r ^ n)⁻¹ * ∫ v in B, f (blowUpMap (ψ u) r (ψ v)) * J v = ∫ y, G r y := by
    intro r hr
    rw [← integral_indicator hBmeas]
    have h1 := Measure.integral_comp_smul (volume : Measure (Rn n))
      (fun y => B.indicator (h r) (u + y)) r
    rw [integral_add_left_eq_self (fun y => B.indicator (h r) y) u] at h1
    rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hr n)), smul_eq_mul] at h1
    exact h1.symm
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- Step 4: dominated convergence with the bound `M Kⁿ 1_{B̄_{R/c}(0)}`.
  have hDCT : Tendsto (fun r => ∫ y, G r y) (𝓝[>] 0) (𝓝 (∫ y, f (L y) * J u)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => (Metric.closedBall (0 : Rn n) (R / c)).indicator (fun _ => M * (K : ℝ) ^ n) y)
      ?_ ?_ ?_ ?_
    · -- `G_r = 1_{S_r} · (h_r ∘ (u + r •))` with `S_r = {y | u + r y ∈ B}` open.
      filter_upwards [self_mem_nhdsWithin] with r hr
      have haff : Continuous (fun y : Rn n => u + r • y) := by fun_prop
      set S : Set (Rn n) := (fun y : Rn n => u + r • y) ⁻¹' B with hSdef
      have hSopen : IsOpen S := hB.preimage haff
      have hGS : G r = S.indicator (fun y => h r (u + r • y)) := by
        funext y
        by_cases hy : u + r • y ∈ B
        · simp [G, S, Set.indicator_of_mem, hy]
        · simp [G, S, Set.indicator_of_notMem, hy]
      rw [hGS, aestronglyMeasurable_indicator_iff hSopen.measurableSet]
      have h1 : ContinuousOn (fun y : Rn n => f (blowUpMap (ψ u) r (ψ (u + r • y)))) S := by
        have hb : Continuous (fun z : Rn N => blowUpMap (ψ u) r z) := by
          unfold blowUpMap; fun_prop
        exact (f.continuous.comp hb).comp_continuousOn
          (hψcont.comp haff.continuousOn (fun y hy => hy))
      have h2 : Measurable (fun y : Rn n => J (u + r • y)) := hJmeas.comp haff.measurable
      exact (h1.aestronglyMeasurable hSopen.measurableSet).mul
        h2.aestronglyMeasurable.restrict
    · -- If `G_r(y) ≠ 0` then `c r ‖y‖ ≤ ‖ψ(u + r y) - ψ(u)‖ ≤ r R`, so `‖y‖ ≤ R / c`.
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : (0:ℝ) < r := hr
      refine Eventually.of_forall (fun y => ?_)
      by_cases hy : u + r • y ∈ B
      · have hGy : G r y = f (blowUpMap (ψ u) r (ψ (u + r • y))) * J (u + r • y) := by
          simp [G, h, Set.indicator_of_mem, hy]
        rw [hGy]
        by_cases hf0 : f (blowUpMap (ψ u) r (ψ (u + r • y))) = 0
        · rw [hf0, zero_mul, norm_zero]
          exact Set.indicator_nonneg (fun _ _ => by positivity) _
        · have hRb := hR _ hf0
          have hyball : y ∈ Metric.closedBall (0 : Rn n) (R / c) := by
            rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hc]
            have h1 := hlow (u + r • y) hy u hu
            rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr'.le] at h1
            unfold blowUpMap at hRb
            rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr'.le)] at hRb
            have h2 : ‖ψ (u + r • y) - ψ u‖ ≤ r * R := by
              rw [inv_mul_le_iff₀ hr'] at hRb; linarith
            nlinarith
          rw [Set.indicator_of_mem hyball, norm_mul, Real.norm_of_nonneg (hJnn _)]
          exact mul_le_mul (hM _) (hJle _ hy) (hJnn _) hM0
      · have hGy : G r y = 0 := by simp [G, Set.indicator_of_notMem, hy]
        rw [hGy, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => by positivity) _
    · exact (integrableOn_const (measure_closedBall_lt_top (x := (0 : Rn n))
        (r := R / c)).ne).integrable_indicator measurableSet_closedBall
    · -- Pointwise: eventually `u + r y ∈ B`, `r⁻¹(ψ(u + r y) - ψ(u)) → L y`, `J(u + r y) → J(u)`.
      refine Eventually.of_forall (fun y => ?_)
      have hlin : Tendsto (fun r : ℝ => u + r • y) (𝓝[>] 0) (𝓝 u) := by
        have : Tendsto (fun r : ℝ => u + r • y) (𝓝 0) (𝓝 (u + (0:ℝ) • y)) :=
          ((continuous_const.add (continuous_id.smul continuous_const)).tendsto 0)
        simpa using this.mono_left nhdsWithin_le_nhds
      have hevB : ∀ᶠ r in 𝓝[>] (0:ℝ), u + r • y ∈ B := hlin (hB.mem_nhds hu)
      have hq : Tendsto (fun r : ℝ => blowUpMap (ψ u) r (ψ (u + r • y))) (𝓝[>] 0)
          (𝓝 (L y)) := by
        have := hd.lim y (c := fun r : ℝ => r⁻¹) (l := 𝓝[>] (0:ℝ)) (by
          refine (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).congr' ?_
          filter_upwards [self_mem_nhdsWithin] with t ht
          simp [abs_of_pos (show (0:ℝ) < t from ht)])
        simpa [blowUpMap, inv_inv] using this
      have hlim : Tendsto (fun r : ℝ => f (blowUpMap (ψ u) r (ψ (u + r • y))) * J (u + r • y))
          (𝓝[>] 0) (𝓝 (f (L y) * J u)) :=
        ((f.continuous.tendsto _).comp hq).mul (hJcont.tendsto.comp hlin)
      refine hlim.congr' ?_
      filter_upwards [hevB] with r hr
      simp [G, h, Set.indicator_of_mem, hr]
  -- Step 5: `∫ f(L y) J(u) dy = J(u) ∫ f(L y) dy`, and the two sides agree for `r > 0`.
  rw [integral_mul_const, mul_comm] at hDCT
  refine hDCT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hsub r hr).symm

/-- **Vanishing normalized density of `|w|` kills the normalized blow-up integrals of `f w`**
(Simon Ch. 3, proof of Theorem 1.6 "⇒", `chapter-03.txt` lines 127–140, with a weight `w` as in
Remark 1.8(1), lines 298–306): if `w` is `Hⁿ`-integrable on `S ∩ B_ρ(x)` for every `ρ > 0` and
`ρ⁻ⁿ ∫_{S ∩ B_ρ(x)} |w| dHⁿ → 0` as `ρ ↓ 0`, then `r⁻ⁿ ∫_S f(η_{x,r}(z)) w(z) dHⁿ(z) → 0` as
`r ↓ 0` for every `f ∈ C_c(ℝᴺ, ℝ)`. With `|f| ≤ C` and `f(y) = 0` for `‖y‖ ≥ R`, the integrand
vanishes off `B_{Rr}(x)`, so `|∫_S f(η_{x,r}(z)) w(z) dHⁿ(z)| ≤ C ∫_{S ∩ B_{Rr}(x)} |w| dHⁿ`
(`setIntegral_indicator`, `norm_integral_le_of_norm_le`), and the normalized integral is at most
`C Rⁿ · (Rr)⁻ⁿ ∫_{S ∩ B_{Rr}(x)} |w| dHⁿ → 0`. -/
theorem Submission.chartTD_blowup_integral_tendsto_zero : ∀ (n N : ℕ) (S : Set (Rn N)) (w : Rn N → ℝ) (x : Rn N), (∀ ρ : ℝ, 0 < ρ → IntegrableOn w (S ∩ Metric.ball x ρ) μHE[n]) → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ z in S ∩ Metric.ball x ρ, |w z| ∂μHE[n]) (𝓝[>] 0) (𝓝 0) → ∀ f : C_c(Rn N, ℝ), Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ z in S, f (blowUpMap x r z) * w z ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
  intro n N S w x hw hlim f
  -- `|f| ≤ C`, and `f y = 0` whenever `R ≤ ‖y‖`, for some `R > 0`.
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
  -- For `r > 0` the integrand vanishes off `B_{Rr}(x)`, which gives
  -- `|∫_S f(η_{x,r}(z)) w(z) dHⁿ(z)| ≤ C ∫_{S ∩ B_{Rr}(x)} |w| dHⁿ`.
  have hbound : ∀ r : ℝ, 0 < r → ‖∫ z in S, f (blowUpMap x r z) * w z ∂μHE[n]‖ ≤
      C * ∫ z in S ∩ Metric.ball x (R * r), |w z| ∂μHE[n] := by
    intro r hr
    have hloc : (fun z ↦ f (blowUpMap x r z) * w z) =
        (Metric.ball x (R * r)).indicator (fun z ↦ f (blowUpMap x r z) * w z) := by
      funext z
      by_cases hz : z ∈ Metric.ball x (R * r)
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]
        rw [Metric.mem_ball, not_lt, dist_eq_norm] at hz
        have hRz : R ≤ ‖blowUpMap x r z‖ := by
          rw [blowUpMap, norm_smul, norm_inv, Real.norm_of_nonneg hr.le, le_inv_mul_iff₀' hr]
          exact hz
        rw [hfR _ hRz, zero_mul]
    rw [hloc, setIntegral_indicator measurableSet_ball]
    calc ‖∫ z in S ∩ Metric.ball x (R * r), f (blowUpMap x r z) * w z ∂μHE[n]‖
        ≤ ∫ z in S ∩ Metric.ball x (R * r), C * |w z| ∂μHE[n] := by
          refine norm_integral_le_of_norm_le ((hw _ (mul_pos hR hr)).abs.const_mul C)
            (Eventually.of_forall fun z ↦ ?_)
          rw [norm_mul, Real.norm_eq_abs (w z)]
          exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _)
      _ = C * ∫ z in S ∩ Metric.ball x (R * r), |w z| ∂μHE[n] := integral_const_mul C _
  -- `r ↦ Rr` maps `𝓝[>] 0` into itself, so `C Rⁿ · (Rr)⁻ⁿ ∫_{S ∩ B_{Rr}(x)} |w| dHⁿ → 0`.
  have hRr : Tendsto (fun r : ℝ ↦ R * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Tendsto (fun r : ℝ ↦ R * r) (𝓝 0) (𝓝 (R * 0)) := tendsto_id.const_mul R
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hR hr
  have hmaj : Tendsto (fun r : ℝ ↦ C * R ^ n *
      (((R * r) ^ n)⁻¹ * ∫ z in S ∩ Metric.ball x (R * r), |w z| ∂μHE[n])) (𝓝[>] 0) (𝓝 0) := by
    have h := (hlim.comp hRr).const_mul (C * R ^ n)
    rw [mul_zero] at h
    exact h
  -- Squeeze: `|r⁻ⁿ ∫_S f(η_{x,r}(z)) w(z) dHⁿ(z)| ≤ C Rⁿ · (Rr)⁻ⁿ ∫_{S ∩ B_{Rr}(x)} |w| dHⁿ`.
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hrn : 0 < r ^ n := pow_pos hr n
  have hRn : 0 < R ^ n := pow_pos hR n
  rw [norm_mul, norm_inv, norm_pow, Real.norm_of_nonneg hr.le]
  calc (r ^ n)⁻¹ * ‖∫ z in S, f (blowUpMap x r z) * w z ∂μHE[n]‖
      ≤ (r ^ n)⁻¹ * (C * ∫ z in S ∩ Metric.ball x (R * r), |w z| ∂μHE[n]) :=
        mul_le_mul_of_nonneg_left (hbound r hr) (inv_nonneg.mpr hrn.le)
    _ = C * R ^ n * (((R * r) ^ n)⁻¹ * ∫ z in S ∩ Metric.ball x (R * r), |w z| ∂μHE[n]) := by
        rw [mul_pow]
        field_simp

/-- **Splitting the localized weighted blow-up integral along a comparison set** (the
decomposition in Simon Ch. 3, proof of Theorem 1.6 "⇒", `chapter-03.txt` lines 116–120, in the
weighted form of Def. 1.7 and Remark 1.8(1), lines 284–306). Let `M`, `Γ` be `Hⁿ`-measurable with
`Hⁿ(Γ) < ∞`, `θ` a positive locally integrable weight on `M`, `f ∈ C_c(ℝᴺ, ℝ)`, `r > 0` and
`g = f ∘ η_{x,r}`. Then
`∫_M g θ = ∫_{M ∖ Γ} g θ + θ(x) (∫_Γ g - ∫_{Γ ∖ M} g) + ∫_{M ∩ Γ} g (θ - θ(x))`.
`g` is continuous, `|g| ≤ C`, and `g = 0` off the closed ball `K = B̄_{r R₀}(x)`, where
`tsupport f ⊆ B_{R₀}(0)`. So `|g θ| ≤ 1_K C |θ|` makes `g θ` integrable on `M`, and `g` is
integrable on `Γ`. The identity follows from `integral_inter_add_sdiff₀` (splitting `∫_M g θ` along
`Γ` and `∫_Γ g` along `M`) and linearity on `M ∩ Γ`. -/
theorem Submission.chartTD_weighted_blowup_integral_split : ∀ (n N : ℕ) (M Γ : Set (Rn N)) (θ : Rn N → ℝ) (x : Rn N) (f : C_c(Rn N, ℝ)) (r : ℝ), 0 < r → NullMeasurableSet M μHE[n] → NullMeasurableSet Γ μHE[n] → μHE[n] Γ < ∞ → IsPositiveLocallyIntegrableWeight n M θ → ∫ z in M, f (blowUpMap x r z) * θ z ∂μHE[n] = ∫ z in M \ Γ, f (blowUpMap x r z) * θ z ∂μHE[n] + θ x * (∫ z in Γ, f (blowUpMap x r z) ∂μHE[n] - ∫ z in Γ \ M, f (blowUpMap x r z) ∂μHE[n]) + ∫ z in M ∩ Γ, f (blowUpMap x r z) * (θ z - θ x) ∂μHE[n] := by
  intro n N M Γ θ x f r hr hM hΓ hΓfin hθ
  obtain ⟨-, hθmeas, hθint⟩ := hθ
  -- Step 1: `g = f ∘ η_{x,r}` is continuous, `|g| ≤ C`, and `g = 0` off `K = B̄_{r R₀}(x)`
  have hη : Continuous (blowUpMap x r) := by
    unfold blowUpMap
    fun_prop
  have hgc : Continuous fun z ↦ f (blowUpMap x r z) := f.continuous.comp hη
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_ball (0 : Rn N)
  set K := Metric.closedBall x (r * R₀)
  have hgK : ∀ z, f (blowUpMap x r z) ≠ 0 → z ∈ K := by
    intro z hz
    have hball : blowUpMap x r z ∈ Metric.ball (0 : Rn N) R₀ := hR₀ (subset_tsupport _ hz)
    rw [mem_ball_zero_iff, blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
      inv_mul_lt_iff₀ hr] at hball
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hball.le
  -- Step 2: `g θ` is `Hⁿ ⌞ M`-integrable, dominated by `1_K C |θ|`
  have h1 : IntegrableOn (fun z ↦ f (blowUpMap x r z) * θ z) M μHE[n] := by
    have hmaj : IntegrableOn (K.indicator fun z ↦ C * ‖θ z‖) M μHE[n] := by
      rw [IntegrableOn, integrable_indicator_iff Metric.isClosed_closedBall.measurableSet,
        IntegrableOn, Measure.restrict_restrict Metric.isClosed_closedBall.measurableSet,
        inter_comm]
      exact (hθint K (isCompact_closedBall x _)).norm.const_mul C
    refine Integrable.mono' hmaj (hgc.aestronglyMeasurable.mul hθmeas.aestronglyMeasurable) ?_
    refine Eventually.of_forall fun z ↦ ?_
    by_cases hz : f (blowUpMap x r z) = 0
    · rw [hz, zero_mul, norm_zero]
      exact indicator_nonneg (fun _ _ ↦ mul_nonneg ((norm_nonneg _).trans (hC 0))
        (norm_nonneg _)) z
    · rw [indicator_of_mem (hgK z hz), norm_mul]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  -- Step 3: `g` is `Hⁿ ⌞ Γ`-integrable (bounded and continuous, `Hⁿ(Γ) < ∞`)
  have h2 : IntegrableOn (fun z ↦ f (blowUpMap x r z)) Γ μHE[n] :=
    IntegrableOn.of_bound hΓfin hgc.aestronglyMeasurable C (Eventually.of_forall fun z ↦ hC _)
  -- Step 4: `g θ` and `g` are integrable on `M ∩ Γ`
  have h1' := h1.mono_set (inter_subset_left : M ∩ Γ ⊆ M)
  have h2' := h2.mono_set (inter_subset_right : M ∩ Γ ⊆ Γ)
  -- Step 5: split `∫_M g θ` along `Γ` and `∫_Γ g` along `M`; linearity on `M ∩ Γ`
  have hA := integral_inter_add_sdiff₀ hΓ h1
  have hB := integral_inter_add_sdiff₀ hM h2
  rw [inter_comm Γ M] at hB
  have hD : ∫ z in M ∩ Γ, f (blowUpMap x r z) * (θ z - θ x) ∂μHE[n] =
      ∫ z in M ∩ Γ, f (blowUpMap x r z) * θ z ∂μHE[n] -
        θ x * ∫ z in M ∩ Γ, f (blowUpMap x r z) ∂μHE[n] := by
    rw [← integral_const_mul, ← integral_sub h1' (h2'.const_mul _)]
    congr 1
    funext z
    ring
  -- Step 6: substitute and rearrange
  rw [hD, ← hB, ← hA]
  ring

/-- **Change of variables for blow-ups** (Simon Ch. 3, proof of Theorem 1.6 "⇒",
`chapter-03.txt` lines 113–143, esp. line 133; Def. 1.7, lines 284–295): for `r > 0`, every set
`A` and every `g`, `∫_{η_{x,r}(A)} g dHⁿ = r⁻ⁿ ∫_A g ∘ η_{x,r} dHⁿ`. The map
`η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` is a measurable equivalence with `Hⁿ(η⁻¹(T)) = rⁿ Hⁿ(T)` for
every `T` (translation invariance and `euclideanHausdorffMeasure_smul₀`), so
`η_#(Hⁿ⌞A) = rⁿ Hⁿ⌞η(A)`; conclude by `integral_map_equiv` and `integral_smul_nnreal_measure`. -/
theorem Submission.chartTD_setIntegral_blowUpMap_image : ∀ (N n : ℕ) (x : Rn N) (r : ℝ), 0 < r → ∀ (A : Set (Rn N)) (g : Rn N → ℝ), ∫ y in blowUpMap x r '' A, g y ∂μHE[n] = (r ^ n)⁻¹ * ∫ z in A, g (blowUpMap x r z) ∂μHE[n] := by
  intro N n x r hr A g
  -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` as a measurable equivalence of `ℝᴺ`.
  set e : Rn N ≃ᵐ Rn N :=
    (MeasurableEquiv.subRight x).trans (MeasurableEquiv.smul₀ r⁻¹ (inv_ne_zero hr.ne'))
  have he : ⇑e = blowUpMap x r := rfl
  -- Scaling: `Hⁿ(η⁻¹(T)) = rⁿ Hⁿ(T)` for every set `T`, since `η⁻¹(T) = r • T + x`.
  have hmap : (μHE[n] : Measure (Rn N)).map e = (‖r‖₊ ^ n) • μHE[n] := by
    ext T -
    have hT : ⇑e ⁻¹' T = (fun y ↦ y + -x) ⁻¹' ((fun z ↦ r⁻¹ • z) ⁻¹' T) := by
      ext y
      simp [he, blowUpMap, sub_eq_add_neg]
    rw [e.map_apply, Measure.smul_apply, hT, measure_preimage_add_right,
      preimage_smul_inv₀ hr.ne', Measure.euclideanHausdorffMeasure_smul₀ n hr.ne']
  -- Hence `η_#(Hⁿ⌞A) = rⁿ Hⁿ⌞η(A)`, as `η⁻¹(η(A)) = A`.
  have hres : ((μHE[n] : Measure (Rn N)).restrict A).map e =
      (‖r‖₊ ^ n) • (μHE[n] : Measure (Rn N)).restrict (e '' A) := by
    rw [← Measure.restrict_smul, ← hmap, e.restrict_map, e.preimage_image]
  have hint : ∫ z in A, g (blowUpMap x r z) ∂μHE[n] =
      r ^ n * ∫ y in blowUpMap x r '' A, g y ∂μHE[n] := by
    rw [← he, ← integral_map_equiv, hres, integral_smul_nnreal_measure, NNReal.smul_def,
      NNReal.coe_pow, coe_nnnorm, Real.norm_of_nonneg hr.le, smul_eq_mul]
  rw [hint, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hr.ne'), one_mul]

/-- **`C¹` immersions are locally bi-Lipschitz**, the localization step behind the local
representation of `C¹` immersions (Simon Ch. 2, §4): if `ψ` is `C¹` on the open set `V ⊆ ℝⁿ`
and `Dψ(u)` is injective for every `u ∈ V`, then each `u₀ ∈ V` has a ball `B_r(u₀) ⊆ V` on
which `ψ` is `K`-Lipschitz and `c |u - u'| ≤ |ψ(u) - ψ(u')|` for some `c > 0`. The injective
`L = Dψ(u₀)` satisfies `c₀ |v| ≤ |L v|` (`LinearMap.exists_antilipschitzWith`); continuity of
`Dψ` gives `‖Dψ(u) - L‖ ≤ c₀/2` on a small ball, and the mean value inequality on the convex
ball, applied to `ψ` and to `ψ - L`, gives `K = ‖L‖ + c₀/2` and `c = c₀/2`. -/
theorem Submission.chartTD_immersion_local_biLipschitz : ∀ (n N : ℕ) (V : Set (Rn n))
    (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 1 ψ V →
    (∀ u ∈ V, Function.Injective (fderiv ℝ ψ u)) → ∀ u₀ ∈ V, ∃ r : ℝ, 0 < r ∧
      Metric.ball u₀ r ⊆ V ∧ ∃ (K : ℝ≥0) (c : ℝ), 0 < c ∧ LipschitzOnWith K ψ (Metric.ball u₀ r) ∧
        ∀ u ∈ Metric.ball u₀ r, ∀ u' ∈ Metric.ball u₀ r, c * ‖u - u'‖ ≤ ‖ψ u - ψ u'‖ := by
  intro n N V ψ hV hψ hinj u₀ hu₀
  -- Step 1: `ψ` is differentiable on the open set `V` and `Dψ` is continuous there.
  have hdiff : ∀ u ∈ V, DifferentiableAt ℝ ψ u := fun u hu ↦
    (hψ.differentiableOn_one u hu).differentiableAt (hV.mem_nhds hu)
  have hcont : ContinuousOn (fderiv ℝ ψ) V := hψ.continuousOn_fderiv_of_isOpen hV le_rfl
  -- Step 2: `L = Dψ(u₀)` is injective, hence bounded below: `c₀ ‖v‖ ≤ ‖L v‖` with `c₀ = A⁻¹`.
  set L := fderiv ℝ ψ u₀ with hL_def
  obtain ⟨A, hA, hAL⟩ := (L : Rn n →ₗ[ℝ] Rn N).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 (hinj u₀ hu₀))
  have hA' : (0 : ℝ) < A := NNReal.coe_pos.2 hA
  have hc₀ : 0 < (A : ℝ)⁻¹ := inv_pos.2 hA'
  have hlow : ∀ v, (A : ℝ)⁻¹ * ‖v‖ ≤ ‖L v‖ := by
    intro v
    have h := hAL.le_mul_dist v 0
    simp only [dist_zero_right, map_zero, ContinuousLinearMap.coe_coe] at h
    rw [inv_mul_le_iff₀ hA']
    exact h
  -- Step 3: choose `r` with `B_r(u₀) ⊆ V` and `‖Dψ(u) - L‖ ≤ c₀/2` on `B_r(u₀)`.
  have hev : ∀ᶠ u in 𝓝 u₀, u ∈ V ∧ ‖fderiv ℝ ψ u - L‖ ≤ (A : ℝ)⁻¹ / 2 := by
    refine (hV.eventually_mem hu₀).and ?_
    filter_upwards [(hcont.continuousAt (hV.mem_nhds hu₀)).eventually_mem
      (Metric.closedBall_mem_nhds L (half_pos hc₀))] with u hu
    rwa [Metric.mem_closedBall, dist_eq_norm] at hu
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  -- Step 4: `‖Dψ(u)‖ ≤ ‖L‖ + c₀/2` on `B_r(u₀)`.
  have hC : 0 ≤ ‖L‖ + (A : ℝ)⁻¹ / 2 := add_nonneg (norm_nonneg _) (half_pos hc₀).le
  have hbound : ∀ u ∈ Metric.ball u₀ r, ‖fderiv ℝ ψ u‖ ≤ ‖L‖ + (A : ℝ)⁻¹ / 2 := fun u hu ↦
    calc ‖fderiv ℝ ψ u‖ = ‖L + (fderiv ℝ ψ u - L)‖ := by congr 1; abel
      _ ≤ ‖L‖ + ‖fderiv ℝ ψ u - L‖ := norm_add_le _ _
      _ ≤ ‖L‖ + (A : ℝ)⁻¹ / 2 := by linarith [(hball u hu).2]
  refine ⟨r, hr, fun u hu ↦ (hball u hu).1, (‖L‖ + (A : ℝ)⁻¹ / 2).toNNReal, (A : ℝ)⁻¹ / 2,
    half_pos hc₀, ?_, ?_⟩
  · -- Step 5: mean value inequality on the convex ball.
    rw [lipschitzOnWith_iff_norm_sub_le, Real.coe_toNNReal _ hC]
    intro x hx y hy
    exact (convex_ball u₀ r).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (fun u hu ↦ hdiff u (hball u hu).1) hbound hy hx
  · -- Step 6: mean value inequality for `ψ - L`, then the lower bound for `L`.
    intro u hu u' hu'
    have hmv := (convex_ball u₀ r).norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ) (φ := L)
      (fun x hx ↦ hdiff x (hball x hx).1) (fun x hx ↦ (hball x hx).2) hu' hu
    have h2 := hlow (u - u')
    have h3 : ‖L (u - u')‖ ≤ ‖ψ u - ψ u'‖ + ‖ψ u - ψ u' - L (u - u')‖ := by
      calc ‖L (u - u')‖ = ‖(ψ u - ψ u') - (ψ u - ψ u' - L (u - u'))‖ := by congr 1; abel
        _ ≤ ‖ψ u - ψ u'‖ + ‖ψ u - ψ u' - L (u - u')‖ := norm_sub_le _ _
    linarith

/-- **Measure-theoretic facts for a bi-Lipschitz image of a bounded open set** (parent
`root.chart_tangent_differential-a1`, Step 2, (Σ1)–(Σ3); Simon Ch. 2, Theorem 1.8(i)). Let
`B ⊆ ℝⁿ` be open and bounded, `ψ : ℝⁿ → ℝᴺ` `K`-Lipschitz on `B` with
`c |u - u'| ≤ |ψ u - ψ u'|` on `B` (`c > 0`), and `Γ = ψ(B)`. Then `Γ` is `Hⁿ`-measurable and
bounded, `Hⁿ(Γ) < ∞`, `Hⁿ(Γ ∩ B̄_ρ(x)) ≤ C ρⁿ` for `x ∈ Γ`, `ρ > 0`, and `B ∩ ψ⁻¹(Z)` is
`Lⁿ`-null whenever `Hⁿ(Z) = 0`. The bounds follow from `Hⁿ(φ(E)) ≤ Λⁿ Hⁿ(E)` for `Λ`-Lipschitz
`φ` (SimonGMT `euclideanHausdorffMeasure_image_le_of_lipschitzOn`) and `Hⁿ = Lⁿ` on `ℝⁿ`, applied
to `ψ` and to the `c⁻¹`-Lipschitz inverse of `ψ|_B`; measurability is Lusin–Souslin. -/
theorem Submission.chartTD_biLipschitz_image_measure_facts : ∀ (n N : ℕ) (B : Set (Rn n))
    (ψ : Rn n → Rn N) (K : ℝ≥0) (c : ℝ), IsOpen B → Bornology.IsBounded B →
    LipschitzOnWith K ψ B → 0 < c → (∀ u ∈ B, ∀ u' ∈ B, c * ‖u - u'‖ ≤ ‖ψ u - ψ u'‖) →
    NullMeasurableSet (ψ '' B) μHE[n] ∧ Bornology.IsBounded (ψ '' B) ∧ μHE[n] (ψ '' B) < ∞ ∧
      (∃ C : ℝ, ∀ x ∈ ψ '' B, ∀ ρ : ℝ, 0 < ρ →
        μHE[n] (ψ '' B ∩ Metric.closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) ∧
      ∀ Z : Set (Rn N), μHE[n] Z = 0 → volume (B ∩ ψ ⁻¹' Z) = 0 := by
  intro n N B ψ K c hBo hBb hψ hc hlow
  -- `Hⁿ = Lⁿ` on `ℝⁿ`.
  have hHE : (μHE[n] : Measure (Rn n)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
  -- Since `c > 0`, the lower bound makes `ψ` injective on `B`.
  have hinj : InjOn ψ B := by
    intro u hu u' hu' h
    have h1 := hlow u hu u' hu'
    rw [h, sub_self, norm_zero] at h1
    have h2 : ‖u - u'‖ ≤ 0 := le_of_mul_le_mul_left (by rwa [mul_zero]) hc
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  -- (F2) for `ψ` on subsets `A ⊆ B`: `Hⁿ(ψ(A)) ≤ Kⁿ Lⁿ(A)`.
  have hF2 : ∀ A ⊆ B, μHE[n] (ψ '' A) ≤ (K : ℝ≥0∞) ^ n * volume A := by
    intro A hA
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hψ.mono hA)
    rwa [hHE] at h
  -- (i) Lusin–Souslin: `ψ` is continuous and injective on the Borel set `B`, so `Γ` is Borel.
  refine ⟨(hBo.measurableSet.image_of_continuousOn_injOn hψ.continuousOn hinj).nullMeasurableSet,
    ?_, ?_, ?_, ?_⟩
  -- (ii) `|ψ u - ψ u'| ≤ K |u - u'| ≤ K R` on `B`.
  · obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp hBb
    refine Metric.isBounded_iff.mpr ⟨K * R, ?_⟩
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    calc dist (ψ u) (ψ u') ≤ K * dist u u' := hψ.dist_le_mul u hu u' hu'
      _ ≤ K * R := mul_le_mul_of_nonneg_left (hR hu hu') K.coe_nonneg
  -- (iii) `Hⁿ(Γ) ≤ Kⁿ Lⁿ(B) < ∞`.
  · calc μHE[n] (ψ '' B) ≤ (K : ℝ≥0∞) ^ n * volume B := hF2 B subset_rfl
      _ < ∞ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hBb.measure_lt_top
  -- (iv) `C = Kⁿ ω_n c⁻ⁿ`: `Γ ∩ B̄_ρ(ψ u) ⊆ ψ(B ∩ B̄_{ρ/c}(u))` and `Lⁿ(B̄_s(u)) = sⁿ ω_n`.
  · set V : ℝ := (volume (Metric.ball (0 : Rn n) 1)).toReal with hV
    refine ⟨(K : ℝ) ^ n * V * c⁻¹ ^ n, ?_⟩
    rintro _ ⟨u, hu, rfl⟩ ρ hρ
    have hsub : ψ '' B ∩ Metric.closedBall (ψ u) ρ ⊆ ψ '' (B ∩ Metric.closedBall u (ρ / c)) := by
      rintro _ ⟨⟨u', hu', rfl⟩, hy⟩
      refine ⟨u', ⟨hu', ?_⟩, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
      rw [le_div_iff₀ hc]
      have := hlow u' hu' u hu
      linarith
    have hball : volume (Metric.ball (0 : Rn n) 1) = ENNReal.ofReal V := by
      rw [hV, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
    calc μHE[n] (ψ '' B ∩ Metric.closedBall (ψ u) ρ)
        ≤ μHE[n] (ψ '' (B ∩ Metric.closedBall u (ρ / c))) := measure_mono hsub
      _ ≤ (K : ℝ≥0∞) ^ n * volume (B ∩ Metric.closedBall u (ρ / c)) := hF2 _ inter_subset_left
      _ ≤ (K : ℝ≥0∞) ^ n * volume (Metric.closedBall u (ρ / c)) := by
          gcongr; exact inter_subset_right
      _ = (K : ℝ≥0∞) ^ n * (ENNReal.ofReal ((ρ / c) ^ n) * ENNReal.ofReal V) := by
          rw [Measure.addHaar_closedBall _ _ (div_pos hρ hc).le, finrank_euclideanSpace_fin, hball]
      _ = ENNReal.ofReal ((K : ℝ) ^ n * ((ρ / c) ^ n * V)) := by
          rw [ENNReal.ofReal_mul (pow_nonneg K.coe_nonneg n),
            ENNReal.ofReal_mul (pow_nonneg (div_pos hρ hc).le n), ENNReal.ofReal_pow K.coe_nonneg,
            ENNReal.ofReal_coe_nnreal]
      _ = ENNReal.ofReal ((K : ℝ) ^ n * V * c⁻¹ ^ n * ρ ^ n) := by
          congr 1
          rw [div_pow, div_eq_mul_inv, inv_pow]
          ring
  -- (v) The inverse `φ` of `ψ|_B` is `c⁻¹`-Lipschitz on `Γ` and `B ∩ ψ⁻¹(Z) ⊆ φ(Γ ∩ Z)`, so
  -- `Lⁿ(B ∩ ψ⁻¹(Z)) ≤ c⁻ⁿ Hⁿ(Γ ∩ Z) = 0`.
  · intro Z hZ
    have hleft : LeftInvOn (Function.invFunOn ψ B) ψ B := hinj.leftInvOn_invFunOn
    have hφ : LipschitzOnWith (Real.toNNReal c⁻¹) (Function.invFunOn ψ B) (ψ '' B) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
      rw [hleft hu, hleft hu', Real.coe_toNNReal _ (inv_nonneg.mpr hc.le), dist_eq_norm,
        dist_eq_norm, inv_mul_eq_div, le_div_iff₀ hc]
      linarith [hlow u hu u' hu']
    have hsub : B ∩ ψ ⁻¹' Z ⊆ Function.invFunOn ψ B '' (ψ '' B ∩ Z) := by
      rintro u ⟨hu, hZu⟩
      exact ⟨ψ u, ⟨mem_image_of_mem ψ hu, hZu⟩, hleft hu⟩
    have h1 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hφ.mono (inter_subset_left : ψ '' B ∩ Z ⊆ ψ '' B))
    rw [hHE] at h1
    refine nonpos_iff_eq_zero.mp ?_
    calc volume (B ∩ ψ ⁻¹' Z)
        ≤ volume (Function.invFunOn ψ B '' (ψ '' B ∩ Z)) := measure_mono hsub
      _ ≤ (Real.toNNReal c⁻¹ : ℝ≥0∞) ^ n * μHE[n] (ψ '' B ∩ Z) := h1
      _ ≤ (Real.toNNReal c⁻¹ : ℝ≥0∞) ^ n * μHE[n] Z := by gcongr; exact inter_subset_right
      _ = 0 := by rw [hZ, mul_zero]

/-- **Approximate tangent space of a bi-Lipschitz `C¹` chart** (Simon Ch. 3, Remark 1.5(2) and
the proof of Theorem 1.6 "⇒", `chapter-03.txt` lines 87–90 and 113–143, esp. lines 122–126): if
`ψ` is `C¹` and `K`-Lipschitz on the open set `B ⊆ ℝⁿ` with `c|u - u'| ≤ |ψ(u) - ψ(u')|` there
(`c > 0`), then at every `u ∈ B` the image `ψ(B)` has approximate tangent space
`T = range Dψ(u)`. As `c|w| ≤ |Dψ(u) w|`, `Dψ(u)` is injective and `finrank T = n`. For `r > 0`
the blow-up scaling and the area formula on `B` give `∫_{η_{ψ(u),r}(ψ(B))} f dHⁿ =
r⁻ⁿ ∫_B f(η_{ψ(u),r}(ψ(v))) Jψ(v) dv`, which tends to `Jψ(u) ∫ f(Dψ(u) y) dy`; the area formula
for the injective linear map `Dψ(u)` on `ℝⁿ` identifies this limit with `∫_T f dHⁿ`. -/
theorem Submission.chartTD_biLipschitz_chart_approx_tangent : ∀ (n N : ℕ) (B : Set (Rn n)) (ψ : Rn n → Rn N) (K : ℝ≥0) (c : ℝ), IsOpen B → ContDiffOn ℝ 1 ψ B → LipschitzOnWith K ψ B → 0 < c → (∀ u ∈ B, ∀ u' ∈ B, c * ‖u - u'‖ ≤ ‖ψ u - ψ u'‖) → ∀ u ∈ B, HasApproximateTangentSpaceAt n (ψ '' B) (ψ u) (LinearMap.range (fderiv ℝ ψ u).toLinearMap) := by
  intro n N B ψ K c hB hψ hK hc hlow u hu
  -- Since `c > 0`, `c‖x‖ ≤ 0` forces `x = 0`.
  have hzero : ∀ x : Rn n, c * ‖x‖ ≤ 0 → x = 0 := fun x hx ↦
    norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right hx hc)
  -- `c‖w‖ ≤ ‖Dψ(u) w‖` makes `Dψ(u)` injective, and the lower bound makes `ψ` injective on `B`.
  have hLinj : Function.Injective (fderiv ℝ ψ u) := fun w w' hww' ↦ by
    have h := (Submission.chartTD_chart_fderiv_bounds n N B ψ K c hB hψ hK hlow u hu).2 (w - w')
    rw [map_sub, hww', sub_self, norm_zero] at h
    exact sub_eq_zero.1 (hzero _ h)
  have hinj : InjOn ψ B := fun v hv v' hv' hvv' ↦ by
    have h := hlow v hv v' hv'
    rw [hvv', sub_self, norm_zero] at h
    exact sub_eq_zero.1 (hzero _ h)
  refine ⟨by rw [LinearMap.finrank_range_of_inj (f := (fderiv ℝ ψ u).toLinearMap) hLinj,
    finrank_euclideanSpace_fin], fun f ↦ ?_⟩
  -- The area formula for `Dψ(u)` on `ℝⁿ`, whose Jacobian is the constant `Jψ(u)`:
  -- `∫_T f dHⁿ = Jψ(u) ∫ f(Dψ(u) y) dy`.
  have hT : ∫ y in (LinearMap.range (fderiv ℝ ψ u).toLinearMap : Set (Rn N)), f y ∂μHE[n] =
      (fderiv ℝ ψ u).toLinearMap.normDet * ∫ y, f (fderiv ℝ ψ u y) := by
    have h := Submission.chartTD_injective_area_setIntegral n N univ (fderiv ℝ ψ u)
      ‖fderiv ℝ ψ u‖₊ isOpen_univ (fderiv ℝ ψ u).lipschitzWith.lipschitzOnWith hLinj.injOn f
      (map_continuous f)
    simp only [image_univ, Measure.restrict_univ, ContinuousLinearMap.fderiv] at h
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe, h, integral_mul_const, mul_comm]
  rw [hT]
  -- For `r > 0`, the blow-up scaling and the area formula on `B` with `g = f ∘ η_{ψ(u),r}` turn
  -- `∫_{η_{ψ(u),r}(ψ(B))} f dHⁿ` into the blown-up chart integral, whose limit is known.
  refine (Submission.chartTD_chart_blowup_integral_tendsto n N B ψ K c hB hψ hK hc hlow u hu
    f).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hg : Continuous fun z ↦ f (blowUpMap (ψ u) r z) := by
    unfold blowUpMap
    fun_prop
  rw [Submission.chartTD_setIntegral_blowUpMap_image N n (ψ u) r hr (ψ '' B) f,
    Submission.chartTD_injective_area_setIntegral n N B ψ K hB hK hinj _ hg]

/-- **Upper density theorem for `|w| Hⁿ⌞A`** (Simon Ch. 1, Theorem 3.6 and Remark 3.7(2),
`chapter-01.txt` lines 700–721, by the covering argument of the proof of Theorem 3.3, lines
666–698): if `A` is `Hⁿ`-measurable and `w` is `Hⁿ`-integrable on `A ∩ K` for every compact `K`,
then `ρ⁻ⁿ ∫_{A ∩ B_ρ(x)} |w| dHⁿ → 0` as `ρ ↓ 0` for `Hⁿ`-a.e. `x ∉ A`. Take a Borel `A₀ ⊆ A`
with `Hⁿ(A ∖ A₀) = 0` and `ν = |w| Hⁿ⌞A₀`, which is finite on compact sets, hence outer regular:
`ν(U) < ε` for some open `U ⊇ ℝᴺ ∖ A₀` (Simon uses the closed `ℝᴺ ∖ U ⊆ A₀`). The points
`x ∉ A₀` with `ν(B̄_ρ(x)) ≥ ρⁿ/(k+1)` for arbitrarily small `ρ` are covered finely by such balls
inside `U`; the 5r-covering lemma gives disjoint ones with `∑ (10ρⱼ)ⁿ ≤ 10ⁿ (k+1) ν(U)`, so this
set is `Hⁿ`-null (only nullity is needed, so the non-sharp constant `10ⁿ` suffices). Off these
null sets, `∫_{A ∩ B_ρ(x)} |w| dHⁿ ≤ ν(B̄_ρ(x))`. -/
theorem Submission.chartTD_upper_density_zero_ae : ∀ (n N : ℕ) (A : Set (Rn N)) (w : Rn N → ℝ), NullMeasurableSet A μHE[n] → (∀ K : Set (Rn N), IsCompact K → IntegrableOn w (A ∩ K) μHE[n]) → ∀ᵐ x ∂(μHE[n] : Measure (Rn N)), x ∉ A → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ z in A ∩ Metric.ball x ρ, |w z| ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
  intro n N A w hA hw
  -- A Borel kernel `A₀ ⊆ A` with `Hⁿ(A ∖ A₀) = 0`.
  obtain ⟨A₀, hA₀A, hA₀, hA₀ae⟩ := hA.exists_measurable_subset_ae_eq
  -- The weighted measure `ν = |w| Hⁿ⌞A₀`: concentrated on `A₀` and finite on compact sets.
  set ν : Measure (Rn N) :=
    ((μHE[n] : Measure (Rn N)).restrict A₀).withDensity (fun z ↦ ‖w z‖ₑ) with hν
  have hνapp : ∀ s : Set (Rn N), MeasurableSet s →
      ν s = ∫⁻ z in s ∩ A₀, ‖w z‖ₑ ∂(μHE[n] : Measure (Rn N)) := by
    intro s hs
    rw [hν, withDensity_apply _ hs, Measure.restrict_restrict hs]
  have hνA₀ : ν A₀ᶜ = 0 := by
    rw [hνapp _ hA₀.compl, compl_inter_self, Measure.restrict_empty, lintegral_zero_measure]
  have : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => by
    rw [hνapp K hK.isClosed.measurableSet]
    exact (lintegral_mono_set (s := K ∩ A₀) (t := A ∩ K) fun z hz => ⟨hA₀A hz.2, hz.1⟩).trans_lt
      (hw K hK).2⟩
  -- `S k`: the points `x ∉ A₀` with `ν(B̄_ρ(x)) ≥ ρⁿ/(k+1)` for arbitrarily small `ρ > 0`.
  set S : ℕ → Set (Rn N) := fun k ↦ {x | x ∉ A₀ ∧ ∀ δ > 0, ∃ ρ ∈ Ioo (0 : ℝ) δ,
    ENNReal.ofReal (((k : ℝ) + 1)⁻¹ * ρ ^ n) ≤ ν (Metric.closedBall x ρ)} with hS
  -- Simon 3.3/3.6: each `S k` is `Hⁿ`-null.
  have hSH : ∀ k, (μH[(n : ℝ)] : Measure (Rn N)) (S k) = 0 := by
    intro k
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
    rw [zero_add]
    -- An open `U ⊇ ℝᴺ ∖ A₀` with `ν(U) < ε / (10ⁿ (k+1))` (outer regularity, `ν(ℝᴺ ∖ A₀) = 0`).
    obtain ⟨U, hUA, hUo, hUν⟩ := Set.exists_isOpen_lt_of_lt (μ := ν) A₀ᶜ
      (ENNReal.ofReal (((k : ℝ) + 1)⁻¹ * ε / 10 ^ n))
      (by rw [hνA₀]; exact ENNReal.ofReal_pos.2 (by positivity))
    -- At every scale `1/(m+1)`, the 5r-covering lemma applied to the balls `B̄_ρ(x) ⊆ U`,
    -- `x ∈ S k`, `ρ < 1/(m+1)`, `ν(B̄_ρ(x)) ≥ ρⁿ/(k+1)` gives a countable disjoint
    -- subfamily whose 5-fold enlargements cover `S k`.
    have hcov : ∀ m : ℕ, ∃ u : Set (Rn N × ℝ), u.Countable ∧
        (∀ b ∈ u, 0 < b.2 ∧ b.2 < ((m : ℝ) + 1)⁻¹) ∧
        S k ⊆ (⋃ b : u, Metric.closedBall b.1.1 (5 * b.1.2)) ∧
        ∑' b : u, ENNReal.ofReal (((k : ℝ) + 1)⁻¹ * b.1.2 ^ n) ≤
          ENNReal.ofReal (((k : ℝ) + 1)⁻¹ * ε / 10 ^ n) := by
      intro m
      let B : Set (Rn N × ℝ) := {b | b.1 ∈ S k ∧ 0 < b.2 ∧ b.2 < ((m : ℝ) + 1)⁻¹ ∧
        Metric.closedBall b.1 b.2 ⊆ U ∧
        ENNReal.ofReal (((k : ℝ) + 1)⁻¹ * b.2 ^ n) ≤ ν (Metric.closedBall b.1 b.2)}
      obtain ⟨u, huB, hudisj, hucov⟩ :=
        Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall B Prod.fst Prod.snd
          ((m : ℝ) + 1)⁻¹ (fun b hb => hb.2.2.1.le) 5 (by norm_num)
      have hucount : u.Countable := hudisj.countable_of_nonempty_interior fun b hb =>
        ⟨b.1, mem_interior_iff_mem_nhds.2 (Metric.closedBall_mem_nhds _ (huB hb).2.1)⟩
      refine ⟨u, hucount, fun b hb => ⟨(huB hb).2.1, (huB hb).2.2.1⟩, ?_, ?_⟩
      · intro x hx
        obtain ⟨r₀, hr₀, hr₀U⟩ :=
          Metric.nhds_basis_closedBall.mem_iff.1 (hUo.mem_nhds (hUA hx.1))
        obtain ⟨ρ, hρ, hρν⟩ := hx.2 (min r₀ ((m : ℝ) + 1)⁻¹) (lt_min hr₀ (by positivity))
        have hb : (x, ρ) ∈ B := ⟨hx, hρ.1, hρ.2.trans_le (min_le_right _ _),
          (Metric.closedBall_subset_closedBall (hρ.2.le.trans (min_le_left _ _))).trans hr₀U,
          hρν⟩
        obtain ⟨b, hbu, hsub⟩ := hucov (x, ρ) hb
        exact mem_iUnion.2 ⟨⟨b, hbu⟩, hsub (Metric.mem_closedBall_self hρ.1.le)⟩
      · calc ∑' b : u, ENNReal.ofReal (((k : ℝ) + 1)⁻¹ * b.1.2 ^ n)
            ≤ ∑' b : u, ν (Metric.closedBall b.1.1 b.1.2) :=
              ENNReal.tsum_le_tsum fun b => (huB b.2).2.2.2.2
          _ = ν (⋃ b ∈ u, Metric.closedBall b.1 b.2) :=
              (measure_biUnion hucount hudisj fun b _ =>
                Metric.isClosed_closedBall.measurableSet).symm
          _ ≤ ν U := measure_mono (iUnion₂_subset fun b hb => (huB hb).2.2.2.1)
          _ ≤ ENNReal.ofReal (((k : ℝ) + 1)⁻¹ * ε / 10 ^ n) := hUν.le
    choose u hucount hur hucov husum using hcov
    have : ∀ m, Countable (u m) := fun m => (hucount m).to_subtype
    have hr0 : Tendsto (fun m : ℕ => ENNReal.ofReal (10 * ((m : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (10 : ℝ)
      simp only [one_div, mul_zero] at h
      have h' := ENNReal.tendsto_ofReal h
      rwa [ENNReal.ofReal_zero] at h'
    -- `diam(B̄_{5r}(c))ⁿ ≤ (10r)ⁿ = 10ⁿ (k+1) · rⁿ/(k+1)`.
    have hterm : ∀ (r : ℝ) (c : Rn N), 0 < r →
        Metric.ediam (Metric.closedBall c (5 * r)) ^ (n : ℝ) ≤
          ENNReal.ofReal (10 ^ n / ((k : ℝ) + 1)⁻¹) *
            ENNReal.ofReal (((k : ℝ) + 1)⁻¹ * r ^ n) := by
      intro r c hr
      have hd : Metric.ediam (Metric.closedBall c (5 * r)) ≤ ENNReal.ofReal (10 * r) :=
        Metric.ediam_le_of_forall_dist_le fun y hy z hz =>
          (dist_triangle_right y z c).trans (by
            have := Metric.mem_closedBall.1 hy
            have := Metric.mem_closedBall.1 hz
            linarith)
      calc Metric.ediam (Metric.closedBall c (5 * r)) ^ (n : ℝ)
          ≤ ENNReal.ofReal (10 * r) ^ (n : ℝ) := ENNReal.rpow_le_rpow hd (Nat.cast_nonneg n)
        _ = ENNReal.ofReal ((10 * r) ^ n) := by
            rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow (by positivity)]
        _ = ENNReal.ofReal (10 ^ n / ((k : ℝ) + 1)⁻¹ * (((k : ℝ) + 1)⁻¹ * r ^ n)) := by
            congr 1
            field_simp
            ring
        _ = ENNReal.ofReal (10 ^ n / ((k : ℝ) + 1)⁻¹) *
            ENNReal.ofReal (((k : ℝ) + 1)⁻¹ * r ^ n) := ENNReal.ofReal_mul (by positivity)
    -- Hence `Hⁿ(S k) ≤ ε` by the definition of `Hⁿ` through covers of vanishing diameter.
    calc (μH[(n : ℝ)] : Measure (Rn N)) (S k)
        ≤ liminf (fun m => ∑' b : u m,
            Metric.ediam (Metric.closedBall b.1.1 (5 * b.1.2)) ^ (n : ℝ)) atTop :=
          Measure.hausdorffMeasure_le_liminf_tsum (β := ℕ) (ι := fun m => ↥(u m)) (n : ℝ) (S k)
            (l := atTop) (fun m : ℕ => ENNReal.ofReal (10 * ((m : ℝ) + 1)⁻¹)) hr0
            (fun m b => Metric.closedBall b.1.1 (5 * b.1.2))
            (Eventually.of_forall fun m b => by
              obtain ⟨hb0, hb1⟩ := hur m b.1 b.2
              refine Metric.ediam_le_of_forall_dist_le fun y hy z hz =>
                (dist_triangle_right y z b.1.1).trans ?_
              have := Metric.mem_closedBall.1 hy
              have := Metric.mem_closedBall.1 hz
              linarith)
            (Eventually.of_forall hucov)
      _ ≤ ε := by
        refine liminf_le_of_frequently_le' (Frequently.of_forall fun m => ?_)
        calc ∑' b : u m, Metric.ediam (Metric.closedBall b.1.1 (5 * b.1.2)) ^ (n : ℝ)
            ≤ ∑' b : u m, ENNReal.ofReal (10 ^ n / ((k : ℝ) + 1)⁻¹) *
                ENNReal.ofReal (((k : ℝ) + 1)⁻¹ * b.1.2 ^ n) :=
              ENNReal.tsum_le_tsum fun b => hterm _ _ (hur m b.1 b.2).1
          _ = ENNReal.ofReal (10 ^ n / ((k : ℝ) + 1)⁻¹) *
                ∑' b : u m, ENNReal.ofReal (((k : ℝ) + 1)⁻¹ * b.1.2 ^ n) :=
              ENNReal.tsum_mul_left
          _ ≤ ENNReal.ofReal (10 ^ n / ((k : ℝ) + 1)⁻¹) *
                ENNReal.ofReal (((k : ℝ) + 1)⁻¹ * ε / 10 ^ n) := by gcongr; exact husum m
          _ = ε := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal]
            congr 1
            field_simp
  -- `μHE[n]` is a finite multiple of `μH[n]`.
  have hSμ : ∀ k, (μHE[n] : Measure (Rn N)) (S k) = 0 := by
    intro k
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hSH k, smul_zero]
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null hSμ)
  simp only [mem_ofPred_eq, not_imp] at hx
  obtain ⟨hxA, hxT⟩ := hx
  by_contra hxS
  simp only [mem_iUnion, not_exists] at hxS
  apply hxT
  -- At `x ∉ A` outside every `S k`: `ν(B̄_ρ(x)) < ρⁿ/(k+1)` for all small `ρ > 0`.
  have hgood : ∀ k : ℕ, ∃ δ > 0, ∀ ρ ∈ Ioo (0 : ℝ) δ,
      ν (Metric.closedBall x ρ) < ENNReal.ofReal (((k : ℝ) + 1)⁻¹ * ρ ^ n) := by
    intro k
    have h := hxS k
    simp only [hS, mem_ofPred_eq, not_and, not_forall, not_exists, not_le] at h
    obtain ⟨δ, hδ, h'⟩ := h (fun h₀ => hxA (hA₀A h₀))
    exact ⟨δ, hδ, h'⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨δ, hδ, h⟩ := hgood k
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
  have hρn : 0 < ρ ^ n := pow_pos hρ.1 n
  have hI0 : 0 ≤ ∫ z in A ∩ Metric.ball x ρ, |w z| ∂(μHE[n] : Measure (Rn N)) :=
    integral_nonneg fun z => abs_nonneg _
  -- `∫_{A ∩ B_ρ(x)} |w| dHⁿ ≤ ∫⁻_{A₀ ∩ B_ρ(x)} |w| dHⁿ ≤ ν(B̄_ρ(x)) < ρⁿ/(k+1)`.
  have hI : ∫ z in A ∩ Metric.ball x ρ, |w z| ∂(μHE[n] : Measure (Rn N)) <
      ((k : ℝ) + 1)⁻¹ * ρ ^ n := by
    have h1 : ENNReal.ofReal (∫ z in A ∩ Metric.ball x ρ, |w z| ∂(μHE[n] : Measure (Rn N))) ≤
        ν (Metric.closedBall x ρ) := by
      calc ENNReal.ofReal (∫ z in A ∩ Metric.ball x ρ, |w z| ∂(μHE[n] : Measure (Rn N)))
          = ‖∫ z in A ∩ Metric.ball x ρ, |w z| ∂(μHE[n] : Measure (Rn N))‖ₑ :=
            (Real.enorm_of_nonneg hI0).symm
        _ ≤ ∫⁻ z in A ∩ Metric.ball x ρ, ‖|w z|‖ₑ ∂(μHE[n] : Measure (Rn N)) :=
            enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ z in A₀ ∩ Metric.ball x ρ, ‖w z‖ₑ ∂(μHE[n] : Measure (Rn N)) := by
            simp only [Real.enorm_abs]
            exact setLIntegral_congr (hA₀ae.symm.inter (EventuallyEq.refl _ _))
        _ ≤ ∫⁻ z in Metric.closedBall x ρ ∩ A₀, ‖w z‖ₑ ∂(μHE[n] : Measure (Rn N)) :=
            lintegral_mono_set fun z hz => ⟨Metric.ball_subset_closedBall hz.2, hz.1⟩
        _ = ν (Metric.closedBall x ρ) :=
            (hνapp _ Metric.isClosed_closedBall.measurableSet).symm
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 (h1.trans_lt (h ρ hρ))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (inv_nonneg.2 hρn.le) hI0)]
  calc (ρ ^ n)⁻¹ * ∫ z in A ∩ Metric.ball x ρ, |w z| ∂(μHE[n] : Measure (Rn N))
      ≤ (ρ ^ n)⁻¹ * (((k : ℝ) + 1)⁻¹ * ρ ^ n) :=
        mul_le_mul_of_nonneg_left hI.le (inv_nonneg.2 hρn.le)
    _ = ((k : ℝ) + 1)⁻¹ := by field_simp
    _ < ε := by simpa [one_div] using hk

/-- **Lebesgue points of `Hⁿ ⌞ S` with the `ρⁿ` normalization** (Simon Ch. 1, Corollary 3.17;
parent proof step (P3)). Let `Hⁿ(S) < ∞`, `w ∈ L¹(Hⁿ ⌞ S)` and `Hⁿ(S ∩ B̄_ρ(x)) ≤ Cρⁿ` for
`x ∈ S`, `ρ > 0`. Then for `Hⁿ`-a.e. `x ∈ S`, `ρ⁻ⁿ ∫_{S ∩ B_ρ(x)} |w - w(x)| dHⁿ → 0` as `ρ ↓ 0`.
The Lebesgue–Besicovitch differentiation theorem for the finite measure `λ₀ = Hⁿ ⌞ S` along
closed balls gives `a(ρ) = ⨍_{B̄_ρ(x)} |w - w(x)| dλ₀ → 0` for `λ₀`-a.e. (i.e. `Hⁿ`-a.e. on `S`)
`x`, and `ρ⁻ⁿ ∫_{S ∩ B_ρ(x)} |w - w(x)| dHⁿ ≤ ρ⁻ⁿ λ₀(B̄_ρ(x)) a(ρ) ≤ max(C, 0) a(ρ)`. -/
theorem Submission.chartTD_lebesgue_point_ae : ∀ (n N : ℕ) (S : Set (Rn N)) (w : Rn N → ℝ) (C : ℝ), NullMeasurableSet S μHE[n] → μHE[n] S < ∞ → IntegrableOn w S μHE[n] → (∀ x ∈ S, ∀ ρ : ℝ, 0 < ρ → μHE[n] (S ∩ Metric.closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → ∀ᵐ x ∂(μHE[n] : Measure (Rn N)), x ∈ S → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ z in S ∩ Metric.ball x ρ, |w z - w x| ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
  intro n N S w C hS hSfin hw hC
  -- `λ₀ = Hⁿ ⌞ S` is a finite measure and `w ∈ L¹(λ₀)`.
  have : IsFiniteMeasure ((μHE[n] : Measure (Rn N)).restrict S) :=
    ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hw' : Integrable w ((μHE[n] : Measure (Rn N)).restrict S) := hw
  -- Lebesgue–Besicovitch differentiation for `λ₀`; `λ₀`-a.e. is `Hⁿ`-a.e. on `S`.
  have hdiff := VitaliFamily.ae_tendsto_average_norm_sub
    (Besicovitch.vitaliFamily ((μHE[n] : Measure (Rn N)).restrict S)) hw'.locallyIntegrable
  filter_upwards [(ae_restrict_iff'₀ hS).1 hdiff] with x hx hxS
  -- `max(C, 0) a(ρ) → 0` as `ρ ↓ 0`, where `a(ρ) = ⨍_{B̄_ρ(x)} |w - w(x)| dλ₀`.
  have ha : Tendsto (fun ρ : ℝ ↦ max C 0 * ⨍ y in Metric.closedBall x ρ, ‖w y - w x‖
      ∂((μHE[n] : Measure (Rn N)).restrict S)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      ((hx hxS).comp (Besicovitch.tendsto_filterAt _ x)).const_mul (max C 0)
  have hint : Integrable (fun z ↦ |w z - w x|) ((μHE[n] : Measure (Rn N)).restrict S) :=
    (hw'.sub (integrable_const (w x))).abs
  refine squeeze_zero' ?_ ?_ ha
  · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
    exact mul_nonneg (inv_nonneg.2 (pow_nonneg hρ.le n)) (integral_nonneg fun _ ↦ abs_nonneg _)
  · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
    have hρn : 0 < ρ ^ n := pow_pos hρ n
    -- `λ₀(B̄_ρ(x)) = Hⁿ(S ∩ B̄_ρ(x)) ≤ max(C, 0) ρⁿ`.
    have hmeas : ((μHE[n] : Measure (Rn N)).restrict S).real (Metric.closedBall x ρ) ≤
        max C 0 * ρ ^ n := by
      rw [measureReal_def, Measure.restrict_apply measurableSet_closedBall, inter_comm]
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ((hC x hxS ρ hρ).trans ?_)
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hρn.le)
    have havg : 0 ≤ ⨍ y in Metric.closedBall x ρ, ‖w y - w x‖
        ∂((μHE[n] : Measure (Rn N)).restrict S) :=
      average_nonneg fun _ ↦ norm_nonneg _
    rw [inv_mul_le_iff₀ hρn]
    calc ∫ z in S ∩ Metric.ball x ρ, |w z - w x| ∂μHE[n]
        = ∫ z in Metric.ball x ρ, |w z - w x| ∂((μHE[n] : Measure (Rn N)).restrict S) := by
          rw [Measure.restrict_restrict measurableSet_ball, inter_comm S]
      _ ≤ ∫ z in Metric.closedBall x ρ, |w z - w x| ∂((μHE[n] : Measure (Rn N)).restrict S) :=
          setIntegral_mono_set hint.integrableOn (Eventually.of_forall fun _ ↦ abs_nonneg _)
            Metric.ball_subset_closedBall.eventuallyLE
      _ = ((μHE[n] : Measure (Rn N)).restrict S).real (Metric.closedBall x ρ) *
            ⨍ y in Metric.closedBall x ρ, ‖w y - w x‖ ∂((μHE[n] : Measure (Rn N)).restrict S) := by
          rw [← smul_eq_mul, measure_smul_setAverage _ (measure_ne_top _ _)]
          simp only [Real.norm_eq_abs]
      _ ≤ ρ ^ n * (max C 0 * ⨍ y in Metric.closedBall x ρ, ‖w y - w x‖
            ∂((μHE[n] : Measure (Rn N)).restrict S)) := by
          rw [← mul_assoc, mul_comm (ρ ^ n)]
          exact mul_le_mul_of_nonneg_right hmeas havg

/-- **Weighted approximate tangent space from density estimates against a comparison set**
(Simon Ch. 3, proof of Theorem 1.6 "⇒", `chapter-03.txt` lines 113–143, in the weighted form of
Def. 1.7 and Remark 1.8(1), lines 284–306). Let `M`, `Γ` be `Hⁿ`-measurable with `Hⁿ(Γ) < ∞`,
`θ` a positive locally integrable weight on `M`, and let `Γ` have approximate tangent space `P`
at `x`. If, as `ρ ↓ 0`, `ρ⁻ⁿ ∫_{(M ∖ Γ) ∩ B_ρ(x)} |θ| dHⁿ → 0`, `ρ⁻ⁿ Hⁿ((Γ ∖ M) ∩ B_ρ(x)) → 0`
and `ρ⁻ⁿ ∫_{M ∩ Γ ∩ B_ρ(x)} |θ - θ(x)| dHⁿ → 0`, then `P` is the approximate tangent space of
`M` at `x` with respect to `θ`. For `f ∈ C_c(ℝᴺ, ℝ)` and `r > 0`, the change of variables
`chartTD_setIntegral_blowUpMap_image` (with `x + r η_{x,r}(z) = z`) and the splitting
`chartTD_weighted_blowup_integral_split` give
`∫_{η_{x,r}(M)} f(y) θ(x + r y) dHⁿ(y) = E₁(r) + θ(x) (∫_{η_{x,r}(Γ)} f dHⁿ - E₂(r)) + E₃(r)`,
where `E₁`, `E₂`, `E₃` are the `r⁻ⁿ`-normalized integrals of `f ∘ η_{x,r}` against `θ` over
`M ∖ Γ`, `1` over `Γ ∖ M` and `θ - θ(x)` over `M ∩ Γ`. Each `Eᵢ(r) → 0` by
`chartTD_blowup_integral_tendsto_zero`, and `∫_{η_{x,r}(Γ)} f dHⁿ → ∫_P f dHⁿ`. -/
theorem Submission.chartTD_weighted_tangent_of_density : ∀ (n N : ℕ) (M Γ : Set (Rn N)) (θ : Rn N → ℝ) (x : Rn N) (P : Submodule ℝ (Rn N)), NullMeasurableSet M μHE[n] → NullMeasurableSet Γ μHE[n] → μHE[n] Γ < ∞ → IsPositiveLocallyIntegrableWeight n M θ → HasApproximateTangentSpaceAt n Γ x P → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ z in (M \ Γ) ∩ Metric.ball x ρ, |θ z| ∂μHE[n]) (𝓝[>] 0) (𝓝 0) → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * (μHE[n] ((Γ \ M) ∩ Metric.ball x ρ)).toReal) (𝓝[>] 0) (𝓝 0) → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ z in M ∩ Γ ∩ Metric.ball x ρ, |θ z - θ x| ∂μHE[n]) (𝓝[>] 0) (𝓝 0) → HasWeightedApproximateTangentSpaceAt n M θ x P := by
  intro n N M Γ θ x P hM hΓ hΓfin hθ hT h₁ h₂ h₃
  refine ⟨hT.1, fun f ↦ ?_⟩
  -- `θ` is integrable on `M ∩ B_ρ(x) ⊆ M ∩ B̄_ρ(x)`, and subsets of `Γ` have finite measure.
  have hθball : ∀ ρ : ℝ, IntegrableOn θ (M ∩ Metric.ball x ρ) μHE[n] := fun ρ ↦
    (hθ.2.2 _ (isCompact_closedBall x ρ)).mono_set
      (inter_subset_inter_right _ Metric.ball_subset_closedBall)
  have hΓsub : ∀ s ⊆ Γ, μHE[n] s ≠ ∞ := fun s hs ↦ ((measure_mono hs).trans_lt hΓfin).ne
  -- `E₁(r) = r⁻ⁿ ∫_{M ∖ Γ} f(η_{x,r}(z)) θ(z) dHⁿ(z) → 0`
  have hE₁ : Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ z in M \ Γ, f (blowUpMap x r z) * θ z ∂μHE[n])
      (𝓝[>] 0) (𝓝 0) :=
    Submission.chartTD_blowup_integral_tendsto_zero n N (M \ Γ) θ x
      (fun ρ _ ↦ (hθball ρ).mono_set (inter_subset_inter_left _ sdiff_subset)) h₁ f
  -- `E₂(r) = r⁻ⁿ ∫_{Γ ∖ M} f(η_{x,r}(z)) dHⁿ(z) → 0`, with the weight `w ≡ 1`
  have hE₂ : Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ z in Γ \ M, f (blowUpMap x r z) ∂μHE[n])
      (𝓝[>] 0) (𝓝 0) := by
    have h := Submission.chartTD_blowup_integral_tendsto_zero n N (Γ \ M) (fun _ ↦ (1 : ℝ)) x
      (fun ρ _ ↦ integrableOn_const (hΓsub _ (inter_subset_left.trans sdiff_subset)))
      (h₂.congr fun ρ ↦ by
        simp only [abs_one, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]) f
    simpa only [mul_one] using h
  -- `E₃(r) = r⁻ⁿ ∫_{M ∩ Γ} f(η_{x,r}(z)) (θ(z) - θ(x)) dHⁿ(z) → 0`
  have hE₃ : Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ *
      ∫ z in M ∩ Γ, f (blowUpMap x r z) * (θ z - θ x) ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
    refine Submission.chartTD_blowup_integral_tendsto_zero n N (M ∩ Γ) (fun z ↦ θ z - θ x) x
      (fun ρ _ ↦ ?_) h₃ f
    have hc : IntegrableOn (fun _ ↦ θ x) (M ∩ Γ ∩ Metric.ball x ρ) μHE[n] :=
      integrableOn_const (hΓsub _ (inter_subset_left.trans inter_subset_right))
    exact ((hθball ρ).mono_set (inter_subset_inter_left _ inter_subset_left)).sub hc
  -- Combine with `∫_{η_{x,r}(Γ)} f dHⁿ → ∫_P f dHⁿ`.
  have hlim := (hE₁.add (((hT.2 f).sub hE₂).const_mul (θ x))).add hE₃
  rw [zero_add, sub_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  -- For `r > 0`: change variables (`x + r η_{x,r}(z) = z`), then split along `Γ`.
  have hη : ∀ z, x + r • blowUpMap x r z = z := fun z ↦ by
    rw [blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
  rw [Submission.chartTD_setIntegral_blowUpMap_image N n x r hr M,
    Submission.chartTD_setIntegral_blowUpMap_image N n x r hr Γ]
  simp only [hη]
  rw [Submission.chartTD_weighted_blowup_integral_split n N M Γ θ x f r hr hM hΓ hΓfin hθ]
  ring

/-- **Rademacher's theorem on an open set** (Simon Ch. 2, Theorem 1.4, applied locally as in
(4.8)): if `g : ℝⁿ → ℝᵖ` is locally Lipschitz on the open set `W ⊆ ℝⁿ`, then `g` is
differentiable at `Lⁿ`-a.e. point of `W`. Each point `x` of the exceptional set
`Z = {u ∈ W : g is not differentiable at u}` has a ball `B_r(x)` on which `g` is Lipschitz;
Rademacher for maps Lipschitz on a set (`LipschitzOnWith.ae_differentiableWithinAt_of_mem`) and
openness of the ball give `Lⁿ(Z ∩ B_r(x)) = 0`, and second countability
(`measure_null_of_locally_null`) gives `Lⁿ(Z) = 0`. -/
theorem Submission.chartTD_ae_differentiableAt_of_locallyLipschitzOn : ∀ (n p : ℕ)
    (W : Set (Rn n)) (g : Rn n → Rn p), IsOpen W → LocallyLipschitzOn W g →
    ∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ W → DifferentiableAt ℝ g u := by
  intro n p W g hW hg
  -- Step 1: the claim says that `Z = {u | ¬(u ∈ W → DifferentiableAt ℝ g u)}` is `Lⁿ`-null.
  rw [ae_iff]
  -- Step 6: by second countability, it suffices that each `x ∈ Z` has a null neighbourhood
  -- within `Z`.
  refine measure_null_of_locally_null _ fun x hx ↦ ?_
  simp only [mem_ofPred_eq, not_imp] at hx
  -- Step 2: `g` is `K`-Lipschitz on a ball `B_r(x)`, since `𝓝[W] x = 𝓝 x` for the open `W`.
  obtain ⟨K, T, hT, hgT⟩ := hg hx.1
  rw [hW.nhdsWithin_eq hx.1] at hT
  obtain ⟨r, hr, hrT⟩ := Metric.mem_nhds_iff.1 hT
  -- Step 5: `Z ∩ B_r(x)` is a neighbourhood of `x` within `Z`.
  refine ⟨_, inter_mem_nhdsWithin _ (Metric.ball_mem_nhds x hr), ?_⟩
  -- Step 3: Rademacher on `B_r(x)`: `g` is differentiable within the ball at a.e. point of it.
  have hR := ae_iff.1 ((hgT.mono hrT).ae_differentiableWithinAt_of_mem
    (μ := (volume : Measure (Rn n))))
  -- Step 4: `Z ∩ B_r(x)` lies in the Rademacher exceptional set, because the ball is open.
  refine measure_mono_null (fun v hv ↦ ?_) hR
  simp only [mem_inter_iff, mem_ofPred_eq, not_imp] at hv ⊢
  exact ⟨hv.2, fun hd ↦ hv.1.2 (hd.differentiableAt (Metric.isOpen_ball.mem_nhds hv.2))⟩

/-- **Line derivative of a locally Lipschitz map along a chart** (Simon Ch. 2, (4.7) and (4.10)):
let `f : ℝᴺ → ℝᵖ` be locally Lipschitz on the open set `U ⊆ ℝᴺ`, and let `ψ : ℝⁿ → ℝᴺ` and
`f ∘ ψ` be differentiable at `u`, with `ψ(u) ∈ U`. Then for every `w ∈ ℝⁿ`, `f` has line
derivative `D(f ∘ ψ)(u) w` at `ψ(u)` in the direction `Dψ(u) w`. The chart curve
`t ↦ ψ(u + t w)` and the line `t ↦ ψ(u) + t Dψ(u) w` agree to first order at `t = 0`, so the
Lipschitz bound of `f` near `ψ(u)` makes the values of `f` along them differ by `o(t)`. -/
theorem Submission.chartTD_hasLineDerivAt_of_comp_differentiableAt : ∀ (n N p : ℕ)
    (U : Set (Rn N)) (f : Rn N → Rn p) (ψ : Rn n → Rn N) (u : Rn n), IsOpen U →
    LocallyLipschitzOn U f → ψ u ∈ U → DifferentiableAt ℝ ψ u → DifferentiableAt ℝ (f ∘ ψ) u →
    ∀ w : Rn n, HasLineDerivAt ℝ f (fderiv ℝ (f ∘ ψ) u w) (ψ u) (fderiv ℝ ψ u w) := by
  intro n N p U f ψ u hU hf hu hψ hfψ w
  -- Step 2: `f` is `L`-Lipschitz on a neighbourhood `T` of `ψ u`, since `𝓝[U] (ψ u) = 𝓝 (ψ u)`.
  obtain ⟨L, T, hT, hfT⟩ := hf hu
  rw [hU.nhdsWithin_eq hu] at hT
  -- Step 3: the line derivatives of `ψ` and of `f ∘ ψ` at `u` in the direction `w`.
  have ha := hψ.hasFDerivAt.hasLineDerivAt w
  have hb := hfψ.hasFDerivAt.hasLineDerivAt w
  -- Step 1: write the two hypotheses and the goal as `o(t)` statements as `t → 0`.
  rw [hasLineDerivAt_iff_isLittleO_nhds_zero] at ha hb ⊢
  -- Step 4: for `t` near `0`, both `ψ (u + t • w)` and `ψ u + t • Dψ(u) w` lie in `T`.
  have hγ : ∀ᶠ t in 𝓝 (0 : ℝ), ψ (u + t • w) ∈ T :=
    hψ.continuousAt.tendsto.comp
      ((by fun_prop : Continuous fun t : ℝ ↦ u + t • w).tendsto' 0 u (by simp)) hT
  have hα : ∀ᶠ t in 𝓝 (0 : ℝ), ψ u + t • fderiv ℝ ψ u w ∈ T :=
    (by fun_prop : Continuous fun t : ℝ ↦ ψ u + t • fderiv ℝ ψ u w).tendsto' 0 (ψ u) (by simp) hT
  -- Step 5 (Simon (4.7)): the Lipschitz bound compares `f` along the line and along the chart
  -- curve, and the difference of the two curves is `o(t)`.
  have hO : (fun t : ℝ ↦ f (ψ u + t • fderiv ℝ ψ u w) - f (ψ (u + t • w))) =O[𝓝 0]
      fun t : ℝ ↦ ψ (u + t • w) - ψ u - t • fderiv ℝ ψ u w := by
    refine Asymptotics.IsBigO.of_bound L ?_
    filter_upwards [hγ, hα] with t hγt hαt
    rw [← sub_add_eq_sub_sub, norm_sub_rev (ψ (u + t • w))]
    exact hfT.norm_sub_le hαt hγt
  -- Step 6: the two `o(t)` terms add up to the claim.
  refine ((hO.trans_isLittleO ha).add hb).congr_left fun t ↦ ?_
  simp only [Function.comp_apply]
  abel

/-- **Simon Ch. 2, Theorem 1.4 and (4.8)–(4.10)** (`chapter-02.txt` lines 59–72, 925–957), in one
`C¹` chart `ψ` on an open `V ⊆ ℝⁿ` (injectivity of `Dψ` is not needed). Let `f` be locally
Lipschitz on an open `U ⊆ ℝᴺ`. For `Lⁿ`-a.e. `u ∈ V` with `ψ(u) ∈ U`, `f ∘ ψ` is differentiable
at `u` (Rademacher) and `D(f ∘ ψ)(u) w = d/dt f(ψ(u) + t Dψ(u) w)|_{t=0}` for every `w` ((4.10)).
On the open set `W = V ∩ ψ⁻¹(U)` the map `f ∘ ψ` is locally Lipschitz, so Rademacher's theorem
applies on `W`. At each point of differentiability, the curve `t ↦ ψ(u + t w)` is compared with
the line `t ↦ ψ(u) + t Dψ(u) w` as in (4.7). -/
theorem Submission.chartTD_comp_differentiable_lineDeriv_ae : ∀ (n N p : ℕ) (U : Set (Rn N))
    (f : Rn N → Rn p) (V : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen U → LocallyLipschitzOn U f →
    IsOpen V → ContDiffOn ℝ 1 ψ V →
    ∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ V → ψ u ∈ U →
      DifferentiableAt ℝ (f ∘ ψ) u ∧
        ∀ w : Rn n, HasLineDerivAt ℝ f (fderiv ℝ (f ∘ ψ) u w) (ψ u) (fderiv ℝ ψ u w) := by
  intro n N p U f V ψ hU hf hV hψ
  -- Step 1: `W = V ∩ ψ⁻¹(U)` is open, since `ψ` is continuous on the open set `V`.
  have hW : IsOpen (V ∩ ψ ⁻¹' U) := hψ.continuousOn.isOpen_inter_preimage hV hU
  -- Step 2: `f ∘ ψ` is locally Lipschitz on `W`: `ψ` is Lipschitz near `u` (it is `C¹` there),
  -- `f` is Lipschitz near `ψ(u)` (`U` is open), and `ψ` maps a neighbourhood of `u` into the
  -- latter.
  have hfψ : LocallyLipschitzOn (V ∩ ψ ⁻¹' U) (f ∘ ψ) := by
    rintro u ⟨huV, huU⟩
    have hψu : ContDiffAt ℝ 1 ψ u := hψ.contDiffAt (hV.mem_nhds huV)
    obtain ⟨Kψ, s, hs, hψs⟩ := hψu.exists_lipschitzOnWith
    obtain ⟨Kf, t, ht, hft⟩ := hf huU
    rw [hU.nhdsWithin_eq huU] at ht
    exact ⟨Kf * Kψ, s ∩ ψ ⁻¹' t,
      mem_nhdsWithin_of_mem_nhds (inter_mem hs (hψu.continuousAt.preimage_mem_nhds ht)),
      hft.comp (hψs.mono inter_subset_left) fun _ hx ↦ hx.2⟩
  -- Steps 3–4: Rademacher's theorem on `W` (via the countable cover in the accepted child).
  filter_upwards [Submission.chartTD_ae_differentiableAt_of_locallyLipschitzOn n p _ _ hW hfψ]
    with u hu huV huU
  have hdiff : DifferentiableAt ℝ (f ∘ ψ) u := hu ⟨huV, huU⟩
  -- Step 5 (Simon (4.10)): the line derivative at every point of differentiability.
  exact ⟨hdiff, Submission.chartTD_hasLineDerivAt_of_comp_differentiableAt n N p U f ψ u hU hf
    huU ((hψ.contDiffAt (hV.mem_nhds huV)).differentiableAt one_ne_zero) hdiff⟩

/-- **Simon Ch. 3, Remark 1.5(2) and proof of Theorem 1.6 "⇒", in the weighted form of
Remark 1.8(1); Ch. 2, (4.8)–(4.10)** (`chapter-03.txt` lines 87–90, 113–143, 284–306;
`chapter-02.txt` lines 925–957), for one `C¹` chart `ψ` on an open `V ⊆ ℝⁿ` with injective `Dψ`.
For `Lⁿ`-a.e. `u ∈ V` with `ψ(u) ∈ M`: (A) `range Dψ(u)` is the approximate tangent space of `M`
at `ψ(u)` with respect to `θ` (Def. 1.7); (B) `f ∘ ψ` is differentiable at `u` (Rademacher);
(C) `D(f ∘ ψ)(u) w = d/dt f(ψ(u) + t Dψ(u) w)|_{t=0}` (Ch. 2 (4.10)).
For (A), `V` is covered by countably many balls `B` on which `ψ` is bi-Lipschitz. With
`Γ = ψ(B)`: by the upper density theorem and Lebesgue's differentiation theorem, `Hⁿ`-a.e.
`x ∈ M ∩ Γ` satisfies the density conditions (P1)–(P3) of the proof of 1.6; the blow-ups of `Γ` at
`ψ(u)` converge to `range Dψ(u)` (Remark 1.5(2)); so (A) holds off the preimage of an `Hⁿ`-null
set, which is `Lⁿ`-null in `B` because `ψ⁻¹` is Lipschitz on `Γ`. -/
theorem Submission.chart_approx_tangent_and_differential : ∀ (n ℓ p : ℕ) (M U : Set (Rn (n + ℓ)))
    (θ : Rn (n + ℓ) → ℝ) (f : Rn (n + ℓ) → Rn p) (V : Set (Rn n)) (ψ : Rn n → Rn (n + ℓ)),
    NullMeasurableSet M μHE[n] → IsPositiveLocallyIntegrableWeight n M θ → IsOpen U → M ⊆ U →
    LocallyLipschitzOn U f → IsOpen V → ContDiffOn ℝ 1 ψ V →
    (∀ u ∈ V, Function.Injective (fderiv ℝ ψ u)) →
    ∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ V → ψ u ∈ M →
      HasWeightedApproximateTangentSpaceAt n M θ (ψ u)
          (LinearMap.range (fderiv ℝ ψ u).toLinearMap) ∧
        DifferentiableAt ℝ (f ∘ ψ) u ∧
        ∀ w : Rn n, HasLineDerivAt ℝ f (fderiv ℝ (f ∘ ψ) u w) (ψ u) (fderiv ℝ ψ u w) := by
  intro n ℓ p M U θ f V ψ hM hθ hU hMU hf hV hψ hinj
  -- (B), (C): Rademacher's theorem in the chart and Ch. 2 (4.10), at points with `ψ u ∈ U`.
  have hBC := Submission.chartTD_comp_differentiable_lineDeriv_ae n (n + ℓ) p U f V ψ hU hf hV hψ
  -- (A) on a ball `B ⊆ V` around each `u₀ ∈ V` on which `ψ` is bi-Lipschitz.
  have hloc : ∀ u₀ ∈ V, ∃ r : ℝ, 0 < r ∧ Metric.ball u₀ r ⊆ V ∧
      ∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ Metric.ball u₀ r → ψ u ∈ M →
        HasWeightedApproximateTangentSpaceAt n M θ (ψ u)
          (LinearMap.range (fderiv ℝ ψ u).toLinearMap) := by
    intro u₀ hu₀
    obtain ⟨r, hr, hrV, K, c, hc, hLip, hlow⟩ :=
      Submission.chartTD_immersion_local_biLipschitz n (n + ℓ) V ψ hV hψ hinj u₀ hu₀
    refine ⟨r, hr, hrV, ?_⟩
    set B := Metric.ball u₀ r
    -- `Γ = ψ(B)` is `Hⁿ`-measurable and bounded, `Hⁿ(Γ) < ∞`, `Hⁿ(Γ ∩ B̄_ρ(x)) ≤ C ρⁿ`, and
    -- preimages in `B` of `Hⁿ`-null sets are `Lⁿ`-null.
    obtain ⟨hΓm, hΓb, hΓfin, ⟨C, hC⟩, hnull⟩ :=
      Submission.chartTD_biLipschitz_image_measure_facts n (n + ℓ) B ψ K c Metric.isOpen_ball
        Metric.isBounded_ball hLip hc hlow
    set Γ := ψ '' B
    -- (P1): `θ Hⁿ ⌞ (M \ Γ)` has `n`-density `0` at `Hⁿ`-a.e. point of `M ∩ Γ`.
    have hP1 := Submission.chartTD_upper_density_zero_ae n (n + ℓ) (M \ Γ) θ (hM.diff hΓm)
      fun K hK ↦ (hθ.2.2 K hK).mono_set (inter_subset_inter_left K sdiff_subset)
    -- (P2): `Hⁿ ⌞ (Γ \ M)` has `n`-density `0` at `Hⁿ`-a.e. point of `M ∩ Γ`.
    have hP2 := Submission.chartTD_upper_density_zero_ae n (n + ℓ) (Γ \ M) (fun _ ↦ (1 : ℝ))
      (hΓm.diff hM) fun K _ ↦ integrableOn_const
        ((measure_mono (inter_subset_left.trans sdiff_subset)).trans_lt hΓfin).ne
    -- (P3): `Hⁿ`-a.e. point of `M ∩ Γ` is a Lebesgue point of `θ`, with the `ρⁿ` normalization.
    have hP3 := Submission.chartTD_lebesgue_point_ae n (n + ℓ) (M ∩ Γ) θ C (hM.inter hΓm)
      ((measure_mono inter_subset_right).trans_lt hΓfin)
      ((hθ.2.2 _ hΓb.isCompact_closure).mono_set (inter_subset_inter_right M subset_closure))
      fun x hx ρ hρ ↦ (measure_mono (inter_subset_inter_left _ inter_subset_right)).trans
        (hC x hx.2 ρ hρ)
    have hgood : ∀ᵐ x ∂(μHE[n] : Measure (Rn (n + ℓ))), x ∈ M → x ∈ Γ →
        Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ z in (M \ Γ) ∩ Metric.ball x ρ, |θ z| ∂μHE[n])
          (𝓝[>] 0) (𝓝 0) ∧
        Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * (μHE[n] ((Γ \ M) ∩ Metric.ball x ρ)).toReal)
          (𝓝[>] 0) (𝓝 0) ∧
        Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ z in M ∩ Γ ∩ Metric.ball x ρ, |θ z - θ x| ∂μHE[n])
          (𝓝[>] 0) (𝓝 0) := by
      filter_upwards [hP1, hP2, hP3] with x h1 h2 h3 hxM hxΓ
      refine ⟨h1 fun h ↦ h.2 hxΓ, ?_, h3 ⟨hxM, hxΓ⟩⟩
      simpa [setIntegral_const, Measure.real] using h2 fun h ↦ h.2 hxM
    -- Off the `Lⁿ`-null preimage of the set where (P1)–(P3) fail, the blow-ups of `Γ` at `ψ u`
    -- converge to `range Dψ(u)` (Remark 1.5(2)), and (P1)–(P3) transfer this to `M` and `θ`.
    refine ae_iff.2 (measure_mono_null (fun u hu ↦ ?_) (hnull _ (ae_iff.1 hgood)))
    simp only [mem_ofPred_eq, not_imp] at hu
    obtain ⟨huB, huM, hnot⟩ := hu
    refine ⟨huB, ?_⟩
    simp only [mem_preimage, mem_ofPred_eq, not_imp]
    refine ⟨huM, mem_image_of_mem ψ huB, ?_⟩
    rintro ⟨h1, h2, h3⟩
    exact hnot (Submission.chartTD_weighted_tangent_of_density n (n + ℓ) M Γ θ (ψ u) _ hM hΓm
      hΓfin hθ (Submission.chartTD_biLipschitz_chart_approx_tangent n (n + ℓ) B ψ K c
        Metric.isOpen_ball (hψ.mono hrV) hLip hc hlow u huB) h1 h2 h3)
  -- Countably many of these balls cover `V` (Lindelöf).
  choose! r hr hrV hae using hloc
  obtain ⟨T, hTV, hTc, hTcover⟩ := TopologicalSpace.isOpen_biUnion_countable V
    (fun u ↦ Metric.ball u (r u)) fun u _ ↦ Metric.isOpen_ball
  have hA : ∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ V → ψ u ∈ M →
      HasWeightedApproximateTangentSpaceAt n M θ (ψ u)
        (LinearMap.range (fderiv ℝ ψ u).toLinearMap) := by
    filter_upwards [(ae_ball_iff hTc).2 fun i hi ↦ hae i (hTV hi)] with u hu huV huM
    have hmem : u ∈ ⋃ i ∈ T, Metric.ball i (r i) :=
      hTcover ▸ mem_biUnion huV (Metric.mem_ball_self (hr u huV))
    obtain ⟨i, hi, hui⟩ := mem_iUnion₂.1 hmem
    exact hu i hi hui huM
  filter_upwards [hA, hBC] with u hAu hBCu huV huM
  exact ⟨hAu huV huM, hBCu huV (hMU huM)⟩

/-- **Gluing local co-area formulas over countably many Borel pieces** (Simon Ch. 3, proof of the
co-area formula (2.8)–(2.9), pp. 76–77, decomposition and summation steps; with the erratum of
(2.9): the domain is `A` on both sides). Let `f` be continuous on the open `U ⊇ M`, `w ≥ 0`
arbitrary and `S_j` Borel with `Hⁿ(M ∖ ⋃ S_j) = 0`. Assume (NS): every `Hⁿ`-null `Z ⊆ M` has
`Hᵏ`-null slices `Z ∩ f⁻¹{y}` for `Lᵐ`-a.e. `y`, and (Loc): for Borel `B ⊆ S_j` and Borel `φ ≥ 0`,
`∫_B φ w dHⁿ = ∫ ∫_{B ∩ f⁻¹{y}} φ dHᵏ dLᵐ(y)` with an a.e.-measurable inner integral. Then
`∫_A g w dHⁿ = ∫ ∫_{A ∩ f⁻¹{y}} g dHᵏ dLᵐ(y)` for every `Hⁿ`-measurable `A ⊆ M` and every
`Hⁿ ⌞ A`-measurable `g ≥ 0`. Replace `g` by a Borel `g'` and `A` by a Borel `A' ⊆ A` (up to
`Hⁿ`-null sets) and disjointify `A' ∩ S_j` into Borel `T_j`; the remainder `A ∖ ⋃ T_j` is
`Hⁿ`-null. The left side is `∑_j ∫_{T_j} g' w dHⁿ` (countable additivity of the set integral,
valid for any integrand), each term is given by (Loc), and monotone convergence sums the inner
integrals. Since `f` is continuous on the open `U`, the slices `T_j ∩ f⁻¹{y}` are disjoint Borel
sets, so the sum is `∫_{⋃ T_j ∩ f⁻¹{y}} g' dHᵏ`; by (NS) applied to `A ∖ ⋃ T_j` and to
`{x ∈ A : g x ≠ g' x}` this is `∫_{A ∩ f⁻¹{y}} g dHᵏ` for `Lᵐ`-a.e. `y`. -/
theorem Submission.coarea_gluing_of_pieces : ∀ (N n m k : ℕ) (U M : Set (Rn N)) (f : Rn N → Rn m)
    (w : Rn N → ℝ≥0∞) (S : ℕ → Set (Rn N)), IsOpen U → M ⊆ U → ContinuousOn f U →
    (∀ Z ⊆ M, μHE[n] Z = 0 → ∀ᵐ y ∂(volume : Measure (Rn m)), μHE[k] (Z ∩ f ⁻¹' {y}) = 0) →
    (∀ j, MeasurableSet (S j)) → μHE[n] (M \ ⋃ j, S j) = 0 →
    (∀ j, ∀ B ⊆ S j, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ →
      AEMeasurable (fun y : Rn m ↦ ∫⁻ x in B ∩ f ⁻¹' {y}, φ x ∂μHE[k]) volume ∧
        ∫⁻ x in B, φ x * w x ∂μHE[n] = ∫⁻ y, (∫⁻ x in B ∩ f ⁻¹' {y}, φ x ∂μHE[k]) ∂volume) →
    ∀ A ⊆ M, NullMeasurableSet A μHE[n] → ∀ g : Rn N → ℝ≥0∞,
      AEMeasurable g ((μHE[n] : Measure (Rn N)).restrict A) →
      ∫⁻ x in A, g x * w x ∂μHE[n] = ∫⁻ y, (∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]) ∂volume := by
  intro N n m k U M f w S hU hMU hf hNS hS hcov hloc A hAM hA g hg
  -- Borel representatives: `g = g'` `Hⁿ ⌞ A`-a.e. and a Borel `A' ⊆ A` with `A' = A` `Hⁿ`-a.e.
  have hg'm : Measurable (hg.mk g) := hg.measurable_mk
  have hgg' : g =ᵐ[(μHE[n] : Measure (Rn N)).restrict A] hg.mk g := hg.ae_eq_mk
  obtain ⟨A', hA'A, hA'm, hA'ae⟩ := hA.exists_measurable_subset_ae_eq
  -- Disjoint Borel pieces `T j ⊆ A' ∩ S j` with union `A' ∩ ⋃ j, S j`.
  have hTm : ∀ j, MeasurableSet (disjointed (fun j ↦ A' ∩ S j) j) :=
    MeasurableSet.disjointed fun j ↦ hA'm.inter (hS j)
  have hTd := disjoint_disjointed fun j ↦ A' ∩ S j
  have hTS : ∀ j, disjointed (fun j ↦ A' ∩ S j) j ⊆ S j :=
    fun j ↦ (disjointed_subset _ j).trans inter_subset_right
  have hTU : ⋃ j, disjointed (fun j ↦ A' ∩ S j) j = A' ∩ ⋃ j, S j := by
    rw [iUnion_disjointed, inter_iUnion]
  have hA''A : ⋃ j, disjointed (fun j ↦ A' ∩ S j) j ⊆ A := by
    rw [hTU]
    exact inter_subset_left.trans hA'A
  -- The remainder `Z = A ∖ ⋃ T j` is `Hⁿ`-null.
  have hZ : μHE[n] (A \ ⋃ j, disjointed (fun j ↦ A' ∩ S j) j) = 0 := by
    have hsub : A \ ⋃ j, disjointed (fun j ↦ A' ∩ S j) j ⊆ (A \ A') ∪ (M \ ⋃ j, S j) := by
      intro x hx
      rw [hTU] at hx
      by_cases hx' : x ∈ A'
      · exact Or.inr ⟨hAM hx.1, fun hxS ↦ hx.2 ⟨hx', hxS⟩⟩
      · exact Or.inl ⟨hx.1, hx'⟩
    exact measure_mono_null hsub (measure_union_null (ae_eq_set.1 hA'ae).2 hcov)
  have hA''ae : A =ᵐ[(μHE[n] : Measure (Rn N))] ⋃ j, disjointed (fun j ↦ A' ∩ S j) j := by
    rw [ae_eq_set, sdiff_eq_empty.2 hA''A]
    exact ⟨hZ, measure_empty⟩
  -- Left side: countable additivity of the set integral over the pieces.
  have hL : ∫⁻ x in A, g x * w x ∂μHE[n] =
      ∑' j, ∫⁻ x in disjointed (fun j ↦ A' ∩ S j) j, hg.mk g x * w x ∂μHE[n] := by
    calc ∫⁻ x in A, g x * w x ∂μHE[n] = ∫⁻ x in A, hg.mk g x * w x ∂μHE[n] := by
          refine lintegral_congr_ae ?_
          filter_upwards [hgg'] with x hx
          rw [hx]
      _ = ∫⁻ x in ⋃ j, disjointed (fun j ↦ A' ∩ S j) j, hg.mk g x * w x ∂μHE[n] :=
          setLIntegral_congr hA''ae
      _ = ∑' j, ∫⁻ x in disjointed (fun j ↦ A' ∩ S j) j, hg.mk g x * w x ∂μHE[n] :=
          lintegral_iUnion hTm hTd _
  -- Each piece by (Loc); monotone convergence for the series.
  have hpiece := fun j ↦ hloc j _ (hTS j) (hTm j) (hg.mk g) hg'm
  have hsum : ∑' j, ∫⁻ x in disjointed (fun j ↦ A' ∩ S j) j, hg.mk g x * w x ∂μHE[n] =
      ∫⁻ y, ∑' j, ∫⁻ x in disjointed (fun j ↦ A' ∩ S j) j ∩ f ⁻¹' {y}, hg.mk g x ∂μHE[k]
        ∂volume := by
    rw [lintegral_tsum fun j ↦ (hpiece j).1]
    exact tsum_congr fun j ↦ (hpiece j).2
  -- The slices of the pieces are Borel since `f` is continuous on the open `U`.
  have hslice : ∀ y : Rn m, MeasurableSet (U ∩ f ⁻¹' {y}) := by
    intro y
    have hopen : IsOpen (U ∩ f ⁻¹' {y}ᶜ) := hf.isOpen_inter_preimage hU isOpen_compl_singleton
    have heq : U ∩ f ⁻¹' {y} = U \ (U ∩ f ⁻¹' {y}ᶜ) := by
      ext x
      simp only [mem_inter_iff, Set.mem_sdiff, mem_preimage, mem_compl_iff, mem_singleton_iff]
      tauto
    rw [heq]
    exact hU.measurableSet.diff hopen.measurableSet
  have hTslice : ∀ j (y : Rn m), MeasurableSet (disjointed (fun j ↦ A' ∩ S j) j ∩ f ⁻¹' {y}) := by
    intro j y
    have hTU' : disjointed (fun j ↦ A' ∩ S j) j ⊆ U :=
      fun x hx ↦ hMU (hAM (hA''A (mem_iUnion.2 ⟨j, hx⟩)))
    rw [← inter_eq_left.2 hTU', inter_assoc]
    exact (hTm j).inter (hslice y)
  have hsumslice : ∀ y : Rn m,
      ∑' j, ∫⁻ x in disjointed (fun j ↦ A' ∩ S j) j ∩ f ⁻¹' {y}, hg.mk g x ∂μHE[k] =
        ∫⁻ x in (⋃ j, disjointed (fun j ↦ A' ∩ S j) j) ∩ f ⁻¹' {y}, hg.mk g x ∂μHE[k] := by
    intro y
    rw [iUnion_inter]
    exact (lintegral_iUnion (fun j ↦ hTslice j y)
      (fun i j hij ↦ Disjoint.mono inter_subset_left inter_subset_left (hTd hij)) _).symm
  -- Exceptional slices: (NS) for `Z = A ∖ ⋃ T j` and `Y = {x ∈ A : g x ≠ g' x}`.
  have hY : μHE[n] {x | x ∈ A ∧ g x ≠ hg.mk g x} = 0 := by
    have h := (ae_restrict_iff'₀ hA).1 hgg'
    rw [ae_iff] at h
    refine measure_mono_null (fun x hx ↦ ?_) h
    simp only [mem_ofPred_eq, not_imp]
    exact hx
  have hae : ∀ᵐ y ∂(volume : Measure (Rn m)),
      ∫⁻ x in (⋃ j, disjointed (fun j ↦ A' ∩ S j) j) ∩ f ⁻¹' {y}, hg.mk g x ∂μHE[k] =
        ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k] := by
    filter_upwards [hNS _ (fun x hx ↦ hAM hx.1) hZ, hNS _ (fun x hx ↦ hAM hx.1) hY]
      with y hZy hYy
    have hset : (⋃ j, disjointed (fun j ↦ A' ∩ S j) j) ∩ f ⁻¹' {y}
        =ᵐ[(μHE[k] : Measure (Rn N))] A ∩ f ⁻¹' {y} := by
      rw [ae_eq_set, sdiff_eq_empty.2 (inter_subset_inter_left _ hA''A)]
      refine ⟨measure_empty, measure_mono_null (fun x hx ↦ ?_) hZy⟩
      exact ⟨⟨hx.1.1, fun h ↦ hx.2 ⟨h, hx.1.2⟩⟩, hx.1.2⟩
    have hfun : ∀ᵐ x ∂(μHE[k] : Measure (Rn N)),
        x ∈ (⋃ j, disjointed (fun j ↦ A' ∩ S j) j) ∩ f ⁻¹' {y} → hg.mk g x = g x := by
      rw [ae_iff]
      refine measure_mono_null (fun x hx ↦ ?_) hYy
      simp only [mem_ofPred_eq, not_imp] at hx
      exact ⟨⟨hA''A hx.1.1, fun h ↦ hx.2 h.symm⟩, hx.1.2⟩
    have hmeas : MeasurableSet ((⋃ j, disjointed (fun j ↦ A' ∩ S j) j) ∩ f ⁻¹' {y}) := by
      rw [iUnion_inter]
      exact MeasurableSet.iUnion fun j ↦ hTslice j y
    rw [setLIntegral_congr_fun_ae hmeas hfun]
    exact setLIntegral_congr hset
  calc ∫⁻ x in A, g x * w x ∂μHE[n]
      = ∑' j, ∫⁻ x in disjointed (fun j ↦ A' ∩ S j) j, hg.mk g x * w x ∂μHE[n] := hL
    _ = ∫⁻ y, ∑' j, ∫⁻ x in disjointed (fun j ↦ A' ∩ S j) j ∩ f ⁻¹' {y}, hg.mk g x ∂μHE[k]
          ∂volume := hsum
    _ = ∫⁻ y, ∫⁻ x in (⋃ j, disjointed (fun j ↦ A' ∩ S j) j) ∩ f ⁻¹' {y}, hg.mk g x ∂μHE[k]
          ∂volume := lintegral_congr hsumslice
    _ = ∫⁻ y, (∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]) ∂volume := lintegral_congr_ae hae

/-- **`T_x M` and `d^M f_x` exist for `Hⁿ`-a.e. `x ∈ M`** (Simon Ch. 3, 2.1–2.2 with Remark 1.3
and Lemma 1.2; conclusion (a) of the area and co-area formulas), assuming Lemma 1.2, the `C¹`
approximation theorem (C1) and the chart lemma (CT). By `rectifiable_c1_chart_pieces`, `M` is
covered up to an `Hⁿ`-null set by the images `ψⱼ(Eⱼ)`, `Eⱼ ⊆ Dⱼ`, of `C¹` immersions `ψⱼ` of
open sets `Dⱼ ⊆ ℝⁿ`, Lipschitz on `Dⱼ`. By (CT), off an `Lⁿ`-null set `Dⱼ \ Tⱼ`, every
`u ∈ Dⱼ` with `ψⱼ(u) ∈ M` has the weighted approximate tangent plane `range Dψⱼ(u)` at `ψⱼ(u)`
and `D_{Dψⱼ(u) w} f(ψⱼ(u)) = D(f ∘ ψⱼ)(u) w`; there part (ii) of
`chart_coarea_jacobian_identification` gives `d^M f_x`. The remaining points of `M` lie in
`(M \ ⋃ⱼ ψⱼ(Eⱼ)) ∪ ⋃ⱼ ψⱼ(Dⱼ \ Tⱼ)`, which is `Hⁿ`-null since `Hⁿ(ψⱼ(Z)) ≤ Kⱼⁿ Lⁿ(Z)`. -/
theorem Submission.coarea_tangent_existence :
    SubmanifoldCoverCharacterization →
    (∀ (n p : ℕ) (f : Rn n → Rn p) (K : ℝ≥0), LipschitzWith K f → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ g : Rn n → Rn p, ContDiff ℝ 1 g ∧
        volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x} < ε) →
    (∀ (n ℓ p : ℕ) (M U : Set (Rn (n + ℓ))) (θ : Rn (n + ℓ) → ℝ) (f : Rn (n + ℓ) → Rn p)
      (V : Set (Rn n)) (ψ : Rn n → Rn (n + ℓ)), NullMeasurableSet M μHE[n] →
      IsPositiveLocallyIntegrableWeight n M θ → IsOpen U → M ⊆ U → LocallyLipschitzOn U f →
      IsOpen V → ContDiffOn ℝ 1 ψ V → (∀ u ∈ V, Function.Injective (fderiv ℝ ψ u)) →
      ∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ V → ψ u ∈ M →
        HasWeightedApproximateTangentSpaceAt n M θ (ψ u)
            (LinearMap.range (fderiv ℝ ψ u).toLinearMap) ∧
          DifferentiableAt ℝ (f ∘ ψ) u ∧
          ∀ w : Rn n, HasLineDerivAt ℝ f (fderiv ℝ (f ∘ ψ) u w) (ψ u) (fderiv ℝ ψ u w)) →
    ∀ (n ℓ p : ℕ) (M U : Set (Rn (n + ℓ))) (θ : Rn (n + ℓ) → ℝ) (f : Rn (n + ℓ) → Rn p),
      NullMeasurableSet M μHE[n] → CountablyRectifiable n M →
      IsPositiveLocallyIntegrableWeight n M θ → IsOpen U → M ⊆ U → LocallyLipschitzOn U f →
      ∀ᵐ x ∂(μHE[n] : Measure (Rn (n + ℓ))), x ∈ M →
        ∃ (P : Submodule ℝ (Rn (n + ℓ))) (L : P →L[ℝ] Rn p),
          HasWeightedApproximateTangentSpaceAt n M θ x P ∧ HasTangentialDifferentialAt P f x L := by
  intro hSub hC1 hCT n ℓ p M U θ f hM hrect hθ hU hMU hf
  -- Step 1 (charts): `Hⁿ(M \ ⋃ⱼ ψⱼ(Eⱼ)) = 0`, `Eⱼ ⊆ Dⱼ`.
  obtain ⟨D, ψ, G, E, hDo, hψC, -, hψL, hDψ, -, -, hED, -, hcov⟩ :=
    Submission.rectifiable_c1_chart_pieces hSub hC1 n ℓ p M U f hrect hU hMU hf
  -- Step 2 (chart lemma): the conclusion of (CT) for `ψⱼ` holds on an `Lⁿ`-conull set `Tⱼ`.
  choose T hTae hTgood using fun j ↦
    (hCT n ℓ p M U θ f (D j) (ψ j) hM hθ hU hMU hf (hDo j) (hψC j) (hDψ j)).exists_mem
  -- Step 4 (null images): `Hⁿ(ψⱼ(Dⱼ \ Tⱼ)) ≤ Kⱼⁿ Lⁿ(Dⱼ \ Tⱼ) = 0`.
  have hnull : ∀ j, μHE[n] (ψ j '' (D j \ T j)) = 0 := by
    intro j
    obtain ⟨K, hK⟩ := hψL j
    have hvol : volume (D j \ T j) = 0 :=
      measure_mono_null (fun u hu ↦ hu.2) (mem_ae_iff.1 (hTae j))
    refine le_antisymm ?_ zero_le
    calc μHE[n] (ψ j '' (D j \ T j))
        ≤ (K : ℝ≥0∞) ^ n * μHE[n] (D j \ T j) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hK.mono Set.sdiff_subset)
      _ = 0 := by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hvol, mul_zero]
  -- Steps 3–4: every `x ∈ M` failing the conclusion lies in the `Hⁿ`-null set
  -- `(M \ ⋃ⱼ ψⱼ(Eⱼ)) ∪ ⋃ⱼ ψⱼ(Dⱼ \ Tⱼ)`.
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_union_null hcov (measure_iUnion_null hnull))
  intro x hx
  obtain ⟨hxM, hxbad⟩ := not_imp.1 hx
  by_cases hxcov : x ∈ ⋃ j, ψ j '' E j
  · obtain ⟨j, u, hu, rfl⟩ := mem_iUnion.1 hxcov
    refine Or.inr (mem_iUnion.2 ⟨j, u, ⟨hED j hu, fun huT ↦ hxbad ?_⟩, rfl⟩)
    -- Step 3: at `x = ψⱼ(u)` with `u ∈ Tⱼ`, identification (ii) gives `L` on `range Dψⱼ(u)`.
    obtain ⟨hT, -, hline⟩ := hTgood j u huT (hED j hu) hxM
    obtain ⟨-, ⟨L, hL⟩, -⟩ := Submission.chart_coarea_jacobian_identification n (n + ℓ) p M θ f
      (ψ j u) (fderiv ℝ (ψ j) u) (fderiv ℝ (f ∘ ψ j) u) (hθ.1 _ hxM).ne' (hDψ j u (hED j hu)) hT
      hline
    exact ⟨_, L, hT, hL⟩
  · exact Or.inl ⟨hxM, hxcov⟩

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

/-- **Lusin's theorem for `Lⁿ` with closed sets and finite-dimensional targets** (Simon Ch. 2,
proof of Theorem 1.5, `chapter-02.txt` lines 248–251: Lusin's theorem "applies to sets of
infinite measure for `Lⁿ`"; cf. Ch. 1, Theorems 1.15 and 1.17): for a Borel `u : ℝⁿ → F`, `F`
finite-dimensional, a Borel `S ⊆ ℝⁿ` and `ε ∈ (0, ∞]`, some closed `C ⊆ S` has `Lⁿ(S ∖ C) < ε`
and `u|C` continuous. `Lⁿ` is outer regular on sets of finite measure, so exhausting by its
finite-measure spanning sets gives, for every Borel `A`, an open `U ⊇ A` with `Lⁿ(U ∖ A)`
arbitrarily small, and complements give a closed `C ⊆ A` with `Lⁿ(A ∖ C)` small (Simon 1.15).
For each `V` in a countable basis of `F` take such a `U_V ⊇ u⁻¹(V)`. Off
`E = ⋃_V (U_V ∖ u⁻¹(V))` each `u⁻¹(V)` agrees with the open `U_V`, so `u` is continuous on `Eᶜ`;
a closed `C ⊆ S ∖ E` with small defect works. -/
theorem Submission.lusin_closed_subset_continuousOn_volume : ∀ (n : ℕ) (F : Type)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] (u : Rn n → F) (S : Set (Rn n)), Measurable u → MeasurableSet S →
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ C ⊆ S, IsClosed C ∧ volume (S \ C) < ε ∧ ContinuousOn u C := by
  intro n F _ _ _ _ _ u S hu hS ε hε
  -- Outer approximation of an arbitrary Borel set by open sets, through the finite-measure
  -- spanning sets of the σ-finite measure `Lⁿ`.
  have outer : ∀ A : Set (Rn n), MeasurableSet A → ∀ δ : ℝ≥0∞, δ ≠ 0 →
      ∃ U, A ⊆ U ∧ IsOpen U ∧ volume (U \ A) < δ := by
    intro A hA δ hδ
    obtain ⟨δ', hδ'0, hδ'⟩ := ENNReal.exists_pos_sum_of_countable hδ ℕ
    have hj : ∀ j, ∃ U, A ∩ spanningSets volume j ⊆ U ∧ IsOpen U ∧
        volume (U \ (A ∩ spanningSets volume j)) < δ' j := fun j ↦ by
      obtain ⟨U, hAU, hU, -, hUA⟩ :=
        (hA.inter (measurableSet_spanningSets volume j)).exists_isOpen_sdiff_lt
          ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top volume j)).ne
          (ENNReal.coe_ne_zero.2 (hδ'0 j).ne')
      exact ⟨U, hAU, hU, hUA⟩
    choose U hAU hU hUA using hj
    refine ⟨⋃ j, U j, fun x hx ↦ ?_, isOpen_iUnion hU, ?_⟩
    · have hx' : x ∈ ⋃ j, spanningSets (volume : Measure (Rn n)) j := by
        rw [iUnion_spanningSets]
        exact mem_univ x
      obtain ⟨j, hxj⟩ := mem_iUnion.1 hx'
      exact mem_iUnion.2 ⟨j, hAU j ⟨hx, hxj⟩⟩
    · calc volume ((⋃ j, U j) \ A) ≤ volume (⋃ j, U j \ (A ∩ spanningSets volume j)) := by
            refine measure_mono fun x hx ↦ ?_
            obtain ⟨j, hxj⟩ := mem_iUnion.1 hx.1
            exact mem_iUnion.2 ⟨j, hxj, fun h ↦ hx.2 h.1⟩
        _ ≤ ∑' j, volume (U j \ (A ∩ spanningSets volume j)) := measure_iUnion_le _
        _ ≤ ∑' j, (δ' j : ℝ≥0∞) := ENNReal.tsum_le_tsum fun j ↦ (hUA j).le
        _ < δ := hδ'
  -- Closed inner approximation, by complements.
  have inner : ∀ A : Set (Rn n), MeasurableSet A → ∀ δ : ℝ≥0∞, δ ≠ 0 →
      ∃ C ⊆ A, IsClosed C ∧ volume (A \ C) < δ := by
    intro A hA δ hδ
    obtain ⟨U, hAU, hU, hUA⟩ := outer Aᶜ hA.compl δ hδ
    refine ⟨Uᶜ, fun x hx ↦ not_not.1 fun h ↦ hx (hAU h), hU.isClosed_compl, ?_⟩
    have hdiff : A \ Uᶜ = U \ Aᶜ := by
      ext x
      simp only [Set.mem_sdiff, mem_compl_iff, not_not]
      exact and_comm
    rwa [hdiff]
  -- A countable basis of `F` and the exceptional set `E`.
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  have hB := TopologicalSpace.isBasis_countableBasis F
  have : Countable (TopologicalSpace.countableBasis F) :=
    (TopologicalSpace.countable_countableBasis F).to_subtype
  have hpre : ∀ V : TopologicalSpace.countableBasis F, MeasurableSet (u ⁻¹' (V : Set F)) :=
    fun V ↦ hu (hB.isOpen V.2).measurableSet
  obtain ⟨δ', hδ'0, hδ'⟩ :=
    ENNReal.exists_pos_sum_of_countable hε2 (TopologicalSpace.countableBasis F)
  have hV : ∀ V : TopologicalSpace.countableBasis F, ∃ U, u ⁻¹' (V : Set F) ⊆ U ∧ IsOpen U ∧
      volume (U \ u ⁻¹' (V : Set F)) < δ' V := fun V ↦
    outer _ (hpre V) _ (ENNReal.coe_ne_zero.2 (hδ'0 V).ne')
  choose U hVU hU hUV using hV
  set E := ⋃ V, U V \ u ⁻¹' (V : Set F)
  have hEm : MeasurableSet E := MeasurableSet.iUnion fun V ↦ (hU V).measurableSet.diff (hpre V)
  have hEε : volume E < ε / 2 :=
    calc volume E ≤ ∑' V, volume (U V \ u ⁻¹' (V : Set F)) := measure_iUnion_le _
      _ ≤ ∑' V, (δ' V : ℝ≥0∞) := ENNReal.tsum_le_tsum fun V ↦ (hUV V).le
      _ < ε / 2 := hδ'
  -- Off `E`, `u⁻¹(V) = U_V`, so `u` is continuous on `Eᶜ`.
  have hcont : ContinuousOn u Eᶜ := by
    rw [continuousOn_iff_continuous_domRestrict, hB.continuous_iff]
    intro V hVB
    have hpreim : Eᶜ.domRestrict u ⁻¹' V = Subtype.val ⁻¹' U ⟨V, hVB⟩ := by
      ext ⟨x, hx⟩
      simp only [mem_preimage, Set.domRestrict_apply]
      refine ⟨fun h ↦ hVU ⟨V, hVB⟩ h, fun h ↦ not_not.1 fun h' ↦ hx ?_⟩
      exact mem_iUnion.2 ⟨⟨V, hVB⟩, h, h'⟩
    rw [hpreim]
    exact (hU _).preimage continuous_subtype_val
  -- A closed subset of `S ∖ E` with small defect.
  obtain ⟨C, hCS, hC, hCε⟩ := inner (S ∩ Eᶜ) (hS.inter hEm.compl) (ε / 2) hε2
  refine ⟨C, hCS.trans inter_subset_left, hC, ?_, hcont.mono (hCS.trans inter_subset_right)⟩
  calc volume (S \ C) ≤ volume ((S ∩ Eᶜ) \ C ∪ E) := by
        refine measure_mono fun x hx ↦ ?_
        by_cases hxE : x ∈ E
        · exact Or.inr hxE
        · exact Or.inl ⟨⟨hx.1, hxE⟩, hx.2⟩
    _ ≤ volume ((S ∩ Eᶜ) \ C) + volume E := measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hCε hEε
    _ = ε := ENNReal.add_halves ε

/-- **Egoroff's theorem on `ℝⁿ` with a closed good set** (Simon Ch. 2, proof of Theorem 1.5,
`chapter-02.txt` lines 260–265, with closed inner regularity Ch. 1, Theorem 1.15(2)): if Borel
`ηₖ → g` pointwise on a Borel set `S`, then for every `ε > 0` there is a closed `A ⊆ S` with
`Lⁿ(S ∖ A) < ε` such that `ηₖ → g` uniformly on every compact `Q ⊆ A`. Egoroff on the
finite-measure sets `S ∩ B_{j+1}(0)` gives exceptional sets `tⱼ` with `∑ Lⁿ(tⱼ) < ε/2`; closed
`Fⱼ ⊆ (S ∖ ⋃ tᵢ) ∩ {j ≤ |x| ≤ j + 1}` with total defect `< ε/2` form a locally finite family; and
a compact `Q ⊆ A = ⋃ Fⱼ` lies in a single good set `(S ∩ B_{J+1}(0)) ∖ t_J`. -/
theorem Submission.egorov_closed_subset_uniformOn_compact_volume : ∀ (n : ℕ) (η : ℕ → Rn n → ℝ)
    (g : Rn n → ℝ) (S : Set (Rn n)), (∀ k, Measurable (η k)) → Measurable g → MeasurableSet S →
    (∀ x ∈ S, Tendsto (fun k => η k x) atTop (𝓝 (g x))) → ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ A ⊆ S, IsClosed A ∧ volume (S \ A) < ε ∧
      ∀ Q : Set (Rn n), IsCompact Q → Q ⊆ A → TendstoUniformlyOn η g atTop Q := by
  intro n η g S hη hg hS hconv ε hε
  -- Error budget: positive `δ j` with `∑ δ j < ε / 2`.
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.half_pos hε.ne').ne' ℕ
  have hδ0 : ∀ j, (δ j : ℝ≥0∞) ≠ 0 := fun j => ENNReal.coe_ne_zero.2 (hδpos j).ne'
  -- Egorov on the finite-measure pieces `S ∩ B_{j+1}(0)`.
  have hEg : ∀ j : ℕ, ∃ t ⊆ S ∩ Metric.ball (0 : Rn n) (j + 1), MeasurableSet t ∧
      volume t ≤ δ j ∧ TendstoUniformlyOn η g atTop ((S ∩ Metric.ball (0 : Rn n) (j + 1)) \ t) :=
    fun j => tendstoUniformlyOn_of_ae_tendsto (fun k => (hη k).stronglyMeasurable)
      hg.stronglyMeasurable (hS.inter Metric.isOpen_ball.measurableSet)
      (ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono inter_subset_right))
      (ae_of_all _ fun x hx => hconv x hx.1) (pos_iff_ne_zero.2 (hδ0 j))
  choose t htS htm htμ htu using hEg
  -- `A₀ = S ∖ ⋃ tⱼ` is measurable.
  have hA₀ : MeasurableSet (S \ ⋃ i, t i) := hS.diff (MeasurableSet.iUnion htm)
  -- Closed inner approximation of `A₀` on each annulus `{j ≤ |x| ≤ j + 1}`.
  have hcl : ∀ j : ℕ, ∃ F ⊆ (S \ ⋃ i, t i) ∩
      (Metric.closedBall (0 : Rn n) (j + 1) \ Metric.ball 0 j), IsClosed F ∧
      volume (((S \ ⋃ i, t i) ∩ (Metric.closedBall (0 : Rn n) (j + 1) \ Metric.ball 0 j)) \ F) <
        δ j :=
    fun j => (hA₀.inter (Metric.isClosed_closedBall.measurableSet.diff
      Metric.isOpen_ball.measurableSet)).exists_isClosed_sdiff_lt
      (ne_top_of_le_ne_top measure_closedBall_lt_top.ne
        (measure_mono (inter_subset_right.trans sdiff_subset))) (hδ0 j)
  choose F hFA hFc hFμ using hcl
  refine ⟨⋃ j, F j, iUnion_subset fun j => (hFA j).trans (inter_subset_left.trans sdiff_subset),
    ?_, ?_, ?_⟩
  · -- `⋃ Fⱼ` is closed: `Fⱼ` lies outside `B_j(0)`, so the family is locally finite.
    refine LocallyFinite.isClosed_iUnion (fun x => ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos,
      (Set.finite_Iio ⌈‖x‖ + 1⌉₊).subset ?_⟩) hFc
    rintro j ⟨y, hyF, hyx⟩
    have hj : (j : ℝ) ≤ ‖y‖ := by simpa using ((hFA j hyF).2).2
    have hyx' : ‖y - x‖ < 1 := by simpa [dist_eq_norm] using hyx
    exact Nat.lt_ceil.2 (by linarith [norm_sub_norm_le y x])
  · -- Measure estimate: `S ∖ ⋃ Fⱼ ⊆ ⋃ tⱼ ∪ ⋃ ((A₀ ∩ annulusⱼ) ∖ Fⱼ)`.
    have hsub : S \ ⋃ j, F j ⊆ (⋃ j, t j) ∪ ⋃ j : ℕ, (((S \ ⋃ i, t i) ∩
        (Metric.closedBall (0 : Rn n) (j + 1) \ Metric.ball 0 j)) \ F j) := by
      intro x hx
      by_cases hxt : x ∈ ⋃ j, t j
      · exact Or.inl hxt
      · refine Or.inr (mem_iUnion.2 ⟨⌊‖x‖⌋₊, ⟨⟨hx.1, hxt⟩, ?_, ?_⟩,
          fun hxF => hx.2 (mem_iUnion.2 ⟨_, hxF⟩)⟩)
        · simpa using (Nat.lt_floor_add_one ‖x‖).le
        · simpa using Nat.floor_le (norm_nonneg x)
    calc volume (S \ ⋃ j, F j)
        ≤ volume (⋃ j, t j) + volume (⋃ j : ℕ, (((S \ ⋃ i, t i) ∩
            (Metric.closedBall (0 : Rn n) (j + 1) \ Metric.ball 0 j)) \ F j)) :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ (∑' j, (δ j : ℝ≥0∞)) + ∑' j, (δ j : ℝ≥0∞) :=
          add_le_add ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum htμ))
            ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => (hFμ j).le))
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hδsum hδsum
      _ = ε := ENNReal.add_halves ε
  · -- A compact `Q ⊆ ⋃ Fⱼ ⊆ A₀` lies in some `B_{J+1}(0)`, hence in one Egorov good set.
    intro Q hQ hQA
    obtain ⟨r, hr⟩ := hQ.isBounded.subset_ball 0
    refine (htu ⌈r⌉₊).mono fun x hx => ?_
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hQA hx)
    have hxA₀ := (hFA j hj).1
    exact ⟨⟨hxA₀.1, Metric.ball_subset_ball (by linarith [Nat.le_ceil r]) (hr hx)⟩,
      fun hxt => hxA₀.2 (mem_iUnion.2 ⟨_, hxt⟩)⟩

/-- **Uniform remainder estimate 1.6(‡) on a closed set** (Simon Ch. 2, proof of Theorem 1.5,
`chapter-02.txt` lines 251–265): let `f : ℝⁿ → ℝ` be `K`-Lipschitz, `L` Borel and `S` Borel with
`Df(x) = L(x)` at every `x ∈ S`. Then for `ε ∈ (0, ∞]` there is a closed `A ⊆ S` with
`Lⁿ(S ∖ A) < ε` such that for every compact `Q ⊆ A` and `ε' > 0` some `δ > 0` gives
`|f(y) − f(x) − L(x)(y − x)| ≤ ε'|y − x|` for `x ∈ Q`, `y ∈ A`, `|x − y| < δ`. With
`R(x, y) = (f(y) − f(x) − L(x)(y − x))/|y − x|`, the suprema
`ηₖ(x) = sup {|R(x, y)| : y ∈ S, 0 < |y − x| < 1/(k + 1)}` are at most `K + ‖L(x)‖`, tend to `0`
on `S`, and are Borel (by continuity of `f` off the diagonal they are suprema over a countable
dense `D ⊆ S`); Egoroff (`Submission.egorov_closed_subset_uniformOn_compact_volume`) gives `A`,
and `η_{k₀} < ε'` on `Q` gives the estimate with `δ = 1/(k₀ + 1)`. -/
theorem Submission.lipschitz_uniform_remainder_on_closed_subset : ∀ (n : ℕ) (f : Rn n → ℝ)
    (K : ℝ≥0) (L : Rn n → (Rn n →L[ℝ] ℝ)) (S : Set (Rn n)), LipschitzWith K f → Measurable L →
    MeasurableSet S → (∀ x ∈ S, HasFDerivAt f (L x) x) → ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ A ⊆ S, IsClosed A ∧ volume (S \ A) < ε ∧
      ∀ Q : Set (Rn n), IsCompact Q → Q ⊆ A → ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ Q, ∀ y ∈ A, dist x y < δ → ‖f y - f x - L x (y - x)‖ ≤ ε' * ‖y - x‖ := by
  intro n f K L S hf hL hS hdiff ε hε
  -- Step 1: `φ k x y = |R(x, y)|` on the shell `0 < |y - x| < 1/(k + 1)` (`0` elsewhere; Simon's
  -- `1/k`, `k ≥ 1`, reindexed) and `η k x = sup_{y ∈ S} φ k x y`, with `0 ≤ φ ≤ K + ‖L x‖`.
  set φ : ℕ → Rn n → Rn n → ℝ := fun k x y =>
    if 0 < ‖y - x‖ ∧ ‖y - x‖ < 1 / ((k : ℝ) + 1) then ‖f y - f x - L x (y - x)‖ / ‖y - x‖
    else 0 with hφ
  set η : ℕ → Rn n → ℝ := fun k x => ⨆ y : S, φ k x y
  have hφ0 : ∀ k x y, 0 ≤ φ k x y := by
    intro k x y
    simp only [hφ]
    split_ifs
    · positivity
    · exact le_rfl
  have hφK : ∀ k x y, φ k x y ≤ K + ‖L x‖ := by
    intro k x y
    simp only [hφ]
    split_ifs with h
    · rw [div_le_iff₀ h.1]
      calc ‖f y - f x - L x (y - x)‖ ≤ ‖f y - f x‖ + ‖L x (y - x)‖ := norm_sub_le _ _
        _ ≤ K * ‖y - x‖ + ‖L x‖ * ‖y - x‖ :=
          add_le_add (by simpa only [dist_eq_norm] using hf.dist_le_mul y x) ((L x).le_opNorm _)
        _ = (K + ‖L x‖) * ‖y - x‖ := by ring
    · positivity
  have hbdd : ∀ k x (T : Set (Rn n)), BddAbove (range fun y : T => φ k x y) :=
    fun k x T => ⟨K + ‖L x‖, by rintro _ ⟨y, rfl⟩; exact hφK k x y⟩
  have hη0 : ∀ k x, 0 ≤ η k x := fun k x => Real.iSup_nonneg fun y => hφ0 k x y
  -- Step 2: `η k x → 0` for `x ∈ S`, since `|R(x, y)| ≤ e/2` for `|y - x| < ρ(x, e)`.
  have hconv : ∀ x ∈ S, Tendsto (fun k => η k x) atTop (𝓝 0) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro e he
    obtain ⟨ρ, hρ, hball⟩ :=
      Metric.eventually_nhds_iff.mp ((hdiff x hx).isLittleO.bound (half_pos he))
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hρ
    refine ⟨N, fun k hk => ?_⟩
    have hle : η k x ≤ e / 2 := by
      refine Real.iSup_le (fun y => ?_) (half_pos he).le
      simp only [hφ]
      split_ifs with h
      · rw [div_le_iff₀ h.1]
        refine hball ?_
        rw [dist_eq_norm]
        calc ‖(y : Rn n) - x‖ < 1 / ((k : ℝ) + 1) := h.2
          _ ≤ 1 / ((N : ℝ) + 1) := by gcongr
          _ < ρ := hN
      · exact (half_pos he).le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hη0 k x)]
    linarith
  -- Step 3: each `η k` is Borel. For a countable `D ⊆ S` with `S ⊆ closure D`,
  -- `η k x = sup_{z ∈ D} φ k x z`, as `z ↦ |R(x, z)|` is continuous on the open shell.
  have hfc : Continuous f := hf.continuous
  obtain ⟨D, hDS, hDc, hSD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  have hηD : ∀ k x, η k x = ⨆ z : D, φ k x z := by
    intro k x
    have hM0 : 0 ≤ ⨆ z : D, φ k x z := Real.iSup_nonneg fun z => hφ0 k x z
    refine le_antisymm (Real.iSup_le (fun y => ?_) hM0)
      (Real.iSup_le (fun z => le_ciSup (hbdd k x S) ⟨z, hDS z.2⟩) (hη0 k x))
    by_cases hy : 0 < ‖(y : Rn n) - x‖ ∧ ‖(y : Rn n) - x‖ < 1 / ((k : ℝ) + 1)
    · have hU : {z : Rn n | 0 < ‖z - x‖ ∧ ‖z - x‖ < 1 / ((k : ℝ) + 1)} ∈ 𝓝 (y : Rn n) := by
        refine IsOpen.mem_nhds ?_ hy
        have hc : Continuous fun z : Rn n => ‖z - x‖ := (continuous_id.sub continuous_const).norm
        exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
      have hR : ContinuousAt (fun z => ‖f z - f x - L x (z - x)‖ / ‖z - x‖) (y : Rn n) := by
        refine ContinuousAt.div ?_ ?_ hy.1.ne' <;> fun_prop
      have hRD : Tendsto (fun z => ‖f z - f x - L x (z - x)‖ / ‖z - x‖) (𝓝[D] (y : Rn n))
          (𝓝 (‖f y - f x - L x (y - x)‖ / ‖(y : Rn n) - x‖)) :=
        tendsto_nhdsWithin_of_tendsto_nhds hR
      have : (𝓝[D] (y : Rn n)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hSD y.2)
      calc φ k x y = ‖f y - f x - L x (y - x)‖ / ‖(y : Rn n) - x‖ := ite_eq_left hy
        _ ≤ ⨆ z : D, φ k x z := by
          refine le_of_tendsto hRD ?_
          filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hU] with z hzD hzU
          calc ‖f z - f x - L x (z - x)‖ / ‖z - x‖ = φ k x z := (ite_eq_left hzU).symm
            _ ≤ ⨆ z : D, φ k x z := le_ciSup (hbdd k x D) ⟨z, hzD⟩
    · calc φ k x y = 0 := ite_eq_right hy
        _ ≤ ⨆ z : D, φ k x z := hM0
  have hηm : ∀ k, Measurable (η k) := by
    intro k
    have hφm : ∀ z : D, Measurable fun x => φ k x z := by
      intro z
      have hd : Measurable fun x : Rn n => ‖(z : Rn n) - x‖ :=
        (measurable_const.sub measurable_id).norm
      simp only [hφ]
      refine Measurable.ite ((measurableSet_lt measurable_const hd).inter
        (measurableSet_lt hd measurable_const)) ?_ measurable_const
      exact ((measurable_const.sub hfc.measurable).sub (ContinuousLinearMap.measurable_apply₂.comp
        (hL.prodMk (measurable_const.sub measurable_id)))).norm.div hd
    have : Countable D := hDc.to_subtype
    rw [show η k = fun x => ⨆ z : D, φ k x z from funext (hηD k)]
    exact Measurable.iSup hφm
  -- Step 4: Egoroff (sibling `egorov_sigma_finite`) with limit `0` gives the closed set `A`.
  obtain ⟨A, hAS, hAc, hAμ, hAu⟩ := Submission.egorov_closed_subset_uniformOn_compact_volume n η 0
    S hηm measurable_const hS hconv ε hε
  refine ⟨A, hAS, hAc, hAμ, fun Q hQ hQA ε' hε' => ?_⟩
  -- Step 5: `η k₀ < ε'` on `Q` gives the estimate for `y ∈ A`, `|x - y| < δ = 1/(k₀ + 1)`.
  obtain ⟨k₀, hk₀⟩ := (Metric.tendstoUniformlyOn_iff.mp (hAu Q hQ hQA) ε' hε').exists
  refine ⟨1 / ((k₀ : ℝ) + 1), by positivity, fun x hx y hy hxy => ?_⟩
  obtain rfl | hyx := eq_or_ne y x
  · simp
  have hpos : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  have hlt : ‖y - x‖ < 1 / ((k₀ : ℝ) + 1) := by rwa [← dist_eq_norm, dist_comm]
  have h1 : ‖f y - f x - L x (y - x)‖ ≤ η k₀ x * ‖y - x‖ := by
    rw [← div_le_iff₀ hpos]
    calc ‖f y - f x - L x (y - x)‖ / ‖y - x‖ = φ k₀ x y := (ite_eq_left ⟨hpos, hlt⟩).symm
      _ ≤ η k₀ x := le_ciSup (hbdd k₀ x S) ⟨y, hAS hy⟩
  have h2 : η k₀ x < ε' := by
    have h := hk₀ x hx
    rwa [Pi.zero_apply, dist_comm, Real.dist_eq, sub_zero, abs_of_nonneg (hη0 k₀ x)] at h
  exact h1.trans (mul_le_mul_of_nonneg_right h2.le (norm_nonneg _))

/-- **Simon Ch. 2, Theorem 1.5 (C¹ approximation), scalar case** (`chapter-02.txt` lines 165–168,
proof lines 246–266). For a Lipschitz `f : ℝⁿ → ℝ` and `ε ∈ (0, ∞]` there is a `C¹` function `g`
with `Lⁿ({f ≠ g} ∪ {Df ≠ Dg}) < ε`, where `D` is `fderiv` (`0` where `f` is not differentiable).
Rademacher, Lusin for `Df` (`ε/2`), the uniform Taylor remainder on a closed `A` (`ε/2`) and
Whitney's extension theorem 1.6 (lines 173–184) applied on `A`. Whitney's theorem is proved inline:
off `A`, `g` averages the jets `f(p) + Df(p)(· - p)` at nearest points `p ∈ A` with a partition of
unity on Vitali-selected balls `B(c, min(1, d(c, A))/100)`; the balls have bounded overlap, so the
weights satisfy `∑ ‖Dw‖ ≲ 1/d(·, A)`. -/
theorem Submission.lipschitz_real_c1_approximation : ∀ (n : ℕ) (f : Rn n → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x} < ε := by
  intro n f K hf ε hε
  -- Whitney's extension theorem (Simon Ch. 2, Theorem 1.6) for the values of `f` on a closed `A`
  -- and a gradient field `L` continuous on `A` with the uniform remainder condition 1.6(‡).
  have hW : ∀ (A : Set (Rn n)) (L : Rn n → (Rn n →L[ℝ] ℝ)), IsClosed A →
      ContinuousOn L A → (∀ Q : Set (Rn n), IsCompact Q → Q ⊆ A → ∀ ε' : ℝ, 0 < ε' →
        ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < δ →
          ‖f y - f x - L x (y - x)‖ ≤ ε' * ‖y - x‖) →
      ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ (∀ a ∈ A, g a = f a) ∧
        ∀ a ∈ A, HasFDerivAt g (L a) a := by
    intro A L hA hLc hrem
    rcases A.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => 0, contDiff_const, by simp, by simp⟩
    -- Compact-uniform compatibility near a point `a ∈ A`, for pairs of anchors.
    have hloc : ∀ a ∈ A, ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
        (∀ b ∈ A, dist b a < δ → ‖L b - L a‖ ≤ e) ∧
        ∀ b ∈ A, dist b a < δ → ∀ c ∈ A, dist c a < δ →
          ‖f c - f b - L b (c - b)‖ ≤ e * ‖c - b‖ := by
      intro a ha e he
      obtain ⟨ρ, hρ, hρrem⟩ := hrem (A ∩ Metric.closedBall a 1)
        ((isCompact_closedBall a 1).inter_left hA) inter_subset_left e he
      obtain ⟨η, hη, hD⟩ := Metric.continuousWithinAt_iff.mp (hLc a ha) e he
      have h1 := min_le_left 1 (min η (ρ / 3))
      have h2 : min 1 (min η (ρ / 3)) ≤ η := (min_le_right _ _).trans (min_le_left _ _)
      have h3 : min 1 (min η (ρ / 3)) ≤ ρ / 3 := (min_le_right _ _).trans (min_le_right _ _)
      refine ⟨min 1 (min η (ρ / 3)), lt_min one_pos (lt_min hη (by positivity)), h1,
        fun b hb hba => ?_, fun b hb hba c hc hca => ?_⟩
      · simpa only [dist_eq_norm] using (hD hb (hba.trans_le h2)).le
      · refine hρrem b ⟨hb, Metric.mem_closedBall.2 (by linarith)⟩ c hc ?_
        have htri := dist_triangle b a c
        rw [dist_comm a c] at htri
        linarith
    -- Whitney radius `r x = min 1 d(x, A) / 100`.
    obtain ⟨r, hr⟩ : ∃ r : Rn n → ℝ, ∀ x, r x = min 1 (Metric.infDist x A) / 100 :=
      ⟨_, fun _ => rfl⟩
    have hr0 : ∀ x, 0 ≤ r x := fun x => by
      rw [hr]; exact div_nonneg (le_min zero_le_one Metric.infDist_nonneg) (by norm_num)
    have hr1 : ∀ x, r x ≤ 1 / 100 := fun x => by
      rw [hr]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hrd : ∀ x, 100 * r x ≤ Metric.infDist x A := fun x => by
      rw [hr]; linarith [min_le_right (1 : ℝ) (Metric.infDist x A)]
    have hrpos : ∀ x ∉ A, 0 < r x := fun x hx => by
      rw [hr]
      exact div_pos (lt_min one_pos ((hA.notMem_iff_infDist_pos hne).mp hx)) (by norm_num)
    have hrlip : ∀ x y, r x ≤ r y + dist x y / 100 := by
      intro x y
      have h := ((Metric.lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
      simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
      have h' := (abs_sub_le_iff.mp h).1
      rw [hr, hr]
      linarith
    have hnA : ∀ x y, dist y x < r x → y ∉ A := by
      intro x y hy hyA
      have hi := Metric.infDist_le_dist_of_mem (x := x) hyA
      rw [dist_comm x y] at hi
      linarith [hrd x, hr0 x]
    -- Vitali: disjoint balls `B(c, r c)`, `c ∈ S`, whose fourfold enlargements cover `Aᶜ`.
    obtain ⟨S, hSA, hSdisj, hScov⟩ : ∃ S : Set (Rn n), S ⊆ Aᶜ ∧
        S.PairwiseDisjoint (fun c => Metric.ball c (r c)) ∧
        ∀ x ∉ A, ∃ c ∈ S, dist x c < 4 * r c := by
      obtain ⟨s, hs, hd, hc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
        Aᶜ (fun x : Rn n => x) r (1 / 100) (fun x _ => hr1 x) 4 (by norm_num)
      refine ⟨s, hs, hd, fun x hx => ?_⟩
      obtain ⟨c, hcs, hxc⟩ := hc x hx
      exact ⟨c, hcs, hxc (Metric.mem_ball_self (hrpos x hx))⟩
    have hsep : ∀ c ∈ S, ∀ d ∈ S, c ≠ d → r c ≤ dist c d := by
      intro c hc d hd hcd
      by_contra h
      have hdc : d ∈ Metric.ball c (r c) := by
        simpa only [Metric.mem_ball, dist_comm] using lt_of_not_ge h
      exact Set.disjoint_left.mp (hSdisj hc hd hcd) hdc
        (Metric.mem_ball_self (hrpos d (hSA hd)))
    have hcomp : ∀ x c, dist x c ≤ r x + 10 * r c →
        r x / 2 ≤ r c ∧ r c ≤ 2 * r x ∧ dist x c ≤ 21 * r x := by
      intro x c hxc
      have h₁ := hrlip x c
      have h₂ := hrlip c x
      rw [dist_comm c x] at h₂
      have := hr0 x
      have := hr0 c
      exact ⟨by linarith, by linarith, by linarith⟩
    -- Bounded overlap: rescaled near centres are `1/2`-separated in `closedBall 0 21`.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ x ∉ A, {c | c ∈ S ∧ dist x c ≤ r x + 10 * r c}.Finite ∧
        {c | c ∈ S ∧ dist x c ≤ r x + 10 * r c}.ncard ≤ N := by
      obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
        (isCompact_closedBall (0 : Rn n) 21).totallyBounded (1 / 4) (by norm_num)
      refine ⟨t.ncard, fun x hx => ?_⟩
      set s := {c | c ∈ S ∧ dist x c ≤ r x + 10 * r c} with hs_def
      have hrx := hrpos x hx
      have hrx' : 0 ≤ (r x)⁻¹ := inv_nonneg.mpr hrx.le
      have hmem : ∀ c : s, ∃ y : t, dist ((r x)⁻¹ • ((c : Rn n) - x)) y < 1 / 4 := by
        intro c
        have hd := (hcomp x c c.2.2).2.2
        rw [dist_comm, dist_eq_norm] at hd
        have hφc : (r x)⁻¹ • ((c : Rn n) - x) ∈ Metric.closedBall (0 : Rn n) 21 := by
          rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hrx']
          calc (r x)⁻¹ * ‖(c : Rn n) - x‖ ≤ (r x)⁻¹ * (21 * r x) :=
                mul_le_mul_of_nonneg_left hd hrx'
            _ = 21 := by field_simp
        have hcov := hcover hφc
        simp only [mem_iUnion, Metric.mem_ball, exists_prop] at hcov
        obtain ⟨y, hyt, hy⟩ := hcov
        exact ⟨⟨y, hyt⟩, hy⟩
      choose y hy using hmem
      have hinj : Function.Injective y := by
        intro c d hcd
        by_contra hne'
        have hne'' : (c : Rn n) ≠ d := fun h => hne' (Subtype.ext h)
        have hdist := hsep c c.2.1 d d.2.1 hne''
        have hrad := (hcomp x c c.2.2).1
        have h1 : 1 / 2 ≤ dist ((r x)⁻¹ • ((c : Rn n) - x)) ((r x)⁻¹ • ((d : Rn n) - x)) := by
          rw [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
            Real.norm_of_nonneg hrx']
          rw [dist_eq_norm] at hdist
          calc (1 : ℝ) / 2 = (r x)⁻¹ * (r x / 2) := by field_simp
            _ ≤ (r x)⁻¹ * ‖(c : Rn n) - d‖ := mul_le_mul_of_nonneg_left (hrad.trans hdist) hrx'
        have h2 := hy c
        have h3 := hy d
        rw [hcd] at h2
        have := dist_triangle ((r x)⁻¹ • ((c : Rn n) - x)) (y d) ((r x)⁻¹ • ((d : Rn n) - x))
        rw [dist_comm (y d : Rn n) ((r x)⁻¹ • ((d : Rn n) - x))] at this
        linarith
      have : Finite t := ht.to_subtype
      have : Finite s := Finite.of_injective y hinj
      exact ⟨Set.toFinite s, Nat.card_le_card_of_injective y hinj⟩
    -- The finite set of centres near `x ∉ A`.
    have hnear : ∀ x, ∃ F : Finset S, x ∉ A → F.card ≤ N ∧
        ∀ c : S, c ∈ F ↔ dist x c ≤ r x + 10 * r c := by
      intro x
      by_cases hx : x ∈ A
      · exact ⟨∅, fun h => absurd hx h⟩
      obtain ⟨hfin, hcard⟩ := hN x hx
      have hfin' : {c : S | dist x c ≤ r x + 10 * r c}.Finite :=
        (hfin.preimage Subtype.val_injective.injOn).subset fun c hc => ⟨c.2, hc⟩
      refine ⟨hfin'.toFinset, fun _ => ⟨?_, fun c => by simp⟩⟩
      rw [← Set.ncard_eq_toFinset_card _ hfin']
      refine le_trans (le_of_eq ?_) hcard
      change {c : S | (c : Rn n) ∈ {y | dist x y ≤ r x + 10 * r y}}.ncard = _
      rw [Set.ncard_subtype]
      congr 1
      ext c
      exact and_comm
    choose nF hnF using hnear
    -- Rescaled copies of one fixed bump, `= 1` on `B(c, 4 r c)` and `= 0` off `B(c, 8 r c)`.
    obtain ⟨φ₀, hφin, hφout⟩ : ∃ φ₀ : ContDiffBump (0 : Rn n), φ₀.rIn = 4 ∧ φ₀.rOut = 8 :=
      ⟨⟨4, 8, by norm_num, by norm_num⟩, rfl, rfl⟩
    obtain ⟨bump, hbump⟩ : ∃ bump : Rn n → Rn n → ℝ,
        ∀ c, bump c = fun y => φ₀ ((r c)⁻¹ • (y - c)) := ⟨_, fun _ => rfl⟩
    have hb_cd : ∀ c, ContDiff ℝ 1 (bump c) := fun c => by
      rw [hbump]
      exact (φ₀.contDiff (n := 1)).comp ((contDiff_id.sub contDiff_const).const_smul _)
    have hb_nn : ∀ c y, 0 ≤ bump c y := fun c y => by rw [hbump]; exact φ₀.nonneg
    have hb_le : ∀ c y, bump c y ≤ 1 := fun c y => by rw [hbump]; exact φ₀.le_one
    have hb_one : ∀ c y, 0 < r c → dist y c ≤ 4 * r c → bump c y = 1 := by
      intro c y hc hy
      rw [hbump]
      apply φ₀.one_of_mem_closedBall
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hc.le), hφin]
      rw [dist_eq_norm] at hy
      calc (r c)⁻¹ * ‖y - c‖ ≤ (r c)⁻¹ * (4 * r c) :=
            mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hc.le)
        _ = 4 := by field_simp
    have hb_zero : ∀ c y, 0 < r c → 8 * r c ≤ dist y c → bump c y = 0 := by
      intro c y hc hy
      rw [hbump]
      apply Function.notMem_support.mp
      rw [φ₀.support_eq, Metric.mem_ball, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hc.le), hφout, not_lt]
      rw [dist_eq_norm] at hy
      calc (8 : ℝ) = (r c)⁻¹ * (8 * r c) := by field_simp
        _ ≤ (r c)⁻¹ * ‖y - c‖ := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hc.le)
    obtain ⟨Bd, hBd, hb_der⟩ : ∃ Bd : ℝ, 0 < Bd ∧
        ∀ c y, 0 < r c → ‖fderiv ℝ (bump c) y‖ ≤ Bd / r c := by
      obtain ⟨Lb, hLb⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ₀.hasCompactSupport
        (φ₀.contDiff (n := 1)) (by simp)
      refine ⟨(Lb : ℝ) + 1, by positivity, fun c y hc => ?_⟩
      let ρ : ℝ≥0 := ⟨r c, hc.le⟩
      have hf' : LipschitzWith ρ⁻¹ (fun z : Rn n => (r c)⁻¹ • (z - c)) := by
        apply LipschitzWith.of_dist_le_mul
        intro y z
        have hid : (y - c) - (z - c) = y - z := by abel
        simp only [dist_eq_norm, ← smul_sub, hid, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr hc.le), NNReal.coe_inv]
        exact le_rfl
      have hg : LipschitzWith (Lb * ρ⁻¹) (bump c) := by rw [hbump]; exact hLb.comp hf'
      have hb := norm_fderiv_le_of_lipschitz ℝ hg (x₀ := y)
      simp only [NNReal.coe_mul, NNReal.coe_inv] at hb
      change ‖fderiv ℝ (bump c) y‖ ≤ (Lb : ℝ) * (r c)⁻¹ at hb
      refine hb.trans ?_
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hc.le)
    -- Bumps of far centres vanish on `B(x, r x)`.
    have hbz : ∀ x ∉ A, ∀ y, dist y x < r x → ∀ c : S, c ∉ nF x → bump c y = 0 := by
      intro x hx y hy c hc
      apply hb_zero c y (hrpos c (hSA c.2))
      have hnot : ¬ dist x c ≤ r x + 10 * r c := fun h => hc (((hnF x hx).2 c).2 h)
      have ht := dist_triangle x y c
      rw [dist_comm x y] at ht
      have := hr0 c
      linarith
    -- The bump sum `σ ≥ 1` on `Aᶜ` and the normalized weights `w c = bump c / σ`.
    obtain ⟨σ, hσ⟩ : ∃ σ : Rn n → ℝ, ∀ y, σ y = ∑ᶠ c : S, bump c y := ⟨_, fun _ => rfl⟩
    have hσ_eq : ∀ x ∉ A, ∀ y, dist y x < r x → σ y = ∑ c ∈ nF x, bump c y := by
      intro x hx y hy
      rw [hσ]
      apply finsum_eq_sum_of_support_subset
      intro c hc
      by_contra h
      exact hc (hbz x hx y hy c h)
    have hσ_cd : ∀ x ∉ A, ContDiffAt ℝ 1 σ x := by
      intro x hx
      have hs : ContDiff ℝ 1 (fun y => ∑ c ∈ nF x, bump c y) := ContDiff.sum fun c _ => hb_cd c
      apply hs.contDiffAt.congr_of_eventuallyEq
      filter_upwards [Metric.ball_mem_nhds x (hrpos x hx)] with y hy
      exact hσ_eq x hx y hy
    have hσ_ge : ∀ x ∉ A, 1 ≤ σ x := by
      intro x hx
      rw [hσ_eq x hx x (by simpa using hrpos x hx)]
      obtain ⟨c, hc, hxc⟩ := hScov x hx
      have hi : (⟨c, hc⟩ : S) ∈ nF x := by
        refine ((hnF x hx).2 _).2 ?_
        show dist x c ≤ r x + 10 * r c
        have := hr0 c
        have := hr0 x
        linarith
      calc (1 : ℝ) = bump c x := (hb_one c x (hrpos c (hSA hc)) hxc.le).symm
        _ ≤ ∑ c ∈ nF x, bump c x :=
          Finset.single_le_sum (f := fun c : S => bump c x) (fun c _ => hb_nn c x) hi
    obtain ⟨w, hw⟩ : ∃ w : S → Rn n → ℝ, ∀ c, w c = fun y => bump c y / σ y :=
      ⟨_, fun _ => rfl⟩
    have hw_cd : ∀ (c : S), ∀ x ∉ A, ContDiffAt ℝ 1 (w c) x := by
      intro c x hx
      rw [hw]
      exact (hb_cd c).contDiffAt.div (hσ_cd x hx) (by linarith [hσ_ge x hx])
    have hw_nn : ∀ (c : S), ∀ x ∉ A, 0 ≤ w c x := by
      intro c x hx
      rw [hw]
      exact div_nonneg (hb_nn c x) (by linarith [hσ_ge x hx])
    have hw_zero : ∀ x ∉ A, ∀ y, dist y x < r x → ∀ c : S, c ∉ nF x → w c y = 0 := by
      intro x hx y hy c hc
      rw [hw]
      simp only [hbz x hx y hy c hc, zero_div]
    have hw_sum : ∀ x ∉ A, ∀ y, dist y x < r x → ∑ c ∈ nF x, w c y = 1 := by
      intro x hx y hy
      simp only [hw]
      rw [← Finset.sum_div, ← hσ_eq x hx y hy]
      exact div_self (by linarith [hσ_ge y (hnA x y hy)])
    have hw_dsum : ∀ x ∉ A, ∑ c ∈ nF x, fderiv ℝ (w c) x = 0 := by
      intro x hx
      have heq : (fun y => ∑ c ∈ nF x, w c y) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
        filter_upwards [Metric.ball_mem_nhds x (hrpos x hx)] with y hy
        exact hw_sum x hx y hy
      have hh := heq.fderiv_eq (𝕜 := ℝ)
      rw [fderiv_fun_const] at hh
      rw [fderiv_fun_sum (fun c _ => (hw_cd c x hx).differentiableAt (by simp))] at hh
      exact hh
    obtain ⟨M, hM, hw_dbound⟩ : ∃ M : ℝ, 0 < M ∧
        ∀ x ∉ A, ∑ c ∈ nF x, ‖fderiv ℝ (w c) x‖ ≤ M / r x := by
      refine ⟨2 * Bd * ((N : ℝ) + 1) ^ 2, by positivity, fun x hx => ?_⟩
      have hrx := hrpos x hx
      obtain ⟨T, hT_def⟩ : ∃ T : ℝ, T = 2 * Bd / r x := ⟨_, rfl⟩
      have hT : 0 ≤ T := by rw [hT_def]; positivity
      have hb' : ∀ c ∈ nF x, ‖fderiv ℝ (bump c) x‖ ≤ T := by
        intro c hc
        have hcr := hrpos c (hSA c.2)
        have hlow := (hcomp x c (((hnF x hx).2 c).1 hc)).1
        refine (hb_der c x hcr).trans ?_
        calc Bd / r c ≤ Bd / (r x / 2) := div_le_div_of_nonneg_left hBd.le (half_pos hrx) hlow
          _ = T := by rw [hT_def]; ring
      have hcard : ((nF x).card : ℝ) ≤ N := by exact_mod_cast (hnF x hx).1
      have hσd : fderiv ℝ σ x = ∑ c ∈ nF x, fderiv ℝ (bump c) x := by
        have heq : σ =ᶠ[𝓝 x] (fun y => ∑ c ∈ nF x, bump c y) := by
          filter_upwards [Metric.ball_mem_nhds x hrx] with y hy
          exact hσ_eq x hx y hy
        rw [heq.fderiv_eq]
        exact fderiv_fun_sum (fun c _ => (hb_cd c).differentiable (by simp) x)
      have hsum : ‖fderiv ℝ σ x‖ ≤ (N : ℝ) * T := by
        rw [hσd]
        calc ‖∑ c ∈ nF x, fderiv ℝ (bump c) x‖ ≤ ∑ c ∈ nF x, ‖fderiv ℝ (bump c) x‖ :=
              norm_sum_le _ _
          _ ≤ ∑ _c ∈ nF x, T := Finset.sum_le_sum hb'
          _ = ((nF x).card : ℝ) * T := by simp
          _ ≤ (N : ℝ) * T := mul_le_mul_of_nonneg_right hcard hT
      have hwd : ∀ c : S, ‖fderiv ℝ (w c) x‖ ≤ ‖fderiv ℝ (bump c) x‖ + ‖fderiv ℝ σ x‖ := by
        intro c
        have hS1 : 1 ≤ σ x := hσ_ge x hx
        have hSpos : 0 < σ x := lt_of_lt_of_le one_pos hS1
        have hSi : (σ x)⁻¹ ≤ 1 := by
          simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hS1
        have hSi2 : (σ x ^ 2)⁻¹ ≤ 1 := by
          simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
            (show 1 ≤ σ x ^ 2 by nlinarith)
        have hb := ((hb_cd c).differentiable (by simp) x).hasFDerivAt
        have hd := ((hσ_cd x hx).differentiableAt (by simp)).hasFDerivAt
        have hi := (hasDerivAt_inv hSpos.ne').comp_hasFDerivAt x hd
        have hprod := hb.fun_mul hi
        have hder : fderiv ℝ (w c) x =
            bump c x • (-(σ x ^ 2)⁻¹ • fderiv ℝ σ x) + (σ x)⁻¹ • fderiv ℝ (bump c) x := by
          rw [hw]
          simpa only [div_eq_mul_inv, Function.comp_def] using hprod.fderiv
        rw [hder]
        have hb0 := hb_nn c x
        have hb1 := hb_le c x
        calc ‖bump c x • (-(σ x ^ 2)⁻¹ • fderiv ℝ σ x) + (σ x)⁻¹ • fderiv ℝ (bump c) x‖ ≤
              ‖bump c x • (-(σ x ^ 2)⁻¹ • fderiv ℝ σ x)‖ +
                ‖(σ x)⁻¹ • fderiv ℝ (bump c) x‖ := norm_add_le _ _
          _ = bump c x * ((σ x ^ 2)⁻¹ * ‖fderiv ℝ σ x‖) +
                (σ x)⁻¹ * ‖fderiv ℝ (bump c) x‖ := by
            rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hb0, norm_neg,
              Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg (σ x))),
              Real.norm_of_nonneg (inv_nonneg.mpr hSpos.le)]
          _ ≤ ‖fderiv ℝ (bump c) x‖ + ‖fderiv ℝ σ x‖ := by
            have h₁ := mul_le_mul_of_nonneg_right hSi (norm_nonneg (fderiv ℝ (bump c) x))
            have h₂ := mul_le_mul_of_nonneg_right hSi2 (norm_nonneg (fderiv ℝ σ x))
            have h₃ := mul_le_mul_of_nonneg_right hb1
              (mul_nonneg (inv_nonneg.mpr (sq_nonneg (σ x))) (norm_nonneg (fderiv ℝ σ x)))
            linarith
      calc ∑ c ∈ nF x, ‖fderiv ℝ (w c) x‖ ≤ ∑ _c ∈ nF x, (T + (N : ℝ) * T) :=
            Finset.sum_le_sum fun c hc => (hwd c).trans (add_le_add (hb' c hc) hsum)
        _ = ((nF x).card : ℝ) * (T + (N : ℝ) * T) := by simp [mul_add]
        _ ≤ (N : ℝ) * (T + (N : ℝ) * T) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ ≤ ((N : ℝ) + 1) ^ 2 * T := by nlinarith
        _ = 2 * Bd * ((N : ℝ) + 1) ^ 2 / r x := by rw [hT_def]; ring
    -- Nearest points `p x ∈ A` and the first-order jets `P a y = f a + L a (y - a)`.
    obtain ⟨p, hpA, hpd⟩ : ∃ p : Rn n → Rn n, (∀ x, p x ∈ A) ∧
        ∀ x, dist x (p x) = Metric.infDist x A := by
      choose p hp using fun x => hA.exists_infDist_eq_dist hne x
      exact ⟨p, fun x => (hp x).1, fun x => ((hp x).2).symm⟩
    have hp_near : ∀ x ∉ A, ∀ c ∈ nF x, dist x (p c) ≤ 2 * Metric.infDist x A := by
      intro x hx c hc
      have hd := (hcomp x c (((hnF x hx).2 c).1 hc)).2.2
      have hi := Metric.infDist_le_infDist_add_dist (s := A) (x := (c : Rn n)) (y := x)
      have ht := dist_triangle x (c : Rn n) (p c)
      rw [dist_comm (c : Rn n) x] at hi
      rw [hpd] at ht
      linarith [hrd x, Metric.infDist_nonneg (x := x) (s := A)]
    have hp_pt : ∀ x ∉ A, ∀ a ∈ A, ∀ c ∈ nF x, dist (p c) a ≤ 3 * dist x a := by
      intro x hx a ha c hc
      have hd := hp_near x hx c hc
      have hi := Metric.infDist_le_dist_of_mem (x := x) ha
      have ht := dist_triangle (p c) x a
      rw [dist_comm (p c) x] at ht
      linarith
    obtain ⟨P, hP⟩ : ∃ P : Rn n → Rn n → ℝ, ∀ a, P a = fun y => f a + L a (y - a) :=
      ⟨_, fun _ => rfl⟩
    have hP_cd : ∀ a, ContDiff ℝ 1 (P a) := fun a => by
      rw [hP]
      exact contDiff_const.add ((L a).contDiff.comp (contDiff_id.sub contDiff_const))
    have hP_d : ∀ a y, HasFDerivAt (P a) (L a) y := fun a y => by
      have h := ((L a).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const a)).const_add (f a)
      rw [ContinuousLinearMap.comp_id] at h
      rw [hP]
      exact h
    have hP_sub : ∀ a b y, ‖P b y - P a y‖ ≤
        ‖f b - f a - L a (b - a)‖ + ‖L b - L a‖ * ‖y - b‖ := by
      intro a b y
      have hid : P b y - P a y = (f b - f a - L a (b - a)) + (L b - L a) (y - b) := by
        have hy : y - a = (y - b) + (b - a) := by abel
        simp only [hP, hy, map_add, sub_apply]
        ring
      rw [hid]
      exact (norm_add_le _ _).trans (add_le_add le_rfl ((L b - L a).le_opNorm (y - b)))
    -- The extension: `f` on `A`, the weighted average of the jets `P (p c)` off `A`.
    classical
    obtain ⟨g, hg⟩ : ∃ g : Rn n → ℝ,
        ∀ y, g y = if y ∈ A then f y else ∑ᶠ c : S, w c y * P (p c) y := ⟨_, fun _ => rfl⟩
    have hgA : ∀ a ∈ A, g a = f a := fun a ha => by rw [hg, ite_eq_left ha]
    have hg_eq : ∀ x ∉ A, ∀ y, dist y x < r x → g y = ∑ c ∈ nF x, w c y * P (p c) y := by
      intro x hx y hy
      rw [hg, ite_eq_right (hnA x y hy)]
      apply finsum_eq_sum_of_support_subset
      intro c hc
      by_contra hc'
      apply hc
      simp only [hw_zero x hx y hy c hc', zero_mul]
    have hg_ev : ∀ x ∉ A, g =ᶠ[𝓝 x] (fun y => ∑ c ∈ nF x, w c y * P (p c) y) := by
      intro x hx
      filter_upwards [Metric.ball_mem_nhds x (hrpos x hx)] with y hy
      exact hg_eq x hx y hy
    have hg_cd : ∀ x ∉ A, ContDiffAt ℝ 1 g x := by
      intro x hx
      have hs : ContDiffAt ℝ 1 (fun y => ∑ c ∈ nF x, w c y * P (p c) y) x :=
        ContDiffAt.sum fun c _ => (hw_cd c x hx).mul (hP_cd _).contDiffAt
      exact hs.congr_of_eventuallyEq (hg_ev x hx)
    have hg_fd : ∀ x ∉ A, fderiv ℝ g x =
        ∑ c ∈ nF x, (w c x • L (p c) + P (p c) x • fderiv ℝ (w c) x) := by
      intro x hx
      rw [(hg_ev x hx).fderiv_eq]
      apply HasFDerivAt.fderiv
      apply HasFDerivAt.fun_sum
      intro c _
      exact ((hw_cd c x hx).differentiableAt (by simp)).hasFDerivAt.fun_mul (hP_d _ x)
    -- `Dg(a) = L(a)` on `A` (Simon 1.6, value estimate).
    have hg_dA : ∀ a ∈ A, HasFDerivAt g (L a) a := by
      intro a ha
      apply HasFDerivAt.of_isLittleO
      apply Asymptotics.IsLittleO.of_bound
      intro e he
      have he5 : 0 < e / 5 := by positivity
      obtain ⟨δ, hδ, -, hD, hrm⟩ := hloc a ha (e / 5) he5
      filter_upwards [Metric.ball_mem_nhds a (show 0 < δ / 4 by positivity)] with x hx
      have hxa : dist x a < δ / 4 := hx
      rw [hgA a ha]
      by_cases hxA : x ∈ A
      · rw [hgA x hxA]
        have h := hrm a ha (by simpa using hδ) x hxA (by linarith)
        exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
      · have hx' : dist x x < r x := by simpa using hrpos x hxA
        have hid : g x - f a - L a (x - a) = ∑ c ∈ nF x, w c x * (P (p c) x - P a x) := by
          rw [hg_eq x hxA x hx']
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw_sum x hxA x hx', one_mul, hP]
          ring
        rw [hid]
        have hkey : ∀ c ∈ nF x, ‖P (p c) x - P a x‖ ≤ e * ‖x - a‖ := by
          intro c hc
          have hba : dist (p c) a ≤ 3 * dist x a := hp_pt x hxA a ha c hc
          have hxb : dist x (p c) ≤ 2 * dist x a := (hp_near x hxA c hc).trans
            (mul_le_mul_of_nonneg_left (Metric.infDist_le_dist_of_mem ha) (by norm_num))
          have hbaδ : dist (p c) a < δ := by linarith
          have hDb := hD (p c) (hpA c) hbaδ
          have hr' := hrm a ha (by simpa using hδ) (p c) (hpA c) hbaδ
          have hba' : ‖p c - a‖ ≤ 3 * ‖x - a‖ := by simpa only [dist_eq_norm] using hba
          have hxb' : ‖x - p c‖ ≤ 2 * ‖x - a‖ := by simpa only [dist_eq_norm] using hxb
          calc ‖P (p c) x - P a x‖ ≤
                ‖f (p c) - f a - L a (p c - a)‖ + ‖L (p c) - L a‖ * ‖x - p c‖ := hP_sub _ _ _
            _ ≤ (e / 5) * ‖p c - a‖ + (e / 5) * ‖x - p c‖ :=
              add_le_add hr' (mul_le_mul_of_nonneg_right hDb (norm_nonneg _))
            _ ≤ (e / 5) * (3 * ‖x - a‖) + (e / 5) * (2 * ‖x - a‖) :=
              add_le_add (mul_le_mul_of_nonneg_left hba' he5.le)
                (mul_le_mul_of_nonneg_left hxb' he5.le)
            _ = e * ‖x - a‖ := by ring
        calc ‖∑ c ∈ nF x, w c x * (P (p c) x - P a x)‖ ≤
              ∑ c ∈ nF x, ‖w c x * (P (p c) x - P a x)‖ := norm_sum_le _ _
          _ = ∑ c ∈ nF x, w c x * ‖P (p c) x - P a x‖ := Finset.sum_congr rfl fun c _ => by
              rw [norm_mul, Real.norm_of_nonneg (hw_nn c x hxA)]
          _ ≤ ∑ c ∈ nF x, w c x * (e * ‖x - a‖) := Finset.sum_le_sum fun c hc =>
              mul_le_mul_of_nonneg_left (hkey c hc) (hw_nn c x hxA)
          _ = e * ‖x - a‖ := by rw [← Finset.sum_mul, hw_sum x hxA x hx', one_mul]
    have hg_fdA : ∀ a ∈ A, fderiv ℝ g a = L a := fun a ha => (hg_dA a ha).fderiv
    -- `Dg` is continuous at points of `A` (Simon 1.6, derivative estimate).
    have hg_cA : ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
      intro a ha
      apply Metric.continuousAt_iff.mpr
      intro e he
      obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = e / (2 * (1 + 700 * M)) := ⟨_, rfl⟩
      have hη : 0 < η := by rw [hη_def]; positivity
      have heq : η * (1 + 700 * M) = e / 2 := by rw [hη_def]; field_simp
      have hηe : η ≤ e / 2 := by nlinarith
      obtain ⟨δ, hδ, hδ1, hD, hrm⟩ := hloc a ha η hη
      refine ⟨δ / 4, by positivity, fun x hxa => ?_⟩
      rw [hg_fdA a ha, dist_eq_norm]
      apply lt_of_le_of_lt (b := e / 2) ?_ (by linarith)
      by_cases hxA : x ∈ A
      · rw [hg_fdA x hxA]
        exact (hD x hxA (by linarith)).trans hηe
      have hrx := hrpos x hxA
      have hx' : dist x x < r x := by simpa using hrx
      have hbA : p x ∈ A := hpA x
      have hxb : dist x (p x) = Metric.infDist x A := hpd x
      have hxa' : Metric.infDist x A ≤ dist x a := Metric.infDist_le_dist_of_mem ha
      have hba : dist (p x) a ≤ 2 * dist x a := by
        have ht := dist_triangle (p x) x a
        rw [dist_comm (p x) x] at ht
        linarith
      have hbaδ : dist (p x) a < δ := by linarith
      have hDb := hD (p x) hbA hbaδ
      have hdx : Metric.infDist x A ≤ 1 := by linarith
      have hscale : Metric.infDist x A = 100 * r x := by
        rw [hr, min_eq_right hdx]
        ring
      have hD' : ∀ c ∈ nF x, ‖L (p c) - L a‖ ≤ η := fun c hc =>
        hD _ (hpA c) (by linarith [hp_pt x hxA a ha c hc])
      have hPb : ∀ c ∈ nF x, ‖P (p c) x - P (p x) x‖ ≤ 700 * η * r x := by
        intro c hc
        have hda : dist (p c) a ≤ 3 * dist x a := hp_pt x hxA a ha c hc
        have hdaδ : dist (p c) a < δ := by linarith
        have hxd : dist x (p c) ≤ 2 * Metric.infDist x A := hp_near x hxA c hc
        have hdb : dist (p c) (p x) ≤ 3 * Metric.infDist x A := by
          have ht := dist_triangle (p c) x (p x)
          rw [dist_comm (p c) x, hxb] at ht
          linarith
        have hDd : ‖L (p c) - L (p x)‖ ≤ 2 * η := by
          calc ‖L (p c) - L (p x)‖ = ‖(L (p c) - L a) - (L (p x) - L a)‖ := by
                congr 1; abel
            _ ≤ ‖L (p c) - L a‖ + ‖L (p x) - L a‖ := norm_sub_le _ _
            _ ≤ η + η := add_le_add (hD' c hc) hDb
            _ = 2 * η := by ring
        have hre := hrm (p x) hbA hbaδ (p c) (hpA c) hdaδ
        have hdb' : ‖p c - p x‖ ≤ 3 * Metric.infDist x A := by
          simpa only [dist_eq_norm] using hdb
        have hxd' : ‖x - p c‖ ≤ 2 * Metric.infDist x A := by
          simpa only [dist_eq_norm] using hxd
        calc ‖P (p c) x - P (p x) x‖ ≤
              ‖f (p c) - f (p x) - L (p x) (p c - p x)‖ + ‖L (p c) - L (p x)‖ * ‖x - p c‖ :=
            hP_sub _ _ _
          _ ≤ η * ‖p c - p x‖ + (2 * η) * ‖x - p c‖ :=
            add_le_add hre (mul_le_mul_of_nonneg_right hDd (norm_nonneg _))
          _ ≤ η * (3 * Metric.infDist x A) + (2 * η) * (2 * Metric.infDist x A) :=
            add_le_add (mul_le_mul_of_nonneg_left hdb' hη.le)
              (mul_le_mul_of_nonneg_left hxd' (by positivity))
          _ = 700 * η * r x := by rw [hscale]; ring
      have hfd : fderiv ℝ g x - L a = (∑ c ∈ nF x, w c x • (L (p c) - L a)) +
          ∑ c ∈ nF x, (P (p c) x - P (p x) x) • fderiv ℝ (w c) x := by
        rw [hg_fd x hxA]
        simp_rw [smul_sub, sub_smul]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_smul, ← Finset.smul_sum, hw_sum x hxA x hx', hw_dsum x hxA,
          one_smul, smul_zero, sub_zero]
        abel
      rw [hfd]
      have h1 : ‖∑ c ∈ nF x, w c x • (L (p c) - L a)‖ ≤ η := by
        calc ‖∑ c ∈ nF x, w c x • (L (p c) - L a)‖ ≤ ∑ c ∈ nF x, ‖w c x • (L (p c) - L a)‖ :=
              norm_sum_le _ _
          _ = ∑ c ∈ nF x, w c x * ‖L (p c) - L a‖ := Finset.sum_congr rfl fun c _ => by
              rw [norm_smul, Real.norm_of_nonneg (hw_nn c x hxA)]
          _ ≤ ∑ c ∈ nF x, w c x * η := Finset.sum_le_sum fun c hc =>
              mul_le_mul_of_nonneg_left (hD' c hc) (hw_nn c x hxA)
          _ = η := by rw [← Finset.sum_mul, hw_sum x hxA x hx', one_mul]
      have h2 : ‖∑ c ∈ nF x, (P (p c) x - P (p x) x) • fderiv ℝ (w c) x‖ ≤
          (700 * η * r x) * ∑ c ∈ nF x, ‖fderiv ℝ (w c) x‖ := by
        calc ‖∑ c ∈ nF x, (P (p c) x - P (p x) x) • fderiv ℝ (w c) x‖ ≤
              ∑ c ∈ nF x, ‖(P (p c) x - P (p x) x) • fderiv ℝ (w c) x‖ := norm_sum_le _ _
          _ ≤ ∑ c ∈ nF x, (700 * η * r x) * ‖fderiv ℝ (w c) x‖ := Finset.sum_le_sum fun c hc => by
              rw [norm_smul]
              exact mul_le_mul_of_nonneg_right (hPb c hc) (norm_nonneg _)
          _ = (700 * η * r x) * ∑ c ∈ nF x, ‖fderiv ℝ (w c) x‖ := (Finset.mul_sum ..).symm
      calc ‖(∑ c ∈ nF x, w c x • (L (p c) - L a)) +
            ∑ c ∈ nF x, (P (p c) x - P (p x) x) • fderiv ℝ (w c) x‖ ≤
            η + (700 * η * r x) * ∑ c ∈ nF x, ‖fderiv ℝ (w c) x‖ :=
          (norm_add_le _ _).trans (add_le_add h1 h2)
        _ ≤ η + (700 * η * r x) * (M / r x) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (hw_dbound x hxA) (by positivity))
        _ = η * (1 + 700 * M) := by field_simp
        _ = e / 2 := heq
    refine ⟨g, contDiff_one_iff_fderiv.mpr ⟨fun x => ?_, continuous_iff_continuousAt.mpr
      fun x => ?_⟩, hgA, hg_dA⟩
    · by_cases hx : x ∈ A
      · exact (hg_dA x hx).differentiableAt
      · exact (hg_cd x hx).differentiableAt (by simp)
    · by_cases hx : x ∈ A
      · exact hg_cA x hx
      · exact (hg_cd x hx).continuousAt_fderiv (by simp)
  -- Rademacher: `f` is differentiable off a null set `Bᶜ`; `B` and `Df` are Borel.
  let B : Set (Rn n) := {x | DifferentiableAt ℝ f x}
  have hB : MeasurableSet B := measurableSet_of_differentiableAt ℝ f
  have hBc : volume Bᶜ = 0 := ae_iff.mp (hf.ae_differentiableAt (μ := volume))
  have hDf : Measurable (fderiv ℝ f) := measurable_fderiv ℝ f
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- Lusin: a closed `C ⊆ B` with `Lⁿ(B \ C) < ε/2` on which `Df` is continuous.
  obtain ⟨C, hCB, hC, hBC, hDfC⟩ := Submission.lusin_closed_subset_continuousOn_volume n
    (Rn n →L[ℝ] ℝ) (fderiv ℝ f) B hDf hB (ε / 2) hε2
  -- A closed `A ⊆ C` with `Lⁿ(C \ A) < ε/2` carrying the uniform remainder estimate 1.6(‡).
  obtain ⟨A, hAC, hA, hCA, hrem⟩ := Submission.lipschitz_uniform_remainder_on_closed_subset n f
    K (fderiv ℝ f) C hf hDf hC.measurableSet
    (fun x hx ↦ DifferentiableAt.hasFDerivAt (hCB hx)) (ε / 2) hε2
  -- Whitney: `g ∈ C¹` with `g = f` and `Dg = Df` on `A`.
  obtain ⟨g, hg, hgA, hDgA⟩ := hW A (fderiv ℝ f) hA (hDfC.mono hAC) hrem
  refine ⟨g, hg, ?_⟩
  -- The exceptional set misses `A ⊆ C ⊆ B`.
  have hsub : {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x} ⊆ Bᶜ ∪ (B \ C) ∪ (C \ A) := by
    intro x hx
    by_cases hxA : x ∈ A
    · exfalso
      rcases hx with h | h
      · exact h (hgA x hxA).symm
      · exact h (hDgA x hxA).fderiv.symm
    by_cases hxB : x ∈ B
    · by_cases hxC : x ∈ C
      · exact Or.inr ⟨hxC, hxA⟩
      · exact Or.inl (Or.inr ⟨hxB, hxC⟩)
    · exact Or.inl (Or.inl hxB)
  calc volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x}
      ≤ volume (Bᶜ ∪ (B \ C) ∪ (C \ A)) := measure_mono hsub
    _ ≤ volume Bᶜ + volume (B \ C) + volume (C \ A) :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ = volume (B \ C) + volume (C \ A) := by rw [hBc, zero_add]
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hBC hCA
    _ = ε := ENNReal.add_halves ε

/-- **Simon Ch. 2, proof of Theorem 1.9, choice (1)** (`chapter-02.txt` lines 366–370), for
Mathlib's unnormalized Hausdorff measure: if `μH[d](s) < ∞`, then for every `r > 0` and `ε ≠ 0`
some countable cover `(tₙ)` of `s` by sets of diameter `≤ r` has `∑ₙ diam(tₙ)^d ≤ μH[d](s) + ε`
(empty `tₙ` cost `0`). By `hausdorffMeasure_apply` the infimum over such covers is at most
`μH[d](s) < μH[d](s) + ε`, so some cover lies strictly below that bound. -/
theorem Submission.hausdorffMeasure_exists_cover_tsum_le_add : ∀ {X : Type} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (d : ℝ) (s : Set X) (r ε : ℝ≥0∞), 0 < r → ε ≠ 0 →
    μH[d] s ≠ ∞ → ∃ t : ℕ → Set X, s ⊆ ⋃ n, t n ∧ (∀ n, Metric.ediam (t n) ≤ r) ∧
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d ≤ μH[d] s + ε := by
  intro X _ _ _ d s r ε hr hε hs
  -- The infimum over covers by sets of diameter `≤ r` is the `r`-term of the supremum.
  have hle : (⨅ (t : ℕ → Set X) (_ : s ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d) ≤ μH[d] s := by
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup₂_of_le r hr le_rfl
  have hlt := hle.trans_lt (ENNReal.lt_add_right hs hε)
  simp only [iInf_lt_iff] at hlt
  obtain ⟨t, hst, htr, hsum⟩ := hlt
  exact ⟨t, hst, htr, hsum.le⟩

/-- **Volume–diameter bound**, the step of Simon Ch. 2, proof of Theorem 1.9
(`chapter-02.txt` lines 401–406) where `Lᵐ(f(C_{ij})) ≤ ωₘ (diam f(C_{ij})/2)ᵐ` is taken from the
isodiametric inequality 2.10, with the cruder constant of a closed-ball inclusion:
`Lᵐ(closure S) ≤ ωₘ (diam S)ᵐ` for every `S ⊆ ℝᵐ`, where `ωₘ = Lᵐ(B₁(0))`. The cases `S = ∅`,
`m = 0` (`B₁(0) = ℝ⁰`, power `1`) and `diam S = ∞` (`ωₘ > 0`) are immediate. Otherwise
`closure S ⊆ B̄_{diam S}(s₀)` for any `s₀ ∈ S`, and `Lᵐ(B̄_D(s₀)) = Dᵐ ωₘ` by `addHaar_closedBall`. -/
theorem Submission.volume_closure_le_unitBall_mul_ediam_pow : ∀ (m : ℕ) (S : Set (Rn m)),
    volume (closure S) ≤ volume (Metric.ball (0 : Rn m) 1) * Metric.ediam S ^ m := by
  intro m S
  rcases S.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · simp
  by_cases hm : m = 0
  · -- `ℝ⁰` is a single point, so `B₁(0)` is the whole space and the power is `1`.
    subst hm
    have hball : Metric.ball (0 : Rn 0) 1 = univ := by
      ext x; simp [Subsingleton.elim x 0]
    rw [pow_zero, mul_one, hball]
    exact measure_mono (subset_univ _)
  have hω0 : volume (Metric.ball (0 : Rn m) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume (0 : Rn m) one_pos).ne'
  by_cases hD : Metric.ediam S = ∞
  · rw [hD, ENNReal.top_pow hm, ENNReal.mul_top hω0]
    exact le_top
  -- `S` is bounded and `closure S` has the same diameter, so it lies in `B̄_{diam S}(s₀)`.
  have hb : Bornology.IsBounded S := Metric.isBounded_iff_ediam_ne_top.2 hD
  have hsub : closure S ⊆ Metric.closedBall s₀ (Metric.diam S) := by
    intro x hx
    rw [Metric.mem_closedBall, ← Metric.diam_closure]
    exact Metric.dist_le_diam_of_mem hb.closure hx (subset_closure hs₀)
  calc volume (closure S) ≤ volume (Metric.closedBall s₀ (Metric.diam S)) := measure_mono hsub
    _ = ENNReal.ofReal (Metric.diam S ^ m) * volume (Metric.ball (0 : Rn m) 1) := by
        rw [Measure.addHaar_closedBall volume s₀ Metric.diam_nonneg, finrank_euclideanSpace_fin]
    _ = volume (Metric.ball (0 : Rn m) 1) * Metric.ediam S ^ m := by
        rw [mul_comm, ENNReal.ofReal_pow Metric.diam_nonneg, Metric.diam, ENNReal.ofReal_toReal hD]

/-- **Simon Ch. 2, Theorem 1.9 (pp. 45–46), Eilenberg's inequality when `H^{m+k}(A) < ∞`**
(`chapter-02.txt` lines 366–411), for Mathlib's unnormalized Hausdorff measures `μH[·]` and an
arbitrary `A ⊆ ℝᴺ`: an `L`-Lipschitz `f : ℝᴺ → ℝᵐ` has a Borel `g ≥ μH[k](A ∩ f⁻¹{y})` with
`∫ g dLᵐ ≤ ωₘ Lᵐ μH[m+k](A)`, `ωₘ = Lᵐ(B₁(0))`. As in (1)–(2), take covers `Cᵢⱼ` of `A` with
`diam Cᵢⱼ ≤ 1/i` and `∑ⱼ diam(Cᵢⱼ)^{m+k} ≤ μH[m+k](A) + 1/i`, and the Borel functions
`gᵢ = ∑ⱼ diam(Cᵢⱼ)ᵏ 1_{closure f(Cᵢⱼ)}`. The majorant is `g = liminf gᵢ`, so Fatou's lemma
replaces the upper integral of Remark 1.10, and `Lᵐ(closure S) ≤ ωₘ (diam S)ᵐ` replaces the
isodiametric inequality. -/
theorem Submission.eilenberg_hausdorff_upper_integral_of_ne_top :
    ∀ (N m k : ℕ) (A : Set (Rn N)) (f : Rn N → Rn m) (L : ℝ≥0), LipschitzWith L f →
      μH[((m + k : ℕ) : ℝ)] A ≠ ∞ → ∃ g : Rn m → ℝ≥0∞, Measurable g ∧
        (∀ y, μH[(k : ℝ)] (A ∩ f ⁻¹' {y}) ≤ g y) ∧
        ∫⁻ y, g y ≤ volume (Metric.ball (0 : Rn m) 1) * (L : ℝ≥0∞) ^ m *
          μH[((m + k : ℕ) : ℝ)] A := by
  intro N m k A f L hf hA
  set ω := volume (Metric.ball (0 : Rn m) 1)
  -- (1): covers `C i j` of `A` with `diam (C i j) ≤ 1/i` and cost `≤ μH[m+k](A) + 1/i`.
  choose C hCcov hCdiam hCsum using fun i : ℕ ↦
    Submission.hausdorffMeasure_exists_cover_tsum_le_add ((m + k : ℕ) : ℝ) A (i : ℝ≥0∞)⁻¹
      (i : ℝ≥0∞)⁻¹ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top i))
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top i)) hA
  set G : ℕ → Rn m → ℝ≥0∞ := fun i y ↦
    ∑' j, (closure (f '' C i j)).indicator (fun _ ↦ Metric.ediam (C i j) ^ (k : ℝ)) y with hG
  have hGj : ∀ i j, Measurable ((closure (f '' C i j)).indicator
      fun _ : Rn m ↦ Metric.ediam (C i j) ^ (k : ℝ)) := fun i j ↦
    measurable_const.indicator isClosed_closure.measurableSet
  have hGmeas : ∀ i, Measurable (G i) := fun i ↦ Measurable.tsum (hGj i)
  refine ⟨fun y ↦ liminf (fun i ↦ G i y) atTop, Measurable.liminf hGmeas, fun y ↦ ?_, ?_⟩
  · -- (2): the `C i j` with `y ∈ f '' C i j` cover `A ∩ f⁻¹{y}`, at a cost of at most `G i y`.
    have hcov : ∀ i, A ∩ f ⁻¹' {y} ⊆ ⋃ j : {j : ℕ // y ∈ f '' C i j}, C i j := fun i x hx ↦ by
      obtain ⟨j, hj⟩ := mem_iUnion.1 (hCcov i hx.1)
      exact mem_iUnion.2 ⟨⟨j, x, hj, hx.2⟩, hj⟩
    refine (Measure.hausdorffMeasure_le_liminf_tsum (ι := fun i : ℕ ↦ {j : ℕ // y ∈ f '' C i j})
      (k : ℝ) (A ∩ f ⁻¹' {y}) (l := atTop) (fun i : ℕ ↦ (i : ℝ≥0∞)⁻¹)
      ENNReal.tendsto_inv_nat_nhds_zero (fun i j ↦ C i j)
      (Eventually.of_forall fun i j ↦ hCdiam i j) (Eventually.of_forall hcov)).trans
      (liminf_le_liminf (Eventually.of_forall fun i ↦ ?_))
    calc ∑' j : {j : ℕ // y ∈ f '' C i j}, Metric.ediam (C i j.1) ^ (k : ℝ)
        = ∑' j, {j : ℕ | y ∈ f '' C i j}.indicator (fun j ↦ Metric.ediam (C i j) ^ (k : ℝ)) j :=
          tsum_subtype {j : ℕ | y ∈ f '' C i j} fun j ↦ Metric.ediam (C i j) ^ (k : ℝ)
      _ ≤ G i y := ENNReal.tsum_le_tsum fun j ↦ by
          by_cases hj : y ∈ f '' C i j
          · rw [Set.indicator_of_mem (show j ∈ {j : ℕ | y ∈ f '' C i j} from hj),
              Set.indicator_of_mem (subset_closure hj)]
          · rw [Set.indicator_of_notMem (show j ∉ {j : ℕ | y ∈ f '' C i j} from hj)]
            exact zero_le
  · -- `∫ G i ≤ ωₘ Lᵐ (μH[m+k](A) + 1/i)`, since `Lᵐ(closure f(C)) ≤ ωₘ (L diam C)ᵐ`.
    have hint : ∀ i : ℕ, ∫⁻ y, G i y ≤
        ω * (L : ℝ≥0∞) ^ m * (μH[((m + k : ℕ) : ℝ)] A + (i : ℝ≥0∞)⁻¹) := by
      intro i
      rw [hG]
      dsimp only
      rw [lintegral_tsum fun j ↦ (hGj i j).aemeasurable]
      calc ∑' j, ∫⁻ y, (closure (f '' C i j)).indicator
              (fun _ ↦ Metric.ediam (C i j) ^ (k : ℝ)) y
          = ∑' j, Metric.ediam (C i j) ^ (k : ℝ) * volume (closure (f '' C i j)) :=
            tsum_congr fun j ↦ lintegral_indicator_const isClosed_closure.measurableSet _
        _ ≤ ∑' j, ω * (L : ℝ≥0∞) ^ m *
              ⨆ _ : (C i j).Nonempty, Metric.ediam (C i j) ^ ((m + k : ℕ) : ℝ) :=
            ENNReal.tsum_le_tsum fun j ↦ by
              rcases (C i j).eq_empty_or_nonempty with h | h
              · simp [h]
              rw [iSup_pos h]
              calc Metric.ediam (C i j) ^ (k : ℝ) * volume (closure (f '' C i j))
                  ≤ Metric.ediam (C i j) ^ (k : ℝ) * (ω * Metric.ediam (f '' C i j) ^ m) := by
                    gcongr
                    exact Submission.volume_closure_le_unitBall_mul_ediam_pow m _
                _ ≤ Metric.ediam (C i j) ^ (k : ℝ) *
                      (ω * ((L : ℝ≥0∞) * Metric.ediam (C i j)) ^ m) := by
                    gcongr
                    exact hf.ediam_image_le _
                _ = ω * (L : ℝ≥0∞) ^ m * Metric.ediam (C i j) ^ ((m + k : ℕ) : ℝ) := by
                    rw [ENNReal.rpow_natCast, ENNReal.rpow_natCast, mul_pow, pow_add]
                    ring
        _ = ω * (L : ℝ≥0∞) ^ m *
              ∑' j, ⨆ _ : (C i j).Nonempty, Metric.ediam (C i j) ^ ((m + k : ℕ) : ℝ) :=
            ENNReal.tsum_mul_left
        _ ≤ ω * (L : ℝ≥0∞) ^ m * (μH[((m + k : ℕ) : ℝ)] A + (i : ℝ≥0∞)⁻¹) := by
            gcongr
            exact hCsum i
    -- Fatou's lemma, and `1/i → 0`.
    have hlim : Tendsto (fun i : ℕ ↦ ω * (L : ℝ≥0∞) ^ m *
        (μH[((m + k : ℕ) : ℝ)] A + (i : ℝ≥0∞)⁻¹)) atTop
        (𝓝 (ω * (L : ℝ≥0∞) ^ m * μH[((m + k : ℕ) : ℝ)] A)) := by
      have h : Tendsto (fun i : ℕ ↦ μH[((m + k : ℕ) : ℝ)] A + (i : ℝ≥0∞)⁻¹) atTop
          (𝓝 (μH[((m + k : ℕ) : ℝ)] A + 0)) :=
        tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero
      rw [add_zero] at h
      exact ENNReal.Tendsto.const_mul h
        (Or.inr (ENNReal.mul_ne_top measure_ball_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)))
    calc ∫⁻ y, liminf (fun i ↦ G i y) atTop ≤ liminf (fun i ↦ ∫⁻ y, G i y) atTop :=
          lintegral_liminf_le hGmeas
      _ ≤ liminf (fun i : ℕ ↦ ω * (L : ℝ≥0∞) ^ m *
            (μH[((m + k : ℕ) : ℝ)] A + (i : ℝ≥0∞)⁻¹)) atTop :=
          liminf_le_liminf (Eventually.of_forall hint)
      _ = ω * (L : ℝ≥0∞) ^ m * μH[((m + k : ℕ) : ℝ)] A := hlim.liminf_eq

/-- **Eilenberg's inequality, Simon Ch. 2, Theorem 1.9 and Remark 1.10 (pp. 45–46)**
(`chapter-02.txt` lines 335–411; `k = 0` is Theorem 1.8(ii)), in upper-integral form for an
arbitrary `A`: a Borel `g ≥ Hᵏ(A ∩ f⁻¹{y})` with `∫ g dLᵐ ≤ C Lᵐ H^{m+k}(A)`. Writing
`μHE[d] = c_d • μH[d]` and `ωₘ = Lᵐ(B₁(0))`, take `C = ωₘ c_k / c_{m+k}` (any constant will do,
so the isodiametric inequality is not needed). If `μH[m+k](A) < ∞`, then `g = c_k g₀` for the
majorant `g₀` of `Submission.eilenberg_hausdorff_upper_integral_of_ne_top`. Otherwise
`H^{m+k}(A) = ∞`, and `g ≡ ∞` works unless `C Lᵐ = 0`, i.e. `L = 0` and `m ≥ 1`; then `f` is
constant, equal to `y₀` say, and `g = ∞ · 1_{y₀}` has integral `0`. -/
theorem Submission.eilenberg_upper_integral_inequality : ∀ (N m k : ℕ), ∃ C : ℝ≥0,
    ∀ (A : Set (Rn N)) (f : Rn N → Rn m) (L : ℝ≥0), LipschitzWith L f →
      ∃ g : Rn m → ℝ≥0∞, Measurable g ∧ (∀ y, μHE[k] (A ∩ f ⁻¹' {y}) ≤ g y) ∧
        ∫⁻ y, g y ≤ ((C * L ^ m : ℝ≥0) : ℝ≥0∞) * μHE[m + k] A := by
  intro N m k
  -- `μHE[d] = c d • μH[d]` with `c d ≠ 0`, and `ω = Lᵐ(B₁(0)) ∈ (0, ∞)`.
  obtain ⟨c, hc_eq⟩ : ∃ c : ℕ → ℝ≥0, ∀ d, c d =
      Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d] :=
    ⟨_, fun _ ↦ rfl⟩
  have hc : ∀ d, c d ≠ 0 := fun d ↦ by
    rw [hc_eq]; exact Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d
  have hHE : ∀ (d : ℕ) (S : Set (Rn N)), μHE[d] S = c d * μH[(d : ℝ)] S := fun d S ↦ by
    rw [hc_eq, Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul]
  set ω := volume (Metric.ball (0 : Rn m) 1)
  have hω0 : ω ≠ 0 := (Metric.measure_ball_pos volume (0 : Rn m) one_pos).ne'
  have hω : ω ≠ ∞ := measure_ball_ne_top
  set C : ℝ≥0 := ω.toNNReal * c k / c (m + k) with hC
  have hC0 : C ≠ 0 :=
    div_ne_zero (mul_ne_zero (ENNReal.toNNReal_pos hω0 hω).ne' (hc k)) (hc (m + k))
  have hCc : (C : ℝ≥0∞) * c (m + k) = ω * c k := by
    rw [← ENNReal.coe_mul, hC, div_mul_cancel₀ _ (hc (m + k)), ENNReal.coe_mul,
      ENNReal.coe_toNNReal hω]
  refine ⟨C, fun A f L hf ↦ ?_⟩
  by_cases hA : μH[((m + k : ℕ) : ℝ)] A = ∞
  · have hAE : μHE[m + k] A = ∞ := by
      rw [hHE, hA, ENNReal.mul_top (ENNReal.coe_ne_zero.2 (hc (m + k)))]
    by_cases hCL : C * L ^ m = 0
    · -- `L = 0` and `m ≠ 0`, so `f ≡ f 0` and `{f 0}` is `Lᵐ`-null.
      obtain ⟨rfl, hm⟩ := pow_eq_zero_iff'.1 ((mul_eq_zero.1 hCL).resolve_left hC0)
      have hfc : ∀ x, f x = f 0 := fun x ↦ (LipschitzWith.zero_iff f).1 hf x 0
      have : Nontrivial (Rn m) := Module.nontrivial_of_finrank_pos (R := ℝ)
        (by rw [finrank_euclideanSpace_fin]; exact Nat.pos_of_ne_zero hm)
      refine ⟨({f 0} : Set (Rn m)).indicator fun _ ↦ ∞,
        measurable_const.indicator (measurableSet_singleton _), fun y ↦ ?_, ?_⟩
      · by_cases hy : y = f 0
        · rw [Set.indicator_of_mem (Set.mem_singleton_iff.2 hy)]
          exact le_top
        · have hS : A ∩ f ⁻¹' {y} = ∅ := Set.eq_empty_of_forall_notMem fun x hx ↦
            hy ((show f x = y from hx.2).symm.trans (hfc x))
          rw [hS, measure_empty]
          exact zero_le
      · rw [lintegral_indicator_const (measurableSet_singleton _), measure_singleton, mul_zero]
        exact zero_le
    · refine ⟨fun _ ↦ ∞, measurable_const, fun _ ↦ le_top, ?_⟩
      rw [hAE, ENNReal.mul_top (ENNReal.coe_ne_zero.2 hCL)]
      exact le_top
  · obtain ⟨g₀, hg₀, hle, hint⟩ :=
      Submission.eilenberg_hausdorff_upper_integral_of_ne_top N m k A f L hf hA
    refine ⟨fun y ↦ c k * g₀ y, hg₀.const_mul _, fun y ↦ ?_, ?_⟩
    · show μHE[k] (A ∩ f ⁻¹' {y}) ≤ c k * g₀ y
      rw [hHE]
      gcongr
      exact hle y
    · calc ∫⁻ y, (c k : ℝ≥0∞) * g₀ y = c k * ∫⁻ y, g₀ y := lintegral_const_mul _ hg₀
        _ ≤ c k * (ω * L ^ m * μH[((m + k : ℕ) : ℝ)] A) := by gcongr
        _ = C * c (m + k) * L ^ m * μH[((m + k : ℕ) : ℝ)] A := by rw [hCc]; ring
        _ = ((C * L ^ m : ℝ≥0) : ℝ≥0∞) * μHE[m + k] A := by
          rw [hHE, ENNReal.coe_mul, ENNReal.coe_pow]; ring

/-- **Simon Ch. 2, Theorem 1.5 (p. 42), `C¹` approximation of Lipschitz maps**, vector-valued
(`chapter-02.txt` lines 165–168, proof lines 246–266; used in this form in Ch. 3, proof of
Lemma 1.2, `chapter-03.txt` lines 39–42): for a Lipschitz `f : ℝⁿ → ℝᵖ` and `ε ∈ (0, ∞]` there is
a `C¹` map `g` with `Lⁿ({x : f(x) ≠ g(x) or Df(x) ≠ Dg(x)}) < ε`. Simon proves the scalar case
(`Submission.lipschitz_real_c1_approximation`); it is applied to each coordinate `fⁱ = ⟨f, eᵢ⟩`
with error `ε / p`, and `g = Σ gⁱ eᵢ`. By Rademacher's theorem `f` is differentiable off an
`Lⁿ`-null set, and at each differentiability point `Dfⁱ = ⟨Df, eᵢ⟩` and `Dgⁱ = ⟨Dg, eᵢ⟩`, so
`f ≠ g` or `Df ≠ Dg` there forces `fⁱ ≠ gⁱ` or `Dfⁱ ≠ Dgⁱ` for some `i`. -/
theorem Submission.lipschitz_c1_approximation : ∀ (n p : ℕ) (f : Rn n → Rn p) (K : ℝ≥0),
    LipschitzWith K f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Rn n → Rn p, ContDiff ℝ 1 g ∧
      volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x} < ε := by
  intro n p f K hf ε hε
  -- Each coordinate `fⁱ = ⟨f, eᵢ⟩` is Lipschitz; approximate it with error `ε / p`.
  have hcomp : ∀ i : Fin p, ∃ gi : Rn n → ℝ, ContDiff ℝ 1 gi ∧
      volume {x | f x i ≠ gi x ∨ fderiv ℝ (fun y ↦ f y i) x ≠ fderiv ℝ gi x} < ε / p := fun i ↦
    Submission.lipschitz_real_c1_approximation n (fun y ↦ f y i) _
      ((EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp hf) (ε / p)
      (ENNReal.div_pos hε.ne' (ENNReal.natCast_ne_top p))
  choose G hG hGε using hcomp
  -- `g = Σ gⁱ eᵢ` is `C¹` because its coordinates are.
  let g : Rn n → Rn p := fun x ↦ WithLp.toLp 2 fun i ↦ G i x
  have hgC : ContDiff ℝ 1 g := contDiff_euclidean.2 hG
  refine ⟨g, hgC, ?_⟩
  -- Rademacher: `f` is differentiable off an `Lⁿ`-null set.
  have hZ : volume {x | ¬DifferentiableAt ℝ f x} = 0 := ae_iff.1 hf.ae_differentiableAt
  have hsub : {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x} ⊆ {x | ¬DifferentiableAt ℝ f x} ∪
      ⋃ i, {x | f x i ≠ G i x ∨ fderiv ℝ (fun y ↦ f y i) x ≠ fderiv ℝ (G i) x} := by
    intro x hx
    by_contra hx'
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists, ne_eq,
      not_not] at hx'
    obtain ⟨hfx, hE⟩ := hx'
    -- At a differentiability point, `Dfⁱ(x) = ⟨Df(x), eᵢ⟩` and `Dgⁱ(x) = ⟨Dg(x), eᵢ⟩`.
    have hD : ∀ i, (EuclideanSpace.proj i).comp (fderiv ℝ f x) =
        (EuclideanSpace.proj i).comp (fderiv ℝ g x) := by
      intro i
      have hfi : HasFDerivAt (fun y ↦ f y i) ((EuclideanSpace.proj i).comp (fderiv ℝ f x)) x :=
        (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hfx.hasFDerivAt
      have hgi : HasFDerivAt (G i) ((EuclideanSpace.proj i).comp (fderiv ℝ g x)) x :=
        (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x
          (hgC.differentiable one_ne_zero x).hasFDerivAt
      exact hfi.fderiv.symm.trans ((hE i).2.trans hgi.fderiv)
    rcases hx with hx | hx
    · exact hx (PiLp.ext fun i ↦ (hE i).1)
    · exact hx (ContinuousLinearMap.ext fun v ↦ PiLp.ext fun i ↦
        congrArg (fun L : Rn n →L[ℝ] ℝ ↦ L v) (hD i))
  calc volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x}
      ≤ volume {x | ¬DifferentiableAt ℝ f x} +
          volume (⋃ i, {x | f x i ≠ G i x ∨ fderiv ℝ (fun y ↦ f y i) x ≠ fderiv ℝ (G i) x}) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ∑ i, volume {x | f x i ≠ G i x ∨ fderiv ℝ (fun y ↦ f y i) x ≠ fderiv ℝ (G i) x} := by
        rw [hZ, zero_add]
        exact measure_iUnion_fintype_le _ _
    _ < ε := by
        rcases (Finset.univ : Finset (Fin p)).eq_empty_or_nonempty with h0 | hne
        · rw [h0, Finset.sum_empty]
          exact hε
        · calc _ < ∑ _i : Fin p, ε / p := ENNReal.sum_lt_sum_of_nonempty hne fun i _ ↦ hGε i
            _ = p * (ε / p) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            _ ≤ ε := ENNReal.mul_div_le

/-- **Simon Ch. 3, Lemma 1.2 (pp. 69–70)** (`chapter-03.txt` lines 25–65).
"If": SimonGMT's `countablyRectifiable_of_submanifold_cover`, since `IsC1Submanifold n` is
`Chapter02.IsSimonSubmanifold 1` with the conditions reordered. "Only if": `C¹` approximation
(Ch. 2, 1.5) gives `C¹` maps `Gⱼᵢ` with `Lⁿ{Fⱼ ≠ Gⱼᵢ} < 1/i`; with `Zⱼ = ℝⁿ ∖ ⋃ᵢ {Fⱼ = Gⱼᵢ}`,
`Fⱼ(ℝⁿ) ⊆ Fⱼ(Zⱼ) ∪ ⋃ᵢ Gⱼᵢ(ℝⁿ)` (erratum: (1) is printed as `graph Fⱼ ⊂ Eⱼ ∩ …`) and
`Hⁿ(Fⱼ(Zⱼ)) = 0`; each `Gⱼᵢ(ℝⁿ)` is an `Hⁿ`-null set plus countably many embedded `C¹`
submanifolds. The case `n = 0` needs no separate treatment. -/
theorem Submission.submanifoldCoverCharacterization_holds : SubmanifoldCoverCharacterization := by
  intro n ℓ M
  constructor
  · rintro ⟨M₀, hM₀, F, hF, hM⟩
    choose K hK using hF
    choose G hG hGF using fun j (i : ℕ) ↦ Submission.lipschitz_c1_approximation n (n + ℓ) (F j)
      (K j) (hK j) (i : ℝ≥0∞)⁻¹ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top i))
    -- `Zⱼ` has measure `< 1/i` for every `i`, so `Lⁿ(Zⱼ) = 0` and `Hⁿ(Fⱼ(Zⱼ)) = 0`.
    have hZ : ∀ j, volume {x | ∀ i, F j x ≠ G j i x} = 0 := fun j ↦ by
      by_contra h
      obtain ⟨i, hi⟩ := ENNReal.exists_inv_nat_lt h
      have hsub : {x | ∀ i, F j x ≠ G j i x} ⊆
          {x | F j x ≠ G j i x ∨ fderiv ℝ (F j) x ≠ fderiv ℝ (G j i) x} :=
        fun x hx ↦ Or.inl (hx i)
      exact lt_irrefl _ (((measure_mono hsub).trans_lt (hGF j i)).trans hi)
    have hE : ∀ j, μHE[n] (F j '' {x | ∀ i, F j x ≠ G j i x}) = 0 := fun j ↦ by
      refine le_antisymm ?_ zero_le
      calc _ ≤ (K j : ℝ≥0∞) ^ n * μHE[n] {x | ∀ i, F j x ≠ G j i x} :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              (hK j).lipschitzOnWith
        _ = 0 := by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hZ j, mul_zero]
    -- Each `Gⱼᵢ(ℝⁿ)` is covered by an `Hⁿ`-null set `Cⱼᵢ` and submanifolds `Sⱼᵢₖ`.
    choose C S hC hS hGS using fun j i ↦
      Submission.c1_range_null_union_submanifolds n (n + ℓ) (G j i) (hG j i)
    refine ⟨M₀ ∪ (⋃ j, F j '' {x | ∀ i, F j x ≠ G j i x}) ∪ ⋃ j, ⋃ i, C j i,
      fun k ↦ S k.unpair.1 k.unpair.2.unpair.1 k.unpair.2.unpair.2,
      measure_union_null (measure_union_null hM₀ (measure_iUnion_null hE))
        (measure_iUnion_null fun j ↦ measure_iUnion_null (hC j)),
      fun k ↦ hS _ _ _, fun y hy ↦ ?_⟩
    rcases hM hy with hy | hy
    · exact Or.inl (Or.inl (Or.inl hy))
    obtain ⟨j, z, rfl⟩ := mem_iUnion.1 hy
    rcases em (∃ i, F j z = G j i z) with ⟨i, hi⟩ | hz
    · rw [hi]
      rcases hGS j i (mem_range_self z) with h | h
      · exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨j, i, h⟩))
      obtain ⟨k, hk⟩ := mem_iUnion.1 h
      exact Or.inr (mem_iUnion.2
        ⟨Nat.pair j (Nat.pair i k), by simpa only [Nat.unpair_pair] using hk⟩)
    · exact Or.inl (Or.inl (Or.inr (mem_iUnion.2 ⟨j, z, fun i hi ↦ hz ⟨i, hi⟩, rfl⟩)))
  · rintro ⟨N₀, N, hN₀, hN, hM⟩
    refine Poincare.SimonGMT.Chapter03.countablyRectifiable_of_submanifold_cover hN₀
      (fun j ↦ ⟨le_rfl, fun y hy ↦ ?_⟩) hM
    obtain ⟨V, W, ψ, hV, hW, hyW, hψ, hinj, himage, hproper, hD⟩ := hN j y hy
    exact ⟨V, W, ψ, hyW, hV, hW, hψ, hinj, himage, hproper, hD⟩

/-- **Simon Ch. 3, co-area formula (2.7)–(2.9) and Remark 2.10(2) (p. 77).** Simon derives both
from the `C¹` case (Ch. 2 §6), the decomposition of Remark 1.3 and the `C¹` Approximation
Theorem 1.5 of Ch. 2 (`chapter-03.txt` lines 426–428, 439–442). `rectifiable_c1_chart_pieces`
covers `M`, up to an `Hⁿ`-null set, by pieces `ψ_j(E_j)` of injective `C¹` charts on which
`f ∘ ψ_j` agrees to first order with a `C¹` map `G_j`. (a) is `coarea_tangent_existence`. For
(c), intersect the pieces with a Borel `M_b ⊆ M` of full measure (`ψ_j(E_j)` is Borel by
Lusin–Souslin), apply `chart_piece_coarea_formula` on each piece and glue with
`coarea_gluing_of_pieces`, null sets having `Hᵏ`-null slices by
`coarea_null_slices_of_eilenberg`; (b) is (c) with `g ≡ 1`. For the slices, `M ∩ f⁻¹(y)` lies in
the slice of the uncovered null part together with the sets `ψ_j(D_j ∩ G_j⁻¹(y))`, which are
countably `k`-rectifiable for a.e. `y` by `c1_level_slices_countablyRectifiable`. -/
theorem Submission.coareaFormula_and_slices_hold : CoareaFormula ∧ SlicesAreRectifiable := by
  refine ⟨?_, ?_⟩
  · intro m k ℓ hk M U θ f hM hrect hθ hU hMU hf
    -- Chart pieces `ψ j '' E j` covering `M` up to an `Hⁿ`-null set, with `f ∘ ψ j = G j` on `E j`.
    obtain ⟨D, ψ, G, E, hDo, hψC, hψi, hψL, hψd, hGC, hEm, hED, hfG, hnull⟩ :=
      Submission.rectifiable_c1_chart_pieces Submission.submanifoldCoverCharacterization_holds
        Submission.lipschitz_c1_approximation (m + k) ℓ m M U f hrect hU hMU hf
    -- A Borel `Mb ⊆ M` with `Hⁿ(M \ Mb) = 0`; the Borel pieces are `ψ j '' E j ∩ Mb`.
    obtain ⟨Mb, hMbM, hMbm, hMbae⟩ := hM.exists_measurable_subset_ae_eq
    have hS : ∀ j, MeasurableSet (ψ j '' E j ∩ Mb) := fun j =>
      ((hEm j).image_of_continuousOn_injOn ((hψC j).continuousOn.mono (hED j))
        ((hψi j).mono (hED j))).inter hMbm
    have hSnull : μHE[m + k] (M \ ⋃ j, (ψ j '' E j ∩ Mb)) = 0 := by
      refine measure_mono_null ?_ (measure_union_null hnull (ae_eq_set.1 hMbae).2)
      rintro x ⟨hxM, hx⟩
      by_cases hxb : x ∈ Mb
      · refine Or.inl ⟨hxM, fun hxU => hx ?_⟩
        obtain ⟨j, hj⟩ := mem_iUnion.1 hxU
        exact mem_iUnion.2 ⟨j, hj, hxb⟩
      · exact Or.inr ⟨hxM, hxb⟩
    -- (c): glue the one-piece formulas; null sets have null slices by Eilenberg's inequality.
    have hc := Submission.coarea_gluing_of_pieces (m + k + ℓ) (m + k) m k U M f
      (fun x => ENNReal.ofReal (coareaJacobian (approxTangentPlane (m + k) M θ x) f x))
      (fun j => ψ j '' E j ∩ Mb) hU hMU hf.continuousOn
      (fun Z hZM hZ => Submission.coarea_null_slices_of_eilenberg
        Submission.eilenberg_upper_integral_inequality (m + k + ℓ) m k U Z f hf (hZM.trans hMU) hZ)
      hS hSnull
      (fun j B hB hBm φ hφ => Submission.chart_piece_coarea_formula
        Submission.chart_approx_tangent_and_differential m k ℓ M U θ f (D j) (E j) (ψ j) (G j)
        hk hM hθ hU hMU hf (hDo j) (hψC j) (hψi j) (hψL j) (hψd j) (hGC j) (hEm j) (hED j) (hfG j)
        B (fun x hx => ⟨(hB hx).1, hMbM (hB hx).2⟩) hBm φ hφ)
    refine ⟨Submission.coarea_tangent_existence Submission.submanifoldCoverCharacterization_holds
      Submission.lipschitz_c1_approximation Submission.chart_approx_tangent_and_differential
      (m + k) ℓ m M U θ f hM hrect hθ hU hMU hf, fun A hAM hA => ?_, hc⟩
    -- (b) is (c) with `g ≡ 1`.
    simpa only [one_mul, setLIntegral_one] using hc A hAM hA (fun _ => 1) aemeasurable_const
  · intro m k ℓ hk M U f _ hrect hU hMU hf
    obtain ⟨D, ψ, G, E, hDo, hψC, -, -, -, hGC, -, hED, hfG, hnull⟩ :=
      Submission.rectifiable_c1_chart_pieces Submission.submanifoldCoverCharacterization_holds
        Submission.lipschitz_c1_approximation (m + k) ℓ m M U f hrect hU hMU hf
    -- The uncovered part of `M` has `Hᵏ`-null slices for a.e. `y`.
    have hZ := Submission.coarea_null_slices_of_eilenberg
      Submission.eilenberg_upper_integral_inequality (m + k + ℓ) m k U (M \ ⋃ j, ψ j '' E j) f hf
      (Set.sdiff_subset.trans hMU) hnull
    -- For a.e. `y`, every `ψ j '' (D j ∩ G j ⁻¹' {y})` is countably `k`-rectifiable.
    have hR : ∀ᵐ y ∂(volume : Measure (Rn m)), ∀ j,
        CountablyRectifiable k (ψ j '' (D j ∩ G j ⁻¹' {y})) :=
      ae_all_iff.2 fun j => Submission.c1_level_slices_countablyRectifiable m k (m + k + ℓ) (D j)
        (ψ j) (G j) hk (hDo j) (hψC j) (hGC j)
    filter_upwards [hZ, hR] with y hy hyR
    obtain ⟨M₀, hM₀, F, hF, hcov⟩ := Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion _ hyR
    refine ⟨M₀ ∪ ((M \ ⋃ j, ψ j '' E j) ∩ f ⁻¹' {y}), measure_union_null hM₀ hy, F, hF, ?_⟩
    rintro x ⟨hxM, hxy⟩
    by_cases hx : x ∈ ⋃ j, ψ j '' E j
    · -- `x = ψ j u` with `u ∈ E j ⊆ D j` and `G j u = f x = y`.
      obtain ⟨j, u, hu, rfl⟩ := mem_iUnion.1 hx
      rcases hcov (mem_iUnion.2 ⟨j, u, ⟨hED j hu, (hfG j u hu).1.symm.trans hxy⟩, rfl⟩) with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · exact Or.inl (Or.inr ⟨⟨hxM, hx⟩, hxy⟩)

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
