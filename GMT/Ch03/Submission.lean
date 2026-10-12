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

/-- **Locally Lipschitz maps send `Hⁿ`-null sets to `Hⁿ`-null sets**: the "(easily checked)
fact" used to conclude the area formula (2.4) in Simon Ch. 3 (`chapter-03.txt` lines 393–396).
Each `x ∈ Z ⊆ U` has an open `o x ∋ x` with `f` `K x`-Lipschitz on `o x ∩ U`; by Lindelöf
countably many `o x`, `x ∈ T ⊆ Z`, cover `Z`. By Ch. 2, Thm. 1.8(i) (`chapter-02.txt`
lines 270–295, valid for non-measurable sets) `Hⁿ(f(Z ∩ o x)) ≤ (K x)ⁿ Hⁿ(Z ∩ o x) = 0`, and
countable subadditivity gives `Hⁿ(f(Z)) = 0`. Neither openness of `U` nor measurability of `Z`
is needed: all estimates are for outer measures. -/
theorem Submission.areaFormula_image_null_of_locallyLipschitzOn : ∀ (N P n : ℕ)
    (U Z : Set (Rn N)) (f : Rn N → Rn P), LocallyLipschitzOn U f → Z ⊆ U → μHE[n] Z = 0 →
    μHE[n] (f '' Z) = 0 := by
  intro N P n U Z f hf hZU hZ
  -- Step 1: each `x ∈ Z` has an open `o x ∋ x` with `f` `K x`-Lipschitz on `o x ∩ U`.
  have hloc : ∀ x ∈ Z, ∃ o : Set (Rn N), IsOpen o ∧ x ∈ o ∧
      ∃ K : ℝ≥0, LipschitzOnWith K f (o ∩ U) := by
    intro x hx
    obtain ⟨K, t, ht, hK⟩ := hf (hZU hx)
    obtain ⟨o, ho, hxo, hot⟩ := mem_nhdsWithin.mp ht
    exact ⟨o, ho, hxo, K, hK.mono hot⟩
  choose! o ho hxo K hK using hloc
  -- Step 2 (Lindelöf): countably many `o x`, `x ∈ T ⊆ Z`, cover `Z`.
  obtain ⟨T, hTZ, hTc, hTo⟩ := TopologicalSpace.isOpen_biUnion_countable Z o ho
  have hcover : f '' Z ⊆ ⋃ x ∈ T, f '' (Z ∩ o x) := by
    rintro _ ⟨z, hz, rfl⟩
    have hzT : z ∈ ⋃ x ∈ T, o x := by
      rw [hTo]
      exact mem_biUnion hz (hxo z hz)
    obtain ⟨x, hxT, hzx⟩ := mem_iUnion₂.mp hzT
    exact mem_iUnion₂.mpr ⟨x, hxT, z, ⟨hz, hzx⟩, rfl⟩
  -- Step 3: `Z ∩ o x ⊆ o x ∩ U`, so `Hⁿ(f(Z ∩ o x)) ≤ (K x)ⁿ Hⁿ(Z ∩ o x) = 0`.
  have hpiece : ∀ x ∈ T, μHE[n] (f '' (Z ∩ o x)) = 0 := by
    intro x hx
    have hL : LipschitzOnWith (K x) f (Z ∩ o x) :=
      (hK x (hTZ hx)).mono fun z hz ↦ ⟨hz.2, hZU hz.1⟩
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hL
    rw [measure_mono_null inter_subset_left hZ, mul_zero] at h
    exact nonpos_iff_eq_zero.mp h
  -- Step 4: countable subadditivity.
  exact measure_mono_null hcover ((measure_biUnion_null_iff hTc).2 hpiece)
/-- **Good chart pieces** (Simon Ch. 3, Lemma 1.2, "if" part, `chapter-03.txt` lines 25–38, for
the embedded `C¹` submanifolds of Ch. 2, (4.1)). Let `U` be open, `M ⊆ U`, `f` locally Lipschitz
on `U`, and `M ⊆ N₀ ∪ ⋃ⱼ Sⱼ` with every `Sⱼ` an `n`-dimensional embedded `C¹` submanifold. Then
`M ⊆ N₀ ∪ ⋃_α ψ_α(D_α)` for countably many `C¹` maps `ψ_α` on open `V_α ⊆ ℝⁿ` with injective
differential and compact `D_α ⊆ V_α` on which `ψ_α` is bi-Lipschitz and `f ∘ ψ_α` is Lipschitz.
By Lindelöf, countably many charts cover each `Sⱼ`. At a parameter `u₀` with `ψ(u₀) ∈ U`, the
injectivity of `A = Dψ(u₀)`, the continuity of `Dψ` and the mean value inequality give a closed
ball on which `|ψ(u) - ψ(v) - A(u - v)| ≤ (m/2)|u - v|`, `m|w| ≤ |A w|`, so `ψ` is bi-Lipschitz
there; shrinking it, `ψ` maps it into a ball on which `f` is Lipschitz. By Lindelöf again,
countably many such balls cover `V ∩ ψ⁻¹(U)`, and all pieces are enumerated by `ℕ`. -/
theorem Submission.areaFormula_good_chart_pieces : ∀ (n N p : ℕ) (M U N₀ : Set (Rn N)) (S : ℕ → Set (Rn N)) (f : Rn N → Rn p), IsOpen U → M ⊆ U → LocallyLipschitzOn U f → (∀ j, IsC1Submanifold n (S j)) → M ⊆ N₀ ∪ ⋃ j, S j → ∃ (V D : ℕ → Set (Rn n)) (ψ : ℕ → Rn n → Rn N) (K C : ℕ → ℝ≥0), (∀ α, IsOpen (V α) ∧ ContDiffOn ℝ 1 (ψ α) (V α) ∧ (∀ u ∈ V α, Function.Injective (fderiv ℝ (ψ α) u)) ∧ IsCompact (D α) ∧ D α ⊆ V α ∧ LipschitzOnWith (K α) (ψ α) (D α) ∧ (∀ u ∈ D α, ∀ v ∈ D α, dist u v ≤ (C α : ℝ) * dist (ψ α u) (ψ α v)) ∧ LipschitzOnWith (K α) (f ∘ ψ α) (D α)) ∧ M ⊆ N₀ ∪ ⋃ α, ψ α '' D α := by
  intro n N p M U N₀ S f hU hMU hf hS hcov
  classical
  -- Step 2: a good closed ball around a chart parameter `u₀` with `ψ(u₀) ∈ U`.
  have goodBall : ∀ (V : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 1 ψ V →
      (∀ u ∈ V, Function.Injective (fderiv ℝ ψ u)) → ∀ u₀ ∈ V, ψ u₀ ∈ U →
      ∃ r > 0, Metric.closedBall u₀ r ⊆ V ∧ ∃ K C : ℝ≥0,
        LipschitzOnWith K ψ (Metric.closedBall u₀ r) ∧
        (∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
          dist u v ≤ (C : ℝ) * dist (ψ u) (ψ v)) ∧
        LipschitzOnWith K (f ∘ ψ) (Metric.closedBall u₀ r) := by
    intro V ψ hV hψC hInj u₀ hu₀ hx₀
    -- (a) `A = Dψ(u₀)` is injective, so `m ‖w‖ ≤ ‖A w‖` with `m = K_A⁻¹ > 0`.
    set A := fderiv ℝ ψ u₀ with hA
    obtain ⟨KA, hKA0, hKA⟩ := LinearMap.exists_antilipschitzWith A.toLinearMap
      (LinearMap.ker_eq_bot.mpr (hInj u₀ hu₀))
    have hKA0' : (0 : ℝ) < KA := by exact_mod_cast hKA0
    set m : ℝ := (KA : ℝ)⁻¹ with hm
    have hm0 : 0 < m := inv_pos.mpr hKA0'
    have hAlow : ∀ w : Rn n, m * ‖w‖ ≤ ‖A w‖ := by
      intro w
      have h1 : dist w 0 ≤ KA * dist (A.toLinearMap w) (A.toLinearMap 0) := hKA.le_mul_dist w 0
      rw [map_zero, dist_zero_right, dist_zero_right] at h1
      have h2 : ‖w‖ ≤ KA * ‖A w‖ := h1
      rw [hm, inv_mul_le_iff₀ hKA0']
      exact h2
    -- (b), (c) radii: `‖Dψ(z) - A‖ < m/2`, the ball lies in `V`, and `ψ` maps it into a ball
    -- `B_s(ψ(u₀)) ⊆ t` on which `f` is `L_f`-Lipschitz.
    have hcont : ContinuousOn (fun z ↦ fderiv ℝ ψ z) V :=
      hψC.continuousOn_fderiv_of_isOpen hV le_rfl
    have hcontAt : ContinuousAt (fun z ↦ fderiv ℝ ψ z) u₀ := hcont.continuousAt (hV.mem_nhds hu₀)
    obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.mp hcontAt (m / 2) (half_pos hm0)
    obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.isOpen_iff.mp hV u₀ hu₀
    obtain ⟨Lf, t, ht, hLf⟩ := hf hx₀
    rw [hU.nhdsWithin_eq hx₀] at ht
    obtain ⟨s, hs, hst⟩ := Metric.mem_nhds_iff.mp ht
    have hψcontAt : ContinuousAt ψ u₀ := hψC.continuousOn.continuousAt (hV.mem_nhds hu₀)
    obtain ⟨δ₃, hδ₃, hδ₃'⟩ := Metric.continuousAt_iff.mp hψcontAt s hs
    set r := min (min δ₁ δ₂) δ₃ / 2 with hr
    have hmin0 : 0 < min (min δ₁ δ₂) δ₃ := lt_min (lt_min hδ₁ hδ₂) hδ₃
    have hr0 : 0 < r := by rw [hr]; linarith
    have hrmin : r < min (min δ₁ δ₂) δ₃ := by rw [hr]; linarith
    have hrlt : ∀ u ∈ Metric.closedBall u₀ r,
        dist u u₀ < δ₁ ∧ dist u u₀ < δ₂ ∧ dist u u₀ < δ₃ := by
      intro u hu
      have hu' : dist u u₀ < min (min δ₁ δ₂) δ₃ :=
        lt_of_le_of_lt (Metric.mem_closedBall.mp hu) hrmin
      simp only [lt_min_iff] at hu'
      exact ⟨hu'.1.1, hu'.1.2, hu'.2⟩
    have hBV : Metric.closedBall u₀ r ⊆ V := fun u hu ↦ hδ₂' (Metric.mem_ball.mpr (hrlt u hu).2.1)
    have hdiffB : ∀ z ∈ Metric.closedBall u₀ r, DifferentiableAt ℝ ψ z := fun z hz ↦
      ((hψC.differentiableOn one_ne_zero) z (hBV hz)).differentiableAt (hV.mem_nhds (hBV hz))
    -- Mean value inequality for `z ↦ ψ z - A z` on the convex ball.
    have hMV : ∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
        ‖(ψ u - A u) - (ψ v - A v)‖ ≤ m / 2 * ‖u - v‖ := by
      intro u hu v hv
      have hg : ∀ z ∈ Metric.closedBall u₀ r, DifferentiableAt ℝ (fun z ↦ ψ z - A z) z :=
        fun z hz ↦ (hdiffB z hz).sub A.differentiableAt
      have hbound : ∀ z ∈ Metric.closedBall u₀ r, ‖fderiv ℝ (fun z ↦ ψ z - A z) z‖ ≤ m / 2 := by
        intro z hz
        rw [fderiv_fun_sub (hdiffB z hz) A.differentiableAt, A.fderiv, ← dist_eq_norm]
        exact (hδ₁' (hrlt z hz).1).le
      exact Convex.norm_image_sub_le_of_norm_fderiv_le hg hbound (convex_closedBall u₀ r) hv hu
    have hupper : ∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
        dist (ψ u) (ψ v) ≤ (‖A‖ + m / 2) * dist u v := by
      intro u hu v hv
      rw [dist_eq_norm, dist_eq_norm]
      have h1 := hMV u hu v hv
      have h2 : ‖A (u - v)‖ ≤ ‖A‖ * ‖u - v‖ := A.le_opNorm _
      have h3 : ψ u - ψ v = ((ψ u - A u) - (ψ v - A v)) + A (u - v) := by rw [map_sub]; abel
      calc ‖ψ u - ψ v‖ = ‖((ψ u - A u) - (ψ v - A v)) + A (u - v)‖ := by rw [← h3]
        _ ≤ ‖(ψ u - A u) - (ψ v - A v)‖ + ‖A (u - v)‖ := norm_add_le _ _
        _ ≤ m / 2 * ‖u - v‖ + ‖A‖ * ‖u - v‖ := add_le_add h1 h2
        _ = (‖A‖ + m / 2) * ‖u - v‖ := by ring
    have hlower : ∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
        dist u v ≤ ((2 * KA : ℝ≥0) : ℝ) * dist (ψ u) (ψ v) := by
      intro u hu v hv
      rw [dist_eq_norm, dist_eq_norm]
      have h1 := hMV u hu v hv
      have h2 := hAlow (u - v)
      have h3 : A (u - v) = (ψ u - ψ v) - ((ψ u - A u) - (ψ v - A v)) := by rw [map_sub]; abel
      have h4 : ‖A (u - v)‖ ≤ ‖ψ u - ψ v‖ + m / 2 * ‖u - v‖ := by
        rw [h3]; exact (norm_sub_le _ _).trans (add_le_add le_rfl h1)
      have h5 : m / 2 * ‖u - v‖ ≤ ‖ψ u - ψ v‖ := by linarith
      have hKAeq : (KA : ℝ) * m = 1 := by rw [hm]; exact mul_inv_cancel₀ hKA0'.ne'
      push_cast
      calc ‖u - v‖ = (2 * KA) * (m / 2 * ‖u - v‖) := by
            have : (2 * (KA : ℝ)) * (m / 2 * ‖u - v‖) = ((KA : ℝ) * m) * ‖u - v‖ := by ring
            rw [this, hKAeq, one_mul]
        _ ≤ (2 * KA) * ‖ψ u - ψ v‖ := mul_le_mul_of_nonneg_left h5 (by positivity)
    -- (d) `K = (‖A‖ + m/2) + L_f (‖A‖ + m/2)` and `C = 2 K_A`.
    set K0 : ℝ≥0 := ⟨‖A‖ + m / 2, by positivity⟩ with hK0
    have hK0r : (K0 : ℝ) = ‖A‖ + m / 2 := rfl
    refine ⟨r, hr0, hBV, K0 + Lf * K0, 2 * KA, ?_, hlower, ?_⟩
    · refine LipschitzOnWith.of_dist_le_mul fun u hu v hv ↦ ?_
      calc dist (ψ u) (ψ v) ≤ (‖A‖ + m / 2) * dist u v := hupper u hu v hv
        _ ≤ ((K0 + Lf * K0 : ℝ≥0) : ℝ) * dist u v := by
          push_cast
          rw [hK0r]
          have h0 : 0 ≤ (Lf : ℝ) * (‖A‖ + m / 2) := by positivity
          exact mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    · refine LipschitzOnWith.of_dist_le_mul fun u hu v hv ↦ ?_
      have hψu : ψ u ∈ t := hst (Metric.mem_ball.mpr (hδ₃' (hrlt u hu).2.2))
      have hψv : ψ v ∈ t := hst (Metric.mem_ball.mpr (hδ₃' (hrlt v hv).2.2))
      calc dist (f (ψ u)) (f (ψ v)) ≤ Lf * dist (ψ u) (ψ v) := hLf.dist_le_mul _ hψu _ hψv
        _ ≤ Lf * ((‖A‖ + m / 2) * dist u v) := by gcongr; exact hupper u hu v hv
        _ ≤ ((K0 + Lf * K0 : ℝ≥0) : ℝ) * dist u v := by
          push_cast
          rw [hK0r]
          have h0 : 0 ≤ (‖A‖ + m / 2) * dist u v := by positivity
          have h1 : (‖A‖ + m / 2 + ↑Lf * (‖A‖ + m / 2)) * dist u v =
              (‖A‖ + m / 2) * dist u v + ↑Lf * ((‖A‖ + m / 2) * dist u v) := by ring
          rw [h1]
          linarith
  -- Step 1: by Lindelöf, countably many charts `ψ_{j,y}`, `y ∈ T j`, cover each `S j`.
  choose! Vc Wc ψc hVc hWc hyW hψC hInjOn hImg hProper hDer using hS
  choose T hTS hTc hTU using fun j ↦
    TopologicalSpace.isOpen_biUnion_countable (S j) (Wc j) (fun y hy ↦ hWc j y hy)
  -- Step 3: by Lindelöf in `ℝⁿ`, countably many good balls cover `V_{j,y} ∩ ψ_{j,y}⁻¹(U)`.
  have hgood : ∀ j, ∀ y ∈ S j, ∀ u₀ ∈ Vc j y ∩ ψc j y ⁻¹' U, ∃ r > 0,
      Metric.closedBall u₀ r ⊆ Vc j y ∧ ∃ K C : ℝ≥0,
        LipschitzOnWith K (ψc j y) (Metric.closedBall u₀ r) ∧
        (∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
          dist u v ≤ (C : ℝ) * dist (ψc j y u) (ψc j y v)) ∧
        LipschitzOnWith K (f ∘ ψc j y) (Metric.closedBall u₀ r) := fun j y hy u₀ hu₀ ↦
    goodBall (Vc j y) (ψc j y) (hVc j y hy) (hψC j y hy) (hDer j y hy) u₀ hu₀.1 hu₀.2
  choose! r hr hrV Kb Cb hKb hCb hfKb using hgood
  choose Q hQO hQc hQU using fun j y ↦
    TopologicalSpace.isOpen_biUnion_countable (Vc j y ∩ ψc j y ⁻¹' U)
      (fun u₀ ↦ Metric.ball u₀ (r j y u₀)) (fun _ _ ↦ Metric.isOpen_ball)
  -- Step 4: the countable index set of pieces `(j, y, u₀)`.
  set I : Set (ℕ × Rn N × Rn n) := ⋃ j, ⋃ y ∈ T j, (fun u ↦ (j, y, u)) '' Q j y with hIdef
  have hIc : I.Countable :=
    Set.countable_iUnion fun j ↦ (hTc j).biUnion fun y _ ↦ (hQc j y).image _
  have hImem : ∀ π ∈ I, π.2.1 ∈ T π.1 ∧ π.2.2 ∈ Q π.1 π.2.1 := by
    intro π hπ
    simp only [hIdef, mem_iUnion, mem_image] at hπ
    obtain ⟨j, y, hy, u, hu, rfl⟩ := hπ
    exact ⟨hy, hu⟩
  -- Step 5: the per-piece properties.
  have hpiece : ∀ π ∈ I, IsOpen (Vc π.1 π.2.1) ∧ ContDiffOn ℝ 1 (ψc π.1 π.2.1) (Vc π.1 π.2.1) ∧
      (∀ u ∈ Vc π.1 π.2.1, Function.Injective (fderiv ℝ (ψc π.1 π.2.1) u)) ∧
      IsCompact (Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2)) ∧
      Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2) ⊆ Vc π.1 π.2.1 ∧
      LipschitzOnWith (Kb π.1 π.2.1 π.2.2) (ψc π.1 π.2.1)
        (Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2)) ∧
      (∀ u ∈ Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2),
        ∀ v ∈ Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2),
          dist u v ≤ (Cb π.1 π.2.1 π.2.2 : ℝ) * dist (ψc π.1 π.2.1 u) (ψc π.1 π.2.1 v)) ∧
      LipschitzOnWith (Kb π.1 π.2.1 π.2.2) (f ∘ ψc π.1 π.2.1)
        (Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2)) := by
    intro π hπ
    obtain ⟨hyT, huQ⟩ := hImem π hπ
    have hy : π.2.1 ∈ S π.1 := hTS π.1 hyT
    have hu : π.2.2 ∈ Vc π.1 π.2.1 ∩ ψc π.1 π.2.1 ⁻¹' U := hQO π.1 π.2.1 huQ
    exact ⟨hVc _ _ hy, hψC _ _ hy, hDer _ _ hy, isCompact_closedBall _ _, hrV _ _ hy _ hu,
      hKb _ _ hy _ hu, hCb _ _ hy _ hu, hfKb _ _ hy _ hu⟩
  -- Step 6: every `x ∈ M \ N₀` is `ψ_{j,y}(u)` with `u` in one of the chosen balls.
  have hcovI : ∀ x ∈ M, x ∉ N₀ → ∃ π ∈ I,
      x ∈ ψc π.1 π.2.1 '' Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2) := by
    intro x hxM hxN
    rcases hcov hxM with hx0 | hx1
    · exact absurd hx0 hxN
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx1
    have hxW : x ∈ ⋃ y ∈ T j, Wc j y := by
      rw [hTU j]; exact mem_biUnion hxj (hyW j x hxj)
    obtain ⟨y, hyT, hxWy⟩ := mem_iUnion₂.mp hxW
    have hy : y ∈ S j := hTS j hyT
    have hxim : x ∈ ψc j y '' Vc j y := by rw [hImg j y hy]; exact ⟨hxWy, hxj⟩
    obtain ⟨u, huV, rfl⟩ := hxim
    have huO : u ∈ Vc j y ∩ ψc j y ⁻¹' U := ⟨huV, hMU hxM⟩
    have hu' : u ∈ ⋃ u₀ ∈ Q j y, Metric.ball u₀ (r j y u₀) := by
      rw [hQU j y]; exact mem_biUnion huO (Metric.mem_ball_self (hr j y hy u huO))
    obtain ⟨u₀, hu₀Q, huB⟩ := mem_iUnion₂.mp hu'
    refine ⟨(j, y, u₀), ?_, u, Metric.ball_subset_closedBall huB, rfl⟩
    simp only [hIdef, mem_iUnion, mem_image]
    exact ⟨j, y, hyT, u₀, hu₀Q, rfl⟩
  -- Step 4 (enumeration): a surjection `ℕ → I`, or empty pieces if `I = ∅`.
  by_cases hIne : I.Nonempty
  · obtain ⟨e, he⟩ := hIc.exists_eq_range hIne
    have heI : ∀ α, e α ∈ I := fun α ↦ by rw [he]; exact mem_range_self α
    refine ⟨fun α ↦ Vc (e α).1 (e α).2.1,
      fun α ↦ Metric.closedBall (e α).2.2 (r (e α).1 (e α).2.1 (e α).2.2),
      fun α ↦ ψc (e α).1 (e α).2.1, fun α ↦ Kb (e α).1 (e α).2.1 (e α).2.2,
      fun α ↦ Cb (e α).1 (e α).2.1 (e α).2.2, fun α ↦ hpiece (e α) (heI α), ?_⟩
    intro x hxM
    by_cases hxN : x ∈ N₀
    · exact Or.inl hxN
    · obtain ⟨π, hπI, hxπ⟩ := hcovI x hxM hxN
      rw [he] at hπI
      obtain ⟨α, rfl⟩ := hπI
      exact Or.inr (mem_iUnion.mpr ⟨α, hxπ⟩)
  · refine ⟨fun _ ↦ ∅, fun _ ↦ ∅, fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, fun α ↦ ?_, ?_⟩
    · simp
    · intro x hxM
      by_cases hxN : x ∈ N₀
      · exact Or.inl hxN
      · obtain ⟨π, hπI, -⟩ := hcovI x hxM hxN
        exact absurd ⟨π, hπI⟩ hIne
/-- **Tangent plane, tangential differential and Jacobian chain rule at a chart parameter**
(Simon Ch. 3, (2.1)–(2.3), `chapter-03.txt` lines 327–369, with the Jacobian chain rule of Ch. 2,
(4.11), `chapter-02.txt` lines 960–981). Let `x = ψ(u)`, `A = Dψ(u)`, `T = range A` and
`B = D(f ∘ ψ)(u)`. If `θ(x) ≠ 0`, `T` is a weighted approximate tangent space of `M` at `x`, and
`t ↦ f(x + t A w)` has derivative `B w` at `t = 0` for every `w`, then `T_x M = T`, `d^M f_x`
exists on `T`, and `J^M_f(x) · Jψ(u) = J(f ∘ ψ)(u)`. By uniqueness of approximate tangent spaces
`T_x M = T`; `dim T = n` makes `A` injective, so `L = B ∘ (A|^T)⁻¹` is a tangential differential,
and by uniqueness of line derivatives it is `d^M f_x`; finally `B = L ∘ A|^T` with
`dim ℝⁿ = dim T` gives `normDet B = normDet L · normDet A`. -/
theorem Submission.areaFormula_chart_jacobian_identity : ∀ (n N p : ℕ) (M : Set (Rn N)) (θ : Rn N → ℝ) (f : Rn N → Rn p) (ψ : Rn n → Rn N) (u : Rn n), θ (ψ u) ≠ 0 → HasWeightedApproximateTangentSpaceAt n M θ (ψ u) (LinearMap.range (fderiv ℝ ψ u).toLinearMap) → (∀ w : Rn n, HasLineDerivAt ℝ f (fderiv ℝ (f ∘ ψ) u w) (ψ u) (fderiv ℝ ψ u w)) → approxTangentPlane n M θ (ψ u) = LinearMap.range (fderiv ℝ ψ u).toLinearMap ∧ (∃ L : ↥(LinearMap.range (fderiv ℝ ψ u).toLinearMap) →L[ℝ] Rn p, HasTangentialDifferentialAt (LinearMap.range (fderiv ℝ ψ u).toLinearMap) f (ψ u) L) ∧ areaJacobian (approxTangentPlane n M θ (ψ u)) f (ψ u) * (fderiv ℝ ψ u).toLinearMap.normDet = (fderiv ℝ (f ∘ ψ) u).toLinearMap.normDet := by
  intro n N p M θ f ψ u hθ hW hline
  classical
  -- Step 1: `T_x M = T`, by uniqueness of weighted approximate tangent spaces (`θ x ≠ 0`).
  have h1 : approxTangentPlane n M θ (ψ u) = LinearMap.range (fderiv ℝ ψ u).toLinearMap := by
    have hex : ∃ P : Submodule ℝ (Rn N), HasWeightedApproximateTangentSpaceAt n M θ (ψ u) P :=
      ⟨_, hW⟩
    unfold approxTangentPlane
    rw [dite_eq_left hex]
    exact hex.choose_spec.unique hθ hW
  -- Step 2: `finrank T = n = dim ℝⁿ`, so `A` is injective by rank–nullity.
  have hinj : Function.Injective (fderiv ℝ ψ u).toLinearMap := by
    have h := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ ψ u).toLinearMap
    rw [hW.1, finrank_euclideanSpace_fin] at h
    have hk : Module.finrank ℝ (LinearMap.ker (fderiv ℝ ψ u).toLinearMap) = 0 := by omega
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.finrank_eq_zero.mp hk
  set T := LinearMap.range (fderiv ℝ ψ u).toLinearMap
  -- The corestriction `A' : ℝⁿ ≃ T` of `A`.
  let e : Rn n ≃ₗ[ℝ] T := LinearEquiv.ofInjective (fderiv ℝ ψ u).toLinearMap hinj
  -- Step 3: `L = B ∘ (A')⁻¹` is a tangential differential of `f` at `x` along `T`.
  let L : T →L[ℝ] Rn p :=
    LinearMap.toContinuousLinearMap ((fderiv ℝ (f ∘ ψ) u).toLinearMap ∘ₗ e.symm.toLinearMap)
  have hLapp : ∀ τ : T, L τ = fderiv ℝ (f ∘ ψ) u (e.symm τ) := fun τ ↦ rfl
  have heA : ∀ τ : T, fderiv ℝ ψ u (e.symm τ) = (τ : Rn N) := fun τ ↦
    congrArg Subtype.val (e.apply_symm_apply τ)
  have hL : HasTangentialDifferentialAt T f (ψ u) L := by
    intro τ
    have := hline (e.symm τ)
    rw [heA τ] at this
    rwa [hLapp τ]
  -- Step 4: by uniqueness of line derivatives, `d^M f_x = L`.
  have hunique : tangentialDifferential T f (ψ u) = L := by
    have hex : ∃ L' : T →L[ℝ] Rn p, HasTangentialDifferentialAt T f (ψ u) L' := ⟨L, hL⟩
    unfold tangentialDifferential
    rw [dite_eq_left hex]
    refine ContinuousLinearMap.ext fun τ ↦ ?_
    exact (hex.choose_spec τ).unique (hL τ)
  refine ⟨h1, ⟨L, hL⟩, ?_⟩
  rw [h1]
  unfold areaJacobian
  rw [hunique]
  -- Step 5: `B = L ∘ A'` with `dim ℝⁿ = dim T`, and `normDet A' = normDet A`.
  have hcomp : L.toLinearMap ∘ₗ e.toLinearMap = (fderiv ℝ (f ∘ ψ) u).toLinearMap := by
    refine LinearMap.ext fun w ↦ ?_
    show L (e w) = _
    rw [hLapp]
    simp
  have hcod : e.toLinearMap =
      (fderiv ℝ ψ u).toLinearMap.codRestrict T (fun c ↦ LinearMap.mem_range_self _ c) :=
    LinearMap.ext fun w ↦ Subtype.ext rfl
  have h2 := LinearMap.normDet_comp_of_finrank_eq e.toLinearMap L.toLinearMap
    (by rw [finrank_euclideanSpace_fin, hW.1])
  rw [hcomp, hcod, LinearMap.normDet_codRestrict] at h2
  exact h2.symm
/-- **Area formula on one chart piece**: Simon Ch. 3, (2.4)–(2.5) on a single piece `ψ(D)`
(`chapter-03.txt` lines 370–401). Let `ψ` be differentiable with injective derivative at every
point of the compact set `D ⊆ ℝⁿ`, `K`-Lipschitz with `|u - v| ≤ C |ψ u - ψ v|` on `D`, and let
`f ∘ ψ` be `K`-Lipschitz on `D`. If `S ⊆ ψ(D)` is `Hⁿ`-measurable, `J(ψ u) Jψ(u) = J(f ∘ ψ)(u)`
for `Lⁿ`-a.e. `u ∈ B = D ∩ ψ⁻¹(S)`, and `h ≥ 0` is `Hⁿ⌞S`-measurable, then
`∫_S h J dHⁿ = ∫ ∑_{x ∈ S ∩ f⁻¹(y)} h(x) dHⁿ(y)` and the fibre sum is `Hⁿ`-measurable.

Proof: the weighted area formula with multiplicity, Simon Ch. 2 (3.2), (3.4)–(3.5)
(`chapter-02.txt` lines 760–797), is applied to `ψ` and to `f ∘ ψ` on `B`; the Jacobian identity
links the two, and `ψ` reindexes the fibres of `f ∘ ψ` in `B` as the fibres of `f` in `S`.
Simon refers to [Har79], [Fed69] for the approximation argument behind (3.2), and the SimonGMT modules
proving it lie outside the frozen imports, so it is derived here from the linear case (3.1),
Mathlib's `LinearMap.euclideanHausdorffMeasure_image`: comparison with linear maps on the
pieces of `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, a density-point bound on
derivatives (adapted from Mathlib's `ApproximatesLinearOn.norm_fderiv_sub_le`), injective
branches for the multiplicity, and null images of critical points via the graphs
`x ↦ (g x, ε x)` as `ε → 0`. -/
theorem Submission.areaFormula_on_chart_piece : ∀ (n N p : ℕ) (ψ : Rn n → Rn N) (f : Rn N → Rn p) (D : Set (Rn n)) (K C : ℝ≥0) (J : Rn N → ℝ) (S : Set (Rn N)) (h : Rn N → ℝ≥0∞), IsCompact D → (∀ u ∈ D, DifferentiableAt ℝ ψ u) → (∀ u ∈ D, Function.Injective (fderiv ℝ ψ u)) → LipschitzOnWith K ψ D → (∀ u ∈ D, ∀ v ∈ D, dist u v ≤ (C : ℝ) * dist (ψ u) (ψ v)) → LipschitzOnWith K (f ∘ ψ) D → S ⊆ ψ '' D → NullMeasurableSet S μHE[n] → (∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ D → ψ u ∈ S → DifferentiableAt ℝ (f ∘ ψ) u ∧ J (ψ u) * (fderiv ℝ ψ u).toLinearMap.normDet = (fderiv ℝ (f ∘ ψ) u).toLinearMap.normDet) → AEMeasurable h ((μHE[n] : Measure (Rn N)).restrict S) → (∫⁻ x in S, h x * ENNReal.ofReal (J x) ∂μHE[n] = ∫⁻ y, ∑' x : ↥(S ∩ f ⁻¹' {y}), h x ∂μHE[n]) ∧ AEMeasurable (fun y ↦ ∑' x : ↥(S ∩ f ⁻¹' {y}), h x) (μHE[n] : Measure (Rn p)) := by
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
  -- Simon Ch. 3 (2.4)–(2.5) on the chart piece `ψ(D)`.
  intro N p ψ f D K C J S h hD hdiff hinj hψL hanti hgL hSD hS hJ hh
  -- Step 1: `ψ` is injective on `D` with a `C`-Lipschitz inverse, so `Hⁿ`-null subsets of
  -- `ψ(D)` pull back to `Lⁿ`-null subsets of `D`.
  set B : Set (Rn n) := D ∩ ψ ⁻¹' S with hBdef
  have hBD : B ⊆ D := inter_subset_left
  have hψinj : InjOn ψ D := by
    intro u hu v hv huv
    have := hanti u hu v hv
    rw [huv, dist_self, mul_zero] at this
    exact dist_le_zero.mp this
  have hφL : LipschitzOnWith C (Function.invFunOn ψ D) (ψ '' D) := by
    refine LipschitzOnWith.of_dist_le_mul fun y₁ hy₁ y₂ hy₂ ↦ ?_
    obtain ⟨u₁, hu₁, rfl⟩ := hy₁
    obtain ⟨u₂, hu₂, rfl⟩ := hy₂
    rw [hψinj.leftInvOn_invFunOn hu₁, hψinj.leftInvOn_invFunOn hu₂]
    exact hanti u₁ hu₁ u₂ hu₂
  have hpre : ∀ E ⊆ ψ '' D, D ∩ ψ ⁻¹' E = Function.invFunOn ψ D '' E := by
    intro E hE
    ext u
    constructor
    · rintro ⟨huD, huE⟩
      exact ⟨ψ u, huE, hψinj.leftInvOn_invFunOn huD⟩
    · rintro ⟨y, hyE, rfl⟩
      have hy : ∃ a ∈ D, ψ a = y := hE hyE
      refine ⟨Function.invFunOn_mem hy, ?_⟩
      rw [mem_preimage, Function.invFunOn_eq hy]
      exact hyE
  have hnullpre : ∀ E ⊆ ψ '' D, μHE[n] E = 0 →
      (volume : Measure (Rn n)) (D ∩ ψ ⁻¹' E) = 0 := by
    intro E hE hE0
    rw [hpre E hE, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    refine le_antisymm ?_ bot_le
    calc μHE[n] (Function.invFunOn ψ D '' E)
        ≤ (C : ℝ≥0∞) ^ n * μHE[n] E :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hφL.mono hE)
      _ = 0 := by rw [hE0, mul_zero]
  -- Step 2: `B = D ∩ ψ⁻¹(S)` is `Lⁿ`-null-measurable.
  have hDc : IsClosed D := hD.isClosed
  have hψtm : Measurable (D.piecewise ψ 0) :=
    ContinuousOn.measurable_piecewise hψL.continuousOn continuous_zero.continuousOn
      hDc.measurableSet
  have hψt_eq : ∀ u ∈ D, D.piecewise ψ 0 u = ψ u := fun u hu ↦ Set.piecewise_eq_of_mem _ _ _ hu
  obtain ⟨S', hS'S, hS'm, hS'ae⟩ := hS.exists_measurable_subset_ae_eq
  have hSS' : μHE[n] (S \ S') = 0 := (ae_eq_set.mp hS'ae).2
  have hBm : NullMeasurableSet B volume := by
    have h1 : MeasurableSet (D ∩ D.piecewise ψ 0 ⁻¹' S') := hDc.measurableSet.inter (hψtm hS'm)
    have h2 : (volume : Measure (Rn n)) (D ∩ ψ ⁻¹' (S \ S')) = 0 :=
      hnullpre _ (Set.sdiff_subset.trans hSD) hSS'
    have heq : B = (D ∩ D.piecewise ψ 0 ⁻¹' S') ∪ (D ∩ ψ ⁻¹' (S \ S')) := by
      ext u
      simp only [hBdef, mem_inter_iff, mem_preimage, mem_union, Set.mem_sdiff]
      constructor
      · rintro ⟨huD, huS⟩
        by_cases hu' : ψ u ∈ S'
        · exact Or.inl ⟨huD, by rw [hψt_eq u huD]; exact hu'⟩
        · exact Or.inr ⟨huD, huS, hu'⟩
      · rintro (⟨huD, hu'⟩ | ⟨huD, huS, -⟩)
        · rw [hψt_eq u huD] at hu'
          exact ⟨huD, hS'S hu'⟩
        · exact ⟨huD, huS⟩
    rw [heq]
    exact h1.nullMeasurableSet.union (NullMeasurableSet.of_null h2)
  -- Step 3: the weights `h ∘ ψ` and `(h · ofReal J) ∘ ψ` are a.e.-measurable on `B`, using
  -- `J ∘ ψ = J(f ∘ ψ) / Jψ` a.e. on `B` and `Jψ > 0` on `D`.
  have hE0 : μHE[n] (S ∩ {x | h x ≠ hh.mk h x}) = 0 := by
    have := (ae_restrict_iff'₀ hS).mp hh.ae_eq_mk
    rw [ae_iff] at this
    refine measure_mono_null (fun x hx ↦ ?_) this
    simp only [Set.mem_ofPred_eq, not_imp]
    exact ⟨hx.1, hx.2⟩
  have hbadh : (volume : Measure (Rn n)) (D ∩ ψ ⁻¹' (S ∩ {x | h x ≠ hh.mk h x})) = 0 :=
    hnullpre _ (inter_subset_left.trans hSD) hE0
  have hhψ : AEMeasurable (fun u ↦ h (ψ u)) (volume.restrict B) := by
    refine ⟨fun u ↦ hh.mk h (D.piecewise ψ 0 u), hh.measurable_mk.comp hψtm, ?_⟩
    refine (ae_restrict_iff'₀ hBm).mpr ?_
    rw [ae_iff]
    refine measure_mono_null (fun u hu ↦ ?_) hbadh
    simp only [Set.mem_ofPred_eq, not_imp] at hu
    obtain ⟨⟨huD, huS⟩, hne⟩ := hu
    rw [hψt_eq u huD] at hne
    exact ⟨huD, huS, hne⟩
  have hJψm : Measurable (fun u ↦ (fderiv ℝ ψ u).toLinearMap.normDet) :=
    (normDet_cont (Rn N)).measurable.comp (measurable_fderiv ℝ ψ)
  have hJgm : Measurable (fun u ↦ (fderiv ℝ (f ∘ ψ) u).toLinearMap.normDet) :=
    (normDet_cont (Rn p)).measurable.comp (measurable_fderiv ℝ (f ∘ ψ))
  have hJψpos : ∀ u ∈ D, 0 < (fderiv ℝ ψ u).toLinearMap.normDet := by
    intro u hu
    refine lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm ?_)
    intro h0
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp h0) (LinearMap.ker_eq_bot.mpr (hinj u hu))
  have hJrel : ∀ᵐ u ∂(volume.restrict B), J (ψ u) * (fderiv ℝ ψ u).toLinearMap.normDet =
      (fderiv ℝ (f ∘ ψ) u).toLinearMap.normDet := by
    refine (ae_restrict_iff'₀ hBm).mpr ?_
    filter_upwards [hJ] with u hu huB
    exact (hu huB.1 huB.2).2
  have hJae : ∀ᵐ u ∂(volume.restrict B), (fderiv ℝ (f ∘ ψ) u).toLinearMap.normDet /
      (fderiv ℝ ψ u).toLinearMap.normDet = J (ψ u) := by
    have hD' : ∀ᵐ u ∂(volume.restrict B), u ∈ B := ae_restrict_mem₀ hBm
    filter_upwards [hJrel, hD'] with u hu huB
    rw [← hu, mul_div_assoc, div_self (hJψpos u huB.1).ne', mul_one]
  have hJψm' : AEMeasurable (fun u ↦ J (ψ u)) (volume.restrict B) :=
    (hJgm.div hJψm).aemeasurable.congr hJae
  have hw : AEMeasurable (fun u ↦ h (ψ u) * ENNReal.ofReal (J (ψ u))) (volume.restrict B) :=
    hhψ.mul (ENNReal.measurable_ofReal.comp_aemeasurable hJψm')
  -- Step 4: the weighted area formula for `ψ` and for `f ∘ ψ` on `B`.
  have A1 := area_mult (Rn N) B ψ K (fun u ↦ h (ψ u) * ENNReal.ofReal (J (ψ u))) hBm (hψL.mono hBD)
    (Eventually.of_forall fun u hu ↦ hdiff u hu.1) hw
  have hdg : ∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ B → DifferentiableAt ℝ (f ∘ ψ) u := by
    filter_upwards [hJ] with u hu huB
    exact (hu huB.1 huB.2).1
  have A2 := area_mult (Rn p) B (f ∘ ψ) K (fun u ↦ h (ψ u)) hBm (hgL.mono hBD) hdg hhψ
  -- Step 5: the fibres of `ψ` in `B` are singletons over `S`, and `ψ` maps the fibres of
  -- `f ∘ ψ` in `B` bijectively onto the fibres of `f` in `S`.
  have hfib1 : ∀ y, (∑' x : ↥(B ∩ ψ ⁻¹' {y}), h (ψ x) * ENNReal.ofReal (J (ψ x))) =
      S.indicator (fun x ↦ h x * ENNReal.ofReal (J x)) y := by
    intro y
    by_cases hy : y ∈ S
    · rw [indicator_of_mem hy]
      obtain ⟨u, huD, rfl⟩ := hSD hy
      exact tsum_eq_single (⟨u, ⟨huD, hy⟩, rfl⟩ : ↥(B ∩ ψ ⁻¹' {ψ u})) fun b hb ↦
        absurd (Subtype.ext (hψinj b.2.1.1 huD (show ψ b.1 = ψ u from b.2.2))) hb
    · rw [indicator_of_notMem hy]
      exact ENNReal.tsum_eq_zero.mpr fun b ↦
        absurd (show y ∈ S by rw [← (show ψ b.1 = y from b.2.2)]; exact b.2.1.2) hy
  have hfib2 : ∀ y, (∑' x : ↥(B ∩ (f ∘ ψ) ⁻¹' {y}), h (ψ x)) =
      ∑' x : ↥(S ∩ f ⁻¹' {y}), h x := by
    intro y
    have hinj' : Function.Injective (fun b : ↥(B ∩ (f ∘ ψ) ⁻¹' {y}) ↦
        (⟨ψ b.1, b.2.1.2, b.2.2⟩ : ↥(S ∩ f ⁻¹' {y}))) := by
      intro b₁ b₂ hb
      exact Subtype.ext (hψinj b₁.2.1.1 b₂.2.1.1 (congrArg Subtype.val hb))
    have hsurj : Function.Surjective (fun b : ↥(B ∩ (f ∘ ψ) ⁻¹' {y}) ↦
        (⟨ψ b.1, b.2.1.2, b.2.2⟩ : ↥(S ∩ f ⁻¹' {y}))) := by
      rintro ⟨x, hxS, hxf⟩
      obtain ⟨u, huD, rfl⟩ := hSD hxS
      exact ⟨⟨u, ⟨huD, hxS⟩, hxf⟩, rfl⟩
    exact (Equiv.ofBijective _ ⟨hinj', hsurj⟩).tsum_eq (fun x : ↥(S ∩ f ⁻¹' {y}) ↦ h x)
  have hfun : (fun y ↦ ∑' x : ↥(S ∩ f ⁻¹' {y}), h x) =
      fun y ↦ ∑' x : ↥(B ∩ (f ∘ ψ) ⁻¹' {y}), h (ψ x) :=
    funext fun y ↦ (hfib2 y).symm
  -- Step 6: chain the two area formulas through the Jacobian identity.
  refine ⟨?_, by rw [hfun]; exact A2.1⟩
  calc ∫⁻ x in S, h x * ENNReal.ofReal (J x) ∂μHE[n]
      = ∫⁻ y, S.indicator (fun x ↦ h x * ENNReal.ofReal (J x)) y ∂μHE[n] :=
        (lintegral_indicator₀ hS _).symm
    _ = ∫⁻ y, ∑' x : ↥(B ∩ ψ ⁻¹' {y}), h (ψ x) * ENNReal.ofReal (J (ψ x)) ∂μHE[n] :=
        lintegral_congr fun y ↦ (hfib1 y).symm
    _ = ∫⁻ u in B, ENNReal.ofReal (fderiv ℝ ψ u).toLinearMap.normDet *
          (h (ψ u) * ENNReal.ofReal (J (ψ u))) := A1.2
    _ = ∫⁻ u in B, ENNReal.ofReal (fderiv ℝ (f ∘ ψ) u).toLinearMap.normDet * h (ψ u) := by
        apply lintegral_congr_ae
        filter_upwards [hJrel] with u h3
        rw [← h3, mul_comm (J (ψ u)), ENNReal.ofReal_mul (LinearMap.normDet_nonneg _)]
        ring
    _ = ∫⁻ y, ∑' x : ↥(B ∩ (f ∘ ψ) ⁻¹' {y}), h (ψ x) ∂μHE[n] := A2.2.symm
    _ = ∫⁻ y, ∑' x : ↥(S ∩ f ⁻¹' {y}), h x ∂μHE[n] := lintegral_congr hfib2
/-- **Gluing fibre-sum area identities over a countable cover** (Simon Ch. 3, proof of the area
formula (2.4)–(2.5), pp. 76–77: summation over the pieces, using that the image of the uncovered
part is null), for abstract measure spaces. Write `F_S(y) = ∑_{x ∈ S ∩ f⁻¹{y}} h(x)`. Let `M` and
every `G_α` be `μ`-null-measurable with `μ(M ∖ ⋃ G_α) = 0` and `ν(f(M ∖ ⋃ G_α)) = 0`, and assume
that `∫_S g dμ = ∫ F_S dν`, with `F_S` `ν`-a.e. measurable, for every `μ`-null-measurable
`S ⊆ M ∩ G_α`. Then `∫_M g dμ = ∫ F_M dν`. The pieces `S_α = M ∩ disjointed G α` are disjoint and
null-measurable with union `M ∩ ⋃ G_α`, which is `μ`-a.e. equal to `M`; so the left side is
`∑_α ∫_{S_α} g dμ = ∑_α ∫ F_{S_α} dν = ∫ ∑_α F_{S_α} dν` (monotone convergence). For `y` outside
the `ν`-null set `f(M ∖ ⋃ G_α)`, the fibres `S_α ∩ f⁻¹{y}` partition `M ∩ f⁻¹{y}`, so
`∑_α F_{S_α}(y) = F_M(y)`. -/
theorem Submission.areaFormula_glue_pieces : ∀ (X Y : Type) [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) (f : X → Y) (g h : X → ℝ≥0∞) (M : Set X)
    (G : ℕ → Set X), NullMeasurableSet M μ → (∀ α, NullMeasurableSet (G α) μ) →
    μ (M \ ⋃ α, G α) = 0 → ν (f '' (M \ ⋃ α, G α)) = 0 →
    (∀ α, ∀ S ⊆ M ∩ G α, NullMeasurableSet S μ →
      (∫⁻ x in S, g x ∂μ = ∫⁻ y, ∑' x : ↥(S ∩ f ⁻¹' {y}), h x ∂ν) ∧
        AEMeasurable (fun y ↦ ∑' x : ↥(S ∩ f ⁻¹' {y}), h x) ν) →
    ∫⁻ x in M, g x ∂μ = ∫⁻ y, ∑' x : ↥(M ∩ f ⁻¹' {y}), h x ∂ν := by
  intro X Y _ _ μ ν f g h M G hM hG hnull himnull H
  -- Disjoint null-measurable pieces `S α = M ∩ disjointed G α ⊆ M ∩ G α` with union `M ∩ ⋃ G`.
  let S : ℕ → Set X := fun α ↦ M ∩ disjointed G α
  have hSsub : ∀ α, S α ⊆ M ∩ G α := fun α x hx ↦ ⟨hx.1, disjointed_subset G α hx.2⟩
  have hSmeas : ∀ α, NullMeasurableSet (S α) μ := fun α ↦
    hM.inter (NullMeasurableSet.disjointed hG α)
  have hSdisj : Pairwise (Function.onFun Disjoint S) := fun a b hab ↦
    (show Disjoint (disjointed G a) (disjointed G b) from disjoint_disjointed G hab).mono
      inter_subset_right inter_subset_right
  have hSU : ⋃ α, S α = M ∩ ⋃ α, G α := by
    show ⋃ α, (M ∩ disjointed G α) = M ∩ ⋃ α, G α
    rw [← inter_iUnion, iUnion_disjointed]
  -- Source side: `M ∩ ⋃ G` is `μ`-a.e. equal to `M`.
  have hMae : M ∩ ⋃ α, G α =ᵐ[μ] M := by
    rw [ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [sdiff_eq_empty.mpr inter_subset_left, measure_empty]
    · exact measure_mono_null (show M \ (M ∩ ⋃ α, G α) ⊆ M \ ⋃ α, G α from
        fun x hx ↦ ⟨hx.1, fun hG' ↦ hx.2 ⟨hx.1, hG'⟩⟩) hnull
  -- Target side: off the `ν`-null set `f(M ∖ ⋃ G)`, the fibre sums over the pieces regroup to
  -- the fibre sum over `M`.
  have hE : ∀ᵐ y ∂ν,
      ∑' α, ∑' x : ↥(S α ∩ f ⁻¹' {y}), h x = ∑' x : ↥(M ∩ f ⁻¹' {y}), h x := by
    rw [ae_iff]
    refine measure_mono_null (fun y hy ↦ ?_) himnull
    rw [mem_ofPred_eq] at hy
    by_contra hy'
    apply hy
    have hset : ⋃ α, (S α ∩ f ⁻¹' {y}) = M ∩ f ⁻¹' {y} := by
      rw [← iUnion_inter, hSU]
      ext x
      simp only [mem_inter_iff, mem_iUnion, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨⟨hxM, _⟩, hfx⟩
        exact ⟨hxM, hfx⟩
      · rintro ⟨hxM, hfx⟩
        refine ⟨⟨hxM, ?_⟩, hfx⟩
        by_contra hxG
        exact hy' ⟨x, ⟨hxM, by simpa [mem_iUnion] using hxG⟩, hfx⟩
    have hdisj : (Set.univ : Set ℕ).PairwiseDisjoint (fun α ↦ S α ∩ f ⁻¹' {y}) := by
      intro a _ b _ hab
      exact (show Disjoint (S a) (S b) from hSdisj hab).mono inter_subset_left inter_subset_left
    rw [← ENNReal.tsum_biUnion hdisj, hset]
  calc ∫⁻ x in M, g x ∂μ = ∫⁻ x in ⋃ α, S α, g x ∂μ := by
        rw [hSU, Measure.restrict_congr_set hMae]
    _ = ∑' α, ∫⁻ x in S α, g x ∂μ := lintegral_iUnion₀ hSmeas hSdisj.aedisjoint g
    _ = ∑' α, ∫⁻ y, ∑' x : ↥(S α ∩ f ⁻¹' {y}), h x ∂ν :=
        tsum_congr fun α ↦ (H α (S α) (hSsub α) (hSmeas α)).1
    _ = ∫⁻ y, ∑' α, ∑' x : ↥(S α ∩ f ⁻¹' {y}), h x ∂ν :=
        (lintegral_tsum fun α ↦ (H α (S α) (hSsub α) (hSmeas α)).2).symm
    _ = ∫⁻ y, ∑' x : ↥(M ∩ f ⁻¹' {y}), h x ∂ν := lintegral_congr_ae hE
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

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

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

end GMT.Ch03
