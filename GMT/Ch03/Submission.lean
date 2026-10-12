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

/-- **Simon Ch. 3, Lemma 3.2 (p. 78)** (`chapter-03.txt` lines 449–469). The pieces `Aⱼ` of
`A = ⋃ⱼ Aⱼ` cover `A` with `Hⁿ(Aⱼ) < ∞`, so SimonGMT's `simon_lemma_3_2` applies with `S := Aj`.
Its first part is the decomposition; its Borel-choice part also gives `NullMeasurableSet P`,
which is dropped. -/
theorem Submission.section3_rectifiableDecomposition : RectifiableDecomposition := by
  rintro n ℓ A ⟨Aj, hA, hfin⟩
  obtain ⟨hdecomp, hborel⟩ := Poincare.SimonGMT.Chapter03.simon_lemma_3_2 Aj hA.subset hfin
  refine ⟨hdecomp, fun hAmeas ↦ ?_⟩
  obtain ⟨R, P, hRP, hdisj, hR, -, hRrect, hPpure⟩ := hborel hAmeas
  exact ⟨R, P, hRP, hdisj, hR, hRrect, hPpure⟩
/-- **`C¹` maps send `Lⁿ`-null sets to `Hⁿ`-null sets**: the measure step in Simon Ch. 3,
proof of Lemma 3.3 (p. 79, `chapter-03.txt` lines 495–496: a `C¹` diffeomorphism `p` gives
`Hⁿ(p(S ∩ N ∩ B_σ(x))) > 0`). Each `u ∈ T ⊆ V` has a neighbourhood `t` on which `ψ` is
`K`-Lipschitz, since `ψ` is `C¹` near `u` and hence strictly differentiable at `u`. As
`Hⁿ = c • μH[n]` with one constant `c` on every space and `Hⁿ = Lⁿ` on `ℝⁿ`,
`Hⁿ(ψ(T ∩ t)) ≤ Kⁿ Hⁿ(T ∩ t) = Kⁿ Lⁿ(T ∩ t) = 0`. By second countability
(`measure_null_of_locally_null` for the outer measure `B ↦ Hⁿ(ψ(B))`), `Hⁿ(ψ(T)) = 0`. -/
theorem Submission.section3_contDiffOn_image_null_of_volume_null : ∀ (n N : ℕ) (V T : Set (Rn n))
    (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 1 ψ V → T ⊆ V → volume T = 0 →
    μHE[n] (ψ '' T) = 0 := by
  intro n N V T ψ hV hψ hTV hT
  -- `B ↦ Hⁿ(ψ(B))` is an outer measure on `ℝⁿ`; it suffices that it vanishes on a relative
  -- neighbourhood of each point of `T`.
  suffices h : OuterMeasure.comap ψ (μHE[n] : Measure (Rn N)).toOuterMeasure T = 0 by
    simpa using h
  refine measure_null_of_locally_null T fun u hu ↦ ?_
  obtain ⟨K, t, ht, hK⟩ :=
    ((hψ.contDiffAt (hV.mem_nhds (hTV hu))).hasStrictFDerivAt one_ne_zero).exists_lipschitzOnWith
  refine ⟨T ∩ t, inter_mem_nhdsWithin T ht, ?_⟩
  have hvol : (μHE[n] : Measure (Rn n)) (T ∩ t) = 0 := by
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact measure_mono_null inter_subset_left hT
  -- `μHE[n] = c • μH[n]` with the same constant `c` on `ℝⁿ` and on `ℝᴺ`.
  have himg : (μHE[n] : Measure (Rn N)) (ψ '' (T ∩ t)) ≤
      (K : ℝ≥0∞) ^ (n : ℝ) * (μHE[n] : Measure (Rn n)) (T ∩ t) := by
    simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul]
    rw [mul_left_comm]
    gcongr
    exact (hK.mono inter_subset_right).hausdorffMeasure_image_le (Nat.cast_nonneg n)
  rw [hvol, mul_zero] at himg
  simpa using himg
/-- **An injective strict derivative gives a local anti-Lipschitz bound**: the local step of
Simon Ch. 3, proof of Lemma 3.3 (p. 79, `chapter-03.txt` lines 494–496: `p_J` restricted to `N`
near `x` is a `C¹` diffeomorphism), with strict differentiability in place of the inverse function
theorem. As `A` is injective on `ℝⁿ`, `‖v‖ ≤ K₀ ‖A v‖` for some `K₀ > 0`. Near `u₀`,
`‖Φ x - Φ y - A (x - y)‖ ≤ (2K₀)⁻¹ ‖x - y‖`, so the triangle inequality gives
`‖x - y‖ ≤ K₀ ‖Φ x - Φ y‖ + ‖x - y‖ / 2`, i.e. `‖x - y‖ ≤ 2K₀ ‖Φ x - Φ y‖`. -/
theorem Submission.section3_hasStrictFDerivAt_injective_local_antilipschitz : ∀ (n p : ℕ)
    (Φ : Rn n → Rn p) (A : Rn n →L[ℝ] Rn p) (u₀ : Rn n), HasStrictFDerivAt Φ A u₀ →
    Function.Injective A → ∃ s ∈ 𝓝 u₀, ∃ K : ℝ≥0, ∀ x ∈ s, ∀ y ∈ s,
      ‖x - y‖ ≤ K * ‖Φ x - Φ y‖ := by
  intro n p Φ A u₀ hΦ hA
  -- Step 1: `A` is injective on a finite-dimensional space, so `‖v‖ ≤ K₀ ‖A v‖` with `K₀ > 0`.
  obtain ⟨K₀, hK₀, hAK₀⟩ :=
    LinearMap.exists_antilipschitzWith (A : Rn n →ₗ[ℝ] Rn p) (LinearMap.ker_eq_bot.mpr hA)
  have hK₀' : (0 : ℝ) < K₀ := hK₀
  have h1 (v : Rn n) : ‖v‖ ≤ K₀ * ‖A v‖ := by
    simpa [dist_eq_norm] using hAK₀.le_mul_dist v 0
  -- Step 2: on a neighbourhood `s` of `u₀`, `Φ` approximates `A` with constant `(2K₀)⁻¹`.
  obtain ⟨s, hs, hΦs⟩ := hΦ.approximates_deriv_on_nhds (c := (2 * K₀)⁻¹) (Or.inr (by positivity))
  refine ⟨s, hs, 2 * K₀, fun x hx y hy ↦ ?_⟩
  have h2 : ‖Φ x - Φ y - A (x - y)‖ ≤ (2 * K₀ : ℝ)⁻¹ * ‖x - y‖ := by
    exact_mod_cast hΦs x hx y hy
  -- Step 3: the triangle inequality for `A (x - y) = (Φ x - Φ y) - (Φ x - Φ y - A (x - y))`.
  have h3 : ‖A (x - y)‖ ≤ ‖Φ x - Φ y‖ + ‖Φ x - Φ y - A (x - y)‖ := by
    calc ‖A (x - y)‖ = ‖(Φ x - Φ y) - (Φ x - Φ y - A (x - y))‖ := by rw [sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
  -- Steps 4–5: since `K₀ (2K₀)⁻¹ = 1 / 2`, half of `‖x - y‖` is absorbed into the left side.
  have h4 : ‖x - y‖ ≤ K₀ * ‖Φ x - Φ y‖ + ‖x - y‖ / 2 :=
    calc ‖x - y‖ ≤ K₀ * ‖A (x - y)‖ := h1 (x - y)
      _ ≤ K₀ * (‖Φ x - Φ y‖ + (2 * K₀ : ℝ)⁻¹ * ‖x - y‖) := by gcongr; linarith
      _ = K₀ * ‖Φ x - Φ y‖ + ‖x - y‖ / 2 := by field_simp
  push_cast
  linarith
/-- **Anti-Lipschitz maps on subsets of `ℝⁿ` satisfy `Lⁿ(S) ≤ Kⁿ Hⁿ(f(S))`**: step 7 of the
proof of Simon Ch. 3, Lemma 3.3 (p. 79), stated for an arbitrary map `f` and set `S`. The
restriction `g = f|_S` is `K`-anti-Lipschitz on the metric subspace `S`, so
`μH[n]_S(S) ≤ Kⁿ μH[n](g(S)) = Kⁿ μH[n](f(S))`; the isometric inclusion `S ↪ ℝⁿ` gives
`μH[n](S) = μH[n]_S(S)`. Multiplying by the normalising constant of `μHE[n]` and using
`μHE[n] = Lⁿ` on `ℝⁿ` gives the claim. No measurability of `S` or `f` is needed: all estimates
are for outer measures. -/
theorem Submission.section3_antilipschitzOn_volume_le_euclideanHausdorff_image : ∀ (n p : ℕ)
    (f : Rn n → Rn p) (S : Set (Rn n)) (K : ℝ≥0),
    (∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ K * ‖f x - f y‖) →
    volume S ≤ (K : ℝ≥0∞) ^ n * μHE[n] (f '' S) := by
  intro n p f S K hf
  -- Step 2: the restriction `g = f|_S` is `K`-anti-Lipschitz on the metric subspace `S`.
  have hg : AntilipschitzWith K (S.domRestrict f) :=
    AntilipschitzWith.of_le_mul_dist fun a b => by
      simpa only [Subtype.dist_eq, dist_eq_norm, domRestrict_apply] using hf a a.2 b b.2
  -- Step 3: `μH[n]_S(S) ≤ Kⁿ μH[n](g(S))`, and `g(S) = f(S)`.
  have h3 := hg.le_hausdorffMeasure_image (Nat.cast_nonneg n) univ
  rw [image_univ, range_domRestrict, ENNReal.rpow_natCast] at h3
  -- Step 4: the isometric inclusion `S ↪ ℝⁿ` gives `μH[n](S) = μH[n]_S(S)`.
  have h4 := isometry_subtype_coe.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg n))
    (univ : Set S)
  rw [image_univ, Subtype.range_coe] at h4
  -- Steps 5–6: multiply by the normalising constant of `μHE[n]`, and `μHE[n] = Lⁿ` on `ℝⁿ`.
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.euclideanHausdorffMeasure_def,
    Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply, h4,
    ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_left_comm]
  gcongr
/-- **Simon Ch. 3, proof of Lemma 3.3, first claim (pp. 78–79)** (`chapter-03.txt` lines
482–489). An `n`-plane `L ⊆ ℝᴺ` has `n` coordinates `J` with `p_J` injective on `L`. The
restricted coordinate functionals `φⱼ = xⱼ|_L` span `L*`, since a nonzero `x ∈ L` has a nonzero
coordinate. So `n` of them, `φ_{j(1)}, …, φ_{j(n)}`, form a basis of `L*`, and their indices are
distinct; an `x ∈ L` with every `x_{j(i)} = 0` is then `0`. As `x - p_J x ⊥ e_j` for `j ∈ J`,
`p_J` keeps the coordinates in `J`, so `J = {j(1), …, j(n)}` works. This is the dual form of
Simon's nonsingular `n × n` minor. -/
theorem Submission.section3_exists_coordinateProjection_injOn :
    ∀ (N n : ℕ) (L : Submodule ℝ (Rn N)), finrank ℝ L = n →
      ∃ J : Finset (Fin N), J.card = n ∧ Set.InjOn (coordinateProjection J) (L : Set (Rn N)) := by
  intro N n L hL
  -- Step 1: `p_J` keeps the coordinates indexed by `J`, as `x - p_J x ⊥ e_i` for `i ∈ J`.
  have hcoord : ∀ (J : Finset (Fin N)) (x : Rn N), ∀ i ∈ J, coordinateProjection J x i = x i := by
    intro J x i hi
    have hmem : EuclideanSpace.single i (1 : ℝ) ∈
        Submodule.span ℝ ((fun j ↦ EuclideanSpace.single j (1 : ℝ)) '' (J : Set (Fin N))) :=
      Submodule.subset_span ⟨i, hi, rfl⟩
    have h := Submodule.starProjection_inner_eq_zero x _ hmem
    rw [inner_sub_left, EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_right,
      one_mul, one_mul, conj_trivial, conj_trivial, sub_eq_zero] at h
    exact h.symm
  -- Step 2: the coordinate functionals `φⱼ` restricted to `L` span `L*`.
  let φ : Fin N → Module.Dual ℝ L := fun j ↦ (EuclideanSpace.projₗ j).comp L.subtype
  have hspan : Submodule.span ℝ (Set.range φ) = ⊤ := by
    refine Submodule.span_eq_top_of_ne_zero fun z hz ↦ ?_
    obtain ⟨j, hj⟩ : ∃ j, (z : Rn N) j ≠ 0 := by
      by_contra! h
      exact hz (Subtype.ext (PiLp.ext h))
    exact ⟨φ j, Set.mem_range_self j, hj⟩
  -- Step 3: `n` of them, `φ_{j(1)}, …, φ_{j(n)}`, form a basis of `L*`; the `j(i)` are distinct.
  obtain ⟨f, hf_mem, hf_span, hf_indep⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range φ)
  choose j hj using hf_mem
  have hj_inj : Function.Injective j := fun a b hab ↦
    hf_indep.injective (by rw [← hj a, ← hj b, hab])
  have hcard : finrank ℝ (Submodule.span ℝ (Set.range φ)) = n := by
    rw [hspan, finrank_top, Subspace.dual_finrank_eq, hL]
  -- Step 4: a vector of `L` whose selected coordinates vanish is `0`.
  have hzero : ∀ z : L, (∀ i, (z : Rn N) (j i) = 0) → z = 0 := by
    intro z hz
    refine (Module.forall_dual_apply_eq_zero_iff ℝ z).mp fun g ↦ ?_
    have hle : Submodule.span ℝ (Set.range f) ≤ LinearMap.ker (Module.Dual.eval ℝ L z) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply, ← hj i]
      exact hz i
    have hg : g ∈ Submodule.span ℝ (Set.range f) := by
      rw [hf_span, hspan]
      exact Submodule.mem_top
    simpa using hle hg
  -- Step 5: `J = {j(1), …, j(n)}` has `n` elements and `p_J` is injective on `L`.
  refine ⟨Finset.univ.image j, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hj_inj, Finset.card_univ, Fintype.card_fin, hcard]
  · intro x hx y hy hxy
    have hsel : ∀ i, (x - y) (j i) = 0 := fun i ↦ by
      have hi : j i ∈ Finset.univ.image j := Finset.mem_image_of_mem j (Finset.mem_univ i)
      rw [PiLp.sub_apply, ← hcoord _ x (j i) hi, ← hcoord _ y (j i) hi, hxy, sub_self]
    exact sub_eq_zero.mp (congrArg Subtype.val (hzero ⟨x - y, L.sub_mem hx hy⟩ hsel))
/-- **`C¹` maps send `Lⁿ`-null sets to `Hⁿ`-null sets**: the measure step in Simon Ch. 3,
proof of Lemma 3.3 (p. 79, `chapter-03.txt` lines 495–496: a `C¹` diffeomorphism `p` gives
`Hⁿ(p(S ∩ N ∩ B_σ(x))) > 0`). Each `u ∈ T ⊆ V` has a neighbourhood `t` on which `ψ` is
`K`-Lipschitz, since `ψ` is `C¹` near `u` and hence strictly differentiable at `u`. As
`Hⁿ = c • μH[n]` with one constant `c` on every space and `Hⁿ = Lⁿ` on `ℝⁿ`,
`Hⁿ(ψ(T ∩ t)) ≤ Kⁿ Hⁿ(T ∩ t) = Kⁿ Lⁿ(T ∩ t) = 0`. By second countability
(`measure_null_of_locally_null` for the outer measure `B ↦ Hⁿ(ψ(B))`), `Hⁿ(ψ(T)) = 0`. -/
theorem Submission.section3_contDiffOn_image_null_of_volume_null : ∀ (n N : ℕ) (V T : Set (Rn n))
    (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 1 ψ V → T ⊆ V → volume T = 0 →
    μHE[n] (ψ '' T) = 0 := by
  intro n N V T ψ hV hψ hTV hT
  -- `B ↦ Hⁿ(ψ(B))` is an outer measure on `ℝⁿ`; it suffices that it vanishes on a relative
  -- neighbourhood of each point of `T`.
  suffices h : OuterMeasure.comap ψ (μHE[n] : Measure (Rn N)).toOuterMeasure T = 0 by
    simpa using h
  refine measure_null_of_locally_null T fun u hu ↦ ?_
  obtain ⟨K, t, ht, hK⟩ :=
    ((hψ.contDiffAt (hV.mem_nhds (hTV hu))).hasStrictFDerivAt one_ne_zero).exists_lipschitzOnWith
  refine ⟨T ∩ t, inter_mem_nhdsWithin T ht, ?_⟩
  have hvol : (μHE[n] : Measure (Rn n)) (T ∩ t) = 0 := by
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact measure_mono_null inter_subset_left hT
  -- `μHE[n] = c • μH[n]` with the same constant `c` on `ℝⁿ` and on `ℝᴺ`.
  have himg : (μHE[n] : Measure (Rn N)) (ψ '' (T ∩ t)) ≤
      (K : ℝ≥0∞) ^ (n : ℝ) * (μHE[n] : Measure (Rn n)) (T ∩ t) := by
    simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul]
    rw [mul_left_comm]
    gcongr
    exact (hK.mono inter_subset_right).hausdorffMeasure_image_le (Nat.cast_nonneg n)
  rw [hvol, mul_zero] at himg
  simpa using himg

/-- **Simon Ch. 3, proof of Lemma 3.3, positivity step (p. 79)** (`chapter-03.txt` lines
490–496). If `ψ` is `C¹` on an open `V ⊆ ℝⁿ` with `Dψ` injective and `T ⊆ V` has `Lⁿ(T) > 0`,
then `Hⁿ(p_J(ψ(T))) > 0` for some `J` with `#J = n`. Every neighbourhood of some `u₀ ∈ T` meets
`T` in positive measure. Choose `J` with `p_J` injective on the `n`-plane `Dψ(u₀)(ℝⁿ)`, so that
`A = p_J ∘ Dψ(u₀)` is injective. Then `Φ = p_J ∘ ψ` has strict derivative `A` at `u₀`, so it is
`K`-anti-Lipschitz on a neighbourhood `s` of `u₀`. Hence `0 < Lⁿ(T ∩ s) ≤ Kⁿ Hⁿ(Φ(T ∩ s))`, and
`Φ(T ∩ s) ⊆ p_J(ψ(T))`. Strict differentiability replaces Simon's local `C¹` diffeomorphism
(Ch. 2, Remark 4.4). -/
theorem Submission.section3_chart_coordinateProjection_pos :
    ∀ (n ℓ : ℕ) (V T : Set (Rn n)) (ψ : Rn n → Rn (n + ℓ)), IsOpen V → ContDiffOn ℝ 1 ψ V →
      (∀ u ∈ V, Function.Injective (fderiv ℝ ψ u)) → T ⊆ V → 0 < volume T →
        ∃ J : Finset (Fin (n + ℓ)), J.card = n ∧
          0 < μHE[n] (coordinateProjection J '' (ψ '' T)) := by
  intro n ℓ V T ψ hV hψ hDψ hTV hT
  -- Step 1: every neighbourhood of some `u₀ ∈ T` meets `T` in positive measure.
  obtain ⟨u₀, hu₀, hdens⟩ := exists_mem_forall_mem_nhdsWithin_pos_measure hT.ne'
  -- Step 2: `p_J` is injective on the `n`-plane `Dψ(u₀)(ℝⁿ)`, so `A = p_J ∘ Dψ(u₀)` is injective.
  set D := fderiv ℝ ψ u₀
  have hD : Function.Injective D := hDψ u₀ (hTV hu₀)
  obtain ⟨J, hJ, hJinj⟩ := Submission.section3_exists_coordinateProjection_injOn (n + ℓ) n
    (LinearMap.range (D : Rn n →ₗ[ℝ] Rn (n + ℓ)))
    (by rw [LinearMap.finrank_range_of_inj (f := (D : Rn n →ₗ[ℝ] Rn (n + ℓ))) hD,
      finrank_euclideanSpace_fin])
  set A := (coordinateProjection J).comp D
  have hA : Function.Injective A := fun v w hvw ↦
    hD (hJinj (LinearMap.mem_range_self _ v) (LinearMap.mem_range_self _ w) hvw)
  -- Step 3: `Φ = p_J ∘ ψ` is strictly differentiable at `u₀` with derivative `A`.
  have hΦ : HasStrictFDerivAt (coordinateProjection J ∘ ψ) A u₀ :=
    (coordinateProjection J).hasStrictFDerivAt.comp u₀
      ((hψ.contDiffAt (hV.mem_nhds (hTV hu₀))).hasStrictFDerivAt one_ne_zero)
  -- Step 4: `Φ` is `K`-anti-Lipschitz on a neighbourhood `s` of `u₀`.
  obtain ⟨s, hs, K, hK⟩ := Submission.section3_hasStrictFDerivAt_injective_local_antilipschitz
    n (n + ℓ) (coordinateProjection J ∘ ψ) A u₀ hΦ hA
  -- Step 5: `0 < Lⁿ(T ∩ s) ≤ Kⁿ Hⁿ(Φ(T ∩ s))`, so `Hⁿ(Φ(T ∩ s)) ≠ 0`.
  have hbound := Submission.section3_antilipschitzOn_volume_le_euclideanHausdorff_image
    n (n + ℓ) (coordinateProjection J ∘ ψ) (T ∩ s) K fun x hx y hy ↦ hK x hx.2 y hy.2
  have himage : μHE[n] ((coordinateProjection J ∘ ψ) '' (T ∩ s)) ≠ 0 := fun h ↦ by
    rw [h, mul_zero] at hbound
    exact (hdens _ (inter_mem_nhdsWithin T hs)).ne' (nonpos_iff_eq_zero.mp hbound)
  -- Step 6: `Φ(T ∩ s) ⊆ p_J(ψ(T))`, and `Hⁿ` is monotone.
  refine ⟨J, hJ, (pos_iff_ne_zero.mpr himage).trans_le (measure_mono ?_)⟩
  rw [Set.image_comp]
  exact Set.image_mono (Set.image_mono Set.inter_subset_left)

/-- **Simon Ch. 3, Theorem 3.8 (p. 80)** (`chapter-03.txt` lines 540–548), given Theorem 3.6.
Erratum: line 540 "by combining 3.2 and 3.7" should read "3.2 and 3.6". Lemma 3.2 splits
`A = R ∪ P` with `R` countably `n`-rectifiable and `P` purely `n`-unrectifiable. Since
`P = ⋃ⱼ (P ∩ Aⱼ)` with `Hⁿ(P ∩ Aⱼ) ≤ Hⁿ(Aⱼ) < ∞`, Theorem 3.6 makes `Hⁿ(p(P)) = 0` for almost all
`p`, so the hypothesis with `B := P` forces `Hⁿ(P) = 0`. Adding `P` to the null exceptional set
of a Lipschitz cover of `R` shows that `A` is countably `n`-rectifiable. -/
theorem Submission.section3_rectifiabilityTheorem_of_besicovitchFederer :
    BesicovitchFedererProjectionTheorem → RectifiabilityTheoremForSets := by
  rintro hBF n ℓ A ⟨Aj, hAeq, hAj⟩ hpos
  obtain ⟨R, P, hRP, -, hR, hP⟩ :=
    (Submission.section3_rectifiableDecomposition n ℓ A ⟨Aj, hAeq, hAj⟩).1
  have hPA : P ⊆ A := hRP ▸ subset_union_right
  have hPproj : ForAlmostAllProjections (n + ℓ) n (fun p ↦ μHE[n] (p '' P) = 0) := by
    refine hBF n ℓ P hP ⟨fun j ↦ P ∩ Aj j, ?_, fun j ↦ ?_⟩
    · rw [← inter_iUnion, ← hAeq, inter_eq_left.mpr hPA]
    · exact (measure_mono inter_subset_right).trans_lt (hAj j)
  have hP0 : μHE[n] P = 0 := by
    by_contra hne
    exact hpos P hPA (pos_iff_ne_zero.mpr hne) hPproj
  obtain ⟨M₀, hM₀, F, hF, hRcover⟩ := hR
  refine ⟨M₀ ∪ P, measure_union_null hM₀ hP0, F, hF, ?_⟩
  calc A = R ∪ P := hRP
    _ ⊆ (M₀ ∪ ⋃ j, range (F j)) ∪ P := union_subset_union_left P hRcover
    _ = M₀ ∪ P ∪ ⋃ j, range (F j) := union_right_comm _ _ _
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

/-- **Simon Ch. 3, Lemma 3.3 (pp. 78–79), given Lemma 1.2** (`chapter-03.txt` lines 476–496).
Let `R ⊆ S` be countably `n`-rectifiable. Lemma 1.2 ("⇒") gives `R ⊆ N₀ ∪ ⋃ⱼ Nⱼ` with
`Hⁿ(N₀) = 0` and `Nⱼ` embedded `C¹` submanifolds, so it suffices that each `R ∩ Nⱼ` is
`Hⁿ`-null, and by Lindelöf (`measure_null_of_locally_null`) that `R ∩ Nⱼ ∩ W` is `Hⁿ`-null for
the chart `ψ : V → W` of `Nⱼ` at each of its points. There `R ∩ Nⱼ ∩ W = ψ(T)` with
`T = V ∩ ψ⁻¹(R)`. If `Lⁿ(T) = 0`, then `Hⁿ(ψ(T)) = 0` (`C¹` images of null sets). Otherwise
some `p_J` with `#J = n` has `Hⁿ(p_J(ψ(T))) > 0` (`p_J ∘ ψ` is anti-Lipschitz near a density
point of `T`), contradicting `Hⁿ(p_J(S)) = 0` as `ψ(T) ⊆ R ⊆ S`. -/
theorem Submission.section3_coordinateProjectionCriterion_of_submanifoldCover :
    SubmanifoldCoverCharacterization → CoordinateProjectionCriterion := by
  intro hcover n ℓ S hS R hRS hR
  obtain ⟨N₀, N, hN₀, hN, hRN⟩ := (hcover n ℓ R).1 hR
  have hRN_null : ∀ j, μHE[n] (R ∩ N j) = 0 := by
    intro j
    refine measure_null_of_locally_null _ fun x hx ↦ ?_
    -- The chart of `N j` at `x`; injectivity and properness of `ψ` are not needed.
    obtain ⟨V, W, ψ, hV, hW, hxW, hψ, -, himage, -, hD⟩ := hN j x hx.2
    refine ⟨R ∩ N j ∩ W, inter_mem_nhdsWithin _ (hW.mem_nhds hxW), ?_⟩
    have hTV : V ∩ ψ ⁻¹' R ⊆ V := inter_subset_left
    have hsub : R ∩ N j ∩ W ⊆ ψ '' (V ∩ ψ ⁻¹' R) := by
      rw [image_inter_preimage, himage]
      exact fun z hz ↦ ⟨⟨hz.2, hz.1.2⟩, hz.1.1⟩
    refine measure_mono_null hsub ?_
    by_cases hT : volume (V ∩ ψ ⁻¹' R) = 0
    · exact Submission.section3_contDiffOn_image_null_of_volume_null n (n + ℓ) V
        (V ∩ ψ ⁻¹' R) ψ hV hψ hTV hT
    · obtain ⟨J, hJ, hpos⟩ := Submission.section3_chart_coordinateProjection_pos n ℓ V
        (V ∩ ψ ⁻¹' R) ψ hV hψ hD hTV (pos_iff_ne_zero.2 hT)
      have hψS : ψ '' (V ∩ ψ ⁻¹' R) ⊆ S := (image_subset_iff.2 inter_subset_right).trans hRS
      exact absurd (measure_mono_null (image_mono hψS) (hS J hJ)) hpos.ne'
  have hnull : μHE[n] (N₀ ∪ ⋃ j, R ∩ N j) = 0 :=
    measure_union_null hN₀ (measure_iUnion_null hRN_null)
  refine measure_mono_null (fun x hx ↦ ?_) hnull
  rcases hRN hx with h | h
  · exact Or.inl h
  · obtain ⟨j, hj⟩ := mem_iUnion.1 h
    exact Or.inr (mem_iUnion.2 ⟨j, hx, hj⟩)
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
