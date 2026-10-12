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

/-- **Carathéodory-measurable fields have Borel a.e.-versions** (Step 6 of the proof of the
Riesz representation on open sets, after Simon Ch. 1, Thm. 4.14): let `X` be Hausdorff, locally
compact and `σ`-compact with its Borel `σ`-algebra, and `μ` a measure on `X` finite on compact
sets. If `ν : X → ℝᴺ` is measurable for the Carathéodory `σ`-algebra of the outer measure `μ*`,
then `ν` agrees `μ`-a.e. with a Borel (strongly measurable) map. Since `μ` is `σ`-finite, every
Carathéodory set `A` is the countable union of the Carathéodory sets `A ∩ Sₙ` of finite measure;
the Carathéodory identity for `A ∩ Sₙ` tested on its measurable hull makes the hull exceed it by a
null set, so `A` is `μ`-null-measurable. Hence `ν` is null-measurable, and as the Borel
`σ`-algebra of `ℝᴺ` is countably generated, `ν` is `μ`-a.e. measurable. -/
theorem Submission.gaussGreenRep_riesz_caratheodory_borel_version : ∀ (X : Type)
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SigmaCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (N : ℕ) (ν : X → Rn N),
    (∀ K : Set X, IsCompact K → μ K < ∞) → Measurable[μ.toOuterMeasure.caratheodory] ν →
    ∃ ν' : X → Rn N, StronglyMeasurable ν' ∧ ν =ᵐ[μ] ν' := by
  intro X _ _ _ _ _ _ μ N ν hμ hν
  -- Step 2: `μ` is finite on compact sets, hence `σ`-finite on the `σ`-compact space `X`; its
  -- spanning sets `Sₙ` are measurable, of finite measure, and cover `X`.
  have : IsFiniteMeasureOnCompacts μ := ⟨hμ⟩
  -- Step 3: every Carathéodory-measurable set is `μ`-null-measurable.
  have hnull : ∀ A : Set X, MeasurableSet[μ.toOuterMeasure.caratheodory] A →
      NullMeasurableSet A μ := by
    intro A hA
    have hpiece : ∀ n, NullMeasurableSet (A ∩ spanningSets μ n) μ := by
      intro n
      set B := A ∩ spanningSets μ n
      -- `B` is Carathéodory measurable (Borel sets are) and has finite measure.
      have hB : MeasurableSet[μ.toOuterMeasure.caratheodory] B :=
        hA.inter (le_toOuterMeasure_caratheodory μ _ (measurableSet_spanningSets μ n))
      have hBfin : μ B ≠ ∞ :=
        ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne
      -- The Carathéodory identity for `B` tested on its measurable hull `H ⊇ B`, `μ H = μ B`,
      -- gives `μ B = μ B + μ (H \ B)`, so `μ (H \ B) = 0`.
      have hcar : μ (toMeasurable μ B) =
          μ (toMeasurable μ B ∩ B) + μ (toMeasurable μ B \ B) :=
        (OuterMeasure.isCaratheodory_iff _).1 hB _
      rw [inter_eq_right.2 (subset_toMeasurable μ B), measure_toMeasurable] at hcar
      have hdiff : μ (toMeasurable μ B \ B) = 0 :=
        (ENNReal.add_right_inj hBfin).1 (by rw [add_zero]; exact hcar.symm)
      -- Hence `B = H` up to a `μ`-null set.
      refine (measurableSet_toMeasurable μ B).nullMeasurableSet.congr (ae_eq_set.2 ⟨hdiff, ?_⟩)
      rw [sdiff_eq_empty.2 (subset_toMeasurable μ B), measure_empty]
    -- `A = ⋃ₙ (A ∩ Sₙ)` is a countable union of null-measurable sets.
    rw [← inter_univ A, ← iUnion_spanningSets μ, inter_iUnion]
    exact .iUnion hpiece
  -- Step 4: preimages of Borel sets under `ν` are Carathéodory, hence null-measurable.
  have hν₀ : NullMeasurable ν μ := fun s hs ↦ hnull _ (hν hs)
  -- Steps 5–6: the Borel `σ`-algebra of `ℝᴺ` is countably generated, so `ν` is a.e.-measurable,
  -- hence a.e.-strongly measurable; its strongly measurable representative is the version.
  have hsm := hν₀.aemeasurable.aestronglyMeasurable
  exact ⟨hsm.mk ν, hsm.stronglyMeasurable_mk, hsm.ae_eq_mk⟩

/-- **Riesz representation with a Borel unit field on a σ-compact locally compact Hausdorff
space**: Simon Ch. 1, Theorem 4.14 (`chapter-01.txt` lines 1654–1663) with `H = ℝᴺ`, as used
for (4.1). For an orthonormal basis `b` of `ℝᴺ`, each component `ℓᵢ h = L (h • bᵢ)` is bounded
above on the order intervals `[0, f]` of `C_c(X, ℝ)`. Hence `q f = sup {ℓᵢ g : 0 ≤ g ≤ f}` is
additive (split `g ≤ f₁ + f₂` as `g ⊓ f₁ + g₂`) and positively homogeneous on the cone, and
`ℓᵢ = Aᵢ - Bᵢ` with the positive functionals `Aᵢ = q`, `Bᵢ = q - ℓᵢ`. Mathlib's
Riesz–Markov–Kakutani theorem represents `Aᵢ` and `Bᵢ` by Radon measures, which have Borel
Radon–Nikodym densities with respect to their sum `μ₀`; so `L f = ∫ ⟨f, ρ⟩ dμ₀` for a Borel field
`ρ = ∑ᵢ dᵢ bᵢ`, locally `μ₀`-integrable. The polar decomposition `μ = |ρ| μ₀`, `ν = ρ / |ρ|`
gives the claim. -/
theorem Submission.gaussGreenRep_riesz_sigmaCompact_borel : ∀ (X : Type) [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (N : ℕ) (L : C_c(X, Rn N) →ₗ[ℝ] ℝ), (∀ K : Set X, IsCompact K → ∃ C : ℝ,
      ∀ f : C_c(X, Rn N), (∀ x, ‖f x‖ ≤ 1) → tsupport f ⊆ K → L f ≤ C) →
    ∃ (μ : Measure X) (ν : X → Rn N), (∀ K : Set X, IsCompact K → μ K < ∞) ∧
      StronglyMeasurable ν ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
      ∀ f : C_c(X, Rn N), L f = ∫ x, inner ℝ (f x) (ν x) ∂μ := by
  intro X _ _ _ _ _ _ N L hbound
  -- Step 1 (Jordan decomposition): a real functional `ℓ` on `C_c(X, ℝ)` that is bounded above on
  -- every order interval `[0, f]` is a difference of two positive functionals.
  have jordan : ∀ ℓ : C_c(X, ℝ) →ₗ[ℝ] ℝ,
      (∀ f : C_c(X, ℝ≥0), BddAbove ((fun g : C_c(X, ℝ≥0) ↦ ℓ g.toReal) '' {g | g ≤ f})) →
      ∃ A B : C_c(X, ℝ) →ₚ[ℝ] ℝ, ∀ h, ℓ h = A h - B h := by
    intro ℓ hℓ
    have h0le : ∀ f : C_c(X, ℝ≥0), 0 ≤ f := fun f ↦
      CompactlySupportedContinuousMap.le_def.2 fun x ↦ by simp
    have htoReal0 : (0 : C_c(X, ℝ≥0)).toReal = 0 := by ext x; simp
    have hsmulR : ∀ (c : ℝ≥0) (f : C_c(X, ℝ≥0)), (c • f).toReal = (c : ℝ) • f.toReal :=
      fun c f ↦ by ext x; simp [NNReal.smul_def]
    -- `q f = sup {ℓ g : 0 ≤ g ≤ f}`, the positive part of `ℓ` on the cone `C_c(X, ℝ≥0)`.
    obtain ⟨q, hq⟩ : ∃ q : C_c(X, ℝ≥0) → ℝ,
        ∀ f, q f = sSup ((fun g : C_c(X, ℝ≥0) ↦ ℓ g.toReal) '' {g | g ≤ f}) := ⟨_, fun _ ↦ rfl⟩
    have hle : ∀ f g : C_c(X, ℝ≥0), g ≤ f → ℓ g.toReal ≤ q f := fun f g hg ↦ by
      rw [hq]; exact le_csSup (hℓ f) ⟨g, hg, rfl⟩
    have hsup : ∀ (f : C_c(X, ℝ≥0)) (c : ℝ),
        (∀ g : C_c(X, ℝ≥0), g ≤ f → ℓ g.toReal ≤ c) → q f ≤ c := by
      intro f c hc
      rw [hq]
      exact csSup_le ⟨_, ⟨0, h0le f, rfl⟩⟩ (by rintro _ ⟨g, hg, rfl⟩; exact hc g hg)
    -- Additivity: `g ≤ f₁ + f₂` splits as `(g ⊓ f₁) + g₂` with `g₂ ≤ f₂`.
    have hq_add : ∀ f₁ f₂ : C_c(X, ℝ≥0), q (f₁ + f₂) = q f₁ + q f₂ := by
      intro f₁ f₂
      apply le_antisymm
      · refine hsup _ _ fun g hg ↦ ?_
        obtain ⟨g₂, hg₂⟩ :=
          CompactlySupportedContinuousMap.exists_add_of_le (inf_le_left : g ⊓ f₁ ≤ g)
        have h₂ : g₂ ≤ f₂ := by
          rw [CompactlySupportedContinuousMap.le_def] at hg ⊢
          intro x
          have hx := hg x
          have hgx := congrArg (fun φ : C_c(X, ℝ≥0) ↦ φ x) hg₂
          simp only [CompactlySupportedContinuousMap.add_apply,
            CompactlySupportedContinuousMap.inf_apply] at hx hgx
          rcases le_total (g x) (f₁ x) with h | h
          · rw [inf_eq_left.2 h] at hgx
            have : g₂ x = 0 := by simpa using hgx
            rw [this]
            exact zero_le
          · rw [inf_eq_right.2 h] at hgx
            rw [← hgx] at hx
            exact le_of_add_le_add_left hx
        rw [← hg₂, CompactlySupportedContinuousMap.toReal_add, map_add]
        exact add_le_add (hle _ _ inf_le_right) (hle _ _ h₂)
      · have h1 : q f₁ ≤ q (f₁ + f₂) - q f₂ := hsup _ _ fun g₁ hg₁ ↦ by
          have h2 : q f₂ ≤ q (f₁ + f₂) - ℓ g₁.toReal := hsup _ _ fun g₂ hg₂ ↦ by
            have := hle (f₁ + f₂) (g₁ + g₂) (add_le_add hg₁ hg₂)
            rw [CompactlySupportedContinuousMap.toReal_add, map_add] at this
            linarith
          linarith
        linarith
    -- Positive homogeneity.
    have hq_le_smul : ∀ (c : ℝ≥0) (f : C_c(X, ℝ≥0)), c ≠ 0 → q (c • f) ≤ c * q f := by
      intro c f hc
      refine hsup _ _ fun g hg ↦ ?_
      have hg' : c⁻¹ • g ≤ f := by
        rw [CompactlySupportedContinuousMap.le_def] at hg ⊢
        intro x
        rw [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
        calc c⁻¹ * g x ≤ c⁻¹ * (c • f) x := mul_le_mul_of_nonneg_left (hg x) zero_le
          _ = f x := by
            rw [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ hc]
      have h2 : ℓ g.toReal = c * ℓ (c⁻¹ • g).toReal := by
        rw [hsmulR, map_smul, smul_eq_mul, NNReal.coe_inv, ← mul_assoc,
          mul_inv_cancel₀ (NNReal.coe_ne_zero.2 hc), one_mul]
      rw [h2]
      exact mul_le_mul_of_nonneg_left (hle f _ hg') c.coe_nonneg
    have hq_smul : ∀ (c : ℝ≥0) (f : C_c(X, ℝ≥0)), q (c • f) = c * q f := by
      intro c f
      rcases eq_or_ne c 0 with rfl | hc
      · have h0 := hq_add 0 0
        rw [add_zero] at h0
        rw [zero_smul, NNReal.coe_zero, zero_mul]
        linarith
      · refine le_antisymm (hq_le_smul c f hc) ?_
        have h1 := hq_le_smul c⁻¹ (c • f) (inv_ne_zero hc)
        rw [inv_smul_smul₀ hc, NNReal.coe_inv] at h1
        have hc' : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
        calc (c : ℝ) * q f ≤ c * ((c : ℝ)⁻¹ * q (c • f)) := mul_le_mul_of_nonneg_left h1 hc'.le
          _ = q (c • f) := by rw [← mul_assoc, mul_inv_cancel₀ hc'.ne', one_mul]
    have hq_nonneg : ∀ f, 0 ≤ q f := fun f ↦ by
      have := hle f 0 (h0le f)
      rwa [htoReal0, map_zero] at this
    have hq_ge : ∀ f, ℓ f.toReal ≤ q f := fun f ↦ hle f f le_rfl
    -- The positive part `P = q` and the negative part `Q = q - ℓ` on the cone.
    let P : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 :=
      { toFun := fun f ↦ Real.toNNReal (q f)
        map_add' := fun f₁ f₂ ↦ by
          simp only [hq_add]
          exact Real.toNNReal_add (hq_nonneg f₁) (hq_nonneg f₂)
        map_smul' := fun c f ↦ by
          simp only [hq_smul, RingHom.id_apply, smul_eq_mul]
          rw [Real.toNNReal_mul c.coe_nonneg, Real.toNNReal_coe] }
    let Q : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 :=
      { toFun := fun f ↦ Real.toNNReal (q f - ℓ f.toReal)
        map_add' := fun f₁ f₂ ↦ by
          simp only [hq_add, CompactlySupportedContinuousMap.toReal_add, map_add]
          rw [← Real.toNNReal_add (sub_nonneg.2 (hq_ge f₁)) (sub_nonneg.2 (hq_ge f₂))]
          congr 1
          ring
        map_smul' := fun c f ↦ by
          simp only [hq_smul, hsmulR, map_smul, RingHom.id_apply, smul_eq_mul]
          rw [← mul_sub, Real.toNNReal_mul c.coe_nonneg, Real.toNNReal_coe] }
    have hPQ : ∀ f : C_c(X, ℝ≥0), ((P f : ℝ≥0) : ℝ) - ((Q f : ℝ≥0) : ℝ) = ℓ f.toReal := by
      intro f
      show ((Real.toNNReal (q f) : ℝ≥0) : ℝ) - ((Real.toNNReal (q f - ℓ f.toReal) : ℝ≥0) : ℝ) =
        ℓ f.toReal
      rw [Real.coe_toNNReal _ (hq_nonneg f), Real.coe_toNNReal _ (sub_nonneg.2 (hq_ge f))]
      ring
    refine ⟨CompactlySupportedContinuousMap.toRealPositiveLinear P,
      CompactlySupportedContinuousMap.toRealPositiveLinear Q, fun h ↦ ?_⟩
    rw [CompactlySupportedContinuousMap.toRealPositiveLinear_apply,
      CompactlySupportedContinuousMap.toRealPositiveLinear_apply]
    conv_lhs => rw [← CompactlySupportedContinuousMap.nnrealPart_sub_nnrealPart_neg h]
    rw [map_sub, ← hPQ, ← hPQ]
    ring
  -- Step 2: the components `ℓᵢ h = L (h • bᵢ)` of `L` in an orthonormal basis `b` of `ℝᴺ`.
  obtain ⟨b⟩ : Nonempty (OrthonormalBasis (Fin N) ℝ (Rn N)) :=
    ⟨EuclideanSpace.basisFun (Fin N) ℝ⟩
  have hbn : ∀ i, ‖b i‖ = 1 := fun i ↦ b.orthonormal.1 i
  let E : Fin N → C_c(X, ℝ) →ₗ[ℝ] C_c(X, Rn N) := fun i ↦
    { toFun := fun h ↦ ⟨⟨fun x ↦ h x • b i, h.continuous.smul continuous_const⟩,
        h.hasCompactSupport.smul_right⟩
      map_add' := fun h₁ h₂ ↦ by ext x; simp [add_smul]
      map_smul' := fun c h ↦ by ext x; simp [smul_smul] }
  have hE : ∀ i (h : C_c(X, ℝ)) (x : X), E i h x = h x • b i := fun _ _ _ ↦ rfl
  let comp : Fin N → C_c(X, Rn N) → C_c(X, ℝ) := fun i g ↦
    ⟨⟨fun x ↦ inner ℝ (b i) (g x), continuous_const.inner g.continuous⟩,
      g.hasCompactSupport.comp_left (g := fun y ↦ inner ℝ (b i) y) (inner_zero_right _)⟩
  have hcomp : ∀ i (g : C_c(X, Rn N)) (x : X), comp i g x = inner ℝ (b i) (g x) :=
    fun _ _ _ ↦ rfl
  have hdecomp : ∀ g : C_c(X, Rn N), L g = ∑ i, L (E i (comp i g)) := by
    intro g
    rw [← map_sum]
    congr 1
    refine CompactlySupportedContinuousMap.ext fun x ↦ ?_
    rw [CompactlySupportedContinuousMap.sum_apply]
    simp only [hE, hcomp]
    exact (b.sum_repr' (g x)).symm
  -- The local bound on `L` bounds each `ℓᵢ` above on the order intervals `[0, f]`.
  have hℓbdd : ∀ i (f : C_c(X, ℝ≥0)),
      BddAbove ((fun g : C_c(X, ℝ≥0) ↦ (L ∘ₗ E i) g.toReal) '' {g | g ≤ f}) := by
    intro i f
    obtain ⟨C, hC⟩ := hbound (tsupport f) f.hasCompactSupport
    obtain ⟨M, hM⟩ := (f.hasCompactSupport.isCompact_range f.continuous).bddAbove
    have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    refine ⟨((M : ℝ) + 1) * C, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    have hgf : ∀ x, (g x : ℝ) ≤ M := fun x ↦
      NNReal.coe_le_coe.2 ((CompactlySupportedContinuousMap.le_def.1 hg x).trans (hM ⟨x, rfl⟩))
    have hφ1 : ∀ x, ‖E i (((M : ℝ) + 1)⁻¹ • g.toReal) x‖ ≤ 1 := fun x ↦ by
      rw [hE, CompactlySupportedContinuousMap.smul_apply,
        CompactlySupportedContinuousMap.toReal_apply, smul_eq_mul, norm_smul, hbn, mul_one,
        Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_mul_le_iff₀ hM1]
      linarith [hgf x]
    have hφK : tsupport (E i (((M : ℝ) + 1)⁻¹ • g.toReal)) ⊆ tsupport f := by
      refine closure_mono fun x hx ↦ ?_
      rw [Function.mem_support] at hx ⊢
      intro hfx
      apply hx
      have hgx : g x = 0 :=
        le_antisymm ((CompactlySupportedContinuousMap.le_def.1 hg x).trans hfx.le) zero_le
      rw [hE, CompactlySupportedContinuousMap.smul_apply,
        CompactlySupportedContinuousMap.toReal_apply, hgx]
      simp
    calc (L ∘ₗ E i) g.toReal = ((M : ℝ) + 1) * L (E i (((M : ℝ) + 1)⁻¹ • g.toReal)) := by
          rw [LinearMap.comp_apply, map_smul, map_smul, smul_eq_mul, ← mul_assoc,
            mul_inv_cancel₀ hM1.ne', one_mul]
      _ ≤ ((M : ℝ) + 1) * C := mul_le_mul_of_nonneg_left (hC _ hφ1 hφK) hM1.le
  -- Step 3: Jordan decompositions `ℓᵢ = Aᵢ - Bᵢ` and the Riesz measures of `Aᵢ`, `Bᵢ` (Mathlib's
  -- Riesz–Markov–Kakutani theorem), all absolutely continuous with respect to their sum `μ₀`.
  choose A B hAB using fun i ↦ jordan (L ∘ₗ E i) (hℓbdd i)
  have hAB' : ∀ i h, L (E i h) = A i h - B i h := hAB
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀ : Measure X,
      μ₀ = ∑ i, (RealRMK.rieszMeasure (A i) + RealRMK.rieszMeasure (B i)) := ⟨_, rfl⟩
  have hμ₀K : ∀ K : Set X, IsCompact K → μ₀ K < ∞ := by
    intro K hK
    rw [hμ₀, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.2 fun i _ ↦ by
      rw [Measure.add_apply]
      exact ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hK.measure_lt_top⟩
  have : IsFiniteMeasureOnCompacts μ₀ := ⟨hμ₀K⟩
  have hac : ∀ i, RealRMK.rieszMeasure (A i) ≪ μ₀ ∧ RealRMK.rieszMeasure (B i) ≪ μ₀ := by
    intro i
    have h0 : ∀ s, μ₀ s = 0 →
        RealRMK.rieszMeasure (A i) s = 0 ∧ RealRMK.rieszMeasure (B i) s = 0 := by
      intro s hs
      rw [hμ₀, Measure.finsetSum_apply, Finset.sum_eq_zero_iff] at hs
      have := hs i (Finset.mem_univ i)
      rwa [Measure.add_apply, add_eq_zero] at this
    exact ⟨fun ⦃s⦄ hs ↦ (h0 s hs).1, fun ⦃s⦄ hs ↦ (h0 s hs).2⟩
  -- Radon–Nikodym: a measure `m ≪ μ₀` finite on compact sets is `μ₀` with a density `d`.
  have rn : ∀ m : Measure X, IsFiniteMeasureOnCompacts m → m ≪ μ₀ →
      ∃ d : X → ℝ≥0∞, Measurable d ∧ (∀ K : Set X, IsCompact K → ∫⁻ x in K, d x ∂μ₀ < ∞) ∧
        ∀ h : C_c(X, ℝ), Integrable (fun x ↦ (d x).toReal * h x) μ₀ ∧
          ∫ x, h x ∂m = ∫ x, (d x).toReal * h x ∂μ₀ := by
    intro m hm hmac
    have hwd : μ₀.withDensity (m.rnDeriv μ₀) = m := by
      conv_rhs => rw [m.haveLebesgueDecomposition_add μ₀]
      rw [Measure.singularPart_eq_zero_of_ac hmac, zero_add]
    have hlt := Measure.rnDeriv_lt_top m μ₀
    refine ⟨m.rnDeriv μ₀, Measure.measurable_rnDeriv m μ₀, fun K hK ↦
      Measure.lintegral_rnDeriv_lt_top_of_measure_ne_top μ₀ hK.measure_lt_top.ne,
      fun h ↦ ⟨?_, ?_⟩⟩
    · have hint : Integrable (fun x ↦ h x) (μ₀.withDensity (m.rnDeriv μ₀)) := by
        rw [hwd]
        exact h.continuous.integrable_of_hasCompactSupport h.hasCompactSupport
      exact (integrable_withDensity_iff_integrable_smul' (Measure.measurable_rnDeriv m μ₀) hlt).1
        hint
    · calc ∫ x, h x ∂m = ∫ x, h x ∂(μ₀.withDensity (m.rnDeriv μ₀)) := by rw [hwd]
        _ = ∫ x, (m.rnDeriv μ₀ x).toReal • h x ∂μ₀ :=
          integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv m μ₀) hlt _
  -- Each `ℓᵢ` has a locally `μ₀`-integrable density `dᵢ`.
  have hd : ∀ i, ∃ d : X → ℝ, Measurable d ∧
      (∀ K : Set X, IsCompact K → ∫⁻ x in K, ‖d x‖ₑ ∂μ₀ < ∞) ∧
      ∀ h : C_c(X, ℝ), Integrable (fun x ↦ d x * h x) μ₀ ∧ L (E i h) = ∫ x, d x * h x ∂μ₀ := by
    intro i
    obtain ⟨dA, hdAm, hdAK, hdA⟩ := rn _ inferInstance (hac i).1
    obtain ⟨dB, hdBm, hdBK, hdB⟩ := rn _ inferInstance (hac i).2
    refine ⟨fun x ↦ (dA x).toReal - (dB x).toReal, hdAm.ennreal_toReal.sub hdBm.ennreal_toReal,
      fun K hK ↦ ?_, fun h ↦ ?_⟩
    · have hpt : ∀ x, ‖(dA x).toReal - (dB x).toReal‖ₑ ≤ dA x + dB x := fun x ↦ by
        refine enorm_sub_le.trans (add_le_add ?_ ?_) <;>
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg] <;>
          exact ENNReal.ofReal_toReal_le
      calc ∫⁻ x in K, ‖(dA x).toReal - (dB x).toReal‖ₑ ∂μ₀ ≤ ∫⁻ x in K, (dA x + dB x) ∂μ₀ :=
            lintegral_mono hpt
        _ = ∫⁻ x in K, dA x ∂μ₀ + ∫⁻ x in K, dB x ∂μ₀ := lintegral_add_left hdAm _
        _ < ∞ := ENNReal.add_lt_top.2 ⟨hdAK K hK, hdBK K hK⟩
    · obtain ⟨hiA, hA⟩ := hdA h
      obtain ⟨hiB, hB⟩ := hdB h
      refine ⟨(hiA.sub hiB).congr (ae_of_all _ fun x ↦ ?_), ?_⟩
      · simp only [Pi.sub_apply]
        ring
      · rw [hAB', ← RealRMK.integral_rieszMeasure (A i), ← RealRMK.integral_rieszMeasure (B i),
          hA, hB, ← integral_sub hiA hiB]
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        beta_reduce
        ring
  choose d hdm hdK hdrep using hd
  -- Step 4: the field `ρ = ∑ᵢ dᵢ bᵢ` represents `L` against `μ₀`.
  obtain ⟨ρ, hρ⟩ : ∃ ρ : X → Rn N, ρ = fun x ↦ ∑ i, d i x • b i := ⟨_, rfl⟩
  have hρm : Measurable ρ := by
    rw [hρ]
    exact Finset.measurable_sum _ fun i _ ↦ (hdm i).smul_const _
  have hρK : ∀ K : Set X, IsCompact K → ∫⁻ x in K, ‖ρ x‖ₑ ∂μ₀ < ∞ := by
    intro K hK
    have hpt : ∀ x, ‖ρ x‖ₑ ≤ ∑ i, ‖d i x‖ₑ := fun x ↦ by
      rw [hρ]
      refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
      rw [enorm_smul, ← ofReal_norm (b i), hbn, ENNReal.ofReal_one, mul_one]
    calc ∫⁻ x in K, ‖ρ x‖ₑ ∂μ₀ ≤ ∫⁻ x in K, ∑ i, ‖d i x‖ₑ ∂μ₀ := lintegral_mono hpt
      _ = ∑ i, ∫⁻ x in K, ‖d i x‖ₑ ∂μ₀ := lintegral_finsetSum _ fun i _ ↦ (hdm i).enorm
      _ < ∞ := ENNReal.sum_lt_top.2 fun i _ ↦ hdK i K hK
  have hrep₀ : ∀ g : C_c(X, Rn N), L g = ∫ x, inner ℝ (g x) (ρ x) ∂μ₀ := by
    intro g
    rw [hdecomp g, Finset.sum_congr rfl fun i _ ↦ (hdrep i (comp i g)).2,
      ← integral_finsetSum _ fun i _ ↦ (hdrep i (comp i g)).1]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [hρ, inner_sum, real_inner_smul_right, hcomp]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm]
  -- Step 5 (polar decomposition): `μ = |ρ| μ₀` and `ν = ρ / |ρ|`.
  refine ⟨μ₀.withDensity fun x ↦ ‖ρ x‖ₑ, fun x ↦ ‖ρ x‖⁻¹ • ρ x, fun K hK ↦ ?_,
    (hρm.norm.inv.smul hρm).stronglyMeasurable, ?_, fun g ↦ ?_⟩
  · rw [withDensity_apply _ hK.measurableSet]
    exact hρK K hK
  · rw [ae_withDensity_iff hρm.enorm]
    refine ae_of_all _ fun x hx ↦ ?_
    have hx0 : ρ x ≠ 0 := fun h ↦ hx (by rw [h, enorm_zero])
    show ‖‖ρ x‖⁻¹ • ρ x‖ = 1
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]
  · rw [hrep₀ g, integral_withDensity_eq_integral_toReal_smul hρm.enorm
      (ae_of_all _ fun x ↦ enorm_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    show inner ℝ (g x) (ρ x) = (‖ρ x‖ₑ).toReal • inner ℝ (g x) (‖ρ x‖⁻¹ • ρ x)
    rw [toReal_enorm, smul_eq_mul, real_inner_smul_right]
    rcases eq_or_ne (ρ x) 0 with h | h
    · simp [h]
    · rw [mul_inv_cancel_left₀ (norm_ne_zero_iff.2 h)]
/-- **Zero extension of a functional on admissible fields** (Steps 1–4 of the proof of the
Gauss–Green representation on an open `U`, passing from `ℝᴺ` to `U` to apply Simon Ch. 1,
Theorem 4.14, `chapter-01.txt` lines 1654–1663, in Ch. 2 (2.1)–(2.2), `chapter-02.txt`
lines 485–496). For `f ∈ C_c(U; ℝᴺ)` the zero extension `f̃ = extend ι f 0` (`ι : U → ℝᴺ`) is
continuous since `U` is open (`HasCompactSupport.continuous_extend_zero`), has
`tsupport f̃ ⊆ ι(tsupport f) ⊆ U` (`tsupport_extend_zero_subset`) and is linear in `f`, so
`L f := Λ f̃` is linear and inherits the bound of `Λ` on `ι(K)`. For admissible `g`, the
restriction `g ∘ ι` vanishes off the compact `ι⁻¹(tsupport g)` and its zero extension is `g`. -/
theorem Submission.gaussGreenRep_riesz_zero_extension_functional : ∀ (N : ℕ) (U : Set (Rn N)) (Λ : (Rn N → Rn N) → ℝ), IsOpen U → (∀ g h : Rn N → Rn N, Continuous g → HasCompactSupport g → tsupport g ⊆ U → Continuous h → HasCompactSupport h → tsupport h ⊆ U → Λ (g + h) = Λ g + Λ h) → (∀ (c : ℝ) (g : Rn N → Rn N), Continuous g → HasCompactSupport g → tsupport g ⊆ U → Λ (c • g) = c * Λ g) → (∀ K : Set (Rn N), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ g : Rn N → Rn N, Continuous g → tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → Λ g ≤ C) → ∃ L : C_c(U, Rn N) →ₗ[ℝ] ℝ, (∀ K : Set U, IsCompact K → ∃ C : ℝ, ∀ f : C_c(U, Rn N), (∀ x, ‖f x‖ ≤ 1) → tsupport f ⊆ K → L f ≤ C) ∧ ∀ g : Rn N → Rn N, Continuous g → HasCompactSupport g → tsupport g ⊆ U → ∃ f : C_c(U, Rn N), (∀ y : U, f y = g ↑y) ∧ L f = Λ g := by
  intro N U Λ hU hadd hsmul hbd
  -- The zero extension `f̃ = extend ι f 0` of `f ∈ C_c(U; ℝᴺ)`, `ι : U → ℝᴺ` the inclusion.
  let E : C_c(U, Rn N) → Rn N → Rn N := fun f ↦ Subtype.val.extend (⇑f) 0
  have hEval : ∀ (f : C_c(U, Rn N)) (y : U), E f y = f y := fun f y ↦
    Subtype.val_injective.extend_apply _ _ y
  have hEout : ∀ (f : C_c(U, Rn N)) (x : Rn N), x ∉ U → E f x = 0 := fun f x hx ↦
    Function.extend_apply' _ _ x fun ⟨y, hy⟩ ↦ hx (hy ▸ y.2)
  -- `f̃` is admissible: continuous (`U` is open), compactly supported, `tsupport f̃ ⊆ ι(tsupport f)`.
  have hEcont : ∀ f : C_c(U, Rn N), Continuous (E f) := fun f ↦
    HasCompactSupport.continuous_extend_zero hU f.continuous f.hasCompactSupport
  have hEcs : ∀ f : C_c(U, Rn N), HasCompactSupport (E f) := fun f ↦
    f.hasCompactSupport.extend_zero continuous_subtype_val
  have hEsupp : ∀ f : C_c(U, Rn N), tsupport (E f) ⊆ Subtype.val '' tsupport f := fun f ↦
    f.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val
  have hEU : ∀ f : C_c(U, Rn N), tsupport (E f) ⊆ U := fun f ↦
    (hEsupp f).trans (Subtype.coe_image_subset _ _)
  -- The extension is linear in `f`.
  have hEadd : ∀ f f' : C_c(U, Rn N), E (f + f') = E f + E f' := by
    intro f f'
    funext x
    by_cases hx : x ∈ U
    · lift x to U using hx
      simp [hEval]
    · simp [hEout _ _ hx]
  have hEsmul : ∀ (c : ℝ) (f : C_c(U, Rn N)), E (c • f) = c • E f := by
    intro c f
    funext x
    by_cases hx : x ∈ U
    · lift x to U using hx
      simp [hEval]
    · simp [hEout _ _ hx]
  refine ⟨{ toFun := fun f ↦ Λ (E f)
            map_add' := fun f f' ↦ by
              simp only [hEadd]
              exact hadd _ _ (hEcont f) (hEcs f) (hEU f) (hEcont f') (hEcs f') (hEU f')
            map_smul' := fun c f ↦ by
              simp only [hEsmul, RingHom.id_apply, smul_eq_mul]
              exact hsmul c _ (hEcont f) (hEcs f) (hEU f) }, ?_, ?_⟩
  · -- (i) the local bound, from the bound for `Λ` on `ι(K)`.
    intro K hK
    obtain ⟨C, hC⟩ := hbd (Subtype.val '' K) (hK.image continuous_subtype_val)
      (Subtype.coe_image_subset _ _)
    refine ⟨C, fun f hf1 hfK ↦ hC (E f) (hEcont f) ((hEsupp f).trans (image_mono hfK)) ?_⟩
    intro x
    by_cases hx : x ∈ U
    · lift x to U using hx
      rw [hEval]
      exact hf1 x
    · rw [hEout _ _ hx, norm_zero]
      exact zero_le_one
  · -- (ii) the restriction `g ∘ ι` lies in `C_c(U; ℝᴺ)` and its zero extension is `g`.
    intro g hg hgc hgU
    have hK₀ : IsCompact (Subtype.val ⁻¹' tsupport g : Set U) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr hgU]
      exact hgc
    let f : C_c(U, Rn N) :=
      ⟨⟨g ∘ Subtype.val, hg.comp continuous_subtype_val⟩,
        HasCompactSupport.intro hK₀ fun y hy ↦ image_eq_zero_of_notMem_tsupport (f := g) hy⟩
    have hEf : E f = g := by
      funext x
      by_cases hx : x ∈ U
      · lift x to U using hx
        rw [hEval]
        rfl
      · rw [hEout _ _ hx]
        exact (image_eq_zero_of_notMem_tsupport fun h ↦ hx (hgU h)).symm
    exact ⟨f, fun y ↦ rfl, show Λ (E f) = Λ g by rw [hEf]⟩
/-- **Push-forward of a Riesz pair from a Borel set `U ⊆ ℝᴺ`** (step 7 of the proof that Simon's
Riesz Representation Theorem, Ch. 1, 4.14 (`chapter-01.txt` lines 1654–1663), applied on `X = U`
gives the measure `μ_E` and unit field `ν` on `ℝᴺ` of Ch. 3, (4.1) (`chapter-03.txt` lines
556–564)). Let `ι : U → ℝᴺ` be the inclusion, `μ = ι_# μ₀` and `ν = extend ι ν₀ 0`, so
`ν ∘ ι = ν₀`. As `U` is Borel, `ι` is a measurable embedding, so `μ(S) = μ₀(ι⁻¹ S)` for every `S`:
`μ(ℝᴺ ∖ U) = μ₀(∅) = 0` and `μ(K) = μ₀(ι⁻¹ K) < ∞` for compact `K ⊆ U`. A.e. statements,
a.e.-strong measurability and Bochner integrals transfer along `ι`. -/
theorem Submission.gaussGreenRep_riesz_pushforward_subtype : ∀ (N : ℕ) (U : Set (Rn N)) (μ₀ : Measure U) (ν₀ : U → Rn N), MeasurableSet U → (∀ K : Set U, IsCompact K → μ₀ K < ∞) → AEStronglyMeasurable ν₀ μ₀ → (∀ᵐ y ∂μ₀, ‖ν₀ y‖ = 1) → ∃ (μ : Measure (Rn N)) (ν : Rn N → Rn N), μ Uᶜ = 0 ∧ (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) ∧ AEStronglyMeasurable ν μ ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧ ∀ g : Rn N → Rn N, ∫ x, inner ℝ (g x) (ν x) ∂μ = ∫ y, inner ℝ (g ↑y) (ν₀ y) ∂μ₀ := by
  intro N U μ₀ ν₀ hU hfin hν₀ hnorm
  -- Step 1: the inclusion `ι : U → ℝᴺ` is a measurable embedding since `U` is Borel.
  have hι : MeasurableEmbedding ((↑) : U → Rn N) := MeasurableEmbedding.subtype_coe hU
  -- Step 2: `ν` extends `ν₀` by zero, so `ν ∘ ι = ν₀`.
  have hνι : (Function.extend ((↑) : U → Rn N) ν₀ 0) ∘ ((↑) : U → Rn N) = ν₀ :=
    funext fun y ↦ Subtype.val_injective.extend_apply ν₀ 0 y
  refine ⟨μ₀.map (↑), Function.extend ((↑) : U → Rn N) ν₀ 0, ?_, ?_, ?_, ?_, ?_⟩
  · -- Step 5: `μ(ℝᴺ ∖ U) = μ₀(ι⁻¹(ℝᴺ ∖ U)) = μ₀(∅) = 0`.
    rw [hι.map_apply, preimage_compl, Subtype.coe_preimage_self, compl_univ, measure_empty]
  · -- Step 6: for compact `K ⊆ U`, `ι⁻¹ K` is compact (its image is `U ∩ K = K`).
    intro K hK hKU
    rw [hι.map_apply]
    refine hfin _ ?_
    rwa [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hKU]
  · -- Step 7: a.e.-strong measurability transfers along `ι`.
    rw [hι.aestronglyMeasurable_map_iff, hνι]
    exact hν₀
  · -- Step 8: `|ν(ι y)| = |ν₀ y| = 1` for `μ₀`-a.e. `y`.
    rw [hι.ae_map_iff]
    filter_upwards [hnorm] with y hy
    rwa [Subtype.val_injective.extend_apply]
  · -- Step 9: change of variables `∫ F dμ = ∫ F ∘ ι dμ₀` for every `F`.
    intro g
    rw [hι.integral_map]
    simp only [Subtype.val_injective.extend_apply]

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
