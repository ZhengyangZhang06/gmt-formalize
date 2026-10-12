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

/-- **The slab around a cone point is covered by two cones**: the covering step in the proof of
P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Lemma 15.14 (M. G. Dall'Alba,
*The Besicovitch–Federer Projection Theorem*, Lemma 4.6), used for Simon Ch. 3, Theorem 3.6
(`chapter-03.txt` lines 530–536, which defers the proof to [Fed69]). With
`Y = {y ∈ S : |P(y - x)| < (s/4)|y - x|} ≠ ∅`, `h = sup_{y ∈ Y} |y - x| ∈ (0, R]` and `x' ∈ Y`
with `|x' - x| > 3h/4`, a point `z ≠ x` of `S` with `|P(z - x)| < sh/4` has `|z - x| ≤ h` by
maximality of `h`; if it is not in the `s`-cone at `x'`, linearity of `P` gives `|z - x'| < h/2`,
hence `|z - x| > h/4` and `z` is in the `s`-cone at `x`. -/
theorem Submission.bf_coneMass_slab_cover : ∀ (N : ℕ) (P : Rn N →L[ℝ] Rn N) (s R : ℝ) (S : Set (Rn N)) (x : Rn N), 0 < s → (∃ y ∈ S, ‖P (y - x)‖ < s / 4 * ‖y - x‖) → (∀ y ∈ S, ‖y - x‖ ≤ R) → ∃ h : ℝ, 0 < h ∧ h ≤ R ∧ ∃ x' ∈ S, S ∩ {z | ‖P (z - x)‖ < s * h / 4} ⊆ insert x ({y | ‖P (y - x)‖ < s * ‖y - x‖} ∩ Metric.ball x (3 * h) ∪ {y | ‖P (y - x')‖ < s * ‖y - x'‖} ∩ Metric.ball x' (3 * h)) := by
  intro N P s R S x hs ⟨y₀, hy₀S, hy₀⟩ hR
  -- Step 1: the cone points `Y` all differ from `x`, since `P 0 = 0`.
  set Y : Set (Rn N) := {y | y ∈ S ∧ ‖P (y - x)‖ < s / 4 * ‖y - x‖}
  have hy₀Y : y₀ ∈ Y := ⟨hy₀S, hy₀⟩
  have hYpos : ∀ y ∈ Y, 0 < ‖y - x‖ := by
    intro y hy
    refine lt_of_le_of_ne (norm_nonneg _) fun h0 ↦ ?_
    have hc := hy.2
    rw [← h0, mul_zero] at hc
    exact (norm_nonneg _).not_gt hc
  -- Step 2: `h = sup {|y - x| : y ∈ Y}` satisfies `0 < h ≤ R` and `|y - x| ≤ h` on `Y`.
  set D : Set ℝ := (fun y ↦ ‖y - x‖) '' Y
  have hDne : D.Nonempty := ⟨_, y₀, hy₀Y, rfl⟩
  have hDbdd : BddAbove D := ⟨R, by rintro _ ⟨y, hy, rfl⟩; exact hR y hy.1⟩
  set h := sSup D
  have hle : ∀ y ∈ Y, ‖y - x‖ ≤ h := fun y hy ↦ le_csSup hDbdd ⟨y, hy, rfl⟩
  have hpos : 0 < h := (hYpos y₀ hy₀Y).trans_le (hle y₀ hy₀Y)
  have hhR : h ≤ R := csSup_le hDne (by rintro _ ⟨y, hy, rfl⟩; exact hR y hy.1)
  -- Step 3: a far cone point `x' ∈ Y` with `3h/4 < |x' - x| ≤ h`.
  obtain ⟨_, ⟨x', hx'Y, rfl⟩, hx'far⟩ :=
    exists_lt_of_lt_csSup hDne (show 3 * h / 4 < h by linarith)
  have hx'le : ‖x' - x‖ ≤ h := hle x' hx'Y
  refine ⟨h, hpos, hhR, x', hx'Y.1, ?_⟩
  -- Step 4: the slab inclusion.
  rintro z ⟨hzS, hz : ‖P (z - x)‖ < s * h / 4⟩
  rw [Set.mem_insert_iff]
  by_cases hzx : z = x
  · exact Or.inl hzx
  right
  -- (a) By maximality of `h`, `|z - x| ≤ h`; hence `z ∈ B(x, 3h)` and `z ∈ B(x', 3h)`.
  have hzle : ‖z - x‖ ≤ h := by
    by_contra hcon
    have hsh := mul_lt_mul_of_pos_left (not_le.mp hcon) hs
    exact hcon (hle z ⟨hzS, by linarith⟩)
  have hzball : z ∈ Metric.ball x (3 * h) := by
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  have hzball' : z ∈ Metric.ball x' (3 * h) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have htri := norm_sub_le_norm_sub_add_norm_sub z x x'
    rw [norm_sub_rev x x'] at htri
    linarith
  by_cases hzc : ‖P (z - x')‖ < s * ‖z - x'‖
  · -- (c) `z` lies in the cone at `x'`.
    exact Or.inr ⟨hzc, hzball'⟩
  · -- (d) Otherwise `|z - x'| < h/2`, so `|z - x| > h/4` and `z` lies in the cone at `x`.
    left
    refine ⟨?_, hzball⟩
    have hsplit : P (z - x') = P (z - x) - P (x' - x) := by
      rw [← map_sub]
      congr 1
      abel
    have hPtri : ‖P (z - x')‖ ≤ ‖P (z - x)‖ + ‖P (x' - x)‖ := by
      rw [hsplit]
      exact norm_sub_le _ _
    have hx'cone : ‖P (x' - x)‖ < s / 4 * ‖x' - x‖ := hx'Y.2
    have hsx' := mul_le_mul_of_nonneg_left hx'le hs.le
    have h1 : s * ‖z - x'‖ < s * (h / 2) := by linarith [not_lt.mp hzc]
    have h2 : ‖z - x'‖ < h / 2 := lt_of_mul_lt_mul_left h1 hs.le
    have h3 : ‖x' - x‖ ≤ ‖z - x'‖ + ‖z - x‖ := by
      have htri := norm_sub_le_norm_sub_add_norm_sub x' z x
      rwa [norm_sub_rev x' z] at htri
    have h4 := mul_lt_mul_of_pos_left (show h / 4 < ‖z - x‖ by linarith) hs
    show ‖P (z - x)‖ < s * ‖z - x‖
    linarith
/-- **Packing disjoint balls centred in an `n`-plane** (Mattila, Lemma 15.14; used in the proof of
Simon Ch. 3, Theorem 3.6). Let `W ⊆ ℝᴺ` be a subspace with `dim W = n` and let `B(w i, ρ i)`,
`i ∈ T` (`T` countable), be pairwise disjoint open balls with `w i ∈ W`, `ρ i > 0`, contained in
`B(w₀, R)` with `w₀ ∈ W`. Then `∑_{i ∈ T} ρ iⁿ ≤ Rⁿ`. The inclusion `W → ℝᴺ` is an isometry and
`μHE[n]` on `W` is an additive Haar measure, so `Hⁿ(W ∩ B(v, r)) = rⁿ ω` for `v ∈ W`, `r > 0`,
with `0 < ω < ∞`; countable additivity on the disjoint Borel pieces `W ∩ B(w i, ρ i)` gives
`ω ∑ ρ iⁿ ≤ ω Rⁿ`, and `ω` cancels. -/
theorem Submission.bf_coneMass_subspace_ball_packing : ∀ (n N : ℕ) (W : Submodule ℝ (Rn N)), finrank ℝ W = n → ∀ (ι : Type) (T : Set ι) (w : ι → Rn N) (ρ : ι → ℝ) (w₀ : Rn N) (R : ℝ), T.Countable → (∀ i ∈ T, w i ∈ W) → w₀ ∈ W → (∀ i ∈ T, 0 < ρ i) → T.PairwiseDisjoint (fun i ↦ Metric.ball (w i) (ρ i)) → (∀ i ∈ T, Metric.ball (w i) (ρ i) ⊆ Metric.ball w₀ R) → ∑' i : T, ENNReal.ofReal (ρ i ^ n) ≤ ENNReal.ofReal (R ^ n) := by
  intro n N W hW ι T w ρ w₀ R hTc hwW hw₀ hρ hdisj hsub
  -- Step 1: if `T = ∅` the sum vanishes; otherwise a nonempty ball inside `B(w₀, R)` forces `R > 0`.
  rcases T.eq_empty_or_nonempty with hT | ⟨i₀, hi₀⟩
  · subst hT; simp
  have hR : 0 < R :=
    dist_nonneg.trans_lt (hsub i₀ hi₀ (Metric.mem_ball_self (hρ i₀ hi₀)))
  -- Steps 2–3: `Hⁿ(W ∩ B(v, r)) = ofReal (rⁿ) * ω` for `v ∈ W`, `r > 0`, with `0 < ω < ∞`.
  obtain ⟨ω, hω0, hωtop, hball⟩ : ∃ ω : ℝ≥0∞, ω ≠ 0 ∧ ω ≠ ⊤ ∧ ∀ v ∈ W, ∀ r : ℝ, 0 < r →
      μHE[n] ((W : Set (Rn N)) ∩ Metric.ball v r) = ENNReal.ofReal (r ^ n) * ω := by
    subst hW
    refine ⟨(μHE[finrank ℝ W] : Measure W) (Metric.ball 0 1),
      (Metric.measure_ball_pos _ _ one_pos).ne', measure_ball_lt_top.ne, fun v hv r hr ↦ ?_⟩
    -- The ambient piece `W ∩ B(v, r)` is the image of the intrinsic ball `B_W(v, r)`.
    have himg : (W : Set (Rn N)) ∩ Metric.ball v r =
        (Subtype.val : W → Rn N) '' Metric.ball (⟨v, hv⟩ : W) r := by
      ext z
      constructor
      · rintro ⟨hzW, hz⟩
        exact ⟨⟨z, hzW⟩, by simpa [Metric.mem_ball, Subtype.dist_eq] using hz, rfl⟩
      · rintro ⟨⟨z, hzW⟩, hz, rfl⟩
        exact ⟨hzW, by simpa [Metric.mem_ball, Subtype.dist_eq] using hz⟩
    rw [himg, isometry_subtype_coe.euclideanHausdorffMeasure_image,
      Measure.addHaar_ball_of_pos _ _ hr]
  -- Steps 4–5: the pieces `W ∩ B(w i, ρ i)` are disjoint Borel subsets of `W ∩ B(w₀, R)`.
  have hWclosed : IsClosed (W : Set (Rn N)) := Submodule.closed_of_finiteDimensional W
  have key : (∑' i : T, ENNReal.ofReal (ρ i ^ n)) * ω ≤ ENNReal.ofReal (R ^ n) * ω := by
    rw [← ENNReal.tsum_mul_right]
    calc ∑' i : T, ENNReal.ofReal (ρ i ^ n) * ω
        = ∑' i : T, μHE[n] ((W : Set (Rn N)) ∩ Metric.ball (w i) (ρ i)) := by
          congr 1; ext i; rw [hball _ (hwW i i.2) _ (hρ i i.2)]
      _ = μHE[n] (⋃ i ∈ T, (W : Set (Rn N)) ∩ Metric.ball (w i) (ρ i)) := by
          rw [measure_biUnion hTc]
          · intro i hi j hj hij
            exact Disjoint.mono inter_subset_right inter_subset_right (hdisj hi hj hij)
          · intro i _
            exact hWclosed.measurableSet.inter measurableSet_ball
      _ ≤ μHE[n] ((W : Set (Rn N)) ∩ Metric.ball w₀ R) :=
          measure_mono (iUnion₂_subset fun i hi ↦ inter_subset_inter_right _ (hsub i hi))
      _ = ENNReal.ofReal (R ^ n) * ω := hball w₀ hw₀ R hR
  -- Step 6: cancel `ω ∈ (0, ∞)`.
  exact (ENNReal.mul_le_mul_iff_left hω0 hωtop).1 key
/-- **Cone-free sets are countably `n`-rectifiable** (P. Mattila, *Geometry of Sets and Measures
in Euclidean Spaces*, Lemma 15.13; M. G. Dall'Alba, *The Besicovitch–Federer Projection
Theorem*, Padova 2020, Lemma 4.5), used in Step 2 of the proof of the Besicovitch–Federer
projection theorem (Simon Ch. 3, Theorem 3.6). Let `W ⊆ ℝᴺ` be an `n`-plane with orthogonal
projection `P`, and let `s|b - a| ≤ |P(b - a)|` for `a, b ∈ E` with `|b - a| < r`. Cover `E` by
the pieces `E_k = E ∩ B(d_k, r/2)`, `(d_k)` dense. On `E_k` the projection `P` is injective with
an `s⁻¹`-Lipschitz inverse `φ_k` on `P(E_k)`; extend `φ_k` to a Lipschitz `G_k : ℝᴺ → ℝᴺ`
(McShane, `LipschitzOnWith.extend_finite_dimension`) and precompose with a linear isometry
`J : ℝⁿ → ℝᴺ` onto `W`. Then `E_k ⊆ (G_k ∘ J)(ℝⁿ)`, and `M₀ = ∅` works. -/
theorem Submission.bf_coneFree_countablyRectifiable :
    ∀ (n ℓ : ℕ) (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∀ (s r : ℝ), 0 < s → 0 < r →
      ∀ E : Set (Rn (n + ℓ)), (∀ a ∈ E, ∀ b ∈ E, dist b a < r →
        s * ‖b - a‖ ≤ ‖W.starProjection (b - a)‖) → CountablyRectifiable n E := by
  intro n ℓ W hW s r hs hr E hE
  -- Step 1: the pieces `E_k = E ∩ B(d_k, r/2)` for a dense sequence `(d_k)`; points of one piece
  -- are at distance `< r`, so `s|a - b| ≤ |Pa - Pb|` on each piece.
  let d : ℕ → Rn (n + ℓ) := TopologicalSpace.denseSeq (Rn (n + ℓ))
  let Ek : ℕ → Set (Rn (n + ℓ)) := fun k ↦ E ∩ Metric.ball (d k) (r / 2)
  have hpiece : ∀ k, ∀ a ∈ Ek k, ∀ b ∈ Ek k,
      s * ‖a - b‖ ≤ ‖W.starProjection a - W.starProjection b‖ := by
    intro k a ha b hb
    have hab : dist a b < r :=
      calc dist a b ≤ dist a (d k) + dist (d k) b := dist_triangle _ _ _
        _ < r / 2 + r / 2 := add_lt_add (Metric.mem_ball.1 ha.2) (Metric.mem_ball'.1 hb.2)
        _ = r := add_halves r
    rw [← map_sub]
    exact hE b hb.1 a ha.1 hab
  -- Step 2: `P` is injective on `E_k`, with an `s⁻¹`-Lipschitz inverse `φ_k` on `P(E_k)`.
  have hinj : ∀ k, InjOn W.starProjection (Ek k) := by
    intro k a ha b hb hab
    have h := hpiece k a ha b hb
    rw [hab, sub_self, norm_zero] at h
    have h0 : ‖a - b‖ ≤ 0 := by nlinarith [norm_nonneg (a - b)]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
  let φ : ℕ → Rn (n + ℓ) → Rn (n + ℓ) := fun k ↦ Function.invFunOn W.starProjection (Ek k)
  have hφ : ∀ k, ∀ a ∈ Ek k, φ k (W.starProjection a) = a :=
    fun k ↦ (hinj k).leftInvOn_invFunOn
  have hφLip : ∀ k, LipschitzOnWith (Real.toNNReal s⁻¹) (φ k) (W.starProjection '' Ek k) := by
    intro k
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [hφ k a ha, hφ k b hb, Real.coe_toNNReal _ (inv_nonneg.2 hs.le), dist_eq_norm,
      dist_eq_norm, inv_mul_eq_div, le_div_iff₀' hs]
    exact hpiece k a ha b hb
  -- Step 3: extend `φ_k` to a Lipschitz map `G_k : ℝᴺ → ℝᴺ`.
  choose G hGLip hGEq using fun k ↦ (hφLip k).extend_finite_dimension
  -- Step 4: a linear isometry `J : ℝⁿ → ℝᴺ` onto `W`.
  obtain ⟨ι⟩ : Nonempty (Rn n ≃ₗᵢ[ℝ] W) :=
    ⟨((stdOrthonormalBasis ℝ W).reindex (finCongr hW)).repr.symm⟩
  let J : Rn n →ₗᵢ[ℝ] Rn (n + ℓ) := W.subtypeₗᵢ.comp ι.toLinearIsometry
  have hJ : ∀ x ∈ W, ∃ u, J u = x := fun x hx ↦ ⟨ι.symm ⟨x, hx⟩, by simp [J]⟩
  -- Steps 5–6: `E_k ⊆ (G_k ∘ J)(ℝⁿ)`, so `E ⊆ ∅ ∪ ⋃_k (G_k ∘ J)(ℝⁿ)`.
  refine ⟨∅, measure_empty, fun k ↦ G k ∘ J, fun k ↦ ⟨_, (hGLip k).comp J.lipschitzWith⟩, ?_⟩
  intro a ha
  obtain ⟨k, hk⟩ :=
    (TopologicalSpace.denseRange_denseSeq (Rn (n + ℓ))).exists_dist_lt a (half_pos hr)
  have hak : a ∈ Ek k := ⟨ha, hk⟩
  obtain ⟨u, hu⟩ := hJ _ (W.starProjection_apply_mem a)
  refine Or.inr (mem_iUnion.2 ⟨k, u, ?_⟩)
  show G k (J u) = a
  rw [hu, ← hGEq k ⟨a, hak, rfl⟩, hφ k a hak]

/-- **Small cone mass forces small mass** (P. Mattila, *Geometry of Sets and Measures in
Euclidean Spaces*, Lemma 15.14; M. G. Dall'Alba, *The Besicovitch–Federer Projection Theorem*,
Lemma 4.6), Step 3 of the proof of the Besicovitch–Federer projection theorem (Simon Ch. 3,
Theorem 3.6). Let `W ⊆ ℝ^{n+ℓ}` be an `n`-plane with orthogonal projection `P`, `0 < s < 1`, and
let `B` be purely `n`-unrectifiable with `Hⁿ(B ∩ X(x, r, s)) ≤ c (rs)ⁿ` for `x ∈ B`, `0 < r < δ`,
where `X(x, r, s) = {y : |P(y - x)| < s|y - x|} ∩ B(x, r)`. Then `Hⁿ(B ∩ B(a, δ/8)) ≤ 2·15ⁿ c δⁿ`.
In `B' = B ∩ B(a, δ/8)` the points whose `(s/4)`-cone misses `B'` form a cone-free, hence
rectifiable, hence null set. Every other `x` has a slab `{z : |P(z - x)| < s h(x)/4}` meeting `B'`
in mass `≤ 2c·3ⁿ(s h(x))ⁿ`; the Vitali `5r`-lemma for the balls `B(Px, s h(x)/20)` covers the
rest of `B'` by countably many slabs, and packing the disjoint balls in `W ∩ B(Pa, δ/4)` gives
`∑ (s h(t))ⁿ ≤ 5ⁿ δⁿ`. -/
theorem Submission.bf_coneMass_ball_le : ∀ (n ℓ : ℕ), 0 < n → ∀ (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∀ (s δ c : ℝ), 0 < s → s < 1 → 0 < δ → 0 ≤ c → ∀ B : Set (Rn (n + ℓ)), PurelyUnrectifiable n B → (∀ x ∈ B, ∀ r : ℝ, 0 < r → r < δ → μHE[n] (B ∩ ({y | ‖W.starProjection (y - x)‖ < s * ‖y - x‖} ∩ Metric.ball x r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) → ∀ a : Rn (n + ℓ), μHE[n] (B ∩ Metric.ball a (δ / 8)) ≤ ENNReal.ofReal (2 * 15 ^ n * c * δ ^ n) := by
  intro n ℓ hn W hW s δ c hs hs1 hδ hc B hB hH a
  set P : Rn (n + ℓ) →L[ℝ] Rn (n + ℓ) := W.starProjection
  -- Step 1: `B' = B ∩ B(a, δ/8)` and the points `B''` of `B'` whose `(s/4)`-cone meets `B'`.
  set B' : Set (Rn (n + ℓ)) := B ∩ Metric.ball a (δ / 8)
  set B'' : Set (Rn (n + ℓ)) := {x | x ∈ B' ∧ ∃ y ∈ B', ‖P (y - x)‖ < s / 4 * ‖y - x‖}
  -- Step 2: the cone-free remainder `B' \ B''` is countably rectifiable, hence null.
  have hE : μHE[n] (B' \ B'') = 0 := by
    apply hB
    · intro x hx
      exact hx.1.1
    · apply Submission.bf_coneFree_countablyRectifiable n ℓ W hW (s / 4) 1 (by positivity) one_pos
      intro x hx y hy _
      exact not_lt.1 fun hlt ↦ hx.2 ⟨hx.1, y, hy.1, hlt⟩
  -- Steps 3–4: for `x ∈ B''`, the radius `h x ∈ (0, δ/4]`, the far cone point `x' x ∈ B'` and the
  -- slab inclusion, from `bf_coneMass_slab_cover` (`|y - x| < δ/4` on `B'`).
  have hslab : ∀ x, ∃ h : ℝ, ∃ x' : Rn (n + ℓ), x ∈ B'' → 0 < h ∧ h ≤ δ / 4 ∧ x' ∈ B' ∧
      B' ∩ {z | ‖P (z - x)‖ < s * h / 4} ⊆ insert x ({y | ‖P (y - x)‖ < s * ‖y - x‖} ∩
        Metric.ball x (3 * h) ∪ {y | ‖P (y - x')‖ < s * ‖y - x'‖} ∩ Metric.ball x' (3 * h)) := by
    intro x
    by_cases hx : x ∈ B''
    · obtain ⟨h, hh, hhδ, x', hx', hsub⟩ :=
        Submission.bf_coneMass_slab_cover (n + ℓ) P s (δ / 4) B' x hs hx.2 fun y hy ↦ by
          have h1 : dist y a < δ / 8 := hy.2
          have h2 : dist x a < δ / 8 := hx.1.2
          calc ‖y - x‖ = dist y x := (dist_eq_norm y x).symm
            _ ≤ dist y a + dist x a := dist_triangle_right y x a
            _ ≤ δ / 4 := by linarith
      exact ⟨h, x', fun _ ↦ ⟨hh, hhδ, hx', hsub⟩⟩
    · exact ⟨0, 0, fun h ↦ absurd h hx⟩
  choose h x' hhx using hslab
  -- Step 5: mass of a slab, by (H) at `x` and at `x' x` with `r = 3 h x < δ`, and `Hⁿ{x} = 0`.
  have hsingle : ∀ x : Rn (n + ℓ), μHE[n] ({x} : Set (Rn (n + ℓ))) = 0 := by
    intro x
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
    have := Measure.nullSingletonClass_hausdorff (Rn (n + ℓ))
      (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn)
    simp
  have hmass : ∀ x ∈ B'', μHE[n] (B' ∩ {z | ‖P (z - x)‖ < s * h x / 4}) ≤
      ENNReal.ofReal (2 * 60 ^ n * c) * ENNReal.ofReal ((s * h x / 20) ^ n) := by
    intro x hx
    obtain ⟨hh, hhδ, hx'B, hsub⟩ := hhx x hx
    have hr : 0 < 3 * h x := by linarith
    have hrδ : 3 * h x < δ := by linarith
    have hsub' : B' ∩ {z | ‖P (z - x)‖ < s * h x / 4} ⊆ {x} ∪
        ((B ∩ ({y | ‖W.starProjection (y - x)‖ < s * ‖y - x‖} ∩ Metric.ball x (3 * h x))) ∪
          (B ∩ ({y | ‖W.starProjection (y - x' x)‖ < s * ‖y - x' x‖} ∩
            Metric.ball (x' x) (3 * h x)))) := by
      intro z hz
      have hzB : z ∈ B := hz.1.1
      rcases hsub hz with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨hzB, h2⟩)
      · exact Or.inr (Or.inr ⟨hzB, h3⟩)
    calc μHE[n] (B' ∩ {z | ‖P (z - x)‖ < s * h x / 4})
        ≤ μHE[n] ({x} ∪
          ((B ∩ ({y | ‖W.starProjection (y - x)‖ < s * ‖y - x‖} ∩ Metric.ball x (3 * h x))) ∪
            (B ∩ ({y | ‖W.starProjection (y - x' x)‖ < s * ‖y - x' x‖} ∩
              Metric.ball (x' x) (3 * h x))))) := measure_mono hsub'
      _ ≤ μHE[n] ({x} : Set (Rn (n + ℓ))) +
          (μHE[n] (B ∩ ({y | ‖W.starProjection (y - x)‖ < s * ‖y - x‖} ∩ Metric.ball x (3 * h x))) +
            μHE[n] (B ∩ ({y | ‖W.starProjection (y - x' x)‖ < s * ‖y - x' x‖} ∩
              Metric.ball (x' x) (3 * h x)))) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ 0 + (ENNReal.ofReal (c * (3 * h x * s) ^ n) + ENNReal.ofReal (c * (3 * h x * s) ^ n)) := by
          gcongr
          · rw [hsingle]
          · exact hH x hx.1.1 _ hr hrδ
          · exact hH (x' x) hx'B.1 _ hr hrδ
      _ = ENNReal.ofReal (2 * 60 ^ n * c) * ENNReal.ofReal ((s * h x / 20) ^ n) := by
          rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [div_pow, mul_pow, mul_pow, mul_pow, show (60 : ℝ) ^ n = 3 ^ n * 20 ^ n by
            rw [← mul_pow]; norm_num]
          field_simp
          ring
  -- Step 6: Vitali `5r`-covering of the balls `B(Px, s h x / 20)`, `x ∈ B''` (`τ = 2`); the
  -- disjoint subfamily `T` is countable and its slabs cover `B''`.
  have hρ : ∀ x ∈ B'', 0 < s * h x / 20 := fun x hx ↦ by have := (hhx x hx).1; positivity
  obtain ⟨T, hTB, hTdisj, hTcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun x ↦ Metric.ball (P x) (s * h x / 20)) B'' (fun x ↦ s * h x / 20) 2 one_lt_two
    (fun x hx ↦ (hρ x hx).le) (s * δ / 80)
    (fun x hx ↦ by
      have h1 := (hhx x hx).2.1
      have h2 : s * h x ≤ s * (δ / 4) := mul_le_mul_of_nonneg_left h1 hs.le
      show s * h x / 20 ≤ s * δ / 80
      linarith)
    (fun x hx ↦ Metric.nonempty_ball.2 (hρ x hx))
  have hTc : T.Countable := hTdisj.countable_of_isOpen (fun _ _ ↦ Metric.isOpen_ball)
    (fun x hx ↦ Metric.nonempty_ball.2 (hρ x (hTB hx)))
  have hcov : B'' ⊆ ⋃ t ∈ T, B' ∩ {z | ‖P (z - t)‖ < s * h t / 4} := by
    intro x hx
    obtain ⟨t, htT, ⟨z, hz1, hz2⟩, hle⟩ := hTcov x hx
    have h1 : dist z (P x) < s * h x / 20 := hz1
    have h2 : dist z (P t) < s * h t / 20 := hz2
    have h3 : s * h x / 20 ≤ 2 * (s * h t / 20) := hle
    have hd : dist (P x) (P t) < 3 * (s * h t / 20) :=
      calc dist (P x) (P t) ≤ dist z (P x) + dist z (P t) := dist_triangle_left _ _ _
        _ < s * h x / 20 + s * h t / 20 := add_lt_add h1 h2
        _ ≤ 3 * (s * h t / 20) := by linarith
    have ht := (hhx t (hTB htT)).1
    refine mem_iUnion₂.2 ⟨t, htT, hx.1, ?_⟩
    show ‖P (x - t)‖ < s * h t / 4
    rw [map_sub, ← dist_eq_norm]
    have : 0 < s * h t := mul_pos hs ht
    linarith
  -- Step 7: packing the disjoint balls `B(Pt, s h t / 20) ⊆ B(Pa, δ/4)` centred in `W`.
  have hpack : ∑' t : T, ENNReal.ofReal ((s * h t / 20) ^ n) ≤ ENNReal.ofReal ((δ / 4) ^ n) :=
    Submission.bf_coneMass_subspace_ball_packing n (n + ℓ) W hW (Rn (n + ℓ)) T (fun x ↦ P x)
      (fun x ↦ s * h x / 20) (P a) (δ / 4) hTc (fun x _ ↦ W.starProjection_apply_mem x)
      (W.starProjection_apply_mem a) (fun x hx ↦ hρ x (hTB hx)) hTdisj
      (fun t ht ↦ by
        apply Metric.ball_subset_ball'
        have h1 : dist (P t) (P a) ≤ dist t a := by
          rw [dist_eq_norm, dist_eq_norm, ← map_sub]
          exact W.norm_starProjection_apply_le _
        have h2 : dist t a < δ / 8 := (hTB ht).1.2
        have h3 : h t ≤ δ / 4 := (hhx t (hTB ht)).2.1
        have h4 : s * h t ≤ 1 * (δ / 4) :=
          mul_le_mul hs1.le h3 (hhx t (hTB ht)).1.le zero_le_one
        show s * h t / 20 + dist (P t) (P a) ≤ δ / 4
        linarith)
  -- Steps 8–9: `Hⁿ(B') ≤ Hⁿ(B'') ≤ ∑_{t ∈ T} 2c·60ⁿ (s h t / 20)ⁿ ≤ 2c·60ⁿ (δ/4)ⁿ = 2·15ⁿ c δⁿ`.
  calc μHE[n] (B ∩ Metric.ball a (δ / 8)) = μHE[n] B' := rfl
    _ ≤ μHE[n] B'' + μHE[n] (B' \ B'') := by
        calc μHE[n] B' ≤ μHE[n] (B'' ∪ (B' \ B'')) := measure_mono fun x hx ↦ by
              by_cases hxx : x ∈ B''
              · exact Or.inl hxx
              · exact Or.inr ⟨hx, hxx⟩
          _ ≤ _ := measure_union_le _ _
    _ = μHE[n] B'' := by rw [hE, add_zero]
    _ ≤ μHE[n] (⋃ t ∈ T, B' ∩ {z | ‖P (z - t)‖ < s * h t / 4}) := measure_mono hcov
    _ ≤ ∑' t : T, μHE[n] (B' ∩ {z | ‖P (z - t)‖ < s * h t / 4}) := measure_biUnion_le _ hTc _
    _ ≤ ∑' t : T, ENNReal.ofReal (2 * 60 ^ n * c) * ENNReal.ofReal ((s * h t / 20) ^ n) :=
        ENNReal.tsum_le_tsum fun t ↦ hmass t (hTB t.2)
    _ = ENNReal.ofReal (2 * 60 ^ n * c) * ∑' t : T, ENNReal.ofReal ((s * h t / 20) ^ n) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (2 * 60 ^ n * c) * ENNReal.ofReal ((δ / 4) ^ n) := by gcongr
    _ = ENNReal.ofReal (2 * 15 ^ n * c * δ ^ n) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [div_pow, show (60 : ℝ) ^ n = 15 ^ n * 4 ^ n by rw [← mul_pow]; norm_num]
        field_simp

/-- **Vanishing cone density happens only on an `Hⁿ`-null set** (Steps 4–5 of the proof of
Simon Ch. 3, Theorem 3.6, `chapter-03.txt` lines 530–536, whose proof Simon defers to
[Fed69]/[Ros84]; Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, 15.15–15.16;
Dall'Alba, Cor. 4.7 and Lemma 5.2). Let `Z` be the set of `a ∈ A` where, for every `c > 0`,
`Hⁿ(A ∩ X(a, r, s)) ≤ c (rs)ⁿ` for all `0 < r < δ` and all small `s > 0`. Fix `c > 0` and `b`.
The points of `Z` where this bound holds for all `s < 1/(i+2)` form sets `Zᵢ ⊆ A` increasing to
`Z`; each `Zᵢ` is purely unrectifiable and satisfies the cone hypothesis of `bf_coneMass_ball_le`
with aperture `1/(2(i+2))`, so `Hⁿ(Zᵢ ∩ B(b, δ/8)) ≤ 2·15ⁿ c δⁿ`. Continuity from below (valid for
arbitrary sets) gives the same bound for `Z ∩ B(b, δ/8)`, which is therefore null (`c ↓ 0`), and
`Z` is covered by countably many such balls. -/
theorem Submission.bf_coneDensity_zero_null : ∀ (n ℓ : ℕ), 0 < n →
    ∀ (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∀ A : Set (Rn (n + ℓ)),
    PurelyUnrectifiable n A → ∀ δ : ℝ, 0 < δ →
    μHE[n] {a | a ∈ A ∧ ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
      ∀ r : ℝ, 0 < r → r < δ →
        μHE[n] (A ∩ ({x | ‖W.starProjection (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r)) ≤
          ENNReal.ofReal (c * (r * s) ^ n)} = 0 := by
  intro n ℓ hn W hW A hA δ hδ
  set Z := {a | a ∈ A ∧ ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
    ∀ r : ℝ, 0 < r → r < δ →
      μHE[n] (A ∩ ({x | ‖W.starProjection (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r)) ≤
        ENNReal.ofReal (c * (r * s) ^ n)}
  -- Steps 1–3: for `c > 0`, `Hⁿ(Z ∩ B(b, δ/8)) ≤ 2·15ⁿ c δⁿ`.
  have hbound : ∀ c : ℝ, 0 < c → ∀ b : Rn (n + ℓ),
      μHE[n] (Z ∩ Metric.ball b (δ / 8)) ≤ ENNReal.ofReal (2 * 15 ^ n * c * δ ^ n) := by
    intro c hc b
    -- `Zᵢ`: the points of `Z` where the bound holds for all `s < 1/(i+2)`.
    set Zi : ℕ → Set (Rn (n + ℓ)) := fun i ↦ {a | a ∈ Z ∧ ∀ s : ℝ, 0 < s → s < 1 / (i + 2) →
      ∀ r : ℝ, 0 < r → r < δ →
        μHE[n] (A ∩ ({x | ‖W.starProjection (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r)) ≤
          ENNReal.ofReal (c * (r * s) ^ n)}
    have hZiA : ∀ i, Zi i ⊆ A := fun i a ha ↦ ha.1.1
    have hmono : Monotone fun i ↦ Zi i ∩ Metric.ball b (δ / 8) := by
      intro i j hij a ha
      refine ⟨⟨ha.1.1, fun s hs hsj r hr hrδ ↦ ha.1.2 s hs (hsj.trans_le ?_) r hr hrδ⟩, ha.2⟩
      have hij' : (i : ℝ) ≤ j := Nat.cast_le.2 hij
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    -- The `Zᵢ` exhaust `Z`: if the bound holds for `s < ε` and `1/(i+1) < ε`, then `a ∈ Zᵢ`.
    have hunion : (⋃ i, Zi i ∩ Metric.ball b (δ / 8)) = Z ∩ Metric.ball b (δ / 8) := by
      refine Subset.antisymm (iUnion_subset fun i ↦ inter_subset_inter_left _ fun a ha ↦ ha.1) ?_
      rintro a ⟨haZ, hab⟩
      obtain ⟨ε, hε, hεs⟩ := haZ.2 c hc
      obtain ⟨i, hi⟩ := exists_nat_one_div_lt hε
      refine mem_iUnion.2 ⟨i, ⟨haZ, fun s hs hsi r hr hrδ ↦ hεs s hs ?_ r hr hrδ⟩, hab⟩
      calc s < 1 / ((i : ℝ) + 2) := hsi
        _ ≤ 1 / ((i : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) (by linarith)
        _ < ε := hi
    -- Each `Zᵢ` satisfies the hypotheses of `bf_coneMass_ball_le` with `s = 1/(2(i+2))`.
    have hZi_bound : ∀ i : ℕ,
        μHE[n] (Zi i ∩ Metric.ball b (δ / 8)) ≤ ENNReal.ofReal (2 * 15 ^ n * c * δ ^ n) := by
      intro i
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have hs0 : (0 : ℝ) < 1 / (2 * ((i : ℝ) + 2)) := by positivity
      have hsi : 1 / (2 * ((i : ℝ) + 2)) < 1 / ((i : ℝ) + 2) :=
        one_div_lt_one_div_of_lt (by positivity) (by linarith)
      have hs1 : 1 / (2 * ((i : ℝ) + 2)) < 1 := (div_lt_one (by positivity)).2 (by linarith)
      refine Submission.bf_coneMass_ball_le n ℓ hn W hW _ δ c hs0 hs1 hδ hc.le (Zi i)
        (hA.mono (hZiA i)) ?_ b
      intro x hx r hr hrδ
      exact (measure_mono (inter_subset_inter_left _ (hZiA i))).trans (hx.2 _ hs0 hsi r hr hrδ)
    rw [← hunion, hmono.measure_iUnion]
    exact iSup_le hZi_bound
  -- Step 4: letting `c ↓ 0`, `Hⁿ(Z ∩ B(b, δ/8)) = 0`.
  have hnull : ∀ b : Rn (n + ℓ), μHE[n] (Z ∩ Metric.ball b (δ / 8)) = 0 := by
    intro b
    have hlim : Tendsto (fun c : ℝ ↦ ENNReal.ofReal (2 * 15 ^ n * c * δ ^ n)) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun c : ℝ ↦ 2 * 15 ^ n * c * δ ^ n) (𝓝 0) (𝓝 0) :=
        (by fun_prop : Continuous fun c : ℝ ↦ 2 * 15 ^ n * c * δ ^ n).tendsto' 0 0 (by simp)
      rw [← ENNReal.ofReal_zero]
      exact (ENNReal.tendsto_ofReal h).mono_left nhdsWithin_le_nhds
    exact le_antisymm
      (ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun c hc ↦ hbound c hc b)) zero_le
  -- Step 5: every point of `Z` has the null neighbourhood `Z ∩ B(a, δ/8)` in `Z`.
  exact measure_null_of_locally_null Z fun a _ ↦ ⟨Z ∩ Metric.ball a (δ / 8),
    inter_mem_nhdsWithin Z (Metric.ball_mem_nhds a (div_pos hδ (by norm_num))), hnull a⟩
/-- **Hausdorff measure of closed discs in an `n`-plane** (Simon Ch. 1, Theorem 2.9,
`chapter-01.txt` lines 445–470: `Lⁿ = Hⁿ` on `ℝⁿ`, transported to an `n`-dimensional subspace).
For a subspace `W ⊆ ℝᴺ` with `dim W = n`, `ω = Hⁿ(W ∩ B̄(0, 1)) < ∞` and
`Hⁿ(W ∩ B̄(y, ρ)) = ρⁿ ω` for every `y ∈ W` and `ρ ≥ 0`. The inclusion `W → ℝᴺ` is an isometry
mapping the intrinsic ball `B̄_W(y, ρ)` onto `W ∩ B̄(y, ρ)`, and `μHE[n]` on `W` is an additive
Haar measure, finite on the compact unit ball and scaling closed balls by `ρⁿ`. -/
theorem Submission.bf_plane_closedBall_measure_eq : ∀ (n N : ℕ) (W : Submodule ℝ (Rn N)), finrank ℝ W = n → μHE[n] ((W : Set (Rn N)) ∩ Metric.closedBall 0 1) < ∞ ∧ ∀ y ∈ W, ∀ ρ : ℝ, 0 ≤ ρ → μHE[n] ((W : Set (Rn N)) ∩ Metric.closedBall y ρ) = ENNReal.ofReal (ρ ^ n) * μHE[n] ((W : Set (Rn N)) ∩ Metric.closedBall 0 1) := by
  intro n N W hW
  subst hW
  -- The ambient disc `W ∩ B̄(y, ρ)` is the image of the intrinsic ball `B̄_W(y, ρ)`.
  have himg : ∀ (y : W) (ρ : ℝ), (W : Set (Rn N)) ∩ Metric.closedBall (y : Rn N) ρ =
      Subtype.val '' Metric.closedBall y ρ := by
    intro y ρ
    ext x
    constructor
    · rintro ⟨hxW, hx⟩
      exact ⟨⟨x, hxW⟩, by simpa [Metric.mem_closedBall, Subtype.dist_eq] using hx, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, by simpa [Metric.mem_closedBall, Subtype.dist_eq] using hz⟩
  -- The inclusion is an isometry, so `Hⁿ(W ∩ B̄(y, ρ))` is the intrinsic `μHE[n]` of the ball.
  have hmeas : ∀ (y : W) (ρ : ℝ),
      μHE[finrank ℝ W] ((W : Set (Rn N)) ∩ Metric.closedBall (y : Rn N) ρ) =
        (μHE[finrank ℝ W] : Measure W) (Metric.closedBall y ρ) := by
    intro y ρ
    rw [himg, isometry_subtype_coe.euclideanHausdorffMeasure_image]
  have h01 := hmeas 0 1
  simp only [ZeroMemClass.coe_zero] at h01
  refine ⟨?_, ?_⟩
  · -- `μHE[n]` is an additive Haar measure on `W`, hence finite on the compact unit ball.
    rw [h01]
    exact (isCompact_closedBall _ _).measure_lt_top
  · -- Scaling of closed balls under the additive Haar measure `μHE[n]` on `W`.
    intro y hy ρ hρ
    rw [show y = ((⟨y, hy⟩ : W) : Rn N) from rfl, hmeas ⟨y, hy⟩ ρ, h01,
      Measure.addHaar_closedBall' _ _ hρ]
/-- Vitali covering for `Hⁿ` by closed discs in an `n`-plane `W ⊆ ℝᴺ`: the Symmetric Vitali
Property of Simon Ch. 1, Def. 3.10, for the doubling measure `Hⁿ ⌞ W` (`chapter-01.txt` lines
765–799; Remark 3.11(2) derives it from the 5-times covering lemma 3.4 and Corollary 3.5, lines
609–660). If the discs `W ∩ B̄(c i, ρ i)` (`i ∈ t`, `c i ∈ W`, `ρ i > 0`) cover an arbitrary
`S ⊆ W` finely, then countably many pairwise disjoint ones cover `Hⁿ`-almost all of `S`. As
`Hⁿ(W) = ∞` for `n ≥ 1`, Simon's finite-mass hypothesis is unavailable; we use instead the locally
finite form `Vitali.exists_disjoint_covering_ae` on the subtype `W`, where `μHE[finrank W]` is an
additive Haar measure whose closed balls are `3ⁿ`-doubling (`Measure.addHaar_closedBall'`), and
transfer the result along the isometric inclusion `W → ℝᴺ`. -/
theorem Submission.bf_plane_vitali_disjoint_cover : ∀ (n N : ℕ) (W : Submodule ℝ (Rn N)),
    finrank ℝ W = n → ∀ (ι : Type) (S : Set (Rn N)) (t : Set ι) (c : ι → Rn N) (ρ : ι → ℝ),
      S ⊆ (W : Set (Rn N)) → (∀ i ∈ t, c i ∈ W ∧ 0 < ρ i) →
        (∀ x ∈ S, ∀ ε : ℝ, 0 < ε → ∃ i ∈ t, c i = x ∧ ρ i ≤ ε) →
          ∃ u ⊆ t, u.Countable ∧
            u.PairwiseDisjoint (fun i ↦ (W : Set (Rn N)) ∩ Metric.closedBall (c i) (ρ i)) ∧
            μHE[n] (S \ ⋃ i ∈ u, ((W : Set (Rn N)) ∩ Metric.closedBall (c i) (ρ i))) = 0 := by
  intro n N W hW ι S t c ρ hSW hct hfine
  -- work intrinsically on the subtype `W`, with `n = finrank W`
  subst hW
  classical
  set μ : Measure W := μHE[finrank ℝ W]
  -- lifted centres `c' i ∈ W` and balls `B i = B̄_W(c' i, ρ i)`
  let c' : ι → W := fun i ↦ if h : c i ∈ W then ⟨c i, h⟩ else 0
  have hc' : ∀ i ∈ t, (c' i : Rn N) = c i := by
    intro i hi
    simp [c', (hct i hi).1]
  let B : ι → Set W := fun i ↦ Metric.closedBall (c' i) (ρ i)
  -- the inclusion maps `B i` onto the disc `W ∩ B̄(c i, ρ i)`
  have himg : ∀ i ∈ t, Subtype.val '' B i = (W : Set (Rn N)) ∩ Metric.closedBall (c i) (ρ i) := by
    intro i hi
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, ?_⟩
      have : dist z (c' i) ≤ ρ i := hz
      rwa [Subtype.dist_eq, hc' i hi] at this
    · rintro ⟨hxW, hx⟩
      refine ⟨⟨x, hxW⟩, ?_, rfl⟩
      show dist (⟨x, hxW⟩ : W) (c' i) ≤ ρ i
      rwa [Subtype.dist_eq, hc' i hi]
  -- hypotheses of the Vitali theorem: doubling with constant `3ⁿ`, nonempty interiors,
  -- closedness and fineness at the preimage `S'` of `S` in `W`
  have hdoub : ∀ i ∈ t, μ (Metric.closedBall (c' i) (3 * ρ i)) ≤
      ((3 ^ finrank ℝ W : ℝ≥0) : ℝ≥0∞) * μ (B i) := by
    intro i hi
    have hρ : 0 ≤ ρ i := (hct i hi).2.le
    rw [Measure.addHaar_closedBall' μ _ (by positivity), Measure.addHaar_closedBall' μ _ hρ,
      mul_pow, ENNReal.ofReal_mul (by positivity), mul_assoc]
    gcongr
    rw [ENNReal.ofReal_pow (by norm_num)]
    simp
  have hint : ∀ i ∈ t, (interior (B i)).Nonempty := fun i hi ↦
    ⟨c' i, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self (hct i hi).2)⟩
  have hclosed : ∀ i ∈ t, IsClosed (B i) := fun i _ ↦ Metric.isClosed_closedBall
  have hfine' : ∀ x ∈ (Subtype.val ⁻¹' S : Set W), ∀ ε > (0 : ℝ), ∃ a ∈ t, ρ a ≤ ε ∧ c' a = x := by
    intro x hx ε hε
    obtain ⟨i, hi, hcx, hρε⟩ := hfine x hx ε hε
    exact ⟨i, hi, hρε, Subtype.ext (by rw [hc' i hi, hcx])⟩
  obtain ⟨u, hut, hu, hdisj, hnull⟩ := Vitali.exists_disjoint_covering_ae μ (Subtype.val ⁻¹' S) t
    (3 ^ finrank ℝ W) ρ c' B (fun i _ ↦ subset_rfl) hdoub hint hclosed hfine'
  refine ⟨u, hut, hu, ?_, ?_⟩
  -- the inclusion is injective, so the discs are pairwise disjoint
  · intro i hi j hj hij
    simp only [Function.onFun]
    rw [← himg i (hut hi), ← himg j (hut hj)]
    exact (disjoint_image_iff Subtype.val_injective).mpr (hdisj hi hj hij)
  -- `S \ ⋃ discs` is the image of `S' \ ⋃ B i`, and the inclusion preserves `μHE[n]`
  · have hset : S \ ⋃ i ∈ u, ((W : Set (Rn N)) ∩ Metric.closedBall (c i) (ρ i)) =
        Subtype.val '' ((Subtype.val ⁻¹' S : Set W) \ ⋃ i ∈ u, B i) := by
      ext x
      constructor
      · rintro ⟨hxS, hxU⟩
        refine ⟨⟨x, hSW hxS⟩, ⟨hxS, fun hmem ↦ hxU ?_⟩, rfl⟩
        obtain ⟨i, hi, hiB⟩ := mem_iUnion₂.1 hmem
        exact mem_iUnion₂.2 ⟨i, hi, himg i (hut hi) ▸ ⟨_, hiB, rfl⟩⟩
      · rintro ⟨z, ⟨hzS, hzU⟩, rfl⟩
        refine ⟨hzS, fun hmem ↦ hzU ?_⟩
        obtain ⟨i, hi, hiD⟩ := mem_iUnion₂.1 hmem
        rw [← himg i (hut hi)] at hiD
        obtain ⟨w, hw, hwz⟩ := hiD
        exact mem_iUnion₂.2 ⟨i, hi, Subtype.ext hwz ▸ hw⟩
    rw [hset, isometry_subtype_coe.euclideanHausdorffMeasure_image]
    exact hnull

/-- **Infinite cone density has `Hⁿ`-null projection** (M. G. Dall'Alba, *The Besicovitch–Federer
Projection Theorem*, Lemma 5.3; P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*,
Ch. 18). Let `W ⊆ ℝ^{n+ℓ}` be an `n`-plane with orthogonal projection `P`, `A` compact with
`Hⁿ(A) < ∞`, `δ > 0`, and `A₂` the set of `a ∈ A` with infinite cone density `Φ_δ(a, W^⊥)`: for
every `K` and `ε > 0` there are `0 < s < ε`, `0 < r < δ` with `K (rs)ⁿ ≤ Hⁿ(A ∩ X(a, r, s))`, where
`X(a, r, s) = {x : |P(x - a)| < s |x - a|} ∩ B_r(a)`. Then `Hⁿ(P(A₂)) = 0`. For fixed `K > 0` the
discs `W ∩ B̄(P a, rs)` cover `P(A₂)` finely, so countably many disjoint ones cover `Hⁿ`-almost all
of it (`bf_plane_vitali_disjoint_cover`). The cone pieces `A ∩ X(a, r, s)` project into their
discs, hence are disjoint Borel subsets of `A`, and with `ω = Hⁿ(W ∩ B̄(0, 1))`
(`bf_plane_closedBall_measure_eq`), `Hⁿ(P(A₂)) ≤ Σ ω (rs)ⁿ ≤ (ω / K) Hⁿ(A) → 0` as `K → ∞`. -/
theorem Submission.bf_coneDensity_top_projection_null : ∀ (n ℓ : ℕ), 0 < n → ∀ (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∀ A : Set (Rn (n + ℓ)), IsCompact A → μHE[n] A < ∞ → ∀ δ : ℝ, 0 < δ → μHE[n] (W.starProjection '' {a | a ∈ A ∧ ∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μHE[n] (A ∩ ({x | ‖W.starProjection (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r))}) = 0 := by
  intro n ℓ _hn W hW A hA hAfin δ hδ
  set P := W.starProjection
  set A₂ := {a | a ∈ A ∧ ∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧
    r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤
      μHE[n] (A ∩ ({x | ‖P (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r))}
  set T := P '' A₂
  obtain ⟨hωfin, hball⟩ := Submission.bf_plane_closedBall_measure_eq n (n + ℓ) W hW
  set ω := μHE[n] ((W : Set (Rn (n + ℓ))) ∩ Metric.closedBall 0 1)
  have hTW : T ⊆ (W : Set (Rn (n + ℓ))) := by
    rintro _ ⟨b, -, rfl⟩
    exact W.starProjection_apply_mem b
  -- Step 1: a point `a y ∈ A₂` over each `y ∈ P(A₂)`
  have hpre : ∀ y ∈ T, ∃ a, a ∈ A₂ ∧ P a = y := fun y hy ↦ hy
  choose! a ha using hpre
  -- the cone pieces `A ∩ X(b, r, s)` are Borel
  let X : Rn (n + ℓ) → ℝ → ℝ → Set (Rn (n + ℓ)) := fun b r s ↦
    {x | ‖P (x - b)‖ < s * ‖x - b‖} ∩ Metric.ball b r
  have hXmeas : ∀ b r s, MeasurableSet (A ∩ X b r s) := by
    intro b r s
    refine hA.isClosed.measurableSet.inter (IsOpen.measurableSet ?_)
    refine IsOpen.inter (isOpen_lt ?_ ?_) Metric.isOpen_ball
    · exact (P.continuous.comp (continuous_id.sub continuous_const)).norm
    · exact continuous_const.mul (continuous_id.sub continuous_const).norm
  -- Step 4: `|P x - y| = |P(x - a y)| < s |x - a y| < rs`, so `P(X(a y, r, s)) ⊆ W ∩ B̄(y, rs)`
  have hXproj : ∀ y ∈ T, ∀ r s : ℝ, 0 < s → ∀ x ∈ X (a y) r s,
      P x ∈ (W : Set (Rn (n + ℓ))) ∩ Metric.closedBall y (r * s) := by
    intro y hy r s hs x hx
    refine ⟨W.starProjection_apply_mem x, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm,
      show P x - y = P (x - a y) by rw [map_sub, (ha y hy).2]]
    have h2 : ‖x - a y‖ < r := by simpa [dist_eq_norm] using hx.2
    have h3 : ‖P (x - a y)‖ < s * ‖x - a y‖ := hx.1
    nlinarith [norm_nonneg (x - a y)]
  -- Steps 1–5 for a fixed `K > 0`: `Hⁿ(P(A₂)) ≤ (ω / K) Hⁿ(A)`
  have key : ∀ K : ℝ, 0 < K → μHE[n] T ≤ ω / ENNReal.ofReal K * μHE[n] A := by
    intro K hK
    let t : Set (Rn (n + ℓ) × ℝ × ℝ) := {i | i.1 ∈ T ∧ 0 < i.2.1 ∧ i.2.1 < δ ∧ 0 < i.2.2 ∧
      ENNReal.ofReal (K * (i.2.1 * i.2.2) ^ n) ≤ μHE[n] (A ∩ X (a i.1) i.2.1 i.2.2)}
    -- Step 2: fineness, with `ε / δ` in the definition of `A₂`
    have hfine : ∀ x ∈ T, ∀ ε : ℝ, 0 < ε → ∃ i ∈ t, i.1 = x ∧ i.2.1 * i.2.2 ≤ ε := by
      intro x hx ε hε
      obtain ⟨s, hs0, hsε, r, hr0, hrδ, hK'⟩ := (ha x hx).1.2 K (ε / δ) (div_pos hε hδ)
      refine ⟨(x, r, s), ⟨hx, hr0, hrδ, hs0, hK'⟩, rfl, ?_⟩
      have : r * s ≤ δ * (ε / δ) := mul_le_mul hrδ.le hsε.le hs0.le hδ.le
      rwa [mul_div_cancel₀ _ hδ.ne'] at this
    -- Step 3: a disjoint Vitali subfamily of discs covering `Hⁿ`-almost all of `P(A₂)`
    obtain ⟨u, hut, hu, hdisj, hnull⟩ := Submission.bf_plane_vitali_disjoint_cover n (n + ℓ) W hW
      (Rn (n + ℓ) × ℝ × ℝ) T t (fun i ↦ i.1) (fun i ↦ i.2.1 * i.2.2) hTW
      (fun i hi ↦ ⟨hTW hi.1, mul_pos hi.2.1 hi.2.2.2.1⟩) hfine
    let D : Rn (n + ℓ) × ℝ × ℝ → Set (Rn (n + ℓ)) := fun i ↦
      (W : Set (Rn (n + ℓ))) ∩ Metric.closedBall i.1 (i.2.1 * i.2.2)
    let Sp : Rn (n + ℓ) × ℝ × ℝ → Set (Rn (n + ℓ)) := fun i ↦ A ∩ X (a i.1) i.2.1 i.2.2
    -- Step 4: the cone pieces project into the disjoint discs, so they are disjoint
    have hSdisj : u.PairwiseDisjoint Sp := by
      intro i hi j hj hij
      refine Set.disjoint_left.2 fun x hxi hxj ↦ ?_
      have hi' := hut hi
      have hj' := hut hj
      exact Set.disjoint_left.1 (hdisj hi hj hij)
        (hXproj i.1 hi'.1 i.2.1 i.2.2 hi'.2.2.2.1 x hxi.2)
        (hXproj j.1 hj'.1 j.2.1 j.2.2 hj'.2.2.2.1 x hxj.2)
    -- Step 5: `Hⁿ(D_i) = ω (rs)ⁿ ≤ (ω / K) Hⁿ(S_i)`
    have hDle : ∀ i ∈ u, μHE[n] (D i) ≤ ω / ENNReal.ofReal K * μHE[n] (Sp i) := by
      intro i hi
      have hi' := hut hi
      have hK1 : ENNReal.ofReal K * ENNReal.ofReal ((i.2.1 * i.2.2) ^ n) ≤ μHE[n] (Sp i) := by
        rw [← ENNReal.ofReal_mul hK.le]
        exact hi'.2.2.2.2
      have hKpos : ENNReal.ofReal K ≠ 0 := by simpa using hK
      calc μHE[n] (D i) = ENNReal.ofReal ((i.2.1 * i.2.2) ^ n) * ω :=
            hball i.1 (hTW hi'.1) _ (mul_pos hi'.2.1 hi'.2.2.2.1).le
        _ = ω / ENNReal.ofReal K * (ENNReal.ofReal K * ENNReal.ofReal ((i.2.1 * i.2.2) ^ n)) := by
            rw [← mul_assoc, ENNReal.div_mul_cancel hKpos ENNReal.ofReal_ne_top, mul_comm]
        _ ≤ ω / ENNReal.ofReal K * μHE[n] (Sp i) := by gcongr
    calc μHE[n] T ≤ μHE[n] (T \ ⋃ i ∈ u, D i) + μHE[n] (⋃ i ∈ u, D i) := by
          refine (measure_mono fun x hx ↦ ?_).trans (measure_union_le _ _)
          by_cases hxU : x ∈ ⋃ i ∈ u, D i
          · exact Or.inr hxU
          · exact Or.inl ⟨hx, hxU⟩
      _ = μHE[n] (⋃ i ∈ u, D i) := by rw [hnull, zero_add]
      _ ≤ ∑' i : u, μHE[n] (D i) := measure_biUnion_le _ hu _
      _ ≤ ∑' i : u, ω / ENNReal.ofReal K * μHE[n] (Sp i) :=
          ENNReal.tsum_le_tsum fun i ↦ hDle i i.2
      _ = ω / ENNReal.ofReal K * ∑' i : u, μHE[n] (Sp i) := ENNReal.tsum_mul_left
      _ = ω / ENNReal.ofReal K * μHE[n] (⋃ i ∈ u, Sp i) := by
          rw [measure_biUnion hu hSdisj fun i _ ↦ hXmeas _ _ _]
      _ ≤ ω / ENNReal.ofReal K * μHE[n] A := by
          gcongr
          exact iUnion₂_subset fun i _ ↦ inter_subset_left
  -- Step 6: let `K → ∞`, using `ω < ∞` and `Hⁿ(A) < ∞`
  have hlim : Tendsto (fun K : ℝ ↦ ω / ENNReal.ofReal K * μHE[n] A) atTop (𝓝 0) := by
    have h2 : Tendsto (fun K : ℝ ↦ ω / ENNReal.ofReal K) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_div ENNReal.tendsto_ofReal_atTop (Or.inr hωfin.ne)
    simpa using ENNReal.Tendsto.mul_const h2 (Or.inr hAfin.ne)
  exact nonpos_iff_eq_zero.mp
    (ge_of_tendsto hlim (by filter_upwards [eventually_gt_atTop 0] with K hK using key K hK))
/-- **Simon Ch. 1, §2 (p. 10)** (`chapter-01.txt` lines 411–412), the `H⁰` of Ch. 3 (2.4):
`H⁰` is counting measure, i.e. `H⁰(S) = #S` for every `S ⊆ ℝᴺ`, with `H⁰(S) = ∞` for infinite `S`.
Since `μHE[0] = μH[0]` and `μH[0]{x} = 1`, additivity over the measurable singletons gives
`H⁰(t) = #t` for finite `t`; an infinite `S` contains `⌈r⌉` points for every `r ≥ 0`, so
`H⁰(S) = ∞` by monotonicity. -/
theorem Submission.bf_hausdorffZero_eq_encard :
    ∀ (N : ℕ) (S : Set (Rn N)), μHE[0] S = (S.encard : ℝ≥0∞) := by
  intro N S
  rw [Measure.euclideanHausdorffMeasure_zero]
  -- Finite sets: sum the unit masses of the measurable singletons.
  have hfin : ∀ t : Finset (Rn N), μH[0] (t : Set (Rn N)) = t.card := by
    intro t
    rw [← sum_measure_singleton]
    simp
  rcases S.finite_or_infinite with hS | hS
  · lift S to Finset (Rn N) using hS
    rw [hfin, Set.encard_coe_eq_coe_finsetCard]
    rfl
  -- Infinite sets: `S` contains `⌈r⌉₊` points for every `r`, so `μH[0] S` is unbounded.
  · rw [Set.encard_eq_top_iff.mpr hS, ENat.toENNReal_top]
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    obtain ⟨t, hts, htc⟩ := hS.exists_subset_card_eq ⌈r⌉₊
    calc (r : ℝ≥0∞) ≤ (⌈r⌉₊ : ℝ≥0∞) := by exact_mod_cast Nat.le_ceil r
      _ = μH[0] (t : Set (Rn N)) := by rw [hfin, htc]
      _ ≤ μH[0] S := measure_mono hts
/-- **Isometric chart of the orthogonal projection onto an `n`-plane** (Dall'Alba, *The
Besicovitch–Federer Projection Theorem*, Lemma 5.4, p. 70, made explicit). For a subspace
`W ⊆ ℝ^{n+ℓ}` with `dim W = n` and `P = W.starProjection`, there is a `1`-Lipschitz
`f : ℝ^{n+ℓ} → ℝⁿ` with the fibres of `P` and `Hⁿ(P(S)) = Lⁿ(f(S))` for every set `S`. Take
`f = ι ∘ π` with `π` the orthogonal projection onto `W` and `ι : W ≃ ℝⁿ` the coordinate map of
an orthonormal basis; then `P = J ∘ f` for the isometry `J = ↑ ∘ ι⁻¹`, and `μHE[n]` is
isometry invariant and equals `volume` on `ℝⁿ`. -/
theorem Submission.bf_starProjection_isometricChart : ∀ (n ℓ : ℕ) (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∃ f : Rn (n + ℓ) → Rn n, LipschitzWith 1 f ∧ (∀ a b : Rn (n + ℓ), f a = f b ↔ W.starProjection a = W.starProjection b) ∧ ∀ S : Set (Rn (n + ℓ)), μHE[n] (W.starProjection '' S) = volume (f '' S) := by
  intro n ℓ W hW
  -- `ι : W ≃ ℝⁿ`, the coordinate map of an orthonormal basis of `W` indexed by `Fin n`.
  let ι : W ≃ₗᵢ[ℝ] Rn n := ((stdOrthonormalBasis ℝ W).reindex (finCongr hW)).repr
  refine ⟨fun x ↦ ι (W.orthogonalProjectionOnto x), ?_, ?_, ?_⟩
  · -- (i) `π` has operator norm `≤ 1` and `ι` is an isometry.
    have h := ι.lipschitzWith.comp W.lipschitzWith_orthogonalProjectionOnto
    rw [one_mul] at h
    exact h
  · -- (ii) `f a = f b ↔ π a = π b ↔ P a = P b`, by injectivity of `ι` and of the inclusion.
    intro a b
    rw [ι.injective.eq_iff, Submodule.starProjection_apply, Submodule.starProjection_apply,
      SetLike.coe_eq_coe]
  · -- (iii) `P = J ∘ f` with `J = ↑ ∘ ι⁻¹` an isometry, and `μHE[n] = volume` on `ℝⁿ`.
    intro S
    have hJ : Isometry (fun y : Rn n ↦ ((ι.symm y : W) : Rn (n + ℓ))) :=
      isometry_subtype_coe.comp ι.symm.isometry
    have hP : W.starProjection '' S =
        (fun y : Rn n ↦ ((ι.symm y : W) : Rn (n + ℓ))) ''
          ((fun x ↦ ι (W.orthogonalProjectionOnto x)) '' S) := by
      rw [Set.image_image]
      refine Set.image_congr fun x _ ↦ ?_
      rw [LinearIsometryEquiv.symm_apply_apply, Submodule.starProjection_apply]
    rw [hP, hJ.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]

/-- **Infinite fibres of an `n`-plane projection project to an `Hⁿ`-null set** (Dall'Alba,
*The Besicovitch–Federer Projection Theorem*, Lemma 5.4, p. 70), assuming Eilenberg's
inequality (Eil). Let `P = W.starProjection`, `dim W = n`, `Hⁿ(A) < ∞` and
`A₃ = {a ∈ A : {b ∈ A : P b = P a} infinite}`. With the `1`-Lipschitz chart `f` of `P`, (Eil)
for `(N, m, k) = (n + ℓ, n, 0)` and `L = 1` gives a measurable `g ≥ H⁰(A ∩ f⁻¹{y})` with
`∫ g dLⁿ ≤ C Hⁿ(A) < ∞`, so `g < ∞` `Lⁿ`-a.e. As `H⁰` is counting measure, `g = ∞` on
`f(A₃)`, hence `Hⁿ(P(A₃)) = Lⁿ(f(A₃)) = 0`. -/
theorem Submission.bf_infiniteFibre_projection_null : (∀ (N m k : ℕ), ∃ C : ℝ≥0, ∀ (A : Set (Rn N)) (f : Rn N → Rn m) (L : ℝ≥0), LipschitzWith L f → ∃ g : Rn m → ℝ≥0∞, Measurable g ∧ (∀ y, μHE[k] (A ∩ f ⁻¹' {y}) ≤ g y) ∧ ∫⁻ y, g y ≤ ((C * L ^ m : ℝ≥0) : ℝ≥0∞) * μHE[m + k] A) → ∀ (n ℓ : ℕ) (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∀ A : Set (Rn (n + ℓ)), μHE[n] A < ∞ → μHE[n] (W.starProjection '' {a | a ∈ A ∧ {b | b ∈ A ∧ W.starProjection b = W.starProjection a}.Infinite}) = 0 := by
  intro hEil n ℓ W hW A hA
  -- The chart `f`: `1`-Lipschitz, with the fibres of `P` and `Hⁿ(P(S)) = Lⁿ(f(S))`.
  obtain ⟨f, hf, hfib, hvol⟩ := Submission.bf_starProjection_isometricChart n ℓ W hW
  -- (Eil) with `(N, m, k) = (n + ℓ, n, 0)` and `L = 1`.
  obtain ⟨C, hC⟩ := hEil (n + ℓ) n 0
  obtain ⟨g, hg, hgle, hgint⟩ := hC A f 1 hf
  -- `∫ g dLⁿ ≤ C Hⁿ(A) < ∞`, so `{g = ∞}` is `Lⁿ`-null.
  have hnull : volume {y | ¬g y < ∞} = 0 :=
    ae_iff.mp (ae_lt_top hg
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hA.ne) hgint))
  -- `f(A₃) ⊆ {g = ∞}`: the fibre of `f` through `a ∈ A₃` meets `A` in infinitely many points.
  rw [hvol]
  refine measure_mono_null ?_ hnull
  rintro _ ⟨a, ⟨-, hinf⟩, rfl⟩
  have hfibre : A ∩ f ⁻¹' {f a} = {b | b ∈ A ∧ W.starProjection b = W.starProjection a} := by
    ext b
    simp [hfib]
  have hfa := hgle (f a)
  rw [hfibre, Submission.bf_hausdorffZero_eq_encard, Set.encard_eq_top_iff.mpr hinf,
    ENat.toENNReal_top] at hfa
  exact not_lt.mpr hfa

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
