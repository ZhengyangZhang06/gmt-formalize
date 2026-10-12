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

/-- **Exhaustion of an open set by open sets with compact closure inside it** (localization step
in the proof of Simon Ch. 3, Thm. 4.3): every open `U ⊆ ℝᴺ` is the union of the open sets
`W_i = {y : |y| < i, 1/i < d(y)}` (with `1/0 = ∞`), where `d = infEDist(·, ℝᴺ ∖ U)` is the
continuous extended distance to the complement. `closure W_i` lies in the closed set
`K_i = {y : |y| ≤ i, 1/i ≤ d(y)}`, which is contained in the compact ball `B̄_i(0)` and in `U`
(`d` vanishes off `U`). Every `y ∈ U` has `d(y) > 0`, since `ℝᴺ ∖ U` is closed, so `y ∈ W_i`
for large `i`. -/
theorem Submission.deGiorgiRH_open_exhaustion : ∀ (N : ℕ) (U : Set (Rn N)), IsOpen U → ∃ W : ℕ → Set (Rn N), (∀ i, IsOpen (W i) ∧ IsCompact (closure (W i)) ∧ closure (W i) ⊆ U) ∧ ⋃ i, W i = U := by
  intro N U hU
  -- `1/i ≤ d(y)` forces `y ∈ U`: `d` vanishes on `ℝᴺ ∖ U`, while `1/i > 0` (`1/i ≠ 0` as `i ≠ ∞`).
  have hKU : ∀ (i : ℕ) (y : Rn N), (i : ℝ≥0∞)⁻¹ ≤ Metric.infEDist y Uᶜ → y ∈ U := by
    intro i y hy
    by_contra hyU
    rw [Metric.infEDist_zero_of_mem hyU, nonpos_iff_eq_zero, ENNReal.inv_eq_zero] at hy
    exact ENNReal.natCast_ne_top i hy
  refine ⟨fun i ↦ {y | ‖y‖ < (i : ℝ) ∧ (i : ℝ≥0∞)⁻¹ < Metric.infEDist y Uᶜ}, fun i ↦ ?_, ?_⟩
  · -- `closure W_i ⊆ K_i`, as `K_i ⊇ W_i` is closed (the norm and `d` are continuous).
    have hK : closure {y : Rn N | ‖y‖ < (i : ℝ) ∧ (i : ℝ≥0∞)⁻¹ < Metric.infEDist y Uᶜ} ⊆
        {y | ‖y‖ ≤ (i : ℝ) ∧ (i : ℝ≥0∞)⁻¹ ≤ Metric.infEDist y Uᶜ} :=
      closure_minimal (fun y hy ↦ ⟨hy.1.le, hy.2.le⟩)
        ((isClosed_le continuous_norm continuous_const).inter
          (isClosed_le continuous_const Metric.continuous_infEDist))
    refine ⟨(isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const Metric.continuous_infEDist), ?_, fun y hy ↦ hKU i y (hK hy).2⟩
    exact (isCompact_closedBall (0 : Rn N) (i : ℝ)).of_isClosed_subset isClosed_closure
      fun y hy ↦ mem_closedBall_zero_iff.2 (hK hy).1
  · refine Subset.antisymm (iUnion_subset fun i y hy ↦ hKU i y hy.2.le) fun y hy ↦ ?_
    -- `d(y) ≠ 0` as `ℝᴺ ∖ U` is closed; take `i = max k m + 1` with `1/k < d(y)` and `m > |y|`.
    have hd : Metric.infEDist y Uᶜ ≠ 0 := fun h ↦
      (Metric.mem_iff_infEDist_zero_of_closed hU.isClosed_compl).2 h hy
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hd
    obtain ⟨m, hm⟩ := exists_nat_gt ‖y‖
    refine mem_iUnion.2 ⟨max k m + 1, hm.trans_le ?_, lt_of_le_of_lt ?_ hk⟩
    · exact_mod_cast (le_max_right k m).trans (Nat.le_succ _)
    · exact ENNReal.inv_le_inv.2 (by exact_mod_cast (le_max_left k m).trans (Nat.le_succ _))
/-- **Approximate tangent planes are local** (Simon Ch. 3, proof of Thm. 4.3; parent proof
step 5). If `W ⊆ ℝᴺ` is open, `x ∈ W` and `μ` has approximate tangent plane `P` with multiplicity
`θ` at `x`, then so does `μ ⌞ W`. For `f ∈ C_c(ℝᴺ, ℝ)` choose `R > 0` with `f = 0` off `B_R(0)`
and `δ > 0` with `B_δ(x) ⊆ W`. For `0 < r < δ / R`, `f ∘ η_{x,r}` vanishes off `W`, so the
blow-up integrals against `μ ⌞ W` and against `μ` agree. -/
theorem Submission.deGiorgiRH_tangentPlane_restrict_open : ∀ (n N : ℕ) (μ : Measure (Rn N)) (W : Set (Rn N)) (x : Rn N) (P : Submodule ℝ (Rn N)) (θ : ℝ), IsOpen W → x ∈ W → HasApproxTangentPlaneWithMultiplicity n μ x P θ → HasApproxTangentPlaneWithMultiplicity n (μ.restrict W) x P θ := by
  intro n N μ W x P θ hW hxW hP
  -- The dimension clause `finrank P = n` does not involve the measure.
  refine ⟨hP.1, fun f ↦ ?_⟩
  -- `tsupport f ⊆ B̄_{R₀}(0)`, so `f z = 0` once `‖z‖ ≥ R := max R₀ 0 + 1`.
  obtain ⟨R, hR, hf⟩ : ∃ R > 0, ∀ z, R ≤ ‖z‖ → f z = 0 := by
    obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
    refine ⟨max R₀ 0 + 1, by positivity, fun z hz ↦ ?_⟩
    by_contra hfz
    have := mem_closedBall_zero_iff.1 (hR₀ (subset_tsupport _ hfz))
    linarith [le_max_left R₀ 0]
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hW x hxW
  -- The two blow-up quotients agree for `0 < r < δ / R`.
  refine (hP.2 f).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR)] with r hr
  -- `f ∘ η_{x,r}` vanishes off `W`, so restricting to `W` does not change the integral (no
  -- integrability needed).
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro y hy
  apply hf
  -- `y ∉ B_δ(x)`, so `‖η_{x,r}(y)‖ = ‖y - x‖ / r ≥ δ / r > R`.
  have hyx : δ ≤ ‖y - x‖ := by
    by_contra h
    exact hy (hball (by rw [Metric.mem_ball, dist_eq_norm]; linarith))
  have hrR : r * R < δ := (lt_div_iff₀ hR).1 hr.2
  rw [blowUpMap, norm_smul, norm_inv, Real.norm_of_nonneg hr.1.le, le_inv_mul_iff₀ hr.1]
  linarith
/-- **Hausdorff measure of an `n`-disc in an `n`-plane** (Simon Ch. 1, Theorem 2.9: `Hⁿ = Lⁿ` on
`ℝⁿ`, transported to an `n`-dimensional subspace; the normalization `Hⁿ(P ∩ B_ρ(0)) = ωₙ ρⁿ`
behind Ch. 3, Remark 1.5(3)). If `P ⊆ ℝᴺ` is a subspace with `dim P = n` and `s > 0`, then
`Hⁿ(P ∩ B̄_s(0)) = sⁿ ωₙ` with `ωₙ = Lⁿ(B_1(0))`. An orthonormal basis of `P` gives a linear
isometry `ι : ℝⁿ → ℝᴺ` onto `P` with `P ∩ B̄_s(0) = ι(B̄_s(0))`; `Hⁿ` is isometry invariant and
equals `Lⁿ` on `ℝⁿ`, and `Lⁿ(B̄_s(0)) = sⁿ Lⁿ(B_1(0))` by Haar scaling. -/
theorem Submission.deGiorgiRH_plane_closedBall_measure : ∀ (n N : ℕ) (P : Submodule ℝ (Rn N)), finrank ℝ P = n → ∀ s : ℝ, 0 < s → μHE[n] ((P : Set (Rn N)) ∩ Metric.closedBall 0 s) = ENNReal.ofReal (s ^ n) * volume (Metric.ball (0 : Rn n) 1) := by
  intro n N P hP s hs
  subst hP
  -- Step 1: an orthonormal basis of `P` gives a linear isometric isomorphism `e : P → ℝⁿ`; then
  -- `ι = (P ↪ ℝᴺ) ∘ e⁻¹ : ℝⁿ → ℝᴺ` is a linear isometry with range `P`.
  let e : P ≃ₗᵢ[ℝ] Rn (finrank ℝ P) := (stdOrthonormalBasis ℝ P).repr
  let ι : Rn (finrank ℝ P) →ₗᵢ[ℝ] Rn N := P.subtypeₗᵢ.comp e.symm.toLinearIsometry
  -- Step 2: `P ∩ B̄_s(0) = ι(B̄_s(0))`.
  have himg : (P : Set (Rn N)) ∩ Metric.closedBall 0 s = ι '' Metric.closedBall 0 s := by
    ext y
    constructor
    · rintro ⟨hyP, hy⟩
      refine ⟨e ⟨y, hyP⟩, ?_, by simp [ι]⟩
      rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
      simpa using hy
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(e.symm t).2, ?_⟩
      rw [mem_closedBall_zero_iff] at ht ⊢
      rwa [ι.norm_map]
  -- Steps 3–6: isometry invariance, `Hⁿ = Lⁿ` on `ℝⁿ`, and Haar scaling of closed balls.
  rw [himg, ι.isometry.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_closedBall _ _ hs.le,
    finrank_euclideanSpace_fin]

/-- **Vague convergence to an `n`-plane gives the mass of the unit ball** (Simon Ch. 3, proof of
Thm. 4.3, parent proof Steps 3 and 7; the squeeze of Remark 1.5(3)). Let `P ⊆ ℝᴺ` be an
`n`-dimensional subspace and `(ν_r)` measures with `ν_r(B̄_2(0)) < ∞` for small `r > 0` and
`∫ f dν_r → ∫_P f dHⁿ` for every `f ∈ C_c(ℝᴺ, ℝ)`. Then `ν_r(B̄_1(0)) → ω_n` in `[0, ∞]` as
`r ↓ 0`. For `0 < τ < 1` take bump functions `g, f ∈ C_c` with values in `[0, 1]`, `g = 1` on
`B̄_{1-τ}(0)`, `g = 0` off `B_1(0)`, `f = 1` on `B̄_1(0)` and `f = 0` off `B_{1+τ}(0)`. Comparing
with indicators gives `∫ g dν_r ≤ ν_r(B̄_1(0)) ≤ ∫ f dν_r` for small `r`, while
`Hⁿ(P ∩ B̄_s(0)) = sⁿ ω_n` gives `∫_P g dHⁿ ≥ (1 - τ)ⁿ ω_n` and `∫_P f dHⁿ ≤ (1 + τ)ⁿ ω_n`.
Letting `r ↓ 0` and then `τ ↓ 0` squeezes `ν_r(B̄_1(0))` to `ω_n`. -/
theorem Submission.deGiorgiRH_closedBall_tendsto_of_vague_plane : ∀ (n N : ℕ) (ν : ℝ → Measure (Rn N)) (P : Submodule ℝ (Rn N)), finrank ℝ P = n → (∀ᶠ r in 𝓝[>] (0 : ℝ), ν r (Metric.closedBall 0 2) < ∞) → (∀ f : C_c(Rn N, ℝ), Tendsto (fun r : ℝ ↦ ∫ y, f y ∂(ν r)) (𝓝[>] 0) (𝓝 (∫ y in (P : Set (Rn N)), f y ∂μHE[n]))) → Tendsto (fun r : ℝ ↦ ν r (Metric.closedBall 0 1)) (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : Rn n) 1))) := by
  intro n N ν P hP hfin hlim
  have hω : volume (Metric.ball (0 : Rn n) 1) ≠ ∞ := measure_ball_lt_top.ne
  set ω : ℝ≥0∞ := volume (Metric.ball (0 : Rn n) 1)
  -- `(Hⁿ ⌞ P)(B̄_s(0)) = Hⁿ(P ∩ B̄_s(0)) = sⁿ ω_n` (sibling `plane_ball_measure`).
  have hplane : ∀ s : ℝ, 0 < s → (μHE[n] : Measure (Rn N)).restrict (P : Set (Rn N))
      (Metric.closedBall 0 s) = ENNReal.ofReal (s ^ n) * ω := by
    intro s hs
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm]
    exact Submission.deGiorgiRH_plane_closedBall_measure n N P hP s hs
  -- Step 1 (cut-offs): for `0 < a < b`, a bump function `φ ∈ C_c` with values in `[0, 1]`,
  -- `φ = 1` on `B̄_a(0)` and `φ = 0` off `B_b(0)`.
  have hcut : ∀ a b : ℝ, 0 < a → a < b → ∃ φ : C_c(Rn N, ℝ), (∀ y, 0 ≤ φ y) ∧ (∀ y, φ y ≤ 1) ∧
      (∀ y : Rn N, ‖y‖ ≤ a → φ y = 1) ∧ ∀ y : Rn N, b < ‖y‖ → φ y = 0 := by
    intro a b ha hab
    let β : ContDiffBump (0 : Rn N) := ⟨a, b, ha, hab⟩
    refine ⟨⟨⟨β, β.continuous⟩, β.hasCompactSupport⟩, fun y ↦ β.nonneg' y,
      fun y ↦ β.le_one (x := y), fun y hy ↦ β.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hy),
      fun y hy ↦ β.zero_of_le_dist ?_⟩
    rw [dist_zero_right]
    exact hy.le
  -- Steps 2 and 4 (comparison with indicators): if `μ(B̄_b(0)) < ∞`, then
  -- `μ(B̄_a(0)) ≤ ∫ φ dμ ≤ μ(B̄_b(0))`.
  have key : ∀ (μ : Measure (Rn N)) (φ : C_c(Rn N, ℝ)) (a b : ℝ),
      μ (Metric.closedBall 0 b) ≠ ∞ → (∀ y, 0 ≤ φ y) → (∀ y, φ y ≤ 1) →
      (∀ y : Rn N, ‖y‖ ≤ a → φ y = 1) → (∀ y : Rn N, b < ‖y‖ → φ y = 0) →
      μ (Metric.closedBall 0 a) ≤ ENNReal.ofReal (∫ y, φ y ∂μ) ∧
        ENNReal.ofReal (∫ y, φ y ∂μ) ≤ μ (Metric.closedBall 0 b) := by
    intro μ φ a b hb h0 h1 ha hb'
    have hle : ∫⁻ y, ENNReal.ofReal (φ y) ∂μ ≤ μ (Metric.closedBall 0 b) := by
      rw [← lintegral_indicator_one measurableSet_closedBall]
      refine lintegral_mono fun y ↦ ?_
      by_cases hy : y ∈ Metric.closedBall (0 : Rn N) b
      · rw [indicator_of_mem hy, Pi.one_apply]
        exact ENNReal.ofReal_le_one.2 (h1 y)
      · rw [hb' y (not_le.1 (mt mem_closedBall_zero_iff.2 hy)), ENNReal.ofReal_zero]
        exact zero_le
    have hge : μ (Metric.closedBall 0 a) ≤ ∫⁻ y, ENNReal.ofReal (φ y) ∂μ := by
      rw [← lintegral_indicator_one measurableSet_closedBall]
      refine lintegral_mono fun y ↦ ?_
      by_cases hy : y ∈ Metric.closedBall (0 : Rn N) a
      · rw [indicator_of_mem hy, Pi.one_apply, ha y (mem_closedBall_zero_iff.1 hy),
          ENNReal.ofReal_one]
      · rw [indicator_of_notMem hy]
        exact zero_le
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0)
      (map_continuous φ).aestronglyMeasurable, ENNReal.ofReal_toReal (ne_top_of_le_ne_top hb hle)]
    exact ⟨hge, hle⟩
  -- `sⁿ ω_n → ω_n` as `s → 1`, and `1 ∓ τ → 1` as `τ ↓ 0`.
  have hpow : Tendsto (fun s : ℝ ↦ ENNReal.ofReal (s ^ n) * ω) (𝓝 1) (𝓝 ω) := by
    have h := ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_ofReal ((continuous_pow n).tendsto (1 : ℝ))) (Or.inr hω)
    rwa [one_pow, ENNReal.ofReal_one, one_mul] at h
  have hsub : Tendsto (fun τ : ℝ ↦ 1 - τ) (𝓝[>] 0) (𝓝 1) :=
    ((continuous_sub_left (1 : ℝ)).tendsto' 0 1 (sub_zero 1)).mono_left nhdsWithin_le_nhds
  have hadd : Tendsto (fun τ : ℝ ↦ 1 + τ) (𝓝[>] 0) (𝓝 1) :=
    ((show Continuous fun τ : ℝ ↦ 1 + τ from continuous_const.add continuous_id).tendsto' 0 1
      (add_zero 1)).mono_left nhdsWithin_le_nhds
  -- Steps 5 and 6: squeeze `ν_r(B̄_1(0))` in `[0, ∞]`.
  rw [tendsto_order]
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · -- `c < ω_n`: fix `τ ∈ (0, 1)` with `c < (1 - τ)ⁿ ω_n ≤ ∫_P g dHⁿ`.
    obtain ⟨τ, hτc, hτ0, hτ1⟩ := (((hpow.comp hsub).eventually (lt_mem_nhds hc)).and
      (Ioo_mem_nhdsGT one_pos : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ∈ Ioo 0 1)).exists
    obtain ⟨g, hg0, hg1, hga, hgb⟩ := hcut (1 - τ) 1 (by linarith) (by linarith)
    have hPg := (key ((μHE[n] : Measure (Rn N)).restrict (P : Set (Rn N))) g (1 - τ) 1
      (by rw [hplane 1 one_pos]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω)
      hg0 hg1 hga hgb).1
    rw [hplane (1 - τ) (by linarith)] at hPg
    filter_upwards [(ENNReal.tendsto_ofReal (hlim g)).eventually (lt_mem_nhds (hτc.trans_le hPg)),
      hfin] with r hr hr2
    -- `∫ g dν_r ≤ ν_r(B̄_1(0))`, as `ν_r(B̄_1(0)) ≤ ν_r(B̄_2(0)) < ∞`.
    exact hr.trans_le (key (ν r) g (1 - τ) 1
      ((measure_mono (Metric.closedBall_subset_closedBall one_le_two)).trans_lt hr2).ne
      hg0 hg1 hga hgb).2
  · -- `ω_n < c`: fix `τ ∈ (0, 1)` with `∫_P f dHⁿ ≤ (1 + τ)ⁿ ω_n < c`.
    obtain ⟨τ, hτc, hτ0, hτ1⟩ := (((hpow.comp hadd).eventually (gt_mem_nhds hc)).and
      (Ioo_mem_nhdsGT one_pos : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ∈ Ioo 0 1)).exists
    obtain ⟨f, hf0, hf1, hfa, hfb⟩ := hcut 1 (1 + τ) one_pos (by linarith)
    have hPf := (key ((μHE[n] : Measure (Rn N)).restrict (P : Set (Rn N))) f 1 (1 + τ)
      (by rw [hplane (1 + τ) (by linarith)]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω)
      hf0 hf1 hfa hfb).2
    rw [hplane (1 + τ) (by linarith)] at hPf
    filter_upwards [(ENNReal.tendsto_ofReal (hlim f)).eventually (gt_mem_nhds (hPf.trans_lt hτc)),
      hfin] with r hr hr2
    -- `ν_r(B̄_1(0)) ≤ ∫ f dν_r`, as `ν_r(B̄_{1+τ}(0)) ≤ ν_r(B̄_2(0)) < ∞`.
    exact (key (ν r) f 1 (1 + τ)
      ((measure_mono (Metric.closedBall_subset_closedBall (by linarith))).trans_lt hr2).ne
      hf0 hf1 hfa hfb).1.trans_lt hr

/-- **Density `ωₙ` at a point with an approximate tangent plane of multiplicity `1`** (the
measure form of Simon Ch. 3, Remark 1.5(3), as used for `μ_E` in Thm. 4.3; parent proof step 3).
If `μ(B̄_δ(x)) < ∞` for some `δ > 0` and `μ` has approximate tangent plane `P` with multiplicity
`1` at `x`, then `μ(B̄_ρ(x)) / ρⁿ → ωₙ = Lⁿ(B₁(0))` in `[0, ∞]` as `ρ ↓ 0`.
The rescaled push-forwards `ν_r = (rⁿ)⁻¹ η_{x,r#} μ` satisfy `ν_r(B̄_R(0)) = μ(B̄_{rR}(x)) / rⁿ`
for `r > 0`, as `η_{x,r}⁻¹(B̄_R(0)) = B̄_{rR}(x)`. Hence `ν_r(B̄_2(0)) < ∞` for `r < δ / 2`, and
`∫ f dν_r = (rⁿ)⁻¹ ∫ f ∘ η_{x,r} dμ → ∫_P f dHⁿ` for `f ∈ C_c(ℝᴺ)`, so
`deGiorgiRH_closedBall_tendsto_of_vague_plane` gives `ν_r(B̄_1(0)) → ωₙ`. -/
theorem Submission.deGiorgiRH_measure_density_of_tangentPlane : ∀ (n N : ℕ) (μ : Measure (Rn N)) (x : Rn N) (P : Submodule ℝ (Rn N)), (∃ δ : ℝ, 0 < δ ∧ μ (Metric.closedBall x δ) < ∞) → HasApproxTangentPlaneWithMultiplicity n μ x P 1 → Tendsto (fun ρ : ℝ ↦ μ (Metric.closedBall x ρ) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : Rn n) 1))) := by
  intro n N μ x P ⟨δ, hδ, hδμ⟩ hP
  have hη : ∀ r, Measurable (blowUpMap x r) := fun r ↦ by
    unfold blowUpMap
    fun_prop
  let ν : ℝ → Measure (Rn N) := fun r ↦ (ENNReal.ofReal (r ^ n))⁻¹ • μ.map (blowUpMap x r)
  -- `‖η_{x,r}(y)‖ = ‖y - x‖ / r`, so `ν_r(B̄_R(0)) = μ(B̄_{rR}(x)) / rⁿ`.
  have hν : ∀ r : ℝ, 0 < r → ∀ R : ℝ,
      ν r (Metric.closedBall 0 R) = μ (Metric.closedBall x (r * R)) / ENNReal.ofReal (r ^ n) := by
    intro r hr R
    have hpre : blowUpMap x r ⁻¹' Metric.closedBall 0 R = Metric.closedBall x (r * R) := by
      ext y
      rw [mem_preimage, mem_closedBall_zero_iff, mem_closedBall_iff_norm, blowUpMap, norm_smul,
        norm_inv, Real.norm_eq_abs, abs_of_pos hr, inv_mul_le_iff₀ hr]
    rw [Measure.smul_apply, Measure.map_apply (hη r) Metric.isClosed_closedBall.measurableSet,
      hpre, smul_eq_mul, ENNReal.div_eq_inv_mul]
  -- For `0 < r < δ / 2`, `ν_r(B̄_2(0)) = μ(B̄_{2r}(x)) / rⁿ ≤ μ(B̄_δ(x)) / rⁿ < ∞`.
  have hfin : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν r (Metric.closedBall 0 2) < ∞ := by
    filter_upwards [Ioo_mem_nhdsGT (half_pos hδ)] with r hr
    rw [hν r hr.1]
    refine ENNReal.div_lt_top ?_ (ENNReal.ofReal_pos.2 (pow_pos hr.1 n)).ne'
    refine ((measure_mono (Metric.closedBall_subset_closedBall ?_)).trans_lt hδμ).ne
    linarith [hr.2]
  -- `∫ f dν_r = (rⁿ)⁻¹ ∫ f ∘ η_{x,r} dμ`, which tends to `1 * ∫_P f dHⁿ`.
  have hlim : ∀ f : C_c(Rn N, ℝ), Tendsto (fun r : ℝ ↦ ∫ y, f y ∂(ν r)) (𝓝[>] 0)
      (𝓝 (∫ y in (P : Set (Rn N)), f y ∂μHE[n])) := by
    intro f
    have hf := hP.2 f
    rw [one_mul] at hf
    refine hf.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [integral_smul_measure, integral_map (hη r).aemeasurable
      (map_continuous f).aestronglyMeasurable, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (pow_nonneg hr.le n), smul_eq_mul]
  refine (Submission.deGiorgiRH_closedBall_tendsto_of_vague_plane n N ν P hP.1 hfin hlim).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [hν r hr, mul_one]
/-- **An approximate tangent space forces `Hⁿ`-density one** (Simon Ch. 3, Remark 1.5(3); Step 7
of the supplied proof that `μ_E = Hⁿ ⌞ ∂*E` in De Giorgi's Theorem 4.3). Let `M ⊆ ℝᴺ` be
arbitrary with `Hⁿ(M ∩ B̄_δ(x)) < ∞` for some `δ > 0`, and let `M` have approximate tangent space
`P` at `x` (Def. 1.4). Then `Hⁿ(M ∩ B̄_ρ(x))/ρⁿ → ω_n = Lⁿ(B_1(0))` as `ρ ↓ 0`. The blow-up
measures `ν_r = Hⁿ ⌞ η_{x,r}(M)` satisfy `ν_r(B̄_R(0)) = Hⁿ(M ∩ B̄_{rR}(x))/rⁿ` (translation
invariance and `n`-homogeneity of `Hⁿ`) and converge vaguely to `Hⁿ ⌞ P` by Def. 1.4, so the
vague-limit lemma `deGiorgiRH_closedBall_tendsto_of_vague_plane` applies; take `R = 1`. -/
theorem Submission.deGiorgiRH_hausdorff_density_of_approxTangent : ∀ (n N : ℕ) (M : Set (Rn N)) (x : Rn N) (P : Submodule ℝ (Rn N)), (∃ δ : ℝ, 0 < δ ∧ μHE[n] (M ∩ Metric.closedBall x δ) < ∞) → HasApproximateTangentSpaceAt n M x P → Tendsto (fun ρ : ℝ ↦ μHE[n] (M ∩ Metric.closedBall x ρ) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : Rn n) 1))) := by
  intro n N M x P ⟨δ, hδ, hMδ⟩ hP
  -- Step 1: `Hⁿ(η_{x,r}(B)) = Hⁿ(B)/rⁿ` for `r > 0` and every `B ⊆ ℝᴺ`: `η_{x,r}(B)` is
  -- `r⁻¹ • (B - x)`, translations are isometries and `Hⁿ(c • B) = |c|ⁿ Hⁿ(B)`.
  have hscale : ∀ r : ℝ, 0 < r → ∀ B : Set (Rn N),
      μHE[n] (blowUpMap x r '' B) = μHE[n] B / ENNReal.ofReal (r ^ n) := by
    intro r hr B
    have himage :
        blowUpMap x r '' B = (fun z ↦ r⁻¹ • z) '' (IsometryEquiv.subRight x '' B) := by
      rw [Set.image_image]
      rfl
    rw [himage, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image, ENNReal.smul_def,
      smul_eq_mul, div_eq_mul_inv, mul_comm, ← ENNReal.ofReal_inv_of_pos (pow_pos hr n), ← inv_pow,
      ENNReal.ofReal_pow (inv_nonneg.2 hr.le), ENNReal.coe_pow, ← enorm_eq_nnnorm,
      Real.enorm_eq_ofReal (inv_nonneg.2 hr.le)]
  -- Step 2: `η_{x,r}⁻¹(B̄_R(0)) = B̄_{rR}(x)` for `r > 0`, so that
  -- `B̄_R(0) ∩ η_{x,r}(M) = η_{x,r}(M ∩ B̄_{rR}(x))`.
  have hpre : ∀ r : ℝ, 0 < r → ∀ R : ℝ,
      blowUpMap x r ⁻¹' Metric.closedBall 0 R = Metric.closedBall x (r * R) := by
    intro r hr R
    ext y
    rw [Set.mem_preimage, Metric.mem_closedBall, Metric.mem_closedBall, dist_zero_right,
      dist_eq_norm, blowUpMap, norm_smul, norm_inv, Real.norm_of_nonneg hr.le, inv_mul_le_iff₀ hr]
  -- Step 3: the blow-up measures `ν_r = Hⁿ ⌞ η_{x,r}(M)` satisfy
  -- `ν_r(B̄_R(0)) = Hⁿ(M ∩ B̄_{rR}(x))/rⁿ` (`B̄_R(0)` is closed, hence Borel).
  have hball : ∀ r : ℝ, 0 < r → ∀ R : ℝ,
      (μHE[n] : Measure (Rn N)).restrict (blowUpMap x r '' M) (Metric.closedBall 0 R) =
        μHE[n] (M ∩ Metric.closedBall x (r * R)) / ENNReal.ofReal (r ^ n) := by
    intro r hr R
    rw [Measure.restrict_apply Metric.isClosed_closedBall.measurableSet, Set.inter_comm,
      ← Set.image_inter_preimage, hpre r hr R, hscale r hr]
  -- Step 4: hypothesis (i) of the vague-limit lemma: for `0 < r < δ/2`,
  -- `ν_r(B̄_2(0)) = Hⁿ(M ∩ B̄_{2r}(x))/rⁿ ≤ Hⁿ(M ∩ B̄_δ(x))/rⁿ < ∞`.
  have hfin : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (μHE[n] : Measure (Rn N)).restrict (blowUpMap x r '' M) (Metric.closedBall 0 2) < ∞ := by
    filter_upwards [Ioo_mem_nhdsGT (half_pos hδ)] with r hr
    rw [hball r hr.1 2]
    refine ENNReal.div_lt_top (ne_top_of_le_ne_top hMδ.ne (measure_mono ?_))
      (ENNReal.ofReal_pos.2 (pow_pos hr.1 n)).ne'
    exact Set.inter_subset_inter_right _
      (Metric.closedBall_subset_closedBall (by linarith [hr.2]))
  -- Steps 5–6: hypothesis (ii) is Def. 1.4 itself (`∫ f dν_r = ∫_{η_{x,r}(M)} f dHⁿ`), so the
  -- lemma gives `ν_r(B̄_1(0)) → ω_n`; by Step 3 with `R = 1`, `ν_r(B̄_1(0)) = Hⁿ(M ∩ B̄_r(x))/rⁿ`.
  refine (Submission.deGiorgiRH_closedBall_tendsto_of_vague_plane n N
    (fun r ↦ (μHE[n] : Measure (Rn N)).restrict (blowUpMap x r '' M)) P hP.1 hfin hP.2).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [hball r hr 1, mul_one]

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
