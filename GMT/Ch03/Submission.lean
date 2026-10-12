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

/-- **Orthogonal projection onto `W ⊕ ℝu`** (used in the proof of the Besicovitch–Federer
Theorem 3.6 of Simon Ch. 3, `chapter-03.txt` lines 530–536, whose proof the book defers to
[Fed69]/[Ros84]). For a subspace `W ⊆ ℝᴺ` with orthogonal projection `P` and a unit vector
`u ∈ Wᗮ`, the orthogonal projection onto `W ⊔ span{u}` is `y ↦ P y + (y · u) u`: the vector
`z = P y + (y · u) u` lies in `W ⊔ span{u}`, and `y - z` is orthogonal to `W` and to `u`, hence to
`W ⊔ span{u}`. -/
theorem Submission.bf_starProjection_sup_span_unit : ∀ (N : ℕ) (W : Submodule ℝ (Rn N)) (u : Rn N), u ∈ Wᗮ → ‖u‖ = 1 → ∀ y : Rn N, (W ⊔ Submodule.span ℝ {u}).starProjection y = W.starProjection y + inner ℝ y u • u := by
  intro N W u hu hu1 y
  -- Characterization: `z ∈ H` and `y - z ∈ Hᗮ` give `H.starProjection y = z`.
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · -- `z ∈ W ⊔ span{u}`: `P y ∈ W` and `(y · u) u ∈ span{u}`.
    exact Submodule.add_mem_sup (W.starProjection_apply_mem y)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
  · -- `(W ⊔ span{u})ᗮ = Wᗮ ⊓ span{u}ᗮ`.
    rw [← Submodule.inf_orthogonal]
    refine ⟨?_, ?_⟩
    · -- `y - z = (y - P y) - (y · u) u ∈ Wᗮ`.
      have h : y - (W.starProjection y + inner ℝ y u • u) =
          (y - W.starProjection y) - inner ℝ y u • u := by abel
      rw [h]
      exact Submodule.sub_mem _ (W.sub_starProjection_mem_orthogonal y) (Submodule.smul_mem _ _ hu)
    · -- `u · (y - z) = u · y - u · P y - (y · u) ‖u‖² = 0`.
      refine Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_
      have hPu : inner ℝ u (W.starProjection y) = (0 : ℝ) :=
        Submodule.inner_left_of_mem_orthogonal (W.starProjection_apply_mem y) hu
      rw [inner_sub_right, inner_add_right, real_inner_smul_right, hPu,
        real_inner_self_eq_norm_sq, hu1, real_inner_comm]
      ring
/-- **A narrow cone about `Wᗮ` is covered by the `ℓ` slab cones with aperture enlarged by `√ℓ`**:
step 3(b) of the cone trichotomy in the proof of Simon Ch. 3, Theorem 3.6 (`chapter-03.txt`
lines 530–536, which defers the proof to [Fed69]). This is the right inclusion
`X(0, V, s) ⊆ ⋃_j Z(j, s*)` of M. G. Dall'Alba, *The Besicovitch–Federer Projection Theorem*,
Lemma 5.5, for `V = Wᗮ` with the frame `(u_j)` and `s* ≤ √ℓ s`, at the point `y = x - a`.
Since `dim Wᗮ = ℓ`, the `u_k` form an orthonormal basis of `Wᗮ`, so Parseval and Pythagoras give
`|y|² = |Py|² + Σ_k (y·u_k)²`. For `j` maximizing `(y·u_j)²`,
`|Py + (y·u_j)u_j|² = |Py|² + (y·u_j)²` and `|Py|² < s²|y|² ≤ ℓ s² |Py + (y·u_j)u_j|²`. -/
theorem Submission.bf_cone_subset_iUnion_slabCones : ∀ (n ℓ : ℕ), 0 < ℓ → ∀ W : Submodule ℝ (Rn (n + ℓ)), finrank ℝ W = n → ∀ u : Fin ℓ → Rn (n + ℓ), Orthonormal ℝ u → (∀ j, u j ∈ Wᗮ) → ∀ (y : Rn (n + ℓ)) (s : ℝ), ‖W.starProjection y‖ < s * ‖y‖ → ∃ j, ‖W.starProjection y‖ < Real.sqrt (ℓ : ℝ) * s * ‖W.starProjection y + inner ℝ y (u j) • u j‖ := by
  intro n ℓ hℓ W hW u hu huW y s hys
  have : Nonempty (Fin ℓ) := ⟨⟨0, hℓ⟩⟩
  -- Steps 1–2: `dim Wᗮ = ℓ`, so `u`, viewed in `Wᗮ`, is an orthonormal basis `b` of `Wᗮ`.
  have hdim : finrank ℝ Wᗮ = ℓ := by
    have h := W.finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace_fin, hW] at h
    omega
  let v : Fin ℓ → Wᗮ := fun k ↦ ⟨u k, huW k⟩
  have hv : Orthonormal ℝ v := by
    refine ⟨fun i ↦ ?_, fun i k hik ↦ ?_⟩
    · simpa [v] using hu.1 i
    · simpa [v] using hu.2 hik
  have hcard : Fintype.card (Fin ℓ) = finrank ℝ Wᗮ := by simp [hdim]
  let b : OrthonormalBasis (Fin ℓ) ℝ Wᗮ :=
    OrthonormalBasis.mk hv (hv.linearIndependent.span_eq_top_of_card_eq_finrank hcard).ge
  have hb : ∀ k, (b k : Rn (n + ℓ)) = u k := fun k ↦ by simp [b, v]
  -- Step 3: `P y ⊥ u_k`.
  have hPu : ∀ k, inner ℝ (W.starProjection y) (u k) = (0 : ℝ) := fun k ↦
    Submodule.inner_right_of_mem_orthogonal (W.starProjection_apply_mem y) (huW k)
  -- Step 4: Parseval in `Wᗮ` gives `‖y - P y‖² = ∑ₖ (y · u_k)²`.
  have hpars : ‖y - W.starProjection y‖ ^ 2 = ∑ k, (inner ℝ y (u k)) ^ 2 := by
    have h := b.sum_sq_inner_right ⟨y - W.starProjection y, W.sub_starProjection_mem_orthogonal y⟩
    have hn : ‖(⟨y - W.starProjection y, W.sub_starProjection_mem_orthogonal y⟩ : Wᗮ)‖ =
        ‖y - W.starProjection y‖ := rfl
    rw [hn] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Submodule.coe_inner, hb k, real_inner_comm, inner_sub_left, hPu, sub_zero]
  -- Step 5: Pythagoras, `‖y‖² = ‖P y‖² + ∑ₖ (y · u_k)²`.
  have hpyth : ‖y‖ ^ 2 = ‖W.starProjection y‖ ^ 2 + ∑ k, (inner ℝ y (u k)) ^ 2 := by
    rw [← hpars]
    have h := W.norm_sq_eq_add_norm_sq_starProjection y
    rwa [Submodule.starProjection_orthogonal_val] at h
  -- Step 6: choose `j` maximizing `(y · u_j)²`, so `∑ₖ (y · u_k)² ≤ ℓ (y · u_j)²`.
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun k ↦ (inner ℝ y (u k)) ^ 2)
    Finset.univ_nonempty
  have hsum : ∑ k, (inner ℝ y (u k)) ^ 2 ≤ ℓ * (inner ℝ y (u j)) ^ 2 := by
    calc ∑ k, (inner ℝ y (u k)) ^ 2 ≤ ∑ _k : Fin ℓ, (inner ℝ y (u j)) ^ 2 :=
          Finset.sum_le_sum fun k hk ↦ hj k hk
      _ = ℓ * (inner ℝ y (u j)) ^ 2 := by simp
  -- Step 7: `‖P y + (y · u_j) u_j‖² = ‖P y‖² + (y · u_j)²`.
  have hpj : ‖W.starProjection y + inner ℝ y (u j) • u j‖ ^ 2 =
      ‖W.starProjection y‖ ^ 2 + (inner ℝ y (u j)) ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, hPu, norm_smul, hu.1 j, Real.norm_eq_abs, mul_one,
      sq_abs]
    ring
  refine ⟨j, ?_⟩
  -- Step 8: `s > 0`.
  have hP0 : 0 ≤ ‖W.starProjection y‖ := norm_nonneg _
  have hs : 0 < s := by
    by_contra hs
    have : s * ‖y‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hs) (norm_nonneg _)
    linarith
  -- Steps 9–10: compare squares, then take square roots.
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hsqrt : Real.sqrt (ℓ : ℝ) ^ 2 = ℓ := Real.sq_sqrt (by positivity)
  have hR : 0 ≤ Real.sqrt (ℓ : ℝ) * s * ‖W.starProjection y + inner ℝ y (u j) • u j‖ := by
    positivity
  refine lt_of_pow_lt_pow_left₀ 2 hR ?_
  calc ‖W.starProjection y‖ ^ 2 < (s * ‖y‖) ^ 2 := pow_lt_pow_left₀ hys hP0 two_ne_zero
    _ = s ^ 2 * (‖W.starProjection y‖ ^ 2 + ∑ k, (inner ℝ y (u k)) ^ 2) := by rw [mul_pow, hpyth]
    _ ≤ s ^ 2 * (ℓ * ‖W.starProjection y‖ ^ 2 + ℓ * (inner ℝ y (u j)) ^ 2) := by
        gcongr
        nlinarith [sq_nonneg ‖W.starProjection y‖]
    _ = (Real.sqrt (ℓ : ℝ) * s * ‖W.starProjection y + inner ℝ y (u j) • u j‖) ^ 2 := by
        rw [mul_pow, mul_pow, hsqrt, hpj]
        ring

/-- **Transfer of the cone density trichotomy from finitely many comparable cone families**: the
case analysis in the slab-to-cone step of the proof of the Besicovitch–Federer projection theorem,
Simon Ch. 3, Theorem 3.6 (`chapter-03.txt` lines 530–536, which defers the proof to [Fed69]; cf.
M. G. Dall'Alba, *The Besicovitch–Federer Projection Theorem*, Lemma 5.5). Suppose
`Z_j(s) ⊆ X(s) ⊆ ⋃_j Z_j(κ s)` for `s > 0`, and each `Z_j` has zero cone density `Ψ0_j`,
infinite cone density `Ψ∞_j`, or an axis point `Ax'_j ⇒ Ax`. Then `X` has zero cone density,
infinite cone density, or `Ax`. An axis point or an infinite density transfers directly by
monotonicity. Otherwise, for `c > 0`, put `c' = c / (#ι κⁿ)` and `ε = min_j ε_j(c') / κ`; the
cover and finite subadditivity bound `X` by `#ι · c' (r κ s)ⁿ = c (r s)ⁿ`. -/
theorem Submission.bf_coneTrichotomy_of_slabCover : ∀ (N n : ℕ) (ι : Type) [Fintype ι] [Nonempty ι] (μ : Measure (Rn N)) (A : Set (Rn N)) (δ κ : ℝ) (a : Rn N) (X : ℝ → Set (Rn N)) (Z : ι → ℝ → Set (Rn N)) (Ax : Prop) (Ax' : ι → Prop), 0 < κ → (∀ j (s : ℝ), 0 < s → Z j s ⊆ X s) → (∀ s : ℝ, 0 < s → X s ⊆ ⋃ j, Z j (κ * s)) → (∀ j, Ax' j → Ax) → (∀ j, ((∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ, 0 < r → r < δ → μ (A ∩ (Z j s ∩ Metric.ball a r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) ∨ (∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μ (A ∩ (Z j s ∩ Metric.ball a r))) ∨ Ax' j)) → ((∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ, 0 < r → r < δ → μ (A ∩ (X s ∩ Metric.ball a r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) ∨ (∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μ (A ∩ (X s ∩ Metric.ball a r))) ∨ Ax) := by
  intro N n ι _ _ μ A δ κ a X Z Ax Ax' hκ hZX hXZ hAx hcases
  -- Case 1: some `Ax'_j` holds, hence `Ax`.
  by_cases hax : ∃ j, Ax' j
  · obtain ⟨j, hj⟩ := hax
    exact Or.inr (Or.inr (hAx j hj))
  -- Case 2: some `Ψ∞_j` holds; `Φ∞` follows with the same `s, r`, as `Z_j(s) ⊆ X(s)`.
  by_cases hinf : ∃ j, ∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧
      r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μ (A ∩ (Z j s ∩ Metric.ball a r))
  · obtain ⟨j, hj⟩ := hinf
    refine Or.inr (Or.inl fun K ε hε ↦ ?_)
    obtain ⟨s, hs, hsε, r, hr, hrδ, hK⟩ := hj K ε hε
    exact ⟨s, hs, hsε, r, hr, hrδ, hK.trans (measure_mono
      (Set.inter_subset_inter_right _ (Set.inter_subset_inter_left _ (hZX j s hs))))⟩
  -- Case 3: every `Ψ0_j` holds; we prove `Φ0`.
  have hzero : ∀ j, ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ,
      0 < r → r < δ → μ (A ∩ (Z j s ∩ Metric.ball a r)) ≤ ENNReal.ofReal (c * (r * s) ^ n) := by
    intro j
    rcases hcases j with h | h | h
    · exact h
    · exact absurd ⟨j, h⟩ hinf
    · exact absurd ⟨j, h⟩ hax
  refine Or.inl fun c hc ↦ ?_
  have hM : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hc' : 0 < c / (Fintype.card ι * κ ^ n) := div_pos hc (mul_pos hM (pow_pos hκ n))
  -- Choice of `ε`: `ε_j` from `Ψ0_j` for `c'`, `ε₀ = min_j ε_j > 0` and `ε = ε₀ / κ`.
  choose ε hε hεb using fun j ↦ hzero j _ hc'
  set ε₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty ε
  have hε₀ : 0 < ε₀ := (Finset.lt_inf'_iff _).2 fun j _ ↦ hε j
  refine ⟨ε₀ / κ, div_pos hε₀ hκ, fun s hs hsε r hr hrδ ↦ ?_⟩
  -- `s' = κ s` satisfies `0 < s' < ε_j` for every `j`.
  have hs' : 0 < κ * s := mul_pos hκ hs
  have hs'ε : ∀ j, κ * s < ε j := fun j ↦
    ((lt_div_iff₀' hκ).1 hsε).trans_le (Finset.inf'_le _ (Finset.mem_univ j))
  -- Cover by the `Z_j(s')`, finite subadditivity, and `#ι · c' (r κ s)ⁿ = c (r s)ⁿ`.
  calc μ (A ∩ (X s ∩ Metric.ball a r))
      ≤ μ (⋃ j, A ∩ (Z j (κ * s) ∩ Metric.ball a r)) := by
        refine measure_mono fun x ⟨hxA, hxX, hxB⟩ ↦ ?_
        obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hXZ s hs hxX)
        exact Set.mem_iUnion.2 ⟨j, hxA, hj, hxB⟩
    _ ≤ ∑ j, μ (A ∩ (Z j (κ * s) ∩ Metric.ball a r)) := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _j : ι, ENNReal.ofReal (c / (Fintype.card ι * κ ^ n) * (r * (κ * s)) ^ n) :=
        Finset.sum_le_sum fun j _ ↦ hεb j (κ * s) hs' (hs'ε j) r hr hrδ
    _ = ENNReal.ofReal (c * (r * s) ^ n) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        field_simp
        ring

/-- **Slab-to-cone step** of the proof of the Besicovitch–Federer projection theorem, Simon Ch. 3,
Theorem 3.6 (`chapter-03.txt` lines 530–536, which defers the proof to [Fed69]; cf. M. G.
Dall'Alba, *The Besicovitch–Federer Projection Theorem*, Lemma 5.5, here in codimension `ℓ`). Let
`P = W.starProjection` for an `n`-plane `W ⊆ ℝ^{n+ℓ}`, `u_1, …, u_ℓ` orthonormal in `Wᗮ` and `p_j`
the orthogonal projection onto `W ⊔ span{u_j}`. As `p_j y = P y + (y · u_j) u_j`, the slab cones
`Z_j(s) = {x : |p_j(x - a) - (p_j(x - a) · u_j) u_j| < s |p_j(x - a)|}` are
`{x : |P(x - a)| < s |p_j(x - a)|}` and `Ax'_j` is `Ax`. Hence `Z_j(s) ⊆ X(s)` as `|p_j y| ≤ |y|`,
and `X(s) ⊆ ⋃_j Z_j(√ℓ s)` by the cone cover, so the trichotomy of the `Z_j` transfers to the cone
`X(s) = {x : |P(x - a)| < s |x - a|}` (`bf_coneTrichotomy_of_slabCover` with `κ = √ℓ`). -/
theorem Submission.bf_slabGood_imp_coneTrichotomy : ∀ (n ℓ : ℕ), 0 < n → 0 < ℓ → ∀ W : Submodule ℝ (Rn (n + ℓ)), finrank ℝ W = n → ∀ u : Fin ℓ → Rn (n + ℓ), Orthonormal ℝ u → (∀ j, u j ∈ Wᗮ) → ∀ (A : Set (Rn (n + ℓ))) (δ : ℝ) (a : Rn (n + ℓ)), (∀ j, ((∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ, 0 < r → r < δ → μHE[n] (A ∩ ({x | ‖(W ⊔ Submodule.span ℝ {u j}).starProjection (x - a) - inner ℝ ((W ⊔ Submodule.span ℝ {u j}).starProjection (x - a)) (u j) • u j‖ < s * ‖(W ⊔ Submodule.span ℝ {u j}).starProjection (x - a)‖} ∩ Metric.ball a r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) ∨ (∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μHE[n] (A ∩ ({x | ‖(W ⊔ Submodule.span ℝ {u j}).starProjection (x - a) - inner ℝ ((W ⊔ Submodule.span ℝ {u j}).starProjection (x - a)) (u j) • u j‖ < s * ‖(W ⊔ Submodule.span ℝ {u j}).starProjection (x - a)‖} ∩ Metric.ball a r))) ∨ ∃ b ∈ A, b ≠ a ∧ dist b a < δ ∧ (W ⊔ Submodule.span ℝ {u j}).starProjection (b - a) - inner ℝ ((W ⊔ Submodule.span ℝ {u j}).starProjection (b - a)) (u j) • u j = 0)) → ((∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ, 0 < r → r < δ → μHE[n] (A ∩ ({x | ‖W.starProjection (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) ∨ (∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μHE[n] (A ∩ ({x | ‖W.starProjection (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r))) ∨ ∃ b ∈ A, b ≠ a ∧ dist b a < δ ∧ W.starProjection (b - a) = 0) := by
  intro n ℓ _ hℓ W hWn u hu hW A δ a hslab
  have : Nonempty (Fin ℓ) := ⟨⟨0, hℓ⟩⟩
  -- `p_j y = P y + (y · u_j) u_j`.
  have hp : ∀ j y, (W ⊔ Submodule.span ℝ {u j}).starProjection y =
      W.starProjection y + inner ℝ y (u j) • u j := fun j y ↦
    Submission.bf_starProjection_sup_span_unit (n + ℓ) W (u j) (hW j) (hu.1 j) y
  -- Hence `p_j y - (p_j y · u_j) u_j = P y`, as `P y ⊥ u_j` and `|u_j| = 1`.
  have hq : ∀ j y, (W ⊔ Submodule.span ℝ {u j}).starProjection y -
      inner ℝ ((W ⊔ Submodule.span ℝ {u j}).starProjection y) (u j) • u j =
        W.starProjection y := by
    intro j y
    have h0 : inner ℝ (W.starProjection y) (u j) = (0 : ℝ) :=
      Submodule.inner_right_of_mem_orthogonal (W.starProjection_apply_mem y) (hW j)
    rw [hp j y, inner_add_left, real_inner_smul_left, h0, real_inner_self_eq_norm_sq, hu.1 j]
    simp
  refine Submission.bf_coneTrichotomy_of_slabCover (n + ℓ) n (Fin ℓ) μHE[n] A δ
    (Real.sqrt (ℓ : ℝ)) a (fun s ↦ {x | ‖W.starProjection (x - a)‖ < s * ‖x - a‖})
    (fun j s ↦ {x | ‖(W ⊔ Submodule.span ℝ {u j}).starProjection (x - a) -
      inner ℝ ((W ⊔ Submodule.span ℝ {u j}).starProjection (x - a)) (u j) • u j‖ <
        s * ‖(W ⊔ Submodule.span ℝ {u j}).starProjection (x - a)‖})
    (∃ b ∈ A, b ≠ a ∧ dist b a < δ ∧ W.starProjection (b - a) = 0)
    (fun j ↦ ∃ b ∈ A, b ≠ a ∧ dist b a < δ ∧ (W ⊔ Submodule.span ℝ {u j}).starProjection (b - a) -
      inner ℝ ((W ⊔ Submodule.span ℝ {u j}).starProjection (b - a)) (u j) • u j = 0)
    (Real.sqrt_pos.2 (Nat.cast_pos.2 hℓ)) ?_ ?_ ?_ hslab
  · -- `Z_j(s) ⊆ X(s)`, since `|p_j y| ≤ |y|`.
    intro j s hs x hx
    simp only [Set.mem_ofPred_eq, hq] at hx ⊢
    exact hx.trans_le
      (mul_le_mul_of_nonneg_left (Submodule.norm_starProjection_apply_le _ _) hs.le)
  · -- `X(s) ⊆ ⋃_j Z_j(√ℓ s)`, by the cone cover and `P y + (y · u_j) u_j = p_j y`.
    intro s _ x hx
    obtain ⟨j, hj⟩ := Submission.bf_cone_subset_iUnion_slabCones n ℓ hℓ W hWn u hu hW (x - a) s hx
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    simp only [Set.mem_ofPred_eq, hq]
    rwa [hp]
  · -- `Ax'_j ⇒ Ax`.
    rintro j ⟨b, hbA, hba, hbδ, hb⟩
    exact ⟨b, hbA, hba, hbδ, (hq j (b - a)).symm.trans hb⟩

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
