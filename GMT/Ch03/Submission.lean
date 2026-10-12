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

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
