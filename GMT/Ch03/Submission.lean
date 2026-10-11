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
      Metric.eventually_nhds_iff.mp ((hdiff x hx).isLittleO.def (half_pos he))
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

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
