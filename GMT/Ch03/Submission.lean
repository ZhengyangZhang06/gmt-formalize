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

/-- **Linearity of `g ↦ ∫_S div g` on `C¹` vector fields** (Step 1 of the extension of
`g ↦ ∫_{E ∩ U} div g` used for Simon Ch. 3, (4.1) (p. 80); the linearity behind the remark after
Ch. 2, (2.1) (p. 48, `chapter-02.txt` lines 480–498)). For an arbitrary set `S ⊆ ℝᴺ`:
(i) if `g, h` are `C¹` with compact support then `∫_S div(g + h) = ∫_S div g + ∫_S div h`;
(ii) if `g` is `C¹` and `c ∈ ℝ` then `∫_S div(c g) = c ∫_S div g`. For `C¹` fields
`D(g + h) = Dg + Dh` and `D(c g) = c Dg`, and the trace is linear, so the integrands agree
pointwise. In (i), `div g = ∑ᵢ ⟨bᵢ, Dg(·) bᵢ⟩` is continuous and vanishes off `tsupport g`, hence
is integrable on `S`, and the integral is additive; in (ii) the constant comes out of the integral
without any integrability hypothesis. -/
theorem Submission.gaussGreenRep_setIntegral_divergence_linear : ∀ (N : ℕ) (S : Set (Rn N)), (∀ g h : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → ContDiff ℝ 1 h → HasCompactSupport h → ∫ x in S, Poincare.SimonGMT.Chapter02.euclideanDivergence (g + h) x = (∫ x in S, Poincare.SimonGMT.Chapter02.euclideanDivergence g x) + ∫ x in S, Poincare.SimonGMT.Chapter02.euclideanDivergence h x) ∧ ∀ (c : ℝ) (g : Rn N → Rn N), ContDiff ℝ 1 g → ∫ x in S, Poincare.SimonGMT.Chapter02.euclideanDivergence (c • g) x = c * ∫ x in S, Poincare.SimonGMT.Chapter02.euclideanDivergence g x := by
  intro N S
  -- Steps 1–2: for `C¹` compactly supported `g`, `div g` is continuous with compact support,
  -- hence integrable on `S`.
  have hint : ∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g →
      IntegrableOn (Poincare.SimonGMT.Chapter02.euclideanDivergence g) S := by
    intro g hg hgc
    have hcont : Continuous (Poincare.SimonGMT.Chapter02.euclideanDivergence g) := by
      have hDg := hg.continuous_fderiv one_ne_zero
      simp only [funext (Poincare.SimonGMT.Chapter02.euclideanDivergence_eq_sum_inner
        (stdOrthonormalBasis ℝ (Rn N)) g)]
      exact continuous_finsetSum _ fun i _ ↦ continuous_const.inner (hDg.clm_apply continuous_const)
    have hsupp : HasCompactSupport (Poincare.SimonGMT.Chapter02.euclideanDivergence g) :=
      hgc.mono' (Poincare.SimonGMT.Chapter02.support_euclideanDivergence_subset g)
    exact (hcont.integrable_of_hasCompactSupport hsupp).integrableOn
  refine ⟨fun g h hg hgc hh hhc ↦ ?_, fun c g hg ↦ ?_⟩
  · -- Steps 3–4: `div (g + h) = div g + div h` pointwise, and the integral is additive.
    have hpt : ∀ x, Poincare.SimonGMT.Chapter02.euclideanDivergence (g + h) x =
        Poincare.SimonGMT.Chapter02.euclideanDivergence g x +
          Poincare.SimonGMT.Chapter02.euclideanDivergence h x := by
      intro x
      simp only [Poincare.SimonGMT.Chapter02.euclideanDivergence,
        fderiv_add (hg.differentiable one_ne_zero x) (hh.differentiable one_ne_zero x),
        ContinuousLinearMap.toLinearMap_add, map_add]
    simp only [hpt]
    exact integral_add (hint g hg hgc) (hint h hh hhc)
  · -- Steps 5–6: `div (c • g) = c * div g` pointwise, and `c` comes out of the integral.
    have hpt : ∀ x, Poincare.SimonGMT.Chapter02.euclideanDivergence (c • g) x =
        c * Poincare.SimonGMT.Chapter02.euclideanDivergence g x := by
      intro x
      simp only [Poincare.SimonGMT.Chapter02.euclideanDivergence,
        fderiv_const_smul (hg.differentiable one_ne_zero x) c,
        ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul]
    simp only [hpt]
    exact integral_const_mul c _
/-- **Simon Ch. 2, (2.1) and the remark after it, for `u = χ_E` (Ch. 3, §4, p. 80).** If `E` has
locally finite perimeter in the open set `U` and `K ⊆ U` is compact, there is `C ≥ 0` with
`|∫_{E ∩ U} div g| ≤ C M` for every `C¹` field `g` with compact support in `K` and `|g| ≤ M`.
Choose an open `W` with `K ⊆ W ⊂⊂ U` and take `C = c(W)` from (2.1). Since `div g = 0` off
`tsupport g ⊆ W ⊆ U`, `∫_W χ_E div g = ∫_{E ∩ U} div g`, and `sup |g| ≤ M`; this gives the upper
bound, and the lower bound follows from the upper bound for `-g`, as `div (-g) = -div g`. -/
theorem Submission.gaussGreenRep_divergence_integral_local_bound : ∀ (N : ℕ) (U E : Set (Rn N)), IsOpen U → NullMeasurableSet E volume → HasLocallyFinitePerimeter U E → ∀ K : Set (Rn N), IsCompact K → K ⊆ U → ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ K → ∀ M : ℝ, (∀ x, ‖g x‖ ≤ M) → |∫ x in E ∩ U, Poincare.SimonGMT.Chapter02.euclideanDivergence g x| ≤ C * M := by
  intro N U E hU hE hBV K hK hKU
  obtain ⟨-, -, hbound⟩ := hBV
  -- Step 1: an open `W` with `K ⊆ W` and `closure W` compact in `U`; (2.1) on `W` gives `c ≥ 0`.
  obtain ⟨W, hWo, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨c, hc, hcW⟩ := hbound W hWo ⟨hWc, hWU⟩
  refine ⟨c, hc, ?_⟩
  -- Step 2: the upper bound `∫_{E ∩ U} div g ≤ c M`.
  have hupper : ∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ K →
      ∀ M : ℝ, (∀ x, ‖g x‖ ≤ M) →
        ∫ x in E ∩ U, Poincare.SimonGMT.Chapter02.euclideanDivergence g x ≤ c * M := by
    intro g hg hgc hgK M hM
    -- (a) `g` is a `C¹` test field in `C_c(ℝᴺ, ℝᴺ)` supported in `W`.
    let G : C_c(Rn N, Rn N) := ⟨⟨g, hg.continuous⟩, hgc⟩
    have ha := hcW G hg (hgK.trans hKW)
    -- (b) `∫_W χ_E div g = ∫_{E ∩ U} div g`, since `div g` vanishes off `tsupport g ⊆ W ⊆ U`.
    have hb : ∫ x in W, E.indicator (fun _ ↦ (1 : ℝ)) x *
          Poincare.SimonGMT.Chapter02.euclideanDivergence g x =
        ∫ x in E ∩ U, Poincare.SimonGMT.Chapter02.euclideanDivergence g x := by
      rw [← integral_indicator hWo.measurableSet,
        ← integral_indicator₀ (hE.inter hU.measurableSet.nullMeasurableSet)]
      congr 1
      ext x
      by_cases hxW : x ∈ W
      · have hxU : x ∈ U := hWU (subset_closure hxW)
        by_cases hxE : x ∈ E <;> simp [hxW, hxU, hxE]
      · have hx0 : Poincare.SimonGMT.Chapter02.euclideanDivergence g x = 0 :=
          Function.notMem_support.mp fun hx ↦
            hxW (hKW (hgK (Poincare.SimonGMT.Chapter02.support_euclideanDivergence_subset g hx)))
        rw [Set.indicator_of_notMem hxW, eq_comm, Set.indicator_apply_eq_zero]
        exact fun _ ↦ hx0
    -- (c) `sup |g| ≤ M`.
    have hsup : Poincare.SimonGMT.Chapter02.compactlySupportedSupNorm G ≤ M :=
      csSup_le (Set.range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact hM x)
    -- (d) Combine.
    calc ∫ x in E ∩ U, Poincare.SimonGMT.Chapter02.euclideanDivergence g x
        = ∫ x in W, E.indicator (fun _ ↦ (1 : ℝ)) x *
            Poincare.SimonGMT.Chapter02.euclideanDivergence g x := hb.symm
      _ ≤ c * Poincare.SimonGMT.Chapter02.compactlySupportedSupNorm G := ha
      _ ≤ c * M := mul_le_mul_of_nonneg_left hsup hc
  -- Step 3: the lower bound, from step 2 for `-g`, using `div (-g) = -div g`.
  intro g hg hgc hgK M hM
  have hneg : ∀ x, Poincare.SimonGMT.Chapter02.euclideanDivergence (-g) x =
      -Poincare.SimonGMT.Chapter02.euclideanDivergence g x := by
    intro x
    simp only [Poincare.SimonGMT.Chapter02.euclideanDivergence, fderiv_neg,
      ContinuousLinearMap.toLinearMap_neg, map_neg]
  have hlower := hupper (-g) hg.neg hgc.neg (by rwa [tsupport_neg]) M (by simpa using hM)
  simp only [hneg, integral_neg] at hlower
  -- Step 4: `-c M ≤ ∫_{E ∩ U} div g ≤ c M`.
  exact abs_le.mpr ⟨by linarith, hupper g hg hgc hgK M hM⟩
/-- **Extension of a locally sup-bounded functional from `C¹_c` fields to `C_c` fields** (the
remark after Simon Ch. 2, (2.1), p. 48, used for Ch. 3, (4.1)). If `Λ₀` is additive and
homogeneous on `C¹` fields with compact support in `U` and `|Λ₀ g| ≤ C(K) sup |g|` for such fields
supported in a compact `K ⊆ U`, and every continuous compactly supported field is a uniform limit
of `C¹` fields supported in a fixed compact subset of any open neighbourhood of its support, then
`Λ₀` extends to a functional `Λ` on continuous compactly supported fields in `U` that is additive,
homogeneous and bounded above on unit fields supported in each compact `K ⊆ U`. `Λ g` is the limit
of `Λ₀ (h_k)` along any sequence of `C¹` fields `h_k → g` uniformly with supports in one compact
subset of `U`; this limit exists and does not depend on the sequence by the bound on `Λ₀`. -/
theorem Submission.gaussGreenRep_extend_C1_functional : ∀ (N : ℕ) (U : Set (Rn N))
    (Λ₀ : (Rn N → Rn N) → ℝ), IsOpen U →
    (∀ (g : Rn N → Rn N) (W : Set (Rn N)), Continuous g → HasCompactSupport g → IsOpen W →
      tsupport g ⊆ W → ∃ K : Set (Rn N), IsCompact K ∧ tsupport g ⊆ K ∧ K ⊆ W ∧
        ∃ h : ℕ → Rn N → Rn N, (∀ k, ContDiff ℝ 1 (h k) ∧ HasCompactSupport (h k) ∧
          tsupport (h k) ⊆ K) ∧ TendstoUniformly h g atTop) →
    (∀ g h : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ U →
      ContDiff ℝ 1 h → HasCompactSupport h → tsupport h ⊆ U → Λ₀ (g + h) = Λ₀ g + Λ₀ h) →
    (∀ (c : ℝ) (g : Rn N → Rn N), ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ U →
      Λ₀ (c • g) = c * Λ₀ g) →
    (∀ K : Set (Rn N), IsCompact K → K ⊆ U → ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Rn N → Rn N,
      ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ K → ∀ M : ℝ, (∀ x, ‖g x‖ ≤ M) →
        |Λ₀ g| ≤ C * M) →
    ∃ Λ : (Rn N → Rn N) → ℝ,
      (∀ g h : Rn N → Rn N, Continuous g → HasCompactSupport g → tsupport g ⊆ U →
        Continuous h → HasCompactSupport h → tsupport h ⊆ U → Λ (g + h) = Λ g + Λ h) ∧
      (∀ (c : ℝ) (g : Rn N → Rn N), Continuous g → HasCompactSupport g → tsupport g ⊆ U →
        Λ (c • g) = c * Λ g) ∧
      (∀ K : Set (Rn N), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ g : Rn N → Rn N, Continuous g →
        tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → Λ g ≤ C) ∧
      ∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ U → Λ g = Λ₀ g := by
  intro N U Λ₀ hU happ hadd hhom hbd
  -- Two sequences of `C¹` fields supported in one compact `L ⊆ U` and converging uniformly to the
  -- same `g`: `Λ₀ (s m) - Λ₀ (s' n) = Λ₀ (s m - s' n)` and `|s m - s' n| ≤ 2δ` for large `m, n`.
  have hclose : ∀ (g : Rn N → Rn N) (s s' : ℕ → Rn N → Rn N) (L : Set (Rn N)),
      IsCompact L → L ⊆ U →
      (∀ k, ContDiff ℝ 1 (s k) ∧ HasCompactSupport (s k) ∧ tsupport (s k) ⊆ L) →
      (∀ k, ContDiff ℝ 1 (s' k) ∧ HasCompactSupport (s' k) ∧ tsupport (s' k) ⊆ L) →
      TendstoUniformly s g atTop → TendstoUniformly s' g atTop →
      ∀ ε > 0, ∃ k₀ : ℕ, ∀ m ≥ k₀, ∀ n ≥ k₀, |Λ₀ (s m) - Λ₀ (s' n)| < ε := by
    intro g s s' L hL hLU hs hs' hsg hs'g ε hε
    obtain ⟨C, hC0, hC⟩ := hbd L hL hLU
    have hC1 : 0 < C + 1 := by linarith
    have hδ : 0 < ε / (2 * (C + 1)) := div_pos hε (by linarith)
    obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hsg _ hδ)
    obtain ⟨k₂, hk₂⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hs'g _ hδ)
    refine ⟨max k₁ k₂, fun m hm n hn => ?_⟩
    have hm' := hk₁ m (le_of_max_le_left hm)
    have hn' := hk₂ n (le_of_max_le_right hn)
    have hd : ContDiff ℝ 1 (s m - s' n) := (hs m).1.sub (hs' n).1
    have hdc : HasCompactSupport (s m - s' n) := (hs m).2.1.sub (hs' n).2.1
    have hdL : tsupport (s m - s' n) ⊆ L :=
      (tsupport_sub (s m) (s' n)).trans (union_subset (hs m).2.2 (hs' n).2.2)
    have hsplit := hadd (s m - s' n) (s' n) hd hdc (hdL.trans hLU) (hs' n).1 (hs' n).2.1
      ((hs' n).2.2.trans hLU)
    rw [sub_add_cancel] at hsplit
    have hle := hC (s m - s' n) hd hdc hdL (2 * (ε / (2 * (C + 1)))) fun x => by
      rw [Pi.sub_apply, ← dist_eq_norm]
      linarith [dist_triangle_left (s m x) (s' n x) (g x), hm' x, hn' x]
    rw [hsplit, add_sub_cancel_right]
    refine hle.trans_lt ?_
    rw [show C * (2 * (ε / (2 * (C + 1)))) = C / (C + 1) * ε by field_simp]
    exact mul_lt_of_lt_one_left hε ((div_lt_one hC1).mpr (lt_add_one C))
  -- Choose, for every admissible `g`, an approximating sequence `S g` (hypothesis with `W = U`).
  have hseq : ∀ g : Rn N → Rn N, ∃ s : ℕ → Rn N → Rn N,
      Continuous g → HasCompactSupport g → tsupport g ⊆ U → ∃ L : Set (Rn N), IsCompact L ∧
        L ⊆ U ∧ (∀ k, ContDiff ℝ 1 (s k) ∧ HasCompactSupport (s k) ∧ tsupport (s k) ⊆ L) ∧
          TendstoUniformly s g atTop := by
    intro g
    by_cases hg : Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ U
    · obtain ⟨K, hK, -, hKU, h, hh, hhg⟩ := happ g U hg.1 hg.2.1 hU hg.2.2
      exact ⟨h, fun _ _ _ => ⟨K, hK, hKU, hh, hhg⟩⟩
    · exact ⟨0, fun h₁ h₂ h₃ => absurd ⟨h₁, h₂, h₃⟩ hg⟩
  choose S hS using hseq
  -- `Λ₀ (s k) → lim Λ₀ (S g k)` along every approximating sequence `s` of an admissible `g`.
  have hstar : ∀ g : Rn N → Rn N, Continuous g → HasCompactSupport g → tsupport g ⊆ U →
      ∀ (s : ℕ → Rn N → Rn N) (L : Set (Rn N)), IsCompact L → L ⊆ U →
      (∀ k, ContDiff ℝ 1 (s k) ∧ HasCompactSupport (s k) ∧ tsupport (s k) ⊆ L) →
      TendstoUniformly s g atTop →
      Tendsto (fun k => Λ₀ (s k)) atTop (𝓝 (limUnder atTop fun k => Λ₀ (S g k))) := by
    intro g hg hgc hgU s L hL hLU hs hsg
    obtain ⟨L', hL', hL'U, hSg, hSgt⟩ := hS g hg hgc hgU
    have hLL : IsCompact (L ∪ L') := hL.union hL'
    have hLLU : L ∪ L' ⊆ U := union_subset hLU hL'U
    have hs2 : ∀ k, ContDiff ℝ 1 (s k) ∧ HasCompactSupport (s k) ∧ tsupport (s k) ⊆ L ∪ L' :=
      fun k => ⟨(hs k).1, (hs k).2.1, (hs k).2.2.trans subset_union_left⟩
    have hS2 : ∀ k, ContDiff ℝ 1 (S g k) ∧ HasCompactSupport (S g k) ∧
        tsupport (S g k) ⊆ L ∪ L' :=
      fun k => ⟨(hSg k).1, (hSg k).2.1, (hSg k).2.2.trans subset_union_right⟩
    have hcauchy : CauchySeq fun k => Λ₀ (S g k) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨k₀, hk₀⟩ := hclose g (S g) (S g) _ hLL hLLU hS2 hS2 hSgt hSgt ε hε
      exact ⟨k₀, fun m hm n hn => by rw [Real.dist_eq]; exact hk₀ m hm n hn⟩
    have hlim := Metric.tendsto_atTop.mp hcauchy.tendsto_limUnder
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k₁, hk₁⟩ := hlim (ε / 2) (half_pos hε)
    obtain ⟨k₀, hk₀⟩ := hclose g s (S g) _ hLL hLLU hs2 hS2 hsg hSgt (ε / 2) (half_pos hε)
    refine ⟨max k₀ k₁, fun n hn => ?_⟩
    have h₁ := hk₁ n (le_of_max_le_right hn)
    have h₂ := hk₀ n (le_of_max_le_left hn) n (le_of_max_le_left hn)
    rw [Real.dist_eq] at h₁ ⊢
    calc |Λ₀ (s n) - limUnder atTop (fun k => Λ₀ (S g k))|
        ≤ |Λ₀ (s n) - Λ₀ (S g n)| + |Λ₀ (S g n) - limUnder atTop (fun k => Λ₀ (S g k))| :=
          abs_sub_le _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h₂ h₁
      _ = ε := add_halves ε
  refine ⟨fun g => limUnder atTop fun k => Λ₀ (S g k), ?_, ?_, ?_, ?_⟩
  · -- Additivity: `S g + S h` approximates `g + h`.
    intro g h hg hgc hgU hh hhc hhU
    obtain ⟨L, hL, hLU, hSg, hSgt⟩ := hS g hg hgc hgU
    obtain ⟨L', hL', hL'U, hSh, hSht⟩ := hS h hh hhc hhU
    have h₁ := hstar (g + h) (hg.add hh) (hgc.add hhc)
      ((tsupport_add g h).trans (union_subset hgU hhU)) (fun k => S g k + S h k) (L ∪ L')
      (hL.union hL') (union_subset hLU hL'U)
      (fun k => ⟨(hSg k).1.add (hSh k).1, (hSg k).2.1.add (hSh k).2.1,
        (tsupport_add (S g k) (S h k)).trans (union_subset_union (hSg k).2.2 (hSh k).2.2)⟩)
      (hSgt.add hSht)
    have h₂ := (hstar g hg hgc hgU (S g) L hL hLU hSg hSgt).add
      (hstar h hh hhc hhU (S h) L' hL' hL'U hSh hSht)
    refine tendsto_nhds_unique h₁ (h₂.congr fun k => ?_)
    exact (hadd _ _ (hSg k).1 (hSg k).2.1 ((hSg k).2.2.trans hLU) (hSh k).1 (hSh k).2.1
      ((hSh k).2.2.trans hL'U)).symm
  · -- Homogeneity: `c • S g` approximates `c • g`.
    intro c g hg hgc hgU
    obtain ⟨L, hL, hLU, hSg, hSgt⟩ := hS g hg hgc hgU
    have hcs : TendstoUniformly (fun k => c • S g k) (c • g) atTop := by
      rw [Metric.tendstoUniformly_iff] at hSgt ⊢
      intro ε hε
      have hc1 : 0 < ‖c‖ + 1 := by positivity
      filter_upwards [hSgt (ε / (‖c‖ + 1)) (div_pos hε hc1)] with k hk x
      show dist (c • g x) (c • S g k x) < ε
      rw [dist_smul₀]
      calc ‖c‖ * dist (g x) (S g k x) ≤ ‖c‖ * (ε / (‖c‖ + 1)) :=
            mul_le_mul_of_nonneg_left (hk x).le (norm_nonneg c)
        _ < (‖c‖ + 1) * (ε / (‖c‖ + 1)) :=
            mul_lt_mul_of_pos_right (lt_add_one _) (div_pos hε hc1)
        _ = ε := by field_simp
    have h₁ := hstar (c • g) (hg.const_smul c) (hgc.mono (Function.support_const_smul_subset c g))
      ((closure_mono (Function.support_const_smul_subset c g)).trans hgU) (fun k => c • S g k) L
      hL hLU (fun k => ⟨(hSg k).1.const_smul c,
        (hSg k).2.1.mono (Function.support_const_smul_subset c (S g k)),
        (closure_mono (Function.support_const_smul_subset c (S g k))).trans (hSg k).2.2⟩) hcs
    have h₂ := (hstar g hg hgc hgU (S g) L hL hLU hSg hSgt).const_mul c
    refine tendsto_nhds_unique h₁ (h₂.congr fun k => ?_)
    exact (hhom c _ (hSg k).1 (hSg k).2.1 ((hSg k).2.2.trans hLU)).symm
  · -- Bound: approximate inside an open `W ⊇ K` with compact closure in `U`.
    intro K hK hKU
    obtain ⟨W, hW, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    obtain ⟨C, hC0, hC⟩ := hbd (closure W) hWc hWU
    refine ⟨C, fun g hg hgK hg1 => ?_⟩
    have hgc : HasCompactSupport g := hK.of_isClosed_subset (isClosed_tsupport g) hgK
    obtain ⟨K', hK', -, hK'W, h, hh, hhg⟩ := happ g W hg hgc hW (hgK.trans hKW)
    have hlim := hstar g hg hgc (hgK.trans hKU) h K' hK' (hK'W.trans (subset_closure.trans hWU))
      hh hhg
    have hC1 : 0 < C + 1 := by linarith
    refine le_of_forall_pos_le_add fun ε hε => le_of_tendsto hlim ?_
    filter_upwards [Metric.tendstoUniformly_iff.mp hhg (ε / (C + 1)) (div_pos hε hC1)] with k hk
    have hbound := hC (h k) (hh k).1 (hh k).2.1 ((hh k).2.2.trans (hK'W.trans subset_closure))
      (1 + ε / (C + 1)) fun x => by
        have h₁ := norm_sub_norm_le (h k x) (g x)
        rw [← dist_eq_norm, dist_comm] at h₁
        linarith [hg1 x, hk x]
    have h₃ : C * (ε / (C + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ hC1]
      nlinarith
    calc Λ₀ (h k) ≤ |Λ₀ (h k)| := le_abs_self _
      _ ≤ C * (1 + ε / (C + 1)) := hbound
      _ ≤ C + ε := by rw [mul_add, mul_one]; linarith
  · -- Agreement on `C¹` fields: use the constant sequence.
    intro g hg hgc hgU
    have h₁ := hstar g hg.continuous hgc hgU (fun _ => g) (tsupport g) hgc.isCompact hgU
      (fun _ => ⟨hg, hgc, subset_rfl⟩)
      (Metric.tendstoUniformly_iff.mpr fun ε hε => Eventually.of_forall fun _ x => by
        simpa using hε)
    exact tendsto_nhds_unique h₁ tendsto_const_nhds
/-- **Uniform `C¹` approximation inside an open set** (the mollification step behind Simon
Ch. 2, (2.1), used for (4.1)): a continuous compactly supported field `g : ℝᴺ → ℝᴺ` with
`tsupport g ⊆ W`, `W` open, is the uniform limit of `C¹` fields `h_k` with compact supports in
one compact `K`, `tsupport g ⊆ K ⊆ W`. Take `K` a closed `δ`-neighbourhood of `tsupport g` inside
`W` and `h_k = φ_k * g`, `φ_k ≥ 0` a normalized smooth bump supported in `B_{ε_k}(0)`, where
`ε_k ≤ δ` is a modulus of uniform continuity of `g` for `1/(k+1)`: then `h_k` vanishes off the
`ε_k`-neighbourhood of `tsupport g` and `|h_k - g| ≤ 1/(k+1)` everywhere. -/
theorem Submission.gaussGreenRep_c1_uniform_approx : ∀ (N : ℕ) (g : Rn N → Rn N)
    (W : Set (Rn N)), Continuous g → HasCompactSupport g → IsOpen W → tsupport g ⊆ W →
    ∃ K : Set (Rn N), IsCompact K ∧ tsupport g ⊆ K ∧ K ⊆ W ∧ ∃ h : ℕ → Rn N → Rn N,
      (∀ k, ContDiff ℝ 1 (h k) ∧ HasCompactSupport (h k) ∧ tsupport (h k) ⊆ K) ∧
        TendstoUniformly h g atTop := by
  intro N g W hg hgc hW hgW
  -- `K` is a closed `δ`-neighbourhood of `S = tsupport g` contained in `W`.
  obtain ⟨δ, hδ, hδW⟩ := hgc.isCompact.exists_cthickening_subset_open hW hgW
  refine ⟨Metric.cthickening δ (tsupport g), hgc.isCompact.cthickening,
    Metric.self_subset_cthickening _, hδW, ?_⟩
  -- Uniform continuity: radii `0 < ε k ≤ δ` with `|g a - g b| < 1/(k+1)` when `|a - b| < ε k`.
  have hu := hgc.uniformContinuous_of_continuous hg
  have hη : ∀ k : ℕ, ∃ ε > 0, ε ≤ δ ∧
      ∀ a b, dist a b < ε → dist (g a) (g b) < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨ε, hε, hεg⟩ := Metric.uniformContinuous_iff.mp hu _ (Nat.one_div_pos_of_nat (n := k))
    exact ⟨min ε δ, lt_min hε hδ, min_le_right _ _,
      fun a b hab => hεg (hab.trans_le (min_le_left _ _))⟩
  choose ε hε hεδ hεg using hη
  -- Mollifiers: a smooth bump on `B_{ε k}(0)`, normalized to have integral `1`.
  have hφ : ∀ k : ℕ, ∃ φ : Rn N → ℝ, ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ (∀ x, 0 ≤ φ x) ∧
      ∫ x, φ x = 1 ∧ Function.support φ ⊆ Metric.ball 0 (ε k) := by
    intro k
    let b : ContDiffBump (0 : Rn N) := ⟨ε k / 2, ε k, half_pos (hε k), half_lt_self (hε k)⟩
    have hpos : 0 < ∫ x, b x :=
      b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero b.hasCompactSupport
        (fun x => b.nonneg) (x := 0)
        (by rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos (hε k)).le)]
            exact one_ne_zero)
    refine ⟨fun x => (∫ y, b y)⁻¹ * b x, contDiff_const.mul b.contDiff,
      b.hasCompactSupport.mono (Function.support_mul_subset_right _ _),
      fun x => mul_nonneg (inv_nonneg.2 hpos.le) b.nonneg, ?_, ?_⟩
    · rw [integral_const_mul, inv_mul_cancel₀ hpos.ne']
    · exact (Function.support_mul_subset_right _ _).trans b.support_eq.subset
  choose φ hφc hφs hφn hφi hφb using hφ
  refine ⟨fun k => convolution (φ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume, fun k => ?_, ?_⟩
  · -- `φ k * g` vanishes off the `ε k`-neighbourhood of `S`, as `g = 0` on `B_{ε k}(x)` there.
    have hsupp : Function.support (convolution (φ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
        Metric.thickening (ε k) (tsupport g) := by
      intro x hx
      by_contra hxt
      apply hx
      refine dist_le_zero.1 (dist_convolution_le (μ := volume) (z₀ := 0) le_rfl (hφb k) (hφn k)
        (hφi k) hg.aestronglyMeasurable fun y hy => ?_)
      have hyS : y ∉ tsupport g := fun hyS =>
        hxt (Metric.mem_thickening_iff.2 ⟨y, hyS, by rw [dist_comm]; exact hy⟩)
      rw [image_eq_zero_of_notMem_tsupport hyS, dist_self]
    have htsupp : tsupport (convolution (φ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
        Metric.cthickening δ (tsupport g) :=
      closure_minimal (hsupp.trans ((Metric.thickening_subset_cthickening _ _).trans
        (Metric.cthickening_mono (hεδ k) _))) Metric.isClosed_cthickening
    exact ⟨(hφs k).contDiff_convolution_left _ (hφc k) hg.locallyIntegrable,
      hgc.isCompact.cthickening.of_isClosed_subset (isClosed_tsupport _) htsupp, htsupp⟩
  · -- `|(φ k * g)(x) - g(x)| ≤ 1/(k+1)` for every `x`, since `|g y - g x| < 1/(k+1)` on
    -- `B_{ε k}(x)`.
    rw [Metric.tendstoUniformly_iff]
    intro η hη
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hη
    filter_upwards [eventually_ge_atTop k₀] with k hk x
    rw [dist_comm]
    refine lt_of_le_of_lt ?_ ((Nat.one_div_le_one_div hk).trans_lt hk₀)
    exact dist_convolution_le (μ := volume) (z₀ := g x) Nat.one_div_pos_of_nat.le (hφb k)
      (hφn k) (hφi k) hg.aestronglyMeasurable fun y hy => (hεg k y x hy).le

/-- **Simon Ch. 2, the remark after (2.1) (p. 48), for `u = χ_E` (Ch. 3, §4, p. 80).** If `E` has
locally finite perimeter in the open set `U`, the functional `g ↦ ∫_{E ∩ U} div g` on `C¹` fields
with compact support in `U` extends to a functional `Λ` on continuous fields with compact support
in `U` that is additive, homogeneous and, for each compact `K ⊆ U`, bounded above on the fields
supported in `K` with `|g| ≤ 1`. `Λ₀ g = ∫_{E ∩ U} div g` is linear on `C¹` fields and satisfies
`|Λ₀ g| ≤ C(K) sup |g|` for `g` supported in `K`; every continuous compactly supported field in
`U` is a uniform limit of `C¹` fields supported in one compact subset of `U`, and `Λ g` is the
limit of `Λ₀` along such approximations. -/
theorem Submission.gaussGreenRep_bv_functional_extension : ∀ (N : ℕ) (U E : Set (Rn N)), IsOpen U → NullMeasurableSet E volume → HasLocallyFinitePerimeter U E → ∃ Λ : (Rn N → Rn N) → ℝ, (∀ g h : Rn N → Rn N, Continuous g → HasCompactSupport g → tsupport g ⊆ U → Continuous h → HasCompactSupport h → tsupport h ⊆ U → Λ (g + h) = Λ g + Λ h) ∧ (∀ (c : ℝ) (g : Rn N → Rn N), Continuous g → HasCompactSupport g → tsupport g ⊆ U → Λ (c • g) = c * Λ g) ∧ (∀ K : Set (Rn N), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ g : Rn N → Rn N, Continuous g → tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → Λ g ≤ C) ∧ ∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ U → Λ g = ∫ x in E ∩ U, Poincare.SimonGMT.Chapter02.euclideanDivergence g x := by
  intro N U E hU hE hBV
  -- Step 1: `Λ₀ g = ∫_{E ∩ U} div g` is additive and homogeneous on `C¹` fields.
  obtain ⟨hadd, hsmul⟩ := Submission.gaussGreenRep_setIntegral_divergence_linear N (E ∩ U)
  -- Steps 4–10: extend `Λ₀` along uniform `C¹` approximations supported in a fixed compact subset
  -- of `U` (step 4), using the two-sided bound `|Λ₀ g| ≤ C(K) sup |g|` (steps 0, 2, 3); the last
  -- conjunct, `Λ = Λ₀` on `C¹` fields, is (d).
  exact Submission.gaussGreenRep_extend_C1_functional N U
    (fun g ↦ ∫ x in E ∩ U, Poincare.SimonGMT.Chapter02.euclideanDivergence g x) hU
    (Submission.gaussGreenRep_c1_uniform_approx N)
    (fun g h hg hgc _ hh hhc _ ↦ hadd g h hg hgc hh hhc) (fun c g hg _ _ ↦ hsmul c g hg)
    (Submission.gaussGreenRep_divergence_integral_local_bound N U E hU hE hBV)

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
