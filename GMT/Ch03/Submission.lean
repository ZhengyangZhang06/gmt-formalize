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

/-- **A uniform closed-ball bound gives `μ(B) ≤ c μH[n](B)`** (the covering step behind
`μ_E ≤ Hⁿ ⌞ ∂*E` in Simon Ch. 3, Theorem 4.3; cf. the proof of Ch. 1, Theorem 3.26(2)). Let
`B ⊆ ℝᴺ` be arbitrary, `0 < c < ∞`, `δ > 0`, and `μ(B̄_ρ(x)) ≤ c ρⁿ` for all `x ∈ B` and
`0 < ρ < δ`. The outer measure `ν(C) = μ(C ∩ B)` satisfies `ν(C) ≤ c (diam C)ⁿ` whenever
`diam C ≤ δ / 2`: for `x ∈ C ∩ B` and `ρ ∈ (diam C, δ)` we have `C ∩ B ⊆ B̄_ρ(x)`, and we let
`ρ ↓ diam C`. Hence `ν ≤ mkMetric (c • tⁿ) = c • μH[n]`, so `μ(B) = ν(B) ≤ c μH[n](B)`. -/
theorem Submission.deGiorgiRH_measure_le_mul_hausdorffMeasure_of_closedBall_le : ∀ (n N : ℕ) (μ : Measure (Rn N)) (B : Set (Rn N)) (c : ℝ≥0∞) (δ : ℝ), c ≠ 0 → c ≠ ∞ → 0 < δ → (∀ x ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < δ → μ (Metric.closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ n)) → μ B ≤ c * μH[(n : ℝ)] B := by
  intro n N μ B c δ hc0 hctop hδ hball
  -- Step 1: the outer measure `ν(C) = μ(C ∩ B)`, compared with `mkMetric (c • tⁿ)` at scale `δ / 2`.
  let ν : OuterMeasure (Rn N) := OuterMeasure.restrict B μ.toOuterMeasure
  have hle : ν ≤ OuterMeasure.mkMetric (c • fun t : ℝ≥0∞ => t ^ (n : ℝ)) := by
    refine OuterMeasure.le_mkMetric _ ν (ENNReal.ofReal (δ / 2))
      (ENNReal.ofReal_pos.mpr (half_pos hδ)) ?_
    -- Step 2: `ν(C) ≤ c (diam C)ⁿ` whenever `diam C ≤ δ / 2`.
    intro s hs
    change μ.toOuterMeasure.restrict B s ≤ _
    rw [OuterMeasure.restrict_apply, Measure.toOuterMeasure_apply]
    -- (a) If `C ∩ B = ∅`, then `ν(C) = 0`.
    rcases (s ∩ B).eq_empty_or_nonempty with hempty | ⟨x, hxs, hxB⟩
    · simp [hempty]
    -- (b) Otherwise fix `x ∈ C ∩ B`; `d = diam C` is real with `0 ≤ d ≤ δ / 2 < δ`.
    have hdfin : Metric.ediam s ≠ ∞ := (hs.trans_lt ENNReal.ofReal_lt_top).ne
    set d : ℝ := (Metric.ediam s).toReal with hd
    have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
    have hdediam : ENNReal.ofReal d = Metric.ediam s := ENNReal.ofReal_toReal hdfin
    have hdδ : d < δ := by
      have : d ≤ δ / 2 := ENNReal.toReal_le_of_le_ofReal (by linarith) hs
      linarith
    -- (c) `ρ ↦ c ρⁿ` is continuous since `c ≠ ∞`; let `ρ ↓ d` in `ν(C) ≤ μ(B̄_ρ(x)) ≤ c ρⁿ`.
    have hlim : Tendsto (fun ρ : ℝ => c * ENNReal.ofReal (ρ ^ n)) (𝓝[>] d)
        (𝓝 (c * ENNReal.ofReal (d ^ n))) := by
      have : Tendsto (fun ρ : ℝ => ENNReal.ofReal (ρ ^ n)) (𝓝[>] d)
          (𝓝 (ENNReal.ofReal (d ^ n))) :=
        ((ENNReal.continuous_ofReal.comp (continuous_pow n)).tendsto d).mono_left
          nhdsWithin_le_nhds
      exact ENNReal.Tendsto.const_mul this (Or.inr hctop)
    have hmass : μ (s ∩ B) ≤ c * ENNReal.ofReal (d ^ n) := by
      apply ge_of_tendsto hlim
      filter_upwards [Ioo_mem_nhdsGT hdδ] with ρ hρ
      have hρ0 : 0 < ρ := hd0.trans_lt hρ.1
      have hsub : s ∩ B ⊆ Metric.closedBall x ρ := by
        intro y hy
        rw [Metric.mem_closedBall]
        have h1 : edist y x ≤ Metric.ediam s := Metric.edist_le_ediam_of_mem hy.1 hxs
        have h2 : dist y x ≤ d := by
          rw [dist_edist]
          exact ENNReal.toReal_mono hdfin h1
        linarith [hρ.1]
      exact (measure_mono hsub).trans (hball x hxB ρ hρ0 hρ.2)
    calc μ (s ∩ B) ≤ c * ENNReal.ofReal (d ^ n) := hmass
      _ = (c • fun t : ℝ≥0∞ => t ^ (n : ℝ)) (Metric.ediam s) := by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← hdediam, ENNReal.ofReal_pow hd0, ENNReal.rpow_natCast]
  -- Steps 3–4: covers and the infimum over them are packaged in `le_mkMetric`; pull `c` out of
  -- `mkMetric` (`c ≠ 0`, `c ≠ ∞`) and identify `mkMetric (tⁿ)` with `μH[n]`.
  have h := hle B
  change μ.toOuterMeasure.restrict B B ≤ _ at h
  rw [OuterMeasure.restrict_apply, inter_self, OuterMeasure.mkMetric_smul _ hctop hc0,
    smul_apply, smul_eq_mul] at h
  calc μ B ≤ c * OuterMeasure.mkMetric (fun t : ℝ≥0∞ => t ^ (n : ℝ)) B := h
    _ = c * μH[(n : ℝ)] B := by
      rw [Measure.hausdorffMeasure, ← Measure.mkMetric_toOuterMeasure]
      rfl
/-- **Normalization `ωₙ μH[n] = 2ⁿ μHE[n]` on `ℝᴺ`** (parent Notation paragraph; Simon Ch. 1,
Theorems 2.9–2.10, `chapter-01.txt` lines 467–565), with `ωₙ = Lⁿ(B₁(0))`. Mathlib defines
`μHE[n] = cₙ • μH[n]`, where `Lⁿ = cₙ • μH[n]` on `ℝⁿ` (Haar uniqueness), so it suffices that
`μH[n](B₁(0)) = 2ⁿ`; for `n = 0`, `μHE[0] = μH[0]` and `ω₀ = μH[0]{0} = 1`. A leaf may not add
imports, so the kernel-checked SimonGMT proof of 2.9–2.10 (`Chapter01.SteinerSliceBounds`,
`SteinerDiameter`, `SteinerVolume`, `SteinerSymmetry`, `IsodiametricBounds`,
`EuclideanHausdorffUpper`, `EuclideanNormalization`) is reproduced inline:
* 2.10, `Lⁿ(C) ≤ ωₙ (diam C / 2)ⁿ`: replacing each coordinate slice by the centred interval of
  the same length (Steiner symmetrization) does not increase the diameter (a one-dimensional
  cross-distance bound) and, by Fubini, does not decrease the volume of a compact set. The
  closures of `n` successive symmetrizations are compact and symmetric in every coordinate
  reflection, hence centrally symmetric and contained in `B̄_{diam/2}(0)`;
* by 2.10, `2ⁿ ωₙ⁻¹ Lⁿ ≤ μH[n]` (`le_hausdorffMeasure`);
* conversely `μH[n] ≤ 2ⁿ ωₙ⁻¹ Lⁿ`: a Besicovitch cover by small closed balls with
  `∑ Lⁿ(B̄_ρ) ≤ Lⁿ(s) + ε`, `diam B̄_ρ ≤ 2ρ` and `Lⁿ(B̄_ρ) = ωₙ ρⁿ` bounds every `δ`-content.
Hence `μH[n](B₁(0)) = 2ⁿ`, `ωₙ = 2ⁿ cₙ`, and `ωₙ μH[n](s) = 2ⁿ cₙ μH[n](s) = 2ⁿ μHE[n](s)`. -/
theorem Submission.deGiorgiRH_unitBall_mul_hausdorffMeasure_eq_two_pow_mul :
    ∀ (n N : ℕ) (s : Set (Rn N)),
      volume (Metric.ball (0 : Rn n) 1) * μH[(n : ℝ)] s = 2 ^ n * μHE[n] s := by
  -- Simon 2.10, one-dimensional step: if all cross-distances of two nonempty real sets are `≤ d`,
  -- then so are those of the centred intervals of the same outer lengths.
  have hA1 : ∀ (A B : Set ℝ), A.Nonempty → B.Nonempty → ∀ d : ℝ,
      (∀ a ∈ A, ∀ b ∈ B, dist a b ≤ d) → ∀ x y : ℝ,
      |x| ≤ (volume A).toReal / 2 → |y| ≤ (volume B).toReal / 2 → dist x y ≤ d := by
    intro A B hA hB d hcross x y hx hy
    obtain ⟨a₀, ha₀⟩ := hA
    obtain ⟨b₀, hb₀⟩ := hB
    have hdist : ∀ a ∈ A, ∀ b ∈ B, a - b ≤ d ∧ b - a ≤ d := fun a ha b hb =>
      abs_sub_le_iff.mp (by simpa only [Real.dist_eq] using hcross a ha b hb)
    have hAl : BddBelow A := ⟨b₀ - d, fun a ha => by have := (hdist a ha b₀ hb₀).2; linarith⟩
    have hAu : BddAbove A := ⟨b₀ + d, fun a ha => by have := (hdist a ha b₀ hb₀).1; linarith⟩
    have hBl : BddBelow B := ⟨a₀ - d, fun b hb => by have := (hdist a₀ ha₀ b hb).1; linarith⟩
    have hBu : BddAbove B := ⟨a₀ + d, fun b hb => by have := (hdist a₀ ha₀ b hb).2; linarith⟩
    have hAB : sSup A ≤ d + sInf B := by
      apply csSup_le ⟨a₀, ha₀⟩
      intro a ha
      have h : a - d ≤ sInf B := le_csInf ⟨b₀, hb₀⟩ fun b hb => by
        have := (hdist a ha b hb).1
        linarith
      linarith
    have hBA : sSup B ≤ d + sInf A := by
      apply csSup_le ⟨b₀, hb₀⟩
      intro b hb
      have h : b - d ≤ sInf A := le_csInf ⟨a₀, ha₀⟩ fun a ha => by
        have := (hdist a ha b hb).2
        linarith
      linarith
    have hwA : 0 ≤ sSup A - sInf A :=
      sub_nonneg.mpr ((csInf_le hAl ha₀).trans (le_csSup hAu ha₀))
    have hwB : 0 ≤ sSup B - sInf B :=
      sub_nonneg.mpr ((csInf_le hBl hb₀).trans (le_csSup hBu hb₀))
    have hvA : volume A ≤ ENNReal.ofReal (sSup A - sInf A) := by
      rw [← Real.volume_Icc]
      exact measure_mono (subset_Icc_csInf_csSup hAl hAu)
    have hvB : volume B ≤ ENNReal.ofReal (sSup B - sInf B) := by
      rw [← Real.volume_Icc]
      exact measure_mono (subset_Icc_csInf_csSup hBl hBu)
    have hA' : (volume A).toReal ≤ sSup A - sInf A := ENNReal.toReal_le_of_le_ofReal hwA hvA
    have hB' : (volume B).toReal ≤ sSup B - sInf B := ENNReal.toReal_le_of_le_ofReal hwB hvB
    rw [Real.dist_eq]
    calc |x - y| ≤ |x| + |y| := abs_sub _ _
      _ ≤ (volume A).toReal / 2 + (volume B).toReal / 2 := add_le_add hx hy
      _ ≤ d := by linarith
  -- The centred interval has the outer length of the slice.
  have hB1 : ∀ T : Set ℝ, volume T ≠ ∞ →
      volume {t : ℝ | T.Nonempty ∧ |t| ≤ (volume T).toReal / 2} = volume T := by
    intro T hfin
    rcases T.eq_empty_or_nonempty with rfl | hT
    · simp
    · have hI : {t : ℝ | T.Nonempty ∧ |t| ≤ (volume T).toReal / 2} =
          Icc (-((volume T).toReal / 2)) ((volume T).toReal / 2) := by
        ext t
        simp [hT, abs_le]
      rw [hI, Real.volume_Icc,
        show (volume T).toReal / 2 - -((volume T).toReal / 2) = (volume T).toReal by ring]
      exact ENNReal.ofReal_toReal hfin
  -- Changing the `j`-th coordinates only changes the `j`-th term of the squared distance.
  have hC1 : ∀ (m : ℕ) (j : Fin m) (x y : Rn m) (a b : ℝ),
      dist (WithLp.toLp 2 (Function.update x.ofLp j a) : Rn m)
        (WithLp.toLp 2 (Function.update y.ofLp j b)) ^ 2 =
        dist x y ^ 2 - dist (x j) (y j) ^ 2 + dist a b ^ 2 := by
    intro m j x y a b
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
    have hsum := Finset.sum_erase_add Finset.univ
      (fun i : Fin m => dist (x i) (y i) ^ 2) (Finset.mem_univ j)
    have hsum' := Finset.sum_erase_add Finset.univ
      (fun i : Fin m => dist (Function.update x.ofLp j a i)
        (Function.update y.ofLp j b i) ^ 2) (Finset.mem_univ j)
    have hrest : (∑ i ∈ Finset.univ.erase j,
        dist (Function.update x.ofLp j a i) (Function.update y.ofLp j b i) ^ 2) =
        ∑ i ∈ Finset.univ.erase j, dist (x i) (y i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Function.update_of_ne (Finset.mem_erase.mp hi).1]
    rw [hrest, Function.update_self, Function.update_self] at hsum'
    linarith
  -- Steiner symmetrization `S_j(A)` in the `j`-th coordinate: each nonempty slice of `A` parallel
  -- to `e_j` is replaced by the centred closed interval of the same outer length.
  obtain ⟨St, mem_St⟩ : ∃ St : ∀ m : ℕ, Fin m → Set (Rn m) → Set (Rn m),
      ∀ (m : ℕ) (j : Fin m) (A : Set (Rn m)) (x : Rn m), x ∈ St m j A ↔
        ({t : ℝ | (WithLp.toLp 2 (Function.update x.ofLp j t) : Rn m) ∈ A}.Nonempty ∧
          |x j| ≤
            (volume {t : ℝ | (WithLp.toLp 2 (Function.update x.ofLp j t) : Rn m) ∈ A}).toReal /
              2) :=
    ⟨fun m j A => {x | {t : ℝ | (WithLp.toLp 2 (Function.update x.ofLp j t) : Rn m) ∈ A}.Nonempty ∧
      |x j| ≤
        (volume {t : ℝ | (WithLp.toLp 2 (Function.update x.ofLp j t) : Rn m) ∈ A}).toReal / 2},
      fun _ _ _ _ => Iff.rfl⟩
  -- `S_j` does not increase the diameter.
  have hD1 : ∀ (m : ℕ) (j : Fin m) (A : Set (Rn m)), Metric.ediam (St m j A) ≤ Metric.ediam A := by
    intro m j A
    by_cases hfin : Metric.ediam A = ∞
    · rw [hfin]
      exact le_top
    have hbounded : Bornology.IsBounded A := Metric.isBounded_iff_ediam_ne_top.mpr hfin
    have hdiam : Metric.ediam (St m j A) ≤ ENNReal.ofReal (Metric.diam A) := by
      apply Metric.ediam_le_of_forall_dist_le
      intro x hx y hy
      rw [mem_St] at hx hy
      have hsq : ∀ a ∈ {t : ℝ | (WithLp.toLp 2 (Function.update x.ofLp j t) : Rn m) ∈ A},
          ∀ b ∈ {t : ℝ | (WithLp.toLp 2 (Function.update y.ofLp j t) : Rn m) ∈ A},
          dist a b ^ 2 ≤ Metric.diam A ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2 := by
        intro a ha b hb
        have hd := Metric.dist_le_diam_of_mem hbounded ha hb
        have hsq' : dist (WithLp.toLp 2 (Function.update x.ofLp j a) : Rn m)
            (WithLp.toLp 2 (Function.update y.ofLp j b)) ^ 2 ≤ Metric.diam A ^ 2 :=
          pow_le_pow_left₀ dist_nonneg hd 2
        rw [hC1] at hsq'
        linarith
      have hD : 0 ≤ Metric.diam A ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2 := by
        obtain ⟨a, ha⟩ := hx.1
        obtain ⟨b, hb⟩ := hy.1
        exact (sq_nonneg (dist a b)).trans (hsq a ha b hb)
      have hcross : ∀ a ∈ {t : ℝ | (WithLp.toLp 2 (Function.update x.ofLp j t) : Rn m) ∈ A},
          ∀ b ∈ {t : ℝ | (WithLp.toLp 2 (Function.update y.ofLp j t) : Rn m) ∈ A},
          dist a b ≤ Real.sqrt (Metric.diam A ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2) := by
        intro a ha b hb
        have h := hsq a ha b hb
        have hsqrt := Real.sq_sqrt hD
        nlinarith [dist_nonneg (x := a) (y := b),
          Real.sqrt_nonneg (Metric.diam A ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2)]
      have hcentered := hA1 _ _ hx.1 hy.1 _ hcross _ _ hx.2 hy.2
      have hsqrt := Real.sq_sqrt hD
      have hcentered_sq : dist (x j) (y j) ^ 2 ≤
          Metric.diam A ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2 := by
        nlinarith [dist_nonneg (x := x j) (y := y j),
          Real.sqrt_nonneg (Metric.diam A ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2)]
      nlinarith [dist_nonneg (x := x) (y := y), Metric.diam_nonneg (s := A)]
    simpa only [Metric.diam, ENNReal.ofReal_toReal hfin] using hdiam
  -- For compact `A`, `S_j` does not decrease the volume (Fubini along `e_j`, comparing `S_j(A)`
  -- with a measurable hull).
  have hE1 : ∀ (m : ℕ) (j : Fin m) (A : Set (Rn m)), IsCompact A →
      volume A ≤ volume (St m j A) := by
    intro m j A hA
    cases m with
    | zero => exact Fin.elim0 j
    | succ k =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) j
      let φ : ℝ × (Fin k → ℝ) → Rn (k + 1) := fun p => WithLp.toLp 2 (e.symm p)
      have hφ : MeasurePreserving φ volume volume :=
        (PiLp.volume_preserving_toLp (Fin (k + 1))).comp
          (MeasurePreserving.symm e (volume_preserving_piFinSuccAbove _ j))
      have hφcoord : ∀ (t : ℝ) (z : Fin k → ℝ), φ (t, z) j = t := fun t z =>
        Fin.insertNth_apply_same (α := fun _ : Fin (k + 1) => ℝ) j t z
      let S := St (k + 1) j A
      let T := toMeasurable volume S
      have hT : MeasurableSet T := measurableSet_toMeasurable volume S
      have hTA : S ⊆ T := subset_toMeasurable volume S
      have hslice : ∀ (t : ℝ) (z : Fin k → ℝ),
          {s : ℝ | (WithLp.toLp 2 (Function.update (φ (t, z)).ofLp j s) : Rn (k + 1)) ∈ A} =
            (fun s => φ (s, z)) ⁻¹' A := by
        intro t z
        ext s
        change (WithLp.toLp 2 (Function.update (j.insertNth t z) j s) ∈ A) ↔
          WithLp.toLp 2 (j.insertNth s z) ∈ A
        rw [Fin.update_insertNth]
      have hfinite : ∀ z : Fin k → ℝ, volume ((fun t => φ (t, z)) ⁻¹' A) ≠ ∞ := by
        intro z
        have hproj : IsCompact ((fun x : Rn (k + 1) => x j) '' A) := hA.image (by fun_prop)
        have hsub : (fun t => φ (t, z)) ⁻¹' A ⊆ (fun x : Rn (k + 1) => x j) '' A := by
          intro t ht
          exact ⟨φ (t, z), ht, hφcoord t z⟩
        exact (measure_lt_top_of_subset hsub hproj.measure_lt_top.ne).ne
      calc
        volume A = volume (φ ⁻¹' A) :=
          (hφ.measure_preimage hA.measurableSet.nullMeasurableSet).symm
        _ = ∫⁻ z : Fin k → ℝ, volume ((fun t => φ (t, z)) ⁻¹' A) :=
          Measure.prod_apply_symm (hA.measurableSet.preimage hφ.measurable)
        _ = ∫⁻ z : Fin k → ℝ, volume {s : ℝ | ((fun t => φ (t, z)) ⁻¹' A).Nonempty ∧
              |s| ≤ (volume ((fun t => φ (t, z)) ⁻¹' A)).toReal / 2} := by
          apply lintegral_congr
          intro z
          exact (hB1 _ (hfinite z)).symm
        _ ≤ ∫⁻ z : Fin k → ℝ, volume ((fun t => φ (t, z)) ⁻¹' T) := by
          apply lintegral_mono
          intro z
          apply measure_mono
          intro t ht
          apply hTA
          rw [mem_St, hφcoord, hslice]
          exact ht
        _ = volume (φ ⁻¹' T) := (Measure.prod_apply_symm (hT.preimage hφ.measurable)).symm
        _ = volume T := hφ.measure_preimage hT.nullMeasurableSet
        _ = volume S := measure_toMeasurable S
  -- Reflection in the `j`-th coordinate hyperplane; `S_j(A)` is symmetric under it, `S_j` keeps the
  -- symmetry under the other coordinate reflections, and so do closures.
  obtain ⟨Rf, hRf⟩ : ∃ Rf : ∀ m : ℕ, Fin m → Rn m → Rn m,
      ∀ (m : ℕ) (j : Fin m) (x : Rn m),
        Rf m j x = WithLp.toLp 2 (Function.update x.ofLp j (-x j)) :=
    ⟨fun m j x => WithLp.toLp 2 (Function.update x.ofLp j (-x j)), fun _ _ _ => rfl⟩
  have hRf_same : ∀ (m : ℕ) (j : Fin m) (x : Rn m), Rf m j x j = -x j := by
    intro m j x
    rw [hRf]
    simp
  have hRf_ne : ∀ (m : ℕ) (i j : Fin m), i ≠ j → ∀ x : Rn m, Rf m j x i = x i := by
    intro m i j hij x
    rw [hRf]
    exact Function.update_of_ne hij _ _
  have hRf_inv : ∀ (m : ℕ) (j : Fin m) (x : Rn m), Rf m j (Rf m j x) = x := by
    intro m j x
    ext i
    by_cases hij : i = j
    · subst hij
      rw [hRf_same, hRf_same, neg_neg]
    · rw [hRf_ne m i j hij, hRf_ne m i j hij]
  have hRf_cont : ∀ (m : ℕ) (j : Fin m), Continuous (Rf m j) := by
    intro m j
    have h : Rf m j = fun x => WithLp.toLp 2 (Function.update x.ofLp j (-x j)) := funext (hRf m j)
    rw [h]
    apply (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp
    apply continuous_pi
    intro i
    by_cases hij : i = j
    · subst i
      simpa only [Function.update_self] using
        (show Continuous (fun x : Rn m => -x j) by fun_prop)
    · simpa only [Function.update_of_ne hij] using
        (show Continuous (fun x : Rn m => x i) by fun_prop)
  have hsl_same : ∀ (m : ℕ) (j : Fin m) (A : Set (Rn m)) (x : Rn m),
      {t : ℝ | (WithLp.toLp 2 (Function.update (Rf m j x).ofLp j t) : Rn m) ∈ A} =
        {t : ℝ | (WithLp.toLp 2 (Function.update x.ofLp j t) : Rn m) ∈ A} := by
    intro m j A x
    ext t
    rw [hRf]
    simp only [mem_ofPred_eq, Function.update_idem]
  have hRf_update : ∀ (m : ℕ) (i j : Fin m), i ≠ j → ∀ (x : Rn m) (t : ℝ),
      Rf m i (WithLp.toLp 2 (Function.update x.ofLp j t)) =
        WithLp.toLp 2 (Function.update (Rf m i x).ofLp j t) := by
    intro m i j hij x t
    ext k
    by_cases hki : k = i
    · subst k
      rw [hRf_same]
      simp [Function.update_of_ne hij, hRf_same]
    · rw [hRf_ne m k i hki]
      by_cases hkj : k = j
      · subst k
        simp
      · simp [Function.update_of_ne hkj, hRf_ne m k i hki]
  have hsl_refl : ∀ (m : ℕ) (i j : Fin m), i ≠ j → ∀ (A : Set (Rn m)),
      (∀ x ∈ A, Rf m i x ∈ A) → ∀ x : Rn m,
      {t : ℝ | (WithLp.toLp 2 (Function.update (Rf m i x).ofLp j t) : Rn m) ∈ A} =
        {t : ℝ | (WithLp.toLp 2 (Function.update x.ofLp j t) : Rn m) ∈ A} := by
    intro m i j hij A hA x
    ext t
    simp only [mem_ofPred_eq]
    rw [← hRf_update m i j hij]
    constructor
    · intro h
      simpa only [hRf_inv] using hA _ h
    · exact hA _
  have hSt_refl : ∀ (m : ℕ) (j : Fin m) (A : Set (Rn m)), ∀ x ∈ St m j A, Rf m j x ∈ St m j A := by
    intro m j A x hx
    rw [mem_St] at hx ⊢
    rw [hsl_same, hRf_same, abs_neg]
    exact hx
  have hSt_pres : ∀ (m : ℕ) (i j : Fin m), i ≠ j → ∀ (A : Set (Rn m)),
      (∀ x ∈ A, Rf m i x ∈ A) → ∀ x ∈ St m j A, Rf m i x ∈ St m j A := by
    intro m i j hij A hA x hx
    rw [mem_St] at hx ⊢
    rw [hsl_refl m i j hij A hA, hRf_ne m j i (Ne.symm hij)]
    exact hx
  have hcl_refl : ∀ (m : ℕ) (i : Fin m) (A : Set (Rn m)), (∀ x ∈ A, Rf m i x ∈ A) →
      ∀ x ∈ closure A, Rf m i x ∈ closure A := by
    intro m i A hA x hx
    have hsub : A ⊆ Rf m i ⁻¹' closure A := fun y hy => subset_closure (hA y hy)
    exact closure_minimal hsub (isClosed_closure.preimage (hRf_cont m i)) hx
  -- Symmetry under every coordinate reflection is central symmetry.
  have hneg : ∀ (m : ℕ) (A : Set (Rn m)), (∀ i, ∀ x ∈ A, Rf m i x ∈ A) → ∀ x ∈ A, -x ∈ A := by
    intro m A hA x hx
    have hmem : ∀ s : Finset (Fin m),
        (WithLp.toLp 2 (fun k => if k ∈ s then -x k else x k) : Rn m) ∈ A := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hx
      | @insert i s hi ih =>
        have h := hA i _ ih
        convert h using 1
        ext k
        by_cases hki : k = i
        · subst k
          rw [hRf_same]
          simp [hi]
        · rw [hRf_ne m k i hki]
          simp [hki]
    have heq : (WithLp.toLp 2 fun k => -x k : Rn m) = -x := by
      ext k
      rfl
    simpa only [Finset.mem_univ, ite_true, heq] using hmem Finset.univ
  -- The closures of `m` successive symmetrizations: a compact, centrally symmetric replacement
  -- with no larger diameter and no smaller volume.
  have hiter : ∀ (m : ℕ) (A : Set (Rn m)), IsCompact A →
      ∃ K : Set (Rn m), IsCompact K ∧ Metric.ediam K ≤ Metric.ediam A ∧ volume A ≤ volume K ∧
        ∀ x ∈ K, -x ∈ K := by
    intro m A hA
    have hfinite : ∀ s : Finset (Fin m), ∃ K : Set (Rn m), IsCompact K ∧
        Metric.ediam K ≤ Metric.ediam A ∧ volume A ≤ volume K ∧ ∀ i ∈ s, ∀ x ∈ K, Rf m i x ∈ K := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨A, hA, le_rfl, le_rfl, by simp⟩
      | @insert i s hi ih =>
        obtain ⟨K, hK, hdiam, hvol, hsym⟩ := ih
        refine ⟨closure (St m i K), ?_, ?_, ?_, ?_⟩
        · apply Bornology.IsBounded.isCompact_closure
          apply Metric.isBounded_iff_ediam_ne_top.mpr
          exact ne_top_of_le_ne_top hK.isBounded.ediam_ne_top (hD1 m i K)
        · rw [Metric.ediam_closure]
          exact (hD1 m i K).trans hdiam
        · exact hvol.trans ((hE1 m i K hK).trans (measure_mono subset_closure))
        · intro k hk
          rcases Finset.mem_insert.mp hk with hki | hk
          · subst k
            exact hcl_refl m i _ (hSt_refl m i K)
          · apply hcl_refl m k
            apply hSt_pres m k i
            · intro hki
              subst k
              exact hi hk
            · exact hsym k hk
    obtain ⟨K, hK, hdiam, hvol, hsym⟩ := hfinite Finset.univ
    exact ⟨K, hK, hdiam, hvol, hneg m K (fun i => hsym i (Finset.mem_univ i))⟩
  -- Simon 2.10 (isodiametric inequality): a centrally symmetric compact set lies in
  -- `B̄_{diam/2}(0)`.
  have hiso : ∀ (m : ℕ), 0 < m → ∀ C : Set (Rn m),
      volume C ≤ volume (Metric.ball (0 : Rn m) 1) * (Metric.ediam C / 2) ^ m := by
    intro m hm C
    have hω0 : volume (Metric.ball (0 : Rn m) 1) ≠ 0 :=
      (Metric.measure_ball_pos volume (0 : Rn m) one_pos).ne'
    by_cases hfin : Metric.ediam C = ∞
    · rw [hfin, ENNReal.top_div_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞), ENNReal.top_pow hm.ne',
        ENNReal.mul_top hω0]
      exact le_top
    have hb : Bornology.IsBounded C := Metric.isBounded_iff_ediam_ne_top.mpr hfin
    obtain ⟨K, hK, hdiam, hvol, hsym⟩ := hiter m (closure C) hb.isCompact_closure
    rw [Metric.ediam_closure] at hdiam
    have hKb : Bornology.IsBounded K := hK.isBounded
    have hsub : K ⊆ Metric.closedBall 0 (Metric.diam K / 2) := by
      intro x hx
      have hdist := Metric.dist_le_diam_of_mem hKb hx (hsym x hx)
      rw [dist_eq_norm_sub, sub_neg_eq_add, ← two_smul ℝ, norm_smul] at hdist
      norm_num at hdist
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    have hKfin : Metric.ediam K ≠ ∞ := hKb.ediam_ne_top
    have hr : 0 ≤ Metric.diam K / 2 := div_nonneg Metric.diam_nonneg zero_le_two
    calc volume C ≤ volume (closure C) := measure_mono subset_closure
      _ ≤ volume K := hvol
      _ ≤ volume (Metric.closedBall (0 : Rn m) (Metric.diam K / 2)) := measure_mono hsub
      _ = ENNReal.ofReal ((Metric.diam K / 2) ^ m) * volume (Metric.ball (0 : Rn m) 1) := by
          rw [Measure.addHaar_closedBall volume 0 hr, finrank_euclideanSpace_fin]
      _ = volume (Metric.ball (0 : Rn m) 1) * (Metric.ediam K / 2) ^ m := by
          rw [mul_comm, ENNReal.ofReal_pow hr, ENNReal.ofReal_div_of_pos two_pos,
            ENNReal.ofReal_ofNat, Metric.diam, ENNReal.ofReal_toReal hKfin]
      _ ≤ volume (Metric.ball (0 : Rn m) 1) * (Metric.ediam C / 2) ^ m := by gcongr
  -- Lower half of Simon 2.9, from 2.10: `2ⁿ ωₙ⁻¹ Lⁿ ≤ μH[n]`.
  have hlow : ∀ (n : ℕ), 0 < n → ∀ s : Set (Rn n),
      2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹ * volume s ≤ μH[(n : ℝ)] s := by
    intro n hn s
    have hω0 : volume (Metric.ball (0 : Rn n) 1) ≠ 0 :=
      (Metric.measure_ball_pos volume (0 : Rn n) one_pos).ne'
    have hωt : volume (Metric.ball (0 : Rn n) 1) ≠ ∞ := measure_ball_lt_top.ne
    have hle : (2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹) • (volume : Measure (Rn n)) ≤
        μH[(n : ℝ)] := by
      apply Measure.le_hausdorffMeasure _ _ 1 one_pos
      intro C _
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.rpow_natCast]
      calc 2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹ * volume C
          ≤ 2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹ *
              (volume (Metric.ball (0 : Rn n) 1) * (Metric.ediam C / 2) ^ n) := by
            gcongr
            exact hiso n hn C
        _ = (2 * (Metric.ediam C / 2)) ^ n := by
            rw [mul_pow, ← mul_assoc, mul_assoc (2 ^ n), ENNReal.inv_mul_cancel hω0 hωt, mul_one]
        _ = Metric.ediam C ^ n := by
            rw [ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]
    exact Measure.le_iff'.mp hle s
  -- Upper half of Simon 2.9: `μH[n] ≤ 2ⁿ ωₙ⁻¹ Lⁿ`, bounding every `r`-content by Besicovitch
  -- covers with closed balls of radius `< r / 2`.
  have hup : ∀ (n : ℕ) (s : Set (Rn n)),
      μH[(n : ℝ)] s ≤ 2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹ * volume s := by
    intro n s
    have hω0 : volume (Metric.ball (0 : Rn n) 1) ≠ 0 :=
      (Metric.measure_ball_pos volume (0 : Rn n) one_pos).ne'
    have hωt : volume (Metric.ball (0 : Rn n) 1) ≠ ∞ := measure_ball_lt_top.ne
    have hK0 : 2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹ ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ two_ne_zero) (ENNReal.inv_ne_zero.mpr hωt)
    have hKt : 2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹ ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) (ENNReal.inv_ne_top.mpr hω0)
    have hdiamB : ∀ (x : Rn n) (ρ : ℝ),
        Metric.ediam (Metric.closedBall x ρ) ≤ ENNReal.ofReal (2 * ρ) := by
      intro x ρ
      apply Metric.ediam_le_of_forall_dist_le
      intro u hu v hv
      calc dist u v ≤ dist u x + dist x v := dist_triangle _ _ _
        _ ≤ ρ + ρ := add_le_add hu (by simpa only [Metric.mem_closedBall, dist_comm] using hv)
        _ = 2 * ρ := (two_mul ρ).symm
    -- `diam B̄_ρ(x)ⁿ ≤ (2ρ)ⁿ = 2ⁿ ωₙ⁻¹ Lⁿ(B̄_ρ(x))`.
    have hball : ∀ (x : Rn n) (ρ : ℝ), 0 < ρ →
        Metric.ediam (Metric.closedBall x ρ) ^ (n : ℝ) ≤
          2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹ * volume (Metric.closedBall x ρ) := by
      intro x ρ hρ
      have hd : Metric.ediam (Metric.closedBall x ρ) ≤ 2 * ENNReal.ofReal ρ := by
        have h := hdiamB x ρ
        rwa [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat] at h
      rw [Measure.addHaar_closedBall volume x hρ.le, finrank_euclideanSpace_fin,
        ENNReal.rpow_natCast]
      calc Metric.ediam (Metric.closedBall x ρ) ^ n ≤ (2 * ENNReal.ofReal ρ) ^ n := by gcongr
        _ = 2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹ *
              (ENNReal.ofReal (ρ ^ n) * volume (Metric.ball (0 : Rn n) 1)) := by
            rw [mul_pow, ENNReal.ofReal_pow hρ.le, mul_assoc (2 ^ n),
              mul_comm (ENNReal.ofReal ρ ^ n), ← mul_assoc _ (volume (Metric.ball (0 : Rn n) 1)),
              ENNReal.inv_mul_cancel hω0 hωt, one_mul]
    rw [show (μH[(n : ℝ)] : Measure (Rn n)) s =
        OuterMeasure.mkMetric (fun r : ℝ≥0∞ => r ^ (n : ℝ)) s by
      rw [OuterMeasure.coe_mkMetric]
      rfl]
    simp only [OuterMeasure.mkMetric, OuterMeasure.mkMetric', OuterMeasure.iSup_apply]
    refine iSup₂_le fun r hr => ?_
    obtain ⟨d, -, hd, hdr⟩ := ENNReal.lt_iff_exists_real_btwn.mp hr
    have hdpos : 0 < d := ENNReal.ofReal_pos.mp hd
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hε' : (ε : ℝ≥0∞) / (2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹) ≠ 0 :=
      ENNReal.div_ne_zero.mpr ⟨by exact_mod_cast hε.ne', hKt⟩
    obtain ⟨t, ρ, ht, -, hρ, hcover, hsum⟩ :=
      Besicovitch.exists_closedBall_covering_tsum_measure_le (volume : Measure (Rn n)) hε'
        (fun _ => Ioo 0 (d / 2)) s (by
          intro x _ δ hδ
          have hmin : 0 < min (d / 2) δ := lt_min (half_pos hdpos) hδ
          refine ⟨min (d / 2) δ / 2, ⟨half_pos hmin, ?_⟩, half_pos hmin, ?_⟩
          · exact (half_lt_self hmin).trans_le (min_le_left _ _)
          · exact (half_lt_self hmin).trans_le (min_le_right _ _))
    have : Countable t := ht.to_subtype
    calc OuterMeasure.mkMetric'.pre (fun s : Set (Rn n) => Metric.ediam s ^ (n : ℝ)) r s
        ≤ OuterMeasure.mkMetric'.pre (fun s : Set (Rn n) => Metric.ediam s ^ (n : ℝ)) r
            (⋃ x ∈ t, Metric.closedBall x (ρ x)) := measure_mono hcover
      _ = OuterMeasure.mkMetric'.pre (fun s : Set (Rn n) => Metric.ediam s ^ (n : ℝ)) r
            (⋃ x : t, Metric.closedBall (x : Rn n) (ρ x)) := by rw [biUnion_eq_iUnion]
      _ ≤ ∑' x : t, OuterMeasure.mkMetric'.pre (fun s : Set (Rn n) => Metric.ediam s ^ (n : ℝ)) r
            (Metric.closedBall (x : Rn n) (ρ x)) := measure_iUnion_le _
      _ ≤ ∑' x : t, 2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹ *
            volume (Metric.closedBall (x : Rn n) (ρ x)) := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          have hρx := hρ x x.2
          refine (OuterMeasure.mkMetric'.pre_le ?_).trans (hball x (ρ x) hρx.1)
          calc Metric.ediam (Metric.closedBall (x : Rn n) (ρ x)) ≤ ENNReal.ofReal (2 * ρ x) :=
                hdiamB x (ρ x)
            _ ≤ ENNReal.ofReal d := ENNReal.ofReal_le_ofReal (by linarith [hρx.2])
            _ ≤ r := hdr.le
      _ = 2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹ *
            ∑' x : t, volume (Metric.closedBall (x : Rn n) (ρ x)) := ENNReal.tsum_mul_left
      _ ≤ 2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹ *
            (volume s + ε / (2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹)) := by gcongr
      _ = 2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹ * volume s + ε := by
          rw [mul_add, ENNReal.mul_div_cancel hK0 hKt]
  intro n N s
  rcases Nat.eq_zero_or_pos n with rfl | hn
  -- `n = 0`: `ω₀ = μHE[0]{0} = μH[0]{0} = 1` and `μHE[0] = μH[0]`.
  · have h1 : volume (Metric.ball (0 : Rn 0) 1) = 1 := by
      have hb : Metric.ball (0 : Rn 0) 1 = {0} := by
        ext x
        simp [Subsingleton.elim x 0]
      rw [hb, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
        Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]
    simp [h1]
  · have hω0 : volume (Metric.ball (0 : Rn n) 1) ≠ 0 :=
      (Metric.measure_ball_pos volume (0 : Rn n) one_pos).ne'
    have hωt : volume (Metric.ball (0 : Rn n) 1) ≠ ∞ := measure_ball_lt_top.ne
    -- `μH[n](B₁(0)) = 2ⁿ`, so the Haar scalar `cₙ` of `Lⁿ = cₙ • μH[n]` is `ωₙ / 2ⁿ`.
    have hB : μH[(n : ℝ)] (Metric.ball (0 : Rn n) 1) = 2 ^ n := by
      apply le_antisymm
      · calc μH[(n : ℝ)] (Metric.ball (0 : Rn n) 1)
            ≤ 2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹ * volume (Metric.ball (0 : Rn n) 1) :=
              hup n _
          _ = 2 ^ n := by rw [mul_assoc, ENNReal.inv_mul_cancel hω0 hωt, mul_one]
      · calc (2 : ℝ≥0∞) ^ n
            = 2 ^ n * (volume (Metric.ball (0 : Rn n) 1))⁻¹ *
                volume (Metric.ball (0 : Rn n) 1) := by
              rw [mul_assoc, ENNReal.inv_mul_cancel hω0 hωt, mul_one]
          _ ≤ μH[(n : ℝ)] (Metric.ball (0 : Rn n) 1) := hlow n hn _
    have hF1 := Measure.isAddLeftInvariant_eq_smul (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (μH[(n : ℝ)])
    have key : volume (Metric.ball (0 : Rn n) 1) = 2 ^ n *
        (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n)))
          μH[(n : ℝ)] : ℝ≥0∞) := by
      calc volume (Metric.ball (0 : Rn n) 1)
          = (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[(n : ℝ)] •
              (μH[(n : ℝ)] : Measure (EuclideanSpace ℝ (Fin n)))) (Metric.ball (0 : Rn n) 1) := by
            rw [← hF1]
        _ = _ := by
            rw [Measure.smul_apply, hB, ENNReal.smul_def, smul_eq_mul, mul_comm]
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
      key, mul_assoc]

/-- **Density `ωₙ` on `A` gives `μ(A) ≤ 2ⁿ Hⁿ(A)`** (the step `μ_E ≤ Hⁿ ⌞ ∂*E` in Simon Ch. 3,
Theorem 4.3; parent Step 6 (D2)). Let `A ⊆ ℝᴺ` be arbitrary, `ωₙ = Lⁿ(B₁(0))`, and suppose
`μ(B̄_ρ(x)) / ρⁿ → ωₙ` as `ρ ↓ 0` for every `x ∈ A`; no finiteness of `μ` is used. Fix
`c = ωₙ + τ` with `τ > 0` and let `A_j` be the set of `x ∈ A` with `μ(B̄_ρ(x)) ≤ c ρⁿ` for all
`0 < ρ < 1/(j+1)`. Since `ωₙ < c`, the `A_j` increase to `A`. The closed-ball covering bound
gives `μ(A_j) ≤ c μH[n](A_j) ≤ c μH[n](A)`, and continuity from below (valid for arbitrary
sets) gives `μ(A) ≤ c μH[n](A)`. Letting `τ ↓ 0`, `μ(A) ≤ ωₙ μH[n](A) = 2ⁿ μHE[n](A)`. -/
theorem Submission.deGiorgiRH_measure_le_two_pow_mul_hausdorff : ∀ (n N : ℕ) (μ : Measure (Rn N)) (A : Set (Rn N)), (∀ x ∈ A, Tendsto (fun ρ : ℝ ↦ μ (Metric.closedBall x ρ) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : Rn n) 1)))) → μ A ≤ 2 ^ n * μHE[n] A := by
  intro n N μ A hdens
  have hω0 : volume (Metric.ball (0 : Rn n) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume (0 : Rn n) one_pos).ne'
  have hωt : volume (Metric.ball (0 : Rn n) 1) ≠ ∞ := measure_ball_lt_top.ne
  -- Steps 1–4: `μ(A) ≤ (ωₙ + τ) μH[n](A)` for every `τ > 0`.
  have hτ : ∀ τ : ℝ, 0 < τ →
      μ A ≤ (volume (Metric.ball (0 : Rn n) 1) + ENNReal.ofReal τ) * μH[(n : ℝ)] A := by
    intro τ hτ
    set c : ℝ≥0∞ := volume (Metric.ball (0 : Rn n) 1) + ENNReal.ofReal τ
    have hωc : volume (Metric.ball (0 : Rn n) 1) < c :=
      ENNReal.lt_add_right hωt (ENNReal.ofReal_pos.mpr hτ).ne'
    have hc0 : c ≠ 0 := (zero_le.trans_lt hωc).ne'
    have hct : c ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hωt, ENNReal.ofReal_ne_top⟩
    -- Step 1: `A_j` is the set of `x ∈ A` with `μ(B̄_ρ(x)) ≤ c ρⁿ` for all `0 < ρ < 1/(j+1)`.
    let Aj : ℕ → Set (Rn N) := fun j => {x | x ∈ A ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 / ((j : ℝ) + 1) →
      μ (Metric.closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ n)}
    have hmono : Monotone Aj := by
      intro j k hjk x hx
      refine ⟨hx.1, fun ρ hρ0 hρ => hx.2 ρ hρ0 (hρ.trans_le ?_)⟩
      gcongr
    -- Since `ωₙ < c`, the density hypothesis puts every `x ∈ A` into some `A_j`.
    have hunion : A = ⋃ j, Aj j := by
      refine Subset.antisymm (fun x hx => ?_) (iUnion_subset fun j x hx => hx.1)
      obtain ⟨ε, hε, hεsub⟩ :=
        mem_nhdsGT_iff_exists_Ioo_subset.mp ((hdens x hx).eventually (gt_mem_nhds hωc))
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (mem_Ioi.mp hε)
      refine mem_iUnion.mpr ⟨j, hx, fun ρ hρ0 hρ => ?_⟩
      have hlt : μ (Metric.closedBall x ρ) / ENNReal.ofReal (ρ ^ n) < c :=
        hεsub ⟨hρ0, hρ.trans hj⟩
      exact (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr (pow_pos hρ0 n)).ne'
        ENNReal.ofReal_ne_top).mp hlt.le
    -- Steps 2–3: the closed-ball covering bound on each `A_j`, then monotonicity of `μH[n]`.
    have hAj : ∀ j, μ (Aj j) ≤ c * μH[(n : ℝ)] A := fun j =>
      (Submission.deGiorgiRH_measure_le_mul_hausdorffMeasure_of_closedBall_le n N μ (Aj j) c
        (1 / ((j : ℝ) + 1)) hc0 hct Nat.one_div_pos_of_nat fun x hx => hx.2).trans
        (by gcongr; exact fun x hx => hx.1)
    -- Step 4: continuity from below along `A_j ↑ A` (arbitrary sets).
    calc μ A = μ (⋃ j, Aj j) := by rw [← hunion]
      _ = ⨆ j, μ (Aj j) := hmono.measure_iUnion
      _ ≤ c * μH[(n : ℝ)] A := iSup_le hAj
  -- Step 5: let `τ ↓ 0`, then use `ωₙ μH[n] = 2ⁿ μHE[n]`.
  have hlim : Tendsto (fun τ : ℝ => (volume (Metric.ball (0 : Rn n) 1) + ENNReal.ofReal τ) *
      μH[(n : ℝ)] A) (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : Rn n) 1) * μH[(n : ℝ)] A)) := by
    have h : Tendsto (fun τ : ℝ => volume (Metric.ball (0 : Rn n) 1) + ENNReal.ofReal τ) (𝓝 0)
        (𝓝 (volume (Metric.ball (0 : Rn n) 1) + ENNReal.ofReal 0)) :=
      (continuous_const.add ENNReal.continuous_ofReal).tendsto 0
    rw [ENNReal.ofReal_zero, add_zero] at h
    exact ENNReal.Tendsto.mul_const (h.mono_left nhdsWithin_le_nhds) (Or.inl hω0)
  calc μ A ≤ volume (Metric.ball (0 : Rn n) 1) * μH[(n : ℝ)] A :=
        ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun τ hτ' => hτ τ hτ')
    _ = 2 ^ n * μHE[n] A :=
        Submission.deGiorgiRH_unitBall_mul_hausdorffMeasure_eq_two_pow_mul n N A

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
