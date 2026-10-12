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

/-- **The exceptional set of the cone trichotomy is Borel** (used in the proof of Simon Ch. 3,
Theorem 3.6; Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Ch. 18). Let
`A ⊆ ℝ^{n+ℓ}` be compact with `Hⁿ(A) < ∞`, `δ > 0`, `X` a finite-dimensional normed space,
`α : X → ℝ^{n+ℓ}` continuous and `F₁, F₂ : X → ℝ^{n+ℓ} → ℝ^{n+ℓ}` jointly continuous. With the
cones `C(ξ, r, s) = {x : |F₁ ξ (x - αξ)| < s |F₂ ξ (x - αξ)|} ∩ B(αξ, r)` and
`m(ξ, r, s) = Hⁿ(A ∩ C(ξ, r, s))`, the set of `ξ` with `αξ ∈ A` at which none of
`(Φ0)` `m(ξ, r, s) ≤ c (rs)ⁿ` (every `c > 0`, small `s`, all `r < δ`), `(Φ∞)` `K (rs)ⁿ ≤ m(ξ, r, s)`
(every `K`, arbitrarily small `s`, some `r < δ`) and `(Ax)` `F₁ ξ (b - αξ) = 0` (some `b ∈ A`,
`0 < |b - αξ| < δ`) holds is measurable. For fixed `r, s`, `ξ ↦ m(ξ, r, s)` is measurable by
Tonelli (the cones are the sections of an open subset of `X × ℝ^{n+ℓ}` and `Hⁿ ⌞ A` is finite);
`m` is monotone in `(r, s)` and continuous from below along rationals, so `{Φ0}` and `{Φ∞}` are
countable Boolean combinations of sublevel and superlevel sets of these functions; `{Ax}` is
`F_σ` because the projection `X × A → X` is closed; and `α⁻¹(A)` is closed. -/
theorem Submission.bf_coneExceptional_measurableSet : ∀ (n ℓ : ℕ) {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] (A : Set (Rn (n + ℓ))), IsCompact A → μHE[n] A < ∞ → ∀ δ : ℝ, 0 < δ → ∀ (α : X → Rn (n + ℓ)) (F₁ F₂ : X → Rn (n + ℓ) → Rn (n + ℓ)), Continuous α → Continuous (fun q : X × Rn (n + ℓ) ↦ F₁ q.1 q.2) → Continuous (fun q : X × Rn (n + ℓ) ↦ F₂ q.1 q.2) → MeasurableSet {ξ : X | α ξ ∈ A ∧ ¬ ((∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ, 0 < r → r < δ → μHE[n] (A ∩ ({x | ‖F₁ ξ (x - α ξ)‖ < s * ‖F₂ ξ (x - α ξ)‖} ∩ Metric.ball (α ξ) r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) ∨ (∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μHE[n] (A ∩ ({x | ‖F₁ ξ (x - α ξ)‖ < s * ‖F₂ ξ (x - α ξ)‖} ∩ Metric.ball (α ξ) r))) ∨ ∃ b ∈ A, b ≠ (α ξ) ∧ dist b (α ξ) < δ ∧ F₁ ξ (b - α ξ) = 0)} := by
  intro n ℓ X _ _ _ _ _ A hA hAfin δ _hδ α F₁ F₂ hα hF₁ hF₂
  -- Step 1: the cone mass `m ξ r s = Hⁿ(A ∩ C(ξ, r, s))`.
  let m : X → ℝ → ℝ → ℝ≥0∞ := fun ξ r s ↦
    μHE[n] (A ∩ ({x | ‖F₁ ξ (x - α ξ)‖ < s * ‖F₂ ξ (x - α ξ)‖} ∩ Metric.ball (α ξ) r))
  -- Step 2: for fixed `r, s`, `ξ ↦ m ξ r s` is measurable: `C(ξ, r, s)` is the `ξ`-section of an
  -- open set `U ⊆ X × ℝ^{n+ℓ}` and `Hⁿ ⌞ A` is a finite measure (Tonelli).
  have hm : ∀ r s : ℝ, Measurable (fun ξ ↦ m ξ r s) := by
    intro r s
    have : IsFiniteMeasure ((μHE[n] : Measure (Rn (n + ℓ))).restrict A) :=
      isFiniteMeasure_restrict.mpr hAfin.ne
    let U : Set (X × Rn (n + ℓ)) := {q | ‖F₁ q.1 (q.2 - α q.1)‖ < s * ‖F₂ q.1 (q.2 - α q.1)‖ ∧
      q.2 ∈ Metric.ball (α q.1) r}
    have hg : Continuous (fun q : X × Rn (n + ℓ) ↦ (q.1, q.2 - α q.1)) :=
      continuous_fst.prodMk (continuous_snd.sub (hα.comp continuous_fst))
    have hU : IsOpen U :=
      (isOpen_lt (hF₁.comp hg).norm (continuous_const.mul (hF₂.comp hg).norm)).inter
        (isOpen_lt (continuous_snd.dist (hα.comp continuous_fst)) continuous_const)
    convert measurable_measure_prodMk_left
      (ν := (μHE[n] : Measure (Rn (n + ℓ))).restrict A) hU.measurableSet using 1
    funext ξ
    rw [Measure.restrict_apply' hA.measurableSet, inter_comm]
    rfl
  -- Step 3: `C(ξ, r, s)` is monotone in `(r, s)` and is the directed union of the cones with
  -- rational `0 < r' < r`, `0 < s' < s` (since `‖F₂‖ > 0` on it); by continuity from below, every
  -- `t < m ξ r s` is exceeded by some `m ξ r' s'` with such rationals `r', s'`.
  have happrox : ∀ (ξ : X) (r s : ℝ) (t : ℝ≥0∞), t < m ξ r s →
      ∃ r' s' : ℚ, 0 < r' ∧ (r' : ℝ) < r ∧ 0 < s' ∧ (s' : ℝ) < s ∧ t < m ξ r' s' := by
    intro ξ r s t ht
    let C : ℝ → ℝ → Set (Rn (n + ℓ)) := fun r s ↦
      A ∩ ({x | ‖F₁ ξ (x - α ξ)‖ < s * ‖F₂ ξ (x - α ξ)‖} ∩ Metric.ball (α ξ) r)
    have hmono : ∀ r₁ r₂ s₁ s₂ : ℝ, r₁ ≤ r₂ → s₁ ≤ s₂ → C r₁ s₁ ⊆ C r₂ s₂ := by
      rintro r₁ r₂ s₁ s₂ hr hs x ⟨hxA, hx1, hx2⟩
      exact ⟨hxA, lt_of_lt_of_le hx1 (mul_le_mul_of_nonneg_right hs (norm_nonneg _)),
        Metric.ball_subset_ball hr hx2⟩
    let I := {q : ℚ × ℚ // 0 < q.1 ∧ (q.1 : ℝ) < r ∧ 0 < q.2 ∧ (q.2 : ℝ) < s}
    have hU : C r s = ⋃ q : I, C q.1.1 q.1.2 := by
      refine Subset.antisymm (fun x hx ↦ ?_)
        (iUnion_subset fun q ↦ hmono _ _ _ _ q.2.2.1.le q.2.2.2.2.le)
      obtain ⟨hxA, hx1, hx2⟩ := hx
      have hx1' : ‖F₁ ξ (x - α ξ)‖ < s * ‖F₂ ξ (x - α ξ)‖ := hx1
      have hv : 0 < ‖F₂ ξ (x - α ξ)‖ := by
        by_contra h
        rw [le_antisymm (not_lt.mp h) (norm_nonneg _), mul_zero] at hx1'
        exact (norm_nonneg _).not_gt hx1'
      obtain ⟨s', hs'1, hs'2⟩ := exists_rat_btwn ((div_lt_iff₀ hv).mpr hx1')
      obtain ⟨r', hr'1, hr'2⟩ := exists_rat_btwn (Metric.mem_ball.mp hx2)
      have hs'pos : (0 : ℝ) < s' := lt_of_le_of_lt (by positivity) hs'1
      have hr'pos : (0 : ℝ) < r' := lt_of_le_of_lt dist_nonneg hr'1
      exact mem_iUnion.mpr ⟨⟨(r', s'), Rat.cast_pos.mp hr'pos, hr'2, Rat.cast_pos.mp hs'pos, hs'2⟩,
        hxA, (div_lt_iff₀ hv).mp hs'1, Metric.mem_ball.mpr hr'1⟩
    have hdir : Directed (· ⊆ ·) fun q : I ↦ C q.1.1 q.1.2 := by
      intro q₁ q₂
      refine ⟨⟨(max q₁.1.1 q₂.1.1, max q₁.1.2 q₂.1.2), lt_max_of_lt_left q₁.2.1, ?_,
        lt_max_of_lt_left q₁.2.2.2.1, ?_⟩, hmono _ _ _ _ ?_ ?_, hmono _ _ _ _ ?_ ?_⟩
      · rw [Rat.cast_max]
        exact max_lt q₁.2.2.1 q₂.2.2.1
      · rw [Rat.cast_max]
        exact max_lt q₁.2.2.2.2 q₂.2.2.2.2
      all_goals simp
    have ht' : t < μHE[n] (⋃ q : I, C q.1.1 q.1.2) := by
      rw [← hU]
      exact ht
    rw [hdir.measure_iUnion] at ht'
    obtain ⟨q, hq⟩ := lt_iSup_iff.mp ht'
    exact ⟨q.1.1, q.1.2, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2, hq⟩
  -- Step 4: `{Φ0}` is the countable combination
  -- `⋂_{c ∈ ℚ₊} ⋃_{ε ∈ ℚ₊} ⋂_{s ∈ ℚ ∩ (0, ε)} ⋂_{r ∈ ℚ ∩ (0, δ)} {m(·, r, s) ≤ c (rs)ⁿ}`.
  have h0 : MeasurableSet {ξ : X | ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
      ∀ r : ℝ, 0 < r → r < δ → m ξ r s ≤ ENNReal.ofReal (c * (r * s) ^ n)} := by
    have heq : {ξ : X | ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ,
        0 < r → r < δ → m ξ r s ≤ ENNReal.ofReal (c * (r * s) ^ n)} =
        ⋂ (c : ℚ) (_ : 0 < c), ⋃ (ε : ℚ) (_ : 0 < ε), ⋂ (s : ℚ) (_ : 0 < s) (_ : (s : ℝ) < ε),
          ⋂ (r : ℚ) (_ : 0 < r) (_ : (r : ℝ) < δ),
            {ξ | m ξ r s ≤ ENNReal.ofReal ((c : ℝ) * ((r : ℝ) * (s : ℝ)) ^ n)} := by
      ext ξ
      simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
      constructor
      · intro h c hc
        obtain ⟨ε, hε, hb⟩ := h c (Rat.cast_pos.mpr hc)
        obtain ⟨ε', hε'1, hε'2⟩ := exists_rat_btwn hε
        exact ⟨ε', Rat.cast_pos.mp hε'1, fun s hs hsε r hr hrδ ↦
          hb s (Rat.cast_pos.mpr hs) (hsε.trans hε'2) r (Rat.cast_pos.mpr hr) hrδ⟩
      · intro h c hc
        obtain ⟨c', hc'1, hc'2⟩ := exists_rat_btwn hc
        obtain ⟨ε, hε, hb⟩ := h c' (Rat.cast_pos.mp hc'1)
        refine ⟨ε, Rat.cast_pos.mpr hε, fun s hs hsε r hr hrδ ↦ ?_⟩
        by_contra hcon
        obtain ⟨r', s', hr', hr'r, hs', hs's, hlt⟩ := happrox ξ r s _ (not_le.mp hcon)
        have hr'0 : (0 : ℝ) < r' := Rat.cast_pos.mpr hr'
        have hs'0 : (0 : ℝ) < s' := Rat.cast_pos.mpr hs'
        have hle : ENNReal.ofReal ((c' : ℝ) * ((r' : ℝ) * (s' : ℝ)) ^ n) ≤
            ENNReal.ofReal (c * (r * s) ^ n) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul hc'2.le (pow_le_pow_left₀ (by positivity)
            (mul_le_mul hr'r.le hs's.le hs'0.le hr.le) n) (by positivity) hc.le)
        exact (hlt.trans_le ((hb s' hs' (hs's.trans hsε) r' hr' (hr'r.trans hrδ)).trans hle)).false
    rw [heq]
    refine MeasurableSet.iInter fun c ↦ MeasurableSet.iInter fun _ ↦ MeasurableSet.iUnion fun ε ↦
      MeasurableSet.iUnion fun _ ↦ MeasurableSet.iInter fun s ↦ MeasurableSet.iInter fun _ ↦
        MeasurableSet.iInter fun _ ↦ MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun _ ↦
          MeasurableSet.iInter fun _ ↦ measurableSet_le (hm r s) measurable_const
  -- Step 5: `{Φ∞}` is the countable combination
  -- `⋂_{K ∈ ℕ} ⋂_{ε ∈ ℚ₊} ⋃_{s ∈ ℚ ∩ (0, ε)} ⋃_{r ∈ ℚ ∩ (0, δ)} {K (rs)ⁿ < m(·, r, s)}`.
  have hinf : MeasurableSet {ξ : X | ∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ,
      0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ m ξ r s} := by
    have heq : {ξ : X | ∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧
        r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ m ξ r s} =
        ⋂ (K : ℕ) (ε : ℚ) (_ : 0 < ε), ⋃ (s : ℚ) (_ : 0 < s) (_ : (s : ℝ) < ε),
          ⋃ (r : ℚ) (_ : 0 < r) (_ : (r : ℝ) < δ),
            {ξ | ENNReal.ofReal ((K : ℝ) * ((r : ℝ) * (s : ℝ)) ^ n) < m ξ r s} := by
      ext ξ
      simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
      constructor
      · intro h K ε hε
        obtain ⟨s, hs, hsε, r, hr, hrδ, hle⟩ := h ((K : ℝ) + 1) ε (Rat.cast_pos.mpr hε)
        have hrs : 0 < (r * s) ^ n := pow_pos (mul_pos hr hs) n
        have hlt : ENNReal.ofReal ((K : ℝ) * (r * s) ^ n) < m ξ r s := by
          refine lt_of_lt_of_le ?_ hle
          rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
          linarith
        obtain ⟨r', s', hr', hr'r, hs', hs's, hlt'⟩ := happrox ξ r s _ hlt
        have hr'0 : (0 : ℝ) < r' := Rat.cast_pos.mpr hr'
        have hs'0 : (0 : ℝ) < s' := Rat.cast_pos.mpr hs'
        refine ⟨s', hs', hs's.trans hsε, r', hr', hr'r.trans hrδ, lt_of_le_of_lt ?_ hlt'⟩
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (by positivity) (mul_le_mul hr'r.le hs's.le hs'0.le hr.le) n) (Nat.cast_nonneg K))
      · intro h K ε hε
        obtain ⟨K', hK'⟩ := exists_nat_ge K
        obtain ⟨ε', hε'1, hε'2⟩ := exists_rat_btwn hε
        obtain ⟨s, hs, hsε, r, hr, hrδ, hlt⟩ := h K' ε' (Rat.cast_pos.mp hε'1)
        have hr0 : (0 : ℝ) < r := Rat.cast_pos.mpr hr
        have hs0 : (0 : ℝ) < s := Rat.cast_pos.mpr hs
        refine ⟨s, hs0, hsε.trans hε'2, r, hr0, hrδ, (lt_of_le_of_lt ?_ hlt).le⟩
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK' (by positivity))
    rw [heq]
    refine MeasurableSet.iInter fun K ↦ MeasurableSet.iInter fun ε ↦ MeasurableSet.iInter fun _ ↦
      MeasurableSet.iUnion fun s ↦ MeasurableSet.iUnion fun _ ↦ MeasurableSet.iUnion fun _ ↦
        MeasurableSet.iUnion fun r ↦ MeasurableSet.iUnion fun _ ↦ MeasurableSet.iUnion fun _ ↦
          measurableSet_lt measurable_const (hm r s)
  -- Step 6: the axis set is `⋃_j fst '' C_j`, where
  -- `C_j = {(ξ, b) ∈ X × A : 1/(j+1) ≤ |b - αξ| ≤ δ - 1/(j+1), F₁ ξ (b - αξ) = 0}` is closed and
  -- the projection `X × A → X` is a closed map since `A` is compact; so it is `F_σ`.
  have hax : MeasurableSet {ξ : X | ∃ b ∈ A, b ≠ α ξ ∧ dist b (α ξ) < δ ∧ F₁ ξ (b - α ξ) = 0} := by
    have : CompactSpace A := isCompact_iff_compactSpace.mp hA
    let C : ℕ → Set (X × A) := fun j ↦ {q | 1 / ((j : ℝ) + 1) ≤ dist (q.2 : Rn (n + ℓ)) (α q.1) ∧
      dist (q.2 : Rn (n + ℓ)) (α q.1) ≤ δ - 1 / ((j : ℝ) + 1) ∧
        F₁ q.1 ((q.2 : Rn (n + ℓ)) - α q.1) = 0}
    have hc1 : Continuous (fun q : X × A ↦ dist (q.2 : Rn (n + ℓ)) (α q.1)) :=
      (continuous_subtype_val.comp continuous_snd).dist (hα.comp continuous_fst)
    have hc2 : Continuous (fun q : X × A ↦ F₁ q.1 ((q.2 : Rn (n + ℓ)) - α q.1)) :=
      hF₁.comp (continuous_fst.prodMk
        ((continuous_subtype_val.comp continuous_snd).sub (hα.comp continuous_fst)))
    have hC : ∀ j, IsClosed (C j) := fun j ↦
      (isClosed_le continuous_const hc1).inter
        ((isClosed_le hc1 continuous_const).inter (isClosed_eq hc2 continuous_const))
    have heq : {ξ : X | ∃ b ∈ A, b ≠ α ξ ∧ dist b (α ξ) < δ ∧ F₁ ξ (b - α ξ) = 0} =
        ⋃ j, Prod.fst '' C j := by
      ext ξ
      simp only [mem_ofPred_eq, mem_iUnion, mem_image]
      constructor
      · rintro ⟨b, hbA, hne, hlt, h0⟩
        obtain ⟨j, hj⟩ := exists_nat_one_div_lt (lt_min (dist_pos.mpr hne) (sub_pos.mpr hlt))
        refine ⟨j, (ξ, ⟨b, hbA⟩), ⟨(hj.trans_le (min_le_left _ _)).le, ?_, h0⟩, rfl⟩
        have := hj.trans_le (min_le_right _ _)
        simp only at this ⊢
        linarith
      · rintro ⟨j, ⟨ξ', b⟩, ⟨h1, h2, h3⟩, rfl⟩
        have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
        refine ⟨b, b.2, fun h ↦ ?_, ?_, h3⟩
        · simp only [h, dist_self] at h1
          linarith
        · simp only at h2
          linarith
    rw [heq]
    exact MeasurableSet.iUnion fun j ↦ (isClosedMap_fst_of_compactSpace _ (hC j)).measurableSet
  -- Step 7: the exceptional set is `α⁻¹(A) ∖ ({Φ0} ∪ {Φ∞} ∪ {Ax})`, and `α⁻¹(A)` is closed.
  exact (hA.isClosed.preimage hα).measurableSet.inter (h0.union (hinf.union hax)).compl
/-- **Density dichotomy** (Step 4 of the supplied proof of the sphere lemma in the
Besicovitch–Federer argument, Simon Ch. 3, Theorem 3.6; cf. Dall'Alba, Lemma 4.15 and
Theorem 4.16, and Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Ch. 18).
Let `σ` be a finite measure on `ℝᴺ` and `S ⊆ ℝᴺ` with `c₁ ρⁿ ≤ σ(B_ρ(ζ))` for `ζ ∈ S`,
`0 < ρ ≤ 2`, and `σ(B_ρ(ζ)) ≤ C₁ ρⁿ` for `ζ ∈ S`, `ρ > 0`. Let `m` be an outer measure and
`F ⊆ S` a Borel set with `m(F) = 0`. Then for `σ`-a.e. `θ ∈ F` either (α) `m(S ∩ B_t(θ)) = o(tⁿ)`
or (β) `m(S ∩ B_t(θ)) / tⁿ` is unbounded as `t ↓ 0`. By inner regularity `F` may be taken
closed. Then `Fⱼ = {θ ∈ F : m(S ∩ B_t(θ)) ≤ (j+1) tⁿ for 0 < t < 1/(j+1)}` is closed and
`m`-null, and covers the points of `F` where (β) fails. A Vitali covering of
`(S ∩ B_t(θ)) ∖ Fⱼ` by balls of radius `dist(·, Fⱼ)/2` and the lower bound give
`m(S ∩ B_t(θ)) ≤ ((j+1) 10ⁿ/c₁) σ(B̄_{2t}(θ) ∖ Fⱼ)`; at the `σ`-density points of `Fⱼ`
(Besicovitch) the upper bound turns this into (α). -/
theorem Submission.bf_sphereGood_densityDichotomy : ∀ (N n : ℕ) (σ : Measure (Rn N)), IsFiniteMeasure σ → ∀ (S : Set (Rn N)) (c₁ C₁ : ℝ), 0 < c₁ → (∀ ζ ∈ S, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 2 → ENNReal.ofReal (c₁ * ρ ^ n) ≤ σ (Metric.ball ζ ρ)) → (∀ ζ ∈ S, ∀ ρ : ℝ, 0 < ρ → σ (Metric.ball ζ ρ) ≤ ENNReal.ofReal (C₁ * ρ ^ n)) → ∀ (m : OuterMeasure (Rn N)) (F : Set (Rn N)), MeasurableSet F → F ⊆ S → m F = 0 → σ {θ | θ ∈ F ∧ ¬ (∀ c : ℝ, 0 < c → ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t → t < η → m (S ∩ Metric.ball θ t) ≤ ENNReal.ofReal (c * t ^ n)) ∧ ¬ (∀ K : ℝ, ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ t < η ∧ ENNReal.ofReal (K * t ^ n) < m (S ∩ Metric.ball θ t))} = 0 := by
  intro N n σ hσ S c₁ C₁ hc₁ hL hU m F hFm hFS hmF
  -- Step 3 (covering estimate): if `G` is closed and `m`-null and `m(S ∩ B_t(φ)) ≤ L tⁿ` for
  -- `φ ∈ G`, `0 < t < λ`, then `m(S ∩ B_t(θ)) ≤ (L 10ⁿ/c₁) σ(B̄_{2t}(θ) ∖ G)` for `θ ∈ G`,
  -- `0 < t ≤ 1` and `10 t < λ`.
  have hcover : ∀ G : Set (Rn N), IsClosed G → m G = 0 → ∀ L lam : ℝ, 0 ≤ L →
      (∀ φ ∈ G, ∀ t : ℝ, 0 < t → t < lam →
        m (S ∩ Metric.ball φ t) ≤ ENNReal.ofReal (L * t ^ n)) →
      ∀ θ ∈ G, ∀ t : ℝ, 0 < t → 10 * t < lam → t ≤ 1 →
        m (S ∩ Metric.ball θ t) ≤
          ENNReal.ofReal (L * 10 ^ n / c₁) * σ (Metric.closedBall θ (2 * t) \ G) := by
    intro G hG hmG L lam hL0 hGdef θ hθ t ht htlam ht1
    -- `R = (S ∩ B_t(θ)) ∖ G` carries all of the `m`-mass, as `m(G) = 0`.
    set R : Set (Rn N) := (S ∩ Metric.ball θ t) \ G
    have hmR : m (S ∩ Metric.ball θ t) ≤ m R :=
      calc m (S ∩ Metric.ball θ t) ≤ m (R ∪ G) := by
            refine measure_mono fun x hx ↦ ?_
            by_cases hxG : x ∈ G
            · exact Or.inr hxG
            · exact Or.inl ⟨hx, hxG⟩
        _ ≤ m R + m G := measure_union_le _ _
        _ = m R := by rw [hmG, add_zero]
    refine hmR.trans ?_
    have hGne : G.Nonempty := ⟨θ, hθ⟩
    -- (a) The radii `s_ζ = dist(ζ, G)/2` satisfy `0 < s_ζ < t/2` for `ζ ∈ R`.
    set s : Rn N → ℝ := fun ζ ↦ Metric.infDist ζ G / 2 with hs
    have hinf_pos : ∀ ζ ∈ R, 0 < Metric.infDist ζ G := fun ζ hζ ↦
      (hG.notMem_iff_infDist_pos hGne).1 hζ.2
    have hs_pos : ∀ ζ ∈ R, 0 < s ζ := fun ζ hζ ↦ half_pos (hinf_pos ζ hζ)
    have hs_lt : ∀ ζ ∈ R, s ζ < t / 2 := by
      intro ζ hζ
      have h1 : Metric.infDist ζ G ≤ dist ζ θ := Metric.infDist_le_dist_of_mem hθ
      have h2 : dist ζ θ < t := hζ.1.2
      simp only [hs]
      linarith
    -- (c), (d) Vitali: a disjoint, hence countable, subfamily `u` whose 5-fold enlargements
    -- cover `R`.
    obtain ⟨u, huR, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball R
      (fun ζ ↦ ζ) s (t / 2) (fun ζ hζ ↦ (hs_lt ζ hζ).le) 5 (by norm_num)
    have hu_count : u.Countable := hudisj.countable_of_isOpen (fun ζ _ ↦ Metric.isOpen_ball)
      (fun ζ hζ ↦ ⟨ζ, Metric.mem_ball_self (hs_pos ζ (huR hζ))⟩)
    have hRcov : R ⊆ ⋃ ζ ∈ u, S ∩ Metric.ball ζ (5 * s ζ) := by
      intro ζ hζ
      obtain ⟨ζ', hζ'u, hsub⟩ := hucov ζ hζ
      exact mem_biUnion hζ'u ⟨hζ.1.1, hsub (Metric.mem_ball_self (hs_pos ζ hζ))⟩
    -- (e) Each enlarged ball lies in a ball of radius `10 s_ζ` about some `φ ∈ G`, and the
    -- lower bound at `ζ ∈ S` controls `s_ζⁿ` by `σ(B_{s_ζ}(ζ))`.
    have hpiece : ∀ ζ ∈ u, m (S ∩ Metric.ball ζ (5 * s ζ)) ≤
        ENNReal.ofReal (L * 10 ^ n / c₁) * σ (Metric.ball ζ (s ζ)) := by
      intro ζ hζu
      have hζR := huR hζu
      have hsζ := hs_pos ζ hζR
      have hsζt := hs_lt ζ hζR
      have hinf := hinf_pos ζ hζR
      obtain ⟨φ, hφG, hφ⟩ : ∃ φ ∈ G, dist ζ φ < 5 * s ζ := by
        refine (Metric.infDist_lt_iff hGne).1 ?_
        simp only [hs]
        linarith
      have hball : Metric.ball ζ (5 * s ζ) ⊆ Metric.ball φ (10 * s ζ) :=
        Metric.ball_subset_ball' (by linarith)
      calc m (S ∩ Metric.ball ζ (5 * s ζ)) ≤ m (S ∩ Metric.ball φ (10 * s ζ)) :=
            measure_mono (inter_subset_inter_right _ hball)
        _ ≤ ENNReal.ofReal (L * (10 * s ζ) ^ n) := hGdef φ hφG _ (by positivity) (by linarith)
        _ = ENNReal.ofReal (L * 10 ^ n / c₁) * ENNReal.ofReal (c₁ * s ζ ^ n) := by
            rw [← ENNReal.ofReal_mul (div_nonneg (mul_nonneg hL0 (by positivity)) hc₁.le)]
            congr 1
            rw [mul_pow, div_mul_eq_mul_div, eq_div_iff hc₁.ne']
            ring
        _ ≤ ENNReal.ofReal (L * 10 ^ n / c₁) * σ (Metric.ball ζ (s ζ)) := by
            gcongr
            exact hL ζ hζR.1.1 _ hsζ (by linarith)
    -- (f) Countable subadditivity of `m`, additivity of `σ` on the disjoint balls, and (b):
    -- `B_{s_ζ}(ζ) ⊆ B̄_{2t}(θ) ∖ G`.
    calc m R ≤ m (⋃ ζ ∈ u, S ∩ Metric.ball ζ (5 * s ζ)) := measure_mono hRcov
      _ ≤ ∑' ζ : u, m (S ∩ Metric.ball ζ (5 * s ζ)) := measure_biUnion_le m hu_count _
      _ ≤ ∑' ζ : u, ENNReal.ofReal (L * 10 ^ n / c₁) * σ (Metric.ball ζ (s ζ)) :=
          ENNReal.tsum_le_tsum fun ζ ↦ hpiece ζ ζ.2
      _ = ENNReal.ofReal (L * 10 ^ n / c₁) * ∑' ζ : u, σ (Metric.ball ζ (s ζ)) :=
          ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (L * 10 ^ n / c₁) * σ (⋃ ζ ∈ u, Metric.ball ζ (s ζ)) := by
          rw [measure_biUnion hu_count hudisj fun _ _ ↦ measurableSet_ball]
      _ ≤ ENNReal.ofReal (L * 10 ^ n / c₁) * σ (Metric.closedBall θ (2 * t) \ G) := by
          gcongr
          intro x hx
          simp only [mem_iUnion] at hx
          obtain ⟨ζ, hζu, hxζ⟩ := hx
          have hζR := huR hζu
          have hsζt := hs_lt ζ hζR
          have hinf := hinf_pos ζ hζR
          rw [Metric.mem_ball] at hxζ
          refine ⟨?_, fun hxG ↦ ?_⟩
          · rw [Metric.mem_closedBall]
            have : dist ζ θ < t := hζR.1.2
            linarith [dist_triangle x ζ θ]
          · have h1 : Metric.infDist ζ G ≤ dist ζ x := Metric.infDist_le_dist_of_mem hxG
            rw [dist_comm] at h1
            simp only [hs] at hxζ
            linarith
  -- Step 4: with `G`, `L`, `λ` as in Step 3 and `G ⊆ S`, (α) holds at every `θ ∈ G` where the
  -- `σ`-density `q_θ(ρ) = σ(G ∩ B̄_ρ(θ)) / σ(B̄_ρ(θ))` tends to `1` as `ρ ↓ 0`.
  have halpha : ∀ G : Set (Rn N), IsClosed G → G ⊆ S → m G = 0 → ∀ L lam : ℝ, 0 ≤ L → 0 < lam →
      (∀ φ ∈ G, ∀ t : ℝ, 0 < t → t < lam →
        m (S ∩ Metric.ball φ t) ≤ ENNReal.ofReal (L * t ^ n)) →
      ∀ θ ∈ G, Tendsto (fun r ↦ σ (G ∩ Metric.closedBall θ r) / σ (Metric.closedBall θ r))
          (𝓝[>] 0) (𝓝 1) →
        ∀ c : ℝ, 0 < c → ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t → t < η →
          m (S ∩ Metric.ball θ t) ≤ ENNReal.ofReal (c * t ^ n) := by
    intro G hG hGS hmG L lam hL0 hlam hGdef θ hθ hdens c hc
    have hθS : θ ∈ S := hGS hθ
    -- 0(b) Closed balls about `θ ∈ S` have positive, finite `σ`-measure.
    have hpos : ∀ ρ : ℝ, 0 < ρ → σ (Metric.closedBall θ ρ) ≠ 0 := by
      intro ρ hρ
      have h1 : ENNReal.ofReal (c₁ * (min ρ 2) ^ n) ≤ σ (Metric.ball θ (min ρ 2)) :=
        hL θ hθS _ (lt_min hρ two_pos) (min_le_right _ _)
      have h2 : σ (Metric.ball θ (min ρ 2)) ≤ σ (Metric.closedBall θ ρ) :=
        measure_mono ((Metric.ball_subset_ball (min_le_left _ _)).trans
          Metric.ball_subset_closedBall)
      have h3 : 0 < ENNReal.ofReal (c₁ * (min ρ 2) ^ n) :=
        ENNReal.ofReal_pos.2 (mul_pos hc₁ (pow_pos (lt_min hρ two_pos) n))
      exact (h3.trans_le (h1.trans h2)).ne'
    have hfin : ∀ ρ : ℝ, σ (Metric.closedBall θ ρ) ≠ ∞ := fun ρ ↦ measure_ne_top σ _
    -- (a), (c) `σ(B̄_{2t}(θ) ∖ G) / σ(B̄_{2t}(θ)) = 1 - q_θ(2t) → 0` as `t ↓ 0`.
    have h2t : Tendsto (fun t : ℝ ↦ 2 * t) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun t : ℝ ↦ 2 * t) (𝓝 0) (𝓝 (2 * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_pos two_pos (show (0 : ℝ) < t from ht)
    have hq := hdens.comp h2t
    have hf : Tendsto (fun t : ℝ ↦ σ (Metric.closedBall θ (2 * t) \ G) /
        σ (Metric.closedBall θ (2 * t))) (𝓝[>] 0) (𝓝 0) := by
      have hsub := ENNReal.Tendsto.sub tendsto_const_nhds hq (Or.inl ENNReal.one_ne_top)
      rw [tsub_self] at hsub
      refine hsub.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      simp only [Function.comp_apply]
      have hρ : 0 < 2 * t := mul_pos two_pos ht
      have hadd := measure_inter_add_sdiff (μ := σ) (Metric.closedBall θ (2 * t)) hG.measurableSet
      have hdiff : σ (Metric.closedBall θ (2 * t) \ G) =
          σ (Metric.closedBall θ (2 * t)) - σ (Metric.closedBall θ (2 * t) ∩ G) :=
        ENNReal.eq_sub_of_add_eq (measure_ne_top σ _) (by rw [add_comm]; exact hadd)
      rw [hdiff, ENNReal.sub_div (fun _ _ ↦ hpos _ hρ), ENNReal.div_self (hpos _ hρ) (hfin _),
        inter_comm]
    -- (b) With `M = (L 10ⁿ/c₁) C₁ 4ⁿ`, Step 3 and the upper bound at radius `4t` give
    -- `m(S ∩ B_t(θ)) ≤ tⁿ · M · σ(B̄_{2t}(θ) ∖ G) / σ(B̄_{2t}(θ))`; choose `η` from (c).
    obtain ⟨M, hM⟩ : ∃ M : ℝ≥0∞,
        M = ENNReal.ofReal (L * 10 ^ n / c₁) * ENNReal.ofReal (C₁ * 4 ^ n) := ⟨_, rfl⟩
    have hMf : M ≠ ∞ := by
      rw [hM]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hMf' : Tendsto (fun t : ℝ ↦ M * (σ (Metric.closedBall θ (2 * t) \ G) /
        σ (Metric.closedBall θ (2 * t)))) (𝓝[>] 0) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hf (Or.inr hMf)
      rwa [mul_zero] at this
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), M * (σ (Metric.closedBall θ (2 * t) \ G) /
        σ (Metric.closedBall θ (2 * t))) < ENNReal.ofReal c :=
      hMf'.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hc))
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    refine ⟨min u (min (lam / 10) 1), lt_min hu (lt_min (by positivity) one_pos),
      fun t ht htη ↦ ?_⟩
    have htu : t < u := htη.trans_le (min_le_left _ _)
    have htlam : 10 * t < lam := by
      have := htη.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      linarith
    have ht1 : t ≤ 1 := (htη.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
    have hρ : 0 < 2 * t := mul_pos two_pos ht
    have hlt : M * (σ (Metric.closedBall θ (2 * t) \ G) / σ (Metric.closedBall θ (2 * t))) <
        ENNReal.ofReal c := hsub ⟨ht, htu⟩
    have hball : σ (Metric.closedBall θ (2 * t)) ≤
        ENNReal.ofReal (C₁ * 4 ^ n) * ENNReal.ofReal (t ^ n) := by
      calc σ (Metric.closedBall θ (2 * t)) ≤ σ (Metric.ball θ (4 * t)) :=
            measure_mono (Metric.closedBall_subset_ball (by linarith))
        _ ≤ ENNReal.ofReal (C₁ * (4 * t) ^ n) := hU θ hθS _ (by positivity)
        _ = ENNReal.ofReal (C₁ * 4 ^ n) * ENNReal.ofReal (t ^ n) := by
            rw [mul_pow, ← mul_assoc, ENNReal.ofReal_mul' (by positivity)]
    calc m (S ∩ Metric.ball θ t)
        ≤ ENNReal.ofReal (L * 10 ^ n / c₁) * σ (Metric.closedBall θ (2 * t) \ G) :=
          hcover G hG hmG L lam hL0 hGdef θ hθ t ht htlam ht1
      _ = ENNReal.ofReal (L * 10 ^ n / c₁) * (σ (Metric.closedBall θ (2 * t)) *
            (σ (Metric.closedBall θ (2 * t) \ G) / σ (Metric.closedBall θ (2 * t)))) := by
          rw [ENNReal.mul_div_cancel (hpos _ hρ) (hfin _)]
      _ ≤ ENNReal.ofReal (L * 10 ^ n / c₁) * ((ENNReal.ofReal (C₁ * 4 ^ n) *
            ENNReal.ofReal (t ^ n)) * (σ (Metric.closedBall θ (2 * t) \ G) /
              σ (Metric.closedBall θ (2 * t)))) := by
          gcongr
      _ = ENNReal.ofReal (t ^ n) * (M * (σ (Metric.closedBall θ (2 * t) \ G) /
            σ (Metric.closedBall θ (2 * t)))) := by
          rw [hM]
          ring
      _ ≤ ENNReal.ofReal (t ^ n) * ENNReal.ofReal c := mul_le_mul' le_rfl hlt.le
      _ = ENNReal.ofReal (c * t ^ n) := by
          rw [ENNReal.ofReal_mul' (pow_nonneg ht.le n), mul_comm]
  -- Steps 2 and 5: the statement for a closed `F' ⊆ S` with `m(F') = 0`.
  have hclosed : ∀ F' : Set (Rn N), IsClosed F' → F' ⊆ S → m F' = 0 →
      σ {θ | θ ∈ F' ∧ ¬ (∀ c : ℝ, 0 < c → ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t → t < η →
          m (S ∩ Metric.ball θ t) ≤ ENNReal.ofReal (c * t ^ n)) ∧
        ¬ (∀ K : ℝ, ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ t < η ∧
          ENNReal.ofReal (K * t ^ n) < m (S ∩ Metric.ball θ t))} = 0 := by
    intro F' hFc hF'S hmF'
    -- Step 2: `F'ⱼ = {θ ∈ F' : m(S ∩ B_t(θ)) ≤ (j+1) tⁿ for 0 < t < 1/(j+1)}`.
    let Fj : ℕ → Set (Rn N) := fun j ↦ {θ | θ ∈ F' ∧ ∀ t : ℝ, 0 < t → t < 1 / ((j : ℝ) + 1) →
      m (S ∩ Metric.ball θ t) ≤ ENNReal.ofReal (((j : ℝ) + 1) * t ^ n)}
    have hFjF : ∀ j, Fj j ⊆ F' := fun j θ hθ ↦ hθ.1
    -- (b) `F'ⱼ` is closed: `B_t(θ) ⊆ B_{t+τ}(θ')` for `θ' ∈ F'ⱼ` near `θ`; let `τ ↓ 0`.
    have hFjc : ∀ j, IsClosed (Fj j) := by
      intro j
      rw [← closure_subset_iff_isClosed]
      intro θ hθ
      have hθF : θ ∈ F' := hFc.closure_subset_iff.2 (hFjF j) hθ
      refine ⟨hθF, fun t ht htj ↦ ?_⟩
      have key : ∀ τ ∈ Ioo (0 : ℝ) (1 / ((j : ℝ) + 1) - t),
          m (S ∩ Metric.ball θ t) ≤ ENNReal.ofReal (((j : ℝ) + 1) * (t + τ) ^ n) := by
        rintro τ ⟨hτ, hτ'⟩
        obtain ⟨θ', hθ', hd⟩ := Metric.mem_closure_iff.1 hθ τ hτ
        calc m (S ∩ Metric.ball θ t) ≤ m (S ∩ Metric.ball θ' (t + τ)) :=
              measure_mono (inter_subset_inter_right _ (Metric.ball_subset_ball' (by linarith)))
          _ ≤ _ := hθ'.2 (t + τ) (by linarith) (by linarith)
      have hcont : Tendsto (fun τ : ℝ ↦ ENNReal.ofReal (((j : ℝ) + 1) * (t + τ) ^ n)) (𝓝[>] 0)
          (𝓝 (ENNReal.ofReal (((j : ℝ) + 1) * t ^ n))) := by
        have h : Continuous fun τ : ℝ ↦ ENNReal.ofReal (((j : ℝ) + 1) * (t + τ) ^ n) :=
          ENNReal.continuous_ofReal.comp
            (continuous_const.mul ((continuous_const.add continuous_id).pow n))
        have := h.tendsto 0
        simp only [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      exact ge_of_tendsto hcont (mem_of_superset (Ioo_mem_nhdsGT
        (by linarith : (0 : ℝ) < 1 / ((j : ℝ) + 1) - t)) fun τ hτ ↦ key τ hτ)
    -- (a) `m(F'ⱼ) ≤ m(F') = 0`.
    have hmFj : ∀ j, m (Fj j) = 0 := fun j ↦ measure_mono_null (hFjF j) hmF'
    -- (c) A point of `F'` where (β) fails lies in some `F'ⱼ`.
    have hβ : ∀ θ ∈ F', ¬ (∀ K : ℝ, ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ t < η ∧
        ENNReal.ofReal (K * t ^ n) < m (S ∩ Metric.ball θ t)) → ∃ j, θ ∈ Fj j := by
      intro θ hθ hnβ
      push Not at hnβ
      obtain ⟨K, η, hη, hK⟩ := hnβ
      obtain ⟨j, hj⟩ := exists_nat_ge (max K (1 / η))
      refine ⟨j, hθ, fun t ht htj ↦ ?_⟩
      have hjK : K ≤ (j : ℝ) + 1 := by linarith [le_max_left K (1 / η)]
      have hjη : 1 / ((j : ℝ) + 1) ≤ η := by
        rw [div_le_iff₀ (by positivity)]
        have : 1 / η ≤ j := (le_max_right _ _).trans hj
        rw [div_le_iff₀ hη] at this
        nlinarith
      calc m (S ∩ Metric.ball θ t) ≤ ENNReal.ofReal (K * t ^ n) := hK t ht (by linarith)
        _ ≤ ENNReal.ofReal (((j : ℝ) + 1) * t ^ n) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hjK (by positivity))
    -- Step 4 with the Besicovitch density theorem: (α) fails only on a `σ`-null part of `F'ⱼ`.
    have hnull : ∀ j, σ {θ | θ ∈ Fj j ∧ ¬ (∀ c : ℝ, 0 < c → ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t →
        t < η → m (S ∩ Metric.ball θ t) ≤ ENNReal.ofReal (c * t ^ n))} = 0 := by
      intro j
      have h := Besicovitch.ae_tendsto_measure_inter_div σ (Fj j)
      rw [ae_restrict_iff' (hFjc j).measurableSet, ae_iff] at h
      refine measure_mono_null ?_ h
      rintro θ ⟨hθ, hnα⟩ hall
      exact hnα (halpha (Fj j) (hFjc j) ((hFjF j).trans hF'S) (hmFj j) ((j : ℝ) + 1)
        (1 / ((j : ℝ) + 1)) (by positivity) (by positivity) (fun φ hφ ↦ hφ.2) θ hθ (hall hθ))
    -- Step 5: the exceptional set lies in `⋃ⱼ {θ ∈ F'ⱼ : (α) fails at θ}`.
    refine measure_mono_null ?_ (measure_iUnion_null hnull)
    rintro θ ⟨hθF, hnα, hnβ⟩
    obtain ⟨j, hj⟩ := hβ θ hθF hnβ
    exact mem_iUnion.2 ⟨j, hj, hnα⟩
  -- Step 1: reduction to closed sets. Inner regularity gives closed `Fₖ ⊆ F` with
  -- `σ(F ∖ Fₖ) < 1/k`, and the exceptional set lies in `(F ∖ ⋃ₖ Fₖ) ∪ ⋃ₖ Exc(Fₖ)`.
  have happrox : ∀ k : ℕ, ∃ Fk, Fk ⊆ F ∧ IsClosed Fk ∧ σ (F \ Fk) < (k : ℝ≥0∞)⁻¹ := fun k ↦
    hFm.exists_isClosed_sdiff_lt (measure_ne_top σ F) (by simp)
  choose Fk hFkF hFkc hFkσ using happrox
  have hD : σ (F \ ⋃ k, Fk k) = 0 := by
    refine le_antisymm (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun k ↦ ?_) zero_le
    exact (measure_mono (sdiff_subset_sdiff_right (subset_iUnion Fk k))).trans (hFkσ k).le
  refine measure_mono_null ?_ (measure_union_null hD (measure_iUnion_null fun k ↦
    hclosed (Fk k) (hFkc k) ((hFkF k).trans hFS) (measure_mono_null (hFkF k) hmF)))
  rintro θ ⟨hθF, hnα, hnβ⟩
  by_cases h : θ ∈ ⋃ k, Fk k
  · obtain ⟨k, hk⟩ := mem_iUnion.1 h
    exact Or.inr (mem_iUnion.2 ⟨k, hk, hnα, hnβ⟩)
  · exact Or.inl ⟨hθF, h⟩
/-- **The non-axis unit directions of a subspace form a Borel set** (Step 2 of the supplied proof
of the sphere lemma in the Besicovitch–Federer argument, Simon Ch. 3, Theorem 3.6). Let
`H ⊆ ℝᴺ` be a subspace with orthogonal projection `p_H`, `A ⊆ ℝᴺ` compact, `δ ∈ ℝ` and `a ∈ ℝᴺ`.
The unit vectors `θ ∈ H` for which no `b ∈ A` with `0 < |b - a| < δ` has
`p_H(b - a) - (p_H(b - a) · θ) θ = 0` form a Borel set: with `S(H) = H ∩ ∂B₁(0)` (compact) and
the compact sets `Kⱼ = {(θ, b) ∈ S(H) × A : 1/(j+1) ≤ |b - a| ≤ δ - 1/(j+1),
p_H(b - a) - (p_H(b - a) · θ) θ = 0}`, the set is `S(H) ∖ ⋃ⱼ π₁(Kⱼ)`, and each `π₁(Kⱼ)` is
compact, hence closed. -/
theorem Submission.bf_sphereGood_axisFree_measurableSet : ∀ (N : ℕ) (H : Submodule ℝ (Rn N)) (A : Set (Rn N)), IsCompact A → ∀ (δ : ℝ) (a : Rn N), MeasurableSet {θ : Rn N | θ ∈ H ∧ ‖θ‖ = 1 ∧ ¬ ∃ b ∈ A, b ≠ a ∧ dist b a < δ ∧ H.starProjection (b - a) - inner ℝ (H.starProjection (b - a)) θ • θ = 0} := by
  intro N H A hA δ a
  -- Step 1: the unit sphere `S(H) = H ∩ ∂B₁(0)` of `H` is compact (`H` is closed).
  let S : Set (Rn N) := (H : Set (Rn N)) ∩ Metric.sphere 0 1
  have hS : IsCompact S := (isCompact_sphere 0 1).inter_left H.closed_of_finiteDimensional
  -- Step 2: `g(θ, b) = p_H(b - a) - (p_H(b - a) · θ) θ` is continuous on `ℝᴺ × ℝᴺ`.
  let g : Rn N × Rn N → Rn N := fun p ↦
    H.starProjection (p.2 - a) - inner ℝ (H.starProjection (p.2 - a)) p.1 • p.1
  have hg : Continuous g := by
    have hp : Continuous fun p : Rn N × Rn N ↦ H.starProjection (p.2 - a) :=
      H.starProjection.continuous.comp (continuous_snd.sub continuous_const)
    exact hp.sub ((hp.inner continuous_fst).fun_smul continuous_fst)
  have hd : Continuous fun p : Rn N × Rn N ↦ dist p.2 a := continuous_snd.dist continuous_const
  -- Step 3: `Kⱼ` is a closed subset of the compact set `S(H) × A`, so `Pⱼ = π₁(Kⱼ)` is closed.
  let K : ℕ → Set (Rn N × Rn N) := fun j ↦
    S ×ˢ A ∩ {p | 1 / ((j : ℝ) + 1) ≤ dist p.2 a} ∩ {p | dist p.2 a ≤ δ - 1 / ((j : ℝ) + 1)} ∩
      {p | g p = 0}
  have hP : ∀ j, IsClosed (Prod.fst '' K j) := fun j ↦
    ((((hS.prod hA).inter_right (isClosed_le continuous_const hd)).inter_right
      (isClosed_le hd continuous_const)).inter_right
        (isClosed_eq hg continuous_const)).image continuous_fst |>.isClosed
  -- Step 5: `S(H) ∖ ⋃ⱼ Pⱼ` is Borel.
  have hmeas : MeasurableSet (S \ ⋃ j, Prod.fst '' K j) :=
    hS.isClosed.measurableSet.diff (.iUnion fun j ↦ (hP j).measurableSet)
  convert hmeas using 1
  -- Step 4: for `θ ∈ S(H)`, some `b ∈ A` with `0 < |b - a| < δ` and `g(θ, b) = 0` exists iff
  -- `θ ∈ ⋃ⱼ Pⱼ` (Archimedean choice of `j`).
  ext θ
  constructor
  · rintro ⟨hθH, hθ1, hno⟩
    refine ⟨⟨hθH, mem_sphere_zero_iff_norm.2 hθ1⟩, fun hmem ↦ hno ?_⟩
    obtain ⟨j, ⟨θ', b⟩, ⟨⟨⟨⟨-, hbA⟩, hlo⟩, hhi⟩, hg0⟩, rfl⟩ := Set.mem_iUnion.1 hmem
    have hlo' : 1 / ((j : ℝ) + 1) ≤ dist b a := hlo
    have hhi' : dist b a ≤ δ - 1 / ((j : ℝ) + 1) := hhi
    have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    refine ⟨b, hbA, fun hba ↦ ?_, by linarith, hg0⟩
    rw [hba, dist_self] at hlo'
    linarith
  · rintro ⟨hθS, hno⟩
    refine ⟨hθS.1, mem_sphere_zero_iff_norm.1 hθS.2, ?_⟩
    rintro ⟨b, hbA, hba, hbδ, hg0⟩
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (lt_min (dist_pos.2 hba) (sub_pos.2 hbδ))
    have hlo : 1 / ((j : ℝ) + 1) ≤ dist b a := (hj.trans_le (min_le_left _ _)).le
    have hhi : dist b a ≤ δ - 1 / ((j : ℝ) + 1) := by
      linarith [hj.trans_le (min_le_right _ _)]
    exact hno (Set.mem_iUnion.2 ⟨j, (θ, b), ⟨⟨⟨⟨hθS, hbA⟩, hlo⟩, hhi⟩, hg0⟩, rfl⟩)
/-- **Double-cone outer measure on directions** (Steps 1–3 of the supplied proof of the
sphere-good-directions lemma for the Besicovitch–Federer theorem, Simon Ch. 3, Theorem 3.6; cf.
Dall'Alba, Theorem 4.16). With `y_x = p_H(x - a)` and the double cone
`Λ(E') = {x : y_x ≠ 0, ±y_x/|y_x| ∈ E'}`, the outer measure
`m(E') = sup_{0<r<δ} Hⁿ(A ∩ B_r(a) ∩ Λ(E')) / rⁿ` vanishes on the unit directions of `H` whose
axis through `a` meets no `b ∈ A ∖ {a}` with `|b - a| < δ`, and its cap densities control the
slab-cone densities of `A` at `a`, since
`Z_θ(s) ⊆ Λ(S(H) ∩ B_{2s}(θ))` and `Λ(S(H) ∩ B_t(θ)) ⊆ Z_θ(t)`. -/
theorem Submission.bf_sphereGood_doubleCone_outerMeasure : ∀ (N n : ℕ) (H : Submodule ℝ (Rn N)) (A : Set (Rn N)) (δ : ℝ), 0 < δ → ∀ a : Rn N, ∃ m : OuterMeasure (Rn N), m {θ | θ ∈ H ∧ ‖θ‖ = 1 ∧ ¬ ∃ b ∈ A, b ≠ a ∧ dist b a < δ ∧ H.starProjection (b - a) - inner ℝ (H.starProjection (b - a)) θ • θ = 0} = 0 ∧ ∀ θ ∈ H, ‖θ‖ = 1 → ((∀ c : ℝ, 0 < c → ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t → t < η → m ({ζ | ζ ∈ H ∧ ‖ζ‖ = 1} ∩ Metric.ball θ t) ≤ ENNReal.ofReal (c * t ^ n)) → ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ, 0 < r → r < δ → μHE[n] (A ∩ ({x | ‖H.starProjection (x - a) - inner ℝ (H.starProjection (x - a)) θ • θ‖ < s * ‖H.starProjection (x - a)‖} ∩ Metric.ball a r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) ∧ ((∀ K : ℝ, ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ t < η ∧ ENNReal.ofReal (K * t ^ n) < m ({ζ | ζ ∈ H ∧ ‖ζ‖ = 1} ∩ Metric.ball θ t)) → ∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μHE[n] (A ∩ ({x | ‖H.starProjection (x - a) - inner ℝ (H.starProjection (x - a)) θ • θ‖ < s * ‖H.starProjection (x - a)‖} ∩ Metric.ball a r))) := by
  intro N n H A δ hδ a
  -- Step 0: `d(v, θ) = |v - (v·θ)θ|` is the distance from `v` to the line `ℝθ`.
  have perp_smul : ∀ (θ v : Rn N) (c : ℝ),
      c • v - inner ℝ (c • v) θ • θ = c • (v - inner ℝ v θ • θ) := by
    intro θ v c
    rw [real_inner_smul_left, smul_sub, smul_smul]
  have perp_neg : ∀ θ v : Rn N, -v - inner ℝ (-v) θ • θ = -(v - inner ℝ v θ • θ) := by
    intro θ v
    rw [inner_neg_left, neg_smul]
    abel
  -- `d(v, θ) ≤ |v - θ|` for a unit vector `θ`.
  have perp_le : ∀ θ v : Rn N, ‖θ‖ = 1 → ‖v - inner ℝ v θ • θ‖ ≤ ‖v - θ‖ := by
    intro θ v hθ
    have h1 : ‖v - inner ℝ v θ • θ‖ ^ 2 = ‖v‖ ^ 2 - (inner ℝ v θ) ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        hθ]
      ring
    have h2 : ‖v - θ‖ ^ 2 = ‖v‖ ^ 2 - 2 * inner ℝ v θ + 1 := by
      rw [norm_sub_sq_real, hθ]
      ring
    have h3 : ‖v - inner ℝ v θ • θ‖ ^ 2 ≤ ‖v - θ‖ ^ 2 := by
      rw [h1, h2]
      nlinarith [sq_nonneg (inner ℝ v θ - 1)]
    nlinarith [norm_nonneg (v - inner ℝ v θ • θ), norm_nonneg (v - θ)]
  -- `|ξ - θ| ≤ 2 d(ξ, θ)` for unit vectors `ξ, θ` with `ξ·θ ≥ 0`.
  have sub_le_two_perp : ∀ θ ξ : Rn N, ‖θ‖ = 1 → ‖ξ‖ = 1 → 0 ≤ inner ℝ ξ θ →
      ‖ξ - θ‖ ≤ 2 * ‖ξ - inner ℝ ξ θ • θ‖ := by
    intro θ ξ hθ hξ hpos
    have h1 : ‖ξ - inner ℝ ξ θ • θ‖ ^ 2 = 1 - (inner ℝ ξ θ) ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        hθ, hξ]
      ring
    have h2 : ‖ξ - θ‖ ^ 2 = 2 - 2 * inner ℝ ξ θ := by
      rw [norm_sub_sq_real, hθ, hξ]
      ring
    have hle : inner ℝ ξ θ ≤ 1 := by
      have := real_inner_le_norm ξ θ
      rw [hθ, hξ] at this
      linarith
    have h3 : ‖ξ - θ‖ ^ 2 ≤ (2 * ‖ξ - inner ℝ ξ θ • θ‖) ^ 2 := by
      rw [mul_pow, h1, h2]
      nlinarith [mul_nonneg (sub_nonneg.2 hle) (by linarith : (0 : ℝ) ≤ 1 + 2 * inner ℝ ξ θ)]
    nlinarith [norm_nonneg (ξ - θ), norm_nonneg (ξ - inner ℝ ξ θ • θ)]
  -- Step 1: the double cone `Λ(E')` over a set of directions `E'`, with vertex `a`.
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : Set (Rn N) → Set (Rn N), ∀ (E' : Set (Rn N)) (x : Rn N),
      x ∈ Λ E' ↔ H.starProjection (x - a) ≠ 0 ∧
        (‖H.starProjection (x - a)‖⁻¹ • H.starProjection (x - a) ∈ E' ∨
          -(‖H.starProjection (x - a)‖⁻¹ • H.starProjection (x - a)) ∈ E') :=
    ⟨fun E' ↦ {x | H.starProjection (x - a) ≠ 0 ∧
      (‖H.starProjection (x - a)‖⁻¹ • H.starProjection (x - a) ∈ E' ∨
        -(‖H.starProjection (x - a)‖⁻¹ • H.starProjection (x - a)) ∈ E')}, fun _ _ ↦ Iff.rfl⟩
  have Λ_mono : ∀ {E₁ E₂ : Set (Rn N)}, E₁ ⊆ E₂ → Λ E₁ ⊆ Λ E₂ := by
    intro E₁ E₂ h x hx
    rw [hΛ] at hx ⊢
    obtain ⟨hx0, hx | hx⟩ := hx
    · exact ⟨hx0, Or.inl (h hx)⟩
    · exact ⟨hx0, Or.inr (h hx)⟩
  have Λ_iUnion : ∀ s : ℕ → Set (Rn N), Λ (⋃ i, s i) = ⋃ i, Λ (s i) := by
    intro s
    ext x
    simp only [hΛ, mem_iUnion]
    constructor
    · rintro ⟨hx0, ⟨i, hi⟩ | ⟨i, hi⟩⟩
      · exact ⟨i, hx0, Or.inl hi⟩
      · exact ⟨i, hx0, Or.inr hi⟩
    · rintro ⟨i, hx0, hi | hi⟩
      · exact ⟨hx0, Or.inl ⟨i, hi⟩⟩
      · exact ⟨hx0, Or.inr ⟨i, hi⟩⟩
  have Λ_empty : Λ ∅ = ∅ := by
    ext x
    simp [hΛ]
  -- Step 2: the outer measure `m(E') = sup_{0<r<δ} Hⁿ(A ∩ B_r(a) ∩ Λ(E')) / rⁿ`.
  obtain ⟨m, hm⟩ : ∃ m : OuterMeasure (Rn N), ∀ E' : Set (Rn N),
      m E' = ⨆ r ∈ Set.Ioo (0 : ℝ) δ,
        μHE[n] (A ∩ Metric.ball a r ∩ Λ E') / ENNReal.ofReal (r ^ n) := by
    refine ⟨{ measureOf := fun E' ↦ ⨆ r ∈ Set.Ioo (0 : ℝ) δ,
                μHE[n] (A ∩ Metric.ball a r ∩ Λ E') / ENNReal.ofReal (r ^ n)
              empty := ?_
              mono := ?_
              iUnion_nat := ?_ }, fun _ ↦ rfl⟩
    · simp [Λ_empty]
    · intro s₁ s₂ h
      exact iSup₂_mono fun r _ ↦
        ENNReal.div_le_div_right (measure_mono (inter_subset_inter_right _ (Λ_mono h))) _
    · intro s _
      refine iSup₂_le fun r hr ↦ ?_
      rw [Λ_iUnion, inter_iUnion]
      calc μHE[n] (⋃ i, A ∩ Metric.ball a r ∩ Λ (s i)) / ENNReal.ofReal (r ^ n)
          ≤ (∑' i, μHE[n] (A ∩ Metric.ball a r ∩ Λ (s i))) / ENNReal.ofReal (r ^ n) :=
            ENNReal.div_le_div_right (measure_iUnion_le _) _
        _ = ∑' i, μHE[n] (A ∩ Metric.ball a r ∩ Λ (s i)) / ENNReal.ofReal (r ^ n) := by
            simp only [div_eq_mul_inv, ENNReal.tsum_mul_right]
        _ ≤ ∑' i, ⨆ r ∈ Set.Ioo (0 : ℝ) δ,
              μHE[n] (A ∩ Metric.ball a r ∩ Λ (s i)) / ENNReal.ofReal (r ^ n) :=
            ENNReal.tsum_le_tsum fun i ↦ le_iSup₂_of_le r hr le_rfl
  refine ⟨m, ?_, ?_⟩
  · -- Step 3: no point of `A ∩ B_r(a)` lies in the double cone over the axis-free directions.
    rw [hm]
    refine le_antisymm (iSup₂_le fun r hr ↦ ?_) zero_le
    have hnull : A ∩ Metric.ball a r ∩ Λ {θ | θ ∈ H ∧ ‖θ‖ = 1 ∧ ¬ ∃ b ∈ A, b ≠ a ∧
        dist b a < δ ∧ H.starProjection (b - a) - inner ℝ (H.starProjection (b - a)) θ • θ = 0}
        = ∅ := by
      refine eq_empty_of_forall_notMem ?_
      rintro x ⟨⟨hxA, hxr⟩, hxΛ⟩
      rw [hΛ] at hxΛ
      obtain ⟨hy0, hξ⟩ := hxΛ
      have hxa : x ≠ a := by
        intro h
        apply hy0
        rw [h, sub_self, map_zero]
      have hdist : dist x a < δ := (Metric.mem_ball.1 hxr).trans hr.2
      set y := H.starProjection (x - a) with hy
      have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy0
      have hcoef : ‖y‖⁻¹ * ‖y‖ ^ 2 * ‖y‖⁻¹ = 1 := by field_simp
      have hcol1 : y - inner ℝ y (‖y‖⁻¹ • y) • (‖y‖⁻¹ • y) = 0 := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq, smul_smul, hcoef, one_smul,
          sub_self]
      have hcol2 : y - inner ℝ y (-(‖y‖⁻¹ • y)) • (-(‖y‖⁻¹ • y)) = 0 := by
        rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq, neg_smul, smul_neg,
          neg_neg, smul_smul, hcoef, one_smul, sub_self]
      rcases hξ with hξ | hξ
      · exact hξ.2.2 ⟨x, hxA, hxa, hdist, hcol1⟩
      · exact hξ.2.2 ⟨x, hxA, hxa, hdist, hcol2⟩
    rw [hnull, measure_empty, ENNReal.zero_div]
  · intro θ hθH hθ1
    refine ⟨fun hα c hc ↦ ?_, fun hβ K ε hε ↦ ?_⟩
    · -- Step 5: small caps give small slab cones, via `Z_θ(s) ⊆ Λ(S(H) ∩ B_{2s}(θ))`.
      obtain ⟨η, hη, hηt⟩ := hα (c / 2 ^ n) (div_pos hc (by positivity))
      refine ⟨η / 2, half_pos hη, fun s hs hsε r hr hrδ ↦ ?_⟩
      have hrn : ENNReal.ofReal (r ^ n) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact pow_pos hr n
      have hsub : A ∩ ({x | ‖H.starProjection (x - a) - inner ℝ (H.starProjection (x - a)) θ • θ‖
          < s * ‖H.starProjection (x - a)‖} ∩ Metric.ball a r) ⊆
          A ∩ Metric.ball a r ∩ Λ ({ζ | ζ ∈ H ∧ ‖ζ‖ = 1} ∩ Metric.ball θ (2 * s)) := by
        rintro x ⟨hxA, hxZ, hxr⟩
        refine ⟨⟨hxA, hxr⟩, ?_⟩
        have hx' : ‖H.starProjection (x - a) - inner ℝ (H.starProjection (x - a)) θ • θ‖ <
            s * ‖H.starProjection (x - a)‖ := hxZ
        have hyH : H.starProjection (x - a) ∈ H := H.starProjection_apply_mem _
        rw [hΛ]
        set y := H.starProjection (x - a) with hy
        have hy0 : y ≠ 0 := by
          intro h0
          rw [h0] at hx'
          simp at hx'
        have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
        set w : Rn N := ‖y‖⁻¹ • y with hw
        have hwH : w ∈ H := H.smul_mem _ hyH
        have hw1 : ‖w‖ = 1 := by
          rw [hw, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hyn.ne']
        have hdw : ‖w - inner ℝ w θ • θ‖ < s := by
          rw [hw, perp_smul, norm_smul, norm_inv, norm_norm, inv_mul_lt_iff₀ hyn]
          linarith [hx', mul_comm s ‖y‖]
        refine ⟨hy0, ?_⟩
        rcases le_or_gt 0 (inner ℝ w θ) with hpos | hneg
        · left
          refine ⟨⟨hwH, hw1⟩, ?_⟩
          rw [Metric.mem_ball, dist_eq_norm]
          calc ‖w - θ‖ ≤ 2 * ‖w - inner ℝ w θ • θ‖ := sub_le_two_perp θ w hθ1 hw1 hpos
            _ < 2 * s := by linarith
        · right
          refine ⟨⟨H.neg_mem hwH, by rw [norm_neg, hw1]⟩, ?_⟩
          rw [Metric.mem_ball, dist_eq_norm]
          have hpos' : 0 ≤ inner ℝ (-w) θ := by
            rw [inner_neg_left]
            linarith
          calc ‖-w - θ‖ ≤ 2 * ‖-w - inner ℝ (-w) θ • θ‖ :=
                sub_le_two_perp θ (-w) hθ1 (by rw [norm_neg, hw1]) hpos'
            _ = 2 * ‖w - inner ℝ w θ • θ‖ := by rw [perp_neg, norm_neg]
            _ < 2 * s := by linarith
      refine (measure_mono hsub).trans ?_
      -- `Hⁿ(A ∩ B_r(a) ∩ Λ(E')) ≤ rⁿ m(E')` for `0 < r < δ`.
      have hK : μHE[n] (A ∩ Metric.ball a r ∩ Λ ({ζ | ζ ∈ H ∧ ‖ζ‖ = 1} ∩
          Metric.ball θ (2 * s))) ≤
          m ({ζ | ζ ∈ H ∧ ‖ζ‖ = 1} ∩ Metric.ball θ (2 * s)) * ENNReal.ofReal (r ^ n) := by
        rw [← ENNReal.div_le_iff hrn ENNReal.ofReal_ne_top, hm]
        exact le_iSup₂_of_le (f := fun r (_ : r ∈ Set.Ioo (0 : ℝ) δ) ↦
          μHE[n] (A ∩ Metric.ball a r ∩ Λ ({ζ | ζ ∈ H ∧ ‖ζ‖ = 1} ∩
            Metric.ball θ (2 * s))) / ENNReal.ofReal (r ^ n)) r ⟨hr, hrδ⟩ le_rfl
      refine hK.trans ?_
      calc m ({ζ | ζ ∈ H ∧ ‖ζ‖ = 1} ∩ Metric.ball θ (2 * s)) * ENNReal.ofReal (r ^ n)
          ≤ ENNReal.ofReal (c / 2 ^ n * (2 * s) ^ n) * ENNReal.ofReal (r ^ n) := by
            gcongr
            exact hηt (2 * s) (by positivity) (by linarith)
        _ = ENNReal.ofReal (c * (r * s) ^ n) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [mul_pow, mul_pow]
            field_simp
    · -- Step 6: large caps give large slab cones, via `Λ(S(H) ∩ B_t(θ)) ⊆ Z_θ(t)`.
      by_cases hK : K ≤ 0
      · refine ⟨ε / 2, half_pos hε, by linarith, δ / 2, half_pos hδ, by linarith, ?_⟩
        rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hK (by positivity))]
        exact zero_le
      · rw [not_le] at hK
        obtain ⟨t, ht, htε, hlt⟩ := hβ K ε hε
        rw [hm] at hlt
        obtain ⟨r, hr, hlt'⟩ : ∃ r ∈ Set.Ioo (0 : ℝ) δ, ENNReal.ofReal (K * t ^ n) <
            μHE[n] (A ∩ Metric.ball a r ∩ Λ ({ζ | ζ ∈ H ∧ ‖ζ‖ = 1} ∩
              Metric.ball θ t)) / ENNReal.ofReal (r ^ n) := by
          simpa only [lt_iSup_iff, exists_prop] using hlt
        have hrn : ENNReal.ofReal (r ^ n) ≠ 0 := by
          rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
          exact pow_pos hr.1 n
        refine ⟨t, ht, htε, r, hr.1, hr.2, ?_⟩
        have h2 := (ENNReal.lt_div_iff_mul_lt (Or.inl hrn) (Or.inl ENNReal.ofReal_ne_top)).1 hlt'
        rw [← ENNReal.ofReal_mul (mul_pos hK (pow_pos ht n)).le] at h2
        have hsub : A ∩ Metric.ball a r ∩ Λ ({ζ | ζ ∈ H ∧ ‖ζ‖ = 1} ∩ Metric.ball θ t) ⊆
            A ∩ ({x | ‖H.starProjection (x - a) - inner ℝ (H.starProjection (x - a)) θ • θ‖ <
              t * ‖H.starProjection (x - a)‖} ∩ Metric.ball a r) := by
          rintro x ⟨⟨hxA, hxr⟩, hxΛ⟩
          refine ⟨hxA, ?_, hxr⟩
          rw [hΛ] at hxΛ
          obtain ⟨hy0, hξ⟩ := hxΛ
          show ‖H.starProjection (x - a) - inner ℝ (H.starProjection (x - a)) θ • θ‖ <
            t * ‖H.starProjection (x - a)‖
          set y := H.starProjection (x - a) with hy
          have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
          set w : Rn N := ‖y‖⁻¹ • y with hw
          have hyw : y = ‖y‖ • w := by
            rw [hw, smul_smul, mul_inv_cancel₀ hyn.ne', one_smul]
          have key : ‖y - inner ℝ y θ • θ‖ = ‖y‖ * ‖w - inner ℝ w θ • θ‖ := by
            conv_lhs => rw [hyw]
            rw [perp_smul, norm_smul, norm_norm]
          have hdist : ‖w - inner ℝ w θ • θ‖ < t := by
            rcases hξ with ⟨_, hb⟩ | ⟨_, hb⟩
            · rw [Metric.mem_ball, dist_eq_norm] at hb
              exact (perp_le θ w hθ1).trans_lt hb
            · rw [Metric.mem_ball, dist_eq_norm] at hb
              have := (perp_le θ (-w) hθ1).trans_lt hb
              rwa [perp_neg, norm_neg] at this
          rw [key]
          calc ‖y‖ * ‖w - inner ℝ w θ • θ‖ < ‖y‖ * t := mul_lt_mul_of_pos_left hdist hyn
            _ = t * ‖y‖ := mul_comm _ _
        calc ENNReal.ofReal (K * (r * t) ^ n) = ENNReal.ofReal (K * t ^ n * r ^ n) := by
              congr 1
              ring
          _ ≤ _ := h2.le
          _ ≤ _ := measure_mono hsub
/-- **Uniform `Hⁿ`-measure of open balls in `n`-planes** (flat-ball step of the sphere-cap bounds
for the Besicovitch–Federer theorem; Dall'Alba, Lemma 4.15; Mattila, Ch. 18). For each `n` the
constant `ω = Lⁿ(B_{ℝⁿ}(0, 1)) > 0` satisfies `Hⁿ(T ∩ B(w, ρ)) = ω ρⁿ` for every `n`-dimensional
subspace `T ⊆ ℝᴺ`, every `w ∈ T` and every `ρ > 0`. An orthonormal basis of `T` gives a linear
isometric equivalence `e : T ≃ ℝⁿ`, and `ι = e⁻¹` followed by `T ↪ ℝᴺ` is an isometry with
`T ∩ B(w, ρ) = ι(B(e w, ρ))`; `Hⁿ` is invariant under isometries, equals `Lⁿ` on `ℝⁿ`, and
`Lⁿ(B(z, ρ)) = ρⁿ Lⁿ(B(0, 1))`. -/
theorem Submission.bf_planeBall_measure_uniform : ∀ n : ℕ, ∃ ω : ℝ, 0 < ω ∧ ∀ (N : ℕ) (T : Submodule ℝ (Rn N)), finrank ℝ T = n → ∀ w ∈ T, ∀ ρ : ℝ, 0 < ρ → μHE[n] ((T : Set (Rn N)) ∩ Metric.ball w ρ) = ENNReal.ofReal (ω * ρ ^ n) := by
  intro n
  -- Step 1: `ω = Lⁿ(B(0, 1))` is positive and finite, `Lⁿ` being an additive Haar measure on
  -- the proper space `ℝⁿ`; it depends only on `n`.
  have hB₀pos : 0 < volume (Metric.ball (0 : Rn n) 1) := Metric.measure_ball_pos _ _ one_pos
  have hB₀fin : volume (Metric.ball (0 : Rn n) 1) < ∞ := measure_ball_lt_top
  refine ⟨(volume (Metric.ball (0 : Rn n) 1)).toReal, ENNReal.toReal_pos hB₀pos.ne' hB₀fin.ne,
    fun N T hT w hw ρ hρ ↦ ?_⟩
  -- Step 2: an orthonormal basis of `T` indexed by `Fin n` gives a linear isometric equivalence
  -- `e : T ≃ ℝⁿ`, and `ι = (↑) ∘ e⁻¹ : ℝⁿ → ℝᴺ` is an isometry with `ι (e x) = x` on `T`.
  let e : T ≃ₗᵢ[ℝ] Rn n := ((stdOrthonormalBasis ℝ T).reindex (finCongr hT)).repr
  let ι : Rn n → Rn N := fun z ↦ (e.symm z : Rn N)
  have hι : Isometry ι := isometry_subtype_coe.comp e.symm.isometry
  have hιe : ∀ x : T, ι (e x) = x := fun x ↦ by simp [ι]
  have hιw : ι (e ⟨w, hw⟩) = w := hιe ⟨w, hw⟩
  -- Step 3: `T ∩ B(w, ρ) = ι(B(e w, ρ))`, since `ι` preserves distances.
  have himg : (T : Set (Rn N)) ∩ Metric.ball w ρ = ι '' Metric.ball (e ⟨w, hw⟩) ρ := by
    ext x
    constructor
    · rintro ⟨hxT, hx⟩
      refine ⟨e ⟨x, hxT⟩, ?_, hιe ⟨x, hxT⟩⟩
      rw [Metric.mem_ball, ← hι.dist_eq, hιe, hιw]
      exact hx
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(e.symm z).2, ?_⟩
      rw [Metric.mem_ball, ← hιw, hι.dist_eq]
      exact hz
  -- Step 4: isometry invariance of `Hⁿ`, `Hⁿ = Lⁿ` on `ℝⁿ` and the Haar scaling law for balls.
  rw [himg, hι.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
    Measure.addHaar_ball_of_pos _ _ hρ, finrank_euclideanSpace_fin,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hB₀fin.ne, mul_comm]
/-- **Projection lower comparison for caps of the unit sphere of an `(n+1)`-plane** (the graph
map over `T_ζ` and the orthogonal projection `π_ζ`; Dall'Alba, Lemma 4.15; Mattila, Ch. 18).
For a subspace `H ⊆ ℝᴺ` with `dim H = n + 1` and a unit vector `ζ ∈ H`, the `n`-plane
`T = (ℝζ)^⊥ ∩ H` satisfies `Hⁿ(T ∩ B(0, ρ/2)) ≤ Hⁿ(S(H) ∩ B(ζ, ρ))` for `0 < ρ ≤ 2`, where
`S(H) = {θ ∈ H : |θ| = 1}`. Every `w ∈ T ∩ B(0, ρ/2)` is `π ξ` for the lift
`ξ = w + (1 - |w|²)^{1/2} ζ ∈ S(H) ∩ B(ζ, ρ)`, where `π` is the `1`-Lipschitz orthogonal
projection onto `T`. -/
theorem Submission.bf_sphereCap_lower_comparison : ∀ (n N : ℕ) (H : Submodule ℝ (Rn N)), finrank ℝ H = n + 1 → ∀ ζ ∈ H, ‖ζ‖ = 1 → ∃ T : Submodule ℝ (Rn N), finrank ℝ T = n ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 2 → μHE[n] ((T : Set (Rn N)) ∩ Metric.ball 0 (ρ / 2)) ≤ μHE[n] ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ) := by
  intro n N H hH ζ hζ hζ1
  -- Step 1: the plane `T = (ℝζ)^⊥ ∩ H` has dimension `n`, since `ℝζ ⊆ H` is a line.
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ1
  have hTdim : finrank ℝ ((ℝ ∙ ζ)ᗮ ⊓ H : Submodule ℝ (Rn N)) = n :=
    Submodule.finrank_add_inf_finrank_orthogonal' ((Submodule.span_singleton_le_iff_mem ζ H).2 hζ)
      (by rw [finrank_span_singleton hζ0, hH, add_comm])
  refine ⟨(ℝ ∙ ζ)ᗮ ⊓ H, hTdim, fun ρ hρ hρ2 ↦ ?_⟩
  set T : Submodule ℝ (Rn N) := (ℝ ∙ ζ)ᗮ ⊓ H
  -- Step 2: the orthogonal projection `π` onto `T` sends `ζ` to `0`, since `ζ ⊥ T`.
  have hπζ : T.starProjection ζ = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    intro u hu
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 hu.1
  -- Step 3: every `w ∈ T ∩ B(0, ρ/2)` is `π ξ` for `ξ = w + (1 - |w|²)^{1/2} ζ` in the cap.
  have hsub : (T : Set (Rn N)) ∩ Metric.ball 0 (ρ / 2) ⊆
      T.starProjection '' ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ) := by
    rintro w ⟨hwT, hw⟩
    have hwζ : inner ℝ w ζ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.1 hwT.1
    rw [mem_ball_zero_iff] at hw
    set t : ℝ := ‖w‖ ^ 2
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t < 1 := by nlinarith [norm_nonneg w]
    have htρ : t < ρ ^ 2 / 4 := by nlinarith [norm_nonneg w]
    set f : ℝ := Real.sqrt (1 - t)
    have hf0 : 0 ≤ f := Real.sqrt_nonneg _
    have hf2 : f ^ 2 = 1 - t := Real.sq_sqrt (by linarith)
    have hf1 : f ≤ 1 := Real.sqrt_le_one.2 (by linarith)
    have hft : 1 - t ≤ f := (Real.le_sqrt (by linarith) (by linarith)).2 (by nlinarith)
    refine ⟨w + f • ζ, ⟨⟨H.add_mem hwT.2 (H.smul_mem f hζ), ?_⟩, ?_⟩, ?_⟩
    · -- (b) `|ξ|² = |w|² + f² = 1`
      have hsq : ‖w + f • ζ‖ ^ 2 = 1 := by
        rw [norm_add_sq_real, inner_smul_right, hwζ, norm_smul, hζ1, Real.norm_of_nonneg hf0]
        nlinarith
      nlinarith [norm_nonneg (w + f • ζ)]
    · -- (c) `|ξ - ζ|² = |w|² + (1 - f)² ≤ 2 |w|² < ρ²`
      rw [Metric.mem_ball, dist_eq_norm]
      have hsq : ‖w + f • ζ - ζ‖ ^ 2 = t + (1 - f) ^ 2 := by
        rw [show w + f • ζ - ζ = w + (f - 1) • ζ by rw [sub_smul, one_smul]; abel,
          norm_add_sq_real, inner_smul_right, hwζ, norm_smul, hζ1, Real.norm_eq_abs, mul_one,
          sq_abs]
        ring
      have hlt : ‖w + f • ζ - ζ‖ ^ 2 < ρ ^ 2 := by
        rw [hsq]
        nlinarith [mul_nonneg (sub_nonneg.2 hf1) (sub_nonneg.2 hft),
          mul_nonneg ht0 (sub_nonneg.2 hft), mul_nonneg ht0 (sub_nonneg.2 ht1.le)]
      exact lt_of_pow_lt_pow_left₀ 2 hρ.le hlt
    · -- (d) `π ξ = π w + f π ζ = w`
      rw [map_add, map_smul, hπζ, smul_zero, add_zero, Submodule.starProjection_eq_self_iff.2 hwT]
  -- Step 4: monotonicity and the Lipschitz image bound with constant `1`.
  calc μHE[n] ((T : Set (Rn N)) ∩ Metric.ball 0 (ρ / 2))
      ≤ μHE[n] (T.starProjection '' ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ)) :=
        measure_mono hsub
    _ ≤ ((1 : ℝ≥0) : ℝ≥0∞) ^ n * μHE[n] ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ) :=
        Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
          T.lipschitzWith_starProjection.lipschitzOnWith
    _ = μHE[n] ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ) := by simp
/-- **Graph upper comparison for small caps of the unit sphere of an `(n+1)`-plane** (a cap
estimate for Simon Ch. 3, Theorem 3.6, `chapter-03.txt` lines 530–536, whose proof Simon defers
to [Fed69]/[Ros84]; cf. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Ch. 18).
Let `H ⊆ ℝᴺ` be a subspace with `dim H = n + 1`, `S(H) = {θ ∈ H : |θ| = 1}` and `ζ ∈ S(H)`.
The `n`-plane `T = H ∩ ζ^⊥` satisfies `Hⁿ(S(H) ∩ B(ζ, ρ)) ≤ 2ⁿ Hⁿ(T ∩ B(0, ρ))` for
`0 < ρ ≤ 1/2`: the cap lies in the image of the disc `T ∩ B(0, ρ)` under the graph map
`Γ(w) = w + (1 - |w|²)^{1/2} ζ`, which is `2`-Lipschitz on that disc. -/
theorem Submission.bf_sphereCap_upper_comparison : ∀ (n N : ℕ) (H : Submodule ℝ (Rn N)), finrank ℝ H = n + 1 → ∀ ζ ∈ H, ‖ζ‖ = 1 → ∃ T : Submodule ℝ (Rn N), finrank ℝ T = n ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 → μHE[n] ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ) ≤ 2 ^ n * μHE[n] ((T : Set (Rn N)) ∩ Metric.ball 0 ρ) := by
  intro n N H hH ζ hζ hζ1
  -- The plane `T = (ℝζ)ᗮ ⊓ H` has dimension `dim H - dim ℝζ = n`.
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ1
  have hT : finrank ℝ ((ℝ ∙ ζ)ᗮ ⊓ H : Submodule ℝ (Rn N)) = n :=
    Submodule.finrank_add_inf_finrank_orthogonal' ((Submodule.span_singleton_le_iff_mem _ _).2 hζ)
      (by rw [finrank_span_singleton hζ0, hH, add_comm])
  refine ⟨(ℝ ∙ ζ)ᗮ ⊓ H, hT, fun ρ hρ hρ2 ↦ ?_⟩
  set T : Submodule ℝ (Rn N) := (ℝ ∙ ζ)ᗮ ⊓ H
  set Γ : Rn N → Rn N := fun w ↦ w + Real.sqrt (1 - ‖w‖ ^ 2) • ζ with hΓ
  -- The cap lies in `Γ(T ∩ B(0, ρ))`: `ξ = Γ(w)` for `s = ξ · ζ > 0` and `w = ξ - s ζ ∈ T`.
  have hsub : {θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ ⊆
      Γ '' ((T : Set (Rn N)) ∩ Metric.ball 0 ρ) := by
    rintro ξ ⟨⟨hξH, hξ1⟩, hξ⟩
    rw [Metric.mem_ball, dist_eq_norm] at hξ
    set s : ℝ := inner ℝ ξ ζ
    have hd : ‖ξ - ζ‖ ^ 2 = 2 - 2 * s := by rw [norm_sub_sq_real, hξ1, hζ1]; ring
    have hs1 : s ≤ 1 := by simpa [hξ1, hζ1] using real_inner_le_norm ξ ζ
    have hdlt : ‖ξ - ζ‖ ^ 2 < ρ ^ 2 := by nlinarith [norm_nonneg (ξ - ζ)]
    have hspos : 0 < s := by nlinarith
    set w : Rn N := ξ - s • ζ with hw
    have hwζ : inner ℝ w ζ = 0 := by
      rw [hw, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hζ1]; ring
    have hw2 : ‖w‖ ^ 2 = 1 - s ^ 2 := by
      rw [hw, norm_sub_sq_real, real_inner_smul_right, norm_smul, hξ1, hζ1, Real.norm_eq_abs,
        mul_one, sq_abs]
      ring
    refine ⟨w, ⟨⟨Submodule.mem_orthogonal_singleton_iff_inner_left.2 hwζ,
      H.sub_mem hξH (H.smul_mem s hζ)⟩, ?_⟩, ?_⟩
    · -- `|w|² = (1 - s)(1 + s) ≤ 2 (1 - s) = |ξ - ζ|² < ρ²`
      rw [mem_ball_zero_iff]
      have hle : ‖w‖ ^ 2 ≤ ‖ξ - ζ‖ ^ 2 := by rw [hw2, hd]; nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 hρ.le (hle.trans_lt hdlt)
    · -- `(1 - |w|²)^{1/2} = (s²)^{1/2} = s`
      show w + Real.sqrt (1 - ‖w‖ ^ 2) • ζ = ξ
      rw [hw2, show (1 : ℝ) - (1 - s ^ 2) = s ^ 2 by ring, Real.sqrt_sq hspos.le, hw,
        sub_add_cancel]
  -- `Γ` is `2`-Lipschitz on `T ∩ B(0, ρ)`.
  have hlip : LipschitzOnWith 2 Γ ((T : Set (Rn N)) ∩ Metric.ball 0 ρ) := by
    refine LipschitzOnWith.of_dist_le_mul fun w hw w' hw' ↦ ?_
    have hwζ : inner ℝ w ζ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.1 hw.1.1
    have hwζ' : inner ℝ w' ζ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.1 hw'.1.1
    have ha : ‖w‖ < 1 / 2 := (mem_ball_zero_iff.1 hw.2).trans_le hρ2
    have hb : ‖w'‖ < 1 / 2 := (mem_ball_zero_iff.1 hw'.2).trans_le hρ2
    have ha0 := norm_nonneg w
    have hb0 := norm_nonneg w'
    -- `|f(w) - f(w')| ≤ |w - w'|` for `f(w) = (1 - |w|²)^{1/2}`: with `x = 1 - |w|²` and
    -- `y = 1 - |w'|²` we have `√x, √y ≥ 1/2`, so `|√x - √y| = |x - y| / (√x + √y) ≤ |x - y|`,
    -- and `|x - y| = ||w| - |w'|| (|w| + |w'|) ≤ |w - w'|`.
    have hff : |Real.sqrt (1 - ‖w‖ ^ 2) - Real.sqrt (1 - ‖w'‖ ^ 2)| ≤ ‖w - w'‖ := by
      set x : ℝ := 1 - ‖w‖ ^ 2 with hx
      set y : ℝ := 1 - ‖w'‖ ^ 2 with hy
      have hsx : 1 / 2 ≤ Real.sqrt x := by
        rw [Real.le_sqrt (by norm_num) (by nlinarith)]; nlinarith
      have hsy : 1 / 2 ≤ Real.sqrt y := by
        rw [Real.le_sqrt (by norm_num) (by nlinarith)]; nlinarith
      have hprod : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by nlinarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ y by nlinarith)]
      have hsqrt : |Real.sqrt x - Real.sqrt y| ≤ |x - y| := by
        rw [← hprod, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.sqrt x + Real.sqrt y)]
        nlinarith [abs_nonneg (Real.sqrt x - Real.sqrt y)]
      have hxy : |x - y| = |‖w‖ - ‖w'‖| * (‖w‖ + ‖w'‖) := by
        rw [hx, hy, show (1 - ‖w‖ ^ 2) - (1 - ‖w'‖ ^ 2) = (‖w'‖ - ‖w‖) * (‖w‖ + ‖w'‖) by ring,
          abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ‖w‖ + ‖w'‖), abs_sub_comm]
      refine hsqrt.trans ?_
      rw [hxy]
      nlinarith [abs_norm_sub_norm_le w w', abs_nonneg (‖w‖ - ‖w'‖)]
    -- Pythagoras: `(w - w') ⟂ ζ`, so `|Γ(w) - Γ(w')|² = |w - w'|² + (f(w) - f(w'))² ≤ (2 |w - w'|)²`.
    have hdiff : Γ w - Γ w' =
        (w - w') + (Real.sqrt (1 - ‖w‖ ^ 2) - Real.sqrt (1 - ‖w'‖ ^ 2)) • ζ := by
      simp only [hΓ, sub_smul]; abel
    have hinner : inner ℝ (w - w') ζ = 0 := by rw [inner_sub_left, hwζ, hwζ', sub_zero]
    have hsq : ‖Γ w - Γ w'‖ ^ 2 =
        ‖w - w'‖ ^ 2 + (Real.sqrt (1 - ‖w‖ ^ 2) - Real.sqrt (1 - ‖w'‖ ^ 2)) ^ 2 := by
      rw [hdiff, norm_add_sq_real, real_inner_smul_right, hinner, norm_smul, hζ1, Real.norm_eq_abs,
        mul_one, sq_abs]
      ring
    have hff2 : (Real.sqrt (1 - ‖w‖ ^ 2) - Real.sqrt (1 - ‖w'‖ ^ 2)) ^ 2 ≤ ‖w - w'‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hff 2
    rw [dist_eq_norm, dist_eq_norm]
    have h2 : ‖Γ w - Γ w'‖ ^ 2 ≤ ((2 : ℝ≥0) * ‖w - w'‖) ^ 2 := by
      push_cast; nlinarith [norm_nonneg (w - w')]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  -- Monotonicity and the Lipschitz image bound `Hⁿ(Γ(A)) ≤ 2ⁿ Hⁿ(A)`.
  calc μHE[n] ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ)
      ≤ μHE[n] (Γ '' ((T : Set (Rn N)) ∩ Metric.ball 0 ρ)) := measure_mono hsub
    _ ≤ ((2 : ℝ≥0) : ℝ≥0∞) ^ n * μHE[n] ((T : Set (Rn N)) ∩ Metric.ball 0 ρ) :=
        Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hlip
    _ = 2 ^ n * μHE[n] ((T : Set (Rn N)) ∩ Metric.ball 0 ρ) := by norm_num

/-- **Two-sided `Hⁿ` bounds for caps of the unit sphere of an `(n+1)`-plane** (Step 2.1 of the
cone trichotomy for Simon Ch. 3, Theorem 3.6; Dall'Alba, Lemma 4.15; Mattila, Ch. 18). Let
`H ⊆ ℝ^{n+ℓ}` be a subspace with `dim H = n + 1` and `S(H) = {θ ∈ H : |θ| = 1}`. There are
constants `c > 0` and `C`, depending only on `n` and `H`, such that for every `ζ ∈ S(H)` and
every `ρ > 0`: `c ρⁿ ≤ Hⁿ(S(H) ∩ B(ζ, ρ))` if `ρ ≤ 2`, and `Hⁿ(S(H) ∩ B(ζ, ρ)) ≤ C ρⁿ`. With `ω`
the flat-ball constant (`Hⁿ(T ∩ B(w, ρ)) = ω ρⁿ` on `n`-planes), the projection comparison gives
`c = 2⁻ⁿ ω`; the graph comparison gives `2ⁿ ω ρⁿ` for `ρ ≤ 1/2`; finitely many caps of radius
`1/2` cover the compact `S(H)`, so `σ = Hⁿ(S(H)) < ∞`; and `C = 2ⁿ (ω + σ)` covers `ρ > 1/2`
via `σ ≤ σ (2ρ)ⁿ`. -/
theorem Submission.bf_sphereCap_measure_bounds : ∀ (n ℓ : ℕ), 0 < n → ∀ H : Submodule ℝ (Rn (n + ℓ)), finrank ℝ H = n + 1 → ∃ c C : ℝ, 0 < c ∧ ∀ ζ ∈ H, ‖ζ‖ = 1 → ∀ ρ : ℝ, 0 < ρ → (ρ ≤ 2 → ENNReal.ofReal (c * ρ ^ n) ≤ μHE[n] ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ)) ∧ μHE[n] ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ) ≤ ENNReal.ofReal (C * ρ ^ n) := by
  intro n ℓ _ H hH
  set S : Set (Rn (n + ℓ)) := {θ | θ ∈ H ∧ ‖θ‖ = 1} with hS
  -- Step 1: the flat-ball constant `ω`, with `Hⁿ(T ∩ B(w, ρ)) = ω ρⁿ` for every `n`-plane `T`.
  obtain ⟨ω, hω, hball⟩ := Submission.bf_planeBall_measure_uniform n
  -- Step 4: small caps, `Hⁿ(S(H) ∩ B(ζ, ρ)) ≤ 2ⁿ Hⁿ(T_ζ ∩ B(0, ρ)) = 2ⁿ ω ρⁿ` for `ρ ≤ 1/2`.
  have hsmall : ∀ ζ ∈ H, ‖ζ‖ = 1 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 →
      μHE[n] (S ∩ Metric.ball ζ ρ) ≤ ENNReal.ofReal (2 ^ n * ω * ρ ^ n) := by
    intro ζ hζ hζ1 ρ hρ hρ2
    obtain ⟨T, hT, hcmp⟩ := Submission.bf_sphereCap_upper_comparison n (n + ℓ) H hH ζ hζ hζ1
    calc μHE[n] (S ∩ Metric.ball ζ ρ)
        ≤ 2 ^ n * μHE[n] ((T : Set (Rn (n + ℓ))) ∩ Metric.ball 0 ρ) := hcmp ρ hρ hρ2
      _ = ENNReal.ofReal (2 ^ n * ω * ρ ^ n) := by
        rw [hball (n + ℓ) T hT 0 T.zero_mem ρ hρ, mul_assoc,
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ n),
          ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  -- Step 5: `Hⁿ(S(H)) < ∞`, since the compact `S(H)` is covered by finitely many caps of radius
  -- `1/2`, each of measure at most `2ⁿ ω 2⁻ⁿ`.
  have hScpt : IsCompact S := by
    have hSeq : S = (H : Set (Rn (n + ℓ))) ∩ {θ | ‖θ‖ = 1} := rfl
    rw [hSeq]
    refine Metric.isCompact_of_isClosed_isBounded
      (H.closed_of_finiteDimensional.inter (isClosed_eq continuous_norm continuous_const))
      ((Metric.isBounded_closedBall (x := (0 : Rn (n + ℓ))) (r := 1)).subset ?_)
    rintro θ ⟨-, hθ⟩
    have hθ1 : ‖θ‖ = 1 := hθ
    rw [mem_closedBall_zero_iff]
    exact hθ1.le
  obtain ⟨t, htS, htfin, hcover⟩ :=
    finite_cover_balls_of_compact hScpt (by norm_num : (0 : ℝ) < 1 / 2)
  have hSfin : μHE[n] S < ∞ := by
    have hsub : S ⊆ ⋃ ζ ∈ t, S ∩ Metric.ball ζ (1 / 2) := fun θ hθ ↦ by
      obtain ⟨ζ, hζt, hθζ⟩ := Set.mem_iUnion₂.1 (hcover hθ)
      exact Set.mem_iUnion₂.2 ⟨ζ, hζt, hθ, hθζ⟩
    refine (measure_mono hsub).trans_lt (measure_biUnion_lt_top htfin fun ζ hζ ↦ ?_)
    have hζS : ζ ∈ H ∧ ‖ζ‖ = 1 := by
      have := htS hζ
      rwa [hS] at this
    exact (hsmall ζ hζS.1 hζS.2 (1 / 2) (by norm_num) le_rfl).trans_lt ENNReal.ofReal_lt_top
  -- Steps 3, 6 and 7: `c = 2⁻ⁿ ω` and `C = 2ⁿ (ω + σ)` with `σ = Hⁿ(S(H))`.
  set σ : ℝ := (μHE[n] S).toReal
  have hσ0 : 0 ≤ σ := ENNReal.toReal_nonneg
  refine ⟨ω / 2 ^ n, 2 ^ n * (ω + σ), div_pos hω (pow_pos two_pos n),
    fun ζ hζ hζ1 ρ hρ ↦ ⟨fun hρ2 ↦ ?_, ?_⟩⟩
  · -- Step 3: `c ρⁿ = ω (ρ/2)ⁿ = Hⁿ(T_ζ ∩ B(0, ρ/2)) ≤ Hⁿ(S(H) ∩ B(ζ, ρ))`.
    obtain ⟨T, hT, hcmp⟩ := Submission.bf_sphereCap_lower_comparison n (n + ℓ) H hH ζ hζ hζ1
    calc ENNReal.ofReal (ω / 2 ^ n * ρ ^ n) = ENNReal.ofReal (ω * (ρ / 2) ^ n) := by
          congr 1
          rw [div_pow]
          ring
      _ = μHE[n] ((T : Set (Rn (n + ℓ))) ∩ Metric.ball 0 (ρ / 2)) :=
          (hball (n + ℓ) T hT 0 T.zero_mem (ρ / 2) (half_pos hρ)).symm
      _ ≤ μHE[n] (S ∩ Metric.ball ζ ρ) := hcmp ρ hρ hρ2
  · -- Step 6: for `ρ ≤ 1/2` use step 4; for `ρ > 1/2`, `Hⁿ(S(H) ∩ B(ζ, ρ)) ≤ σ ≤ σ (2ρ)ⁿ`.
    rcases le_or_gt ρ (1 / 2) with hρ2 | hρ2
    · refine (hsmall ζ hζ hζ1 ρ hρ hρ2).trans (ENNReal.ofReal_le_ofReal ?_)
      have h2 : 0 ≤ 2 ^ n * σ * ρ ^ n :=
        mul_nonneg (mul_nonneg (pow_nonneg zero_le_two n) hσ0) (pow_nonneg hρ.le n)
      linarith
    · have h1 : 1 ≤ 2 ^ n * ρ ^ n := by
        rw [← mul_pow]
        exact one_le_pow₀ (by linarith)
      calc μHE[n] (S ∩ Metric.ball ζ ρ) ≤ μHE[n] S := measure_mono Set.inter_subset_left
        _ = ENNReal.ofReal σ := (ENNReal.ofReal_toReal hSfin.ne).symm
        _ ≤ ENNReal.ofReal (2 ^ n * (ω + σ) * ρ ^ n) := by
          refine ENNReal.ofReal_le_ofReal ?_
          -- `2ⁿ (ω + σ) ρⁿ - σ = ω (2ρ)ⁿ + σ ((2ρ)ⁿ - 1) ≥ 0`
          nlinarith [mul_nonneg hσ0 (sub_nonneg.2 h1), mul_nonneg hω.le (zero_le_one.trans h1)]

/-- **Almost every unit direction of `H` is good** (the sphere lemma of the Besicovitch–Federer
argument, Simon Ch. 3, Theorem 3.6; Dall'Alba, Theorem 4.16; Mattila Ch. 18). Let `n ≥ 1`,
`H ⊆ ℝ^{n+ℓ}` a subspace of dimension `n + 1` with orthogonal projection `p_H`, `A ⊆ ℝ^{n+ℓ}`
compact with `Hⁿ(A) < ∞`, `δ > 0` and `a ∈ ℝ^{n+ℓ}`. For `Hⁿ`-a.e. unit vector `θ ∈ H`, the slab
cones `Z_θ(s) = {x : |p_H(x - a) - (p_H(x - a) · θ) θ| < s |p_H(x - a)|}` with vertex `a` satisfy
`Hⁿ(A ∩ Z_θ(s) ∩ B_r(a)) = o((rs)ⁿ)` as `s ↓ 0`, uniformly in `r ∈ (0, δ)` (`Ψ0`), or the ratios
`Hⁿ(A ∩ Z_θ(s) ∩ B_r(a)) / (rs)ⁿ`, `r ∈ (0, δ)`, are unbounded as `s ↓ 0` (`Ψ∞`), or the axis of `θ`
meets `A ∖ {a}` within distance `δ` after projecting to `H` (`Ax′`). With `σ_H = Hⁿ ⌞ S(H)` (finite,
with cap bounds `c₁ρⁿ ≤ σ_H(B_ρ(ζ)) ≤ C₁ρⁿ`) and the double-cone outer measure `m` on directions,
the axis-free directions form a Borel `m`-null set `F ⊆ S(H)`; by the density dichotomy, `σ_H`-a.e.
`θ ∈ F` has vanishing or infinite upper `m`-density of caps, which gives `Ψ0` or `Ψ∞` at `θ`. -/
theorem Submission.bf_sphere_ae_slabGood : ∀ (n ℓ : ℕ), 0 < n → ∀ H : Submodule ℝ (Rn (n + ℓ)), finrank ℝ H = n + 1 → ∀ A : Set (Rn (n + ℓ)), IsCompact A → μHE[n] A < ∞ → ∀ δ : ℝ, 0 < δ → ∀ a : Rn (n + ℓ), μHE[n] {θ | θ ∈ H ∧ ‖θ‖ = 1 ∧ ¬ ((∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ, 0 < r → r < δ → μHE[n] (A ∩ ({x | ‖H.starProjection (x - a) - inner ℝ (H.starProjection (x - a)) θ • θ‖ < s * ‖H.starProjection (x - a)‖} ∩ Metric.ball a r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) ∨ (∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μHE[n] (A ∩ ({x | ‖H.starProjection (x - a) - inner ℝ (H.starProjection (x - a)) θ • θ‖ < s * ‖H.starProjection (x - a)‖} ∩ Metric.ball a r))) ∨ ∃ b ∈ A, b ≠ a ∧ dist b a < δ ∧ H.starProjection (b - a) - inner ℝ (H.starProjection (b - a)) θ • θ = 0)} = 0 := by
  intro n ℓ hn H hH A hA _ δ hδ a
  -- Step 0: the unit sphere `S(H)` of `H` is closed; `σ_H = Hⁿ ⌞ S(H)`.
  let S : Set (Rn (n + ℓ)) := {θ | θ ∈ H ∧ ‖θ‖ = 1}
  have hSmeas : MeasurableSet S :=
    (H.closed_of_finiteDimensional.inter
      (isClosed_eq continuous_norm continuous_const)).measurableSet
  have hσ : ∀ (ζ : Rn (n + ℓ)) (ρ : ℝ),
      (μHE[n] : Measure (Rn (n + ℓ))).restrict S (Metric.ball ζ ρ) =
        μHE[n] (S ∩ Metric.ball ζ ρ) := fun ζ ρ ↦ by
    rw [Measure.restrict_apply' hSmeas, inter_comm]
  -- The cap bounds `c₁ρⁿ ≤ σ_H(B_ρ(ζ)) ≤ C₁ρⁿ` (sibling `sphere_cap_bounds`).
  obtain ⟨c₁, C₁, hc₁, hcap⟩ := Submission.bf_sphereCap_measure_bounds n ℓ hn H hH
  -- `σ_H` is finite: `S(H) ⊆ B₃(ζ₀)` for any `ζ₀ ∈ S(H)`.
  have hSfin : μHE[n] S < ∞ := by
    rcases S.eq_empty_or_nonempty with hS0 | ⟨ζ₀, hζ₀⟩
    · rw [hS0, measure_empty]
      exact ENNReal.zero_lt_top
    · have hsub : S ⊆ S ∩ Metric.ball ζ₀ 3 := fun θ hθ ↦ ⟨hθ, by
        rw [Metric.mem_ball, dist_eq_norm]
        linarith [norm_sub_le θ ζ₀, hθ.2, hζ₀.2]⟩
      calc μHE[n] S ≤ μHE[n] (S ∩ Metric.ball ζ₀ 3) := measure_mono hsub
        _ ≤ ENNReal.ofReal (C₁ * 3 ^ n) := (hcap ζ₀ hζ₀.1 hζ₀.2 3 (by norm_num)).2
        _ < ∞ := ENNReal.ofReal_lt_top
  have hσfin : IsFiniteMeasure ((μHE[n] : Measure (Rn (n + ℓ))).restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hSfin⟩
  -- Steps 1–3: the double-cone outer measure `m` on directions; it vanishes on the Borel set
  -- `F = S(H) ∖ C` of axis-free directions, and its cap densities control `Ψ0` and `Ψ∞`.
  obtain ⟨m, hmF, hm⟩ :=
    Submission.bf_sphereGood_doubleCone_outerMeasure (n + ℓ) n H A δ hδ a
  -- Step 4: the density dichotomy for `σ_H` and `m` on `F`.
  have hnull := Submission.bf_sphereGood_densityDichotomy (n + ℓ) n
    ((μHE[n] : Measure (Rn (n + ℓ))).restrict S) hσfin S c₁ C₁ hc₁
    (fun ζ hζ ρ hρ hρ2 ↦ by rw [hσ]; exact (hcap ζ hζ.1 hζ.2 ρ hρ).1 hρ2)
    (fun ζ hζ ρ hρ ↦ by rw [hσ]; exact (hcap ζ hζ.1 hζ.2 ρ hρ).2) m _
    (Submission.bf_sphereGood_axisFree_measurableSet (n + ℓ) H A hA δ a)
    (fun θ hθ ↦ ⟨hθ.1, hθ.2.1⟩) hmF
  rw [Measure.restrict_apply' hSmeas] at hnull
  -- Step 5: a non-good direction is axis-free and has neither vanishing nor infinite upper cap
  -- density, so it lies in the `σ_H`-null exceptional set of the dichotomy.
  refine measure_mono_null ?_ hnull
  rintro θ ⟨hθH, hθ1, hbad⟩
  obtain ⟨hΨ0, hbad⟩ := not_or.1 hbad
  obtain ⟨hΨinf, hAx⟩ := not_or.1 hbad
  exact ⟨⟨⟨hθH, hθ1, hAx⟩, fun hα ↦ hΨ0 ((hm θ hθH hθ1).1 hα),
    fun hβ ↦ hΨinf ((hm θ hθH hθ1).2 hβ)⟩, hθH, hθ1⟩

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
