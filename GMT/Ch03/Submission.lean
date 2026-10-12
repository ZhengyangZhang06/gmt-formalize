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

/-- **`normDet` of an adjoint** (Simon Ch. 2, §6, co-area formula for linear maps,
`chapter-02.txt` lines 1424–1461, and Ch. 3 (2.7), `chapter-03.txt` lines 412–419): for a linear
map `P : X → Y` of finite-dimensional real inner product spaces, if `P` is surjective then
`normDet P* = normDet (P ∘ ι)` with `ι` the inclusion of `(ker P)ᗮ`, and otherwise
`normDet P* = 0`. The horizontal map `h = P ∘ ι` is an isomorphism, `P*` corestricts to `h*`
(as `range P* = (ker P)ᗮ`), and in orthonormal bases with a common index the matrix of `h*` is
the transpose of that of `h`. If `P` is not surjective, `ker P* = (range P)ᗮ ≠ 0`. -/
theorem Submission.coarea_normDet_adjoint_eq_horizontal : ∀ {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y] (P : X →ₗ[ℝ] Y), (Function.Surjective P → (LinearMap.adjoint P).normDet = (P ∘ₗ (LinearMap.ker P)ᗮ.subtype).normDet) ∧ (¬ Function.Surjective P → (LinearMap.adjoint P).normDet = 0) := by
  intro X Y _ _ _ _ _ _ P
  refine ⟨fun hP => ?_, fun hP => ?_⟩
  · set H := (LinearMap.ker P)ᗮ
    set h : H →ₗ[ℝ] Y := P ∘ₗ H.subtype with hh
    -- `h` is injective, as `ker P ⊓ (ker P)ᗮ = ⊥`.
    have hinj : Function.Injective h := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro u hu
      have hz : (u : X) ∈ LinearMap.ker P ⊓ H := ⟨hu, u.property⟩
      rw [Submodule.inf_orthogonal_eq_bot] at hz
      exact (Submodule.mem_bot ℝ).mpr (Subtype.ext ((Submodule.mem_bot ℝ).mp hz))
    -- `h` is surjective: `P x = h (x - π x)` with `π` the orthogonal projection onto `ker P`.
    have hsurj : Function.Surjective h := by
      intro y
      obtain ⟨x, rfl⟩ := hP y
      refine ⟨⟨x - (LinearMap.ker P).starProjection x,
        Submodule.sub_starProjection_mem_orthogonal x⟩, ?_⟩
      simp [hh, (LinearMap.mem_ker).mp ((LinearMap.ker P).starProjection_apply_mem x)]
    have hd : finrank ℝ H = finrank ℝ Y := (LinearEquiv.ofBijective h ⟨hinj, hsurj⟩).finrank_eq
    -- `P*` takes values in `H = (ker P)ᗮ = range P*`, and its corestriction to `H` is `h*`.
    have hm : ∀ y, LinearMap.adjoint P y ∈ H := by
      intro y
      rw [show H = LinearMap.range (LinearMap.adjoint P) from LinearMap.orthogonal_ker P]
      exact ⟨y, rfl⟩
    have ha : (LinearMap.adjoint P).codRestrict H hm = LinearMap.adjoint h := by
      apply (LinearMap.eq_adjoint_iff _ _).mpr
      intro y u
      exact LinearMap.adjoint_inner_left P (u : X) y
    rw [← LinearMap.normDet_codRestrict hm, ha]
    -- In orthonormal bases indexed by the same `Fin d`, the matrix of `h*` is `Mᴴ = Mᵀ`.
    classical
    let bH := stdOrthonormalBasis ℝ H
    let bY := (stdOrthonormalBasis ℝ Y).reindex (finCongr hd.symm)
    rw [(LinearMap.adjoint h).normDet_eq_norm_det_toMatrix bY bH,
      h.normDet_eq_norm_det_toMatrix bH bY, LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose]
    simp
  · -- `ker P* = (range P)ᗮ ≠ ⊥`, since `range P ≠ ⊤`.
    rw [LinearMap.normDet_eq_zero_iff_ker_ne_bot, ← LinearMap.orthogonal_range, ne_eq,
      Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top]
    exact hP
/-- **Block-triangular factorization of `normDet`** (step 5 of the parent proof of
`coarea_normDet_chain_rule`, the block form of `A`). Let `f : V → X` be a linear bijection,
`K ⊆ V` a subspace and `W = f(K)ᗮ`. In orthonormal bases of `V = K ⊕ Kᗮ` and `X = f(K) ⊕ W`
indexed by `Fin r ⊕ Fin s` (`r = dim K = dim f(K)`, `s = dim Kᗮ = dim W`), the matrix of `f` is
`fromBlocks M₁₁ M₁₂ 0 M₂₂`: `M₁₁` is the matrix of `f|_K : K → f(K)`, the lower-left block
vanishes because `W ⊥ f(K)`, and `M₂₂` is the matrix of `p_W ∘ f ∘ ι_{Kᗮ}` because
`⟪w, x⟫ = ⟪w, p_W x⟫` for `w ∈ W`. Hence `normDet f = |det M₁₁| · |det M₂₂|`, and
`|det M₁₁| = normDet (f ∘ ι_K)` since corestricting to `f(K)` does not change `normDet`. -/
theorem Submission.coarea_normDet_block_triangular : ∀ {V X : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] (f : V →ₗ[ℝ] X) (K : Submodule ℝ V) (W : Submodule ℝ X), Function.Bijective f → W = (K.map f)ᗮ → f.normDet = (f ∘ₗ K.subtype).normDet * ((W.orthogonalProjectionOnto : X →ₗ[ℝ] W) ∘ₗ f ∘ₗ Kᗮ.subtype).normDet := by
  intro V X _ _ _ _ _ _ f K W hf hW
  classical
  -- Notation: `F = f(K)`, so `W = Fᗮ`.
  obtain ⟨F, hF⟩ : ∃ F : Submodule ℝ X, F = K.map f := ⟨_, rfl⟩
  rw [← hF] at hW
  -- Step 1: dimensions, `dim F = dim K` and `dim W = dim Kᗮ`.
  have hr : finrank ℝ F = finrank ℝ K := by
    rw [hF]; exact (Submodule.equivMapOfInjective f hf.1 K).finrank_eq.symm
  have hVX : finrank ℝ V = finrank ℝ X := (LinearEquiv.ofBijective f hf).finrank_eq
  have e1 := Submodule.finrank_add_finrank_orthogonal K
  have e2 := Submodule.finrank_add_finrank_orthogonal F
  rw [← hW] at e2
  have hs : finrank ℝ W = finrank ℝ Kᗮ := by omega
  -- Steps 2–3: orthonormal bases of `K`, `Kᗮ`, `F`, `W`; adapted bases `β` of `V`, `γ` of `X`.
  let b₁ := stdOrthonormalBasis ℝ K
  let b₂ := stdOrthonormalBasis ℝ Kᗮ
  let c₁ : OrthonormalBasis (Fin (finrank ℝ K)) ℝ F :=
    (stdOrthonormalBasis ℝ F).reindex (finCongr hr)
  let c₂ : OrthonormalBasis (Fin (finrank ℝ Kᗮ)) ℝ W :=
    (stdOrthonormalBasis ℝ W).reindex (finCongr hs)
  let c₂' : OrthonormalBasis (Fin (finrank ℝ Kᗮ)) ℝ Fᗮ := c₂.map (LinearIsometryEquiv.ofEq _ _ hW)
  let β := (b₁.prod b₂).map K.orthogonalDecomposition.symm
  let γ := (c₁.prod c₂').map F.orthogonalDecomposition.symm
  have hβl : ∀ i, β (Sum.inl i) = (b₁ i : V) := by intro i; simp [β]
  have hβr : ∀ j, β (Sum.inr j) = (b₂ j : V) := by intro j; simp [β]
  have hγl : ∀ i, γ (Sum.inl i) = (c₁ i : X) := by intro i; simp [γ]
  have hγr : ∀ j, γ (Sum.inr j) = (c₂ j : X) := by intro j; simp [γ, c₂']
  -- The diagonal blocks: `f_K : K → F` and `g = p_W ∘ f ∘ ι_{Kᗮ} : Kᗮ → W`.
  have hmemF : ∀ k : K, f k ∈ F := fun k => hF ▸ Submodule.mem_map_of_mem k.2
  let fK : K →ₗ[ℝ] F := (f ∘ₗ K.subtype).codRestrict F (fun k => hmemF k)
  let g : Kᗮ →ₗ[ℝ] W := (W.orthogonalProjectionOnto : X →ₗ[ℝ] W) ∘ₗ f ∘ₗ Kᗮ.subtype
  -- Steps 6–7: `normDet = |det|` in square orthonormal bases; `normDet (f ∘ ι_K) = normDet f_K`.
  have h1 : (f ∘ₗ K.subtype).normDet = fK.normDet := (LinearMap.normDet_codRestrict _).symm
  rw [h1, LinearMap.normDet_eq_norm_det_toMatrix f β γ,
    LinearMap.normDet_eq_norm_det_toMatrix fK b₁ c₁, LinearMap.normDet_eq_norm_det_toMatrix g b₂ c₂,
    ← norm_mul]
  congr 1
  -- Step 4: the matrix of `f` in `β`, `γ` is block upper triangular.
  have hM : LinearMap.toMatrix β.toBasis γ.toBasis f =
      Matrix.fromBlocks (LinearMap.toMatrix b₁.toBasis c₁.toBasis fK)
        (Matrix.of fun i j => inner ℝ (c₁ i : X) (f (b₂ j))) 0
        (LinearMap.toMatrix b₂.toBasis c₂.toBasis g) := by
    ext a b
    rcases a with i | i <;> rcases b with j | j
    · -- (a) the `K → F` block is the matrix of `f_K`.
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, Matrix.fromBlocks_apply₁₁,
        hβl, hγl]
      rfl
    · -- (d) the unconstrained block `M₁₂`.
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, Matrix.fromBlocks_apply₁₂,
        hβr, hγl, Matrix.of_apply]
    · -- (b) `W ⊥ F` kills the `K → W` block.
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, Matrix.fromBlocks_apply₂₁,
        hβl, hγr, Matrix.zero_apply]
      have hmem : (c₂ i : X) ∈ Fᗮ := hW ▸ (c₂ i).2
      exact Submodule.inner_left_of_mem_orthogonal (hmemF (b₁ j)) hmem
    · -- (c) `⟪w, x⟫ = ⟪w, p_W x⟫` for `w ∈ W`: the `Kᗮ → W` block is the matrix of `g`.
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, Matrix.fromBlocks_apply₂₂,
        hβr, hγr]
      simp [g]
  -- Step 5: `det (fromBlocks M₁₁ M₁₂ 0 M₂₂) = det M₁₁ * det M₂₂`.
  rw [hM, Matrix.det_fromBlocks_zero₂₁]
/-- **Horizontal step of the `normDet` chain rule** (step 6 of the supplied proof of the `normDet`
chain rule behind the co-area Jacobian, Simon Ch. 3, (2.7)). Let `B : V → X` be bijective,
`Γ = L ∘ B`, `K = ker Γ` and `W = (ker L)ᗮ`. Since `Wᗮ = ker L`, the restriction of `Γ` to `Kᗮ`
factors as `L|_W ∘ (p_W ∘ B|_{Kᗮ})`, and `B(K) = ker L` gives `dim Kᗮ = dim W`; hence
`normDet (Γ|_{Kᗮ}) = normDet (L|_W) · normDet (p_W ∘ B|_{Kᗮ})`. -/
theorem Submission.coarea_normDet_horizontal_comp : ∀ {V X Y : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y] (B : V →ₗ[ℝ] X) (L : X →ₗ[ℝ] Y) (Γ : V →ₗ[ℝ] Y) (K : Submodule ℝ V) (W : Submodule ℝ X), Function.Bijective B → (∀ v, Γ v = L (B v)) → K = LinearMap.ker Γ → W = (LinearMap.ker L)ᗮ → (Γ ∘ₗ Kᗮ.subtype).normDet = (L ∘ₗ W.subtype).normDet * ((W.orthogonalProjectionOnto : X →ₗ[ℝ] W) ∘ₗ B ∘ₗ Kᗮ.subtype).normDet := by
  intro V X Y _ _ _ _ _ _ _ _ _ B L Γ K W hB hΓ hK hW
  -- `Wᗮ = (ker L)ᗮᗮ = ker L`.
  have hWperp : Wᗮ = LinearMap.ker L := by
    rw [hW, Submodule.orthogonal_orthogonal]
  -- `Γ ∘ ι_{Kᗮ} = (L ∘ ι_W) ∘ (p_W ∘ B ∘ ι_{Kᗮ})`, since `B u - p_W (B u) ∈ Wᗮ = ker L`.
  have hcomp : Γ ∘ₗ Kᗮ.subtype =
      (L ∘ₗ W.subtype) ∘ₗ ((W.orthogonalProjectionOnto : X →ₗ[ℝ] W) ∘ₗ B ∘ₗ Kᗮ.subtype) := by
    refine LinearMap.ext fun u ↦ ?_
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, ContinuousLinearMap.coe_coe]
    have h : B u - (W.orthogonalProjectionOnto (B u) : X) ∈ Wᗮ :=
      Submodule.sub_starProjection_mem_orthogonal (K := W) (B u)
    rw [hWperp, LinearMap.mem_ker, map_sub, sub_eq_zero] at h
    rw [hΓ]
    exact h
  -- `ker L = B(K)`, using that `B` is surjective.
  have hker : LinearMap.ker L = K.map B := by
    ext t
    constructor
    · intro ht
      obtain ⟨v, rfl⟩ := hB.2 t
      refine ⟨v, ?_, rfl⟩
      rw [SetLike.mem_coe, hK, LinearMap.mem_ker, hΓ]
      exact LinearMap.mem_ker.mp ht
    · rintro ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, hK, LinearMap.mem_ker, hΓ] at hv
      exact hv
  -- `dim Kᗮ = dim V - dim K = dim X - dim (ker L) = dim W`.
  have hfin : finrank ℝ Kᗮ = finrank ℝ W := by
    have e1 := Submodule.finrank_add_finrank_orthogonal K
    have e2 := Submodule.finrank_add_finrank_orthogonal (LinearMap.ker L)
    rw [← hW] at e2
    have e3 := (LinearEquiv.ofBijective B hB).finrank_eq
    have e4 := (Submodule.equivMapOfInjective B hB.1 K).finrank_eq
    rw [← hker] at e4
    omega
  -- Multiplicativity of `normDet` for a composition through an equal-dimensional space.
  rw [hcomp]
  exact LinearMap.normDet_comp_of_finrank_eq _ _ hfin

/-- **Chain rule for the co-area factor** (Simon Ch. 3, (2.7)–(2.8), `chapter-03.txt`
lines 412–428, where `J^{M*}_f` is reduced to the `C¹` case along charts): let `A : ℝⁿ → ℝᴺ` be
injective with range `T`, `L : T → ℝᵐ` linear and `Γ = L ∘ A`. Then
`normDet L* · normDet A = normDet (A ∘ ι_{ker Γ}) · normDet Γ*`.
The corestriction `A' : ℝⁿ → T` of `A` is bijective with the same `normDet`, `Γ = L ∘ A'` and
`range L = range Γ`. If `Γ` is not surjective, both adjoints have `normDet` zero
(`Submission.coarea_normDet_adjoint_eq_horizontal`). Otherwise `normDet P* = normDet (P ∘ ι)` for
the inclusion `ι` of `(ker P)ᗮ`, `P = L, Γ`; `ker L = A'(K)` for `K = ker Γ`, and with
`W = (ker L)ᗮ`, `g = p_W ∘ A' ∘ ι_{Kᗮ}`:
`normDet A' = normDet (A' ∘ ι_K) · normDet g` (`Submission.coarea_normDet_block_triangular`) and
`normDet (Γ ∘ ι_{Kᗮ}) = normDet (L ∘ ι_W) · normDet g`
(`Submission.coarea_normDet_horizontal_comp`). -/
theorem Submission.coarea_normDet_chain_rule : ∀ (n N m : ℕ) (T : Submodule ℝ (Rn N))
    (A : Rn n →ₗ[ℝ] Rn N) (L : T →ₗ[ℝ] Rn m) (Γ : Rn n →ₗ[ℝ] Rn m), Function.Injective A →
    LinearMap.range A = T → (∀ (v : Rn n) (hv : A v ∈ T), Γ v = L ⟨A v, hv⟩) →
    (LinearMap.adjoint L).normDet * A.normDet =
      (A ∘ₗ (LinearMap.ker Γ).subtype).normDet * (LinearMap.adjoint Γ).normDet := by
  intro n N m T A L Γ hA hT hΓ
  -- Step 1(i): `A` corestricts to a bijection `A' : ℝⁿ → T` with `Γ = L ∘ A'`; corestricting
  -- does not change `normDet`.
  have hmem : ∀ v, A v ∈ T := fun v ↦ hT ▸ LinearMap.mem_range_self A v
  obtain ⟨A', hA'⟩ : ∃ A' : Rn n →ₗ[ℝ] T, A' = A.codRestrict T hmem := ⟨_, rfl⟩
  have hA'v : ∀ v, (A' v : Rn N) = A v := fun v ↦ by rw [hA']; rfl
  have hbij : Function.Bijective A' := by
    refine ⟨fun v w h ↦ hA (by rw [← hA'v, ← hA'v, h]), ?_⟩
    rintro ⟨t, ht⟩
    obtain ⟨v, rfl⟩ : t ∈ LinearMap.range A := hT ▸ ht
    exact ⟨v, Subtype.ext (hA'v v)⟩
  have hΓA' : ∀ v, Γ v = L (A' v) := fun v ↦ by
    rw [hΓ v (hmem v)]
    exact congrArg L (Subtype.ext (hA'v v).symm)
  have hnA : A.normDet = A'.normDet := by
    rw [hA', LinearMap.normDet_codRestrict]
  obtain ⟨K, hK⟩ : ∃ K : Submodule ℝ (Rn n), K = LinearMap.ker Γ := ⟨_, rfl⟩
  rw [← hK]
  have hnAK : (A ∘ₗ K.subtype).normDet = (A' ∘ₗ K.subtype).normDet := by
    have hKT : ∀ k : K, (A ∘ₗ K.subtype) k ∈ T := fun k ↦ hmem k
    have h : A' ∘ₗ K.subtype = (A ∘ₗ K.subtype).codRestrict T hKT :=
      LinearMap.ext fun k ↦ Subtype.ext (hA'v k)
    rw [h, LinearMap.normDet_codRestrict]
  -- Step 2: `range L = range Γ`, since `A'` is onto `T`; so `L` is onto iff `Γ` is.
  by_cases hsurj : Function.Surjective Γ
  · -- Step 4: `normDet P* = normDet (P ∘ ι_{(ker P)ᗮ})` for `P = L, Γ`, and `ker L = A'(K)`.
    have hLsurj : Function.Surjective L := fun y ↦ by
      obtain ⟨v, hv⟩ := hsurj y
      exact ⟨A' v, (hΓA' v).symm.trans hv⟩
    rw [(Submission.coarea_normDet_adjoint_eq_horizontal L).1 hLsurj,
      (Submission.coarea_normDet_adjoint_eq_horizontal Γ).1 hsurj, ← hK]
    have hker : LinearMap.ker L = K.map A' := by
      rw [hK, show Γ = L ∘ₗ A' from LinearMap.ext hΓA', LinearMap.ker_comp,
        Submodule.map_comap_eq_of_surjective hbij.2]
    obtain ⟨W, hW⟩ : ∃ W : Submodule ℝ T, W = (LinearMap.ker L)ᗮ := ⟨_, rfl⟩
    rw [← hW]
    -- Step 5: `A'` is block triangular along `K ⊕ Kᗮ → A'(K) ⊕ W`.
    have hblock := Submission.coarea_normDet_block_triangular A' K W hbij (by rw [hW, hker])
    -- Step 6: `Γ ∘ ι_{Kᗮ} = (L ∘ ι_W) ∘ (p_W ∘ A' ∘ ι_{Kᗮ})`.
    have hstep := Submission.coarea_normDet_horizontal_comp A' L Γ K W hbij hΓA' hK hW
    -- Step 7.
    rw [hnA, hblock, hnAK, hstep]
    ring
  · -- Step 3: neither `L` nor `Γ` is onto, so both adjoints have `normDet` zero.
    have hLsurj : ¬ Function.Surjective L := fun hL ↦ hsurj fun y ↦ by
      obtain ⟨t, ht⟩ := hL y
      obtain ⟨v, rfl⟩ := hbij.2 t
      exact ⟨v, (hΓA' v).trans ht⟩
    rw [(Submission.coarea_normDet_adjoint_eq_horizontal L).2 hLsurj,
      (Submission.coarea_normDet_adjoint_eq_horizontal Γ).2 hsurj, zero_mul, mul_zero]

/-- **Simon Ch. 3, 2.1–2.2 and (2.7)** (`chapter-03.txt` lines 335–360 and 412–418), along a
chart: let `A : ℝⁿ → ℝᴺ` be injective with `range A` a weighted approximate tangent plane of `M`
at `x`, `θ x ≠ 0`, and let `f` have line derivative `Γ w` at `x` in every direction `A w`. Then
`T_x M = range A` (uniqueness of weighted tangent planes, SimonGMT
`HasWeightedApproximateTangentSpaceAt.unique`), `L = Γ ∘ A⁻¹` is a tangential differential on
`range A`, it is `d^M f_x` (uniqueness of line derivatives, `HasLineDerivAt.unique`), and
`J^{M*}_f(x) · normDet A = normDet (A ∘ ι_{ker Γ}) · normDet Γ*` by the chain rule
`Submission.coarea_normDet_chain_rule` applied to `T = range A`, `A`, `L` and `Γ`. -/
theorem Submission.chart_coarea_jacobian_identification : ∀ (n N m : ℕ) (M : Set (Rn N))
    (θ : Rn N → ℝ) (f : Rn N → Rn m) (x : Rn N) (A : Rn n →L[ℝ] Rn N) (Γ : Rn n →L[ℝ] Rn m),
    θ x ≠ 0 → Function.Injective A →
    HasWeightedApproximateTangentSpaceAt n M θ x (LinearMap.range A.toLinearMap) →
    (∀ w : Rn n, HasLineDerivAt ℝ f (Γ w) x (A w)) →
    approxTangentPlane n M θ x = LinearMap.range A.toLinearMap ∧
    (∃ L : ↥(LinearMap.range A.toLinearMap) →L[ℝ] Rn m,
      HasTangentialDifferentialAt (LinearMap.range A.toLinearMap) f x L) ∧
    coareaJacobian (approxTangentPlane n M θ x) f x * A.toLinearMap.normDet =
      (A.toLinearMap ∘ₗ (LinearMap.ker Γ.toLinearMap).subtype).normDet *
        (LinearMap.adjoint Γ.toLinearMap).normDet := by
  intro n N m M θ f x A Γ hθ hA hT hΓ
  set T : Submodule ℝ (Rn N) := LinearMap.range A.toLinearMap
  -- (i) `T_x M = T`: the chosen plane and `T` are both weighted tangent planes and `θ x ≠ 0`.
  have hplane : approxTangentPlane n M θ x = T := by
    have h : ∃ P : Submodule ℝ (Rn N), HasWeightedApproximateTangentSpaceAt n M θ x P := ⟨T, hT⟩
    rw [approxTangentPlane, dite_eq_left h]
    exact Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique hθ
      h.choose_spec hT
  -- (ii) `L = Γ ∘ e⁻¹`, `e : ℝⁿ ≃ T` induced by `A`, has line derivative `Γ w` along `e w = A w`.
  let e : Rn n ≃ₗ[ℝ] T := LinearEquiv.ofInjective A.toLinearMap hA
  have he : ∀ w : Rn n, (e w : Rn N) = A w := fun _ ↦ rfl
  obtain ⟨L, hLe⟩ : ∃ L : T →L[ℝ] Rn m, ∀ w : Rn n, L (e w) = Γ w :=
    ⟨LinearMap.toContinuousLinearMap (Γ.toLinearMap ∘ₗ e.symm.toLinearMap), fun w ↦ by simp⟩
  have hL : HasTangentialDifferentialAt T f x L := by
    intro τ
    obtain ⟨w, rfl⟩ := e.surjective τ
    rw [hLe, he]
    exact hΓ w
  -- `d^M f_x = L`: both are line derivatives of `f` at `x` in every direction `τ ∈ T`.
  have hdiff : tangentialDifferential T f x = L := by
    have h : ∃ L' : T →L[ℝ] Rn m, HasTangentialDifferentialAt T f x L' := ⟨L, hL⟩
    rw [tangentialDifferential, dite_eq_left h]
    exact ContinuousLinearMap.ext fun τ ↦ (h.choose_spec τ).unique (hL τ)
  -- (iii) `J^{M*}_f(x) = normDet L*`, and `Γ v = L (A v)` feeds the co-area chain rule.
  refine ⟨hplane, ⟨L, hL⟩, ?_⟩
  rw [hplane, coareaJacobian, hdiff]
  refine Submission.coarea_normDet_chain_rule n N m T A.toLinearMap L.toLinearMap Γ.toLinearMap
    hA rfl fun v hv ↦ ?_
  show Γ v = L ⟨A v, hv⟩
  rw [show (⟨A v, hv⟩ : T) = e v from Subtype.ext (he v).symm, hLe]

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
