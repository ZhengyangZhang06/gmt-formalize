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

/-- **Pairing upper bound** (the easy half `sup ≤ μ(O)` of the total-variation formula behind
Simon Ch. 2, (2.4) (`chapter-02.txt` lines 517–521), used for the uniqueness in Ch. 3, (4.1)):
if `|ν| ≤ 1` `μ`-a.e., `O` is Borel, `tsupport g ⊆ O` and `|g| ≤ 1`, then
`ofReal(∫ ⟨g, ν⟩ dμ) ≤ μ(O)`. On `O` Cauchy–Schwarz gives `|⟨g, ν⟩| ≤ 1`, and off `O` we have
`g = 0`, so `|⟨g, ν⟩| ≤ 1_O` `μ`-a.e. Hence
`ofReal(∫ ⟨g, ν⟩ dμ) ≤ ‖∫ ⟨g, ν⟩ dμ‖ₑ ≤ ∫⁻ ‖⟨g, ν⟩‖ₑ dμ ≤ ∫⁻ 1_O dμ = μ(O)`. No integrability is
needed: the Bochner integral of a non-integrable function is `0`. -/
theorem Submission.gaussGreenVar_ofReal_integral_inner_le_measure : ∀ (N : ℕ) (O : Set (Rn N)) (μ : Measure (Rn N)) (ν g : Rn N → Rn N), MeasurableSet O → (∀ᵐ x ∂μ, ‖ν x‖ ≤ 1) → tsupport g ⊆ O → (∀ x, ‖g x‖ ≤ 1) → ENNReal.ofReal (∫ x, inner ℝ (g x) (ν x) ∂μ) ≤ μ O := by
  intro N O μ ν g hO hν hgO hg
  -- Step 1: `‖⟨g x, ν x⟩‖ₑ ≤ 1_O(x)` for `μ`-a.e. `x`.
  have hbound : ∀ᵐ x ∂μ, ‖inner ℝ (g x) (ν x)‖ₑ ≤ O.indicator 1 x := by
    filter_upwards [hν] with x hx
    by_cases hxO : x ∈ O
    · -- (a) On `O`, Cauchy–Schwarz: `|⟨g x, ν x⟩| ≤ ‖g x‖ ‖ν x‖ ≤ 1`.
      rw [indicator_of_mem hxO, Pi.one_apply, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_one]
      calc |inner ℝ (g x) (ν x)| ≤ ‖g x‖ * ‖ν x‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * 1 := mul_le_mul (hg x) hx (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · -- (b) Off `O`, `x ∉ tsupport g`, so `g x = 0` and the pairing vanishes.
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hxO (hgO h), inner_zero_left, enorm_zero]
      exact zero_le
  -- Steps 2–5: `ofReal(∫ f) ≤ ‖∫ f‖ₑ ≤ ∫⁻ ‖f‖ₑ ≤ ∫⁻ 1_O = μ(O)`, with no integrability needed.
  calc ENNReal.ofReal (∫ x, inner ℝ (g x) (ν x) ∂μ) ≤ ‖∫ x, inner ℝ (g x) (ν x) ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ x, ‖inner ℝ (g x) (ν x)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, O.indicator 1 x ∂μ := lintegral_mono_ae hbound
    _ = μ O := lintegral_indicator_one hO
/-- **Compact inner approximation of open sets, for an arbitrary measure** (step 2 of the
total-variation formula `μ_E(O) = sup ∫ g · ν dμ_E` behind Simon Ch. 3, (4.1); compare Ch. 1,
Remark 1.16 (`chapter-01.txt` lines 287–295), where a closed subset of a `σ`-compact space is an
increasing union of compact sets). Let `O ⊆ ℝᴺ` be open and `μ` any measure on `ℝᴺ`. If
`μ(K) ≤ c` for every compact `K ⊆ O`, then `μ(O) ≤ c`. Write `O = ⋃ₙ Fₙ` with `Fₙ` closed and
increasing; then `Kₙ = Fₙ ∩ B̄(0, n)` are compact, increasing and exhaust `O`, so continuity from
below gives `μ(O) = supₙ μ(Kₙ) ≤ c`. No finiteness or regularity of `μ` is needed. -/
theorem Submission.gaussGreenVar_measure_isOpen_le_of_isCompact : ∀ (N : ℕ) (O : Set (Rn N)) (μ : Measure (Rn N)) (c : ℝ≥0∞), IsOpen O → (∀ K : Set (Rn N), IsCompact K → K ⊆ O → μ K ≤ c) → μ O ≤ c := by
  intro N O μ c hO hK
  -- Step 1: closed exhaustion `F n` of `O`.
  obtain ⟨F, hFc, hFO, hFU, hFm⟩ := hO.exists_iUnion_isClosed
  -- Step 2: compact exhaustion `K n := F n ∩ B̄(0, n)`.
  let K : ℕ → Set (Rn N) := fun n ↦ F n ∩ Metric.closedBall 0 n
  have hKc : ∀ n, IsCompact (K n) := fun n ↦ (isCompact_closedBall 0 (n : ℝ)).inter_left (hFc n)
  have hKO : ∀ n, K n ⊆ O := fun n ↦ inter_subset_left.trans (hFO n)
  have hKm : Monotone K := fun m n hmn ↦
    inter_subset_inter (hFm hmn) (Metric.closedBall_subset_closedBall (by exact_mod_cast hmn))
  -- Step 3: `⋃ n, K n = O`.
  have hKU : ⋃ n, K n = O := by
    refine Subset.antisymm (iUnion_subset hKO) fun x hx ↦ ?_
    rw [← hFU] at hx
    obtain ⟨n, hn⟩ := mem_iUnion.1 hx
    obtain ⟨m, hm⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.2 ⟨max n m, hFm (le_max_left n m) hn, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hm.trans (by exact_mod_cast le_max_right n m)
  -- Steps 4–5: continuity from below, and `μ (K n) ≤ c` for each compact `K n ⊆ O`.
  rw [← hKU, hKm.measure_iUnion]
  exact iSup_le fun n ↦ hK (K n) (hKc n) (hKO n)
/-- **Open outer approximation of a compact set** (step 4 of the total-variation formula behind
Simon Ch. 2, (2.4), `chapter-02.txt` lines 518–526, used for the uniqueness in Ch. 3, (4.1)): if
`O` is open, `K ⊆ O` is compact and `μ` is finite on compact subsets of `O`, then for every
`ε > 0` some open `V` with `K ⊆ V ⊆ O` has `μ(V) < ∞` and `μ(V ∖ K) < ε`. Some closed thickening
`L₀ = {dist(·, K) ≤ δ₀}` is a compact subset of `O`, so `μ(L₀) < ∞`; the open thickenings
`V_r = {dist(·, K) < r}` decrease to the closed set `K` as `r ↓ 0`, so `μ(V_r) → μ(K)`
(`tendsto_measure_thickening_of_isClosed`). Take `V = V_r` with `r < δ₀` and
`μ(V_r) < μ(K) + ε`; then `μ(V ∖ K) = μ(V) - μ(K) < ε`. -/
theorem Submission.gaussGreenVar_exists_isOpen_superset_measure_sdiff_lt : ∀ (N : ℕ) (O K : Set (Rn N)) (μ : Measure (Rn N)), IsOpen O → IsCompact K → K ⊆ O → (∀ L : Set (Rn N), IsCompact L → L ⊆ O → μ L < ∞) → ∀ ε : ℝ≥0∞, 0 < ε → ∃ V : Set (Rn N), IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ μ V < ∞ ∧ μ (V \ K) < ε := by
  intro N O K μ hO hK hKO hfin ε hε
  -- A compact closed thickening `L₀ = cthickening δ K` inside `O`; `μ` is finite on it and on `K`.
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  have hL₀ : μ (Metric.cthickening δ K) < ∞ := hfin _ hK.cthickening hδO
  have hKfin : μ K < ∞ := hfin K hK hKO
  -- Continuity from above along the open thickenings `V_r = thickening r K`, `r ↓ 0`.
  have htend : Tendsto (fun r ↦ μ (Metric.thickening r K)) (𝓝[>] 0) (𝓝 (μ K)) :=
    tendsto_measure_thickening_of_isClosed
      ⟨δ, hδ, ((measure_mono (Metric.thickening_subset_cthickening δ K)).trans_lt hL₀).ne⟩
      hK.isClosed
  -- Choose `0 < r < δ` with `μ(V_r) < μ(K) + ε`.
  have hlt : μ K < μ K + ε := ENNReal.lt_add_right hKfin.ne hε.ne'
  have h₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (Metric.thickening r K) < μ K + ε := htend (Iio_mem_nhds hlt)
  have h₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < δ := nhdsWithin_le_nhds (Iio_mem_nhds hδ)
  have h₃ : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hrμ, hrδ, hr⟩ := (h₁.and (h₂.and h₃)).exists
  have hKV : K ⊆ Metric.thickening r K := Metric.self_subset_thickening hr K
  have hVL₀ : Metric.thickening r K ⊆ Metric.cthickening δ K :=
    Metric.thickening_subset_cthickening_of_le (le_of_lt hrδ) K
  refine ⟨Metric.thickening r K, Metric.isOpen_thickening, hKV, hVL₀.trans hδO,
    (measure_mono hVL₀).trans_lt hL₀, ?_⟩
  -- `μ(V ∖ K) = μ(V) - μ(K) < ε`, as `K` is closed with `μ(K) < ∞`.
  rw [measure_sdiff hKV hK.isClosed.measurableSet.nullMeasurableSet hKfin.ne]
  exact ENNReal.sub_lt_of_lt_add (measure_mono hKV) (by rwa [add_comm] at hrμ)
/-- **Lusin's theorem for `ℝᴺ`-valued Borel maps on a set of finite `μ`-measure** (Simon Ch. 1,
Theorems 1.15 and 1.17, `chapter-01.txt` lines 274–372): for any measure `μ` on `ℝᴺ`, a Borel
`f : ℝᴺ → ℝᴺ`, a Borel `A` with `μ(A) < ∞` and `ε ∈ (0, ∞]`, some closed `C ⊆ A` has
`μ(A ∖ C) < ε` and `f|C` continuous. `ρ = μ⌞A` is a finite Borel measure on a metric space, hence
outer regular and closed-inner regular (Simon 1.15). For each `V` in a countable basis of `ℝᴺ`
take an open `U_V ⊇ f⁻¹(V)` with `ρ(U_V ∖ f⁻¹(V))` small. Off `E = ⋃_V (U_V ∖ f⁻¹(V))` each
`f⁻¹(V)` agrees with the open `U_V`, so `f` is continuous on every `C ⊆ Eᶜ`; a closed
`C ⊆ A ∖ E` with small `ρ`-defect works. -/
theorem Submission.gaussGreenVar_lusin_closed_subset_continuousOn : ∀ (N : ℕ) (μ : Measure (Rn N)) (f : Rn N → Rn N) (A : Set (Rn N)), Measurable f → MeasurableSet A → μ A ≠ ∞ → ∀ ε : ℝ≥0∞, 0 < ε → ∃ C ⊆ A, IsClosed C ∧ μ (A \ C) < ε ∧ ContinuousOn f C := by
  intro N μ f A hf hA hAfin ε hε
  -- The finite Borel measure `ρ = μ⌞A` is weakly regular (Simon 1.15).
  set ρ := μ.restrict A
  have : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr hAfin
  -- A countable basis of `ℝᴺ` and the exceptional set `E`.
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  have hB := TopologicalSpace.isBasis_countableBasis (Rn N)
  have : Countable (TopologicalSpace.countableBasis (Rn N)) :=
    (TopologicalSpace.countable_countableBasis (Rn N)).to_subtype
  have hpre : ∀ V : TopologicalSpace.countableBasis (Rn N),
      MeasurableSet (f ⁻¹' (V : Set (Rn N))) :=
    fun V ↦ hf (hB.isOpen V.2).measurableSet
  obtain ⟨δ, hδ0, hδ⟩ :=
    ENNReal.exists_pos_sum_of_countable hε2 (TopologicalSpace.countableBasis (Rn N))
  have hV : ∀ V : TopologicalSpace.countableBasis (Rn N), ∃ U, U ⊇ f ⁻¹' (V : Set (Rn N)) ∧
      IsOpen U ∧ ρ U < ∞ ∧ ρ (U \ f ⁻¹' (V : Set (Rn N))) < δ V := fun V ↦
    (hpre V).exists_isOpen_sdiff_lt (measure_ne_top ρ _) (ENNReal.coe_ne_zero.2 (hδ0 V).ne')
  choose U hVU hU _hUfin hUV using hV
  set E := ⋃ V, U V \ f ⁻¹' (V : Set (Rn N))
  have hEm : MeasurableSet E := MeasurableSet.iUnion fun V ↦ (hU V).measurableSet.diff (hpre V)
  have hEε : ρ E < ε / 2 :=
    calc ρ E ≤ ∑' V, ρ (U V \ f ⁻¹' (V : Set (Rn N))) := measure_iUnion_le _
      _ ≤ ∑' V, (δ V : ℝ≥0∞) := ENNReal.tsum_le_tsum fun V ↦ (hUV V).le
      _ < ε / 2 := hδ
  -- A closed `C ⊆ A ∖ E` with `ρ((A ∖ E) ∖ C) < ε / 2` (Simon 1.15(2) for `ρ`).
  obtain ⟨C, hCAE, hC, hCε⟩ :=
    (hA.diff hEm).exists_isClosed_sdiff_lt (μ := ρ) (measure_ne_top ρ _) hε2
  refine ⟨C, hCAE.trans sdiff_subset, hC, ?_, ?_⟩
  · -- `μ(A ∖ C) = ρ(A ∖ C) ≤ ρ((A ∖ E) ∖ C) + ρ(E) < ε`.
    rw [← Measure.restrict_eq_self μ sdiff_subset]
    calc ρ (A \ C) ≤ ρ ((A \ E) \ C ∪ E) := by
          refine measure_mono fun x hx ↦ ?_
          by_cases hxE : x ∈ E
          · exact Or.inr hxE
          · exact Or.inl ⟨⟨hx.1, hxE⟩, hx.2⟩
      _ ≤ ρ ((A \ E) \ C) + ρ E := measure_union_le _ _
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hCε hEε
      _ = ε := ENNReal.add_halves ε
  · -- Off `E`, `f⁻¹(V) = U_V` for every basic `V`, so `f` is continuous on `C`.
    intro x hxC
    rw [ContinuousWithinAt, hB.nhds_hasBasis.tendsto_right_iff]
    rintro V ⟨hVB, hfxV⟩
    filter_upwards [mem_nhdsWithin_of_mem_nhds ((hU ⟨V, hVB⟩).mem_nhds (hVU ⟨V, hVB⟩ hfxV)),
      self_mem_nhdsWithin] with y hyU hyC
    by_contra hyV
    exact (hCAE hyC).2 (mem_iUnion.2 ⟨⟨V, hVB⟩, hyU, hyV⟩)
/-- **Tietze–Urysohn unit-field extension** (steps 6–7 of the variation formula behind
`GaussGreenRepresentation`): a field `f` continuous on a compact `C ⊆ V`, `V` open, with
`|f| ≤ 1` on `C` agrees on `C` with a continuous `g`, `|g| ≤ 1`, with compact support in `V`.
Tietze extends `f|C` coordinatewise to `G₁` (proved inline by the classical Urysohn iteration
`u_n`, `|u_n| ≤ (2/3)ⁿ/3`, since `Mathlib.Topology.TietzeExtension` is not imported);
`G = G₁ / max(1, |G₁|)` has `|G| ≤ 1` and `G = f` on `C`; with a Urysohn cut-off `χ`
(`χ = 1` on `C`, compact `tsupport χ ⊆ V`, `0 ≤ χ ≤ 1`) take `g = χ G`. -/
theorem Submission.gaussGreenVar_exists_unit_field_eqOn_compact : ∀ (N : ℕ) (C V : Set (Rn N))
    (f : Rn N → Rn N), IsCompact C → IsOpen V → C ⊆ V → ContinuousOn f C →
    (∀ x ∈ C, ‖f x‖ ≤ 1) → ∃ g : Rn N → Rn N, Continuous g ∧ HasCompactSupport g ∧
      tsupport g ⊆ V ∧ (∀ x, ‖g x‖ ≤ 1) ∧ ∀ x ∈ C, g x = f x := by
  intro N C V f hC hV hCV hf hf1
  -- Step 1: `C` is closed.
  have hCc : IsClosed C := hC.isClosed
  -- Step 2: Tietze extension for real functions on the closed set `C`, by the classical
  -- Urysohn iteration. One step: if `h` is continuous on `C` with `|h| ≤ r` there, then a
  -- continuous `u` on `ℝᴺ` with `|u| ≤ r / 3` approximates `h` within `2r/3` on `C`.
  have step : ∀ (h : Rn N → ℝ) (r : ℝ), 0 < r → ContinuousOn h C → (∀ x ∈ C, |h x| ≤ r) →
      ∃ u : Rn N → ℝ, Continuous u ∧ (∀ x, |u x| ≤ r / 3) ∧
        ∀ x ∈ C, |h x - u x| ≤ 2 / 3 * r := by
    intro h r hr hhc hhr
    obtain ⟨φ, hφA, hφB, hφ01⟩ := exists_continuous_zero_one_of_isClosed
      (hhc.preimage_isClosed_of_isClosed hCc isClosed_Iic :
        IsClosed (C ∩ h ⁻¹' Iic (-(r / 3))))
      (hhc.preimage_isClosed_of_isClosed hCc isClosed_Ici : IsClosed (C ∩ h ⁻¹' Ici (r / 3)))
      (Set.disjoint_left.mpr fun x hx1 hx2 => by
        have h1 : h x ≤ -(r / 3) := hx1.2
        have h2 : r / 3 ≤ h x := hx2.2
        linarith)
    refine ⟨fun x => r / 3 * (2 * φ x - 1), by fun_prop, fun x => ?_, fun x hx => ?_⟩
    · obtain ⟨h0, h1⟩ := hφ01 x
      rw [abs_le]
      constructor <;> nlinarith [mul_nonneg hr.le h0, mul_nonneg hr.le (sub_nonneg.mpr h1)]
    · show |h x - r / 3 * (2 * φ x - 1)| ≤ 2 / 3 * r
      obtain ⟨hb1, hb2⟩ := abs_le.mp (hhr x hx)
      rw [abs_le]
      by_cases h1 : h x ≤ -(r / 3)
      · rw [show φ x = 0 from hφA ⟨hx, h1⟩]
        constructor <;> linarith
      · by_cases h2 : r / 3 ≤ h x
        · rw [show φ x = 1 from hφB ⟨hx, h2⟩]
          constructor <;> linarith
        · obtain ⟨h0, h1'⟩ := hφ01 x
          have h1 := not_le.mp h1
          have h2 := not_le.mp h2
          constructor <;> nlinarith [mul_nonneg hr.le h0, mul_nonneg hr.le (sub_nonneg.mpr h1')]
  -- Iterating the step with `r = (2/3)ⁿ` and summing gives the extension.
  have tietze : ∀ h : Rn N → ℝ, ContinuousOn h C → (∀ x ∈ C, |h x| ≤ 1) →
      ∃ H : Rn N → ℝ, Continuous H ∧ ∀ x ∈ C, H x = h x := by
    intro h hhc hh1
    choose! u hu using step
    -- The remainders `R 0 = h`, `R (n + 1) = R n - u (R n) ((2/3)ⁿ)`.
    obtain ⟨R, hR0, hRs⟩ : ∃ R : ℕ → Rn N → ℝ,
        R 0 = h ∧ ∀ n, R (n + 1) = R n - u (R n) ((2 / 3 : ℝ) ^ n) :=
      ⟨fun n => Nat.rec h (fun k Rk => Rk - u Rk ((2 / 3 : ℝ) ^ k)) n, rfl, fun _ => rfl⟩
    have hR : ∀ n, ContinuousOn (R n) C ∧ ∀ x ∈ C, |R n x| ≤ (2 / 3 : ℝ) ^ n := by
      intro n
      induction n with
      | zero => rw [hR0]; exact ⟨hhc, fun x hx => by simpa using hh1 x hx⟩
      | succ k ih =>
        obtain ⟨hc, -, hb⟩ := hu (R k) ((2 / 3 : ℝ) ^ k) (by positivity) ih.1 ih.2
        rw [hRs k]
        refine ⟨ih.1.sub hc.continuousOn, fun x hx => ?_⟩
        rw [pow_succ, Pi.sub_apply]
        linarith [hb x hx]
    have hv : ∀ n, Continuous (u (R n) ((2 / 3 : ℝ) ^ n)) ∧
        ∀ x, ‖u (R n) ((2 / 3 : ℝ) ^ n) x‖ ≤ (2 / 3 : ℝ) ^ n / 3 := fun n => by
      obtain ⟨hc, hb, -⟩ := hu (R n) ((2 / 3 : ℝ) ^ n) (by positivity) (hR n).1 (hR n).2
      exact ⟨hc, fun x => by rw [Real.norm_eq_abs]; exact hb x⟩
    have hgeom : Summable fun n : ℕ => (2 / 3 : ℝ) ^ n / 3 :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).div_const 3
    refine ⟨fun x => ∑' n, u (R n) ((2 / 3 : ℝ) ^ n) x,
      continuous_tsum (fun n => (hv n).1) hgeom (fun n x => (hv n).2 x), fun x hx => ?_⟩
    -- On `C` the partial sums are `h - R n`, and `|R n| ≤ (2/3)ⁿ → 0`.
    have hpart : ∀ n, ∑ k ∈ Finset.range n, u (R k) ((2 / 3 : ℝ) ^ k) x = h x - R n x := by
      intro n
      induction n with
      | zero => simp [hR0]
      | succ k ih => rw [Finset.sum_range_succ, ih, hRs k, Pi.sub_apply]; ring
    have hRx : Tendsto (fun n => R n x) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact (hR n).2 x hx)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    have hlim : Tendsto (fun n => ∑ k ∈ Finset.range n, u (R k) ((2 / 3 : ℝ) ^ k) x) atTop
        (𝓝 (h x)) := by
      simp_rw [hpart]
      simpa using (tendsto_const_nhds (x := h x)).sub hRx
    exact tendsto_nhds_unique
      (Summable.of_norm_bounded hgeom (fun n => (hv n).2 x)).hasSum.tendsto_sum_nat hlim
  -- Coordinatewise extension `G₁` of `f`, continuous on `ℝᴺ` and equal to `f` on `C`.
  have hcoord : ∀ i : Fin N, ∃ H : Rn N → ℝ, Continuous H ∧ ∀ x ∈ C, H x = f x i := by
    intro i
    refine tietze (fun x => f x i) ((PiLp.continuous_apply 2 _ i).comp_continuousOn hf)
      (fun x hx => ?_)
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le (f x) i).trans (hf1 x hx)
  choose H hHc hHC using hcoord
  let G₁ : Rn N → Rn N := fun x => WithLp.toLp 2 fun i => H i x
  have hG₁c : Continuous G₁ := (PiLp.continuous_toLp 2 _).comp (continuous_pi hHc)
  have hG₁C : ∀ x ∈ C, G₁ x = f x := fun x hx => PiLp.ext fun i => hHC i x hx
  -- Step 3: radial retraction `z ↦ z / max(1, |z|)` onto the closed unit ball.
  have hmax : ∀ x, 0 < max 1 ‖G₁ x‖ := fun x => lt_of_lt_of_le one_pos (le_max_left _ _)
  let G : Rn N → Rn N := fun x => (max 1 ‖G₁ x‖)⁻¹ • G₁ x
  have hGc : Continuous G :=
    ((continuous_const.max hG₁c.norm).inv₀ fun x => (hmax x).ne').smul hG₁c
  have hG1 : ∀ x, ‖G x‖ ≤ 1 := by
    intro x
    simp only [G]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hmax x), inv_mul_le_iff₀ (hmax x),
      mul_one]
    exact le_max_right _ _
  have hGC : ∀ x ∈ C, G x = f x := by
    intro x hx
    simp only [G, hG₁C x hx, max_eq_left (hf1 x hx), inv_one, one_smul]
  -- Step 4: Urysohn cut-off `χ`, equal to `1` on `C`, with compact support inside `V`.
  obtain ⟨χ, hχ1, hχcs, hχV, hχ01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hC hV hCV
  -- Step 5: `g = χ • G`.
  refine ⟨fun x => χ x • G x, χ.continuous.smul hGc,
    HasCompactSupport.smul_right (f := ⇑χ) (f' := G) hχcs,
    (tsupport_smul_subset_left _ _).trans hχV, fun x => ?_, fun x hx => ?_⟩
  · have h1 : ‖χ x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [(hχ01 x).1, (hχ01 x).2]
    rw [norm_smul]
    calc ‖χ x‖ * ‖G x‖ ≤ 1 * 1 := mul_le_mul h1 (hG1 x) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · simp only
    rw [hχ1 hx, Pi.one_apply, one_smul, hGC x hx]
/-- **Lower bound for the pairing** (step 8 of the proof that the total variation `μ(O)` of the
vector measure `ν μ` on an open set `O` is the supremum of the pairings `∫ ⟨g, ν⟩ dμ` over
continuous unit fields `g` supported in `O`, the characterization of `|Du|` by Simon Ch. 2, (2.4)
(`chapter-02.txt` lines 518–522)). Put `f = ⟨g, ν⟩`. By Cauchy–Schwarz `|f| ≤ 1_V` a.e., so `f`
is integrable as `μ(V) < ∞`. A.e. `f ≥ 1_C - 1_{V ∖ C}`: `f = 1` on `C`, `f ≥ -1` on `V ∖ C` and
`f = 0` off `V`. Integrating gives `μ(C) - μ(V ∖ C) ≤ ∫ f dμ` in `ℝ`, and since `μ(C)` and
`μ(V ∖ C)` are finite, `μ(C) ≤ ofReal(∫ f dμ) + μ(V ∖ C)` in `[0, ∞]`. -/
theorem Submission.gaussGreenVar_measure_le_ofReal_integral_inner_add : ∀ (N : ℕ) (μ : Measure (Rn N)) (ν g : Rn N → Rn N) (C V : Set (Rn N)), MeasurableSet C → MeasurableSet V → C ⊆ V → μ V ≠ ∞ → AEStronglyMeasurable ν μ → Continuous g → (∀ᵐ x ∂μ, ‖ν x‖ ≤ 1) → (∀ x, ‖g x‖ ≤ 1) → (∀ x, x ∉ V → g x = 0) → (∀ᵐ x ∂μ, x ∈ C → inner ℝ (g x) (ν x) = 1) → μ C ≤ ENNReal.ofReal (∫ x, inner ℝ (g x) (ν x) ∂μ) + μ (V \ C) := by
  intro N μ ν g C V hC hV hCV hμV hν hg hν1 hg1 hg0 hgC
  -- Step 1: `f = ⟨g, ν⟩` is a.e. strongly measurable (`g` continuous, `⟨·, ·⟩` continuous).
  have hfm : AEStronglyMeasurable (fun x ↦ inner ℝ (g x) (ν x)) μ :=
    continuous_inner.comp_aestronglyMeasurable (hg.aestronglyMeasurable.prodMk hν)
  -- Step 2: `|f| ≤ |g| |ν| ≤ 1` wherever `|ν| ≤ 1`, and `f = 0` off `V`; so `|f| ≤ 1_V` a.e.
  have habs : ∀ x, ‖ν x‖ ≤ 1 → |inner ℝ (g x) (ν x)| ≤ 1 := fun x hx ↦
    (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul (hg1 x) hx (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hbound : ∀ᵐ x ∂μ, ‖inner ℝ (g x) (ν x)‖ ≤ V.indicator 1 x := by
    filter_upwards [hν1] with x hx
    by_cases hxV : x ∈ V
    · rw [indicator_of_mem hxV, Pi.one_apply, Real.norm_eq_abs]
      exact habs x hx
    · rw [indicator_of_notMem hxV, hg0 x hxV, inner_zero_left, norm_zero]
  -- Step 3: integrability; `μ(C) ≤ μ(V) < ∞` and `μ(V ∖ C) ≤ μ(V) < ∞`.
  have hμC : μ C ≠ ∞ := ne_top_of_le_ne_top hμV (measure_mono hCV)
  have hμVC : μ (V \ C) ≠ ∞ := ne_top_of_le_ne_top hμV (measure_mono sdiff_subset)
  have hVint : Integrable (V.indicator (1 : Rn N → ℝ)) μ :=
    (integrableOn_const hμV).integrable_indicator hV
  have hCint : Integrable (C.indicator (1 : Rn N → ℝ)) μ :=
    (integrableOn_const hμC).integrable_indicator hC
  have hVCint : Integrable ((V \ C).indicator (1 : Rn N → ℝ)) μ :=
    (integrableOn_const hμVC).integrable_indicator (hV.diff hC)
  have hfint : Integrable (fun x ↦ inner ℝ (g x) (ν x)) μ := hVint.mono' hfm hbound
  -- Step 4: `1_C - 1_{V ∖ C} ≤ f` a.e., by cases `x ∈ C`, `x ∈ V ∖ C`, `x ∉ V`.
  have hlow : (fun x ↦ C.indicator 1 x - (V \ C).indicator 1 x) ≤ᵐ[μ]
      fun x ↦ inner ℝ (g x) (ν x) := by
    filter_upwards [hν1, hgC] with x hx hxC
    by_cases h1 : x ∈ C
    · rw [indicator_of_mem h1, indicator_of_notMem (fun h ↦ h.2 h1), hxC h1, Pi.one_apply,
        sub_zero]
    · by_cases h2 : x ∈ V
      · rw [indicator_of_notMem h1, indicator_of_mem (show x ∈ V \ C from ⟨h2, h1⟩),
          Pi.one_apply, zero_sub]
        exact neg_le_of_abs_le (habs x hx)
      · rw [indicator_of_notMem h1, indicator_of_notMem (fun h ↦ h2 h.1), hg0 x h2,
          inner_zero_left, sub_zero]
  -- Step 5: integrate: `μ(C) - μ(V ∖ C) ≤ ∫ f dμ` in `ℝ`.
  have hint : μ.real C - μ.real (V \ C) ≤ ∫ x, inner ℝ (g x) (ν x) ∂μ := by
    rw [← integral_indicator_one hC, ← integral_indicator_one (hV.diff hC),
      ← integral_sub hCint hVCint]
    exact integral_mono_ae (hCint.sub hVCint) hfint hlow
  -- Step 6: pass to `[0, ∞]` through `ofReal`, using `μ(C), μ(V ∖ C) < ∞`.
  calc μ C = ENNReal.ofReal (μ.real C) := (ofReal_measureReal hμC).symm
    _ ≤ ENNReal.ofReal (∫ x, inner ℝ (g x) (ν x) ∂μ + μ.real (V \ C)) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (∫ x, inner ℝ (g x) (ν x) ∂μ) + ENNReal.ofReal (μ.real (V \ C)) :=
      ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (∫ x, inner ℝ (g x) (ν x) ∂μ) + μ (V \ C) := by
      rw [ofReal_measureReal hμVC]

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03


/-- **Total-variation formula** (step 7 of the uniqueness in `GaussGreenRepresentation`; the
characterization of `|Du|` by Simon Ch. 2, (2.4), `chapter-02.txt` lines 518–526, behind
"`μ_E (= |D χ_E|)`" in Ch. 3, (4.1)). Let `O ⊆ ℝᴺ` be open, `μ` finite on compact subsets of `O`
and `ν` `μ`-a.e. strongly measurable with `|ν| = 1` `μ`-a.e. Then `μ(O)` is the supremum `S` of
`ofReal(∫ ⟨g, ν⟩ dμ)` over continuous `g` with compact support in `O` and `|g| ≤ 1`.
`S ≤ μ(O)` is the pairing upper bound. Conversely it suffices to show `μ(K) ≤ S + ε` for compact
`K ⊆ O` and `ε > 0`. With `η = ε / 3` take an open `V`, `K ⊆ V ⊆ O`, `μ(V) < ∞`, `μ(V ∖ K) < η`,
a Borel version `ν₀` of `ν` and `A = K ∩ {|ν₀| = 1}`, so `μ(K ∖ A) = 0`. Lusin gives a closed
`C ⊆ A` with `μ(A ∖ C) < η` and `ν₀|C` continuous; the unit-field extension gives a competitor
`g` with `tsupport g ⊆ V` and `g = ν₀` on `C`, so `⟨g, ν⟩ = |ν₀|² = 1` a.e. on `C`. The pairing
lower bound gives `μ(C) ≤ ofReal(∫ ⟨g, ν⟩ dμ) + μ(V ∖ C)`; with `μ(K ∖ C) < η` and
`μ(V ∖ C) < 2η` this yields `μ(K) ≤ S + 3η = S + ε`. -/
theorem Submission.gaussGreenRep_measure_eq_iSup_pairing : ∀ (N : ℕ) (O : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen O → (∀ K : Set (Rn N), IsCompact K → K ⊆ O → μ K < ∞) → AEStronglyMeasurable ν μ → (∀ᵐ x ∂μ, ‖ν x‖ = 1) → μ O = ⨆ (g : Rn N → Rn N) (_ : Continuous g) (_ : HasCompactSupport g) (_ : tsupport g ⊆ O) (_ : ∀ x, ‖g x‖ ≤ 1), ENNReal.ofReal (∫ x, inner ℝ (g x) (ν x) ∂μ) := by
  intro N O μ ν hO hfin hν hν1
  have hν1' : ∀ᵐ x ∂μ, ‖ν x‖ ≤ 1 := hν1.mono fun x hx ↦ hx.le
  set S := ⨆ (g : Rn N → Rn N) (_ : Continuous g) (_ : HasCompactSupport g)
    (_ : tsupport g ⊆ O) (_ : ∀ x, ‖g x‖ ≤ 1), ENNReal.ofReal (∫ x, inner ℝ (g x) (ν x) ∂μ)
  refine le_antisymm ?_ ?_
  · -- `μ(O) ≤ S`: by compact inner approximation it suffices that `μ(K) ≤ S + ε`.
    refine Submission.gaussGreenVar_measure_isOpen_le_of_isCompact N O μ S hO fun K hK hKO ↦ ?_
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    -- Step 1: `η = ε / 3`.
    obtain ⟨η, hη, hη3⟩ : ∃ η : ℝ≥0∞, 0 < η ∧ η + η + η = ε :=
      ⟨ε / 3, ENNReal.div_pos (ENNReal.coe_ne_zero.2 hε.ne') ENNReal.ofNat_ne_top,
        ENNReal.add_thirds _⟩
    -- Step 2: an open `V`, `K ⊆ V ⊆ O`, with `μ(V) < ∞` and `μ(V ∖ K) < η`.
    obtain ⟨V, hVo, hKV, hVO, hVfin, hVK⟩ :=
      Submission.gaussGreenVar_exists_isOpen_superset_measure_sdiff_lt N O K μ hO hK hKO hfin η hη
    -- Step 3: a Borel version `ν₀` of `ν`; `A = K ∩ {|ν₀| = 1}` is Borel, finite, `μ(K ∖ A) = 0`.
    obtain ⟨ν₀, hν₀m, hνν₀⟩ : ∃ ν₀ : Rn N → Rn N, Measurable ν₀ ∧ ν =ᵐ[μ] ν₀ :=
      ⟨hν.mk ν, hν.measurable_mk, hν.ae_eq_mk⟩
    set A := K ∩ {x | ‖ν₀ x‖ = 1}
    have hAm : MeasurableSet A :=
      hK.isClosed.measurableSet.inter (hν₀m.norm (measurableSet_singleton 1))
    have hAfin : μ A ≠ ∞ := ((measure_mono inter_subset_left).trans_lt (hfin K hK hKO)).ne
    have hKA : μ (K \ A) = 0 := by
      have h : ∀ᵐ x ∂μ, ‖ν₀ x‖ = 1 := by
        filter_upwards [hνν₀, hν1] with x hx hx1
        rwa [← hx]
      exact measure_mono_null (fun x hx h1 ↦ hx.2 ⟨hx.1, h1⟩) (ae_iff.1 h)
    -- Step 4: Lusin: a closed `C ⊆ A` with `μ(A ∖ C) < η` and `ν₀` continuous on `C`.
    obtain ⟨C, hCA, hCc, hAC, hν₀C⟩ :=
      Submission.gaussGreenVar_lusin_closed_subset_continuousOn N μ ν₀ A hν₀m hAm hAfin η hη
    have hCK : C ⊆ K := hCA.trans inter_subset_left
    have hCV : C ⊆ V := hCK.trans hKV
    have hC1 : ∀ x ∈ C, ‖ν₀ x‖ = 1 := fun x hx ↦ (hCA hx).2
    -- Step 5: an admissible `g` with `tsupport g ⊆ V ⊆ O` and `g = ν₀` on `C`.
    obtain ⟨g, hgc, hgcs, hgV, hg1, hgC⟩ :=
      Submission.gaussGreenVar_exists_unit_field_eqOn_compact N C V ν₀
        (hK.of_isClosed_subset hCc hCK) hVo hCV hν₀C fun x hx ↦ (hC1 x hx).le
    have hgS : ENNReal.ofReal (∫ x, inner ℝ (g x) (ν x) ∂μ) ≤ S :=
      le_iSup_of_le g <| le_iSup_of_le hgc <| le_iSup_of_le hgcs <|
        le_iSup_of_le (hgV.trans hVO) <| le_iSup_of_le hg1 le_rfl
    -- Step 6: `g = 0` off `V` and `⟨g, ν⟩ = |ν₀|² = 1` a.e. on `C`; the pairing lower bound.
    have hg0 : ∀ x, x ∉ V → g x = 0 := fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (hgV h)
    have hgν : ∀ᵐ x ∂μ, x ∈ C → inner ℝ (g x) (ν x) = 1 := by
      filter_upwards [hνν₀] with x hx hxC
      rw [hx, hgC x hxC, real_inner_self_eq_norm_sq, hC1 x hxC, one_pow]
    have hlow : μ C ≤ ENNReal.ofReal (∫ x, inner ℝ (g x) (ν x) ∂μ) + μ (V \ C) :=
      Submission.gaussGreenVar_measure_le_ofReal_integral_inner_add N μ ν g C V
        hCc.measurableSet hVo.measurableSet hCV hVfin.ne hν hgc hν1' hg1 hg0 hgν
    -- Step 7: `μ(K ∖ C) ≤ μ(K ∖ A) + μ(A ∖ C) < η` and `μ(V ∖ C) ≤ μ(V ∖ K) + μ(K ∖ C) < 2η`.
    have hKC : μ (K \ C) ≤ η :=
      calc μ (K \ C) ≤ μ (K \ A ∪ A \ C) := measure_mono (sdiff_triangle K A C)
        _ ≤ μ (K \ A) + μ (A \ C) := measure_union_le _ _
        _ ≤ η := by rw [hKA, zero_add]; exact hAC.le
    have hVC : μ (V \ C) ≤ η + η :=
      calc μ (V \ C) ≤ μ (V \ K ∪ K \ C) := measure_mono (sdiff_triangle V K C)
        _ ≤ μ (V \ K) + μ (K \ C) := measure_union_le _ _
        _ ≤ η + η := add_le_add hVK.le hKC
    -- Step 8: `μ(K) ≤ μ(C) + μ(K ∖ C) ≤ S + (η + η) + η = S + ε`.
    calc μ K ≤ μ (K ∩ C) + μ (K \ C) := measure_le_inter_add_sdiff μ K C
      _ = μ C + μ (K \ C) := by rw [inter_eq_right.2 hCK]
      _ ≤ ENNReal.ofReal (∫ x, inner ℝ (g x) (ν x) ∂μ) + μ (V \ C) + μ (K \ C) :=
        add_le_add hlow le_rfl
      _ ≤ S + (η + η) + η := add_le_add (add_le_add hgS hVC) hKC
      _ = S + ε := by rw [add_assoc, hη3]
  · -- `S ≤ μ(O)`: the pairing upper bound for every competitor.
    refine iSup_le fun g ↦ iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun hgO ↦ iSup_le fun hg1 ↦ ?_
    exact Submission.gaussGreenVar_ofReal_integral_inner_le_measure N O μ ν g hO.measurableSet
      hν1' hgO hg1
