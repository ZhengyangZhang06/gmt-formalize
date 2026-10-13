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

/-- **Flat flux identity** (the flat limit in the last step of Simon Ch. 3, proof of Thm. 4.3,
`chapter-03.txt` lines 739–746: `μ_{ρ⁻¹E} → Hⁿ ⌞ {x^{n+1} = 0}`): for `|e| = 1`,
`H = {y : ⟨y, e⟩ > 0}`, `P = (span{e})^⊥` and `φ ∈ C¹_c(ℝ^{n+1})`,
`∫_H D_eφ dL^{n+1} = -∫_P φ dHⁿ`. Split `ℝ^{n+1} ≅ span{e} × P` measure-preservingly and apply
Fubini; on each line `t ↦ te + p` (`p ∈ P`, so `⟨te + p, e⟩ = t`) the improper FTC gives
`∫_0^∞ D_eφ(te + p) dt = -φ(p)`; finally `Hⁿ ⌞ P` is the volume of `P`, as `dim P = n`. -/
theorem Submission.deGiorgiTM_halfSpace_integral_fderiv : ∀ (n : ℕ) (e : Rn (n + 1)) (φ : Rn (n + 1) → ℝ), ‖e‖ = 1 → ContDiff ℝ 1 φ → HasCompactSupport φ → ∫ y in {y : Rn (n + 1) | 0 < inner ℝ y e}, fderiv ℝ φ y e = -∫ y in ((Submodule.span ℝ {e})ᗮ : Set (Rn (n + 1))), φ y ∂μHE[n] := by
  intro n e φ he hφ hφc
  set L : Submodule ℝ (Rn (n + 1)) := Submodule.span ℝ {e}
  set H : Set (Rn (n + 1)) := {y | 0 < inner ℝ y e}
  set ψ : Rn (n + 1) → ℝ := fun y ↦ fderiv ℝ φ y e
  -- Step 1: `dim P = n`, `ψ = D_eφ` is continuous with compact support, and `H` is open.
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  have : Fact (finrank ℝ (Rn (n + 1)) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hfinP : finrank ℝ Lᗮ = n := Submodule.finrank_orthogonal_span_singleton he0
  have hψc : Continuous ψ := (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hψcs : HasCompactSupport ψ := hφc.fderiv_apply ℝ e
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψcs
  have hHm : MeasurableSet H :=
    (isOpen_lt continuous_const (continuous_id.inner continuous_const)).measurableSet
  -- Step 2: the measure-preserving decomposition `Φ : ℝ^{n+1} ≃ L × P`, then Fubini.
  let Φ := L.measurableEquivProd (0 : Rn (n + 1))
  have hΦ : MeasurePreserving Φ volume volume := by
    have := L.measurePreserving_measurableEquivProd (0 : Rn (n + 1))
    rwa [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at this
  have hΦs : MeasurePreserving Φ.symm volume volume := hΦ.symm Φ
  have hΦapp : ∀ q : L × Lᗮ, Φ.symm q = (q.1 : Rn (n + 1)) + q.2 := by
    intro q
    simp [Φ]
  let F : L × Lᗮ → ℝ := fun q ↦ H.indicator ψ (Φ.symm q)
  have hFi : Integrable F (volume.prod volume) :=
    (hΦs.integrable_comp_emb Φ.symm.measurableEmbedding).mpr (hψi.indicator hHm)
  have h1 : ∫ y in H, ψ y = ∫ p : Lᗮ, ∫ l : L, F (l, p) := by
    rw [← integral_indicator hHm, ← hΦs.integral_comp' (H.indicator ψ)]
    exact integral_prod_symm F hFi
  -- Steps 3–4: for `p ∈ P` the inner integral is `∫_0^∞ ψ(te + p) dt = -φ(p)`.
  have h2 : ∀ p : Lᗮ, ∫ l : L, F (l, p) = -φ p := by
    intro p
    let T := LinearIsometryEquiv.toSpanUnitSingleton (𝕜 := ℝ) e he
    have hT : MeasurePreserving T volume volume := T.measurePreserving
    have hp : inner ℝ (p : Rn (n + 1)) e = 0 := by
      have := p.2
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
      rwa [real_inner_comm]
    set c : ℝ → Rn (n + 1) := fun t ↦ t • e + p
    have hcinner : ∀ t : ℝ, inner ℝ (c t) e = t := by
      intro t
      simp [c, inner_add_left, inner_smul_left, he, hp]
    have hcpre : c ⁻¹' H = Ioi 0 := by
      ext t
      simp [H, hcinner]
    have hciso : Isometry c := by
      refine Isometry.of_dist_eq fun s t ↦ ?_
      simp [c, dist_eq_norm, ← sub_smul, norm_smul, he]
    have hcemb : Topology.IsClosedEmbedding c := hciso.isClosedEmbedding
    have hcc : Continuous c := hciso.continuous
    have hderiv : ∀ t : ℝ, HasDerivAt (fun t ↦ φ (c t)) (ψ (c t)) t := by
      intro t
      have hc' : HasDerivAt c e t := by
        simpa only [one_smul] using ((hasDerivAt_id' t).smul_const e).add_const (p : Rn (n + 1))
      exact ((hφ.differentiable one_ne_zero) (c t)).hasFDerivAt.comp_hasDerivAt t hc'
    have hfcs : HasCompactSupport (φ ∘ c) := hφc.comp_isClosedEmbedding hcemb
    have hgcs : HasCompactSupport (ψ ∘ c) := hψcs.comp_isClosedEmbedding hcemb
    have hgi : Integrable (ψ ∘ c) := (hψc.comp hcc).integrable_of_hasCompactSupport hgcs
    have hlim : Tendsto (φ ∘ c) atTop (𝓝 0) :=
      hfcs.is_zero_at_infty.mono_left atTop_le_cocompact
    calc ∫ l : L, F (l, p) = ∫ t : ℝ, F (T t, p) :=
          (hT.integral_comp T.toMeasurableEquiv.measurableEmbedding (fun l ↦ F (l, p))).symm
      _ = ∫ t : ℝ, (Ioi (0 : ℝ)).indicator (ψ ∘ c) t := by
          congr 1
          ext t
          rw [← hcpre, indicator_comp_right]
          simp [F, hΦapp, T, c]
      _ = ∫ t in Ioi (0 : ℝ), (ψ ∘ c) t := integral_indicator measurableSet_Ioi
      _ = 0 - (φ ∘ c) 0 :=
          integral_Ioi_of_hasDerivAt_of_tendsto (hφ.continuous.comp hcc).continuousWithinAt
            (fun t _ ↦ hderiv t) hgi.integrableOn hlim
      _ = -φ p := by simp [c]
  -- Step 5: `Hⁿ ⌞ P` is the push-forward of the volume of `P`, since `dim P = n`.
  have h3 : ∫ y in (Lᗮ : Set (Rn (n + 1))), φ y ∂μHE[n] = ∫ p : Lᗮ, φ p := by
    have hmap := Isometry.map_euclideanHausdorffMeasure (d := n)
      (isometry_subtype_coe (s := (Lᗮ : Set (Rn (n + 1)))))
    rw [Subtype.range_coe] at hmap
    have hPm : MeasurableSet (Lᗮ : Set (Rn (n + 1))) :=
      Lᗮ.closed_of_finiteDimensional.measurableSet
    have hvol : (μHE[finrank ℝ Lᗮ] : Measure Lᗮ) = volume :=
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume
    rw [hfinP] at hvol
    rw [← hmap, (MeasurableEmbedding.subtype_coe hPm).integral_map, hvol]
    rfl
  -- Step 6: combine Steps 2–5.
  show ∫ y in H, ψ y = _
  rw [h1, h3, ← integral_neg]
  exact integral_congr_ae (Eventually.of_forall h2)
/-- **`L¹_loc` convergence of sets gives convergence of integrals of `C_c` functions**: the
`L¹_loc` step behind the last sentence of the proof of Simon Ch. 3, Theorem 4.3
(`chapter-03.txt` lines 739–746). With `K = tsupport g` and `|g| ≤ M`, whenever `A r` is
null-measurable, `|∫_{A r} g - ∫_H g| = |∫ (1_{A r} - 1_H) g| ≤ M L^N(K ∩ (A r Δ H))`, and the
right side tends to `0` as `r ↓ 0`. -/
theorem Submission.deGiorgiTM_tendsto_setIntegral_of_symmDiff : ∀ (N : ℕ) (A : ℝ → Set (Rn N))
    (H : Set (Rn N)) (g : Rn N → ℝ), (∀ᶠ r in 𝓝[>] (0 : ℝ), NullMeasurableSet (A r) volume) →
    NullMeasurableSet H volume → Continuous g → HasCompactSupport g →
    Tendsto (fun r : ℝ ↦ volume (tsupport g ∩ symmDiff (A r) H)) (𝓝[>] 0) (𝓝 0) →
    Tendsto (fun r : ℝ ↦ ∫ y in A r, g y) (𝓝[>] 0) (𝓝 (∫ y in H, g y)) := by
  intro N A H g hA hH hg hgc hlim
  -- Step 1: `|g| ≤ M`, `g` is integrable, `K = tsupport g` is compact and `g = 0` off `K`.
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  have hgi : Integrable g volume := hg.integrable_of_hasCompactSupport hgc
  have hKm : MeasurableSet (tsupport g) := (isClosed_tsupport g).measurableSet
  have hKfin : volume (tsupport g) < ∞ := hgc.isCompact.measure_lt_top
  -- Steps 2–4: `|∫_{A r} g - ∫_H g| ≤ M L^N(K ∩ (A r Δ H))` whenever `A r` is null-measurable.
  have hbound : ∀ r, NullMeasurableSet (A r) volume →
      ‖(∫ y in A r, g y) - ∫ y in H, g y‖ ≤
        M * (volume (tsupport g ∩ symmDiff (A r) H)).toReal := by
    intro r hAr
    have hS : NullMeasurableSet (tsupport g ∩ symmDiff (A r) H) volume :=
      hKm.nullMeasurableSet.inter (hAr.symmDiff hH)
    have hSfin : volume (tsupport g ∩ symmDiff (A r) H) ≠ ∞ :=
      ((measure_mono inter_subset_left).trans_lt hKfin).ne
    rw [← integral_indicator₀ hAr, ← integral_indicator₀ hH,
      ← integral_sub (hgi.indicator₀ hAr) (hgi.indicator₀ hH)]
    calc ‖∫ y, ((A r).indicator g y - H.indicator g y)‖
        ≤ ∫ y, (tsupport g ∩ symmDiff (A r) H).indicator (fun _ ↦ M) y := by
          refine norm_integral_le_of_norm_le ((integrableOn_const hSfin).integrable_indicator₀ hS)
            (Eventually.of_forall fun y ↦ ?_)
          by_cases hy : y ∈ tsupport g
          · have hMy : |g y| ≤ M := by simpa using hM y
            by_cases hyA : y ∈ A r <;> by_cases hyH : y ∈ H <;>
              simp [hy, hyA, hyH, mem_symmDiff, hMy]
          · have h0 : g y = 0 := image_eq_zero_of_notMem_tsupport hy
            by_cases hyA : y ∈ A r <;> by_cases hyH : y ∈ H <;> simp [hy, hyA, hyH, h0]
      _ = M * (volume (tsupport g ∩ symmDiff (A r) H)).toReal := by
          rw [integral_indicator₀ hS, setIntegral_const, smul_eq_mul, mul_comm, measureReal_def]
  -- Step 5: the bound tends to `0` (`ENNReal.toReal` is continuous at `0`); squeeze.
  have hlim' : Tendsto (fun r ↦ M * (volume (tsupport g ∩ symmDiff (A r) H)).toReal)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim).const_mul M
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun r ↦ norm_nonneg _) ?_ hlim'
  filter_upwards [hA] with r hr using hbound r hr
/-- **Excess defect of the blow-ups** (Step 3(ii) of the supplied proof of (‡) in De Giorgi's
theorem, Simon Ch. 3, Theorem 4.3). Let `|ν| = 1` `μ`-a.e., `|e| = 1`, `μ(B_{ρ₁}(x)) < ∞`, and let the
excess `Q(ρ) = ρ⁻ⁿ ∫_{B_ρ(x)} |ν - e| dμ` tend to `0` as `ρ ↓ 0`. Then for continuous compactly
supported `φ`, `r⁻ⁿ ∫ φ(η_{x,r}(y)) dμ(y) - r⁻ⁿ ∫ φ(η_{x,r}(y)) ⟨e, ν(y)⟩ dμ(y) → 0` as `r ↓ 0`:
if `|φ| ≤ M` and `tsupport φ ⊆ B_R(0)`, then `φ ∘ η_{x,r}` vanishes off `B_{rR}(x)` and
`|1 - ⟨e, ν⟩| = |⟨e, e - ν⟩| ≤ |ν - e|`, so the difference is at most `M Rⁿ Q(rR)`. -/
theorem Submission.deGiorgiTM_blowUp_defect_tendsto_zero : ∀ (N n : ℕ) (μ : Measure (Rn N)) (ν : Rn N → Rn N) (x e : Rn N) (ρ₁ : ℝ) (φ : Rn N → ℝ), 0 < ρ₁ → μ (Metric.ball x ρ₁) < ∞ → AEStronglyMeasurable ν μ → (∀ᵐ y ∂μ, ‖ν y‖ = 1) → ‖e‖ = 1 → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ y in Metric.ball x ρ, ‖ν y - e‖ ∂μ) (𝓝[>] 0) (𝓝 0) → Continuous φ → HasCompactSupport φ → Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ y, φ (blowUpMap x r y) ∂μ - (r ^ n)⁻¹ * ∫ y, φ (blowUpMap x r y) * inner ℝ e (ν y) ∂μ) (𝓝[>] 0) (𝓝 0) := by
  intro N n μ ν x e ρ₁ φ hρ₁ hμ hν hν1 he hQ hφ hφs
  -- Step 1: `|φ| ≤ M` everywhere and `tsupport φ ⊆ B_R(0)` with `R > 0`.
  obtain ⟨M, hM⟩ := hφ.bounded_above_of_compact_support hφs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨R, hR, hsupp⟩ : ∃ R : ℝ, 0 < R ∧ tsupport φ ⊆ Metric.ball 0 R := by
    obtain ⟨R₀, hR₀⟩ := hφs.isCompact.isBounded.subset_ball (0 : Rn N)
    exact ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _),
      hR₀.trans (Metric.ball_subset_ball (le_max_left _ _))⟩
  -- Step 2: for `r > 0`, `φ (η_{x,r} y) ≠ 0` forces `y ∈ B_{rR}(x)`.
  have hloc : ∀ r : ℝ, 0 < r → ∀ y, φ (blowUpMap x r y) ≠ 0 → y ∈ Metric.ball x (r * R) := by
    intro r hr y hy
    have h1 : blowUpMap x r y ∈ Metric.ball (0 : Rn N) R := hsupp (subset_tsupport φ hy)
    rw [mem_ball_zero_iff, blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
      inv_mul_lt_iff₀ hr] at h1
    rwa [Metric.mem_ball, dist_eq_norm]
  -- Step 7: `M Rⁿ Q(rR) → 0` as `r ↓ 0`, since `r ↦ rR` maps `𝓝[>] 0` into `𝓝[>] 0`.
  have hmap : Tendsto (fun r : ℝ ↦ r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos hr hR
  have hlim := (hQ.comp hmap).const_mul (M * R ^ n)
  rw [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  -- Steps 3–6: for `0 < r < ρ₁ / R`, `|D(r)| ≤ M Rⁿ Q(rR)`.
  filter_upwards [Ioo_mem_nhdsGT (div_pos hρ₁ hR)] with r hr
  obtain ⟨hr0, hrR⟩ := hr
  have hBmeas : MeasurableSet (Metric.ball x (r * R)) := Metric.isOpen_ball.measurableSet
  have hBfin : μ (Metric.ball x (r * R)) ≠ ∞ :=
    ((measure_mono (Metric.ball_subset_ball ((lt_div_iff₀ hR).1 hrR).le)).trans_lt hμ).ne
  -- Step 4: both integrands are bounded and vanish off `B_{rR}(x)`, hence integrable.
  have hFc : Continuous fun y ↦ φ (blowUpMap x r y) := by
    unfold blowUpMap
    fun_prop
  have hFi : Integrable (fun y ↦ φ (blowUpMap x r y)) μ := by
    refine (integrableOn_iff_integrable_of_support_subset (fun y hy ↦ hloc r hr0 y hy)).1
      (Measure.integrableOn_of_bounded hBfin hFc.aestronglyMeasurable (M := M)
        (Eventually.of_forall fun y ↦ hM _))
  have hIm : AEStronglyMeasurable (fun y ↦ inner ℝ e (ν y)) μ :=
    (continuous_const.inner continuous_id).comp_aestronglyMeasurable hν
  have hGi : Integrable (fun y ↦ φ (blowUpMap x r y) * inner ℝ e (ν y)) μ := by
    refine (integrableOn_iff_integrable_of_support_subset
      (fun y hy ↦ hloc r hr0 y (left_ne_zero_of_mul hy))).1
      (Measure.integrableOn_of_bounded hBfin (hFc.aestronglyMeasurable.mul hIm) (M := M)
        (ae_restrict_of_ae (hν1.mono fun y hy ↦ ?_)))
    rw [norm_mul]
    calc ‖φ (blowUpMap x r y)‖ * ‖inner ℝ e (ν y)‖ ≤ M * (‖e‖ * ‖ν y‖) :=
          mul_le_mul (hM _) (norm_inner_le_norm _ _) (norm_nonneg _) hM0
      _ = M := by rw [he, hy, one_mul, mul_one]
  -- Step 3: `|ν - e|` is integrable on `B_{rR}(x)`.
  have hEi : IntegrableOn (fun y ↦ ‖ν y - e‖) (Metric.ball x (r * R)) μ := by
    refine Measure.integrableOn_of_bounded hBfin (hν.sub aestronglyMeasurable_const).norm (M := 2)
      (ae_restrict_of_ae (hν1.mono fun y hy ↦ ?_))
    rw [norm_norm]
    calc ‖ν y - e‖ ≤ ‖ν y‖ + ‖e‖ := norm_sub_le _ _
      _ = 2 := by rw [hy, he]; norm_num
  -- Step 5: the pointwise bound `|F - G| ≤ 1_{B_{rR}(x)} M |ν - e|`.
  have hpt : ∀ y, ‖φ (blowUpMap x r y) - φ (blowUpMap x r y) * inner ℝ e (ν y)‖ ≤
      (Metric.ball x (r * R)).indicator (fun y ↦ M * ‖ν y - e‖) y := by
    intro y
    by_cases hy : φ (blowUpMap x r y) = 0
    · rw [hy, zero_mul, sub_zero, norm_zero]
      exact Set.indicator_nonneg (fun y _ ↦ mul_nonneg hM0 (norm_nonneg _)) y
    · rw [Set.indicator_of_mem (hloc r hr0 y hy)]
      have hdiff : φ (blowUpMap x r y) - φ (blowUpMap x r y) * inner ℝ e (ν y) =
          φ (blowUpMap x r y) * inner ℝ e (e - ν y) := by
        rw [inner_sub_right, real_inner_self_eq_norm_sq, he]
        ring
      rw [hdiff, norm_mul]
      refine mul_le_mul (hM _) ?_ (norm_nonneg _) hM0
      calc ‖inner ℝ e (e - ν y)‖ ≤ ‖e‖ * ‖e - ν y‖ := norm_inner_le_norm _ _
        _ = ‖ν y - e‖ := by rw [he, one_mul, norm_sub_rev]
  -- Step 6: the estimate `|D(r)| ≤ r⁻ⁿ M ∫_{B_{rR}(x)} |ν - e| dμ = M Rⁿ Q(rR)`.
  have hgi : Integrable ((Metric.ball x (r * R)).indicator fun y ↦ M * ‖ν y - e‖) μ :=
    (integrable_indicator_iff hBmeas).2 (hEi.const_mul M)
  have hrn : 0 < r ^ n := pow_pos hr0 n
  rw [← mul_sub, ← integral_sub hFi hGi, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hrn)]
  calc (r ^ n)⁻¹ * ‖∫ y, φ (blowUpMap x r y) - φ (blowUpMap x r y) * inner ℝ e (ν y) ∂μ‖
      ≤ (r ^ n)⁻¹ * ∫ y, (Metric.ball x (r * R)).indicator (fun y ↦ M * ‖ν y - e‖) y ∂μ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hgi (Eventually.of_forall hpt))
          (inv_pos.2 hrn).le
    _ = M * R ^ n * (((r * R) ^ n)⁻¹ * ∫ y in Metric.ball x (r * R), ‖ν y - e‖ ∂μ) := by
        rw [integral_indicator hBmeas, integral_const_mul, mul_pow, mul_inv]
        field_simp
/-- **Uniform `C¹_c` approximation with support control**: the smoothing step that extends the
blow-up convergence for `C¹_c` test functions to all of `C_c` (the approximation left implicit at
the end of the proof of Simon Ch. 3, Thm. 4.3, `chapter-03.txt` lines 739–746). A continuous
compactly supported `f` vanishing off `B_{R-1}(0)` is uniformly `δ`-approximated by a `C¹_c`
function `φ` vanishing off `B_R(0)`: `φ = κ ⋆ f` with `κ ≥ 0` a `C¹_c` bump of integral `1`
supported in `B_ε(0)`, where `ε ≤ 1/2` is a modulus of uniform continuity of `f` for `δ`. -/
theorem Submission.deGiorgiTM_cc_contDiff_approx : ∀ (N : ℕ) (f : Rn N → ℝ) (R δ : ℝ),
    Continuous f → HasCompactSupport f → (∀ z, f z ≠ 0 → ‖z‖ < R - 1) → 0 < δ →
    ∃ φ : Rn N → ℝ, ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ (∀ z, |φ z - f z| ≤ δ) ∧
      ∀ z, φ z ≠ 0 → ‖z‖ < R := by
  intro N f R δ hfc hfs hfR hδ
  -- Step 1: `f` is uniformly continuous; `ε = min ε₀ (1/2)` for a modulus `ε₀` at `δ`.
  obtain ⟨ε₀, hε₀, hε₀f⟩ :=
    Metric.uniformContinuous_iff.mp (hfs.uniformContinuous_of_continuous hfc) δ hδ
  set ε : ℝ := min ε₀ (1 / 2) with hεdef
  have hεpos : 0 < ε := lt_min hε₀ (by norm_num)
  have hεle₀ : ε ≤ ε₀ := min_le_left _ _
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  -- Step 2: a normalized `C¹` bump `κ = c⁻¹ ψ`, `c = ∫ ψ > 0`, supported in `B_ε(0)`.
  obtain ⟨ψ, hψt, hψcs, hψd, hψr, hψ0⟩ :=
    exists_contDiff_tsupport_subset (n := 1) (Metric.ball_mem_nhds (0 : Rn N) hεpos)
  have hψnn : ∀ t, 0 ≤ ψ t := fun t => (hψr (mem_range_self t)).1
  have hc : 0 < ∫ t, ψ t := hψd.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hψcs
    (fun t => hψnn t) (x := 0) (by rw [hψ0]; exact one_ne_zero)
  set κ : Rn N → ℝ := fun t => (∫ t, ψ t)⁻¹ * ψ t with hκdef
  have hκd : ContDiff ℝ 1 κ := contDiff_const.mul hψd
  have hκsupp' : Function.support κ ⊆ Function.support ψ := fun t ht h0 => ht (by simp [hκdef, h0])
  have hκcs : HasCompactSupport κ := hψcs.mono hκsupp'
  have hκnn : ∀ t, 0 ≤ κ t := fun t => mul_nonneg (inv_nonneg.mpr hc.le) (hψnn t)
  have hκint : ∫ t, κ t = 1 := by
    simp only [hκdef]
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hc.ne'
  have hκsupp : Function.support κ ⊆ Metric.ball (0 : Rn N) ε :=
    fun t ht => hψt (subset_tsupport _ (hκsupp' ht))
  -- Step 3: the mollification `φ = κ ⋆ f` is `C¹` with compact support.
  set φ : Rn N → ℝ := convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume with hφdef
  have hφd : ContDiff ℝ 1 φ := hκcs.contDiff_convolution_left _ hκd hfc.locallyIntegrable
  have hφcs : HasCompactSupport φ := hκcs.convolution _ hfs
  -- Step 4: averaging estimate: `|f - w| ≤ η` on `B_ε(z)` implies `|φ z - w| ≤ η`.
  have avg : ∀ (z : Rn N) (w η : ℝ), 0 ≤ η → (∀ z' ∈ Metric.ball z ε, dist (f z') w ≤ η) →
      dist (φ z) w ≤ η := fun z w η hη h =>
    dist_convolution_le (μ := (volume : Measure (Rn N))) hη hκsupp hκnn hκint
      hfc.aestronglyMeasurable h
  refine ⟨φ, hφd, hφcs, fun z => ?_, fun z hz => ?_⟩
  · -- Step 5: uniform approximation (`w = f z`, `η = δ`).
    have h := avg z (f z) δ hδ.le fun z' hz' =>
      (hε₀f (lt_of_lt_of_le (Metric.mem_ball.mp hz') hεle₀)).le
    rwa [Real.dist_eq] at h
  · -- Step 6: support control: for `‖z‖ ≥ R`, `f = 0` on `B_ε(z)` (there `‖z'‖ > R - 1/2`).
    by_contra hzR
    push Not at hzR
    apply hz
    have h0 : ∀ z' ∈ Metric.ball z ε, dist (f z') 0 ≤ 0 := by
      intro z' hz'
      have hfz' : f z' = 0 := by
        by_contra hne
        have h1 := hfR z' hne
        have h2 := norm_sub_norm_le z z'
        rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hz'
        linarith
      simp [hfz']
    exact dist_le_zero.mp (avg z 0 0 le_rfl h0)
/-- **Integral bound for a bounded continuous function supported in a ball** (the integrability
and estimate step of the proof of Simon Ch. 3, Theorem 4.3, passing from `C¹_c` to `C_c` test
functions). If `ν(B_ρ(a)) < ∞`, `g` is continuous with `|g| ≤ M` and `g` vanishes off
`B_ρ(a)`, then `g` is `ν`-integrable and `|∫ g dν| ≤ M ν(B_ρ(a))`: a bounded continuous function
is integrable on the finite-measure ball, hence on the whole space as its support lies in the
ball, and `∫ g dν = ∫_{B_ρ(a)} g dν` is bounded by `M ν(B_ρ(a))`. -/
theorem Submission.deGiorgiTM_integral_bound_of_ball : ∀ (N : ℕ) (ν : Measure (Rn N)) (a : Rn N) (ρ M : ℝ) (g : Rn N → ℝ), ν (Metric.ball a ρ) < ∞ → Continuous g → (∀ y, |g y| ≤ M) → (∀ y, g y ≠ 0 → y ∈ Metric.ball a ρ) → Integrable g ν ∧ |∫ y, g y ∂ν| ≤ M * ν.real (Metric.ball a ρ) := by
  intro N ν a ρ M g hball hg hM hsupp
  -- `‖g y‖ = |g y| ≤ M` everywhere.
  have hnorm : ∀ y, ‖g y‖ ≤ M := fun y => (Real.norm_eq_abs (g y)).le.trans (hM y)
  -- `g` vanishes off the ball `B_ρ(a)`.
  have hzero : ∀ y, y ∉ Metric.ball a ρ → g y = 0 := fun y hy => by
    by_contra h
    exact hy (hsupp y h)
  -- `g` is bounded and continuous, hence integrable on the finite-measure ball, hence on the
  -- whole space since its support lies in the ball.
  have hint : Integrable g ν :=
    (integrableOn_iff_integrable_of_support_subset fun y hy => hsupp y hy).1
      (Measure.integrableOn_of_bounded hball.ne hg.aestronglyMeasurable
        (Eventually.of_forall hnorm))
  refine ⟨hint, ?_⟩
  -- `∫ g dν = ∫_{B_ρ(a)} g dν`, and `|∫_{B_ρ(a)} g dν| ≤ M ν(B_ρ(a))`.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, ← Real.norm_eq_abs]
  exact norm_setIntegral_le_of_norm_le_const hball fun y _ => hnorm y

/-- **Mass bound for the blow-ups** (Step 3 of the proof of
`Submission.deGiorgiTM_blowUp_tendsto_of_contDiff`: the estimate
`|r⁻ⁿ ∫ (f - φ)(η_{x,r}(y)) dμ(y)| ≤ δ r⁻ⁿ μ(B_{rR}(x)) ≤ δ C Rⁿ`, with the mass bound of
Simon Ch. 3, proof of Theorem 4.3, display (6), `chapter-03.txt` line 648, at `ρ = rR`). Let
`r, R > 0` with `μ(B_{rR}(x)) ≤ C (rR)ⁿ`, and let `h` be continuous with `|h| ≤ M` and `|z| < R`
whenever `h z ≠ 0`. Then `g = h ∘ η_{x,r}` is continuous, bounded by `M` and vanishes off
`B_{rR}(x)`, so by `Submission.deGiorgiTM_integral_bound_of_ball` it is `μ`-integrable with
`|∫ g dμ| ≤ M μ(B_{rR}(x)) ≤ M max(C, 0) (rR)ⁿ` (`C` may be negative); dividing by `rⁿ > 0`
gives `|r⁻ⁿ ∫ g dμ| ≤ M max(C, 0) Rⁿ`. -/
theorem Submission.deGiorgiTM_blowUp_integral_bound : ∀ (N n : ℕ) (μ : Measure (Rn N)) (x : Rn N) (C R r M : ℝ) (h : Rn N → ℝ), 0 < r → 0 < R → μ (Metric.ball x (r * R)) ≤ ENNReal.ofReal (C * (r * R) ^ n) → Continuous h → (∀ z, |h z| ≤ M) → (∀ z, h z ≠ 0 → ‖z‖ < R) → Integrable (fun y ↦ h (blowUpMap x r y)) μ ∧ |(r ^ n)⁻¹ * ∫ y, h (blowUpMap x r y) ∂μ| ≤ M * max C 0 * R ^ n := by
  intro N n μ x C R r M h hr hR hμ hh hM hsupp
  -- Step 1: `g = h ∘ η_{x,r}` is continuous, as `η_{x,r}(y) = r⁻¹ • (y - x)` is affine.
  have hη : Continuous (blowUpMap x r) := (continuous_sub_right x).const_smul r⁻¹
  -- Step 2: `g y ≠ 0` gives `r⁻¹ ‖y - x‖ = ‖η_{x,r}(y)‖ < R`, i.e. `y ∈ B_{rR}(x)`.
  have hgsupp : ∀ y, h (blowUpMap x r y) ≠ 0 → y ∈ Metric.ball x (r * R) := by
    intro y hy
    have hlt := hsupp _ hy
    rw [blowUpMap, norm_smul_of_nonneg (inv_nonneg.2 hr.le), inv_mul_lt_iff₀ hr] at hlt
    exact mem_ball_iff_norm.2 hlt
  -- Step 3: `μ(B_{rR}(x)) ≤ ofReal (C (rR)ⁿ) < ∞`.
  have hfin : μ (Metric.ball x (r * R)) < ∞ := hμ.trans_lt ENNReal.ofReal_lt_top
  -- Step 4: the ball bound gives integrability and `|∫ g dμ| ≤ M μ.real(B_{rR}(x))`.
  obtain ⟨hint, hbound⟩ := Submission.deGiorgiTM_integral_bound_of_ball N μ x (r * R) M
    (fun y ↦ h (blowUpMap x r y)) hfin (hh.comp hη) (fun _ ↦ hM _) hgsupp
  refine ⟨hint, ?_⟩
  -- Step 5: `μ.real(B_{rR}(x)) ≤ max (C (rR)ⁿ) 0 = max C 0 * (rR)ⁿ`, as `(rR)ⁿ ≥ 0`.
  have hreal : μ.real (Metric.ball x (r * R)) ≤ max C 0 * (r * R) ^ n := by
    rw [measureReal_def, max_mul_of_nonneg _ _ (pow_nonneg (mul_pos hr hR).le n), zero_mul,
      ← ENNReal.toReal_ofReal']
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hμ
  -- Step 6: `M ≥ |h 0| ≥ 0`, so `|∫ g dμ| ≤ M max C 0 (rR)ⁿ = rⁿ (M max C 0 Rⁿ)`.
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- Step 7: `(rⁿ)⁻¹ > 0` (also for `n = 0`), and multiplying by it cancels `rⁿ`.
  have hrn : 0 < r ^ n := pow_pos hr n
  rw [abs_mul, abs_of_pos (inv_pos.2 hrn)]
  calc (r ^ n)⁻¹ * |∫ y, h (blowUpMap x r y) ∂μ|
      ≤ (r ^ n)⁻¹ * (r ^ n * (M * max C 0 * R ^ n)) := by
        gcongr
        calc |∫ y, h (blowUpMap x r y) ∂μ| ≤ M * μ.real (Metric.ball x (r * R)) := hbound
          _ ≤ M * (max C 0 * (r * R) ^ n) := by gcongr
          _ = r ^ n * (M * max C 0 * R ^ n) := by ring
    _ = M * max C 0 * R ^ n := inv_mul_cancel_left₀ hrn.ne' _

/-- **From `C¹_c` to `C_c` test functions** (the last step of Simon Ch. 3, proof of Thm. 4.3,
`chapter-03.txt` lines 739–746, with the mass bound (6′)): if `μ(B_ρ(x)) ≤ Cρⁿ` for
`0 < ρ < ρ₁`, `σ` is finite on balls, and `(rⁿ)⁻¹ ∫ φ(η_{x,r}(y)) dμ(y) → ∫ φ dσ` as `r ↓ 0` for
every `φ ∈ C¹_c(ℝᴺ)`, then the same convergence holds for every `f ∈ C_c(ℝᴺ)`. Take `R > 0` with
`f = 0` off `B_{R-1}(0)` and, given `ε > 0`, a `C¹_c` function `φ` with `|φ - f| ≤ δ` and `φ = 0`
off `B_R(0)`, where `δ(C⁺Rⁿ + σ(B_R(0))) < ε/2` and `C⁺ = max(C, 0)`. For `0 < r < ρ₁/R` the
error `d = f - φ` changes the blow-up integral by at most `δC⁺Rⁿ` and `∫ f dσ` by at most
`δσ(B_R(0))`, while the hypothesis for `φ` bounds the remaining error by `ε/2` for small `r`. -/
theorem Submission.deGiorgiTM_blowUp_tendsto_of_contDiff : ∀ (N n : ℕ) (μ σ : Measure (Rn N)) (x : Rn N) (ρ₁ C : ℝ), 0 < ρ₁ → (∀ ρ ∈ Ioo 0 ρ₁, μ (Metric.ball x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ R : ℝ, σ (Metric.ball 0 R) < ∞) → (∀ φ : Rn N → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ y, φ (blowUpMap x r y) ∂μ) (𝓝[>] 0) (𝓝 (∫ y, φ y ∂σ))) → ∀ f : C_c(Rn N, ℝ), Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ y, f (blowUpMap x r y) ∂μ) (𝓝[>] 0) (𝓝 (∫ y, f y ∂σ)) := by
  intro N n μ σ x ρ₁ C hρ₁ hμ hσ hC1 f
  have hfc : Continuous f := map_continuous f
  -- Step 1: a radius `R > 0` with `f = 0` off `B_{R-1}(0)`.
  obtain ⟨R, hRpos, hfR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ z, f z ≠ 0 → ‖z‖ < R - 1 := by
    obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_ball 0
    refine ⟨max R₀ 0 + 1, by positivity, fun z hz ↦ ?_⟩
    rw [add_sub_cancel_right]
    exact (mem_ball_zero_iff.mp (hR₀ (subset_tsupport f hz))).trans_le (le_max_left R₀ 0)
  have hS : 0 ≤ σ.real (Metric.ball 0 R) := measureReal_nonneg
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Step 5: `δ > 0` with `δ (C⁺Rⁿ + σ(B_R(0))) < ε / 2`, `C⁺ = max C 0`.
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧
      δ * (max C 0 * R ^ n + σ.real (Metric.ball 0 R)) < ε / 2 := by
    have hA : 0 ≤ max C 0 * R ^ n + σ.real (Metric.ball 0 R) := by positivity
    generalize max C 0 * R ^ n + σ.real (Metric.ball 0 R) = A at hA ⊢
    refine ⟨ε / (2 * (A + 1)), by positivity, ?_⟩
    calc ε / (2 * (A + 1)) * A < ε / (2 * (A + 1)) * (A + 1) :=
          mul_lt_mul_of_pos_left (lt_add_one A) (by positivity)
      _ = ε / 2 := by field_simp
  -- Step 2: a `C¹_c` function `φ` with `|φ - f| ≤ δ`, and the error `d = f - φ`; both vanish
  -- off `B_R(0)`.
  obtain ⟨φ, hφ, hφc, hφf, hφR⟩ :=
    Submission.deGiorgiTM_cc_contDiff_approx N f R δ hfc f.hasCompactSupport hfR hδ
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hφM : ∀ z, |φ z| ≤ M := fun z ↦ by simpa only [Real.norm_eq_abs] using hM z
  set d : Rn N → ℝ := fun z ↦ f z - φ z with hd
  have hdc : Continuous d := hfc.sub hφ.continuous
  have hdδ : ∀ z, |d z| ≤ δ := fun z ↦ (abs_sub_comm (f z) (φ z)).trans_le (hφf z)
  have hdR : ∀ z, d z ≠ 0 → ‖z‖ < R := by
    intro z hz
    by_contra hzR
    have hf0 : f z = 0 := by
      by_contra h
      exact hzR ((hfR z h).trans (sub_lt_self R one_pos))
    have hφ0 : φ z = 0 := by
      by_contra h
      exact hzR (hφR z h)
    exact hz (show f z - φ z = 0 by rw [hf0, hφ0, sub_zero])
  have hfdφ : ∀ z, f z = d z + φ z := fun z ↦ (sub_add_cancel (f z) (φ z)).symm
  -- Step 4: `d` and `φ` are `σ`-integrable and `|∫ d dσ| ≤ δ σ(B_R(0))`.
  obtain ⟨hdσ, hdσb⟩ := Submission.deGiorgiTM_integral_bound_of_ball N σ 0 R δ d (hσ R) hdc
    hdδ fun y hy ↦ mem_ball_zero_iff.mpr (hdR y hy)
  obtain ⟨hφσ, -⟩ := Submission.deGiorgiTM_integral_bound_of_ball N σ 0 R M φ (hσ R)
    hφ.continuous hφM fun y hy ↦ mem_ball_zero_iff.mpr (hφR y hy)
  have hsplitσ : ∫ y, f y ∂σ = ∫ y, d y ∂σ + ∫ y, φ y ∂σ := by
    rw [← integral_add hdσ hφσ]
    congr 1
    ext y
    exact hfdφ y
  -- Step 5: for `0 < r < ρ₁ / R` close to `0`, combine the hypothesis for `φ` with the bounds.
  filter_upwards [Metric.tendsto_nhds.mp (hC1 φ hφ hφc) (ε / 2) (half_pos hε),
    Ioo_mem_nhdsGT (div_pos hρ₁ hRpos)] with r hr hrI
  have hr0 : 0 < r := hrI.1
  have hμr : μ (Metric.ball x (r * R)) ≤ ENNReal.ofReal (C * (r * R) ^ n) :=
    hμ (r * R) ⟨mul_pos hr0 hRpos, (lt_div_iff₀ hRpos).mp hrI.2⟩
  -- Step 3: `d ∘ η_{x,r}` and `φ ∘ η_{x,r}` are `μ`-integrable and
  -- `|(rⁿ)⁻¹ ∫ d(η_{x,r}(y)) dμ(y)| ≤ δ C⁺ Rⁿ`.
  obtain ⟨hdμ, hdμb⟩ :=
    Submission.deGiorgiTM_blowUp_integral_bound N n μ x C R r δ d hr0 hRpos hμr hdc hdδ hdR
  obtain ⟨hφμ, -⟩ := Submission.deGiorgiTM_blowUp_integral_bound N n μ x C R r M φ hr0 hRpos hμr
    hφ.continuous hφM hφR
  have hsplitμ : ∫ y, f (blowUpMap x r y) ∂μ =
      ∫ y, d (blowUpMap x r y) ∂μ + ∫ y, φ (blowUpMap x r y) ∂μ := by
    rw [← integral_add hdμ hφμ]
    congr 1
    ext y
    exact hfdφ _
  have hr' : |(r ^ n)⁻¹ * ∫ y, φ (blowUpMap x r y) ∂μ - ∫ y, φ y ∂σ| < ε / 2 := by
    simpa only [Real.dist_eq] using hr
  show dist ((r ^ n)⁻¹ * ∫ y, f (blowUpMap x r y) ∂μ) (∫ y, f y ∂σ) < ε
  rw [Real.dist_eq, hsplitμ, hsplitσ, abs_lt]
  obtain ⟨h₁, h₂⟩ := abs_le.mp hdμb
  obtain ⟨h₃, h₄⟩ := abs_lt.mp hr'
  obtain ⟨h₅, h₆⟩ := abs_le.mp hdσb
  constructor <;> linarith
/-- **Blow-up images of sets under `η_{x,r}`**: the change of variables `y ↦ r⁻¹ (y - x)` of
Simon Ch. 3, proof of Theorem 4.3, display (8) (`chapter-03.txt` lines 662–667), for a general
centre `x`. Write `η_{x,r}` as the translation `y ↦ y - x`, which preserves `Lᴺ`, followed by the
dilation `z ↦ r⁻¹ z`, which multiplies `Lᴺ` by `|r⁻ᴺ|` (`addHaar_smul`). Then `η_{x,r}` maps
null-measurable sets to null-measurable sets for every `r` (including `r = 0`, where `r⁻¹ = 0`),
and multiplies `Lᴺ` by `r⁻ᴺ` when `r > 0`. For `r > 0` it is injective with
`η_{x,r}(B_{rR}(x)) = B_R(0)`, so it commutes with `∩` and `\`, giving the two ball identities. -/
theorem Submission.deGiorgiHS_blowUpMap_image_volume : ∀ (N : ℕ) (x : Rn N) (r : ℝ) (A : Set (Rn N)), (NullMeasurableSet A volume → NullMeasurableSet (blowUpMap x r '' A) volume) ∧ (0 < r → volume (blowUpMap x r '' A) = ENNReal.ofReal ((r ^ N)⁻¹) * volume A ∧ ∀ R : ℝ, blowUpMap x r '' A ∩ Metric.ball 0 R = blowUpMap x r '' (A ∩ Metric.ball x (r * R)) ∧ Metric.ball 0 R \ blowUpMap x r '' A = blowUpMap x r '' (Metric.ball x (r * R) \ A)) := by
  intro N x r A
  -- Step 1: `η(A) = r⁻¹ • τ⁻¹(A)` for the translation `τ z = z + x`.
  have himage : blowUpMap x r '' A = (fun z ↦ r⁻¹ • z) '' ((fun z ↦ z + x) ⁻¹' A) := by
    have htrans : (fun y ↦ y - x) '' A = (fun z ↦ z + x) ⁻¹' A := by
      ext z
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hz
        exact ⟨z + x, hz, by simp⟩
    rw [← htrans, Set.image_image]
    rfl
  refine ⟨fun hA ↦ ?_, fun hr ↦ ⟨?_, fun R ↦ ?_⟩⟩
  · -- Step 3: `τ` is measure preserving, and dilations preserve null-measurability.
    rw [himage, Set.image_smul]
    exact Measure.NullMeasurableSet.const_smul
      (hA.preimage (measurePreserving_add_right volume x).quasiMeasurePreserving) _
  · -- Step 4: `Lᴺ(r⁻¹ • S) = |r⁻ᴺ| Lᴺ(S)` and `Lᴺ(τ⁻¹(A)) = Lᴺ(A)`.
    rw [himage, Set.image_smul, Measure.addHaar_smul, measure_preimage_add_right,
      finrank_euclideanSpace_fin, inv_pow, abs_of_pos (by positivity)]
  · -- Steps 5–7: `η` is injective and `η(B_{rR}(x)) = B_R(0)`.
    have hinj : Function.Injective (blowUpMap x r) := by
      intro y₁ y₂ h
      simp only [blowUpMap] at h
      exact sub_left_injective (smul_right_injective (Rn N) (inv_ne_zero hr.ne') h)
    have hball : blowUpMap x r '' Metric.ball x (r * R) = Metric.ball 0 R := by
      ext z
      simp only [Set.mem_image, Metric.mem_ball, dist_eq_norm, sub_zero, blowUpMap]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_lt_iff₀ hr]
        exact hy
      · intro hz
        refine ⟨x + r • z, ?_, ?_⟩
        · rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
          exact mul_lt_mul_of_pos_left hz hr
        · rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    rw [← hball, Set.image_inter hinj, Set.image_sdiff hinj]
    exact ⟨rfl, rfl⟩
/-- **`L¹_loc` convergence of sets passes to integrals and volumes** (the passage from
`χ_{ρ_k⁻¹E} → χ_F` in `L¹_loc` to (7) in the proof of Simon Ch. 3, Theorem 4.3). Let `F_k`, `G`
be `Lᴺ`-measurable subsets of `ℝᴺ` with `Lᴺ(K ∩ (F_k Δ G)) → 0` for every compact `K`. Then
`∫_{F_k} f → ∫_G f` for every continuous compactly supported `f`, and for every bounded `B`,
`Lᴺ(F_k ∩ B) → Lᴺ(G ∩ B)` and `Lᴺ(B ∖ F_k) → Lᴺ(B ∖ G)`. -/
theorem Submission.deGiorgiHS_L1loc_limit_transfer : ∀ (N : ℕ) (F : ℕ → Set (Rn N)) (G : Set (Rn N)), (∀ k, NullMeasurableSet (F k) volume) → NullMeasurableSet G volume → (∀ K : Set (Rn N), IsCompact K → Tendsto (fun k ↦ volume (K ∩ symmDiff (F k) G)) atTop (𝓝 0)) → (∀ f : Rn N → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k ↦ ∫ y in F k, f y) atTop (𝓝 (∫ y in G, f y))) ∧ ∀ B : Set (Rn N), Bornology.IsBounded B → Tendsto (fun k ↦ volume (F k ∩ B)) atTop (𝓝 (volume (G ∩ B))) ∧ Tendsto (fun k ↦ volume (B \ F k)) atTop (𝓝 (volume (B \ G))) := by
  intro N F G hF hG hK
  -- Squeeze in `ℝ≥0∞`: `a - d k ≤ u k ≤ a + d k`, `d k → 0` and `a ≠ ∞` give `u k → a`.
  have squeeze : ∀ {u d : ℕ → ℝ≥0∞} {a : ℝ≥0∞}, a ≠ ∞ → Tendsto d atTop (𝓝 0) →
      (∀ k, u k ≤ a + d k) → (∀ k, a ≤ u k + d k) → Tendsto u atTop (𝓝 a) := by
    intro u d a ha hd h1 h2
    have hup : Tendsto (fun k ↦ a + d k) atTop (𝓝 a) := by
      have := (tendsto_const_nhds (x := a)).add hd
      rwa [add_zero] at this
    have hlow : Tendsto (fun k ↦ a - d k) atTop (𝓝 a) := by
      have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := a)) hd (Or.inl ha)
      rwa [tsub_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup
      (fun k ↦ tsub_le_iff_right.mpr (h2 k)) h1
  refine ⟨fun f hf hfc ↦ ?_, fun B hB ↦ ?_⟩
  · -- (i): `|∫_{F k} f - ∫_G f| ≤ Lᴺ(tsupport f ∩ (F k Δ G)) M → 0` with `|f| ≤ M`.
    obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
    have hfi : Integrable f volume := hf.integrable_of_hasCompactSupport hfc
    have hbound : ∀ k, ‖(∫ y in F k, f y) - ∫ y in G, f y‖ ≤
        (volume (tsupport f ∩ symmDiff (F k) G)).toReal * M := by
      intro k
      have hS : NullMeasurableSet (tsupport f ∩ symmDiff (F k) G) volume :=
        (isClosed_tsupport f).measurableSet.nullMeasurableSet.inter ((hF k).symmDiff hG)
      have hSfin : volume (tsupport f ∩ symmDiff (F k) G) ≠ ∞ :=
        ((measure_mono inter_subset_left).trans_lt hfc.isCompact.measure_lt_top).ne
      have hgi : Integrable ((tsupport f ∩ symmDiff (F k) G).indicator fun _ ↦ M) volume :=
        (integrableOn_const hSfin).integrable_indicator₀ hS
      -- Pointwise `|(1_{F k} - 1_G) f| ≤ M 1_{tsupport f ∩ (F k Δ G)}`.
      have hpt : ∀ x, ‖(F k).indicator f x - G.indicator f x‖ ≤
          (tsupport f ∩ symmDiff (F k) G).indicator (fun _ ↦ M) x := by
        intro x
        by_cases hxK : x ∈ tsupport f
        · have hMx : |f x| ≤ M := by simpa [Real.norm_eq_abs] using hM x
          by_cases hxF : x ∈ F k <;> by_cases hxG : x ∈ G <;>
            simp [Set.mem_symmDiff, hxF, hxG, hxK, hMx]
        · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport hxK
          have h1 : (F k).indicator f x = 0 := Set.indicator_apply_eq_zero.mpr fun _ ↦ hfx
          have h2 : G.indicator f x = 0 := Set.indicator_apply_eq_zero.mpr fun _ ↦ hfx
          have h3 : (tsupport f ∩ symmDiff (F k) G).indicator (fun _ ↦ M) x = 0 :=
            Set.indicator_of_notMem (fun h ↦ hxK h.1) _
          simp [h1, h2, h3]
      rw [← integral_indicator₀ (hF k), ← integral_indicator₀ hG,
        ← integral_sub (hfi.indicator₀ (hF k)) (hfi.indicator₀ hG)]
      calc ‖∫ y, ((F k).indicator f y - G.indicator f y)‖
          ≤ ∫ y, (tsupport f ∩ symmDiff (F k) G).indicator (fun _ ↦ M) y :=
            norm_integral_le_of_norm_le hgi (Eventually.of_forall hpt)
        _ = (volume (tsupport f ∩ symmDiff (F k) G)).toReal * M := by
            rw [integral_indicator₀ hS, setIntegral_const, smul_eq_mul, measureReal_def]
    have hd : Tendsto (fun k ↦ (volume (tsupport f ∩ symmDiff (F k) G)).toReal * M) atTop
        (𝓝 0) := by
      have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hK (tsupport f) hfc.isCompact)
      rw [ENNReal.toReal_zero] at h0
      have := h0.mul_const M
      rwa [zero_mul] at this
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun k ↦ norm_nonneg _) hbound hd
  · -- (ii): two-sided inclusions up to `closure B ∩ (F k Δ G)`, `closure B` compact.
    have hKc : IsCompact (closure B) := hB.isCompact_closure
    have hd := hK (closure B) hKc
    have hfin : ∀ S ⊆ closure B, volume S ≠ ∞ := fun S hS ↦
      ((measure_mono hS).trans_lt hKc.measure_lt_top).ne
    refine ⟨squeeze (hfin _ (inter_subset_right.trans subset_closure)) hd (fun k ↦ ?_)
      (fun k ↦ ?_), squeeze (hfin _ (Set.sdiff_subset.trans subset_closure)) hd (fun k ↦ ?_)
      (fun k ↦ ?_)⟩
    · have hsub : F k ∩ B ⊆ (G ∩ B) ∪ (closure B ∩ symmDiff (F k) G) := by
        intro x hx
        by_cases hxG : x ∈ G
        · exact Or.inl ⟨hxG, hx.2⟩
        · exact Or.inr ⟨subset_closure hx.2, Set.mem_symmDiff.mpr (Or.inl ⟨hx.1, hxG⟩)⟩
      exact (measure_mono hsub).trans (measure_union_le _ _)
    · have hsub : G ∩ B ⊆ (F k ∩ B) ∪ (closure B ∩ symmDiff (F k) G) := by
        intro x hx
        by_cases hxF : x ∈ F k
        · exact Or.inl ⟨hxF, hx.2⟩
        · exact Or.inr ⟨subset_closure hx.2, Set.mem_symmDiff.mpr (Or.inr ⟨hx.1, hxF⟩)⟩
      exact (measure_mono hsub).trans (measure_union_le _ _)
    · have hsub : B \ F k ⊆ (B \ G) ∪ (closure B ∩ symmDiff (F k) G) := by
        intro x hx
        by_cases hxG : x ∈ G
        · exact Or.inr ⟨subset_closure hx.1, Set.mem_symmDiff.mpr (Or.inr ⟨hxG, hx.2⟩)⟩
        · exact Or.inl ⟨hx.1, hxG⟩
      exact (measure_mono hsub).trans (measure_union_le _ _)
    · have hsub : B \ G ⊆ (B \ F k) ∪ (closure B ∩ symmDiff (F k) G) := by
        intro x hx
        by_cases hxF : x ∈ F k
        · exact Or.inr ⟨subset_closure hx.1, Set.mem_symmDiff.mpr (Or.inl ⟨hxF, hx.2⟩)⟩
        · exact Or.inl ⟨hx.1, hxF⟩
      exact (measure_mono hsub).trans (measure_union_le _ _)
/-- **Uniform perimeter bound for the blow-ups** (parent proof, Step 2(a); Simon Ch. 3, proof of
Theorem 4.3, `chapter-03.txt` lines 653–656, from the mass bound (6)). Let `|ν| = 1` `μ`-a.e.,
assume the mass bound (M) `μ(B_ρ(x)) ≤ C ρⁿ` for `ρ ∈ (0, ρ₁)` and the blow-up Gauss–Green
identity (I) `∫_{η_{x,r}(E)} div g = -(rⁿ)⁻¹ ∫ ⟨g ∘ η_{x,r}, ν⟩ dμ` for `C¹` fields `g` with
compact support in `B_R(0)`, `r R < ρ₁`. Then every such `g` with `|g| ≤ 1` satisfies
`∫_{η_{x,r}(E)} div g ≤ max(C, 0) Rⁿ`:
1. `ρ := r R ∈ (0, ρ₁)`, so `μ(B_ρ(x)) ≤ C ρⁿ < ∞` by (M);
2. `g ∘ η_{x,r}` vanishes off `B_ρ(x)`, since there `|η_{x,r}(y)| = r⁻¹ |y - x| ≥ R`;
3. hence `|⟨g ∘ η_{x,r}, ν⟩| ≤ 1_{B_ρ(x)}` `μ`-a.e. (Cauchy–Schwarz, `|g| ≤ 1`, `|ν| = 1`), so
   `|∫ ⟨g ∘ η_{x,r}, ν⟩ dμ| ≤ μ(B_ρ(x)) ≤ max(C, 0) ρⁿ` (also when the pairing is not
   integrable, its Bochner integral then being `0`);
4. by (I), `∫_{η_{x,r}(E)} div g ≤ (rⁿ)⁻¹ max(C, 0) (r R)ⁿ = max(C, 0) Rⁿ`. -/
theorem Submission.deGiorgiHS_blowUp_divergence_bound : ∀ (N n : ℕ) (E : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N) (x : Rn N) (ρ₁ C : ℝ), (∀ᵐ y ∂μ, ‖ν y‖ = 1) → (∀ ρ ∈ Ioo 0 ρ₁, μ (Metric.ball x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ r R : ℝ, 0 < r → 0 < R → r * R < ρ₁ → ∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ Metric.ball 0 R → ∫ z in blowUpMap x r '' E, Poincare.SimonGMT.Chapter02.euclideanDivergence g z = -((r ^ n)⁻¹ * ∫ y, inner ℝ (g (blowUpMap x r y)) (ν y) ∂μ)) → ∀ r R : ℝ, 0 < r → 0 < R → r * R < ρ₁ → ∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ Metric.ball 0 R → (∀ y, ‖g y‖ ≤ 1) → ∫ z in blowUpMap x r '' E, Poincare.SimonGMT.Chapter02.euclideanDivergence g z ≤ max C 0 * R ^ n := by
  intro N n E μ ν x ρ₁ C hν hM hI r R hr hR hrR g hg hgc hgs hg1
  rw [hI r R hr hR hrR g hg hgc hgs]
  -- Step 1: `ρ := r R ∈ (0, ρ₁)`, so `B := B_ρ(x)` has finite mass `μ(B) ≤ C ρⁿ` by (M).
  have hρ : 0 < r * R := mul_pos hr hR
  have hμB : μ (Metric.ball x (r * R)) ≤ ENNReal.ofReal (C * (r * R) ^ n) := hM (r * R) ⟨hρ, hrR⟩
  have hμB_ne_top : μ (Metric.ball x (r * R)) ≠ ∞ := (hμB.trans_lt ENNReal.ofReal_lt_top).ne
  -- Step 2: off `B`, `|η(y)| = r⁻¹ |y - x| ≥ R`, so `η(y) ∉ tsupport g` and `g (η y) = 0`.
  have hzero : ∀ y ∉ Metric.ball x (r * R), g (blowUpMap x r y) = 0 := by
    intro y hy
    refine image_eq_zero_of_notMem_tsupport fun hmem ↦ hy ?_
    have h1 := hgs hmem
    rw [mem_ball_zero_iff] at h1
    simp only [blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at h1
    rw [Metric.mem_ball, dist_eq_norm]
    exact (inv_mul_lt_iff₀ hr).1 h1
  -- Step 3: `|⟨g (η y), ν y⟩| ≤ 1_B(y)` whenever `|ν y| = 1`, i.e. `μ`-a.e.
  have hbound : ∀ᵐ y ∂μ, ‖inner ℝ (g (blowUpMap x r y)) (ν y)‖ ≤
      (Metric.ball x (r * R)).indicator (1 : Rn N → ℝ) y := by
    filter_upwards [hν] with y hy
    by_cases hyB : y ∈ Metric.ball x (r * R)
    · rw [Set.indicator_of_mem hyB, Pi.one_apply]
      calc ‖inner ℝ (g (blowUpMap x r y)) (ν y)‖ ≤ ‖g (blowUpMap x r y)‖ * ‖ν y‖ :=
            norm_inner_le_norm _ _
        _ ≤ 1 := by rw [hy, mul_one]; exact hg1 _
    · rw [Set.indicator_of_notMem hyB, hzero y hyB, inner_zero_left, norm_zero]
  -- Step 4: `1_B` is integrable with integral `μ(B)`, which bounds the norm of the Bochner
  -- integral of the pairing (integrable or not).
  have hint : Integrable ((Metric.ball x (r * R)).indicator (1 : Rn N → ℝ)) μ :=
    (integrableOn_const hμB_ne_top).integrable_indicator measurableSet_ball
  have hpair : ‖∫ y, inner ℝ (g (blowUpMap x r y)) (ν y) ∂μ‖ ≤ μ.real (Metric.ball x (r * R)) :=
    (norm_integral_le_of_norm_le hint hbound).trans_eq (integral_indicator_one measurableSet_ball)
  -- Step 5: `μ(B) ≤ max(C ρⁿ, 0) ≤ max(C, 0) ρⁿ` as real numbers, since `ρⁿ > 0`.
  have hρn : 0 < (r * R) ^ n := pow_pos hρ n
  have hmass : μ.real (Metric.ball x (r * R)) ≤ max C 0 * (r * R) ^ n := by
    rw [measureReal_def]
    calc (μ (Metric.ball x (r * R))).toReal ≤ (ENNReal.ofReal (C * (r * R) ^ n)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hμB
      _ = max (C * (r * R) ^ n) 0 := ENNReal.toReal_ofReal'
      _ ≤ max C 0 * (r * R) ^ n :=
          max_le (mul_le_mul_of_nonneg_right (le_max_left C 0) hρn.le)
            (mul_nonneg (le_max_right C 0) hρn.le)
  -- Step 6: by (I), `∫_{η(E)} div g = -(rⁿ)⁻¹ ∫ ⟨g ∘ η, ν⟩ dμ ≤ (rⁿ)⁻¹ max(C, 0) (r R)ⁿ`.
  have hrn : 0 < r ^ n := pow_pos hr n
  calc -((r ^ n)⁻¹ * ∫ y, inner ℝ (g (blowUpMap x r y)) (ν y) ∂μ)
      = (r ^ n)⁻¹ * -∫ y, inner ℝ (g (blowUpMap x r y)) (ν y) ∂μ := (mul_neg _ _).symm
    _ ≤ (r ^ n)⁻¹ * (max C 0 * (r * R) ^ n) :=
        mul_le_mul_of_nonneg_left
          ((neg_le_abs _).trans ((Real.norm_eq_abs _).symm.le.trans (hpair.trans hmass)))
          (inv_nonneg.2 hrn.le)
    _ = max C 0 * ((r ^ n)⁻¹ * r ^ n) * R ^ n := by rw [mul_pow]; ring
    _ = max C 0 * R ^ n := by rw [inv_mul_cancel₀ hrn.ne', mul_one]
/-- **Directional limits of the blow-ups**: Simon Ch. 3, proof of Theorem 4.3, display (8) and the
display after it, with the sign corrected for `ζ ≥ 0` (`chapter-03.txt` lines 662–686), at a
general point `x` and unit vector `e`. Testing the blow-up identity (I) with `g = ζ • w`, whose
divergence is `D_w ζ`, gives `∫_{η_r(E)} D_w ζ = -(rⁿ)⁻¹ ∫ ζ(η_r(y)) ⟨w, ν(y)⟩ dμ(y)`, where
`ζ ∘ η_r` vanishes off `B_{rR}(x)` once `tsupport ζ ⊆ B_R(0)`. For `⟨v, e⟩ = 0` we have
`⟨v, ν⟩ = ⟨v, ν - e⟩`, and for `ζ ≥ 0` we have `-ζ ⟨e, ν⟩ ≤ M |ν - e|`; in both cases the
integral is bounded by a constant times `Rⁿ ε(rR)`, where `ε(ρ) = (ρⁿ)⁻¹ ∫_{B_ρ(x)} |ν - e| dμ`,
and this bound tends to `0` as `r ↓ 0` by (X). -/
theorem Submission.deGiorgiHS_blowUp_directional_limits : ∀ (N n : ℕ) (E : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N) (x e : Rn N) (ρ₁ : ℝ), AEStronglyMeasurable ν μ → (∀ᵐ y ∂μ, ‖ν y‖ = 1) → ‖e‖ = 1 → 0 < ρ₁ → (∀ ρ ∈ Ioo 0 ρ₁, μ (Metric.ball x ρ) < ∞) → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ y in Metric.ball x ρ, ‖ν y - e‖ ∂μ) (𝓝[>] 0) (𝓝 0) → (∀ r R : ℝ, 0 < r → 0 < R → r * R < ρ₁ → ∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ Metric.ball 0 R → ∫ z in blowUpMap x r '' E, Poincare.SimonGMT.Chapter02.euclideanDivergence g z = -((r ^ n)⁻¹ * ∫ y, inner ℝ (g (blowUpMap x r y)) (ν y) ∂μ)) → (∀ (ζ : Rn N → ℝ) (v : Rn N), ContDiff ℝ 1 ζ → HasCompactSupport ζ → inner ℝ v e = 0 → Tendsto (fun r : ℝ ↦ ∫ z in blowUpMap x r '' E, fderiv ℝ ζ z v) (𝓝[>] 0) (𝓝 0)) ∧ ∀ ζ : Rn N → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ y, 0 ≤ ζ y) → ∀ δ : ℝ, 0 < δ → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∫ z in blowUpMap x r '' E, fderiv ℝ ζ z e ≤ δ := by
  intro N n E μ ν x e ρ₁ hν hν1 he hρ₁ hF hX hI
  -- The divergence of the rank-one field `z ↦ ζ z • w` is the directional derivative `D_w ζ`.
  have hdiv : ∀ ζ : Rn N → ℝ, Differentiable ℝ ζ → ∀ w z : Rn N,
      Poincare.SimonGMT.Chapter02.euclideanDivergence (fun z ↦ ζ z • w) z = fderiv ℝ ζ z w := by
    intro ζ hζ w z
    rw [Poincare.SimonGMT.Chapter02.euclideanDivergence_eq_sum_inner
      (stdOrthonormalBasis ℝ (Rn N)), fderiv_smul_const (hζ z)]
    simp only [ContinuousLinearMap.smulRight_apply, real_inner_smul_right]
    conv_rhs => rw [← (stdOrthonormalBasis ℝ (Rn N)).sum_repr' w]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  -- `r ↦ r * R` maps `𝓝[>] 0` to `𝓝[>] 0` when `0 < R`.
  have hscale : ∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ ↦ r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    intro R hR
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Tendsto (fun r : ℝ ↦ r * R) (𝓝 0) (𝓝 (0 * R)) := tendsto_id.mul_const R
      rw [zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hR
  -- Points outside `B_{rR}(x)` are blown up outside `B_R(0)`.
  have hout : ∀ (y : Rn N) (r R : ℝ), 0 < r → y ∉ Metric.ball x (r * R) →
      blowUpMap x r y ∉ Metric.ball (0 : Rn N) R := by
    intro y r R hr hy h
    apply hy
    rw [Metric.mem_ball, dist_zero_right] at h
    rw [Metric.mem_ball, dist_eq_norm]
    unfold blowUpMap at h
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, inv_mul_lt_iff₀ hr] at h
    exact h
  -- The identity (★) on the window `r ∈ (0, ρ₁ / R)`, with the integrability it needs.
  have key : ∀ ζ : Rn N → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      ∃ R > 0, ∃ M : ℝ, (∀ z, ‖ζ z‖ ≤ M) ∧ ∀ r ∈ Ioo 0 (ρ₁ / R), ∀ w : Rn N,
        IntegrableOn (fun y ↦ ‖ν y - e‖) (Metric.ball x (r * R)) μ ∧
        IntegrableOn (fun y ↦ ζ (blowUpMap x r y) * inner ℝ w (ν y)) (Metric.ball x (r * R)) μ ∧
        ∫ z in blowUpMap x r '' E, fderiv ℝ ζ z w =
          -((r ^ n)⁻¹ * ∫ y in Metric.ball x (r * R), ζ (blowUpMap x r y) * inner ℝ w (ν y) ∂μ) := by
    intro ζ hζ hζc
    obtain ⟨R, hR, hRsub⟩ := hζc.isCompact.isBounded.subset_ball_lt 0 (0 : Rn N)
    obtain ⟨M, hM⟩ := hζ.continuous.bounded_above_of_compact_support hζc
    refine ⟨R, hR, M, hM, fun r hr w ↦ ?_⟩
    have hr0 : 0 < r := hr.1
    have hrR : r * R < ρ₁ := (lt_div_iff₀ hR).1 hr.2
    have hB : μ (Metric.ball x (r * R)) ≠ ∞ := (hF _ ⟨mul_pos hr0 hR, hrR⟩).ne
    have hη : Continuous (blowUpMap x r) := by
      unfold blowUpMap
      fun_prop
    refine ⟨?_, ?_, ?_⟩
    · refine Measure.integrableOn_of_bounded (M := 2) hB (hν.sub aestronglyMeasurable_const).norm ?_
      filter_upwards [ae_restrict_of_ae hν1] with y hy
      rw [norm_norm]
      calc ‖ν y - e‖ ≤ ‖ν y‖ + ‖e‖ := norm_sub_le _ _
        _ = 2 := by rw [hy, he]; norm_num
    · refine Measure.integrableOn_of_bounded (M := M * ‖w‖) hB
        ((hζ.continuous.comp hη).aestronglyMeasurable.mul
          ((Continuous.inner (𝕜 := ℝ) continuous_const continuous_id).comp_aestronglyMeasurable
            hν)) ?_
      filter_upwards [ae_restrict_of_ae hν1] with y hy
      rw [norm_mul]
      calc ‖ζ (blowUpMap x r y)‖ * ‖inner ℝ w (ν y)‖ ≤ M * (‖w‖ * ‖ν y‖) :=
            mul_le_mul (hM _) (norm_inner_le_norm _ _) (norm_nonneg _) ((norm_nonneg _).trans (hM 0))
        _ = M * ‖w‖ := by rw [hy, mul_one]
    · have hI' := hI r R hr0 hR hrR (fun z ↦ ζ z • w) (hζ.smul contDiff_const)
        (hζc.smul_right (f' := fun _ : Rn N ↦ w))
        ((tsupport_smul_subset_left ζ (fun _ ↦ w)).trans hRsub)
      have hdiff : Differentiable ℝ ζ := hζ.differentiable one_ne_zero
      simp only [hdiv ζ hdiff, real_inner_smul_left] at hI'
      rw [hI', setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro y hy
      have h0 : ζ (blowUpMap x r y) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hout y r R hr0 hy (hRsub h))
      simp [h0]
  refine ⟨?_, ?_⟩
  · -- (H): horizontal directions.
    intro ζ v hζ hζc hve
    obtain ⟨R, hR, M, hM, hkey⟩ := key ζ hζ hζc
    have hlim : Tendsto (fun r : ℝ ↦ M * ‖v‖ * R ^ n *
        (((r * R) ^ n)⁻¹ * ∫ y in Metric.ball x (r * R), ‖ν y - e‖ ∂μ)) (𝓝[>] 0) (𝓝 0) := by
      have h := (hX.comp (hscale R hR)).const_mul (M * ‖v‖ * R ^ n)
      rw [mul_zero] at h
      exact h
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Ioo_mem_nhdsGT (div_pos hρ₁ hR)] with r hr
    obtain ⟨hi1, -, heq⟩ := hkey r hr v
    have hr0 : 0 < r := hr.1
    have hle : ‖∫ y in Metric.ball x (r * R), ζ (blowUpMap x r y) * inner ℝ v (ν y) ∂μ‖ ≤
        M * ‖v‖ * ∫ y in Metric.ball x (r * R), ‖ν y - e‖ ∂μ := by
      rw [← integral_const_mul]
      refine norm_integral_le_of_norm_le (Integrable.const_mul hi1 _) ?_
      filter_upwards with y
      have h1 : inner ℝ v (ν y) = inner ℝ v (ν y - e) := by rw [inner_sub_right, hve, sub_zero]
      rw [norm_mul, h1, mul_assoc]
      exact mul_le_mul (hM _) (norm_inner_le_norm _ _) (norm_nonneg _)
        ((norm_nonneg _).trans (hM 0))
    rw [heq, norm_neg, norm_mul, norm_inv, norm_pow, Real.norm_of_nonneg hr0.le]
    calc (r ^ n)⁻¹ * ‖∫ y in Metric.ball x (r * R), ζ (blowUpMap x r y) * inner ℝ v (ν y) ∂μ‖
        ≤ (r ^ n)⁻¹ * (M * ‖v‖ * ∫ y in Metric.ball x (r * R), ‖ν y - e‖ ∂μ) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.2 (pow_nonneg hr0.le n))
      _ = M * ‖v‖ * R ^ n * (((r * R) ^ n)⁻¹ * ∫ y in Metric.ball x (r * R), ‖ν y - e‖ ∂μ) := by
        have hRn : R ^ n ≠ 0 := pow_ne_zero _ hR.ne'
        have hrn : r ^ n ≠ 0 := pow_ne_zero _ hr0.ne'
        rw [mul_pow]
        field_simp
  · -- (M): the normal direction, sign-corrected.
    intro ζ hζ hζc hζ0 δ hδ
    obtain ⟨R, hR, M, hM, hkey⟩ := key ζ hζ hζc
    have hlim : Tendsto (fun r : ℝ ↦ M * R ^ n *
        (((r * R) ^ n)⁻¹ * ∫ y in Metric.ball x (r * R), ‖ν y - e‖ ∂μ)) (𝓝[>] 0) (𝓝 0) := by
      have h := (hX.comp (hscale R hR)).const_mul (M * R ^ n)
      rw [mul_zero] at h
      exact h
    filter_upwards [Ioo_mem_nhdsGT (div_pos hρ₁ hR), (tendsto_order.1 hlim).2 δ hδ] with r hr hlt
    refine le_trans ?_ hlt.le
    obtain ⟨hi1, hi2, heq⟩ := hkey r hr e
    have hr0 : 0 < r := hr.1
    have hle : -∫ y in Metric.ball x (r * R), ζ (blowUpMap x r y) * inner ℝ e (ν y) ∂μ ≤
        M * ∫ y in Metric.ball x (r * R), ‖ν y - e‖ ∂μ := by
      rw [← integral_neg, ← integral_const_mul]
      refine integral_mono_ae hi2.neg (Integrable.const_mul hi1 M) ?_
      filter_upwards with y
      have h1 : inner ℝ e (ν y) = 1 + inner ℝ e (ν y - e) := by
        rw [inner_sub_right, real_inner_self_eq_norm_sq, he]; ring
      have h2 : -inner ℝ e (ν y - e) ≤ ‖ν y - e‖ := by
        have h := abs_real_inner_le_norm e (ν y - e)
        rw [he, one_mul] at h
        exact (neg_le_abs _).trans h
      have h3 : ζ (blowUpMap x r y) ≤ M := (Real.le_norm_self _).trans (hM _)
      have h4 := hζ0 (blowUpMap x r y)
      rw [h1]
      nlinarith [mul_nonneg h4 (by linarith : 0 ≤ ‖ν y - e‖ + inner ℝ e (ν y - e)),
        mul_nonneg (sub_nonneg.2 h3) (norm_nonneg (ν y - e))]
    rw [heq]
    calc -((r ^ n)⁻¹ * ∫ y in Metric.ball x (r * R), ζ (blowUpMap x r y) * inner ℝ e (ν y) ∂μ)
        = (r ^ n)⁻¹ * -∫ y in Metric.ball x (r * R), ζ (blowUpMap x r y) * inner ℝ e (ν y) ∂μ := by
          ring
      _ ≤ (r ^ n)⁻¹ * (M * ∫ y in Metric.ball x (r * R), ‖ν y - e‖ ∂μ) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.2 (pow_nonneg hr0.le n))
      _ = M * R ^ n * (((r * R) ^ n)⁻¹ * ∫ y in Metric.ball x (r * R), ‖ν y - e‖ ∂μ) := by
        have hRn : R ^ n ≠ 0 := pow_ne_zero _ hR.ne'
        have hrn : r ^ n ≠ 0 := pow_ne_zero _ hr0.ne'
        rw [mul_pow]
        field_simp
/-- **Gauss–Green identity for the blow-ups `η_{x,r}(E)`** (Simon Ch. 3, proof of Theorem 4.3,
display (8), `chapter-03.txt` lines 662–667): for a Gauss–Green pair `(μ, ν)` of `(U, E)`, `r > 0`
and `g ∈ C¹_c(ℝ^{n+1}; ℝ^{n+1})` with `tsupport g ⊆ η_{x,r}(U)`,
`∫_{η_{x,r}(E)} div g dL^{n+1} = -r⁻ⁿ ∫ g(η_{x,r}(y)) · ν(y) dμ(y)`. Apply (4.1) to
`h = g ∘ η_{x,r}` (`C¹`, compactly supported in `U`, `div h = r⁻¹ (div g) ∘ η_{x,r}`) and change
variables `z = η_{x,r}(y)`: `η_{x,r}` pushes `L^{n+1}` forward to `r^{n+1} L^{n+1}`. -/
theorem Submission.deGiorgi_blowUp_gaussGreen_identity : ∀ (n : ℕ) (U E : Set (Rn (n + 1))) (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)) (x : Rn (n + 1)) (r : ℝ), IsOpen U → NullMeasurableSet E volume → IsGaussGreenPair U E μ ν → 0 < r → ∀ g : Rn (n + 1) → Rn (n + 1), ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ blowUpMap x r '' U → ∫ z in blowUpMap x r '' E, Poincare.SimonGMT.Chapter02.euclideanDivergence g z = -((r ^ n)⁻¹ * ∫ y, inner ℝ (g (blowUpMap x r y)) (ν y) ∂μ) := by
  intro n U E μ ν x r hU _ hGG hr g hg hgc hgU
  obtain ⟨-, -, -, -, hGG⟩ := hGG
  -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)`, as a homeomorphism and as a measurable equivalence.
  set φ : Rn (n + 1) ≃ₜ Rn (n + 1) :=
    (Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  set e : Rn (n + 1) ≃ᵐ Rn (n + 1) :=
    (MeasurableEquiv.subRight x).trans (MeasurableEquiv.smul₀ r⁻¹ (inv_ne_zero hr.ne'))
  have he : ⇑e = blowUpMap x r := rfl
  -- Step 1: `h = g ∘ η` is `C¹`, compactly supported, and `tsupport h ⊆ η⁻¹(η(U)) = U`.
  have hcd : ContDiff ℝ 1 (g ∘ blowUpMap x r) :=
    hg.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)
  have hcs : HasCompactSupport (g ∘ blowUpMap x r) := hgc.comp_homeomorph φ
  have hts : tsupport (g ∘ blowUpMap x r) ⊆ U := by
    refine (tsupport_comp_subset_preimage g φ.continuous).trans fun y hy ↦ ?_
    obtain ⟨u, hu, huy⟩ := hgU (show φ y ∈ tsupport g from hy)
    exact φ.injective huy ▸ hu
  -- Step 2: `D h(y) = r⁻¹ D g(η y)`, so `div h = r⁻¹ (div g) ∘ η`.
  have hη : ∀ y, HasFDerivAt (blowUpMap x r) (r⁻¹ • ContinuousLinearMap.id ℝ (Rn (n + 1))) y :=
    fun y ↦ ((hasFDerivAt_id y).sub_const x).const_smul r⁻¹
  have hdiv : ∀ y, Poincare.SimonGMT.Chapter02.euclideanDivergence (g ∘ blowUpMap x r) y =
      r⁻¹ * Poincare.SimonGMT.Chapter02.euclideanDivergence g (blowUpMap x r y) := by
    intro y
    have hd := ((hg.differentiable one_ne_zero) (blowUpMap x r y)).hasFDerivAt.comp y (hη y)
    rw [Poincare.SimonGMT.Chapter02.euclideanDivergence, hd.fderiv, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_id, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul]
    rfl
  -- Steps 3–4: (4.1) for `h`. As `div h` vanishes off `tsupport h ⊆ U`, `E ∩ U` may be replaced
  -- by `E` (Step 6, done here before the change of variables instead of after it).
  have hGG' : ∫ y in E ∩ U, Poincare.SimonGMT.Chapter02.euclideanDivergence (g ∘ blowUpMap x r) y =
      -∫ y, inner ℝ (g (blowUpMap x r y)) (ν y) ∂μ := hGG _ hcd hcs hts
  have hEU : ∫ y in E ∩ U, Poincare.SimonGMT.Chapter02.euclideanDivergence (g ∘ blowUpMap x r) y =
      ∫ y in E, Poincare.SimonGMT.Chapter02.euclideanDivergence (g ∘ blowUpMap x r) y := by
    rw [← setIntegral_indicator hU.measurableSet, Set.indicator_eq_self.2
      ((Poincare.SimonGMT.Chapter02.support_euclideanDivergence_subset _).trans hts)]
  -- Step 5: change of variables; `L^{n+1}(η⁻¹(T)) = L^{n+1}(r • T + x) = r^{n+1} L^{n+1}(T)`.
  have hmap : (volume : Measure (Rn (n + 1))).map e = ENNReal.ofReal (r ^ (n + 1)) • volume := by
    ext T -
    have hT : ⇑e ⁻¹' T = (fun y ↦ y + -x) ⁻¹' ((fun z ↦ r⁻¹ • z) ⁻¹' T) := by
      ext y
      simp [he, blowUpMap, sub_eq_add_neg]
    rw [e.map_apply, Measure.smul_apply, hT, measure_preimage_add_right,
      Set.preimage_smul_inv₀ hr.ne', Measure.addHaar_smul, finrank_euclideanSpace_fin,
      abs_of_pos (pow_pos hr _), smul_eq_mul]
  have hres : ((volume : Measure (Rn (n + 1))).restrict E).map e =
      ENNReal.ofReal (r ^ (n + 1)) • (volume : Measure (Rn (n + 1))).restrict (e '' E) := by
    rw [← Measure.restrict_smul, ← hmap, e.restrict_map, e.preimage_image]
  have hcov : ∫ y in E, Poincare.SimonGMT.Chapter02.euclideanDivergence g (blowUpMap x r y) =
      r ^ (n + 1) *
        ∫ z in blowUpMap x r '' E, Poincare.SimonGMT.Chapter02.euclideanDivergence g z := by
    rw [← he, ← integral_map_equiv, hres, integral_smul_measure,
      ENNReal.toReal_ofReal (pow_pos hr _).le, smul_eq_mul]
  -- Step 7: `rⁿ ∫_{η(E)} div g = -∫ g(η y) · ν(y) dμ(y)`; divide by `rⁿ > 0`.
  have hmain : r ^ n * ∫ z in blowUpMap x r '' E,
      Poincare.SimonGMT.Chapter02.euclideanDivergence g z =
        -∫ y, inner ℝ (g (blowUpMap x r y)) (ν y) ∂μ := by
    rw [← hGG', hEU]
    simp only [hdiv]
    rw [integral_const_mul, hcov, ← mul_assoc, pow_succ', ← mul_assoc, inv_mul_cancel₀ hr.ne',
      one_mul]
  rw [neg_mul_eq_mul_neg, ← hmain, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hr.ne'), one_mul]
/-- **Basic facts at a reduced-boundary point** (Steps 1 and 4 of the normal-average bounds in the
proof of Simon Ch. 3, Theorem 4.3; definition (4.2) of `∂*E`, `chapter-03.txt` lines 576–580, and
of `ν_E(x)` in 4.3, lines 588–596). If `x ∈ ∂*E`, then `x ∈ U` and the averages
`A(ρ) = μ(B_ρ(x))⁻¹ ∫_{B_ρ(x)} ν dμ` tend to some `v` with `|v| = 1` as `ρ ↓ 0`; by uniqueness
of limits along the nontrivial filter `𝓝[>] 0`, `ν_E(x) = limUnder A = v`. If `μ(B_ρ(x)) = 0`
for some `ρ > 0`, then `μ(B_r(x)) = 0` and `A(r) = 0⁻¹ • ∫ ν = 0` for `r ∈ (0, ρ)`, so `A → 0`
and `v = 0`, contradicting `|v| = 1`. -/
theorem Submission.deGiorgiNAB_reducedBoundary_basic : ∀ (N : ℕ) (U : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), ∀ x ∈ reducedBoundary U μ ν, x ∈ U ∧ ‖reducedNormal μ ν x‖ = 1 ∧ Tendsto (normalAverage μ ν x) (𝓝[>] 0) (𝓝 (reducedNormal μ ν x)) ∧ ∀ ρ : ℝ, 0 < ρ → 0 < μ (Metric.ball x ρ) := by
  intro N U μ ν x hx
  -- Step 1: `x ∈ U` and `A → v` along `𝓝[>] 0` with `‖v‖ = 1`.
  obtain ⟨hxU, v, hv, hv1⟩ := hx
  -- Steps 2–3: `ν_E(x) = limUnder A = v` (`𝓝[>] 0` is nontrivial and `ℝᴺ` is Hausdorff).
  have he : reducedNormal μ ν x = v := hv.limUnder_eq
  refine ⟨hxU, he ▸ hv1, he ▸ hv, fun ρ hρ ↦ pos_iff_ne_zero.2 fun h0 ↦ ?_⟩
  -- Step 4: if `μ(B_ρ(x)) = 0`, then `A = 0` on `(0, ρ)`, so `v = 0`, contradicting `‖v‖ = 1`.
  have hA : normalAverage μ ν x =ᶠ[𝓝[>] 0] fun _ ↦ 0 := by
    filter_upwards [Ioo_mem_nhdsGT hρ] with r hr
    rw [normalAverage, measure_mono_null (Metric.ball_subset_ball hr.2.le) h0,
      ENNReal.toReal_zero, inv_zero, zero_smul]
  have hv0 : v = 0 := tendsto_nhds_unique_of_eventuallyEq hv tendsto_const_nhds hA
  simp [hv0] at hv1
/-- **Cauchy–Schwarz bound for the normal excess on a set of finite measure** (Simon Ch. 3, proof
of Theorem 4.3, display (2)). Let `ν` be `μ`-a.e. strongly measurable with `|ν| = 1` `μ`-a.e., let
`|e| = 1`, and let `S ⊆ ℝᴺ` be any set with `μ(S) < ∞`; put `m = μ(S)` and `I = ∫_S ⟨ν, e⟩ dμ`.
Then `∫_S |ν − e| dμ ≤ m √(2(1 − m⁻¹ I))`. A.e. on `S`, `|ν − e|² = 2 − 2⟨ν, e⟩`, so
`∫_S |ν − e|² dμ = 2(m − I)`; with `J = ∫_S |ν − e| dμ`, expanding `0 ≤ ∫_S (|ν − e| − J/m)² dμ`
gives `J² ≤ 2m(m − I)` (Cauchy–Schwarz), and `√(2m(m − I)) = m √(2(1 − m⁻¹ I))` for `m > 0`. For
`m = 0` both sides vanish. -/
theorem Submission.deGiorgiNAB_excess_le_sqrt : ∀ (N : ℕ) (μ : Measure (Rn N)) (ν : Rn N → Rn N) (e : Rn N) (S : Set (Rn N)), μ S < ∞ → AEStronglyMeasurable ν μ → (∀ᵐ y ∂μ, ‖ν y‖ = 1) → ‖e‖ = 1 → ∫ y in S, ‖ν y - e‖ ∂μ ≤ (μ S).toReal * Real.sqrt (2 * (1 - (μ S).toReal⁻¹ * ∫ y in S, inner ℝ (ν y) e ∂μ)) := by
  intro N μ ν e S hS hν hν1 he
  -- Step 1: `μ ⌞ S` is a finite measure, for which `ν` is a.e. strongly measurable with `|ν| = 1`.
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hS.ne
  have hνS : ∀ᵐ y ∂(μ.restrict S), ‖ν y‖ = 1 := ae_restrict_of_ae hν1
  have hνm : AEStronglyMeasurable ν (μ.restrict S) := hν.restrict
  -- Step 2: `|ν − e| ≤ 2`, `|ν − e|² ≤ 4` and `|⟨ν, e⟩| ≤ 1` a.e., so all three are integrable.
  have hf_meas : AEStronglyMeasurable (fun y ↦ ‖ν y - e‖) (μ.restrict S) :=
    (hνm.sub aestronglyMeasurable_const).norm
  have hf_bd : ∀ᵐ y ∂(μ.restrict S), ‖ν y - e‖ ≤ 2 := by
    filter_upwards [hνS] with y hy
    calc ‖ν y - e‖ ≤ ‖ν y‖ + ‖e‖ := norm_sub_le _ _
      _ = 2 := by rw [hy, he]; norm_num
  have hf_int : Integrable (fun y ↦ ‖ν y - e‖) (μ.restrict S) := by
    refine Integrable.of_bound hf_meas 2 ?_
    filter_upwards [hf_bd] with y hy
    rwa [Real.norm_of_nonneg (norm_nonneg _)]
  have hf2_int : Integrable (fun y ↦ ‖ν y - e‖ ^ 2) (μ.restrict S) := by
    refine Integrable.of_bound (hf_meas.pow 2) 4 ?_
    filter_upwards [hf_bd] with y hy
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [norm_nonneg (ν y - e)]
  have hg_int : Integrable (fun y ↦ inner ℝ (ν y) e) (μ.restrict S) := by
    refine Integrable.of_bound ((continuous_id.inner continuous_const).comp_aestronglyMeasurable
      (g := fun v : Rn N ↦ inner ℝ v e) hνm) 1 ?_
    filter_upwards [hνS] with y hy
    calc ‖inner ℝ (ν y) e‖ ≤ ‖ν y‖ * ‖e‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [hy, he]; norm_num
  set m := (μ S).toReal
  set I := ∫ y in S, inner ℝ (ν y) e ∂μ
  set J := ∫ y in S, ‖ν y - e‖ ∂μ
  have hreal : (μ.restrict S).real univ = m := by
    simp [measureReal_def, m]
  -- Step 3: a.e. `|ν − e|² = 2 − 2⟨ν, e⟩`, hence `∫_S |ν − e|² dμ = 2(m − I)`.
  have hK : ∫ y in S, ‖ν y - e‖ ^ 2 ∂μ = 2 * (m - I) := by
    have hae : (fun y ↦ ‖ν y - e‖ ^ 2) =ᵐ[μ.restrict S] fun y ↦ 2 - 2 * inner ℝ (ν y) e := by
      filter_upwards [hνS] with y hy
      rw [norm_sub_sq_real, hy, he]; ring
    rw [integral_congr_ae hae, integral_sub (integrable_const _) (hg_int.const_mul 2),
      integral_const_mul, integral_const, hreal, smul_eq_mul]
    ring
  have hJnn : 0 ≤ J := integral_nonneg fun y ↦ norm_nonneg _
  by_cases hm0 : m = 0
  · -- Step 4: `m = 0` forces `μ(S) = 0`, so `J = 0` and the right-hand side is `0`.
    have hS0 : μ S = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).mp hm0 with h | h
      · exact h
      · exact absurd h hS.ne
    have hres : μ.restrict S = 0 := Measure.restrict_eq_zero.mpr hS0
    have hJ0 : J = 0 := by simp [J, hres]
    rw [hJ0, hm0, zero_mul]
  · have hmpos : 0 < m := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hm0)
    -- Step 5: `0 ≤ ∫_S (|ν − e| − J/m)² dμ = 2(m − I) − J²/m`, i.e. `J² ≤ m · 2(m − I)`.
    have hCS : J ^ 2 ≤ m * (2 * (m - I)) := by
      have h0 : 0 ≤ ∫ y in S, (‖ν y - e‖ - J / m) ^ 2 ∂μ := integral_nonneg fun y ↦ sq_nonneg _
      have hexp : ∫ y in S, (‖ν y - e‖ - J / m) ^ 2 ∂μ =
          2 * (m - I) - 2 * (J / m) * J + (J / m) ^ 2 * m := by
        have hfun : (fun y ↦ (‖ν y - e‖ - J / m) ^ 2) =
            fun y ↦ (‖ν y - e‖ ^ 2 - 2 * (J / m) * ‖ν y - e‖) + (J / m) ^ 2 := by
          ext y; ring
        have h1 : Integrable (fun y ↦ ‖ν y - e‖ ^ 2 - 2 * (J / m) * ‖ν y - e‖) (μ.restrict S) :=
          hf2_int.sub (hf_int.const_mul _)
        rw [hfun, integral_add h1 (integrable_const _),
          integral_sub hf2_int (hf_int.const_mul _), integral_const_mul, integral_const, hreal,
          hK, smul_eq_mul]
        ring
      rw [hexp] at h0
      have hJm : (J / m) ^ 2 * m = J ^ 2 / m := by field_simp
      have h2 : 2 * (J / m) * J = 2 * (J ^ 2 / m) := by field_simp
      rw [hJm, h2] at h0
      have h3 : J ^ 2 / m ≤ 2 * (m - I) := by linarith
      rwa [div_le_iff₀ hmpos, mul_comm] at h3
    -- Step 6: `J = √(J²) ≤ √(m² · 2(1 − m⁻¹ I)) = m √(2(1 − m⁻¹ I))`.
    calc J = Real.sqrt (J ^ 2) := (Real.sqrt_sq hJnn).symm
      _ ≤ Real.sqrt (m * (2 * (m - I))) := Real.sqrt_le_sqrt hCS
      _ = m * Real.sqrt (2 * (1 - m⁻¹ * I)) := by
        rw [show m * (2 * (m - I)) = m ^ 2 * (2 * (1 - m⁻¹ * I)) by field_simp,
          Real.sqrt_mul (sq_nonneg m), Real.sqrt_sq hmpos.le]

/-- **Scalar normal averages at a reduced-boundary point** (Simon Ch. 3, proof of Theorem 4.3,
display (1), `chapter-03.txt` lines 607–614). Let `μ` be finite on compact subsets of the open set
`U`, `|ν| = 1` `μ`-a.e., `x ∈ ∂*E` and `e = ν_E(x)`. Then
`μ(B_ρ(x))⁻¹ ∫_{B_ρ(x)} ν · e dμ → 1` as `ρ ↓ 0` (with `0⁻¹ = 0`). For `ρ` below the radius of a
compact ball `B̄_r(x) ⊆ U`, `ν` is integrable on `B_ρ(x)`, so the functional `w ↦ e · w` commutes
with the integral and the scalar average is `A(ρ) · e` for `A(ρ) = normalAverage μ ν x ρ`; since
`A(ρ) → e` and `|e| = 1`, `A(ρ) · e → e · e = 1`. -/
theorem Submission.deGiorgiNAB_innerAverage_tendsto_one : ∀ (N : ℕ) (U : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ν μ → (∀ᵐ y ∂μ, ‖ν y‖ = 1) → ∀ x ∈ reducedBoundary U μ ν, Tendsto (fun ρ : ℝ ↦ (μ (Metric.ball x ρ)).toReal⁻¹ * ∫ y in Metric.ball x ρ, inner ℝ (ν y) (reducedNormal μ ν x) ∂μ) (𝓝[>] 0) (𝓝 1) := by
  intro N U μ ν hU hfin hν hν1 x hx
  -- `x ∈ U`, `|e| = 1` and `A(ρ) → e`.
  obtain ⟨hxU, he, hA, -⟩ := Submission.deGiorgiNAB_reducedBoundary_basic N U μ ν x hx
  set e := reducedNormal μ ν x
  -- A compact ball `B̄_{ε/2}(x) ⊆ U`, so that `μ(B_ρ(x)) < ∞` for `ρ ≤ ε / 2`.
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hxU
  have hrU : Metric.closedBall x (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hfinr : μ (Metric.closedBall x (ε / 2)) < ∞ := hfin _ (isCompact_closedBall x _) hrU
  -- `A(ρ) · e → e · e = |e|² = 1`.
  have hlim : Tendsto (fun ρ ↦ inner ℝ (normalAverage μ ν x ρ) e) (𝓝[>] 0)
      (𝓝 (inner ℝ e e)) := hA.inner tendsto_const_nhds
  rw [real_inner_self_eq_norm_sq, he, one_pow] at hlim
  -- On `(0, ε / 2)` the scalar average equals `A(ρ) · e`.
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (half_pos hε)] with ρ hρ
  have hfinρ : μ (Metric.ball x ρ) < ∞ := (measure_mono (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall hρ.2.le))).trans_lt hfinr
  -- `ν` is integrable on `B_ρ(x)`: `|ν| ≤ 1` a.e. on a set of finite measure.
  have hint : IntegrableOn ν (Metric.ball x ρ) μ :=
    IntegrableOn.of_bound hfinρ hν.restrict 1 ((ae_restrict_of_ae hν1).mono fun y hy ↦ hy.le)
  -- The continuous linear functional `w ↦ e · w` commutes with the integral.
  have hcomm : ∫ y in Metric.ball x ρ, inner ℝ (ν y) e ∂μ =
      inner ℝ (∫ y in Metric.ball x ρ, ν y ∂μ) e := by
    simpa only [innerSL_apply_apply, real_inner_comm e] using
      (innerSL ℝ e).integral_comp_comm hint
  rw [normalAverage, real_inner_smul_left, hcomm]

/-- **Normal averages at a reduced-boundary point** (Simon Ch. 3, proof of Theorem 4.3, displays
(1) and (2), `chapter-03.txt` lines 604–620). Let `μ` be finite on compact subsets of the open set
`U`, `|ν| = 1` `μ`-a.e., `x ∈ ∂*E` and `e = ν_E(x)`. Then `|e| = 1`; there is `ρ₀ > 0` with
`B_{ρ₀}(x) ⊆ U` and `0 < μ(B_ρ(x)) ≤ 2 ∫_{B_ρ(x)} ν · e dμ` for `0 < ρ < ρ₀`; and if
`μ(B_ρ(x)) ≤ C ρⁿ` for small `ρ`, then `ρ⁻ⁿ ∫_{B_ρ(x)} |ν - e| dμ → 0` as `ρ ↓ 0`.
With `a(ρ) = μ(B_ρ(x))⁻¹ ∫_{B_ρ(x)} ν · e dμ`, (1) says `a(ρ) → 1`, so `a > 1/2` near `0`; and by
Cauchy–Schwarz (2), `∫_{B_ρ(x)} |ν - e| dμ ≤ μ(B_ρ(x)) √(2 (1 - a(ρ)))`, which is at most
`max(C, 0) ρⁿ √(2 (1 - a(ρ)))` and squeezes `ρ⁻ⁿ ∫_{B_ρ(x)} |ν - e| dμ` to `0`. -/
theorem Submission.deGiorgiDens_normalAverage_bounds : ∀ (N : ℕ) (U : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ν μ → (∀ᵐ y ∂μ, ‖ν y‖ = 1) → ∀ x ∈ reducedBoundary U μ ν, ‖reducedNormal μ ν x‖ = 1 ∧ (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ Metric.ball x ρ₀ ⊆ U ∧ ∀ ρ ∈ Ioo 0 ρ₀, 0 < μ (Metric.ball x ρ) ∧ (μ (Metric.ball x ρ)).toReal ≤ 2 * ∫ y in Metric.ball x ρ, inner ℝ (ν y) (reducedNormal μ ν x) ∂μ) ∧ ∀ (n : ℕ) (C ρ₂ : ℝ), 0 < ρ₂ → (∀ ρ ∈ Ioo 0 ρ₂, μ (Metric.ball x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ y in Metric.ball x ρ, ‖ν y - reducedNormal μ ν x‖ ∂μ) (𝓝[>] 0) (𝓝 0) := by
  intro N U μ ν hU hfin hν hν1 x hx
  -- `x ∈ U`, `|e| = 1` and `μ(B_ρ(x)) > 0` for every `ρ > 0`; Simon (1): `a(ρ) → 1`.
  obtain ⟨hxU, he, -, hpos⟩ := Submission.deGiorgiNAB_reducedBoundary_basic N U μ ν x hx
  have ha := Submission.deGiorgiNAB_innerAverage_tendsto_one N U μ ν hU hfin hν hν1 x hx
  set e := reducedNormal μ ν x
  -- A compact ball `B̄_{ε/2}(x) ⊆ U`, so that `μ(B_ρ(x)) < ∞` for `ρ ≤ ε / 2`.
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hxU
  have hr : 0 < ε / 2 := half_pos hε
  have hrU : Metric.closedBall x (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hfinρ : ∀ ρ ≤ ε / 2, μ (Metric.ball x ρ) < ∞ := fun ρ hρ ↦
    (measure_mono (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall hρ))).trans_lt (hfin _ (isCompact_closedBall x _) hrU)
  refine ⟨he, ?_, ?_⟩
  · -- `a > 1/2` on some `(0, δ)`; take `ρ₀ = min δ (ε / 2)`.
    obtain ⟨δ, hδ, hδa⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
      (ha.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1))
    refine ⟨min δ (ε / 2), lt_min hδ hr, (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (min_le_right _ _))).trans hrU,
      fun ρ hρ ↦ ⟨hpos ρ hρ.1, ?_⟩⟩
    have h12 : 1 / 2 <
        (μ (Metric.ball x ρ)).toReal⁻¹ * ∫ y in Metric.ball x ρ, inner ℝ (ν y) e ∂μ :=
      hδa ⟨hρ.1, hρ.2.trans_le (min_le_left _ _)⟩
    have hm : 0 < (μ (Metric.ball x ρ)).toReal :=
      ENNReal.toReal_pos (hpos ρ hρ.1).ne' (hfinρ ρ (hρ.2.le.trans (min_le_right _ _))).ne
    rw [lt_inv_mul_iff₀ hm] at h12
    linarith
  · -- Simon (2) and `μ(B_ρ(x)) ≤ max(C, 0) ρⁿ` squeeze the scaled excess to `0`.
    intro n C ρ₂ hρ₂ hmass
    have hup : Tendsto (fun ρ : ℝ ↦ max C 0 * Real.sqrt (2 * (1 - (μ (Metric.ball x ρ)).toReal⁻¹ *
        ∫ y in Metric.ball x ρ, inner ℝ (ν y) e ∂μ))) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous fun t : ℝ ↦ max C 0 * Real.sqrt (2 * (1 - t)) := by fun_prop
      exact (hc.tendsto' 1 0 (by simp)).comp ha
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
      exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hρ.le n)) (integral_nonneg fun y ↦ norm_nonneg _)
    · filter_upwards [Ioo_mem_nhdsGT (lt_min hρ₂ hr)] with ρ hρ
      have hρn : 0 < ρ ^ n := pow_pos hρ.1 n
      have hm : (μ (Metric.ball x ρ)).toReal ≤ max C 0 * ρ ^ n :=
        calc (μ (Metric.ball x ρ)).toReal ≤ (ENNReal.ofReal (C * ρ ^ n)).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_ne_top
                (hmass ρ ⟨hρ.1, hρ.2.trans_le (min_le_left _ _)⟩)
          _ = max C 0 * ρ ^ n := by
              rw [ENNReal.toReal_ofReal', max_mul_of_nonneg _ _ hρn.le, zero_mul]
      have hB := Submission.deGiorgiNAB_excess_le_sqrt N μ ν e (Metric.ball x ρ)
        (hfinρ ρ (hρ.2.le.trans (min_le_right _ _))) hν hν1 he
      calc (ρ ^ n)⁻¹ * ∫ y in Metric.ball x ρ, ‖ν y - e‖ ∂μ
          ≤ (ρ ^ n)⁻¹ * (max C 0 * ρ ^ n * Real.sqrt (2 * (1 - (μ (Metric.ball x ρ)).toReal⁻¹ *
              ∫ y in Metric.ball x ρ, inner ℝ (ν y) e ∂μ))) :=
            mul_le_mul_of_nonneg_left
              (hB.trans (mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg _)))
              (inv_nonneg.mpr hρn.le)
        _ = max C 0 * Real.sqrt (2 * (1 - (μ (Metric.ball x ρ)).toReal⁻¹ *
              ∫ y in Metric.ball x ρ, inner ℝ (ν y) e ∂μ)) := by
            rw [mul_comm (max C 0), mul_assoc, inv_mul_cancel_left₀ hρn.ne']
/-- **Radial cut-off between `B_s(x)` and `B_ρ(x)`** (Simon Ch. 3, proof of Thm. 4.3, (4)
(p. 82, `chapter-03.txt` lines 631–637), with `ρ − 1/k` replaced by any `s ∈ (0, ρ)`).
`ζ(y) = min{1, max{0, (ρ − |y − x|)/(ρ − s)}}` is `(ρ − s)⁻¹`-Lipschitz, `0 ≤ ζ ≤ 1`, `ζ = 1`
on `B_s(x)` and `ζ = 0` off `B_ρ(x)`. `Dζ = 0` on `B_s(x)` and off `B̄_ρ(x)`; on the open annulus
`‖Dζ‖ = (ρ − s)⁻¹` (`≤` by the Lipschitz bound, `≥` since the derivative in the direction
`v = y − x` is `−|v|/(ρ − s)`). The two spheres are Lebesgue-null (empty if `N = 0`), so
`‖Dζ‖ = (ρ − s)⁻¹ 1_{B_ρ(x) ∖ B_s(x)}` a.e., and integrating over `G` gives
`(L^N(G ∩ B_ρ(x)) − L^N(G ∩ B_s(x)))/(ρ − s)`. -/
theorem Submission.deGiorgiDens_radial_cutoff : ∀ (N : ℕ) (x : Rn N) (s ρ : ℝ), 0 < s → s < ρ → ∃ ζ : Rn N → ℝ, (∃ K : ℝ≥0, LipschitzWith K ζ) ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ Metric.closedBall x ρ ∧ (∀ y, 0 ≤ ζ y ∧ ζ y ≤ 1) ∧ (∀ y ∈ Metric.ball x s, ζ y = 1) ∧ (∀ y ∉ Metric.ball x ρ, ζ y = 0) ∧ ∀ G : Set (Rn N), NullMeasurableSet G volume → ∫ y in G, ‖fderiv ℝ ζ y‖ = ((volume (G ∩ Metric.ball x ρ)).toReal - (volume (G ∩ Metric.ball x s)).toReal) / (ρ - s) := by
  intro N x s ρ hs hsρ
  have hc : 0 < ρ - s := sub_pos.mpr hsρ
  -- Step 1: `ζ = min 1 (max 0 ((ρ - |y - x|)/(ρ - s)))` is `(ρ - s)⁻¹`-Lipschitz.
  set K : ℝ≥0 := ⟨(ρ - s)⁻¹, (inv_pos.mpr hc).le⟩ with hK
  set ζ : Rn N → ℝ := fun y ↦ min 1 (max 0 ((ρ - dist y x) / (ρ - s))) with hζ
  have hlip : LipschitzWith K ζ := by
    have hg : LipschitzWith K fun y : Rn N ↦ (ρ - dist y x) / (ρ - s) := by
      refine LipschitzWith.of_dist_le_mul fun a b ↦ ?_
      rw [Real.dist_eq, show (ρ - dist a x) / (ρ - s) - (ρ - dist b x) / (ρ - s) =
        (ρ - s)⁻¹ * (dist b x - dist a x) by ring, abs_mul, abs_of_pos (inv_pos.mpr hc)]
      exact mul_le_mul_of_nonneg_left ((abs_dist_sub_le b a x).trans_eq (dist_comm b a))
        (inv_pos.mpr hc).le
    exact (hg.const_max 0).const_min 1
  -- Step 2: values and support.
  have hone : ∀ y : Rn N, dist y x < s → ζ y = 1 := by
    intro y hy
    have h1 : 1 ≤ (ρ - dist y x) / (ρ - s) := by
      rw [le_div_iff₀ hc]; linarith
    exact min_eq_left (le_max_of_le_right h1)
  have hzero : ∀ y : Rn N, ρ ≤ dist y x → ζ y = 0 := by
    intro y hy
    have h1 : (ρ - dist y x) / (ρ - s) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le
    simp only [hζ, max_eq_left h1, min_eq_right zero_le_one]
  have hval : ∀ y, 0 ≤ ζ y ∧ ζ y ≤ 1 := fun y ↦
    ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  have hout : ∀ y ∉ Metric.ball x ρ, ζ y = 0 := fun y hy ↦
    hzero y (not_lt.mp (mt Metric.mem_ball.mpr hy))
  have htsupp : tsupport ζ ⊆ Metric.closedBall x ρ := by
    refine closure_minimal (fun y hy ↦ ?_) Metric.isClosed_closedBall
    by_contra hyρ
    exact (Function.mem_support.mp hy) (hout y fun hb ↦ hyρ (Metric.ball_subset_closedBall hb))
  -- Step 3: off the spheres `{|y - x| = s}`, `{|y - x| = ρ}`, `|Dζ| = (ρ - s)⁻¹ 1_{B_ρ ∖ B_s}`.
  have hcont : Continuous fun z : Rn N ↦ dist z x := continuous_id.dist continuous_const
  have hpt : ∀ y : Rn N, dist y x ≠ s → dist y x ≠ ρ →
      ‖fderiv ℝ ζ y‖ = (Metric.ball x ρ \ Metric.ball x s).indicator (fun _ ↦ (ρ - s)⁻¹) y := by
    intro y hys hyρ
    rcases lt_or_gt_of_ne hys with h1 | h1
    · -- in `B_s(x)`, `ζ ≡ 1` near `y`
      have hev : ∀ᶠ z in 𝓝 y, dist z x < s := (hcont.tendsto y).eventually (gt_mem_nhds h1)
      have hEq : ζ =ᶠ[𝓝 y] fun _ ↦ (1 : ℝ) := by
        filter_upwards [hev] with z hz using hone z hz
      have hnA : y ∉ Metric.ball x ρ \ Metric.ball x s := fun h ↦ h.2 (Metric.mem_ball.mpr h1)
      rw [Set.indicator_of_notMem hnA, hEq.fderiv_eq, fderiv_const_apply, norm_zero]
    rcases lt_or_gt_of_ne hyρ with h2 | h2
    · -- on the open annulus, `ζ = g` near `y`, `g z = (ρ - |z - x|)/(ρ - s)`
      have hyA : y ∈ Metric.ball x ρ \ Metric.ball x s :=
        ⟨Metric.mem_ball.mpr h2, fun h ↦ lt_asymm (Metric.mem_ball.mp h) h1⟩
      rw [Set.indicator_of_mem hyA]
      set g : Rn N → ℝ := fun z ↦ (ρ - ‖z - x‖) * (ρ - s)⁻¹ with hg
      have hev1 : ∀ᶠ z in 𝓝 y, s < dist z x := (hcont.tendsto y).eventually (lt_mem_nhds h1)
      have hev2 : ∀ᶠ z in 𝓝 y, dist z x < ρ := (hcont.tendsto y).eventually (gt_mem_nhds h2)
      have hEq : ζ =ᶠ[𝓝 y] g := by
        filter_upwards [hev1, hev2] with z hz1 hz2
        have hlo : 0 ≤ (ρ - dist z x) / (ρ - s) := div_nonneg (by linarith) hc.le
        have hhi : (ρ - dist z x) / (ρ - s) ≤ 1 := by rw [div_le_one hc]; linarith
        simp only [hζ, hg]
        rw [max_eq_right hlo, min_eq_right hhi, dist_eq_norm, div_eq_mul_inv]
      set v : Rn N := y - x with hv
      have hvpos : 0 < ‖v‖ := by rw [hv, ← dist_eq_norm]; linarith
      have hvne : v ≠ 0 := norm_pos_iff.mp hvpos
      have hgd : DifferentiableAt ℝ g y :=
        (((differentiableAt_id.sub_const x).norm ℝ hvne).const_sub ρ).mul_const (ρ - s)⁻¹
      -- the radial derivative of `g` at `y` is `-|v|/(ρ - s)`
      have hline : HasDerivAt (fun t : ℝ ↦ g (y + t • v)) (fderiv ℝ g y v) 0 := by
        have hℓ : HasDerivAt (fun t : ℝ ↦ y + t • v) v 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
        exact hgd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hℓ (by simp)
      have hline' : HasDerivAt (fun t : ℝ ↦ g (y + t • v)) (-(‖v‖ / (ρ - s))) 0 := by
        have haff : HasDerivAt (fun t : ℝ ↦ (ρ - (1 + t) * ‖v‖) * (ρ - s)⁻¹)
            (-(‖v‖ / (ρ - s))) 0 :=
          ((((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const ‖v‖).const_sub ρ).mul_const
            (ρ - s)⁻¹ |>.congr_deriv (by ring)
        refine haff.congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with t ht
        have h1t : 0 ≤ 1 + t := by linarith [show (-1 : ℝ) < t from ht]
        have hyt : y + t • v - x = (1 + t) • v := by rw [add_smul, one_smul, hv]; abel
        simp only [hg]
        rw [hyt, norm_smul, Real.norm_of_nonneg h1t]
      have hgv : fderiv ℝ g y v = -(‖v‖ / (ρ - s)) := hline.unique hline'
      refine le_antisymm (norm_fderiv_le_of_lipschitz ℝ hlip) ?_
      rw [hEq.fderiv_eq]
      have h := (fderiv ℝ g y).le_opNorm v
      rw [hgv, norm_neg, Real.norm_of_nonneg (div_nonneg hvpos.le hc.le), div_eq_inv_mul] at h
      exact le_of_mul_le_mul_right h hvpos
    · -- off `B̄_ρ(x)`, `ζ ≡ 0` near `y`
      have hev : ∀ᶠ z in 𝓝 y, ρ < dist z x := (hcont.tendsto y).eventually (lt_mem_nhds h2)
      have hEq : ζ =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
        filter_upwards [hev] with z hz using hzero z hz.le
      have hnA : y ∉ Metric.ball x ρ \ Metric.ball x s := fun h ↦
        lt_asymm (Metric.mem_ball.mp h.1) h2
      rw [Set.indicator_of_notMem hnA, hEq.fderiv_eq, fderiv_const_apply, norm_zero]
  -- spheres of positive radius are Lebesgue-null (empty when `N = 0`)
  have hsph : ∀ r : ℝ, 0 < r → volume (Metric.sphere x r) = 0 := by
    intro r hr
    rcases subsingleton_or_nontrivial (Rn N) with hsub | hnt
    · have : Metric.sphere x r = ∅ := Set.eq_empty_of_forall_notMem fun y hy ↦ by
        rw [Metric.mem_sphere, Subsingleton.elim y x, dist_self] at hy
        exact hr.ne hy
      rw [this, measure_empty]
    · exact Measure.addHaar_sphere volume x r
  have hae : ∀ᵐ y ∂(volume : Measure (Rn N)),
      ‖fderiv ℝ ζ y‖ = (Metric.ball x ρ \ Metric.ball x s).indicator (fun _ ↦ (ρ - s)⁻¹) y := by
    have h0 : volume (Metric.sphere x s ∪ Metric.sphere x ρ) = 0 :=
      measure_union_null (hsph s hs) (hsph ρ (hs.trans hsρ))
    filter_upwards [compl_mem_ae_iff.mpr h0] with y hy
    simp only [Set.mem_compl_iff, Set.mem_union, Metric.mem_sphere, not_or] at hy
    exact hpt y hy.1 hy.2
  refine ⟨ζ, ⟨K, hlip⟩, (isCompact_closedBall x ρ).of_isClosed_subset (isClosed_tsupport ζ) htsupp,
    htsupp, hval, fun y hy ↦ hone y (Metric.mem_ball.mp hy), hout, fun G hG ↦ ?_⟩
  -- Step 4: integrate over `G`; `L^N(G ∩ B_ρ) = L^N(G ∩ B_s) + L^N(G ∩ (B_ρ ∖ B_s))`.
  have hAm : MeasurableSet (Metric.ball x ρ \ Metric.ball x s) :=
    measurableSet_ball.diff measurableSet_ball
  have hint : ∫ y in G, ‖fderiv ℝ ζ y‖ =
      ∫ y in G, (Metric.ball x ρ \ Metric.ball x s).indicator (fun _ ↦ (ρ - s)⁻¹) y :=
    integral_congr_ae (ae_restrict_of_ae hae)
  have hset : (Metric.ball x ρ \ Metric.ball x s) ∩ G =
      (G ∩ Metric.ball x ρ) \ (G ∩ Metric.ball x s) := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_sdiff]; tauto
  have hsub : G ∩ Metric.ball x s ⊆ G ∩ Metric.ball x ρ :=
    Set.inter_subset_inter_right G (Metric.ball_subset_ball hsρ.le)
  have hfin : volume (G ∩ Metric.ball x ρ) ≠ ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt measure_ball_lt_top).ne
  rw [hint, integral_indicator_const _ hAm, measureReal_restrict_apply hAm, smul_eq_mul, hset,
    measureReal_def, measure_sdiff hsub (hG.inter measurableSet_ball.nullMeasurableSet)
      (ne_top_of_le_ne_top hfin (measure_mono hsub)),
    ENNReal.toReal_sub_of_le (measure_mono hsub) hfin, div_eq_mul_inv]
/-- **A mollifier sequence and the mollified indicators of a measurable set** (Steps 1 and 3 of
the mollification argument for the Sobolev inequality for `ζ χ_G` in the proof of Simon Ch. 3,
Theorem 4.3, `chapter-03.txt` lines 689–705; mollifiers as in Simon Ch. 2, §2, `chapter-02.txt`
lines 531–545, at the radii `s_j = r/(j+1)`). `ρ_j = φ_j / ∫ φ_j`, where `φ_j` is a smooth bump
with `φ_j = 1` on `B̄_{s_j/2}(0)` and `tsupport φ_j = B̄_{s_j}(0)`. For null-measurable
`G`, `u_j(y) = ∫_G ρ_j(y - z) dz` satisfies `0 ≤ u_j ≤ ∫ ρ_j = 1`; `u_j` is Lipschitz because
`|ρ_j(a) - ρ_j(b)| ≤ C |a - b| (χ_B(a) + χ_B(b))` with `B = B̄_{s_j}(0)`; `u_j → χ_G` a.e. by the
Lebesgue differentiation theorem (Besicovitch Vitali family), since `∫ φ_j ≥ |B̄_{s_j/2}|` gives
`ρ_j ≤ 2ᴺ / |B̄_{s_j}|`; and `∫ u_j h → ∫_G h` by dominated convergence with bound `|h|`. -/
theorem Submission.deGiorgiSobInd_mollifier_seq : ∀ (N : ℕ) (r : ℝ), 0 < r → ∃ ρ : ℕ → Rn N → ℝ, (∀ j, ContDiff ℝ 1 (ρ j)) ∧ (∀ j, HasCompactSupport (ρ j)) ∧ (∀ j y, 0 ≤ ρ j y) ∧ (∀ j, ∫ y, ρ j y = 1) ∧ (∀ j, tsupport (ρ j) ⊆ Metric.closedBall (0 : Rn N) (r / ((j : ℝ) + 1))) ∧ ∀ G : Set (Rn N), NullMeasurableSet G volume → (∀ j, ∃ L : ℝ≥0, LipschitzWith L (fun y ↦ ∫ z in G, ρ j (y - z))) ∧ (∀ j y, 0 ≤ (∫ z in G, ρ j (y - z)) ∧ (∫ z in G, ρ j (y - z)) ≤ 1) ∧ (∀ᵐ y ∂(volume : Measure (Rn N)), Tendsto (fun j ↦ ∫ z in G, ρ j (y - z)) atTop (𝓝 (G.indicator (fun _ ↦ (1 : ℝ)) y))) ∧ ∀ h : Rn N → ℝ, Integrable h → Tendsto (fun j ↦ ∫ y, (∫ z in G, ρ j (y - z)) * h y) atTop (𝓝 (∫ y in G, h y)) := by
  intro N r hr
  -- Step 1: radii `s j = r/(j+1)`, bumps `φ j` with radii `s j / 2 < s j`, `ρ j = φ j / ∫ φ j`.
  obtain ⟨s, hs_def⟩ : ∃ s : ℕ → ℝ, ∀ j, s j = r / ((j : ℝ) + 1) :=
    ⟨fun j ↦ r / ((j : ℝ) + 1), fun _ ↦ rfl⟩
  have hs : ∀ j, 0 < s j := fun j ↦ by rw [hs_def]; positivity
  obtain ⟨φ, hφin, hφout⟩ : ∃ φ : ℕ → ContDiffBump (0 : Rn N),
      (∀ j, (φ j).rIn = s j / 2) ∧ ∀ j, (φ j).rOut = s j :=
    ⟨fun j ↦ ⟨s j / 2, s j, half_pos (hs j), half_lt_self (hs j)⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hφint : ∀ j, Integrable (φ j) (volume : Measure (Rn N)) := fun j ↦
    (φ j).continuous.integrable_of_hasCompactSupport (φ j).hasCompactSupport
  have hball : ∀ (x : Rn N) (t : ℝ), 0 < t → 0 < volume.real (Metric.closedBall x t) :=
    fun x t ht ↦ ENNReal.toReal_pos (Metric.measure_closedBall_pos volume x ht).ne'
      measure_closedBall_lt_top.ne
  -- `∫ φ j ≥ |B̄_{s j / 2}(0)|`, as `φ j = 1` on `B̄_{rIn}(0)` and `φ j ≥ 0`.
  have hφlow : ∀ j, volume.real (Metric.closedBall (0 : Rn N) (s j / 2)) ≤ ∫ x, φ j x := by
    intro j
    calc volume.real (Metric.closedBall (0 : Rn N) (s j / 2))
        = ∫ x in Metric.closedBall (0 : Rn N) (s j / 2), (1 : ℝ) := by simp
      _ = ∫ x in Metric.closedBall (0 : Rn N) (s j / 2), φ j x :=
          setIntegral_congr_fun measurableSet_closedBall fun x hx ↦
            ((φ j).one_of_mem_closedBall (by rwa [hφin])).symm
      _ ≤ ∫ x, φ j x :=
          setIntegral_le_integral (hφint j) (Eventually.of_forall fun x ↦ (φ j).nonneg)
  have hc : ∀ j, 0 < ∫ x, φ j x := fun j ↦ (hball 0 _ (half_pos (hs j))).trans_le (hφlow j)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → Rn N → ℝ, ∀ j x, ρ j x = (∫ y, φ j y)⁻¹ * φ j x :=
    ⟨fun j x ↦ (∫ y, φ j y)⁻¹ * φ j x, fun _ _ ↦ rfl⟩
  have hρfun : ∀ j, ρ j = fun x ↦ (∫ y, φ j y)⁻¹ * φ j x := fun j ↦ funext (hρ j)
  have hρ_diff : ∀ j, ContDiff ℝ 1 (ρ j) := fun j ↦ by
    rw [hρfun]
    exact contDiff_const.mul ((φ j).contDiff (n := 1))
  have hρ_nonneg : ∀ j x, 0 ≤ ρ j x := fun j x ↦ by
    rw [hρ]
    exact mul_nonneg (inv_nonneg.2 (hc j).le) (φ j).nonneg
  have hρ_le : ∀ j x, ρ j x ≤ (∫ y, φ j y)⁻¹ := fun j x ↦ by
    rw [hρ]
    exact mul_le_of_le_one_right (inv_nonneg.2 (hc j).le) (φ j).le_one
  have hρ_tsupp : ∀ j, tsupport (ρ j) ⊆ Metric.closedBall (0 : Rn N) (s j) := fun j ↦ by
    rw [hρfun, ← hφout j, ← (φ j).tsupport_eq]
    exact tsupport_mul_subset_right
  have hρ_zero : ∀ j x, x ∉ Metric.closedBall (0 : Rn N) (s j) → ρ j x = 0 :=
    fun j x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hρ_tsupp j h)
  have hρ_cs : ∀ j, HasCompactSupport (ρ j) := fun j ↦
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hρ_tsupp j)
  have hρ_integrable : ∀ j, Integrable (ρ j) (volume : Measure (Rn N)) := fun j ↦
    (hρ_diff j).continuous.integrable_of_hasCompactSupport (hρ_cs j)
  have hρ_int : ∀ j, ∫ x, ρ j x = 1 := fun j ↦ by
    simp_rw [hρ]
    rw [integral_const_mul, inv_mul_cancel₀ (hc j).ne']
  refine ⟨ρ, hρ_diff, hρ_cs, hρ_nonneg, hρ_int, fun j ↦ by rw [← hs_def]; exact hρ_tsupp j,
    fun G hG ↦ ?_⟩
  -- Step 2: `u j y = ∫_G ρ j (y - z) dz`; the kernel `z ↦ ρ j (y - z)` is integrable with total
  -- integral `1` (translation invariance) and support in `B̄_{s j}(y)`.
  have hu_int : ∀ j (y : Rn N), Integrable (fun z ↦ ρ j (y - z)) (volume : Measure (Rn N)) :=
    fun j y ↦ (hρ_integrable j).comp_sub_left y
  have hu_total : ∀ j (y : Rn N), ∫ z, ρ j (y - z) = 1 := fun j y ↦ by
    rw [integral_sub_left_eq_self (ρ j) volume y, hρ_int]
  -- Step 3: `0 ≤ u j ≤ 1`.
  have hu_bd : ∀ j y, 0 ≤ (∫ z in G, ρ j (y - z)) ∧ (∫ z in G, ρ j (y - z)) ≤ 1 := fun j y ↦
    ⟨integral_nonneg fun z ↦ hρ_nonneg j _,
      (setIntegral_le_integral (hu_int j y) (Eventually.of_forall fun z ↦ hρ_nonneg j _)).trans
        (hu_total j y).le⟩
  -- Step 4: `u j` is Lipschitz: `|ρ j a - ρ j b| ≤ C ‖a - b‖ (χ_B a + χ_B b)`, `B = B̄_{s j}(0)`.
  have hLip : ∀ j, ∃ L : ℝ≥0, LipschitzWith L (fun y ↦ ∫ z in G, ρ j (y - z)) := by
    intro j
    obtain ⟨C, hC⟩ :=
      ContDiff.lipschitzWith_of_hasCompactSupport (hρ_cs j) (hρ_diff j) one_ne_zero
    obtain ⟨B, hB⟩ : ∃ B : Set (Rn N), B = Metric.closedBall 0 (s j) := ⟨_, rfl⟩
    have hBm : MeasurableSet B := by rw [hB]; exact measurableSet_closedBall
    have hBfin : volume B ≠ ⊤ := by rw [hB]; exact measure_closedBall_lt_top.ne
    have hzero : ∀ x, x ∉ B → ρ j x = 0 := by rw [hB]; exact hρ_zero j
    have hind : ∀ x, 0 ≤ B.indicator (1 : Rn N → ℝ) x :=
      Set.indicator_nonneg fun _ _ ↦ zero_le_one
    have hind_int : ∀ y : Rn N,
        Integrable (fun z ↦ B.indicator (1 : Rn N → ℝ) (y - z)) volume := fun y ↦
      ((integrable_indicator_iff hBm).2 (integrableOn_const (C := (1 : ℝ)) hBfin)).comp_sub_left y
    have hpt : ∀ a b : Rn N, |ρ j a - ρ j b| ≤
        C * ‖a - b‖ * (B.indicator (1 : Rn N → ℝ) a + B.indicator (1 : Rn N → ℝ) b) := by
      intro a b
      have hab : |ρ j a - ρ j b| ≤ C * ‖a - b‖ := by
        rw [← Real.dist_eq, ← dist_eq_norm]
        exact hC.dist_le_mul a b
      have h0 : 0 ≤ (C : ℝ) * ‖a - b‖ := by positivity
      by_cases hmem : a ∈ B ∨ b ∈ B
      · have h1 : (1 : ℝ) ≤ B.indicator (1 : Rn N → ℝ) a + B.indicator (1 : Rn N → ℝ) b := by
          rcases hmem with h | h <;> rw [Set.indicator_of_mem h, Pi.one_apply]
          · linarith [hind b]
          · linarith [hind a]
        calc |ρ j a - ρ j b| ≤ C * ‖a - b‖ * 1 := by rw [mul_one]; exact hab
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 h0
      obtain ⟨ha, hb⟩ := not_or.1 hmem
      rw [hzero a ha, hzero b hb, sub_zero, abs_zero]
      exact mul_nonneg h0 (add_nonneg (hind a) (hind b))
    refine ⟨C * (2 * (volume B).toNNReal), LipschitzWith.of_dist_le_mul fun y y' ↦ ?_⟩
    show dist (∫ z in G, ρ j (y - z)) (∫ z in G, ρ j (y' - z)) ≤ _
    rw [Real.dist_eq, ← integral_sub (hu_int j y).integrableOn (hu_int j y').integrableOn]
    calc |∫ z in G, (ρ j (y - z) - ρ j (y' - z))|
        ≤ ∫ z in G, |ρ j (y - z) - ρ j (y' - z)| := abs_integral_le_integral_abs
      _ ≤ ∫ z, |ρ j (y - z) - ρ j (y' - z)| :=
          setIntegral_le_integral ((hu_int j y).sub (hu_int j y')).abs
            (Eventually.of_forall fun z ↦ abs_nonneg _)
      _ ≤ ∫ z, C * ‖y - y'‖ *
            (B.indicator (1 : Rn N → ℝ) (y - z) + B.indicator (1 : Rn N → ℝ) (y' - z)) := by
          refine integral_mono ((hu_int j y).sub (hu_int j y')).abs
            (((hind_int y).add (hind_int y')).const_mul _) fun z ↦ ?_
          simpa only [sub_sub_sub_cancel_right] using hpt (y - z) (y' - z)
      _ = C * ‖y - y'‖ * (volume.real B + volume.real B) := by
          rw [integral_const_mul, integral_add (hind_int y) (hind_int y'),
            integral_sub_left_eq_self (B.indicator (1 : Rn N → ℝ)) volume y,
            integral_sub_left_eq_self (B.indicator (1 : Rn N → ℝ)) volume y',
            integral_indicator_one hBm]
      _ = ↑(C * (2 * (volume B).toNNReal)) * dist y y' := by
          simp only [NNReal.coe_mul, NNReal.coe_ofNat, ENNReal.coe_toNNReal_eq_toReal,
            dist_eq_norm, measureReal_def]
          ring
  -- Step 5: `u j → χ_G` a.e., by the Lebesgue differentiation theorem.
  have hχ : LocallyIntegrable (G.indicator fun _ ↦ (1 : ℝ)) (volume : Measure (Rn N)) :=
    ((locallyIntegrable_const (1 : ℝ)).indicator (measurableSet_toMeasurable volume G)).congr
      (indicator_ae_eq_of_ae_eq_set hG.toMeasurable_ae_eq)
  have hs0 : Tendsto s atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hs⟩
    rw [show s = fun j : ℕ ↦ r / ((j : ℝ) + 1) from funext hs_def]
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hsupp : ∀ j (y : Rn N),
      Function.support (fun z ↦ ρ j (y - z)) ⊆ Metric.closedBall y (s j) := by
    intro j y z hz
    by_contra hzB
    refine (Function.mem_support.1 hz) (hρ_zero j _ fun hmem ↦ hzB ?_)
    rw [Metric.mem_closedBall, dist_eq_norm']
    rwa [mem_closedBall_zero_iff] at hmem
  have hbound : ∀ j (y z : Rn N),
      |ρ j (y - z)| ≤ 2 ^ Module.finrank ℝ (Rn N) / volume.real (Metric.closedBall y (s j)) := by
    intro j y z
    rw [abs_of_nonneg (hρ_nonneg j _), le_div_iff₀ (hball y _ (hs j))]
    refine (mul_le_mul_of_nonneg_right (hρ_le j _) (hball y _ (hs j)).le).trans ?_
    rw [inv_mul_le_iff₀ (hc j)]
    calc volume.real (Metric.closedBall y (s j))
        = 2 ^ Module.finrank ℝ (Rn N) * volume.real (Metric.closedBall (0 : Rn N) (s j / 2)) := by
          rw [Measure.addHaar_real_closedBall' volume y (hs j).le,
            Measure.addHaar_real_closedBall' volume 0 (half_pos (hs j)).le, ← mul_assoc,
            ← mul_pow]
          congr 2
          ring
      _ ≤ 2 ^ Module.finrank ℝ (Rn N) * ∫ x, φ j x :=
          mul_le_mul_of_nonneg_left (hφlow j) (by positivity)
      _ = (∫ x, φ j x) * 2 ^ Module.finrank ℝ (Rn N) := mul_comm _ _
  have hae : ∀ᵐ y ∂(volume : Measure (Rn N)),
      Tendsto (fun j ↦ ∫ z in G, ρ j (y - z)) atTop (𝓝 (G.indicator (fun _ ↦ (1 : ℝ)) y)) := by
    filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (Rn N))).ae_tendsto_average_norm_sub
      hχ] with y hy
    have h1 : Tendsto (fun j ↦ ⨍ z in Metric.closedBall y (s j),
        ‖G.indicator (fun _ ↦ (1 : ℝ)) z - G.indicator (fun _ ↦ (1 : ℝ)) y‖) atTop (𝓝 0) :=
      (hy.comp (Besicovitch.tendsto_filterAt volume y)).comp hs0
    have h2 : Tendsto (fun j ↦ ∫ z, ρ j (y - z) • G.indicator (fun _ ↦ (1 : ℝ)) z) atTop
        (𝓝 (G.indicator (fun _ ↦ (1 : ℝ)) y)) :=
      tendsto_integral_smul_of_tendsto_average_norm_sub (2 ^ Module.finrank ℝ (Rn N)) h1
        (Eventually.of_forall fun j ↦ hχ.integrableOn_isCompact (isCompact_closedBall _ _))
        (tendsto_const_nhds.congr fun j ↦ (hu_total j y).symm)
        (Eventually.of_forall fun j ↦ hsupp j y) (Eventually.of_forall fun j ↦ hbound j y)
    refine h2.congr fun j ↦ ?_
    rw [← integral_indicator₀ hG]
    congr 1
    funext z
    by_cases hz : z ∈ G <;> simp [hz]
  -- Step 6: `∫ u j h → ∫_G h` by dominated convergence with bound `|h|`.
  refine ⟨hLip, hu_bd, hae, fun h hh ↦ ?_⟩
  have hcont : ∀ j, Continuous (fun y ↦ ∫ z in G, ρ j (y - z)) := fun j ↦ by
    obtain ⟨L, hL⟩ := hLip j
    exact hL.continuous
  have hdom : ∀ j y, ‖(∫ z in G, ρ j (y - z)) * h y‖ ≤ ‖h y‖ := fun j y ↦ by
    rw [norm_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hu_bd j y).1]
    exact (hu_bd j y).2
  have key : Tendsto (fun j ↦ ∫ y, (∫ z in G, ρ j (y - z)) * h y) atTop
      (𝓝 (∫ y, G.indicator (fun _ ↦ (1 : ℝ)) y * h y)) :=
    tendsto_integral_of_dominated_convergence (fun y ↦ ‖h y‖)
      (fun j ↦ (hcont j).aestronglyMeasurable.mul hh.aestronglyMeasurable) hh.norm
      (fun j ↦ Eventually.of_forall (hdom j)) (hae.mono fun y hy ↦ hy.mul_const (h y))
  have hlim : ∫ y, G.indicator (fun _ ↦ (1 : ℝ)) y * h y = ∫ y in G, h y := by
    rw [← integral_indicator₀ hG]
    congr 1
    funext y
    by_cases hy : y ∈ G <;> simp [hy]
  rwa [hlim] at key
/-- **Product rule bound for `ζ u`** (Step 1 of the supplied proof of the Sobolev inequality for
`ζ χ_G`, part of the density estimates for De Giorgi's theorem, Simon Ch. 3, Theorem 4.3). Let
`ζ ≥ 0` be `K`-Lipschitz with compact support and `u` be `L`-Lipschitz with `0 ≤ u ≤ 1` on `ℝᴺ`.
Then `ζ u` is Lipschitz with compact support and, by Rademacher's theorem and the product rule,
`∫ |D(ζ u)| ≤ ∫ ζ |Du| + ∫ u |Dζ|`. -/
theorem Submission.deGiorgiSobInd_mul_lipschitz_fderiv_bound : ∀ (N : ℕ) (ζ u : Rn N → ℝ) (K L : ℝ≥0), LipschitzWith K ζ → HasCompactSupport ζ → (∀ y, 0 ≤ ζ y) → LipschitzWith L u → (∀ y, 0 ≤ u y ∧ u y ≤ 1) → (∃ K' : ℝ≥0, LipschitzWith K' (fun y ↦ ζ y * u y)) ∧ HasCompactSupport (fun y ↦ ζ y * u y) ∧ ∫ y, ‖fderiv ℝ (fun y ↦ ζ y * u y) y‖ ≤ (∫ y, ζ y * ‖fderiv ℝ u y‖) + ∫ y, u y * ‖fderiv ℝ ζ y‖ := by
  intro N ζ u K L hζ hζc hζ0 hu hu01
  -- Step 1: `0 ≤ ζ ≤ M` for some `M ∈ ℝ≥0`.
  obtain ⟨M, hM⟩ : ∃ M : ℝ≥0, ∀ y, ζ y ≤ M := by
    obtain ⟨B, hB⟩ := hζ.continuous.bddAbove_range_of_hasCompactSupport hζc
    exact ⟨B.toNNReal, fun y ↦ (hB (Set.mem_range_self y)).trans (Real.le_coe_toNNReal B)⟩
  -- Step 2: `ζ u` is `(M L + K)`-Lipschitz.
  have hlip : LipschitzWith (M * L + K) (fun y ↦ ζ y * u y) := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    have h1 := hu.dist_le_mul x y
    have h2 := hζ.dist_le_mul x y
    rw [Real.dist_eq] at h1 h2 ⊢
    calc |ζ x * u x - ζ y * u y| = |ζ x * (u x - u y) + u y * (ζ x - ζ y)| := by
          congr 1; ring
      _ ≤ |ζ x * (u x - u y)| + |u y * (ζ x - ζ y)| := abs_add_le _ _
      _ = ζ x * |u x - u y| + u y * |ζ x - ζ y| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (hζ0 x), abs_of_nonneg (hu01 y).1]
      _ ≤ M * (L * dist x y) + 1 * (K * dist x y) := by
          gcongr
          · exact hM x
          · exact (hu01 y).2
      _ = ((M * L + K : ℝ≥0) : ℝ) * dist x y := by push_cast; ring
  -- Step 3: `ζ u` has compact support, and `tsupport (ζ u) ⊆ T := tsupport ζ`.
  have hcs : HasCompactSupport (fun y ↦ ζ y * u y) := hζc.mul_right
  have hsub : tsupport (fun y ↦ ζ y * u y) ⊆ tsupport ζ := tsupport_mul_subset_left
  -- Step 4: the pointwise bound at every point where `ζ` and `u` are differentiable.
  have hpt : ∀ᵐ y ∂(volume : Measure (Rn N)),
      ‖fderiv ℝ (fun y ↦ ζ y * u y) y‖ ≤ ζ y * ‖fderiv ℝ u y‖ + u y * ‖fderiv ℝ ζ y‖ := by
    filter_upwards [hζ.ae_differentiableAt (μ := volume), hu.ae_differentiableAt (μ := volume)]
      with y hy1 hy2
    rw [fderiv_fun_mul hy1 hy2]
    calc ‖ζ y • fderiv ℝ u y + u y • fderiv ℝ ζ y‖
        ≤ ‖ζ y • fderiv ℝ u y‖ + ‖u y • fderiv ℝ ζ y‖ := norm_add_le _ _
      _ = ζ y * ‖fderiv ℝ u y‖ + u y * ‖fderiv ℝ ζ y‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (hζ0 y), Real.norm_of_nonneg (hu01 y).1]
  -- Step 5: integrability; all three functions are bounded and vanish off `T`.
  have hT : volume (tsupport ζ) ≠ ∞ := hζc.isCompact.measure_lt_top.ne
  have hi1 : Integrable (fun y ↦ ‖fderiv ℝ (fun y ↦ ζ y * u y) y‖) := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport ζ) ?_ fun y hy ↦ ?_
    · refine Measure.integrableOn_of_bounded (M := ((M * L + K : ℝ≥0) : ℝ)) hT
        (measurable_fderiv ℝ _).norm.aestronglyMeasurable (ae_of_all _ fun y ↦ ?_)
      rw [norm_norm]
      exact norm_fderiv_le_of_lipschitz ℝ hlip
    · rw [fderiv_of_notMem_tsupport ℝ fun h ↦ hy (hsub h), norm_zero]
  have hi2 : Integrable (fun y ↦ ζ y * ‖fderiv ℝ u y‖) := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport ζ) ?_ fun y hy ↦ ?_
    · refine Measure.integrableOn_of_bounded (M := (M : ℝ) * L) hT
        (hζ.continuous.measurable.mul (measurable_fderiv ℝ u).norm).aestronglyMeasurable
        (ae_of_all _ fun y ↦ ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (hζ0 y) (norm_nonneg _))]
      exact mul_le_mul (hM y) (norm_fderiv_le_of_lipschitz ℝ hu) (norm_nonneg _) M.2
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have hi3 : Integrable (fun y ↦ u y * ‖fderiv ℝ ζ y‖) := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport ζ) ?_ fun y hy ↦ ?_
    · refine Measure.integrableOn_of_bounded (M := 1 * (K : ℝ)) hT
        (hu.continuous.measurable.mul (measurable_fderiv ℝ ζ).norm).aestronglyMeasurable
        (ae_of_all _ fun y ↦ ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (hu01 y).1 (norm_nonneg _))]
      exact mul_le_mul (hu01 y).2 (norm_fderiv_le_of_lipschitz ℝ hζ) (norm_nonneg _) zero_le_one
    · rw [fderiv_of_notMem_tsupport ℝ hy, norm_zero, mul_zero]
  -- Step 6: integrate the pointwise bound.
  refine ⟨⟨M * L + K, hlip⟩, hcs, ?_⟩
  calc ∫ y, ‖fderiv ℝ (fun y ↦ ζ y * u y) y‖
      ≤ ∫ y, (ζ y * ‖fderiv ℝ u y‖ + u y * ‖fderiv ℝ ζ y‖) := integral_mono_ae hi1 (hi2.add hi3) hpt
    _ = (∫ y, ζ y * ‖fderiv ℝ u y‖) + ∫ y, u y * ‖fderiv ℝ ζ y‖ := integral_add hi2 hi3
/-- Differentiation under the integral sign for a mollified set integral (Simon Ch. 2, §2,
mollification and Lemma 2.5, with `χ_G` in place of `u` and a general `C¹` kernel `ρ`; used in
Ch. 3, proof of Theorem 4.3): for `G ⊆ ℝᴺ` and `ρ ∈ C¹_c(ℝᴺ)`, `u(x) = ∫_G ρ(x - z) dz` satisfies
`Du(x) w = ∫_G Dρ(x - z) w dz`. The derivative is computed directly for `Lᴺ ⌞ G` by
`hasFDerivAt_integral_of_dominated_of_fderiv_le`, with the bound `C · χ_{B̄_{R+1}(x)}` on
`B_1(x)`, where `‖Dρ‖ ≤ C` and `tsupport ρ ⊆ B̄_R(0)`; the measurability of `G` is not used. -/
theorem Submission.deGiorgiSobIndMFL_fderiv_setIntegral_apply : ∀ (N : ℕ) (G : Set (Rn N)) (ρ : Rn N → ℝ), NullMeasurableSet G volume → ContDiff ℝ 1 ρ → HasCompactSupport ρ → ∀ x w : Rn N, fderiv ℝ (fun x ↦ ∫ z in G, ρ (x - z)) x w = ∫ z in G, fderiv ℝ ρ (x - z) w := by
  intro N G ρ _hG hρ hρc x₀ w
  -- Step 1: `Dρ` is continuous, compactly supported and bounded by `C`; `tsupport ρ ⊆ B̄_R(0)`.
  have hρd : Differentiable ℝ ρ := hρ.differentiable one_ne_zero
  have hρ'c : Continuous (fderiv ℝ ρ) := hρ.continuous_fderiv one_ne_zero
  have hρ'cs : HasCompactSupport (fderiv ℝ ρ) := hρc.fderiv ℝ
  obtain ⟨C, hC⟩ := hρ'c.bounded_above_of_compact_support hρ'cs
  obtain ⟨R, hR⟩ : ∃ R, tsupport ρ ⊆ Metric.closedBall (0 : Rn N) R :=
    hρc.isCompact.isBounded.subset_closedBall 0
  -- Step 2: `z ↦ f (a - z)` is continuous with compact support, hence integrable on `G`.
  have hrefl : ∀ {E : Type} [NormedAddCommGroup E] (f : Rn N → E) (a : Rn N), Continuous f →
      HasCompactSupport f → Continuous (fun z ↦ f (a - z)) ∧ IntegrableOn (fun z ↦ f (a - z)) G :=
    fun f a hf hfc ↦ ⟨hf.comp (continuous_const.sub continuous_id),
      ((hf.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
        (hfc.comp_homeomorph (Homeomorph.subLeft a))).integrableOn⟩
  -- Step 3: by the chain rule, `x ↦ ρ (x - z)` has derivative `Dρ (x - z)` at every `x`.
  have hderiv : ∀ z x, HasFDerivAt (fun x ↦ ρ (x - z)) (fderiv ℝ ρ (x - z)) x := fun z x ↦
    ((hρd (x - z)).hasFDerivAt.comp x (hasFDerivAt_sub_const z)).congr_fderiv
      (ContinuousLinearMap.comp_id _)
  -- Step 4: for `x ∈ B_1(x₀)`, `‖Dρ (x - z)‖ ≤ C · χ_{B̄_{R+1}(x₀)}(z)`.
  have hbound : ∀ z, ∀ x ∈ Metric.ball x₀ 1,
      ‖fderiv ℝ ρ (x - z)‖ ≤ (Metric.closedBall x₀ (R + 1)).indicator (fun _ ↦ C) z := by
    intro z x hx
    by_cases hz : z ∈ Metric.closedBall x₀ (R + 1)
    · simpa [hz] using hC (x - z)
    · have hxz : x - z ∉ tsupport ρ := by
        intro h
        apply hz
        have h2 := hR h
        rw [Metric.mem_closedBall, dist_zero_right] at h2
        rw [Metric.mem_ball] at hx
        rw [Metric.mem_closedBall]
        calc dist z x₀ ≤ dist z x + dist x x₀ := dist_triangle _ _ _
          _ = ‖x - z‖ + dist x x₀ := by rw [dist_eq_norm, norm_sub_rev]
          _ ≤ R + 1 := by linarith
      simp [hz, fderiv_of_notMem_tsupport ℝ hxz]
  -- Step 5: differentiation under the integral sign for `Lᴺ ⌞ G`.
  have hkey : HasFDerivAt (fun x ↦ ∫ z in G, ρ (x - z)) (∫ z in G, fderiv ℝ ρ (x₀ - z)) x₀ :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds x₀ one_pos)
      (Eventually.of_forall fun x ↦ (hrefl ρ x hρ.continuous hρc).1.aestronglyMeasurable)
      (hrefl ρ x₀ hρ.continuous hρc).2 (hrefl (fderiv ℝ ρ) x₀ hρ'c hρ'cs).1.aestronglyMeasurable
      (Eventually.of_forall hbound)
      ((integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const (isCompact_closedBall x₀ (R + 1)).measure_lt_top.ne))
      (Eventually.of_forall fun z x _ ↦ hderiv z x)
  -- Step 6: evaluation at `w` commutes with the Bochner integral.
  rw [hkey.fderiv, ContinuousLinearMap.integral_apply (hrefl (fderiv ℝ ρ) x₀ hρ'c hρ'cs).2]
/-- **Gauss–Green identity for a translated reflected kernel** (the pointwise form of the
identity `∫ g · ∇u_σ = -∫ u div(φ_σ ⋆ g)` in the proof of Simon Ch. 2, Lemma 2.5,
`chapter-02.txt` lines 543–596, tested against the single field `ρ(y - ·) w`). Let `(μ, ν)` be a
Gauss–Green pair for `(U, G)`, `ρ` a `C¹` function with `tsupport ρ ⊆ B̄_r(0)`, and
`B̄_r(y) ⊆ U`. Then `∫_G Dρ(y - z) w dz = ∫ ρ(y - z) ⟨w, ν(z)⟩ dμ(z)`. The field
`h(z) = ρ(y - z) w` is `C¹` with `tsupport h ⊆ B̄_r(y) ⊆ U`, and
`div h(z) = trace((-Dρ(y - z)).smulRight w) = -Dρ(y - z) w`, so the Gauss–Green identity of the
pair gives the claim over `G ∩ U`; the integrand vanishes off `B̄_r(y) ⊆ U`, so `∫_G = ∫_{G ∩ U}`. -/
theorem Submission.deGiorgiSobIndMFL_setIntegral_fderiv_kernel_eq : ∀ (N : ℕ) (U G : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → IsGaussGreenPair U G μ ν → ∀ (ρ : Rn N → ℝ) (r : ℝ) (y w : Rn N), ContDiff ℝ 1 ρ → HasCompactSupport ρ → tsupport ρ ⊆ Metric.closedBall (0 : Rn N) r → Metric.closedBall y r ⊆ U → ∫ z in G, fderiv ℝ ρ (y - z) w = ∫ z, ρ (y - z) * inner ℝ w (ν z) ∂μ := by
  intro N U G μ ν hU hGG ρ r y w hρ hρc hρr hyU
  have hρd : Differentiable ℝ ρ := hρ.differentiable one_ne_zero
  -- Step 1: `y - z ∈ tsupport ρ` forces `z ∈ B̄_r(y)`; hence `tsupport ρ(y - ·) ⊆ B̄_r(y)`.
  have hball : ∀ z, y - z ∈ tsupport ρ → z ∈ Metric.closedBall y r := by
    intro z hz
    have h := hρr hz
    rw [Metric.mem_closedBall, dist_zero_right] at h
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact h
  have hφsupp : tsupport (fun z ↦ ρ (y - z)) ⊆ Metric.closedBall y r :=
    closure_minimal (fun z hz ↦ hball z (subset_tsupport _ hz)) Metric.isClosed_closedBall
  -- Step 2: chain rule, `D(ρ(y - ·))(z) = -Dρ(y - z)`.
  have hφd : ∀ z, HasFDerivAt (fun z ↦ ρ (y - z)) (-(fderiv ℝ ρ (y - z))) z := by
    intro z
    have h1 : HasFDerivAt (fun z : Rn N ↦ y - z) (-(ContinuousLinearMap.id ℝ (Rn N))) z :=
      (hasFDerivAt_id z).const_sub y
    exact ((hρd (y - z)).hasFDerivAt.comp z h1).congr_fderiv (by ext v; simp)
  -- Step 3: the test field `h z = ρ (y - z) • w` is `C¹` with compact support in `B̄_r(y) ⊆ U`.
  have hhC : ContDiff ℝ 1 (fun z ↦ ρ (y - z) • w) :=
    (hρ.comp (contDiff_const.sub contDiff_id)).smul contDiff_const
  have hhsupp : tsupport (fun z ↦ ρ (y - z) • w) ⊆ Metric.closedBall y r :=
    (tsupport_smul_subset_left (fun z ↦ ρ (y - z)) (fun _ ↦ w)).trans hφsupp
  have hhc : HasCompactSupport (fun z ↦ ρ (y - z) • w) :=
    (isCompact_closedBall y r).of_isClosed_subset (isClosed_tsupport _) hhsupp
  have hGGh := hGG.2.2.2.2 (fun z ↦ ρ (y - z) • w) hhC hhc (hhsupp.trans hyU)
  -- Step 4: `div h(z) = trace((-Dρ(y - z)).smulRight w) = -Dρ(y - z) w`.
  have hdiv : ∀ z, Poincare.SimonGMT.Chapter02.euclideanDivergence (fun z ↦ ρ (y - z) • w) z =
      -(fderiv ℝ ρ (y - z) w) := by
    intro z
    have hfd : fderiv ℝ (fun z ↦ ρ (y - z) • w) z = (-(fderiv ℝ ρ (y - z))).smulRight w :=
      ((hφd z).smul_const w).fderiv
    unfold Poincare.SimonGMT.Chapter02.euclideanDivergence
    rw [hfd, ContinuousLinearMap.coe_smulRight, LinearMap.trace_smulRight]
    simp
  -- Step 5: Gauss–Green for `h`, with the signs cancelled.
  have hL : ∫ z in G ∩ U, Poincare.SimonGMT.Chapter02.euclideanDivergence
      (fun z ↦ ρ (y - z) • w) z = -∫ z in G ∩ U, fderiv ℝ ρ (y - z) w := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall hdiv)
  have hR : ∫ z, inner ℝ ((fun z ↦ ρ (y - z) • w) z) (ν z) ∂μ =
      ∫ z, ρ (y - z) * inner ℝ w (ν z) ∂μ :=
    integral_congr_ae (Eventually.of_forall fun z ↦ real_inner_smul_left w (ν z) (ρ (y - z)))
  rw [hL, hR] at hGGh
  -- Step 6: the integrand vanishes off `B̄_r(y) ⊆ U`, so `∫_G = ∫_{G ∩ U}`.
  have hvan : ∀ z, z ∉ U → fderiv ℝ ρ (y - z) w = 0 := by
    intro z hz
    have hz' : y - z ∉ tsupport ρ := fun h ↦ hz (hyU (hball z h))
    rw [fderiv_of_notMem_tsupport ℝ hz']
    simp
  have hrestr : ∫ z in G, fderiv ℝ ρ (y - z) w = ∫ z in G ∩ U, fderiv ℝ ρ (y - z) w := by
    rw [← setIntegral_indicator hU.measurableSet]
    refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
    by_cases hz : z ∈ U
    · simp [hz]
    · simp [hz, hvan z hz]
  rw [hrestr]
  exact neg_inj.mp hGGh

/-- **Pointwise bound for the derivative of a mollified indicator** (the pointwise form of the
estimate `|φ_σ ⋆ g| ≤ φ_σ ⋆ f` in the proof of Simon Ch. 2, Lemma 2.5, `chapter-02.txt`
lines 543–596). Let `(μ, ν)` be a Gauss–Green pair for `(U, G)`, `ρ ≥ 0` a `C¹_c` function with
`tsupport ρ ⊆ B̄_r(0)`, and `B̄_r(y) ⊆ U`. Then `u(x) = ∫_G ρ(x - z) dz` satisfies
`‖Du(y)‖ ≤ ∫ ρ(y - z) dμ(z)`. By the two preceding lemmas,
`Du(y) w = ∫_G Dρ(y - z) w dz = ∫ ρ(y - z) ⟨w, ν(z)⟩ dμ(z)`; the kernel `ρ(y - ·)` is continuous,
bounded and vanishes off the compact `B̄_r(y) ⊆ U`, so it is `μ`-integrable, and since `|ν| = 1`
`μ`-a.e., Cauchy–Schwarz gives `|Du(y) w| ≤ |w| ∫ ρ(y - z) dμ(z)`. -/
theorem Submission.deGiorgiSobIndMFL_norm_fderiv_le : ∀ (N : ℕ) (U G : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → NullMeasurableSet G volume → IsGaussGreenPair U G μ ν → ∀ (ρ : Rn N → ℝ) (r : ℝ) (y : Rn N), ContDiff ℝ 1 ρ → HasCompactSupport ρ → (∀ x, 0 ≤ ρ x) → tsupport ρ ⊆ Metric.closedBall (0 : Rn N) r → Metric.closedBall y r ⊆ U → ‖fderiv ℝ (fun x ↦ ∫ z in G, ρ (x - z)) y‖ ≤ ∫ z, ρ (y - z) ∂μ := by
  intro N U G μ ν hU hG hGG ρ r y hρ hρc hρ0 hρr hyU
  -- Step 1: `μ(B̄_r(y)) < ∞`, since `B̄_r(y)` is a compact subset of `U`.
  have hfin : μ (Metric.closedBall y r) < ∞ := hGG.2.1 _ (isCompact_closedBall y r) hyU
  -- Step 2: `ρ(y - ·)` is continuous, bounded by `M` and supported in `B̄_r(y)`, hence
  -- `μ`-integrable.
  have hφc : Continuous (fun z ↦ ρ (y - z)) :=
    hρ.continuous.comp (continuous_const.sub continuous_id)
  obtain ⟨M, hM⟩ := hρ.continuous.bounded_above_of_compact_support hρc
  have hsupp : Function.support (fun z ↦ ρ (y - z)) ⊆ Metric.closedBall y r := by
    intro z hz
    have h2 := hρr (subset_tsupport _ hz)
    rw [Metric.mem_closedBall, dist_zero_right] at h2
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact h2
  have hint : Integrable (fun z ↦ ρ (y - z)) μ := by
    refine (integrableOn_iff_integrable_of_support_subset hsupp).1 ?_
    exact Measure.integrableOn_of_bounded hfin.ne hφc.aestronglyMeasurable (M := M)
      (Eventually.of_forall fun z ↦ hM _)
  -- Step 3: by the operator-norm criterion it suffices that `|Du(y) w| ≤ A |w|`,
  -- `A = ∫ ρ(y - z) dμ(z) ≥ 0`.
  refine ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun z ↦ hρ0 _) fun w ↦ ?_
  -- Step 4: `Du(y) w = ∫_G Dρ(y - z) w dz = ∫ ρ(y - z) ⟨w, ν(z)⟩ dμ(z)`.
  rw [deGiorgiSobIndMFL_fderiv_setIntegral_apply N G ρ hG hρ hρc y w,
    deGiorgiSobIndMFL_setIntegral_fderiv_kernel_eq N U G μ ν hU hGG ρ r y w hρ hρc hρr hyU,
    ← integral_mul_const]
  -- Step 5: `ρ ≥ 0`, `|ν| = 1` `μ`-a.e. and Cauchy–Schwarz give the integrable majorant
  -- `ρ(y - ·) |w|`.
  refine norm_integral_le_of_norm_le (hint.mul_const _) ?_
  filter_upwards [hGG.2.2.2.1] with z hz
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hρ0 _)]
  refine mul_le_mul_of_nonneg_left ?_ (hρ0 _)
  calc ‖inner ℝ w (ν z)‖ ≤ ‖w‖ * ‖ν z‖ := by
        rw [Real.norm_eq_abs]; exact abs_real_inner_le_norm _ _
    _ = ‖w‖ := by rw [hz, mul_one]
/-- Fubini swap for the mollified weight: the last step of the bound on the derivative of a
mollified indicator used with Simon Ch. 2, Lemma 2.5 (p. 49, `chapter-02.txt` lines 543–596) in
the proof of Ch. 3, Theorem 4.3. Let `ζ, ρ` be continuous with compact support,
`tsupport ρ ⊆ B̄_r(0)`, and `μ(K') < ∞` for `K' = cthickening r (tsupport ζ)`. Then
`y ↦ ζ(y) ∫ ρ(y - z) dμ(z)` is `Lᴺ`-integrable and
`∫ ζ(y) (∫ ρ(y - z) dμ(z)) dy = ∫ (∫ ζ(y) ρ(y - z) dy) dμ(z)`. The integrand
`F(y, z) = ζ(y) ρ(y - z)` vanishes unless `y ∈ tsupport ζ` and `z ∈ K'`. It is bounded and
continuous with support in `tsupport ζ × ℝᴺ`, hence integrable for `Lᴺ ⊗ μ⌞K'`; `μ⌞K'` is
finite, so `μ` need not be s-finite. Fubini's theorem for `Lᴺ` and `μ⌞K'` gives the identity once
`μ⌞K'` is replaced by `μ` in the inner and outer integrals, whose integrands vanish off `K'`. -/
theorem Submission.deGiorgiSobIndMFL_integral_mul_swap : ∀ (N : ℕ) (μ : Measure (Rn N)) (ζ ρ : Rn N → ℝ) (r : ℝ), Continuous ζ → HasCompactSupport ζ → Continuous ρ → HasCompactSupport ρ → tsupport ρ ⊆ Metric.closedBall (0 : Rn N) r → μ (Metric.cthickening r (tsupport ζ)) < ∞ → Integrable (fun y ↦ ζ y * (∫ z, ρ (y - z) ∂μ)) ∧ ∫ y, ζ y * (∫ z, ρ (y - z) ∂μ) = ∫ z, (∫ y, ζ y * ρ (y - z)) ∂μ := by
  intro N μ ζ ρ r hζ hζc hρ hρc hρr hfin
  set K' := Metric.cthickening r (tsupport ζ)
  -- Step 1: `F(y, z) = ζ y * ρ (y - z)` vanishes unless `y ∈ tsupport ζ` and `z ∈ K'`.
  have hvan : ∀ y z, z ∉ K' → ζ y * ρ (y - z) = 0 := by
    intro y z hz
    by_contra hne
    have hy : y ∈ tsupport ζ := subset_tsupport _ (left_ne_zero_of_mul hne)
    have hyz := hρr (subset_tsupport _ (right_ne_zero_of_mul hne))
    rw [Metric.mem_closedBall, dist_zero_right] at hyz
    exact hz (Metric.mem_cthickening_of_dist_le z y r _ hy
      (by rw [dist_eq_norm, norm_sub_rev]; exact hyz))
  -- Step 2: `μ' = μ⌞K'` is a finite measure.
  have : IsFiniteMeasure (μ.restrict K') := isFiniteMeasure_restrict.2 hfin.ne
  -- Step 3: `F` is continuous, bounded by `Mζ * Mρ` and supported in `tsupport ζ × ℝᴺ`, a set of
  -- finite `Lᴺ ⊗ μ'` measure, so it is `Lᴺ ⊗ μ'`-integrable.
  have hFc : Continuous (Function.uncurry fun y z : Rn N ↦ ζ y * ρ (y - z)) :=
    (hζ.comp continuous_fst).mul (hρ.comp (continuous_fst.sub continuous_snd))
  obtain ⟨Mζ, hMζ⟩ := hζ.bounded_above_of_compact_support hζc
  obtain ⟨Mρ, hMρ⟩ := hρ.bounded_above_of_compact_support hρc
  have hFint : Integrable (Function.uncurry fun y z : Rn N ↦ ζ y * ρ (y - z))
      ((volume : Measure (Rn N)).prod (μ.restrict K')) := by
    have hsupp : Function.support (Function.uncurry fun y z : Rn N ↦ ζ y * ρ (y - z)) ⊆
        tsupport ζ ×ˢ univ := fun p hp ↦ ⟨subset_tsupport _ (left_ne_zero_of_mul hp), trivial⟩
    refine (integrableOn_iff_integrable_of_support_subset hsupp).1 ?_
    refine Measure.integrableOn_of_bounded ?_ hFc.aestronglyMeasurable (M := Mζ * Mρ)
      (Eventually.of_forall fun p ↦ ?_)
    · rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top hζc.isCompact.measure_lt_top.ne (measure_ne_top _ _)
    · simp only [Function.uncurry, norm_mul]
      exact mul_le_mul (hMζ _) (hMρ _) (norm_nonneg _) ((norm_nonneg _).trans (hMζ p.1))
  -- Step 5: `∫ F(y, z) dμ'(z) = ∫ F(y, z) dμ(z) = ζ y * ∫ ρ (y - z) dμ(z)`.
  have hin : ∀ y, ∫ z in K', ζ y * ρ (y - z) ∂μ = ζ y * ∫ z, ρ (y - z) ∂μ := by
    intro y
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ hvan y z hz,
      integral_const_mul]
  -- Step 6: `H z = ∫ F(y, z) dy` vanishes off `K'`, so `∫ H dμ' = ∫ H dμ`.
  have hout : ∫ z in K', (∫ y, ζ y * ρ (y - z)) ∂μ = ∫ z, (∫ y, ζ y * ρ (y - z)) ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ ?_
    simp [hvan _ z hz]
  -- Steps 4 and 7: Fubini for `Lᴺ` and `μ'` (with integrability of the inner integral), then
  -- Steps 5 and 6.
  refine ⟨hFint.integral_prod_left.congr (Eventually.of_forall fun y ↦ hin y), ?_⟩
  rw [← hout, ← integral_integral_swap hFint]
  exact integral_congr_ae (Eventually.of_forall fun y ↦ (hin y).symm)

/-- Weighted bound on the derivative of a mollified indicator: Simon Ch. 2, Lemma 2.5 (3)
(p. 49, `chapter-02.txt` lines 543–596), as used in the proof of Ch. 3, Theorem 4.3
(`chapter-03.txt` lines 689–705), for a general `C¹` kernel `ρ` and a Gauss–Green pair `(μ, ν)`
of `G` in `U`. Let `ζ ≥ 0` be continuous with compact support, `ρ ≥ 0` be `C¹` with compact
support and `tsupport ρ ⊆ B̄_r(0)`, and `K' = cthickening r (tsupport ζ) ⊆ U`. Then
`u(x) = ∫_G ρ(x - z) dz` satisfies `∫ ζ |Du| dLᴺ ≤ ∫ (∫ ζ(y) ρ(y - z) dy) dμ(z)`.
`K'` is a compact subset of `U`, so `μ(K') < ∞`. For `y ∈ tsupport ζ`, `B̄_r(y) ⊆ K' ⊆ U`, hence
`|Du(y)| ≤ ∫ ρ(y - z) dμ(z)` (`deGiorgiSobIndMFL_norm_fderiv_le`); off `tsupport ζ` both sides
vanish. Integrating against `ζ` and swapping the integrals (`deGiorgiSobIndMFL_integral_mul_swap`)
gives the bound. -/
theorem Submission.deGiorgiSobInd_mollified_fderiv_le : ∀ (N : ℕ) (U G : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → NullMeasurableSet G volume → IsGaussGreenPair U G μ ν → ∀ (ζ ρ : Rn N → ℝ) (r : ℝ), Continuous ζ → HasCompactSupport ζ → (∀ y, 0 ≤ ζ y) → ContDiff ℝ 1 ρ → HasCompactSupport ρ → (∀ y, 0 ≤ ρ y) → tsupport ρ ⊆ Metric.closedBall (0 : Rn N) r → Metric.cthickening r (tsupport ζ) ⊆ U → ∫ y, ζ y * ‖fderiv ℝ (fun x ↦ ∫ z in G, ρ (x - z)) y‖ ≤ ∫ z, (∫ y, ζ y * ρ (y - z)) ∂μ := by
  intro N U G μ ν hU hG hGG ζ ρ r hζ hζc hζ0 hρ hρc hρ0 hρr hK
  -- (a) `K' = cthickening r (tsupport ζ)` is a compact subset of `U`, so `μ K' < ∞`.
  have hK'fin : μ (Metric.cthickening r (tsupport ζ)) < ∞ :=
    hGG.2.1 _ hζc.isCompact.cthickening hK
  -- (b) Fubini: `y ↦ ζ y * ∫ ρ (y - z) dμ` is integrable, and its integral is the right-hand side.
  obtain ⟨hint, hswap⟩ :=
    Submission.deGiorgiSobIndMFL_integral_mul_swap N μ ζ ρ r hζ hζc hρ.continuous hρc hρr hK'fin
  rw [← hswap]
  -- (c) Pointwise comparison of the nonnegative integrands, then (d) monotonicity of the integral.
  refine integral_mono_of_nonneg
    (Eventually.of_forall fun y ↦ mul_nonneg (hζ0 y) (norm_nonneg _)) hint
    (Eventually.of_forall fun y ↦ ?_)
  by_cases hy : y ∈ tsupport ζ
  · -- `B̄_r(y) ⊆ K' ⊆ U`, so the pointwise bound applies at `y`.
    exact mul_le_mul_of_nonneg_left
      (Submission.deGiorgiSobIndMFL_norm_fderiv_le N U G μ ν hU hG hGG ρ r y hρ hρc hρ0 hρr
        ((Metric.closedBall_subset_cthickening hy r).trans hK)) (hζ0 y)
  · simp [image_eq_zero_of_notMem_tsupport hy]
/-- **Mollified test functions converge against `μ`** (Simon Ch. 3, proof of Theorem 4.3, p. 83:
the passage `σ ↓ 0` in the Sobolev inequality for `ζ χ_E`, via Ch. 2, 2.5). Let `ζ ∈ C_c(ℝᴺ)`
with `μ(cthickening δ (spt ζ)) < ∞`, and let `ρ_j ≥ 0` be continuous with `∫ ρ_j dLᴺ = 1` and
`spt ρ_j ⊆ B̄_{r_j}(0)`, where `r_j ≤ δ` and `r_j → 0`. Then
`∫ (∫ ζ(y) ρ_j(y - z) dy) dμ(z) → ∫ ζ dμ`: `ζ̃_j(z) = ∫ ζ(y) ρ_j(y - z) dy` is measurable,
vanishes off `cthickening δ (spt ζ)`, is bounded by `sup |ζ|`, and tends to `ζ` pointwise by
uniform continuity of `ζ`, so dominated convergence applies. -/
theorem Submission.deGiorgiSobInd_mollified_integral_tendsto : ∀ (N : ℕ) (μ : Measure (Rn N)) (ζ : Rn N → ℝ) (ρ : ℕ → Rn N → ℝ) (r : ℕ → ℝ) (δ : ℝ), Continuous ζ → HasCompactSupport ζ → μ (Metric.cthickening δ (tsupport ζ)) < ∞ → (∀ j, Continuous (ρ j)) → (∀ j y, 0 ≤ ρ j y) → (∀ j, ∫ y, ρ j y = 1) → (∀ j, tsupport (ρ j) ⊆ Metric.closedBall (0 : Rn N) (r j)) → (∀ j, r j ≤ δ) → Tendsto r atTop (𝓝 0) → Tendsto (fun j ↦ ∫ z, (∫ y, ζ y * ρ j (y - z)) ∂μ) atTop (𝓝 (∫ z, ζ z ∂μ)) := by
  intro N μ ζ ρ r δ hζc hζs hμK hρc hρnn hρint hρsupp hrδ hr
  -- Notation: `K' = cthickening δ (tsupport ζ)` and `C ≥ sup |ζ|`.
  set K' := Metric.cthickening δ (tsupport ζ)
  obtain ⟨C, hC⟩ := hζc.bounded_above_of_compact_support hζs
  -- Step 1: `ρ j` is integrable, `∫ ρ j (y - z) dy = 1`, and `ρ j (y - z) ≠ 0` forces
  -- `|y - z| ≤ r j`.
  have hρi : ∀ j, Integrable (ρ j) := fun j ↦
    Integrable.of_integral_ne_zero (by rw [hρint j]; exact one_ne_zero)
  have hmass : ∀ j z, ∫ y, ρ j (y - z) = 1 := fun j z ↦ by
    rw [integral_sub_right_eq_self (ρ j) z, hρint j]
  have hsupp : ∀ j y z, ρ j (y - z) ≠ 0 → dist y z ≤ r j := fun j y z h ↦ by
    have := hρsupp j (subset_tsupport _ h)
    rwa [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm] at this
  have hint : ∀ j z, Integrable (fun y ↦ ζ y * ρ j (y - z)) := fun j z ↦
    ((hρi j).comp_sub_right z).bdd_mul hζc.aestronglyMeasurable (Eventually.of_forall hC)
  -- Step 2: `|ζ̃_j| ≤ C · 1_{K'}`.
  have hbound : ∀ j z, ‖∫ y, ζ y * ρ j (y - z)‖ ≤ K'.indicator (fun _ ↦ C) z := by
    intro j z
    by_cases hz : z ∈ K'
    · rw [indicator_of_mem hz]
      calc ‖∫ y, ζ y * ρ j (y - z)‖ ≤ ∫ y, C * ρ j (y - z) := by
            refine norm_integral_le_of_norm_le (((hρi j).comp_sub_right z).const_mul C)
              (Eventually.of_forall fun y ↦ ?_)
            rw [norm_mul, Real.norm_of_nonneg (hρnn j _)]
            exact mul_le_mul_of_nonneg_right (hC y) (hρnn j _)
        _ = C := by rw [integral_const_mul, hmass, mul_one]
    · rw [indicator_of_notMem hz]
      have h0 : ∀ y, ζ y * ρ j (y - z) = 0 := by
        intro y
        by_contra h
        obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
        exact hz (Metric.mem_cthickening_of_dist_le z y δ _ (subset_tsupport _ h1)
          ((dist_comm z y).le.trans ((hsupp j y z h2).trans (hrδ j))))
      simp [h0]
  -- Step 3: each `ζ̃_j` is strongly measurable.
  have hmeas : ∀ j, AEStronglyMeasurable (fun z ↦ ∫ y, ζ y * ρ j (y - z)) μ := fun j ↦ by
    have h : StronglyMeasurable (fun p : Rn N × Rn N ↦ ζ p.2 * ρ j (p.2 - p.1)) :=
      ((hζc.comp continuous_snd).mul
        ((hρc j).comp (continuous_snd.sub continuous_fst))).stronglyMeasurable
    exact h.integral_prod_right'.aestronglyMeasurable
  -- Step 4: `ζ̃_j → ζ` pointwise, by uniform continuity of `ζ`.
  have hlim : ∀ z, Tendsto (fun j ↦ ∫ y, ζ y * ρ j (y - z)) atTop (𝓝 (ζ z)) := by
    intro z
    have huc := hζs.uniformContinuous_of_continuous hζc
    rw [Metric.uniformContinuous_iff] at huc
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨η, hη, hηε⟩ := huc (ε / 2) (half_pos hε)
    obtain ⟨j₀, hj₀⟩ := (Metric.tendsto_atTop.1 hr) η hη
    refine ⟨j₀, fun j hj ↦ ?_⟩
    have hrj : r j < η := by
      have := hj₀ j hj
      rw [Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans_lt this
    have hdiff : (∫ y, ζ y * ρ j (y - z)) - ζ z = ∫ y, (ζ y - ζ z) * ρ j (y - z) := by
      simp_rw [sub_mul]
      rw [integral_sub (hint j z) (((hρi j).comp_sub_right z).const_mul _), integral_const_mul,
        hmass, mul_one]
    rw [Real.dist_eq, hdiff]
    calc |∫ y, (ζ y - ζ z) * ρ j (y - z)| ≤ ∫ y, ε / 2 * ρ j (y - z) := by
          rw [← Real.norm_eq_abs]
          refine norm_integral_le_of_norm_le (((hρi j).comp_sub_right z).const_mul _)
            (Eventually.of_forall fun y ↦ ?_)
          rw [norm_mul, Real.norm_of_nonneg (hρnn j _)]
          by_cases hy : ρ j (y - z) = 0
          · rw [hy]; simp
          · refine mul_le_mul_of_nonneg_right ?_ (hρnn j _)
            rw [← dist_eq_norm]
            exact (hηε ((hsupp j y z hy).trans_lt hrj)).le
      _ = ε / 2 := by rw [integral_const_mul, hmass, mul_one]
      _ < ε := half_lt_self hε
  -- Step 5: dominated convergence with the bound `C · 1_{K'} ∈ L¹(μ)`.
  have hK'meas : MeasurableSet K' := Metric.isClosed_cthickening.measurableSet
  refine tendsto_integral_of_dominated_convergence (K'.indicator fun _ ↦ C) hmeas ?_
    (fun j ↦ Eventually.of_forall (hbound j)) (Eventually.of_forall hlim)
  exact (integrable_indicator_iff hK'meas).2 (integrableOn_const hμK.ne)
/-- **Gagliardo–Nirenberg–Sobolev inequality, `L¹` case** (Simon Ch. 3, proof of Theorem 4.3,
Step 7; [GT01, Thm 7.10]): for `n ≥ 1` and a `C¹` compactly supported `v : ℝ^{n+1} → ℝ`,
`‖v‖_{L^{(n+1)/n}} ≤ c ∫ |Dv|`, here with `c = 1`. The module
`Mathlib.Analysis.FunctionalSpaces.SobolevInequality` is outside the frozen imports, so its
argument is replayed inline: the grid-lines lemma (Hölder's inequality and induction over the
integrated coordinates, as in Mathlib's
`MeasureTheory.GridLines.T_insert_le_T_lmarginal_singleton`), the bound
`|v(x)| ≤ ∫ |Dv(x + t eⱼ)| dt` along each coordinate line, and the volume-preserving
identification `WithLp.toLp 2 : (Fin (n + 1) → ℝ) → ℝ^{n+1}`. -/
theorem Submission.deGiorgiDensSob_gns_contDiff : ∀ (n : ℕ), 0 < n → ∃ c : ℝ, 0 < c ∧ ∀ v : Rn (n + 1) → ℝ, ContDiff ℝ 1 v → HasCompactSupport v → eLpNorm v ((n + 1 : ℝ≥0∞) / n) volume ≤ ENNReal.ofReal (c * ∫ y, ‖fderiv ℝ v y‖) := by
  intro n hn
  refine ⟨1, one_pos, fun v hv hvs => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set p : ℝ := 1 / (n : ℝ) with hp_def
  have hp0 : 0 ≤ p := by positivity
  -- Grid-lines lemma (Mathlib `GridLines.T_insert_le_T_lmarginal_singleton` and induction)
  have grid : ∀ (μ : Fin (n + 1) → Measure ℝ) [∀ i, SigmaFinite (μ i)] (s : Finset (Fin (n + 1))),
      ((s.card : ℝ) - 1) * p ≤ 1 → ∀ g : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable g → ∀ x,
      (∫⋯∫⁻_s, g ^ (1 - ((s.card : ℝ) - 1) * p) * ∏ j ∈ s, (∫⋯∫⁻_{j}, g ∂μ) ^ p ∂μ) x ≤
        (∫⋯∫⁻_s, g ∂μ) x ^ (1 + p) := by
    intro μ _ s
    have step : ∀ (s : Finset (Fin (n + 1))) (i : Fin (n + 1)), i ∉ s → (s.card : ℝ) * p ≤ 1 →
        ∀ f : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable f →
        (∫⋯∫⁻_insert i s, f ^ (1 - (s.card : ℝ) * p) *
            ∏ j ∈ insert i s, (∫⋯∫⁻_{j}, f ∂μ) ^ p ∂μ) ≤
          ∫⋯∫⁻_s, (∫⋯∫⁻_{i}, f ∂μ) ^ (1 - ((s.card : ℝ) - 1) * p) *
            ∏ j ∈ s, (∫⋯∫⁻_{j}, (∫⋯∫⁻_{i}, f ∂μ) ∂μ) ^ p ∂μ := by
      intro s i hi hp f hf
      calc (∫⋯∫⁻_insert i s, f ^ (1 - (s.card : ℝ) * p) *
              ∏ j ∈ insert i s, (∫⋯∫⁻_{j}, f ∂μ) ^ p ∂μ)
          = ∫⋯∫⁻_s, (fun x ↦ ∫⁻ (t : ℝ), (f (Function.update x i t) ^ (1 - (s.card : ℝ) * p)
              * ∏ j ∈ insert i s, (∫⋯∫⁻_{j}, f ∂μ) (Function.update x i t) ^ p) ∂(μ i)) ∂μ := by
            rw [lmarginal_insert' _ _ hi]
            · simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
            · change Measurable (fun x ↦ _)
              simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
              refine (hf.pow_const _).mul <| Finset.measurable_fun_prod _ ?_
              exact fun _ _ ↦ hf.lmarginal μ |>.pow_const _
        _ ≤ _ := lmarginal_mono (s := s) (fun x ↦ ?_)
      simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
      set X := Function.update x i
      have hF₁ : ∀ {j : Fin (n + 1)}, Measurable fun t ↦ (∫⋯∫⁻_{j}, f ∂μ) (X t) :=
        fun {_} ↦ hf.lmarginal μ |>.comp <| measurable_update _
      have hF₀ : Measurable fun t ↦ f (X t) := hf.comp <| measurable_update _
      let k : ℝ := s.card
      have hk' : 0 ≤ 1 - k * p := by linarith only [hp]
      calc ∫⁻ t, f (X t) ^ (1 - k * p)
              * ∏ j ∈ insert i s, (∫⋯∫⁻_{j}, f ∂μ) (X t) ^ p ∂(μ i)
          = ∫⁻ t, (∫⋯∫⁻_{i}, f ∂μ) (X t) ^ p * (f (X t) ^ (1 - k * p)
              * ∏ j ∈ s, ((∫⋯∫⁻_{j}, f ∂μ) (X t) ^ p)) ∂(μ i) := by
            clear_value X
            congr! 2 with t
            simp_rw [Finset.prod_insert hi]
            ring_nf
        _ = (∫⋯∫⁻_{i}, f ∂μ) x ^ p *
              ∫⁻ t, f (X t) ^ (1 - k * p) * ∏ j ∈ s, ((∫⋯∫⁻_{j}, f ∂μ) (X t)) ^ p ∂(μ i) := by
            have : ∀ t, (∫⋯∫⁻_{i}, f ∂μ) (X t) = (∫⋯∫⁻_{i}, f ∂μ) x := by
              intro t
              rw [lmarginal_update_of_mem]
              exact Iff.mpr Finset.mem_singleton rfl
            simp_rw [this]
            rw [lintegral_const_mul]
            exact (hF₀.pow_const _).mul <| Finset.measurable_fun_prod _ fun _ _ ↦ hF₁.pow_const _
        _ ≤ (∫⋯∫⁻_{i}, f ∂μ) x ^ p *
              ((∫⁻ t, f (X t) ∂μ i) ^ (1 - k * p)
              * ∏ j ∈ s, (∫⁻ t, (∫⋯∫⁻_{j}, f ∂μ) (X t) ∂μ i) ^ p) := by
            gcongr
            apply ENNReal.lintegral_mul_prod_norm_pow_le
            · exact hF₀.aemeasurable
            · intros
              exact hF₁.aemeasurable
            · simp only [Finset.sum_const, nsmul_eq_mul]
              ring
            · exact hk'
            · exact fun _ _ ↦ hp0
        _ = (∫⋯∫⁻_{i}, f ∂μ) x ^ p *
              ((∫⋯∫⁻_{i}, f ∂μ) x ^ (1 - k * p) * ∏ j ∈ s, (∫⋯∫⁻_{i, j}, f ∂μ) x ^ p) := by
            congr! 2
            · rw [lmarginal_singleton]
            refine Finset.prod_congr rfl fun j hj => ?_
            have hi' : i ∉ ({j} : Finset (Fin (n + 1))) := by
              simp only [Finset.mem_singleton] at hj ⊢
              exact fun h ↦ hi (h ▸ hj)
            rw [lmarginal_insert _ hf hi']
        _ = (∫⋯∫⁻_{i}, f ∂μ) x ^ (p + (1 - k * p)) *
              ∏ j ∈ s, (∫⋯∫⁻_{i, j}, f ∂μ) x ^ p := by
            rw [ENNReal.rpow_add_of_nonneg]
            · ring
            · exact hp0
            · exact hk'
        _ ≤ (∫⋯∫⁻_{i}, f ∂μ) x ^ (1 - ((s.card : ℝ) - 1) * p) *
              ∏ j ∈ s, (∫⋯∫⁻_{j}, (∫⋯∫⁻_{i}, f ∂μ) ∂μ) x ^ p := by
            congr! 2 with j hj
            · ring
            · congr! 1
              rw [← lmarginal_union μ f hf]
              · congr
                rw [Finset.union_comm]
                rfl
              · rw [Finset.disjoint_singleton]
                exact fun h ↦ hi (h ▸ hj)
    induction s using Finset.induction_on with
    | empty =>
      intro _ g _ x
      simp only [lmarginal_empty, Finset.prod_empty, mul_one, Finset.card_empty, Nat.cast_zero,
        Pi.pow_apply]
      ring_nf
      exact le_rfl
    | insert i s hi ih =>
      intro hcard g hg x
      rw [Finset.card_insert_of_notMem hi] at hcard ⊢
      have e : (((s.card + 1 : ℕ) : ℝ) - 1) = s.card := by push_cast; ring
      rw [e] at hcard ⊢
      have hs' : ((s.card : ℝ) - 1) * p ≤ 1 := by nlinarith
      calc _ ≤ _ := step s i hi hcard g hg x
        _ ≤ (∫⋯∫⁻_s, (∫⋯∫⁻_{i}, g ∂μ) ∂μ) x ^ (1 + p) := ih hs' _ (hg.lmarginal μ) x
        _ = (∫⋯∫⁻_insert i s, g ∂μ) x ^ (1 + p) := by
          rw [← lmarginal_union' μ g hg (Finset.disjoint_singleton_left.2 hi), ← Finset.insert_eq]
  -- coordinates: `L : (Fin (n + 1) → ℝ) ≃L[ℝ] Rn (n + 1)` is `WithLp.toLp 2`
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm
  have hL : ∀ x, L x = WithLp.toLp 2 x := fun x => rfl
  -- one-dimensional bound along coordinate lines (fundamental theorem of calculus)
  have ftc : ∀ (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)),
      ‖v (L x)‖ₑ ≤ ∫⁻ t, ‖fderiv ℝ v (L (Function.update x j t))‖ₑ := by
    intro x j
    have hφ : ContDiff ℝ 1 (fun t : ℝ => v (L (Function.update x j t))) :=
      hv.comp (L.contDiff.comp (contDiff_update 1 x j))
    have hφs : HasCompactSupport (fun t : ℝ => v (L (Function.update x j t))) :=
      hvs.comp_isClosedEmbedding
        (L.toHomeomorph.isClosedEmbedding.comp (isClosedEmbedding_update x j))
    have hder : ∀ t, HasDerivAt (fun t : ℝ => v (L (Function.update x j t)))
        (fderiv ℝ v (L (Function.update x j t)) (L (Pi.single j 1))) t := by
      intro t
      have h1 : HasDerivAt (Function.update x j) (Pi.single j (1 : ℝ)) t := by
        rw [hasDerivAt_pi]
        intro k
        by_cases hk : k = j
        · subst hk
          simp only [Function.update_self, Pi.single_eq_same]
          exact hasDerivAt_id' t
        · simpa [Function.update_of_ne hk, Pi.single_eq_of_ne hk] using hasDerivAt_const t (x k)
      exact ((hv.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t
        (L.hasFDerivAt.comp_hasDerivAt t h1)
    have hsingle : ‖L (Pi.single j (1 : ℝ))‖ₑ = 1 := by
      rw [hL, PiLp.toLp_single]
      simp [enorm_eq_nnnorm, PiLp.nnnorm_single]
    calc ‖v (L x)‖ₑ = ‖(fun t : ℝ => v (L (Function.update x j t))) (x j)‖ₑ := by
          simp only [Function.update_eq_self]
      _ ≤ ∫⁻ t in Iic (x j), ‖deriv (fun t : ℝ => v (L (Function.update x j t))) t‖ₑ :=
          HasCompactSupport.enorm_le_lintegral_Ici_deriv hφ hφs (x j)
      _ ≤ ∫⁻ t, ‖deriv (fun t : ℝ => v (L (Function.update x j t))) t‖ₑ :=
          setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ t, ‖fderiv ℝ v (L (Function.update x j t))‖ₑ := by
          refine lintegral_mono fun t => ?_
          rw [(hder t).deriv]
          refine (ContinuousLinearMap.le_opENorm _ _).trans ?_
          rw [hsingle, mul_one]
  -- the main inequality `∫ |v| ^ (1 + p) ≤ (∫ |Dv|) ^ (1 + p)`
  have hDv : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  have hg : Measurable fun x : Fin (n + 1) → ℝ => ‖fderiv ℝ v (L x)‖ₑ :=
    (hDv.comp L.continuous).enorm.measurable
  have hcard : (((Finset.univ : Finset (Fin (n + 1))).card : ℝ) - 1) = n := by simp
  have hnp : (n : ℝ) * p = 1 := by rw [hp_def]; field_simp
  have hpow : ∀ a : ℝ≥0∞, a ^ (1 + p) = ∏ _j : Fin (n + 1), a ^ p := by
    intro a
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    congr 1
    push_cast
    linarith
  have main : ∫⁻ y, ‖v y‖ₑ ^ (1 + p) ≤ (∫⁻ y, ‖fderiv ℝ v y‖ₑ) ^ (1 + p) := by
    have e1 : ∫⁻ y, ‖v y‖ₑ ^ (1 + p) = ∫⁻ x : Fin (n + 1) → ℝ, ‖v (L x)‖ₑ ^ (1 + p) :=
      ((PiLp.volume_preserving_toLp (Fin (n + 1))).lintegral_comp
        (hv.continuous.enorm.measurable.pow_const _)).symm
    have e2 : ∫⁻ y, ‖fderiv ℝ v y‖ₑ = ∫⁻ x : Fin (n + 1) → ℝ, ‖fderiv ℝ v (L x)‖ₑ :=
      ((PiLp.volume_preserving_toLp (Fin (n + 1))).lintegral_comp hDv.enorm.measurable).symm
    have hgrid := grid (fun _ => volume) Finset.univ (by rw [hcard, hnp])
      (fun x : Fin (n + 1) → ℝ => ‖fderiv ℝ v (L x)‖ₑ) hg 0
    simp only [lmarginal_univ, Pi.mul_apply, Pi.pow_apply, Finset.prod_apply,
      lmarginal_singleton, hcard, hnp, sub_self, ENNReal.rpow_zero, one_mul] at hgrid
    rw [e1, e2, volume_pi]
    refine le_trans (lintegral_mono fun x => ?_) hgrid
    rw [hpow]
    gcongr with j
    exact ftc x j
  -- conversion to `eLpNorm`
  have hq0 : ((n + 1 : ℝ≥0∞) / n) ≠ 0 := by simp [ENNReal.div_eq_zero_iff]
  have hqtop : ((n + 1 : ℝ≥0∞) / n) ≠ ∞ := by simp [ENNReal.div_eq_top, hn.ne']
  have hqr : ((n + 1 : ℝ≥0∞) / n).toReal = 1 + p := by
    rw [ENNReal.toReal_div, ENNReal.toReal_add (by simp) (by simp)]
    simp only [ENNReal.toReal_natCast, ENNReal.toReal_one]
    rw [hp_def]
    field_simp
  have hint : Integrable (fderiv ℝ v) volume :=
    hDv.integrable_of_hasCompactSupport (hvs.fderiv ℝ)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop hv.continuous.aestronglyMeasurable, hqr,
    one_mul, ofReal_integral_norm_eq_lintegral_enorm hint]
  have h1p : (0 : ℝ) < 1 + p := by positivity
  calc (∫⁻ y, ‖v y‖ₑ ^ (1 + p)) ^ (1 / (1 + p))
      ≤ ((∫⁻ y, ‖fderiv ℝ v y‖ₑ) ^ (1 + p)) ^ (1 / (1 + p)) :=
        ENNReal.rpow_le_rpow main (by positivity)
    _ = ∫⁻ y, ‖fderiv ℝ v y‖ₑ := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel h1p.ne', ENNReal.rpow_one]
/-- **One-dimensional endpoint Sobolev inequality** (Simon Ch. 3, proof of Theorem 4.3, Step 7
"Constants", erratum E6: for `N = 1` the Sobolev inequality is replaced by
`sup |w| ≤ ½ ∫ |w'|`). Every `C¹` function `v : ℝ¹ → ℝ` with compact support satisfies
`‖v‖_∞ ≤ ½ ∫ ‖Dv‖ dL¹`. Parametrise `ℝ¹` by the isometric, measure-preserving map
`ι(t) = t e₀` (`e₀ = EuclideanSpace.single 0 1`) and put `f = v ∘ ι`, so
`|f'(t)| = |Dv(ι t) e₀| ≤ ‖Dv(ι t)‖`. The fundamental theorem of calculus from both ends gives
`f(t) = ∫_{(-∞, t]} f' = -∫_{(t, ∞)} f'`, hence `2 |f(t)| ≤ ∫ |f'| ≤ ∫_ℝ ‖Dv(ι t)‖ dt = ∫ ‖Dv‖ dL¹`.
Since `v(y) = f(y 0)`, the bound `|v| ≤ ½ ∫ ‖Dv‖` holds everywhere, hence for the essential
supremum. -/
theorem Submission.deGiorgiDensSob_one_dim_contDiff : ∀ v : Rn 1 → ℝ, ContDiff ℝ 1 v → HasCompactSupport v → eLpNorm v ∞ volume ≤ ENNReal.ofReal (1 / 2 * ∫ y, ‖fderiv ℝ v y‖) := by
  intro v hv hvs
  -- Step 1: the isometric parametrisation `ι(t) = t e₀` of `ℝ¹`, with `y = ι(y 0)`.
  set e₀ : Rn 1 := EuclideanSpace.single 0 1 with he₀
  have hne₀ : ‖e₀‖ = 1 := by simp [he₀]
  let ι : ℝ →L[ℝ] Rn 1 := (ContinuousLinearMap.id ℝ ℝ).smulRight e₀
  have hι : ∀ t, ι t = t • e₀ := fun t ↦ by simp [ι]
  have hιnorm : ∀ t, ‖ι t‖ = ‖t‖ := fun t ↦ by rw [hι, norm_smul, hne₀, mul_one]
  have hιce : Topology.IsClosedEmbedding ι :=
    (AddMonoidHomClass.isometry_of_norm ι hιnorm).isClosedEmbedding
  have hιsurj : ∀ y : Rn 1, ι (y 0) = y := by
    intro y
    ext i
    fin_cases i
    simp [hι, he₀]
  -- Step 2: `ι` agrees with the measure-preserving equivalence
  -- `toLp 2 ∘ (funUnique (Fin 1) ℝ).symm`, so `∫_ℝ ‖Dv(ι t)‖ dt = ∫_{ℝ¹} ‖Dv‖ dL¹`.
  let E : ℝ ≃ᵐ Rn 1 :=
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.trans (MeasurableEquiv.toLp 2 (Fin 1 → ℝ))
  have hE : MeasurePreserving E volume volume :=
    (PiLp.volume_preserving_toLp (Fin 1)).comp (volume_preserving_funUnique (Fin 1) ℝ).symm
  have hEι : ∀ t, E t = ι t := by
    intro t
    ext i
    fin_cases i
    simp [E, hι, he₀]
  have hchange : ∫ t, ‖fderiv ℝ v (ι t)‖ = ∫ y, ‖fderiv ℝ v y‖ := by
    rw [← hE.integral_comp' (fun y ↦ ‖fderiv ℝ v y‖)]
    simp only [hEι]
  -- Step 3: `f = v ∘ ι` is `C¹` with compact support and `|f'(t)| ≤ ‖Dv(ι t)‖`.
  set f : ℝ → ℝ := v ∘ ι with hf_def
  have hf : ContDiff ℝ 1 f := hv.comp ι.contDiff
  have hfs : HasCompactSupport f := hvs.comp_isClosedEmbedding hιce
  have hderiv : ∀ t, HasDerivAt f (fderiv ℝ v (ι t) e₀) t := by
    intro t
    have h1 : HasDerivAt (ι : ℝ → Rn 1) e₀ t := by
      have hfun : (ι : ℝ → Rn 1) = fun s ↦ s • e₀ := funext hι
      rw [hfun]
      simpa using (hasDerivAt_id t).smul_const e₀
    exact HasFDerivAt.comp_hasDerivAt (x := t)
      (hv.differentiable one_ne_zero (ι t)).hasFDerivAt h1
  have hderiv_eq : ∀ t, deriv f t = fderiv ℝ v (ι t) e₀ := fun t ↦ (hderiv t).deriv
  have hdbound : ∀ t, ‖deriv f t‖ ≤ ‖fderiv ℝ v (ι t)‖ := by
    intro t
    rw [hderiv_eq]
    calc ‖fderiv ℝ v (ι t) e₀‖ ≤ ‖fderiv ℝ v (ι t)‖ * ‖e₀‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ v (ι t)‖ := by rw [hne₀, mul_one]
  -- Step 4: `f'` and `t ↦ ‖Dv(ι t)‖` are integrable, and `∫ |f'| ≤ ∫ ‖Dv(ι t)‖ dt`.
  have hdcont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hdint : Integrable (deriv f) := hdcont.integrable_of_hasCompactSupport hfs.deriv
  have hgint : Integrable (fun t ↦ ‖fderiv ℝ v (ι t)‖) := by
    have hc : Continuous (fun t ↦ ‖fderiv ℝ v (ι t)‖) :=
      ((hv.continuous_fderiv one_ne_zero).comp ι.continuous).norm
    exact hc.integrable_of_hasCompactSupport
      (((hvs.fderiv ℝ).norm).comp_isClosedEmbedding hιce)
  have hmono : ∫ s, ‖deriv f s‖ ≤ ∫ s, ‖fderiv ℝ v (ι s)‖ :=
    integral_mono hdint.norm hgint hdbound
  -- Step 5: FTC from the left, `∫_{(-∞, t]} f' = f(t)`.
  have hftc_left : ∀ t, ∫ s in Iic t, deriv f s = f t := fun t ↦
    hfs.integral_Iic_deriv_eq hf t
  -- Step 6: FTC from the right, `∫_{(t, ∞)} f' = 0 - f(t)`, as `f → 0` at `+∞`.
  have hlim_top : Tendsto f atTop (𝓝 0) := by
    have h := hfs
    rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at h
    exact (h.filter_mono _root_.atTop_le_cocompact).tendsto
  have hftc_right : ∀ t, ∫ s in Ioi t, deriv f s = 0 - f t := fun t ↦
    integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun s _ ↦ (hf.differentiable one_ne_zero s).hasDerivAt) hdint.integrableOn hlim_top
  -- Step 7: adding the two bounds, `2 |f(t)| ≤ ∫ |f'| ≤ ∫ ‖Dv‖ dL¹`.
  have hpt : ∀ t, ‖f t‖ ≤ 1 / 2 * ∫ y, ‖fderiv ℝ v y‖ := by
    intro t
    have h1 : ‖f t‖ ≤ ∫ s in Iic t, ‖deriv f s‖ := by
      rw [← hftc_left t]
      exact norm_integral_le_integral_norm _
    have h2 : ‖f t‖ ≤ ∫ s in Ioi t, ‖deriv f s‖ := by
      have : f t = -∫ s in Ioi t, deriv f s := by rw [hftc_right t]; ring
      rw [this, norm_neg]
      exact norm_integral_le_integral_norm _
    have h3 : (∫ s in Iic t, ‖deriv f s‖) + ∫ s in Ioi t, ‖deriv f s‖ = ∫ s, ‖deriv f s‖ :=
      intervalIntegral.integral_Iic_add_Ioi hdint.norm.integrableOn hdint.norm.integrableOn
    calc ‖f t‖ = 1 / 2 * (‖f t‖ + ‖f t‖) := by ring
      _ ≤ 1 / 2 * ((∫ s in Iic t, ‖deriv f s‖) + ∫ s in Ioi t, ‖deriv f s‖) := by gcongr
      _ = 1 / 2 * ∫ s, ‖deriv f s‖ := by rw [h3]
      _ ≤ 1 / 2 * ∫ s, ‖fderiv ℝ v (ι s)‖ := by gcongr
      _ = 1 / 2 * ∫ y, ‖fderiv ℝ v y‖ := by rw [hchange]
  -- Step 8: `v(y) = f(y 0)`, so `|v(y)| ≤ ½ ∫ ‖Dv‖ dL¹` for every `y ∈ ℝ¹`.
  have hall : ∀ y, ‖v y‖ ≤ 1 / 2 * ∫ y, ‖fderiv ℝ v y‖ := by
    intro y
    have := hpt (y 0)
    rwa [hf_def, Function.comp_apply, hιsurj] at this
  -- Step 9: the everywhere bound bounds the essential supremum `eLpNorm v ∞`.
  rw [eLpNorm_exponent_top hv.continuous.aestronglyMeasurable]
  exact eLpNormEssSup_le_of_ae_bound (ae_of_all _ hall)
/-- **Passing to the limit in a Sobolev bound along `C¹` approximations** (used in the proof of
Simon Ch. 3, Theorem 4.3, for the Sobolev inequality of Lipschitz functions). Let `S ⊆ ℝᴺ` be
compact and `v_j ∈ C¹(ℝᴺ)` with `tsupport v_j ⊆ S` and `‖Dv_j‖ ≤ K`, such that `v_j → u` and
`Dv_j → Du` `Lᴺ`-a.e. If `‖v_j‖_{L^p} ≤ c ∫ ‖Dv_j‖ dLᴺ` for every `j`, then
`‖u‖_{L^p} ≤ c ∫ ‖Du‖ dLᴺ`. Dominated convergence (with the bound `K 1_S`) gives
`∫ ‖Dv_j‖ → ∫ ‖Du‖`, and Fatou's lemma for `eLpNorm` gives `‖u‖_{L^p} ≤ liminf_j ‖v_j‖_{L^p}`. -/
theorem Submission.deGiorgiDensSob_eLpNorm_le_of_approx : ∀ (N : ℕ) (p : ℝ≥0∞) (c : ℝ) (K : ℝ≥0) (S : Set (Rn N)) (u : Rn N → ℝ) (v : ℕ → Rn N → ℝ), IsCompact S → (∀ j, ContDiff ℝ 1 (v j)) → (∀ j, tsupport (v j) ⊆ S) → (∀ j y, ‖fderiv ℝ (v j) y‖ ≤ K) → (∀ᵐ y ∂(volume : Measure (Rn N)), Tendsto (fun j ↦ v j y) atTop (𝓝 (u y))) → (∀ᵐ y ∂(volume : Measure (Rn N)), Tendsto (fun j ↦ fderiv ℝ (v j) y) atTop (𝓝 (fderiv ℝ u y))) → (∀ j, eLpNorm (v j) p volume ≤ ENNReal.ofReal (c * ∫ y, ‖fderiv ℝ (v j) y‖)) → eLpNorm u p volume ≤ ENNReal.ofReal (c * ∫ y, ‖fderiv ℝ u y‖) := by
  intro N p c K S u v hS hv hsupp hbd hlim hdlim hineq
  -- Step 1: each `v j` is continuous, so their a.e. limit `u` is a.e. strongly measurable.
  have hvm : ∀ j, AEStronglyMeasurable (v j) volume :=
    fun j ↦ (hv j).continuous.aestronglyMeasurable
  have hum : AEStronglyMeasurable u volume := aestronglyMeasurable_of_tendsto_ae atTop hvm hlim
  -- Steps 2–4: dominated convergence of `∫ ‖Dv_j‖`; `Dv_j` vanishes off `tsupport v_j ⊆ S`, so
  -- `‖Dv_j‖ ≤ K 1_S`, which is integrable because `S` is compact.
  have hconv : Tendsto (fun j ↦ ∫ y, ‖fderiv ℝ (v j) y‖) atTop (𝓝 (∫ y, ‖fderiv ℝ u y‖)) := by
    refine tendsto_integral_of_dominated_convergence (S.indicator fun _ ↦ (K : ℝ))
      (F := fun j y ↦ ‖fderiv ℝ (v j) y‖) (f := fun y ↦ ‖fderiv ℝ u y‖)
      (fun j ↦ ((hv j).continuous_fderiv one_ne_zero).norm.aestronglyMeasurable)
      ((integrableOn_const hS.measure_lt_top.ne).integrable_indicator hS.measurableSet)
      (fun j ↦ ae_of_all _ fun y ↦ ?_) (hdlim.mono fun y hy ↦ hy.norm)
    show ‖‖fderiv ℝ (v j) y‖‖ ≤ S.indicator (fun _ ↦ (K : ℝ)) y
    by_cases hy : y ∈ S
    · rw [norm_norm, indicator_of_mem hy]
      exact hbd j y
    · rw [indicator_of_notMem hy, fderiv_of_notMem_tsupport ℝ fun h ↦ hy (hsupp j h), norm_zero,
        norm_zero]
  -- Steps 5–7: Fatou's lemma for `eLpNorm`, the bounds for `v j`, and the limit of those bounds.
  calc eLpNorm u p volume ≤ atTop.liminf fun j ↦ eLpNorm (v j) p volume :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm hvm u hum hlim
    _ ≤ atTop.liminf fun j ↦ ENNReal.ofReal (c * ∫ y, ‖fderiv ℝ (v j) y‖) :=
        liminf_le_liminf (.of_forall hineq)
    _ = ENNReal.ofReal (c * ∫ y, ‖fderiv ℝ u y‖) :=
        (ENNReal.tendsto_ofReal (hconv.const_mul c)).liminf_eq
/-- **Mollifying a compactly supported Lipschitz function**: the approximation step of Simon Ch. 3,
proof of Theorem 4.3, used to apply (3) to the Lipschitz cut-offs `ζ_k` of (4) and in the Sobolev
step (`chapter-03.txt` lines 622–637 and 689–704). For the normalized bump `φ_j ≥ 0` with
`∫ φ_j = 1` and support in `B_{σ_j}(0)`, `σ_j = 1 / (j + 2)`, the mollification `v_j = φ_j ⋆ u` is
`C¹` with `tsupport v_j ⊆ cthickening σ_j (tsupport u)` and `|v_j - u| ≤ K σ_j`. Difference
quotients, Rademacher's theorem and dominated convergence give `D v_j = φ_j ⋆ D u`, hence
`‖D v_j‖ ≤ K`, and the Lebesgue differentiation theorem gives `D v_j → D u` a.e. -/
theorem Submission.deGiorgiDens_lipschitz_smooth_approx : ∀ (N : ℕ) (u : Rn N → ℝ) (K : ℝ≥0), LipschitzWith K u → HasCompactSupport u → ∃ v : ℕ → Rn N → ℝ, (∀ j, ContDiff ℝ 1 (v j)) ∧ (∀ j, HasCompactSupport (v j)) ∧ (∀ j, tsupport (v j) ⊆ Metric.cthickening (1 / ((j : ℝ) + 1)) (tsupport u)) ∧ (∀ j y, ‖fderiv ℝ (v j) y‖ ≤ K) ∧ TendstoUniformly v u atTop ∧ ∀ᵐ y ∂(volume : Measure (Rn N)), Tendsto (fun j ↦ fderiv ℝ (v j) y) atTop (𝓝 (fderiv ℝ u y)) := by
  intro N u K hu hcu
  -- Step 1: the radii `σ j = 1 / (j + 2) ∈ (0, 1 / (j + 1)]`, tending to `0`.
  set σ : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 2) with hσ
  have hσpos : ∀ j, 0 < σ j := fun j ↦ by simp only [hσ]; positivity
  have hσle : ∀ j, σ j ≤ 1 / ((j : ℝ) + 1) := fun j ↦ by
    simp only [hσ]
    gcongr
    linarith
  have hσlim : Tendsto σ atTop (𝓝 0) :=
    squeeze_zero (fun j ↦ (hσpos j).le) hσle tendsto_one_div_add_atTop_nhds_zero_nat
  -- Step 2: the bump `b j` (equal to `1` on `B̄_{σ j / 2}(0)`, supported in `B_{σ j}(0)`) and
  -- the normalized kernel `φ j = b j / ∫ b j ≤ 2ᴺ / Lᴺ(B̄_{σ j}(y))`.
  let b : ℕ → ContDiffBump (0 : Rn N) := fun j ↦
    { rIn := σ j / 2, rOut := σ j, rIn_pos := half_pos (hσpos j),
      rIn_lt_rOut := half_lt_self (hσpos j) }
  have hb_int : ∀ j, Integrable (b j) volume := fun j ↦
    (b j).continuous.integrable_of_hasCompactSupport (b j).hasCompactSupport
  have hvol_pos : ∀ (x : Rn N) (r : ℝ), 0 < r → 0 < volume.real (Metric.closedBall x r) :=
    fun x r hr ↦ ENNReal.toReal_pos (Metric.measure_closedBall_pos _ _ hr).ne'
      measure_closedBall_lt_top.ne
  have hc_ge : ∀ j, volume.real (Metric.closedBall (0 : Rn N) (σ j / 2)) ≤ ∫ x, b j x := by
    intro j
    calc volume.real (Metric.closedBall (0 : Rn N) (σ j / 2))
        = ∫ _ in Metric.closedBall (0 : Rn N) (σ j / 2), (1 : ℝ) := by simp
      _ = ∫ x in Metric.closedBall (0 : Rn N) (σ j / 2), b j x :=
          setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet
            (fun x hx ↦ ((b j).one_of_mem_closedBall hx).symm)
      _ ≤ ∫ x, b j x :=
          setIntegral_le_integral (hb_int j) (Eventually.of_forall fun x ↦ (b j).nonneg)
  have hc_pos : ∀ j, 0 < ∫ x, b j x := fun j ↦
    (hvol_pos 0 _ (half_pos (hσpos j))).trans_le (hc_ge j)
  set φ : ℕ → Rn N → ℝ := fun j x ↦ (∫ y, b j y)⁻¹ * b j x with hφ
  have hφ_nonneg : ∀ j x, 0 ≤ φ j x := fun j x ↦
    mul_nonneg (inv_nonneg.2 (hc_pos j).le) (b j).nonneg
  have hφ_cd : ∀ j, ContDiff ℝ 1 (φ j) := fun j ↦ contDiff_const.mul (b j).contDiff
  have hφ_cs : ∀ j, HasCompactSupport (φ j) := fun j ↦ (b j).hasCompactSupport.mul_left
  have hφ_int : ∀ j, Integrable (φ j) volume := fun j ↦ (hb_int j).const_mul _
  have hφ_one : ∀ j, ∫ x, φ j x = 1 := fun j ↦ by
    simp only [hφ]
    rw [integral_const_mul]
    exact inv_mul_cancel₀ (hc_pos j).ne'
  have hφ_supp : ∀ j, Function.support (φ j) ⊆ Metric.ball 0 (σ j) := fun j x hx ↦ by
    have hbx : b j x ≠ 0 := fun h ↦ hx (by simp only [hφ, h, mul_zero])
    exact (b j).support_eq ▸ hbx
  have hφ_le : ∀ j x (y : Rn N),
      φ j x ≤ 2 ^ finrank ℝ (Rn N) / volume.real (Metric.closedBall y (σ j)) := by
    intro j x y
    have h1 := Measure.addHaar_real_closedBall' (volume : Measure (Rn N)) y (hσpos j).le
    have h2 := Measure.addHaar_real_closedBall' (volume : Measure (Rn N)) 0 (half_pos (hσpos j)).le
    have hV := hvol_pos 0 1 one_pos
    calc φ j x = (∫ y, b j y)⁻¹ * b j x := rfl
      _ ≤ (∫ y, b j y)⁻¹ * 1 := by
          gcongr
          · exact inv_nonneg.2 (hc_pos j).le
          · exact (b j).le_one
      _ ≤ (volume.real (Metric.closedBall (0 : Rn N) (σ j / 2)))⁻¹ := by
          rw [mul_one]
          exact inv_anti₀ (hvol_pos _ _ (half_pos (hσpos j))) (hc_ge j)
      _ = 2 ^ finrank ℝ (Rn N) / volume.real (Metric.closedBall y (σ j)) := by
          rw [h1, h2, div_pow]
          have := hσpos j
          field_simp
  -- Step 3: the mollifications `v j = φ j ⋆ u`: `C¹`, with support in the `σ j`-neighbourhood.
  set v : ℕ → Rn N → ℝ := fun j ↦
    MeasureTheory.convolution (φ j) u (ContinuousLinearMap.lsmul ℝ ℝ) volume with hv
  have hv_eq : ∀ j y, v j y = ∫ x, φ j (y - x) * u x := fun j y ↦ by
    simp only [hv]
    rw [convolution_eq_swap]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hv_cd : ∀ j, ContDiff ℝ 1 (v j) := fun j ↦
    (hφ_cs j).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (n := 1) (hφ_cd j)
      hu.continuous.locallyIntegrable
  have hv_cs : ∀ j, HasCompactSupport (v j) := fun j ↦
    (hφ_cs j).convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcu
  have hv_tsupp : ∀ j, tsupport (v j) ⊆ Metric.cthickening (1 / ((j : ℝ) + 1)) (tsupport u) := by
    intro j
    have h1 : Function.support (v j) ⊆ Metric.cthickening (σ j) (tsupport u) := by
      intro y hy
      obtain ⟨a, ha, t, ht, rfl⟩ := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hy
      refine Metric.mem_cthickening_of_dist_le _ t _ _ (subset_tsupport _ ht) ?_
      rw [dist_eq_norm, add_sub_cancel_right]
      have := hφ_supp j ha
      rw [Metric.mem_ball, dist_zero_right] at this
      exact this.le
    exact (closure_minimal h1 Metric.isClosed_cthickening).trans
      (Metric.cthickening_mono (hσle j) _)
  -- Step 4: uniform convergence, `|v j y - u y| ≤ K σ j`.
  have hv_unif : ∀ j y, dist (v j y) (u y) ≤ K * σ j := fun j y ↦
    dist_convolution_le (by positivity) (hφ_supp j) (hφ_nonneg j) (hφ_one j)
      hu.continuous.aestronglyMeasurable
      (fun x hx ↦ (hu.dist_le_mul x y).trans (by gcongr; exact (Metric.mem_ball.1 hx).le))
  have hunif : TendstoUniformly v u atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hKσ : Tendsto (fun j ↦ (K : ℝ) * σ j) atTop (𝓝 0) := by
      simpa using hσlim.const_mul (K : ℝ)
    filter_upwards [hKσ.eventually (gt_mem_nhds hε)] with j hj y
    rw [dist_comm]
    exact (hv_unif j y).trans_lt hj
  -- Step 5: `D v_j = φ_j ⋆ D u`, via difference quotients, Rademacher and dominated convergence.
  have hG_bdd : ∀ x, ‖fderiv ℝ u x‖ ≤ K := fun x ↦ norm_fderiv_le_of_lipschitz ℝ hu
  have hG_memLp : MemLp (fderiv ℝ u) ∞ (volume : Measure (Rn N)) :=
    memLp_top_of_bound (measurable_fderiv ℝ u).aestronglyMeasurable K
      (Eventually.of_forall hG_bdd)
  have hG_loc : LocallyIntegrable (fderiv ℝ u) (volume : Measure (Rn N)) :=
    hG_memLp.locallyIntegrable le_top
  have hderiv : ∀ j y, fderiv ℝ (v j) y = ∫ x, φ j (y - x) • fderiv ℝ u x := by
    intro j y
    have hg_int : Integrable (fun x ↦ φ j (y - x)) volume := (hφ_int j).comp_sub_left y
    have hint : Integrable (fun x ↦ φ j (y - x) • fderiv ℝ u x) volume :=
      hg_int.smul_of_top_left hG_memLp
    ext h
    rw [ContinuousLinearMap.integral_apply hint]
    have hlim1 : Tendsto (fun t : ℝ ↦ t⁻¹ • (v j (y + t • h) - v j y)) (𝓝[>] 0)
        (𝓝 (fderiv ℝ (v j) y h)) :=
      (((hv_cd j).differentiable one_ne_zero y).hasFDerivAt.hasLineDerivAt
        h).tendsto_slope_zero_right
    have hlim2 :=
      hu.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul (μ := volume) hg_int h
    have hcomp : ∀ s : Rn N, Integrable (fun x ↦ φ j (y - x) * u (x + s)) volume := by
      intro s
      apply Continuous.integrable_of_hasCompactSupport
      · exact ((hφ_cd j).continuous.comp (continuous_const.sub continuous_id)).mul
          (hu.continuous.comp (continuous_id.add continuous_const))
      · exact ((hφ_cs j).comp_homeomorph (Homeomorph.subLeft y)).mul_right
    have heq : ∀ t : ℝ, t⁻¹ • (v j (y + t • h) - v j y) =
        ∫ x, t⁻¹ • (u (x + t • h) - u x) * φ j (y - x) := by
      intro t
      have hshift : v j (y + t • h) = ∫ x, φ j (y - x) * u (x + t • h) := by
        rw [hv_eq, ← integral_add_right_eq_self _ (t • h)]
        simp only [add_sub_add_right_eq_sub]
      have h0 : v j y = ∫ x, φ j (y - x) * u (x + 0) := by
        rw [hv_eq]
        simp only [add_zero]
      rw [hshift, h0, ← integral_sub (hcomp _) (hcomp _), ← integral_smul]
      congr 1
      ext x
      simp only [add_zero, smul_eq_mul]
      ring
    simp_rw [heq] at hlim1
    rw [tendsto_nhds_unique hlim1 hlim2]
    apply integral_congr_ae
    filter_upwards [hu.ae_differentiableAt (μ := volume)] with x hx
    rw [hx.lineDeriv_eq_fderiv]
    simp only [smul_apply, smul_eq_mul]
    ring
  -- Step 6: `‖D v_j‖ ≤ K`.
  have hbound : ∀ j y, ‖fderiv ℝ (v j) y‖ ≤ K := by
    intro j y
    rw [hderiv j y]
    calc ‖∫ x, φ j (y - x) • fderiv ℝ u x‖ ≤ ∫ x, (K : ℝ) * φ j (y - x) := by
          refine norm_integral_le_of_norm_le (((hφ_int j).comp_sub_left y).const_mul _) ?_
          filter_upwards with x
          rw [norm_smul, Real.norm_of_nonneg (hφ_nonneg j _), mul_comm]
          exact mul_le_mul_of_nonneg_right (hG_bdd x) (hφ_nonneg j _)
      _ = K := by
          rw [integral_const_mul, integral_sub_left_eq_self (φ j) volume y, hφ_one, mul_one]
  -- Step 7: the Lebesgue differentiation theorem gives `D v_j → D u` a.e.
  have hae : ∀ᵐ y ∂(volume : Measure (Rn N)),
      Tendsto (fun j ↦ fderiv ℝ (v j) y) atTop (𝓝 (fderiv ℝ u y)) := by
    filter_upwards [(Besicovitch.vitaliFamily
      (volume : Measure (Rn N))).ae_tendsto_average_norm_sub hG_loc] with x₀ h₀
    have hσ' : Tendsto σ atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hσlim, Eventually.of_forall hσpos⟩
    have hav := (h₀.comp (Besicovitch.tendsto_filterAt volume x₀)).comp hσ'
    simp_rw [hderiv]
    refine tendsto_integral_smul_of_tendsto_average_norm_sub (g := fun j x ↦ φ j (x₀ - x))
      (2 ^ finrank ℝ (Rn N)) hav ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun j ↦ hG_loc.integrableOn_isCompact (isCompact_closedBall _ _)
    · refine tendsto_const_nhds.congr fun j ↦ ?_
      rw [integral_sub_left_eq_self (φ j) volume x₀, hφ_one]
    · filter_upwards with j x hx
      have := hφ_supp j hx
      rw [Metric.mem_ball, dist_zero_right] at this
      rw [Metric.mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
      exact this.le
    · filter_upwards with j x
      rw [abs_of_nonneg (hφ_nonneg j _)]
      exact hφ_le j _ x₀
  exact ⟨v, hv_cd, hv_cs, hv_tsupp, hbound, hunif, hae⟩
/-- **Sobolev inequality for compactly supported Lipschitz functions** (Simon Ch. 3, proof of
Theorem 4.3, Step 7 "Constants"): for `N = n + 1` and `p = (n + 1) / n` (so `p = ∞` when `n = 0`)
there is `c > 0` with `‖u‖_{L^p} ≤ c ∫ ‖Du‖ dLᴺ` for every Lipschitz `u : ℝᴺ → ℝ` with compact
support. For `C¹` functions with compact support this is the Gagliardo–Nirenberg–Sobolev
inequality [GT01, Thm 7.10] when `n ≥ 1` and the bound `sup |v| ≤ ½ ∫ |v'|` (erratum E6) when
`n = 0`. The mollifications `v_j` of `u` are `C¹`, supported in the compact set
`cthickening 1 (tsupport u)`, with `‖Dv_j‖ ≤ K`, `v_j → u` uniformly and `Dv_j → Du` a.e., so the
bound passes to the limit by dominated convergence and Fatou's lemma for `eLpNorm`. -/
theorem Submission.deGiorgiDens_lipschitz_sobolev : ∀ (n : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ (u : Rn (n + 1) → ℝ) (K : ℝ≥0), LipschitzWith K u → HasCompactSupport u → eLpNorm u ((n + 1 : ℝ≥0∞) / n) volume ≤ ENNReal.ofReal (c * ∫ y, ‖fderiv ℝ u y‖) := by
  intro n
  -- Steps 1–2: the inequality for `C¹` functions with compact support, with `c = ½` if `n = 0`
  -- (where `p = (0 + 1) / 0 = ∞`) and the Gagliardo–Nirenberg–Sobolev constant if `n ≥ 1`.
  obtain ⟨c, hc, hsmooth⟩ : ∃ c : ℝ, 0 < c ∧ ∀ v : Rn (n + 1) → ℝ, ContDiff ℝ 1 v →
      HasCompactSupport v →
        eLpNorm v ((n + 1 : ℝ≥0∞) / n) volume ≤ ENNReal.ofReal (c * ∫ y, ‖fderiv ℝ v y‖) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨1 / 2, one_half_pos, fun v hv hvs ↦ ?_⟩
      convert Submission.deGiorgiDensSob_one_dim_contDiff v hv hvs using 2
      simp
    · exact Submission.deGiorgiDensSob_gns_contDiff n hn
  refine ⟨c, hc, fun u K hu hcu ↦ ?_⟩
  -- Step 3: the `C¹` approximations `v j`, supported in the compact set
  -- `cthickening (1 / (j + 1)) (tsupport u) ⊆ cthickening 1 (tsupport u)`.
  obtain ⟨v, hv_cd, hv_cs, hv_tsupp, hbound, hunif, hae⟩ :=
    Submission.deGiorgiDens_lipschitz_smooth_approx (n + 1) u K hu hcu
  have hsupp : ∀ j, tsupport (v j) ⊆ Metric.cthickening 1 (tsupport u) := fun j ↦
    (hv_tsupp j).trans (Metric.cthickening_mono
      (div_le_one_of_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg j)) (by positivity)) _)
  -- Steps 4–5: dominated convergence of `∫ ‖Dv_j‖` and Fatou's lemma for `eLpNorm`.
  exact Submission.deGiorgiDensSob_eLpNorm_le_of_approx (n + 1) _ c K
    (Metric.cthickening 1 (tsupport u)) u v hcu.isCompact.cthickening hv_cd hsupp hbound
    (ae_of_all _ hunif.tendsto_at) hae fun j ↦ hsmooth (v j) (hv_cd j) (hv_cs j)

/-- **Gauss–Green identity for a Lipschitz test function times a constant vector** (Simon Ch. 3,
proof of 4.3, (3) and its use for Lipschitz cut-offs in (4)–(5), pp. 81–82, `chapter-03.txt`
lines 622–643): for `ζ` Lipschitz with compact support in `U` and `w ∈ ℝᴺ`,
`∫_{G ∩ U} Dζ(y) w dLᴺ(y) = -∫ ζ ⟨w, ν⟩ dμ`. Take `C¹` functions `v_j → ζ` uniformly with
`|Dv_j| ≤ K`, `Dv_j → Dζ` `Lᴺ`-a.e. and `tsupport v_j` in the closed `1/(j+1)`-neighbourhood of
`tsupport ζ` (`deGiorgiDens_lipschitz_smooth_approx`). The field `v_j w` has divergence
`Dv_j(·) w`, so (4.1) gives the identity for `v_j` once `tsupport v_j ⊆ U`; dominated convergence
(bounds `K |w| 1_{K₁}` for `Lᴺ` and `(sup |ζ| + 1) |w| 1_{K_δ}` for `μ`, `K_ρ` the closed
`ρ`-neighbourhood of `tsupport ζ`, `K_δ ⊆ U`) passes to the limit on both sides. -/
theorem Submission.deGiorgiDens_lipschitz_gaussGreen : ∀ (N : ℕ) (U G : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → NullMeasurableSet G volume → IsGaussGreenPair U G μ ν → ∀ (ζ : Rn N → ℝ) (K : ℝ≥0), LipschitzWith K ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∀ w : Rn N, ∫ y in G ∩ U, fderiv ℝ ζ y w = -∫ y, ζ y * inner ℝ w (ν y) ∂μ := by
  intro N U G μ ν hU _hG hpair ζ K hζ hζc hζU w
  obtain ⟨-, hμK, hν, hν1, hGG⟩ := hpair
  -- Step 1: a closed `δ`-neighbourhood of `tsupport ζ` inside `U`; it and the closed
  -- `1`-neighbourhood of `tsupport ζ` are compact.
  obtain ⟨δ, hδ, hδU⟩ := hζc.isCompact.exists_cthickening_subset_open hU hζU
  have hK₁ : IsCompact (Metric.cthickening 1 (tsupport ζ)) := hζc.isCompact.cthickening
  have hKδ : IsCompact (Metric.cthickening δ (tsupport ζ)) := hζc.isCompact.cthickening
  -- Step 2: the `C¹` approximations; their supports lie in `K₁`, and in `K_δ` for large `j`.
  obtain ⟨v, hvC1, hvc, hvsupp, hvD, hvunif, hvae⟩ :=
    Submission.deGiorgiDens_lipschitz_smooth_approx N ζ K hζ hζc
  have hv₁ : ∀ j : ℕ, tsupport (v j) ⊆ Metric.cthickening 1 (tsupport ζ) := fun j =>
    (hvsupp j).trans (Metric.cthickening_mono
      ((Nat.one_div_le_one_div (Nat.zero_le j)).trans (by norm_num)) _)
  have hvδ : ∀ᶠ j : ℕ in atTop, tsupport (v j) ⊆ Metric.cthickening δ (tsupport ζ) := by
    obtain ⟨j₀, hj₀⟩ := exists_nat_one_div_lt hδ
    filter_upwards [eventually_ge_atTop j₀] with j hj
    exact (hvsupp j).trans (Metric.cthickening_mono ((Nat.one_div_le_one_div hj).trans hj₀.le) _)
  -- Step 3: (4.1) for the `C¹` fields `v_j w`, whose divergence is the trace `Dv_j(·) w` of the
  -- rank-one map `h ↦ (Dv_j(·) h) w`.
  have hGGj : ∀ᶠ j : ℕ in atTop,
      -∫ y, v j y * inner ℝ w (ν y) ∂μ = ∫ y in G ∩ U, fderiv ℝ (v j) y w := by
    filter_upwards [hvδ] with j hj
    have h := hGG (fun y => v j y • w) ((hvC1 j).smul contDiff_const)
      ((hvc j).smul_right (f' := fun _ => w))
      ((tsupport_smul_subset_left _ _).trans (hj.trans hδU))
    have hdiv : ∀ y, Poincare.SimonGMT.Chapter02.euclideanDivergence (fun y => v j y • w) y =
        fderiv ℝ (v j) y w := by
      intro y
      rw [Poincare.SimonGMT.Chapter02.euclideanDivergence,
        fderiv_smul_const ((hvC1 j).differentiable one_ne_zero y)]
      exact LinearMap.trace_smulRight _ _
    simp only [hdiv, real_inner_smul_left] at h
    exact h.symm
  -- Step 4: dominated convergence on the left, with bound `K |w| 1_{K₁}`.
  have hL : Tendsto (fun j => ∫ y in G ∩ U, fderiv ℝ (v j) y w) atTop
      (𝓝 (∫ y in G ∩ U, fderiv ℝ ζ y w)) := by
    refine tendsto_integral_of_dominated_convergence
      ((Metric.cthickening 1 (tsupport ζ)).indicator fun _ => (K : ℝ) * ‖w‖) (fun j => ?_) ?_
      (fun j => ae_of_all _ fun y => ?_) ?_
    · exact (((hvC1 j).continuous_fderiv one_ne_zero).clm_apply
        continuous_const).aestronglyMeasurable
    · refine (integrable_indicator_iff Metric.isClosed_cthickening.measurableSet).2
        (integrableOn_const ?_)
      exact ((Measure.restrict_apply_le _ _).trans_lt hK₁.measure_lt_top).ne
    · by_cases hy : y ∈ Metric.cthickening 1 (tsupport ζ)
      · rw [indicator_of_mem hy]
        exact ((fderiv ℝ (v j) y).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right (hvD j y) (norm_nonneg w))
      · rw [indicator_of_notMem hy, fderiv_of_notMem_tsupport ℝ (fun h => hy (hv₁ j h)),
          zero_apply, norm_zero]
    · filter_upwards [ae_restrict_of_ae hvae] with y hy
      exact hy.eval_const w
  -- Step 5: dominated convergence on the right, with bound `(sup |ζ| + 1) |w| 1_{K_δ}`.
  obtain ⟨M, hM⟩ := hζ.continuous.bounded_above_of_compact_support hζc
  have hR : Tendsto (fun j => ∫ y, v j y * inner ℝ w (ν y) ∂μ) atTop
      (𝓝 (∫ y, ζ y * inner ℝ w (ν y) ∂μ)) := by
    have hνw : AEStronglyMeasurable (fun y => inner ℝ w (ν y)) μ :=
      (continuous_const.inner continuous_id).comp_aestronglyMeasurable hν
    refine tendsto_integral_filter_of_dominated_convergence
      ((Metric.cthickening δ (tsupport ζ)).indicator fun _ => (M + 1) * ‖w‖)
      (Eventually.of_forall fun j => (hvC1 j).continuous.aestronglyMeasurable.mul hνw) ?_ ?_ ?_
    · filter_upwards [hvδ, Metric.tendstoUniformly_iff.1 hvunif 1 one_pos] with j hj hj1
      filter_upwards [hν1] with y hy
      by_cases hyδ : y ∈ Metric.cthickening δ (tsupport ζ)
      · rw [indicator_of_mem hyδ, norm_mul]
        have h1 := hj1 y
        rw [dist_eq_norm] at h1
        have h2 : ‖v j y‖ ≤ M + 1 := by
          linarith [norm_sub_norm_le (v j y) (ζ y), norm_sub_rev (ζ y) (v j y), hM y]
        exact mul_le_mul h2 ((norm_inner_le_norm w (ν y)).trans (by rw [hy, mul_one]))
          (norm_nonneg _) ((norm_nonneg _).trans h2)
      · rw [indicator_of_notMem hyδ, image_eq_zero_of_notMem_tsupport (fun h => hyδ (hj h)),
          zero_mul, norm_zero]
    · exact (integrable_indicator_iff Metric.isClosed_cthickening.measurableSet).2
        (integrableOn_const (hμK _ hKδ hδU).ne)
    · exact ae_of_all _ fun y => (hvunif.tendsto_at y).mul_const _
  -- Step 6: both sides of the identity for `v_j` converge, so the limits agree.
  exact tendsto_nhds_unique hL (hR.neg.congr' hGGj)

/-- **First-variation bound at a differentiability radius** (Simon Ch. 3, proof of 4.3, (3)–(5),
pp. 81–82, `chapter-03.txt` lines 622–645): if `B̄_ρ(x) ⊆ U`, `|w| ≤ 1` and
`V(r) = Lᴺ(G ∩ B_r(x))` has derivative `d` at `r = ρ`, then `∫_{B_ρ(x)} ⟨ν, w⟩ dμ ≤ d`.
For `s ∈ (0, ρ)` let `ζ_s` be the radial cut-off of `deGiorgiDens_radial_cutoff` (`ζ_s = 1` on
`B_s(x)`, `ζ_s = 0` off `B_ρ(x)`). By `deGiorgiDens_lipschitz_gaussGreen` and `|w| ≤ 1`,
`∫ ζ_s ⟨ν, w⟩ dμ = -∫_{G ∩ U} Dζ_s w ≤ ∫_{G ∩ U} |Dζ_s| = (V(ρ) - V(s)) / (ρ - s)`, using
`(G ∩ U) ∩ B_r(x) = G ∩ B_r(x)` for `r ≤ ρ`. As `s ↑ ρ` the right side tends to `d`, and by
dominated convergence (bound `1_{B̄_ρ(x)}`, `μ(B̄_ρ(x)) < ∞`) the left side tends to
`∫_{B_ρ(x)} ⟨ν, w⟩ dμ`. -/
theorem Submission.deGiorgiDens_ball_normal_le_deriv : ∀ (N : ℕ) (U G : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → NullMeasurableSet G volume → IsGaussGreenPair U G μ ν → ∀ (x w : Rn N) (ρ d : ℝ), 0 < ρ → Metric.closedBall x ρ ⊆ U → ‖w‖ ≤ 1 → HasDerivAt (fun r : ℝ ↦ (volume (G ∩ Metric.ball x r)).toReal) d ρ → ∫ y in Metric.ball x ρ, inner ℝ (ν y) w ∂μ ≤ d := by
  intro N U G μ ν hU hG hpair x w ρ d hρ hcl hw hV
  obtain ⟨-, hμK, hνm, hν1, -⟩ := id hpair
  set V : ℝ → ℝ := fun r ↦ (volume (G ∩ Metric.ball x r)).toReal
  -- Step 1: `μ(B̄_ρ(x)) < ∞`.
  have hμB : μ (Metric.closedBall x ρ) < ∞ := hμK _ (isCompact_closedBall x ρ) hcl
  -- Step 2: a radial cut-off `ζ s` for every `s ∈ (0, ρ)`.
  have hcut : ∀ s : ℝ, ∃ ζ : Rn N → ℝ, 0 < s → s < ρ →
      (∃ K : ℝ≥0, LipschitzWith K ζ) ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ Metric.closedBall x ρ ∧ (∀ y, 0 ≤ ζ y ∧ ζ y ≤ 1) ∧
      (∀ y ∈ Metric.ball x s, ζ y = 1) ∧ (∀ y ∉ Metric.ball x ρ, ζ y = 0) ∧
      ∀ G' : Set (Rn N), NullMeasurableSet G' volume → ∫ y in G', ‖fderiv ℝ ζ y‖ =
        ((volume (G' ∩ Metric.ball x ρ)).toReal - (volume (G' ∩ Metric.ball x s)).toReal) /
          (ρ - s) := by
    intro s
    by_cases hs : 0 < s ∧ s < ρ
    · obtain ⟨ζ, hζ⟩ := Submission.deGiorgiDens_radial_cutoff N x s ρ hs.1 hs.2
      exact ⟨ζ, fun _ _ ↦ hζ⟩
    · exact ⟨0, fun h₁ h₂ ↦ (hs ⟨h₁, h₂⟩).elim⟩
  choose ζ hζ using hcut
  -- Step 3: `∫ ζ_s ⟨ν, w⟩ dμ ≤ (V(ρ) - V(s)) / (ρ - s)` for every `s ∈ (0, ρ)`.
  have hkey : ∀ s, 0 < s → s < ρ →
      ∫ y, ζ s y * inner ℝ (ν y) w ∂μ ≤ (V ρ - V s) / (ρ - s) := by
    intro s hs hsρ
    obtain ⟨⟨K, hK⟩, hcs, hts, -, -, -, hgrad⟩ := hζ s hs hsρ
    have hGG := Submission.deGiorgiDens_lipschitz_gaussGreen N U G μ ν hU hG hpair (ζ s) K hK hcs
      (hts.trans hcl) w
    have hGU : ∀ r ≤ ρ, G ∩ U ∩ Metric.ball x r = G ∩ Metric.ball x r := fun r hr ↦ by
      rw [inter_assoc, inter_eq_right.2 ((Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall hr)).trans hcl)]
    have hgradGU := hgrad (G ∩ U) (hG.inter hU.measurableSet.nullMeasurableSet)
    rw [hGU ρ le_rfl, hGU s hsρ.le] at hgradGU
    -- `|Dζ_s| ≤ K 1_{B̄_ρ(x)}`, so `|Dζ_s|` is integrable on `G ∩ U`.
    have hint : Integrable (fun y ↦ ‖fderiv ℝ (ζ s) y‖) (volume.restrict (G ∩ U)) := by
      have hKB : Integrable ((Metric.closedBall x ρ).indicator fun _ ↦ (K : ℝ))
          (volume.restrict (G ∩ U)) :=
        ((integrable_indicator_iff measurableSet_closedBall).2
          (integrableOn_const (C := (K : ℝ)) measure_closedBall_lt_top.ne)).restrict
      refine hKB.mono' (measurable_fderiv ℝ (ζ s)).norm.aestronglyMeasurable
        (ae_of_all _ fun y ↦ ?_)
      rw [norm_norm]
      by_cases hy : y ∈ Metric.closedBall x ρ
      · rw [indicator_of_mem hy]
        exact norm_fderiv_le_of_lipschitz ℝ hK
      · rw [indicator_of_notMem hy, fderiv_of_notMem_tsupport ℝ fun h ↦ hy (hts h), norm_zero]
    calc ∫ y, ζ s y * inner ℝ (ν y) w ∂μ = -∫ y in G ∩ U, fderiv ℝ (ζ s) y w := by
          rw [hGG, neg_neg]
          exact integral_congr_ae (ae_of_all _ fun y ↦
            congrArg (ζ s y * ·) (real_inner_comm w (ν y)))
      _ ≤ ‖∫ y in G ∩ U, fderiv ℝ (ζ s) y w‖ := by
          rw [Real.norm_eq_abs]
          exact neg_le_abs _
      _ ≤ ∫ y in G ∩ U, ‖fderiv ℝ (ζ s) y w‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ y in G ∩ U, ‖fderiv ℝ (ζ s) y‖ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun y ↦ norm_nonneg _) hint
            (ae_of_all _ fun y ↦ ?_)
          calc ‖fderiv ℝ (ζ s) y w‖ ≤ ‖fderiv ℝ (ζ s) y‖ * ‖w‖ := (fderiv ℝ (ζ s) y).le_opNorm w
            _ ≤ ‖fderiv ℝ (ζ s) y‖ * 1 := by gcongr
            _ = ‖fderiv ℝ (ζ s) y‖ := mul_one _
      _ = (V ρ - V s) / (ρ - s) := hgradGU
  -- Step 4: `(V(ρ) - V(s)) / (ρ - s) → d` as `s ↑ ρ`.
  have hR : Tendsto (fun s ↦ (V ρ - V s) / (ρ - s)) (𝓝[<] ρ) (𝓝 d) := by
    rw [hasDerivAt_iff_tendsto_slope] at hV
    refine (hV.mono_left (nhdsWithin_mono _ fun t (ht : t ∈ Iio ρ) ↦ ne_of_lt ht)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : s < ρ)
    rw [slope_def_field, ← neg_div_neg_eq, neg_sub, neg_sub]
  -- Step 5: `∫ ζ_s ⟨ν, w⟩ dμ → ∫_{B_ρ(x)} ⟨ν, w⟩ dμ` as `s ↑ ρ` (dominated convergence).
  have hL : Tendsto (fun s ↦ ∫ y, ζ s y * inner ℝ (ν y) w ∂μ) (𝓝[<] ρ)
      (𝓝 (∫ y in Metric.ball x ρ, inner ℝ (ν y) w ∂μ)) := by
    rw [← integral_indicator measurableSet_ball]
    refine tendsto_integral_filter_of_dominated_convergence
      ((Metric.closedBall x ρ).indicator fun _ ↦ (1 : ℝ)) ?_ ?_ ?_ ?_
    · filter_upwards [Ioo_mem_nhdsLT hρ] with s hs
      obtain ⟨⟨K, hK⟩, -⟩ := hζ s hs.1 hs.2
      exact hK.continuous.aestronglyMeasurable.mul
        ((continuous_id.inner continuous_const).comp_aestronglyMeasurable hνm)
    · filter_upwards [Ioo_mem_nhdsLT hρ] with s hs
      obtain ⟨-, -, -, h01, -, h0, -⟩ := hζ s hs.1 hs.2
      filter_upwards [hν1] with y hy
      by_cases hyb : y ∈ Metric.ball x ρ
      · rw [indicator_of_mem (Metric.ball_subset_closedBall hyb), norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (h01 y).1]
        calc ζ s y * ‖inner ℝ (ν y) w‖ ≤ 1 * 1 := by
              gcongr
              · exact (h01 y).2
              · exact (norm_inner_le_norm (ν y) w).trans (by rw [hy, one_mul]; exact hw)
          _ = 1 := one_mul 1
      · rw [h0 y hyb, zero_mul, norm_zero]
        exact indicator_nonneg (fun _ _ ↦ zero_le_one) y
    · exact (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const (C := (1 : ℝ)) hμB.ne)
    · refine ae_of_all _ fun y ↦ ?_
      by_cases hyb : y ∈ Metric.ball x ρ
      · rw [indicator_of_mem hyb]
        refine tendsto_const_nhds.congr' ?_
        have hdy : dist y x < ρ := hyb
        filter_upwards [Ioo_mem_nhdsLT hdy] with s hs
        obtain ⟨-, -, -, -, h1, -⟩ := hζ s (dist_nonneg.trans_lt hs.1) hs.2
        rw [h1 y hs.1, one_mul]
      · rw [indicator_of_notMem hyb]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsLT hρ] with s hs
        obtain ⟨-, -, -, -, -, h0, -⟩ := hζ s hs.1 hs.2
        rw [h0 y hyb, zero_mul]
  -- Step 6: pass to the limit `s ↑ ρ` in Step 3.
  exact le_of_tendsto_of_tendsto hL hR
    (by filter_upwards [Ioo_mem_nhdsLT hρ] with s hs using hkey s hs.1 hs.2)

/-- **Sobolev inequality for `ζ χ_G`** (Simon Ch. 3, proof of 4.3, `chapter-03.txt`
lines 689–712, for a single Gauss–Green pair): there is `c = c(n) > 0` with
`‖ζ χ_G‖_{L^{(n+1)/n}} ≤ c (∫ ζ dμ + ∫_G |Dζ| dL^{n+1})` (`L^∞` for `n = 0`) for every
Gauss–Green pair `(μ, ν)` of `(U, G)` and every non-negative Lipschitz `ζ` with compact support
in `U`. Take `δ > 0` with `cthickening δ (spt ζ) ⊆ U`, mollifiers `ρ_j` supported in
`B̄_{δ/(j+1)}(0)`, `u_j(y) = ∫_G ρ_j(y - z) dz` and `w_j = ζ u_j`. The Lipschitz Sobolev
inequality, the product rule and the Gauss–Green duality estimate `∫ ζ |Du_j| ≤ ∫ ζ̃_j dμ`,
`ζ̃_j(z) = ∫ ζ(y) ρ_j(y - z) dy` (Simon Ch. 2, Lemma 2.5, `chapter-02.txt` lines 543–596) give
`‖w_j‖_p ≤ c (∫ ζ̃_j dμ + ∫ u_j |Dζ|)`. The right side tends to `c (∫ ζ dμ + ∫_G |Dζ|)` and
`w_j → ζ χ_G` a.e., so Fatou's lemma for `eLpNorm` (valid also for `p = ∞`) concludes. -/
theorem Submission.deGiorgiDens_sobolev_indicator : ∀ (n : ℕ), ∃ c : ℝ, 0 < c ∧
    ∀ (U G : Set (Rn (n + 1))) (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)),
      IsOpen U → NullMeasurableSet G volume → IsGaussGreenPair U G μ ν →
      ∀ (ζ : Rn (n + 1) → ℝ) (K : ℝ≥0), LipschitzWith K ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ U → (∀ y, 0 ≤ ζ y) →
        eLpNorm (G.indicator ζ) ((n + 1 : ℝ≥0∞) / n) volume ≤
          ENNReal.ofReal (c * (∫ y, ζ y ∂μ + ∫ y in G, ‖fderiv ℝ ζ y‖)) := by
  intro n
  -- Step 0: the constant of the Lipschitz Sobolev inequality.
  obtain ⟨c, hc, hsob⟩ := Submission.deGiorgiDens_lipschitz_sobolev n
  refine ⟨c, hc, ?_⟩
  intro U G μ ν hU hG hGG ζ K hζ hζc hζU hζ0
  -- `cthickening δ (tsupport ζ) ⊆ U` is compact, so it has finite `μ`-measure.
  obtain ⟨δ, hδ, hδU⟩ := hζc.isCompact.exists_cthickening_subset_open hU hζU
  have hδμ : μ (Metric.cthickening δ (tsupport ζ)) < ∞ :=
    hGG.2.1 _ hζc.isCompact.cthickening hδU
  -- Step 1: mollifiers `ρ j` supported in `B̄_{δ/(j+1)}(0)` and the mollified indicators
  -- `u j = ∫_G ρ j (· - z) dz`, which are Lipschitz with values in `[0, 1]`.
  obtain ⟨ρ, hρC, hρc, hρ0, hρ1, hρs, hρG⟩ :=
    Submission.deGiorgiSobInd_mollifier_seq (n + 1) δ hδ
  obtain ⟨hLip, hbd, hae, hweak⟩ := hρG G hG
  have hr : ∀ j : ℕ, δ / ((j : ℝ) + 1) ≤ δ := fun j ↦
    div_le_self hδ.le (le_add_of_nonneg_left (Nat.cast_nonneg j))
  have hr0 : Tendsto (fun j : ℕ ↦ δ / ((j : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
  -- `w j = ζ u j` is Lipschitz with compact support and `∫ |D w j| ≤ ∫ ζ |D u j| + ∫ u j |Dζ|`.
  have hw : ∀ j : ℕ, (∃ K' : ℝ≥0, LipschitzWith K' (fun y ↦ ζ y * ∫ z in G, ρ j (y - z))) ∧
      HasCompactSupport (fun y ↦ ζ y * ∫ z in G, ρ j (y - z)) ∧
      ∫ y, ‖fderiv ℝ (fun y ↦ ζ y * ∫ z in G, ρ j (y - z)) y‖ ≤
        (∫ y, ζ y * ‖fderiv ℝ (fun x ↦ ∫ z in G, ρ j (x - z)) y‖) +
          ∫ y, (∫ z in G, ρ j (y - z)) * ‖fderiv ℝ ζ y‖ := fun j ↦ by
    obtain ⟨L, hL⟩ := hLip j
    exact Submission.deGiorgiSobInd_mul_lipschitz_fderiv_bound (n + 1) ζ
      (fun x ↦ ∫ z in G, ρ j (x - z)) K L hζ hζc hζ0 hL (hbd j)
  -- Step 2 (Gauss–Green duality): `∫ ζ |D u j| ≤ ∫ (∫ ζ(y) ρ j (y - z) dy) dμ(z)`.
  have hkey : ∀ j : ℕ, ∫ y, ζ y * ‖fderiv ℝ (fun x ↦ ∫ z in G, ρ j (x - z)) y‖ ≤
      ∫ z, (∫ y, ζ y * ρ j (y - z)) ∂μ := fun j ↦
    Submission.deGiorgiSobInd_mollified_fderiv_le (n + 1) U G μ ν hU hG hGG ζ (ρ j)
      (δ / ((j : ℝ) + 1)) hζ.continuous hζc hζ0 (hρC j) (hρc j) (hρ0 j) (hρs j)
      ((Metric.cthickening_mono (hr j) _).trans hδU)
  -- Step 3: the bounds tend to `∫ ζ dμ + ∫_G |Dζ|`; `|Dζ| ≤ K` vanishes off `tsupport ζ`.
  have hμlim := Submission.deGiorgiSobInd_mollified_integral_tendsto (n + 1) μ ζ ρ
    (fun j : ℕ ↦ δ / ((j : ℝ) + 1)) δ hζ.continuous hζc hδμ (fun j ↦ (hρC j).continuous)
    hρ0 hρ1 hρs hr hr0
  have hDζ : Integrable (fun y ↦ ‖fderiv ℝ ζ y‖) := by
    have hsupp : Function.support (fun y ↦ ‖fderiv ℝ ζ y‖) ⊆ tsupport ζ := by
      intro y hy
      by_contra h
      exact hy (by simp [fderiv_of_notMem_tsupport ℝ h])
    refine (integrableOn_iff_integrable_of_support_subset hsupp).1 ?_
    exact Measure.integrableOn_of_bounded (M := K) hζc.isCompact.measure_lt_top.ne
      (measurable_fderiv ℝ ζ).norm.aestronglyMeasurable
      (Eventually.of_forall fun y ↦ by simpa using norm_fderiv_le_of_lipschitz ℝ hζ)
  have hlim := hμlim.add (hweak (fun y ↦ ‖fderiv ℝ ζ y‖) hDζ)
  -- Step 4: the Sobolev inequality for each `w j`, `w j → ζ χ_G` a.e., and Fatou's lemma.
  have hbound : ∀ j : ℕ, eLpNorm (fun y ↦ ζ y * ∫ z in G, ρ j (y - z)) ((n + 1 : ℝ≥0∞) / n)
      volume ≤ ENNReal.ofReal (c * ((∫ z, (∫ y, ζ y * ρ j (y - z)) ∂μ) +
        ∫ y, (∫ z in G, ρ j (y - z)) * ‖fderiv ℝ ζ y‖)) := by
    intro j
    obtain ⟨⟨K', hK'⟩, hcs, hgrad⟩ := hw j
    refine (hsob _ K' hK' hcs).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (hgrad.trans (by linarith [hkey j])) hc.le
  have hwlim : ∀ᵐ y ∂(volume : Measure (Rn (n + 1))),
      Tendsto (fun j : ℕ ↦ ζ y * ∫ z in G, ρ j (y - z)) atTop (𝓝 (G.indicator ζ y)) := by
    filter_upwards [hae] with y hy
    have hy' : G.indicator ζ y = ζ y * G.indicator (fun _ ↦ (1 : ℝ)) y := by
      by_cases hyG : y ∈ G <;> simp [hyG]
    rw [hy']
    exact hy.const_mul (ζ y)
  calc eLpNorm (G.indicator ζ) ((n + 1 : ℝ≥0∞) / n) volume
      ≤ atTop.liminf fun j : ℕ ↦
          eLpNorm (fun y ↦ ζ y * ∫ z in G, ρ j (y - z)) ((n + 1 : ℝ≥0∞) / n) volume :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm
          (fun j ↦ (hw j).1.choose_spec.continuous.aestronglyMeasurable) _
          (hζ.continuous.aestronglyMeasurable.indicator₀ hG) hwlim
    _ ≤ atTop.liminf fun j : ℕ ↦ ENNReal.ofReal (c * ((∫ z, (∫ y, ζ y * ρ j (y - z)) ∂μ) +
          ∫ y, (∫ z in G, ρ j (y - z)) * ‖fderiv ℝ ζ y‖)) :=
        liminf_le_liminf (Eventually.of_forall hbound)
    _ = ENNReal.ofReal (c * (∫ y, ζ y ∂μ + ∫ y in G, ‖fderiv ℝ ζ y‖)) :=
        ((ENNReal.continuous_ofReal.tendsto _).comp (hlim.const_mul c)).liminf_eq

/-- **Isoperimetric differential inequality** at a differentiability radius, from the proof of
Simon Ch. 3, Theorem 4.3 (p. 83, `chapter-03.txt` lines 706–722): with
`V(r) = L^{n+1}(G ∩ B_r(x))` and `B̄_ρ(x) ⊆ U`, `V(ρ)^{n/(n+1)} ≤ c (μ(B_ρ(x)) + V'(ρ))`.
Let `c` be the constant of `deGiorgiDens_sobolev_indicator` and `p = (n+1)/n`, so that
`1/p = n/(n+1)` (also for `n = 0`, where `p = ∞`). For `s ∈ (0, ρ)` with `V(s) > 0`, apply it to
the radial cut-off `ζ_s` of `deGiorgiDens_radial_cutoff` (`ζ_s = 1` on `B_s`, `0 ≤ ζ_s ≤ 1_{B_ρ}`,
`∫_G |Dζ_s| = (V(ρ) - V(s))/(ρ - s)`): since `1_{G ∩ B_s} ≤ χ_G ζ_s` and `∫ ζ_s dμ ≤ μ(B_ρ)`,
`V(s)^{n/(n+1)} = ‖1_{G ∩ B_s}‖_p ≤ ‖χ_G ζ_s‖_p ≤ c (μ(B_ρ) + (V(ρ) - V(s))/(ρ - s))`. As `s ↑ ρ`,
`V(s) → V(ρ) > 0` (so the bound holds for all `s` near `ρ`) and the difference quotient tends to
`V'(ρ)`. -/
theorem Submission.deGiorgiDens_ball_isoperimetric : ∀ (n : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ (U G : Set (Rn (n + 1))) (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)), IsOpen U → NullMeasurableSet G volume → IsGaussGreenPair U G μ ν → ∀ (x : Rn (n + 1)) (ρ d : ℝ), 0 < ρ → Metric.closedBall x ρ ⊆ U → 0 < volume (G ∩ Metric.ball x ρ) → HasDerivAt (fun r : ℝ ↦ (volume (G ∩ Metric.ball x r)).toReal) d ρ → (volume (G ∩ Metric.ball x ρ)).toReal ^ ((n : ℝ) / (n + 1)) ≤ c * ((μ (Metric.ball x ρ)).toReal + d) := by
  intro n
  -- Step 0: `c` is the Sobolev constant; `p = (n+1)/n ≠ 0`, `1/p = n/(n+1)` (`1/⊤ = 0` if `n = 0`).
  obtain ⟨c, hc, hsob⟩ := Submission.deGiorgiDens_sobolev_indicator n
  refine ⟨c, hc, fun U G μ ν hU hG hμν x ρ d hρ hcl hpos hderiv ↦ ?_⟩
  have hp0 : (n + 1 : ℝ≥0∞) / n ≠ 0 := ENNReal.div_ne_zero.2 ⟨by simp, ENNReal.natCast_ne_top n⟩
  have hpa : 1 / ((n + 1 : ℝ≥0∞) / n).toReal = (n : ℝ) / (n + 1) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_add (ENNReal.natCast_ne_top n) ENNReal.one_ne_top,
      ENNReal.toReal_natCast, ENNReal.toReal_one, one_div_div]
  -- Step 1: `V(r) = L(G ∩ B_r)` is finite and non-decreasing, `V(ρ) > 0`, and `μ(B_ρ) < ∞`.
  set V : ℝ → ℝ := fun r ↦ (volume (G ∩ Metric.ball x r)).toReal
  have hfin : ∀ r, volume (G ∩ Metric.ball x r) ≠ ∞ := fun r ↦
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  have hVρ : 0 < V ρ := ENNReal.toReal_pos hpos.ne' (hfin ρ)
  have hμB : μ (Metric.ball x ρ) ≠ ∞ :=
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      (hμν.2.1 _ (isCompact_closedBall x ρ) hcl)).ne
  -- Step 2: `(∗) V(s)^{n/(n+1)} ≤ c (μ(B_ρ) + (V(ρ) - V(s))/(ρ - s))` for `s ∈ (0, ρ)`, `V(s) > 0`.
  have hstar : ∀ s, 0 < s → s < ρ → 0 < volume (G ∩ Metric.ball x s) →
      V s ^ ((n : ℝ) / (n + 1)) ≤ c * ((μ (Metric.ball x ρ)).toReal + (V ρ - V s) / (ρ - s)) := by
    intro s hs hsρ hVs
    obtain ⟨ζ, ⟨K, hK⟩, hζc, hζt, hζ01, hζ1, hζ0, hζD⟩ :=
      Submission.deGiorgiDens_radial_cutoff (n + 1) x s ρ hs hsρ
    have hS := hsob U G μ ν hU hG hμν ζ K hK hζc (hζt.trans hcl) fun y ↦ (hζ01 y).1
    -- (a) `∫_G |Dζ_s| = (V(ρ) - V(s))/(ρ - s) ≥ 0`.
    have hD : ∫ y in G, ‖fderiv ℝ ζ y‖ = (V ρ - V s) / (ρ - s) := hζD G hG
    have hD0 : 0 ≤ (V ρ - V s) / (ρ - s) :=
      div_nonneg (sub_nonneg.2 (ENNReal.toReal_mono (hfin ρ)
        (measure_mono (inter_subset_inter_right _ (Metric.ball_subset_ball hsρ.le)))))
        (sub_nonneg.2 hsρ.le)
    -- (b) `0 ≤ ∫ ζ_s dμ ≤ ∫ 1_{B_ρ} dμ = μ(B_ρ)`.
    have hI0 : 0 ≤ ∫ y, ζ y ∂μ := integral_nonneg fun y ↦ (hζ01 y).1
    have hI : ∫ y, ζ y ∂μ ≤ (μ (Metric.ball x ρ)).toReal := by
      calc ∫ y, ζ y ∂μ ≤ ∫ y, (Metric.ball x ρ).indicator 1 y ∂μ := by
            refine integral_mono_of_nonneg (ae_of_all _ fun y ↦ (hζ01 y).1)
              ((integrable_indicator_iff measurableSet_ball).2
                (integrableOn_const (C := (1 : ℝ)) hμB)) (ae_of_all _ fun y ↦ ?_)
            by_cases hy : y ∈ Metric.ball x ρ
            · rw [indicator_of_mem hy]
              exact (hζ01 y).2
            · rw [indicator_of_notMem hy, hζ0 y hy]
        _ = (μ (Metric.ball x ρ)).toReal := integral_indicator_one measurableSet_ball
    -- (c) `L(G ∩ B_s)^{n/(n+1)} = ‖1_{G ∩ B_s}‖_p ≤ ‖χ_G ζ_s‖_p`, as `ζ_s = 1` on `B_s`.
    have hGs : NullMeasurableSet (G ∩ Metric.ball x s) volume :=
      hG.inter measurableSet_ball.nullMeasurableSet
    have hlow : volume (G ∩ Metric.ball x s) ^ ((n : ℝ) / (n + 1)) ≤
        eLpNorm (G.indicator ζ) ((n + 1 : ℝ≥0∞) / n) volume := by
      have h1 := eLpNorm_indicator_const' (c := (1 : ℝ)) hGs hVs.ne' hp0
      rw [hpa, enorm_one, one_mul] at h1
      rw [← h1]
      refine eLpNorm_mono (aestronglyMeasurable_const.indicator₀ hGs) fun y ↦ ?_
      by_cases hy : y ∈ G ∩ Metric.ball x s
      · rw [indicator_of_mem hy, indicator_of_mem hy.1, hζ1 y hy.2]
      · rw [indicator_of_notMem hy, norm_zero]
        exact norm_nonneg _
    -- Combine (a)–(c) and pass to real numbers.
    have hR0 : 0 ≤ c * (∫ y, ζ y ∂μ + ∫ y in G, ‖fderiv ℝ ζ y‖) := by
      rw [hD]
      exact mul_nonneg hc.le (add_nonneg hI0 hD0)
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hlow.trans hS)
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hR0, hD] at hreal
    exact hreal.trans (mul_le_mul_of_nonneg_left (add_le_add hI le_rfl) hc.le)
  -- Step 3: let `s ↑ ρ`; `V` is continuous at `ρ` and its difference quotients tend to `d`.
  have hcont : Tendsto V (𝓝[<] ρ) (𝓝 (V ρ)) :=
    hderiv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hslope : Tendsto (fun s ↦ (V ρ - V s) / (ρ - s)) (𝓝[<] ρ) (𝓝 d) :=
    ((hasDerivAt_iff_tendsto_slope.1 hderiv).mono_left
      (nhdsWithin_mono _ fun s (hs : s < ρ) ↦ hs.ne)).congr fun s ↦ by
        rw [slope_comm, slope_def_field]
  show V ρ ^ ((n : ℝ) / (n + 1)) ≤ c * ((μ (Metric.ball x ρ)).toReal + d)
  refine le_of_tendsto_of_tendsto (hcont.rpow_const (Or.inl hVρ.ne'))
    ((tendsto_const_nhds.add hslope).const_mul c) ?_
  filter_upwards [Ioo_mem_nhdsLT hρ, hcont.eventually (lt_mem_nhds hVρ)] with s hs hVs
  exact hstar s hs.1 hs.2 (ENNReal.toReal_pos_iff.1 hVs).1
/-- **Integration of the differential inequality `V^{n/(n+1)} ≤ K V'`** (Simon Ch. 3, proof of
Theorem 4.3, (10), `chapter-03.txt` lines 723–729: "Integration (using the fact that
`L^{n+1}(E ∩ B_ρ(0))` is non-decreasing) then implies (10)"). If `V > 0` is non-decreasing on
`(0, ρ₁)` and for a.e. `ρ ∈ (0, ρ₁)` it has a derivative `d` with `V(ρ)^{n/(n+1)} ≤ K d`, then
`(ρ/((n+1)K))^{n+1} ≤ V(ρ)` on `(0, ρ₁)`. By the chain rule `W = V^{1/(n+1)}` is non-decreasing
with `W' ≥ s = 1/((n+1)K)` a.e. Its monotone extension `g` (`0` on `(-∞, 0]`, `W(min x ρ)` on
`(0, ∞)`) has, a.e., derivative the density of its Stieltjes measure `μ` with respect to `L¹`, so
`s ρ ≤ ∫_{(0,ρ)} g' ≤ μ((0, ρ]) ≤ W(ρ)`; raising to the power `n + 1` gives the claim. -/
theorem Submission.deGiorgiDens_lower_bound_of_deriv : ∀ (n : ℕ) (K ρ₁ : ℝ) (V : ℝ → ℝ), 0 < K → MonotoneOn V (Ioo 0 ρ₁) → (∀ ρ ∈ Ioo 0 ρ₁, 0 < V ρ) → (∀ᵐ ρ ∂(volume : Measure ℝ), ρ ∈ Ioo 0 ρ₁ → ∃ d : ℝ, HasDerivAt V d ρ ∧ V ρ ^ ((n : ℝ) / (n + 1)) ≤ K * d) → ∀ ρ ∈ Ioo 0 ρ₁, (ρ / ((n + 1) * K)) ^ (n + 1) ≤ V ρ := by
  intro n K ρ₁ V hK hmono hpos hderiv ρ hρ
  -- Step 1: `W = V^b` with `b = 1/(n+1)` is positive and non-decreasing on `(0, ρ₁)`.
  set b : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹ with hb_def
  have hb : 0 < b := inv_pos.mpr (by positivity)
  set W : ℝ → ℝ := fun t => V t ^ b
  have hWmono : MonotoneOn W (Ioo 0 ρ₁) := fun x hx y hy hxy =>
    Real.rpow_le_rpow (hpos x hx).le (hmono hx hy hxy) hb.le
  have hWpos : ∀ t ∈ Ioo 0 ρ₁, 0 < W t := fun t ht => Real.rpow_pos_of_pos (hpos t ht) b
  set s : ℝ := (((n : ℝ) + 1) * K)⁻¹ with hs_def
  have hs : 0 < s := inv_pos.mpr (by positivity)
  have hsb : s = b / K := by
    rw [hs_def, hb_def, mul_inv, div_eq_mul_inv, Nat.cast_add, Nat.cast_one]
  -- Step 2: a.e. on `(0, ρ₁)`, `W' = b V^{b-1} V' = V'/((n+1) V^{n/(n+1)}) ≥ s`.
  have hWderiv : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo 0 ρ₁ →
      ∃ w : ℝ, HasDerivAt W w t ∧ s ≤ w := by
    filter_upwards [hderiv] with t ht htI
    obtain ⟨d, hd, hdK⟩ := ht htI
    have hVt := hpos t htI
    refine ⟨d * b * V t ^ (b - 1), hd.rpow_const (Or.inl hVt.ne'), ?_⟩
    have hexp : b - 1 = -((n : ℝ) / (n + 1)) := by
      rw [hb_def]; push_cast; field_simp; ring
    rw [hexp, Real.rpow_neg hVt.le]
    have hA : 0 < V t ^ ((n : ℝ) / (n + 1)) := Real.rpow_pos_of_pos hVt _
    rw [le_mul_inv_iff₀ hA, hsb]
    calc b / K * V t ^ ((n : ℝ) / (n + 1)) = b * (V t ^ ((n : ℝ) / (n + 1)) / K) := by ring
      _ ≤ b * d := mul_le_mul_of_nonneg_left (by rw [div_le_iff₀ hK]; linarith) hb.le
      _ = d * b := by ring
  -- Steps 3–4: `s ρ ≤ W ρ`.
  have key : s * ρ ≤ W ρ := by
    have hρ0 : 0 < ρ := hρ.1
    have hρ1 : ρ < ρ₁ := hρ.2
    have hmemI : ∀ x, 0 < x → min x ρ ∈ Ioo 0 ρ₁ := fun x hx =>
      ⟨lt_min hx hρ0, (min_le_right x ρ).trans_lt hρ1⟩
    -- The monotone extension `g` of `W|(0, ρ]` to `ℝ`; `W > 0` makes the value `0` on `(-∞, 0]`
    -- compatible with monotonicity, which replaces the limit `ε ↓ 0`.
    set g : ℝ → ℝ := fun x => if x ≤ 0 then 0 else W (min x ρ) with hg_def
    have hg : Monotone g := by
      intro x y hxy
      simp only [hg_def]
      split_ifs with hx hy hy
      · exact le_rfl
      · exact (hWpos _ (hmemI y (not_le.mp hy))).le
      · exact absurd (hxy.trans hy) hx
      · exact hWmono (hmemI x (not_le.mp hx)) (hmemI y (not_le.mp hy)) (min_le_min_right ρ hxy)
    -- The Stieltjes measure of `g` gives `(0, ρ]` mass `g(ρ+) - g(0+) ≤ W(ρ) - 0`.
    set μ : Measure ℝ := hg.stieltjesFunction.measure with hμ
    have hμle : μ (Ioc 0 ρ) ≤ ENNReal.ofReal (W ρ) := by
      rw [hμ, StieltjesFunction.measure_Ioc, hg.stieltjesFunction_eq, hg.stieltjesFunction_eq]
      apply ENNReal.ofReal_le_ofReal
      have h1 : Function.rightLim g ρ ≤ g (ρ + 1) := hg.rightLim_le (by linarith)
      have h2 : g 0 ≤ Function.rightLim g 0 := hg.le_rightLim le_rfl
      have h3 : g (ρ + 1) = W ρ := by
        simp only [hg_def]
        rw [ite_eq_right (not_le.mpr (by linarith)), min_eq_right (by linarith)]
      have h4 : g 0 = 0 := by simp [hg_def]
      linarith
    -- A.e. on `(0, ρ)`, `g' = W' ≥ s` and `g' = dμ/dL¹`.
    have hae : ∀ᵐ x ∂(volume.restrict (Ioo 0 ρ)), ENNReal.ofReal s ≤ μ.rnDeriv volume x := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hWderiv, hg.ae_hasDerivAt] with x hx hgx hxI
      obtain ⟨w, hw, hsw⟩ := hx ⟨hxI.1, hxI.2.trans hρ1⟩
      have hgw : HasDerivAt g w x := by
        apply hw.congr_of_eventuallyEq
        filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
        simp only [hg_def]
        rw [ite_eq_right (not_le.mpr hy.1), min_eq_left hy.2.le]
      have hwx := hgx.unique hgw
      calc ENNReal.ofReal s ≤ ENNReal.ofReal w := ENNReal.ofReal_le_ofReal hsw
        _ = ENNReal.ofReal (μ.rnDeriv volume x).toReal := by rw [hwx]
        _ ≤ μ.rnDeriv volume x := ENNReal.ofReal_toReal_le
    -- Integrate: `s ρ ≤ ∫_{(0,ρ)} dμ/dL¹ ≤ μ((0, ρ]) ≤ W ρ`.
    have hint : ENNReal.ofReal s * volume (Ioo 0 ρ) ≤ μ (Ioc 0 ρ) :=
      calc ENNReal.ofReal s * volume (Ioo 0 ρ) = ∫⁻ _ in Ioo 0 ρ, ENNReal.ofReal s := by
            rw [setLIntegral_const]
        _ ≤ ∫⁻ x in Ioo 0 ρ, μ.rnDeriv volume x := lintegral_mono_ae hae
        _ ≤ volume.withDensity (μ.rnDeriv volume) (Ioo 0 ρ) := withDensity_apply_le _ _
        _ ≤ μ (Ioo 0 ρ) := Measure.le_iff'.1 (Measure.withDensity_rnDeriv_le μ volume) _
        _ ≤ μ (Ioc 0 ρ) := measure_mono Ioo_subset_Ioc_self
    rw [Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul hs.le] at hint
    exact (ENNReal.ofReal_le_ofReal_iff (hWpos ρ hρ).le).mp (hint.trans hμle)
  -- Step 5: `V ρ = (W ρ)^{n+1} ≥ (s ρ)^{n+1}`.
  have hsρ : ρ / ((n + 1) * K) = s * ρ := by rw [hs_def]; ring
  calc (ρ / ((n + 1) * K)) ^ (n + 1) = (s * ρ) ^ (n + 1) := by rw [hsρ]
    _ ≤ W ρ ^ (n + 1) := pow_le_pow_left₀ (mul_pos hs hρ.1).le key _
    _ = V ρ := Real.rpow_inv_natCast_pow (hpos ρ hρ).le (Nat.succ_ne_zero n)

/-- **Upper mass bound from the half-average condition** (Simon Ch. 3, proof of 4.3, (5)–(6),
p. 82, `chapter-03.txt` lines 641–652): if `B_{ρ₁}(x) ⊆ U`, `|w| ≤ 1` and
`μ(B_ρ(x)) ≤ 2 ∫_{B_ρ(x)} ⟨ν, w⟩ dμ` for all `ρ ∈ (0, ρ₁)`, then
`μ(B_ρ(x)) ≤ 2(n + 1) ω_{n+1} ρⁿ` for all `ρ ∈ (0, ρ₁)`, where `ω_{n+1} = L^{n+1}(B_1(0))`.
`V(r) = L^{n+1}(E ∩ B_r(x))` is monotone, hence differentiable at `L¹`-a.e. `r`
(`Monotone.ae_differentiableAt`). At such `r ∈ (0, ρ₁)` the first-variation bound
(`deGiorgiDens_ball_normal_le_deriv`) and the hypothesis give `μ(B_r(x)) ≤ 2 V'(r)`, and
`V'(r) ≤ (n + 1) ω_{n+1} rⁿ` because `t ↦ ω_{n+1} t^{n+1} − V(t)` is non-decreasing on `[0, ∞)`
(`V(t) − V(s) ≤ L^{n+1}(B_t(x) ∖ B_s(x))`). For `ρ < t < ρ₁` such an `r ∈ (ρ, t)` gives
`μ(B_ρ(x)) ≤ μ(B_r(x)) ≤ 2(n + 1) ω_{n+1} tⁿ`; let `t ↓ ρ`. -/
theorem Submission.deGiorgiDens_ball_mass_le : ∀ (n : ℕ) (U E : Set (Rn (n + 1))) (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)), IsOpen U → NullMeasurableSet E volume → IsGaussGreenPair U E μ ν → ∀ (x w : Rn (n + 1)) (ρ₁ : ℝ), ‖w‖ ≤ 1 → Metric.ball x ρ₁ ⊆ U → (∀ ρ ∈ Ioo 0 ρ₁, (μ (Metric.ball x ρ)).toReal ≤ 2 * ∫ y in Metric.ball x ρ, inner ℝ (ν y) w ∂μ) → ∀ ρ ∈ Ioo 0 ρ₁, μ (Metric.ball x ρ) ≤ ENNReal.ofReal (2 * (n + 1) * (volume (Metric.ball (0 : Rn (n + 1)) 1)).toReal * ρ ^ n) := by
  intro n U E μ ν hU hE hpair x w ρ₁ hw hxU hhalf ρ hρ
  set ω : ℝ := (volume (Metric.ball (0 : Rn (n + 1)) 1)).toReal with hω
  have hω0 : 0 ≤ ω := ENNReal.toReal_nonneg
  -- Step 1: `V(r) = L^{n+1}(E ∩ B_r(x))` is finite and monotone, and `μ(B_r(x)) < ∞` for
  -- `r < ρ₁` (`B̄_r(x)` is a compact subset of `U`).
  have hBfin : ∀ r : ℝ, volume (Metric.ball x r) ≠ ∞ := fun r => measure_ball_lt_top.ne
  have hVfin : ∀ r : ℝ, volume (E ∩ Metric.ball x r) ≠ ∞ := fun r =>
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  have hVmono : Monotone fun r : ℝ ↦ (volume (E ∩ Metric.ball x r)).toReal := fun r s hrs =>
    ENNReal.toReal_mono (hVfin s)
      (measure_mono (inter_subset_inter_right E (Metric.ball_subset_ball hrs)))
  have hμfin : ∀ r < ρ₁, μ (Metric.ball x r) ≠ ∞ := fun r hr =>
    ((measure_mono Metric.ball_subset_closedBall).trans_lt (hpair.2.1 _ (isCompact_closedBall x r)
      ((Metric.closedBall_subset_ball hr).trans hxU))).ne
  -- Step 2: `L^{n+1}(B_r(x)) = ω r^{n+1}` for `r ≥ 0`.
  have hball : ∀ r : ℝ, 0 ≤ r → (volume (Metric.ball x r)).toReal = ω * r ^ (n + 1) := by
    intro r hr
    rw [hω, Measure.addHaar_ball volume x hr, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hr _)]
    exact mul_comm _ _
  -- Step 3: `V(t) − V(s) ≤ ω (t^{n+1} − s^{n+1})` for `0 ≤ s ≤ t`, as
  -- `E ∩ B_t(x) ⊆ (E ∩ B_s(x)) ∪ (B_t(x) ∖ B_s(x))`.
  have hgrowth : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      (volume (E ∩ Metric.ball x t)).toReal + ω * s ^ (n + 1) ≤
        (volume (E ∩ Metric.ball x s)).toReal + ω * t ^ (n + 1) := by
    intro s t hs hst
    have hsub : Metric.ball x s ⊆ Metric.ball x t := Metric.ball_subset_ball hst
    have hcover : E ∩ Metric.ball x t ⊆
        (E ∩ Metric.ball x s) ∪ (Metric.ball x t \ Metric.ball x s) := by
      intro y hy
      by_cases hys : y ∈ Metric.ball x s
      · exact Or.inl ⟨hy.1, hys⟩
      · exact Or.inr ⟨hy.2, hys⟩
    have hsplit : volume (Metric.ball x t \ Metric.ball x s) + volume (Metric.ball x s) =
        volume (Metric.ball x t) := by
      have h := measure_sdiff_add_inter (μ := volume) (Metric.ball x t)
        (measurableSet_ball : MeasurableSet (Metric.ball x s))
      rwa [inter_eq_right.2 hsub] at h
    have hle : volume (E ∩ Metric.ball x t) + volume (Metric.ball x s) ≤
        volume (E ∩ Metric.ball x s) + volume (Metric.ball x t) := by
      calc volume (E ∩ Metric.ball x t) + volume (Metric.ball x s)
          ≤ volume (E ∩ Metric.ball x s) + volume (Metric.ball x t \ Metric.ball x s) +
              volume (Metric.ball x s) := by
            gcongr
            exact (measure_mono hcover).trans (measure_union_le _ _)
        _ = volume (E ∩ Metric.ball x s) + volume (Metric.ball x t) := by rw [add_assoc, hsplit]
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hVfin s, hBfin t⟩) hle
    rwa [ENNReal.toReal_add (hVfin t) (hBfin s), ENNReal.toReal_add (hVfin s) (hBfin t),
      hball s hs, hball t (hs.trans hst)] at h
  -- Step 4 (Simon (6) at a.e. radius): wherever `V` is differentiable in `(0, ρ₁)`,
  -- `μ(B_r(x)) ≤ 2 V'(r) ≤ 2(n + 1) ω rⁿ`.
  have hgood : ∀ᵐ r : ℝ, r ∈ Ioo 0 ρ₁ →
      (μ (Metric.ball x r)).toReal ≤ 2 * (n + 1) * ω * r ^ n := by
    filter_upwards [hVmono.ae_differentiableAt] with r hdiff hr
    have hd := hdiff.hasDerivAt
    -- (a) the first-variation bound (Simon (5)): `∫_{B_r(x)} ⟨ν, w⟩ dμ ≤ V'(r)`.
    have h1 := Submission.deGiorgiDens_ball_normal_le_deriv (n + 1) U E μ ν hU hE hpair x w r _
      hr.1 ((Metric.closedBall_subset_ball hr.2).trans hxU) hw hd
    -- (b) `V'(r) ≤ (n + 1) ω rⁿ`: `t ↦ ω t^{n+1} − V(t)` has non-negative slopes right of `r`.
    have hg : HasDerivAt (fun t : ℝ ↦ ω * t ^ (n + 1) - (volume (E ∩ Metric.ball x t)).toReal)
        ((n + 1) * ω * r ^ n - deriv (fun t : ℝ ↦ (volume (E ∩ Metric.ball x t)).toReal) r) r :=
      (((hasDerivAt_pow (n + 1) r).const_mul ω).sub hd).congr_deriv (by
        rw [Nat.add_sub_cancel]; push_cast; ring)
    have h2 : 0 ≤ (n + 1) * ω * r ^ n -
        deriv (fun t : ℝ ↦ (volume (E ∩ Metric.ball x t)).toReal) r := by
      refine ge_of_tendsto ((hasDerivAt_iff_tendsto_slope.1 hg).mono_left (nhdsGT_le_nhdsNE r)) ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hrt : r < t := ht
      have hmono : ω * r ^ (n + 1) - (volume (E ∩ Metric.ball x r)).toReal ≤
          ω * t ^ (n + 1) - (volume (E ∩ Metric.ball x t)).toReal := by
        linarith [hgrowth r t hr.1.le hrt.le]
      rw [slope_def_field]
      exact div_nonneg (sub_nonneg.2 hmono) (sub_nonneg.2 hrt.le)
    linarith [hhalf r hr]
  -- Step 5 (Simon (6) at every radius): for `ρ < t < ρ₁` the interval `(ρ, t)` has positive
  -- measure, so it contains such an `r`, and `μ(B_ρ(x)) ≤ μ(B_r(x)) ≤ 2(n + 1) ω tⁿ`; let `t ↓ ρ`.
  obtain ⟨hρ0, hρ1⟩ := hρ
  have hcoef : 0 ≤ 2 * ((n : ℝ) + 1) * ω := mul_nonneg (by positivity) hω0
  have hbound : ∀ t ∈ Ioo ρ ρ₁, (μ (Metric.ball x ρ)).toReal ≤ 2 * (n + 1) * ω * t ^ n := by
    intro t ht
    have hpos : volume (Ioo ρ t) ≠ 0 := by
      rw [Real.volume_Ioo, ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_pos]
      exact ht.1
    obtain ⟨r, hr, hrgood⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hgood)
    have hr' : r ∈ Ioo 0 ρ₁ := ⟨hρ0.trans hr.1, hr.2.trans ht.2⟩
    calc (μ (Metric.ball x ρ)).toReal ≤ (μ (Metric.ball x r)).toReal :=
          ENNReal.toReal_mono (hμfin r hr'.2) (measure_mono (Metric.ball_subset_ball hr.1.le))
      _ ≤ 2 * (n + 1) * ω * r ^ n := hrgood hr'
      _ ≤ 2 * (n + 1) * ω * t ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr'.1.le hr.2.le n) hcoef
  have hlim : Tendsto (fun t : ℝ ↦ 2 * (n + 1) * ω * t ^ n) (𝓝[>] ρ)
      (𝓝 (2 * (n + 1) * ω * ρ ^ n)) :=
    ((continuous_const.mul (continuous_pow n)).tendsto ρ).mono_left nhdsWithin_le_nhds
  rw [ENNReal.le_ofReal_iff_toReal_le (hμfin ρ hρ1) (mul_nonneg hcoef (pow_nonneg hρ0.le n))]
  exact ge_of_tendsto hlim (eventually_of_mem (Ioo_mem_nhdsGT hρ1) hbound)
/-- **Lower volume bound** in the proof of De Giorgi's theorem (Simon Ch. 3, proof of Theorem 4.3,
(10)–(11), `chapter-03.txt` lines 706–733; parent Step 8 (i)–(iii)). Let `(μ, ν)` be a Gauss–Green
pair for `(U, G)`, `|w| ≤ 1`, `B_{ρ₁}(x) ⊆ U`, and `0 < μ(B_ρ(x)) ≤ 2 ∫_{B_ρ(x)} ν · w dμ` for
`ρ ∈ (0, ρ₁)`. Put `V(r) = L^{n+1}(G ∩ B_r(x))` (finite, non-decreasing), let `c_F` be the constant
of `deGiorgiDens_ball_isoperimetric` and `K = 3 c_F`.
(i) `V > 0` on `(0, ρ₁)`: if `V(r) = 0`, then `V` vanishes on `(-∞, r)`, so `V'(r/2) = 0` and
`deGiorgiDens_ball_normal_le_deriv` gives `∫_{B_{r/2}(x)} ν · w dμ ≤ 0 < μ(B_{r/2}(x))`, which
contradicts the hypothesis. (ii) At every `r ∈ (0, ρ₁)` where the monotone `V` is differentiable
(Lebesgue-a.e. `r`), `μ(B_r(x)) ≤ 2 V'(r)` by `deGiorgiDens_ball_normal_le_deriv`, so the
isoperimetric inequality gives `V(r)^{n/(n+1)} ≤ c_F (μ(B_r(x)) + V'(r)) ≤ K V'(r)`.
(iii) `deGiorgiDens_lower_bound_of_deriv` integrates this to
`V(ρ) ≥ (ρ / ((n + 1) K))^{n+1} = c ρ^{n+1}` with `c = ((n + 1) K)^{-(n+1)}`. -/
theorem Submission.deGiorgiDens_ball_volume_ge : ∀ (n : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ (U G : Set (Rn (n + 1))) (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)), IsOpen U → NullMeasurableSet G volume → IsGaussGreenPair U G μ ν → ∀ (x w : Rn (n + 1)) (ρ₁ : ℝ), ‖w‖ ≤ 1 → Metric.ball x ρ₁ ⊆ U → (∀ ρ ∈ Ioo 0 ρ₁, 0 < μ (Metric.ball x ρ) ∧ (μ (Metric.ball x ρ)).toReal ≤ 2 * ∫ y in Metric.ball x ρ, inner ℝ (ν y) w ∂μ) → ∀ ρ ∈ Ioo 0 ρ₁, ENNReal.ofReal (c * ρ ^ (n + 1)) ≤ volume (G ∩ Metric.ball x ρ) := by
  intro n
  obtain ⟨cF, hcF, hiso⟩ := Submission.deGiorgiDens_ball_isoperimetric n
  have hK : 0 < 3 * cF := by positivity
  refine ⟨(1 / ((n + 1) * (3 * cF))) ^ (n + 1), by positivity, ?_⟩
  intro U G μ ν hU hG hGG x w ρ₁ hw hball hmass ρ hρ
  -- `V(r) = L^{n+1}(G ∩ B_r(x))` is finite and non-decreasing.
  set V : ℝ → ℝ := fun r ↦ (volume (G ∩ Metric.ball x r)).toReal
  have hfin : ∀ r, volume (G ∩ Metric.ball x r) ≠ ∞ := fun r ↦
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  have hVmono : Monotone V := fun r s hrs ↦ ENNReal.toReal_mono (hfin s)
    (measure_mono (inter_subset_inter_right _ (Metric.ball_subset_ball hrs)))
  -- For `r ∈ (0, ρ₁)`: `B̄_r(x) ⊆ U`, hence `0 < μ(B_r(x)) < ∞`.
  have hcl : ∀ r ∈ Ioo 0 ρ₁, Metric.closedBall x r ⊆ U := fun r hr ↦
    (Metric.closedBall_subset_ball hr.2).trans hball
  have hm : ∀ r ∈ Ioo 0 ρ₁, 0 < (μ (Metric.ball x r)).toReal := fun r hr ↦
    ENNReal.toReal_pos (hmass r hr).1.ne' ((measure_mono Metric.ball_subset_closedBall).trans_lt
      (hGG.2.1 _ (isCompact_closedBall x r) (hcl r hr))).ne
  -- (i) `V > 0` on `(0, ρ₁)`.
  have hVpos : ∀ r ∈ Ioo 0 ρ₁, 0 < V r := by
    intro r hr
    by_contra hVr
    have hr2 : r / 2 ∈ Ioo 0 ρ₁ := ⟨half_pos hr.1, (half_lt_self hr.1).trans hr.2⟩
    -- `V` vanishes on `(-∞, r)`, so `V'(r/2) = 0`.
    have hd : HasDerivAt V 0 (r / 2) := by
      refine (hasDerivAt_const (r / 2) (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds (half_lt_self hr.1)] with t ht
      exact le_antisymm ((hVmono ht.le).trans (not_lt.1 hVr)) ENNReal.toReal_nonneg
    have h₁ := Submission.deGiorgiDens_ball_normal_le_deriv (n + 1) U G μ ν hU hG hGG x w (r / 2) 0
      hr2.1 (hcl _ hr2) hw hd
    linarith [(hmass _ hr2).2, hm _ hr2]
  -- (ii) `V(r)^{n/(n+1)} ≤ 3 c_F V'(r)` wherever `V` is differentiable in `(0, ρ₁)`.
  have hae : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo 0 ρ₁ →
      ∃ d : ℝ, HasDerivAt V d r ∧ V r ^ ((n : ℝ) / (n + 1)) ≤ 3 * cF * d := by
    filter_upwards [hVmono.ae_differentiableAt] with r hr hrI
    have h₁ := Submission.deGiorgiDens_ball_normal_le_deriv (n + 1) U G μ ν hU hG hGG x w r
      (deriv V r) hrI.1 (hcl r hrI) hw hr.hasDerivAt
    have h₂ := hiso U G μ ν hU hG hGG x r (deriv V r) hrI.1 (hcl r hrI)
      (ENNReal.toReal_pos_iff.1 (hVpos r hrI)).1 hr.hasDerivAt
    have h₃ : (μ (Metric.ball x r)).toReal ≤ 2 * deriv V r := by linarith [(hmass r hrI).2]
    refine ⟨deriv V r, hr.hasDerivAt, h₂.trans ?_⟩
    linarith [mul_le_mul_of_nonneg_left h₃ hcF.le]
  -- (iii) Integrate: `V(ρ) ≥ (ρ / ((n + 1) K))^{n+1} = c ρ^{n+1}`.
  have hV := Submission.deGiorgiDens_lower_bound_of_deriv n (3 * cF) ρ₁ V hK (hVmono.monotoneOn _)
    hVpos hae ρ hρ
  rw [ENNReal.ofReal_le_iff_le_toReal (hfin ρ), ← mul_pow, one_div_mul_eq_div]
  exact hV
/-- **The complement of a Gauss–Green pair** (Simon Ch. 3, proof of Theorem 4.3, "Repeating the
same argument with `U ∖ E` in place of `E`", `chapter-03.txt` line 729): if `(μ, ν)` represents
`D χ_E` in `U` (4.1), then `(μ, -ν)` represents `D χ_{U ∖ E}` in `U`. Only the Gauss–Green
identity needs proof. For `g ∈ C¹_c(U; ℝᴺ)` we have `∫ div g = 0`: for each direction `v`,
`t ↦ ∫ g(x + t v) dx` is constant by translation invariance, and differentiating under the
integral sign at `t = 0` gives `∫ Dg(x) v dx = 0`. Since `div g` vanishes off `tsupport g ⊆ U`,
`∫_{U ∖ E} div g = ∫_U div g - ∫_{E ∩ U} div g = ∫ g · ν dμ = -∫ g · (-ν) dμ`. -/
theorem Submission.deGiorgi_gaussGreenPair_compl : ∀ (N : ℕ) (U E : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → NullMeasurableSet E volume → IsGaussGreenPair U E μ ν → IsGaussGreenPair U (U \ E) μ (-ν) := by
  intro N U E μ ν hU hE hpair
  obtain ⟨hμU, hμK, hνm, hν1, hGG⟩ := hpair
  -- The clauses not involving the set: `μ` is unchanged and `|-ν| = |ν| = 1` `μ`-a.e.
  refine ⟨hμU, hμK, hνm.neg, ?_, ?_⟩
  · filter_upwards [hν1] with x hx
    simpa using hx
  intro g hg hgc hgU
  set b := stdOrthonormalBasis ℝ (Rn N)
  have hdiv : ∀ x, Poincare.SimonGMT.Chapter02.euclideanDivergence g x =
      ∑ i, inner ℝ (b i) (fderiv ℝ g x (b i)) :=
    Poincare.SimonGMT.Chapter02.euclideanDivergence_eq_sum_inner b g
  have hDcont : ∀ v : Rn N, Continuous (fun x ↦ fderiv ℝ g x v) := fun v ↦
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- `Dg(·) v` and `div g` are continuous with compact support, hence integrable.
  have hDg : ∀ v : Rn N, Integrable (fun x ↦ fderiv ℝ g x v) volume := fun v ↦
    (hDcont v).integrable_of_hasCompactSupport (hgc.fderiv_apply (𝕜 := ℝ) v)
  have hterm : ∀ i, Integrable (fun x ↦ inner ℝ (b i) (fderiv ℝ g x (b i))) volume := fun i ↦
    (continuous_const.inner (hDcont (b i))).integrable_of_hasCompactSupport
      ((hgc.fderiv_apply (𝕜 := ℝ) (b i)).comp_left (inner_zero_right (b i)))
  have hint : Integrable (Poincare.SimonGMT.Chapter02.euclideanDivergence g) volume := by
    rw [funext hdiv]
    exact integrable_finsetSum _ fun i _ ↦ hterm i
  -- `∫ Dg(x) v dx = 0` for every direction `v`: differentiate `t ↦ ∫ g(x + t v) dx` at `0`.
  have hDzero : ∀ v : Rn N, ∫ x, fderiv ℝ g x v = 0 := by
    intro v
    obtain ⟨C, hC⟩ := (hg.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
      (hgc.fderiv ℝ)
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    -- For `|t| < 1` the derivatives `Dg(x + t v) v` are dominated by `C |v| 1_{K'}`.
    set K' := Metric.cthickening ‖v‖ (tsupport g)
    have hK' : IsCompact K' := hgc.isCompact.cthickening
    have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (volume : Measure (Rn N))) (F := fun (t : ℝ) (x : Rn N) ↦ g (x + t • v))
      (F' := fun (t : ℝ) (x : Rn N) ↦ fderiv ℝ g (x + t • v) v) (x₀ := 0)
      (bound := K'.indicator (fun _ ↦ C * ‖v‖)) (s := Metric.ball 0 1)
      (Metric.ball_mem_nhds 0 one_pos)
      (Eventually.of_forall fun t ↦
        (hg.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
      (by simpa using hg.continuous.integrable_of_hasCompactSupport hgc)
      ((((hg.continuous_fderiv one_ne_zero).comp
        (continuous_id.add continuous_const)).clm_apply continuous_const).aestronglyMeasurable)
      (ae_of_all _ fun x t ht ↦ ?_)
      ((integrableOn_const hK'.measure_lt_top.ne).integrable_indicator hK'.measurableSet)
      (ae_of_all _ fun x t _ ↦ ?_)
    · -- By translation invariance `t ↦ ∫ g(x + t v) dx` is constant, so its derivative vanishes.
      have hconst : (fun t : ℝ ↦ ∫ x, g (x + t • v)) = fun _ ↦ ∫ x, g x :=
        funext fun t ↦ integral_add_right_eq_self g (t • v)
      have h2 := hderiv.2
      rw [hconst] at h2
      simpa using (hasDerivAt_const (0 : ℝ) (∫ x, g x)).unique h2 |>.symm
    · -- The domination bound.
      by_cases hx : x + t • v ∈ tsupport g
      · have hxK : x ∈ K' := by
          refine Metric.mem_cthickening_of_dist_le x (x + t • v) ‖v‖ (tsupport g) hx ?_
          rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul]
          have : ‖t‖ ≤ 1 := by
            have := Metric.mem_ball.1 ht
            rw [dist_zero_right] at this
            exact this.le
          calc ‖t‖ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right this (norm_nonneg v)
            _ = ‖v‖ := one_mul _
        rw [indicator_of_mem hxK]
        exact ((fderiv ℝ g (x + t • v)).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg v))
      · rw [fderiv_of_notMem_tsupport ℝ hx, zero_apply, norm_zero]
        exact indicator_nonneg (fun _ _ ↦ mul_nonneg hC0 (norm_nonneg v)) x
    · -- The derivative of `t ↦ g (x + t • v)` is `Dg(x + t v) v`.
      have h1 : HasDerivAt (fun t : ℝ ↦ x + t • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add x
      exact ((hg.differentiable one_ne_zero (x + t • v)).hasFDerivAt).comp_hasDerivAt t h1
  -- `∫ div g = ∑ᵢ ⟨bᵢ, ∫ Dg(x) bᵢ dx⟩ = 0`.
  have hzero : ∫ x, Poincare.SimonGMT.Chapter02.euclideanDivergence g x = 0 := by
    simp_rw [hdiv]
    rw [integral_finsetSum _ fun i _ ↦ hterm i]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have h := (innerSL ℝ (b i)).integral_comp_comm (hDg (b i))
    simp only [innerSL_apply_apply] at h
    rw [h, hDzero, inner_zero_right]
  -- `div g` vanishes off `tsupport g ⊆ U`, so `∫_U div g = 0`.
  have hU0 : ∫ x in U, Poincare.SimonGMT.Chapter02.euclideanDivergence g x = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hzero]
    intro x hx
    by_contra h
    exact hx (hgU (Poincare.SimonGMT.Chapter02.support_euclideanDivergence_subset g h))
  -- Split `U = (U ∩ E) ⊔ (U ∖ E)` and use the Gauss–Green identity for `(U, E)`.
  have hsplit := integral_inter_add_sdiff₀ (s := U) hE hint.integrableOn
  rw [inter_comm, hGG g hg hgc hgU, hU0] at hsplit
  -- Negating the normal negates the right-hand side.
  have hneg : ∫ x, inner ℝ (g x) ((-ν) x) ∂μ = -∫ x, inner ℝ (g x) (ν x) ∂μ := by
    simp only [Pi.neg_apply, inner_neg_right, integral_neg]
  rw [inter_eq_left.2 sdiff_subset, hneg]
  linarith
/-- **Gauss–Green identity for the blow-ups `η_{x,r}(E)`** (Simon Ch. 3, proof of Theorem 4.3,
display (8), `chapter-03.txt` lines 662–667): for a Gauss–Green pair `(μ, ν)` of `(U, E)`, `r > 0`
and `g ∈ C¹_c(ℝ^{n+1}; ℝ^{n+1})` with `tsupport g ⊆ η_{x,r}(U)`,
`∫_{η_{x,r}(E)} div g dL^{n+1} = -r⁻ⁿ ∫ g(η_{x,r}(y)) · ν(y) dμ(y)`. Apply (4.1) to
`h = g ∘ η_{x,r}` (`C¹`, compactly supported in `U`, `div h = r⁻¹ (div g) ∘ η_{x,r}`) and change
variables `z = η_{x,r}(y)`: `η_{x,r}` pushes `L^{n+1}` forward to `r^{n+1} L^{n+1}`. -/
theorem Submission.deGiorgi_blowUp_gaussGreen_identity : ∀ (n : ℕ) (U E : Set (Rn (n + 1))) (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)) (x : Rn (n + 1)) (r : ℝ), IsOpen U → NullMeasurableSet E volume → IsGaussGreenPair U E μ ν → 0 < r → ∀ g : Rn (n + 1) → Rn (n + 1), ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ blowUpMap x r '' U → ∫ z in blowUpMap x r '' E, Poincare.SimonGMT.Chapter02.euclideanDivergence g z = -((r ^ n)⁻¹ * ∫ y, inner ℝ (g (blowUpMap x r y)) (ν y) ∂μ) := by
  intro n U E μ ν x r hU _ hGG hr g hg hgc hgU
  obtain ⟨-, -, -, -, hGG⟩ := hGG
  -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)`, as a homeomorphism and as a measurable equivalence.
  set φ : Rn (n + 1) ≃ₜ Rn (n + 1) :=
    (Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  set e : Rn (n + 1) ≃ᵐ Rn (n + 1) :=
    (MeasurableEquiv.subRight x).trans (MeasurableEquiv.smul₀ r⁻¹ (inv_ne_zero hr.ne'))
  have he : ⇑e = blowUpMap x r := rfl
  -- Step 1: `h = g ∘ η` is `C¹`, compactly supported, and `tsupport h ⊆ η⁻¹(η(U)) = U`.
  have hcd : ContDiff ℝ 1 (g ∘ blowUpMap x r) :=
    hg.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)
  have hcs : HasCompactSupport (g ∘ blowUpMap x r) := hgc.comp_homeomorph φ
  have hts : tsupport (g ∘ blowUpMap x r) ⊆ U := by
    refine (tsupport_comp_subset_preimage g φ.continuous).trans fun y hy ↦ ?_
    obtain ⟨u, hu, huy⟩ := hgU (show φ y ∈ tsupport g from hy)
    exact φ.injective huy ▸ hu
  -- Step 2: `D h(y) = r⁻¹ D g(η y)`, so `div h = r⁻¹ (div g) ∘ η`.
  have hη : ∀ y, HasFDerivAt (blowUpMap x r) (r⁻¹ • ContinuousLinearMap.id ℝ (Rn (n + 1))) y :=
    fun y ↦ ((hasFDerivAt_id y).sub_const x).const_smul r⁻¹
  have hdiv : ∀ y, Poincare.SimonGMT.Chapter02.euclideanDivergence (g ∘ blowUpMap x r) y =
      r⁻¹ * Poincare.SimonGMT.Chapter02.euclideanDivergence g (blowUpMap x r y) := by
    intro y
    have hd := ((hg.differentiable one_ne_zero) (blowUpMap x r y)).hasFDerivAt.comp y (hη y)
    rw [Poincare.SimonGMT.Chapter02.euclideanDivergence, hd.fderiv, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_id, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul]
    rfl
  -- Steps 3–4: (4.1) for `h`. As `div h` vanishes off `tsupport h ⊆ U`, `E ∩ U` may be replaced
  -- by `E` (Step 6, done here before the change of variables instead of after it).
  have hGG' : ∫ y in E ∩ U, Poincare.SimonGMT.Chapter02.euclideanDivergence (g ∘ blowUpMap x r) y =
      -∫ y, inner ℝ (g (blowUpMap x r y)) (ν y) ∂μ := hGG _ hcd hcs hts
  have hEU : ∫ y in E ∩ U, Poincare.SimonGMT.Chapter02.euclideanDivergence (g ∘ blowUpMap x r) y =
      ∫ y in E, Poincare.SimonGMT.Chapter02.euclideanDivergence (g ∘ blowUpMap x r) y := by
    rw [← setIntegral_indicator hU.measurableSet, Set.indicator_eq_self.2
      ((Poincare.SimonGMT.Chapter02.support_euclideanDivergence_subset _).trans hts)]
  -- Step 5: change of variables; `L^{n+1}(η⁻¹(T)) = L^{n+1}(r • T + x) = r^{n+1} L^{n+1}(T)`.
  have hmap : (volume : Measure (Rn (n + 1))).map e = ENNReal.ofReal (r ^ (n + 1)) • volume := by
    ext T -
    have hT : ⇑e ⁻¹' T = (fun y ↦ y + -x) ⁻¹' ((fun z ↦ r⁻¹ • z) ⁻¹' T) := by
      ext y
      simp [he, blowUpMap, sub_eq_add_neg]
    rw [e.map_apply, Measure.smul_apply, hT, measure_preimage_add_right,
      Set.preimage_smul_inv₀ hr.ne', Measure.addHaar_smul, finrank_euclideanSpace_fin,
      abs_of_pos (pow_pos hr _), smul_eq_mul]
  have hres : ((volume : Measure (Rn (n + 1))).restrict E).map e =
      ENNReal.ofReal (r ^ (n + 1)) • (volume : Measure (Rn (n + 1))).restrict (e '' E) := by
    rw [← Measure.restrict_smul, ← hmap, e.restrict_map, e.preimage_image]
  have hcov : ∫ y in E, Poincare.SimonGMT.Chapter02.euclideanDivergence g (blowUpMap x r y) =
      r ^ (n + 1) *
        ∫ z in blowUpMap x r '' E, Poincare.SimonGMT.Chapter02.euclideanDivergence g z := by
    rw [← he, ← integral_map_equiv, hres, integral_smul_measure,
      ENNReal.toReal_ofReal (pow_pos hr _).le, smul_eq_mul]
  -- Step 7: `rⁿ ∫_{η(E)} div g = -∫ g(η y) · ν(y) dμ(y)`; divide by `rⁿ > 0`.
  have hmain : r ^ n * ∫ z in blowUpMap x r '' E,
      Poincare.SimonGMT.Chapter02.euclideanDivergence g z =
        -∫ y, inner ℝ (g (blowUpMap x r y)) (ν y) ∂μ := by
    rw [← hGG', hEU]
    simp only [hdiv]
    rw [integral_const_mul, hcov, ← mul_assoc, pow_succ', ← mul_assoc, inv_mul_cancel₀ hr.ne',
      one_mul]
  rw [neg_mul_eq_mul_neg, ← hmain, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hr.ne'), one_mul]

/-- **Density estimates at the reduced boundary** (Simon Ch. 3, proof of Theorem 4.3, (1)–(6),
(10), (11), `chapter-03.txt` lines 607–652 and 689–733). Let `(μ, ν)` be a Gauss–Green pair for
`(U, E)`, `x ∈ ∂*E` and `e = ν_E(x)`. Then there are `ρ₁ > 0` with `B_{ρ₁}(x) ⊆ U` and constants
`C`, `c > 0` with `μ(B_ρ(x)) ≤ C ρⁿ`, `L^{n+1}(E ∩ B_ρ(x)) ≥ c ρ^{n+1}` and
`L^{n+1}(B_ρ(x) ∖ E) ≥ c ρ^{n+1}` for `0 < ρ < ρ₁`, and `ρ⁻ⁿ ∫_{B_ρ(x)} |ν - e| dμ → 0` as
`ρ ↓ 0`. The normal-average bounds give `|e| = 1` and `ρ₀ > 0` with `B_{ρ₀}(x) ⊆ U` and
`0 < μ(B_ρ(x)) ≤ 2 ∫_{B_ρ(x)} ν · e dμ` for `0 < ρ < ρ₀`; take `ρ₁ = ρ₀`. The upper mass bound
with `w = e` gives (6') with `C = 2 (n + 1) ω_{n+1}`, and the lower volume bound gives (10) with
`w = e`; for (11) it is applied to the pair `(μ, -ν)` of `(U, U ∖ E)` with `w = -e`, since
`(-ν) · (-e) = ν · e` and `(U ∖ E) ∩ B_ρ(x) = B_ρ(x) ∖ E`. The excess decay is the last clause of
the normal-average bounds, fed with (6'). -/
theorem Submission.deGiorgi_density_estimates : ∀ (n : ℕ) (U E : Set (Rn (n + 1))) (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)), IsOpen U → NullMeasurableSet E volume → IsGaussGreenPair U E μ ν → ∀ x ∈ reducedBoundary U μ ν, ∃ ρ₁ : ℝ, 0 < ρ₁ ∧ Metric.ball x ρ₁ ⊆ U ∧ ∃ C c : ℝ, 0 < c ∧ (∀ ρ ∈ Ioo 0 ρ₁, μ (Metric.ball x ρ) ≤ ENNReal.ofReal (C * ρ ^ n) ∧ ENNReal.ofReal (c * ρ ^ (n + 1)) ≤ volume (E ∩ Metric.ball x ρ) ∧ ENNReal.ofReal (c * ρ ^ (n + 1)) ≤ volume (Metric.ball x ρ \ E)) ∧ Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ y in Metric.ball x ρ, ‖ν y - reducedNormal μ ν x‖ ∂μ) (𝓝[>] 0) (𝓝 0) := by
  intro n U E μ ν hU hE hpair x hx
  -- Simon (1), (2): `|e| = 1` and `0 < μ(B_ρ(x)) ≤ 2 ∫_{B_ρ(x)} ν · e dμ` for `0 < ρ < ρ₀`.
  obtain ⟨he, ⟨ρ₀, hρ₀, hball, hhalf⟩, hexcess⟩ :=
    Submission.deGiorgiDens_normalAverage_bounds (n + 1) U μ ν hU hpair.2.1 hpair.2.2.1
      hpair.2.2.2.1 x hx
  -- (6'): `μ(B_ρ(x)) ≤ 2 (n + 1) ω_{n+1} ρⁿ`.
  have hmass := Submission.deGiorgiDens_ball_mass_le n U E μ ν hU hE hpair x
    (reducedNormal μ ν x) ρ₀ he.le hball fun ρ hρ ↦ (hhalf ρ hρ).2
  -- (10) for `E` with `w = e`, and (11) for the pair `(μ, -ν)` of `(U, U ∖ E)` with `w = -e`.
  obtain ⟨c, hc, hvol⟩ := Submission.deGiorgiDens_ball_volume_ge n
  have hlowE := hvol U E μ ν hU hE hpair x (reducedNormal μ ν x) ρ₀ he.le hball hhalf
  have hlowC := hvol U (U \ E) μ (-ν) hU (hU.measurableSet.nullMeasurableSet.diff hE)
    (Submission.deGiorgi_gaussGreenPair_compl (n + 1) U E μ ν hU hE hpair) x
    (-reducedNormal μ ν x) ρ₀ (by rw [norm_neg]; exact he.le) hball fun ρ hρ ↦ by
      simpa only [Pi.neg_apply, inner_neg_neg] using hhalf ρ hρ
  refine ⟨ρ₀, hρ₀, hball, 2 * (n + 1) * (volume (Metric.ball (0 : Rn (n + 1)) 1)).toReal, c, hc,
    fun ρ hρ ↦ ⟨hmass ρ hρ, hlowE ρ hρ, ?_⟩, hexcess n _ ρ₀ hρ₀ hmass⟩
  -- `(U ∖ E) ∩ B_ρ(x) = B_ρ(x) ∖ E`, as `B_ρ(x) ⊆ B_{ρ₀}(x) ⊆ U`.
  have hsub : Metric.ball x ρ ⊆ U := (Metric.ball_subset_ball hρ.2.le).trans hball
  rw [← inter_eq_right.2 hsub, ← sdiff_inter_right_comm]
  exact hlowC ρ hρ
/-- **The measure of a symmetric difference in a ball is the `L¹` distance of the indicators**
(used in the BV translation estimate for the compactness of sets of locally bounded perimeter,
Simon Ch. 2, Thm. 2.6). For `Lᴺ`-measurable `A, F ⊆ ℝᴺ` and the open ball `B = B_R(0)`,
`Lᴺ(B ∩ (A Δ F)) = ∫_B |1_A - 1_F| dLᴺ`: pointwise `|1_A - 1_F| = 1_{A Δ F}`, and
`∫_B 1_{A Δ F} dLᴺ = Lᴺ(A Δ F ∩ B)`, which is finite since `Lᴺ(B) < ∞`. -/
theorem Submission.indCompact_transEst_volume_symmDiff_eq_integral : ∀ (N : ℕ) (A F : Set (Rn N)) (R : ℝ), NullMeasurableSet A volume → NullMeasurableSet F volume → volume (Metric.ball (0 : Rn N) R ∩ symmDiff A F) = ENNReal.ofReal (∫ y in Metric.ball (0 : Rn N) R, |A.indicator (1 : Rn N → ℝ) y - F.indicator (1 : Rn N → ℝ) y|) := by
  intro N A F R hA hF
  -- Step 1: `|1_A - 1_F| = 1_{A Δ F}` pointwise.
  have h1 : ∀ y, |A.indicator (1 : Rn N → ℝ) y - F.indicator (1 : Rn N → ℝ) y| =
      (symmDiff A F).indicator (fun _ ↦ (1 : ℝ)) y := by
    intro y
    rw [← abs_indicator_symmDiff]
    by_cases hy : y ∈ symmDiff A F <;> simp [hy]
  simp_rw [h1]
  -- Step 2: `A Δ F` is null-measurable for `Lᴺ`, hence for `Lᴺ ⌞ B ≤ Lᴺ`.
  have hS : NullMeasurableSet (symmDiff A F) (volume.restrict (Metric.ball (0 : Rn N) R)) :=
    (hA.symmDiff hF).mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  -- Step 5: `Lᴺ(A Δ F ∩ B) ≤ Lᴺ(B) < ∞`.
  have hfin : volume (symmDiff A F ∩ Metric.ball (0 : Rn N) R) ≠ ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt measure_ball_lt_top).ne
  -- Steps 3, 4 and 6: `∫_B 1_{A Δ F} dLᴺ = (Lᴺ ⌞ B)(A Δ F) = Lᴺ(A Δ F ∩ B)`, `B` being open.
  rw [integral_indicator₀ hS, setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
    Measure.restrict_apply' measurableSet_ball, ENNReal.ofReal_toReal hfin, Set.inter_comm]
/-- **Translation change of variables for indicator differences** (Step 5(a) of the supplied
proof of the BV translation estimate used for the compactness of sets of bounded perimeter in
De Giorgi's theorem, Simon Ch. 3, Theorem 4.3). For `L^N`-measurable `F ⊆ ℝᴺ`, integrable `ψ`
and `h ∈ ℝᴺ`, `∫ (χ_F(y + h) - χ_F(y)) ψ(y) dy = ∫_F (ψ(z - h) - ψ(z)) dz`: pointwise the
integrand is `G(y + h) - H(y)` with `G = χ_F ψ(· - h)` and `H = χ_F ψ`, and Lebesgue measure is
translation invariant. -/
theorem Submission.indCompact_transEst_integral_indicator_shift_mul : ∀ (N : ℕ) (F : Set (Rn N)) (ψ : Rn N → ℝ) (h : Rn N), NullMeasurableSet F volume → Integrable ψ volume → ∫ y, (F.indicator (1 : Rn N → ℝ) (y + h) - F.indicator (1 : Rn N → ℝ) y) * ψ y = ∫ z in F, (ψ (z - h) - ψ z) := by
  intro N F ψ h hF hψ
  -- The translate `ψ_h = ψ (· - h)` is integrable.
  have hψh : Integrable (fun z ↦ ψ (z - h)) volume := hψ.comp_sub_right h
  -- `y ↦ G (y + h)` with `G = 1_F ψ_h`, and `H = 1_F ψ`, are integrable.
  have hG : Integrable (fun y ↦ F.indicator (fun z ↦ ψ (z - h)) (y + h)) volume :=
    (hψh.indicator₀ hF).comp_add_right h
  have hH : Integrable (F.indicator ψ) volume := hψ.indicator₀ hF
  -- Pointwise, `(1_F (y + h) - 1_F y) ψ y = G (y + h) - H y` (four cases).
  have hpt : ∀ y, (F.indicator (1 : Rn N → ℝ) (y + h) - F.indicator (1 : Rn N → ℝ) y) * ψ y =
      F.indicator (fun z ↦ ψ (z - h)) (y + h) - F.indicator ψ y := by
    intro y
    by_cases hy₁ : y + h ∈ F <;> by_cases hy₂ : y ∈ F <;> simp [hy₁, hy₂]
  -- Linearity, translation invariance, indicator integrals, linearity on `F`.
  calc ∫ y, (F.indicator (1 : Rn N → ℝ) (y + h) - F.indicator (1 : Rn N → ℝ) y) * ψ y
      = ∫ y, (F.indicator (fun z ↦ ψ (z - h)) (y + h) - F.indicator ψ y) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = (∫ y, F.indicator (fun z ↦ ψ (z - h)) (y + h)) - ∫ y, F.indicator ψ y :=
        integral_sub hG hH
    _ = (∫ z in F, ψ (z - h)) - ∫ z in F, ψ z := by
        rw [integral_add_right_eq_self (F.indicator fun z ↦ ψ (z - h)) h,
          integral_indicator₀ hF, integral_indicator₀ hF]
    _ = ∫ z in F, (ψ (z - h) - ψ z) :=
        (integral_sub hψh.integrableOn hψ.integrableOn).symm
/-- **Translation difference of a `C¹_c` function as a parametric integral of directional
derivatives** (steps 5(b) and 5(d) of the BV translation estimate behind the Compactness
Theorem 2.6 of Simon Ch. 2, `chapter-02.txt` lines 598–620, [GT01, Thm. 7.22], as used in the
proof of Ch. 3, Thm. 4.3, `chapter-03.txt` line 653). For an arbitrary `F ⊆ ℝᴺ`, `ψ ∈ C¹_c(ℝᴺ)`
and `h ∈ ℝᴺ`: `∫_F (ψ(z - h) - ψ(z)) dz = -∫₀¹ ∫_F Dψ(z - th)[h] dz dt`. For fixed `z`, the
fundamental theorem of calculus along `t ↦ ψ(z - th)` gives
`ψ(z - h) - ψ(z) = -∫₀¹ Dψ(z - th)[h] dt`. The integrand `f(z, t) = Dψ(z - th)[h]` is continuous
and, for `t ∈ [0, 1]`, vanishes unless `z` lies in the compact `K = tsupport ψ + [0, 1] h`; so it
is integrable on `ℝᴺ × [0, 1] ⊇ F × (0, 1]`, and Fubini for `Lᴺ ⌞ F ⊗ L¹ ⌞ (0, 1]` swaps the
integrals. -/
theorem Submission.indCompact_transEst_setIntegral_shift_sub_ftc : ∀ (N : ℕ) (F : Set (Rn N)) (ψ : Rn N → ℝ) (h : Rn N), ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∫ z in F, (ψ (z - h) - ψ z) = -∫ t in (0 : ℝ)..1, ∫ z in F, fderiv ℝ ψ (z - t • h) h := by
  intro N F ψ h hψ hψs
  -- Step 1: `ψ` is differentiable and `f(z, t) = Dψ(z - th)[h]` is continuous on `ℝᴺ × ℝ`.
  have hdiff : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  set f : Rn N → ℝ → ℝ := fun z t ↦ fderiv ℝ ψ (z - t • h) h
  have hfc : Continuous (Function.uncurry f) :=
    (hcont.comp (continuous_fst.sub (continuous_snd.smul continuous_const))).clm_apply
      continuous_const
  -- Step 2 (FTC along `t ↦ ψ(z - th)`, whose derivative is `-f(z, t)`):
  -- `ψ(z - h) - ψ(z) = -∫₀¹ f(z, t) dt`.
  have hftc : ∀ z, ψ (z - h) - ψ z = -∫ t in (0 : ℝ)..1, f z t := by
    intro z
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ ↦ ψ (z - t • h)) (-(f z t)) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ ↦ z - t • h) (-h) t := by
        simpa using ((hasDerivAt_id t).smul_const h).const_sub z
      have h2 : HasDerivAt (fun t : ℝ ↦ ψ (z - t • h)) (fderiv ℝ ψ (z - t • h) (-h)) t :=
        (hdiff (z - t • h)).hasFDerivAt.comp_hasDerivAt t h1
      simpa [f, map_neg] using h2
    have hint : IntervalIntegrable (fun t ↦ -(f z t)) volume 0 1 :=
      ((hfc.comp (continuous_const.prodMk continuous_id)).neg).intervalIntegrable 0 1
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simp only [one_smul, zero_smul, sub_zero, intervalIntegral.integral_neg] at this
    linarith
  -- Step 3: integrate over `F`, write `∫₀¹` as `∫_{(0, 1]}`, and reduce to Fubini for
  -- `Lᴺ ⌞ F ⊗ L¹ ⌞ (0, 1]`.
  rw [integral_congr_ae (Eventually.of_forall hftc), integral_neg]
  congr 1
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  apply integral_integral_swap
  -- Step 4: integrability. With `K = {x + s h : x ∈ tsupport ψ, s ∈ [0, 1]}` compact, `f` is
  -- integrable on `K × [0, 1]` and vanishes on `(ℝᴺ × [0, 1]) \ (K × [0, 1])`.
  set K : Set (Rn N) := (fun p : Rn N × ℝ ↦ p.1 + p.2 • h) '' (tsupport ψ ×ˢ Icc (0 : ℝ) 1)
  have hK : IsCompact K := (hψs.isCompact.prod isCompact_Icc).image (by fun_prop)
  rw [Measure.prod_restrict]
  have h1 : IntegrableOn (Function.uncurry f) (K ×ˢ Icc (0 : ℝ) 1) (volume.prod volume) :=
    hfc.continuousOn.integrableOn_compact (hK.prod isCompact_Icc)
  have h2 : IntegrableOn (Function.uncurry f) (univ ×ˢ Icc (0 : ℝ) 1) (volume.prod volume) := by
    refine h1.of_forall_sdiff_eq_zero (MeasurableSet.univ.prod measurableSet_Icc) ?_
    rintro ⟨z, t⟩ ⟨⟨-, ht⟩, hnot⟩
    simp only [Function.uncurry_apply_pair, f]
    by_contra hne
    apply hnot
    refine ⟨?_, ht⟩
    -- `Dψ = 0` off `tsupport ψ`, so `z - th ∈ tsupport ψ` and `z = (z - th) + th ∈ K`.
    have hmem : z - t • h ∈ tsupport ψ := by
      by_contra hns
      apply hne
      rw [fderiv_of_notMem_tsupport ℝ hns]
      simp
    exact ⟨(z - t • h, t), ⟨hmem, ht⟩, by simp⟩
  -- Step 5: `F × (0, 1] ⊆ ℝᴺ × [0, 1]`.
  exact h2.mono_set (prod_mono (subset_univ _) Ioc_subset_Icc_self)
/-- **Divergence-test bound for translated directional derivatives** (a step of the translation
estimate behind the compactness theorem, Simon Ch. 2, Thm. 2.6, used in Ch. 3, proof of
Thm. 4.3): if `∫_F div g ≤ C` for every `C¹` field `g` with compact support in `B_{R+1}(0)` and
`|g| ≤ 1`, then `|∫_F Dψ(z - a)[h] dz| ≤ C |h|` for every `C¹` function `ψ` with compact support
in `B_R(0)` and `|ψ| ≤ 1`, and all `a, h` with `|a| ≤ 1`. For `|c| = |h|⁻¹` the field
`G = c ψ(· - a) h` is admissible and `div G(z) = c Dψ(z - a)[h]` (the trace of a rank-one map),
so `c ∫_F Dψ(z - a)[h] dz ≤ C`; take `c = ±|h|⁻¹`. -/
theorem Submission.indCompact_transEst_abs_setIntegral_fderiv_le : ∀ (N : ℕ) (F : Set (Rn N))
    (R C : ℝ), (∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g →
      tsupport g ⊆ Metric.ball (0 : Rn N) (R + 1) → (∀ y, ‖g y‖ ≤ 1) →
      ∫ y in F, Poincare.SimonGMT.Chapter02.euclideanDivergence g y ≤ C) →
    ∀ ψ : Rn N → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball (0 : Rn N) R → (∀ y, |ψ y| ≤ 1) →
      ∀ a h : Rn N, ‖a‖ ≤ 1 → |∫ z in F, fderiv ℝ ψ (z - a) h| ≤ C * ‖h‖ := by
  intro N F R C hdiv ψ hψ hψs hψsub hψ1 a h ha
  -- Step 1. The case `h = 0` is trivial; otherwise `‖h‖ > 0`.
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  have hpos : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hdiff : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  set I := ∫ z in F, fderiv ℝ ψ (z - a) h with hI
  -- Step 2. `ψ(· - a)` has compact support, and `tsupport ψ(· - a) ⊆ B_{R+1}(0)`.
  have hTs : HasCompactSupport (fun y ↦ ψ (y - a)) := by
    simpa [Function.comp_def] using hψs.comp_homeomorph (Homeomorph.subRight a)
  have hTsub : tsupport (fun y ↦ ψ (y - a)) ⊆ Metric.ball 0 (R + 1) := by
    intro y hy
    have hy' : y - a ∈ tsupport ψ := by
      have := tsupport_comp_eq_preimage ψ (Homeomorph.subRight a)
      have hy2 : y ∈ tsupport (ψ ∘ (Homeomorph.subRight a)) := by
        simpa [Function.comp_def] using hy
      rw [this] at hy2
      simpa using hy2
    have h1 := hψsub hy'
    rw [mem_ball_zero_iff] at h1 ⊢
    calc ‖y‖ = ‖(y - a) + a‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - a‖ + ‖a‖ := norm_add_le _ _
      _ < R + 1 := by linarith
  -- Step 3. For `|c| = ‖h‖⁻¹`, testing the hypothesis with `G = c ψ(· - a) h` gives `c I ≤ C`.
  have key : ∀ c : ℝ, |c| = ‖h‖⁻¹ → c * I ≤ C := by
    intro c hc
    set G : Rn N → Rn N := fun y ↦ (c * ψ (y - a)) • h with hG
    have hGc : ContDiff ℝ 1 G :=
      (contDiff_const.mul (hψ.comp (contDiff_id.sub contDiff_const))).smul contDiff_const
    have hGsupp : tsupport G ⊆ tsupport (fun y ↦ ψ (y - a)) := by
      refine (tsupport_smul_subset_left _ _).trans ?_
      exact tsupport_mul_subset_right
    have hGcs : HasCompactSupport G :=
      hTs.of_isClosed_subset (isClosed_tsupport _) hGsupp
    have hGb : ∀ y, ‖G y‖ ≤ 1 := by
      intro y
      simp only [hG, norm_smul, Real.norm_eq_abs, abs_mul, hc]
      calc ‖h‖⁻¹ * |ψ (y - a)| * ‖h‖ = |ψ (y - a)| := by field_simp
        _ ≤ 1 := hψ1 _
    -- `div G(z) = trace (Dφ(z).smulRight h) = Dφ(z)[h] = c Dψ(z - a)[h]`, `φ = c ψ(· - a)`.
    have hdivG : ∀ z, Poincare.SimonGMT.Chapter02.euclideanDivergence G z
        = c * fderiv ℝ ψ (z - a) h := by
      intro z
      have hd : DifferentiableAt ℝ (fun y ↦ c * ψ (y - a)) z :=
        (differentiableAt_const _).mul ((hdiff _).comp z (differentiableAt_id.sub_const a))
      simp only [Poincare.SimonGMT.Chapter02.euclideanDivergence, hG]
      rw [fderiv_smul_const hd]
      have : ((fderiv ℝ (fun y ↦ c * ψ (y - a)) z).smulRight h : Rn N →L[ℝ] Rn N).toLinearMap
          = (fderiv ℝ (fun y ↦ c * ψ (y - a)) z).toLinearMap.smulRight h := by
        ext v; simp
      rw [this, LinearMap.trace_smulRight]
      have hd' : DifferentiableAt ℝ (fun y ↦ ψ (y - a)) z :=
        (hdiff (z - a)).comp z (differentiableAt_id.sub_const a)
      rw [ContinuousLinearMap.coe_coe, fderiv_const_mul hd' c, fderiv_comp_sub]
      simp
    have := hdiv G hGc hGcs (hGsupp.trans hTsub) hGb
    simpa [hdivG, integral_const_mul] using this
  -- Step 4. `c = ‖h‖⁻¹` gives `I ≤ C ‖h‖`, and `c = -‖h‖⁻¹` gives `-I ≤ C ‖h‖`.
  have k1 := key ‖h‖⁻¹ (abs_of_pos (inv_pos.mpr hpos))
  have k2 := key (-‖h‖⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.mpr hpos)])
  have e1 : I ≤ C * ‖h‖ := by
    have := mul_le_mul_of_nonneg_left k1 hpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this
    linarith
  have e2 : -I ≤ C * ‖h‖ := by
    have := mul_le_mul_of_nonneg_left k2 hpos.le
    rw [← mul_assoc, mul_neg, mul_inv_cancel₀ hpos.ne', neg_one_mul] at this
    linarith
  exact abs_le.mpr ⟨by linarith, e1⟩
/-- **A.e. approximation by admissible `C¹` test functions** (the mollification part of the
`L¹`-duality step of the proof of Simon Ch. 2, Thm. 2.6, used in Ch. 3, proof of Thm. 4.3): if `s`
is a.e.-strongly measurable, `|s| ≤ 1` and `s = 0` off `B_R(0)`, then `C¹` functions `ψⱼ` with
compact support, `tsupport ψⱼ ⊆ B_R(0)` and `|ψⱼ| ≤ 1` converge to `s` a.e. Here
`ψⱼ = ρⱼ ⋆ (1_{B_{R - 2δⱼ}(0)} s)`, `δⱼ = R / (4 (j + 1))`, `ρⱼ` the bump with radii
`δⱼ / 2 < δⱼ` normalized to integral `1`: `supp ψⱼ ⊆ B̄_{R - δⱼ}(0)`, `ψⱼ = ρⱼ ⋆ s` near each
point of `B_R(0)` for large `j`, and `ρⱼ ⋆ s → s` a.e. by Lebesgue differentiation. -/
theorem Submission.indCompact_l1Dual_exists_admissible_ae_tendsto : ∀ (N : ℕ) (R : ℝ)
    (s : Rn N → ℝ), 0 < R → AEStronglyMeasurable s volume → (∀ y, |s y| ≤ 1) →
    (∀ y, y ∉ Metric.ball (0 : Rn N) R → s y = 0) →
    ∃ ψ : ℕ → Rn N → ℝ, (∀ j, ContDiff ℝ 1 (ψ j)) ∧ (∀ j, HasCompactSupport (ψ j)) ∧
      (∀ j, tsupport (ψ j) ⊆ Metric.ball (0 : Rn N) R) ∧ (∀ j y, |ψ j y| ≤ 1) ∧
      ∀ᵐ y ∂(volume : Measure (Rn N)), Tendsto (fun j ↦ ψ j y) atTop (𝓝 (s y)) := by
  intro N R s hR hs_meas hs_le hs_zero
  -- Step 1. `|s| ≤ 1_{B_R(0)}` and `L^N(B_R(0)) < ∞`, so `s` is integrable.
  have hs_int : Integrable s volume := by
    refine Integrable.mono' (g := (Metric.ball (0 : Rn N) R).indicator fun _ ↦ (1 : ℝ))
      ((integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne))
      hs_meas (Eventually.of_forall fun y ↦ ?_)
    by_cases hy : y ∈ Metric.ball (0 : Rn N) R
    · simpa [indicator_of_mem hy, Real.norm_eq_abs] using hs_le y
    · simp [indicator_of_notMem hy, hs_zero y hy]
  -- Step 2. Radii `δⱼ = R / (4 (j + 1)) > 0` with `δⱼ → 0`.
  obtain ⟨δ, hδ_pos, hδ_lim⟩ : ∃ δ : ℕ → ℝ, (∀ j, 0 < δ j) ∧ Tendsto δ atTop (𝓝 0) :=
    ⟨fun j ↦ R / 4 * (1 / ((j : ℝ) + 1)), fun j ↦ by positivity,
      by simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (R / 4)⟩
  -- Step 3. Mollifiers `ρⱼ = φⱼ / ∫ φⱼ`, `φⱼ` the bump with `rIn = δⱼ / 2`, `rOut = δⱼ`.
  obtain ⟨ρ, hρ_cd, hρ_cs, hρ_nn, hρ_int, hρ_supp, hρ_le⟩ : ∃ ρ : ℕ → Rn N → ℝ,
      (∀ j, ContDiff ℝ 1 (ρ j)) ∧ (∀ j, HasCompactSupport (ρ j)) ∧ (∀ j y, 0 ≤ ρ j y) ∧
      (∀ j, ∫ y, ρ j y = 1) ∧ (∀ j, Function.support (ρ j) ⊆ Metric.ball 0 (δ j)) ∧
      ∀ j y, ρ j y ≤ 2 ^ finrank ℝ (Rn N) / volume.real (Metric.closedBall (0 : Rn N) (δ j)) := by
    let φ : ℕ → ContDiffBump (0 : Rn N) := fun j ↦
      ⟨δ j / 2, δ j, half_pos (hδ_pos j), half_lt_self (hδ_pos j)⟩
    have hφ_int : ∀ j, Integrable (φ j) volume := fun j ↦
      (φ j).continuous.integrable_of_hasCompactSupport (φ j).hasCompactSupport
    -- `φⱼ = 1` on `B̄_{δⱼ/2}(0)` and `φⱼ ≥ 0`, so `L^N(B̄_{δⱼ/2}(0)) ≤ ∫ φⱼ`.
    have hφ_ge : ∀ j, volume.real (Metric.closedBall (0 : Rn N) (δ j / 2)) ≤ ∫ y, φ j y := by
      intro j
      calc volume.real (Metric.closedBall (0 : Rn N) (δ j / 2))
          = ∫ y in Metric.closedBall (0 : Rn N) (δ j / 2), (1 : ℝ) := by simp
        _ = ∫ y in Metric.closedBall (0 : Rn N) (δ j / 2), φ j y :=
          setIntegral_congr_fun measurableSet_closedBall
            fun y hy ↦ ((φ j).one_of_mem_closedBall hy).symm
        _ ≤ ∫ y, φ j y :=
          setIntegral_le_integral (hφ_int j) (Eventually.of_forall fun y ↦ (φ j).nonneg)
    have hball : ∀ j, 0 < volume.real (Metric.closedBall (0 : Rn N) (δ j / 2)) := fun j ↦
      ENNReal.toReal_pos (Metric.measure_closedBall_pos _ _ (half_pos (hδ_pos j))).ne'
        measure_closedBall_lt_top.ne
    have hI : ∀ j, 0 < ∫ y, φ j y := fun j ↦ (hball j).trans_le (hφ_ge j)
    -- Scaling: `L^N(B̄_{δⱼ}(0)) = 2^N L^N(B̄_{δⱼ/2}(0))`.
    have hscale : ∀ j, volume.real (Metric.closedBall (0 : Rn N) (δ j)) =
        2 ^ finrank ℝ (Rn N) * volume.real (Metric.closedBall (0 : Rn N) (δ j / 2)) := by
      intro j
      have h := Measure.addHaar_closedBall_mul (volume : Measure (Rn N)) 0 zero_le_two
        (half_pos (hδ_pos j)).le
      rw [show (2 : ℝ) * (δ j / 2) = δ j by ring] at h
      rw [measureReal_def, measureReal_def, h, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity)]
    refine ⟨fun j y ↦ (∫ y, φ j y)⁻¹ * φ j y, fun j ↦ contDiff_const.mul (φ j).contDiff,
      fun j ↦ (φ j).hasCompactSupport.mul_left,
      fun j y ↦ mul_nonneg (inv_nonneg.2 (hI j).le) (φ j).nonneg, fun j ↦ ?_, fun j y hy ↦ ?_,
      fun j y ↦ ?_⟩
    · show ∫ y, (∫ y, φ j y)⁻¹ * φ j y = 1
      rw [integral_const_mul, inv_mul_cancel₀ (hI j).ne']
    · have hy' : φ j y ≠ 0 := right_ne_zero_of_mul hy
      rw [← Function.mem_support, (φ j).support_eq] at hy'
      exact hy'
    · show (∫ y, φ j y)⁻¹ * φ j y ≤ _
      calc (∫ y, φ j y)⁻¹ * φ j y ≤ (∫ y, φ j y)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (φ j).le_one (inv_nonneg.2 (hI j).le)
        _ ≤ (volume.real (Metric.closedBall (0 : Rn N) (δ j / 2)))⁻¹ := by
            rw [mul_one]; exact inv_anti₀ (hball j) (hφ_ge j)
        _ = 2 ^ finrank ℝ (Rn N) / volume.real (Metric.closedBall (0 : Rn N) (δ j)) := by
            rw [hscale j]; field_simp
  -- Step 4. Truncations `sⱼ = 1_{B_{R - 2δⱼ}(0)} s`.
  obtain ⟨sj, hsj_int, hsj_le, hsj_supp, hsj_eq⟩ : ∃ sj : ℕ → Rn N → ℝ,
      (∀ j, Integrable (sj j) volume) ∧ (∀ j y, |sj j y| ≤ 1) ∧
      (∀ j, Function.support (sj j) ⊆ Metric.ball 0 (R - 2 * δ j)) ∧
      ∀ j y, y ∈ Metric.ball (0 : Rn N) (R - 2 * δ j) → sj j y = s y := by
    refine ⟨fun j ↦ (Metric.ball (0 : Rn N) (R - 2 * δ j)).indicator s,
      fun j ↦ hs_int.indicator measurableSet_ball, fun j y ↦ ?_,
      fun j ↦ support_indicator_subset, fun j y hy ↦ indicator_of_mem hy s⟩
    show |(Metric.ball (0 : Rn N) (R - 2 * δ j)).indicator s y| ≤ 1
    by_cases hy : y ∈ Metric.ball (0 : Rn N) (R - 2 * δ j)
    · rw [indicator_of_mem hy]; exact hs_le y
    · rw [indicator_of_notMem hy, abs_zero]; exact zero_le_one
  -- Step 7. `supp (ρⱼ ⋆ sⱼ) ⊆ B_{δⱼ}(0) + B_{R - 2δⱼ}(0) ⊆ B̄_{R - δⱼ}(0) ⊆ B_R(0)`.
  have hψ_supp : ∀ j, Function.support (convolution (ρ j) (sj j)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆ Metric.closedBall 0 (R - δ j) := by
    intro j x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 (support_convolution_subset _ hx)
    have ha' := mem_ball_zero_iff.1 (hρ_supp j ha)
    have hb' := mem_ball_zero_iff.1 (hsj_supp j hb)
    rw [mem_closedBall_zero_iff]
    linarith [norm_add_le a b]
  have hψ_tsupp : ∀ j, tsupport (convolution (ρ j) (sj j)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆ Metric.closedBall 0 (R - δ j) :=
    fun j ↦ closure_minimal (hψ_supp j) Metric.isClosed_closedBall
  have hball_sub : ∀ j, Metric.closedBall (0 : Rn N) (R - δ j) ⊆ Metric.ball 0 R :=
    fun j ↦ Metric.closedBall_subset_ball (by linarith [hδ_pos j])
  -- Step 9. Lebesgue differentiation: `ρⱼ ⋆ s → s` almost everywhere.
  have hconv : ∀ᵐ x ∂(volume : Measure (Rn N)),
      Tendsto (fun j ↦ convolution (ρ j) s (ContinuousLinearMap.lsmul ℝ ℝ) volume x) atTop
        (𝓝 (s x)) := by
    have hδ' : Tendsto δ atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hδ_lim, Eventually.of_forall hδ_pos⟩
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume
      hs_int.locallyIntegrable 1] with x hx
    have hav := hx (fun _ ↦ x) δ hδ' (Eventually.of_forall fun j ↦
      Metric.mem_closedBall_self (by linarith [hδ_pos j]))
    simp only [convolution_eq_swap, ContinuousLinearMap.lsmul_apply]
    refine tendsto_integral_smul_of_tendsto_average_norm_sub
      (a := fun j ↦ Metric.closedBall x (δ j)) (g := fun j y ↦ ρ j (x - y))
      (2 ^ finrank ℝ (Rn N)) hav (Eventually.of_forall fun j ↦ hs_int.integrableOn)
      (tendsto_const_nhds.congr fun j ↦ ?_) (Eventually.of_forall fun j y hy ↦ ?_)
      (Eventually.of_forall fun j y ↦ ?_)
    · rw [integral_sub_left_eq_self (ρ j) volume x, hρ_int j]
    · rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
      exact (mem_ball_zero_iff.1 (hρ_supp j hy)).le
    · show |ρ j (x - y)| ≤ 2 ^ finrank ℝ (Rn N) / volume.real (Metric.closedBall x (δ j))
      rw [abs_of_nonneg (hρ_nn j _), Measure.addHaar_real_closedBall_center]
      exact hρ_le j (x - y)
  -- Steps 5 (`C¹`), 7 (support) and 11.
  refine ⟨fun j ↦ convolution (ρ j) (sj j) (ContinuousLinearMap.lsmul ℝ ℝ) volume,
    fun j ↦ (hρ_cs j).contDiff_convolution_left _ (hρ_cd j) (hsj_int j).locallyIntegrable,
    fun j ↦ HasCompactSupport.intro (isCompact_closedBall 0 (R - δ j))
      fun x hx ↦ Function.notMem_support.1 fun h ↦ hx (hψ_supp j h),
    fun j ↦ (hψ_tsupp j).trans (hball_sub j), fun j y ↦ ?_, ?_⟩
  · -- Step 6. `|ρⱼ ⋆ sⱼ| ≤ ∫ ρⱼ = 1`.
    have h := dist_convolution_le (μ := volume) (x₀ := y) (z₀ := (0 : ℝ)) zero_le_one
      (hρ_supp j) (hρ_nn j) (hρ_int j) (hsj_int j).aestronglyMeasurable
      fun x _ ↦ by rw [Real.dist_0_eq_abs]; exact hsj_le j x
    rwa [Real.dist_0_eq_abs] at h
  · -- Step 10. On `B_R(0)`, eventually `ψⱼ = ρⱼ ⋆ s` (step 8); off `B_R(0)`, `ψⱼ = 0 = s`.
    filter_upwards [hconv] with x hx
    by_cases hxB : x ∈ Metric.ball (0 : Rn N) R
    · have hx' := mem_ball_zero_iff.1 hxB
      have hη : 0 < (R - ‖x‖) / 3 := by linarith
      refine hx.congr' ?_
      filter_upwards [hδ_lim.eventually (gt_mem_nhds hη)] with j hj
      show convolution (ρ j) s _ volume x = convolution (ρ j) (sj j) _ volume x
      rw [convolution_def, convolution_def]
      refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
      show ContinuousLinearMap.lsmul ℝ ℝ (ρ j t) (s (x - t)) =
        ContinuousLinearMap.lsmul ℝ ℝ (ρ j t) (sj j (x - t))
      by_cases ht : ρ j t = 0
      · simp [ht]
      · have ht' := mem_ball_zero_iff.1 (hρ_supp j ht)
        rw [hsj_eq j (x - t) (mem_ball_zero_iff.2 (by linarith [norm_sub_le x t]))]
    · rw [hs_zero x hxB]
      refine tendsto_const_nhds.congr fun j ↦ ?_
      show 0 = convolution (ρ j) (sj j) _ volume x
      by_contra h
      exact hxB ((hψ_supp j).trans (hball_sub j) (Ne.symm h))
/-- **Dominated convergence for pairings with a function integrable on a ball**: the limit step of
the `L¹`-duality argument in the compactness theorem (Simon Ch. 2, Thm. 2.6) as used in the proof
of Ch. 3, Thm. 4.3. If `w` is integrable on `B = B_R(0)` and the a.e.-strongly measurable `ψ_j`
satisfy `|ψ_j| ≤ 1`, vanish off `B` and converge a.e. to `s`, then `∫ w ψ_j → ∫ w s`. Dominated
convergence with the integrable bound `1_B |w|`; `w ψ_j = 1_B (w ψ_j)` is a.e.-strongly measurable
because `w` is on `B`. No measurability of `s` is needed, and `R ≤ 0` (`B = ∅`) is not special. -/
theorem Submission.indCompact_l1Dual_tendsto_integral_mul : ∀ (N : ℕ) (w s : Rn N → ℝ) (R : ℝ)
    (ψ : ℕ → Rn N → ℝ), IntegrableOn w (Metric.ball (0 : Rn N) R) volume →
    (∀ j, AEStronglyMeasurable (ψ j) volume) → (∀ j y, |ψ j y| ≤ 1) →
    (∀ j y, y ∉ Metric.ball (0 : Rn N) R → ψ j y = 0) →
    (∀ᵐ y ∂(volume : Measure (Rn N)), Tendsto (fun j ↦ ψ j y) atTop (𝓝 (s y))) →
    Tendsto (fun j ↦ ∫ y, w y * ψ j y) atTop (𝓝 (∫ y, w y * s y)) := by
  intro N w s R ψ hw hψm hψ1 hψ0 hlim
  have hB : MeasurableSet (Metric.ball (0 : Rn N) R) := Metric.isOpen_ball.measurableSet
  -- Off the ball every `w ψ_j` vanishes, so `w ψ_j = 1_B (w ψ_j)`.
  have hind : ∀ j, (fun y ↦ w y * ψ j y) = (Metric.ball (0 : Rn N) R).indicator
      fun y ↦ w y * ψ j y := fun j ↦ funext fun y ↦ by
    by_cases hy : y ∈ Metric.ball (0 : Rn N) R
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy, hψ0 j y hy, mul_zero]
  refine tendsto_integral_of_dominated_convergence ((Metric.ball (0 : Rn N) R).indicator
      fun y ↦ ‖w y‖) (fun j ↦ ?_) ((integrable_indicator_iff hB).2 hw.norm)
      (fun j ↦ ae_of_all _ fun y ↦ ?_) ?_
  · -- Measurability: `w` is a.e.-strongly measurable on the ball.
    rw [hind j, aestronglyMeasurable_indicator_iff hB]
    exact hw.aestronglyMeasurable.mul (hψm j).restrict
  · -- Domination by `1_B |w|`.
    by_cases hy : y ∈ Metric.ball (0 : Rn N) R
    · rw [indicator_of_mem hy, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) ((Real.norm_eq_abs _).trans_le (hψ1 j y))
    · rw [indicator_of_notMem hy, hψ0 j y hy, mul_zero, norm_zero]
  · -- Pointwise a.e. convergence.
    filter_upwards [hlim] with y hy
    exact hy.const_mul (w y)

/-- **`L¹` norm on a ball by duality with `C¹` test functions** (the `L¹`-duality step of the
mollification proof of Simon Ch. 2, Thm. 2.6, used in Ch. 3, proof of Thm. 4.3): if `w` is
integrable on `B_R(0)` and `∫ w ψ ≤ M` for every `C¹` function `ψ` with compact support,
`tsupport ψ ⊆ B_R(0)` and `|ψ| ≤ 1`, then `∫_{B_R(0)} |w| ≤ M`. The test `ψ = 0` settles the
empty ball `R ≤ 0`. For `R > 0` the sign function `s = 1_{B_R(0)} sgn w` (here `sgn 0 = 1`)
satisfies `w s = 1_{B_R(0)} |w|`; admissible `ψⱼ → s` a.e.
(`indCompact_l1Dual_exists_admissible_ae_tendsto`) and dominated convergence
(`indCompact_l1Dual_tendsto_integral_mul`) give `M ≥ ∫ w ψⱼ → ∫_{B_R(0)} |w|`. -/
theorem Submission.indCompact_ball_integral_abs_le_of_test_bound : ∀ (N : ℕ) (w : Rn N → ℝ)
    (R M : ℝ), IntegrableOn w (Metric.ball (0 : Rn N) R) volume →
    (∀ ψ : Rn N → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball (0 : Rn N) R → (∀ y, |ψ y| ≤ 1) → ∫ y, w y * ψ y ≤ M) →
    ∫ y in Metric.ball (0 : Rn N) R, |w y| ≤ M := by
  intro N w R M hw hM
  rcases le_or_gt R 0 with hR | hR
  · -- Empty ball: the admissible test `ψ = 0` gives `0 ≤ M`.
    rw [Metric.ball_eq_empty.2 hR, setIntegral_empty]
    simpa using hM 0 contDiff_const HasCompactSupport.zero (by simp) (by simp)
  -- The sign function `s = 1_{B_R(0)} sgn w`: `|s| ≤ 1` and `s = 0` off the ball.
  obtain ⟨s, hs⟩ : ∃ s : Rn N → ℝ,
      s = (Metric.ball (0 : Rn N) R).indicator fun y ↦ if 0 ≤ w y then 1 else -1 := ⟨_, rfl⟩
  have hs_meas : AEStronglyMeasurable s volume := by
    rw [hs, aestronglyMeasurable_indicator_iff measurableSet_ball]
    exact ((Measurable.ite measurableSet_Ici measurable_const measurable_const).comp_aemeasurable
      hw.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hs_le : ∀ y, |s y| ≤ 1 := by
    intro y
    by_cases hy : y ∈ Metric.ball (0 : Rn N) R
    · rw [hs, indicator_of_mem hy]
      split_ifs <;> simp
    · simp [hs, indicator_of_notMem hy]
  have hs_zero : ∀ y, y ∉ Metric.ball (0 : Rn N) R → s y = 0 := fun y hy ↦ by
    rw [hs, indicator_of_notMem hy]
  -- `w s = 1_{B_R(0)} |w|`.
  have hws : ∫ y, w y * s y = ∫ y in Metric.ball (0 : Rn N) R, |w y| := by
    rw [← integral_indicator measurableSet_ball]
    congr 1
    funext y
    by_cases hy : y ∈ Metric.ball (0 : Rn N) R
    · rw [hs, indicator_of_mem hy, indicator_of_mem hy]
      split_ifs with h
      · rw [mul_one, abs_of_nonneg h]
      · rw [mul_neg_one, abs_of_neg (not_le.1 h)]
    · rw [hs, indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]
  -- Admissible `ψⱼ → s` a.e., and dominated convergence `∫ w ψⱼ → ∫ w s`.
  obtain ⟨ψ, hψ, hψc, hψt, hψb, hψs⟩ :=
    Submission.indCompact_l1Dual_exists_admissible_ae_tendsto N R s hR hs_meas hs_le hs_zero
  have hlim := Submission.indCompact_l1Dual_tendsto_integral_mul N w s R ψ hw
    (fun j ↦ (hψ j).continuous.aestronglyMeasurable) hψb
    (fun j y hy ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hy (hψt j h)) hψs
  rw [hws] at hlim
  exact le_of_tendsto' hlim fun j ↦ hM (ψ j) (hψ j) (hψc j) (hψt j) (hψb j)

/-- **Translation estimate for the indicator of a set with bounded perimeter in `B_{R+1}(0)`**
(the `L¹` translation bound behind the compactness theorem for sets of locally bounded perimeter,
Simon Ch. 2, Thm. 2.6, used in Ch. 3, proof of Thm. 4.3): if `∫_F div g ≤ C` for every `C¹`
field `g` with compact support in `B_{R+1}(0)` and `|g| ≤ 1`, then
`Lᴺ(B_R(0) ∩ (F_h Δ F)) ≤ C |h|` for `|h| ≤ 1`, where `F_h = {y : y + h ∈ F}`. With
`w = 1_F(· + h) - 1_F` we have `Lᴺ(B_R(0) ∩ (F_h Δ F)) = ∫_{B_R(0)} |w|`, and for every `C¹`
test function `ψ` with compact support in `B_R(0)` and `|ψ| ≤ 1`,
`∫ w ψ = ∫_F (ψ(z - h) - ψ(z)) dz = -∫_0^1 ∫_F Dψ(z - t h)[h] dz dt ≤ C |h|`, since each inner
integral is the integral over `F` of the divergence of the field `ψ(· - t h) h`. `L¹` duality on
`B_R(0)` concludes. -/
theorem Submission.indCompact_translation_estimate : ∀ (N : ℕ) (F : Set (Rn N)) (R C : ℝ), NullMeasurableSet F volume → (∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ Metric.ball (0 : Rn N) (R + 1) → (∀ y, ‖g y‖ ≤ 1) → ∫ y in F, Poincare.SimonGMT.Chapter02.euclideanDivergence g y ≤ C) → ∀ h : Rn N, ‖h‖ ≤ 1 → volume (Metric.ball (0 : Rn N) R ∩ symmDiff ((fun y ↦ y + h) ⁻¹' F) F) ≤ ENNReal.ofReal (C * ‖h‖) := by
  intro N F R C hF hdiv h hh
  -- `F_h = (· + h)⁻¹ F` is null-measurable, since `y ↦ y + h` preserves `Lᴺ`.
  have hA : NullMeasurableSet ((fun y ↦ y + h) ⁻¹' F) volume :=
    hF.preimage (measurePreserving_add_right volume h).quasiMeasurePreserving
  -- Step 4. `Lᴺ(B_R(0) ∩ (F_h Δ F)) = ofReal ∫_{B_R(0)} |w|` with `w = 1_F(· + h) - 1_F`,
  -- because `1_{F_h}(y) = 1_F(y + h)`. It remains to show `∫_{B_R(0)} |w| ≤ C |h|`.
  rw [Submission.indCompact_transEst_volume_symmDiff_eq_integral N _ F R hA hF]
  apply ENNReal.ofReal_le_ofReal
  have hw : ∀ y, ((fun y ↦ y + h) ⁻¹' F).indicator (1 : Rn N → ℝ) y
      = F.indicator (1 : Rn N → ℝ) (y + h) := fun y ↦ rfl
  simp only [hw]
  -- Step 6. `L¹` duality on `B_R(0)` with `M = C |h|`.
  apply Submission.indCompact_ball_integral_abs_le_of_test_bound N
    (fun y ↦ F.indicator (1 : Rn N → ℝ) (y + h) - F.indicator (1 : Rn N → ℝ) y) R (C * ‖h‖)
  · -- `w` is a.e.-strongly measurable with `|w| ≤ 1`, and `Lᴺ(B_R(0)) < ∞`.
    refine Measure.integrableOn_of_bounded (M := 1) measure_ball_lt_top.ne ?_ ?_
    · have h1 : AEStronglyMeasurable (fun y ↦ F.indicator (1 : Rn N → ℝ) (y + h)) volume :=
        (aestronglyMeasurable_const (b := (1 : ℝ))).indicator₀ hA
      have h2 : AEStronglyMeasurable (fun y ↦ F.indicator (1 : Rn N → ℝ) y) volume :=
        (aestronglyMeasurable_const (b := (1 : ℝ))).indicator₀ hF
      exact h1.sub h2
    · refine Eventually.of_forall fun y ↦ ?_
      by_cases h1 : y + h ∈ F <;> by_cases h2 : y ∈ F <;> simp [h1, h2]
  · -- Step 5. Fix a `C¹` test function `ψ` with compact support in `B_R(0)` and `|ψ| ≤ 1`.
    intro ψ hψ hψs hψsub hψ1
    -- (a) translation invariance and (b), (d) the fundamental theorem of calculus and Fubini:
    -- `∫ w ψ = ∫_F (ψ(z - h) - ψ(z)) dz = -∫_0^1 ∫_F Dψ(z - t h)[h] dz dt`.
    rw [Submission.indCompact_transEst_integral_indicator_shift_mul N F ψ h hF
        (hψ.continuous.integrable_of_hasCompactSupport hψs),
      Submission.indCompact_transEst_setIntegral_shift_sub_ftc N F ψ h hψ hψs]
    -- (c) for `t ∈ (0, 1]`, `‖t h‖ ≤ 1`, so `|∫_F Dψ(z - t h)[h] dz| ≤ C |h|`; (e) integrate.
    have hb : ‖∫ t in (0 : ℝ)..1, ∫ z in F, fderiv ℝ ψ (z - t • h) h‖ ≤ C * ‖h‖ * |1 - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Real.norm_eq_abs]
      apply Submission.indCompact_transEst_abs_setIntegral_fderiv_le N F R C hdiv ψ hψ hψs hψsub
        hψ1 (t • h) h
      rw [Set.uIoc_of_le zero_le_one] at ht
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      nlinarith [ht.2, norm_nonneg h]
    rw [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at hb
    linarith [neg_le_abs (∫ t in (0 : ℝ)..1, ∫ z in F, fderiv ℝ ψ (z - t • h) h)]
/-- **L¹ mollification error of an indicator** (Step 2 of the supplied proof that translation
estimates and uniformly Cauchy mollifications give local Cauchy in measure, part of the
compactness of indicators used for De Giorgi's theorem, Simon Ch. 3, Theorem 4.3; cf. the
mollification argument in the proof of Simon Ch. 2, Theorem 2.6). Let `F ⊆ ℝᴺ` be
`Lᴺ`-measurable and `ρ ≥ 0` continuous with `∫ ρ = 1` and support in `B̄_σ(0)`. If
`Lᴺ(B_R ∩ (F_h Δ F)) ≤ C|h|` for all `|h| ≤ σ`, where `F_h = {y : y + h ∈ F}` and `C ≥ 0`, then
`∫_{B_R} |∫_F ρ(y - z) dz - χ_F(y)| dy ≤ σ C`. -/
theorem Submission.indCompact_mollCauchy_l1_error : ∀ (N : ℕ) (F : Set (Rn N)) (ρ : Rn N → ℝ) (σ R C : ℝ), NullMeasurableSet F volume → Continuous ρ → HasCompactSupport ρ → (∀ y, 0 ≤ ρ y) → ∫ y, ρ y = 1 → Function.support ρ ⊆ Metric.closedBall (0 : Rn N) σ → 0 ≤ C → (∀ h : Rn N, ‖h‖ ≤ σ → volume (Metric.ball (0 : Rn N) R ∩ symmDiff ((fun y ↦ y + h) ⁻¹' F) F) ≤ ENNReal.ofReal (C * ‖h‖)) → ∫⁻ y in Metric.ball (0 : Rn N) R, ENNReal.ofReal |(∫ z in F, ρ (y - z)) - F.indicator (fun _ ↦ (1 : ℝ)) y| ≤ ENNReal.ofReal (σ * C) := by
  intro N F ρ σ R C hF hρc hρs hρ0 hρ1 hsupp hC htr
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have hρm : Measurable ρ := hρc.measurable
  -- Step 1: replace `F` by its measurable hull `F'`.
  set F' := toMeasurable volume F
  have hF'm : MeasurableSet F' := measurableSet_toMeasurable _ _
  have hae : F' =ᵐ[volume] F := hF.toMeasurable_ae_eq
  have hind : F'.indicator (fun _ ↦ (1 : ℝ)) =ᵐ[volume] F.indicator (fun _ ↦ (1 : ℝ)) :=
    indicator_ae_eq_of_ae_eq_set hae
  have htr' : ∀ h : Rn N, ‖h‖ ≤ σ → volume (Metric.ball (0 : Rn N) R ∩
      symmDiff ((fun y ↦ y + h) ⁻¹' F') F') ≤ ENNReal.ofReal (C * ‖h‖) := by
    intro h hh
    have hpre : (fun y ↦ y + h) ⁻¹' F' =ᵐ[volume] (fun y ↦ y + h) ⁻¹' F :=
      (measurePreserving_add_right volume h).quasiMeasurePreserving.preimage_ae_eq hae
    rw [measure_congr (ae_eq_set_inter (EventuallyEq.refl _ _) (ae_eq_set_symmDiff hpre hae))]
    exact htr h hh
  have hcongr : ∫⁻ y in Metric.ball (0 : Rn N) R,
      ENNReal.ofReal |(∫ z in F, ρ (y - z)) - F.indicator (fun _ ↦ (1 : ℝ)) y| =
      ∫⁻ y in Metric.ball (0 : Rn N) R,
        ENNReal.ofReal |(∫ z in F', ρ (y - z)) - F'.indicator (fun _ ↦ (1 : ℝ)) y| := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hind] with y hy
    rw [setIntegral_congr_set hae, hy]
  rw [hcongr]
  clear_value F'
  clear hcongr htr hind hae hF
  set χ : Rn N → ℝ := F'.indicator (fun _ ↦ (1 : ℝ)) with hχ
  set B := Metric.ball (0 : Rn N) R with hB
  have hχm : Measurable χ := measurable_const.indicator hF'm
  have hχb : ∀ x, |χ x| ≤ 1 := by
    intro x; by_cases hx : x ∈ F' <;> simp [hχ, hx]
  have hχd : ∀ x x', |χ x - χ x'| ≤ 1 := by
    intro x x'; by_cases hx : x ∈ F' <;> by_cases hx' : x' ∈ F' <;> simp [hχ, hx, hx']
  -- Step 3: pointwise bound.
  have hpt : ∀ y, ENNReal.ofReal |(∫ z in F', ρ (y - z)) - χ y| ≤
      ∫⁻ h, ENNReal.ofReal (ρ h) * ENNReal.ofReal |χ (y - h) - χ y| := by
    intro y
    have h1 : (∫ z in F', ρ (y - z)) = ∫ h, ρ h * χ (y - h) := by
      rw [← integral_indicator hF'm]
      have : (fun z ↦ F'.indicator (fun z ↦ ρ (y - z)) z) =
          fun z ↦ (fun h ↦ ρ h * χ (y - h)) (y - z) := by
        ext z
        by_cases hz : z ∈ F' <;> simp [hχ, hz]
      rw [this, integral_sub_left_eq_self (fun h ↦ ρ h * χ (y - h)) volume y]
    have hint1 : Integrable (fun h ↦ ρ h * χ (y - h)) := by
      refine hρi.mono' (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun h ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 h)]
      exact mul_le_of_le_one_right (hρ0 h) (hχb _)
    have h3 : (∫ z in F', ρ (y - z)) - χ y = ∫ h, ρ h * (χ (y - h) - χ y) := by
      have e : (fun h ↦ ρ h * (χ (y - h) - χ y)) = fun h ↦ ρ h * χ (y - h) - ρ h * χ y := by
        ext h; ring
      rw [e, integral_sub hint1 (hρi.mul_const _), integral_mul_const, hρ1, one_mul, h1]
    have hint3 : Integrable (fun h ↦ ρ h * |χ (y - h) - χ y|) := by
      refine hρi.mono' (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun h ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 h), abs_abs]
      exact mul_le_of_le_one_right (hρ0 h) (hχd _ _)
    rw [h3]
    calc ENNReal.ofReal |∫ h, ρ h * (χ (y - h) - χ y)|
        ≤ ENNReal.ofReal (∫ h, |ρ h * (χ (y - h) - χ y)|) :=
          ENNReal.ofReal_le_ofReal abs_integral_le_integral_abs
      _ = ENNReal.ofReal (∫ h, ρ h * |χ (y - h) - χ y|) := by
          congr 2; ext h; rw [abs_mul, abs_of_nonneg (hρ0 h)]
      _ = ∫⁻ h, ENNReal.ofReal (ρ h * |χ (y - h) - χ y|) :=
          ofReal_integral_eq_lintegral_ofReal hint3
            (ae_of_all _ fun h ↦ mul_nonneg (hρ0 h) (abs_nonneg _))
      _ = ∫⁻ h, ENNReal.ofReal (ρ h) * ENNReal.ofReal |χ (y - h) - χ y| := by
          congr 1; ext h; rw [ENNReal.ofReal_mul (hρ0 h)]
  -- Steps 4–6: Tonelli, inner integral, conclusion.
  calc ∫⁻ y in B, ENNReal.ofReal |(∫ z in F', ρ (y - z)) - χ y|
      ≤ ∫⁻ y in B, ∫⁻ h, ENNReal.ofReal (ρ h) * ENNReal.ofReal |χ (y - h) - χ y| :=
        lintegral_mono hpt
    _ = ∫⁻ h, ∫⁻ y in B, ENNReal.ofReal (ρ h) * ENNReal.ofReal |χ (y - h) - χ y| := by
        apply lintegral_lintegral_swap
        apply Measurable.aemeasurable
        fun_prop
    _ ≤ ∫⁻ h, ENNReal.ofReal (ρ h) * ENNReal.ofReal (σ * C) := by
        refine lintegral_mono fun h ↦ ?_
        dsimp only
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        by_cases hρh : ρ h = 0
        · simp [hρh]
        · gcongr
          have hnorm : ‖h‖ ≤ σ := by
            have := hsupp hρh
            simpa [Metric.mem_closedBall, dist_zero_right] using this
          have hmeas : MeasurableSet (symmDiff ((fun y ↦ y + -h) ⁻¹' F') F') :=
            (measurable_add_const (-h) hF'm).symmDiff hF'm
          have hset : ∀ y, ENNReal.ofReal |χ (y - h) - χ y| =
              (symmDiff ((fun y ↦ y + -h) ⁻¹' F') F').indicator 1 y := by
            intro y
            by_cases h1 : y - h ∈ F' <;> by_cases h2 : y ∈ F' <;>
              simp [hχ, h1, h2, Set.mem_symmDiff, ← sub_eq_add_neg]
          simp_rw [hset]
          rw [lintegral_indicator_one hmeas, Measure.restrict_apply hmeas, Set.inter_comm]
          calc volume (B ∩ symmDiff ((fun y ↦ y + -h) ⁻¹' F') F')
              ≤ ENNReal.ofReal (C * ‖-h‖) := htr' (-h) (by rwa [norm_neg])
            _ ≤ ENNReal.ofReal (σ * C) := by
              apply ENNReal.ofReal_le_ofReal
              rw [norm_neg, mul_comm]
              exact mul_le_mul_of_nonneg_right hnorm hC
    _ = (∫⁻ h, ENNReal.ofReal (ρ h)) * ENNReal.ofReal (σ * C) :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (σ * C) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hρi (ae_of_all _ hρ0), hρ1, ENNReal.ofReal_one,
          one_mul]
/-- **Continuity of the mollified set integral** (Step 1 of the supplied proof that translation
estimates and uniformly Cauchy mollifications give local Cauchy in measure, part of the
compactness of indicators used for De Giorgi's theorem, Simon Ch. 3, Theorem 4.3; cf. the
mollification argument in the proof of Simon Ch. 2, Theorem 2.6). For an arbitrary `F ⊆ ℝᴺ` and a
continuous, compactly supported `ρ`, the map `y ↦ ∫_F ρ(y - z) dz` is continuous: it is the
convolution of `1` with `ρ` for the locally finite measure `Lᴺ ⌞ F`. -/
theorem Submission.indCompact_mollCauchy_setIntegral_continuous : ∀ (N : ℕ) (F : Set (Rn N)) (ρ : Rn N → ℝ), Continuous ρ → HasCompactSupport ρ → Continuous (fun y : Rn N ↦ ∫ z in F, ρ (y - z)) := by
  intro N F ρ hρ hρc
  -- `y ↦ ∫_F ρ(y - z) dz` is the convolution of `1` with `ρ` for the measure `volume.restrict F`.
  have hconv : (fun y : Rn N ↦ ∫ z in F, ρ (y - z)) =
      convolution (fun _ ↦ (1 : ℝ)) ρ (ContinuousLinearMap.lsmul ℝ ℝ) (volume.restrict F) := by
    ext y
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, one_smul]
  rw [hconv]
  -- `volume.restrict F` is locally finite for every `F`, so the constant `1` is locally
  -- integrable; convolving with the continuous, compactly supported `ρ` gives a continuous map.
  exact hρc.continuous_convolution_right _ (locallyIntegrable_const 1) hρ

/-- **Translation estimates and uniformly Cauchy mollifications give local Cauchy in measure**
(Steps 3 and 6 of the supplied proof of the compactness of indicators used for De Giorgi's theorem,
Simon Ch. 3, Theorem 4.3; cf. the mollification argument in the proof of Simon Ch. 2,
Theorem 2.6). Let `ρ_m ≥ 0` be continuous kernels with `∫ ρ_m = 1` and support in
`B̄_{1/(m+1)}(0)`, and `v_{m,k}(y) = ∫_{F_k} ρ_m(y - z) dz`. If the `F_k` satisfy a uniform local
translation estimate `Lᴺ(B_R ∩ ((F_k)_h Δ F_k)) ≤ C_R |h|` and, for each `m`, the `v_{m,k}` are
uniformly Cauchy on `B̄_m(0)`, then `Lᴺ(B_R ∩ (F_k Δ F_l)) → 0`: on `B_R ⊆ B̄_m(0)`,
`1_{F_k Δ F_l} ≤ |v_{m,k} - 1_{F_k}| + |v_{m,k} - v_{m,l}| + |v_{m,l} - 1_{F_l}|`, and the outer
terms have `L¹(B_R)`-norm at most `C_R / (m + 1)`. -/
theorem Submission.indCompact_local_cauchy_of_mollified_cauchy : ∀ (N : ℕ) (F : ℕ → Set (Rn N)) (ρ : ℕ → Rn N → ℝ), (∀ k, NullMeasurableSet (F k) volume) → (∀ m, Continuous (ρ m)) → (∀ m, HasCompactSupport (ρ m)) → (∀ m y, 0 ≤ ρ m y) → (∀ m, ∫ y, ρ m y = 1) → (∀ m, Function.support (ρ m) ⊆ Metric.closedBall (0 : Rn N) (1 / ((m : ℝ) + 1))) → (∀ R : ℕ, ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ h : Rn N, ‖h‖ ≤ 1 → volume (Metric.ball (0 : Rn N) R ∩ symmDiff ((fun y ↦ y + h) ⁻¹' F k) (F k)) ≤ ENNReal.ofReal (C * ‖h‖)) → (∀ (m : ℕ) (ε : ℝ), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ l ≥ k₀, ∀ y ∈ Metric.closedBall (0 : Rn N) m, |(∫ z in F k, ρ m (y - z)) - ∫ z in F l, ρ m (y - z)| ≤ ε) → ∀ (R : ℕ) (ε : ℝ≥0∞), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ l ≥ k₀, volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) (F l)) ≤ ε := by
  intro N F ρ hF hρc hρs hρ0 hρ1 hρsupp htrans hcauchy R ε hε
  -- For `ε = ∞` any `k₀` works; otherwise put `e := ε.toReal > 0`, so that `ε = ofReal e`.
  rcases eq_or_ne ε ∞ with rfl | hε_top
  · exact ⟨0, fun _ _ _ _ ↦ le_top⟩
  set e := ε.toReal
  have he : 0 < e := ENNReal.toReal_pos hε.ne' hε_top
  have hεe : ε = ENNReal.ofReal e := (ENNReal.ofReal_toReal hε_top).symm
  -- (a) The translation estimate on `B_R`, with the nonnegative constant `C' := max C 0`.
  obtain ⟨C, k₁, hC⟩ := htrans R
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  -- (b) A kernel index `m ≥ R` with `σ_m C' ≤ e / 4`, where `σ_m := 1 / (m + 1) ≤ 1`.
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (4 * C' / e)
  set m := max m₀ R
  have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hσ_le : 1 / ((m : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hm_pos]
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hσC : 1 / ((m : ℝ) + 1) * C' ≤ e / 4 := by
    have hm₀m : (m₀ : ℝ) ≤ m := by exact_mod_cast le_max_left m₀ R
    have h4 : 4 * C' / e < (m : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ he] at h4
    rw [one_div_mul_eq_div, div_le_iff₀ hm_pos]
    linarith
  have hRm : Metric.ball (0 : Rn N) R ⊆ Metric.closedBall (0 : Rn N) m :=
    Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by exact_mod_cast le_max_right m₀ R))
  -- (c) The uniform Cauchy property of `v_{m,·}` on `B̄_m(0)` with `η := e / (2 (Lᴺ(B_R) + 1))`.
  set V := (volume (Metric.ball (0 : Rn N) R)).toReal with hV_def
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  set η := e / (2 * (V + 1)) with hη_def
  have hη : 0 < η := by positivity
  have hηV : η * V ≤ e / 2 := by
    rw [hη_def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨k₂, hk₂⟩ := hcauchy m η hη
  refine ⟨max k₁ k₂, fun k hk l hl ↦ ?_⟩
  -- Step 2 (mollification error): `∫⁻_{B_R} |v_{m,j} - 1_{F_j}| ≤ σ_m C' ≤ e / 4` for `j ≥ k₁`.
  have herr : ∀ j ≥ k₁, ∫⁻ y in Metric.ball (0 : Rn N) R,
      ENNReal.ofReal |(∫ z in F j, ρ m (y - z)) - (F j).indicator (fun _ ↦ (1 : ℝ)) y| ≤
        ENNReal.ofReal (e / 4) := by
    intro j hj
    refine (Submission.indCompact_mollCauchy_l1_error N (F j) (ρ m) (1 / ((m : ℝ) + 1)) R C'
      (hF j) (hρc m) (hρs m) (hρ0 m) (hρ1 m) (hρsupp m) hC' fun h hh ↦ ?_).trans
        (ENNReal.ofReal_le_ofReal hσC)
    exact (hC j hj h (hh.trans hσ_le)).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg h)))
  -- Step 1: each `v_{m,j}` is continuous and `F_j` is null-measurable, so the error terms are
  -- a.e.-measurable and `∫⁻` is additive on them.
  have hmeas : ∀ j, AEMeasurable (fun y ↦
      ENNReal.ofReal |(∫ z in F j, ρ m (y - z)) - (F j).indicator (fun _ ↦ (1 : ℝ)) y|)
      (volume.restrict (Metric.ball (0 : Rn N) R)) := by
    intro j
    have hv : AEMeasurable (fun y : Rn N ↦ ∫ z in F j, ρ m (y - z)) volume :=
      (Submission.indCompact_mollCauchy_setIntegral_continuous N (F j) (ρ m) (hρc m)
        (hρs m)).measurable.aemeasurable
    have hχ : AEMeasurable ((F j).indicator (fun _ ↦ (1 : ℝ))) volume :=
      aemeasurable_const.indicator₀ (hF j)
    exact (continuous_abs.measurable.comp_aemeasurable (hv.sub hχ)).ennreal_ofReal.restrict
  -- (d) For `y ∈ B_R ⊆ B̄_m(0)`:
  -- `1_{F_k Δ F_l}(y) ≤ |v_{m,k}(y) - 1_{F_k}(y)| + η + |v_{m,l}(y) - 1_{F_l}(y)|`.
  have hpt : ∀ y ∈ Metric.ball (0 : Rn N) R, (symmDiff (F k) (F l)).indicator 1 y ≤
      ENNReal.ofReal |(∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y| +
        ENNReal.ofReal η +
          ENNReal.ofReal |(∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y| := by
    intro y hy
    have hvkl := hk₂ k (le_of_max_le_right hk) l (le_of_max_le_right hl) y (hRm hy)
    refine Set.indicator_apply_le' (fun hyD ↦ ?_) (fun _ ↦ zero_le)
    have h1 : |(F k).indicator (fun _ ↦ (1 : ℝ)) y - (F l).indicator (fun _ ↦ (1 : ℝ)) y| = 1 := by
      rcases Set.mem_symmDiff.mp hyD with ⟨hk', hl'⟩ | ⟨hl', hk'⟩ <;> simp [hk', hl']
    have h2 : |(F k).indicator (fun _ ↦ (1 : ℝ)) y - (F l).indicator (fun _ ↦ (1 : ℝ)) y| ≤
        |(∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y| + η +
          |(∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y| := by
      rw [abs_le] at hvkl ⊢
      constructor <;>
        linarith [le_abs_self ((∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y),
          neg_abs_le ((∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y),
          le_abs_self ((∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y),
          neg_abs_le ((∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y)]
    rw [h1] at h2
    calc (1 : Rn N → ℝ≥0∞) y = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (|(∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y| + η +
            |(∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y|) :=
          ENNReal.ofReal_le_ofReal h2
      _ ≤ _ := ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
  -- (e) Integrate over `B_R`: `Lᴺ(B_R ∩ (F_k Δ F_l)) ≤ e / 4 + η Lᴺ(B_R) + e / 4 ≤ e`.
  have hconst : ∫⁻ _ in Metric.ball (0 : Rn N) R, ENNReal.ofReal η ≤ ENNReal.ofReal (e / 2) := by
    rw [setLIntegral_const, ← ENNReal.ofReal_toReal (measure_ball_lt_top (μ := volume)).ne,
      ← hV_def, ← ENNReal.ofReal_mul hη.le]
    exact ENNReal.ofReal_le_ofReal hηV
  calc volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) (F l))
      = ∫⁻ y in Metric.ball (0 : Rn N) R, (symmDiff (F k) (F l)).indicator 1 y := by
        rw [lintegral_indicator_one₀
            (((hF k).symmDiff (hF l)).mono_ac Measure.absolutelyContinuous_restrict),
          Measure.restrict_apply' measurableSet_ball, Set.inter_comm]
    _ ≤ ∫⁻ y in Metric.ball (0 : Rn N) R,
          (ENNReal.ofReal |(∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y| +
            ENNReal.ofReal η +
              ENNReal.ofReal |(∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y|) :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = (∫⁻ y in Metric.ball (0 : Rn N) R,
          ENNReal.ofReal |(∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y|) +
        (∫⁻ _ in Metric.ball (0 : Rn N) R, ENNReal.ofReal η) +
          ∫⁻ y in Metric.ball (0 : Rn N) R,
            ENNReal.ofReal |(∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y| := by
        rw [lintegral_add_right' _ (hmeas l), lintegral_add_right' _ aemeasurable_const]
    _ ≤ ENNReal.ofReal (e / 4) + ENNReal.ofReal (e / 2) + ENNReal.ofReal (e / 4) :=
        add_le_add (add_le_add (herr k (le_of_max_le_left hk)) hconst)
          (herr l (le_of_max_le_left hl))
    _ = ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), hεe]
        congr 1
        ring
/-- **Diagonal Arzelà–Ascoli extraction for mollified sets** (Steps 4–5 of the mollification
proof of Simon Ch. 2, Thm. 2.6, with arbitrary continuous compactly supported kernels `ρₘ`): for
arbitrary sets `Fₖ ⊆ ℝᴺ` some subsequence `φ` makes every `y ↦ ∫_{F_{φ(k)}} ρₘ(y - z) dz`
uniformly Cauchy on `B̄ₘ(0)`. Only `Lᴺ ⌞ S ≤ Lᴺ` is used, so these functions are bounded by
`Mₘ Lᴺ(B̄_{Rₘ}(0))` and equicontinuous uniformly in `S`. Tychonoff in the countable product
`∏_{(m, d) ∈ ℕ × D}` (`D` countable dense) gives `φ` with convergence at every `(m, d)`;
equicontinuity and a finite cover of `B̄ₘ(0)` by balls centred in `D` upgrade this to the uniform
Cauchy property. -/
theorem Submission.indCompact_diagonal_mollified_uniform_cauchy : ∀ (N : ℕ) (ρ : ℕ → Rn N → ℝ)
    (F : ℕ → Set (Rn N)), (∀ m, Continuous (ρ m)) → (∀ m, HasCompactSupport (ρ m)) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ (m : ℕ) (ε : ℝ), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ l ≥ k₀,
      ∀ y ∈ Metric.closedBall (0 : Rn N) m,
        |(∫ z in F (φ k), ρ m (y - z)) - ∫ z in F (φ l), ρ m (y - z)| ≤ ε := by
  intro N ρ F hc hs
  -- A function bounded by `C` and vanishing off `B̄_r(c)` has `|∫_S f| ≤ C Lᴺ(B̄_r(0))` for every
  -- set `S`, since `Lᴺ ⌞ S ≤ Lᴺ`.
  have key : ∀ (S : Set (Rn N)) (c : Rn N) (r C : ℝ) (f : Rn N → ℝ), (∀ z, ‖f z‖ ≤ C) →
      (∀ z, f z ≠ 0 → z ∈ Metric.closedBall c r) →
      |∫ z in S, f z| ≤ C * (volume (Metric.closedBall (0 : Rn N) r)).toReal := by
    intro S c r C f hfC hfs
    have hC : 0 ≤ C := (norm_nonneg _).trans (hfC 0)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (f := f) (s := Metric.closedBall c r)
      (μ := volume.restrict S) (fun z hz => not_not.1 (mt (hfs z) hz)), ← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le_const
      ((Measure.restrict_apply_le _ _).trans_lt measure_closedBall_lt_top)
      (fun z _ => hfC z)).trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [Measure.real, ← Measure.addHaar_closedBall_center volume c r]
    exact ENNReal.toReal_mono measure_closedBall_lt_top.ne (Measure.restrict_apply_le _ _)
  -- Support radius `Rₘ` and sup bound `Mₘ` of each kernel.
  have hR : ∀ m, ∃ R : ℝ, ∀ x, ρ m x ≠ 0 → ‖x‖ ≤ R := by
    intro m
    obtain ⟨R, hR⟩ := (hs m).isCompact.isBounded.subset_closedBall 0
    exact ⟨R, fun x hx => by simpa using hR (subset_tsupport _ hx)⟩
  choose R hR using hR
  choose M hM using fun m => (hc m).bounded_above_of_compact_support (hs m)
  -- Uniform bound: `|∫_S ρₘ(y - z) dz| ≤ Mₘ Lᴺ(B̄_{Rₘ}(0))`.
  have hbd : ∀ (m : ℕ) (S : Set (Rn N)) (y : Rn N),
      |∫ z in S, ρ m (y - z)| ≤ M m * (volume (Metric.closedBall (0 : Rn N) (R m))).toReal := by
    intro m S y
    refine key S y (R m) (M m) (fun z => ρ m (y - z)) (fun z => hM m _) (fun z hz => ?_)
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
    exact hR m _ hz
  have hint : ∀ (m : ℕ) (y : Rn N) (S : Set (Rn N)),
      Integrable (fun z => ρ m (y - z)) (volume.restrict S) := fun m y S =>
    (((hc m).integrable_of_hasCompactSupport (hs m)).comp_sub_left y).restrict
  -- Equicontinuity, uniformly in the set `S`.
  have heq : ∀ (m : ℕ) (η : ℝ), 0 < η → ∃ δ > 0, ∀ (S : Set (Rn N)) (y y' : Rn N), dist y y' < δ →
      |(∫ z in S, ρ m (y - z)) - ∫ z in S, ρ m (y' - z)| ≤ η := by
    intro m η hη
    obtain ⟨V, hV0, hV⟩ : ∃ V, 0 ≤ V ∧
        (volume (Metric.closedBall (0 : Rn N) (R m + 1))).toReal = V :=
      ⟨_, ENNReal.toReal_nonneg, rfl⟩
    have hV1 : 0 < V + 1 := by linarith
    obtain ⟨δ, hδ, hδρ⟩ := Metric.uniformContinuous_iff.1
      ((hs m).uniformContinuous_of_continuous (hc m)) (η / (V + 1)) (div_pos hη hV1)
    refine ⟨min δ 1, lt_min hδ one_pos, fun S y y' hyy' => ?_⟩
    rw [← integral_sub (hint m y S) (hint m y' S)]
    refine (key S y (R m + 1) (η / (V + 1)) (fun z => ρ m (y - z) - ρ m (y' - z)) (fun z => ?_)
      (fun z hz => ?_)).trans ?_
    · show ‖ρ m (y - z) - ρ m (y' - z)‖ ≤ _
      rw [← dist_eq_norm]
      have hd : dist (y - z) (y' - z) < δ := by
        rw [dist_sub_right]; exact hyy'.trans_le (min_le_left _ _)
      exact (hδρ hd).le
    · have hz' : ρ m (y - z) - ρ m (y' - z) ≠ 0 := hz
      rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
      by_cases h : ρ m (y - z) = 0
      · have h' : ρ m (y' - z) ≠ 0 := fun h' => hz' (by rw [h, h', sub_self])
        have h'' := hR m _ h'
        have hyy1 : ‖y - y'‖ < 1 := by
          rw [← dist_eq_norm]; exact hyy'.trans_le (min_le_right _ _)
        calc ‖y - z‖ = ‖(y - y') + (y' - z)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖y - y'‖ + ‖y' - z‖ := norm_add_le _ _
          _ ≤ R m + 1 := by linarith
      · linarith [hR m _ h]
    · rw [hV]
      calc η / (V + 1) * V ≤ η / (V + 1) * (V + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (div_pos hη hV1).le
        _ = η := div_mul_cancel₀ _ hV1.ne'
  -- Tychonoff on the countable product indexed by `ℕ × D`, `D` countable dense.
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Rn N)
  have : Countable D := hDc.to_subtype
  have hK : IsCompact (Set.pi univ fun p : ℕ × D =>
      Icc (-(M p.1 * (volume (Metric.closedBall (0 : Rn N) (R p.1))).toReal))
        (M p.1 * (volume (Metric.closedBall (0 : Rn N) (R p.1))).toReal)) :=
    isCompact_univ_pi fun p => isCompact_Icc
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq
    (x := fun k (p : ℕ × D) => ∫ z in F k, ρ p.1 ((p.2 : Rn N) - z))
    fun k => Set.mem_univ_pi.2 fun p => abs_le.1 (hbd p.1 (F k) p.2)
  refine ⟨φ, hφ, fun m ε hε => ?_⟩
  obtain ⟨δ, hδ, hδV⟩ := heq m (ε / 3) (by positivity)
  -- Finitely many `δ`-balls centred in `D` cover `B̄ₘ(0)`.
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : Rn N) (m : ℝ)).elim_finite_subcover
    (fun d : D => Metric.ball (d : Rn N) δ) (fun _ => Metric.isOpen_ball) fun y _ => by
      obtain ⟨d, hd, hyd⟩ := hDd.exists_dist_lt y hδ
      exact mem_iUnion.2 ⟨⟨d, hd⟩, hyd⟩
  have hev : ∀ᶠ k in atTop, ∀ d ∈ t,
      dist (∫ z in F (φ k), ρ m ((d : Rn N) - z)) (a (m, d)) < ε / 6 :=
    (eventually_all_finset t).2 fun d _ =>
      Metric.tendsto_nhds.1 (tendsto_pi_nhds.1 hlim (m, d)) (ε / 6) (by positivity)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hev
  refine ⟨k₀, fun k hk l hl y hy => ?_⟩
  obtain ⟨d, hdt, hyd⟩ := mem_iUnion₂.1 (ht hy)
  have h1 := hδV (F (φ k)) y d hyd
  have h2 := hδV (F (φ l)) y d hyd
  have h3 := hk₀ k hk d hdt
  have h4 := hk₀ l hl d hdt
  rw [Real.dist_eq] at h3 h4
  rw [abs_le] at h1 h2 ⊢
  rw [abs_lt] at h3 h4
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
/-- **Local `L¹` Cauchy sequences of sets have a local limit**: the completeness step of the
compactness theorem (Simon Ch. 2, Thm. 2.6) for characteristic functions, as used in the proof of
Ch. 3, Thm. 4.3. If for every `R ∈ ℕ` the sets `F k` are Cauchy in measure on `B_R(0)`, i.e.
`|B_R(0) ∩ (F_k Δ F_l)| → 0` as `k, l → ∞`, then some measurable `G` has `|K ∩ (F_k Δ G)| → 0`
for every compact `K`. Riesz–Fischer argument: choose `n_j ≥ k₀(j)` monotone, where
`|B_j ∩ (F_k Δ F_l)| ≤ 2⁻ʲ` for `k, l ≥ k₀(j)`, and put `G₀ = ⋃ᵢ ⋂_{j ≥ i} F_{n_j}`. Then
`F_{n_i} Δ G₀ ⊆ ⋃_{j ≥ i} (F_{n_j} Δ F_{n_{j+1}})`, so `|B_R ∩ (F_{n_i} Δ G₀)| ≤ 2 · 2⁻ⁱ` for
`i ≥ R`, and by the triangle inequality for `Δ`, `|B_R ∩ (F_k Δ G₀)| ≤ 3 · 2⁻ⁱ` for `k ≥ n_i`.
These estimates only use outer measure; `G` is a measurable hull of the null-measurable set `G₀`,
and every compact `K` lies in some `B_R`. -/
theorem Submission.indCompact_limit_of_local_cauchy : ∀ (N : ℕ) (F : ℕ → Set (Rn N)),
    (∀ k, NullMeasurableSet (F k) volume) →
    (∀ (R : ℕ) (ε : ℝ≥0∞), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ l ≥ k₀,
      volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) (F l)) ≤ ε) →
    ∃ G : Set (Rn N), MeasurableSet G ∧ ∀ K : Set (Rn N), IsCompact K →
      Tendsto (fun k ↦ volume (K ∩ symmDiff (F k) G)) atTop (𝓝 0) := by
  intro N F hF hC
  -- Fast subsequence: `k₀ j` is a Cauchy index for `R = j`, `ε = 2⁻ʲ`; `n` is monotone, `n ≥ k₀`.
  choose k₀ hk₀ using fun j : ℕ ↦ hC j ((2 : ℝ≥0∞)⁻¹ ^ j) (ENNReal.pow_pos (by simp) j)
  obtain ⟨n, hn_ge, hn_mono⟩ : ∃ n : ℕ → ℕ, (∀ j, k₀ j ≤ n j) ∧ Monotone n :=
    ⟨fun j ↦ (Finset.range (j + 1)).sup k₀, fun j ↦ Finset.le_sup (Finset.self_mem_range_succ j),
      fun i j hij ↦ Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ hij))⟩
  have hstep : ∀ j : ℕ, volume (Metric.ball (0 : Rn N) j ∩ symmDiff (F (n j)) (F (n (j + 1)))) ≤
      (2 : ℝ≥0∞)⁻¹ ^ j := fun j ↦
    hk₀ j _ (hn_ge j) _ ((hn_ge j).trans (hn_mono (Nat.le_succ j)))
  -- The limit set `G₀ = ⋃ᵢ ⋂_{j ≥ i} F (n j)`.
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : Set (Rn N), G₀ = ⋃ i, ⋂ j ≥ i, F (n j) := ⟨_, rfl⟩
  have hmem : ∀ y, y ∈ G₀ ↔ ∃ i, ∀ j ≥ i, y ∈ F (n j) := fun y ↦ by
    simp only [hG₀, mem_iUnion, mem_iInter]
  -- Tail inclusion: `F (n i) Δ G₀ ⊆ ⋃_{j ≥ i} (F (n j) Δ F (n (j + 1)))`.
  have htail : ∀ i, symmDiff (F (n i)) G₀ ⊆
      ⋃ m : ℕ, symmDiff (F (n (i + m))) (F (n (i + m + 1))) := by
    intro i y hy
    by_contra hcon
    simp only [mem_iUnion, not_exists] at hcon
    have hiff : ∀ m, (y ∈ F (n (i + m)) ↔ y ∈ F (n i)) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have h := hcon m
        rw [mem_symmDiff] at h
        rw [← ih, ← add_assoc]
        tauto
    rw [mem_symmDiff, hmem] at hy
    rcases hy with ⟨hyA, hyG⟩ | ⟨⟨i', hi'⟩, hyA⟩
    · refine hyG ⟨i, fun j hj ↦ ?_⟩
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
      exact (hiff m).2 hyA
    · exact hyA ((hiff i').1 (hi' (i + i') (Nat.le_add_left i' i)))
  -- Along the subsequence: `|B_R ∩ (F (n i) Δ G₀)| ≤ 2⁻ⁱ · 2` for `R ≤ i`.
  have hsub : ∀ R i : ℕ, R ≤ i →
      volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F (n i)) G₀) ≤ (2 : ℝ≥0∞)⁻¹ ^ i * 2 := by
    intro R i hRi
    calc volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F (n i)) G₀)
        ≤ volume (⋃ m : ℕ, Metric.ball (0 : Rn N) ↑(i + m) ∩
            symmDiff (F (n (i + m))) (F (n (i + m + 1)))) := by
          refine measure_mono fun y hy ↦ ?_
          obtain ⟨m, hm⟩ := mem_iUnion.1 (htail i hy.2)
          refine mem_iUnion.2 ⟨m, Metric.ball_subset_ball ?_ hy.1, hm⟩
          exact_mod_cast hRi.trans (Nat.le_add_right i m)
      _ ≤ ∑' m : ℕ, volume (Metric.ball (0 : Rn N) ↑(i + m) ∩
            symmDiff (F (n (i + m))) (F (n (i + m + 1)))) := measure_iUnion_le _
      _ ≤ ∑' m : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (i + m) := ENNReal.tsum_le_tsum fun m ↦ hstep (i + m)
      _ = (2 : ℝ≥0∞)⁻¹ ^ i * 2 := by
          simp_rw [pow_add]
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  -- Whole sequence: `|B_R ∩ (F k Δ G₀)| ≤ 2⁻ⁱ + 2⁻ⁱ · 2` for `R ≤ i` and `k ≥ n i`.
  have hwhole : ∀ R i k : ℕ, R ≤ i → n i ≤ k →
      volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) G₀) ≤
        (2 : ℝ≥0∞)⁻¹ ^ i + (2 : ℝ≥0∞)⁻¹ ^ i * 2 := by
    intro R i k hRi hk
    calc volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) G₀)
        ≤ volume ((Metric.ball (0 : Rn N) i ∩ symmDiff (F k) (F (n i))) ∪
            (Metric.ball (0 : Rn N) R ∩ symmDiff (F (n i)) G₀)) := by
          refine measure_mono fun y hy ↦ ?_
          rcases symmDiff_triangle (F k) (F (n i)) G₀ hy.2 with h | h
          · exact Or.inl ⟨Metric.ball_subset_ball (by exact_mod_cast hRi) hy.1, h⟩
          · exact Or.inr ⟨hy.1, h⟩
      _ ≤ volume (Metric.ball (0 : Rn N) i ∩ symmDiff (F k) (F (n i))) +
            volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F (n i)) G₀) := measure_union_le _ _
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ i + (2 : ℝ≥0∞)⁻¹ ^ i * 2 :=
          add_le_add (hk₀ i k ((hn_ge i).trans hk) (n i) (hn_ge i)) (hsub R i hRi)
  -- Hence `|B_R ∩ (F k Δ G₀)| → 0` for every `R ∈ ℕ`.
  have hgeom : Tendsto (fun i : ℕ ↦ (2 : ℝ≥0∞)⁻¹ ^ i + (2 : ℝ≥0∞)⁻¹ ^ i * 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun i : ℕ ↦ (2 : ℝ≥0∞)⁻¹ ^ i) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
    have h2 := h1.add (ENNReal.Tendsto.mul_const h1 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞)))
    rwa [zero_mul, add_zero] at h2
  have hball : ∀ R : ℕ,
      Tendsto (fun k ↦ volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) G₀)) atTop (𝓝 0) := by
    intro R
    refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
    obtain ⟨i, hiR, hiε⟩ :=
      ((eventually_ge_atTop R).and (ENNReal.tendsto_nhds_zero.1 hgeom ε hε)).exists
    exact (eventually_ge_atTop (n i)).mono fun k hk ↦ (hwhole R i k hiR hk).trans hiε
  -- `G = toMeasurable G₀` is measurable and a.e. equal to the null-measurable `G₀`; every compact
  -- `K` lies in some `B_R`.
  have hG₀m : NullMeasurableSet G₀ volume := by
    rw [hG₀]
    exact .iUnion fun i ↦ .iInter fun j ↦ .iInter fun _ ↦ hF (n j)
  refine ⟨toMeasurable volume G₀, measurableSet_toMeasurable _ _, fun K hK ↦ ?_⟩
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Rn N)
  obtain ⟨R, hR⟩ := exists_nat_gt r
  have hKR : K ⊆ Metric.ball (0 : Rn N) R := hr.trans (Metric.ball_subset_ball hR.le)
  have heq : ∀ k, volume (K ∩ symmDiff (F k) (toMeasurable volume G₀)) =
      volume (K ∩ symmDiff (F k) G₀) := fun k ↦
    measure_congr (EventuallyEqSet.rfl.inter (EventuallyEqSet.rfl.symmDiff hG₀m.toMeasurable_ae_eq))
  refine (tendsto_congr heq).2 ?_
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hball R)
    (fun k ↦ zero_le) (fun k ↦ measure_mono (inter_subset_inter_left _ hKR))

/-- **Density estimates at the reduced boundary** (Simon Ch. 3, proof of Theorem 4.3, (1)–(6),
(10), (11), `chapter-03.txt` lines 607–652 and 689–733). Let `(μ, ν)` be a Gauss–Green pair for
`(U, E)`, `x ∈ ∂*E` and `e = ν_E(x)`. Then there are `ρ₁ > 0` with `B_{ρ₁}(x) ⊆ U` and constants
`C`, `c > 0` with `μ(B_ρ(x)) ≤ C ρⁿ`, `L^{n+1}(E ∩ B_ρ(x)) ≥ c ρ^{n+1}` and
`L^{n+1}(B_ρ(x) ∖ E) ≥ c ρ^{n+1}` for `0 < ρ < ρ₁`, and `ρ⁻ⁿ ∫_{B_ρ(x)} |ν - e| dμ → 0` as
`ρ ↓ 0`. The normal-average bounds give `|e| = 1` and `ρ₀ > 0` with `B_{ρ₀}(x) ⊆ U` and
`0 < μ(B_ρ(x)) ≤ 2 ∫_{B_ρ(x)} ν · e dμ` for `0 < ρ < ρ₀`; take `ρ₁ = ρ₀`. The upper mass bound
with `w = e` gives (6') with `C = 2 (n + 1) ω_{n+1}`, and the lower volume bound gives (10) with
`w = e`; for (11) it is applied to the pair `(μ, -ν)` of `(U, U ∖ E)` with `w = -e`, since
`(-ν) · (-e) = ν · e` and `(U ∖ E) ∩ B_ρ(x) = B_ρ(x) ∖ E`. The excess decay is the last clause of
the normal-average bounds, fed with (6'). -/
theorem Submission.deGiorgi_density_estimates : ∀ (n : ℕ) (U E : Set (Rn (n + 1))) (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)), IsOpen U → NullMeasurableSet E volume → IsGaussGreenPair U E μ ν → ∀ x ∈ reducedBoundary U μ ν, ∃ ρ₁ : ℝ, 0 < ρ₁ ∧ Metric.ball x ρ₁ ⊆ U ∧ ∃ C c : ℝ, 0 < c ∧ (∀ ρ ∈ Ioo 0 ρ₁, μ (Metric.ball x ρ) ≤ ENNReal.ofReal (C * ρ ^ n) ∧ ENNReal.ofReal (c * ρ ^ (n + 1)) ≤ volume (E ∩ Metric.ball x ρ) ∧ ENNReal.ofReal (c * ρ ^ (n + 1)) ≤ volume (Metric.ball x ρ \ E)) ∧ Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ y in Metric.ball x ρ, ‖ν y - reducedNormal μ ν x‖ ∂μ) (𝓝[>] 0) (𝓝 0) := by
  intro n U E μ ν hU hE hpair x hx
  -- Simon (1), (2): `|e| = 1` and `0 < μ(B_ρ(x)) ≤ 2 ∫_{B_ρ(x)} ν · e dμ` for `0 < ρ < ρ₀`.
  obtain ⟨he, ⟨ρ₀, hρ₀, hball, hhalf⟩, hexcess⟩ :=
    Submission.deGiorgiDens_normalAverage_bounds (n + 1) U μ ν hU hpair.2.1 hpair.2.2.1
      hpair.2.2.2.1 x hx
  -- (6'): `μ(B_ρ(x)) ≤ 2 (n + 1) ω_{n+1} ρⁿ`.
  have hmass := Submission.deGiorgiDens_ball_mass_le n U E μ ν hU hE hpair x
    (reducedNormal μ ν x) ρ₀ he.le hball fun ρ hρ ↦ (hhalf ρ hρ).2
  -- (10) for `E` with `w = e`, and (11) for the pair `(μ, -ν)` of `(U, U ∖ E)` with `w = -e`.
  obtain ⟨c, hc, hvol⟩ := Submission.deGiorgiDens_ball_volume_ge n
  have hlowE := hvol U E μ ν hU hE hpair x (reducedNormal μ ν x) ρ₀ he.le hball hhalf
  have hlowC := hvol U (U \ E) μ (-ν) hU (hU.measurableSet.nullMeasurableSet.diff hE)
    (Submission.deGiorgi_gaussGreenPair_compl (n + 1) U E μ ν hU hE hpair) x
    (-reducedNormal μ ν x) ρ₀ (by rw [norm_neg]; exact he.le) hball fun ρ hρ ↦ by
      simpa only [Pi.neg_apply, inner_neg_neg] using hhalf ρ hρ
  refine ⟨ρ₀, hρ₀, hball, 2 * (n + 1) * (volume (Metric.ball (0 : Rn (n + 1)) 1)).toReal, c, hc,
    fun ρ hρ ↦ ⟨hmass ρ hρ, hlowE ρ hρ, ?_⟩, hexcess n _ ρ₀ hρ₀ hmass⟩
  -- `(U ∖ E) ∩ B_ρ(x) = B_ρ(x) ∖ E`, as `B_ρ(x) ⊆ B_{ρ₀}(x) ⊆ U`.
  have hsub : Metric.ball x ρ ⊆ U := (Metric.ball_subset_ball hρ.2.le).trans hball
  rw [← inter_eq_right.2 hsub, ← sdiff_inter_right_comm]
  exact hlowC ρ hρ
/-- **The measure of a symmetric difference in a ball is the `L¹` distance of the indicators**
(used in the BV translation estimate for the compactness of sets of locally bounded perimeter,
Simon Ch. 2, Thm. 2.6). For `Lᴺ`-measurable `A, F ⊆ ℝᴺ` and the open ball `B = B_R(0)`,
`Lᴺ(B ∩ (A Δ F)) = ∫_B |1_A - 1_F| dLᴺ`: pointwise `|1_A - 1_F| = 1_{A Δ F}`, and
`∫_B 1_{A Δ F} dLᴺ = Lᴺ(A Δ F ∩ B)`, which is finite since `Lᴺ(B) < ∞`. -/
theorem Submission.indCompact_transEst_volume_symmDiff_eq_integral : ∀ (N : ℕ) (A F : Set (Rn N)) (R : ℝ), NullMeasurableSet A volume → NullMeasurableSet F volume → volume (Metric.ball (0 : Rn N) R ∩ symmDiff A F) = ENNReal.ofReal (∫ y in Metric.ball (0 : Rn N) R, |A.indicator (1 : Rn N → ℝ) y - F.indicator (1 : Rn N → ℝ) y|) := by
  intro N A F R hA hF
  -- Step 1: `|1_A - 1_F| = 1_{A Δ F}` pointwise.
  have h1 : ∀ y, |A.indicator (1 : Rn N → ℝ) y - F.indicator (1 : Rn N → ℝ) y| =
      (symmDiff A F).indicator (fun _ ↦ (1 : ℝ)) y := by
    intro y
    rw [← abs_indicator_symmDiff]
    by_cases hy : y ∈ symmDiff A F <;> simp [hy]
  simp_rw [h1]
  -- Step 2: `A Δ F` is null-measurable for `Lᴺ`, hence for `Lᴺ ⌞ B ≤ Lᴺ`.
  have hS : NullMeasurableSet (symmDiff A F) (volume.restrict (Metric.ball (0 : Rn N) R)) :=
    (hA.symmDiff hF).mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  -- Step 5: `Lᴺ(A Δ F ∩ B) ≤ Lᴺ(B) < ∞`.
  have hfin : volume (symmDiff A F ∩ Metric.ball (0 : Rn N) R) ≠ ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt measure_ball_lt_top).ne
  -- Steps 3, 4 and 6: `∫_B 1_{A Δ F} dLᴺ = (Lᴺ ⌞ B)(A Δ F) = Lᴺ(A Δ F ∩ B)`, `B` being open.
  rw [integral_indicator₀ hS, setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
    Measure.restrict_apply' measurableSet_ball, ENNReal.ofReal_toReal hfin, Set.inter_comm]
/-- **Translation change of variables for indicator differences** (Step 5(a) of the supplied
proof of the BV translation estimate used for the compactness of sets of bounded perimeter in
De Giorgi's theorem, Simon Ch. 3, Theorem 4.3). For `L^N`-measurable `F ⊆ ℝᴺ`, integrable `ψ`
and `h ∈ ℝᴺ`, `∫ (χ_F(y + h) - χ_F(y)) ψ(y) dy = ∫_F (ψ(z - h) - ψ(z)) dz`: pointwise the
integrand is `G(y + h) - H(y)` with `G = χ_F ψ(· - h)` and `H = χ_F ψ`, and Lebesgue measure is
translation invariant. -/
theorem Submission.indCompact_transEst_integral_indicator_shift_mul : ∀ (N : ℕ) (F : Set (Rn N)) (ψ : Rn N → ℝ) (h : Rn N), NullMeasurableSet F volume → Integrable ψ volume → ∫ y, (F.indicator (1 : Rn N → ℝ) (y + h) - F.indicator (1 : Rn N → ℝ) y) * ψ y = ∫ z in F, (ψ (z - h) - ψ z) := by
  intro N F ψ h hF hψ
  -- The translate `ψ_h = ψ (· - h)` is integrable.
  have hψh : Integrable (fun z ↦ ψ (z - h)) volume := hψ.comp_sub_right h
  -- `y ↦ G (y + h)` with `G = 1_F ψ_h`, and `H = 1_F ψ`, are integrable.
  have hG : Integrable (fun y ↦ F.indicator (fun z ↦ ψ (z - h)) (y + h)) volume :=
    (hψh.indicator₀ hF).comp_add_right h
  have hH : Integrable (F.indicator ψ) volume := hψ.indicator₀ hF
  -- Pointwise, `(1_F (y + h) - 1_F y) ψ y = G (y + h) - H y` (four cases).
  have hpt : ∀ y, (F.indicator (1 : Rn N → ℝ) (y + h) - F.indicator (1 : Rn N → ℝ) y) * ψ y =
      F.indicator (fun z ↦ ψ (z - h)) (y + h) - F.indicator ψ y := by
    intro y
    by_cases hy₁ : y + h ∈ F <;> by_cases hy₂ : y ∈ F <;> simp [hy₁, hy₂]
  -- Linearity, translation invariance, indicator integrals, linearity on `F`.
  calc ∫ y, (F.indicator (1 : Rn N → ℝ) (y + h) - F.indicator (1 : Rn N → ℝ) y) * ψ y
      = ∫ y, (F.indicator (fun z ↦ ψ (z - h)) (y + h) - F.indicator ψ y) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = (∫ y, F.indicator (fun z ↦ ψ (z - h)) (y + h)) - ∫ y, F.indicator ψ y :=
        integral_sub hG hH
    _ = (∫ z in F, ψ (z - h)) - ∫ z in F, ψ z := by
        rw [integral_add_right_eq_self (F.indicator fun z ↦ ψ (z - h)) h,
          integral_indicator₀ hF, integral_indicator₀ hF]
    _ = ∫ z in F, (ψ (z - h) - ψ z) :=
        (integral_sub hψh.integrableOn hψ.integrableOn).symm
/-- **Translation difference of a `C¹_c` function as a parametric integral of directional
derivatives** (steps 5(b) and 5(d) of the BV translation estimate behind the Compactness
Theorem 2.6 of Simon Ch. 2, `chapter-02.txt` lines 598–620, [GT01, Thm. 7.22], as used in the
proof of Ch. 3, Thm. 4.3, `chapter-03.txt` line 653). For an arbitrary `F ⊆ ℝᴺ`, `ψ ∈ C¹_c(ℝᴺ)`
and `h ∈ ℝᴺ`: `∫_F (ψ(z - h) - ψ(z)) dz = -∫₀¹ ∫_F Dψ(z - th)[h] dz dt`. For fixed `z`, the
fundamental theorem of calculus along `t ↦ ψ(z - th)` gives
`ψ(z - h) - ψ(z) = -∫₀¹ Dψ(z - th)[h] dt`. The integrand `f(z, t) = Dψ(z - th)[h]` is continuous
and, for `t ∈ [0, 1]`, vanishes unless `z` lies in the compact `K = tsupport ψ + [0, 1] h`; so it
is integrable on `ℝᴺ × [0, 1] ⊇ F × (0, 1]`, and Fubini for `Lᴺ ⌞ F ⊗ L¹ ⌞ (0, 1]` swaps the
integrals. -/
theorem Submission.indCompact_transEst_setIntegral_shift_sub_ftc : ∀ (N : ℕ) (F : Set (Rn N)) (ψ : Rn N → ℝ) (h : Rn N), ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∫ z in F, (ψ (z - h) - ψ z) = -∫ t in (0 : ℝ)..1, ∫ z in F, fderiv ℝ ψ (z - t • h) h := by
  intro N F ψ h hψ hψs
  -- Step 1: `ψ` is differentiable and `f(z, t) = Dψ(z - th)[h]` is continuous on `ℝᴺ × ℝ`.
  have hdiff : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  set f : Rn N → ℝ → ℝ := fun z t ↦ fderiv ℝ ψ (z - t • h) h
  have hfc : Continuous (Function.uncurry f) :=
    (hcont.comp (continuous_fst.sub (continuous_snd.smul continuous_const))).clm_apply
      continuous_const
  -- Step 2 (FTC along `t ↦ ψ(z - th)`, whose derivative is `-f(z, t)`):
  -- `ψ(z - h) - ψ(z) = -∫₀¹ f(z, t) dt`.
  have hftc : ∀ z, ψ (z - h) - ψ z = -∫ t in (0 : ℝ)..1, f z t := by
    intro z
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ ↦ ψ (z - t • h)) (-(f z t)) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ ↦ z - t • h) (-h) t := by
        simpa using ((hasDerivAt_id t).smul_const h).const_sub z
      have h2 : HasDerivAt (fun t : ℝ ↦ ψ (z - t • h)) (fderiv ℝ ψ (z - t • h) (-h)) t :=
        (hdiff (z - t • h)).hasFDerivAt.comp_hasDerivAt t h1
      simpa [f, map_neg] using h2
    have hint : IntervalIntegrable (fun t ↦ -(f z t)) volume 0 1 :=
      ((hfc.comp (continuous_const.prodMk continuous_id)).neg).intervalIntegrable 0 1
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simp only [one_smul, zero_smul, sub_zero, intervalIntegral.integral_neg] at this
    linarith
  -- Step 3: integrate over `F`, write `∫₀¹` as `∫_{(0, 1]}`, and reduce to Fubini for
  -- `Lᴺ ⌞ F ⊗ L¹ ⌞ (0, 1]`.
  rw [integral_congr_ae (Eventually.of_forall hftc), integral_neg]
  congr 1
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  apply integral_integral_swap
  -- Step 4: integrability. With `K = {x + s h : x ∈ tsupport ψ, s ∈ [0, 1]}` compact, `f` is
  -- integrable on `K × [0, 1]` and vanishes on `(ℝᴺ × [0, 1]) \ (K × [0, 1])`.
  set K : Set (Rn N) := (fun p : Rn N × ℝ ↦ p.1 + p.2 • h) '' (tsupport ψ ×ˢ Icc (0 : ℝ) 1)
  have hK : IsCompact K := (hψs.isCompact.prod isCompact_Icc).image (by fun_prop)
  rw [Measure.prod_restrict]
  have h1 : IntegrableOn (Function.uncurry f) (K ×ˢ Icc (0 : ℝ) 1) (volume.prod volume) :=
    hfc.continuousOn.integrableOn_compact (hK.prod isCompact_Icc)
  have h2 : IntegrableOn (Function.uncurry f) (univ ×ˢ Icc (0 : ℝ) 1) (volume.prod volume) := by
    refine h1.of_forall_sdiff_eq_zero (MeasurableSet.univ.prod measurableSet_Icc) ?_
    rintro ⟨z, t⟩ ⟨⟨-, ht⟩, hnot⟩
    simp only [Function.uncurry_apply_pair, f]
    by_contra hne
    apply hnot
    refine ⟨?_, ht⟩
    -- `Dψ = 0` off `tsupport ψ`, so `z - th ∈ tsupport ψ` and `z = (z - th) + th ∈ K`.
    have hmem : z - t • h ∈ tsupport ψ := by
      by_contra hns
      apply hne
      rw [fderiv_of_notMem_tsupport ℝ hns]
      simp
    exact ⟨(z - t • h, t), ⟨hmem, ht⟩, by simp⟩
  -- Step 5: `F × (0, 1] ⊆ ℝᴺ × [0, 1]`.
  exact h2.mono_set (prod_mono (subset_univ _) Ioc_subset_Icc_self)
/-- **Divergence-test bound for translated directional derivatives** (a step of the translation
estimate behind the compactness theorem, Simon Ch. 2, Thm. 2.6, used in Ch. 3, proof of
Thm. 4.3): if `∫_F div g ≤ C` for every `C¹` field `g` with compact support in `B_{R+1}(0)` and
`|g| ≤ 1`, then `|∫_F Dψ(z - a)[h] dz| ≤ C |h|` for every `C¹` function `ψ` with compact support
in `B_R(0)` and `|ψ| ≤ 1`, and all `a, h` with `|a| ≤ 1`. For `|c| = |h|⁻¹` the field
`G = c ψ(· - a) h` is admissible and `div G(z) = c Dψ(z - a)[h]` (the trace of a rank-one map),
so `c ∫_F Dψ(z - a)[h] dz ≤ C`; take `c = ±|h|⁻¹`. -/
theorem Submission.indCompact_transEst_abs_setIntegral_fderiv_le : ∀ (N : ℕ) (F : Set (Rn N))
    (R C : ℝ), (∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g →
      tsupport g ⊆ Metric.ball (0 : Rn N) (R + 1) → (∀ y, ‖g y‖ ≤ 1) →
      ∫ y in F, Poincare.SimonGMT.Chapter02.euclideanDivergence g y ≤ C) →
    ∀ ψ : Rn N → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball (0 : Rn N) R → (∀ y, |ψ y| ≤ 1) →
      ∀ a h : Rn N, ‖a‖ ≤ 1 → |∫ z in F, fderiv ℝ ψ (z - a) h| ≤ C * ‖h‖ := by
  intro N F R C hdiv ψ hψ hψs hψsub hψ1 a h ha
  -- Step 1. The case `h = 0` is trivial; otherwise `‖h‖ > 0`.
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  have hpos : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hdiff : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  set I := ∫ z in F, fderiv ℝ ψ (z - a) h with hI
  -- Step 2. `ψ(· - a)` has compact support, and `tsupport ψ(· - a) ⊆ B_{R+1}(0)`.
  have hTs : HasCompactSupport (fun y ↦ ψ (y - a)) := by
    simpa [Function.comp_def] using hψs.comp_homeomorph (Homeomorph.subRight a)
  have hTsub : tsupport (fun y ↦ ψ (y - a)) ⊆ Metric.ball 0 (R + 1) := by
    intro y hy
    have hy' : y - a ∈ tsupport ψ := by
      have := tsupport_comp_eq_preimage ψ (Homeomorph.subRight a)
      have hy2 : y ∈ tsupport (ψ ∘ (Homeomorph.subRight a)) := by
        simpa [Function.comp_def] using hy
      rw [this] at hy2
      simpa using hy2
    have h1 := hψsub hy'
    rw [mem_ball_zero_iff] at h1 ⊢
    calc ‖y‖ = ‖(y - a) + a‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - a‖ + ‖a‖ := norm_add_le _ _
      _ < R + 1 := by linarith
  -- Step 3. For `|c| = ‖h‖⁻¹`, testing the hypothesis with `G = c ψ(· - a) h` gives `c I ≤ C`.
  have key : ∀ c : ℝ, |c| = ‖h‖⁻¹ → c * I ≤ C := by
    intro c hc
    set G : Rn N → Rn N := fun y ↦ (c * ψ (y - a)) • h with hG
    have hGc : ContDiff ℝ 1 G :=
      (contDiff_const.mul (hψ.comp (contDiff_id.sub contDiff_const))).smul contDiff_const
    have hGsupp : tsupport G ⊆ tsupport (fun y ↦ ψ (y - a)) := by
      refine (tsupport_smul_subset_left _ _).trans ?_
      exact tsupport_mul_subset_right
    have hGcs : HasCompactSupport G :=
      hTs.of_isClosed_subset (isClosed_tsupport _) hGsupp
    have hGb : ∀ y, ‖G y‖ ≤ 1 := by
      intro y
      simp only [hG, norm_smul, Real.norm_eq_abs, abs_mul, hc]
      calc ‖h‖⁻¹ * |ψ (y - a)| * ‖h‖ = |ψ (y - a)| := by field_simp
        _ ≤ 1 := hψ1 _
    -- `div G(z) = trace (Dφ(z).smulRight h) = Dφ(z)[h] = c Dψ(z - a)[h]`, `φ = c ψ(· - a)`.
    have hdivG : ∀ z, Poincare.SimonGMT.Chapter02.euclideanDivergence G z
        = c * fderiv ℝ ψ (z - a) h := by
      intro z
      have hd : DifferentiableAt ℝ (fun y ↦ c * ψ (y - a)) z :=
        (differentiableAt_const _).mul ((hdiff _).comp z (differentiableAt_id.sub_const a))
      simp only [Poincare.SimonGMT.Chapter02.euclideanDivergence, hG]
      rw [fderiv_smul_const hd]
      have : ((fderiv ℝ (fun y ↦ c * ψ (y - a)) z).smulRight h : Rn N →L[ℝ] Rn N).toLinearMap
          = (fderiv ℝ (fun y ↦ c * ψ (y - a)) z).toLinearMap.smulRight h := by
        ext v; simp
      rw [this, LinearMap.trace_smulRight]
      have hd' : DifferentiableAt ℝ (fun y ↦ ψ (y - a)) z :=
        (hdiff (z - a)).comp z (differentiableAt_id.sub_const a)
      rw [ContinuousLinearMap.coe_coe, fderiv_const_mul hd' c, fderiv_comp_sub]
      simp
    have := hdiv G hGc hGcs (hGsupp.trans hTsub) hGb
    simpa [hdivG, integral_const_mul] using this
  -- Step 4. `c = ‖h‖⁻¹` gives `I ≤ C ‖h‖`, and `c = -‖h‖⁻¹` gives `-I ≤ C ‖h‖`.
  have k1 := key ‖h‖⁻¹ (abs_of_pos (inv_pos.mpr hpos))
  have k2 := key (-‖h‖⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.mpr hpos)])
  have e1 : I ≤ C * ‖h‖ := by
    have := mul_le_mul_of_nonneg_left k1 hpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this
    linarith
  have e2 : -I ≤ C * ‖h‖ := by
    have := mul_le_mul_of_nonneg_left k2 hpos.le
    rw [← mul_assoc, mul_neg, mul_inv_cancel₀ hpos.ne', neg_one_mul] at this
    linarith
  exact abs_le.mpr ⟨by linarith, e1⟩
/-- **A.e. approximation by admissible `C¹` test functions** (the mollification part of the
`L¹`-duality step of the proof of Simon Ch. 2, Thm. 2.6, used in Ch. 3, proof of Thm. 4.3): if `s`
is a.e.-strongly measurable, `|s| ≤ 1` and `s = 0` off `B_R(0)`, then `C¹` functions `ψⱼ` with
compact support, `tsupport ψⱼ ⊆ B_R(0)` and `|ψⱼ| ≤ 1` converge to `s` a.e. Here
`ψⱼ = ρⱼ ⋆ (1_{B_{R - 2δⱼ}(0)} s)`, `δⱼ = R / (4 (j + 1))`, `ρⱼ` the bump with radii
`δⱼ / 2 < δⱼ` normalized to integral `1`: `supp ψⱼ ⊆ B̄_{R - δⱼ}(0)`, `ψⱼ = ρⱼ ⋆ s` near each
point of `B_R(0)` for large `j`, and `ρⱼ ⋆ s → s` a.e. by Lebesgue differentiation. -/
theorem Submission.indCompact_l1Dual_exists_admissible_ae_tendsto : ∀ (N : ℕ) (R : ℝ)
    (s : Rn N → ℝ), 0 < R → AEStronglyMeasurable s volume → (∀ y, |s y| ≤ 1) →
    (∀ y, y ∉ Metric.ball (0 : Rn N) R → s y = 0) →
    ∃ ψ : ℕ → Rn N → ℝ, (∀ j, ContDiff ℝ 1 (ψ j)) ∧ (∀ j, HasCompactSupport (ψ j)) ∧
      (∀ j, tsupport (ψ j) ⊆ Metric.ball (0 : Rn N) R) ∧ (∀ j y, |ψ j y| ≤ 1) ∧
      ∀ᵐ y ∂(volume : Measure (Rn N)), Tendsto (fun j ↦ ψ j y) atTop (𝓝 (s y)) := by
  intro N R s hR hs_meas hs_le hs_zero
  -- Step 1. `|s| ≤ 1_{B_R(0)}` and `L^N(B_R(0)) < ∞`, so `s` is integrable.
  have hs_int : Integrable s volume := by
    refine Integrable.mono' (g := (Metric.ball (0 : Rn N) R).indicator fun _ ↦ (1 : ℝ))
      ((integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne))
      hs_meas (Eventually.of_forall fun y ↦ ?_)
    by_cases hy : y ∈ Metric.ball (0 : Rn N) R
    · simpa [indicator_of_mem hy, Real.norm_eq_abs] using hs_le y
    · simp [indicator_of_notMem hy, hs_zero y hy]
  -- Step 2. Radii `δⱼ = R / (4 (j + 1)) > 0` with `δⱼ → 0`.
  obtain ⟨δ, hδ_pos, hδ_lim⟩ : ∃ δ : ℕ → ℝ, (∀ j, 0 < δ j) ∧ Tendsto δ atTop (𝓝 0) :=
    ⟨fun j ↦ R / 4 * (1 / ((j : ℝ) + 1)), fun j ↦ by positivity,
      by simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (R / 4)⟩
  -- Step 3. Mollifiers `ρⱼ = φⱼ / ∫ φⱼ`, `φⱼ` the bump with `rIn = δⱼ / 2`, `rOut = δⱼ`.
  obtain ⟨ρ, hρ_cd, hρ_cs, hρ_nn, hρ_int, hρ_supp, hρ_le⟩ : ∃ ρ : ℕ → Rn N → ℝ,
      (∀ j, ContDiff ℝ 1 (ρ j)) ∧ (∀ j, HasCompactSupport (ρ j)) ∧ (∀ j y, 0 ≤ ρ j y) ∧
      (∀ j, ∫ y, ρ j y = 1) ∧ (∀ j, Function.support (ρ j) ⊆ Metric.ball 0 (δ j)) ∧
      ∀ j y, ρ j y ≤ 2 ^ finrank ℝ (Rn N) / volume.real (Metric.closedBall (0 : Rn N) (δ j)) := by
    let φ : ℕ → ContDiffBump (0 : Rn N) := fun j ↦
      ⟨δ j / 2, δ j, half_pos (hδ_pos j), half_lt_self (hδ_pos j)⟩
    have hφ_int : ∀ j, Integrable (φ j) volume := fun j ↦
      (φ j).continuous.integrable_of_hasCompactSupport (φ j).hasCompactSupport
    -- `φⱼ = 1` on `B̄_{δⱼ/2}(0)` and `φⱼ ≥ 0`, so `L^N(B̄_{δⱼ/2}(0)) ≤ ∫ φⱼ`.
    have hφ_ge : ∀ j, volume.real (Metric.closedBall (0 : Rn N) (δ j / 2)) ≤ ∫ y, φ j y := by
      intro j
      calc volume.real (Metric.closedBall (0 : Rn N) (δ j / 2))
          = ∫ y in Metric.closedBall (0 : Rn N) (δ j / 2), (1 : ℝ) := by simp
        _ = ∫ y in Metric.closedBall (0 : Rn N) (δ j / 2), φ j y :=
          setIntegral_congr_fun measurableSet_closedBall
            fun y hy ↦ ((φ j).one_of_mem_closedBall hy).symm
        _ ≤ ∫ y, φ j y :=
          setIntegral_le_integral (hφ_int j) (Eventually.of_forall fun y ↦ (φ j).nonneg)
    have hball : ∀ j, 0 < volume.real (Metric.closedBall (0 : Rn N) (δ j / 2)) := fun j ↦
      ENNReal.toReal_pos (Metric.measure_closedBall_pos _ _ (half_pos (hδ_pos j))).ne'
        measure_closedBall_lt_top.ne
    have hI : ∀ j, 0 < ∫ y, φ j y := fun j ↦ (hball j).trans_le (hφ_ge j)
    -- Scaling: `L^N(B̄_{δⱼ}(0)) = 2^N L^N(B̄_{δⱼ/2}(0))`.
    have hscale : ∀ j, volume.real (Metric.closedBall (0 : Rn N) (δ j)) =
        2 ^ finrank ℝ (Rn N) * volume.real (Metric.closedBall (0 : Rn N) (δ j / 2)) := by
      intro j
      have h := Measure.addHaar_closedBall_mul (volume : Measure (Rn N)) 0 zero_le_two
        (half_pos (hδ_pos j)).le
      rw [show (2 : ℝ) * (δ j / 2) = δ j by ring] at h
      rw [measureReal_def, measureReal_def, h, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity)]
    refine ⟨fun j y ↦ (∫ y, φ j y)⁻¹ * φ j y, fun j ↦ contDiff_const.mul (φ j).contDiff,
      fun j ↦ (φ j).hasCompactSupport.mul_left,
      fun j y ↦ mul_nonneg (inv_nonneg.2 (hI j).le) (φ j).nonneg, fun j ↦ ?_, fun j y hy ↦ ?_,
      fun j y ↦ ?_⟩
    · show ∫ y, (∫ y, φ j y)⁻¹ * φ j y = 1
      rw [integral_const_mul, inv_mul_cancel₀ (hI j).ne']
    · have hy' : φ j y ≠ 0 := right_ne_zero_of_mul hy
      rw [← Function.mem_support, (φ j).support_eq] at hy'
      exact hy'
    · show (∫ y, φ j y)⁻¹ * φ j y ≤ _
      calc (∫ y, φ j y)⁻¹ * φ j y ≤ (∫ y, φ j y)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (φ j).le_one (inv_nonneg.2 (hI j).le)
        _ ≤ (volume.real (Metric.closedBall (0 : Rn N) (δ j / 2)))⁻¹ := by
            rw [mul_one]; exact inv_anti₀ (hball j) (hφ_ge j)
        _ = 2 ^ finrank ℝ (Rn N) / volume.real (Metric.closedBall (0 : Rn N) (δ j)) := by
            rw [hscale j]; field_simp
  -- Step 4. Truncations `sⱼ = 1_{B_{R - 2δⱼ}(0)} s`.
  obtain ⟨sj, hsj_int, hsj_le, hsj_supp, hsj_eq⟩ : ∃ sj : ℕ → Rn N → ℝ,
      (∀ j, Integrable (sj j) volume) ∧ (∀ j y, |sj j y| ≤ 1) ∧
      (∀ j, Function.support (sj j) ⊆ Metric.ball 0 (R - 2 * δ j)) ∧
      ∀ j y, y ∈ Metric.ball (0 : Rn N) (R - 2 * δ j) → sj j y = s y := by
    refine ⟨fun j ↦ (Metric.ball (0 : Rn N) (R - 2 * δ j)).indicator s,
      fun j ↦ hs_int.indicator measurableSet_ball, fun j y ↦ ?_,
      fun j ↦ support_indicator_subset, fun j y hy ↦ indicator_of_mem hy s⟩
    show |(Metric.ball (0 : Rn N) (R - 2 * δ j)).indicator s y| ≤ 1
    by_cases hy : y ∈ Metric.ball (0 : Rn N) (R - 2 * δ j)
    · rw [indicator_of_mem hy]; exact hs_le y
    · rw [indicator_of_notMem hy, abs_zero]; exact zero_le_one
  -- Step 7. `supp (ρⱼ ⋆ sⱼ) ⊆ B_{δⱼ}(0) + B_{R - 2δⱼ}(0) ⊆ B̄_{R - δⱼ}(0) ⊆ B_R(0)`.
  have hψ_supp : ∀ j, Function.support (convolution (ρ j) (sj j)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆ Metric.closedBall 0 (R - δ j) := by
    intro j x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 (support_convolution_subset _ hx)
    have ha' := mem_ball_zero_iff.1 (hρ_supp j ha)
    have hb' := mem_ball_zero_iff.1 (hsj_supp j hb)
    rw [mem_closedBall_zero_iff]
    linarith [norm_add_le a b]
  have hψ_tsupp : ∀ j, tsupport (convolution (ρ j) (sj j)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆ Metric.closedBall 0 (R - δ j) :=
    fun j ↦ closure_minimal (hψ_supp j) Metric.isClosed_closedBall
  have hball_sub : ∀ j, Metric.closedBall (0 : Rn N) (R - δ j) ⊆ Metric.ball 0 R :=
    fun j ↦ Metric.closedBall_subset_ball (by linarith [hδ_pos j])
  -- Step 9. Lebesgue differentiation: `ρⱼ ⋆ s → s` almost everywhere.
  have hconv : ∀ᵐ x ∂(volume : Measure (Rn N)),
      Tendsto (fun j ↦ convolution (ρ j) s (ContinuousLinearMap.lsmul ℝ ℝ) volume x) atTop
        (𝓝 (s x)) := by
    have hδ' : Tendsto δ atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hδ_lim, Eventually.of_forall hδ_pos⟩
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume
      hs_int.locallyIntegrable 1] with x hx
    have hav := hx (fun _ ↦ x) δ hδ' (Eventually.of_forall fun j ↦
      Metric.mem_closedBall_self (by linarith [hδ_pos j]))
    simp only [convolution_eq_swap, ContinuousLinearMap.lsmul_apply]
    refine tendsto_integral_smul_of_tendsto_average_norm_sub
      (a := fun j ↦ Metric.closedBall x (δ j)) (g := fun j y ↦ ρ j (x - y))
      (2 ^ finrank ℝ (Rn N)) hav (Eventually.of_forall fun j ↦ hs_int.integrableOn)
      (tendsto_const_nhds.congr fun j ↦ ?_) (Eventually.of_forall fun j y hy ↦ ?_)
      (Eventually.of_forall fun j y ↦ ?_)
    · rw [integral_sub_left_eq_self (ρ j) volume x, hρ_int j]
    · rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
      exact (mem_ball_zero_iff.1 (hρ_supp j hy)).le
    · show |ρ j (x - y)| ≤ 2 ^ finrank ℝ (Rn N) / volume.real (Metric.closedBall x (δ j))
      rw [abs_of_nonneg (hρ_nn j _), Measure.addHaar_real_closedBall_center]
      exact hρ_le j (x - y)
  -- Steps 5 (`C¹`), 7 (support) and 11.
  refine ⟨fun j ↦ convolution (ρ j) (sj j) (ContinuousLinearMap.lsmul ℝ ℝ) volume,
    fun j ↦ (hρ_cs j).contDiff_convolution_left _ (hρ_cd j) (hsj_int j).locallyIntegrable,
    fun j ↦ HasCompactSupport.intro (isCompact_closedBall 0 (R - δ j))
      fun x hx ↦ Function.notMem_support.1 fun h ↦ hx (hψ_supp j h),
    fun j ↦ (hψ_tsupp j).trans (hball_sub j), fun j y ↦ ?_, ?_⟩
  · -- Step 6. `|ρⱼ ⋆ sⱼ| ≤ ∫ ρⱼ = 1`.
    have h := dist_convolution_le (μ := volume) (x₀ := y) (z₀ := (0 : ℝ)) zero_le_one
      (hρ_supp j) (hρ_nn j) (hρ_int j) (hsj_int j).aestronglyMeasurable
      fun x _ ↦ by rw [Real.dist_0_eq_abs]; exact hsj_le j x
    rwa [Real.dist_0_eq_abs] at h
  · -- Step 10. On `B_R(0)`, eventually `ψⱼ = ρⱼ ⋆ s` (step 8); off `B_R(0)`, `ψⱼ = 0 = s`.
    filter_upwards [hconv] with x hx
    by_cases hxB : x ∈ Metric.ball (0 : Rn N) R
    · have hx' := mem_ball_zero_iff.1 hxB
      have hη : 0 < (R - ‖x‖) / 3 := by linarith
      refine hx.congr' ?_
      filter_upwards [hδ_lim.eventually (gt_mem_nhds hη)] with j hj
      show convolution (ρ j) s _ volume x = convolution (ρ j) (sj j) _ volume x
      rw [convolution_def, convolution_def]
      refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
      show ContinuousLinearMap.lsmul ℝ ℝ (ρ j t) (s (x - t)) =
        ContinuousLinearMap.lsmul ℝ ℝ (ρ j t) (sj j (x - t))
      by_cases ht : ρ j t = 0
      · simp [ht]
      · have ht' := mem_ball_zero_iff.1 (hρ_supp j ht)
        rw [hsj_eq j (x - t) (mem_ball_zero_iff.2 (by linarith [norm_sub_le x t]))]
    · rw [hs_zero x hxB]
      refine tendsto_const_nhds.congr fun j ↦ ?_
      show 0 = convolution (ρ j) (sj j) _ volume x
      by_contra h
      exact hxB ((hψ_supp j).trans (hball_sub j) (Ne.symm h))
/-- **Dominated convergence for pairings with a function integrable on a ball**: the limit step of
the `L¹`-duality argument in the compactness theorem (Simon Ch. 2, Thm. 2.6) as used in the proof
of Ch. 3, Thm. 4.3. If `w` is integrable on `B = B_R(0)` and the a.e.-strongly measurable `ψ_j`
satisfy `|ψ_j| ≤ 1`, vanish off `B` and converge a.e. to `s`, then `∫ w ψ_j → ∫ w s`. Dominated
convergence with the integrable bound `1_B |w|`; `w ψ_j = 1_B (w ψ_j)` is a.e.-strongly measurable
because `w` is on `B`. No measurability of `s` is needed, and `R ≤ 0` (`B = ∅`) is not special. -/
theorem Submission.indCompact_l1Dual_tendsto_integral_mul : ∀ (N : ℕ) (w s : Rn N → ℝ) (R : ℝ)
    (ψ : ℕ → Rn N → ℝ), IntegrableOn w (Metric.ball (0 : Rn N) R) volume →
    (∀ j, AEStronglyMeasurable (ψ j) volume) → (∀ j y, |ψ j y| ≤ 1) →
    (∀ j y, y ∉ Metric.ball (0 : Rn N) R → ψ j y = 0) →
    (∀ᵐ y ∂(volume : Measure (Rn N)), Tendsto (fun j ↦ ψ j y) atTop (𝓝 (s y))) →
    Tendsto (fun j ↦ ∫ y, w y * ψ j y) atTop (𝓝 (∫ y, w y * s y)) := by
  intro N w s R ψ hw hψm hψ1 hψ0 hlim
  have hB : MeasurableSet (Metric.ball (0 : Rn N) R) := Metric.isOpen_ball.measurableSet
  -- Off the ball every `w ψ_j` vanishes, so `w ψ_j = 1_B (w ψ_j)`.
  have hind : ∀ j, (fun y ↦ w y * ψ j y) = (Metric.ball (0 : Rn N) R).indicator
      fun y ↦ w y * ψ j y := fun j ↦ funext fun y ↦ by
    by_cases hy : y ∈ Metric.ball (0 : Rn N) R
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy, hψ0 j y hy, mul_zero]
  refine tendsto_integral_of_dominated_convergence ((Metric.ball (0 : Rn N) R).indicator
      fun y ↦ ‖w y‖) (fun j ↦ ?_) ((integrable_indicator_iff hB).2 hw.norm)
      (fun j ↦ ae_of_all _ fun y ↦ ?_) ?_
  · -- Measurability: `w` is a.e.-strongly measurable on the ball.
    rw [hind j, aestronglyMeasurable_indicator_iff hB]
    exact hw.aestronglyMeasurable.mul (hψm j).restrict
  · -- Domination by `1_B |w|`.
    by_cases hy : y ∈ Metric.ball (0 : Rn N) R
    · rw [indicator_of_mem hy, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) ((Real.norm_eq_abs _).trans_le (hψ1 j y))
    · rw [indicator_of_notMem hy, hψ0 j y hy, mul_zero, norm_zero]
  · -- Pointwise a.e. convergence.
    filter_upwards [hlim] with y hy
    exact hy.const_mul (w y)

/-- **`L¹` norm on a ball by duality with `C¹` test functions** (the `L¹`-duality step of the
mollification proof of Simon Ch. 2, Thm. 2.6, used in Ch. 3, proof of Thm. 4.3): if `w` is
integrable on `B_R(0)` and `∫ w ψ ≤ M` for every `C¹` function `ψ` with compact support,
`tsupport ψ ⊆ B_R(0)` and `|ψ| ≤ 1`, then `∫_{B_R(0)} |w| ≤ M`. The test `ψ = 0` settles the
empty ball `R ≤ 0`. For `R > 0` the sign function `s = 1_{B_R(0)} sgn w` (here `sgn 0 = 1`)
satisfies `w s = 1_{B_R(0)} |w|`; admissible `ψⱼ → s` a.e.
(`indCompact_l1Dual_exists_admissible_ae_tendsto`) and dominated convergence
(`indCompact_l1Dual_tendsto_integral_mul`) give `M ≥ ∫ w ψⱼ → ∫_{B_R(0)} |w|`. -/
theorem Submission.indCompact_ball_integral_abs_le_of_test_bound : ∀ (N : ℕ) (w : Rn N → ℝ)
    (R M : ℝ), IntegrableOn w (Metric.ball (0 : Rn N) R) volume →
    (∀ ψ : Rn N → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball (0 : Rn N) R → (∀ y, |ψ y| ≤ 1) → ∫ y, w y * ψ y ≤ M) →
    ∫ y in Metric.ball (0 : Rn N) R, |w y| ≤ M := by
  intro N w R M hw hM
  rcases le_or_gt R 0 with hR | hR
  · -- Empty ball: the admissible test `ψ = 0` gives `0 ≤ M`.
    rw [Metric.ball_eq_empty.2 hR, setIntegral_empty]
    simpa using hM 0 contDiff_const HasCompactSupport.zero (by simp) (by simp)
  -- The sign function `s = 1_{B_R(0)} sgn w`: `|s| ≤ 1` and `s = 0` off the ball.
  obtain ⟨s, hs⟩ : ∃ s : Rn N → ℝ,
      s = (Metric.ball (0 : Rn N) R).indicator fun y ↦ if 0 ≤ w y then 1 else -1 := ⟨_, rfl⟩
  have hs_meas : AEStronglyMeasurable s volume := by
    rw [hs, aestronglyMeasurable_indicator_iff measurableSet_ball]
    exact ((Measurable.ite measurableSet_Ici measurable_const measurable_const).comp_aemeasurable
      hw.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hs_le : ∀ y, |s y| ≤ 1 := by
    intro y
    by_cases hy : y ∈ Metric.ball (0 : Rn N) R
    · rw [hs, indicator_of_mem hy]
      split_ifs <;> simp
    · simp [hs, indicator_of_notMem hy]
  have hs_zero : ∀ y, y ∉ Metric.ball (0 : Rn N) R → s y = 0 := fun y hy ↦ by
    rw [hs, indicator_of_notMem hy]
  -- `w s = 1_{B_R(0)} |w|`.
  have hws : ∫ y, w y * s y = ∫ y in Metric.ball (0 : Rn N) R, |w y| := by
    rw [← integral_indicator measurableSet_ball]
    congr 1
    funext y
    by_cases hy : y ∈ Metric.ball (0 : Rn N) R
    · rw [hs, indicator_of_mem hy, indicator_of_mem hy]
      split_ifs with h
      · rw [mul_one, abs_of_nonneg h]
      · rw [mul_neg_one, abs_of_neg (not_le.1 h)]
    · rw [hs, indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]
  -- Admissible `ψⱼ → s` a.e., and dominated convergence `∫ w ψⱼ → ∫ w s`.
  obtain ⟨ψ, hψ, hψc, hψt, hψb, hψs⟩ :=
    Submission.indCompact_l1Dual_exists_admissible_ae_tendsto N R s hR hs_meas hs_le hs_zero
  have hlim := Submission.indCompact_l1Dual_tendsto_integral_mul N w s R ψ hw
    (fun j ↦ (hψ j).continuous.aestronglyMeasurable) hψb
    (fun j y hy ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hy (hψt j h)) hψs
  rw [hws] at hlim
  exact le_of_tendsto' hlim fun j ↦ hM (ψ j) (hψ j) (hψc j) (hψt j) (hψb j)

/-- **Translation estimate for the indicator of a set with bounded perimeter in `B_{R+1}(0)`**
(the `L¹` translation bound behind the compactness theorem for sets of locally bounded perimeter,
Simon Ch. 2, Thm. 2.6, used in Ch. 3, proof of Thm. 4.3): if `∫_F div g ≤ C` for every `C¹`
field `g` with compact support in `B_{R+1}(0)` and `|g| ≤ 1`, then
`Lᴺ(B_R(0) ∩ (F_h Δ F)) ≤ C |h|` for `|h| ≤ 1`, where `F_h = {y : y + h ∈ F}`. With
`w = 1_F(· + h) - 1_F` we have `Lᴺ(B_R(0) ∩ (F_h Δ F)) = ∫_{B_R(0)} |w|`, and for every `C¹`
test function `ψ` with compact support in `B_R(0)` and `|ψ| ≤ 1`,
`∫ w ψ = ∫_F (ψ(z - h) - ψ(z)) dz = -∫_0^1 ∫_F Dψ(z - t h)[h] dz dt ≤ C |h|`, since each inner
integral is the integral over `F` of the divergence of the field `ψ(· - t h) h`. `L¹` duality on
`B_R(0)` concludes. -/
theorem Submission.indCompact_translation_estimate : ∀ (N : ℕ) (F : Set (Rn N)) (R C : ℝ), NullMeasurableSet F volume → (∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ Metric.ball (0 : Rn N) (R + 1) → (∀ y, ‖g y‖ ≤ 1) → ∫ y in F, Poincare.SimonGMT.Chapter02.euclideanDivergence g y ≤ C) → ∀ h : Rn N, ‖h‖ ≤ 1 → volume (Metric.ball (0 : Rn N) R ∩ symmDiff ((fun y ↦ y + h) ⁻¹' F) F) ≤ ENNReal.ofReal (C * ‖h‖) := by
  intro N F R C hF hdiv h hh
  -- `F_h = (· + h)⁻¹ F` is null-measurable, since `y ↦ y + h` preserves `Lᴺ`.
  have hA : NullMeasurableSet ((fun y ↦ y + h) ⁻¹' F) volume :=
    hF.preimage (measurePreserving_add_right volume h).quasiMeasurePreserving
  -- Step 4. `Lᴺ(B_R(0) ∩ (F_h Δ F)) = ofReal ∫_{B_R(0)} |w|` with `w = 1_F(· + h) - 1_F`,
  -- because `1_{F_h}(y) = 1_F(y + h)`. It remains to show `∫_{B_R(0)} |w| ≤ C |h|`.
  rw [Submission.indCompact_transEst_volume_symmDiff_eq_integral N _ F R hA hF]
  apply ENNReal.ofReal_le_ofReal
  have hw : ∀ y, ((fun y ↦ y + h) ⁻¹' F).indicator (1 : Rn N → ℝ) y
      = F.indicator (1 : Rn N → ℝ) (y + h) := fun y ↦ rfl
  simp only [hw]
  -- Step 6. `L¹` duality on `B_R(0)` with `M = C |h|`.
  apply Submission.indCompact_ball_integral_abs_le_of_test_bound N
    (fun y ↦ F.indicator (1 : Rn N → ℝ) (y + h) - F.indicator (1 : Rn N → ℝ) y) R (C * ‖h‖)
  · -- `w` is a.e.-strongly measurable with `|w| ≤ 1`, and `Lᴺ(B_R(0)) < ∞`.
    refine Measure.integrableOn_of_bounded (M := 1) measure_ball_lt_top.ne ?_ ?_
    · have h1 : AEStronglyMeasurable (fun y ↦ F.indicator (1 : Rn N → ℝ) (y + h)) volume :=
        (aestronglyMeasurable_const (b := (1 : ℝ))).indicator₀ hA
      have h2 : AEStronglyMeasurable (fun y ↦ F.indicator (1 : Rn N → ℝ) y) volume :=
        (aestronglyMeasurable_const (b := (1 : ℝ))).indicator₀ hF
      exact h1.sub h2
    · refine Eventually.of_forall fun y ↦ ?_
      by_cases h1 : y + h ∈ F <;> by_cases h2 : y ∈ F <;> simp [h1, h2]
  · -- Step 5. Fix a `C¹` test function `ψ` with compact support in `B_R(0)` and `|ψ| ≤ 1`.
    intro ψ hψ hψs hψsub hψ1
    -- (a) translation invariance and (b), (d) the fundamental theorem of calculus and Fubini:
    -- `∫ w ψ = ∫_F (ψ(z - h) - ψ(z)) dz = -∫_0^1 ∫_F Dψ(z - t h)[h] dz dt`.
    rw [Submission.indCompact_transEst_integral_indicator_shift_mul N F ψ h hF
        (hψ.continuous.integrable_of_hasCompactSupport hψs),
      Submission.indCompact_transEst_setIntegral_shift_sub_ftc N F ψ h hψ hψs]
    -- (c) for `t ∈ (0, 1]`, `‖t h‖ ≤ 1`, so `|∫_F Dψ(z - t h)[h] dz| ≤ C |h|`; (e) integrate.
    have hb : ‖∫ t in (0 : ℝ)..1, ∫ z in F, fderiv ℝ ψ (z - t • h) h‖ ≤ C * ‖h‖ * |1 - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Real.norm_eq_abs]
      apply Submission.indCompact_transEst_abs_setIntegral_fderiv_le N F R C hdiv ψ hψ hψs hψsub
        hψ1 (t • h) h
      rw [Set.uIoc_of_le zero_le_one] at ht
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      nlinarith [ht.2, norm_nonneg h]
    rw [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at hb
    linarith [neg_le_abs (∫ t in (0 : ℝ)..1, ∫ z in F, fderiv ℝ ψ (z - t • h) h)]
/-- **L¹ mollification error of an indicator** (Step 2 of the supplied proof that translation
estimates and uniformly Cauchy mollifications give local Cauchy in measure, part of the
compactness of indicators used for De Giorgi's theorem, Simon Ch. 3, Theorem 4.3; cf. the
mollification argument in the proof of Simon Ch. 2, Theorem 2.6). Let `F ⊆ ℝᴺ` be
`Lᴺ`-measurable and `ρ ≥ 0` continuous with `∫ ρ = 1` and support in `B̄_σ(0)`. If
`Lᴺ(B_R ∩ (F_h Δ F)) ≤ C|h|` for all `|h| ≤ σ`, where `F_h = {y : y + h ∈ F}` and `C ≥ 0`, then
`∫_{B_R} |∫_F ρ(y - z) dz - χ_F(y)| dy ≤ σ C`. -/
theorem Submission.indCompact_mollCauchy_l1_error : ∀ (N : ℕ) (F : Set (Rn N)) (ρ : Rn N → ℝ) (σ R C : ℝ), NullMeasurableSet F volume → Continuous ρ → HasCompactSupport ρ → (∀ y, 0 ≤ ρ y) → ∫ y, ρ y = 1 → Function.support ρ ⊆ Metric.closedBall (0 : Rn N) σ → 0 ≤ C → (∀ h : Rn N, ‖h‖ ≤ σ → volume (Metric.ball (0 : Rn N) R ∩ symmDiff ((fun y ↦ y + h) ⁻¹' F) F) ≤ ENNReal.ofReal (C * ‖h‖)) → ∫⁻ y in Metric.ball (0 : Rn N) R, ENNReal.ofReal |(∫ z in F, ρ (y - z)) - F.indicator (fun _ ↦ (1 : ℝ)) y| ≤ ENNReal.ofReal (σ * C) := by
  intro N F ρ σ R C hF hρc hρs hρ0 hρ1 hsupp hC htr
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have hρm : Measurable ρ := hρc.measurable
  -- Step 1: replace `F` by its measurable hull `F'`.
  set F' := toMeasurable volume F
  have hF'm : MeasurableSet F' := measurableSet_toMeasurable _ _
  have hae : F' =ᵐ[volume] F := hF.toMeasurable_ae_eq
  have hind : F'.indicator (fun _ ↦ (1 : ℝ)) =ᵐ[volume] F.indicator (fun _ ↦ (1 : ℝ)) :=
    indicator_ae_eq_of_ae_eq_set hae
  have htr' : ∀ h : Rn N, ‖h‖ ≤ σ → volume (Metric.ball (0 : Rn N) R ∩
      symmDiff ((fun y ↦ y + h) ⁻¹' F') F') ≤ ENNReal.ofReal (C * ‖h‖) := by
    intro h hh
    have hpre : (fun y ↦ y + h) ⁻¹' F' =ᵐ[volume] (fun y ↦ y + h) ⁻¹' F :=
      (measurePreserving_add_right volume h).quasiMeasurePreserving.preimage_ae_eq hae
    rw [measure_congr (ae_eq_set_inter (EventuallyEq.refl _ _) (ae_eq_set_symmDiff hpre hae))]
    exact htr h hh
  have hcongr : ∫⁻ y in Metric.ball (0 : Rn N) R,
      ENNReal.ofReal |(∫ z in F, ρ (y - z)) - F.indicator (fun _ ↦ (1 : ℝ)) y| =
      ∫⁻ y in Metric.ball (0 : Rn N) R,
        ENNReal.ofReal |(∫ z in F', ρ (y - z)) - F'.indicator (fun _ ↦ (1 : ℝ)) y| := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hind] with y hy
    rw [setIntegral_congr_set hae, hy]
  rw [hcongr]
  clear_value F'
  clear hcongr htr hind hae hF
  set χ : Rn N → ℝ := F'.indicator (fun _ ↦ (1 : ℝ)) with hχ
  set B := Metric.ball (0 : Rn N) R with hB
  have hχm : Measurable χ := measurable_const.indicator hF'm
  have hχb : ∀ x, |χ x| ≤ 1 := by
    intro x; by_cases hx : x ∈ F' <;> simp [hχ, hx]
  have hχd : ∀ x x', |χ x - χ x'| ≤ 1 := by
    intro x x'; by_cases hx : x ∈ F' <;> by_cases hx' : x' ∈ F' <;> simp [hχ, hx, hx']
  -- Step 3: pointwise bound.
  have hpt : ∀ y, ENNReal.ofReal |(∫ z in F', ρ (y - z)) - χ y| ≤
      ∫⁻ h, ENNReal.ofReal (ρ h) * ENNReal.ofReal |χ (y - h) - χ y| := by
    intro y
    have h1 : (∫ z in F', ρ (y - z)) = ∫ h, ρ h * χ (y - h) := by
      rw [← integral_indicator hF'm]
      have : (fun z ↦ F'.indicator (fun z ↦ ρ (y - z)) z) =
          fun z ↦ (fun h ↦ ρ h * χ (y - h)) (y - z) := by
        ext z
        by_cases hz : z ∈ F' <;> simp [hχ, hz]
      rw [this, integral_sub_left_eq_self (fun h ↦ ρ h * χ (y - h)) volume y]
    have hint1 : Integrable (fun h ↦ ρ h * χ (y - h)) := by
      refine hρi.mono' (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun h ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 h)]
      exact mul_le_of_le_one_right (hρ0 h) (hχb _)
    have h3 : (∫ z in F', ρ (y - z)) - χ y = ∫ h, ρ h * (χ (y - h) - χ y) := by
      have e : (fun h ↦ ρ h * (χ (y - h) - χ y)) = fun h ↦ ρ h * χ (y - h) - ρ h * χ y := by
        ext h; ring
      rw [e, integral_sub hint1 (hρi.mul_const _), integral_mul_const, hρ1, one_mul, h1]
    have hint3 : Integrable (fun h ↦ ρ h * |χ (y - h) - χ y|) := by
      refine hρi.mono' (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun h ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 h), abs_abs]
      exact mul_le_of_le_one_right (hρ0 h) (hχd _ _)
    rw [h3]
    calc ENNReal.ofReal |∫ h, ρ h * (χ (y - h) - χ y)|
        ≤ ENNReal.ofReal (∫ h, |ρ h * (χ (y - h) - χ y)|) :=
          ENNReal.ofReal_le_ofReal abs_integral_le_integral_abs
      _ = ENNReal.ofReal (∫ h, ρ h * |χ (y - h) - χ y|) := by
          congr 2; ext h; rw [abs_mul, abs_of_nonneg (hρ0 h)]
      _ = ∫⁻ h, ENNReal.ofReal (ρ h * |χ (y - h) - χ y|) :=
          ofReal_integral_eq_lintegral_ofReal hint3
            (ae_of_all _ fun h ↦ mul_nonneg (hρ0 h) (abs_nonneg _))
      _ = ∫⁻ h, ENNReal.ofReal (ρ h) * ENNReal.ofReal |χ (y - h) - χ y| := by
          congr 1; ext h; rw [ENNReal.ofReal_mul (hρ0 h)]
  -- Steps 4–6: Tonelli, inner integral, conclusion.
  calc ∫⁻ y in B, ENNReal.ofReal |(∫ z in F', ρ (y - z)) - χ y|
      ≤ ∫⁻ y in B, ∫⁻ h, ENNReal.ofReal (ρ h) * ENNReal.ofReal |χ (y - h) - χ y| :=
        lintegral_mono hpt
    _ = ∫⁻ h, ∫⁻ y in B, ENNReal.ofReal (ρ h) * ENNReal.ofReal |χ (y - h) - χ y| := by
        apply lintegral_lintegral_swap
        apply Measurable.aemeasurable
        fun_prop
    _ ≤ ∫⁻ h, ENNReal.ofReal (ρ h) * ENNReal.ofReal (σ * C) := by
        refine lintegral_mono fun h ↦ ?_
        dsimp only
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        by_cases hρh : ρ h = 0
        · simp [hρh]
        · gcongr
          have hnorm : ‖h‖ ≤ σ := by
            have := hsupp hρh
            simpa [Metric.mem_closedBall, dist_zero_right] using this
          have hmeas : MeasurableSet (symmDiff ((fun y ↦ y + -h) ⁻¹' F') F') :=
            (measurable_add_const (-h) hF'm).symmDiff hF'm
          have hset : ∀ y, ENNReal.ofReal |χ (y - h) - χ y| =
              (symmDiff ((fun y ↦ y + -h) ⁻¹' F') F').indicator 1 y := by
            intro y
            by_cases h1 : y - h ∈ F' <;> by_cases h2 : y ∈ F' <;>
              simp [hχ, h1, h2, Set.mem_symmDiff, ← sub_eq_add_neg]
          simp_rw [hset]
          rw [lintegral_indicator_one hmeas, Measure.restrict_apply hmeas, Set.inter_comm]
          calc volume (B ∩ symmDiff ((fun y ↦ y + -h) ⁻¹' F') F')
              ≤ ENNReal.ofReal (C * ‖-h‖) := htr' (-h) (by rwa [norm_neg])
            _ ≤ ENNReal.ofReal (σ * C) := by
              apply ENNReal.ofReal_le_ofReal
              rw [norm_neg, mul_comm]
              exact mul_le_mul_of_nonneg_right hnorm hC
    _ = (∫⁻ h, ENNReal.ofReal (ρ h)) * ENNReal.ofReal (σ * C) :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (σ * C) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hρi (ae_of_all _ hρ0), hρ1, ENNReal.ofReal_one,
          one_mul]
/-- **Continuity of the mollified set integral** (Step 1 of the supplied proof that translation
estimates and uniformly Cauchy mollifications give local Cauchy in measure, part of the
compactness of indicators used for De Giorgi's theorem, Simon Ch. 3, Theorem 4.3; cf. the
mollification argument in the proof of Simon Ch. 2, Theorem 2.6). For an arbitrary `F ⊆ ℝᴺ` and a
continuous, compactly supported `ρ`, the map `y ↦ ∫_F ρ(y - z) dz` is continuous: it is the
convolution of `1` with `ρ` for the locally finite measure `Lᴺ ⌞ F`. -/
theorem Submission.indCompact_mollCauchy_setIntegral_continuous : ∀ (N : ℕ) (F : Set (Rn N)) (ρ : Rn N → ℝ), Continuous ρ → HasCompactSupport ρ → Continuous (fun y : Rn N ↦ ∫ z in F, ρ (y - z)) := by
  intro N F ρ hρ hρc
  -- `y ↦ ∫_F ρ(y - z) dz` is the convolution of `1` with `ρ` for the measure `volume.restrict F`.
  have hconv : (fun y : Rn N ↦ ∫ z in F, ρ (y - z)) =
      convolution (fun _ ↦ (1 : ℝ)) ρ (ContinuousLinearMap.lsmul ℝ ℝ) (volume.restrict F) := by
    ext y
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, one_smul]
  rw [hconv]
  -- `volume.restrict F` is locally finite for every `F`, so the constant `1` is locally
  -- integrable; convolving with the continuous, compactly supported `ρ` gives a continuous map.
  exact hρc.continuous_convolution_right _ (locallyIntegrable_const 1) hρ

/-- **Translation estimates and uniformly Cauchy mollifications give local Cauchy in measure**
(Steps 3 and 6 of the supplied proof of the compactness of indicators used for De Giorgi's theorem,
Simon Ch. 3, Theorem 4.3; cf. the mollification argument in the proof of Simon Ch. 2,
Theorem 2.6). Let `ρ_m ≥ 0` be continuous kernels with `∫ ρ_m = 1` and support in
`B̄_{1/(m+1)}(0)`, and `v_{m,k}(y) = ∫_{F_k} ρ_m(y - z) dz`. If the `F_k` satisfy a uniform local
translation estimate `Lᴺ(B_R ∩ ((F_k)_h Δ F_k)) ≤ C_R |h|` and, for each `m`, the `v_{m,k}` are
uniformly Cauchy on `B̄_m(0)`, then `Lᴺ(B_R ∩ (F_k Δ F_l)) → 0`: on `B_R ⊆ B̄_m(0)`,
`1_{F_k Δ F_l} ≤ |v_{m,k} - 1_{F_k}| + |v_{m,k} - v_{m,l}| + |v_{m,l} - 1_{F_l}|`, and the outer
terms have `L¹(B_R)`-norm at most `C_R / (m + 1)`. -/
theorem Submission.indCompact_local_cauchy_of_mollified_cauchy : ∀ (N : ℕ) (F : ℕ → Set (Rn N)) (ρ : ℕ → Rn N → ℝ), (∀ k, NullMeasurableSet (F k) volume) → (∀ m, Continuous (ρ m)) → (∀ m, HasCompactSupport (ρ m)) → (∀ m y, 0 ≤ ρ m y) → (∀ m, ∫ y, ρ m y = 1) → (∀ m, Function.support (ρ m) ⊆ Metric.closedBall (0 : Rn N) (1 / ((m : ℝ) + 1))) → (∀ R : ℕ, ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ h : Rn N, ‖h‖ ≤ 1 → volume (Metric.ball (0 : Rn N) R ∩ symmDiff ((fun y ↦ y + h) ⁻¹' F k) (F k)) ≤ ENNReal.ofReal (C * ‖h‖)) → (∀ (m : ℕ) (ε : ℝ), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ l ≥ k₀, ∀ y ∈ Metric.closedBall (0 : Rn N) m, |(∫ z in F k, ρ m (y - z)) - ∫ z in F l, ρ m (y - z)| ≤ ε) → ∀ (R : ℕ) (ε : ℝ≥0∞), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ l ≥ k₀, volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) (F l)) ≤ ε := by
  intro N F ρ hF hρc hρs hρ0 hρ1 hρsupp htrans hcauchy R ε hε
  -- For `ε = ∞` any `k₀` works; otherwise put `e := ε.toReal > 0`, so that `ε = ofReal e`.
  rcases eq_or_ne ε ∞ with rfl | hε_top
  · exact ⟨0, fun _ _ _ _ ↦ le_top⟩
  set e := ε.toReal
  have he : 0 < e := ENNReal.toReal_pos hε.ne' hε_top
  have hεe : ε = ENNReal.ofReal e := (ENNReal.ofReal_toReal hε_top).symm
  -- (a) The translation estimate on `B_R`, with the nonnegative constant `C' := max C 0`.
  obtain ⟨C, k₁, hC⟩ := htrans R
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  -- (b) A kernel index `m ≥ R` with `σ_m C' ≤ e / 4`, where `σ_m := 1 / (m + 1) ≤ 1`.
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (4 * C' / e)
  set m := max m₀ R
  have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hσ_le : 1 / ((m : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hm_pos]
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hσC : 1 / ((m : ℝ) + 1) * C' ≤ e / 4 := by
    have hm₀m : (m₀ : ℝ) ≤ m := by exact_mod_cast le_max_left m₀ R
    have h4 : 4 * C' / e < (m : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ he] at h4
    rw [one_div_mul_eq_div, div_le_iff₀ hm_pos]
    linarith
  have hRm : Metric.ball (0 : Rn N) R ⊆ Metric.closedBall (0 : Rn N) m :=
    Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by exact_mod_cast le_max_right m₀ R))
  -- (c) The uniform Cauchy property of `v_{m,·}` on `B̄_m(0)` with `η := e / (2 (Lᴺ(B_R) + 1))`.
  set V := (volume (Metric.ball (0 : Rn N) R)).toReal with hV_def
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  set η := e / (2 * (V + 1)) with hη_def
  have hη : 0 < η := by positivity
  have hηV : η * V ≤ e / 2 := by
    rw [hη_def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨k₂, hk₂⟩ := hcauchy m η hη
  refine ⟨max k₁ k₂, fun k hk l hl ↦ ?_⟩
  -- Step 2 (mollification error): `∫⁻_{B_R} |v_{m,j} - 1_{F_j}| ≤ σ_m C' ≤ e / 4` for `j ≥ k₁`.
  have herr : ∀ j ≥ k₁, ∫⁻ y in Metric.ball (0 : Rn N) R,
      ENNReal.ofReal |(∫ z in F j, ρ m (y - z)) - (F j).indicator (fun _ ↦ (1 : ℝ)) y| ≤
        ENNReal.ofReal (e / 4) := by
    intro j hj
    refine (Submission.indCompact_mollCauchy_l1_error N (F j) (ρ m) (1 / ((m : ℝ) + 1)) R C'
      (hF j) (hρc m) (hρs m) (hρ0 m) (hρ1 m) (hρsupp m) hC' fun h hh ↦ ?_).trans
        (ENNReal.ofReal_le_ofReal hσC)
    exact (hC j hj h (hh.trans hσ_le)).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg h)))
  -- Step 1: each `v_{m,j}` is continuous and `F_j` is null-measurable, so the error terms are
  -- a.e.-measurable and `∫⁻` is additive on them.
  have hmeas : ∀ j, AEMeasurable (fun y ↦
      ENNReal.ofReal |(∫ z in F j, ρ m (y - z)) - (F j).indicator (fun _ ↦ (1 : ℝ)) y|)
      (volume.restrict (Metric.ball (0 : Rn N) R)) := by
    intro j
    have hv : AEMeasurable (fun y : Rn N ↦ ∫ z in F j, ρ m (y - z)) volume :=
      (Submission.indCompact_mollCauchy_setIntegral_continuous N (F j) (ρ m) (hρc m)
        (hρs m)).measurable.aemeasurable
    have hχ : AEMeasurable ((F j).indicator (fun _ ↦ (1 : ℝ))) volume :=
      aemeasurable_const.indicator₀ (hF j)
    exact (continuous_abs.measurable.comp_aemeasurable (hv.sub hχ)).ennreal_ofReal.restrict
  -- (d) For `y ∈ B_R ⊆ B̄_m(0)`:
  -- `1_{F_k Δ F_l}(y) ≤ |v_{m,k}(y) - 1_{F_k}(y)| + η + |v_{m,l}(y) - 1_{F_l}(y)|`.
  have hpt : ∀ y ∈ Metric.ball (0 : Rn N) R, (symmDiff (F k) (F l)).indicator 1 y ≤
      ENNReal.ofReal |(∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y| +
        ENNReal.ofReal η +
          ENNReal.ofReal |(∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y| := by
    intro y hy
    have hvkl := hk₂ k (le_of_max_le_right hk) l (le_of_max_le_right hl) y (hRm hy)
    refine Set.indicator_apply_le' (fun hyD ↦ ?_) (fun _ ↦ zero_le)
    have h1 : |(F k).indicator (fun _ ↦ (1 : ℝ)) y - (F l).indicator (fun _ ↦ (1 : ℝ)) y| = 1 := by
      rcases Set.mem_symmDiff.mp hyD with ⟨hk', hl'⟩ | ⟨hl', hk'⟩ <;> simp [hk', hl']
    have h2 : |(F k).indicator (fun _ ↦ (1 : ℝ)) y - (F l).indicator (fun _ ↦ (1 : ℝ)) y| ≤
        |(∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y| + η +
          |(∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y| := by
      rw [abs_le] at hvkl ⊢
      constructor <;>
        linarith [le_abs_self ((∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y),
          neg_abs_le ((∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y),
          le_abs_self ((∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y),
          neg_abs_le ((∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y)]
    rw [h1] at h2
    calc (1 : Rn N → ℝ≥0∞) y = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (|(∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y| + η +
            |(∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y|) :=
          ENNReal.ofReal_le_ofReal h2
      _ ≤ _ := ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
  -- (e) Integrate over `B_R`: `Lᴺ(B_R ∩ (F_k Δ F_l)) ≤ e / 4 + η Lᴺ(B_R) + e / 4 ≤ e`.
  have hconst : ∫⁻ _ in Metric.ball (0 : Rn N) R, ENNReal.ofReal η ≤ ENNReal.ofReal (e / 2) := by
    rw [setLIntegral_const, ← ENNReal.ofReal_toReal (measure_ball_lt_top (μ := volume)).ne,
      ← hV_def, ← ENNReal.ofReal_mul hη.le]
    exact ENNReal.ofReal_le_ofReal hηV
  calc volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) (F l))
      = ∫⁻ y in Metric.ball (0 : Rn N) R, (symmDiff (F k) (F l)).indicator 1 y := by
        rw [lintegral_indicator_one₀
            (((hF k).symmDiff (hF l)).mono_ac Measure.absolutelyContinuous_restrict),
          Measure.restrict_apply' measurableSet_ball, Set.inter_comm]
    _ ≤ ∫⁻ y in Metric.ball (0 : Rn N) R,
          (ENNReal.ofReal |(∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y| +
            ENNReal.ofReal η +
              ENNReal.ofReal |(∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y|) :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = (∫⁻ y in Metric.ball (0 : Rn N) R,
          ENNReal.ofReal |(∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y|) +
        (∫⁻ _ in Metric.ball (0 : Rn N) R, ENNReal.ofReal η) +
          ∫⁻ y in Metric.ball (0 : Rn N) R,
            ENNReal.ofReal |(∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y| := by
        rw [lintegral_add_right' _ (hmeas l), lintegral_add_right' _ aemeasurable_const]
    _ ≤ ENNReal.ofReal (e / 4) + ENNReal.ofReal (e / 2) + ENNReal.ofReal (e / 4) :=
        add_le_add (add_le_add (herr k (le_of_max_le_left hk)) hconst)
          (herr l (le_of_max_le_left hl))
    _ = ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), hεe]
        congr 1
        ring
/-- **Diagonal Arzelà–Ascoli extraction for mollified sets** (Steps 4–5 of the mollification
proof of Simon Ch. 2, Thm. 2.6, with arbitrary continuous compactly supported kernels `ρₘ`): for
arbitrary sets `Fₖ ⊆ ℝᴺ` some subsequence `φ` makes every `y ↦ ∫_{F_{φ(k)}} ρₘ(y - z) dz`
uniformly Cauchy on `B̄ₘ(0)`. Only `Lᴺ ⌞ S ≤ Lᴺ` is used, so these functions are bounded by
`Mₘ Lᴺ(B̄_{Rₘ}(0))` and equicontinuous uniformly in `S`. Tychonoff in the countable product
`∏_{(m, d) ∈ ℕ × D}` (`D` countable dense) gives `φ` with convergence at every `(m, d)`;
equicontinuity and a finite cover of `B̄ₘ(0)` by balls centred in `D` upgrade this to the uniform
Cauchy property. -/
theorem Submission.indCompact_diagonal_mollified_uniform_cauchy : ∀ (N : ℕ) (ρ : ℕ → Rn N → ℝ)
    (F : ℕ → Set (Rn N)), (∀ m, Continuous (ρ m)) → (∀ m, HasCompactSupport (ρ m)) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ (m : ℕ) (ε : ℝ), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ l ≥ k₀,
      ∀ y ∈ Metric.closedBall (0 : Rn N) m,
        |(∫ z in F (φ k), ρ m (y - z)) - ∫ z in F (φ l), ρ m (y - z)| ≤ ε := by
  intro N ρ F hc hs
  -- A function bounded by `C` and vanishing off `B̄_r(c)` has `|∫_S f| ≤ C Lᴺ(B̄_r(0))` for every
  -- set `S`, since `Lᴺ ⌞ S ≤ Lᴺ`.
  have key : ∀ (S : Set (Rn N)) (c : Rn N) (r C : ℝ) (f : Rn N → ℝ), (∀ z, ‖f z‖ ≤ C) →
      (∀ z, f z ≠ 0 → z ∈ Metric.closedBall c r) →
      |∫ z in S, f z| ≤ C * (volume (Metric.closedBall (0 : Rn N) r)).toReal := by
    intro S c r C f hfC hfs
    have hC : 0 ≤ C := (norm_nonneg _).trans (hfC 0)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (f := f) (s := Metric.closedBall c r)
      (μ := volume.restrict S) (fun z hz => not_not.1 (mt (hfs z) hz)), ← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le_const
      ((Measure.restrict_apply_le _ _).trans_lt measure_closedBall_lt_top)
      (fun z _ => hfC z)).trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [Measure.real, ← Measure.addHaar_closedBall_center volume c r]
    exact ENNReal.toReal_mono measure_closedBall_lt_top.ne (Measure.restrict_apply_le _ _)
  -- Support radius `Rₘ` and sup bound `Mₘ` of each kernel.
  have hR : ∀ m, ∃ R : ℝ, ∀ x, ρ m x ≠ 0 → ‖x‖ ≤ R := by
    intro m
    obtain ⟨R, hR⟩ := (hs m).isCompact.isBounded.subset_closedBall 0
    exact ⟨R, fun x hx => by simpa using hR (subset_tsupport _ hx)⟩
  choose R hR using hR
  choose M hM using fun m => (hc m).bounded_above_of_compact_support (hs m)
  -- Uniform bound: `|∫_S ρₘ(y - z) dz| ≤ Mₘ Lᴺ(B̄_{Rₘ}(0))`.
  have hbd : ∀ (m : ℕ) (S : Set (Rn N)) (y : Rn N),
      |∫ z in S, ρ m (y - z)| ≤ M m * (volume (Metric.closedBall (0 : Rn N) (R m))).toReal := by
    intro m S y
    refine key S y (R m) (M m) (fun z => ρ m (y - z)) (fun z => hM m _) (fun z hz => ?_)
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
    exact hR m _ hz
  have hint : ∀ (m : ℕ) (y : Rn N) (S : Set (Rn N)),
      Integrable (fun z => ρ m (y - z)) (volume.restrict S) := fun m y S =>
    (((hc m).integrable_of_hasCompactSupport (hs m)).comp_sub_left y).restrict
  -- Equicontinuity, uniformly in the set `S`.
  have heq : ∀ (m : ℕ) (η : ℝ), 0 < η → ∃ δ > 0, ∀ (S : Set (Rn N)) (y y' : Rn N), dist y y' < δ →
      |(∫ z in S, ρ m (y - z)) - ∫ z in S, ρ m (y' - z)| ≤ η := by
    intro m η hη
    obtain ⟨V, hV0, hV⟩ : ∃ V, 0 ≤ V ∧
        (volume (Metric.closedBall (0 : Rn N) (R m + 1))).toReal = V :=
      ⟨_, ENNReal.toReal_nonneg, rfl⟩
    have hV1 : 0 < V + 1 := by linarith
    obtain ⟨δ, hδ, hδρ⟩ := Metric.uniformContinuous_iff.1
      ((hs m).uniformContinuous_of_continuous (hc m)) (η / (V + 1)) (div_pos hη hV1)
    refine ⟨min δ 1, lt_min hδ one_pos, fun S y y' hyy' => ?_⟩
    rw [← integral_sub (hint m y S) (hint m y' S)]
    refine (key S y (R m + 1) (η / (V + 1)) (fun z => ρ m (y - z) - ρ m (y' - z)) (fun z => ?_)
      (fun z hz => ?_)).trans ?_
    · show ‖ρ m (y - z) - ρ m (y' - z)‖ ≤ _
      rw [← dist_eq_norm]
      have hd : dist (y - z) (y' - z) < δ := by
        rw [dist_sub_right]; exact hyy'.trans_le (min_le_left _ _)
      exact (hδρ hd).le
    · have hz' : ρ m (y - z) - ρ m (y' - z) ≠ 0 := hz
      rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
      by_cases h : ρ m (y - z) = 0
      · have h' : ρ m (y' - z) ≠ 0 := fun h' => hz' (by rw [h, h', sub_self])
        have h'' := hR m _ h'
        have hyy1 : ‖y - y'‖ < 1 := by
          rw [← dist_eq_norm]; exact hyy'.trans_le (min_le_right _ _)
        calc ‖y - z‖ = ‖(y - y') + (y' - z)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖y - y'‖ + ‖y' - z‖ := norm_add_le _ _
          _ ≤ R m + 1 := by linarith
      · linarith [hR m _ h]
    · rw [hV]
      calc η / (V + 1) * V ≤ η / (V + 1) * (V + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (div_pos hη hV1).le
        _ = η := div_mul_cancel₀ _ hV1.ne'
  -- Tychonoff on the countable product indexed by `ℕ × D`, `D` countable dense.
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Rn N)
  have : Countable D := hDc.to_subtype
  have hK : IsCompact (Set.pi univ fun p : ℕ × D =>
      Icc (-(M p.1 * (volume (Metric.closedBall (0 : Rn N) (R p.1))).toReal))
        (M p.1 * (volume (Metric.closedBall (0 : Rn N) (R p.1))).toReal)) :=
    isCompact_univ_pi fun p => isCompact_Icc
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq
    (x := fun k (p : ℕ × D) => ∫ z in F k, ρ p.1 ((p.2 : Rn N) - z))
    fun k => Set.mem_univ_pi.2 fun p => abs_le.1 (hbd p.1 (F k) p.2)
  refine ⟨φ, hφ, fun m ε hε => ?_⟩
  obtain ⟨δ, hδ, hδV⟩ := heq m (ε / 3) (by positivity)
  -- Finitely many `δ`-balls centred in `D` cover `B̄ₘ(0)`.
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : Rn N) (m : ℝ)).elim_finite_subcover
    (fun d : D => Metric.ball (d : Rn N) δ) (fun _ => Metric.isOpen_ball) fun y _ => by
      obtain ⟨d, hd, hyd⟩ := hDd.exists_dist_lt y hδ
      exact mem_iUnion.2 ⟨⟨d, hd⟩, hyd⟩
  have hev : ∀ᶠ k in atTop, ∀ d ∈ t,
      dist (∫ z in F (φ k), ρ m ((d : Rn N) - z)) (a (m, d)) < ε / 6 :=
    (eventually_all_finset t).2 fun d _ =>
      Metric.tendsto_nhds.1 (tendsto_pi_nhds.1 hlim (m, d)) (ε / 6) (by positivity)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hev
  refine ⟨k₀, fun k hk l hl y hy => ?_⟩
  obtain ⟨d, hdt, hyd⟩ := mem_iUnion₂.1 (ht hy)
  have h1 := hδV (F (φ k)) y d hyd
  have h2 := hδV (F (φ l)) y d hyd
  have h3 := hk₀ k hk d hdt
  have h4 := hk₀ l hl d hdt
  rw [Real.dist_eq] at h3 h4
  rw [abs_le] at h1 h2 ⊢
  rw [abs_lt] at h3 h4
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
/-- **Local `L¹` Cauchy sequences of sets have a local limit**: the completeness step of the
compactness theorem (Simon Ch. 2, Thm. 2.6) for characteristic functions, as used in the proof of
Ch. 3, Thm. 4.3. If for every `R ∈ ℕ` the sets `F k` are Cauchy in measure on `B_R(0)`, i.e.
`|B_R(0) ∩ (F_k Δ F_l)| → 0` as `k, l → ∞`, then some measurable `G` has `|K ∩ (F_k Δ G)| → 0`
for every compact `K`. Riesz–Fischer argument: choose `n_j ≥ k₀(j)` monotone, where
`|B_j ∩ (F_k Δ F_l)| ≤ 2⁻ʲ` for `k, l ≥ k₀(j)`, and put `G₀ = ⋃ᵢ ⋂_{j ≥ i} F_{n_j}`. Then
`F_{n_i} Δ G₀ ⊆ ⋃_{j ≥ i} (F_{n_j} Δ F_{n_{j+1}})`, so `|B_R ∩ (F_{n_i} Δ G₀)| ≤ 2 · 2⁻ⁱ` for
`i ≥ R`, and by the triangle inequality for `Δ`, `|B_R ∩ (F_k Δ G₀)| ≤ 3 · 2⁻ⁱ` for `k ≥ n_i`.
These estimates only use outer measure; `G` is a measurable hull of the null-measurable set `G₀`,
and every compact `K` lies in some `B_R`. -/
theorem Submission.indCompact_limit_of_local_cauchy : ∀ (N : ℕ) (F : ℕ → Set (Rn N)),
    (∀ k, NullMeasurableSet (F k) volume) →
    (∀ (R : ℕ) (ε : ℝ≥0∞), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ l ≥ k₀,
      volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) (F l)) ≤ ε) →
    ∃ G : Set (Rn N), MeasurableSet G ∧ ∀ K : Set (Rn N), IsCompact K →
      Tendsto (fun k ↦ volume (K ∩ symmDiff (F k) G)) atTop (𝓝 0) := by
  intro N F hF hC
  -- Fast subsequence: `k₀ j` is a Cauchy index for `R = j`, `ε = 2⁻ʲ`; `n` is monotone, `n ≥ k₀`.
  choose k₀ hk₀ using fun j : ℕ ↦ hC j ((2 : ℝ≥0∞)⁻¹ ^ j) (ENNReal.pow_pos (by simp) j)
  obtain ⟨n, hn_ge, hn_mono⟩ : ∃ n : ℕ → ℕ, (∀ j, k₀ j ≤ n j) ∧ Monotone n :=
    ⟨fun j ↦ (Finset.range (j + 1)).sup k₀, fun j ↦ Finset.le_sup (Finset.self_mem_range_succ j),
      fun i j hij ↦ Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ hij))⟩
  have hstep : ∀ j : ℕ, volume (Metric.ball (0 : Rn N) j ∩ symmDiff (F (n j)) (F (n (j + 1)))) ≤
      (2 : ℝ≥0∞)⁻¹ ^ j := fun j ↦
    hk₀ j _ (hn_ge j) _ ((hn_ge j).trans (hn_mono (Nat.le_succ j)))
  -- The limit set `G₀ = ⋃ᵢ ⋂_{j ≥ i} F (n j)`.
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : Set (Rn N), G₀ = ⋃ i, ⋂ j ≥ i, F (n j) := ⟨_, rfl⟩
  have hmem : ∀ y, y ∈ G₀ ↔ ∃ i, ∀ j ≥ i, y ∈ F (n j) := fun y ↦ by
    simp only [hG₀, mem_iUnion, mem_iInter]
  -- Tail inclusion: `F (n i) Δ G₀ ⊆ ⋃_{j ≥ i} (F (n j) Δ F (n (j + 1)))`.
  have htail : ∀ i, symmDiff (F (n i)) G₀ ⊆
      ⋃ m : ℕ, symmDiff (F (n (i + m))) (F (n (i + m + 1))) := by
    intro i y hy
    by_contra hcon
    simp only [mem_iUnion, not_exists] at hcon
    have hiff : ∀ m, (y ∈ F (n (i + m)) ↔ y ∈ F (n i)) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have h := hcon m
        rw [mem_symmDiff] at h
        rw [← ih, ← add_assoc]
        tauto
    rw [mem_symmDiff, hmem] at hy
    rcases hy with ⟨hyA, hyG⟩ | ⟨⟨i', hi'⟩, hyA⟩
    · refine hyG ⟨i, fun j hj ↦ ?_⟩
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
      exact (hiff m).2 hyA
    · exact hyA ((hiff i').1 (hi' (i + i') (Nat.le_add_left i' i)))
  -- Along the subsequence: `|B_R ∩ (F (n i) Δ G₀)| ≤ 2⁻ⁱ · 2` for `R ≤ i`.
  have hsub : ∀ R i : ℕ, R ≤ i →
      volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F (n i)) G₀) ≤ (2 : ℝ≥0∞)⁻¹ ^ i * 2 := by
    intro R i hRi
    calc volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F (n i)) G₀)
        ≤ volume (⋃ m : ℕ, Metric.ball (0 : Rn N) ↑(i + m) ∩
            symmDiff (F (n (i + m))) (F (n (i + m + 1)))) := by
          refine measure_mono fun y hy ↦ ?_
          obtain ⟨m, hm⟩ := mem_iUnion.1 (htail i hy.2)
          refine mem_iUnion.2 ⟨m, Metric.ball_subset_ball ?_ hy.1, hm⟩
          exact_mod_cast hRi.trans (Nat.le_add_right i m)
      _ ≤ ∑' m : ℕ, volume (Metric.ball (0 : Rn N) ↑(i + m) ∩
            symmDiff (F (n (i + m))) (F (n (i + m + 1)))) := measure_iUnion_le _
      _ ≤ ∑' m : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (i + m) := ENNReal.tsum_le_tsum fun m ↦ hstep (i + m)
      _ = (2 : ℝ≥0∞)⁻¹ ^ i * 2 := by
          simp_rw [pow_add]
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  -- Whole sequence: `|B_R ∩ (F k Δ G₀)| ≤ 2⁻ⁱ + 2⁻ⁱ · 2` for `R ≤ i` and `k ≥ n i`.
  have hwhole : ∀ R i k : ℕ, R ≤ i → n i ≤ k →
      volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) G₀) ≤
        (2 : ℝ≥0∞)⁻¹ ^ i + (2 : ℝ≥0∞)⁻¹ ^ i * 2 := by
    intro R i k hRi hk
    calc volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) G₀)
        ≤ volume ((Metric.ball (0 : Rn N) i ∩ symmDiff (F k) (F (n i))) ∪
            (Metric.ball (0 : Rn N) R ∩ symmDiff (F (n i)) G₀)) := by
          refine measure_mono fun y hy ↦ ?_
          rcases symmDiff_triangle (F k) (F (n i)) G₀ hy.2 with h | h
          · exact Or.inl ⟨Metric.ball_subset_ball (by exact_mod_cast hRi) hy.1, h⟩
          · exact Or.inr ⟨hy.1, h⟩
      _ ≤ volume (Metric.ball (0 : Rn N) i ∩ symmDiff (F k) (F (n i))) +
            volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F (n i)) G₀) := measure_union_le _ _
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ i + (2 : ℝ≥0∞)⁻¹ ^ i * 2 :=
          add_le_add (hk₀ i k ((hn_ge i).trans hk) (n i) (hn_ge i)) (hsub R i hRi)
  -- Hence `|B_R ∩ (F k Δ G₀)| → 0` for every `R ∈ ℕ`.
  have hgeom : Tendsto (fun i : ℕ ↦ (2 : ℝ≥0∞)⁻¹ ^ i + (2 : ℝ≥0∞)⁻¹ ^ i * 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun i : ℕ ↦ (2 : ℝ≥0∞)⁻¹ ^ i) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
    have h2 := h1.add (ENNReal.Tendsto.mul_const h1 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞)))
    rwa [zero_mul, add_zero] at h2
  have hball : ∀ R : ℕ,
      Tendsto (fun k ↦ volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) G₀)) atTop (𝓝 0) := by
    intro R
    refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
    obtain ⟨i, hiR, hiε⟩ :=
      ((eventually_ge_atTop R).and (ENNReal.tendsto_nhds_zero.1 hgeom ε hε)).exists
    exact (eventually_ge_atTop (n i)).mono fun k hk ↦ (hwhole R i k hiR hk).trans hiε
  -- `G = toMeasurable G₀` is measurable and a.e. equal to the null-measurable `G₀`; every compact
  -- `K` lies in some `B_R`.
  have hG₀m : NullMeasurableSet G₀ volume := by
    rw [hG₀]
    exact .iUnion fun i ↦ .iInter fun j ↦ .iInter fun _ ↦ hF (n j)
  refine ⟨toMeasurable volume G₀, measurableSet_toMeasurable _ _, fun K hK ↦ ?_⟩
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Rn N)
  obtain ⟨R, hR⟩ := exists_nat_gt r
  have hKR : K ⊆ Metric.ball (0 : Rn N) R := hr.trans (Metric.ball_subset_ball hR.le)
  have heq : ∀ k, volume (K ∩ symmDiff (F k) (toMeasurable volume G₀)) =
      volume (K ∩ symmDiff (F k) G₀) := fun k ↦
    measure_congr (EventuallyEqSet.rfl.inter (EventuallyEqSet.rfl.symmDiff hG₀m.toMeasurable_ae_eq))
  refine (tendsto_congr heq).2 ?_
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hball R)
    (fun k ↦ zero_le) (fun k ↦ measure_mono (inter_subset_inter_left _ hKR))

/-- **Compactness for sets of locally bounded perimeter** (Simon Ch. 2, Thm. 2.6, for
characteristic functions, as used in the proof of Ch. 3, Thm. 4.3): if `∫_{F_k} div g ≤ C_R` for
all large `k` and all `g ∈ C¹_c(B_R(0); ℝᴺ)` with `|g| ≤ 1`, then some subsequence `F_{φ(k)}`
converges in `L¹_loc` to a measurable set `G`. Mollify with `ρₘ = bₘ / ∫ bₘ` (`bₘ` a smooth bump
with support `B_{1/(m+1)}(0)`). The diagonal Arzelà–Ascoli extraction gives `φ`. The perimeter
bound on `B_{R+1}(0)` gives translation estimates on `B_R(0)`, which together with the uniformly
Cauchy mollifications make `F_{φ(k)}` locally Cauchy in measure, so it has a measurable limit. -/
theorem Submission.deGiorgi_indicator_compactness : ∀ (N : ℕ) (F : ℕ → Set (Rn N)),
    (∀ k, NullMeasurableSet (F k) volume) →
    (∀ R : ℝ, 0 < R → ∃ C : ℝ, ∀ᶠ k in atTop, ∀ g : Rn N → Rn N, ContDiff ℝ 1 g →
      HasCompactSupport g → tsupport g ⊆ Metric.ball 0 R → (∀ y, ‖g y‖ ≤ 1) →
        ∫ y in F k, Poincare.SimonGMT.Chapter02.euclideanDivergence g y ≤ C) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : Set (Rn N), MeasurableSet G ∧
      ∀ K : Set (Rn N), IsCompact K →
        Tendsto (fun k ↦ volume (K ∩ symmDiff (F (φ k)) G)) atTop (𝓝 0) := by
  intro N F hF hbd
  -- Kernels `ρₘ := bₘ / ∫ bₘ`, `bₘ` the smooth bump at `0` with `rOut = 1/(m+1)`, `rIn = rOut/2`.
  obtain ⟨b, hbr⟩ : ∃ b : ℕ → ContDiffBump (0 : Rn N), ∀ m, (b m).rOut = 1 / ((m : ℝ) + 1) :=
    ⟨fun m => ⟨1 / ((m : ℝ) + 1) / 2, 1 / ((m : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩, fun _ => rfl⟩
  have hb : ∀ m, 0 < ∫ y, b m y := fun m =>
    (b m).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (b m).hasCompactSupport
      (fun _ => (b m).nonneg) ((b m).pos_of_mem_ball (Metric.mem_ball_self (b m).rOut_pos)).ne'
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → Rn N → ℝ, ∀ m y, ρ m y = b m y / ∫ z, b m z :=
    ⟨_, fun _ _ => rfl⟩
  have hρb : ∀ m, Function.support (ρ m) ⊆ Function.support (b m) := fun m y hy =>
    Function.mem_support.2 fun h0 => Function.mem_support.1 hy (by rw [hρ, h0, zero_div])
  have hρc : ∀ m, Continuous (ρ m) := fun m => by
    rw [show ρ m = fun y => b m y / ∫ z, b m z from funext (hρ m)]
    exact (b m).continuous.div_const _
  have hρs : ∀ m, HasCompactSupport (ρ m) := fun m => (b m).hasCompactSupport.mono (hρb m)
  -- Diagonal Arzelà–Ascoli: along `φ` the mollified sets are uniformly Cauchy on every `B̄ₘ(0)`.
  obtain ⟨φ, hφ, hcau⟩ := Submission.indCompact_diagonal_mollified_uniform_cauchy N ρ F hρc hρs
  -- Translation estimates on `B_R(0)` along `φ`, from the perimeter bound on `B_{R+1}(0)`.
  have htr : ∀ R : ℕ, ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ h : Rn N, ‖h‖ ≤ 1 →
      volume (Metric.ball (0 : Rn N) R ∩ symmDiff ((fun y ↦ y + h) ⁻¹' F (φ k)) (F (φ k))) ≤
        ENNReal.ofReal (C * ‖h‖) := by
    intro R
    obtain ⟨C, hC⟩ := hbd ((R : ℝ) + 1) (by positivity)
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hC
    exact ⟨C, k₀, fun k hk => Submission.indCompact_translation_estimate N (F (φ k)) R C (hF _)
      (hk₀ _ (le_trans hk hφ.le_apply))⟩
  -- `F_{φ(k)}` is locally Cauchy in measure, hence converges locally to a measurable set `G`.
  obtain ⟨G, hG, hlim⟩ := Submission.indCompact_limit_of_local_cauchy N (fun k => F (φ k))
    (fun _ => hF _) (Submission.indCompact_local_cauchy_of_mollified_cauchy N (fun k => F (φ k))
      ρ (fun _ => hF _) hρc hρs (fun m y => by rw [hρ]; exact div_nonneg (b m).nonneg (hb m).le)
      (fun m => by simp_rw [hρ]; rw [integral_div, div_self (hb m).ne'])
      (fun m => (hρb m).trans (by
        rw [(b m).support_eq, hbr m]; exact Metric.ball_subset_closedBall))
      htr hcau)
  exact ⟨φ, hφ, G, hG, hlim⟩
/-- **Half-space rigidity** (Simon Ch. 3, proof of Theorem 4.3, `chapter-03.txt` lines 656–688
and 733, with (9) read as `{x^{n+1} > λ}`). Let `G ⊆ ℝᴺ` be `Lᴺ`-measurable and `|e| = 1` with
(H) `∫_G D_v ζ = 0` for `v ⊥ e`, (M) `∫_G D_e ζ ≤ 0` for `ζ ≥ 0`, and (P) `G` and `ℝᴺ ∖ G` meet
every ball `B_R(0)` in positive measure. Then `G = {y : y · e > 0}` up to an `Lᴺ`-null set.
The mollifications `U_j = φ_j * χ_G` have `D_v U_j(z) = -∫_G D_v[φ_j(z - ·)] ≥ 0` when `v · e ≥ 0`,
so each `U_j` is a non-decreasing function of `y · e`. By Lebesgue differentiation `U_j → χ_G`
a.e., so `χ_G` is a.e. non-decreasing in `y · e`; (P) on `B_{|x₀ · e|}(0)` puts the jump at
`y · e = 0`, and the hyperplane `{y · e = 0}` is null. -/
theorem Submission.deGiorgi_halfSpace_rigidity : ∀ (N : ℕ) (G : Set (Rn N)) (e : Rn N),
    NullMeasurableSet G volume → ‖e‖ = 1 →
    (∀ (ζ : Rn N → ℝ) (v : Rn N), ContDiff ℝ 1 ζ → HasCompactSupport ζ → inner ℝ v e = 0 →
      ∫ y in G, fderiv ℝ ζ y v = 0) →
    (∀ ζ : Rn N → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ y, 0 ≤ ζ y) →
      ∫ y in G, fderiv ℝ ζ y e ≤ 0) →
    (∀ R : ℝ, 0 < R → 0 < volume (G ∩ Metric.ball 0 R) ∧ 0 < volume (Metric.ball 0 R \ G)) →
    volume (symmDiff G {y | 0 < inner ℝ y e}) = 0 := by
  intro N G e hG he hH hM hP
  -- Step 0: replace `G` by a measurable set `S` with `S =ᵐ G`.
  obtain ⟨S, hSm, hSG⟩ : ∃ S : Set (Rn N), MeasurableSet S ∧ S =ᵐ[volume] G :=
    ⟨toMeasurable volume G, measurableSet_toMeasurable _ _, hG.toMeasurable_ae_eq⟩
  have hH' : ∀ (ζ : Rn N → ℝ) (v : Rn N), ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      inner ℝ v e = 0 → ∫ y in S, fderiv ℝ ζ y v = 0 := by
    intro ζ v h1 h2 h3
    rw [Measure.restrict_congr_set hSG]
    exact hH ζ v h1 h2 h3
  have hM' : ∀ ζ : Rn N → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ y, 0 ≤ ζ y) →
      ∫ y in S, fderiv ℝ ζ y e ≤ 0 := by
    intro ζ h1 h2 h3
    rw [Measure.restrict_congr_set hSG]
    exact hM ζ h1 h2 h3
  have hP' : ∀ R : ℝ, 0 < R →
      0 < volume (S ∩ Metric.ball 0 R) ∧ 0 < volume (Metric.ball 0 R \ S) := by
    intro R hR
    rw [measure_congr (hSG.inter (EventuallyEqSet.refl _ _)),
      measure_congr ((EventuallyEqSet.refl _ _).diff hSG)]
    exact hP R hR
  rw [measure_symmDiff_eq_zero_iff]
  refine hSG.symm.trans ?_
  -- Step 1: `∫_S Dζ · v ≤ 0` for `ζ ≥ 0` and `⟪v, e⟫ ≥ 0`.
  have hK : ∀ ζ : Rn N → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ y, 0 ≤ ζ y) →
      ∀ v : Rn N, 0 ≤ inner ℝ v e → ∫ y in S, fderiv ℝ ζ y v ≤ 0 := by
    intro ζ h1 h2 h3 v hv
    have hw : inner ℝ (v - inner ℝ v e • e) e = 0 := by
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]
      ring
    have hsplit : ∀ y, fderiv ℝ ζ y v =
        fderiv ℝ ζ y (v - inner ℝ v e • e) + inner ℝ v e * fderiv ℝ ζ y e := by
      intro y
      rw [map_sub, map_smul, smul_eq_mul]
      ring
    have hint : ∀ w, Integrable (fun y ↦ fderiv ℝ ζ y w) (volume.restrict S) := by
      intro w
      exact (((h1.continuous_fderiv one_ne_zero).clm_apply
        continuous_const).integrable_of_hasCompactSupport (h2.fderiv_apply (𝕜 := ℝ) w)).integrableOn
    simp_rw [hsplit]
    rw [integral_add (hint _) ((hint e).const_mul _), integral_const_mul, hH' ζ _ h1 h2 hw,
      zero_add]
    exact mul_nonpos_of_nonneg_of_nonpos hv (hM' ζ h1 h2 h3)
  -- Step 2: mollifiers `φ j = (∫ b j)⁻¹ • b j`, `b j` a smooth bump with radii `r j / 2 < r j`.
  set u : Rn N → ℝ := S.indicator (fun _ ↦ (1 : ℝ))
  have hu_loc : LocallyIntegrable u volume := (locallyIntegrable_const (1 : ℝ)).indicator hSm
  set r : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hr_pos : ∀ j, 0 < r j := fun j ↦ by positivity
  set b : ℕ → ContDiffBump (0 : Rn N) := fun j ↦
    ⟨r j / 2, r j, half_pos (hr_pos j), half_lt_self (hr_pos j)⟩
  have hball_pos : ∀ ρ : ℝ, 0 < ρ → 0 < volume.real (Metric.closedBall (0 : Rn N) ρ) := by
    intro ρ hρ
    exact ENNReal.toReal_pos (Metric.measure_closedBall_pos volume 0 hρ).ne'
      measure_closedBall_lt_top.ne
  have hb_int : ∀ j, Integrable (b j) volume := fun j ↦
    (b j).continuous.integrable_of_hasCompactSupport (b j).hasCompactSupport
  have hb_ge : ∀ j, volume.real (Metric.closedBall (0 : Rn N) (r j / 2)) ≤ ∫ z, b j z := by
    intro j
    rw [← integral_indicator_one measurableSet_closedBall]
    refine integral_mono ((integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const measure_closedBall_lt_top.ne)) (hb_int j) fun z ↦ ?_
    by_cases hz : z ∈ Metric.closedBall (0 : Rn N) (r j / 2)
    · rw [indicator_of_mem hz, Pi.one_apply, (b j).one_of_mem_closedBall hz]
    · rw [indicator_of_notMem hz]
      exact (b j).nonneg
  have hb_pos : ∀ j, 0 < ∫ z, b j z := fun j ↦
    (hball_pos _ (half_pos (hr_pos j))).trans_le (hb_ge j)
  set φ : ℕ → Rn N → ℝ := fun j z ↦ (∫ w, b j w)⁻¹ * b j z
  have hφc1 : ∀ j, ContDiff ℝ 1 (φ j) := fun j ↦ contDiff_const.mul (b j).contDiff
  have hφcs : ∀ j, HasCompactSupport (φ j) := fun j ↦ (b j).hasCompactSupport.mul_left
  have hφnn : ∀ j z, 0 ≤ φ j z := fun j z ↦
    mul_nonneg (inv_nonneg.2 (hb_pos j).le) (b j).nonneg
  have hφint : ∀ j, ∫ z, φ j z = 1 := by
    intro j
    simp only [φ]
    rw [integral_const_mul, inv_mul_cancel₀ (hb_pos j).ne']
  have hφsupp : ∀ j z, φ j z ≠ 0 → ‖z‖ < r j := by
    intro j z hz
    have hz' : b j z ≠ 0 := right_ne_zero_of_mul hz
    have : z ∈ Function.support (b j) := hz'
    rw [(b j).support_eq] at this
    simpa using this
  set U : ℕ → Rn N → ℝ := fun j ↦ convolution (φ j) u (ContinuousLinearMap.lsmul ℝ ℝ) volume
  -- Step 3: each `U j` is a non-decreasing function of `⟪x, e⟫`.
  have hmono : ∀ j x x', inner ℝ x e ≤ inner ℝ x' e → U j x ≤ U j x' := by
    intro j x x' hxx'
    set D : Rn N → Rn N →L[ℝ] ℝ := fun z ↦ convolution (fderiv ℝ (φ j)) u
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Rn N)) volume z
    have hD : ∀ z, HasFDerivAt (U j) (D z) z := fun z ↦
      (hφcs j).hasFDerivAt_convolution_left _ (hφc1 j) hu_loc z
    have hDv : ∀ z v, 0 ≤ inner ℝ v e → 0 ≤ D z v := by
      intro z v hv
      have hI : Integrable (fun t ↦ ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Rn N))
          (fderiv ℝ (φ j) (z - t)) (u t)) volume :=
        ((hφcs j).fderiv (𝕜 := ℝ)).convolutionExists_left _
          ((hφc1 j).continuous_fderiv one_ne_zero) hu_loc z |>.integrable_swap
      simp only [D]
      rw [convolution_eq_swap, ContinuousLinearMap.integral_apply hI]
      simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      -- the integrand is `S.indicator (fun t ↦ fderiv (φ j) (z - t) v)`
      have hind : (fun t ↦ fderiv ℝ (φ j) (z - t) v * u t) =
          S.indicator (fun t ↦ fderiv ℝ (φ j) (z - t) v) := by
        ext t
        by_cases ht : t ∈ S <;> simp [u, ht]
      rw [hind, integral_indicator hSm]
      -- `ζ t = φ j (z - t)` is a nonnegative C¹ test function with `Dζ t = -Dφ (z - t)`
      set ζ : Rn N → ℝ := fun t ↦ φ j (z - t)
      have hζc1 : ContDiff ℝ 1 ζ := (hφc1 j).comp (contDiff_const.sub contDiff_id)
      have hζcs : HasCompactSupport ζ := (hφcs j).comp_homeomorph (Homeomorph.subLeft z)
      have hζnn : ∀ t, 0 ≤ ζ t := fun t ↦ hφnn j _
      have hζd : ∀ t, fderiv ℝ ζ t v = -(fderiv ℝ (φ j) (z - t) v) := by
        intro t
        have h1 : HasFDerivAt (fun t : Rn N ↦ z - t) (-ContinuousLinearMap.id ℝ (Rn N)) t :=
          (hasFDerivAt_id t).const_sub z
        have h2 : HasFDerivAt ζ ((fderiv ℝ (φ j) (z - t)).comp
            (-ContinuousLinearMap.id ℝ (Rn N))) t :=
          (((hφc1 j).differentiable one_ne_zero) (z - t)).hasFDerivAt.comp t h1
        rw [h2.fderiv]
        simp
      have := hK ζ hζc1 hζcs hζnn v hv
      simp_rw [hζd, integral_neg] at this
      linarith
    set g : ℝ → ℝ := fun s ↦ U j (x + s • (x' - x))
    have hg : ∀ s, HasDerivAt g (D (x + s • (x' - x)) (x' - x)) s := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ ↦ x + s • (x' - x)) (x' - x) s := by
        simpa using ((hasDerivAt_id s).smul_const (x' - x)).const_add x
      exact (hD _).comp_hasDerivAt s h1
    have hgm : Monotone g := monotone_of_deriv_nonneg (fun s ↦ (hg s).differentiableAt)
      (fun s ↦ by
        rw [(hg s).deriv]
        refine hDv _ _ ?_
        rw [inner_sub_left]
        linarith)
    have := hgm zero_le_one
    simpa [g] using this
  -- Step 4: Lebesgue differentiation gives `U j x → u x` for a.e. `x`.
  have hconv : ∀ᵐ x ∂(volume : Measure (Rn N)), Tendsto (fun j ↦ U j x) atTop (𝓝 (u x)) := by
    filter_upwards [(Besicovitch.vitaliFamily
      (volume : Measure (Rn N))).ae_tendsto_average_norm_sub hu_loc] with x h₀
    have hr : Tendsto r atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall hr_pos⟩
    have hlim := (h₀.comp (Besicovitch.tendsto_filterAt volume x)).comp hr
    have hU : ∀ j, U j x = ∫ t, φ j (x - t) • u t := fun j ↦ by
      simp only [U, convolution_eq_swap, ContinuousLinearMap.lsmul_apply]
    simp_rw [hU]
    have hfin : Module.finrank ℝ (Rn N) = N := finrank_euclideanSpace_fin
    refine tendsto_integral_smul_of_tendsto_average_norm_sub (2 ^ N)
      (a := fun j ↦ Metric.closedBall x (r j)) hlim ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun j ↦ hu_loc.integrableOn_isCompact (isCompact_closedBall _ _)
    · refine tendsto_const_nhds.congr fun j ↦ ?_
      rw [integral_sub_left_eq_self (φ j) volume x, hφint j]
    · refine Eventually.of_forall fun j t ht ↦ ?_
      have := hφsupp j _ ht
      rw [Metric.mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
      exact this.le
    · refine Eventually.of_forall fun j t ↦ ?_
      have hV := Measure.addHaar_real_closedBall' volume x (hr_pos j).le
      have hV' := Measure.addHaar_real_closedBall' volume (0 : Rn N) (half_pos (hr_pos j)).le
      rw [hfin] at hV hV'
      have hle1 : |φ j (x - t)| ≤ (∫ w, b j w)⁻¹ := by
        rw [abs_of_nonneg (hφnn j _)]
        calc φ j (x - t) = (∫ w, b j w)⁻¹ * b j (x - t) := rfl
          _ ≤ (∫ w, b j w)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (b j).le_one (inv_nonneg.2 (hb_pos j).le)
          _ = _ := mul_one _
      have hle2 : (∫ w, b j w)⁻¹ ≤ (volume.real (Metric.closedBall (0 : Rn N) (r j / 2)))⁻¹ :=
        inv_anti₀ (hball_pos _ (half_pos (hr_pos j))) (hb_ge j)
      have heq : (volume.real (Metric.closedBall (0 : Rn N) (r j / 2)))⁻¹ =
          2 ^ N / volume.real (Metric.closedBall x (r j)) := by
        have hV1 : 0 < volume.real (Metric.closedBall (0 : Rn N) 1) := hball_pos 1 one_pos
        have := hr_pos j
        rw [hV, hV', div_pow]
        field_simp
      calc |φ j (x - t)| ≤ _ := hle1
        _ ≤ _ := hle2
        _ = _ := heq
  -- Step 5: the threshold is `0`.
  have hgood : ∀ x x', Tendsto (fun j ↦ U j x) atTop (𝓝 (u x)) →
      Tendsto (fun j ↦ U j x') atTop (𝓝 (u x')) → inner ℝ x e ≤ inner ℝ x' e → u x ≤ u x' :=
    fun x x' hx hx' hxx' ↦ le_of_tendsto_of_tendsto' hx hx' fun j ↦ hmono j x x' hxx'
  set Z : Set (Rn N) := {x | ¬ Tendsto (fun j ↦ U j x) atTop (𝓝 (u x))}
  have hZ : volume Z = 0 := ae_iff.1 hconv
  have hinner : ∀ x : Rn N, |inner ℝ x e| ≤ ‖x‖ := fun x ↦ by
    simpa [he] using abs_real_inner_le_norm x e
  have hA : ∀ x₀, x₀ ∉ Z → inner ℝ x₀ e < 0 → x₀ ∉ S := by
    intro x₀ hx₀ hneg hx₀S
    have hR : 0 < -inner ℝ x₀ e := neg_pos.2 hneg
    have h1 := (hP' _ hR).2
    have h2 : volume (Metric.ball 0 (-inner ℝ x₀ e) \ S) = 0 := by
      refine measure_mono_null (fun x hx ↦ ?_) hZ
      by_contra hxZ
      obtain ⟨hxb, hxS⟩ := hx
      rw [Metric.mem_ball, dist_zero_right] at hxb
      have hle : inner ℝ x₀ e ≤ inner ℝ x e := by
        have := hinner x
        have := neg_abs_le (inner ℝ x e)
        linarith
      have := hgood x₀ x (not_not.1 hx₀) (not_not.1 hxZ) hle
      simp only [u, indicator_of_mem hx₀S, indicator_of_notMem hxS] at this
      linarith
    rw [h2] at h1
    exact lt_irrefl _ h1
  have hB : ∀ x₀, x₀ ∉ Z → 0 < inner ℝ x₀ e → x₀ ∈ S := by
    intro x₀ hx₀ hpos
    by_contra hx₀S
    have h1 := (hP' _ hpos).1
    have h2 : volume (S ∩ Metric.ball 0 (inner ℝ x₀ e)) = 0 := by
      refine measure_mono_null (fun x hx ↦ ?_) hZ
      by_contra hxZ
      obtain ⟨hxS, hxb⟩ := hx
      rw [Metric.mem_ball, dist_zero_right] at hxb
      have hle : inner ℝ x e ≤ inner ℝ x₀ e := by
        have := hinner x
        have := le_abs_self (inner ℝ x e)
        linarith
      have := hgood x x₀ (not_not.1 hxZ) (not_not.1 hx₀) hle
      simp only [u, indicator_of_mem hxS, indicator_of_notMem hx₀S] at this
      linarith
    rw [h2] at h1
    exact lt_irrefl _ h1
  have hplane : volume {x : Rn N | inner ℝ x e = 0} = 0 := by
    have hset : {x : Rn N | inner ℝ x e = 0} =
        ((Submodule.span ℝ {e})ᗮ : Submodule ℝ (Rn N)) := by
      ext x
      simp [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    rw [hset]
    refine Measure.addHaar_submodule volume _ fun h ↦ ?_
    have he' : e ∈ (Submodule.span ℝ {e})ᗮ := h ▸ Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq, he]
      at he'
    norm_num at he'
  rw [eventuallyEqSet_iff, ae_iff]
  refine measure_mono_null (fun x hx ↦ ?_) (measure_union_null hZ hplane)
  by_contra hxn
  simp only [mem_union, mem_ofPred_eq, not_or] at hxn
  obtain ⟨hxZ, hx0⟩ := hxn
  apply hx
  rcases lt_or_gt_of_ne hx0 with hlt | hgt
  · exact ⟨fun hxS ↦ absurd hxS (hA x hxZ hlt), fun h ↦ absurd h (not_lt.2 hlt.le)⟩
  · exact ⟨fun _ ↦ hgt, fun _ ↦ hB x hxZ hgt⟩

/-- **The blow-ups `η_{x,r}(E)` converge to the half-space** (Simon Ch. 3, Theorem 4.3 (‡‡) and
its proof, `chapter-03.txt` lines 653–739, with (9) and the last display read as
`{x^{n+1} > λ}`, `{x^{n+1} > 0}`): for a Gauss–Green pair `(μ, ν)` of `(U, E)` and `x ∈ ∂*E`,
`η_{x,r}(E) → H = {y : y · ν_E(x) > 0}` in `L¹_loc(ℝ^{n+1})` as `r ↓ 0`. By the density estimates
and the blow-up identity, on `B_R(0)` the blow-ups have perimeter `≤ C Rⁿ`, satisfy
`∫ D_v ζ → 0` for `v ⊥ ν_E(x)` and `∫ D_{ν_E(x)} ζ ≤ o(1)` for `ζ ≥ 0`, and they and their
complements have volume `≥ c R^{n+1}`. So every sequence `r_k ↓ 0` has a subsequence along which
they converge in `L¹_loc` (compactness), the limit inherits these properties and is `H` up to a
null set (half-space rigidity), and hence the whole family converges. -/
theorem Submission.deGiorgi_blowUp_tendsto_halfSpace : ∀ (n : ℕ) (U E : Set (Rn (n + 1))) (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)), IsOpen U → NullMeasurableSet E volume → IsGaussGreenPair U E μ ν → ∀ x ∈ reducedBoundary U μ ν, ∀ K : Set (Rn (n + 1)), IsCompact K → Tendsto (fun r : ℝ ↦ volume (K ∩ symmDiff (blowUpMap x r '' E) {y | 0 < inner ℝ y (reducedNormal μ ν x)})) (𝓝[>] 0) (𝓝 0) := by
  intro n U E μ ν hU hE hGG x hx K hK
  -- Step 0: `e = ν_E(x)` is the limit of the normal averages, so it is a unit vector.
  have he : ‖reducedNormal μ ν x‖ = 1 := by
    obtain ⟨-, v, hv, hv1⟩ := hx
    rw [reducedNormal, hv.limUnder_eq]
    exact hv1
  set e := reducedNormal μ ν x
  -- Step 1: `ρ₁` with `B_{ρ₁}(x) ⊆ U`, `μ(B_ρ(x)) ≤ C ρⁿ` and
  -- `L(E ∩ B_ρ(x)), L(B_ρ(x) ∖ E) ≥ c ρ^{n+1}` for `ρ < ρ₁`, and `ρ⁻ⁿ ∫_{B_ρ(x)} |ν - e| dμ → 0`.
  obtain ⟨ρ₁, hρ₁, hballU, C, c, hc, hbounds, hexc⟩ :=
    Submission.deGiorgi_density_estimates n U E μ ν hU hE hGG x hx
  -- Step 2: the blow-up identity for `tsupport g ⊆ B_R(0)` and `r R < ρ₁`; here
  -- `B_R(0) ∖ η_{x,r}(U) = η_{x,r}(B_{rR}(x) ∖ U) = ∅`.
  have hId : ∀ r R : ℝ, 0 < r → 0 < R → r * R < ρ₁ → ∀ g : Rn (n + 1) → Rn (n + 1),
      ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ Metric.ball 0 R →
      ∫ z in blowUpMap x r '' E, Poincare.SimonGMT.Chapter02.euclideanDivergence g z =
        -((r ^ n)⁻¹ * ∫ y, inner ℝ (g (blowUpMap x r y)) (ν y) ∂μ) := by
    intro r R hr _ hrR g hg hgc hgs
    refine Submission.deGiorgi_blowUp_gaussGreen_identity n U E μ ν x r hU hE hGG hr g hg hgc
      (hgs.trans ?_)
    have h := (((Submission.deGiorgiHS_blowUpMap_image_volume (n + 1) x r U).2 hr).2 R).2
    rw [sdiff_eq_empty.2 ((Metric.ball_subset_ball hrR.le).trans hballU), image_empty,
      sdiff_eq_empty] at h
    exact h
  have hfin : ∀ ρ ∈ Ioo 0 ρ₁, μ (Metric.ball x ρ) < ∞ := fun ρ hρ ↦
    (hbounds ρ hρ).1.trans_lt ENNReal.ofReal_lt_top
  -- Step 2(a): `∫_{η_{x,r}(E)} div g ≤ max C 0 Rⁿ` for `|g| ≤ 1`, `tsupport g ⊆ B_R(0)`.
  have hdiv := Submission.deGiorgiHS_blowUp_divergence_bound (n + 1) n E μ ν x ρ₁ C hGG.2.2.2.1
    (fun ρ hρ ↦ (hbounds ρ hρ).1) hId
  -- Step 2(b): `∫_{η_{x,r}(E)} D_v ζ → 0` for `v ⊥ e`, and `∫_{η_{x,r}(E)} D_e ζ ≤ o(1)` for
  -- `ζ ≥ 0`.
  obtain ⟨hHor, hVert⟩ := Submission.deGiorgiHS_blowUp_directional_limits (n + 1) n E μ ν x e ρ₁
    hGG.2.2.1 hGG.2.2.2.1 he hρ₁ hfin hexc hId
  -- For fixed `R > 0`, eventually `0 < r < ρ₁ / R` as `r ↓ 0`.
  have hwin : ∀ R : ℝ, 0 < R → ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r * R < ρ₁ := by
    intro R hR
    filter_upwards [Ioo_mem_nhdsGT (div_pos hρ₁ hR)] with r hr
    exact ⟨hr.1, (lt_div_iff₀ hR).1 hr.2⟩
  -- Step 6: it suffices that every sequence `r_k → 0⁺` has a subsequence along which the
  -- measures tend to `0`.
  apply tendsto_of_subseq_tendsto
  intro rs hrs
  set F : ℕ → Set (Rn (n + 1)) := fun k ↦ blowUpMap x (rs k) '' E
  have hFm : ∀ k, NullMeasurableSet (F k) volume := fun k ↦
    (Submission.deGiorgiHS_blowUpMap_image_volume (n + 1) x (rs k) E).1 hE
  -- Step 3: by Step 2(a) and compactness, `F (φ k) → G` in `L¹_loc` for some `φ` and `G`.
  have hbd : ∀ R : ℝ, 0 < R → ∃ C' : ℝ, ∀ᶠ k in atTop, ∀ g : Rn (n + 1) → Rn (n + 1),
      ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ Metric.ball 0 R →
      (∀ y, ‖g y‖ ≤ 1) →
      ∫ y in F k, Poincare.SimonGMT.Chapter02.euclideanDivergence g y ≤ C' := by
    intro R hR
    refine ⟨max C 0 * R ^ n, ?_⟩
    filter_upwards [hrs.eventually (hwin R hR)] with k hk
    exact hdiv (rs k) R hk.1 hR hk.2
  obtain ⟨φ, hφ, G, hGm, hconv⟩ := Submission.deGiorgi_indicator_compactness (n + 1) F hFm hbd
  have hrsφ : Tendsto (fun k ↦ rs (φ k)) atTop (𝓝[>] 0) := hrs.comp hφ.tendsto_atTop
  obtain ⟨hint, hvol⟩ := Submission.deGiorgiHS_L1loc_limit_transfer (n + 1) (fun k ↦ F (φ k)) G
    (fun k ↦ hFm (φ k)) hGm.nullMeasurableSet hconv
  -- Step 4 (H): `∫_G D_v ζ = lim_k ∫_{F (φ k)} D_v ζ = 0` for `v ⊥ e`.
  have hH : ∀ (ζ : Rn (n + 1) → ℝ) (v : Rn (n + 1)), ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      inner ℝ v e = 0 → ∫ y in G, fderiv ℝ ζ y v = 0 := by
    intro ζ v hζ hζc hv
    exact tendsto_nhds_unique (hint _ ((hζ.continuous_fderiv one_ne_zero).clm_apply
      continuous_const) (hζc.fderiv_apply ℝ v)) ((hHor ζ v hζ hζc hv).comp hrsφ)
  -- Step 4 (M): `∫_G D_e ζ = lim_k ∫_{F (φ k)} D_e ζ ≤ δ` for every `δ > 0`, when `ζ ≥ 0`.
  have hM : ∀ ζ : Rn (n + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ y, 0 ≤ ζ y) →
      ∫ y in G, fderiv ℝ ζ y e ≤ 0 := by
    intro ζ hζ hζc hζ0
    refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
    rw [zero_add]
    exact le_of_tendsto (hint _ ((hζ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hζc.fderiv_apply ℝ e)) (hrsφ.eventually (hVert ζ hζ hζc hζ0 δ hδ))
  -- Step 4 (P): `L(G ∩ B_R(0)), L(B_R(0) ∖ G) ≥ c R^{n+1} > 0`, as limits of the same quantities
  -- for `F (φ k)`.
  have hP : ∀ R : ℝ, 0 < R →
      0 < volume (G ∩ Metric.ball 0 R) ∧ 0 < volume (Metric.ball 0 R \ G) := by
    intro R hR
    obtain ⟨h1, h2⟩ := hvol (Metric.ball 0 R) Metric.isBounded_ball
    have hpos : 0 < ENNReal.ofReal (c * R ^ (n + 1)) :=
      ENNReal.ofReal_pos.2 (mul_pos hc (pow_pos hR _))
    have hev : ∀ᶠ k in atTop,
        ENNReal.ofReal (c * R ^ (n + 1)) ≤ volume (F (φ k) ∩ Metric.ball 0 R) ∧
        ENNReal.ofReal (c * R ^ (n + 1)) ≤ volume (Metric.ball 0 R \ F (φ k)) := by
      filter_upwards [hrsφ.eventually (hwin R hR)] with k hk
      obtain ⟨hr, hrR⟩ := hk
      obtain ⟨-, hlow1, hlow2⟩ := hbounds _ ⟨mul_pos hr hR, hrR⟩
      obtain ⟨hs1, hs2⟩ :=
        ((Submission.deGiorgiHS_blowUpMap_image_volume (n + 1) x (rs (φ k)) E).2 hr).2 R
      -- Step 2(c): `L(η_{x,r}(A)) = r^{-(n+1)} L(A) ≥ c R^{n+1}` when `L(A) ≥ c (rR)^{n+1}`.
      have key : ∀ A : Set (Rn (n + 1)),
          ENNReal.ofReal (c * (rs (φ k) * R) ^ (n + 1)) ≤ volume A →
          ENNReal.ofReal (c * R ^ (n + 1)) ≤ volume (blowUpMap x (rs (φ k)) '' A) := by
        intro A hA
        rw [((Submission.deGiorgiHS_blowUpMap_image_volume (n + 1) x (rs (φ k)) A).2 hr).1]
        calc ENNReal.ofReal (c * R ^ (n + 1))
            = ENNReal.ofReal ((rs (φ k) ^ (n + 1))⁻¹) *
                ENNReal.ofReal (c * (rs (φ k) * R) ^ (n + 1)) := by
              rw [← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg hr.le _))]
              congr 1
              rw [mul_pow]
              field_simp
          _ ≤ _ := by gcongr
      exact ⟨hs1 ▸ key _ hlow1, hs2 ▸ key _ hlow2⟩
    exact ⟨hpos.trans_le (ge_of_tendsto h1 (hev.mono fun k hk ↦ hk.1)),
      hpos.trans_le (ge_of_tendsto h2 (hev.mono fun k hk ↦ hk.2))⟩
  -- Step 5: by rigidity `L(G Δ H) = 0`, so `L(K ∩ (F (φ k) Δ H)) ≤ L(K ∩ (F (φ k) Δ G)) → 0`.
  have hGH : volume (symmDiff G {y | 0 < inner ℝ y e}) = 0 :=
    Submission.deGiorgi_halfSpace_rigidity (n + 1) G e hGm.nullMeasurableSet he hH hM hP
  refine ⟨φ, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv K hK)
    (fun _ ↦ zero_le) fun k ↦ ?_⟩
  calc volume (K ∩ symmDiff (blowUpMap x (rs (φ k)) '' E) {y | 0 < inner ℝ y e})
      ≤ volume ((K ∩ symmDiff (F (φ k)) G) ∪ symmDiff G {y | 0 < inner ℝ y e}) := by
        refine measure_mono fun y hy ↦ ?_
        rcases symmDiff_triangle (F (φ k)) G {y | 0 < inner ℝ y e} hy.2 with h | h
        · exact Or.inl ⟨hy.1, h⟩
        · exact Or.inr h
    _ ≤ volume (K ∩ symmDiff (F (φ k)) G) + volume (symmDiff G {y | 0 < inner ℝ y e}) :=
        measure_union_le _ _
    _ = volume (K ∩ symmDiff (F (φ k)) G) := by rw [hGH, add_zero]

/-- **De Giorgi, the tangent measure of `μ_E` at `x ∈ ∂*E`** (Simon Ch. 3, Theorem 4.3 (‡), proof
`chapter-03.txt` lines 739–746, with the sign correction E1 for the limit half-space and erratum
E3): for a Gauss–Green pair `(μ, ν)` of `(U, E)` and `x ∈ ∂*E`, `μ` has approximate tangent space
`P = (span{ν_E(x)})^⊥` with multiplicity `1` at `x`. So `dim P = n` and
`r⁻ⁿ ∫ f(η_{x,r}(y)) dμ(y) → ∫_P f dHⁿ` as `r ↓ 0` for every `f ∈ C_c(ℝ^{n+1})`. For `φ ∈ C¹_c` and
`e = ν_E(x)`, the blow-up Gauss–Green identity with `g = φ e` and `η_{x,r}(E) → {y · e > 0}` in
`L¹_loc` give `r⁻ⁿ ∫ φ(η_{x,r}(y)) e · ν(y) dμ(y) → -∫_{y · e > 0} D_e φ = ∫_P φ dHⁿ`, and the
excess decay at `x` removes the defect `1 - e · ν`. The mass bound `μ(B_ρ(x)) ≤ C ρⁿ` and the local
finiteness of `Hⁿ ⌞ P` extend the limit from `C¹_c` to `C_c`. -/
theorem Submission.deGiorgi_tangent_measure : ∀ (n : ℕ) (U E : Set (Rn (n + 1))) (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)), IsOpen U → NullMeasurableSet E volume → IsGaussGreenPair U E μ ν → ∀ x ∈ reducedBoundary U μ ν, HasApproxTangentPlaneWithMultiplicity n μ x ((Submodule.span ℝ {reducedNormal μ ν x})ᗮ) 1 := by
  intro n U E μ ν hU hE hGG x hx
  -- Step 0: `e = ν_E(x)` is the limit of the normal averages, a unit vector, so `dim P = n`.
  obtain ⟨-, v, hv, hv1⟩ := id hx
  set e := reducedNormal μ ν x
  have he1 : ‖e‖ = 1 := by rw [show e = v from hv.limUnder_eq, hv1]
  have he0 : e ≠ 0 := norm_ne_zero_iff.mp (by rw [he1]; exact one_ne_zero)
  have : Fact (finrank ℝ (Rn (n + 1)) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  set P : Submodule ℝ (Rn (n + 1)) := (Submodule.span ℝ {e})ᗮ
  have hPn : finrank ℝ P = n := Submodule.finrank_orthogonal_span_singleton he0
  -- Step 2: the mass bound and the excess decay at `x`.
  obtain ⟨ρ₁, hρ₁, hρ₁U, C, c, -, hmass, hexc⟩ :=
    Submission.deGiorgi_density_estimates n U E μ ν hU hE hGG x hx
  -- Step 1: `σ = Hⁿ ⌞ P` is finite on balls, as `Hⁿ ⌞ P` is Lebesgue measure on `P ≅ ℝⁿ`.
  set σ : Measure (Rn (n + 1)) := (μHE[n] : Measure (Rn (n + 1))).restrict (P : Set (Rn (n + 1)))
    with hσ
  have hσR : ∀ R : ℝ, σ (Metric.ball 0 R) < ∞ := by
    intro R
    have hvol := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := P)
    rw [hPn] at hvol
    have hiso : Isometry ((↑) : P → Rn (n + 1)) := fun _ _ ↦ rfl
    have hrange : Set.range ((↑) : P → Rn (n + 1)) = P := by
      ext z
      simp
    have hpre : ((↑) : P → Rn (n + 1)) ⁻¹' Metric.ball 0 R = Metric.ball (0 : P) R := by
      ext z
      simp
    rw [hσ, Measure.restrict_apply measurableSet_ball, ← hrange,
      ← hiso.euclideanHausdorffMeasure_preimage, hpre, hvol]
    exact measure_ball_lt_top
  -- Step 3: the limit for `C¹_c` test functions `φ`.
  have hC1 : ∀ φ : Rn (n + 1) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ y, φ (blowUpMap x r y) ∂μ) (𝓝[>] 0)
        (𝓝 (∫ y, φ y ∂σ)) := by
    intro φ hφ hφc
    obtain ⟨R₀, hR₀⟩ := hφc.isCompact.isBounded.subset_ball (0 : Rn (n + 1))
    set R := max R₀ 1
    have hR0 : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
    have hφR : tsupport φ ⊆ Metric.ball 0 R :=
      hR₀.trans (Metric.ball_subset_ball (le_max_left _ _))
    -- `div (φ e) = D_e φ`.
    have hdiv : ∀ z, Poincare.SimonGMT.Chapter02.euclideanDivergence (fun z ↦ φ z • e) z =
        fderiv ℝ φ z e := by
      intro z
      rw [Poincare.SimonGMT.Chapter02.euclideanDivergence,
        fderiv_smul_const ((hφ.differentiable one_ne_zero) z)]
      exact LinearMap.trace_smulRight _ _
    -- (i) The blow-up Gauss–Green identity for `g = φ e`, for `r ∈ (0, ρ₁ / R)`:
    -- `tsupport g ⊆ B_R(0) ⊆ η_{x,r}(B_{ρ₁}(x)) ⊆ η_{x,r}(U)`.
    have hid : ∀ r ∈ Ioo 0 (ρ₁ / R),
        (r ^ n)⁻¹ * ∫ y, φ (blowUpMap x r y) * inner ℝ e (ν y) ∂μ =
          -∫ z in blowUpMap x r '' E, fderiv ℝ φ z e := by
      intro r hr
      have hrR : r * R < ρ₁ := (lt_div_iff₀ hR0).1 hr.2
      have hgU : tsupport (fun z ↦ φ z • e) ⊆ blowUpMap x r '' U := by
        intro z hz
        have hzR : ‖z‖ < R := mem_ball_zero_iff.1 (hφR (tsupport_smul_subset_left _ _ hz))
        refine ⟨x + r • z, hρ₁U ?_, ?_⟩
        · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg hr.1.le]
          exact (mul_le_mul_of_nonneg_left hzR.le hr.1.le).trans_lt hrR
        · simp [blowUpMap, smul_smul, inv_mul_cancel₀ hr.1.ne']
      have h := Submission.deGiorgi_blowUp_gaussGreen_identity n U E μ ν x r hU hE hGG hr.1
        (fun z ↦ φ z • e) (hφ.smul contDiff_const) (hφc.smul_right (f' := fun _ ↦ e)) hgU
      simp only [hdiv, real_inner_smul_left] at h
      rw [h, neg_neg]
    -- (ii) `η_{x,r}(E) → H = {y · e > 0}` in `L¹_loc`, and the half-space flux identity.
    have hEr : ∀ᶠ r in 𝓝[>] (0 : ℝ), NullMeasurableSet (blowUpMap x r '' E) volume := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : 0 < r := hr
      have himg : blowUpMap x r '' E = (fun z ↦ r • z + x) ⁻¹' E := by
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          simpa [blowUpMap, smul_smul, mul_inv_cancel₀ hr0.ne'] using hy
        · intro hz
          exact ⟨r • z + x, hz, by simp [blowUpMap, smul_smul, inv_mul_cancel₀ hr0.ne']⟩
      rw [himg]
      exact hE.preimage ((measurePreserving_add_right volume x).quasiMeasurePreserving.comp
        (Measure.quasiMeasurePreserving_smul volume hr0.ne'))
    have hH : NullMeasurableSet {y : Rn (n + 1) | 0 < inner ℝ y e} volume :=
      (isOpen_lt continuous_const (continuous_id.inner continuous_const)).measurableSet
        |>.nullMeasurableSet
    have hconv : Tendsto (fun r : ℝ ↦ ∫ z in blowUpMap x r '' E, fderiv ℝ φ z e) (𝓝[>] 0)
        (𝓝 (∫ z in {y : Rn (n + 1) | 0 < inner ℝ y e}, fderiv ℝ φ z e)) :=
      Submission.deGiorgiTM_tendsto_setIntegral_of_symmDiff (n + 1) (fun r ↦ blowUpMap x r '' E)
        {y | 0 < inner ℝ y e} (fun z ↦ fderiv ℝ φ z e) hEr hH
        ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hφc.fderiv_apply ℝ e)
        (Submission.deGiorgi_blowUp_tendsto_halfSpace n U E μ ν hU hE hGG x hx _
          (hφc.fderiv_apply ℝ e).isCompact)
    rw [Submission.deGiorgiTM_halfSpace_integral_fderiv n e φ he1 hφ hφc] at hconv
    have hmain : Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ y, φ (blowUpMap x r y) * inner ℝ e (ν y) ∂μ)
        (𝓝[>] 0) (𝓝 (∫ y, φ y ∂σ)) := by
      have h := hconv.neg
      rw [neg_neg] at h
      refine h.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (div_pos hρ₁ hR0)] with r hr
      exact (hid r hr).symm
    -- (iii) The excess decay removes the defect `1 - e · ν`.
    have hdef := Submission.deGiorgiTM_blowUp_defect_tendsto_zero (n + 1) n μ ν x e (ρ₁ / 2) φ
      (half_pos hρ₁) ((hmass _ ⟨half_pos hρ₁, half_lt_self hρ₁⟩).1.trans_lt ENNReal.ofReal_lt_top)
      hGG.2.2.1 hGG.2.2.2.1 he1 hexc hφ.continuous hφc
    simpa only [sub_add_cancel, zero_add] using hdef.add hmain
  -- Steps 4–5: the mass bound extends the limit from `C¹_c` to `C_c` test functions.
  refine ⟨hPn, fun f ↦ ?_⟩
  rw [one_mul]
  exact Submission.deGiorgiTM_blowUp_tendsto_of_contDiff (n + 1) n μ σ x ρ₁ C hρ₁
    (fun ρ hρ ↦ (hmass ρ hρ).1) hσR hC1 f
/-- **The reduced boundary is a Borel set** (De Giorgi, parent Part 5b; cf. Simon Ch. 1, §3,
`chapter-01.txt` lines 575–592). `μ` is `σ`-finite, so for fixed `ρ` the centre map
`x ↦ normalAverage μ ν x ρ` is measurable (product measurability of `{dist < ρ}`). For `x ∈ U` the
map `ρ ↦ normalAverage μ ν x ρ` is left-continuous for small `ρ` (continuity from below and
dominated convergence), so the limit as `ρ ↓ 0` may be taken along rational radii. -/
theorem Submission.deGiorgi_measurableSet_reducedBoundary : ∀ (N : ℕ) (U : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → μ Uᶜ = 0 → (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ν μ → (∀ᵐ y ∂μ, ‖ν y‖ = 1) → MeasurableSet (reducedBoundary U μ ν) := by
  intro N U μ ν hU hUc hfin hν hν1
  -- Step 1: `μ` is `σ`-finite: `U` is a countable union of compact sets and `μ Uᶜ = 0`.
  obtain ⟨F, hFc, hFU, hFun, -⟩ := hU.exists_iUnion_isClosed
  have : SigmaFinite μ := by
    refine Measure.sigmaFinite_of_countable
      (S := insert Uᶜ (Set.range fun p : ℕ × ℕ => F p.1 ∩ Metric.closedBall 0 p.2))
      ((Set.countable_range _).insert _) ?_ ?_
    · rintro s (rfl | ⟨⟨n, m⟩, rfl⟩)
      · simp [hUc]
      · exact hfin _ ((isCompact_closedBall 0 (m : ℝ)).inter_left (hFc n))
          (Set.inter_subset_left.trans (hFU n))
    · refine Set.eq_univ_of_forall fun y => ?_
      by_cases hy : y ∈ U
      · rw [← hFun] at hy
        obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hy
        obtain ⟨m, hm⟩ := exists_nat_ge ‖y‖
        exact Set.mem_sUnion.2 ⟨_, Or.inr ⟨(n, m), rfl⟩, hn, by simpa using hm⟩
      · exact Set.mem_sUnion.2 ⟨Uᶜ, Or.inl rfl, hy⟩
  -- Step 2: for fixed `ρ`, the centre map `x ↦ normalAverage μ ν x ρ` is measurable.
  have hmeas : ∀ ρ : ℝ, Measurable fun x => normalAverage μ ν x ρ := by
    intro ρ
    have hS : MeasurableSet {p : Rn N × Rn N | dist p.2 p.1 < ρ} :=
      measurableSet_lt (measurable_snd.dist measurable_fst) measurable_const
    have h1 : Measurable fun x => μ (Metric.ball x ρ) := measurable_measure_prodMk_left hS
    have h2 : StronglyMeasurable fun x => ∫ y in Metric.ball x ρ, ν y ∂μ := by
      have : (fun x => ∫ y in Metric.ball x ρ, ν y ∂μ) = fun x =>
          ∫ y, {p : Rn N × Rn N | dist p.2 p.1 < ρ}.indicator (fun p => hν.mk ν p.2) (x, y) ∂μ := by
        funext x
        rw [integral_congr_ae (ae_restrict_of_ae hν.ae_eq_mk),
          ← integral_indicator measurableSet_ball]
        rfl
      rw [this]
      exact StronglyMeasurable.integral_prod_right' (ν := μ)
        ((hν.stronglyMeasurable_mk.comp_measurable measurable_snd).indicator hS)
    exact (h1.ennreal_toReal.inv).smul h2.measurable
  -- Step 3: for `x ∈ U`, `ρ ↦ normalAverage μ ν x ρ` is left-continuous on `(0, r)`.
  have hleft : ∀ x ∈ U, ∃ r > 0, ∀ ρ, 0 < ρ → ρ < r →
      Tendsto (normalAverage μ ν x) (𝓝[<] ρ) (𝓝 (normalAverage μ ν x ρ)) := by
    intro x hx
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hx
    refine ⟨ε / 2, half_pos hε, fun ρ hρ hρr => ?_⟩
    have hball : μ (Metric.ball x ρ) < ∞ :=
      (measure_mono (Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall hρr.le))).trans_lt
        (hfin _ (isCompact_closedBall x (ε / 2))
          ((Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU))
    have key : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Rn N → E),
        AEStronglyMeasurable g μ → (∀ᵐ y ∂μ, ‖g y‖ ≤ 1) →
        Tendsto (fun ρ' => ∫ y, (Metric.ball x ρ').indicator g y ∂μ) (𝓝[<] ρ)
          (𝓝 (∫ y, (Metric.ball x ρ).indicator g y ∂μ)) := by
      intro E _ _ g hg hg1
      refine tendsto_integral_filter_of_dominated_convergence
        ((Metric.ball x ρ).indicator (1 : Rn N → ℝ)) ?_ ?_ ?_ ?_
      · exact Eventually.of_forall fun ρ' => hg.indicator measurableSet_ball
      · filter_upwards [self_mem_nhdsWithin] with ρ' hρ'
        filter_upwards [hg1] with y hy
        by_cases hy' : y ∈ Metric.ball x ρ'
        · rw [Set.indicator_of_mem hy',
            Set.indicator_of_mem (Metric.ball_subset_ball (le_of_lt hρ') hy')]
          simpa using hy
        · rw [Set.indicator_of_notMem hy', norm_zero]
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) y
      · exact (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const hball.ne)
      · refine Eventually.of_forall fun y => ?_
        by_cases hy : dist y x < ρ
        · rw [Set.indicator_of_mem (show y ∈ Metric.ball x ρ from hy)]
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [Ioo_mem_nhdsLT hy] with ρ' hρ'
          exact (Set.indicator_of_mem (show y ∈ Metric.ball x ρ' from hρ'.1) g).symm
        · rw [Set.indicator_of_notMem (show y ∉ Metric.ball x ρ from hy)]
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with ρ' hρ'
          exact (Set.indicator_of_notMem
            (show y ∉ Metric.ball x ρ' from fun h => hy (lt_trans h hρ')) g).symm
    have hA : Tendsto (fun ρ' => (μ (Metric.ball x ρ')).toReal) (𝓝[<] ρ)
        (𝓝 (μ (Metric.ball x ρ)).toReal) := by
      have := key (1 : Rn N → ℝ) aestronglyMeasurable_one (Eventually.of_forall fun _ => by simp)
      simpa only [integral_indicator_one measurableSet_ball, measureReal_def] using this
    have hB : Tendsto (fun ρ' => ∫ y in Metric.ball x ρ', ν y ∂μ) (𝓝[<] ρ)
        (𝓝 (∫ y in Metric.ball x ρ, ν y ∂μ)) := by
      have := key ν hν (by filter_upwards [hν1] with y hy using hy.le)
      simpa only [integral_indicator measurableSet_ball] using this
    by_cases h0 : (μ (Metric.ball x ρ)).toReal = 0
    · have hμ0 : μ (Metric.ball x ρ) = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h | h
        · exact h
        · exact absurd h hball.ne
      have hz : ∀ ρ' ≤ ρ, normalAverage μ ν x ρ' = 0 := by
        intro ρ' hρ'
        have : μ (Metric.ball x ρ') = 0 := measure_mono_null (Metric.ball_subset_ball hρ') hμ0
        simp [normalAverage, this]
      rw [hz ρ le_rfl]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ρ' hρ'
      exact (hz ρ' (le_of_lt hρ')).symm
    · exact (hA.inv₀ h0).smul hB
  -- Step 4: the limit along `ρ ↓ 0` may be taken along rational radii.
  have hne : (Filter.comap (fun q : ℚ => (q : ℝ)) (𝓝[>] (0 : ℝ))).NeBot := by
    rw [Filter.comap_neBot_iff]
    intro t ht
    obtain ⟨δ, hδ, hδt⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ht
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (Set.mem_Ioi.1 hδ)
    exact ⟨q, hδt ⟨hq1, hq2⟩⟩
  have hset : reducedBoundary U μ ν = U ∩
      ({x | ∃ c, Tendsto (fun q : ℚ => normalAverage μ ν x q)
          (Filter.comap (fun q : ℚ => (q : ℝ)) (𝓝[>] (0 : ℝ))) (𝓝 c)} ∩
        {x | ‖limUnder (Filter.comap (fun q : ℚ => (q : ℝ)) (𝓝[>] (0 : ℝ)))
          (fun q : ℚ => normalAverage μ ν x q)‖ = 1}) := by
    ext x
    simp only [reducedBoundary, Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hxU, v, hv, hv1⟩
      have hq : Tendsto (fun q : ℚ => normalAverage μ ν x q)
          (Filter.comap (fun q : ℚ => (q : ℝ)) (𝓝[>] (0 : ℝ))) (𝓝 v) := hv.comp tendsto_comap
      exact ⟨hxU, ⟨v, hq⟩, by rw [hq.limUnder_eq]; exact hv1⟩
    · rintro ⟨hxU, ⟨c, hc⟩, hc1⟩
      rw [hc.limUnder_eq] at hc1
      refine ⟨hxU, c, ?_, hc1⟩
      obtain ⟨r, hr, hcont⟩ := hleft x hxU
      rw [Metric.nhds_basis_closedBall.tendsto_right_iff]
      intro ε hε
      obtain ⟨t, ht, hts⟩ :=
        Filter.mem_comap.1 ((Metric.nhds_basis_closedBall.tendsto_right_iff.1 hc) ε hε)
      obtain ⟨δ, hδ, hδt⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ht
      filter_upwards [Ioo_mem_nhdsGT (lt_min (Set.mem_Ioi.1 hδ) hr)] with ρ hρ
      have hρδ : ρ < δ := hρ.2.trans_le (min_le_left _ _)
      have hρr : ρ < r := hρ.2.trans_le (min_le_right _ _)
      have : (Filter.comap (fun q : ℚ => (q : ℝ)) (𝓝[<] ρ)).NeBot := by
        rw [Filter.comap_neBot_iff]
        intro s hs
        obtain ⟨a, ha, has⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hs
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (Set.mem_Iio.1 ha)
        exact ⟨q, has ⟨hq1, hq2⟩⟩
      refine Metric.isClosed_closedBall.mem_of_tendsto
        ((hcont ρ hρ.1 hρr).comp (tendsto_comap (f := fun q : ℚ => (q : ℝ)))) ?_
      filter_upwards [Filter.preimage_mem_comap (Ioo_mem_nhdsLT hρ.1)] with q hq
      exact hts (hδt ⟨hq.1, hq.2.trans hρδ⟩)
  -- Step 5: a countable description of `∂*`.
  rw [hset]
  refine hU.measurableSet.inter (MeasurableSet.inter ?_ ?_)
  · exact StronglyMeasurable.measurableSet_exists_tendsto fun q : ℚ => (hmeas q).stronglyMeasurable
  · exact (StronglyMeasurable.limUnder fun q : ℚ => (hmeas q).stronglyMeasurable).measurable.norm
      (measurableSet_singleton 1)
/-- **Lebesgue–Besicovitch differentiation along open balls** (Simon Ch. 1, Corollary 3.17, with
the passage from closed to open balls; parent proof steps 2–3). Let `μ` be a finite measure on
`ℝᴺ` and `f ∈ L¹(μ)`. Then for `μ`-a.e. `x`, `normalAverage μ f x ρ = μ(B_ρ(x))⁻¹ ∫_{B_ρ(x)} f dμ`
tends to `f(x)` as `ρ ↓ 0`. Besicovitch differentiation gives `c(r) = ⨍_{B̄_r(x)} f dμ → f(x)`.
Given a closed neighbourhood `F` of `f(x)`, take `δ > 0` with `c(r) ∈ F` for `r ∈ (0, δ)`, and let
`ρ ∈ (0, δ)`. If `μ(B_ρ(x)) = 0`, then `normalAverage μ f x ρ = 0 = c(ρ/2)`. Otherwise the closed
balls `B̄_{r_n}(x)`, `ρ/2 < r_n ↑ ρ`, exhaust `B_ρ(x)`, so `c(r_n) → normalAverage μ f x ρ` by
continuity of measure from below and of set integrals, and `F` is closed. -/
theorem Submission.deGiorgiBFM_normalAverage_tendsto_ae : ∀ (N : ℕ) (μ : Measure (Rn N)) (f : Rn N → Rn N), IsFiniteMeasure μ → Integrable f μ → ∀ᵐ x ∂μ, Tendsto (normalAverage μ f x) (𝓝[>] 0) (𝓝 (f x)) := by
  intro N μ f hμ hf
  -- Lebesgue–Besicovitch differentiation along closed balls.
  filter_upwards [VitaliFamily.ae_tendsto_average (Besicovitch.vitaliFamily μ) hf.locallyIntegrable]
    with x hx
  have hc : Tendsto (fun r : ℝ ↦ ⨍ y in Metric.closedBall x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) :=
    hx.comp (Besicovitch.tendsto_filterAt μ x)
  refine (closed_nhds_basis (f x)).tendsto_right_iff.2 fun F ⟨hF, hFc⟩ ↦ ?_
  obtain ⟨δ, hδ, hδF⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 (hc.eventually_mem hF)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ ⟨hρ, hρδ⟩
  rcases eq_or_ne (μ (Metric.ball x ρ)) 0 with h0 | hne
  · -- `μ(B_ρ(x)) = 0`: both `normalAverage μ f x ρ` and `c(ρ/2)` vanish.
    have h1 : normalAverage μ f x ρ = 0 := by
      rw [normalAverage, h0, ENNReal.toReal_zero, inv_zero, zero_smul]
    have h2 : ⨍ y in Metric.closedBall x (ρ / 2), f y ∂μ = 0 := by
      rw [setAverage_eq, measureReal_def,
        measure_mono_null (Metric.closedBall_subset_ball (half_lt_self hρ)) h0,
        ENNReal.toReal_zero, inv_zero, zero_smul]
    rw [id, h1, ← h2]
    exact hδF ⟨half_pos hρ, (half_lt_self hρ).trans hρδ⟩
  · -- `μ(B_ρ(x)) > 0`: the closed balls `B̄_{u n}(x)`, `ρ/2 < u n ↑ ρ`, exhaust `B_ρ(x)`.
    obtain ⟨u, hu_mono, hu_mem, hu_lim⟩ := exists_seq_strictMono_tendsto' (half_lt_self hρ)
    have hU : ⋃ n, Metric.closedBall x (u n) = Metric.ball x ρ := by
      refine Subset.antisymm (iUnion_subset fun n ↦ Metric.closedBall_subset_ball (hu_mem n).2) ?_
      intro y hy
      obtain ⟨n, hn⟩ := (hu_lim.eventually (lt_mem_nhds (Metric.mem_ball.1 hy))).exists
      exact mem_iUnion.2 ⟨n, Metric.mem_closedBall.2 hn.le⟩
    have hmono : Monotone fun n ↦ Metric.closedBall x (u n) :=
      fun m n hmn ↦ Metric.closedBall_subset_closedBall (hu_mono.monotone hmn)
    -- `μ(B̄_{u n}(x))⁻¹ → μ(B_ρ(x))⁻¹` (continuity from below; `0 < μ(B_ρ(x)) < ∞`).
    have hmeas : Tendsto (fun n ↦ (μ (Metric.closedBall x (u n))).toReal⁻¹) atTop
        (𝓝 (μ (Metric.ball x ρ)).toReal⁻¹) := by
      refine ((ENNReal.tendsto_toReal (measure_ne_top μ _)).comp ?_).inv₀
        (ENNReal.toReal_ne_zero.2 ⟨hne, measure_ne_top μ _⟩)
      rw [← hU]
      exact tendsto_measure_iUnion_atTop hmono
    -- `∫_{B̄_{u n}(x)} f dμ → ∫_{B_ρ(x)} f dμ`.
    have hint : Tendsto (fun n ↦ ∫ y in Metric.closedBall x (u n), f y ∂μ) atTop
        (𝓝 (∫ y in Metric.ball x ρ, f y ∂μ)) := by
      rw [← hU]
      exact tendsto_setIntegral_of_monotone (fun _ ↦ measurableSet_closedBall) hmono
        hf.integrableOn
    refine hFc.mem_of_tendsto (hmeas.smul hint) (Eventually.of_forall fun n ↦ ?_)
    simpa only [setAverage_eq, measureReal_def] using
      hδF ⟨(half_pos hρ).trans (hu_mem n).1, (hu_mem n).2.trans hρδ⟩
/-- **Open exhaustion by sets of finite measure** (Simon Ch. 1, Def. 1.14 and the remark after it,
as used in the proof of Ch. 1, Thm. 3.16; parent proof step 1). If `U ⊆ ℝᴺ` is open and
`μ(K) < ∞` for every compact `K ⊆ U`, then `U = ⋃ᵢ Wᵢ` with `Wᵢ` open and `μ(Wᵢ) < ∞`.
With `d(y, Uᶜ) ∈ [0, ∞]` the extended distance and `cᵢ = (i + 1)⁻¹ > 0`, take
`Wᵢ = B_{i+1}(0) ∩ {y : cᵢ < d(y, Uᶜ)}`: it is open, it lies in the compact set
`Kᵢ = B̄_{i+1}(0) ∩ {y : cᵢ ≤ d(y, Uᶜ)} ⊆ U`, and every `y ∈ U` has `d(y, Uᶜ) > 0` since `Uᶜ` is
closed, so `y ∈ Wᵢ` once `cᵢ < d(y, Uᶜ)` and `‖y‖ < i + 1`. -/
theorem Submission.deGiorgiBFM_exists_open_exhaustion : ∀ (N : ℕ) (U : Set (Rn N)) (μ : Measure (Rn N)), IsOpen U → (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) → ∃ W : ℕ → Set (Rn N), (∀ i, IsOpen (W i)) ∧ (∀ i, μ (W i) < ∞) ∧ ⋃ i, W i = U := by
  intro N U μ hU hK
  -- `cᵢ = (i + 1)⁻¹` is positive, so `cᵢ ≤ d(y, Uᶜ)` forces `y ∈ U` (`d(y, Uᶜ) = 0` on `Uᶜ`).
  have hc : ∀ i : ℕ, ((i : ℝ≥0∞) + 1)⁻¹ ≠ 0 := fun i ↦
    ENNReal.inv_ne_zero.2 (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top i, ENNReal.one_ne_top⟩)
  have hmem : ∀ (i : ℕ) (y : Rn N), ((i : ℝ≥0∞) + 1)⁻¹ ≤ Metric.infEDist y Uᶜ → y ∈ U := by
    intro i y hy
    by_contra h
    rw [Metric.infEDist_zero_of_mem (show y ∈ Uᶜ from h)] at hy
    exact hc i (nonpos_iff_eq_zero.1 hy)
  refine ⟨fun i ↦ Metric.ball 0 ((i : ℝ) + 1) ∩ {y | ((i : ℝ≥0∞) + 1)⁻¹ < Metric.infEDist y Uᶜ},
    fun i ↦ ?_, fun i ↦ ?_, Subset.antisymm (iUnion_subset fun i y hy ↦ hmem i y (le_of_lt hy.2))
      fun y hy ↦ ?_⟩
  · exact Metric.isOpen_ball.inter (isOpen_lt continuous_const Metric.continuous_infEDist)
  · -- `Wᵢ ⊆ Kᵢ`, and `Kᵢ` is a compact subset of `U`.
    have hKi : IsCompact (Metric.closedBall (0 : Rn N) ((i : ℝ) + 1) ∩
        {y | ((i : ℝ≥0∞) + 1)⁻¹ ≤ Metric.infEDist y Uᶜ}) :=
      (isCompact_closedBall _ _).inter_right
        (isClosed_le continuous_const Metric.continuous_infEDist)
    refine (measure_mono ?_).trans_lt (hK _ hKi fun y hy ↦ hmem i y hy.2)
    exact inter_subset_inter Metric.ball_subset_closedBall
      (ofPred_subset_ofPred_of_imp fun _ ↦ le_of_lt)
  · -- `d(y, Uᶜ) ≠ 0` as `Uᶜ` is closed; take `i = max n m` with `n⁻¹ < d(y, Uᶜ)` and `‖y‖ < m`.
    have hd : Metric.infEDist y Uᶜ ≠ 0 := fun h0 ↦
      (Metric.mem_iff_infEDist_zero_of_closed hU.isClosed_compl).2 h0 hy
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hd
    obtain ⟨m, hm⟩ := exists_nat_gt ‖y‖
    refine mem_iUnion.2 ⟨max n m, ?_, ?_⟩
    · rw [mem_ball_zero_iff]
      calc ‖y‖ < m := hm
        _ ≤ ((max n m : ℕ) : ℝ) := by exact_mod_cast le_max_right n m
        _ < ((max n m : ℕ) : ℝ) + 1 := lt_add_one _
    · calc (((max n m : ℕ) : ℝ≥0∞) + 1)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ :=
            ENNReal.inv_le_inv.2 (by exact_mod_cast (show n ≤ max n m + 1 by omega))
        _ < Metric.infEDist y Uᶜ := hn

/-- **The reduced boundary has full `μ`-measure** (Simon Ch. 3, after (4.2) (p. 81): "Since
`|ν| = 1` `μ_E`-a.e. in `U`, by virtue of Theorem 3.23 of Ch. 1 we have `μ_E(U ∖ ∂*E) = 0`").
Let `U ⊆ ℝᴺ` be open, `μ` a Borel measure with `μ(Uᶜ) = 0` and `μ(K) < ∞` for compact `K ⊆ U`,
and `ν` `μ`-measurable with `|ν| = 1` `μ`-a.e. Exhaust `U = ⋃ᵢ Wᵢ` by open `Wᵢ` with
`μ(Wᵢ) < ∞`. Then `μ ⌞ Wᵢ` is finite and `ν ∈ L¹(μ ⌞ Wᵢ)`, so by Lebesgue–Besicovitch
differentiation along open balls, `⨍_{B_ρ(x)} ν d(μ ⌞ Wᵢ) → ν(x)` as `ρ ↓ 0` for `μ`-a.e.
`x ∈ Wᵢ`. For such `x` and small `ρ`, `B_ρ(x) ⊆ Wᵢ`, where `μ ⌞ Wᵢ` and `μ` agree; so
`⨍_{B_ρ(x)} ν dμ → ν(x)`, a unit vector `μ`-a.e., i.e. `x ∈ ∂*E`. As `μ(Uᶜ) = 0`, countable
subadditivity gives `μ(ℝᴺ ∖ ∂*E) = 0` (no measurability of `∂*E` is needed). -/
theorem Submission.deGiorgi_measure_compl_reducedBoundary : ∀ (N : ℕ) (U : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → μ Uᶜ = 0 → (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ν μ → (∀ᵐ y ∂μ, ‖ν y‖ = 1) → μ (reducedBoundary U μ ν)ᶜ = 0 := by
  intro N U μ ν hU hUc hK hν hν1
  -- Localization: `U = ⋃ᵢ Wᵢ` with `Wᵢ` open and `μ(Wᵢ) < ∞`.
  obtain ⟨W, hWo, hWfin, hWU⟩ := Submission.deGiorgiBFM_exists_open_exhaustion N U μ hU hK
  -- Differentiate `ν ∈ L¹(μ ⌞ Wᵢ)` along open balls; read back as a `μ`-a.e. statement on `Wᵢ`.
  have hdiff : ∀ i, ∀ᵐ x ∂μ, x ∈ W i →
      Tendsto (normalAverage (μ.restrict (W i)) ν x) (𝓝[>] 0) (𝓝 (ν x)) := by
    intro i
    have hfin : IsFiniteMeasure (μ.restrict (W i)) := isFiniteMeasure_restrict.2 (hWfin i).ne
    have hint : Integrable ν (μ.restrict (W i)) :=
      Integrable.of_bound hν.restrict 1 (ae_restrict_of_ae (hν1.mono fun y hy ↦ hy.le))
    exact (ae_restrict_iff' (hWo i).measurableSet).1
      (Submission.deGiorgiBFM_normalAverage_tendsto_ae N (μ.restrict (W i)) ν hfin hint)
  have hUae : ∀ᵐ x ∂μ, x ∈ U :=
    (measure_eq_zero_iff_ae_notMem.1 hUc).mono fun x hx ↦ notMem_compl_iff.1 hx
  -- Off a `μ`-null set, `x ∈ U = ⋃ᵢ Wᵢ` and all the above hold, so `x` is in the reduced boundary.
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_all_iff.2 hdiff, hUae, hν1] with x hxdiff hxU hx1
  rw [notMem_compl_iff]
  obtain ⟨i, hi⟩ := mem_iUnion.1 (show x ∈ ⋃ i, W i by rwa [hWU])
  obtain ⟨R, hR, hRW⟩ := Metric.isOpen_iff.1 (hWo i) x hi
  refine ⟨hxU, ν x, (hxdiff i hi).congr' ?_, hx1⟩
  -- For `0 < ρ < R`, `B_ρ(x) ⊆ Wᵢ`, so the averages for `μ ⌞ Wᵢ` and for `μ` coincide.
  filter_upwards [Ioo_mem_nhdsGT hR] with ρ hρ
  have hsub : Metric.ball x ρ ⊆ W i := (Metric.ball_subset_ball hρ.2.le).trans hRW
  simp only [normalAverage, Measure.restrict_eq_self μ hsub,
    Measure.restrict_restrict_of_subset hsub]
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
/-- **Density comparison: unit density on `A` gives `Hⁿ(A) ≤ μ(A)`** (parent proof, Step 4;
Simon Ch. 1, Theorem 3.3 with `A₁ = A`, `t = 1`, `chapter-01.txt` lines 602–604, proof lines
666–695). If `μ` is finite on compact subsets of `ℝᴺ` and `μ(B̄_ρ(x)) / ρⁿ → ω_n = Lⁿ(B₁(0))` as
`ρ ↓ 0` at every `x ∈ A`, then `Hⁿ(A) ≤ μ(A)` (outer measures; `A` arbitrary). SimonGMT's
comparison theorem and its normalization of `μHE[n]` are not imported here, so the proof is
self-contained:
1. the isodiametric inequality `Lᵈ(s) ≤ ω_d (diam s / 2)ᵈ` (Simon (2.10), lines 502–536), by
   successive Steiner symmetrizations in the coordinate directions, as in Simon;
2. hence `μHE[n] = c • μH[n]` with `c 2ⁿ ≤ ω_n` (Simon (2.9), lines 547–559), so a closed ball
   `B̄_ρ` has `Hⁿ`-cost `c (diam B̄_ρ)ⁿ ≤ ω_n ρⁿ`;
3. the density hypothesis makes the balls `B̄_ρ(x)`, `x ∈ A`, with `ω_n ρⁿ ≤ (1 + ε) μ(B̄_ρ(x))` a
   fine cover of `A`; Besicovitch's covering (Simon 3.12, line 804, in Mathlib's outer-regular
   form, which replaces the open sets `O ⊇ A` and the 5-times covering lemma) gives a countable
   subcover with `∑ μ(B̄_ρ(x)) ≤ μ(A) + ε`;
4. thus `Hⁿ(A) ≤ (1 + ε)(μ(A) + ε)` at every scale, and `ε ↓ 0`. -/
theorem Submission.deGiorgiRH_hausdorff_le_of_density : ∀ (n N : ℕ) (μ : Measure (Rn N)) (A : Set (Rn N)), (∀ K : Set (Rn N), IsCompact K → μ K < ∞) → (∀ x ∈ A, Tendsto (fun ρ : ℝ ↦ μ (Metric.closedBall x ρ) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : Rn n) 1)))) → μHE[n] A ≤ μ A := by
  -- Step 1: the isodiametric inequality `Lᵈ(s) ≤ ω_d (diam s / 2)ᵈ` for bounded `s ⊆ ℝᵈ`.
  have hiso : ∀ (d : ℕ) (s : Set (Rn d)), Bornology.IsBounded s →
      volume s ≤ ENNReal.ofReal ((Metric.diam s / 2) ^ d) * volume (Metric.ball (0 : Rn d) 1) := by
    -- Two nonempty real sets with all cross-distances `≤ δ` have total length `≤ 2δ`, so the
    -- centred intervals of the same lengths still have cross-distances `≤ δ`.
    have h1d : ∀ (P Q : Set ℝ), P.Nonempty → Q.Nonempty → ∀ δ : ℝ,
        (∀ a ∈ P, ∀ b ∈ Q, dist a b ≤ δ) → ∀ x y : ℝ, |x| ≤ (volume P).toReal / 2 →
          |y| ≤ (volume Q).toReal / 2 → dist x y ≤ δ := by
      intro P Q hP hQ δ hcross x y hx hy
      obtain ⟨a₀, ha₀⟩ := hP
      obtain ⟨b₀, hb₀⟩ := hQ
      have hdist (a : ℝ) (ha : a ∈ P) (b : ℝ) (hb : b ∈ Q) : a - b ≤ δ ∧ b - a ≤ δ :=
        abs_sub_le_iff.mp (by simpa only [Real.dist_eq] using hcross a ha b hb)
      have hPl : BddBelow P := ⟨b₀ - δ, fun a ha => by have := (hdist a ha b₀ hb₀).2; linarith⟩
      have hPu : BddAbove P := ⟨b₀ + δ, fun a ha => by have := (hdist a ha b₀ hb₀).1; linarith⟩
      have hQl : BddBelow Q := ⟨a₀ - δ, fun b hb => by have := (hdist a₀ ha₀ b hb).1; linarith⟩
      have hQu : BddAbove Q := ⟨a₀ + δ, fun b hb => by have := (hdist a₀ ha₀ b hb).2; linarith⟩
      have hPQ : sSup P ≤ δ + sInf Q := by
        apply csSup_le ⟨a₀, ha₀⟩
        intro a ha
        have h : a - δ ≤ sInf Q := le_csInf ⟨b₀, hb₀⟩ fun b hb => by
          have := (hdist a ha b hb).1
          linarith
        linarith
      have hQP : sSup Q ≤ δ + sInf P := by
        apply csSup_le ⟨b₀, hb₀⟩
        intro b hb
        have h : b - δ ≤ sInf P := le_csInf ⟨a₀, ha₀⟩ fun a ha => by
          have := (hdist a ha b hb).2
          linarith
        linarith
      have hwP : 0 ≤ sSup P - sInf P :=
        sub_nonneg.mpr ((csInf_le hPl ha₀).trans (le_csSup hPu ha₀))
      have hwQ : 0 ≤ sSup Q - sInf Q :=
        sub_nonneg.mpr ((csInf_le hQl hb₀).trans (le_csSup hQu hb₀))
      have hvP : (volume P).toReal ≤ sSup P - sInf P := by
        have h := measure_mono (μ := volume) (subset_Icc_csInf_csSup hPl hPu)
        rw [Real.volume_Icc] at h
        exact ENNReal.toReal_le_of_le_ofReal hwP h
      have hvQ : (volume Q).toReal ≤ sSup Q - sInf Q := by
        have h := measure_mono (μ := volume) (subset_Icc_csInf_csSup hQl hQu)
        rw [Real.volume_Icc] at h
        exact ENNReal.toReal_le_of_le_ofReal hwQ h
      calc dist x y = |x - y| := Real.dist_eq _ _
        _ ≤ |x| + |y| := abs_sub _ _
        _ ≤ (volume P).toReal / 2 + (volume Q).toReal / 2 := add_le_add hx hy
        _ ≤ δ := by linarith
    -- The centred interval replacing a slice of finite length has the same length.
    have hcsvol : ∀ P : Set ℝ, volume P ≠ ∞ →
        volume {t : ℝ | P.Nonempty ∧ |t| ≤ (volume P).toReal / 2} = volume P := by
      intro P hfin
      rcases P.eq_empty_or_nonempty with rfl | hP
      · simp
      · have hinterval : {t : ℝ | P.Nonempty ∧ |t| ≤ (volume P).toReal / 2} =
            Icc (-(volume P).toReal / 2) ((volume P).toReal / 2) := by
          ext x
          simp [hP, abs_le, neg_div]
        rw [hinterval, Real.volume_Icc]
        convert ENNReal.ofReal_toReal hfin using 1
        congr 1
        ring
    intro d
    -- `R i` is the reflection in the coordinate plane `xⁱ = 0`.
    obtain ⟨R, hR⟩ : ∃ R : Fin d → Rn d → Rn d,
        ∀ i x, R i x = WithLp.toLp 2 (Function.update x.ofLp i (-x i)) := ⟨_, fun _ _ => rfl⟩
    have hRcont : ∀ i, Continuous (R i) := by
      intro i
      have : R i = fun x => WithLp.toLp 2 (Function.update x.ofLp i (-x i)) := funext (hR i)
      rw [this]
      apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
      apply continuous_pi
      intro k
      by_cases hki : k = i
      · subst k
        simpa only [Function.update_self] using
          (show Continuous (fun x : Rn d => -x i) by fun_prop)
      · simpa only [Function.update_of_ne hki] using
          (show Continuous (fun x : Rn d => x k) by fun_prop)
    have hRsame : ∀ i x, R i x i = -x i := by intro i x; simp [hR]
    have hRne : ∀ i k x, k ≠ i → R i x k = x k := by
      intro i k x hki; simp [hR, Function.update_of_ne hki]
    have hRinv : ∀ i x, R i (R i x) = x := by
      intro i x; ext k
      by_cases hki : k = i
      · subst k; rw [hRsame, hRsame, neg_neg]
      · rw [hRne i k _ hki, hRne i k _ hki]
    -- Taking closures preserves reflection symmetry.
    have hclos : ∀ (i : Fin d) (S : Set (Rn d)), (∀ x ∈ S, R i x ∈ S) →
        ∀ x ∈ closure S, R i x ∈ closure S := by
      intro i S hS x hx
      have h : closure S ⊆ R i ⁻¹' closure S :=
        closure_minimal (fun y hy => subset_closure (hS y hy))
          (isClosed_closure.preimage (hRcont i))
      exact h hx
    -- Changing the `j`-th coordinates changes `|x - y|²` only through `(xʲ - yʲ)²`.
    have hdist2 : ∀ (j : Fin d) (x y : Rn d) (a b : ℝ),
        dist (WithLp.toLp 2 (Function.update x.ofLp j a))
          (WithLp.toLp 2 (Function.update y.ofLp j b)) ^ 2 =
          dist x y ^ 2 - dist (x j) (y j) ^ 2 + dist a b ^ 2 := by
      intro j x y a b
      rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
      have hsum := Finset.sum_erase_add Finset.univ
        (fun i : Fin d => dist (x i) (y i) ^ 2) (Finset.mem_univ j)
      have hsum' := Finset.sum_erase_add Finset.univ
        (fun i : Fin d => dist (Function.update x.ofLp j a i)
          (Function.update y.ofLp j b i) ^ 2) (Finset.mem_univ j)
      have hrest : (∑ i ∈ Finset.univ.erase j,
          dist (Function.update x.ofLp j a i) (Function.update y.ofLp j b i) ^ 2) =
          ∑ i ∈ Finset.univ.erase j, dist (x i) (y i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Function.update_of_ne (Finset.mem_erase.mp hi).1]
      rw [hrest, Function.update_self, Function.update_self] at hsum'
      linarith
    -- One Steiner symmetrization in the direction `eⱼ` (closed up to keep compactness): the
    -- slice `sl x` of `K` along the line through `x` is replaced by the centred interval `S`.
    have hstep : ∀ (j : Fin d) (K : Set (Rn d)), IsCompact K →
        ∃ K' : Set (Rn d), IsCompact K' ∧ Metric.diam K' ≤ Metric.diam K ∧ volume K ≤ volume K' ∧
          (∀ x ∈ K', R j x ∈ K') ∧
          ∀ i, i ≠ j → (∀ x ∈ K, R i x ∈ K) → ∀ x ∈ K', R i x ∈ K' := by
      intro j K hK
      have hKb := hK.isBounded
      obtain ⟨sl, hsl⟩ : ∃ sl : Rn d → Set ℝ,
          ∀ x, sl x = {u : ℝ | WithLp.toLp 2 (Function.update x.ofLp j u) ∈ K} := ⟨_, fun _ => rfl⟩
      obtain ⟨S, hS⟩ : ∃ S : Set (Rn d),
          S = {x | (sl x).Nonempty ∧ |x j| ≤ (volume (sl x)).toReal / 2} := ⟨_, rfl⟩
      have hslR : ∀ x, sl (R j x) = sl x := by
        intro x
        rw [hsl, hsl, hR]
        ext u
        simp only [mem_ofPred_eq, Function.update_idem]
      -- The diameter does not increase.
      have hdiamS : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ Metric.diam K := by
        intro x hx y hy
        rw [hS] at hx hy
        obtain ⟨hxne, hxle⟩ := hx
        obtain ⟨hyne, hyle⟩ := hy
        have hsq : ∀ a ∈ sl x, ∀ b ∈ sl y,
            dist a b ^ 2 ≤ Metric.diam K ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2 := by
          intro a ha b hb
          rw [hsl] at ha hb
          have hd := Metric.dist_le_diam_of_mem hKb ha hb
          have hsq' := pow_le_pow_left₀ dist_nonneg hd 2
          rw [hdist2] at hsq'
          linarith
        have hD0 : 0 ≤ Metric.diam K ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2 := by
          obtain ⟨a, ha⟩ := hxne
          obtain ⟨b, hb⟩ := hyne
          exact (sq_nonneg _).trans (hsq a ha b hb)
        have hcross : ∀ a ∈ sl x, ∀ b ∈ sl y,
            dist a b ≤ Real.sqrt (Metric.diam K ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2) :=
          fun a ha b hb => Real.le_sqrt_of_sq_le (hsq a ha b hb)
        have hc := h1d _ _ hxne hyne _ hcross (x j) (y j) hxle hyle
        have hc2 : dist (x j) (y j) ^ 2 ≤
            Metric.diam K ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2 := by
          have := pow_le_pow_left₀ dist_nonneg hc 2
          rwa [Real.sq_sqrt hD0] at this
        have h2 : dist x y ^ 2 ≤ Metric.diam K ^ 2 := by linarith
        exact (pow_le_pow_iff_left₀ dist_nonneg Metric.diam_nonneg two_ne_zero).mp h2
      have hSb : Bornology.IsBounded S := Metric.isBounded_iff.mpr ⟨_, hdiamS⟩
      have hdiamS' : Metric.diam S ≤ Metric.diam K :=
        Metric.diam_le_of_forall_dist_le Metric.diam_nonneg hdiamS
      -- The volume does not decrease (Fubini in the splitting `ℝᵈ = ℝ × ℝᵈ⁻¹`, comparing with a
      -- measurable hull of `S`).
      have hvolS : volume K ≤ volume S := by
        obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by have := j.pos; omega⟩
        let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j
        let φ : ℝ × (Fin m → ℝ) → Rn (m + 1) := fun p => WithLp.toLp 2 (e.symm p)
        have hφ : MeasurePreserving φ volume volume :=
          (PiLp.volume_preserving_toLp (Fin (m + 1))).comp
            (MeasurePreserving.symm e (volume_preserving_piFinSuccAbove _ j))
        have hφcoord (t : ℝ) (z : Fin m → ℝ) : φ (t, z) j = t :=
          Fin.insertNth_apply_same (α := fun _ : Fin (m + 1) => ℝ) j t z
        have hT : MeasurableSet (toMeasurable volume S) := measurableSet_toMeasurable volume S
        have hTA : S ⊆ toMeasurable volume S := subset_toMeasurable volume S
        have hslice (t : ℝ) (z : Fin m → ℝ) : sl (φ (t, z)) = (fun s => φ (s, z)) ⁻¹' K := by
          rw [hsl]
          ext s
          change (WithLp.toLp 2 (Function.update (j.insertNth t z) j s) ∈ K) ↔
            WithLp.toLp 2 (j.insertNth s z) ∈ K
          rw [Fin.update_insertNth]
        have hfinite (z : Fin m → ℝ) : volume ((fun t => φ (t, z)) ⁻¹' K) ≠ ∞ := by
          have hproj : IsCompact ((fun x : Rn (m + 1) => x j) '' K) := hK.image (by fun_prop)
          have hsub : (fun t => φ (t, z)) ⁻¹' K ⊆ (fun x : Rn (m + 1) => x j) '' K := by
            intro t ht
            exact ⟨φ (t, z), ht, hφcoord t z⟩
          exact (measure_lt_top_of_subset hsub hproj.measure_lt_top.ne).ne
        calc
          volume K = volume (φ ⁻¹' K) :=
            (hφ.measure_preimage hK.measurableSet.nullMeasurableSet).symm
          _ = ∫⁻ z : Fin m → ℝ, volume ((fun t => φ (t, z)) ⁻¹' K) :=
            Measure.prod_apply_symm (hK.measurableSet.preimage hφ.measurable)
          _ = ∫⁻ z : Fin m → ℝ, volume {t : ℝ | ((fun t => φ (t, z)) ⁻¹' K).Nonempty ∧
                |t| ≤ (volume ((fun t => φ (t, z)) ⁻¹' K)).toReal / 2} := by
            apply lintegral_congr
            intro z
            exact (hcsvol _ (hfinite z)).symm
          _ ≤ ∫⁻ z : Fin m → ℝ, volume ((fun t => φ (t, z)) ⁻¹' toMeasurable volume S) := by
            apply lintegral_mono
            intro z
            apply measure_mono
            intro t ht
            apply hTA
            rw [hS]
            show (sl (φ (t, z))).Nonempty ∧ |φ (t, z) j| ≤ (volume (sl (φ (t, z)))).toReal / 2
            rw [hφcoord, hslice]
            exact ht
          _ = volume (φ ⁻¹' toMeasurable volume S) :=
            (Measure.prod_apply_symm (hT.preimage hφ.measurable)).symm
          _ = volume (toMeasurable volume S) := hφ.measure_preimage hT.nullMeasurableSet
          _ = volume S := measure_toMeasurable S
      -- `S` is symmetric in `xʲ = 0`.
      have hSj : ∀ x ∈ S, R j x ∈ S := by
        intro x hx
        rw [hS] at hx ⊢
        refine ⟨by rw [hslR]; exact hx.1, ?_⟩
        rw [hslR, hRsame, abs_neg]
        exact hx.2
      -- Symmetry of `K` in another coordinate plane `xⁱ = 0` passes to `S`.
      have hSi : ∀ i, i ≠ j → (∀ x ∈ K, R i x ∈ K) → ∀ x ∈ S, R i x ∈ S := by
        intro i hij hKi x hx
        have hsli : sl (R i x) = sl x := by
          rw [hsl, hsl]
          ext u
          simp only [mem_ofPred_eq]
          have hcomm : WithLp.toLp 2 (Function.update (R i x).ofLp j u) =
              R i (WithLp.toLp 2 (Function.update x.ofLp j u)) := by
            ext k
            by_cases hkj : k = j
            · subst k
              rw [hRne i j _ (Ne.symm hij)]
              simp
            · by_cases hki : k = i
              · subst k
                rw [hRsame]
                simp [Function.update_of_ne hkj, hRsame]
              · rw [hRne i k _ hki]
                simp [Function.update_of_ne hkj, hRne i k _ hki]
          rw [hcomm]
          constructor
          · intro h
            simpa [hRinv] using hKi _ h
          · exact hKi _
        rw [hS] at hx ⊢
        refine ⟨by rw [hsli]; exact hx.1, ?_⟩
        rw [hsli, hRne i j x (Ne.symm hij)]
        exact hx.2
      refine ⟨closure S, hSb.isCompact_closure, ?_, ?_, hclos j S hSj,
        fun i hij hKi => hclos i S (hSi i hij hKi)⟩
      · rw [Metric.diam_closure]
        exact hdiamS'
      · exact hvolS.trans (measure_mono subset_closure)
    -- Symmetrizing in every coordinate direction in turn.
    have hfin : ∀ (F : Finset (Fin d)) (K : Set (Rn d)), IsCompact K →
        ∃ K' : Set (Rn d), IsCompact K' ∧ Metric.diam K' ≤ Metric.diam K ∧ volume K ≤ volume K' ∧
          ∀ i ∈ F, ∀ x ∈ K', R i x ∈ K' := by
      intro F
      induction F using Finset.induction_on with
      | empty => intro K hK; exact ⟨K, hK, le_rfl, le_rfl, by simp⟩
      | @insert i F hi ih =>
        intro K hK
        obtain ⟨K₁, hK₁, hd₁, hv₁, hs₁⟩ := ih K hK
        obtain ⟨K₂, hK₂, hd₂, hv₂, hs₂, hp₂⟩ := hstep i K₁ hK₁
        refine ⟨K₂, hK₂, hd₂.trans hd₁, hv₁.trans hv₂, ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact hs₂
        · exact hp₂ k (fun h => hi (h ▸ hk)) (hs₁ k hk)
    -- The result `K` for `closure s` is centrally symmetric, hence lies in `B̄_{diam K / 2}(0)`.
    intro s hs
    obtain ⟨K, hK, hdK, hvK, hsymK⟩ := hfin Finset.univ (closure s) hs.isCompact_closure
    have hneg : ∀ x ∈ K, -x ∈ K := by
      intro x hx
      have hmem : ∀ F : Finset (Fin d),
          WithLp.toLp 2 (fun k => if k ∈ F then -x k else x k) ∈ K := by
        intro F
        induction F using Finset.induction_on with
        | empty => simpa using hx
        | @insert i F hi ih =>
          have h := hsymK i (Finset.mem_univ i) _ ih
          convert h using 1
          ext k
          by_cases hki : k = i
          · subst k
            simp [hR, hi]
          · simp [hR, hki]
      have heq : (WithLp.toLp 2 fun k => -x k) = -x := by
        ext k
        rfl
      simpa only [Finset.mem_univ, ite_true, heq] using hmem Finset.univ
    have hsub : K ⊆ Metric.closedBall 0 (Metric.diam K / 2) := by
      intro x hx
      have h := Metric.dist_le_diam_of_mem hK.isBounded hx (hneg x hx)
      rw [dist_eq_norm_sub, sub_neg_eq_add, ← two_smul ℝ, norm_smul] at h
      norm_num at h
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    have hdK' : Metric.diam K ≤ Metric.diam s := hdK.trans (Metric.diam_closure s).le
    calc volume s ≤ volume (closure s) := measure_mono subset_closure
      _ ≤ volume K := hvK
      _ ≤ volume (Metric.closedBall (0 : Rn d) (Metric.diam K / 2)) := measure_mono hsub
      _ = ENNReal.ofReal ((Metric.diam K / 2) ^ d) * volume (Metric.ball (0 : Rn d) 1) := by
        rw [Measure.addHaar_closedBall volume 0 (by positivity), finrank_euclideanSpace_fin]
      _ ≤ ENNReal.ofReal ((Metric.diam s / 2) ^ d) * volume (Metric.ball (0 : Rn d) 1) := by
        gcongr
  intro n N μ A hμK hden
  have : IsFiniteMeasureOnCompacts μ := ⟨hμK⟩
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ≥0∞, ω = volume (Metric.ball (0 : Rn n) 1) := ⟨_, rfl⟩
  rw [← hω] at hden
  have hω0 : ω ≠ 0 := hω ▸ (Metric.measure_ball_pos volume (0 : Rn n) one_pos).ne'
  have hωtop : ω ≠ ∞ := hω ▸ measure_ball_lt_top.ne
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0,
      c = (volume : Measure (Rn n)).addHaarScalarFactor μH[(n : ℝ)] := ⟨_, rfl⟩
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    rw [hc]
    exact_mod_cast Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n
  have hHE : ∀ s : Set (Rn N), μHE[n] s = c * μH[(n : ℝ)] s := by
    intro s
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ← hc, ENNReal.smul_def,
      smul_eq_mul]
  -- Step 2 (normalization, Simon (2.9)): `μHE[n] = c • μH[n]` with `c 2ⁿ ≤ ω_n`, because
  -- `Lⁿ ≤ (ω_n / 2ⁿ) μH[n]` on `ℝⁿ` by Step 1 while `c • μH[n] = Lⁿ` there.
  have hcω : (c : ℝ≥0∞) * 2 ^ n ≤ ω := by
    have hle : ((2 : ℝ≥0∞) ^ n / ω) • (volume : Measure (Rn n)) ≤ μH[(n : ℝ)] := by
      rw [Measure.hausdorffMeasure]
      refine Measure.le_mkMetric _ _ 1 one_pos fun s hs => ?_
      have hfin : Metric.ediam s ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hs
      have hb : Bornology.IsBounded s := Metric.isBounded_iff_ediam_ne_top.mpr hfin
      have hdiam : Metric.ediam s = ENNReal.ofReal (Metric.diam s) :=
        (ENNReal.ofReal_toReal hfin).symm
      have hs' := hiso n s hb
      rw [← hω] at hs'
      rw [Measure.smul_apply, smul_eq_mul, hdiam, ENNReal.rpow_natCast]
      calc (2 : ℝ≥0∞) ^ n / ω * volume s
          ≤ (2 : ℝ≥0∞) ^ n / ω * (ENNReal.ofReal ((Metric.diam s / 2) ^ n) * ω) := by
            gcongr
        _ = (2 : ℝ≥0∞) ^ n * ENNReal.ofReal ((Metric.diam s / 2) ^ n) := by
            rw [mul_comm (ENNReal.ofReal _) ω, ← mul_assoc, ENNReal.div_mul_cancel hω0 hωtop]
        _ = ENNReal.ofReal (Metric.diam s) ^ n := by
            rw [← ENNReal.ofReal_pow Metric.diam_nonneg,
              show (2 : ℝ≥0∞) ^ n = ENNReal.ofReal (2 ^ n) by
                rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat],
              ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
            congr 2
            ring
    have hB := hle (Metric.ball (0 : Rn n) 1)
    rw [Measure.smul_apply, smul_eq_mul, ← hω, ENNReal.div_mul_cancel hω0 hωtop] at hB
    have hvol : (c : ℝ≥0∞) * μH[(n : ℝ)] (Metric.ball (0 : Rn n) 1) = ω := by
      have h := congrArg (fun ν : Measure (Rn n) => ν (Metric.ball 0 1))
        (EuclideanSpace.euclideanHausdorffMeasure_eq_volume n)
      simp only at h
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ← hc, ENNReal.smul_def,
        smul_eq_mul] at h
      rw [h, hω]
    calc (c : ℝ≥0∞) * 2 ^ n ≤ c * μH[(n : ℝ)] (Metric.ball (0 : Rn n) 1) := by gcongr
      _ = ω := hvol
  -- Step 3 (density, covering): for `x ∈ A` and small `ρ`, `ω_n ρⁿ ≤ (1 + ε_k) μ(B̄_ρ(x))`; by
  -- Besicovitch, such balls with `ρ < 1/(k+1)` cover `A` with `∑ μ(B̄_ρ(x)) ≤ μ(A) + ε_k`.
  obtain ⟨ε, hε⟩ : ∃ ε : ℕ → ℝ≥0∞, ε = fun k : ℕ => ((k : ℝ≥0∞) + 1)⁻¹ := ⟨_, rfl⟩
  have hε0 : ∀ k, ε k ≠ 0 := fun k => by simp [hε]
  have hεtop : ∀ k, ε k ≠ ∞ := fun k => by simp [hε]
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    rw [hε]
    convert h using 2 with k
    simp
  have hfine : ∀ k : ℕ, ∀ x ∈ A, ∀ δ > 0,
      ((fun x : Rn N => {ρ : ℝ | ρ ∈ Ioo 0 (1 / ((k : ℝ) + 1)) ∧
        ω * ENNReal.ofReal (ρ ^ n) ≤ (1 + ε k) * μ (Metric.closedBall x ρ)}) x ∩
          Ioo 0 δ).Nonempty := by
    intro k x hx δ hδ
    have hlt : ω < (1 + ε k) * ω := by
      rw [add_mul, one_mul]
      exact ENNReal.lt_add_right hωtop (mul_ne_zero (hε0 k) hω0)
    have hlim : Tendsto (fun ρ : ℝ => (1 + ε k) *
        (μ (Metric.closedBall x ρ) / ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 ((1 + ε k) * ω)) :=
      ENNReal.Tendsto.const_mul (hden x hx)
        (Or.inr (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hεtop k⟩))
    have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
        ω < (1 + ε k) * (μ (Metric.closedBall x ρ) / ENNReal.ofReal (ρ ^ n)) :=
      hlim.eventually (lt_mem_nhds hlt)
    have hev2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 (min δ (1 / ((k : ℝ) + 1))) :=
      Ioo_mem_nhdsGT (lt_min hδ (by positivity))
    obtain ⟨ρ, hρ1, hρ2⟩ := (hev.and hev2).exists
    refine ⟨ρ, ⟨⟨hρ2.1, hρ2.2.trans_le (min_le_right _ _)⟩, ?_⟩,
      hρ2.1, hρ2.2.trans_le (min_le_left _ _)⟩
    have hpos : ENNReal.ofReal (ρ ^ n) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact pow_pos hρ2.1 n
    rw [← mul_div_assoc] at hρ1
    exact ((ENNReal.lt_div_iff_mul_lt (Or.inl hpos) (Or.inl ENNReal.ofReal_ne_top)).mp hρ1).le
  choose T r hTc hTA hr hcov hsum using fun k : ℕ =>
    Besicovitch.exists_closedBall_covering_tsum_measure_le μ (hε0 k)
      (fun x : Rn N => {ρ : ℝ | ρ ∈ Ioo 0 (1 / ((k : ℝ) + 1)) ∧
        ω * ENNReal.ofReal (ρ ^ n) ≤ (1 + ε k) * μ (Metric.closedBall x ρ)}) A (hfine k)
  have : ∀ k, Countable (T k) := fun k => (hTc k).to_subtype
  have hdiam : ∀ k (i : T k), Metric.ediam (Metric.closedBall (i : Rn N) (r k i)) ≤
      ENNReal.ofReal (2 * r k i) := by
    intro k i
    apply Metric.ediam_le_of_forall_dist_le
    intro y hy z hz
    rw [Metric.mem_closedBall] at hy hz
    linarith [dist_triangle_right y z (i : Rn N)]
  have hH : μH[(n : ℝ)] A ≤ liminf (fun k => ∑' i : T k,
      Metric.ediam (Metric.closedBall (i : Rn N) (r k i)) ^ (n : ℝ)) atTop := by
    refine Measure.hausdorffMeasure_le_liminf_tsum (n : ℝ) A
      (fun k : ℕ => ENNReal.ofReal (2 * (1 / ((k : ℝ) + 1)))) ?_
      (fun k (i : T k) => Metric.closedBall (i : Rn N) (r k i)) ?_ ?_
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
      rw [mul_zero] at h
      simpa using ENNReal.tendsto_ofReal h
    · refine Eventually.of_forall fun k i => (hdiam k i).trans ?_
      obtain ⟨⟨-, h1⟩, -⟩ := hr k i i.2
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · refine Eventually.of_forall fun k => ?_
      intro y hy
      obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hcov k hy)
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hyx⟩
  -- Step 4: `c (diam B̄_ρ)ⁿ ≤ c 2ⁿ ρⁿ ≤ ω_n ρⁿ`, so `c ∑ (diam B̄)ⁿ ≤ (1 + ε_k)(μ(A) + ε_k)`.
  have hbound : ∀ k, (c : ℝ≥0∞) * ∑' i : T k,
      Metric.ediam (Metric.closedBall (i : Rn N) (r k i)) ^ (n : ℝ) ≤
        (1 + ε k) * (μ A + ε k) := by
    intro k
    rw [← ENNReal.tsum_mul_left]
    calc ∑' i : T k, (c : ℝ≥0∞) * Metric.ediam (Metric.closedBall (i : Rn N) (r k i)) ^ (n : ℝ)
        ≤ ∑' i : T k, (1 + ε k) * μ (Metric.closedBall (i : Rn N) (r k i)) := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          obtain ⟨⟨h0, -⟩, h2⟩ := hr k i i.2
          calc (c : ℝ≥0∞) * Metric.ediam (Metric.closedBall (i : Rn N) (r k i)) ^ (n : ℝ)
              ≤ c * ENNReal.ofReal (2 * r k i) ^ (n : ℝ) := by
                gcongr
                exact hdiam k i
            _ = c * 2 ^ n * ENNReal.ofReal (r k i ^ n) := by
                rw [ENNReal.rpow_natCast, ENNReal.ofReal_mul (by norm_num), mul_pow,
                  ENNReal.ofReal_ofNat, ENNReal.ofReal_pow h0.le, mul_assoc]
            _ ≤ ω * ENNReal.ofReal (r k i ^ n) := by gcongr
            _ ≤ (1 + ε k) * μ (Metric.closedBall (i : Rn N) (r k i)) := h2
      _ = (1 + ε k) * ∑' i : T k, μ (Metric.closedBall (i : Rn N) (r k i)) :=
          ENNReal.tsum_mul_left
      _ ≤ (1 + ε k) * (μ A + ε k) := by
          gcongr
          exact hsum k
  -- Step 5: let `k → ∞`.
  have hlimD : Tendsto (fun k => (1 + ε k) * (μ A + ε k)) atTop (𝓝 (μ A)) := by
    have h1 : Tendsto (fun k => 1 + ε k) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hεlim
    have h2 : Tendsto (fun k => μ A + ε k) atTop (𝓝 (μ A)) := by
      simpa using tendsto_const_nhds.add hεlim
    simpa using ENNReal.Tendsto.mul h1 (Or.inl one_ne_zero) h2 (Or.inr ENNReal.one_ne_top)
  have hS : ∀ k, ∑' i : T k, Metric.ediam (Metric.closedBall (i : Rn N) (r k i)) ^ (n : ℝ) ≤
      (1 + ε k) * (μ A + ε k) / c := fun k =>
    (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl ENNReal.coe_ne_top)).mpr
      (by rw [mul_comm]; exact hbound k)
  have hlim2 : Tendsto (fun k => (1 + ε k) * (μ A + ε k) / c) atTop (𝓝 (μ A / c)) :=
    ENNReal.Tendsto.div_const hlimD (Or.inr hc0)
  calc μHE[n] A = c * μH[(n : ℝ)] A := hHE A
    _ ≤ c * liminf (fun k => ∑' i : T k,
        Metric.ediam (Metric.closedBall (i : Rn N) (r k i)) ^ (n : ℝ)) atTop := by gcongr
    _ ≤ c * liminf (fun k => (1 + ε k) * (μ A + ε k) / c) atTop := by
        gcongr
        exact Filter.liminf_le_liminf (Eventually.of_forall hS)
    _ = c * (μ A / c) := by rw [hlim2.liminf_eq]
    _ = μ A := ENNReal.mul_div_cancel hc0 ENNReal.coe_ne_top
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
/-- **Equal `n`-dimensional densities force equality** (proof of Simon Ch. 3, Theorem 4.3, the
final identification `μ_E = Hⁿ ⌞ ∂*E`; Besicovitch differentiation, Simon Ch. 1, Theorems
3.22–3.24, and Radon–Nikodym). Let `μ, σ` be measures on `ℝᴺ`, finite on compact sets, with
`μ ≪ σ`, such that for `σ`-a.e. `x` both `μ(B̄_ρ(x))/ρⁿ` and `σ(B̄_ρ(x))/ρⁿ` tend to
`ωₙ = Lⁿ(B_1(0))` as `ρ ↓ 0`. Then `μ = σ`: by Besicovitch `μ(B̄_ρ(x))/σ(B̄_ρ(x)) → dμ/dσ(x)`
`σ`-a.e., the density hypotheses make this ratio tend to `ωₙ/ωₙ = 1`, and the Lebesgue
decomposition of `μ` with respect to `σ` has no singular part, so `μ = (dμ/dσ) σ = σ`. -/
theorem Submission.deGiorgiRH_measure_eq_of_density : ∀ (n N : ℕ) (μ σ : Measure (Rn N)), (∀ K : Set (Rn N), IsCompact K → μ K < ∞) → (∀ K : Set (Rn N), IsCompact K → σ K < ∞) → μ ≪ σ → (∀ᵐ x ∂σ, Tendsto (fun ρ : ℝ ↦ μ (Metric.closedBall x ρ) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : Rn n) 1))) ∧ Tendsto (fun ρ : ℝ ↦ σ (Metric.closedBall x ρ) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : Rn n) 1)))) → μ = σ := by
  intro n N μ σ hμ hσ hac hdens
  -- Step 1: finiteness on compacts makes `μ` and `σ` locally finite, hence σ-finite on `ℝᴺ`.
  have : IsFiniteMeasureOnCompacts μ := ⟨hμ⟩
  have : IsFiniteMeasureOnCompacts σ := ⟨hσ⟩
  -- `ωₙ = Lⁿ(B_1(0)) ∈ (0, ∞)`.
  have hω₀ : volume (Metric.ball (0 : Rn n) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume (0 : Rn n) one_pos).ne'
  have hω : volume (Metric.ball (0 : Rn n) 1) ≠ ∞ := measure_ball_lt_top.ne
  -- Steps 2–4: by Besicovitch differentiation `μ(B̄_ρ(x))/σ(B̄_ρ(x)) → dμ/dσ(x)` for `σ`-a.e. `x`,
  -- while the density hypotheses force this ratio to tend to `ωₙ/ωₙ = 1`.
  have hD : μ.rnDeriv σ =ᵐ[σ] 1 := by
    filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ σ, hdens] with x hx ⟨hxμ, hxσ⟩
    have hq := ENNReal.Tendsto.div hxμ (Or.inl hω₀) hxσ (Or.inl hω)
    rw [ENNReal.div_self hω₀ hω] at hq
    refine tendsto_nhds_unique hx (hq.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
    -- Cancel the finite nonzero factor `(ρⁿ)⁻¹`.
    have hc : ENNReal.ofReal (ρ ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hρ n)).ne'
    rw [div_eq_mul_inv (μ _), div_eq_mul_inv (σ _)]
    exact ENNReal.mul_div_mul_right _ _ (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
      (ENNReal.inv_ne_top.2 hc)
  -- Step 5: Radon–Nikodym: the singular part vanishes as `μ ≪ σ`, so `μ = (dμ/dσ) σ = σ`.
  calc μ = μ.singularPart σ + σ.withDensity (μ.rnDeriv σ) :=
        Measure.haveLebesgueDecomposition_add μ σ
    _ = σ := by
      rw [Measure.singularPart_eq_zero_of_ac hac, zero_add, withDensity_congr_ae hD,
        withDensity_one]

/-- **Simon Ch. 3, Theorem 4.3 (p. 81), first part, global case**: `∂*E` is countably
`n`-rectifiable and `μ_E = Hⁿ⌞∂*E` (`chapter-03.txt` lines 588–589). The printed proof of this
part is the sketch "By 1.6 and 3.6 of Ch. 1" (line 604); it is completed by Steps 3–8 of the
parent node with `U = ℝ^{n+ℓ}`, using (RT), the measure form of Theorem 1.6 "⇐", and (AT),
Theorem 1.6. Let `μ` be finite on compact sets and carried by the measurable set `S`, with an
approximate tangent plane of multiplicity `1` at every point of `S`, and put `σ = Hⁿ⌞S`.
Step 3: `μ(B̄_ρ(x))/ρⁿ → ωₙ` at every `x ∈ S` (`deGiorgiRH_measure_density_of_tangentPlane`).
Steps 4, 6: hence `Hⁿ(A) ≤ μ(A) ≤ 2ⁿ Hⁿ(A)` for every `A ⊆ S` (`deGiorgiRH_hausdorff_le_of_density`,
`deGiorgiRH_measure_le_two_pow_mul_hausdorff`).
Step 5: (RT) gives a countably `n`-rectifiable `R` with `μ(Rᶜ) = 0`; `S \ R` is `μ`-null, hence
`Hⁿ`-null, so `S ⊆ R ∪ (S \ R)` is countably `n`-rectifiable.
Step 8 (preliminaries): `σ` is finite on compact sets and `μ ≪ σ`.
Step 7: by (AT) "⇒", `S` has an approximate tangent space at `Hⁿ`-a.e. point, and there
`σ(B̄_ρ(x))/ρⁿ → ωₙ` (`deGiorgiRH_hausdorff_density_of_approxTangent`).
Step 8: the density comparison `deGiorgiRH_measure_eq_of_density` gives `μ = σ`. -/
theorem Submission.deGiorgiRH_locallyFinite_case : (∀ (n ℓ : ℕ) (μ : Measure (Rn (n + ℓ))), (∀ K : Set (Rn (n + ℓ)), IsCompact K → μ K < ∞) → (∀ᵐ x ∂μ, ∃ (P : Submodule ℝ (Rn (n + ℓ))) (θ : ℝ), 0 < θ ∧ HasApproxTangentPlaneWithMultiplicity n μ x P θ) → ∃ R : Set (Rn (n + ℓ)), MeasurableSet R ∧ CountablyRectifiable n R ∧ μ Rᶜ = 0) → ApproximateTangentCharacterization → ∀ (n ℓ : ℕ) (S : Set (Rn (n + ℓ))) (μ : Measure (Rn (n + ℓ))), (∀ K : Set (Rn (n + ℓ)), IsCompact K → μ K < ∞) → MeasurableSet S → μ Sᶜ = 0 → (∀ x ∈ S, ∃ P : Submodule ℝ (Rn (n + ℓ)), HasApproxTangentPlaneWithMultiplicity n μ x P 1) → CountablyRectifiable n S ∧ μ = (μHE[n] : Measure (Rn (n + ℓ))).restrict S := by
  intro RT AT n ℓ S μ hμK hS hμS htan
  -- Step 3: `μ` has density `ωₙ` at every point of `S`.
  have hdens : ∀ x ∈ S, Tendsto (fun ρ : ℝ ↦ μ (Metric.closedBall x ρ) / ENNReal.ofReal (ρ ^ n))
      (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : Rn n) 1))) := fun x hx ↦ by
    obtain ⟨P, hP⟩ := htan x hx
    exact Submission.deGiorgiRH_measure_density_of_tangentPlane n (n + ℓ) μ x P
      ⟨1, one_pos, hμK _ (isCompact_closedBall x 1)⟩ hP
  -- Steps 4 and 6: `Hⁿ(A) ≤ μ(A) ≤ 2ⁿ Hⁿ(A)` for every `A ⊆ S`.
  have hHle : ∀ A ⊆ S, μHE[n] A ≤ μ A := fun A hA ↦
    Submission.deGiorgiRH_hausdorff_le_of_density n (n + ℓ) μ A hμK fun x hx ↦ hdens x (hA hx)
  have hμle : ∀ A ⊆ S, μ A ≤ 2 ^ n * μHE[n] A := fun A hA ↦
    Submission.deGiorgiRH_measure_le_two_pow_mul_hausdorff n (n + ℓ) μ A
      fun x hx ↦ hdens x (hA hx)
  -- Step 5: (RT) gives a rectifiable `R` carrying `μ`; `S \ R` is `μ`-null, hence `Hⁿ`-null.
  have hCR : CountablyRectifiable n S := by
    have hae : ∀ᵐ x ∂μ, ∃ (P : Submodule ℝ (Rn (n + ℓ))) (θ : ℝ), 0 < θ ∧
        HasApproxTangentPlaneWithMultiplicity n μ x P θ := by
      filter_upwards [mem_ae_iff.2 hμS] with x hx
      obtain ⟨P, hP⟩ := htan x hx
      exact ⟨P, 1, one_pos, hP⟩
    obtain ⟨R, -, hR, hμR⟩ := RT n ℓ μ hμK hae
    have hSR : μHE[n] (S \ R) = 0 := nonpos_iff_eq_zero.1 <|
      (hHle _ sdiff_subset).trans (measure_mono_null (sdiff_subset_compl S R) hμR).le
    have hU : CountablyRectifiable n (⋃ i : ℕ, if i = 0 then R else S \ R) :=
      Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion _ fun i ↦ by
        split_ifs
        · exact hR
        · exact Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero hSR
    refine hU.mono fun y hy ↦ mem_iUnion.2 ?_
    by_cases hyR : y ∈ R
    · exact ⟨0, by simpa using hyR⟩
    · exact ⟨1, by simpa using And.intro hy hyR⟩
  -- Step 8 (preliminaries): `σ = Hⁿ⌞S` is finite on compact sets and `μ ≪ σ`.
  have hHK : ∀ K : Set (Rn (n + ℓ)), IsCompact K → μHE[n] (S ∩ K) < ∞ := fun K hK ↦
    ((hHle _ inter_subset_left).trans (measure_mono inter_subset_right)).trans_lt (hμK K hK)
  have hσK : ∀ K : Set (Rn (n + ℓ)), IsCompact K →
      (μHE[n] : Measure (Rn (n + ℓ))).restrict S K < ∞ := fun K hK ↦ by
    rw [Measure.restrict_apply' hS, inter_comm]
    exact hHK K hK
  have hac : μ ≪ (μHE[n] : Measure (Rn (n + ℓ))).restrict S := by
    refine Measure.AbsolutelyContinuous.mk fun s hs hσs ↦ ?_
    rw [Measure.restrict_apply hs] at hσs
    have h₁ : μ (s ∩ S) = 0 := nonpos_iff_eq_zero.1 <|
      (hμle _ inter_subset_right).trans_eq (by rw [hσs, mul_zero])
    have h₂ : μ (s \ S) = 0 := measure_mono_null (sdiff_subset_compl s S) hμS
    exact nonpos_iff_eq_zero.1 <|
      (measure_le_inter_add_sdiff μ s S).trans_eq (by rw [h₁, h₂, add_zero])
  -- Step 7: by (AT) "⇒", `S` has an approximate tangent space at `Hⁿ`-a.e. point; there `σ` has
  -- density `ωₙ`, and so has `μ` (Step 3).
  have hT := (AT n ℓ S hS.nullMeasurableSet hHK).1 hCR
  have hσdens : ∀ᵐ x ∂(μHE[n] : Measure (Rn (n + ℓ))).restrict S,
      Tendsto (fun ρ : ℝ ↦ μ (Metric.closedBall x ρ) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0)
          (𝓝 (volume (Metric.ball (0 : Rn n) 1))) ∧
        Tendsto (fun ρ : ℝ ↦ (μHE[n] : Measure (Rn (n + ℓ))).restrict S (Metric.closedBall x ρ) /
          ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : Rn n) 1))) := by
    rw [ae_restrict_iff' hS]
    filter_upwards [hT] with x hx hxS
    obtain ⟨P, hP⟩ := hx hxS
    refine ⟨hdens x hxS, (Submission.deGiorgiRH_hausdorff_density_of_approxTangent n (n + ℓ) S x
      P ⟨1, one_pos, hHK _ (isCompact_closedBall x 1)⟩ hP).congr fun ρ ↦ ?_⟩
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm]
  -- Step 8: density comparison of `μ` and `σ`.
  exact ⟨hCR, Submission.deGiorgiRH_measure_eq_of_density n (n + ℓ) μ _ hμK hσK hac hσdens⟩

/-- **A measure with unit-multiplicity tangent planes on its carrier is `Hⁿ ⌞ S`** (Simon Ch. 3,
proof of Thm. 4.3, parent proof Parts 5c–5d; erratum E4: chapter-03.txt line 604 only sketches
this, as Thm. 1.6 concerns `Hⁿ ⌞ M` rather than `μ_E`, so the measure form (RT) of 1.6 "⇐" and
density comparison are used instead). Assume (RT) and (AT) (Thm. 1.6). Let `U ⊆ ℝ^{n+ℓ}` be open
and `μ` a measure vanishing off `U`, finite on compact subsets of `U`, and carried by a measurable
`S ⊆ U` at each point of which it has an approximate tangent plane with multiplicity `1`. Then
`S` is countably `n`-rectifiable and `μ = Hⁿ ⌞ S`. Exhaust `U` by open `W_i` with compact closure
in `U`: each `μ ⌞ W_i` is finite on all compacts, carried by `S ∩ W_i` and keeps the tangent
planes there, so the globally finite case gives `S ∩ W_i` rectifiable and
`μ ⌞ W_i = Hⁿ ⌞ (S ∩ W_i)`. Now `S = ⋃ᵢ S ∩ W_i`, and `μ`, `Hⁿ ⌞ S` are carried by
`U = ⋃ᵢ W_i`. -/
theorem Submission.deGiorgi_rectifiable_measure_eq_hausdorff : (∀ (n ℓ : ℕ) (μ : Measure (Rn (n + ℓ))), (∀ K : Set (Rn (n + ℓ)), IsCompact K → μ K < ∞) → (∀ᵐ x ∂μ, ∃ (P : Submodule ℝ (Rn (n + ℓ))) (θ : ℝ), 0 < θ ∧ HasApproxTangentPlaneWithMultiplicity n μ x P θ) → ∃ R : Set (Rn (n + ℓ)), MeasurableSet R ∧ CountablyRectifiable n R ∧ μ Rᶜ = 0) → ApproximateTangentCharacterization → ∀ (n ℓ : ℕ) (U S : Set (Rn (n + ℓ))) (μ : Measure (Rn (n + ℓ))), IsOpen U → μ Uᶜ = 0 → (∀ K : Set (Rn (n + ℓ)), IsCompact K → K ⊆ U → μ K < ∞) → MeasurableSet S → S ⊆ U → μ Sᶜ = 0 → (∀ x ∈ S, ∃ P : Submodule ℝ (Rn (n + ℓ)), HasApproxTangentPlaneWithMultiplicity n μ x P 1) → CountablyRectifiable n S ∧ μ = (μHE[n] : Measure (Rn (n + ℓ))).restrict S := by
  intro RT AT n ℓ U S μ hU hμU hμK hS hSU hμS htan
  -- Step 2 (localization): open `W_i` with compact closure in `U` and `⋃ᵢ W_i = U`.
  obtain ⟨W, hW, hWU⟩ := Submission.deGiorgiRH_open_exhaustion (n + ℓ) U hU
  -- Steps 3–8 for `μ ⌞ W_i` and its carrier `S ∩ W_i` (sibling `locally_finite_case`).
  have hloc : ∀ i, CountablyRectifiable n (S ∩ W i) ∧
      μ.restrict (W i) = (μHE[n] : Measure (Rn (n + ℓ))).restrict (S ∩ W i) := by
    intro i
    obtain ⟨hWo, hWc, hWsub⟩ := hW i
    refine Submission.deGiorgiRH_locallyFinite_case RT AT n ℓ (S ∩ W i) (μ.restrict (W i))
      (fun K _ ↦ ?_) (hS.inter hWo.measurableSet) ?_ fun x hx ↦ ?_
    · -- `(μ ⌞ W_i)(K) ≤ μ(closure W_i) < ∞`, as `closure W_i` is a compact subset of `U`.
      calc μ.restrict (W i) K ≤ μ.restrict (W i) univ := measure_mono (subset_univ K)
        _ = μ (W i) := Measure.restrict_apply_univ _
        _ ≤ μ (closure (W i)) := measure_mono subset_closure
        _ < ∞ := hμK _ hWc hWsub
    · -- `(μ ⌞ W_i)((S ∩ W_i)ᶜ) = μ(W_i ∖ S) ≤ μ(Sᶜ) = 0`.
      rw [Measure.restrict_apply' hWo.measurableSet]
      exact measure_mono_null (fun y hy hyS ↦ hy.1 ⟨hyS, hy.2⟩) hμS
    · -- Tangent planes are local: `W_i` is an open neighbourhood of `x` (sibling
      -- `tangent_restrict`).
      obtain ⟨P, hP⟩ := htan x hx.1
      exact ⟨P, Submission.deGiorgiRH_tangentPlane_restrict_open n (n + ℓ) μ (W i) x P 1 hWo
        hx.2 hP⟩
  -- Step 5: `S = ⋃ᵢ S ∩ W_i` (as `S ⊆ U`) is a countable union of rectifiable sets.
  have hSW : S = ⋃ i, S ∩ W i := by rw [← inter_iUnion, hWU, inter_eq_left.2 hSU]
  refine ⟨?_, ?_⟩
  · rw [hSW]
    exact Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion _ fun i ↦ (hloc i).1
  -- Step 8: `μ` and `Hⁿ ⌞ S` are carried by `U = ⋃ᵢ W_i` and agree on every `W_i`.
  have hμU' : μ.restrict U = μ := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hμU)
  have hσU : ((μHE[n] : Measure (Rn (n + ℓ))).restrict S).restrict U =
      (μHE[n] : Measure (Rn (n + ℓ))).restrict S := by
    rw [Measure.restrict_restrict hU.measurableSet, inter_eq_right.2 hSU]
  rw [← hμU', ← hσU, ← hWU, Measure.restrict_iUnion_congr]
  intro i
  rw [(hloc i).2, Measure.restrict_restrict (hW i).1.measurableSet, inter_comm]
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
/-- **Simon Ch. 3, (4.1), direction "⇐"** (`chapter-03.txt` lines 555–573, with Ch. 2 (2.1),
`chapter-02.txt` lines 477–484): a Gauss–Green pair `(μ, ν)` for `(U, E)` forces
`χ_E ∈ BV_loc(U)`. `χ_E` is bounded and a.e. equal to the indicator of a measurable set, hence
locally integrable. For `W ⊂⊂ U` and a `C¹` field `g` with `tsupport g ⊆ W`, `div g` vanishes off
`tsupport g`, so `∫_W χ_E div g = ∫_{E ∩ U} div g`, which is `-∫ g · ν dμ` by (4.1). As `|ν| = 1`
`μ`-a.e. and `g = 0` off `W̄`, this is at most `μ(W̄) sup |g|`. -/
theorem Submission.gaussGreenRep_isLocallyBV_of_pair : ∀ (N : ℕ) (U E : Set (Rn N))
    (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → NullMeasurableSet E volume →
    IsGaussGreenPair U E μ ν → HasLocallyFinitePerimeter U E := by
  intro N U E μ ν hU hE hpair
  obtain ⟨-, hμK, -, hν, hGG⟩ := hpair
  refine ⟨hU, ?_, fun W hWo hWU ↦ ⟨(μ (closure W)).toReal, ENNReal.toReal_nonneg,
    fun g hg hgW ↦ ?_⟩⟩
  · -- `χ_E` is a.e. the indicator of the measurable hull of `E`.
    exact (((locallyIntegrable_const (1 : ℝ)).indicator
      (measurableSet_toMeasurable volume E)).congr
        (indicator_ae_eq_of_ae_eq_set hE.toMeasurable_ae_eq)).locallyIntegrableOn U
  -- `div g` vanishes off `tsupport g ⊆ W ⊆ U`, so both integrals have the same integrand.
  have hgU : tsupport g ⊆ U := hgW.trans (subset_closure.trans hWU.2)
  have hdiv : ∀ x, x ∉ tsupport g →
      Poincare.SimonGMT.Chapter02.euclideanDivergence (⇑g) x = 0 := fun x hx ↦
    Function.notMem_support.1 fun h ↦
      hx (Poincare.SimonGMT.Chapter02.support_euclideanDivergence_subset _ h)
  have hR1 : ∫ x in W, E.indicator (fun _ ↦ (1 : ℝ)) x *
        Poincare.SimonGMT.Chapter02.euclideanDivergence (⇑g) x =
      ∫ x in E ∩ U, Poincare.SimonGMT.Chapter02.euclideanDivergence (⇑g) x := by
    rw [← integral_indicator hWo.measurableSet,
      ← integral_indicator₀ (hE.inter hU.measurableSet.nullMeasurableSet)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ tsupport g
    · by_cases hxE : x ∈ E <;> simp [hgW hx, hgU hx, hxE]
    · rw [Set.indicator_apply_eq_zero.2 fun _ ↦ by simp [hdiv x hx],
        Set.indicator_apply_eq_zero.2 fun _ ↦ hdiv x hx]
  -- `sup |g|` bounds `|g|`, and `g = 0` off `W̄`.
  set M := Poincare.SimonGMT.Chapter02.compactlySupportedSupNorm g
  have hM : ∀ x, ‖g x‖ ≤ M := fun x ↦
    le_csSup ((map_continuous g).norm.bddAbove_range_of_hasCompactSupport
      g.hasCompactSupport.norm) (Set.mem_range_self x)
  have hbound : ∀ᵐ x ∂μ, ‖inner ℝ (g x) (ν x)‖ ≤ (closure W).indicator (fun _ ↦ M) x := by
    filter_upwards [hν] with x hx
    by_cases hxW : x ∈ closure W
    · rw [Set.indicator_of_mem hxW]
      calc ‖inner ℝ (g x) (ν x)‖ ≤ ‖g x‖ * ‖ν x‖ := norm_inner_le_norm _ _
        _ = ‖g x‖ := by rw [hx, mul_one]
        _ ≤ M := hM x
    · have hgx : g x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h ↦ hxW (subset_closure (hgW h))
      simp [Set.indicator_of_notMem hxW, hgx]
  have hint : Integrable ((closure W).indicator fun _ ↦ M) μ :=
    (integrable_indicator_iff isClosed_closure.measurableSet).2
      (integrableOn_const (hμK _ hWU.1 hWU.2).ne)
  calc ∫ x in W, E.indicator (fun _ ↦ (1 : ℝ)) x *
        Poincare.SimonGMT.Chapter02.euclideanDivergence (⇑g) x
      = -∫ x, inner ℝ (g x) (ν x) ∂μ := by rw [hR1, hGG g hg g.hasCompactSupport hgU]
    _ ≤ ‖∫ x, inner ℝ (g x) (ν x) ∂μ‖ := (neg_le_abs _).trans_eq (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, (closure W).indicator (fun _ ↦ M) x ∂μ := norm_integral_le_of_norm_le hint hbound
    _ = (μ (closure W)).toReal * M := by
      rw [integral_indicator_const _ isClosed_closure.measurableSet, smul_eq_mul, measureReal_def]

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
/-- **Carathéodory-measurable fields have Borel a.e.-versions** (Step 6 of the proof of the
Riesz representation on open sets, after Simon Ch. 1, Thm. 4.14): let `X` be Hausdorff, locally
compact and `σ`-compact with its Borel `σ`-algebra, and `μ` a measure on `X` finite on compact
sets. If `ν : X → ℝᴺ` is measurable for the Carathéodory `σ`-algebra of the outer measure `μ*`,
then `ν` agrees `μ`-a.e. with a Borel (strongly measurable) map. Since `μ` is `σ`-finite, every
Carathéodory set `A` is the countable union of the Carathéodory sets `A ∩ Sₙ` of finite measure;
the Carathéodory identity for `A ∩ Sₙ` tested on its measurable hull makes the hull exceed it by a
null set, so `A` is `μ`-null-measurable. Hence `ν` is null-measurable, and as the Borel
`σ`-algebra of `ℝᴺ` is countably generated, `ν` is `μ`-a.e. measurable. -/
theorem Submission.gaussGreenRep_riesz_caratheodory_borel_version : ∀ (X : Type)
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SigmaCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (N : ℕ) (ν : X → Rn N),
    (∀ K : Set X, IsCompact K → μ K < ∞) → Measurable[μ.toOuterMeasure.caratheodory] ν →
    ∃ ν' : X → Rn N, StronglyMeasurable ν' ∧ ν =ᵐ[μ] ν' := by
  intro X _ _ _ _ _ _ μ N ν hμ hν
  -- Step 2: `μ` is finite on compact sets, hence `σ`-finite on the `σ`-compact space `X`; its
  -- spanning sets `Sₙ` are measurable, of finite measure, and cover `X`.
  have : IsFiniteMeasureOnCompacts μ := ⟨hμ⟩
  -- Step 3: every Carathéodory-measurable set is `μ`-null-measurable.
  have hnull : ∀ A : Set X, MeasurableSet[μ.toOuterMeasure.caratheodory] A →
      NullMeasurableSet A μ := by
    intro A hA
    have hpiece : ∀ n, NullMeasurableSet (A ∩ spanningSets μ n) μ := by
      intro n
      set B := A ∩ spanningSets μ n
      -- `B` is Carathéodory measurable (Borel sets are) and has finite measure.
      have hB : MeasurableSet[μ.toOuterMeasure.caratheodory] B :=
        hA.inter (le_toOuterMeasure_caratheodory μ _ (measurableSet_spanningSets μ n))
      have hBfin : μ B ≠ ∞ :=
        ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne
      -- The Carathéodory identity for `B` tested on its measurable hull `H ⊇ B`, `μ H = μ B`,
      -- gives `μ B = μ B + μ (H \ B)`, so `μ (H \ B) = 0`.
      have hcar : μ (toMeasurable μ B) =
          μ (toMeasurable μ B ∩ B) + μ (toMeasurable μ B \ B) :=
        (OuterMeasure.isCaratheodory_iff _).1 hB _
      rw [inter_eq_right.2 (subset_toMeasurable μ B), measure_toMeasurable] at hcar
      have hdiff : μ (toMeasurable μ B \ B) = 0 :=
        (ENNReal.add_right_inj hBfin).1 (by rw [add_zero]; exact hcar.symm)
      -- Hence `B = H` up to a `μ`-null set.
      refine (measurableSet_toMeasurable μ B).nullMeasurableSet.congr (ae_eq_set.2 ⟨hdiff, ?_⟩)
      rw [sdiff_eq_empty.2 (subset_toMeasurable μ B), measure_empty]
    -- `A = ⋃ₙ (A ∩ Sₙ)` is a countable union of null-measurable sets.
    rw [← inter_univ A, ← iUnion_spanningSets μ, inter_iUnion]
    exact .iUnion hpiece
  -- Step 4: preimages of Borel sets under `ν` are Carathéodory, hence null-measurable.
  have hν₀ : NullMeasurable ν μ := fun s hs ↦ hnull _ (hν hs)
  -- Steps 5–6: the Borel `σ`-algebra of `ℝᴺ` is countably generated, so `ν` is a.e.-measurable,
  -- hence a.e.-strongly measurable; its strongly measurable representative is the version.
  have hsm := hν₀.aemeasurable.aestronglyMeasurable
  exact ⟨hsm.mk ν, hsm.stronglyMeasurable_mk, hsm.ae_eq_mk⟩

/-- **Riesz representation with a Borel unit field on a σ-compact locally compact Hausdorff
space**: Simon Ch. 1, Theorem 4.14 (`chapter-01.txt` lines 1654–1663) with `H = ℝᴺ`, as used
for (4.1). For an orthonormal basis `b` of `ℝᴺ`, each component `ℓᵢ h = L (h • bᵢ)` is bounded
above on the order intervals `[0, f]` of `C_c(X, ℝ)`. Hence `q f = sup {ℓᵢ g : 0 ≤ g ≤ f}` is
additive (split `g ≤ f₁ + f₂` as `g ⊓ f₁ + g₂`) and positively homogeneous on the cone, and
`ℓᵢ = Aᵢ - Bᵢ` with the positive functionals `Aᵢ = q`, `Bᵢ = q - ℓᵢ`. Mathlib's
Riesz–Markov–Kakutani theorem represents `Aᵢ` and `Bᵢ` by Radon measures, which have Borel
Radon–Nikodym densities with respect to their sum `μ₀`; so `L f = ∫ ⟨f, ρ⟩ dμ₀` for a Borel field
`ρ = ∑ᵢ dᵢ bᵢ`, locally `μ₀`-integrable. The polar decomposition `μ = |ρ| μ₀`, `ν = ρ / |ρ|`
gives the claim. -/
theorem Submission.gaussGreenRep_riesz_sigmaCompact_borel : ∀ (X : Type) [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (N : ℕ) (L : C_c(X, Rn N) →ₗ[ℝ] ℝ), (∀ K : Set X, IsCompact K → ∃ C : ℝ,
      ∀ f : C_c(X, Rn N), (∀ x, ‖f x‖ ≤ 1) → tsupport f ⊆ K → L f ≤ C) →
    ∃ (μ : Measure X) (ν : X → Rn N), (∀ K : Set X, IsCompact K → μ K < ∞) ∧
      StronglyMeasurable ν ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
      ∀ f : C_c(X, Rn N), L f = ∫ x, inner ℝ (f x) (ν x) ∂μ := by
  intro X _ _ _ _ _ _ N L hbound
  -- Step 1 (Jordan decomposition): a real functional `ℓ` on `C_c(X, ℝ)` that is bounded above on
  -- every order interval `[0, f]` is a difference of two positive functionals.
  have jordan : ∀ ℓ : C_c(X, ℝ) →ₗ[ℝ] ℝ,
      (∀ f : C_c(X, ℝ≥0), BddAbove ((fun g : C_c(X, ℝ≥0) ↦ ℓ g.toReal) '' {g | g ≤ f})) →
      ∃ A B : C_c(X, ℝ) →ₚ[ℝ] ℝ, ∀ h, ℓ h = A h - B h := by
    intro ℓ hℓ
    have h0le : ∀ f : C_c(X, ℝ≥0), 0 ≤ f := fun f ↦
      CompactlySupportedContinuousMap.le_def.2 fun x ↦ by simp
    have htoReal0 : (0 : C_c(X, ℝ≥0)).toReal = 0 := by ext x; simp
    have hsmulR : ∀ (c : ℝ≥0) (f : C_c(X, ℝ≥0)), (c • f).toReal = (c : ℝ) • f.toReal :=
      fun c f ↦ by ext x; simp [NNReal.smul_def]
    -- `q f = sup {ℓ g : 0 ≤ g ≤ f}`, the positive part of `ℓ` on the cone `C_c(X, ℝ≥0)`.
    obtain ⟨q, hq⟩ : ∃ q : C_c(X, ℝ≥0) → ℝ,
        ∀ f, q f = sSup ((fun g : C_c(X, ℝ≥0) ↦ ℓ g.toReal) '' {g | g ≤ f}) := ⟨_, fun _ ↦ rfl⟩
    have hle : ∀ f g : C_c(X, ℝ≥0), g ≤ f → ℓ g.toReal ≤ q f := fun f g hg ↦ by
      rw [hq]; exact le_csSup (hℓ f) ⟨g, hg, rfl⟩
    have hsup : ∀ (f : C_c(X, ℝ≥0)) (c : ℝ),
        (∀ g : C_c(X, ℝ≥0), g ≤ f → ℓ g.toReal ≤ c) → q f ≤ c := by
      intro f c hc
      rw [hq]
      exact csSup_le ⟨_, ⟨0, h0le f, rfl⟩⟩ (by rintro _ ⟨g, hg, rfl⟩; exact hc g hg)
    -- Additivity: `g ≤ f₁ + f₂` splits as `(g ⊓ f₁) + g₂` with `g₂ ≤ f₂`.
    have hq_add : ∀ f₁ f₂ : C_c(X, ℝ≥0), q (f₁ + f₂) = q f₁ + q f₂ := by
      intro f₁ f₂
      apply le_antisymm
      · refine hsup _ _ fun g hg ↦ ?_
        obtain ⟨g₂, hg₂⟩ :=
          CompactlySupportedContinuousMap.exists_add_of_le (inf_le_left : g ⊓ f₁ ≤ g)
        have h₂ : g₂ ≤ f₂ := by
          rw [CompactlySupportedContinuousMap.le_def] at hg ⊢
          intro x
          have hx := hg x
          have hgx := congrArg (fun φ : C_c(X, ℝ≥0) ↦ φ x) hg₂
          simp only [CompactlySupportedContinuousMap.add_apply,
            CompactlySupportedContinuousMap.inf_apply] at hx hgx
          rcases le_total (g x) (f₁ x) with h | h
          · rw [inf_eq_left.2 h] at hgx
            have : g₂ x = 0 := by simpa using hgx
            rw [this]
            exact zero_le
          · rw [inf_eq_right.2 h] at hgx
            rw [← hgx] at hx
            exact le_of_add_le_add_left hx
        rw [← hg₂, CompactlySupportedContinuousMap.toReal_add, map_add]
        exact add_le_add (hle _ _ inf_le_right) (hle _ _ h₂)
      · have h1 : q f₁ ≤ q (f₁ + f₂) - q f₂ := hsup _ _ fun g₁ hg₁ ↦ by
          have h2 : q f₂ ≤ q (f₁ + f₂) - ℓ g₁.toReal := hsup _ _ fun g₂ hg₂ ↦ by
            have := hle (f₁ + f₂) (g₁ + g₂) (add_le_add hg₁ hg₂)
            rw [CompactlySupportedContinuousMap.toReal_add, map_add] at this
            linarith
          linarith
        linarith
    -- Positive homogeneity.
    have hq_le_smul : ∀ (c : ℝ≥0) (f : C_c(X, ℝ≥0)), c ≠ 0 → q (c • f) ≤ c * q f := by
      intro c f hc
      refine hsup _ _ fun g hg ↦ ?_
      have hg' : c⁻¹ • g ≤ f := by
        rw [CompactlySupportedContinuousMap.le_def] at hg ⊢
        intro x
        rw [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
        calc c⁻¹ * g x ≤ c⁻¹ * (c • f) x := mul_le_mul_of_nonneg_left (hg x) zero_le
          _ = f x := by
            rw [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ hc]
      have h2 : ℓ g.toReal = c * ℓ (c⁻¹ • g).toReal := by
        rw [hsmulR, map_smul, smul_eq_mul, NNReal.coe_inv, ← mul_assoc,
          mul_inv_cancel₀ (NNReal.coe_ne_zero.2 hc), one_mul]
      rw [h2]
      exact mul_le_mul_of_nonneg_left (hle f _ hg') c.coe_nonneg
    have hq_smul : ∀ (c : ℝ≥0) (f : C_c(X, ℝ≥0)), q (c • f) = c * q f := by
      intro c f
      rcases eq_or_ne c 0 with rfl | hc
      · have h0 := hq_add 0 0
        rw [add_zero] at h0
        rw [zero_smul, NNReal.coe_zero, zero_mul]
        linarith
      · refine le_antisymm (hq_le_smul c f hc) ?_
        have h1 := hq_le_smul c⁻¹ (c • f) (inv_ne_zero hc)
        rw [inv_smul_smul₀ hc, NNReal.coe_inv] at h1
        have hc' : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
        calc (c : ℝ) * q f ≤ c * ((c : ℝ)⁻¹ * q (c • f)) := mul_le_mul_of_nonneg_left h1 hc'.le
          _ = q (c • f) := by rw [← mul_assoc, mul_inv_cancel₀ hc'.ne', one_mul]
    have hq_nonneg : ∀ f, 0 ≤ q f := fun f ↦ by
      have := hle f 0 (h0le f)
      rwa [htoReal0, map_zero] at this
    have hq_ge : ∀ f, ℓ f.toReal ≤ q f := fun f ↦ hle f f le_rfl
    -- The positive part `P = q` and the negative part `Q = q - ℓ` on the cone.
    let P : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 :=
      { toFun := fun f ↦ Real.toNNReal (q f)
        map_add' := fun f₁ f₂ ↦ by
          simp only [hq_add]
          exact Real.toNNReal_add (hq_nonneg f₁) (hq_nonneg f₂)
        map_smul' := fun c f ↦ by
          simp only [hq_smul, RingHom.id_apply, smul_eq_mul]
          rw [Real.toNNReal_mul c.coe_nonneg, Real.toNNReal_coe] }
    let Q : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 :=
      { toFun := fun f ↦ Real.toNNReal (q f - ℓ f.toReal)
        map_add' := fun f₁ f₂ ↦ by
          simp only [hq_add, CompactlySupportedContinuousMap.toReal_add, map_add]
          rw [← Real.toNNReal_add (sub_nonneg.2 (hq_ge f₁)) (sub_nonneg.2 (hq_ge f₂))]
          congr 1
          ring
        map_smul' := fun c f ↦ by
          simp only [hq_smul, hsmulR, map_smul, RingHom.id_apply, smul_eq_mul]
          rw [← mul_sub, Real.toNNReal_mul c.coe_nonneg, Real.toNNReal_coe] }
    have hPQ : ∀ f : C_c(X, ℝ≥0), ((P f : ℝ≥0) : ℝ) - ((Q f : ℝ≥0) : ℝ) = ℓ f.toReal := by
      intro f
      show ((Real.toNNReal (q f) : ℝ≥0) : ℝ) - ((Real.toNNReal (q f - ℓ f.toReal) : ℝ≥0) : ℝ) =
        ℓ f.toReal
      rw [Real.coe_toNNReal _ (hq_nonneg f), Real.coe_toNNReal _ (sub_nonneg.2 (hq_ge f))]
      ring
    refine ⟨CompactlySupportedContinuousMap.toRealPositiveLinear P,
      CompactlySupportedContinuousMap.toRealPositiveLinear Q, fun h ↦ ?_⟩
    rw [CompactlySupportedContinuousMap.toRealPositiveLinear_apply,
      CompactlySupportedContinuousMap.toRealPositiveLinear_apply]
    conv_lhs => rw [← CompactlySupportedContinuousMap.nnrealPart_sub_nnrealPart_neg h]
    rw [map_sub, ← hPQ, ← hPQ]
    ring
  -- Step 2: the components `ℓᵢ h = L (h • bᵢ)` of `L` in an orthonormal basis `b` of `ℝᴺ`.
  obtain ⟨b⟩ : Nonempty (OrthonormalBasis (Fin N) ℝ (Rn N)) :=
    ⟨EuclideanSpace.basisFun (Fin N) ℝ⟩
  have hbn : ∀ i, ‖b i‖ = 1 := fun i ↦ b.orthonormal.1 i
  let E : Fin N → C_c(X, ℝ) →ₗ[ℝ] C_c(X, Rn N) := fun i ↦
    { toFun := fun h ↦ ⟨⟨fun x ↦ h x • b i, h.continuous.smul continuous_const⟩,
        h.hasCompactSupport.smul_right⟩
      map_add' := fun h₁ h₂ ↦ by ext x; simp [add_smul]
      map_smul' := fun c h ↦ by ext x; simp [smul_smul] }
  have hE : ∀ i (h : C_c(X, ℝ)) (x : X), E i h x = h x • b i := fun _ _ _ ↦ rfl
  let comp : Fin N → C_c(X, Rn N) → C_c(X, ℝ) := fun i g ↦
    ⟨⟨fun x ↦ inner ℝ (b i) (g x), continuous_const.inner g.continuous⟩,
      g.hasCompactSupport.comp_left (g := fun y ↦ inner ℝ (b i) y) (inner_zero_right _)⟩
  have hcomp : ∀ i (g : C_c(X, Rn N)) (x : X), comp i g x = inner ℝ (b i) (g x) :=
    fun _ _ _ ↦ rfl
  have hdecomp : ∀ g : C_c(X, Rn N), L g = ∑ i, L (E i (comp i g)) := by
    intro g
    rw [← map_sum]
    congr 1
    refine CompactlySupportedContinuousMap.ext fun x ↦ ?_
    rw [CompactlySupportedContinuousMap.sum_apply]
    simp only [hE, hcomp]
    exact (b.sum_repr' (g x)).symm
  -- The local bound on `L` bounds each `ℓᵢ` above on the order intervals `[0, f]`.
  have hℓbdd : ∀ i (f : C_c(X, ℝ≥0)),
      BddAbove ((fun g : C_c(X, ℝ≥0) ↦ (L ∘ₗ E i) g.toReal) '' {g | g ≤ f}) := by
    intro i f
    obtain ⟨C, hC⟩ := hbound (tsupport f) f.hasCompactSupport
    obtain ⟨M, hM⟩ := (f.hasCompactSupport.isCompact_range f.continuous).bddAbove
    have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    refine ⟨((M : ℝ) + 1) * C, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    have hgf : ∀ x, (g x : ℝ) ≤ M := fun x ↦
      NNReal.coe_le_coe.2 ((CompactlySupportedContinuousMap.le_def.1 hg x).trans (hM ⟨x, rfl⟩))
    have hφ1 : ∀ x, ‖E i (((M : ℝ) + 1)⁻¹ • g.toReal) x‖ ≤ 1 := fun x ↦ by
      rw [hE, CompactlySupportedContinuousMap.smul_apply,
        CompactlySupportedContinuousMap.toReal_apply, smul_eq_mul, norm_smul, hbn, mul_one,
        Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_mul_le_iff₀ hM1]
      linarith [hgf x]
    have hφK : tsupport (E i (((M : ℝ) + 1)⁻¹ • g.toReal)) ⊆ tsupport f := by
      refine closure_mono fun x hx ↦ ?_
      rw [Function.mem_support] at hx ⊢
      intro hfx
      apply hx
      have hgx : g x = 0 :=
        le_antisymm ((CompactlySupportedContinuousMap.le_def.1 hg x).trans hfx.le) zero_le
      rw [hE, CompactlySupportedContinuousMap.smul_apply,
        CompactlySupportedContinuousMap.toReal_apply, hgx]
      simp
    calc (L ∘ₗ E i) g.toReal = ((M : ℝ) + 1) * L (E i (((M : ℝ) + 1)⁻¹ • g.toReal)) := by
          rw [LinearMap.comp_apply, map_smul, map_smul, smul_eq_mul, ← mul_assoc,
            mul_inv_cancel₀ hM1.ne', one_mul]
      _ ≤ ((M : ℝ) + 1) * C := mul_le_mul_of_nonneg_left (hC _ hφ1 hφK) hM1.le
  -- Step 3: Jordan decompositions `ℓᵢ = Aᵢ - Bᵢ` and the Riesz measures of `Aᵢ`, `Bᵢ` (Mathlib's
  -- Riesz–Markov–Kakutani theorem), all absolutely continuous with respect to their sum `μ₀`.
  choose A B hAB using fun i ↦ jordan (L ∘ₗ E i) (hℓbdd i)
  have hAB' : ∀ i h, L (E i h) = A i h - B i h := hAB
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀ : Measure X,
      μ₀ = ∑ i, (RealRMK.rieszMeasure (A i) + RealRMK.rieszMeasure (B i)) := ⟨_, rfl⟩
  have hμ₀K : ∀ K : Set X, IsCompact K → μ₀ K < ∞ := by
    intro K hK
    rw [hμ₀, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.2 fun i _ ↦ by
      rw [Measure.add_apply]
      exact ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hK.measure_lt_top⟩
  have : IsFiniteMeasureOnCompacts μ₀ := ⟨hμ₀K⟩
  have hac : ∀ i, RealRMK.rieszMeasure (A i) ≪ μ₀ ∧ RealRMK.rieszMeasure (B i) ≪ μ₀ := by
    intro i
    have h0 : ∀ s, μ₀ s = 0 →
        RealRMK.rieszMeasure (A i) s = 0 ∧ RealRMK.rieszMeasure (B i) s = 0 := by
      intro s hs
      rw [hμ₀, Measure.finsetSum_apply, Finset.sum_eq_zero_iff] at hs
      have := hs i (Finset.mem_univ i)
      rwa [Measure.add_apply, add_eq_zero] at this
    exact ⟨fun ⦃s⦄ hs ↦ (h0 s hs).1, fun ⦃s⦄ hs ↦ (h0 s hs).2⟩
  -- Radon–Nikodym: a measure `m ≪ μ₀` finite on compact sets is `μ₀` with a density `d`.
  have rn : ∀ m : Measure X, IsFiniteMeasureOnCompacts m → m ≪ μ₀ →
      ∃ d : X → ℝ≥0∞, Measurable d ∧ (∀ K : Set X, IsCompact K → ∫⁻ x in K, d x ∂μ₀ < ∞) ∧
        ∀ h : C_c(X, ℝ), Integrable (fun x ↦ (d x).toReal * h x) μ₀ ∧
          ∫ x, h x ∂m = ∫ x, (d x).toReal * h x ∂μ₀ := by
    intro m hm hmac
    have hwd : μ₀.withDensity (m.rnDeriv μ₀) = m := by
      conv_rhs => rw [m.haveLebesgueDecomposition_add μ₀]
      rw [Measure.singularPart_eq_zero_of_ac hmac, zero_add]
    have hlt := Measure.rnDeriv_lt_top m μ₀
    refine ⟨m.rnDeriv μ₀, Measure.measurable_rnDeriv m μ₀, fun K hK ↦
      Measure.lintegral_rnDeriv_lt_top_of_measure_ne_top μ₀ hK.measure_lt_top.ne,
      fun h ↦ ⟨?_, ?_⟩⟩
    · have hint : Integrable (fun x ↦ h x) (μ₀.withDensity (m.rnDeriv μ₀)) := by
        rw [hwd]
        exact h.continuous.integrable_of_hasCompactSupport h.hasCompactSupport
      exact (integrable_withDensity_iff_integrable_smul' (Measure.measurable_rnDeriv m μ₀) hlt).1
        hint
    · calc ∫ x, h x ∂m = ∫ x, h x ∂(μ₀.withDensity (m.rnDeriv μ₀)) := by rw [hwd]
        _ = ∫ x, (m.rnDeriv μ₀ x).toReal • h x ∂μ₀ :=
          integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv m μ₀) hlt _
  -- Each `ℓᵢ` has a locally `μ₀`-integrable density `dᵢ`.
  have hd : ∀ i, ∃ d : X → ℝ, Measurable d ∧
      (∀ K : Set X, IsCompact K → ∫⁻ x in K, ‖d x‖ₑ ∂μ₀ < ∞) ∧
      ∀ h : C_c(X, ℝ), Integrable (fun x ↦ d x * h x) μ₀ ∧ L (E i h) = ∫ x, d x * h x ∂μ₀ := by
    intro i
    obtain ⟨dA, hdAm, hdAK, hdA⟩ := rn _ inferInstance (hac i).1
    obtain ⟨dB, hdBm, hdBK, hdB⟩ := rn _ inferInstance (hac i).2
    refine ⟨fun x ↦ (dA x).toReal - (dB x).toReal, hdAm.ennreal_toReal.sub hdBm.ennreal_toReal,
      fun K hK ↦ ?_, fun h ↦ ?_⟩
    · have hpt : ∀ x, ‖(dA x).toReal - (dB x).toReal‖ₑ ≤ dA x + dB x := fun x ↦ by
        refine enorm_sub_le.trans (add_le_add ?_ ?_) <;>
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg] <;>
          exact ENNReal.ofReal_toReal_le
      calc ∫⁻ x in K, ‖(dA x).toReal - (dB x).toReal‖ₑ ∂μ₀ ≤ ∫⁻ x in K, (dA x + dB x) ∂μ₀ :=
            lintegral_mono hpt
        _ = ∫⁻ x in K, dA x ∂μ₀ + ∫⁻ x in K, dB x ∂μ₀ := lintegral_add_left hdAm _
        _ < ∞ := ENNReal.add_lt_top.2 ⟨hdAK K hK, hdBK K hK⟩
    · obtain ⟨hiA, hA⟩ := hdA h
      obtain ⟨hiB, hB⟩ := hdB h
      refine ⟨(hiA.sub hiB).congr (ae_of_all _ fun x ↦ ?_), ?_⟩
      · simp only [Pi.sub_apply]
        ring
      · rw [hAB', ← RealRMK.integral_rieszMeasure (A i), ← RealRMK.integral_rieszMeasure (B i),
          hA, hB, ← integral_sub hiA hiB]
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        beta_reduce
        ring
  choose d hdm hdK hdrep using hd
  -- Step 4: the field `ρ = ∑ᵢ dᵢ bᵢ` represents `L` against `μ₀`.
  obtain ⟨ρ, hρ⟩ : ∃ ρ : X → Rn N, ρ = fun x ↦ ∑ i, d i x • b i := ⟨_, rfl⟩
  have hρm : Measurable ρ := by
    rw [hρ]
    exact Finset.measurable_sum _ fun i _ ↦ (hdm i).smul_const _
  have hρK : ∀ K : Set X, IsCompact K → ∫⁻ x in K, ‖ρ x‖ₑ ∂μ₀ < ∞ := by
    intro K hK
    have hpt : ∀ x, ‖ρ x‖ₑ ≤ ∑ i, ‖d i x‖ₑ := fun x ↦ by
      rw [hρ]
      refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
      rw [enorm_smul, ← ofReal_norm (b i), hbn, ENNReal.ofReal_one, mul_one]
    calc ∫⁻ x in K, ‖ρ x‖ₑ ∂μ₀ ≤ ∫⁻ x in K, ∑ i, ‖d i x‖ₑ ∂μ₀ := lintegral_mono hpt
      _ = ∑ i, ∫⁻ x in K, ‖d i x‖ₑ ∂μ₀ := lintegral_finsetSum _ fun i _ ↦ (hdm i).enorm
      _ < ∞ := ENNReal.sum_lt_top.2 fun i _ ↦ hdK i K hK
  have hrep₀ : ∀ g : C_c(X, Rn N), L g = ∫ x, inner ℝ (g x) (ρ x) ∂μ₀ := by
    intro g
    rw [hdecomp g, Finset.sum_congr rfl fun i _ ↦ (hdrep i (comp i g)).2,
      ← integral_finsetSum _ fun i _ ↦ (hdrep i (comp i g)).1]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [hρ, inner_sum, real_inner_smul_right, hcomp]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm]
  -- Step 5 (polar decomposition): `μ = |ρ| μ₀` and `ν = ρ / |ρ|`.
  refine ⟨μ₀.withDensity fun x ↦ ‖ρ x‖ₑ, fun x ↦ ‖ρ x‖⁻¹ • ρ x, fun K hK ↦ ?_,
    (hρm.norm.inv.smul hρm).stronglyMeasurable, ?_, fun g ↦ ?_⟩
  · rw [withDensity_apply _ hK.measurableSet]
    exact hρK K hK
  · rw [ae_withDensity_iff hρm.enorm]
    refine ae_of_all _ fun x hx ↦ ?_
    have hx0 : ρ x ≠ 0 := fun h ↦ hx (by rw [h, enorm_zero])
    show ‖‖ρ x‖⁻¹ • ρ x‖ = 1
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]
  · rw [hrep₀ g, integral_withDensity_eq_integral_toReal_smul hρm.enorm
      (ae_of_all _ fun x ↦ enorm_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    show inner ℝ (g x) (ρ x) = (‖ρ x‖ₑ).toReal • inner ℝ (g x) (‖ρ x‖⁻¹ • ρ x)
    rw [toReal_enorm, smul_eq_mul, real_inner_smul_right]
    rcases eq_or_ne (ρ x) 0 with h | h
    · simp [h]
    · rw [mul_inv_cancel_left₀ (norm_ne_zero_iff.2 h)]
/-- **Zero extension of a functional on admissible fields** (Steps 1–4 of the proof of the
Gauss–Green representation on an open `U`, passing from `ℝᴺ` to `U` to apply Simon Ch. 1,
Theorem 4.14, `chapter-01.txt` lines 1654–1663, in Ch. 2 (2.1)–(2.2), `chapter-02.txt`
lines 485–496). For `f ∈ C_c(U; ℝᴺ)` the zero extension `f̃ = extend ι f 0` (`ι : U → ℝᴺ`) is
continuous since `U` is open (`HasCompactSupport.continuous_extend_zero`), has
`tsupport f̃ ⊆ ι(tsupport f) ⊆ U` (`tsupport_extend_zero_subset`) and is linear in `f`, so
`L f := Λ f̃` is linear and inherits the bound of `Λ` on `ι(K)`. For admissible `g`, the
restriction `g ∘ ι` vanishes off the compact `ι⁻¹(tsupport g)` and its zero extension is `g`. -/
theorem Submission.gaussGreenRep_riesz_zero_extension_functional : ∀ (N : ℕ) (U : Set (Rn N)) (Λ : (Rn N → Rn N) → ℝ), IsOpen U → (∀ g h : Rn N → Rn N, Continuous g → HasCompactSupport g → tsupport g ⊆ U → Continuous h → HasCompactSupport h → tsupport h ⊆ U → Λ (g + h) = Λ g + Λ h) → (∀ (c : ℝ) (g : Rn N → Rn N), Continuous g → HasCompactSupport g → tsupport g ⊆ U → Λ (c • g) = c * Λ g) → (∀ K : Set (Rn N), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ g : Rn N → Rn N, Continuous g → tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → Λ g ≤ C) → ∃ L : C_c(U, Rn N) →ₗ[ℝ] ℝ, (∀ K : Set U, IsCompact K → ∃ C : ℝ, ∀ f : C_c(U, Rn N), (∀ x, ‖f x‖ ≤ 1) → tsupport f ⊆ K → L f ≤ C) ∧ ∀ g : Rn N → Rn N, Continuous g → HasCompactSupport g → tsupport g ⊆ U → ∃ f : C_c(U, Rn N), (∀ y : U, f y = g ↑y) ∧ L f = Λ g := by
  intro N U Λ hU hadd hsmul hbd
  -- The zero extension `f̃ = extend ι f 0` of `f ∈ C_c(U; ℝᴺ)`, `ι : U → ℝᴺ` the inclusion.
  let E : C_c(U, Rn N) → Rn N → Rn N := fun f ↦ Subtype.val.extend (⇑f) 0
  have hEval : ∀ (f : C_c(U, Rn N)) (y : U), E f y = f y := fun f y ↦
    Subtype.val_injective.extend_apply _ _ y
  have hEout : ∀ (f : C_c(U, Rn N)) (x : Rn N), x ∉ U → E f x = 0 := fun f x hx ↦
    Function.extend_apply' _ _ x fun ⟨y, hy⟩ ↦ hx (hy ▸ y.2)
  -- `f̃` is admissible: continuous (`U` is open), compactly supported, `tsupport f̃ ⊆ ι(tsupport f)`.
  have hEcont : ∀ f : C_c(U, Rn N), Continuous (E f) := fun f ↦
    HasCompactSupport.continuous_extend_zero hU f.continuous f.hasCompactSupport
  have hEcs : ∀ f : C_c(U, Rn N), HasCompactSupport (E f) := fun f ↦
    f.hasCompactSupport.extend_zero continuous_subtype_val
  have hEsupp : ∀ f : C_c(U, Rn N), tsupport (E f) ⊆ Subtype.val '' tsupport f := fun f ↦
    f.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val
  have hEU : ∀ f : C_c(U, Rn N), tsupport (E f) ⊆ U := fun f ↦
    (hEsupp f).trans (Subtype.coe_image_subset _ _)
  -- The extension is linear in `f`.
  have hEadd : ∀ f f' : C_c(U, Rn N), E (f + f') = E f + E f' := by
    intro f f'
    funext x
    by_cases hx : x ∈ U
    · lift x to U using hx
      simp [hEval]
    · simp [hEout _ _ hx]
  have hEsmul : ∀ (c : ℝ) (f : C_c(U, Rn N)), E (c • f) = c • E f := by
    intro c f
    funext x
    by_cases hx : x ∈ U
    · lift x to U using hx
      simp [hEval]
    · simp [hEout _ _ hx]
  refine ⟨{ toFun := fun f ↦ Λ (E f)
            map_add' := fun f f' ↦ by
              simp only [hEadd]
              exact hadd _ _ (hEcont f) (hEcs f) (hEU f) (hEcont f') (hEcs f') (hEU f')
            map_smul' := fun c f ↦ by
              simp only [hEsmul, RingHom.id_apply, smul_eq_mul]
              exact hsmul c _ (hEcont f) (hEcs f) (hEU f) }, ?_, ?_⟩
  · -- (i) the local bound, from the bound for `Λ` on `ι(K)`.
    intro K hK
    obtain ⟨C, hC⟩ := hbd (Subtype.val '' K) (hK.image continuous_subtype_val)
      (Subtype.coe_image_subset _ _)
    refine ⟨C, fun f hf1 hfK ↦ hC (E f) (hEcont f) ((hEsupp f).trans (image_mono hfK)) ?_⟩
    intro x
    by_cases hx : x ∈ U
    · lift x to U using hx
      rw [hEval]
      exact hf1 x
    · rw [hEout _ _ hx, norm_zero]
      exact zero_le_one
  · -- (ii) the restriction `g ∘ ι` lies in `C_c(U; ℝᴺ)` and its zero extension is `g`.
    intro g hg hgc hgU
    have hK₀ : IsCompact (Subtype.val ⁻¹' tsupport g : Set U) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr hgU]
      exact hgc
    let f : C_c(U, Rn N) :=
      ⟨⟨g ∘ Subtype.val, hg.comp continuous_subtype_val⟩,
        HasCompactSupport.intro hK₀ fun y hy ↦ image_eq_zero_of_notMem_tsupport (f := g) hy⟩
    have hEf : E f = g := by
      funext x
      by_cases hx : x ∈ U
      · lift x to U using hx
        rw [hEval]
        rfl
      · rw [hEout _ _ hx]
        exact (image_eq_zero_of_notMem_tsupport fun h ↦ hx (hgU h)).symm
    exact ⟨f, fun y ↦ rfl, show Λ (E f) = Λ g by rw [hEf]⟩
/-- **Push-forward of a Riesz pair from a Borel set `U ⊆ ℝᴺ`** (step 7 of the proof that Simon's
Riesz Representation Theorem, Ch. 1, 4.14 (`chapter-01.txt` lines 1654–1663), applied on `X = U`
gives the measure `μ_E` and unit field `ν` on `ℝᴺ` of Ch. 3, (4.1) (`chapter-03.txt` lines
556–564)). Let `ι : U → ℝᴺ` be the inclusion, `μ = ι_# μ₀` and `ν = extend ι ν₀ 0`, so
`ν ∘ ι = ν₀`. As `U` is Borel, `ι` is a measurable embedding, so `μ(S) = μ₀(ι⁻¹ S)` for every `S`:
`μ(ℝᴺ ∖ U) = μ₀(∅) = 0` and `μ(K) = μ₀(ι⁻¹ K) < ∞` for compact `K ⊆ U`. A.e. statements,
a.e.-strong measurability and Bochner integrals transfer along `ι`. -/
theorem Submission.gaussGreenRep_riesz_pushforward_subtype : ∀ (N : ℕ) (U : Set (Rn N)) (μ₀ : Measure U) (ν₀ : U → Rn N), MeasurableSet U → (∀ K : Set U, IsCompact K → μ₀ K < ∞) → AEStronglyMeasurable ν₀ μ₀ → (∀ᵐ y ∂μ₀, ‖ν₀ y‖ = 1) → ∃ (μ : Measure (Rn N)) (ν : Rn N → Rn N), μ Uᶜ = 0 ∧ (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) ∧ AEStronglyMeasurable ν μ ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧ ∀ g : Rn N → Rn N, ∫ x, inner ℝ (g x) (ν x) ∂μ = ∫ y, inner ℝ (g ↑y) (ν₀ y) ∂μ₀ := by
  intro N U μ₀ ν₀ hU hfin hν₀ hnorm
  -- Step 1: the inclusion `ι : U → ℝᴺ` is a measurable embedding since `U` is Borel.
  have hι : MeasurableEmbedding ((↑) : U → Rn N) := MeasurableEmbedding.subtype_coe hU
  -- Step 2: `ν` extends `ν₀` by zero, so `ν ∘ ι = ν₀`.
  have hνι : (Function.extend ((↑) : U → Rn N) ν₀ 0) ∘ ((↑) : U → Rn N) = ν₀ :=
    funext fun y ↦ Subtype.val_injective.extend_apply ν₀ 0 y
  refine ⟨μ₀.map (↑), Function.extend ((↑) : U → Rn N) ν₀ 0, ?_, ?_, ?_, ?_, ?_⟩
  · -- Step 5: `μ(ℝᴺ ∖ U) = μ₀(ι⁻¹(ℝᴺ ∖ U)) = μ₀(∅) = 0`.
    rw [hι.map_apply, preimage_compl, Subtype.coe_preimage_self, compl_univ, measure_empty]
  · -- Step 6: for compact `K ⊆ U`, `ι⁻¹ K` is compact (its image is `U ∩ K = K`).
    intro K hK hKU
    rw [hι.map_apply]
    refine hfin _ ?_
    rwa [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hKU]
  · -- Step 7: a.e.-strong measurability transfers along `ι`.
    rw [hι.aestronglyMeasurable_map_iff, hνι]
    exact hν₀
  · -- Step 8: `|ν(ι y)| = |ν₀ y| = 1` for `μ₀`-a.e. `y`.
    rw [hι.ae_map_iff]
    filter_upwards [hnorm] with y hy
    rwa [Subtype.val_injective.extend_apply]
  · -- Step 9: change of variables `∫ F dμ = ∫ F ∘ ι dμ₀` for every `F`.
    intro g
    rw [hι.integral_map]
    simp only [Subtype.val_injective.extend_apply]

/-- **Riesz representation on an open set `U ⊆ ℝᴺ`** (Simon Ch. 1, Theorem 4.14,
`chapter-01.txt` lines 1654–1663, applied with `X = U`, `H = ℝᴺ` as in Ch. 2, (2.1)–(2.2),
`chapter-02.txt` lines 485–496). Zero extension identifies `C_c(U; ℝᴺ)` with the admissible
fields, so `L f := Λ f̃` is linear and bounded on the unit fields supported in each compact
`K ⊆ U`. As an open subset of `ℝᴺ`, `U` is Hausdorff, locally compact and second countable,
hence `σ`-compact, and the Riesz representation with a Borel unit field gives `(μ₀, ν₀)` on `U`
with `L f = ∫_U ⟨f, ν₀⟩ dμ₀`. Pushing forward along the inclusion `ι : U → ℝᴺ` gives `(μ, ν)`,
and for admissible `g` with restriction `f = g ∘ ι`:
`Λ g = L f = ∫_U ⟨g ∘ ι, ν₀⟩ dμ₀ = ∫ ⟨g, ν⟩ dμ`. -/
theorem Submission.gaussGreenRep_riesz_on_open : ∀ (N : ℕ) (U : Set (Rn N)) (Λ : (Rn N → Rn N) → ℝ), IsOpen U → (∀ g h : Rn N → Rn N, Continuous g → HasCompactSupport g → tsupport g ⊆ U → Continuous h → HasCompactSupport h → tsupport h ⊆ U → Λ (g + h) = Λ g + Λ h) → (∀ (c : ℝ) (g : Rn N → Rn N), Continuous g → HasCompactSupport g → tsupport g ⊆ U → Λ (c • g) = c * Λ g) → (∀ K : Set (Rn N), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ g : Rn N → Rn N, Continuous g → tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → Λ g ≤ C) → ∃ (μ : Measure (Rn N)) (ν : Rn N → Rn N), μ Uᶜ = 0 ∧ (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) ∧ AEStronglyMeasurable ν μ ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧ ∀ g : Rn N → Rn N, Continuous g → HasCompactSupport g → tsupport g ⊆ U → Λ g = ∫ x, inner ℝ (g x) (ν x) ∂μ := by
  intro N U Λ hU hadd hsmul hbd
  -- Steps 2–4: the functional `L f := Λ f̃` on `C_c(U; ℝᴺ)`, bounded on unit fields supported in
  -- each compact `K ⊆ U`; each admissible `g` is the zero extension of some `f = g ∘ ι`.
  obtain ⟨L, hLbd, hLres⟩ :=
    Submission.gaussGreenRep_riesz_zero_extension_functional N U Λ hU hadd hsmul hbd
  -- Step 1: `U` is locally compact (open in `ℝᴺ`), hence `σ`-compact (second countable).
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  have : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  -- Steps 5–6: Riesz representation of `L` on `U` with a Borel unit field `ν₀`.
  obtain ⟨μ₀, ν₀, hμ₀, hν₀, hν₀1, hL⟩ :=
    Submission.gaussGreenRep_riesz_sigmaCompact_borel U N L hLbd
  -- Step 7: push `(μ₀, ν₀)` forward along the inclusion `ι : U → ℝᴺ` of the Borel set `U`.
  obtain ⟨μ, ν, hμU, hμK, hν, hν1, hint⟩ :=
    Submission.gaussGreenRep_riesz_pushforward_subtype N U μ₀ ν₀ hU.measurableSet hμ₀
      hν₀.aestronglyMeasurable hν₀1
  refine ⟨μ, ν, hμU, hμK, hν, hν1, fun g hg hgc hgU ↦ ?_⟩
  -- Step 7(e): with `f = g ∘ ι`, `Λ g = L f = ∫_U ⟨g ∘ ι, ν₀⟩ dμ₀ = ∫ ⟨g, ν⟩ dμ`.
  obtain ⟨f, hf, hLf⟩ := hLres g hg hgc hgU
  calc Λ g = L f := hLf.symm
    _ = ∫ y, inner ℝ (f y) (ν₀ y) ∂μ₀ := hL f
    _ = ∫ y, inner ℝ (g ↑y) (ν₀ y) ∂μ₀ := by simp only [hf]
    _ = ∫ x, inner ℝ (g x) (ν x) ∂μ := (hint g).symm

/-- **Simon Ch. 3, (4.1): two Gauss–Green pairs pair equally with continuous fields**
(`chapter-03.txt` lines 551–567, with Ch. 2, §2, `chapter-02.txt` line 489: `∫ u div g`
"extends uniquely" from `C¹_c` to continuous compactly supported fields). By (4.1) for both pairs,
`∫ h · ν dμ = -∫_{E ∩ U} div h = ∫ h · ν' dμ'` for every `C¹` field `h` with compact support in
`U`. For continuous `g` with compact support in `U`, `gaussGreenRep_c1_uniform_approx` gives such
`h_k → g` uniformly, all supported in one compact `K ⊆ U`. Eventually `|h_k| ≤ sup |g| + 1`, and
`h_k = 0` off `K`; as `|ν| = 1` `μ`-a.e. and `μ(K) < ∞`, dominated convergence with the bound
`(sup |g| + 1) 1_K` gives `∫ h_k · ν dμ → ∫ g · ν dμ`, and likewise for `(μ', ν')`. -/
theorem Submission.gaussGreenRep_pairing_eq_continuous : ∀ (N : ℕ) (U E : Set (Rn N))
    (μ μ' : Measure (Rn N)) (ν ν' : Rn N → Rn N), IsOpen U → IsGaussGreenPair U E μ ν →
    IsGaussGreenPair U E μ' ν' → ∀ g : Rn N → Rn N, Continuous g → HasCompactSupport g →
    tsupport g ⊆ U → ∫ x, inner ℝ (g x) (ν x) ∂μ = ∫ x, inner ℝ (g x) (ν' x) ∂μ' := by
  rintro N U E μ μ' ν ν' hU ⟨-, hμK, hνm, hν, hGG⟩ ⟨-, hμK', hνm', hν', hGG'⟩ g hg hgc hgU
  -- Step 1: by (4.1) for both pairs, the pairings agree on `C¹` fields supported in `U`.
  have hC1 : ∀ h : Rn N → Rn N, ContDiff ℝ 1 h → HasCompactSupport h → tsupport h ⊆ U →
      ∫ x, inner ℝ (h x) (ν x) ∂μ = ∫ x, inner ℝ (h x) (ν' x) ∂μ' := fun h h1 hc hU' ↦
    neg_inj.1 ((hGG h h1 hc hU').symm.trans (hGG' h h1 hc hU'))
  -- Step 2: `C¹` fields `h k → g` uniformly, all supported in one compact `K ⊆ U`.
  obtain ⟨K, hK, -, hKU, h, hh, hlim⟩ :=
    Submission.gaussGreenRep_c1_uniform_approx N g U hg hgc hU hgU
  -- `|g| ≤ C`, and eventually `|h k - g| < 1` everywhere.
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  have hev : ∀ᶠ k in atTop, ∀ x, dist (g x) (h k x) < 1 :=
    Metric.tendstoUniformly_iff.1 hlim 1 one_pos
  -- Steps 3–4: dominated convergence with the bound `(C + 1) 1_K`, for any measure `m` with
  -- `m K < ∞` and any `m`-measurable `n` with `|n| = 1` `m`-a.e.
  have hlimit : ∀ (m : Measure (Rn N)) (n : Rn N → Rn N), m K < ∞ → AEStronglyMeasurable n m →
      (∀ᵐ x ∂m, ‖n x‖ = 1) → Tendsto (fun k ↦ ∫ x, inner ℝ (h k x) (n x) ∂m) atTop
        (𝓝 (∫ x, inner ℝ (g x) (n x) ∂m)) := by
    intro m n hmK hnm hn
    refine tendsto_integral_filter_of_dominated_convergence (K.indicator fun _ ↦ C + 1)
      (Eventually.of_forall fun k ↦ ?_) ?_ ?_ (Eventually.of_forall fun x ↦ ?_)
    · exact continuous_inner.comp_aestronglyMeasurable
        ((hh k).1.continuous.aestronglyMeasurable.prodMk hnm)
    · filter_upwards [hev] with k hk
      filter_upwards [hn] with x hx
      by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxK]
        calc ‖inner ℝ (h k x) (n x)‖ ≤ ‖h k x‖ * ‖n x‖ := norm_inner_le_norm _ _
          _ ≤ C + 1 := by
            rw [hx, mul_one]
            linarith [hC x, hk x, norm_sub_norm_le (h k x) (g x), dist_eq_norm (g x) (h k x),
              norm_sub_rev (h k x) (g x)]
      · have h0 : h k x = 0 := image_eq_zero_of_notMem_tsupport fun hx' ↦ hxK ((hh k).2.2 hx')
        rw [indicator_of_notMem hxK, h0, inner_zero_left, norm_zero]
    · exact (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hmK.ne)
    · exact (hlim.tendsto_at x).inner tendsto_const_nhds
  -- Step 5: by Step 1 the two sequences agree termwise, so their limits agree.
  exact tendsto_nhds_unique
    ((hlimit μ ν (hμK K hK hKU) hνm hν).congr fun k ↦
      hC1 (h k) (hh k).1 (hh k).2.1 ((hh k).2.2.trans hKU))
    (hlimit μ' ν' (hμK' K hK hKU) hνm' hν')
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
/-- **A measure on an open set is determined by its values on open subsets** (uniqueness of
`μ_E` in Simon Ch. 3, (4.1)): if `μ`, `μ'` vanish off the open set `U ⊆ ℝᴺ`, `μ` is finite on
compact subsets of `U`, and `μ(O) = μ'(O)` for every open `O ⊆ U`, then `μ = μ'`. The open
subsets of `U` of finite `μ`-measure cover `U` (balls with compact closure in `U`), so countably
many of them do (Lindelöf); with `ℝᴺ ∖ U` they form a countable cover of `ℝᴺ` by sets of finite
`μ`-measure on whose traces `μ` and `μ'` agree, and the open sets are a π-system generating the
Borel σ-algebra, so the π-λ uniqueness theorem applies on each piece. -/
theorem Submission.gaussGreenRep_measure_eq_of_open_eq : ∀ (N : ℕ) (U : Set (Rn N))
    (μ μ' : Measure (Rn N)), IsOpen U → μ Uᶜ = 0 → μ' Uᶜ = 0 →
    (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) →
    (∀ O : Set (Rn N), IsOpen O → O ⊆ U → μ O = μ' O) → μ = μ' := by
  intro N U μ μ' hU hμ hμ' hfin hopen
  -- The open subsets of `U` of finite `μ`-measure cover `U`: each `x ∈ U` lies in a ball
  -- `B_{r/2}(x)` whose compact closure `B̄_{r/2}(x)` is contained in `U`.
  have hSU : ⋃₀ {V : Set (Rn N) | IsOpen V ∧ V ⊆ U ∧ μ V < ∞} = U := by
    refine subset_antisymm (sUnion_subset fun V hV => hV.2.1) fun x hx => ?_
    obtain ⟨r, hr, hxr⟩ := Metric.isOpen_iff.1 hU x hx
    have hcl : Metric.closedBall x (r / 2) ⊆ U :=
      (Metric.closedBall_subset_ball (half_lt_self hr)).trans hxr
    exact mem_sUnion_of_mem (Metric.mem_ball_self (half_pos hr))
      ⟨Metric.isOpen_ball, Metric.ball_subset_closedBall.trans hcl,
        (measure_mono Metric.ball_subset_closedBall).trans_lt
          (hfin _ (isCompact_closedBall x (r / 2)) hcl)⟩
  -- Lindelöf: countably many of them, `T`, still cover `U`.
  obtain ⟨T, hTc, hTS, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable
    {V : Set (Rn N) | IsOpen V ∧ V ⊆ U ∧ μ V < ∞} fun V hV => hV.1
  -- The open sets are a π-system generating the Borel σ-algebra, and `{Uᶜ} ∪ T` is a countable
  -- cover of `ℝᴺ` by sets of finite `μ`-measure on whose traces `μ` and `μ'` agree.
  refine Measure.ext_of_generateFrom_of_cover (S := {s | IsOpen s}) (T := insert Uᶜ T)
    BorelSpace.measurable_eq (hTc.insert _) isPiSystem_isOpen ?_ ?_ ?_ ?_
  · rw [sUnion_insert, hTU, hSU, compl_union_self]
  · rintro t (rfl | ht)
    · rw [hμ]
      exact ENNReal.zero_ne_top
    · exact (hTS ht).2.2.ne
  · rintro t (rfl | ht) s (hs : IsOpen s)
    · rw [measure_mono_null inter_subset_right hμ, measure_mono_null inter_subset_right hμ']
    · exact hopen _ (hs.inter (hTS ht).1) (inter_subset_right.trans (hTS ht).2.1)
  · rintro t (rfl | ht)
    · rw [hμ, hμ']
    · exact hopen _ (hTS ht).1 (hTS ht).2.1
/-- **A bounded field is determined `μ`-a.e. by its pairings** (uniqueness of the normal in the
Gauss–Green identity, Simon Ch. 3, (4.1)): let `U ⊆ ℝᴺ` be open, `μ` carried by `U` and finite on
compact subsets of `U`, and `ν, ν'` `μ`-measurable with `|ν|, |ν'| ≤ 1` `μ`-a.e. If
`∫ ⟨g, ν⟩ dμ = ∫ ⟨g, ν'⟩ dμ` for every continuous `g` compactly supported in `U`, then `ν = ν'`
`μ`-a.e. Bounded fields are integrable on compact subsets of `U`; testing with `g = φ v` (`φ` a
smooth scalar function compactly supported in `U`, `v ∈ ℝᴺ`) gives `∫ φ (ν - ν') dμ = 0`, so
`ν - ν'` vanishes `μ`-a.e. on `U` by the fundamental lemma of the calculus of variations
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`), and `μ(ℝᴺ ∖ U) = 0`. -/
theorem Submission.gaussGreenRep_normal_ae_eq_of_pairing : ∀ (N : ℕ) (U : Set (Rn N))
    (μ : Measure (Rn N)) (ν ν' : Rn N → Rn N), IsOpen U → μ Uᶜ = 0 →
    (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ν μ →
    AEStronglyMeasurable ν' μ → (∀ᵐ x ∂μ, ‖ν x‖ ≤ 1) → (∀ᵐ x ∂μ, ‖ν' x‖ ≤ 1) →
    (∀ g : Rn N → Rn N, Continuous g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ x, inner ℝ (g x) (ν x) ∂μ = ∫ x, inner ℝ (g x) (ν' x) ∂μ) → ν =ᵐ[μ] ν' := by
  intro N U μ ν ν' hU hUc hK hν hν' hν1 hν'1 hpair
  -- A field bounded by `1` is integrable on every compact subset of `U`.
  have hloc : ∀ w : Rn N → Rn N, AEStronglyMeasurable w μ → (∀ᵐ x ∂μ, ‖w x‖ ≤ 1) →
      LocallyIntegrableOn w U μ := fun w hw hw1 =>
    (locallyIntegrableOn_iff hU.isLocallyClosed).2 fun k hkU hk =>
      Measure.integrableOn_of_bounded (hK k hk hkU).ne hw (ae_restrict_of_ae hw1)
  -- Its product with a continuous scalar function compactly supported in `U` is integrable.
  have hint : ∀ w : Rn N → Rn N, LocallyIntegrableOn w U μ → ∀ g : Rn N → ℝ, Continuous g →
      HasCompactSupport g → tsupport g ⊆ U → Integrable (fun x => g x • w x) μ := by
    intro w hw g hg hgc hgU
    refine (integrableOn_iff_integrable_of_support_subset
      ((Function.support_smul_subset_left g w).trans (subset_tsupport g))).1 ?_
    exact (hw.integrableOn_compact_subset hgU hgc.isCompact).continuousOn_smul hg.continuousOn
      hgc.isCompact
  have hlν := hloc ν hν hν1
  have hlν' := hloc ν' hν' hν'1
  -- `ν - ν'` integrates to zero against smooth test functions, so it vanishes a.e. on `U`.
  have h0 : ∀ᵐ x ∂μ, x ∈ U → (ν - ν') x = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hlν.sub hlν') fun g hg hgc hgU => ?_
    have hgν := hint ν hlν g hg.continuous hgc hgU
    have hgν' := hint ν' hlν' g hg.continuous hgc hgU
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub hgν hgν', sub_eq_zero]
    refine ext_inner_left ℝ fun v => ?_
    have e := (innerSL ℝ v).integral_comp_comm hgν
    have e' := (innerSL ℝ v).integral_comp_comm hgν'
    simp only [innerSL_apply_apply] at e e'
    rw [← e, ← e']
    have h := hpair (fun x => g x • v) (hg.continuous.smul continuous_const) hgc.smul_right
      ((tsupport_smul_subset_left _ _).trans hgU)
    simpa only [real_inner_smul_left, real_inner_smul_right] using h
  -- `μ` is carried by `U`.
  filter_upwards [h0, mem_ae_iff.2 hUc] with x hx hxU
  exact sub_eq_zero.1 (hx hxU)

/-- **Simon Ch. 3, (4.1) (p. 80)** (`chapter-03.txt` lines 555–573, with Ch. 2 (2.1)–(2.4),
`chapter-02.txt` lines 477–530): `E` has locally finite perimeter in `U` iff it has a Gauss–Green
pair `(μ, ν)`, and the pair is unique. "⇐" is `gaussGreenRep_isLocallyBV_of_pair`. "⇒": the BV
bound extends `g ↦ ∫_{E ∩ U} div g` to a locally bounded linear functional `Λ` on continuous fields
compactly supported in `U` (`gaussGreenRep_bv_functional_extension`), and the Riesz representation
theorem on `U` (`gaussGreenRep_riesz_on_open`) gives `Λ g = ∫ g · ν₀ dμ`; because of the minus sign
in (4.1) the pair is `(μ, -ν₀)`. Uniqueness: two pairs have the same pairings `∫ g · ν dμ` for all
continuous `g` compactly supported in `U` (`gaussGreenRep_pairing_eq_continuous`), so by the
variation formula (2.4) (`gaussGreenRep_measure_eq_iSup_pairing`) the measures agree on open
subsets of `U`, hence everywhere (`gaussGreenRep_measure_eq_of_open_eq`), and then the normals
agree `μ`-a.e. (`gaussGreenRep_normal_ae_eq_of_pairing`). -/
theorem Submission.gaussGreenRepresentation_holds : GaussGreenRepresentation := by
  intro n U E hU hE
  refine ⟨⟨fun hBV ↦ ?_, fun ⟨μ, ν, h⟩ ↦
    Submission.gaussGreenRep_isLocallyBV_of_pair (n + 1) U E μ ν hU hE h⟩, ?_⟩
  · -- "⇒": represent the extension of `g ↦ ∫_{E ∩ U} div g` to continuous fields; by the
    -- minus sign in (4.1) the normal of the pair is `-ν`.
    obtain ⟨Λ, hadd, hsmul, hbdd, hΛ⟩ :=
      Submission.gaussGreenRep_bv_functional_extension (n + 1) U E hU hE hBV
    obtain ⟨μ, ν, hμU, hμK, hν, hν1, hrep⟩ :=
      Submission.gaussGreenRep_riesz_on_open (n + 1) U Λ hU hadd hsmul hbdd
    refine ⟨μ, -ν, hμU, hμK, hν.neg, ?_, fun g hg hgc hgU ↦ ?_⟩
    · filter_upwards [hν1] with x hx
      rwa [Pi.neg_apply, norm_neg]
    · rw [← hΛ g hg hgc hgU, hrep g hg.continuous hgc hgU]
      simp only [Pi.neg_apply, inner_neg_right, integral_neg, neg_neg]
  · -- Uniqueness: both pairs have the same pairings with continuous fields.
    intro μ μ' ν ν' h h'
    have hpair := Submission.gaussGreenRep_pairing_eq_continuous (n + 1) U E μ μ' ν ν' hU h h'
    obtain ⟨hμU, hμK, hν, hν1, -⟩ := h
    obtain ⟨hμU', hμK', hν', hν1', -⟩ := h'
    -- By the variation formula both measures are the supremum of the same pairings on open
    -- subsets of `U`.
    have hopen : ∀ O : Set (Rn (n + 1)), IsOpen O → O ⊆ U → μ O = μ' O := by
      intro O hO hOU
      rw [Submission.gaussGreenRep_measure_eq_iSup_pairing (n + 1) O μ ν hO
          (fun K hK hKO ↦ hμK K hK (hKO.trans hOU)) hν hν1,
        Submission.gaussGreenRep_measure_eq_iSup_pairing (n + 1) O μ' ν' hO
          (fun K hK hKO ↦ hμK' K hK (hKO.trans hOU)) hν' hν1']
      refine iSup_congr fun g ↦ iSup_congr fun hg ↦ iSup_congr fun hgc ↦ iSup_congr fun hgO ↦ ?_
      rw [hpair g hg hgc (hgO.trans hOU)]
    have hμμ' : μ = μ' :=
      Submission.gaussGreenRep_measure_eq_of_open_eq (n + 1) U μ μ' hU hμU hμU' hμK hopen
    subst hμμ'
    exact ⟨rfl, Submission.gaussGreenRep_normal_ae_eq_of_pairing (n + 1) U _ ν ν' hU hμU hμK hν
      hν' (hν1.mono fun _ hx ↦ hx.le) (hν1'.mono fun _ hx ↦ hx.le) hpair⟩

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
