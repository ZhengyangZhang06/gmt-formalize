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

/-- **The slab around a cone point is covered by two cones**: the covering step in the proof of
P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Lemma 15.14 (M. G. Dall'Alba,
*The Besicovitch–Federer Projection Theorem*, Lemma 4.6), used for Simon Ch. 3, Theorem 3.6
(`chapter-03.txt` lines 530–536, which defers the proof to [Fed69]). With
`Y = {y ∈ S : |P(y - x)| < (s/4)|y - x|} ≠ ∅`, `h = sup_{y ∈ Y} |y - x| ∈ (0, R]` and `x' ∈ Y`
with `|x' - x| > 3h/4`, a point `z ≠ x` of `S` with `|P(z - x)| < sh/4` has `|z - x| ≤ h` by
maximality of `h`; if it is not in the `s`-cone at `x'`, linearity of `P` gives `|z - x'| < h/2`,
hence `|z - x| > h/4` and `z` is in the `s`-cone at `x`. -/
theorem Submission.bf_coneMass_slab_cover : ∀ (N : ℕ) (P : Rn N →L[ℝ] Rn N) (s R : ℝ) (S : Set (Rn N)) (x : Rn N), 0 < s → (∃ y ∈ S, ‖P (y - x)‖ < s / 4 * ‖y - x‖) → (∀ y ∈ S, ‖y - x‖ ≤ R) → ∃ h : ℝ, 0 < h ∧ h ≤ R ∧ ∃ x' ∈ S, S ∩ {z | ‖P (z - x)‖ < s * h / 4} ⊆ insert x ({y | ‖P (y - x)‖ < s * ‖y - x‖} ∩ Metric.ball x (3 * h) ∪ {y | ‖P (y - x')‖ < s * ‖y - x'‖} ∩ Metric.ball x' (3 * h)) := by
  intro N P s R S x hs ⟨y₀, hy₀S, hy₀⟩ hR
  -- Step 1: the cone points `Y` all differ from `x`, since `P 0 = 0`.
  set Y : Set (Rn N) := {y | y ∈ S ∧ ‖P (y - x)‖ < s / 4 * ‖y - x‖}
  have hy₀Y : y₀ ∈ Y := ⟨hy₀S, hy₀⟩
  have hYpos : ∀ y ∈ Y, 0 < ‖y - x‖ := by
    intro y hy
    refine lt_of_le_of_ne (norm_nonneg _) fun h0 ↦ ?_
    have hc := hy.2
    rw [← h0, mul_zero] at hc
    exact (norm_nonneg _).not_gt hc
  -- Step 2: `h = sup {|y - x| : y ∈ Y}` satisfies `0 < h ≤ R` and `|y - x| ≤ h` on `Y`.
  set D : Set ℝ := (fun y ↦ ‖y - x‖) '' Y
  have hDne : D.Nonempty := ⟨_, y₀, hy₀Y, rfl⟩
  have hDbdd : BddAbove D := ⟨R, by rintro _ ⟨y, hy, rfl⟩; exact hR y hy.1⟩
  set h := sSup D
  have hle : ∀ y ∈ Y, ‖y - x‖ ≤ h := fun y hy ↦ le_csSup hDbdd ⟨y, hy, rfl⟩
  have hpos : 0 < h := (hYpos y₀ hy₀Y).trans_le (hle y₀ hy₀Y)
  have hhR : h ≤ R := csSup_le hDne (by rintro _ ⟨y, hy, rfl⟩; exact hR y hy.1)
  -- Step 3: a far cone point `x' ∈ Y` with `3h/4 < |x' - x| ≤ h`.
  obtain ⟨_, ⟨x', hx'Y, rfl⟩, hx'far⟩ :=
    exists_lt_of_lt_csSup hDne (show 3 * h / 4 < h by linarith)
  have hx'le : ‖x' - x‖ ≤ h := hle x' hx'Y
  refine ⟨h, hpos, hhR, x', hx'Y.1, ?_⟩
  -- Step 4: the slab inclusion.
  rintro z ⟨hzS, hz : ‖P (z - x)‖ < s * h / 4⟩
  rw [Set.mem_insert_iff]
  by_cases hzx : z = x
  · exact Or.inl hzx
  right
  -- (a) By maximality of `h`, `|z - x| ≤ h`; hence `z ∈ B(x, 3h)` and `z ∈ B(x', 3h)`.
  have hzle : ‖z - x‖ ≤ h := by
    by_contra hcon
    have hsh := mul_lt_mul_of_pos_left (not_le.mp hcon) hs
    exact hcon (hle z ⟨hzS, by linarith⟩)
  have hzball : z ∈ Metric.ball x (3 * h) := by
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  have hzball' : z ∈ Metric.ball x' (3 * h) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have htri := norm_sub_le_norm_sub_add_norm_sub z x x'
    rw [norm_sub_rev x x'] at htri
    linarith
  by_cases hzc : ‖P (z - x')‖ < s * ‖z - x'‖
  · -- (c) `z` lies in the cone at `x'`.
    exact Or.inr ⟨hzc, hzball'⟩
  · -- (d) Otherwise `|z - x'| < h/2`, so `|z - x| > h/4` and `z` lies in the cone at `x`.
    left
    refine ⟨?_, hzball⟩
    have hsplit : P (z - x') = P (z - x) - P (x' - x) := by
      rw [← map_sub]
      congr 1
      abel
    have hPtri : ‖P (z - x')‖ ≤ ‖P (z - x)‖ + ‖P (x' - x)‖ := by
      rw [hsplit]
      exact norm_sub_le _ _
    have hx'cone : ‖P (x' - x)‖ < s / 4 * ‖x' - x‖ := hx'Y.2
    have hsx' := mul_le_mul_of_nonneg_left hx'le hs.le
    have h1 : s * ‖z - x'‖ < s * (h / 2) := by linarith [not_lt.mp hzc]
    have h2 : ‖z - x'‖ < h / 2 := lt_of_mul_lt_mul_left h1 hs.le
    have h3 : ‖x' - x‖ ≤ ‖z - x'‖ + ‖z - x‖ := by
      have htri := norm_sub_le_norm_sub_add_norm_sub x' z x
      rwa [norm_sub_rev x' z] at htri
    have h4 := mul_lt_mul_of_pos_left (show h / 4 < ‖z - x‖ by linarith) hs
    show ‖P (z - x)‖ < s * ‖z - x‖
    linarith
/-- **Packing disjoint balls centred in an `n`-plane** (Mattila, Lemma 15.14; used in the proof of
Simon Ch. 3, Theorem 3.6). Let `W ⊆ ℝᴺ` be a subspace with `dim W = n` and let `B(w i, ρ i)`,
`i ∈ T` (`T` countable), be pairwise disjoint open balls with `w i ∈ W`, `ρ i > 0`, contained in
`B(w₀, R)` with `w₀ ∈ W`. Then `∑_{i ∈ T} ρ iⁿ ≤ Rⁿ`. The inclusion `W → ℝᴺ` is an isometry and
`μHE[n]` on `W` is an additive Haar measure, so `Hⁿ(W ∩ B(v, r)) = rⁿ ω` for `v ∈ W`, `r > 0`,
with `0 < ω < ∞`; countable additivity on the disjoint Borel pieces `W ∩ B(w i, ρ i)` gives
`ω ∑ ρ iⁿ ≤ ω Rⁿ`, and `ω` cancels. -/
theorem Submission.bf_coneMass_subspace_ball_packing : ∀ (n N : ℕ) (W : Submodule ℝ (Rn N)), finrank ℝ W = n → ∀ (ι : Type) (T : Set ι) (w : ι → Rn N) (ρ : ι → ℝ) (w₀ : Rn N) (R : ℝ), T.Countable → (∀ i ∈ T, w i ∈ W) → w₀ ∈ W → (∀ i ∈ T, 0 < ρ i) → T.PairwiseDisjoint (fun i ↦ Metric.ball (w i) (ρ i)) → (∀ i ∈ T, Metric.ball (w i) (ρ i) ⊆ Metric.ball w₀ R) → ∑' i : T, ENNReal.ofReal (ρ i ^ n) ≤ ENNReal.ofReal (R ^ n) := by
  intro n N W hW ι T w ρ w₀ R hTc hwW hw₀ hρ hdisj hsub
  -- Step 1: if `T = ∅` the sum vanishes; otherwise a nonempty ball inside `B(w₀, R)` forces `R > 0`.
  rcases T.eq_empty_or_nonempty with hT | ⟨i₀, hi₀⟩
  · subst hT; simp
  have hR : 0 < R :=
    dist_nonneg.trans_lt (hsub i₀ hi₀ (Metric.mem_ball_self (hρ i₀ hi₀)))
  -- Steps 2–3: `Hⁿ(W ∩ B(v, r)) = ofReal (rⁿ) * ω` for `v ∈ W`, `r > 0`, with `0 < ω < ∞`.
  obtain ⟨ω, hω0, hωtop, hball⟩ : ∃ ω : ℝ≥0∞, ω ≠ 0 ∧ ω ≠ ⊤ ∧ ∀ v ∈ W, ∀ r : ℝ, 0 < r →
      μHE[n] ((W : Set (Rn N)) ∩ Metric.ball v r) = ENNReal.ofReal (r ^ n) * ω := by
    subst hW
    refine ⟨(μHE[finrank ℝ W] : Measure W) (Metric.ball 0 1),
      (Metric.measure_ball_pos _ _ one_pos).ne', measure_ball_lt_top.ne, fun v hv r hr ↦ ?_⟩
    -- The ambient piece `W ∩ B(v, r)` is the image of the intrinsic ball `B_W(v, r)`.
    have himg : (W : Set (Rn N)) ∩ Metric.ball v r =
        (Subtype.val : W → Rn N) '' Metric.ball (⟨v, hv⟩ : W) r := by
      ext z
      constructor
      · rintro ⟨hzW, hz⟩
        exact ⟨⟨z, hzW⟩, by simpa [Metric.mem_ball, Subtype.dist_eq] using hz, rfl⟩
      · rintro ⟨⟨z, hzW⟩, hz, rfl⟩
        exact ⟨hzW, by simpa [Metric.mem_ball, Subtype.dist_eq] using hz⟩
    rw [himg, isometry_subtype_coe.euclideanHausdorffMeasure_image,
      Measure.addHaar_ball_of_pos _ _ hr]
  -- Steps 4–5: the pieces `W ∩ B(w i, ρ i)` are disjoint Borel subsets of `W ∩ B(w₀, R)`.
  have hWclosed : IsClosed (W : Set (Rn N)) := Submodule.closed_of_finiteDimensional W
  have key : (∑' i : T, ENNReal.ofReal (ρ i ^ n)) * ω ≤ ENNReal.ofReal (R ^ n) * ω := by
    rw [← ENNReal.tsum_mul_right]
    calc ∑' i : T, ENNReal.ofReal (ρ i ^ n) * ω
        = ∑' i : T, μHE[n] ((W : Set (Rn N)) ∩ Metric.ball (w i) (ρ i)) := by
          congr 1; ext i; rw [hball _ (hwW i i.2) _ (hρ i i.2)]
      _ = μHE[n] (⋃ i ∈ T, (W : Set (Rn N)) ∩ Metric.ball (w i) (ρ i)) := by
          rw [measure_biUnion hTc]
          · intro i hi j hj hij
            exact Disjoint.mono inter_subset_right inter_subset_right (hdisj hi hj hij)
          · intro i _
            exact hWclosed.measurableSet.inter measurableSet_ball
      _ ≤ μHE[n] ((W : Set (Rn N)) ∩ Metric.ball w₀ R) :=
          measure_mono (iUnion₂_subset fun i hi ↦ inter_subset_inter_right _ (hsub i hi))
      _ = ENNReal.ofReal (R ^ n) * ω := hball w₀ hw₀ R hR
  -- Step 6: cancel `ω ∈ (0, ∞)`.
  exact (ENNReal.mul_le_mul_iff_left hω0 hωtop).1 key
/-- **Cone-free sets are countably `n`-rectifiable** (P. Mattila, *Geometry of Sets and Measures
in Euclidean Spaces*, Lemma 15.13; M. G. Dall'Alba, *The Besicovitch–Federer Projection
Theorem*, Padova 2020, Lemma 4.5), used in Step 2 of the proof of the Besicovitch–Federer
projection theorem (Simon Ch. 3, Theorem 3.6). Let `W ⊆ ℝᴺ` be an `n`-plane with orthogonal
projection `P`, and let `s|b - a| ≤ |P(b - a)|` for `a, b ∈ E` with `|b - a| < r`. Cover `E` by
the pieces `E_k = E ∩ B(d_k, r/2)`, `(d_k)` dense. On `E_k` the projection `P` is injective with
an `s⁻¹`-Lipschitz inverse `φ_k` on `P(E_k)`; extend `φ_k` to a Lipschitz `G_k : ℝᴺ → ℝᴺ`
(McShane, `LipschitzOnWith.extend_finite_dimension`) and precompose with a linear isometry
`J : ℝⁿ → ℝᴺ` onto `W`. Then `E_k ⊆ (G_k ∘ J)(ℝⁿ)`, and `M₀ = ∅` works. -/
theorem Submission.bf_coneFree_countablyRectifiable :
    ∀ (n ℓ : ℕ) (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∀ (s r : ℝ), 0 < s → 0 < r →
      ∀ E : Set (Rn (n + ℓ)), (∀ a ∈ E, ∀ b ∈ E, dist b a < r →
        s * ‖b - a‖ ≤ ‖W.starProjection (b - a)‖) → CountablyRectifiable n E := by
  intro n ℓ W hW s r hs hr E hE
  -- Step 1: the pieces `E_k = E ∩ B(d_k, r/2)` for a dense sequence `(d_k)`; points of one piece
  -- are at distance `< r`, so `s|a - b| ≤ |Pa - Pb|` on each piece.
  let d : ℕ → Rn (n + ℓ) := TopologicalSpace.denseSeq (Rn (n + ℓ))
  let Ek : ℕ → Set (Rn (n + ℓ)) := fun k ↦ E ∩ Metric.ball (d k) (r / 2)
  have hpiece : ∀ k, ∀ a ∈ Ek k, ∀ b ∈ Ek k,
      s * ‖a - b‖ ≤ ‖W.starProjection a - W.starProjection b‖ := by
    intro k a ha b hb
    have hab : dist a b < r :=
      calc dist a b ≤ dist a (d k) + dist (d k) b := dist_triangle _ _ _
        _ < r / 2 + r / 2 := add_lt_add (Metric.mem_ball.1 ha.2) (Metric.mem_ball'.1 hb.2)
        _ = r := add_halves r
    rw [← map_sub]
    exact hE b hb.1 a ha.1 hab
  -- Step 2: `P` is injective on `E_k`, with an `s⁻¹`-Lipschitz inverse `φ_k` on `P(E_k)`.
  have hinj : ∀ k, InjOn W.starProjection (Ek k) := by
    intro k a ha b hb hab
    have h := hpiece k a ha b hb
    rw [hab, sub_self, norm_zero] at h
    have h0 : ‖a - b‖ ≤ 0 := by nlinarith [norm_nonneg (a - b)]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
  let φ : ℕ → Rn (n + ℓ) → Rn (n + ℓ) := fun k ↦ Function.invFunOn W.starProjection (Ek k)
  have hφ : ∀ k, ∀ a ∈ Ek k, φ k (W.starProjection a) = a :=
    fun k ↦ (hinj k).leftInvOn_invFunOn
  have hφLip : ∀ k, LipschitzOnWith (Real.toNNReal s⁻¹) (φ k) (W.starProjection '' Ek k) := by
    intro k
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [hφ k a ha, hφ k b hb, Real.coe_toNNReal _ (inv_nonneg.2 hs.le), dist_eq_norm,
      dist_eq_norm, inv_mul_eq_div, le_div_iff₀' hs]
    exact hpiece k a ha b hb
  -- Step 3: extend `φ_k` to a Lipschitz map `G_k : ℝᴺ → ℝᴺ`.
  choose G hGLip hGEq using fun k ↦ (hφLip k).extend_finite_dimension
  -- Step 4: a linear isometry `J : ℝⁿ → ℝᴺ` onto `W`.
  obtain ⟨ι⟩ : Nonempty (Rn n ≃ₗᵢ[ℝ] W) :=
    ⟨((stdOrthonormalBasis ℝ W).reindex (finCongr hW)).repr.symm⟩
  let J : Rn n →ₗᵢ[ℝ] Rn (n + ℓ) := W.subtypeₗᵢ.comp ι.toLinearIsometry
  have hJ : ∀ x ∈ W, ∃ u, J u = x := fun x hx ↦ ⟨ι.symm ⟨x, hx⟩, by simp [J]⟩
  -- Steps 5–6: `E_k ⊆ (G_k ∘ J)(ℝⁿ)`, so `E ⊆ ∅ ∪ ⋃_k (G_k ∘ J)(ℝⁿ)`.
  refine ⟨∅, measure_empty, fun k ↦ G k ∘ J, fun k ↦ ⟨_, (hGLip k).comp J.lipschitzWith⟩, ?_⟩
  intro a ha
  obtain ⟨k, hk⟩ :=
    (TopologicalSpace.denseRange_denseSeq (Rn (n + ℓ))).exists_dist_lt a (half_pos hr)
  have hak : a ∈ Ek k := ⟨ha, hk⟩
  obtain ⟨u, hu⟩ := hJ _ (W.starProjection_apply_mem a)
  refine Or.inr (mem_iUnion.2 ⟨k, u, ?_⟩)
  show G k (J u) = a
  rw [hu, ← hGEq k ⟨a, hak, rfl⟩, hφ k a hak]

/-- **Small cone mass forces small mass** (P. Mattila, *Geometry of Sets and Measures in
Euclidean Spaces*, Lemma 15.14; M. G. Dall'Alba, *The Besicovitch–Federer Projection Theorem*,
Lemma 4.6), Step 3 of the proof of the Besicovitch–Federer projection theorem (Simon Ch. 3,
Theorem 3.6). Let `W ⊆ ℝ^{n+ℓ}` be an `n`-plane with orthogonal projection `P`, `0 < s < 1`, and
let `B` be purely `n`-unrectifiable with `Hⁿ(B ∩ X(x, r, s)) ≤ c (rs)ⁿ` for `x ∈ B`, `0 < r < δ`,
where `X(x, r, s) = {y : |P(y - x)| < s|y - x|} ∩ B(x, r)`. Then `Hⁿ(B ∩ B(a, δ/8)) ≤ 2·15ⁿ c δⁿ`.
In `B' = B ∩ B(a, δ/8)` the points whose `(s/4)`-cone misses `B'` form a cone-free, hence
rectifiable, hence null set. Every other `x` has a slab `{z : |P(z - x)| < s h(x)/4}` meeting `B'`
in mass `≤ 2c·3ⁿ(s h(x))ⁿ`; the Vitali `5r`-lemma for the balls `B(Px, s h(x)/20)` covers the
rest of `B'` by countably many slabs, and packing the disjoint balls in `W ∩ B(Pa, δ/4)` gives
`∑ (s h(t))ⁿ ≤ 5ⁿ δⁿ`. -/
theorem Submission.bf_coneMass_ball_le : ∀ (n ℓ : ℕ), 0 < n → ∀ (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∀ (s δ c : ℝ), 0 < s → s < 1 → 0 < δ → 0 ≤ c → ∀ B : Set (Rn (n + ℓ)), PurelyUnrectifiable n B → (∀ x ∈ B, ∀ r : ℝ, 0 < r → r < δ → μHE[n] (B ∩ ({y | ‖W.starProjection (y - x)‖ < s * ‖y - x‖} ∩ Metric.ball x r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) → ∀ a : Rn (n + ℓ), μHE[n] (B ∩ Metric.ball a (δ / 8)) ≤ ENNReal.ofReal (2 * 15 ^ n * c * δ ^ n) := by
  intro n ℓ hn W hW s δ c hs hs1 hδ hc B hB hH a
  set P : Rn (n + ℓ) →L[ℝ] Rn (n + ℓ) := W.starProjection
  -- Step 1: `B' = B ∩ B(a, δ/8)` and the points `B''` of `B'` whose `(s/4)`-cone meets `B'`.
  set B' : Set (Rn (n + ℓ)) := B ∩ Metric.ball a (δ / 8)
  set B'' : Set (Rn (n + ℓ)) := {x | x ∈ B' ∧ ∃ y ∈ B', ‖P (y - x)‖ < s / 4 * ‖y - x‖}
  -- Step 2: the cone-free remainder `B' \ B''` is countably rectifiable, hence null.
  have hE : μHE[n] (B' \ B'') = 0 := by
    apply hB
    · intro x hx
      exact hx.1.1
    · apply Submission.bf_coneFree_countablyRectifiable n ℓ W hW (s / 4) 1 (by positivity) one_pos
      intro x hx y hy _
      exact not_lt.1 fun hlt ↦ hx.2 ⟨hx.1, y, hy.1, hlt⟩
  -- Steps 3–4: for `x ∈ B''`, the radius `h x ∈ (0, δ/4]`, the far cone point `x' x ∈ B'` and the
  -- slab inclusion, from `bf_coneMass_slab_cover` (`|y - x| < δ/4` on `B'`).
  have hslab : ∀ x, ∃ h : ℝ, ∃ x' : Rn (n + ℓ), x ∈ B'' → 0 < h ∧ h ≤ δ / 4 ∧ x' ∈ B' ∧
      B' ∩ {z | ‖P (z - x)‖ < s * h / 4} ⊆ insert x ({y | ‖P (y - x)‖ < s * ‖y - x‖} ∩
        Metric.ball x (3 * h) ∪ {y | ‖P (y - x')‖ < s * ‖y - x'‖} ∩ Metric.ball x' (3 * h)) := by
    intro x
    by_cases hx : x ∈ B''
    · obtain ⟨h, hh, hhδ, x', hx', hsub⟩ :=
        Submission.bf_coneMass_slab_cover (n + ℓ) P s (δ / 4) B' x hs hx.2 fun y hy ↦ by
          have h1 : dist y a < δ / 8 := hy.2
          have h2 : dist x a < δ / 8 := hx.1.2
          calc ‖y - x‖ = dist y x := (dist_eq_norm y x).symm
            _ ≤ dist y a + dist x a := dist_triangle_right y x a
            _ ≤ δ / 4 := by linarith
      exact ⟨h, x', fun _ ↦ ⟨hh, hhδ, hx', hsub⟩⟩
    · exact ⟨0, 0, fun h ↦ absurd h hx⟩
  choose h x' hhx using hslab
  -- Step 5: mass of a slab, by (H) at `x` and at `x' x` with `r = 3 h x < δ`, and `Hⁿ{x} = 0`.
  have hsingle : ∀ x : Rn (n + ℓ), μHE[n] ({x} : Set (Rn (n + ℓ))) = 0 := by
    intro x
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
    have := Measure.nullSingletonClass_hausdorff (Rn (n + ℓ))
      (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn)
    simp
  have hmass : ∀ x ∈ B'', μHE[n] (B' ∩ {z | ‖P (z - x)‖ < s * h x / 4}) ≤
      ENNReal.ofReal (2 * 60 ^ n * c) * ENNReal.ofReal ((s * h x / 20) ^ n) := by
    intro x hx
    obtain ⟨hh, hhδ, hx'B, hsub⟩ := hhx x hx
    have hr : 0 < 3 * h x := by linarith
    have hrδ : 3 * h x < δ := by linarith
    have hsub' : B' ∩ {z | ‖P (z - x)‖ < s * h x / 4} ⊆ {x} ∪
        ((B ∩ ({y | ‖W.starProjection (y - x)‖ < s * ‖y - x‖} ∩ Metric.ball x (3 * h x))) ∪
          (B ∩ ({y | ‖W.starProjection (y - x' x)‖ < s * ‖y - x' x‖} ∩
            Metric.ball (x' x) (3 * h x)))) := by
      intro z hz
      have hzB : z ∈ B := hz.1.1
      rcases hsub hz with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨hzB, h2⟩)
      · exact Or.inr (Or.inr ⟨hzB, h3⟩)
    calc μHE[n] (B' ∩ {z | ‖P (z - x)‖ < s * h x / 4})
        ≤ μHE[n] ({x} ∪
          ((B ∩ ({y | ‖W.starProjection (y - x)‖ < s * ‖y - x‖} ∩ Metric.ball x (3 * h x))) ∪
            (B ∩ ({y | ‖W.starProjection (y - x' x)‖ < s * ‖y - x' x‖} ∩
              Metric.ball (x' x) (3 * h x))))) := measure_mono hsub'
      _ ≤ μHE[n] ({x} : Set (Rn (n + ℓ))) +
          (μHE[n] (B ∩ ({y | ‖W.starProjection (y - x)‖ < s * ‖y - x‖} ∩ Metric.ball x (3 * h x))) +
            μHE[n] (B ∩ ({y | ‖W.starProjection (y - x' x)‖ < s * ‖y - x' x‖} ∩
              Metric.ball (x' x) (3 * h x)))) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ 0 + (ENNReal.ofReal (c * (3 * h x * s) ^ n) + ENNReal.ofReal (c * (3 * h x * s) ^ n)) := by
          gcongr
          · rw [hsingle]
          · exact hH x hx.1.1 _ hr hrδ
          · exact hH (x' x) hx'B.1 _ hr hrδ
      _ = ENNReal.ofReal (2 * 60 ^ n * c) * ENNReal.ofReal ((s * h x / 20) ^ n) := by
          rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [div_pow, mul_pow, mul_pow, mul_pow, show (60 : ℝ) ^ n = 3 ^ n * 20 ^ n by
            rw [← mul_pow]; norm_num]
          field_simp
          ring
  -- Step 6: Vitali `5r`-covering of the balls `B(Px, s h x / 20)`, `x ∈ B''` (`τ = 2`); the
  -- disjoint subfamily `T` is countable and its slabs cover `B''`.
  have hρ : ∀ x ∈ B'', 0 < s * h x / 20 := fun x hx ↦ by have := (hhx x hx).1; positivity
  obtain ⟨T, hTB, hTdisj, hTcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun x ↦ Metric.ball (P x) (s * h x / 20)) B'' (fun x ↦ s * h x / 20) 2 one_lt_two
    (fun x hx ↦ (hρ x hx).le) (s * δ / 80)
    (fun x hx ↦ by
      have h1 := (hhx x hx).2.1
      have h2 : s * h x ≤ s * (δ / 4) := mul_le_mul_of_nonneg_left h1 hs.le
      show s * h x / 20 ≤ s * δ / 80
      linarith)
    (fun x hx ↦ Metric.nonempty_ball.2 (hρ x hx))
  have hTc : T.Countable := hTdisj.countable_of_isOpen (fun _ _ ↦ Metric.isOpen_ball)
    (fun x hx ↦ Metric.nonempty_ball.2 (hρ x (hTB hx)))
  have hcov : B'' ⊆ ⋃ t ∈ T, B' ∩ {z | ‖P (z - t)‖ < s * h t / 4} := by
    intro x hx
    obtain ⟨t, htT, ⟨z, hz1, hz2⟩, hle⟩ := hTcov x hx
    have h1 : dist z (P x) < s * h x / 20 := hz1
    have h2 : dist z (P t) < s * h t / 20 := hz2
    have h3 : s * h x / 20 ≤ 2 * (s * h t / 20) := hle
    have hd : dist (P x) (P t) < 3 * (s * h t / 20) :=
      calc dist (P x) (P t) ≤ dist z (P x) + dist z (P t) := dist_triangle_left _ _ _
        _ < s * h x / 20 + s * h t / 20 := add_lt_add h1 h2
        _ ≤ 3 * (s * h t / 20) := by linarith
    have ht := (hhx t (hTB htT)).1
    refine mem_iUnion₂.2 ⟨t, htT, hx.1, ?_⟩
    show ‖P (x - t)‖ < s * h t / 4
    rw [map_sub, ← dist_eq_norm]
    have : 0 < s * h t := mul_pos hs ht
    linarith
  -- Step 7: packing the disjoint balls `B(Pt, s h t / 20) ⊆ B(Pa, δ/4)` centred in `W`.
  have hpack : ∑' t : T, ENNReal.ofReal ((s * h t / 20) ^ n) ≤ ENNReal.ofReal ((δ / 4) ^ n) :=
    Submission.bf_coneMass_subspace_ball_packing n (n + ℓ) W hW (Rn (n + ℓ)) T (fun x ↦ P x)
      (fun x ↦ s * h x / 20) (P a) (δ / 4) hTc (fun x _ ↦ W.starProjection_apply_mem x)
      (W.starProjection_apply_mem a) (fun x hx ↦ hρ x (hTB hx)) hTdisj
      (fun t ht ↦ by
        apply Metric.ball_subset_ball'
        have h1 : dist (P t) (P a) ≤ dist t a := by
          rw [dist_eq_norm, dist_eq_norm, ← map_sub]
          exact W.norm_starProjection_apply_le _
        have h2 : dist t a < δ / 8 := (hTB ht).1.2
        have h3 : h t ≤ δ / 4 := (hhx t (hTB ht)).2.1
        have h4 : s * h t ≤ 1 * (δ / 4) :=
          mul_le_mul hs1.le h3 (hhx t (hTB ht)).1.le zero_le_one
        show s * h t / 20 + dist (P t) (P a) ≤ δ / 4
        linarith)
  -- Steps 8–9: `Hⁿ(B') ≤ Hⁿ(B'') ≤ ∑_{t ∈ T} 2c·60ⁿ (s h t / 20)ⁿ ≤ 2c·60ⁿ (δ/4)ⁿ = 2·15ⁿ c δⁿ`.
  calc μHE[n] (B ∩ Metric.ball a (δ / 8)) = μHE[n] B' := rfl
    _ ≤ μHE[n] B'' + μHE[n] (B' \ B'') := by
        calc μHE[n] B' ≤ μHE[n] (B'' ∪ (B' \ B'')) := measure_mono fun x hx ↦ by
              by_cases hxx : x ∈ B''
              · exact Or.inl hxx
              · exact Or.inr ⟨hx, hxx⟩
          _ ≤ _ := measure_union_le _ _
    _ = μHE[n] B'' := by rw [hE, add_zero]
    _ ≤ μHE[n] (⋃ t ∈ T, B' ∩ {z | ‖P (z - t)‖ < s * h t / 4}) := measure_mono hcov
    _ ≤ ∑' t : T, μHE[n] (B' ∩ {z | ‖P (z - t)‖ < s * h t / 4}) := measure_biUnion_le _ hTc _
    _ ≤ ∑' t : T, ENNReal.ofReal (2 * 60 ^ n * c) * ENNReal.ofReal ((s * h t / 20) ^ n) :=
        ENNReal.tsum_le_tsum fun t ↦ hmass t (hTB t.2)
    _ = ENNReal.ofReal (2 * 60 ^ n * c) * ∑' t : T, ENNReal.ofReal ((s * h t / 20) ^ n) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (2 * 60 ^ n * c) * ENNReal.ofReal ((δ / 4) ^ n) := by gcongr
    _ = ENNReal.ofReal (2 * 15 ^ n * c * δ ^ n) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [div_pow, show (60 : ℝ) ^ n = 15 ^ n * 4 ^ n by rw [← mul_pow]; norm_num]
        field_simp

/-- **Vanishing cone density happens only on an `Hⁿ`-null set** (Steps 4–5 of the proof of
Simon Ch. 3, Theorem 3.6, `chapter-03.txt` lines 530–536, whose proof Simon defers to
[Fed69]/[Ros84]; Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, 15.15–15.16;
Dall'Alba, Cor. 4.7 and Lemma 5.2). Let `Z` be the set of `a ∈ A` where, for every `c > 0`,
`Hⁿ(A ∩ X(a, r, s)) ≤ c (rs)ⁿ` for all `0 < r < δ` and all small `s > 0`. Fix `c > 0` and `b`.
The points of `Z` where this bound holds for all `s < 1/(i+2)` form sets `Zᵢ ⊆ A` increasing to
`Z`; each `Zᵢ` is purely unrectifiable and satisfies the cone hypothesis of `bf_coneMass_ball_le`
with aperture `1/(2(i+2))`, so `Hⁿ(Zᵢ ∩ B(b, δ/8)) ≤ 2·15ⁿ c δⁿ`. Continuity from below (valid for
arbitrary sets) gives the same bound for `Z ∩ B(b, δ/8)`, which is therefore null (`c ↓ 0`), and
`Z` is covered by countably many such balls. -/
theorem Submission.bf_coneDensity_zero_null : ∀ (n ℓ : ℕ), 0 < n →
    ∀ (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∀ A : Set (Rn (n + ℓ)),
    PurelyUnrectifiable n A → ∀ δ : ℝ, 0 < δ →
    μHE[n] {a | a ∈ A ∧ ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
      ∀ r : ℝ, 0 < r → r < δ →
        μHE[n] (A ∩ ({x | ‖W.starProjection (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r)) ≤
          ENNReal.ofReal (c * (r * s) ^ n)} = 0 := by
  intro n ℓ hn W hW A hA δ hδ
  set Z := {a | a ∈ A ∧ ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
    ∀ r : ℝ, 0 < r → r < δ →
      μHE[n] (A ∩ ({x | ‖W.starProjection (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r)) ≤
        ENNReal.ofReal (c * (r * s) ^ n)}
  -- Steps 1–3: for `c > 0`, `Hⁿ(Z ∩ B(b, δ/8)) ≤ 2·15ⁿ c δⁿ`.
  have hbound : ∀ c : ℝ, 0 < c → ∀ b : Rn (n + ℓ),
      μHE[n] (Z ∩ Metric.ball b (δ / 8)) ≤ ENNReal.ofReal (2 * 15 ^ n * c * δ ^ n) := by
    intro c hc b
    -- `Zᵢ`: the points of `Z` where the bound holds for all `s < 1/(i+2)`.
    set Zi : ℕ → Set (Rn (n + ℓ)) := fun i ↦ {a | a ∈ Z ∧ ∀ s : ℝ, 0 < s → s < 1 / (i + 2) →
      ∀ r : ℝ, 0 < r → r < δ →
        μHE[n] (A ∩ ({x | ‖W.starProjection (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r)) ≤
          ENNReal.ofReal (c * (r * s) ^ n)}
    have hZiA : ∀ i, Zi i ⊆ A := fun i a ha ↦ ha.1.1
    have hmono : Monotone fun i ↦ Zi i ∩ Metric.ball b (δ / 8) := by
      intro i j hij a ha
      refine ⟨⟨ha.1.1, fun s hs hsj r hr hrδ ↦ ha.1.2 s hs (hsj.trans_le ?_) r hr hrδ⟩, ha.2⟩
      have hij' : (i : ℝ) ≤ j := Nat.cast_le.2 hij
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    -- The `Zᵢ` exhaust `Z`: if the bound holds for `s < ε` and `1/(i+1) < ε`, then `a ∈ Zᵢ`.
    have hunion : (⋃ i, Zi i ∩ Metric.ball b (δ / 8)) = Z ∩ Metric.ball b (δ / 8) := by
      refine Subset.antisymm (iUnion_subset fun i ↦ inter_subset_inter_left _ fun a ha ↦ ha.1) ?_
      rintro a ⟨haZ, hab⟩
      obtain ⟨ε, hε, hεs⟩ := haZ.2 c hc
      obtain ⟨i, hi⟩ := exists_nat_one_div_lt hε
      refine mem_iUnion.2 ⟨i, ⟨haZ, fun s hs hsi r hr hrδ ↦ hεs s hs ?_ r hr hrδ⟩, hab⟩
      calc s < 1 / ((i : ℝ) + 2) := hsi
        _ ≤ 1 / ((i : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) (by linarith)
        _ < ε := hi
    -- Each `Zᵢ` satisfies the hypotheses of `bf_coneMass_ball_le` with `s = 1/(2(i+2))`.
    have hZi_bound : ∀ i : ℕ,
        μHE[n] (Zi i ∩ Metric.ball b (δ / 8)) ≤ ENNReal.ofReal (2 * 15 ^ n * c * δ ^ n) := by
      intro i
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have hs0 : (0 : ℝ) < 1 / (2 * ((i : ℝ) + 2)) := by positivity
      have hsi : 1 / (2 * ((i : ℝ) + 2)) < 1 / ((i : ℝ) + 2) :=
        one_div_lt_one_div_of_lt (by positivity) (by linarith)
      have hs1 : 1 / (2 * ((i : ℝ) + 2)) < 1 := (div_lt_one (by positivity)).2 (by linarith)
      refine Submission.bf_coneMass_ball_le n ℓ hn W hW _ δ c hs0 hs1 hδ hc.le (Zi i)
        (hA.mono (hZiA i)) ?_ b
      intro x hx r hr hrδ
      exact (measure_mono (inter_subset_inter_left _ (hZiA i))).trans (hx.2 _ hs0 hsi r hr hrδ)
    rw [← hunion, hmono.measure_iUnion]
    exact iSup_le hZi_bound
  -- Step 4: letting `c ↓ 0`, `Hⁿ(Z ∩ B(b, δ/8)) = 0`.
  have hnull : ∀ b : Rn (n + ℓ), μHE[n] (Z ∩ Metric.ball b (δ / 8)) = 0 := by
    intro b
    have hlim : Tendsto (fun c : ℝ ↦ ENNReal.ofReal (2 * 15 ^ n * c * δ ^ n)) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun c : ℝ ↦ 2 * 15 ^ n * c * δ ^ n) (𝓝 0) (𝓝 0) :=
        (by fun_prop : Continuous fun c : ℝ ↦ 2 * 15 ^ n * c * δ ^ n).tendsto' 0 0 (by simp)
      rw [← ENNReal.ofReal_zero]
      exact (ENNReal.tendsto_ofReal h).mono_left nhdsWithin_le_nhds
    exact le_antisymm
      (ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun c hc ↦ hbound c hc b)) zero_le
  -- Step 5: every point of `Z` has the null neighbourhood `Z ∩ B(a, δ/8)` in `Z`.
  exact measure_null_of_locally_null Z fun a _ ↦ ⟨Z ∩ Metric.ball a (δ / 8),
    inter_mem_nhdsWithin Z (Metric.ball_mem_nhds a (div_pos hδ (by norm_num))), hnull a⟩
/-- **Hausdorff measure of closed discs in an `n`-plane** (Simon Ch. 1, Theorem 2.9,
`chapter-01.txt` lines 445–470: `Lⁿ = Hⁿ` on `ℝⁿ`, transported to an `n`-dimensional subspace).
For a subspace `W ⊆ ℝᴺ` with `dim W = n`, `ω = Hⁿ(W ∩ B̄(0, 1)) < ∞` and
`Hⁿ(W ∩ B̄(y, ρ)) = ρⁿ ω` for every `y ∈ W` and `ρ ≥ 0`. The inclusion `W → ℝᴺ` is an isometry
mapping the intrinsic ball `B̄_W(y, ρ)` onto `W ∩ B̄(y, ρ)`, and `μHE[n]` on `W` is an additive
Haar measure, finite on the compact unit ball and scaling closed balls by `ρⁿ`. -/
theorem Submission.bf_plane_closedBall_measure_eq : ∀ (n N : ℕ) (W : Submodule ℝ (Rn N)), finrank ℝ W = n → μHE[n] ((W : Set (Rn N)) ∩ Metric.closedBall 0 1) < ∞ ∧ ∀ y ∈ W, ∀ ρ : ℝ, 0 ≤ ρ → μHE[n] ((W : Set (Rn N)) ∩ Metric.closedBall y ρ) = ENNReal.ofReal (ρ ^ n) * μHE[n] ((W : Set (Rn N)) ∩ Metric.closedBall 0 1) := by
  intro n N W hW
  subst hW
  -- The ambient disc `W ∩ B̄(y, ρ)` is the image of the intrinsic ball `B̄_W(y, ρ)`.
  have himg : ∀ (y : W) (ρ : ℝ), (W : Set (Rn N)) ∩ Metric.closedBall (y : Rn N) ρ =
      Subtype.val '' Metric.closedBall y ρ := by
    intro y ρ
    ext x
    constructor
    · rintro ⟨hxW, hx⟩
      exact ⟨⟨x, hxW⟩, by simpa [Metric.mem_closedBall, Subtype.dist_eq] using hx, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, by simpa [Metric.mem_closedBall, Subtype.dist_eq] using hz⟩
  -- The inclusion is an isometry, so `Hⁿ(W ∩ B̄(y, ρ))` is the intrinsic `μHE[n]` of the ball.
  have hmeas : ∀ (y : W) (ρ : ℝ),
      μHE[finrank ℝ W] ((W : Set (Rn N)) ∩ Metric.closedBall (y : Rn N) ρ) =
        (μHE[finrank ℝ W] : Measure W) (Metric.closedBall y ρ) := by
    intro y ρ
    rw [himg, isometry_subtype_coe.euclideanHausdorffMeasure_image]
  have h01 := hmeas 0 1
  simp only [ZeroMemClass.coe_zero] at h01
  refine ⟨?_, ?_⟩
  · -- `μHE[n]` is an additive Haar measure on `W`, hence finite on the compact unit ball.
    rw [h01]
    exact (isCompact_closedBall _ _).measure_lt_top
  · -- Scaling of closed balls under the additive Haar measure `μHE[n]` on `W`.
    intro y hy ρ hρ
    rw [show y = ((⟨y, hy⟩ : W) : Rn N) from rfl, hmeas ⟨y, hy⟩ ρ, h01,
      Measure.addHaar_closedBall' _ _ hρ]
/-- Vitali covering for `Hⁿ` by closed discs in an `n`-plane `W ⊆ ℝᴺ`: the Symmetric Vitali
Property of Simon Ch. 1, Def. 3.10, for the doubling measure `Hⁿ ⌞ W` (`chapter-01.txt` lines
765–799; Remark 3.11(2) derives it from the 5-times covering lemma 3.4 and Corollary 3.5, lines
609–660). If the discs `W ∩ B̄(c i, ρ i)` (`i ∈ t`, `c i ∈ W`, `ρ i > 0`) cover an arbitrary
`S ⊆ W` finely, then countably many pairwise disjoint ones cover `Hⁿ`-almost all of `S`. As
`Hⁿ(W) = ∞` for `n ≥ 1`, Simon's finite-mass hypothesis is unavailable; we use instead the locally
finite form `Vitali.exists_disjoint_covering_ae` on the subtype `W`, where `μHE[finrank W]` is an
additive Haar measure whose closed balls are `3ⁿ`-doubling (`Measure.addHaar_closedBall'`), and
transfer the result along the isometric inclusion `W → ℝᴺ`. -/
theorem Submission.bf_plane_vitali_disjoint_cover : ∀ (n N : ℕ) (W : Submodule ℝ (Rn N)),
    finrank ℝ W = n → ∀ (ι : Type) (S : Set (Rn N)) (t : Set ι) (c : ι → Rn N) (ρ : ι → ℝ),
      S ⊆ (W : Set (Rn N)) → (∀ i ∈ t, c i ∈ W ∧ 0 < ρ i) →
        (∀ x ∈ S, ∀ ε : ℝ, 0 < ε → ∃ i ∈ t, c i = x ∧ ρ i ≤ ε) →
          ∃ u ⊆ t, u.Countable ∧
            u.PairwiseDisjoint (fun i ↦ (W : Set (Rn N)) ∩ Metric.closedBall (c i) (ρ i)) ∧
            μHE[n] (S \ ⋃ i ∈ u, ((W : Set (Rn N)) ∩ Metric.closedBall (c i) (ρ i))) = 0 := by
  intro n N W hW ι S t c ρ hSW hct hfine
  -- work intrinsically on the subtype `W`, with `n = finrank W`
  subst hW
  classical
  set μ : Measure W := μHE[finrank ℝ W]
  -- lifted centres `c' i ∈ W` and balls `B i = B̄_W(c' i, ρ i)`
  let c' : ι → W := fun i ↦ if h : c i ∈ W then ⟨c i, h⟩ else 0
  have hc' : ∀ i ∈ t, (c' i : Rn N) = c i := by
    intro i hi
    simp [c', (hct i hi).1]
  let B : ι → Set W := fun i ↦ Metric.closedBall (c' i) (ρ i)
  -- the inclusion maps `B i` onto the disc `W ∩ B̄(c i, ρ i)`
  have himg : ∀ i ∈ t, Subtype.val '' B i = (W : Set (Rn N)) ∩ Metric.closedBall (c i) (ρ i) := by
    intro i hi
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, ?_⟩
      have : dist z (c' i) ≤ ρ i := hz
      rwa [Subtype.dist_eq, hc' i hi] at this
    · rintro ⟨hxW, hx⟩
      refine ⟨⟨x, hxW⟩, ?_, rfl⟩
      show dist (⟨x, hxW⟩ : W) (c' i) ≤ ρ i
      rwa [Subtype.dist_eq, hc' i hi]
  -- hypotheses of the Vitali theorem: doubling with constant `3ⁿ`, nonempty interiors,
  -- closedness and fineness at the preimage `S'` of `S` in `W`
  have hdoub : ∀ i ∈ t, μ (Metric.closedBall (c' i) (3 * ρ i)) ≤
      ((3 ^ finrank ℝ W : ℝ≥0) : ℝ≥0∞) * μ (B i) := by
    intro i hi
    have hρ : 0 ≤ ρ i := (hct i hi).2.le
    rw [Measure.addHaar_closedBall' μ _ (by positivity), Measure.addHaar_closedBall' μ _ hρ,
      mul_pow, ENNReal.ofReal_mul (by positivity), mul_assoc]
    gcongr
    rw [ENNReal.ofReal_pow (by norm_num)]
    simp
  have hint : ∀ i ∈ t, (interior (B i)).Nonempty := fun i hi ↦
    ⟨c' i, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self (hct i hi).2)⟩
  have hclosed : ∀ i ∈ t, IsClosed (B i) := fun i _ ↦ Metric.isClosed_closedBall
  have hfine' : ∀ x ∈ (Subtype.val ⁻¹' S : Set W), ∀ ε > (0 : ℝ), ∃ a ∈ t, ρ a ≤ ε ∧ c' a = x := by
    intro x hx ε hε
    obtain ⟨i, hi, hcx, hρε⟩ := hfine x hx ε hε
    exact ⟨i, hi, hρε, Subtype.ext (by rw [hc' i hi, hcx])⟩
  obtain ⟨u, hut, hu, hdisj, hnull⟩ := Vitali.exists_disjoint_covering_ae μ (Subtype.val ⁻¹' S) t
    (3 ^ finrank ℝ W) ρ c' B (fun i _ ↦ subset_rfl) hdoub hint hclosed hfine'
  refine ⟨u, hut, hu, ?_, ?_⟩
  -- the inclusion is injective, so the discs are pairwise disjoint
  · intro i hi j hj hij
    simp only [Function.onFun]
    rw [← himg i (hut hi), ← himg j (hut hj)]
    exact (disjoint_image_iff Subtype.val_injective).mpr (hdisj hi hj hij)
  -- `S \ ⋃ discs` is the image of `S' \ ⋃ B i`, and the inclusion preserves `μHE[n]`
  · have hset : S \ ⋃ i ∈ u, ((W : Set (Rn N)) ∩ Metric.closedBall (c i) (ρ i)) =
        Subtype.val '' ((Subtype.val ⁻¹' S : Set W) \ ⋃ i ∈ u, B i) := by
      ext x
      constructor
      · rintro ⟨hxS, hxU⟩
        refine ⟨⟨x, hSW hxS⟩, ⟨hxS, fun hmem ↦ hxU ?_⟩, rfl⟩
        obtain ⟨i, hi, hiB⟩ := mem_iUnion₂.1 hmem
        exact mem_iUnion₂.2 ⟨i, hi, himg i (hut hi) ▸ ⟨_, hiB, rfl⟩⟩
      · rintro ⟨z, ⟨hzS, hzU⟩, rfl⟩
        refine ⟨hzS, fun hmem ↦ hzU ?_⟩
        obtain ⟨i, hi, hiD⟩ := mem_iUnion₂.1 hmem
        rw [← himg i (hut hi)] at hiD
        obtain ⟨w, hw, hwz⟩ := hiD
        exact mem_iUnion₂.2 ⟨i, hi, Subtype.ext hwz ▸ hw⟩
    rw [hset, isometry_subtype_coe.euclideanHausdorffMeasure_image]
    exact hnull

/-- **Infinite cone density has `Hⁿ`-null projection** (M. G. Dall'Alba, *The Besicovitch–Federer
Projection Theorem*, Lemma 5.3; P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*,
Ch. 18). Let `W ⊆ ℝ^{n+ℓ}` be an `n`-plane with orthogonal projection `P`, `A` compact with
`Hⁿ(A) < ∞`, `δ > 0`, and `A₂` the set of `a ∈ A` with infinite cone density `Φ_δ(a, W^⊥)`: for
every `K` and `ε > 0` there are `0 < s < ε`, `0 < r < δ` with `K (rs)ⁿ ≤ Hⁿ(A ∩ X(a, r, s))`, where
`X(a, r, s) = {x : |P(x - a)| < s |x - a|} ∩ B_r(a)`. Then `Hⁿ(P(A₂)) = 0`. For fixed `K > 0` the
discs `W ∩ B̄(P a, rs)` cover `P(A₂)` finely, so countably many disjoint ones cover `Hⁿ`-almost all
of it (`bf_plane_vitali_disjoint_cover`). The cone pieces `A ∩ X(a, r, s)` project into their
discs, hence are disjoint Borel subsets of `A`, and with `ω = Hⁿ(W ∩ B̄(0, 1))`
(`bf_plane_closedBall_measure_eq`), `Hⁿ(P(A₂)) ≤ Σ ω (rs)ⁿ ≤ (ω / K) Hⁿ(A) → 0` as `K → ∞`. -/
theorem Submission.bf_coneDensity_top_projection_null : ∀ (n ℓ : ℕ), 0 < n → ∀ (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∀ A : Set (Rn (n + ℓ)), IsCompact A → μHE[n] A < ∞ → ∀ δ : ℝ, 0 < δ → μHE[n] (W.starProjection '' {a | a ∈ A ∧ ∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μHE[n] (A ∩ ({x | ‖W.starProjection (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r))}) = 0 := by
  intro n ℓ _hn W hW A hA hAfin δ hδ
  set P := W.starProjection
  set A₂ := {a | a ∈ A ∧ ∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧
    r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤
      μHE[n] (A ∩ ({x | ‖P (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r))}
  set T := P '' A₂
  obtain ⟨hωfin, hball⟩ := Submission.bf_plane_closedBall_measure_eq n (n + ℓ) W hW
  set ω := μHE[n] ((W : Set (Rn (n + ℓ))) ∩ Metric.closedBall 0 1)
  have hTW : T ⊆ (W : Set (Rn (n + ℓ))) := by
    rintro _ ⟨b, -, rfl⟩
    exact W.starProjection_apply_mem b
  -- Step 1: a point `a y ∈ A₂` over each `y ∈ P(A₂)`
  have hpre : ∀ y ∈ T, ∃ a, a ∈ A₂ ∧ P a = y := fun y hy ↦ hy
  choose! a ha using hpre
  -- the cone pieces `A ∩ X(b, r, s)` are Borel
  let X : Rn (n + ℓ) → ℝ → ℝ → Set (Rn (n + ℓ)) := fun b r s ↦
    {x | ‖P (x - b)‖ < s * ‖x - b‖} ∩ Metric.ball b r
  have hXmeas : ∀ b r s, MeasurableSet (A ∩ X b r s) := by
    intro b r s
    refine hA.isClosed.measurableSet.inter (IsOpen.measurableSet ?_)
    refine IsOpen.inter (isOpen_lt ?_ ?_) Metric.isOpen_ball
    · exact (P.continuous.comp (continuous_id.sub continuous_const)).norm
    · exact continuous_const.mul (continuous_id.sub continuous_const).norm
  -- Step 4: `|P x - y| = |P(x - a y)| < s |x - a y| < rs`, so `P(X(a y, r, s)) ⊆ W ∩ B̄(y, rs)`
  have hXproj : ∀ y ∈ T, ∀ r s : ℝ, 0 < s → ∀ x ∈ X (a y) r s,
      P x ∈ (W : Set (Rn (n + ℓ))) ∩ Metric.closedBall y (r * s) := by
    intro y hy r s hs x hx
    refine ⟨W.starProjection_apply_mem x, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm,
      show P x - y = P (x - a y) by rw [map_sub, (ha y hy).2]]
    have h2 : ‖x - a y‖ < r := by simpa [dist_eq_norm] using hx.2
    have h3 : ‖P (x - a y)‖ < s * ‖x - a y‖ := hx.1
    nlinarith [norm_nonneg (x - a y)]
  -- Steps 1–5 for a fixed `K > 0`: `Hⁿ(P(A₂)) ≤ (ω / K) Hⁿ(A)`
  have key : ∀ K : ℝ, 0 < K → μHE[n] T ≤ ω / ENNReal.ofReal K * μHE[n] A := by
    intro K hK
    let t : Set (Rn (n + ℓ) × ℝ × ℝ) := {i | i.1 ∈ T ∧ 0 < i.2.1 ∧ i.2.1 < δ ∧ 0 < i.2.2 ∧
      ENNReal.ofReal (K * (i.2.1 * i.2.2) ^ n) ≤ μHE[n] (A ∩ X (a i.1) i.2.1 i.2.2)}
    -- Step 2: fineness, with `ε / δ` in the definition of `A₂`
    have hfine : ∀ x ∈ T, ∀ ε : ℝ, 0 < ε → ∃ i ∈ t, i.1 = x ∧ i.2.1 * i.2.2 ≤ ε := by
      intro x hx ε hε
      obtain ⟨s, hs0, hsε, r, hr0, hrδ, hK'⟩ := (ha x hx).1.2 K (ε / δ) (div_pos hε hδ)
      refine ⟨(x, r, s), ⟨hx, hr0, hrδ, hs0, hK'⟩, rfl, ?_⟩
      have : r * s ≤ δ * (ε / δ) := mul_le_mul hrδ.le hsε.le hs0.le hδ.le
      rwa [mul_div_cancel₀ _ hδ.ne'] at this
    -- Step 3: a disjoint Vitali subfamily of discs covering `Hⁿ`-almost all of `P(A₂)`
    obtain ⟨u, hut, hu, hdisj, hnull⟩ := Submission.bf_plane_vitali_disjoint_cover n (n + ℓ) W hW
      (Rn (n + ℓ) × ℝ × ℝ) T t (fun i ↦ i.1) (fun i ↦ i.2.1 * i.2.2) hTW
      (fun i hi ↦ ⟨hTW hi.1, mul_pos hi.2.1 hi.2.2.2.1⟩) hfine
    let D : Rn (n + ℓ) × ℝ × ℝ → Set (Rn (n + ℓ)) := fun i ↦
      (W : Set (Rn (n + ℓ))) ∩ Metric.closedBall i.1 (i.2.1 * i.2.2)
    let Sp : Rn (n + ℓ) × ℝ × ℝ → Set (Rn (n + ℓ)) := fun i ↦ A ∩ X (a i.1) i.2.1 i.2.2
    -- Step 4: the cone pieces project into the disjoint discs, so they are disjoint
    have hSdisj : u.PairwiseDisjoint Sp := by
      intro i hi j hj hij
      refine Set.disjoint_left.2 fun x hxi hxj ↦ ?_
      have hi' := hut hi
      have hj' := hut hj
      exact Set.disjoint_left.1 (hdisj hi hj hij)
        (hXproj i.1 hi'.1 i.2.1 i.2.2 hi'.2.2.2.1 x hxi.2)
        (hXproj j.1 hj'.1 j.2.1 j.2.2 hj'.2.2.2.1 x hxj.2)
    -- Step 5: `Hⁿ(D_i) = ω (rs)ⁿ ≤ (ω / K) Hⁿ(S_i)`
    have hDle : ∀ i ∈ u, μHE[n] (D i) ≤ ω / ENNReal.ofReal K * μHE[n] (Sp i) := by
      intro i hi
      have hi' := hut hi
      have hK1 : ENNReal.ofReal K * ENNReal.ofReal ((i.2.1 * i.2.2) ^ n) ≤ μHE[n] (Sp i) := by
        rw [← ENNReal.ofReal_mul hK.le]
        exact hi'.2.2.2.2
      have hKpos : ENNReal.ofReal K ≠ 0 := by simpa using hK
      calc μHE[n] (D i) = ENNReal.ofReal ((i.2.1 * i.2.2) ^ n) * ω :=
            hball i.1 (hTW hi'.1) _ (mul_pos hi'.2.1 hi'.2.2.2.1).le
        _ = ω / ENNReal.ofReal K * (ENNReal.ofReal K * ENNReal.ofReal ((i.2.1 * i.2.2) ^ n)) := by
            rw [← mul_assoc, ENNReal.div_mul_cancel hKpos ENNReal.ofReal_ne_top, mul_comm]
        _ ≤ ω / ENNReal.ofReal K * μHE[n] (Sp i) := by gcongr
    calc μHE[n] T ≤ μHE[n] (T \ ⋃ i ∈ u, D i) + μHE[n] (⋃ i ∈ u, D i) := by
          refine (measure_mono fun x hx ↦ ?_).trans (measure_union_le _ _)
          by_cases hxU : x ∈ ⋃ i ∈ u, D i
          · exact Or.inr hxU
          · exact Or.inl ⟨hx, hxU⟩
      _ = μHE[n] (⋃ i ∈ u, D i) := by rw [hnull, zero_add]
      _ ≤ ∑' i : u, μHE[n] (D i) := measure_biUnion_le _ hu _
      _ ≤ ∑' i : u, ω / ENNReal.ofReal K * μHE[n] (Sp i) :=
          ENNReal.tsum_le_tsum fun i ↦ hDle i i.2
      _ = ω / ENNReal.ofReal K * ∑' i : u, μHE[n] (Sp i) := ENNReal.tsum_mul_left
      _ = ω / ENNReal.ofReal K * μHE[n] (⋃ i ∈ u, Sp i) := by
          rw [measure_biUnion hu hSdisj fun i _ ↦ hXmeas _ _ _]
      _ ≤ ω / ENNReal.ofReal K * μHE[n] A := by
          gcongr
          exact iUnion₂_subset fun i _ ↦ inter_subset_left
  -- Step 6: let `K → ∞`, using `ω < ∞` and `Hⁿ(A) < ∞`
  have hlim : Tendsto (fun K : ℝ ↦ ω / ENNReal.ofReal K * μHE[n] A) atTop (𝓝 0) := by
    have h2 : Tendsto (fun K : ℝ ↦ ω / ENNReal.ofReal K) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_div ENNReal.tendsto_ofReal_atTop (Or.inr hωfin.ne)
    simpa using ENNReal.Tendsto.mul_const h2 (Or.inr hAfin.ne)
  exact nonpos_iff_eq_zero.mp
    (ge_of_tendsto hlim (by filter_upwards [eventually_gt_atTop 0] with K hK using key K hK))
/-- **Simon Ch. 1, §2 (p. 10)** (`chapter-01.txt` lines 411–412), the `H⁰` of Ch. 3 (2.4):
`H⁰` is counting measure, i.e. `H⁰(S) = #S` for every `S ⊆ ℝᴺ`, with `H⁰(S) = ∞` for infinite `S`.
Since `μHE[0] = μH[0]` and `μH[0]{x} = 1`, additivity over the measurable singletons gives
`H⁰(t) = #t` for finite `t`; an infinite `S` contains `⌈r⌉` points for every `r ≥ 0`, so
`H⁰(S) = ∞` by monotonicity. -/
theorem Submission.bf_hausdorffZero_eq_encard :
    ∀ (N : ℕ) (S : Set (Rn N)), μHE[0] S = (S.encard : ℝ≥0∞) := by
  intro N S
  rw [Measure.euclideanHausdorffMeasure_zero]
  -- Finite sets: sum the unit masses of the measurable singletons.
  have hfin : ∀ t : Finset (Rn N), μH[0] (t : Set (Rn N)) = t.card := by
    intro t
    rw [← sum_measure_singleton]
    simp
  rcases S.finite_or_infinite with hS | hS
  · lift S to Finset (Rn N) using hS
    rw [hfin, Set.encard_coe_eq_coe_finsetCard]
    rfl
  -- Infinite sets: `S` contains `⌈r⌉₊` points for every `r`, so `μH[0] S` is unbounded.
  · rw [Set.encard_eq_top_iff.mpr hS, ENat.toENNReal_top]
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    obtain ⟨t, hts, htc⟩ := hS.exists_subset_card_eq ⌈r⌉₊
    calc (r : ℝ≥0∞) ≤ (⌈r⌉₊ : ℝ≥0∞) := by exact_mod_cast Nat.le_ceil r
      _ = μH[0] (t : Set (Rn N)) := by rw [hfin, htc]
      _ ≤ μH[0] S := measure_mono hts
/-- **Isometric chart of the orthogonal projection onto an `n`-plane** (Dall'Alba, *The
Besicovitch–Federer Projection Theorem*, Lemma 5.4, p. 70, made explicit). For a subspace
`W ⊆ ℝ^{n+ℓ}` with `dim W = n` and `P = W.starProjection`, there is a `1`-Lipschitz
`f : ℝ^{n+ℓ} → ℝⁿ` with the fibres of `P` and `Hⁿ(P(S)) = Lⁿ(f(S))` for every set `S`. Take
`f = ι ∘ π` with `π` the orthogonal projection onto `W` and `ι : W ≃ ℝⁿ` the coordinate map of
an orthonormal basis; then `P = J ∘ f` for the isometry `J = ↑ ∘ ι⁻¹`, and `μHE[n]` is
isometry invariant and equals `volume` on `ℝⁿ`. -/
theorem Submission.bf_starProjection_isometricChart : ∀ (n ℓ : ℕ) (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∃ f : Rn (n + ℓ) → Rn n, LipschitzWith 1 f ∧ (∀ a b : Rn (n + ℓ), f a = f b ↔ W.starProjection a = W.starProjection b) ∧ ∀ S : Set (Rn (n + ℓ)), μHE[n] (W.starProjection '' S) = volume (f '' S) := by
  intro n ℓ W hW
  -- `ι : W ≃ ℝⁿ`, the coordinate map of an orthonormal basis of `W` indexed by `Fin n`.
  let ι : W ≃ₗᵢ[ℝ] Rn n := ((stdOrthonormalBasis ℝ W).reindex (finCongr hW)).repr
  refine ⟨fun x ↦ ι (W.orthogonalProjectionOnto x), ?_, ?_, ?_⟩
  · -- (i) `π` has operator norm `≤ 1` and `ι` is an isometry.
    have h := ι.lipschitzWith.comp W.lipschitzWith_orthogonalProjectionOnto
    rw [one_mul] at h
    exact h
  · -- (ii) `f a = f b ↔ π a = π b ↔ P a = P b`, by injectivity of `ι` and of the inclusion.
    intro a b
    rw [ι.injective.eq_iff, Submodule.starProjection_apply, Submodule.starProjection_apply,
      SetLike.coe_eq_coe]
  · -- (iii) `P = J ∘ f` with `J = ↑ ∘ ι⁻¹` an isometry, and `μHE[n] = volume` on `ℝⁿ`.
    intro S
    have hJ : Isometry (fun y : Rn n ↦ ((ι.symm y : W) : Rn (n + ℓ))) :=
      isometry_subtype_coe.comp ι.symm.isometry
    have hP : W.starProjection '' S =
        (fun y : Rn n ↦ ((ι.symm y : W) : Rn (n + ℓ))) ''
          ((fun x ↦ ι (W.orthogonalProjectionOnto x)) '' S) := by
      rw [Set.image_image]
      refine Set.image_congr fun x _ ↦ ?_
      rw [LinearIsometryEquiv.symm_apply_apply, Submodule.starProjection_apply]
    rw [hP, hJ.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]

/-- **Infinite fibres of an `n`-plane projection project to an `Hⁿ`-null set** (Dall'Alba,
*The Besicovitch–Federer Projection Theorem*, Lemma 5.4, p. 70), assuming Eilenberg's
inequality (Eil). Let `P = W.starProjection`, `dim W = n`, `Hⁿ(A) < ∞` and
`A₃ = {a ∈ A : {b ∈ A : P b = P a} infinite}`. With the `1`-Lipschitz chart `f` of `P`, (Eil)
for `(N, m, k) = (n + ℓ, n, 0)` and `L = 1` gives a measurable `g ≥ H⁰(A ∩ f⁻¹{y})` with
`∫ g dLⁿ ≤ C Hⁿ(A) < ∞`, so `g < ∞` `Lⁿ`-a.e. As `H⁰` is counting measure, `g = ∞` on
`f(A₃)`, hence `Hⁿ(P(A₃)) = Lⁿ(f(A₃)) = 0`. -/
theorem Submission.bf_infiniteFibre_projection_null : (∀ (N m k : ℕ), ∃ C : ℝ≥0, ∀ (A : Set (Rn N)) (f : Rn N → Rn m) (L : ℝ≥0), LipschitzWith L f → ∃ g : Rn m → ℝ≥0∞, Measurable g ∧ (∀ y, μHE[k] (A ∩ f ⁻¹' {y}) ≤ g y) ∧ ∫⁻ y, g y ≤ ((C * L ^ m : ℝ≥0) : ℝ≥0∞) * μHE[m + k] A) → ∀ (n ℓ : ℕ) (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∀ A : Set (Rn (n + ℓ)), μHE[n] A < ∞ → μHE[n] (W.starProjection '' {a | a ∈ A ∧ {b | b ∈ A ∧ W.starProjection b = W.starProjection a}.Infinite}) = 0 := by
  intro hEil n ℓ W hW A hA
  -- The chart `f`: `1`-Lipschitz, with the fibres of `P` and `Hⁿ(P(S)) = Lⁿ(f(S))`.
  obtain ⟨f, hf, hfib, hvol⟩ := Submission.bf_starProjection_isometricChart n ℓ W hW
  -- (Eil) with `(N, m, k) = (n + ℓ, n, 0)` and `L = 1`.
  obtain ⟨C, hC⟩ := hEil (n + ℓ) n 0
  obtain ⟨g, hg, hgle, hgint⟩ := hC A f 1 hf
  -- `∫ g dLⁿ ≤ C Hⁿ(A) < ∞`, so `{g = ∞}` is `Lⁿ`-null.
  have hnull : volume {y | ¬g y < ∞} = 0 :=
    ae_iff.mp (ae_lt_top hg
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hA.ne) hgint))
  -- `f(A₃) ⊆ {g = ∞}`: the fibre of `f` through `a ∈ A₃` meets `A` in infinitely many points.
  rw [hvol]
  refine measure_mono_null ?_ hnull
  rintro _ ⟨a, ⟨-, hinf⟩, rfl⟩
  have hfibre : A ∩ f ⁻¹' {f a} = {b | b ∈ A ∧ W.starProjection b = W.starProjection a} := by
    ext b
    simp [hfib]
  have hfa := hgle (f a)
  rw [hfibre, Submission.bf_hausdorffZero_eq_encard, Set.encard_eq_top_iff.mpr hinf,
    ENat.toENNReal_top] at hfa
  exact not_lt.mpr hfa
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
/-- **Bi-invariant Haar probability on the orthogonal stabilizer of a subspace** (Step 1 of the
frame-averaging argument in the proof of Simon Ch. 3, Theorem 3.6; Mattila, *Geometry of Sets and
Measures in Euclidean Spaces*, Ch. 3). Let `U ⊆ ℝᴺ` be a subspace, `𝓛 = ℝᴺ →L[ℝ] ℝᴺ` and
`K_U = {g ∈ 𝓛 : g* g = 1, g x = x for x ∈ U}`. There is a Borel probability `θ` on `𝓛` with
`θ`-a.e. `g ∈ K_U`, invariant under `g ↦ k g` and `g ↦ g k` for every `k ∈ K_U`. `K_U` is a closed
bounded subgroup of the unitary group of the finite-dimensional `𝓛`, hence a compact group; `θ` is
the image under the inclusion of its Haar probability `μ`, and `μ` is also right invariant by
uniqueness of Haar measure on compact groups. -/
theorem Submission.bf_orthStabilizer_haar_exists : ∀ (N : ℕ) (U : Submodule ℝ (Rn N)), ∃ θ : Measure (Rn N →L[ℝ] Rn N), IsProbabilityMeasure θ ∧ (∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1 ∧ ∀ x ∈ U, g x = x) ∧ ∀ k : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint k * k = 1 → (∀ x ∈ U, k x = x) → Measure.map (fun g ↦ k * g) θ = θ ∧ Measure.map (fun g ↦ g * k) θ = θ := by
  intro N U
  -- Step 3 (topology): the adjoint `g ↦ g*` is continuous, so `star` is continuous on `𝓛` and
  -- `unitary 𝓛` (inversion = `star`) is a topological group.
  have hadj : Continuous (fun g : Rn N →L[ℝ] Rn N ↦ ContinuousLinearMap.adjoint g) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn N) (F := Rn N)).continuous
  have : ContinuousStar (Rn N →L[ℝ] Rn N) := ⟨by
    have h : (star : (Rn N →L[ℝ] Rn N) → (Rn N →L[ℝ] Rn N)) =
        fun g ↦ ContinuousLinearMap.adjoint g := funext ContinuousLinearMap.star_eq_adjoint
    rw [h]
    exact hadj⟩
  have : ContinuousInv (unitary (Rn N →L[ℝ] Rn N)) :=
    ⟨continuous_induced_rng.mpr continuous_subtype_val.star⟩
  have : IsTopologicalGroup (unitary (Rn N →L[ℝ] Rn N)) := {}
  -- Step 1: `g* g = 1` forces `g g* = 1` (`g` is injective, hence surjective), so `g ∈ unitary 𝓛`.
  have hunit : ∀ g : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint g * g = 1 →
      g ∈ unitary (Rn N →L[ℝ] Rn N) := by
    intro g hg
    have hgg : ∀ x, ContinuousLinearMap.adjoint g (g x) = x := fun x ↦ by
      rw [← mul_apply_eq_comp, hg, one_apply_eq_self]
    have hsurj : Function.Surjective g :=
      LinearMap.surjective_of_injective (f := (g : Rn N →ₗ[ℝ] Rn N))
        (Function.LeftInverse.injective hgg)
    rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint]
    refine ⟨hg, ?_⟩
    ext1 y
    obtain ⟨x, rfl⟩ := hsurj y
    rw [mul_apply_eq_comp, hgg, one_apply_eq_self]
  -- Step 2: `K = K_U` as a subgroup of `unitary 𝓛`, with inclusion `ι : K → 𝓛`.
  let K : Subgroup (unitary (Rn N →L[ℝ] Rn N)) :=
    { carrier := {u | ∀ x ∈ U, (u : Rn N →L[ℝ] Rn N) x = x}
      mul_mem' := by
        intro a b ha hb x hx
        change ((a : Rn N →L[ℝ] Rn N) * (b : Rn N →L[ℝ] Rn N)) x = x
        rw [mul_apply_eq_comp, hb x hx, ha x hx]
      one_mem' := fun _ _ ↦ rfl
      inv_mem' := by
        intro a ha x hx
        change (star (a : Rn N →L[ℝ] Rn N)) x = x
        conv_lhs => rw [← ha x hx]
        rw [← mul_apply_eq_comp, Unitary.star_mul_self_of_mem a.2, one_apply_eq_self] }
  let ι : K → Rn N →L[ℝ] Rn N := fun k ↦ ((k : unitary (Rn N →L[ℝ] Rn N)) : Rn N →L[ℝ] Rn N)
  have hι : Continuous ι := continuous_subtype_val.comp continuous_subtype_val
  have hιind : Topology.IsInducing ι :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  -- Step 3: `S = ι(K)` is closed and bounded (`‖g‖ ≤ 1`) in the finite-dimensional `𝓛`, so `K`
  -- is compact.
  set S : Set (Rn N →L[ℝ] Rn N) :=
    {g | ContinuousLinearMap.adjoint g * g = 1 ∧ ∀ x ∈ U, g x = x}
  have hSclosed : IsClosed S := by
    have h1 : IsClosed {g : Rn N →L[ℝ] Rn N | ContinuousLinearMap.adjoint g * g = 1} :=
      isClosed_eq (hadj.mul continuous_id) continuous_const
    have h2 : IsClosed {g : Rn N →L[ℝ] Rn N | ∀ x ∈ U, g x = x} := by
      have : {g : Rn N →L[ℝ] Rn N | ∀ x ∈ U, g x = x} = ⋂ x ∈ U, {g | g x = x} := by
        ext g
        simp
      rw [this]
      exact isClosed_biInter fun x _ ↦
        isClosed_eq (continuous_id.clm_apply continuous_const) continuous_const
    exact h1.inter h2
  have hrange : Set.range ι = S := by
    ext g
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨?_, k.2⟩
      have := Unitary.star_mul_self_of_mem (k : unitary (Rn N →L[ℝ] Rn N)).2
      rwa [ContinuousLinearMap.star_eq_adjoint] at this
    · rintro ⟨hg, hfix⟩
      exact ⟨⟨⟨g, hunit g hg⟩, hfix⟩, rfl⟩
  have hSbdd : Bornology.IsBounded S := by
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1, fun g hg ↦ ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
    have h2 : inner ℝ (g x) (g x) = inner ℝ x x := by
      rw [← ContinuousLinearMap.adjoint_inner_right, ← mul_apply_eq_comp, hg.1, one_apply_eq_self]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h2
    rw [one_mul, (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2]
  have : CompactSpace K := by
    rw [← isCompact_univ_iff, hιind.isCompact_iff, Set.image_univ, hrange]
    exact Metric.isCompact_of_isClosed_isBounded hSclosed hSbdd
  -- Step 4: the Haar measure `μ` on `K` normalized by `μ(K) = 1`.
  let μ : Measure K := Measure.haarMeasure ⊤
  have : IsProbabilityMeasure μ := ⟨by
    have := Measure.haarMeasure_self (G := K) (K₀ := ⊤)
    rw [TopologicalSpace.PositiveCompacts.coe_top] at this
    exact this⟩
  -- Step 5: right invariance of `μ`, by uniqueness of Haar measure on the compact group `K`.
  have hright : ∀ k : K, Measure.map (fun h ↦ h * k) μ = μ := by
    intro k
    set ρ := Measure.map (fun h ↦ h * k) μ with hρ
    have hc := Measure.isMulInvariant_eq_smul_of_compactSpace ρ μ
    have huniv : ρ univ = 1 := by
      rw [hρ, Measure.map_apply (measurable_mul_const k) MeasurableSet.univ, Set.preimage_univ,
        measure_univ]
    have hc1 : ρ.haarScalarFactor μ = 1 := by
      have h := congrArg (fun m : Measure K ↦ m univ) hc
      simp only [Measure.smul_apply, measure_univ, huniv] at h
      have h' : ((ρ.haarScalarFactor μ : ℝ≥0) : ℝ≥0∞) = 1 := by
        simpa [ENNReal.smul_def] using h.symm
      exact_mod_cast h'
    rw [hc1, one_smul] at hc
    exact hc
  -- Steps 6–7: `θ = ι_* μ` is concentrated on `S`, and translations by `k ∈ K_U` commute with `ι`.
  refine ⟨Measure.map ι μ, inferInstance, ?_, ?_⟩
  · rw [ae_map_iff hι.aemeasurable hSclosed.measurableSet]
    exact Eventually.of_forall fun k ↦ (hrange ▸ ⟨k, rfl⟩ : ι k ∈ S)
  · intro k hk hfix
    let k' : K := ⟨⟨k, hunit k hk⟩, hfix⟩
    have hl : Measurable (fun g : Rn N →L[ℝ] Rn N ↦ k * g) := measurable_const_mul k
    have hr : Measurable (fun g : Rn N →L[ℝ] Rn N ↦ g * k) := measurable_mul_const k
    constructor
    · rw [Measure.map_map hl hι.measurable]
      have : (fun g : Rn N →L[ℝ] Rn N ↦ k * g) ∘ ι = ι ∘ (fun h : K ↦ k' * h) := rfl
      rw [this, ← Measure.map_map hι.measurable (measurable_const_mul k'),
        map_mul_left_eq_self μ k']
    · rw [Measure.map_map hr hι.measurable]
      have : (fun g : Rn N →L[ℝ] Rn N ↦ g * k) ∘ ι = ι ∘ (fun h : K ↦ h * k') := rfl
      rw [this, ← Measure.map_map hι.measurable (measurable_mul_const k'), hright k']
/-- Orbit law under the stabilizer `K = {g : g*g = 1, g = id on V^⊥}`, used when averaging over
`O(N)` for Simon Ch. 3, Thm. 3.6 (cf. Mattila, *Geometry of Sets and Measures in Euclidean
Spaces*, Ch. 3 "Invariant measures"). Let `θ` be a probability on `ℝᴺ →L[ℝ] ℝᴺ`
concentrated on `K` and invariant under `K`, and let `0 < Hⁿ(S(V)) < ∞`, `S(V) = V ∩ ∂B₁(0)`.
Then `θ{g : gζ ∈ Y} = 0` for `ζ ∈ S(V)` and every Borel `Y` with `Hⁿ(Y ∩ S(V)) = 0`.
Slice `T = {(g, x) : gx ∈ Y}` under `θ ⊗ Hⁿ⌞S(V)` both ways. Each `g ∈ K` is an isometry
mapping `S(V)` into itself, so every `g`-slice is `Hⁿ⌞S(V)`-null. The reflection in
`(ζ - x)^⊥` lies in `K` and maps `ζ` to `x ∈ S(V)`, so by right invariance every such `x`-slice
has `θ`-measure `θ{g : gζ ∈ Y}`. Hence `θ{g : gζ ∈ Y} · Hⁿ(S(V)) = 0`. -/
theorem Submission.bf_stabilizerOrbit_null : ∀ (N n : ℕ) (V : Submodule ℝ (Rn N)) (θ : Measure (Rn N →L[ℝ] Rn N)), IsProbabilityMeasure θ → (∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1 ∧ ∀ x ∈ Vᗮ, g x = x) → (∀ k : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint k * k = 1 → (∀ x ∈ Vᗮ, k x = x) → Measure.map (fun g ↦ k * g) θ = θ ∧ Measure.map (fun g ↦ g * k) θ = θ) → 0 < μHE[n] {x : Rn N | x ∈ V ∧ ‖x‖ = 1} → μHE[n] {x : Rn N | x ∈ V ∧ ‖x‖ = 1} < ∞ → ∀ ζ ∈ V, ‖ζ‖ = 1 → ∀ Y : Set (Rn N), MeasurableSet Y → μHE[n] (Y ∩ {x : Rn N | x ∈ V ∧ ‖x‖ = 1}) = 0 → θ {g | g ζ ∈ Y} = 0 := by
  intro N n V θ hθP hθK hθinv hpos hfin ζ hζV hζ1 Y hY hYnull
  set S : Set (Rn N) := {x : Rn N | x ∈ V ∧ ‖x‖ = 1}
  have hSm : MeasurableSet S :=
    (V.closed_of_finiteDimensional.inter
      (isClosed_eq continuous_norm continuous_const)).measurableSet
  -- `g*g = 1` makes `g` preserve inner products, hence norms.
  have hinner : ∀ g : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint g * g = 1 →
      ∀ x y : Rn N, inner ℝ (g x) (g y) = inner ℝ x y := by
    intro g hg x y
    rw [← ContinuousLinearMap.adjoint_inner_right, ← mul_apply_eq_comp, hg, one_apply_eq_self]
  have hnorm : ∀ g : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint g * g = 1 →
      ∀ x : Rn N, ‖g x‖ = ‖x‖ := by
    intro g hg x
    have h := hinner g hg x x
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
  -- Every `g ∈ K` maps `V = V^⊥⊥` into itself, hence `S` into `S`.
  have hmaps : ∀ g : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint g * g = 1 →
      (∀ x ∈ Vᗮ, g x = x) → ∀ x ∈ S, g x ∈ S := by
    rintro g hg hfix x ⟨hxV, hx1⟩
    refine ⟨?_, (hnorm g hg x).trans hx1⟩
    rw [← Submodule.orthogonal_orthogonal V]
    intro y hy
    calc inner ℝ y (g x) = inner ℝ (g y) (g x) := by rw [hfix y hy]
      _ = inner ℝ y x := hinner g hg y x
      _ = 0 := Submodule.inner_left_of_mem_orthogonal hxV hy
  -- `K` is transitive on `S`: the reflection in `(ζ - x)^⊥` lies in `K` and maps `ζ` to `x`.
  have htrans : ∀ x ∈ S, ∃ k : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint k * k = 1 ∧
      (∀ z ∈ Vᗮ, k z = z) ∧ k ζ = x := by
    rintro x ⟨hxV, hx1⟩
    let r := (ℝ ∙ (ζ - x))ᗮ.reflection
    let k : Rn N →L[ℝ] Rn N := r.toContinuousLinearEquiv.toContinuousLinearMap
    have hkr : ∀ z, k z = r z := fun z ↦ rfl
    refine ⟨k, ?_, fun z hz ↦ ?_, ?_⟩
    · ext1 z
      refine ext_inner_right ℝ fun w ↦ ?_
      rw [mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_left, one_apply_eq_self, hkr,
        hkr]
      exact r.inner_map_map z w
    · rw [hkr]
      refine Submodule.reflection_mem_subspace_eq_self ?_
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact Submodule.inner_right_of_mem_orthogonal (V.sub_mem hζV hxV) hz
    · rw [hkr]
      exact Submodule.reflection_sub (hζ1.trans hx1.symm)
  -- Right invariance: `θ{g : gx ∈ Y} = θ{g : gζ ∈ Y}` for `x ∈ S`.
  have hev : MeasurableSet {g : Rn N →L[ℝ] Rn N | g ζ ∈ Y} :=
    (continuous_id.clm_apply continuous_const).measurable hY
  have horbit : ∀ x ∈ S, θ {g | g x ∈ Y} = θ {g | g ζ ∈ Y} := by
    intro x hx
    obtain ⟨k, hk, hkfix, rfl⟩ := htrans x hx
    calc θ {g | g (k ζ) ∈ Y} = Measure.map (fun g ↦ g * k) θ {g | g ζ ∈ Y} := by
          rw [Measure.map_apply (measurable_mul_const k) hev]
          rfl
      _ = θ {g | g ζ ∈ Y} := by rw [(hθinv k hk hkfix).2]
  -- Slice `T = {(g, x) : gx ∈ Y}` under `θ ⊗ Hⁿ⌞S` in both orders.
  have : IsFiniteMeasure ((μHE[n] : Measure (Rn N)).restrict S) :=
    isFiniteMeasure_restrict.mpr hfin.ne
  have hT : MeasurableSet {p : (Rn N →L[ℝ] Rn N) × Rn N | p.1 p.2 ∈ Y} :=
    (continuous_fst.clm_apply continuous_snd).measurable hY
  have h1 : θ.prod ((μHE[n] : Measure (Rn N)).restrict S)
      {p : (Rn N →L[ℝ] Rn N) × Rn N | p.1 p.2 ∈ Y} = 0 := by
    rw [Measure.prod_apply hT]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hθK] with g hg
    rw [Measure.restrict_apply (measurable_prodMk_left hT)]
    refine measure_mono_null (t := ⇑g ⁻¹' (Y ∩ S))
      (fun x hx ↦ ⟨hx.1, hmaps g hg.1 hg.2 x hx.2⟩) ?_
    rw [(AddMonoidHomClass.isometry_of_norm g (hnorm g hg.1)).euclideanHausdorffMeasure_preimage]
    exact measure_mono_null Set.inter_subset_left hYnull
  have h2 : θ.prod ((μHE[n] : Measure (Rn N)).restrict S)
      {p : (Rn N →L[ℝ] Rn N) × Rn N | p.1 p.2 ∈ Y} = θ {g | g ζ ∈ Y} * μHE[n] S := by
    rw [Measure.prod_apply_symm hT]
    have hae : (fun x : Rn N ↦ θ ((fun g ↦ (g, x)) ⁻¹'
        {p : (Rn N →L[ℝ] Rn N) × Rn N | p.1 p.2 ∈ Y})) =ᵐ[(μHE[n] : Measure (Rn N)).restrict S]
        fun _ ↦ θ {g | g ζ ∈ Y} := by
      filter_upwards [ae_restrict_mem hSm] with x hx
      exact horbit x hx
    rw [lintegral_congr_ae hae, lintegral_const, Measure.restrict_apply_univ]
  exact (mul_eq_zero.mp (h2.symm.trans h1)).resolve_right hpos.ne'
/-- **Simon Ch. 3, Theorem 3.6 (p. 80)** (`chapter-03.txt` lines 530–536; the book defers the
proof to [Fed69]/[Ros84]), Step 6 of the frame-averaging argument: Fubini over left cosets.
Let `θ` be a finite and `θ'` a probability measure on `𝓛 = ℝᴺ →L[ℝ] ℝᴺ`, with `(r_k)_# θ = θ`
for `θ'`-a.e. `k`, where `r_k(g) = g k`. If `θ'{g : h g ∈ B} = 0` for `θ`-a.e. `h`, then
`θ(B) = 0`. The set `D = {(h, g) : h g ∈ B}` is measurable (multiplication on the
second-countable normed ring `𝓛` is continuous), and Tonelli in both orders gives
`0 = ∫ θ'{g : h g ∈ B} dθ(h) = (θ ⊗ θ')(D) = ∫ θ(r_g⁻¹ B) dθ'(g) = θ(B) θ'(𝓛) = θ(B)`. -/
theorem Submission.bf_haar_null_of_cosetFibres_null :
    ∀ (N : ℕ) (θ θ' : Measure (Rn N →L[ℝ] Rn N)), IsFiniteMeasure θ → IsProbabilityMeasure θ' →
      (∀ᵐ k ∂θ', Measure.map (fun g ↦ g * k) θ = θ) → ∀ B : Set (Rn N →L[ℝ] Rn N),
        MeasurableSet B → (∀ᵐ h ∂θ, θ' {g | h * g ∈ B} = 0) → θ B = 0 := by
  intro N θ θ' _ _ hinv B hB hfib
  -- Step 1: `D = {(h, g) | h * g ∈ B}` is measurable, as multiplication is continuous.
  set D : Set ((Rn N →L[ℝ] Rn N) × (Rn N →L[ℝ] Rn N)) := {p | p.1 * p.2 ∈ B}
  have hD : MeasurableSet D := measurable_mul hB
  -- Step 2: slicing in `g` first, `(θ ⊗ θ')(D) = ∫ θ'{g | h * g ∈ B} dθ(h) = 0`.
  have h0 : θ.prod θ' D = 0 := by
    rw [Measure.prod_apply hD]
    calc ∫⁻ h, θ' (Prod.mk h ⁻¹' D) ∂θ = ∫⁻ _, 0 ∂θ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hfib] with h hh
          exact hh
      _ = 0 := lintegral_zero
  -- Step 3: slicing in `h` first, `θ{h | h * k ∈ B} = (r_k)_# θ (B) = θ(B)` for `θ'`-a.e. `k`.
  have h1 : θ.prod θ' D = θ B := by
    rw [Measure.prod_apply_symm hD]
    calc ∫⁻ k, θ ((fun h ↦ (h, k)) ⁻¹' D) ∂θ' = ∫⁻ _, θ B ∂θ' := by
          refine lintegral_congr_ae ?_
          filter_upwards [hinv] with k hk
          calc θ ((fun h ↦ (h, k)) ⁻¹' D) = θ ((fun g ↦ g * k) ⁻¹' B) := rfl
            _ = Measure.map (fun g ↦ g * k) θ B :=
              (Measure.map_apply (measurable_mul_const k) hB).symm
            _ = θ B := by rw [hk]
      _ = θ B := by rw [lintegral_const, measure_univ, mul_one]
  -- Step 4: compare the two evaluations of `(θ ⊗ θ')(D)`.
  rw [← h1, h0]
/-- **Projection onto a rotated subspace** (fact (F1) of the frame-averaging step for Simon Ch. 3,
Theorem 3.6). Let `g : ℝᴺ → ℝᴺ` be linear with `g* g = 1` and `V ⊆ ℝᴺ` a subspace. Then the
orthogonal projection onto `gV` is `P_{gV} = g P_V g*`, and `dim gV = dim V`. Since `g* g = 1`,
`g` is injective and restricts to a linear isomorphism `V ≃ gV`. For `x ∈ ℝᴺ`, `g P_V g* x ∈ gV`,
and `(x - g P_V g* x) · g y = (g* x - P_V g* x) · y = 0` for `y ∈ V`; the characterization of the
orthogonal projection then gives `P_{gV} x = g P_V g* x`. -/
theorem Submission.bf_starProjection_map_orthogonal : ∀ (N : ℕ) (g : Rn N →L[ℝ] Rn N), ContinuousLinearMap.adjoint g * g = 1 → ∀ V : Submodule ℝ (Rn N), (V.map (g : Rn N →ₗ[ℝ] Rn N)).starProjection = g * V.starProjection * ContinuousLinearMap.adjoint g ∧ finrank ℝ (V.map (g : Rn N →ₗ[ℝ] Rn N)) = finrank ℝ V := by
  intro N g hg V
  -- Step 1: `g* (g x) = x`, so `g` is injective.
  have hgg : ∀ x, ContinuousLinearMap.adjoint g (g x) = x := by
    intro x
    rw [← mul_apply_eq_comp, hg, one_apply_eq_self]
  have hinj : Function.Injective g := Function.LeftInverse.injective hgg
  refine ⟨?_, ?_⟩
  -- Step 3: `v = g P_V g* x` lies in `gV` and `x - v ⊥ gV`, so `P_{gV} x = v`.
  · ext1 x
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · exact Submodule.mem_map_of_mem (V.starProjection_apply_mem _)
    · rintro _ ⟨y, hy, rfl⟩
      change inner ℝ (x - g (V.starProjection (ContinuousLinearMap.adjoint g x))) (g y) = 0
      rw [inner_sub_left, ← ContinuousLinearMap.adjoint_inner_left,
        ← ContinuousLinearMap.adjoint_inner_left, hgg, ← inner_sub_left]
      exact Submodule.starProjection_inner_eq_zero _ _ hy
  -- Step 2: `g` restricts to a linear isomorphism `V ≃ gV`, so `dim gV = dim V`.
  · exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj V)).symm
/-- Used for Simon Ch. 3, Theorem 3.6 (Besicovitch–Federer), Step 9(b) of the frame averaging
`bf_frameAveraging_null`: `O(N)` acts transitively on the linear subspaces of `ℝᴺ` of each
dimension. If `dim W₀ = dim W`, matching orthonormal bases give a linear isometric equivalence
`e : W₀ ≃ W`; the isometry `x ↦ e x` of `W₀` into `ℝᴺ` extends to a linear isometry `h` of `ℝᴺ`
(`LinearIsometry.extend`), so `h* h = 1`, and `h = e` on `W₀`, so `h(W₀) = e(W₀) = W`. -/
theorem Submission.bf_orthogonal_exists_map_eq : ∀ (N : ℕ) (W₀ W : Submodule ℝ (Rn N)), finrank ℝ W₀ = finrank ℝ W → ∃ h : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint h * h = 1 ∧ W₀.map (h : Rn N →ₗ[ℝ] Rn N) = W := by
  intro N W₀ W hdim
  -- Step 1: matching orthonormal bases of `W₀` and `W` give a linear isometric equivalence.
  let e : W₀ ≃ₗᵢ[ℝ] W := (stdOrthonormalBasis ℝ W₀).repr.trans
    ((stdOrthonormalBasis ℝ W).reindex (finCongr hdim.symm)).repr.symm
  -- Step 2: the isometry `x ↦ e x` of `W₀` into `ℝᴺ` extends to a linear isometry `h` of `ℝᴺ`.
  let L : W₀ →ₗᵢ[ℝ] Rn N := W.subtypeₗᵢ.comp e.toLinearIsometry
  let h : Rn N →L[ℝ] Rn N := L.extend.toContinuousLinearMap
  have hL : ∀ x : W₀, h x = (e x : Rn N) := fun x ↦ L.extend_apply x
  refine ⟨h, ?_, ?_⟩
  -- Step 3: `h` preserves inner products, hence `h* h = 1`.
  · ext1 x
    refine ext_inner_right ℝ fun y ↦ ?_
    rw [mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_left, one_apply_eq_self]
    exact L.extend.inner_map_map x y
  -- Step 4: `h` agrees with `e` on `W₀`, hence `h(W₀) = e(W₀) = W`.
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change h x ∈ W
      rw [hL ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).2
    · intro w hw
      refine ⟨(e.symm ⟨w, hw⟩ : Rn N), (e.symm ⟨w, hw⟩).2, ?_⟩
      change h (e.symm ⟨w, hw⟩ : Rn N) = w
      rw [hL (e.symm ⟨w, hw⟩), LinearIsometryEquiv.apply_symm_apply]

/-- **Null sets of rotated plane–direction pairs** (Steps 5–6 of the frame-averaging step for
Simon Ch. 3, Theorem 3.6). Let `Bad ⊆ ℝᴺ × 𝓛 × ℝᴺ` be measurable and `a ∈ ℝᴺ` with
`Hⁿ({x ∈ H : |x| = 1, (a, P_H, x) ∈ Bad}) = 0` for every `(n+1)`-plane `H`. Let `θ` be a
probability on `𝓛` carried by `{g : g* g = 1}` and invariant under `g ↦ g k` whenever `k* k = 1`,
`V` an `(n+1)`-plane with `0 < Hⁿ(S(V)) < ∞`, `S(V) = {x ∈ V : |x| = 1}`, and `ζ ∈ S(V)`. Then
`θ(B) = 0` for `B = {g : (a, g P_V g*, g ζ) ∈ Bad}`. Let `θ'` be a bi-invariant probability on the
stabilizer `K` of `Vᗮ`. By Fubini over the cosets `h K` it suffices that `θ'{g' : h g' ∈ B} = 0`
for every `h` with `h* h = 1`. For such `h`, `H = hV` is an `(n+1)`-plane with `P_H = h P_V h*`, and
`h` is an isometry, so `Y = {y : (a, P_H, h y) ∈ Bad}` has `Hⁿ(Y ∩ S(V)) = 0`; the orbit law of
`θ'` gives `θ'{g' : g' ζ ∈ Y} = 0`. Every `g' ∈ K` maps `V` onto `V`, so `(h g') P_V (h g')* = P_H`
and `h g' ∈ B` iff `g' ζ ∈ Y`. -/
theorem Submission.bf_haar_planeDirection_null : ∀ (n N : ℕ) (Bad : Set (Rn N × (Rn N →L[ℝ] Rn N) × Rn N)), MeasurableSet Bad → ∀ a : Rn N, (∀ H : Submodule ℝ (Rn N), finrank ℝ H = n + 1 → μHE[n] {x | x ∈ H ∧ ‖x‖ = 1 ∧ (a, H.starProjection, x) ∈ Bad} = 0) → ∀ θ : Measure (Rn N →L[ℝ] Rn N), IsProbabilityMeasure θ → (∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1) → (∀ k : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint k * k = 1 → Measure.map (fun g ↦ g * k) θ = θ) → ∀ V : Submodule ℝ (Rn N), finrank ℝ V = n + 1 → 0 < μHE[n] {x : Rn N | x ∈ V ∧ ‖x‖ = 1} → μHE[n] {x : Rn N | x ∈ V ∧ ‖x‖ = 1} < ∞ → ∀ ζ ∈ V, ‖ζ‖ = 1 → θ {g | (a, g * V.starProjection * ContinuousLinearMap.adjoint g, g ζ) ∈ Bad} = 0 := by
  intro n N Bad hBad a hnull θ _ hθO hθR V hV hS0 hSfin ζ hζV hζ1
  -- Step 1: a probability `θ'` carried by the stabilizer `K = {g' : g'* g' = 1, g' = 1 on Vᗮ}`,
  -- invariant under left and right translation by elements of `K`.
  obtain ⟨θ', hθ'P, hθ'K, hθ'inv⟩ := Submission.bf_orthStabilizer_haar_exists N Vᗮ
  -- Maps with `g* g = 1` preserve inner products.
  have hinner : ∀ g : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint g * g = 1 →
      ∀ x y : Rn N, inner ℝ (g x) (g y) = inner ℝ x y :=
    fun g hg ↦ g.inner_map_map_iff_adjoint_comp_self.mpr hg
  -- Step 2: `B` is Borel, as `g ↦ (a, g P_V g*, g ζ)` is continuous (the adjoint is an isometry).
  set B : Set (Rn N →L[ℝ] Rn N) :=
    {g | (a, g * V.starProjection * ContinuousLinearMap.adjoint g, g ζ) ∈ Bad}
  have hBm : MeasurableSet B := by
    have hadj : Continuous fun g : Rn N →L[ℝ] Rn N ↦ ContinuousLinearMap.adjoint g :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn N) (F := Rn N)).continuous
    have hm : Measurable fun g : Rn N →L[ℝ] Rn N ↦
        (a, g * V.starProjection * ContinuousLinearMap.adjoint g, g ζ) :=
      measurable_const.prodMk ((((continuous_id.mul continuous_const).mul hadj).measurable).prodMk
        (ContinuousLinearMap.measurable_apply ζ))
    exact hm hBad
  -- Step 3: Fubini over the cosets `h K`. As `θ'`-a.e. `k` has `k* k = 1`, `θ` is invariant under
  -- `g ↦ g k` for `θ'`-a.e. `k`; it remains to show `θ'{g' | h g' ∈ B} = 0` whenever `h* h = 1`.
  refine Submission.bf_haar_null_of_cosetFibres_null N θ θ' inferInstance hθ'P ?_ B hBm ?_
  · filter_upwards [hθ'K] with k hk
    exact hθR k hk.1
  filter_upwards [hθO] with h hh
  -- Step 4: `H = hV` is an `(n+1)`-plane with `P_H = h P_V h*`, and `h` is an isometry.
  obtain ⟨hPH, hHdim⟩ := Submission.bf_starProjection_map_orthogonal N h hh V
  have hiso : Isometry h := h.isometry_iff_adjoint_comp_self.mpr hh
  -- Step 5: `Y = {y | (a, P_H, h y) ∈ Bad}` is Borel, and `h` maps `Y ∩ S(V)` into the `Hⁿ`-null
  -- set `{x ∈ H | ‖x‖ = 1, (a, P_H, x) ∈ Bad}`; as `h` is an isometry, `Hⁿ(Y ∩ S(V)) = 0`.
  set Y : Set (Rn N) :=
    {y | (a, (V.map (h : Rn N →ₗ[ℝ] Rn N)).starProjection, h y) ∈ Bad}
  have hYm : MeasurableSet Y := by
    have hm : Measurable fun y : Rn N ↦
        (a, (V.map (h : Rn N →ₗ[ℝ] Rn N)).starProjection, h y) :=
      measurable_const.prodMk (measurable_const.prodMk h.continuous.measurable)
    exact hm hBad
  have hYnull : μHE[n] (Y ∩ {x : Rn N | x ∈ V ∧ ‖x‖ = 1}) = 0 := by
    rw [← hiso.euclideanHausdorffMeasure_image]
    refine measure_mono_null ?_ (hnull (V.map (h : Rn N →ₗ[ℝ] Rn N)) (hHdim.trans hV))
    rintro _ ⟨y, ⟨hyY, hyV, hy1⟩, rfl⟩
    exact ⟨Submodule.mem_map_of_mem hyV, (hiso.norm_map_of_map_zero (map_zero h) y).trans hy1,
      hyY⟩
  -- Step 6: the orbit law of `θ'` gives `θ'{g' | g' ζ ∈ Y} = 0`.
  have hYθ' : θ' {g' | g' ζ ∈ Y} = 0 :=
    Submission.bf_stabilizerOrbit_null N n V θ' hθ'P hθ'K hθ'inv hS0 hSfin ζ hζV hζ1 Y hYm hYnull
  -- Step 7: for `θ'`-a.e. `g'`, `g' ∈ K` and `g' ζ ∉ Y`; and `g' ∈ K`, `h g' ∈ B` give `g' ζ ∈ Y`.
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hθ'K, measure_eq_zero_iff_ae_notMem.mp hYθ'] with g' hK hg'Y hg'B
  -- (a) `g'V ⊆ V`: for `x ∈ V` and `y ∈ Vᗮ`, `y · g'x = g'y · g'x = y · x = 0`. Since
  -- `dim g'V = dim V`, `g'V = V`, so `g' P_V g'* = P_{g'V} = P_V`.
  obtain ⟨hPg', hdg'⟩ := Submission.bf_starProjection_map_orthogonal N g' hK.1 V
  have hle : V.map (g' : Rn N →ₗ[ℝ] Rn N) ≤ V := by
    rintro _ ⟨x, hxV, rfl⟩
    rw [← Submodule.orthogonal_orthogonal V, Submodule.mem_orthogonal]
    intro y hy
    change inner ℝ y (g' x) = 0
    rw [← hK.2 y hy, hinner g' hK.1]
    exact Submodule.inner_left_of_mem_orthogonal hxV hy
  have hstar : ∀ W₁ W₂ : Submodule ℝ (Rn N), W₁ = W₂ →
      W₁.starProjection = W₂.starProjection := by
    rintro W₁ W₂ rfl
    rfl
  have hPV : g' * V.starProjection * ContinuousLinearMap.adjoint g' = V.starProjection :=
    hPg'.symm.trans (hstar _ _ (Submodule.eq_of_le_of_finrank_eq hle hdg'))
  -- (b) `(h g')* = g'* h*`, so `(h g') P_V (h g')* = h (g' P_V g'*) h* = h P_V h* = P_H`.
  have hcoset : h * g' * V.starProjection * ContinuousLinearMap.adjoint (h * g') =
      (V.map (h : Rn N →ₗ[ℝ] Rn N)).starProjection := by
    calc h * g' * V.starProjection * ContinuousLinearMap.adjoint (h * g')
        = h * (g' * V.starProjection * ContinuousLinearMap.adjoint g') *
            ContinuousLinearMap.adjoint h := by
          rw [show ContinuousLinearMap.adjoint (h * g') =
            ContinuousLinearMap.adjoint g' * ContinuousLinearMap.adjoint h from
              ContinuousLinearMap.adjoint_comp h g']
          simp only [mul_assoc]
      _ = (V.map (h : Rn N →ₗ[ℝ] Rn N)).starProjection := by rw [hPV, hPH]
  -- (c) Hence `h g' ∈ B` says `(a, P_H, h (g' ζ)) ∈ Bad`, i.e. `g' ζ ∈ Y`.
  have hg'B' : (a, h * g' * V.starProjection * ContinuousLinearMap.adjoint (h * g'),
      (h * g') ζ) ∈ Bad := hg'B
  rw [hcoset] at hg'B'
  exact hg'Y hg'B'

/-- **For each point `a`, Haar-a.e. rotation of an `n`-plane is not exceptional** (Steps 2–6 of
the frame-averaging step for Simon Ch. 3, Theorem 3.6). Let `f₁, …, f_ℓ` be an orthonormal basis
of `W₀ᗮ`. Each `V_j = W₀ ⊔ span{f_j}` is `(n+1)`-dimensional and contains the unit vector `f_j`,
so `B_j = {g : (a, g P_{V_j} g*, g f_j) ∈ Bad}` is `θ`-null by `bf_haar_planeDirection_null`. If
`g* g = 1` and `(a, g P_{W₀} g*) ∈ Exc`, then `W = gW₀` is `n`-dimensional with
`P_W = g P_{W₀} g*`, and the `g f_j` are orthonormal in `Wᗮ`; so (h2_a) and
`W ⊔ span{g f_j} = g V_j` put `g` in some `B_j`. Hence the exceptional set lies in the `θ`-null
set `{g* g ≠ 1} ∪ ⋃_j B_j`. -/
theorem Submission.bf_haar_excPointwise_null : ∀ (n ℓ : ℕ) (Exc : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)))) (Bad : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)) × Rn (n + ℓ))), MeasurableSet Bad → (∀ H : Submodule ℝ (Rn (n + ℓ)), finrank ℝ H = n + 1 → 0 < μHE[n] {x : Rn (n + ℓ) | x ∈ H ∧ ‖x‖ = 1} ∧ μHE[n] {x : Rn (n + ℓ) | x ∈ H ∧ ‖x‖ = 1} < ∞) → ∀ a : Rn (n + ℓ), (∀ H : Submodule ℝ (Rn (n + ℓ)), finrank ℝ H = n + 1 → μHE[n] {x | x ∈ H ∧ ‖x‖ = 1 ∧ (a, H.starProjection, x) ∈ Bad} = 0) → (∀ W : Submodule ℝ (Rn (n + ℓ)), finrank ℝ W = n → (a, W.starProjection) ∈ Exc → ∀ u : Fin ℓ → Rn (n + ℓ), Orthonormal ℝ u → (∀ j, u j ∈ Wᗮ) → ∃ j, (a, (W ⊔ Submodule.span ℝ {u j}).starProjection, u j) ∈ Bad) → ∀ θ : Measure (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)), IsProbabilityMeasure θ → (∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1) → (∀ k : Rn (n + ℓ) →L[ℝ] Rn (n + ℓ), ContinuousLinearMap.adjoint k * k = 1 → Measure.map (fun g ↦ g * k) θ = θ) → ∀ W₀ : Submodule ℝ (Rn (n + ℓ)), finrank ℝ W₀ = n → θ {g | (a, g * W₀.starProjection * ContinuousLinearMap.adjoint g) ∈ Exc} = 0 := by
  intro n ℓ Exc Bad hBad hS a h1 h2 θ hθP hθG hθR W₀ hW₀
  -- Step 1: an orthonormal basis `f` of `W₀ᗮ`, indexed by `Fin ℓ`.
  have hdim : finrank ℝ W₀ᗮ = ℓ := by
    have := W₀.finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace_fin, hW₀] at this
    omega
  let b := (stdOrthonormalBasis ℝ W₀ᗮ).reindex (finCongr hdim)
  let f : Fin ℓ → Rn (n + ℓ) := fun j ↦ (b j : Rn (n + ℓ))
  have hf : Orthonormal ℝ f := b.orthonormal.comp_linearIsometry W₀ᗮ.subtypeₗᵢ
  have hfW : ∀ j, f j ∈ W₀ᗮ := fun j ↦ (b j).2
  -- Step 2: the planes `V_j = W₀ ⊔ span{f_j}` are `(n+1)`-dimensional.
  let V : Fin ℓ → Submodule ℝ (Rn (n + ℓ)) := fun j ↦ W₀ ⊔ Submodule.span ℝ {f j}
  have hVdim : ∀ j, finrank ℝ (V j) = n + 1 := by
    intro j
    have hinf : W₀ ⊓ Submodule.span ℝ {f j} = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxW, hxs⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxs
      have h0 : inner ℝ (f j) (c • f j) = 0 := Submodule.inner_left_of_mem_orthogonal hxW (hfW j)
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hf.1 j, one_pow, mul_one] at h0
      rw [h0, zero_smul]
      exact Submodule.zero_mem _
    have := Submodule.finrank_sup_add_finrank_inf_eq W₀ (Submodule.span ℝ {f j})
    rw [hinf, finrank_bot, finrank_span_singleton (hf.ne_zero j), hW₀] at this
    exact this
  -- Step 3: each `B_j = {g : (a, g P_{V_j} g*, g f_j) ∈ Bad}` is `θ`-null.
  have hnull : ∀ j, θ {g | (a, g * (V j).starProjection * ContinuousLinearMap.adjoint g,
      g (f j)) ∈ Bad} = 0 := fun j ↦
    Submission.bf_haar_planeDirection_null n (n + ℓ) Bad hBad a h1 θ hθP hθG hθR (V j) (hVdim j)
      (hS _ (hVdim j)).1 (hS _ (hVdim j)).2 (f j)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)) (hf.1 j)
  -- Step 5: the exceptional set lies in `{g* g ≠ 1} ∪ ⋃_j B_j`, a `θ`-null set.
  refine measure_mono_null (t := {g | ¬ContinuousLinearMap.adjoint g * g = 1} ∪
    ⋃ j, {g | (a, g * (V j).starProjection * ContinuousLinearMap.adjoint g, g (f j)) ∈ Bad})
    ?_ (measure_union_null hθG (measure_iUnion_null hnull))
  intro g hg
  by_cases hgG : ContinuousLinearMap.adjoint g * g = 1
  swap
  · exact Or.inl hgG
  -- Step 4: for orthogonal `g`, the bad plane `W = gW₀` gives a bad direction `g f_j`.
  right
  have hinner : ∀ x y, inner ℝ (g x) (g y) = inner ℝ x y := by
    intro x y
    rw [← ContinuousLinearMap.adjoint_inner_right, ← mul_apply_eq_comp, hgG, one_apply_eq_self]
  obtain ⟨hP₀, hd₀⟩ := Submission.bf_starProjection_map_orthogonal (n + ℓ) g hgG W₀
  set W := W₀.map (g : Rn (n + ℓ) →ₗ[ℝ] Rn (n + ℓ))
  have hWexc : (a, W.starProjection) ∈ Exc := by
    rw [hP₀]
    exact hg
  have hu : Orthonormal ℝ (fun j ↦ g (f j)) := by
    rw [orthonormal_iff_ite] at hf ⊢
    intro i j
    rw [hinner]
    exact hf i j
  have huW : ∀ j, g (f j) ∈ Wᗮ := by
    intro j
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨w, hw, rfl⟩
    exact (hinner w (f j)).trans (Submodule.inner_right_of_mem_orthogonal hw (hfW j))
  obtain ⟨j, hj⟩ := h2 W (hd₀.trans hW₀) hWexc (fun j ↦ g (f j)) hu huW
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  -- `W ⊔ span{g f_j} = g V_j`; rewrite the projection through this equality of subspaces.
  have hsup : W ⊔ Submodule.span ℝ {g (f j)} = (V j).map (g : Rn (n + ℓ) →ₗ[ℝ] Rn (n + ℓ)) := by
    rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton]
    rfl
  have key : ∀ W₁ W₂ : Submodule ℝ (Rn (n + ℓ)), W₁ = W₂ →
      W₁.starProjection = W₂.starProjection := by
    rintro _ _ rfl
    rfl
  rw [key _ _ hsup, (Submission.bf_starProjection_map_orthogonal (n + ℓ) g hgG (V j)).1] at hj
  exact hj
/-- **From Haar-random rotated planes to Lebesgue-a.e. frames** (Steps 8–10 of the frame-averaging
step for Simon Ch. 3, Theorem 3.6). Let `θ` be a probability measure on `𝓛 = ℝᴺ →L[ℝ] ℝᴺ` with
`g* g = 1` for `θ`-a.e. `g`, invariant under `g ↦ g k` for every `k` with `k* k = 1`, let
`dim W₀ = n` and let `Q ⊆ 𝓛` be Borel with `θ{g | g P_{W₀} g* ∈ Q} = 0`. If the frame projection
is continuous on the linearly independent frames, then for Lebesgue-a.e. frame `v ∈ (ℝᴺ)ⁿ`, if
`v` is linearly independent then `P_{span v} ∉ Q`. The set `𝒮` of bad frames is Borel. For every
frame `v`, `θ{g | g·v ∈ 𝒮} = 0`: if `v` is dependent then so is `g·v` for injective `g`; otherwise
`span v = h W₀` with `h* h = 1`, so `P_{span(g·v)} = (gh) P_{W₀} (gh)*` and right invariance
reduces to `θ{g | g P_{W₀} g* ∈ Q} = 0`. As `v ↦ g·v` preserves Lebesgue measure for `g* g = 1`,
Tonelli on `θ ⊗ λ` gives `λ(𝒮) = ∫ λ{v | g·v ∈ 𝒮} dθ = ∫ θ{g | g·v ∈ 𝒮} dλ = 0`. -/
theorem Submission.bf_haar_null_to_frames : ∀ (N n : ℕ), ContinuousOn (fun v : Fin n → Rn N ↦ frameProjection v) {v | LinearIndependent ℝ v} → ∀ θ : Measure (Rn N →L[ℝ] Rn N), IsProbabilityMeasure θ → (∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1) → (∀ k : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint k * k = 1 → Measure.map (fun g ↦ g * k) θ = θ) → ∀ W₀ : Submodule ℝ (Rn N), finrank ℝ W₀ = n → ∀ Q : Set (Rn N →L[ℝ] Rn N), MeasurableSet Q → θ {g | g * W₀.starProjection * ContinuousLinearMap.adjoint g ∈ Q} = 0 → ForAlmostAllProjections N n (fun p ↦ p ∉ Q) := by
  intro N n hcont θ hθ hθO hθR W₀ hW₀ Q hQ hnull
  classical
  -- Step 1: `𝒮 = {v ∈ 𝒱 | P_{span v} ∈ Q}` is Borel, as `frameProjection` is continuous on the
  -- open set `𝒱` of linearly independent frames.
  set 𝒱 : Set (Fin n → Rn N) := {v | LinearIndependent ℝ v} with h𝒱
  have h𝒱o : IsOpen 𝒱 := isOpen_setOfPred_linearIndependent
  set S : Set (Fin n → Rn N) := {v | LinearIndependent ℝ v ∧ frameProjection v ∈ Q} with hS
  have hSm : MeasurableSet S := by
    have hF : Measurable (𝒱.piecewise (fun v ↦ frameProjection v)
        (fun _ ↦ (0 : Rn N →L[ℝ] Rn N))) :=
      ContinuousOn.measurable_piecewise hcont continuousOn_const h𝒱o.measurableSet
    have hSF : S = 𝒱 ∩ (𝒱.piecewise (fun v ↦ frameProjection v)
        (fun _ ↦ (0 : Rn N →L[ℝ] Rn N))) ⁻¹' Q := by
      ext v
      simp only [hS, h𝒱, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨hv, hq⟩
        exact ⟨hv, by rwa [Set.piecewise_eq_of_mem _ _ _ hv]⟩
      · rintro ⟨hv, hq⟩
        exact ⟨hv, by rwa [Set.piecewise_eq_of_mem _ _ _ hv] at hq⟩
    rw [hSF]
    exact h𝒱o.measurableSet.inter (hF hQ)
  -- Step 2: `M = {(g, v) | g·v ∈ 𝒮}` is measurable, as `(g, v) ↦ g·v` is continuous.
  set M : Set ((Rn N →L[ℝ] Rn N) × (Fin n → Rn N)) := {p | (fun i ↦ p.1 (p.2 i)) ∈ S} with hM
  have hMm : MeasurableSet M := by
    have hc : Continuous (fun p : (Rn N →L[ℝ] Rn N) × (Fin n → Rn N) ↦ fun i ↦ p.1 (p.2 i)) :=
      continuous_pi fun i ↦ continuous_fst.clm_apply ((continuous_apply i).comp continuous_snd)
    exact hc.measurable hSm
  have hA : MeasurableSet {g : Rn N →L[ℝ] Rn N |
      g * W₀.starProjection * ContinuousLinearMap.adjoint g ∈ Q} :=
    ((continuous_id.mul continuous_const).mul
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn N) (F := Rn N)).continuous).measurable hQ
  -- Step 3: `θ{g | g·v ∈ 𝒮} = 0` for every frame `v`.
  have hfib : ∀ v : Fin n → Rn N, θ {g : Rn N →L[ℝ] Rn N | (fun i ↦ g (v i)) ∈ S} = 0 := by
    intro v
    by_cases hv : LinearIndependent ℝ v
    · -- `span v = h W₀` for some `h` with `h* h = 1`.
      have hspan : finrank ℝ (Submodule.span ℝ (Set.range v)) = n := by
        rw [finrank_span_eq_card hv, Fintype.card_fin]
      obtain ⟨h, hh, hmap⟩ := Submission.bf_orthogonal_exists_map_eq N W₀
        (Submodule.span ℝ (Set.range v)) (hW₀.trans hspan.symm)
      have hsub : {g : Rn N →L[ℝ] Rn N | (fun i ↦ g (v i)) ∈ S} ⊆
          {g | ¬ContinuousLinearMap.adjoint g * g = 1} ∪ (fun g ↦ g * h) ⁻¹'
            {g | g * W₀.starProjection * ContinuousLinearMap.adjoint g ∈ Q} := by
        intro g hg
        by_cases hg1 : ContinuousLinearMap.adjoint g * g = 1
        · right
          -- `(gh)* (gh) = h* (g* g) h = 1` and `span(g·v) = g h W₀`, so
          -- `P_{span(g·v)} = (gh) P_{W₀} (gh)*`.
          have hgh : ContinuousLinearMap.adjoint (g * h) * (g * h) = 1 := by
            rw [show ContinuousLinearMap.adjoint (g * h) =
                ContinuousLinearMap.adjoint h * ContinuousLinearMap.adjoint g from
              ContinuousLinearMap.adjoint_comp g h]
            calc ContinuousLinearMap.adjoint h * ContinuousLinearMap.adjoint g * (g * h)
                = ContinuousLinearMap.adjoint h * (ContinuousLinearMap.adjoint g * g) * h := by
                  simp only [mul_assoc]
              _ = 1 := by rw [hg1, mul_one, hh]
          have hspan' : Submodule.span ℝ (Set.range fun i ↦ g (v i)) =
              W₀.map ((g * h : Rn N →L[ℝ] Rn N) : Rn N →ₗ[ℝ] Rn N) := by
            have hr : Set.range (fun i ↦ g (v i)) = (g : Rn N →ₗ[ℝ] Rn N) '' Set.range v := by
              rw [← Set.range_comp]
              rfl
            rw [hr, Submodule.span_image, ← hmap, ← Submodule.map_comp]
            rfl
          have hPeq : ∀ W₁ W₂ : Submodule ℝ (Rn N), W₁ = W₂ →
              W₁.starProjection = W₂.starProjection := by
            rintro W₁ W₂ rfl
            rfl
          have hP : frameProjection (fun i ↦ g (v i)) =
              g * h * W₀.starProjection * ContinuousLinearMap.adjoint (g * h) := by
            unfold frameProjection
            rw [hPeq _ _ hspan']
            exact (Submission.bf_starProjection_map_orthogonal N (g * h) hgh W₀).1
          change g * h * W₀.starProjection * ContinuousLinearMap.adjoint (g * h) ∈ Q
          rw [← hP]
          exact hg.2
        · left
          exact hg1
      -- By right invariance under `h`, `θ{g | g h ∈ A} = θ(A) = 0`.
      refine measure_mono_null hsub (measure_union_null hθO ?_)
      rw [← Measure.map_apply (measurable_mul_const h) hA, hθR h hh]
      exact hnull
    · -- If `v` is dependent, so is `g·v` for every injective `g`.
      refine measure_mono_null ?_ hθO
      intro g hg hg1
      exact hv (LinearIndependent.of_comp (g : Rn N →ₗ[ℝ] Rn N) hg.1)
  -- Step 5 (Tonelli): `∫ λ{v | g·v ∈ 𝒮} dθ = (θ ⊗ λ)(M) = ∫ θ{g | g·v ∈ 𝒮} dλ = 0`, so
  -- `λ{v | g·v ∈ 𝒮} = 0` for some `g` with `g* g = 1`.
  have hprod : (θ.prod volume) M = 0 := by
    rw [Measure.prod_apply_symm hMm]
    have h0 : (fun v : Fin n → Rn N ↦ θ ((fun g ↦ (g, v)) ⁻¹' M)) = fun _ ↦ 0 := by
      funext v
      exact hfib v
    rw [h0, lintegral_zero]
  rw [Measure.prod_apply hMm] at hprod
  have hmeas : Measurable (fun g : Rn N →L[ℝ] Rn N ↦ (volume : Measure (Fin n → Rn N))
      (Prod.mk g ⁻¹' M)) := measurable_measure_prodMk_left hMm
  have hae := (lintegral_eq_zero_iff hmeas).mp hprod
  have : (ae θ).NeBot := ae_neBot.mpr (IsProbabilityMeasure.ne_zero θ)
  obtain ⟨g, hg1, hg0⟩ := (hθO.and hae).exists
  -- Step 4: `g` is a linear isometry of `ℝᴺ` onto itself, so `v ↦ g·v` preserves `λ`.
  have hgg : ∀ x, ContinuousLinearMap.adjoint g (g x) = x := by
    intro x
    rw [← mul_apply_eq_comp, hg1, one_apply_eq_self]
  have hnorm : ∀ x, ‖g x‖ = ‖x‖ := by
    intro x
    have h2 : inner ℝ (g x) (g x) = inner ℝ x x := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hgg]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h2
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
  let gi : Rn N →ₗᵢ[ℝ] Rn N := { toLinearMap := (g : Rn N →ₗ[ℝ] Rn N), norm_map' := hnorm }
  have hsurj : Function.Surjective gi :=
    LinearMap.surjective_of_injective (f := (g : Rn N →ₗ[ℝ] Rn N)) gi.injective
  have hmp : MeasurePreserving (fun v : Fin n → Rn N ↦ fun i ↦ g (v i)) volume volume :=
    measurePreserving_pi (fun _ ↦ volume) (fun _ ↦ volume)
      (fun _ ↦ (LinearIsometryEquiv.ofSurjective gi hsurj).measurePreserving)
  have hS0 : (volume : Measure (Fin n → Rn N)) S = 0 := by
    rw [← hmp.measure_preimage hSm.nullMeasurableSet]
    exact hg0
  -- Step 6: `λ(𝒮) = 0` is the claim.
  rw [ForAlmostAllProjections, ae_iff]
  refine measure_mono_null ?_ hS0
  intro v hv
  simp only [Set.mem_ofPred_eq, not_imp, not_not] at hv
  exact hv
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
/-- **Continuity of the frame projection on independent frames** (Step 1.5(b) of the supplied
proof of the Besicovitch–Federer theorem, Simon Ch. 3, Theorem 3.6). On the linearly independent
frames `v = (v₁, …, vₙ)` in `ℝᴺ`, the orthogonal projection onto `span v` depends continuously on
`v`: with the synthesis operator `M_v c = ∑ᵢ cᵢ vᵢ` and the Gram operator `Γ_v = M_v* M_v`
(invertible for independent `v`), `frameProjection v = M_v Γ_v⁻¹ M_v*`, and ring inversion is
continuous at units. -/
theorem Submission.bf_frameProjection_continuousOn : ∀ (N n : ℕ), ContinuousOn (fun v : Fin n → Rn N ↦ frameProjection v) {v | LinearIndependent ℝ v} := by
  intro N n
  -- The synthesis operator `M v : ℝⁿ → ℝᴺ`, `c ↦ ∑ᵢ cᵢ vᵢ`, depends continuously on `v`.
  let M : (Fin n → Rn N) → (EuclideanSpace ℝ (Fin n) →L[ℝ] Rn N) := fun v ↦
    ∑ i, (EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ (Fin n))).smulRight (v i)
  have hM_apply : ∀ v c, M v c = ∑ i, c i • v i := by
    intro v c
    simp [M]
  have hM : Continuous M := by
    refine continuous_finsetSum _ fun i _ ↦ ?_
    exact (ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin n)) (Rn N)
      (EuclideanSpace.proj i)).continuous.comp (continuous_apply i)
  -- The adjoint `M v*` and the Gram operator `Γ v = M v* ∘ M v` depend continuously on `v`.
  have hMadj : Continuous fun v ↦ ContinuousLinearMap.adjoint (M v) :=
    ContinuousLinearMap.adjoint.continuous.comp hM
  let Γ : (Fin n → Rn N) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    fun v ↦ (ContinuousLinearMap.adjoint (M v)).comp (M v)
  have hΓ : Continuous Γ := hMadj.clm_comp hM
  -- For an independent frame, `Γ v` is injective, hence a unit.
  have hunit : ∀ v : Fin n → Rn N, LinearIndependent ℝ v → IsUnit (Γ v) := by
    intro v hv
    have hinj : Function.Injective (Γ v) := by
      rw [injective_iff_map_eq_zero]
      intro c hc
      have h1 : inner ℝ (M v c) (M v c) = 0 := by
        rw [← ContinuousLinearMap.adjoint_inner_left]
        exact (congrArg (fun y ↦ inner ℝ y c) hc).trans (inner_zero_left _)
      have h2 : ∑ i, c i • v i = 0 := by
        rw [← hM_apply]
        exact inner_self_eq_zero.1 h1
      have h3 := Fintype.linearIndependent_iff.1 hv (fun i ↦ c i) h2
      ext i
      simpa using h3 i
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  -- For an independent frame, `M v ∘ Γ v⁻¹ ∘ M v*` is the orthogonal projection onto `span v`.
  have hR : ∀ v : Fin n → Rn N, LinearIndependent ℝ v →
      (M v).comp ((Ring.inverse (Γ v)).comp (ContinuousLinearMap.adjoint (M v))) =
        frameProjection v := by
    intro v hv
    have hΓinv : ∀ y, Γ v (Ring.inverse (Γ v) y) = y := by
      intro y
      have := Ring.mul_inverse_cancel (Γ v) (hunit v hv)
      exact congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) ↦ T y) this
    ext1 x
    symm
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨_, (hM_apply _ _).symm⟩
    · intro w hw
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw
      have hc : ∑ i, c i • v i = M v (WithLp.toLp 2 c) := (hM_apply _ _).symm
      rw [hc, ← ContinuousLinearMap.adjoint_inner_left, map_sub]
      have : ContinuousLinearMap.adjoint (M v)
          (((M v).comp ((Ring.inverse (Γ v)).comp (ContinuousLinearMap.adjoint (M v)))) x) =
          ContinuousLinearMap.adjoint (M v) x :=
        hΓinv _
      rw [this, sub_self, inner_zero_left]
  -- Conclusion: ring inversion is continuous at the unit `Γ v₀`.
  intro v₀ hv₀
  have hinv : ContinuousAt (fun v ↦ Ring.inverse (Γ v)) v₀ := by
    obtain ⟨u, hu⟩ := hunit v₀ hv₀
    have h := NormedRing.inverse_continuousAt u
    rw [hu] at h
    exact h.comp hΓ.continuousAt
  have hcont : ContinuousAt (fun v ↦
      (M v).comp ((Ring.inverse (Γ v)).comp (ContinuousLinearMap.adjoint (M v)))) v₀ :=
    hM.continuousAt.clm_comp (hinv.clm_comp hMadj.continuousAt)
  exact hcont.continuousWithinAt.congr (fun v hv ↦ (hR v hv).symm) (hR v₀ hv₀).symm

/-- **Averaging over `O(N)` and transfer to Lebesgue-a.e. frames** (Steps 0.2, 4 and 5 of the
supplied proof of the Besicovitch–Federer theorem, Simon Ch. 3, Theorem 3.6; Dall'Alba,
Lemma 5.6). Let `θ_N` be the bi-invariant Haar probability on `O(N) = {g : g* g = 1}` and `P₀`
the projection onto an `n`-plane `W₀`. For every `a`, (h1), (h2) and `0 < Hⁿ(S(H)) < ∞` for the
unit spheres `S(H)` of the `(n+1)`-planes `H` give `θ_N{g : (a, g P₀ g*) ∈ Exc} = 0`. Tonelli
over `μ ⊗ θ_N` then gives `μ(Exc^{g P₀ g*}) = 0` for `θ_N`-a.e. `g`, and this transfers from
`θ_N` to Lebesgue-a.e. frames. -/
theorem Submission.bf_frameAveraging_null : ∀ (n ℓ : ℕ), 0 < n → 0 < ℓ → ∀ μ : Measure (Rn (n + ℓ)), IsFiniteMeasure μ → ∀ (Exc : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)))) (Bad : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)) × Rn (n + ℓ))), MeasurableSet Exc → MeasurableSet Bad → (∀ (a : Rn (n + ℓ)) (H : Submodule ℝ (Rn (n + ℓ))), finrank ℝ H = n + 1 → μHE[n] {θ | θ ∈ H ∧ ‖θ‖ = 1 ∧ (a, H.starProjection, θ) ∈ Bad} = 0) → (∀ (a : Rn (n + ℓ)) (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → (a, W.starProjection) ∈ Exc → ∀ u : Fin ℓ → Rn (n + ℓ), Orthonormal ℝ u → (∀ j, u j ∈ Wᗮ) → ∃ j, (a, (W ⊔ Submodule.span ℝ {u j}).starProjection, u j) ∈ Bad) → ForAlmostAllProjections (n + ℓ) n (fun p ↦ μ {a | (a, p) ∈ Exc} = 0) := by
  intro n ℓ hn _hℓ μ _hμ Exc Bad hExc hBad h1 h2
  -- Step 4: `0 < Hⁿ(S(H)) < ∞` for every `(n+1)`-plane `H`, from the cap bounds around a unit
  -- vector `ζ ∈ H` at radius `2`, and at radius `3` since `S(H) ⊆ B(ζ, 3)`.
  have hS : ∀ H : Submodule ℝ (Rn (n + ℓ)), finrank ℝ H = n + 1 →
      0 < μHE[n] {x : Rn (n + ℓ) | x ∈ H ∧ ‖x‖ = 1} ∧
        μHE[n] {x : Rn (n + ℓ) | x ∈ H ∧ ‖x‖ = 1} < ∞ := by
    intro H hH
    obtain ⟨c, C, hc, hcap⟩ := Submission.bf_sphereCap_measure_bounds n ℓ hn H hH
    obtain ⟨ζ, hζH, hζ⟩ : ∃ ζ ∈ H, ‖ζ‖ = 1 := by
      have hH0 : H ≠ ⊥ := by
        rintro rfl
        rw [finrank_bot] at hH
        omega
      obtain ⟨x, hxH, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH0
      exact ⟨(‖x‖⁻¹ : ℝ) • x, H.smul_mem _ hxH, norm_smul_inv_norm hx⟩
    refine ⟨?_, ?_⟩
    · calc (0 : ℝ≥0∞) < ENNReal.ofReal (c * 2 ^ n) := ENNReal.ofReal_pos.2 (by positivity)
        _ ≤ μHE[n] ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ 2) :=
          (hcap ζ hζH hζ 2 two_pos).1 le_rfl
        _ ≤ μHE[n] {x : Rn (n + ℓ) | x ∈ H ∧ ‖x‖ = 1} := measure_mono inter_subset_left
    · have hsub : {x : Rn (n + ℓ) | x ∈ H ∧ ‖x‖ = 1} ⊆
          {θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ 3 := by
        intro x hx
        refine ⟨hx, ?_⟩
        rw [Metric.mem_ball, dist_eq_norm]
        calc ‖x - ζ‖ ≤ ‖x‖ + ‖ζ‖ := norm_sub_le x ζ
          _ < 3 := by rw [hx.2, hζ]; norm_num
      exact (measure_mono hsub).trans_lt
        ((hcap ζ hζH hζ 3 three_pos).2.trans_lt ENNReal.ofReal_lt_top)
  -- Step 1: the bi-invariant Haar probability `θ_N` on `O(N)`, the stabilizer of `U = 0`.
  obtain ⟨θ, hθ, hθO, hθinv⟩ := Submission.bf_orthStabilizer_haar_exists (n + ℓ) ⊥
  have hθO' : ∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1 := hθO.mono fun _ hg ↦ hg.1
  have hθR : ∀ k : Rn (n + ℓ) →L[ℝ] Rn (n + ℓ), ContinuousLinearMap.adjoint k * k = 1 →
      Measure.map (fun g ↦ g * k) θ = θ := fun k hk ↦
    (hθinv k hk fun x hx ↦ by rw [(Submodule.mem_bot ℝ).1 hx, map_zero]).2
  -- `W₀ = span{e_1, …, e_n}`, an `n`-plane.
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Submodule ℝ (Rn (n + ℓ)), finrank ℝ W₀ = n := by
    have hv : LinearIndependent ℝ fun i : Fin n ↦
        EuclideanSpace.basisFun (Fin (n + ℓ)) ℝ (Fin.castAdd ℓ i) :=
      (EuclideanSpace.basisFun (Fin (n + ℓ)) ℝ).orthonormal.linearIndependent.comp _
        (Fin.castAdd_injective n ℓ)
    exact ⟨_, (finrank_span_eq_card hv).trans (Fintype.card_fin n)⟩
  -- Steps 2–6: for every `a`, `θ_N{g : (a, g P₀ g*) ∈ Exc} = 0`.
  have hpt : ∀ a : Rn (n + ℓ),
      θ {g | (a, g * W₀.starProjection * ContinuousLinearMap.adjoint g) ∈ Exc} = 0 := fun a ↦
    Submission.bf_haar_excPointwise_null n ℓ Exc Bad hBad hS a (h1 a) (h2 a) θ hθ hθO' hθR W₀ hW₀
  -- Step 7: Tonelli over `μ ⊗ θ_N`. The set `Q` of the `p` with `μ(Exc^p) ≠ 0` is Borel, and
  -- `g P₀ g* ∉ Q` for `θ_N`-a.e. `g`.
  set Q : Set (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)) := {p | μ {a | (a, p) ∈ Exc} ≠ 0} with hQ
  have hμExc : Measurable fun p : Rn (n + ℓ) →L[ℝ] Rn (n + ℓ) ↦ μ {a | (a, p) ∈ Exc} :=
    measurable_measure_prodMk_right hExc
  have hQm : MeasurableSet Q := hμExc (measurableSet_singleton 0).compl
  have hconj : Continuous fun g : Rn (n + ℓ) →L[ℝ] Rn (n + ℓ) ↦
      g * W₀.starProjection * ContinuousLinearMap.adjoint g :=
    (continuous_id.mul continuous_const).mul
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn (n + ℓ)) (F := Rn (n + ℓ))).continuous
  have hgood : MeasurableSet {q : Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)) |
      (q.1, q.2 * W₀.starProjection * ContinuousLinearMap.adjoint q.2) ∉ Exc} :=
    (measurable_fst.prodMk (hconj.measurable.comp measurable_snd) hExc).compl
  have hae : ∀ᵐ a ∂μ, ∀ᵐ g ∂θ,
      (a, g * W₀.starProjection * ContinuousLinearMap.adjoint g) ∉ Exc :=
    Eventually.of_forall fun a ↦ measure_eq_zero_iff_ae_notMem.1 (hpt a)
  have hQnull : θ {g | g * W₀.starProjection * ContinuousLinearMap.adjoint g ∈ Q} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [(Measure.ae_ae_comm (p := fun a g ↦
      (a, g * W₀.starProjection * ContinuousLinearMap.adjoint g) ∉ Exc) hgood).1 hae] with g hg
    simp only [hQ, mem_ofPred_eq, ne_eq, not_not]
    exact measure_eq_zero_iff_ae_notMem.2 hg
  -- Steps 8–10: transfer from `θ_N` to Lebesgue-a.e. frames.
  exact (Submission.bf_haar_null_to_frames (n + ℓ) n
    (Submission.bf_frameProjection_continuousOn (n + ℓ) n) θ hθ hθO' hθR W₀ hW₀ Q hQm
    hQnull).mono fun v hv hlin ↦ not_not.1 (hv hlin)

/-- **Cone trichotomy for almost every frame** (Steps 8–9 of the proof of Simon Ch. 3,
Theorem 3.6, `chapter-03.txt` lines 530–536, whose proof Simon defers to [Fed69]/[Ros84];
P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Ch. 18; M. G. Dall'Alba,
*The Besicovitch–Federer Projection Theorem*, Padova 2020, Lemmas 4.15, 5.5, 5.6 and
Theorem 4.16). Let `A ⊆ ℝ^{n+ℓ}` be compact with `Hⁿ(A) < ∞`, `δ > 0`, and
`X_p(a, r, s) = {x : |p(x - a)| < s|x - a|} ∩ B(a, r)`. Then for Lebesgue-a.e. linearly
independent frame `v`, with `p = p_{span v}`, `Hⁿ`-a.e. `a ∈ A` satisfies the trichotomy
`T(a, p)`: `(rs)⁻ⁿ Hⁿ(A ∩ X_p(a, r, s)) → 0` as `s ↓ 0` uniformly in `r ∈ (0, δ)`; or for every
`K` there are arbitrarily small `s` and some `r ∈ (0, δ)` with `Hⁿ(A ∩ X_p(a, r, s)) ≥ K(rs)ⁿ`;
or some `b ∈ A \ {a}` with `|b - a| < δ` has `p(b - a) = 0`.
The exceptional pairs `Exc = {(a, p) : a ∈ A, ¬T(a, p)}` and the bad axes
`Bad = {(a, Q, θ) : a ∈ A, ¬T_θ(a, Q)}`, where `T_θ` is the same trichotomy for the slab cones
`{x : |Q(x - a) - (Q(x - a)·θ)θ| < s|Q(x - a)|} ∩ B(a, r)` (axis condition
`Q(b - a) = (Q(b - a)·θ)θ`), are Borel (`bf_coneExceptional_measurableSet`, Steps 1 and 4.2 of
the node proof). For an `(n+1)`-plane `H`, `Hⁿ`-a.e. unit `θ ∈ H` is a good axis for `Q = p_H`
(`bf_sphere_ae_slabGood`, Step 2). If `T(a, p_W)` fails for an `n`-plane `W`, then every
orthonormal basis `u` of `Wᗮ` has a bad axis `u_j` for `p_{W ⊕ ℝu_j}`
(`bf_slabGood_imp_coneTrichotomy`, Step 3). Averaging over `O(n+ℓ)` and transferring to frames
(`bf_frameAveraging_null`, Steps 4–5) with the finite measure `μ = Hⁿ ⌞ A` gives
`Hⁿ(A ∩ {a : (a, p_{span v}) ∈ Exc}) = 0` for a.e. linearly independent `v`. -/
theorem Submission.bf_coneTrichotomy_ae_frames :
    ∀ (n ℓ : ℕ), 0 < n → 0 < ℓ → ∀ A : Set (Rn (n + ℓ)), IsCompact A → μHE[n] A < ∞ →
      ∀ δ : ℝ, 0 < δ → ForAlmostAllProjections (n + ℓ) n (fun p ↦ μHE[n] {a | a ∈ A ∧
        ¬ ((∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ, 0 < r →
          r < δ → μHE[n] (A ∩ ({x | ‖p (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r)) ≤
            ENNReal.ofReal (c * (r * s) ^ n)) ∨
        (∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧
          ENNReal.ofReal (K * (r * s) ^ n) ≤
            μHE[n] (A ∩ ({x | ‖p (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r))) ∨
        ∃ b ∈ A, b ≠ a ∧ dist b a < δ ∧ p (b - a) = 0)} = 0) := by
  intro n ℓ hn hℓ A hA hAfin δ hδ
  -- `Exc = {(a, p) : a ∈ A, ¬T(a, p)}`, the exceptional pairs of the statement
  let Exc : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ))) :=
    {q | q.1 ∈ A ∧ ¬ ((∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ,
      0 < r → r < δ → μHE[n] (A ∩ ({x | ‖q.2 (x - q.1)‖ < s * ‖x - q.1‖} ∩ Metric.ball q.1 r)) ≤
        ENNReal.ofReal (c * (r * s) ^ n)) ∨
      (∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧
        ENNReal.ofReal (K * (r * s) ^ n) ≤
          μHE[n] (A ∩ ({x | ‖q.2 (x - q.1)‖ < s * ‖x - q.1‖} ∩ Metric.ball q.1 r))) ∨
      ∃ b ∈ A, b ≠ q.1 ∧ dist b q.1 < δ ∧ q.2 (b - q.1) = 0)}
  -- `Bad = {(a, Q, θ) : a ∈ A, ¬T_θ(a, Q)}`, the bad axes `θ` of the slab cones of `Q`
  let Bad : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)) × Rn (n + ℓ)) :=
    {q | q.1 ∈ A ∧ ¬ ((∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ,
      0 < r → r < δ → μHE[n] (A ∩ ({x | ‖q.2.1 (x - q.1) -
        inner ℝ (q.2.1 (x - q.1)) q.2.2 • q.2.2‖ < s * ‖q.2.1 (x - q.1)‖} ∩
          Metric.ball q.1 r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) ∨
      (∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧
        ENNReal.ofReal (K * (r * s) ^ n) ≤ μHE[n] (A ∩ ({x | ‖q.2.1 (x - q.1) -
          inner ℝ (q.2.1 (x - q.1)) q.2.2 • q.2.2‖ < s * ‖q.2.1 (x - q.1)‖} ∩
            Metric.ball q.1 r))) ∨
      ∃ b ∈ A, b ≠ q.1 ∧ dist b q.1 < δ ∧
        q.2.1 (b - q.1) - inner ℝ (q.2.1 (b - q.1)) q.2.2 • q.2.2 = 0)}
  -- Step 1: `Exc` is Borel (cones `|p(x - a)| < s|x - a|`: `F₁ (a, p) = p`, `F₂ = id`)
  have hExc : MeasurableSet Exc :=
    Submission.bf_coneExceptional_measurableSet n ℓ
      (X := Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ))) A hA hAfin δ hδ Prod.fst
      (fun ξ y ↦ ξ.2 y) (fun _ y ↦ y) continuous_fst (by fun_prop) (by fun_prop)
  -- Step 4.2: `Bad` is Borel (slab cones: `F₁ (a, Q, θ) = Q - ⟪Q ·, θ⟫ θ`, `F₂ (a, Q, θ) = Q`)
  have hBad : MeasurableSet Bad :=
    Submission.bf_coneExceptional_measurableSet n ℓ
      (X := Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)) × Rn (n + ℓ)) A hA hAfin δ hδ Prod.fst
      (fun ξ y ↦ ξ.2.1 y - inner ℝ (ξ.2.1 y) ξ.2.2 • ξ.2.2) (fun ξ y ↦ ξ.2.1 y)
      continuous_fst (by fun_prop) (by fun_prop)
  -- Step 2 (sphere lemma): on the unit sphere of an `(n+1)`-plane `H`, `Hⁿ`-a.e. axis is good
  have hsph : ∀ (a : Rn (n + ℓ)) (H : Submodule ℝ (Rn (n + ℓ))), finrank ℝ H = n + 1 →
      μHE[n] {θ | θ ∈ H ∧ ‖θ‖ = 1 ∧ (a, H.starProjection, θ) ∈ Bad} = 0 := by
    intro a H hH
    refine measure_mono_null ?_ (Submission.bf_sphere_ae_slabGood n ℓ hn H hH A hA hAfin δ hδ a)
    intro θ hθ
    exact ⟨hθ.1, hθ.2.1, hθ.2.2.2⟩
  -- Step 3 (slab cones versus cones): if `T(a, p_W)` fails, some axis `u_j` is bad
  have hslab : ∀ (a : Rn (n + ℓ)) (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n →
      (a, W.starProjection) ∈ Exc → ∀ u : Fin ℓ → Rn (n + ℓ), Orthonormal ℝ u →
        (∀ j, u j ∈ Wᗮ) → ∃ j, (a, (W ⊔ Submodule.span ℝ {u j}).starProjection, u j) ∈ Bad := by
    intro a W hW haW u hu huW
    by_contra hcon
    push Not at hcon
    refine haW.2
      (Submission.bf_slabGood_imp_coneTrichotomy n ℓ hn hℓ W hW u hu huW A δ a fun j ↦ ?_)
    by_contra hng
    exact hcon j ⟨haW.1, hng⟩
  -- Steps 4–5: average over `O(n + ℓ)` and transfer to frames, for `μ = Hⁿ ⌞ A` (finite)
  have hfin : IsFiniteMeasure ((μHE[n] : Measure (Rn (n + ℓ))).restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hAfin⟩
  have key := Submission.bf_frameAveraging_null n ℓ hn hℓ
    ((μHE[n] : Measure (Rn (n + ℓ))).restrict A) hfin Exc Bad hExc hBad hsph hslab
  refine key.mono fun v hv hlin ↦ ?_
  have h0 : ((μHE[n] : Measure (Rn (n + ℓ))).restrict A) {a | (a, frameProjection v) ∈ Exc} = 0 :=
    hv hlin
  rw [Measure.restrict_apply' hA.measurableSet] at h0
  refine measure_mono_null ?_ h0
  intro a ha
  exact ⟨ha, ha.1⟩

/-- **Besicovitch–Federer for compact purely unrectifiable sets of finite measure**, given
Eilenberg's inequality (Step 10 of the proof of Simon Ch. 3, Theorem 3.6, `chapter-03.txt`
lines 530–536, whose proof Simon defers to [Fed69]/[Ros84]; M. G. Dall'Alba, *The
Besicovitch–Federer Projection Theorem*, Padova 2020, proof of Theorem 5.1; P. Mattila, *Geometry
of Sets and Measures in Euclidean Spaces*, Theorem 18.1). For a.e. frame `v` the cone trichotomy
holds off an `Hⁿ`-null set at every scale `δᵢ = 1/(i+1)`; let `P = p_{span v}`. A point `a ∈ A`
outside that set, outside the `Hⁿ`-null set of zero cone density and outside the set of infinite
cone density (whose `P`-image is null) has, for every `i`, a point `b ≠ a` of `A` with
`|b - a| < δᵢ` and `Pb = Pa`; so its fibre `A ∩ P⁻¹(Pa)` is infinite, and the infinite fibres
have `Hⁿ`-null image by Eilenberg's inequality. As `P` is Lipschitz, `Hⁿ(P(A)) = 0`. -/
theorem Submission.bf_compact_projection_null :
    (∀ (N m k : ℕ), ∃ C : ℝ≥0, ∀ (A : Set (Rn N)) (f : Rn N → Rn m) (L : ℝ≥0),
      LipschitzWith L f → ∃ g : Rn m → ℝ≥0∞, Measurable g ∧
        (∀ y, μHE[k] (A ∩ f ⁻¹' {y}) ≤ g y) ∧
          ∫⁻ y, g y ≤ ((C * L ^ m : ℝ≥0) : ℝ≥0∞) * μHE[m + k] A) →
      ∀ (n ℓ : ℕ), 0 < n → 0 < ℓ → ∀ A : Set (Rn (n + ℓ)), IsCompact A →
        PurelyUnrectifiable n A → μHE[n] A < ∞ →
          ForAlmostAllProjections (n + ℓ) n (fun p ↦ μHE[n] (p '' A) = 0) := by
  intro hEil n ℓ hn hℓ A hAc hAu hAfin
  -- Step 2: for a.e. frame `v`, for every `i` the cone trichotomy at scale `δᵢ = 1/(i+1)` holds
  -- off an `Hⁿ`-null set `Gᵢ(v)` (a countable intersection of full-measure sets of frames).
  have htri := fun i : ℕ ↦
    Submission.bf_coneTrichotomy_ae_frames n ℓ hn hℓ A hAc hAfin (1 / ((i : ℝ) + 1))
      Nat.one_div_pos_of_nat
  unfold ForAlmostAllProjections at htri ⊢
  filter_upwards [ae_all_iff.2 htri] with v hv hli
  -- Step 3: `p_{span v}` is the orthogonal projection `P` onto the `n`-plane `W = span v`.
  obtain ⟨W, hWdef⟩ : ∃ W : Submodule ℝ (Rn (n + ℓ)), W = Submodule.span ℝ (Set.range v) :=
    ⟨_, rfl⟩
  have hW : finrank ℝ W = n := by rw [hWdef, finrank_span_eq_card hli, Fintype.card_fin]
  have hPW : frameProjection v = W.starProjection := by subst hWdef; rfl
  rw [hPW] at hv ⊢
  -- `P` is `1`-Lipschitz, so it maps `Hⁿ`-null sets to `Hⁿ`-null sets.
  have hPnull : ∀ S : Set (Rn (n + ℓ)), μHE[n] S = 0 → μHE[n] (W.starProjection '' S) = 0 := by
    intro S hS
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
      (A := S) n W.lipschitzWith_starProjection.lipschitzOnWith
    rwa [hS, mul_zero, nonpos_iff_eq_zero] at h
  -- Step 4: the exceptional sets, each `Hⁿ`-null or with `Hⁿ`-null image under `P`.
  have hA1 := fun i : ℕ ↦
    Submission.bf_coneDensity_zero_null n ℓ hn W hW A hAu (1 / ((i : ℝ) + 1))
      Nat.one_div_pos_of_nat
  have hA2 := fun i : ℕ ↦
    Submission.bf_coneDensity_top_projection_null n ℓ hn W hW A hAc hAfin (1 / ((i : ℝ) + 1))
      Nat.one_div_pos_of_nat
  have hA3 := Submission.bf_infiniteFibre_projection_null hEil n ℓ W hW A hAfin
  -- Steps 5–6: `P(A)` is covered by the images of the exceptional sets.
  refine measure_mono_null ?_ (measure_union_null (measure_union_null
    (hPnull _ (measure_iUnion_null fun i ↦ measure_union_null (hv i hli) (hA1 i)))
    (measure_iUnion_null hA2)) hA3)
  rintro _ ⟨a, ha, rfl⟩
  by_contra hcon
  obtain ⟨h12, h3⟩ := not_or.1 hcon
  obtain ⟨h1, h2⟩ := not_or.1 h12
  refine h3 ⟨a, ⟨ha, ?_⟩, rfl⟩
  -- At every scale `δᵢ` only the third alternative of the trichotomy is left: some `b ≠ a` in `A`
  -- has `|b - a| < δᵢ` and `P(b - a) = 0`.
  have hax : ∀ i : ℕ, ∃ b ∈ A, b ≠ a ∧ dist b a < 1 / ((i : ℝ) + 1) ∧
      W.starProjection (b - a) = 0 := by
    intro i
    by_contra hnot
    refine h1 ⟨a, mem_iUnion.2 ⟨i, Or.inl ⟨ha, ?_⟩⟩, rfl⟩
    rintro (h0 | htop | hb)
    · exact h1 ⟨a, mem_iUnion.2 ⟨i, Or.inr ⟨ha, h0⟩⟩, rfl⟩
    · exact h2 (mem_iUnion.2 ⟨i, a, ⟨ha, htop⟩, rfl⟩)
    · exact hnot hb
  -- Hence the fibre `{b ∈ A | Pb = Pa}` is infinite: were it finite, its points other than `a`
  -- would form a closed set missing `a`, hence missing a ball `B(a, ε)` with `ε > δᵢ` for some `i`.
  intro hfin
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.1 (hfin.sdiff (t := {a})).isClosed.isOpen_compl a fun h ↦ h.2 rfl
  obtain ⟨i, hi⟩ := exists_nat_one_div_lt hε
  obtain ⟨b, hbA, hba, hdist, hPb⟩ := hax i
  rw [map_sub, sub_eq_zero] at hPb
  exact hball (Metric.mem_ball.2 (hdist.trans hi)) ⟨⟨hbA, hPb⟩, hba⟩

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
