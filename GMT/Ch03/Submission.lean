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

/-- **Regular level slices of a `C¹` map have countably `k`-rectifiable `C¹` images**
(Simon Ch. 2, proof of Theorem 6.4, `chapter-02.txt` lines 1476–1496: off the critical set the
implicit function theorem makes `G⁻¹(y)` a `k`-dimensional `C¹` submanifold). At a point `u₀` of
`D` where `DG(u₀)` is onto, `K₀ = ker DG(u₀)` has dimension `k`; with `π` the orthogonal
projection onto `K₀` followed by `K₀ ≅ ℝᵏ`, the map `Φ = (G, π)` has invertible derivative at
`u₀`, and its local inverse `Θ` parametrizes the slice near `u₀` by the open set
`W = {z | (y, z) ∈ Φ(U₀), Θ(y, z) ∈ D, DΦ(Θ(y, z)) invertible}` through the `C¹` map
`z ↦ ψ(Θ(y, z))`. `C¹` images of open subsets of `ℝᵏ` are countably `k`-rectifiable (Lipschitz
on each compact piece of a compact exhaustion, then extended), and by Lindelöf countably many
such charts cover the regular part. -/
theorem Submission.c1_regular_level_slice_image_countablyRectifiable : ∀ (m k N : ℕ) (D : Set (Rn (m + k))) (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m) (y : Rn m), IsOpen D → ContDiffOn ℝ 1 ψ D → ContDiff ℝ 1 G → CountablyRectifiable k (ψ '' (D ∩ {u | Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y})) := by
  intro m k N D ψ G y hD hψ hG
  -- C¹ images of open subsets of ℝᵏ are countably k-rectifiable
  -- (inline copy of SimonGMT `countablyRectifiable_image_contDiffOn_open`).
  have himage : ∀ (W : Set (Rn k)) (h : Rn k → Rn N), IsOpen W → ContDiffOn ℝ 1 h W →
      CountablyRectifiable k (h '' W) := by
    intro W h hW hh
    let _ : LocallyCompactSpace W := hW.locallyCompactSpace
    obtain ⟨Kc, hKc, hKcover⟩ := SigmaCompactSpace.exists_compact_covering (X := W)
    let C : ℕ → Set (Rn k) := fun j => ((↑) : W → Rn k) '' Kc j
    have hCc : ∀ j, IsCompact (C j) := fun j => (hKc j).image continuous_subtype_val
    have hCW : ∀ j, C j ⊆ W := by
      rintro j _ ⟨x, -, rfl⟩
      exact x.2
    have hLip : ∀ j, ∃ L : ℝ≥0, LipschitzOnWith L h (C j) := by
      intro j
      apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hCc j)
      intro x hx
      obtain ⟨L, t, ht, hht⟩ := (hh.contDiffAt (hW.mem_nhds (hCW j hx))).exists_lipschitzOnWith
      exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hht⟩
    choose L hL using hLip
    choose g hgL hgeq using fun j => (hL j).extend_finite_dimension
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion (fun j => range (g j))
      (fun j => Poincare.SimonGMT.Chapter03.countablyRectifiable_range (hgL j))).mono ?_
    rintro _ ⟨x, hxW, rfl⟩
    have hx : (⟨x, hxW⟩ : W) ∈ ⋃ j, Kc j := by rw [hKcover]; trivial
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    exact mem_iUnion.2 ⟨j, x, (hgeq j ⟨⟨x, hxW⟩, hj, rfl⟩).symm⟩
  -- Local charts at regular points (implicit function theorem via Φ = (G, π)).
  have hloc : ∀ u₀ : ↥(D ∩ {u | Function.Surjective (fderiv ℝ G u)}),
      ∃ O : Set (Rn (m + k)), IsOpen O ∧ (u₀ : Rn (m + k)) ∈ O ∧
        CountablyRectifiable k (ψ '' (O ∩ G ⁻¹' {y})) := by
    rintro ⟨u₀, hu₀D, hu₀S⟩
    set A : Rn (m + k) →L[ℝ] Rn m := fderiv ℝ G u₀ with hA
    have hrange : LinearMap.range (A : Rn (m + k) →ₗ[ℝ] Rn m) = ⊤ := LinearMap.range_eq_top.2 hu₀S
    set K₀ : Submodule ℝ (Rn (m + k)) := LinearMap.ker (A : Rn (m + k) →ₗ[ℝ] Rn m) with hK₀
    have hker : finrank ℝ K₀ = k := by
      have h1 := LinearMap.finrank_range_add_finrank_ker (A : Rn (m + k) →ₗ[ℝ] Rn m)
      rw [hrange, finrank_top] at h1
      simp only [finrank_euclideanSpace, Fintype.card_fin] at h1
      change m + finrank ℝ K₀ = m + k at h1
      omega
    obtain ⟨ι⟩ : Nonempty (K₀ ≃L[ℝ] Rn k) :=
      FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by simp [hker])
    let π : Rn (m + k) →L[ℝ] Rn k := (ι : K₀ →L[ℝ] Rn k).comp K₀.orthogonalProjectionOnto
    let Φ : Rn (m + k) → Rn m × Rn k := fun u => (G u, π u)
    have hΦ : ContDiff ℝ 1 Φ := hG.prodMk π.contDiff
    have hΦd : ∀ u, HasFDerivAt Φ ((fderiv ℝ G u).prod π) u := fun u =>
      ((hG.differentiable one_ne_zero u).hasFDerivAt).prodMk π.hasFDerivAt
    have hinj : Function.Injective (A.prod π) := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      have hAv : A v = 0 := congrArg Prod.fst hv
      have hπv : π v = 0 := congrArg Prod.snd hv
      have hvK : v ∈ K₀ := hAv
      have hP : K₀.orthogonalProjectionOnto v = ⟨v, hvK⟩ :=
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨v, hvK⟩
      have : ι ⟨v, hvK⟩ = 0 := by simpa [π, hP] using hπv
      have h0 : (⟨v, hvK⟩ : K₀) = 0 := by simpa using this
      simpa using congrArg Subtype.val h0
    have hdim : finrank ℝ (Rn (m + k)) = finrank ℝ (Rn m × Rn k) := by
      simp [Module.finrank_prod]
    let e' : Rn (m + k) ≃L[ℝ] Rn m × Rn k :=
      ((A.prod π : Rn (m + k) →ₗ[ℝ] Rn m × Rn k).linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
    have he' : (e' : Rn (m + k) →L[ℝ] Rn m × Rn k) = A.prod π := by ext1 v; rfl
    -- `V`: the open set where `DΦ` is invertible.
    let V : Set (Rn (m + k)) := (fderiv ℝ Φ) ⁻¹'
      range ((↑) : (Rn (m + k) ≃L[ℝ] Rn m × Rn k) → Rn (m + k) →L[ℝ] Rn m × Rn k)
    have hVo : IsOpen V := ContinuousLinearEquiv.isOpen.preimage (hΦ.continuous_fderiv one_ne_zero)
    have hu₀V : u₀ ∈ V := ⟨e', by rw [he', (hΦd u₀).fderiv]⟩
    have hΦa : ContDiffAt ℝ 1 Φ u₀ := hΦ.contDiffAt
    have hΦ'a : HasFDerivAt Φ (e' : Rn (m + k) →L[ℝ] Rn m × Rn k) u₀ := by
      rw [he']; exact hΦd u₀
    have hstrict := ContDiffAt.hasStrictFDerivAt' hΦa hΦ'a one_ne_zero
    let e := HasStrictFDerivAt.toOpenPartialHomeomorph Φ hstrict
    have hecoe : (e : Rn (m + k) → Rn m × Rn k) = Φ := rfl
    refine ⟨e.source ∩ D ∩ V, (e.open_source.inter hD).inter hVo,
      ⟨⟨HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hstrict, hu₀D⟩, hu₀V⟩, ?_⟩
    -- The slice through the chart is the image of the open set `W` under `h`.
    let W : Set (Rn k) := (fun z => (y, z)) ⁻¹' (e.target ∩ e.symm ⁻¹' (D ∩ V))
    have hWo : IsOpen W :=
      (e.isOpen_inter_preimage_symm (hD.inter hVo)).preimage (continuous_const.prodMk continuous_id)
    let h : Rn k → Rn N := fun z => ψ (e.symm (y, z))
    have hh : ContDiffOn ℝ 1 h W := by
      intro z hz
      apply ContDiffAt.contDiffWithinAt
      obtain ⟨hzt, hzD, ⟨L, hL⟩⟩ := hz
      have h1 : ContDiffAt ℝ 1 e.symm (y, z) := by
        refine e.contDiffAt_symm hzt (f₀' := L) ?_ ?_
        · rw [hL, hecoe]
          exact (hΦ.differentiable one_ne_zero _).hasFDerivAt
        · rw [hecoe]; exact hΦ.contDiffAt
      have h2 : ContDiffAt ℝ 1 ψ (e.symm (y, z)) := hψ.contDiffAt (hD.mem_nhds hzD)
      exact h2.comp z (h1.comp z (contDiffAt_const.prodMk contDiffAt_id))
    apply (himage W h hWo hh).mono
    rintro _ ⟨u, ⟨⟨⟨hus, huD⟩, huV⟩, huy⟩, rfl⟩
    have hey : e u = (y, π u) := by
      rw [hecoe]; simp only [Φ]; rw [show G u = y from huy]
    refine ⟨π u, ?_, ?_⟩
    · show (y, π u) ∈ e.target ∩ e.symm ⁻¹' (D ∩ V)
      rw [← hey]
      exact ⟨e.map_source hus, by rw [mem_preimage, e.left_inv hus]; exact ⟨huD, huV⟩⟩
    · show ψ (e.symm (y, π u)) = ψ u
      rw [← hey, e.left_inv hus]
  -- Lindelöf: countably many charts cover the regular part.
  choose O hOo hmem hrect using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable O hOo
  have hsub : ψ '' (D ∩ {u | Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y}) ⊆
      ⋃₀ ((fun i => ψ '' (O i ∩ G ⁻¹' {y})) '' T) := by
    rintro _ ⟨u, ⟨huDS, huy⟩, rfl⟩
    have hu : u ∈ ⋃ i ∈ T, O i := by
      rw [hTU]; exact mem_iUnion.2 ⟨⟨u, huDS⟩, hmem _⟩
    obtain ⟨i, hiT, hui⟩ := mem_iUnion₂.1 hu
    exact ⟨_, ⟨i, hiT, rfl⟩, ⟨u, ⟨hui, huy⟩, rfl⟩⟩
  refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion (hTc.image _) ?_).mono hsub
  rintro _ ⟨i, -, rfl⟩
  exact hrect i
/-- **`C¹` maps on open sets send `Hᵏ`-null sets to `Hᵏ`-null sets**: the critical-part step of
the slice rectifiability in Simon Ch. 3, Remark 2.10(2) (`chapter-03.txt` lines 437–442). Each
`u ∈ D` has an open `t u ∋ u` on which `ψ` is `K u`-Lipschitz (mean value inequality); by
Lindelöf countably many `t u`, `u ∈ T`, cover `Z ⊆ D`. By Ch. 2, Thm. 1.8(i) (`chapter-02.txt`
lines 270–295, valid for non-measurable sets) `Hᵏ(ψ(Z ∩ t u)) ≤ (K u)ᵏ Hᵏ(Z ∩ t u) = 0`, and
countable subadditivity gives `Hᵏ(ψ(Z)) = 0`. No measurability of `Z` and no relation between
`k` and `n` is needed: all estimates are for outer measures. -/
theorem Submission.contDiffOn_image_euclideanHausdorff_null : ∀ (n N k : ℕ) (D Z : Set (Rn n))
    (ψ : Rn n → Rn N), IsOpen D → ContDiffOn ℝ 1 ψ D → Z ⊆ D → μHE[k] Z = 0 →
    μHE[k] (ψ '' Z) = 0 := by
  intro n N k D Z ψ hD hψ hZD hZ
  -- Step 1: each `u ∈ D` has an open `t u ∋ u` on which `ψ` is `K u`-Lipschitz.
  have hloc : ∀ u : D, ∃ K : ℝ≥0, ∃ t : Set (Rn n), IsOpen t ∧ (u : Rn n) ∈ t ∧
      LipschitzOnWith K ψ t := by
    intro u
    obtain ⟨K, t, ht, hKt⟩ := (hψ.contDiffAt (hD.mem_nhds u.2)).exists_lipschitzOnWith
    obtain ⟨t', ht't, ht'o, hut'⟩ := mem_nhds_iff.mp ht
    exact ⟨K, t', ht'o, hut', hKt.mono ht't⟩
  choose K t ht hut hKt using hloc
  -- Step 2 (Lindelöf): countably many `t u`, `u ∈ T`, cover `Z ⊆ D`.
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable t ht
  have hcover : Z ⊆ ⋃ i ∈ T, t i := by
    intro z hz
    rw [hTU]
    exact mem_iUnion.2 ⟨⟨z, hZD hz⟩, hut _⟩
  have himg : ψ '' Z ⊆ ⋃ i ∈ T, ψ '' (Z ∩ t i) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, hiT, hzi⟩ := mem_iUnion₂.1 (hcover hz)
    exact mem_iUnion₂.2 ⟨i, hiT, ⟨z, ⟨hz, hzi⟩, rfl⟩⟩
  -- Steps 3–4: `Hᵏ(ψ(Z ∩ t i)) ≤ (K i)ᵏ Hᵏ(Z ∩ t i) = 0`, then countable subadditivity.
  refine measure_mono_null himg ((measure_biUnion_null_iff hTc).2 fun i _ => ?_)
  refine le_antisymm ?_ bot_le
  calc μHE[k] (ψ '' (Z ∩ t i)) ≤ (K i : ℝ≥0∞) ^ k * μHE[k] (Z ∩ t i) :=
        Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k
          ((hKt i).mono inter_subset_right)
    _ = 0 := by rw [measure_mono_null inter_subset_left hZ, mul_zero]
/-- **Fine covers with small weighted image volume give `Hᵏ`-null slices** (the Fatou covering
criterion behind Simon Ch. 2, p. 66, the consequence of (6.3) stated before 6.4,
`chapter-02.txt` lines 1476–1478). Let `k > 0` and let `S ⊆ ℝⁿ` and `G : ℝⁿ → ℝᵐ` be arbitrary.
If for every `ε > 0` some countable cover `(Tᵢ)` of `S` has `diam Tᵢ ≤ ε` and
`∑ᵢ (diam Tᵢ)ᵏ Lᵐ(G(Tᵢ ∩ S)) ≤ ε`, then `Hᵏ(S ∩ G⁻¹{y}) = 0` for `Lᵐ`-a.e. `y ∈ ℝᵐ`.
With measurable hulls `Aⱼᵢ ⊇ G(Tⱼᵢ ∩ S)` of equal measure, the majorants
`gⱼ = ∑ᵢ (diam Tⱼᵢ)ᵏ 1_{Aⱼᵢ}` have `∫ gⱼ ≤ εⱼ → 0`, so `liminf gⱼ = 0` a.e. by Fatou; for such
`y` the covers `Tⱼᵢ ∩ S ∩ G⁻¹{y}` give `Hᵏ(S ∩ G⁻¹{y}) ≤ liminf gⱼ(y) = 0`. -/
theorem Submission.critSlices_ae_slice_null_of_covers : ∀ (n m k : ℕ) (S : Set (Rn n)) (G : Rn n → Rn m), 0 < k → (∀ ε : ℝ≥0∞, 0 < ε → ∃ (ι : Type) (_ : Countable ι) (T : ι → Set (Rn n)), S ⊆ ⋃ i, T i ∧ (∀ i, Metric.ediam (T i) ≤ ε) ∧ ∑' i, Metric.ediam (T i) ^ k * volume (G '' (T i ∩ S)) ≤ ε) → ∀ᵐ y ∂(volume : Measure (Rn m)), μHE[k] (S ∩ G ⁻¹' {y}) = 0 := by
  intro n m k S G hk hcov
  -- Covers at the scales `εⱼ = (j + 1)⁻¹ → 0`.
  have hεpos : ∀ j : ℕ, (0 : ℝ≥0∞) < ((j : ℝ≥0∞) + 1)⁻¹ := fun j =>
    ENNReal.inv_pos.2 (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top j, ENNReal.one_ne_top⟩)
  have hr : Tendsto (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) :=
    (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)).congr fun j => by
      simp [Nat.cast_add, Nat.cast_one]
  choose ι hι T hTcov hTdiam hTsum using fun j : ℕ => hcov _ (hεpos j)
  -- Measurable hulls `Aⱼᵢ ⊇ G(Tⱼᵢ ∩ S)` of equal measure and the majorants `gⱼ`.
  set A : ∀ j, ι j → Set (Rn m) := fun j i => toMeasurable volume (G '' (T j i ∩ S))
  set g : ℕ → Rn m → ℝ≥0∞ := fun j y => ∑' i, Metric.ediam (T j i) ^ k * (A j i).indicator 1 y
  have hterm : ∀ j i, Measurable fun y => Metric.ediam (T j i) ^ k * (A j i).indicator 1 y :=
    fun j i => measurable_const.mul (measurable_one.indicator (measurableSet_toMeasurable _ _))
  have hgm : ∀ j, Measurable (g j) := fun j => Measurable.tsum fun i => hterm j i
  have hgint : ∀ j, ∫⁻ y, g j y ≤ ((j : ℝ≥0∞) + 1)⁻¹ := by
    intro j
    calc ∫⁻ y, g j y
        = ∑' i, ∫⁻ y, Metric.ediam (T j i) ^ k * (A j i).indicator 1 y :=
          lintegral_tsum fun i => (hterm j i).aemeasurable
      _ = ∑' i, Metric.ediam (T j i) ^ k * volume (G '' (T j i ∩ S)) := by
          congr 1
          ext i
          rw [lintegral_const_mul _ (measurable_one.indicator (measurableSet_toMeasurable _ _)),
            lintegral_indicator_one (measurableSet_toMeasurable _ _), measure_toMeasurable]
      _ ≤ ((j : ℝ≥0∞) + 1)⁻¹ := hTsum j
  -- Fatou: `∫ liminf gⱼ ≤ liminf ∫ gⱼ ≤ liminf εⱼ = 0`, so `liminf gⱼ = 0` a.e.
  have hfatou : ∫⁻ y, liminf (fun j => g j y) atTop = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ y, liminf (fun j => g j y) atTop ≤ liminf (fun j => ∫⁻ y, g j y) atTop :=
          lintegral_liminf_le hgm
      _ ≤ liminf (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) atTop :=
          liminf_le_liminf (Eventually.of_forall hgint)
      _ = 0 := hr.liminf_eq
  have hae : ∀ᵐ y ∂(volume : Measure (Rn m)), liminf (fun j => g j y) atTop = 0 := by
    filter_upwards [(lintegral_eq_zero_iff (Measurable.liminf hgm)).1 hfatou] with y hy
    simpa using hy
  filter_upwards [hae] with y hy
  -- The covers `Tⱼᵢ ∩ (S ∩ G⁻¹{y})` of the slice: an empty piece contributes `0ᵏ = 0`, and a
  -- nonempty one forces `y ∈ G(Tⱼᵢ ∩ S) ⊆ Aⱼᵢ`.
  have hH : μH[(k : ℝ)] (S ∩ G ⁻¹' {y}) ≤ liminf (fun j => g j y) atTop := by
    calc μH[(k : ℝ)] (S ∩ G ⁻¹' {y})
        ≤ liminf (fun j => ∑' i, Metric.ediam (T j i ∩ (S ∩ G ⁻¹' {y})) ^ (k : ℝ)) atTop :=
          Measure.hausdorffMeasure_le_liminf_tsum (k : ℝ) (S ∩ G ⁻¹' {y}) _ hr
            (fun j i => T j i ∩ (S ∩ G ⁻¹' {y}))
            (Eventually.of_forall fun j i =>
              (Metric.ediam_mono inter_subset_left).trans (hTdiam j i))
            (Eventually.of_forall fun j u hu => by
              obtain ⟨i, hi⟩ := mem_iUnion.1 (hTcov j hu.1)
              exact mem_iUnion.2 ⟨i, hi, hu⟩)
      _ ≤ liminf (fun j => g j y) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun j => ENNReal.tsum_le_tsum fun i => ?_)
          by_cases hne : (T j i ∩ (S ∩ G ⁻¹' {y})).Nonempty
          · obtain ⟨u, huT, huS, huy⟩ := hne
            have hyA : y ∈ A j i := subset_toMeasurable _ _ ⟨u, ⟨huT, huS⟩, huy⟩
            rw [indicator_of_mem hyA, Pi.one_apply, mul_one, ENNReal.rpow_natCast]
            exact pow_le_pow_left' (Metric.ediam_mono inter_subset_left) k
          · rw [not_nonempty_iff_eq_empty.1 hne, Metric.ediam_empty,
              ENNReal.zero_rpow_of_pos (by exact_mod_cast hk)]
            exact zero_le
  have hμH : μH[(k : ℝ)] (S ∩ G ⁻¹' {y}) = 0 := le_antisymm (hH.trans hy.le) zero_le
  -- `μHE[k] = c_k • μH[k]`.
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hμH, smul_zero]
/-- **Volume of a slab intersected with a ball**: for a unit vector `ν` of `ℝᵐ`,
`Lᵐ{w : |⟨w - c, ν⟩| ≤ r, |w - c| ≤ R} ≤ 2r (2R)^{m-1}`. This is the slab estimate in a direct
covering proof that critical slices are null (Simon Ch. 2, p. 66: the consequence of 6.3 stated
before 6.4, which Simon derives from the co-area formula 6.3, whose proof he defers to [Har79],
[Fed69]). The set is empty if `r < 0` or `R < 0`, and `‖ν‖ = 1` forces `m ≥ 1`. The reflection
`ρ` of `ℝᵐ` in `(ℝ (ν - e₀))ᗮ` maps `ν` to `e₀`, so `w ↦ ρ(w - c)` maps the set into the box
`[-r, r] × [-R, R]^{m-1}`, since `⟨ρ(w - c), e₀⟩ = ⟨w - c, ν⟩` and `|x_i| ≤ |x| = |w - c|`.
Translation, `ρ` and `ofLp` preserve Lebesgue measure, and the box has volume `2r (2R)^{m-1}`. -/
theorem Submission.critSlices_slab_volume_le : ∀ (m : ℕ) (ν c : Rn m) (r R : ℝ), ‖ν‖ = 1 → volume {w : Rn m | |inner ℝ (w - c) ν| ≤ r ∧ ‖w - c‖ ≤ R} ≤ ENNReal.ofReal (2 * r * (2 * R) ^ (m - 1)) := by
  intro m ν c r R hν
  -- Step 1: for `r < 0` or `R < 0` the set is empty.
  by_cases hr : r < 0
  · have hempty : {w : Rn m | |inner ℝ (w - c) ν| ≤ r ∧ ‖w - c‖ ≤ R} = ∅ := by
      ext w
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h
      exact absurd ((abs_nonneg _).trans h) (not_le.2 hr)
    rw [hempty, measure_empty]
    positivity
  by_cases hR : R < 0
  · have hempty : {w : Rn m | |inner ℝ (w - c) ν| ≤ r ∧ ‖w - c‖ ≤ R} = ∅ := by
      ext w
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro _ h
      exact absurd ((norm_nonneg _).trans h) (not_le.2 hR)
    rw [hempty, measure_empty]
    positivity
  push Not at hr hR
  -- Step 2: `‖ν‖ = 1` rules out `m = 0`.
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
    rcases m with _ | m'
    · exfalso
      have h0 : ν = 0 := Subsingleton.elim _ _
      rw [h0, norm_zero] at hν
      exact zero_ne_one hν
    · exact ⟨m', rfl⟩
  -- Step 3: the reflection `ρ` in `(ℝ (ν - e₀))ᗮ` satisfies `ρ ν = e₀`.
  set e₀ : Rn (m' + 1) := EuclideanSpace.single 0 1 with he₀
  have he₀n : ‖e₀‖ = 1 := by simp [he₀]
  set ρ : Rn (m' + 1) ≃ₗᵢ[ℝ] Rn (m' + 1) := (ℝ ∙ (ν - e₀))ᗮ.reflection with hρ
  have hρν : ρ ν = e₀ := Submodule.reflection_sub (hν.trans he₀n.symm)
  -- Step 4: `w ↦ ofLp (ρ (w - c))` maps the set into the box `Icc a b`.
  set a : Fin (m' + 1) → ℝ := fun i ↦ if i = 0 then -r else -R with ha
  set b : Fin (m' + 1) → ℝ := fun i ↦ if i = 0 then r else R with hb
  have hsub : {w : Rn (m' + 1) | |inner ℝ (w - c) ν| ≤ r ∧ ‖w - c‖ ≤ R} ⊆
      (WithLp.ofLp ∘ ρ ∘ fun w ↦ w - c) ⁻¹' Icc a b := by
    intro w hw
    obtain ⟨h1, h2⟩ := hw
    simp only [mem_preimage, Function.comp_apply, mem_Icc]
    set x := ρ (w - c) with hx
    have hx0 : x.ofLp 0 = inner ℝ (w - c) ν := by
      have h : inner ℝ x e₀ = x.ofLp 0 := by
        rw [he₀, EuclideanSpace.inner_single_right]
        simp
      rw [← h, ← hρν, hx, LinearIsometryEquiv.inner_map_map]
    have hxn : ‖x‖ = ‖w - c‖ := LinearIsometryEquiv.norm_map _ _
    have hcoord : ∀ i, |x.ofLp i| ≤ R := by
      intro i
      have := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at this
      exact this.trans (hxn ▸ h2)
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · by_cases hi : i = 0
      · subst hi
        simp only [ha, ite_true]
        rw [hx0]
        exact (abs_le.1 h1).1
      · simp only [ha, hi, ite_false]
        exact (abs_le.1 (hcoord i)).1
    · by_cases hi : i = 0
      · subst hi
        simp only [hb, ite_true]
        rw [hx0]
        exact (abs_le.1 h1).2
      · simp only [hb, hi, ite_false]
        exact (abs_le.1 (hcoord i)).2
  -- Step 5: translation, `ρ` and `ofLp` preserve Lebesgue measure.
  have hmp : MeasurePreserving (WithLp.ofLp ∘ ρ ∘ fun w : Rn (m' + 1) ↦ w - c) volume volume :=
    (PiLp.volume_preserving_ofLp (Fin (m' + 1))).comp
      (ρ.measurePreserving.comp (measurePreserving_sub_right volume c))
  -- Steps 6–7: the box has volume `2r (2R)^{m'}`; conclude by monotonicity.
  calc volume {w : Rn (m' + 1) | |inner ℝ (w - c) ν| ≤ r ∧ ‖w - c‖ ≤ R}
      ≤ volume ((WithLp.ofLp ∘ ρ ∘ fun w ↦ w - c) ⁻¹' Icc a b) := measure_mono hsub
    _ = volume (Icc a b) := hmp.measure_preimage measurableSet_Icc.nullMeasurableSet
    _ = ∏ i, ENNReal.ofReal (b i - a i) := Real.volume_Icc_pi
    _ = ENNReal.ofReal (2 * r * (2 * R) ^ (m' + 1 - 1)) := by
      rw [Fin.prod_univ_succ]
      simp only [ha, hb, ite_true, Fin.succ_ne_zero, ite_false, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
      rw [ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_pow (by linarith)]
      congr 2 <;> ring

/-- **Images under a nearly degenerate derivative lie in a thin slab.** This is the step "the
image of a critical subcube lies in a thin slab" of the covering proof that critical slices are
null (Simon Ch. 2, p. 66, the consequence of 6.3, `chapter-02.txt` lines 1476–1478; Simon gives
no proof). Here it is stated for a convex `S` of radius `d` about `u₀`. Since `P` is not
surjective, some unit `ν` is orthogonal to `range P`. The mean value inequality for `G - P` gives
`G(u) - G(u₀) = P(u - u₀) + e` with `|e| ≤ εd`. Hence `G(S)` lies in
`{w : |⟨w - G(u₀), ν⟩| ≤ εd, |w - G(u₀)| ≤ (Λ + ε)d}`, whose volume is bounded by
`Submission.critSlices_slab_volume_le`. -/
theorem Submission.critSlices_image_volume_le_of_fderiv_near : ∀ (n m : ℕ) (G : Rn n → Rn m)
    (S : Set (Rn n)) (P : Rn n →L[ℝ] Rn m) (u₀ : Rn n) (d ε Λ : ℝ), Convex ℝ S → u₀ ∈ S →
    (∀ v ∈ S, DifferentiableAt ℝ G v) → (∀ v ∈ S, ‖fderiv ℝ G v - P‖ ≤ ε) →
    (∀ v ∈ S, ‖v - u₀‖ ≤ d) → ¬ Function.Surjective P → ‖P‖ ≤ Λ →
    volume (G '' S) ≤ ENNReal.ofReal (2 * (ε * d) * (2 * ((Λ + ε) * d)) ^ (m - 1)) := by
  intro n m G S P u₀ d ε Λ hS hu₀ hdiff hnear hd hP hΛ
  -- `u₀ ∈ S` gives `ε ≥ ‖DG(u₀) - P‖ ≥ 0`.
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hnear u₀ hu₀)
  -- A unit normal `ν` to the proper subspace `range P`: `(range P)ᗮ ≠ 0` as `range P ≠ ℝᵐ`.
  obtain ⟨ν, hν, hPν⟩ : ∃ ν : Rn m, ‖ν‖ = 1 ∧ ∀ x, inner ℝ (P x) ν = 0 := by
    have hV : LinearMap.range (P : Rn n →ₗ[ℝ] Rn m) ≠ ⊤ := fun h ↦
      hP fun y ↦ LinearMap.mem_range.1 (h ▸ Submodule.mem_top)
    obtain ⟨ν₀, hν₀, hν₀0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (mt Submodule.orthogonal_eq_bot_iff.1 hV)
    refine ⟨‖ν₀‖⁻¹ • ν₀, ?_, fun x ↦ ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hν₀0)]
    · have h0 : inner ℝ (P x) ν₀ = 0 :=
        (Submodule.mem_orthogonal _ _).1 hν₀ (P x) (LinearMap.mem_range_self _ x)
      rw [inner_smul_right, h0, mul_zero]
  -- `G(S)` lies in the slab of half-width `εd` normal to `ν`, cut off by the closed ball of
  -- radius `(Λ + ε)d`, both about `G(u₀)`.
  have hsub : G '' S ⊆
      {w : Rn m | |inner ℝ (w - G u₀) ν| ≤ ε * d ∧ ‖w - G u₀‖ ≤ (Λ + ε) * d} := by
    rintro _ ⟨u, hu, rfl⟩
    -- Mean value inequality for `G - P` on the convex `S`: `|e| ≤ ε|u - u₀| ≤ εd`.
    set e := G u - G u₀ - P (u - u₀) with he_def
    have he : ‖e‖ ≤ ε * d :=
      (hS.norm_image_sub_le_of_norm_fderiv_le' hdiff hnear hu₀ hu).trans
        (mul_le_mul_of_nonneg_left (hd u hu) hε)
    have hw : G u - G u₀ = P (u - u₀) + e := by
      rw [he_def]
      abel
    refine ⟨?_, ?_⟩
    · -- `⟨w, ν⟩ = ⟨e, ν⟩` because `ν ⊥ range P`; then Cauchy–Schwarz.
      rw [hw, inner_add_left, hPν, zero_add]
      calc |inner ℝ e ν| ≤ ‖e‖ * ‖ν‖ := abs_real_inner_le_norm e ν
        _ = ‖e‖ := by rw [hν, mul_one]
        _ ≤ ε * d := he
    · -- `|w| ≤ ‖P‖ |u - u₀| + |e| ≤ Λd + εd`.
      rw [hw]
      calc ‖P (u - u₀) + e‖ ≤ ‖P (u - u₀)‖ + ‖e‖ := norm_add_le _ _
        _ ≤ Λ * d + ε * d := add_le_add ((P.le_opNorm _).trans
            (mul_le_mul hΛ (hd u hu) (norm_nonneg _) ((norm_nonneg _).trans hΛ))) he
        _ = (Λ + ε) * d := by ring
  calc volume (G '' S)
      ≤ volume {w : Rn m | |inner ℝ (w - G u₀) ν| ≤ ε * d ∧ ‖w - G u₀‖ ≤ (Λ + ε) * d} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (2 * (ε * d) * (2 * ((Λ + ε) * d)) ^ (m - 1)) :=
        Submission.critSlices_slab_volume_le m ν (G u₀) (ε * d) ((Λ + ε) * d) hν
/-- **Subdivision of `[-R, R]ⁿ` into `Mⁿ` subcubes**: for `M > 0` and `R ≥ 0`, with side
`s = 2R/M`, the closed cubes `Q_α = {u : -R + s αᵢ ≤ uᵢ ≤ -R + s (αᵢ + 1) for all i}`,
`α : Fin n → Fin M`, are convex, lie in `closedBall 0 (√n R)`, have diameter at most `√n s` and
cover `closedBall 0 R`. This is the cube subdivision in the covering proof that critical slices
are null (Simon Ch. 2, p. 66, the consequence of (6.3) stated before 6.4). The defining
inequalities are preserved by convex combinations. Every coordinate of a point of `Q_α` lies in
`[-R, R]`, and two points of `Q_α` differ by at most `s` in every coordinate, which gives the two
norm bounds. A point `u` of `closedBall 0 R` has `|uᵢ| ≤ R`; it lies in `Q_α` for `α ≡ 0` if
`R = 0`, and for `αᵢ = min ⌊(uᵢ + R)/s⌋₊ (M - 1)` if `R > 0`. -/
theorem Submission.critSlices_cube_cover : ∀ (n M : ℕ) (R : ℝ), 0 < M → 0 ≤ R → ∃ Q : (Fin n → Fin M) → Set (Rn n), (∀ α, Convex ℝ (Q α)) ∧ (∀ α, Q α ⊆ Metric.closedBall 0 (Real.sqrt n * R)) ∧ (∀ α, ∀ u ∈ Q α, ∀ v ∈ Q α, dist u v ≤ Real.sqrt n * (2 * R / M)) ∧ Metric.closedBall (0 : Rn n) R ⊆ ⋃ α, Q α := by
  intro n M R hM hR
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
  -- The side length `s = 2R/M`, so `s ≥ 0` and `s M = 2R`.
  set s : ℝ := 2 * R / M with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hM'.le
  have hsM : s * M = 2 * R := div_mul_cancel₀ _ hM'.ne'
  refine ⟨fun α ↦ {u : Rn n | ∀ i, -R + s * (α i : ℕ) ≤ u i ∧ u i ≤ -R + s * ((α i : ℕ) + 1)},
    ?_, ?_, ?_, ?_⟩
  -- Step 1: the defining inequalities are preserved by convex combinations.
  · intro α u hu v hv a b ha hb hab i
    obtain ⟨hu1, hu2⟩ := hu i
    obtain ⟨hv1, hv2⟩ := hv i
    obtain rfl : b = 1 - a := by linarith
    have hcomb : (a • u + (1 - a) • v) i = a * u i + (1 - a) * v i := rfl
    rw [hcomb]
    constructor
    · linarith [mul_le_mul_of_nonneg_left hu1 ha, mul_le_mul_of_nonneg_left hv1 hb]
    · linarith [mul_le_mul_of_nonneg_left hu2 ha, mul_le_mul_of_nonneg_left hv2 hb]
  -- Step 2: the coordinates of a point of `Q α` lie in `[-R, R]`, so its norm is at most `√n R`.
  · intro α u hu
    have hcoord : ∀ i, ‖u i‖ ≤ R := by
      intro i
      obtain ⟨h1, h2⟩ := hu i
      have hα0 : (0 : ℝ) ≤ (α i : ℕ) := Nat.cast_nonneg _
      have hαM : ((α i : ℕ) : ℝ) + 1 ≤ M := by exact_mod_cast (α i).isLt
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [mul_nonneg hs0 hα0]
      · linarith [mul_le_mul_of_nonneg_left hαM hs0]
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    calc √(∑ i, ‖u i‖ ^ 2) ≤ √(∑ _i : Fin n, R ^ 2) := by
          gcongr with i
          exact hcoord i
      _ = √n * R := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hR]
  -- Step 3: two points of `Q α` differ by at most `s` in every coordinate.
  · intro α u hu v hv
    have hcoord : ∀ i, dist (u i) (v i) ≤ s := by
      intro i
      obtain ⟨hu1, hu2⟩ := hu i
      obtain ⟨hv1, hv2⟩ := hv i
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith
    rw [EuclideanSpace.dist_eq]
    calc √(∑ i, dist (u i) (v i) ^ 2) ≤ √(∑ _i : Fin n, s ^ 2) := by
          gcongr with i
          exact hcoord i
      _ = √n * s := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hs0]
  -- Step 4: every point of `closedBall 0 R` lies in some `Q α`.
  · intro u hu
    rw [mem_closedBall_zero_iff] at hu
    have hcoord : ∀ i, |u i| ≤ R := fun i ↦ by
      have h := PiLp.norm_apply_le u i
      rw [Real.norm_eq_abs] at h
      exact h.trans hu
    rcases hR.eq_or_lt with rfl | hRpos
    · -- `R = 0`: all coordinates vanish and `s = 0`; take `α ≡ 0`.
      refine mem_iUnion.2 ⟨fun _ ↦ ⟨0, hM⟩, fun i ↦ ?_⟩
      have hui : u i = 0 := abs_nonpos_iff.1 (hcoord i)
      have hs00 : s = 0 := by rw [hs]; simp
      simp [hui, hs00]
    · -- `R > 0`: `αᵢ = min ⌊tᵢ⌋₊ (M - 1)` with `tᵢ = (uᵢ + R)/s ∈ [0, M]`.
      have hspos : 0 < s := div_pos (by linarith) hM'
      obtain ⟨t, ht⟩ : ∃ t : Fin n → ℝ, ∀ i, t i = (u i + R) / s := ⟨_, fun _ ↦ rfl⟩
      have ht0 : ∀ i, 0 ≤ t i := fun i ↦ by
        rw [ht i]
        exact div_nonneg (by linarith [(abs_le.1 (hcoord i)).1]) hs0
      have htM : ∀ i, t i ≤ M := fun i ↦ by
        rw [ht i, div_le_iff₀ hspos]
        linarith [(abs_le.1 (hcoord i)).2]
      have hk : ∀ i, ((min ⌊t i⌋₊ (M - 1) : ℕ) : ℝ) ≤ t i ∧
          t i ≤ ((min ⌊t i⌋₊ (M - 1) : ℕ) : ℝ) + 1 := by
        intro i
        refine ⟨(Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le (ht0 i)), ?_⟩
        rcases le_total ⌊t i⌋₊ (M - 1) with hle | hle
        · rw [min_eq_left hle]
          exact (Nat.lt_floor_add_one (t i)).le
        · rw [min_eq_right hle, Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hM.ne'), Nat.cast_one,
            sub_add_cancel]
          exact htM i
      refine mem_iUnion.2 ⟨fun i ↦ ⟨min ⌊t i⌋₊ (M - 1), by omega⟩, fun i ↦ ?_⟩
      obtain ⟨hk1, hk2⟩ := hk i
      have hut : u i = -R + s * t i := by
        rw [ht i, mul_div_cancel₀ _ hspos.ne']
        ring
      show -R + s * ((min ⌊t i⌋₊ (M - 1) : ℕ) : ℝ) ≤ u i ∧
        u i ≤ -R + s * (((min ⌊t i⌋₊ (M - 1) : ℕ) : ℝ) + 1)
      rw [hut]
      exact ⟨by linarith [mul_le_mul_of_nonneg_left hk1 hs0],
        by linarith [mul_le_mul_of_nonneg_left hk2 hs0]⟩

/-- **`C¹` critical slices are `Hᵏ`-null** (Simon Ch. 2, p. 66: the consequence of the co-area
formula 6.3 stated before Theorem 6.4, `chapter-02.txt` lines 1476–1478, whose proof Simon leaves
to [Har79]/[Fed69]). Let `G : ℝ^{m+k} → ℝᵐ` be `C¹`, `k > 0` and `C = {u : DG(u) not surjective}`.
Then `Hᵏ(C ∩ G⁻¹{y}) = 0` for `Lᵐ`-a.e. `y`. If `m = 0` then `C = ∅`. Otherwise, by the fine-cover
criterion, it suffices to treat `C ∩ B̄_R` for `R ∈ ℕ`. Given `ε > 0`, let `Λ` bound `‖DG‖` on
`K = B̄_{√n R}` (`n = m + k`), let `η > 0` be small and `δ > 0` such that
`‖DG(v) - DG(v')‖ ≤ η` for `v, v' ∈ K` with `|v - v'| ≤ δ`, and subdivide `[-R, R]ⁿ` into `Mⁿ`
convex cubes `Q` of diameter `d ≤ min(δ, ε)`. If `Q` meets `C` at `u₀`, then `G(Q)` lies in a slab
normal to `range DG(u₀)`, so `Lᵐ(G(Q)) ≤ 2ηd (2(Λ + η)d)^{m-1}`. As `Md = 2√n R`, the cover has
`Σ_Q (diam Q)ᵏ Lᵐ(G(Q ∩ C)) ≤ (2√n R)ⁿ 2ᵐ (Λ + 1)^{m-1} η ≤ ε`. -/
theorem Submission.c1_critical_slices_null : ∀ (m k : ℕ) (G : Rn (m + k) → Rn m), 0 < k →
    ContDiff ℝ 1 G → ∀ᵐ y ∂(volume : Measure (Rn m)),
      μHE[k] ({u | ¬ Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y}) = 0 := by
  intro m k G hk hG
  -- `m = 0`: every linear map into `ℝ⁰` is surjective, so the critical set is empty.
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hC : {u : Rn (0 + k) | ¬ Function.Surjective (fderiv ℝ G u)} = ∅ := by
      ext u
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_not]
      exact fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
    filter_upwards with y
    simp [hC]
  set C := {u : Rn (m + k) | ¬ Function.Surjective (fderiv ℝ G u)} with hCdef
  have hdiff : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  -- `m ≥ 1`: by the fine-cover criterion, each `C ∩ B̄_R` (`R ∈ ℕ`) has `Hᵏ`-null slices over
  -- `Lᵐ`-a.e. `y`.
  have key : ∀ R : ℕ, ∀ᵐ y ∂(volume : Measure (Rn m)),
      μHE[k] ((C ∩ Metric.closedBall 0 (R : ℝ)) ∩ G ⁻¹' {y}) = 0 := by
    intro R
    refine Submission.critSlices_ae_slice_null_of_covers (m + k) m k
      (C ∩ Metric.closedBall 0 (R : ℝ)) G hk fun ε hε ↦ ?_
    -- Constants: `0 < e` with `e ≤ ε`; a bound `Λ ≥ 0` of `‖DG‖` on the compact `K = B̄_{√n R}`;
    -- the tolerance `η ∈ (0, 1]` with `A₀ η ≤ e`; the modulus `δ > 0` of uniform continuity of
    -- `DG` on `K` for `η`; and `M ∈ ℕ` with cube diameter `d = √n (2R / M) ≤ min(δ, e)`.
    obtain ⟨e, he0, he⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e ≤ ε := by
      obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
      exact ⟨r, ENNReal.ofReal_pos.1 hr, hrε.le⟩
    set K := Metric.closedBall (0 : Rn (m + k)) (Real.sqrt ((m + k : ℕ) : ℝ) * R) with hKdef
    have hK : IsCompact K := isCompact_closedBall _ _
    obtain ⟨Λ₀, hΛ₀⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    set Λ : ℝ := max Λ₀ 0 with hΛdef
    have hΛ : ∀ x ∈ K, ‖fderiv ℝ G x‖ ≤ Λ := fun x hx ↦ (hΛ₀ x hx).trans (le_max_left _ _)
    have hΛ0 : 0 ≤ Λ := le_max_right _ _
    set A₀ : ℝ := (2 * Real.sqrt ((m + k : ℕ) : ℝ) * R) ^ (m + k) * 2 ^ m * (Λ + 1) ^ (m - 1)
      with hA₀def
    have hA₀ : 0 ≤ A₀ := by positivity
    set η : ℝ := min 1 (e / (A₀ + 1)) with hηdef
    have hη0 : 0 < η := lt_min one_pos (div_pos he0 (by linarith))
    have hη1 : η ≤ 1 := min_le_left _ _
    have hηA : A₀ * η ≤ e := by
      have h1 : A₀ * η ≤ A₀ * (e / (A₀ + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hA₀
      have h2 : A₀ * (e / (A₀ + 1)) ≤ e := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff_le.1
      (hK.uniformContinuousOn_of_continuous hcont.continuousOn) η hη0
    set ρ : ℝ := min δ e with hρdef
    have hρ0 : 0 < ρ := lt_min hδ0 he0
    obtain ⟨M, hM⟩ := exists_nat_gt (2 * Real.sqrt ((m + k : ℕ) : ℝ) * R / ρ)
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    have hMpos' : (0 : ℝ) < M := lt_of_le_of_lt (by positivity) hM
    have hMpos : 0 < M := by exact_mod_cast hMpos'
    set d : ℝ := Real.sqrt ((m + k : ℕ) : ℝ) * (2 * R / M) with hddef
    have hd0 : 0 ≤ d := by positivity
    have hdρ : d ≤ ρ := by
      have h := (div_lt_iff₀ hρ0).1 hM
      rw [hddef, mul_div_assoc', div_le_iff₀ hMpos']
      nlinarith
    have hdδ : d ≤ δ := hdρ.trans (min_le_left _ _)
    have hde : d ≤ e := hdρ.trans (min_le_right _ _)
    -- The cover: the `Mⁿ` convex cubes `Q α ⊆ K` of diameter `≤ d ≤ ε` covering `B̄_R`.
    obtain ⟨Q, hQconv, hQK, hQdiam, hQcov⟩ :=
      Submission.critSlices_cube_cover (m + k) M R hMpos hR0
    have hdiamQ : ∀ α, Metric.ediam (Q α) ≤ ENNReal.ofReal d := fun α ↦
      Metric.ediam_le fun u hu v hv ↦ by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (hQdiam α u hu v hv)
    refine ⟨Fin (m + k) → Fin M, inferInstance, Q, inter_subset_right.trans hQcov,
      fun α ↦ (hdiamQ α).trans ((ENNReal.ofReal_le_ofReal hde).trans he), ?_⟩
    rw [tsum_fintype]
    -- A cube `Q α` meeting `C` at `u₀`: `‖DG(v) - DG(u₀)‖ ≤ η` and `|v - u₀| ≤ d` on `Q α`, and
    -- `DG(u₀)` is not surjective, so `Lᵐ(G(Q α)) ≤ 2ηd (2(Λ + η)d)^{m-1}`.
    have hterm : ∀ α, Metric.ediam (Q α) ^ k *
        volume (G '' (Q α ∩ (C ∩ Metric.closedBall 0 (R : ℝ)))) ≤
        ENNReal.ofReal (d ^ k * (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m - 1))) := by
      intro α
      by_cases hne : (Q α ∩ (C ∩ Metric.closedBall 0 (R : ℝ))).Nonempty
      · obtain ⟨u₀, hu₀Q, hu₀C, -⟩ := hne
        have hu₀K : u₀ ∈ K := hQK α hu₀Q
        have hvol := Submission.critSlices_image_volume_le_of_fderiv_near (m + k) m G (Q α)
          (fderiv ℝ G u₀) u₀ d η Λ (hQconv α) hu₀Q (fun v _ ↦ hdiff v)
          (fun v hv ↦ by
            have h := hδ v (hQK α hv) u₀ hu₀K ((hQdiam α v hv u₀ hu₀Q).trans hdδ)
            rwa [dist_eq_norm] at h)
          (fun v hv ↦ by
            rw [← dist_eq_norm]
            exact hQdiam α v hv u₀ hu₀Q)
          hu₀C (hΛ u₀ hu₀K)
        calc Metric.ediam (Q α) ^ k * volume (G '' (Q α ∩ (C ∩ Metric.closedBall 0 (R : ℝ))))
            ≤ ENNReal.ofReal d ^ k * volume (G '' Q α) :=
              mul_le_mul' (pow_le_pow_left' (hdiamQ α) k)
                (measure_mono (image_mono inter_subset_left))
          _ ≤ ENNReal.ofReal d ^ k *
              ENNReal.ofReal (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m - 1)) :=
              mul_le_mul' le_rfl hvol
          _ = ENNReal.ofReal (d ^ k * (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m - 1))) := by
              rw [ENNReal.ofReal_mul (pow_nonneg hd0 k), ENNReal.ofReal_pow hd0]
      · rw [not_nonempty_iff_eq_empty.1 hne, image_empty, measure_empty, mul_zero]
        positivity
    -- Summing over the `Mⁿ` cubes: `Md = 2√n R`, `n = m + k`, `m ≥ 1` and `η ≤ 1` give
    -- `Σ ≤ (2√n R)ⁿ 2ᵐ (Λ + η)^{m-1} η ≤ A₀ η ≤ e ≤ ε`.
    calc ∑ α, Metric.ediam (Q α) ^ k * volume (G '' (Q α ∩ (C ∩ Metric.closedBall 0 (R : ℝ))))
        ≤ ∑ _α : Fin (m + k) → Fin M,
            ENNReal.ofReal (d ^ k * (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m - 1))) :=
          Finset.sum_le_sum fun α _ ↦ hterm α
      _ = ENNReal.ofReal ((M : ℝ) ^ (m + k) *
            (d ^ k * (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m - 1)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (M : ℝ) ^ (m + k)),
            ← Nat.cast_pow, ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal e := by
          apply ENNReal.ofReal_le_ofReal
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
          have hMd : (M : ℝ) * d = 2 * Real.sqrt ((m' + 1 + k : ℕ) : ℝ) * R := by
            rw [hddef]
            field_simp
          have hpow : (Λ + η) ^ (m' + 1 - 1) ≤ (Λ + 1) ^ (m' + 1 - 1) :=
            pow_le_pow_left₀ (by linarith) (by linarith) _
          have hid : (M : ℝ) ^ (m' + 1 + k) *
              (d ^ k * (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m' + 1 - 1))) =
              ((M : ℝ) * d) ^ (m' + 1 + k) * 2 ^ (m' + 1) * (Λ + η) ^ (m' + 1 - 1) * η := by
            simp only [Nat.add_sub_cancel, mul_pow]
            ring
          rw [hid, hMd]
          calc (2 * Real.sqrt ((m' + 1 + k : ℕ) : ℝ) * R) ^ (m' + 1 + k) * 2 ^ (m' + 1) *
                (Λ + η) ^ (m' + 1 - 1) * η
              ≤ (2 * Real.sqrt ((m' + 1 + k : ℕ) : ℝ) * R) ^ (m' + 1 + k) * 2 ^ (m' + 1) *
                (Λ + 1) ^ (m' + 1 - 1) * η := by gcongr
            _ = A₀ * η := by rw [hA₀def]
            _ ≤ e := hηA
      _ ≤ ε := he
  -- `C ∩ G⁻¹{y} ⊆ ⋃_R (C ∩ B̄_R) ∩ G⁻¹{y}`, a countable union of `Hᵏ`-null sets for a.e. `y`.
  filter_upwards [ae_all_iff.2 key] with y hy
  refine measure_mono_null (fun u hu ↦ ?_) (measure_iUnion_null hy)
  obtain ⟨R, hR⟩ := exists_nat_ge ‖u‖
  exact mem_iUnion.2 ⟨R, ⟨hu.1, mem_closedBall_zero_iff.2 hR⟩, hu.2⟩

/-- **Level slices of a `C¹` map have countably `k`-rectifiable `C¹` images for `Lᵐ`-a.e. value**
(Simon Ch. 3, Remark 2.10(2), `chapter-03.txt` lines 439–442, via the `C¹` Sard-type Ch. 2,
Theorem 6.4, `chapter-02.txt` lines 1476–1497). With `C = {u | DG(u) not onto}`,
`ψ(D ∩ G⁻¹{y})` is the union of the regular part `ψ(D ∖ C ∩ G⁻¹{y})`, countably
`k`-rectifiable for every `y` (implicit function charts), and the critical part
`ψ(D ∩ C ∩ G⁻¹{y})`. For `Lᵐ`-a.e. `y`, `Hᵏ(C ∩ G⁻¹{y}) = 0`, and `ψ`, locally Lipschitz on `D`,
keeps it `Hᵏ`-null; an `Hᵏ`-null set is countably `k`-rectifiable. -/
theorem Submission.c1_level_slices_countablyRectifiable : ∀ (m k N : ℕ) (D : Set (Rn (m + k))) (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m), 0 < k → IsOpen D → ContDiffOn ℝ 1 ψ D → ContDiff ℝ 1 G → ∀ᵐ y ∂(volume : Measure (Rn m)), CountablyRectifiable k (ψ '' (D ∩ G ⁻¹' {y})) := by
  intro m k N D ψ G hk hD hψ hG
  -- The critical slices are `Hᵏ`-null for `Lᵐ`-a.e. `y`.
  filter_upwards [Submission.c1_critical_slices_null m k G hk hG] with y hy
  -- Split the slice into its regular part and its critical part.
  have hsplit : ψ '' (D ∩ G ⁻¹' {y}) ⊆
      ⋃₀ {ψ '' (D ∩ {u | Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y}),
        ψ '' (D ∩ ({u | ¬ Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y}))} := by
    rw [sUnion_pair]
    rintro _ ⟨u, ⟨huD, huy⟩, rfl⟩
    by_cases hu : Function.Surjective (fderiv ℝ G u)
    · exact Or.inl ⟨u, ⟨⟨huD, hu⟩, huy⟩, rfl⟩
    · exact Or.inr ⟨u, ⟨huD, hu, huy⟩, rfl⟩
  refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion
    ((countable_singleton _).insert _) ?_).mono hsplit
  rintro S (rfl | rfl)
  -- Regular part: countably `k`-rectifiable for every `y` (implicit function charts).
  · exact Submission.c1_regular_level_slice_image_countablyRectifiable m k N D ψ G y hD hψ hG
  -- Critical part: `ψ`, locally Lipschitz on `D`, keeps it `Hᵏ`-null.
  · exact Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero
      (Submission.contDiffOn_image_euclideanHausdorff_null (m + k) N k D _ ψ hD hψ
        inter_subset_left (measure_mono_null inter_subset_right hy))

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
