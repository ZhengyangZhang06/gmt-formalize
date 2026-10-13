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

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
