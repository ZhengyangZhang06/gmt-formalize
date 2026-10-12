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

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
