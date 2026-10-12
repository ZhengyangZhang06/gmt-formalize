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

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
