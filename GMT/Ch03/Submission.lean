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

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
