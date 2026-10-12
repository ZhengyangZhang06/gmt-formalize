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

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
