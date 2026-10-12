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

/-- **Simon Ch. 3, Lemma 3.2 (p. 78)** (`chapter-03.txt` lines 449–469). The pieces `Aⱼ` of
`A = ⋃ⱼ Aⱼ` cover `A` with `Hⁿ(Aⱼ) < ∞`, so SimonGMT's `simon_lemma_3_2` applies with `S := Aj`.
Its first part is the decomposition; its Borel-choice part also gives `NullMeasurableSet P`,
which is dropped. -/
theorem Submission.section3_rectifiableDecomposition : RectifiableDecomposition := by
  rintro n ℓ A ⟨Aj, hA, hfin⟩
  obtain ⟨hdecomp, hborel⟩ := Poincare.SimonGMT.Chapter03.simon_lemma_3_2 Aj hA.subset hfin
  refine ⟨hdecomp, fun hAmeas ↦ ?_⟩
  obtain ⟨R, P, hRP, hdisj, hR, -, hRrect, hPpure⟩ := hborel hAmeas
  exact ⟨R, P, hRP, hdisj, hR, hRrect, hPpure⟩
/-- **`C¹` maps send `Lⁿ`-null sets to `Hⁿ`-null sets**: the measure step in Simon Ch. 3,
proof of Lemma 3.3 (p. 79, `chapter-03.txt` lines 495–496: a `C¹` diffeomorphism `p` gives
`Hⁿ(p(S ∩ N ∩ B_σ(x))) > 0`). Each `u ∈ T ⊆ V` has a neighbourhood `t` on which `ψ` is
`K`-Lipschitz, since `ψ` is `C¹` near `u` and hence strictly differentiable at `u`. As
`Hⁿ = c • μH[n]` with one constant `c` on every space and `Hⁿ = Lⁿ` on `ℝⁿ`,
`Hⁿ(ψ(T ∩ t)) ≤ Kⁿ Hⁿ(T ∩ t) = Kⁿ Lⁿ(T ∩ t) = 0`. By second countability
(`measure_null_of_locally_null` for the outer measure `B ↦ Hⁿ(ψ(B))`), `Hⁿ(ψ(T)) = 0`. -/
theorem Submission.section3_contDiffOn_image_null_of_volume_null : ∀ (n N : ℕ) (V T : Set (Rn n))
    (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 1 ψ V → T ⊆ V → volume T = 0 →
    μHE[n] (ψ '' T) = 0 := by
  intro n N V T ψ hV hψ hTV hT
  -- `B ↦ Hⁿ(ψ(B))` is an outer measure on `ℝⁿ`; it suffices that it vanishes on a relative
  -- neighbourhood of each point of `T`.
  suffices h : OuterMeasure.comap ψ (μHE[n] : Measure (Rn N)).toOuterMeasure T = 0 by
    simpa using h
  refine measure_null_of_locally_null T fun u hu ↦ ?_
  obtain ⟨K, t, ht, hK⟩ :=
    ((hψ.contDiffAt (hV.mem_nhds (hTV hu))).hasStrictFDerivAt one_ne_zero).exists_lipschitzOnWith
  refine ⟨T ∩ t, inter_mem_nhdsWithin T ht, ?_⟩
  have hvol : (μHE[n] : Measure (Rn n)) (T ∩ t) = 0 := by
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact measure_mono_null inter_subset_left hT
  -- `μHE[n] = c • μH[n]` with the same constant `c` on `ℝⁿ` and on `ℝᴺ`.
  have himg : (μHE[n] : Measure (Rn N)) (ψ '' (T ∩ t)) ≤
      (K : ℝ≥0∞) ^ (n : ℝ) * (μHE[n] : Measure (Rn n)) (T ∩ t) := by
    simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul]
    rw [mul_left_comm]
    gcongr
    exact (hK.mono inter_subset_right).hausdorffMeasure_image_le (Nat.cast_nonneg n)
  rw [hvol, mul_zero] at himg
  simpa using himg
/-- **An injective strict derivative gives a local anti-Lipschitz bound**: the local step of
Simon Ch. 3, proof of Lemma 3.3 (p. 79, `chapter-03.txt` lines 494–496: `p_J` restricted to `N`
near `x` is a `C¹` diffeomorphism), with strict differentiability in place of the inverse function
theorem. As `A` is injective on `ℝⁿ`, `‖v‖ ≤ K₀ ‖A v‖` for some `K₀ > 0`. Near `u₀`,
`‖Φ x - Φ y - A (x - y)‖ ≤ (2K₀)⁻¹ ‖x - y‖`, so the triangle inequality gives
`‖x - y‖ ≤ K₀ ‖Φ x - Φ y‖ + ‖x - y‖ / 2`, i.e. `‖x - y‖ ≤ 2K₀ ‖Φ x - Φ y‖`. -/
theorem Submission.section3_hasStrictFDerivAt_injective_local_antilipschitz : ∀ (n p : ℕ)
    (Φ : Rn n → Rn p) (A : Rn n →L[ℝ] Rn p) (u₀ : Rn n), HasStrictFDerivAt Φ A u₀ →
    Function.Injective A → ∃ s ∈ 𝓝 u₀, ∃ K : ℝ≥0, ∀ x ∈ s, ∀ y ∈ s,
      ‖x - y‖ ≤ K * ‖Φ x - Φ y‖ := by
  intro n p Φ A u₀ hΦ hA
  -- Step 1: `A` is injective on a finite-dimensional space, so `‖v‖ ≤ K₀ ‖A v‖` with `K₀ > 0`.
  obtain ⟨K₀, hK₀, hAK₀⟩ :=
    LinearMap.exists_antilipschitzWith (A : Rn n →ₗ[ℝ] Rn p) (LinearMap.ker_eq_bot.mpr hA)
  have hK₀' : (0 : ℝ) < K₀ := hK₀
  have h1 (v : Rn n) : ‖v‖ ≤ K₀ * ‖A v‖ := by
    simpa [dist_eq_norm] using hAK₀.le_mul_dist v 0
  -- Step 2: on a neighbourhood `s` of `u₀`, `Φ` approximates `A` with constant `(2K₀)⁻¹`.
  obtain ⟨s, hs, hΦs⟩ := hΦ.approximates_deriv_on_nhds (c := (2 * K₀)⁻¹) (Or.inr (by positivity))
  refine ⟨s, hs, 2 * K₀, fun x hx y hy ↦ ?_⟩
  have h2 : ‖Φ x - Φ y - A (x - y)‖ ≤ (2 * K₀ : ℝ)⁻¹ * ‖x - y‖ := by
    exact_mod_cast hΦs x hx y hy
  -- Step 3: the triangle inequality for `A (x - y) = (Φ x - Φ y) - (Φ x - Φ y - A (x - y))`.
  have h3 : ‖A (x - y)‖ ≤ ‖Φ x - Φ y‖ + ‖Φ x - Φ y - A (x - y)‖ := by
    calc ‖A (x - y)‖ = ‖(Φ x - Φ y) - (Φ x - Φ y - A (x - y))‖ := by rw [sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
  -- Steps 4–5: since `K₀ (2K₀)⁻¹ = 1 / 2`, half of `‖x - y‖` is absorbed into the left side.
  have h4 : ‖x - y‖ ≤ K₀ * ‖Φ x - Φ y‖ + ‖x - y‖ / 2 :=
    calc ‖x - y‖ ≤ K₀ * ‖A (x - y)‖ := h1 (x - y)
      _ ≤ K₀ * (‖Φ x - Φ y‖ + (2 * K₀ : ℝ)⁻¹ * ‖x - y‖) := by gcongr; linarith
      _ = K₀ * ‖Φ x - Φ y‖ + ‖x - y‖ / 2 := by field_simp
  push_cast
  linarith
/-- **Anti-Lipschitz maps on subsets of `ℝⁿ` satisfy `Lⁿ(S) ≤ Kⁿ Hⁿ(f(S))`**: step 7 of the
proof of Simon Ch. 3, Lemma 3.3 (p. 79), stated for an arbitrary map `f` and set `S`. The
restriction `g = f|_S` is `K`-anti-Lipschitz on the metric subspace `S`, so
`μH[n]_S(S) ≤ Kⁿ μH[n](g(S)) = Kⁿ μH[n](f(S))`; the isometric inclusion `S ↪ ℝⁿ` gives
`μH[n](S) = μH[n]_S(S)`. Multiplying by the normalising constant of `μHE[n]` and using
`μHE[n] = Lⁿ` on `ℝⁿ` gives the claim. No measurability of `S` or `f` is needed: all estimates
are for outer measures. -/
theorem Submission.section3_antilipschitzOn_volume_le_euclideanHausdorff_image : ∀ (n p : ℕ)
    (f : Rn n → Rn p) (S : Set (Rn n)) (K : ℝ≥0),
    (∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ K * ‖f x - f y‖) →
    volume S ≤ (K : ℝ≥0∞) ^ n * μHE[n] (f '' S) := by
  intro n p f S K hf
  -- Step 2: the restriction `g = f|_S` is `K`-anti-Lipschitz on the metric subspace `S`.
  have hg : AntilipschitzWith K (S.domRestrict f) :=
    AntilipschitzWith.of_le_mul_dist fun a b => by
      simpa only [Subtype.dist_eq, dist_eq_norm, domRestrict_apply] using hf a a.2 b b.2
  -- Step 3: `μH[n]_S(S) ≤ Kⁿ μH[n](g(S))`, and `g(S) = f(S)`.
  have h3 := hg.le_hausdorffMeasure_image (Nat.cast_nonneg n) univ
  rw [image_univ, range_domRestrict, ENNReal.rpow_natCast] at h3
  -- Step 4: the isometric inclusion `S ↪ ℝⁿ` gives `μH[n](S) = μH[n]_S(S)`.
  have h4 := isometry_subtype_coe.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg n))
    (univ : Set S)
  rw [image_univ, Subtype.range_coe] at h4
  -- Steps 5–6: multiply by the normalising constant of `μHE[n]`, and `μHE[n] = Lⁿ` on `ℝⁿ`.
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.euclideanHausdorffMeasure_def,
    Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply, h4,
    ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_left_comm]
  gcongr
/-- **Simon Ch. 3, proof of Lemma 3.3, first claim (pp. 78–79)** (`chapter-03.txt` lines
482–489). An `n`-plane `L ⊆ ℝᴺ` has `n` coordinates `J` with `p_J` injective on `L`. The
restricted coordinate functionals `φⱼ = xⱼ|_L` span `L*`, since a nonzero `x ∈ L` has a nonzero
coordinate. So `n` of them, `φ_{j(1)}, …, φ_{j(n)}`, form a basis of `L*`, and their indices are
distinct; an `x ∈ L` with every `x_{j(i)} = 0` is then `0`. As `x - p_J x ⊥ e_j` for `j ∈ J`,
`p_J` keeps the coordinates in `J`, so `J = {j(1), …, j(n)}` works. This is the dual form of
Simon's nonsingular `n × n` minor. -/
theorem Submission.section3_exists_coordinateProjection_injOn :
    ∀ (N n : ℕ) (L : Submodule ℝ (Rn N)), finrank ℝ L = n →
      ∃ J : Finset (Fin N), J.card = n ∧ Set.InjOn (coordinateProjection J) (L : Set (Rn N)) := by
  intro N n L hL
  -- Step 1: `p_J` keeps the coordinates indexed by `J`, as `x - p_J x ⊥ e_i` for `i ∈ J`.
  have hcoord : ∀ (J : Finset (Fin N)) (x : Rn N), ∀ i ∈ J, coordinateProjection J x i = x i := by
    intro J x i hi
    have hmem : EuclideanSpace.single i (1 : ℝ) ∈
        Submodule.span ℝ ((fun j ↦ EuclideanSpace.single j (1 : ℝ)) '' (J : Set (Fin N))) :=
      Submodule.subset_span ⟨i, hi, rfl⟩
    have h := Submodule.starProjection_inner_eq_zero x _ hmem
    rw [inner_sub_left, EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_right,
      one_mul, one_mul, conj_trivial, conj_trivial, sub_eq_zero] at h
    exact h.symm
  -- Step 2: the coordinate functionals `φⱼ` restricted to `L` span `L*`.
  let φ : Fin N → Module.Dual ℝ L := fun j ↦ (EuclideanSpace.projₗ j).comp L.subtype
  have hspan : Submodule.span ℝ (Set.range φ) = ⊤ := by
    refine Submodule.span_eq_top_of_ne_zero fun z hz ↦ ?_
    obtain ⟨j, hj⟩ : ∃ j, (z : Rn N) j ≠ 0 := by
      by_contra! h
      exact hz (Subtype.ext (PiLp.ext h))
    exact ⟨φ j, Set.mem_range_self j, hj⟩
  -- Step 3: `n` of them, `φ_{j(1)}, …, φ_{j(n)}`, form a basis of `L*`; the `j(i)` are distinct.
  obtain ⟨f, hf_mem, hf_span, hf_indep⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range φ)
  choose j hj using hf_mem
  have hj_inj : Function.Injective j := fun a b hab ↦
    hf_indep.injective (by rw [← hj a, ← hj b, hab])
  have hcard : finrank ℝ (Submodule.span ℝ (Set.range φ)) = n := by
    rw [hspan, finrank_top, Subspace.dual_finrank_eq, hL]
  -- Step 4: a vector of `L` whose selected coordinates vanish is `0`.
  have hzero : ∀ z : L, (∀ i, (z : Rn N) (j i) = 0) → z = 0 := by
    intro z hz
    refine (Module.forall_dual_apply_eq_zero_iff ℝ z).mp fun g ↦ ?_
    have hle : Submodule.span ℝ (Set.range f) ≤ LinearMap.ker (Module.Dual.eval ℝ L z) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply, ← hj i]
      exact hz i
    have hg : g ∈ Submodule.span ℝ (Set.range f) := by
      rw [hf_span, hspan]
      exact Submodule.mem_top
    simpa using hle hg
  -- Step 5: `J = {j(1), …, j(n)}` has `n` elements and `p_J` is injective on `L`.
  refine ⟨Finset.univ.image j, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hj_inj, Finset.card_univ, Fintype.card_fin, hcard]
  · intro x hx y hy hxy
    have hsel : ∀ i, (x - y) (j i) = 0 := fun i ↦ by
      have hi : j i ∈ Finset.univ.image j := Finset.mem_image_of_mem j (Finset.mem_univ i)
      rw [PiLp.sub_apply, ← hcoord _ x (j i) hi, ← hcoord _ y (j i) hi, hxy, sub_self]
    exact sub_eq_zero.mp (congrArg Subtype.val (hzero ⟨x - y, L.sub_mem hx hy⟩ hsel))
/-- **`C¹` maps send `Lⁿ`-null sets to `Hⁿ`-null sets**: the measure step in Simon Ch. 3,
proof of Lemma 3.3 (p. 79, `chapter-03.txt` lines 495–496: a `C¹` diffeomorphism `p` gives
`Hⁿ(p(S ∩ N ∩ B_σ(x))) > 0`). Each `u ∈ T ⊆ V` has a neighbourhood `t` on which `ψ` is
`K`-Lipschitz, since `ψ` is `C¹` near `u` and hence strictly differentiable at `u`. As
`Hⁿ = c • μH[n]` with one constant `c` on every space and `Hⁿ = Lⁿ` on `ℝⁿ`,
`Hⁿ(ψ(T ∩ t)) ≤ Kⁿ Hⁿ(T ∩ t) = Kⁿ Lⁿ(T ∩ t) = 0`. By second countability
(`measure_null_of_locally_null` for the outer measure `B ↦ Hⁿ(ψ(B))`), `Hⁿ(ψ(T)) = 0`. -/
theorem Submission.section3_contDiffOn_image_null_of_volume_null : ∀ (n N : ℕ) (V T : Set (Rn n))
    (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 1 ψ V → T ⊆ V → volume T = 0 →
    μHE[n] (ψ '' T) = 0 := by
  intro n N V T ψ hV hψ hTV hT
  -- `B ↦ Hⁿ(ψ(B))` is an outer measure on `ℝⁿ`; it suffices that it vanishes on a relative
  -- neighbourhood of each point of `T`.
  suffices h : OuterMeasure.comap ψ (μHE[n] : Measure (Rn N)).toOuterMeasure T = 0 by
    simpa using h
  refine measure_null_of_locally_null T fun u hu ↦ ?_
  obtain ⟨K, t, ht, hK⟩ :=
    ((hψ.contDiffAt (hV.mem_nhds (hTV hu))).hasStrictFDerivAt one_ne_zero).exists_lipschitzOnWith
  refine ⟨T ∩ t, inter_mem_nhdsWithin T ht, ?_⟩
  have hvol : (μHE[n] : Measure (Rn n)) (T ∩ t) = 0 := by
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact measure_mono_null inter_subset_left hT
  -- `μHE[n] = c • μH[n]` with the same constant `c` on `ℝⁿ` and on `ℝᴺ`.
  have himg : (μHE[n] : Measure (Rn N)) (ψ '' (T ∩ t)) ≤
      (K : ℝ≥0∞) ^ (n : ℝ) * (μHE[n] : Measure (Rn n)) (T ∩ t) := by
    simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul]
    rw [mul_left_comm]
    gcongr
    exact (hK.mono inter_subset_right).hausdorffMeasure_image_le (Nat.cast_nonneg n)
  rw [hvol, mul_zero] at himg
  simpa using himg

/-- **Simon Ch. 3, proof of Lemma 3.3, positivity step (p. 79)** (`chapter-03.txt` lines
490–496). If `ψ` is `C¹` on an open `V ⊆ ℝⁿ` with `Dψ` injective and `T ⊆ V` has `Lⁿ(T) > 0`,
then `Hⁿ(p_J(ψ(T))) > 0` for some `J` with `#J = n`. Every neighbourhood of some `u₀ ∈ T` meets
`T` in positive measure. Choose `J` with `p_J` injective on the `n`-plane `Dψ(u₀)(ℝⁿ)`, so that
`A = p_J ∘ Dψ(u₀)` is injective. Then `Φ = p_J ∘ ψ` has strict derivative `A` at `u₀`, so it is
`K`-anti-Lipschitz on a neighbourhood `s` of `u₀`. Hence `0 < Lⁿ(T ∩ s) ≤ Kⁿ Hⁿ(Φ(T ∩ s))`, and
`Φ(T ∩ s) ⊆ p_J(ψ(T))`. Strict differentiability replaces Simon's local `C¹` diffeomorphism
(Ch. 2, Remark 4.4). -/
theorem Submission.section3_chart_coordinateProjection_pos :
    ∀ (n ℓ : ℕ) (V T : Set (Rn n)) (ψ : Rn n → Rn (n + ℓ)), IsOpen V → ContDiffOn ℝ 1 ψ V →
      (∀ u ∈ V, Function.Injective (fderiv ℝ ψ u)) → T ⊆ V → 0 < volume T →
        ∃ J : Finset (Fin (n + ℓ)), J.card = n ∧
          0 < μHE[n] (coordinateProjection J '' (ψ '' T)) := by
  intro n ℓ V T ψ hV hψ hDψ hTV hT
  -- Step 1: every neighbourhood of some `u₀ ∈ T` meets `T` in positive measure.
  obtain ⟨u₀, hu₀, hdens⟩ := exists_mem_forall_mem_nhdsWithin_pos_measure hT.ne'
  -- Step 2: `p_J` is injective on the `n`-plane `Dψ(u₀)(ℝⁿ)`, so `A = p_J ∘ Dψ(u₀)` is injective.
  set D := fderiv ℝ ψ u₀
  have hD : Function.Injective D := hDψ u₀ (hTV hu₀)
  obtain ⟨J, hJ, hJinj⟩ := Submission.section3_exists_coordinateProjection_injOn (n + ℓ) n
    (LinearMap.range (D : Rn n →ₗ[ℝ] Rn (n + ℓ)))
    (by rw [LinearMap.finrank_range_of_inj (f := (D : Rn n →ₗ[ℝ] Rn (n + ℓ))) hD,
      finrank_euclideanSpace_fin])
  set A := (coordinateProjection J).comp D
  have hA : Function.Injective A := fun v w hvw ↦
    hD (hJinj (LinearMap.mem_range_self _ v) (LinearMap.mem_range_self _ w) hvw)
  -- Step 3: `Φ = p_J ∘ ψ` is strictly differentiable at `u₀` with derivative `A`.
  have hΦ : HasStrictFDerivAt (coordinateProjection J ∘ ψ) A u₀ :=
    (coordinateProjection J).hasStrictFDerivAt.comp u₀
      ((hψ.contDiffAt (hV.mem_nhds (hTV hu₀))).hasStrictFDerivAt one_ne_zero)
  -- Step 4: `Φ` is `K`-anti-Lipschitz on a neighbourhood `s` of `u₀`.
  obtain ⟨s, hs, K, hK⟩ := Submission.section3_hasStrictFDerivAt_injective_local_antilipschitz
    n (n + ℓ) (coordinateProjection J ∘ ψ) A u₀ hΦ hA
  -- Step 5: `0 < Lⁿ(T ∩ s) ≤ Kⁿ Hⁿ(Φ(T ∩ s))`, so `Hⁿ(Φ(T ∩ s)) ≠ 0`.
  have hbound := Submission.section3_antilipschitzOn_volume_le_euclideanHausdorff_image
    n (n + ℓ) (coordinateProjection J ∘ ψ) (T ∩ s) K fun x hx y hy ↦ hK x hx.2 y hy.2
  have himage : μHE[n] ((coordinateProjection J ∘ ψ) '' (T ∩ s)) ≠ 0 := fun h ↦ by
    rw [h, mul_zero] at hbound
    exact (hdens _ (inter_mem_nhdsWithin T hs)).ne' (nonpos_iff_eq_zero.mp hbound)
  -- Step 6: `Φ(T ∩ s) ⊆ p_J(ψ(T))`, and `Hⁿ` is monotone.
  refine ⟨J, hJ, (pos_iff_ne_zero.mpr himage).trans_le (measure_mono ?_)⟩
  rw [Set.image_comp]
  exact Set.image_mono (Set.image_mono Set.inter_subset_left)

/-- **Simon Ch. 3, Theorem 3.8 (p. 80)** (`chapter-03.txt` lines 540–548), given Theorem 3.6.
Erratum: line 540 "by combining 3.2 and 3.7" should read "3.2 and 3.6". Lemma 3.2 splits
`A = R ∪ P` with `R` countably `n`-rectifiable and `P` purely `n`-unrectifiable. Since
`P = ⋃ⱼ (P ∩ Aⱼ)` with `Hⁿ(P ∩ Aⱼ) ≤ Hⁿ(Aⱼ) < ∞`, Theorem 3.6 makes `Hⁿ(p(P)) = 0` for almost all
`p`, so the hypothesis with `B := P` forces `Hⁿ(P) = 0`. Adding `P` to the null exceptional set
of a Lipschitz cover of `R` shows that `A` is countably `n`-rectifiable. -/
theorem Submission.section3_rectifiabilityTheorem_of_besicovitchFederer :
    BesicovitchFedererProjectionTheorem → RectifiabilityTheoremForSets := by
  rintro hBF n ℓ A ⟨Aj, hAeq, hAj⟩ hpos
  obtain ⟨R, P, hRP, -, hR, hP⟩ :=
    (Submission.section3_rectifiableDecomposition n ℓ A ⟨Aj, hAeq, hAj⟩).1
  have hPA : P ⊆ A := hRP ▸ subset_union_right
  have hPproj : ForAlmostAllProjections (n + ℓ) n (fun p ↦ μHE[n] (p '' P) = 0) := by
    refine hBF n ℓ P hP ⟨fun j ↦ P ∩ Aj j, ?_, fun j ↦ ?_⟩
    · rw [← inter_iUnion, ← hAeq, inter_eq_left.mpr hPA]
    · exact (measure_mono inter_subset_right).trans_lt (hAj j)
  have hP0 : μHE[n] P = 0 := by
    by_contra hne
    exact hpos P hPA (pos_iff_ne_zero.mpr hne) hPproj
  obtain ⟨M₀, hM₀, F, hF, hRcover⟩ := hR
  refine ⟨M₀ ∪ P, measure_union_null hM₀ hP0, F, hF, ?_⟩
  calc A = R ∪ P := hRP
    _ ⊆ (M₀ ∪ ⋃ j, range (F j)) ∪ P := union_subset_union_left P hRcover
    _ = M₀ ∪ P ∪ ⋃ j, range (F j) := union_right_comm _ _ _

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

/-- **Simon Ch. 3, Lemma 3.3 (pp. 78–79), given Lemma 1.2** (`chapter-03.txt` lines 476–496).
Let `R ⊆ S` be countably `n`-rectifiable. Lemma 1.2 ("⇒") gives `R ⊆ N₀ ∪ ⋃ⱼ Nⱼ` with
`Hⁿ(N₀) = 0` and `Nⱼ` embedded `C¹` submanifolds, so it suffices that each `R ∩ Nⱼ` is
`Hⁿ`-null, and by Lindelöf (`measure_null_of_locally_null`) that `R ∩ Nⱼ ∩ W` is `Hⁿ`-null for
the chart `ψ : V → W` of `Nⱼ` at each of its points. There `R ∩ Nⱼ ∩ W = ψ(T)` with
`T = V ∩ ψ⁻¹(R)`. If `Lⁿ(T) = 0`, then `Hⁿ(ψ(T)) = 0` (`C¹` images of null sets). Otherwise
some `p_J` with `#J = n` has `Hⁿ(p_J(ψ(T))) > 0` (`p_J ∘ ψ` is anti-Lipschitz near a density
point of `T`), contradicting `Hⁿ(p_J(S)) = 0` as `ψ(T) ⊆ R ⊆ S`. -/
theorem Submission.section3_coordinateProjectionCriterion_of_submanifoldCover :
    SubmanifoldCoverCharacterization → CoordinateProjectionCriterion := by
  intro hcover n ℓ S hS R hRS hR
  obtain ⟨N₀, N, hN₀, hN, hRN⟩ := (hcover n ℓ R).1 hR
  have hRN_null : ∀ j, μHE[n] (R ∩ N j) = 0 := by
    intro j
    refine measure_null_of_locally_null _ fun x hx ↦ ?_
    -- The chart of `N j` at `x`; injectivity and properness of `ψ` are not needed.
    obtain ⟨V, W, ψ, hV, hW, hxW, hψ, -, himage, -, hD⟩ := hN j x hx.2
    refine ⟨R ∩ N j ∩ W, inter_mem_nhdsWithin _ (hW.mem_nhds hxW), ?_⟩
    have hTV : V ∩ ψ ⁻¹' R ⊆ V := inter_subset_left
    have hsub : R ∩ N j ∩ W ⊆ ψ '' (V ∩ ψ ⁻¹' R) := by
      rw [image_inter_preimage, himage]
      exact fun z hz ↦ ⟨⟨hz.2, hz.1.2⟩, hz.1.1⟩
    refine measure_mono_null hsub ?_
    by_cases hT : volume (V ∩ ψ ⁻¹' R) = 0
    · exact Submission.section3_contDiffOn_image_null_of_volume_null n (n + ℓ) V
        (V ∩ ψ ⁻¹' R) ψ hV hψ hTV hT
    · obtain ⟨J, hJ, hpos⟩ := Submission.section3_chart_coordinateProjection_pos n ℓ V
        (V ∩ ψ ⁻¹' R) ψ hV hψ hD hTV (pos_iff_ne_zero.2 hT)
      have hψS : ψ '' (V ∩ ψ ⁻¹' R) ⊆ S := (image_subset_iff.2 inter_subset_right).trans hRS
      exact absurd (measure_mono_null (image_mono hψS) (hS J hJ)) hpos.ne'
  have hnull : μHE[n] (N₀ ∪ ⋃ j, R ∩ N j) = 0 :=
    measure_union_null hN₀ (measure_iUnion_null hRN_null)
  refine measure_mono_null (fun x hx ↦ ?_) hnull
  rcases hRN hx with h | h
  · exact Or.inl h
  · obtain ⟨j, hj⟩ := mem_iUnion.1 h
    exact Or.inr (mem_iUnion.2 ⟨j, hx, hj⟩)

end GMT.Ch03
