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

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
