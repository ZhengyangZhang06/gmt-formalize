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

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
