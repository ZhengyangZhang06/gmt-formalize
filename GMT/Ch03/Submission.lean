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

/-- **Derivative bounds for a `C¹` chart with upper and lower Lipschitz bounds** (Simon Ch. 3, the
`C¹` charts in the proof of Theorem 1.6 "⇒", `chapter-03.txt` lines 113–143, and Remark 1.5(2)).
Let `B ⊆ ℝⁿ` be open and `ψ : ℝⁿ → ℝᴺ` be `C¹` and `K`-Lipschitz on `B`, with
`c |u - u'| ≤ |ψ(u) - ψ(u')|` for all `u, u' ∈ B` (no sign condition on `c`). Then for every
`v ∈ B`: `‖Dψ(v)‖ ≤ K` by `norm_fderiv_le_of_lipschitzOn`, as `B ∈ 𝓝 v`; and `c |w| ≤ |Dψ(v) w|`
for every `w ∈ ℝⁿ`, since for small `t > 0` we have `v + t w ∈ B`, hence
`c |w| ≤ |t⁻¹ (ψ(v + t w) - ψ(v))|`, and these difference quotients tend to `Dψ(v) w` as `t ↓ 0`
(`HasFDerivAt.lim`). -/
theorem Submission.chartTD_chart_fderiv_bounds : ∀ (n N : ℕ) (B : Set (Rn n)) (ψ : Rn n → Rn N) (K : ℝ≥0) (c : ℝ), IsOpen B → ContDiffOn ℝ 1 ψ B → LipschitzOnWith K ψ B → (∀ u ∈ B, ∀ u' ∈ B, c * ‖u - u'‖ ≤ ‖ψ u - ψ u'‖) → ∀ v ∈ B, ‖fderiv ℝ ψ v‖ ≤ K ∧ ∀ w : Rn n, c * ‖w‖ ≤ ‖fderiv ℝ ψ v w‖ := by
  intro n N B ψ K c hB hψ hLip hlow v hv
  have hBv : B ∈ 𝓝 v := hB.mem_nhds hv
  -- Upper bound: `ψ` is `K`-Lipschitz on the neighbourhood `B` of `v`.
  refine ⟨norm_fderiv_le_of_lipschitzOn ℝ hBv hLip, fun w ↦ ?_⟩
  -- `ψ` is `C¹` on the open set `B`, so it has derivative `Dψ(v)` at `v`.
  have hd : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    ((hψ.differentiableOn one_ne_zero).differentiableAt hBv).hasFDerivAt
  -- `|t⁻¹ (ψ(v + t w) - ψ(v))| → |Dψ(v) w|` as `t ↓ 0`, since `|t⁻¹| = t⁻¹ → ∞`.
  have hlim : Tendsto (fun t : ℝ ↦ ‖t⁻¹ • (ψ (v + t⁻¹⁻¹ • w) - ψ v)‖) (𝓝[>] 0)
      (𝓝 ‖fderiv ℝ ψ v w‖) := by
    refine (hd.lim w (c := fun t : ℝ ↦ t⁻¹) ?_).norm
    refine (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [Real.norm_of_nonneg (inv_nonneg.2 ht.le)]
  -- Eventually `v + t w ∈ B`, as `v + t w → v` when `t ↓ 0`.
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), v + t • w ∈ B := by
    have hcont : Tendsto (fun t : ℝ ↦ v + t • w) (𝓝 0) (𝓝 v) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 v (by simp)
    exact hcont.mono_left nhdsWithin_le_nhds hBv
  -- For such `t > 0`: `c |w| = t⁻¹ c |t w| ≤ t⁻¹ |ψ(v + t w) - ψ(v)|`.
  refine ge_of_tendsto hlim ?_
  filter_upwards [hev, self_mem_nhdsWithin] with t ht (htpos : 0 < t)
  have h := hlow (v + t • w) ht v hv
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le] at h
  rw [inv_inv, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 htpos.le)]
  calc c * ‖w‖ = t⁻¹ * (c * (t * ‖w‖)) := by field_simp
    _ ≤ t⁻¹ * ‖ψ (v + t • w) - ψ v‖ := by gcongr
/-- **Operator-norm bound for the area factor** (Simon Ch. 2, linear area formula (3.1),
`chapter-02.txt` lines 742–758, and the Lipschitz image estimate Thm. 1.8(i), lines 268–275):
for every linear map `A : ℝⁿ → ℝᴺ`, `normDet A = √det(A* A) ≤ ‖A‖ⁿ`. On the closed unit ball
`S ⊆ ℝⁿ` the linear area formula gives `Hⁿ(A(S)) = normDet A · Lⁿ(S)`, while `A` is
`‖A‖`-Lipschitz, so `Hⁿ(A(S)) ≤ ‖A‖ⁿ Hⁿ(S) = ‖A‖ⁿ Lⁿ(S)`; cancel `0 < Lⁿ(S) < ∞`. -/
theorem Submission.chartTD_normDet_le_opNorm_pow : ∀ (n N : ℕ) (A : Rn n →L[ℝ] Rn N), A.toLinearMap.normDet ≤ ‖A‖ ^ n := by
  intro n N A
  have hfin : finrank ℝ (Rn n) = n := finrank_euclideanSpace_fin
  set S : Set (Rn n) := Metric.closedBall 0 1
  -- Simon Ch. 2 (3.1): `Hⁿ(A(S)) = normDet A · Lⁿ(S)`.
  have h1 := LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume A.toLinearMap S
  -- `A` is `‖A‖₊`-Lipschitz, so `Hⁿ(A(S)) ≤ ‖A‖₊ⁿ Hⁿ(S) = ‖A‖₊ⁿ Lⁿ(S)`.
  have h2 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
    (finrank ℝ (Rn n)) (A.lipschitzWith.lipschitzOnWith (s := S))
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h2
  have hcoe : (A.toLinearMap : Rn n → Rn N) '' S = A '' S := rfl
  rw [← hcoe, h1] at h2
  -- Cancel `0 < Lⁿ(S) < ∞`.
  have hpos : 0 < volume S := Metric.measure_closedBall_pos _ _ one_pos
  have hfinite : volume S < ∞ := measure_closedBall_lt_top
  have h3 : ENNReal.ofReal A.toLinearMap.normDet ≤ (‖A‖₊ : ℝ≥0∞) ^ finrank ℝ (Rn n) :=
    (ENNReal.mul_le_mul_iff_left hpos.ne' hfinite.ne).mp h2
  rw [hfin] at h3
  -- Back to `ℝ`: `(‖A‖₊ : ℝ≥0∞)ⁿ = ofReal (‖A‖ⁿ)`.
  have h4 : ENNReal.ofReal A.toLinearMap.normDet ≤ ENNReal.ofReal (‖A‖ ^ n) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _)]
    simpa [ofReal_norm, enorm_eq_nnnorm] using h3
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h4

/-- **Blow-up limit of a pulled-back chart integral** (Simon Ch. 3, proof of Theorem 1.6 "⇒" and
Remark 1.5(2), `chapter-03.txt` lines 87–90 and 113–143, for a single bi-Lipschitz `C¹` chart):
let `B ⊆ ℝⁿ` be open, `ψ` `C¹` and `K`-Lipschitz on `B` with `c|u - u'| ≤ |ψ(u) - ψ(u')|`
(`c > 0`) on `B`, and `Jψ(v) = normDet(Dψ(v))`. Then for `u ∈ B` and `f ∈ C_c(ℝᴺ)`,
`r⁻ⁿ ∫_B f(η_{ψ(u),r}(ψ(v))) Jψ(v) dv → Jψ(u) ∫_{ℝⁿ} f(Dψ(u) y) dy` as `r ↓ 0`. The substitution
`v = u + r y` turns the left side into `∫ G_r` with
`G_r(y) = 1_B(u + r y) f(r⁻¹(ψ(u + r y) - ψ(u))) Jψ(u + r y)`. If `f(z) ≠ 0` forces `|z| ≤ R`, the
lower bound gives `G_r = 0` off `B̄_{R/c}(0)`, and `|G_r| ≤ (sup |f|) Kⁿ` by
`Submission.chartTD_chart_fderiv_bounds` and `Submission.chartTD_normDet_le_opNorm_pow`. Since
`G_r(y) → f(Dψ(u) y) Jψ(u)` pointwise (`Dψ` and `normDet` are continuous), dominated convergence
applies. -/
theorem Submission.chartTD_chart_blowup_integral_tendsto : ∀ (n N : ℕ) (B : Set (Rn n))
    (ψ : Rn n → Rn N) (K : ℝ≥0) (c : ℝ), IsOpen B → ContDiffOn ℝ 1 ψ B →
    LipschitzOnWith K ψ B → 0 < c → (∀ u ∈ B, ∀ u' ∈ B, c * ‖u - u'‖ ≤ ‖ψ u - ψ u'‖) →
    ∀ u ∈ B, ∀ f : C_c(Rn N, ℝ),
      Tendsto (fun r : ℝ ↦ (r ^ n)⁻¹ * ∫ v in B, f (blowUpMap (ψ u) r (ψ v)) *
          (fderiv ℝ ψ v).toLinearMap.normDet) (𝓝[>] 0)
        (𝓝 ((fderiv ℝ ψ u).toLinearMap.normDet * ∫ y, f (fderiv ℝ ψ u y))) := by
  intro n N B ψ K c hB hψ hLip hc hlow u hu f
  set J : Rn n → ℝ := fun v => (fderiv ℝ ψ v).toLinearMap.normDet with hJdef
  set L := fderiv ℝ ψ u with hLdef
  have hBmeas : MeasurableSet B := hB.measurableSet
  -- Step 1: `normDet = √det(A* ∘ A)` is continuous, so `J = normDet ∘ Dψ` is Borel and continuous
  -- at `u`; `0 ≤ J ≤ Kⁿ` on `B`; `ψ` is continuous on `B` and has derivative `L` at `u`.
  have hND : Continuous (fun A : Rn n →L[ℝ] Rn N ↦ A.toLinearMap.normDet) := by
    have key : ∀ A : Rn n →L[ℝ] Rn N, A.toLinearMap.normDet =
        Real.sqrt ((ContinuousLinearMap.adjoint A ∘L A).det) := by
      intro A
      rw [← A.normDet_sq]
      simp [Real.sqrt_sq (LinearMap.normDet_nonneg _)]
    simp_rw [key]
    exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id))
  have hJmeas : Measurable J := hND.measurable.comp (measurable_fderiv ℝ ψ)
  have hJnn : ∀ v, 0 ≤ J v := fun v => LinearMap.normDet_nonneg _
  have hJle : ∀ v ∈ B, J v ≤ (K : ℝ) ^ n := fun v hv =>
    (Submission.chartTD_normDet_le_opNorm_pow n N _).trans
      (pow_le_pow_left₀ (norm_nonneg _)
        (Submission.chartTD_chart_fderiv_bounds n N B ψ K c hB hψ hLip hlow v hv).1 n)
  have hJcont : ContinuousAt J u := by
    have h1 : ContinuousAt (fderiv ℝ ψ) u :=
      (hψ.continuousOn_fderiv_of_isOpen hB le_rfl).continuousAt (hB.mem_nhds hu)
    exact hND.continuousAt.comp h1
  have hψcont : ContinuousOn ψ B := hLip.continuousOn
  have hd : HasFDerivAt ψ L u :=
    ((hψ.differentiableOn one_ne_zero).differentiableAt (hB.mem_nhds hu)).hasFDerivAt
  -- Step 2: `|f| ≤ M` everywhere, and `f z ≠ 0` forces `‖z‖ ≤ R`.
  obtain ⟨M, hM⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  obtain ⟨R, hR⟩ : ∃ R, ∀ z, f z ≠ 0 → ‖z‖ ≤ R := by
    obtain ⟨R, hR⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
    exact ⟨R, fun z hz => by simpa using hR (subset_tsupport _ hz)⟩
  -- Step 3: the substitution `v = u + r y`: `r⁻ⁿ ∫_B h_r = ∫ G_r` for every `r > 0`.
  let h : ℝ → Rn n → ℝ := fun r v => f (blowUpMap (ψ u) r (ψ v)) * J v
  let G : ℝ → Rn n → ℝ := fun r y => B.indicator (h r) (u + r • y)
  have hsub : ∀ r : ℝ, 0 < r →
      (r ^ n)⁻¹ * ∫ v in B, f (blowUpMap (ψ u) r (ψ v)) * J v = ∫ y, G r y := by
    intro r hr
    rw [← integral_indicator hBmeas]
    have h1 := Measure.integral_comp_smul (volume : Measure (Rn n))
      (fun y => B.indicator (h r) (u + y)) r
    rw [integral_add_left_eq_self (fun y => B.indicator (h r) y) u] at h1
    rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hr n)), smul_eq_mul] at h1
    exact h1.symm
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- Step 4: dominated convergence with the bound `M Kⁿ 1_{B̄_{R/c}(0)}`.
  have hDCT : Tendsto (fun r => ∫ y, G r y) (𝓝[>] 0) (𝓝 (∫ y, f (L y) * J u)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => (Metric.closedBall (0 : Rn n) (R / c)).indicator (fun _ => M * (K : ℝ) ^ n) y)
      ?_ ?_ ?_ ?_
    · -- `G_r = 1_{S_r} · (h_r ∘ (u + r •))` with `S_r = {y | u + r y ∈ B}` open.
      filter_upwards [self_mem_nhdsWithin] with r hr
      have haff : Continuous (fun y : Rn n => u + r • y) := by fun_prop
      set S : Set (Rn n) := (fun y : Rn n => u + r • y) ⁻¹' B with hSdef
      have hSopen : IsOpen S := hB.preimage haff
      have hGS : G r = S.indicator (fun y => h r (u + r • y)) := by
        funext y
        by_cases hy : u + r • y ∈ B
        · simp [G, S, Set.indicator_of_mem, hy]
        · simp [G, S, Set.indicator_of_notMem, hy]
      rw [hGS, aestronglyMeasurable_indicator_iff hSopen.measurableSet]
      have h1 : ContinuousOn (fun y : Rn n => f (blowUpMap (ψ u) r (ψ (u + r • y)))) S := by
        have hb : Continuous (fun z : Rn N => blowUpMap (ψ u) r z) := by
          unfold blowUpMap; fun_prop
        exact (f.continuous.comp hb).comp_continuousOn
          (hψcont.comp haff.continuousOn (fun y hy => hy))
      have h2 : Measurable (fun y : Rn n => J (u + r • y)) := hJmeas.comp haff.measurable
      exact (h1.aestronglyMeasurable hSopen.measurableSet).mul
        h2.aestronglyMeasurable.restrict
    · -- If `G_r(y) ≠ 0` then `c r ‖y‖ ≤ ‖ψ(u + r y) - ψ(u)‖ ≤ r R`, so `‖y‖ ≤ R / c`.
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : (0:ℝ) < r := hr
      refine Eventually.of_forall (fun y => ?_)
      by_cases hy : u + r • y ∈ B
      · have hGy : G r y = f (blowUpMap (ψ u) r (ψ (u + r • y))) * J (u + r • y) := by
          simp [G, h, Set.indicator_of_mem, hy]
        rw [hGy]
        by_cases hf0 : f (blowUpMap (ψ u) r (ψ (u + r • y))) = 0
        · rw [hf0, zero_mul, norm_zero]
          exact Set.indicator_nonneg (fun _ _ => by positivity) _
        · have hRb := hR _ hf0
          have hyball : y ∈ Metric.closedBall (0 : Rn n) (R / c) := by
            rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hc]
            have h1 := hlow (u + r • y) hy u hu
            rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr'.le] at h1
            unfold blowUpMap at hRb
            rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr'.le)] at hRb
            have h2 : ‖ψ (u + r • y) - ψ u‖ ≤ r * R := by
              rw [inv_mul_le_iff₀ hr'] at hRb; linarith
            nlinarith
          rw [Set.indicator_of_mem hyball, norm_mul, Real.norm_of_nonneg (hJnn _)]
          exact mul_le_mul (hM _) (hJle _ hy) (hJnn _) hM0
      · have hGy : G r y = 0 := by simp [G, Set.indicator_of_notMem, hy]
        rw [hGy, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => by positivity) _
    · exact (integrableOn_const (measure_closedBall_lt_top (x := (0 : Rn n))
        (r := R / c)).ne).integrable_indicator measurableSet_closedBall
    · -- Pointwise: eventually `u + r y ∈ B`, `r⁻¹(ψ(u + r y) - ψ(u)) → L y`, `J(u + r y) → J(u)`.
      refine Eventually.of_forall (fun y => ?_)
      have hlin : Tendsto (fun r : ℝ => u + r • y) (𝓝[>] 0) (𝓝 u) := by
        have : Tendsto (fun r : ℝ => u + r • y) (𝓝 0) (𝓝 (u + (0:ℝ) • y)) :=
          ((continuous_const.add (continuous_id.smul continuous_const)).tendsto 0)
        simpa using this.mono_left nhdsWithin_le_nhds
      have hevB : ∀ᶠ r in 𝓝[>] (0:ℝ), u + r • y ∈ B := hlin (hB.mem_nhds hu)
      have hq : Tendsto (fun r : ℝ => blowUpMap (ψ u) r (ψ (u + r • y))) (𝓝[>] 0)
          (𝓝 (L y)) := by
        have := hd.lim y (c := fun r : ℝ => r⁻¹) (l := 𝓝[>] (0:ℝ)) (by
          refine (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).congr' ?_
          filter_upwards [self_mem_nhdsWithin] with t ht
          simp [abs_of_pos (show (0:ℝ) < t from ht)])
        simpa [blowUpMap, inv_inv] using this
      have hlim : Tendsto (fun r : ℝ => f (blowUpMap (ψ u) r (ψ (u + r • y))) * J (u + r • y))
          (𝓝[>] 0) (𝓝 (f (L y) * J u)) :=
        ((f.continuous.tendsto _).comp hq).mul (hJcont.tendsto.comp hlin)
      refine hlim.congr' ?_
      filter_upwards [hevB] with r hr
      simp [G, h, Set.indicator_of_mem, hr]
  -- Step 5: `∫ f(L y) J(u) dy = J(u) ∫ f(L y) dy`, and the two sides agree for `r > 0`.
  rw [integral_mul_const, mul_comm] at hDCT
  refine hDCT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hsub r hr).symm

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
