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

/-- **Bi-invariant Haar probability on the orthogonal stabilizer of a subspace** (Step 1 of the
frame-averaging argument in the proof of Simon Ch. 3, Theorem 3.6; Mattila, *Geometry of Sets and
Measures in Euclidean Spaces*, Ch. 3). Let `U ⊆ ℝᴺ` be a subspace, `𝓛 = ℝᴺ →L[ℝ] ℝᴺ` and
`K_U = {g ∈ 𝓛 : g* g = 1, g x = x for x ∈ U}`. There is a Borel probability `θ` on `𝓛` with
`θ`-a.e. `g ∈ K_U`, invariant under `g ↦ k g` and `g ↦ g k` for every `k ∈ K_U`. `K_U` is a closed
bounded subgroup of the unitary group of the finite-dimensional `𝓛`, hence a compact group; `θ` is
the image under the inclusion of its Haar probability `μ`, and `μ` is also right invariant by
uniqueness of Haar measure on compact groups. -/
theorem Submission.bf_orthStabilizer_haar_exists : ∀ (N : ℕ) (U : Submodule ℝ (Rn N)), ∃ θ : Measure (Rn N →L[ℝ] Rn N), IsProbabilityMeasure θ ∧ (∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1 ∧ ∀ x ∈ U, g x = x) ∧ ∀ k : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint k * k = 1 → (∀ x ∈ U, k x = x) → Measure.map (fun g ↦ k * g) θ = θ ∧ Measure.map (fun g ↦ g * k) θ = θ := by
  intro N U
  -- Step 3 (topology): the adjoint `g ↦ g*` is continuous, so `star` is continuous on `𝓛` and
  -- `unitary 𝓛` (inversion = `star`) is a topological group.
  have hadj : Continuous (fun g : Rn N →L[ℝ] Rn N ↦ ContinuousLinearMap.adjoint g) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn N) (F := Rn N)).continuous
  have : ContinuousStar (Rn N →L[ℝ] Rn N) := ⟨by
    have h : (star : (Rn N →L[ℝ] Rn N) → (Rn N →L[ℝ] Rn N)) =
        fun g ↦ ContinuousLinearMap.adjoint g := funext ContinuousLinearMap.star_eq_adjoint
    rw [h]
    exact hadj⟩
  have : ContinuousInv (unitary (Rn N →L[ℝ] Rn N)) :=
    ⟨continuous_induced_rng.mpr continuous_subtype_val.star⟩
  have : IsTopologicalGroup (unitary (Rn N →L[ℝ] Rn N)) := {}
  -- Step 1: `g* g = 1` forces `g g* = 1` (`g` is injective, hence surjective), so `g ∈ unitary 𝓛`.
  have hunit : ∀ g : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint g * g = 1 →
      g ∈ unitary (Rn N →L[ℝ] Rn N) := by
    intro g hg
    have hgg : ∀ x, ContinuousLinearMap.adjoint g (g x) = x := fun x ↦ by
      rw [← mul_apply_eq_comp, hg, one_apply_eq_self]
    have hsurj : Function.Surjective g :=
      LinearMap.surjective_of_injective (f := (g : Rn N →ₗ[ℝ] Rn N))
        (Function.LeftInverse.injective hgg)
    rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint]
    refine ⟨hg, ?_⟩
    ext1 y
    obtain ⟨x, rfl⟩ := hsurj y
    rw [mul_apply_eq_comp, hgg, one_apply_eq_self]
  -- Step 2: `K = K_U` as a subgroup of `unitary 𝓛`, with inclusion `ι : K → 𝓛`.
  let K : Subgroup (unitary (Rn N →L[ℝ] Rn N)) :=
    { carrier := {u | ∀ x ∈ U, (u : Rn N →L[ℝ] Rn N) x = x}
      mul_mem' := by
        intro a b ha hb x hx
        change ((a : Rn N →L[ℝ] Rn N) * (b : Rn N →L[ℝ] Rn N)) x = x
        rw [mul_apply_eq_comp, hb x hx, ha x hx]
      one_mem' := fun _ _ ↦ rfl
      inv_mem' := by
        intro a ha x hx
        change (star (a : Rn N →L[ℝ] Rn N)) x = x
        conv_lhs => rw [← ha x hx]
        rw [← mul_apply_eq_comp, Unitary.star_mul_self_of_mem a.2, one_apply_eq_self] }
  let ι : K → Rn N →L[ℝ] Rn N := fun k ↦ ((k : unitary (Rn N →L[ℝ] Rn N)) : Rn N →L[ℝ] Rn N)
  have hι : Continuous ι := continuous_subtype_val.comp continuous_subtype_val
  have hιind : Topology.IsInducing ι :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  -- Step 3: `S = ι(K)` is closed and bounded (`‖g‖ ≤ 1`) in the finite-dimensional `𝓛`, so `K`
  -- is compact.
  set S : Set (Rn N →L[ℝ] Rn N) :=
    {g | ContinuousLinearMap.adjoint g * g = 1 ∧ ∀ x ∈ U, g x = x}
  have hSclosed : IsClosed S := by
    have h1 : IsClosed {g : Rn N →L[ℝ] Rn N | ContinuousLinearMap.adjoint g * g = 1} :=
      isClosed_eq (hadj.mul continuous_id) continuous_const
    have h2 : IsClosed {g : Rn N →L[ℝ] Rn N | ∀ x ∈ U, g x = x} := by
      have : {g : Rn N →L[ℝ] Rn N | ∀ x ∈ U, g x = x} = ⋂ x ∈ U, {g | g x = x} := by
        ext g
        simp
      rw [this]
      exact isClosed_biInter fun x _ ↦
        isClosed_eq (continuous_id.clm_apply continuous_const) continuous_const
    exact h1.inter h2
  have hrange : Set.range ι = S := by
    ext g
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨?_, k.2⟩
      have := Unitary.star_mul_self_of_mem (k : unitary (Rn N →L[ℝ] Rn N)).2
      rwa [ContinuousLinearMap.star_eq_adjoint] at this
    · rintro ⟨hg, hfix⟩
      exact ⟨⟨⟨g, hunit g hg⟩, hfix⟩, rfl⟩
  have hSbdd : Bornology.IsBounded S := by
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1, fun g hg ↦ ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
    have h2 : inner ℝ (g x) (g x) = inner ℝ x x := by
      rw [← ContinuousLinearMap.adjoint_inner_right, ← mul_apply_eq_comp, hg.1, one_apply_eq_self]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h2
    rw [one_mul, (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2]
  have : CompactSpace K := by
    rw [← isCompact_univ_iff, hιind.isCompact_iff, Set.image_univ, hrange]
    exact Metric.isCompact_of_isClosed_isBounded hSclosed hSbdd
  -- Step 4: the Haar measure `μ` on `K` normalized by `μ(K) = 1`.
  let μ : Measure K := Measure.haarMeasure ⊤
  have : IsProbabilityMeasure μ := ⟨by
    have := Measure.haarMeasure_self (G := K) (K₀ := ⊤)
    rw [TopologicalSpace.PositiveCompacts.coe_top] at this
    exact this⟩
  -- Step 5: right invariance of `μ`, by uniqueness of Haar measure on the compact group `K`.
  have hright : ∀ k : K, Measure.map (fun h ↦ h * k) μ = μ := by
    intro k
    set ρ := Measure.map (fun h ↦ h * k) μ with hρ
    have hc := Measure.isMulInvariant_eq_smul_of_compactSpace ρ μ
    have huniv : ρ univ = 1 := by
      rw [hρ, Measure.map_apply (measurable_mul_const k) MeasurableSet.univ, Set.preimage_univ,
        measure_univ]
    have hc1 : ρ.haarScalarFactor μ = 1 := by
      have h := congrArg (fun m : Measure K ↦ m univ) hc
      simp only [Measure.smul_apply, measure_univ, huniv] at h
      have h' : ((ρ.haarScalarFactor μ : ℝ≥0) : ℝ≥0∞) = 1 := by
        simpa [ENNReal.smul_def] using h.symm
      exact_mod_cast h'
    rw [hc1, one_smul] at hc
    exact hc
  -- Steps 6–7: `θ = ι_* μ` is concentrated on `S`, and translations by `k ∈ K_U` commute with `ι`.
  refine ⟨Measure.map ι μ, inferInstance, ?_, ?_⟩
  · rw [ae_map_iff hι.aemeasurable hSclosed.measurableSet]
    exact Eventually.of_forall fun k ↦ (hrange ▸ ⟨k, rfl⟩ : ι k ∈ S)
  · intro k hk hfix
    let k' : K := ⟨⟨k, hunit k hk⟩, hfix⟩
    have hl : Measurable (fun g : Rn N →L[ℝ] Rn N ↦ k * g) := measurable_const_mul k
    have hr : Measurable (fun g : Rn N →L[ℝ] Rn N ↦ g * k) := measurable_mul_const k
    constructor
    · rw [Measure.map_map hl hι.measurable]
      have : (fun g : Rn N →L[ℝ] Rn N ↦ k * g) ∘ ι = ι ∘ (fun h : K ↦ k' * h) := rfl
      rw [this, ← Measure.map_map hι.measurable (measurable_const_mul k'),
        map_mul_left_eq_self μ k']
    · rw [Measure.map_map hr hι.measurable]
      have : (fun g : Rn N →L[ℝ] Rn N ↦ g * k) ∘ ι = ι ∘ (fun h : K ↦ h * k') := rfl
      rw [this, ← Measure.map_map hι.measurable (measurable_mul_const k'), hright k']
/-- Orbit law under the stabilizer `K = {g : g*g = 1, g = id on V^⊥}`, used when averaging over
`O(N)` for Simon Ch. 3, Thm. 3.6 (cf. Mattila, *Geometry of Sets and Measures in Euclidean
Spaces*, Ch. 3 "Invariant measures"). Let `θ` be a probability on `ℝᴺ →L[ℝ] ℝᴺ`
concentrated on `K` and invariant under `K`, and let `0 < Hⁿ(S(V)) < ∞`, `S(V) = V ∩ ∂B₁(0)`.
Then `θ{g : gζ ∈ Y} = 0` for `ζ ∈ S(V)` and every Borel `Y` with `Hⁿ(Y ∩ S(V)) = 0`.
Slice `T = {(g, x) : gx ∈ Y}` under `θ ⊗ Hⁿ⌞S(V)` both ways. Each `g ∈ K` is an isometry
mapping `S(V)` into itself, so every `g`-slice is `Hⁿ⌞S(V)`-null. The reflection in
`(ζ - x)^⊥` lies in `K` and maps `ζ` to `x ∈ S(V)`, so by right invariance every such `x`-slice
has `θ`-measure `θ{g : gζ ∈ Y}`. Hence `θ{g : gζ ∈ Y} · Hⁿ(S(V)) = 0`. -/
theorem Submission.bf_stabilizerOrbit_null : ∀ (N n : ℕ) (V : Submodule ℝ (Rn N)) (θ : Measure (Rn N →L[ℝ] Rn N)), IsProbabilityMeasure θ → (∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1 ∧ ∀ x ∈ Vᗮ, g x = x) → (∀ k : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint k * k = 1 → (∀ x ∈ Vᗮ, k x = x) → Measure.map (fun g ↦ k * g) θ = θ ∧ Measure.map (fun g ↦ g * k) θ = θ) → 0 < μHE[n] {x : Rn N | x ∈ V ∧ ‖x‖ = 1} → μHE[n] {x : Rn N | x ∈ V ∧ ‖x‖ = 1} < ∞ → ∀ ζ ∈ V, ‖ζ‖ = 1 → ∀ Y : Set (Rn N), MeasurableSet Y → μHE[n] (Y ∩ {x : Rn N | x ∈ V ∧ ‖x‖ = 1}) = 0 → θ {g | g ζ ∈ Y} = 0 := by
  intro N n V θ hθP hθK hθinv hpos hfin ζ hζV hζ1 Y hY hYnull
  set S : Set (Rn N) := {x : Rn N | x ∈ V ∧ ‖x‖ = 1}
  have hSm : MeasurableSet S :=
    (V.closed_of_finiteDimensional.inter
      (isClosed_eq continuous_norm continuous_const)).measurableSet
  -- `g*g = 1` makes `g` preserve inner products, hence norms.
  have hinner : ∀ g : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint g * g = 1 →
      ∀ x y : Rn N, inner ℝ (g x) (g y) = inner ℝ x y := by
    intro g hg x y
    rw [← ContinuousLinearMap.adjoint_inner_right, ← mul_apply_eq_comp, hg, one_apply_eq_self]
  have hnorm : ∀ g : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint g * g = 1 →
      ∀ x : Rn N, ‖g x‖ = ‖x‖ := by
    intro g hg x
    have h := hinner g hg x x
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
  -- Every `g ∈ K` maps `V = V^⊥⊥` into itself, hence `S` into `S`.
  have hmaps : ∀ g : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint g * g = 1 →
      (∀ x ∈ Vᗮ, g x = x) → ∀ x ∈ S, g x ∈ S := by
    rintro g hg hfix x ⟨hxV, hx1⟩
    refine ⟨?_, (hnorm g hg x).trans hx1⟩
    rw [← Submodule.orthogonal_orthogonal V]
    intro y hy
    calc inner ℝ y (g x) = inner ℝ (g y) (g x) := by rw [hfix y hy]
      _ = inner ℝ y x := hinner g hg y x
      _ = 0 := Submodule.inner_left_of_mem_orthogonal hxV hy
  -- `K` is transitive on `S`: the reflection in `(ζ - x)^⊥` lies in `K` and maps `ζ` to `x`.
  have htrans : ∀ x ∈ S, ∃ k : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint k * k = 1 ∧
      (∀ z ∈ Vᗮ, k z = z) ∧ k ζ = x := by
    rintro x ⟨hxV, hx1⟩
    let r := (ℝ ∙ (ζ - x))ᗮ.reflection
    let k : Rn N →L[ℝ] Rn N := r.toContinuousLinearEquiv.toContinuousLinearMap
    have hkr : ∀ z, k z = r z := fun z ↦ rfl
    refine ⟨k, ?_, fun z hz ↦ ?_, ?_⟩
    · ext1 z
      refine ext_inner_right ℝ fun w ↦ ?_
      rw [mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_left, one_apply_eq_self, hkr,
        hkr]
      exact r.inner_map_map z w
    · rw [hkr]
      refine Submodule.reflection_mem_subspace_eq_self ?_
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact Submodule.inner_right_of_mem_orthogonal (V.sub_mem hζV hxV) hz
    · rw [hkr]
      exact Submodule.reflection_sub (hζ1.trans hx1.symm)
  -- Right invariance: `θ{g : gx ∈ Y} = θ{g : gζ ∈ Y}` for `x ∈ S`.
  have hev : MeasurableSet {g : Rn N →L[ℝ] Rn N | g ζ ∈ Y} :=
    (continuous_id.clm_apply continuous_const).measurable hY
  have horbit : ∀ x ∈ S, θ {g | g x ∈ Y} = θ {g | g ζ ∈ Y} := by
    intro x hx
    obtain ⟨k, hk, hkfix, rfl⟩ := htrans x hx
    calc θ {g | g (k ζ) ∈ Y} = Measure.map (fun g ↦ g * k) θ {g | g ζ ∈ Y} := by
          rw [Measure.map_apply (measurable_mul_const k) hev]
          rfl
      _ = θ {g | g ζ ∈ Y} := by rw [(hθinv k hk hkfix).2]
  -- Slice `T = {(g, x) : gx ∈ Y}` under `θ ⊗ Hⁿ⌞S` in both orders.
  have : IsFiniteMeasure ((μHE[n] : Measure (Rn N)).restrict S) :=
    isFiniteMeasure_restrict.mpr hfin.ne
  have hT : MeasurableSet {p : (Rn N →L[ℝ] Rn N) × Rn N | p.1 p.2 ∈ Y} :=
    (continuous_fst.clm_apply continuous_snd).measurable hY
  have h1 : θ.prod ((μHE[n] : Measure (Rn N)).restrict S)
      {p : (Rn N →L[ℝ] Rn N) × Rn N | p.1 p.2 ∈ Y} = 0 := by
    rw [Measure.prod_apply hT]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hθK] with g hg
    rw [Measure.restrict_apply (measurable_prodMk_left hT)]
    refine measure_mono_null (t := ⇑g ⁻¹' (Y ∩ S))
      (fun x hx ↦ ⟨hx.1, hmaps g hg.1 hg.2 x hx.2⟩) ?_
    rw [(AddMonoidHomClass.isometry_of_norm g (hnorm g hg.1)).euclideanHausdorffMeasure_preimage]
    exact measure_mono_null Set.inter_subset_left hYnull
  have h2 : θ.prod ((μHE[n] : Measure (Rn N)).restrict S)
      {p : (Rn N →L[ℝ] Rn N) × Rn N | p.1 p.2 ∈ Y} = θ {g | g ζ ∈ Y} * μHE[n] S := by
    rw [Measure.prod_apply_symm hT]
    have hae : (fun x : Rn N ↦ θ ((fun g ↦ (g, x)) ⁻¹'
        {p : (Rn N →L[ℝ] Rn N) × Rn N | p.1 p.2 ∈ Y})) =ᵐ[(μHE[n] : Measure (Rn N)).restrict S]
        fun _ ↦ θ {g | g ζ ∈ Y} := by
      filter_upwards [ae_restrict_mem hSm] with x hx
      exact horbit x hx
    rw [lintegral_congr_ae hae, lintegral_const, Measure.restrict_apply_univ]
  exact (mul_eq_zero.mp (h2.symm.trans h1)).resolve_right hpos.ne'
/-- **Simon Ch. 3, Theorem 3.6 (p. 80)** (`chapter-03.txt` lines 530–536; the book defers the
proof to [Fed69]/[Ros84]), Step 6 of the frame-averaging argument: Fubini over left cosets.
Let `θ` be a finite and `θ'` a probability measure on `𝓛 = ℝᴺ →L[ℝ] ℝᴺ`, with `(r_k)_# θ = θ`
for `θ'`-a.e. `k`, where `r_k(g) = g k`. If `θ'{g : h g ∈ B} = 0` for `θ`-a.e. `h`, then
`θ(B) = 0`. The set `D = {(h, g) : h g ∈ B}` is measurable (multiplication on the
second-countable normed ring `𝓛` is continuous), and Tonelli in both orders gives
`0 = ∫ θ'{g : h g ∈ B} dθ(h) = (θ ⊗ θ')(D) = ∫ θ(r_g⁻¹ B) dθ'(g) = θ(B) θ'(𝓛) = θ(B)`. -/
theorem Submission.bf_haar_null_of_cosetFibres_null :
    ∀ (N : ℕ) (θ θ' : Measure (Rn N →L[ℝ] Rn N)), IsFiniteMeasure θ → IsProbabilityMeasure θ' →
      (∀ᵐ k ∂θ', Measure.map (fun g ↦ g * k) θ = θ) → ∀ B : Set (Rn N →L[ℝ] Rn N),
        MeasurableSet B → (∀ᵐ h ∂θ, θ' {g | h * g ∈ B} = 0) → θ B = 0 := by
  intro N θ θ' _ _ hinv B hB hfib
  -- Step 1: `D = {(h, g) | h * g ∈ B}` is measurable, as multiplication is continuous.
  set D : Set ((Rn N →L[ℝ] Rn N) × (Rn N →L[ℝ] Rn N)) := {p | p.1 * p.2 ∈ B}
  have hD : MeasurableSet D := measurable_mul hB
  -- Step 2: slicing in `g` first, `(θ ⊗ θ')(D) = ∫ θ'{g | h * g ∈ B} dθ(h) = 0`.
  have h0 : θ.prod θ' D = 0 := by
    rw [Measure.prod_apply hD]
    calc ∫⁻ h, θ' (Prod.mk h ⁻¹' D) ∂θ = ∫⁻ _, 0 ∂θ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hfib] with h hh
          exact hh
      _ = 0 := lintegral_zero
  -- Step 3: slicing in `h` first, `θ{h | h * k ∈ B} = (r_k)_# θ (B) = θ(B)` for `θ'`-a.e. `k`.
  have h1 : θ.prod θ' D = θ B := by
    rw [Measure.prod_apply_symm hD]
    calc ∫⁻ k, θ ((fun h ↦ (h, k)) ⁻¹' D) ∂θ' = ∫⁻ _, θ B ∂θ' := by
          refine lintegral_congr_ae ?_
          filter_upwards [hinv] with k hk
          calc θ ((fun h ↦ (h, k)) ⁻¹' D) = θ ((fun g ↦ g * k) ⁻¹' B) := rfl
            _ = Measure.map (fun g ↦ g * k) θ B :=
              (Measure.map_apply (measurable_mul_const k) hB).symm
            _ = θ B := by rw [hk]
      _ = θ B := by rw [lintegral_const, measure_univ, mul_one]
  -- Step 4: compare the two evaluations of `(θ ⊗ θ')(D)`.
  rw [← h1, h0]
/-- **Projection onto a rotated subspace** (fact (F1) of the frame-averaging step for Simon Ch. 3,
Theorem 3.6). Let `g : ℝᴺ → ℝᴺ` be linear with `g* g = 1` and `V ⊆ ℝᴺ` a subspace. Then the
orthogonal projection onto `gV` is `P_{gV} = g P_V g*`, and `dim gV = dim V`. Since `g* g = 1`,
`g` is injective and restricts to a linear isomorphism `V ≃ gV`. For `x ∈ ℝᴺ`, `g P_V g* x ∈ gV`,
and `(x - g P_V g* x) · g y = (g* x - P_V g* x) · y = 0` for `y ∈ V`; the characterization of the
orthogonal projection then gives `P_{gV} x = g P_V g* x`. -/
theorem Submission.bf_starProjection_map_orthogonal : ∀ (N : ℕ) (g : Rn N →L[ℝ] Rn N), ContinuousLinearMap.adjoint g * g = 1 → ∀ V : Submodule ℝ (Rn N), (V.map (g : Rn N →ₗ[ℝ] Rn N)).starProjection = g * V.starProjection * ContinuousLinearMap.adjoint g ∧ finrank ℝ (V.map (g : Rn N →ₗ[ℝ] Rn N)) = finrank ℝ V := by
  intro N g hg V
  -- Step 1: `g* (g x) = x`, so `g` is injective.
  have hgg : ∀ x, ContinuousLinearMap.adjoint g (g x) = x := by
    intro x
    rw [← mul_apply_eq_comp, hg, one_apply_eq_self]
  have hinj : Function.Injective g := Function.LeftInverse.injective hgg
  refine ⟨?_, ?_⟩
  -- Step 3: `v = g P_V g* x` lies in `gV` and `x - v ⊥ gV`, so `P_{gV} x = v`.
  · ext1 x
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · exact Submodule.mem_map_of_mem (V.starProjection_apply_mem _)
    · rintro _ ⟨y, hy, rfl⟩
      change inner ℝ (x - g (V.starProjection (ContinuousLinearMap.adjoint g x))) (g y) = 0
      rw [inner_sub_left, ← ContinuousLinearMap.adjoint_inner_left,
        ← ContinuousLinearMap.adjoint_inner_left, hgg, ← inner_sub_left]
      exact Submodule.starProjection_inner_eq_zero _ _ hy
  -- Step 2: `g` restricts to a linear isomorphism `V ≃ gV`, so `dim gV = dim V`.
  · exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj V)).symm
/-- Used for Simon Ch. 3, Theorem 3.6 (Besicovitch–Federer), Step 9(b) of the frame averaging
`bf_frameAveraging_null`: `O(N)` acts transitively on the linear subspaces of `ℝᴺ` of each
dimension. If `dim W₀ = dim W`, matching orthonormal bases give a linear isometric equivalence
`e : W₀ ≃ W`; the isometry `x ↦ e x` of `W₀` into `ℝᴺ` extends to a linear isometry `h` of `ℝᴺ`
(`LinearIsometry.extend`), so `h* h = 1`, and `h = e` on `W₀`, so `h(W₀) = e(W₀) = W`. -/
theorem Submission.bf_orthogonal_exists_map_eq : ∀ (N : ℕ) (W₀ W : Submodule ℝ (Rn N)), finrank ℝ W₀ = finrank ℝ W → ∃ h : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint h * h = 1 ∧ W₀.map (h : Rn N →ₗ[ℝ] Rn N) = W := by
  intro N W₀ W hdim
  -- Step 1: matching orthonormal bases of `W₀` and `W` give a linear isometric equivalence.
  let e : W₀ ≃ₗᵢ[ℝ] W := (stdOrthonormalBasis ℝ W₀).repr.trans
    ((stdOrthonormalBasis ℝ W).reindex (finCongr hdim.symm)).repr.symm
  -- Step 2: the isometry `x ↦ e x` of `W₀` into `ℝᴺ` extends to a linear isometry `h` of `ℝᴺ`.
  let L : W₀ →ₗᵢ[ℝ] Rn N := W.subtypeₗᵢ.comp e.toLinearIsometry
  let h : Rn N →L[ℝ] Rn N := L.extend.toContinuousLinearMap
  have hL : ∀ x : W₀, h x = (e x : Rn N) := fun x ↦ L.extend_apply x
  refine ⟨h, ?_, ?_⟩
  -- Step 3: `h` preserves inner products, hence `h* h = 1`.
  · ext1 x
    refine ext_inner_right ℝ fun y ↦ ?_
    rw [mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_left, one_apply_eq_self]
    exact L.extend.inner_map_map x y
  -- Step 4: `h` agrees with `e` on `W₀`, hence `h(W₀) = e(W₀) = W`.
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change h x ∈ W
      rw [hL ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).2
    · intro w hw
      refine ⟨(e.symm ⟨w, hw⟩ : Rn N), (e.symm ⟨w, hw⟩).2, ?_⟩
      change h (e.symm ⟨w, hw⟩ : Rn N) = w
      rw [hL (e.symm ⟨w, hw⟩), LinearIsometryEquiv.apply_symm_apply]

/-- **Null sets of rotated plane–direction pairs** (Steps 5–6 of the frame-averaging step for
Simon Ch. 3, Theorem 3.6). Let `Bad ⊆ ℝᴺ × 𝓛 × ℝᴺ` be measurable and `a ∈ ℝᴺ` with
`Hⁿ({x ∈ H : |x| = 1, (a, P_H, x) ∈ Bad}) = 0` for every `(n+1)`-plane `H`. Let `θ` be a
probability on `𝓛` carried by `{g : g* g = 1}` and invariant under `g ↦ g k` whenever `k* k = 1`,
`V` an `(n+1)`-plane with `0 < Hⁿ(S(V)) < ∞`, `S(V) = {x ∈ V : |x| = 1}`, and `ζ ∈ S(V)`. Then
`θ(B) = 0` for `B = {g : (a, g P_V g*, g ζ) ∈ Bad}`. Let `θ'` be a bi-invariant probability on the
stabilizer `K` of `Vᗮ`. By Fubini over the cosets `h K` it suffices that `θ'{g' : h g' ∈ B} = 0`
for every `h` with `h* h = 1`. For such `h`, `H = hV` is an `(n+1)`-plane with `P_H = h P_V h*`, and
`h` is an isometry, so `Y = {y : (a, P_H, h y) ∈ Bad}` has `Hⁿ(Y ∩ S(V)) = 0`; the orbit law of
`θ'` gives `θ'{g' : g' ζ ∈ Y} = 0`. Every `g' ∈ K` maps `V` onto `V`, so `(h g') P_V (h g')* = P_H`
and `h g' ∈ B` iff `g' ζ ∈ Y`. -/
theorem Submission.bf_haar_planeDirection_null : ∀ (n N : ℕ) (Bad : Set (Rn N × (Rn N →L[ℝ] Rn N) × Rn N)), MeasurableSet Bad → ∀ a : Rn N, (∀ H : Submodule ℝ (Rn N), finrank ℝ H = n + 1 → μHE[n] {x | x ∈ H ∧ ‖x‖ = 1 ∧ (a, H.starProjection, x) ∈ Bad} = 0) → ∀ θ : Measure (Rn N →L[ℝ] Rn N), IsProbabilityMeasure θ → (∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1) → (∀ k : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint k * k = 1 → Measure.map (fun g ↦ g * k) θ = θ) → ∀ V : Submodule ℝ (Rn N), finrank ℝ V = n + 1 → 0 < μHE[n] {x : Rn N | x ∈ V ∧ ‖x‖ = 1} → μHE[n] {x : Rn N | x ∈ V ∧ ‖x‖ = 1} < ∞ → ∀ ζ ∈ V, ‖ζ‖ = 1 → θ {g | (a, g * V.starProjection * ContinuousLinearMap.adjoint g, g ζ) ∈ Bad} = 0 := by
  intro n N Bad hBad a hnull θ _ hθO hθR V hV hS0 hSfin ζ hζV hζ1
  -- Step 1: a probability `θ'` carried by the stabilizer `K = {g' : g'* g' = 1, g' = 1 on Vᗮ}`,
  -- invariant under left and right translation by elements of `K`.
  obtain ⟨θ', hθ'P, hθ'K, hθ'inv⟩ := Submission.bf_orthStabilizer_haar_exists N Vᗮ
  -- Maps with `g* g = 1` preserve inner products.
  have hinner : ∀ g : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint g * g = 1 →
      ∀ x y : Rn N, inner ℝ (g x) (g y) = inner ℝ x y :=
    fun g hg ↦ g.inner_map_map_iff_adjoint_comp_self.mpr hg
  -- Step 2: `B` is Borel, as `g ↦ (a, g P_V g*, g ζ)` is continuous (the adjoint is an isometry).
  set B : Set (Rn N →L[ℝ] Rn N) :=
    {g | (a, g * V.starProjection * ContinuousLinearMap.adjoint g, g ζ) ∈ Bad}
  have hBm : MeasurableSet B := by
    have hadj : Continuous fun g : Rn N →L[ℝ] Rn N ↦ ContinuousLinearMap.adjoint g :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn N) (F := Rn N)).continuous
    have hm : Measurable fun g : Rn N →L[ℝ] Rn N ↦
        (a, g * V.starProjection * ContinuousLinearMap.adjoint g, g ζ) :=
      measurable_const.prodMk ((((continuous_id.mul continuous_const).mul hadj).measurable).prodMk
        (ContinuousLinearMap.measurable_apply ζ))
    exact hm hBad
  -- Step 3: Fubini over the cosets `h K`. As `θ'`-a.e. `k` has `k* k = 1`, `θ` is invariant under
  -- `g ↦ g k` for `θ'`-a.e. `k`; it remains to show `θ'{g' | h g' ∈ B} = 0` whenever `h* h = 1`.
  refine Submission.bf_haar_null_of_cosetFibres_null N θ θ' inferInstance hθ'P ?_ B hBm ?_
  · filter_upwards [hθ'K] with k hk
    exact hθR k hk.1
  filter_upwards [hθO] with h hh
  -- Step 4: `H = hV` is an `(n+1)`-plane with `P_H = h P_V h*`, and `h` is an isometry.
  obtain ⟨hPH, hHdim⟩ := Submission.bf_starProjection_map_orthogonal N h hh V
  have hiso : Isometry h := h.isometry_iff_adjoint_comp_self.mpr hh
  -- Step 5: `Y = {y | (a, P_H, h y) ∈ Bad}` is Borel, and `h` maps `Y ∩ S(V)` into the `Hⁿ`-null
  -- set `{x ∈ H | ‖x‖ = 1, (a, P_H, x) ∈ Bad}`; as `h` is an isometry, `Hⁿ(Y ∩ S(V)) = 0`.
  set Y : Set (Rn N) :=
    {y | (a, (V.map (h : Rn N →ₗ[ℝ] Rn N)).starProjection, h y) ∈ Bad}
  have hYm : MeasurableSet Y := by
    have hm : Measurable fun y : Rn N ↦
        (a, (V.map (h : Rn N →ₗ[ℝ] Rn N)).starProjection, h y) :=
      measurable_const.prodMk (measurable_const.prodMk h.continuous.measurable)
    exact hm hBad
  have hYnull : μHE[n] (Y ∩ {x : Rn N | x ∈ V ∧ ‖x‖ = 1}) = 0 := by
    rw [← hiso.euclideanHausdorffMeasure_image]
    refine measure_mono_null ?_ (hnull (V.map (h : Rn N →ₗ[ℝ] Rn N)) (hHdim.trans hV))
    rintro _ ⟨y, ⟨hyY, hyV, hy1⟩, rfl⟩
    exact ⟨Submodule.mem_map_of_mem hyV, (hiso.norm_map_of_map_zero (map_zero h) y).trans hy1,
      hyY⟩
  -- Step 6: the orbit law of `θ'` gives `θ'{g' | g' ζ ∈ Y} = 0`.
  have hYθ' : θ' {g' | g' ζ ∈ Y} = 0 :=
    Submission.bf_stabilizerOrbit_null N n V θ' hθ'P hθ'K hθ'inv hS0 hSfin ζ hζV hζ1 Y hYm hYnull
  -- Step 7: for `θ'`-a.e. `g'`, `g' ∈ K` and `g' ζ ∉ Y`; and `g' ∈ K`, `h g' ∈ B` give `g' ζ ∈ Y`.
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hθ'K, measure_eq_zero_iff_ae_notMem.mp hYθ'] with g' hK hg'Y hg'B
  -- (a) `g'V ⊆ V`: for `x ∈ V` and `y ∈ Vᗮ`, `y · g'x = g'y · g'x = y · x = 0`. Since
  -- `dim g'V = dim V`, `g'V = V`, so `g' P_V g'* = P_{g'V} = P_V`.
  obtain ⟨hPg', hdg'⟩ := Submission.bf_starProjection_map_orthogonal N g' hK.1 V
  have hle : V.map (g' : Rn N →ₗ[ℝ] Rn N) ≤ V := by
    rintro _ ⟨x, hxV, rfl⟩
    rw [← Submodule.orthogonal_orthogonal V, Submodule.mem_orthogonal]
    intro y hy
    change inner ℝ y (g' x) = 0
    rw [← hK.2 y hy, hinner g' hK.1]
    exact Submodule.inner_left_of_mem_orthogonal hxV hy
  have hstar : ∀ W₁ W₂ : Submodule ℝ (Rn N), W₁ = W₂ →
      W₁.starProjection = W₂.starProjection := by
    rintro W₁ W₂ rfl
    rfl
  have hPV : g' * V.starProjection * ContinuousLinearMap.adjoint g' = V.starProjection :=
    hPg'.symm.trans (hstar _ _ (Submodule.eq_of_le_of_finrank_eq hle hdg'))
  -- (b) `(h g')* = g'* h*`, so `(h g') P_V (h g')* = h (g' P_V g'*) h* = h P_V h* = P_H`.
  have hcoset : h * g' * V.starProjection * ContinuousLinearMap.adjoint (h * g') =
      (V.map (h : Rn N →ₗ[ℝ] Rn N)).starProjection := by
    calc h * g' * V.starProjection * ContinuousLinearMap.adjoint (h * g')
        = h * (g' * V.starProjection * ContinuousLinearMap.adjoint g') *
            ContinuousLinearMap.adjoint h := by
          rw [show ContinuousLinearMap.adjoint (h * g') =
            ContinuousLinearMap.adjoint g' * ContinuousLinearMap.adjoint h from
              ContinuousLinearMap.adjoint_comp h g']
          simp only [mul_assoc]
      _ = (V.map (h : Rn N →ₗ[ℝ] Rn N)).starProjection := by rw [hPV, hPH]
  -- (c) Hence `h g' ∈ B` says `(a, P_H, h (g' ζ)) ∈ Bad`, i.e. `g' ζ ∈ Y`.
  have hg'B' : (a, h * g' * V.starProjection * ContinuousLinearMap.adjoint (h * g'),
      (h * g') ζ) ∈ Bad := hg'B
  rw [hcoset] at hg'B'
  exact hg'Y hg'B'

/-- **For each point `a`, Haar-a.e. rotation of an `n`-plane is not exceptional** (Steps 2–6 of
the frame-averaging step for Simon Ch. 3, Theorem 3.6). Let `f₁, …, f_ℓ` be an orthonormal basis
of `W₀ᗮ`. Each `V_j = W₀ ⊔ span{f_j}` is `(n+1)`-dimensional and contains the unit vector `f_j`,
so `B_j = {g : (a, g P_{V_j} g*, g f_j) ∈ Bad}` is `θ`-null by `bf_haar_planeDirection_null`. If
`g* g = 1` and `(a, g P_{W₀} g*) ∈ Exc`, then `W = gW₀` is `n`-dimensional with
`P_W = g P_{W₀} g*`, and the `g f_j` are orthonormal in `Wᗮ`; so (h2_a) and
`W ⊔ span{g f_j} = g V_j` put `g` in some `B_j`. Hence the exceptional set lies in the `θ`-null
set `{g* g ≠ 1} ∪ ⋃_j B_j`. -/
theorem Submission.bf_haar_excPointwise_null : ∀ (n ℓ : ℕ) (Exc : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)))) (Bad : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)) × Rn (n + ℓ))), MeasurableSet Bad → (∀ H : Submodule ℝ (Rn (n + ℓ)), finrank ℝ H = n + 1 → 0 < μHE[n] {x : Rn (n + ℓ) | x ∈ H ∧ ‖x‖ = 1} ∧ μHE[n] {x : Rn (n + ℓ) | x ∈ H ∧ ‖x‖ = 1} < ∞) → ∀ a : Rn (n + ℓ), (∀ H : Submodule ℝ (Rn (n + ℓ)), finrank ℝ H = n + 1 → μHE[n] {x | x ∈ H ∧ ‖x‖ = 1 ∧ (a, H.starProjection, x) ∈ Bad} = 0) → (∀ W : Submodule ℝ (Rn (n + ℓ)), finrank ℝ W = n → (a, W.starProjection) ∈ Exc → ∀ u : Fin ℓ → Rn (n + ℓ), Orthonormal ℝ u → (∀ j, u j ∈ Wᗮ) → ∃ j, (a, (W ⊔ Submodule.span ℝ {u j}).starProjection, u j) ∈ Bad) → ∀ θ : Measure (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)), IsProbabilityMeasure θ → (∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1) → (∀ k : Rn (n + ℓ) →L[ℝ] Rn (n + ℓ), ContinuousLinearMap.adjoint k * k = 1 → Measure.map (fun g ↦ g * k) θ = θ) → ∀ W₀ : Submodule ℝ (Rn (n + ℓ)), finrank ℝ W₀ = n → θ {g | (a, g * W₀.starProjection * ContinuousLinearMap.adjoint g) ∈ Exc} = 0 := by
  intro n ℓ Exc Bad hBad hS a h1 h2 θ hθP hθG hθR W₀ hW₀
  -- Step 1: an orthonormal basis `f` of `W₀ᗮ`, indexed by `Fin ℓ`.
  have hdim : finrank ℝ W₀ᗮ = ℓ := by
    have := W₀.finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace_fin, hW₀] at this
    omega
  let b := (stdOrthonormalBasis ℝ W₀ᗮ).reindex (finCongr hdim)
  let f : Fin ℓ → Rn (n + ℓ) := fun j ↦ (b j : Rn (n + ℓ))
  have hf : Orthonormal ℝ f := b.orthonormal.comp_linearIsometry W₀ᗮ.subtypeₗᵢ
  have hfW : ∀ j, f j ∈ W₀ᗮ := fun j ↦ (b j).2
  -- Step 2: the planes `V_j = W₀ ⊔ span{f_j}` are `(n+1)`-dimensional.
  let V : Fin ℓ → Submodule ℝ (Rn (n + ℓ)) := fun j ↦ W₀ ⊔ Submodule.span ℝ {f j}
  have hVdim : ∀ j, finrank ℝ (V j) = n + 1 := by
    intro j
    have hinf : W₀ ⊓ Submodule.span ℝ {f j} = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxW, hxs⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxs
      have h0 : inner ℝ (f j) (c • f j) = 0 := Submodule.inner_left_of_mem_orthogonal hxW (hfW j)
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hf.1 j, one_pow, mul_one] at h0
      rw [h0, zero_smul]
      exact Submodule.zero_mem _
    have := Submodule.finrank_sup_add_finrank_inf_eq W₀ (Submodule.span ℝ {f j})
    rw [hinf, finrank_bot, finrank_span_singleton (hf.ne_zero j), hW₀] at this
    exact this
  -- Step 3: each `B_j = {g : (a, g P_{V_j} g*, g f_j) ∈ Bad}` is `θ`-null.
  have hnull : ∀ j, θ {g | (a, g * (V j).starProjection * ContinuousLinearMap.adjoint g,
      g (f j)) ∈ Bad} = 0 := fun j ↦
    Submission.bf_haar_planeDirection_null n (n + ℓ) Bad hBad a h1 θ hθP hθG hθR (V j) (hVdim j)
      (hS _ (hVdim j)).1 (hS _ (hVdim j)).2 (f j)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)) (hf.1 j)
  -- Step 5: the exceptional set lies in `{g* g ≠ 1} ∪ ⋃_j B_j`, a `θ`-null set.
  refine measure_mono_null (t := {g | ¬ContinuousLinearMap.adjoint g * g = 1} ∪
    ⋃ j, {g | (a, g * (V j).starProjection * ContinuousLinearMap.adjoint g, g (f j)) ∈ Bad})
    ?_ (measure_union_null hθG (measure_iUnion_null hnull))
  intro g hg
  by_cases hgG : ContinuousLinearMap.adjoint g * g = 1
  swap
  · exact Or.inl hgG
  -- Step 4: for orthogonal `g`, the bad plane `W = gW₀` gives a bad direction `g f_j`.
  right
  have hinner : ∀ x y, inner ℝ (g x) (g y) = inner ℝ x y := by
    intro x y
    rw [← ContinuousLinearMap.adjoint_inner_right, ← mul_apply_eq_comp, hgG, one_apply_eq_self]
  obtain ⟨hP₀, hd₀⟩ := Submission.bf_starProjection_map_orthogonal (n + ℓ) g hgG W₀
  set W := W₀.map (g : Rn (n + ℓ) →ₗ[ℝ] Rn (n + ℓ))
  have hWexc : (a, W.starProjection) ∈ Exc := by
    rw [hP₀]
    exact hg
  have hu : Orthonormal ℝ (fun j ↦ g (f j)) := by
    rw [orthonormal_iff_ite] at hf ⊢
    intro i j
    rw [hinner]
    exact hf i j
  have huW : ∀ j, g (f j) ∈ Wᗮ := by
    intro j
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨w, hw, rfl⟩
    exact (hinner w (f j)).trans (Submodule.inner_right_of_mem_orthogonal hw (hfW j))
  obtain ⟨j, hj⟩ := h2 W (hd₀.trans hW₀) hWexc (fun j ↦ g (f j)) hu huW
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  -- `W ⊔ span{g f_j} = g V_j`; rewrite the projection through this equality of subspaces.
  have hsup : W ⊔ Submodule.span ℝ {g (f j)} = (V j).map (g : Rn (n + ℓ) →ₗ[ℝ] Rn (n + ℓ)) := by
    rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton]
    rfl
  have key : ∀ W₁ W₂ : Submodule ℝ (Rn (n + ℓ)), W₁ = W₂ →
      W₁.starProjection = W₂.starProjection := by
    rintro _ _ rfl
    rfl
  rw [key _ _ hsup, (Submission.bf_starProjection_map_orthogonal (n + ℓ) g hgG (V j)).1] at hj
  exact hj
/-- **From Haar-random rotated planes to Lebesgue-a.e. frames** (Steps 8–10 of the frame-averaging
step for Simon Ch. 3, Theorem 3.6). Let `θ` be a probability measure on `𝓛 = ℝᴺ →L[ℝ] ℝᴺ` with
`g* g = 1` for `θ`-a.e. `g`, invariant under `g ↦ g k` for every `k` with `k* k = 1`, let
`dim W₀ = n` and let `Q ⊆ 𝓛` be Borel with `θ{g | g P_{W₀} g* ∈ Q} = 0`. If the frame projection
is continuous on the linearly independent frames, then for Lebesgue-a.e. frame `v ∈ (ℝᴺ)ⁿ`, if
`v` is linearly independent then `P_{span v} ∉ Q`. The set `𝒮` of bad frames is Borel. For every
frame `v`, `θ{g | g·v ∈ 𝒮} = 0`: if `v` is dependent then so is `g·v` for injective `g`; otherwise
`span v = h W₀` with `h* h = 1`, so `P_{span(g·v)} = (gh) P_{W₀} (gh)*` and right invariance
reduces to `θ{g | g P_{W₀} g* ∈ Q} = 0`. As `v ↦ g·v` preserves Lebesgue measure for `g* g = 1`,
Tonelli on `θ ⊗ λ` gives `λ(𝒮) = ∫ λ{v | g·v ∈ 𝒮} dθ = ∫ θ{g | g·v ∈ 𝒮} dλ = 0`. -/
theorem Submission.bf_haar_null_to_frames : ∀ (N n : ℕ), ContinuousOn (fun v : Fin n → Rn N ↦ frameProjection v) {v | LinearIndependent ℝ v} → ∀ θ : Measure (Rn N →L[ℝ] Rn N), IsProbabilityMeasure θ → (∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1) → (∀ k : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint k * k = 1 → Measure.map (fun g ↦ g * k) θ = θ) → ∀ W₀ : Submodule ℝ (Rn N), finrank ℝ W₀ = n → ∀ Q : Set (Rn N →L[ℝ] Rn N), MeasurableSet Q → θ {g | g * W₀.starProjection * ContinuousLinearMap.adjoint g ∈ Q} = 0 → ForAlmostAllProjections N n (fun p ↦ p ∉ Q) := by
  intro N n hcont θ hθ hθO hθR W₀ hW₀ Q hQ hnull
  classical
  -- Step 1: `𝒮 = {v ∈ 𝒱 | P_{span v} ∈ Q}` is Borel, as `frameProjection` is continuous on the
  -- open set `𝒱` of linearly independent frames.
  set 𝒱 : Set (Fin n → Rn N) := {v | LinearIndependent ℝ v} with h𝒱
  have h𝒱o : IsOpen 𝒱 := isOpen_setOfPred_linearIndependent
  set S : Set (Fin n → Rn N) := {v | LinearIndependent ℝ v ∧ frameProjection v ∈ Q} with hS
  have hSm : MeasurableSet S := by
    have hF : Measurable (𝒱.piecewise (fun v ↦ frameProjection v)
        (fun _ ↦ (0 : Rn N →L[ℝ] Rn N))) :=
      ContinuousOn.measurable_piecewise hcont continuousOn_const h𝒱o.measurableSet
    have hSF : S = 𝒱 ∩ (𝒱.piecewise (fun v ↦ frameProjection v)
        (fun _ ↦ (0 : Rn N →L[ℝ] Rn N))) ⁻¹' Q := by
      ext v
      simp only [hS, h𝒱, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨hv, hq⟩
        exact ⟨hv, by rwa [Set.piecewise_eq_of_mem _ _ _ hv]⟩
      · rintro ⟨hv, hq⟩
        exact ⟨hv, by rwa [Set.piecewise_eq_of_mem _ _ _ hv] at hq⟩
    rw [hSF]
    exact h𝒱o.measurableSet.inter (hF hQ)
  -- Step 2: `M = {(g, v) | g·v ∈ 𝒮}` is measurable, as `(g, v) ↦ g·v` is continuous.
  set M : Set ((Rn N →L[ℝ] Rn N) × (Fin n → Rn N)) := {p | (fun i ↦ p.1 (p.2 i)) ∈ S} with hM
  have hMm : MeasurableSet M := by
    have hc : Continuous (fun p : (Rn N →L[ℝ] Rn N) × (Fin n → Rn N) ↦ fun i ↦ p.1 (p.2 i)) :=
      continuous_pi fun i ↦ continuous_fst.clm_apply ((continuous_apply i).comp continuous_snd)
    exact hc.measurable hSm
  have hA : MeasurableSet {g : Rn N →L[ℝ] Rn N |
      g * W₀.starProjection * ContinuousLinearMap.adjoint g ∈ Q} :=
    ((continuous_id.mul continuous_const).mul
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn N) (F := Rn N)).continuous).measurable hQ
  -- Step 3: `θ{g | g·v ∈ 𝒮} = 0` for every frame `v`.
  have hfib : ∀ v : Fin n → Rn N, θ {g : Rn N →L[ℝ] Rn N | (fun i ↦ g (v i)) ∈ S} = 0 := by
    intro v
    by_cases hv : LinearIndependent ℝ v
    · -- `span v = h W₀` for some `h` with `h* h = 1`.
      have hspan : finrank ℝ (Submodule.span ℝ (Set.range v)) = n := by
        rw [finrank_span_eq_card hv, Fintype.card_fin]
      obtain ⟨h, hh, hmap⟩ := Submission.bf_orthogonal_exists_map_eq N W₀
        (Submodule.span ℝ (Set.range v)) (hW₀.trans hspan.symm)
      have hsub : {g : Rn N →L[ℝ] Rn N | (fun i ↦ g (v i)) ∈ S} ⊆
          {g | ¬ContinuousLinearMap.adjoint g * g = 1} ∪ (fun g ↦ g * h) ⁻¹'
            {g | g * W₀.starProjection * ContinuousLinearMap.adjoint g ∈ Q} := by
        intro g hg
        by_cases hg1 : ContinuousLinearMap.adjoint g * g = 1
        · right
          -- `(gh)* (gh) = h* (g* g) h = 1` and `span(g·v) = g h W₀`, so
          -- `P_{span(g·v)} = (gh) P_{W₀} (gh)*`.
          have hgh : ContinuousLinearMap.adjoint (g * h) * (g * h) = 1 := by
            rw [show ContinuousLinearMap.adjoint (g * h) =
                ContinuousLinearMap.adjoint h * ContinuousLinearMap.adjoint g from
              ContinuousLinearMap.adjoint_comp g h]
            calc ContinuousLinearMap.adjoint h * ContinuousLinearMap.adjoint g * (g * h)
                = ContinuousLinearMap.adjoint h * (ContinuousLinearMap.adjoint g * g) * h := by
                  simp only [mul_assoc]
              _ = 1 := by rw [hg1, mul_one, hh]
          have hspan' : Submodule.span ℝ (Set.range fun i ↦ g (v i)) =
              W₀.map ((g * h : Rn N →L[ℝ] Rn N) : Rn N →ₗ[ℝ] Rn N) := by
            have hr : Set.range (fun i ↦ g (v i)) = (g : Rn N →ₗ[ℝ] Rn N) '' Set.range v := by
              rw [← Set.range_comp]
              rfl
            rw [hr, Submodule.span_image, ← hmap, ← Submodule.map_comp]
            rfl
          have hPeq : ∀ W₁ W₂ : Submodule ℝ (Rn N), W₁ = W₂ →
              W₁.starProjection = W₂.starProjection := by
            rintro W₁ W₂ rfl
            rfl
          have hP : frameProjection (fun i ↦ g (v i)) =
              g * h * W₀.starProjection * ContinuousLinearMap.adjoint (g * h) := by
            unfold frameProjection
            rw [hPeq _ _ hspan']
            exact (Submission.bf_starProjection_map_orthogonal N (g * h) hgh W₀).1
          change g * h * W₀.starProjection * ContinuousLinearMap.adjoint (g * h) ∈ Q
          rw [← hP]
          exact hg.2
        · left
          exact hg1
      -- By right invariance under `h`, `θ{g | g h ∈ A} = θ(A) = 0`.
      refine measure_mono_null hsub (measure_union_null hθO ?_)
      rw [← Measure.map_apply (measurable_mul_const h) hA, hθR h hh]
      exact hnull
    · -- If `v` is dependent, so is `g·v` for every injective `g`.
      refine measure_mono_null ?_ hθO
      intro g hg hg1
      exact hv (LinearIndependent.of_comp (g : Rn N →ₗ[ℝ] Rn N) hg.1)
  -- Step 5 (Tonelli): `∫ λ{v | g·v ∈ 𝒮} dθ = (θ ⊗ λ)(M) = ∫ θ{g | g·v ∈ 𝒮} dλ = 0`, so
  -- `λ{v | g·v ∈ 𝒮} = 0` for some `g` with `g* g = 1`.
  have hprod : (θ.prod volume) M = 0 := by
    rw [Measure.prod_apply_symm hMm]
    have h0 : (fun v : Fin n → Rn N ↦ θ ((fun g ↦ (g, v)) ⁻¹' M)) = fun _ ↦ 0 := by
      funext v
      exact hfib v
    rw [h0, lintegral_zero]
  rw [Measure.prod_apply hMm] at hprod
  have hmeas : Measurable (fun g : Rn N →L[ℝ] Rn N ↦ (volume : Measure (Fin n → Rn N))
      (Prod.mk g ⁻¹' M)) := measurable_measure_prodMk_left hMm
  have hae := (lintegral_eq_zero_iff hmeas).mp hprod
  have : (ae θ).NeBot := ae_neBot.mpr (IsProbabilityMeasure.ne_zero θ)
  obtain ⟨g, hg1, hg0⟩ := (hθO.and hae).exists
  -- Step 4: `g` is a linear isometry of `ℝᴺ` onto itself, so `v ↦ g·v` preserves `λ`.
  have hgg : ∀ x, ContinuousLinearMap.adjoint g (g x) = x := by
    intro x
    rw [← mul_apply_eq_comp, hg1, one_apply_eq_self]
  have hnorm : ∀ x, ‖g x‖ = ‖x‖ := by
    intro x
    have h2 : inner ℝ (g x) (g x) = inner ℝ x x := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hgg]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h2
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
  let gi : Rn N →ₗᵢ[ℝ] Rn N := { toLinearMap := (g : Rn N →ₗ[ℝ] Rn N), norm_map' := hnorm }
  have hsurj : Function.Surjective gi :=
    LinearMap.surjective_of_injective (f := (g : Rn N →ₗ[ℝ] Rn N)) gi.injective
  have hmp : MeasurePreserving (fun v : Fin n → Rn N ↦ fun i ↦ g (v i)) volume volume :=
    measurePreserving_pi (fun _ ↦ volume) (fun _ ↦ volume)
      (fun _ ↦ (LinearIsometryEquiv.ofSurjective gi hsurj).measurePreserving)
  have hS0 : (volume : Measure (Fin n → Rn N)) S = 0 := by
    rw [← hmp.measure_preimage hSm.nullMeasurableSet]
    exact hg0
  -- Step 6: `λ(𝒮) = 0` is the claim.
  rw [ForAlmostAllProjections, ae_iff]
  refine measure_mono_null ?_ hS0
  intro v hv
  simp only [Set.mem_ofPred_eq, not_imp, not_not] at hv
  exact hv
/-- **Uniform `Hⁿ`-measure of open balls in `n`-planes** (flat-ball step of the sphere-cap bounds
for the Besicovitch–Federer theorem; Dall'Alba, Lemma 4.15; Mattila, Ch. 18). For each `n` the
constant `ω = Lⁿ(B_{ℝⁿ}(0, 1)) > 0` satisfies `Hⁿ(T ∩ B(w, ρ)) = ω ρⁿ` for every `n`-dimensional
subspace `T ⊆ ℝᴺ`, every `w ∈ T` and every `ρ > 0`. An orthonormal basis of `T` gives a linear
isometric equivalence `e : T ≃ ℝⁿ`, and `ι = e⁻¹` followed by `T ↪ ℝᴺ` is an isometry with
`T ∩ B(w, ρ) = ι(B(e w, ρ))`; `Hⁿ` is invariant under isometries, equals `Lⁿ` on `ℝⁿ`, and
`Lⁿ(B(z, ρ)) = ρⁿ Lⁿ(B(0, 1))`. -/
theorem Submission.bf_planeBall_measure_uniform : ∀ n : ℕ, ∃ ω : ℝ, 0 < ω ∧ ∀ (N : ℕ) (T : Submodule ℝ (Rn N)), finrank ℝ T = n → ∀ w ∈ T, ∀ ρ : ℝ, 0 < ρ → μHE[n] ((T : Set (Rn N)) ∩ Metric.ball w ρ) = ENNReal.ofReal (ω * ρ ^ n) := by
  intro n
  -- Step 1: `ω = Lⁿ(B(0, 1))` is positive and finite, `Lⁿ` being an additive Haar measure on
  -- the proper space `ℝⁿ`; it depends only on `n`.
  have hB₀pos : 0 < volume (Metric.ball (0 : Rn n) 1) := Metric.measure_ball_pos _ _ one_pos
  have hB₀fin : volume (Metric.ball (0 : Rn n) 1) < ∞ := measure_ball_lt_top
  refine ⟨(volume (Metric.ball (0 : Rn n) 1)).toReal, ENNReal.toReal_pos hB₀pos.ne' hB₀fin.ne,
    fun N T hT w hw ρ hρ ↦ ?_⟩
  -- Step 2: an orthonormal basis of `T` indexed by `Fin n` gives a linear isometric equivalence
  -- `e : T ≃ ℝⁿ`, and `ι = (↑) ∘ e⁻¹ : ℝⁿ → ℝᴺ` is an isometry with `ι (e x) = x` on `T`.
  let e : T ≃ₗᵢ[ℝ] Rn n := ((stdOrthonormalBasis ℝ T).reindex (finCongr hT)).repr
  let ι : Rn n → Rn N := fun z ↦ (e.symm z : Rn N)
  have hι : Isometry ι := isometry_subtype_coe.comp e.symm.isometry
  have hιe : ∀ x : T, ι (e x) = x := fun x ↦ by simp [ι]
  have hιw : ι (e ⟨w, hw⟩) = w := hιe ⟨w, hw⟩
  -- Step 3: `T ∩ B(w, ρ) = ι(B(e w, ρ))`, since `ι` preserves distances.
  have himg : (T : Set (Rn N)) ∩ Metric.ball w ρ = ι '' Metric.ball (e ⟨w, hw⟩) ρ := by
    ext x
    constructor
    · rintro ⟨hxT, hx⟩
      refine ⟨e ⟨x, hxT⟩, ?_, hιe ⟨x, hxT⟩⟩
      rw [Metric.mem_ball, ← hι.dist_eq, hιe, hιw]
      exact hx
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(e.symm z).2, ?_⟩
      rw [Metric.mem_ball, ← hιw, hι.dist_eq]
      exact hz
  -- Step 4: isometry invariance of `Hⁿ`, `Hⁿ = Lⁿ` on `ℝⁿ` and the Haar scaling law for balls.
  rw [himg, hι.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
    Measure.addHaar_ball_of_pos _ _ hρ, finrank_euclideanSpace_fin,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hB₀fin.ne, mul_comm]
/-- **Projection lower comparison for caps of the unit sphere of an `(n+1)`-plane** (the graph
map over `T_ζ` and the orthogonal projection `π_ζ`; Dall'Alba, Lemma 4.15; Mattila, Ch. 18).
For a subspace `H ⊆ ℝᴺ` with `dim H = n + 1` and a unit vector `ζ ∈ H`, the `n`-plane
`T = (ℝζ)^⊥ ∩ H` satisfies `Hⁿ(T ∩ B(0, ρ/2)) ≤ Hⁿ(S(H) ∩ B(ζ, ρ))` for `0 < ρ ≤ 2`, where
`S(H) = {θ ∈ H : |θ| = 1}`. Every `w ∈ T ∩ B(0, ρ/2)` is `π ξ` for the lift
`ξ = w + (1 - |w|²)^{1/2} ζ ∈ S(H) ∩ B(ζ, ρ)`, where `π` is the `1`-Lipschitz orthogonal
projection onto `T`. -/
theorem Submission.bf_sphereCap_lower_comparison : ∀ (n N : ℕ) (H : Submodule ℝ (Rn N)), finrank ℝ H = n + 1 → ∀ ζ ∈ H, ‖ζ‖ = 1 → ∃ T : Submodule ℝ (Rn N), finrank ℝ T = n ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 2 → μHE[n] ((T : Set (Rn N)) ∩ Metric.ball 0 (ρ / 2)) ≤ μHE[n] ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ) := by
  intro n N H hH ζ hζ hζ1
  -- Step 1: the plane `T = (ℝζ)^⊥ ∩ H` has dimension `n`, since `ℝζ ⊆ H` is a line.
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ1
  have hTdim : finrank ℝ ((ℝ ∙ ζ)ᗮ ⊓ H : Submodule ℝ (Rn N)) = n :=
    Submodule.finrank_add_inf_finrank_orthogonal' ((Submodule.span_singleton_le_iff_mem ζ H).2 hζ)
      (by rw [finrank_span_singleton hζ0, hH, add_comm])
  refine ⟨(ℝ ∙ ζ)ᗮ ⊓ H, hTdim, fun ρ hρ hρ2 ↦ ?_⟩
  set T : Submodule ℝ (Rn N) := (ℝ ∙ ζ)ᗮ ⊓ H
  -- Step 2: the orthogonal projection `π` onto `T` sends `ζ` to `0`, since `ζ ⊥ T`.
  have hπζ : T.starProjection ζ = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    intro u hu
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 hu.1
  -- Step 3: every `w ∈ T ∩ B(0, ρ/2)` is `π ξ` for `ξ = w + (1 - |w|²)^{1/2} ζ` in the cap.
  have hsub : (T : Set (Rn N)) ∩ Metric.ball 0 (ρ / 2) ⊆
      T.starProjection '' ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ) := by
    rintro w ⟨hwT, hw⟩
    have hwζ : inner ℝ w ζ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.1 hwT.1
    rw [mem_ball_zero_iff] at hw
    set t : ℝ := ‖w‖ ^ 2
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t < 1 := by nlinarith [norm_nonneg w]
    have htρ : t < ρ ^ 2 / 4 := by nlinarith [norm_nonneg w]
    set f : ℝ := Real.sqrt (1 - t)
    have hf0 : 0 ≤ f := Real.sqrt_nonneg _
    have hf2 : f ^ 2 = 1 - t := Real.sq_sqrt (by linarith)
    have hf1 : f ≤ 1 := Real.sqrt_le_one.2 (by linarith)
    have hft : 1 - t ≤ f := (Real.le_sqrt (by linarith) (by linarith)).2 (by nlinarith)
    refine ⟨w + f • ζ, ⟨⟨H.add_mem hwT.2 (H.smul_mem f hζ), ?_⟩, ?_⟩, ?_⟩
    · -- (b) `|ξ|² = |w|² + f² = 1`
      have hsq : ‖w + f • ζ‖ ^ 2 = 1 := by
        rw [norm_add_sq_real, inner_smul_right, hwζ, norm_smul, hζ1, Real.norm_of_nonneg hf0]
        nlinarith
      nlinarith [norm_nonneg (w + f • ζ)]
    · -- (c) `|ξ - ζ|² = |w|² + (1 - f)² ≤ 2 |w|² < ρ²`
      rw [Metric.mem_ball, dist_eq_norm]
      have hsq : ‖w + f • ζ - ζ‖ ^ 2 = t + (1 - f) ^ 2 := by
        rw [show w + f • ζ - ζ = w + (f - 1) • ζ by rw [sub_smul, one_smul]; abel,
          norm_add_sq_real, inner_smul_right, hwζ, norm_smul, hζ1, Real.norm_eq_abs, mul_one,
          sq_abs]
        ring
      have hlt : ‖w + f • ζ - ζ‖ ^ 2 < ρ ^ 2 := by
        rw [hsq]
        nlinarith [mul_nonneg (sub_nonneg.2 hf1) (sub_nonneg.2 hft),
          mul_nonneg ht0 (sub_nonneg.2 hft), mul_nonneg ht0 (sub_nonneg.2 ht1.le)]
      exact lt_of_pow_lt_pow_left₀ 2 hρ.le hlt
    · -- (d) `π ξ = π w + f π ζ = w`
      rw [map_add, map_smul, hπζ, smul_zero, add_zero, Submodule.starProjection_eq_self_iff.2 hwT]
  -- Step 4: monotonicity and the Lipschitz image bound with constant `1`.
  calc μHE[n] ((T : Set (Rn N)) ∩ Metric.ball 0 (ρ / 2))
      ≤ μHE[n] (T.starProjection '' ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ)) :=
        measure_mono hsub
    _ ≤ ((1 : ℝ≥0) : ℝ≥0∞) ^ n * μHE[n] ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ) :=
        Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
          T.lipschitzWith_starProjection.lipschitzOnWith
    _ = μHE[n] ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ) := by simp
/-- **Graph upper comparison for small caps of the unit sphere of an `(n+1)`-plane** (a cap
estimate for Simon Ch. 3, Theorem 3.6, `chapter-03.txt` lines 530–536, whose proof Simon defers
to [Fed69]/[Ros84]; cf. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Ch. 18).
Let `H ⊆ ℝᴺ` be a subspace with `dim H = n + 1`, `S(H) = {θ ∈ H : |θ| = 1}` and `ζ ∈ S(H)`.
The `n`-plane `T = H ∩ ζ^⊥` satisfies `Hⁿ(S(H) ∩ B(ζ, ρ)) ≤ 2ⁿ Hⁿ(T ∩ B(0, ρ))` for
`0 < ρ ≤ 1/2`: the cap lies in the image of the disc `T ∩ B(0, ρ)` under the graph map
`Γ(w) = w + (1 - |w|²)^{1/2} ζ`, which is `2`-Lipschitz on that disc. -/
theorem Submission.bf_sphereCap_upper_comparison : ∀ (n N : ℕ) (H : Submodule ℝ (Rn N)), finrank ℝ H = n + 1 → ∀ ζ ∈ H, ‖ζ‖ = 1 → ∃ T : Submodule ℝ (Rn N), finrank ℝ T = n ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 → μHE[n] ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ) ≤ 2 ^ n * μHE[n] ((T : Set (Rn N)) ∩ Metric.ball 0 ρ) := by
  intro n N H hH ζ hζ hζ1
  -- The plane `T = (ℝζ)ᗮ ⊓ H` has dimension `dim H - dim ℝζ = n`.
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ1
  have hT : finrank ℝ ((ℝ ∙ ζ)ᗮ ⊓ H : Submodule ℝ (Rn N)) = n :=
    Submodule.finrank_add_inf_finrank_orthogonal' ((Submodule.span_singleton_le_iff_mem _ _).2 hζ)
      (by rw [finrank_span_singleton hζ0, hH, add_comm])
  refine ⟨(ℝ ∙ ζ)ᗮ ⊓ H, hT, fun ρ hρ hρ2 ↦ ?_⟩
  set T : Submodule ℝ (Rn N) := (ℝ ∙ ζ)ᗮ ⊓ H
  set Γ : Rn N → Rn N := fun w ↦ w + Real.sqrt (1 - ‖w‖ ^ 2) • ζ with hΓ
  -- The cap lies in `Γ(T ∩ B(0, ρ))`: `ξ = Γ(w)` for `s = ξ · ζ > 0` and `w = ξ - s ζ ∈ T`.
  have hsub : {θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ ⊆
      Γ '' ((T : Set (Rn N)) ∩ Metric.ball 0 ρ) := by
    rintro ξ ⟨⟨hξH, hξ1⟩, hξ⟩
    rw [Metric.mem_ball, dist_eq_norm] at hξ
    set s : ℝ := inner ℝ ξ ζ
    have hd : ‖ξ - ζ‖ ^ 2 = 2 - 2 * s := by rw [norm_sub_sq_real, hξ1, hζ1]; ring
    have hs1 : s ≤ 1 := by simpa [hξ1, hζ1] using real_inner_le_norm ξ ζ
    have hdlt : ‖ξ - ζ‖ ^ 2 < ρ ^ 2 := by nlinarith [norm_nonneg (ξ - ζ)]
    have hspos : 0 < s := by nlinarith
    set w : Rn N := ξ - s • ζ with hw
    have hwζ : inner ℝ w ζ = 0 := by
      rw [hw, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hζ1]; ring
    have hw2 : ‖w‖ ^ 2 = 1 - s ^ 2 := by
      rw [hw, norm_sub_sq_real, real_inner_smul_right, norm_smul, hξ1, hζ1, Real.norm_eq_abs,
        mul_one, sq_abs]
      ring
    refine ⟨w, ⟨⟨Submodule.mem_orthogonal_singleton_iff_inner_left.2 hwζ,
      H.sub_mem hξH (H.smul_mem s hζ)⟩, ?_⟩, ?_⟩
    · -- `|w|² = (1 - s)(1 + s) ≤ 2 (1 - s) = |ξ - ζ|² < ρ²`
      rw [mem_ball_zero_iff]
      have hle : ‖w‖ ^ 2 ≤ ‖ξ - ζ‖ ^ 2 := by rw [hw2, hd]; nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 hρ.le (hle.trans_lt hdlt)
    · -- `(1 - |w|²)^{1/2} = (s²)^{1/2} = s`
      show w + Real.sqrt (1 - ‖w‖ ^ 2) • ζ = ξ
      rw [hw2, show (1 : ℝ) - (1 - s ^ 2) = s ^ 2 by ring, Real.sqrt_sq hspos.le, hw,
        sub_add_cancel]
  -- `Γ` is `2`-Lipschitz on `T ∩ B(0, ρ)`.
  have hlip : LipschitzOnWith 2 Γ ((T : Set (Rn N)) ∩ Metric.ball 0 ρ) := by
    refine LipschitzOnWith.of_dist_le_mul fun w hw w' hw' ↦ ?_
    have hwζ : inner ℝ w ζ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.1 hw.1.1
    have hwζ' : inner ℝ w' ζ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.1 hw'.1.1
    have ha : ‖w‖ < 1 / 2 := (mem_ball_zero_iff.1 hw.2).trans_le hρ2
    have hb : ‖w'‖ < 1 / 2 := (mem_ball_zero_iff.1 hw'.2).trans_le hρ2
    have ha0 := norm_nonneg w
    have hb0 := norm_nonneg w'
    -- `|f(w) - f(w')| ≤ |w - w'|` for `f(w) = (1 - |w|²)^{1/2}`: with `x = 1 - |w|²` and
    -- `y = 1 - |w'|²` we have `√x, √y ≥ 1/2`, so `|√x - √y| = |x - y| / (√x + √y) ≤ |x - y|`,
    -- and `|x - y| = ||w| - |w'|| (|w| + |w'|) ≤ |w - w'|`.
    have hff : |Real.sqrt (1 - ‖w‖ ^ 2) - Real.sqrt (1 - ‖w'‖ ^ 2)| ≤ ‖w - w'‖ := by
      set x : ℝ := 1 - ‖w‖ ^ 2 with hx
      set y : ℝ := 1 - ‖w'‖ ^ 2 with hy
      have hsx : 1 / 2 ≤ Real.sqrt x := by
        rw [Real.le_sqrt (by norm_num) (by nlinarith)]; nlinarith
      have hsy : 1 / 2 ≤ Real.sqrt y := by
        rw [Real.le_sqrt (by norm_num) (by nlinarith)]; nlinarith
      have hprod : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by nlinarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ y by nlinarith)]
      have hsqrt : |Real.sqrt x - Real.sqrt y| ≤ |x - y| := by
        rw [← hprod, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.sqrt x + Real.sqrt y)]
        nlinarith [abs_nonneg (Real.sqrt x - Real.sqrt y)]
      have hxy : |x - y| = |‖w‖ - ‖w'‖| * (‖w‖ + ‖w'‖) := by
        rw [hx, hy, show (1 - ‖w‖ ^ 2) - (1 - ‖w'‖ ^ 2) = (‖w'‖ - ‖w‖) * (‖w‖ + ‖w'‖) by ring,
          abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ‖w‖ + ‖w'‖), abs_sub_comm]
      refine hsqrt.trans ?_
      rw [hxy]
      nlinarith [abs_norm_sub_norm_le w w', abs_nonneg (‖w‖ - ‖w'‖)]
    -- Pythagoras: `(w - w') ⟂ ζ`, so `|Γ(w) - Γ(w')|² = |w - w'|² + (f(w) - f(w'))² ≤ (2 |w - w'|)²`.
    have hdiff : Γ w - Γ w' =
        (w - w') + (Real.sqrt (1 - ‖w‖ ^ 2) - Real.sqrt (1 - ‖w'‖ ^ 2)) • ζ := by
      simp only [hΓ, sub_smul]; abel
    have hinner : inner ℝ (w - w') ζ = 0 := by rw [inner_sub_left, hwζ, hwζ', sub_zero]
    have hsq : ‖Γ w - Γ w'‖ ^ 2 =
        ‖w - w'‖ ^ 2 + (Real.sqrt (1 - ‖w‖ ^ 2) - Real.sqrt (1 - ‖w'‖ ^ 2)) ^ 2 := by
      rw [hdiff, norm_add_sq_real, real_inner_smul_right, hinner, norm_smul, hζ1, Real.norm_eq_abs,
        mul_one, sq_abs]
      ring
    have hff2 : (Real.sqrt (1 - ‖w‖ ^ 2) - Real.sqrt (1 - ‖w'‖ ^ 2)) ^ 2 ≤ ‖w - w'‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hff 2
    rw [dist_eq_norm, dist_eq_norm]
    have h2 : ‖Γ w - Γ w'‖ ^ 2 ≤ ((2 : ℝ≥0) * ‖w - w'‖) ^ 2 := by
      push_cast; nlinarith [norm_nonneg (w - w')]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  -- Monotonicity and the Lipschitz image bound `Hⁿ(Γ(A)) ≤ 2ⁿ Hⁿ(A)`.
  calc μHE[n] ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ)
      ≤ μHE[n] (Γ '' ((T : Set (Rn N)) ∩ Metric.ball 0 ρ)) := measure_mono hsub
    _ ≤ ((2 : ℝ≥0) : ℝ≥0∞) ^ n * μHE[n] ((T : Set (Rn N)) ∩ Metric.ball 0 ρ) :=
        Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hlip
    _ = 2 ^ n * μHE[n] ((T : Set (Rn N)) ∩ Metric.ball 0 ρ) := by norm_num

/-- **Two-sided `Hⁿ` bounds for caps of the unit sphere of an `(n+1)`-plane** (Step 2.1 of the
cone trichotomy for Simon Ch. 3, Theorem 3.6; Dall'Alba, Lemma 4.15; Mattila, Ch. 18). Let
`H ⊆ ℝ^{n+ℓ}` be a subspace with `dim H = n + 1` and `S(H) = {θ ∈ H : |θ| = 1}`. There are
constants `c > 0` and `C`, depending only on `n` and `H`, such that for every `ζ ∈ S(H)` and
every `ρ > 0`: `c ρⁿ ≤ Hⁿ(S(H) ∩ B(ζ, ρ))` if `ρ ≤ 2`, and `Hⁿ(S(H) ∩ B(ζ, ρ)) ≤ C ρⁿ`. With `ω`
the flat-ball constant (`Hⁿ(T ∩ B(w, ρ)) = ω ρⁿ` on `n`-planes), the projection comparison gives
`c = 2⁻ⁿ ω`; the graph comparison gives `2ⁿ ω ρⁿ` for `ρ ≤ 1/2`; finitely many caps of radius
`1/2` cover the compact `S(H)`, so `σ = Hⁿ(S(H)) < ∞`; and `C = 2ⁿ (ω + σ)` covers `ρ > 1/2`
via `σ ≤ σ (2ρ)ⁿ`. -/
theorem Submission.bf_sphereCap_measure_bounds : ∀ (n ℓ : ℕ), 0 < n → ∀ H : Submodule ℝ (Rn (n + ℓ)), finrank ℝ H = n + 1 → ∃ c C : ℝ, 0 < c ∧ ∀ ζ ∈ H, ‖ζ‖ = 1 → ∀ ρ : ℝ, 0 < ρ → (ρ ≤ 2 → ENNReal.ofReal (c * ρ ^ n) ≤ μHE[n] ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ)) ∧ μHE[n] ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ ρ) ≤ ENNReal.ofReal (C * ρ ^ n) := by
  intro n ℓ _ H hH
  set S : Set (Rn (n + ℓ)) := {θ | θ ∈ H ∧ ‖θ‖ = 1} with hS
  -- Step 1: the flat-ball constant `ω`, with `Hⁿ(T ∩ B(w, ρ)) = ω ρⁿ` for every `n`-plane `T`.
  obtain ⟨ω, hω, hball⟩ := Submission.bf_planeBall_measure_uniform n
  -- Step 4: small caps, `Hⁿ(S(H) ∩ B(ζ, ρ)) ≤ 2ⁿ Hⁿ(T_ζ ∩ B(0, ρ)) = 2ⁿ ω ρⁿ` for `ρ ≤ 1/2`.
  have hsmall : ∀ ζ ∈ H, ‖ζ‖ = 1 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 →
      μHE[n] (S ∩ Metric.ball ζ ρ) ≤ ENNReal.ofReal (2 ^ n * ω * ρ ^ n) := by
    intro ζ hζ hζ1 ρ hρ hρ2
    obtain ⟨T, hT, hcmp⟩ := Submission.bf_sphereCap_upper_comparison n (n + ℓ) H hH ζ hζ hζ1
    calc μHE[n] (S ∩ Metric.ball ζ ρ)
        ≤ 2 ^ n * μHE[n] ((T : Set (Rn (n + ℓ))) ∩ Metric.ball 0 ρ) := hcmp ρ hρ hρ2
      _ = ENNReal.ofReal (2 ^ n * ω * ρ ^ n) := by
        rw [hball (n + ℓ) T hT 0 T.zero_mem ρ hρ, mul_assoc,
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ n),
          ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  -- Step 5: `Hⁿ(S(H)) < ∞`, since the compact `S(H)` is covered by finitely many caps of radius
  -- `1/2`, each of measure at most `2ⁿ ω 2⁻ⁿ`.
  have hScpt : IsCompact S := by
    have hSeq : S = (H : Set (Rn (n + ℓ))) ∩ {θ | ‖θ‖ = 1} := rfl
    rw [hSeq]
    refine Metric.isCompact_of_isClosed_isBounded
      (H.closed_of_finiteDimensional.inter (isClosed_eq continuous_norm continuous_const))
      ((Metric.isBounded_closedBall (x := (0 : Rn (n + ℓ))) (r := 1)).subset ?_)
    rintro θ ⟨-, hθ⟩
    have hθ1 : ‖θ‖ = 1 := hθ
    rw [mem_closedBall_zero_iff]
    exact hθ1.le
  obtain ⟨t, htS, htfin, hcover⟩ :=
    finite_cover_balls_of_compact hScpt (by norm_num : (0 : ℝ) < 1 / 2)
  have hSfin : μHE[n] S < ∞ := by
    have hsub : S ⊆ ⋃ ζ ∈ t, S ∩ Metric.ball ζ (1 / 2) := fun θ hθ ↦ by
      obtain ⟨ζ, hζt, hθζ⟩ := Set.mem_iUnion₂.1 (hcover hθ)
      exact Set.mem_iUnion₂.2 ⟨ζ, hζt, hθ, hθζ⟩
    refine (measure_mono hsub).trans_lt (measure_biUnion_lt_top htfin fun ζ hζ ↦ ?_)
    have hζS : ζ ∈ H ∧ ‖ζ‖ = 1 := by
      have := htS hζ
      rwa [hS] at this
    exact (hsmall ζ hζS.1 hζS.2 (1 / 2) (by norm_num) le_rfl).trans_lt ENNReal.ofReal_lt_top
  -- Steps 3, 6 and 7: `c = 2⁻ⁿ ω` and `C = 2ⁿ (ω + σ)` with `σ = Hⁿ(S(H))`.
  set σ : ℝ := (μHE[n] S).toReal
  have hσ0 : 0 ≤ σ := ENNReal.toReal_nonneg
  refine ⟨ω / 2 ^ n, 2 ^ n * (ω + σ), div_pos hω (pow_pos two_pos n),
    fun ζ hζ hζ1 ρ hρ ↦ ⟨fun hρ2 ↦ ?_, ?_⟩⟩
  · -- Step 3: `c ρⁿ = ω (ρ/2)ⁿ = Hⁿ(T_ζ ∩ B(0, ρ/2)) ≤ Hⁿ(S(H) ∩ B(ζ, ρ))`.
    obtain ⟨T, hT, hcmp⟩ := Submission.bf_sphereCap_lower_comparison n (n + ℓ) H hH ζ hζ hζ1
    calc ENNReal.ofReal (ω / 2 ^ n * ρ ^ n) = ENNReal.ofReal (ω * (ρ / 2) ^ n) := by
          congr 1
          rw [div_pow]
          ring
      _ = μHE[n] ((T : Set (Rn (n + ℓ))) ∩ Metric.ball 0 (ρ / 2)) :=
          (hball (n + ℓ) T hT 0 T.zero_mem (ρ / 2) (half_pos hρ)).symm
      _ ≤ μHE[n] (S ∩ Metric.ball ζ ρ) := hcmp ρ hρ hρ2
  · -- Step 6: for `ρ ≤ 1/2` use step 4; for `ρ > 1/2`, `Hⁿ(S(H) ∩ B(ζ, ρ)) ≤ σ ≤ σ (2ρ)ⁿ`.
    rcases le_or_gt ρ (1 / 2) with hρ2 | hρ2
    · refine (hsmall ζ hζ hζ1 ρ hρ hρ2).trans (ENNReal.ofReal_le_ofReal ?_)
      have h2 : 0 ≤ 2 ^ n * σ * ρ ^ n :=
        mul_nonneg (mul_nonneg (pow_nonneg zero_le_two n) hσ0) (pow_nonneg hρ.le n)
      linarith
    · have h1 : 1 ≤ 2 ^ n * ρ ^ n := by
        rw [← mul_pow]
        exact one_le_pow₀ (by linarith)
      calc μHE[n] (S ∩ Metric.ball ζ ρ) ≤ μHE[n] S := measure_mono Set.inter_subset_left
        _ = ENNReal.ofReal σ := (ENNReal.ofReal_toReal hSfin.ne).symm
        _ ≤ ENNReal.ofReal (2 ^ n * (ω + σ) * ρ ^ n) := by
          refine ENNReal.ofReal_le_ofReal ?_
          -- `2ⁿ (ω + σ) ρⁿ - σ = ω (2ρ)ⁿ + σ ((2ρ)ⁿ - 1) ≥ 0`
          nlinarith [mul_nonneg hσ0 (sub_nonneg.2 h1), mul_nonneg hω.le (zero_le_one.trans h1)]
/-- **Continuity of the frame projection on independent frames** (Step 1.5(b) of the supplied
proof of the Besicovitch–Federer theorem, Simon Ch. 3, Theorem 3.6). On the linearly independent
frames `v = (v₁, …, vₙ)` in `ℝᴺ`, the orthogonal projection onto `span v` depends continuously on
`v`: with the synthesis operator `M_v c = ∑ᵢ cᵢ vᵢ` and the Gram operator `Γ_v = M_v* M_v`
(invertible for independent `v`), `frameProjection v = M_v Γ_v⁻¹ M_v*`, and ring inversion is
continuous at units. -/
theorem Submission.bf_frameProjection_continuousOn : ∀ (N n : ℕ), ContinuousOn (fun v : Fin n → Rn N ↦ frameProjection v) {v | LinearIndependent ℝ v} := by
  intro N n
  -- The synthesis operator `M v : ℝⁿ → ℝᴺ`, `c ↦ ∑ᵢ cᵢ vᵢ`, depends continuously on `v`.
  let M : (Fin n → Rn N) → (EuclideanSpace ℝ (Fin n) →L[ℝ] Rn N) := fun v ↦
    ∑ i, (EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ (Fin n))).smulRight (v i)
  have hM_apply : ∀ v c, M v c = ∑ i, c i • v i := by
    intro v c
    simp [M]
  have hM : Continuous M := by
    refine continuous_finsetSum _ fun i _ ↦ ?_
    exact (ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin n)) (Rn N)
      (EuclideanSpace.proj i)).continuous.comp (continuous_apply i)
  -- The adjoint `M v*` and the Gram operator `Γ v = M v* ∘ M v` depend continuously on `v`.
  have hMadj : Continuous fun v ↦ ContinuousLinearMap.adjoint (M v) :=
    ContinuousLinearMap.adjoint.continuous.comp hM
  let Γ : (Fin n → Rn N) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    fun v ↦ (ContinuousLinearMap.adjoint (M v)).comp (M v)
  have hΓ : Continuous Γ := hMadj.clm_comp hM
  -- For an independent frame, `Γ v` is injective, hence a unit.
  have hunit : ∀ v : Fin n → Rn N, LinearIndependent ℝ v → IsUnit (Γ v) := by
    intro v hv
    have hinj : Function.Injective (Γ v) := by
      rw [injective_iff_map_eq_zero]
      intro c hc
      have h1 : inner ℝ (M v c) (M v c) = 0 := by
        rw [← ContinuousLinearMap.adjoint_inner_left]
        exact (congrArg (fun y ↦ inner ℝ y c) hc).trans (inner_zero_left _)
      have h2 : ∑ i, c i • v i = 0 := by
        rw [← hM_apply]
        exact inner_self_eq_zero.1 h1
      have h3 := Fintype.linearIndependent_iff.1 hv (fun i ↦ c i) h2
      ext i
      simpa using h3 i
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  -- For an independent frame, `M v ∘ Γ v⁻¹ ∘ M v*` is the orthogonal projection onto `span v`.
  have hR : ∀ v : Fin n → Rn N, LinearIndependent ℝ v →
      (M v).comp ((Ring.inverse (Γ v)).comp (ContinuousLinearMap.adjoint (M v))) =
        frameProjection v := by
    intro v hv
    have hΓinv : ∀ y, Γ v (Ring.inverse (Γ v) y) = y := by
      intro y
      have := Ring.mul_inverse_cancel (Γ v) (hunit v hv)
      exact congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) ↦ T y) this
    ext1 x
    symm
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨_, (hM_apply _ _).symm⟩
    · intro w hw
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw
      have hc : ∑ i, c i • v i = M v (WithLp.toLp 2 c) := (hM_apply _ _).symm
      rw [hc, ← ContinuousLinearMap.adjoint_inner_left, map_sub]
      have : ContinuousLinearMap.adjoint (M v)
          (((M v).comp ((Ring.inverse (Γ v)).comp (ContinuousLinearMap.adjoint (M v)))) x) =
          ContinuousLinearMap.adjoint (M v) x :=
        hΓinv _
      rw [this, sub_self, inner_zero_left]
  -- Conclusion: ring inversion is continuous at the unit `Γ v₀`.
  intro v₀ hv₀
  have hinv : ContinuousAt (fun v ↦ Ring.inverse (Γ v)) v₀ := by
    obtain ⟨u, hu⟩ := hunit v₀ hv₀
    have h := NormedRing.inverse_continuousAt u
    rw [hu] at h
    exact h.comp hΓ.continuousAt
  have hcont : ContinuousAt (fun v ↦
      (M v).comp ((Ring.inverse (Γ v)).comp (ContinuousLinearMap.adjoint (M v)))) v₀ :=
    hM.continuousAt.clm_comp (hinv.clm_comp hMadj.continuousAt)
  exact hcont.continuousWithinAt.congr (fun v hv ↦ (hR v hv).symm) (hR v₀ hv₀).symm

/-- **Averaging over `O(N)` and transfer to Lebesgue-a.e. frames** (Steps 0.2, 4 and 5 of the
supplied proof of the Besicovitch–Federer theorem, Simon Ch. 3, Theorem 3.6; Dall'Alba,
Lemma 5.6). Let `θ_N` be the bi-invariant Haar probability on `O(N) = {g : g* g = 1}` and `P₀`
the projection onto an `n`-plane `W₀`. For every `a`, (h1), (h2) and `0 < Hⁿ(S(H)) < ∞` for the
unit spheres `S(H)` of the `(n+1)`-planes `H` give `θ_N{g : (a, g P₀ g*) ∈ Exc} = 0`. Tonelli
over `μ ⊗ θ_N` then gives `μ(Exc^{g P₀ g*}) = 0` for `θ_N`-a.e. `g`, and this transfers from
`θ_N` to Lebesgue-a.e. frames. -/
theorem Submission.bf_frameAveraging_null : ∀ (n ℓ : ℕ), 0 < n → 0 < ℓ → ∀ μ : Measure (Rn (n + ℓ)), IsFiniteMeasure μ → ∀ (Exc : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)))) (Bad : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)) × Rn (n + ℓ))), MeasurableSet Exc → MeasurableSet Bad → (∀ (a : Rn (n + ℓ)) (H : Submodule ℝ (Rn (n + ℓ))), finrank ℝ H = n + 1 → μHE[n] {θ | θ ∈ H ∧ ‖θ‖ = 1 ∧ (a, H.starProjection, θ) ∈ Bad} = 0) → (∀ (a : Rn (n + ℓ)) (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → (a, W.starProjection) ∈ Exc → ∀ u : Fin ℓ → Rn (n + ℓ), Orthonormal ℝ u → (∀ j, u j ∈ Wᗮ) → ∃ j, (a, (W ⊔ Submodule.span ℝ {u j}).starProjection, u j) ∈ Bad) → ForAlmostAllProjections (n + ℓ) n (fun p ↦ μ {a | (a, p) ∈ Exc} = 0) := by
  intro n ℓ hn _hℓ μ _hμ Exc Bad hExc hBad h1 h2
  -- Step 4: `0 < Hⁿ(S(H)) < ∞` for every `(n+1)`-plane `H`, from the cap bounds around a unit
  -- vector `ζ ∈ H` at radius `2`, and at radius `3` since `S(H) ⊆ B(ζ, 3)`.
  have hS : ∀ H : Submodule ℝ (Rn (n + ℓ)), finrank ℝ H = n + 1 →
      0 < μHE[n] {x : Rn (n + ℓ) | x ∈ H ∧ ‖x‖ = 1} ∧
        μHE[n] {x : Rn (n + ℓ) | x ∈ H ∧ ‖x‖ = 1} < ∞ := by
    intro H hH
    obtain ⟨c, C, hc, hcap⟩ := Submission.bf_sphereCap_measure_bounds n ℓ hn H hH
    obtain ⟨ζ, hζH, hζ⟩ : ∃ ζ ∈ H, ‖ζ‖ = 1 := by
      have hH0 : H ≠ ⊥ := by
        rintro rfl
        rw [finrank_bot] at hH
        omega
      obtain ⟨x, hxH, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH0
      exact ⟨(‖x‖⁻¹ : ℝ) • x, H.smul_mem _ hxH, norm_smul_inv_norm hx⟩
    refine ⟨?_, ?_⟩
    · calc (0 : ℝ≥0∞) < ENNReal.ofReal (c * 2 ^ n) := ENNReal.ofReal_pos.2 (by positivity)
        _ ≤ μHE[n] ({θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ 2) :=
          (hcap ζ hζH hζ 2 two_pos).1 le_rfl
        _ ≤ μHE[n] {x : Rn (n + ℓ) | x ∈ H ∧ ‖x‖ = 1} := measure_mono inter_subset_left
    · have hsub : {x : Rn (n + ℓ) | x ∈ H ∧ ‖x‖ = 1} ⊆
          {θ | θ ∈ H ∧ ‖θ‖ = 1} ∩ Metric.ball ζ 3 := by
        intro x hx
        refine ⟨hx, ?_⟩
        rw [Metric.mem_ball, dist_eq_norm]
        calc ‖x - ζ‖ ≤ ‖x‖ + ‖ζ‖ := norm_sub_le x ζ
          _ < 3 := by rw [hx.2, hζ]; norm_num
      exact (measure_mono hsub).trans_lt
        ((hcap ζ hζH hζ 3 three_pos).2.trans_lt ENNReal.ofReal_lt_top)
  -- Step 1: the bi-invariant Haar probability `θ_N` on `O(N)`, the stabilizer of `U = 0`.
  obtain ⟨θ, hθ, hθO, hθinv⟩ := Submission.bf_orthStabilizer_haar_exists (n + ℓ) ⊥
  have hθO' : ∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1 := hθO.mono fun _ hg ↦ hg.1
  have hθR : ∀ k : Rn (n + ℓ) →L[ℝ] Rn (n + ℓ), ContinuousLinearMap.adjoint k * k = 1 →
      Measure.map (fun g ↦ g * k) θ = θ := fun k hk ↦
    (hθinv k hk fun x hx ↦ by rw [(Submodule.mem_bot ℝ).1 hx, map_zero]).2
  -- `W₀ = span{e_1, …, e_n}`, an `n`-plane.
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Submodule ℝ (Rn (n + ℓ)), finrank ℝ W₀ = n := by
    have hv : LinearIndependent ℝ fun i : Fin n ↦
        EuclideanSpace.basisFun (Fin (n + ℓ)) ℝ (Fin.castAdd ℓ i) :=
      (EuclideanSpace.basisFun (Fin (n + ℓ)) ℝ).orthonormal.linearIndependent.comp _
        (Fin.castAdd_injective n ℓ)
    exact ⟨_, (finrank_span_eq_card hv).trans (Fintype.card_fin n)⟩
  -- Steps 2–6: for every `a`, `θ_N{g : (a, g P₀ g*) ∈ Exc} = 0`.
  have hpt : ∀ a : Rn (n + ℓ),
      θ {g | (a, g * W₀.starProjection * ContinuousLinearMap.adjoint g) ∈ Exc} = 0 := fun a ↦
    Submission.bf_haar_excPointwise_null n ℓ Exc Bad hBad hS a (h1 a) (h2 a) θ hθ hθO' hθR W₀ hW₀
  -- Step 7: Tonelli over `μ ⊗ θ_N`. The set `Q` of the `p` with `μ(Exc^p) ≠ 0` is Borel, and
  -- `g P₀ g* ∉ Q` for `θ_N`-a.e. `g`.
  set Q : Set (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)) := {p | μ {a | (a, p) ∈ Exc} ≠ 0} with hQ
  have hμExc : Measurable fun p : Rn (n + ℓ) →L[ℝ] Rn (n + ℓ) ↦ μ {a | (a, p) ∈ Exc} :=
    measurable_measure_prodMk_right hExc
  have hQm : MeasurableSet Q := hμExc (measurableSet_singleton 0).compl
  have hconj : Continuous fun g : Rn (n + ℓ) →L[ℝ] Rn (n + ℓ) ↦
      g * W₀.starProjection * ContinuousLinearMap.adjoint g :=
    (continuous_id.mul continuous_const).mul
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn (n + ℓ)) (F := Rn (n + ℓ))).continuous
  have hgood : MeasurableSet {q : Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)) |
      (q.1, q.2 * W₀.starProjection * ContinuousLinearMap.adjoint q.2) ∉ Exc} :=
    (measurable_fst.prodMk (hconj.measurable.comp measurable_snd) hExc).compl
  have hae : ∀ᵐ a ∂μ, ∀ᵐ g ∂θ,
      (a, g * W₀.starProjection * ContinuousLinearMap.adjoint g) ∉ Exc :=
    Eventually.of_forall fun a ↦ measure_eq_zero_iff_ae_notMem.1 (hpt a)
  have hQnull : θ {g | g * W₀.starProjection * ContinuousLinearMap.adjoint g ∈ Q} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [(Measure.ae_ae_comm (p := fun a g ↦
      (a, g * W₀.starProjection * ContinuousLinearMap.adjoint g) ∉ Exc) hgood).1 hae] with g hg
    simp only [hQ, mem_ofPred_eq, ne_eq, not_not]
    exact measure_eq_zero_iff_ae_notMem.2 hg
  -- Steps 8–10: transfer from `θ_N` to Lebesgue-a.e. frames.
  exact (Submission.bf_haar_null_to_frames (n + ℓ) n
    (Submission.bf_frameProjection_continuousOn (n + ℓ) n) θ hθ hθO' hθR W₀ hW₀ Q hQm
    hQnull).mono fun v hv hlin ↦ not_not.1 (hv hlin)

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
