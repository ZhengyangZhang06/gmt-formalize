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

/-- **The measure of a symmetric difference in a ball is the `L¹` distance of the indicators**
(used in the BV translation estimate for the compactness of sets of locally bounded perimeter,
Simon Ch. 2, Thm. 2.6). For `Lᴺ`-measurable `A, F ⊆ ℝᴺ` and the open ball `B = B_R(0)`,
`Lᴺ(B ∩ (A Δ F)) = ∫_B |1_A - 1_F| dLᴺ`: pointwise `|1_A - 1_F| = 1_{A Δ F}`, and
`∫_B 1_{A Δ F} dLᴺ = Lᴺ(A Δ F ∩ B)`, which is finite since `Lᴺ(B) < ∞`. -/
theorem Submission.indCompact_transEst_volume_symmDiff_eq_integral : ∀ (N : ℕ) (A F : Set (Rn N)) (R : ℝ), NullMeasurableSet A volume → NullMeasurableSet F volume → volume (Metric.ball (0 : Rn N) R ∩ symmDiff A F) = ENNReal.ofReal (∫ y in Metric.ball (0 : Rn N) R, |A.indicator (1 : Rn N → ℝ) y - F.indicator (1 : Rn N → ℝ) y|) := by
  intro N A F R hA hF
  -- Step 1: `|1_A - 1_F| = 1_{A Δ F}` pointwise.
  have h1 : ∀ y, |A.indicator (1 : Rn N → ℝ) y - F.indicator (1 : Rn N → ℝ) y| =
      (symmDiff A F).indicator (fun _ ↦ (1 : ℝ)) y := by
    intro y
    rw [← abs_indicator_symmDiff]
    by_cases hy : y ∈ symmDiff A F <;> simp [hy]
  simp_rw [h1]
  -- Step 2: `A Δ F` is null-measurable for `Lᴺ`, hence for `Lᴺ ⌞ B ≤ Lᴺ`.
  have hS : NullMeasurableSet (symmDiff A F) (volume.restrict (Metric.ball (0 : Rn N) R)) :=
    (hA.symmDiff hF).mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  -- Step 5: `Lᴺ(A Δ F ∩ B) ≤ Lᴺ(B) < ∞`.
  have hfin : volume (symmDiff A F ∩ Metric.ball (0 : Rn N) R) ≠ ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt measure_ball_lt_top).ne
  -- Steps 3, 4 and 6: `∫_B 1_{A Δ F} dLᴺ = (Lᴺ ⌞ B)(A Δ F) = Lᴺ(A Δ F ∩ B)`, `B` being open.
  rw [integral_indicator₀ hS, setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
    Measure.restrict_apply' measurableSet_ball, ENNReal.ofReal_toReal hfin, Set.inter_comm]
/-- **Translation change of variables for indicator differences** (Step 5(a) of the supplied
proof of the BV translation estimate used for the compactness of sets of bounded perimeter in
De Giorgi's theorem, Simon Ch. 3, Theorem 4.3). For `L^N`-measurable `F ⊆ ℝᴺ`, integrable `ψ`
and `h ∈ ℝᴺ`, `∫ (χ_F(y + h) - χ_F(y)) ψ(y) dy = ∫_F (ψ(z - h) - ψ(z)) dz`: pointwise the
integrand is `G(y + h) - H(y)` with `G = χ_F ψ(· - h)` and `H = χ_F ψ`, and Lebesgue measure is
translation invariant. -/
theorem Submission.indCompact_transEst_integral_indicator_shift_mul : ∀ (N : ℕ) (F : Set (Rn N)) (ψ : Rn N → ℝ) (h : Rn N), NullMeasurableSet F volume → Integrable ψ volume → ∫ y, (F.indicator (1 : Rn N → ℝ) (y + h) - F.indicator (1 : Rn N → ℝ) y) * ψ y = ∫ z in F, (ψ (z - h) - ψ z) := by
  intro N F ψ h hF hψ
  -- The translate `ψ_h = ψ (· - h)` is integrable.
  have hψh : Integrable (fun z ↦ ψ (z - h)) volume := hψ.comp_sub_right h
  -- `y ↦ G (y + h)` with `G = 1_F ψ_h`, and `H = 1_F ψ`, are integrable.
  have hG : Integrable (fun y ↦ F.indicator (fun z ↦ ψ (z - h)) (y + h)) volume :=
    (hψh.indicator₀ hF).comp_add_right h
  have hH : Integrable (F.indicator ψ) volume := hψ.indicator₀ hF
  -- Pointwise, `(1_F (y + h) - 1_F y) ψ y = G (y + h) - H y` (four cases).
  have hpt : ∀ y, (F.indicator (1 : Rn N → ℝ) (y + h) - F.indicator (1 : Rn N → ℝ) y) * ψ y =
      F.indicator (fun z ↦ ψ (z - h)) (y + h) - F.indicator ψ y := by
    intro y
    by_cases hy₁ : y + h ∈ F <;> by_cases hy₂ : y ∈ F <;> simp [hy₁, hy₂]
  -- Linearity, translation invariance, indicator integrals, linearity on `F`.
  calc ∫ y, (F.indicator (1 : Rn N → ℝ) (y + h) - F.indicator (1 : Rn N → ℝ) y) * ψ y
      = ∫ y, (F.indicator (fun z ↦ ψ (z - h)) (y + h) - F.indicator ψ y) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = (∫ y, F.indicator (fun z ↦ ψ (z - h)) (y + h)) - ∫ y, F.indicator ψ y :=
        integral_sub hG hH
    _ = (∫ z in F, ψ (z - h)) - ∫ z in F, ψ z := by
        rw [integral_add_right_eq_self (F.indicator fun z ↦ ψ (z - h)) h,
          integral_indicator₀ hF, integral_indicator₀ hF]
    _ = ∫ z in F, (ψ (z - h) - ψ z) :=
        (integral_sub hψh.integrableOn hψ.integrableOn).symm
/-- **Translation difference of a `C¹_c` function as a parametric integral of directional
derivatives** (steps 5(b) and 5(d) of the BV translation estimate behind the Compactness
Theorem 2.6 of Simon Ch. 2, `chapter-02.txt` lines 598–620, [GT01, Thm. 7.22], as used in the
proof of Ch. 3, Thm. 4.3, `chapter-03.txt` line 653). For an arbitrary `F ⊆ ℝᴺ`, `ψ ∈ C¹_c(ℝᴺ)`
and `h ∈ ℝᴺ`: `∫_F (ψ(z - h) - ψ(z)) dz = -∫₀¹ ∫_F Dψ(z - th)[h] dz dt`. For fixed `z`, the
fundamental theorem of calculus along `t ↦ ψ(z - th)` gives
`ψ(z - h) - ψ(z) = -∫₀¹ Dψ(z - th)[h] dt`. The integrand `f(z, t) = Dψ(z - th)[h]` is continuous
and, for `t ∈ [0, 1]`, vanishes unless `z` lies in the compact `K = tsupport ψ + [0, 1] h`; so it
is integrable on `ℝᴺ × [0, 1] ⊇ F × (0, 1]`, and Fubini for `Lᴺ ⌞ F ⊗ L¹ ⌞ (0, 1]` swaps the
integrals. -/
theorem Submission.indCompact_transEst_setIntegral_shift_sub_ftc : ∀ (N : ℕ) (F : Set (Rn N)) (ψ : Rn N → ℝ) (h : Rn N), ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∫ z in F, (ψ (z - h) - ψ z) = -∫ t in (0 : ℝ)..1, ∫ z in F, fderiv ℝ ψ (z - t • h) h := by
  intro N F ψ h hψ hψs
  -- Step 1: `ψ` is differentiable and `f(z, t) = Dψ(z - th)[h]` is continuous on `ℝᴺ × ℝ`.
  have hdiff : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  set f : Rn N → ℝ → ℝ := fun z t ↦ fderiv ℝ ψ (z - t • h) h
  have hfc : Continuous (Function.uncurry f) :=
    (hcont.comp (continuous_fst.sub (continuous_snd.smul continuous_const))).clm_apply
      continuous_const
  -- Step 2 (FTC along `t ↦ ψ(z - th)`, whose derivative is `-f(z, t)`):
  -- `ψ(z - h) - ψ(z) = -∫₀¹ f(z, t) dt`.
  have hftc : ∀ z, ψ (z - h) - ψ z = -∫ t in (0 : ℝ)..1, f z t := by
    intro z
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ ↦ ψ (z - t • h)) (-(f z t)) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ ↦ z - t • h) (-h) t := by
        simpa using ((hasDerivAt_id t).smul_const h).const_sub z
      have h2 : HasDerivAt (fun t : ℝ ↦ ψ (z - t • h)) (fderiv ℝ ψ (z - t • h) (-h)) t :=
        (hdiff (z - t • h)).hasFDerivAt.comp_hasDerivAt t h1
      simpa [f, map_neg] using h2
    have hint : IntervalIntegrable (fun t ↦ -(f z t)) volume 0 1 :=
      ((hfc.comp (continuous_const.prodMk continuous_id)).neg).intervalIntegrable 0 1
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simp only [one_smul, zero_smul, sub_zero, intervalIntegral.integral_neg] at this
    linarith
  -- Step 3: integrate over `F`, write `∫₀¹` as `∫_{(0, 1]}`, and reduce to Fubini for
  -- `Lᴺ ⌞ F ⊗ L¹ ⌞ (0, 1]`.
  rw [integral_congr_ae (Eventually.of_forall hftc), integral_neg]
  congr 1
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  apply integral_integral_swap
  -- Step 4: integrability. With `K = {x + s h : x ∈ tsupport ψ, s ∈ [0, 1]}` compact, `f` is
  -- integrable on `K × [0, 1]` and vanishes on `(ℝᴺ × [0, 1]) \ (K × [0, 1])`.
  set K : Set (Rn N) := (fun p : Rn N × ℝ ↦ p.1 + p.2 • h) '' (tsupport ψ ×ˢ Icc (0 : ℝ) 1)
  have hK : IsCompact K := (hψs.isCompact.prod isCompact_Icc).image (by fun_prop)
  rw [Measure.prod_restrict]
  have h1 : IntegrableOn (Function.uncurry f) (K ×ˢ Icc (0 : ℝ) 1) (volume.prod volume) :=
    hfc.continuousOn.integrableOn_compact (hK.prod isCompact_Icc)
  have h2 : IntegrableOn (Function.uncurry f) (univ ×ˢ Icc (0 : ℝ) 1) (volume.prod volume) := by
    refine h1.of_forall_sdiff_eq_zero (MeasurableSet.univ.prod measurableSet_Icc) ?_
    rintro ⟨z, t⟩ ⟨⟨-, ht⟩, hnot⟩
    simp only [Function.uncurry_apply_pair, f]
    by_contra hne
    apply hnot
    refine ⟨?_, ht⟩
    -- `Dψ = 0` off `tsupport ψ`, so `z - th ∈ tsupport ψ` and `z = (z - th) + th ∈ K`.
    have hmem : z - t • h ∈ tsupport ψ := by
      by_contra hns
      apply hne
      rw [fderiv_of_notMem_tsupport ℝ hns]
      simp
    exact ⟨(z - t • h, t), ⟨hmem, ht⟩, by simp⟩
  -- Step 5: `F × (0, 1] ⊆ ℝᴺ × [0, 1]`.
  exact h2.mono_set (prod_mono (subset_univ _) Ioc_subset_Icc_self)
/-- **Divergence-test bound for translated directional derivatives** (a step of the translation
estimate behind the compactness theorem, Simon Ch. 2, Thm. 2.6, used in Ch. 3, proof of
Thm. 4.3): if `∫_F div g ≤ C` for every `C¹` field `g` with compact support in `B_{R+1}(0)` and
`|g| ≤ 1`, then `|∫_F Dψ(z - a)[h] dz| ≤ C |h|` for every `C¹` function `ψ` with compact support
in `B_R(0)` and `|ψ| ≤ 1`, and all `a, h` with `|a| ≤ 1`. For `|c| = |h|⁻¹` the field
`G = c ψ(· - a) h` is admissible and `div G(z) = c Dψ(z - a)[h]` (the trace of a rank-one map),
so `c ∫_F Dψ(z - a)[h] dz ≤ C`; take `c = ±|h|⁻¹`. -/
theorem Submission.indCompact_transEst_abs_setIntegral_fderiv_le : ∀ (N : ℕ) (F : Set (Rn N))
    (R C : ℝ), (∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g →
      tsupport g ⊆ Metric.ball (0 : Rn N) (R + 1) → (∀ y, ‖g y‖ ≤ 1) →
      ∫ y in F, Poincare.SimonGMT.Chapter02.euclideanDivergence g y ≤ C) →
    ∀ ψ : Rn N → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball (0 : Rn N) R → (∀ y, |ψ y| ≤ 1) →
      ∀ a h : Rn N, ‖a‖ ≤ 1 → |∫ z in F, fderiv ℝ ψ (z - a) h| ≤ C * ‖h‖ := by
  intro N F R C hdiv ψ hψ hψs hψsub hψ1 a h ha
  -- Step 1. The case `h = 0` is trivial; otherwise `‖h‖ > 0`.
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  have hpos : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hdiff : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  set I := ∫ z in F, fderiv ℝ ψ (z - a) h with hI
  -- Step 2. `ψ(· - a)` has compact support, and `tsupport ψ(· - a) ⊆ B_{R+1}(0)`.
  have hTs : HasCompactSupport (fun y ↦ ψ (y - a)) := by
    simpa [Function.comp_def] using hψs.comp_homeomorph (Homeomorph.subRight a)
  have hTsub : tsupport (fun y ↦ ψ (y - a)) ⊆ Metric.ball 0 (R + 1) := by
    intro y hy
    have hy' : y - a ∈ tsupport ψ := by
      have := tsupport_comp_eq_preimage ψ (Homeomorph.subRight a)
      have hy2 : y ∈ tsupport (ψ ∘ (Homeomorph.subRight a)) := by
        simpa [Function.comp_def] using hy
      rw [this] at hy2
      simpa using hy2
    have h1 := hψsub hy'
    rw [mem_ball_zero_iff] at h1 ⊢
    calc ‖y‖ = ‖(y - a) + a‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - a‖ + ‖a‖ := norm_add_le _ _
      _ < R + 1 := by linarith
  -- Step 3. For `|c| = ‖h‖⁻¹`, testing the hypothesis with `G = c ψ(· - a) h` gives `c I ≤ C`.
  have key : ∀ c : ℝ, |c| = ‖h‖⁻¹ → c * I ≤ C := by
    intro c hc
    set G : Rn N → Rn N := fun y ↦ (c * ψ (y - a)) • h with hG
    have hGc : ContDiff ℝ 1 G :=
      (contDiff_const.mul (hψ.comp (contDiff_id.sub contDiff_const))).smul contDiff_const
    have hGsupp : tsupport G ⊆ tsupport (fun y ↦ ψ (y - a)) := by
      refine (tsupport_smul_subset_left _ _).trans ?_
      exact tsupport_mul_subset_right
    have hGcs : HasCompactSupport G :=
      hTs.of_isClosed_subset (isClosed_tsupport _) hGsupp
    have hGb : ∀ y, ‖G y‖ ≤ 1 := by
      intro y
      simp only [hG, norm_smul, Real.norm_eq_abs, abs_mul, hc]
      calc ‖h‖⁻¹ * |ψ (y - a)| * ‖h‖ = |ψ (y - a)| := by field_simp
        _ ≤ 1 := hψ1 _
    -- `div G(z) = trace (Dφ(z).smulRight h) = Dφ(z)[h] = c Dψ(z - a)[h]`, `φ = c ψ(· - a)`.
    have hdivG : ∀ z, Poincare.SimonGMT.Chapter02.euclideanDivergence G z
        = c * fderiv ℝ ψ (z - a) h := by
      intro z
      have hd : DifferentiableAt ℝ (fun y ↦ c * ψ (y - a)) z :=
        (differentiableAt_const _).mul ((hdiff _).comp z (differentiableAt_id.sub_const a))
      simp only [Poincare.SimonGMT.Chapter02.euclideanDivergence, hG]
      rw [fderiv_smul_const hd]
      have : ((fderiv ℝ (fun y ↦ c * ψ (y - a)) z).smulRight h : Rn N →L[ℝ] Rn N).toLinearMap
          = (fderiv ℝ (fun y ↦ c * ψ (y - a)) z).toLinearMap.smulRight h := by
        ext v; simp
      rw [this, LinearMap.trace_smulRight]
      have hd' : DifferentiableAt ℝ (fun y ↦ ψ (y - a)) z :=
        (hdiff (z - a)).comp z (differentiableAt_id.sub_const a)
      rw [ContinuousLinearMap.coe_coe, fderiv_const_mul hd' c, fderiv_comp_sub]
      simp
    have := hdiv G hGc hGcs (hGsupp.trans hTsub) hGb
    simpa [hdivG, integral_const_mul] using this
  -- Step 4. `c = ‖h‖⁻¹` gives `I ≤ C ‖h‖`, and `c = -‖h‖⁻¹` gives `-I ≤ C ‖h‖`.
  have k1 := key ‖h‖⁻¹ (abs_of_pos (inv_pos.mpr hpos))
  have k2 := key (-‖h‖⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.mpr hpos)])
  have e1 : I ≤ C * ‖h‖ := by
    have := mul_le_mul_of_nonneg_left k1 hpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this
    linarith
  have e2 : -I ≤ C * ‖h‖ := by
    have := mul_le_mul_of_nonneg_left k2 hpos.le
    rw [← mul_assoc, mul_neg, mul_inv_cancel₀ hpos.ne', neg_one_mul] at this
    linarith
  exact abs_le.mpr ⟨by linarith, e1⟩
/-- **A.e. approximation by admissible `C¹` test functions** (the mollification part of the
`L¹`-duality step of the proof of Simon Ch. 2, Thm. 2.6, used in Ch. 3, proof of Thm. 4.3): if `s`
is a.e.-strongly measurable, `|s| ≤ 1` and `s = 0` off `B_R(0)`, then `C¹` functions `ψⱼ` with
compact support, `tsupport ψⱼ ⊆ B_R(0)` and `|ψⱼ| ≤ 1` converge to `s` a.e. Here
`ψⱼ = ρⱼ ⋆ (1_{B_{R - 2δⱼ}(0)} s)`, `δⱼ = R / (4 (j + 1))`, `ρⱼ` the bump with radii
`δⱼ / 2 < δⱼ` normalized to integral `1`: `supp ψⱼ ⊆ B̄_{R - δⱼ}(0)`, `ψⱼ = ρⱼ ⋆ s` near each
point of `B_R(0)` for large `j`, and `ρⱼ ⋆ s → s` a.e. by Lebesgue differentiation. -/
theorem Submission.indCompact_l1Dual_exists_admissible_ae_tendsto : ∀ (N : ℕ) (R : ℝ)
    (s : Rn N → ℝ), 0 < R → AEStronglyMeasurable s volume → (∀ y, |s y| ≤ 1) →
    (∀ y, y ∉ Metric.ball (0 : Rn N) R → s y = 0) →
    ∃ ψ : ℕ → Rn N → ℝ, (∀ j, ContDiff ℝ 1 (ψ j)) ∧ (∀ j, HasCompactSupport (ψ j)) ∧
      (∀ j, tsupport (ψ j) ⊆ Metric.ball (0 : Rn N) R) ∧ (∀ j y, |ψ j y| ≤ 1) ∧
      ∀ᵐ y ∂(volume : Measure (Rn N)), Tendsto (fun j ↦ ψ j y) atTop (𝓝 (s y)) := by
  intro N R s hR hs_meas hs_le hs_zero
  -- Step 1. `|s| ≤ 1_{B_R(0)}` and `L^N(B_R(0)) < ∞`, so `s` is integrable.
  have hs_int : Integrable s volume := by
    refine Integrable.mono' (g := (Metric.ball (0 : Rn N) R).indicator fun _ ↦ (1 : ℝ))
      ((integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne))
      hs_meas (Eventually.of_forall fun y ↦ ?_)
    by_cases hy : y ∈ Metric.ball (0 : Rn N) R
    · simpa [indicator_of_mem hy, Real.norm_eq_abs] using hs_le y
    · simp [indicator_of_notMem hy, hs_zero y hy]
  -- Step 2. Radii `δⱼ = R / (4 (j + 1)) > 0` with `δⱼ → 0`.
  obtain ⟨δ, hδ_pos, hδ_lim⟩ : ∃ δ : ℕ → ℝ, (∀ j, 0 < δ j) ∧ Tendsto δ atTop (𝓝 0) :=
    ⟨fun j ↦ R / 4 * (1 / ((j : ℝ) + 1)), fun j ↦ by positivity,
      by simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (R / 4)⟩
  -- Step 3. Mollifiers `ρⱼ = φⱼ / ∫ φⱼ`, `φⱼ` the bump with `rIn = δⱼ / 2`, `rOut = δⱼ`.
  obtain ⟨ρ, hρ_cd, hρ_cs, hρ_nn, hρ_int, hρ_supp, hρ_le⟩ : ∃ ρ : ℕ → Rn N → ℝ,
      (∀ j, ContDiff ℝ 1 (ρ j)) ∧ (∀ j, HasCompactSupport (ρ j)) ∧ (∀ j y, 0 ≤ ρ j y) ∧
      (∀ j, ∫ y, ρ j y = 1) ∧ (∀ j, Function.support (ρ j) ⊆ Metric.ball 0 (δ j)) ∧
      ∀ j y, ρ j y ≤ 2 ^ finrank ℝ (Rn N) / volume.real (Metric.closedBall (0 : Rn N) (δ j)) := by
    let φ : ℕ → ContDiffBump (0 : Rn N) := fun j ↦
      ⟨δ j / 2, δ j, half_pos (hδ_pos j), half_lt_self (hδ_pos j)⟩
    have hφ_int : ∀ j, Integrable (φ j) volume := fun j ↦
      (φ j).continuous.integrable_of_hasCompactSupport (φ j).hasCompactSupport
    -- `φⱼ = 1` on `B̄_{δⱼ/2}(0)` and `φⱼ ≥ 0`, so `L^N(B̄_{δⱼ/2}(0)) ≤ ∫ φⱼ`.
    have hφ_ge : ∀ j, volume.real (Metric.closedBall (0 : Rn N) (δ j / 2)) ≤ ∫ y, φ j y := by
      intro j
      calc volume.real (Metric.closedBall (0 : Rn N) (δ j / 2))
          = ∫ y in Metric.closedBall (0 : Rn N) (δ j / 2), (1 : ℝ) := by simp
        _ = ∫ y in Metric.closedBall (0 : Rn N) (δ j / 2), φ j y :=
          setIntegral_congr_fun measurableSet_closedBall
            fun y hy ↦ ((φ j).one_of_mem_closedBall hy).symm
        _ ≤ ∫ y, φ j y :=
          setIntegral_le_integral (hφ_int j) (Eventually.of_forall fun y ↦ (φ j).nonneg)
    have hball : ∀ j, 0 < volume.real (Metric.closedBall (0 : Rn N) (δ j / 2)) := fun j ↦
      ENNReal.toReal_pos (Metric.measure_closedBall_pos _ _ (half_pos (hδ_pos j))).ne'
        measure_closedBall_lt_top.ne
    have hI : ∀ j, 0 < ∫ y, φ j y := fun j ↦ (hball j).trans_le (hφ_ge j)
    -- Scaling: `L^N(B̄_{δⱼ}(0)) = 2^N L^N(B̄_{δⱼ/2}(0))`.
    have hscale : ∀ j, volume.real (Metric.closedBall (0 : Rn N) (δ j)) =
        2 ^ finrank ℝ (Rn N) * volume.real (Metric.closedBall (0 : Rn N) (δ j / 2)) := by
      intro j
      have h := Measure.addHaar_closedBall_mul (volume : Measure (Rn N)) 0 zero_le_two
        (half_pos (hδ_pos j)).le
      rw [show (2 : ℝ) * (δ j / 2) = δ j by ring] at h
      rw [measureReal_def, measureReal_def, h, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity)]
    refine ⟨fun j y ↦ (∫ y, φ j y)⁻¹ * φ j y, fun j ↦ contDiff_const.mul (φ j).contDiff,
      fun j ↦ (φ j).hasCompactSupport.mul_left,
      fun j y ↦ mul_nonneg (inv_nonneg.2 (hI j).le) (φ j).nonneg, fun j ↦ ?_, fun j y hy ↦ ?_,
      fun j y ↦ ?_⟩
    · show ∫ y, (∫ y, φ j y)⁻¹ * φ j y = 1
      rw [integral_const_mul, inv_mul_cancel₀ (hI j).ne']
    · have hy' : φ j y ≠ 0 := right_ne_zero_of_mul hy
      rw [← Function.mem_support, (φ j).support_eq] at hy'
      exact hy'
    · show (∫ y, φ j y)⁻¹ * φ j y ≤ _
      calc (∫ y, φ j y)⁻¹ * φ j y ≤ (∫ y, φ j y)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (φ j).le_one (inv_nonneg.2 (hI j).le)
        _ ≤ (volume.real (Metric.closedBall (0 : Rn N) (δ j / 2)))⁻¹ := by
            rw [mul_one]; exact inv_anti₀ (hball j) (hφ_ge j)
        _ = 2 ^ finrank ℝ (Rn N) / volume.real (Metric.closedBall (0 : Rn N) (δ j)) := by
            rw [hscale j]; field_simp
  -- Step 4. Truncations `sⱼ = 1_{B_{R - 2δⱼ}(0)} s`.
  obtain ⟨sj, hsj_int, hsj_le, hsj_supp, hsj_eq⟩ : ∃ sj : ℕ → Rn N → ℝ,
      (∀ j, Integrable (sj j) volume) ∧ (∀ j y, |sj j y| ≤ 1) ∧
      (∀ j, Function.support (sj j) ⊆ Metric.ball 0 (R - 2 * δ j)) ∧
      ∀ j y, y ∈ Metric.ball (0 : Rn N) (R - 2 * δ j) → sj j y = s y := by
    refine ⟨fun j ↦ (Metric.ball (0 : Rn N) (R - 2 * δ j)).indicator s,
      fun j ↦ hs_int.indicator measurableSet_ball, fun j y ↦ ?_,
      fun j ↦ support_indicator_subset, fun j y hy ↦ indicator_of_mem hy s⟩
    show |(Metric.ball (0 : Rn N) (R - 2 * δ j)).indicator s y| ≤ 1
    by_cases hy : y ∈ Metric.ball (0 : Rn N) (R - 2 * δ j)
    · rw [indicator_of_mem hy]; exact hs_le y
    · rw [indicator_of_notMem hy, abs_zero]; exact zero_le_one
  -- Step 7. `supp (ρⱼ ⋆ sⱼ) ⊆ B_{δⱼ}(0) + B_{R - 2δⱼ}(0) ⊆ B̄_{R - δⱼ}(0) ⊆ B_R(0)`.
  have hψ_supp : ∀ j, Function.support (convolution (ρ j) (sj j)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆ Metric.closedBall 0 (R - δ j) := by
    intro j x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 (support_convolution_subset _ hx)
    have ha' := mem_ball_zero_iff.1 (hρ_supp j ha)
    have hb' := mem_ball_zero_iff.1 (hsj_supp j hb)
    rw [mem_closedBall_zero_iff]
    linarith [norm_add_le a b]
  have hψ_tsupp : ∀ j, tsupport (convolution (ρ j) (sj j)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆ Metric.closedBall 0 (R - δ j) :=
    fun j ↦ closure_minimal (hψ_supp j) Metric.isClosed_closedBall
  have hball_sub : ∀ j, Metric.closedBall (0 : Rn N) (R - δ j) ⊆ Metric.ball 0 R :=
    fun j ↦ Metric.closedBall_subset_ball (by linarith [hδ_pos j])
  -- Step 9. Lebesgue differentiation: `ρⱼ ⋆ s → s` almost everywhere.
  have hconv : ∀ᵐ x ∂(volume : Measure (Rn N)),
      Tendsto (fun j ↦ convolution (ρ j) s (ContinuousLinearMap.lsmul ℝ ℝ) volume x) atTop
        (𝓝 (s x)) := by
    have hδ' : Tendsto δ atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hδ_lim, Eventually.of_forall hδ_pos⟩
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume
      hs_int.locallyIntegrable 1] with x hx
    have hav := hx (fun _ ↦ x) δ hδ' (Eventually.of_forall fun j ↦
      Metric.mem_closedBall_self (by linarith [hδ_pos j]))
    simp only [convolution_eq_swap, ContinuousLinearMap.lsmul_apply]
    refine tendsto_integral_smul_of_tendsto_average_norm_sub
      (a := fun j ↦ Metric.closedBall x (δ j)) (g := fun j y ↦ ρ j (x - y))
      (2 ^ finrank ℝ (Rn N)) hav (Eventually.of_forall fun j ↦ hs_int.integrableOn)
      (tendsto_const_nhds.congr fun j ↦ ?_) (Eventually.of_forall fun j y hy ↦ ?_)
      (Eventually.of_forall fun j y ↦ ?_)
    · rw [integral_sub_left_eq_self (ρ j) volume x, hρ_int j]
    · rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
      exact (mem_ball_zero_iff.1 (hρ_supp j hy)).le
    · show |ρ j (x - y)| ≤ 2 ^ finrank ℝ (Rn N) / volume.real (Metric.closedBall x (δ j))
      rw [abs_of_nonneg (hρ_nn j _), Measure.addHaar_real_closedBall_center]
      exact hρ_le j (x - y)
  -- Steps 5 (`C¹`), 7 (support) and 11.
  refine ⟨fun j ↦ convolution (ρ j) (sj j) (ContinuousLinearMap.lsmul ℝ ℝ) volume,
    fun j ↦ (hρ_cs j).contDiff_convolution_left _ (hρ_cd j) (hsj_int j).locallyIntegrable,
    fun j ↦ HasCompactSupport.intro (isCompact_closedBall 0 (R - δ j))
      fun x hx ↦ Function.notMem_support.1 fun h ↦ hx (hψ_supp j h),
    fun j ↦ (hψ_tsupp j).trans (hball_sub j), fun j y ↦ ?_, ?_⟩
  · -- Step 6. `|ρⱼ ⋆ sⱼ| ≤ ∫ ρⱼ = 1`.
    have h := dist_convolution_le (μ := volume) (x₀ := y) (z₀ := (0 : ℝ)) zero_le_one
      (hρ_supp j) (hρ_nn j) (hρ_int j) (hsj_int j).aestronglyMeasurable
      fun x _ ↦ by rw [Real.dist_0_eq_abs]; exact hsj_le j x
    rwa [Real.dist_0_eq_abs] at h
  · -- Step 10. On `B_R(0)`, eventually `ψⱼ = ρⱼ ⋆ s` (step 8); off `B_R(0)`, `ψⱼ = 0 = s`.
    filter_upwards [hconv] with x hx
    by_cases hxB : x ∈ Metric.ball (0 : Rn N) R
    · have hx' := mem_ball_zero_iff.1 hxB
      have hη : 0 < (R - ‖x‖) / 3 := by linarith
      refine hx.congr' ?_
      filter_upwards [hδ_lim.eventually (gt_mem_nhds hη)] with j hj
      show convolution (ρ j) s _ volume x = convolution (ρ j) (sj j) _ volume x
      rw [convolution_def, convolution_def]
      refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
      show ContinuousLinearMap.lsmul ℝ ℝ (ρ j t) (s (x - t)) =
        ContinuousLinearMap.lsmul ℝ ℝ (ρ j t) (sj j (x - t))
      by_cases ht : ρ j t = 0
      · simp [ht]
      · have ht' := mem_ball_zero_iff.1 (hρ_supp j ht)
        rw [hsj_eq j (x - t) (mem_ball_zero_iff.2 (by linarith [norm_sub_le x t]))]
    · rw [hs_zero x hxB]
      refine tendsto_const_nhds.congr fun j ↦ ?_
      show 0 = convolution (ρ j) (sj j) _ volume x
      by_contra h
      exact hxB ((hψ_supp j).trans (hball_sub j) (Ne.symm h))
/-- **Dominated convergence for pairings with a function integrable on a ball**: the limit step of
the `L¹`-duality argument in the compactness theorem (Simon Ch. 2, Thm. 2.6) as used in the proof
of Ch. 3, Thm. 4.3. If `w` is integrable on `B = B_R(0)` and the a.e.-strongly measurable `ψ_j`
satisfy `|ψ_j| ≤ 1`, vanish off `B` and converge a.e. to `s`, then `∫ w ψ_j → ∫ w s`. Dominated
convergence with the integrable bound `1_B |w|`; `w ψ_j = 1_B (w ψ_j)` is a.e.-strongly measurable
because `w` is on `B`. No measurability of `s` is needed, and `R ≤ 0` (`B = ∅`) is not special. -/
theorem Submission.indCompact_l1Dual_tendsto_integral_mul : ∀ (N : ℕ) (w s : Rn N → ℝ) (R : ℝ)
    (ψ : ℕ → Rn N → ℝ), IntegrableOn w (Metric.ball (0 : Rn N) R) volume →
    (∀ j, AEStronglyMeasurable (ψ j) volume) → (∀ j y, |ψ j y| ≤ 1) →
    (∀ j y, y ∉ Metric.ball (0 : Rn N) R → ψ j y = 0) →
    (∀ᵐ y ∂(volume : Measure (Rn N)), Tendsto (fun j ↦ ψ j y) atTop (𝓝 (s y))) →
    Tendsto (fun j ↦ ∫ y, w y * ψ j y) atTop (𝓝 (∫ y, w y * s y)) := by
  intro N w s R ψ hw hψm hψ1 hψ0 hlim
  have hB : MeasurableSet (Metric.ball (0 : Rn N) R) := Metric.isOpen_ball.measurableSet
  -- Off the ball every `w ψ_j` vanishes, so `w ψ_j = 1_B (w ψ_j)`.
  have hind : ∀ j, (fun y ↦ w y * ψ j y) = (Metric.ball (0 : Rn N) R).indicator
      fun y ↦ w y * ψ j y := fun j ↦ funext fun y ↦ by
    by_cases hy : y ∈ Metric.ball (0 : Rn N) R
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy, hψ0 j y hy, mul_zero]
  refine tendsto_integral_of_dominated_convergence ((Metric.ball (0 : Rn N) R).indicator
      fun y ↦ ‖w y‖) (fun j ↦ ?_) ((integrable_indicator_iff hB).2 hw.norm)
      (fun j ↦ ae_of_all _ fun y ↦ ?_) ?_
  · -- Measurability: `w` is a.e.-strongly measurable on the ball.
    rw [hind j, aestronglyMeasurable_indicator_iff hB]
    exact hw.aestronglyMeasurable.mul (hψm j).restrict
  · -- Domination by `1_B |w|`.
    by_cases hy : y ∈ Metric.ball (0 : Rn N) R
    · rw [indicator_of_mem hy, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) ((Real.norm_eq_abs _).trans_le (hψ1 j y))
    · rw [indicator_of_notMem hy, hψ0 j y hy, mul_zero, norm_zero]
  · -- Pointwise a.e. convergence.
    filter_upwards [hlim] with y hy
    exact hy.const_mul (w y)

/-- **`L¹` norm on a ball by duality with `C¹` test functions** (the `L¹`-duality step of the
mollification proof of Simon Ch. 2, Thm. 2.6, used in Ch. 3, proof of Thm. 4.3): if `w` is
integrable on `B_R(0)` and `∫ w ψ ≤ M` for every `C¹` function `ψ` with compact support,
`tsupport ψ ⊆ B_R(0)` and `|ψ| ≤ 1`, then `∫_{B_R(0)} |w| ≤ M`. The test `ψ = 0` settles the
empty ball `R ≤ 0`. For `R > 0` the sign function `s = 1_{B_R(0)} sgn w` (here `sgn 0 = 1`)
satisfies `w s = 1_{B_R(0)} |w|`; admissible `ψⱼ → s` a.e.
(`indCompact_l1Dual_exists_admissible_ae_tendsto`) and dominated convergence
(`indCompact_l1Dual_tendsto_integral_mul`) give `M ≥ ∫ w ψⱼ → ∫_{B_R(0)} |w|`. -/
theorem Submission.indCompact_ball_integral_abs_le_of_test_bound : ∀ (N : ℕ) (w : Rn N → ℝ)
    (R M : ℝ), IntegrableOn w (Metric.ball (0 : Rn N) R) volume →
    (∀ ψ : Rn N → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball (0 : Rn N) R → (∀ y, |ψ y| ≤ 1) → ∫ y, w y * ψ y ≤ M) →
    ∫ y in Metric.ball (0 : Rn N) R, |w y| ≤ M := by
  intro N w R M hw hM
  rcases le_or_gt R 0 with hR | hR
  · -- Empty ball: the admissible test `ψ = 0` gives `0 ≤ M`.
    rw [Metric.ball_eq_empty.2 hR, setIntegral_empty]
    simpa using hM 0 contDiff_const HasCompactSupport.zero (by simp) (by simp)
  -- The sign function `s = 1_{B_R(0)} sgn w`: `|s| ≤ 1` and `s = 0` off the ball.
  obtain ⟨s, hs⟩ : ∃ s : Rn N → ℝ,
      s = (Metric.ball (0 : Rn N) R).indicator fun y ↦ if 0 ≤ w y then 1 else -1 := ⟨_, rfl⟩
  have hs_meas : AEStronglyMeasurable s volume := by
    rw [hs, aestronglyMeasurable_indicator_iff measurableSet_ball]
    exact ((Measurable.ite measurableSet_Ici measurable_const measurable_const).comp_aemeasurable
      hw.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hs_le : ∀ y, |s y| ≤ 1 := by
    intro y
    by_cases hy : y ∈ Metric.ball (0 : Rn N) R
    · rw [hs, indicator_of_mem hy]
      split_ifs <;> simp
    · simp [hs, indicator_of_notMem hy]
  have hs_zero : ∀ y, y ∉ Metric.ball (0 : Rn N) R → s y = 0 := fun y hy ↦ by
    rw [hs, indicator_of_notMem hy]
  -- `w s = 1_{B_R(0)} |w|`.
  have hws : ∫ y, w y * s y = ∫ y in Metric.ball (0 : Rn N) R, |w y| := by
    rw [← integral_indicator measurableSet_ball]
    congr 1
    funext y
    by_cases hy : y ∈ Metric.ball (0 : Rn N) R
    · rw [hs, indicator_of_mem hy, indicator_of_mem hy]
      split_ifs with h
      · rw [mul_one, abs_of_nonneg h]
      · rw [mul_neg_one, abs_of_neg (not_le.1 h)]
    · rw [hs, indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]
  -- Admissible `ψⱼ → s` a.e., and dominated convergence `∫ w ψⱼ → ∫ w s`.
  obtain ⟨ψ, hψ, hψc, hψt, hψb, hψs⟩ :=
    Submission.indCompact_l1Dual_exists_admissible_ae_tendsto N R s hR hs_meas hs_le hs_zero
  have hlim := Submission.indCompact_l1Dual_tendsto_integral_mul N w s R ψ hw
    (fun j ↦ (hψ j).continuous.aestronglyMeasurable) hψb
    (fun j y hy ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hy (hψt j h)) hψs
  rw [hws] at hlim
  exact le_of_tendsto' hlim fun j ↦ hM (ψ j) (hψ j) (hψc j) (hψt j) (hψb j)

/-- **Translation estimate for the indicator of a set with bounded perimeter in `B_{R+1}(0)`**
(the `L¹` translation bound behind the compactness theorem for sets of locally bounded perimeter,
Simon Ch. 2, Thm. 2.6, used in Ch. 3, proof of Thm. 4.3): if `∫_F div g ≤ C` for every `C¹`
field `g` with compact support in `B_{R+1}(0)` and `|g| ≤ 1`, then
`Lᴺ(B_R(0) ∩ (F_h Δ F)) ≤ C |h|` for `|h| ≤ 1`, where `F_h = {y : y + h ∈ F}`. With
`w = 1_F(· + h) - 1_F` we have `Lᴺ(B_R(0) ∩ (F_h Δ F)) = ∫_{B_R(0)} |w|`, and for every `C¹`
test function `ψ` with compact support in `B_R(0)` and `|ψ| ≤ 1`,
`∫ w ψ = ∫_F (ψ(z - h) - ψ(z)) dz = -∫_0^1 ∫_F Dψ(z - t h)[h] dz dt ≤ C |h|`, since each inner
integral is the integral over `F` of the divergence of the field `ψ(· - t h) h`. `L¹` duality on
`B_R(0)` concludes. -/
theorem Submission.indCompact_translation_estimate : ∀ (N : ℕ) (F : Set (Rn N)) (R C : ℝ), NullMeasurableSet F volume → (∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ Metric.ball (0 : Rn N) (R + 1) → (∀ y, ‖g y‖ ≤ 1) → ∫ y in F, Poincare.SimonGMT.Chapter02.euclideanDivergence g y ≤ C) → ∀ h : Rn N, ‖h‖ ≤ 1 → volume (Metric.ball (0 : Rn N) R ∩ symmDiff ((fun y ↦ y + h) ⁻¹' F) F) ≤ ENNReal.ofReal (C * ‖h‖) := by
  intro N F R C hF hdiv h hh
  -- `F_h = (· + h)⁻¹ F` is null-measurable, since `y ↦ y + h` preserves `Lᴺ`.
  have hA : NullMeasurableSet ((fun y ↦ y + h) ⁻¹' F) volume :=
    hF.preimage (measurePreserving_add_right volume h).quasiMeasurePreserving
  -- Step 4. `Lᴺ(B_R(0) ∩ (F_h Δ F)) = ofReal ∫_{B_R(0)} |w|` with `w = 1_F(· + h) - 1_F`,
  -- because `1_{F_h}(y) = 1_F(y + h)`. It remains to show `∫_{B_R(0)} |w| ≤ C |h|`.
  rw [Submission.indCompact_transEst_volume_symmDiff_eq_integral N _ F R hA hF]
  apply ENNReal.ofReal_le_ofReal
  have hw : ∀ y, ((fun y ↦ y + h) ⁻¹' F).indicator (1 : Rn N → ℝ) y
      = F.indicator (1 : Rn N → ℝ) (y + h) := fun y ↦ rfl
  simp only [hw]
  -- Step 6. `L¹` duality on `B_R(0)` with `M = C |h|`.
  apply Submission.indCompact_ball_integral_abs_le_of_test_bound N
    (fun y ↦ F.indicator (1 : Rn N → ℝ) (y + h) - F.indicator (1 : Rn N → ℝ) y) R (C * ‖h‖)
  · -- `w` is a.e.-strongly measurable with `|w| ≤ 1`, and `Lᴺ(B_R(0)) < ∞`.
    refine Measure.integrableOn_of_bounded (M := 1) measure_ball_lt_top.ne ?_ ?_
    · have h1 : AEStronglyMeasurable (fun y ↦ F.indicator (1 : Rn N → ℝ) (y + h)) volume :=
        (aestronglyMeasurable_const (b := (1 : ℝ))).indicator₀ hA
      have h2 : AEStronglyMeasurable (fun y ↦ F.indicator (1 : Rn N → ℝ) y) volume :=
        (aestronglyMeasurable_const (b := (1 : ℝ))).indicator₀ hF
      exact h1.sub h2
    · refine Eventually.of_forall fun y ↦ ?_
      by_cases h1 : y + h ∈ F <;> by_cases h2 : y ∈ F <;> simp [h1, h2]
  · -- Step 5. Fix a `C¹` test function `ψ` with compact support in `B_R(0)` and `|ψ| ≤ 1`.
    intro ψ hψ hψs hψsub hψ1
    -- (a) translation invariance and (b), (d) the fundamental theorem of calculus and Fubini:
    -- `∫ w ψ = ∫_F (ψ(z - h) - ψ(z)) dz = -∫_0^1 ∫_F Dψ(z - t h)[h] dz dt`.
    rw [Submission.indCompact_transEst_integral_indicator_shift_mul N F ψ h hF
        (hψ.continuous.integrable_of_hasCompactSupport hψs),
      Submission.indCompact_transEst_setIntegral_shift_sub_ftc N F ψ h hψ hψs]
    -- (c) for `t ∈ (0, 1]`, `‖t h‖ ≤ 1`, so `|∫_F Dψ(z - t h)[h] dz| ≤ C |h|`; (e) integrate.
    have hb : ‖∫ t in (0 : ℝ)..1, ∫ z in F, fderiv ℝ ψ (z - t • h) h‖ ≤ C * ‖h‖ * |1 - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Real.norm_eq_abs]
      apply Submission.indCompact_transEst_abs_setIntegral_fderiv_le N F R C hdiv ψ hψ hψs hψsub
        hψ1 (t • h) h
      rw [Set.uIoc_of_le zero_le_one] at ht
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      nlinarith [ht.2, norm_nonneg h]
    rw [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at hb
    linarith [neg_le_abs (∫ t in (0 : ℝ)..1, ∫ z in F, fderiv ℝ ψ (z - t • h) h)]
/-- **L¹ mollification error of an indicator** (Step 2 of the supplied proof that translation
estimates and uniformly Cauchy mollifications give local Cauchy in measure, part of the
compactness of indicators used for De Giorgi's theorem, Simon Ch. 3, Theorem 4.3; cf. the
mollification argument in the proof of Simon Ch. 2, Theorem 2.6). Let `F ⊆ ℝᴺ` be
`Lᴺ`-measurable and `ρ ≥ 0` continuous with `∫ ρ = 1` and support in `B̄_σ(0)`. If
`Lᴺ(B_R ∩ (F_h Δ F)) ≤ C|h|` for all `|h| ≤ σ`, where `F_h = {y : y + h ∈ F}` and `C ≥ 0`, then
`∫_{B_R} |∫_F ρ(y - z) dz - χ_F(y)| dy ≤ σ C`. -/
theorem Submission.indCompact_mollCauchy_l1_error : ∀ (N : ℕ) (F : Set (Rn N)) (ρ : Rn N → ℝ) (σ R C : ℝ), NullMeasurableSet F volume → Continuous ρ → HasCompactSupport ρ → (∀ y, 0 ≤ ρ y) → ∫ y, ρ y = 1 → Function.support ρ ⊆ Metric.closedBall (0 : Rn N) σ → 0 ≤ C → (∀ h : Rn N, ‖h‖ ≤ σ → volume (Metric.ball (0 : Rn N) R ∩ symmDiff ((fun y ↦ y + h) ⁻¹' F) F) ≤ ENNReal.ofReal (C * ‖h‖)) → ∫⁻ y in Metric.ball (0 : Rn N) R, ENNReal.ofReal |(∫ z in F, ρ (y - z)) - F.indicator (fun _ ↦ (1 : ℝ)) y| ≤ ENNReal.ofReal (σ * C) := by
  intro N F ρ σ R C hF hρc hρs hρ0 hρ1 hsupp hC htr
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have hρm : Measurable ρ := hρc.measurable
  -- Step 1: replace `F` by its measurable hull `F'`.
  set F' := toMeasurable volume F
  have hF'm : MeasurableSet F' := measurableSet_toMeasurable _ _
  have hae : F' =ᵐ[volume] F := hF.toMeasurable_ae_eq
  have hind : F'.indicator (fun _ ↦ (1 : ℝ)) =ᵐ[volume] F.indicator (fun _ ↦ (1 : ℝ)) :=
    indicator_ae_eq_of_ae_eq_set hae
  have htr' : ∀ h : Rn N, ‖h‖ ≤ σ → volume (Metric.ball (0 : Rn N) R ∩
      symmDiff ((fun y ↦ y + h) ⁻¹' F') F') ≤ ENNReal.ofReal (C * ‖h‖) := by
    intro h hh
    have hpre : (fun y ↦ y + h) ⁻¹' F' =ᵐ[volume] (fun y ↦ y + h) ⁻¹' F :=
      (measurePreserving_add_right volume h).quasiMeasurePreserving.preimage_ae_eq hae
    rw [measure_congr (ae_eq_set_inter (EventuallyEq.refl _ _) (ae_eq_set_symmDiff hpre hae))]
    exact htr h hh
  have hcongr : ∫⁻ y in Metric.ball (0 : Rn N) R,
      ENNReal.ofReal |(∫ z in F, ρ (y - z)) - F.indicator (fun _ ↦ (1 : ℝ)) y| =
      ∫⁻ y in Metric.ball (0 : Rn N) R,
        ENNReal.ofReal |(∫ z in F', ρ (y - z)) - F'.indicator (fun _ ↦ (1 : ℝ)) y| := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hind] with y hy
    rw [setIntegral_congr_set hae, hy]
  rw [hcongr]
  clear_value F'
  clear hcongr htr hind hae hF
  set χ : Rn N → ℝ := F'.indicator (fun _ ↦ (1 : ℝ)) with hχ
  set B := Metric.ball (0 : Rn N) R with hB
  have hχm : Measurable χ := measurable_const.indicator hF'm
  have hχb : ∀ x, |χ x| ≤ 1 := by
    intro x; by_cases hx : x ∈ F' <;> simp [hχ, hx]
  have hχd : ∀ x x', |χ x - χ x'| ≤ 1 := by
    intro x x'; by_cases hx : x ∈ F' <;> by_cases hx' : x' ∈ F' <;> simp [hχ, hx, hx']
  -- Step 3: pointwise bound.
  have hpt : ∀ y, ENNReal.ofReal |(∫ z in F', ρ (y - z)) - χ y| ≤
      ∫⁻ h, ENNReal.ofReal (ρ h) * ENNReal.ofReal |χ (y - h) - χ y| := by
    intro y
    have h1 : (∫ z in F', ρ (y - z)) = ∫ h, ρ h * χ (y - h) := by
      rw [← integral_indicator hF'm]
      have : (fun z ↦ F'.indicator (fun z ↦ ρ (y - z)) z) =
          fun z ↦ (fun h ↦ ρ h * χ (y - h)) (y - z) := by
        ext z
        by_cases hz : z ∈ F' <;> simp [hχ, hz]
      rw [this, integral_sub_left_eq_self (fun h ↦ ρ h * χ (y - h)) volume y]
    have hint1 : Integrable (fun h ↦ ρ h * χ (y - h)) := by
      refine hρi.mono' (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun h ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 h)]
      exact mul_le_of_le_one_right (hρ0 h) (hχb _)
    have h3 : (∫ z in F', ρ (y - z)) - χ y = ∫ h, ρ h * (χ (y - h) - χ y) := by
      have e : (fun h ↦ ρ h * (χ (y - h) - χ y)) = fun h ↦ ρ h * χ (y - h) - ρ h * χ y := by
        ext h; ring
      rw [e, integral_sub hint1 (hρi.mul_const _), integral_mul_const, hρ1, one_mul, h1]
    have hint3 : Integrable (fun h ↦ ρ h * |χ (y - h) - χ y|) := by
      refine hρi.mono' (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun h ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 h), abs_abs]
      exact mul_le_of_le_one_right (hρ0 h) (hχd _ _)
    rw [h3]
    calc ENNReal.ofReal |∫ h, ρ h * (χ (y - h) - χ y)|
        ≤ ENNReal.ofReal (∫ h, |ρ h * (χ (y - h) - χ y)|) :=
          ENNReal.ofReal_le_ofReal abs_integral_le_integral_abs
      _ = ENNReal.ofReal (∫ h, ρ h * |χ (y - h) - χ y|) := by
          congr 2; ext h; rw [abs_mul, abs_of_nonneg (hρ0 h)]
      _ = ∫⁻ h, ENNReal.ofReal (ρ h * |χ (y - h) - χ y|) :=
          ofReal_integral_eq_lintegral_ofReal hint3
            (ae_of_all _ fun h ↦ mul_nonneg (hρ0 h) (abs_nonneg _))
      _ = ∫⁻ h, ENNReal.ofReal (ρ h) * ENNReal.ofReal |χ (y - h) - χ y| := by
          congr 1; ext h; rw [ENNReal.ofReal_mul (hρ0 h)]
  -- Steps 4–6: Tonelli, inner integral, conclusion.
  calc ∫⁻ y in B, ENNReal.ofReal |(∫ z in F', ρ (y - z)) - χ y|
      ≤ ∫⁻ y in B, ∫⁻ h, ENNReal.ofReal (ρ h) * ENNReal.ofReal |χ (y - h) - χ y| :=
        lintegral_mono hpt
    _ = ∫⁻ h, ∫⁻ y in B, ENNReal.ofReal (ρ h) * ENNReal.ofReal |χ (y - h) - χ y| := by
        apply lintegral_lintegral_swap
        apply Measurable.aemeasurable
        fun_prop
    _ ≤ ∫⁻ h, ENNReal.ofReal (ρ h) * ENNReal.ofReal (σ * C) := by
        refine lintegral_mono fun h ↦ ?_
        dsimp only
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        by_cases hρh : ρ h = 0
        · simp [hρh]
        · gcongr
          have hnorm : ‖h‖ ≤ σ := by
            have := hsupp hρh
            simpa [Metric.mem_closedBall, dist_zero_right] using this
          have hmeas : MeasurableSet (symmDiff ((fun y ↦ y + -h) ⁻¹' F') F') :=
            (measurable_add_const (-h) hF'm).symmDiff hF'm
          have hset : ∀ y, ENNReal.ofReal |χ (y - h) - χ y| =
              (symmDiff ((fun y ↦ y + -h) ⁻¹' F') F').indicator 1 y := by
            intro y
            by_cases h1 : y - h ∈ F' <;> by_cases h2 : y ∈ F' <;>
              simp [hχ, h1, h2, Set.mem_symmDiff, ← sub_eq_add_neg]
          simp_rw [hset]
          rw [lintegral_indicator_one hmeas, Measure.restrict_apply hmeas, Set.inter_comm]
          calc volume (B ∩ symmDiff ((fun y ↦ y + -h) ⁻¹' F') F')
              ≤ ENNReal.ofReal (C * ‖-h‖) := htr' (-h) (by rwa [norm_neg])
            _ ≤ ENNReal.ofReal (σ * C) := by
              apply ENNReal.ofReal_le_ofReal
              rw [norm_neg, mul_comm]
              exact mul_le_mul_of_nonneg_right hnorm hC
    _ = (∫⁻ h, ENNReal.ofReal (ρ h)) * ENNReal.ofReal (σ * C) :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (σ * C) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hρi (ae_of_all _ hρ0), hρ1, ENNReal.ofReal_one,
          one_mul]
/-- **Continuity of the mollified set integral** (Step 1 of the supplied proof that translation
estimates and uniformly Cauchy mollifications give local Cauchy in measure, part of the
compactness of indicators used for De Giorgi's theorem, Simon Ch. 3, Theorem 4.3; cf. the
mollification argument in the proof of Simon Ch. 2, Theorem 2.6). For an arbitrary `F ⊆ ℝᴺ` and a
continuous, compactly supported `ρ`, the map `y ↦ ∫_F ρ(y - z) dz` is continuous: it is the
convolution of `1` with `ρ` for the locally finite measure `Lᴺ ⌞ F`. -/
theorem Submission.indCompact_mollCauchy_setIntegral_continuous : ∀ (N : ℕ) (F : Set (Rn N)) (ρ : Rn N → ℝ), Continuous ρ → HasCompactSupport ρ → Continuous (fun y : Rn N ↦ ∫ z in F, ρ (y - z)) := by
  intro N F ρ hρ hρc
  -- `y ↦ ∫_F ρ(y - z) dz` is the convolution of `1` with `ρ` for the measure `volume.restrict F`.
  have hconv : (fun y : Rn N ↦ ∫ z in F, ρ (y - z)) =
      convolution (fun _ ↦ (1 : ℝ)) ρ (ContinuousLinearMap.lsmul ℝ ℝ) (volume.restrict F) := by
    ext y
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, one_smul]
  rw [hconv]
  -- `volume.restrict F` is locally finite for every `F`, so the constant `1` is locally
  -- integrable; convolving with the continuous, compactly supported `ρ` gives a continuous map.
  exact hρc.continuous_convolution_right _ (locallyIntegrable_const 1) hρ

/-- **Translation estimates and uniformly Cauchy mollifications give local Cauchy in measure**
(Steps 3 and 6 of the supplied proof of the compactness of indicators used for De Giorgi's theorem,
Simon Ch. 3, Theorem 4.3; cf. the mollification argument in the proof of Simon Ch. 2,
Theorem 2.6). Let `ρ_m ≥ 0` be continuous kernels with `∫ ρ_m = 1` and support in
`B̄_{1/(m+1)}(0)`, and `v_{m,k}(y) = ∫_{F_k} ρ_m(y - z) dz`. If the `F_k` satisfy a uniform local
translation estimate `Lᴺ(B_R ∩ ((F_k)_h Δ F_k)) ≤ C_R |h|` and, for each `m`, the `v_{m,k}` are
uniformly Cauchy on `B̄_m(0)`, then `Lᴺ(B_R ∩ (F_k Δ F_l)) → 0`: on `B_R ⊆ B̄_m(0)`,
`1_{F_k Δ F_l} ≤ |v_{m,k} - 1_{F_k}| + |v_{m,k} - v_{m,l}| + |v_{m,l} - 1_{F_l}|`, and the outer
terms have `L¹(B_R)`-norm at most `C_R / (m + 1)`. -/
theorem Submission.indCompact_local_cauchy_of_mollified_cauchy : ∀ (N : ℕ) (F : ℕ → Set (Rn N)) (ρ : ℕ → Rn N → ℝ), (∀ k, NullMeasurableSet (F k) volume) → (∀ m, Continuous (ρ m)) → (∀ m, HasCompactSupport (ρ m)) → (∀ m y, 0 ≤ ρ m y) → (∀ m, ∫ y, ρ m y = 1) → (∀ m, Function.support (ρ m) ⊆ Metric.closedBall (0 : Rn N) (1 / ((m : ℝ) + 1))) → (∀ R : ℕ, ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ h : Rn N, ‖h‖ ≤ 1 → volume (Metric.ball (0 : Rn N) R ∩ symmDiff ((fun y ↦ y + h) ⁻¹' F k) (F k)) ≤ ENNReal.ofReal (C * ‖h‖)) → (∀ (m : ℕ) (ε : ℝ), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ l ≥ k₀, ∀ y ∈ Metric.closedBall (0 : Rn N) m, |(∫ z in F k, ρ m (y - z)) - ∫ z in F l, ρ m (y - z)| ≤ ε) → ∀ (R : ℕ) (ε : ℝ≥0∞), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ l ≥ k₀, volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) (F l)) ≤ ε := by
  intro N F ρ hF hρc hρs hρ0 hρ1 hρsupp htrans hcauchy R ε hε
  -- For `ε = ∞` any `k₀` works; otherwise put `e := ε.toReal > 0`, so that `ε = ofReal e`.
  rcases eq_or_ne ε ∞ with rfl | hε_top
  · exact ⟨0, fun _ _ _ _ ↦ le_top⟩
  set e := ε.toReal
  have he : 0 < e := ENNReal.toReal_pos hε.ne' hε_top
  have hεe : ε = ENNReal.ofReal e := (ENNReal.ofReal_toReal hε_top).symm
  -- (a) The translation estimate on `B_R`, with the nonnegative constant `C' := max C 0`.
  obtain ⟨C, k₁, hC⟩ := htrans R
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  -- (b) A kernel index `m ≥ R` with `σ_m C' ≤ e / 4`, where `σ_m := 1 / (m + 1) ≤ 1`.
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (4 * C' / e)
  set m := max m₀ R
  have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hσ_le : 1 / ((m : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hm_pos]
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hσC : 1 / ((m : ℝ) + 1) * C' ≤ e / 4 := by
    have hm₀m : (m₀ : ℝ) ≤ m := by exact_mod_cast le_max_left m₀ R
    have h4 : 4 * C' / e < (m : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ he] at h4
    rw [one_div_mul_eq_div, div_le_iff₀ hm_pos]
    linarith
  have hRm : Metric.ball (0 : Rn N) R ⊆ Metric.closedBall (0 : Rn N) m :=
    Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by exact_mod_cast le_max_right m₀ R))
  -- (c) The uniform Cauchy property of `v_{m,·}` on `B̄_m(0)` with `η := e / (2 (Lᴺ(B_R) + 1))`.
  set V := (volume (Metric.ball (0 : Rn N) R)).toReal with hV_def
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  set η := e / (2 * (V + 1)) with hη_def
  have hη : 0 < η := by positivity
  have hηV : η * V ≤ e / 2 := by
    rw [hη_def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨k₂, hk₂⟩ := hcauchy m η hη
  refine ⟨max k₁ k₂, fun k hk l hl ↦ ?_⟩
  -- Step 2 (mollification error): `∫⁻_{B_R} |v_{m,j} - 1_{F_j}| ≤ σ_m C' ≤ e / 4` for `j ≥ k₁`.
  have herr : ∀ j ≥ k₁, ∫⁻ y in Metric.ball (0 : Rn N) R,
      ENNReal.ofReal |(∫ z in F j, ρ m (y - z)) - (F j).indicator (fun _ ↦ (1 : ℝ)) y| ≤
        ENNReal.ofReal (e / 4) := by
    intro j hj
    refine (Submission.indCompact_mollCauchy_l1_error N (F j) (ρ m) (1 / ((m : ℝ) + 1)) R C'
      (hF j) (hρc m) (hρs m) (hρ0 m) (hρ1 m) (hρsupp m) hC' fun h hh ↦ ?_).trans
        (ENNReal.ofReal_le_ofReal hσC)
    exact (hC j hj h (hh.trans hσ_le)).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg h)))
  -- Step 1: each `v_{m,j}` is continuous and `F_j` is null-measurable, so the error terms are
  -- a.e.-measurable and `∫⁻` is additive on them.
  have hmeas : ∀ j, AEMeasurable (fun y ↦
      ENNReal.ofReal |(∫ z in F j, ρ m (y - z)) - (F j).indicator (fun _ ↦ (1 : ℝ)) y|)
      (volume.restrict (Metric.ball (0 : Rn N) R)) := by
    intro j
    have hv : AEMeasurable (fun y : Rn N ↦ ∫ z in F j, ρ m (y - z)) volume :=
      (Submission.indCompact_mollCauchy_setIntegral_continuous N (F j) (ρ m) (hρc m)
        (hρs m)).measurable.aemeasurable
    have hχ : AEMeasurable ((F j).indicator (fun _ ↦ (1 : ℝ))) volume :=
      aemeasurable_const.indicator₀ (hF j)
    exact (continuous_abs.measurable.comp_aemeasurable (hv.sub hχ)).ennreal_ofReal.restrict
  -- (d) For `y ∈ B_R ⊆ B̄_m(0)`:
  -- `1_{F_k Δ F_l}(y) ≤ |v_{m,k}(y) - 1_{F_k}(y)| + η + |v_{m,l}(y) - 1_{F_l}(y)|`.
  have hpt : ∀ y ∈ Metric.ball (0 : Rn N) R, (symmDiff (F k) (F l)).indicator 1 y ≤
      ENNReal.ofReal |(∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y| +
        ENNReal.ofReal η +
          ENNReal.ofReal |(∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y| := by
    intro y hy
    have hvkl := hk₂ k (le_of_max_le_right hk) l (le_of_max_le_right hl) y (hRm hy)
    refine Set.indicator_apply_le' (fun hyD ↦ ?_) (fun _ ↦ zero_le)
    have h1 : |(F k).indicator (fun _ ↦ (1 : ℝ)) y - (F l).indicator (fun _ ↦ (1 : ℝ)) y| = 1 := by
      rcases Set.mem_symmDiff.mp hyD with ⟨hk', hl'⟩ | ⟨hl', hk'⟩ <;> simp [hk', hl']
    have h2 : |(F k).indicator (fun _ ↦ (1 : ℝ)) y - (F l).indicator (fun _ ↦ (1 : ℝ)) y| ≤
        |(∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y| + η +
          |(∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y| := by
      rw [abs_le] at hvkl ⊢
      constructor <;>
        linarith [le_abs_self ((∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y),
          neg_abs_le ((∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y),
          le_abs_self ((∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y),
          neg_abs_le ((∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y)]
    rw [h1] at h2
    calc (1 : Rn N → ℝ≥0∞) y = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (|(∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y| + η +
            |(∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y|) :=
          ENNReal.ofReal_le_ofReal h2
      _ ≤ _ := ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
  -- (e) Integrate over `B_R`: `Lᴺ(B_R ∩ (F_k Δ F_l)) ≤ e / 4 + η Lᴺ(B_R) + e / 4 ≤ e`.
  have hconst : ∫⁻ _ in Metric.ball (0 : Rn N) R, ENNReal.ofReal η ≤ ENNReal.ofReal (e / 2) := by
    rw [setLIntegral_const, ← ENNReal.ofReal_toReal (measure_ball_lt_top (μ := volume)).ne,
      ← hV_def, ← ENNReal.ofReal_mul hη.le]
    exact ENNReal.ofReal_le_ofReal hηV
  calc volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) (F l))
      = ∫⁻ y in Metric.ball (0 : Rn N) R, (symmDiff (F k) (F l)).indicator 1 y := by
        rw [lintegral_indicator_one₀
            (((hF k).symmDiff (hF l)).mono_ac Measure.absolutelyContinuous_restrict),
          Measure.restrict_apply' measurableSet_ball, Set.inter_comm]
    _ ≤ ∫⁻ y in Metric.ball (0 : Rn N) R,
          (ENNReal.ofReal |(∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y| +
            ENNReal.ofReal η +
              ENNReal.ofReal |(∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y|) :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = (∫⁻ y in Metric.ball (0 : Rn N) R,
          ENNReal.ofReal |(∫ z in F k, ρ m (y - z)) - (F k).indicator (fun _ ↦ (1 : ℝ)) y|) +
        (∫⁻ _ in Metric.ball (0 : Rn N) R, ENNReal.ofReal η) +
          ∫⁻ y in Metric.ball (0 : Rn N) R,
            ENNReal.ofReal |(∫ z in F l, ρ m (y - z)) - (F l).indicator (fun _ ↦ (1 : ℝ)) y| := by
        rw [lintegral_add_right' _ (hmeas l), lintegral_add_right' _ aemeasurable_const]
    _ ≤ ENNReal.ofReal (e / 4) + ENNReal.ofReal (e / 2) + ENNReal.ofReal (e / 4) :=
        add_le_add (add_le_add (herr k (le_of_max_le_left hk)) hconst)
          (herr l (le_of_max_le_left hl))
    _ = ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), hεe]
        congr 1
        ring
/-- **Diagonal Arzelà–Ascoli extraction for mollified sets** (Steps 4–5 of the mollification
proof of Simon Ch. 2, Thm. 2.6, with arbitrary continuous compactly supported kernels `ρₘ`): for
arbitrary sets `Fₖ ⊆ ℝᴺ` some subsequence `φ` makes every `y ↦ ∫_{F_{φ(k)}} ρₘ(y - z) dz`
uniformly Cauchy on `B̄ₘ(0)`. Only `Lᴺ ⌞ S ≤ Lᴺ` is used, so these functions are bounded by
`Mₘ Lᴺ(B̄_{Rₘ}(0))` and equicontinuous uniformly in `S`. Tychonoff in the countable product
`∏_{(m, d) ∈ ℕ × D}` (`D` countable dense) gives `φ` with convergence at every `(m, d)`;
equicontinuity and a finite cover of `B̄ₘ(0)` by balls centred in `D` upgrade this to the uniform
Cauchy property. -/
theorem Submission.indCompact_diagonal_mollified_uniform_cauchy : ∀ (N : ℕ) (ρ : ℕ → Rn N → ℝ)
    (F : ℕ → Set (Rn N)), (∀ m, Continuous (ρ m)) → (∀ m, HasCompactSupport (ρ m)) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ (m : ℕ) (ε : ℝ), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ l ≥ k₀,
      ∀ y ∈ Metric.closedBall (0 : Rn N) m,
        |(∫ z in F (φ k), ρ m (y - z)) - ∫ z in F (φ l), ρ m (y - z)| ≤ ε := by
  intro N ρ F hc hs
  -- A function bounded by `C` and vanishing off `B̄_r(c)` has `|∫_S f| ≤ C Lᴺ(B̄_r(0))` for every
  -- set `S`, since `Lᴺ ⌞ S ≤ Lᴺ`.
  have key : ∀ (S : Set (Rn N)) (c : Rn N) (r C : ℝ) (f : Rn N → ℝ), (∀ z, ‖f z‖ ≤ C) →
      (∀ z, f z ≠ 0 → z ∈ Metric.closedBall c r) →
      |∫ z in S, f z| ≤ C * (volume (Metric.closedBall (0 : Rn N) r)).toReal := by
    intro S c r C f hfC hfs
    have hC : 0 ≤ C := (norm_nonneg _).trans (hfC 0)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (f := f) (s := Metric.closedBall c r)
      (μ := volume.restrict S) (fun z hz => not_not.1 (mt (hfs z) hz)), ← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le_const
      ((Measure.restrict_apply_le _ _).trans_lt measure_closedBall_lt_top)
      (fun z _ => hfC z)).trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [Measure.real, ← Measure.addHaar_closedBall_center volume c r]
    exact ENNReal.toReal_mono measure_closedBall_lt_top.ne (Measure.restrict_apply_le _ _)
  -- Support radius `Rₘ` and sup bound `Mₘ` of each kernel.
  have hR : ∀ m, ∃ R : ℝ, ∀ x, ρ m x ≠ 0 → ‖x‖ ≤ R := by
    intro m
    obtain ⟨R, hR⟩ := (hs m).isCompact.isBounded.subset_closedBall 0
    exact ⟨R, fun x hx => by simpa using hR (subset_tsupport _ hx)⟩
  choose R hR using hR
  choose M hM using fun m => (hc m).bounded_above_of_compact_support (hs m)
  -- Uniform bound: `|∫_S ρₘ(y - z) dz| ≤ Mₘ Lᴺ(B̄_{Rₘ}(0))`.
  have hbd : ∀ (m : ℕ) (S : Set (Rn N)) (y : Rn N),
      |∫ z in S, ρ m (y - z)| ≤ M m * (volume (Metric.closedBall (0 : Rn N) (R m))).toReal := by
    intro m S y
    refine key S y (R m) (M m) (fun z => ρ m (y - z)) (fun z => hM m _) (fun z hz => ?_)
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
    exact hR m _ hz
  have hint : ∀ (m : ℕ) (y : Rn N) (S : Set (Rn N)),
      Integrable (fun z => ρ m (y - z)) (volume.restrict S) := fun m y S =>
    (((hc m).integrable_of_hasCompactSupport (hs m)).comp_sub_left y).restrict
  -- Equicontinuity, uniformly in the set `S`.
  have heq : ∀ (m : ℕ) (η : ℝ), 0 < η → ∃ δ > 0, ∀ (S : Set (Rn N)) (y y' : Rn N), dist y y' < δ →
      |(∫ z in S, ρ m (y - z)) - ∫ z in S, ρ m (y' - z)| ≤ η := by
    intro m η hη
    obtain ⟨V, hV0, hV⟩ : ∃ V, 0 ≤ V ∧
        (volume (Metric.closedBall (0 : Rn N) (R m + 1))).toReal = V :=
      ⟨_, ENNReal.toReal_nonneg, rfl⟩
    have hV1 : 0 < V + 1 := by linarith
    obtain ⟨δ, hδ, hδρ⟩ := Metric.uniformContinuous_iff.1
      ((hs m).uniformContinuous_of_continuous (hc m)) (η / (V + 1)) (div_pos hη hV1)
    refine ⟨min δ 1, lt_min hδ one_pos, fun S y y' hyy' => ?_⟩
    rw [← integral_sub (hint m y S) (hint m y' S)]
    refine (key S y (R m + 1) (η / (V + 1)) (fun z => ρ m (y - z) - ρ m (y' - z)) (fun z => ?_)
      (fun z hz => ?_)).trans ?_
    · show ‖ρ m (y - z) - ρ m (y' - z)‖ ≤ _
      rw [← dist_eq_norm]
      have hd : dist (y - z) (y' - z) < δ := by
        rw [dist_sub_right]; exact hyy'.trans_le (min_le_left _ _)
      exact (hδρ hd).le
    · have hz' : ρ m (y - z) - ρ m (y' - z) ≠ 0 := hz
      rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
      by_cases h : ρ m (y - z) = 0
      · have h' : ρ m (y' - z) ≠ 0 := fun h' => hz' (by rw [h, h', sub_self])
        have h'' := hR m _ h'
        have hyy1 : ‖y - y'‖ < 1 := by
          rw [← dist_eq_norm]; exact hyy'.trans_le (min_le_right _ _)
        calc ‖y - z‖ = ‖(y - y') + (y' - z)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖y - y'‖ + ‖y' - z‖ := norm_add_le _ _
          _ ≤ R m + 1 := by linarith
      · linarith [hR m _ h]
    · rw [hV]
      calc η / (V + 1) * V ≤ η / (V + 1) * (V + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (div_pos hη hV1).le
        _ = η := div_mul_cancel₀ _ hV1.ne'
  -- Tychonoff on the countable product indexed by `ℕ × D`, `D` countable dense.
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Rn N)
  have : Countable D := hDc.to_subtype
  have hK : IsCompact (Set.pi univ fun p : ℕ × D =>
      Icc (-(M p.1 * (volume (Metric.closedBall (0 : Rn N) (R p.1))).toReal))
        (M p.1 * (volume (Metric.closedBall (0 : Rn N) (R p.1))).toReal)) :=
    isCompact_univ_pi fun p => isCompact_Icc
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq
    (x := fun k (p : ℕ × D) => ∫ z in F k, ρ p.1 ((p.2 : Rn N) - z))
    fun k => Set.mem_univ_pi.2 fun p => abs_le.1 (hbd p.1 (F k) p.2)
  refine ⟨φ, hφ, fun m ε hε => ?_⟩
  obtain ⟨δ, hδ, hδV⟩ := heq m (ε / 3) (by positivity)
  -- Finitely many `δ`-balls centred in `D` cover `B̄ₘ(0)`.
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : Rn N) (m : ℝ)).elim_finite_subcover
    (fun d : D => Metric.ball (d : Rn N) δ) (fun _ => Metric.isOpen_ball) fun y _ => by
      obtain ⟨d, hd, hyd⟩ := hDd.exists_dist_lt y hδ
      exact mem_iUnion.2 ⟨⟨d, hd⟩, hyd⟩
  have hev : ∀ᶠ k in atTop, ∀ d ∈ t,
      dist (∫ z in F (φ k), ρ m ((d : Rn N) - z)) (a (m, d)) < ε / 6 :=
    (eventually_all_finset t).2 fun d _ =>
      Metric.tendsto_nhds.1 (tendsto_pi_nhds.1 hlim (m, d)) (ε / 6) (by positivity)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hev
  refine ⟨k₀, fun k hk l hl y hy => ?_⟩
  obtain ⟨d, hdt, hyd⟩ := mem_iUnion₂.1 (ht hy)
  have h1 := hδV (F (φ k)) y d hyd
  have h2 := hδV (F (φ l)) y d hyd
  have h3 := hk₀ k hk d hdt
  have h4 := hk₀ l hl d hdt
  rw [Real.dist_eq] at h3 h4
  rw [abs_le] at h1 h2 ⊢
  rw [abs_lt] at h3 h4
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
/-- **Local `L¹` Cauchy sequences of sets have a local limit**: the completeness step of the
compactness theorem (Simon Ch. 2, Thm. 2.6) for characteristic functions, as used in the proof of
Ch. 3, Thm. 4.3. If for every `R ∈ ℕ` the sets `F k` are Cauchy in measure on `B_R(0)`, i.e.
`|B_R(0) ∩ (F_k Δ F_l)| → 0` as `k, l → ∞`, then some measurable `G` has `|K ∩ (F_k Δ G)| → 0`
for every compact `K`. Riesz–Fischer argument: choose `n_j ≥ k₀(j)` monotone, where
`|B_j ∩ (F_k Δ F_l)| ≤ 2⁻ʲ` for `k, l ≥ k₀(j)`, and put `G₀ = ⋃ᵢ ⋂_{j ≥ i} F_{n_j}`. Then
`F_{n_i} Δ G₀ ⊆ ⋃_{j ≥ i} (F_{n_j} Δ F_{n_{j+1}})`, so `|B_R ∩ (F_{n_i} Δ G₀)| ≤ 2 · 2⁻ⁱ` for
`i ≥ R`, and by the triangle inequality for `Δ`, `|B_R ∩ (F_k Δ G₀)| ≤ 3 · 2⁻ⁱ` for `k ≥ n_i`.
These estimates only use outer measure; `G` is a measurable hull of the null-measurable set `G₀`,
and every compact `K` lies in some `B_R`. -/
theorem Submission.indCompact_limit_of_local_cauchy : ∀ (N : ℕ) (F : ℕ → Set (Rn N)),
    (∀ k, NullMeasurableSet (F k) volume) →
    (∀ (R : ℕ) (ε : ℝ≥0∞), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ l ≥ k₀,
      volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) (F l)) ≤ ε) →
    ∃ G : Set (Rn N), MeasurableSet G ∧ ∀ K : Set (Rn N), IsCompact K →
      Tendsto (fun k ↦ volume (K ∩ symmDiff (F k) G)) atTop (𝓝 0) := by
  intro N F hF hC
  -- Fast subsequence: `k₀ j` is a Cauchy index for `R = j`, `ε = 2⁻ʲ`; `n` is monotone, `n ≥ k₀`.
  choose k₀ hk₀ using fun j : ℕ ↦ hC j ((2 : ℝ≥0∞)⁻¹ ^ j) (ENNReal.pow_pos (by simp) j)
  obtain ⟨n, hn_ge, hn_mono⟩ : ∃ n : ℕ → ℕ, (∀ j, k₀ j ≤ n j) ∧ Monotone n :=
    ⟨fun j ↦ (Finset.range (j + 1)).sup k₀, fun j ↦ Finset.le_sup (Finset.self_mem_range_succ j),
      fun i j hij ↦ Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ hij))⟩
  have hstep : ∀ j : ℕ, volume (Metric.ball (0 : Rn N) j ∩ symmDiff (F (n j)) (F (n (j + 1)))) ≤
      (2 : ℝ≥0∞)⁻¹ ^ j := fun j ↦
    hk₀ j _ (hn_ge j) _ ((hn_ge j).trans (hn_mono (Nat.le_succ j)))
  -- The limit set `G₀ = ⋃ᵢ ⋂_{j ≥ i} F (n j)`.
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : Set (Rn N), G₀ = ⋃ i, ⋂ j ≥ i, F (n j) := ⟨_, rfl⟩
  have hmem : ∀ y, y ∈ G₀ ↔ ∃ i, ∀ j ≥ i, y ∈ F (n j) := fun y ↦ by
    simp only [hG₀, mem_iUnion, mem_iInter]
  -- Tail inclusion: `F (n i) Δ G₀ ⊆ ⋃_{j ≥ i} (F (n j) Δ F (n (j + 1)))`.
  have htail : ∀ i, symmDiff (F (n i)) G₀ ⊆
      ⋃ m : ℕ, symmDiff (F (n (i + m))) (F (n (i + m + 1))) := by
    intro i y hy
    by_contra hcon
    simp only [mem_iUnion, not_exists] at hcon
    have hiff : ∀ m, (y ∈ F (n (i + m)) ↔ y ∈ F (n i)) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have h := hcon m
        rw [mem_symmDiff] at h
        rw [← ih, ← add_assoc]
        tauto
    rw [mem_symmDiff, hmem] at hy
    rcases hy with ⟨hyA, hyG⟩ | ⟨⟨i', hi'⟩, hyA⟩
    · refine hyG ⟨i, fun j hj ↦ ?_⟩
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
      exact (hiff m).2 hyA
    · exact hyA ((hiff i').1 (hi' (i + i') (Nat.le_add_left i' i)))
  -- Along the subsequence: `|B_R ∩ (F (n i) Δ G₀)| ≤ 2⁻ⁱ · 2` for `R ≤ i`.
  have hsub : ∀ R i : ℕ, R ≤ i →
      volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F (n i)) G₀) ≤ (2 : ℝ≥0∞)⁻¹ ^ i * 2 := by
    intro R i hRi
    calc volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F (n i)) G₀)
        ≤ volume (⋃ m : ℕ, Metric.ball (0 : Rn N) ↑(i + m) ∩
            symmDiff (F (n (i + m))) (F (n (i + m + 1)))) := by
          refine measure_mono fun y hy ↦ ?_
          obtain ⟨m, hm⟩ := mem_iUnion.1 (htail i hy.2)
          refine mem_iUnion.2 ⟨m, Metric.ball_subset_ball ?_ hy.1, hm⟩
          exact_mod_cast hRi.trans (Nat.le_add_right i m)
      _ ≤ ∑' m : ℕ, volume (Metric.ball (0 : Rn N) ↑(i + m) ∩
            symmDiff (F (n (i + m))) (F (n (i + m + 1)))) := measure_iUnion_le _
      _ ≤ ∑' m : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (i + m) := ENNReal.tsum_le_tsum fun m ↦ hstep (i + m)
      _ = (2 : ℝ≥0∞)⁻¹ ^ i * 2 := by
          simp_rw [pow_add]
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  -- Whole sequence: `|B_R ∩ (F k Δ G₀)| ≤ 2⁻ⁱ + 2⁻ⁱ · 2` for `R ≤ i` and `k ≥ n i`.
  have hwhole : ∀ R i k : ℕ, R ≤ i → n i ≤ k →
      volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) G₀) ≤
        (2 : ℝ≥0∞)⁻¹ ^ i + (2 : ℝ≥0∞)⁻¹ ^ i * 2 := by
    intro R i k hRi hk
    calc volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) G₀)
        ≤ volume ((Metric.ball (0 : Rn N) i ∩ symmDiff (F k) (F (n i))) ∪
            (Metric.ball (0 : Rn N) R ∩ symmDiff (F (n i)) G₀)) := by
          refine measure_mono fun y hy ↦ ?_
          rcases symmDiff_triangle (F k) (F (n i)) G₀ hy.2 with h | h
          · exact Or.inl ⟨Metric.ball_subset_ball (by exact_mod_cast hRi) hy.1, h⟩
          · exact Or.inr ⟨hy.1, h⟩
      _ ≤ volume (Metric.ball (0 : Rn N) i ∩ symmDiff (F k) (F (n i))) +
            volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F (n i)) G₀) := measure_union_le _ _
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ i + (2 : ℝ≥0∞)⁻¹ ^ i * 2 :=
          add_le_add (hk₀ i k ((hn_ge i).trans hk) (n i) (hn_ge i)) (hsub R i hRi)
  -- Hence `|B_R ∩ (F k Δ G₀)| → 0` for every `R ∈ ℕ`.
  have hgeom : Tendsto (fun i : ℕ ↦ (2 : ℝ≥0∞)⁻¹ ^ i + (2 : ℝ≥0∞)⁻¹ ^ i * 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun i : ℕ ↦ (2 : ℝ≥0∞)⁻¹ ^ i) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
    have h2 := h1.add (ENNReal.Tendsto.mul_const h1 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞)))
    rwa [zero_mul, add_zero] at h2
  have hball : ∀ R : ℕ,
      Tendsto (fun k ↦ volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) G₀)) atTop (𝓝 0) := by
    intro R
    refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
    obtain ⟨i, hiR, hiε⟩ :=
      ((eventually_ge_atTop R).and (ENNReal.tendsto_nhds_zero.1 hgeom ε hε)).exists
    exact (eventually_ge_atTop (n i)).mono fun k hk ↦ (hwhole R i k hiR hk).trans hiε
  -- `G = toMeasurable G₀` is measurable and a.e. equal to the null-measurable `G₀`; every compact
  -- `K` lies in some `B_R`.
  have hG₀m : NullMeasurableSet G₀ volume := by
    rw [hG₀]
    exact .iUnion fun i ↦ .iInter fun j ↦ .iInter fun _ ↦ hF (n j)
  refine ⟨toMeasurable volume G₀, measurableSet_toMeasurable _ _, fun K hK ↦ ?_⟩
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Rn N)
  obtain ⟨R, hR⟩ := exists_nat_gt r
  have hKR : K ⊆ Metric.ball (0 : Rn N) R := hr.trans (Metric.ball_subset_ball hR.le)
  have heq : ∀ k, volume (K ∩ symmDiff (F k) (toMeasurable volume G₀)) =
      volume (K ∩ symmDiff (F k) G₀) := fun k ↦
    measure_congr (EventuallyEqSet.rfl.inter (EventuallyEqSet.rfl.symmDiff hG₀m.toMeasurable_ae_eq))
  refine (tendsto_congr heq).2 ?_
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hball R)
    (fun k ↦ zero_le) (fun k ↦ measure_mono (inter_subset_inter_left _ hKR))

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
