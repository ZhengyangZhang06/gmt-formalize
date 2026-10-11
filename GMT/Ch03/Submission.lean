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

/-- **Good chart pieces** (Simon Ch. 3, Lemma 1.2, "if" part, `chapter-03.txt` lines 25–38, for
the embedded `C¹` submanifolds of Ch. 2, (4.1)). Let `U` be open, `M ⊆ U`, `f` locally Lipschitz
on `U`, and `M ⊆ N₀ ∪ ⋃ⱼ Sⱼ` with every `Sⱼ` an `n`-dimensional embedded `C¹` submanifold. Then
`M ⊆ N₀ ∪ ⋃_α ψ_α(D_α)` for countably many `C¹` maps `ψ_α` on open `V_α ⊆ ℝⁿ` with injective
differential and compact `D_α ⊆ V_α` on which `ψ_α` is bi-Lipschitz and `f ∘ ψ_α` is Lipschitz.
By Lindelöf, countably many charts cover each `Sⱼ`. At a parameter `u₀` with `ψ(u₀) ∈ U`, the
injectivity of `A = Dψ(u₀)`, the continuity of `Dψ` and the mean value inequality give a closed
ball on which `|ψ(u) - ψ(v) - A(u - v)| ≤ (m/2)|u - v|`, `m|w| ≤ |A w|`, so `ψ` is bi-Lipschitz
there; shrinking it, `ψ` maps it into a ball on which `f` is Lipschitz. By Lindelöf again,
countably many such balls cover `V ∩ ψ⁻¹(U)`, and all pieces are enumerated by `ℕ`. -/
theorem Submission.areaFormula_good_chart_pieces : ∀ (n N p : ℕ) (M U N₀ : Set (Rn N)) (S : ℕ → Set (Rn N)) (f : Rn N → Rn p), IsOpen U → M ⊆ U → LocallyLipschitzOn U f → (∀ j, IsC1Submanifold n (S j)) → M ⊆ N₀ ∪ ⋃ j, S j → ∃ (V D : ℕ → Set (Rn n)) (ψ : ℕ → Rn n → Rn N) (K C : ℕ → ℝ≥0), (∀ α, IsOpen (V α) ∧ ContDiffOn ℝ 1 (ψ α) (V α) ∧ (∀ u ∈ V α, Function.Injective (fderiv ℝ (ψ α) u)) ∧ IsCompact (D α) ∧ D α ⊆ V α ∧ LipschitzOnWith (K α) (ψ α) (D α) ∧ (∀ u ∈ D α, ∀ v ∈ D α, dist u v ≤ (C α : ℝ) * dist (ψ α u) (ψ α v)) ∧ LipschitzOnWith (K α) (f ∘ ψ α) (D α)) ∧ M ⊆ N₀ ∪ ⋃ α, ψ α '' D α := by
  intro n N p M U N₀ S f hU hMU hf hS hcov
  classical
  -- Step 2: a good closed ball around a chart parameter `u₀` with `ψ(u₀) ∈ U`.
  have goodBall : ∀ (V : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 1 ψ V →
      (∀ u ∈ V, Function.Injective (fderiv ℝ ψ u)) → ∀ u₀ ∈ V, ψ u₀ ∈ U →
      ∃ r > 0, Metric.closedBall u₀ r ⊆ V ∧ ∃ K C : ℝ≥0,
        LipschitzOnWith K ψ (Metric.closedBall u₀ r) ∧
        (∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
          dist u v ≤ (C : ℝ) * dist (ψ u) (ψ v)) ∧
        LipschitzOnWith K (f ∘ ψ) (Metric.closedBall u₀ r) := by
    intro V ψ hV hψC hInj u₀ hu₀ hx₀
    -- (a) `A = Dψ(u₀)` is injective, so `m ‖w‖ ≤ ‖A w‖` with `m = K_A⁻¹ > 0`.
    set A := fderiv ℝ ψ u₀ with hA
    obtain ⟨KA, hKA0, hKA⟩ := LinearMap.exists_antilipschitzWith A.toLinearMap
      (LinearMap.ker_eq_bot.mpr (hInj u₀ hu₀))
    have hKA0' : (0 : ℝ) < KA := by exact_mod_cast hKA0
    set m : ℝ := (KA : ℝ)⁻¹ with hm
    have hm0 : 0 < m := inv_pos.mpr hKA0'
    have hAlow : ∀ w : Rn n, m * ‖w‖ ≤ ‖A w‖ := by
      intro w
      have h1 : dist w 0 ≤ KA * dist (A.toLinearMap w) (A.toLinearMap 0) := hKA.le_mul_dist w 0
      rw [map_zero, dist_zero_right, dist_zero_right] at h1
      have h2 : ‖w‖ ≤ KA * ‖A w‖ := h1
      rw [hm, inv_mul_le_iff₀ hKA0']
      exact h2
    -- (b), (c) radii: `‖Dψ(z) - A‖ < m/2`, the ball lies in `V`, and `ψ` maps it into a ball
    -- `B_s(ψ(u₀)) ⊆ t` on which `f` is `L_f`-Lipschitz.
    have hcont : ContinuousOn (fun z ↦ fderiv ℝ ψ z) V :=
      hψC.continuousOn_fderiv_of_isOpen hV le_rfl
    have hcontAt : ContinuousAt (fun z ↦ fderiv ℝ ψ z) u₀ := hcont.continuousAt (hV.mem_nhds hu₀)
    obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.mp hcontAt (m / 2) (half_pos hm0)
    obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.isOpen_iff.mp hV u₀ hu₀
    obtain ⟨Lf, t, ht, hLf⟩ := hf hx₀
    rw [hU.nhdsWithin_eq hx₀] at ht
    obtain ⟨s, hs, hst⟩ := Metric.mem_nhds_iff.mp ht
    have hψcontAt : ContinuousAt ψ u₀ := hψC.continuousOn.continuousAt (hV.mem_nhds hu₀)
    obtain ⟨δ₃, hδ₃, hδ₃'⟩ := Metric.continuousAt_iff.mp hψcontAt s hs
    set r := min (min δ₁ δ₂) δ₃ / 2 with hr
    have hmin0 : 0 < min (min δ₁ δ₂) δ₃ := lt_min (lt_min hδ₁ hδ₂) hδ₃
    have hr0 : 0 < r := by rw [hr]; linarith
    have hrmin : r < min (min δ₁ δ₂) δ₃ := by rw [hr]; linarith
    have hrlt : ∀ u ∈ Metric.closedBall u₀ r,
        dist u u₀ < δ₁ ∧ dist u u₀ < δ₂ ∧ dist u u₀ < δ₃ := by
      intro u hu
      have hu' : dist u u₀ < min (min δ₁ δ₂) δ₃ :=
        lt_of_le_of_lt (Metric.mem_closedBall.mp hu) hrmin
      simp only [lt_min_iff] at hu'
      exact ⟨hu'.1.1, hu'.1.2, hu'.2⟩
    have hBV : Metric.closedBall u₀ r ⊆ V := fun u hu ↦ hδ₂' (Metric.mem_ball.mpr (hrlt u hu).2.1)
    have hdiffB : ∀ z ∈ Metric.closedBall u₀ r, DifferentiableAt ℝ ψ z := fun z hz ↦
      ((hψC.differentiableOn one_ne_zero) z (hBV hz)).differentiableAt (hV.mem_nhds (hBV hz))
    -- Mean value inequality for `z ↦ ψ z - A z` on the convex ball.
    have hMV : ∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
        ‖(ψ u - A u) - (ψ v - A v)‖ ≤ m / 2 * ‖u - v‖ := by
      intro u hu v hv
      have hg : ∀ z ∈ Metric.closedBall u₀ r, DifferentiableAt ℝ (fun z ↦ ψ z - A z) z :=
        fun z hz ↦ (hdiffB z hz).sub A.differentiableAt
      have hbound : ∀ z ∈ Metric.closedBall u₀ r, ‖fderiv ℝ (fun z ↦ ψ z - A z) z‖ ≤ m / 2 := by
        intro z hz
        rw [fderiv_fun_sub (hdiffB z hz) A.differentiableAt, A.fderiv, ← dist_eq_norm]
        exact (hδ₁' (hrlt z hz).1).le
      exact Convex.norm_image_sub_le_of_norm_fderiv_le hg hbound (convex_closedBall u₀ r) hv hu
    have hupper : ∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
        dist (ψ u) (ψ v) ≤ (‖A‖ + m / 2) * dist u v := by
      intro u hu v hv
      rw [dist_eq_norm, dist_eq_norm]
      have h1 := hMV u hu v hv
      have h2 : ‖A (u - v)‖ ≤ ‖A‖ * ‖u - v‖ := A.le_opNorm _
      have h3 : ψ u - ψ v = ((ψ u - A u) - (ψ v - A v)) + A (u - v) := by rw [map_sub]; abel
      calc ‖ψ u - ψ v‖ = ‖((ψ u - A u) - (ψ v - A v)) + A (u - v)‖ := by rw [← h3]
        _ ≤ ‖(ψ u - A u) - (ψ v - A v)‖ + ‖A (u - v)‖ := norm_add_le _ _
        _ ≤ m / 2 * ‖u - v‖ + ‖A‖ * ‖u - v‖ := add_le_add h1 h2
        _ = (‖A‖ + m / 2) * ‖u - v‖ := by ring
    have hlower : ∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
        dist u v ≤ ((2 * KA : ℝ≥0) : ℝ) * dist (ψ u) (ψ v) := by
      intro u hu v hv
      rw [dist_eq_norm, dist_eq_norm]
      have h1 := hMV u hu v hv
      have h2 := hAlow (u - v)
      have h3 : A (u - v) = (ψ u - ψ v) - ((ψ u - A u) - (ψ v - A v)) := by rw [map_sub]; abel
      have h4 : ‖A (u - v)‖ ≤ ‖ψ u - ψ v‖ + m / 2 * ‖u - v‖ := by
        rw [h3]; exact (norm_sub_le _ _).trans (add_le_add le_rfl h1)
      have h5 : m / 2 * ‖u - v‖ ≤ ‖ψ u - ψ v‖ := by linarith
      have hKAeq : (KA : ℝ) * m = 1 := by rw [hm]; exact mul_inv_cancel₀ hKA0'.ne'
      push_cast
      calc ‖u - v‖ = (2 * KA) * (m / 2 * ‖u - v‖) := by
            have : (2 * (KA : ℝ)) * (m / 2 * ‖u - v‖) = ((KA : ℝ) * m) * ‖u - v‖ := by ring
            rw [this, hKAeq, one_mul]
        _ ≤ (2 * KA) * ‖ψ u - ψ v‖ := mul_le_mul_of_nonneg_left h5 (by positivity)
    -- (d) `K = (‖A‖ + m/2) + L_f (‖A‖ + m/2)` and `C = 2 K_A`.
    set K0 : ℝ≥0 := ⟨‖A‖ + m / 2, by positivity⟩ with hK0
    have hK0r : (K0 : ℝ) = ‖A‖ + m / 2 := rfl
    refine ⟨r, hr0, hBV, K0 + Lf * K0, 2 * KA, ?_, hlower, ?_⟩
    · refine LipschitzOnWith.of_dist_le_mul fun u hu v hv ↦ ?_
      calc dist (ψ u) (ψ v) ≤ (‖A‖ + m / 2) * dist u v := hupper u hu v hv
        _ ≤ ((K0 + Lf * K0 : ℝ≥0) : ℝ) * dist u v := by
          push_cast
          rw [hK0r]
          have h0 : 0 ≤ (Lf : ℝ) * (‖A‖ + m / 2) := by positivity
          exact mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    · refine LipschitzOnWith.of_dist_le_mul fun u hu v hv ↦ ?_
      have hψu : ψ u ∈ t := hst (Metric.mem_ball.mpr (hδ₃' (hrlt u hu).2.2))
      have hψv : ψ v ∈ t := hst (Metric.mem_ball.mpr (hδ₃' (hrlt v hv).2.2))
      calc dist (f (ψ u)) (f (ψ v)) ≤ Lf * dist (ψ u) (ψ v) := hLf.dist_le_mul _ hψu _ hψv
        _ ≤ Lf * ((‖A‖ + m / 2) * dist u v) := by gcongr; exact hupper u hu v hv
        _ ≤ ((K0 + Lf * K0 : ℝ≥0) : ℝ) * dist u v := by
          push_cast
          rw [hK0r]
          have h0 : 0 ≤ (‖A‖ + m / 2) * dist u v := by positivity
          have h1 : (‖A‖ + m / 2 + ↑Lf * (‖A‖ + m / 2)) * dist u v =
              (‖A‖ + m / 2) * dist u v + ↑Lf * ((‖A‖ + m / 2) * dist u v) := by ring
          rw [h1]
          linarith
  -- Step 1: by Lindelöf, countably many charts `ψ_{j,y}`, `y ∈ T j`, cover each `S j`.
  choose! Vc Wc ψc hVc hWc hyW hψC hInjOn hImg hProper hDer using hS
  choose T hTS hTc hTU using fun j ↦
    TopologicalSpace.isOpen_biUnion_countable (S j) (Wc j) (fun y hy ↦ hWc j y hy)
  -- Step 3: by Lindelöf in `ℝⁿ`, countably many good balls cover `V_{j,y} ∩ ψ_{j,y}⁻¹(U)`.
  have hgood : ∀ j, ∀ y ∈ S j, ∀ u₀ ∈ Vc j y ∩ ψc j y ⁻¹' U, ∃ r > 0,
      Metric.closedBall u₀ r ⊆ Vc j y ∧ ∃ K C : ℝ≥0,
        LipschitzOnWith K (ψc j y) (Metric.closedBall u₀ r) ∧
        (∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
          dist u v ≤ (C : ℝ) * dist (ψc j y u) (ψc j y v)) ∧
        LipschitzOnWith K (f ∘ ψc j y) (Metric.closedBall u₀ r) := fun j y hy u₀ hu₀ ↦
    goodBall (Vc j y) (ψc j y) (hVc j y hy) (hψC j y hy) (hDer j y hy) u₀ hu₀.1 hu₀.2
  choose! r hr hrV Kb Cb hKb hCb hfKb using hgood
  choose Q hQO hQc hQU using fun j y ↦
    TopologicalSpace.isOpen_biUnion_countable (Vc j y ∩ ψc j y ⁻¹' U)
      (fun u₀ ↦ Metric.ball u₀ (r j y u₀)) (fun _ _ ↦ Metric.isOpen_ball)
  -- Step 4: the countable index set of pieces `(j, y, u₀)`.
  set I : Set (ℕ × Rn N × Rn n) := ⋃ j, ⋃ y ∈ T j, (fun u ↦ (j, y, u)) '' Q j y with hIdef
  have hIc : I.Countable :=
    Set.countable_iUnion fun j ↦ (hTc j).biUnion fun y _ ↦ (hQc j y).image _
  have hImem : ∀ π ∈ I, π.2.1 ∈ T π.1 ∧ π.2.2 ∈ Q π.1 π.2.1 := by
    intro π hπ
    simp only [hIdef, mem_iUnion, mem_image] at hπ
    obtain ⟨j, y, hy, u, hu, rfl⟩ := hπ
    exact ⟨hy, hu⟩
  -- Step 5: the per-piece properties.
  have hpiece : ∀ π ∈ I, IsOpen (Vc π.1 π.2.1) ∧ ContDiffOn ℝ 1 (ψc π.1 π.2.1) (Vc π.1 π.2.1) ∧
      (∀ u ∈ Vc π.1 π.2.1, Function.Injective (fderiv ℝ (ψc π.1 π.2.1) u)) ∧
      IsCompact (Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2)) ∧
      Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2) ⊆ Vc π.1 π.2.1 ∧
      LipschitzOnWith (Kb π.1 π.2.1 π.2.2) (ψc π.1 π.2.1)
        (Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2)) ∧
      (∀ u ∈ Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2),
        ∀ v ∈ Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2),
          dist u v ≤ (Cb π.1 π.2.1 π.2.2 : ℝ) * dist (ψc π.1 π.2.1 u) (ψc π.1 π.2.1 v)) ∧
      LipschitzOnWith (Kb π.1 π.2.1 π.2.2) (f ∘ ψc π.1 π.2.1)
        (Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2)) := by
    intro π hπ
    obtain ⟨hyT, huQ⟩ := hImem π hπ
    have hy : π.2.1 ∈ S π.1 := hTS π.1 hyT
    have hu : π.2.2 ∈ Vc π.1 π.2.1 ∩ ψc π.1 π.2.1 ⁻¹' U := hQO π.1 π.2.1 huQ
    exact ⟨hVc _ _ hy, hψC _ _ hy, hDer _ _ hy, isCompact_closedBall _ _, hrV _ _ hy _ hu,
      hKb _ _ hy _ hu, hCb _ _ hy _ hu, hfKb _ _ hy _ hu⟩
  -- Step 6: every `x ∈ M \ N₀` is `ψ_{j,y}(u)` with `u` in one of the chosen balls.
  have hcovI : ∀ x ∈ M, x ∉ N₀ → ∃ π ∈ I,
      x ∈ ψc π.1 π.2.1 '' Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2) := by
    intro x hxM hxN
    rcases hcov hxM with hx0 | hx1
    · exact absurd hx0 hxN
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx1
    have hxW : x ∈ ⋃ y ∈ T j, Wc j y := by
      rw [hTU j]; exact mem_biUnion hxj (hyW j x hxj)
    obtain ⟨y, hyT, hxWy⟩ := mem_iUnion₂.mp hxW
    have hy : y ∈ S j := hTS j hyT
    have hxim : x ∈ ψc j y '' Vc j y := by rw [hImg j y hy]; exact ⟨hxWy, hxj⟩
    obtain ⟨u, huV, rfl⟩ := hxim
    have huO : u ∈ Vc j y ∩ ψc j y ⁻¹' U := ⟨huV, hMU hxM⟩
    have hu' : u ∈ ⋃ u₀ ∈ Q j y, Metric.ball u₀ (r j y u₀) := by
      rw [hQU j y]; exact mem_biUnion huO (Metric.mem_ball_self (hr j y hy u huO))
    obtain ⟨u₀, hu₀Q, huB⟩ := mem_iUnion₂.mp hu'
    refine ⟨(j, y, u₀), ?_, u, Metric.ball_subset_closedBall huB, rfl⟩
    simp only [hIdef, mem_iUnion, mem_image]
    exact ⟨j, y, hyT, u₀, hu₀Q, rfl⟩
  -- Step 4 (enumeration): a surjection `ℕ → I`, or empty pieces if `I = ∅`.
  by_cases hIne : I.Nonempty
  · obtain ⟨e, he⟩ := hIc.exists_eq_range hIne
    have heI : ∀ α, e α ∈ I := fun α ↦ by rw [he]; exact mem_range_self α
    refine ⟨fun α ↦ Vc (e α).1 (e α).2.1,
      fun α ↦ Metric.closedBall (e α).2.2 (r (e α).1 (e α).2.1 (e α).2.2),
      fun α ↦ ψc (e α).1 (e α).2.1, fun α ↦ Kb (e α).1 (e α).2.1 (e α).2.2,
      fun α ↦ Cb (e α).1 (e α).2.1 (e α).2.2, fun α ↦ hpiece (e α) (heI α), ?_⟩
    intro x hxM
    by_cases hxN : x ∈ N₀
    · exact Or.inl hxN
    · obtain ⟨π, hπI, hxπ⟩ := hcovI x hxM hxN
      rw [he] at hπI
      obtain ⟨α, rfl⟩ := hπI
      exact Or.inr (mem_iUnion.mpr ⟨α, hxπ⟩)
  · refine ⟨fun _ ↦ ∅, fun _ ↦ ∅, fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, fun α ↦ ?_, ?_⟩
    · simp
    · intro x hxM
      by_cases hxN : x ∈ N₀
      · exact Or.inl hxN
      · obtain ⟨π, hπI, -⟩ := hcovI x hxM hxN
        exact absurd ⟨π, hπI⟩ hIne

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
