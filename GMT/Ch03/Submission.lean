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

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
