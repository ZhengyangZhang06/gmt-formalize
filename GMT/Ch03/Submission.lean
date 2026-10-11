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

/-- **Simon Ch. 2, proof of Theorem 1.9, choice (1)** (`chapter-02.txt` lines 366–370), for
Mathlib's unnormalized Hausdorff measure: if `μH[d](s) < ∞`, then for every `r > 0` and `ε ≠ 0`
some countable cover `(tₙ)` of `s` by sets of diameter `≤ r` has `∑ₙ diam(tₙ)^d ≤ μH[d](s) + ε`
(empty `tₙ` cost `0`). By `hausdorffMeasure_apply` the infimum over such covers is at most
`μH[d](s) < μH[d](s) + ε`, so some cover lies strictly below that bound. -/
theorem Submission.hausdorffMeasure_exists_cover_tsum_le_add : ∀ {X : Type} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (d : ℝ) (s : Set X) (r ε : ℝ≥0∞), 0 < r → ε ≠ 0 →
    μH[d] s ≠ ∞ → ∃ t : ℕ → Set X, s ⊆ ⋃ n, t n ∧ (∀ n, Metric.ediam (t n) ≤ r) ∧
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d ≤ μH[d] s + ε := by
  intro X _ _ _ d s r ε hr hε hs
  -- The infimum over covers by sets of diameter `≤ r` is the `r`-term of the supremum.
  have hle : (⨅ (t : ℕ → Set X) (_ : s ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d) ≤ μH[d] s := by
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup₂_of_le r hr le_rfl
  have hlt := hle.trans_lt (ENNReal.lt_add_right hs hε)
  simp only [iInf_lt_iff] at hlt
  obtain ⟨t, hst, htr, hsum⟩ := hlt
  exact ⟨t, hst, htr, hsum.le⟩
/-- **Volume–diameter bound**, the step of Simon Ch. 2, proof of Theorem 1.9
(`chapter-02.txt` lines 401–406) where `Lᵐ(f(C_{ij})) ≤ ωₘ (diam f(C_{ij})/2)ᵐ` is taken from the
isodiametric inequality 2.10, with the cruder constant of a closed-ball inclusion:
`Lᵐ(closure S) ≤ ωₘ (diam S)ᵐ` for every `S ⊆ ℝᵐ`, where `ωₘ = Lᵐ(B₁(0))`. The cases `S = ∅`,
`m = 0` (`B₁(0) = ℝ⁰`, power `1`) and `diam S = ∞` (`ωₘ > 0`) are immediate. Otherwise
`closure S ⊆ B̄_{diam S}(s₀)` for any `s₀ ∈ S`, and `Lᵐ(B̄_D(s₀)) = Dᵐ ωₘ` by `addHaar_closedBall`. -/
theorem Submission.volume_closure_le_unitBall_mul_ediam_pow : ∀ (m : ℕ) (S : Set (Rn m)),
    volume (closure S) ≤ volume (Metric.ball (0 : Rn m) 1) * Metric.ediam S ^ m := by
  intro m S
  rcases S.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · simp
  by_cases hm : m = 0
  · -- `ℝ⁰` is a single point, so `B₁(0)` is the whole space and the power is `1`.
    subst hm
    have hball : Metric.ball (0 : Rn 0) 1 = univ := by
      ext x; simp [Subsingleton.elim x 0]
    rw [pow_zero, mul_one, hball]
    exact measure_mono (subset_univ _)
  have hω0 : volume (Metric.ball (0 : Rn m) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume (0 : Rn m) one_pos).ne'
  by_cases hD : Metric.ediam S = ∞
  · rw [hD, ENNReal.top_pow hm, ENNReal.mul_top hω0]
    exact le_top
  -- `S` is bounded and `closure S` has the same diameter, so it lies in `B̄_{diam S}(s₀)`.
  have hb : Bornology.IsBounded S := Metric.isBounded_iff_ediam_ne_top.2 hD
  have hsub : closure S ⊆ Metric.closedBall s₀ (Metric.diam S) := by
    intro x hx
    rw [Metric.mem_closedBall, ← Metric.diam_closure]
    exact Metric.dist_le_diam_of_mem hb.closure hx (subset_closure hs₀)
  calc volume (closure S) ≤ volume (Metric.closedBall s₀ (Metric.diam S)) := measure_mono hsub
    _ = ENNReal.ofReal (Metric.diam S ^ m) * volume (Metric.ball (0 : Rn m) 1) := by
        rw [Measure.addHaar_closedBall volume s₀ Metric.diam_nonneg, finrank_euclideanSpace_fin]
    _ = volume (Metric.ball (0 : Rn m) 1) * Metric.ediam S ^ m := by
        rw [mul_comm, ENNReal.ofReal_pow Metric.diam_nonneg, Metric.diam, ENNReal.ofReal_toReal hD]

/-- **Simon Ch. 2, Theorem 1.9 (pp. 45–46), Eilenberg's inequality when `H^{m+k}(A) < ∞`**
(`chapter-02.txt` lines 366–411), for Mathlib's unnormalized Hausdorff measures `μH[·]` and an
arbitrary `A ⊆ ℝᴺ`: an `L`-Lipschitz `f : ℝᴺ → ℝᵐ` has a Borel `g ≥ μH[k](A ∩ f⁻¹{y})` with
`∫ g dLᵐ ≤ ωₘ Lᵐ μH[m+k](A)`, `ωₘ = Lᵐ(B₁(0))`. As in (1)–(2), take covers `Cᵢⱼ` of `A` with
`diam Cᵢⱼ ≤ 1/i` and `∑ⱼ diam(Cᵢⱼ)^{m+k} ≤ μH[m+k](A) + 1/i`, and the Borel functions
`gᵢ = ∑ⱼ diam(Cᵢⱼ)ᵏ 1_{closure f(Cᵢⱼ)}`. The majorant is `g = liminf gᵢ`, so Fatou's lemma
replaces the upper integral of Remark 1.10, and `Lᵐ(closure S) ≤ ωₘ (diam S)ᵐ` replaces the
isodiametric inequality. -/
theorem Submission.eilenberg_hausdorff_upper_integral_of_ne_top :
    ∀ (N m k : ℕ) (A : Set (Rn N)) (f : Rn N → Rn m) (L : ℝ≥0), LipschitzWith L f →
      μH[((m + k : ℕ) : ℝ)] A ≠ ∞ → ∃ g : Rn m → ℝ≥0∞, Measurable g ∧
        (∀ y, μH[(k : ℝ)] (A ∩ f ⁻¹' {y}) ≤ g y) ∧
        ∫⁻ y, g y ≤ volume (Metric.ball (0 : Rn m) 1) * (L : ℝ≥0∞) ^ m *
          μH[((m + k : ℕ) : ℝ)] A := by
  intro N m k A f L hf hA
  set ω := volume (Metric.ball (0 : Rn m) 1)
  -- (1): covers `C i j` of `A` with `diam (C i j) ≤ 1/i` and cost `≤ μH[m+k](A) + 1/i`.
  choose C hCcov hCdiam hCsum using fun i : ℕ ↦
    Submission.hausdorffMeasure_exists_cover_tsum_le_add ((m + k : ℕ) : ℝ) A (i : ℝ≥0∞)⁻¹
      (i : ℝ≥0∞)⁻¹ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top i))
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top i)) hA
  set G : ℕ → Rn m → ℝ≥0∞ := fun i y ↦
    ∑' j, (closure (f '' C i j)).indicator (fun _ ↦ Metric.ediam (C i j) ^ (k : ℝ)) y with hG
  have hGj : ∀ i j, Measurable ((closure (f '' C i j)).indicator
      fun _ : Rn m ↦ Metric.ediam (C i j) ^ (k : ℝ)) := fun i j ↦
    measurable_const.indicator isClosed_closure.measurableSet
  have hGmeas : ∀ i, Measurable (G i) := fun i ↦ Measurable.tsum (hGj i)
  refine ⟨fun y ↦ liminf (fun i ↦ G i y) atTop, Measurable.liminf hGmeas, fun y ↦ ?_, ?_⟩
  · -- (2): the `C i j` with `y ∈ f '' C i j` cover `A ∩ f⁻¹{y}`, at a cost of at most `G i y`.
    have hcov : ∀ i, A ∩ f ⁻¹' {y} ⊆ ⋃ j : {j : ℕ // y ∈ f '' C i j}, C i j := fun i x hx ↦ by
      obtain ⟨j, hj⟩ := mem_iUnion.1 (hCcov i hx.1)
      exact mem_iUnion.2 ⟨⟨j, x, hj, hx.2⟩, hj⟩
    refine (Measure.hausdorffMeasure_le_liminf_tsum (ι := fun i : ℕ ↦ {j : ℕ // y ∈ f '' C i j})
      (k : ℝ) (A ∩ f ⁻¹' {y}) (l := atTop) (fun i : ℕ ↦ (i : ℝ≥0∞)⁻¹)
      ENNReal.tendsto_inv_nat_nhds_zero (fun i j ↦ C i j)
      (Eventually.of_forall fun i j ↦ hCdiam i j) (Eventually.of_forall hcov)).trans
      (liminf_le_liminf (Eventually.of_forall fun i ↦ ?_))
    calc ∑' j : {j : ℕ // y ∈ f '' C i j}, Metric.ediam (C i j.1) ^ (k : ℝ)
        = ∑' j, {j : ℕ | y ∈ f '' C i j}.indicator (fun j ↦ Metric.ediam (C i j) ^ (k : ℝ)) j :=
          tsum_subtype {j : ℕ | y ∈ f '' C i j} fun j ↦ Metric.ediam (C i j) ^ (k : ℝ)
      _ ≤ G i y := ENNReal.tsum_le_tsum fun j ↦ by
          by_cases hj : y ∈ f '' C i j
          · rw [Set.indicator_of_mem (show j ∈ {j : ℕ | y ∈ f '' C i j} from hj),
              Set.indicator_of_mem (subset_closure hj)]
          · rw [Set.indicator_of_notMem (show j ∉ {j : ℕ | y ∈ f '' C i j} from hj)]
            exact zero_le
  · -- `∫ G i ≤ ωₘ Lᵐ (μH[m+k](A) + 1/i)`, since `Lᵐ(closure f(C)) ≤ ωₘ (L diam C)ᵐ`.
    have hint : ∀ i : ℕ, ∫⁻ y, G i y ≤
        ω * (L : ℝ≥0∞) ^ m * (μH[((m + k : ℕ) : ℝ)] A + (i : ℝ≥0∞)⁻¹) := by
      intro i
      rw [hG]
      dsimp only
      rw [lintegral_tsum fun j ↦ (hGj i j).aemeasurable]
      calc ∑' j, ∫⁻ y, (closure (f '' C i j)).indicator
              (fun _ ↦ Metric.ediam (C i j) ^ (k : ℝ)) y
          = ∑' j, Metric.ediam (C i j) ^ (k : ℝ) * volume (closure (f '' C i j)) :=
            tsum_congr fun j ↦ lintegral_indicator_const isClosed_closure.measurableSet _
        _ ≤ ∑' j, ω * (L : ℝ≥0∞) ^ m *
              ⨆ _ : (C i j).Nonempty, Metric.ediam (C i j) ^ ((m + k : ℕ) : ℝ) :=
            ENNReal.tsum_le_tsum fun j ↦ by
              rcases (C i j).eq_empty_or_nonempty with h | h
              · simp [h]
              rw [iSup_pos h]
              calc Metric.ediam (C i j) ^ (k : ℝ) * volume (closure (f '' C i j))
                  ≤ Metric.ediam (C i j) ^ (k : ℝ) * (ω * Metric.ediam (f '' C i j) ^ m) := by
                    gcongr
                    exact Submission.volume_closure_le_unitBall_mul_ediam_pow m _
                _ ≤ Metric.ediam (C i j) ^ (k : ℝ) *
                      (ω * ((L : ℝ≥0∞) * Metric.ediam (C i j)) ^ m) := by
                    gcongr
                    exact hf.ediam_image_le _
                _ = ω * (L : ℝ≥0∞) ^ m * Metric.ediam (C i j) ^ ((m + k : ℕ) : ℝ) := by
                    rw [ENNReal.rpow_natCast, ENNReal.rpow_natCast, mul_pow, pow_add]
                    ring
        _ = ω * (L : ℝ≥0∞) ^ m *
              ∑' j, ⨆ _ : (C i j).Nonempty, Metric.ediam (C i j) ^ ((m + k : ℕ) : ℝ) :=
            ENNReal.tsum_mul_left
        _ ≤ ω * (L : ℝ≥0∞) ^ m * (μH[((m + k : ℕ) : ℝ)] A + (i : ℝ≥0∞)⁻¹) := by
            gcongr
            exact hCsum i
    -- Fatou's lemma, and `1/i → 0`.
    have hlim : Tendsto (fun i : ℕ ↦ ω * (L : ℝ≥0∞) ^ m *
        (μH[((m + k : ℕ) : ℝ)] A + (i : ℝ≥0∞)⁻¹)) atTop
        (𝓝 (ω * (L : ℝ≥0∞) ^ m * μH[((m + k : ℕ) : ℝ)] A)) := by
      have h : Tendsto (fun i : ℕ ↦ μH[((m + k : ℕ) : ℝ)] A + (i : ℝ≥0∞)⁻¹) atTop
          (𝓝 (μH[((m + k : ℕ) : ℝ)] A + 0)) :=
        tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero
      rw [add_zero] at h
      exact ENNReal.Tendsto.const_mul h
        (Or.inr (ENNReal.mul_ne_top measure_ball_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)))
    calc ∫⁻ y, liminf (fun i ↦ G i y) atTop ≤ liminf (fun i ↦ ∫⁻ y, G i y) atTop :=
          lintegral_liminf_le hGmeas
      _ ≤ liminf (fun i : ℕ ↦ ω * (L : ℝ≥0∞) ^ m *
            (μH[((m + k : ℕ) : ℝ)] A + (i : ℝ≥0∞)⁻¹)) atTop :=
          liminf_le_liminf (Eventually.of_forall hint)
      _ = ω * (L : ℝ≥0∞) ^ m * μH[((m + k : ℕ) : ℝ)] A := hlim.liminf_eq

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
