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

/-- **Positive lower `n`-density at a point with an approximate tangent plane of positive
multiplicity** (Simon Ch. 3, Remark 1.5(3), lower half, with multiplicity `θ`; cf. 4.3): if `μ`
is finite on compact sets, `θ > 0` and `λ⁻ⁿ η_{x,λ#} μ → θ Hⁿ ⌞ P` (`finrank P = n`), then
`μ(B_ρ(x)) ≥ c ρⁿ` for some `c > 0` and all small `ρ > 0`. Test with
`g(w) = max(0, 1 - |w|) ∈ C_c(ℝᴺ)`: `Hⁿ ⌞ P` is regular with support `P ∋ 0`, so
`L = θ ∫_P g dHⁿ > 0`; `λ⁻ⁿ ∫ g ∘ η_{x,λ} dμ → L`, and `0 ≤ g ∘ η_{x,ρ} ≤ 1_{B_ρ(x)}` gives
`(L/2) ρⁿ < ∫ g ∘ η_{x,ρ} dμ ≤ μ(B_ρ(x))` for small `ρ`. -/
theorem Submission.tangentMeasure_eventually_lower_density : ∀ (N n : ℕ) (μ : Measure (Rn N))
    (x : Rn N) (P : Submodule ℝ (Rn N)) (θ : ℝ), (∀ K : Set (Rn N), IsCompact K → μ K < ∞) →
    0 < θ → HasApproxTangentPlaneWithMultiplicity n μ x P θ → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (c * ρ ^ n) ≤ μ (Metric.ball x ρ) := by
  intro N n μ x P θ hfin hθ hP
  have : IsFiniteMeasureOnCompacts μ := ⟨hfin⟩
  obtain ⟨hdim, hlim⟩ := hP
  -- The test function `g(w) = max(0, 1 - |w|)`.
  let g0 : Rn N → ℝ := fun w => max 0 (1 - ‖w‖)
  have g0_cont : Continuous g0 := continuous_const.max (continuous_const.sub continuous_norm)
  have g0_supp : HasCompactSupport g0 := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Rn N) 1)
    intro w hw
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hw
    exact max_eq_left (by linarith)
  let g : C_c(Rn N, ℝ) := ⟨⟨g0, g0_cont⟩, g0_supp⟩
  have hg : ∀ w, g w = g0 w := fun w => rfl
  have g0_nonneg : ∀ w, 0 ≤ g0 w := fun w => le_max_left _ _
  have g0_le_one : ∀ w, g0 w ≤ 1 := fun w => max_le zero_le_one (by linarith [norm_nonneg w])
  -- `∫_P g dHⁿ > 0`, since `Hⁿ ⌞ P` is finite on compacts with support `P ∋ 0`.
  have hreg := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
    (E := Rn N) hdim
  have hint_pos : 0 < ∫ y in (P : Set (Rn N)), g y ∂μHE[n] := by
    have hgi : Integrable (fun y => g y) ((μHE[n] : Measure (Rn N)).restrict (P : Set (Rn N))) :=
      g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
    rw [integral_pos_iff_support_of_nonneg (f := fun y => g y) (fun y => g0_nonneg y) hgi]
    have hsub : Metric.ball (0 : Rn N) 1 ⊆ Function.support (fun y => g y) := by
      intro w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      simp only [Function.mem_support, hg, g0]
      apply ne_of_gt
      exact lt_max_of_lt_right (by linarith)
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    have h0 : (0 : Rn N) ∈ ((μHE[n] : Measure (Rn N)).restrict (P : Set (Rn N))).support := by
      rw [Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hdim]
      exact P.zero_mem
    exact (Measure.mem_support_iff_forall _).mp h0 _ (Metric.ball_mem_nhds 0 one_pos)
  -- `c = L / 2` with `L = θ ∫_P g dHⁿ`.
  set L := θ * ∫ y in (P : Set (Rn N)), g y ∂μHE[n] with hLdef
  have hL : 0 < L := mul_pos hθ hint_pos
  refine ⟨L / 2, half_pos hL, ?_⟩
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), L / 2 < (r ^ n)⁻¹ * ∫ y, g (blowUpMap x r y) ∂μ :=
    (hlim g).eventually (lt_mem_nhds (half_lt_self hL))
  filter_upwards [hev, self_mem_nhdsWithin] with ρ hρ hρpos
  have hρpos' : (0 : ℝ) < ρ := hρpos
  have hρn : 0 < ρ ^ n := pow_pos hρpos' n
  have h1 : L / 2 * ρ ^ n < ∫ y, g (blowUpMap x ρ y) ∂μ := by
    have := mul_lt_mul_of_pos_left hρ hρn
    rwa [← mul_assoc, mul_inv_cancel₀ hρn.ne', one_mul, mul_comm] at this
  -- `0 ≤ g ∘ η_{x,ρ} ≤ 1_{B_ρ(x)}` and `μ(B_ρ(x)) < ∞`.
  have hball : μ (Metric.ball x ρ) < ∞ :=
    (measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall x ρ).measure_lt_top
  have hpt : ∀ y, g (blowUpMap x ρ y) ≤ (Metric.ball x ρ).indicator 1 y := by
    intro y
    by_cases hy : y ∈ Metric.ball x ρ
    · rw [Set.indicator_of_mem hy]; exact g0_le_one _
    · rw [Set.indicator_of_notMem hy]
      rw [Metric.mem_ball, dist_eq_norm, not_lt] at hy
      have h1' : 1 ≤ ‖blowUpMap x ρ y‖ := by
        simp only [blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρpos']
        rw [le_inv_mul_iff₀ hρpos']; linarith
      show g0 _ ≤ 0
      exact le_of_eq (max_eq_left (by linarith))
  have h2 : ∫ y, g (blowUpMap x ρ y) ∂μ ≤ μ.real (Metric.ball x ρ) := by
    rw [← integral_indicator_one measurableSet_ball]
    apply integral_mono_of_nonneg
    · exact Eventually.of_forall fun y => g0_nonneg _
    · exact (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_const hball.ne)
    · exact Eventually.of_forall hpt
  calc ENNReal.ofReal (L / 2 * ρ ^ n) ≤ ENNReal.ofReal (μ.real (Metric.ball x ρ)) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = μ (Metric.ball x ρ) := ENNReal.ofReal_toReal hball.ne
/-- Vanishing `n`-density of `μ` in the cone around the normal space at a tangent point: the cone
part of Simon Ch. 3, Remark 1.5(3) (p. 71, `chapter-03.txt` lines 91–105), with multiplicity `θ`.
If `μ` is finite on compact sets, `n ≥ 1` and `μ` has approximate tangent plane `P` with
multiplicity `θ` at `x`, then `μ(C_x ∩ B_ρ(x)) ≤ ε ρⁿ` for all small `ρ > 0`, where
`C_x = {z : |q_P(z - x)| ≤ |z - x|/2}`. As in the book, the indicator of
`S = {w : |q_P w| ≤ |w|/2} ∩ B̄₁(0)` is dominated by a test function, here
`f = max(0, 1 - dist(·, S)/r) ∈ C_c`. On `P`, `f(w) ≠ 0` forces `|w| < 3r`, so
`θ ∫_P f dHⁿ ≤ |θ| Hⁿ(P ∩ B̄_{3r}(0)) < ε` once `r` is small, since `Hⁿ ⌞ P` has no atom at `0`
(`n ≥ 1`); this explicit bound replaces the book's limit over approximating test functions. The
tangent limit then gives `∫ f ∘ η_{x,ρ} dμ < ε ρⁿ` for small `ρ`, and
`1_{C_x ∩ B_ρ(x)} ≤ f ∘ η_{x,ρ}`. -/
theorem Submission.tangentMeasure_eventually_cone_small : ∀ (N n : ℕ) (μ : Measure (Rn N))
    (x : Rn N) (P : Submodule ℝ (Rn N)) (θ : ℝ), (∀ K : Set (Rn N), IsCompact K → μ K < ∞) →
    0 < n → HasApproxTangentPlaneWithMultiplicity n μ x P θ → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ ({z | ‖P.starProjection (z - x)‖ ≤ ‖z - x‖ / 2} ∩ Metric.ball x ρ) ≤
        ENNReal.ofReal (ε * ρ ^ n) := by
  intro N n μ x P θ hfin hn hP ε hε
  have : IsFiniteMeasureOnCompacts μ := ⟨hfin⟩
  obtain ⟨hdim, hlim⟩ := hP
  have hreg := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
    (E := Rn N) hdim
  -- `ν = Hⁿ ⌞ P` has no atom at `0`, so `ν(B̄_{1/(k+1)}(0)) → 0`
  set ν : Measure (Rn N) := (μHE[n] : Measure (Rn N)).restrict (P : Set (Rn N)) with hν
  have hν0 : ν {0} = 0 := by
    rw [hν, Measure.restrict_apply (measurableSet_singleton 0)]
    apply measure_mono_null Set.inter_subset_left
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
    have := Measure.nullSingletonClass_hausdorff (X := Rn N) (d := (n : ℝ))
      (by exact_mod_cast hn)
    simp [measure_singleton]
  have hinter : (⋂ k : ℕ, Metric.closedBall (0 : Rn N) (1 / ((k : ℝ) + 1))) = {0} := by
    ext y
    simp only [Set.mem_iInter, Metric.mem_closedBall, Set.mem_singleton_iff]
    constructor
    · intro h
      by_contra hne
      have hpos : 0 < dist y 0 := dist_pos.mpr hne
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
      exact absurd (h k) (not_le.mpr hk)
    · rintro rfl k
      simp only [dist_self]
      positivity
  have htend : Tendsto (fun k : ℕ => ν (Metric.closedBall 0 (1 / ((k : ℝ) + 1)))) atTop
      (𝓝 (ν {0})) := by
    rw [← hinter]
    apply tendsto_measure_iInter_atTop
    · exact fun k => measurableSet_closedBall.nullMeasurableSet
    · intro k l hkl
      apply Metric.closedBall_subset_closedBall
      gcongr
    · exact ⟨0, (isCompact_closedBall _ _).measure_lt_top.ne⟩
  rw [hν0] at htend
  have htend' : Tendsto (fun k : ℕ => |θ| * (ν (Metric.closedBall 0 (1 / ((k : ℝ) + 1)))).toReal)
      atTop (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend).const_mul |θ|
    simpa using this
  obtain ⟨k, hk⟩ := (htend'.eventually (gt_mem_nhds (half_pos hε))).exists
  set r : ℝ := 1 / (3 * ((k : ℝ) + 1)) with hr
  have hr0 : 0 < r := by positivity
  have hr3 : 3 * r = 1 / ((k : ℝ) + 1) := by rw [hr]; field_simp
  -- the test function `f = max(0, 1 - dist(·, S)/r)`, equal to `1` on the truncated cone `S`
  set q := P.starProjection
  set S : Set (Rn N) := {w | ‖q w‖ ≤ ‖w‖ / 2} ∩ Metric.closedBall 0 1
  have hS0 : (0 : Rn N) ∈ S := ⟨by simp, by simp⟩
  have hSne : S.Nonempty := ⟨0, hS0⟩
  let f0 : Rn N → ℝ := fun w => max 0 (1 - Metric.infDist w S / r)
  have f0_cont : Continuous f0 :=
    continuous_const.max (continuous_const.sub ((Metric.continuous_infDist_pt S).div_const r))
  have f0_nonneg : ∀ w, 0 ≤ f0 w := fun w => le_max_left _ _
  have f0_zero : ∀ w, r ≤ Metric.infDist w S → f0 w = 0 := by
    intro w hw
    apply max_eq_left
    have : 1 ≤ Metric.infDist w S / r := by rw [le_div_iff₀ hr0]; linarith
    linarith
  have f0_out : ∀ w, 1 + r < ‖w‖ → f0 w = 0 := by
    intro w hw
    refine f0_zero w (not_lt.mp fun hlt => ?_)
    obtain ⟨s, hs, hws⟩ := (Metric.infDist_lt_iff hSne).mp hlt
    have hs1 : ‖s‖ ≤ 1 := by simpa using hs.2
    rw [dist_eq_norm] at hws
    have : ‖w‖ ≤ ‖w - s‖ + ‖s‖ := by
      calc ‖w‖ = ‖(w - s) + s‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith
  have f0_supp : HasCompactSupport f0 := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Rn N) (1 + r))
    intro w hw
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hw
    exact f0_out w hw
  let f : C_c(Rn N, ℝ) := ⟨⟨f0, f0_cont⟩, f0_supp⟩
  have hf : ∀ w, f w = f0 w := fun w => rfl
  -- on `P`, `f w ≠ 0` forces `‖w‖ < 3 r`, so the limit `θ ∫_P f dHⁿ` is `< ε`
  have hloc : ∀ w ∈ (P : Set (Rn N)), f0 w ≠ 0 → ‖w‖ < 3 * r := by
    intro w hwP hw
    have hlt : Metric.infDist w S < r := not_le.mp fun h => hw (f0_zero w h)
    obtain ⟨s, hs, hws⟩ := (Metric.infDist_lt_iff hSne).mp hlt
    rw [dist_eq_norm] at hws
    have hqw : q w = w := P.starProjection_eq_self_iff.mpr hwP
    have h1 : ‖w‖ ≤ ‖q s‖ + ‖w - s‖ := by
      calc ‖w‖ = ‖q w‖ := by rw [hqw]
        _ = ‖q s + q (w - s)‖ := by rw [← map_add]; congr 2; abel
        _ ≤ ‖q s‖ + ‖q (w - s)‖ := norm_add_le _ _
        _ ≤ ‖q s‖ + ‖w - s‖ := by gcongr; exact P.norm_starProjection_apply_le _
    have h2 : ‖q s‖ ≤ ‖s‖ / 2 := hs.1
    have h3 : ‖s‖ ≤ ‖w‖ + ‖w - s‖ := by
      calc ‖s‖ = ‖w - (w - s)‖ := by congr 1; abel
        _ ≤ ‖w‖ + ‖w - s‖ := norm_sub_le _ _
    linarith
  have hplane : ∫ y in (P : Set (Rn N)), f y ∂μHE[n] ≤
      (ν (Metric.closedBall 0 (3 * r))).toReal := by
    change ∫ y, f y ∂ν ≤ _
    rw [← measureReal_def, ← integral_indicator_one measurableSet_closedBall]
    apply integral_mono_of_nonneg
    · exact Eventually.of_forall fun y => f0_nonneg _
    · exact (integrable_indicator_iff measurableSet_closedBall).mpr
        (integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne)
    · rw [hν]
      filter_upwards [ae_restrict_mem P.closed_of_finiteDimensional.measurableSet] with y hyP
      by_cases hy0 : f0 y = 0
      · rw [hf, hy0]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
      · have hyb : y ∈ Metric.closedBall (0 : Rn N) (3 * r) := by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact (hloc y hyP hy0).le
        rw [Set.indicator_of_mem hyb, hf]
        exact max_le zero_le_one (by
          have := Metric.infDist_nonneg (x := y) (s := S)
          have : 0 ≤ Metric.infDist y S / r := div_nonneg this hr0.le
          simp only [Pi.one_apply]; linarith)
  have hlimlt : θ * ∫ y in (P : Set (Rn N)), f y ∂μHE[n] < ε := by
    have hint_nonneg : 0 ≤ ∫ y in (P : Set (Rn N)), f y ∂μHE[n] :=
      integral_nonneg fun y => f0_nonneg y
    calc θ * ∫ y in (P : Set (Rn N)), f y ∂μHE[n]
        ≤ |θ| * ∫ y in (P : Set (Rn N)), f y ∂μHE[n] :=
          mul_le_mul_of_nonneg_right (le_abs_self θ) hint_nonneg
      _ ≤ |θ| * (ν (Metric.closedBall 0 (3 * r))).toReal :=
          mul_le_mul_of_nonneg_left hplane (abs_nonneg θ)
      _ < ε / 2 := by rw [hr3]; exact hk
      _ < ε := half_lt_self hε
  -- the tangent limit gives `∫ f ∘ η_{x,ρ} dμ < ε ρⁿ` for small `ρ`
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (ρ ^ n)⁻¹ * ∫ y, f (blowUpMap x ρ y) ∂μ < ε :=
    (hlim f).eventually (gt_mem_nhds hlimlt)
  filter_upwards [hev, self_mem_nhdsWithin] with ρ hρ hρpos
  have hρpos' : (0 : ℝ) < ρ := hρpos
  have hρn : 0 < ρ ^ n := pow_pos hρpos' n
  have hJ : ∫ y, f (blowUpMap x ρ y) ∂μ < ε * ρ ^ n := by
    have := mul_lt_mul_of_pos_left hρ hρn
    rwa [← mul_assoc, mul_inv_cancel₀ hρn.ne', one_mul, mul_comm] at this
  -- `1_{C_x ∩ B_ρ(x)} ≤ f ∘ η_{x,ρ}`, and the latter is continuous with compact support
  set T := {z | ‖q (z - x)‖ ≤ ‖z - x‖ / 2} ∩ Metric.ball x ρ
  have hTm : MeasurableSet T := by
    refine (isClosed_le ?_ ?_).measurableSet.inter measurableSet_ball
    · exact (q.continuous.comp (continuous_id.sub continuous_const)).norm
    · exact (continuous_id.sub continuous_const).norm.div_const 2
  have hTfin : μ T < ∞ :=
    (measure_mono (Set.inter_subset_right.trans Metric.ball_subset_closedBall)).trans_lt
      (isCompact_closedBall x ρ).measure_lt_top
  have hblow : ∀ y, blowUpMap x ρ y = ρ⁻¹ • (y - x) := fun y => rfl
  have hpt : ∀ y, T.indicator 1 y ≤ f (blowUpMap x ρ y) := by
    intro y
    by_cases hy : y ∈ T
    · rw [Set.indicator_of_mem hy]
      have hw : blowUpMap x ρ y ∈ S := by
        obtain ⟨hy1, hy2⟩ := hy
        rw [Metric.mem_ball, dist_eq_norm] at hy2
        simp only [Set.mem_ofPred_eq] at hy1
        refine ⟨?_, ?_⟩
        · show ‖q (blowUpMap x ρ y)‖ ≤ ‖blowUpMap x ρ y‖ / 2
          rw [hblow, map_smul, norm_smul, norm_smul, Real.norm_eq_abs, abs_inv,
            abs_of_pos hρpos']
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hy1 (inv_nonneg.mpr hρpos'.le)
        · rw [Metric.mem_closedBall, dist_zero_right, hblow, norm_smul, Real.norm_eq_abs,
            abs_inv, abs_of_pos hρpos', inv_mul_le_iff₀ hρpos']
          linarith
      rw [hf]
      show (1 : ℝ) ≤ max 0 (1 - Metric.infDist (blowUpMap x ρ y) S / r)
      rw [Metric.infDist_zero_of_mem hw]
      simp
    · rw [Set.indicator_of_notMem hy]
      exact f0_nonneg _
  have hηc : Continuous (blowUpMap x ρ) := by
    change Continuous fun y : Rn N => ρ⁻¹ • (y - x)
    fun_prop
  have hcont : Continuous (fun y => f (blowUpMap x ρ y)) := f.continuous.comp hηc
  have hcs : HasCompactSupport (fun y => f (blowUpMap x ρ y)) := by
    apply HasCompactSupport.intro (isCompact_closedBall x (ρ * (1 + r)))
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hy
    rw [hf]
    apply f0_out
    rw [hblow, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρpos', lt_inv_mul_iff₀ hρpos']
    linarith
  have hfi : Integrable (fun y => f (blowUpMap x ρ y)) μ :=
    hcont.integrable_of_hasCompactSupport hcs
  have hmono : μ.real T ≤ ∫ y, f (blowUpMap x ρ y) ∂μ := by
    rw [← integral_indicator_one hTm]
    exact integral_mono_of_nonneg
      (Eventually.of_forall fun y => Set.indicator_nonneg (fun _ _ => zero_le_one) _) hfi
      (Eventually.of_forall hpt)
  calc μ T = ENNReal.ofReal (μ.real T) := (ENNReal.ofReal_toReal hTfin.ne).symm
    _ ≤ ENNReal.ofReal (ε * ρ ^ n) := ENNReal.ofReal_le_ofReal (by linarith)
/-- **A countable `ε`-net of `n`-planes** for the distance `d(π, π') = ‖q_π - q_{π'}‖` of
Simon Ch. 3, (3) (p. 72). Step 4 of the proof of Theorem 1.6 (p. 73) chooses finitely many
planes `π₁, …, π_N` such that every plane is within `1/16` of one of them; countably many
suffice. The projections `q_P` onto `n`-planes form a subset of the finite-dimensional, hence
separable, space `ℝᴺ →L[ℝ] ℝᴺ`, so they contain a countable dense subset. It is nonempty because
`n ≤ N` gives an `n`-plane, so it is the range of a sequence `q_{Q_j}`. -/
theorem Submission.tangentMeasure_countable_projection_net : ∀ (N n : ℕ) (ε : ℝ), n ≤ N → 0 < ε → ∃ Q : ℕ → Submodule ℝ (Rn N), (∀ j, finrank ℝ (Q j) = n) ∧ ∀ P : Submodule ℝ (Rn N), finrank ℝ P = n → ∃ j, ‖P.starProjection - (Q j).starProjection‖ < ε := by
  intro N n ε hnN hε
  -- Step 1: the projections onto `n`-planes have a countable dense subset `D`.
  let S : Set (Rn N →L[ℝ] Rn N) :=
    (fun P : Submodule ℝ (Rn N) ↦ P.starProjection) '' {P | finrank ℝ P = n}
  obtain ⟨D, hDS, hDc, hSD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  -- Step 2: `n ≤ N` gives an `n`-plane `span (range f)`, so `S` is nonempty.
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := ℝ) (M := Rn N) (n := n)
    (by rwa [finrank_euclideanSpace_fin])
  obtain ⟨T, hT⟩ : S.Nonempty :=
    ⟨_, Submodule.span ℝ (Set.range f), (finrank_span_eq_card hf).trans (Fintype.card_fin n), rfl⟩
  -- Step 3: hence `D` is nonempty, and it is the range of a sequence `e`.
  obtain ⟨e, rfl⟩ := hDc.exists_eq_range (closure_nonempty_iff.mp ⟨T, hSD hT⟩)
  -- Step 4: each `e j` is the projection onto some `n`-plane `Q j`.
  have he : ∀ j, ∃ Q : Submodule ℝ (Rn N), finrank ℝ Q = n ∧ Q.starProjection = e j :=
    fun j ↦ hDS (Set.mem_range_self j)
  choose Q hQ hQe using he
  refine ⟨Q, hQ, fun P hP ↦ ?_⟩
  -- Step 5: density of `range e` in `S` gives `j` with `‖q_P - q_{Q j}‖ < ε`.
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := Metric.mem_closure_iff.mp (hSD ⟨P, hP, rfl⟩) ε hε
  refine ⟨j, ?_⟩
  rw [hQe j, ← dist_eq_norm]
  exact hj

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
