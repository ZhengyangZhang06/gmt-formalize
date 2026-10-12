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

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
